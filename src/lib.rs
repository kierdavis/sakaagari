/*
 * Copyright 2021 Kier Ada Davis
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use serde::{Serialize, de::DeserializeOwned};
use std::borrow::Cow;
use std::path::Path;
use std::convert::Infallible;
use std::marker::PhantomData;
use std::os::unix::ffi::OsStringExt;

pub trait Codec<K> {
  type Accepted: ?Sized;
  type EncodeError: std::error::Error + 'static;
  fn encode<'v>(key: &K, value: &'v Self::Accepted) -> Result<Cow<'v, [u8]>, Self::EncodeError>;
  type Produced;
  type DecodeError: std::error::Error + 'static;
  fn decode(key: &K, value: &[u8]) -> Result<Self::Produced, Self::DecodeError>;
}

#[derive(Debug)]
pub struct Raw;
impl<K> Codec<K> for Raw {
  type Accepted = [u8];
  type EncodeError = Infallible;
  fn encode<'v>(_: &K, value: &'v [u8]) -> Result<Cow<'v, [u8]>, Infallible> { Ok(Cow::Borrowed(value)) }
  type Produced = Vec<u8>;
  type DecodeError = Infallible;
  fn decode(_: &K, value: &[u8]) -> Result<Vec<u8>, Infallible> { Ok(value.to_vec()) }
}

#[derive(Debug)]
pub struct Toml<V: 'static>(PhantomData<&'static V>);
impl<K, V> Codec<K> for Toml<V>
  where V: Serialize + DeserializeOwned
{
  type Accepted = V;
  type EncodeError = toml::ser::Error;
  fn encode<'v>(_: &K, value: &'v V) -> Result<Cow<'v, [u8]>, toml::ser::Error> {
    toml::to_vec(value).map(Cow::Owned)
  }
  type Produced = V;
  type DecodeError = toml::de::Error;
  fn decode(_: &K, value: &[u8]) -> Result<V, toml::de::Error> {
    toml::from_slice(value)
  }
}

pub trait Key: Sized {
  fn to_path(&self) -> Cow<Path>;
  fn from_path(path: &Path) -> Option<Self>;
  type Codec: Codec<Self>;
}

macro_rules! Accepted {
  ($K:ty) => { <<$K as Key>::Codec as Codec<$K>>::Accepted }
}
macro_rules! Produced {
  ($K:ty) => { <<$K as Key>::Codec as Codec<$K>>::Produced }
}

pub struct Store {
  repo: git2::Repository,
}
impl std::fmt::Debug for Store {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    f.debug_struct("Store")
      .field("repo", &self.repo.path())
      .finish()
  }
}
pub fn open<P: AsRef<Path>>(path: P) -> Result<Store, Error> { Store::open(path) }
impl Store {
  pub fn open<P: AsRef<Path>>(path: P) -> Result<Store, Error> {
    use git2::ErrorCode::NotFound;
    let repo = match git2::Repository::open(path.as_ref()) {
      Err(err) if err.code() == NotFound => git2::Repository::init_bare(path),
      res => res,
    }.map_err(Error::git("open repository"))?;
    Ok(Store { repo })
  }
  pub fn current(&self) -> Result<Version, Error> {
    use git2::ErrorCode::UnbornBranch;
    let reference = match self.repo.head() {
      Err(err) if err.code() == UnbornBranch => return Version::new(self, None),
      res => res,
    }.map_err(Error::git("get HEAD"))?;
    let commit = reference.peel_to_commit().map_err(Error::git("resolve HEAD ref to commit"))?;
    Version::new(self, Some(commit))
  }
  pub fn set_current<'repo>(&'repo self, version: &Version<'repo>) -> Result<(), Error> {
    match version.commit.as_ref() {
      None => panic!("not implemented"),
      Some(commit) => {
        const REFERENCE_NAME: &'static str = "refs/heads/master";
        let message = commit.summary_bytes().map_or("[sakaagari] update".into(), String::from_utf8_lossy);
        self.repo.reference(REFERENCE_NAME, commit.id(), true, message.as_ref())
          .map_err(Error::git("create/overwrite HEAD ref"))?;
        self.repo.set_head(REFERENCE_NAME)
          .map_err(Error::git("set HEAD"))
      },
    }
  }
}

mod internal {
  use std::path::PathBuf;
  use std::ffi::OsString;
  use std::os::unix::ffi::OsStringExt;
  use super::Key;
  pub trait Access {
    fn repo(&self) -> &git2::Repository;
    fn index(&self) -> &git2::Index;
    fn blobs<'a, K: Key>(&'a self) -> Box<dyn Iterator<Item=(K, git2::Oid)> + 'a> {
      Box::new(self.index().iter().filter_map(|entry| match entry.mode {
        0o100644 | 0o100755 => {
          let path = PathBuf::from(OsString::from_vec(entry.path));
          let oid = entry.id;
          K::from_path(&path).map(move |key| (key, oid))
        },
        _ => None,
      }))
    }
  }
  pub trait AccessMut: Access {
    fn index_mut(&mut self) -> &mut git2::Index;
  }
}
pub trait Access: internal::Access {
  fn get<K: Key>(&self, key: &K) -> Result<Produced!(K), Error> {
    let entry = self.index().get_path(&key.to_path(), 0)
      .ok_or(Error::NotFound)?;
    let blob = self.repo().find_blob(entry.id)
      .map_err(Error::git("get blob from index entry"))?;
    K::Codec::decode(key, blob.content())
      .map_err(Error::decode)
  }
  fn keys<'a, K: Key + 'a>(&'a self) -> Box<dyn Iterator<Item=K> + 'a> {
    Box::new(self.blobs().map(|pair| pair.0))
  }
  fn iter<'a, K: Key + 'a>(&'a self) -> Box<dyn Iterator<Item=Result<(K, Produced!(K)), Error>> + 'a> {
    Box::new(self.blobs().map(move |(key, oid)| {
      let blob = self.repo().find_blob(oid).map_err(Error::git("get blob by id while iterating"))?;
      let value = K::Codec::decode(&key, blob.content()).map_err(Error::decode)?;
      Ok((key, value))
    }))
  }
  fn values<'a, K: Key + 'a>(&'a self) -> Box<dyn Iterator<Item=Result<Produced!(K), Error>> + 'a> {
    Box::new(self.iter::<K>().map(|result| result.map(|pair| pair.1)))
  }
}
pub trait AccessMut: internal::AccessMut {
  fn put<K: Key>(&mut self, key: &K, value: &Accepted!(K)) -> Result<(), Error> {
    let contents = K::Codec::encode(key, value)
      .map_err(Error::encode)?;
    let blob_id = self.repo().blob(&contents)
      .map_err(Error::git("create blob"))?;
    let now = current_index_time();
    let entry = git2::IndexEntry {
      ctime: now,
      mtime: now,
      dev: 0,
      ino: 0,
      mode: 0o100644,
      uid: 0,
      gid: 0,
      file_size: contents.len() as u32,
      id: blob_id,
      flags: 0,
      flags_extended: 0,
      path: key.to_path().into_owned().into_os_string().into_vec(),
    };
    self.index_mut().add(&entry)
      .map_err(Error::git("insert entry into index"))
  }
  fn delete<K: Key>(&mut self, key: &K) -> Result<(), Error> {
    self.index_mut().remove(&key.to_path(), 0)
      .map_err(Error::git("remove entry from index"))
  }
}

pub struct Version<'repo> {
  store: &'repo Store,
  commit: Option<git2::Commit<'repo>>,
  index: git2::Index,
}
impl<'repo> Version<'repo> {
  fn new(store: &'repo Store, commit: Option<git2::Commit<'repo>>) -> Result<Self, Error> {
    Ok(Version { index: index_from_commit(commit.as_ref())?, store, commit })
  }
  fn commit_id(&self) -> Option<git2::Oid> {
    self.commit.as_ref().map(|c| c.id())
  }
  pub fn derive<F>(&self, f: F) -> Result<Version<'repo>, Error>
    where F: for<'tx> FnOnce(&'tx mut Transaction<'repo>) -> Result<CommitMetadata<'static>, Error>
  {
    let mut tx = Transaction {
      store: self.store,
      index: index_from_commit(self.commit.as_ref())?,
    };
    let commit_metadata = f(&mut tx)?;
    let tree_id = tx.index.write_tree_to(&self.store.repo).map_err(Error::git("create tree from index"))?;
    let tree = self.store.repo.find_tree(tree_id).map_err(Error::git("get created tree"))?;
    Ok(Version::new(
      self.store,
      Some(self.store.repo.find_commit(
        self.store.repo.commit(
          None,
          &commit_metadata.author.signature()?,
          &commit_metadata.committer.signature()?,
          commit_metadata.message.as_ref(),
          &tree,
          &self.commit.iter().collect::<Vec<_>>(),
        ).map_err(Error::git("create commit"))?
      ).map_err(Error::git("get created commit"))?),
    )?)
  }
}
impl<'repo> internal::Access for Version<'repo> {
  fn repo(&self) -> &git2::Repository {
    &self.store.repo
  }
  fn index(&self) -> &git2::Index {
    &self.index
  }
}
impl<'repo> Access for Version<'repo> {}
impl<'repo> Clone for Version<'repo> {
  fn clone(&self) -> Self {
    Version::new(self.store, self.commit.clone()).unwrap()
  }
}
impl<'repo> std::fmt::Debug for Version<'repo> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    f.debug_struct("Version")
      .field("store", &self.store)
      .field("commit", &self.commit)
      .finish()
  }
}
impl<'repo> PartialEq for Version<'repo> {
  fn eq(&self, other: &Self) -> bool {
    self.commit_id() == other.commit_id()
  }
}
impl<'repo> Eq for Version<'repo> {}

pub struct Transaction<'repo> {
  store: &'repo Store,
  index: git2::Index,
}
impl<'repo> internal::Access for Transaction<'repo> {
  fn repo(&self) -> &git2::Repository {
    &self.store.repo
  }
  fn index(&self) -> &git2::Index {
    &self.index
  }
}
impl<'repo> internal::AccessMut for Transaction<'repo> {
  fn index_mut(&mut self) -> &mut git2::Index {
    &mut self.index
  }
}
impl<'repo> Access for Transaction<'repo> {}
impl<'repo> AccessMut for Transaction<'repo> {}
impl<'repo> std::fmt::Debug for Transaction<'repo> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    f.debug_struct("Transaction")
      .field("store", &self.store)
      .finish()
  }
}

fn index_from_commit<'repo>(commit: Option<&git2::Commit<'repo>>) -> Result<git2::Index, Error> {
  let mut index = git2::Index::new()
    .map_err(Error::git("create new index"))?;
  match commit {
    Some(commit) => index.read_tree(
      &commit.tree().map_err(Error::git("get tree from commit"))?
    ).map_err(Error::git("populate index from tree"))?,
    None => {},
  }
  Ok(index)
}

fn current_index_time() -> git2::IndexTime {
  use std::time::SystemTime;
  let t = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH).unwrap();
  git2::IndexTime::new(t.as_secs() as i32, t.subsec_nanos() as u32)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommitMetadata<'a> {
  pub message: Cow<'a, str>,
  pub author: Author<'a>,
  pub committer: Author<'a>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Author<'a> {
  pub name: Cow<'a, str>,
  pub email: Cow<'a, str>,
}
impl<'a> Author<'a> {
  fn signature(&self) -> Result<git2::Signature<'static>, Error> {
    git2::Signature::now(self.name.as_ref(), self.email.as_ref()).map_err(Error::git("create signature"))
  }
}

#[derive(Debug)]
pub enum Error {
  NotFound,
  Git(git2::Error, Cow<'static, str>),
  Encode(Box<dyn std::error::Error>),
  Decode(Box<dyn std::error::Error>),
}
impl Error {
  pub fn git<S: Into<Cow<'static, str>>>(what: S) -> impl FnOnce(git2::Error) -> Self {
    let what = what.into();
    move |err| Error::Git(err, what)
  }
  pub fn encode<E: std::error::Error + 'static>(err: E) -> Self {
    Self::Encode(Box::new(err))
  }
  pub fn decode<E: std::error::Error + 'static>(err: E) -> Self {
    Self::Decode(Box::new(err))
  }
}
impl std::fmt::Display for Error {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Error::NotFound => write!(f, "not found"),
      Error::Git(err, what) => write!(f, "internal git error when attempting to {}: {}", what, err),
      Error::Encode(err) => write!(f, "failed to encode value: {}", err),
      Error::Decode(err) => write!(f, "failed to decode value: {}", err),
    }
  }
}
impl std::error::Error for Error {}
