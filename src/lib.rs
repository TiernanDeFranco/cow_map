//! CowMap: a copy-on-write map that starts as a static lookup table and turns
//! into a `HashMap` on first write.
//!
//! - **Read-only**: Uses a compile-time table (no heap, O(1) lookups).
//! - **First write** (`insert`, `remove`, `get_mut`): Copies the table into a
//!   `HashMap`, then performs the operation. After that it behaves like a normal
//!   `HashMap`.
//!
//! # Creating a CowMap
//!
//! Use the [`cow_map!`] macro. One map in this scope:
//!
//! ```rust
//! use cow_map::cow_map;
//! let config = cow_map!(i32 => "timeout" => 30, "port" => 8080);
//! assert!(config.is_borrowed());
//! ```
//!
//! Several maps in the same scope — give each a name so each gets its own static:
//!
//! ```rust
//! use cow_map::cow_map;
//! let defaults = cow_map!(DEFAULTS: i32 => "timeout" => 30);
//! let other    = cow_map!(OTHER: i32 => "x" => 1, "y" => 2);
//! assert_eq!(defaults.get("timeout"), Some(&30));
//! assert_eq!(other.get("x"), Some(&1));
//! ```

use std::borrow::Borrow;
use std::collections::HashMap;
use std::iter::FromIterator;

use phf::map::Entries;
use phf_shared::PhfBorrow;


pub use phf;

/// Copy-on-write map: either a read-only static table or an owned `HashMap`.
#[derive(Clone)]
pub enum CowMap<K, V>
where
    K: 'static,
    V: 'static,
{
    /// Borrowed: read-only view of a compile-time table (no heap).
    Borrowed(&'static phf::Map<K, V>),
    /// Owned: a `HashMap`; used after the first write (promotion).
    Owned(HashMap<K, V>),
}

impl<K, V> CowMap<K, V>
where
    K: 'static + Eq + std::hash::Hash,
    V: 'static,
{
    /// Creates a CowMap that borrows from a static PHF map (zero alloc).
    #[inline]
    pub const fn borrowed(map: &'static phf::Map<K, V>) -> Self {
        CowMap::Borrowed(map)
    }

    /// Alias for `borrowed`; creates a CowMap from a static PHF map.
    #[inline]
    pub const fn from_static(map: &'static phf::Map<K, V>) -> Self {
        CowMap::Borrowed(map)
    }

    /// Creates a CowMap that starts in owned mode with an empty HashMap.
    #[inline]
    pub fn owned_empty() -> Self
    where
        K: std::hash::Hash + Eq,
        V: 'static,
    {
        CowMap::Owned(HashMap::new())
    }

    /// Creates a CowMap that starts in owned mode with the given HashMap.
    #[inline]
    pub fn owned(map: HashMap<K, V>) -> Self {
        CowMap::Owned(map)
    }

    /// Returns `true` if this map is still the compile-time table (no write yet).
    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        matches!(self, CowMap::Borrowed(_))
    }

    /// Returns `true` if this map has been promoted to an owned `HashMap`.
    #[inline]
    pub const fn is_owned(&self) -> bool {
        matches!(self, CowMap::Owned(_))
    }

    /// Returns the number of entries.
    #[inline]
    pub fn len(&self) -> usize {
        match self {
            CowMap::Borrowed(m) => m.len(),
            CowMap::Owned(m) => m.len(),
        }
    }

    /// Returns `true` if the map is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        match self {
            CowMap::Borrowed(m) => m.is_empty(),
            CowMap::Owned(m) => m.is_empty(),
        }
    }

    /// Returns a reference to the value for `key`, if present.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: PhfBorrow<Q> + Borrow<Q> + Eq + std::hash::Hash,
        Q: ?Sized + Eq + phf::PhfHash + std::hash::Hash,
    {
        match self {
            CowMap::Borrowed(m) => m.get(key),
            CowMap::Owned(m) => m.get(key),
        }
    }

    /// Returns a mutable reference to the value for `key`, if present.
    /// **Promotes** to owned on first use (copies PHF into a HashMap), then performs the lookup.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: PhfBorrow<Q> + Borrow<Q> + Clone + std::hash::Hash + Eq,
        Q: ?Sized + Eq + phf::PhfHash + std::hash::Hash,
        V: Clone,
    {
        self.promote_if_borrowed();
        match self {
            CowMap::Borrowed(_) => unreachable!(),
            CowMap::Owned(m) => m.get_mut(key),
        }
    }

    /// Returns `true` if the map contains `key`.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: PhfBorrow<Q> + Borrow<Q> + Eq + std::hash::Hash,
        Q: ?Sized + Eq + phf::PhfHash + std::hash::Hash,
    {
        match self {
            CowMap::Borrowed(m) => m.contains_key(key),
            CowMap::Owned(m) => m.contains_key(key),
        }
    }

    /// Inserts `key` and `value`. **Promotes** to owned on first write if currently borrowed.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Clone + std::hash::Hash + Eq,
        V: Clone,
    {
        self.promote_if_borrowed();
        match self {
            CowMap::Borrowed(_) => unreachable!(),
            CowMap::Owned(m) => m.insert(key, value),
        }
    }

    /// Removes `key` and returns the value if present. **Promotes** to owned on first write if currently borrowed.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: PhfBorrow<Q> + Borrow<Q> + Clone + std::hash::Hash + Eq,
        Q: ?Sized + Eq + phf::PhfHash + std::hash::Hash,
        V: Clone,
    {
        self.promote_if_borrowed();
        match self {
            CowMap::Borrowed(_) => unreachable!(),
            CowMap::Owned(m) => m.remove(key),
        }
    }

    /// If currently borrowed, copies all PHF entries into a new HashMap and switches to Owned.
    /// No-op if already owned.
    fn promote_if_borrowed(&mut self)
    where
        K: Clone + std::hash::Hash + Eq,
        V: Clone,
    {
        if let CowMap::Borrowed(phf_map) = self {
            let owned: HashMap<K, V> = phf_map.entries().map(|(k, v)| (k.clone(), v.clone())).collect();
            *self = CowMap::Owned(owned);
        }
    }

    /// Returns an iterator over (key, value) references.
    pub fn iter(&self) -> MapIter<'_, K, V> {
        match self {
            CowMap::Borrowed(m) => MapIter::Borrowed(m.entries()),
            CowMap::Owned(m) => MapIter::Owned(m.iter()),
        }
    }

    /// Returns an iterator over keys.
    pub fn keys(&self) -> KeysIter<'_, K, V> {
        match self {
            CowMap::Borrowed(m) => KeysIter::Borrowed(m.keys()),
            CowMap::Owned(m) => KeysIter::Owned(m.keys()),
        }
    }

    /// Returns an iterator over values.
    pub fn values(&self) -> ValuesIter<'_, K, V> {
        match self {
            CowMap::Borrowed(m) => ValuesIter::Borrowed(m.values()),
            CowMap::Owned(m) => ValuesIter::Owned(m.values()),
        }
    }

    /// Returns an owned copy of the map as a `HashMap`.
    /// If this is borrowed (static PHF), copies all entries into a new `HashMap`.
    pub fn to_hashmap(&self) -> HashMap<K, V>
    where
        K: Clone + std::hash::Hash + Eq,
        V: Clone,
    {
        match self {
            CowMap::Borrowed(m) => m.entries().map(|(k, v)| (k.clone(), v.clone())).collect(),
            CowMap::Owned(m) => m.clone(),
        }
    }

    /// Consumes the `CowMap` and returns the underlying `HashMap`.
    /// If this was borrowed (static PHF), copies all entries into a new `HashMap`.
    pub fn into_hashmap(self) -> HashMap<K, V>
    where
        K: Clone + std::hash::Hash + Eq,
        V: Clone,
    {
        match self {
            CowMap::Borrowed(m) => m.entries().map(|(k, v)| (k.clone(), v.clone())).collect(),
            CowMap::Owned(m) => m,
        }
    }
}

/// Iterator over (key, value) references for CowMap.
pub enum MapIter<'a, K, V> {
    Borrowed(Entries<'a, K, V>),
    Owned(std::collections::hash_map::Iter<'a, K, V>),
}

impl<'a, K, V> Iterator for MapIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            MapIter::Borrowed(it) => it.next(),
            MapIter::Owned(it) => it.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            MapIter::Borrowed(it) => it.size_hint(),
            MapIter::Owned(it) => it.size_hint(),
        }
    }
}

/// Iterator over keys for CowMap.
pub enum KeysIter<'a, K, V> {
    Borrowed(phf::map::Keys<'a, K, V>),
    Owned(std::collections::hash_map::Keys<'a, K, V>),
}

impl<'a, K, V> Iterator for KeysIter<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            KeysIter::Borrowed(it) => it.next(),
            KeysIter::Owned(it) => it.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            KeysIter::Borrowed(it) => it.size_hint(),
            KeysIter::Owned(it) => it.size_hint(),
        }
    }
}

/// Iterator over values for CowMap.
pub enum ValuesIter<'a, K, V> {
    Borrowed(phf::map::Values<'a, K, V>),
    Owned(std::collections::hash_map::Values<'a, K, V>),
}

impl<'a, K, V> Iterator for ValuesIter<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ValuesIter::Borrowed(it) => it.next(),
            ValuesIter::Owned(it) => it.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            ValuesIter::Borrowed(it) => it.size_hint(),
            ValuesIter::Owned(it) => it.size_hint(),
        }
    }
}

impl<K, V> Default for CowMap<K, V>
where
    K: 'static + std::hash::Hash + Eq,
    V: 'static,
{
    /// Default is an empty owned HashMap.
    fn default() -> Self {
        CowMap::Owned(HashMap::new())
    }
}

impl<K, V> std::fmt::Debug for CowMap<K, V>
where
    K: 'static + std::fmt::Debug,
    V: 'static + std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CowMap::Borrowed(m) => f.debug_tuple("Borrowed").field(m).finish(),
            CowMap::Owned(m) => f.debug_tuple("Owned").field(m).finish(),
        }
    }
}

impl<K, V> From<HashMap<K, V>> for CowMap<K, V>
where
    K: 'static,
    V: 'static,
{
    fn from(map: HashMap<K, V>) -> Self {
        CowMap::Owned(map)
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for CowMap<K, V>
where
    K: 'static + std::hash::Hash + Eq,
    V: 'static,
{
    fn from(arr: [(K, V); N]) -> Self {
        CowMap::Owned(HashMap::from(arr))
    }
}

impl<K, V> FromIterator<(K, V)> for CowMap<K, V>
where
    K: 'static + std::hash::Hash + Eq,
    V: 'static,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        CowMap::Owned(HashMap::from_iter(iter))
    }
}

/// Creates a borrowed `CowMap` from key–value pairs at compile time.
///
/// You only need `cow_map` in your dependencies; `phf` is re-exported for the
/// macro. You must specify the value type (keys are `&str` by default).
///
/// # One map (short form)
///
/// ```rust
/// use cow_map::cow_map;
/// let m = cow_map!(i32 => "a" => 1, "b" => 2);
/// assert_eq!(m.get("a"), Some(&1));
/// ```
///
/// # Several maps in one scope (named form)
///
/// The short form expands to a static named `__COW_MAP`. Two short-form calls
/// in the same scope would define `__COW_MAP` twice → compile error. Give each
/// map a name so each gets its own static:
///
/// ```rust
/// use cow_map::cow_map;
/// let defaults = cow_map!(DEFAULTS: i32 => "timeout" => 30, "port" => 8080);
/// let other    = cow_map!(OTHER: i32 => "x" => 1, "y" => 2);
/// assert_eq!(defaults.get("timeout"), Some(&30));
/// ```
///
/// # Key and value types
///
/// ```rust
/// use cow_map::cow_map;
/// let m = cow_map!(&str, i32 => "timeout" => 30, "port" => 8080);
/// assert_eq!(m.get("timeout"), Some(&30));
/// ```
#[macro_export]
macro_rules! cow_map {
    ($name:ident : $v:ty => $($k:expr => $val:expr),* $(,)?) => {{
        static $name: $crate::phf::Map<&'static str, $v> = $crate::phf::phf_map! { $($k => $val),* };
        $crate::CowMap::from_static(&$name)
    }};
    ($v:ty => $($k:expr => $val:expr),* $(,)?) => {{
        static __COW_MAP: $crate::phf::Map<&'static str, $v> = $crate::phf::phf_map! { $($k => $val),* };
        $crate::CowMap::from_static(&__COW_MAP)
    }};
    ($k:ty, $v:ty => $($key:expr => $val:expr),* $(,)?) => {{
        static __COW_MAP: $crate::phf::Map<$k, $v> = $crate::phf::phf_map! { $($key => $val),* };
        $crate::CowMap::from_static(&__COW_MAP)
    }};
}

#[cfg(test)]
mod tests {
    use super::*;
    use phf::phf_map;

    static M: phf::Map<&'static str, i32> = phf_map! {
        "a" => 1,
        "b" => 2,
        "c" => 3,
    };

    #[test]
    fn borrowed_read_only() {
        let map = CowMap::from_static(&M);
        assert!(map.is_borrowed());
        assert_eq!(map.get("a"), Some(&1));
        assert_eq!(map.get("b"), Some(&2));
        assert_eq!(map.get("z"), None);
        assert_eq!(map.len(), 3);
        assert!(map.contains_key("a"));
        assert!(!map.contains_key("z"));
    }

    #[test]
    fn promote_on_insert() {
        let mut map = CowMap::from_static(&M);
        assert!(map.is_borrowed());
        map.insert("d", 4);
        assert!(map.is_owned());
        assert_eq!(map.get("a"), Some(&1));
        assert_eq!(map.get("d"), Some(&4));
        assert_eq!(map.len(), 4);
    }

    #[test]
    fn promote_on_remove() {
        let mut map = CowMap::from_static(&M);
        assert!(map.is_borrowed());
        let v = map.remove("b");
        assert_eq!(v, Some(2));
        assert!(map.is_owned());
        assert_eq!(map.get("b"), None);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn promote_on_get_mut() {
        let mut map = CowMap::from_static(&M);
        assert!(map.is_borrowed());
        if let Some(x) = map.get_mut("a") {
            *x = 10;
        }
        assert!(map.is_owned());
        assert_eq!(map.get("a"), Some(&10));
    }

    #[test]
    fn iter_borrowed() {
        let map = CowMap::from_static(&M);
        let mut pairs: Vec<_> = map.iter().map(|(k, v)| (*k, *v)).collect();
        pairs.sort_by_key(|(k, _)| *k);
        assert_eq!(pairs, [("a", 1), ("b", 2), ("c", 3)]);
    }

    #[test]
    fn owned_empty_and_from_iter() {
        let map: CowMap<&str, i32> = CowMap::owned_empty();
        assert!(map.is_owned());
        assert!(map.is_empty());

        let map: CowMap<_, _> = [(1, "a"), (2, "b")].into_iter().collect();
        assert!(map.is_owned());
        assert_eq!(map.get(&1), Some(&"a"));
    }

    #[test]
    fn borrowed_constructor() {
        let map = CowMap::borrowed(&M);
        assert!(map.is_borrowed());
        assert_eq!(map.get("a"), Some(&1));
    }

    #[test]
    fn cow_map_macro_direct_init() {
        let map = cow_map!(i32 => "x" => 10, "y" => 20);
        assert!(map.is_borrowed());
        assert_eq!(map.get("x"), Some(&10));
        assert_eq!(map.get("y"), Some(&20));
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn cow_map_macro_named() {
        let map = cow_map!(NAMED_MAP: i32 => "p" => 1, "q" => 2);
        assert!(map.is_borrowed());
        assert_eq!(map.get("p"), Some(&1));
        assert_eq!(map.get("q"), Some(&2));
    }

    #[test]
    fn len_and_is_empty() {
        let map = CowMap::from_static(&M);
        assert_eq!(map.len(), 3);
        assert!(!map.is_empty());

        let empty: CowMap<&str, i32> = CowMap::owned_empty();
        assert_eq!(empty.len(), 0);
        assert!(empty.is_empty());
    }

    #[test]
    fn iter_owned() {
        let mut map = CowMap::from_static(&M);
        map.insert("d", 4);
        assert!(map.is_owned());
        let mut pairs: Vec<_> = map.iter().map(|(k, v)| (*k, *v)).collect();
        pairs.sort_by_key(|(k, _)| *k);
        assert_eq!(pairs, [("a", 1), ("b", 2), ("c", 3), ("d", 4)]);
    }

    #[test]
    fn keys_and_values() {
        let map = CowMap::from_static(&M);
        let mut keys: Vec<_> = map.keys().copied().collect();
        keys.sort();
        assert_eq!(keys, ["a", "b", "c"]);
        let mut values: Vec<_> = map.values().copied().collect();
        values.sort();
        assert_eq!(values, [1, 2, 3]);

        let mut map = CowMap::from_static(&M);
        map.insert("d", 4);
        let mut keys: Vec<_> = map.keys().copied().collect();
        keys.sort();
        assert_eq!(keys, ["a", "b", "c", "d"]);
    }

    #[test]
    fn remove_missing_key() {
        let mut map = CowMap::from_static(&M);
        assert!(map.is_borrowed());
        let v = map.remove("z");
        assert_eq!(v, None);
        assert!(map.is_owned());
        assert_eq!(map.len(), 3);
    }

    #[test]
    fn insert_overwrite() {
        let mut map = CowMap::from_static(&M);
        let old = map.insert("b", 20);
        assert_eq!(old, Some(2));
        assert_eq!(map.get("b"), Some(&20));
    }

    #[test]
    fn get_mut_missing_key() {
        let mut map = CowMap::from_static(&M);
        assert!(map.is_borrowed());
        let opt = map.get_mut("z");
        assert!(opt.is_none());
        assert!(map.is_owned());
        assert_eq!(map.len(), 3);
    }

    #[test]
    fn clone_borrowed_stays_borrowed() {
        let map = CowMap::from_static(&M);
        let c = map.clone();
        assert!(c.is_borrowed());
        assert_eq!(c.get("a"), Some(&1));
    }

    #[test]
    fn clone_owned_stays_owned() {
        let mut map = CowMap::from_static(&M);
        map.insert("d", 4);
        let c = map.clone();
        assert!(c.is_owned());
        assert_eq!(c.get("d"), Some(&4));
    }

    #[test]
    fn default_is_owned_empty() {
        let map: CowMap<&str, i32> = CowMap::default();
        assert!(map.is_owned());
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn from_hashmap() {
        let mut h = HashMap::new();
        h.insert("x", 10);
        h.insert("y", 20);
        let map = CowMap::from(h);
        assert!(map.is_owned());
        assert_eq!(map.get("x"), Some(&10));
        assert_eq!(map.get("y"), Some(&20));
    }

    #[test]
    fn from_array() {
        let map = CowMap::from([("p", 1), ("q", 2)]);
        assert!(map.is_owned());
        assert_eq!(map.get("p"), Some(&1));
        assert_eq!(map.get("q"), Some(&2));
    }

    #[test]
    fn to_hashmap_borrowed() {
        let map = CowMap::from_static(&M);
        let hashmap = map.to_hashmap();
        assert_eq!(hashmap.get("a"), Some(&1));
        assert_eq!(hashmap.get("b"), Some(&2));
        assert_eq!(hashmap.len(), 3);
        assert!(map.is_borrowed()); // map unchanged
    }

    #[test]
    fn to_hashmap_owned() {
        let mut map = CowMap::from_static(&M);
        map.insert("d", 4);
        let hashmap = map.to_hashmap();
        assert_eq!(hashmap.get("a"), Some(&1));
        assert_eq!(hashmap.get("d"), Some(&4));
        assert_eq!(hashmap.len(), 4);
    }

    #[test]
    fn into_hashmap_borrowed() {
        let map = CowMap::from_static(&M);
        let hashmap = map.into_hashmap();
        assert_eq!(hashmap.get("a"), Some(&1));
        assert_eq!(hashmap.len(), 3);
    }

    #[test]
    fn into_hashmap_owned() {
        let mut map = CowMap::from_static(&M);
        map.insert("d", 4);
        let hashmap = map.into_hashmap();
        assert_eq!(hashmap.get("a"), Some(&1));
        assert_eq!(hashmap.get("d"), Some(&4));
        assert_eq!(hashmap.len(), 4);
    }

    #[test]
    fn debug_fmt() {
        let map = CowMap::from_static(&M);
        let s = format!("{:?}", map);
        assert!(s.starts_with("Borrowed"));
        assert!(s.contains("a"));
    }
}
