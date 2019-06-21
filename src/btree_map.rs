//! A wrapper around
//! [`std::collections::BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html)
//! that guarantees that it will never be empty.
#![macro_use]

use std::{
    borrow::Borrow,
    collections::btree_map::{
        BTreeMap, Entry as StdEntry, Iter, IterMut, Keys, OccupiedEntry as StdOccupiedEntry, Range,
        RangeMut, VacantEntry as StdVacantEntry, Values, ValuesMut,
    },
    convert::TryFrom,
    error::Error,
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    iter::FromIterator,
    num::NonZeroUsize,
    ops::{Index, RangeBounds},
};

#[cfg(feature = "serde")]
use serde::{
    de::{Deserializer, Error as DeserializationError},
    Deserialize, Serialize,
};

/// A convenience macro for constructing `BTreeMap1`.
#[macro_export]
macro_rules! btree_map_1 {
    () => {
        compile_error!("at least one element must be specified for a BTreeMap1 -- try `btree_map_1!(key, value, ...)`")
    };
    (($key: expr, $value: expr) $(, ($other_keys: expr, $other_values: expr))* $(,)?) => {{
        let mut map = map1::BTreeMap1::new($key, $value);
        $(map.insert($other_keys, $other_values);)*
        map
    }};
}

/// A wrapper around
/// [`std::collections::BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html)
/// that guarantees that it will never be empty.
#[derive(Clone, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(serialize = "K: std::cmp::Ord + serde::Serialize, V: serde::Serialize"))
)]
pub struct BTreeMap1<K, V>(pub BTreeMap<K, V>);

/// An error returned when an operation associated with `BTreeMap1` would result in it being empty.
#[allow(missing_copy_implementations)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BTreeEmptyError;

impl Display for BTreeEmptyError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let Self = self;
        write!(f, "cannot construct BTreeMap1 from empty map")
    }
}

impl Error for BTreeEmptyError {}

impl<K: Ord, V> TryFrom<BTreeMap<K, V>> for BTreeMap1<K, V> {
    type Error = BTreeEmptyError;

    fn try_from(b: BTreeMap<K, V>) -> Result<Self, Self::Error> {
        if b.is_empty() {
            Err(BTreeEmptyError)
        } else {
            Ok(Self(b))
        }
    }
}

#[cfg(feature = "serde")]
impl<'de, K, V> Deserialize<'de> for BTreeMap1<K, V>
where
    K: Deserialize<'de> + Ord,
    V: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let map = BTreeMap::deserialize(deserializer)?;
        if map.is_empty() {
            Err(DeserializationError::custom(BTreeEmptyError))
        } else {
            Ok(Self(map))
        }
    }
}

impl<K: Ord, V> Into<BTreeMap<K, V>> for BTreeMap1<K, V> {
    fn into(self) -> BTreeMap<K, V> {
        self.0
    }
}

impl<'a, K: 'a, V: 'a> IntoIterator for &'a BTreeMap1<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = <&'a BTreeMap<K, V> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<K, V> IntoIterator for BTreeMap1<K, V> {
    type Item = (K, V);
    type IntoIter = <BTreeMap<K, V> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, K: 'a, V: 'a> IntoIterator for &'a mut BTreeMap1<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = <&'a mut BTreeMap<K, V> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`BTreeMap1`].
///
/// [`BTreeMap1`]: struct.BTreeMap1.html
/// [`entry`]: struct.BTreeMap1.html#method.entry
pub enum Entry<'a, K: 'a, V: 'a> {
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V>),
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),
}

/// A view into a vacant entry in a `BTreeMap1`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
pub struct VacantEntry<'a, K: 'a, V: 'a> {
    inner: StdVacantEntry<'a, K, V>,
}

impl<K: Debug + Ord, V> Debug for VacantEntry<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_tuple("VacantEntry").field(self.key()).finish()
    }
}

/// A view into an occupied entry in a `BTreeMap1`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
pub struct OccupiedEntry<'a, K: 'a, V: 'a> {
    inner: StdOccupiedEntry<'a, K, V>,
    tree_len: NonZeroUsize,
}

impl<K: Debug + Ord, V: Debug> Debug for OccupiedEntry<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("OccupiedEntry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

impl<K: Ord, V> BTreeMap1<K, V> {
    /// Makes a new BTreeMap1 with a single key-value pair.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let mut map = BTreeMap1::new(2, "b");
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, "a");
    /// ```
    pub fn new(key: K, value: V) -> Self {
        let mut this = BTreeMap::new();
        this.insert(key, value);
        Self(this)
    }

    // FIXME: Need to think about design for `clear` -- do we care?

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let map = BTreeMap1::new(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.0.get(key)
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let map = BTreeMap1::new(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.0.contains_key(key)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let mut map = BTreeMap1::new(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    // See `get` for implementation notes, this is basically a copy-paste with mut's added
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.0.get_mut(key)
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [module-level
    /// documentation] for more.
    ///
    /// [module-level documentation]: index.html#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let mut map = BTreeMap1::new(0, "foo");
    /// assert_eq!(map.insert(37, "a"), None);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.0.insert(key, value)
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::{btree_map::BTreeEmptyError, btree_map_1};
    ///
    /// let mut map = btree_map_1![(1, "a"), (2, "b")];
    /// assert_eq!(map.try_remove(&1), Some(Ok("a")));
    /// assert_eq!(map.try_remove(&1), None);
    /// assert_eq!(map.try_remove(&2), Some(Err(BTreeEmptyError)));
    /// ```
    ///
    /// # Performance
    ///
    /// Note that internally this implementation will search the tree twice in the case that the
    /// key exists. If calling `Clone::clone` on your keys is cheap, consider using
    /// `try_remove_entry` instead.
    /// ```
    pub fn try_remove<Q: ?Sized>(&mut self, key: &Q) -> Option<Result<V, BTreeEmptyError>>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        let len = self.len().get();
        self.get(key).map(|_v| ()).map(|()| {
            if len == 1 {
                Err(BTreeEmptyError)
            } else {
                Ok(self.0.remove(key).unwrap())
            }
        })
    }

    /// Moves all elements from `other` into `Self`, leaving `other` empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use {std::collections::BTreeMap, map1::btree_map_1};
    ///
    /// let mut a = btree_map_1![
    ///     (1, "a"),
    ///     (2, "b"),
    ///     (3, "c"),
    /// ];
    ///
    /// let mut b = BTreeMap::new();
    /// b.insert(3, "d");
    /// b.insert(4, "e");
    /// b.insert(5, "f");
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.len().get(), 5);
    /// assert_eq!(b.len(), 0);
    ///
    /// assert_eq!(a[&1], "a");
    /// assert_eq!(a[&2], "b");
    /// assert_eq!(a[&3], "d");
    /// assert_eq!(a[&4], "e");
    /// assert_eq!(a[&5], "f");
    /// ```
    pub fn append(&mut self, other: &mut BTreeMap<K, V>) {
        self.0.append(other)
    }

    /// Constructs a double-ended iterator over a sub-range of elements in the map.
    /// The simplest way is to use the range syntax `min..max`, thus `range(min..max)` will
    /// yield elements from min (inclusive) to max (exclusive).
    /// The range may also be entered as `(Bound<T>, Bound<T>)`, so for example
    /// `range((Excluded(4), Included(10)))` will yield a left-exclusive, right-inclusive
    /// range from 4 to 10.
    ///
    /// # Panics
    ///
    /// Panics if range `start > end`.
    /// Panics if range `start == end` and both bounds are `Excluded`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::btree_map_1;
    /// use std::ops::Bound::Included;
    ///
    /// let map = btree_map_1![(3, "a"), (5, "b"), (8, "c")];
    /// for (&key, &value) in map.range((Included(&4), Included(&8))) {
    ///     println!("{}: {}", key, value);
    /// }
    /// assert_eq!(Some((&5, &"b")), map.range(4..).next());
    /// ```
    pub fn range<T: ?Sized, R>(&self, range: R) -> Range<'_, K, V>
    where
        T: Ord,
        K: Borrow<T>,
        R: RangeBounds<T>,
    {
        self.0.range(range)
    }

    /// Constructs a mutable double-ended iterator over a sub-range of elements in the map.
    /// The simplest way is to use the range syntax `min..max`, thus `range(min..max)` will
    /// yield elements from min (inclusive) to max (exclusive).
    /// The range may also be entered as `(Bound<T>, Bound<T>)`, so for example
    /// `range((Excluded(4), Included(10)))` will yield a left-exclusive, right-inclusive
    /// range from 4 to 10.
    ///
    /// # Panics
    ///
    /// Panics if range `start > end`.
    /// Panics if range `start == end` and both bounds are `Excluded`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let mut map: BTreeMap1<&str, i32> = BTreeMap1::try_from_iter(
    ///     ["Alice", "Bob", "Carol", "Cheryl"].iter().map(|&s| (s, 0))
    /// ).unwrap();
    /// for (_, balance) in map.range_mut("B".."Cheryl") {
    ///     *balance += 100;
    /// }
    /// for (name, balance) in &map {
    ///     println!("{} => {}", name, balance);
    /// }
    /// ```
    pub fn range_mut<T: ?Sized, R>(&mut self, range: R) -> RangeMut<'_, K, V>
    where
        T: Ord,
        K: Borrow<T>,
        R: RangeBounds<T>,
    {
        self.0.range_mut(range)
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let mut count: BTreeMap1<&str, usize> = BTreeMap1::new("a", 0);
    ///
    /// // count the number of occurrences of letters in the vec
    /// for x in vec!["a","b","a","c","a","b"] {
    ///     *count.entry(x).or_insert(0) += 1;
    /// }
    ///
    /// assert_eq!(count["a"], 3);
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        let tree_len = self.len();
        match self.0.entry(key) {
            StdEntry::Vacant(inner) => Entry::Vacant(VacantEntry { inner }),
            StdEntry::Occupied(inner) => Entry::Occupied(OccupiedEntry { tree_len, inner }),
        }
    }

    /// Splits the collection into two at the given key. Returns a tuple pair of `BTreeMap`; the
    /// first contains everything up to (but not including) the given key, and the second contains
    /// everything after (and including) the given key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::btree_map_1;
    ///
    /// let a = btree_map_1![
    ///     (1, "a"),
    ///     (2, "b"),
    ///     (3, "c"),
    ///     (17, "d"),
    ///     (41, "e"),
    /// ];
    ///
    /// let (a, b) = a.split(&3);
    ///
    /// assert_eq!(a.len(), 2);
    /// assert_eq!(b.len(), 3);
    ///
    /// assert_eq!(a[&1], "a");
    /// assert_eq!(a[&2], "b");
    ///
    /// assert_eq!(b[&3], "c");
    /// assert_eq!(b[&17], "d");
    /// assert_eq!(b[&41], "e");
    /// ```
    pub fn split<Q: ?Sized + Ord>(mut self, key: &Q) -> (BTreeMap<K, V>, BTreeMap<K, V>)
    where
        K: Borrow<Q>,
    {
        let new = self.0.split_off(key);
        (self.0, new)
    }

    /// Attempts to create a value from an iterator. Returns an error if the iterator yields no
    /// items.
    pub fn try_from_iter<I>(iter: I) -> Result<Self, BTreeEmptyError>
    where
        I: Iterator<Item = (K, V)>,
    {
        Self::try_from(BTreeMap::from_iter(iter))
    }
}

impl<K: Ord, V> Extend<(K, V)> for BTreeMap1<K, V> {
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        iter.into_iter().for_each(move |(k, v)| {
            self.insert(k, v);
        });
    }
}

impl<'a, K: Ord + Copy, V: Copy> Extend<(&'a K, &'a V)> for BTreeMap1<K, V> {
    fn extend<I: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: I) {
        self.extend(iter.into_iter().map(|(&key, &value)| (key, value)));
    }
}

impl<K: Ord, Q: ?Sized, V> Index<&Q> for BTreeMap1<K, V>
where
    K: Borrow<Q>,
    Q: Ord,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `BTreeMap1`.
    #[inline]
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

#[allow(clippy::len_without_is_empty)]
impl<K: Ord, V> BTreeMap1<K, V> {
    /// Gets an iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::btree_map_1;
    ///
    /// let map = btree_map_1![
    ///     (3, "c"),
    ///     (2, "b"),
    ///     (1, "a"),
    /// ];
    ///
    /// for (key, value) in map.iter() {
    ///     println!("{}: {}", key, value);
    /// }
    ///
    /// let (first_key, first_value) = map.iter().next().unwrap();
    /// assert_eq!((*first_key, *first_value), (1, "a"));
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        self.0.iter()
    }

    /// Gets a mutable iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::btree_map_1;
    ///
    /// let mut map = btree_map_1![
    ///     ("c", 3),
    ///     ("b", 2),
    ///     ("a", 1),
    /// ];
    ///
    /// // add 10 to the value if the key isn't "a"
    /// for (key, value) in map.iter_mut() {
    ///     if key != &"a" {
    ///         *value += 10;
    ///     }
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        self.0.iter_mut()
    }

    /// Gets an iterator over the keys of the map, in sorted order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::btree_map_1;
    ///
    /// let a = btree_map_1![
    ///     (2, "b"),
    ///     (1, "a"),
    /// ];
    ///
    /// let keys: Vec<_> = a.keys().cloned().collect();
    /// assert_eq!(keys, [1, 2]);
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        self.0.keys()
    }

    /// Gets an iterator over the values of the map, in order by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::btree_map_1;
    ///
    /// let a = btree_map_1![
    ///     (1, "hello"),
    ///     (2, "goodbye"),
    /// ];
    ///
    /// let values: Vec<&str> = a.values().cloned().collect();
    /// assert_eq!(values, ["hello", "goodbye"]);
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        self.0.values()
    }

    /// Gets a mutable iterator over the values of the map, in order by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::btree_map_1;
    ///
    /// let mut a = btree_map_1![
    ///     (1, "hello".to_owned()),
    ///     (2, "goodbye".to_owned()),
    /// ];
    ///
    /// for value in a.values_mut() {
    ///     value.push_str("!");
    /// }
    ///
    /// let values: Vec<String> = a.values().cloned().collect();
    /// assert_eq!(values, [String::from("hello!"),
    ///                     String::from("goodbye!")]);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        self.0.values_mut()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let mut a = BTreeMap1::new(2, "b");
    /// assert_eq!(a.len().get(), 1);
    /// a.insert(1, "a");
    /// assert_eq!(a.len().get(), 2);
    /// ```
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> NonZeroUsize {
        debug_assert!(!self.0.is_empty());
        unsafe { NonZeroUsize::new_unchecked(self.0.len()) }
    }
}

impl<'a, K: Ord, V> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeMap;
    ///
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// ```
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeMap;
    ///
    /// let mut map: BTreeMap<&str, String> = BTreeMap::new();
    /// let s = "hoho".to_string();
    ///
    /// map.entry("poneyland").or_insert_with(|| s);
    ///
    /// assert_eq!(map["poneyland"], "hoho".to_string());
    /// ```
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeMap;
    ///
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        match *self {
            Entry::Occupied(ref entry) => entry.key(),
            Entry::Vacant(ref entry) => entry.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeMap;
    ///
    /// let mut map: BTreeMap<&str, usize> = BTreeMap::new();
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 43);
    /// ```
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

impl<'a, K: Ord, V: Default> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// use std::collections::BTreeMap;
    ///
    /// let mut map: BTreeMap<&str, Option<usize>> = BTreeMap::new();
    /// map.entry("poneyland").or_default();
    ///
    /// assert_eq!(map["poneyland"], None);
    /// # }
    /// ```
    pub fn or_default(self) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

impl<'a, K: Ord, V> VacantEntry<'a, K, V> {
    /// Gets a reference to the key that would be used when inserting a value
    /// through the VacantEntry.
    ///
    /// # Examples
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let mut map: BTreeMap1<&str, usize> = BTreeMap1::new("other", 1);
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        self.inner.key()
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use map1::btree_map::{Entry, BTreeMap1};
    ///
    /// let mut map: BTreeMap1<&str, usize> = BTreeMap1::new("other", 1);
    ///
    /// if let Entry::Vacant(v) = map.entry("poneyland") {
    ///     v.into_key();
    /// }
    /// ```
    pub fn into_key(self) -> K {
        self.inner.into_key()
    }

    /// Sets the value of the entry with the `VacantEntry`'s key,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let mut count: BTreeMap1<&str, usize> = BTreeMap1::new("a", 0);
    ///
    /// // count the number of occurrences of letters in the vec
    /// for x in vec!["a","b","a","c","a","b"] {
    ///     *count.entry(x).or_insert(0) += 1;
    /// }
    ///
    /// assert_eq!(count["a"], 3);
    /// ```
    pub fn insert(self, value: V) -> &'a mut V {
        self.inner.insert(value)
    }
}

impl<'a, K: Ord, V> OccupiedEntry<'a, K, V> {
    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use map1::BTreeMap1;
    ///
    /// let mut map: BTreeMap1<&str, usize> = BTreeMap1::new("other", 1);
    /// map.entry("poneyland").or_insert(12);
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        self.inner.key()
    }

    /// Take ownership of the key and value from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use map1::btree_map::BTreeEmptyError;
    /// use map1::{btree_map::Entry, btree_map_1, BTreeMap1};
    ///
    /// let mut map: BTreeMap1<&str, usize> = btree_map_1![
    ///     ("poneyland", 12),
    ///     ("other", 1),
    /// ];
    ///
    /// # let mut thing = || -> Result<(), BTreeEmptyError> {
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     // We delete the entry from the map.
    ///     o.try_remove_entry()?;
    /// }
    /// # Ok(())
    /// # };
    /// # thing().unwrap();
    ///
    /// // If now try to get the value, it will panic:
    /// // println!("{}", map["poneyland"]);
    /// ```
    pub fn try_remove_entry(self) -> Result<(K, V), BTreeEmptyError> {
        if self.tree_len.get() == 1 {
            Err(BTreeEmptyError)
        } else {
            Ok(self.inner.remove_entry())
        }
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use map1::btree_map::{BTreeMap1, Entry};
    ///
    /// let mut map: BTreeMap1<&str, usize> = BTreeMap1::new("other", 1);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.get(), &12);
    /// }
    /// ```
    pub fn get(&self) -> &V {
        self.inner.get()
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` that may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: #method.into_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use map1::btree_map::{BTreeMap1, Entry};
    ///
    /// let mut map: BTreeMap1<&str, usize> = BTreeMap1::new("other", 1);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    ///
    ///     // We can use the same Entry multiple times.
    ///     *o.get_mut() += 2;
    /// }
    /// assert_eq!(map["poneyland"], 24);
    /// ```
    pub fn get_mut(&mut self) -> &mut V {
        self.inner.get_mut()
    }

    /// Converts the entry into a mutable reference to its value.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: #method.get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use map1::btree_map::{BTreeMap1, Entry};
    ///
    /// let mut map: BTreeMap1<&str, usize> = BTreeMap1::new("other", 1);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     *o.into_mut() += 10;
    /// }
    /// assert_eq!(map["poneyland"], 22);
    /// ```
    pub fn into_mut(self) -> &'a mut V {
        self.inner.into_mut()
    }

    /// Sets the value of the entry with the `OccupiedEntry`'s key,
    /// and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use map1::btree_map::{BTreeMap1, Entry};
    ///
    /// let mut map: BTreeMap1<&str, usize> = BTreeMap1::new("other", 1);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    /// assert_eq!(map["poneyland"], 15);
    /// ```
    pub fn insert(&mut self, value: V) -> V {
        self.inner.insert(value)
    }

    /// Takes the value of the entry out of the map, and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use map1::btree_map::{BTreeMap1, Entry};
    ///
    /// let mut map: BTreeMap1<&str, usize> = BTreeMap1::new("other", 1);
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.try_remove(), Ok(12));
    /// }
    /// // If we try to get "poneyland"'s value, it'll panic:
    /// // println!("{}", map["poneyland"]);
    /// ```
    pub fn try_remove(self) -> Result<V, BTreeEmptyError> {
        if self.tree_len.get() == 1 {
            Err(BTreeEmptyError)
        } else {
            Ok(self.inner.remove())
        }
    }
}
