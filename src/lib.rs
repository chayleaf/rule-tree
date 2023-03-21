use path_trait::{BorrowedPath, OwnedPath};
use std::{borrow::Borrow, collections::HashMap, hash::Hash};

/// This module contains the tree path trait.
pub mod path_trait {
    use std::ffi::{OsStr, OsString};

    /// Tree path (owned)
    pub trait OwnedPath<Seg> {
        /// Iterator over path segments
        type Iter<'a>: Iterator<Item = Seg>
        where
            Self: 'a;
        /// Split tree path into segments
        fn split(&self) -> Self::Iter<'_>;
    }
    /// Tree path (borrowed)
    pub trait BorrowedPath<Seg: ?Sized> {
        /// Iterator over path segments
        type Iter<'a>: Iterator<Item = &'a Seg>
        where
            Self: 'a,
            Seg: 'a;
        /// Split tree path into segments
        fn split(&self) -> Self::Iter<'_>;
    }
    /// An iterator equivalent to `.map(|x| x.to_owned())`
    pub struct ToOwnedIter<I: Iterator>(I)
    where
        I::Item: ToOwned;
    impl<'a, T: 'a + ToOwned + ?Sized, I: Iterator<Item = &'a T>> Iterator for ToOwnedIter<I> {
        type Item = T::Owned;
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(|x| x.to_owned())
        }
    }
    // impl for arrays
    impl<T: Clone, const N: usize> OwnedPath<T> for [T; N] {
        type Iter<'a> = std::iter::Cloned<std::slice::Iter<'a, T>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter().cloned()
        }
    }
    impl<T, const N: usize> BorrowedPath<T> for [T; N] {
        type Iter<'a> = std::slice::Iter<'a, T> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    // impl for slices
    impl<T: Clone> OwnedPath<T> for [T] {
        type Iter<'a> = std::iter::Cloned<std::slice::Iter<'a, T>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter().cloned()
        }
    }
    impl<T> BorrowedPath<T> for [T] {
        type Iter<'a> = std::slice::Iter<'a, T> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    impl<'b, T: Clone> OwnedPath<T> for &'b [T] {
        type Iter<'a> = std::iter::Cloned<std::slice::Iter<'a, T>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter().cloned()
        }
    }
    impl<'b, T> BorrowedPath<T> for &'b [T] {
        type Iter<'a> = std::slice::Iter<'a, T> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    impl<'b, T: Clone> OwnedPath<T> for &'b mut [T] {
        type Iter<'a> = std::iter::Cloned<std::slice::Iter<'a, T>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter().cloned()
        }
    }
    impl<'b, T> BorrowedPath<T> for &'b mut [T] {
        type Iter<'a> = std::slice::Iter<'a, T> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    // impl for vectors
    impl<T: Clone> OwnedPath<T> for Vec<T> {
        type Iter<'a> = std::iter::Cloned<std::slice::Iter<'a, T>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter().cloned()
        }
    }
    impl<T> BorrowedPath<T> for Vec<T> {
        type Iter<'a> = std::slice::Iter<'a, T> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    impl<'b, T: Clone> OwnedPath<T> for &'b Vec<T> {
        type Iter<'a> = std::iter::Cloned<std::slice::Iter<'a, T>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter().cloned()
        }
    }
    impl<'b, T> BorrowedPath<T> for &'b Vec<T> {
        type Iter<'a> = std::slice::Iter<'a, T> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    impl<'b, T: Clone> OwnedPath<T> for &'b mut Vec<T> {
        type Iter<'a> = std::iter::Cloned<std::slice::Iter<'a, T>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter().cloned()
        }
    }
    impl<'b, T> BorrowedPath<T> for &'b mut Vec<T> {
        type Iter<'a> = std::slice::Iter<'a, T> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    // impl for path
    impl OwnedPath<OsString> for std::path::Path {
        type Iter<'a> = ToOwnedIter<std::path::Iter<'a>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            ToOwnedIter(self.iter())
        }
    }
    impl BorrowedPath<OsStr> for std::path::Path {
        type Iter<'a> = std::path::Iter<'a> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    impl<'b> OwnedPath<OsString> for &'b std::path::Path {
        type Iter<'a> = ToOwnedIter<std::path::Iter<'a>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            ToOwnedIter(self.iter())
        }
    }
    impl<'b> BorrowedPath<OsStr> for &'b std::path::Path {
        type Iter<'a> = std::path::Iter<'a> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    impl<'b> OwnedPath<OsString> for &'b mut std::path::Path {
        type Iter<'a> = ToOwnedIter<std::path::Iter<'a>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            ToOwnedIter(self.iter())
        }
    }
    impl<'b> BorrowedPath<OsStr> for &'b mut std::path::Path {
        type Iter<'a> = std::path::Iter<'a> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    // impl for pathbuf
    impl OwnedPath<OsString> for std::path::PathBuf {
        type Iter<'a> = ToOwnedIter<std::path::Iter<'a>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            ToOwnedIter(self.iter())
        }
    }
    impl BorrowedPath<OsStr> for std::path::PathBuf {
        type Iter<'a> = std::path::Iter<'a> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    impl<'b> OwnedPath<OsString> for &'b std::path::PathBuf {
        type Iter<'a> = ToOwnedIter<std::path::Iter<'a>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            ToOwnedIter(self.iter())
        }
    }
    impl<'b> BorrowedPath<OsStr> for &'b std::path::PathBuf {
        type Iter<'a> = std::path::Iter<'a> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
    impl<'b> OwnedPath<OsString> for &'b mut std::path::PathBuf {
        type Iter<'a> = ToOwnedIter<std::path::Iter<'a>> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            ToOwnedIter(self.iter())
        }
    }
    impl<'b> BorrowedPath<OsStr> for &'b mut std::path::PathBuf {
        type Iter<'a> = std::path::Iter<'a> where Self: 'a;
        fn split(&self) -> Self::Iter<'_> {
            self.iter()
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeRule<T> {
    value: T,
    conditional: bool,
}

impl<T> TreeRule<T> {
    /// Create a rule that overwrites all preceding rules and applies this value instead.
    pub fn overwrite(value: T) -> Self {
        Self {
            value,
            conditional: false,
        }
    }
    /// Creates a rule that prepend this value to the list of rules. The value picking logic must be written by you.
    pub fn prepend(value: T) -> Self {
        Self {
            value,
            conditional: true,
        }
    }
    /// Get inner value.
    pub fn get(&self) -> &T {
        &self.value
    }
}

/// If you want to store a ruleset about certain directories, use OsString as K and path
/// Path/PathBuf to functions that take `path`. Otherwise, you can use anything as K if you provide
/// arrays/vectors/slices of K as the path.
///
/// For V, anything goes, that's whatever you want to store as the rules.
#[derive(Clone, Debug)]
pub struct RulesTree<K, V> {
    rules: HashMap<String, Vec<TreeRule<V>>>,
    trees: HashMap<K, Self>,
}

impl<K, V> Default for RulesTree<K, V> {
    fn default() -> Self {
        Self {
            rules: HashMap::new(),
            trees: HashMap::new(),
        }
    }
}

impl<K, V> RulesTree<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: Eq + Hash, V> RulesTree<K, V> {
    /// Add a rule at a path. If path is empty, a top level rule will be added.
    pub fn add_rule<P: OwnedPath<K>>(&mut self, path: P, rule_name: &str, rule: TreeRule<V>) {
        self.add_rule_internal(path.split(), rule_name, rule);
    }
    fn add_rule_internal<I: Iterator<Item = K>>(
        &mut self,
        mut path: I,
        rule_name: &str,
        rule: TreeRule<V>,
    ) {
        if let Some(seg) = path.next() {
            self.trees
                .entry(seg)
                .or_default()
                .add_rule_internal(path, rule_name, rule);
        } else if let Some(rules) = self.rules.get_mut(rule_name) {
            if rule.conditional {
                rules.push(rule);
            } else {
                *rules = vec![rule];
            }
        } else {
            self.rules.insert(rule_name.to_owned(), vec![rule]);
        }
    }
    /// Get all rule values at a path. See [`TreeRule`] methods for more info on which rules you will get.
    pub fn get_rules<T: Hash + Eq + ?Sized, P: BorrowedPath<T> + ?Sized>(
        &self,
        path: &P,
        rule_name: &str,
    ) -> Vec<&TreeRule<V>>
    where
        K: Borrow<T>,
    {
        self.get_rules_internal(path.split(), rule_name).0
    }
    fn get_rules_internal<'a, T: 'a + Hash + Eq + ?Sized, I: Iterator<Item = &'a T>>(
        &self,
        mut path: I,
        rule_name: &str,
    ) -> (Vec<&TreeRule<V>>, bool)
    where
        K: Borrow<T>,
    {
        let mut ret = if let Some(seg) = path.next() {
            if let Some(tree) = self.trees.get(seg) {
                let (ret, fin) = tree.get_rules_internal(path, rule_name);
                if fin {
                    return (ret, fin);
                }
                ret
            } else {
                vec![]
            }
        } else {
            vec![]
        };
        if let Some(rules) = self.rules.get(rule_name) {
            for rule in rules.iter().rev() {
                ret.push(rule);
                if !rule.conditional {
                    return (ret, true);
                }
            }
        }
        (ret, false)
    }
    pub fn top_level_rules(&self, key: &str) -> Option<impl IntoIterator<Item = &TreeRule<V>>> {
        self.rules.get(key).map(|x| x.as_slice())
    }
    pub fn children(&self) -> impl IntoIterator<Item = (&K, &Self)> {
        &self.trees
    }
}

impl<K: Eq + Hash + ToOwned<Owned = K>, V: Clone + Eq> RulesTree<K, V> {
    /// Remove all prepend rules; then remove redundant rules
    /// if allow_propagate is true, then if all subtrees have the same value and this sublist doesn't
    /// have a value, subtrees' type becomes self's type
    pub fn simplify(&mut self, key: &str, allow_propagate: bool) {
        self.simplify_internal(key, None, allow_propagate);
    }
    /// returns shouldRemove
    fn simplify_internal(
        &mut self,
        key: &str,
        parent_val: Option<&V>,
        allow_propagate: bool,
    ) -> bool {
        // change lifetime
        let mut parent_val = parent_val;
        let mut force_keep = false;
        let Self { rules, trees } = self;
        if let Some(val) = rules.get_mut(key) {
            if let Some(_val) = val.iter().find(|x| !x.conditional) {
                let val2 = val.drain(..).find(|x| !x.conditional).unwrap();
                if parent_val != Some(val2.get()) {
                    *val = vec![val2];
                    parent_val = Some(&val.get(0).unwrap().value);
                    force_keep = true;
                } else {
                    *val = vec![];
                }
            } else {
                *val = vec![];
            }
        }
        let mut to_remove = Vec::new();
        for (k, v) in &mut *trees {
            if v.simplify_internal(key, parent_val, allow_propagate) {
                to_remove.push(k.to_owned());
            }
        }
        for k in to_remove {
            trees.remove(&k);
        }
        if allow_propagate && parent_val.is_none() && !self.trees.is_empty() {
            let mut it = self.trees.iter();
            if let Some(t) = it
                .next()
                .and_then(|x| x.1.rules.get(key))
                .filter(|x| !x.is_empty())
            {
                if it.all(|x| x.1.rules.get(key) == Some(t)) {
                    let t = t.to_owned();
                    self.trees.clear();
                    self.rules.insert(key.to_owned(), t);
                    force_keep = true;
                }
            }
        }
        self.trees.is_empty() && !force_keep
    }
}

#[cfg(test)]
mod tests {
    use std::{ffi::OsString, path::PathBuf};

    use super::*;

    #[test]
    fn it_works() {
        let mut rules = RulesTree::<&'static str, &'static str>::new();
        rules.add_rule(["a", "b", "c"], "test", TreeRule::overwrite("test_rule"));
        rules.add_rule(
            ["a", "b", "c", "d"],
            "test",
            TreeRule::overwrite("test_rule2"),
        );
        rules.add_rule(
            ["a", "b", "c", "d", "e"],
            "test",
            TreeRule::prepend("test_rule3"),
        );
        rules.add_rule(
            ["a", "b", "c", "d", "e", "f"],
            "test",
            TreeRule::overwrite("test_rule4"),
        );
        assert_eq!(
            rules.get_rules(&["a", "b", "c", "e"], "test"),
            vec![&TreeRule::overwrite("test_rule")]
        );
        assert_eq!(
            rules.get_rules(&["a", "b", "c", "d", "f"], "test"),
            vec![&TreeRule::overwrite("test_rule2")]
        );
        assert_eq!(
            rules.get_rules(&["a", "b", "b"], "test"),
            Vec::<&TreeRule<_>>::new()
        );
        assert_eq!(
            rules.get_rules(&["a", "b", "c", "d", "e"], "test"),
            vec![
                &TreeRule::prepend("test_rule3"),
                &TreeRule::overwrite("test_rule2")
            ]
        );
        assert_eq!(
            rules.get_rules(&["a", "b", "c", "d", "e", "f"], "test"),
            vec![&TreeRule::overwrite("test_rule4")]
        );
        let mut rules = RulesTree::<OsString, &'static str>::new();
        let path = PathBuf::from("test");
        rules.add_rule(path.clone(), "test", TreeRule::overwrite("test_rule"));
        let rules = rules.get_rules(path.as_path(), "test");
        assert_eq!(rules, vec![&TreeRule::overwrite("test_rule")]);
    }
}
