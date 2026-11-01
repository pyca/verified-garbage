//! Reading the JSON test vector files into Rust types: [`json_struct!`]
//! defines a struct and its [`FromJson`] impl, which reads each field from
//! an object by its key, from a file parsed by `serde_json` as a [`Value`].
//!
//! This takes the place of serde's derive, which made `cargo test` take
//! nearly twice as long to build: the tests could not start compiling until
//! `syn` and `serde_derive` had, and the deserializers it generated were a
//! third of the test binary's code. What a field accepts is what the
//! derive's did: an `Option` field may be left out or `null`, a field marked
//! `default` may be left out, and keys that no field reads are ignored.
//!
//! A value that is not what its type reads panics, naming the field: a
//! test of a malformed file fails, as it would on any other broken
//! assumption.
//! Returning `Result`s instead made each field's read return early, past
//! code dropping every field read before it: four times as much code.

use std::collections::BTreeMap;

use serde_json::{Map, Value};

/// A type read from a JSON value.
pub trait FromJson: Sized {
    /// `v`, the value of `key`, as a `Self`; panics, naming `key`, if it is
    /// not one.
    fn from_json(v: &Value, key: &str) -> Self;

    /// The field `key` of an object whose value is `v`, or `None` if the
    /// object leaves it out, which only an `Option` allows.
    fn from_field(v: Option<&Value>, key: &str) -> Self {
        Self::from_json(v.unwrap_or_else(|| panic!("missing field `{key}`")), key)
    }
}

/// Parses `json`, the text of the file `name`, as a `T`; panics if it is
/// not one.
pub fn parse<T: FromJson>(name: &str, json: &str) -> T {
    // `Value`'s `FromStr` is compiled (optimized) in `serde_json`, rather
    // than generically in the test binary.
    let value: Value = json.parse().unwrap_or_else(|e| panic!("{name}: {e}"));
    T::from_json(&value, name)
}

/// `v`, the value of `key`, as an object.
pub fn object<'a>(v: &'a Value, key: &str) -> &'a Map<String, Value> {
    v.as_object()
        .unwrap_or_else(|| panic!("{key}: expected an object, found {v}"))
}

/// The field `key` of the object `o`.
pub fn field<T: FromJson>(o: &Map<String, Value>, key: &str) -> T {
    T::from_field(o.get(key), key)
}

/// The field `key` of the object `o`, or `T`'s default if `o` leaves it out.
pub fn field_or_default<T: FromJson + Default>(o: &Map<String, Value>, key: &str) -> T {
    o.get(key).map_or_else(T::default, |v| T::from_json(v, key))
}

impl FromJson for String {
    fn from_json(v: &Value, key: &str) -> Self {
        let s = v.as_str();
        s.unwrap_or_else(|| panic!("{key}: expected a string, found {v}"))
            .to_owned()
    }
}

impl FromJson for u64 {
    fn from_json(v: &Value, key: &str) -> Self {
        v.as_u64()
            .unwrap_or_else(|| panic!("{key}: expected an unsigned integer, found {v}"))
    }
}

impl FromJson for usize {
    fn from_json(v: &Value, key: &str) -> Self {
        let n = u64::from_json(v, key);
        usize::try_from(n).unwrap_or_else(|e| panic!("{key}: {n}: {e}"))
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl FromJson for u32 {
    fn from_json(v: &Value, key: &str) -> Self {
        let n = u64::from_json(v, key);
        u32::try_from(n).unwrap_or_else(|e| panic!("{key}: {n}: {e}"))
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
impl FromJson for bool {
    fn from_json(v: &Value, key: &str) -> Self {
        v.as_bool()
            .unwrap_or_else(|| panic!("{key}: expected a boolean, found {v}"))
    }
}

/// Any value, kept as it is.
#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
impl FromJson for Value {
    fn from_json(v: &Value, _: &str) -> Self {
        v.clone()
    }
}

/// `null` is `None`, as is a field left out.
impl<T: FromJson> FromJson for Option<T> {
    fn from_json(v: &Value, key: &str) -> Self {
        (!v.is_null()).then(|| T::from_json(v, key))
    }

    fn from_field(v: Option<&Value>, key: &str) -> Self {
        v.and_then(|v| Self::from_json(v, key))
    }
}

impl<T: FromJson> FromJson for Vec<T> {
    fn from_json(v: &Value, key: &str) -> Self {
        let items = v
            .as_array()
            .unwrap_or_else(|| panic!("{key}: expected an array, found {v}"));
        // A loop: `collect`ing compiled iterator adapters for every `T`.
        let mut all = Vec::with_capacity(items.len());
        for x in items {
            all.push(T::from_json(x, key));
        }
        all
    }
}

/// An object, its keys in order.
impl<T: FromJson> FromJson for BTreeMap<String, T> {
    fn from_json(v: &Value, key: &str) -> Self {
        let mut all = BTreeMap::new();
        for (k, x) in object(v, key) {
            all.insert(k.clone(), T::from_json(x, k));
        }
        all
    }
}

/// Defines a struct, as written, and its [`FromJson`] impl, which reads an
/// object with a key for each field: the field's name unless the field
/// says `#[json(rename = "…")]`. A field may also say `#[json(default)]`
/// (after `rename`, comma separated): its type's default if the object
/// leaves it out. Or `#[json(flatten)]`: read from the object itself, as
/// the struct is, which then has the fields of both. A generic struct's
/// parameters must be [`FromJson`]. Its fields' documentation is kept; no
/// other attribute is allowed on them.
#[macro_export]
macro_rules! json_struct {
    (
        $(#[$attr:meta])*
        $vis:vis struct $name:ident $(<$($param:ident),*>)? {
            $(
                $(#[doc = $doc:literal])*
                $(#[json($($opt:tt)*)])?
                $fvis:vis $field:ident: $ty:ty
            ),* $(,)?
        }
    ) => {
        $(#[$attr])*
        $vis struct $name $(<$($param),*>)? {
            $(
                $(#[doc = $doc])*
                $fvis $field: $ty,
            )*
        }

        impl $(<$($param: $crate::json::FromJson),*>)? $crate::json::FromJson
            for $name $(<$($param),*>)?
        {
            fn from_json(v: &serde_json::Value, key: &str) -> Self {
                #[allow(unused_variables)]
                let o = $crate::json::object(v, key);
                Self { $($field: $crate::json_field!(v, key, o, $field $(, $($opt)*)?),)* }
            }
        }
    };
}

/// A field of [`json_struct!`]'s `from_json`: of the value `$v` of `$key`,
/// the object `$o`.
#[macro_export]
#[doc(hidden)]
macro_rules! json_field {
    ($v:ident, $key:ident, $o:ident, $field:ident) => {
        $crate::json::field($o, stringify!($field))
    };
    ($v:ident, $key:ident, $o:ident, $field:ident, rename = $name:literal) => {
        $crate::json::field($o, $name)
    };
    ($v:ident, $key:ident, $o:ident, $field:ident, default) => {
        $crate::json::field_or_default($o, stringify!($field))
    };
    ($v:ident, $key:ident, $o:ident, $field:ident, rename = $name:literal, default) => {
        $crate::json::field_or_default($o, $name)
    };
    ($v:ident, $key:ident, $o:ident, $field:ident, flatten) => {
        $crate::json::FromJson::from_json($v, $key)
    };
}
