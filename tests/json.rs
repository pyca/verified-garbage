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

use std::collections::BTreeMap;

use serde_json::{Map, Value};

/// A type read from a JSON value. An error is a message saying where in
/// the value it is, for the test reading the file to panic with.
pub trait FromJson: Sized {
    /// `v` as a `Self`.
    fn from_json(v: &Value) -> Result<Self, String>;

    /// The field of an object whose value is `v`, or `None` if the object
    /// leaves it out, which only an `Option` allows.
    fn from_field(v: Option<&Value>) -> Result<Self, String> {
        Self::from_json(v.ok_or("missing")?)
    }
}

/// Parses `json`, the text of the file `name`, as a `T`; panics if it is
/// not one.
pub fn parse<T: FromJson>(name: &str, json: &str) -> T {
    // `Value`'s `FromStr` is compiled (optimized) in `serde_json`, rather
    // than generically in the test binary.
    let value: Value = json.parse().unwrap_or_else(|e| panic!("{name}: {e}"));
    T::from_json(&value).unwrap_or_else(|e| panic!("{name}: {e}"))
}

/// `v` as an object.
pub fn object(v: &Value) -> Result<&Map<String, Value>, String> {
    v.as_object()
        .ok_or_else(|| format!("expected an object, found {v}"))
}

/// The field `key` of the object `o`.
pub fn field<T: FromJson>(o: &Map<String, Value>, key: &str) -> Result<T, String> {
    T::from_field(o.get(key)).map_err(|e| format!("{key}: {e}"))
}

/// The field `key` of the object `o`, or `T`'s default if `o` leaves it out.
pub fn field_or_default<T: FromJson + Default>(
    o: &Map<String, Value>,
    key: &str,
) -> Result<T, String> {
    let v = o.get(key).map_or_else(|| Ok(T::default()), T::from_json);
    v.map_err(|e| format!("{key}: {e}"))
}

impl FromJson for String {
    fn from_json(v: &Value) -> Result<Self, String> {
        let s = v
            .as_str()
            .ok_or_else(|| format!("expected a string, found {v}"));
        s.map(str::to_owned)
    }
}

impl FromJson for u64 {
    fn from_json(v: &Value) -> Result<Self, String> {
        v.as_u64()
            .ok_or_else(|| format!("expected an unsigned integer, found {v}"))
    }
}

impl FromJson for usize {
    fn from_json(v: &Value) -> Result<Self, String> {
        usize::try_from(u64::from_json(v)?).map_err(|e| format!("{v}: {e}"))
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
    fn from_json(v: &Value) -> Result<Self, String> {
        u32::try_from(u64::from_json(v)?).map_err(|e| format!("{v}: {e}"))
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
    fn from_json(v: &Value) -> Result<Self, String> {
        v.as_bool()
            .ok_or_else(|| format!("expected a boolean, found {v}"))
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
    fn from_json(v: &Value) -> Result<Self, String> {
        Ok(v.clone())
    }
}

/// `null` is `None`, as is a field left out.
impl<T: FromJson> FromJson for Option<T> {
    fn from_json(v: &Value) -> Result<Self, String> {
        (!v.is_null()).then(|| T::from_json(v)).transpose()
    }

    fn from_field(v: Option<&Value>) -> Result<Self, String> {
        v.map_or(Ok(None), Self::from_json)
    }
}

impl<T: FromJson> FromJson for Vec<T> {
    fn from_json(v: &Value) -> Result<Self, String> {
        let items = v
            .as_array()
            .ok_or_else(|| format!("expected an array, found {v}"))?;
        // A loop: `collect`ing the `Result`s compiled iterator adapters for
        // every `T`, as much code as the rest of reading the files.
        let mut all = Vec::with_capacity(items.len());
        for (i, x) in items.iter().enumerate() {
            all.push(T::from_json(x).map_err(|e| format!("[{i}]: {e}"))?);
        }
        Ok(all)
    }
}

/// An object, its keys in order.
impl<T: FromJson> FromJson for BTreeMap<String, T> {
    fn from_json(v: &Value) -> Result<Self, String> {
        let mut all = BTreeMap::new();
        for (k, x) in object(v)? {
            all.insert(k.clone(), T::from_json(x).map_err(|e| format!("{k}: {e}"))?);
        }
        Ok(all)
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
            fn from_json(v: &serde_json::Value) -> Result<Self, String> {
                #[allow(unused_variables)]
                let o = $crate::json::object(v)?;
                Ok(Self { $($field: $crate::json_field!(v, o, $field $(, $($opt)*)?)?,)* })
            }
        }
    };
}

/// A field of [`json_struct!`]'s `from_json`: of the value `$v`, the object
/// `$o`.
#[macro_export]
#[doc(hidden)]
macro_rules! json_field {
    ($v:ident, $o:ident, $field:ident) => {
        $crate::json::field($o, stringify!($field))
    };
    ($v:ident, $o:ident, $field:ident, rename = $key:literal) => {
        $crate::json::field($o, $key)
    };
    ($v:ident, $o:ident, $field:ident, default) => {
        $crate::json::field_or_default($o, stringify!($field))
    };
    ($v:ident, $o:ident, $field:ident, rename = $key:literal, default) => {
        $crate::json::field_or_default($o, $key)
    };
    ($v:ident, $o:ident, $field:ident, flatten) => {
        $crate::json::FromJson::from_json($v)
    };
}
