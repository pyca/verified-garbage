//! Reading the JSON test vector files: miniserde parses a file into an
//! untyped [`Value`], and a test reads the fields it checks into its own
//! structs, declared with [`json_struct!`](crate::json_struct), through
//! [`FromJson`].
//!
//! This keeps the test binary small: a struct's reader is a call per field
//! to the shared readers of its fields' types, where a `serde` derive
//! expands to generic visitors compiled again for every struct. A reader
//! panics, naming what it expected, when the value is not what the struct
//! says, or a field it requires is missing; like `serde`'s derive, it
//! ignores the fields the struct does not name.

use std::collections::BTreeMap;

pub use miniserde::json::{Number, Object, Value};

/// The value of `v`, which must be the variant `$variant` (e.g.
/// `Value::String`), or a panic saying it is not `$what`. A macro, rather
/// than a function, so that coverage counts the arm that panics at the call.
#[macro_export]
macro_rules! json_variant {
    ($v:expr, $variant:path, $what:literal) => {
        match $v {
            $variant(x) => x,
            _ => panic!(concat!("expected ", $what)),
        }
    };
}

/// Parses the JSON text `text` of the file `name`.
pub fn parse(name: &str, text: &str) -> Value {
    miniserde::json::from_str(text).unwrap_or_else(|e| panic!("{name}: {e}"))
}

/// Reads `T` from the JSON text `text` of the file `name`.
pub fn from_str<T: FromJson>(name: &str, text: &str) -> T {
    T::from_json(&parse(name, text))
}

/// A type read from a JSON value.
pub trait FromJson: Sized {
    /// Reads `v`, panicking if it is not a `Self`.
    fn from_json(v: &Value) -> Self;

    /// Reads the field `key` of an object, `None` if it is missing: which
    /// only an `Option` allows.
    fn from_field(v: Option<&Value>, key: &str) -> Self {
        Self::from_json(v.unwrap_or_else(|| panic!("missing field `{key}`")))
    }
}

/// The object `v`.
pub fn object(v: &Value) -> &Object {
    json_variant!(v, Value::Object, "an object")
}

/// The field `key` of the object `o`, read as a `T`.
pub fn field<T: FromJson>(o: &Object, key: &str) -> T {
    T::from_field(o.get(key), key)
}

/// The field `key` of the object `o`, read as a `T`, or `T`'s default if
/// it is missing (`serde`'s `#[serde(default)]`).
pub fn field_or_default<T: FromJson + Default>(o: &Object, key: &str) -> T {
    o.get(key).map_or_else(T::default, T::from_json)
}

/// The non-negative integer `v`.
fn unsigned(v: &Value) -> u64 {
    let n = json_variant!(v, Value::Number, "a number");
    *json_variant!(n, Number::U64, "a non-negative integer")
}

impl FromJson for String {
    fn from_json(v: &Value) -> Self {
        json_variant!(v, Value::String, "a string").clone()
    }
}

/// For the ACVP tests.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
impl FromJson for bool {
    fn from_json(v: &Value) -> Self {
        *json_variant!(v, Value::Bool, "a boolean")
    }
}

/// A value kept as it is, for the RSA tests.
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
    fn from_json(v: &Value) -> Self {
        v.clone()
    }
}

impl FromJson for u64 {
    fn from_json(v: &Value) -> Self {
        unsigned(v)
    }
}

impl FromJson for u32 {
    fn from_json(v: &Value) -> Self {
        u32::try_from(unsigned(v)).expect("a 32-bit integer")
    }
}

impl FromJson for usize {
    fn from_json(v: &Value) -> Self {
        usize::try_from(unsigned(v)).expect("an integer of the pointer's width")
    }
}

impl<T: FromJson> FromJson for Vec<T> {
    fn from_json(v: &Value) -> Self {
        json_variant!(v, Value::Array, "an array")
            .iter()
            .map(T::from_json)
            .collect()
    }
}

impl<T: FromJson> FromJson for BTreeMap<String, T> {
    fn from_json(v: &Value) -> Self {
        object(v)
            .iter()
            .map(|(k, v)| (k.clone(), T::from_json(v)))
            .collect()
    }
}

impl<T: FromJson> FromJson for Option<T> {
    fn from_json(v: &Value) -> Self {
        (!matches!(v, Value::Null)).then(|| T::from_json(v))
    }

    fn from_field(v: Option<&Value>, _: &str) -> Self {
        v.and_then(Self::from_json)
    }
}

/// Declares a struct read from a JSON object by [`FromJson`]: each field
/// is written `name: Type = "key"`, where `key` is the field of the object
/// it is read from; `= "key" or default` for a field that, if missing,
/// takes its type's default value; and `= flatten` for a field read from
/// the same object (`serde`'s `#[serde(flatten)]`). Type parameters,
/// without bounds, must be `FromJson` themselves.
#[macro_export]
macro_rules! json_struct {
    (
        $(#[$meta:meta])*
        $vis:vis struct $name:ident $(<$($param:ident),*>)? {
            $($(#[$fmeta:meta])* $fvis:vis $field:ident: $ty:ty = $key:tt $(or $default:ident)?),*
            $(,)?
        }
    ) => {
        $(#[$meta])*
        $vis struct $name $(<$($param),*>)? {
            $($(#[$fmeta])* $fvis $field: $ty),*
        }

        impl $(<$($param: $crate::json::FromJson),*>)? $crate::json::FromJson
            for $name $(<$($param),*>)?
        {
            fn from_json(v: &$crate::json::Value) -> Self {
                #[allow(unused_variables)]
                let o = $crate::json::object(v);
                Self {
                    $($field: $crate::json_struct!(@field v, o, $key $(, $default)?)),*
                }
            }
        }
    };
    (@field $v:ident, $o:ident, flatten) => {
        $crate::json::FromJson::from_json($v)
    };
    (@field $v:ident, $o:ident, $key:literal) => {
        $crate::json::field($o, $key)
    };
    (@field $v:ident, $o:ident, $key:literal, default) => {
        $crate::json::field_or_default($o, $key)
    };
}
