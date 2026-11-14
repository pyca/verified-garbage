module

/-! # The names of a generic caller's instances

A function that calls functions of several interfaces is registered once for
each combination of their implementations (each element of their lists of
variants, `Proof/Variants/<Iface>/<Target>.lean`). Its instances need
distinct names, and variants of different interfaces may share a suffix
(e.g. `_avx2`), so each is named by its function's name, then a tag and the
suffix of each interface whose variant is not the baseline. Naming is not
trusted: the emitter checks that every name is unique (`Rust.checkUnique`).
-/

@[expose] public section

namespace VG

/-- `base`, then `_<tag><suffix>` for each `(tag, suffix)` of `parts` (one per
interface, in order) whose suffix is not empty. Suffixes start with `_`, so
`qualifiedName "vg_argon2" [("blake2b", "_avx2"), ("g", "")]` is
`vg_argon2_blake2b_avx2`. Two variants with the same suffix in different
interfaces give different names, as long as the tags differ. -/
def qualifiedName (base : String) (parts : List (String × String)) : String :=
  base ++ String.join (parts.map fun (tag, suffix) =>
    if suffix.isEmpty then "" else "_" ++ tag ++ suffix)

end VG
