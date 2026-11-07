module

import VerifiedGarbage.TCB.Rust
meta import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.Dispatch
meta import VerifiedGarbage.Dispatch
import VerifiedGarbage.Artifacts.Poly1305.AArch64
meta import VerifiedGarbage.Artifacts.Poly1305.AArch64

/-!
# Dispatchers (`Rust.dispatcher`)

How a dispatcher reads and ranks its implementations' suffixes, and what it
is for Poly1305 on AArch64: `vg_poly1305_update` and its `_neon` variant,
which the ranking chooses only on Apple's targets (or where
`VG_CPU_FEATURES` names its features), and only with the `neon` feature
detected; `vg_poly1305_init` and `vg_poly1305_finalize`, its only
implementations, whose dispatchers are other names of them.
-/

namespace VG.Test.Dispatch
open VG

def rs : List Rust.Rank := [
  { suffix := "_shani" }, { suffix := "_avx2" }, { suffix := "_adx" },
  { suffix := "_aes", modules := ["aes"] }]

-- The first rank of a suffix, in any module or in its own.
#guard (Rust.rankOf rs "sha256" "_avx2").map (·.1) == some 1
#guard (Rust.rankOf rs "aes" "_aes").map (·.1) == some 3
#guard (Rust.rankOf rs "gcm" "_aes").isNone

-- A suffix of parts `_<tag><suffix>` (`Emit.qualifiedName`), each ranked.
#guard (Rust.partsOf rs "dsa" 40 "_sha256_avx2_mr_adx").map (·.map fun (t, i, _) => (t, i)) ==
  some [("sha256", 1), ("mr", 2)]
#guard (Rust.partsOf rs "dsa" 40 "_sha256_avx512").isNone
#guard (Rust.partsOf rs "dsa" 40 "_avx2").isNone

-- Parts compare by the first tag's rank, then the next.
#guard Rust.lexLe [0, 4] [1, 0]
#guard !Rust.lexLe [1, 0] [0, 4]
#guard Rust.lexLe [1, 2] [1, 2]

def out : List (String × String) :=
  match Rust.files Artifacts.Poly1305.AArch64.artifacts Dispatch.ranking with
  | .ok fs => fs
  | .error e => [("error", e)]

def file : String :=
  ((out.find? (·.1 == "verified-garbage-asm-aarch64/src/dispatch/poly1305.rs")).map (·.2)).getD ""

def has (text part : String) : Bool := (text.splitOn part).length > 1

-- The functions with one implementation: other names of it.
#guard has file "pub use crate::poly1305::vg_poly1305_init as vg_poly1305_init_auto;\n"
#guard has file "pub use crate::poly1305::vg_poly1305_finalize as vg_poly1305_finalize_auto;\n"

-- `vg_poly1305_update`: `_neon` where the ranking chooses it, else the base.
#guard has file
  "pub unsafe fn vg_poly1305_update_auto(state: *mut [u64; 16], count: u64, data: *const u8, \
    len: usize) {\n    \
    let cpu = verified_garbage_cpu::detected();\n    \
    if (cfg!(target_vendor = \"apple\") || verified_garbage_cpu::requested(\
    verified_garbage_cpu::Features(verified_garbage_cpu::feature::NEON))) && \
    cpu.contains(verified_garbage_cpu::Features(verified_garbage_cpu::feature::NEON)) {\n"
#guard has file
  "        return unsafe { crate::poly1305::vg_poly1305_update_neon(state, count, data, len) };\n    }\n"
#guard has file "    unsafe { crate::poly1305::vg_poly1305_update(state, count, data, len) }\n}\n"

-- They are a module of their own, not in the module of the functions.
#guard ((out.find? (·.1 == "verified-garbage-asm-aarch64/src/poly1305.rs")).map
  fun (_, t) => !has t "_auto").getD false
#guard has (((out.find? (·.1 == "verified-garbage-asm-aarch64/src/dispatch/mod.rs")).map (·.2)).getD "")
  "pub mod poly1305;\n"

/-- The position of a suffix in x86-64's ranking for a module. -/
def x86Rank (module suffix : String) : Option Nat :=
  (Rust.rankOf ((Dispatch.ranking.lookup "x86_64").getD []) module suffix).map (·.1)

-- ChaCha20's and ChaCha20-Poly1305's dispatchers try `_avx2` before `_ssse3`,
-- so they never choose `_ssse3` with AVX2 (`NEVER_WITH` in
-- `ci/check_variants.py`), and `_ssse3` without it.
#guard ["chacha20", "chacha20poly1305"].all fun m =>
  match x86Rank m "_avx2", x86Rank m "_ssse3" with
  | some a, some s => a < s
  | _, _ => false

-- ChaCha20's `_ifma` needs AVX512_IFMA too, which its own features do not
-- name: it is chosen where ChaCha20-Poly1305's `_ifma` is.
#guard ((Rust.rankOf ((Dispatch.ranking.lookup "x86_64").getD []) "chacha20" "_ifma").map
  (·.2.extra)) == some ["avx512ifma"]

-- An unranked suffix fails the emitter.
#guard match Rust.files Artifacts.Poly1305.AArch64.artifacts [("aarch64", [])] with
  | .error e => has e "vg_poly1305_update_neon: its suffix `_neon` is not ranked"
  | .ok _ => false

/-! ## Tables of functions (`Rust.tableDispatcher`) -/

/-- Tables of one interface: `VG_T` and its implementations `_SHANI` and
`_AVX2`, of the same data; `VG_T_2`, whose name extends `VG_T`'s but whose
data is not its own, a table of its own; and `VG_U_AVX2`, which needs a CPU
feature and has no base to fall back on. -/
def tT : FnTable := { name := "VG_T", iface := "Fns", fns := ["vg_t"], data := [1] }
def tShani : FnTable := { name := "VG_T_SHANI", iface := "Fns", fns := ["vg_t_shani"], data := [1] }
def tAvx2 : FnTable := { name := "VG_T_AVX2", iface := "Fns", fns := ["vg_t_avx2"], data := [1] }
def t2 : FnTable := { name := "VG_T_2", iface := "Fns", fns := ["vg_t"], data := [2] }
def tU : FnTable := { name := "VG_U_AVX2", iface := "Fns", fns := ["vg_t_avx2"], data := [3] }

def tableFeatures (T : FnTable) : List String :=
  if T.name.endsWith "_SHANI" then ["sha"] else if T.name.endsWith "_AVX2" then ["avx2"] else []

def tableText (rs : List Rust.Rank) (ts : List FnTable) : String :=
  match Rust.tableDispatchers rs "x86_64" [] ts tableFeatures
      (fun fs => fs.map fun f => s!"target_feature = \"{f}\"") (fun _ => "sha256") with
  | .ok s => s
  | .error e => "error: " ++ e

def tables : String := tableText rs [tU, tAvx2, t2, tT, tShani]

-- Implementations of `VG_T`: the tables of its interface and data named after it.
#guard (Rust.tableGroupsOf [tU, tAvx2, t2, tT, tShani]).map (fun (b, ms) => (b.name, ms.map (·.2))) ==
  [("VG_T", ["_AVX2", "_SHANI"]), ("VG_T_2", []), ("VG_U_AVX2", [])]

-- `VG_T`'s dispatcher returns `_SHANI` where the CPU has its features, then
-- `_AVX2`, as the ranking orders them, else `VG_T`.
#guard has tables
  "pub fn vg_t_auto() -> &'static crate::fn_tables::Fns {\n    \
    let cpu = verified_garbage_cpu::detected();\n    \
    #[cfg(target_feature = \"sha\")]\n    \
    if cpu.contains(crate::fn_tables::VG_T_SHANI_FEATURES) {\n        \
    return &crate::fn_tables::VG_T_SHANI;\n    }\n    \
    #[cfg(target_feature = \"avx2\")]\n    \
    if cpu.contains(crate::fn_tables::VG_T_AVX2_FEATURES) {\n        \
    return &crate::fn_tables::VG_T_AVX2;\n    }\n    \
    &crate::fn_tables::VG_T\n}\n"

-- `VG_T_2`, of other data, has its own, returning it; `VG_U_AVX2`, which
-- needs a feature, has none.
#guard has tables "pub fn vg_t_2_auto() -> &'static crate::fn_tables::Fns {\n    \
  &crate::fn_tables::VG_T_2\n}\n"
#guard !has tables "vg_u_avx2_auto"

-- An unranked suffix fails the emitter.
#guard tableText [] [tT, tShani] ==
  "error: x86_64: VG_T_SHANI: its suffix `_shani` is not ranked (`VG.Dispatch.ranking`), nor \
    made of parts `_<tag><suffix>` whose suffixes are"

-- A dispatcher's name may not be an artifact's.
#guard match Rust.tableDispatchers rs "x86_64" ["vg_t_auto"] [tT] tableFeatures (fun _ => [])
    (fun _ => "") with
  | .error e => has e "vg_t_auto is both an artifact and the dispatcher of VG_T"
  | .ok _ => false

end VG.Test.Dispatch
