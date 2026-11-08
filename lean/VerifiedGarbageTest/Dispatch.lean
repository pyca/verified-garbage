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
which its registration lets the dispatcher choose only on Apple's targets
(or where `VG_CPU_FEATURES` names its features), and only with the `neon` feature
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

-- `vg_poly1305_update`: `_neon` where its registration lets it be chosen, else the base,
-- chosen by `select` on the first call (`first`) and called through `CHOSEN`
-- from then on.
#guard has file
  "pub unsafe fn vg_poly1305_update_auto(state: *mut [u64; 16], count: u64, data: *const u8, \
    len: usize) {\n    \
    /// The type of the implementations.\n    \
    type Impl = unsafe extern \"C\" fn(state: *mut [u64; 16], count: u64, data: *const u8, \
    len: usize);\n"
#guard has file
  "    fn select() -> Impl {\n        \
    let cpu = verified_garbage_cpu::detected();\n        \
    if (cfg!(target_vendor = \"apple\") || verified_garbage_cpu::requested(\
    verified_garbage_cpu::Features(verified_garbage_cpu::feature::NEON))) && \
    cpu.contains(verified_garbage_cpu::Features(verified_garbage_cpu::feature::NEON)) {\n            \
    return crate::poly1305::vg_poly1305_update_neon;\n        }\n        \
    crate::poly1305::vg_poly1305_update\n    }\n"
#guard has file
  "    unsafe extern \"C\" fn first(state: *mut [u64; 16], count: u64, data: *const u8, \
    len: usize) {\n        \
    let f = select();\n        \
    CHOSEN.store(f as *mut (), core::sync::atomic::Ordering::Relaxed);\n"
#guard has file "        unsafe { f(state, count, data, len) }\n    }\n"
#guard has file
  "    static CHOSEN: core::sync::atomic::AtomicPtr<()> =\n        \
    core::sync::atomic::AtomicPtr::new(first as Impl as *mut ());\n"
#guard has file
  "    unsafe { core::mem::transmute::<*mut (), Impl>(CHOSEN.load(\
    core::sync::atomic::Ordering::Relaxed))(state, count, data, len) }\n}\n"

-- They are a module of their own, not in the module of the functions.
#guard ((out.find? (·.1 == "verified-garbage-asm-aarch64/src/poly1305.rs")).map
  fun (_, t) => !has t "_auto").getD false
#guard has (((out.find? (·.1 == "verified-garbage-asm-aarch64/src/dispatch/mod.rs")).map (·.2)).getD "")
  "pub mod poly1305;\n"

/-! ## A registration's `extra` features and `vendor` (`Artifact.extra`, `Artifact.vendor`) -/

/-- The ranking without any rule for Poly1305 alone. -/
def plainRanking : Rust.Ranking :=
  Dispatch.ranking.map fun (t, rs) => (t, rs.filter fun r => !r.modules.contains "poly1305")

/-- The files of Poly1305 on AArch64 under `rk`, with `f` applied to `_neon`
without its registration's `extra` features and `vendor`. -/
def neonOut (rk : Rust.Ranking) (f : Artifact → Artifact) : Except String (List (String × String)) :=
  Rust.files (Artifacts.Poly1305.AArch64.artifacts.map fun a =>
    if a.name == "vg_poly1305_update_neon" then f { a with extra := [], vendor := none } else a) rk

-- The registration's choice: the same files.
#guard match neonOut plainRanking fun a => { a with vendor := some "apple", extra := ["neon"] } with
  | .ok fs => fs == out
  | .error _ => false

-- The ranking and the registration may each give some of it, and they combine.
#guard match neonOut (plainRanking.map fun (t, rs) => (t, if t == "aarch64" then
      { suffix := "_neon", modules := ["poly1305"], vendor := some "apple" } :: rs else rs))
    fun a => { a with extra := ["neon"] } with
  | .ok fs => fs == out
  | .error _ => false

-- Without either, `_neon` is chosen everywhere.
#guard match neonOut plainRanking id with
  | .ok fs => fs != out && has (((fs.find? (·.1 ==
      "verified-garbage-asm-aarch64/src/dispatch/poly1305.rs")).map (·.2)).getD "")
      "    if cpu.0 != 0 {\n"
  | .error _ => false

-- A vendor or feature that is not a name fails the emitter.
#guard match neonOut plainRanking fun a => { a with vendor := some "Apple" } with
  | .error e => has e "vg_poly1305_update_neon names the vendor `Apple`"
  | .ok _ => false
#guard match neonOut plainRanking fun a => { a with extra := ["ne on"] } with
  | .error e => has e "vg_poly1305_update_neon needs the feature `ne on`"
  | .ok _ => false

/-- The position of a suffix in x86-64's ranking for a module. -/
def x86Rank (module suffix : String) : Option Nat :=
  (Rust.rankOf ((Dispatch.ranking.lookup "x86_64").getD []) module suffix).map (·.1)

-- ChaCha20's and ChaCha20-Poly1305's dispatchers try `_avx2` before `_ssse3`,
-- so they never choose `_ssse3` with AVX2, and `_ssse3` without it.
#guard ["chacha20", "chacha20poly1305"].all fun m =>
  match x86Rank m "_avx2", x86Rank m "_ssse3" with
  | some a, some s => a < s
  | _, _ => false

-- AES-CMAC's, AES-SIV's and AES-CCM's dispatchers rank `_aesni`, which needs
-- only AES-NI and SSSE3, so they never choose the baseline with those.
#guard ["cmac_aes", "aes_siv", "aes_ccm"].all fun m => (x86Rank m "_aesni").isSome

-- AES-GCM-SIV's dispatchers try `_aesni_pclmul_avx_avx2` before `_aesni_avx2`
-- and `_pclmul_avx2`, and `_vaes_vpclmul_avx512` before `_vaes_avx2` and
-- `_vpclmul_avx2`.
#guard [("_aesni_pclmul_avx_avx2", "_aesni_avx2"), ("_aesni_pclmul_avx_avx2", "_pclmul_avx2"),
    ("_vaes_vpclmul_avx512", "_vaes_avx2"), ("_vaes_vpclmul_avx512", "_vpclmul_avx2")].all fun (a, b) =>
  match x86Rank "aes_gcm_siv" a, x86Rank "aes_gcm_siv" b with
  | some i, some j => i < j
  | _, _ => false

-- ChaCha20's `_avx512` needs AVX512_IFMA too, which its own features do not
-- name: it is chosen where ChaCha20-Poly1305's `_ifma`, built on it, is.
#guard ((Rust.rankOf ((Dispatch.ranking.lookup "x86_64").getD []) "chacha20" "_avx512").map
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
