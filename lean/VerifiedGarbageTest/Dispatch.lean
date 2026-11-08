module

import VerifiedGarbage.TCB.Rust
meta import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.Emit
meta import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Artifacts.Poly1305.AArch64
meta import VerifiedGarbage.Artifacts.Poly1305.AArch64

/-!
# Dispatchers (`Rust.dispatcher`)

Which implementations a dispatcher tries, in what order, and what it is for
Poly1305 on AArch64: `vg_poly1305_update` and its `_neon` variant,
which its registration lets the dispatcher choose only on Apple's targets
(or where `VG_CPU_FEATURES` names its features), and only where the target
enables or detection reports the `neon` feature; `vg_poly1305_init` and
`vg_poly1305_finalize`, its only implementations, whose dispatchers are
other names of them.
-/

namespace VG.Test.Dispatch
open VG

def out : List (String × String) :=
  match Rust.files Artifacts.Poly1305.AArch64.artifacts with
  | .ok fs => fs
  | .error e => [("error", e)]

def file : String :=
  ((out.find? (·.1 == "verified-garbage-asm-aarch64/src/dispatch/poly1305.rs")).map (·.2)).getD ""

def has (text part : String) : Bool := (text.splitOn part).length > 1

-- The functions with one implementation: a dispatcher that takes the token and calls it.
#guard has file
  "pub unsafe fn vg_poly1305_init_auto(_dit: verified_garbage_cpu::Dit<'_>, \
    state: *mut [u64; 16], key: *const [u8; 32]) {\n    \
    // SAFETY: the caller's obligations, which are the base's; it needs no CPU feature.\n    \
    unsafe { crate::poly1305::vg_poly1305_init(state, key) }\n}\n"
#guard has file "pub unsafe fn vg_poly1305_finalize_auto(_dit: verified_garbage_cpu::Dit<'_>, "

-- The implementations of a function with a dispatcher are the crate's own: the library
-- reaches them only through it, with the token.
#guard has (((out.find? (·.1 == "verified-garbage-asm-aarch64/src/poly1305.rs")).map (·.2)).getD "")
  "pub(crate) unsafe extern \"C\" fn vg_poly1305_update_neon("
#guard !has (((out.find? (·.1 == "verified-garbage-asm-aarch64/src/poly1305.rs")).map (·.2)).getD "")
  "\npub unsafe extern"

-- `vg_poly1305_update`: `_neon` where its registration lets it be chosen, else the base,
-- chosen by `select` on the first call (`first`) and called through `CHOSEN`
-- from then on.
#guard has file
  "pub unsafe fn vg_poly1305_update_auto(_dit: verified_garbage_cpu::Dit<'_>, \
    state: *mut [u64; 16], count: u64, data: *const u8, len: usize) {\n    \
    /// The type of the implementations.\n    \
    type Impl = unsafe extern \"C\" fn(state: *mut [u64; 16], count: u64, data: *const u8, \
    len: usize);\n"
#guard has file
  "    fn select() -> Impl {\n        \
    let cpu = verified_garbage_cpu::detected();\n        \
    if (cfg!(target_vendor = \"apple\") || verified_garbage_cpu::requested(\
    verified_garbage_cpu::Features(verified_garbage_cpu::feature::NEON)))\n            \
    && (const { verified_garbage_cpu::target_contains(\
    verified_garbage_cpu::Features(verified_garbage_cpu::feature::NEON)) }\n            \
    || cpu.contains(verified_garbage_cpu::Features(verified_garbage_cpu::feature::NEON)))\n        {\n            \
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

/-- The files of Poly1305 on AArch64, with `f` applied to `_neon` without its
registration's `extra` features and `vendor`. -/
def neonOut (f : Artifact → Artifact) : Except String (List (String × String)) :=
  Rust.files (Artifacts.Poly1305.AArch64.artifacts.map fun a =>
    if a.name == "vg_poly1305_update_neon" then f { a with extra := [], vendor := none } else a)

-- The registration's choice: the same files.
#guard match neonOut fun a => { a with vendor := some "apple", extra := ["neon"] } with
  | .ok fs => fs == out
  | .error _ => false

-- Without either, `_neon` is chosen everywhere.
#guard match neonOut id with
  | .ok fs => fs != out && has (((fs.find? (·.1 ==
      "verified-garbage-asm-aarch64/src/dispatch/poly1305.rs")).map (·.2)).getD "")
      "        if const { verified_garbage_cpu::COMPILED.0 != 0 }\n            || cpu.0 != 0\n        {\n"
  | .error _ => false

-- A vendor or feature that is not a name fails the emitter.
#guard match neonOut fun a => { a with vendor := some "Apple" } with
  | .error e => has e "vg_poly1305_update_neon names the vendor `Apple`"
  | .ok _ => false
#guard match neonOut fun a => { a with extra := ["ne on"] } with
  | .error e => has e "vg_poly1305_update_neon needs the feature `ne on`"
  | .ok _ => false

/-! ## The order of the implementations -/

/-- `_neon` as the registration has it (a list of it), its other
implementations, and another name of `_neon` that any target may choose. -/
def neon : List Artifact :=
  Artifacts.Poly1305.AArch64.artifacts.filter (·.name == "vg_poly1305_update_neon")
def others : List Artifact :=
  Artifacts.Poly1305.AArch64.artifacts.filter (·.name != "vg_poly1305_update_neon")
def neon2 : List Artifact := neon.map fun a => { a with name := "vg_poly1305_update_neon2", vendor := none }

/-- The dispatchers of Poly1305 with the artifacts `as`. -/
def dispatchOf (as : List Artifact) : String :=
  match Rust.files as with
  | .ok fs => ((fs.find? (·.1 == "verified-garbage-asm-aarch64/src/dispatch/poly1305.rs")).map
      (·.2)).getD ""
  | .error e => "error: " ++ e

-- It tries them in the order the artifacts list them: `_neon`, then `_neon2`.
#guard ((((dispatchOf (others ++ neon ++ neon2)).splitOn
  "return crate::poly1305::vg_poly1305_update_neon;").getD 1 "").splitOn
  "return crate::poly1305::vg_poly1305_update_neon2;").length == 2

-- One that it could choose only where one before it can fails the emitter.
#guard has (dispatchOf (others ++ neon2 ++ neon)) "error: aarch64: vg_poly1305_update_neon would \
  never run: its dispatcher tries vg_poly1305_update_neon2 before it"

-- An implementation of another signature or documentation than its base's fails it.
#guard has (dispatchOf (others ++ neon.map fun a => { a with doc := "Another function. " ++ a.doc }))
  "vg_poly1305_update_neon, an implementation of vg_poly1305_update, has another signature or \
  documentation"

-- Every implementation of a function is in one registration file.
#guard (Emit.checkSources [("A", Artifacts.Poly1305.AArch64.artifacts)]).toOption.isSome
#guard match Emit.checkSources [("A", others), ("B", neon)] with
  | .error e => has e "aarch64: the implementations of vg_poly1305_update are in two registration \
      files, A and B"
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

def tableText (ts : List FnTable) : String :=
  match Rust.tableDispatchers "x86_64" [] ts tableFeatures
      (fun fs => fs.map fun f => s!"target_feature = \"{f}\"") with
  | .ok s => s
  | .error e => "error: " ++ e

def tables : String := tableText [tU, tShani, tAvx2, t2, tT]

-- Implementations of `VG_T`: the tables of its interface and data named after it,
-- in the order of the list.
#guard (Rust.tableGroupsOf [tU, tShani, tAvx2, t2, tT]).map (fun (b, ms) => (b.name, ms.map (·.name))) ==
  [("VG_U_AVX2", []), ("VG_T_2", []), ("VG_T", ["VG_T_SHANI", "VG_T_AVX2"])]

-- `VG_T`'s dispatcher returns `_SHANI` where the CPU has its features, then
-- `_AVX2`, in the order of the list, else `VG_T`.
#guard has tables
  "pub fn vg_t_auto() -> &'static crate::fn_tables::Fns {\n    \
    let cpu = verified_garbage_cpu::detected();\n    \
    #[cfg(target_feature = \"sha\")]\n    \
    if const { verified_garbage_cpu::target_contains(crate::fn_tables::VG_T_SHANI_FEATURES) }\n        \
    || cpu.contains(crate::fn_tables::VG_T_SHANI_FEATURES)\n    {\n        \
    return &crate::fn_tables::VG_T_SHANI;\n    }\n    \
    #[cfg(target_feature = \"avx2\")]\n    \
    if const { verified_garbage_cpu::target_contains(crate::fn_tables::VG_T_AVX2_FEATURES) }\n        \
    || cpu.contains(crate::fn_tables::VG_T_AVX2_FEATURES)\n    {\n        \
    return &crate::fn_tables::VG_T_AVX2;\n    }\n    \
    &crate::fn_tables::VG_T\n}\n"

-- `VG_T_2`, of other data, has its own, returning it; `VG_U_AVX2`, which
-- needs a feature, has none.
#guard has tables "pub fn vg_t_2_auto() -> &'static crate::fn_tables::Fns {\n    \
  &crate::fn_tables::VG_T_2\n}\n"
#guard !has tables "vg_u_avx2_auto"

-- One that it could choose only where one before it can fails the emitter.
#guard tableText [tT, tShani, { tShani with name := "VG_T_X_SHANI" }] ==
  "error: x86_64: VG_T_X_SHANI would never run: its dispatcher tries VG_T_SHANI before it, \
    which needs nothing it does not"

-- A dispatcher's name may not be an artifact's.
#guard match Rust.tableDispatchers "x86_64" ["vg_t_auto"] [tT] tableFeatures (fun _ => []) with
  | .error e => has e "vg_t_auto is both an artifact and the dispatcher of VG_T"
  | .ok _ => false

end VG.Test.Dispatch
