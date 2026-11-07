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

/-! ## The same instance from several variants (`Rust.checkSame`) -/

def poly := Artifacts.Poly1305.AArch64.artifacts

-- Each artifact twice, as a generic function's instance for two variants that
-- differ in a part it does not use: the files are those of each once.
#guard match Rust.files (poly ++ poly) Dispatch.ranking, Rust.files poly Dispatch.ranking with
  | .ok a, .ok b => a == b
  | _, _ => false

-- Of the same name but not the same function: an error.
#guard match poly.head? with
  | some a => match Rust.files (poly ++ [{ a with doc := a.doc ++ " " }]) Dispatch.ranking with
    | .error e => has e s!"{a.name} is defined more than once, as different functions"
    | .ok _ => false
  | none => false

-- An unranked suffix fails the emitter.
#guard match Rust.files Artifacts.Poly1305.AArch64.artifacts [("aarch64", [])] with
  | .error e => has e "vg_poly1305_update_neon: its suffix `_neon` is not ranked"
  | .ok _ => false

end VG.Test.Dispatch
