module

import VerifiedGarbage.TCB.Rust
meta import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Bounds on what a function writes (`Artifact.written`)

A function `(buf: *mut [u64; 4], other: *mut [u8; 16])` that returns at once,
so it writes nothing: it is proven to change no byte of `buf` at offset 8 or
beyond (`writtenOk`), and the emitter exports the bound as a constant and
documents it. The checks (`Rust.checkWritten`) refuse a bound larger than
the buffer, on a parameter that is not a writable array or not a parameter,
and two bounds on one parameter.
-/

namespace VG.Test.Written
open VG VG.AArch64

def sig : Sig := { params := [("buf", .array true .u64 4), ("other", .array true .u8 16),
  ("key", .array false .u8 32)] }

/-- The postcondition, which says nothing (the test is of `written`). -/
def Nothing (_ : Addr) : Prop := True

def contract : Contract isa := sig.contract abi (post := fun buf _ _ _ _ _ => Nothing buf)

def code : Prog isa := .block []

theorem exec_code {s t s'} (e : Exec isa code s t s') : s' = s := by
  cases e with | block e => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e; exact e.1.symm

/-- Code that writes nothing meets any bound. -/
theorem written_ok (w : List (String × Nat)) : ∀ s t s', contract.pre s → Exec isa code s t s' →
    Sig.writtenWithin (target.abi.withConsts []) sig w s s' := by
  intro s t s' _ e
  rw [exec_code e]
  unfold Sig.writtenWithin
  split
  · exact True.intro
  · split
    · exact True.intro
    · exact fun _ _ _ _ _ _ _ _ => rfl

/-- A state satisfying the precondition: `buf` at `0x1000`, `other` at
`0x2000` and `key` at `0x3000`. -/
def sat : State where
  gpr r := if r = .x0 then 0x1000 else if r = .x1 then 0x2000 else if r = .x2 then 0x3000 else 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 16⟩]

theorem verified : Verified target code contract := by
  refine ⟨fun s _ => ⟨_, _, .block rfl, ?_, ?_⟩,
    .of_leakage (fun _ => []) (fun s t s' _ e => by cases e with | block e =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e; exact e.2.symm)
      (fun _ _ _ _ _ => rfl), ?_⟩
  · exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl⟩
  · sig_post [contract, sig, abi, argRegs]
    exact True.intro
  · refine ⟨sat, ?_⟩
    sig_pre [contract, sig, abi, argRegs, stackBelow, sat]
    exact ⟨Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, by decide, by decide⟩

def artifact (w : List (String × Nat)) : Artifact where
  target := target
  module := "test"
  name := "vg_test_written"
  sig := sig
  doc := "Writes nothing.\n\n# Safety\n\n* None."
  code := code
  contract := contract
  verified := verified
  written := w
  writtenOk := written_ok w

/-- The rendering: the constant of the bound, and the paragraph documenting
it before the `# Safety` section. -/
def expected : String := "/// The bytes of `buf` that `vg_test_written` may write: it changes no byte of `buf` at this offset or beyond (`Artifact.written`).
pub const VG_TEST_WRITTEN_BUF_WRITTEN: usize = 8;

/// Writes nothing.
///
/// It writes at most the first 8 bytes of `buf` (`VG_TEST_WRITTEN_BUF_WRITTEN`): no byte of `buf` beyond them changes.
///
/// # Safety
///
/// * `buf` must be valid for reads and writes of 32 bytes.
/// * `other` must be valid for reads and writes of 16 bytes.
/// * `key` must be valid for reads of 32 bytes.
/// * None.
/// * `buf` and `other` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `buf`, `other` and `key` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub unsafe extern \"C\" fn vg_test_written(buf: *mut [u64; 4], other: *mut [u8; 16], key: *const [u8; 32]) {
    core::arch::naked_asm!(
        r\".inst 0xd65f03c0
.p2align 6\",
    )
}
"

#guard Rust.function (artifact [("buf", 8)]) (fun _ => "") == expected

-- Without bounds, nothing is added.
#guard ((Rust.function (artifact []) (fun _ => "")).splitOn "WRITTEN").length == 1

#guard (Rust.checkWritten (artifact [])).isOk
#guard (Rust.checkWritten (artifact [("buf", 8)])).isOk
#guard (Rust.checkWritten (artifact [("buf", 32), ("other", 0)])).isOk
-- Larger than the buffer.
#guard !(Rust.checkWritten (artifact [("buf", 33)])).isOk
#guard !(Rust.checkWritten (artifact [("other", 17)])).isOk
-- Not a writable array.
#guard !(Rust.checkWritten (artifact [("key", 0)])).isOk
-- Not a parameter.
#guard !(Rust.checkWritten (artifact [("scratch", 0)])).isOk
-- Twice.
#guard !(Rust.checkWritten (artifact [("buf", 8), ("buf", 16)])).isOk

#guard Rust.writtenName "vg_x25519_base" "scratch" == "VG_X25519_BASE_SCRATCH_WRITTEN"

end VG.Test.Written
