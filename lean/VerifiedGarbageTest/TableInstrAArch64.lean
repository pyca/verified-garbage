module

import VerifiedGarbage.TCB.Rust
meta import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint

/-!
# Tables of constants carried by instructions (`ldrqTbl`) on AArch64

As on x86-64 (`TableInstrX86_64.lean`). A function `() -> u64` that returns
word 3 of a table of constants: `adrp`/`add` of the table's `static` into `x1`
(`adrSym`), `ldr q0, [x1, #16]` (`ldrqTbl`, carrying the table: words 2 and 3
into `v0`), then `umov x0, v0.d[1]`. It is proven against the contract of its
signature under the plain calling convention, without `abi.withConsts`: the
instruction carries the table's words, and its access is observed as its
offset in the table, 16, whatever the table's address. The emitter writes the
static from the instruction, byte for byte, and refuses a table two artifacts
give different words; the model's semantics read the two words at the
table's offset, and fault past the table, at an offset `ldr q` does not
encode, or through a base register not holding the table's address (which
the hardware would read from wherever it points).
-/

namespace VG.Test.TableInstrAArch64
open VG VG.AArch64

def sig : Sig := { params := [], ret := some .u64 }
def name : String := "VG_TEST_LDRQTBL"

/-- The table `[7, 8, 9, w]`. -/
def tbl (w : BitVec 64) : List (BitVec 64) := [7, 8, 9, w]

def contract (w : BitVec 64) : Contract isa :=
  sig.contract abi (post := fun m m' r => r = w ∧ m' = m)

def ld (w : BitVec 64) : Instr := .ldrqTbl .v0 .x1 16 name (tbl w)

def code (w : BitVec 64) : Prog isa := .block [.adrSym .x1 name, ld w, .umov .x .x0 .v0 1]

/-- The state after the code. -/
def res (w : BitVec 64) (s : State) : State :=
  let s₂ := (s.write .x .x1 (s.syms name)).setV .v0 (w ++ (9 : BitVec 64))
  s₂.write .x .x0 w

theorem exec_code (w : BitVec 64) (s : State) :
    execBlock isa [.adrSym .x1 name, ld w, .umov .x .x0 .v0 1] s =
      some (res w s, [Leak.addr (BitVec.ofNat 64 16)]) := by
  have g : (s.write .x .x1 (s.syms name)).gpr .x1 = (s.write .x .x1 (s.syms name)).syms name :=
    RegUpd.gpr_write_self s .x .x1 _
  have e₂ : AArch64.exec (ld w) (s.write .x .x1 (s.syms name)) =
      some ((s.write .x .x1 (s.syms name)).setV .v0 (w ++ (9 : BitVec 64))) := by
    simp [AArch64.exec, ld, g, tbl]
  have hv : ((s.write .x .x1 (s.syms name)).setV .v0 (w ++ (9 : BitVec 64))).v .v0 =
      w ++ (9 : BitVec 64) := by simp [RegUpd.v_setV]
  have e₃ : AArch64.exec (.umov .x .x0 .v0 1)
      ((s.write .x .x1 (s.syms name)).setV .v0 (w ++ (9 : BitVec 64))) = some (res w s) := by
    simp only [AArch64.exec, Size.bits, Nat.reduceMul, Nat.reduceLT, ite_true, hv,
      BitVec.extractLsb'_append_eq_left, res]
  have ha : addrs (ld w) (s.write .x .x1 (s.syms name)) = [BitVec.ofNat 64 16] := rfl
  simp only [execBlock, isa, exec_adrSym, e₂, e₃, ha, Option.map_some]
  rfl

/-- A state satisfying the precondition: the stack at `0x10000`. -/
def sat : State where
  gpr _ := 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := []
  syms _ := 0x1000

theorem verified (w : BitVec 64) : Verified target (code w) (contract w) := by
  refine ⟨fun s _ => ⟨_, _, .block (exec_code w s), ?_, ?_⟩,
    .of_leakage (fun _ => [Leak.addr (BitVec.ofNat 64 16)])
      (fun s t s' _ e => by cases e with | block e => rw [exec_code w s] at e; cases e; rfl)
      (fun _ _ _ _ _ => rfl), ⟨sat, ?_⟩⟩
  · exact ⟨fun r hr => by
      simp only [res]
      rw [RegUpd.gpr_write_of_ne _ _ _ (fun e => by subst e; exact absurd hr (by decide))]
      show (s.write .x .x1 (s.syms name)).gpr r = s.gpr r
      rw [RegUpd.gpr_write_of_ne _ _ _ (fun e => by subst e; exact absurd hr (by decide))],
      rfl, fun v hv => by
        have hne : v ≠ .v0 := fun e => by subst e; exact absurd hv (by decide)
        simp only [res, RegUpd.v_write, RegUpd.v_setV, hne, ite_false]⟩
  · sig_post [contract, sig, abi, argRegs]
  · sig_pre [contract, sig, abi, argRegs, stackBelow, sat]

def artifactOf (fn : String) (w : BitVec 64) : Artifact where
  target := target
  module := "test"
  name := fn
  sig := sig
  doc := "Returns word 3 of its table."
  code := code w
  contract := contract w
  verified := verified w
  spSafe := rfl

def artifact : Artifact := artifactOf "vg_test_ldrqtbl" 42

/-- The rendering: the table's address formed with `adrSym`, then read
through the register as by any `ldr q`. -/
def expected : String := "/// Returns word 3 of its table.
#[allow(clippy::missing_safety_doc)]
#[unsafe(naked)]
pub unsafe extern \"C\" fn vg_test_ldrqtbl() -> u64 {
    core::arch::naked_asm!(
        concat!(\"adrp x1, \", vg_sym_page!(\"{VG_TEST_LDRQTBL}\")),
        concat!(\"add x1, x1, \", vg_sym_pageoff!(\"{VG_TEST_LDRQTBL}\")),
        // ldr q0, [x1, #16]
        // umov x0, v0.d[1]
        // ret
        r\".inst 0x3dc00420,0x4e183c00,0xd65f03c0
.p2align 6\",
        VG_TEST_LDRQTBL = sym super::consts::VG_TEST_LDRQTBL,
    )
}
"

#guard Rust.function artifact (fun _ => "") == expected

-- The emitter writes the static from the instruction's words, byte for byte,
-- and the code may name it without `Artifact.consts`.
#guard (Rust.checkConsts [.of artifact] (.of artifact)).isOk
#guard Rust.tables [artifact] == [(name, tbl 42)]
#guard Rust.tableFile "aarch64" name (tbl 42) ==
  Rust.header ++ "//! The table of constants `VG_TEST_LDRQTBL` of the verified functions for `aarch64` (`Artifact.consts`).
#![allow(dead_code)]

use super::Table;

/// The table of constants `VG_TEST_LDRQTBL` (`Artifact.consts`).
pub static VG_TEST_LDRQTBL: Table<32> = Table(*b\"\\
    \\x07\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\
    \\x08\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\
    \\x09\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\
    \\x2a\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\
\");
"

-- Two artifacts carrying the same table: one static. Another giving it other
-- words: refused.
def same : Artifact := artifactOf "vg_test_ldrqtbl_same" 42
def other : Artifact := artifactOf "vg_test_ldrqtbl_other" 41
#guard (Rust.checkConsts [.of artifact, .of same] (.of artifact)).isOk
#guard Rust.tables [artifact, same] == [(name, tbl 42)]
#guard !(Rust.checkConsts [.of artifact, .of other] (.of artifact)).isOk
#guard !(Rust.checkConsts [.of artifact, .of other] (.of other)).isOk

/-! ## The semantics -/

/-- The table `[8, 9, …, 15]`, whose words differ from their indices. -/
def vtbl : List (BitVec 64) := (List.range 8).map fun j => BitVec.ofNat 64 (8 + j)

def vld (off : Nat) : Instr := .ldrqTbl .v3 .x2 off name vtbl

/-- `x2` holds `a`; the table is at `0x1000`. -/
def st (a : BitVec 64) : State := { sat with gpr := fun r => if r = .x2 then a else 0 }

-- Printed as any `ldr q`; in the baseline ISA; carries its table.
#guard Instr.asm (vld 32) == ["ldr q3, [x2, #32]"]
#guard printer.tables (vld 32) == [(name, vtbl)]
#guard isa.writesSp (vld 32) == false
-- The access is observed as the offset, wherever the table is.
#guard addrs (vld 32) (st 0x1000) == [32]
#guard addrs (vld 32) { st 0x2000 with syms := fun _ => 0x2000 } == [32]
-- Words 4 and 5, the first in bits 63:0: the 16 bytes at the offset,
-- little-endian, as `ldrq` reads them from memory.
#guard ((AArch64.exec (vld 32) (st 0x1000)).map fun t => t.v .v3) ==
  some (BitVec.ofNat 64 13 ++ BitVec.ofNat 64 12)
-- The last two words.
#guard ((AArch64.exec (vld 48) (st 0x1000)).map fun t => t.v .v3) ==
  some (BitVec.ofNat 64 15 ++ BitVec.ofNat 64 14)
-- Past the table (the second word past its end), and an offset `ldr q`
-- does not encode (not a multiple of 16, or at least 65536): faults.
#guard (AArch64.exec (vld 64) (st 0x1000)).isNone
#guard (AArch64.exec (vld 56) (st 0x1000)).isNone
#guard (AArch64.exec (vld 8) (st 0x1000)).isNone
#guard (AArch64.exec (.ldrqTbl .v3 .x2 65536 name ((List.range 8194).map fun _ => 0)) (st 0x1000)).isNone
-- A base register not holding the table's address: faults, even when the
-- address it forms is in the table (the hardware would read whatever is at
-- `x2 + off`, not the table).
#guard (AArch64.exec (vld 16) (st 0x0FF0)).isNone
#guard (AArch64.exec (vld 0) (st 0x1010)).isNone
-- The taint analyses: the offset is public whatever `x2` is, and the words
-- loaded are public to the vector one.
#guard (VG.AArch64.Taint.step (RegSet.ofList []) (vld 16)).isSome
#guard ((VG.AArch64.VectorTaint.step (RegSet.ofList [], RegSet.ofList []) (vld 16)).map fun τ => τ.2.mem .v3) ==
  some true

end VG.Test.TableInstrAArch64
