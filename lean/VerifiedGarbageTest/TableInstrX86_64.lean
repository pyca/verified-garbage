import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Tables of constants carried by instructions (`aluTbl`, `vmovdquTbl`) on x86-64

A function `() -> u64` that returns 1 plus word 1 of a table of constants:
`lea rdx, [rip + VG_TEST_ALUTBL]` (`leaSym`), `movabs rax, 1`, then `add rax,
QWORD PTR [rdx+8]` (`aluTbl`, carrying the table). It is proven against the
contract of its signature under the plain calling convention, without
`abi.withConsts`: the instruction carries the table's words, and its access
is observed as its offset in the table, 8, whatever the table's address. The
emitter writes the static from the instruction, byte for byte, and refuses a
table two artifacts give different words; the model's semantics read the
word at the table's offset, and fault outside the table, between its words,
or through a base register not holding its address.
-/

namespace VG.Test.TableInstrX86_64
open VG VG.X86_64

def sig : Sig := { params := [], ret := some .u64 }
def name : String := "VG_TEST_ALUTBL"

/-- The table `[7, w]`. -/
def tbl (w : BitVec 64) : List (BitVec 64) := [7, w]

def contract (w : BitVec 64) : Contract isa :=
  sig.contract abi (post := fun m m' r => r.toNat = (1 + w).toNat ∧ m' = m)

def add (w : BitVec 64) : Instr := .aluTbl .add .rax { base := .rdx, disp := 8 } name (tbl w)

def code (w : BitVec 64) : Prog isa := .block [.leaSym .rdx name, .movImm64 .rax 1, add w]

/-- The state after the code. -/
def res (w : BitVec 64) (s : State) : State :=
  let s₂ := (s.setReg .rdx (s.syms name)).setReg .rax 1
  (arithFlags s₂ (1 + w) (decide (2 ^ 64 ≤ (1 : BitVec 64).toNat + w.toNat))
    (addOverflow 1 w (1 + w))).setReg .rax (1 + w)

theorem exec_code (w : BitVec 64) (s : State) :
    execBlock isa [.leaSym .rdx name, .movImm64 .rax 1, add w] s =
      some (res w s, [Leak.addr (BitVec.ofInt 64 8)]) := by
  let s₂ := (s.setReg .rdx (s.syms name)).setReg .rax 1
  have hoff : s₂.ea { base := .rdx, disp := 8 } - s₂.gpr .rdx = BitVec.ofInt 64 8 := by
    simp only [State.ea]
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  have hoff' : s₂.ea { base := .rdx, disp := 8 } - s₂.syms name = BitVec.ofInt 64 8 := hoff
  have h8 : (BitVec.ofInt 64 8).toNat = 8 := by decide
  have e₁ : X86_64.exec (.leaSym .rdx name) s = some (s.setReg .rdx (s.syms name)) := rfl
  have e₂ : X86_64.exec (.movImm64 .rax 1) (s.setReg .rdx (s.syms name)) = some s₂ := rfl
  have e₃ : X86_64.exec (add w) s₂ = execAluW .add .rax w s₂ := by
    have hb : s₂.gpr .rdx = s₂.syms name := rfl
    simp only [X86_64.exec, add, hb, hoff', h8, tbl, List.length_cons, List.length_nil]
    rfl
  have hA : addrs (add w) s₂ = [BitVec.ofInt 64 8] := by simp only [addrs, add, hoff]
  simp only [execBlock, isa, e₁, e₂, e₃, execAluW, Option.map_some, hA]
  rfl

theorem res_gpr (w : BitVec 64) (s : State) (r : Reg) (h1 : r ≠ .rax) (h2 : r ≠ .rdx) :
    (res w s).gpr r = s.gpr r := by
  simp only [res, State.setReg, arithFlags, State.setFlags, h1, h2, ↓reduceIte]

/-- A state satisfying the precondition: the stack at `0x10000`. -/
def sat : State where
  gpr r := if r = .rsp then 0x10000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := []
  syms _ := 0x1000

theorem verified (w : BitVec 64) : Verified target (code w) (contract w) := by
  refine ⟨fun s _ => ?_, .of_leakage (fun _ => [Leak.addr (BitVec.ofInt 64 8)])
      (fun s t s' _ e => ?_) (fun _ _ _ _ _ => rfl), ⟨sat, ?_⟩⟩
  · refine ⟨_, _, .block (exec_code w s), ⟨fun r hr' => ?_, rfl, rfl⟩, ?_⟩
    · have h1 : r ≠ .rax := fun e => by subst e; exact absurd hr' (by decide)
      have h2 : r ≠ .rdx := fun e => by subst e; exact absurd hr' (by decide)
      exact res_gpr w s r h1 h2
    · sig_post [contract, sig, abi, argRegs]
  · cases e with | block e => rw [exec_code w s] at e; cases e; rfl
  · sig_pre [contract, sig, abi, argRegs, stackBelow, sat]

def artifactOf (fn : String) (w : BitVec 64) : Artifact where
  target := target
  module := "test"
  name := fn
  sig := sig
  doc := "Returns 1 plus word 1 of its table."
  code := code w
  contract := contract w
  verified := verified w
  spSafe := rfl

def artifact : Artifact := artifactOf "vg_test_alutbl" 42

/-- The rendering: the table read through a register, as any memory operand. -/
def expected : String := "/// Returns 1 plus word 1 of its table.
#[allow(clippy::missing_safety_doc)]
#[unsafe(naked)]
pub unsafe extern \"sysv64\" fn vg_test_alutbl() -> u64 {
    core::arch::naked_asm!(
        r\"lea rdx, [rip + {VG_TEST_ALUTBL}]\",
        // movabs rax, 1
        // add rax, QWORD PTR [rdx+8]
        // ret
        r\".byte 0x48,0xb8,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x48,0x03,0x42,0x08,0xc3
.p2align 6\",
        VG_TEST_ALUTBL = sym super::consts::VG_TEST_ALUTBL,
    )
}
"

#guard Rust.function artifact (fun _ => "") == expected

-- The emitter writes the static from the instruction's words, byte for byte,
-- and the code may name it without `Artifact.consts`.
#guard (Rust.checkConsts [.of artifact] (.of artifact)).isOk
#guard Rust.tables [artifact] == [(name, tbl 42)]
#guard Rust.tableFile "x86_64" name (tbl 42) ==
  Rust.header ++ "//! The table of constants `VG_TEST_ALUTBL` of the verified functions for `x86_64` (`Artifact.consts`).
#![allow(dead_code)]

use super::Table;

/// The table of constants `VG_TEST_ALUTBL` (`Artifact.consts`).
pub static VG_TEST_ALUTBL: Table<16> = Table(*b\"\\
    \\x07\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\
    \\x2a\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\
\");
"

-- Two artifacts carrying the same table: one static. Another giving it other
-- words: refused.
def same : Artifact := artifactOf "vg_test_alutbl_same" 42
def other : Artifact := artifactOf "vg_test_alutbl_other" 41
#guard (Rust.checkConsts [.of artifact, .of same] (.of artifact)).isOk
#guard Rust.tables [artifact, same] == [(name, tbl 42)]
#guard !(Rust.checkConsts [.of artifact, .of other] (.of artifact)).isOk
#guard !(Rust.checkConsts [.of artifact, .of other] (.of other)).isOk

-- The semantics: the word at the table's offset, else a fault.
#guard Instr.asm (add 42) == ["add rax, QWORD PTR [rdx+8]"]
#guard (add 42).requires.isEmpty
#guard isa.writesSp (add 42) == false
-- The access is observed as the offset, wherever the table is.
#guard addrs (add 42) { sat with gpr := fun r => if r = .rdx then 0x1000 else 0 } == [8]
#guard addrs (add 42) { sat with gpr := fun r => if r = .rdx then 0x2000 else 0 } == [8]
#guard ((X86_64.exec (add 42)
  { sat with gpr := fun r => if r = .rdx then 0x1000 else if r = .rax then 1 else 0 }).map fun t =>
    (t.gpr .rax, t.cf, t.zf)) == some (43, some false, some false)
-- Word 0, through an index register.
#guard ((X86_64.exec (.aluTbl .sub .rax { base := .rdx, index := some .rcx, scale := 8 } name (tbl 42))
  { sat with gpr := fun r => if r = .rdx then 0x1000 else if r = .rax then 10 else 0 }).map fun t =>
    t.gpr .rax) == some 3
-- Past the table, and between its words: faults.
#guard (X86_64.exec (.aluTbl .add .rax { base := .rdx, disp := 16 } name (tbl 42))
  { sat with gpr := fun r => if r = .rdx then 0x1000 else 0 }).isNone
#guard (X86_64.exec (.aluTbl .add .rax { base := .rdx, disp := 4 } name (tbl 42))
  { sat with gpr := fun r => if r = .rdx then 0x1000 else 0 }).isNone
-- Below the table: the offset wraps around, and faults.
#guard (X86_64.exec (.aluTbl .add .rax { base := .rdx, disp := -8 } name (tbl 42))
  { sat with gpr := fun r => if r = .rdx then 0x1008 else 0 }).isNone
-- A base register not holding the table's address: faults, even when the
-- address it forms is in the table.
#guard (X86_64.exec (.aluTbl .add .rax { base := .rdx, disp := 8 } name (tbl 42))
  { sat with gpr := fun r => if r = .rdx then 0x0FF8 else 0 }).isNone

/-! ## `vmovdquTbl`: four words of a table into a `ymm` register -/

/-- The table `[8, 9, …, 15]`, whose words differ from their indices. -/
def vtbl : List (BitVec 64) := (List.range 8).map fun j => BitVec.ofNat 64 (8 + j)

def vld (m : MemOp) : Instr := .vmovdquTbl .xmm3 m name vtbl

def at1000 : State := { sat with gpr := fun r => if r = .rdx then 0x1000 else 0 }

-- Printed as any `vmovdqu` load; needs AVX, as `vmovdquLoad`; carries its table.
#guard Instr.asm (vld { base := .rdx, disp := 32 }) == ["vmovdqu ymm3, YMMWORD PTR [rdx+32]"]
#guard (vld { base := .rdx }).requires == ["avx"]
#guard isa.writesSp (vld { base := .rdx }) == false
#guard printer.tables (vld { base := .rdx }) == [(name, vtbl)]
-- The access is observed as the offset, wherever the table is.
#guard addrs (vld { base := .rdx, disp := 32 }) at1000 == [32]
#guard addrs (vld { base := .rdx, disp := 32 })
  { sat with gpr := fun r => if r = .rdx then 0x2000 else 0 } == [32]
-- Words 4 to 7, the first in bits 63:0: the 32 bytes at the offset,
-- little-endian, as `vmovdquLoad .l256` reads them from memory.
#guard ((X86_64.exec (vld { base := .rdx, disp := 32 }) at1000).map fun t => t.ymm .xmm3) ==
  some ((BitVec.ofNat 64 15 ++ BitVec.ofNat 64 14) ++ (BitVec.ofNat 64 13 ++ BitVec.ofNat 64 12))
-- Words 1 to 4, through an index register: any multiple of 8 is allowed.
#guard ((X86_64.exec (vld { base := .rdx, index := some .rcx, scale := 8 })
  { sat with gpr := fun r => if r = .rdx then 0x1000 else if r = .rcx then 1 else 0 }).map
    fun t => t.ymm .xmm3) ==
  some ((BitVec.ofNat 64 12 ++ BitVec.ofNat 64 11) ++ (BitVec.ofNat 64 10 ++ BitVec.ofNat 64 9))
-- Past the table (the last word past its end), and between its words: faults.
#guard (X86_64.exec (vld { base := .rdx, disp := 40 }) at1000).isNone
#guard (X86_64.exec (vld { base := .rdx, disp := 4 }) at1000).isNone
-- Below the table: the offset wraps around, and faults.
#guard (X86_64.exec (vld { base := .rdx, disp := -8 })
  { sat with gpr := fun r => if r = .rdx then 0x1008 else 0 }).isNone
-- A base register not holding the table's address: faults.
#guard (X86_64.exec (vld { base := .rdx, disp := 8 })
  { sat with gpr := fun r => if r = .rdx then 0x0FF8 else 0 }).isNone

end VG.Test.TableInstrX86_64
