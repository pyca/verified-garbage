module

import VerifiedGarbage.TCB.Rust
meta import VerifiedGarbage.TCB.Rust
import VerifiedGarbageTest.RenderOnly
meta import VerifiedGarbageTest.RenderOnly
import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.TCB.X86.Print
meta import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.SymFrame
meta import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.ResidueTaint
meta import VerifiedGarbage.Proof.Framework.X86.ResidueTaint
import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# Tables of constants carried by instructions (`movdquTbl`, `movqTbl`) on x86 (32-bit)

A function `()` that takes the address of a table of constants with the
four-byte frame of `symPush` (`call 2f; 2: mov eax, [esp]; add eax, name -
2b`, released by `pop ecx`), then loads words 1 and 2 of the table into
`xmm0` (`movdqu xmm0, XMMWORD PTR [eax+8]`, `movdquTbl`) and word 2 into
`xmm1` (`movq xmm1, QWORD PTR [eax+16]`, `movqTbl`). It is proven against
the contract of its signature under the plain calling convention, with four
bytes of stack and without `abi.withConsts`: the instructions carry the
table's words, the proof shows that the base register holds the table's
address and that the offsets are in the table (the model faults otherwise),
and the accesses are observed as their offsets in the table, 8 and 16,
whatever the table's address. The emitter writes the static from the
instructions, byte for byte, and refuses a table two artifacts give
different words; the model's semantics read the words at the table's
offset, and fault past the table, between its words, or through a base
register not holding its address. The constant-time and residue analyses
take the instructions (a constant offset, a value both runs share) and the
address frame (a secret word and a secret register).
-/

namespace VG.Test.TableInstrX86
open VG VG.X86

def sig : Sig := { params := [], ret := none }
def name : String := "VG_TEST_TBL"

/-- The table `[7, 8, w, 10]`. -/
def tbl (w : BitVec 64) : List (BitVec 64) := [7, 8, w, 10]

def contract : Contract isa :=
  sig.contract abi (post := fun _ _ _ => True) (stack := 4)

def ld16 (w : BitVec 64) : Instr := .movdquTbl .xmm0 { base := .eax, disp := 8 } name (tbl w)
def ld8 (w : BitVec 64) : Instr := .movqTbl .xmm1 { base := .eax, disp := 16 } name (tbl w)

def code (w : BitVec 64) : Prog isa :=
  .seq (.frame (.symPush .eax name) (.block []) (.pop .ecx 1)) (.block [ld16 w, ld8 w])

/-- The state after the loads. -/
def res (w : BitVec 64) (s : State) : State :=
  (s.setXmm .xmm0 (w ++ (8 : BitVec 64))).setXmm .xmm1 ((0 : BitVec 64) ++ w)

/-- The loads, through a register holding the table's address: the offsets leak. -/
theorem exec_loads (w : BitVec 64) (s : State) (h : s.gpr .eax = s.syms name) :
    execBlock isa [ld16 w, ld8 w] s =
      some (res w s, [Leak.addr (BitVec.ofNat 64 8), Leak.addr (BitVec.ofNat 64 16)]) := by
  have e₁ : X86.exec (ld16 w) s = some (s.setXmm .xmm0 (w ++ (8 : BitVec 64))) := by
    simp only [X86.exec, ld16]
    split
    · rfl
    · rename_i hn; exact absurd ⟨h, by decide, (by decide : 8 / 8 + 2 ≤ 4)⟩ hn
  have e₂ : X86.exec (ld8 w) (s.setXmm .xmm0 (w ++ (8 : BitVec 64))) = some (res w s) := by
    simp only [X86.exec, ld8]
    split
    · rfl
    · rename_i hn; exact absurd ⟨h, by decide, (by decide : 16 / 8 < 4)⟩ hn
  simp only [execBlock, isa, e₁, e₂, Option.map_some]
  rfl

/-- What the function leaks: the three accesses of the address frame, at the
word below the stack pointer, and the two offsets in the table. -/
def leaks (s : State) : List Leak :=
  List.replicate 3 (.addr ((s.gpr .esp - 4).setWidth 64)) ++
    [Leak.addr (BitVec.ofNat 64 8), Leak.addr (BitVec.ofNat 64 16)]

theorem exec_code (w : BitVec 64) (s : State) (hsp : 4 ≤ (s.gpr .esp).toNat) :
    ∃ s₁, SymAddrPost name s s₁ ∧ Exec isa (code w) s (leaks s) (res w s₁) := by
  obtain ⟨t, s₁, e, P⟩ := symFrame_ok name s hsp
  have ht := symFrame_trace hsp e
  subst ht
  exact ⟨s₁, P, .seq e (.block (exec_loads w s₁ (by rw [P.addr, P.syms])))⟩

/-- A state satisfying the precondition: the stack at `0x10000`. -/
def sat : State where
  gpr r := if r = .esp then 0x10000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := []
  syms _ := 0x1000

theorem pre_sp {s : State} (h : contract.pre s) :
    4 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [contract, sig, abi, stackBelow] at h
  exact ⟨h.1, h.2.1⟩

theorem verified (w : BitVec 64) : Verified target (code w) contract := by
  refine ⟨fun s h => ?_, .of_leakage leaks (fun s t s' h e => ?_) (fun s₁ s₂ _ _ hp => ?_), ⟨sat, ?_⟩⟩
  · obtain ⟨hsp, hfit⟩ := pre_sp h
    obtain ⟨s₁, P, e⟩ := exec_code w s hsp
    refine ⟨_, _, e, ⟨fun r hr => ?_, P.ret hsp hfit⟩, trivial⟩
    have hne : r ∉ [Reg.eax, Reg.ecx] := by revert hr; cases r <;> decide
    exact P.gpr r hne
  · obtain ⟨s₁, -, e'⟩ := exec_code w s (pre_sp h).1
    exact (Exec.det e e').1
  · sig_pub [contract, sig, abi] at hp
    simp only [leaks, hp]
  · sig_pre [contract, sig, abi, stackBelow, sat]
    exact ⟨by decide, by decide⟩

def artifactOf (fn : String) (w : BitVec 64) : Artifact where
  target := .of (renderOnly target)
  module := "test"
  name := fn
  sig := sig
  doc := "Loads words of its table."
  code := code w
  contract := contract
  verified := renderOnly_verified (verified w)
  stack := 4
  spSafe := rfl

def artifact : Artifact := artifactOf "vg_test_tbl" 42

/-- The rendering: the address frame with the static's symbol, and the loads
through the register, as any memory operand (`pop ecx`, `movdqu xmm0,
XMMWORD PTR [eax+8]`, `movq xmm1, QWORD PTR [eax+16]`, `ret`). -/
def expected : String := "/// Loads words of its table.
#[allow(clippy::missing_safety_doc)]
#[unsafe(naked)]
pub unsafe extern \"C\" fn vg_test_tbl() {
    core::arch::naked_asm!(
        r#\"call 2f
2:
mov eax, DWORD PTR [esp]
.byte 0x81, 192
.long {VG_TEST_TBL} - 2b
.base64 \"WfMPb0AI8w9+SBDD\"
.p2align 6\"#,
        VG_TEST_TBL = sym super::consts::VG_TEST_TBL,
    )
}
"

#guard Rust.function artifact (fun _ => "") == expected

-- The emitter writes the static from the instructions' words, byte for byte,
-- and the code may name it without `Artifact.consts`.
#guard (Rust.checkConsts [.of (.of artifact)] (.of (.of artifact))).isOk
#guard Rust.tables [artifact] == [(name, tbl 42)]
#guard Rust.tableFile "x86" name (tbl 42) ==
  Rust.header ++ "//! The table of constants `VG_TEST_TBL` of the verified functions for `x86` (`Artifact.consts`).
#![allow(dead_code)]

use super::Table;

/// The table of constants `VG_TEST_TBL` (`Artifact.consts`).
pub static VG_TEST_TBL: Table<32> = Table(*b\"\\
    \\x07\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\
    \\x08\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\
    \\x2a\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\
    \\x0a\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\
\");
"

-- Two artifacts carrying the same table: one static. Another giving it other
-- words: refused.
def same : Artifact := artifactOf "vg_test_tbl_same" 42
def other : Artifact := artifactOf "vg_test_tbl_other" 41
#guard (Rust.checkConsts [.of (.of artifact), .of (.of same)] (.of (.of artifact))).isOk
#guard Rust.tables [artifact, same] == [(name, tbl 42)]
#guard !(Rust.checkConsts [.of (.of artifact), .of (.of other)] (.of (.of artifact))).isOk
#guard !(Rust.checkConsts [.of (.of artifact), .of (.of other)] (.of (.of other))).isOk

/-! ## The instructions -/

/-- The table at `0x1000`, its address in `eax`. -/
def at1000 : State := { sat with gpr := fun r => if r = .eax then 0x1000 else 0 }

-- Printed and encoded as the loads they are (`movdquLoad`, `movqLoad`: F3 0F
-- 6F /r and F3 0F 7E /r, with `[ebp]` taking a displacement byte and `[esp]`
-- a SIB byte); in the baseline; each carries its table.
#guard Instr.asm (ld16 42) == ["movdqu xmm0, XMMWORD PTR [eax+8]"]
#guard Instr.asm (ld8 42) == ["movq xmm1, QWORD PTR [eax+16]"]
#guard (ld16 42).encode == some [[0xF3, 0x0F, 0x6F, 0x40, 0x08]]
#guard (ld8 42).encode == some [[0xF3, 0x0F, 0x7E, 0x48, 0x10]]
#guard (Instr.movdquTbl .xmm0 { base := .ebp } name (tbl 42)).encode == some [[0xF3, 0x0F, 0x6F, 0x45, 0x00]]
#guard (Instr.movqTbl .xmm7 { base := .esp, disp := 8 } name (tbl 42)).encode ==
  some [[0xF3, 0x0F, 0x7E, 0x7C, 0x24, 0x08]]
#guard (ld16 42).encode == (Instr.movdquLoad .xmm0 { base := .eax, disp := 8 }).encode
#guard (ld8 42).encode == (Instr.movqLoad .xmm1 { base := .eax, disp := 16 }).encode
#guard (Instr.movdquTbl .xmm0 { base := .eax, disp := 2 ^ 32 } name (tbl 42)).encode.isNone
#guard (ld16 42).requires.isEmpty && (ld8 42).requires.isEmpty
#guard isa.writesSp (ld16 42) == false && isa.writesSp (ld8 42) == false
#guard printer.tables (ld16 42) == [(name, tbl 42)] && printer.tables (ld8 42) == [(name, tbl 42)]
-- The access is observed as the offset, wherever the table is.
#guard addrs (ld16 42) at1000 == [8] && addrs (ld8 42) at1000 == [16]
#guard addrs (ld16 42) { sat with gpr := fun r => if r = .eax then 0x2000 else 0, syms := fun _ => 0x2000 } == [8]
-- The values: words 1 and 2 (bits 63:0 the first), and word 2 under a zero
-- high half; nothing else changes.
#guard ((X86.exec (ld16 42) at1000).map fun t => (t.xmm .xmm0, t.xmm .xmm1, t.gpr .eax, t.cf)) ==
  some ((42 : BitVec 64) ++ (8 : BitVec 64), 0, 0x1000, none)
#guard ((X86.exec (ld8 42) { at1000 with xmm := fun _ => -1 }).map fun t => (t.xmm .xmm1, t.xmm .xmm0)) ==
  some ((0 : BitVec 64) ++ (42 : BitVec 64), -1)
-- The last words of the table.
#guard ((X86.exec (.movdquTbl .xmm2 { base := .eax, disp := 16 } name (tbl 42)) at1000).map fun t =>
  t.xmm .xmm2) == some ((10 : BitVec 64) ++ (42 : BitVec 64))
#guard ((X86.exec (.movqTbl .xmm2 { base := .eax, disp := 24 } name (tbl 42)) at1000).map fun t =>
  t.xmm .xmm2) == some ((0 : BitVec 64) ++ (10 : BitVec 64))
-- Past the table, and between its words: faults.
#guard (X86.exec (.movdquTbl .xmm0 { base := .eax, disp := 24 } name (tbl 42)) at1000).isNone
#guard (X86.exec (.movqTbl .xmm0 { base := .eax, disp := 32 } name (tbl 42)) at1000).isNone
#guard (X86.exec (.movdquTbl .xmm0 { base := .eax, disp := 4 } name (tbl 42)) at1000).isNone
#guard (X86.exec (.movqTbl .xmm0 { base := .eax, disp := 12 } name (tbl 42)) at1000).isNone
-- A base register not holding the table's address: faults, even when the
-- address it forms is in the table.
#guard (X86.exec (.movdquTbl .xmm0 { base := .eax, disp := 16 } name (tbl 42))
  { sat with gpr := fun r => if r = .eax then 0x0FF8 else 0 }).isNone
#guard (X86.exec (.movqTbl .xmm0 { base := .eax, disp := 16 } name (tbl 42))
  { sat with gpr := fun r => if r = .eax then 0x0FF8 else 0 }).isNone
#guard (X86.exec (ld16 42) { at1000 with gpr := fun r => if r = .ecx then 0x1000 else 0 }).isNone

/-! ## The analyses -/

/-- A taint with `esp` and `eax` public, the flags public, one writable
region, and sixteen bytes of stack to use. -/
def τ : X86.Taint.T := { regs := .ofList [.esp, .eax], flags := true, lens := [8], room := 16 }

-- Constant time: a table load leaks a constant, and changes no register the
-- analysis tracks; the scalar analysis has no SSE instruction.
#guard ((X86.SseTaint.step τ (ld16 42)).map fun t => (X86.Taint.pub t .eax, t.flags, t.stk)) == some (true, true, [])
#guard ((X86.SseTaint.step τ (ld8 42)).map fun t => (X86.Taint.pub t .eax, t.flags, t.stk)) == some (true, true, [])
#guard (X86.SseTaint.step { τ with regs := .ofList [.esp] } (ld16 42)).isSome
#guard (X86.Taint.step τ (ld16 42)).isNone
-- The address frame: a frame of four bytes holding a secret, a secret
-- register (no contract says the address is the same in two runs) and
-- secret flags; not through `esp`, nor without the stack for it.
#guard ((X86.Taint.pushStep τ (.symPush .eax name)).map fun t =>
  (X86.Taint.pub t .eax, X86.Taint.pub t .esp, t.flags, t.stk, t.lens)) == some (false, true, false, [some 4], [4, 8])
#guard (X86.Taint.pushStep τ (.symPush .esp name)).isNone
#guard (X86.Taint.pushStep { τ with room := 3 } (.symPush .eax name)).isNone
#guard (X86.Taint.pushStep { τ with regs := .ofList [.eax] } (.symPush .eax name)).isNone
-- The copy the checks' hints are computed with (`NativeHintData.lean`) says the same.
#guard ((NativeHints.X86.pushStep { regs := .ofList [.esp, .eax], flags := true, lens := [8], room := 16 }
  (.symPush .eax name)).map fun t =>
    (NativeHints.X86.pub t .eax, NativeHints.X86.pub t .esp, t.flags, t.stk, t.lens)) ==
  some (false, true, false, [some 4], [4, 8])
#guard (NativeHints.X86.pushStep { regs := .ofList [.esp, .eax], flags := true, lens := [8], room := 3 }
  (.symPush .eax name)).isNone
-- Residue: what a table load leaves in its register is the same in both
-- runs, unlike a load from memory.
#guard ((X86.RTaint.stepB (X86.RTaint.setX (X86.RTaint.init 0 0) .xmm0 false) (ld16 42)).map fun t =>
  X86.RTaint.pubX t .xmm0) == some true
#guard ((X86.RTaint.stepB (X86.RTaint.setX (X86.RTaint.init 0 0) .xmm1 false) (ld8 42)).map fun t =>
  X86.RTaint.pubX t .xmm1) == some true
#guard ((X86.RTaint.stepB (X86.RTaint.init 0 0) (.movdquLoad .xmm0 { base := .eax })).map fun t =>
  X86.RTaint.pubX t .xmm0) == some false

end VG.Test.TableInstrX86
