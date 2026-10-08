import VerifiedGarbage.Proof.AesCfb8.X86_64.Loop
import VerifiedGarbage.Proof.AesCbc.X86_64.Body

/-!
# AES-CFB8 on x86-64: the code between the calls

The straight-line pieces of a byte, run once each: the arguments of the
call on the copy of the input block (`args`), the data byte XORed with the
first byte of the enciphered block (`encByte`, `decByte`), and the input
block shifted (`shift`), with their memories as explicit writes
(`shiftMem64`, `Proof/AesCfb8/Mem.lean`).
-/

namespace VG.Proof.AesCfb8.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCbc.X86_64 VG.Impl.AesCfb8.X86_64
open VG.Proof.AesCbc.X86_64 (offset_nat)

/-- The arguments of the call on the copy of the input block. -/
def args : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (.imm cOff),
   .mov32 .rcx (.imm 1), .mov .r8 (.reg .r15)]

theorem pre_eq : pre = copy .r15 cOff .r12 0 ++ args := rfl

theorem args_ok (s : State) :
    ∃ s', runBlock isa args s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 2048 ∧
      s'.gpr .rcx = 1 ∧ s'.gpr .r8 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [args, cOff, runBlock_cons, runStep_some, exec, execAlu, readSrc, Option.map_some,
      Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, State.setReg32]

/-- The first four instructions of `encPost`. -/
def encByte : List Instr :=
  [.movzx8 .rax (at_ .r13 0), .movzx8 .rcx (at_ .r15 cOff), .alu .xor .rax (.reg .rcx),
   .store8 (at_ .r13 0) .rax]

/-- The first four instructions of `decPost`. -/
def decByte : List Instr :=
  [.movzx8 .rax (at_ .r13 0), .movzx8 .rcx (at_ .r15 cOff), .alu .xor .rcx (.reg .rax),
   .store8 (at_ .r13 0) .rcx]

theorem encPost_eq : encPost = encByte ++ (shift ++ Impl.AesCfb8.X86_64.advance) := rfl

theorem decPost_eq : decPost = decByte ++ (shift ++ Impl.AesCfb8.X86_64.advance) := rfl

theorem low_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem low_zext (a : Byte) : (a.setWidth 64).setWidth 8 = a := by
  ext i hi; simp

theorem encByte_ok (s : State) {P T : Addr} (hp : s.gpr .r13 = P) (ht : s.gpr .r15 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa encByte s = some s' ∧ (s'.gpr .rax).setWidth 8 = s.mem P ^^^ s.mem T ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem T) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, encByte, cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, State.load8, State.store8, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, BitVec.add_zero, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, h₁, h₂]
  · simp only [low_xor]

theorem decByte_ok (s : State) {P T : Addr} (hp : s.gpr .r13 = P) (ht : s.gpr .r15 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa decByte s = some s' ∧ (s'.gpr .rax).setWidth 8 = s.mem P ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW P (s.mem T ^^^ s.mem P) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, decByte, cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, State.load8, State.store8, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, BitVec.add_zero, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, h₁, h₂]
  · simp only [low_xor]

theorem shift_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (r1 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 1) 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w7 : InRegions s.wr (Q + BitVec.ofNat 64 7) 8)
    (w15 : InRegions s.wr (Q + BitVec.ofNat 64 15) 1) :
    ∃ s', runBlock isa shift s = some s' ∧
      (∀ r, r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = AesCfb8.shiftMem64 s.mem Q ((s.gpr .rax).setWidth 8) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, shift, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.store8, State.ea, offset_nat, Option.map_some,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hq, BitVec.add_zero, r1, r8, w0, w7, w15]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, h₁, h₂]

end VG.Proof.AesCfb8.X86_64
