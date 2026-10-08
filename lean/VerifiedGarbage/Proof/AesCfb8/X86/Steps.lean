import VerifiedGarbage.Proof.AesCfb8.X86.Loop
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# AES-CFB8 on x86: the code after the call

The straight-line pieces after a call, run once each: the data byte XORed
with the first byte of the enciphered block (`encByte`, `decByte`), and the
input block shifted (`shift`), with their memories as explicit writes
(`shiftMem32`, `Proof/AesCfb8/Mem.lean`).
-/

namespace VG.Proof.AesCfb8.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCfb8.X86
open VG.Impl.AesCbc.X86 (cOff)
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Proof.CmacAes.X86 (ea_at')

/-- The byte instructions of `encPost`. -/
def encByte : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .ecx (at_ .ebp cOff), .alu .xor .eax (.reg .ecx), .store8 (at_ .esi 0) .al]

/-- The byte instructions of `decPost`. -/
def decByte : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .ecx (at_ .ebp cOff), .alu .xor .ecx (.reg .eax), .store8 (at_ .esi 0) .cl]

theorem encPost_eq : encPost = .mov .ebp (argOp 5) :: (encByte ++ (.mov .ebx (argOp 2) ::
    (shift ++ Impl.AesCfb8.X86.advance))) := rfl

theorem decPost_eq : decPost = .mov .ebp (argOp 5) :: (decByte ++ (.mov .ebx (argOp 2) ::
    (shift ++ Impl.AesCfb8.X86.advance))) := rfl

theorem low_xor (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem low_zext (a : Byte) : (a.setWidth 32).setWidth 8 = a := by
  ext i hi; simp

theorem encByte_ok (s : State) {P T : Addr} (hp : addr (s.gpr .esi) 0 = P) (ht : addr (s.gpr .ebp) 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa encByte s = some s' ∧ (s'.gpr .eax).setWidth 8 = s.mem P ^^^ s.mem T ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem T) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, encByte, cOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, State.load8, State.store8, ea_at', execAlu, Option.bind_some, Option.map_some, Reg8.reg,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, h₁, h₂]
  · simp only [low_xor]

theorem decByte_ok (s : State) {P T : Addr} (hp : addr (s.gpr .esi) 0 = P) (ht : addr (s.gpr .ebp) 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa decByte s = some s' ∧ (s'.gpr .eax).setWidth 8 = s.mem P ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW P (s.mem T ^^^ s.mem P) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, decByte, cOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, State.load8, State.store8, ea_at', execAlu, Option.bind_some, Option.map_some, Reg8.reg,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, h₁, h₂]
  · simp only [low_xor]

theorem shift_ok (s : State) {Q : Addr} (hq : (s.gpr .ebx).setWidth 64 = Q) (hfit : (s.gpr .ebx).toNat + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa shift s = some s' ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → r ≠ .ebp → s'.gpr r = s.gpr r) ∧
      s'.mem = AesCfb8.shiftMem32 s.mem Q ((s.gpr .eax).setWidth 8) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : addr (s.gpr .ebx) d = Q + BitVec.ofNat 64 d := by
    rw [addr_eq (by omega), hq]
  have a0 : addr (s.gpr .ebx) 0 = Q := by rw [a 0 (by decide)]; simp
  have w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, shift, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, State.store8, ea_at', Option.map_some, Reg8.reg,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, a0, a 1 (by decide), a 4 (by decide), a 5 (by decide),
      a 8 (by decide), a 9 (by decide), a 11 (by decide), a 12 (by decide), a 15 (by decide),
      hr 1 4 (by decide), hr 5 4 (by decide), hr 9 4 (by decide), hr 12 4 (by decide), w0,
      hw 4 4 (by decide), hw 8 4 (by decide), hw 11 4 (by decide), hw 15 1 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, h₁, h₂, h₃, h₄]

end VG.Proof.AesCfb8.X86
