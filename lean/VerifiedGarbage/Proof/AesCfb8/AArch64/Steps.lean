import VerifiedGarbage.Proof.AesCfb8.AArch64.Loop
import VerifiedGarbage.Proof.AesCbc.AArch64.Body

/-!
# AES-CFB8 on AArch64: the code between the calls

The straight-line pieces of a byte, run once each: the arguments of the
call on the copy of the input block (`args`), the data byte XORed with the
first byte of the enciphered block (`encByte`, `decByte`), and the input
block shifted (`shift`), with their memories as explicit writes
(`shiftMemX`, `Proof/AesCfb8/Mem.lean`).
-/

namespace VG.Proof.AesCfb8.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCfb8.AArch64
open VG.Impl.AesCbc.AArch64 (mov cOff copy)

theorem read1 (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [BitVec.add_zero] at this
  rw [← this]
  exact (BitVec.extractLsb'_eq_self (x := m.read a 1)).symm

theorem write1 (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v = m.writeW a v := by
  simp [Mem.writeW]

/-- The arguments of the call on the copy of the input block. -/
def args : List Instr := [mov .x0 .x19, mov .x1 .x20, .addImm .x .x2 .x24 2048, .movz .x .x3 1 0, mov .x4 .x24]

theorem pre_eq : pre = copy .x24 cOff .x21 0 ++ args := rfl

theorem args_ok (s : State) :
    ∃ s', runBlock isa args s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = s.gpr .x24 + BitVec.ofNat 64 2048 ∧
      s'.gpr .x3 = 1 ∧ s'.gpr .x4 = s.gpr .x24 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [args, exec_addImm_x (show 2048 < 4096 by decide)], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], ?_, by simp [gpr_write],
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- The byte instructions of `encPost`. -/
def encByte : List Instr := [.ldrb .x9 .x22 0, .ldrb .x10 .x24 cOff, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x22 0]

/-- The byte instructions of `decPost`. -/
def decByte : List Instr := [.ldrb .x9 .x22 0, .ldrb .x10 .x24 cOff, .logic .eor .x .x10 .x10 .x9, .strb .x10 .x22 0]

theorem encPost_eq : encPost = encByte ++ (shift ++ Impl.AesCfb8.AArch64.advance) := rfl

theorem decPost_eq : decPost = decByte ++ (shift ++ Impl.AesCfb8.AArch64.advance) := rfl

theorem zext_xor (a b : Byte) :
    (a.setWidth 32).setWidth 64 ^^^ (b.setWidth 32).setWidth 64 = (a ^^^ b).setWidth 64 := by
  ext i hi; simp

theorem zext_zext (a : Byte) : (a.setWidth 32).setWidth 64 = a.setWidth 64 := by
  ext i hi; simp

theorem low_xor (a b : Byte) :
    (((a.setWidth 32).setWidth 64 ^^^ (b.setWidth 32).setWidth 64).setWidth 32).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem encByte_ok (s : State) {P T : Addr} (hp : s.gpr .x22 = P) (ht : s.gpr .x24 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa encByte s = some s' ∧ s'.gpr .x9 = (s.mem P ^^^ s.mem T).setWidth 64 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem T) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [encByte, cOff, read1, write1, hp, ht, rP, rT, wP], ?_⟩
  refine ⟨by simp [gpr_write], fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [low_xor]

theorem decByte_ok (s : State) {P T : Addr} (hp : s.gpr .x22 = P) (ht : s.gpr .x24 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa decByte s = some s' ∧ s'.gpr .x9 = (s.mem P).setWidth 64 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW P (s.mem T ^^^ s.mem P) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [decByte, cOff, read1, write1, hp, ht, rP, rT, wP], ?_⟩
  refine ⟨by simp [gpr_write, zext_zext], fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [low_xor]

theorem shift_ok (s : State) {Q : Addr} {c : Byte} (hq : s.gpr .x21 = Q) (hc : s.gpr .x9 = c.setWidth 64)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa shift s = some s' ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = AesCfb8.shiftMemX s.mem Q c ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [shift, hq, hc, r0, r8, w0, w8], ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, ?_, rfl, rfl⟩
  simp only [AesCfb8.shiftMemX, Mem.writeW, Mem.readW, BitVec.setWidth_eq]

end VG.Proof.AesCfb8.AArch64
