import VerifiedGarbage.Proof.AesCfb8.Arm.Loop
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# AES-CFB8 on ARMv7: the code after the call

The straight-line pieces after a call, run once each: the data byte XORed
with the first byte of the enciphered block (`encByte`, `decByte`), and the
input block shifted (`shift`), with their memories as explicit writes
(`shiftMem32`, `Proof/AesCfb8/Mem.lean`).
-/

namespace VG.Proof.AesCfb8.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCfb8.Arm
open VG.Impl.AesCbc.Arm (cOff)

/-- The byte instructions of `encPost`. -/
def encByte : List Instr :=
  [.ldrb .r12 .r7 0, .ldrb .lr .r10 cOff, .dp .eor .r12 .r12 (.reg .lr), .strb .r12 .r7 0]

/-- The byte instructions of `decPost`. -/
def decByte : List Instr :=
  [.ldrb .r12 .r7 0, .ldrb .lr .r10 cOff, .dp .eor .lr .lr (.reg .r12), .strb .lr .r7 0]

theorem encPost_eq : encPost = encByte ++ (shift ++ Impl.AesCfb8.Arm.advance) := rfl

theorem decPost_eq : decPost = decByte ++ (shift ++ Impl.AesCfb8.Arm.advance) := rfl

theorem low_xor (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem encByte_ok (s : State) {P T : Addr} (hp : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = P)
    (ht : State.addr (s.gpr .r10 + BitVec.ofNat 32 2048) = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa encByte s = some s' ∧ s'.gpr .r12 = (s.mem P ^^^ s.mem T).setWidth 32 ∧
      (∀ r, r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem T) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, encByte, cOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Op2.eval, State.load8, State.store8, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hp, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [low_xor]

theorem decByte_ok (s : State) {P T : Addr} (hp : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = P)
    (ht : State.addr (s.gpr .r10 + BitVec.ofNat 32 2048) = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa decByte s = some s' ∧ s'.gpr .r12 = (s.mem P).setWidth 32 ∧
      (∀ r, r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW P (s.mem T ^^^ s.mem P) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, decByte, cOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Op2.eval, State.load8, State.store8, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hp, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [low_xor]

theorem shift_ok (s : State) {Q : Addr} {c : Byte} (hq : State.addr (s.gpr .r6) = Q)
    (hfit : (s.gpr .r6).toNat + 16 ≤ 2 ^ 32) (hc : s.gpr .r12 = c.setWidth 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa shift s = some s' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = AesCfb8.shiftMem32 s.mem Q c ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : State.addr (s.gpr .r6 + BitVec.ofNat 32 d) = Q + BitVec.ofNat 64 d := by
    rw [addr_add (by omega), hq]
  have a0 : State.addr (s.gpr .r6 + BitVec.ofNat 32 0) = Q := by rw [a 0 (by decide)]; simp
  have w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, shift, runBlock_cons, runStep_some, runBlock_nil, exec,
      State.load32, State.store32, State.store8, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, a0, a 1 (by decide), a 5 (by decide),
      a 9 (by decide), a 12 (by decide), a 4 (by decide), a 8 (by decide), a 11 (by decide), a 15 (by decide),
      hr 1 4 (by decide), hr 5 4 (by decide), hr 9 4 (by decide), hr 12 4 (by decide), w0,
      hw 4 4 (by decide), hw 8 4 (by decide), hw 11 4 (by decide), hw 15 1 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => by simp [gpr_setReg, h₁, h₂, h₃, h₄], rfl, ?_, rfl, rfl⟩
  simp only [hc, AesCfb8.shiftMem32]
  congr 1
  ext i hi; simp

end VG.Proof.AesCfb8.Arm
