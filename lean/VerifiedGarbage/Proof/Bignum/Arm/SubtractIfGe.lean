module

public import VerifiedGarbage.Impl.Bignum.Arm.SubtractIfGe
public import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasState
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Exact conditional subtraction and the borrow used by RSA division -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem subtractIfGe_ok (s : State) {base : BitVec 32} {size out a b tmp n : Nat}
    (ctx : SubCtx s base size tmp a b n)
    (selCtx : SelectCtx s base size out tmp a n) (hn : 0 < n)
    (p0 : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (p10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (p12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (p9 : s.gpr .r9 = base + BitVec.ofNat 32 out)
    (count : s.gpr .lr = BitVec.ofNat 32 n) (savedCount : s.gpr .r7 = BitVec.ofNat 32 n)
    (carry : s.gpr .r11 = 0) :
    WP isa subtractIfGe s fun t =>
      val32 t.mem (State.addr base) out n =
        (if val32 s.mem (State.addr base) a n < val32 s.mem (State.addr base) b n
        then val32 s.mem (State.addr base) a n
        else val32 s.mem (State.addr base) a n - val32 s.mem (State.addr base) b n) ∧
      (t.gpr .r11).toNat = (if val32 s.mem (State.addr base) a n <
        val32 s.mem (State.addr base) b n then 1 else 0) ∧
      Outs (State.addr base) [(tmp, 4 * n), (out, 4 * n)] s.mem t.mem ∧
      Rest subLoopClobbers s t := by
  rw [subtractIfGe, WP.seq_iff]
  refine WP.mono (subRow_ok s ctx hn p0 p10 p12 count (by rw [carry]; decide)) ?_
  intro u inv
  have diff := inv.value
  simp only [carry, show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero] at diff
  have al := val32_lt s.mem (State.addr base) a n
  have bl := val32_lt s.mem (State.addr base) b n
  have tl := val32_lt u.mem (State.addr base) tmp n
  have bit : (u.gpr .r11).toNat = if val32 s.mem (State.addr base) a n <
      val32 s.mem (State.addr base) b n then 1 else 0 := by
    have bound := inv.borrow
    have cases : (u.gpr .r11).toNat = 0 ∨ (u.gpr .r11).toNat = 1 := by omega
    rcases cases with h | h <;> rw [h] at diff ⊢ <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at diff <;> split <;> omega
  have oldA := inv.outside.val32 (d := a) (k := n)
    (by have := ctx.sepA; omega) (by have := ctx.aFits; have := ctx.nowrap; omega)
  rw [WP.seq_iff]
  refine WP.mono (selectPrepare_ok u) ?_
  rintro v ⟨vp0, vp10, vp12, vc, keep⟩
  have saved : u.gpr .r7 = BitVec.ofNat 32 n :=
    (inv.rest.gpr .r7 (by simp [subLoopClobbers])).trans savedCount
  have ready : SelectCtx v base size out tmp a n :=
    { selCtx with writable := by rw [keep.wr, inv.rest.wr]; exact selCtx.writable }
  have p0v : v.gpr .r0 = base + BitVec.ofNat 32 out := by
    rw [vp0, inv.rest.gpr .r9 (by simp [subLoopClobbers]), p9]
  have p10v : v.gpr .r10 = base + BitVec.ofNat 32 tmp := by
    rw [vp10, inv.outPtr, saved, rewind32]
  have p12v : v.gpr .r12 = base + BitVec.ofNat 32 a := by
    rw [vp12, inv.aPtr, saved, rewind32]
  have bv : v.gpr .r11 = u.gpr .r11 := keep.regs .r11 (by simp)
  refine WP.mono (selectAliasRow_ok v ready hn p0v p10v p12v (vc.trans saved)
    (by rw [bv]; exact inv.borrow)) ?_
  intro t h
  have bt : t.gpr .r11 = u.gpr .r11 :=
    (h.rest.gpr .r11 (by simp [selectLoopClobbers])).trans bv
  refine ⟨?_, by rw [bt]; exact bit, ?_, ?_⟩
  · rw [h.value, bv, bit, keep.mem, oldA]
    split <;> simp_all only [Nat.one_ne_zero, ↓reduceIte]
    omega
  · have f : Outs (State.addr base) [(tmp, 4 * n), (out, 4 * n)] s.mem v.mem := by
      rw [keep.mem]; exact Outs.of_outside inv.outside (by simp)
    exact f.trans (Outs.of_outside h.outside (by simp))
  · have k : Rest [.r0, .r10, .r12, .lr] u v := ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩
    exact inv.rest.trans ((k.mono (by simp [subLoopClobbers])).trans
      (h.rest.mono (by simp [subLoopClobbers, selectLoopClobbers])))

end VG.Proof.Bignum.Arm
