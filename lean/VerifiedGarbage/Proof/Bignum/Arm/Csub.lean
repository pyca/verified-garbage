module

public import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
public import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
public import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
public import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Final modular reduction: subtraction followed by secret-bit selection -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CsubCtx (s : State) (base : BitVec 32) (size out acc mod tmp n : Nat) : Prop where
  sub : SubCtx s base size tmp acc mod n
  accFits : acc + 4 * (n + 2) ≤ size
  sepTmpAcc : tmp + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ tmp
  outFits : out + 4 * n ≤ size
  sepOutTmp : out + 4 * n ≤ tmp ∨ tmp + 4 * n ≤ out
  sepOutAcc : out + 4 * n ≤ acc ∨ acc + 4 * n ≤ out

/-- An extended accumulator below twice the modulus is reduced exactly,
writing only the temporary and result ranges. The result may alias the
modulus, which has already been consumed when selection starts. -/
theorem csub_ok (s : State) {base : BitVec 32} {size out acc mod tmp n : Nat}
    (ctx : CsubCtx s base size out acc mod tmp n) (hn : 0 < n)
    (p0 : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (p10 : s.gpr .r10 = base + BitVec.ofNat 32 acc)
    (p12 : s.gpr .r12 = base + BitVec.ofNat 32 mod)
    (p9 : s.gpr .r9 = base + BitVec.ofNat 32 out)
    (count : s.gpr .lr = BitVec.ofNat 32 n) (savedCount : s.gpr .r7 = BitVec.ofNat 32 n)
    (carry : s.gpr .r11 = 0)
    (hT : val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n) :
    WP isa csub s fun t =>
      val32 t.mem (State.addr base) out n =
        val32 s.mem (State.addr base) acc (n + 2) % val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(tmp, 4 * n), (out, 4 * n)] s.mem t.mem ∧
      Rest subLoopClobbers s t := by
  have nowrap := ctx.sub.nowrap
  have fits := ctx.accFits
  have sep := ctx.sepTmpAcc
  rw [csub, WP.seq_iff]
  refine WP.mono (subRow_ok s ctx.sub hn p0 p10 p12 count (by rw [carry]; decide)) ?_
  intro u inv
  have atop : State.addr (u.gpr .r10 + BitVec.ofNat 32 0) = off (State.addr base) (acc + 4 * n) := by
    rw [inv.aPtr, Offset.add_add, Nat.add_zero]
    exact VG.Arm.addr_add (by omega)
  have read : InRegions (u.rd ++ u.wr) (off (State.addr base) (acc + 4 * n)) 4 := by
    refine ⟨⟨State.addr base, size⟩, List.mem_append_right _ ?_, Offset.contains_base _ (by omega) (by omega)⟩
    rw [inv.rest.wr]
    exact ctx.sub.writable
  have oldTop := inv.outside.w32 (d := acc + 4 * n) (by omega) (by omega)
  have oldAcc := inv.outside.val32 (d := acc) (k := n) (by omega) (by omega)
  have diff : val32 u.mem (State.addr base) tmp n + val32 s.mem (State.addr base) mod n =
      val32 s.mem (State.addr base) acc n + 2 ^ (32 * n) * (u.gpr .r11).toNat := by
    have h := inv.value
    simpa only [carry, show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero] using h
  have result := csub_value inv.borrow hT diff
  rw [WP.seq_iff]
  refine WP.mono (reduceChoice_ok u _ atop read) ?_
  rintro v ⟨choice, bitBound, memv, keepv⟩
  have choice' : v.gpr .r11 = if (u.gpr .r11).toNat ≤ w32 s.mem (State.addr base) (acc + 4 * n)
      then 0 else 1 := by
    rw [choice]
    change (if (u.gpr .r11).toNat ≤ w32 u.mem (State.addr base) (acc + 4 * n) then 0 else 1) = _
    rw [oldTop]
  have ksv : Rest subLoopClobbers s v := inv.rest.trans (keepv.mono (by simp [subLoopClobbers]))
  rw [WP.seq_iff]
  refine WP.mono (selectPrepare_ok v) ?_
  rintro w ⟨wp0, wp10, wp12, wc, keepw⟩
  have kw : Rest [.r0, .r10, .r12, .lr] v w := ⟨keepw.regs, keepw.rd, keepw.wr, keepw.sp⟩
  have ksw : Rest subLoopClobbers s w := ksv.trans (kw.mono (by simp [subLoopClobbers]))
  have memw : w.mem = u.mem := keepw.mem.trans memv
  have saved : v.gpr .r7 = BitVec.ofNat 32 n := (ksv.gpr .r7 (by simp [subLoopClobbers])).trans savedCount
  have bp0 : w.gpr .r0 = base + BitVec.ofNat 32 out := by
    rw [wp0, ksv.gpr .r9 (by simp [subLoopClobbers]), p9]
  have bp10 : w.gpr .r10 = base + BitVec.ofNat 32 tmp := by
    rw [wp10, keepv.gpr .r0 (by simp), inv.outPtr, saved, rewind32]
  have bp12 : w.gpr .r12 = base + BitVec.ofNat 32 acc := by
    rw [wp12, keepv.gpr .r10 (by simp), inv.aPtr, saved, rewind32]
  have bc : w.gpr .lr = BitVec.ofNat 32 n := wc.trans saved
  have bit : w.gpr .r11 = v.gpr .r11 := keepw.regs .r11 (by simp)
  have selectCtx : SubCtx w base size out tmp acc n :=
    ⟨nowrap, ctx.outFits, ctx.sub.outFits, ctx.sub.aFits, ctx.sepOutTmp, ctx.sepOutAcc,
      by rw [ksw.wr]; exact ctx.sub.writable⟩
  refine WP.mono (selectRow_ok w selectCtx hn bp0 bp10 bp12 bc (by rw [bit]; exact bitBound)) ?_
  intro t sel
  refine ⟨?_, ?_, ?_⟩
  · rw [sel.value, bit, choice', memw, oldAcc]
    by_cases h : (u.gpr .r11).toNat ≤ w32 s.mem (State.addr base) (acc + 4 * n)
    · simpa only [h, ite_true, show (0 : BitVec 32).toNat = 0 from rfl] using result
    · simpa only [h, ite_false, show (1 : BitVec 32).toNat = 1 from rfl, Nat.one_ne_zero] using result
  · have first : Outs (State.addr base) [(tmp, 4 * n), (out, 4 * n)] s.mem w.mem := by
      rw [memw]
      exact Outs.of_outside inv.outside (by simp)
    exact first.trans (Outs.of_outside sel.outside (by simp))
  · exact ksw.trans (sel.rest.mono (by simp [subLoopClobbers, selectLoopClobbers]))

end VG.Proof.Bignum.Arm
