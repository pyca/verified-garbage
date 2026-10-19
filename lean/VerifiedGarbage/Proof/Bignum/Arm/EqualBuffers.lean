module
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SubState
public import VerifiedGarbage.Impl.Bignum.Arm.EqualBuffers

import VerifiedGarbage.Proof.Bignum.Arm.EqualControls
import VerifiedGarbage.Proof.Bignum.Arm.EqualReverse
import VerifiedGarbage.Proof.Bignum.Arm.SubCompareRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
import VerifiedGarbage.Proof.Framework.Block

/-! # Both unsigned comparisons yield exact equality without secret-dependent branches -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem equalBuffers_ok (s : State) {base : BitVec 32} {size o a b n : Nat}
    (ctx : SubCtx s base size o a b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b) (count : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa equalBuffers s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a n = val32 s.mem (State.addr base) b n then 1 else 0) ∧
      Outside (State.addr base) o (4 * n) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [equalBuffers, WP.seq_iff]
  refine WP.mono (equalHead_ok s) ?_
  rintro u ⟨saved, zero, memU, restU⟩
  have ctxU : SubCtx u base size o a b n :=
    ⟨ctx.nowrap, ctx.outFits, ctx.aFits, ctx.bFits, ctx.sepA, ctx.sepB, by rw [restU.wr]; exact ctx.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (subCompareRow_ok u ctxU hn
    ((restU.gpr .r0 (by simp)).trans hp0) ((restU.gpr .r10 (by simp)).trans hp10)
    ((restU.gpr .r12 (by simp)).trans hp12) ((restU.gpr .lr (by simp)).trans count) zero) ?_
  rintro v ⟨less, inv⟩
  have width : v.gpr .r8 = BitVec.ofNat 32 n :=
    (inv.rest.gpr .r8 (by simp [subLoopClobbers])).trans (saved.trans count)
  rw [memU] at less
  rw [WP.seq_iff]
  refine WP.mono (equalReverse_ok v) ?_
  rintro z ⟨bit, p0, p10, p12, countZ, zeroZ, keep⟩
  rw [width, inv.outPtr, rewind32] at p0
  rw [width, inv.bPtr, rewind32] at p10
  rw [width, inv.aPtr, rewind32] at p12
  rw [width] at countZ
  have ctxZ : SubCtx z base size o b a n :=
    ⟨ctx.nowrap, ctx.outFits, ctx.bFits, ctx.aFits, ctx.sepB, ctx.sepA,
      by rw [keep.wr, inv.rest.wr, restU.wr]; exact ctx.writable⟩
  have aOld : val32 z.mem (State.addr base) a n = val32 s.mem (State.addr base) a n := by
    rw [keep.mem, inv.outside.val32 ctx.sepA.symm (by have := ctx.nowrap; have := ctx.aFits; omega), memU]
  have bOld : val32 z.mem (State.addr base) b n = val32 s.mem (State.addr base) b n := by
    rw [keep.mem, inv.outside.val32 ctx.sepB.symm (by have := ctx.nowrap; have := ctx.bFits; omega), memU]
  rw [WP.seq_iff]
  refine WP.mono (subCompare_ok z ctxZ hn p0 p10 p12 countZ zeroZ) ?_
  rintro t ⟨greater, outsideT, restT⟩
  rw [aOld, bOld] at greater
  have first : t.gpr .r6 = (if val32 s.mem (State.addr base) a n < val32 s.mem (State.addr base) b n then 1 else 0) :=
    (restT.gpr .r6 (by simp [subLoopClobbers])).trans (bit.trans less)
  refine WP.mono (equalFinish_ok t first greater) ?_
  rintro final ⟨result, memFinal, restFinal⟩
  have outsideV := inv.outside
  rw [memU] at outsideV
  rw [keep.mem] at outsideT
  have restZ : Rest [.r0, .r6, .r7, .r10, .r11, .r12, .lr] v z := ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩
  exact ⟨result, by rw [memFinal]; exact outsideV.trans outsideT,
    (restU.mono (by simp [roundClobbers])).trans ((inv.rest.mono (by simp [roundClobbers, subLoopClobbers])).trans
      ((restZ.mono (by simp [roundClobbers])).trans ((restT.mono (by simp [roundClobbers, subLoopClobbers])).trans
        (restFinal.mono (by simp [roundClobbers])))))⟩

end VG.Proof.Bignum.Arm
