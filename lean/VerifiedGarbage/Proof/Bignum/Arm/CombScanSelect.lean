module

public import VerifiedGarbage.Proof.Bignum.Arm.CombTableState
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.Select
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Bignum.Arm.WindowSelect
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.SelectReadState
import VerifiedGarbage.Proof.Bignum.Arm.SelectReadBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Block
/-! The ordinary RSA selector reads one dense, external comb row. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SelectReadRow.lean`, which only this module imported.
section

/-! A masked row reuses the RSA selector with an external read-only source. -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem selectReadRow_ok (s : State) {dst src : BitVec 32} {n : Nat}
    (ctx : SelectReadCtx s dst src n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = dst) (hp10 : s.gpr .r10 = dst) (hp12 : s.gpr .r12 = src)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) (hc : (s.gpr .r11).toNat ≤ 1) :
    WP isa selectRow s (SelectReadInv s dst src n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ SelectReadInv s dst src n i t
  rw [selectRow, WP.seq_iff]
  refine WP.mono (selectMask_ok s) ?_
  rintro u ⟨mask, keep⟩
  refine WP.loop (M := isa) inv ?_ n u ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (selectReadBody_ok ctx hi (by omega) hc) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (show Rest [.r4] s u from ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩).mono (by simp [selectLoopClobbers])⟩
    · simpa using
        (keep.regs .r0 (by simp)).trans hp0
    · simpa using
        (keep.regs .r10 (by simp)).trans hp10
    · simpa using
        (keep.regs .r12 (by simp)).trans hp12
    · simpa only [Nat.sub_zero] using (keep.regs .lr (by simp)).trans hcount
    · rw [keep.mem]; exact Outside.refl _ _ _ _
    · rw [keep.mem]; exact Frame.refl _ _
    · simp only [val32, ite_self]
    · rw [keep.regs .r11 (by simp)]; exact mask

end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombScan
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem val32_rebase (m : Mem) (base : Addr) (a b k : Nat) :
    val32 m (off base a) b k=val32 m base (a+b) k := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    simp only [val32,w32,Offset.add_add,ih,Nat.add_assoc]

theorem frame_outside {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Frame [⟨off base o,n⟩] m m') (hn : o+n<2^64) : Outside base o n m m' := by
  intro x hx
  refine h x fun r hr hc => ?_
  rw [List.mem_singleton.mp hr] at hc
  change (x-off base o).toNat+1≤n at hc
  simp only [off] at hc
  have hi := (Offset.lt_iff x base (d:=o) (n:=n) (by omega)).mp (by omega)
  change (x-base).toNat<o ∨ o+n≤(x-base).toNat at hx
  omega

theorem select_ok (s : State) {s0 : State} {base table : BitVec 32} {len w M g N j : Nat}
    (h : ArithmeticReady base len w s0) (tableReady : CombTable table w M g N s0)
    (separate : Region.Disjoint ⟨State.addr table,32*(8*w)⟩ ⟨State.addr base,8*len⟩)
    (mem : s.mem=s0.mem) (rest : Rest roundClobbers s0 s) (hj : j<32)
    (p0 : s.gpr .r0=base+BitVec.ofNat 32 (arrAt w 1))
    (p10 : s.gpr .r10=base+BitVec.ofNat 32 (arrAt w 1))
    (p12 : s.gpr .r12=table+BitVec.ofNat 32 (8*w*j))
    (count : s.gpr .lr=BitVec.ofNat 32 (2*w)) (bit : (s.gpr .r11).toNat≤1) :
    WP isa (.seq selectRow (.block [.ldrSp .r0 0])) s fun t =>
      ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 1=(if (s.gpr .r11).toNat=0 then
        numAt s0.mem (State.addr base) w 1 else
        Spec.Rsa.powMod g (Spec.Rsa.FixedBaseComb.exponent N j) M*2^(64*w)%M) ∧
      Outside (State.addr base) (arrAt w 1) (8*w) s0.mem t.mem ∧
      Keeps (State.addr base) len w 1 s0.mem t.mem ∧
      Frame [⟨State.addr base,8*len⟩] s0.mem t.mem ∧ Rest roundClobbers s0 t := by
  have fits : arrAt w 8≤8*len := h.width ▸ h.layout.2.2.1
  have arrayFits : arrAt w 1+8*w≤8*len := by have := array_end_le (w:=w) (show 1<8 by decide); omega
  have entryFits : 8*w*j+8*w≤32*(8*w) := by
    have bound := Nat.mul_le_mul_left (8*w) (show j+1≤32 by omega)
    simpa only [Nat.mul_add,Nat.mul_one,Nat.mul_comm (8*w) 32] using bound
  let dst := base+BitVec.ofNat 32 (arrAt w 1)
  let src := table+BitVec.ofNat 32 (8*w*j)
  have dstAddr : State.addr dst=off (State.addr base) (arrAt w 1) := addr_add (by have := h.workspace.nowrap; have := tableReady.positive; omega)
  have srcAddr : State.addr src=off (State.addr table) (8*w*j) := addr_add (by have := tableReady.fits; have := tableReady.positive; omega)
  have dstVal : dst.toNat=base.toNat+arrAt w 1 := by
    simp only [dst,BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := h.workspace.nowrap; have := tableReady.positive; omega),
      Nat.mod_eq_of_lt (by have := h.workspace.nowrap; have := tableReady.positive; omega)]
  have srcVal : src.toNat=table.toNat+8*w*j := by
    simp only [src,BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := tableReady.fits; have := tableReady.positive; omega),
      Nat.mod_eq_of_lt (by have := tableReady.fits; have := tableReady.positive; omega)]
  have ctx : SelectReadCtx s dst src (2*w) := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [dstVal]; have := h.workspace.nowrap; omega
    · rw [srcVal]; have := tableReady.fits; omega
    · have := h.workspace.nowrap; have := tableReady.fits; omega
    · rw [dstAddr,rest.wr]
      exact ⟨_,h.workspace.writable,Offset.contains_base _ (by omega) (by have := h.workspace.nowrap; omega)⟩
    · rw [srcAddr,rest.rd,rest.wr]
      exact VG.CallLay.inRegions_sub tableReady.readable (by omega) (by have := tableReady.fits; omega)
    · rw [srcAddr,dstAddr]
      exact (separate.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega : arrAt w 1+4*(2*w)≤8*len))
  rw [WP.seq_iff]
  refine WP.mono (selectReadRow_ok s ctx (by have := tableReady.positive; omega) p0 p10 p12 count bit) ?_
  intro v inv
  have value := inv.value
  simp only [dstAddr,srcAddr,val32_rebase,Nat.add_zero,mem] at value
  rw [←numAt_native,←numAt_native,tableReady.values j hj] at value
  have narrow : Frame [⟨off (State.addr base) (arrAt w 1),8*w⟩] s0.mem v.mem := by
    simpa only [dstAddr,show 4*(2*w)=8*w by omega,mem] using inv.frame
  have outside := frame_outside narrow (by have := h.workspace.nowrap; omega)
  have frame := outside_workspace outside arrayFits
  have keeps := outside_array_keeps outside (by have := h.workspace.nowrap; omega : 8*len<2^64)
  have restV : Rest roundClobbers s0 v := rest.trans (inv.rest.mono (by decide))
  refine WP.mono (restoreBase_ok v (by rw [restV.rd,restV.wr,restV.sp]; exact h.stackRead)
    (saved_base_kept frame h.stackSep h.saved restV.sp)) ?_
  rintro t ⟨ptrT,memT,restT⟩
  rw [←memT] at value outside frame keeps
  have allRest := restV.trans (restT.mono (by decide))
  exact ⟨(h.after_array (by decide) keeps frame allRest ptrT).1,value,outside,keeps,frame,allRest⟩

end VG.Proof.Bignum.Arm.CombScan
