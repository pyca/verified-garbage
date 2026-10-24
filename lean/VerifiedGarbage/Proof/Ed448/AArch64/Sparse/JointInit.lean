module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Core
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Const
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint

/-! Initialize a bounded neutral accumulator and the joint public counter. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot)
open VG.Proof.X448.AArch64 (Scr Keeps Outside2 limbs word)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.X448.AArch64.Base (pt limb_lt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem jointInit_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base) :
    WP isa (.block init) s fun t => Core base t ∧ t.gpr .x19=BitVec.ofNat 64 464 ∧
      pt (EV t.mem base) 3 4 5=Spec.Ed448.identity ∧
      Outside2 base 64 2816 ACC 1152 s.mem t.mem ∧
      Keeps (.x19::pointClob) s t := by
  simp only [init,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constE hs hb 3 0) fun a ⟨ab,_,ae,_,ao,ak⟩ => ?_
  have ha:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE ha ab 4 1) fun b ⟨bb,_,be,_,bo,bk⟩ => ?_
  have hb':=ha.of_keeps bk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE hb' bb 5 1) fun c ⟨cb,_,ce,cv,co,ck⟩ => ?_
  have hc:=hb'.of_keeps ck (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE hc cb 19 0) fun d ⟨db,dsm,de,dv,do',dk⟩ => ?_
  have hd:=hc.of_keeps dk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE hd db 20 1) fun e ⟨eb,esm,ee,_,eo,ek⟩ => ?_
  have he:=hd.of_keeps ek (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok e 464 (by decide))
    fun t ⟨t19,tg,tm,tr,tw⟩ => ?_
  have tk:Keeps [.x19] e t:=⟨fun r hr => tg r (by simpa only [List.mem_singleton] using hr),tr,tw⟩
  have et:EV t.mem base=EV e.mem base:=by rw [tm]
  refine ⟨⟨he.of_keeps tk (by decide),?_,?_,?_,?_⟩,t19,?_,?_,?_⟩
  · rw [tm]
    exact eb
  · intro w hw
    rw [tm,esm 19 (by decide) w hw]
    change (word d.mem base (slot (19:Index).val+8*w)).toNat=0
    rw [dv w hw,Window.limb_zero]
    rfl
  · rw [et,ee]
    rfl
  · intro w hw
    change limbs t.mem base (slot (5:Index).val) w<Mb
    rw [tm,esm 5 (by decide) w hw,dsm 5 (by decide) w hw]
    change (word c.mem base (slot (5:Index).val+8*w)).toNat<Mb
    rw [cv w hw]
    exact Nat.lt_of_lt_of_le (limb_lt 1 w) (by decide)
  · rw [et,ee,de,ce,be,ae]
    rfl
  · intro x hx _
    rw [tm,eo x (by simp only [slot] at hx ⊢;omega),do' x (by simp only [slot] at hx ⊢;omega),
      co x (by simp only [slot] at hx ⊢;omega),bo x (by simp only [slot] at hx ⊢;omega),
      ao x (by simp only [slot] at hx ⊢;omega)]
  · have k1:Keeps (.x19::pointClob) s c:=((ak.mono (by decide)).trans (bk.mono (by decide))).trans
      (ck.mono (by decide))
    have k2:Keeps (.x19::pointClob) c t:=((dk.mono (by decide)).trans (ek.mono (by decide))).trans
      (tk.mono (by decide))
    exact k1.trans k2

end VG.Proof.Ed448.AArch64.Sparse
