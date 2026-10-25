module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.OddLoop
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.RestoreEntry
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Cross
import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Framework.Block

/-! Retain 2P as the addend and restore P as the odd table accumulator. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.Ed448.AArch64 (TAB)
open VG.Impl.Ed448.AArch64.Sparse
open VG.Proof.X448.AArch64 (Scr Keeps Outside Outside2 limbs word off)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.X448.AArch64.Base (pt)
open VG.Proof.Ed448.AArch64.Window (TPt TBnd tw)
open VG.Spec.Ed448 (Point)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem tableStepSetup_ok {s:State} {base:Addr} {P:Point} (hs:Scr s base) (hb:BEnv s.mem base)
    (hz:∀ w<8,limbs s.mem base (slot (19:Index).val) w=0)
    (hp:pt (EV s.mem base) 3 4 5=VG.Proof.Ed448.double P)
    (ht:TPt s.mem base 0=P ∧ TBnd s.mem base 0)
    (hxb:∀ w<8,(tw s.mem base 0 w).toNat<Mb) :
    WP isa (.block tableStepSetup) s fun t =>
      OddInv t base P 1 t ∧ EV t.mem base 20=EV s.mem base 20 ∧
      Outside2 base 64 2816 ACC 1152 s.mem t.mem ∧
      Keeps (.x19::VG.Proof.X448.AArch64.Fast.fclob) s t := by
  have he:tableStepSetup=VG.Impl.Ed448.AArch64.Point56.copy3 6 3++
      (restoreWords 24 TAB++[.movz .x .x19 1 0]):=by rfl
  rw [he,WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.Window.copy3_ok hs 6 3 (by decide) (by decide) (by decide))
    fun a ⟨av,akeep,ao,ak⟩ => ?_
  have ha:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (restoreWords_ok ha ha.x3 (Nat.le_refl 24) (by decide) (by decide)
    (fun w hw => ha.read (by simp only [TAB];omega_arith))
    (fun w hw j hj => by
      rw [VG.Proof.X448.AArch64.ofs_off base (by simp only [TAB];omega_arith)]
      simp only [TAB]
      omega_arith)) fun b ⟨bv,bo,bk⟩ => ?_
  change Outside base 448 384 a.mem b.mem at bo
  have hb':Scr b base:=ha.of_keeps bk (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok b 1 (by decide))
    fun t ⟨t19,tg,tm,tr,twr⟩ => ?_
  have tk:Keeps [.x19] b t:=⟨fun r hr => tg r (by simpa only [List.mem_singleton] using hr),tr,twr⟩
  have hst:=hb'.of_keeps tk (by decide)
  have src:∀ w<24,tw a.mem base 0 w=tw s.mem base 0 w:=by
    intro w hw
    exact ao.word (Or.inr (by simp only [slot,TAB];omega_arith)) (by simp only [TAB];omega_arith)
  have dstWord:∀ w<24,word t.mem base (restoreDst w)=tw s.mem base 0 w:=by
    intro w hw
    rw [tm,bv w hw]
    exact src w hw
  have fieldKeep:∀ (i:Index), (i.val < 3 ∨ 6 ≤ i.val) → ∀ j<8,
      limbs t.mem base (slot i.val) j=limbs a.mem base (slot i.val) j:=by
    intro i hi j hj
    have := i.isLt
    rw [tm]
    exact bo.limbs (by simp only [slot];omega_arith) (by simp only [slot];omega_arith) (by omega_arith)
  have ab:BEnv a.mem base:=by
    intro i j hj
    by_cases hi:i.val < 6 ∨ 9 ≤ i.val
    · rw [akeep i hi j hj]
      exact hb i j hj
    · have hr:slot i.val=slot (6+(i.val-6)):=by congr 1;omega_arith
      rw [hr,av _ (by omega_arith) j hj]
      exact hb ⟨3+(i.val-6),by omega_arith⟩ j hj
  have tb:BEnv t.mem base:=by
    intro i j hj
    by_cases hi:i.val < 3 ∨ 6 ≤ i.val
    · rw [fieldKeep i hi j hj]
      exact ab i j hj
    · have hr:restoreDst (8*(i.val-3)+j)=slot i.val+8*j:=by
        simp only [restoreDst,slot]
        omega_arith
      show (word t.mem base (slot i.val+8*j)).toNat<_
      rw [←hr,dstWord _ (by omega_arith)]
      exact ht.2 _ (by omega_arith)
  have cw:∀ c<3,∀ j<8,tw s.mem base 0 (8*c+j)=word t.mem base (slot (3+c)+8*j):=by
    intro c hc j hj
    rw [←dstWord _ (by omega_arith)]
    congr 1
    simp only [restoreDst,slot]
    omega_arith
  have envPt:pt (EV t.mem base) 3 4 5=P:=by
    rw [←ht.1]
    symm
    unfold TPt pt
    refine Point.mk.injEq _ _ _ _ _ _ |>.mpr ⟨?_,?_,?_⟩
    · exact Window.FV_entry _ _ _ (e:=0) (c:=0) (by omega_arith) (cw 0 (by decide))
    · exact Window.FV_entry _ _ _ (e:=0) (c:=1) (by omega_arith) (cw 1 (by decide))
    · exact Window.FV_entry _ _ _ (e:=0) (c:=2) (by omega_arith) (cw 2 (by decide))
  have cp:∀ c<3,∀ j<8,limbs t.mem base (slot (6+c)) j=limbs s.mem base (slot (3+c)) j:=by
    intro c hc j hj
    rw [fieldKeep ⟨6+c,by omega_arith⟩ (by change 6+c < 3 ∨ 6 ≤ 6+c;omega_arith) j hj]
    exact av c hc j hj
  have envPnt:pt (EV t.mem base) 6 7 8=VG.Proof.Ed448.double P:=by
    rw [←hp]
    unfold pt
    refine Point.mk.injEq _ _ _ _ _ _ |>.mpr ⟨?_,?_,?_⟩
    · exact Window.FV_of_limbs (cp 0 (by decide))
    · exact Window.FV_of_limbs (cp 1 (by decide))
    · exact Window.FV_of_limbs (cp 2 (by decide))
  have tz:∀ w<8,limbs t.mem base (slot (19:Index).val) w=0:=by
    intro w hw
    rw [fieldKeep _ (by decide) w hw,akeep _ (by decide) w hw]
    exact hz w hw
  have hOne:EV t.mem base 20=EV s.mem base 20:=by
    apply Window.FV_of_limbs
    intro j hj
    rw [fieldKeep _ (by decide) j hj,akeep _ (by decide) j hj]
  have ot:Outside2 base 64 2816 ACC 1152 s.mem t.mem:=by
    intro x hx _
    rw [tm,bo x (by omega_arith),ao x (by simp only [slot];omega_arith)]
  refine ⟨⟨⟨by decide,by decide⟩,hst,tb,tz,t19,?_,envPnt,rfl,?_,?_,rfl,rfl,rfl,fun _ _ _ _ => rfl⟩,
    hOne,ot,?_⟩
  · exact envPt
  · intro e he
    have he:e=0:=by omega_arith
    subst e
    refine ⟨?_,?_⟩
    · rw [Window.TPt_of_tw (fun w hw => by
        exact ot.word (Or.inr (by simp only [TAB];omega_arith)) (Or.inr (by simp only [ACC,TAB];omega_arith))
          (by simp only [TAB];omega_arith)),ht.1]
      rfl
    · intro w hw
      rw [tw,ot.word (Or.inr (by simp only [TAB];omega_arith)) (Or.inr (by simp only [ACC,TAB];omega_arith))
        (by simp only [TAB];omega_arith)]
      exact ht.2 w hw
  · intro e he w hw
    have he:e=0:=by omega_arith
    subst e
    have hm:tw t.mem base 0 w=tw s.mem base 0 w:=
      ot.word (Or.inr (by simp only [TAB];omega_arith)) (Or.inr (by simp only [ACC,TAB];omega_arith))
        (by simp only [TAB];omega_arith)
    rw [hm]
    exact hxb w hw
  · exact ((ak.mono (by decide)).trans (bk.mono (by decide))).trans (tk.mono (by decide))

end VG.Proof.Ed448.AArch64.Sparse
