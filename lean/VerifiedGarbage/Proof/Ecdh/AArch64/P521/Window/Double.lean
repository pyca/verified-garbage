module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Impl.Ecdh.P521.AArch64.Window
public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Impl.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJBuild

/-! # Scheduled doublings retain the existing Jacobian formula -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P521.Window

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Spec.Weierstrass

theorem scheduled_spec {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt} (hAp : RcbApart K.S p p o)
    (hw : (∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ winSlots K) ∧
      (∀ x ∈ rcbW K.S o, x ∈ winOther K) ∧
      ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ winRo K ++ winOther K) {V : List Nat}
    (hV : ∀ x ∈ rcbR K.S p p, x ∈ V) :
    DblSpec K C base size (fprogB K.M (dblJS K.S p o)) p o V := by
  intro E s hI
  rw [show dblJS K.S p o = ofN (dblJSChoiceN false) K.S p p o from dblJSChoice_eq false _ _ _]
  refine WP.mono (winN_ok hL hA hp (dblJSChoiceN_ok false) hAp hw.1 hw.2.1 hw.2.2 hI hV)
    fun t ⟨k,U,E',I,_,v⟩ => ⟨k.mono (fun _ h => List.mem_append_left _ h),U,E',I,?_⟩
  rw [dblJSChoiceN_run false] at v
  rw [dblJChoiceN_run]
  exact v

theorem scheduled_doubles {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : WinLay K size) (hA : WinA K) (hp : UnitMod C.p (2^(64*K.M.n))) :
    DblsOk K C base size (some (fprogB K.M (dblJS K.S K.R K.D),
      fprogB K.M (dblJS K.S K.D K.R))) := by
  intro d hd
  cases Option.some.inj hd
  obtain ⟨hRD,hDR,_⟩ := hL.rcbApart_winJ
  have hRo := pt_other (K := K) (p := K.R) (.inl rfl)
  have hDo := pt_other (K := K) (p := K.D) (.inr (.inr rfl))
  have hR : ∀ x ∈ [K.R.x,K.R.y,K.R.z], x ∈ winRo K ++ winOther K :=
    fun _ h => List.mem_append_right _ (hRo _ h)
  have hD : ∀ x ∈ [K.D.x,K.D.y,K.D.z], x ∈ winRo K ++ winOther K :=
    fun _ h => List.mem_append_right _ (hDo _ h)
  refine ⟨scheduled_spec hL hA hp hRD (winJ_sl hDo hR hR) ?_,
    scheduled_spec hL hA hp hDR (winJ_sl hRo hD hD) ?_⟩
  all_goals
    intro x hx
    simp only [rcbR,dblVR,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> simp only [h,true_or,or_true]

end VG.Proof.Ecdh.AArch64.P521.Window
