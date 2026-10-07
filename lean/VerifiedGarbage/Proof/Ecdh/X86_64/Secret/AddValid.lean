import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Add
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.LayoutOps

/-! Masked addition executes for every scalar; point correctness needs the scalar's noncollision bound. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem SecretLay.cache_apart_rcb {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    K.E.x+96∉rcbW K.S K.D ∧ K.E.x+128∉rcbW K.S K.D := by
  have hh := hL.nodup
  simp only [localWrites,winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_cons,List.not_mem_nil,or_false,not_or] at hh ⊢
  grind

theorem add_valid_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : SecretLay K size) (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈rcbR K.S K.R K.E++[K.E.x+96,K.E.x+128],x∈V)
    (h2 : E (K.E.x+96)=E K.E.z*E K.E.z)
    (h3 : E (K.E.x+128)=E (K.E.x+96)*E K.E.z)
    {valid : Prop} {P Q : Point C}
    (hP : valid → onCurve C P=true) (hQ : valid → onCurve C Q=true)
    (hJP : valid → InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P)
    (hJQ : valid → InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q)
    (hne : valid → P≠.infinity → Q≠.infinity → P≠Q) :
    WP isa (Impl.Ecdh.X86_64.Window5.add K) s fun t =>
      ∃ F,ProgKeep K.M base (localWrites K) s t ∧
      Inv K.M base size C.p (·∈slots K) V F t ∧
      (valid → InvJ C (F K.R.x) (F K.R.y) (F K.R.z) (Spec.Weierstrass.add P Q)) := by
  have h3a : K.E.x+96+32=K.E.x+128 := by omega
  have hsl : ∀ x∈(rcbW K.S K.D++rcbR K.S K.R K.E)++[K.E.x+96,K.E.x+96+32],x∈slots K := by
    intro x hx
    rw [h3a] at hx
    rcases List.mem_append.mp hx with hx|hx
    · rcases List.mem_append.mp hx with hx|hx
      · exact local_slots K x (rcb_local K x hx)
      · exact hI.sl x (hV x (List.mem_append_left _ hx))
    · exact hI.sl x (hV x (List.mem_append_right _ hx))
  refine WP.mono (add_fields_ok hL.n hL.lay hm (hL.toWinLay.rcbApart_D (Or.inr rfl))
    hL.rxy hL.rxz hL.dxy hL.dxz hL.cache_apart_rcb.1
    (by rw [h3a]; exact hL.cache_apart_rcb.2) hsl hI
    (by rw [h3a]; exact hV) h2 (by rw [h3a]; exact h3)) fun t ⟨F,kt,it,vt⟩ => ?_
  refine ⟨F,kt.mono ?_,it.sub (fun _ hx => List.mem_append_right _ (List.mem_append_right _ hx)),?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact rcb_local K x hx
    · exact r_local K x hx
  · intro hv
    have jp := (hJP hv).add_masked hC ha (hP hv) (hQ hv) (hJQ hv) (hne hv)
    dsimp only at jp
    rw [←vt] at jp
    exact jp

end VG.Proof.Ecdh.X86_64.Secret
