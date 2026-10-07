import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacMasked
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointCopy

/-! The secret loop's masked addition, including the copy back to its accumulator. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem add_fields_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hn : K.M.n=4) (hL : Lay K.M size Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hA : RcbApart K.S K.R K.E K.D)
    (hRy : K.R.y=K.R.x+32) (hRz : K.R.z=K.R.x+64)
    (hDy : K.D.y=K.D.x+32) (hDz : K.D.z=K.D.x+64)
    (h2a : K.E.x+96∉rcbW K.S K.D) (h3a : K.E.x+96+32∉rcbW K.S K.D)
    (hSl : ∀ x∈(rcbW K.S K.D++rcbR K.S K.R K.E)++[K.E.x+96,K.E.x+96+32],Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p Sl V E s)
    (hV : ∀ x∈rcbR K.S K.R K.E++[K.E.x+96,K.E.x+96+32],x∈V)
    (h2 : E (K.E.x+96)=E K.E.z*E K.E.z)
    (h3 : E (K.E.x+96+32)=E (K.E.x+96)*E K.E.z) :
    WP isa (Impl.Ecdh.X86_64.Window5.add K) s fun t =>
      ∃ E', ProgKeep K.M base (rcbW K.S K.D++jacCoords K.R) s t ∧
      Inv K.M base size C.p Sl (jacCoords K.R++(jacCoords K.D++V)) E' t ∧
      (E' K.R.x,E' K.R.y,E' K.R.z)=
        jacAddMasked (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have hr : ∀ x∈jacCoords K.R,x∈rcbR K.S K.R K.E := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [rcbR]
  have hd : ∀ x∈jacCoords K.D,x∈rcbW K.S K.D := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [rcbW]
  have hrs : ∀ x∈jacCoords K.R,Sl x :=
    fun x hx => hSl x (List.mem_append_left _ (List.mem_append_right _ (hr x hx)))
  have hap : ∀ x∈jacCoords K.D,∀ y∈jacCoords K.R,x≠y := by
    intro x hx y hy he
    exact hA.apart y (hr y hy) (he ▸ hd x hx)
  rw [Impl.Ecdh.X86_64.Window5.add,←hn]
  apply WP.seq
  refine WP.mono (cachedJacMaskedField_ok hn hL hm hA hDy hDz h2a h3a hSl hI hV h2 h3)
    fun u ⟨ku,iu,hu⟩ => ?_
  refine WP.mono (copyPointTransfer_ok hL iu hRy hRz hrs
    (fun _ hx => List.mem_append_left _ hx) hap) fun t ⟨kt,it⟩ => ?_
  exact ⟨_,(ku.mono (fun _ hx => List.mem_append_left _ hx)).trans
    (kt.mono (fun _ hx => List.mem_append_right _ hx)),it,
    (pointTransferEnv_values _ K.R K.D hRy hRz).trans hu⟩

theorem add_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hn : K.M.n=4) (hL : Lay K.M size Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (hA : RcbApart K.S K.R K.E K.D)
    (hRy : K.R.y=K.R.x+32) (hRz : K.R.z=K.R.x+64)
    (hDy : K.D.y=K.D.x+32) (hDz : K.D.z=K.D.x+64)
    (h2a : K.E.x+96∉rcbW K.S K.D) (h3a : K.E.x+96+32∉rcbW K.S K.D)
    (hSl : ∀ x∈(rcbW K.S K.D++rcbR K.S K.R K.E)++[K.E.x+96,K.E.x+96+32],Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p Sl V E s)
    (hV : ∀ x∈rcbR K.S K.R K.E++[K.E.x+96,K.E.x+96+32],x∈V)
    (h2 : E (K.E.x+96)=E K.E.z*E K.E.z)
    (h3 : E (K.E.x+96+32)=E (K.E.x+96)*E K.E.z)
    {P Q : Point C} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hJP : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P)
    (hJQ : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q)
    (hne : P≠.infinity → Q≠.infinity → P≠Q) :
    WP isa (Impl.Ecdh.X86_64.Window5.add K) s fun t =>
      ∃ E', ProgKeep K.M base (rcbW K.S K.D++jacCoords K.R) s t ∧
      Inv K.M base size C.p Sl (jacCoords K.R++(jacCoords K.D++V)) E' t ∧
      InvJ C (E' K.R.x) (E' K.R.y) (E' K.R.z) (Spec.Weierstrass.add P Q) := by
  refine WP.mono (add_fields_ok hn hL hm hA hRy hRz hDy hDz h2a h3a hSl hI hV h2 h3)
    fun t ⟨E',kt,it,ht⟩ => ?_
  have jt := hJP.add_masked hC ha hP hQ hJQ hne
  dsimp only at jt
  rw [←ht] at jt
  exact ⟨E',kt,it,jt⟩

end VG.Proof.Ecdh.X86_64.Secret
