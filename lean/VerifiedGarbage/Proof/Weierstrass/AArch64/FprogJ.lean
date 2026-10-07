import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Weierstrass.JacMadd

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

/-- A field compiler's exact values, bounds and memory frame at a fixed scratch size. -/
def FieldCompilerCorrect (arithmetic : Mod → List FOp → Prog isa) (size : Nat) : Prop :=
  ∀ (M : Mod) (base : Addr) (m : Nat) [NeZero m] (Sl : Nat → Prop),
    Lay M size Sl → Aligned M Sl → UnitMod m (2^(64*M.n)) →
    ∀ (ops : List FOp) (V : List Nat) (E : Nat → Fin m) (s : State),
    Inv M base size m Sl V E s →
    (∀ op∈ops,∀ x∈op.out::op.ins,Sl x) → readsOk ops V=true →
    WP isa (arithmetic M ops) s fun t => ProgKeep M base (ops.map FOp.out) s t ∧
      Inv M base size m Sl (validAfter ops V) (runOps ops E) t

theorem fprogB_correct (size : Nat) : FieldCompilerCorrect fprogB size := by
  intro M base m _ Sl hL hAl hm ops V E s hi hS hV
  exact (fprogB_wp _ _).mpr (fprog_ok hL hAl hm ops hi hS hV)

theorem FieldCompilerCorrect.ofN {arithmetic : Mod → List FOp → Prog isa} {size : Nat}
    (hc : FieldCompilerCorrect arithmetic size) {M : Mod} {base : Addr} {m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl) (hm : UnitMod m (2^(64*M.n)))
    {N : List FOp} (hN : NumOk N) {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x∈rcbW S o++rcbR S p q,Sl x) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x∈rcbR S p q,x∈V) :
    WP isa (arithmetic M (ofN N S p q o)) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl ([o.x,o.y,o.z]++V) (runOps (ofN N S p q o) E) t ∧
      (runOps (ofN N S p q o) E o.x,runOps (ofN N S p q o) E o.y,runOps (ofN N S p q o) E o.z)=
        (runOps N (fun y => E (rcbσ S p q o y)) 6,runOps N (fun y => E (rcbσ S p q o y)) 7,
          runOps N (fun y => E (rcbσ S p q o y)) 8) := by
  refine WP.mono (hc M base m Sl hL hAl hm _ V E s hI
    (fun op hop x hx => hSl x (ofN_slots op hop x hx))
    (readsOk_mono (ofN_readsOk hN S p q o) hV)) fun t ⟨hk,hi⟩ => ⟨hk.mono ?_,hi.sub ?_,?_⟩
  · intro w hw
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hw
    exact ofN_out hN op hop
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx
  · exact congrArg₂ Prod.mk (ofN_run hN hA E 6)
      (congrArg₂ Prod.mk (ofN_run hN hA E 7) (ofN_run hN hA E 8))

/-- The partial mixed formula has an exact field result even on exceptional inputs. -/
theorem FieldCompilerCorrect.maddJ_values_ok {arithmetic : Mod → List FOp → Prog isa}
    {size : Nat} (hc : FieldCompilerCorrect arithmetic size) {M : Mod} {base : Addr} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod C.p (2^(64*M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x∈rcbW S o++rcbR S p q,Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x∈rcbR S p q,x∈V) :
    WP isa (arithmetic M (maddJ S p q o)) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (maddJ S p q o) E) t ∧
      (runOps (maddJ S p q o) E o.x,runOps (maddJ S p q o) E o.y,
        runOps (maddJ S p q o) E o.z)=maddJF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) := by
  rw [maddJ_eq]
  exact WP.mono (hc.ofN hL hAl hm maddJN_ok hA hSl hI hV)
    fun _ ⟨hk,hi,hv⟩ => ⟨hk,hi,hv.trans (maddJN_run _)⟩

theorem maddJ_values_ok {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod C.p (2^(64*M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x∈rcbW S o++rcbR S p q,Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x∈rcbR S p q,x∈V) :
    WP isa (fprogB M (maddJ S p q o)) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (maddJ S p q o) E) t ∧
      (runOps (maddJ S p q o) E o.x,runOps (maddJ S p q o) E o.y,
        runOps (maddJ S p q o) E o.z)=maddJF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) := by
  apply (fprogB_wp _ _).mpr
  rw [maddJ_eq]
  exact WP.mono (ofN_ok hL hAl hm maddJN_ok hA hSl hI hV)
    fun _ ⟨hk,hi,hv⟩ => ⟨hk,hi,hv.trans (maddJN_run _)⟩

/-- Mixed Jacobian addition, when both finite inputs are distinct. -/
theorem maddJ_ok {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x∈rcbW S o++rcbR S p q,Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x∈rcbR S p q,x∈V) {P : Point C}
    (hP : onCurve C P=true) (hQ : onCurve C (.affine (E q.x) (E q.y))=true)
    (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) (hZ : E p.z≠0)
    (hne : P≠.affine (E q.x) (E q.y)) :
    WP isa (fprogB M (maddJ S p q o)) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (maddJ S p q o) E) t ∧
      InvJ C (runOps (maddJ S p q o) E o.x) (runOps (maddJ S p q o) E o.y)
        (runOps (maddJ S p q o) E o.z) (Spec.Weierstrass.add P (.affine (E q.x) (E q.y))) := by
  refine WP.mono (maddJ_values_ok hL hAl hm hA hSl hI hV) fun _ ⟨hk,hi,hv⟩ => ⟨hk,hi,?_⟩
  have h := InvJ.madd hC ha hP hQ hJ hZ hne
  rw [←hv] at h
  exact h

end VG.Proof.Weierstrass.AArch64
