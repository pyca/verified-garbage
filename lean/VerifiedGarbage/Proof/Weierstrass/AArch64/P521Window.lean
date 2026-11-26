module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad

/-! # P-521's doubling in a window's loop -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.P521

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Spec.Weierstrass

/-- The window's memory, as a program on its slots changes it. -/
theorem unch_of_keep {K : WinCfg} {base : Addr} {W : List Nat} {s t : State} (h : ProgKeep K.M base W s t)
    (hW : ∀ x ∈ W, x ∈ winOther K) : Unch base (loopW K) s.mem t.mem :=
  h.unch.mono fun w hw => by
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, hW y hy, rfl⟩
    · exact Or.inr rfl

theorem double_spec {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hsp : Impl.Weierstrass.AArch64.P521.supported K.M = true) (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt} (hAp : RcbApart K.S p p o)
    (hw : (∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ winSlots K) ∧
      (∀ x ∈ rcbW K.S o, x ∈ winOther K) ∧
      ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ winRo K ++ winOther K) {V : List Nat}
    (hV : ∀ x ∈ rcbR K.S p p, x ∈ V) :
    DblSpec K C base size (Impl.Weierstrass.AArch64.P521.double K.M K.S p o) p o V := by
  intro E s hI
  have hN := doubleN_ok
  rw [Impl.Weierstrass.AArch64.P521.double]
  refine WP.mono (program_ok hsp hL.lay hA.al hp _ hI (doubleSteps_ok K.S p o)
    (by rw [double_eq]; exact fun op hop x hx => hw.1 x (ofN_slots op hop x hx))
    (by rw [double_eq]; exact readsOk_mono (ofN_readsOk hN K.S p p o) hV)) fun t ⟨k, I⟩ => ?_
  rw [double_eq] at k I
  refine ⟨⟨fun r hr => k.gpr r fun h => hr (List.mem_append_left _ h), k.rd, k.wr, k.sp⟩,
    unch_of_keep (k.mono fun w hw' => ?_) hw.2.1, _, I.sub fun x hx => ?_, ?_⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw'
    exact ofN_out hN op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx
  · rw [dblJChoiceN_run]
    refine Eq.trans ?_ (doubleN_run fun y => E (rcbσ K.S p p o y))
    exact congr (congrArg Prod.mk (ofN_run hN hAp E 6))
      (congr (congrArg Prod.mk (ofN_run hN hAp E 7)) (ofN_run hN hAp E 8))

theorem doubles_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hsp : Impl.Weierstrass.AArch64.P521.supported K.M = true)
    (hL : WinLay K size) (hA : WinA K) (hp : UnitMod C.p (2^(64*K.M.n))) :
    DblsOk K C base size (some (Impl.Weierstrass.AArch64.P521.double K.M K.S K.R K.D,
      Impl.Weierstrass.AArch64.P521.double K.M K.S K.D K.R)) := by
  intro d hd
  cases Option.some.inj hd
  obtain ⟨hRD,hDR,_⟩ := hL.rcbApart_winJ
  have hRo := pt_other (K := K) (p := K.R) (.inl rfl)
  have hDo := pt_other (K := K) (p := K.D) (.inr (.inr rfl))
  have hR : ∀ x ∈ [K.R.x,K.R.y,K.R.z], x ∈ winRo K ++ winOther K :=
    fun _ h => List.mem_append_right _ (hRo _ h)
  have hD : ∀ x ∈ [K.D.x,K.D.y,K.D.z], x ∈ winRo K ++ winOther K :=
    fun _ h => List.mem_append_right _ (hDo _ h)
  refine ⟨double_spec hsp hL hA hp hRD (winJ_sl hDo hR hR) ?_,
    double_spec hsp hL hA hp hDR (winJ_sl hRo hD hD) ?_⟩
  all_goals
    intro x hx
    simp only [rcbR,dblVR,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> simp only [h,true_or,or_true]

end VG.Proof.Weierstrass.AArch64.P521
