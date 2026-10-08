import VerifiedGarbage.Proof.Weierstrass.X86.WinJacEntryState
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacAdd

/-! Separate the accumulator, selected point, and addition output. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem rcb_D_work (K : JacWinCfg) : ∀ x∈rcbW K.S K.D,x∈work K := by
  intro x hx
  simp only [rcbW,work,temps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem add_apart {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    RcbApart K.S K.R K.E K.D ∧ K.z2∉rcbW K.S K.D ∧ K.z3∉rcbW K.S K.D := by
  have nd := hL.nd
  have ar := hL.readonly K.S.a (by simp [ro])
  have br := hL.readonly K.S.b3 (by simp [ro])
  simp only [work,temps,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at nd ar br
  refine ⟨⟨?_,?_⟩,?_,?_⟩ <;>
    simp only [rcbW,rcbR,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
      List.nodup_nil,and_true,forall_eq_or_imp,forall_eq] <;> grind

theorem point_nd {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk)
    {p : Pt} (hp : p=K.R ∨ p=K.D ∨ p=K.E) : (jacCoords p).Nodup := by
  rcases hp with rfl|rfl|rfl
  all_goals
    apply List.Nodup.sublist (l₂:=work K) _ hL.nd
    simp only [jacCoords,work,temps,List.cons_append,List.nil_append]
    repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons

theorem points_apart {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    (∀ x∈jacCoords K.D,∀ y∈jacCoords K.E,x≠y) ∧
    (∀ x∈jacCoords K.R,∀ y∈jacCoords K.D,x≠y) := by
  have hn := hL.nd
  simp only [work,temps,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hn
  constructor <;> simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] <;> grind

end VG.Proof.Weierstrass.X86.JWin
