import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFive
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
local macro "jmem" : tactic => `(tactic| simp only [jacCoords,nafLive,jacWinSlots,jacWinWrites,
  winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

theorem nafAdd_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod m (2^(64*K.M.n))) (hOne : K.one<m)
    (hc : JacAddChecks K K.R K.E K.D) (hcopy : FieldCT (.block (copyPt K.M.n K.R K.D)))
    {E : Nat → Fin m} :
    RelCT isa (FieldPair K.M base size m (·∈jacWinSlots K) (jacCoords K.E++nafLive K) E)
      (.seq (Jacobian.jacAdd K K.R K.E K.D) (.block (copyPt 4 K.R K.D)))
      (fun s t => ∃ E', FieldPair K.M base size m (·∈jacWinSlots K) (nafLive K) E' s t) := by
  have old := hL.toWinLay hJ
  have sl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ jacWinSlots K := by
    intro x hx
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with h | h
    all_goals simp_all only [jacWinSlots,winRo,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    all_goals grind
  have vr : ∀ x ∈ rcbR K.S K.R K.E, x ∈ jacCoords K.E++nafLive K := by
    intro x hx
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jmem
  apply RelCT.seq (jacAdd_relCT hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm (old.rcbApart_D (Or.inr rfl)) sl vr hOne hc)
  apply RelCT.exists_
  intro E'
  rw [←hL.n]
  exact (copyPoint_relCT (E:=E') hL.lay hAl (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jmem) (by
    intro x hx
    exact List.mem_append_left _ hx) hcopy).mono
    (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hx)))⟩)

theorem nafDouble_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod m (2^(64*K.M.n)))
    (hd : FieldCT (Naf.double K K.R K.D)) (hcopy : FieldCT (.block (copyPt K.M.n K.R K.D)))
    {E : Nat → Fin m} :
    RelCT isa (FieldPair K.M base size m (·∈jacWinSlots K) (nafLive K) E)
      (.seq (Naf.double K K.R K.D) (.block (copyPt 4 K.R K.D)))
      (fun s t => ∃ E',FieldPair K.M base size m (·∈jacWinSlots K) (nafLive K) E' s t) := by
  have old := hL.toWinLay hJ
  have hs : ∀ x∈rcbW K.S K.D++rcbR K.S K.R K.R,x∈jacWinSlots K := by
    intro x hx; apply hL.old_slots x
    simp only [rcbW,rcbR,winSlots,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hv : ∀ x∈rcbR K.S K.R K.R,x∈nafLive K := by
    intro x hx
    simp only [rcbR,nafLive,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  apply RelCT.seq (Forward.field_relCT Forward.Production.cases hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm (old.rcbApart_D (Or.inl rfl)) hs hv hd)
  rw [←hL.n]
  exact (copyPoint_relCT hL.lay hAl (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jmem) (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jmem) hcopy).mono
    (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_append_right _ hx)⟩)

end VG.Proof.Weierstrass.AArch64
