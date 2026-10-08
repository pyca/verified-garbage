import VerifiedGarbage.Proof.Weierstrass.X86.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafSum

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

local macro "jmem" : tactic => `(tactic| simp only [nafLive,nafTableLive,jacCoords,nafSlots,nafWrites,
  winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

theorem nafAdd_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat} {E : Nat → Fe C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    (ha : JacAddChecks K F K.R K.E K.D) (hcp : ScratchCT (.block (copyPt K.M.n K.R K.D))) :
    RelCT isa (FieldPair K.M base size C.p (·∈nafSlots K) (jacCoords K.E++nafLive K) E counter)
      (.seq (Jacobian.jacAdd K F K.R K.E K.D) (.block (copyPt 4 K.R K.D)))
      (fun s t => ∃ E',FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E' counter s t) := by
  have sl : ∀ x∈rcbW K.S K.D++rcbR K.S K.R K.E,x∈nafSlots K := by
    intro x hx
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    jmem
    grind
  have vr : ∀ x∈rcbR K.S K.R K.E,x∈jacCoords K.E++nafLive K := by
    intro x hx
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> jmem
  apply RelCT.seq (jacAdd_relCT hL.lay hW hm ha ((hL.toWinLay hJ).rcbApart_D (Or.inr rfl)) sl vr hOne)
  apply RelCT.exists_
  intro E'
  rw [←hL.n]
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> jmem
  exact (copyPoint_relCT (E:=E') hL.lay hW rs (fun _ hx => List.mem_append_left _ hx) hcp).mono
    (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ hx)))⟩)

theorem nafDouble_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat} {E : Nat → Fe C}
    (hL : NafLay K size) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n)))
    (hd : ScratchCT (fprog F (dblJMul K.S K.R K.D)))
    (hcp : ScratchCT (.block (copyPt K.M.n K.R K.D))) :
    RelCT isa (FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E counter)
      (.seq (fprog F (dblJMul K.S K.R K.D)) (.block (copyPt 4 K.R K.D)))
      (fun s t => ∃ E',FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E' counter s t) := by
  have sl : ∀ x∈rcbW K.S K.D++rcbR K.S K.R K.R,x∈nafSlots K := by
    intro x hx
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    jmem
    grind
  have vr : ∀ x∈rcbR K.S K.R K.R,x∈nafLive K := by
    intro x hx
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> jmem
  apply RelCT.seq (doubleFieldPlain_relCT hL.lay hW hm sl vr hd)
  rw [←hL.n]
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> jmem
  exact (copyPoint_relCT hL.lay hW rs (fun _ hx => List.mem_append_left _ hx) hcp).mono
    (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_append_right _
      (List.mem_append_right _ hx))⟩)

end VG.Proof.Weierstrass.X86
