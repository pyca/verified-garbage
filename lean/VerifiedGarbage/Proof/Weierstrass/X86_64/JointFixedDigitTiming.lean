import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming

/-! Timing of a complete fixed-generator digit, including its public zero case. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| (simp only [jointSlots,jointLive,jointWork,
  nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
  List.not_mem_nil,or_false] at * <;> grind))

structure JointFixedChecks (c : Joint.Cfg) : Prop where
  read : RegCT [.rdi,.rbx] (.block (Naf.digitRead {c.K with bits:=c.gBits}))
  entry : FixedEntryCT c.K c.tsym
  add : JacMixedChecks c.K c.K.R c.K.E c.K.D
  copy : ScratchCT (.block (copyPt 4 c.K.R c.K.D))

theorem jointFixedSum_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (hc : JointFixedChecks c) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c) (jacCoords c.K.E++jointLive c) E)
      (.seq (Jacobian.jacMixedForward c.K c.K.R c.K.E c.K.D) (.block (copyPt 4 c.K.R c.K.D)))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E,x∈jointSlots c := by intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E,x∈jacCoords c.K.E++jointLive c := by intro x hx; jslots
  apply RelCT.seq (jacMixedForward_relCT hL.lookup.layout.n hL.lookup.layout.lay hm hc.add hL.addApart sl vr hOne)
  apply RelCT.exists_
  intro E'
  have cp := copyPoint_relCT (base:=base) (E:=E') hL.lookup.layout.lay
    (o:=c.K.R) (q:=c.K.D) (by intro x hx; jslots)
    (V:=jacCoords c.K.D++(jacCoords c.K.E++jointLive c))
    (by intro x hx; exact List.mem_append_left _ hx) (by rw [hL.lookup.layout.n]; exact hc.copy)
  rw [hL.lookup.layout.n] at cp
  exact cp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun _ hx =>
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hx)))⟩)

theorem jointFixedDigit_relCT {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {row : JointGeneratorRow C G} {E : Nat → Fe C}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (hj : j<257) (hc : JointFixedChecks c) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) A t ∧
      s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j)
      (Joint.fixedDigit c)
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have hbytes : c.gBits+j<size := by
    have hh := hL.lookup.layout.stableBounds (c.gBits,257) (by simp [jointStableRanges])
    dsimp only at hh
    omega
  apply nafDigitBranch_relCT (K:={c.K with bits:=c.gBits}) hbytes hc.read
    (fun _ hs => hs.stable.generator j hj)
    (fun _ _ hk st hs => hs.of_keeps hk (by decide)
      (fun a ha hb ho => (hs.external a ha hb ho).of_keeps hk st))
  intro hb s t ts tt s' t' ⟨hp,cs,ct,s8,t8⟩ es et
  have hmag : FastNaf.magnitude 7 u j≠0 := fun he => hb ((FastNaf.byte_zero_iff 7 u j).mpr he)
  have ha : 1≤FastNaf.magnitude 7 u j := by omega
  have hbound := FastNaf.magnitude_le (Or.inr rfl) u j
  have ho := (FastNaf.magnitude_odd_or_zero 7 u j).resolve_left hmag
  have hmagn : nafMagnitude (FastNaf.byte 7 u j)=FastNaf.magnitude 7 u j := FastNaf.byte_magnitude 7 u j
  have zero : E c.K.zero=0 := by
    rw [←hp.1.val _ (by simp [jointLive,winRo])]
    exact cs.stable.zero
  have ds : ∀ x∈jacCoords c.K.E,x∈jointSlots c := by intro x hx; jslots
  have entry := jointFixedEntry_relCT (base:=base) (T:=T) (E:=E) (V:=jointLive c)
    (b:=FastNaf.byte 7 u j) hL.lookup.layout.lay hL.lookup.layout.n hm
    (hmagn.symm ▸ ha) hL.lookup.exy hL.lookup.exz ds
    (row.canonical _ ha hbound ho).1 (row.canonical _ ha hbound ho).2 hOne
    (by simp [jointLive,winRo]) zero
    (fun hx => hL.lookup.zeroApart (List.mem_append_left _ hx)) hc.entry
  exact (RelCT.seq entry (jointFixedSum_relCT hL hm hOne hc)) _ _ _ _ _ _
    ⟨hp,hmagn.symm ▸ cs.external _ ha hbound ho,hmagn.symm ▸ ct.external _ ha hbound ho,s8,t8⟩ es et

end VG.Proof.Weierstrass.X86_64
