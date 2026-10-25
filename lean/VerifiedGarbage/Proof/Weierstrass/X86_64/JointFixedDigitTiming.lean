module

import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming
public import VerifiedGarbage.Impl.Weierstrass.X86_64.JointFixed
public import VerifiedGarbage.Impl.Weierstrass.X86_64.TComb
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState
public import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming

/-! Timing of a complete fixed-generator digit, including its public zero case. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
                   List.not_mem_nil,or_false] at * <;> grind))

structure JointFixedChecks (c : Joint.Cfg) : Prop where
  read : RegCT [.rdi,.rbx] (.block (Joint.fixedRead c))
  entry : FixedLookupCT c.tsym
    (if c.gw=9 then Joint.fixedEntryW c.K c.tsym else Joint.fixedEntry c.K c.tsym)
  add : JacMixedChecks c.K c.K.R c.K.E c.K.D
  copy : ScratchCT (.block (copyPt c.K.M.n c.K.R c.K.D))

theorem jointFixedSum_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (hc : JointFixedChecks c) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c) (jacCoords c.K.E++jointLive c) E)
      (Joint.fixedAdd c).inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  refine jointAdd_relCT_dispatch (body := PointOps.addAffineBody c.K) rfl (fun _ => rfl)
    (fun C' hp => (hL.calls.ok C' hp).2.1) ?_
  have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E,x∈jointSlots c := by intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E,x∈jacCoords c.K.E++jointLive c := by intro x hx; jslots
  apply RelCT.seq (jacMixedForward_relCT hL.lookup.layout.lay hm hc.add hL.addApart sl vr hOne)
  apply RelCT.exists_
  intro E'
  have cp := copyPoint_relCT (base:=base) (E:=E') hL.lookup.layout.lay
    (o:=c.K.R) (q:=c.K.D) (by intro x hx; jslots)
    (V:=jacCoords c.K.D++(jacCoords c.K.E++jointLive c))
    (by intro x hx; exact List.mem_append_left _ hx) hc.copy
  exact cp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun _ hx =>
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hx)))⟩)

theorem jointFixedDigit_relCT {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {E : Nat → Fe C}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (hj : j<64*c.K.M.n+1) (hc : JointFixedChecks c) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) A t ∧
      s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j)
      (Joint.fixedDigit c).inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  rw [Joint.fixedDigit]
  simp only [Code.inline]
  apply digitBranchRead_relCT hc.read (fun s _ cs hb => jointFixedRead_ok hL.lookup.layout cs hj hb)
    (fun _ _ hk st hs => hs.of_keeps hk (by decide)
      (fun a ha hb ho => (hs.external a ha hb ho).of_keeps hk st))
  intro hz
  have hmag : FastNaf.magnitude c.gw u j≠0 := of_decide_eq_false hz
  have ha : 1≤FastNaf.magnitude c.gw u j := by omega
  have hbound : FastNaf.magnitude c.gw u j≤jointGTop c := by
    unfold jointGTop
    rcases hL.lookup.layout.gw with h|h
    · simp only [h,show ¬(7:Nat)=9 from by decide,ite_false]
      exact FastNaf.magnitude_le (Or.inr rfl) u j
    · simp only [h,ite_true]
      have := FastNaf9.magnitude_le u j
      simpa only [FastNaf.magnitude,FastNaf.ne_9_7,ite_true,ite_false] using this
  have ho := (FastNaf.magnitude_odd_or_zero c.gw u j).resolve_left hmag
  have ds : ∀ x∈jacCoords c.K.E,x∈jointSlots c := by intro x hx; jslots
  have hzero : c.K.zero∉jacCoords c.K.E := fun hx => hL.lookup.zeroApart (List.mem_append_left _ hx)
  have entry : RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) A t ∧
      s.gpr .r8=jointGCell c u j ∧ t.gpr .r8=jointGCell c u j)
      (if c.gw=9 then Joint.fixedEntryW c.K c.tsym else Joint.fixedEntry c.K c.tsym).inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        (jacCoords c.K.E++jointLive c) E' s t) := by
    intro s t ts tt s' t' ⟨hp,cs,ct,s8,t8⟩ es et
    have zero : E c.K.zero=0 := by
      rw [←hp.1.val _ (by simp [jointLive,winRo])]
      exact cs.stable.zero
    have hce := hc.entry
    by_cases h9 : c.gw=9
    · rw [ite_eq_left h9] at es et hce
      rw [jointGCell,ite_eq_left h9] at s8 t8
      have hmw := word_magnitudeW u j
      rw [h9] at ha hbound ho
      rw [← hmw] at ha hbound ho
      have e := jointFixedEntryW_relCT (base:=base) (T:=T) (E:=E) (V:=jointLive c)
        (d:=FastNaf.word u j) hL.lookup.layout.lay hL.lookup.layout.n hm
        ha hL.lookup.exy hL.lookup.exz ds
        (row.canonical _ ha hbound ho).1 (row.canonical _ ha hbound ho).2 hOne
        (by simp [jointLive,winRo]) zero hzero hce
      exact (e.mono (Q':=fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        (jacCoords c.K.E++jointLive c) E' s t) (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)) _ _ _ _ _ _
        ⟨hp,cs.external _ ha hbound ho,ct.external _ ha hbound ho,s8,t8⟩ es et
    · have h7 : c.gw=7 := hL.lookup.layout.gw.resolve_right h9
      rw [ite_eq_right h9] at es et hce
      rw [jointGCell,ite_eq_right h9] at s8 t8
      have hmb : nafMagnitude (FastNaf.byte 7 u j)=FastNaf.magnitude 7 u j := FastNaf.byte_magnitude 7 u j
      rw [h7] at ha hbound ho
      rw [← hmb] at ha hbound ho
      have e := jointFixedEntry_relCT (base:=base) (T:=T) (E:=E) (V:=jointLive c)
        (b:=FastNaf.byte 7 u j) hL.lookup.layout.lay hL.lookup.layout.n hm
        ha hL.lookup.exy hL.lookup.exz ds
        (row.canonical _ ha hbound ho).1 (row.canonical _ ha hbound ho).2 hOne
        (by simp [jointLive,winRo]) zero hzero hce
      exact (e.mono (Q':=fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        (jacCoords c.K.E++jointLive c) E' s t) (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)) _ _ _ _ _ _
        ⟨hp,cs.external _ ha hbound ho,ct.external _ ha hbound ho,s8,t8⟩ es et
  exact RelCT.seq entry (RelCT.exists_ fun E' => jointFixedSum_relCT (E:=E') hL hm hOne hc)

end VG.Proof.Weierstrass.X86_64
