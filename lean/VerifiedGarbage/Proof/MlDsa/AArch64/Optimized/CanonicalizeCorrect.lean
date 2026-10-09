import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Spec.MlDsa.Canonicalize

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)

theorem canonicalizePrefix_poly {initial current : Mem} {p : Addr}
    (h : CanonicalizePrefix initial current p 256) (hb : CenteredReduced initial p) :
    PolyIs current p (signedPolyAt initial p) := by
  constructor
  · intro i hi
    rw [canonicalizePrefix_complete h hi]
    exact acceptedCanonical_bounds _ (hb i hi).1 (hb i hi).2
  · apply Vector.ext
    intro i hi
    simp only [polyAt,signedPolyAt,Vector.getElem_ofFn]
    rw [canonicalizePrefix_complete h hi]
    unfold ofInt
    congr 1
    have he := acceptedCanonical_mod (coeffAt initial p i) (hb i hi).1 (hb i hi).2
    exact (Int.toNat_natCast _).symm.trans (congrArg Int.toNat he)

/-- Complete measured accepted-response conversion, including initialization
and all sixteen fixed-count iterations. -/
theorem canonicalize_ok (s : State)
    (hb : CenteredReduced s.mem (s.gpr .x0))
    (hr : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize s fun t =>
      Keep [.x0,.x9,.x10] s t ∧ PolyIs t.mem (s.gpr .x0) (signedPolyAt s.mem (s.gpr .x0)) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize
  apply WP.seq
  refine WP.mono (HighPack.vc_ok s .v16 8380417) fun a ⟨ha,hva⟩ => ?_
  have ka := setup_keep (HighPack.SetupKeep.ofConst ha) (by decide)
  unfold VG.Impl.MlDsa.AArch64.Optimized.Response.loop
  apply WP.seq
  refine WP.mono (counter_ok a) fun b ⟨⟨⟨hc,hm⟩,kb⟩,hvb⟩ => ?_
  have hq : ∀e<4,vword (b.v .v16) e=8380417#32 := by
    intro e he
    rw [hvb,hva,HighPack.repeatedWord_lane _ he]
  have h0 : b.gpr .x0=s.gpr .x0 := (kb.get .x0).trans (ha.gpr .x0 (by decide))
  have hmem : b.mem=s.mem := hm.trans ha.mem
  have hrd : b.rd=s.rd := kb.rd.trans ha.rd
  have hwr : b.wr=s.wr := kb.wr.trans ha.wr
  change WP isa (.loop (.block (canonicalizeBody++advance [.x0])) (.nonzero .x .x10)) b _
  refine WP.mono (canonicalizeLoop_ok hq hc ?_ ?_) fun t ⟨kt,_,_,hp⟩ => ?_
  · simpa only [hrd,hwr,h0] using hr
  · simpa only [hwr,h0] using hw
  · refine ⟨((ka.trans kb).trans kt).mono,?_⟩
    rw [hmem,h0] at hp
    exact canonicalizePrefix_poly hp hb

end VG.Proof.MlDsa.AArch64.Optimized.Response
