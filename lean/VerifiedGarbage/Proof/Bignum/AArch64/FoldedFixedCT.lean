module

public import VerifiedGarbage.Proof.Bignum.AArch64.FoldedCT
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedExp
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum.AArch64

def FinalReady (p : PublicData) (s : State) : Prop :=
  ∃ X, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ Facts p ∧
    wv s.mem p.L.B (slot p.L.w aY) p.L.w < p.N

theorem exp65536_fw (M : Mont) (p : PublicData) (s : State) (h : Pre p s) :
    WP isa (Folded.exp65536 M.mm) s (FinalReady p) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := h
  exact WP.mono (exp65536_ok M hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hlt hx)
    fun t ⟨ct,yt,_⟩ => ⟨X,ct,hf,yt⟩

/-- The final multiplication keeps the second operand canonical even when
an invalid ordinary input will subsequently be masked out. -/
theorem finalAndMark_ct (M : Mont) :
    RelCT isa (Two FinalReady)
      (.seq (M.mm aY aX aY) (.block [movi .x3 2, sth .x3 sStarted])) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun (p : PublicData) t => t.gpr .x0 = p.L.B)
    (two_map (fun p : PublicData => p.L)
      (fun _ _ ⟨_,hc,hf,_⟩ => ⟨hc.good,hf.1⟩)
      (M.ctL (o := aY) (a := aX) (b := aY) (by simp [MmUse]))) ?_)
    (two_taint [.x0] (fun _ _ _ hs ht r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact hs.trans ht.symm) (by taint_decide))
  rintro p s ⟨X,hc,hf,hlt⟩
  exact WP.mono (M.mm_ok hc.good hf.1 hf.2.1 hf.2.2.1 (o := aY) (a := aX) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hc.inv (by rw [hc.n]; exact hlt)) fun t ⟨hg,_⟩ => hg.x0

theorem fixedLoop_ct (M : Mont) :
    RelCT isa (Two Pre) (Folded.fixedLoop M.mm) (fun _ _ => True) := by
  change RelCT isa (Two Pre) (seqs ([Precomputed.start, .block [movi .x3 16, sth .x3 sI],
    .loop (Folded.squareStep M.mm) (.nonzero .x .x3)] ++
    [M.mm aY aX aY, .block [movi .x3 2, sth .x3 sStarted]])) (fun _ _ => True)
  apply RelCT.seqs_append (by simp) (by simp)
  exact RelCT.seq (two_post (exp65536_ct M) (exp65536_fw M)) (finalAndMark_ct M)

end VG.Proof.Bignum.AArch64.FoldedPublic
