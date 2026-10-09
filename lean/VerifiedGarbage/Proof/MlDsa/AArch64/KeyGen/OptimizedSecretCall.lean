import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretSeeds
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCallTiming

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.Optimized

theorem boundedReady {S : Nat} {p : Params} (hF : PFacts p) {s : State}
    (L : Lay S kgR (kgW p) s) {r : Nat} (hr : r+4≤p.ℓ+p.k+1) :
    BoundedFour.CallReady (sc 1408) (sP p r) (sc (oR4 p)) s := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hs : inB (kgR++kgW p) (sc 1408) 264=true := by lay
  have ho : inB (kgR++kgW p) (sP p r) 4096=true := by lay
  have hw : inB (kgR++kgW p) (sc (oR4 p)) 8192=true := by lay
  have hwo : inB (kgW p) (sP p r) 4096=true := by lay
  have hww : inB (kgW p) (sc (oR4 p)) 8192=true := by lay
  have hso : sepB kgR (kgW p) (sc 1408) 264 (sP p r) 4096=true := by lay
  have hsw : sepB kgR (kgW p) (sc 1408) 264 (sc (oR4 p)) 8192=true := by lay
  have how : sepB kgR (kgW p) (sP p r) 4096 (sc (oR4 p)) 8192=true := by lay
  exact ⟨L.nwp hs,L.nwp ho,L.nwp hw,L.disj hso,L.disj hsw,L.disj how,
    Covers.cons (L.cR hs) (Covers.cons (L.cR ho) (L.cR hw)),Covers.cons (L.cW hwo) (L.cW hww)⟩

theorem boundedAt_layout {S : Nat} {p : Params} (hF : PFacts p) {s : State}
    (L : Lay S kgR (kgW p) s) {r : Nat} (hr : r+4≤p.ℓ+p.k+1)
    (c : Impl.Sha3.AArch64.Callee) :
    WP isa (callAt (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.boundedFourSymbol c p.η)
      (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler c.pairedSha3 true p.η)
      (BoundedFour.samplerArgs (sc 1408) (sP p r) (sc (oR4 p)))) s fun t=>
      PPostB S s t [(sP p r,4096),(sc (oR4 p),8192)] ∧ t.gpr .x24=s.gpr .x24 ∧
      (∀i<4,Reduced t.mem (pa s (sP p r)+BitVec.ofNat 64 (1024*i))) ∧
      (∀i<4,BoundedOutput p.η t.mem (pa s (sP p r)+BitVec.ofNat 64 (1024*i))) ∧
      Outcome (fun b=>(rejBoundedFour p.η b.rejBounded s.mem (pa s (sc 1408))).map (List.map toRq))
        ((t.gpr .x0).setWidth 32)
        ((List.range 4).map fun i=>polyAt t.mem (pa s (sP p r)+BitVec.ofNat 64 (1024*i))) := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hs : inB (kgR++kgW p) (sc 1408) 264=true := by lay
  have ho : inB (kgR++kgW p) (sP p r) 4096=true := by lay
  have hw : inB (kgR++kgW p) (sc (oR4 p)) 8192=true := by lay
  have hη : p.η=2∨p.η=4 := by rcases hF.eta with h|h; exact Or.inl h.1; exact Or.inr h.1
  refine WP.mono (BoundedFour.samplerAt_ok L.s64 c.pairedSha3 hη
    (ptr_ok (L.ptrBs hs)) (ptr_ok (L.ptrBs ho)) (ptr_ok (L.ptrBs hw)) (boundedReady hF L hr))
    fun t ⟨hp,hred,hsmall,hout⟩=>?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hred,hsmall,hout⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
