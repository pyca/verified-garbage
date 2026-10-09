import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintCheck
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowState

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- The response hint is unchanged when low/high decomposition is kept separately. -/
theorem hintRow_value (p : Params) (σ : State) (κ i : Nat) :
    Vector.zipWith (fun ci fi=>makeHint p.γ₂ (-ci) (fi+ci))
      (CT0v p σ κ i) (W'v p σ κ i) = Hv p σ κ i := by
  apply Vector.ext
  intro j hj
  simp only [Hv,VG.Proof.MlDsa.Sign.hF,VG.Proof.MlDsa.Sign.w''F,
    neg,add,Vector.getElem_zipWith,Vector.getElem_map]

def hintRowWrites (i : Nat) := [(t1P,1024),(sc oPS,1024),(hP i,1024)]

def hintProductFrameChk (p : Params) (i : Nat) : Bool :=
  let ws := [(t1P,1024),(sc oPS,1024)]
  stChk p ws && ws.all (fun w=>inB (sgW p) w.1 w.2) &&
  keepB (sgR p) (sgW p) ws (hP i) 1024 &&
  keepB (sgR p) (sgW p) ws (wP p i) 1024

theorem hintProductFrameChk_ok {p : Params} (hp : Ok3 p) :
    ∀i<p.k,hintProductFrameChk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

/-- One raw challenge product and the fused norm/hint helper, with their complete write frame. -/
theorem hintRow_ok {p : Params} {S : Nat} {σ s : State} {i : Nat} {f ch sk : Poly}
    (hp : Ok3 p) (hi : i<p.k) (hs : RootedSt p S σ s)
    (hch : PosPolyIs s.mem (pa s cP) ch)
    (hsk : PosPolyIs s.mem (pa s (t0P p i)) sk)
    (hl : SignedPolyIs s.mem (pa s (hP i))
      (f.map fun r=>ofInt (lowBits p.γ₂ r)) (-(p.γ₂:Int)) p.γ₂)
    (hh : NatPolyIs s.mem (pa s (wP p i)) (f.map fun r=>(highBits p.γ₂ r).toNat))
    (hg : p.γ₂∈gamma2s) :
    WP isa (.seq (Impl.MlDsa.AArch64.Sign.Optimized.responseProduct t1P (t0P p i))
      (callAt "vg_mldsa_signed_hint_norm" Impl.MlDsa.AArch64.Optimized.Response.hintNorm
        (Response.hintNormArgs (hP i) t1P (wP p i) p.γ₂))) s fun t =>
      let c := nttInv (multiplyNTT ch sk)
      let h := Vector.zipWith (fun ci fi=>makeHint p.γ₂ (-ci) (fi+ci)) c f
      PPostB S s t (hintRowWrites i) ∧ RootedSt p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧
      HintIs t.mem (pa t (hP i)) 1 [h] ∧
      t.gpr .x0=BitVec.ofNat 64 (hintOnes [h]+if normRq [c]<p.γ₂ then 4294967296 else 0) := by
  have hcf := hintProductFrameChk_ok hp i hi
  simp only [hintProductFrameChk,Bool.and_eq_true] at hcf
  obtain ⟨⟨⟨hst,hw⟩,hkl⟩,hkh⟩ := hcf
  refine WP.seq (WP.mono_syms (responseProduct_ok hs (responseProductChk_hint hp i hi) hch hsk)
    fun a ⟨hpa,h24a,hprod⟩ hsa => ?_)
  have ha := hs.step hpa hsa hst (List.all_eq_true.mp hw)
  have hla := keepSignedPoly hs.1.lay hpa hkl hl
  have hha := keepNatPoly hs.1.lay hpa hkh hh
  have hraw : RawPolyIs a.mem (pa a t1P) (nttInv (multiplyNTT ch sk)) := by
    rw [hpa.pa (by decide)]; exact hprod
  refine WP.mono (hintNorm_rooted_frame (hintNormChk_ok hp i hi) ha hla hha hraw hg)
    fun t ⟨hpb,ht,h24b,hout,hret⟩ => ?_
  refine ⟨PPostB.trans hpa hpb ?_ ?_ ?_,ht,h24b.trans h24a,hout,hret⟩
  · simp [hP,pS,sc,keptRegs]
  · intro x hx; simp only [hintRowWrites,List.mem_cons,List.not_mem_nil,or_false] at *; grind
  · intro x hx; simp only [hintRowWrites,List.mem_cons,List.not_mem_nil,or_false] at *; grind

end VG.Proof.MlDsa.AArch64.Sign
