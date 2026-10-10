import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCanonicalizeVector
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

def conversionOutputChk (p : Params) : Bool :=
  (List.range p.ℓ).all fun r =>
    keepB (sgR p) (sgW p) [(yP p r,1024)] (sc oCT) (cLen p) &&
    famChk (sgR p) (sgW p) [(yP p r,1024)] 5 p.k

theorem conversionOutputChk_ok {p : Params} (hp : Ok3 p) : conversionOutputChk p=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

structure AcceptedConversion (p : Params) (S : Nat) (σ : State) (κ : Nat)
    (lo hi : Int) (done : Nat) (s : State) : Prop where
  z : CanonicalizeZState p S σ (Zv p σ κ) lo hi done s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p)=CTv p σ κ
  hints : HFam s 5 p.k (Hv p σ κ)

theorem acceptedConversion_step {p : Params} {S : Nat} {σ s : State} {κ r : Nat} {lo hi : Int}
    (hp : Ok3 p) (hr : r<p.ℓ) (hl : -(q:Int)<lo) (hh : hi<(q:Int))
    (h : AcceptedConversion p S σ κ lo hi r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p r) s
      (AcceptedConversion p S σ κ lo hi (r+1)) := by
  have hc := conversionOutputChk_ok hp
  simp only [conversionOutputChk,List.all_eq_true,List.mem_range,Bool.and_eq_true] at hc
  refine WP.mono (canonicalizeZ_step_post hr (canonicalizeZChk_ok hp r hr)
    (canonicalizeZKeepChk_ok hp) hl hh h.z) fun t ⟨hz,hpost⟩ => ?_
  exact ⟨hz,(h.z.rooted.1.lay.keepBytes hpost (hc r hr).1).trans h.ct,
    HFam.keep h.z.rooted.1.lay hpost (hc r hr).2 h.hints⟩

/-- Accepted signed responses are converted once and packed to the exact
signature bytes of the passing iteration. -/
theorem optimizedOutput_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {σ s : State} {κ : Nat} {lo hi : Int}
    (h : AcceptedConversion p S σ κ lo hi 0 s)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int)) (hpass : PassV p σ κ) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.output P p) s fun t =>
      St p S σ t ∧ bytesAt t.mem (pa t (.x23,0)) p.sigLen=sigV p σ κ ∧ t.gpr .x24=1 := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.output
  refine WP.seq (WP.mono (seqR_ok (I := fun r s => AcceptedConversion p S σ κ lo hi r s)
    p.ℓ 0 (fun r _ hr s h => acceptedConversion_step hp (by omega) hl hh h) s h)
    fun t ht => ?_)
  simp only [Nat.zero_add] at ht
  exact Output.output_ok hP (Output.oChk_ok hp) ht.z.rooted.1 ht.ct ht.z.converted ht.hints hpass ht.z.flag

end VG.Proof.MlDsa.AArch64.Sign
