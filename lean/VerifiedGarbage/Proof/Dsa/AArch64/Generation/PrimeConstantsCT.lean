module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2CT
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2CT
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Derive the remaining Montgomery constants with a public trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

def PrimeGood (p : PrimeParams) (s : State) : Prop := VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w

def PrimeR2Ready (p : PrimeParams) (s : State) : Prop :=
  VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w ∧
    ((word s.mem p.B (slot p.w aN)).toNat * (word s.mem p.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem p.B (slot p.w aN) p.w = p.N ∧ wv s.mem p.B (slot p.w aOne) p.w = 1 ∧
    wv s.mem p.B (slot p.w aR2) p.w = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N

theorem primeR2_ready (M : Mont) {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (Impl.Dsa.AArch64.Generation.primeR2 M.mm) s (PrimeR2Ready p) :=
  WP.mono (primeR2_ok M h.1 h.2.2 h.2.1 p.odd (by have := p.n3; omega))
    (fun _ ⟨ws, inv, hn, hone, hr2, _, _⟩ => ⟨ws, inv, hn, hone, hr2⟩)

theorem primeMontOne_good (M : Mont) {p : PrimeParams} {s : State} (h : PrimeR2Ready p s) :
    WP isa (M.mm aY aR2 aOne) s (PrimeGood p) := by
  obtain ⟨hw, hi, hn, hone, _⟩ := h
  refine WP.mono (M.mm_ok hw.good.1 hw.good.2 hw.w1 (by have := hw.w2; omega)
    (o := aY) (a := aR2) (b := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hi (by rw [hone, hn]; have := p.n3; omega))
    fun t ⟨_, _, _, ha, hk⟩ => ?_
  have hf : Frm p.B (VG.Proof.Ffdh.AArch64.ParameterCandidate.mpTail p.w) s.mem t.mem :=
    Frm.of_arrays ha (by simp [VG.Proof.Ffdh.AArch64.ParameterCandidate.mpTail])
  exact hw.congr' hf (VG.Proof.Ffdh.AArch64.ParameterCandidate.mpTail_kmut p.w) hk (by decide)

theorem copyR1_ct : RelCT isa (Two PrimeGood) (copyA aR1 aY) (fun _ _ => True) := by
  change RelCT isa (Two PrimeGood)
    (.seq (.block (ws ++ (base aY .x16 ++ base aR1 .x17))) copyWords) _
  exact ws_ct0 PrimeParams.B PrimeParams.Z PrimeParams.w (fun _ _ h => h) (by taint_decide)

theorem copyR1_good {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa (copyA aR1 aY) s (PrimeGood p) := by
  refine WP.mono (copyA_ok h (o := aR1) (a := aY) (by decide) (by decide) (by decide))
    fun t ⟨_, ho, _, _, hk⟩ => ?_
  have hf : Frm p.B [(slot p.w aR1, 8 * p.w)] s.mem t.mem := Frm.of_outside ho (by simp)
  exact h.congr' hf
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.ofSlot _ _ _) hk (by decide)

theorem negateR1_ct : RelCT isa (Two PrimeGood) (seqs (subA aRm1 aN aR1)) (fun _ _ => True) := by
  rw [subA_eq']
  exact ws_ct0 PrimeParams.B PrimeParams.Z PrimeParams.w (fun _ _ h => h) (by taint_decide)

theorem primeConstants_ct (M : Mont) : RelCT isa (Two PrimeR2Ready)
    (seqs (Impl.Dsa.AArch64.Generation.primeConstants M.mm)) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.primeConstants
  apply RelCT.seqs_append (by simp) (by simp [subA])
  simp only [seqs]
  refine RelCT.seq (RelCT.seq (two_post
    (two_map (fun p : PrimeParams => (⟨p.B, p.Z, p.w⟩ : VG.Proof.Bignum.AArch64.Ws))
      (fun _ _ h => ⟨_, h.1.good⟩) (M.ct (o := aY) (a := aR2) (b := aOne) (by unfold MmUse; decide)))
    (fun _ _ h => primeMontOne_good M h))
    (two_post copyR1_ct (fun _ _ h => copyR1_good h))) negateR1_ct

end VG.Proof.Dsa.AArch64.Generation
