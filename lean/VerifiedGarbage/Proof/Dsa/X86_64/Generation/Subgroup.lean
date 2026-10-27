module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupState
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Algebra.Group.Nat.Defs

/-! # Complete native subgroup-candidate generation and primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate

theorem subgroup_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Pbkdf2.Md.X86_64.Calls.StreamOK G1) (h256 : Pbkdf2.Md.X86_64.Calls.StreamOK G256)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32) (T : PrimeTest)
    {p : SubgroupPlan} {used : Nat} {s : State} (h : SubgroupState p used s) :
    WP isa (Impl.Dsa.X86_64.Generation.subgroup G1 G256 T.run p.prime.len) s fun t =>
      let res := Spec.Dsa.probablePrime p.prime.N (p.prime.rand.drop used)
      ∃ used' status V', used' ≤ p.prime.rand.length ∧
        Lay t p.prime.sp p.hash ∧
        Rep t.mem p.prime.sp p.hash V' (upd (upd p.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        Spec.Rsa.bytesAt t.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.prime.rand.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨V, R⟩ := h.rep
  have plen : p.prime.len ≤ 32 := by rcases p.width with hh | hh <;> omega
  unfold Impl.Dsa.X86_64.Generation.subgroup
  refine WP.seq (WP.mono (qCandidate_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 p.width
    h.layout R h.label p.outputSlot h.outputWrite (fun i hi j hj => ?_) p.outputHash)
    fun u ⟨uq, urd, uwr, _, fu, Lu, Vu, Ru⟩ => ?_)
  · have he := p.outputHash.scratch j hj (oDig + i) (by unfold oDig oRsa; omega)
    simpa only [off_off] using Ne.symm he
  have ubytes : Spec.Rsa.bytesAt u.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N := by
    rw [uq, h.seed, ← p.modulus]
  have tapeU := source_of_frame h.tape fu p.tapeHash p.prime.randMax urd uwr
  have hc : Impl.Dsa.X86_64.ProbablePrime.candidate (8 * p.prime.len) = Impl.Dsa.Generation.Layout.q := by
    unfold Impl.Dsa.X86_64.ProbablePrime.candidate
    rcases p.width with hh | hh <;> rw [hh] <;> decide
  have hin : PrimeCallInputs (8 * p.prime.len) p.prime.sp p.hash (p.W 5) p.prime.rp p.prime.rand
      p.prime.N used p.W Vu u := {
    layout := Lu
    rep := Ru
    arena := rfl
    arenaWrite := h.arena.congr uwr
    tapePtr := p.tapePtr
    tapeLength := p.tapeLength
    usedSlot := h.usedSlot
    usedBound := h.usedBound
    tapeSize := p.prime.randMax
    tapeCover := by rw [urd, uwr]; exact h.tapeCover
    tapeBytes := bytes_of_src tapeU
    candidate := by
      rw [hc, Nat.mul_div_cancel_left _ (by decide)]
      change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt u.mem (p.W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.q)
        p.prime.len) = p.prime.N
      rw [p.outputPtr, ubytes, VG.Proof.Dsa.decodeBE_os2ip]
      exact p.encoding
    odd := by
      rw [p.modulus]
      exact (VG.Proof.Dsa.Generation.qCandidate_shape
        (show 2 ≤ 8 * p.prime.len by rcases p.width with hh | hh <;> omega) p.seed).1
    bitLen := p.bits }
  have hch : primeCallChanged (8 * p.prime.len) p.prime.sp (p.W 5) =
      p.primeWrites ++ [⟨p.prime.sp, frameBytes⟩] := by
    rw [SubgroupPlan.primeWrites, ← p.base, ← p.witnessPtr, primeCallChanged,
      Nat.mul_div_cancel_left _ (by decide)]
    rfl
  refine WP.mono (primeCall_ok T (by rcases p.width with hh | hh <;> rw [hh] <;> unfold ProbablePrime.Supported <;> decide) hin p.geometry)
    fun t ⟨used', status, hb, Lt, Rt, he, hr, ft, rdt, wrt⟩ => ?_
  rw [hch] at ft
  refine ⟨used', status, Vu, hb, Lt, Rt, ?_, he, hr, ?_, rdt.trans urd, wrt.trans uwr⟩
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact p.outputPrime r hr
      · rcases List.mem_singleton.mp hr with rfl; exact p.outputFrame) (by omega), ubytes]
  · exact (fu.mono (by intro r hr; simp only [SubgroupPlan.changed, List.mem_append]; exact Or.inl (Or.inl hr))).trans
      (ft.mono (by intro r hr; simp only [SubgroupPlan.changed, List.append_assoc]; exact List.mem_append_right _ hr))

end VG.Proof.Dsa.X86_64.Generation
