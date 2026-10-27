module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets

/-! # A full-width p candidate is tested by the probable-prime function -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaOaep.AArch64

theorem PrimeCallPlan.bits_eq (p : PrimeCallPlan) : 8 * p.prime.len = p.bits := by
  rw [p.len]; rcases p.supported with h | h | h | h | h <;> rw [h]

theorem pTest_full_ok (T : PrimeTest) {p : PrimeCallPlan} {used : Nat} {s : State}
    {V : Nat → Byte} {pp : Addr}
    (L : Lay s p.F p.hash) (R : Rep s.mem p.F p.hash V p.W)
    (h : Ws s p.prime.B p.prime.Z p.prime.w)
    (hptr : VG.Proof.Bignum.word s.mem p.prime.B 160 = pp)
    (hbound : p.prime.N < 256 ^ p.prime.len)
    (hbytes : Spec.Rsa.bytesAt s.mem pp p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N)
    (hrd : InRegions (s.rd ++ s.wr) pp 1) (hfull : ¬ p.prime.N < 2 ^ (8 * p.prime.len - 1))
    (hcandidate : Impl.Dsa.AArch64.ProbablePrime.candidate p.bits = Impl.Dsa.Generation.Layout.p)
    (hused : p.W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.prime.rand.length)
    (hA : Scr s (p.W 5) Impl.Dsa.Generation.Layout.domainCheck)
    (htc : Covers [⟨p.prime.rp, p.prime.rand.length⟩] (s.rd ++ s.wr))
    (htape : Src s p.prime.B p.prime.Z p.prime.rp p.prime.rand)
    (hcand : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off (p.W 5) Impl.Dsa.Generation.Layout.p)
      p.prime.len) = p.prime.N) :
    WP isa (Impl.Dsa.AArch64.Generation.pTest T.run p.prime.len) s fun t =>
      let res := Spec.Dsa.probablePrime p.prime.N (p.prime.rand.drop used)
      ∃ used' status, used' ≤ p.prime.rand.length ∧ Lay t p.F p.hash ∧
        Rep t.mem p.F p.hash V (upd (upd p.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.prime.rand.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.AArch64.Generation.pTest
  refine WP.seq (WP.mono (candidateWidth_ok h hptr (by have := p.prime.len2; omega)
    hbound hbytes hrd) fun u ⟨hcf, hm, ku⟩ => ?_)
  have Ru : Rep u.mem p.F p.hash V p.W := hm ▸ R
  have Lu := lay_of_rep L R Ru rfl ku.sp ku.wr
  refine WP.ite false (by simp [hcf, hfull]) (fun he => Bool.noConfusion he) (fun _ => ?_)
  rw [p.bits_eq]
  have hin : PrimeCallInputs p.bits p.F p.hash (p.W 5) p.prime.rp p.prime.rand p.prime.N used p.W V u := {
    layout := Lu
    rep := Ru
    arena := rfl
    arenaWrite := hA.congr ku.wr
    tapePtr := p.tapePtr
    tapeLength := p.tapeLength
    usedSlot := hused
    usedBound := hu
    tapeSize := p.prime.randMax
    tapeCover := by rw [ku.rd, ku.wr]; exact htc
    tapeBytes := by rw [hm]; exact bytes_of_src htape
    candidate := by rw [hcandidate, hm, ← p.bits_eq, Nat.mul_div_cancel_left _ (by decide)]; exact hcand
    odd := p.prime.odd
    bitLen := by rw [p.prime.bitLength_eq, p.bits_eq] }
  refine WP.mono (primeCall_ok T p.supported hin p.geometry)
    fun t ⟨used', status, hb, Lt, Rt, he, hr, ft, rdt, wrt⟩ => ?_
  refine ⟨used', status, hb, Lt, Rt, he, hr, ?_, rdt.trans ku.rd, wrt.trans ku.wr⟩
  rw [p.changed_eq, ← hm]
  exact ft

end VG.Proof.Dsa.AArch64.Generation
