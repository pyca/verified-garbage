module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparationReads
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MillerRabin
public import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.BitLengthBounds

/-! Prepare one full-width candidate and run the existing DSA witness policy. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.Generation (candidateLoop)

theorem test_candidate (v : RoundImpl) {s : State} {base : Addr}
    {bytes n len candidate : Nat} {r : List Byte} {ptr : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - 16#32) base bytes)
    (tape : WitnessTape base bytes (s.gpr .esp) ptr r s)
    (cursor : s.mem.readW (off base witnessCursor) 32 = ptr)
    (remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length)
    (lower : 4 ≤ n) (upper : n ≤ 48) (lenLow : 4 ≤ len) (length : len ≤ 8 * n) (aligned : len % 4 = 0)
    (modulus : wordsVal s.mem base (slot n 0) n = candidate) (large : 3 ≤ candidate) (odd : candidate % 2 = 1)
    (bitLength : Spec.Dsa.bitLength candidate = 8 * len) (startBound : r.length < 2 ^ 32) :
    WP isa (testCandidate v.name v.code n len) s fun t => ∃ rest next,
      LoopResult s base bytes n len candidate (candidateLoop candidate (Spec.Dsa.primeChecks (8 * len)) 1 0 r) rest next t := by
  have lenBound : len ≤ 384 := by omega
  have bounds := (VG.Proof.Dsa.bitLength_iff_bounds (by omega : 0 < 8 * len)).mp bitLength
  have bits := VG.Proof.Dsa.Generation.predecessor_bits (by omega : 2 ≤ 8 * len) odd bitLength
  have width : Spec.RsaKeyGen.witnessBytes candidate = witnessDrawBytes len := by
    rw [Spec.RsaKeyGen.witnessBytes, bits]
    unfold witnessDrawBytes
    congr 1
    omega
  have drawBound : witnessDrawBytes len < 2 ^ 32 := by unfold witnessDrawBytes; omega
  have checksBound : Spec.Dsa.primeChecks (8 * len) < 2 ^ 32 := by unfold Spec.Dsa.primeChecks; split <;> decide
  unfold testCandidate
  refine WP.seq (WP.mono (prepare_prime scr capacity room.callRoom stack lower upper modulus large odd
    (by omega) (by omega) bounds.1) fun a ⟨A, F, K⟩ => ?_)
  have Sa := scr.of_keeps K (by decide)
  have Ra : RoundRoom (a.gpr .esp) base bytes := by rw [K.1 .esp (by decide)]; exact room
  have stage := preparation_round_frame (len := len) F room.low
  have Ta : WitnessTape base bytes (a.gpr .esp) ptr r a := by
    rw [K.1 .esp (by decide)]
    exact tape.keep stage capacity lenBound K.2.1 K.2.2
  have controls := preparation_control F capacity room.callRoom
  refine WP.mono (miller_rabin v Sa capacity A Ra Ta
    (by rw [controls witnessCursor (by decide) (by decide)]; exact cursor)
    (by rw [controls witnessRemaining (by decide) (by decide)]; exact remaining)
    (by omega) upper lenLow length aligned (by unfold witnessDrawBytes; omega) bits width drawBound checksBound startBound)
    fun t ⟨rest, next, R⟩ => ?_
  exact ⟨rest, next, R.prefix stage (K.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
