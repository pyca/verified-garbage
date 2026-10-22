module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.LoadCandidate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ProbablePrime

/-! A saved big-endian candidate is checked without resetting its witness tape. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem check_candidate (v : RoundImpl) {s : State} {base : Addr}
    {bytes n len offset candidate : Nat} {r : List Byte} {ptr : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - 16#32) base bytes)
    (tape : WitnessTape base bytes (s.gpr .esp) ptr r s)
    (cursor : s.mem.readW (off base witnessCursor) 32 = ptr)
    (remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length)
    (lower : 4 ≤ n) (upper : n ≤ 48) (lenLow : 4 ≤ len) (length : len ≤ 8 * n) (aligned : len % 4 = 0)
    (sourceLow : 16384 ≤ offset) (sourceFit : offset + len ≤ bytes)
    (candidateBytes : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base offset) len) = candidate)
    (large : 8161 < candidate) (odd : candidate % 2 = 1)
    (bitLength : Spec.Dsa.bitLength candidate = 8 * len)
    (policy : 1024 < 8 * len ↔ 16 < n) (startBound : r.length < 2 ^ 32) :
    WP isa (checkCandidate v.name v.code n len offset) s fun t => ∃ rest next,
      PrimalityResult s base bytes len (Spec.Dsa.probablePrime candidate r) rest next t := by
  unfold checkCandidate
  refine WP.seq (WP.mono (load_candidate scr capacity upper lenLow length aligned sourceLow sourceFit)
    fun a ⟨value, F, K⟩ => ?_)
  have Sa := scr.of_keeps K (by decide)
  have Ra : RoundRoom (a.gpr .esp) base bytes := by rw [K.1 .esp (by decide)]; exact room
  have stackA : StkOk (a.gpr .esp - 16#32) base bytes := by rw [K.1 .esp (by decide)]; exact stack
  have stage := preparation_round_frame (len := len) F room.low
  have Ta : WitnessTape base bytes (a.gpr .esp) ptr r a := by
    rw [K.1 .esp (by decide)]
    exact tape.keep stage capacity (by omega) K.2.1 K.2.2
  have controls := preparation_control F capacity room.callRoom
  refine WP.mono (probable_prime v Sa capacity Ra stackA Ta
    (by rw [controls witnessCursor (by decide) (by decide)]; exact cursor)
    (by rw [controls witnessRemaining (by decide) (by decide)]; exact remaining)
    lower upper lenLow length aligned (value.trans candidateBytes) large odd bitLength policy startBound)
    fun t ⟨rest, next, R⟩ => ?_
  exact ⟨rest, next, R.prefix stage (K.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
