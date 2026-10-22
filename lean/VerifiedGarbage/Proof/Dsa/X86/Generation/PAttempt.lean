module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PConstruct
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PTest
public import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeObservation
import VerifiedGarbage.Proof.Dsa.X86.Generation.SubgroupReads
import VerifiedGarbage.Proof.Dsa.Generation.PCandidate

/-! Construct and check one specified modulus candidate with exact witness-tape consumption. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.MillerRabin.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

structure PAttemptResult (s₀ : State) (base : Addr) (bytes n p q : Nat)
    (result : Option (Bool × List Byte)) (r : List Byte) (ptr : BitVec 32) (s : State) : Prop where
  observation : PrimeObservation s₀ base bytes result r ptr s
  candidate : Spec.Rsa.bytesAt s.mem (off base Layout.p) (8 * n) = Spec.Dsa.encodeBE (8 * n) p
  exponent : Spec.Rsa.bytesAt s.mem (off base Layout.exponent) (8 * n) = Spec.Dsa.encodeBE (8 * n) ((p - 1) / q)
  frame : AttemptFrame base (s₀.gpr .esp) (8 * n) s₀ s

theorem p_attempt (v : RoundImpl) {H : Hash} (ok : HashOK H) {s : State} {base : Addr}
    {bytes n offset q : Nat} {seedSrc ptr : BitVec 32} {seed r : List Byte}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - 16#32) base bytes)
    (supported : Spec.Dsa.subgroupBits (64 * n) = some (8 * H.D))
    (seedTape : WitnessTape base bytes (s.gpr .esp) seedSrc seed s) (length : seed.length ≤ 32)
    (pointer : s.mem.readW (off base seedPointer) 32 = seedSrc)
    (value : s.mem.readW (off base candidateOffset) 32 = BitVec.ofNat 32 offset)
    (small : offset + (64 * n - 1) / (8 * H.D) < 2 ^ 31)
    (hash : ∀ x, ok.SH.H.hash x = Spec.Dsa.seedHash (8 * H.D) x)
    (digestLength : ∀ x, (Spec.Dsa.seedHash (8 * H.D) x).length = H.D)
    (subgroup : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base Layout.q) H.D) = q)
    (positive : 0 < q) (bound : 2 * q < 2 ^ (64 * n))
    (tape : WitnessTape base bytes (s.gpr .esp) ptr r s)
    (cursor : s.mem.readW (off base witnessCursor) 32 = ptr)
    (remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length)
    (startBound : r.length < 2 ^ 32) :
    WP isa (pAttempt H v.name v.code seed.length n) s fun t => ∃ rest next,
      PAttemptResult s base bytes n (Spec.Dsa.pCandidate (64 * n) (8 * H.D) q seed offset) q
        (pTestResult (64 * n) (Spec.Dsa.pCandidate (64 * n) (8 * H.D) q seed offset) r) rest next t := by
  have pairs := construction_sizes supported
  have sizes : n = 16 ∨ n = 32 ∨ n = 48 := by rcases pairs with h | h | h <;> omega
  have upper : n ≤ 48 := by rcases sizes with h | h | h <;> omega
  have hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * H.D) bs).length = 8 * H.D := by intro bs; rw [digestLength]
  have shape := VG.Proof.Dsa.Generation.pCandidate_shape (by rcases sizes with h | h | h <;> omega : 2 ≤ 64 * n)
    hashSize q seed offset
  unfold pAttempt
  refine WP.seq (WP.mono (p_construct ok scr capacity room stack supported seedTape length pointer value small
    hash digestLength subgroup positive bound) fun a ⟨pBytes, exponentBytes, F, K⟩ => ?_)
  have Sa := scr.of_keeps K (by decide)
  have Ra : RoundRoom (a.gpr .esp) base bytes := by rw [K.1 .esp (by decide)]; exact room
  have stackA : StkOk (a.gpr .esp - 16#32) base bytes := by rw [K.1 .esp (by decide)]; exact stack
  have prefixFrame := construction_enclose F capacity room
  have Ta : WitnessTape base bytes (a.gpr .esp) ptr r a := by
    rw [K.1 .esp (by decide)]
    exact tape.keep_enclosed prefixFrame K.2.1 K.2.2
  have controls := construction_control F capacity room
  refine WP.mono (p_test v Sa capacity Ra stackA sizes Ta
    (by rw [controls witnessCursor (by decide) (by decide)]; exact cursor)
    (by rw [controls witnessRemaining (by decide) (by decide)]; exact remaining)
    shape.2.2 shape.1 pBytes startBound) fun t ⟨rest, next, R⟩ => ?_
  refine ⟨rest, next, (R.observation capacity (by omega)).prefix prefixFrame (K.mono (by decide)), ?_, ?_, ?_⟩
  · rw [sample_saved_bytes R.frame capacity Ra (by decide) (by unfold Layout.p Layout.witness; omega) (by omega)]
    exact pBytes
  · rw [sample_saved_bytes R.frame capacity Ra (by decide) (by unfold Layout.exponent Layout.witness; omega) (by omega)]
    exact exponentBytes
  · have last := attempt_sample_frame R.frame
    rw [K.1 .esp (by decide)] at last
    exact (attempt_construction_frame F room.low).trans last

end VG.Proof.Dsa.X86.Generation
