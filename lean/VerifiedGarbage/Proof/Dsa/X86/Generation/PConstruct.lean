module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PConstruct
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashes
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PShape
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ConstructionFrame
import VerifiedGarbage.Proof.Dsa.Generation.Sizes
import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundContext

/-! Construct the specification's modulus candidate and generator exponent from one seed offset. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.Generation
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem construction_sizes {n digestLen : Nat} (supported : Spec.Dsa.subgroupBits (64 * n) = some (8 * digestLen)) :
    (n = 16 ∧ digestLen = 20) ∨ (n = 32 ∧ digestLen = 32) ∨ (n = 48 ∧ digestLen = 32) := by
  rcases generation_sizes supported with sizes | sizes | sizes <;> omega

theorem p_construct {H : Hash} (ok : HashOK H) {s : State} {base : Addr}
    {bytes n offset q : Nat} {src : BitVec 32} {seed : List Byte}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - 16#32) base bytes)
    (supported : Spec.Dsa.subgroupBits (64 * n) = some (8 * H.D))
    (tape : WitnessTape base bytes (s.gpr .esp) src seed s) (length : seed.length ≤ 32)
    (pointer : s.mem.readW (off base seedPointer) 32 = src)
    (value : s.mem.readW (off base candidateOffset) 32 = BitVec.ofNat 32 offset)
    (small : offset + (64 * n - 1) / (8 * H.D) < 2 ^ 31)
    (hash : ∀ x, ok.SH.H.hash x = Spec.Dsa.seedHash (8 * H.D) x)
    (digestLength : ∀ x, (Spec.Dsa.seedHash (8 * H.D) x).length = H.D)
    (subgroup : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base Layout.q) H.D) = q)
    (positive : 0 < q) (bound : 2 * q < 2 ^ (64 * n)) :
    WP isa (pConstruct H seed.length n) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base Layout.p) (8 * n) =
        Spec.Dsa.encodeBE (8 * n) (Spec.Dsa.pCandidate (64 * n) (8 * H.D) q seed offset) ∧
      Spec.Rsa.bytesAt t.mem (off base Layout.exponent) (8 * n) =
        Spec.Dsa.encodeBE (8 * n) ((Spec.Dsa.pCandidate (64 * n) (8 * H.D) q seed offset - 1) / q) ∧
      ConstructionFrame base (s.gpr .esp) s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have sizes := construction_sizes supported
  have nBounds : 4 ≤ n ∧ n ≤ 48 := by rcases sizes with h | h | h <;> omega
  have dBounds : 4 ≤ H.D ∧ H.D ≤ 32 := by rcases sizes with h | h | h <;> omega
  have dAligned : H.D % 4 = 0 := by rcases sizes with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]
  have digestFit : ((64 * n - 1) / (8 * H.D) + 1) * H.D ≤ 384 := by
    rcases sizes with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rw [h] <;> decide
  have digestRoom : 8 * n ≤ ((64 * n - 1) / (8 * H.D) + 1) * H.D := by
    rcases sizes with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rw [h] <;> decide
  have hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * H.D) bs).length = 8 * H.D := by
    intro bs; rw [digestLength]
  have candidateEq := pCandidate_shaped (by omega : 2 ≤ 64 * n) hashSize q seed offset
  unfold pConstruct
  refine WP.seq (WP.mono (p_hashes ok scr capacity room tape length pointer value small hash digestFit)
    fun a ⟨hashes, FA, KA⟩ => ?_)
  have Sa := scr.of_keeps KA (by decide)
  refine WP.seq (WP.mono (p_shape Sa capacity (by omega : 2 ≤ 8 * n) digestRoom digestFit hashes)
    fun b ⟨shaped, FB, KB⟩ => ?_)
  rw [show 8 * (8 * n) = 64 * n by omega] at shaped
  have prefixFrame : ConstructionFrame base (s.gpr .esp) s b := by
    have frameB := construction_shape_frame FB (by omega : 8 * n ≤ 384)
    rw [KA.1 .esp (by decide)] at frameB
    exact (construction_hash_frame FA).trans frameB
  have Sb := Sa.of_keeps KB (by decide)
  have prefixRegs := KA.trans KB
  have Rb : RoundRoom (b.gpr .esp) base bytes := by rw [prefixRegs.1 .esp (by decide)]; exact room
  have stackB : StkOk (b.gpr .esp - 16#32) base bytes := by rw [prefixRegs.1 .esp (by decide)]; exact stack
  refine WP.mono (p_reduce Sb capacity Rb.callRoom stackB nBounds.1 nBounds.2 dBounds.1
    (by rcases sizes with h | h | h <;> omega) dAligned shaped
    (by rw [construction_q_bytes prefixFrame capacity room dBounds.2]; exact subgroup) positive bound)
    fun t ⟨pBytes, exponentBytes, FT, KT⟩ => ?_
  rw [← candidateEq] at pBytes exponentBytes
  refine ⟨pBytes, exponentBytes, ?_, (prefixRegs.mono (by decide)).trans KT⟩
  have last := construction_reduction_frame FT nBounds.2 (by have := Rb.low; omega)
  rw [prefixRegs.1 .esp (by decide)] at last
  exact prefixFrame.trans last

end VG.Proof.Dsa.X86.Generation
