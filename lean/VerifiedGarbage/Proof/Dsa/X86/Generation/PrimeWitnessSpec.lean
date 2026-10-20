module
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeDrawRound

/-! # Whole-limb witness draws agree with the shared RSA sampler -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.Mont VG.Proof.RsaKeyGen

theorem primeTape_segment (m : Mem) (p : Addr) {a n k : Nat} (h : a + n ≤ k) :
    seg (Spec.Rsa.bytesAt m p k) a n = Spec.Rsa.bytesAt m (off p a) n := by
  unfold seg Spec.Rsa.bytesAt
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range, off]
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem PrimeConfig.witnessBytes (G : PrimeConfig) : Spec.RsaKeyGen.witnessBytes G.modulus = G.draw := by
  unfold Spec.RsaKeyGen.witnessBytes
  rw [G.predecessorBits]
  unfold PrimeConfig.draw PrimeConfig.n
  omega

theorem primeDrawValue_spec {G : PrimeConfig} (mem : Mem) {used : Nat} (full : used + G.draw ≤ G.tapeLen) :
    primeDrawValue G mem used = Spec.RsaKeyGen.witness (G.modulus - 1)
      (Spec.Rsa.os2ip (seg (Spec.Rsa.bytesAt mem (G.tape.setWidth 64) G.tapeLen) used G.draw)) := by
  have enough : G.len ≤ G.draw := by unfold PrimeConfig.draw PrimeConfig.n; omega
  rw [primeTape_segment _ _ full]
  rw [show G.draw = (G.draw - G.len) + G.len by omega,
    VG.Proof.Dsa.Generation.bytesAt_append]
  rw [VG.Proof.Dsa.Generation.witness_drop_padding _ _ (by
    simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using G.predecessorBits)]
  simp only [primeDrawValue, off, Offset.add_add]
  rfl
end VG.Proof.Dsa.X86.Generation
