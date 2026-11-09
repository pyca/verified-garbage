module

import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.Wychelean
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! # Byte-adapter and axiom checks for the Wychelean contracts -/

namespace VG.Test.X25519Wychelean

open VG.Spec.X25519

/-- The adapter preserves every byte, including bit 255. Masking belongs
to Wychelean, not to the memory adapter. -/
example (m : Mem) (p : Addr) : outputBytes (inputAt m p) = bytesAt m p 32 := by
  apply List.ext_getElem
  · simp [outputBytes, bytesAt]
  · intro i hi hj
    simp [outputBytes, inputAt, bytesAt] at hi hj ⊢

example (v : Vector UInt8 32) : (outputBytes v).length = 32 := by
  simp [outputBytes]

example (v : Vector UInt8 32) :
    outputBytes v = List.replicate 32 0 ↔ v = Vector.replicate 32 0 := by
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    have e := List.getElem_of_eq h (by simpa [outputBytes] using hi)
    simp only [outputBytes, List.getElem_map, Vector.getElem_toList,
      List.getElem_replicate] at e
    simp only [Vector.getElem_replicate]
    apply UInt8.toBitVec_inj.mp
    simpa only [UInt8.toBitVec_ofNat, BitVec.ofNat_eq_ofNat] using e
  · rintro rfl
    simp [outputBytes]

#assert_standard_axioms VG.Proof.X25519.Wychelean.x25519_eq_wychelean
#assert_standard_axioms VG.Proof.X25519.Wychelean.exchangeContract_ladder
#assert_standard_axioms VG.Proof.X25519.Wychelean.baseContract_ladder
#assert_standard_axioms VG.Spec.X25519.x25519BaseContract
#assert_standard_axioms VG.Spec.X25519.exchangeContract

end VG.Test.X25519Wychelean
