module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResiduePrime
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Convert public big-endian candidate octets to the shared reducer's backward reads. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

theorem trialBuffers_of_octets {s : State} {dst prime : BitVec 32} {n : Nat} {xs : List Byte}
    (h : ReadContext dst n s) (length : xs.length = n)
    (bytes : Spec.Rsa.bytesAt s.mem (State.addr dst) n = xs) :
    TrialBuffers ⟨dst, n, prime, xs.reverse⟩ s := by
  refine ⟨h, ?_⟩
  intro i hi
  change i < n at hi
  change s.mem (State.addr (dst + BitVec.ofNat 32 n - BitVec.ofNat 32 (i + 1))) = xs.reverse[i]?.getD 0
  rw [List.getElem?_reverse (by omega), length]
  have index : n - 1 - i = n - (i + 1) := by omega
  rw [index, VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega),
    VG.Arm.addr_add (by have := h.bufferFits; omega)]
  have value := congrArg (fun bs : List Byte => bs[n - (i + 1)]?.getD 0) bytes
  simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range (by omega : n - (i + 1) < n),
    Option.map_some, Option.getD_some] using value

end VG.Proof.Ffdh.Arm.ParameterCandidate
