module

import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Spec.Ed25519
public import VerifiedGarbage.TCB.Artifact

/-! # The reduced challenge, zero-extended

`verify`'s challenge, `SHA-512(R ‖ A ‖ M) mod L` as 64 bytes, is the 32 bytes
`scalarReduce` writes followed by 32 zero bytes (`reduced_challenge`), as code
that zeroes the upper half after `scalar_reduce` computes it. -/

@[expose] public section

namespace VG.Proof.Ed25519

private theorem encodeLE_eq (n x : Nat) : Spec.Ed25519.encodeLE n x = Proof.X25519.leBytes n x := by
  unfold Spec.Ed25519.encodeLE Proof.X25519.leBytes
  apply congrArg (List.map · (List.range n))
  funext i
  rw [Nat.shiftRight_eq_div_pow, show 256 ^ i = 2 ^ (8 * i) by rw [Nat.pow_mul]]

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

end VG.Proof.Ed25519
