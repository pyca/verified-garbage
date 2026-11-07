module

public import VerifiedGarbage.Proof.Modes.Cbc
public import VerifiedGarbage.Proof.Modes.Fb

/-!
# CFB decryption's input blocks are the preceding ciphertext blocks

`input_eq`: CFB decryption's input block `j` is CBC's chaining value, the
preceding ciphertext block (or the IV), so that every input block is known
before any block is decrypted, as the batched decryptions use
(`Proof/Modes/<ISA>/CfbDec/`). `of_dinv`: their data loop's invariant, when
done, gives the specification's result.
-/

@[expose] public section
namespace VG.Proof.Modes.CfbDec
open VG VG.Proof.Modes

/-- CFB decryption's input chain is CBC's preceding original ciphertext. -/
theorem input_eq (L : Nat) (cipher : Spec.Cbc.Cipher) (m : Mem) (D : Addr)
    (iv : List Byte) (j : Nat) :
    fbIn .cfbDec L cipher m D iv j = cbcPrev L m D iv j := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [fbIn,fbStep,cbcPrev,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel]

/-- A completed byte invariant gives the public CFB-decryption result. -/
theorem of_dinv {L : Nat} {cipher : Spec.Cbc.Cipher}
    (hc : ∀ b, (cipher b).length = L) {m₀ m : Mem} {D : Addr} {n : Nat} {iv : List Byte}
    (h : DInv L m₀ m D n n (fbOut .cfbDec L cipher m₀ D iv)) :
    blocksOf L m D n = Spec.Cfb.decrypt cipher iv (blocksOf L m₀ D n) := by
  rw [blocksOf_of_dinv (fun j => fbOut_length hc m₀ D iv j) h]
  exact (cfbDec_of L cipher m₀ D iv n).1

end VG.Proof.Modes.CfbDec
