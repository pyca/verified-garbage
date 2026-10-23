module

public import VerifiedGarbage.Proof.Modes.Cbc
public import VerifiedGarbage.Proof.Modes.Fb

/-! # Original ciphertext supplies every independent CFB-decryption input -/

@[expose] public section
namespace VG.Proof.Modes.AArch64.CfbDec
open VG VG.Proof.Modes

/-- CFB decryption's input chain is CBC's preceding original ciphertext. -/
theorem input_eq (L : Nat) (cipher : Spec.Cbc.Cipher) (m : Mem) (D : Addr)
    (iv : List Byte) (j : Nat) :
    fbIn .cfbDec L cipher m D iv j = cbcPrev L m D iv j := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [fbIn,fbStep,cbcPrev,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel]

theorem output_eq (L : Nat) (cipher : Spec.Cbc.Cipher) (m : Mem) (D : Addr)
    (iv : List Byte) (j : Nat) :
    fbOut .cfbDec L cipher m D iv j =
      Spec.Cbc.xor (Spec.Aes.bytesAt m (D+BitVec.ofNat 64 (L*j)) L)
        (cipher (cbcPrev L m D iv j)) := by
  rw [fbOut,input_eq]

/-- A completed byte invariant gives the public CFB-decryption result. -/
theorem of_dinv {L : Nat} {cipher : Spec.Cbc.Cipher}
    (hc : ∀ b, (cipher b).length = L) {m₀ m : Mem} {D : Addr} {n : Nat} {iv : List Byte}
    (h : DInv L m₀ m D n n (fbOut .cfbDec L cipher m₀ D iv)) :
    blocksOf L m D n = Spec.Cfb.decrypt cipher iv (blocksOf L m₀ D n) := by
  rw [blocksOf_of_dinv (fun j => fbOut_length hc m₀ D iv j) h]
  exact (cfbDec_of L cipher m₀ D iv n).1

end VG.Proof.Modes.AArch64.CfbDec
