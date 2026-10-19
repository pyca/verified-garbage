module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawResult
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding

/-! Convert the right-aligned sampled scalar to the signer's nonce encoding. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

private theorem decode_padding (bs : List Byte) (n : Nat) :
    Spec.Dsa.decodeBE (List.replicate n 0 ++ bs) = Spec.Dsa.decodeBE bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, VG.Proof.Dsa.decodeBE_zero_cons]
    exact ih

theorem random_nonce_encoding {C : RandomContext} {used draws k : Nat} {s : State}
    (hr : RandomReady C used draws s) (hv : RandomNonceValue C k s) :
    Spec.Rsa.bytesAt s.mem (off C.B 200) C.qBytes.length = Spec.Dsa.encodeBE C.qBytes.length k := by
  obtain ⟨copied, hlen, hbytes, hdecode⟩ := hv
  let pad := C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1
  let padded := List.replicate pad (0 : Byte) ++ copied
  have hnfit := VG.Proof.Dsa.significant_fits C.qBytes
  have hpLen : padded.length = C.qBytes.length := by
    simp only [padded, List.length_append, List.length_replicate, hlen]
    exact Nat.sub_add_cancel hnfit
  have hpDec : Spec.Dsa.decodeBE padded = k := (decode_padding copied pad).trans hdecode
  have hpBytes : Spec.Rsa.bytesAt s.mem (off C.B 200) C.qBytes.length = padded := by
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, hpLen]
    · intro i hi hj
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      have hil : i < C.qBytes.length := by simpa only [hpLen] using hj
      by_cases hip : i < pad
      · have he : off C.B 200 + BitVec.ofNat 64 i = off C.B (200 + i) := by
          simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
        rw [he, hr.padding i hip]
        simp only [padded, List.getElem_append_left (as := List.replicate pad (0 : Byte)) (bs := copied) (i := i) (by simpa only [List.length_replicate] using hip),
          List.getElem_replicate]
      · have htail : i - pad < copied.length := by rw [hlen]; omega
        have he : off C.B 200 + BitVec.ofNat 64 i =
            off C.B (200 + C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1) +
              BitVec.ofNat 64 (i - pad) := by
          simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
          congr 2
          dsimp only [pad]
          omega
        rw [he, hbytes (i - pad) htail]
        simp only [padded, List.getElem_append_right (as := List.replicate pad (0 : Byte)) (bs := copied) (i := i) (by simpa only [List.length_replicate] using Nat.le_of_not_lt hip),
          List.length_replicate]
  rw [hpBytes, ← hpLen, ← hpDec, VG.Proof.Dsa.encodeBE_decodeBE]

end VG.Proof.Dsa.X86_64
