module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecSel
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint

/-!
# RSAES-PKCS1-v1_5 decryption on x86: the body

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecBody.lean`): the pieces in order,
each correct and constant time (`body_vp`), from the state the body starts
from to the result (`Fin`); and no instruction of the body or of the
functions it calls writes `esp` (`body_noSp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Pbkdf2.Whole.X86 (sha256OKF)

variable {P : EP}

/-! ## The private-key operation and `D` -/

theorem privArgs_vp : VP (S P) (.block privArgs) (R1 P) :=
  VP.taint [.esp] privArgs_taint (sp_agree fun _ _ h => h) fun _ _ h => privArgs_wp h

theorem dZero_vp : VP (R2 P) (.block (saveR ++ dZero)) (D1 P) :=
  VP.taint [.esp] dZero_taint (sp_agree fun _ _ h => h.1) fun _ _ h => dZero_wp h

theorem zero_vp : VP (D1 P) zeroLoop (D2 P) :=
  VP.taint [.esi, .ecx] zeroLoop_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]) fun _ _ h => zero_wp h

theorem dCopy_vp : VP (D2 P) (.block dCopy) (D3 P) :=
  VP.taint [.esp] dCopy_taint (sp_agree fun _ _ h => h.1.1) fun _ _ h => dCopy_wp h

theorem copy_vp : VP (D3 P) Impl.Bignum.X86.copyBytes (D4 P) :=
  VP.taint [.esi, .ebx, .ecx] copyBytes_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) fun _ _ h => copy_wp h

/-! ## `KDK` -/

theorem kdkMac_vp (v : Backend) : VP (H6 P) (kdkMac v.F) (K6 P) :=
  kdkInitArgs_vp.seq ((kdkInit_vp v).seq (kdkUpdArgs_vp.seq ((kdkUpd_vp v).seq (kdkFinArgs_vp.seq
    (kdkFin_vp v)))))

/-! ## The padding and the output -/

theorem validBlock_vp : VP (SCQ P) (.block validBlock) (VB P) := by
  have := validHead_vp.block_append (validRest_vp (P := P))
  rwa [List.take_append_drop] at this

theorem mlStore_vp : VP (VB P) (.block mlStore) (VW P) := by
  have := mlHead_vp.block_append (mlRest_vp (P := P))
  rwa [List.take_append_drop] at this

theorem selPart_vp : VP (AL P) selPart (Fin P) :=
  scanInit_vp.seq (scanLoop_vp.seq (validBlock_vp.seq (mlStore_vp.seq (selInit_vp.seq (selLoop_vp.seq
    finR_vp)))))

/-! ## The body -/

theorem body_vp (v : Backend) (c : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (S P) (body v.F (privName c) (Proof.Rsa.X86.PrivChecked.privCode c)) (Fin P) :=
  privArgs_vp.seq ((call_vp c).seq (dZero_vp.seq (zero_vp.seq (dCopy_vp.seq (copy_vp.seq ((hashD_vp v).seq
    ((kdkMac_vp v).seq ((clLoop_vp v).seq ((amLoop_vp v).seq (alPart_vp.seq selPart_vp))))))))))

theorem prfBody_noSp (v : Backend) {label : List Nat} {len : List Instr} {dst : Nat}
    (hm : NoSp (.block (msgPtr ++ msgBytes label len) : Prog isa))
    (hu : NoSp (.block (prfUpdArgs (label.length + 4)) : Prog isa))
    (hf : NoSp (.block (prfFinArgs (label.length + 4) dst) : Prog isa)) :
    NoSp (prfBody v.F label len dst) :=
  noSp_seq hm (noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_pushCall (sha256OKF v).hiSp)
    (noSp_seq hu (noSp_seq (noSp_pushCall (hk v).updSp) (noSp_seq hf (noSp_seq (noSp_pushCall (sha256OKF v).hfSp)
      (.of_all (by decide +kernel))))))))

theorem body_noSp (v : Backend) (c : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    NoSp (body v.F (privName c) (Proof.Rsa.X86.PrivChecked.privCode c)) := by
  refine noSp_seq (.of_all (by decide +kernel))
    (noSp_seq (noSp_call (Proof.Rsa.X86.PrivChecked.privateCode_noSp c)) ?_)
  refine noSp_seq (.of_all (by decide +kernel)) (noSp_seq (.of_all (by decide +kernel)) ?_)
  refine noSp_seq (.of_all (by decide +kernel)) (noSp_seq (.of_all (by decide +kernel)) ?_)
  refine noSp_seq ?_ (noSp_seq ?_ (noSp_seq ?_ (noSp_seq ?_
    (noSp_seq (.of_all (by decide +kernel)) (.of_all (by decide +kernel))))))
  · exact noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_pushCall (hk v).initSp)
      (noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_pushCall (hk v).updSp)
      (noSp_seq (.of_all (by decide +kernel)) (noSp_pushCall (hk v).finSp)))))
  · exact noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_pushCall (sha256OKF v).hiSp)
      (noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_pushCall (hk v).updSp)
      (noSp_seq (.of_all (by decide +kernel)) (noSp_pushCall (sha256OKF v).hfSp)))))
  · exact noSp_seq (.of_all (by decide +kernel)) (noSp_loop (prfBody_noSp v (.of_all (by decide +kernel))
      (.of_all (by decide +kernel)) (.of_all (by decide +kernel))))
  · exact noSp_seq (.of_all (by decide +kernel)) (noSp_loop (prfBody_noSp v (.of_all (by decide +kernel))
      (.of_all (by decide +kernel)) (.of_all (by decide +kernel))))

end VG.Proof.RsaPkcs1Enc.X86.Dec
