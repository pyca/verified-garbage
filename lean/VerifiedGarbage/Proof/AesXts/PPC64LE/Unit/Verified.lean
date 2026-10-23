module

public import VerifiedGarbage.Impl.AesXts.PPC64LEUnit
public import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Contract
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.CT
import VerifiedGarbage.Proof.AesXts.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Dec

/-!
# XTS-AES of data units on PPC64LE: `Verified`

`vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit` meet `unitPPC64LE`
(`encrypt_wp`, `decrypt_wp`, `encrypt_ct`, `decrypt_ct`), from the
whole-block functions' proofs (`Proof/AesXts/PPC64LE/Verified.lean`), and
so the shared contracts of `Spec/Xts/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LEUnit

theorem encrypt_correct (s : State) (hs : (unitPPC64LE true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (unitPPC64LE true).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hlr⟩, hp⟩ := encrypt_wp (UPre.of hs) Proof.AesXts.PPC64LE.encrypt_correct
    Proof.AesXts.PPC64LE.encrypt_noFrames
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (unitPPC64LE false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (unitPPC64LE false).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hlr⟩, hp⟩ := decrypt_wp (UPre.of hs) Proof.AesXts.PPC64LE.encrypt_correct
    Proof.AesXts.PPC64LE.encrypt_noFrames Proof.AesXts.PPC64LE.decrypt_correct
    Proof.AesXts.PPC64LE.decrypt_noFrames
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at `0x5000`. -/
def unitSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 10 | .r6 => 0x3000 | .r7 => 0x4000 | .r8 => 16 | .r9 => 0x5000
    | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x4000, 16⟩, ⟨0x5000, 2432⟩]

theorem encrypt_verified : Verified PPC64LE.target encrypt (Spec.Xts.aesEncryptUnitContract PPC64LE.abi) :=
  Verified.of_correct encrypt_correct
    (encrypt_ct Proof.AesXts.PPC64LE.encrypt_correct Proof.AesXts.PPC64LE.encrypt_noFrames
      Proof.AesXts.PPC64LE.encrypt_ct) (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitPPC64LE, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, PPC64LE.abi, PPC64LE.argRegs] [unitSat] using unitSat)

theorem decrypt_verified : Verified PPC64LE.target decrypt (Spec.Xts.aesDecryptUnitContract PPC64LE.abi) :=
  Verified.of_correct decrypt_correct
    (decrypt_ct Proof.AesXts.PPC64LE.encrypt_correct Proof.AesXts.PPC64LE.encrypt_noFrames
      Proof.AesXts.PPC64LE.encrypt_ct Proof.AesXts.PPC64LE.decrypt_correct Proof.AesXts.PPC64LE.decrypt_noFrames
      Proof.AesXts.PPC64LE.decrypt_ct) (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitPPC64LE, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, PPC64LE.abi, PPC64LE.argRegs] [unitSat] using unitSat)

end VG.Proof.AesXts.PPC64LE.Unit
