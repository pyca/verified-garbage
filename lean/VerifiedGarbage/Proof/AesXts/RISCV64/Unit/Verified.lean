module

public import VerifiedGarbage.Impl.AesXts.RISCV64Unit
public import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Contract
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.CT
import VerifiedGarbage.Proof.AesXts.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Dec

/-!
# XTS-AES of data units on RISC-V: `Verified`

`vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit` meet `unitRISCV64`
(`encrypt_wp`, `decrypt_wp`, `encrypt_ct`, `decrypt_ct`), from the
whole-block functions' proofs (`Proof/AesXts/RISCV64/Verified.lean`), and
so the shared contracts of `Spec/Xts/Contract.lean`, as on PPC64LE
(`Proof/AesXts/PPC64LE/Unit/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.Impl.AesXts.RISCV64Unit

theorem encrypt_correct (s : State) (hs : (unitRISCV64 true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (unitRISCV64 true).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hra⟩, hp⟩ := encrypt_wp (UPre.of hs) Proof.AesXts.RISCV64.encrypt_correct
    Proof.AesXts.RISCV64.encrypt_noFrames
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (unitRISCV64 false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (unitRISCV64 false).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hra⟩, hp⟩ := decrypt_wp (UPre.of hs) Proof.AesXts.RISCV64.encrypt_correct
    Proof.AesXts.RISCV64.encrypt_noFrames Proof.AesXts.RISCV64.decrypt_correct
    Proof.AesXts.RISCV64.decrypt_noFrames
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at `0x5000`. -/
def unitSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 10 | .a3 => 0x3000 | .a4 => 0x4000 | .a5 => 16 | .a6 => 0x5000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x4000, 16⟩, ⟨0x5000, 2432⟩]

theorem encrypt_verified : Verified RISCV64.target encrypt (Spec.Xts.aesEncryptUnitContract RISCV64.abi) :=
  Verified.of_correct encrypt_correct
    (encrypt_ct Proof.AesXts.RISCV64.encrypt_correct Proof.AesXts.RISCV64.encrypt_noFrames
      Proof.AesXts.RISCV64.encrypt_ct) (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitRISCV64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, RISCV64.abi, RISCV64.argRegs] [unitSat] using unitSat)

theorem decrypt_verified : Verified RISCV64.target decrypt (Spec.Xts.aesDecryptUnitContract RISCV64.abi) :=
  Verified.of_correct decrypt_correct
    (decrypt_ct Proof.AesXts.RISCV64.encrypt_correct Proof.AesXts.RISCV64.encrypt_noFrames
      Proof.AesXts.RISCV64.encrypt_ct Proof.AesXts.RISCV64.decrypt_correct Proof.AesXts.RISCV64.decrypt_noFrames
      Proof.AesXts.RISCV64.decrypt_ct) (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitRISCV64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, RISCV64.abi, RISCV64.argRegs] [unitSat] using unitSat)

end VG.Proof.AesXts.RISCV64.Unit
