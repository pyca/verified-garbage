module

import VerifiedGarbage.Proof.AesXts.AArch64.Unit.CT
public import VerifiedGarbage.Proof.AesXts.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesCbc.AArch64.Call
public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Contract
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Dec
import VerifiedGarbage.Proof.AesXts.AArch64.CT

/-!
# XTS-AES of data units on AArch64: `Verified`

Correctness (`encrypt_wp`, `decrypt_wp`) and constant time (`encrypt_ct`,
`decrypt_ct`) for any implementation `v` of the whole-block functions
(`XtsImpl`), a state satisfying the precondition (`unitSat`), and the shared
contracts of `Spec/Xts/Contract.lean`, with no stack: the calls keep the
return address in `x30`, which the functions save in the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64 VG.Impl.AesXts.AArch64Unit
open VG.Proof.AesXts.AArch64 (XtsImpl)

theorem encrypt_keepsV (v : XtsImpl) : (encrypt v.enc).allInstrs keepsV = true := by
  simp only [encrypt, tweak, encSteal, swap, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem decrypt_keepsV (v : XtsImpl) : (decrypt v.enc v.dec).allInstrs keepsV = true := by
  simp only [decrypt, tweak, decSteal, swap, Code.allInstrs, v.encKeepsV, v.decKeepsV]; decide +kernel

theorem encrypt_correct (v : XtsImpl) (s : State) (hs : (unitAArch64 true).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (unitAArch64 true).post s s' :=
  WP.withPreservedV (encrypt_wp (UPre.of hs) v.encOk v.encNoFrames) (encrypt_keepsV v)

theorem decrypt_correct (v : XtsImpl) (s : State) (hs : (unitAArch64 false).pre s) :
    ∃ t s', Exec isa (decrypt v.enc v.dec) s t s' ∧ abiPreserved s s' ∧ (unitAArch64 false).post s s' :=
  WP.withPreservedV (decrypt_wp (UPre.of hs) v.encOk v.encNoFrames v.decOk v.decNoFrames) (decrypt_keepsV v)

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at `0x5000`. -/
def unitSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 10 | .x3 => 0x3000 | .x4 => 0x4000 | .x5 => 16 | .x6 => 0x5000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x4000, 16⟩, ⟨0x5000, 2432⟩]

theorem encrypt_verified (v : XtsImpl) :
    Verified AArch64.target (encrypt v.enc) (Spec.Xts.aesEncryptUnitContract AArch64.abi) :=
  Verified.of_correct (encrypt_correct v) (encrypt_ct v.encOk v.encNoFrames v.encCt) (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitAArch64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, AArch64.abi, AArch64.argRegs] [unitSat] using unitSat)

theorem decrypt_verified (v : XtsImpl) :
    Verified AArch64.target (decrypt v.enc v.dec) (Spec.Xts.aesDecryptUnitContract AArch64.abi) :=
  Verified.of_correct (decrypt_correct v)
    (decrypt_ct v.encOk v.encNoFrames v.encCt v.decOk v.decNoFrames v.decCt) (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitAArch64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, AArch64.abi, AArch64.argRegs] [unitSat] using unitSat)

end VG.Proof.AesXts.AArch64.Unit
