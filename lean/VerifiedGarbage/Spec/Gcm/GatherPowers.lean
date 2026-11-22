module

public import VerifiedGarbage.Spec.Gcm.Powers8

/-!
# AES-GCM gather sealing with eight prepared GHASH powers

AArch64 keys keep the powers apart from the AES schedule. This entry point
takes the same plaintext pieces and destination as `sealGatherApi` and can
use the powers already computed at key setup by `storePowersApi`.
-/

@[expose] public section

namespace VG.Spec.Gcm

/-- The gather signature with a read-only buffer of eight prepared powers. -/
def sealGatherWithPowersSig : Sig where
  params := sealGatherSig.params ++ [withPowersParam]

/-- The usual gather requirements and the eight powers for this key. -/
def sealGatherWithPowersPre (pb : Nat) : Curry (sealGatherWithPowersSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen src count dst len tag pw m =>
    sealGatherPre pb ctx rounds nonce nonceLen aad aadLen src count dst len tag m ∧
      Powers8Repr m pw (ctxH m ctx)

/-- GCM encryption of the concatenated pieces into the destination. -/
def sealGatherWithPowersPost (pb : Nat) : sealGatherWithPowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src count dst len tag _pw m m' r =>
    sealGatherPost pb ctx rounds nonce nonceLen aad aadLen src count dst len tag m m' r

/-- Gather sealing with the powers of the same key context. -/
def sealGatherWithPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherWithPowersSig.contract A (pre := sealGatherWithPowersPre A.ptrBits)
    (post := sealGatherWithPowersPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_gather_with_powers` on every target. -/
def sealGatherWithPowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather_with_powers"
  sig := sealGatherWithPowersSig
  writeArgs := true
  contracts := some fun A stack => sealGatherWithPowersContract A stack
  summary := withPowersSummary "vg_aes_gcm_seal_gather" "sealGatherWithPowersContract"
  safety := sealGatherApi.safety ++ [withPowersSafety]

end VG.Spec.Gcm
