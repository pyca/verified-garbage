module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256

/-!
# RSAES-OAEP encryption on PPC64LE: the hash functions' constant time

Untrusted: everything here is checked by Lean. The streaming functions of
SHA-1 and the SHA-2 family (`Proof/Hmac/Stream/PPC64LE/`) are constant time
for the contracts the proofs call them by (`HashCT`), from their artifacts'
proofs.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE

theorem ct_mono {pre pre' : State → Prop} {pub pub' : State → State → Prop} {c : Prog isa}
    (h : ConstantTime isa pre pub c) (hp : ∀ s, pre' s → pre s) (hq : ∀ s₁ s₂, pub' s₁ s₂ → pub s₁ s₂) :
    ConstantTime isa pre' pub' c :=
  fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ => h _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (hq _ _ hpub) e₁ e₂

theorem sha1CT : HashCT Sha1.ok where
  init := ct_mono Proof.Sha1.PPC64LE.Stream.init_verified.2.1 (fun _ hs => ⟨hs.1, hs.2.1⟩) fun _ _ h => h
  upd := ct_mono Proof.Sha1.PPC64LE.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Sha1.PPC64LE.Stream.Finalize.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha256CT : HashCT Sha256.ok where
  init := ct_mono Proof.Sha256.PPC64LE.Stream.init_verified.2.1 (fun _ hs => ⟨hs.1, hs.2.1⟩) fun _ _ h => h
  upd := ct_mono Proof.Sha256.PPC64LE.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Sha256.PPC64LE.Stream.Finalize.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha224CT : HashCT Sha224.ok where
  init := ct_mono Proof.Sha256.PPC64LE.Stream.init224_verified.2.1 (fun _ hs => ⟨hs.1, hs.2.1⟩) fun _ _ h => h
  upd := ct_mono Proof.Sha256.PPC64LE.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Sha256.PPC64LE.Stream.Finalize.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha512FamilyCT (iv : Spec.Sha512.HashValue) {D : Nat} {initN hmacInitN : String}
    (hok : HashOK (Sha512Family.hash iv D initN hmacInitN)) : HashCT hok where
  init := ct_mono (Proof.Sha512.PPC64LE.Stream.init_verified iv).2.1 (fun _ hs => ⟨hs.1, hs.2.1⟩) fun _ _ h => h
  upd := ct_mono Proof.Sha512.PPC64LE.Stream.Update.update_verified.2.1
    (fun _ hs => ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩) fun _ _ h => h
  fin := ct_mono Proof.Sha512.PPC64LE.Stream.Finalize.finalize_verified.2.1
    (fun _ hs => ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩) fun _ _ h => h

theorem sha384CT : HashCT Sha384.ok := sha512FamilyCT _ _
theorem sha512CT : HashCT Sha512.ok := sha512FamilyCT _ _
theorem sha512_224CT : HashCT Sha512_224.ok := sha512FamilyCT _ _
theorem sha512_256CT : HashCT Sha512_256.ok := sha512FamilyCT _ _

end VG.Proof.RsaOaep.PPC64LE
