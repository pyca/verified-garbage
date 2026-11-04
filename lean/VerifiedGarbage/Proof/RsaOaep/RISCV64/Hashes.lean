module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBase
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256

/-!
# RSA paddings on RISC-V: the hash functions

Untrusted: everything here is checked by Lean. The streaming functions of
SHA-1 and the SHA-2 family are constant time for the contracts the proofs
call them by (`HashCT`), from their artifacts' proofs; a hash function's
streaming functions with what RSAES-OAEP's proofs need of them (`Link`:
`HashOK`, `HashCT`, the bound on their frames, `FitsF`, and the hash
function of `Spec.Mgf1` they compute, among those the label may be hashed
with, `labelHashes`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64

/-- What the proofs need of the hash functions' streaming functions: that
their frames fit in the 208 bytes below ours. -/
abbrev FitsF (H : Hash) : Prop := H.F ≤ 208

/-- The hash functions the label is hashed with. -/
def labelHashes : List Spec.Mgf1.Hash :=
  [Spec.Mgf1.sha1, Spec.Mgf1.sha224, Spec.Mgf1.sha256, Spec.Mgf1.sha384, Spec.Mgf1.sha512, Spec.Mgf1.sha512_224,
    Spec.Mgf1.sha512_256]

/-! ## The hash functions -/

theorem ct_mono {pre pre' : State → Prop} {pub pub' : State → State → Prop} {c : Prog isa}
    (h : ConstantTime isa pre pub c) (hp : ∀ s, pre' s → pre s) (hq : ∀ s₁ s₂, pub' s₁ s₂ → pub s₁ s₂) :
    ConstantTime isa pre' pub' c :=
  fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ => h _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (hq _ _ hpub) e₁ e₂

theorem sha1CT : HashCT Sha1.ok where
  init := ct_mono Proof.Sha1.RISCV64.Stream.init_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  upd := ct_mono Proof.Sha1.RISCV64.Stream.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Sha1.RISCV64.Stream.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha256CT : HashCT Sha256Family.ok256 where
  init := ct_mono Proof.Sha256.RISCV64.Stream.init_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  upd := ct_mono Proof.Sha256.RISCV64.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Sha256.RISCV64.Stream.Finalize.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha224CT : HashCT Sha256Family.ok224 where
  init := ct_mono Proof.Sha256.RISCV64.Stream.init224_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  upd := ct_mono Proof.Sha256.RISCV64.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Sha256.RISCV64.Stream.Finalize.finalize224_verified.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha512FamilyCT (iv : Spec.Sha512.HashValue) {D : Nat} {initN finN : String} {finC : Prog isa}
    {HF : Spec.Hmac.HashFunction} {hB : HF.blockSize = 128} {hD : 0 < D ∧ D ≤ 64}
    {hinit : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith iv) (Proof.Sha512.initRISCV64 iv)}
    {hfin : Verified RISCV64.target finC (Proof.Sha512.finalizeDRISCV64 D)} {hfs : sdepth finC ≤ 208}
    {htake : ∀ x, HF.hash x = (Spec.Sha512.finalHash iv x).take D} :
    HashCT (Sha512Family.ok iv D initN finN finC HF hB hD hinit hfin hfs htake) where
  init := ct_mono hinit.2.1 (fun _ hs => hs) fun _ _ h => h
  upd := ct_mono Proof.Sha512.RISCV64.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono hfin.2.1 (fun _ hs => hs) fun _ _ h => h

theorem sha384CT : HashCT Sha384.ok := sha512FamilyCT _
theorem sha512CT : HashCT Sha512.ok := sha512FamilyCT _
theorem sha512_224CT : HashCT Sha512_224.ok := sha512FamilyCT _
theorem sha512_256CT : HashCT Sha512_256.ok := sha512FamilyCT _

/-- A hash function's streaming functions, with what the proofs need. -/
structure Link (H : Hash) where
  ok : HashOK H
  ct : HashCT ok
  fits : FitsF H
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  len : G.len = H.D
  mem : G ∈ labelHashes

theorem Link.valid {H : Hash} (l : Link H) : Proof.Mgf1.Valid l.G :=
  ⟨by rw [l.len]; exact l.ok.hD0, fun x => by rw [l.hash, l.ok.hashLen, l.len]⟩

def sha1L : Link Sha1.hash :=
  ⟨Sha1.ok, sha1CT, by decide, Spec.Mgf1.sha1, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha224L : Link Sha256Family.hash224 :=
  ⟨Sha256Family.ok224, sha224CT, by decide, Spec.Mgf1.sha224, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha256L : Link Sha256Family.hash256 :=
  ⟨Sha256Family.ok256, sha256CT, by decide, Spec.Mgf1.sha256, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha384L : Link Sha384.hash :=
  ⟨Sha384.ok, sha384CT, by decide, Spec.Mgf1.sha384, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha512L : Link Sha512.hash :=
  ⟨Sha512.ok, sha512CT, by decide, Spec.Mgf1.sha512, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha512_224L : Link Sha512_224.hash :=
  ⟨Sha512_224.ok, sha512_224CT, by decide, Spec.Mgf1.sha512_224, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha512_256L : Link Sha512_256.hash :=
  ⟨Sha512_256.ok, sha512_256CT, by decide, Spec.Mgf1.sha512_256, fun _ => rfl, rfl, by simp [labelHashes]⟩

end VG.Proof.RsaOaep.RISCV64
