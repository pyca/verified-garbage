module

import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Update
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Finalize
public import VerifiedGarbage.Proof.Sha256.Scratch
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.Reloc
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Init
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Update
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Finalize
meta import VerifiedGarbage.Proof.Sha256.Scratch
meta import VerifiedGarbage.Spec.Sha256.Contract
meta import VerifiedGarbage.Proof.Hmac.Stream.Reloc
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash

/-!
# SHA-256's streaming functions, for the code over any streaming hash function

SHA-256's streaming functions as the code over any streaming hash function
calls them (`hash`), and what the proofs need of them (`ok`): PBKDF2's
`iterate` uses them. (HMAC-SHA-256 keeps its own PPC64LE code.)
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Sha256

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

/-- SHA-256's streaming functions. -/
def hash : Hash where
  B := 64
  N := 32
  D := 32
  FD := 32
  W := 160
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.PPC64LE.Stream.init
  updN := Spec.Sha256.updateScratchApi.name
  updC := Impl.Sha256.PPC64LE.Stream.update
  finN := Spec.Sha256.finalizeScratchApi.name
  finC := Impl.Sha256.PPC64LE.Stream.finalize
  hmacInitN := Spec.Hmac.sha256I.initScratchApi.name

/-- What the proofs need of them. -/
def ok : HashOK hash where
  SH := Spec.Hmac.sha256S
  hS := rfl
  hD := rfl
  hB := rfl
  dims := ⟨by decide, by decide, by decide, by decide⟩
  hN4 := by decide
  hD0 := by decide
  hDB := by decide
  hD4 := by decide
  hDF := by decide
  hFD64 := by decide
  fh := Spec.Sha256.finalHash Spec.Sha256.H0
  init s hs := Proof.Sha256.PPC64LE.Stream.init_verified.1 s ⟨hs.1, hs.2.1⟩
  upd s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha256.PPC64LE.Stream.Update.update_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr hc => h _ m hr hc⟩
  fin s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha256.PPC64LE.Stream.Finalize.finalize_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr _ hc => h _ m hr hc⟩
  initFd := by decide +kernel
  updFd := by decide +kernel
  finFd := by decide +kernel
  initPf := by decide +kernel
  updPf := by decide +kernel
  finPf := by decide +kernel
  reloc m m' p q x hx h hr := Proof.Hmac.Stream.sha256_reloc _ m m' p q x hx h hr
  congr _ _ _ _ h hr := Proof.Sha256.reprFrom_congr (fun i hi => h i hi) hr
  fhLen x := Proof.Sha256.PPC64LE.Stream.Finalize.finalHash_length _ x
  hashTake x := (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.PPC64LE.Stream.Finalize.finalHash_length _ x))).symm

end VG.Proof.Hmac.Stream.PPC64LE.Sha256
