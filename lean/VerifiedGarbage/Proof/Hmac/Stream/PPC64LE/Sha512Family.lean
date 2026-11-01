module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Update
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Finalize
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.Reloc
public import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha512.Stream

/-!
# HMAC over the SHA-512 family on PPC64LE

The streaming functions of SHA-384, SHA-512, SHA-512/224 and SHA-512/256 as
HMAC's code over any streaming hash function calls them (`hash`): the hash
function's `init` (from its initial hash value `iv`), and SHA-512's `update`
and `finalize`, which writes the whole final hash value (64 bytes), whose
first `D` bytes are the digest; and what the proofs need of them (`ok`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Sha512Family

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open Spec.Sha512 (HashValue)

/-- The streaming functions of the hash function with initial hash value
`iv` (whose `init` is `initN`) and a digest of `D` bytes, for HMAC's `init`
named `hmacInitN`. -/
def hash (iv : HashValue) (D : Nat) (initN hmacInitN : String) : Hash where
  B := 128
  N := 64
  D := D
  FD := 64
  W := 224
  initN := initN
  initC := Impl.Sha512.PPC64LE.Stream.init iv
  updN := "vg_sha512_update_scratch"
  updC := Impl.Sha512.PPC64LE.Stream.update
  finN := "vg_sha512_finalize_scratch"
  finC := Impl.Sha512.PPC64LE.Stream.finalize
  hmacInitN := hmacInitN

theorem updFd : Impl.Sha512.PPC64LE.Stream.update.fdepth ≤ 1 := by decide +kernel
theorem finFd : Impl.Sha512.PPC64LE.Stream.finalize.fdepth ≤ 1 := by decide +kernel
theorem updPf : pushFrames Impl.Sha512.PPC64LE.Stream.update = true := by decide +kernel
theorem finPf : pushFrames Impl.Sha512.PPC64LE.Stream.finalize = true := by decide +kernel

/-- What the proofs need of them, for a hash function `HF` of SHA-512's block
whose digest is the first `D` bytes of the final hash value from `iv`. -/
def ok (iv : HashValue) (D : Nat) (initN hmacInitN : String) (HF : Spec.Hmac.HashFunction)
    (hB : HF.blockSize = 128) (hD : 0 < D ∧ D % 4 = 0 ∧ D ≤ 64)
    (htake : ∀ x, HF.hash x = (Spec.Sha512.finalHash iv x).take D) :
    HashOK (hash iv D initN hmacInitN) where
  SH := ⟨HF, 192, D, Spec.Sha512.Repr iv⟩
  hS := rfl
  hD := rfl
  hB := hB
  dims := ⟨by simp [hash], by simp [hash], by simp [hash],
    by simp [hash, Hash.lsv, Hash.ldg, Hash.lst, Hash.S]⟩
  hN4 := by simp [hash]
  hD0 := hD.1
  hDB := by show D ≤ 128; omega
  hD4 := hD.2.1
  hDF := hD.2.2
  hFD64 := by simp [hash]
  fh := Spec.Sha512.finalHash iv
  init s hs := Proof.Sha512.PPC64LE.Stream.init_verified iv |>.1 s ⟨hs.1, hs.2.1⟩
  upd s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha512.PPC64LE.Stream.Update.update_verified.1 s
      ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
    exact ⟨t, s', he, ha, fun m hr hc => h iv m hr hc⟩
  fin s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha512.PPC64LE.Stream.Finalize.finalize_verified.1 s
      ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
    exact ⟨t, s', he, ha, fun m hr hl hc => h iv m hr hl hc⟩
  initFd := Nat.zero_le _
  updFd := updFd
  finFd := finFd
  initPf := rfl
  updPf := updPf
  finPf := finPf
  reloc m m' p q x hx h hr := Proof.Hmac.Stream.sha512_reloc iv m m' p q x hx h hr
  congr _ _ _ _ h hr := Proof.Sha512.Stream.repr_congr (fun i hi => h i hi) hr
  fhLen x := Proof.Hmac.Generic.Common.finalHash_length _ x
  hashTake := htake

end VG.Proof.Hmac.Stream.PPC64LE.Sha512Family
