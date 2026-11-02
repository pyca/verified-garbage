module

import VerifiedGarbage.Proof.RsaPss.RISCV64.CTMain
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
public import VerifiedGarbage.Spec.RsaPss.Precomputed

/-!
# RSASSA-PSS verification on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Verified.lean`, `Inst.lean`): constant time
(`code_constantTime`, from `code_ct`, with the contract's public data as
`PubP`); a state meeting the precondition for each hash function the other
targets verify with (`verify_sat`); MD5's streaming functions constant time
for the contracts the proofs call them by (`md5CT`), as SHA-1's and the SHA-2
family's are (`Proof/RsaOaep/RISCV64/Verified.lean`); and a hash function's
streaming functions with what the proofs need of them (`Link`), for which
`link_verified` is verification, which the registration files bind.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64
open VG.Proof.RsaOaep.RISCV64 (HashCT FitsF stackBytes ct_mono sha1CT sha224CT sha256CT sha384CT sha512CT
  sha512_224CT sha512_256CT)

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs)
include cH hF hGh hGl hGv

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi stackBytes).pre
      (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi stackBytes).pub (verifyPrecomputed H) :=
  RelCT.constantTime ((code_ct hH cH hF hGh hGl hGv).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preP_of h₁, pubP_refl s₁, by have := (preP_of h₁).k1; exact Nat.le_trans (by decide) this⟩,
      preP_of h₂, pubP_of hp, by have := (preP_of h₂).k1; exact Nat.le_trans (by decide) this⟩) fun _ _ h => h)

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed` against its shared contract,
given a state meeting it. -/
theorem verify_verified (hsat : ∃ s, (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi stackBytes).pre s) :
    Verified RISCV64.target (verifyPrecomputed H) (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi stackBytes) :=
  ⟨code_correct hH hF hGh hGl hGv, code_constantTime hH cH hF hGh hGl hGv, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting verification's contract for `H`: a 512-bit modulus, a
one-byte `e`, `H`'s digest, a 64-byte signature, a working space of 2080
words, 16 words of `pre` at `0x5000`, and the stack arguments at `sp`. -/
def verifySatState (H : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .a0 => 0x2000 | .a1 => 64 | .a2 => 0x3000 | .a3 => 1 | .a4 => 0x4200 | .a5 => 0x4000 | .a6 => 64
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x1000A then 0x02
    else bif Nat.beq a.toNat 0x10010 then 0x20 else bif Nat.beq a.toNat 0x10011 then 0x08
    else bif Nat.beq a.toNat 0x10019 then 0x50 else bif Nat.beq a.toNat 0x10020 then 16 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, H.len⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x10000, 40⟩]
  wr := [⟨0x20000, 16640⟩]

/-- The hash functions verification uses, as on the other targets. -/
def pssHashes : List Spec.Mgf1.Hash :=
  [Spec.Mgf1.md5, Spec.Mgf1.sha1, Spec.Mgf1.sha224, Spec.Mgf1.sha256, Spec.Mgf1.sha384, Spec.Mgf1.sha512,
    Spec.Mgf1.sha512_224, Spec.Mgf1.sha512_256]

theorem verify_sat {H : Spec.Mgf1.Hash} (hH : H ∈ pssHashes) :
    ∃ s, (Spec.RsaPss.verifyPrecomputedContract H H abi stackBytes).pre s := by
  simp only [pssHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.md5
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha512_256

/-! ## The hash functions -/

theorem md5CT : HashCT Md5.ok where
  init := ct_mono Proof.Md5.RISCV64.Stream.init_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  upd := ct_mono Proof.Md5.RISCV64.Stream.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Md5.RISCV64.Stream.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

/-- A hash function's streaming functions, with what the proofs need. -/
structure Link (H : Hash) where
  ok : HashOK H
  ct : HashCT ok
  fits : FitsF H
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  len : G.len = H.D
  mem : G ∈ pssHashes

theorem Link.valid {H : Hash} (l : Link H) : Proof.Mgf1.Valid l.G :=
  ⟨by rw [l.len]; exact l.ok.hD0, fun x => by rw [l.hash, l.ok.hashLen, l.len]⟩

def md5L : Link Md5.hash :=
  ⟨Md5.ok, md5CT, by decide, Spec.Mgf1.md5, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha1L : Link Sha1.hash :=
  ⟨Sha1.ok, sha1CT, by decide, Spec.Mgf1.sha1, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha224L : Link Sha256Family.hash224 :=
  ⟨Sha256Family.ok224, sha224CT, by decide, Spec.Mgf1.sha224, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha256L : Link Sha256Family.hash256 :=
  ⟨Sha256Family.ok256, sha256CT, by decide, Spec.Mgf1.sha256, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha384L : Link Sha384.hash :=
  ⟨Sha384.ok, sha384CT, by decide, Spec.Mgf1.sha384, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha512L : Link Sha512.hash :=
  ⟨Sha512.ok, sha512CT, by decide, Spec.Mgf1.sha512, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha512_224L : Link Sha512_224.hash :=
  ⟨Sha512_224.ok, sha512_224CT, by decide, Spec.Mgf1.sha512_224, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha512_256L : Link Sha512_256.hash :=
  ⟨Sha512_256.ok, sha512_256CT, by decide, Spec.Mgf1.sha512_256, fun _ => rfl, rfl, by simp [pssHashes]⟩

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed` for a linked hash function. -/
theorem link_verified {H : Hash} (l : Link H) :
    Verified RISCV64.target (Impl.RsaPss.RISCV64.verifyPrecomputed H)
      (Spec.RsaPss.verifyPrecomputedContract l.G l.G abi stackBytes) :=
  verify_verified l.ok l.ct l.fits l.hash l.len l.valid (verify_sat l.mem)

end VG.Proof.RsaPss.RISCV64
