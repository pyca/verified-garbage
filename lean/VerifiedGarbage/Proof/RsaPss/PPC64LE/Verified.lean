module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTMain
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Post
public import VerifiedGarbage.Spec.RsaPss.Precomputed

/-!
# RSASSA-PSS verification on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Constant time
(`code_constantTime`, from `code_ct`, with the contract's public data as
`PubP`); a state meeting the precondition for each hash function the other
targets verify with (`verify_sat`); and `verify_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (HashCT)

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs)
include cH hGh hGl hGv

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi 304).pre
      (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi 304).pub (verifyPrecomputed H) :=
  RelCT.constantTime ((code_ct hH cH hGh hGl hGv).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preP_of h₁, pubP_refl s₁, by have := (preP_of h₁).k1; exact Nat.le_trans (by decide) this⟩,
      preP_of h₂, pubP_of hp, by have := (preP_of h₂).k1; exact Nat.le_trans (by decide) this⟩) fun _ _ h => h)

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed` against its shared contract,
given a state meeting it. -/
theorem verify_verified (hsat : ∃ s, (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi 304).pre s) :
    Verified PPC64LE.target (verifyPrecomputed H) (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi 304) :=
  ⟨code_correct hH hGh hGl hGv, code_constantTime hH cH hGh hGl hGv, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting verification's contract for `H`: a 512-bit modulus, a
one-byte `e`, `H`'s digest, a 64-byte signature, a working space of 2080
words, 16 words of `pre` at `0x5000`, and the stack arguments at `sp + 96`. -/
def verifySatState (H : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .r3 => 0x2000 | .r4 => 64 | .r5 => 0x3000 | .r6 => 1 | .r7 => 0x4200 | .r8 => 0x4000 | .r9 => 64
    | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x1006A then 0x02
    else bif Nat.beq a.toNat 0x10070 then 0x20 else bif Nat.beq a.toNat 0x10071 then 0x08
    else bif Nat.beq a.toNat 0x10079 then 0x50 else bif Nat.beq a.toNat 0x10080 then 16 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, H.len⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x10060, 40⟩]
  wr := [⟨0x20000, 16640⟩]

/-- The hash functions verification uses, as on the other targets. -/
def pssHashes : List Spec.Mgf1.Hash :=
  [Spec.Mgf1.md5, Spec.Mgf1.sha1, Spec.Mgf1.sha224, Spec.Mgf1.sha256, Spec.Mgf1.sha384, Spec.Mgf1.sha512,
    Spec.Mgf1.sha512_224, Spec.Mgf1.sha512_256]

theorem verify_sat {H : Spec.Mgf1.Hash} (hH : H ∈ pssHashes) :
    ∃ s, (Spec.RsaPss.verifyPrecomputedContract H H abi 304).pre s := by
  simp only [pssHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.md5
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha512_256

end VG.Proof.RsaPss.PPC64LE
