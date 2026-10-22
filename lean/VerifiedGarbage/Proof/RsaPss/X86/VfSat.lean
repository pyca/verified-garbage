module

public import VerifiedGarbage.Proof.RsaPss.X86.VfBase
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the contract is satisfiable

A state that meets `verifyPrecomputedContract` (`verify_sat_<hash>`), for
each hash function x86 registers RSASSA-PSS with: a modulus of 64 bytes, `e`
of one byte, a signature of 64 bytes, the working space it needs, the
precomputed values' 16 words, and the arguments above `esp = 0x20000`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes)

/-- The state, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 0x20 else if a = 131080 then 0x40 else if a = 131085 then 0x21 else
    if a = 131088 then 0x1 else if a = 131093 then 0x30 else if a = 131097 then 0x31 else
    if a = 131100 then 0x40 else if a = 131114 then 0x1 else if a = 131116 then 0x20 else
    if a = 131117 then 0x8 else if a = 131121 then 0x70 else if a = 131124 then 0x10 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, D⟩, ⟨0x3100, 64⟩, ⟨0x7000, 128⟩]
  wr := [⟨0x10000, 2080 * 8⟩, ⟨0x20004, 52⟩]

theorem verify_sat_md5 : ∃ s, (spec Spec.Mgf1.md5).pre s := by
  have a0 : arg (satState 16) 0 = 0x2000 := by decide
  have a1 : arg (satState 16) 1 = 64 := by decide
  have a2 : arg (satState 16) 2 = 0x2100 := by decide
  have a3 : arg (satState 16) 3 = 1 := by decide
  have a4 : arg (satState 16) 4 = 0x3000 := by decide
  have a5 : arg (satState 16) 5 = 0x3100 := by decide
  have a6 : arg (satState 16) 6 = 64 := by decide
  have a7 : arg (satState 16) 7 = 0 := by decide
  have a8 : arg (satState 16) 8 = 0 := by decide
  have a9 : arg (satState 16) 9 = 0x10000 := by decide
  have a10 : arg (satState 16) 10 = 0x820 := by decide
  have a11 : arg (satState 16) 11 = 0x7000 := by decide
  have a12 : arg (satState 16) 12 = 16 := by decide
  have e : argAddr (satState 16) 0 = 0x20004 := by decide
  have esp : (satState 16).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState 16

theorem verify_sat_sha1 : ∃ s, (spec Spec.Mgf1.sha1).pre s := by
  have a0 : arg (satState 20) 0 = 0x2000 := by decide
  have a1 : arg (satState 20) 1 = 64 := by decide
  have a2 : arg (satState 20) 2 = 0x2100 := by decide
  have a3 : arg (satState 20) 3 = 1 := by decide
  have a4 : arg (satState 20) 4 = 0x3000 := by decide
  have a5 : arg (satState 20) 5 = 0x3100 := by decide
  have a6 : arg (satState 20) 6 = 64 := by decide
  have a7 : arg (satState 20) 7 = 0 := by decide
  have a8 : arg (satState 20) 8 = 0 := by decide
  have a9 : arg (satState 20) 9 = 0x10000 := by decide
  have a10 : arg (satState 20) 10 = 0x820 := by decide
  have a11 : arg (satState 20) 11 = 0x7000 := by decide
  have a12 : arg (satState 20) 12 = 16 := by decide
  have e : argAddr (satState 20) 0 = 0x20004 := by decide
  have esp : (satState 20).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState 20

theorem verify_sat_sha224 : ∃ s, (spec Spec.Mgf1.sha224).pre s := by
  have a0 : arg (satState 28) 0 = 0x2000 := by decide
  have a1 : arg (satState 28) 1 = 64 := by decide
  have a2 : arg (satState 28) 2 = 0x2100 := by decide
  have a3 : arg (satState 28) 3 = 1 := by decide
  have a4 : arg (satState 28) 4 = 0x3000 := by decide
  have a5 : arg (satState 28) 5 = 0x3100 := by decide
  have a6 : arg (satState 28) 6 = 64 := by decide
  have a7 : arg (satState 28) 7 = 0 := by decide
  have a8 : arg (satState 28) 8 = 0 := by decide
  have a9 : arg (satState 28) 9 = 0x10000 := by decide
  have a10 : arg (satState 28) 10 = 0x820 := by decide
  have a11 : arg (satState 28) 11 = 0x7000 := by decide
  have a12 : arg (satState 28) 12 = 16 := by decide
  have e : argAddr (satState 28) 0 = 0x20004 := by decide
  have esp : (satState 28).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState 28

theorem verify_sat_sha256 : ∃ s, (spec Spec.Mgf1.sha256).pre s := by
  have a0 : arg (satState 32) 0 = 0x2000 := by decide
  have a1 : arg (satState 32) 1 = 64 := by decide
  have a2 : arg (satState 32) 2 = 0x2100 := by decide
  have a3 : arg (satState 32) 3 = 1 := by decide
  have a4 : arg (satState 32) 4 = 0x3000 := by decide
  have a5 : arg (satState 32) 5 = 0x3100 := by decide
  have a6 : arg (satState 32) 6 = 64 := by decide
  have a7 : arg (satState 32) 7 = 0 := by decide
  have a8 : arg (satState 32) 8 = 0 := by decide
  have a9 : arg (satState 32) 9 = 0x10000 := by decide
  have a10 : arg (satState 32) 10 = 0x820 := by decide
  have a11 : arg (satState 32) 11 = 0x7000 := by decide
  have a12 : arg (satState 32) 12 = 16 := by decide
  have e : argAddr (satState 32) 0 = 0x20004 := by decide
  have esp : (satState 32).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState 32

theorem verify_sat_sha384 : ∃ s, (spec Spec.Mgf1.sha384).pre s := by
  have a0 : arg (satState 48) 0 = 0x2000 := by decide
  have a1 : arg (satState 48) 1 = 64 := by decide
  have a2 : arg (satState 48) 2 = 0x2100 := by decide
  have a3 : arg (satState 48) 3 = 1 := by decide
  have a4 : arg (satState 48) 4 = 0x3000 := by decide
  have a5 : arg (satState 48) 5 = 0x3100 := by decide
  have a6 : arg (satState 48) 6 = 64 := by decide
  have a7 : arg (satState 48) 7 = 0 := by decide
  have a8 : arg (satState 48) 8 = 0 := by decide
  have a9 : arg (satState 48) 9 = 0x10000 := by decide
  have a10 : arg (satState 48) 10 = 0x820 := by decide
  have a11 : arg (satState 48) 11 = 0x7000 := by decide
  have a12 : arg (satState 48) 12 = 16 := by decide
  have e : argAddr (satState 48) 0 = 0x20004 := by decide
  have esp : (satState 48).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState 48

theorem verify_sat_sha512 : ∃ s, (spec Spec.Mgf1.sha512).pre s := by
  have a0 : arg (satState 64) 0 = 0x2000 := by decide
  have a1 : arg (satState 64) 1 = 64 := by decide
  have a2 : arg (satState 64) 2 = 0x2100 := by decide
  have a3 : arg (satState 64) 3 = 1 := by decide
  have a4 : arg (satState 64) 4 = 0x3000 := by decide
  have a5 : arg (satState 64) 5 = 0x3100 := by decide
  have a6 : arg (satState 64) 6 = 64 := by decide
  have a7 : arg (satState 64) 7 = 0 := by decide
  have a8 : arg (satState 64) 8 = 0 := by decide
  have a9 : arg (satState 64) 9 = 0x10000 := by decide
  have a10 : arg (satState 64) 10 = 0x820 := by decide
  have a11 : arg (satState 64) 11 = 0x7000 := by decide
  have a12 : arg (satState 64) 12 = 16 := by decide
  have e : argAddr (satState 64) 0 = 0x20004 := by decide
  have esp : (satState 64).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState 64

theorem verify_sat_sha512_224 : ∃ s, (spec Spec.Mgf1.sha512_224).pre s := by
  have a0 : arg (satState 28) 0 = 0x2000 := by decide
  have a1 : arg (satState 28) 1 = 64 := by decide
  have a2 : arg (satState 28) 2 = 0x2100 := by decide
  have a3 : arg (satState 28) 3 = 1 := by decide
  have a4 : arg (satState 28) 4 = 0x3000 := by decide
  have a5 : arg (satState 28) 5 = 0x3100 := by decide
  have a6 : arg (satState 28) 6 = 64 := by decide
  have a7 : arg (satState 28) 7 = 0 := by decide
  have a8 : arg (satState 28) 8 = 0 := by decide
  have a9 : arg (satState 28) 9 = 0x10000 := by decide
  have a10 : arg (satState 28) 10 = 0x820 := by decide
  have a11 : arg (satState 28) 11 = 0x7000 := by decide
  have a12 : arg (satState 28) 12 = 16 := by decide
  have e : argAddr (satState 28) 0 = 0x20004 := by decide
  have esp : (satState 28).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState 28

theorem verify_sat_sha512_256 : ∃ s, (spec Spec.Mgf1.sha512_256).pre s := by
  have a0 : arg (satState 32) 0 = 0x2000 := by decide
  have a1 : arg (satState 32) 1 = 64 := by decide
  have a2 : arg (satState 32) 2 = 0x2100 := by decide
  have a3 : arg (satState 32) 3 = 1 := by decide
  have a4 : arg (satState 32) 4 = 0x3000 := by decide
  have a5 : arg (satState 32) 5 = 0x3100 := by decide
  have a6 : arg (satState 32) 6 = 64 := by decide
  have a7 : arg (satState 32) 7 = 0 := by decide
  have a8 : arg (satState 32) 8 = 0 := by decide
  have a9 : arg (satState 32) 9 = 0x10000 := by decide
  have a10 : arg (satState 32) 10 = 0x820 := by decide
  have a11 : arg (satState 32) 11 = 0x7000 := by decide
  have a12 : arg (satState 32) 12 = 16 := by decide
  have e : argAddr (satState 32) 0 = 0x20004 := by decide
  have esp : (satState 32).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState 32

end VG.Proof.RsaPss.X86.Vf
