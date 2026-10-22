module

public import VerifiedGarbage.Proof.RsaPss.X86.SgBase
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS signing on x86: the contract is satisfiable

A state that meets `signContract` (`sign_sat_<hash>`), for each hash function
x86 registers RSASSA-PSS with: a modulus of 64 bytes, `e`, `p`, `q`, `dP`,
`dQ` and `qInv` of one byte, an empty salt, the working space it needs, and
the arguments above `esp = 0x20000`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

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
  mem a := if a = 131077 then 0x10 else if a = 131080 then 0x40 else if a = 131085 then 0x20 else
    if a = 131088 then 0x40 else if a = 131093 then 0x21 else if a = 131096 then 0x1 else
    if a = 131101 then 0x31 else if a = 131104 then 0x1 else if a = 131109 then 0x32 else
    if a = 131112 then 0x1 else if a = 131117 then 0x33 else if a = 131120 then 0x1 else
    if a = 131125 then 0x34 else if a = 131128 then 0x1 else if a = 131133 then 0x35 else
    if a = 131136 then 0x1 else if a = 131141 then 0x30 else if a = 131145 then 0x36 else
    if a = 131154 then 0x1 else if a = 131156 then 0x20 else if a = 131157 then 0x8 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3000, D⟩, ⟨0x3600, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩, ⟨0x20004, 84⟩]

theorem sign_sat_md5 : ∃ s, (spec Spec.Mgf1.md5).pre s := by
  have a0 : arg (satState 16) 0 = 0x1000 := by decide
  have a1 : arg (satState 16) 1 = 64 := by decide
  have a2 : arg (satState 16) 2 = 0x2000 := by decide
  have a3 : arg (satState 16) 3 = 64 := by decide
  have a4 : arg (satState 16) 4 = 0x2100 := by decide
  have a5 : arg (satState 16) 5 = 1 := by decide
  have a6 : arg (satState 16) 6 = 0x3100 := by decide
  have a7 : arg (satState 16) 7 = 1 := by decide
  have a8 : arg (satState 16) 8 = 0x3200 := by decide
  have a9 : arg (satState 16) 9 = 1 := by decide
  have a10 : arg (satState 16) 10 = 0x3300 := by decide
  have a11 : arg (satState 16) 11 = 1 := by decide
  have a12 : arg (satState 16) 12 = 0x3400 := by decide
  have a13 : arg (satState 16) 13 = 1 := by decide
  have a14 : arg (satState 16) 14 = 0x3500 := by decide
  have a15 : arg (satState 16) 15 = 1 := by decide
  have a16 : arg (satState 16) 16 = 0x3000 := by decide
  have a17 : arg (satState 16) 17 = 0x3600 := by decide
  have a18 : arg (satState 16) 18 = 0 := by decide
  have a19 : arg (satState 16) 19 = 0x10000 := by decide
  have a20 : arg (satState 16) 20 = 0x820 := by decide
  have e : argAddr (satState 16) 0 = 0x20004 := by decide
  have esp : (satState 16).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 16

theorem sign_sat_sha1 : ∃ s, (spec Spec.Mgf1.sha1).pre s := by
  have a0 : arg (satState 20) 0 = 0x1000 := by decide
  have a1 : arg (satState 20) 1 = 64 := by decide
  have a2 : arg (satState 20) 2 = 0x2000 := by decide
  have a3 : arg (satState 20) 3 = 64 := by decide
  have a4 : arg (satState 20) 4 = 0x2100 := by decide
  have a5 : arg (satState 20) 5 = 1 := by decide
  have a6 : arg (satState 20) 6 = 0x3100 := by decide
  have a7 : arg (satState 20) 7 = 1 := by decide
  have a8 : arg (satState 20) 8 = 0x3200 := by decide
  have a9 : arg (satState 20) 9 = 1 := by decide
  have a10 : arg (satState 20) 10 = 0x3300 := by decide
  have a11 : arg (satState 20) 11 = 1 := by decide
  have a12 : arg (satState 20) 12 = 0x3400 := by decide
  have a13 : arg (satState 20) 13 = 1 := by decide
  have a14 : arg (satState 20) 14 = 0x3500 := by decide
  have a15 : arg (satState 20) 15 = 1 := by decide
  have a16 : arg (satState 20) 16 = 0x3000 := by decide
  have a17 : arg (satState 20) 17 = 0x3600 := by decide
  have a18 : arg (satState 20) 18 = 0 := by decide
  have a19 : arg (satState 20) 19 = 0x10000 := by decide
  have a20 : arg (satState 20) 20 = 0x820 := by decide
  have e : argAddr (satState 20) 0 = 0x20004 := by decide
  have esp : (satState 20).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 20

theorem sign_sat_sha224 : ∃ s, (spec Spec.Mgf1.sha224).pre s := by
  have a0 : arg (satState 28) 0 = 0x1000 := by decide
  have a1 : arg (satState 28) 1 = 64 := by decide
  have a2 : arg (satState 28) 2 = 0x2000 := by decide
  have a3 : arg (satState 28) 3 = 64 := by decide
  have a4 : arg (satState 28) 4 = 0x2100 := by decide
  have a5 : arg (satState 28) 5 = 1 := by decide
  have a6 : arg (satState 28) 6 = 0x3100 := by decide
  have a7 : arg (satState 28) 7 = 1 := by decide
  have a8 : arg (satState 28) 8 = 0x3200 := by decide
  have a9 : arg (satState 28) 9 = 1 := by decide
  have a10 : arg (satState 28) 10 = 0x3300 := by decide
  have a11 : arg (satState 28) 11 = 1 := by decide
  have a12 : arg (satState 28) 12 = 0x3400 := by decide
  have a13 : arg (satState 28) 13 = 1 := by decide
  have a14 : arg (satState 28) 14 = 0x3500 := by decide
  have a15 : arg (satState 28) 15 = 1 := by decide
  have a16 : arg (satState 28) 16 = 0x3000 := by decide
  have a17 : arg (satState 28) 17 = 0x3600 := by decide
  have a18 : arg (satState 28) 18 = 0 := by decide
  have a19 : arg (satState 28) 19 = 0x10000 := by decide
  have a20 : arg (satState 28) 20 = 0x820 := by decide
  have e : argAddr (satState 28) 0 = 0x20004 := by decide
  have esp : (satState 28).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 28

theorem sign_sat_sha256 : ∃ s, (spec Spec.Mgf1.sha256).pre s := by
  have a0 : arg (satState 32) 0 = 0x1000 := by decide
  have a1 : arg (satState 32) 1 = 64 := by decide
  have a2 : arg (satState 32) 2 = 0x2000 := by decide
  have a3 : arg (satState 32) 3 = 64 := by decide
  have a4 : arg (satState 32) 4 = 0x2100 := by decide
  have a5 : arg (satState 32) 5 = 1 := by decide
  have a6 : arg (satState 32) 6 = 0x3100 := by decide
  have a7 : arg (satState 32) 7 = 1 := by decide
  have a8 : arg (satState 32) 8 = 0x3200 := by decide
  have a9 : arg (satState 32) 9 = 1 := by decide
  have a10 : arg (satState 32) 10 = 0x3300 := by decide
  have a11 : arg (satState 32) 11 = 1 := by decide
  have a12 : arg (satState 32) 12 = 0x3400 := by decide
  have a13 : arg (satState 32) 13 = 1 := by decide
  have a14 : arg (satState 32) 14 = 0x3500 := by decide
  have a15 : arg (satState 32) 15 = 1 := by decide
  have a16 : arg (satState 32) 16 = 0x3000 := by decide
  have a17 : arg (satState 32) 17 = 0x3600 := by decide
  have a18 : arg (satState 32) 18 = 0 := by decide
  have a19 : arg (satState 32) 19 = 0x10000 := by decide
  have a20 : arg (satState 32) 20 = 0x820 := by decide
  have e : argAddr (satState 32) 0 = 0x20004 := by decide
  have esp : (satState 32).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 32

theorem sign_sat_sha384 : ∃ s, (spec Spec.Mgf1.sha384).pre s := by
  have a0 : arg (satState 48) 0 = 0x1000 := by decide
  have a1 : arg (satState 48) 1 = 64 := by decide
  have a2 : arg (satState 48) 2 = 0x2000 := by decide
  have a3 : arg (satState 48) 3 = 64 := by decide
  have a4 : arg (satState 48) 4 = 0x2100 := by decide
  have a5 : arg (satState 48) 5 = 1 := by decide
  have a6 : arg (satState 48) 6 = 0x3100 := by decide
  have a7 : arg (satState 48) 7 = 1 := by decide
  have a8 : arg (satState 48) 8 = 0x3200 := by decide
  have a9 : arg (satState 48) 9 = 1 := by decide
  have a10 : arg (satState 48) 10 = 0x3300 := by decide
  have a11 : arg (satState 48) 11 = 1 := by decide
  have a12 : arg (satState 48) 12 = 0x3400 := by decide
  have a13 : arg (satState 48) 13 = 1 := by decide
  have a14 : arg (satState 48) 14 = 0x3500 := by decide
  have a15 : arg (satState 48) 15 = 1 := by decide
  have a16 : arg (satState 48) 16 = 0x3000 := by decide
  have a17 : arg (satState 48) 17 = 0x3600 := by decide
  have a18 : arg (satState 48) 18 = 0 := by decide
  have a19 : arg (satState 48) 19 = 0x10000 := by decide
  have a20 : arg (satState 48) 20 = 0x820 := by decide
  have e : argAddr (satState 48) 0 = 0x20004 := by decide
  have esp : (satState 48).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 48

theorem sign_sat_sha512 : ∃ s, (spec Spec.Mgf1.sha512).pre s := by
  have a0 : arg (satState 64) 0 = 0x1000 := by decide
  have a1 : arg (satState 64) 1 = 64 := by decide
  have a2 : arg (satState 64) 2 = 0x2000 := by decide
  have a3 : arg (satState 64) 3 = 64 := by decide
  have a4 : arg (satState 64) 4 = 0x2100 := by decide
  have a5 : arg (satState 64) 5 = 1 := by decide
  have a6 : arg (satState 64) 6 = 0x3100 := by decide
  have a7 : arg (satState 64) 7 = 1 := by decide
  have a8 : arg (satState 64) 8 = 0x3200 := by decide
  have a9 : arg (satState 64) 9 = 1 := by decide
  have a10 : arg (satState 64) 10 = 0x3300 := by decide
  have a11 : arg (satState 64) 11 = 1 := by decide
  have a12 : arg (satState 64) 12 = 0x3400 := by decide
  have a13 : arg (satState 64) 13 = 1 := by decide
  have a14 : arg (satState 64) 14 = 0x3500 := by decide
  have a15 : arg (satState 64) 15 = 1 := by decide
  have a16 : arg (satState 64) 16 = 0x3000 := by decide
  have a17 : arg (satState 64) 17 = 0x3600 := by decide
  have a18 : arg (satState 64) 18 = 0 := by decide
  have a19 : arg (satState 64) 19 = 0x10000 := by decide
  have a20 : arg (satState 64) 20 = 0x820 := by decide
  have e : argAddr (satState 64) 0 = 0x20004 := by decide
  have esp : (satState 64).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 64

theorem sign_sat_sha512_224 : ∃ s, (spec Spec.Mgf1.sha512_224).pre s := by
  have a0 : arg (satState 28) 0 = 0x1000 := by decide
  have a1 : arg (satState 28) 1 = 64 := by decide
  have a2 : arg (satState 28) 2 = 0x2000 := by decide
  have a3 : arg (satState 28) 3 = 64 := by decide
  have a4 : arg (satState 28) 4 = 0x2100 := by decide
  have a5 : arg (satState 28) 5 = 1 := by decide
  have a6 : arg (satState 28) 6 = 0x3100 := by decide
  have a7 : arg (satState 28) 7 = 1 := by decide
  have a8 : arg (satState 28) 8 = 0x3200 := by decide
  have a9 : arg (satState 28) 9 = 1 := by decide
  have a10 : arg (satState 28) 10 = 0x3300 := by decide
  have a11 : arg (satState 28) 11 = 1 := by decide
  have a12 : arg (satState 28) 12 = 0x3400 := by decide
  have a13 : arg (satState 28) 13 = 1 := by decide
  have a14 : arg (satState 28) 14 = 0x3500 := by decide
  have a15 : arg (satState 28) 15 = 1 := by decide
  have a16 : arg (satState 28) 16 = 0x3000 := by decide
  have a17 : arg (satState 28) 17 = 0x3600 := by decide
  have a18 : arg (satState 28) 18 = 0 := by decide
  have a19 : arg (satState 28) 19 = 0x10000 := by decide
  have a20 : arg (satState 28) 20 = 0x820 := by decide
  have e : argAddr (satState 28) 0 = 0x20004 := by decide
  have esp : (satState 28).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 28

theorem sign_sat_sha512_256 : ∃ s, (spec Spec.Mgf1.sha512_256).pre s := by
  have a0 : arg (satState 32) 0 = 0x1000 := by decide
  have a1 : arg (satState 32) 1 = 64 := by decide
  have a2 : arg (satState 32) 2 = 0x2000 := by decide
  have a3 : arg (satState 32) 3 = 64 := by decide
  have a4 : arg (satState 32) 4 = 0x2100 := by decide
  have a5 : arg (satState 32) 5 = 1 := by decide
  have a6 : arg (satState 32) 6 = 0x3100 := by decide
  have a7 : arg (satState 32) 7 = 1 := by decide
  have a8 : arg (satState 32) 8 = 0x3200 := by decide
  have a9 : arg (satState 32) 9 = 1 := by decide
  have a10 : arg (satState 32) 10 = 0x3300 := by decide
  have a11 : arg (satState 32) 11 = 1 := by decide
  have a12 : arg (satState 32) 12 = 0x3400 := by decide
  have a13 : arg (satState 32) 13 = 1 := by decide
  have a14 : arg (satState 32) 14 = 0x3500 := by decide
  have a15 : arg (satState 32) 15 = 1 := by decide
  have a16 : arg (satState 32) 16 = 0x3000 := by decide
  have a17 : arg (satState 32) 17 = 0x3600 := by decide
  have a18 : arg (satState 32) 18 = 0 := by decide
  have a19 : arg (satState 32) 19 = 0x10000 := by decide
  have a20 : arg (satState 32) 20 = 0x820 := by decide
  have e : argAddr (satState 32) 0 = 0x20004 := by decide
  have esp : (satState 32).gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 32

end VG.Proof.RsaPss.X86.Sg
