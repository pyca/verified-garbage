module

import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCCt
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
public import VerifiedGarbage.Spec.RsaPss.Precomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTop

/-!
# RSASSA-PSS verification on AArch64, calling `checkEncoding`: `Verified`

The shared contract (`Spec.RsaPss.verifyPrecomputedContract`, with the stack
of the frame and of the deeper callee, `stk K`) from correctness
(`code_ok`), constant time (`code_ct`) and a state meeting the precondition
(`verify_sat`, for the stack of `checkEncoding`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.RsaPkcs1Sig.AArch64.Pc (stackArgs_five)
open VG.Proof.Pbkdf2.Md.AArch64 (mdHashes)
open VG.Proof.RsaPss.AArch64 (ChkImpl)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

section
variable {G : Spec.Mgf1.Hash} (c : PdChecked) (e : ChkImpl G) {K : Nat} (hcK : c.stack ≤ K) (heK : e.stack ≤ K)

include hcK heK in
theorem code_correct (s : State) (h : (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)).pre s) :
    ∃ t s', Exec isa (verifyC e.name e.code c.name c.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c e hcK heK (preV_of G h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  exact hr

include hcK heK in
theorem code_constantTime :
    ConstantTime isa (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)).pre
      (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)).pub (verifyC e.name e.code c.name c.code) :=
  RelCT.constantTime ((code_ct c e hcK heK).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preV_of G h₁, PubV.refl s₁⟩, preV_of G h₂, pubV_of G hp⟩) fun _ _ h => h)

include hcK heK in
theorem code_verified (hsat : ∃ s, (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)).pre s) :
    Verified AArch64.target (verifyC e.name e.code c.name c.code)
      (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)) :=
  ⟨code_correct c e hcK heK, code_constantTime c e hcK heK, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A 512-bit modulus, a one-byte `e`, the digest and the signature, a
working space of 2048 words, 16 precomputed words, and the stack pointer at
`2^40`, far above them. -/
def satState (G : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | .x5 => 0x4000 | .x6 => 64
    | _ => 0
  sp := 0x10000000000
  mem a := if a = 0x10000000010 then 0x20
    else if a = 0x1000000000A then 1 else if a = 0x10000000011 then 8
    else if a = 0x10000000019 then 0x50 else if a = 0x10000000020 then 16 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, G.len⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x10000000000, 40⟩]
  wr := [⟨0x10000, 2080 * 8⟩]

/-- `verifyPrecomputedContract` is satisfiable for each of `MdHash`'s hash
functions, with the stack of the frame and the 352 bytes of
`checkEncoding`'s. -/
theorem verify_sat {G : Spec.Mgf1.Hash} (hG : G ∈ mdHashes) :
    ∃ s, (Spec.RsaPss.verifyPrecomputedContract G G abi (stk 352)).pre s := by
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract,
      Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, stk, frameBytes, stackArgs_five, List.append_eq]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.md5
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract,
      Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, stk, frameBytes, stackArgs_five, List.append_eq]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract,
      Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, stk, frameBytes, stackArgs_five, List.append_eq]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract,
      Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, stk, frameBytes, stackArgs_five, List.append_eq]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract,
      Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, stk, frameBytes, stackArgs_five, List.append_eq]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract,
      Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, stk, frameBytes, stackArgs_five, List.append_eq]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract,
      Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, stk, frameBytes, stackArgs_five, List.append_eq]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract,
      Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, stk, frameBytes, stackArgs_five, List.append_eq]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512_256

end VG.Proof.RsaPss.AArch64.Vfy
