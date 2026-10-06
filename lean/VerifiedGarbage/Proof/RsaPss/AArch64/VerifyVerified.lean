import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS verification on AArch64: `Verified`

The shared contract (`Spec.RsaPss.verifyPrecomputedContract`, with the stack
of the frame and the callee, `stk`) from correctness (`code_ok`), constant
time (`code_ct`) and a state meeting the precondition (`verify_sat`, for the
stack of the precomputed public operation).
-/

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.RsaPkcs1Sig.AArch64.Pc (stackArgs_five)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK mdHashes)
open VG.Proof.RsaPss.AArch64 (PssChecks)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

section
variable {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
  (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G) (hc : PssChecks H.P H.D) (c : PdChecked) {K : Nat}
  (hK : 16 ≤ K) (hcK : c.stack ≤ K)

include hH hGh hGl hG hK hcK in
theorem code_correct (s : State) (h : (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)).pre s) :
    ∃ t s', Exec isa (verifyPrecomputed H c.name c.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)).post s s' := by
  have hp := preV_of G h
  rw [hGl] at hp
  obtain ⟨t, s', he, habi, hr⟩ := code_ok hH hGh hGl hG c hK hcK hp
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  exact hr

include hH hGh hGl hG hc hK hcK in
theorem code_constantTime :
    ConstantTime isa (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)).pre
      (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)).pub (verifyPrecomputed H c.name c.code) :=
  RelCT.constantTime ((code_ct hH hGh hGl hG hc c hK hcK).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨hGl ▸ preV_of G h₁, PubV.refl s₁⟩, hGl ▸ preV_of G h₂, pubV_of G hp⟩) fun _ _ h => h)

include hH hGh hGl hG hc hK hcK in
theorem code_verified (hsat : ∃ s, (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)).pre s) :
    Verified AArch64.target (verifyPrecomputed H c.name c.code)
      (Spec.RsaPss.verifyPrecomputedContract G G abi (stk K)) :=
  ⟨code_correct hH hGh hGl hG c hK hcK, code_constantTime hH hGh hGl hG hc c hK hcK, hsat⟩

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
  mem a := if a = 0x1000000000A then 1 else if a = 0x10000000011 then 8
    else if a = 0x10000000019 then 0x50 else if a = 0x10000000020 then 16 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, G.len⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x10000000000, 40⟩]
  wr := [⟨0x10000, 2048 * 8⟩]

/-- `verifyPrecomputedContract` is satisfiable for each of `MdHash`'s hash
functions, with the stack of the frame and 16 bytes for the callee and the
hash function's calls. -/
theorem verify_sat {G : Spec.Mgf1.Hash} (hG : G ∈ mdHashes) :
    ∃ s, (Spec.RsaPss.verifyPrecomputedContract G G abi (stk 16)).pre s := by
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
