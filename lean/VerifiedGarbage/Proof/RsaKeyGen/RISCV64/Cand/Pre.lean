module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract
meta import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract

/-!
# A candidate on RISC-V: the contract's arguments

`CIn s`: the shared contract's precondition (`Proof.RsaKeyGen.candidateContract`,
with the `stackBytes` of stack of the frame and the round's), without the
table of small primes, as the proof uses it (`cin_of_pre`): `(out, out_len,
used, e, e_len, p, p_len, rand)` in `a0`–`a7`, and `rand_len`, `scratch` and
`scratch_len` the stack arguments 0–2. The readable regions are stated by
membership, so that `CIn` also holds with the constants' regions after them.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64

/-- The stack the code uses: its frame of 192 bytes and the round's of 96. -/
def stackBytes : Nat := 288

/-- The arguments' regions. -/
abbrev cO (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev cU (s : State) : Region := ⟨s.gpr .a2, 8⟩
abbrev cE (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
abbrev cP (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
abbrev cR (s : State) : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
abbrev cS (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
abbrev cA (s : State) : Region := ⟨stackArgAddr s 0, 24⟩
/-- The stack the code uses: its frame and the round's. -/
abbrev cF (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 288, 288⟩

/-- The contract's precondition. -/
structure CIn (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  spLo : 288 ≤ s.sp.toNat
  spHi : s.sp.toNat + 24 ≤ 2 ^ 64
  rE : cE s ∈ s.rd
  rP : cP s ∈ s.rd
  rR : cR s ∈ s.rd
  rA : cA s ∈ s.rd
  wr : s.wr = [cO s, cU s, cS s]
  oU : (cO s).Disjoint (cU s)
  oE : (cO s).Disjoint (cE s)
  oP : (cO s).Disjoint (cP s)
  oR : (cO s).Disjoint (cR s)
  oS : (cO s).Disjoint (cS s)
  oA : (cO s).Disjoint (cA s)
  uE : (cU s).Disjoint (cE s)
  uP : (cU s).Disjoint (cP s)
  uR : (cU s).Disjoint (cR s)
  uS : (cU s).Disjoint (cS s)
  uA : (cU s).Disjoint (cA s)
  eS : (cE s).Disjoint (cS s)
  pS : (cP s).Disjoint (cS s)
  rS : (cR s).Disjoint (cS s)
  SA : (cS s).Disjoint (cA s)
  Fo : (cF s).Disjoint (cO s)
  Fu : (cF s).Disjoint (cU s)
  Fe : (cF s).Disjoint (cE s)
  Fp : (cF s).Disjoint (cP s)
  Fr : (cF s).Disjoint (cR s)
  FS : (cF s).Disjoint (cS s)
  FA : (cF s).Disjoint (cA s)
  fo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  fu : (s.gpr .a2).toNat + 8 ≤ 2 ^ 64
  fe : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  fp : (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64
  fr : (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  fS : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  valid : Spec.RsaKeyGen.primeLenValid (s.gpr .a1).toNat
  el1 : 1 ≤ (s.gpr .a4).toNat
  el2 : (s.gpr .a4).toNat ≤ 8
  plv : (s.gpr .a6).toNat = 0 ∨ (s.gpr .a6).toNat = (s.gpr .a1).toNat
  scr : Spec.Rsa.scratchWords (s.gpr .a1).toNat ≤ (stackArg s 2).toNat
  alU : (s.gpr .a2).toNat % 8 = 0
  alS : (stackArg s 1).toNat % 8 = 0

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem cin_of_pre (s : State) (h : (Proof.RsaKeyGen.candidateContract RISCV64.abi stackBytes).pre s) :
    CIn s := by
  have e : stackBytes = 287 + 1 := rfl
  rw [e] at h
  sig_pre [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_three, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp16, spLo, spHi, rd, wr, oU, oE, oP, oR, oS, oA, uE, uP, uR, uS, uA, eS, pS, rS, SA, Fo, Fu, Fe, Fp,
    Fr, FS, FA, fo, fu, fe, fp, fr, fS, valid, el1, el2, plv, scr, alU, alS⟩ := h
  exact ⟨sp16, spLo, spHi, by rw [rd]; simp, by rw [rd]; simp, by rw [rd]; simp, by rw [rd]; simp, wr, oU, oE, oP,
    oR, oS, oA, uE, uP, uR, uS, uA, eS, pS, rS, SA, Fo, Fu, Fe, Fp, Fr, FS, FA, fo, fu, fe, fp, fr, fS, valid, el1,
    el2, plv, scr, alU, alS⟩

end VG.Proof.RsaKeyGen.RISCV64.Cand
