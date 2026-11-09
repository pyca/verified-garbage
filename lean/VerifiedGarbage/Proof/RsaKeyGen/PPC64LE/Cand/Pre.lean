module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract

/-!
# A candidate on PPC64LE: the contract's arguments

`CIn s`: the shared contract's precondition (`Proof.RsaKeyGen.candidateContract`,
with 400 bytes of stack), without the table of small primes, as the proof
uses it: `(out, out_len, used, e, e_len, p, p_len, rand)` in
`r3`–`r10`, and `rand_len`, `scratch` and `scratch_len` the stack arguments
0–2.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE

/-- The arguments' regions. -/
abbrev cO (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev cU (s : State) : Region := ⟨s.gpr .r5, 8⟩
abbrev cE (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
abbrev cP (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
abbrev cR (s : State) : Region := ⟨s.gpr .r10, (PPC64LE.stackArg s 0).toNat⟩
abbrev cS (s : State) : Region := ⟨PPC64LE.stackArg s 1, (PPC64LE.stackArg s 2).toNat * 8⟩
abbrev cA (s : State) : Region := ⟨stackArgAddr s 0, 24⟩
/-- The stack the code uses: its frames and the round's. -/
abbrev cF (s : State) : Region := below s.sp 400

/-- The contract's precondition. -/
structure CIn (s : State) : Prop where
  spLo : 400 ≤ s.sp.toNat
  spHi : s.sp.toNat + 32 + 8 * 11 ≤ 2 ^ 64
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
  fo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  fu : (s.gpr .r5).toNat + 8 ≤ 2 ^ 64
  fe : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  fp : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  fr : (s.gpr .r10).toNat + (PPC64LE.stackArg s 0).toNat ≤ 2 ^ 64
  fS : (PPC64LE.stackArg s 1).toNat + (PPC64LE.stackArg s 2).toNat * 8 ≤ 2 ^ 64
  valid : Spec.RsaKeyGen.primeLenValid (s.gpr .r4).toNat
  el1 : 1 ≤ (s.gpr .r7).toNat
  el2 : (s.gpr .r7).toNat ≤ 8
  plv : (s.gpr .r9).toNat = 0 ∨ (s.gpr .r9).toNat = (s.gpr .r4).toNat
  scr : Spec.Rsa.scratchWords (s.gpr .r4).toNat ≤ (PPC64LE.stackArg s 2).toNat

theorem stackArgs_three (s : State) :
    List.map (PPC64LE.stackArg s) (List.range 3) = [PPC64LE.stackArg s 0, PPC64LE.stackArg s 1,
      PPC64LE.stackArg s 2] := rfl

end VG.Proof.RsaKeyGen.PPC64LE.Cand
