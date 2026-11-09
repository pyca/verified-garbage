module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.RndCT
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.RndCT
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_pkcs1_encrypt_random` on RISC-V: `Verified`

Correctness against the shared contract (`code_correct`, from `code_ok`),
constant time (`code_constantTime`) and a state meeting the precondition.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Rnd

open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Random

theorem wordsAt_two (m : Mem) (p : Addr) :
    Spec.Rsa.wordsAt m p 2 = [m.readW p 64, m.readW (p + BitVec.ofNat 64 8) 64] := by
  simp [Spec.Rsa.wordsAt, List.range_succ]

/-- The correctness of `vg_rsa_pkcs1_encrypt_random`, against its shared contract. -/
theorem code_correct (s : State) (h : (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok (rPre_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argRegs,
    stackArgs_seven, List.append_eq, List.range, List.range.loop]
  obtain ⟨⟨req, h0, h1, hq⟩, hm⟩ := hr
  exact ⟨⟨req, by rw [wordsAt_two, h0, h1], hq⟩, hm⟩

/-! ## A state meeting the precondition -/

/-- `out`, `tape` and a modulus of 64 bytes at `0x6000`, `0x7000` and
`0x1000`, `e` and the message of a byte each, an empty tape, 112 words of
working space and 16 precomputed words; the stack arguments at `sp`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x6000 | .a1 => 64 | .a2 => 0x7000 | .a3 => 0x1000 | .a4 => 64 | .a5 => 0x2000 | .a6 => 1
    | .a7 => 0x3000 | _ => 0
  sp := 0x10000000000
  mem a := bif Nat.beq a.toNat 0x10000000000 then 1
    else bif Nat.beq a.toNat 0x10000000009 then 0x40 else bif Nat.beq a.toNat 0x1000000001A then 1
    else bif Nat.beq a.toNat 0x10000000020 then 0x70 else bif Nat.beq a.toNat 0x10000000029 then 0x50
    else bif Nat.beq a.toNat 0x10000000030 then 16 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x5000, 128⟩, ⟨0x10000000000, 56⟩]
  wr := [⟨0x6000, 64⟩, ⟨0x7000, 16⟩, ⟨0x10000, 896⟩]

theorem sat_args : stackArg satState 0 = 1 ∧ stackArg satState 1 = 0x4000 ∧ stackArg satState 2 = 0 ∧
    stackArg satState 3 = 0x10000 ∧ stackArg satState 4 = 112 ∧ stackArg satState 5 = 0x5000 ∧
    stackArg satState 6 = 16 := by
  decide

theorem sat : ∃ s, (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre s := by
  refine ⟨satState, ?_⟩
  have e : rndStack = 4303 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argRegs,
    stackArgs_seven, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := sat_args
  have ha : stackArgAddr satState 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, ha]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by unfold Spec.Rsa.lenValid; decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem code_verified : Verified RISCV64.target code (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack) :=
  ⟨code_correct, code_constantTime, sat⟩

end VG.Proof.RsaPkcs1Enc.RISCV64.Rnd
