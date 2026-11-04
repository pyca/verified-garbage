module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ffdh.CachedSat
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.X86_64.Target

/-! # FFDH key generation from the context on x86-64: a caller that meets the contract

A valid 64-byte domain (`CachedSat.domain`) and its context
(`CachedSat.withContext`), the outputs, the random bytes, the working space
and the seven stack arguments. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64

private def attemptBase (a : Addr) : Byte :=
  if a = 0x8008 then 0x40 else if a = 0x8011 then 0x70 else if a = 0x8018 then 0x40
  else if a = 0x8021 then 0x90 else if a = 0x8028 then 0x20 else if a = 0x8029 then 0x04
  else if a = 0x8032 then 0x10 else if a = 0x8038 then 0x13 else if a = 0x8039 then 0x01
  else CachedSat.domainMem a

private def attemptState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 128
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := CachedSat.withContext attemptBase
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 64⟩, ⟨0x100000, 2200⟩, ⟨0x8008, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x9000, 8448⟩]
  syms _ := 0

private theorem attempt_arg (i : Nat) (hi : i < 7) :
    stackArg attemptState i = Mem.readW attemptBase (0x8000 + BitVec.ofNat 64 (8 * (i + 1))) 64 := by
  unfold stackArg stackArgAddr
  refine CachedSat.readW_outside _ ?_
  have small : ∀ i < 7, (attemptState.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))).toNat + 64 / 8 ≤ 0x100000 := by
    decide
  exact small i hi

private theorem a0 : stackArg attemptState 0 = 64 := by rw [attempt_arg 0 (by decide)]; decide
private theorem a1 : stackArg attemptState 1 = 0x7000 := by rw [attempt_arg 1 (by decide)]; decide
private theorem a2 : stackArg attemptState 2 = 64 := by rw [attempt_arg 2 (by decide)]; decide
private theorem a3 : stackArg attemptState 3 = 0x9000 := by rw [attempt_arg 3 (by decide)]; decide
private theorem a4 : stackArg attemptState 4 = 1056 := by rw [attempt_arg 4 (by decide)]; decide
private theorem a5 : stackArg attemptState 5 = 0x100000 := by rw [attempt_arg 5 (by decide)]; decide
private theorem a6 : stackArg attemptState 6 = 275 := by rw [attempt_arg 6 (by decide)]; decide

private theorem attempt_args : List.map (stackArg attemptState) (List.range 7) =
    [64, 0x7000, 64, 0x9000, 1056, 0x100000, 275] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append,
    a0, a1, a2, a3, a4, a5, a6]

private theorem attempt_domain : Spec.Rsa.bytesAt attemptState.mem 0x3000 128 = CachedSat.domain := by
  rw [show attemptState.mem = CachedSat.withContext attemptBase from rfl, CachedSat.domain_unchanged]
  apply CachedSat.bytesAt_eq
  have : ∀ i < 128, attemptBase (0x3000 + BitVec.ofNat 64 i) = CachedSat.domainMem (0x3000 + BitVec.ofNat 64 i) := by
    decide
  exact this

theorem attempt_sat : ∃ s, (Spec.Ffdh.cachedGenerateKeyContract abi).pre s := by
  refine ⟨attemptState, ?_⟩
  sig_pre [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Ffdh.generationContextAt, abi, argRegs, attempt_args]
  simp only [a0, a1, a2, a3, a4, a5, a6]
  repeat' apply And.intro
  all_goals first
    | rfl
    | decide
    | (apply Region.disjoint_of_sep; decide)
    | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt attemptState.mem 0x3000 128) = true
       rw [attempt_domain]; exact CachedSat.domain_valid)
    | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt attemptState.mem 0x3000 128) =
          some (Spec.Rsa.wordsAt attemptState.mem 0x100000 275)
       rw [attempt_domain]; exact (CachedSat.canonical attemptBase).2)

end VG.Proof.Ffdh.X86_64.Cached
