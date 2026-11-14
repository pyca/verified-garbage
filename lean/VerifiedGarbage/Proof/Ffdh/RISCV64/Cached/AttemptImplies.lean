module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.AttemptFn
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.CachedSat
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.RISCV64.Target
-- separate module: the shared contract's unfolding, apart from the correctness proof's chain of modules

/-!
# `vg_ffdh_generate_key_cached` on RISC-V: the shared contract

`cgContract` states the shared contract on the registers and the stack
(`cg_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64

theorem cgStackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] :=
  rfl

theorem cg_pre {s : State} (h : (Spec.Ffdh.cachedGenerateKeyContract RISCV64.abi).pre s) : cgContract.pre s := by
  sig_pre [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig,
    RISCV64.abi, RISCV64.argRegs, cgContract, cgStackArgs_five, List.getD_cons_succ, List.getD_cons_zero,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, List.append_eq, List.filter_cons, List.filter_nil, List.map_cons,
    List.map_nil, List.filterMap_cons, List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append,
    List.cons_append, List.nil_append, List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true,
    Bool.cond_false, Bool.or_true, Bool.or_false] at h
  sig_split h
  sig_reduce [cgContract, cgDom, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Ffdh.generationContextAt]
  sig_and_intros
  sig_close
  all_goals first
    | with_reducible assumption
    | sig_disjoint_symm
    | omega
    | exact (‹Spec.Ffdh.generationContextAt _ _ _ _ _›).1
    | exact (‹Spec.Ffdh.generationContextAt _ _ _ _ _›).2
    | (sig_simp_only [Nat.mul_comm] at *
       first | with_reducible assumption | sig_disjoint_symm)
    | (simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.or_true, Bool.or_false,
        Bool.cond_true, Bool.cond_false, Sig.conj_cons, List.nil_append, List.cons_append] at *
       simp_all only [cgStack])

/-- The stack's bytes: `rand_len` 64, `scratch` `0x4000`, `scratch_len`
1056, `ctx` `0x100000` and `ctx_len` 275, at `0x9000`. -/
private def attemptBase (a : Addr) : Byte :=
  if a = 0x9000 then 0x40 else if a = 0x9009 then 0x40 else if a = 0x9010 then 0x20
  else if a = 0x9011 then 0x04 else if a = 0x901a then 0x10 else if a = 0x9020 then 0x13
  else if a = 0x9021 then 0x01 else CachedSat.domainMem a

/-- A state meeting the contract: the domain at `0x3000`, x at `0x1000`, `y`
at `0x1100`, `rand` at `0x7000`, the working space at `0x4000` and the
context at `0x100000`. -/
private def attemptState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x1100 | .a3 => 64 | .a4 => 0x3000 | .a5 => 128 | .a6 => 64
    | .a7 => 0x7000 | _ => 0
  sp := 0x9000
  mem := CachedSat.withContext attemptBase
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 64⟩, ⟨0x100000, 2200⟩, ⟨0x9000, 40⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x4000, 8448⟩]

private theorem attempt_arg (i : Nat) (hi : i < 5) :
    stackArg attemptState i = Mem.readW attemptBase (0x9000 + BitVec.ofNat 64 (8 * i)) 64 := by
  unfold stackArg stackArgAddr
  rw [show attemptState.sp = 0x9000 from rfl]
  refine CachedSat.readW_outside _ ?_
  have small : ∀ i < 5, ((0x9000 : BitVec 64) + BitVec.ofNat 64 (8 * i)).toNat + 64 / 8 ≤ 0x100000 := by
    decide
  exact small i hi

private theorem a0 : stackArg attemptState 0 = 64 := by rw [attempt_arg 0 (by decide)]; decide
private theorem a1 : stackArg attemptState 1 = 0x4000 := by rw [attempt_arg 1 (by decide)]; decide
private theorem a2 : stackArg attemptState 2 = 1056 := by rw [attempt_arg 2 (by decide)]; decide
private theorem a3 : stackArg attemptState 3 = 0x100000 := by rw [attempt_arg 3 (by decide)]; decide
private theorem a4 : stackArg attemptState 4 = 275 := by rw [attempt_arg 4 (by decide)]; decide

private theorem attempt_args : List.map (stackArg attemptState) (List.range 5) =
    [64, 0x4000, 1056, 0x100000, 275] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append,
    a0, a1, a2, a3, a4]

private theorem attempt_domain : Spec.Rsa.bytesAt attemptState.mem 0x3000 128 = CachedSat.domain := by
  rw [show attemptState.mem = CachedSat.withContext attemptBase from rfl, CachedSat.domain_unchanged]
  apply CachedSat.bytesAt_eq
  have : ∀ i < 128, attemptBase (0x3000 + BitVec.ofNat 64 i) = CachedSat.domainMem (0x3000 + BitVec.ofNat 64 i) := by
    decide
  exact this

theorem attempt_sat : ∃ s, (Spec.Ffdh.cachedGenerateKeyContract RISCV64.abi).pre s := by
  refine ⟨attemptState, ?_⟩
  sig_pre [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Ffdh.generationContextAt, RISCV64.abi, argRegs, attempt_args]
  simp only [a0, a1, a2, a3, a4]
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

theorem cg_post {s t : State} (h : cgContract.post s t) : (Spec.Ffdh.cachedGenerateKeyContract RISCV64.abi).post s t := by
  sig_post [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, RISCV64.abi,
    RISCV64.argRegs, cgStackArgs_five, List.getD_cons_succ, List.getD_cons_zero, List.append_eq]
  sig_reduce [cgContract, cgDom, cgA, cgScalar] at h
  exact h

theorem cg_pub {s₁ s₂ : State} (h : (Spec.Ffdh.cachedGenerateKeyContract RISCV64.abi).pub s₁ s₂) : cgContract.pub s₁ s₂ := by
  sig_pub [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, RISCV64.abi,
    RISCV64.argRegs, cgStackArgs_five, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  exact h

theorem cg_implies : cgContract.Implies (Spec.Ffdh.cachedGenerateKeyContract RISCV64.abi) where
  pre _ h := cg_pre h
  post _ _ _ h := cg_post h
  pub _ _ _ _ h := cg_pub h
  sat := attempt_sat

end VG.Proof.Ffdh.RISCV64.Cached
