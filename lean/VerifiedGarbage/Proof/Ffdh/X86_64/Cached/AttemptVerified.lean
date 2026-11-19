module

public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Impl.Ffdh.X86_64.Cached
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Cached
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.CombCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Zero
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.CombCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Start
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Start
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Zero
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Flags
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
meta import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Flags
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutInputs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutInputs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ScanRawCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanRawCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Front
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.CachedSat
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.X86_64.Target
import Batteries.Logic
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Tactic.Push
meta import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
meta import VerifiedGarbage.Proof.Ffdh.ScalarWidth
meta import VerifiedGarbage.Proof.Ffdh.VettedPolicy
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Front
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Ffdh.CachedSat
meta import Batteries.Logic

/-! ### `Ffdh.X86_64.Cached.AttemptCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.Cached.AttemptCorrect`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.Cached.AttemptContract`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.Cached.AttemptSat`, which this module and modules that import it used -/

section

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

private theorem attempt_sat_stack (n : Nat) (hn : n = 0 ∨ n = 8) :
    (Proof.Ffdh.cachedGenerateKeyContract abi n).pre attemptState := by
  rcases hn with rfl | rfl
  all_goals
    sig_pre [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig,
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

theorem attempt_sat : ∃ s, (Proof.Ffdh.cachedGenerateKeyContract abi).pre s :=
  ⟨attemptState, attempt_sat_stack 0 (.inl rfl)⟩

theorem attempt_sat8 : ∃ s, (Proof.Ffdh.cachedGenerateKeyContract abi 8).pre s :=
  ⟨attemptState, attempt_sat_stack 8 (.inr rfl)⟩

end VG.Proof.Ffdh.X86_64.Cached

end

end

/-! # FFDH key generation from the context on x86-64: the attempt's internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp powMod)

/-- `(x, x_len, y, y_len, domain, domain_len, p_len, rand, rand_len,
scratch, scratch_len, ctx, ctx_len)`. -/
def cgPre (s : State) : Prop :=
  let xr : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let yr : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let dom : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let rnd : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
  let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  let ctx : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 56⟩
  (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64 ∧ s.rd = [dom, rnd, ctx, args] ∧ s.wr = [xr, yr, scr] ∧
    xr.Disjoint yr ∧ xr.Disjoint dom ∧ xr.Disjoint rnd ∧ xr.Disjoint scr ∧ xr.Disjoint ctx ∧
    xr.Disjoint args ∧ yr.Disjoint dom ∧ yr.Disjoint rnd ∧ yr.Disjoint scr ∧ yr.Disjoint ctx ∧
    yr.Disjoint args ∧ dom.Disjoint scr ∧ rnd.Disjoint scr ∧ scr.Disjoint ctx ∧ scr.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
    (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
    (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint xr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint yr ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint dom ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint rnd ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ctx ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint args ∧
    pLenValid (stackArg s 0).toNat ∧ domainLenValid (stackArg s 0).toNat (s.gpr .r9).toNat ∧
    (s.gpr .rsi).toNat = (stackArg s 0).toNat ∧ (s.gpr .rcx).toNat = (stackArg s 0).toNat ∧
    (stackArg s 2).toNat = (stackArg s 0).toNat ∧ Spec.Rsa.scratchWords (stackArg s 0).toNat ≤ (stackArg s 4).toNat ∧
    domainValid (stackArg s 0).toNat (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) ∧
    generationContextAt s.mem (stackArg s 5) (stackArg s 6).toNat (stackArg s 0).toNat
      (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)

/-- The parameters and the scalar on entry. -/
abbrev cgDom (s : State) : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
abbrev cgA (s : State) : Parameters := domainOf (stackArg s 0).toNat (cgDom s)
abbrev cgRand (s : State) : List Byte := bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
abbrev cgS (s : State) : Nat := vettedScalarOfOctets (cgA s) (cgRand s)

def cgPost (s s' : State) : Prop :=
  ((s'.gpr .rax).setWidth 32).toNat = keyStatus (cgA s) (cgS s) ∧
    if keyStatus (cgA s) (cgS s) = 1 then
      bytesAt s'.mem (s.gpr .rdi) (stackArg s 0).toNat = i2osp (cgS s) (stackArg s 0).toNat ∧
        bytesAt s'.mem (s.gpr .rdx) (stackArg s 0).toNat =
          i2osp (powMod (cgA s).g (cgS s) (cgA s).p) (stackArg s 0).toNat
    else bytesAt s'.mem (s.gpr .rdi) (stackArg s 0).toNat = List.replicate (stackArg s 0).toNat 0 ∧
      bytesAt s'.mem (s.gpr .rdx) (stackArg s 0).toNat = List.replicate (stackArg s 0).toNat 0

/-- What timing may depend on, beyond the arguments. -/
def cgLeak (s : State) : List Nat := (cgDom s).map (·.toNat) ++ [keyStatus (cgA s) (cgS s)]

def cgPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ cgLeak s₁ = cgLeak s₂ ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
    stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
    stackArg s₁ 6 = stackArg s₂ 6

def cgContract : Contract isa where
  pre := cgPre
  post := cgPost
  pub := cgPub

theorem stackArgs_seven (s : State) : List.map (stackArg s) (List.range 7) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

theorem cg_pre0 {s : State} (h : (Proof.Ffdh.cachedGenerateKeyContract abi).pre s) : cgPre s := by
  sig_pre [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs,
    List.append_eq, pLenValid, domainLenValid, List.range, List.range.loop] at h
  sig_pre [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs,
    List.append_eq, pLenValid, domainLenValid, List.range, List.range.loop] at h
  sig_split h
  sig_reduce [cgPre, pLenValid, domainLenValid, generationContextAt, List.range, List.range.loop]
  sig_and_intros
  sig_close
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

theorem cg_post0 {s t : State} (h : cgPost s t) : (Proof.Ffdh.cachedGenerateKeyContract abi).post s t := by
  sig_post [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs, stackArgs_seven,
    List.append_eq]
  sig_reduce [cgPost, cgDom, cgA, cgRand, cgS] at h
  exact h

theorem cg_pub0 {s₁ s₂ : State} (h : (Proof.Ffdh.cachedGenerateKeyContract abi).pub s₁ s₂) : cgPub s₁ s₂ := by
  sig_pub [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs, stackArgs_seven,
    List.append_eq, pLenValid, domainLenValid] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  exact h

theorem cg_implies : cgContract.Implies (Proof.Ffdh.cachedGenerateKeyContract abi) where
  pre _ h := cg_pre0 h
  post _ _ _ h := cg_post0 h
  pub _ _ _ _ h := cg_pub0 h
  sat := attempt_sat

end VG.Proof.Ffdh.X86_64.Cached

end

end

/-! ### `Ffdh.X86_64.GenerateKey.Core`, which only this module used -/

section

/-! # FFDH on x86-64: scalar rejection and generated public values -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Reject.lean`, which only this module imported.
section

/-! # FFDH on x86-64: rejected scalars zero both key outputs -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

def RejectPost (p : GkP) (s t : State) : Prop :=
  t.gpr .rax = 2 ∧ t.gpr .rdi = p.B ∧
    Spec.Rsa.bytesAt t.mem p.xp p.k = List.replicate p.k 0 ∧
    Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem reject_ok {p : GkP} {rb : List Byte} {mi : BitVec 64} {s : State}
    (h : CheckPrivate.Work p.kp (p.xb rb) mi s) (hd : s.gpr .rdi = off p.B (inner p.w))
    (hax : s.gpr .rax = 0) (hx : Src s p.B p.Z p.xp (p.cut rb))
    (ho : OutOk s p.B p.Z p.xp p.k) (ha : Apart p.xp p.k p.yp p.k)
    (hlen : (p.cut rb).length = p.k) (hld : p.ld < p.k) :
    WP isa (seqs [.block [leave], maskX, ret 2]) s (RejectPost p s) := by
  have hZ : 128 * p.k + 256 ≤ p.Z := h.base.hZ
  have hk : p.k ≤ 1024 := h.base.k2
  change WP isa (.seq (.block [leave]) (.seq maskX (ret 2))) s _
  refine WP.seq (WP.mono (leave_ok (h.mem.ctx hd)) fun u ⟨hdu, hmu, k₁⟩ => ?_)
  have hb := h.base
  obtain hXu : word u.mem p.B (8 * sX) = off p.xp p.ld := by
    rw [hmu]; exact hb.hdr (sX, off p.xp p.ld) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  obtain hLu : word u.mem p.B (8 * sXl) = BitVec.ofNat 64 (p.k - p.ld) := by
    rw [hmu]; exact hb.hdr (sXl, BitVec.ofNat 64 p.n) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  obtain hKu : word u.mem p.B (8 * sK) = BitVec.ofNat 64 p.k := by
    rw [hmu]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  obtain hiu : InScr p.B p.Z s.mem u.mem := by intro a _; rw [hmu]
  obtain hxu := hx.congrK hiu k₁
  obtain hyu : Src u p.B p.Z p.yp (List.replicate p.k 0) := hb.y.congrK hiu k₁
  obtain hou : OutOk u p.B p.Z p.xp p.k := ⟨fun i hi => by rw [k₁.2.2]; exact ho.wr i hi, ho.sep⟩
  refine WP.seq (WP.mono (maskX_ok (B := p.B) (Z := p.Z) (hb.scr.congr k₁.2.2) hdu (by omega) (by omega) hld
    hXu hLu hKu (c := false) (by rw [k₁.gpr (by decide), hax]; rfl) hou)
    fun v ⟨hmask, _, hdv, hf, hs, k₂⟩ => ?_)
  obtain hXv : Spec.Rsa.bytesAt v.mem p.xp p.k = List.replicate p.k 0 := bytes_masked hxu hlen hmask
  obtain hYv : Src v p.B p.Z p.yp (List.replicate p.k 0) := by
    refine ⟨fun i hi => by rw [k₂.2.1, k₂.2.2]; exact hyu.rd i hi, ?_, hyu.out⟩
    intro i hi
    rw [hf _ (hyu.out i hi) (fun j hj => Ne.symm (ha j hj i (by simpa only [List.length_replicate] using hi)))]
    exact hyu.val i hi
  obtain hYbytes : Spec.Rsa.bytesAt v.mem p.yp p.k = List.replicate p.k 0 := by
    obtain hh := bytes_src hYv
    simpa only [List.length_replicate] using hh
  refine WP.mono (ret_ok (r := 2) v (by decide)) fun t ⟨hr, hmem, k₃⟩ => ?_
  exact ⟨hr, (k₃.gpr (by decide)).trans hdv, by rw [hmem]; exact hXv,
    by rw [hmem]; exact hYbytes, fun i hi => by rw [hmem, hs i hi, hmu],
    (fun a ha hx _ => by rw [hmem, hf a ha hx, hmu]),
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/ResultMath.lean`, which only this module imported.
section

/-! # FFDH on x86-64: generation's machine status matches the shared specification -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.Spec.Ffdh

/-- The scalar test rejects with 2; a power's range flag selects 1 or 3. -/
def resultStatus (p : GkP) (rb : List Byte) : Nat :=
  if p.sv = false then 2 else if p.fl rb then 1 else 3

theorem Base.power_value {p : GkP} {rb : List Byte} {s : X86_64.State} (h : Base p rb s)
    (hm : p.mv = true) : p.z rb = p.params.g ^ p.scalar rb % p.params.p := by
  change p.params.g ^ Spec.Rsa.os2ip (p.xb rb) % p.params.p = _
  rw [h.sample_value hm]

theorem Base.resultStatus_eq {p : GkP} {rb : List Byte} {s : X86_64.State} (h : Base p rb s)
    (hm : p.mv = true) (ha : parametersValid p.params = true) :
    resultStatus p rb = keyStatus p.params (p.scalar rb) := by
  cases hsv : p.sv with
  | false =>
    obtain hx : privateValid p.params (p.scalar rb) = false := h.valid.trans hsv
    obtain hr := (VG.Proof.Ffdh.keyStatus_scalar p.params (p.scalar rb)).mpr hx
    simpa only [resultStatus, hsv, ↓reduceIte] using hr.symm
  | true =>
    obtain hx : privateValid p.params (p.scalar rb) = true := h.valid.trans hsv
    rw [VG.Proof.Ffdh.keyStatus_power ha _ hx]
    simp only [resultStatus, hsv, Bool.true_eq_false, ↓reduceIte]
    congr 1
    apply propext
    change (1 < p.z rb ∧ 2 * (p.z rb / 2) + 1 < p.P) ↔ _
    rw [lt_pm1 (VG.Proof.Bignum.valid_facts hm h.k1).1, h.power_value hm]
    rfl

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

/-- The complete attempt result before restoring the caller's saved registers. -/
def AttemptPost (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (resultStatus p rb) ∧ t.gpr .rdi = p.B ∧
    Spec.Rsa.bytesAt t.mem p.xp p.k = (if resultStatus p rb = 1 then p.cut rb else List.replicate p.k 0) ∧
    Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if resultStatus p rb = 1 then p.z rb else 0) p.k ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

/-- The core of an attempt with any tail that computes the power from a
checked scalar. -/
theorem coreWith_ok {tl : List (Prog isa)}
    {p : GkP} {rb : List Byte} {s : State}
    (htail : ∀ mi u, CheckPrivate.Work p.kp (p.xb rb) mi u → u.gpr .rdi = off p.B (inner p.w) →
      Src u p.B p.Z p.xp (p.cut rb) → OutOk u p.B p.Z p.xp p.k → OutOk u p.B p.Z p.yp p.k →
      InScr p.B p.Z s.mem u.mem → Keep (.rdi :: mmRegs) s u → WP isa (seqs tl) u (PowerPost p rb u))
    (h : CheckPrivate.Base p.kp (p.xb rb) s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) (hx : Src s p.B p.Z p.xp (p.cut rb))
    (hoX : OutOk s p.B p.Z p.xp p.k) (hoY : OutOk s p.B p.Z p.yp p.k)
    (ha : Apart p.xp p.k p.yp p.k) (hlen : (p.cut rb).length = p.k) (hld : p.ld < p.k) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup ++ VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl ++
      VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++ ([.block [.alu .test .rax (.reg .rax)],
        .ite .e (seqs [.block [VG.Impl.Rsa.X86_64.Crt.leave], maskX, ret 2]) (seqs tl)] : List (Prog isa)))) s (AttemptPost p rb s) := by
  have hk : 64 ≤ p.k := h.k1
  obtain hodd := (valid_facts hm hk).1
  simp only [List.append_assoc]
  refine wp_seqs_append
    (a := ([.block VG.Impl.Rsa.X86_64.head] ++ pSetup ++ VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl))
    (b := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++ [.block [.alu .test .rax (.reg .rax)],
      .ite .e (seqs [.block [VG.Impl.Rsa.X86_64.Crt.leave], maskX, ret 2]) (seqs tl)])
    (by simp [pSetup]) (by simp)
    (WP.mono (CheckPrivate.setup_work h hd hG hQ hm) fun u₁ S₁ => ?_)
  obtain ⟨mi, hw₁, hd₁⟩ := S₁.1
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr]) (by simp)
    (WP.mono (CheckPrivate.scalar_ok hw₁ hd₁ hodd) fun u₂ S₂ => ?_)
  have hw₂ := S₂.1.1
  have hd₂ := S₂.1.2.1
  simp only [seqs]
  have hflag₂ : u₂.gpr .rax = bit (p.sv = true) := S₂.1.2.2
  refine WP.seq (WP.mono (test_bit_ok hflag₂) fun u₃ ⟨hz, hmem, k⟩ => ?_)
  obtain hw₃ := hw₂.keep hmem k
  obtain hd₃ := (k.gpr (by decide)).trans hd₂
  obtain S₃ : CheckPrivate.StepPost p.kp u₂ (fun _ => True) u₃ :=
    ⟨trivial, by rw [hmem]; exact InScr.refl _ _ _, fun _ _ => by rw [hmem], k.mono (by decide)⟩
  obtain H := (S₁.trans S₂).trans S₃
  obtain hx₃ := hx.congrK H.2.1 H.2.2.2
  obtain hox₃ : OutOk u₃ p.B p.Z p.xp p.k :=
    ⟨fun i hi => by rw [H.2.2.2.2.2]; exact hoX.wr i hi, hoX.sep⟩
  obtain hoy₃ : OutOk u₃ p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [H.2.2.2.2.2]; exact hoY.wr i hi, hoY.sep⟩
  refine WP.ite (!decide (p.sv = true)) (by simp [eval, hz]) (fun he => ?_) (fun he => ?_)
  · have hsv : p.sv = false := by cases h : p.sv <;> simp_all
    obtain hax₃ : u₃.gpr .rax = 0 := by
      rw [k.gpr (by decide)]
      simpa only [bit, hsv, Bool.false_eq_true, ↓reduceIte] using hflag₂
    refine WP.mono (reject_ok hw₃ hd₃ hax₃ hx₃ hox₃ ha hlen hld)
      fun t ⟨hr, hd, hX, hY, hs, hf, kt⟩ => ?_
    refine ⟨?_, hd, ?_, ?_, ?_, (RunFrame.of_scr H.2.1).trans hf, keep_trans H.2.2.2 kt⟩
    · simpa [resultStatus, hsv] using hr
    · simpa [resultStatus, hsv] using hX
    · simpa [resultStatus, hsv, i2osp_zero'] using hY
    · intro i hi
      obtain hH : word u₃.mem p.B (8 * i) = word s.mem p.B (8 * i) := H.2.2.1 i hi
      exact (hs i hi).trans hH
  · have hsv : p.sv = true := by cases h : p.sv <;> simp_all
    refine WP.mono (htail mi u₃ hw₃ hd₃ hx₃ hox₃ hoy₃ H.2.1 H.2.2.2)
      fun t ⟨hr, hd, hX, hY, hs, hf, kt⟩ => ?_
    obtain hres : resultStatus p rb = if p.fl rb then 1 else 3 := by
      simp only [resultStatus, hsv, Bool.true_eq_false, ↓reduceIte]
    refine ⟨by rwa [hres], hd, ?_, ?_, ?_, (RunFrame.of_scr H.2.1).trans hf, keep_trans H.2.2.2 kt⟩
    · rw [hres]
      by_cases hf : p.fl rb
      · rw [ite_eq_left hf, ite_eq_left (by decide)]
        simpa only [ite_eq_left hf] using hX
      · rw [ite_eq_right hf, ite_eq_right (by decide)]
        simpa only [ite_eq_right hf] using hX
    · rw [hres]
      by_cases hf : p.fl rb
      · rw [ite_eq_left hf, ite_eq_left (by decide)]
        simpa only [ite_eq_left hf] using hY
      · rw [ite_eq_right hf, ite_eq_right (by decide)]
        simpa only [ite_eq_right hf] using hY
    · intro i hi
      obtain hH : word u₃.mem p.B (8 * i) = word s.mem p.B (8 * i) := H.2.2.1 i hi
      exact (hs i hi).trans hH

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end


/-! # FFDH key generation from the context on x86-64: the attempt meets its contract -/

@[expose] public section

/-! # FFDH key generation from the context on x86-64: the attempt

`vg_ffdh_generate_key`'s attempt with the scalar cut at the context's width
(`metaLoad`) and `g^x mod p` by the context's comb (`comb_ok`). -/

/-! # FFDH key generation from the context on x86-64: the attempt's data

`vg_ffdh_generate_key`'s data (`GkP`) with the scalar cut at the context's
public width (`cgOf`), and what the attempt keeps of the context: its words,
outside the working space and both outputs, and its pointer in the sixth
stack argument (`CtxIn`). -/

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey

/-- The attempt's public scalar width. -/
abbrev cgBits (s : State) : Nat := Spec.Ffdh.generationScalarBits (gkA s)

/-- Its bytes. -/
abbrev cgEl (s : State) : Nat := (cgBits s + 7) / 8

/-- The mask `metaLoad` computes: `255 >> (8 bytes - width)`. -/
def cgMask (bits : Nat) : BitVec 64 := BitVec.ofNat 64 255 >>> ((8 * ((bits + 7) / 8) - bits) % 64)

/-- `vg_ffdh_generate_key`'s data, with the scalar of the context's width. -/
def cgOf (s : State) : GkP :=
  { gkOf s with
    sv := Spec.Ffdh.privateValid (gkA s) (Spec.Ffdh.vettedScalarOfOctets (gkA s) (gkRand s))
    ld := (stackArg s 0).toNat - cgEl s
    msk := cgMask (cgBits s)
    sf := Spec.Ffdh.vettedScalarOfOctets (gkA s) }

theorem cgMask_byte {bits : Nat} (h1 : 1 ≤ bits) :
    (cgMask bits).setWidth 8 = ScalarWidth.mask bits := by
  obtain hw : ScalarWidth.width bits = (bits + 7) / 8 := by unfold ScalarWidth.width; omega_using [h1]
  obtain hh : ScalarWidth.headBits bits = 8 - (8 * ((bits + 7) / 8) - bits) := by
    unfold ScalarWidth.headBits; rw [hw]; omega_using [h1]
  obtain hd : 8 * ((bits + 7) / 8) - bits < 8 := by omega_using []
  obtain ⟨d, hd'⟩ : ∃ d, d = 8 * ((bits + 7) / 8) - bits := ⟨_, rfl⟩
  rw [← hd'] at hd hh
  unfold cgMask ScalarWidth.mask
  rw [← hd', hh]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  obtain key : ∀ d < 8, 255 % 2 ^ 64 / 2 ^ (d % 64) % 2 ^ 8 = (2 ^ (8 - d) - 1) % 2 ^ 8 := by decide
  exact key d hd

/-- The context's words. -/
structure CtxIn (p : GkP) (cp : Addr) (s : State) : Prop where
  reg : CtxRd s p.B p.Z cp (3 + 34 * p.w)
  ax : ∀ i < 8 * (3 + 34 * p.w), ∀ j < p.k, cp + BitVec.ofNat 64 i ≠ off p.xp j
  ay : ∀ i < 8 * (3 + 34 * p.w), ∀ j < p.k, cp + BitVec.ofNat 64 i ≠ off p.yp j
  words : Spec.Rsa.wordsAt s.mem cp (3 + 34 * p.w) = VG.Proof.Ffdh.generationValues p.k p.dom
  sprd : InRegions (s.rd ++ s.wr) (off p.sp (8 * 6)) 8
  spout : ∀ b < 8, p.Z ≤ ofs p.B (off p.sp (8 * 6) + BitVec.ofNat 64 b)
  spx : ∀ b < 8, ∀ j < p.k, off p.sp (8 * 6) + BitVec.ofNat 64 b ≠ off p.xp j
  spy : ∀ b < 8, ∀ j < p.k, off p.sp (8 * 6) + BitVec.ofNat 64 b ≠ off p.yp j
  sp : word s.mem p.sp (8 * 6) = cp

theorem wordsAt_congr {m m' : Mem} {cp : Addr} {n : Nat}
    (h : ∀ i < 8 * n, m' (cp + BitVec.ofNat 64 i) = m (cp + BitVec.ofNat 64 i)) :
    Spec.Rsa.wordsAt m' cp n = Spec.Rsa.wordsAt m cp n := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left fun i hi => Mem.readW_congr fun b hb => ?_
  obtain hi' := List.mem_range.mp hi
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact h _ (by omega_using [hb, hi'])

theorem CtxIn.keep {p : GkP} {cp : Addr} {s t : State} (h : CtxIn p cp s) (hf : RunFrame p s.mem t.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : CtxIn p cp t := by
  refine ⟨h.reg.congr hrd hwr, h.ax, h.ay, ?_, by rw [hrd, hwr]; exact h.sprd, h.spout, h.spx, h.spy, ?_⟩
  · rw [← h.words]
    exact wordsAt_congr fun i hi => hf _ (h.reg.sep i hi) (h.ax i hi) (h.ay i hi)
  · rw [← h.sp]
    exact Mem.readW_congr fun b hb => hf _ (h.spout b hb) (h.spx b hb) (h.spy b hb)

/-- The stack argument's word is outside the working space. -/
theorem CtxIn.sp_inScr {p : GkP} {cp : Addr} {s : State} (h : CtxIn p cp s) {m m' : Mem}
    (hm : InScr p.B p.Z m m') : word m' p.sp (8 * 6) = word m p.sp (8 * 6) :=
  Mem.readW_congr fun b hb => hm _ (h.spout b hb)

/-- Word `i` of the context. -/
theorem word_of_wordsAt {m : Mem} {cp : Addr} {n i : Nat} (hi : i < n) :
    word m cp (8 * i) = (Spec.Rsa.wordsAt m cp n)[i]'(by simp [Spec.Rsa.wordsAt, hi]) := by
  simp [Spec.Rsa.wordsAt, Bignum.word, off]

/-- Row `j` of the context, a slice of its words. -/
theorem row_of_wordsAt {m : Mem} {cp : Addr} {w j n : Nat} (hj : 3 + w * j + w ≤ n) :
    row m cp w j = ((Spec.Rsa.wordsAt m cp n).drop (3 + j * w)).take w := by
  apply List.ext_getElem
  · simp only [row, List.length_map, List.length_range, List.length_take, List.length_drop, Spec.Rsa.wordsAt]
    rw [Nat.mul_comm j w]; omega_using [hj]
  · intro i h1 h2
    simp only [row, List.length_map, List.length_range] at h1
    simp only [row, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop, Spec.Rsa.wordsAt]
    rw [rowOff]
    simp only [Bignum.word, off]
    rw [show 3 + w * j + i = 3 + j * w + i by rw [Nat.mul_comm j w]]

/-- The comb's data for the attempt's context. -/
def cgT (p : GkP) (mi : BitVec 64) (cp : Addr) : TabP :=
  ⟨p.B, p.Z, VG.Proof.Ffdh.X86_64.inner p.w, p.w, mi, cp, p.P, Spec.Rsa.os2ip ((p.dom.drop p.k).take p.k),
    Spec.Ffdh.generationScalarBits p.params⟩

theorem CtxIn.hdr {p : GkP} {cp : Addr} {s : State} (h : CtxIn p cp s) :
    word s.mem cp 0 = BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits p.params) ∧
    word s.mem cp 8 = BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) ∧
    word s.mem cp 16 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits p.params)) := by
  obtain e := VG.Proof.Ffdh.generationValues_headers p.k p.dom
  rw [← h.words] at e
  obtain g : ∀ i (hi : i < 3), word s.mem cp (8 * i) = ((Spec.Rsa.wordsAt s.mem cp (3 + 34 * p.w)).take 3)[i]'(by
      simp [Spec.Rsa.wordsAt]; omega_using [hi]) := fun i hi => by
    rw [word_of_wordsAt (n := 3 + 34 * p.w) (by omega_using [hi]), List.getElem_take]
  refine ⟨?_, ?_, ?_⟩
  · have := g 0 (by decide); simp only [e] at this; simpa using this
  · have := g 1 (by decide); simp only [e] at this; simpa using this
  · have := g 2 (by decide); simp only [e] at this; simpa using this

theorem CtxIn.ent {p : GkP} {cp : Addr} {s : State} (h : CtxIn p cp s) (mi : BitVec 64) :
    ∀ a < 32, row s.mem cp p.w (2 + a) = Spec.Rsa.toWords ((cgT p mi cp).entry a) p.w := by
  intro a ha
  obtain hfit : 3 + p.w * (2 + a) + p.w ≤ 3 + 34 * p.w := by
    obtain h' := Nat.mul_le_mul_left p.w (show 2 + a + 1 ≤ 34 by omega_using [ha]); rw [Nat.mul_succ] at h'; omega_using [h']
  rw [row_of_wordsAt hfit, h.words]
  exact VG.Proof.Ffdh.generationValues_entry p.k p.dom a ha

theorem bitLength_le_of_lt {x n : Nat} (h : x < 2 ^ n) : Spec.RsaKeyGen.bitLength x ≤ n := by
  by_cases hx : x = 0
  · subst hx; unfold Spec.RsaKeyGen.bitLength; simp
  · have hb := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds hx).1
    by_contra hc
    have : 2 ^ n ≤ 2 ^ (Spec.RsaKeyGen.bitLength x - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega_using [h, hb, this]

/-- The public scalar width of valid parameters: at least 1 and at most
p's bits. -/
theorem genBits_facts {k : Nat} {dom : List Byte} (hv : Spec.Ffdh.domainValid k dom = true) :
    1 ≤ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) ∧
      Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) ≤ 8 * k := by
  obtain hv' := (VG.Proof.Ffdh.domainValid_iff k dom).mp hv
  obtain hbnd : 2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv'.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega_using [this]
  obtain hle : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≤ (Spec.Ffdh.domainOf k dom).p := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega_using []
    | some q => have := (hv'.2.2 q hq).1.2.2; simp only [Option.getD_some]; omega_using [this]
  obtain hp : (Spec.Ffdh.domainOf k dom).p < 2 ^ (8 * k) := by
    obtain h1 := VG.Proof.Bignum.os2ip_lt (dom.take k)
    obtain h2 : 256 ^ (dom.take k).length ≤ 2 ^ (8 * k) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega_using [])
    change Spec.Rsa.os2ip (dom.take k) < _
    omega_using [h1, h2]
  obtain hb := VG.Proof.Ffdh.VettedPolicy.bits_le_bound (Spec.Ffdh.domainOf k dom)
  obtain hbl : 1 ≤ Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) := by
    have := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds
      (show Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≠ 0 by omega_using [hbnd])).2
    by_contra hc
    obtain e : Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) = 0 := by omega
    rw [e] at this; omega_using [hbnd, this]
  refine ⟨?_, Nat.le_trans hb (bitLength_le_of_lt (Nat.lt_of_le_of_lt hle hp))⟩
  unfold Spec.Ffdh.generationScalarBits
  cases he : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simpa using hbl
  | some b => have := recognized_nonzero he; simp only; omega_using [hbl, this]

end VG.Proof.Ffdh.X86_64.Cached

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Ffdh.X86_64.Cached (at_)
open VG.Impl.Ffdh.X86_64.Cached.Generate (metaLoad)
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey
open VG.Proof.Rsa.X86_64 (OutOk Apart)

theorem toNat_mod64 {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat % 64 = x % 64 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- The context's width: `sEl :=` its bytes, `sMsk :=` the mask of its first byte. -/
theorem metaLoad_inputs {p : GkP} {rb : List Byte} {s : State} {cp : Addr} (h : Inputs p rb s)
    (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8 * p.k)
    (hld : p.ld = p.k - (Spec.Ffdh.generationScalarBits p.params + 7) / 8)
    (hmsk : p.msk = cgMask (Spec.Ffdh.generationScalarBits p.params)) :
    WP isa (.block metaLoad) s fun t =>
      Inputs p rb t ∧ word t.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n ∧
      word t.mem p.B (8 * sMsk) = p.msk ∧ Frm p.B scanRanges s.mem t.mem ∧
      Keep [.rax, .rsi, .rdx, .rcx] s t := by
  have hZ := h.base.hZ
  have hk := h.base.k2
  obtain ⟨hw0, hw1, _⟩ := hc.hdr
  obtain hr0 : InRegions (s.rd ++ s.wr) cp 8 := by simpa [off] using hc.reg.rd 0 (by omega)
  obtain hw0' : s.mem.readW cp 64 = BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits p.params) := by
    simpa [Bignum.word, off] using hw0
  obtain hr1 : InRegions (s.rd ++ s.wr) (off cp 8) 8 := hc.reg.rd 1 (by omega)
  obtain hn : p.n = (Spec.Ffdh.generationScalarBits p.params + 7) / 8 := by
    change p.k - p.ld = _; rw [hld]; omega
  obtain hsub : BitVec.ofNat 64 (8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8)) -
      BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits p.params) =
      BitVec.ofNat 64 (8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) - Spec.Ffdh.generationScalarBits p.params) :=
    sub_ofNat (by omega) (by omega)
  let m := (s.mem.writeW (off p.B (8 * sEl)) (BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8))).writeW
    (off p.B (8 * sMsk)) (cgMask (Spec.Ffdh.generationScalarBits p.params))
  refine WP.mono (WP.keep [.rax, .rsi, .rdx, .rcx] (Q := fun t => t.mem = m) (by
    unfold metaLoad
    xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.stk, hdr, at_, h.rdi, hsp, hdrOff, hc.sprd, hc.sp, atOff', hr0, hr1,
      hw0', hw1, h.base.scr.st (d := 8 * sEl) (by change 200 ≤ p.Z; omega),
      h.base.scr.st (d := 8 * sMsk) (by change 256 ≤ p.Z; omega), shl3 (show 8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) < 2 ^ 64 by omega),
      hsub, execShiftCl, VarShiftOp.eval, toNat_mod64 (show 8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) -
        Spec.Ffdh.generationScalarBits p.params < 2 ^ 64 by omega), m, cgMask]
    rfl) rfl)
    fun t ⟨hm, k⟩ => ?_
  obtain o1 := writeW_outside s.mem p.B (d := 8 * sEl)
    (BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8)) (by decide)
  obtain o2 := writeW_outside (s.mem.writeW (off p.B (8 * sEl))
    (BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8))) p.B (d := 8 * sMsk)
    (cgMask (Spec.Ffdh.generationScalarBits p.params)) (by decide)
  obtain hf : Frm p.B scanRanges s.mem t.mem := by
    rw [hm]
    exact (Frm.of_outside o1 (by simp [scanRanges])).trans (Frm.of_outside o2 (by simp [scanRanges]))
  refine ⟨h.keep hf k (by decide), ?_, ?_, hf, k⟩
  · rw [hm, o2.word (by decide) (by decide), word_writeW_self, hn]
  · rw [hm, word_writeW_self, hmsk]

/-- The sampled scalar is ready for the existing private-key arithmetic proofs. -/
def ScalarPostC (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  CheckPrivate.Base p.kp (p.xb rb) t ∧ Src t p.B p.Z p.xp (p.cut rb) ∧ t.gpr .rdi = p.B ∧
    word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep mmRegs s t

/-- The sampled scalar, cut at the context's width. -/
theorem scalarC_ok {p : GkP} {rb : List Byte} {s : State} {cp : Addr} (h : Inputs p rb s)
    (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp) (hm : p.mv = true)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8 * p.k)
    (hld : p.ld = p.k - (Spec.Ffdh.generationScalarBits p.params + 7) / 8)
    (hmsk : p.msk = cgMask (Spec.Ffdh.generationScalarBits p.params)) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Cached.Generate.scalar) s fun t => ScalarPostC p rb s t ∧ CtxIn p cp t := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.scalar
  change WP isa (.seq (.block metaLoad) (.seq (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutSetup)
    (.seq (.loop (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutBody) .ne)
      (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutFinish)))) s _
  refine WP.seq (WP.mono (metaLoad_inputs h hc hsp h1 h8 hld hmsk) fun v ⟨hv, hnv, hmask, hfv, k₂⟩ => ?_)
  refine WP.seq (WP.mono (cutSetup_ok hv hnv hmask) fun z ⟨⟨hr, hmz⟩, k₃⟩ => ?_)
  obtain hz : Inputs p rb z := hv.keep (by intro a _; rw [hmz]) k₃ (by decide)
  refine WP.seq (WP.mono (cut_inputs hz hr) fun a ⟨ha, hx, hh, h8', hf₄, k₄⟩ => ?_)
  obtain hna : word a.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n := by
    rw [hh _ (by have := ha.base.hZ; change 200 ≤ p.Z; omega_using [this]), hmz]
    exact hnv
  refine WP.mono (finish_base ha hx hm hna h8') fun t ⟨hb, hd, hG, hQ, hs, hi, k₅⟩ => ?_
  obtain hZ : 256 ≤ p.Z := by have := h.base.hZ; omega_using [this]
  obtain f₁ : RunFrame p s.mem v.mem := .of_frm hfv (fun r hr => Nat.le_trans (scanRanges_end r hr) hZ)
  obtain f₃ : RunFrame p v.mem z.mem := by rw [hmz]; exact .refl _ _
  obtain F : RunFrame p s.mem t.mem := ((f₁.trans f₃).trans hf₄).trans (.of_scr hi)
  obtain K := ((k₂.trans k₃).trans (k₄.trans k₅))
  refine ⟨⟨hb, hx.congrK hi k₅, hd, hG, hQ, ?_, F, K.mono (by decide)⟩, hc.keep F K.2.1 K.2.2⟩
  intro i hi'
  obtain sv : word v.mem p.B (8 * i) = word s.mem p.B (8 * i) := hfv.word_eq (by
    simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [sEp, sEl, sMsk, sFn] <;> omega_using [hi']) (by omega_using [hi'])
  rw [hs i hi', hh _ (by have := h.base.hZ; omega_using [hZ, hi']), hmz, sv]

/-- `g^x mod p` by the context's comb, from `R² mod p`. -/
theorem ready_comb (Mo : Mont) {p : GkP} {rb : List Byte} {cp : Addr} {s : State}
    (h : CheckPrivate.Ready p.kp (p.xb rb) s) (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8192)
    (hxb : Spec.Rsa.os2ip (p.xb rb) < 2 ^ Spec.Ffdh.generationScalarBits p.params) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.comb Mo.mm)) s
      (CheckPrivate.StepPost p.kp s (CheckPrivate.Value p.kp (p.xb rb))) := by
  obtain ⟨mi, hb, hcm, hG⟩ := h
  have hk := hb.k2
  obtain hrs := Rsa.FixedBaseComb.rows_small h8
  obtain hrp := Rsa.FixedBaseComb.rows_pos (show 0 < Spec.Ffdh.generationScalarBits p.params by omega_using [h1])
  have hxl : (p.xb rb).length = p.kp.xl := hb.xlen
  have hxk : p.kp.xl ≤ p.kp.k := hb.xl2
  refine WP.mono (comb_ok Mo (T := cgT p mi cp) hcm (by rw [hsp]; exact hc.sprd)
    (fun hm => by rw [hsp]; exact hc.sp_inScr hm) (by rw [hsp]; exact hc.sp)
    (hb.hdr (sX, p.kp.xp) (by simp [CheckPrivate.KpP.headers]))
    (by rw [hxl]; exact hb.hdr (sXl, BitVec.ofNat 64 p.kp.xl) (by simp [CheckPrivate.KpP.headers]))
    hc.reg hc.hdr.2.2 (hc.ent mi) hb.x hrp
    (show 5 * Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits p.params) < 2 ^ 31 by omega_using [hrs]) (by rw [hxl]; change 8 * p.kp.xl < 2 ^ 32; omega_using [hk, hxk]) hxb)
    fun t ⟨hct, hy, hf, k⟩ => ?_
  obtain hr : ∀ r ∈ innerR p.w, r.1 + r.2 ≤ slot p.w 8 + tabBytes p.w 32 :=
    fun r hr => by have := (innerR_ok p.w r hr).2.1; omega_using [this]
  obtain ⟨hb', hi, hs⟩ := hb.child hcm.sub hf hr k
  obtain ⟨hh, _⟩ := VG.Proof.Ffdh.X86_64.child_frm hcm.sub hcm.wide hf hr
  refine ⟨⟨⟨mi, hb', hct, (hh _ (by decide)).trans hG⟩, hy.trans ?_⟩, hi, hs, k.mono (by decide)⟩
  rw [powMod_eq]
  rfl

/-- `vg_ffdh_generate_key`'s tail with the comb. -/
theorem tailC_ok (Mo : Mont) (R : R2Impl Mo)
    {p : GkP} {rb : List Byte} {mi : BitVec 64} {s : State} {cp : Addr}
    (h : CheckPrivate.Work p.kp (p.xb rb) mi s) (hd : s.gpr .rdi = off p.B (VG.Proof.Ffdh.X86_64.inner p.w))
    (hm : p.mv = true) (hx : Src s p.B p.Z p.xp (p.cut rb))
    (hoX : OutOk s p.B p.Z p.xp p.k) (hoY : OutOk s p.B p.Z p.yp p.k)
    (ha : Apart p.xp p.k p.yp p.k) (hlen : (p.cut rb).length = p.k) (hld : p.ld < p.k)
    (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8192)
    (hxb : Spec.Rsa.os2ip (p.xb rb) < 2 ^ Spec.Ffdh.generationScalarBits p.params) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.tail Mo.mm (.seq (.block r2Head) R.code))) s
      (PowerPost p rb s) := by
  have hZ : 128 * p.k + 256 ≤ p.Z := h.base.hZ
  have hk : p.k ≤ 1024 := h.base.k2
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.tail
  simp only [List.append_assoc]
  refine wp_seqs_append (a := [.seq (.block r2Head) R.code]) (by simp) (by simp)
    (WP.mono (CheckPrivate.work_ready Mo R h hd hm) fun u ⟨hu, hi₁, hs₁, k₁⟩ => ?_)
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Cached.Generate.comb Mo.mm)
    (b := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput ++
      [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, .block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.status])
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.comb]) (by simp)
    (WP.mono (ready_comb Mo hu (hc.keep (.of_scr hi₁) k₁.2.1 k₁.2.2) ((k₁.gpr (by decide)).trans hsp) h1 h8 hxb)
      fun v ⟨hv, hi₂, hs₂, k₂⟩ => ?_)
  obtain hxy := (hx.congrK hi₁ k₁).congrK hi₂ k₂
  obtain hyv : OutOk v p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact hoY.wr i hi, hoY.sep⟩
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput)
    (b := [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, .block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.status])
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput]) (by simp)
    (WP.mono (publicOutput_ok hv hxy hyv ha hlen) fun z hz => ?_)
  have hz' := hz
  obtain ⟨_, _, _, _, _, _, _, _, hs₃, hf₃, k₃⟩ := hz
  obtain hox : OutOk z p.B p.Z p.xp p.k :=
    ⟨fun i hi => by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hoX.wr i hi, hoX.sep⟩
  obtain hoy : OutOk z p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hoY.wr i hi, hoY.sep⟩
  refine WP.mono (outputs_ok hz' hox hoy ha (by omega_using [hZ]) (by omega_using [hk]) hld hlen)
    fun t ⟨hret, hdi, hX, hY, hs₄, hf₄, k₄⟩ => ?_
  refine ⟨hret, hdi, hX, hY, ?_, ?_, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · intro i hi
    obtain a₁ : word u.mem p.B (8 * i) = word s.mem p.B (8 * i) := hs₁ i hi
    obtain a₂ : word v.mem p.B (8 * i) = word u.mem p.B (8 * i) := hs₂ i hi
    exact (hs₄ i hi).trans ((hs₃ i hi).trans (a₂.trans a₁))
  · exact (RunFrame.of_scr hi₁).trans ((RunFrame.of_scr hi₂).trans (hf₃.trans hf₄))

/-- A complete attempt, from a valid modulus. -/
theorem mainC_ok (Mo : Mont) (R : R2Impl Mo)
    {p : GkP} {rb : List Byte} {s : State} {cp : Addr} (h : Base p rb s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8 * p.k)
    (hld : p.ld = p.k - (Spec.Ffdh.generationScalarBits p.params + 7) / 8)
    (hmsk : p.msk = cgMask (Spec.Ffdh.generationScalarBits p.params))
    (hsf : p.sf rb = Spec.Ffdh.vettedScalarOfOctets p.params rb) :
    WP isa (VG.Impl.Ffdh.X86_64.Cached.Generate.main Mo.mm (.seq (.block r2Head) R.code)) s
      (AttemptPost p rb s) := by
  have hk := h.k1
  have hk' := h.k2
  have hZ := h.hZ
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.main
  change WP isa (.seq (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK)
    (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.scalar ++
      VG.Impl.Ffdh.X86_64.Cached.Generate.core Mo.mm (.seq (.block r2Head) R.code)))) s _
  refine WP.seq (WP.mono (zero_ok h hd) fun u ⟨hu, hy, hf₁, hh, k₁⟩ => ?_)
  obtain hdi : u.gpr .rdi = p.B := (k₁.gpr (by decide)).trans hd
  obtain hg : word u.mem p.B (8 * sG) = off p.dp p.k := by
    rw [hh _ (by change 224 ≤ p.Z; omega_using [hZ])]; exact hG
  obtain hq : word u.mem p.B (8 * sQ) = off p.dp (2 * p.k) := by
    rw [hh _ (by change 232 ≤ p.Z; omega_using [hZ])]; exact hQ
  obtain hcu : CtxIn p cp u := hc.keep (RunFrame.of_y hf₁) k₁.2.1 k₁.2.2
  obtain hspu : u.gpr .rsp = p.sp := (k₁.gpr (by decide)).trans hsp
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Cached.Generate.scalar)
    (b := VG.Impl.Ffdh.X86_64.Cached.Generate.core Mo.mm (.seq (.block r2Head) R.code))
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.scalar])
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.core, pSetup])
    (WP.mono (scalarC_ok ⟨hu, hdi, hy, hg, hq⟩ hcu hspu hm h1 h8 hld hmsk)
      fun v ⟨⟨hb, hx, hdv, hgv, hqv, hs₂, hf₂, k₂⟩, hcv⟩ => ?_)
  obtain hox : OutOk v p.B p.Z p.xp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact h.x.wr i hi, h.x.sep⟩
  obtain hoy : OutOk v p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact h.y.wr i hi, h.y.sep⟩
  obtain hxb : Spec.Rsa.os2ip (p.xb rb) < 2 ^ Spec.Ffdh.generationScalarBits p.params := by
    change Spec.Rsa.os2ip ((p.cut rb).drop p.ld) < _
    rw [VG.Proof.Ffdh.KeyScalar.os2ip_cut_drop, h.cutv hm]
    change p.sf rb < _
    rw [hsf]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain hspv : v.gpr .rsp = p.sp := (k₂.gpr (by decide)).trans hspu
  refine WP.mono (coreWith_ok (tl := VG.Impl.Ffdh.X86_64.Cached.Generate.tail Mo.mm (.seq (.block r2Head) R.code))
    (fun mi w hw hdw hxw hoxw hoyw hiw kw => tailC_ok Mo R hw hdw hm hxw hoxw hoyw h.xy h.cut_length h.ld_lt
      (hcv.keep (.of_scr hiw) kw.2.1 kw.2.2) ((kw.gpr (by decide)).trans hspv) h1 (by omega_using [h8, hk']) hxb)
    hb hdv hgv hqv hm hx hox hoy h.xy h.cut_length h.ld_lt)
    fun t ⟨hr, hdt, hX, hY, hs₃, hf₃, k₃⟩ => ?_
  refine ⟨hr, hdt, hX, hY, ?_, (RunFrame.of_y hf₁).trans (hf₂.trans hf₃), ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro i hi
  rw [hs₃ i hi, hs₂ i hi, hh _ (by omega_using [hZ, hi])]

end VG.Proof.Ffdh.X86_64.Cached

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey
open VG.Proof.Rsa.X86_64 (OutOk Apart apart_of)

theorem genWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = 3 + 34 * ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
  omega_using []

/-- The attempt's precondition: `vg_ffdh_generate_key`'s, the context, and valid parameters. -/
theorem cgCtx_of {s : State} (h : cgPre s) :
    GkCtx s ∧ CtxIn (cgOf s) (stackArg s 5) s ∧ Spec.Ffdh.domainValid (stackArg s 0).toNat (gkDom s) = true := by
  obtain ⟨hsp, hrd, hwr, dxy, dxd, dxr, dxs, dxc, dxa, dyd, dyr, dys, dyc, dya, dds, drs, dsc, dsa,
    wX, wY, wD, wR, wS, wC, _, _, _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hxl, hyl, hrl, hsl, hdv, hcl, hcw⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  obtain hargs : ∀ i < 7, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := fun i hi => by
    refine ⟨⟨stackArgAddr s 0, 56⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]; congr 2; omega_using []]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  refine ⟨⟨hk1, hk2, hdl, hxl, hyl, hrl, by omega_using [hsl], Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dds,
    src_of_region (by rw [hrd]; simp) (by omega_using []) drs, fun i hi => hargs i (by omega_using [hi]), ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩, ?_, hdv⟩
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega_using [hxl, hi]) (by omega_using [])⟩
  · intro i hi
    exact out_scr dxs (contains_byte _ (by omega_using [hxl, hi]) (by omega_using []))
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, by simp, contains_byte _ (by omega_using [hyl, hi]) (by omega_using [])⟩
  · intro i hi
    exact out_scr dys (contains_byte _ (by omega_using [hyl, hi]) (by omega_using []))
  · simpa only [hxl, hyl] using (apart_of dxy (by omega_using []) (by omega_using []))
  · simpa only [hxl] using (apart_of dxd (by omega_using []) (by omega_using []))
  · simpa only [hxl, hrl] using (apart_of dxr (by omega_using []) (by omega_using []))
  · simpa only [hyl] using (apart_of dyd (by omega_using []) (by omega_using []))
  · simpa only [hyl, hrl] using (apart_of dyr (by omega_using []) (by omega_using []))
  · have hn : (stackArg s 6).toNat = 3 + 34 * ((cgOf s).w) := by rw [hcl, genWords_eq]; rfl
    obtain hdl' : (stackArg s 0).toNat ≤ (gkDom s).length := by
      have h2 : (s.gpr .r9).toNat = 2 * (stackArg s 0).toNat ∨ (s.gpr .r9).toNat = 3 * (stackArg s 0).toNat := hdl
      rw [show (gkDom s).length = (s.gpr .r9).toNat from VG.Proof.Bignum.bytesAt_length _ _ _]; omega_using [h2]
    obtain hmv := VG.Proof.Ffdh.domainValid_mod hdv
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_, by rw [← hn]; omega_using [wC]⟩, fun i hi j hj => ?_, fun i hi j hj => ?_,
      ?_, hargs 5 (by decide), fun b hb => ?_, fun b hb j hj => ?_, fun b hb j hj => ?_, rfl⟩
    · refine ⟨⟨stackArg s 5, (stackArg s 6).toNat * 8⟩, by rw [hrd]; simp, ?_⟩
      exact Offset.contains_base _ (by rw [hn]; omega_using [hi]) (by omega_using [wC, hn, hi])
    · exact out_scr dsc.symm (contains_byte _ (by rw [hn]; omega_using [hi]) (by omega_using [wC]))
    · have := apart_of dxc.symm (by omega_using [wC]) (by omega_using []) i (by rw [hn]; omega_using [hi]) j (by rw [hxl]; exact hj)
      exact this
    · have := apart_of dyc.symm (by omega_using [wC]) (by omega_using []) i (by rw [hn]; omega_using [hi]) j (by rw [hyl]; exact hj)
      exact this
    · have e := VG.Proof.Ffdh.generationPrecompute_eq hdl' hmv
      rw [hcw, hn] at e
      exact Option.some.inj e
    · have e : off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (40 + b) := by
        simp only [stackArgAddr, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 8 * (0 + 1) + (40 + b) = 8 * 6 + b by omega_using []]
      change (cgOf s).Z ≤ ofs (cgOf s).B (off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b)
      rw [e]
      exact out_scr dsa.symm (contains_byte _ (by omega_using [hb]) (by omega_using []))
    · have e : off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (40 + b) := by
        simp only [stackArgAddr, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 8 * (0 + 1) + (40 + b) = 8 * 6 + b by omega_using []]
      change off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b ≠ off (cgOf s).xp j
      rw [e]
      exact (apart_of dxa (by omega_using []) (by omega_using []) j (by rw [hxl]; exact hj) (40 + b) (by omega_using [hb])).symm
    · have e : off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (40 + b) := by
        simp only [stackArgAddr, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 8 * (0 + 1) + (40 + b) = 8 * 6 + b by omega_using []]
      change off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b ≠ off (cgOf s).yp j
      rw [e]
      exact (apart_of dya (by omega_using []) (by omega_using []) j (by rw [hyl]; exact hj) (40 + b) (by omega_using [hb])).symm

/-- `vg_ffdh_generate_key`'s inputs, with the scalar of the context's width. -/
theorem _root_.VG.Proof.Ffdh.X86_64.GenerateKey.Base.cached {s t : State} (hb : Base (gkOf s) (gkRand s) t)
    (hv : Spec.Ffdh.domainValid (stackArg s 0).toNat (gkDom s) = true) : Base (cgOf s) (gkRand s) t := by
  obtain hbits := genBits_facts hv
  have hb1 : 1 ≤ cgBits s := hbits.1
  have hb2 : cgBits s ≤ 8 * (stackArg s 0).toNat := hbits.2
  have hk := hb.k1
  have hrl := hb.rl
  refine ⟨hb.k1, hb.k2, hb.dl, hb.doml, hb.rl, hb.hZ, hb.scr, hb.dom, hb.rand, hb.x, hb.y, hb.xy, hb.xd, hb.xr,
    hb.yd, hb.yr, hb.hdr, rfl, ?_, fun _ => ?_⟩
  · change (stackArg s 0).toNat - cgEl s < (stackArg s 0).toNat
    have : 1 ≤ cgEl s := by unfold cgEl; omega_using [hb1]
    change 64 ≤ (stackArg s 0).toNat at hk
    omega_using [hbits, this]
  · change Spec.Rsa.os2ip (VG.Proof.Ffdh.KeyScalar.cut (gkRand s) ((stackArg s 0).toNat - cgEl s)
      ((cgMask (cgBits s)).setWidth 8)) = Spec.Ffdh.vettedScalarOfOctets (gkA s) (gkRand s)
    have hl : (gkRand s).length = (stackArg s 0).toNat := hrl
    obtain hw : ScalarWidth.width (cgBits s) = cgEl s := by unfold ScalarWidth.width cgEl; omega_using [hb1]
    rw [cgMask_byte hb1]
    change 64 ≤ (stackArg s 0).toNat at hk
    have := ScalarWidth.cut_value (r := gkRand s) (bits := cgBits s) (by omega_using [hbits, hl]) (by omega_using [hb2, hl])
    rw [hl, hw] at this
    exact this

theorem resultStatus_lt' (p : GkP) (rb : List Byte) : resultStatus p rb < 2 ^ 32 := by
  unfold resultStatus
  split
  · decide
  · split <;> decide

/-- The attempt's outputs, by `keyStatus`. -/
theorem attempt_specC {p : GkP} {rb : List Byte} {s u t : State} (hb : Base p rb u)
    (hm : p.mv = true) (ha : Spec.Ffdh.parametersValid p.params = true) (h : AttemptPost p rb s t) :
    ((t.gpr .rax).setWidth 32).toNat = Spec.Ffdh.keyStatus p.params (p.scalar rb) ∧
      if Spec.Ffdh.keyStatus p.params (p.scalar rb) = 1 then
        Spec.Rsa.bytesAt t.mem p.xp p.k = Spec.Rsa.i2osp (p.scalar rb) p.k ∧
          Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (Spec.Rsa.powMod p.params.g (p.scalar rb) p.params.p) p.k
      else Spec.Rsa.bytesAt t.mem p.xp p.k = List.replicate p.k 0 ∧
        Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 := by
  obtain ⟨hr, _, hx, hy, _⟩ := h
  obtain hst := hb.resultStatus_eq hm ha
  obtain hlt := resultStatus_lt' p rb
  refine ⟨?_, ?_⟩
  · rw [hr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide)), Nat.mod_eq_of_lt hlt]
    exact hst
  · rw [← hst]
    by_cases hs : resultStatus p rb = 1
    · simp only [ite_eq_left hs] at hx hy ⊢
      refine ⟨hx.trans (hb.cut_i2osp hm), ?_⟩
      rw [hb.power_value hm] at hy
      rw [VG.Proof.Bignum.powMod_eq]
      exact hy
    · simp only [ite_eq_right hs] at hx hy ⊢
      exact ⟨hx, by rw [hy, i2osp_zero']⟩

theorem cgBody_ok (Mo : Mont) (R : R2Impl Mo) {s : State} (hpre : cgPre s) :
    WP isa (VG.Impl.Ffdh.X86_64.Cached.Generate.body Mo.mm (.seq (.block r2Head) R.code)) s fun t =>
      cgPost s t ∧ t.gpr .rdi = (cgOf s).B ∧ RunFrame (cgOf s) s.mem t.mem ∧
      (∀ i < 6, word t.mem (cgOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  obtain ⟨c, hci, hv⟩ := cgCtx_of hpre
  obtain hbits := genBits_facts hv
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_base c) fun u ⟨hb, hd, hi, hs, k⟩ => ?_
  obtain hb₁ : Base (cgOf s) (gkRand s) u := hb.cached hv
  refine WP.mono (dom_base hb₁ hd) fun v ⟨hb', hz, hd', hG, hQ, hi', hs', k'⟩ => ?_
  obtain H : InScr (cgOf s).B (cgOf s).Z s.mem v.mem := hi.trans hi'
  obtain K := keep_trans k k'
  obtain hS : ∀ i < 6, word v.mem (cgOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs' i hi).trans (hs i hi)
  obtain hm : (cgOf s).mv = true := VG.Proof.Ffdh.domainValid_mod hv
  refine WP.ite (!(cgOf s).mv) (by simp [eval, hz]) (fun hf => ?_) (fun _ => ?_)
  · exfalso
    rw [hm] at hf
    exact absurd hf (by decide)
  · refine WP.mono (mainC_ok Mo R hb' hd' hG hQ hm (hci.keep (.of_scr H) K.2.1 K.2.2)
      ((K.gpr (by decide)).trans rfl) hbits.1 hbits.2 rfl rfl rfl) fun t hh => ?_
    have hmain := hh
    obtain ⟨_, hdt, _, _, hsave, hframe, kk⟩ := hh
    refine ⟨?_, hdt, (RunFrame.of_scr H).trans hframe,
      (fun i hi => (hsave i hi).trans (hS i hi)), keep_trans K kk⟩
    obtain hp : Spec.Ffdh.parametersValid (cgOf s).params = true := by
      unfold Spec.Ffdh.domainValid at hv
      exact ((Bool.and_eq_true _ _).mp hv).1
    exact attempt_specC (p := cgOf s) (rb := gkRand s) (s := v) (u := v) (t := t) hb' hm hp hmain

theorem cg_correct (Mo : Mont) (R : R2Impl Mo)
    (hmx : (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) (s : State) (h : cgContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ cgContract.post s t := by
  have hpre := h
  obtain c := (cgCtx_of h).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hRetX, hRetY, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ cgContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.code
  refine WP.seq (WP.mono (cgBody_ok Mo R hpre) fun u ⟨hp, hd, hf, hs, k⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k.2.2) hd (by omega_using [hZ]) hs)
    fun t ⟨hRestore, hm, kk⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (kk.gpr (by decide)).trans (k.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    obtain hbyte := contains_byte (s.gpr .rsp) hi (by decide)
    refine hf _ (out_scr hRetScr hbyte) ?_ ?_
    · intro j hj he
      exact hRetX _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.xl]; exact hj) (by have := c.k2; omega_using []))
    · intro j hj he
      exact hRetY _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.yl]; exact hj) (by have := c.k2; omega_using []))
  · change cgPost s t
    unfold cgPost
    rw [kk.gpr (show .rax ∉ saved by decide), hm]
    exact hp

end VG.Proof.Ffdh.X86_64.Cached

end

end

/-! ### `Ffdh.X86_64.GenerateKey.StagesCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.GenerateKey.MainCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.GenerateKey.CoreCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.GenerateKey.SetupCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.GenerateKey.ScalarCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.GenerateKey.BoundCT`, which only this module used -/

section

/-! # FFDH on x86-64: bound selection depends only on the public domain -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Secret random bytes are existential; domain data is shared between runs. -/
def I (p : GkP) (s : State) : Prop := ∃ rb, Inputs p rb s

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! # FFDH on x86-64: sampling does not branch on the random bytes -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

def MS (p : GkP) (s : State) : Prop := ∃ rb, Inputs p rb s ∧
  word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n ∧ word s.mem p.B (8 * sMsk) = p.msk ∧ p.mv = true

/-- The result is ready for the shared private-key setup and scalar-range check. -/
def Sliced (p : GkP) (s : State) : Prop := ∃ rb, CheckPrivate.Base p.kp (p.xb rb) s ∧
  s.gpr .rdi = p.B ∧ word s.mem p.B (8 * sG) = off p.dp p.k ∧
  word s.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧ p.mv = true ∧ Buffers p rb s

def cutVal (p : GkP) : Reg → BitVec 64
  | .rdi => p.B | .r8 => BitVec.ofNat 64 p.ld | .r10 => p.rp | .r11 => p.xp
  | .rcx => 0 | .r14 => BitVec.ofNat 64 p.k | _ => 0

theorem cut_regs (p : GkP) (s : State) (h : MS p s) :
    WP isa (.block cutSetup) s fun t =>
      ∀ r ∈ [.rdi, .r8, .r10, .r11, .rcx, .r14], t.gpr r = cutVal p r := by
  obtain ⟨rb, hi, hn, hmask, _⟩ := h
  refine WP.mono (cutSetup_ok hi hn hmask) fun t ⟨⟨⟨hrp, hxp, _, hld, hcx, hk⟩, _⟩, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (k.gpr (by decide)).trans hi.rdi
  · exact hld
  · exact hrp
  · exact hxp
  · exact hcx
  · exact hk

theorem cut_stage (p : GkP) (s : State) (h : MS p s) :
    WP isa (.seq (.block cutSetup) (.seq (.loop (.block cutBody) .ne) (.block cutFinish))) s (Sliced p) := by
  obtain ⟨rb, hi, hn, hmask, hm⟩ := h
  refine WP.seq (WP.mono (cutSetup_ok hi hn hmask) fun u ⟨⟨hr, hmem⟩, k₁⟩ => ?_)
  have hu : Inputs p rb u := hi.keep (by intro a _; rw [hmem]) k₁ (by decide)
  refine WP.seq (WP.mono (cut_inputs hu hr) fun v ⟨hv, hx, hh, h8, _, k₂⟩ => ?_)
  have hnv : word v.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n := by
    rw [hh _ (by have := hi.base.hZ; change 200 ≤ p.Z; omega_using [this]), hmem]; exact hn
  refine WP.mono (finish_base hv hx hm hnv h8) fun t ⟨hb, hd, hG, hQ, _, hf, k₃⟩ => ?_
  refine ⟨rb, hb, hd, hG, hQ, hm, hx.congrK hf k₃, ?_, ?_, hi.base.xy, hi.base.cut_length, hi.base.ld_lt⟩
  · exact ⟨fun i hi' => by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hi.base.x.wr i hi', hi.base.x.sep⟩
  · exact ⟨fun i hi' => by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hi.base.y.wr i hi', hi.base.y.sep⟩

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! ### `Ffdh.X86_64.GenerateKey.TailCT`, which this module and modules that import it used -/

section

/-! # FFDH on x86-64: successful scalar attempts use the shared exponentiation timing proof -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- A checked scalar and its two full-width output buffers. -/
def WorkIn (p : GkP) (s : State) : Prop := ∃ rb mi,
  CheckPrivate.Work p.kp (p.xb rb) mi s ∧ s.gpr .rdi = off p.B (inner p.w) ∧
    p.mv = true ∧ Buffers p rb s

theorem work_inner (p : GkP) (s : State) (h : WorkIn p s) : CheckPrivate.Inner p.kp s := by
  obtain ⟨rb, mi, hw, hd, hm, _⟩ := h
  exact ⟨_, mi, hw, hd, hm⟩

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! # FFDH on x86-64: set up the private-scalar core in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (loadArr)

abbrev GkP.d (p : GkP) : DPub := ⟨p.B, p.Z, p.k, p.dp⟩

private theorem sliced_setup (p : GkP) (s : State) (h : Sliced p s) : SetupP p.d s := by
  obtain ⟨_, hb, hd, _, _, hm, _⟩ := h
  have ho := (valid_facts hm hb.k1).1
  exact ⟨p.pb, hb.scr, hd, hb.k1, hb.k2, hb.hZ,
    hb.hdr (sDom, p.dp) (by simp [CheckPrivate.KpP.headers, GkP.kp]),
    hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CheckPrivate.KpP.headers, GkP.kp]),
    hb.dom.take p.k, hb.plen, ho⟩

private def Before (p : GkP) (s : State) : Prop := ∃ rb mi,
  CheckPrivate.Base p.kp (p.xb rb) s ∧ SubCtx s p.B p.Z (inner p.w) p.w p.w mi ∧
    WP isa (seqs (loadArr aXm sX sXl)) s (WorkIn p)

private theorem sliced_before (p : GkP) (s : State) (h : Sliced p s) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s (Before p) := by
  obtain ⟨rb, hb, hd, hG, hQ, hm, hbuf⟩ := h
  have hfull := WP.mono (CheckPrivate.setup_work hb hd hG hQ hm) fun t ⟨⟨mi, hw, hdi⟩, hi, _, k⟩ =>
    (show WorkIn p t from ⟨rb, mi, hw, hdi, hm, hbuf.keep hi k⟩)
  have htail : WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s
      fun t => WP isa (seqs (loadArr aXm sX sXl)) t (WorkIn p) := by
    obtain ⟨tr, t, he, hp⟩ := hfull
    exact WP.seq_iff.mp ⟨tr, t, exec_seqs_append (by simp [pSetup]) (by simp [loadArr]) he, hp⟩
  have hsetup : WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s
      fun t => ∃ mi, CheckPrivate.Base p.kp (p.xb rb) t ∧ SubCtx t p.B p.Z (inner p.w) p.w p.w mi :=
    WP.mono (setup_ok (B := p.B) (Z := p.Z) (k := p.k) (dp := p.dp) (pb := p.pb)
      hb.scr hd hb.k1 hb.k2 hb.hZ
      (hb.hdr (sDom, p.dp) (by simp [CheckPrivate.KpP.headers, GkP.kp]))
      (hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CheckPrivate.KpP.headers, GkP.kp]))
      (hb.dom.take p.k) hb.plen (valid_facts hm hb.k1).1)
      fun t ⟨mi, hc, _, _, hf, k⟩ => by
        obtain ⟨hi, hh, _, _⟩ := CheckPrivate.setup_frame (p := p.kp) hb.k1 hb.hZ hf
        exact ⟨mi, hb.keep hi k hh, hc⟩
  exact WP.mono (WP.and hsetup htail) fun _ ⟨⟨mi, hb, hc⟩, hw⟩ => ⟨rb, mi, hb, hc, hw⟩

private theorem before_load (p : GkP) (s : State) (h : Before p s) : LPre aXm sX sXl p.kp.xlPub s := by
  obtain ⟨rb, mi, hb, hc, hw⟩ := h
  refine CheckPrivate.beforeX_load p.kp s ⟨p.xb rb, mi, hb, hc, ?_⟩
  exact WP.mono hw fun _ ⟨rb, mi, hw, hd, hm, _⟩ => ⟨p.xb rb, mi, hw, hd, hm⟩

theorem setup_load_ct : RelCT isa (Two Sliced)
    (seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++ loadArr aXm sX sXl))
    (Two WorkIn) :=
  RelCT.seqs_append (by simp [pSetup]) (by simp [loadArr])
    (RelCT.seq (R := Two Before)
      (two_post (two_map GkP.d sliced_setup setup_ct) sliced_before)
      (two_post (two_map (fun p => p.kp.xlPub) before_load
        (loadArr_ct (by decide) (by taint_decide) (by taint_decide)))
        (fun _ _ h => h.choose_spec.choose_spec.2.2)))

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! # FFDH on x86-64: only the permitted scalar rejection class controls a branch -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (loadArr leave)

def CB (p : GkP) (s : State) : Prop :=
  WorkIn p s ∧ s.zf = some (!decide (p.sv = true)) ∧ s.gpr .rax = bit (p.sv = true)

theorem branch_eval {p : GkP} {s : State} (h : CB p s) :
    isa.eval .e s = some (!decide (p.sv = true)) := by simp [eval, h.2.1]

theorem reject_mask (p : GkP) (s : State) (h : CB p s ∧ isa.eval .e s = some true) :
    WP isa (.block [leave]) s (MaskPre p) := by
  obtain ⟨⟨⟨rb, mi, hw, hd, _, hb⟩, _, ha⟩, _⟩ := h
  have hZ : 128 * p.k + 256 ≤ p.Z := hw.base.hZ
  have hk : p.k ≤ 1024 := hw.base.k2
  refine WP.mono (leave_ok (hw.mem.ctx hd)) fun t ⟨hdt, hm, k⟩ => ?_
  refine ⟨hw.base.scr.congr k.2.2, hdt, by omega_using [hZ], by omega_using [hk], hb.ld, ?_, ?_, ?_,
    ⟨fun i hi => by rw [k.2.2]; exact hb.ox.wr i hi, hb.ox.sep⟩, decide (p.sv = true), ?_⟩
  · rw [hm]
    exact hw.base.hdr (sX, off p.xp p.ld) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  · rw [hm]
    exact hw.base.hdr (sXl, BitVec.ofNat 64 p.n) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  · rw [hm]
    exact hw.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  · exact ((k.gpr (by decide)).trans ha).trans (bit_eq_bool (p.sv = true))

theorem reject_ct : RelCT isa (Two fun p s => CB p s ∧ isa.eval .e s = some true)
    (seqs [.block [leave], VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, ret 2]) fun _ _ => True := by
  simp only [seqs]
  refine RelCT.seq (R := Two MaskPre)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, _, _, hd, _⟩ := h.1.1; exact hd) (by taint_decide) reject_mask) ?_
  exact RelCT.seq mask_ct (two_taint [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide))

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! # FFDH on x86-64: a key-generation attempt in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

def zeroLoads : List Instr :=
  [.mov .rsi (.mem (hdr sY)), .mov .rcx (.mem (hdr sK)), .mov32 .rax (.imm 0)]

def zeroVal (p : GkP) : Reg → BitVec 64
  | .rsi => p.yp | .rcx => BitVec.ofNat 64 p.k | _ => 0

theorem zero_regs (p : GkP) (s : State) (h : ∃ rb, Base p rb s ∧ s.gpr .rdi = p.B) :
    WP isa (.block zeroLoads) s fun t => ∀ r ∈ [.rsi, .rcx], t.gpr r = zeroVal p r := by
  obtain ⟨rb, hb, hd⟩ := h
  have hZ := hb.hZ
  refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = p.yp ∧
      t.gpr .rcx = BitVec.ofNat 64 p.k) (by
    unfold zeroLoads
    xrun [State.ea, hdr, hd, hdrOff,
      hb.scr.ld (d := 8 * sY) (by change 160 ≤ p.Z; omega_using [hZ]),
      hb.scr.ld (d := 8 * sK) (by change 152 ≤ p.Z; omega_using [hZ]),
      hb.hdr (sY, p.yp) (by simp [GkP.headers]),
      hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers])]) rfl)
    fun t ⟨⟨hy, hk⟩, _⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hy
  · exact hk

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! # FFDH key generation on x86-64: public entry and modulus validation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (stk ws)

def loads : List Instr :=
  [.mov .rax (.mem (stk 4)), .mov .r10 (.mem (stk 1)), .mov .r11 (.mem (stk 2))]

def entryTail : List Instr := save .rax ++
  [.store (ws .rax sX) .rdi, .store (ws .rax sY) .rdx, .store (ws .rax sDom) .r8,
    .store (ws .rax sDomLen) .r9, .store (ws .rax sK) .r10, .store (ws .rax sRand) .r11, .mov .rdi (.reg .rax)]

theorem loads_ok (s : State) (c : GkCtx s) : WP isa (.block loads) s
    fun t => t.gpr .rax = stackArg s 3 := by
  have h3 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 32) 8 := c.ha 3 (by decide)
  have h0 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 8) 8 := c.ha 0 (by decide)
  have h1 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 16) 8 := c.ha 1 (by decide)
  unfold loads stk
  xrun [State.ea, hdrOff, h3, h0, h1]
  rfl

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! # FFDH key generation from the context on x86-64: the attempt in constant time

`vg_ffdh_generate_key`'s stages, each with what the attempt keeps of the
context (`CtxIn`) and `rsp`, and the context's own stages: the width's mask
(`metaLoad`) and the comb. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Ffdh.X86_64.Cached.Generate (metaLoad)
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey

/-- The attempt's public data: `vg_ffdh_generate_key`'s and the context. -/
abbrev AQ : Type := GkP × Addr

/-- The cut at the context's width. -/
def Cut (p : GkP) : Prop :=
  1 ≤ Spec.Ffdh.generationScalarBits p.params ∧ Spec.Ffdh.generationScalarBits p.params ≤ 8 * p.k ∧
    p.ld = p.k - (Spec.Ffdh.generationScalarBits p.params + 7) / 8 ∧
    p.msk = cgMask (Spec.Ffdh.generationScalarBits p.params) ∧ p.sf = Spec.Ffdh.vettedScalarOfOctets p.params

/-- What the attempt keeps of the context. -/
def X (q : AQ) (s : State) : Prop := CtxIn q.1 q.2 s ∧ s.gpr .rsp = q.1.sp ∧ Cut q.1

theorem X.keep {q : AQ} {s t : State} {rs : List Reg} (h : X q s) (hf : RunFrame q.1 s.mem t.mem) (k : Keep rs s t)
    (hr : .rsp ∉ rs) : X q t :=
  ⟨h.1.keep hf k.2.1 k.2.2, (k.gpr hr).trans h.2.1, h.2.2⟩

/-- Before the cut. -/
def IVc (q : AQ) (s : State) : Prop := I q.1 s ∧ q.1.mv = true ∧ X q s

def MSc (q : AQ) (s : State) : Prop := MS q.1 s ∧ X q s

theorem metaLoad_ct : RelCT isa (Two IVc) (.block metaLoad) (Two MSc) := by
  change RelCT isa (Two IVc) (.block ([.mov .rax (.mem (VG.Impl.Rsa.X86_64.Crt.stk 6))] ++ metaLoad.drop 1)) _
  refine RelCT.block_append (pin_ct [.rdi, .rsp] [.rdi, .rax] (fun q r => if r = .rdi then q.1.B else q.2)
    (pins_of (fun q r => if r = .rdi then q.1.B else q.1.sp) fun q s h r hr => by
      obtain ⟨⟨rb, hi⟩, _, hx⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hi.rdi
      · exact hx.2.1) (by taint_decide) (fun q s h => ?_) (by taint_decide) (fun q s h => ?_))
  · obtain ⟨⟨rb, hi⟩, _, hc, hsp, _⟩ := h
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = q.2) (by
      xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.stk, hsp, hdrOff, hc.sprd, hc.sp]) rfl) fun t ⟨hax, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (k.gpr (by decide)).trans hi.rdi
    · exact hax
  · obtain ⟨⟨rb, hi⟩, hm, hx⟩ := h
    obtain ⟨h1, h8, hld, hmsk, _⟩ := hx.2.2
    have hw := metaLoad_inputs hi hx.1 hx.2.1 h1 h8 hld hmsk
    rw [show metaLoad = [.mov .rax (.mem (VG.Impl.Rsa.X86_64.Crt.stk 6))] ++ metaLoad.drop 1 from rfl,
      WP.block_append_iff] at hw
    refine WP.seq (WP.mono hw fun t ht => WP.mono ht fun u ⟨hu, hn, hmk, hf, k⟩ => ⟨⟨rb, hu, hn, hmk, hm⟩, ?_⟩)
    have hZ := hi.base.hZ
    exact hx.keep (.of_frm hf fun r hr => Nat.le_trans (scanRanges_end r hr) (by omega_using [hZ])) k (by decide)

/-- `Sliced`, with the random bytes' length. -/
def SlicedC (q : AQ) (s : State) : Prop := (∃ rb, CheckPrivate.Base q.1.kp (q.1.xb rb) s ∧
  s.gpr .rdi = q.1.B ∧ word s.mem q.1.B (8 * sG) = off q.1.dp q.1.k ∧
  word s.mem q.1.B (8 * sQ) = off q.1.dp (2 * q.1.k) ∧ q.1.mv = true ∧ Buffers q.1 rb s ∧ rb.length = q.1.k) ∧ X q s

theorem SlicedC.sliced {q : AQ} {s : State} (h : SlicedC q s) : Sliced q.1 s := by
  obtain ⟨⟨rb, hb, hd, hG, hQ, hm, hbuf, _⟩, _⟩ := h
  exact ⟨rb, hb, hd, hG, hQ, hm, hbuf⟩

theorem scalar_slicedC (q : AQ) (s : State) (h : IVc q s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Cached.Generate.scalar) s (SlicedC q) := by
  obtain ⟨⟨rb, hi⟩, hm, hx⟩ := h
  obtain ⟨h1, h8, hld, hmsk, _⟩ := hx.2.2
  refine WP.mono (scalarC_ok hi hx.1 hx.2.1 hm h1 h8 hld hmsk) fun t ⟨⟨hb, hxs, hd, hG, hQ, _, hf, k⟩, hc⟩ => ?_
  refine ⟨⟨rb, hb, hd, hG, hQ, hm, ⟨hxs, ⟨fun i hi' => by rw [k.2.2]; exact hi.base.x.wr i hi', hi.base.x.sep⟩,
    ⟨fun i hi' => by rw [k.2.2]; exact hi.base.y.wr i hi', hi.base.y.sep⟩, hi.base.xy, hi.base.cut_length,
    hi.base.ld_lt⟩, hi.base.rl⟩, hc, (k.gpr (by decide)).trans hx.2.1, hx.2.2⟩

theorem sampleC_ct : RelCT isa (Two IVc) (seqs VG.Impl.Ffdh.X86_64.Cached.Generate.scalar) (Two SlicedC) := by
  refine two_post ?_ scalar_slicedC
  change RelCT isa (Two IVc) (.seq (.block metaLoad) (.seq (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutSetup)
    (.seq (.loop (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutBody) .ne)
      (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutFinish)))) _
  refine RelCT.seq metaLoad_ct (two_map Prod.fst (fun _ _ h => h.1) ((pin_ct [.rdi] [.rdi, .r8, .r10, .r11, .rcx, .r14]
    cutVal (pins_rdiB GkP.B fun _ _ h => by obtain ⟨_, hi, _⟩ := h; exact hi.rdi)
    (by taint_decide) cut_regs (by taint_decide) cut_stage).mono (fun _ _ h => h) fun _ _ _ => trivial))

/-! ## The tail -/

/-- `WorkIn`, with the random bytes' length and the context. -/
def WorkInC (q : AQ) (s : State) : Prop := (∃ rb mi, CheckPrivate.Work q.1.kp (q.1.xb rb) mi s ∧
  s.gpr .rdi = off q.1.B (VG.Proof.Ffdh.X86_64.inner q.1.w) ∧ q.1.mv = true ∧ Buffers q.1 rb s ∧
  rb.length = q.1.k) ∧ X q s

theorem WorkInC.workIn {q : AQ} {s : State} (h : WorkInC q s) : WorkIn q.1 s := by
  obtain ⟨⟨rb, mi, hw, hd, hm, hb, _⟩, _⟩ := h
  exact ⟨rb, mi, hw, hd, hm, hb⟩

def ReadyInC (q : AQ) (s : State) : Prop := (∃ rb, CheckPrivate.Ready q.1.kp (q.1.xb rb) s ∧ Buffers q.1 rb s ∧
  rb.length = q.1.k) ∧ q.1.mv = true ∧ X q s

/-- `-p⁻¹ mod 2⁶⁴`, which every run's inner workspace has. -/
noncomputable def canonMi (P : Nat) : BitVec 64 :=
  Classical.epsilon fun mi : BitVec 64 => (P % 2 ^ 64 * mi.toNat + 1) % 2 ^ 64 = 0

theorem canonMi_eq {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat} (hc : ModCtx s B Z o w mi P) :
    mi = canonMi P := by
  have hn0 : (word s.mem (off B o) (slot w aN)).toNat = P % 2 ^ 64 := by
    have := word_of_wv s.mem (off B o) (slot w aN) w (q := 0) (by have := hc.w2; omega_using [this])
    simp only [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one] at this
    rw [this, hc.xv.n]
  have h := hc.xv.inv
  rw [hn0] at h
  have hs := Classical.epsilon_spec (p := fun mi : BitVec 64 => (P % 2 ^ 64 * mi.toNat + 1) % 2 ^ 64 = 0) ⟨mi, h⟩
  exact minv_unique (n := P % 2 ^ 64) (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hc.odd) h hs

/-- The comb's public data for the attempt's. -/
noncomputable def combQ (q : AQ) : CQ :=
  (cgT q.1 (canonMi q.1.P) q.2, off q.1.xp q.1.ld, q.1.n, q.1.sp)

/-- The scalar's value is below the width's power. -/
theorem xb_lt {p : GkP} {rb : List Byte} (hc : Cut p) (hrl : rb.length = p.k) (hk : 1 ≤ p.k) :
    Spec.Rsa.os2ip (p.xb rb) < 2 ^ Spec.Ffdh.generationScalarBits p.params := by
  obtain ⟨h1, h8, hld, hmsk, _⟩ := hc
  change Spec.Rsa.os2ip ((p.cut rb).drop p.ld) < _
  rw [VG.Proof.Ffdh.KeyScalar.os2ip_cut_drop]
  have hw : ScalarWidth.width (Spec.Ffdh.generationScalarBits p.params) =
      (Spec.Ffdh.generationScalarBits p.params + 7) / 8 := by unfold ScalarWidth.width; omega_using [h1]
  change Spec.Rsa.os2ip (VG.Proof.Ffdh.KeyScalar.cut rb p.ld (p.msk.setWidth 8)) < _
  rw [hmsk, cgMask_byte h1, hld, ← hrl, ← hw, ScalarWidth.cut_value (by omega_using [hrl, hk]) (by omega_using [hrl, h8])]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem ready_q0 (q : AQ) (s : State) (h : ReadyInC q s) : Q0 (combQ q) s := by
  obtain ⟨⟨rb, ⟨mi, hb, hcm, hG⟩, hbuf, hrl⟩, hm, hc, hsp, hcut⟩ := h
  have hmi := canonMi_eq hcm
  subst hmi
  have hk := hb.k2
  have hk1 := hb.k1
  have h1 := hcut.1
  have h8 := hcut.2.1
  have h8' : Spec.Ffdh.generationScalarBits q.1.params ≤ 8192 := by
    have : q.1.k = q.1.kp.k := rfl; omega_using [hk, h8, this]
  have hrs := Rsa.FixedBaseComb.rows_small h8'
  have hrp := Rsa.FixedBaseComb.rows_pos (show 0 < Spec.Ffdh.generationScalarBits q.1.params by omega_using [h1])
  have hxl : (q.1.xb rb).length = q.1.kp.xl := hb.xlen
  have hxk : q.1.kp.xl ≤ q.1.kp.k := hb.xl2
  refine ⟨q.1.xb rb, hxl, ⟨hcm, by rw [hsp]; exact hc.sprd, fun hm' => by rw [hsp]; exact hc.sp_inScr hm',
    by rw [hsp]; exact hc.sp, hb.hdr (sX, q.1.kp.xp) (by simp [CheckPrivate.KpP.headers]),
    by rw [hxl]; exact hb.hdr (sXl, BitVec.ofNat 64 q.1.kp.xl) (by simp [CheckPrivate.KpP.headers]),
    hc.reg, hc.hdr.2.2, hc.ent _, hb.x, hrp,
    show 5 * Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits q.1.params) < 2 ^ 31 by omega_using [hrs],
    by rw [hxl]; change 8 * q.1.kp.xl < 2 ^ 32; omega_using [hk, hxk], xb_lt hcut hrl (by omega_using [h1, h8])⟩, hsp⟩


theorem work_readyC (Mo : Mont) (R : R2Impl Mo) (q : AQ) (s : State) (h : WorkInC q s) :
    WP isa (.seq (.block r2Head) R.code) s (ReadyInC q) := by
  obtain ⟨⟨rb, mi, hw, hd, hm, hb, hrl⟩, hx⟩ := h
  exact WP.mono (CheckPrivate.work_ready Mo R hw hd hm) fun _ ⟨hr, hi, _, k⟩ =>
    ⟨⟨rb, hr, hb.keep hi k, hrl⟩, hm, hx.keep (.of_scr hi) k (by decide)⟩

theorem ready_valueC (Mo : Mont) (q : AQ) (s : State) (h : ReadyInC q s) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.comb Mo.mm)) s (ValueIn q.1) := by
  obtain ⟨⟨rb, hr, hb, hrl⟩, _, hc, hsp, hcut⟩ := h
  have hk := hr.choose_spec.1.k2
  have hk1 := hr.choose_spec.1.k1
  have h8 := hcut.2.1
  have h8' : Spec.Ffdh.generationScalarBits q.1.params ≤ 8192 := by
    have : q.1.k = q.1.kp.k := rfl; omega_using [hk, h8, this]
  exact WP.mono (ready_comb Mo hr hc hsp hcut.1 h8' (xb_lt hcut hrl (by have : q.1.k = q.1.kp.k := rfl; omega_using [hk1, this]))) fun _ ⟨hv, hi, _, k⟩ =>
    ⟨rb, hv, hb.keep hi k⟩

theorem tailC_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two WorkInC)
      (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.tail Mo.mm (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.tail
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine seqs_cons_ct (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.comb]) (RelCT.seq (R := Two ReadyInC)
    (two_post (two_map (fun q : AQ => q.1.kp) (fun _ _ h => work_inner _ _ h.workIn)
      ((CheckPrivate.r2_ct Mo R).mono (fun _ _ h => h) (fun _ _ _ => trivial))) (work_readyC Mo R)) ?_)
  refine RelCT.seqs_append (a := VG.Impl.Ffdh.X86_64.Cached.Generate.comb Mo.mm)
    (b := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput ++
      [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, .block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.status])
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.comb]) (by simp) (RelCT.seq (R := Two fun q : AQ => ValueIn q.1)
      (two_post (two_map combQ ready_q0 (comb_ct Mo)) (ready_valueC Mo)) ?_)
  exact two_map Prod.fst (fun _ _ h => h) (RelCT.seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput]) (by simp)
    (RelCT.seq public_mask_ct mask_status_ct))


/-! ## The core -/

theorem sliced_workC (q : AQ) (s : State) (h : SlicedC q s) :
    WP isa (seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
      VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl)) s (WorkInC q) := by
  obtain ⟨⟨rb, hb, hd, hG, hQ, hm, hbuf, hrl⟩, hx⟩ := h
  exact WP.mono (CheckPrivate.setup_work hb hd hG hQ hm) fun t ⟨⟨mi, hw, hdi⟩, hi, _, k⟩ =>
    ⟨⟨rb, mi, hw, hdi, hm, hbuf.keep hi k, hrl⟩, hx.keep (.of_scr hi) k (by decide)⟩

/-- The working space after the scalar's stage, and its flag in `rax`, with
the random bytes' length and the context. -/
def CSc (q : AQ) (s : State) : Prop := WorkInC q s ∧ s.gpr .rax = bit (q.1.sv = true)

def CBc (q : AQ) (s : State) : Prop :=
  WorkInC q s ∧ s.zf = some (!decide (q.1.sv = true)) ∧ s.gpr .rax = bit (q.1.sv = true)

theorem CBc.cb {q : AQ} {s : State} (h : CBc q s) : CB q.1 s := ⟨h.1.workIn, h.2⟩

theorem scalarC_stage (q : AQ) (s : State) (h : WorkInC q s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange) s (CSc q) := by
  obtain ⟨⟨rb, mi, hw, hd, hm, hb, hrl⟩, hx⟩ := h
  exact WP.mono (CheckPrivate.scalar_ok hw hd (valid_facts hm hw.base.k1).1)
    fun _ ⟨⟨hw', hd', ha⟩, hi, _, k⟩ => ⟨⟨⟨rb, mi, hw', hd', hm, hb.keep hi k, hrl⟩,
      hx.keep (.of_scr hi) k (by decide)⟩, ha⟩

theorem testC_stage (q : AQ) (s : State) (h : CSc q s) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s (CBc q) := by
  obtain ⟨⟨⟨rb, mi, hw, hd, hm, hb, hrl⟩, hx⟩, ha⟩ := h
  refine WP.mono (test_bit_ok ha) fun t ⟨hz, hmem, k⟩ => ?_
  have hf : InScr q.1.B q.1.Z s.mem t.mem := by intro a _; rw [hmem]
  exact ⟨⟨⟨rb, mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm, hb.keep hf k, hrl⟩,
    hx.keep (.of_scr hf) k (by decide)⟩, hz, (k.gpr (by decide)).trans ha⟩

theorem coreC_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two SlicedC)
      (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.core Mo.mm (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.core
  simp only [List.append_assoc]
  refine RelCT.seqs_append (a := ([.block VG.Impl.Rsa.X86_64.head] ++ pSetup ++
      VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl))
    (b := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++ [.block [.alu .test .rax (.reg .rax)],
      .ite .e (seqs [.block [VG.Impl.Rsa.X86_64.Crt.leave], VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, ret 2])
        (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.tail Mo.mm (.seq (.block r2Head) R.code)))])
    (by simp [pSetup]) (by simp) (RelCT.seq (R := Two WorkInC)
      (two_post (two_map Prod.fst (fun _ _ h => h.sliced) (setup_load_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) sliced_workC) ?_)
  refine RelCT.seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two CSc)
      (two_post (two_map (fun q : AQ => q.1.kp) (fun _ _ h => work_inner _ _ h.workIn)
        CheckPrivate.scalar_ct) scalarC_stage) ?_)
  simp only [seqs]
  refine RelCT.seq (R := Two CBc)
    (two_piece [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide) testC_stage) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [branch_eval h₁.cb, branch_eval h₂.cb])
    (two_map Prod.fst (fun _ _ h => ⟨h.1.cb, h.2⟩) reject_ct)
    (two_map id (fun _ _ h => h.1.1) (tailC_ct Mo R))


/-! ## The attempt -/

def ZeroPreC (q : AQ) (s : State) : Prop := (∃ rb, Base q.1 rb s ∧ s.gpr .rdi = q.1.B ∧
  word s.mem q.1.B (8 * sG) = off q.1.dp q.1.k ∧ word s.mem q.1.B (8 * sQ) = off q.1.dp (2 * q.1.k)) ∧
    q.1.mv = true ∧ X q s

theorem zero_inputsC (q : AQ) (s : State) (h : ZeroPreC q s) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) s (IVc q) := by
  obtain ⟨⟨rb, hb, hd, hG, hQ⟩, hm, hx⟩ := h
  have hZ := hb.hZ
  refine WP.mono (zero_ok hb hd) fun t ⟨hb', hy, hf, hh, k⟩ => ?_
  exact ⟨⟨rb, hb', (k.gpr (by decide)).trans hd, hy,
    (hh _ (by change 224 ≤ q.1.Z; omega_using [hZ])).trans hG,
    (hh _ (by change 232 ≤ q.1.Z; omega_using [hZ])).trans hQ⟩, hm, hx.keep (RunFrame.of_y hf) k (by decide)⟩

theorem zeroC_ct : RelCT isa (Two ZeroPreC) (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) (Two IVc) :=
  pin_ct [.rdi] [.rsi, .rcx] (fun q => zeroVal q.1)
    (pins_rdiB (fun q : AQ => q.1.B) fun _ _ h => by obtain ⟨⟨_, _, hd, _⟩, _⟩ := h; exact hd)
    (by taint_decide) (fun q s h => zero_regs q.1 s (by obtain ⟨⟨rb, hb, hd, _⟩, _⟩ := h; exact ⟨rb, hb, hd⟩))
    (by taint_decide) zero_inputsC

theorem mainC_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two ZeroPreC)
      (VG.Impl.Ffdh.X86_64.Cached.Generate.main Mo.mm (.seq (.block r2Head) R.code)) fun _ _ => True := by
  change RelCT isa (Two ZeroPreC) (.seq (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK)
    (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.scalar ++
      VG.Impl.Ffdh.X86_64.Cached.Generate.core Mo.mm (.seq (.block r2Head) R.code)))) _
  exact RelCT.seq zeroC_ct (RelCT.seqs_append
    (a := VG.Impl.Ffdh.X86_64.Cached.Generate.scalar)
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.scalar])
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.core, pSetup])
    (RelCT.seq sampleC_ct (coreC_ct Mo R)))

/-- The contract's caller, and its public data. -/
def CRc (q : AQ) (s : State) : Prop := cgPre s ∧ (cgOf s, stackArg s 5) = q

def E1c (q : AQ) (s : State) : Prop := (∃ rb, Base q.1 rb s ∧ s.gpr .rdi = q.1.B) ∧ X q s

def ELc (q : AQ) (s : State) : Prop := s.gpr .rax = q.1.B ∧ WP isa (.block entryTail) s (E1c q)

theorem cut_cgOf {s : State} (hv : Spec.Ffdh.domainValid (stackArg s 0).toNat (gkDom s) = true) : Cut (cgOf s) :=
  ⟨(genBits_facts hv).1, (genBits_facts hv).2, rfl, rfl, rfl⟩

theorem entryC_ct : RelCT isa (Two CRc) (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.entry) (Two E1c) := by
  change RelCT isa (Two CRc) (.block (loads ++ entryTail)) (Two E1c)
  refine RelCT.block_append (RelCT.seq (R := Two ELc)
    (two_piece [.rsp] (pins_of (fun q _ => q.1.sp) fun q s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [← h.2]; rfl)
      (by taint_decide) ?_) ?_)
  · intro q s h
    obtain ⟨c, hci, hv⟩ := cgCtx_of h.1
    have hw : WP isa (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.entry) s (E1c q) :=
      WP.mono (entry_base c) fun t ⟨hb, hd, hi, _, k⟩ => by
        rw [← h.2]
        exact ⟨⟨gkRand s, hb.cached hv, hd⟩, hci.keep (.of_scr hi) k.2.1 k.2.2, (k.gpr (by decide)).trans rfl,
          cut_cgOf hv⟩
    change WP isa (.block (loads ++ entryTail)) s (E1c q) at hw
    refine WP.and ?_ (WP.block_append_iff.mp hw)
    exact WP.mono (loads_ok s c) fun t hh => by rw [← h.2]; exact hh
  exact two_piece [.rax] (pins_of (fun q _ => q.1.B) fun _ _ h _ hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.1) (by taint_decide) fun _ _ h => h.2

theorem e1c_dhp (q : AQ) (s : State) (h : E1c q s) : DHP q.1.d s := by
  obtain ⟨⟨rb, hb, hd⟩, _⟩ := h
  have hZ := hb.hZ
  exact ⟨hb.scr, hd, by change 256 ≤ q.1.Z; omega_using [hZ],
    hb.hdr (sDom, q.1.dp) (by simp [GkP.headers]),
    hb.hdr (sK, BitVec.ofNat 64 q.1.k) (by simp [GkP.headers])⟩

def CEc (q : AQ) (s : State) : Prop := (∃ rb, Base q.1 rb s ∧ s.gpr .rdi = q.1.B ∧
  word s.mem q.1.B (8 * sG) = off q.1.dp q.1.k ∧ word s.mem q.1.B (8 * sQ) = off q.1.dp (2 * q.1.k)) ∧
    s.zf = some q.1.mv ∧ X q s

theorem e1c_ce (q : AQ) (s : State) (h : E1c q s) : WP isa (.block domHead) s (CEc q) := by
  obtain ⟨⟨rb, hb, hd⟩, hx⟩ := h
  exact WP.mono (dom_base hb hd) fun _ ⟨hb', hz, hd', hG, hQ, hi, _, k⟩ =>
    ⟨⟨rb, hb', hd', hG, hQ⟩, hz, hx.keep (.of_scr hi) k (by decide)⟩

theorem cec_eval {q : AQ} {s : State} (h : CEc q s) : isa.eval .ne s = some (!q.1.mv) := by
  simp [eval, h.2.1]

theorem cec_zero (q : AQ) (s : State) (h : CEc q s ∧ isa.eval .ne s = some false) : ZeroPreC q s := by
  have he := h.2
  rw [cec_eval h.1] at he
  have hm : q.1.mv = true := by simpa using he
  exact ⟨h.1.1, hm, h.1.2.2⟩

theorem bodyC_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two CRc) (VG.Impl.Ffdh.X86_64.Cached.Generate.body Mo.mm (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.body
  refine RelCT.seq (R := Two CEc) (RelCT.block_append (RelCT.seq entryC_ct
    (two_post (two_map (fun q : AQ => q.1.d) e1c_dhp domHead_ct) e1c_ce))) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [cec_eval h₁, cec_eval h₂])
    (two_taint [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide))
    (two_map id cec_zero (mainC_ct Mo R))

theorem codeC_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two CRc) (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.code
  refine RelCT.seq (R := Two fun (q : AQ) s => s.gpr .rdi = q.1.B)
    (two_post (bodyC_ct Mo R) fun q s h =>
      WP.mono (cgBody_ok Mo R h.1) fun t ⟨_, hd, _⟩ => by rw [← h.2]; exact hd)
    (two_taint [.rdi] (pins_rdiB (fun q : AQ => q.1.B) fun _ _ h => h) (by taint_decide))


theorem cg_constantTime (Mo : Mont) (R : R2Impl Mo) :
    ConstantTime isa cgContract.pre cgContract.pub
      (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)) := by
  refine RelCT.constantTime ((codeC_ct Mo R).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(cgOf s₁, stackArg s₁ 5), ⟨h₁, rfl⟩, h₂, ?_⟩) fun _ _ h => h)
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, a0, a1, a2, a3, a4, a5, a6⟩ := hp
  unfold cgLeak at hl
  obtain ⟨hd, hstatus⟩ := List.append_inj hl (by simp [cgDom, Spec.Rsa.bytesAt, r5])
  have hdom := ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd)
  have hs := (List.cons.inj hstatus).1
  have hfalse : ((cgOf s₁).sv = false) ↔ ((cgOf s₂).sv = false) := by
    change (Spec.Ffdh.privateValid (cgA s₁) (cgS s₁) = false) ↔
      (Spec.Ffdh.privateValid (cgA s₂) (cgS s₂) = false)
    rw [← keyStatus_scalar _ _, ← keyStatus_scalar _ _, hs]
  have hsv : (cgOf s₁).sv = (cgOf s₂).sv := by
    cases h₁ : (cgOf s₁).sv <;> cases h₂ : (cgOf s₂).sv <;> simp_all
  have hA : gkA s₂ = gkA s₁ := by simp only [gkA, a0, hdom]
  have hD : gkDom s₂ = gkDom s₁ := hdom.symm
  simp only [cgOf, gkOf, cgBits, cgEl, r0, r2, r4, r5, a0, a1, a3, a4, a5, hsp, hD, hA]
  congr 2
  simpa only [cgOf, gkOf, r0, r1, r2, r3, r4, r5, a0, a1, a2, a3, a4, hsp, hD, hA] using hsv.symm

end VG.Proof.Ffdh.X86_64.Cached

end

end

/-! # FFDH key generation from the context on x86-64: verified, with the Montgomery multiplications called

The attempt is proven with each backend's multiplication inline
(`attemptInline`) and emitted with calls of it (`attemptCode`), which inline
to it (`Verified.of_inline_verified`). -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Cached
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64 (R2Impl Verified.of_inline_verified bytesAt_overlay)
open VG.Proof.Bignum.X86_64 (inlineOk_seqs inline_seqs inline_of_noCalls map_inline_of_noCalls allInstrs_inline)

def attemptWith (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Cached.Generate.code mul (.seq (.block r2Head) (R2Words.choice mul))

private theorem all_seqs (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).allInstrs p = l.all (fun c => c.allInstrs p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.allInstrs, List.all_cons] at ih ⊢; rw [ih]

private theorem i_seq (p : Instr → Bool) (a b : Prog isa) :
    (Code.seq a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_ite (p : Instr → Bool) (c : Cond) (a b : Prog isa) :
    (Code.ite c a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_loop (p : Instr → Bool) (a : Prog isa) (c : Cond) :
    (Code.loop a c).allInstrs p = a.allInstrs p := rfl
private theorem i_empty (p : Instr → Bool) :
    (Code.block ([] : List Instr) : Prog isa).allInstrs p = true := rfl

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa)
    (hp : (attemptWith (fun _ _ _ => .block [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) :
    (attemptWith mul).allInstrs p = true := by
  unfold attemptWith VG.Impl.Ffdh.X86_64.Cached.Generate.code VG.Impl.Ffdh.X86_64.Cached.Generate.body
    VG.Impl.Ffdh.X86_64.Cached.Generate.main VG.Impl.Ffdh.X86_64.Cached.Generate.core
    VG.Impl.Ffdh.X86_64.Cached.Generate.tail VG.Impl.Ffdh.X86_64.Cached.Generate.comb
    VG.Impl.Ffdh.X86_64.Cached.Generate.step R2Words.choice R2Words.fast R2Words.old
    VG.Impl.Bignum.X86_64.Public.R2Squares.run VG.Impl.Bignum.X86_64.Public.R2Squares.init
    VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [all_seqs] at *
    | rw [i_seq] at *
    | rw [i_ite] at *
    | rw [i_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  repeat' rw [i_empty] at hp
  exact hp

private theorem k_seq (a b : Prog isa) : (Code.seq a b).InlineOk = (a.InlineOk && b.InlineOk) := rfl
private theorem k_ite (c : Cond) (a b : Prog isa) : (Code.ite c a b).InlineOk = (a.InlineOk && b.InlineOk) := rfl
private theorem k_loop (a : Prog isa) (c : Cond) : (Code.loop a c).InlineOk = a.InlineOk := rfl
private theorem k_empty : (Code.block ([] : List Instr) : Prog isa).InlineOk = true := rfl

private theorem template_inlineOk (mul : Nat → Nat → Nat → Prog isa)
    (hp : (attemptWith (fun _ _ _ => .block [])).InlineOk = true)
    (hm : ∀ o a b, (mul o a b).InlineOk = true) :
    (attemptWith mul).InlineOk = true := by
  unfold attemptWith VG.Impl.Ffdh.X86_64.Cached.Generate.code VG.Impl.Ffdh.X86_64.Cached.Generate.body
    VG.Impl.Ffdh.X86_64.Cached.Generate.main VG.Impl.Ffdh.X86_64.Cached.Generate.core
    VG.Impl.Ffdh.X86_64.Cached.Generate.tail VG.Impl.Ffdh.X86_64.Cached.Generate.comb
    VG.Impl.Ffdh.X86_64.Cached.Generate.step R2Words.choice R2Words.fast R2Words.old
    VG.Impl.Bignum.X86_64.Public.R2Squares.run VG.Impl.Bignum.X86_64.Public.R2Squares.init
    VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [inlineOk_seqs] at *
    | rw [k_seq] at *
    | rw [k_ite] at *
    | rw [k_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  repeat' rw [k_empty] at hp
  exact hp

private theorem template_inline (mul : Nat → Nat → Nat → Prog isa) :
    (attemptWith mul).inline = attemptWith (fun o a b => (mul o a b).inline) := by
  unfold attemptWith VG.Impl.Ffdh.X86_64.Cached.Generate.code VG.Impl.Ffdh.X86_64.Cached.Generate.body
    VG.Impl.Ffdh.X86_64.Cached.Generate.main VG.Impl.Ffdh.X86_64.Cached.Generate.core
    VG.Impl.Ffdh.X86_64.Cached.Generate.tail VG.Impl.Ffdh.X86_64.Cached.Generate.comb
    VG.Impl.Ffdh.X86_64.Cached.Generate.step R2Words.choice R2Words.fast R2Words.old
    VG.Impl.Bignum.X86_64.Public.R2Squares.run VG.Impl.Bignum.X86_64.Public.R2Squares.init
    VG.Impl.Bignum.X86_64.Public.R2Squares.next
  simp only [Code.inline, inline_seqs, List.map_append, List.map_cons, List.map_nil]
  simp (disch := decide) only [inline_of_noCalls, map_inline_of_noCalls]

/-- The attempt as proven: `mont.mm` inline. -/
def attemptInline (v : RoundImpl) : Prog isa := attemptWith v.mont.mm

/-- The attempt as emitted: `mm`, which inlines to `attemptInline`. -/
def attemptCode (v : RoundImpl) : Prog isa := attemptWith v.mm

theorem attemptCode_inline (v : RoundImpl) : (attemptCode v).inline = attemptInline v := by
  have h := template_inline v.mm
  simp only [v.mmInline] at h
  exact h

theorem attemptCode_inlineOk (v : RoundImpl) : (attemptCode v).InlineOk = true :=
  template_inlineOk v.mm (by decide +kernel) v.mmOk

private theorem attemptCode_safe (v : RoundImpl) :
    (attemptCode v).allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true := by
  rw [← allInstrs_inline, attemptCode_inline]
  exact template_instrs _ _ (by decide +kernel) v.arithSafe

theorem attemptInline_mx (v : RoundImpl) :
    (attemptInline v).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := attemptCode_safe v
  rw [← allInstrs_inline, attemptCode_inline] at h
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).1

theorem attemptCode_sp (v : RoundImpl) :
    (attemptCode v).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have h := attemptCode_safe v
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).2

theorem attemptInline_verified (v : RoundImpl) :
    Verified target (attemptInline v) (Proof.Ffdh.cachedGenerateKeyContract abi) :=
  Verified.of_correct (cg_correct v.mont (R2Impl.words v.mont) (attemptInline_mx v))
    (cg_constantTime v.mont (R2Impl.words v.mont)) cg_implies

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem attemptCode_verified (v : RoundImpl) : Verified target (attemptCode v)
    (Proof.Ffdh.cachedGenerateKeyContract abi 8) := by
  have hv := attemptInline_verified v
  rw [← attemptCode_inline] at hv
  refine Verified.of_inline_verified (attemptCode_inlineOk v) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi attempt_sat8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  obtain ⟨-, -, hw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hxl, hyl, -, -, -, -, -⟩ := cg_implies.pre s (Sig.pre_stack0_abi hs)
  have hx := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := (s.gpr .rsi).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt)
  have hy := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := (s.gpr .rcx).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rcx).isLt)
  rw [hxl] at hx
  rw [hyl] at hy
  sig_post [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argRegs, stackArgs_seven, List.append_eq] at hp ⊢
  rw [bytesAt_overlay hx, bytesAt_overlay hy]
  exact hp

end VG.Proof.Ffdh.X86_64.Cached
