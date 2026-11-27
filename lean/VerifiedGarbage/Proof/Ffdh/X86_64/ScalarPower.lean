module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ScalarPower
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Backend
import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Backend
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Backend
import VerifiedGarbage.Proof.Ffdh.X86_64.Scrub
import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
import VerifiedGarbage.Proof.Variants.FfdhExp.X86_64.Base
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ScalarPower
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
meta import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
meta import VerifiedGarbage.Proof.Variants.FfdhExp.X86_64.Base

/-! # The shared scalar FFDH power

Inlining the single shared leaf changes only sequence association. The
existing scalar proofs supply correctness and constant time; the call fits
in the public functions' existing eight bytes of stack.
-/

-- separate module: the three closed cleanup checks cost more than their imports

namespace VG.Proof.Ffdh.X86_64.ScalarPower

open VG VG.X86_64 VG.Proof.Bignum.X86_64

-- Reassociate sequences through branches, leaving loops and other programs intact.
def appendCode {I C : Type} : Code I C → Code I C → Code I C
  | .seq a b,c => .seq a (appendCode b c)
  | a,b => .seq a b

def reassoc {I C : Type} : Code I C → Code I C
  | .seq a b => appendCode (reassoc a) (reassoc b)
  | .ite q a b => .ite q (reassoc a) (reassoc b)
  | c => c

def SameExec {M : ISA} (a b : Prog M) : Prop :=
  ∀ s t u, Exec M a s t u ↔ Exec M b s t u

theorem same_seq {M : ISA} {a b c d : Prog M} (h : SameExec a b) (k : SameExec c d) :
    SameExec (.seq a c) (.seq b d) := by
  intro s t u
  constructor
  · intro he
    cases he with
    | seq x y => exact .seq ((h _ _ _).mp x) ((k _ _ _).mp y)
  · intro he
    cases he with
    | seq x y => exact .seq ((h _ _ _).mpr x) ((k _ _ _).mpr y)

theorem same_assoc {M : ISA} (a b c : Prog M) :
    SameExec (.seq a (.seq b c)) (.seq (.seq a b) c) := by
  intro s t u
  constructor
  · intro he
    cases he with
    | seq x y => cases y with
      | seq z w => rw [← List.append_assoc]; exact .seq (.seq x z) w
  · intro he
    cases he with
    | seq x y => cases x with
      | seq z w => rw [List.append_assoc]; exact .seq z (.seq w y)

theorem append_same {M : ISA} (a b : Prog M) : SameExec (appendCode a b) (.seq a b) := by
  induction a with
  | seq x y _ ih =>
    intro s t u
    exact (same_seq (fun _ _ _ => Iff.rfl) ih _ _ _).trans (same_assoc x y b _ _ _)
  | _ => exact fun _ _ _ => Iff.rfl

theorem reassoc_same {M : ISA} (c : Prog M) : SameExec (reassoc c) c := by
  induction c with
  | seq a b ia ib =>
    intro s t u
    exact (append_same (reassoc a) (reassoc b) _ _ _).trans (same_seq ia ib _ _ _)
  | ite q a b ia ib =>
    intro s t u
    constructor
    · intro he
      cases he with
      | iteT h e => exact .iteT h ((ia _ _ _).mp e)
      | iteF h e => exact .iteF h ((ib _ _ _).mp e)
    · intro he
      cases he with
      | iteT h e => exact .iteT h ((ia _ _ _).mpr e)
      | iteF h e => exact .iteF h ((ib _ _ _).mpr e)
  | _ => exact fun _ _ _ => Iff.rfl

theorem verified_reassoc {a b : Prog isa} {k : Contract isa}
    (he : reassoc a = reassoc b) (hv : Verified target b k) : Verified target a k := by
  have ex : SameExec a b := fun s t u =>
    ((reassoc_same a s t u).symm.trans (he.symm ▸ reassoc_same b s t u))
  refine ⟨?_,?_,hv.2.2⟩
  · intro s hs
    obtain ⟨t,u,e,ha,hp⟩ := hv.1 s hs
    exact ⟨t,u,(ex _ _ _).mpr e,ha,hp⟩
  · intro s t ts tt us ut ps pt hp es et
    exact hv.2.1 _ _ _ _ _ _ ps pt hp ((ex _ _ _).mp es) ((ex _ _ _).mp et)

abbrev arith := Variants.MillerRabin.X86_64.Base.variant
abbrev exponent := Variants.FfdhExp.X86_64.Base.variant



open CheckPrivate in
theorem private_verified : Verified target Impl.Ffdh.X86_64.ScalarPower.privateCode
    (Spec.Ffdh.checkPrivateContract abi 8) := by
  have hv := verified_reassoc (a := (Impl.Ffdh.X86_64.ScalarPower.privateCode).inline)
    (by kernel_rfl) (privateInline_verified arith exponent)
  refine Verified.of_inline_verified (by lit_decide) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi kpSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  sig_post [Spec.Ffdh.checkPrivateContract,Spec.Ffdh.checkPrivateSig,abi,argRegs,stackArgs_three,List.append_eq] at hp ⊢
  exact hp

open DerivePublic in
theorem derive_verified : Verified target Impl.Ffdh.X86_64.ScalarPower.deriveCode
    (Spec.Ffdh.derivePublicContract abi 8) := by
  have hv := verified_reassoc (a := (Impl.Ffdh.X86_64.ScalarPower.deriveCode).inline)
    (by kernel_rfl) (deriveInline_verified arith exponent)
  refine Verified.of_inline_verified (by lit_decide) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi dvSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  obtain ⟨-, -, hw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hyl, -, -, -⟩ :=
    dv_implies.pre s (Sig.pre_stack0_abi hs)
  have hy := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := (s.gpr .rsi).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt)
  rw [hyl] at hy
  sig_post [Spec.Ffdh.derivePublicContract,Spec.Ffdh.derivePublicSig,abi,argRegs,stackArgs_three,List.append_eq] at hp ⊢
  rw [bytesAt_overlay hy]
  exact hp

open Exchange in
theorem exchange_verified : Verified target Impl.Ffdh.X86_64.ScalarPower.exchangeCode
    (Spec.Ffdh.exchangeContract abi 8) := by
  have hv := verified_reassoc (a := (Impl.Ffdh.X86_64.ScalarPower.exchangeCode).inline)
    (by kernel_rfl) (exchangeInline_verified arith exponent)
  refine Verified.of_inline_verified (by lit_decide) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi exSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  have hw : s.wr = _ := (ex_implies.pre s (Sig.pre_stack0_abi hs)).2.2.1
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := (s.gpr .rsi).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt)
  sig_post [Spec.Ffdh.exchangeContract,Spec.Ffdh.exchangeSig,abi,argRegs,stackArgs_five,List.append_eq] at hp ⊢
  intro h₁ h₂
  rw [written_overlay hb]
  exact hp h₁ h₂

public theorem private_scrubbed : VerifiedScrubbed target Impl.Ffdh.X86_64.Fn.checkPrivateScalar
    (Spec.Ffdh.checkPrivateContract abi 8) 32 :=
  Scrub.verifiedScrubbedAll (api := Spec.Ffdh.checkPrivateApi)
    { code := Impl.Ffdh.X86_64.ScalarPower.privateCode
      verified := private_verified } .sse (Proof.Ffdh.X86_64.Scrub.checkPrivateOut 8)

public theorem derive_scrubbed : VerifiedScrubbed target Impl.Ffdh.X86_64.Fn.derivePublicScalar
    (Spec.Ffdh.derivePublicContract abi 8) 32 :=
  Scrub.verifiedScrubbedAll (api := Spec.Ffdh.derivePublicApi)
    { code := Impl.Ffdh.X86_64.ScalarPower.deriveCode
      verified := derive_verified } .sse (Proof.Ffdh.X86_64.Scrub.derivePublicOut 8)

public theorem exchange_scrubbed : VerifiedScrubbed target Impl.Ffdh.X86_64.Fn.exchangeScalar
    (Spec.Ffdh.exchangeContract abi 8) 32 :=
  Scrub.verifiedScrubbedAll (api := Spec.Ffdh.exchangeApi)
    { code := Impl.Ffdh.X86_64.ScalarPower.exchangeCode
      verified := exchange_verified } .sse (Proof.Ffdh.X86_64.Scrub.exchangeOut 8)

end VG.Proof.Ffdh.X86_64.ScalarPower
