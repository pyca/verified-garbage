module

public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl
meta import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.CT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Correct
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.CT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Correct

/-! ### `Ffdh.X86_64.CheckPrivate.Verified`, which only this module used -/

section

/-! # FFDH private-key validation on x86-64: verified -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain

theorem kp_verified (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl)
    (hmx : ctlOk (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code)) = true) :
    Verified target (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code))
      (Spec.Ffdh.checkPrivateContract abi) := by
  exact Verified.of_correct (kp_correct M E R hmx) (kp_constantTime M E R hE) kp_implies

end VG.Proof.Ffdh.X86_64.CheckPrivate

end

end

/-! ### `Ffdh.X86_64.CheckPrivate.Safety`, which only this module used -/

section

/-! # Instruction safety of the x86-64 FFDH private-key validator -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64 (inlineOk_seqs inline_seqs inline_of_noCalls map_inline_of_noCalls allInstrs_inline)

private def codeWith (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code mul ex (.seq (.block r2Head) (R2Words.choice mul))

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa)
    (ex : Nat → Nat → List (Prog isa))
    (hp : (codeWith (fun _ _ _ => .block []) (fun _ _ => [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) (he : (ex sX sXl).all (fun c => c.allInstrs p) = true) :
    (codeWith mul ex).allInstrs p = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  -- the lemmas at the instructions' own type, where `simp` finds them
  obtain e₁ : ∀ a b : Code Instr Cond, Code.allInstrs p (Code.seq a b) = (Code.allInstrs p a && Code.allInstrs p b) :=
    i_seq p
  obtain e₂ : ∀ (c : Cond) (a b : Code Instr Cond),
      Code.allInstrs p (Code.ite c a b) = (Code.allInstrs p a && Code.allInstrs p b) := i_ite p
  obtain e₃ : ∀ (a : Code Instr Cond) (c : Cond), Code.allInstrs p (Code.loop a c) = Code.allInstrs p a := i_loop p
  obtain e₄ : ∀ l : List (Code Instr Cond), Code.allInstrs p (seqs l) = l.all (fun c => Code.allInstrs p c) :=
    all_seqs p
  simp only [e₁, e₂, e₃, e₄, List.all_append, List.all_cons] at hp ⊢
  repeat' rw [hm]
  rw [he]
  repeat' rw [i_empty] at hp
  exact hp

/-- The template's calls can be inlined if `mul`'s and `ex`'s can. -/
private theorem template_inlineOk (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa))
    (hp : (codeWith (fun _ _ _ => .block []) (fun _ _ => [])).InlineOk = true)
    (hm : ∀ o a b, (mul o a b).InlineOk = true) (he : (ex sX sXl).all Code.InlineOk = true) :
    (codeWith mul ex).InlineOk = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  obtain e₁ : ∀ a b : Code Instr Cond, (Code.seq a b).InlineOk = (a.InlineOk && b.InlineOk) := k_seq
  obtain e₂ : ∀ (c : Cond) (a b : Code Instr Cond), (Code.ite c a b).InlineOk = (a.InlineOk && b.InlineOk) := k_ite
  obtain e₃ : ∀ (a : Code Instr Cond) (c : Cond), (Code.loop a c).InlineOk = a.InlineOk := k_loop
  obtain e₄ : ∀ l : List (Code Instr Cond), (seqs l).InlineOk = l.all Code.InlineOk := inlineOk_seqs
  simp only [e₁, e₂, e₃, e₄, List.all_append, List.all_cons] at hp ⊢
  repeat' rw [hm]
  rw [he]
  repeat' rw [k_empty] at hp
  exact hp

/-- The template has no calls of its own: it commutes with inlining. -/
private theorem template_inline (mul : Nat → Nat → Nat → Prog isa) (ex ex' : Nat → Nat → List (Prog isa))
    (he : @List.map (Code Instr Cond) (Prog isa) (@Code.inline Instr Cond) (ex sX sXl) = ex' sX sXl) :
    (codeWith mul ex).inline = codeWith (fun o a b => (mul o a b).inline) ex' := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  simp only [Code.inline, inline_seqs, List.map_append, List.map_cons, List.map_nil, he]
  simp (disch := decide) only [inline_of_noCalls, map_inline_of_noCalls]

/-- The template loads MXCSR only where `ex` restores it. -/
private theorem template_ctl (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa))
    (hm : ∀ o a b, (mul o a b).allInstrs (fun i => !loadsMxcsr i) = true) (he : (ex sX sXl).all ctlOk = true) :
    ctlOk (codeWith mul ex) = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  -- `ctl_tac hm he`, with its second alternative at reducible transparency: where the code is not `mul`'s,
  -- the `exact` otherwise compares `Code.allInstrs` of the two by evaluating it on the template's blocks;
  -- and its `apply`s, which otherwise unfold `ctlOk` on code of another shape before they fail
  repeat' first
    | with_reducible exact he
    | with_reducible exact ctlOk_of_noLoad (hm _ _ _)
    | decide +kernel
    | (with_reducible apply ctlOk_seqs_of
       simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
       try and_intros)
    | with_reducible apply ctlOk_seq_of
    | with_reducible apply ctlOk_ite_of
    | with_reducible apply ctlOk_loop_of

/-- The function as proven: `mont.mm` inline. -/
def privateInline (v : RoundImpl) (e : ExpImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code v.mont.mm (e.code v.mont.mm)
    (.seq (.block r2Head) (R2Words.choice v.mont.mm))

/-- The function as emitted: `mm`, which inlines to `privateInline`. -/
def privateCode (v : RoundImpl) (e : ExpImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code v.mm (e.code v.mm) (.seq (.block r2Head) (R2Words.choice v.mm))

theorem privateCode_inline (v : RoundImpl) (e : ExpImpl) : (privateCode v e).inline = privateInline v e := by
  have h := template_inline v.mm (e.code v.mm) (e.code fun o a b => (v.mm o a b).inline)
    (e.inline v.mm _ _ (Or.inl ⟨rfl, rfl⟩))
  simp only [v.mmInline] at h
  exact h

theorem privateCode_inlineOk (v : RoundImpl) (e : ExpImpl) : (privateCode v e).InlineOk = true :=
  template_inlineOk v.mm _ (by decide +kernel) v.mmOk (e.inlineOk v.mm v.mmOk _ _ (Or.inl ⟨rfl, rfl⟩))

theorem privateInline_ctl (v : RoundImpl) (e : ExpImpl) : ctlOk (privateInline v e) = true :=
  template_ctl _ _ (mul_and_left v.arithSafe) (e.ctl _ (mul_and_left v.arithSafe) _ _ (Or.inl ⟨rfl, rfl⟩))

theorem privateCode_sp (v : RoundImpl) (e : ExpImpl) :
    (privateCode v e).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  rw [← allInstrs_inline, privateCode_inline]
  exact template_instrs _ _ _ (by decide +kernel) (mul_and_right v.arithSafe)
    (e.spSafe _ (mul_and_right v.arithSafe) _ _ (Or.inl ⟨rfl, rfl⟩))

end VG.Proof.Ffdh.X86_64.CheckPrivate

end

end

/-! # Verify FFDH private-key validation for every Montgomery backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64

theorem privateInline_verified (v : RoundImpl) (e : ExpImpl) : Verified target (privateInline v e)
    (Spec.Ffdh.checkPrivateContract abi) := by
  have h := kp_verified v.mont (e.E v.mont) (R2Impl.words v.mont) (e.ctX v.mont)
  rw [e.code_eq] at h
  exact h (privateInline_ctl v e)

theorem kpSatisfiable8 : ∃ s, (Spec.Ffdh.checkPrivateContract abi 8).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [kpSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using kpSat

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem privateCode_verified (v : RoundImpl) (e : ExpImpl) : Verified target (privateCode v e)
    (Spec.Ffdh.checkPrivateContract abi 8) := by
  have hv := privateInline_verified v e
  rw [← privateCode_inline v e] at hv
  refine Verified.of_inline_verified (privateCode_inlineOk v e) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi kpSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  sig_post [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq] at hp ⊢
  exact hp

end VG.Proof.Ffdh.X86_64.CheckPrivate
