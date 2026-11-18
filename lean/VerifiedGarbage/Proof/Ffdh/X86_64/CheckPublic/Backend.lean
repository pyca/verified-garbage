module

public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Verified
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Context
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Context
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Domain

/-! ### `Ffdh.X86_64.CheckPublic.Safety`, which only this module used -/

section

/-! # Instruction safety of the x86-64 FFDH public-key validator -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64 (inlineOk_seqs inline_seqs inline_of_noCalls map_inline_of_noCalls allInstrs_inline)

private def codeWith (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code mul ex (.seq (.block r2Head) (R2Words.choice mul))

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa)
    (ex : Nat → Nat → List (Prog isa))
    (hp : (codeWith (fun _ _ _ => .block []) (fun _ _ => [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) (he : (ex sEp sEl).all (fun c => c.allInstrs p) = true) :
    (codeWith mul ex).allInstrs p = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [all_seqs] at *
    | rw [i_seq] at *
    | rw [i_ite] at *
    | rw [i_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  rw [he]
  repeat' rw [i_empty] at hp
  exact hp

/-- The template's calls can be inlined if `mul`'s and `ex`'s can. -/
private theorem template_inlineOk (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa))
    (hp : (codeWith (fun _ _ _ => .block []) (fun _ _ => [])).InlineOk = true)
    (hm : ∀ o a b, (mul o a b).InlineOk = true) (he : (ex sEp sEl).all Code.InlineOk = true) :
    (codeWith mul ex).InlineOk = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [inlineOk_seqs] at *
    | rw [k_seq] at *
    | rw [k_ite] at *
    | rw [k_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  rw [he]
  repeat' rw [k_empty] at hp
  exact hp

/-- The template has no calls of its own: it commutes with inlining. -/
private theorem template_inline (mul : Nat → Nat → Nat → Prog isa) (ex ex' : Nat → Nat → List (Prog isa))
    (he : @List.map (Code Instr Cond) (Prog isa) (@Code.inline Instr Cond) (ex sEp sEl) = ex' sEp sEl) :
    (codeWith mul ex).inline = codeWith (fun o a b => (mul o a b).inline) ex' := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  simp only [Code.inline, inline_seqs, List.map_append, List.map_cons, List.map_nil, he]
  simp (disch := decide) only [inline_of_noCalls, map_inline_of_noCalls]

/-- The template loads MXCSR only where `ex` restores it. -/
private theorem template_ctl (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa))
    (hm : ∀ o a b, (mul o a b).allInstrs (fun i => !loadsMxcsr i) = true) (he : (ex sEp sEl).all ctlOk = true) :
    ctlOk (codeWith mul ex) = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  ctl_tac hm he

/-- The function as proven: `mont.mm` inline. -/
def publicInline (v : RoundImpl) (e : ExpImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code v.mont.mm (e.code v.mont.mm)
    (.seq (.block r2Head) (R2Words.choice v.mont.mm))

/-- The function as emitted: `mm`, which inlines to `publicInline`. -/
def publicCode (v : RoundImpl) (e : ExpImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code v.mm (e.code v.mm) (.seq (.block r2Head) (R2Words.choice v.mm))

theorem publicCode_inline (v : RoundImpl) (e : ExpImpl) : (publicCode v e).inline = publicInline v e := by
  have h := template_inline v.mm (e.code v.mm) (e.code fun o a b => (v.mm o a b).inline)
    (e.inline v.mm _ _ (Or.inr ⟨rfl, rfl⟩))
  simp only [v.mmInline] at h
  exact h

theorem publicCode_inlineOk (v : RoundImpl) (e : ExpImpl) : (publicCode v e).InlineOk = true :=
  template_inlineOk v.mm _ (by decide +kernel) v.mmOk (e.inlineOk v.mm v.mmOk _ _ (Or.inr ⟨rfl, rfl⟩))

theorem publicInline_ctl (v : RoundImpl) (e : ExpImpl) : ctlOk (publicInline v e) = true :=
  template_ctl _ _ (mul_and_left v.arithSafe) (e.ctl _ (mul_and_left v.arithSafe) _ _ (Or.inr ⟨rfl, rfl⟩))

theorem publicCode_sp (v : RoundImpl) (e : ExpImpl) :
    (publicCode v e).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  rw [← allInstrs_inline, publicCode_inline]
  exact template_instrs _ _ _ (by decide +kernel) (mul_and_right v.arithSafe)
    (e.spSafe _ (mul_and_right v.arithSafe) _ _ (Or.inr ⟨rfl, rfl⟩))

end VG.Proof.Ffdh.X86_64.CheckPublic

end

end

/-! # Verify FFDH public-key validation for every Montgomery backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64

theorem publicInline_verified (v : RoundImpl) (e : ExpImpl) : Verified target (publicInline v e)
    (Spec.Ffdh.checkPublicContract abi) := by
  have h := cp_verified v.mont (e.E v.mont) (R2Impl.words v.mont) (e.ctE v.mont)
  rw [e.code_eq] at h
  exact h (publicInline_ctl v e)

theorem cpSatisfiable8 : ∃ s, (Spec.Ffdh.checkPublicContract abi 8).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, stackArgs_one, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [cpSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cpSat

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem publicCode_verified (v : RoundImpl) (e : ExpImpl) : Verified target (publicCode v e)
    (Spec.Ffdh.checkPublicContract abi 8) := by
  have hv := publicInline_verified v e
  rw [← publicCode_inline v e] at hv
  refine Verified.of_inline_verified (publicCode_inlineOk v e) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi cpSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  sig_post [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, stackArgs_one, List.append_eq] at hp ⊢
  exact hp

end VG.Proof.Ffdh.X86_64.CheckPublic
