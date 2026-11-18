module

public import VerifiedGarbage.Proof.Ffdh.X86.KeyGenTop
import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyGenTop
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive

/-!
# `vg_ffdh_generate_key` on i686 in time that depends on the domain and the status only

The contract releases the domain and the status: runs with the same ones
leak the same traces. The scan of the bound reads the domain, the cut of
`rand` and the rest have no branch on it; the one branch on the scalar,
whether it is invalid, is whether the status is 2.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeyGen

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame ret testMask)

/-! ## The taint checks -/

theorem mod_check : ACheck (Prog.chain [.block PublicFn.modulusArgs, .block modulusCheck] (.block [])) := by
  dsimp only [ACheck]; taint_decide
theorem ret0_check : ACheck (ret 0) := by dsimp only [ACheck]; taint_decide
theorem fail_check : ACheck Impl.Ffdh.X86.GenerateKey.fail := by dsimp only [ACheck]; taint_decide

theorem copy612_check : ACheck (copy (.slot .wide 6) (.slot .wide 12) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem nil_check : ACheck (.block []) := by dsimp only [ACheck]; taint_decide
theorem outStat_check : ACheck (.seq Impl.Ffdh.X86.GenerateKey.outputs (.block statusOf)) := by
  dsimp only [ACheck]; taint_decide

/-! ## The runs of the tail -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- A run, with the domain's geometry. -/
abbrev TP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (u : State) : Prop :=
  Run Ex base bytes len args sp u ∧ DomGeo args base bytes len dlen u.rd u.wr

theorem tp_step {x u : State} (T : TP Ex base bytes len dlen args sp x) (S : Step Ex base bytes len args x u) :
    TP Ex base bytes len dlen args sp u :=
  ⟨run_step T.1 S, T.2.keep ⟨rfl, rfl⟩ S.keeps⟩

/-- The tail with the stage `pow`, whose runs are related. -/
theorem tailWith_trace {Q : State → Prop} {pow : Prog isa}
    (hpow : RelCT isa (Both Q) pow (Both (TP Ex base bytes len dlen args sp))) :
    RelCT isa (Both Q) (tailWith pow) fun _ _ => True := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  apply VG.RelCT.chain
  refine VG.RelCT.seq (M := isa) (R := Both (TP Ex base bytes len dlen args sp)) ?_ ?_
  · refine VG.RelCT.seq hpow ?_
    refine VG.RelCT.seq (aRel (F := TP Ex base bytes len dlen args sp) (fun _ T => T.1) copy612_check fun x T =>
      WP.mono (KeyGen.copyW_ok T.1.1 (a := 6) (b := 12) (by decide) (by decide) (by decide))
        fun _ ⟨S, _⟩ => tp_step T S) ?_
    refine VG.RelCT.seq (aRel (F := fun u => TP Ex base bytes len dlen args sp u ∧ ∃ c, u.gpr .ecx = cmask c)
      (fun _ T => T.1) VG.Proof.Ffdh.X86.CheckPrivate.range_check fun x T =>
        WP.mono (rangeMask_ok T.1.1 (a := 12) (by decide)) fun _ ⟨_, e, O, K⟩ =>
          ⟨tp_step T (Step.word T.1.1 (by decide) O K), _, e⟩) ?_
    refine VG.RelCT.seq (aRel (F := TP Ex base bytes len dlen args sp) (fun _ T => T.1.1)
      VG.Proof.Ffdh.X86.CheckPrivate.store_check fun x ⟨T, c, e⟩ =>
        WP.mono (storeMask_ok T.1.1 (d := accOff) (by omega_using [ao, nb]) e) fun _ ⟨_, O, _, _, K⟩ =>
          tp_step T (Step.word T.1.1 (by omega_using [ao]) O K)) ?_
    exact aRel (fun _ T => T.1) nil_check fun _ T => WP.block_nil T
  · exact aEnd (fun _ T => T.1) outStat_check

end

/-! ## The runs of the body -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {D : List Byte} {St : Nat}

theorem keyStatus_two {a : Spec.Ffdh.Parameters} {x : Nat} :
    Spec.Ffdh.keyStatus a x = 2 ↔ Spec.Ffdh.privateValid a x = false := by
  unfold Spec.Ffdh.keyStatus
  cases Spec.Ffdh.privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, iff_false]
    split <;> decide

/-- The modulus check, as the domain's. -/
abbrev modOk (len : Nat) (D : List Byte) : Prop := Spec.Rsa.modulusValid (Spec.Ffdh.domainOf len D).p len = true

end

/-! ## Against the contract -/

end VG.Proof.Ffdh.X86.KeyGen
