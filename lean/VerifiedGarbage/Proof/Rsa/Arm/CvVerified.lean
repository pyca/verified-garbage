module

public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Proof.Rsa.Arm.CvFail
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
import VerifiedGarbage.Proof.Rsa.Arm.CvLoads
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Rsa.Arm.KcBodyW
import VerifiedGarbage.Proof.Rsa.KeyCheckMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.CrtValuesMath
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Finiteness.Attr
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
public import VerifiedGarbage.Proof.Rsa.Arm.CvChecksB
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Rsa.Arm.CvFin
import VerifiedGarbage.Proof.Rsa.Arm.CvStore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
meta import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Rsa.Arm.CvTaint`, which only this module used -/

section

/-! # `vg_rsa_crt_values` on ARMv7: the pieces the taint analysis checks

Between the divisions (whose constant time is `Div.code_ct`) and around the
branch on the modulus' validity, every piece of `vg_rsa_crt_values` reads its
addresses and loop counts from the stack arguments (`argTaint _ 48`) and from
the registers given here, which the two runs agree on by correctness.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues

theorem entry_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 48) (.block entry) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem loads_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48) loads hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem divN_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r7, .r8, .r9] 48) (seqs divN) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `checks`, either variant of its inverse: by `taintU`, which also follows `umaal`. -/
theorem checks_taint (um : Bool) : ∃ hc, (VG.Taint.check taintU (argTaint [] 48) (checks um) hc).isSome = true := by
  cases um
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem divQ_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48) divQ hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem glue_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48)
    (.block (ctx ++ ([.ldr .r10 .r8 sDp, .ldr .r12 .r8 sDq] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem stores_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [.r7, .r8, .r9, .r10, .r12] 48) stores hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem fail_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r3] 48) fail hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48) (.block restore) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.CrtValues

end

end

/-! ### `Rsa.Arm.CvSpec`, which only this module used -/

section

/-! ### `Rsa.Arm.CvTaintW`, which this module and modules that import it used -/

section

/-! # `vg_rsa_crt_values` on ARMv7: the balanced key's pieces the taint analysis checks

`shapeCv` and the pieces of `midW` between its product and divisions by words
(`KeyDiv.mulLo_ct`, `KeyDiv.divW_ct`), and those functions' own pieces for the
arrays they are called on: from the stack arguments and `r7`–`r9`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.KeyDiv

/-- `midW` after the product, to the first division. -/
abbrev chunkW (um : Bool := false) : List (Prog isa) := [eqS sE1 aDR aDQ aT1, eqS sE2 aZero aZero aT1] ++ invSetup ++ [
  .block primeWidth, inverse um, .block ctx, eqS sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3),
  copy aDQ aD, copy aDD aP, .block (clrLow aDD ++ divHdr aDQ aDR2 aDD aDT),
  copy 0 aZero, copy aDD aP, .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)]

theorem shapeCv_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48) (.block shapeCv) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem oddW_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [] 48) (.block (ctx ++ bitOf sPodd aP)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `chunkW`, either variant of its inverse: by `taintU`, which also follows `umaal`. -/
theorem chunkW_taint (um : Bool) :
    ∃ hc, (VG.Taint.check taintU (argTaint [.r7, .r8, .r9] 48) (seqs (chunkW um)) hc).isSome = true := by
  cases um
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem setQ_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r7, .r8, .r9] 48)
    (seqs [copy aDD aQ, .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mulW_taint : MulTaint aDR aP aQ :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem divW2_taint : DivTaint aD aDR2 aDD aDQ aDT aT1 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem divW3_taint : DivTaint aD aDR3 aDD aDQ aDT aT1 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.Rsa.Arm.CrtValues

end

end

/-! ### `Rsa.Arm.CvWords`, which the modules that import this one used -/

section

/-! ### `Rsa.Arm.CvFinish`, which this module and modules that import it used -/

section

/-! ### `Rsa.Arm.CvDivD`, which this module and modules that import it used -/

section

/-! # `vg_rsa_crt_values` on ARMv7: the divisions of `d` -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

theorem divR_ok {s0 s : State} (b : Base s0 s) (hw : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr) {r : Nat}
    (hr : r = aDR2 ∨ r = aDR3) (hd : DivHdr s.mem (cvB s0) (cvW s0) aDQ r aDD aDT)
    (top : w32 s.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0) :
    WP isa VG.Impl.Rsa.Arm.Div.code s fun t => Base s0 t ∧ Keep (cvB s0) (cvW s0) [aDQ, r, aDT] [] s.mem t.mem ∧
      (0 < num s.mem (cvB s0) (cvW s0) aDD → num t.mem (cvB s0) (cvW s0) r =
        num s.mem (cvB s0) (cvW s0) aDQ % num s.mem (cvB s0) (cvW s0) aDD) := by
  have hr' : r < nArr ∧ r ≠ aDQ ∧ r ≠ aDD ∧ r ≠ aDT := by rcases hr with rfl | rfl <;> decide
  refine WP.mono (div_ok hw (q := aDQ) (r := r) (d := aDD) (t := aDT) (by decide) hr'.1 (by decide) (by decide)
    (Ne.symm hr'.2.1) (by decide) (by decide) hr'.2.2.1 hr'.2.2.2 (by decide) hd top) fun t ⟨k, rt, v⟩ =>
    ⟨b.keep k (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl | rfl) <;>
      first | decide | exact hr'.1) (by simp) (by simp) rt.sp rt.rd rt.wr, k, fun pos => (v pos).1⟩

/-- After the division of `d` by `p - 1`. -/
structure StE (s0 : State) (X₁ X₂ : Nat) (s : State) : Prop where
  base : Base s0 s
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  q : num s.mem (cvB s0) (cvW s0) aQ = cvQ s0
  d : num s.mem (cvB s0) (cvW s0) aD = cvD s0
  ddTop : w32 s.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0
  dp : 0 < 2 * (cvP s0 / 2) → num s.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % (2 * (cvP s0 / 2))
  mask : ∃ V, slot s.mem (cvB s0) sMask = (if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then 1 else 0) ∧
    (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
      (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧
      num s.mem (cvB s0) (cvW s0) 3 < cvM s0)

theorem divP_ok {s0 s : State} {X₁ X₂ : Nat} (h : StD s0 X₁ X₂ s) :
    WP isa VG.Impl.Rsa.Arm.Div.code s (StE s0 X₁ X₂) := by
  have hw := h.ws
  have fit := fun j (hj : j < nArr) => hw.fit64 (j := j) hj
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  refine WP.mono (divR_ok h.base hw (.inl rfl) h.hdr h.ddTop) fun t ⟨bt, k, v⟩ => ?_
  obtain ⟨V, mV, iV⟩ := h.mask
  refine ⟨bt, ?_, ?_, ?_, ?_, fun pos => ?_, ⟨V, ?_, ?_⟩⟩
  · rw [← h.count]; exact BitVec.eq_of_toNat_eq (k.slot (e := 16) (by decide) (by simp))
  · rw [k.num (by decide) (by simp) (fit _ (by decide)), h.q]
  · rw [k.num (by decide) (by simp) (fit _ (by decide)), h.d]
  · rw [k.word (by omega_arith) (by decide) (by simp) (fit _ (by decide)), h.ddTop]
  · rw [v (by rw [h.dd]; exact pos), h.dq, h.dd]
  · rw [k.slot (by decide) (by simp), mV]
  · rw [k.num (by decide) (by simp) (fit _ (by decide))]; exact iV

/-- After the division of `d` by `q - 1`. -/
structure StG (s0 : State) (X₁ X₂ : Nat) (s : State) : Prop where
  base : Base s0 s
  dp : 0 < 2 * (cvP s0 / 2) → num s.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % (2 * (cvP s0 / 2))
  dq : 0 < 2 * (cvQ s0 / 2) → num s.mem (cvB s0) (cvW s0) aDR3 = cvD s0 % (2 * (cvQ s0 / 2))
  mask : ∃ V, slot s.mem (cvB s0) sMask = (if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then 1 else 0) ∧
    (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
      (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧
      num s.mem (cvB s0) (cvW s0) 3 < cvM s0)

/-- The geometries of the divisions of `d`. -/
abbrev gP (s0 : State) : VG.Proof.Rsa.Arm.Div.Geometry := divGeom (cvB s0) (cvZ s0) (cvW s0) aDQ aDR2 aDD aDT
abbrev gQ (s0 : State) : VG.Proof.Rsa.Arm.Div.Geometry := divGeom (cvB s0) (cvZ s0) (cvW s0) aDQ aDR3 aDD aDT

theorem StD.ctx {s0 s : State} {X₁ X₂ : Nat} (h : StD s0 X₁ X₂ s) : VG.Proof.Rsa.Arm.Div.Context (gP s0) s :=
  divGeom_ctx h.ws (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h.hdr

/-- `divQ`, then the division, which starts from its context. -/
theorem divQ_pre_ok {s0 s : State} {X₁ X₂ : Nat} (h : StE s0 X₁ X₂ s) :
    WP isa divQ s fun u => VG.Proof.Rsa.Arm.Div.Context (gQ s0) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (StG s0 X₁ X₂) := by
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  unfold divQ
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil ctx]
  refine ctx_ok h.base fun t1 b1 h1 r1 m1 => WP.block_nil ?_
  have fit := fun j (hj : j < nArr) => h1.fit64 (j := j) hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (o := aDQ) (a := aD) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨h2, k2, e2, r2, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h2 (o := aDD) (a := aQ) (by decide) (by decide) (by decide) (by decide))
    fun t3 ⟨h3, k3, e3, r3, top3⟩ => ?_
  show WP isa (.block (clrLow aDD ++ divHdr aDQ aDR3 aDD aDT)) t3 _
  refine clrLow_ok h3 (by decide) (by decide) fun t4 h4 k4 e4 r4 top4 => ?_
  rw [← List.append_nil (divHdr _ _ _ _)]
  have K : Keep (cvB s0) (cvW s0) [aDQ, aDD] [] t1.mem t4.mem := k2.mono.trans (k3.mono.trans k4.mono)
  have c4 : t4.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0) := by
    rw [← h.count, ← m1]; exact BitVec.eq_of_toNat_eq (K.slot (e := 16) (by decide) (by simp))
  refine divHdr_ok h4 (by decide) (by decide) (by decide) (by decide) c4 fun t5 h5 k5 d5 r5 => WP.block_nil ?_
  have K5 : Keep (cvB s0) (cvW s0) [aDQ, aDD] [0, 4, 8, 12] t1.mem t5.mem := K.mono.trans k5.mono
  have R5 : Rest opRegs t1 t5 := r2.trans (r3.trans (r4.trans r5))
  have b5 := b1.keep K5 (by decide) (by decide) (by decide) R5.sp R5.rd R5.wr
  have fDD := fit aDD (by decide)
  have top5 : w32 t5.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0 := by
    rw [k5.word (by omega_arith) (by simp) (by decide) fDD, top4, top3, k2.word (by omega_arith) (by decide) (by simp) fDD, m1,
      h.ddTop]
  refine ⟨divGeom_ctx h5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) d5, ?_⟩
  refine WP.mono (divR_ok b5 h5 (.inr rfl) d5 top5) fun t ⟨bt, k, v⟩ => ?_
  obtain ⟨V, mV, iV⟩ := h.mask
  have tr : ∀ j, j < nArr → j ∉ [aDQ, aDD, aDR3, aDT] →
      num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := fun j hj hn => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [k.num (by simp; omega_arith) (by simp) (fit j hj), K5.num (by simp; omega_arith) (by decide) (fit j hj), m1]
  refine ⟨bt, fun pos => ?_, fun pos => ?_, ⟨V, ?_, ?_⟩⟩
  · rw [tr _ (by decide) (by decide)]; exact h.dp pos
  · have dd5 : num t5.mem (cvB s0) (cvW s0) aDD = 2 * (cvQ s0 / 2) := by
      rw [k5.num (by simp) (by decide) fDD, e4, e3, k2.num (by decide) (by simp) (fit _ (by decide)), m1, h.q]
    have dq5 : num t5.mem (cvB s0) (cvW s0) aDQ = cvD s0 := by
      rw [k5.num (by simp) (by decide) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
        k3.num (by decide) (by simp) (fit _ (by decide)), e2, m1, h.d]
    rw [v (by rw [dd5]; exact pos), dq5, dd5]
  · rw [k.slot (by decide) (by simp), K5.slot (by decide) (by decide), m1, mV]
  · rw [tr _ (by decide) (by decide)]; exact iV

theorem divQ_ok {s0 s : State} {X₁ X₂ : Nat} (h : StE s0 X₁ X₂ s) :
    WP isa (.seq divQ VG.Impl.Rsa.Arm.Div.code) s (StG s0 X₁ X₂) :=
  WP.seq_iff.mpr (WP.mono (divQ_pre_ok h) fun _ h => h.2)

end VG.Proof.Rsa.Arm.CrtValues

end

end

/-! # `vg_rsa_crt_values` on ARMv7: the results written out -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- What the outputs and the result are, from the mask `c` and the values computed. -/
structure Outs (s0 : State) (t : State) (c : Bool) (R₂ R₃ X : Nat) : Prop where
  done : Done s0 t
  ret : t.gpr .r0 = if c then 1 else 0
  dp : outDp t.mem s0 = if c then Spec.Rsa.i2osp (R₂ % 2 ^ (8 * cvPl s0)) (cvPl s0) else List.replicate (cvPl s0) 0
  dq : outDq t.mem s0 = if c then Spec.Rsa.i2osp (R₃ % 2 ^ (8 * cvQl s0)) (cvQl s0) else List.replicate (cvQl s0) 0
  qi : outQi t.mem s0 = if c then Spec.Rsa.i2osp (X % 2 ^ (8 * cvPl s0)) (cvPl s0) else List.replicate (cvPl s0) 0

theorem num_frame {s0 : State} (pre : CvPre s0) {m m' : Mem} {R : Region} (hf : Frame [R] m m')
    (hd : R.Disjoint (rS s0)) {j : Nat} (hj : j < nArr) :
    num m' (cvB s0) (cvW s0) j = num m (cvB s0) (cvW s0) j := by
  obtain fa := Nat.le_trans (arr_end (w := cvW s0) hj) pre.fits
  have fS := pre.fS
  have eZ : cvZ s0 = (stackArg s0 11).toNat * 8 := rfl
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  refine val32_congr fun i hi => congrArg BitVec.toNat (hf.readW (r := rS s0)
    (Offset.contains_base _ (by omega_using [fa, eZ, hS, hi]) (by omega_using [fa, eZ, hS, hi])) (by simpa using hd.symm) (by decide))

theorem slot_frame' {s0 : State} (pre : CvPre s0) {m m' : Mem} {R : Region} (hf : Frame [R] m m')
    (hd : R.Disjoint (rS s0)) {e : Nat} (he : e + 4 ≤ hdr) :
    slot m' (cvB s0) e = slot m (cvB s0) e := by
  have := pre.fits
  have fS := pre.fS
  have eZ : cvZ s0 = (stackArg s0 11).toNat * 8 := rfl
  obtain hz : hdr ≤ cvZ s0 := Nat.le_trans (Nat.le_add_right _ _) this
  exact congrArg BitVec.toNat (hf.readW (r := rS s0) (Offset.contains_base _ (by omega_using [he, eZ, hz]) (by simp only [hdr] at he; omega_using [he]))
    (by simpa using hd.symm) (by decide))

theorem ite_mask (c : Bool) {α : Type} (a b : α) : (if (if c then 1 else 0 : Nat) = 1 then a else b) = if c then a else b := by
  cases c <;> rfl

/-- What the stores need: the mask in `sMask`. -/
structure StM (s0 : State) (X₁ X₂ : Nat) (s : State) : Prop where
  base : Base s0 s
  mask : ∃ V, slot s.mem (cvB s0) sMask = (if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then 1 else 0) ∧
    (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
      (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧
      num s.mem (cvB s0) (cvW s0) 3 < cvM s0)

theorem StG.toM {s0 s : State} {X₁ X₂ : Nat} (h : StG s0 X₁ X₂ s) : StM s0 X₁ X₂ s := ⟨h.base, h.mask⟩

/-- The glue: the working space, and `dp` and `dq` from the header. -/
def glue : List Instr := ctx ++ [.ldr .r10 .r8 sDp, .ldr .r12 .r8 sDq]

theorem glue_ok {s0 s : State} {X₁ X₂ : Nat} (h : StM s0 X₁ X₂ s) :
    WP isa (.block glue) s fun u => Base s0 u ∧ Ws u (cvB s0) (cvZ s0) (cvW s0) nArr ∧
    u.gpr .r10 = s0.gpr .r0 ∧ u.gpr .r12 = s0.gpr .r2 ∧
    WP isa stores u fun t => ∃ V,
      (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
        (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧ num s.mem (cvB s0) (cvW s0) 3 < cvM s0) ∧
      Outs s0 t (maskOf (cvP s0) (cvQ s0) X₁ X₂ V) (num s.mem (cvB s0) (cvW s0) aDR2)
        (num s.mem (cvB s0) (cvW s0) aDR3) (num s.mem (cvB s0) (cvW s0) 3) := by
  have pre := h.base.pre
  obtain ⟨V, mV, iV⟩ := h.mask
  unfold glue
  refine ctx_ok h.base fun t1 b1 h1 r1 m1 => ?_
  refine wp_ldrSlot h1 (d := sDp) (by decide) fun t2 u2 => ?_
  refine wp_ldrSlot (h1.of_upd u2 (by decide) (by decide) (by decide)) (d := sDq) (by decide) fun t3 u3 => WP.block_nil ?_
  obtain h3 := (h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)
  obtain b3 := b1.of_rest ((u2.rest (ws := [.r10, .r12]) (by simp)).trans (u3.rest (by simp))) (u3.mem.trans u2.mem)
  obtain p10 : t3.gpr .r10 = s0.gpr .r0 := by
    rw [u3.other _ (by decide), u2.gpr, m1]
    exact BitVec.eq_of_toNat_eq (h.base.saved 9 (by decide))
  obtain p12 : t3.gpr .r12 = s0.gpr .r2 := by
    rw [u3.gpr, u2.mem, m1]
    exact BitVec.eq_of_toNat_eq (h.base.saved 10 (by decide))
  refine ⟨b3, h3, p10, p12, ?_⟩
  have d3 := b3.done
  have w16 := pre.w16
  have kb := pre.kb
  obtain hkw : ∀ k, k < cvK s0 → k ≤ 4 * cvW s0 := fun k hk => by simp only [cvW] at *; omega_using [hk]
  obtain mb : slot t3.mem (cvB s0) sMask ≤ 1 := by
    rw [u3.mem, u2.mem, m1, mV]; split <;> omega_using []
  unfold stores
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_ldrSp d3.rA_mem (by rw [d3.sp]; exact pre.sp48) (i := 5) (by decide) fun t4 u4 => WP.block_nil ?_
  obtain d4 := d3.of_rest (u4.rest (ws := [.r11]) (by simp)) u4.mem
  obtain h4 := h3.of_upd u4 (by decide) (by decide) (by decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok d4 h4 (j := aDR2) (by decide) (R := rDp s0) (.inl rfl) (dst := s0.gpr .r0)
    (k := cvPl s0) (by simp [rDp, reg, pre.dpLen]) pre.pl1 (hkw _ pre.pl2) (by rw [← pre.dpLen]; exact pre.fDp)
    (by rw [u4.other _ (by decide), p10]) (by rw [u4.gpr, d3.arg (by decide)]; simp)
    (by rw [u4.mem]; exact mb)) fun t5 ⟨d5, h5, o5, f5, r5⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_mov (op2_reg _ _) fun t6 u6 => ?_
  obtain d6 := d5.of_rest (u6.rest (ws := [.r10]) (by simp)) u6.mem
  refine wp_ldrSp d6.rA_mem (by rw [d6.sp]; exact pre.sp48) (i := 7) (by decide) fun t7 u7 => WP.block_nil ?_
  obtain d7 := d6.of_rest (u7.rest (ws := [.r11]) (by simp)) u7.mem
  obtain h7 := (h5.of_upd u6 (by decide) (by decide) (by decide)).of_upd u7 (by decide) (by decide) (by decide)
  obtain mb5 : slot t5.mem (cvB s0) sMask = slot t3.mem (cvB s0) sMask := by
    rw [slot_frame' pre f5 pre.dpS (by decide), u4.mem]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok d7 h7 (j := aDR3) (by decide) (R := rDq s0) (.inr (.inl rfl)) (dst := s0.gpr .r2)
    (k := cvQl s0) (by simp [rDq, reg, pre.dqLen]) pre.ql1 (hkw _ pre.ql2) (by rw [← pre.dqLen]; exact pre.fDq)
    (by rw [u7.other _ (by decide), u6.gpr, r5.gpr _ (by decide), u4.other _ (by decide), p12])
    (by rw [u7.gpr, d6.arg (by decide)]; simp)
    (by rw [u7.mem, u6.mem, mb5]; exact mb)) fun t8 ⟨d8, h8, o8, f8, r8⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_ldrSp d8.rA_mem (by rw [d8.sp]; exact pre.sp48) (i := 0) (by decide) fun t9 u9 => ?_
  obtain d9 := d8.of_rest (u9.rest (ws := [.r10]) (by simp)) u9.mem
  refine wp_ldrSp d9.rA_mem (by rw [d9.sp]; exact pre.sp48) (i := 5) (by decide) fun t10 u10 => WP.block_nil ?_
  obtain d10 := d9.of_rest (u10.rest (ws := [.r11]) (by simp)) u10.mem
  obtain h10 := (h8.of_upd u9 (by decide) (by decide) (by decide)).of_upd u10 (by decide) (by decide) (by decide)
  obtain mb8 : slot t8.mem (cvB s0) sMask = slot t3.mem (cvB s0) sMask := by
    rw [slot_frame' pre f8 pre.dqS (by decide), u7.mem, u6.mem, mb5]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok d10 h10 (j := 3) (by decide) (R := rQi s0) (.inr (.inr rfl)) (dst := stackArg s0 0)
    (k := cvPl s0) (by simp [rQi, reg, pre.qiLen]) pre.pl1 (hkw _ pre.pl2) (by rw [← pre.qiLen]; exact pre.fQi)
    (by rw [u10.other _ (by decide), u9.gpr, d8.arg (by decide)])
    (by rw [u10.gpr, d9.arg (by decide)]; simp)
    (by rw [u10.mem, u9.mem, mb8]; exact mb)) fun t11 ⟨d11, h11, o11, f11, r11⟩ => ?_
  refine wp_ldrSlot h11 (d := sMask) (by decide) fun t u12 => WP.block_nil ?_
  obtain mb11 : slot t11.mem (cvB s0) sMask = slot t3.mem (cvB s0) sMask := by
    rw [slot_frame' pre f11 pre.qiS (by decide), u10.mem, u9.mem, mb8]
  obtain ms : slot t3.mem (cvB s0) sMask = if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then 1 else 0 := by
    rw [u3.mem, u2.mem, m1, mV]
  obtain n3 : ∀ j, j < nArr → num t3.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := fun j _ => by
    rw [u3.mem, u2.mem, m1]
  refine ⟨V, iV, ⟨d11.of_rest (u12.rest (ws := [.r0]) (by simp)) u12.mem, ?_, ?_, ?_, ?_⟩⟩
  · rw [u12.gpr]
    apply BitVec.eq_of_toNat_eq
    change slot t11.mem (cvB s0) sMask = _
    rw [mb11, ms]; split <;> rfl
  · have lp := pre.pl2; have lq := pre.ql2
    obtain eDp : (⟨State.addr (s0.gpr .r0), cvPl s0⟩ : Region) = rDp s0 := by simp [rDp, reg, pre.dpLen]
    simp only [outDp]
    rw [u12.mem, bytes_frame f11 (by rw [eDp]; simpa using pre.dpQi) (by omega_using [kb, lp]), u10.mem, u9.mem,
      bytes_frame f8 (by rw [eDp]; simpa using pre.dpDq) (by omega_using [kb, lp]), u7.mem, u6.mem, o5, u4.mem, ms, ite_mask,
      n3 _ (by decide)]
  · have lq := pre.ql2
    obtain eDq : (⟨State.addr (s0.gpr .r2), cvQl s0⟩ : Region) = rDq s0 := by simp [rDq, reg, pre.dqLen]
    simp only [outDq]
    rw [u12.mem, bytes_frame f11 (by rw [eDq]; simpa using pre.dqQi) (by omega_using [kb, lq]), u10.mem, u9.mem, o8,
      u7.mem, u6.mem, mb5, ms, ite_mask, num_frame pre f5 pre.dpS (by decide), u4.mem, n3 _ (by decide)]
  · simp only [outQi]
    rw [u12.mem, o11, u10.mem, u9.mem, mb8, ms, ite_mask, num_frame pre f8 pre.dqS (by decide), u7.mem, u6.mem,
      num_frame pre f5 pre.dpS (by decide), u4.mem, n3 _ (by decide)]

theorem finish_ok {s0 s : State} {X₁ X₂ : Nat} (h : StM s0 X₁ X₂ s) :
    WP isa (.seq (.block glue) stores) s fun t => ∃ V,
      (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
        (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧ num s.mem (cvB s0) (cvW s0) 3 < cvM s0) ∧
      Outs s0 t (maskOf (cvP s0) (cvQ s0) X₁ X₂ V) (num s.mem (cvB s0) (cvW s0) aDR2)
        (num s.mem (cvB s0) (cvW s0) aDR3) (num s.mem (cvB s0) (cvW s0) 3) :=
  WP.seq_iff.mpr (WP.mono (glue_ok h) fun _ h => h.2.2.2.2)

end VG.Proof.Rsa.Arm.CrtValues

end

end

/-! # `vg_rsa_crt_values` on ARMv7: a balanced key, by words

`shapeCv_ok`: Z exactly for a balanced key (`BalCv`); `midW_ok`: for one, the
checks and the values by words (`KeyDiv.mulLo`, `KeyDiv.divW`), which leave the
mask of `p` odd, `p q mod 2^(32 w) = n` and the inverse's gcd 1, and the
remainders of `d` modulo `p - 1` and `q - 1` with their top words made not zero
(`fixT`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- A balanced key: `p` and `q` of `2 w` bytes, `w` even. -/
abbrev BalCv (s0 : State) : Prop := cvPl s0 = 2 * cvW s0 ∧ cvQl s0 = 2 * cvW s0 ∧ cvW s0 % 2 = 0

theorem StA.of_rest {s0 s t : State} (h : StA s0 s) {ws : List Reg} (r : Rest ws s t) (m : t.mem = s.mem)
    (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide) (h9 : .r9 ∉ ws := by decide) : StA s0 t :=
  ⟨h.base.of_rest r m, h.ws.rest r h7 h8 h9, m ▸ h.count, m ▸ h.n, m ▸ h.p, m ▸ h.q, m ▸ h.d,
    fun j hj => m ▸ h.zeros j hj⟩

/-- `shapeCv`: Z exactly for a balanced key; only `r0`–`r3`, `r11` and the flags change. -/
theorem shapeCv_ok {s0 s : State} (h : StA s0 s) :
    WP isa (.block shapeCv) s fun t => StA s0 t ∧ t.z = decide (BalCv s0) := by
  have pre := h.base.pre
  have kb := pre.kb
  have sp := pre.sp48
  rw [h.base.sp.symm] at sp
  unfold shapeCv VG.Impl.Rsa.Arm.KeyDiv.shape
  refine wp_ldrSp h.base.rA_mem sp (i := 3) (by decide) fun s1 u1 => ?_
  have b1 := h.base.of_rest (u1.rest (ws := [.r11]) (by simp)) u1.mem
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  have b3 := b1.of_rest ((u2.rest (ws := [.r3]) (by simp)).trans (u3.rest (by simp))) (u3.mem.trans u2.mem)
  refine wp_ldrSp b3.rA_mem (by rw [u3.sp, u2.sp, u1.sp]; exact sp) (i := 5) (by decide) fun s4 u4 => ?_
  have b4 := b3.of_rest (u4.rest (ws := [.r0]) (by simp)) u4.mem
  refine wp_ldrSp b4.rA_mem (by rw [u4.sp, u3.sp, u2.sp, u1.sp]; exact sp) (i := 7) (by decide) fun s5 u5 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun s7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun s9 u9 => ?_
  refine wp_dp (op2_imm (by decide)) fun s10 u10 => ?_
  refine wp_dp (op2_reg _ _) fun s11 u11 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ut zt => WP.block_nil ?_
  have R : Rest [.r0, .r1, .r2, .r3, .r11] s t :=
    (((((((((((u1.rest (by simp)).trans (u2.rest (by simp))).trans (u3.rest (by simp))).trans
      (u4.rest (by simp))).trans (u5.rest (by simp))).trans (u6.rest (by simp))).trans (u7.rest (by simp))).trans
      (u8.rest (by simp))).trans (u9.rest (by simp))).trans (u10.rest (by simp))).trans (u11.rest (by simp))).trans
      (ut.rest _)
  have m : t.mem = s.mem := by
    rw [ut.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨h.of_rest R m, ?_⟩
  have a3 : stackArg s 3 = stackArg s0 3 := h.base.arg (by decide)
  have a5 : stackArg s3 5 = stackArg s0 5 := b3.arg (by decide)
  have a7 : stackArg s4 7 = stackArg s0 7 := b4.arg (by decide)
  have e0 : s11.gpr .r0 = (((stackArg s0 5 ^^^ (((stackArg s0 3 + 3) >>> 2) <<< 1)) |||
      (stackArg s0 7 ^^^ (((stackArg s0 3 + 3) >>> 2) <<< 1))) ||| (((stackArg s0 3 + 3) >>> 2) &&& 1)) := by
    simp (disch := decide) only [u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr,
      u1.gpr, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, dpVal, a3, a5, a7]
  rw [zt, e0]
  exact VG.Proof.Rsa.Arm.KeyCheck.shape_z kb.2

/-- The first comparison's quotient for a balanced key: `q` exactly when `p q mod 2^(32 w) = n`. -/
abbrev xW (s0 : State) : Nat :=
  if cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0) = cvN s0 then cvQ s0 else cvQ s0 + 1

/-- `fixT` of `p - 1` and of `q - 1`, the divisors of the divisions by words. -/
abbrev fP (s0 : State) : Nat := VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvP s0 / 2))
abbrev fQ (s0 : State) : Nat := VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvQ s0 / 2))

theorem slot16 {s0 : State} {m : Mem} (pre : CvPre s0)
    (h : m.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)) : slot m (cvB s0) 16 = cvW s0 := by
  have := pre.w16
  simp only [slot, w32]; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])]

theorem bytes_lt_half {s0 : State} {b : List Byte} (hl : b.length = 2 * cvW s0) (hw : cvW s0 % 2 = 0) :
    Spec.Rsa.os2ip b < 2 ^ (32 * (cvW s0 / 2)) := by
  have := VG.Proof.Bignum.os2ip_lt b
  rw [hl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  rw [show 32 * (cvW s0 / 2) = 8 * (2 * cvW s0) by omega_using [hw]]
  exact this

theorem BalCv.p_lt {s0 : State} (hB : BalCv s0) : cvP s0 < 2 ^ (32 * (cvW s0 / 2)) :=
  bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.1) hB.2.2

theorem BalCv.q_lt {s0 : State} (hB : BalCv s0) : cvQ s0 < 2 ^ (32 * (cvW s0 / 2)) :=
  bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.2.1) hB.2.2

/-- Before the product: the loads, and `p` odd. -/
structure SA (s0 s : State) : Prop where
  base : Base s0 s
  ws : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  podd : slot s.mem (cvB s0) sPodd = cvP s0 % 2
  n : num s.mem (cvB s0) (cvW s0) aDQ = cvN s0
  p : num s.mem (cvB s0) (cvW s0) aP = cvP s0
  q : num s.mem (cvB s0) (cvW s0) aQ = cvQ s0
  d : num s.mem (cvB s0) (cvW s0) aD = cvD s0
  ddTop : w32 s.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0
  zeros : ∀ j ∈ [0, 2, 3, aZero, aOne], num s.mem (cvB s0) (cvW s0) j = 0

theorem SA.mulPre {s0 s : State} (h : SA s0 s) (hB : BalCv s0) :
    VG.Proof.Rsa.Arm.KeyDiv.MulPre (cvB s0) (cvZ s0) (cvW s0) nArr aQ s :=
  ⟨h.ws, slot16 h.base.pre h.count, by rw [h.q]; exact hB.q_lt, h.zeros 0 (by decide)⟩

/-- `ctx`, and `p` odd. -/
theorem oddW_ok {s0 s : State} (h : StA s0 s) : WP isa (.block (ctx ++ bitOf sPodd aP)) s (SA s0) := by
  rw [← List.append_nil (bitOf sPodd aP), ← List.append_assoc]
  refine ctx_ok h.base fun t1 b1 h1 r1 m1 => ?_
  have fit := fun j (hj : j < nArr) => h1.fit64 (j := j) hj
  refine bitOf_ok h1 (j := aP) (sl := sPodd) (by decide) (by decide) (by decide) fun t2 h2 k2 e2 r2 =>
    WP.block_nil ?_
  have K1 : ∀ j, j < nArr → num t2.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j :=
    fun j hj => by rw [k2.num (by simp) (by decide) (fit j hj), m1]
  refine ⟨b1.keep k2 (by decide) (by decide) (by decide) r2.sp r2.rd r2.wr, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.count, ← m1]
    exact BitVec.eq_of_toNat_eq (k2.slot (e := 16) (by decide) (by decide))
  · rw [e2, m1, h.p]
  · rw [K1 _ (by decide), h.n]
  · rw [K1 _ (by decide), h.p]
  · rw [K1 _ (by decide), h.q]
  · rw [K1 _ (by decide), h.d]
  · rw [k2.word (by simp only [S]; omega_arith) (by simp) (by decide) (fit _ (by decide)), m1]
    exact top_of_full (h.zeros aDD (by decide))
  · intro j hj
    have hj' : j < nArr := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [K1 _ hj']
    exact num_of_zero (h.zeros j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide))

/-- The product `p q mod 2^(32 w)`. -/
theorem mulW_ok {s0 s : State} (h : SA s0 s) (hB : BalCv s0) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ) s fun t => SA s0 t ∧
      num t.mem (cvB s0) (cvW s0) aDR = cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0) := by
  have pre := h.base.pre
  have w16 := pre.w16
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.mulLo_ok h.ws (o := aDR) (x := aP) (y := aQ) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (slot16 pre h.count) hB.2.2 (by omega_using [w16]) (n := none)
    h.p h.q hB.q_lt (h.zeros 0 (by decide))) fun t ⟨ht, e, k, r⟩ => ⟨?_, by rw [e, Nat.mod_eq_of_lt hB.p_lt]⟩
  have K1 : ∀ j, j < nArr → j ≠ aDR → num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j :=
    fun j hj hn => k.num (by simpa using Ne.symm hn) (by decide) (fit j hj)
  refine ⟨h.base.keep k (by decide) (by decide) (by decide) r.sp r.rd r.wr, ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.count]; exact BitVec.eq_of_toNat_eq (k.slot (e := 16) (by decide) (by decide))
  · rw [k.slot (by decide) (by decide), h.podd]
  · rw [K1 _ (by decide) (by decide), h.n]
  · rw [K1 _ (by decide) (by decide), h.p]
  · rw [K1 _ (by decide) (by decide), h.q]
  · rw [K1 _ (by decide) (by decide), h.d]
  · rw [k.word (by simp only [S]; omega_arith) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
  · intro j hj
    have hj' : j < nArr ∧ j ≠ aDR := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [K1 _ hj'.1 hj'.2]; exact h.zeros j hj

/-- The two comparisons: `p q mod 2^(32 w) = n`, and the remainder 0. -/
theorem cmpW_ok {s0 s : State} (h : SA s0 s)
    (e : num s.mem (cvB s0) (cvW s0) aDR = cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0)) :
    WP isa (seqs [eqS sE1 aDR aDQ aT1, eqS sE2 aZero aZero aT1]) s (StC1 s0 (xW s0) 0) := by
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h.ws (d := sE1) (a := aDR) (b := aDQ) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun t4 ⟨h4, k4, e4, r4⟩ => ?_
  refine WP.mono (eqS_ok h4 (d := sE2) (a := aZero) (b := aZero) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  have K : Keep (cvB s0) (cvW s0) [aT1] [sT, sE1, sE2] s.mem t5.mem := k4.mono.trans k5.mono
  have R : Rest opRegs s t5 := r4.trans r5
  have K1 : ∀ j, j < nArr → j ≠ aT1 → num t5.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j :=
    fun j hj hn => K.num (by simpa using Ne.symm hn) (by decide) (fit j hj)
  refine ⟨h.base.keep K (by decide) (by decide) (by decide) R.sp R.rd R.wr, h5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.count]; exact BitVec.eq_of_toNat_eq (K.slot (e := 16) (by decide) (by decide))
  · rw [K.slot (by decide) (by decide), h.podd]
  · rw [k5.slot (by decide) (by decide), e4, e, h.n]
    by_cases c : cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0) = cvN s0 <;> simp [xW, c]
  · rw [e5]; simp
  · rw [K1 _ (by decide) (by decide), h.p]
  · rw [K1 _ (by decide) (by decide), h.q]
  · rw [K1 _ (by decide) (by decide), h.d]
  · rw [K.word (by simp only [S]; omega_arith) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
  · intro j hj
    have hj' : j < nArr ∧ j ≠ aT1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl | rfl <;> decide
    rw [K1 _ hj'.1 hj'.2]
    exact h.zeros j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega_using [hj])

/-- Between the divisions by words: the mask, `q`, `d` and the zero array. -/
structure SW (s0 : State) (X₁ : Nat) (s : State) : Prop where
  base : Base s0 s
  ws : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  q : num s.mem (cvB s0) (cvW s0) aQ = cvQ s0
  d : num s.mem (cvB s0) (cvW s0) aD = cvD s0
  zero : num s.mem (cvB s0) (cvW s0) 0 = 0
  mask : ∃ V, slot s.mem (cvB s0) sMask = (if maskOf (cvP s0) (cvQ s0) X₁ 0 V then 1 else 0) ∧
    (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
      (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧
      num s.mem (cvB s0) (cvW s0) 3 < cvM s0)

/-- `SW` after code that keeps every array but `js` (none of `aQ`, `aD`, 0, 3) and the header but
`ds`. -/
theorem SW.keep {s0 s t : State} {X₁ : Nat} (h : SW s0 X₁ s) {js ds : List Nat}
    (k : Keep (cvB s0) (cvW s0) js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hj : ∀ j ∈ js, j ≠ aQ ∧ j ≠ aD ∧ j ≠ 0 ∧ j ≠ 3) (hds : ∀ d ∈ ds, 64 ≤ d ∧ d + 4 ≤ hdr ∧ (sMask + 4 ≤ d ∨ d + 4 ≤ sMask))
    (W : Ws t (cvB s0) (cvZ s0) (cvW s0) nArr) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    SW s0 X₁ t := by
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  have hd1 : ∀ d ∈ ds, d + 4 ≤ hdr := fun d hd => (hds d hd).2.1
  have K1 : ∀ i, i < nArr → (∀ j ∈ js, j ≠ i) → num t.mem (cvB s0) (cvW s0) i = num s.mem (cvB s0) (cvW s0) i :=
    fun i hi hn => k.num hn hd1 (fit i hi)
  obtain ⟨V, mV, iV⟩ := h.mask
  refine ⟨h.base.keep k hjs (fun d hd => Or.inr (hds d hd).1) hd1 sp rd wr, W, ?_,
    by rw [K1 _ (by decide) fun j hj' => (hj j hj').1, h.q], by rw [K1 _ (by decide) fun j hj' => (hj j hj').2.1, h.d],
    by rw [K1 _ (by decide) fun j hj' => (hj j hj').2.2.1, h.zero], V, ?_, ?_⟩
  · rw [← h.count]
    exact BitVec.eq_of_toNat_eq (k.slot (e := 16) (by decide) fun d hd => Or.inl (by have := (hds d hd).1; omega_using [this]))
  · rw [k.slot (by decide) fun d hd => (hds d hd).2.2, mV]
  · rw [K1 _ (by decide) fun j hj' => (hj j hj').2.2.2]; exact iV

theorem SW.divPre {s0 s : State} {X₁ : Nat} (h : SW s0 X₁ s) {M : Nat}
    (hM : num s.mem (cvB s0) (cvW s0) aDD = VG.Proof.Rsa.fixT (cvW s0 / 2) M) (hMl : M < 2 ^ (32 * (cvW s0 / 2))) :
    VG.Proof.Rsa.Arm.KeyDiv.DivPre (cvB s0) (cvZ s0) (cvW s0) nArr aDD s := by
  have w16 := h.base.pre.w16
  have l := VG.Proof.Rsa.fixT_lt (k := cvW s0 / 2) (by omega_using [w16]) hMl
  refine ⟨h.ws, slot16 h.base.pre h.count, by rw [hM]; exact l,
    VG.Proof.Rsa.Arm.KeyCheck.top_word_pos (k := cvW s0 / 2 - 1) (n := cvW s0) (by omega_using [w16]) hM
      (by rw [show cvW s0 / 2 - 1 + 1 = cvW s0 / 2 by omega_using [w16]]; exact l) VG.Proof.Rsa.fixT_ge, h.zero, trivial⟩

/-- `[aDD] := fixT [d']` cleared of its low bit. -/
theorem setW_ok {s0 s : State} {X₁ : Nat} (h : SW s0 X₁ s) {d' : Nat} (hd : d' ∈ [aP, aQ])
    {Dv : Nat} (hD : num s.mem (cvB s0) (cvW s0) d' = Dv) (hDl : Dv < 2 ^ (32 * (cvW s0 / 2))) :
    WP isa (seqs [copy aDD d', .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)]) s fun t =>
      SW s0 X₁ t ∧ num t.mem (cvB s0) (cvW s0) aDD = VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (Dv / 2)) ∧
      ∀ j, j < nArr → j ≠ aDD → num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := by
  have w16 := h.base.pre.w16
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  have hd' : d' < nArr ∧ d' ≠ aDD := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl <;> decide
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h.ws (o := aDD) (a := d') (by decide) hd'.1 (by decide) (Ne.symm hd'.2))
    fun t1 ⟨h1, k1, e1, r1, _⟩ => ?_
  refine clrLow_ok h1 (j := aDD) (by decide) (by decide) fun t2 h2 k2 e2 r2 _ => ?_
  have D2 : num t2.mem (cvB s0) (cvW s0) aDD = 2 * (Dv / 2) := by rw [e2, e1, hD]
  refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.fixTopW_ok h2 (m := aDD) (by decide) (by decide) D2
    (Nat.lt_of_le_of_lt (by omega_using []) hDl) (by omega_using [w16])) fun t ⟨ht, k3, e3, r3, _⟩ => ?_
  have K : Keep (cvB s0) (cvW s0) [aDD] [] s.mem t.mem := k1.trans (k2.trans k3)
  have R : Rest opRegs s t := r1.trans (r2.trans (r3.mono (by decide)))
  refine ⟨h.keep K (by decide) (by decide) (by decide) ht R.sp R.rd R.wr, e3, fun j hj hn =>
    K.num (by simpa using Ne.symm hn) (by decide) (fit j hj)⟩

/-- `[r] := [aD] mod [aDD]` by words. -/
theorem remW_ok {s0 s : State} {X₁ : Nat} (h : SW s0 X₁ s) {r : Nat} (hr : r ∈ [aDR2, aDR3]) {M : Nat}
    (hM : num s.mem (cvB s0) (cvW s0) aDD = VG.Proof.Rsa.fixT (cvW s0 / 2) M) (hMl : M < 2 ^ (32 * (cvW s0 / 2))) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.divW aD r aDD aDQ aDT aT1) s fun t =>
      SW s0 X₁ t ∧ num t.mem (cvB s0) (cvW s0) r = cvD s0 % VG.Proof.Rsa.fixT (cvW s0 / 2) M ∧
      ∀ j, j < nArr → j ∉ [r, aDQ, aT1, aDT] → num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := by
  have w16 := h.base.pre.w16
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  have hr' : r < nArr ∧ r ≠ aD ∧ r ≠ aDD ∧ r ≠ aDQ ∧ r ≠ aT1 ∧ r ≠ aDT ∧ r ≠ 0 ∧ r ≠ aQ ∧ r ≠ 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
  obtain ⟨W, c, ML, T0, z, -⟩ := h.divPre hM hMl
  refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.divW_ok W (a := aD) (r := r) (m := aDD) (t := aDQ) (nm := aDT)
    (u := aT1) (by decide) hr'.1 (by decide) (by decide) (by decide) (by decide) (by decide) hr'.2.1
    hr'.2.2.2.1 hr'.2.2.2.2.1 (by decide) (Ne.symm hr'.2.2.1) (by decide) (by decide)
    (Ne.symm hr'.2.2.2.2.2.1) (by decide) (by decide) (by decide) hr'.2.2.2.2.2.2.1 (by decide) (by decide)
    (by decide) (by omega_using [w16]) c hM (by rw [← hM]; exact ML) T0 z) fun t ⟨ht, et, _, kt, rt⟩ => ?_
  refine ⟨h.keep kt (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> first | decide | exact hr'.1)
    (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> first | decide | exact ⟨hr'.2.2.2.2.2.2.2.1, hr'.2.1, hr'.2.2.2.2.2.2.1,
        hr'.2.2.2.2.2.2.2.2⟩) (by decide) ht rt.sp rt.rd rt.wr, by rw [et, h.d], fun j hj hn =>
    kt.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj)⟩

/-- What a balanced key's checks leave: the mask of `p` odd, `p q mod 2^(32 w) = n` (for the
quotient `xW`, and the remainder 0) and the inverse, and the remainders by words. -/
def MidW (s0 t : State) : Prop :=
  StM s0 (xW s0) 0 t ∧
  num t.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % fP s0 ∧ num t.mem (cvB s0) (cvW s0) aDR3 = cvD s0 % fQ s0

/-- The comparisons, the inverse and `checks`' set-up, the zero array again, and `fixT (p - 1)`. -/
theorem chunkW_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} {s0 s : State} (h : SA s0 s) (hB : BalCv s0)
    (e : num s.mem (cvB s0) (cvW s0) aDR = cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0)) :
    WP isa (seqs (chunkW um)) s fun t => SW s0 (xW s0) t ∧ num t.mem (cvB s0) (cvW s0) aDD = fP s0 := by
  rw [show chunkW um = [eqS sE1 aDR aDQ aT1, eqS sE2 aZero aZero aT1] ++ (invSetup ++ (checksB um ++
    [copy 0 aZero, copy aDD aP, .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)])) from rfl,
    wp_seqs_append (List.cons_ne_nil _ _) (by unfold invSetup; simp)]
  refine WP.mono (cmpW_ok h e) fun t1 h1 => ?_
  rw [wp_seqs_append (by unfold invSetup; simp) (by unfold checksB; simp)]
  refine WP.mono (invSetup_ok h1) fun t2 h2 => ?_
  rw [wp_seqs_append (by unfold checksB; simp) (List.cons_ne_nil _ _)]
  refine WP.mono (checksB_ok h2) fun t3 h3 => ?_
  have fit := fun j (hj : j < nArr) => h3.ws.fit64 (j := j) hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3.ws (o := 0) (a := aZero) (by decide) (by decide) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  obtain ⟨V, mV, iV⟩ := h3.mask
  have s4 : SW s0 (xW s0) t4 := by
    refine ⟨h3.base.keep k4 (by decide) (by decide) (by decide) r4.sp r4.rd r4.wr, h4, ?_,
      by rw [k4.num (by decide) (by decide) (fit _ (by decide)), h3.q],
      by rw [k4.num (by decide) (by decide) (fit _ (by decide)), h3.d], by rw [e4, h3.zero], V, ?_, ?_⟩
    · rw [← h3.count]; exact BitVec.eq_of_toNat_eq (k4.slot (e := 16) (by decide) (by decide))
    · rw [k4.slot (by decide) (by decide), mV]
    · rw [k4.num (by decide) (by decide) (fit _ (by decide))]; exact iV
  exact WP.mono (setW_ok s4 (d' := aP) (by decide)
    (by rw [k4.num (by decide) (by decide) (fit _ (by decide)), h3.p]) hB.p_lt) fun t ⟨ht, et, _⟩ => ⟨ht, et⟩

theorem midW_eq (um : Bool) : midW um = seqs (([.block (ctx ++ bitOf sPodd aP), VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ] :
    List (Prog isa)) ++ (chunkW um ++ ([VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR2 aDD aDQ aDT aT1, copy aDD aQ,
      .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD), VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR3 aDD aDQ aDT aT1] :
        List (Prog isa)))) :=
  rfl

/-- After the first division by words. -/
theorem div2W_ok {s0 s : State} (h : SW s0 (xW s0) s) (hB : BalCv s0)
    (e : num s.mem (cvB s0) (cvW s0) aDD = fP s0) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR2 aDD aDQ aDT aT1) s fun t =>
      SW s0 (xW s0) t ∧ num t.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % fP s0 :=
  WP.mono (remW_ok h (r := aDR2) (by decide) e (Nat.lt_of_le_of_lt (by omega_using []) hB.p_lt)) fun _ ⟨ht, et, _⟩ => ⟨ht, et⟩

theorem setQW_ok {s0 s : State} (h : SW s0 (xW s0) s) (hB : BalCv s0)
    (e : num s.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % fP s0) :
    WP isa (seqs [copy aDD aQ, .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)]) s fun t =>
      SW s0 (xW s0) t ∧ num t.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % fP s0 ∧
      num t.mem (cvB s0) (cvW s0) aDD = fQ s0 :=
  WP.mono (setW_ok h (d' := aQ) (by decide) h.q hB.q_lt) fun _ ⟨ht, et, k⟩ =>
    ⟨ht, by rw [k _ (by decide) (by decide), e], et⟩

theorem div3W_ok {s0 s : State} (h : SW s0 (xW s0) s) (hB : BalCv s0)
    (e2 : num s.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % fP s0) (e : num s.mem (cvB s0) (cvW s0) aDD = fQ s0) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR3 aDD aDQ aDT aT1) s (MidW s0) :=
  WP.mono (remW_ok h (r := aDR3) (by decide) e (Nat.lt_of_le_of_lt (by omega_using []) hB.q_lt)) fun _ ⟨ht, et, k⟩ =>
    ⟨⟨ht.base, ht.mask⟩, by rw [k _ (by decide) (by decide), e2], et⟩

/-- A balanced key's checks and values. -/
theorem midW_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} {s0 s : State} (h : StA s0 s) (hB : BalCv s0) :
    WP isa (midW um) s (MidW s0) := by
  rw [midW_eq, wp_seqs_append (List.cons_ne_nil _ _) (by simp)]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (oddW_ok h) fun t1 h1 => ?_
  refine WP.mono (mulW_ok h1 hB) fun t2 ⟨h2, e2⟩ => ?_
  rw [wp_seqs_append (by simp) (List.cons_ne_nil _ _)]
  refine WP.mono (chunkW_ok h2 hB e2) fun t3 ⟨h3, e3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (div2W_ok h3 hB e3) fun t4 ⟨h4, e4⟩ => ?_
  rw [show ∀ a b c : Prog isa, seqs [a, b, c] = seqs ([a, b] ++ [c]) from fun _ _ _ => rfl,
    wp_seqs_append (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)]
  exact WP.mono (setQW_ok h4 hB e4) fun t5 ⟨h5, e5, e5'⟩ => div3W_ok h5 hB e5 e5'
end VG.Proof.Rsa.Arm.CrtValues

end

end

/-! # `vg_rsa_crt_values` on ARMv7: the checks are `crtKey`

`crtKey_masked`: with the mask of the checks computed as `vg_rsa_crt_values`
computes them (`p` odd, `n / p = q`, `n mod p = 0`, and the gcd that
`inverse` finds modulo `p | 1` is 1), `crtKey` is the values computed if the
mask is set, and nothing otherwise.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG.Spec.Rsa

alias pq_iff := VG.Proof.Rsa.CrtValues.pq_iff
alias odd_of_mul := VG.Proof.Rsa.CrtValues.odd_of_mul
alias crtKey_masked := VG.Proof.Rsa.CrtValues.crtKey_masked

end VG.Proof.Rsa.Arm.CrtValues

end

end

/-! ### `Rsa.Arm.CvCT`, which only this module used -/

section

/-! # `vg_rsa_crt_values` on ARMv7: constant time

Two runs from states that agree on what the contract makes public
(`PubI`) are related at every stage by what correctness says of each run
from its own initial state (`Lift`): the pieces the taint analysis checks
(`CvTaint.lean`) agree on the stack arguments and on the registers
correctness determines from them, and the divisions start from the same
geometry (`Div.code_ct`). The branch on the modulus' validity agrees, as
`n` is public.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- What the two runs' initial states agree on. -/
structure PubI (σ₁ σ₂ : State) : Prop where
  sp : σ₁.sp = σ₂.sp
  n : nBytes σ₁ = nBytes σ₂
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  args : ∀ i < 12, stackArg σ₁ i = stackArg σ₂ i

theorem PubI.geom {σ₁ σ₂ : State} (p : PubI σ₁ σ₂) :
    cvB σ₁ = cvB σ₂ ∧ cvZ σ₁ = cvZ σ₂ ∧ cvW σ₁ = cvW σ₂ := by
  simp only [cvB, cvZ, cvW, cvK, p.args 10 (by decide), p.args 11 (by decide), p.args 3 (by decide),
    and_self]

/-- What makes a state of a run agree with the other run's on the stack arguments. -/
structure Run (σ s : State) : Prop where
  pre : CvPre σ
  sp : s.sp = σ.sp
  wr : s.wr = σ.wr
  args : ∀ i < 12, stackArg s i = stackArg σ i

theorem Base.run {σ s : State} (h : Base σ s) : Run σ s := ⟨h.pre, h.sp, h.wr, fun _ hi => h.arg hi⟩
theorem Done.run {σ s : State} (h : Done σ s) : Run σ s := ⟨h.pre, h.sp, h.wr, fun _ hi => h.arg hi⟩

theorem run_wf {σ s : State} (h : Run σ s) :
    s.sp.toNat + 48 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 48⟩ r := by
  refine ⟨by rw [h.sp]; exact h.pre.sp48, ?_⟩
  have e : (⟨State.addr s.sp, 48⟩ : Region) = rA σ := by
    simp only [rA, stackArgAddr, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [e, h.wr, h.pre.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  exacts [h.pre.dpA.symm, h.pre.dqA.symm, h.pre.qiA.symm, h.pre.sA.symm]

theorem agree {σ₁ σ₂ s₁ s₂ : State} (p : PubI σ₁ σ₂) (h₁ : Run σ₁ s₁) (h₂ : Run σ₂ s₂) {rs : List Reg}
    (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.Arm.Taint.Agree (argTaint rs 48) s₁ s₂ := by
  have hsp : s₁.sp = s₂.sp := by rw [h₁.sp, h₂.sp, p.sp]
  exact agree_argTaint hr hsp (run_wf h₁) (run_wf h₂)
    (argMem_of (j := 12) hsp (by rw [h₁.sp]; exact h₁.pre.sp48) fun i hi => by
      rw [h₁.args i hi, h₂.args i hi, p.args i hi])

/-- Two runs at the same stage, each from its own initial state. -/
def Lift (F : State → State → Prop) (s t : State) : Prop := ∃ σ₁ σ₂, PubI σ₁ σ₂ ∧ F σ₁ s ∧ F σ₂ t

theorem Lift.mono {F G : State → State → Prop} (h : ∀ σ s, F σ s → G σ s) {s t : State} :
    Lift F s t → Lift G s t := fun ⟨σ₁, σ₂, p, h₁, h₂⟩ => ⟨σ₁, σ₂, p, h _ _ h₁, h _ _ h₂⟩

theorem lift {F G : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, PubI σ₁ σ₂ → RelCT isa (fun s t => F σ₁ s ∧ F σ₂ t) c fun s t => G σ₁ s ∧ G σ₂ t) :
    RelCT isa (Lift F) c (Lift G) := by
  intro s t tr1 tr2 u v ⟨σ₁, σ₂, p, h₁, h₂⟩ e1 e2
  obtain ⟨tr, g₁, g₂⟩ := h σ₁ σ₂ p s t tr1 tr2 u v ⟨h₁, h₂⟩ e1 e2
  exact ⟨tr, σ₁, σ₂, p, g₁, g₂⟩

/-- A piece the taint analysis checks with the registers `rs` public. -/
theorem piece {F G : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hc : ∃ hc, (VG.Taint.check taint (argTaint rs 48) c hc).isSome = true)
    (run : ∀ σ s, F σ s → Run σ s)
    (regs : ∀ σ₁ σ₂ s₁ s₂, PubI σ₁ σ₂ → F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ σ s, F σ s → WP isa c s (G σ)) : RelCT isa (Lift F) c (Lift G) :=
  lift fun σ₁ σ₂ p => rel_agree (F := F σ₁) (F' := F σ₂) (argTaint rs 48)
    (fun _ _ h h' => agree p (run _ _ h) (run _ _ h') (regs _ _ _ _ p h h')) hc (hw σ₁) (hw σ₂)

/-- `piece`, for code `taintU` checks: code with `umaal`. -/
theorem pieceU {F G : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hc : ∃ hc, (VG.Taint.check taintU (argTaint rs 48) c hc).isSome = true)
    (run : ∀ σ s, F σ s → Run σ s)
    (regs : ∀ σ₁ σ₂ s₁ s₂, PubI σ₁ σ₂ → F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ σ s, F σ s → WP isa c s (G σ)) : RelCT isa (Lift F) c (Lift G) :=
  lift fun σ₁ σ₂ p => by
    obtain ⟨_, hc⟩ := hc
    exact ((RelCT.taint (A := taintU) (argTaint rs 48)
      (fun s s' h => agree p (run _ _ h.1) (run _ _ h.2) (regs _ _ _ _ p h.1 h.2)) hc).wp
      fun s s' h => ⟨hw σ₁ s h.1, hw σ₂ s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A division, from the same geometry in both runs. -/
theorem divPiece {g : State → VG.Proof.Rsa.Arm.Div.Geometry} {Q : State → State → Prop}
    (hg : ∀ σ₁ σ₂, PubI σ₁ σ₂ → g σ₁ = g σ₂) :
    RelCT isa (Lift fun σ u => VG.Proof.Rsa.Arm.Div.Context (g σ) u ∧ WP isa VG.Impl.Rsa.Arm.Div.code u (Q σ))
      VG.Impl.Rsa.Arm.Div.code (Lift Q) :=
  lift fun _ _ p => rel_wp (VG.Proof.Rsa.Arm.Div.code_ct.mono (fun _ _ h => ⟨h.1.1, hg _ _ p ▸ h.2.1⟩)
    fun _ _ h => h) (fun _ h => h.2) (fun _ h => h.2)

theorem geom_eq {σ₁ σ₂ : State} (p : PubI σ₁ σ₂) (q r d t : Nat) :
    divGeom (cvB σ₁) (cvZ σ₁) (cvW σ₁) q r d t = divGeom (cvB σ₂) (cvZ σ₂) (cvW σ₂) q r d t := by
  obtain ⟨eB, eZ, eW⟩ := p.geom
  rw [eB, eZ, eW]

/-- The registers `ptr` uses agree. -/
theorem ws_regs {σ₁ σ₂ s₁ s₂ : State} (p : PubI σ₁ σ₂) {N₁ N₂ : Nat}
    (h₁ : Ws s₁ (cvB σ₁) (cvZ σ₁) (cvW σ₁) N₁) (h₂ : Ws s₂ (cvB σ₂) (cvZ σ₂) (cvW σ₂) N₂) :
    s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 := by
  obtain ⟨eB, -, eW⟩ := p.geom
  rw [h₁.r7, h₂.r7, h₁.r8, h₂.r8, h₁.r9, h₂.r9, eB, eW]
  exact ⟨rfl, rfl, rfl⟩

/-- A piece constant time from the same geometry in both runs. -/
theorem gPiece {c : Prog isa} {Pre : State → State → Prop}
    (hc : ∀ σ₁ σ₂, PubI σ₁ σ₂ → RelCT isa (fun s t => Pre σ₁ s ∧ Pre σ₂ t) c fun _ _ => True)
    {F G : State → State → Prop} (hpre : ∀ σ s, F σ s → Pre σ s) (hw : ∀ σ s, F σ s → WP isa c s (G σ)) :
    RelCT isa (Lift F) c (Lift G) :=
  lift fun σ₁ σ₂ p => (((hc σ₁ σ₂ p).mono (P' := fun s t => F σ₁ s ∧ F σ₂ t)
    (fun _ _ h => ⟨hpre _ _ h.1, hpre _ _ h.2⟩) fun _ _ h => h).wp (F₁ := G σ₁) (F₂ := G σ₂)
    fun _ _ h => ⟨hw _ _ h.1, hw _ _ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The product of a balanced key. -/
theorem mulPiece {F G : State → State → Prop} (hpre : ∀ σ s, F σ s → SA σ s ∧ BalCv σ)
    (hw : ∀ σ s, F σ s → WP isa (VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ) s (G σ)) :
    RelCT isa (Lift F) (VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ) (Lift G) :=
  gPiece (Pre := fun σ s => SA σ s ∧ BalCv σ) (fun σ₁ σ₂ p => by
    obtain ⟨eB, eZ, eW⟩ := p.geom
    exact RelCT.exists_ (P := fun (_ : 16 ≤ cvW σ₁ ∧ cvW σ₁ % 2 = 0) s t => (SA σ₁ s ∧ BalCv σ₁) ∧
        (SA σ₂ t ∧ BalCv σ₂)) (fun hw => (VG.Proof.Rsa.Arm.KeyDiv.mulLo_ct mulW_taint (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hw.2 (by omega_using [hw])).mono
      (fun s t h => ⟨h.1.1.mulPre h.1.2, by rw [eB, eZ, eW]; exact h.2.1.mulPre h.2.2⟩) fun _ _ h => h)
      |>.mono (fun s t h => ⟨⟨h.1.1.base.pre.w16.1, h.1.2.2.2⟩, h⟩) fun _ _ h => h) hpre hw

/-- A division by words of a balanced key. -/
theorem divPieceW {r : Nat} (T : VG.Proof.Rsa.Arm.KeyDiv.DivTaint aD r aDD aDQ aDT aT1) (hr : r ∈ [aDR2, aDR3])
    {F G : State → State → Prop} {M : State → Nat}
    (hpre : ∀ σ s, F σ s → ∃ X₁, SW σ X₁ s ∧
      num s.mem (cvB σ) (cvW σ) aDD = VG.Proof.Rsa.fixT (cvW σ / 2) (M σ) ∧ M σ < 2 ^ (32 * (cvW σ / 2)))
    (hw : ∀ σ s, F σ s → WP isa (VG.Impl.Rsa.Arm.KeyDiv.divW aD r aDD aDQ aDT aT1) s (G σ)) :
    RelCT isa (Lift F) (VG.Impl.Rsa.Arm.KeyDiv.divW aD r aDD aDQ aDT aT1) (Lift G) := by
  have hr' : r < nArr ∧ r ≠ aD ∧ r ≠ aDQ ∧ r ≠ aT1 ∧ r ≠ aDT ∧ r ≠ aDD ∧ r ≠ 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
  refine gPiece (Pre := fun σ s => 16 ≤ cvW σ ∧ VG.Proof.Rsa.Arm.KeyDiv.DivPre (cvB σ) (cvZ σ) (cvW σ) nArr aDD s)
    (fun σ₁ σ₂ p => ?_) (fun σ s h => ?_) hw
  · obtain ⟨eB, eZ, eW⟩ := p.geom
    exact RelCT.exists_ (P := fun (_ : 16 ≤ cvW σ₁) s t => (16 ≤ cvW σ₁ ∧
        VG.Proof.Rsa.Arm.KeyDiv.DivPre (cvB σ₁) (cvZ σ₁) (cvW σ₁) nArr aDD s) ∧
        (16 ≤ cvW σ₂ ∧ VG.Proof.Rsa.Arm.KeyDiv.DivPre (cvB σ₂) (cvZ σ₂) (cvW σ₂) nArr aDD t))
      (fun hw => (VG.Proof.Rsa.Arm.KeyDiv.divW_ct T (by decide) hr'.1 (by decide) (by decide) (by decide)
        (by decide) (by decide) hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 (by decide) (Ne.symm hr'.2.2.2.2.2.1) (by decide)
        (by decide) (Ne.symm hr'.2.2.2.2.1) (by decide) (by decide) (by decide) hr'.2.2.2.2.2.2 (by decide)
        (by decide) (by decide) (by omega_using [hw])).mono
        (fun s t h => ⟨h.1.2, by rw [eB, eZ, eW]; exact h.2.2⟩) fun _ _ h => h)
      |>.mono (fun s t h => ⟨h.1.1, h⟩) fun _ _ h => h
  · obtain ⟨X₁, hs, hM, hMl⟩ := hpre σ s h
    exact ⟨hs.base.pre.w16.1, hs.divPre hM hMl⟩

/-- The checks and values of a balanced key are constant time. -/
theorem midW_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} :
    RelCT isa (Lift fun σ s => StA σ s ∧ BalCv σ) (midW um) (Lift MidW) := by
  rw [show midW um = seqs ([[.block (ctx ++ bitOf sPodd aP)], [VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ], chunkW um,
      [VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR2 aDD aDQ aDT aT1],
      [copy aDD aQ, .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)],
      [VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR3 aDD aDQ aDT aT1]] : List (List (Prog isa))).flatten from rfl]
  refine RelCT.of_join (fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (List.cons_ne_nil _ _) ?_
  simp only [List.map_cons, List.map_nil, seqs_single]
  refine RelCT.seq (piece (G := fun σ s => SA σ s ∧ BalCv σ) [] oddW_taint (fun _ _ h => h.1.base.run)
    (fun _ _ _ _ _ _ _ _ h => nomatch h) fun _ _ h => WP.mono (oddW_ok h.1) fun _ h' => ⟨h', h.2⟩) ?_
  refine RelCT.seq (mulPiece (G := fun σ s => (SA σ s ∧
      num s.mem (cvB σ) (cvW σ) aDR = cvP σ * cvQ σ % 2 ^ (32 * cvW σ)) ∧ BalCv σ) (fun _ _ h => h)
    fun _ _ h => WP.mono (mulW_ok h.1 h.2) fun _ h' => ⟨h', h.2⟩) ?_
  refine RelCT.seq (pieceU (G := fun σ s => (SW σ (xW σ) s ∧ num s.mem (cvB σ) (cvW σ) aDD = fP σ) ∧ BalCv σ)
    [.r7, .r8, .r9] (chunkW_taint um) (fun _ _ h => h.1.1.base.run)
    (fun _ _ _ _ p h₁ h₂ => by
      obtain ⟨e7, e8, e9⟩ := ws_regs p h₁.1.1.ws h₂.1.1.ws
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> first | exact e7 | exact e8 | exact e9)
    fun _ _ h => WP.mono (chunkW_ok h.1.1 h.2 h.1.2) fun _ h' => ⟨h', h.2⟩) ?_
  refine RelCT.seq (divPieceW (M := fun σ => 2 * (cvP σ / 2)) (G := fun σ s => (SW σ (xW σ) s ∧
      num s.mem (cvB σ) (cvW σ) aDR2 = cvD σ % fP σ) ∧ BalCv σ) divW2_taint (by decide)
    (fun _ _ h => ⟨_, h.1.1, h.1.2, Nat.lt_of_le_of_lt (by omega_using []) h.2.p_lt⟩)
    fun _ _ h => WP.mono (div2W_ok h.1.1 h.2 h.1.2) fun _ h' => ⟨h', h.2⟩) ?_
  refine RelCT.seq (piece (G := fun σ s => (SW σ (xW σ) s ∧ num s.mem (cvB σ) (cvW σ) aDR2 = cvD σ % fP σ ∧
      num s.mem (cvB σ) (cvW σ) aDD = fQ σ) ∧ BalCv σ)
    [.r7, .r8, .r9] setQ_taint (fun _ _ h => h.1.1.base.run)
    (fun _ _ _ _ p h₁ h₂ => by
      obtain ⟨e7, e8, e9⟩ := ws_regs p h₁.1.1.ws h₂.1.1.ws
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> first | exact e7 | exact e8 | exact e9)
    fun _ _ h => WP.mono (setQW_ok h.1.1 h.2 h.1.2) fun _ h' => ⟨h', h.2⟩) ?_
  exact divPieceW (M := fun σ => 2 * (cvQ σ / 2)) divW3_taint (by decide)
    (fun _ _ h => ⟨_, h.1.1, h.1.2.2, Nat.lt_of_le_of_lt (by omega_using []) h.2.q_lt⟩)
    fun _ _ h => div3W_ok h.1.1 h.2 h.1.2.1 h.1.2.2

/-- The stages of the valid branch. -/
abbrev F1 (σ u : State) : Prop :=
  VG.Proof.Rsa.Arm.Div.Context (gN σ) u ∧ WP isa VG.Impl.Rsa.Arm.Div.code u (StC σ)
abbrev F3 (σ u : State) : Prop := ∃ X₁ X₂, StD σ X₁ X₂ u
abbrev F4 (σ u : State) : Prop := ∃ X₁ X₂, StE σ X₁ X₂ u
abbrev F5 (σ u : State) : Prop :=
  VG.Proof.Rsa.Arm.Div.Context (gQ σ) u ∧ WP isa VG.Impl.Rsa.Arm.Div.code u (fun t => ∃ X₁ X₂, StG σ X₁ X₂ t)
abbrev F7 (σ u : State) : Prop := Base σ u ∧ Ws u (cvB σ) (cvZ σ) (cvW σ) nArr ∧
  u.gpr .r10 = σ.gpr .r0 ∧ u.gpr .r12 = σ.gpr .r2 ∧ WP isa stores u (Done σ)
/-- After either branch. -/
abbrev FJ (σ u : State) : Prop := ∃ X₁ X₂, StM σ X₁ X₂ u

/-- Any key's checks: `n` divided by `p`. -/
theorem midD_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} : RelCT isa (Lift StA) (midD um) (Lift FJ) := by
  unfold midD
  simp only [seqs]
  refine RelCT.seq (piece (G := F1) [.r7, .r8, .r9] divN_taint (fun _ _ h => h.base.run)
    (fun _ _ _ _ p h₁ h₂ => by
      obtain ⟨e7, e8, e9⟩ := ws_regs p h₁.ws h₂.ws
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> first | exact e7 | exact e8 | exact e9)
    fun _ _ h => divN_pre_ok h) ?_
  refine RelCT.seq (divPiece (g := gN) fun _ _ p => geom_eq p _ _ _ _) ?_
  refine RelCT.seq (pieceU (G := F3) [] (checks_taint um) (fun _ _ h => h.base.run)
    (fun _ _ _ _ _ _ _ _ h => nomatch h) fun _ _ h => ?_) ?_
  · rw [checks_eq]
    exact (wp_seqs_append (by unfold checksA invSetup; simp) (by unfold checksB; simp)).mpr
      (WP.mono (checksA_ok h) fun _ h3 => WP.mono (checksB_ok h3) fun _ h4 => ⟨_, _, h4⟩)
  refine RelCT.seq ((divPiece (g := gP) (Q := F4) fun _ _ p => geom_eq p _ _ _ _).mono
    (fun _ _ => Lift.mono fun _ _ ⟨_, _, h⟩ => ⟨h.ctx, WP.mono (divP_ok h) fun _ h' => ⟨_, _, h'⟩⟩)
    fun _ _ h => h) ?_
  refine RelCT.seq (piece (G := F5) [] divQ_taint (fun _ _ ⟨_, _, h⟩ => h.base.run)
    (fun _ _ _ _ _ _ _ _ h => nomatch h)
    fun _ _ ⟨_, _, h⟩ => WP.mono (divQ_pre_ok h) fun _ h' => ⟨h'.1, WP.mono h'.2 fun _ h'' => ⟨_, _, h''⟩⟩) ?_
  exact (divPiece (g := gQ) fun _ _ p => geom_eq p _ _ _ _).mono (fun _ _ h => h)
    fun _ _ h => Lift.mono (fun _ _ ⟨_, _, h⟩ => ⟨_, _, h.toM⟩) h

theorem valid_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} : RelCT isa (Lift Base) (valid um) (Lift Done) := by
  unfold valid
  simp only [seqs]
  refine RelCT.seq (piece (G := StA) [] loads_taint (fun _ _ h => h.run) (fun _ _ _ _ _ _ _ _ h => nomatch h)
    fun _ _ h => loads_ok h) ?_
  refine RelCT.seq (piece (G := fun σ u => StA σ u ∧ u.z = decide (BalCv σ)) [] shapeCv_taint
    (fun _ _ h => h.base.run) (fun _ _ _ _ _ _ _ _ h => nomatch h) fun _ _ h => shapeCv_ok h) ?_
  refine RelCT.seq (R := Lift FJ) (RelCT.ite (fun s t ⟨σ₁, σ₂, p, h₁, h₂⟩ => ?_) ?_ ?_) ?_
  · show some s.z = some t.z
    rw [h₁.2, h₂.2]
    simp only [BalCv, cvPl, cvQl, cvW, cvK, p.args 3 (by decide), p.args 5 (by decide), p.args 7 (by decide)]
  · exact (midW_ct.mono (fun s t ⟨⟨σ₁, σ₂, p, h₁, h₂⟩, hz⟩ => by
      have z₁ : s.z = true := Option.some.inj hz
      have b₁ : BalCv σ₁ := of_decide_eq_true (h₁.2 ▸ z₁)
      have b₂ : BalCv σ₂ := by
        obtain ⟨l1, l2, l3⟩ := b₁
        simp only [BalCv, cvPl, cvQl, cvW, cvK, ← p.args 3 (by decide), ← p.args 5 (by decide),
          ← p.args 7 (by decide)]
        exact ⟨l1, l2, l3⟩
      exact ⟨σ₁, σ₂, p, ⟨h₁.1, b₁⟩, ⟨h₂.1, b₂⟩⟩) fun _ _ h => h).mono (fun _ _ h => h)
      fun _ _ h => Lift.mono (fun _ _ h => ⟨_, _, h.1⟩) h
  · exact midD_ct.mono (fun _ _ ⟨h, _⟩ => Lift.mono (fun _ _ h => h.1) h) fun _ _ h => h
  refine RelCT.seq (piece (G := F7) [] glue_taint (fun _ _ ⟨_, _, h⟩ => h.base.run)
    (fun _ _ _ _ _ _ _ _ h => nomatch h)
    fun _ _ ⟨_, _, h⟩ => WP.mono (glue_ok h) fun _ ⟨b, w, p10, p12, k⟩ =>
      ⟨b, w, p10, p12, WP.mono k fun _ ⟨_, _, o⟩ => o.done⟩) ?_
  exact piece [.r7, .r8, .r9, .r10, .r12] stores_taint (fun _ _ h => h.1.run)
    (fun _ _ _ _ p h₁ h₂ => by
      obtain ⟨e7, e8, e9⟩ := ws_regs p h₁.2.1 h₂.2.1
      have e10 : _ = _ := (h₁.2.2.1.trans p.r0).trans h₂.2.2.1.symm
      have e12 : _ = _ := (h₁.2.2.2.1.trans p.r2).trans h₂.2.2.2.1.symm
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl)
      exacts [e7, e8, e9, e10, e12])
    fun _ _ h => h.2.2.2.2

/-- Entry: the initial state itself. -/
abbrev FE (σ s : State) : Prop := s = σ ∧ CvPre σ
abbrev GE (σ u : State) : Prop := Base σ u ∧ u.gpr .r0 = σ.gpr .r0 ∧ u.gpr .r3 = σ.gpr .r2 ∧
  u.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes σ)) (cvK σ)

theorem code_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} : RelCT isa (Lift FE) (code um) fun _ _ => True := by
  refine RelCT.seq (piece (G := GE) [.r0, .r1, .r2, .r3] entry_taint
    (fun _ _ ⟨e, h⟩ => by subst e; exact ⟨h, rfl, rfl, fun _ _ => rfl⟩)
    (fun _ _ _ _ p ⟨e₁, _⟩ ⟨e₂, _⟩ => by
      subst e₁ e₂
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      exacts [p.r0, p.r1, p.r2, p.r3])
    fun _ _ ⟨e, h⟩ => by
      subst e; exact WP.mono (entry_ok h) fun _ ⟨b, _, r0, r3, _, z⟩ => ⟨b, r0, r3, z⟩) ?_
  refine RelCT.seq (R := Lift Done) (RelCT.ite (fun s t ⟨σ₁, σ₂, p, h₁, h₂⟩ => ?_) ?_ ?_) ?_
  · have eK : cvK σ₁ = cvK σ₂ := by simp only [cvK, p.args 3 (by decide)]
    show some s.z = some t.z
    rw [h₁.2.2.2, h₂.2.2.2, p.n, eK]
  · exact valid_ct.mono (fun _ _ ⟨h, _⟩ => Lift.mono (fun _ _ h => h.1) h) fun _ _ h => h
  · refine (piece (F := fun σ s => Base σ s ∧ s.gpr .r0 = σ.gpr .r0 ∧ s.gpr .r3 = σ.gpr .r2) (G := Done)
      [.r0, .r3] fail_taint (fun _ _ h => h.1.run) (fun _ _ _ _ p h₁ h₂ => ?_)
      fun _ _ h => WP.mono (fail_ok h.1 h.2.1 h.2.2) fun _ h => h.1).mono
      (fun _ _ ⟨h, _⟩ => Lift.mono (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩) h) fun _ _ h => h
    have e0 : _ = _ := (h₁.2.1.trans p.r0).trans h₂.2.1.symm
    have e3 : _ = _ := (h₁.2.2.trans p.r2).trans h₂.2.2.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [e0, e3]
  · exact (piece (G := fun _ _ => True) [] restore_taint (fun _ _ h => h.run)
      (fun _ _ _ _ _ _ _ _ h => nomatch h) fun _ _ h => WP.mono (restore_ok h) fun _ _ => trivial).mono
      (fun _ _ h => h) fun _ _ _ => trivial

theorem cv_contract_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} :
    ConstantTime isa (Spec.Rsa.crtValuesContract abi 0).pre (Spec.Rsa.crtValuesContract abi 0).pub (code um) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := cv_pre s hs
  have it := cv_pre t ht
  sig_pub [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hp
  have nb : nBytes s = nBytes t := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 bytes
  have args : ∀ i < 12, stackArg s i = stackArg t i := fun i hi =>
    match i, hi with
    | 0, _ => a0 | 1, _ => a1 | 2, _ => a2 | 3, _ => a3 | 4, _ => a4 | 5, _ => a5
    | 6, _ => a6 | 7, _ => a7 | 8, _ => a8 | 9, _ => a9 | 10, _ => a10 | 11, _ => a11
    | _ + 12, h => absurd h (by omega_using [])
  exact (code_ct (um := um) s t tr1 tr2 u v ⟨s, t, ⟨sp, nb, p0, p1, p2, p3, args⟩, ⟨rfl, is⟩, ⟨rfl, it⟩⟩ e1 e2).1

end VG.Proof.Rsa.Arm.CrtValues

end

end

/-! ### `Rsa.Arm.CvCorrect`, which only this module used -/

section

/-! ### `Rsa.Arm.CvValid`, which only this module used -/

section

/-! # `vg_rsa_crt_values` on ARMv7: a valid modulus (`valid_ok`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- What a valid modulus leaves. -/
def ValidPost (s0 t : State) : Prop := ∃ X₁ X₂ V R₂ R₃ X : Nat,
  (0 < cvP s0 → X₁ = cvN s0 / cvP s0 ∧ X₂ = cvN s0 % cvP s0) ∧
  (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧ (cvM s0 : Int) ∣ (X : Int) * cvQ s0 - V ∧ X < cvM s0) ∧
  (0 < 2 * (cvP s0 / 2) → R₂ = cvD s0 % (2 * (cvP s0 / 2))) ∧
  (0 < 2 * (cvQ s0 / 2) → R₃ = cvD s0 % (2 * (cvQ s0 / 2))) ∧
  Outs s0 t (maskOf (cvP s0) (cvQ s0) X₁ X₂ V) R₂ R₃ X

theorem Outs.congr {s0 t : State} {c : Bool} {R₂ R₃ R₂' R₃' X : Nat} (o : Outs s0 t c R₂ R₃ X)
    (e₂ : c = true → R₂ = R₂') (e₃ : c = true → R₃ = R₃') : Outs s0 t c R₂' R₃' X := by
  cases c
  · exact ⟨o.done, o.ret, o.dp, o.dq, o.qi⟩
  · rw [← e₂ rfl, ← e₃ rfl]; exact o

/-- For a balanced key, `p q < 2^(32 w)`. -/
theorem pq_lt {s0 : State} (hB : BalCv s0) (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2)))
    (hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2))) : cvP s0 * cvQ s0 < 2 ^ (32 * cvW s0) := by
  have hW : (2 : Nat) ^ (32 * cvW s0) = 2 ^ (32 * (cvW s0 / 2)) * 2 ^ (32 * (cvW s0 / 2)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hW]; exact VG.Proof.Rsa.mul_lt_sq hp hq

/-- The mask of a balanced key's checks is that of the division of `n` by `p`. -/
theorem maskW_eq {s0 : State} (hm : Spec.Rsa.modulusValid (cvN s0) (cvK s0) = true) (hB : BalCv s0)
    (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2))) (hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2))) (V : Nat) :
    maskOf (cvP s0) (cvQ s0) (xW s0) 0 V = maskOf (cvP s0) (cvQ s0) (cvN s0 / cvP s0) (cvN s0 % cvP s0) V := by
  have hN := (VG.Proof.Rsa.modulusValid_facts hm).1
  simp only [xW, Nat.mod_eq_of_lt (pq_lt hB hp hq)]
  by_cases e : cvP s0 * cvQ s0 = cvN s0
  · obtain ⟨a, b, c⟩ := (pq_iff hN).mpr e
    simp only [e, ↓reduceIte, maskOf, VG.Proof.Rsa.CrtValues.maskOf, b, c]
  · have r : ¬(cvP s0 % 2 = 1 ∧ cvN s0 / cvP s0 = cvQ s0 ∧ cvN s0 % cvP s0 = 0) := fun h => e ((pq_iff hN).mp h)
    simp only [e, ↓reduceIte, maskOf, VG.Proof.Rsa.CrtValues.maskOf]
    rw [decide_eq_false (by omega_using []), decide_eq_false (fun ⟨a, b, c, _⟩ => r ⟨a, b, c⟩)]

/-- Under the mask, a balanced key's remainders by words are those modulo `p - 1` and `q - 1`. -/
theorem remW_eq {s0 : State} (hm : Spec.Rsa.modulusValid (cvN s0) (cvK s0) = true) (hB : BalCv s0)
    (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2))) (hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2))) {V : Nat}
    (w16 : 16 ≤ cvW s0) (hc : maskOf (cvP s0) (cvQ s0) (xW s0) 0 V = true) :
    VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvP s0 / 2)) = 2 * (cvP s0 / 2) ∧
      VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvQ s0 / 2)) = 2 * (cvQ s0 / 2) := by
  have e : cvP s0 * cvQ s0 = cvN s0 := by
    simp only [xW, Nat.mod_eq_of_lt (pq_lt hB hp hq), maskOf, VG.Proof.Rsa.CrtValues.maskOf,
      decide_eq_true_eq] at hc
    by_contra n
    simp [n] at hc
  obtain ⟨-, a, b⟩ := VG.Proof.Rsa.top_words hm rfl (by simp only [cvW] at w16; omega_using [w16]) hp hq e
  exact ⟨VG.Proof.Rsa.fixT_of_ge a, VG.Proof.Rsa.fixT_of_ge b⟩

theorem valid_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} {s0 s : State} (h : Base s0 s)
    (hm : Spec.Rsa.modulusValid (cvN s0) (cvK s0) = true) : WP isa (valid um) s (ValidPost s0) := by
  unfold valid
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h) fun t1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shapeCv_ok h1) fun t2 ⟨h2, z2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  rw [show seqs [Code.block (ctx ++ [Instr.ldr .r10 .r8 sDp, Instr.ldr .r12 .r8 sDq]), stores] =
    .seq (.block glue) stores from rfl]
  refine WP.ite t2.z rfl (fun hz => ?_) (fun _ => ?_)
  · -- A balanced key.
    rw [z2] at hz
    have hB : BalCv s0 := of_decide_eq_true hz
    have hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2)) :=
      bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.1) hB.2.2
    have hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2)) :=
      bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.2.1) hB.2.2
    refine WP.mono (midW_ok h2 hB) fun t3 ⟨h3, e2, e3⟩ => ?_
    refine WP.mono (finish_ok h3) fun t ⟨V, iV, outs⟩ => ?_
    refine ⟨_, _, V, _, _, _, fun _ => ⟨rfl, rfl⟩, iV, fun _ => rfl, fun _ => rfl, ?_⟩
    rw [← maskW_eq hm hB hp hq V]
    exact outs.congr (fun hc => by rw [e2, fP, (remW_eq hm hB hp hq h.pre.w16.1 hc).1])
      (fun hc => by rw [e3, fQ, (remW_eq hm hB hp hq h.pre.w16.1 hc).2])
  · -- Any key: `n` divided by `p`.
    unfold midD
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (WP.seq_iff.mp (divN_ok h2)) fun u hu => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono hu fun t3 h3 => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _), checks_eq]
    refine (wp_seqs_append (by unfold checksA invSetup; simp) (by unfold checksB; simp)).mpr
      (WP.mono (checksA_ok h3) fun t4 h4 => WP.mono (checksB_ok h4) fun t5 h5 => ?_)
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (divP_ok h5) fun t6 h6 => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (WP.seq_iff.mp (divQ_ok h6)) fun u' hu' => ?_
    refine WP.mono hu' fun t7 h7 => ?_
    refine WP.mono (finish_ok h7.toM) fun t ⟨V, iV, outs⟩ => ?_
    exact ⟨_, _, V, _, _, _, h3.div, iV, h7.dp, h7.dq, outs⟩

end VG.Proof.Rsa.Arm.CrtValues

end

end


/-! # `vg_rsa_crt_values` on ARMv7: correctness

`cv_ok`: from a state meeting the contract's precondition, the code returns
with the callee-saved registers and `sp` restored and the results of `crtKey`
written out (`CvPost`); `cv_contract_correct` states it as the contract does.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The results as the contract states them. -/
def CvPost (s0 t : State) : Prop :=
  abiPreserved s0 t ∧ Spec.Rsa.writtenAll t.mem
    [(State.addr (s0.gpr .r0), cvPl s0), (State.addr (s0.gpr .r2), cvQl s0),
      (State.addr (stackArg s0 0), cvPl s0)] (t.gpr .r0)
    ((Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0)).map fun v => [v.1, v.2.1, v.2.2])

/-- The outputs of the valid branch are `crtKey`'s. -/
theorem written_valid {s0 t : State} {c : Bool} {R₂ R₃ X : Nat} (o : Outs s0 t c R₂ R₃ X)
    (e : Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0) = if c then
      some (Spec.Rsa.i2osp (R₂ % 2 ^ (8 * cvPl s0)) (cvPl s0), Spec.Rsa.i2osp (R₃ % 2 ^ (8 * cvQl s0)) (cvQl s0),
        Spec.Rsa.i2osp (X % 2 ^ (8 * cvPl s0)) (cvPl s0)) else none) :
    Spec.Rsa.writtenAll t.mem
      [(State.addr (s0.gpr .r0), cvPl s0), (State.addr (s0.gpr .r2), cvQl s0),
        (State.addr (stackArg s0 0), cvPl s0)] (t.gpr .r0)
      ((Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0)).map fun v => [v.1, v.2.1, v.2.2]) := by
  have r := o.ret; have dp := o.dp; have dq := o.dq; have qi := o.qi
  rw [e]
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte] at r dp dq qi ⊢
    refine ⟨r, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dp, dq, qi⟩
  · simp only [↓reduceIte] at r dp dq qi ⊢
    refine ⟨r, ?_⟩
    simp only [List.map_cons, List.map_nil]
    rw [show Spec.Rsa.bytesAt t.mem (State.addr (s0.gpr .r0)) (cvPl s0) = outDp t.mem s0 from rfl,
      show Spec.Rsa.bytesAt t.mem (State.addr (s0.gpr .r2)) (cvQl s0) = outDq t.mem s0 from rfl,
      show Spec.Rsa.bytesAt t.mem (State.addr (stackArg s0 0)) (cvPl s0) = outQi t.mem s0 from rfl,
      dp, dq, qi]

theorem crtKey_valid {s0 : State} (pre : CvPre s0)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0) = true)
    {X₁ X₂ V R₂ R₃ X : Nat}
    (h₁ : 0 < cvP s0 → X₁ = cvN s0 / cvP s0 ∧ X₂ = cvN s0 % cvP s0)
    (h₂ : 1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧ (cvM s0 : Int) ∣ (X : Int) * cvQ s0 - V ∧
      X < cvM s0)
    (h₃ : 0 < 2 * (cvP s0 / 2) → R₂ = cvD s0 % (2 * (cvP s0 / 2)))
    (h₄ : 0 < 2 * (cvQ s0 / 2) → R₃ = cvD s0 % (2 * (cvQ s0 / 2))) :
    Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0) =
      if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then
      some (Spec.Rsa.i2osp (R₂ % 2 ^ (8 * cvPl s0)) (cvPl s0), Spec.Rsa.i2osp (R₃ % 2 ^ (8 * cvQl s0)) (cvQl s0),
        Spec.Rsa.i2osp (X % 2 ^ (8 * cvPl s0)) (cvPl s0)) else none := by
  have ln : (nBytes s0).length = cvK s0 := bytesAt_length _ _ _
  have lp : (pBytes s0).length = cvPl s0 := bytesAt_length _ _ _
  have lq : (qBytes s0).length = cvQl s0 := bytesAt_length _ _ _
  have e := crtKey_masked (nb := nBytes s0) (pb := pBytes s0) (qb := qBytes s0) (db := dBytes s0)
    (by rw [ln]; exact hv) (by rw [lp, ln]; exact pre.pl2) (by rw [lq, ln]; exact pre.ql2) h₁ h₂ h₃ h₄
  rw [lp, lq] at e
  exact e

theorem crtKey_invalid {s0 : State}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0) = false) :
    Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0) = none := by
  have ln : (nBytes s0).length = cvK s0 := bytesAt_length _ _ _
  unfold Spec.Rsa.crtKey
  simp only [ln, hv, Bool.false_eq_true, false_and, ↓reduceIte]

/-- What the branches leave for `restore`. -/
def CvMid (s0 t : State) : Prop := Done s0 t ∧ Spec.Rsa.writtenAll t.mem
  [(State.addr (s0.gpr .r0), cvPl s0), (State.addr (s0.gpr .r2), cvQl s0),
    (State.addr (stackArg s0 0), cvPl s0)] (t.gpr .r0)
  ((Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0)).map fun v => [v.1, v.2.1, v.2.2])

theorem branches_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} {s0 s : State} (pre : CvPre s0) (hb : Base s0 s) (p0 : s.gpr .r0 = s0.gpr .r0)
    (p3 : s.gpr .r3 = s0.gpr .r2)
    (hz : s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0)) :
    WP isa (.ite .eq (valid um) fail) s (CvMid s0) := by
  refine WP.ite s.z rfl (fun hv => ?_) (fun hv => ?_)
  · rw [hz] at hv
    refine WP.mono (valid_ok hb hv) fun (t : State) ⟨X₁, X₂, V, R₂, R₃, X, h₁, h₂, h₃, h₄, o⟩ => ⟨o.done, ?_⟩
    exact written_valid o (crtKey_valid pre hv h₁ h₂ h₃ h₄)
  · refine WP.mono (fail_ok hb p0 p3) fun (t : State) ⟨d, r0, dp, dq, qi⟩ => ⟨d, ?_⟩
    rw [hz] at hv
    rw [crtKey_invalid hv]
    refine ⟨r0, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dp, dq, qi⟩

theorem cv_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} {s0 : State} (pre : CvPre s0) :
    WP isa (code um) s0 (CvPost s0) := by
  refine WP.seq (WP.mono (entry_ok pre) fun (s : State) ⟨hb, _, p0, p3, _, hz⟩ =>
    WP.seq (WP.mono (branches_ok pre hb p0 p3 hz) fun (t : State) ⟨ht, w⟩ =>
      WP.mono (restore_ok ht) fun (u : State) ⟨hr, hsp, hm, h0⟩ => ⟨⟨hr, hsp⟩, ?_⟩))
  rw [hm, h0]; exact w

theorem cv_contract_correct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} (s : State) (h : (Spec.Rsa.crtValuesContract abi 0).pre s) :
    ∃ tr t, Exec isa (code um) s tr t ∧ abiPreserved s t ∧ (Spec.Rsa.crtValuesContract abi 0).post s t := by
  obtain ⟨tr, t, run, ⟨pres, w⟩⟩ := cv_ok (cv_pre s h)
  refine ⟨tr, t, run, pres, ?_⟩
  sig_post [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact w

end VG.Proof.Rsa.Arm.CrtValues

end

end


/-! # `vg_rsa_crt_values` on ARMv7 is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Impl.Rsa.Arm.CrtValues

/-- A 64-byte modulus, one-byte factors, exponent and outputs, the working
space at `0x4000`, and the stack arguments at `0x8000`. -/
def cvSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x1200 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x11 else if a = 0x8004 then 1 else if a = 0x8009 then 0x20
    else if a = 0x800C then 0x40 else if a = 0x8011 then 0x30 else if a = 0x8014 then 1
    else if a = 0x8019 then 0x31 else if a = 0x801C then 1 else if a = 0x8021 then 0x32
    else if a = 0x8024 then 1 else if a = 0x8029 then 0x40 else if a = 0x802C then 0x20
    else if a = 0x802D then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x8000, 48⟩]
  wr := [⟨0x1000, 1⟩, ⟨0x1200, 1⟩, ⟨0x1100, 1⟩, ⟨0x4000, 8448⟩]

theorem cv_contract_sat : ∃ s, (Spec.Rsa.crtValuesContract abi 0).pre s := by
  sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
    [cvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using cvSatState

/-- `vg_rsa_crt_values`, either variant of its inverse. -/
theorem crt_values_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} :
    Verified target (code um) (Spec.Rsa.crtValuesContract abi 0) :=
  ⟨cv_contract_correct, cv_contract_ct, cv_contract_sat⟩

/-- `vg_rsa_crt_values` (`um = false`) or `vg_rsa_crt_values_umaal` (`um`). -/
theorem crt_values_for_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] (um : Bool) :
    Verified target (codeFor um) (Spec.Rsa.crtValuesContract abi 0) := by
  cases um
  · exact crt_values_verified
  · exact VG.Proof.Bignum.Arm.umaalArithmetic_verified crt_values_verified

end VG.Proof.Rsa.Arm.CrtValues
