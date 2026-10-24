module

import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBoundedRun
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBoundedRun
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBoundedBody

/-!
# ML-DSA on PPC64LE: the loop of `vg_mldsa_rej_bounded_poly`, constant time

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/RejBoundedCT.lean`). Two runs of
the loop for `η`, whose XOF outputs `X₁` and `X₂` have their half-bytes
accepted alike (`hbOks`, which the leak of the contract determines), leak the
same: at iteration `t`, both runs have sampled as many coefficients
(`rbFold_length_congr`), and the byte to read has its half-bytes accepted
alike, so the tests in `r12` agree (`acc_eq`), and with them the branches of
`accept` and the addresses of its stores; the coefficients themselves are
computed by code that the taint analysis proves leaks nothing of them but the
address of the byte read (`load_ct`, `hi_ct`). What each run is at each point
comes from the correctness proof (`relct_wp`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold hbOks rbFold_length_congr rbB halfByteOk_eq halfByteOk_le)
open VG.Proof.MlKem.PPC64LE (relct_noMem)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Spec.MlDsa (Zq halfByteOk)

/-! ## The blocks, for any `η` -/

/-- The load of the byte and the block of its low half-byte. -/
theorem load_ct {η : Nat} (hη : η = 2 ∨ η = 4) {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h3 : ∀ a b, R a b → a.gpr .r3 = b.gpr .r3) :
    RelCT isa R (.block (([.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60] : List Instr) ++ rbHalf η)) fun _ _ => True := by
  rcases hη with rfl | rfl <;>
  exact taint_block [.r3] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h3 a b hab)
    (by taint_decide)

/-- The block of the high half-byte. -/
theorem hi_ct {η : Nat} (hη : η = 2 ∨ η = 4) {R : State → State → Prop} :
    RelCT isa R (.block (.lsr .d .r9 .r8 4 :: rbHalf η)) fun _ _ => True := by
  rcases hη with rfl | rfl <;> exact relct_noMem rfl

/-- The tests of two half-bytes accepted alike, with as many coefficients. -/
theorem acc_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b₁ b₂ j : Nat} (hb₁ : b₁ < 16) (hb₂ : b₂ < 16) (hj : j ≤ 256)
    (hok : halfByteOk η b₁ = halfByteOk η b₂) :
    accH (BitVec.ofNat 64 b₁) (rbB η) (BitVec.ofNat 64 j) = accH (BitVec.ofNat 64 b₂) (rbB η) (BitVec.ofNat 64 j) := by
  rw [accH_val hb₁ rbB_le hj, accH_val hb₂ rbB_le hj]
  rw [halfByteOk_eq hη, halfByteOk_eq hη] at hok
  by_cases h₁ : b₁ < rbB η <;> by_cases h₂ : b₂ < rbB η <;> simp only [h₁, h₂, ite_true, ite_false] at hok ⊢ <;>
    first | rfl | exact absurd hok (by decide)

/-! ## The loop -/

section
variable {σ₁ σ₂ : State} (hp₁ : SpOk (spOf σ₁) σ₁) (hp₂ : SpOk (spOf σ₂) σ₂) (hsp : σ₁.sp = σ₂.sp)
  (h5 : σ₁.gpr .r5 = σ₂.gpr .r5) (h6 : σ₁.gpr .r6 = σ₂.gpr .r6) {η : Nat} (hη : η = 2 ∨ η = 4)
  {X₁ X₂ : List Byte}

theorem base_sp {t₁ t₂ : Nat} {L₁ L₂ : List Zq} {a b : State} (ha : Base σ₁ X₁ t₁ L₁ a) (hb : Base σ₂ X₂ t₂ L₂ b)
    (hsp : σ₁.sp = σ₂.sp) : a.sp = b.sp := by
  rw [ha.env.sp, hb.env.sp, hsp]

theorem base_r4 {t₁ t₂ : Nat} {L₁ L₂ : List Zq} {a b : State} (ha : Base σ₁ X₁ t₁ L₁ a) (hb : Base σ₂ X₂ t₂ L₂ b)
    (h5 : σ₁.gpr .r5 = σ₂.gpr .r5) (hl : L₁.length = L₂.length) : a.gpr .r4 = b.gpr .r4 := by
  rw [ha.at'.r4, hb.at'.r4, hl]; exact congrArg (· + _) h5

include hp₁ hp₂ hsp h5 hη in
/-- A try, in two runs with as many coefficients and half-bytes accepted
alike. -/
theorem try_ct {t : Nat} {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length) {b₁ b₂ : Nat} (hb₁ : b₁ < 16)
    (hb₂ : b₂ < 16) (hok : halfByteOk η b₁ = halfByteOk η b₂) {v₁ v₂ : BitVec 64} :
    RelCT isa (fun a b => H1 η σ₁ X₁ t L₁ b₁ v₁ a ∧ H1 η σ₂ X₂ t L₂ b₂ v₂ b) (accept .r10)
      fun a b => (Base σ₁ X₁ t (tryJ η L₁ b₁) a ∧ a.gpr .r8 = v₁) ∧
        (Base σ₂ X₂ t (tryJ η L₂ b₂) b ∧ b.gpr .r8 = v₂) :=
  relct_wp (accept_ct (fun a b hab => base_sp hab.1.base hab.2.base hsp)
    (fun a b hab => by rw [hab.1.r12, hab.2.r12, hl, acc_eq hη hb₁ hb₂ (hl ▸ hab.2.base.at'.len) hok])
    fun a b hab => base_r4 hab.1.base hab.2.base h5 hl)
    fun a b hab => ⟨try_ok hp₁ hη hb₁ hab.1, try_ok hp₂ hη hb₂ hab.2⟩

variable (hX₁ : X₁.length = 544) (hX₂ : X₂.length = 544) (oks : X₁.map (hbOks η) = X₂.map (hbOks η))

include oks in
theorem len_eq (t : Nat) : (Lf η X₁ t).length = (Lf η X₂ t).length :=
  rbFold_length_congr rfl (by rw [List.map_take, List.map_take, oks])

include hX₁ hX₂ oks in
theorem ok_eq {t : Nat} (ht : t < 544) : hbOks η (zAt X₁ t) = hbOks η (zAt X₂ t) := by
  have h := congrArg (fun L => L[t]?) oks
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show t < X₁.length by omega),
    List.getElem?_eq_getElem (show t < X₂.length by omega), Option.map_some, Option.some.injEq] at h
  rw [zAt, zAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t < X₁.length by omega), List.getElem?_eq_getElem (show t < X₂.length by omega)]
  exact h

theorem tryJ_length_congr {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length) {b₁ b₂ : Nat}
    (hok : halfByteOk η b₁ = halfByteOk η b₂) : (tryJ η L₁ b₁).length = (tryJ η L₂ b₂).length := by
  rw [tryJ_length, tryJ_length, hl, hok]

include hp₁ hp₂ hsp h5 h6 hη hX₁ hX₂ oks in
/-- An iteration, in two runs. -/
theorem body_ct {t : Nat} (ht : t < 544) :
    RelCT isa (fun a b => Base σ₁ X₁ t (Lf η X₁ t) a ∧ Base σ₂ X₂ t (Lf η X₂ t) b) (rbBody η)
      fun a b => (Base σ₁ X₁ (t + 1) (Lf η X₁ (t + 1)) a ∧ (a.gpr .r6 != 0) = decide (t + 1 ≠ 544)) ∧
        (Base σ₂ X₂ (t + 1) (Lf η X₂ (t + 1)) b ∧ (b.gpr .r6 != 0) = decide (t + 1 ≠ 544)) := by
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ hη hX₁ ht hab.1, body_ok hp₂ hη hX₂ ht hab.2⟩
  have hl := len_eq oks t
  have hok := ok_eq hX₁ hX₂ oks ht
  simp only [hbOks, Prod.mk.injEq] at hok
  have hlo₁ : (zAt X₁ t).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have hlo₂ : (zAt X₂ t).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have hhi₁ : (zAt X₁ t).toNat / 16 < 16 := by have := (zAt X₁ t).isLt; omega
  have hhi₂ : (zAt X₂ t).toNat / 16 < 16 := by have := (zAt X₂ t).isLt; omega
  -- the byte and its low half-byte
  refine RelCT.seq (R := fun a b =>
      H1 η σ₁ X₁ t (Lf η X₁ t) ((zAt X₁ t).toNat % 16) ((zAt X₁ t).setWidth 64) a ∧
      H1 η σ₂ X₂ t (Lf η X₂ t) ((zAt X₂ t).toNat % 16) ((zAt X₂ t).setWidth 64) b)
    (relct_wp (load_ct hη (fun a b hab => base_sp hab.1 hab.2 hsp) fun a b hab => by
      rw [hab.1.r3, hab.2.r3, h6]) fun a b hab => ⟨loHalf_ok hp₁ hη ht hab.1, loHalf_ok hp₂ hη ht hab.2⟩) ?_
  -- its try
  refine RelCT.seq (try_ct hp₁ hp₂ hsp h5 hη hl hlo₁ hlo₂ hok.1) ?_
  -- the high half-byte
  have hl' := tryJ_length_congr (η := η) hl hok.1
  refine RelCT.seq (R := fun a b =>
      H1 η σ₁ X₁ t (tryJ η (Lf η X₁ t) ((zAt X₁ t).toNat % 16)) ((zAt X₁ t).toNat / 16) ((zAt X₁ t).setWidth 64) a ∧
      H1 η σ₂ X₂ t (tryJ η (Lf η X₂ t) ((zAt X₂ t).toNat % 16)) ((zAt X₂ t).toNat / 16) ((zAt X₂ t).setWidth 64) b)
    (relct_wp (hi_ct hη) fun a b hab => ⟨hiHalf_ok hp₁ hη hab.1.1 hab.1.2, hiHalf_ok hp₂ hη hab.2.1 hab.2.2⟩) ?_
  -- its try, and the step
  exact RelCT.seq (try_ct hp₁ hp₂ hsp h5 hη hl' hhi₁ hhi₂ hok.2) (relct_noMem rfl)

include hp₁ hp₂ hsp h5 h6 hη hX₁ hX₂ oks in
/-- The loop. -/
theorem loop_ct :
    RelCT isa (fun a b => Base σ₁ X₁ 0 (Lf η X₁ 0) a ∧ Base σ₂ X₂ 0 (Lf η X₂ 0) b) (.loop (rbBody η) (.nonzero .d .r6))
      fun a b => Base σ₁ X₁ 544 (Lf η X₁ 544) a ∧ Base σ₂ X₂ 544 (Lf η X₂ 544) b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rbBody η) (c := .nonzero .d .r6)
    (Q := fun a b => Base σ₁ X₁ 544 (Lf η X₁ 544) a ∧ Base σ₂ X₂ 544 (Lf η X₂ 544) b)
    (fun n a b => ∃ t, t < 544 ∧ n = 544 - t ∧ Base σ₁ X₁ t (Lf η X₁ t) a ∧ Base σ₂ X₂ t (Lf η X₂ t) b)
    (fun n => ?_) 544) (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 544 ∧ n = 544 - t ∧ Base σ₁ X₁ t (Lf η X₁ t) a ∧
      Base σ₂ X₂ t (Lf η X₂ t) b) (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 544
  · by_cases hn : n = 544 - t
    · refine RelCT.mono (P := fun a b => Base σ₁ X₁ t (Lf η X₁ t) a ∧ Base σ₂ X₂ t (Lf η X₂ t) b)
        (body_ct hp₁ hp₂ hsp h5 h6 hη hX₁ hX₂ oks ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [eval_nonzero, eval_nonzero, z₁, z₂]
      · have : t + 1 = 544 := by
          have e' : (a.gpr .r6 != 0) = false := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 544 := by
          have e' : (a.gpr .r6 != 0) = true := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨544 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

end

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded
