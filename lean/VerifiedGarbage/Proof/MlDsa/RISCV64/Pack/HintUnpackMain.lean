module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintUnpack
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_unpack`, correct

The polynomials (`upoly_ok`: one of them is `huPoly` of the spec, or nothing
once a check failed), the trailing bytes (`trail_ok`: `huTrail`), the return
value, and the whole function (`correct`), from the steps of
`HintUnpack.lean`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_add)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.RISCV64.Pack.Hint (add0)

/-- The spec's state after `i` polynomials. -/
abbrev uSt (s₀ : State) (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (uω s₀) (uYs s₀)) (List.range i) (Array.replicate (uk s₀) noHint, 0)

/-- Before polynomial `i`. -/
structure OInv (s₀ : State) (i : Nat) (s : State) : Prop where
  com : UCom s₀ s
  a3 : s.gpr .a3 = uH s₀ + BitVec.ofNat 64 (1024 * i)
  a7 : s.gpr .a7 = uY s₀ + BitVec.ofNat 64 (uω s₀ + i)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (uk s₀ - i)
  st : SRel s₀ (uSt s₀ i) s

theorem fail_ok {s : State} :
    WP isa hbuFail s fun s' => Keep [.t1] s s' ∧ s'.mem = s.mem ∧ s'.gpr .t1 = BitVec.ofNat 64 256 :=
  Steps.wp_li (by decide) fun _ o => WP.block_nil ⟨o.keepH, o.mem, o.gpr⟩

/-- `ltBit t x y` of numbers. -/
theorem lt_ok {t x y : Reg} {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) {s : State}
    (hx : s.gpr x = BitVec.ofNat 64 a) (hy : s.gpr y = BitVec.ofNat 64 b) :
    WP isa (.block (ltBit t x y)) s fun s' => Keep [t] s s' ∧ s'.mem = s.mem ∧
      s'.gpr t = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  unfold ltBit
  refine Steps.wp_sub fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => WP.block_nil ⟨(o₁.keepH.trans o₂.keepH).mono (by simp),
    by rw [o₂.mem, o₁.mem], by rw [o₂.gpr, o₁.gpr, hx, hy, ltBit_eq ha hb]⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- What a polynomial leaves before the pointers move on. -/
def PPost (s₀ : State) (i : Nat) (s s' : State) : Prop :=
  Keep [.t0, .a5, .a6, .t1] s s' ∧ UCom s₀ s' ∧ SRel s₀ (uSt s₀ (i + 1)) s'

omit hp in
theorem uSt_succ (i : Nat) : uSt s₀ (i + 1) = (uSt s₀ i).bind fun st => huPoly (uω s₀) (uYs s₀) st i :=
  optFold_range_succ _ _ _

/-- Polynomial `i`, unless a check failed. -/
theorem poly_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ i s) :
    WP isa hbuPoly s (PPost s₀ i s) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  have hS := hI.st
  have hsucc := uSt_succ (s₀ := s₀) i
  unfold hbuPoly
  cases hst : uSt s₀ i with
  | none =>
    rw [hst] at hS hsucc
    refine WP.seq (WP.mono (lt_ok (a := uω s₀) (b := 256) (by omega_arith) (by decide) hI.com.a2 hS)
      fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
    refine WP.ite _ (eval_lt_zero r0₁) (fun h => absurd (of_decide_eq_true h) (by omega_arith)) fun _ =>
      WP.block_nil ⟨k₁.mono (by decide), hI.com.of k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _), ?_⟩
    rw [hsucc]; show s₁.gpr .t1 = _; rw [k₁.gpr (by decide), hS]
  | some st =>
    obtain ⟨hA, idx⟩ := st
    rw [hst] at hS hsucc
    obtain ⟨h11, hidx, hh⟩ := hS
    have hP : huPoly (uω s₀) (uYs s₀) (hA, idx) i = if ((uYs s₀).getD (uω s₀ + i) 0).toNat < idx ∨
        ((uYs s₀).getD (uω s₀ + i) 0).toNat > uω s₀ then none else
        optFold (huStep (uYs s₀) i idx) (List.range (((uYs s₀).getD (uω s₀ + i) 0).toNat - idx)) (hA, idx) := rfl
    simp only [Option.bind_some] at hsucc
    rw [hP] at hsucc
    refine WP.seq (WP.mono (lt_ok (a := uω s₀) (b := idx) (by omega_arith) (by omega_arith) hI.com.a2 h11)
      fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
    refine WP.ite _ (eval_lt_zero r0₁) (fun _ => ?_) fun h => absurd (of_decide_eq_false h) (by omega_arith)
    obtain ⟨bound, hbound⟩ : ∃ b, ((uYs s₀).getD (uω s₀ + i) 0).toNat = b := ⟨_, rfl⟩
    rw [hbound] at hsucc
    have hb : bound < 256 := hbound ▸ ((uYs s₀).getD (uω s₀ + i) 0).isLt
    have hc₁ : UCom s₀ s₁ := hI.com.of k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _)
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine wp_lbz (a := uY s₀ + BitVec.ofNat 64 (uω s₀ + i)) (by decide) (by decide)
      (by rw [k₁.gpr (by decide), hI.a7, add0]) (yIn hp hc₁ (by omega_arith)) fun s₂ o₂ => WP.block_nil ?_
    have hc₂ : UCom s₀ s₂ := hc₁.of o₂.keepH (by decide) (by decide) (by rw [o₂.mem]; exact Frame.refl _ _)
    have r8 : s₂.gpr .a5 = BitVec.ofNat 64 bound := by rw [o₂.gpr, yByte hp hc₁ (by omega_arith), byte_ofNat, hbound]
    have h11₂ : s₂.gpr .t1 = BitVec.ofNat 64 idx := by rw [o₂.other _ (by decide), k₁.gpr (by decide), h11]
    refine WP.mono (lt_ok (by omega_arith) (by omega_arith) r8 h11₂) fun s₃ ⟨k₃, m₃, r0₃⟩ => ?_
    have k₃' : Keep [.t0, .a5, .a6, .t1] s s₃ := ((k₁.trans o₂.keepH).trans k₃).mono (by decide)
    have m₃' : s₃.mem = s.mem := by rw [m₃, o₂.mem, m₁]
    have hc₃ : UCom s₀ s₃ := hc₂.of k₃ (by decide) (by decide) (by rw [m₃]; exact Frame.refl _ _)
    have fail : ∀ {s'}, Keep [.t0, .t1] s₃ s' → s'.mem = s₃.mem → s'.gpr .t1 = BitVec.ofNat 64 256 →
        bound < idx ∨ bound > uω s₀ → PPost s₀ i s s' := fun k' m' h11' hc => by
      refine ⟨(k₃'.trans k').mono (by decide), hc₃.of k' (by decide) (by decide) (by rw [m']; exact Frame.refl _ _),
        ?_⟩
      rw [hsucc, ite_eq_left_of_eq_true _ _ (eq_true hc)]; exact h11'
    refine WP.ite _ (eval_lt_zero r0₃) (fun hge => ?_)
      fun hlt => WP.mono fail_ok fun s' ⟨k', m', h11'⟩ => fail (k'.mono (by decide)) m' h11' (.inl (by have := of_decide_eq_false hlt; omega_arith))
    have hge : idx ≤ bound := of_decide_eq_true hge
    refine WP.seq (WP.mono (lt_ok (a := uω s₀) (b := bound) (by omega_arith) (by omega_arith) hc₃.a2
      (by rw [k₃.gpr (by decide), r8])) fun s₄ ⟨k₄, m₄, r0₄⟩ => ?_)
    refine WP.ite _ (eval_lt_zero r0₄) (fun hle => ?_)
      fun hgt => WP.mono fail_ok fun s' ⟨k', m', h11'⟩ => fail (s' := s') ((k₄.trans k').mono (by decide))
        (by rw [m', m₄]) h11' (.inr (by have := of_decide_eq_false hgt; omega_arith))
    have hle : bound ≤ uω s₀ := of_decide_eq_true hle
    have hP₄ : PCom s₀ i bound s₄ := ⟨hc₃.of k₄ (by decide) (by decide) (by rw [m₄]; exact Frame.refl _ _),
      by rw [k₄.gpr (by decide), k₃.gpr (by decide), o₂.other _ (by decide), k₁.gpr (by decide), hI.a3],
      by rw [k₄.gpr (by decide), k₃.gpr (by decide), r8]⟩
    refine WP.mono (coefs_ok hp hi (hA := hA) hge hle hP₄ (by rw [k₄.gpr (by decide), k₃.gpr (by decide), h11₂])
      (by rw [m₄, m₃']; exact hh))
      fun s' ⟨hP', k', hS'⟩ => ⟨((k₃'.trans k₄).trans k').mono (by decide), hP'.com, ?_⟩
    rw [hsucc, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]; exact hS'

omit hp in
theorem SRel.of {st : Option (Array (Vector Bool n) × Nat)} {s s' : State} (h : SRel s₀ st s)
    (h11 : s'.gpr .t1 = s.gpr .t1) (hm : s'.mem = s.mem) : SRel s₀ st s' := by
  cases st with
  | none => exact h11.trans h
  | some st => obtain ⟨hA, idx⟩ := st; exact ⟨h11.trans h.1, h.2.1, by rw [hm]; exact h.2.2⟩

/-- Polynomial `i`, and the pointers and the count moved on. -/
theorem upoly_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ i s) :
    WP isa (.seq hbuPoly (.block [.addi .a7 .a7 1, .addi .a3 .a3 1024, .addi .t2 .t2 (-1)])) s fun s' =>
      OInv s₀ (i + 1) s' ∧ (s'.gpr .t2 != 0) = decide (i + 1 ≠ uk s₀) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  refine WP.seq (WP.mono (poly_ok hp hi hI) fun s₁ ⟨k₁, hc₁, hS₁⟩ => ?_)
  refine Steps.wp_addi (by decide) fun s₂ o₂ => Steps.wp_addi (by decide) fun s₃ o₃ =>
    Steps.wp_subi (by decide) fun s₄ o₄ => WP.block_nil ?_
  have k₄ := (o₂.keepH.trans o₃.keepH).trans o₄.keepH
  have m₄ : s₄.mem = s₁.mem := by rw [o₄.mem, o₃.mem, o₂.mem]
  have c12 : s₄.gpr .t2 = BitVec.ofNat 64 (uk s₀ - (i + 1)) := by
    rw [o₄.gpr, o₃.other _ (by decide), o₂.other _ (by decide), k₁.gpr (by decide), hI.t2, count_sub hi]
  refine ⟨⟨hc₁.of k₄ (by decide) (by decide) (by rw [m₄]; exact Frame.refl _ _), ?_, ?_, c12,
    hS₁.of (k₄.gpr (by decide)) m₄⟩, by rw [c12]; exact count_nz hi (by omega_arith)⟩
  · rw [o₄.other _ (by decide), o₃.gpr, o₂.other _ (by decide), k₁.gpr (by decide), hI.a3, ptr_add, Nat.mul_succ]
  · rw [o₄.other _ (by decide), o₃.other _ (by decide), o₂.gpr, k₁.gpr (by decide), hI.a7, ptr_add,
      Nat.add_assoc]

/-- The polynomials, from the state after zeroing `h`. -/
theorem main_ok {s : State} (hz : ZPost s₀ s) : WP isa hbuMain s (OInv s₀ (uk s₀)) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuMain
  refine WP.seq (Steps.wp_add fun s₁ o₁ => WP.block_nil ?_)
  refine wp_loop_nz (OInv s₀) (N := uk s₀) (by omega_arith) (fun i hi s hI => upoly_ok hp hi hI) (fun _ h => h)
    ⟨hz.com.of o₁.keepH (by decide) (by decide) (by rw [o₁.mem]; exact Frame.refl _ _),
      by rw [o₁.other _ (by decide), hz.a3, Nat.mul_zero]; exact (add0 _).symm,
      by rw [o₁.gpr, hz.com.a0, hz.com.a2, Nat.add_zero],
      by rw [o₁.other _ (by decide), hz.t2, Nat.sub_zero],
      ⟨by rw [o₁.other _ (by decide), hz.t1]; rfl, Nat.zero_le _, by rw [o₁.mem]; exact harr_zero hz.zero⟩⟩

/-! ## The bytes after the last index -/

/-- Once a check failed, nothing. -/
theorem trail_none {s : State} (hc : UCom s₀ s) (h11 : s.gpr .t1 = BitVec.ofNat 64 256) :
    WP isa hbuTrail s fun s' => UCom s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .t1 = BitVec.ofNat 64 256 := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuTrail
  refine WP.seq (WP.mono (lt_ok (by decide) (by omega_arith) h11 hc.a2) fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
  refine WP.ite _ (eval_lt_zero r0₁) (fun _ => WP.block_nil ⟨hc.of k₁ (by decide) (by decide)
    (by rw [m₁]; exact Frame.refl _ _), m₁, by rw [k₁.gpr (by decide), h11]⟩)
    fun h => absurd (of_decide_eq_false h) (by omega_arith)

/-- The bytes from the index `idx` up to `ω` are zero, or the index becomes 256. -/
theorem trail_some {idx : Nat} (hidx : idx ≤ uω s₀) {s : State} (hc : UCom s₀ s)
    (h11 : s.gpr .t1 = BitVec.ofNat 64 idx) :
    WP isa hbuTrail s fun s' => UCom s₀ s' ∧ s'.mem = s.mem ∧
      s'.gpr .t1 = BitVec.ofNat 64
        (if (optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) ()).isSome then uω s₀ else 256) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuTrail
  refine WP.seq (WP.mono (lt_ok (by omega_arith) (by omega_arith) h11 hc.a2) fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
  have hc₁ : UCom s₀ s₁ := hc.of k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _)
  refine WP.ite _ (eval_lt_zero r0₁) (fun hge => ?_) (fun hlt => ?_)
  · -- `idx = ω`: nothing.
    have e : uω s₀ - idx = 0 := by have := of_decide_eq_true hge; omega_arith
    refine WP.block_nil ⟨hc₁, m₁, ?_⟩
    rw [k₁.gpr (by decide), h11, e]
    simp only [List.range'_zero, optFold, Option.isSome_some, ↓reduceIte]
    congr 1; omega_arith
  have hlt : idx < uω s₀ := by have := of_decide_eq_false hlt; omega_arith
  refine WP.loop (M := isa) (fun m s' => ∃ u, m = uω s₀ - idx - u ∧ idx + u < uω s₀ ∧
      optFold (huTrail (uYs s₀)) (List.range' idx u) () = some () ∧ s'.gpr .t1 = BitVec.ofNat 64 (idx + u) ∧
      UCom s₀ s' ∧ s'.mem = s.mem)
    (fun m s' ⟨u, hm, hu, hF, h11', hc', hm'⟩ => ?_) _ s₁
    ⟨0, rfl, by omega_arith, rfl, by rw [k₁.gpr (by decide), h11]; rfl, hc₁, m₁⟩
  have hF1 : optFold (huTrail (uYs s₀)) (List.range' idx (u + 1)) () = huTrail (uYs s₀) () (idx + u) := by
    rw [optFold_range'_succ, hF]; rfl
  refine WP.seq (Steps.wp_add fun s₂ o₂ => wp_lbz (a := uY s₀ + BitVec.ofNat 64 (idx + u)) (by decide) (by decide)
    (by rw [o₂.gpr, hc'.a0, h11', add0]) (by rw [o₂.rd, o₂.wr]; exact yIn hp hc' (by omega_arith)) fun s₃ o₃ =>
    WP.block_nil ?_)
  have k₃ := o₂.keepH.trans o₃.keepH
  have m₃ : s₃.mem = s'.mem := by rw [o₃.mem, o₂.mem]
  have hc₃ : UCom s₀ s₃ := hc'.of k₃ (by decide) (by decide) (by rw [m₃]; exact Frame.refl _ _)
  have r9 : s₃.gpr .a6 = BitVec.ofNat 64 ((uYs s₀).getD (idx + u) 0).toNat := by
    rw [o₃.gpr, o₂.mem, yByte hp hc' (by omega_arith), byte_ofNat]
  have hyb := ((uYs s₀).getD (idx + u) 0).isLt
  refine WP.seq (WP.ite _ (eval_zero_ofNat s₃ .a6 (by omega_arith) r9) (fun hz => ?_) (fun hnz => ?_))
  · -- A zero byte: next.
    have hz : (uYs s₀).getD (idx + u) 0 = 0 := by
      apply BitVec.eq_of_toNat_eq; exact of_decide_eq_true hz
    have hF2 : optFold (huTrail (uYs s₀)) (List.range' idx (u + 1)) () = some () := by
      rw [hF1]; simp only [huTrail, hz, ne_eq, not_true_eq_false, ↓reduceIte]
    refine Steps.wp_addi (by decide) fun s₄ o₄ => WP.block_nil ?_
    have h11₄ : s₄.gpr .t1 = BitVec.ofNat 64 (idx + (u + 1)) := by
      rw [o₄.gpr, k₃.gpr (by decide), h11', ofNat_succ, Nat.add_assoc]
    have hc₄ : UCom s₀ s₄ := hc₃.of o₄.keepH (by decide) (by decide) (by rw [o₄.mem]; exact Frame.refl _ _)
    refine WP.mono (lt_ok (by omega_arith) (by omega_arith) h11₄ hc₄.a2) fun s₅ ⟨k₅, m₅, r0₅⟩ => ?_
    have hc₅ : UCom s₀ s₅ := hc₄.of k₅ (by decide) (by decide) (by rw [m₅]; exact Frame.refl _ _)
    have h11₅ : s₅.gpr .t1 = BitVec.ofNat 64 (idx + (u + 1)) := by rw [k₅.gpr (by decide), h11₄]
    have hm₅ : s₅.mem = s.mem := by rw [m₅, o₄.mem, m₃, hm']
    by_cases e : idx + (u + 1) < uω s₀
    · exact .inr ⟨by rw [eval_lt_nonzero r0₅]; exact congrArg some (decide_eq_true e), _, by omega_arith, u + 1, rfl, e,
        hF2, h11₅, hc₅, hm₅⟩
    · refine .inl ⟨by rw [eval_lt_nonzero r0₅]; exact congrArg some (decide_eq_false e), hc₅, hm₅, ?_⟩
      rw [show uω s₀ - idx = u + 1 by omega_arith, hF2, h11₅]
      simp only [Option.isSome_some, ↓reduceIte]
      congr 1; omega_arith
  · -- A nonzero byte: fail.
    have hnz : (uYs s₀).getD (idx + u) 0 ≠ 0 := fun e => by
      have := of_decide_eq_false hnz; rw [e] at this; exact this rfl
    have hn : optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () = none :=
      optFold_range'_none _ _ (show u + 1 ≤ uω s₀ - idx by omega_arith)
        (by rw [hF1, huTrail, ite_eq_left_of_eq_true _ _ (eq_true hnz)])
    refine WP.mono fail_ok fun s₄ ⟨k₄, m₄, h11₄⟩ => ?_
    have hc₄ : UCom s₀ s₄ := hc₃.of k₄ (by decide) (by decide) (by rw [m₄]; exact Frame.refl _ _)
    refine WP.mono (lt_ok (by decide) (by omega_arith) h11₄ hc₄.a2) fun s₅ ⟨k₅, m₅, r0₅⟩ => ?_
    refine .inl ⟨by rw [eval_lt_nonzero r0₅]; exact congrArg some (decide_eq_false (by omega_arith)),
      hc₄.of k₅ (by decide) (by decide) (by rw [m₅]; exact Frame.refl _ _), by rw [m₅, m₄, m₃, hm'], ?_⟩
    rw [k₅.gpr (by decide), h11₄, hn]
    rfl

/-! ## The return value -/

omit hp in
theorem ret_ok {x ω : Nat} (hx : x ≤ 256) (hω : ω ≤ 80) {s : State} (h11 : s.gpr .t1 = BitVec.ofNat 64 x)
    (h5 : s.gpr .a2 = BitVec.ofNat 64 ω) :
    WP isa (.block hbuRet) s fun s' => s'.mem = s.mem ∧
      (s'.gpr .a0).setWidth 32 = if x ≤ ω then 1 else 0 := by
  unfold hbuRet
  refine Steps.wp_sub fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => Steps.wp_li (by decide) fun s₃ o₃ =>
    Steps.wp_sub fun s₄ o₄ => WP.block_nil ⟨by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem], ?_⟩
  rw [o₄.gpr, o₃.gpr, o₃.other _ (by decide), o₂.gpr, o₁.gpr, h5, h11, ltBit_eq (by omega_arith) (by omega_arith)]
  by_cases e : x ≤ ω
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true e)]; rfl
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false e)]; rfl

/-! ## The function -/

/-- The registers `hintBitUnpack` writes. -/
abbrev hbuRegs : List Reg := [.t0, .a0, .a2, .a3, .a5, .a6, .a7, .t1, .t2]

/-- The postcondition, as `sig_post` states it. -/
def UPost (s₀ s' : State) : Prop :=
  match hintBitUnpack (uω s₀) (uk s₀) (bytesAt s₀.mem (uY s₀) (uLen s₀)) with
  | some hint => (s'.gpr .a0).setWidth 32 = 1 ∧ HintIs s'.mem (uH s₀) (uk s₀) hint
  | none => (s'.gpr .a0).setWidth 32 = 0

theorem correct : WP isa Impl.MlDsa.RISCV64.Pack.hintBitUnpack s₀ fun s' => UPost s₀ s' ∧ Keep hbuRegs s₀ s' := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  refine WP.keep hbuRegs ?_ (by decide +kernel)
  unfold Impl.MlDsa.RISCV64.Pack.hintBitUnpack
  refine WP.seq (WP.mono (zero_ok hp) fun s₁ hz => WP.seq (WP.mono (main_ok hp hz) fun s₂ hI => ?_))
  have hS := hI.st
  cases hst : uSt s₀ (uk s₀) with
  | none =>
    rw [hst] at hS
    have e : optFold (huPoly (uω s₀) (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range (uk s₀))
        (Array.replicate (uk s₀) noHint, 0) = none := hst
    refine WP.seq (WP.mono (trail_none hp hI.com hS) fun s₃ ⟨hc₃, m₃, h11₃⟩ =>
      WP.mono (ret_ok (by decide) hω80 h11₃ hc₃.a2) fun s₄ ⟨_, r3₄⟩ => ?_)
    simp only [UPost, hintBitUnpack_eq, e]
    rw [r3₄, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
  | some st =>
    obtain ⟨hA, idx⟩ := st
    rw [hst] at hS
    obtain ⟨h11, hidx, hh⟩ := hS
    have e : optFold (huPoly (uω s₀) (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range (uk s₀))
        (Array.replicate (uk s₀) noHint, 0) = some (hA, idx) := hst
    refine WP.seq (WP.mono (trail_some hp hidx hI.com h11) fun s₃ ⟨hc₃, m₃, h11₃⟩ =>
      WP.mono (ret_ok (by split <;> omega_arith) hω80 h11₃ hc₃.a2) fun s₄ ⟨m₄, r3₄⟩ => ?_)
    cases hT : optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () with
    | none =>
      have eT : optFold (huTrail (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range' idx (uω s₀ - idx)) () =
        none := hT
      simp only [UPost, hintBitUnpack_eq, e, eT, Option.map_none]
      rw [hT] at r3₄
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at r3₄
      rw [r3₄, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
    | some u =>
      have eT : optFold (huTrail (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range' idx (uω s₀ - idx)) () =
        some u := hT
      simp only [UPost, hintBitUnpack_eq, e, eT, Option.map_some]
      rw [hT] at r3₄
      simp only [Option.isSome_some, ↓reduceIte] at r3₄
      refine ⟨by rw [r3₄, ite_eq_left_of_eq_true _ _ (eq_true (Nat.le_refl _))], ?_⟩
      rw [m₄, m₃]
      exact harr_hintIs hh

end

end VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack
