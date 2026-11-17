module

public import VerifiedGarbage.Impl.Ed25519.AArch64.PointEncode
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ed25519.AArch64.Ops
public import VerifiedGarbage.Proof.Ed25519.Canonical64
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Ed25519.AArch64.Freeze`, which this module and modules that import it used -/

section

/-! Full reduction of four limbs to the canonical residue. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64
open VG.Spec.X25519 (P)

theorem freezeFold_ok (s : State) (hz : s.gpr .x10 = 0) (h19 : s.gpr .x11 = 19)
    (hl : s.gpr .x2 = low63) :
    WP isa (.block freezeFold) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) % P =
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % P ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) < 2 ^ 255 + 19 ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x3] s t := by
  have hm (x : Word) : ((x >>> 63) * 19).toNat = 19 * (x.toNat / 2 ^ 63) := by
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show (19 : Word).toNat = 19 from rfl, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])
  apply WP.of_runBlock
  simp only [freezeFold, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, hz, h19, hl, show 63 < Size.x.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have H := fold_top (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
    (s.gpr .x7 &&& low63) ((s.gpr .x7 >>> 63) * 19) (hm _) (and_low63 _)
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem freezeCandidate_ok (s : State) (hz : s.gpr .x10 = 0) (h19 : s.gpr .x11 = 19)
    (hl : s.gpr .x2 = low63)
    (hx : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) < 2 ^ 255 + 19) :
    WP isa (.block freezeCandidate) s fun t =>
      t.gpr .x3 = mask (decide (P ≤ val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7))) ∧
      (P ≤ val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) →
        val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) =
          val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) - P) ∧
      Keeps [.x21, .x22, .x23, .x24, .x8, .x3] s t := by
  apply WP.of_runBlock
  simp only [freezeCandidate, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, hz, h19, hl, show 63 < Size.x.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have H := add19_top (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) hx
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits, low63] at H ⊢
    exact H.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem select4_ok (s : State) {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block select4) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        (if sw then val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)
          else val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) ∧
      Keeps [.x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [select4, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, hm, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', xor_sel']
  refine ⟨by cases sw <;> rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

/-- The result is the unique representative below p. -/
theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base large) {a : Nat} (ha : FieldRange a large) :
    WP isa (.block (freeze a)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem base a % P ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x21, .x22, .x23, .x24] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [freeze, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (fieldInit_ok s 19) fun s₀ ⟨hz, h19, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₀ .x2 low63) fun s₁ ⟨hl, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs₁ ha (by decide)) fun s₂ ⟨w4, w5, w6, w7, k2⟩ => ?_
  have hz2 : s₂.gpr .x10 = 0 := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans hz)
  have h192 : s₂.gpr .x11 = 19 := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h19)
  have hl2 : s₂.gpr .x2 = low63 := (k2.gpr _ (by decide)).trans hl
  rw [WP.block_append_iff]
  refine WP.mono (freezeFold_ok s₂ hz2 h192 hl2) fun s₃ ⟨e3, b3, k3⟩ => ?_
  have hz3 := (k3.gpr .x10 (by decide)).trans hz2
  have h193 := (k3.gpr .x11 (by decide)).trans h192
  have hl3 := (k3.gpr .x2 (by decide)).trans hl2
  rw [WP.block_append_iff]
  refine WP.mono (freezeCandidate_ok s₃ hz3 h193 hl3 b3) fun s₄ ⟨m4, v4, k4⟩ => ?_
  refine WP.mono (select4_ok s₄ m4) fun s₅ ⟨v5, k5⟩ => ?_
  have K : Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x21, .x22, .x23, .x24] s s₅ :=
    ((((k0.mono (by decide)).trans (k1.mono (by decide))).trans (k2.mono (by decide))).trans
      (k3.mono (by decide))).trans (k4.mono (by decide)) |>.trans (k5.mono (by decide))
  rw [k4.gpr .x4 (by decide), k4.gpr .x5 (by decide), k4.gpr .x6 (by decide),
    k4.gpr .x7 (by decide)] at v5
  rw [w4, w5, w6, w7, k1.mem, k0.mem] at e3
  refine ⟨?_, K⟩
  rw [v5, ← e3]
  generalize val4 (s₃.gpr .x4) (s₃.gpr .x5) (s₃.gpr .x6) (s₃.gpr .x7) = x at b3 v4 ⊢
  by_cases h : P ≤ x
  · simp only [decide_eq_true h, ite_true]
    rw [v4 h]
    simp only [P] at h b3 ⊢
    omega_using [h, b3]
  · simp only [decide_eq_false h, Bool.false_eq_true, ite_false]
    exact (Nat.mod_eq_of_lt (by omega_using [h])).symm

end VG.Proof.Ed25519.AArch64

end

end

/-! Merged from `Proof.Ed25519.AArch64.PointAffine`. -/

@[expose] public section

section
/-! Normalize extended coordinates with the verified inversion chain. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩

theorem pointAffine_ok [Divstep.Sound] {s : State} {base : Addr} (hs : Scr s base) :
    WP isa pointAffine s fun t => CounterKeep base s t ∧
      env t.mem base 0 = env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) ∧
      env t.mem base 1 = env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) := by
  rw [pointAffine]
  refine WP.seq (WP.mono (Divstep.invert_ok hs) fun t ⟨hv, hk, h1, hO⟩ => ?_)
  have invClob : ∀ r ∈ (.x19 :: VG.Proof.Mont.AArch64.clob 4 ++ ([.x2, .x20] : List Reg)),
      r = .x1 ∨ r = .x19 ∨ r ∈ clob := by decide
  have hkg : ∀ r, r ∉ clob → r ≠ .x19 → t.gpr r = s.gpr r := fun r hr hb => by
    by_cases hx : r = .x1
    · subst hx; exact h1
    · exact hk.gpr r fun hm => by
        rcases invClob r hm with h | h | h
        · exact hx h
        · exact hb h
        · exact hr h
  have ht : Scr t base := ⟨(hkg _ (by decide) (by decide)).trans hs.x0, hk.wr ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (fieldCode_ok affineOps ht) fun u ⟨ku, vu⟩ => ?_
  refine ⟨⟨fun r hr hb => (ku.gpr r hr).trans (hkg r hr hb), ku.rd.trans hk.rd,
    ku.wr.trans hk.wr, ku.sp.trans hk.sp,
    (hO.mono (by decide) (by decide)).trans ku.mem⟩, ?_, ?_⟩
  · rw [vu, (affine_eval _).1, hv]
    have he : env t.mem base 0 = env s.mem base 0 := by
      change F t.mem base 64 = F s.mem base 64
      unfold F; rw [hO.fe (Or.inl (by decide)) (by decide)]
    rw [he, Proof.X25519.invert_eq]
  · rw [vu, (affine_eval _).2, hv]
    have he : env t.mem base 1 = env s.mem base 1 := by
      change F t.mem base 96 = F s.mem base 96
      unfold F; rw [hO.fe (Or.inl (by decide)) (by decide)]
    rw [he, Proof.X25519.invert_eq]

end VG.Proof.Ed25519.AArch64
end

/-! Canonical point encoding in four machine words. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem freezeField_ok {s : State} {base : Addr} (hs : Scr s base) (a : Slot) :
    WP isa (.block (freeze (offset a))) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = (env s.mem base a).val ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x21, .x22, .x23, .x24] s t :=
  freeze_ok hs (slot_range a)

theorem sign_word (w : BitVec 64) :
    (w &&& 1) <<< 63 = BitVec.ofNat 64 ((w.toNat % 2) * 2 ^ 63) := by
  have he : w &&& 1 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega_using [])]
  rw [he]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega_using []
  rcases h with h | h <;> rw [h] <;> decide

theorem pointSign_ok (s : State) :
    WP isa (.block pointSign) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 ((val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2) * 2 ^ 63) ∧
      Keeps [.x19, .x9] s t := by
  have hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 = (s.gpr .x4).toNat % 2 := by
    simp only [val4]; omega_using []
  apply WP.of_runBlock
  simp only [pointSign, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.w.bits from by decide, show (63 : Nat) < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [hv]; exact sign_word _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem encodeSign_ok (s : State) (x y : Nat) (hy : y < 2 ^ 255)
    (hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) = y)
    (hs : s.gpr .x19 = BitVec.ofNat 64 ((x % 2) * 2 ^ 63)) :
    WP isa (.block [.add .x .x7 .x7 .x19]) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = y + (x % 2) * 2 ^ 255 ∧
      Keeps [.x7] s t := by
  have hb : (s.gpr .x7).toNat < 2 ^ 63 := by simp only [val4] at hv; omega_using [hy, hv]
  have hm : ((x % 2) * 2 ^ 63) < 2 ^ 64 := by omega_using []
  have ha : (s.gpr .x7 + s.gpr .x19).toNat = (s.gpr .x7).toNat + (x % 2) * 2 ^ 63 := by
    rw [hs, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega_using [hb])]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [val4, ha] at hv ⊢; omega_using [hv]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem pointEncode_ok [Divstep.Sound] {s : State} {base : Addr} (hs : Scr s base) :
    WP isa pointEncode s fun t => CounterKeep base s t ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val +
        ((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  rw [pointEncode]
  refine WP.seq (WP.mono (pointAffine_ok hs) fun a ⟨ka, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (freezeField_ok (ka.scr hs) 0) fun b ⟨bx, kb⟩ => ?_
  have kbe : CounterKeep base a b := CounterKeep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointSign_ok b) fun c ⟨cx, kc⟩ => ?_
  have kce : CounterKeep base b c := CounterKeep.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok (kce.scr (kbe.scr (ka.scr hs))) 1) fun d ⟨dy, kd⟩ => ?_
  have kde : CounterKeep base c d := CounterKeep.of_keeps kd (by decide)
  have dx : d.gpr .x19 = BitVec.ofNat 64
      (((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 63) := by
    rw [kd.gpr .x19 (by decide), cx, bx, ax]
  rw [kc.mem, kb.mem, ay] at dy
  refine WP.mono (encodeSign_ok d _ _ (by
    exact Nat.lt_trans (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).isLt
      (by decide : Spec.X25519.P < 2 ^ 255)) dy dx) fun t ⟨hv, kt⟩ => ?_
  exact ⟨(((ka.trans kbe).trans kce).trans kde).trans (CounterKeep.of_keeps kt (by decide)), hv⟩

end VG.Proof.Ed25519.AArch64
