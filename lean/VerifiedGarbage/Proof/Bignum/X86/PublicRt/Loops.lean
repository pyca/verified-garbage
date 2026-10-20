module

import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

/-! # The loops of public RSA at a run-time width

Each loop runs over `N` words, its pointers moving up a word and a register
counting `4 N` bytes down (`countLoop`): zeroing (`zeroLoop_ok`), the
comparison of two numbers (`compareLoop_ok`), a doubling (`doubleLoop_ok`),
a subtraction (`reduceLoop_ok`), a selection under a mask (`selectLoop_ok`)
and a masking (`maskLoop_ok`). A carry between words is a mask in `ecx`,
`add ecx, ecx` turning it back into the carry flag (`wp_carry`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

/-- A loop over `N` words: an invariant at each word, and ZF at the last. -/
theorem countLoop {body : Prog isa} {N : Nat} (hN : 0 < N) (I : Nat → State → Prop)
    (hstep : ∀ j t, j < N → I j t → WP isa body t fun u => I (j + 1) u ∧ u.zf = some (decide (j + 1 = N)))
    {t₀ : State} (h₀ : I 0 t₀) : WP isa (.loop body .ne) t₀ (I N) := by
  refine WP.loop (M := isa) (Q := I N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ I j t) ?_ N t₀
    ⟨0, by omega, hN, h₀⟩
  rintro m t ⟨j, rfl, hj, hI⟩
  refine WP.mono (hstep j t hj hI) fun u ⟨I', zu⟩ => ?_
  by_cases hjN : j + 1 = N
  · exact .inl ⟨by simp only [eval, zu, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
  · exact .inr ⟨by simp only [eval, zu, decide_eq_false hjN, Option.map_some, Bool.not_false],
      N - (j + 1), by omega, j + 1, rfl, by omega, I'⟩

/-- A pointer up a word. -/
theorem ptr4 {t : State} {W : Addr} {r : Reg} {x j : Nat} (hp : PtrAt t W r (x + 4 * j)) :
    (t.gpr r + 4).toNat = (W.toNat + (x + 4 * (j + 1))) % 2 ^ 32 := by
  rw [ptr_add hp, show (4 : BitVec 32).toNat = 4 from rfl]
  congr 1

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `add ecx, ecx`: the carry flag from the mask `ecx`. -/
theorem wp_carry {c : Bool} (hc : s.gpr .ecx = cmask c)
    (k : ∀ t, Upd s t .ecx (s.gpr .ecx + s.gpr .ecx) → t.cf = some c → WP isa (.block is) t Q) :
    WP isa (.block (.alu .add .ecx (.reg .ecx) :: is)) s Q :=
  wp_addS rfl fun t u cf => k t u (by rw [cf, hc]; cases c <;> rfl)

end

/-! ## Zeroing -/

theorem zeroLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x N : Nat} (hN : 0 < N)
    (hx : x + 4 * N ≤ L) (hebp : PtrAt t₀ W .ebp x) (hecx : (t₀.gpr .ecx).toNat = 4 * N)
    (heax : t₀.gpr .eax = 0) :
    WP isa (.loop (.block [.store (at_ .ebp 0) .eax, .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne) t₀
      fun u => Outside W x (4 * N) t₀.mem u.mem ∧ val32 u.mem W x N = 0 ∧ Keeps [.ebp, .ecx] t₀ u := by
  have hn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.ebp, .ecx] t₀ t ∧ PtrAt t W .ebp (x + 4 * j) ∧
      (t.gpr .ecx).toNat = 4 * (N - j) ∧ Outside W x (4 * j) t₀.mem t.mem ∧ val32 t.mem W x j = 0) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hecx, Outside.refl _ _ _ _, rfl⟩)
    fun u ⟨K, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro j t hj ⟨Kt, ebp, ecx, O, V⟩
  have ht := hw.of_keeps Kt
  have eax : t.gpr .eax = 0 := by rw [Kt.1 _ (by decide)]; exact heax
  refine wp_storeS (ea_ptr ht ebp (d := 0) (by omega_using [hx, hj]))
    (ws_write ht (y := x + 4 * j + 0) (n := 4) (by omega_using [hx, hj])) fun s₁ m₁ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => wp_subZ rfl fun s₃ u₃ z₃ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf ecx hj
  have ecx₂ : s₂.gpr .ecx = t.gpr .ecx := by rw [u₂.other _ (by decide), m₁.gpr]
  refine ⟨⟨((Kt.widen (m₁.keeps [])).widen u₂.keeps).widen u₃.keeps, ?_, by rw [u₃.gpr, ecx₂]; exact c₁, ?_, ?_⟩,
    by rw [z₃, ecx₂, c₂]⟩
  · rw [PtrAt, u₃.other _ (by decide), u₂.gpr, m₁.gpr]; exact ptr4 ebp
  · rw [u₃.mem, u₂.mem, m₁.mem, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hx, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₃.mem, u₂.mem, m₁.mem, Nat.add_zero, val32_store hn (by omega_using [hx, hj]), V, eax]; rfl

/-! ## Masking -/

theorem maskLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x N : Nat} (hN : 0 < N)
    (hx : x + 4 * N ≤ L) (hebp : PtrAt t₀ W .ebp x) (hedx : (t₀.gpr .edx).toNat = 4 * N) {c : Bool}
    (hecx : t₀.gpr .ecx = cmask c) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .and .eax (.reg .ecx), .store (at_ .ebp 0) .eax,
      .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne) t₀
      fun u => Outside W x (4 * N) t₀.mem u.mem ∧
        val32 u.mem W x N = (if c then val32 t₀.mem W x N else 0) ∧ Keeps [.eax, .ebp, .edx] t₀ u := by
  have hn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebp, .edx] t₀ t ∧ PtrAt t W .ebp (x + 4 * j) ∧
      (t.gpr .edx).toNat = 4 * (N - j) ∧ Outside W x (4 * j) t₀.mem t.mem ∧
      val32 t.mem W x j = (if c then val32 t₀.mem W x j else 0)) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hedx, Outside.refl _ _ _ _, by cases c <;> rfl⟩)
    fun u ⟨K, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro j t hj ⟨Kt, ebp, edx, O, V⟩
  have ht := hw.of_keeps Kt
  have ecx : t.gpr .ecx = cmask c := by rw [Kt.1 _ (by decide)]; exact hecx
  refine wp_movS (readSrc_ptr ht ebp (d := 0) (by omega_using [hx, hj])) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  have K₂ : Keeps [.eax] t s₂ := u₁.keeps.trans u₂.keeps
  have ht₂ := ht.of_keeps K₂
  have ebp₂ : PtrAt s₂ W .ebp (x + 4 * j) := by rw [PtrAt, K₂.1 _ (by decide)]; exact ebp
  refine wp_storeS (ea_ptr ht₂ ebp₂ (d := 0) (by omega_using [hx, hj]))
    (ws_write ht₂ (y := x + 4 * j + 0) (n := 4) (by omega_using [hx, hj])) fun s₃ m₃ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => wp_subZ rfl fun s₅ u₅ z₅ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf edx hj
  have edx₄ : s₄.gpr .edx = t.gpr .edx := by rw [u₄.other _ (by decide), m₃.gpr, K₂.1 _ (by decide)]
  have mem₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have eax₂ : s₂.gpr .eax = t.mem.readW (off W (x + 4 * j)) 32 &&& cmask c := by
    rw [u₂.gpr, show s₁.gpr .ecx = t.gpr .ecx from u₁.other _ (by decide), ecx, u₁.gpr, Nat.add_zero]; rfl
  have word : w32 t.mem W (x + 4 * j) = w32 t₀.mem W (x + 4 * j) :=
    O.w32 (by omega_using []) (by omega_using [hx, hj, hn])
  have K₅ : Keeps [.eax, .ebp, .edx] t s₅ :=
    (((K₂.mono (by decide)).widen (m₃.keeps [])).widen u₄.keeps).widen u₅.keeps
  refine ⟨⟨Kt.trans K₅, ?_, by rw [u₅.gpr, edx₄]; exact c₁, ?_, ?_⟩, by rw [z₅, edx₄, c₂]⟩
  · rw [PtrAt, u₅.other _ (by decide), u₄.gpr, m₃.gpr]; exact ptr4 ebp₂
  · rw [u₅.mem, u₄.mem, m₃.mem, mem₂, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hx, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₅.mem, u₄.mem, m₃.mem, mem₂, Nat.add_zero, val32_store hn (by omega_using [hx, hj]), V, eax₂,
      val32_succ t₀.mem W x]
    have hw32 : (t.mem.readW (off W (x + 4 * j)) 32).toNat = w32 t₀.mem W (x + 4 * j) := word
    cases c
    · simp only [Bool.false_eq_true, ite_false, cmask]
      rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.and_zero]; rfl
    · simp only [ite_true, cmask, BitVec.and_allOnes, hw32]

/-! ## Comparison -/

theorem compareLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x y N : Nat} (hN : 0 < N)
    (hx : x + 4 * N ≤ L) (hy : y + 4 * N ≤ L) (hesi : PtrAt t₀ W .esi x) (hebp : PtrAt t₀ W .ebp y)
    (hedx : (t₀.gpr .edx).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask false) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .alu .add .ecx (.reg .ecx),
      .alu .sbb .eax (.mem (at_ .ebp 0)), .alu .sbb .ecx (.reg .ecx), .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne) t₀
      fun u => u.mem = t₀.mem ∧ u.gpr .ecx = cmask (decide (val32 t₀.mem W x N < val32 t₀.mem W y N)) ∧
        Keeps [.eax, .ecx, .edx, .ebp, .esi] t₀ u := by
  have hn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ecx, .edx, .ebp, .esi] t₀ t ∧ t.mem = t₀.mem ∧
      PtrAt t W .esi (x + 4 * j) ∧ PtrAt t W .ebp (y + 4 * j) ∧ (t.gpr .edx).toNat = 4 * (N - j) ∧
      ∃ c : Bool, t.gpr .ecx = cmask c ∧ ∃ D, D < 2 ^ (32 * j) ∧
        D + val32 t₀.mem W y j = val32 t₀.mem W x j + 2 ^ (32 * j) * c.toNat) ?_
    ⟨Keeps.refl _ _, rfl, by simpa using hesi, by simpa using hebp, by simpa using hedx, false, hecx, 0,
      by simp, by simp [val32]⟩) fun u ⟨K, m, _, _, _, c, ec, D, hD, V⟩ => ⟨m, ?_, K⟩
  · rintro j t hj ⟨Kt, mt, esi, ebp, edx, c, ec, D, hD, V⟩
    have ht := hw.of_keeps Kt
    refine wp_movS (readSrc_ptr ht esi (d := 0) (by omega_using [hx, hj])) fun s₁ u₁ _ => ?_
    refine wp_carry (by rw [u₁.other _ (by decide), ec]) fun s₂ u₂ c₂ => ?_
    have K₂ : Keeps [.eax, .ecx] t s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
    have ht₂ := ht.of_keeps K₂
    have ebp₂ : PtrAt s₂ W .ebp (y + 4 * j) := by rw [PtrAt, K₂.1 _ (by decide)]; exact ebp
    refine wp_sbbS (readSrc_ptr ht₂ ebp₂ (d := 0) (by omega_using [hy, hj])) c₂ fun s₃ u₃ c₃ => ?_
    refine wp_sbb_self c₃ fun s₄ u₄ => ?_
    refine wp_addS rfl fun s₅ u₅ _ => wp_addS rfl fun s₆ u₆ _ => wp_subZ rfl fun s₇ u₇ z₇ => WP.block_nil ?_
    obtain ⟨c₁, c₂'⟩ := count_zf edx hj
    have K₄ : Keeps [.eax, .ecx] t s₄ := (K₂.widen u₃.keeps).widen u₄.keeps
    have r₄ : ∀ r, r = .esi ∨ r = .ebp ∨ r = .edx → s₄.gpr r = t.gpr r := by
      intro r hr; apply K₄.1; rcases hr with rfl | rfl | rfl <;> decide
    have m₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
    refine ⟨⟨(((Kt.widen K₄).widen u₅.keeps).widen u₆.keeps).widen u₇.keeps, ?_, ?_, ?_, ?_,
      decide (w32 t₀.mem W (x + 4 * j) < w32 t₀.mem W (y + 4 * j) + c.toNat), ?_, ?_⟩, ?_⟩
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, mt]
    · rw [PtrAt, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, r₄ _ (.inl rfl)]; exact ptr4 esi
    · rw [PtrAt, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), r₄ _ (.inr (.inl rfl))]; exact ptr4 ebp
    · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), r₄ _ (.inr (.inr rfl))]; exact c₁
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
      have eax₂ : (s₂.gpr .eax).toNat = w32 t₀.mem W (x + 4 * j) := by
        rw [u₂.other _ (by decide), u₁.gpr, Nat.add_zero, mt]
      have src₂ : (s₂.mem.readW (off W (y + 4 * j + 0)) 32).toNat = w32 t₀.mem W (y + 4 * j) := by
        rw [m₂, mt, Nat.add_zero]
      rw [eax₂, src₂]
    · have h := sbb_rel (s₂.gpr .eax) (s₂.mem.readW (off W (y + 4 * j + 0)) 32) c
      have eax₂ : (s₂.gpr .eax).toNat = w32 t₀.mem W (x + 4 * j) := by
        rw [u₂.other _ (by decide), u₁.gpr, Nat.add_zero, mt]
      have src₂ : (s₂.mem.readW (off W (y + 4 * j + 0)) 32).toNat = w32 t₀.mem W (y + 4 * j) := by
        rw [m₂, mt, Nat.add_zero]
      rw [eax₂, src₂] at h
      refine ⟨D + 2 ^ (32 * j) * (s₂.gpr .eax - s₂.mem.readW (off W (y + 4 * j + 0)) 32 -
        (BitVec.ofBool c).setWidth 32).toNat, ?_, ?_⟩
      · have := (s₂.gpr .eax - s₂.mem.readW (off W (y + 4 * j + 0)) 32 - (BitVec.ofBool c).setWidth 32).isLt
        rw [pow32_succ]
        have : 2 ^ (32 * j) * (s₂.gpr .eax - s₂.mem.readW (off W (y + 4 * j + 0)) 32 -
            (BitVec.ofBool c).setWidth 32).toNat ≤ 2 ^ (32 * j) * (2 ^ 32 - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have : 2 ^ (32 * j) * (2 ^ 32 - 1) + 2 ^ (32 * j) = 2 ^ (32 * j) * 2 ^ 32 := by
          rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by decide))]
        omega
      · rw [val32_succ t₀.mem W x, val32_succ t₀.mem W y, pow32_succ]
        exact chain_sub_step V h
    · rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), r₄ _ (.inr (.inr rfl)), c₂']
  · -- The borrow of the whole difference.
    have hX := val32_lt t₀.mem W x N
    have hY := val32_lt t₀.mem W y N
    rw [ec]
    congr 1
    cases c
    · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at V
      exact (decide_eq_false (by omega)).symm
    · simp only [Bool.toNat_true, Nat.mul_one] at V
      exact (decide_eq_true (by omega)).symm

end VG.Proof.Bignum.X86.PublicRt
