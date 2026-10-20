module

import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # The doubling, subtraction and selection loops of public RSA at a run-time width -/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

/-! ## Doubling -/

theorem doubleLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x a N : Nat} (hN : 0 < N)
    (hx : x + 4 * N ≤ L) (ha : a + 4 * N ≤ L) (hxa : a + 4 * N ≤ x ∨ x + 4 * N ≤ a)
    (hebx : PtrAt t₀ W .ebx x) (hebp : PtrAt t₀ W .ebp a)
    (hedx : (t₀.gpr .edx).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask false) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .ebx 0)), .alu .add .ecx (.reg .ecx),
      .alu .adc .eax (.reg .eax), .store (at_ .ebp 0) .eax, .alu .sbb .ecx (.reg .ecx),
      .alu .add .ebx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne) t₀
      fun u => Outside W a (4 * N) t₀.mem u.mem ∧ PtrAt u W .ebp (a + 4 * N) ∧
        (∃ c : Bool, u.gpr .ecx = cmask c ∧
          val32 u.mem W a N + 2 ^ (32 * N) * c.toNat = val32 t₀.mem W x N + val32 t₀.mem W x N) ∧
        Keeps [.eax, .ebx, .ecx, .edx, .ebp] t₀ u := by
  have hn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .ecx, .edx, .ebp] t₀ t ∧
      PtrAt t W .ebx (x + 4 * j) ∧ PtrAt t W .ebp (a + 4 * j) ∧ (t.gpr .edx).toNat = 4 * (N - j) ∧
      Outside W a (4 * j) t₀.mem t.mem ∧ ∃ c : Bool, t.gpr .ecx = cmask c ∧
        val32 t.mem W a j + 2 ^ (32 * j) * c.toNat = val32 t₀.mem W x j + val32 t₀.mem W x j) ?_
    ⟨Keeps.refl _ _, by simpa using hebx, by simpa using hebp, by simpa using hedx, Outside.refl _ _ _ _,
      false, hecx, by simp [val32]⟩) fun u ⟨K, _, ebp, _, O, V⟩ => ⟨O, ebp, V, K⟩
  rintro j t hj ⟨Kt, ebx, ebp, edx, O, c, ec, V⟩
  have ht := hw.of_keeps Kt
  have xw : w32 t.mem W (x + 4 * j) = w32 t₀.mem W (x + 4 * j) :=
    O.w32 (by omega_using [hxa, hj]) (by omega_using [hx, hj, hn])
  refine wp_movS (readSrc_ptr ht ebx (d := 0) (by omega_using [hx, hj])) fun s₁ u₁ _ => ?_
  refine wp_carry (by rw [u₁.other _ (by decide), ec]) fun s₂ u₂ c₂ => ?_
  refine wp_adcS rfl c₂ fun s₃ u₃ c₃ => ?_
  have K₃ : Keeps [.eax, .ecx] t s₃ := ((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps
  have ht₃ := ht.of_keeps K₃
  have ebp₃ : PtrAt s₃ W .ebp (a + 4 * j) := by rw [PtrAt, K₃.1 _ (by decide)]; exact ebp
  refine wp_storeS (ea_ptr ht₃ ebp₃ (d := 0) (by omega_using [ha, hj]))
    (ws_write ht₃ (y := a + 4 * j + 0) (n := 4) (by omega_using [ha, hj])) fun s₄ m₄ => ?_
  refine wp_sbb_self (by rw [m₄.cf]; exact c₃) fun s₅ u₅ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => wp_addS rfl fun s₇ u₇ _ => wp_subZ rfl fun s₈ u₈ z₈ => WP.block_nil ?_
  obtain ⟨c₁, c₂'⟩ := count_zf edx hj
  have K₅ : Keeps [.eax, .ecx] t s₅ := (K₃.widen (m₄.keeps [])).widen u₅.keeps
  have r₅ : ∀ r, r = .ebx ∨ r = .ebp ∨ r = .edx → s₅.gpr r = t.gpr r := by
    intro r hr; apply K₅.1; rcases hr with rfl | rfl | rfl <;> decide
  have eax₂ : s₂.gpr .eax = t.mem.readW (off W (x + 4 * j)) 32 := by
    rw [u₂.other _ (by decide), u₁.gpr, Nat.add_zero]
  have m₃ : s₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have xw' : (t.mem.readW (off W (x + 4 * j)) 32).toNat = w32 t₀.mem W (x + 4 * j) := xw
  refine ⟨⟨Kt.trans ((((K₅.mono (by decide)).widen u₆.keeps).widen u₇.keeps).widen u₈.keeps), ?_, ?_, ?_, ?_,
    decide (2 ^ 32 ≤ (s₂.gpr .eax).toNat + (s₂.gpr .eax).toNat + c.toNat), ?_, ?_⟩, ?_⟩
  · rw [PtrAt, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, r₅ _ (.inl rfl)]; exact ptr4 ebx
  · rw [PtrAt, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), r₅ _ (.inr (.inl rfl))]; exact ptr4 ebp
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), r₅ _ (.inr (.inr rfl))]; exact c₁
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄.mem, m₃, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [ha, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄.mem, m₃, Nat.add_zero, val32_store hn (by omega_using [ha, hj]),
      val32_succ t₀.mem W x, pow32_succ, u₃.gpr]
    have h := adc_rel (s₂.gpr .eax) (s₂.gpr .eax) c
    rw [eax₂, xw'] at h ⊢
    exact chain_add_step V h
  · rw [z₈, u₇.other _ (by decide), u₆.other _ (by decide), r₅ _ (.inr (.inr rfl)), c₂']

/-! ## Subtraction -/

theorem reduceLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {a m d N : Nat} (hN : 0 < N)
    (ha : a + 4 * N ≤ L) (hm : m + 4 * N ≤ L) (hd : d + 4 * N ≤ L)
    (hda : d + 4 * N ≤ a ∨ a + 4 * N ≤ d) (hdm : d + 4 * N ≤ m ∨ m + 4 * N ≤ d)
    (hebp : PtrAt t₀ W .ebp a) (hebx : PtrAt t₀ W .ebx m) (hedi : PtrAt t₀ W .edi d)
    (hedx : (t₀.gpr .edx).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask false) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .add .ecx (.reg .ecx),
      .alu .sbb .eax (.mem (at_ .ebx 0)), .store (at_ .edi 0) .eax, .alu .sbb .ecx (.reg .ecx),
      .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .add .edi (.imm 4),
      .alu .sub .edx (.imm 4)]) .ne) t₀
      fun u => Outside W d (4 * N) t₀.mem u.mem ∧ PtrAt u W .ebp (a + 4 * N) ∧
        (∃ c : Bool, u.gpr .ecx = cmask c ∧
          val32 u.mem W d N + val32 t₀.mem W m N = val32 t₀.mem W a N + 2 ^ (32 * N) * c.toNat) ∧
        Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] t₀ u := by
  have hn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] t₀ t ∧
      PtrAt t W .ebp (a + 4 * j) ∧ PtrAt t W .ebx (m + 4 * j) ∧ PtrAt t W .edi (d + 4 * j) ∧
      (t.gpr .edx).toNat = 4 * (N - j) ∧ Outside W d (4 * j) t₀.mem t.mem ∧ ∃ c : Bool, t.gpr .ecx = cmask c ∧
        val32 t.mem W d j + val32 t₀.mem W m j = val32 t₀.mem W a j + 2 ^ (32 * j) * c.toNat) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hebx, by simpa using hedi, by simpa using hedx,
      Outside.refl _ _ _ _, false, hecx, by simp [val32]⟩) fun u ⟨K, ebp, _, _, _, O, V⟩ => ⟨O, ebp, V, K⟩
  rintro j t hj ⟨Kt, ebp, ebx, edi, edx, O, c, ec, V⟩
  have ht := hw.of_keeps Kt
  have aw : w32 t.mem W (a + 4 * j) = w32 t₀.mem W (a + 4 * j) :=
    O.w32 (by omega_using [hda, hj]) (by omega_using [ha, hj, hn])
  have mw : w32 t.mem W (m + 4 * j) = w32 t₀.mem W (m + 4 * j) :=
    O.w32 (by omega_using [hdm, hj]) (by omega_using [hm, hj, hn])
  refine wp_movS (readSrc_ptr ht ebp (d := 0) (by omega_using [ha, hj])) fun s₁ u₁ _ => ?_
  refine wp_carry (by rw [u₁.other _ (by decide), ec]) fun s₂ u₂ c₂ => ?_
  have K₂ : Keeps [.eax, .ecx] t s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
  have ht₂ := ht.of_keeps K₂
  have ebx₂ : PtrAt s₂ W .ebx (m + 4 * j) := by rw [PtrAt, K₂.1 _ (by decide)]; exact ebx
  refine wp_sbbS (readSrc_ptr ht₂ ebx₂ (d := 0) (by omega_using [hm, hj])) c₂ fun s₃ u₃ c₃ => ?_
  have K₃ : Keeps [.eax, .ecx] t s₃ := K₂.widen u₃.keeps
  have ht₃ := ht.of_keeps K₃
  have edi₃ : PtrAt s₃ W .edi (d + 4 * j) := by rw [PtrAt, K₃.1 _ (by decide)]; exact edi
  refine wp_storeS (ea_ptr ht₃ edi₃ (d := 0) (by omega_using [hd, hj]))
    (ws_write ht₃ (y := d + 4 * j + 0) (n := 4) (by omega_using [hd, hj])) fun s₄ m₄ => ?_
  refine wp_sbb_self (by rw [m₄.cf]; exact c₃) fun s₅ u₅ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => wp_addS rfl fun s₇ u₇ _ => wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_subZ rfl fun s₉ u₉ z₉ => WP.block_nil ?_
  obtain ⟨c₁, c₂'⟩ := count_zf edx hj
  have K₅ : Keeps [.eax, .ecx] t s₅ := (K₃.widen (m₄.keeps [])).widen u₅.keeps
  have r₅ : ∀ r, r = .ebp ∨ r = .ebx ∨ r = .edi ∨ r = .edx → s₅.gpr r = t.gpr r := by
    intro r hr; apply K₅.1; rcases hr with rfl | rfl | rfl | rfl <;> decide
  have m₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have eax₂ : (s₂.gpr .eax).toNat = w32 t₀.mem W (a + 4 * j) := by
    rw [u₂.other _ (by decide), u₁.gpr, Nat.add_zero, ← aw]
  have src₂ : (s₂.mem.readW (off W (m + 4 * j + 0)) 32).toNat = w32 t₀.mem W (m + 4 * j) := by
    rw [m₂, Nat.add_zero, ← mw]
  refine ⟨⟨Kt.trans ((((K₅.mono (by decide)).widen u₆.keeps).widen u₇.keeps |>.widen u₈.keeps).widen u₉.keeps),
    ?_, ?_, ?_, ?_, ?_, decide ((s₂.gpr .eax).toNat < (s₂.mem.readW (off W (m + 4 * j + 0)) 32).toNat + c.toNat),
    ?_, ?_⟩, ?_⟩
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      r₅ _ (.inl rfl)]; exact ptr4 ebp
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      r₅ _ (.inr (.inl rfl))]; exact ptr4 ebx
  · rw [PtrAt, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      r₅ _ (.inr (.inr (.inl rfl)))]; exact ptr4 edi
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      r₅ _ (.inr (.inr (.inr rfl)))]; exact c₁
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄.mem, u₃.mem, m₂, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hd, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄.mem, u₃.mem, m₂, Nat.add_zero,
      val32_store hn (by omega_using [hd, hj]), val32_succ t₀.mem W m, val32_succ t₀.mem W a, pow32_succ, u₃.gpr]
    have h := sbb_rel (s₂.gpr .eax) (s₂.mem.readW (off W (m + 4 * j + 0)) 32) c
    rw [eax₂, src₂] at h
    rw [eax₂, show (t.mem.readW (off W (m + 4 * j + 0)) 32).toNat = w32 t₀.mem W (m + 4 * j) by
      rw [← m₂]; exact src₂]
    exact chain_sub_step V h
  · rw [z₉, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      r₅ _ (.inr (.inr (.inr rfl))), c₂']

/-! ## Selection -/

theorem selectLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x d N : Nat} (k : Bool) (hN : 0 < N)
    (hx : x + 4 * N ≤ L) (hd : d + 4 * N ≤ L) (hdx : d + 4 * N ≤ x ∨ x + 4 * N ≤ d)
    (hebp : PtrAt t₀ W .ebp x) (hebx : PtrAt t₀ W .ebx d)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask k) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .ebx 0)), .mov .edx (.mem (at_ .ebp 0)),
      .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
      .store (at_ .ebx 0) .eax, .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4),
      .alu .sub .edi (.imm 4)]) .ne) t₀
      fun u => Outside W d (4 * N) t₀.mem u.mem ∧
        val32 u.mem W d N = (if k then val32 t₀.mem W x N else val32 t₀.mem W d N) ∧
        PtrAt u W .ebx (d + 4 * N) ∧ Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ u := by
  have hn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ t ∧
      PtrAt t W .ebp (x + 4 * j) ∧ PtrAt t W .ebx (d + 4 * j) ∧ (t.gpr .edi).toNat = 4 * (N - j) ∧
      Outside W d (4 * j) t₀.mem t.mem ∧
      val32 t.mem W d j = (if k then val32 t₀.mem W x j else val32 t₀.mem W d j)) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hebx, by simpa using hedi, Outside.refl _ _ _ _,
      by cases k <;> rfl⟩) fun u ⟨K, _, P, _, O, V⟩ => ⟨O, V, P, K⟩
  rintro j t hj ⟨Kt, ebp, ebx, edi, O, V⟩
  have ht := hw.of_keeps Kt
  have ecx : t.gpr .ecx = cmask k := by rw [Kt.1 _ (by decide)]; exact hecx
  have xw : w32 t.mem W (x + 4 * j) = w32 t₀.mem W (x + 4 * j) :=
    O.w32 (by omega_using [hdx, hj]) (by omega_using [hx, hj, hn])
  have dw : w32 t.mem W (d + 4 * j) = w32 t₀.mem W (d + 4 * j) :=
    O.w32 (by omega_using []) (by omega_using [hd, hj, hn])
  refine wp_movS (readSrc_ptr ht ebx (d := 0) (by omega_using [hd, hj])) fun s₁ u₁ _ => ?_
  have ht₁ := ht.of_keeps u₁.keeps
  have ebp₁ : PtrAt s₁ W .ebp (x + 4 * j) := by rw [PtrAt, u₁.other _ (by decide)]; exact ebp
  refine wp_movS (readSrc_ptr ht₁ ebp₁ (d := 0) (by omega_using [hx, hj])) fun s₂ u₂ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₃ u₃ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
  have K₅ : Keeps [.eax, .edx] t s₅ :=
    (((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps |>.widen u₄.keeps).widen u₅.keeps
  have ht₅ := ht.of_keeps K₅
  have ebx₅ : PtrAt s₅ W .ebx (d + 4 * j) := by rw [PtrAt, K₅.1 _ (by decide)]; exact ebx
  refine wp_storeS (ea_ptr ht₅ ebx₅ (d := 0) (by omega_using [hd, hj]))
    (ws_write ht₅ (y := d + 4 * j + 0) (n := 4) (by omega_using [hd, hj])) fun s₆ m₆ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => wp_addS rfl fun s₈ u₈ _ => wp_subZ rfl fun s₉ u₉ z₉ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf edi hj
  have r₆ : ∀ r, r = .ebp ∨ r = .ebx ∨ r = .edi → s₆.gpr r = t.gpr r := by
    intro r hr; rw [m₆.gpr]; apply K₅.1; rcases hr with rfl | rfl | rfl <;> decide
  have mem₅ : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have ecx₃ : s₃.gpr .ecx = t.gpr .ecx := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have eax₅ : s₅.gpr .eax = t.mem.readW (off W (d + 4 * j)) 32 ^^^
      ((t.mem.readW (off W (x + 4 * j)) 32 ^^^ t.mem.readW (off W (d + 4 * j)) 32) &&&
        (if k then BitVec.allOnes 32 else 0)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₄.gpr, ecx₃, ecx, u₃.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem, Nat.add_zero, Nat.add_zero]
    rfl
  rw [select_val] at eax₅
  refine ⟨⟨Kt.trans ((((K₅.mono (by decide)).widen (m₆.keeps [])).widen u₇.keeps |>.widen u₈.keeps).widen u₉.keeps),
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, r₆ _ (.inl rfl)]; exact ptr4 ebp
  · rw [PtrAt, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), r₆ _ (.inr (.inl rfl))]; exact ptr4 ebx
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), r₆ _ (.inr (.inr rfl))]; exact c₁
  · rw [u₉.mem, u₈.mem, u₇.mem, m₆.mem, mem₅, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hd, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₉.mem, u₈.mem, u₇.mem, m₆.mem, mem₅, Nat.add_zero, val32_store hn (by omega_using [hd, hj]), V, eax₅,
      val32_succ t₀.mem W x, val32_succ t₀.mem W d]
    have xw' : (t.mem.readW (off W (x + 4 * j)) 32).toNat = w32 t₀.mem W (x + 4 * j) := xw
    have dw' : (t.mem.readW (off W (d + 4 * j)) 32).toNat = w32 t₀.mem W (d + 4 * j) := dw
    cases k
    · simp only [Bool.false_eq_true, ite_false, dw']
    · simp only [ite_true, xw']
  · rw [z₉, u₈.other _ (by decide), u₇.other _ (by decide), r₆ _ (.inr (.inr rfl)), c₂]

end VG.Proof.Bignum.X86.PublicRt
