module

import VerifiedGarbage.Proof.Ffdh.X86.Cand.Halve
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num2
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Base

/-!
# The FFDH candidate on i686: a phase's preparation

`prepPhase j`: the context of the modulus `w` in wide slot `j` (its
Montgomery inverse and `R² mod w`), one in slot 14, `w − 1` in slot 15,
and `w − 1 = 2^s d` with `d` odd: `d` in slot 11 and `s` in the header,
by halving `w − 1` while it is even (`prepPhase_ok`, `splitTwos_of`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- Halvings while even find the split of `m`. -/
theorem splitTwos_of : ∀ (k m : Nat), 0 < m → (∀ i < k, (m / 2 ^ i) % 2 = 0) → (m / 2 ^ k) % 2 = 1 →
    Spec.Rsa.splitTwos m = (k, m / 2 ^ k)
  | 0, m, _, _, hodd => by
    simp only [Nat.pow_zero, Nat.div_one] at hodd ⊢
    exact VG.Proof.Rsa.splitTwos_odd hodd
  | k + 1, m, hm, heven, hodd => by
    have h0 := heven 0 (by omega)
    simp only [Nat.pow_zero, Nat.div_one] at h0
    rw [VG.Proof.Rsa.splitTwos_even (by omega) h0]
    have ih := splitTwos_of k (m / 2) (by omega) (fun i hi => by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']; exact heven (i + 1) (by omega))
      (by rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']; exact hodd)
    rw [ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-- `o = a − b` for wide slots, with `b ≤ a`. -/
theorem subW_ok (h : In Ex base bytes len args s) {o a b : Nat} (ho : o ≤ 19) (ha : a ≤ 19) (hb : b ≤ 19)
    (hoa : o ≠ a) (hob : o ≠ b) (hle : sv s.mem base len .wide b ≤ sv s.mem base len .wide a) :
    WP isa (chain .sbb (.slot .wide o) (.slot .wide a) (.slot .wide b) (one .wide)) s fun u =>
      Step Ex base bytes len args s u ∧
      sv u.mem base len .wide o = sv s.mem base len .wide a - sv s.mem base len .wide b ∧
      Kept base len [o] [] s.mem u.mem ∧ Outside base (lo len (.slot .wide o)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  refine WP.mono (chainSub_ok h (one_ok .wide) (slot_fit1 h (by omega)) (slot_fit1 h (by omega))
    (slot_fit1 h (by omega)) (apart1 len hoa) (apart1 len hob)) fun u ⟨O, _, ⟨c, _, V⟩, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  refine ⟨Step.slot h (by omega) O K, ?_, kept_slot h O, O, K⟩
  change sv u.mem base len .wide o + sv s.mem base len .wide b = sv s.mem base len .wide a +
    2 ^ (32 * cwc len .wide) * c.toNat at V
  have lt := val32_lt u.mem base (lo len (.slot .wide o)) (cwc len .wide)
  have lta := val32_lt s.mem base (lo len (.slot .wide a)) (cwc len .wide)
  change sv u.mem base len .wide o < _ at lt
  change sv s.mem base len .wide a < _ at lta
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at V <;> omega

/-- The wide slot `a` copied into `b`, with the bytes it changes. -/
theorem copyO_ok (h : In Ex base bytes len args s) {a b : Nat} (ha : a ≤ 19) (hb : b ≤ 19) (hab : a ≠ b) :
    WP isa (copy (.slot .wide a) (.slot .wide b) (one .wide)) s fun u => Step Ex base bytes len args s u ∧
      sv u.mem base len .wide b = sv s.mem base len .wide a ∧ Kept base len [b] [] s.mem u.mem ∧
      Outside base (lo len (.slot .wide b)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  refine WP.mono (copy_ok h (x := .slot .wide a) (d := .slot .wide b) (one_ok .wide)
    (slot_fit1 h (by omega)) (slot_fit1 h (by omega)) (apart1 len (Ne.symm hab))) fun u ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨Step.slot h (by omega) O K, V, kept_slot h O, O, K⟩

/-- A modulus's context, ready for its powers: the context, one in slot 3 and `R² mod w` in slot 4. -/
structure Ready (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (w : Nat) (t : State) : Prop where
  ctx : CtxOk Ex base bytes len args .wide w t
  one : sv t.mem base len .wide 3 = 1
  r2 : sv t.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % w

/-- A write into a wide slot from 5 to 27 keeps a context ready. -/
theorem Ready.slot {w : Nat} (R : Ready Ex base bytes len args w s) {t : State} {a : Nat} (ha9 : 5 ≤ a)
    (ha : a ≤ 27) {rs : List Reg} (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs)
    (O : Outside base (lo len (.slot .wide a)) (bc len .wide) s.mem t.mem) : Ready Ex base bytes len args w t := by
  have h := R.ctx.inp
  have bl := h.bytes_lt
  have f := slot_fit1 h ha
  rw [cb1] at f
  have ea := lo_wide len a
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have := Nat.mul_le_mul_right (st len .wide) ha9
  refine ⟨R.ctx.keepF K di sp (ws := [(lo len (.slot .wide a), bc len .wide)])
    (frameR_of_outside O (by omega) (List.mem_singleton_self _)) (by simp; omega) (by simp; omega), ?_, ?_⟩
  · rw [← R.one]; exact slotKeep h (by decide) (by omega) O
  · rw [← R.r2]; exact slotKeep h (by decide) (by omega) O

/-- A write into a header word keeps a context ready. -/
theorem Ready.hdr {w : Nat} (R : Ready Ex base bytes len args w s) {t : State} {d : Nat} (hd : Hdr d)
    {rs : List Reg} (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs)
    (O : Outside base d 4 s.mem t.mem) : Ready Ex base bytes len args w t := by
  have h := R.ctx.inp
  have bl := h.bytes_lt
  have hf := hdr_fit h hd
  have nb : numBase = 3336 := rfl
  have e3 := lo_wide len 3
  have e4 := lo_wide len 4
  have f4 := slot_fit1 h (j := 4) (by decide)
  rw [cb1] at f4
  have bw := bc_eq_cwc len .wide
  refine ⟨R.ctx.keepF2 K di sp (ws := [(d, 4)]) (frameR_of_outside O (by omega) (List.mem_singleton_self _))
    (by simp; omega) (by simp; rcases hd.1 with e | e <;> omega), ?_, ?_⟩
  · rw [← R.one]; exact O.val32 (.inr (by omega)) (by omega)
  · rw [← R.r2]; exact O.val32 (.inr (by omega)) (by omega)

theorem Ready.regs {w : Nat} (R : Ready Ex base bytes len args w s) {t : State} {rs : List Reg}
    (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs) (m : t.mem = s.mem) : Ready Ex base bytes len args w t :=
  ⟨R.ctx.keepF K di sp (ws := []) (by rw [m]; exact Frame.refl _ _) (fun _ h => nomatch h) (fun _ h => nomatch h),
    by rw [m]; exact R.one, by rw [m]; exact R.r2⟩

/-- The context of the modulus in wide slot `j`, ready. -/
theorem ready_ok (h : In Ex base bytes len args s) {j w : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 19)
    (hw : sv s.mem base len .wide j = w) (hw1 : 1 < w) (hodd : w % 2 = 1) :
    WP isa (.seq (copy (.slot .wide j) (.slot .wide 0) (one .wide)) (prepare .wide)) s fun t =>
      Step Ex base bytes len args s t ∧ Ready Ex base bytes len args w t ∧ Kept base len [] [] s.mem t.mem := by
  have bl := h.bytes_lt
  have f0 := h.slot_fit .wide (j := 0) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  refine WP.seq (WP.mono (copyIn_ok h (j := j) (d := 0) hj9 hj (by decide)) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have F₁ : Frame (frameR base (s.gpr .esp) (stR len 0)) s.mem u₁.mem :=
    stR_of_outside h (by decide) O₁ ⟨_, by simp, slot_in h .wide (j := 0) (by decide)⟩
  have S₁ : Step Ex base bytes len args s u₁ := Step.ops h F₁ K₁
  refine WP.mono (prepCtx_ok S₁.inp .wide) fun u ⟨C, one, R2, F, K⟩ => ?_
  rw [V₁, hw, safeM_of hw1 hodd] at C R2
  have F₂ := stR_widen F (prepR_in S₁.inp .wide 0)
  rw [S₁.esp] at F₂
  exact ⟨S₁.trans (Step.ops S₁.inp (by rw [S₁.esp]; exact F₂) K), ⟨C, one, R2⟩,
    (kept_ops h F₁ h.room).trans (kept_ops h F₂ h.room)⟩

/-- What a phase's preparation leaves for the modulus `w`: its context ready, one in slot 14,
`w − 1` in slot 15, and its split `w − 1 = 2^s d`: `d` in slot 11, `s` in the header. -/
structure Prepped (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (w : Nat) (t : State) : Prop extends Ready Ex base bytes len args w t where
  one14 : sv t.mem base len .wide 14 = 1
  m1 : sv t.mem base len .wide 15 = w - 1
  exp : sv t.mem base len .wide 11 = (Spec.Rsa.splitTwos (w - 1)).2
  two : w32 t.mem base twoOff = (Spec.Rsa.splitTwos (w - 1)).1

/-- The halvings so far: slot 11 holds `(w − 1) / 2^k`, even and positive, and the header `k`. -/
structure Halving (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (s : State) (w k : Nat) (t : State) : Prop where
  step : Step Ex base bytes len args s t
  ready : Ready Ex base bytes len args w t
  one14 : sv t.mem base len .wide 14 = 1
  m1 : sv t.mem base len .wide 15 = w - 1
  exp : sv t.mem base len .wide 11 = (w - 1) / 2 ^ k
  two : w32 t.mem base twoOff = k
  even : ∀ i < k, ((w - 1) / 2 ^ i) % 2 = 0
  kept : Kept base len [11, 14, 15] [twoOff] s.mem t.mem

theorem hdr_two : Hdr twoOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩

/-- One halving of the split. -/
theorem halveIter_ok {w k : Nat} {t : State} (H : Halving Ex base bytes len args s w k t)
    (hx : ((w - 1) / 2 ^ k) % 2 = 0) (hp : 0 < (w - 1) / 2 ^ k) (hwl : w < 2 ^ (32 * cwc len .wide)) :
    WP isa (.seq (halve (.slot .wide 11)) (.block (([.mov .eax (.mem (sc twoOff)), .alu .add .eax (.imm 1),
      .store (sc twoOff) .eax] : List Instr) ++ lowWord (.slot .wide 11) ++ ([.alu .and .eax (.imm 1)] : List Instr)))) t fun u =>
      Halving Ex base bytes len args s w (k + 1) u ∧
        isa.eval .e u = some (decide (((w - 1) / 2 ^ (k + 1)) % 2 = 0)) := by
  have ht := H.step.inp
  have bl := ht.bytes_lt
  have nb : numBase = 3336 := rfl
  have kl : k + 1 < 2 ^ 32 := by
    have p1 : 2 ^ k ≤ w - 1 := (Nat.div_pos_iff.mp hp).2
    have p2 : 2 ^ k < 2 ^ (32 * cwc len .wide) := by omega
    have p3 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp p2
    have := bc_le ht.upper' .wide
    simp only [cwc] at p3
    omega
  have half : (w - 1) / 2 ^ (k + 1) = (w - 1) / 2 ^ k / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  refine WP.seq (WP.mono (halve_ok ht (j := 11) (by decide)) fun u₁ ⟨h₁, O₁, V₁, K₁⟩ => ?_)
  rw [H.exp] at V₁
  have two₁ : w32 u₁.mem base twoOff = k := by
    rw [← H.two]
    have := lo_wide len 11
    exact O₁.w32 (.inl (by simp only [twoOff]; omega)) (by simp only [twoOff]; omega)
  simp only [List.cons_append, List.append_assoc]
  refine wp_movS (hdr_read h₁ hdr_two) fun u₂ U₂ _ => wp_addi fun u₃ U₃ => ?_
  refine hdr_store (h₁.regs ((U₂.keeps.trans U₃.keeps).mono (by decide) : Keeps [.eax] u₁ u₃)
    (by rw [U₃.mem, U₂.mem])) hdr_two fun u₄ S₄ W₄ k₄ O₄ G₄ _ _ => ?_
  refine lowWord_ok S₄.inp (j := 11) (by decide) fun u₅ m₅ K₅ e₅ => wp_andZ fun u U z => WP.block_nil ?_
  have S₃ : Step Ex base bytes len args u₁ u₃ := Step.regs h₁ (by rw [U₃.mem, U₂.mem]) (U₂.keeps.trans U₃.keeps)
  have S₅ : Step Ex base bytes len args u₄ u := Step.regs S₄.inp (by rw [U.mem, m₅]) (K₅.trans (U.keeps.mono (by decide)))
  have S₁ : Step Ex base bytes len args t u₁ := Step.slot ht (by decide) O₁ K₁
  have sv₄ : sv u₄.mem base len .wide 11 = (w - 1) / 2 ^ k / 2 := by
    rw [k₄.slot_eq, U₃.mem, U₂.mem, V₁]
  refine ⟨⟨H.step.trans (S₁.trans (S₃.trans (S₄.trans S₅))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have R₁ := H.ready.slot (a := 11) (by decide) (by decide) K₁ (by decide) (by decide) O₁
    have R₃ := R₁.regs (U₂.keeps.trans U₃.keeps) (by decide) (by decide) (by rw [U₃.mem, U₂.mem])
    exact (R₃.hdr hdr_two S₄.keeps (by decide) (by decide) O₄).regs (K₅.trans (U.keeps.mono (by decide))) (by decide) (by decide)
      (by rw [U.mem, m₅])
  · rw [U.mem, m₅, k₄.slot_eq, U₃.mem, U₂.mem, slotKeep ht (by decide) (by decide) O₁, H.one14]
  · rw [U.mem, m₅, k₄.slot_eq, U₃.mem, U₂.mem, slotKeep ht (by decide) (by decide) O₁, H.m1]
  · rw [U.mem, m₅, sv₄, half]
  · rw [U.mem, m₅, W₄, U₃.gpr, U₂.gpr, two₁, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt kl]
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact H.even i hi
    · exact hx
  · have k₁ : Kept base len [11, 14, 15] [twoOff] t.mem u₁.mem := (kept_slot ht (a := 11) O₁).mono
    have k₃ : Kept base len [11, 14, 15] [twoOff] u₁.mem u₃.mem := by
      rw [U₃.mem, U₂.mem]; exact Kept.refl _ |>.mono
    have k₅ : Kept base len [11, 14, 15] [twoOff] u₄.mem u.mem := by
      rw [U.mem, m₅]; exact Kept.refl _ |>.mono
    exact H.kept.trans (k₁.trans (k₃.trans (k₄.mono.trans k₅)))
  · show u.zf = _
    rw [z, e₅, sv₄, and_one_zero _ (by omega), half, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 32)]


/-- The context of `w`, one, `w − 1` and its copy, and the count of halvings zero. -/
theorem prepHead_ok (h : In Ex base bytes len args s) {j w : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 10)
    (hw : sv s.mem base len .wide j = w) (hw3 : 3 ≤ w) (hodd : w % 2 = 1) :
    WP isa (prepHead j) s (Halving Ex base bytes len args s w 0) := by
  have bl := h.bytes_lt
  have bw := bc_eq_cwc len .wide
  unfold prepHead
  refine WP.assoc (WP.seq (WP.mono (ready_ok h hj9 (by omega) hw (by omega) hodd) fun u₁ ⟨S₁, R₁, k₁⟩ => ?_))
  have h₁ := S₁.inp
  refine WP.seq (WP.mono (setW_ok h₁ (a := 14) (v := 1) (by decide) (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  have S₂ : Step Ex base bytes len args s u₂ := S₁.trans (Step.slot h₁ (by decide) O₂ K₂)
  have R₂ := R₁.slot (a := 14) (by decide) (by decide) K₂ (by decide) (by decide) O₂
  have k₂ : Kept base len [11, 14, 15] [twoOff] s.mem u₂.mem := k₁.mono.trans (kept_slot h₁ (a := 14) O₂).mono
  have wj₂ : sv u₂.mem base len .wide j = w := by
    rw [slotKeep h₁ (by omega) (by omega) O₂, k₁.slot_eq ⟨hj9, by omega, by simp⟩, hw]
  refine WP.seq (WP.mono (subW_ok S₂.inp (o := 15) (a := j) (b := 14) (by decide) (by omega) (by decide) (by omega)
    (by decide) (by rw [V₂, wj₂]; omega)) fun u₃ ⟨S₃, V₃, k₃, O₃, K₃⟩ => ?_)
  rw [V₂, wj₂] at V₃
  have R₃ := R₂.slot (a := 15) (by decide) (by decide) K₃ (by decide) (by decide) O₃
  refine WP.seq (WP.mono (copyO_ok S₃.inp (a := 15) (b := 11) (by decide) (by decide) (by decide))
    fun u₄ ⟨S₄, V₄, k₄, O₄, K₄⟩ => ?_)
  have R₄ := R₃.slot (a := 11) (by decide) (by decide) K₄ (by decide) (by decide) O₄
  refine wp_movi fun u₅ U₅ => hdr_store (S₄.inp.regs U₅.keeps U₅.mem) hdr_two fun u₆ S₆ W₆ k₆ O₆ G₆ _ _ =>
    WP.block_nil ?_
  have S₅ : Step Ex base bytes len args u₄ u₅ := Step.regs S₄.inp U₅.mem U₅.keeps
  refine ⟨S₂.trans (S₃.trans (S₄.trans (S₅.trans S₆))), ((R₄.regs U₅.keeps (by decide) (by decide) U₅.mem).hdr hdr_two
    S₆.keeps (by decide) (by decide) O₆), ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega), ?_⟩
  · rw [k₆.slot_eq, U₅.mem, k₄.slot_eq, k₃.slot_eq, V₂]
  · rw [k₆.slot_eq, U₅.mem, k₄.slot_eq, V₃]
  · rw [k₆.slot_eq, U₅.mem, V₄, V₃, Nat.pow_zero, Nat.div_one]
  · rw [W₆, U₅.gpr]; rfl
  · exact k₂.trans (k₃.mono.trans (k₄.mono.trans ((by rw [U₅.mem]; exact Kept.refl _ : Kept base len [] [] u₄.mem u₅.mem).mono.trans
      k₆.mono)))

/-- The halving loop's invariant: `k` halvings done, `(w − 1) / 2^k` still even. -/
abbrev Halved (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s : State) (w x : Nat) (t : State) : Prop :=
  ∃ k, x = (w - 1) / 2 ^ k ∧ x % 2 = 0 ∧ 0 < x ∧ Halving Ex base bytes len args s w k t

/-- A halving, and whether to halve again. -/
theorem halveRound_ok {w x : Nat} {t : State} (hw3 : 3 ≤ w) (hodd : w % 2 = 1) (hwl : w < 2 ^ (32 * cwc len .wide))
    (H : Halved Ex base bytes len args s w x t) :
    WP isa (.seq (halve (.slot .wide 11)) (.block (([.mov .eax (.mem (sc twoOff)), .alu .add .eax (.imm 1),
      .store (sc twoOff) .eax] : List Instr) ++ lowWord (.slot .wide 11) ++ ([.alu .and .eax (.imm 1)] : List Instr)))) t fun u =>
      (isa.eval .e u = some false ∧ Step Ex base bytes len args s u ∧ Prepped Ex base bytes len args w u ∧
        Kept base len [11, 14, 15] [twoOff] s.mem u.mem) ∨
      (isa.eval .e u = some true ∧ ∃ x' < x, Halved Ex base bytes len args s w x' u) := by
  obtain ⟨k, rfl, hx, hp, H⟩ := H
  refine WP.mono (halveIter_ok H hx hp hwl) fun u ⟨Hu, z⟩ => ?_
  have half : (w - 1) / 2 ^ (k + 1) = (w - 1) / 2 ^ k / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  by_cases ev : ((w - 1) / 2 ^ (k + 1)) % 2 = 0
  · refine .inr ⟨by rw [z]; simp [ev], (w - 1) / 2 ^ (k + 1), by omega, k + 1, rfl, ev, by omega, Hu⟩
  · have od : ((w - 1) / 2 ^ (k + 1)) % 2 = 1 := by omega
    have sp := splitTwos_of (k + 1) (w - 1) (by omega) Hu.even od
    refine .inl ⟨by rw [z]; simp [ev], Hu.step, ⟨Hu.ready, Hu.one14, Hu.m1, by rw [Hu.exp, sp], by rw [Hu.two, sp]⟩,
      Hu.kept⟩

/-- The context of the modulus `w` in wide slot `j`, and the split `w − 1 = 2^s d`. -/
theorem prepPhase_ok (h : In Ex base bytes len args s) {j w : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 10)
    (hw : sv s.mem base len .wide j = w) (hw3 : 3 ≤ w) (hodd : w % 2 = 1) :
    WP isa (prepPhase j) s fun t => Step Ex base bytes len args s t ∧ Prepped Ex base bytes len args w t ∧
      Kept base len [11, 14, 15] [twoOff] s.mem t.mem := by
  have hwl : w < 2 ^ (32 * cwc len .wide) := by rw [← hw]; exact val32_lt _ _ _ _
  unfold prepPhase
  refine WP.seq (WP.mono (prepHead_ok h hj9 hj hw hw3 hodd) fun u₆ H₀ => ?_)
  refine WP.loop (M := isa) (Halved Ex base bytes len args s w) ?_ (w - 1) u₆ ⟨0, by simp, by omega, by omega, H₀⟩
  intro x t H
  refine WP.mono (halveRound_ok hw3 hodd hwl H) fun u o => ?_
  rcases o with ⟨e, r⟩ | ⟨e, r⟩
  · exact .inl ⟨e, r⟩
  · exact .inr ⟨e, r⟩

end VG.Proof.Ffdh.X86.Cand
