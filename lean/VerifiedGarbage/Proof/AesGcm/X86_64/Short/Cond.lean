import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Small
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp

/-!
# AES-GCM's short path on x86-64: the condition

Untrusted: everything here is checked by Lean. `cond` leaves ZF clear iff
the short path applies: a 12-byte nonce, fewer than 512 bytes of additional
data and of text, and fewer than 32 blocks of them (`cond_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.AesGcm.X86_64

/-- When the short path applies. -/
abbrev IsShort (nl al n : Nat) : Prop := nl = 12 ∧ al < 512 ∧ n < 512 ∧ nb16 al + nb16 n < 32

/-- Both below `512` iff their OR is. -/
theorem or_lt_512 {a b : Nat} : a ||| b < 512 ↔ a < 512 ∧ b < 512 := by
  constructor
  · intro h
    exact ⟨Nat.lt_of_le_of_lt Nat.left_le_or h, Nat.lt_of_le_of_lt Nat.right_le_or h⟩
  · rintro ⟨ha, hb⟩
    exact Nat.or_lt_two_pow (n := 9) ha hb

/-- What `cond` keeps. -/
structure CondKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem CondKeep.trans {s₁ s₂ s₃ : State} (h₁ : CondKeep s₁ s₂) (h₂ : CondKeep s₂ s₃) : CondKeep s₁ s₃ :=
  ⟨fun r a b c => (h₂.gpr r a b c).trans (h₁.gpr r a b c), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

/-- What `cond` reads: `W` in `r15`, the nonce's length in `rbp` and the
lengths of the additional data and the text in `W`. -/
structure CondS (W : Addr) (nl al n : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 = W
  w : Covers [⟨W, 2560⟩] s.wr
  rbp : s.gpr .rbp = BitVec.ofNat 64 nl
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n

theorem CondS.keep {W : Addr} {nl al n : Nat} {s t : State} (h : CondS W nl al n s) (k : CondKeep s t) :
    CondS W nl al n t :=
  ⟨by rw [k.gpr _ (by decide) (by decide) (by decide), h.r15], by rw [k.wr]; exact h.w,
    by rw [k.gpr _ (by decide) (by decide) (by decide), h.rbp], by rw [k.mem]; exact h.alen,
    by rw [k.mem]; exact h.len⟩

/-- `cond`'s first block: `rax := 0`, and the nonce's length compared with 12. -/
theorem condB1_ok {W : Addr} {nl al n : Nat} {s : State} (h : CondS W nl al n s) (hnl : nl < 2 ^ 64) :
    WP isa (.block [.mov32 .rax (imm 0), .alu .cmp .rbp (imm 12)]) s fun t =>
      t.zf = some (decide (nl = 12)) ∧ t.gpr .rax = 0 ∧ CondKeep s t := by
  obtain ⟨s₁, run₁, ax₁, k₁⟩ : ∃ s₁, runBlock isa [.mov32 .rax (imm 0)] s = some s₁ ∧
      s₁.gpr .rax = 0 ∧ CondKeep s s₁ := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r hr _ _; simp [gpr_setReg, hr]
    all_goals rfl
  obtain ⟨s₂, run₂, zf₂, -, g₂, m₂, rd₂, wr₂⟩ :=
    cmpImm_ok s₁ .rbp (by rw [k₁.gpr _ (by decide) (by decide) (by decide), h.rbp]) hnl (show 12 < 2 ^ 31 by decide)
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, zf₂, by rw [g₂, ax₁],
    k₁.trans ⟨fun r _ _ _ => by rw [g₂], m₂, rd₂, wr₂⟩⟩⟩)

/-- `cond`'s second block: the OR of the lengths compared with 512. -/
theorem condB2_ok {W : Addr} {nl al n : Nat} {s : State} (h : CondS W nl al n s) (hal : al < 2 ^ 64)
    (hn : n < 2 ^ 64) :
    WP isa (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .or .rcx (.mem (at_ .r15 lenO)),
        .alu .cmp .rcx (imm 512)]) s fun t =>
      t.cf = some (decide (al ||| n < 512)) ∧ t.gpr .rax = s.gpr .rax ∧ CondKeep s t := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 184) 8 := in_left (in_off h.w (by decide) (by decide))
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := in_left (in_off h.w (by decide) (by decide))
  have hal' := h.alen
  have hn' := h.len
  have h15 := h.r15
  have hor : BitVec.ofNat 64 al ||| BitVec.ofNat 64 n = BitVec.ofNat 64 (al ||| n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (Nat.or_lt_two_pow hal hn)]
  obtain ⟨s₃, run₃, cx₃, ax₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .rcx (.mem (at_ .r15 alenO)),
      .alu .or .rcx (.mem (at_ .r15 lenO))] s = some s₃ ∧ s₃.gpr .rcx = BitVec.ofNat 64 (al ||| n) ∧
      s₃.gpr .rax = s.gpr .rax ∧ CondKeep s s₃ := by
    refine ⟨_, by xrun [h15, hal', hn', r₁, r₂, alenO, lenO], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
      exact hor
    · simp [gpr_setReg, gpr_arithFlags]
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, b]
    all_goals rfl
  obtain ⟨s₄, run₄, -, cf₄, g₄, m₄, rd₄, wr₄⟩ :=
    cmpImm_ok s₃ .rcx cx₃ (Nat.or_lt_two_pow hal hn) (show 512 < 2 ^ 31 by decide)
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, cf₄, by rw [g₄, ax₃],
    k₃.trans ⟨fun r _ _ _ => by rw [g₄], m₄, rd₄, wr₄⟩⟩⟩)

/-- `cond`'s third block: the blocks of both lengths compared with 32. -/
theorem condB3_ok {W : Addr} {nl al n : Nat} {s : State} (h : CondS W nl al n s) (hal : al < 512) (hn : n < 512) :
    WP isa (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .add .rcx (imm 15), .shift .shr .rcx 4,
        .mov .rdx (.mem (at_ .r15 lenO)), .alu .add .rdx (imm 15), .shift .shr .rdx 4, .alu .add .rcx (.reg .rdx),
        .alu .cmp .rcx (imm 32)]) s fun t =>
      t.cf = some (decide (nb16 al + nb16 n < 32)) ∧ t.gpr .rax = s.gpr .rax ∧ CondKeep s t := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 184) 8 := in_left (in_off h.w (by decide) (by decide))
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := in_left (in_off h.w (by decide) (by decide))
  have hal' := h.alen
  have hn' := h.len
  have h15 := h.r15
  have e₁ : BitVec.ofNat 64 (al + 15) >>> 4 = BitVec.ofNat 64 (nb16 al) := shr4 _ (by omega)
  have e₂ : BitVec.ofNat 64 (n + 15) >>> 4 = BitVec.ofNat 64 (nb16 n) := shr4 _ (by omega)
  obtain ⟨s₅, run₅, cx₅, ax₅, k₅⟩ : ∃ s₅, runBlock isa [.mov .rcx (.mem (at_ .r15 alenO)), .alu .add .rcx (imm 15),
      .shift .shr .rcx 4, .mov .rdx (.mem (at_ .r15 lenO)), .alu .add .rdx (imm 15), .shift .shr .rdx 4,
      .alu .add .rcx (.reg .rdx)] s = some s₅ ∧ s₅.gpr .rcx = BitVec.ofNat 64 (nb16 al + nb16 n) ∧
      s₅.gpr .rax = s.gpr .rax ∧ CondKeep s s₅ := by
    refine ⟨_, by xrun [execShift, h15, hal', hn', r₁, r₂, alenO, lenO], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hal', hn', ofNat_add_ofNat, e₁, e₂]
    · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags]
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, b, c]
    all_goals rfl
  obtain ⟨s₆, run₆, -, cf₆, g₆, m₆, rd₆, wr₆⟩ :=
    cmpImm_ok s₅ .rcx cx₅ (by simp only [nb16]; omega) (show 32 < 2 ^ 31 by decide)
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₅, run₅, WP.of_runBlock ⟨s₆, run₆, cf₆, by rw [g₆, ax₅],
    k₅.trans ⟨fun r _ _ _ => by rw [g₆], m₆, rd₆, wr₆⟩⟩⟩)

/-- `cond`: ZF clear iff the short path applies, with `rbp` the nonce's length
and the lengths of the additional data and the text in `W`. -/
theorem cond_ok {s : State} {W : Addr} {nl al n : Nat} (h : CondS W nl al n s) (hnl : nl < 2 ^ 64)
    (hal : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    WP isa cond s fun s' => s'.zf = some (decide ¬IsShort nl al n) ∧ CondKeep s s' := by
  refine WP.seq (WP.mono (condB1_ok h hnl) fun s₂ ⟨zf₂, ax₂, k₂⟩ => ?_)
  -- `rax := 1` iff the short path applies.
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .rax = BitVec.ofNat 64 (if IsShort nl al n then 1 else 0) ∧
      CondKeep s s₃) (WP.ite (decide (nl = 12)) (eval_e zf₂) (fun h12 => ?_) (fun h12 => ?_)) fun s₃ ⟨ax₃, k₃⟩ => ?_)
  · have h12 : nl = 12 := by simpa using h12
    refine WP.seq (WP.mono (condB2_ok (h.keep k₂) hal hn) fun s₄ ⟨cf₄, ax₄, k₄⟩ => ?_)
    rw [ax₂] at ax₄
    refine WP.ite (decide (al ||| n < 512)) (eval_b cf₄) (fun h5 => ?_) (fun h5 => ?_)
    · have h5 : al < 512 ∧ n < 512 := or_lt_512.mp (by simpa using h5)
      refine WP.seq (WP.mono (condB3_ok ((h.keep k₂).keep k₄) h5.1 h5.2) fun s₆ ⟨cf₆, ax₆, k₆⟩ => ?_)
      rw [ax₄] at ax₆
      refine WP.ite (decide (nb16 al + nb16 n < 32)) (eval_b cf₆) (fun h32 => ?_) (fun h32 => ?_)
      · have h32 : nb16 al + nb16 n < 32 := by simpa using h32
        refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_⟩
        · simp [gpr_setReg, IsShort, h12, h5, h32]
        · exact k₂.trans (k₄.trans (k₆.trans ⟨fun r a _ _ => by simp [gpr_setReg, a], rfl, rfl, rfl⟩))
      · have h32 : ¬nb16 al + nb16 n < 32 := by simpa using h32
        exact WP.block_nil ⟨by simp [ax₆, IsShort, h32], k₂.trans (k₄.trans k₆)⟩
    · have h5 : ¬(al < 512 ∧ n < 512) := fun h => absurd (or_lt_512.mpr h) (by simpa using h5)
      refine WP.block_nil ⟨?_, k₂.trans k₄⟩
      have h5' : ¬IsShort nl al n := fun ⟨_, a, b, _⟩ => h5 ⟨a, b⟩
      rw [ax₄]
      simp only [h5', ↓reduceIte]
      rfl
  · have h12 : nl ≠ 12 := by simpa using h12
    refine WP.block_nil ⟨?_, k₂⟩
    rw [ax₂]
    simp [IsShort, h12]
  -- `test rax, rax`.
  refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_⟩
  · rw [zf_arithFlags, ax₃]
    split <;> rename_i h <;> simp [h]
  · exact k₃.trans ⟨fun r _ _ _ => by simp [gpr_arithFlags], rfl, rfl, rfl⟩

end VG.Proof.AesGcm.X86_64.Short
