module
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.X25519.AArch64
public import VerifiedGarbage.Proof.X25519.AArch64.Ops
public import Mathlib.Logic.Function.Basic

/-!
# X25519 on AArch64: the setup

`setup` saves our caller's registers, decodes the u-coordinate into `x1` and
`x3` (`decode`), stores the bits of the scalar, clamped, at `BITS` (`bits`),
and sets `x2 = 1`, `z2 = 0`, `z3 = 1` (`initSlots`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## Saving registers -/

/-- The region of the saved registers. -/
abbrev saveR (b : Addr) : Region := ⟨b, 48⟩

theorem saves_ok {b : Addr} : ∀ n ≤ 6, ∀ s : State, Sc b s →
    WP isa (.block ((List.range n).map fun k => st (saved.getD k .x19) (SAVE + 8 * k))) s fun s' =>
      (∀ k < n, wd s'.mem b (SAVE + 8 * k) = v s (saved.getD k .x19)) ∧ Frame [saveR b] s.mem s'.mem ∧
        Kp [] s s'
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (saves_ok n (by omega_arith) s hs) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    have hoff : ∀ k < 6, Off (SAVE + 8 * k) := fun k hk =>
      ⟨by simp only [SAVE]; omega_arith, by simp only [SAVE]; omega_arith⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_st hs₁ _ (hoff n (by omega_arith)), WP.block_nil ⟨fun k hk => ?_, ?_, ?_⟩⟩
    · simp only
      rw [wd_writeW _ _ _ (hoff n (by omega_arith)) (hoff k (by omega_arith))]
      by_cases hkn : k = n
      · subst hkn; rw [ite_eq_left rfl, k₁.gpr _ (List.not_mem_nil)]
      · rw [ite_eq_right (by omega_arith)]
        exact e₁ k (by omega_arith)
    · exact f₁.writeW (List.mem_singleton_self _) _
        (Offset.contains_base b (by simp only [SAVE]; omega_arith) (by simp only [SAVE]; omega_arith))
    · exact ⟨fun r _ => k₁.gpr r List.not_mem_nil, k₁.rd, k₁.wr⟩

theorem save_ok {b : Addr} {s : State} (hs : Sc b s) :
    WP isa (.block save) s fun s' =>
      (∀ k < 6, wd s'.mem b (SAVE + 8 * k) = v s (saved.getD k .x19)) ∧ Frame [saveR b] s.mem s'.mem ∧
        Kp [] s s' := saves_ok 6 (by decide) s hs

/-! ## The bits of the scalar -/

theorem write1_apply (m : Mem) (a x : Addr) (w : BitVec 8) : m.write a 1 w x = if x = a then w else m x := by
  by_cases h : x = a
  · subst h
    rw [ite_eq_left rfl]
    show (if (x - x).toNat < 1 then w.extractLsb' (8 * (x - x).toNat) 8 else m x) = w
    rw [BitVec.sub_self, BitVec.toNat_zero, ite_eq_left (by decide)]
    exact BitVec.extractLsb'_eq_self
  · have h1 : ¬ (x - a).toNat < 1 := by
      intro h1
      apply h
      have h0 : (x - a).toNat = 0 := by omega_arith
      have : x - a = 0 := BitVec.eq_of_toNat_eq (h0.trans rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    rw [ite_eq_right h, Mem.write_apply h1]

/-- Bit `j` of a byte, as a byte. -/
def bitB (kb : Byte) (j : Nat) : Byte := BitVec.ofNat 8 ((kb.toNat >>> j) &&& 1)

/-- The region of the bits of byte `i`. -/
abbrev bitsR (b : Addr) (i : Nat) : Region := ⟨b + BitVec.ofNat 64 (BITS + 8 * i), 8⟩

theorem bitStep_ok {b : Addr} {s : State} (hs : Sc b s) {i j : Nat} (hi : i < 32) (hj : j < 8)
    (h20 : s.gpr .x20 = 1) :
    WP isa (.block [.lsr .x .x19 .x17 j, .logic .and .x .x19 .x19 .x20, .strb .x19 .x3 (BITS + 8 * i + j)]) s
      fun s' => s'.mem = s.mem.write (b + BitVec.ofNat 64 (BITS + 8 * i + j)) 1
          (BitVec.ofNat 8 ((s.gpr .x17).toNat / 2 ^ j % 2)) ∧ Kp [.x19] s s' := by
  have hoff : BITS + 8 * i + j < 4096 := by simp only [BITS, slot, NSLOT]; omega_arith
  have hin : InRegions s.wr (b + BitVec.ofNat 64 (BITS + 8 * i + j)) 1 :=
    ⟨scR b, hs.wr, Offset.contains_base b (by simp only [BITS, slot, NSLOT]; omega_arith) (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_lsr (show j < 64 by omega_arith), runStep_some, exec_and_x, gpr_wx_self,
    gpr_wx_ne _ _ (show Reg.x20 ≠ .x19 by decide), h20]
  rw [exec_strb hoff (by rw [gpr_wx_ne _ _ (by decide), gpr_wx_ne _ _ (by decide), hs.x3]; exact hin)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', mem_wx,
    gpr_wx_ne _ _ (show Reg.x3 ≠ .x19 by decide), hs.x3, State.read, gpr_wx_self]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, lsr_toNat, BitVec.toNat_ofNat,
      show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, Size.bits]
    omega_arith
  · show (State.write _ _ _ _).gpr r = _
    rw [gpr_wx_ne _ _ (by simpa using hr), gpr_wx_ne _ _ (by simpa using hr)]

/-- `x` is not in `[b + d, b + d + n)` if its offset from `b` is outside. -/
theorem not_contains {b : Addr} {d n e : Nat} (h : e < d ∨ d + n ≤ e) (hd : d + n ≤ 2 ^ 64) (he : e < 2 ^ 64) :
    ¬ (⟨b + BitVec.ofNat 64 d, n⟩ : Region).Contains (b + BitVec.ofNat 64 e) 1 := by
  simp only [Region.Contains]
  intro hc
  have := (Offset.lt_iff (b + BitVec.ofNat 64 e) b hd).mp (by omega_arith)
  rw [Mem.sub_ofNat_toNat b he] at this
  omega_arith

theorem bitsN_ok {b : Addr} {i : Nat} (hi : i < 32) : ∀ n ≤ 8, ∀ s : State, Sc b s → s.gpr .x20 = 1 →
    WP isa (.block ((List.range n).flatMap fun j =>
      [.lsr .x .x19 .x17 j, .logic .and .x .x19 .x19 .x20, .strb .x19 .x3 (BITS + 8 * i + j)])) s fun s' =>
      (∀ j < n, s'.mem (b + BitVec.ofNat 64 (BITS + 8 * i + j)) =
        BitVec.ofNat 8 ((s.gpr .x17).toNat / 2 ^ j % 2)) ∧
      Frame [bitsR b i] s.mem s'.mem ∧ Kp [.x19] s s'
  | 0, _, s, _, _ => WP.block_nil ⟨fun j hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs, h20 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (bitsN_ok hi n (by omega_arith) s hs h20) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have h20₁ : s₁.gpr .x20 = 1 := by rw [k₁.gpr _ (by decide), h20]
    have h17₁ : s₁.gpr .x17 = s.gpr .x17 := k₁.gpr _ (by decide)
    refine WP.mono (bitStep_ok (hs.of_kp k₁ (by decide)) hi (j := n) (by omega_arith) h20₁) fun s₂ ⟨m₂, k₂⟩ =>
      ⟨fun j hj => ?_, ?_, (k₁.trans k₂).sub (by sub_regs)⟩
    · rw [m₂, write1_apply]
      by_cases hjn : j = n
      · subst hjn; rw [ite_eq_left rfl, h17₁]
      · rw [ite_eq_right (Offset.add_ofNat_ne b (by simp only [BITS, slot, NSLOT]; omega_arith)
          (by simp only [BITS, slot, NSLOT]; omega_arith) (by omega_arith))]
        exact e₁ j (by omega_arith)
    · rw [m₂]
      exact f₁.write (List.mem_singleton_self _) _ (Offset.contains b (by omega_arith) (by omega_arith)
        (by simp only [BITS, slot, NSLOT]; omega_arith))

theorem bitB_eq (kb : Byte) (j : Nat) : BitVec.ofNat 8 (kb.toNat / 2 ^ j % 2) = bitB kb j := by
  simp only [bitB, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem bitsOf_ok {b : Addr} {s : State} (hs : Sc b s) {i : Nat} (hi : i < 32) (h20 : s.gpr .x20 = 1)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 i) 1) :
    WP isa (.block (bitsOf i)) s fun s' =>
      (∀ j < 8, s'.mem (b + BitVec.ofNat 64 (BITS + 8 * i + j)) =
        bitB (s.mem (s.gpr .x1 + BitVec.ofNat 64 i)) j) ∧
      Frame [bitsR b i] s.mem s'.mem ∧ Kp [.x17, .x19] s s' := by
  rw [bitsOf]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrb (by omega_arith) hin, ?_⟩
  have hs₁ := sc_ww s ((s.mem.read (s.gpr .x1 + BitVec.ofNat 64 i) 1).setWidth 32) hs (show Reg.x17 ≠ .x3 by decide)
  refine WP.mono (bitsN_ok hi 8 (by decide) _ hs₁ (by rw [gpr_ww_ne _ _ (by decide), h20]))
    fun s' ⟨e, f, k⟩ => ⟨fun j hj => ?_, f, ((kp_ww _ _ _).trans k).sub (by sub_regs)⟩
  rw [e j hj, gpr_ww_self, read1_toNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (s.mem _).isLt (by decide)), bitB_eq]

/-- The region of the bits. -/
abbrev bitsArea (b : Addr) : Region := ⟨b + BitVec.ofNat 64 BITS, 256⟩

theorem bitsR_sub (b : Addr) {i : Nat} (hi : i < 32) : Region.Sub (bitsR b i) (bitsArea b) :=
  Offset.sub b (by omega_arith) (by omega_arith)

theorem bitsAll_ok {b sc : Addr} (hdisj : ∀ i < 32, ∀ r ∈ [bitsArea b], ¬ r.Contains (sc + BitVec.ofNat 64 i) 1) :
    ∀ n ≤ 32, ∀ s : State, Sc b s → s.gpr .x20 = 1 → s.gpr .x1 = sc →
    (∀ i < 32, InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 i) 1) →
    WP isa (.block ((List.range n).flatMap bitsOf)) s fun s' =>
      (∀ t < 8 * n, s'.mem (b + BitVec.ofNat 64 (BITS + t)) =
        bitB (s.mem (sc + BitVec.ofNat 64 (t / 8))) (t % 8)) ∧
      Frame [bitsArea b] s.mem s'.mem ∧ Kp [.x17, .x19] s s'
  | 0, _, s, _, _, _, _ => WP.block_nil ⟨fun t ht => absurd ht (by omega_arith), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs, h20, h1, hin => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (bitsAll_ok hdisj n (by omega_arith) s hs h20 h1 hin) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have h20₁ : s₁.gpr .x20 = 1 := by rw [k₁.gpr _ (by decide), h20]
    have h1₁ : s₁.gpr .x1 = sc := by rw [k₁.gpr _ (by decide), h1]
    refine WP.mono (bitsOf_ok (hs.of_kp k₁ (by decide)) (i := n) (by omega_arith) h20₁
      (by rw [h1₁, k₁.rd, k₁.wr]; exact hin n (by omega_arith))) fun s₂ ⟨e₂, f₂, k₂⟩ =>
      ⟨fun t ht => ?_, f₁.trans (f₂.sub fun r hr => ⟨bitsArea b, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact bitsR_sub b (by omega_arith)⟩),
        (k₁.trans k₂).sub (by sub_regs)⟩
    have hsc : s₁.mem (sc + BitVec.ofNat 64 n) = s.mem (sc + BitVec.ofNat 64 n) := f₁ _ (hdisj n (by omega_arith))
    by_cases htn : t < 8 * n
    · rw [f₂ _ (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact not_contains (by omega_arith) (by simp only [BITS, slot, NSLOT]; omega_arith)
          (by simp only [BITS, slot, NSLOT]; omega_arith))]
      exact e₁ t htn
    · have e := e₂ (t - 8 * n) (by omega_arith)
      rw [show BITS + 8 * n + (t - 8 * n) = BITS + t by omega_arith, h1₁, hsc] at e
      rw [e, show t / 8 = n by omega_arith, show t % 8 = t - 8 * n by omega_arith]

/-! ## The clamped bits -/

/-- The byte at `BITS + t`: bit `t` of the clamped scalar with the bytes `kb`. -/
def clampB (kb : Nat → Byte) (t : Nat) : Byte :=
  if t < 3 then 0 else if t = 254 then 1 else bitB (kb (t / 8)) (t % 8)

theorem bits_ok {b sc : Addr} {s : State} (hs : Sc b s) (h1 : s.gpr .x1 = sc)
    (hin : ∀ i < 32, InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 i) 1)
    (hdisj : ∀ i < 32, ∀ r ∈ [bitsArea b], ¬ r.Contains (sc + BitVec.ofNat 64 i) 1) :
    WP isa (.block Impl.X25519.AArch64.bits) s fun s' =>
      (∀ t < 256, s'.mem (b + BitVec.ofNat 64 (BITS + t)) = clampB (fun i => s.mem (sc + BitVec.ofNat 64 i)) t) ∧
      Frame [bitsArea b] s.mem s'.mem ∧ Kp [.x17, .x19, .x20] s s' := by
  simp only [Impl.X25519.AArch64.bits, List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_movz, ?_⟩
  have hs₁ := sc_wx s ((1 : BitVec 16).setWidth 64) hs (show Reg.x20 ≠ .x3 by decide)
  refine WP.block_append (WP.mono (bitsAll_ok hdisj 32 (by decide) _ hs₁ (gpr_wx_self _ _ _)
    (by rw [gpr_wx_ne _ _ (by decide), h1]) hin) fun s₂ ⟨e₂, f₂, k₂⟩ => ?_)
  have hs₂ := hs₁.of_kp k₂ (by decide)
  have h20 : s₂.gpr .x20 = 1 := by rw [k₂.gpr _ (by decide), gpr_wx_self]; rfl
  have c : ∀ t < 256, InRegions s₂.wr (s₂.gpr .x3 + BitVec.ofNat 64 (BITS + t)) 1 := fun t ht => by
    have h1 : BITS + t + 1 ≤ 4096 := by simp only [BITS, slot, NSLOT]; omega_arith
    have h2 : BITS + t < 2 ^ 64 := by simp only [BITS, slot, NSLOT]; omega_arith
    rw [hs₂.x3]
    exact ⟨scR b, hs₂.wr, Offset.contains_base b h1 h2⟩
  have ne : ∀ t < 256, ∀ u < 256, t ≠ u → b + BitVec.ofNat 64 (BITS + t) ≠ b + BitVec.ofNat 64 (BITS + u) :=
    fun t ht u hu h => Offset.add_ofNat_ne b (by simp only [BITS, slot, NSLOT]; omega_arith)
      (by simp only [BITS, slot, NSLOT]; omega_arith) (by omega_arith)
  have cb : ∀ t < 256, (bitsArea b).Contains (b + BitVec.ofNat 64 (BITS + t)) 1 := fun t ht =>
    Offset.contains b (by omega_arith) (by omega_arith) (by simp only [BITS, slot, NSLOT]; omega_arith)
  have hclamp : WP isa (.block [.movz .x .x19 0 0, .strb .x19 .x3 BITS, .strb .x19 .x3 (BITS + 1),
      .strb .x19 .x3 (BITS + 2), .strb .x20 .x3 (BITS + 254)]) s₂ fun s' =>
      s'.mem = (((s₂.mem.write (b + BitVec.ofNat 64 (BITS + 0)) 1 0).write (b + BitVec.ofNat 64 (BITS + 1)) 1 0).write
        (b + BitVec.ofNat 64 (BITS + 2)) 1 0).write (b + BitVec.ofNat 64 (BITS + 254)) 1 1 ∧ Kp [.x19] s₂ s' := by
    refine WP.block_cons_iff.mpr ⟨_, exec_movz, ?_⟩
    have hs₃ := sc_wx s₂ ((0 : BitVec 16).setWidth 64) hs₂ (show Reg.x19 ≠ .x3 by decide)
    have g19 : (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)).gpr .x19 = 0 := gpr_wx_self _ _ _
    have g20 : (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)).gpr .x20 = 1 := by
      rw [gpr_wx_ne _ _ (by decide), h20]
    have k3 : Kp [.x19] s₂ (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)) := kp_wx _ _ _
    have m3 : (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)).mem = s₂.mem := rfl
    generalize s₂.write .x .x19 ((0 : BitVec 16).setWidth 64) = s₃ at hs₃ g19 g20 k3 m3
    have hst : ∀ (r : Reg) (t : Nat) (s₄ : State), t < 256 → Sc b s₄ → ∀ (l : List Instr) (Q : State → Prop),
        WP isa (.block l) { s₄ with mem := s₄.mem.write (b + BitVec.ofNat 64 (BITS + t)) 1 ((s₄.read .w r).setWidth 8) }
          Q → WP isa (.block (.strb r .x3 (BITS + t) :: l)) s₄ Q := fun r t s₄ ht hs₄ l Q h => by
      have h1 : BITS + t + 1 ≤ 4096 := by simp only [BITS, slot, NSLOT]; omega_arith
      have h2 : BITS + t < 2 ^ 64 := by simp only [BITS, slot, NSLOT]; omega_arith
      have hin : InRegions s₄.wr (s₄.gpr .x3 + BitVec.ofNat 64 (BITS + t)) 1 := by
        rw [hs₄.x3]; exact ⟨scR b, hs₄.wr, Offset.contains_base b h1 h2⟩
      refine WP.block_cons_iff.mpr ⟨_, exec_strb (by omega_arith) hin, ?_⟩
      rw [hs₄.x3]
      exact h
    refine hst .x19 0 s₃ (by decide) hs₃ _ _ ?_
    refine hst .x19 1 _ (by decide) (hs₃.mem _) _ _ ?_
    refine hst .x19 2 _ (by decide) ((hs₃.mem _).mem _) _ _ ?_
    refine hst .x20 254 _ (by decide) (((hs₃.mem _).mem _).mem _) _ _ (WP.block_nil ⟨?_, ⟨k3.gpr, k3.rd, k3.wr⟩⟩)
    simp only [State.read, g19, g20, m3]
    rfl
  refine WP.mono hclamp fun s' ⟨m', k'⟩ => ⟨fun t ht => ?_, ?_, ((kp_wx s _ _).trans (k₂.trans k')).sub
    (by sub_regs)⟩
  · have e := e₂ t (by omega_arith)
    simp only [mem_wx] at e
    rw [m', write1_apply, write1_apply, write1_apply, write1_apply]
    simp only [clampB]
    by_cases h254 : t = 254
    · subst h254; rw [ite_eq_left rfl, ite_eq_right (by decide), ite_eq_left rfl]
    rw [ite_eq_right (ne t ht 254 (by decide) h254), ite_eq_right h254]
    by_cases h2 : t = 2
    · subst h2; rw [ite_eq_left rfl, ite_eq_left (by decide)]
    rw [ite_eq_right (ne t ht 2 (by decide) h2)]
    by_cases h1 : t = 1
    · subst h1; rw [ite_eq_left rfl, ite_eq_left (by decide)]
    rw [ite_eq_right (ne t ht 1 (by decide) h1)]
    by_cases h0 : t = 0
    · subst h0; rw [ite_eq_left rfl, ite_eq_left (by decide)]
    rw [ite_eq_right (ne t ht 0 (by decide) h0), ite_eq_right (by omega_arith), e]
  · simp only [mem_wx] at f₂
    rw [m']
    exact (((f₂.write (List.mem_singleton_self _) _ (cb 0 (by decide))).write
      (List.mem_singleton_self _) _ (cb 1 (by decide))).write (List.mem_singleton_self _) _ (cb 2 (by decide))).write
      (List.mem_singleton_self _) _ (cb 254 (by decide))

end VG.Proof.X25519.AArch64
