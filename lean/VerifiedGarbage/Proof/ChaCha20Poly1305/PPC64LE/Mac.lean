module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Prologue
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp

/-!
# ChaCha20-Poly1305 on PPC64LE: absorbing padded data

`macPad p n` absorbs the `n` bytes at `p` into the Poly1305 state (at `ctx`),
and zeros to a multiple of 16: `msg ++ x ++ pad16 x`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Impl.ChaCha20.PPC64LE.Xor (mov)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20Poly1305 (pad16)

variable {e : Bool}

theorem padOff_eq : padOff = 416 := rfl

/-! ## Numbers -/

theorem toNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_beq_zero {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h0; rw [← toNat64 h, h0]; rfl
  · intro hx; subst hx; rfl

theorem ofNat_bne_zero {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x != 0) = decide (x ≠ 0) := by
  rw [bne, ofNat_beq_zero h]; by_cases hx : x = 0 <;> simp [hx]

theorem ofNat_shr {x : Nat} (h : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 4 = BitVec.ofNat 64 (x / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat64 h, toNat64 (by omega), Nat.shiftRight_eq_div_pow]

theorem off_toNat (p : Addr) {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-! ## What `macPad` keeps -/

/-- The Poly1305 state, the padded block, and `vg_poly1305_blocks`'s frame. -/
abbrev macR (s₀ : State) : List Region := [sub s₀ 0 128, sub s₀ padOff 16, belR s₀]

theorem kept_mac0 {s₀ s s' : State} (hk : Kept [] s s') : Kept (macR s₀) s s' :=
  hk.sub fun _ hr => absurd hr List.not_mem_nil

theorem kept_macP {s₀ s s' : State} (hk : Kept [sub s₀ padOff 16] s s') : Kept (macR s₀) s s' :=
  hk.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

theorem kept_macB {s₀ s s' : State} (hk : Kept [sub s₀ 0 128, belR s₀] s s') : Kept (macR s₀) s s' :=
  hk.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

theorem mac_inv {s₀ s s' : State} (hp : APre e s₀) (h : Inv s₀ s) (hk : Kept (macR s₀) s s') : Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩
      · exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩
      · exact ⟨belR s₀, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by decide) (by decide) (by decide)
      · exact sub_disj s₀ (by decide) (by decide) (by decide)
      · exact (hp.b_c.sub_right (sub_ctx s₀ (by decide))).symm)

/-! ## Absorbing whole blocks -/

/-- `n` blocks at `p` absorbed, from `r4 = p` and `r5 = n`. -/
theorem absorb_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) {p : Addr} {n : Nat}
    (h4 : s.gpr .r4 = p) (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (hn : 16 * n < 2 ^ 64)
    (hdj : (sub s₀ 0 128).Disjoint ⟨p, 16 * n⟩) (hbp : (belR s₀).Disjoint ⟨p, 16 * n⟩)
    (hfit : p.toNat + 16 * n ≤ 2 ^ 64) (hc : Covers [⟨p, 16 * n⟩] (s₀.rd ++ s₀.wr)) :
    WP isa absorb s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg → Repr s'.mem (cx s₀) key (msg ++ bytesAt s.mem p (16 * n)) := by
  unfold absorb
  refine WP.seq (wp_mov fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : Kept [] s s₁ :=
    ⟨fun r hr => u₁.other r (ne_of_pres hr), u₁.sp, u₁.rd, u₁.wr, by rw [u₁.mem]; exact Frame.refl _ _⟩
  have i₁ := h.step0 k₁
  have hsp : s₁.sp = s₀.sp := i₁.sp
  have hbP : (⟨s₁.sp - 160, 160⟩ : Region).Disjoint ⟨cx s₀, 128⟩ := by
    rw [hsp, ← sub_zero s₀ 128]; exact hp.b_c.sub_right (sub_ctx s₀ (by decide))
  have hP : (cx s₀).toNat + 128 ≤ 2 ^ 64 := by have := hp.fit_c; omega
  have cv : Covers ([(⟨p, 16 * n⟩ : Region)] ++ [⟨cx s₀, 128⟩]) (s₁.rd ++ s₁.wr) := by
    intro a w ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [i₁.rd, i₁.wr]; exact hc a w ⟨_, List.mem_singleton_self _, hcn⟩
    · rw [← sub_zero s₀ 128] at hcn
      exact covers_right (covers1 hp i₁.wr (a := 0) (n := 128) (by decide)) a w
        ⟨_, List.mem_singleton_self _, hcn⟩
  have cw : Covers [(⟨cx s₀, 128⟩ : Region)] s₁.wr := by
    rw [← sub_zero s₀ 128]; exact covers1 hp i₁.wr (by decide)
  refine blocks_call (P := cx s₀) (p := p) (n := n) (by rw [u₁.gpr, h.regs.r24])
    (by rw [u₁.other _ (by decide), h4]) (by rw [u₁.other _ (by decide), h5]) hn
    (by rw [hsp]; exact hp.sp160) (by rw [← sub_zero s₀ 128]; exact hdj) hbP (by rw [hsp]; exact hbp)
    hP hfit cv cw fun s₂ k₂ repr₂ => ?_
  rw [← sub_zero s₀ 128, hsp] at k₂
  have k₁₂ : Kept (macR s₀) s s₂ := (kept_mac0 k₁).trans (kept_macB k₂)
  exact ⟨mac_inv hp h k₁₂, k₁₂, fun key msg hr => by
    rw [← k₁.mem_eq]; exact repr₂ key msg (by rw [k₁.mem_eq]; exact hr)⟩

/-! ## Zeroing the padded block -/

theorem writeW64_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 64)) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split
  · simp
  · rfl

theorem padZ_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.li .r11 0, .store .d .r11 .r24 padOff, .store .d .r11 .r24 (padOff + 8),
      .addi .r6 .r24 padOff]) s fun s' =>
      s'.gpr .r6 = off (cx s₀) padOff ∧ (∀ r, r ≠ .r11 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ padOff 16] s.mem s'.mem ∧ ∀ j < 16, s'.mem (off (cx s₀) (padOff + j)) = 0 := by
  have h14 := h.regs.r24
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_std (a := off (cx s₀) padOff) (by decide) (by decide) (by rw [u₁.other _ (by decide), h14])
    (by rw [u₁.wr, h.wr]; exact hp.in_ctx (by decide)) fun s₂ g₂ => ?_
  refine wp_std (a := off (cx s₀) (padOff + 8)) (by decide) (by decide)
    (by rw [g₂.gpr, u₁.other _ (by decide), h14]) (by rw [g₂.wr, u₁.wr, h.wr]; exact hp.in_ctx (by decide))
    fun s₃ g₃ => ?_
  refine wp_addi (by decide) (by decide) fun s₄ u₄ => WP.block_nil ?_
  have x11 : s₁.gpr .r11 = 0 := u₁.gpr
  have hm : s₄.mem = (s.mem.writeW (off (cx s₀) padOff) (0 : BitVec 64)).writeW
      (off (cx s₀) (padOff + 8)) (0 : BitVec 64) := by
    rw [u₄.mem, g₃.mem, g₂.gpr, g₂.mem, u₁.mem, x11]
  refine ⟨by rw [u₄.gpr, g₃.gpr, g₂.gpr, u₁.other _ (by decide), h14], fun r h₁ h₂ => by
      rw [u₄.other _ h₂, g₃.gpr, g₂.gpr, u₁.other _ h₁],
    by rw [u₄.rd, g₃.rd, g₂.rd, u₁.rd], by rw [u₄.wr, g₃.wr, g₂.wr, u₁.wr],
    by rw [u₄.sp, g₃.sp, g₂.sp, u₁.sp], ?_, fun j hj => ?_⟩
  · rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega) (by omega) (by decide))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (w := 64 / 8) (by omega) (by omega) (by decide))
  · rw [hm, writeW64_zero_apply]
    by_cases hj8 : 8 ≤ j
    · rw [ite_eq_left (by rw [Offset.sub_toNat _ (by omega) (by rw [padOff_eq]; omega)]; omega)]
    · rw [ite_eq_right (by rw [Offset.sub_toNat' _ (by rw [padOff_eq]; omega) (by rw [padOff_eq]; omega)]; split <;> omega),
        writeW64_zero_apply,
        ite_eq_left (by rw [Offset.sub_toNat _ (by omega) (by rw [padOff_eq]; omega)]; omega)]

/-! ## Copying the last bytes -/

/-- Before byte `i` of the last `t` bytes at `Q` is copied into the padded
block, from the state `s₂` after the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : Addr) (t i : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = Q + BitVec.ofNat 64 i
  r6 : s.gpr .r6 = off (cx s₀) (padOff + i)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (t - i)
  keep : ∀ r ∈ preserved, s.gpr r = s₂.gpr r
  sp : s.sp = s₂.sp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ padOff 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (off (cx s₀) (padOff + j)) = if j < i then s₂.mem (Q + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.lbz .r11 .r4 0, .stb .r11 .r6 0, .addi .r4 .r4 1, .addi .r6 .r6 1, .subi .r12 .r12 1]

theorem copyLoop_eq : copyLoop = .loop (.block copyBody) (.nonzero .d .r12) := rfl

theorem byte_rt (b : Byte) : ((b.setWidth 64).setWidth 8 : Byte) = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem sub_toNat_lt_one (x a : Addr) : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : Addr).toNat = 0 from rfl]; omega)
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; exact BitVec.zero_add a
  · rintro rfl; simp

theorem writeW8_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    (m.writeW a v) x = if x = a then v else m x := by
  by_cases h : x = a
  · subst h; simp [Mem.writeW, Mem.write]
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, sub_toNat_lt_one, h, ite_false]

theorem sub_one {a : Nat} (h : 0 < a) : BitVec.ofNat 64 a - BitVec.ofNat 64 1 = BitVec.ofNat 64 (a - 1) :=
  Offset.ofNat_sub_ofNat h

theorem copy_step {s₀ : State} (hp : APre e s₀) {s₂ : State} {Q : Addr} {t : Nat} (ht : t < 16)
    (hwr : s₂.wr = s₀.wr)
    (hsrc : ∀ j < t, InRegions (s₂.rd ++ s₂.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ padOff 16))
    {i : Nat} (hi : i < t) {s : State} (h : CpInv s₀ s₂ Q t i s) :
    WP isa (.block copyBody) s fun s' => CpInv s₀ s₂ Q t (i + 1) s' := by
  have hin : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1 := by
    rw [h.rd, h.wr]; exact hsrc i hi
  have hout : InRegions s.wr (off (cx s₀) (padOff + i)) 1 := by
    rw [h.wr, hwr]; exact hp.in_ctx (by rw [padOff_eq]; omega)
  unfold copyBody
  refine wp_lbz (a := Q + BitVec.ofNat 64 i) (by decide) (by decide)
    (by rw [h.r4]; exact BitVec.add_zero _) hin fun s₁ u₁ => ?_
  refine wp_stb (a := off (cx s₀) (padOff + i)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), h.r6]; exact BitVec.add_zero _) (by rw [u₁.wr]; exact hout)
    fun s₂' g₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ =>
    wp_subi (by decide) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have hm : s₅.mem = s.mem.writeW (off (cx s₀) (padOff + i)) (s.mem (Q + BitVec.ofNat 64 i)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, byte_rt]
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r4,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r6,
      off_add, Nat.add_assoc]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r12,
      sub_one (by omega), Nat.sub_sub]
  · rw [u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr), u₃.other _ (ne_of_pres hr), g₂.gpr,
      u₁.other _ (ne_of_pres hr), h.keep r hr]
  · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
  · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 8 / 8) (by omega) (by omega) (by decide))
  · have hbyte : s.mem (Q + BitVec.ofNat 64 i) = s₂.mem (Q + BitVec.ofNat 64 i) :=
      h.frame _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdisj i hi _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
    rw [hm, writeW8_apply]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, show k < k + 1 by omega, hbyte]
    · rw [ite_eq_right (Offset.add_ofNat_ne (cx s₀) (by rw [padOff_eq]; omega) (by rw [padOff_eq]; omega)
        (by omega)), h.buf k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (off (cx s₀) (padOff + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (off (cx s₀) padOff) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [off_add, h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hk]

theorem padTail_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) {Q : Addr} {t : Nat}
    (ht0 : 0 < t) (ht : t < 16) (h4 : s.gpr .r4 = Q) (h12 : s.gpr .r12 = BitVec.ofNat 64 t)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ padOff 16)) :
    WP isa padTail s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg →
        Repr s'.mem (cx s₀) key (msg ++ (bytesAt s.mem Q t ++ List.replicate (16 - t) 0)) := by
  unfold padTail
  refine WP.seq (WP.mono (padZ_ok hp h) fun s₂ ⟨r6₂, g₂, rd₂, wr₂, sp₂, f₂, z₂⟩ => ?_)
  have src₂ : ∀ j < t, s₂.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) :=
    fun j hj => f₂ _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj j hj _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  have hk₂ : Kept [sub s₀ padOff 16] s s₂ :=
    ⟨fun r hr => g₂ r (ne_of_pres hr) (ne_of_pres hr), sp₂, rd₂, wr₂, f₂⟩
  have i₂ := h.step1 hk₂ (by decide) (by decide)
  refine WP.seq (WP.mono (Q := CpInv s₀ s₂ Q t t) ?_ fun s₃ h₃ => ?_)
  · rw [copyLoop_eq]
    let I : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q t i s
    have hstep : ∀ n s, I n s → WP isa (.block copyBody) s (fun s' =>
        (isa.eval (.nonzero .d .r12) s' = some false ∧ CpInv s₀ s₂ Q t t s') ∨
        (isa.eval (.nonzero .d .r12) s' = some true ∧ ∃ n' < n, I n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (copy_step hp ht (by rw [i₂.wr]) (by rw [rd₂, wr₂]; exact hsrc) hdisj hi hI)
        fun s' h' => ?_
      have hz : isa.eval (.nonzero .d .r12) s' = some (decide (t - (i + 1) ≠ 0)) := by
        rw [VG.Proof.Poly1305.PPC64LE.eval_nonzero, h'.r12, ofNat_bne_zero (by omega)]
      by_cases hl : i + 1 = t
      · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
      · exact .inr ⟨by rw [hz]; simp; omega, t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) I hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [g₂ _ (by decide) (by decide), h4]; exact (BitVec.add_zero _).symm,
      by rw [r6₂]; rfl, by rw [g₂ _ (by decide) (by decide), h12]; rfl, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  have hk₃ : Kept [sub s₀ padOff 16] s₂ s₃ := ⟨h₃.keep, h₃.sp, h₃.rd, h₃.wr, h₃.frame⟩
  have i₃ := i₂.step1 hk₃ (by decide) (by decide)
  refine WP.seq (wp_addi (by decide) (by decide) fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ => WP.block_nil ?_)
  have k₅ : Kept [] s₃ s₅ := ⟨fun r hr => by rw [u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr)],
    by rw [u₅.sp, u₄.sp], by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr], by rw [u₅.mem, u₄.mem]; exact Frame.refl _ _⟩
  have i₅ := i₃.step0 k₅
  have hdj : (sub s₀ 0 128).Disjoint ⟨off (cx s₀) padOff, 16 * 1⟩ :=
    sub_disj s₀ (by decide) (by decide) (by decide)
  have hbp : (belR s₀).Disjoint ⟨off (cx s₀) padOff, 16 * 1⟩ :=
    hp.b_c.sub_right (sub_ctx s₀ (by decide))
  have hfit : (off (cx s₀) padOff).toNat + 16 * 1 ≤ 2 ^ 64 := by
    have := hp.fit_c; rw [off_toNat _ (by rw [padOff_eq]; omega), padOff_eq]; omega
  have hc : Covers [(⟨off (cx s₀) padOff, 16 * 1⟩ : Region)] (s₀.rd ++ s₀.wr) :=
    covers_right (covers1 hp rfl (a := padOff) (n := 16 * 1) (by decide))
  refine WP.mono (absorb_ok hp i₅ (n := 1) (by rw [u₅.other _ (by decide), u₄.gpr, i₃.regs.r24])
    (by rw [u₅.gpr]) (by decide) hdj hbp hfit hc)
    fun s₆ ⟨i₆, k₆, repr₆⟩ => ⟨i₆, (kept_macP hk₂).trans ((kept_macP hk₃).trans
      ((kept_mac0 k₅).trans k₆)), fun key msg hr => ?_⟩
  have m₅ := k₅.mem_eq
  have hr₅ : Repr s₅.mem (cx s₀) key msg := by
    rw [m₅]
    refine Repr.frame (f₂.trans h₃.frame) (fun r hr => ?_) hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [← sub_zero s₀ 128]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have hb : bytesAt s₅.mem (off (cx s₀) padOff) (16 * 1) =
      bytesAt s.mem Q t ++ List.replicate (16 - t) 0 := by
    rw [m₅, show 16 * 1 = 16 from rfl, padded_bytes ht h₃.buf]
    exact congrArg (· ++ _) (bytesAt_eq_of fun j hj => src₂ j hj)
  have := repr₆ key msg hr₅
  rwa [hb] at this

/-! ## The whole of `macPad` -/

/-- The registers `macPad` may take its arguments in. -/
def MacRegs (p n : Reg) : Prop := (p = .r25 ∧ n = .r26) ∨ (p = .r27 ∧ n = .r28)

/-- Neither is written by `macPad`'s own instructions, and both are callee-saved. -/
structure RegOk (r : Reg) : Prop where
  pres : r ∈ preserved
  r0 : r ≠ .r0
  r4 : r ≠ .r4
  r5 : r ≠ .r5
  r12 : r ≠ .r12

theorem MacRegs.p_ok {p n : Reg} (hr : MacRegs p n) : RegOk p := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem MacRegs.n_ok {p n : Reg} (hr : MacRegs p n) : RegOk n := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- What `macPad` needs of the bytes it absorbs. -/
structure Src (s₀ : State) (P : Addr) (len : Nat) : Prop where
  lt : len < 2 ^ 64
  fit : P.toNat + len ≤ 2 ^ 64
  ctx : (ctxR s₀).Disjoint ⟨P, len⟩
  bel : (belR s₀).Disjoint ⟨P, len⟩
  cov : Covers [⟨P, len⟩] (s₀.rd ++ s₀.wr)

theorem self_contains (a : Addr) : (⟨a, 1⟩ : Region).Contains a 1 := by
  simp only [Region.Contains]; rw [BitVec.sub_self]; simp

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, absorbed. -/
theorem macPad_ok {s₀ : State} (hp : APre e s₀) {p n : Reg} (hr : MacRegs p n) {P : Addr} {len : Nat}
    (hs : Src s₀ P len) {s : State} (h : Inv s₀ s) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len) :
    WP isa (macPad p n) s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg →
        Repr s'.mem (cx s₀) key (msg ++ (bytesAt s.mem P len ++ pad16 (bytesAt s.mem P len))) := by
  have hpn := hr.p_ok
  have hnn := hr.n_ok
  have hlt := hs.lt
  have hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  unfold macPad
  refine WP.seq (wp_mov (hn := hpn.r0) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have k₂ : Kept [] s s₂ := ⟨fun r hr => by rw [u₂.other _ (ne_of_pres hr), u₁.other _ (ne_of_pres hr)],
    by rw [u₂.sp, u₁.sp], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩
  have i₂ := h.step0 k₂
  have hdj : (sub s₀ 0 128).Disjoint ⟨P, 16 * (len / 16)⟩ :=
    (hs.ctx.sub_left (sub_ctx s₀ (by decide))).sub_right (Region.sub_prefix hk)
  refine WP.seq (WP.mono (absorb_ok hp i₂ (p := P) (n := len / 16) (by rw [u₂.other _ (by decide), u₁.gpr, hP])
    (by rw [u₂.gpr, u₁.other _ hnn.r4, hn, ofNat_shr hlt]) (by omega) hdj
    (hs.bel.sub_right (Region.sub_prefix hk)) (by have := hs.fit; omega)
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩))
    fun s₃ ⟨i₃, k₃, repr₃⟩ => ?_)
  have m₂ := k₂.mem_eq
  rw [m₂] at repr₃
  have n₃ : s₃.gpr n = BitVec.ofNat 64 len := by rw [k₃.cs n hnn.pres, k₂.cs n hnn.pres, hn]
  have p₃ : s₃.gpr p = P := by rw [k₃.cs p hpn.pres, k₂.cs p hpn.pres, hP]
  refine WP.seq (wp_li (by decide) fun s₄ u₄ => wp_and fun s₅ u₅ => WP.block_nil ?_)
  have r12₅ : s₅.gpr .r12 = BitVec.ofNat 64 (len % 16) := by
    rw [u₅.gpr, u₄.other _ hnn.r12, u₄.gpr, n₃, VG.Proof.Poly1305.PPC64LE.and15, toNat64 hlt]
  have k₅ : Kept [] s₃ s₅ := ⟨fun r hr => by rw [u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr)],
    by rw [u₅.sp, u₄.sp], by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr], by rw [u₅.mem, u₄.mem]; exact Frame.refl _ _⟩
  have i₅ := i₃.step0 k₅
  have k₁₅ : Kept (macR s₀) s s₅ := (kept_mac0 k₂).trans (k₃.trans (kept_mac0 k₅))
  have x_eq : bytesAt s.mem P len = bytesAt s.mem P (16 * (len / 16)) ++
      bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  have hlen : (bytesAt s.mem P len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  have m₅ := k₅.mem_eq
  refine WP.ite (decide (len % 16 = 0)) (by
      rw [VG.Proof.Poly1305.PPC64LE.eval_zero, r12₅, ofNat_beq_zero (by omega)]) (fun hb => ?_) (fun hb => ?_)
  · -- A multiple of 16: nothing to pad.
    have h0 : len % 16 = 0 := by simpa using hb
    refine WP.block_nil ⟨i₅, k₁₅, fun key msg hr => ?_⟩
    rw [m₅]
    have := repr₃ key msg hr
    rwa [show pad16 (bytesAt s.mem P len) = [] by simp [pad16, hlen, h0], List.append_nil,
      ← show 16 * (len / 16) = len by omega]
  · have h0 : len % 16 ≠ 0 := by simpa using hb
    refine WP.seq (wp_sub fun s₆ u₆ => wp_add fun s₇ u₇ => WP.block_nil ?_)
    have k₇ : Kept [] s₅ s₇ := ⟨fun r hr => by rw [u₇.other _ (ne_of_pres hr), u₆.other _ (ne_of_pres hr)],
      by rw [u₇.sp, u₆.sp], by rw [u₇.rd, u₆.rd], by rw [u₇.wr, u₆.wr], by rw [u₇.mem, u₆.mem]; exact Frame.refl _ _⟩
    have i₇ := i₅.step0 k₇
    have hQ : s₇.gpr .r4 = P + BitVec.ofNat 64 (16 * (len / 16)) := by
      rw [u₇.gpr, u₆.other _ hpn.r4, u₆.gpr, u₅.other _ hpn.r12, u₄.other _ hpn.r12, p₃,
        u₅.other _ hnn.r12, u₄.other _ hnn.r12, n₃, r12₅, Offset.ofNat_sub_ofNat (Nat.mod_le _ _),
        show len - len % 16 = 16 * (len / 16) by omega]
    have hsrc : ∀ j < len % 16, InRegions (s₇.rd ++ s₇.wr)
        (P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [i₇.rd, i₇.wr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hs.cov _ _ ⟨_, List.mem_singleton_self _,
        Offset.contains_base P (d := 16 * (len / 16) + j) (n := 1) (by omega) (by omega)⟩
    have hdj' : ∀ j < len % 16, (⟨P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j, 1⟩ :
        Region).Disjoint (sub s₀ padOff 16) := fun j hj => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ((hs.ctx.sub_left (sub_ctx s₀ (by decide))).sub_right
        (Offset.sub_base P (d := 16 * (len / 16) + j) (n := 1) (by omega))).symm
    refine WP.mono (padTail_ok hp i₇ (Q := P + BitVec.ofNat 64 (16 * (len / 16))) (t := len % 16)
      (by omega) (by omega) hQ (by rw [u₇.other _ (by decide), u₆.other _ (by decide), r12₅]) hsrc hdj')
      fun s₈ ⟨i₈, k₈, repr₈⟩ => ?_
    refine ⟨i₈, k₁₅.trans ((kept_mac0 k₇).trans k₈), fun key msg hr => ?_⟩
    have m₇ := k₇.mem_eq
    have := repr₈ key _ (by rw [m₇, m₅]; exact repr₃ key msg hr)
    rw [m₇, m₅, bytesAt_frame k₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ((hs.ctx.sub_left (sub_ctx s₀ (by decide))).sub_right
            (Offset.sub_base P (d := 16 * (len / 16)) (by omega))).symm
        · exact ((hs.ctx.sub_left (sub_ctx s₀ (by decide))).sub_right
            (Offset.sub_base P (d := 16 * (len / 16)) (by omega))).symm
        · exact (hs.bel.sub_right (Offset.sub_base P (d := 16 * (len / 16)) (by omega))).symm) (by omega),
      m₂] at this
    rw [show pad16 (bytesAt s.mem P len) = List.replicate (16 - len % 16) 0 by
      simp [pad16, hlen, h0], x_eq]
    simpa only [List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.PPC64LE
