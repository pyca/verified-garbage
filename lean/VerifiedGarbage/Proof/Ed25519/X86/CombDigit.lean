import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.Ed25519.X86.AccumulateStep
import VerifiedGarbage.Impl.Ed25519.X86.Comb

/-!
# The comb's digits, and their masks

From the scalar's bits (one per byte at byte 7168 of the workspace),
`combDigits` computes, for both digits of table `esi = j`, the mask of the
digit's sign and the masks of its nine magnitudes, all in the workspace:
`mask 1` (all ones) for the digit's sign if its nibble is below 8 and for its
magnitude `|n - 8|`, `mask 0` otherwise.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519
open VG.Impl.X25519.X86 (sc at_)

/-- Only the masks (bytes 1024–1159 of the workspace) and registers other than `esi`, `edi`
and `esp` change. -/
structure DigitKeep (x : BitVec 32) (s t : State) : Prop where
  keep : Keep s t
  frame : Frame [sub x 1024 136] s.mem t.mem

theorem DigitKeep.trans {x : BitVec 32} {s t u : State} (h : DigitKeep x s t) (k : DigitKeep x t u) :
    DigitKeep x s u := ⟨h.keep.trans k.keep, h.frame.trans k.frame⟩

theorem wp_xori {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _))

/-- `and d, [b + o]` -/
theorem wp_andm {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Wp.Upd s s' d (s.gpr d &&& s.mem.readW (addr B o) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.mem ⟨b, o⟩) :: is)) s Q :=
  Wp.cons (by simp [exec, execAlu, Wp.readSrc_mem hb hin]; rfl) (k _ (Wp.Upd.flags _ _ _ _ _ _))

/-! ## The address of the bits -/

theorem combBits_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {j : Nat}
    (hs : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block combBits) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 (8 * j) := by
  refine Wp.wp_mov fun s₁ h₁ => Wp.wp_add fun s₂ h₂ _ => Wp.wp_add fun s₃ h₃ _ =>
    Wp.wp_add fun s₄ h₄ _ => Wp.wp_add fun s₅ h₅ _ => WP.block_nil ?_
  refine ⟨(updKeep h₁).trans ((updKeep h₂).trans ((updKeep h₃).trans ((updKeep h₄).trans (updKeep h₅)))),
    by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  have e₄ : s₄.gpr .edx = BitVec.ofNat 32 (8 * j) := by
    rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, hs, ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 32) (by omega)
  have i₄ : s₄.gpr .edi = x := by
    rw [h₄.other .edi (by decide), h₃.other .edi (by decide), h₂.other .edi (by decide),
      h₁.other .edi (by decide), hc.edi]
  rw [h₅.gpr, e₄, i₄, BitVec.add_comm]

/-! ## The nibble -/

private theorem byte_word : ∀ v < 2, (BitVec.ofNat 8 v).setWidth 32 = BitVec.ofNat 32 v := by decide

private theorem horner (a b : Nat) :
    BitVec.ofNat 32 a + BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a * 2 + b) := by
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]; exact congrArg (BitVec.ofNat 32) (by omega)

theorem combNibble_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {S j o i : Nat} (hj : j < 32)
    (ho : o = 7168 ∨ o = 7172) (hi : 8 * j + o = 7168 + 4 * i)
    (hd : s.gpr .edx = x + BitVec.ofNat 32 (8 * j))
    (hb : ∀ q < 256, s.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block (combNibble o)) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = s.gpr .edx ∧ t.gpr .eax = BitVec.ofNat 32 (nib S i) := by
  have hbit : ∀ t < 4, s.mem (addr (s.gpr .edx) (o + t)) = BitVec.ofNat 8 ((S / 2 ^ (4 * i + t)) % 2) :=
    fun t ht => by
      rw [hd, addr_plus, show 8 * j + (o + t) = 7168 + (4 * i + t) by omega]
      exact hb _ (by omega)
  have hin : ∀ t < 4, InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) (o + t)) 1 := fun t ht => by
    rw [hd, addr_plus]; exact hc.inRW (by omega) (by decide)
  have lt2 : ∀ t, (S / 2 ^ (4 * i + t)) % 2 < 2 := fun t => Nat.mod_lt _ (by decide)
  refine scalar_ld8 rfl (hin 3 (by decide)) fun s₁ h₁ => Wp.wp_add fun s₂ h₂ _ => ?_
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have d₂ : s₂.gpr .edx = s.gpr .edx := by rw [h₂.other .edx (by decide), h₁.other .edx (by decide)]
  refine scalar_ld8 (by rw [d₂]) (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hin 2 (by decide))
    fun s₃ h₃ => Wp.wp_add fun s₄ h₄ _ => Wp.wp_add fun s₅ h₅ _ => ?_
  have m₅ : s₅.mem = s.mem := by rw [h₅.mem, h₄.mem, h₃.mem, m₂]
  have d₅ : s₅.gpr .edx = s.gpr .edx := by
    rw [h₅.other .edx (by decide), h₄.other .edx (by decide), h₃.other .edx (by decide), d₂]
  have r₅ : s₅.rd ++ s₅.wr = s.rd ++ s.wr := by
    rw [h₅.rd, h₅.wr, h₄.rd, h₄.wr, h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  refine scalar_ld8 (by rw [d₅]) (by rw [r₅]; exact hin 1 (by decide))
    fun s₆ h₆ => Wp.wp_add fun s₇ h₇ _ => Wp.wp_add fun s₈ h₈ _ => ?_
  have m₈ : s₈.mem = s.mem := by rw [h₈.mem, h₇.mem, h₆.mem, m₅]
  have d₈ : s₈.gpr .edx = s.gpr .edx := by
    rw [h₈.other .edx (by decide), h₇.other .edx (by decide), h₆.other .edx (by decide), d₅]
  have r₈ : s₈.rd ++ s₈.wr = s.rd ++ s.wr := by rw [h₈.rd, h₈.wr, h₇.rd, h₇.wr, h₆.rd, h₆.wr, r₅]
  have hin0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) o) 1 := by
    have h0 := hin 0 (by decide); rwa [Nat.add_zero] at h0
  have hbit0 : s.mem (addr (s.gpr .edx) o) = BitVec.ofNat 8 ((S / 2 ^ (4 * i)) % 2) := by
    have h0 := hbit 0 (by decide); rwa [Nat.add_zero, Nat.add_zero] at h0
  refine scalar_ld8 (by rw [d₈]) (by rw [r₈]; exact hin0)
    fun s₉ h₉ => Wp.wp_add fun s₁₀ h₁₀ _ => WP.block_nil ?_
  refine ⟨(updKeep h₁).trans ((updKeep h₂).trans ((updKeep h₃).trans ((updKeep h₄).trans
    ((updKeep h₅).trans ((updKeep h₆).trans ((updKeep h₇).trans ((updKeep h₈).trans
    ((updKeep h₉).trans (updKeep h₁₀))))))))), by rw [h₁₀.mem, h₉.mem, m₈], ?_, ?_⟩
  · rw [h₁₀.other .edx (by decide), h₉.other .edx (by decide), d₈]
  · have v₂ : s₂.gpr .eax = BitVec.ofNat 32 ((S / 2 ^ (4 * i + 3)) % 2 * 2) := by
      rw [h₂.gpr, h₁.gpr, hbit 3 (by decide), byte_word _ (lt2 3), ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 32) (by omega)
    have v₄ : s₄.gpr .eax = BitVec.ofNat 32 ((S / 2 ^ (4 * i + 3)) % 2 * 2 + (S / 2 ^ (4 * i + 2)) % 2) := by
      rw [h₄.gpr, h₃.gpr, h₃.other .eax (by decide), v₂, m₂, hbit 2 (by decide),
        byte_word _ (lt2 2), ← BitVec.ofNat_add]
    have v₇ : s₇.gpr .eax = BitVec.ofNat 32 (((S / 2 ^ (4 * i + 3)) % 2 * 2 + (S / 2 ^ (4 * i + 2)) % 2) * 2 +
        (S / 2 ^ (4 * i + 1)) % 2) := by
      rw [h₇.gpr, h₆.gpr, h₆.other .eax (by decide), h₅.gpr, v₄, m₅, hbit 1 (by decide),
        byte_word _ (lt2 1), horner]
    rw [h₁₀.gpr, h₉.gpr, h₉.other .eax (by decide), h₈.gpr, v₇, m₈, hbit0,
      byte_word _ (by have := lt2 0; rwa [Nat.add_zero] at this), horner, nib_bits]

/-! ## The sign and the magnitude -/

private theorem sign_fact : ∀ n < 16,
    (if decide ((BitVec.ofNat 32 n).toNat < (8 : BitVec 32).toNat) then BitVec.allOnes 32 else 0) =
      mask (decide (n < 8)).toNat ∧
    (BitVec.ofNat 32 n - 8 ^^^ (if decide ((BitVec.ofNat 32 n).toNat < (8 : BitVec 32).toNat) then
      BitVec.allOnes 32 else 0)) - (if decide ((BitVec.ofNat 32 n).toNat < (8 : BitVec 32).toNat) then
      BitVec.allOnes 32 else 0) = BitVec.ofNat 32 (mag n) := by
  decide

theorem combSign_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {sign n : Nat} (hsign : sign + 4 ≤ 8192)
    (hn : n < 16) (ha : s.gpr .eax = BitVec.ofNat 32 n) :
    WP isa (.block (combSign sign)) s fun t =>
      Keep s t ∧ Frame [sub x sign 4] s.mem t.mem ∧ wd t.mem x sign = mask (decide (n < 8)).toNat ∧
      t.gpr .eax = BitVec.ofNat 32 (mag n) ∧ t.gpr .edx = s.gpr .edx := by
  refine Wp.wp_subi fun s₁ h₁ c₁ _ => Wp.wp_sbb_self c₁ fun s₂ h₂ => ?_
  have k₂ : Keep s s₂ := (updKeep h₁).trans (updKeep h₂)
  refine Wp.wp_stm (k₂.ctx hc).edi ((k₂.ctx hc).inW hsign (by decide)) fun s₃ h₃ => ?_
  refine Wp.wp_xor fun s₄ h₄ => Wp.wp_sub fun s₅ h₅ _ => WP.block_nil ?_
  obtain ⟨f₁, f₂⟩ := sign_fact n hn
  rw [ha] at h₁ h₂
  have k₃ : Keep s₂ s₃ := ⟨by rw [h₃.gpr], by rw [h₃.gpr], by rw [h₃.gpr], h₃.rd, h₃.wr⟩
  refine ⟨k₂.trans (k₃.trans ((updKeep h₄).trans (updKeep h₅))), ?_, ?_, ?_, ?_⟩
  · rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    exact frame_write1 (Frame.refl _ _) hc.fit hsign (Nat.le_refl _) (Nat.le_refl _) _
  · rw [h₅.mem, h₄.mem, h₃.mem, wd_write_self, h₂.gpr, ← f₁]
  · rw [h₅.gpr, h₄.gpr, h₄.other .ecx (by decide), h₃.gpr, h₂.gpr, h₂.other .eax (by decide), h₁.gpr]
    exact f₂
  · rw [h₅.other .edx (by decide), h₄.other .edx (by decide), h₃.gpr, h₂.other .edx (by decide),
      h₁.other .edx (by decide)]


/-! ## The masks of the magnitudes -/

private theorem mask_fact : ∀ a < 9, ∀ k < 9,
    (if decide ((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 k).toNat < (1 : BitVec 32).toNat) then
      BitVec.allOnes 32 else 0) = mask (decide (a = k)).toNat := by
  decide

theorem combMask_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {masks a : Nat} (k : Nat)
    (hm : masks + 36 ≤ 8192) (ha : a < 9) (hk : k < 9) (hax : s.gpr .eax = BitVec.ofNat 32 a) :
    WP isa (.block (combMask masks k)) s fun t =>
      Keep s t ∧ t.gpr .eax = s.gpr .eax ∧ t.gpr .edx = s.gpr .edx ∧
      Frame [sub x (masks + 4 * k) 4] s.mem t.mem ∧
      wd t.mem x (masks + 4 * k) = mask (decide (a = k)).toNat := by
  refine Wp.wp_mov fun s₁ h₁ => wp_xori fun s₂ h₂ => Wp.wp_subi fun s₃ h₃ c₃ _ =>
    Wp.wp_sbb_self c₃ fun s₄ h₄ => ?_
  have k₄ : Keep s s₄ := (updKeep h₁).trans ((updKeep h₂).trans ((updKeep h₃).trans (updKeep h₄)))
  have hw : masks + 4 * k + 4 ≤ 8192 := by omega
  refine Wp.wp_stm (k₄.ctx hc).edi ((k₄.ctx hc).inW hw (by decide)) fun t ht => WP.block_nil ?_
  have e₃ : s₂.gpr .ecx = BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 k := by rw [h₂.gpr, h₁.gpr, hax]
  refine ⟨k₄.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, h₄.other .eax (by decide), h₃.other .eax (by decide), h₂.other .eax (by decide),
      h₁.other .eax (by decide)]
  · rw [ht.gpr, h₄.other .edx (by decide), h₃.other .edx (by decide), h₂.other .edx (by decide),
      h₁.other .edx (by decide)]
  · rw [ht.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    exact frame_write1 (Frame.refl _ _) hc.fit hw (Nat.le_refl _) (Nat.le_refl _) _
  · rw [ht.mem, wd_write_self, h₄.gpr, ← mask_fact a ha k hk, e₃]


theorem combMaskAll_ok {x : BitVec 32} {s₀ : State} (hc : Ctx x s₀) {masks a : Nat}
    (hm : masks + 36 ≤ 8192) (ha : a < 9) (hax : s₀.gpr .eax = BitVec.ofNat 32 a) : ∀ n ≤ 9,
    WP isa (.block ((List.range n).flatMap (combMask masks))) s₀ fun t =>
      Keep s₀ t ∧ t.gpr .eax = s₀.gpr .eax ∧ t.gpr .edx = s₀.gpr .edx ∧
      Frame [sub x masks (4 * n)] s₀.mem t.mem ∧
      ∀ k < n, wd t.mem x (masks + 4 * k) = mask (decide (a = k)).toNat
  | 0, _ => WP.block_nil ⟨Keep.refl _, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (combMaskAll_ok hc hm ha hax n (by omega))
      fun s₁ ⟨k₁, a₁, d₁, f₁, w₁⟩ => ?_)
    refine WP.mono (combMask_ok (k₁.ctx hc) n hm ha (by omega) (a₁.trans hax))
      fun t ⟨kt, at', dt, ft, wt⟩ => ?_
    refine ⟨k₁.trans kt, at'.trans a₁, dt.trans d₁, ?_, fun k hk => ?_⟩
    · exact (frameWiden f₁ hc.fit (Nat.le_refl _) (by omega) (by omega)).trans
        (frameWiden ft hc.fit (by omega) (by omega) (by omega))
    · by_cases e : k = n
      · subst e; exact wt
      · rw [wd_frame1 ft hc.fit (by omega) (by omega) (by omega)]; exact w₁ k (by omega)

/-- A byte of the scalar's bits, outside the masks. -/
theorem digit_bit {x : BitVec 32} {m m' : Mem} (hf : Frame [sub x 1024 136] m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) {q : Nat} (hq : q < 512) :
    m' (addr x (7168 + q)) = m (addr x (7168 + q)) := by
  apply hf
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (sub_disj (by omega_using [hx, hq]) (by omega_using [hx])
    (Or.inr (by omega)) : (sub x (7168 + q) 1).Disjoint (sub x 1024 136)) _ (Region.contains_self _ _)

/-- Both digits' masks, of table `j`. -/
structure DigitMasks (x : BitVec 32) (S j : Nat) (m : Mem) : Prop where
  oddMask : ∀ k < 9, wd m x (combOddMasks + 4 * k) = mask (decide (mag (nib S (2 * j + 1)) = k)).toNat
  evenMask : ∀ k < 9, wd m x (combEvenMasks + 4 * k) = mask (decide (mag (nib S (2 * j)) = k)).toNat
  oddSign : wd m x combOddSign = mask (decide (nib S (2 * j + 1) < 8)).toNat
  evenSign : wd m x combEvenSign = mask (decide (nib S (2 * j) < 8)).toNat

theorem combDigits_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {S j : Nat} (hj : j < 32)
    (hs : s.gpr .esi = BitVec.ofNat 32 j)
    (hb : ∀ q < 256, s.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block combDigits) s fun t => DigitKeep x s t ∧ DigitMasks x S j t.mem := by
  have hfit := hc.fit
  simp only [combDigits, List.append_assoc]
  refine WP.block_append (WP.mono (combBits_ok hc hs) fun s₁ ⟨k₁, m₁, d₁⟩ => ?_)
  have c₁ := k₁.ctx hc
  refine WP.block_append (WP.mono (combNibble_ok c₁ (S := S) (i := 2 * j + 1) hj (Or.inr rfl)
    (by omega) d₁ (fun q hq => by rw [m₁]; exact hb q hq)) fun s₂ ⟨k₂, m₂, d₂, a₂⟩ => ?_)
  have c₂ := k₂.ctx c₁
  refine WP.block_append (WP.mono (combSign_ok c₂ (by decide) (nib_lt S _) a₂)
    fun s₃ ⟨k₃, f₃, w₃, a₃, d₃⟩ => ?_)
  have c₃ := k₃.ctx c₂
  refine WP.block_append (WP.mono (combMaskAll_ok c₃ (by decide) (mag_lt (nib_lt S _)) a₃ 9 (le_refl _))
    fun s₄ ⟨k₄, _, d₄, f₄, w₄⟩ => ?_)
  have c₄ := k₄.ctx c₃
  have f₁₄ : Frame [sub x 1024 136] s.mem s₄.mem := by
    rw [← m₁, ← m₂]
    exact (frameWiden f₃ hfit (by decide) (by decide) (by decide)).trans
      (frameWiden f₄ hfit (by decide) (by decide) (by decide))
  refine WP.block_append (WP.mono (combNibble_ok c₄ (S := S) (i := 2 * j) hj (Or.inl rfl)
    (by omega) (by rw [d₄, d₃, d₂, d₁]) (fun q hq => by rw [digit_bit f₁₄ hfit (by omega)]; exact hb q hq))
    fun s₅ ⟨k₅, m₅, _, a₅⟩ => ?_)
  have c₅ := k₅.ctx c₄
  refine WP.block_append (WP.mono (combSign_ok c₅ (by decide) (nib_lt S _) a₅)
    fun s₆ ⟨k₆, f₆, w₆, a₆, _⟩ => ?_)
  have c₆ := k₆.ctx c₅
  refine WP.mono (combMaskAll_ok c₆ (by decide) (mag_lt (nib_lt S _)) a₆ 9 (le_refl _))
    fun t ⟨kt, _, _, ft, wt⟩ => ?_
  have f₅t : Frame [sub x 1024 136] s₄.mem t.mem := by
    rw [← m₅]
    exact (frameWiden f₆ hfit (by decide) (by decide) (by decide)).trans
      (frameWiden ft hfit (by decide) (by decide) (by decide))
  refine ⟨⟨k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans (k₆.trans kt))))), f₁₄.trans f₅t⟩,
    ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩⟩
  · rw [wd_frame1 ft hfit (by decide) (by simp only [combOddMasks]; omega)
      (by simp only [combOddMasks, combEvenMasks]; omega),
      wd_frame1 f₆ hfit (by decide) (by simp only [combOddMasks]; omega)
      (by simp only [combOddMasks, combEvenSign]; omega), m₅]
    exact w₄ k hk
  · exact wt k hk
  · rw [wd_frame1 ft hfit (by decide) (by decide) (by decide), wd_frame1 f₆ hfit (by decide) (by decide)
      (by decide), m₅, wd_frame1 f₄ hfit (by decide) (by decide) (by decide)]
    exact w₃
  · rw [wd_frame1 ft hfit (by decide) (by decide) (by decide)]
    exact w₆

end VG.Proof.Ed25519.X86
