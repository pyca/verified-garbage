import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.Ed25519.X86.MulAddVerified
import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Impl.Ed25519.X86.PointDecode
import VerifiedGarbage.Impl.Ed25519.X86.Recover
import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.PointMul
import VerifiedGarbage.Impl.Ed25519.X86.PointEncode
import VerifiedGarbage.Impl.Ed25519.X86.Field
import VerifiedGarbage.Impl.Ed25519.X86.Power
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Proof.Ed25519.Group.Double

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CombDigit`. -/
section

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
  keep : VG.Proof.X25519.X86.Keep s t
  frame : Frame [VG.Proof.X25519.X86.sub x 1024 136] s.mem t.mem

theorem DigitKeep.trans {x : BitVec 32} {s t u : State} (h : DigitKeep x s t) (k : DigitKeep x t u) :
    DigitKeep x s u := ⟨h.keep.trans k.keep, h.frame.trans k.frame⟩

theorem wp_xori {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _))

/-- `and d, [b + o]` -/
theorem wp_andm {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (VG.X86.addr B o) 4)
    (k : ∀ s', Wp.Upd s s' d (s.gpr d &&& s.mem.readW (VG.X86.addr B o) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.mem ⟨b, o⟩) :: is)) s Q :=
  Wp.cons (by simp [exec, execAlu, Wp.readSrc_mem hb hin]; rfl) (k _ (Wp.Upd.flags _ _ _ _ _ _))

/-! ## The address of the bits -/

theorem combBits_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {j : Nat}
    (hs : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block combBits) s fun t =>
      VG.Proof.X25519.X86.Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 (8 * j) := by
  refine Wp.wp_mov fun s₁ h₁ => Wp.wp_add fun s₂ h₂ _ => Wp.wp_add fun s₃ h₃ _ =>
    Wp.wp_add fun s₄ h₄ _ => Wp.wp_add fun s₅ h₅ _ => WP.block_nil ?_
  refine ⟨(VG.Proof.X25519.X86.updKeep h₁).trans ((VG.Proof.X25519.X86.updKeep h₂).trans ((VG.Proof.X25519.X86.updKeep h₃).trans ((VG.Proof.X25519.X86.updKeep h₄).trans (VG.Proof.X25519.X86.updKeep h₅)))),
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

theorem combNibble_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {S j o i : Nat} (hj : j < 32)
    (ho : o = 7168 ∨ o = 7172) (hi : 8 * j + o = 7168 + 4 * i)
    (hd : s.gpr .edx = x + BitVec.ofNat 32 (8 * j))
    (hb : ∀ q < 256, s.mem (VG.X86.addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block (combNibble o)) s fun t =>
      VG.Proof.X25519.X86.Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = s.gpr .edx ∧ t.gpr .eax = BitVec.ofNat 32 (nib S i) := by
  have hbit : ∀ t < 4, s.mem (VG.X86.addr (s.gpr .edx) (o + t)) = BitVec.ofNat 8 ((S / 2 ^ (4 * i + t)) % 2) :=
    fun t ht => by
      rw [hd, addr_plus, show 8 * j + (o + t) = 7168 + (4 * i + t) by omega]
      exact hb _ (by omega)
  have hin : ∀ t < 4, InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .edx) (o + t)) 1 := fun t ht => by
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
  have hin0 : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .edx) o) 1 := by
    have h0 := hin 0 (by decide); rwa [Nat.add_zero] at h0
  have hbit0 : s.mem (VG.X86.addr (s.gpr .edx) o) = BitVec.ofNat 8 ((S / 2 ^ (4 * i)) % 2) := by
    have h0 := hbit 0 (by decide); rwa [Nat.add_zero, Nat.add_zero] at h0
  refine scalar_ld8 (by rw [d₈]) (by rw [r₈]; exact hin0)
    fun s₉ h₉ => Wp.wp_add fun s₁₀ h₁₀ _ => WP.block_nil ?_
  refine ⟨(VG.Proof.X25519.X86.updKeep h₁).trans ((VG.Proof.X25519.X86.updKeep h₂).trans ((VG.Proof.X25519.X86.updKeep h₃).trans ((VG.Proof.X25519.X86.updKeep h₄).trans
    ((VG.Proof.X25519.X86.updKeep h₅).trans ((VG.Proof.X25519.X86.updKeep h₆).trans ((VG.Proof.X25519.X86.updKeep h₇).trans ((VG.Proof.X25519.X86.updKeep h₈).trans
    ((VG.Proof.X25519.X86.updKeep h₉).trans (VG.Proof.X25519.X86.updKeep h₁₀))))))))), by rw [h₁₀.mem, h₉.mem, m₈], ?_, ?_⟩
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
      VG.Proof.X25519.X86.mask (decide (n < 8)).toNat ∧
    (BitVec.ofNat 32 n - 8 ^^^ (if decide ((BitVec.ofNat 32 n).toNat < (8 : BitVec 32).toNat) then
      BitVec.allOnes 32 else 0)) - (if decide ((BitVec.ofNat 32 n).toNat < (8 : BitVec 32).toNat) then
      BitVec.allOnes 32 else 0) = BitVec.ofNat 32 (mag n) := by
  decide

theorem combSign_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {sign n : Nat} (hsign : sign + 4 ≤ 8192)
    (hn : n < 16) (ha : s.gpr .eax = BitVec.ofNat 32 n) :
    WP isa (.block (combSign sign)) s fun t =>
      VG.Proof.X25519.X86.Keep s t ∧ Frame [VG.Proof.X25519.X86.sub x sign 4] s.mem t.mem ∧ VG.Proof.X25519.X86.wd t.mem x sign = VG.Proof.X25519.X86.mask (decide (n < 8)).toNat ∧
      t.gpr .eax = BitVec.ofNat 32 (mag n) ∧ t.gpr .edx = s.gpr .edx := by
  refine Wp.wp_subi fun s₁ h₁ c₁ _ => Wp.wp_sbb_self c₁ fun s₂ h₂ => ?_
  have k₂ : VG.Proof.X25519.X86.Keep s s₂ := (VG.Proof.X25519.X86.updKeep h₁).trans (VG.Proof.X25519.X86.updKeep h₂)
  refine Wp.wp_stm (k₂.ctx hc).edi ((k₂.ctx hc).inW hsign (by decide)) fun s₃ h₃ => ?_
  refine Wp.wp_xor fun s₄ h₄ => Wp.wp_sub fun s₅ h₅ _ => WP.block_nil ?_
  obtain ⟨f₁, f₂⟩ := sign_fact n hn
  rw [ha] at h₁ h₂
  have k₃ : VG.Proof.X25519.X86.Keep s₂ s₃ := ⟨by rw [h₃.gpr], by rw [h₃.gpr], by rw [h₃.gpr], h₃.rd, h₃.wr⟩
  refine ⟨k₂.trans (k₃.trans ((VG.Proof.X25519.X86.updKeep h₄).trans (VG.Proof.X25519.X86.updKeep h₅))), ?_, ?_, ?_, ?_⟩
  · rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit hsign (Nat.le_refl _) (Nat.le_refl _) _
  · rw [h₅.mem, h₄.mem, h₃.mem, VG.Proof.X25519.X86.wd_write_self, h₂.gpr, ← f₁]
  · rw [h₅.gpr, h₄.gpr, h₄.other .ecx (by decide), h₃.gpr, h₂.gpr, h₂.other .eax (by decide), h₁.gpr]
    exact f₂
  · rw [h₅.other .edx (by decide), h₄.other .edx (by decide), h₃.gpr, h₂.other .edx (by decide),
      h₁.other .edx (by decide)]


/-! ## The masks of the magnitudes -/

private theorem mask_fact : ∀ a < 9, ∀ k < 9,
    (if decide ((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 k).toNat < (1 : BitVec 32).toNat) then
      BitVec.allOnes 32 else 0) = VG.Proof.X25519.X86.mask (decide (a = k)).toNat := by
  decide

theorem combMask_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {masks a : Nat} (k : Nat)
    (hm : masks + 36 ≤ 8192) (ha : a < 9) (hk : k < 9) (hax : s.gpr .eax = BitVec.ofNat 32 a) :
    WP isa (.block (combMask masks k)) s fun t =>
      VG.Proof.X25519.X86.Keep s t ∧ t.gpr .eax = s.gpr .eax ∧ t.gpr .edx = s.gpr .edx ∧
      Frame [VG.Proof.X25519.X86.sub x (masks + 4 * k) 4] s.mem t.mem ∧
      VG.Proof.X25519.X86.wd t.mem x (masks + 4 * k) = VG.Proof.X25519.X86.mask (decide (a = k)).toNat := by
  refine Wp.wp_mov fun s₁ h₁ => wp_xori fun s₂ h₂ => Wp.wp_subi fun s₃ h₃ c₃ _ =>
    Wp.wp_sbb_self c₃ fun s₄ h₄ => ?_
  have k₄ : VG.Proof.X25519.X86.Keep s s₄ := (VG.Proof.X25519.X86.updKeep h₁).trans ((VG.Proof.X25519.X86.updKeep h₂).trans ((VG.Proof.X25519.X86.updKeep h₃).trans (VG.Proof.X25519.X86.updKeep h₄)))
  have hw : masks + 4 * k + 4 ≤ 8192 := by omega
  refine Wp.wp_stm (k₄.ctx hc).edi ((k₄.ctx hc).inW hw (by decide)) fun t ht => WP.block_nil ?_
  have e₃ : s₂.gpr .ecx = BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 k := by rw [h₂.gpr, h₁.gpr, hax]
  refine ⟨k₄.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, h₄.other .eax (by decide), h₃.other .eax (by decide), h₂.other .eax (by decide),
      h₁.other .eax (by decide)]
  · rw [ht.gpr, h₄.other .edx (by decide), h₃.other .edx (by decide), h₂.other .edx (by decide),
      h₁.other .edx (by decide)]
  · rw [ht.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit hw (Nat.le_refl _) (Nat.le_refl _) _
  · rw [ht.mem, VG.Proof.X25519.X86.wd_write_self, h₄.gpr, ← mask_fact a ha k hk, e₃]


theorem combMaskAll_ok {x : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.X86.Ctx x s₀) {masks a : Nat}
    (hm : masks + 36 ≤ 8192) (ha : a < 9) (hax : s₀.gpr .eax = BitVec.ofNat 32 a) : ∀ n ≤ 9,
    WP isa (.block ((List.range n).flatMap (combMask masks))) s₀ fun t =>
      VG.Proof.X25519.X86.Keep s₀ t ∧ t.gpr .eax = s₀.gpr .eax ∧ t.gpr .edx = s₀.gpr .edx ∧
      Frame [VG.Proof.X25519.X86.sub x masks (4 * n)] s₀.mem t.mem ∧
      ∀ k < n, VG.Proof.X25519.X86.wd t.mem x (masks + 4 * k) = VG.Proof.X25519.X86.mask (decide (a = k)).toNat
  | 0, _ => WP.block_nil ⟨Keep.refl _, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (combMaskAll_ok hc hm ha hax n (by omega))
      fun s₁ ⟨k₁, a₁, d₁, f₁, w₁⟩ => ?_)
    refine WP.mono (combMask_ok (k₁.ctx hc) n hm ha (by omega) (a₁.trans hax))
      fun t ⟨kt, at', dt, ft, wt⟩ => ?_
    refine ⟨k₁.trans kt, at'.trans a₁, dt.trans d₁, ?_, fun k hk => ?_⟩
    · exact (VG.Proof.X25519.X86.frameWiden f₁ hc.fit (Nat.le_refl _) (by omega) (by omega)).trans
        (VG.Proof.X25519.X86.frameWiden ft hc.fit (by omega) (by omega) (by omega))
    · by_cases e : k = n
      · subst e; exact wt
      · rw [VG.Proof.X25519.X86.wd_frame1 ft hc.fit (by omega) (by omega) (by omega)]; exact w₁ k (by omega)

/-- A byte of the scalar's bits, outside the masks. -/
theorem digit_bit {x : BitVec 32} {m m' : Mem} (hf : Frame [VG.Proof.X25519.X86.sub x 1024 136] m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) {q : Nat} (hq : q < 512) :
    m' (VG.X86.addr x (7168 + q)) = m (VG.X86.addr x (7168 + q)) := by
  apply hf
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (VG.Proof.X25519.X86.sub_disj (by omega_using [hx, hq]) (by omega_using [hx])
    (Or.inr (by omega)) : (VG.Proof.X25519.X86.sub x (7168 + q) 1).Disjoint (VG.Proof.X25519.X86.sub x 1024 136)) _ (Region.contains_self _ _)

/-- Both digits' masks, of table `j`. -/
structure DigitMasks (x : BitVec 32) (S j : Nat) (m : Mem) : Prop where
  oddMask : ∀ k < 9, VG.Proof.X25519.X86.wd m x (combOddMasks + 4 * k) = VG.Proof.X25519.X86.mask (decide (mag (nib S (2 * j + 1)) = k)).toNat
  evenMask : ∀ k < 9, VG.Proof.X25519.X86.wd m x (combEvenMasks + 4 * k) = VG.Proof.X25519.X86.mask (decide (mag (nib S (2 * j)) = k)).toNat
  oddSign : VG.Proof.X25519.X86.wd m x combOddSign = VG.Proof.X25519.X86.mask (decide (nib S (2 * j + 1) < 8)).toNat
  evenSign : VG.Proof.X25519.X86.wd m x combEvenSign = VG.Proof.X25519.X86.mask (decide (nib S (2 * j) < 8)).toNat

theorem combDigits_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {S j : Nat} (hj : j < 32)
    (hs : s.gpr .esi = BitVec.ofNat 32 j)
    (hb : ∀ q < 256, s.mem (VG.X86.addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
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
  have f₁₄ : Frame [VG.Proof.X25519.X86.sub x 1024 136] s.mem s₄.mem := by
    rw [← m₁, ← m₂]
    exact (VG.Proof.X25519.X86.frameWiden f₃ hfit (by decide) (by decide) (by decide)).trans
      (VG.Proof.X25519.X86.frameWiden f₄ hfit (by decide) (by decide) (by decide))
  refine WP.block_append (WP.mono (combNibble_ok c₄ (S := S) (i := 2 * j) hj (Or.inl rfl)
    (by omega) (by rw [d₄, d₃, d₂, d₁]) (fun q hq => by rw [digit_bit f₁₄ hfit (by omega)]; exact hb q hq))
    fun s₅ ⟨k₅, m₅, _, a₅⟩ => ?_)
  have c₅ := k₅.ctx c₄
  refine WP.block_append (WP.mono (combSign_ok c₅ (by decide) (nib_lt S _) a₅)
    fun s₆ ⟨k₆, f₆, w₆, a₆, _⟩ => ?_)
  have c₆ := k₆.ctx c₅
  refine WP.mono (combMaskAll_ok c₆ (by decide) (mag_lt (nib_lt S _)) a₆ 9 (le_refl _))
    fun t ⟨kt, _, _, ft, wt⟩ => ?_
  have f₅t : Frame [VG.Proof.X25519.X86.sub x 1024 136] s₄.mem t.mem := by
    rw [← m₅]
    exact (VG.Proof.X25519.X86.frameWiden f₆ hfit (by decide) (by decide) (by decide)).trans
      (VG.Proof.X25519.X86.frameWiden ft hfit (by decide) (by decide) (by decide))
  refine ⟨⟨k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans (k₆.trans kt))))), f₁₄.trans f₅t⟩,
    ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩⟩
  · rw [VG.Proof.X25519.X86.wd_frame1 ft hfit (by decide) (by simp only [combOddMasks]; omega)
      (by simp only [combOddMasks, combEvenMasks]; omega),
      VG.Proof.X25519.X86.wd_frame1 f₆ hfit (by decide) (by simp only [combOddMasks]; omega)
      (by simp only [combOddMasks, combEvenSign]; omega), m₅]
    exact w₄ k hk
  · exact wt k hk
  · rw [VG.Proof.X25519.X86.wd_frame1 ft hfit (by decide) (by decide) (by decide), VG.Proof.X25519.X86.wd_frame1 f₆ hfit (by decide) (by decide)
      (by decide), m₅, VG.Proof.X25519.X86.wd_frame1 f₄ hfit (by decide) (by decide) (by decide)]
    exact w₃
  · rw [VG.Proof.X25519.X86.wd_frame1 ft hfit (by decide) (by decide) (by decide)]
    exact w₆

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CombSelect`. -/
section

/-!
# The comb's constant-time selection, for two digits at once

With the word at `combOddMasks + 4k` (`combEvenMasks + 4k`) all ones exactly
for `k` the odd (even) digit's magnitude, `selectWord` loads every nonzero
candidate word once, ANDs it with both digits' masks and ORs it into `ebx`
and `ebp`, so only each digit's candidate survives, and stores them.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519 VG.Impl.Ed25519.X86 VG.Proof.Ed25519
open VG.Impl.X25519.X86 (sc)

/-- The masks of both digits' magnitudes `ao` and `ae`, in memory. -/
def Masks (x : BitVec 32) (ao ae : Nat) (m : Mem) : Prop :=
  (∀ k < 9, wd m x (combOddMasks + 4 * k) = mask (decide (ao = k)).toNat) ∧
  (∀ k < 9, wd m x (combEvenMasks + 4 * k) = mask (decide (ae = k)).toNat)

theorem or0 (v : BitVec 32) : v ||| 0 = v := by ext i; simp
theorem zor (v : BitVec 32) : 0 ||| v = v := by ext i; simp

theorem mask_and (v : BitVec 32) (b : Bool) : v &&& mask b.toNat = if b then v else 0 := by
  cases b
  · show v &&& mask 0 = 0
    rw [show mask 0 = 0 by decide]; ext i; simp
  · show v &&& mask 1 = v
    rw [show mask 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

/-- The masks survive stores below them. -/
theorem Masks.frame {x : BitVec 32} {ao ae : Nat} {m m' : Mem} (h : Masks x ao ae m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ d, 1024 ≤ d → d + 4 ≤ 1160 → ∀ r ∈ rs, (sub x d 4).Disjoint r) :
    Masks x ao ae m' :=
  ⟨fun k hk => (wd_frame hf (hd _ (by simp only [combOddMasks]; omega)
      (by simp only [combOddMasks]; omega))).trans (h.1 k hk),
    fun k hk => (wd_frame hf (hd _ (by simp only [combEvenMasks]; omega)
      (by simp only [combEvenMasks]; omega))).trans (h.2 k hk)⟩

theorem selectCand_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) (v : Spec.X25519.Fe) {k : Nat} (hk : k < 9) (w : Nat) :
    WP isa (.block (selectCand v k w)) s fun t =>
      t.gpr .ebx = s.gpr .ebx ||| (if ao = k then feWord v w else 0) ∧
      t.gpr .ebp = s.gpr .ebp ||| (if ae = k then feWord v w else 0) ∧
      Keep s t ∧ t.mem = s.mem := by
  unfold selectCand
  split
  · rename_i h0
    refine WP.block_nil ⟨?_, ?_, Keep.refl _, rfl⟩ <;> (split <;> simp only [h0, or0])
  · refine Wp.wp_movi fun s₁ h₁ => Wp.wp_mov fun s₂ h₂ => ?_
    have k₂ : Keep s s₂ := (updKeep h₁).trans (updKeep h₂)
    have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
    refine wp_andm (k₂.ctx hc).edi ((k₂.ctx hc).inRW (by simp only [combOddMasks]; omega) (by decide))
      fun s₃ h₃ => ?_
    have k₃ := k₂.trans (updKeep h₃)
    refine wp_andm (k₃.ctx hc).edi ((k₃.ctx hc).inRW (by simp only [combEvenMasks]; omega) (by decide))
      fun s₄ h₄ => Wp.wp_or fun s₅ h₅ => Wp.wp_or fun s₆ h₆ => WP.block_nil ?_
    have m₃ : s₃.mem = s.mem := by rw [h₃.mem, m₂]
    refine ⟨?_, ?_, k₃.trans ((updKeep h₄).trans ((updKeep h₅).trans (updKeep h₆))),
      by rw [h₆.mem, h₅.mem, h₄.mem, m₃]⟩
    · rw [h₆.other .ebx (by decide), h₅.gpr, h₄.other .ebx (by decide), h₄.other .eax (by decide),
        h₃.gpr, h₃.other .ebx (by decide), h₂.other .ebx (by decide), h₂.other .eax (by decide),
        h₁.gpr, h₁.other .ebx (by decide), m₂]
      change _ ||| (feWord v w &&& wd s.mem x (combOddMasks + 4 * k)) = _
      rw [hm.1 k hk, mask_and]
      by_cases e : ao = k <;> simp [e]
    · rw [h₆.gpr, h₅.other .ebp (by decide), h₅.other .edx (by decide), h₄.gpr,
        h₄.other .ebp (by decide), h₃.other .ebp (by decide), h₃.other .edx (by decide), h₂.gpr,
        h₂.other .ebp (by decide), h₁.gpr, h₁.other .ebp (by decide), m₃]
      change _ ||| (feWord v w &&& wd s.mem x (combEvenMasks + 4 * k)) = _
      rw [hm.2 k hk, mask_and]
      by_cases e : ae = k <;> simp [e]

/-- Word `w` of `vs[a]` after the candidates `k < n`, zero if `a ≥ n`. -/
def selWord (vs : List Spec.X25519.Fe) (a n w : Nat) : BitVec 32 :=
  if a < n then feWord (vs.getD a 0) w else 0

theorem sel_step (vs : List Spec.X25519.Fe) (a n w : Nat) :
    selWord vs a n w ||| (if a = n then feWord (vs.getD n 0) w else 0) = selWord vs a (n + 1) w := by
  unfold selWord
  by_cases h : a < n
  · simp only [h, ↓reduceIte, show a < n + 1 by omega, show ¬ a = n by omega, or0]
  · by_cases he : a = n
    · subst he
      simp only [h, ↓reduceIte, Nat.lt_succ_self, zor]
    · simp only [h, he, ↓reduceIte, show ¬ a < n + 1 by omega, or0]

theorem selectCands_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) (vs : List Spec.X25519.Fe) (w : Nat) :
    ∀ n ≤ 9, WP isa (.block ((List.range n).flatMap fun k => selectCand (vs.getD k 0) k w)) s
      fun t => t.gpr .ebx = s.gpr .ebx ||| selWord vs ao n w ∧
        t.gpr .ebp = s.gpr .ebp ||| selWord vs ae n w ∧ Keep s t ∧ t.mem = s.mem
  | 0, _ => WP.block_nil ⟨by simp only [selWord, Nat.not_lt_zero, ↓reduceIte, or0],
      by simp only [selWord, Nat.not_lt_zero, ↓reduceIte, or0], Keep.refl _, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (selectCands_ok hc hm vs w n (by omega)) fun t ⟨tb, tp, kt, mt⟩ => ?_)
    refine WP.mono (selectCand_ok (ao := ao) (ae := ae) (kt.ctx hc) (by rw [mt]; exact hm) _
      (by omega : n < 9) w)
      fun u ⟨ub, up, ku, mu⟩ => ⟨?_, ?_, kt.trans ku, mu.trans mt⟩
    · rw [ub, tb, BitVec.or_assoc, sel_step]
    · rw [up, tp, BitVec.or_assoc, sel_step]

theorem selectWord_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) (vs : List Spec.X25519.Fe) {o e : Nat} (ho : o + 32 ≤ 1024)
    (he : e + 32 ≤ 1024) (w : Nat) (hw : w < 8) :
    WP isa (.block (selectWord vs o e w)) s fun t => Keep s t ∧
      t.mem = (s.mem.writeW (addr x (o + 4 * w)) (selWord vs ao 9 w)).writeW (addr x (e + 4 * w))
        (selWord vs ae 9 w) := by
  rw [show selectWord vs o e w = .mov .ebx (.imm 0) :: .mov .ebp (.imm 0) ::
    ((List.range 9).flatMap (fun k => selectCand (vs.getD k 0) k w) ++
      ([.store (sc (o + 4 * w)) .ebx, .store (sc (e + 4 * w)) .ebp] : List Instr)) from rfl]
  refine Wp.wp_movi fun s₁ h₁ => Wp.wp_movi fun s₂ h₂ => ?_
  have k₂ : Keep s s₂ := (updKeep h₁).trans (updKeep h₂)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  rw [WP.block_append_iff]
  refine WP.mono (selectCands_ok (ao := ao) (ae := ae) (k₂.ctx hc) (by rw [m₂]; exact hm) vs w 9
    (le_refl _))
    fun t ⟨tb, tp, kt, mt⟩ => ?_
  have k₃ := k₂.trans kt
  refine Wp.wp_stm (k₃.ctx hc).edi ((k₃.ctx hc).inW (by omega) (by decide)) fun u hu => ?_
  have ku : Keep t u := ⟨by rw [hu.gpr], by rw [hu.gpr], by rw [hu.gpr], hu.rd, hu.wr⟩
  refine Wp.wp_stm ((k₃.trans ku).ctx hc).edi (((k₃.trans ku).ctx hc).inW (by omega) (by decide))
    fun v hv => WP.block_nil ⟨k₃.trans (ku.trans ⟨by rw [hv.gpr], by rw [hv.gpr], by rw [hv.gpr],
      hv.rd, hv.wr⟩), ?_⟩
  rw [hv.mem, hu.mem, hu.gpr, mt, m₂, tb, tp, h₂.other .ebx (by decide), h₂.gpr, h₁.gpr, zor, zor]

/-- Two regions of the workspace (`[o, o + n)` and `[e, e + n)`) may change. -/
abbrev Frame2 (x : BitVec 32) (o e n : Nat) (m m' : Mem) : Prop := Frame [sub x o n, sub x e n] m m'

theorem selectFieldPrefix_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) (vs : List Spec.X25519.Fe) {o e : Nat} (ho : o + 32 ≤ 1024)
    (he : e + 32 ≤ 1024) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun w => selectWord vs o e w)) s fun t =>
      Keep s t ∧ Frame2 x o e 32 s.mem t.mem ∧
      ∀ w < n, wd t.mem x (o + 4 * w) = selWord vs ao 9 w ∧ wd t.mem x (e + 4 * w) = selWord vs ae 9 w
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have hfit := hc.fit
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (selectFieldPrefix_ok hc hm vs ho he hoe n (by omega))
      fun t ⟨kt, ft, wt⟩ => ?_)
    have hmt : Masks x ao ae t.mem := hm.frame ft fun d h1 h2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
      · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
    refine WP.mono (selectWord_ok (kt.ctx hc) hmt vs ho he n (by omega)) fun u ⟨ku, mu⟩ =>
      ⟨kt.trans ku, ?_, fun w hw => ?_⟩
    · rw [mu]
      refine (ft.writeW List.mem_cons_self _ ?_).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ ?_
      · exact sub_contains (by omega) (by omega) (by omega) (by decide)
      · exact sub_contains (by omega) (by omega) (by omega) (by decide)
    · rw [mu]
      by_cases hwn : w = n
      · subst hwn
        refine ⟨?_, wd_write_self _ _ _ _⟩
        rw [wd_write_ne _ _ (by omega) (by omega) (by omega), wd_write_self]
      · have hwl : w < n := by omega
        rw [wd_write_ne _ _ (by omega) (by omega) (by omega), wd_write_ne _ _ (by omega) (by omega)
          (by omega), wd_write_ne _ _ (by omega) (by omega) (by omega),
          wd_write_ne _ _ (by omega) (by omega) (by omega)]
        exact wt w hwl

theorem feWord_num (v : Spec.X25519.Fe) :
    num (fun w => (feWord v w).toNat) 8 = v.val := by
  rw [num_congr (g := fun k => v.val / (2 ^ 32) ^ k % 2 ^ 32) (fun k _ => by
    simp only [feWord, BitVec.toNat_ofNat]), num_digits]
  exact Nat.mod_eq_of_lt (by have h := v.isLt; simp only [Spec.X25519.P] at h; omega)

theorem selectField_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks x ao ae s.mem) (vs : List Spec.X25519.Fe) {o e : Nat}
    (ho : o + 32 ≤ 1024) (he : e + 32 ≤ 1024) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o) :
    WP isa (.block (selectField vs o e)) s fun t =>
      Keep s t ∧ Frame2 x o e 32 s.mem t.mem ∧
      VG.Proof.X25519.X86.F t.mem x o = vs.getD ao 0 ∧ VG.Proof.X25519.X86.F t.mem x e = vs.getD ae 0 := by
  refine WP.mono (selectFieldPrefix_ok hc hm vs ho he hoe 8 (le_refl _)) fun t ⟨kt, ft, wt⟩ =>
    ⟨kt, ft, ?_, ?_⟩
  · have hf : fe t.mem x o = (vs.getD ao 0).val := by
      unfold fe
      rw [← feWord_num]
      refine num_congr fun w hw => ?_
      show (wd t.mem x (o + 4 * w)).toNat = _
      rw [(wt w hw).1, selWord]; simp only [hao, ↓reduceIte]
    rw [VG.Proof.X25519.X86.F, hf, VG.Proof.X25519.toFe_self]
  · have hf : fe t.mem x e = (vs.getD ae 0).val := by
      unfold fe
      rw [← feWord_num]
      refine num_congr fun w hw => ?_
      show (wd t.mem x (e + 4 * w)).toNat = _
      rw [(wt w hw).2, selWord]; simp only [hae, ↓reduceIte]
    rw [VG.Proof.X25519.X86.F, hf, VG.Proof.X25519.toFe_self]

theorem Frame2.F {x : BitVec 32} {o e q : Nat} {m m' : Mem} (h : Frame2 x o e 32 m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (ho : o + 32 ≤ 8192) (he : e + 32 ≤ 8192) (hq : q + 32 ≤ 8192)
    (h1 : q + 32 ≤ o ∨ o + 32 ≤ q) (h2 : q + 32 ≤ e ∨ e + 32 ≤ q) :
    VG.Proof.X25519.X86.F m' x q = VG.Proof.X25519.X86.F m x q :=
  congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega) (by omega) (by omega)
    · exact sub_disj (by omega) (by omega) (by omega))

theorem Frame2.widen {x : BitVec 32} {o e o' e' : Nat} {m m' : Mem} (h : Frame2 x o e 32 m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (h1 : o' ≤ o) (h2 : o + 32 ≤ o' + 96) (h3 : e' ≤ e)
    (h4 : e + 32 ≤ e' + 96) (ho : o < 8192) (he : e < 8192) :
    Frame [sub x o' 96, sub x e' 96] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_sub hx h1 h2 ho⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_sub hx h3 h4 he⟩

/-- The cached point in slots `a`, `b`, `c`, with `2Z = 2`. -/
def cachedAt (e : Env) (a b c : Slot) : Spec.Ed25519.Point := ⟨e a, e b, e c, 2⟩

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.Ed25519.Point → Spec.X25519.Fe) :
    (((List.range 9).map (combCached j)).map f).getD a 0 = f (combCached j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

theorem combCached_T (j a : Nat) : (combCached j a).T = 2 := by
  unfold combCached
  split
  · rfl
  · split; rfl

theorem cachedAt_eq {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point} (hq : q.T = 2)
    (ha : e a = q.X) (hb : e b = q.Y) (hc : e c = q.Z) : cachedAt e a b c = q := by
  cases q
  simp only [cachedAt, ha, hb, hc] at hq ⊢
  rw [hq]

/-- The selection's frame: slots 4–6 and 13–15. -/
abbrev SelFrame (x : BitVec 32) (m m' : Mem) : Prop := Frame [sub x (offset 4) 96, sub x (offset 13) 96] m m'

theorem combSelect_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks x ao ae s.mem) (j : Nat) :
    WP isa (.block (combSelect j)) s fun t =>
      cachedAt (env t.mem x) 4 5 6 = combCached j ao ∧
      cachedAt (env t.mem x) 13 14 15 = combCached j ae ∧ Keep s t ∧ SelFrame x s.mem t.mem := by
  have hfit := hc.fit
  have mf : ∀ {m m' : Mem} {o e : Nat}, Masks x ao ae m → Frame2 x o e 32 m m' → o + 32 ≤ 1024 →
      e + 32 ≤ 1024 → Masks x ao ae m' := fun hm f ho he => hm.frame f fun d h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
    · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
  rw [combSelect]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok hc hao hae hm _ (o := offset 4) (e := offset 13) (by decide) (by decide)
    (by decide)) fun b ⟨kb, fb, b4, b13⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok (kb.ctx hc) hao hae (mf hm fb (by decide) (by decide)) _ (o := offset 5)
    (e := offset 14) (by decide) (by decide) (by decide)) fun c ⟨kc, fc, c5, c14⟩ => ?_
  refine WP.mono (selectField_ok ((kb.trans kc).ctx hc) hao hae
    (mf (mf hm fb (by decide) (by decide)) fc (by decide) (by decide)) _ (o := offset 6) (e := offset 15)
    (by decide) (by decide) (by decide)) fun t ⟨kt, ft, t6, t15⟩ => ⟨?_, ?_, (kb.trans kc).trans kt, ?_⟩
  · rw [entries_getD j ao hao] at b4 c5 t6
    refine cachedAt_eq (combCached_T j ao) ?_ ?_ t6
    · change VG.Proof.X25519.X86.F t.mem x (offset 4) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide),
        fc.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), b4]
    · change VG.Proof.X25519.X86.F t.mem x (offset 5) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), c5]
  · rw [entries_getD j ae hae] at b13 c14 t15
    refine cachedAt_eq (combCached_T j ae) ?_ ?_ t15
    · change VG.Proof.X25519.X86.F t.mem x (offset 13) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide),
        fc.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), b13]
    · change VG.Proof.X25519.X86.F t.mem x (offset 14) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), c14]
  · exact ((fb.widen hfit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (fc.widen hfit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))).trans
      (ft.widen hfit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

theorem combSelectFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 32) {x : BitVec 32} {s : State}
    (hc : Ctx x s) {ao ae : Nat} (hao : ao < 9) (hae : ae < 9) (hm : Masks x ao ae s.mem)
    {j : Nat} (hj : j ∈ ks) (hj32 : j < 32) (hesi : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (combSelectFrom ks) s fun t =>
      cachedAt (env t.mem x) 4 5 6 = combCached j ao ∧
      cachedAt (env t.mem x) 13 14 15 = combCached j ae ∧ Keep s t ∧ SelFrame x s.mem t.mem := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    have hk : k < 32 := hks k List.mem_cons_self
    rw [combSelectFrom]
    have hcmp : WP isa (.block [.alu .cmp .esi (.imm (BitVec.ofNat 32 k))]) s fun t =>
        Keep s t ∧ t.mem = s.mem ∧ t.zf = some (decide (j = k)) :=
      Wp.wp_cmpi fun t ht _ zt => WP.block_nil ⟨⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd,
        ht.wr⟩, ht.mem, by rw [zt, hesi, Wp.sub_beq (by omega) (by omega)]⟩
    refine WP.seq (WP.mono hcmp fun t ⟨kt, mt, zt⟩ => ?_)
    have ct := kt.ctx hc
    have hmt : Masks x ao ae t.mem := by rw [mt]; exact hm
    refine WP.ite (decide (j = k)) zt (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      refine WP.mono (combSelect_ok ct hao hae hmt j) fun u ⟨u1, u2, ku, fu⟩ =>
        ⟨u1, u2, kt.trans ku, by rw [← mt]; exact fu⟩
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      refine WP.mono (ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) ct hmt hj'
        (by rw [kt.esi]; exact hesi)) fun u ⟨u1, u2, ku, fu⟩ =>
        ⟨u1, u2, kt.trans ku, by rw [← mt]; exact fu⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.RecoverSign`. -/
section

/-! Merged from `Proof.Ed25519.X86.RecoverAdjust`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩
def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem recoverSuccess_ok {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa (.block recoverSuccess) s fun t => FieldKeep x s t ∧ t.gpr .eax = 1 ∧
      point (env t.mem x) 0 1 2 3 = recoveredPoint (env s.mem x 0) (env s.mem x 1) := by
  rw [recoverSuccess, WP.block_append_iff]
  refine WP.mono (fieldCode_ok recoverSuccessOps hc) fun a ⟨ka, ea⟩ => ?_
  refine WP.mono (returnFlag_ok a x true) fun t ⟨kt, mt, rt⟩ => ?_
  exact ⟨ka.trans kt, rt, by rw [mt, ea]; rfl⟩

private theorem adjustBranch_ok {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s) (b : Bool)
    (hz : s.zf = some (((env s.mem x 0).val % 2 == 1) == b)) :
    WP isa (.ite .e (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0]))) s fun t =>
      FieldKeep x s t ∧ env t.mem x 0 = signedX (env s.mem x 0) b ∧ env t.mem x 1 = env s.mem x 1 := by
  apply WP.ite (((env s.mem x 0).val % 2 == 1) == b) hz
  · intro h
    exact WP.block_nil ⟨FieldKeep.refl _ _, by simp only [signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] hc) fun t ⟨kt, et⟩ => ?_
    refine ⟨kt, ?_, ?_⟩
    · rw [et]
      change 0 - env s.mem x 0 = signedX (env s.mem x 0) b
      simp only [signedX, h, Bool.false_eq_true, ite_false]
    · rw [et]; rfl

theorem recoverAdjustSign_ok {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa recoverAdjustSign s fun t => FieldKeep x s t ∧ t.gpr .eax = 1 ∧
      point (env t.mem x) 0 1 2 3 = recoveredPoint (signedX (env s.mem x 0) b) (env s.mem x 1) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hc 0) fun a ⟨ka, ea, va⟩ => ?_
  refine WP.mono (recoverParity_ok (ka.ctx hc) b (ka.keep.esi.trans hb)) fun c ⟨kc, mc, zc⟩ => ?_
  have ec : env c.mem x = env s.mem x := by rw [mc, ea]
  have zc' : c.zf = some (((env c.mem x 0).val % 2 == 1) == b) := by
    change VG.Proof.X25519.X86.fe a.mem x 64 = _ at va
    rw [zc, va, ec]
  refine WP.seq (WP.mono (adjustBranch_ok ((ka.trans kc).ctx hc) b zc') fun d ⟨kd, dx, dy⟩ => ?_)
  refine WP.mono (recoverSuccess_ok (((ka.trans kc).trans kd).ctx hc)) fun t ⟨kt, rt, pt⟩ => ?_
  exact ⟨((ka.trans kc).trans kd).trans kt, rt, by rw [pt, dx, dy, ec]⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def DecodeResult (x : BitVec 32) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .eax = 0
  | some p => s.gpr .eax = 1 ∧ point (env s.mem x) 0 1 2 3 = p

def signResult (x y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if x = 0 && b then none else some (recoveredPoint (signedX x b) y)

theorem recoverInvalid_ok (s : State) (x : BitVec 32) :
    WP isa recoverInvalid s fun t => FieldKeep x s t ∧ DecodeResult x none t :=
  WP.mono (returnFlag_ok s x false) fun _ ⟨kt, _, rt⟩ => ⟨kt, rt⟩

theorem signTest_ok {s : State} (x : BitVec 32) (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa (.block [.alu .test .esi (.reg .esi)]) s fun t => FieldKeep x s t ∧ t.mem = s.mem ∧
      isa.eval .ne t = some b := by
  refine Wp.wp_test fun t ht zt => WP.block_nil ?_
  refine ⟨FieldKeep.of_mem ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩ ht.mem, ht.mem, ?_⟩
  show t.zf.map (!·) = _
  rw [zt, BitVec.and_self, hb]
  cases b <;> rfl

theorem recoverSign_ok {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa recoverSign s fun t => FieldKeep x s t ∧
      DecodeResult x (signResult (env s.mem x 0) (env s.mem x 1) b) t := by
  refine WP.seq (WP.mono (fieldZero_ok hc 0) fun a ⟨ka, ea, za⟩ => ?_)
  apply WP.ite (decide (env s.mem x 0 = 0)) za
  · intro hzero
    have hz := of_decide_eq_true hzero
    refine WP.seq (WP.mono (signTest_ok x b (ka.keep.esi.trans hb)) fun c ⟨kc, mc, zc⟩ => ?_)
    have ec : env c.mem x = env s.mem x := by rw [mc, ea]
    apply WP.ite b zc
    · intro ht
      refine WP.mono (recoverInvalid_ok c x) fun t ⟨kt, tr⟩ => ?_
      refine ⟨(ka.trans kc).trans kt, ?_⟩
      simpa only [signResult, hz, ht, decide_true, Bool.and_self, ite_true] using tr
    · intro hf
      refine WP.mono (recoverAdjustSign_ok ((ka.trans kc).ctx hc) b
        (kc.keep.esi.trans (ka.keep.esi.trans hb))) fun t ⟨kt, rt, pt⟩ => ?_
      refine ⟨(ka.trans kc).trans kt, ?_⟩
      simp only [signResult, hf, Bool.and_false, Bool.false_eq_true, ite_false, DecodeResult]
      exact ⟨rt, by rw [ec, hf] at pt; exact pt⟩
  · intro hnonzero
    have hn := of_decide_eq_false hnonzero
    refine WP.mono (recoverAdjustSign_ok (ka.ctx hc) b (ka.keep.esi.trans hb)) fun t ⟨kt, rt, pt⟩ => ?_
    refine ⟨ka.trans kt, ?_⟩
    simp only [signResult, hn, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, DecodeResult]
    exact ⟨rt, by rw [ea] at pt; exact pt⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.RecoverPoint`. -/
section

/-! Merged from `Proof.Ed25519.X86.RecoverCandidate`. -/
section
/-! Candidate root and its squared check agree with the decoding specification. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

private theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧
    evalOps recoverInitOps e 6 = rootU (e 1) ∧
    evalOps recoverInitOps e 7 = rootV (e 1) ∧
    evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
    evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact pow_three _
  · exact congrArg (rootU (e 1) * ·) (pow_seven _)

private theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧
    evalOps recoverFinishOps e 1 = e 1 ∧
    evalOps recoverFinishOps e 5 = 0 ∧
    evalOps recoverFinishOps e 6 = e 6 ∧
    evalOps recoverFinishOps e 7 = e 7 ∧
    evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
    evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rootEnv_low (e : Env) (i : Slot) (hi : i.val < 14) : rootEnv e i = e i := by
  have h14 : i ≠ 14 := by intro h; subst i; contradiction
  have h15 : i ≠ 15 := by intro h; subst i; contradiction
  have h16 : i ≠ 16 := by intro h; subst i; contradiction
  have h17 : i ≠ 17 := by intro h; subst i; contradiction
  simp only [rootEnv, power250Env, opMul, opSqn, Function.update_apply, h14, h15, h16, h17, ite_false]

theorem recoverCandidate_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.X86.Ctx base s) :
    WP isa recoverCandidate s fun t => IKeep base s t ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  rw [recoverCandidate]
  refine WP.seq (WP.mono (fieldCode_ok recoverInitOps hs) fun a ⟨ka, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPower_spec base a (ka.ctx hs)) fun b ⟨kb, eb⟩ => ?_)
  have kbr := kb
  have vb : env b.mem base 15 = VG.Proof.Ed25519.rootPower (env a.mem base 2) := by rw [eb, rootEnv_eval]
  have be : ∀ i : Slot, i.val < 14 → env b.mem base i = env a.mem base i := by
    intro i hi
    rw [eb]
    exact rootEnv_low _ i hi
  refine WP.mono (fieldCode_ok recoverFinishOps (kbr.ctx (ka.ctx hs))) fun t ⟨kt, vt⟩ => ?_
  have ay := (recoverInit_eval (env s.mem base)).1
  have au := (recoverInit_eval (env s.mem base)).2.1
  have av := (recoverInit_eval (env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (env s.mem base)).2.2.2.2
  have bx : env b.mem base 6 * env b.mem base 9 * env b.mem base 15 = rootX (env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, rootPower_eq, va, au, av3, az]
    rfl
  have kar : IKeep base s a := IKeep.of_field ka
  have ktr : IKeep base b t := IKeep.of_field kt
  refine ⟨kar.trans (kbr.trans ktr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.X86
end

/-! Candidate validation implements RFC 8032's recoverX exactly. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

def recoverResult (y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
  else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b
  else none

private theorem signResult_map (x y : Spec.X25519.Fe) (b : Bool) :
    signResult x y b = (do
      let z ← some x
      if z = 0 && b then none else some (signedX z b)).map (fun z => recoveredPoint z y) := by
  unfold signResult
  change (if x = 0 && b then none else some (recoveredPoint (signedX x b) y)) =
    (if x = 0 && b then none else some (signedX x b)).map (fun z => recoveredPoint z y)
  split <;> rfl

theorem recoverResult_spec (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (Spec.Ed25519.recoverX y b).map (fun x => recoveredPoint x y) := by
  unfold recoverResult Spec.Ed25519.recoverX
  change (if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
    else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b else none) =
    (if rootV y * rootX y * rootX y = rootU y then (do
        let z ← some (rootX y)
        if z = 0 && b then none else some (signedX z b))
      else if rootV y * rootX y * rootX y = 0 - rootU y then (do
        let z ← some (rootX y * Spec.Ed25519.sqrtM1)
        if z = 0 && b then none else some (signedX z b))
      else none).map (fun x => recoveredPoint x y)
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h]
    exact signResult_map _ _ _
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h']
      exact signResult_map _ _ _
    · rw [ite_eq_right h', ite_eq_right h']
      rfl


private theorem sign_known {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.X86.Ctx base s)
    (b : Bool) (hb : s.gpr .esi = signWord b) (x y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa recoverSign s fun t => FieldKeep base s t ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hs b hb) fun t ⟨kt, tr⟩ => ?_
  exact ⟨kt, by rw [hx, hy] at tr; exact tr⟩

theorem recoverChecks_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.X86.Ctx base s)
    (b : Bool) (hb : s.gpr .esi = signWord b) (y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = rootX y) (hy : env s.mem base 1 = y)
    (hu : env s.mem base 6 = rootU y)
    (hvx : env s.mem base 11 = rootV y * rootX y * rootX y)
    (hnu : env s.mem base 12 = 0 - rootU y) :
    WP isa recoverChecks s fun t => FieldKeep base s t ∧ DecodeResult base (recoverResult y b) t := by
  refine WP.seq (WP.mono (fieldEqual_ok hs 11 6) fun c ⟨kc, ce, cz⟩ => ?_)
  have cx : env c.mem base 0 = rootX y := (ce 0 (by decide)).trans hx
  have cy : env c.mem base 1 = y := (ce 1 (by decide)).trans hy
  apply WP.ite (decide (rootV y * rootX y * rootX y = rootU y)) (by rw [← hvx, ← hu]; exact cz)
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kc.ctx hs) b (kc.keep.esi.trans hb) _ _ cx cy) fun t ⟨kt, tr⟩ => ?_
    exact ⟨kc.trans kt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kc.ctx hs) 11 12) fun d ⟨kd, de, dz⟩ => ?_)
    have kcd := kc.trans kd
    have dx : env d.mem base 0 = rootX y := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = y := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV y * rootX y * rootX y = 0 - rootU y))
      (by rw [ce 11 (by decide), ce 12 (by decide), hvx, hnu] at dz; exact dz)
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] (kcd.ctx hs))
        fun e ⟨ke, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX y * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = y := by rw [ve]; exact dy
      have kcde := kcd.trans ke
      refine WP.mono (sign_known (kcde.ctx hs) b (kcde.keep.esi.trans hb) _ _ ex ey)
        fun t ⟨kt, tr⟩ => ?_
      exact ⟨kcde.trans kt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kcd.trans kt, by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

theorem recoverPoint_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.X86.Ctx base s)
    (b : Bool) (hb : VG.Proof.X25519.X86.wd s.mem base 32 = signWord b) :
    WP isa recoverPoint s fun t => IKeep base s t ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec]
  refine WP.seq (WP.mono (recoverCandidate_ok hs) fun a ⟨ka, ax, ay, _, au, _, avx, anu⟩ => ?_)
  have ca := ka.ctx hs
  refine WP.seq (Wp.wp_ldm ca.edi (ca.inRW (by decide) (by decide)) fun c hc => WP.block_nil ?_)
  have kc : IKeep base a c := IKeep.of_counter hc
  have cb : c.gpr .esi = signWord b := by
    rw [hc.gpr]
    change VG.Proof.X25519.X86.wd a.mem base 32 = _
    rw [IKeep.word ka hs 32 (by decide), hb]
  refine WP.mono (recoverChecks_ok (kc.ctx ca) b cb (env s.mem base 1)
    (by rw [hc.mem]; exact ax) (by rw [hc.mem]; exact ay) (by rw [hc.mem]; exact au)
    (by rw [hc.mem]; exact avx) (by rw [hc.mem]; exact anu)) fun t ⟨kt, tr⟩ => ?_
  exact ⟨(ka.trans kc).trans (IKeep.of_field kt), tr⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointMul`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame`. -/
section

/-! Merged from `Proof.Ed25519.X86.PointMulBatch`. -/
section
/-! Rebuild and consume one batch of sixteen exact powers. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem pointMulBatch_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (scalar j : Nat) (p : Spec.Ed25519.Point) (hj : j < 32)
    (hcounter : VG.Proof.X25519.X86.wd s.mem x 28 = BitVec.ofNat 32 (j + 1))
    (hbits : ∀ i < 16, s.mem (VG.X86.addr x (7168 + (16 * j + i))) =
      BitVec.ofNat 8 (scalarBit scalar (16 * j + i)).toNat)
    (hcheckpoint : tablePoint s.mem x (1024 + 128 * j) = powerPoint p (16 * j))
    (hp : point (env s.mem x) 0 1 2 3 = after scalar p (16 * (j + 1)))
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa pointMulBatch s fun t => BatchKeep x s t ∧
      VG.Proof.X25519.X86.wd t.mem x 28 = BitVec.ofNat 32 j ∧ isa.eval .ne t = some (!decide (j = 0)) ∧
      point (env t.mem x) 0 1 2 3 = after scalar p (16 * j) ∧ env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (batchBegin_ok hc j hcounter) fun a ⟨ka, ba, ia, fa⟩ => ?_)
  have ca := ka.ctx hc
  have ea := counter28_env hc.fit fa
  refine WP.seq (WP.mono (prepareBatch_ok ca j hj ba (by rw [ea]; exact hd)) fun b ⟨kb, pb, tb, db⟩ => ?_)
  have cb := kb.ctx ca
  have ib := (kb.batch_index ca).trans ia
  have ks := ka.trans (BatchKeep.of_powers ca kb)
  have bits : ∀ i < 16, b.mem (VG.X86.addr x (7168 + (16 * j + i))) =
      BitVec.ofNat 8 (scalarBit scalar (16 * j + i)).toNat :=
    fun i hi => (ks.bit hc _ (by omega)).trans (hbits i hi)
  have tables : ∀ i < 16, tablePoint b.mem x (5120 + 128 * i) = powerPoint p (16 * j + i) := by
    intro i hi
    rw [tb i hi, ka.checkpoint hc j hj, hcheckpoint, ← powerPoint_add]
  have pointb : point (env b.mem x) 0 1 2 3 = after scalar p (16 * j + 16) := by
    rw [pb, ea, hp, Nat.mul_add, Nat.mul_one]
  refine WP.seq (WP.mono (accumulate16_ok cb scalar j p hj ib bits tables pointb db)
    fun c ⟨kc, pc, dc⟩ => ?_)
  have cc := kc.ctx cb
  have ic := (kc.word cb 28 (by decide)).trans ib
  refine WP.mono (batchTest_ok cc j hj ic) fun t ⟨kt, mt, zt⟩ => ?_
  refine ⟨ks.trans ((BatchKeep.of_ikeep cb kc).trans (BatchKeep.of_ikeep cc kt)), ?_, zt, ?_, ?_⟩
  · rw [mt]; exact ic
  · rw [mt]; exact pc
  · rw [mt]; exact dc

end VG.Proof.Ed25519.X86
end

/-! Complete point multiplication preserves API pointers and scalar bits. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulKeep (x : BitVec 32) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [VG.Proof.X25519.X86.sub x 24 7144] s.mem t.mem

theorem MulKeep.refl (x : BitVec 32) (s : State) : VG.Proof.Ed25519.X86.MulKeep x s s :=
  ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩
theorem MulKeep.ctx {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.MulKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s) : VG.Proof.Ed25519.X86.Ctx x t :=
  hc.keep h.edi h.wr
theorem MulKeep.trans {x : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.X86.MulKeep x s t) (k : VG.Proof.Ed25519.X86.MulKeep x t u) :
    VG.Proof.Ed25519.X86.MulKeep x s u := ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd,
      k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem MulKeep.of_powers {x : BitVec 32} {s t : State} {o n : Nat} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (h : PowersKeep x o n s t) (ho : 24 ≤ o) (hn : o + n ≤ 7168) : VG.Proof.Ed25519.X86.MulKeep x s t := by
  refine ⟨h.edi, h.esp, h.rd, h.wr, h.frame.sub ?_⟩
  intro r hr
  refine ⟨VG.Proof.X25519.X86.sub x 24 7144, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.X25519.X86.sub_sub hc.fit (by decide) (by decide) (by decide)
  · exact VG.Proof.X25519.X86.sub_sub hc.fit (by decide) (by decide) (by decide)
  · exact VG.Proof.X25519.X86.sub_sub hc.fit ho (by omega) (by omega)

theorem MulKeep.of_batch {x : BitVec 32} {s t : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (h : BatchKeep x s t) :
    VG.Proof.Ed25519.X86.MulKeep x s t := by
  refine ⟨h.edi, h.esp, h.rd, h.wr, h.frame.sub ?_⟩
  intro r hr
  refine ⟨VG.Proof.X25519.X86.sub x 24 7144, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.X25519.X86.sub_sub hc.fit (by decide) (by decide) (by decide)
  · exact VG.Proof.X25519.X86.sub_sub hc.fit (by decide) (by decide) (by decide)

theorem MulKeep.of_ikeep {x : BitVec 32} {s t : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (h : IKeep x s t) :
    VG.Proof.Ed25519.X86.MulKeep x s t := MulKeep.of_powers hc (PowersKeep.of_ikeep h 24 0) (by decide) (by decide)

theorem MulKeep.bit {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.MulKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (VG.X86.addr x (7168 + i)) = s.mem (VG.X86.addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (VG.Proof.X25519.X86.sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
    (Or.inr (by omega)) : (VG.Proof.X25519.X86.sub x (7168 + i) 1).Disjoint (VG.Proof.X25519.X86.sub x 24 7144)) _ (Region.contains_self _ _)

theorem MulKeep.word {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.MulKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (o : Nat) (ho : o + 4 ≤ 24) : VG.Proof.X25519.X86.wd t.mem x o = VG.Proof.X25519.X86.wd s.mem x o :=
  VG.Proof.X25519.X86.wd_frame1 h.frame hc.fit (by decide) (by omega) (Or.inl ho)

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointDecode`. -/
section

/-! Merged from `Proof.Ed25519.X86.DecodeY`. -/
section
/-! Merged from `Proof.Ed25519.X86.CanonicalY`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem canonicalY_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (hy : VG.Proof.X25519.X86.fe s.mem x 96 < 2 ^ 255) :
    WP isa (.block canonicalY) s fun t => FieldKeep x s t ∧
      env t.mem x = env s.mem x ∧ VG.Proof.X25519.X86.wd t.mem x 32 = VG.Proof.X25519.X86.wd s.mem x 32 ∧
      t.zf = some (decide (VG.Proof.X25519.X86.fe s.mem x 96 < Spec.X25519.P)) := by
  rw [canonicalY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86.setAcc_ok (s := s) 19) fun a ⟨ka, ma, aa⟩ => ?_
  rw [WP.block_append_iff]
  have ca := ka.ctx hc
  refine WP.mono (VG.Proof.X25519.X86.cols_ok ca (fun k => [.addM (96 + 4 * k)]) 8 (by decide)
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) (by rw [aa]; decide)) fun b ⟨kb, fb, vb, _⟩ => ?_
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [VG.Proof.X25519.X86.treads, List.mem_singleton] at hd; subst hd
    exact ⟨by omega_using [hk], .inl (by simp only [VG.Impl.X25519.X86.T]; omega_using [hk])⟩
  · rw [VG.Proof.X25519.X86.colv_addM]; have := VG.Proof.X25519.X86.wv_lt a.mem x (96 + 4 * k); omega_using [this]
  have nn : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv a.mem x [.addM (96 + 4 * k)]) 8 = VG.Proof.X25519.X86.fe s.mem x 96 := by
    rw [ma]; exact VG.Proof.X25519.X86.num_congr fun k _ => VG.Proof.X25519.X86.colv_addM _ _ _
  rw [nn, aa, show (19 : BitVec 32).toNat = 19 from rfl] at vb
  have vsum : VG.Proof.X25519.X86.fe b.mem x VG.Impl.X25519.X86.T = VG.Proof.X25519.X86.fe s.mem x 96 + 19 := by
    change VG.Proof.X25519.X86.fe b.mem x VG.Impl.X25519.X86.T + (2 ^ 32) ^ 8 * VG.Proof.X25519.X86.acc b = _ at vb
    have hb : VG.Proof.X25519.X86.acc b = 0 := by
      rcases Nat.eq_zero_or_pos (VG.Proof.X25519.X86.acc b) with h | h
      · exact h
      · have hh := Nat.mul_le_mul_left ((2 ^ 32) ^ 8) h
        omega_using [hy, vb, hh]
    rw [hb, Nat.mul_zero, Nat.add_zero] at vb
    omega_using [vb]
  have cb := kb.ctx ca
  refine Wp.wp_ldm cb.edi (cb.inRW (by decide) (by decide)) fun c hcl => ?_
  refine Wp.wp_shr (by decide) fun d hd _ => Wp.wp_test fun t ht zt => WP.block_nil ?_
  have kt : VG.Proof.X25519.X86.Keep b t := (VG.Proof.X25519.X86.updKeep hcl).trans ((VG.Proof.X25519.X86.updKeep hd).trans
    ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩)
  have mt : t.mem = b.mem := by rw [ht.mem, hd.mem, hcl.mem]
  have ff : Frame [VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 32] s.mem t.mem := by rw [mt]; rw [ma] at fb; exact fb
  have envt : env t.mem x = env s.mem x := by
    funext i
    apply congrArg VG.Proof.X25519.toFe
    have ii := i.isLt
    exact VG.Proof.X25519.X86.fe_frame1 ff hc.fit (by decide) (by simp only [offset]; omega_using [ii])
      (Or.inl (by simp only [offset, VG.Impl.X25519.X86.T]; omega_using [ii]))
  refine ⟨⟨ka.trans (kb.trans kt), VG.Proof.X25519.X86.frameWiden ff hc.fit (by decide) (by decide) (by decide)⟩,
    envt, VG.Proof.X25519.X86.wd_frame1 ff hc.fit (by decide) (by decide) (Or.inl (by decide)), ?_⟩
  have top := (VG.Proof.X25519.X86.fold_top (f := fun k => VG.Proof.X25519.X86.wv b.mem x (VG.Impl.X25519.X86.T + 4 * k)) fun _ _ => VG.Proof.X25519.X86.wv_lt _ _ _).2
  change VG.Proof.X25519.X86.fe b.mem x VG.Impl.X25519.X86.T / 2 ^ 255 = VG.Proof.X25519.X86.wv b.mem x (VG.Impl.X25519.X86.T + 28) / 2 ^ 31 at top
  rw [vsum] at top
  have flag : (d.gpr .eax).toNat = (VG.Proof.X25519.X86.fe s.mem x 96 + 19) / 2 ^ 255 := by
    rw [hd.gpr, VG.Proof.X25519.X86.shr31_toNat, hcl.gpr]
    exact top.symm
  rw [zt, BitVec.and_self]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  change (d.gpr .eax == 0) = true ↔ decide (VG.Proof.X25519.X86.fe s.mem x 96 < Spec.X25519.P) = true
  rw [beq_iff_eq, decide_eq_true_eq]
  have hz : d.gpr .eax = 0 ↔ (d.gpr .eax).toNat = 0 :=
    ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  rw [hz, flag]
  simp only [Spec.X25519.P]
  omega_using [hy]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem decodeY_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa (.block decodeY) s fun t => VG.Proof.Ed25519.X86.MulKeep x s t ∧
      VG.Proof.X25519.X86.fe t.mem x 96 = VG.Proof.X25519.X86.fe s.mem x 96 % 2 ^ 255 ∧
      VG.Proof.X25519.X86.wd t.mem x 32 = BitVec.ofNat 32 (VG.Proof.X25519.X86.fe s.mem x 96 / 2 ^ 255) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha => ?_
  refine Wp.wp_shr (by decide) fun b hb _ => ?_
  have kb : IKeep x s b := (IKeep.of_counter ha).trans (IKeep.of_counter hb)
  have cb := kb.ctx hc
  refine Wp.wp_stm cb.edi (cb.inW (by decide) (by decide)) fun c hcw => ?_
  have kc : ScalarKeep s c := ⟨by rw [hcw.gpr, kb.edi], by rw [hcw.gpr, kb.esp], hcw.rd.trans kb.rd, hcw.wr.trans kb.wr⟩
  have cc := kc.ctx hc
  have mc : c.mem = s.mem.writeW (VG.X86.addr x 32) (b.gpr .esi) := by rw [hcw.mem, hb.mem, ha.mem]
  have fc : Frame [VG.Proof.X25519.X86.sub x 32 4] s.mem c.mem := by
    rw [mc]; exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine Wp.wp_ldm cc.edi (cc.inRW (by decide) (by decide)) fun d hd => ?_
  refine Wp.wp_andi fun e he => ?_
  have ce := ((VG.Proof.X25519.X86.updKeep hd).trans (VG.Proof.X25519.X86.updKeep he)).ctx cc
  refine Wp.wp_stm ce.edi (ce.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have kt : VG.Proof.X25519.X86.Keep c t := ((VG.Proof.X25519.X86.updKeep hd).trans (VG.Proof.X25519.X86.updKeep he)).trans
    ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩
  have mt : t.mem = c.mem.writeW (VG.X86.addr x 124) (e.gpr .eax) := by rw [ht.mem, he.mem, hd.mem]
  have ft : Frame [VG.Proof.X25519.X86.sub x 124 4] c.mem t.mem := by
    rw [mt]; exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  have top : VG.Proof.X25519.X86.wd c.mem x 124 = VG.Proof.X25519.X86.wd s.mem x 124 := VG.Proof.X25519.X86.wd_frame1 fc hc.fit (by decide) (by decide) (Or.inr (by decide))
  have ev : (e.gpr .eax).toNat = VG.Proof.X25519.X86.wv s.mem x 124 % 2 ^ 31 := by
    rw [he.gpr, hd.gpr, VG.Proof.X25519.X86.low31_toNat]
    change VG.Proof.X25519.X86.wv c.mem x 124 % 2 ^ 31 = _
    rw [VG.Proof.X25519.X86.wv, top]
  have sv : b.gpr .esi = BitVec.ofNat 32 (VG.Proof.X25519.X86.fe s.mem x 96 / 2 ^ 255) := by
    apply BitVec.eq_of_toNat_eq
    rw [hb.gpr, VG.Proof.X25519.X86.shr31_toNat, ha.gpr, BitVec.toNat_ofNat]
    have hh := (VG.Proof.X25519.X86.fold_top (f := fun k => VG.Proof.X25519.X86.wv s.mem x (96 + 4 * k)) fun _ _ => VG.Proof.X25519.X86.wv_lt _ _ _).2
    change VG.Proof.X25519.X86.fe s.mem x 96 / 2 ^ 255 = VG.Proof.X25519.X86.wv s.mem x 124 / 2 ^ 31 at hh
    rw [hh]
    exact (Nat.mod_eq_of_lt (by have hw := VG.Proof.X25519.X86.wv_lt s.mem x 124; omega_using [hw])).symm
  refine ⟨⟨kt.edi.trans kc.edi, kt.esp.trans kc.esp, kt.rd.trans kc.rd, kt.wr.trans kc.wr,
    (VG.Proof.X25519.X86.frameWiden fc hc.fit (by decide) (by decide) (by decide)).trans
      (VG.Proof.X25519.X86.frameWiden ft hc.fit (by decide) (by decide) (by decide))⟩, ?_, ?_⟩
  · rw [mt, fe_last_write _ _ hc.fit, ev]
    have nl : VG.Proof.X25519.X86.num (fun j => VG.Proof.X25519.X86.wv c.mem x (96 + 4 * j)) 7 = VG.Proof.X25519.X86.num (fun j => VG.Proof.X25519.X86.wv s.mem x (96 + 4 * j)) 7 :=
      VG.Proof.X25519.X86.num_congr fun j hj => congrArg BitVec.toNat
        (VG.Proof.X25519.X86.wd_frame1 fc hc.fit (by decide) (by omega_using [hj]) (Or.inr (by omega_using [hj])))
    rw [nl]
    exact (VG.Proof.X25519.X86.fold_top (f := fun k => VG.Proof.X25519.X86.wv s.mem x (96 + 4 * k)) fun _ _ => VG.Proof.X25519.X86.wv_lt _ _ _).1.symm
  · rw [VG.Proof.X25519.X86.wd_frame1 ft hc.fit (by decide) (by decide) (Or.inl (by decide)), mc, VG.Proof.X25519.X86.wd_write_self, sv]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def decodeNumber (n : Nat) : Option Spec.Ed25519.Point :=
  if h : n % 2 ^ 255 < Spec.X25519.P then
    (Spec.Ed25519.recoverX ⟨n % 2 ^ 255, h⟩ (n / 2 ^ 255 == 1)).map
      (fun x => recoveredPoint x ⟨n % 2 ^ 255, h⟩)
  else none

theorem pointDecode_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa pointDecode s fun t => VG.Proof.Ed25519.X86.MulKeep x s t ∧ DecodeResult x (VG.Proof.Ed25519.X86.decodeNumber (VG.Proof.X25519.X86.fe s.mem x 96)) t := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.decodeY_ok hc) fun a ⟨ka, ya, ba⟩ => ?_
  have ca := ka.ctx hc
  refine WP.mono (VG.Proof.Ed25519.X86.canonicalY_ok ca (by rw [ya]; exact Nat.mod_lt _ (by decide))) fun b ⟨kb, eb, bb, zb⟩ => ?_
  have km := ka.trans (MulKeep.of_ikeep ca (IKeep.of_field kb))
  apply WP.ite (decide (VG.Proof.X25519.X86.fe s.mem x 96 % 2 ^ 255 < Spec.X25519.P)) (by rw [ya] at zb; exact zb)
  · intro hh
    have hh' := of_decide_eq_true hh
    have ey : env b.mem x 1 = (⟨VG.Proof.X25519.X86.fe s.mem x 96 % 2 ^ 255, hh'⟩ : Spec.X25519.Fe) := by
      rw [eb]
      change VG.Proof.X25519.toFe (VG.Proof.X25519.X86.fe a.mem x 96) = _
      rw [ya]
      apply Fin.ext
      exact Nat.mod_eq_of_lt hh'
    have ebits : VG.Proof.X25519.X86.wd b.mem x 32 = signWord (VG.Proof.X25519.X86.fe s.mem x 96 / 2 ^ 255 == 1) := by
      rw [bb, ba]
      have hn : VG.Proof.X25519.X86.fe s.mem x 96 / 2 ^ 255 ≤ 1 := by have := VG.Proof.X25519.X86.fe_lt s.mem x 96; omega_using [this]
      rcases (by omega_using [hn] : fe s.mem x 96 / 2 ^ 255 = 0 ∨ fe s.mem x 96 / 2 ^ 255 = 1) with h | h <;>
        rw [h] <;> rfl
    refine WP.mono (recoverPoint_ok (km.ctx hc) _ ebits) fun t ⟨kt, tr⟩ => ?_
    refine ⟨km.trans (MulKeep.of_ikeep (km.ctx hc) kt), ?_⟩
    rw [ey] at tr
    simpa only [VG.Proof.Ed25519.X86.decodeNumber, dite_eq_left hh'] using tr
  · intro hh
    have hh' := of_decide_eq_false hh
    refine WP.mono (recoverInvalid_ok b x) fun t ⟨kt, tr⟩ => ?_
    exact ⟨km.trans (MulKeep.of_ikeep (km.ctx hc) (IKeep.of_field kt)), by
      simpa only [VG.Proof.Ed25519.X86.decodeNumber, dite_eq_right hh'] using tr⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointMul`. -/
section

/-! Merged from `Proof.Ed25519.X86.PointMulInit`. -/
section
/-! Checkpoints, identity accumulator and the public batch count. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem constPoint_d (p : Spec.Ed25519.Point) (e : Env) : evalOps (constPointOps p) e 16 = e 16 := rfl

theorem pointMultiplyInit_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 32) (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (pointMultiplyInit count) s fun t => VG.Proof.Ed25519.X86.MulKeep x s t ∧
      VG.Proof.X25519.X86.wd t.mem x 28 = BitVec.ofNat 32 count ∧ point (env t.mem x) 0 1 2 3 = Spec.Ed25519.identity ∧
      (∀ j < count, tablePoint t.mem x (1024 + 128 * j) =
        powerPoint (point (env s.mem x) 0 1 2 3) (16 * j)) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (pointPowers_ok true hc 1024 count (by decide) (by omega) hn0 hn hd)
    fun a ⟨ka, ta, _, ha⟩ => ?_)
  have ca := ka.ctx hc
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) ca) fun b ⟨kb, eb⟩ => ?_)
  have cb := kb.ctx ca
  refine WP.mono (mulCounterInit_ok cb count) fun t ⟨kt, ft, it⟩ => ?_
  have et := counter28_env hc.fit ft
  have bt : BatchKeep x b t := BatchKeep.of_counter cb kt.edi kt.esp kt.rd kt.wr ft
  refine ⟨((MulKeep.of_powers hc ka (by decide) (by omega)).trans
    (MulKeep.of_ikeep ca (IKeep.of_field kb))).trans (MulKeep.of_batch cb bt), it, ?_, ?_, ?_⟩
  · rw [et, eb, constPoint_eval]
  · intro j hj
    rw [bt.checkpoint cb j (by omega), workspace_table (IKeep.of_field kb) ca _ (by omega) (by omega), ta j hj]
    rfl
  · rw [et, eb, VG.Proof.Ed25519.X86.constPoint_d, ha 16 (by decide), hd]

end VG.Proof.Ed25519.X86
end

/-! The whole scalar multiplication follows the specification's exact coordinates. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulInv (x : BitVec 32) (s₀ : State) (scalar count : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  keep : VG.Proof.Ed25519.X86.MulKeep x s₀ s
  counter : VG.Proof.X25519.X86.wd s.mem x 28 = BitVec.ofNat 32 n
  value : point (env s.mem x) 0 1 2 3 = after scalar p (16 * n)
  table : ∀ j < count, tablePoint s.mem x (1024 + 128 * j) = powerPoint p (16 * j)
  d : env s.mem x 16 = Spec.Ed25519.d

theorem multiplyLoop_ok {x : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.X86.Ctx x s₀)
    (scalar count : Nat) (p : Spec.Ed25519.Point) (hc0 : 0 < count) (hc32 : count ≤ 32)
    (hcounter : VG.Proof.X25519.X86.wd s₀.mem x 28 = BitVec.ofNat 32 count)
    (hbits : ∀ i < 16 * count, s₀.mem (VG.X86.addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat)
    (htable : ∀ j < count, tablePoint s₀.mem x (1024 + 128 * j) = powerPoint p (16 * j))
    (hp : point (env s₀.mem x) 0 1 2 3 = after scalar p (16 * count))
    (hd : env s₀.mem x 16 = Spec.Ed25519.d) :
    WP isa (.loop pointMulBatch .ne) s₀ fun t => VG.Proof.Ed25519.X86.MulKeep x s₀ t ∧
      point (env t.mem x) 0 1 2 3 = Spec.Ed25519.pointMul scalar p ∧ env t.mem x 16 = Spec.Ed25519.d := by
  apply WP.loop (fun n => VG.Proof.Ed25519.X86.MulInv x s₀ scalar count p n) (n := count)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < count := by have := h.bound; omega
    have cs := h.keep.ctx hc
    refine WP.mono (VG.Proof.Ed25519.X86.pointMulBatch_ok cs scalar j p (by omega) h.counter
      (fun i hi => (h.keep.bit hc _ (by omega)).trans (hbits _ (by omega)))
      (h.table j hj) h.value h.d) fun t ⟨kt, it, zt, pt, dt⟩ => ?_
    have kk := h.keep.trans (MulKeep.of_batch cs kt)
    have tt : ∀ k < count, tablePoint t.mem x (1024 + 128 * k) = powerPoint p (16 * k) :=
      fun k hk => (kt.checkpoint cs k (by omega)).trans (h.table k hk)
    by_cases hz : j = 0
    · subst j
      exact .inl ⟨by rw [zt]; rfl, kk, pt.trans (after_zero scalar p), dt⟩
    · exact .inr ⟨by rw [zt]; simp only [decide_eq_false hz]; rfl,
        j, by omega, ⟨by omega, by omega, kk, it, pt, tt, dt⟩⟩
  · exact ⟨hc0, Nat.le_refl _, MulKeep.refl _ _, hcounter, hp, htable, hd⟩

theorem pointMultiply_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (scalar count : Nat) (hc0 : 0 < count) (hc32 : count ≤ 32) (hscalar : scalar < 2 ^ (16 * count))
    (hbits : ∀ i < 16 * count, s.mem (VG.X86.addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (pointMultiply count) s fun t => VG.Proof.Ed25519.X86.MulKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = Spec.Ed25519.pointMul scalar (point (env s.mem x) 0 1 2 3) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.pointMultiplyInit_ok hc count hc0 hc32 hd) fun u ⟨ku, iu, pu, tu, du⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86.multiplyLoop_ok (ku.ctx hc) scalar count (point (env s.mem x) 0 1 2 3) hc0 hc32 iu
    (fun i hi => (ku.bit hc i (by omega)).trans (hbits i hi)) tu
    (pu.trans (after_top scalar (16 * count) _ hscalar).symm) du) fun t ⟨kt, pt, dt⟩ => ?_
  exact ⟨ku.trans kt, pt, dt⟩

end VG.Proof.Ed25519.X86

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CombLoop`. -/
section

/-!
# The comb's loop

The mixed additions (`addOddOps`, `addEvenOps`) add an affine cached point
exactly as the specification's `pointAdd`; `combNeg` negates the selected
entry under its sign's mask; after step `j`, the accumulator `A` (slots 0–3)
represents `[G + Σ_{i < j} d_{2i+1} 256^i]B` and `B` (slots 17–20) represents
`[G + Σ_{i < j} d_{2i} 256^i]B` (`Proof/Ed25519/CombDigits.lean`); at the end,
`16 A + B` is the scalar's multiple.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86 (sc)

/-! ## Frames -/

theorem MulKeep.of_field {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : FieldKeep x s t) :
    MulKeep x s t := MulKeep.of_ikeep hc (IKeep.of_field h)

theorem MulKeep.of_digit {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : DigitKeep x s t) :
    MulKeep x s t := by
  refine ⟨h.keep.edi, h.keep.esp, h.keep.rd, h.keep.wr, h.frame.sub fun r hr => ?_⟩
  rw [List.mem_singleton.mp hr]
  exact ⟨sub x 24 7144, List.mem_singleton_self _, sub_sub hc.fit (by omega) (by omega) (by omega)⟩

theorem MulKeep.of_sel {x : BitVec 32} {s t : State} (hc : Ctx x s) (k : Keep s t)
    (h : SelFrame x s.mem t.mem) : MulKeep x s t :=
  ⟨k.edi, k.esp, k.rd, k.wr, h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨sub x 24 7144, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · exact sub_sub hc.fit (by decide) (by decide) (by decide)
    · exact sub_sub hc.fit (by decide) (by decide) (by decide)⟩

theorem MulKeep.of_keepMem {x : BitVec 32} {s t : State} (k : Keep s t) (h : t.mem = s.mem) :
    MulKeep x s t := ⟨k.edi, k.esp, k.rd, k.wr, by rw [h]; exact Frame.refl _ _⟩

/-! ## The mixed additions -/

/-- What `addOddOps` and `addEvenOps` compute, from the accumulator's coordinates and the cached
entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> grind

theorem addOdd_formula (e : Env) :
    point (evalOps addOddOps e) 0 1 2 3 = mixedResult (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) := rfl

theorem addEven_formula (e : Env) :
    point (evalOps addEvenOps e) 17 18 19 20 =
      mixedResult (e 17) (e 18) (e 19) (e 20) (e 13) (e 14) (e 15) := rfl

theorem mixed_eval {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point}
    (hq : cachedAt e a b c = cache q) (p : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (e a) (e b) (e c) = Spec.Ed25519.pointAdd p q := by
  have h4 : e a = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e b = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e c = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  rw [h4, h5, h6, mixedResult_eq p q hz]

theorem addOdd_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (q : Spec.Ed25519.Point) (hq : cachedAt (env s.mem x) 4 5 6 = cache q) (hz : q.Z = 1) :
    WP isa (.block (fieldCode addOddOps)) s fun t =>
      FieldKeep x s t ∧ point (env t.mem x) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem x) 0 1 2 3) q ∧
      ∀ i : Slot, (4 ≤ i.val ∧ i.val < 8 ∨ 13 ≤ i.val) → env t.mem x i = env s.mem x i := by
  refine WP.mono (fieldCode_ok addOddOps hc) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  refine ⟨hk, (addOdd_formula _).trans (mixed_eval hq (point (env s.mem x) 0 1 2 3) hz),
    fun i hi => ?_⟩
  apply evalOps_unchanged
  intro op hop h
  have : ∀ op ∈ addOddOps, (fieldDest op).val < 4 ∨ (8 ≤ (fieldDest op).val ∧ (fieldDest op).val < 13) :=
    by decide
  have := this op hop
  rw [← h] at this
  omega

theorem addEven_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (q : Spec.Ed25519.Point) (hq : cachedAt (env s.mem x) 13 14 15 = cache q) (hz : q.Z = 1) :
    WP isa (.block (fieldCode addEvenOps)) s fun t =>
      FieldKeep x s t ∧ point (env t.mem x) 17 18 19 20 =
        Spec.Ed25519.pointAdd (point (env s.mem x) 17 18 19 20) q ∧
      ∀ i : Slot, (i.val < 8 ∨ 13 ≤ i.val ∧ i.val < 17 ∨ 21 ≤ i.val) →
        env t.mem x i = env s.mem x i := by
  refine WP.mono (fieldCode_ok addEvenOps hc) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  refine ⟨hk, (addEven_formula _).trans (mixed_eval hq (point (env s.mem x) 17 18 19 20) hz),
    fun i hi => ?_⟩
  apply evalOps_unchanged
  intro op hop h
  have : ∀ op ∈ addEvenOps, (8 ≤ (fieldDest op).val ∧ (fieldDest op).val < 13) ∨
      (17 ≤ (fieldDest op).val ∧ (fieldDest op).val < 21) := by decide
  have := this op hop
  rw [← h] at this
  omega

/-! ## The negations -/

/-- The negation, on the environment. -/
theorem neg_env (e : Env) (a b c : Slot) (sw : Bool) (hab : a ≠ b) (hc8 : c ≠ 8) (ha : a ≠ 8)
    (hb : b ≠ 8) (hac : a ≠ c) (hbc : b ≠ c) (hz : e 21 = 0) :
    cachedAt (swapsEnv [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e)) a b c =
      if sw then negCached (cachedAt e a b c) else cachedAt e a b c := by
  cases sw <;> simp [cachedAt, negCached, swapsEnv, swapEnv, evalOps, evalOp,
    hab, hc8, ha, hb, ha.symm, hb.symm, hac, hac.symm, hbc, hbc.symm, hz]

theorem neg_other (e : Env) (a b c : Slot) (sw : Bool) (i : Slot) (ha : i ≠ a) (hb : i ≠ b)
    (hc : i ≠ c) (h8 : i ≠ 8) :
    swapsEnv [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e) i = e i := by
  cases sw <;> simp [swapsEnv, swapEnv, evalOps, evalOp, Function.update_apply, ha, hb, hc, h8]

theorem combNeg_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (a b c : Slot) {sign : Nat}
    (hs1 : 928 ≤ sign) (hs2 : sign + 4 ≤ 8192) (sw : Bool) (hm : wd s.mem x sign = mask sw.toNat)
    (hdis : ∀ p ∈ [(a, b), (c, (8 : Slot))], p.1 ≠ p.2) :
    WP isa (.block (combNeg a b c sign)) s fun t => FieldKeep x s t ∧
      env t.mem x = swapsEnv [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] (env s.mem x)) := by
  rw [combNeg, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.sub 8 21 c] hc) fun u ⟨ku, vu⟩ => ?_
  have cu := ku.ctx hc
  rw [List.singleton_append]
  refine Wp.wp_ldm cu.edi (cu.inRW hs2 (by decide)) fun v hv => ?_
  have kv : FieldKeep x u v := FieldKeep.of_mem (updKeep hv) hv.mem
  have hmv : v.gpr .ecx = mask sw.toNat := by
    rw [hv.gpr]
    change wd u.mem x sign = _
    rw [wd_frame1 ku.frame hc.fit (by decide) hs2 (Or.inr (by omega))]
    exact hm
  refine WP.mono (swapFields_ok (kv.ctx cu) _ hdis sw hmv) fun t ⟨kt, _, vt⟩ =>
    ⟨(ku.trans kv).trans kt, ?_⟩
  rw [vt, hv.mem, vu]

/-! ## Four doublings -/

structure Double4Inv (x : BitVec 32) (s₀ : State) (n : Nat) (s : State) : Prop where
  lo : 1 ≤ n
  hi : n ≤ 4
  keep : IKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : point (env s.mem x) 0 1 2 3 = powerPoint (point (env s₀.mem x) 0 1 2 3) (4 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem x i = env s₀.mem x i

theorem double4_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa double4 s fun t => IKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = powerPoint (point (env s.mem x) 0 1 2 3) 4 ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.seq (Wp.wp_movi fun t ht => WP.block_nil ?_)
  refine WP.loop (M := isa) (Inv := Double4Inv x s) ?_ 4 t
    ⟨by decide, by decide, IKeep.of_counter ht, ht.gpr, ?_, ?_⟩
  · intro n u h
    have du : env u.mem x 16 = Spec.Ed25519.d := (h.high 16 (by decide)).trans hd
    refine WP.mono (doubleBody_ok (h.keep.ctx hc) h.lo (by omega_using [h.hi]) h.counter du)
      fun v ⟨kv, bv, zv, pv, high⟩ => ?_
    have kk := h.keep.trans kv
    have pp : point (env v.mem x) 0 1 2 3 =
        powerPoint (point (env s.mem x) 0 1 2 3) (4 - (n - 1)) := by
      exact pv.trans ((congrArg₂ Spec.Ed25519.pointAdd h.value h.value).trans
        (by rw [show 4 - (n - 1) = (4 - n) + 1 by omega_using [h.lo, h.hi]]; rfl))
    have hh : ∀ i : Slot, 16 ≤ i.val → env v.mem x i = env s.mem x i :=
      fun i hi => (high i hi).trans (h.high i hi)
    by_cases hn : n = 1
    · subst n
      exact .inl ⟨by rw [zv]; rfl, kk, pp, hh⟩
    · exact .inr ⟨by rw [zv]; simp only [show n - 1 ≠ 0 by omega_using [hn, h.lo], decide_false]; rfl,
        n - 1, by omega_using [h.lo], by omega_using [hn, h.lo], by omega_using [h.hi], kk, bv, pp, hh⟩
  · rw [ht.mem]; rfl
  · rw [ht.mem]; exact fun _ _ => rfl

/-! ## The loop -/

theorem digit_env {x : BitVec 32} {m m' : Mem} (hf : Frame [sub x 1024 136] m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) : env m' x = env m x := by
  funext i
  have hi := i.isLt
  exact congrArg VG.Proof.X25519.toFe (fe_frame fun k hk =>
    wd_frame1 hf hx (by decide) (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)))

theorem sel_env {x : BitVec 32} {m m' : Mem} (hf : SelFrame x m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (i : Slot) (hi : i.val < 4 ∨ (7 ≤ i.val ∧ i.val < 13) ∨ 16 ≤ i.val) : env m' x i = env m x i := by
  have hl := i.isLt
  exact congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)
    · exact sub_disj (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega))

theorem combNext_ok {s : State} {j : Nat} (hj : j < 32) (h : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 32)]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (j + 1) ∧ isa.eval .ne t = some (!decide (j + 1 = 32)) ∧
      t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mem = s.mem := by
  refine Wp.wp_addi fun u hu => Wp.wp_cmpi fun t ht _ zt => WP.block_nil ?_
  have e : u.gpr .esi = BitVec.ofNat 32 (j + 1) := by rw [hu.gpr, h, BitVec.ofNat_add]; rfl
  refine ⟨by rw [ht.gpr, e], ?_, by rw [ht.gpr, hu.other .edi (by decide)],
    by rw [ht.gpr, hu.other .esp (by decide)], by rw [ht.rd, hu.rd], by rw [ht.wr, hu.wr],
    by rw [ht.mem, hu.mem]⟩
  show t.zf.map (!·) = _
  rw [zt, e, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Wp.sub_beq (by omega) (by omega)]
  rfl

/-- The loop's invariant, after `j` steps. -/
structure CombInv (x : BitVec 32) (s₀ : State) (S j : Nat) (s : State) : Prop where
  bound : j ≤ 32
  keep : MulKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 j
  zero : env s.mem x 21 = 0
  d : env s.mem x 16 = Spec.Ed25519.d
  odd : Rep (point (env s.mem x) 0 1 2 3) ((combGVal + oddSumZ S j) • baseAff)
  even : Rep (point (env s.mem x) 17 18 19 20) ((combGVal + evenSumZ S j) • baseAff)

private theorem dis_odd : ∀ ab ∈ [((4 : Slot), (5 : Slot)), (6, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

private theorem dis_even : ∀ ab ∈ [((13 : Slot), (14 : Slot)), (15, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

theorem combStep_ok {x : BitVec 32} {s₀ s : State} (hc₀ : Ctx x s₀) {S j : Nat}
    (hb : ∀ q < 256, s₀.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (h : CombInv x s₀ S j s) (hj : j < 32) :
    WP isa combStep s fun t => isa.eval .ne t = some (!decide (j + 1 = 32)) ∧
      CombInv x s₀ S (j + 1) t := by
  have hc := h.keep.ctx hc₀
  have hfit := hc.fit
  have bits : ∀ q < 256, s.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) :=
    fun q hq => (h.keep.bit hc₀ q (by omega)).trans (hb q hq)
  rw [combStep]
  have no := nib_lt S (2 * j + 1)
  have ne := nib_lt S (2 * j)
  -- Both digits' masks.
  refine WP.seq (WP.mono (combDigits_ok hc hj h.counter bits) fun a ⟨ka, ma⟩ => ?_)
  have ca := ka.keep.ctx hc
  have ea : env a.mem x = env s.mem x := digit_env ka.frame hfit
  -- Both entries.
  refine WP.seq (WP.mono (combSelectFrom_ok (List.range 32) (fun k hk => List.mem_range.mp hk) ca
    (mag_lt no) (mag_lt ne) ⟨ma.oddMask, ma.evenMask⟩ (List.mem_range.mpr hj) hj
    (ka.keep.esi.trans h.counter)) fun b ⟨bo, be, kb, fb⟩ => ?_)
  have cb := kb.ctx ca
  have eb : ∀ i : Slot, (i.val < 4 ∨ (7 ≤ i.val ∧ i.val < 13) ∨ 16 ≤ i.val) →
      env b.mem x i = env s.mem x i := fun i hi => by rw [sel_env fb hfit i hi, ea]
  have sb : ∀ o, 1024 ≤ o → o + 4 ≤ 8192 → wd b.mem x o = wd a.mem x o := fun o h1 h2 =>
    wd_frame fb fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj (by omega) (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))
      · exact sub_disj (by omega) (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))
  -- The odd entry, negated for a negative digit, and added.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (combNeg_ok cb 4 5 6 (by decide) (by decide) (decide (nib S (2 * j + 1) < 8))
    (by rw [sb _ (by decide) (by decide)]; exact ma.oddSign) dis_odd) fun c ⟨kc, vc⟩ => ?_
  obtain ⟨qo, hqo, hqoz, hrqo⟩ := combEntry_ok j (nib S (2 * j + 1)) hj no
  have b21 : env b.mem x 21 = 0 := (eb 21 (by decide)).trans h.zero
  have co : cachedAt (env c.mem x) 4 5 6 = cache qo := by
    rw [vc, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      b21, bo, ← hqo]
    by_cases hlt : nib S (2 * j + 1) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  have ec : ∀ i : Slot, (i.val < 4 ∨ 9 ≤ i.val) → env c.mem x i = env b.mem x i := fun i hi => by
    rw [vc, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
  have cc := kc.ctx cb
  refine WP.mono (addOdd_ok cc qo co hqoz) fun d ⟨kd, dp, dh⟩ => ?_
  -- The even entry, negated for a negative digit, and added.
  have cd := kd.ctx cc
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have sd : wd d.mem x combEvenSign = wd b.mem x combEvenSign := by
    rw [wd_frame1 kd.frame hfit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 kc.frame hfit (by decide) (by decide) (Or.inr (by decide))]
  refine WP.mono (combNeg_ok cd 13 14 15 (by decide) (by decide) (decide (nib S (2 * j) < 8))
    (by rw [sd, sb _ (by decide) (by decide)]; exact ma.evenSign) dis_even) fun f ⟨kf, vf⟩ => ?_
  obtain ⟨qe, hqe, hqez, hrqe⟩ := combEntry_ok j (nib S (2 * j)) hj ne
  have ed : ∀ i : Slot, 13 ≤ i.val → env d.mem x i = env b.mem x i := fun i hi => by
    rw [dh i (Or.inr hi), ec i (Or.inr (by omega))]
  have fe' : cachedAt (env f.mem x) 13 14 15 = cache qe := by
    rw [vf, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ((ed 21 (by decide)).trans b21)]
    have : cachedAt (env d.mem x) 13 14 15 = cachedAt (env b.mem x) 13 14 15 := by
      simp only [cachedAt, ed 13 (by decide), ed 14 (by decide), ed 15 (by decide)]
    rw [this, be, ← hqe]
    by_cases hlt : nib S (2 * j) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  have ef : ∀ i : Slot, (i.val < 8 ∨ 16 ≤ i.val) → env f.mem x i = env d.mem x i := fun i hi => by
    rw [vf, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
  have cf := kf.ctx cd
  rw [WP.block_append_iff]
  refine WP.mono (addEven_ok cf qe fe' hqez) fun g ⟨kg, gp, gh⟩ => ?_
  have g19 : g.gpr .esi = BitVec.ofNat 32 j := by
    rw [kg.keep.esi, kf.keep.esi, kd.keep.esi, kc.keep.esi, kb.esi, ka.keep.esi, h.counter]
  refine WP.mono (combNext_ok hj g19) fun t ⟨t19, t8, tedi, tesp, trd, twr, tmem⟩ => ⟨t8, ?_⟩
  have kgt : MulKeep x g t := ⟨tedi, tesp, trd, twr, by rw [tmem]; exact Frame.refl _ _⟩
  have kst : MulKeep x s t := (((((((MulKeep.of_digit hc ka).trans (MulKeep.of_sel ca kb fb)).trans
    (MulKeep.of_field cb kc)).trans (MulKeep.of_field cc kd)).trans (MulKeep.of_field cd kf)).trans
    (MulKeep.of_field cf kg)).trans kgt)
  -- Slots 0–3 after the odd addition; 17–20 after the even one.
  have eg : ∀ i : Slot, i.val < 4 → env g.mem x i = env d.mem x i := fun i hi => by
    rw [gh i (Or.inl (by omega)), ef i (Or.inl (by omega))]
  have pc : point (env c.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
    simp only [point, ec 0 (by decide), ec 1 (by decide), ec 2 (by decide), ec 3 (by decide),
      eb 0 (by decide), eb 1 (by decide), eb 2 (by decide), eb 3 (by decide)]
  have pf : point (env f.mem x) 17 18 19 20 = point (env s.mem x) 17 18 19 20 := by
    simp only [point, ef 17 (by decide), ef 18 (by decide), ef 19 (by decide), ef 20 (by decide),
      ed 17 (by decide), ed 18 (by decide), ed 19 (by decide), ed 20 (by decide),
      eb 17 (by decide), eb 18 (by decide), eb 19 (by decide), eb 20 (by decide)]
  refine ⟨by omega, h.keep.trans kst, t19, ?_, ?_, ?_, ?_⟩
  · rw [tmem, gh 21 (Or.inr (Or.inr (by decide))), ef 21 (by decide), ed 21 (by decide)]
    exact b21
  · rw [tmem, gh 16 (Or.inr (Or.inl (by decide))), ef 16 (by decide), ed 16 (by decide),
      eb 16 (by decide)]
    exact h.d
  · have pg : point (env g.mem x) 0 1 2 3 = point (env d.mem x) 0 1 2 3 := by
      simp only [point, eg 0 (by decide), eg 1 (by decide), eg 2 (by decide), eg 3 (by decide)]
    rw [tmem, pg, dp, pc, oddSumZ, ← add_assoc, add_smul]
    exact pointAdd_rep h.odd hrqo
  · rw [tmem, gp, pf, evenSumZ, ← add_assoc, add_smul]
    exact pointAdd_rep h.even hrqe

/-! ## The start and the end -/

theorem combInit_ok {s : State} {x : BitVec 32} (hc : Ctx x s) :
    WP isa (.block combInit) s fun t => MulKeep x s t ∧ env t.mem x 21 = 0 ∧
      env t.mem x 16 = env s.mem x 16 ∧
      point (env t.mem x) 0 1 2 3 = combG ∧ point (env t.mem x) 17 18 19 20 = combG ∧
      t.gpr .esi = BitVec.ofNat 32 0 := by
  rw [combInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hc) fun a ⟨ka, va⟩ => ?_
  refine Wp.wp_movi fun t ht => WP.block_nil ?_
  refine ⟨(MulKeep.of_field hc ka).trans ⟨ht.other .edi (by decide), ht.other .esp (by decide), ht.rd,
      ht.wr, by rw [ht.mem]; exact Frame.refl _ _⟩, ?_, ?_, ?_, ?_, ht.gpr⟩ <;> rw [ht.mem, va] <;> rfl

theorem combFinish_ok {s : State} {x : BitVec 32} (hc : Ctx x s) {v w : ℤ}
    (hd : env s.mem x 16 = Spec.Ed25519.d)
    (ha : Rep (point (env s.mem x) 0 1 2 3) (v • baseAff))
    (hb : Rep (point (env s.mem x) 17 18 19 20) (w • baseAff)) :
    WP isa combFinish s fun t =>
      Rep (point (env t.mem x) 0 1 2 3) ((16 * v + w) • baseAff) ∧ MulKeep x s t := by
  rw [combFinish]
  refine WP.seq (WP.mono (double4_ok hc hd) fun b ⟨kb, bp, bh⟩ => ?_)
  have cb := kb.ctx hc
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] cb)
    fun c ⟨kc, vc⟩ => ?_
  have cc := kc.ctx cb
  have cd : env c.mem x 16 = Spec.Ed25519.d := by
    rw [vc, show evalOps [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] (env b.mem x) 16 =
      env b.mem x 16 from rfl, bh 16 (by decide), hd]
  refine WP.mono (pointAdd_ok cc cd) fun t ⟨kt, tp, _⟩ => ?_
  refine ⟨?_, ((MulKeep.of_ikeep hc kb).trans (MulKeep.of_field cb kc)).trans (MulKeep.of_field cc kt)⟩
  have p0 : point (env c.mem x) 0 1 2 3 = point (env b.mem x) 0 1 2 3 := by rw [vc]; rfl
  have p4 : point (env c.mem x) 4 5 6 7 = point (env s.mem x) 17 18 19 20 := by
    rw [vc]
    show point (env b.mem x) 17 18 19 20 = _
    simp only [point, bh 17 (by decide), bh 18 (by decide), bh 19 (by decide), bh 20 (by decide)]
  rw [tp, p0, p4, bp, ← zsmul_16]
  have h4 := powerPoint_rep ha 4
  rw [show (2 ^ 4 : Nat) = 16 from rfl] at h4
  exact pointAdd_rep h4 hb

theorem combMultiply_ok {s : State} {x : BitVec 32} (hc : Ctx x s) {S : Nat} (hS : S < 2 ^ 256)
    (hb : ∀ q < 256, s.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa combMultiply s fun t =>
      Rep (point (env t.mem x) 0 1 2 3) (S • baseAff) ∧ MulKeep x s t := by
  rw [combMultiply]
  refine WP.seq (WP.mono (combInit_ok hc) fun b ⟨kb, bz, bd, bp, bq, b19⟩ => ?_)
  have hg : Rep combG (((combGVal : ℤ) + 0) • baseAff) := by
    rw [add_zero, natCast_zsmul]; exact combG_ok
  have init : CombInv x s S 0 b :=
    ⟨by decide, kb, b19, bz, bd.trans hd, by rw [bp]; exact hg, by rw [bq]; exact hg⟩
  have hl : WP isa (.loop combStep .ne) b fun t => CombInv x s S 32 t := by
    apply WP.loop (fun n t => CombInv x s S (32 - n) t ∧ 0 < n ∧ n ≤ 32) (n := 32)
    · intro n t ⟨ht, hn0, hn⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      refine WP.mono (combStep_ok hc hb ht (by omega)) fun u ⟨u8, hu⟩ => ?_
      by_cases hk : k = 0
      · subst hk
        exact Or.inl ⟨by rw [u8]; rfl, hu⟩
      · refine Or.inr ⟨by rw [u8, show 32 - (k + 1) + 1 = 32 - k by omega,
          decide_eq_false (show 32 - k ≠ 32 by omega)]; rfl, k, by omega, ?_, by omega, by omega⟩
        rw [show 32 - k = 32 - (k + 1) + 1 by omega]; exact hu
    · exact ⟨init, by decide, by decide⟩
  refine WP.seq (WP.mono hl fun t ht => ?_)
  refine WP.mono (combFinish_ok (ht.keep.ctx hc) ht.d ht.odd ht.even) fun u ⟨hu, ku⟩ =>
    ⟨?_, ht.keep.trans ku⟩
  rw [comb_total hS, natCast_zsmul] at hu
  exact hu

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyLit`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointCTLit`. -/
section

/-! The point arithmetic and the inversion chain as literals
(`materialize_value`, `materialize_code`), which the literals of the code
that contains them read rather than build each field multiplication again. -/
namespace VG.Impl.Ed25519.X86

materialize_value pointAdd
materialize_value pointDouble
materialize_code power250
materialize_code VG.Impl.Ed25519.X86.invert
materialize_code VG.Impl.Ed25519.X86.rootPower

end VG.Impl.Ed25519.X86

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
materialize_code pointEncode
materialize_code accumulate16
materialize_code powersBody16 := powersBody 1024 16 true
materialize_code powersBody32 := powersBody 1024 32 true
materialize_code powersBodyLocal := powersBody 5120 16 false
materialize_code checkpointBlock := (.block loadCheckpoint : Prog isa)
materialize_code restoreBlock := (.block restorePoint : Prog isa)
materialize_code identityBlock := (.block (constPoint Spec.Ed25519.identity) : Prog isa)
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport`. -/
section

/-! Relational trace helpers for public workspace counters. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86

def regsTaint (rs : List Reg) : VG.X86.Taint.T := { regs := .ofList rs, flags := false }

theorem regsTaint_wf (rs : List Reg) (s : State) : VG.X86.Taint.Wf (VG.Proof.Ed25519.X86.regsTaint rs) s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (by cases h),
    fun _ h => (by cases h), fun h => (by cases h), fun _ h => (by cases h)⟩

theorem regsTaint_agree {rs : List Reg} {s t : State}
    (h : ∀ r ∈ rs, s.gpr r = t.gpr r) : VG.X86.Taint.Agree (VG.Proof.Ed25519.X86.regsTaint rs) s t :=
  ⟨⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => (by cases h)⟩,
    fun h => absurd rfl h, VG.Proof.Ed25519.X86.regsTaint_wf rs s, VG.Proof.Ed25519.X86.regsTaint_wf rs t,
    fun _ h => (by cases h), fun _ h => (by cases h), fun h => (by cases h),
    fun n _ h => (Nat.not_lt_zero n h).elim⟩

def pointTaint (o : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.edi], flags := false, lens := [0, 8192], bases := [(.edi, 1, 0)],
    slots := [(1, o, 4)] }

structure PointCTCtx (x : BitVec 32) (s : State) : Prop where
  ctx : VG.Proof.Ed25519.X86.Ctx x s
  lengths : List.Forall₂ (fun r l => l ≤ r.len) s.wr [0, 8192]
  separate : s.wr.Pairwise Region.Disjoint
  fits : ∀ r ∈ s.wr, r.base.toNat + r.len ≤ 2 ^ 32
  region : VG.X86.Taint.region s 1 = VG.Proof.X25519.X86.scR 8192 x

theorem PointCTCtx.keep {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.PointCTCtx x s)
    (he : t.gpr .edi = s.gpr .edi) (hw : t.wr = s.wr) : VG.Proof.Ed25519.X86.PointCTCtx x t :=
  ⟨h.ctx.keep he hw, hw ▸ h.lengths, hw ▸ h.separate, hw ▸ h.fits,
    (congrArg (fun wr => wr.getD 1 ⟨0, 0⟩) hw).trans h.region⟩

theorem pointTaint_wf {x : BitVec 32} {s : State} (h : VG.Proof.Ed25519.X86.PointCTCtx x s) (o : Nat) :
    VG.X86.Taint.Wf (VG.Proof.Ed25519.X86.pointTaint o) s := by
  apply VG.X86.Taint.Wf.entry rfl rfl
  refine ⟨fun _ => ⟨h.lengths, h.separate, h.fits⟩, ?_, fun _ hh => (by cases hh),
    fun hh => (by cases hh), fun _ hh => (by cases hh)⟩
  intro p hp
  simp only [VG.Proof.Ed25519.X86.pointTaint, List.mem_singleton] at hp
  subst p
  rw [h.ctx.edi, VG.Proof.X25519.X86.addr_zero, h.region]

theorem pointTaint_agree {x : BitVec 32} {s t : State} {o : Nat}
    (hs : VG.Proof.Ed25519.X86.PointCTCtx x s) (ht : VG.Proof.Ed25519.X86.PointCTCtx x t) (hw : s.wr = t.wr)
    (ho : o + 4 ≤ 8192) (hv : VG.Proof.X25519.X86.wd s.mem x o = VG.Proof.X25519.X86.wd t.mem x o) :
    VG.X86.Taint.Agree (VG.Proof.Ed25519.X86.pointTaint o) s t := by
  refine ⟨⟨?_, fun h => (by cases h)⟩, fun _ => hw, VG.Proof.Ed25519.X86.pointTaint_wf hs o, VG.Proof.Ed25519.X86.pointTaint_wf ht o,
    ?_, ?_, fun h => (by cases h), fun n _ h => (Nat.not_lt_zero n h).elim⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86.pointTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact hs.ctx.edi.trans ht.ctx.edi.symm
  · intro sl hsl
    simp only [VG.Proof.Ed25519.X86.pointTaint, List.mem_singleton] at hsl
    subst sl; exact ho
  · intro sl hsl k hlo hhi
    simp only [VG.Proof.Ed25519.X86.pointTaint, List.mem_singleton] at hsl
    subst sl
    change o ≤ k at hlo
    change k < o + 4 at hhi
    obtain ⟨j, hj, rfl⟩ : ∃ j < 4, k = o + j := ⟨k - o, by omega, by omega⟩
    simp only [VG.X86.Taint.byteAddr, hs.region, ht.region]
    have hx := hs.ctx.fit
    rw [← addr_eq (by omega : x.toNat + (o + j) < 2 ^ 32),
      addr_offset (x := x) (o := o) (d := j) (by omega),
      Mem.readW_byte s.mem _ hj, Mem.readW_byte t.mem _ hj]
    exact congrArg (BitVec.extractLsb' (8 * j) 8) hv

theorem ctWithRuns {P Q F₁ F₂ : State → State → Prop} {c : Prog isa}
    (h : RelCT isa P c Q) (hw : ∀ s t, P s t → WP isa c s (F₁ s) ∧ WP isa c t (F₂ t)) :
    RelCT isa P c (fun s t => Q s t ∧ ∃ a b, P a b ∧ F₁ a s ∧ F₂ b t) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨he, hq⟩ := h _ _ _ _ _ _ hp es et
  obtain ⟨⟨_, u, eu, hu⟩, ⟨_, v, ev, hv⟩⟩ := hw s t hp
  obtain ⟨-, rfl⟩ := Exec.det es eu
  obtain ⟨-, rfl⟩ := Exec.det et ev
  exact ⟨he, hq, s, t, hp, hu, hv⟩

theorem ctExecBlock_append {xs ys : List Instr} {s t : State} {tr : List Leak}
    (h : Exec isa (.block (xs ++ ys)) s tr t) :
    Exec isa (.seq (.block xs) (.block ys)) s tr t := by
  rw [Exec.block_iff, execBlock_append] at h
  obtain ⟨⟨u, tx⟩, hu, ht⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨v, ty⟩, hv, he⟩ := Option.map_eq_some_iff.mp ht
  cases he
  exact .seq (.block hu) (.block hv)

theorem ctBlockAppend {P R Q : State → State → Prop} {xs ys : List Instr}
    (hx : RelCT isa P (.block xs) R) (hy : RelCT isa R (.block ys) Q) :
    RelCT isa P (.block (xs ++ ys)) Q :=
  fun _ _ _ _ _ _ hp ex ey => VG.RelCT.seq hx hy _ _ _ _ _ _ hp
    (VG.Proof.Ed25519.X86.ctExecBlock_append ex) (VG.Proof.Ed25519.X86.ctExecBlock_append ey)

theorem ctTaintRegs {τ : VG.X86.Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s t, P s t → VG.X86.Taint.Agree τ s t) (rs : List Reg)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : ((taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ'.regs) = some true) :
    RelCT isa P c (fun s t => ∀ r ∈ rs, s.gpr r = t.gpr r) := by
  intro s t ts tt s' t' hp' es et
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨he, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hp') es et
  exact ⟨he, fun r hr => ha.rf.1 r (RegSet.mem_of_subset hs (RegSet.mem_ofList.mpr hr))⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CombCT`. -/
section

/-! The comb has a public trace: its loops' counters (`esi`) are public, every address is the
workspace pointer `edi` plus a constant or `8 esi`, and the digits only reach masks.

The selection from the 32 tables (`combSelectFrom`) is most of the comb's code, 32 blocks of
immediates. Rather than have the kernel analyse each of their instructions, its analysis is
proven for any immediates (`selFrom_ok`): every instruction of a selection only moves an
immediate or a register into `eax`, `ebx`, `edx` or `ebp`, combines them with words at `edi`,
or stores them at `edi`, so `esi` and `edi` stay public. The rest of the comb is evaluated
(`taint_decide`), its parts joined with the taint `selL` (only `esi` and `edi` public) by the
rules of `Taint.check` (`CheckOk.seq`, `CheckOk.loop`). -/
namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (sc)

/-! ## Joining checks -/

/-- The check of `c` from `τ` with the hint `h` succeeds, with a taint that satisfies `P`. -/
def CheckOk (τ : VG.X86.Taint.T) (c : Prog isa) (h : VG.Taint.Hint VG.X86.Taint.T) (P : VG.X86.Taint.T → Prop) :
    Prop :=
  ∃ τ', taint.check τ c h = some τ' ∧ P τ'

theorem CheckOk.of_map {τ : VG.X86.Taint.T} {c : Prog isa} {h : VG.Taint.Hint VG.X86.Taint.T}
    {p : VG.X86.Taint.T → Bool} (e : (taint.check τ c h).map p = some true) :
    VG.Proof.Ed25519.X86.CheckOk τ c h (p · = true) := by
  obtain ⟨τ', h₁, h₂⟩ := Option.map_eq_some_iff.mp e
  exact ⟨τ', h₁, h₂⟩

theorem CheckOk.seq {τ m : VG.X86.Taint.T} {c₁ c₂ : Prog isa} {h₁ h₂ : VG.Taint.Hint VG.X86.Taint.T}
    {P : VG.X86.Taint.T → Prop} (o₁ : VG.Proof.Ed25519.X86.CheckOk τ c₁ h₁ (taint.le m · = true)) (o₂ : VG.Proof.Ed25519.X86.CheckOk m c₂ h₂ P) :
    VG.Proof.Ed25519.X86.CheckOk τ (.seq c₁ c₂) (.seq m h₁ h₂) P := by
  obtain ⟨τ₁, e₁, l₁⟩ := o₁
  obtain ⟨τ₂, e₂, p₂⟩ := o₂
  refine ⟨τ₂, ?_, p₂⟩
  show (taint.check τ c₁ h₁).bind (fun τ' => if taint.le m τ' then taint.check m c₂ h₂ else none) =
    some τ₂
  simp only [e₁, Option.bind_some, l₁, ↓reduceIte, e₂]

theorem CheckOk.loop {τ σ : VG.X86.Taint.T} {body : Prog isa} {c : Cond} {h : VG.Taint.Hint VG.X86.Taint.T}
    {P : VG.X86.Taint.T → Prop} (hl : taint.le σ τ = true)
    (o : VG.Proof.Ed25519.X86.CheckOk σ body h fun σ' => taint.le σ σ' = true ∧ taint.condPub σ' c = true ∧ P σ') :
    VG.Proof.Ed25519.X86.CheckOk τ (.loop body c) (.loop σ h) P := by
  obtain ⟨σ', e, l, hc, p⟩ := o
  refine ⟨σ', ?_, p⟩
  show (if taint.le σ τ then (taint.check σ body h).bind fun σ' =>
    if taint.le σ σ' && taint.condPub σ' c then some σ' else none else none) = some σ'
  simp only [hl, ↓reduceIte, e, Option.bind_some, l, hc, Bool.and_self]

theorem CheckOk.ite {τ : VG.X86.Taint.T} {c : Cond} {t e : Prog isa} {h₁ h₂ : VG.Taint.Hint VG.X86.Taint.T}
    {P : VG.X86.Taint.T → Prop} (hc : taint.condPub τ c = true) (o₁ : VG.Proof.Ed25519.X86.CheckOk τ t h₁ P)
    (o₂ : VG.Proof.Ed25519.X86.CheckOk τ e h₂ P) (hm : ∀ a b, P a → P b → P (taint.meet a b)) :
    VG.Proof.Ed25519.X86.CheckOk τ (.ite c t e) (.ite h₁ h₂) P := by
  obtain ⟨τ₁, e₁, p₁⟩ := o₁
  obtain ⟨τ₂, e₂, p₂⟩ := o₂
  refine ⟨taint.meet τ₁ τ₂, ?_, hm _ _ p₁ p₂⟩
  show (if taint.condPub τ c then (taint.check τ t h₁).bind fun τ₁ =>
    (taint.check τ e h₂).map fun τ₂ => taint.meet τ₁ τ₂ else none) = some (taint.meet τ₁ τ₂)
  simp only [hc, ↓reduceIte, e₁, Option.bind_some, e₂, Option.map_some]

/-! ## The selection, for any immediates -/

/-- A taint that knows only which registers are public, and whether the flags are. -/
def selT (rs : RegSet Reg) (fl : Bool) : VG.X86.Taint.T := { regs := rs, flags := fl }

/-- The taint of the comb's loop: `esi` and `edi` public. -/
def selL : VG.X86.Taint.T := VG.Proof.Ed25519.X86.selT (.ofList [.esi, .edi]) false

/-- What a selection keeps: only registers known, `esi` and `edi` public. -/
def SelInv (τ : VG.X86.Taint.T) : Prop := ∃ rs fl, τ = VG.Proof.Ed25519.X86.selT rs fl ∧ Reg.esi ∈ rs ∧ Reg.edi ∈ rs

theorem subset_esi_edi {rs : RegSet Reg} (h₁ : Reg.esi ∈ rs) (h₂ : Reg.edi ∈ rs) :
    (RegSet.ofList [Reg.esi, .edi]).subset rs = true := by
  rw [RegSet.subset_eq, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  rw [RegSet.mem_iff] at h₁ h₂
  have hb : ∀ i < 8, (RegSet.ofList [Reg.esi, .edi]).bits.testBit i = true →
      i = RegIdx.idx Reg.esi ∨ i = RegIdx.idx Reg.edi := by decide
  cases hi : (RegSet.ofList [Reg.esi, .edi]).bits.testBit i
  · rfl
  · rcases Nat.lt_or_ge i 8 with h8 | h8
    · rcases hb i h8 hi with rfl | rfl
      · rw [h₁]; rfl
      · rw [h₂]; rfl
    · have : (RegSet.ofList [Reg.esi, .edi]).bits < 2 ^ i :=
        Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h8)
      rw [Nat.testBit_lt_two_pow this] at hi
      cases hi

theorem SelInv.le {τ : VG.X86.Taint.T} (h : VG.Proof.Ed25519.X86.SelInv τ) {fl : Bool} (hf : fl = true → τ.flags = true) :
    taint.le (VG.Proof.Ed25519.X86.selT (.ofList [.esi, .edi]) fl) τ = true := by
  obtain ⟨rs, g, rfl, h₁, h₂⟩ := h
  show VG.X86.Taint.leK _ _ = true
  cases fl
  · simp only [VG.X86.Taint.leK, VG.Proof.Ed25519.X86.selT, VG.Proof.Ed25519.X86.subset_esi_edi h₁ h₂]; rfl
  · have hg : g = true := hf rfl
    subst hg
    simp only [VG.X86.Taint.leK, VG.Proof.Ed25519.X86.selT, VG.Proof.Ed25519.X86.subset_esi_edi h₁ h₂]; rfl

theorem SelInv.meet {a b : VG.X86.Taint.T} (ha : VG.Proof.Ed25519.X86.SelInv a) (hb : VG.Proof.Ed25519.X86.SelInv b) : VG.Proof.Ed25519.X86.SelInv (taint.meet a b) := by
  obtain ⟨ra, fa, rfl, ha₁, ha₂⟩ := ha
  obtain ⟨rb, fb, rfl, hb₁, hb₂⟩ := hb
  exact ⟨ra.inter rb, fa && fb, rfl, RegSet.mem_inter.mpr ⟨ha₁, hb₁⟩,
    RegSet.mem_inter.mpr ⟨ha₂, hb₂⟩⟩

/-- The instructions of a selection, for any immediates and displacements. -/
def SelInstr (i : Instr) : Prop :=
  (∃ x, i = .mov .eax (.imm x)) ∨ i = .mov .ebx (.imm 0) ∨ i = .mov .ebp (.imm 0) ∨
    i = .mov .edx (.reg .eax) ∨ (∃ o, i = .alu .and .eax (.mem (sc o))) ∨
    (∃ o, i = .alu .and .edx (.mem (sc o))) ∨ i = .alu .or .ebx (.reg .eax) ∨
    i = .alu .or .ebp (.reg .edx) ∨ (∃ o, i = .store (sc o) .ebx) ∨ (∃ o, i = .store (sc o) .ebp)

theorem setK_inv {rs : RegSet Reg} {fl p : Bool} {d : Reg} (hd₁ : d ≠ .esi) (hd₂ : d ≠ .edi)
    (h₁ : Reg.esi ∈ rs) (h₂ : Reg.edi ∈ rs) :
    Reg.esi ∈ VG.X86.Taint.setK (VG.Proof.Ed25519.X86.selT rs fl) d p ∧ Reg.edi ∈ VG.X86.Taint.setK (VG.Proof.Ed25519.X86.selT rs fl) d p := by
  cases p
  · exact ⟨RegSet.mem_erase.mpr ⟨hd₁.symm, h₁⟩, RegSet.mem_erase.mpr ⟨hd₂.symm, h₂⟩⟩
  · exact ⟨RegSet.mem_insert.mpr (Or.inr h₁), RegSet.mem_insert.mpr (Or.inr h₂)⟩

theorem step_sel {τ : VG.X86.Taint.T} {i : Instr} (hi : VG.Proof.Ed25519.X86.SelInstr i) (h : VG.Proof.Ed25519.X86.SelInv τ) :
    ∃ τ', taint.step τ i = some τ' ∧ VG.Proof.Ed25519.X86.SelInv τ' := by
  obtain ⟨rs, fl, rfl, h₁, h₂⟩ := h
  have hd : rs.mem .edi = true := h₂
  rcases hi with ⟨x, rfl⟩ | rfl | rfl | rfl | ⟨o, rfl⟩ | ⟨o, rfl⟩ | rfl | rfl | ⟨o, rfl⟩ | ⟨o, rfl⟩
  · exact ⟨_, rfl, _, _, rfl, VG.Proof.Ed25519.X86.setK_inv (d := .eax) (by decide) (by decide) h₁ h₂⟩
  · exact ⟨_, rfl, _, _, rfl, VG.Proof.Ed25519.X86.setK_inv (d := .ebx) (by decide) (by decide) h₁ h₂⟩
  · exact ⟨_, rfl, _, _, rfl, VG.Proof.Ed25519.X86.setK_inv (d := .ebp) (by decide) (by decide) h₁ h₂⟩
  · exact ⟨_, rfl, _, _, rfl, VG.Proof.Ed25519.X86.setK_inv (d := .edx) (by decide) (by decide) h₁ h₂⟩
  · have e : taint.step (VG.Proof.Ed25519.X86.selT rs fl) (.alu .and .eax (.mem (sc o))) =
        some (VG.Proof.Ed25519.X86.selT (VG.X86.Taint.setK (VG.Proof.Ed25519.X86.selT rs fl) .eax (VG.X86.Taint.pub (VG.Proof.Ed25519.X86.selT rs fl) .eax && false && true))
          (VG.X86.Taint.pub (VG.Proof.Ed25519.X86.selT rs fl) .eax && false && true)) := by
      show (bif true && rs.mem .edi then _ else none) = _
      rw [hd]; rfl
    exact ⟨_, e, _, _, rfl, VG.Proof.Ed25519.X86.setK_inv (d := .eax) (by decide) (by decide) h₁ h₂⟩
  · have e : taint.step (VG.Proof.Ed25519.X86.selT rs fl) (.alu .and .edx (.mem (sc o))) =
        some (VG.Proof.Ed25519.X86.selT (VG.X86.Taint.setK (VG.Proof.Ed25519.X86.selT rs fl) .edx (VG.X86.Taint.pub (VG.Proof.Ed25519.X86.selT rs fl) .edx && false && true))
          (VG.X86.Taint.pub (VG.Proof.Ed25519.X86.selT rs fl) .edx && false && true)) := by
      show (bif true && rs.mem .edi then _ else none) = _
      rw [hd]; rfl
    exact ⟨_, e, _, _, rfl, VG.Proof.Ed25519.X86.setK_inv (d := .edx) (by decide) (by decide) h₁ h₂⟩
  · exact ⟨_, rfl, _, _, rfl, VG.Proof.Ed25519.X86.setK_inv (d := .ebx) (by decide) (by decide) h₁ h₂⟩
  · exact ⟨_, rfl, _, _, rfl, VG.Proof.Ed25519.X86.setK_inv (d := .ebp) (by decide) (by decide) h₁ h₂⟩
  · refine ⟨VG.Proof.Ed25519.X86.selT rs fl, ?_, rs, fl, rfl, h₁, h₂⟩
    show (bif rs.mem .edi then _ else none) = _
    rw [hd]
    cases VG.X86.Taint.pub (VG.Proof.Ed25519.X86.selT rs fl) .ebx <;> rfl
  · refine ⟨VG.Proof.Ed25519.X86.selT rs fl, ?_, rs, fl, rfl, h₁, h₂⟩
    show (bif rs.mem .edi then _ else none) = _
    rw [hd]
    cases VG.X86.Taint.pub (VG.Proof.Ed25519.X86.selT rs fl) .ebp <;> rfl

theorem checkBlock_sel {is : List Instr} (hi : ∀ i ∈ is, VG.Proof.Ed25519.X86.SelInstr i) {τ : VG.X86.Taint.T}
    (h : VG.Proof.Ed25519.X86.SelInv τ) : ∃ τ', taint.checkBlock τ is = some τ' ∧ VG.Proof.Ed25519.X86.SelInv τ' := by
  induction is generalizing τ with
  | nil => exact ⟨τ, rfl, h⟩
  | cons i is ih =>
    obtain ⟨τ₁, e₁, h₁⟩ := VG.Proof.Ed25519.X86.step_sel (hi i (List.mem_cons_self ..)) h
    obtain ⟨τ₂, e₂, h₂⟩ := ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) h₁
    refine ⟨τ₂, ?_, h₂⟩
    show (taint.step τ i).bind (fun τ' => taint.checkBlock τ' is) = some τ₂
    rw [e₁, Option.bind_some, e₂]

theorem selectField_sel (vs : List Spec.X25519.Fe) (o e : Nat) :
    ∀ i ∈ selectField vs o e, VG.Proof.Ed25519.X86.SelInstr i := by
  intro i hi
  simp only [selectField, selectWord, List.mem_flatMap, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  obtain ⟨w, -, hi⟩ := hi
  rcases hi with ((rfl | rfl) | ⟨k, -, hk⟩) | (rfl | rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · unfold selectCand at hk
    split at hk
    · cases hk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))))))))

theorem combSelect_sel (j : Nat) : ∀ i ∈ combSelect j, VG.Proof.Ed25519.X86.SelInstr i := by
  intro i hi
  simp only [combSelect, List.mem_append] at hi
  rcases hi with (h | h) | h <;> exact VG.Proof.Ed25519.X86.selectField_sel _ _ _ i h

/-- The hint of `combSelectFrom`: after each comparison, `esi`, `edi` and the flags public. -/
def selHint : List Nat → VG.Taint.Hint VG.X86.Taint.T
  | [] => .block []
  | _ :: js => .seq (VG.Proof.Ed25519.X86.selT (.ofList [.esi, .edi]) true) (.block []) (.ite (.block []) (VG.Proof.Ed25519.X86.selHint js))

theorem selFrom_ok (js : List Nat) {τ : VG.X86.Taint.T} (h : VG.Proof.Ed25519.X86.SelInv τ) :
    VG.Proof.Ed25519.X86.CheckOk τ (combSelectFrom js) (VG.Proof.Ed25519.X86.selHint js) VG.Proof.Ed25519.X86.SelInv := by
  induction js generalizing τ with
  | nil => exact ⟨τ, rfl, h⟩
  | cons j js ih =>
    obtain ⟨rs, fl, rfl, h₁, h₂⟩ := h
    have hc : VG.Proof.Ed25519.X86.SelInv (VG.Proof.Ed25519.X86.selT rs (rs.mem .esi && true && (!false || fl))) :=
      ⟨_, _, rfl, h₁, h₂⟩
    have hm : VG.Proof.Ed25519.X86.SelInv (VG.Proof.Ed25519.X86.selT (.ofList [.esi, .edi]) true) := ⟨_, _, rfl, by decide, by decide⟩
    refine CheckOk.seq ⟨_, rfl, hc.le fun _ => ?_⟩ ?_
    · show (rs.mem .esi && true && (!false || fl)) = true
      have : rs.mem .esi = true := h₁
      rw [this]; rfl
    · refine CheckOk.ite rfl ?_ (ih hm) fun _ _ => SelInv.meet
      obtain ⟨τ', e, h'⟩ := VG.Proof.Ed25519.X86.checkBlock_sel (VG.Proof.Ed25519.X86.combSelect_sel j) hm
      exact ⟨τ', e, h'⟩

/-! ## The comb -/

theorem combMultiply_check :
    ∃ h, (taint.check (VG.Proof.Ed25519.X86.regsTaint [.edi]) combMultiply h).isSome = true := by
  have init : VG.Proof.Ed25519.X86.CheckOk (VG.Proof.Ed25519.X86.regsTaint [.edi]) (.block combInit) _ (taint.le VG.Proof.Ed25519.X86.selL · = true) :=
    CheckOk.of_map (by taint_decide)
  have digits : VG.Proof.Ed25519.X86.CheckOk VG.Proof.Ed25519.X86.selL (.block combDigits) _ (taint.le VG.Proof.Ed25519.X86.selL · = true) :=
    CheckOk.of_map (by taint_decide)
  have addOdd : VG.Proof.Ed25519.X86.CheckOk VG.Proof.Ed25519.X86.selL (.block (combNeg 4 5 6 combOddSign ++ fieldCode addOddOps)) _
      (taint.le VG.Proof.Ed25519.X86.selL · = true) :=
    CheckOk.of_map (by taint_decide)
  have addEven : VG.Proof.Ed25519.X86.CheckOk VG.Proof.Ed25519.X86.selL (.block (combNeg 13 14 15 combEvenSign ++ fieldCode addEvenOps ++
      [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 32)])) _
      (fun σ => (taint.le VG.Proof.Ed25519.X86.selL σ && taint.condPub σ .ne) = true) :=
    CheckOk.of_map (by taint_decide)
  have finish : VG.Proof.Ed25519.X86.CheckOk VG.Proof.Ed25519.X86.selL combFinish _ (fun σ => (fun _ => true) σ = true) :=
    CheckOk.of_map (by taint_decide)
  have sel : VG.Proof.Ed25519.X86.CheckOk VG.Proof.Ed25519.X86.selL (combSelectFrom (List.range 32)) (VG.Proof.Ed25519.X86.selHint (List.range 32))
      (taint.le VG.Proof.Ed25519.X86.selL · = true) := by
    obtain ⟨τ, e, h⟩ := VG.Proof.Ed25519.X86.selFrom_ok (List.range 32) (τ := VG.Proof.Ed25519.X86.selL) ⟨_, _, rfl, by decide, by decide⟩
    exact ⟨τ, e, h.le nofun⟩
  obtain ⟨τ₁, e₁, hp⟩ := addEven
  rw [Bool.and_eq_true] at hp
  have body := digits.seq (sel.seq (addOdd.seq
    (P := fun σ' => taint.le VG.Proof.Ed25519.X86.selL σ' = true ∧ taint.condPub σ' .ne = true ∧ taint.le VG.Proof.Ed25519.X86.selL σ' = true)
    ⟨τ₁, e₁, hp.1, hp.2, hp.1⟩))
  obtain ⟨τ, e, -⟩ := init.seq ((CheckOk.loop (by decide) body).seq finish)
  exact ⟨_, Option.isSome_iff_exists.mpr ⟨τ, e⟩⟩

theorem combMultiply_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi) combMultiply
    (fun _ _ => True) := by
  obtain ⟨_, hc⟩ := VG.Proof.Ed25519.X86.combMultiply_check
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.regsTaint [.edi]) _ hc
  intro s t h
  exact VG.Proof.Ed25519.X86.regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CombLit`. -/
section

/-! The comb as a literal (`materialize_code`): its 32 tables of immediates are built once, here,
rather than in every check that evaluates it. -/
namespace VG.Impl.Ed25519.X86

materialize_code combMultiply

end VG.Impl.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks`. -/
section

/-!
# Constant time of the point arithmetic blocks

## Summaries of the addition chain

The constant-time checks of the point encoding (the inversion) and of the
point recovery (the square root) both run the addition chain `power250`, and
it repeats the loops of squarings of `sqn` on the same slots: each is
analysed once here, as a summary (`taint_summary`), which the checks use
(`taint_decide_sum`).
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (mul)

/-- The body of the loop of squarings of `sqn` in the slot at `o`. -/
abbrev sqBody (o : Nat) : Prog isa := .block (mul o o o ++ [.alu .sub .esi (.imm 1)])

taint_summary sqT1 : taint (VG.Proof.Ed25519.X86.regsTaint [.ebp, .esi, .edi]) (VG.Proof.Ed25519.X86.sqBody T1)
taint_summary sqT2 : taint (VG.Proof.Ed25519.X86.regsTaint [.ebp, .esi, .edi]) (VG.Proof.Ed25519.X86.sqBody T2)
taint_summary sqT3 : taint (VG.Proof.Ed25519.X86.regsTaint [.ebp, .esi, .edi]) (VG.Proof.Ed25519.X86.sqBody T3)

taint_summary power250Sum : taint (VG.Proof.Ed25519.X86.regsTaint [.edi]) power250 using sqT1 sqT2 sqT3

/-! ## The checks -/

theorem pointEncode_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi)
    pointEncode (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (VG.Proof.Ed25519.X86.regsTaint [.edi]) pointEncode h).isSome = true := by
    taint_decide_sum [power250Sum, sqT1]
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.regsTaint [.edi]) _ hc
  intro s t h
  exact VG.Proof.Ed25519.X86.regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)

def PowersCTPre (x : BitVec 32) (s t : State) : Prop :=
  VG.Proof.Ed25519.X86.PointCTCtx x s ∧ VG.Proof.Ed25519.X86.PointCTCtx x t ∧ s.wr = t.wr ∧ VG.Proof.X25519.X86.wd s.mem x 24 = VG.Proof.X25519.X86.wd t.mem x 24

/-- What is public at the loop of doublings of `double16`. -/
def doubleTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esi, .edi], flags := false, lens := [0, 8192], bases := [(.edi, 1, 0)] }

/-! The body of the loop of doublings, which both `powersBody 1024 16` and
`powersBody 1024 32` run: analysed once, as a summary. -/

taint_summary doubleSum : taint VG.Proof.Ed25519.X86.doubleTaint (.block doubleBody)

theorem powersBody16_ct (x : BitVec 32) : RelCT isa (VG.Proof.Ed25519.X86.PowersCTPre x)
    (powersBody 1024 16 true) (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (VG.Proof.Ed25519.X86.pointTaint 24) (powersBody 1024 16 true) h).isSome = true := by
    taint_decide_sum [doubleSum]
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.pointTaint 24) _ hc
  intro s t h
  exact VG.Proof.Ed25519.X86.pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem powersBody32_ct (x : BitVec 32) : RelCT isa (VG.Proof.Ed25519.X86.PowersCTPre x)
    (powersBody 1024 32 true) (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (VG.Proof.Ed25519.X86.pointTaint 24) (powersBody 1024 32 true) h).isSome = true := by
    taint_decide_sum [doubleSum]
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.pointTaint 24) _ hc
  intro s t h
  exact VG.Proof.Ed25519.X86.pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem powersBodyLocal_ct (x : BitVec 32) : RelCT isa (VG.Proof.Ed25519.X86.PowersCTPre x)
    (powersBody 5120 16 false) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.pointTaint 24) _ (by taint_decide)
  intro s t h
  exact VG.Proof.Ed25519.X86.pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem accumulate16_ct_regs (x : BitVec 32) : RelCT isa
    (fun s t => VG.Proof.Ed25519.X86.PointCTCtx x s ∧ VG.Proof.Ed25519.X86.PointCTCtx x t ∧ s.wr = t.wr ∧ VG.Proof.X25519.X86.wd s.mem x 28 = VG.Proof.X25519.X86.wd t.mem x 28)
    accumulate16 (fun s t => s.gpr .edi = t.gpr .edi) := by
  have h : RelCT isa (fun s t => VG.Proof.Ed25519.X86.PointCTCtx x s ∧ VG.Proof.Ed25519.X86.PointCTCtx x t ∧ s.wr = t.wr ∧ VG.Proof.X25519.X86.wd s.mem x 28 = VG.Proof.X25519.X86.wd t.mem x 28) accumulate16 (fun s t => ∀ r ∈ ([.edi] : List Reg), s.gpr r = t.gpr r) := by
    apply VG.Proof.Ed25519.X86.ctTaintRegs (τ := VG.Proof.Ed25519.X86.pointTaint 28) _ [.edi] (by taint_decide)
    intro s t h
    exact VG.Proof.Ed25519.X86.pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2
  exact h.mono (fun _ _ h => h) (fun _ _ h => h .edi (List.mem_singleton_self _))

theorem accumulate16_ct (x : BitVec 32) : RelCT isa
    (fun s t => VG.Proof.Ed25519.X86.PointCTCtx x s ∧ VG.Proof.Ed25519.X86.PointCTCtx x t ∧ s.wr = t.wr ∧ VG.Proof.X25519.X86.wd s.mem x 28 = VG.Proof.X25519.X86.wd t.mem x 28)
    accumulate16 (fun _ _ => True) :=
  (VG.Proof.Ed25519.X86.accumulate16_ct_regs x).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.RecoverCTLit`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
materialize_code recoverCandidate
materialize_code parityBlock := (.block (Impl.X25519.X86.freeze 64 ++ recoverParity) : Prog isa)
materialize_code zeroBlock := (.block (fieldZero 0) : Prog isa)
materialize_code rootCheckBlock := (.block (fieldEqual 11 6) : Prog isa)
materialize_code rootCheckMinusBlock := (.block (fieldEqual 11 12) : Prog isa)
materialize_code negateBlock := (.block (fieldCode [.const 5 0, .sub 0 5 0]) : Prog isa)
materialize_code rootAdjustBlock := (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) : Prog isa)
materialize_code successBlock := (.block recoverSuccess : Prog isa)
materialize_code decodeHeadBlock := (.block (decodeY ++ canonicalY) : Prog isa)
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks`. -/
section

/-! Fixed-trace arithmetic blocks used in point recovery. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

theorem edi_agree {base : BitVec 32} {s t : State} (hs : s.gpr .edi = base) (ht : t.gpr .edi = base) :
    VG.X86.Taint.Agree (VG.Proof.Ed25519.X86.regsTaint [.edi]) s t := VG.Proof.Ed25519.X86.regsTaint_agree (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact hs.trans ht.symm)

theorem recoverCandidate_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base) recoverCandidate (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (VG.Proof.Ed25519.X86.regsTaint [.edi]) recoverCandidate h).isSome = true := by
    taint_decide_sum [power250Sum, sqT1]
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.regsTaint [.edi]) _ hc
  exact fun _ _ h => VG.Proof.Ed25519.X86.edi_agree h.1 h.2

theorem parityBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block (Impl.X25519.X86.freeze 64 ++ recoverParity)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.regsTaint [.edi]) _ (by taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.X86.edi_agree h.1 h.2

theorem zeroBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block (fieldZero 0)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.regsTaint [.edi]) _ (by taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.X86.edi_agree h.1 h.2

theorem negateBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block (fieldCode [.const 5 0, .sub 0 5 0])) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.regsTaint [.edi]) _ (by taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.X86.edi_agree h.1 h.2

theorem successBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block recoverSuccess) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.regsTaint [.edi]) _ (by taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.X86.edi_agree h.1 h.2

theorem recoverInvalid_ct : RelCT isa (fun _ _ => True) recoverInvalid (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (VG.Proof.Ed25519.X86.regsTaint []) _ (by taint_decide)
  exact fun _ _ _ => VG.Proof.Ed25519.X86.regsTaint_agree (by simp)

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
materialize_code baseStartBlock := (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps) : Prog isa)
materialize_code baseFinishTail := (.block (outputWords 96 8 ++ Impl.X25519.X86.restore) : Prog isa)
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit`. -/
section

namespace VG.Impl.Ed25519.X86
materialize_code scalarBase
end VG.Impl.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
materialize_code pointEqualFirst := (.block (fieldCode pointEqualOps ++ fieldEqual 8 9) : Prog isa)
materialize_code pointEqualSecond := (.block (fieldEqual 10 11) : Prog isa)
materialize_code verifyFinishBlock := (.block verifyFinish : Prog isa)
materialize_code verifyWriteA := (.block (pointTableWrite 7680) : Prog isa)
materialize_code verifyWriteR := (.block (pointTableWrite 7808) : Prog isa)
materialize_code verifyReadA := (.block (pointTableRead 7680) : Prog isa)
materialize_code verifyScalarTail := (.block (copyWords 64 8 ++ scalarSubtract ++ ([.alu .test .ebx (.reg .ebx)] : List Instr)) : Prog isa)
materialize_code verifyLoadWords := (.block (copyWords 96 8) : Prog isa)
materialize_code dbl
materialize_code windowPrep
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyLit`. -/
section

namespace VG.Impl.Ed25519.X86
materialize_code verifyEquation
end VG.Impl.Ed25519.X86

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointCTMul`. -/
section

/-! Merged from `Proof.Ed25519.X86.PointCTBatch`. -/
section
/-! Merged from `Proof.Ed25519.X86.PointCTPowers`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure PowersCTState (x : BitVec 32) (j : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  counter : VG.Proof.X25519.X86.wd s.mem x 24 = BitVec.ofNat 32 j
  d : env s.mem x 16 = Spec.Ed25519.d

def PowersCTInv (x : BitVec 32) (count n : Nat) (s t : State) : Prop :=
  0 < n ∧ n ≤ count ∧ PowersCTState x (count - n) s ∧ PowersCTState x (count - n) t ∧ s.wr = t.wr

theorem powersLoop_ct (x : BitVec 32) (o count : Nat) (batch : Bool)
    (hlo : 928 ≤ o) (hfit : o + 128 * count ≤ 8192) (hn : count ≤ 32)
    (hc : RelCT isa (PowersCTPre x) (powersBody o count batch) (fun _ _ => True)) (n : Nat) :
    RelCT isa (PowersCTInv x count n) (.loop (powersBody o count batch) .ne) (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa) (PowersCTInv x count) (n := n)
  intro n
  have hb : RelCT isa (PowersCTInv x count n) (powersBody o count batch) (fun _ _ => True) :=
    hc.mono (fun _ _ h => ⟨h.2.2.1.ctx, h.2.2.2.1.ctx, h.2.2.2.2,
      h.2.2.1.counter.trans h.2.2.2.1.counter.symm⟩) (fun _ _ h => h)
  have hw (s : State) (h : PowersCTState x (count - n) s) (h0 : 0 < n) (hle : n ≤ count) :
      WP isa (powersBody o count batch) s fun t =>
        PowersCTState x (count - n + 1) t ∧ t.wr = s.wr ∧
          isa.eval .ne t = some (!decide (count - n + 1 = count)) := by
    refine WP.mono (powersBody_ok h.ctx.ctx o count (count - n) batch (by omega) hn hlo hfit
      h.counter h.d) fun t ⟨kt, it, zt, _, _, dt⟩ => ?_
    exact ⟨⟨h.ctx.keep kt.edi kt.wr, it, (dt 16 (by decide)).trans h.d⟩, kt.wr, zt⟩
  have hh := ctWithRuns hb (fun s t h => ⟨hw s h.2.2.1 h.1 h.2.1, hw t h.2.2.2.1 h.1 h.2.1⟩)
  apply hh.mono (fun _ _ h => h)
  intro s t ⟨_, a, b, hp, hs, ht⟩
  refine ⟨hs.2.2.trans ht.2.2.symm, fun _ => trivial, ?_⟩
  intro hz
  have hpos := hp.1
  have hle := hp.2.1
  rw [hs.2.2] at hz
  have hn1 : 1 < n := by
    by_contra hn1
    have he : count - n + 1 = count := by omega
    simp only [he, decide_true, Bool.not_true, Option.some.injEq] at hz
    cases hz
  have he : count - (n - 1) = count - n + 1 := by omega
  exact ⟨n - 1, by omega, by omega, by omega, he ▸ hs.1, he ▸ ht.1,
    hs.2.1.trans (hp.2.2.2.2.trans ht.2.1.symm)⟩

def PowersCTStart (x : BitVec 32) (s t : State) : Prop :=
  PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧
    env s.mem x 16 = Spec.Ed25519.d ∧ env t.mem x 16 = Spec.Ed25519.d

theorem pointPowers_ct (x : BitVec 32) (o count : Nat) (batch : Bool)
    (hlo : 928 ≤ o) (hfit : o + 128 * count ≤ 8192) (hn0 : 0 < count) (hn : count ≤ 32)
    (hc : RelCT isa (PowersCTPre x) (powersBody o count batch) (fun _ _ => True)) :
    RelCT isa (PowersCTStart x) (pointPowers o count batch) (fun _ _ => True) := by
  have hi : RelCT isa (PowersCTStart x)
      (.block [.mov .eax (.imm 0), .store (Impl.X25519.X86.sc 24) .eax]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ (h.1.ctx.edi.trans h.2.1.ctx.edi.symm))
  have hw (s : State) (h : PointCTCtx x s) (hd : env s.mem x 16 = Spec.Ed25519.d) :
      WP isa (.block [.mov .eax (.imm 0), .store (Impl.X25519.X86.sc 24) .eax]) s fun t =>
        PowersCTState x 0 t ∧ t.wr = s.wr := by
    refine WP.mono (powersInit_ok h.ctx o (128 * count)) fun t ⟨kt, it, ft⟩ => ?_
    exact ⟨⟨h.keep kt.edi kt.wr, it, by rw [counter_env h.ctx.fit ft]; exact hd⟩, kt.wr⟩
  have hh := ctWithRuns hi (fun s t h => ⟨hw s h.1 h.2.2.2.1, hw t h.2.1 h.2.2.2.2⟩)
  rw [pointPowers]
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_) (powersLoop_ct x o count batch hlo hfit hn hc count)
  intro s t ⟨_, a, b, hp, hs, ht⟩
  exact ⟨hn0, Nat.le_refl _, (Nat.sub_self count).symm ▸ hs.1,
    (Nat.sub_self count).symm ▸ ht.1, hs.2.trans (hp.2.2.1.trans ht.2.symm)⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

private theorem prepareBatch_ct (x : BitVec 32) (j : Nat) (hj : j < 32) :
    RelCT isa (fun s t => PowersCTStart x s t ∧ s.gpr .esi = BitVec.ofNat 32 j ∧ t.gpr .esi = BitVec.ofNat 32 j)
      prepareBatch (fun _ _ => True) := by
  have hl : RelCT isa (fun s t => PowersCTStart x s t ∧ s.gpr .esi = BitVec.ofNat 32 j ∧ t.gpr .esi = BitVec.ofNat 32 j)
      (.block loadCheckpoint) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.ctx.edi.trans h.1.2.1.ctx.edi.symm
    · exact h.2.1.trans h.2.2.symm
  have hw (s : State) (h : PointCTCtx x s) (hb : s.gpr .esi = BitVec.ofNat 32 j)
      (hd : env s.mem x 16 = Spec.Ed25519.d) :
      WP isa (.block loadCheckpoint) s fun t => PointCTCtx x t ∧ t.wr = s.wr ∧ env t.mem x 16 = Spec.Ed25519.d := by
    refine WP.mono (loadCheckpoint_ok h.ctx j hj hb) fun t ⟨kt, _, _, dt⟩ => ?_
    exact ⟨h.keep kt.keep.edi kt.keep.wr, kt.keep.wr, dt.trans hd⟩
  have hh := ctWithRuns hl (fun s t h => ⟨hw s h.1.1 h.2.1 h.1.2.2.2.1,
    hw t h.1.2.1 h.2.2 h.1.2.2.2.2⟩)
  have hp := pointPowers_ct x 5120 16 false (by decide) (by decide) (by decide) (by decide) (powersBodyLocal_ct x)
  have hp' := ctWithRuns hp (fun s t h => ⟨pointPowers_ok false h.1.ctx 5120 16 (by decide) (by decide)
    (by decide) (by decide) h.2.2.2.1, pointPowers_ok false h.2.1.ctx 5120 16 (by decide) (by decide)
    (by decide) (by decide) h.2.2.2.2⟩)
  have hr : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi) (.block restorePoint) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)
  rw [prepareBatch]
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_) (VG.RelCT.seq (hp'.mono (fun _ _ h => h) ?_) hr)
  · intro s t ⟨_, a, b, hp, hs, ht⟩
    exact ⟨hs.1, ht.1, hs.2.1.trans (hp.1.2.2.1.trans ht.2.1.symm), hs.2.2, ht.2.2⟩
  · intro s t ⟨_, a, b, hp, hs, ht⟩
    exact (hs.1.ctx hp.1.ctx).edi.trans (ht.1.ctx hp.2.1.ctx).edi.symm

structure BatchCTState (x : BitVec 32) (j : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  counter : VG.Proof.X25519.X86.wd s.mem x 28 = BitVec.ofNat 32 j
  d : env s.mem x 16 = Spec.Ed25519.d

theorem pointMulBatch_ct (x : BitVec 32) (j : Nat) (hj : j < 32) :
    RelCT isa (fun s t => BatchCTState x (j + 1) s ∧ BatchCTState x (j + 1) t ∧ s.wr = t.wr)
      pointMulBatch (fun _ _ => True) := by
  have hb : RelCT isa (fun s t => BatchCTState x (j + 1) s ∧ BatchCTState x (j + 1) t ∧ s.wr = t.wr)
      (.block batchBegin) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ (h.1.ctx.ctx.edi.trans h.2.1.ctx.ctx.edi.symm))
  have hw (s : State) (h : BatchCTState x (j + 1) s) : WP isa (.block batchBegin) s fun t =>
      BatchCTState x j t ∧ t.gpr .esi = BitVec.ofNat 32 j ∧ t.wr = s.wr := by
    refine WP.mono (batchBegin_ok h.ctx.ctx j h.counter) fun t ⟨kt, bt, it, ft⟩ => ?_
    exact ⟨⟨h.ctx.keep kt.edi kt.wr, it, by rw [counter28_env h.ctx.ctx.fit ft]; exact h.d⟩, bt, kt.wr⟩
  have hh := ctWithRuns hb (fun s t h => ⟨hw s h.1, hw t h.2.1⟩)
  have prep := (prepareBatch_ct x j hj).mono
    (P' := fun (s t : State) => BatchCTState x j s ∧ BatchCTState x j t ∧ s.wr = t.wr ∧
      s.gpr .esi = BitVec.ofNat 32 j ∧ t.gpr .esi = BitVec.ofNat 32 j)
    (fun _ _ h => ⟨⟨h.1.ctx, h.2.1.ctx, h.2.2.1, h.1.d, h.2.1.d⟩, h.2.2.2⟩) (fun _ _ h => h)
  have pw (s : State) (h : BatchCTState x j s) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
      WP isa prepareBatch s fun t => BatchCTState x j t ∧ t.wr = s.wr := by
    refine WP.mono (prepareBatch_ok h.ctx.ctx j hj hb h.d) fun t ⟨kt, _, _, dt⟩ => ?_
    exact ⟨⟨h.ctx.keep kt.edi kt.wr, (kt.batch_index h.ctx.ctx).trans h.counter, dt⟩, kt.wr⟩
  have prep' := ctWithRuns prep (fun s t h => ⟨pw s h.1 h.2.2.2.1, pw t h.2.1 h.2.2.2.2⟩)
  have test : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi) (.block batchTest) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)
  rw [pointMulBatch]
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (VG.RelCT.seq (prep'.mono (fun _ _ h => h) ?_) (VG.RelCT.seq (accumulate16_ct_regs x) test))
  · intro s t ⟨_, a, b, hp, hs, ht⟩
    exact ⟨hs.1, ht.1, hs.2.2.trans (hp.2.2.trans ht.2.2.symm), hs.2.1, ht.2.1⟩
  · intro s t ⟨_, a, b, hp, hs, ht⟩
    exact ⟨hs.1.ctx, ht.1.ctx, hs.2.trans (hp.2.2.1.trans ht.2.symm), hs.1.counter.trans ht.1.counter.symm⟩

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointCTMulLoop`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulCTState (x : BitVec 32) (scalar count : Nat) (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  counter : VG.Proof.X25519.X86.wd s.mem x 28 = BitVec.ofNat 32 n
  value : point (env s.mem x) 0 1 2 3 = after scalar p (16 * n)
  table : ∀ j < count, tablePoint s.mem x (1024 + 128 * j) = powerPoint p (16 * j)
  bits : ∀ i < 16 * count, s.mem (addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat
  d : env s.mem x 16 = Spec.Ed25519.d

theorem mulCTState_step {x : BitVec 32} {s : State} {scalar count j : Nat} {p : Spec.Ed25519.Point}
    (h : MulCTState x scalar count p (j + 1) s) (hj : j < count) (hn : count ≤ 32) :
    WP isa pointMulBatch s fun t => MulCTState x scalar count p j t ∧ t.wr = s.wr ∧
      isa.eval .ne t = some (!decide (j = 0)) := by
  refine WP.mono (pointMulBatch_ok h.ctx.ctx scalar j p (by omega) h.counter
    (fun i hi => h.bits _ (by omega)) (h.table j hj) h.value h.d) fun t ⟨kt, it, zt, pt, dt⟩ => ?_
  refine ⟨⟨h.ctx.keep kt.edi kt.wr, it, pt, ?_, ?_, dt⟩, kt.wr, zt⟩
  · intro k hk
    exact (kt.checkpoint h.ctx.ctx k (by omega)).trans (h.table k hk)
  · intro i hi
    exact (kt.bit h.ctx.ctx i (by omega)).trans (h.bits i hi)

def MulCTInv (x : BitVec 32) (a b count : Nat) (p q : Spec.Ed25519.Point) (n : Nat) (s t : State) : Prop :=
  0 < n ∧ n ≤ count ∧ MulCTState x a count p n s ∧ MulCTState x b count q n t ∧ s.wr = t.wr

theorem pointMulLoop_ct (x : BitVec 32) (a b count : Nat) (p q : Spec.Ed25519.Point)
    (hn : count ≤ 32) (n : Nat) :
    RelCT isa (MulCTInv x a b count p q n) (.loop pointMulBatch .ne) (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa) (MulCTInv x a b count p q) (n := n)
  intro n
  by_cases hn0 : n = 0
  · subst n
    exact VG.RelCT.of_false (fun _ _ h => Nat.not_lt_zero _ h.1)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  by_cases hj : j < count
  · have hb := (pointMulBatch_ct x j (by omega)).mono
      (P' := MulCTInv x a b count p q (j + 1))
      (fun _ _ h => ⟨⟨h.2.2.1.ctx, h.2.2.1.counter, h.2.2.1.d⟩,
        ⟨h.2.2.2.1.ctx, h.2.2.2.1.counter, h.2.2.2.1.d⟩, h.2.2.2.2⟩) (fun _ _ h => h)
    have hh := ctWithRuns hb (fun _ _ h => ⟨mulCTState_step h.2.2.1 hj hn, mulCTState_step h.2.2.2.1 hj hn⟩)
    apply hh.mono (fun _ _ h => h)
    intro s t ⟨_, u, v, hp, hs, ht⟩
    refine ⟨hs.2.2.trans ht.2.2.symm, fun _ => trivial, ?_⟩
    intro hz
    have hj0 : 0 < j := by
      by_contra hzero
      have he : j = 0 := by omega
      rw [hs.2.2, he] at hz
      contradiction
    exact ⟨j, by omega, hj0, by omega, hs.1, ht.1,
      hs.2.1.trans (hp.2.2.2.2.trans ht.2.1.symm)⟩
  · exact VG.RelCT.of_false (fun _ _ h => hj (by have := h.2.1; omega))

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

private theorem pointMultiplyInit_ct (x : BitVec 32) (count : Nat) (hn : count = 16 ∨ count = 32) :
    RelCT isa (PowersCTStart x) (pointMultiplyInit count) (fun _ _ => True) := by
  have hn0 : 0 < count := by omega
  have hn32 : count ≤ 32 := by omega
  have bodyct : RelCT isa (PowersCTPre x) (powersBody 1024 count true) (fun _ _ => True) := by
    rcases hn with rfl | rfl
    · exact powersBody16_ct x
    · exact powersBody32_ct x
  have hp := pointPowers_ct x 1024 count true (by decide) (by omega) hn0 hn32 bodyct
  have hh := ctWithRuns hp (fun _ _ h => ⟨pointPowers_ok true h.1.ctx 1024 count (by decide) (by omega)
    hn0 hn32 h.2.2.2.1, pointPowers_ok true h.2.1.ctx 1024 count (by decide) (by omega)
    hn0 hn32 h.2.2.2.2⟩)
  have ht : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi)
      (.seq (.block (constPoint Spec.Ed25519.identity)) (.block (mulCounterInit count))) (fun _ _ => True) := by
    rcases hn with rfl | rfl
    all_goals
      apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
      intro s t h
      exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)
  rw [pointMultiplyInit]
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_) ht
  intro s t ⟨_, a, b, h, hs, ht⟩
  exact (hs.1.ctx h.1.ctx).edi.trans (ht.1.ctx h.2.1.ctx).edi.symm

structure MulCTInput (x : BitVec 32) (scalar count : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  bound : scalar < 2 ^ (16 * count)
  bits : ∀ i < 16 * count, s.mem (addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat
  d : env s.mem x 16 = Spec.Ed25519.d

theorem pointMultiply_ct (x : BitVec 32) (a b count : Nat) (hn : count = 16 ∨ count = 32) :
    RelCT isa (fun s t => MulCTInput x a count s ∧ MulCTInput x b count t ∧ s.wr = t.wr)
      (pointMultiply count) (fun _ _ => True) := by
  have hn0 : 0 < count := by omega
  have hn32 : count ≤ 32 := by omega
  have init := (pointMultiplyInit_ct x count hn).mono
    (P' := fun (s t : State) => MulCTInput x a count s ∧ MulCTInput x b count t ∧ s.wr = t.wr)
    (fun _ _ h => ⟨h.1.ctx, h.2.1.ctx, h.2.2, h.1.d, h.2.1.d⟩) (fun _ _ h => h)
  have hw (s : State) (scalar : Nat) (h : MulCTInput x scalar count s) :
      WP isa (pointMultiplyInit count) s fun t =>
        MulCTState x scalar count (point (env s.mem x) 0 1 2 3) count t ∧ t.wr = s.wr := by
    refine WP.mono (pointMultiplyInit_ok h.ctx.ctx count hn0 hn32 h.d) fun t ⟨kt, it, pt, tt, dt⟩ => ?_
    exact ⟨⟨h.ctx.keep kt.edi kt.wr, it,
      pt.trans (after_top scalar (16 * count) _ h.bound).symm, tt,
      fun i hi => (kt.bit h.ctx.ctx i (by omega)).trans (h.bits i hi), dt⟩, kt.wr⟩
  have hh := ctWithRuns init (fun s t h => ⟨hw s a h.1, hw t b h.2.1⟩)
  rw [pointMultiply]
  refine VG.RelCT.seq hh ?_
  intro s t ts tt s' t' ⟨_, u, v, h, hs, ht⟩ es et
  exact pointMulLoop_ct x a b count _ _ hn32 count _ _ _ _ _ _
    ⟨hn0, Nat.le_refl _, hs.1, ht.1, hs.2.trans (h.2.2.trans ht.2.symm)⟩ es et

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointEqual`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

private theorem eqOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := ⟨rfl, rfl, rfl, rfl⟩

theorem pointEqual_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointEqual s fun t => FieldKeep x s t ∧ t.gpr .eax = signWord
      (Spec.Ed25519.pointEqual (point (env s.mem x) 0 1 2 3) (point (env s.mem x) 4 5 6 7)) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hc) fun a ⟨ka, ea⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.ctx hc) 8 9) fun b ⟨kb, eb, zb⟩ => ?_
  have ab := (eqOps_eval (env s.mem x)).1
  have a9 := (eqOps_eval (env s.mem x)).2.1
  have a10 := (eqOps_eval (env s.mem x)).2.2.1
  have a11 := (eqOps_eval (env s.mem x)).2.2.2
  rw [ea, ab, a9] at zb
  apply WP.ite (decide (env s.mem x 0 * env s.mem x 6 = env s.mem x 4 * env s.mem x 2)) zb
  · intro heq
    refine WP.seq (WP.mono (fieldEqual_ok ((ka.trans kb).ctx hc) 10 11) fun c ⟨kc, _, zc⟩ => ?_)
    rw [eb 10 (by decide), eb 11 (by decide), ea, a10, a11] at zc
    apply WP.ite (decide (env s.mem x 1 * env s.mem x 6 = env s.mem x 5 * env s.mem x 2)) zc
    · intro heq'
      refine WP.mono (returnFlag_ok c x true) fun t ⟨kt, _, rt⟩ => ?_
      refine ⟨((ka.trans kb).trans kc).trans kt, ?_⟩
      have h := of_decide_eq_true heq
      have h' := of_decide_eq_true heq'
      simpa only [Spec.Ed25519.pointEqual, point, h, h', beq_self_eq_true, Bool.true_and] using rt
    · intro hne
      refine WP.mono (returnFlag_ok c x false) fun t ⟨kt, _, rt⟩ => ?_
      refine ⟨((ka.trans kb).trans kc).trans kt, ?_⟩
      have h := of_decide_eq_false hne
      simpa only [Spec.Ed25519.pointEqual, point, beq_eq_false_iff_ne.mpr h, Bool.and_false] using rt
  · intro hne
    refine WP.mono (returnFlag_ok b x false) fun t ⟨kt, _, rt⟩ => ?_
    refine ⟨(ka.trans kb).trans kt, ?_⟩
    have h := of_decide_eq_false hne
    simpa only [Spec.Ed25519.pointEqual, point, beq_eq_false_iff_ne.mpr h, Bool.false_and] using rt

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain`. -/
section

/-! Merged from `Proof.Ed25519.X86.ScalarBaseContract`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

def scalarBaseLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let input : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [input, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      input.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

theorem scalarBase_pre {s : State} (h : scalarBaseLocal.pre s) :
    ScratchPre s 2 3 ∧ InputPre s 2 1 8 ∧ OutputPre s 2 := by
  obtain ⟨rd, wr, os, ins, _, ars, ro, rs, ofit, ifit, sfit, spfit⟩ := h
  refine ⟨⟨by decide, ?_, sfit, ?_, by omega_using [spfit], ars, rs⟩,
    ⟨?_, ifit, ?_⟩, ⟨?_, ofit, os, ro⟩⟩
  · rw [wr]; simp
  · rw [rd]; simp
  · rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero, rd]; simp
  · rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero]; exact ins
  · rw [wr]; simp
end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointEncode`. -/
section
/-! Canonical Ed25519 point encoding in scratch slot1. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem pointEncode_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa pointEncode s fun t => IKeep x s t ∧
      VG.Proof.X25519.X86.fe t.mem x 96 =
        (env s.mem x 1 * Spec.X25519.pow (env s.mem x 2) (Spec.X25519.P - 2)).val +
        ((env s.mem x 0 * Spec.X25519.pow (env s.mem x 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  refine WP.seq (WP.mono (pointAffine_ok hc) fun a ⟨ka, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (freezeField_ok (ka.ctx hc) 0) fun b ⟨kb, eb, vb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointSign_ok (kb.ctx (ka.ctx hc))) fun c ⟨kc, mc, sc⟩ => ?_
  rw [WP.block_append_iff]
  have cc := kc.ctx (kb.ctx (ka.ctx hc))
  refine WP.mono (freezeField_ok cc 1) fun d ⟨kd, _, vd⟩ => ?_
  have ds : d.gpr .esi = BitVec.ofNat 32 (((env a.mem x 0).val % 2) * 2 ^ 31) := by
    change VG.Proof.X25519.X86.fe b.mem x 64 = _ at vb
    rw [kd.keep.esi, sc, vb]
  have dy : VG.Proof.X25519.X86.fe d.mem x 96 = (env a.mem x 1).val := by
    rw [mc, eb] at vd
    exact vd
  refine WP.mono (encodeSign_ok (kd.ctx cc) ((env a.mem x 0).val % 2) ((env a.mem x 1).val)
    (by omega) (Nat.lt_trans (env a.mem x 1).isLt (by decide : Spec.X25519.P < 2 ^ 255)) dy ds)
    fun t ⟨kt, vt⟩ => ?_
  refine ⟨(((ka.trans (IKeep.of_field kb)).trans kc).trans (IKeep.of_field kd)).trans (IKeep.of_field kt), ?_⟩
  rw [vt, ax, ay]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem baseSetup_d (e : Env) : evalOps baseSetupOps e 16 = Spec.Ed25519.d := rfl

theorem Saved.ikeep {s₀ s t : State} {x : BitVec 32} (h : VG.Proof.Ed25519.X86.Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (k : IKeep x s t) : VG.Proof.Ed25519.X86.Saved s₀ x t :=
  h.of_offset hx ⟨k.edi, k.esp, k.rd, k.wr⟩ k.frame (by decide) (by decide) (by decide)

theorem Saved.mulkeep {s₀ s t : State} {x : BitVec 32} (h : VG.Proof.Ed25519.X86.Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (k : MulKeep x s t) : VG.Proof.Ed25519.X86.Saved s₀ x t :=
  h.of_offset hx ⟨k.edi, k.esp, k.rd, k.wr⟩ k.frame (by decide) (by decide) (by decide)

theorem pointEncode_value {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa pointEncode s fun t => IKeep x s t ∧ Spec.Ed25519.encodeLE 32 (VG.Proof.X25519.X86.fe t.mem x 96) =
      Spec.Ed25519.encodePoint (point (env s.mem x) 0 1 2 3) := by
  refine WP.mono (VG.Proof.Ed25519.X86.pointEncode_ok hc) fun t ⟨kt, vt⟩ => ⟨kt, ?_⟩
  rw [vt]; rfl

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTSetup`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def baseScalar (s : State) : Nat := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)

theorem pointCTCtx_saved {s₀ s : State} (h : scalarBaseLocal.pre s₀) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 2) s) :
    PointCTCtx (arg s₀ 2) s := by
  obtain ⟨hp, _, ho⟩ := VG.Proof.Ed25519.X86.scalarBase_pre h
  refine ⟨hs.ctx hp.fit hp.wr, ?_, ?_, ?_, ?_⟩
  · rw [hs.wr, h.2.1]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · rw [hs.wr, h.2.1]
    exact List.pairwise_cons.mpr ⟨by simpa using ho.sep, by simp⟩
  · intro r hr
    rw [hs.wr, h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [BitVec.toNat_setWidth]
    · omega_using [ho.fit]
    · omega_using [hp.fit]
  · change s.wr.getD 1 ⟨0, 0⟩ = _
    rw [hs.wr, h.2.1]; rfl

theorem scalarBaseStart_ok {s : State} (h : scalarBaseLocal.pre s) :
    WP isa (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps)) s fun t =>
      VG.Proof.Ed25519.X86.Saved s (arg s 2) t ∧ MulCTInput (arg s 2) (VG.Proof.Ed25519.X86.baseScalar s) 16 t := by
  obtain ⟨hp, hi, _⟩ := VG.Proof.Ed25519.X86.scalarBase_pre h
  have scalar_bound : VG.Proof.Ed25519.X86.baseScalar s < 2 ^ (16 * 16) := by
    have hb := decodeLE_lt (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at hb
    change VG.Proof.Ed25519.X86.baseScalar s < 256 ^ 32 at hb
    rw [show 2 ^ (16 * 16) = 256 ^ 32 by decide]
    exact hb
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (abiSave_ok hp) fun a ha => ?_)
  refine WP.block_append (WP.mono (inputBits_ok hp hi ha (by decide) (by decide)) fun b ⟨hb, bits⟩ => ?_)
  have cb := hb.ctx hp.fit hp.wr
  refine WP.mono (fieldCode_ok baseSetupOps cb) fun c ⟨kc, ec⟩ => ?_
  have hc := hb.ikeep hp.fit (IKeep.of_field kc)
  refine ⟨hc, VG.Proof.Ed25519.X86.pointCTCtx_saved h hc, scalar_bound, ?_, ?_⟩
  · intro i ii
    rw [IKeep.bit (IKeep.of_field kc) cb i (by omega_using [ii]), bits i (by omega_using [ii]), scalarBit_nat]
    rfl
  · rw [ec, VG.Proof.Ed25519.X86.baseSetup_d]

theorem scalarBaseStart_ct : RelCT isa
    (fun s t => scalarBaseLocal.pre s ∧ scalarBaseLocal.pre t ∧ scalarBaseLocal.pub s t)
    (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by taint_decide)
  intro s t ⟨hs, ht, hp⟩
  obtain ⟨sp, a0, a1, a2⟩ := hp
  obtain ⟨ps, _, os⟩ := VG.Proof.Ed25519.X86.scalarBase_pre hs
  obtain ⟨pt, _, ot⟩ := VG.Proof.Ed25519.X86.scalarBase_pre ht
  refine scalarTaint_agree (scalarTaint_wf ps os hs.2.1 hs.2.2.2.2.1)
    (scalarTaint_wf pt ot ht.2.1 ht.2.2.2.2.1) sp ?_ (by decide) hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified`. -/
section

/-! Merged from `Proof.Ed25519.X86.ScalarBaseCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.ScalarBaseCTFinish`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def BaseSaved (s₀ t₀ s t : State) : Prop := Saved s₀ (arg s₀ 2) s ∧ Saved t₀ (arg t₀ 2) t

theorem scalarBaseFinish_ct (s₀ t₀ : State) (hs : scalarBaseLocal.pre s₀) (ht : scalarBaseLocal.pre t₀)
    (hp : scalarBaseLocal.pub s₀ t₀) : RelCT isa (BaseSaved s₀ t₀) (.block (finishWords 96)) (fun _ _ => True) := by
  obtain ⟨ps, _, _⟩ := scalarBase_pre hs
  obtain ⟨pt, _, _⟩ := scalarBase_pre ht
  have loadct : RelCT isa (BaseSaved s₀ t₀)
      (.block [.mov .esi (.mem (Impl.X25519.X86.at_ .esp 4))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.esp]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (h.1.esp.trans (hp.1.trans h.2.esp.symm)))
  have hh := ctWithRuns loadct (fun _ _ h => ⟨loadArg_ok (i := 0) ps h.1 (by decide),
    loadArg_ok (i := 0) pt h.2 (by decide)⟩)
  have tailct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (outputWords 96 8 ++ Impl.X25519.X86.restore)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2]
  simp only [finishWords, List.append_assoc]
  refine ctBlockAppend (hh.mono (fun _ _ h => h) ?_) tailct
  intro s t ⟨_, a, b, _, ha, hb⟩
  exact ⟨ha.1.edi.trans (hp.2.2.2.trans hb.1.edi.symm), ha.2.1.trans (hp.2.1.trans hb.2.1.symm)⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def BaseCTReady (s₀ s : State) : Prop :=
  Saved s₀ (arg s₀ 2) s ∧ MulCTInput (arg s₀ 2) (baseScalar s₀) 16 s

theorem scalarBaseTail_ct (s₀ t₀ : State) (hs : scalarBaseLocal.pre s₀) (ht : scalarBaseLocal.pre t₀)
    (hp : scalarBaseLocal.pub s₀ t₀) :
    RelCT isa (fun s t => BaseCTReady s₀ s ∧ BaseCTReady t₀ t)
      (.seq combMultiply (.seq pointEncode (.block (finishWords 96)))) (fun _ _ => True) := by
  have mulct := combMultiply_ct.mono
    (P' := fun (s t : State) => BaseCTReady s₀ s ∧ BaseCTReady t₀ t)
    (fun _ _ h => h.1.2.ctx.ctx.edi.trans (hp.2.2.2.trans h.2.2.ctx.ctx.edi.symm)) (fun _ _ h => h)
  have mw (u s : State) (h : BaseCTReady u s) : WP isa combMultiply s (Saved u (arg u 2)) := by
    refine WP.mono (combMultiply_ok (S := baseScalar u) h.2.ctx.ctx (by simpa using h.2.bound)
      (fun q hq => by rw [h.2.bits q (by omega), scalarBit_nat]) h.2.d) fun t ⟨_, kt⟩ => ?_
    exact h.1.mulkeep h.2.ctx.ctx.fit kt
  have mul := ctWithRuns mulct (fun s t h => ⟨mw s₀ s h.1, mw t₀ t h.2⟩)
  have encct := pointEncode_ct.mono (P' := BaseSaved s₀ t₀)
    (fun _ _ h => h.1.edi.trans (hp.2.2.2.trans h.2.edi.symm)) (fun _ _ h => h)
  have ew (u s : State) (hu : scalarBaseLocal.pre u) (h : Saved u (arg u 2) s) :
      WP isa pointEncode s (Saved u (arg u 2)) := by
    have pu := (scalarBase_pre hu).1
    refine WP.mono (pointEncode_ok (h.ctx pu.fit pu.wr)) fun t ⟨kt, _⟩ => ?_
    exact h.ikeep pu.fit kt
  have enc := ctWithRuns encct (fun s t h => ⟨ew s₀ s hs h.1, ew t₀ t ht h.2⟩)
  refine VG.RelCT.seq (mul.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
    (VG.RelCT.seq (enc.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
      (scalarBaseFinish_ct s₀ t₀ hs ht hp))

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have start := ctWithRuns scalarBaseStart_ct
    (fun _ _ h => ⟨scalarBaseStart_ok h.1, scalarBaseStart_ok h.2.1⟩)
  rw [scalarBase]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact scalarBaseTail_ct u v hp.1 hp.2.1 hp.2.2 _ _ _ _ _ _ ⟨hu, hv⟩ es et

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarBase_correct {s : State} (h : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨hp, hi, ho⟩ := scalarBase_pre h
  let scalar := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
  have scalar_bound : scalar < 2 ^ (16 * 16) := by
    have hb := decodeLE_lt (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at hb
    change scalar < 256 ^ 32 at hb
    rw [show 2 ^ (16 * 16) = 256 ^ 32 by decide]
    exact hb
  simp only [scalarBase, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (abiSave_ok hp) fun a ha => ?_))
  refine WP.block_append (WP.mono (inputBits_ok hp hi ha (by decide) (by decide)) fun b ⟨hb, bits⟩ => ?_)
  have cb := hb.ctx hp.fit hp.wr
  refine WP.mono (fieldCode_ok baseSetupOps cb) fun c ⟨kc, ec⟩ => ?_
  have hc := hb.ikeep hp.fit (IKeep.of_field kc)
  have cc := hc.ctx hp.fit hp.wr
  have dc : env c.mem (arg s 2) 16 = Spec.Ed25519.d := by rw [ec, baseSetup_d]
  have bc : ∀ i < 256, c.mem (addr (arg s 2) (7168 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2) := by
    intro i ii
    rw [IKeep.bit (IKeep.of_field kc) cb i (by omega_using [ii]), bits i (by omega_using [ii])]
  refine WP.seq (WP.mono (combMultiply_ok cc (by simpa using scalar_bound) bc dc) fun d ⟨pd, kd⟩ => ?_)
  have hd := hc.mulkeep hp.fit kd
  refine WP.seq (WP.mono (pointEncode_value (hd.ctx hp.fit hp.wr)) fun e ⟨ke, ve⟩ => ?_)
  have he := hd.ikeep hp.fit ke
  refine WP.mono (finishWords_ok hp ho he (src := 96) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, ve, encodePoint_rep pd, Spec.Ed25519.scalarBase,
    encodePoint_rep (pointMul_rep _ basePoint_rep)]

def baseSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

def baseSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := baseSatMem
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

theorem scalarBase_ok (s : State) (h : scalarBaseLocal.pre s) :
    ∃ tr t, Exec isa scalarBase s tr t ∧ abiPreserved s t ∧ scalarBaseLocal.post s t :=
  scalarBase_correct h

def scalarBaseWide : Contract isa :=
  { scalarBaseLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let input : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [input] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      input.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 }

def scalarBaseRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 32⟩, ⟨argAddr s 0, 12⟩]
def scalarBaseWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem scalarBaseWide_pre (s : State) (h : scalarBaseWide.pre s) :
    scalarBaseLocal.pre (s.withRegions (scalarBaseRd s) (scalarBaseWr s)) := by
  simp only [scalarBaseLocal, scalarBaseRd, scalarBaseWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarBaseWide_implies : scalarBaseWide.Implies (Spec.Ed25519.scalarBaseContract X86.abi) := by
    have a0 : arg baseSatState 0 = 0x1000 := by decide
    have a1 : arg baseSatState 1 = 0x2000 := by decide
    have a2 : arg baseSatState 2 = 0x4000 := by decide
    have e : argAddr baseSatState 0 = 0x8004 := by decide
    have esp : baseSatState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, scalarBaseWide, scalarBaseLocal, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, e, esp] using baseSatState

theorem scalarBase_verified : Verified X86.target scalarBase (Spec.Ed25519.scalarBaseContract X86.abi) := by
  have hsat := scalarBaseWide_implies.sat_left
  have satLocal : ∃ s, scalarBaseLocal.pre s := hsat.elim fun s h => ⟨_, scalarBaseWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarBase scalarBaseLocal :=
    Verified.of_correct scalarBase_ok scalarBase_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarBaseRd scalarBaseWr scalarBaseWide_pre
    ?_ ?_ ?_ ?_ hsat) scalarBaseWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarBaseRd, scalarBaseWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl) | rfl | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarBaseWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [scalarBaseWide, scalarBaseLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [scalarBaseWide, scalarBaseLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyTables`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem tablePointer_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (o : Nat) :
    WP isa (.block [.mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 o))]) s fun t =>
      VG.Proof.X25519.X86.Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 o := by
  refine Wp.wp_mov fun a ha => Wp.wp_addi fun t ht => WP.block_nil ?_
  exact ⟨(VG.Proof.X25519.X86.updKeep ha).trans (VG.Proof.X25519.X86.updKeep ht), ht.mem.trans ha.mem, by rw [ht.gpr, ha.gpr, hc.edi]⟩

theorem pointTableWrite_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (o : Nat)
    (ho : 192 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => ScalarKeep s t ∧ VG.Frame [VG.Proof.X25519.X86.sub x o 128] s.mem t.mem ∧
      tablePoint t.mem x o = point (env s.mem x) 0 1 2 3 := by
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.tablePointer_ok hc o) fun a ⟨ka, ma, pa⟩ => ?_)
  refine WP.mono (pointToTable_ok (ka.ctx hc) pa ho hn) fun t ⟨kt, vt⟩ => ?_
  exact ⟨(Keep.scalar ka).trans ⟨kt.gpr _ (by decide), kt.gpr _ (by decide), kt.rd, kt.wr⟩,
    by rw [← ma]; exact kt.frame, by rw [ma] at vt; exact vt⟩

theorem pointTableRead_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (o : Nat)
    (ho : 192 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = tablePoint s.mem x o ∧
      (∀ i : Slot, 4 ≤ i.val → env t.mem x i = env s.mem x i) := by
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.tablePointer_ok hc o) fun a ⟨ka, ma, pa⟩ => ?_)
  refine WP.mono (pointFromTable_ok (ka.ctx hc) pa ho hn) fun t ⟨kt, vt⟩ => ?_
  exact ⟨(FieldKeep.of_mem ka ma).trans (FieldKeep.of_copy kt (ka.ctx hc)),
    by rw [ma] at vt; exact vt, fun i hi => by rw [kt.high (ka.ctx hc) i hi, ma]⟩

theorem Saved.copykeep {s₀ s t : State} {x : BitVec 32} {o n : Nat} (h : VG.Proof.Ed25519.X86.Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (k : ScalarKeep s t) (f : VG.Frame [VG.Proof.X25519.X86.sub x o n] s.mem t.mem)
    (ho : 16 ≤ o) (hn : o + n ≤ 8192) (ho' : o < 8192) : VG.Proof.Ed25519.X86.Saved s₀ x t :=
  h.of_offset hx k f ho hn ho'

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.WindowTables`. -/
section

/-!
# Verification's tables: `[1]A … [15]A` and `-[1]B … -[15]B`

The table of multiples of `A` (byte 1024) is built by repeated addition of `A`,
each entry representing its multiple (`Rep`); the table of negated multiples
of `B` (byte 3072) is stored from constants. Both hold points with the
specification's coordinates, added with `pointAdd`.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

/-! ## Frames -/

/-- A word outside the regions `[o, o + n)` and `[o', o' + n')` of the workspace. -/
theorem wd_frame2 {x : BitVec 32} {m m' : Mem} {o n o' n' d : Nat}
    (hf : VG.Frame [VG.Proof.X25519.X86.sub x o n, VG.Proof.X25519.X86.sub x o' n'] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o + n ≤ 8192) (ho' : o' + n' ≤ 8192) (hd : d + 4 ≤ 8192)
    (h1 : d + 4 ≤ o ∨ o + n ≤ d) (h2 : d + 4 ≤ o' ∨ o' + n' ≤ d) : VG.Proof.X25519.X86.wd m' x d = VG.Proof.X25519.X86.wd m x d :=
  VG.Proof.X25519.X86.wd_frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.X25519.X86.sub_disj (by omega) (by omega) h1
    · exact VG.Proof.X25519.X86.sub_disj (by omega) (by omega) h2

theorem tablePoint_frame2 {x : BitVec 32} {m m' : Mem} {o n o' n' a : Nat}
    (hf : VG.Frame [VG.Proof.X25519.X86.sub x o n, VG.Proof.X25519.X86.sub x o' n'] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o + n ≤ 8192) (ho' : o' + n' ≤ 8192) (ha : a + 128 ≤ 8192)
    (h1 : a + 128 ≤ o ∨ o + n ≤ a) (h2 : a + 128 ≤ o' ∨ o' + n' ≤ a) :
    tablePoint m' x a = tablePoint m x a :=
  table_point_of_words fun k hk => VG.Proof.Ed25519.X86.wd_frame2 hf hx ho ho' (by omega) (by omega) (by omega)

theorem env_frame2 {x : BitVec 32} {m m' : Mem} {o n o' n' : Nat}
    (hf : VG.Frame [VG.Proof.X25519.X86.sub x o n, VG.Proof.X25519.X86.sub x o' n'] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o + n ≤ 8192) (ho' : o' + n' ≤ 8192) (i : Slot)
    (h1 : offset i + 32 ≤ o ∨ o + n ≤ offset i) (h2 : offset i + 32 ≤ o' ∨ o' + n' ≤ offset i) :
    env m' x i = env m x i := by
  have hi := i.isLt
  exact congrArg VG.Proof.X25519.toFe (VG.Proof.X25519.X86.fe_frame fun k hk =>
    VG.Proof.Ed25519.X86.wd_frame2 hf hx ho ho' (by simp only [offset] at h1 ⊢; omega) (by omega) (by omega))

/-- A frame of slots and of a region is one of slots and of a larger region. -/
theorem frame2_widen {x : BitVec 32} {m m' : Mem} {o n o' n' : Nat}
    (hf : VG.Frame [VG.Proof.X25519.X86.sub x o n, VG.Proof.X25519.X86.sub x o' n'] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32) {p q p' q' : Nat}
    (h1 : p ≤ o) (h2 : o + n ≤ p + q) (h3 : p' ≤ o') (h4 : o' + n' ≤ p' + q') (h5 : o < 8192)
    (h6 : o' < 8192) : VG.Frame [VG.Proof.X25519.X86.sub x p q, VG.Proof.X25519.X86.sub x p' q'] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, VG.Proof.X25519.X86.sub_sub hx h1 h2 h5⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, VG.Proof.X25519.X86.sub_sub hx h3 h4 h6⟩

/-- A frame of one region as one of two. -/
theorem frame1_two {x : BitVec 32} {m m' : Mem} {o n : Nat} (hf : VG.Frame [VG.Proof.X25519.X86.sub x o n] m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) {p q p' q' : Nat} (h1 : p ≤ o) (h2 : o + n ≤ p + q) (h5 : o < 8192) :
    VG.Frame [VG.Proof.X25519.X86.sub x p q, VG.Proof.X25519.X86.sub x p' q'] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_cons_self, VG.Proof.X25519.X86.sub_sub hx h1 h2 h5⟩

/-- A frame of one region as the second of two. -/
theorem frame1_two' {x : BitVec 32} {m m' : Mem} {o n : Nat} (hf : VG.Frame [VG.Proof.X25519.X86.sub x o n] m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) {p q p' q' : Nat} (h1 : p' ≤ o) (h2 : o + n ≤ p' + q') (h5 : o < 8192) :
    VG.Frame [VG.Proof.X25519.X86.sub x p q, VG.Proof.X25519.X86.sub x p' q'] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, VG.Proof.X25519.X86.sub_sub hx h1 h2 h5⟩

/-! ## Loading a table entry into slots 4–7 -/

theorem pointFromTableQ_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {o : Nat}
    (hp : s.gpr .edx = x + BitVec.ofNat 32 o) (hlo : 320 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTableQ) s fun t =>
      IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧ point (env t.mem x) 4 5 6 7 = tablePoint s.mem x o ∧
      ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem x i = env s.mem x i := by
  have hb : s.gpr .edi = x + BitVec.ofNat 32 0 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hc.edi
  refine WP.mono (copyWorkspaceWords_ok hc .edx .edi (by decide) (by decide) o 0 0 192 32
    hp hb (by omega) (by decide) (Or.inr (by omega)) 32 (Nat.le_refl _)) fun t ⟨hk, hv⟩ => ?_
  have hf : VG.Frame [VG.Proof.X25519.X86.sub x 192 128] s.mem t.mem := by simpa only [Nat.zero_add] using hk.frame
  refine ⟨⟨hk.gpr _ (by decide), hk.gpr _ (by decide), hk.rd, hk.wr,
    VG.Proof.X25519.X86.frameWiden hf hc.fit (by decide) (by decide) (by decide)⟩, hk.gpr _ (by decide), ?_, fun i hi => ?_⟩
  · have := table_point_of_words (m := s.mem) (m' := t.mem) (x := x) (a := o) (o := 192)
      (fun k hk' => by simpa only [Nat.zero_add, Nat.add_zero] using hv k hk')
    exact this
  · have hl := i.isLt
    exact congrArg VG.Proof.X25519.toFe (VG.Proof.X25519.X86.fe_frame1 hf hc.fit (by decide)
      (by simp only [offset]; omega) (by simp only [offset]; omega))

theorem pointTableQ_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (o : Nat)
    (hlo : 320 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableQ o)) s fun t =>
      IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧ point (env t.mem x) 4 5 6 7 = tablePoint s.mem x o ∧
      ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem x i = env s.mem x i := by
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.tablePointer_ok hc o) fun a ⟨ka, ma, pa⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86.pointFromTableQ_ok (ka.ctx hc) pa hlo hn) fun t ⟨kt, et, pt, ht⟩ => ?_
  exact ⟨(IKeep.of_mem ka ma).trans kt, et.trans ka.esi, by rw [pt, ma],
    fun i hi => by rw [ht i hi, ma]⟩

/-! ## `[i]A` -/

/-- The table of `A`'s multiples, with `n` entries and `[n]A` in slots 0–3. -/
structure ATableInv (x : BitVec 32) (s₀ : State) (A : Spec.Ed25519.Point) (Aa : EPoint dZ)
    (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 15
  ctx : VG.Proof.Ed25519.X86.Ctx x s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  d : env s.mem x 16 = Spec.Ed25519.d
  value : Rep (point (env s.mem x) 0 1 2 3) (n • Aa)
  table : ∀ j < n, Rep (tablePoint s.mem x (1024 + 128 * j)) ((j + 1) • Aa)
  a : tablePoint s.mem x 7680 = A
  keep : ScalarKeep s₀ s
  frame : VG.Frame [VG.Proof.X25519.X86.sub x 64 864, VG.Proof.X25519.X86.sub x 1024 1920] s₀.mem s.mem

theorem aTableInit_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {A : Spec.Ed25519.Point}
    {Aa : EPoint dZ} (hA : Rep A Aa) (ha : tablePoint s.mem x 7680 = A)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (.block aTableInit) s (VG.Proof.Ed25519.X86.ATableInv x s A Aa 1) := by
  rw [aTableInit, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.pointTableRead_ok hc 7680 (by decide) (by decide)) fun a ⟨ka, pa, ha'⟩ => ?_
  have ca := ka.ctx hc
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.pointTableWrite_ok ca 1024 (by decide) (by decide)) fun b ⟨kb, fb, pb⟩ => ?_
  refine Wp.wp_movi fun t ht => WP.block_nil ?_
  have mt : t.mem = b.mem := ht.mem
  have eb : env b.mem x = env a.mem x := table_env hc.fit fb (by decide) (by decide)
  have fab : VG.Frame [VG.Proof.X25519.X86.sub x 64 864, VG.Proof.X25519.X86.sub x 1024 1920] s.mem t.mem := by
    rw [mt]
    exact (VG.Proof.Ed25519.X86.frame1_two ka.frame hc.fit (by decide) (by decide) (by decide)).trans
      (VG.Proof.Ed25519.X86.frame1_two' fb hc.fit (by decide) (by decide) (by decide))
  refine ⟨by decide, by decide, (ka.keep.ctx hc).keep (by rw [ht.other _ (by decide), kb.edi])
    (by rw [ht.wr, kb.wr]), ht.gpr, ?_, ?_, ?_, ?_, ?_, fab⟩
  · rw [mt, eb, ha' 16 (by decide), hd]
  · rw [mt, eb, pa, ha, one_nsmul]; exact hA
  · intro j hj
    obtain rfl : j = 0 := by omega
    rw [mt, Nat.mul_zero, Nat.add_zero, pb, pa, ha, zero_add, one_nsmul]; exact hA
  · rw [VG.Proof.Ed25519.X86.tablePoint_frame2 fab hc.fit (by decide) (by decide) (by decide) (Or.inr (by decide))
      (Or.inr (by decide))]
    exact ha
  · exact ⟨by rw [ht.other _ (by decide), kb.edi, ka.keep.edi], by rw [ht.other _ (by decide), kb.esp,
      ka.keep.esp], by rw [ht.rd, kb.rd, ka.keep.rd], by rw [ht.wr, kb.wr, ka.keep.wr]⟩

theorem esiNext_ok {s : State} {n m : Nat} (hn : n + 1 < 2 ^ 32) (hm : m < 2 ^ 32)
    (h : s.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (.block [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm (BitVec.ofNat 32 m))]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (n + 1) ∧ t.zf = some (decide (n + 1 = m)) ∧
      t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = s.mem := by
  refine Wp.wp_addi fun u hu => Wp.wp_cmpi fun t ht _ zt => WP.block_nil ?_
  have e : u.gpr .esi = BitVec.ofNat 32 (n + 1) := by rw [hu.gpr, h, BitVec.ofNat_add]; rfl
  refine ⟨by rw [ht.gpr, e], ?_, by rw [ht.gpr, hu.other .edi (by decide)],
    by rw [ht.gpr, hu.other .esp (by decide)], by rw [ht.rd, hu.rd], by rw [ht.wr, hu.wr],
    by rw [ht.mem, hu.mem]⟩
  rw [zt, e, Wp.sub_beq hn hm]

theorem aTableBody_ok {x : BitVec 32} {s₀ s : State} {A : Spec.Ed25519.Point} {Aa : EPoint dZ}
    {n : Nat} (hn : n < 15) (hA : Rep A Aa) (h : VG.Proof.Ed25519.X86.ATableInv x s₀ A Aa n s) :
    WP isa (.block aTableBody) s fun t => t.zf = some (decide (n + 1 = 15)) ∧
      VG.Proof.Ed25519.X86.ATableInv x s₀ A Aa (n + 1) t := by
  have hc := h.ctx
  have hfit := hc.fit
  rw [aTableBody, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.pointTableQ_ok hc 7680 (by decide) (by decide)) fun a ⟨ka, ea, pa, ha⟩ => ?_
  have ca := ka.ctx hc
  rw [WP.block_append_iff]
  refine WP.mono (pointAdd_ok ca ((ha 16 (Or.inr (by decide))).trans h.d)) fun b ⟨kb, pb, hb⟩ => ?_
  have cb := kb.ctx ca
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok cb 1024 n (by omega) (by rw [kb.keep.esi, ea, h.counter]))
    fun c ⟨kc, mc, pc⟩ => ?_
  have cc := kc.ctx cb
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok cc pc (by omega) (by omega)) fun d ⟨kd, pd⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86.esiNext_ok (m := 15) (by omega) (by decide)
    (by rw [kd.gpr _ (by decide), kc.esi, kb.keep.esi, ea, h.counter])) fun t ⟨te, tz, tedi, tesp, trd, twr, tm⟩ =>
      ⟨tz, ?_⟩
  have fab : VG.Frame [VG.Proof.X25519.X86.sub x 64 864, VG.Proof.X25519.X86.sub x 1024 1920] s.mem c.mem := by
    rw [mc]; exact (VG.Proof.Ed25519.X86.frame1_two ka.frame hfit (by decide) (by decide) (by decide)).trans
      (VG.Proof.Ed25519.X86.frame1_two kb.frame hfit (by decide) (by decide) (by decide))
  have fd : VG.Frame [VG.Proof.X25519.X86.sub x 64 864, VG.Proof.X25519.X86.sub x 1024 1920] c.mem d.mem :=
    VG.Proof.Ed25519.X86.frame1_two' kd.frame hfit (by omega) (by omega) (by omega)
  have fall : VG.Frame [VG.Proof.X25519.X86.sub x 64 864, VG.Proof.X25519.X86.sub x 1024 1920] s.mem t.mem := by rw [tm]; exact fab.trans fd
  have crep : Rep (point (env c.mem x) 0 1 2 3) ((n + 1) • Aa) := by
    rw [mc, pb, pa, h.a, succ_nsmul]
    have : point (env a.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
      simp only [point, ha 0 (Or.inl (by decide)), ha 1 (Or.inl (by decide)), ha 2 (Or.inl (by decide)),
        ha 3 (Or.inl (by decide))]
    rw [this]
    exact pointAdd_rep h.value hA
  refine ⟨by omega, by omega, ?_, te, ?_, ?_, fun j hj => ?_, ?_, ?_, h.frame.trans fall⟩
  · exact hc.keep (by rw [tedi, kd.gpr _ (by decide), kc.edi, kb.keep.edi, ka.edi])
      (by rw [twr, kd.wr, kc.wr, kb.keep.wr, ka.wr])
  · rw [tm, table_env hfit kd.frame (by omega) (by omega), mc, hb 16 (by decide),
      ha 16 (Or.inr (by decide))]
    exact h.d
  · rw [tm, table_env hfit kd.frame (by omega) (by omega)]; exact crep
  · rw [tm]
    by_cases hjn : j < n
    · rw [tablePoint_frame hfit kd.frame (by omega) (by omega) (Or.inl (by omega)), mc,
        tablePoint_frame hfit kb.frame (by decide) (by omega) (Or.inr (by omega)),
        tablePoint_frame hfit ka.frame (by decide) (by omega) (Or.inr (by omega))]
      exact h.table j hjn
    · obtain rfl : j = n := by omega
      rw [pd]; exact crep
  · rw [tm, tablePoint_frame hfit kd.frame (by omega) (by omega) (Or.inr (by omega)), mc,
      tablePoint_frame hfit kb.frame (by decide) (by decide) (Or.inr (by decide)),
      tablePoint_frame hfit ka.frame (by decide) (by decide) (Or.inr (by decide))]
    exact h.a
  · exact ⟨by rw [tedi, kd.gpr _ (by decide), kc.edi, kb.keep.edi, ka.edi, h.keep.edi],
      by rw [tesp, kd.gpr _ (by decide), kc.esp, kb.keep.esp, ka.esp, h.keep.esp],
      by rw [trd, kd.rd, kc.rd, kb.keep.rd, ka.rd, h.keep.rd],
      by rw [twr, kd.wr, kc.wr, kb.keep.wr, ka.wr, h.keep.wr]⟩

theorem aTable_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {A : Spec.Ed25519.Point}
    {Aa : EPoint dZ} (hA : Rep A Aa) (ha : tablePoint s.mem x 7680 = A)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa aTable s (VG.Proof.Ed25519.X86.ATableInv x s A Aa 15) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.aTableInit_ok hc hA ha hd) fun b (hb : VG.Proof.Ed25519.X86.ATableInv x s A Aa (15 - 14) b) => ?_)
  refine WP.loop (M := isa) (Inv := fun m t => VG.Proof.Ed25519.X86.ATableInv x s A Aa (15 - m) t ∧ 0 < m ∧ m ≤ 14) ?_ 14 b
    ⟨hb, by decide, by decide⟩
  intro m u ⟨hu, hm0, hm⟩
  refine WP.mono (VG.Proof.Ed25519.X86.aTableBody_ok (n := 15 - m) (by omega) hA hu) fun v ⟨zv, hv⟩ => ?_
  by_cases h1 : m = 1
  · subst m
    exact .inl ⟨by show v.zf.map (!·) = _; rw [zv]; rfl, hv⟩
  · refine .inr ⟨by show v.zf.map (!·) = _; rw [zv, decide_eq_false (by omega)]; rfl, m - 1, by omega,
      ?_, by omega, by omega⟩
    rw [show 15 - (m - 1) = 15 - m + 1 by omega]; exact hv

/-! ## `-[i]B` -/

theorem negBase_rep (i : Nat) (hi : i < 15) : Rep (negBase i) ((i + 1) • (-baseAff)) := by
  rw [smul_neg]; exact (baseMultiple_rep i hi).neg

theorem bEntry_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (i : Nat) (hi : i < 15) :
    WP isa (.block (bEntry i)) s fun t => ScalarKeep s t ∧
      VG.Frame [VG.Proof.X25519.X86.sub x 64 864, VG.Proof.X25519.X86.sub x (3072 + 128 * i) 128] s.mem t.mem ∧
      tablePoint t.mem x (3072 + 128 * i) = negBase i ∧ env t.mem x 16 = env s.mem x 16 := by
  rw [bEntry, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hc) fun a ⟨ka, ea⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86.pointTableWrite_ok (ka.ctx hc) (3072 + 128 * i) (by omega) (by omega))
    fun t ⟨kt, ft, pt⟩ => ⟨(Keep.scalar ka.keep).trans kt, ?_, ?_, ?_⟩
  · exact (VG.Proof.Ed25519.X86.frame1_two ka.frame hc.fit (by decide) (by decide) (by decide)).trans
      (VG.Proof.Ed25519.X86.frame1_two' ft hc.fit (by omega) (by omega) (by omega))
  · rw [pt, ea, constPoint_eval]
  · rw [table_env hc.fit ft (by omega) (by omega), ea]; rfl

theorem bEntries_ok {x : BitVec 32} (l : List Nat) (hl : ∀ i ∈ l, i < 15) (hnd : l.Nodup) :
    ∀ {s : State}, VG.Proof.Ed25519.X86.Ctx x s → WP isa (bEntries l) s fun t => ScalarKeep s t ∧
      VG.Frame [VG.Proof.X25519.X86.sub x 64 864, VG.Proof.X25519.X86.sub x 3072 1920] s.mem t.mem ∧
      (∀ i ∈ l, tablePoint t.mem x (3072 + 128 * i) = negBase i) ∧
      (∀ j < 15, j ∉ l → tablePoint t.mem x (3072 + 128 * j) = tablePoint s.mem x (3072 + 128 * j)) ∧
      env t.mem x 16 = env s.mem x 16 := by
  induction l with
  | nil => exact fun _ => WP.block_nil ⟨ScalarKeep.refl _, Frame.refl _ _, fun _ h => absurd h List.not_mem_nil,
      fun _ _ _ => rfl, rfl⟩
  | cons i is ih =>
    intro s hc
    have hi := hl i List.mem_cons_self
    have hnd' := List.nodup_cons.mp hnd
    rw [bEntries]
    refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.bEntry_ok hc i hi) fun a ⟨ka, fa, pa, da⟩ => ?_)
    have ca : VG.Proof.Ed25519.X86.Ctx x a := hc.keep ka.edi ka.wr
    refine WP.mono (ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) hnd'.2 ca)
      fun t ⟨kt, ft, et, ot, dt⟩ => ⟨ka.trans kt, ?_, fun j hj => ?_, fun j hj hjn => ?_, dt.trans da⟩
    · exact (VG.Proof.Ed25519.X86.frame2_widen fa hc.fit (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega) (by decide)
        (by omega)).trans ft
    · rcases List.mem_cons.mp hj with rfl | hj
      · rw [ot j hi hnd'.1, pa]
      · exact et j hj
    · rw [ot j hj (fun h => hjn (List.mem_cons_of_mem _ h)),
        VG.Proof.Ed25519.X86.tablePoint_frame2 fa hc.fit (by decide) (by omega) (by omega) (Or.inr (by omega))
          (by have : j ≠ i := fun e => hjn (e ▸ List.mem_cons_self); omega)]

theorem bTable_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa bTable s fun t => ScalarKeep s t ∧ VG.Frame [VG.Proof.X25519.X86.sub x 64 864, VG.Proof.X25519.X86.sub x 3072 1920] s.mem t.mem ∧
      (∀ i < 15, Rep (tablePoint t.mem x (3072 + 128 * i)) ((i + 1) • (-baseAff))) ∧
      env t.mem x 16 = env s.mem x 16 := by
  refine WP.mono (VG.Proof.Ed25519.X86.bEntries_ok (List.range 15) (fun i hi => List.mem_range.mp hi) List.nodup_range hc)
    fun t ⟨kt, ft, et, _, dt⟩ => ⟨kt, ft, fun i hi => ?_, dt⟩
  rw [et i (List.mem_range.mpr hi)]; exact VG.Proof.Ed25519.X86.negBase_rep i hi

end VG.Proof.Ed25519.X86

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyCTInputs`. -/
section

/-! Merged from `Proof.Ed25519.X86.RecoverCTRoot`. -/
section
/-! Merged from `Proof.Ed25519.X86.RecoverCTSign`. -/
section
/-! Merged from `Proof.Ed25519.X86.RecoverCTAdjust`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def SignCTPre (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  VG.Proof.Ed25519.X86.Ctx base s ∧ s.gpr .esi = signWord b ∧ env s.mem base 0 = x

theorem parityBlock_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.X86.Ctx base s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa (.block (Impl.X25519.X86.freeze 64 ++ recoverParity)) s fun t =>
      FieldKeep base s t ∧ t.zf = some (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hs 0) fun a ⟨ka, _, va⟩ => ?_
  refine WP.mono (recoverParity_ok (ka.ctx hs) b (ka.keep.esi.trans hb)) fun t ⟨kt, _, tz⟩ => ?_
  refine ⟨ka.trans kt, ?_⟩
  change VG.Proof.X25519.X86.fe a.mem base 64 = _ at va
  rw [tz, va]

theorem adjustTail_ct (base : BitVec 32) :
    RelCT isa (fun s t => VG.Proof.Ed25519.X86.Ctx base s ∧ VG.Proof.Ed25519.X86.Ctx base t ∧ s.zf = t.zf)
      (.seq (.ite .e (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0])))
        (.block recoverSuccess)) (fun _ _ => True) := by
  refine VG.RelCT.seq (M := isa) (R := fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
    (VG.RelCT.ite (fun _ _ h => h.2.2) ?_ ?_) (successBlock_ct base)
  · intro s t ts tt s' t' h es et
    rw [Exec.block_iff] at es et
    change some (s, []) = some (s', ts) at es
    change some (t, []) = some (t', tt) at et
    cases es; cases et
    exact ⟨rfl, h.1.1.edi, h.1.2.1.edi⟩
  · have ct := (negateBlock_ct base).mono
      (P' := fun (s t : State) => (VG.Proof.Ed25519.X86.Ctx base s ∧ VG.Proof.Ed25519.X86.Ctx base t ∧ s.zf = t.zf) ∧ isa.eval .e s = some false)
      (fun _ _ h => ⟨h.1.1.edi, h.1.2.1.edi⟩) (fun _ _ h => h)
    have hwp := ct.wp (fun _ _ h =>
      ⟨WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.1) (fun _ k => (k.1.ctx h.1.1).edi),
       WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.2.1) (fun _ k => (k.1.ctx h.1.2.1).edi)⟩)
    exact hwp.mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem recoverAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      recoverAdjustSign (fun _ _ => True) := by
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (Impl.X25519.X86.freeze 64 ++ recoverParity)) s fun t =>
        VG.Proof.Ed25519.X86.Ctx base t ∧ t.zf = some ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlock_ok h.1 b h.2.1) fun t ⟨kt, tz⟩ => ?_
    exact ⟨kt.ctx h.1, by rw [tz, h.2.2]⟩
  have ht := (parityBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.edi, h.2.1.edi⟩)
    (fun _ _ h => h)
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverAdjustSign]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)) (adjustTail_ct base)

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem testThenSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block [.alu .test .esi (.reg .esi)]) (.ite .ne recoverInvalid recoverAdjustSign))
      (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block [.alu .test .esi (.reg .esi)]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block [.alu .test .esi (.reg .esi)]) s fun t =>
        SignCTPre base b x t ∧ isa.eval .ne t = some b := by
    refine WP.mono (signTest_ok base b h.2.1) fun t ⟨kt, mt, zt⟩ => ?_
    exact ⟨⟨kt.ctx h.1, kt.keep.esi.trans h.2.1, by rw [mt]; exact h.2.2⟩, zt⟩
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

theorem recoverSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      recoverSign (fun _ _ => True) := by
  have ht := (zeroBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.edi, h.2.1.edi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldZero 0)) s fun t =>
        SignCTPre base b x t ∧ t.zf = some (decide (x = 0)) := by
    refine WP.mono (fieldZero_ok h.1 0) fun t ⟨kt, et, zt⟩ => ?_
    exact ⟨⟨kt.ctx h.1, kt.keep.esi.trans h.2.1, by rw [et]; exact h.2.2⟩,
      by rw [zt, h.2.2]⟩
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverSign]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (testThenSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

end VG.Proof.Ed25519.X86
end

/-! The two square-root checks branch on public field values. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

def RootCTState (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  SignCTPre base b (rootX y) s ∧
    env s.mem base 11 = rootV y * rootX y * rootX y ∧
    env s.mem base 6 = rootU y ∧ env s.mem base 12 = 0 - rootU y

def rootCheckValue (y : Spec.X25519.Fe) (minus : Bool) : Bool :=
  decide (rootV y * rootX y * rootX y = if minus then 0 - rootU y else rootU y)

theorem rootCheck_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (minus : Bool) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual 11 (if minus then 12 else 6)))
      (fun s t => (RootCTState base b y s ∧ s.zf = some (rootCheckValue y minus)) ∧
        (RootCTState base b y t ∧ t.zf = some (rootCheckValue y minus))) := by
  have ht : RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual 11 (if minus then 12 else 6))) (fun _ _ => True) := by
    cases minus
    · apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
      exact fun _ _ h => edi_agree h.1.1.1.edi h.2.1.1.edi
    · apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
      exact fun _ _ h => edi_agree h.1.1.1.edi h.2.1.1.edi
  have hw (s : State) (h : RootCTState base b y s) :
      WP isa (.block (fieldEqual 11 (if minus then 12 else 6))) s fun t =>
        RootCTState base b y t ∧ t.zf = some (rootCheckValue y minus) := by
    refine WP.mono (fieldEqual_ok h.1.1 11 (if minus then 12 else 6)) fun t ⟨kt, te, tz⟩ => ?_
    refine ⟨⟨⟨kt.ctx h.1.1, kt.keep.esi.trans h.1.2.1,
      (te 0 (by decide)).trans h.1.2.2⟩, (te 11 (by decide)).trans h.2.1,
      (te 6 (by decide)).trans h.2.2.1, (te 12 (by decide)).trans h.2.2.2⟩, ?_⟩
    rw [tz, rootCheckValue, h.2.1]
    cases minus <;> simp only [Bool.false_eq_true, ite_false, ite_true, h.2.2.1, h.2.2.2]
  exact (VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem rootAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign)
      (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) s fun t =>
        SignCTPre base b (x * Spec.Ed25519.sqrtM1) t := by
    refine WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] h.1) fun t ⟨kt, te⟩ => ?_
    refine ⟨kt.ctx h.1, kt.keep.esi.trans h.2.1, ?_⟩
    rw [te]
    change env s.mem base 0 * Spec.Ed25519.sqrtM1 = _
    rw [h.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (recoverSign_ct base b (x * Spec.Ed25519.sqrtM1))

theorem recoverMinus_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual 11 12)) (.ite .e
        (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid))
      (fun _ _ => True) := by
  refine VG.RelCT.seq (rootCheck_ct base b y true) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (rootAdjustSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem recoverChecks_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual 11 6)) (.ite .e recoverSign
        (.seq (.block (fieldEqual 11 12)) (.ite .e
          (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid))))
      (fun _ _ => True) := by
  refine VG.RelCT.seq (rootCheck_ct base b y false) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (recoverSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact (recoverMinus_ct base b y).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)


end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointDecodeCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.RecoverCTPoint`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def RecoverCTPre (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  VG.Proof.Ed25519.X86.Ctx base s ∧ VG.Proof.X25519.X86.wd s.mem base 32 = signWord b ∧ env s.mem base 1 = y

private def CandidateCTState (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  VG.Proof.Ed25519.X86.Ctx base s ∧ VG.Proof.X25519.X86.wd s.mem base 32 = signWord b ∧ env s.mem base 0 = rootX y ∧
    env s.mem base 11 = rootV y * rootX y * rootX y ∧
    env s.mem base 6 = rootU y ∧ env s.mem base 12 = 0 - rootU y

theorem recoverPoint_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RecoverCTPre base b y s ∧ RecoverCTPre base b y t)
      recoverPoint (fun _ _ => True) := by
  have ht := (recoverCandidate_ct base).mono
    (fun _ _ (h : RecoverCTPre base b y _ ∧ RecoverCTPre base b y _) => ⟨h.1.1.edi, h.2.1.edi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : RecoverCTPre base b y s) :
      WP isa recoverCandidate s (CandidateCTState base b y) := by
    refine WP.mono (recoverCandidate_ok h.1) fun t ⟨kt, tx, _, _, tu, _, tv, tn⟩ => ?_
    refine ⟨kt.ctx h.1, (kt.word h.1 32 (by decide)).trans h.2.1, ?_, ?_, ?_, ?_⟩
    · rw [tx, h.2.2]
    · rw [tv, h.2.2]
    · rw [tu, h.2.2]
    · rw [tn, h.2.2]
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have loadct : RelCT isa (fun s t => CandidateCTState base b y s ∧ CandidateCTState base b y t)
      (.block [.mov .esi (.mem (Impl.X25519.X86.sc 32))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have loadwp (s : State) (h : CandidateCTState base b y s) :
      WP isa (.block [.mov .esi (.mem (Impl.X25519.X86.sc 32))]) s (RootCTState base b y) := by
    refine Wp.wp_ldm h.1.edi (h.1.inRW (by decide) (by decide)) fun t kt => WP.block_nil ?_
    have kb : t.gpr .esi = signWord b := kt.gpr.trans h.2.1
    have ke := (IKeep.of_counter kt).ctx h.1
    refine ⟨⟨ke, kb, ?_⟩, ?_, ?_, ?_⟩
    · rw [kt.mem]; exact h.2.2.1
    · rw [kt.mem]; exact h.2.2.2.1
    · rw [kt.mem]; exact h.2.2.2.2.1
    · rw [kt.mem]; exact h.2.2.2.2.2
  have lp := loadct.wp (fun s t h => ⟨loadwp s h.1, loadwp t h.2⟩)
  rw [recoverPoint]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.seq (lp.mono (fun _ _ h => h) (fun _ _ h => h.2)) (recoverChecks_ct base b y))

end VG.Proof.Ed25519.X86
end

/-! Decoding branches only on the shared public compressed point. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def DecodeCTPre (base : BitVec 32) (n : Nat) (s : State) : Prop := VG.Proof.Ed25519.X86.Ctx base s ∧ VG.Proof.X25519.X86.fe s.mem base 96 = n

theorem decodeHeadCT_ok {base : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx base s) :
    WP isa (.block (decodeY ++ canonicalY)) s fun t =>
      RecoverCTPre base (VG.Proof.X25519.X86.fe s.mem base 96 / 2 ^ 255 == 1)
        (VG.Proof.X25519.toFe (VG.Proof.X25519.X86.fe s.mem base 96 % 2 ^ 255)) t ∧
      t.zf = some (decide (VG.Proof.X25519.X86.fe s.mem base 96 % 2 ^ 255 < Spec.X25519.P)) := by
  rw [WP.block_append_iff]
  refine WP.mono (decodeY_ok hc) fun a ⟨ka, ya, ba⟩ => ?_
  have ca := ka.ctx hc
  refine WP.mono (canonicalY_ok ca (by rw [ya]; exact Nat.mod_lt _ (by decide))) fun t ⟨kt, et, bt, zt⟩ => ?_
  refine ⟨⟨kt.ctx ca, ?_, ?_⟩, ?_⟩
  · rw [bt, ba]
    have hn : VG.Proof.X25519.X86.fe s.mem base 96 / 2 ^ 255 ≤ 1 := by
      have hlt := VG.Proof.X25519.X86.fe_lt s.mem base 96
      omega_using [hlt]
    rcases (by omega_using [hn] : fe s.mem base 96 / 2 ^ 255 = 0 ∨ fe s.mem base 96 / 2 ^ 255 = 1) with h | h
    all_goals rw [h]; rfl
  · rw [et]
    change VG.Proof.X25519.toFe (VG.Proof.X25519.X86.fe a.mem base 96) = _
    rw [ya]
  · rw [zt, ya]

theorem pointDecode_ct (base : BitVec 32) (n : Nat) :
    RelCT isa (fun s t => DecodeCTPre base n s ∧ DecodeCTPre base n t) pointDecode (fun _ _ => True) := by
  let b := n / 2 ^ 255 == 1
  let y := VG.Proof.X25519.toFe (n % 2 ^ 255)
  have ht : RelCT isa (fun s t => DecodeCTPre base n s ∧ DecodeCTPre base n t)
      (.block (decodeY ++ canonicalY)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : DecodeCTPre base n s) :
      WP isa (.block (decodeY ++ canonicalY)) s fun t =>
        RecoverCTPre base b y t ∧ t.zf = some (decide (n % 2 ^ 255 < Spec.X25519.P)) := by
    have hh := decodeHeadCT_ok h.1
    rw [h.2] at hh
    exact hh
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [pointDecode]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (recoverPoint_ct base b y).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .eax = signWord p.isSome := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def VerifySaved (s₀ t₀ s t : State) : Prop := VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s ∧ VG.Proof.Ed25519.X86.Saved t₀ (arg t₀ 3) t

structure VerifyCTFacts (s t : State) : Prop where
  left : verifyLocal.pre s
  right : verifyLocal.pre t
  pub : verifyLocal.pub s t

theorem VerifyCTFacts.args {s t : State} (h : VerifyCTFacts s t) (i : Nat) (hi : i < 4) : arg s i = arg t i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  exacts [h.pub.2.1, h.pub.2.2.1, h.pub.2.2.2.1, h.pub.2.2.2.2.1]

theorem loadSlicePointer_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i skip : Nat)
    (hi : i ≤ 2) (hk : skip = 0 ∨ skip = 32) :
    RelCT isa (VerifySaved s₀ t₀) (.block (loadSlicePointer i skip))
      (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi) := by
  have hc : RelCT isa (VerifySaved s₀ t₀) (.block (loadSlicePointer i skip)) (fun _ _ => True) := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    all_goals rcases hk with rfl | rfl
    all_goals
      apply VG.RelCT.taint (A := taint) (regsTaint [.esp]) _ (by taint_decide)
      intro s t hp
      exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
        (hp.1.esp.trans (h.pub.1.trans hp.2.esp.symm)))
  have hp := ctWithRuns hc (fun _ _ hs => ⟨loadSlicePointer_ok (verify_pre h.left).scratch hs.1 (by omega),
    loadSlicePointer_ok (verify_pre h.right).scratch hs.2 (by omega)⟩)
  apply hp.mono (fun _ _ h => h)
  intro s t ⟨_, a, b, _, hs, ht⟩
  exact ⟨hs.1.edi.trans ((h.args 3 (by decide)).trans ht.1.edi.symm),
    hs.2.1.trans ((congrArg (· + BitVec.ofNat 32 skip) (h.args i (by omega))).trans ht.2.1.symm)⟩

theorem copyWords96_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
    (.block (copyWords 96 8)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
  intro s t h
  apply regsTaint_agree
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h.1, h.2]

theorem inputSlice96_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i : Nat) (hi : i ≤ 2) :
    RelCT isa (VerifySaved s₀ t₀) (.block (inputSliceWords i 0 96 8)) (fun _ _ => True) := by
  exact ctBlockAppend (loadSlicePointer_ct h i 0 hi (Or.inl rfl)) copyWords96_ct

theorem verifyScalar_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀) (.block verifyScalar) (fun _ _ => True) := by
  have hc : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (copyWords 64 8 ++ scalarSubtract ++ ([.alu .test .ebx (.reg .ebx)] : List Instr))) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2]
  simp only [verifyScalar, inputSliceWords, List.append_assoc]
  exact ctBlockAppend (loadSlicePointer_ct h 1 32 (by decide) (Or.inr rfl)) hc

theorem verifyFinish_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi)
    (.block verifyFinish) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  intro s t h
  exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)

end VG.Proof.Ed25519.X86

end
