module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Mask
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# Preparing to sample (x86)

`prepare` clears the 32 bytes of the scalar, scans q, and stores the address
of its significant bytes (`oQ`), their count (`oWidth`) and the leading
byte's mask (`oMask`); `eax = 1` exactly when q > 1 (`Prepared`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-! ## Clearing the scalar -/

/-- The memory after clearing the first `k` words of the scalar. -/
def clearMem (m : Mem) (B : Addr) : Nat → Mem
  | 0 => m
  | k + 1 => (clearMem m B k).writeW (off B (oNonce + 4 * k)) (0 : BitVec 32)

theorem zeroWord_at (m : Mem) (B : Addr) (d i : Nat) (hi : i < 4) :
    (m.writeW (off B d) (0 : BitVec 32)) (off B (d + i)) = 0 := by
  have he : off B (d + i) = off B d + BitVec.ofNat 64 i := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [he]
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, Mem.sub_ofNat_toNat (off B d) (i := i) (by omega),
    show 32 / 8 = 4 from rfl, hi, ite_true]
  exact BitVec.extractLsb'_zero

theorem clearMem_outside (m : Mem) (B : Addr) : ∀ k, k ≤ 8 → Outside B oNonce 32 m (clearMem m B k)
  | 0, _ => Outside.refl _ _ _ _
  | k + 1, hk => (clearMem_outside m B k (by omega)).trans
      ((writeW32_outside _ B (d := oNonce + 4 * k) 0 (by unfold oNonce; omega)).mono
        (by unfold oNonce; omega) (by unfold oNonce; omega))

theorem clearMem_zero (m : Mem) (B : Addr) : ∀ k, k ≤ 8 → ∀ i < 4 * k, clearMem m B k (off B (oNonce + i)) = 0
  | 0, _, i, hi => absurd hi (by omega)
  | k + 1, hk, i, hi => by
    by_cases hlo : i < 4 * k
    · rw [clearMem, writeW32_outside _ B (d := oNonce + 4 * k) 0 (by unfold oNonce; omega) _
        (by rw [ofs_off0 B (by unfold oNonce; omega)]; omega)]
      exact clearMem_zero m B k (by omega) i hlo
    · rw [clearMem, show oNonce + i = oNonce + 4 * k + (i - 4 * k) by omega]
      exact zeroWord_at _ B _ _ (by omega)

theorem clearMem_frame (s₀ : State) (m : Mem) : ∀ k, k ≤ 8 → Frame [rStack s₀] m (clearMem m (rBase s₀) k)
  | 0, _ => Frame.refl _ _
  | k + 1, hk => (clearMem_frame s₀ m k (by omega)).trans
      (frame_store s₀ _ (d := oNonce + 4 * k) (by unfold oNonce KeyRandom.frameBytes; omega) 0)

theorem clearNonce_ok {s : State} {B : Addr} (hf : RF s B) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RF t B → t.mem = clearMem s.mem B 8 → Keeps [.eax] s t → t.gpr .eax = 0 →
      WP isa (.block is) t Q) :
    WP isa (.block (clearNonce ++ is)) s Q := by
  unfold clearNonce
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun u₀ v₀ _ => ?_
  have z₀ : u₀.gpr .eax = 0 := v₀.gpr
  refine wp_slot (hf.of_keeps v₀.keeps) (by decide) z₀ fun u₁ f₁ m₁ g₁ r₁ w₁ _ _ =>
    wp_slot f₁ (by decide) (v := 0) (by rw [g₁]; exact z₀) fun u₂ f₂ m₂ g₂ r₂ w₂ _ _ =>
    wp_slot f₂ (by decide) (v := 0) (by rw [g₂, g₁]; exact z₀) fun u₃ f₃ m₃ g₃ r₃ w₃ _ _ =>
    wp_slot f₃ (by decide) (v := 0) (by rw [g₃, g₂, g₁]; exact z₀) fun u₄ f₄ m₄ g₄ r₄ w₄ _ _ =>
    wp_slot f₄ (by decide) (v := 0) (by rw [g₄, g₃, g₂, g₁]; exact z₀) fun u₅ f₅ m₅ g₅ r₅ w₅ _ _ =>
    wp_slot f₅ (by decide) (v := 0) (by rw [g₅, g₄, g₃, g₂, g₁]; exact z₀) fun u₆ f₆ m₆ g₆ r₆ w₆ _ _ =>
    wp_slot f₆ (by decide) (v := 0) (by rw [g₆, g₅, g₄, g₃, g₂, g₁]; exact z₀) fun u₇ f₇ m₇ g₇ r₇ w₇ _ _ =>
    wp_slot f₇ (by decide) (v := 0) (by rw [g₇, g₆, g₅, g₄, g₃, g₂, g₁]; exact z₀) fun u₈ f₈ m₈ g₈ r₈ w₈ _ _ => ?_
  refine k u₈ f₈ ?_ ⟨fun r hr => ?_, ?_, ?_⟩ (by rw [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁]; exact z₀)
  · rw [m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁, v₀.mem]; rfl
  · rw [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁, v₀.other r (by simpa using hr)]
  · rw [r₈, r₇, r₆, r₅, r₄, r₃, r₂, r₁, v₀.rd]
  · rw [w₈, w₇, w₆, w₅, w₄, w₃, w₂, w₁, v₀.wr]

/-! ## Preparing -/

/-- What `prepare` leaves, with q > 1. -/
structure Prepared (s₀ u : State) : Prop where
  ready : Ready s₀ u
  q : slot u.mem (rBase s₀) oQ = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀)
  width : slot u.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)
  mask : slot u.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat
  nonce : ∀ i < 32, u.mem (off (rBase s₀) (oNonce + i)) = 0

theorem add_ofNat_sub32 (a : BitVec 32) {k d : Nat} (hd : d ≤ k) (hk : k < 2 ^ 32) :
    a + BitVec.ofNat 32 k - BitVec.ofNat 32 d = a + BitVec.ofNat 32 (k - d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := a.isLt
  rw [Nat.mod_eq_of_lt (a := k) hk, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (a := k - d) (by omega)]
  omega

theorem prepare_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    WP isa prepare t fun u =>
      u.gpr .eax = (if 1 < Spec.Dsa.decodeBE (rQBytes s₀) then 1 else 0) ∧
      ((1 < Spec.Dsa.decodeBE (rQBytes s₀)) → Prepared s₀ u) ∧ Ready s₀ u ∧
      Outs (rBase s₀) [(oQ, 12), (oNonce, 32)] t.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] t u := by
  have hfit := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  unfold prepare
  refine WP.seq (clearNonce_ok h.rf fun t₁ f₁ m₁ k₁ _ => ?_)
  have h₁ : Ready s₀ t₁ := h.congr k₁ (by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide))
  refine wp_movS (h₁.argSrc A (j := 3) (by decide)) fun t₂ u₂ _ => ?_
  have h₂ := h₁.upd u₂ (by decide)
  refine wp_addS (h₂.argSrc A (j := 5) (by decide)) fun t₃ u₃ _ => ?_
  have h₃ := h₂.upd u₃ (by decide)
  refine wp_movS (h₃.argSrc A (j := 6) (by decide)) fun t₄ u₄ _ => WP.block_nil ?_
  have h₄ := h₃.upd u₄ (by decide)
  have e6 : X86.arg s₀ 6 = BitVec.ofNat 32 (rQBytes s₀).length := by
    rw [hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have esi₄ : t₄.gpr .esi = rQ s₀ := by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]; rfl
  have ecx₄ : t₄.gpr .ecx = BitVec.ofNat 32 (rQBytes s₀).length := by rw [u₄.gpr, e6]
  refine WP.seq (WP.mono (significant_ok esi₄ ecx₄ (h₄.q A) (rQBytes_pos A) (by omega))
    fun t₅ ⟨bx₅, dx₅, m₅, k₅⟩ => ?_)
  have h₅ : Ready s₀ t₅ := h₄.congr k₅ (by rw [m₅]; exact Frame.refl _ _)
  refine WP.seq (wp_movS (h₅.argSrc A (j := 3) (by decide)) fun t₆ u₆ _ => ?_)
  have h₆ := h₅.upd u₆ (by decide)
  refine wp_addS (h₆.argSrc A (j := 5) (by decide)) fun t₇ u₇ _ => ?_
  have h₇ := h₆.upd u₇ (by decide)
  refine wp_addS (h₇.argSrc A (j := 6) (by decide)) fun t₈ u₈ _ => ?_
  have h₈ := h₇.upd u₈ (by decide)
  refine wp_subS rfl fun t₉ u₉ _ => ?_
  have h₉ := h₈.upd u₉ (by decide)
  have ebx₉ : t₉.gpr .ebx = BitVec.ofNat 32 (rWidth s₀) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), bx₅]
  have esi₉ : t₉.gpr .esi = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀) := by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, u₈.other .ebx (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), bx₅, e6, add_ofNat_sub32 _ hfit (by omega)]
    rfl
  refine wp_slot h₉.rf (by decide) esi₉ fun t₁₀ f₁₀ m₁₀ g₁₀ r₁₀ w₁₀ _ _ => ?_
  refine wp_slot f₁₀ (by decide) (v := BitVec.ofNat 32 (rWidth s₀)) (by rw [g₁₀]; exact ebx₉)
    fun t₁₁ f₁₁ m₁₁ g₁₁ r₁₁ w₁₁ _ _ => WP.block_nil ?_
  have edx₁₁ : t₁₁.gpr .edx = (rLead s₀).setWidth 32 := by
    rw [g₁₁, g₁₀, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), dx₅]
  refine WP.mono (prepareFinish_ok f₁₁ (w := rWidth s₀) (b := rLead s₀) (show (VG.Proof.Dsa.significant (rQBytes s₀)).1 < 2 ^ 32 by omega)
    (by rw [g₁₁, g₁₀]; exact ebx₉) edx₁₁) fun u ⟨ax, mu, ku⟩ => ?_
  -- Memory.
  have m₉ : t₉.mem = clearMem t.mem (rBase s₀) 8 := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅, u₄.mem, u₃.mem, u₂.mem, m₁]
  have mu' : u.mem = (((clearMem t.mem (rBase s₀) 8).writeW (off (rBase s₀) oQ)
      (rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))).writeW (off (rBase s₀) oWidth)
      (BitVec.ofNat 32 (rWidth s₀))).writeW (off (rBase s₀) oMask) (maskValue (rLead s₀).toNat) := by
    rw [mu, m₁₁, m₁₀, m₉]
  have kregs : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] t u := by
    refine (((((k₁.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))).trans (k₅.mono (by decide))).trans ?_
    refine (((((u₆.keeps.mono (by decide)).trans (u₇.keeps.mono (by decide))).trans
      (u₈.keeps.mono (by decide))).trans (u₉.keeps.mono (by decide))).trans
      ⟨fun r _ => by rw [g₁₁, g₁₀], by rw [r₁₁, r₁₀], by rw [w₁₁, w₁₀]⟩).trans (ku.mono (by decide))
  have hu : Ready s₀ u := h₉.congr (rs := [.eax, .ebp])
    ⟨fun r hr => by rw [ku.1 r hr, g₁₁, g₁₀], by rw [ku.2.1, r₁₁, r₁₀], by rw [ku.2.2, w₁₁, w₁₀]⟩
    (by rw [mu, m₁₁, m₁₀]
        exact ((frame_store s₀ _ (by decide) _).trans (frame_store s₀ _ (by decide) _)).trans
          (frame_store s₀ _ (by decide) _))
  have e := VG.Proof.Dsa.random_valid_scan_ge (rQBytes s₀)
  refine ⟨by simp only [ax, e], fun _ => ⟨hu, ?_, ?_, ?_, ?_⟩, hu, ?_, kregs⟩
  · rw [mu', slot_write_ne _ _ _ (by unfold oQ oMask; omega) (by decide) (by decide),
      slot_write_ne _ _ _ (by unfold oQ oWidth; omega) (by decide) (by decide), slot_write_self]
  · rw [mu', slot_write_ne _ _ _ (by unfold oWidth oMask; omega) (by decide) (by decide), slot_write_self]
  · rw [mu', slot_write_self]
  · intro i hi
    have ho : ∀ d, d + 4 ≤ oNonce → ofs (rBase s₀) (off (rBase s₀) (oNonce + i)) < d ∨
        d + 4 ≤ ofs (rBase s₀) (off (rBase s₀) (oNonce + i)) := fun d hd => by
      rw [ofs_off0 _ (by unfold oNonce; omega)]; omega
    rw [mu', writeW32_outside _ _ (d := oMask) _ (by decide) _ (ho _ (by decide)),
      writeW32_outside _ _ (d := oWidth) _ (by decide) _ (ho _ (by decide)),
      writeW32_outside _ _ (d := oQ) _ (by decide) _ (ho _ (by decide))]
    exact clearMem_zero _ _ 8 (by decide) i (by omega)
  · rw [mu']
    have o₀ := clearMem_outside t.mem (rBase s₀) 8 (by decide)
    have o₁ := writeW32_outside (clearMem t.mem (rBase s₀) 8) (rBase s₀) (d := oQ)
      (rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀)) (by decide)
    have o₂ := writeW32_outside ((clearMem t.mem (rBase s₀) 8).writeW (off (rBase s₀) oQ)
      (rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))) (rBase s₀) (d := oWidth)
      (BitVec.ofNat 32 (rWidth s₀)) (by decide)
    have o₃ := writeW32_outside (((clearMem t.mem (rBase s₀) 8).writeW (off (rBase s₀) oQ)
      (rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))).writeW (off (rBase s₀) oWidth)
      (BitVec.ofNat 32 (rWidth s₀))) (rBase s₀) (d := oMask) (maskValue (rLead s₀).toNat) (by decide)
    exact (((Outs.of_outside o₀ (by decide)).trans
      (Outs.of_outside (o₁.mono (o' := oQ) (n' := 12) (by decide) (by decide)) (by decide))).trans
      (Outs.of_outside (o₂.mono (o' := oQ) (n' := 12) (by decide) (by decide)) (by decide))).trans
      (Outs.of_outside (o₃.mono (o' := oQ) (n' := 12) (by decide) (by decide)) (by decide))

end VG.Proof.Dsa.X86.KeyRandom
