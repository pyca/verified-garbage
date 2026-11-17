module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86.RandomContext
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Frame

/-! ### `Dsa.X86.KeyRandom.Prepare`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.KeyRandom.Mask`, which this module and modules that import it used -/

section

/-!
# The leading byte's mask, and the check that q > 1 (x86)

`mask` leaves in `ebp` the mask of the significant bits of the public
leading byte in `edx` (`maskValue`), branching on that byte;
`prepareFinish` stores it and sets `eax = 1` exactly when q > 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- The mask `mask` selects for the leading byte `n`. -/
def maskValue (n : Nat) : BitVec 32 :=
  if n < 2 then 1 else if n < 4 then 3 else if n < 8 then 7 else
  if n < 16 then 15 else if n < 32 then 31 else if n < 64 then 63 else
  if n < 128 then 127 else 255

/-- The selected mask keeps exactly the significant bits of a nonzero byte. -/
theorem maskValue_eq (n : Nat) (hpos : 0 < n) (hbound : n < 256) :
    maskValue n = BitVec.ofNat 32 (2 ^ (n.log2 + 1) - 1) := by
  have key : ∀ k, 2 ^ k ≤ n → n < 2 ^ (k + 1) → n.log2 = k := fun k h₁ h₂ =>
    (Nat.log2_eq_iff (by omega_using [hpos])).mpr ⟨h₁, h₂⟩
  unfold maskValue
  split
  · rw [key 0 (show 1 ≤ n by omega_using [hpos]) (by omega_arith)]; rfl
  split
  · rw [key 1 (by omega_arith) (by omega_arith)]; rfl
  split
  · rw [key 2 (by omega_arith) (by omega_arith)]; rfl
  split
  · rw [key 3 (by omega_arith) (by omega_arith)]; rfl
  split
  · rw [key 4 (by omega_arith) (by omega_arith)]; rfl
  split
  · rw [key 5 (by omega_arith) (by omega_arith)]; rfl
  split
  · rw [key 6 (by omega_arith) (by omega_arith)]; rfl
  · rw [key 7 (by omega_arith) (by omega_using [hbound])]; rfl

/-- One threshold of the mask. -/
theorem maskStep_ok {th bits n : Nat} (hth : th < 2 ^ 32) {s u : State} {Q : State → Prop}
    (hd : (u.gpr .edx).toNat = n) (hk : Keeps [.ebp] s u) (hm : u.mem = s.mem)
    (k : ∀ t, t.gpr .ebp = (if n < th then BitVec.ofNat 32 bits else u.gpr .ebp) →
      (t.gpr .edx).toNat = n → Keeps [.ebp] s t → t.mem = s.mem → Q t) :
    WP isa (maskStep th bits) u Q := by
  unfold maskStep
  refine WP.seq (wp_cmpi fun u₁ f₁ c₁ _ => WP.block_nil ?_)
  rw [hd, toNat_ofNat_lt hth] at c₁
  have k₁ : Keeps [.ebp] s u₁ := hk.trans (f₁.keeps _)
  by_cases h : n < th
  · refine WP.ite true (by simp only [eval, c₁, h, decide_true]) (fun _ =>
      wp_movS rfl fun u₂ v₂ _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
    refine k u₂ (by rw [v₂.gpr]; simp only [h, ↓reduceIte]) (by rw [v₂.other _ (by decide), f₁.gpr, hd])
      (k₁.trans v₂.keeps) (by rw [v₂.mem, f₁.mem, hm])
  · refine WP.ite false (by simp only [eval, c₁, h, decide_false]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    exact k u₁ (by simp only [h, ↓reduceIte]; rw [f₁.gpr]) (by rw [f₁.gpr, hd]) k₁ (by rw [f₁.mem, hm])

theorem mask_ok {s : State} {n : Nat} (hd : (s.gpr .edx).toNat = n) :
    WP isa mask s fun t => t.gpr .ebp = maskValue n ∧ t.mem = s.mem ∧ Keeps [.ebp] s t := by
  unfold mask
  refine WP.seq (wp_movS rfl fun s₀ u₀ _ => WP.block_nil ?_)
  have d₀ : (s₀.gpr .edx).toNat = n := by rw [u₀.other _ (by decide), hd]
  refine WP.seq (maskStep_ok (by decide) d₀ u₀.keeps u₀.mem fun s₁ e₁ d₁ k₁ m₁ =>
    WP.seq (maskStep_ok (by decide) d₁ k₁ m₁ fun s₂ e₂ d₂ k₂ m₂ =>
    WP.seq (maskStep_ok (by decide) d₂ k₂ m₂ fun s₃ e₃ d₃ k₃ m₃ =>
    WP.seq (maskStep_ok (by decide) d₃ k₃ m₃ fun s₄ e₄ d₄ k₄ m₄ =>
    WP.seq (maskStep_ok (by decide) d₄ k₄ m₄ fun s₅ e₅ d₅ k₅ m₅ =>
    WP.seq (maskStep_ok (by decide) d₅ k₅ m₅ fun s₆ e₆ d₆ k₆ m₆ =>
    maskStep_ok (by decide) d₆ k₆ m₆ fun s₇ e₇ _ k₇ m₇ => ?_))))))
  refine ⟨?_, m₇, k₇⟩
  rw [e₇, e₆, e₅, e₄, e₃, e₂, e₁, u₀.gpr]
  rfl

/-- Store the mask, and set `eax = 1` exactly when the scan's width or
leading byte is at least two. -/
theorem prepareFinish_ok {s : State} {B : Addr} (hf : RF s B) {w : Nat} {b : Byte} (hw : w < 2 ^ 32)
    (hb : s.gpr .ebx = BitVec.ofNat 32 w) (hd : s.gpr .edx = b.setWidth 32) :
    WP isa prepareFinish s fun t =>
      t.gpr .eax = (if 2 ≤ w ∨ 2 ≤ b.toNat then 1 else 0) ∧
      t.mem = s.mem.writeW (off B oMask) (maskValue b.toNat) ∧
      Keeps [.eax, .ebp] s t := by
  have hb8 : (b.setWidth 32).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide : 2 ^ 8 ≤ 2 ^ 32))]
  unfold prepareFinish
  refine WP.seq (WP.mono (mask_ok (n := b.toNat) (by rw [hd, hb8])) fun s₁ ⟨e₁, m₁, k₁⟩ => ?_)
  have f₁ := hf.of_keeps k₁
  refine WP.seq (wp_storeS (f₁.ea (by decide)) (f₁.write (by decide)) fun s₂ u₂ =>
    wp_movS rfl fun s₃ u₃ _ => wp_cmpi fun s₄ g₄ c₄ _ => WP.block_nil ?_)
  have hbx : s₃.gpr .ebx = BitVec.ofNat 32 w := by
    rw [u₃.other _ (by decide), u₂.gpr, k₁.1 _ (by decide), hb]
  rw [hbx, toNat_ofNat_lt hw, show (2 : BitVec 32).toNat = 2 from rfl] at c₄
  have k₄ : Keeps [.eax, .ebp] s s₄ :=
    ((k₁.mono (by decide)).trans (u₂.keeps _)).trans ((u₃.keeps.mono (by decide)).trans (g₄.keeps _))
  have hm₄ : s₄.mem = s.mem.writeW (off B oMask) (maskValue b.toNat) := by
    rw [g₄.mem, u₃.mem, u₂.mem, e₁, m₁]
  -- The second test, from the first's `eax`.
  have second : ∀ u : State, u.gpr .eax = (if 2 ≤ w then 1 else 0) → Keeps [.eax, .ebp] s u →
      u.mem = s.mem.writeW (off B oMask) (maskValue b.toNat) →
      WP isa (.seq (.block [.alu .cmp .edx (.imm 2)])
        (.ite .ae (.block [.mov .eax (.imm 1)]) (.block []))) u fun t =>
        t.gpr .eax = (if 2 ≤ w ∨ 2 ≤ b.toNat then 1 else 0) ∧
        t.mem = s.mem.writeW (off B oMask) (maskValue b.toNat) ∧ Keeps [.eax, .ebp] s t := by
    intro u hu ku mu
    refine WP.seq (wp_cmpi fun u₁ g₁ c₁ _ => WP.block_nil ?_)
    rw [ku.1 _ (by decide), hd, hb8, show (2 : BitVec 32).toNat = 2 from rfl] at c₁
    have ku₁ : Keeps [.eax, .ebp] s u₁ := ku.trans (g₁.keeps _)
    by_cases h2 : 2 ≤ b.toNat
    · refine WP.ite true (by simp only [eval, c₁, Nat.not_lt.mpr h2, decide_false, Option.map_some,
        Bool.not_false]) (fun _ => wp_movS rfl fun u₂ v₂ _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
      exact ⟨by rw [v₂.gpr]; simp only [h2, or_true, ↓reduceIte], by rw [v₂.mem, g₁.mem, mu],
        ku₁.trans (v₂.keeps.mono (by decide))⟩
    · refine WP.ite false (by simp only [eval, c₁, Nat.not_le.mp h2, decide_true, Option.map_some,
        Bool.not_true]) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
      refine ⟨?_, by rw [g₁.mem, mu], ku₁⟩
      rw [g₁.gpr, hu]
      by_cases hw2 : 2 ≤ w
      · simp only [hw2, true_or, ↓reduceIte]
      · simp only [hw2, h2, or_self, ↓reduceIte]
  by_cases hw2 : 2 ≤ w
  · refine WP.seq (WP.ite true (by simp only [eval, c₄, Nat.not_lt.mpr hw2, decide_false, Option.map_some,
      Bool.not_false]) (fun _ => wp_movS rfl fun s₅ u₅ _ => WP.block_nil ?_) (fun e => Bool.noConfusion e))
    exact second s₅ (by rw [u₅.gpr]; simp only [hw2, ↓reduceIte]) (k₄.trans (u₅.keeps.mono (by decide)))
      (by rw [u₅.mem, hm₄])
  · refine WP.seq (WP.ite false (by simp only [eval, c₄, Nat.not_le.mp hw2, decide_true, Option.map_some,
      Bool.not_true]) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_))
    exact second s₄ (by rw [g₄.gpr, u₃.gpr]; simp only [hw2, ↓reduceIte]) k₄ hm₄

end VG.Proof.Dsa.X86.KeyRandom

end

end

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
  obtain he : off B (d + i) = off B d + BitVec.ofNat 64 i := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [he]
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, Mem.sub_ofNat_toNat (off B d) (i := i) (by omega_using [hi]),
    show 32 / 8 = 4 from rfl, hi, ite_true]
  exact BitVec.extractLsb'_zero

theorem clearMem_outside (m : Mem) (B : Addr) : ∀ k, k ≤ 8 → Outside B oNonce 32 m (clearMem m B k)
  | 0, _ => Outside.refl _ _ _ _
  | k + 1, hk => (clearMem_outside m B k (by omega_using [hk])).trans
      ((writeW32_outside _ B (d := oNonce + 4 * k) 0 (by unfold oNonce; omega_using [hk])).mono
        (by unfold oNonce; omega_using []) (by unfold oNonce; omega_using [hk]))

theorem clearMem_zero (m : Mem) (B : Addr) : ∀ k, k ≤ 8 → ∀ i < 4 * k, clearMem m B k (off B (oNonce + i)) = 0
  | 0, _, i, hi => absurd hi (by omega_using [])
  | k + 1, hk, i, hi => by
    by_cases hlo : i < 4 * k
    · rw [clearMem, writeW32_outside _ B (d := oNonce + 4 * k) 0 (by unfold oNonce; omega_using [hk]) _
        (by rw [ofs_off0 B (by unfold oNonce; omega_using [hk, hi])]; omega_using [hlo])]
      exact clearMem_zero m B k (by omega_using [hk]) i hlo
    · rw [clearMem, show oNonce + i = oNonce + 4 * k + (i - 4 * k) by omega_using [hlo]]
      exact zeroWord_at _ B _ _ (by omega_using [hi])

theorem clearMem_frame (s₀ : State) (m : Mem) : ∀ k, k ≤ 8 → Frame [rStack s₀] m (clearMem m (rBase s₀) k)
  | 0, _ => Frame.refl _ _
  | k + 1, hk => (clearMem_frame s₀ m k (by omega_using [hk])).trans
      (frame_store s₀ _ (d := oNonce + 4 * k) (by unfold oNonce KeyRandom.frameBytes; omega_using [hk]) 0)

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
  rw [Nat.mod_eq_of_lt (a := k) hk, Nat.mod_eq_of_lt (a := d) (by omega_using [hd, hk]), Nat.mod_eq_of_lt (a := k - d) (by omega_using [hk])]
  omega_using [hd, hk]

theorem prepare_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    WP isa prepare t fun u =>
      u.gpr .eax = (if 1 < Spec.Dsa.decodeBE (rQBytes s₀) then 1 else 0) ∧
      ((1 < Spec.Dsa.decodeBE (rQBytes s₀)) → Prepared s₀ u) ∧ Ready s₀ u ∧
      Outs (rBase s₀) [(oQ, 12), (oNonce, 32)] t.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] t u := by
  obtain hfit := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  obtain hql := rQBytes_le A
  obtain hqn := rQBytes_length A
  unfold prepare
  refine WP.seq (clearNonce_ok h.rf fun t₁ f₁ m₁ k₁ _ => ?_)
  obtain h₁ : Ready s₀ t₁ := h.congr k₁ (by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide))
  refine wp_movS (h₁.argSrc A (j := 3) (by decide)) fun t₂ u₂ _ => ?_
  obtain h₂ := h₁.upd u₂ (by decide)
  refine wp_addS (h₂.argSrc A (j := 5) (by decide)) fun t₃ u₃ _ => ?_
  obtain h₃ := h₂.upd u₃ (by decide)
  refine wp_movS (h₃.argSrc A (j := 6) (by decide)) fun t₄ u₄ _ => WP.block_nil ?_
  obtain h₄ := h₃.upd u₄ (by decide)
  obtain e6 : X86.arg s₀ 6 = BitVec.ofNat 32 (rQBytes s₀).length := by
    rw [hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain esi₄ : t₄.gpr .esi = rQ s₀ := by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]; rfl
  obtain ecx₄ : t₄.gpr .ecx = BitVec.ofNat 32 (rQBytes s₀).length := by rw [u₄.gpr, e6]
  refine WP.seq (WP.mono (significant_ok esi₄ ecx₄ (h₄.q A) (rQBytes_pos A) (by omega_using [hql]))
    fun t₅ ⟨bx₅, dx₅, m₅, k₅⟩ => ?_)
  obtain h₅ : Ready s₀ t₅ := h₄.congr k₅ (by rw [m₅]; exact Frame.refl _ _)
  refine WP.seq (wp_movS (h₅.argSrc A (j := 3) (by decide)) fun t₆ u₆ _ => ?_)
  obtain h₆ := h₅.upd u₆ (by decide)
  refine wp_addS (h₆.argSrc A (j := 5) (by decide)) fun t₇ u₇ _ => ?_
  obtain h₇ := h₆.upd u₇ (by decide)
  refine wp_addS (h₇.argSrc A (j := 6) (by decide)) fun t₈ u₈ _ => ?_
  obtain h₈ := h₇.upd u₈ (by decide)
  refine wp_subS rfl fun t₉ u₉ _ => ?_
  obtain h₉ := h₈.upd u₉ (by decide)
  obtain ebx₉ : t₉.gpr .ebx = BitVec.ofNat 32 (rWidth s₀) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), bx₅]
  obtain esi₉ : t₉.gpr .esi = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀) := by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, u₈.other .ebx (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), bx₅, e6, add_ofNat_sub32 _ hfit (by omega_using [hql])]
    rfl
  refine wp_slot h₉.rf (by decide) esi₉ fun t₁₀ f₁₀ m₁₀ g₁₀ r₁₀ w₁₀ _ _ => ?_
  refine wp_slot f₁₀ (by decide) (v := BitVec.ofNat 32 (rWidth s₀)) (by rw [g₁₀]; exact ebx₉)
    fun t₁₁ f₁₁ m₁₁ g₁₁ r₁₁ w₁₁ _ _ => WP.block_nil ?_
  obtain edx₁₁ : t₁₁.gpr .edx = (rLead s₀).setWidth 32 := by
    rw [g₁₁, g₁₀, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), dx₅]
  refine WP.mono (prepareFinish_ok f₁₁ (w := rWidth s₀) (b := rLead s₀) (show (VG.Proof.Dsa.significant (rQBytes s₀)).1 < 2 ^ 32 by omega_using [hfit, hql])
    (by rw [g₁₁, g₁₀]; exact ebx₉) edx₁₁) fun u ⟨ax, mu, ku⟩ => ?_
  -- Memory.
  obtain m₉ : t₉.mem = clearMem t.mem (rBase s₀) 8 := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅, u₄.mem, u₃.mem, u₂.mem, m₁]
  obtain mu' : u.mem = (((clearMem t.mem (rBase s₀) 8).writeW (off (rBase s₀) oQ)
      (rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))).writeW (off (rBase s₀) oWidth)
      (BitVec.ofNat 32 (rWidth s₀))).writeW (off (rBase s₀) oMask) (maskValue (rLead s₀).toNat) := by
    rw [mu, m₁₁, m₁₀, m₉]
  obtain kregs : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] t u := by
    refine (((((k₁.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))).trans (k₅.mono (by decide))).trans ?_
    refine (((((u₆.keeps.mono (by decide)).trans (u₇.keeps.mono (by decide))).trans
      (u₈.keeps.mono (by decide))).trans (u₉.keeps.mono (by decide))).trans
      ⟨fun r _ => by rw [g₁₁, g₁₀], by rw [r₁₁, r₁₀], by rw [w₁₁, w₁₀]⟩).trans (ku.mono (by decide))
  obtain hu : Ready s₀ u := h₉.congr (rs := [.eax, .ebp])
    ⟨fun r hr => by rw [ku.1 r hr, g₁₁, g₁₀], by rw [ku.2.1, r₁₁, r₁₀], by rw [ku.2.2, w₁₁, w₁₀]⟩
    (by rw [mu, m₁₁, m₁₀]
        exact ((frame_store s₀ _ (by decide) _).trans (frame_store s₀ _ (by decide) _)).trans
          (frame_store s₀ _ (by decide) _))
  obtain e := VG.Proof.Dsa.random_valid_scan_ge (rQBytes s₀)
  refine ⟨by simp only [ax, e], fun _ => ⟨hu, ?_, ?_, ?_, ?_⟩, hu, ?_, kregs⟩
  · rw [mu', slot_write_ne _ _ _ (by unfold oQ oMask; omega_using []) (by decide) (by decide),
      slot_write_ne _ _ _ (by unfold oQ oWidth; omega_using []) (by decide) (by decide), slot_write_self]
  · rw [mu', slot_write_ne _ _ _ (by unfold oWidth oMask; omega_using []) (by decide) (by decide), slot_write_self]
  · rw [mu', slot_write_self]
  · intro i hi
    obtain ho : ∀ d, d + 4 ≤ oNonce → ofs (rBase s₀) (off (rBase s₀) (oNonce + i)) < d ∨
        d + 4 ≤ ofs (rBase s₀) (off (rBase s₀) (oNonce + i)) := fun d hd => by
      rw [ofs_off0 _ (by unfold oNonce; omega_using [hi])]; omega_using [hd]
    rw [mu', writeW32_outside _ _ (d := oMask) _ (by decide) _ (ho _ (by decide)),
      writeW32_outside _ _ (d := oWidth) _ (by decide) _ (ho _ (by decide)),
      writeW32_outside _ _ (d := oQ) _ (by decide) _ (ho _ (by decide))]
    exact clearMem_zero _ _ 8 (by decide) i (by omega_using [hi])
  · rw [mu']
    obtain o₀ := clearMem_outside t.mem (rBase s₀) 8 (by decide)
    obtain o₁ := writeW32_outside (clearMem t.mem (rBase s₀) 8) (rBase s₀) (d := oQ)
      (rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀)) (by decide)
    obtain o₂ := writeW32_outside ((clearMem t.mem (rBase s₀) 8).writeW (off (rBase s₀) oQ)
      (rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))) (rBase s₀) (d := oWidth)
      (BitVec.ofNat 32 (rWidth s₀)) (by decide)
    obtain o₃ := writeW32_outside (((clearMem t.mem (rBase s₀) 8).writeW (off (rBase s₀) oQ)
      (rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))).writeW (off (rBase s₀) oWidth)
      (BitVec.ofNat 32 (rWidth s₀))) (rBase s₀) (d := oMask) (maskValue (rLead s₀).toNat) (by decide)
    exact (((Outs.of_outside o₀ (by decide)).trans
      (Outs.of_outside (o₁.mono (o' := oQ) (n' := 12) (by decide) (by decide)) (by decide))).trans
      (Outs.of_outside (o₂.mono (o' := oQ) (n' := 12) (by decide) (by decide)) (by decide))).trans
      (Outs.of_outside (o₃.mono (o' := oQ) (n' := 12) (by decide) (by decide)) (by decide))

end VG.Proof.Dsa.X86.KeyRandom

end

end

/-!
# Copying a draw into the scalar (x86)

`copy` copies the `width` bytes of the tape from `used` on to the last
`width` bytes of the `q_len`-byte scalar, the first masked (`copied`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- `esp + c` as an address in the frame. -/
theorem RF.ptr {s : State} {B : Addr} (hf : RF s B) {c : Nat} (hc : c < argOff 11) :
    (s.gpr .esp + BitVec.ofNat 32 c).setWidth 64 = off B c := by
  rw [← hf.esp]
  exact addr_eq (by have := hf.nowrap; have := hf.esp_toNat; omega_arith)

/-- `[r + 0]`. -/
theorem ea_at0 (s : State) (r : Reg) : s.ea (at_ r 0) = (s.gpr r).setWidth 64 := by
  change (s.gpr r + BitVec.ofNat 32 0).setWidth 64 = _
  rw [BitVec.add_zero]

theorem ptr_add {p : BitVec 32} {i : Nat} (h : p.toNat + i < 2 ^ 32) :
    (p + BitVec.ofNat 32 i).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 i := addr_eq h

/-- A byte of the frame is writable. -/
theorem RF.write1 {s : State} {B : Addr} (hf : RF s B) {d : Nat} (hd : d < KeyRandom.frameBytes) :
    InRegions s.wr (off B d) 1 := hf.write (by omega_arith)

/-- What the scalar's byte `i` from the draw's place becomes: the first byte
masked. -/
def copied (bs : List Byte) (mask : BitVec 32) (i : Nat) : Byte :=
  if i = 0 then ((bs.getD 0 0).setWidth 32 &&& mask).setWidth 8 else bs.getD i 0

/-- The copy after its first `k ≥ 1` bytes. `d` is the draw's place in the
frame, `p` its source. -/
structure CopyInv (s₀ t₀ : State) (p : BitVec 32) (d : Nat) (bs : List Byte) (mask : BitVec 32)
    (k : Nat) (t : State) : Prop where
  ready : Ready s₀ t
  esi : t.gpr .esi = p + BitVec.ofNat 32 k
  edx : t.gpr .edx = t.gpr .esp + BitVec.ofNat 32 (d + k)
  ecx : t.gpr .ecx = BitVec.ofNat 32 (bs.length - k)
  bytes : ∀ i < k, t.mem (off (rBase s₀) (d + i)) = copied bs mask i
  out : Outside (rBase s₀) d bs.length t₀.mem t.mem
  keeps : Keeps [.eax, .ecx, .edx, .esi] t₀ t

theorem byte_setWidth (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- One byte after the first. -/
theorem copyByte_ok {s₀ t₀ t : State} {p : BitVec 32} {d : Nat} {bs : List Byte} {mask : BitVec 32}
    {k : Nat} (hin : BytesIn t p bs) (hd : d + bs.length ≤ KeyRandom.frameBytes) (hk : k < bs.length)
    (I : CopyInv s₀ t₀ p d bs mask k t) (hk0 : 1 ≤ k) :
    WP isa (.block copyByte) t fun u => CopyInv s₀ t₀ p d bs mask (k + 1) u ∧
      u.zf = some (decide (bs.length - (k + 1) = 0)) := by
  have hfit := hin.fit
  have hrf := I.ready.rf
  have hF : KeyRandom.frameBytes = 120 := rfl
  unfold copyByte
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 k)
    (by rw [ea_at0, I.esi]; exact ptr_add (by omega_arith)) (hin.rd k hk) fun u₁ v₁ _ _ => ?_
  rw [hin.val k hk] at v₁
  obtain he : u₁.ea (at_ .edx 0) = off (rBase s₀) (d + k) := by
    rw [ea_at0, v₁.other _ (by decide), I.edx]
    exact hrf.ptr (by unfold argOff KeyRandom.frameBytes at *; omega_arith)
  obtain f₁ := hrf.of_keeps v₁.keeps
  refine wp_store8 he (f₁.write1 (by omega_arith)) fun u₂ m₂ => wp_addi fun u₃ v₃ => wp_addi fun u₄ v₄ =>
    wp_subi fun u₅ v₅ _ z₅ => WP.block_nil ?_
  obtain hv : (u₁.gpr (Reg8.al).reg).setWidth 8 = bs[k] := by
    show (u₁.gpr .eax).setWidth 8 = _; rw [v₁.gpr, byte_setWidth]
  rw [hv] at m₂
  obtain kk : Keeps [.eax, .ecx, .edx, .esi] t u₅ :=
    ((((v₁.keeps.mono (by decide)).trans (m₂.keeps _)).trans (v₃.keeps.mono (by decide))).trans
      (v₄.keeps.mono (by decide))).trans (v₅.keeps.mono (by decide))
  obtain mem₅ : u₅.mem = t.mem.writeW (off (rBase s₀) (d + k)) bs[k] := by
    rw [v₅.mem, v₄.mem, v₃.mem, m₂.mem, v₁.mem]
  obtain esp₅ : u₅.gpr .esp = t.gpr .esp := kk.1 _ (by decide)
  obtain hb : bs.length < 2 ^ 32 := by omega_arith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, I.keeps.trans kk⟩, ?_⟩
  · exact I.ready.congr kk (by rw [mem₅]; exact frame_store8 s₀ _ (by omega_arith) _)
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, m₂.gpr, v₁.other _ (by decide), I.esi,
      Offset.add_ofNat_add_one]
  · rw [v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide), m₂.gpr, v₁.other _ (by decide), I.edx,
      esp₅, Offset.add_ofNat_add_one]; rfl
  · rw [v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), m₂.gpr, v₁.other _ (by decide), I.ecx,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith)]; rfl
  · intro i hi
    rw [mem₅]
    by_cases hik : i = k
    · subst hik
      rw [writeW8_self]
      simp only [copied, show i ≠ 0 by omega_arith, ite_false, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hk, Option.getD_some]
    · rw [writeW8_outside _ _ (d := d + k) _ (by omega_arith) _ (by
        rw [ofs_off0 _ (by omega_arith)]; omega_arith)]
      exact I.bytes i (by omega_arith)
  · rw [mem₅]
    exact I.out.trans ((writeW8_outside _ _ (d := d + k) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · rw [z₅, v₄.other _ (by decide), v₃.other _ (by decide), m₂.gpr, v₁.other _ (by decide), I.ecx,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega_arith) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- The bytes after the first. -/
theorem copyLoop_ok {s₀ t₀ t : State} {p : BitVec 32} {d : Nat} {bs : List Byte} {mask : BitVec 32}
    {k : Nat} (hin : ∀ u, Ready s₀ u → BytesIn u p bs) (hd : d + bs.length ≤ KeyRandom.frameBytes)
    (hk : k < bs.length) (hk0 : 1 ≤ k) (I : CopyInv s₀ t₀ p d bs mask k t) :
    WP isa (.loop (.block copyByte) .ne) t fun u => CopyInv s₀ t₀ p d bs mask bs.length u := by
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) =>
      ∃ j, n = bs.length - j ∧ 1 ≤ j ∧ j < bs.length ∧ CopyInv s₀ t₀ p d bs mask j u)
    (fun n u hu => ?_) (bs.length - k) t ⟨k, rfl, hk0, hk, I⟩
  obtain ⟨j, hn, hj0, hj, J⟩ := hu
  refine WP.mono (copyByte_ok (hin u J.ready) hd hj J hj0) fun v ⟨J', z⟩ => ?_
  by_cases he : bs.length - (j + 1) = 0
  · left
    refine ⟨by simp only [eval, z, he, decide_true, Option.map_some, Bool.not_true], ?_⟩
    rw [show bs.length = j + 1 by omega_arith]; exact J'
  · right
    exact ⟨by simp only [eval, z, he, decide_false, Option.map_some, Bool.not_false],
      bs.length - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, by omega_arith, J'⟩

/-- The draw at `used`, as bytes of the frame reads them. -/
theorem Ready.draw {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {used : Nat}
    (hu : used ≤ (rInput s₀).rand.length) (w : Nat) :
    BytesIn t (X86.arg s₀ 7 + BitVec.ofNat 32 used) (((rInput s₀).rand.drop used).take w) :=
  ((h.rand A).drop used hu).take w

/-- The draw's place in the scalar, and its source. -/
abbrev drawPlace (s₀ : State) : Nat := oNonce + ((rQBytes s₀).length - rWidth s₀)
abbrev drawBytes (s₀ : State) (used : Nat) : List Byte := ((rInput s₀).rand.drop used).take (rWidth s₀)

/-- The draw's source, count and place. -/
theorem copyHeader_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {used : Nat}
    (hu : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used)
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)) :
    WP isa (.block copyHeader) t fun u => Ready s₀ u ∧ u.mem = t.mem ∧ Keeps [.eax, .ecx, .edx, .esi] t u ∧
      u.gpr .esi = X86.arg s₀ 7 + BitVec.ofNat 32 used ∧ u.gpr .ecx = BitVec.ofNat 32 (rWidth s₀) ∧
      u.gpr .edx = u.gpr .esp + BitVec.ofNat 32 (drawPlace s₀) := by
  obtain hql := rQBytes_le A
  obtain hqn := rQBytes_length A
  obtain hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  unfold copyHeader
  refine wp_movS (h.argSrc A (j := 7) (by decide)) fun t₁ u₁ _ => ?_
  obtain h₁ := h.upd u₁ (by decide)
  refine wp_addS (v := BitVec.ofNat 32 used) (by rw [h₁.rf.readSlot (by decide), u₁.mem]; exact congrArg some hu) fun t₂ u₂ _ => ?_
  obtain h₂ := h₁.upd u₂ (by decide)
  refine wp_movS (v := BitVec.ofNat 32 (rWidth s₀)) (by rw [h₂.rf.readSlot (by decide), u₂.mem, u₁.mem]; exact congrArg some hw) fun t₃ u₃ _ => ?_
  obtain h₃ := h₂.upd u₃ (by decide)
  refine wp_movS rfl fun t₄ u₄ _ => ?_
  obtain h₄ := h₃.upd u₄ (by decide)
  refine wp_addi fun t₅ u₅ => ?_
  obtain h₅ := h₄.upd u₅ (by decide)
  refine wp_addS (h₅.argSrc A (j := 6) (by decide)) fun t₆ u₆ _ => ?_
  obtain h₆ := h₅.upd u₆ (by decide)
  refine wp_sub fun t₇ u₇ _ => WP.block_nil ?_
  obtain h₇ := h₆.upd u₇ (by decide)
  obtain k₇ : Keeps [.eax, .ecx, .edx, .esi] t t₇ :=
    ((((((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))).trans (u₅.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))).trans
      (u₇.keeps.mono (by decide))
  obtain m₇ : t₇.mem = t.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain esp₇ : t₇.gpr .esp = t.gpr .esp := k₇.1 _ (by decide)
  obtain esi₇ : t₇.gpr .esi = X86.arg s₀ 7 + BitVec.ofNat 32 used := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.gpr]
  obtain ecx₇ : t₇.gpr .ecx = BitVec.ofNat 32 (rWidth s₀) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  obtain edx₇ : t₇.gpr .edx = t₇.gpr .esp + BitVec.ofNat 32 (drawPlace s₀) := by
    have ecx₃ : t₃.gpr .ecx = BitVec.ofNat 32 (rWidth s₀) := u₃.gpr
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₆.other .ecx (by decide), u₅.other .ecx (by decide),
      u₄.other .ecx (by decide), ecx₃, esp₇, u₃.other .esp (by decide), u₂.other .esp (by decide),
      u₁.other .esp (by decide),
      show X86.arg s₀ 6 = BitVec.ofNat 32 (rQBytes s₀).length by rw [hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      Offset.add_add, add_ofNat_sub32 _ (by omega_arith) (by unfold oNonce; omega_arith)]
    unfold drawPlace; congr 2; omega_arith
  exact ⟨h₇, m₇, k₇, esi₇, ecx₇, edx₇⟩

/-- The draw's header and its first byte. -/
theorem copyInit_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {used : Nat}
    (hu : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used)
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀))
    (hm : slot t.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) (hw1 : 1 ≤ rWidth s₀) :
    WP isa (.block copyInit) t fun u => CopyInv s₀ t (X86.arg s₀ 7 + BitVec.ofNat 32 used) (drawPlace s₀)
      (drawBytes s₀ used) (maskValue (rLead s₀).toNat) 1 u ∧ u.zf = some (decide (rWidth s₀ - 1 = 0)) := by
  have hF : KeyRandom.frameBytes = 120 := rfl
  obtain hql := rQBytes_le A
  obtain hqn := rQBytes_length A
  obtain hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  obtain hlen : (drawBytes s₀ used).length = rWidth s₀ := by
    simp only [drawBytes, List.length_take, List.length_drop]; omega_arith
  obtain hin := fun u (hr : Ready s₀ u) => hr.draw A (show used ≤ _ by omega_arith) (rWidth s₀)
  obtain hd : drawPlace s₀ + (drawBytes s₀ used).length ≤ KeyRandom.frameBytes := by
    rw [hlen]; unfold drawPlace oNonce; omega_arith
  unfold copyInit
  refine WP.block_append (WP.mono (copyHeader_ok A h hu hw) fun t₇ ⟨h₇, m₇, k₇, esi₇, ecx₇, edx₇⟩ => ?_)
  unfold copyFirst
  -- The first byte.
  obtain hb₀ := (hin t₇ h₇).rd 0 (by rw [hlen]; omega_arith)
  rw [BitVec.add_zero] at hb₀
  refine wp_load8 (a := (X86.arg s₀ 7 + BitVec.ofNat 32 used).setWidth 64)
    (by rw [ea_at0, esi₇]) hb₀ fun t₈ u₈ _ _ => ?_
  obtain hv₈ := (hin t₇ h₇).val 0 (by rw [hlen]; omega_arith)
  rw [BitVec.add_zero] at hv₈
  rw [hv₈] at u₈
  obtain h₈ := h₇.upd u₈ (by decide)
  refine wp_logicS (.inl rfl) (v := maskValue (rLead s₀).toNat) (by rw [h₈.rf.readSlot (by decide), u₈.mem, m₇]; exact congrArg some hm) fun t₉ u₉ => ?_
  simp only [↓reduceIte] at u₉
  obtain h₉ := h₈.upd u₉ (by decide)
  obtain he : t₉.ea (at_ .edx 0) = off (rBase s₀) (drawPlace s₀ + 0) := by
    rw [ea_at0, u₉.other _ (by decide), u₈.other _ (by decide), edx₇]
    exact h₇.rf.ptr (by unfold argOff drawPlace oNonce; omega_arith)
  refine wp_store8 he (h₉.rf.write1 (by unfold drawPlace oNonce; omega_arith)) fun t₁₀ m₁₀ =>
    wp_addi fun t₁₁ u₁₁ => wp_addi fun t₁₂ u₁₂ => wp_subi fun t₁₃ u₁₃ _ z₁₃ => WP.block_nil ?_
  obtain k₁₃ : Keeps [.eax, .ecx, .edx, .esi] t₇ t₁₃ :=
    ((((u₈.keeps.mono (by decide)).trans (u₉.keeps.mono (by decide))).trans (m₁₀.keeps _)).trans
      ((u₁₁.keeps.mono (by decide)).trans (u₁₂.keeps.mono (by decide)))).trans (u₁₃.keeps.mono (by decide))
  obtain mem₁₃ : t₁₃.mem = t.mem.writeW (off (rBase s₀) (drawPlace s₀ + 0))
      ((((drawBytes s₀ used)[0]'(by rw [hlen]; omega_arith)).setWidth 32 &&& maskValue (rLead s₀).toNat).setWidth 8) := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀.mem, u₉.mem, u₈.mem, m₇, show (Reg8.al).reg = Reg.eax from rfl,
      u₉.gpr, u₈.gpr]
  obtain hout : Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem t₁₃.mem := by
    rw [mem₁₃]
    exact (writeW8_outside t.mem (rBase s₀) (d := drawPlace s₀ + 0)
      ((((drawBytes s₀ used)[0]'(by rw [hlen]; omega_arith)).setWidth 32 &&& maskValue (rLead s₀).toNat).setWidth 8)
      (by unfold drawPlace oNonce; omega_arith)).mono (o' := drawPlace s₀) (n' := rWidth s₀)
      (by unfold drawPlace oNonce; omega_arith) (by unfold drawPlace oNonce; omega_arith)
  obtain I₁ : CopyInv s₀ t (X86.arg s₀ 7 + BitVec.ofNat 32 used) (drawPlace s₀) (drawBytes s₀ used)
      (maskValue (rLead s₀).toNat) 1 t₁₃ := by
    refine ⟨h₇.congr k₁₃ (by rw [mem₁₃, m₇]; exact frame_store8 s₀ _ (by unfold drawPlace oNonce; omega_arith) _),
      ?_, ?_, ?_, ?_, ?_, k₇.trans k₁₃⟩
    · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, m₁₀.gpr, u₉.other _ (by decide),
        u₈.other _ (by decide), esi₇]; rfl
    · rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), m₁₀.gpr, u₉.other _ (by decide),
        u₈.other _ (by decide), edx₇, k₁₃.1 .esp (by decide), Offset.add_ofNat_add_one]
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), m₁₀.gpr, u₉.other _ (by decide),
        u₈.other _ (by decide), ecx₇, hlen, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        sub_ofNat hw1]
    · intro i hi
      rw [show i = 0 by omega_arith, mem₁₃, writeW8_self]
      simp only [copied, ↓reduceIte, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show 0 < (drawBytes s₀ used).length by rw [hlen]; omega_arith), Option.getD_some]
    · rw [hlen]; exact hout
  obtain z₁ : t₁₃.zf = some (decide (rWidth s₀ - 1 = 0)) := by
    rw [z₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), m₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), ecx₇, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega_arith) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  exact ⟨I₁, z₁⟩

theorem copy_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {used : Nat}
    (hu : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used)
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀))
    (hm : slot t.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) (hw1 : 1 ≤ rWidth s₀) :
    WP isa copy t fun u => Ready s₀ u ∧
      (∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) ∧
      Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem u.mem ∧
      Keeps [.eax, .ecx, .edx, .esi] t u := by
  have hF : KeyRandom.frameBytes = 120 := rfl
  obtain hql := rQBytes_le A
  obtain hqn := rQBytes_length A
  obtain hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  obtain hlen : (drawBytes s₀ used).length = rWidth s₀ := by
    simp only [drawBytes, List.length_take, List.length_drop]; omega_arith
  obtain hin := fun u (hr : Ready s₀ u) => hr.draw A (show used ≤ _ by omega_arith) (rWidth s₀)
  obtain hd : drawPlace s₀ + (drawBytes s₀ used).length ≤ KeyRandom.frameBytes := by
    rw [hlen]; unfold drawPlace oNonce; omega_arith
  obtain fin : ∀ u, CopyInv s₀ t (X86.arg s₀ 7 + BitVec.ofNat 32 used) (drawPlace s₀) (drawBytes s₀ used)
      (maskValue (rLead s₀).toNat) (rWidth s₀) u →
      Ready s₀ u ∧ (∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) ∧
      Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .esi] t u :=
    fun u J => ⟨J.ready, J.bytes, hlen ▸ J.out, J.keeps⟩
  unfold copy
  refine WP.seq (WP.mono (copyInit_ok A h hu hw hm hfull hw1) fun t₁₃ ⟨I₁, z₁⟩ => ?_)
  unfold copyRest
  by_cases h1 : rWidth s₀ = 1
  · refine WP.ite false (by simp only [eval, z₁, h1, Nat.sub_self, decide_true, Option.map_some,
      Bool.not_true]) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil (fin _ ?_))
    rw [h1]; exact I₁
  · refine WP.ite true (by simp only [eval, z₁, show rWidth s₀ - 1 ≠ 0 by omega_arith, decide_false,
      Option.map_some, Bool.not_false]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    exact WP.mono (copyLoop_ok hin hd (by rw [hlen]; omega_arith) (Nat.le_refl _) I₁) fun u J => fin u (hlen ▸ J)

end VG.Proof.Dsa.X86.KeyRandom
