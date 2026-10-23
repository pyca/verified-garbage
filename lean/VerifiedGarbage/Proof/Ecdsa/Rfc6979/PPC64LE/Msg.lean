module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on PPC64LE: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`): the pointers (`msgPtrs`), then `V` copied from the frame, the
byte `b`, then the private key and `h`, `Q` bytes each, copied, a 32-bit
word at a time (`copyW_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Proof.Hmac.Common (bytesAt_add)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- The pointers: the frame's base in `r11`, `scratch` in `r9`, `d` in `r10`. -/
theorem msgPtrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g lr m₀ u ∧ u.mem = t.mem ∧ Kp [.r9, .r10, .r11] t u ∧
      u.gpr .r11 = L.B + BitVec.ofNat 64 96 ∧ u.gpr .r9 = L.scr ∧ u.gpr .r10 = L.d := by
  have hnB := hL.nB
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine stepLd (a := L.B + BitVec.ofNat 64 312) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc₁.inFr (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  have hc₂ := hc₁.kp hL k₂ m₂
  refine stepLd (a := L.B + BitVec.ofNat 64 328) (by decide) (by decide)
    (by rw [k₂.gpr _ (by decide), hb, fr_add]; rfl) (hc₂.inFr (by omega) (by omega)) fun t₃ k₃ m₃ v₃ => wp_nil ?_
  refine ⟨hc₂.kp hL k₃ m₃, by rw [m₃, m₂, m₁], (k₁.mono.trans k₂.mono).trans k₃.mono,
    by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb], by rw [k₃.gpr _ (by decide), v₂, hc₁.pScr],
    by rw [v₃, m₂, hc₁.pD]⟩

theorem bytesAt_byte (m : Mem) (a : Addr) (v : BitVec 8) : Spec.Sha256.bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [Spec.Sha256.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero, Mem.writeW,
    Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero,
    List.cons.injEq, and_true]
  exact BitVec.eq_of_toNat_eq (by simp)

/-- The message at `scratch + 2256`. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {D b : Nat} (full : Bool)
    (hD4 : D % 4 = 0) (hD : D ≤ 64) (hQ4 : L.q % 4 = 0) (hQ : L.q ≤ 48) (hb : b < 2 ^ 15) :
    WP isa (.block (Cfg.msgPtrs ++ Cfg.msg L.q D b full)) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 1 + 2 * L.q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) (D + 1 + (if full then 2 * L.q else 0)) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) D ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d L.q ++ Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 256) L.q
          else []) := by
  have hnB := hL.nB
  have hnc := hL.nc
  have hnd := hL.nd
  rw [WP.block_append_iff]
  refine WP.mono (msgPtrs_ok hL hc) fun t₁ ⟨hc₁, m₁, k₁, b₁, s₁, d₁⟩ => ?_
  rw [Cfg.msg, List.append_assoc, WP.block_append_iff]
  -- `V`.
  have hV : ∀ {u : State}, Ctx L g lr m₀ u → ∀ j < D / 4,
      InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 96 + BitVec.ofNat 64 (96 + 4 * j)) 4 := fun hu j hj => by
    rw [fr_add]; exact hu.inFr (by omega) (by omega)
  have hW : ∀ {u : State}, Ctx L g lr m₀ u → ∀ {d n : Nat}, d + n ≤ 8192 → ∀ j, 4 * j + 4 ≤ n →
      InRegions u.wr (L.scr + BitVec.ofNat 64 (d + 4 * j)) 4 := fun hu d n h j hj =>
    hu.inScrW (by omega)
  refine WP.mono (copyW_ok (S := L.B + BitVec.ofNat 64 96) (D := L.scr) (so := 96) (d := 2256) (K := D / 4)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [fr_add]; exact hL.stk_scr (by omega) (by omega)) (by omega) (by omega) (by omega)
    (D / 4) (Nat.le_refl _) t₁ b₁ s₁ (hV hc₁) (fun j hj => hW hc₁ (d := 2256) (n := D) (by omega) j (by omega)))
    fun t₂ ⟨k₂, f₂, v₂⟩ => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hD4)] at v₂ f₂
  rw [fr_add] at v₂
  have hc₂ := hc₁.keep hL k₂.rd k₂.wr k₂.sp (fun r hr => k₂.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
    f₂ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega))
  -- The byte.
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine stepLi hb fun t₃ k₃ m₃ v₃ => ?_
  refine stepStb (a := L.scr + BitVec.ofNat 64 (2256 + D)) (by decide) (by show 2256 + D < 2 ^ 15; omega)
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁]; rfl) (by rw [k₃.wr]; exact hc₂.inScrW (by omega))
    fun t₄ k₄ g₄ m₄ => ?_
  have hc₃ := hc₂.kp hL k₃ m₃
  have hc₄ := hc₃.keep hL k₄.rd k₄.wr k₄.sp (fun r _ => by rw [g₄]) (ws := [⟨L.scr + BitVec.ofNat 64 (2256 + D), 1⟩])
    (by rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega))
  have hb₄ : Spec.Sha256.bytesAt t₄.mem (L.scr + BitVec.ofNat 64 (2256 + D)) 1 = [BitVec.ofNat 8 b] := by
    rw [m₄, bytesAt_byte, v₃]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)
  have f₄ : Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D), 1⟩] t₃.mem t₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  -- What the later writes keep.
  have keep : ∀ {u u' : State} {o n o' n' : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 o', n'⟩] u.mem u'.mem →
      o + n ≤ o' ∨ o' + n' ≤ o → o' + n' ≤ 8192 → o + n ≤ 8192 →
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 o) n :=
    fun f h h₁ h₂ => bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ h (by omega) (by omega)) (by omega)
  have keepS : ∀ {u u' : State} {p : Addr} {n o' n' : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 o', n'⟩] u.mem u'.mem →
      Region.Disjoint ⟨p, n⟩ ⟨L.scr + BitVec.ofNat 64 o', n'⟩ → n ≤ 8192 →
      Spec.Sha256.bytesAt u'.mem p n = Spec.Sha256.bytesAt u.mem p n :=
    fun f h hn => bytesAt_frame f (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h) (by omega)
  have hV₀ : Spec.Sha256.bytesAt t₂.mem (L.scr + BitVec.ofNat 64 2256) D =
      Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) D := by rw [v₂, m₁]
  cases full
  · simp only [Bool.false_eq_true, ite_false, List.append_nil]
    refine wp_nil ⟨hc₄, ?_, ?_⟩
    · rw [← m₁]
      refine f₂.sub (fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) |>.trans (m₃ ▸ f₄.sub fun r hr => ⟨_,
        List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)
    · rw [Nat.add_zero, bytesAt_add, Offset.add_add, hb₄, keep f₄ (by omega) (by omega) (by omega), m₃, hV₀]
  · simp only [ite_true]
    rw [WP.block_append_iff]
    -- `d`.
    refine WP.mono (copyW_ok (S := L.d) (D := L.scr) (so := 0) (d := 2256 + D + 1) (K := L.q / 4)
      (by decide) (by decide) (by decide) (by decide)
      (by
        rw [BitVec.add_zero]
        exact (hL.dc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega)))
      (by omega) (by omega) (by omega) (L.q / 4) (Nat.le_refl _) t₄
      (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), d₁])
      (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁])
      (fun j hj => hc₄.inD (o := 0 + 4 * j) (by omega) (by omega))
      (fun j hj => hW hc₄ (d := 2256 + D + 1) (n := L.q) (by omega) j (by omega)))
      fun t₅ ⟨k₅, f₅, v₅⟩ => ?_
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hQ4)] at v₅ f₅
    have hc₅ := hc₄.keep hL k₅.rd k₅.wr k₅.sp
      (fun r hr => k₅.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
      f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega))
    -- `h`.
    refine WP.mono (copyW_ok (S := L.B + BitVec.ofNat 64 96) (D := L.scr) (so := 160) (d := 2256 + D + 1 + L.q)
      (K := L.q / 4) (by decide) (by decide) (by decide) (by decide)
      (by rw [fr_add]; exact hL.stk_scr (by omega) (by omega)) (by omega) (by omega) (by omega)
      (L.q / 4) (Nat.le_refl _) t₅
      (by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), b₁])
      (by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁])
      (fun j hj => by rw [fr_add]; exact hc₅.inFr (by omega) (by omega))
      (fun j hj => hW hc₅ (d := 2256 + D + 1 + L.q) (n := L.q) (by omega) j (by omega)))
      fun t₆ ⟨k₆, f₆, v₆⟩ => ?_
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hQ4)] at v₆ f₆
    rw [fr_add] at v₆
    have hc₆ := hc₅.keep hL k₆.rd k₆.wr k₆.sp
      (fun r hr => k₆.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
      f₆ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega))
    refine ⟨hc₆, ?_, ?_⟩
    · rw [← m₁]
      have sub : ∀ {o n : Nat}, 2256 ≤ o → o + n ≤ 2256 + (D + 1 + 2 * L.q) →
          ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, n⟩ : Region)],
            ∃ r' ∈ [(⟨L.scr + BitVec.ofNat 64 2256, D + 1 + 2 * L.q⟩ : Region)], Region.Sub r r' :=
        fun h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_singleton_self _, Offset.sub _ h₁ h₂⟩
      exact (((f₂.sub (sub (by omega) (by omega))).trans (m₃ ▸ f₄.sub (sub (by omega) (by omega)))).trans
        (f₅.sub (sub (by omega) (by omega)))).trans (f₆.sub (sub (by omega) (by omega)))
    · -- `d` and `h`, as on entry.
      have hd₄ : Spec.Sha256.bytesAt t₄.mem L.d L.q = Spec.Sha256.bytesAt t.mem L.d L.q := by
        rw [keepS f₄ ((hL.dc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega)))
          (by omega), m₃, keepS f₂ ((hL.dc.sub_left (Region.sub_prefix (by omega))).sub_right
          (Offset.sub_base _ (by omega))) (by omega), m₁]
      have hh₅ : Spec.Sha256.bytesAt t₅.mem (L.B + BitVec.ofNat 64 256) L.q =
          Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 256) L.q := by
        rw [keepS f₅ (hL.stk_scr (by omega) (by omega)) (by omega), keepS f₄ (hL.stk_scr (by omega) (by omega))
          (by omega), m₃, keepS f₂ (hL.stk_scr (by omega) (by omega)) (by omega), m₁]
      have e₁ : Spec.Sha256.bytesAt t₆.mem (L.scr + BitVec.ofNat 64 2256) D =
          Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) D := by
        rw [keep (o := 2256) (n := D) f₆ (by omega) (by omega) (by omega),
          keep (o := 2256) (n := D) f₅ (by omega) (by omega) (by omega),
          keep (o := 2256) (n := D) f₄ (by omega) (by omega) (by omega), m₃, hV₀]
      have e₂ : Spec.Sha256.bytesAt t₆.mem (L.scr + BitVec.ofNat 64 (2256 + D)) 1 = [BitVec.ofNat 8 b] := by
        rw [keep (o := 2256 + D) (n := 1) f₆ (by omega) (by omega) (by omega),
          keep (o := 2256 + D) (n := 1) f₅ (by omega) (by omega) (by omega), hb₄]
      have e₃ : Spec.Sha256.bytesAt t₆.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) L.q =
          Spec.Sha256.bytesAt t.mem L.d L.q := by
        rw [keep (o := 2256 + D + 1) (n := L.q) f₆ (by omega) (by omega) (by omega), v₅, BitVec.add_zero, hd₄]
      have e₄ : Spec.Sha256.bytesAt t₆.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1 + L.q)) L.q =
          Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 256) L.q := by
        rw [v₆]; exact hh₅
      rw [show D + 1 + 2 * L.q = D + 1 + L.q + L.q by omega, bytesAt_add, bytesAt_add, bytesAt_add, Offset.add_add,
        Offset.add_add, Offset.add_add, show 2256 + (D + 1 + L.q) = 2256 + D + 1 + L.q by omega,
        show 2256 + (D + 1) = 2256 + D + 1 by omega, e₁, e₂, e₃, e₄]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
