module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Layout
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step

/-!
# Deterministic ECDSA on PPC64LE: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`): the pointers (`msgPtrs`), then `V` copied from the frame, the
byte `b`, then the private key and `h`, `Q` bytes each, copied, a 32-bit
word at a time (`copyW_ok`). For scalars longer than the digest (`wide`,
`msgW_ok`), `h` is `Q - D` zero bytes then the digest, and the private key
is copied a word, then a byte, at a time (`copyN_ok`).
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
    (hc₁.inFr (by omega_arith) (by omega_arith)) fun t₂ k₂ m₂ v₂ => ?_
  have hc₂ := hc₁.kp hL k₂ m₂
  refine stepLd (a := L.B + BitVec.ofNat 64 328) (by decide) (by decide)
    (by rw [k₂.gpr _ (by decide), hb, fr_add]; rfl) (hc₂.inFr (by omega_arith) (by omega_arith)) fun t₃ k₃ m₃ v₃ => wp_nil ?_
  refine ⟨hc₂.kp hL k₃ m₃, by rw [m₃, m₂, m₁], (k₁.mono.trans k₂.mono).trans k₃.mono,
    by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb], by rw [k₃.gpr _ (by decide), v₂, hc₁.pScr],
    by rw [v₃, m₂, hc₁.pD]⟩

theorem bytesAt_byte (m : Mem) (a : Addr) (v : BitVec 8) : Spec.Sha256.bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [Spec.Sha256.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero, Mem.writeW,
    Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero,
    List.cons.injEq, and_true]
  exact BitVec.eq_of_toNat_eq (by simp)

/-- The message at `scratch + 2256`, with `h` at the frame's `ho`. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {D b : Nat} (full : Bool) (ho : Nat)
    (hD4 : D % 4 = 0) (hD : D ≤ 64) (hQ4 : full = true → L.q % 4 = 0) (hQ : full = true → L.q ≤ 64)
    (hho : full = true → 64 ≤ ho) (hho' : full = true → ho + L.q ≤ 256 + L.e) (hb : b < 2 ^ 15) :
    WP isa (.block (Cfg.msgPtrs ++ Cfg.msg L.q D b full ho)) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 1 + 2 * L.q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) (D + 1 + (if full then 2 * L.q else 0)) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) D ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d L.q ++
            Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (96 + ho)) L.q
          else []) := by
  have hnB := hL.nB
  have hne := hc.ne
  have hnc := hL.nc
  have hnd := hL.nd
  rw [WP.block_append_iff]
  refine WP.mono (msgPtrs_ok hL hc) fun t₁ ⟨hc₁, m₁, k₁, b₁, s₁, d₁⟩ => ?_
  simp only [Cfg.msg, Bool.false_eq_true, ite_false]
  rw [List.append_assoc, WP.block_append_iff]
  -- `V`.
  have hV : ∀ {u : State}, Ctx L g lr m₀ u → ∀ j < D / 4,
      InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 96 + BitVec.ofNat 64 (96 + 4 * j)) 4 := fun hu j hj => by
    rw [fr_add]; exact hu.inFr (by omega_arith) (by omega_arith)
  have hW : ∀ {u : State}, Ctx L g lr m₀ u → ∀ {d n : Nat}, d + n ≤ 8192 → ∀ j, 4 * j + 4 ≤ n →
      InRegions u.wr (L.scr + BitVec.ofNat 64 (d + 4 * j)) 4 := fun hu d n h j hj =>
    hu.inScrW (by omega_arith)
  refine WP.mono (copyW_ok (S := L.B + BitVec.ofNat 64 96) (D := L.scr) (so := 96) (d := 2256) (K := D / 4)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [fr_add]; exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)
    (D / 4) (Nat.le_refl _) t₁ b₁ s₁ (hV hc₁) (fun j hj => hW hc₁ (d := 2256) (n := D) (by omega_arith) j (by omega_arith)))
    fun t₂ ⟨k₂, f₂, v₂⟩ => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hD4)] at v₂ f₂
  rw [fr_add] at v₂
  have hc₂ := hc₁.keep hL k₂.rd k₂.wr k₂.sp (fun r hr => k₂.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
    f₂ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega_arith))
  -- The byte.
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine stepLi hb fun t₃ k₃ m₃ v₃ => ?_
  refine stepStb (a := L.scr + BitVec.ofNat 64 (2256 + D)) (by decide) (by show 2256 + D < 2 ^ 15; omega_arith)
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁]; rfl) (by rw [k₃.wr]; exact hc₂.inScrW (by omega_arith))
    fun t₄ k₄ g₄ m₄ => ?_
  have hc₃ := hc₂.kp hL k₃ m₃
  have hc₄ := hc₃.keep hL k₄.rd k₄.wr k₄.sp (fun r _ => by rw [g₄]) (ws := [⟨L.scr + BitVec.ofNat 64 (2256 + D), 1⟩])
    (by rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega_arith))
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
      exact Offset.disjoint _ h (by omega_arith) (by omega_arith)) (by omega_arith)
  have keepS : ∀ {u u' : State} {p : Addr} {n o' n' : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 o', n'⟩] u.mem u'.mem →
      Region.Disjoint ⟨p, n⟩ ⟨L.scr + BitVec.ofNat 64 o', n'⟩ → n ≤ 8192 →
      Spec.Sha256.bytesAt u'.mem p n = Spec.Sha256.bytesAt u.mem p n :=
    fun f h hn => bytesAt_frame f (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h) (by omega_arith)
  have hV₀ : Spec.Sha256.bytesAt t₂.mem (L.scr + BitVec.ofNat 64 2256) D =
      Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) D := by rw [v₂, m₁]
  cases full
  · simp only [Bool.false_eq_true, ite_false, List.append_nil]
    refine wp_nil ⟨hc₄, ?_, ?_⟩
    · rw [← m₁]
      refine f₂.sub (fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) |>.trans (m₃ ▸ f₄.sub fun r hr => ⟨_,
        List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
      · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [Nat.add_zero, bytesAt_add, Offset.add_add, hb₄, keep f₄ (by omega_arith) (by omega_arith) (by omega_arith), m₃, hV₀]
  · simp only [ite_true]
    have hQ4 := hQ4 rfl
    have hQ := hQ rfl
    have hho := hho rfl
    have hho' := hho' rfl
    rw [WP.block_append_iff]
    -- `d`.
    refine WP.mono (copyW_ok (S := L.d) (D := L.scr) (so := 0) (d := 2256 + D + 1) (K := L.q / 4)
      (by decide) (by decide) (by decide) (by decide)
      (by
        rw [BitVec.add_zero]
        exact (hL.dc.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)))
      (by omega_arith) (by omega_arith) (by omega_arith) (L.q / 4) (Nat.le_refl _) t₄
      (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), d₁])
      (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁])
      (fun j hj => hc₄.inD (o := 0 + 4 * j) (by omega_arith) (by omega_arith))
      (fun j hj => hW hc₄ (d := 2256 + D + 1) (n := L.q) (by omega_arith) j (by omega_arith)))
      fun t₅ ⟨k₅, f₅, v₅⟩ => ?_
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hQ4)] at v₅ f₅
    have hc₅ := hc₄.keep hL k₅.rd k₅.wr k₅.sp
      (fun r hr => k₅.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
      f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega_arith))
    -- `h`.
    refine WP.mono (copyW_ok (S := L.B + BitVec.ofNat 64 96) (D := L.scr) (so := ho) (d := 2256 + D + 1 + L.q)
      (K := L.q / 4) (by decide) (by decide) (by decide) (by decide)
      (by rw [fr_add]; exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)
      (L.q / 4) (Nat.le_refl _) t₅
      (by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), b₁])
      (by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁])
      (fun j hj => by rw [fr_add]; exact hc₅.inFr (by omega_arith) (by omega_arith))
      (fun j hj => hW hc₅ (d := 2256 + D + 1 + L.q) (n := L.q) (by omega_arith) j (by omega_arith)))
      fun t₆ ⟨k₆, f₆, v₆⟩ => ?_
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hQ4)] at v₆ f₆
    rw [fr_add] at v₆
    have hc₆ := hc₅.keep hL k₆.rd k₆.wr k₆.sp
      (fun r hr => k₆.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
      f₆ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega_arith))
    refine ⟨hc₆, ?_, ?_⟩
    · rw [← m₁]
      have sub : ∀ {o n : Nat}, 2256 ≤ o → o + n ≤ 2256 + (D + 1 + 2 * L.q) →
          ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, n⟩ : Region)],
            ∃ r' ∈ [(⟨L.scr + BitVec.ofNat 64 2256, D + 1 + 2 * L.q⟩ : Region)], Region.Sub r r' :=
        fun h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_singleton_self _, Offset.sub _ h₁ h₂⟩
      exact (((f₂.sub (sub (by omega_arith) (by omega_arith))).trans (m₃ ▸ f₄.sub (sub (by omega_arith) (by omega_arith)))).trans
        (f₅.sub (sub (by omega_arith) (by omega_arith)))).trans (f₆.sub (sub (by omega_arith) (by omega_arith)))
    · -- `d` and `h`, as on entry.
      have hd₄ : Spec.Sha256.bytesAt t₄.mem L.d L.q = Spec.Sha256.bytesAt t.mem L.d L.q := by
        rw [keepS f₄ ((hL.dc.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)))
          (by omega_arith), m₃, keepS f₂ ((hL.dc.sub_left (Region.sub_prefix (by omega_arith))).sub_right
          (Offset.sub_base _ (by omega_arith))) (by omega_arith), m₁]
      have hh₅ : Spec.Sha256.bytesAt t₅.mem (L.B + BitVec.ofNat 64 (96 + ho)) L.q =
          Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (96 + ho)) L.q := by
        rw [keepS f₅ (hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith), keepS f₄ (hL.stk_scr (by omega_arith) (by omega_arith))
          (by omega_arith), m₃, keepS f₂ (hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith), m₁]
      have e₁ : Spec.Sha256.bytesAt t₆.mem (L.scr + BitVec.ofNat 64 2256) D =
          Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) D := by
        rw [keep (o := 2256) (n := D) f₆ (by omega_arith) (by omega_arith) (by omega_arith),
          keep (o := 2256) (n := D) f₅ (by omega_arith) (by omega_arith) (by omega_arith),
          keep (o := 2256) (n := D) f₄ (by omega_arith) (by omega_arith) (by omega_arith), m₃, hV₀]
      have e₂ : Spec.Sha256.bytesAt t₆.mem (L.scr + BitVec.ofNat 64 (2256 + D)) 1 = [BitVec.ofNat 8 b] := by
        rw [keep (o := 2256 + D) (n := 1) f₆ (by omega_arith) (by omega_arith) (by omega_arith),
          keep (o := 2256 + D) (n := 1) f₅ (by omega_arith) (by omega_arith) (by omega_arith), hb₄]
      have e₃ : Spec.Sha256.bytesAt t₆.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) L.q =
          Spec.Sha256.bytesAt t.mem L.d L.q := by
        rw [keep (o := 2256 + D + 1) (n := L.q) f₆ (by omega_arith) (by omega_arith) (by omega_arith), v₅, BitVec.add_zero, hd₄]
      have e₄ : Spec.Sha256.bytesAt t₆.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1 + L.q)) L.q =
          Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (96 + ho)) L.q := by
        rw [v₆]; exact hh₅
      rw [show D + 1 + 2 * L.q = D + 1 + L.q + L.q by omega_arith, bytesAt_add, bytesAt_add, bytesAt_add, Offset.add_add,
        Offset.add_add, Offset.add_add, show 2256 + (D + 1 + L.q) = 2256 + D + 1 + L.q by omega_arith,
        show 2256 + (D + 1) = 2256 + D + 1 by omega_arith, e₁, e₂, e₃, e₄]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The pointers, and `digest` in `r7`. -/
theorem msgPtrsW_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block (Cfg.msgPtrs true)) t fun u => Ctx L g lr m₀ u ∧ u.mem = t.mem ∧ Kp [.r9, .r10, .r11, .r7] t u ∧
      u.gpr .r11 = L.B + BitVec.ofNat 64 96 ∧ u.gpr .r9 = L.scr ∧ u.gpr .r10 = L.d ∧ u.gpr .r7 = L.dg := by
  have hnB := hL.nB
  rw [show Cfg.msgPtrs true = Cfg.msgPtrs ++ [.load .d .r7 .r11 fDigest] from rfl, WP.block_append_iff]
  refine WP.mono (msgPtrs_ok hL hc) fun t₁ ⟨hc₁, m₁, k₁, b₁, s₁, d₁⟩ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide) (by rw [b₁, fr_add]; rfl)
    (hc₁.inFr (by omega_arith) (by omega_arith)) fun t₂ k₂ m₂ v₂ => wp_nil ?_
  refine ⟨hc₁.kp hL k₂ m₂, by rw [m₂, m₁], ?_, by rw [k₂.gpr _ (by decide), b₁], by rw [k₂.gpr _ (by decide), s₁],
    by rw [k₂.gpr _ (by decide), d₁], by rw [v₂, m₁, hc.pDg]⟩
  exact (k₁.mono (rs' := [.r9, .r10, .r11, .r7])).trans (k₂.mono (rs' := [.r9, .r10, .r11, .r7]))

/-- Zero bytes stored from `r8`. -/
theorem zeros_ok {dst : Reg} {D : Addr} {o K : Nat} (hdr : dst ≠ .r0) (ho : o + K < 2 ^ 15) :
    ∀ k ≤ K, ∀ u : State, u.gpr dst = D → u.gpr .r8 = 0 →
      (∀ j < K, InRegions u.wr (D + BitVec.ofNat 64 (o + j)) 1) →
      WP isa (.block ((List.range k).map fun j => .stb .r8 dst (o + j))) u fun u' =>
        Kp [] u u' ∧ Frame [⟨D + BitVec.ofNat 64 o, K⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (D + BitVec.ofNat 64 o) k = List.replicate k 0
  | 0, _, u, _, _, _ => wp_nil ⟨Kp.refl _ _, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hd, h8, hw => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeros_ok hdr ho k (by omega_arith) u hd h8 hw) fun u₁ ⟨k₁, hf₁, hb₁⟩ => ?_
    refine stepStb (a := D + BitVec.ofNat 64 (o + k)) hdr (by omega_arith) (by rw [k₁.gpr _ (by simp), hd])
      (by rw [k₁.wr]; exact hw k (by omega_arith)) fun u₂ k₂ g₂ m₂ => wp_nil ?_
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (o + k), 1⟩] u₁.mem u₂.mem := by
      rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega_arith) (by omega_arith))
    refine ⟨k₁.trans k₂, hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩), ?_⟩
    rw [bytesAt_add, Offset.add_add, List.replicate_succ', ← hb₁]
    congr 1
    · exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
    · rw [m₂, bytesAt_byte, k₁.gpr _ (by simp), h8]; rfl

/-- The message `V ‖ b ‖ d ‖ 0 … 0 ‖ digest` at `scratch + 2256`, for scalars
of `Q` bytes longer than the digest's `D`. -/
theorem msgW_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {D b : Nat} (ho : Nat)
    (hD4 : D % 4 = 0) (hD : D ≤ 64) (hDn : D ≤ dn) (hQ : L.q ≤ 72) (hDQ : D ≤ L.q) (hb : b < 2 ^ 15) :
    WP isa (.block (Cfg.msgPtrs true ++ Cfg.msg L.q D b true ho true)) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 1 + 2 * L.q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) (D + 1 + 2 * L.q) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) D ++ [BitVec.ofNat 8 b] ++
          (Spec.Sha256.bytesAt t.mem L.d L.q ++ List.replicate (L.q - D) 0 ++
            Spec.Sha256.bytesAt t.mem L.dg D) := by
  have hnB := hL.nB
  have hne := hc.ne
  have hnc := hL.nc
  have hnd := hL.nd
  have hng := hL.ng
  rw [WP.block_append_iff]
  refine WP.mono (msgPtrsW_ok hL hc) fun t₁ ⟨hc₁, m₁, k₁, b₁, s₁, d₁, g₁⟩ => ?_
  simp only [Cfg.msg, ite_true]
  rw [List.append_assoc, WP.block_append_iff]
  -- `V`.
  have hW : ∀ {u : State}, Ctx L g lr m₀ u → ∀ {d n : Nat}, d + n ≤ 8192 → ∀ j, 4 * j + 4 ≤ n →
      InRegions u.wr (L.scr + BitVec.ofNat 64 (d + 4 * j)) 4 := fun hu d n h j hj =>
    hu.inScrW (by omega_arith)
  refine WP.mono (copyW_ok (S := L.B + BitVec.ofNat 64 96) (D := L.scr) (so := 96) (d := 2256) (K := D / 4)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [fr_add]; exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)
    (D / 4) (Nat.le_refl _) t₁ b₁ s₁ (fun j hj => by rw [fr_add]; exact hc₁.inFr (by omega_arith) (by omega_arith))
    (fun j hj => hW hc₁ (d := 2256) (n := D) (by omega_arith) j (by omega_arith)))
    fun t₂ ⟨k₂, f₂, v₂⟩ => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hD4)] at v₂ f₂
  rw [fr_add] at v₂
  have hc₂ := hc₁.keep hL k₂.rd k₂.wr k₂.sp (fun r hr => k₂.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
    f₂ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega_arith))
  -- The byte.
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine stepLi hb fun t₃ k₃ m₃ v₃ => ?_
  refine stepStb (a := L.scr + BitVec.ofNat 64 (2256 + D)) (by decide) (by show 2256 + D < 2 ^ 15; omega_arith)
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁]; rfl) (by rw [k₃.wr]; exact hc₂.inScrW (by omega_arith))
    fun t₄ k₄ g₄ m₄ => ?_
  have hc₃ := hc₂.kp hL k₃ m₃
  have hc₄ := hc₃.keep hL k₄.rd k₄.wr k₄.sp (fun r _ => by rw [g₄]) (ws := [⟨L.scr + BitVec.ofNat 64 (2256 + D), 1⟩])
    (by rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega_arith))
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
      exact Offset.disjoint _ h (by omega_arith) (by omega_arith)) (by omega_arith)
  have keepS : ∀ {u u' : State} {p : Addr} {n o' n' : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 o', n'⟩] u.mem u'.mem →
      Region.Disjoint ⟨p, n⟩ ⟨L.scr + BitVec.ofNat 64 o', n'⟩ → n ≤ 8192 →
      Spec.Sha256.bytesAt u'.mem p n = Spec.Sha256.bytesAt u.mem p n :=
    fun f h hn => bytesAt_frame f (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h) (by omega_arith)
  have hV₀ : Spec.Sha256.bytesAt t₂.mem (L.scr + BitVec.ofNat 64 2256) D =
      Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) D := by rw [v₂, m₁]
  have r₄ : ∀ r, r ≠ .r8 → t₄.gpr r = t₁.gpr r := fun r hr => by
    rw [g₄, k₃.gpr _ (by simp [hr]), k₂.gpr _ (by simp [hr])]
  have hdD : ∀ {o n : Nat}, o + n ≤ 8192 → Region.Disjoint ⟨L.d, L.q⟩ ⟨L.scr + BitVec.ofNat 64 o, n⟩ :=
    fun h => hL.dc.sub_right (Offset.sub_base _ h)
  have hgD : ∀ {o n : Nat}, o + n ≤ 8192 → Region.Disjoint ⟨L.dg, D⟩ ⟨L.scr + BitVec.ofNat 64 o, n⟩ :=
    fun h => (hL.gc.sub_left (Region.sub_prefix hDn)).sub_right (Offset.sub_base _ h)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- `d`.
  refine WP.mono (copyN_ok (S := L.d) (D := L.scr) (so := 0) (d := 2256 + D + 1) (n := L.q)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [BitVec.add_zero]; exact hdD (by omega_arith)) (by omega_arith) (by omega_arith) t₄
    (by rw [r₄ _ (by decide), d₁]) (by rw [r₄ _ (by decide), s₁])
    (fun j k h => hc₄.inD (o := 0 + j) (by omega_arith) (by omega_arith))
    (fun j k h => hc₄.inScrW (by omega_arith))) fun t₅ ⟨k₅, f₅, v₅⟩ => ?_
  rw [BitVec.add_zero] at v₅
  have hc₅ := hc₄.keep hL k₅.rd k₅.wr k₅.sp
    (fun r hr => k₅.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
    f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega_arith))
  -- The zero bytes.
  rw [List.cons_append, List.nil_append]
  refine stepLi (by decide) fun t₆ k₆ m₆ v₆ => ?_
  have hc₆ := hc₅.kp hL k₆ m₆
  have r₆ : ∀ r, r ≠ .r8 → t₆.gpr r = t₁.gpr r := fun r hr => by
    rw [k₆.gpr _ (by simp [hr]), k₅.gpr _ (by simp [hr]), r₄ r hr]
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok (D := L.scr) (o := 2256 + D + 1 + L.q) (K := L.q - D) (by decide) (by omega_arith)
    (L.q - D) (Nat.le_refl _) t₆ (by rw [r₆ _ (by decide), s₁]) (by rw [v₆]; rfl)
    (fun j hj => hc₆.inScrW (by omega_arith))) fun t₇ ⟨k₇, f₇, v₇⟩ => ?_
  have hc₇ := hc₆.keep hL k₇.rd k₇.wr k₇.sp (fun r _ => k₇.gpr r (by simp))
    f₇ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega_arith))
  have r₇ : ∀ r, r ≠ .r8 → t₇.gpr r = t₁.gpr r := fun r hr => by rw [k₇.gpr _ (by simp), r₆ r hr]
  -- The digest.
  refine WP.mono (copyW_ok (S := L.dg) (D := L.scr) (so := 0) (d := 2256 + 1 + 2 * L.q) (K := D / 4)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [BitVec.add_zero, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hD4)]; exact hgD (by omega_arith))
    (by omega_arith) (by omega_arith) (by omega_arith) (D / 4) (Nat.le_refl _) t₇
    (by rw [r₇ _ (by decide), g₁]) (by rw [r₇ _ (by decide), s₁])
    (fun j hj => hc₇.inDg (o := 0 + 4 * j) (by omega_arith) (by omega_arith))
    (fun j hj => hW hc₇ (d := 2256 + 1 + 2 * L.q) (n := D) (by omega_arith) j (by omega_arith)))
    fun t₈ ⟨k₈, f₈, v₈⟩ => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hD4)] at v₈ f₈
  rw [BitVec.add_zero] at v₈
  have hc₈ := hc₇.keep hL k₈.rd k₈.wr k₈.sp
    (fun r hr => k₈.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
    f₈ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by omega_arith))
  refine ⟨hc₈, ?_, ?_⟩
  · rw [← m₁]
    have sub : ∀ {o n : Nat}, 2256 ≤ o → o + n ≤ 2256 + (D + 1 + 2 * L.q) →
        ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, n⟩ : Region)],
          ∃ r' ∈ [(⟨L.scr + BitVec.ofNat 64 2256, D + 1 + 2 * L.q⟩ : Region)], Region.Sub r r' :=
      fun h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ h₁ h₂⟩
    exact ((((f₂.sub (sub (by omega_arith) (by omega_arith))).trans (m₃ ▸ f₄.sub (sub (by omega_arith) (by omega_arith)))).trans
      (f₅.sub (sub (by omega_arith) (by omega_arith)))).trans (m₆ ▸ f₇.sub (sub (by omega_arith) (by omega_arith)))).trans
      (f₈.sub (sub (by omega_arith) (by omega_arith)))
  · -- `d` and the digest, as on entry.
    have hd₄ : Spec.Sha256.bytesAt t₄.mem L.d L.q = Spec.Sha256.bytesAt t.mem L.d L.q := by
      rw [keepS f₄ (hdD (by omega_arith)) (by omega_arith), m₃, keepS f₂ (hdD (by omega_arith)) (by omega_arith), m₁]
    have hg₇ : Spec.Sha256.bytesAt t₇.mem L.dg D = Spec.Sha256.bytesAt t.mem L.dg D := by
      rw [keepS f₇ (hgD (by omega_arith)) (by omega_arith), m₆, keepS f₅ (hgD (by omega_arith)) (by omega_arith),
        keepS f₄ (hgD (by omega_arith)) (by omega_arith), m₃, keepS f₂ (hgD (by omega_arith)) (by omega_arith), m₁]
    have e₁ : Spec.Sha256.bytesAt t₈.mem (L.scr + BitVec.ofNat 64 2256) D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) D := by
      rw [keep (o := 2256) (n := D) f₈ (by omega_arith) (by omega_arith) (by omega_arith),
        keep (o := 2256) (n := D) f₇ (by omega_arith) (by omega_arith) (by omega_arith), m₆,
        keep (o := 2256) (n := D) f₅ (by omega_arith) (by omega_arith) (by omega_arith),
        keep (o := 2256) (n := D) f₄ (by omega_arith) (by omega_arith) (by omega_arith), m₃, hV₀]
    have e₂ : Spec.Sha256.bytesAt t₈.mem (L.scr + BitVec.ofNat 64 (2256 + D)) 1 = [BitVec.ofNat 8 b] := by
      rw [keep (o := 2256 + D) (n := 1) f₈ (by omega_arith) (by omega_arith) (by omega_arith),
        keep (o := 2256 + D) (n := 1) f₇ (by omega_arith) (by omega_arith) (by omega_arith), m₆,
        keep (o := 2256 + D) (n := 1) f₅ (by omega_arith) (by omega_arith) (by omega_arith), hb₄]
    have e₃ : Spec.Sha256.bytesAt t₈.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) L.q =
        Spec.Sha256.bytesAt t.mem L.d L.q := by
      rw [keep (o := 2256 + D + 1) (n := L.q) f₈ (by omega_arith) (by omega_arith) (by omega_arith),
        keep (o := 2256 + D + 1) (n := L.q) f₇ (by omega_arith) (by omega_arith) (by omega_arith), m₆, v₅, hd₄]
    have e₄ : Spec.Sha256.bytesAt t₈.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1 + L.q)) (L.q - D) =
        List.replicate (L.q - D) 0 := by
      rw [keep (o := 2256 + D + 1 + L.q) (n := L.q - D) f₈ (by omega_arith) (by omega_arith) (by omega_arith), v₇]
    have e₅ : Spec.Sha256.bytesAt t₈.mem (L.scr + BitVec.ofNat 64 (2256 + 1 + 2 * L.q)) D =
        Spec.Sha256.bytesAt t.mem L.dg D := by
      rw [v₈, hg₇]
    rw [show D + 1 + 2 * L.q = D + 1 + L.q + (L.q - D) + D by omega_arith, bytesAt_add, bytesAt_add, bytesAt_add,
      bytesAt_add, Offset.add_add, Offset.add_add, Offset.add_add, Offset.add_add,
      show 2256 + (D + 1 + L.q + (L.q - D)) = 2256 + 1 + 2 * L.q by omega_arith,
      show 2256 + (D + 1 + L.q) = 2256 + D + 1 + L.q by omega_arith,
      show 2256 + (D + 1) = 2256 + D + 1 by omega_arith, e₁, e₂, e₃, e₄, e₅]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
