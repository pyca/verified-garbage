module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Twos
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the stages

Each stage of `RecoverDet.main` between two changes of width, against the
model of `Proof/Rsa/RecoverDetModel.lean`: `d e - 1` and whether `d e ≥ 2`
(`deMinus_ok`), …
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet

/-- The mask word. -/
abbrev mw (m : Mem) (B : Addr) : BitVec 64 := word m B (8 * Impl.Bignum.X86_64.Public.sMask)

theorem mask_eq_zero (b : Bool) : mask b = 0 ↔ b = false := by cases b <;> decide

/-- `andZero` after a borrow `b` in `rbp`: the mask and'ed with `!b`. -/
theorem andB_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c b : Bool} (hm : mw s.mem B = mask c)
    (hb : s.gpr .rbp = mask b) :
    WP isa (.block CrtValues.andZero) s fun t =>
      t.mem = s.mem.writeW (off B (8 * Impl.Bignum.X86_64.Public.sMask)) (mask (c && !b)) ∧ Keep [.rbp] s t :=
  WP.mono (andZero_ok h hm (z := b = false) (by rw [hb]; exact mask_eq_zero b)) fun t ⟨mt, k⟩ =>
    ⟨by rw [mt]; cases b <;> rfl, k⟩

/-- A number zero but its low word one. -/
theorem wv_one {m : Mem} {B : Addr} {d n : Nat} (hn : 1 ≤ n) (hz : wv m B d n = 0) (hd : d + 8 * n ≤ 2 ^ 64) :
    wv (m.writeW (off B d) (1 : BitVec 64)) B d n = 1 := by
  rw [wv_low hn, word_writeW_self, (writeW_outside m B (1 : BitVec 64) (by omega_arith)).wv (Or.inr (by omega_arith))
    (by omega_arith)]
  have hz' := (wv_eq_zero_iff _ _ _ _).mp hz
  rw [wv_zero (n := n - 1) fun q hq => by
    have := hz' (1 + q) (by omega_arith)
    rwa [show d + 8 * (1 + q) = d + 8 + 8 * q by omega_arith] at this]
  rfl

/-- A subtraction's result, from its equation. -/
theorem wsub_of_eq {b a c t : Nat} {x : Bool} (h : t + c = a + 2 ^ b * x.toNat) (ht : t < 2 ^ b) (ha : a < 2 ^ b)
    (hc : c < 2 ^ b) : t = wsub b a c := by
  unfold wsub
  cases x
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
    rw [show a + 2 ^ b - c = t + 2 ^ b by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  · simp only [Bool.toNat_true, Nat.mul_one] at h
    rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

macro "st_omega" : tactic =>
  `(tactic| (simp only [DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith))

/-! ## `d e - 1` (wide) -/

/-- `deMinus`: one (wide array 1, all its words), `x = d e - 1` (wide array 2),
and the mask and'ed with whether `d e ≥ 2`. -/
theorem deMinus_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {DE : Nat} {c : Bool}
    (hM : wv s.mem B (slot w 5) w = DE) (hm : mw s.mem B = mask c) :
    WP isa (seqs deMinus) s fun t =>
      wv t.mem B (slot w 1) (w + 2) = 1 ∧ wv t.mem B (slot w 2) w = deX (64 * w) DE ∧
      mw t.mem B = mask (c && okDE (64 * w) DE) ∧
      FrmP B (fun y => (slot w 1 ≤ y ∧ y < slot w 4) ∨ (176 ≤ y ∧ y < 184)) s.mem t.mem ∧
      Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .rbp, .r10, .rsi] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw1 := h.w1
  have hDE : DE < 2 ^ (64 * w) := hM ▸ wv_lt _ _ _ _
  simp only [deMinus, seqs]
  refine WP.seq (WP.mono (zeroA_ok h (j := 1) (by decide)) fun t₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (by st_omega) k1 (by simp)
  refine WP.seq (WP.mono (setOneA_ok h₁ (j := 1) (by decide)) fun t₂ ⟨m2, k2⟩ => ?_)
  have o2 : Outside B (slot w 1) 8 t₁.mem t₂.mem := by rw [m2]; exact writeW_outside _ _ _ (by st_omega)
  have h₂ := h₁.congrO o2 (by st_omega) k2 (by simp)
  have v1 : wv t₂.mem B (slot w 1) (w + 2) = 1 := by rw [m2]; exact wv_one (by omega_arith) z1 (by st_omega)
  have M₂ : wv t₂.mem B (slot w 5) w = DE := by
    rw [o2.wv (by st_omega) (by st_omega), o1.wv (by st_omega) (by st_omega), hM]
  have one₂ : wv t₂.mem B (slot w 1) w = 1 := by
    rw [wv_low_of_lt (m := t₂.mem) (B := B) (e := slot w 1) (v := w) (w := w + 2) (by omega_arith)
      (by rw [v1]; exact Nat.one_lt_two_pow (by omega_arith))]
    exact v1
  -- `x = d e - 1`.
  refine WP.seq (WP.mono (subA_ok h₂ (t := 2) (a := 5) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₃ ⟨hb3, e3, o3, k3⟩ => ?_)
  rw [M₂, one₂] at hb3 e3
  have h₃ := h₂.congrO o3 (by st_omega) k3 (by simp)
  have hm₃ : mw t₃.mem B = mask c := by
    unfold mw at hm ⊢
    rw [o3.word (by st_omega) (by st_omega), o2.word (by st_omega) (by st_omega), o1.word (by st_omega) (by st_omega),
      hm]
  refine WP.seq (WP.mono (andB_ok h₃ hm₃ hb3) fun t₄ ⟨m4, k4⟩ => ?_)
  have h₄ := h₃.congrW m4 (by st_omega) (by decide) k4 (by simp)
  have o4 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₃.mem t₄.mem := by
    rw [m4]; exact writeW_outside _ _ _ (by st_omega)
  have X₄ : wv t₄.mem B (slot w 2) w = deX (64 * w) DE := by
    rw [o4.wv (by st_omega) (by st_omega)]
    exact wsub_of_eq e3 (wv_lt _ _ _ _) hDE (Nat.one_lt_two_pow (by omega_arith))
  have one₄ : wv t₄.mem B (slot w 1) w = 1 := by
    rw [o4.wv (by st_omega) (by st_omega), o3.wv (by st_omega) (by st_omega), one₂]
  -- `x - 1`.
  refine WP.seq (WP.mono (subA_ok h₄ (t := 3) (a := 2) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₅ ⟨hb5, _, o5, k5⟩ => ?_)
  rw [X₄, one₄] at hb5
  have h₅ := h₄.congrO o5 (by st_omega) k5 (by simp)
  have hm₅ : mw t₅.mem B = mask (c && !decide (DE < 1)) := by
    unfold mw
    rw [o5.word (by st_omega) (by st_omega), m4, word_writeW_self]
  refine WP.mono (andB_ok h₅ hm₅ hb5) fun t ⟨m6, k6⟩ => ?_
  have o6 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₅.mem t.mem := by
    rw [m6]; exact writeW_outside _ _ _ (by st_omega)
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' →
      (∀ y, o ≤ y → y < o + n → (slot w 1 ≤ y ∧ y < slot w 4) ∨ (176 ≤ y ∧ y < 184)) →
      FrmP B (fun y => (slot w 1 ≤ y ∧ y < slot w 4) ∨ (176 ≤ y ∧ y < 184)) m m' := fun ho hP => FrmP.of_out ho hP
  have f16 := (((((fr o1 fun y => by st_omega).trans (fr o2 fun y => by st_omega)).trans
    (fr o3 fun y => by st_omega)).trans (fr o4 fun y => by st_omega)).trans (fr o5 fun y => by st_omega)).trans
    (fr o6 fun y => by st_omega)
  have k16 := (((((k1.trans k2).trans k3).trans k4).trans k5).trans k6)
  refine ⟨?_, ?_, ?_, f16, k16.mono (by simp)⟩
  · rw [o6.wv (by st_omega) (by st_omega), o5.wv (by st_omega) (by st_omega), o4.wv (by st_omega) (by st_omega),
      o3.wv (by st_omega) (by st_omega), v1]
  · rw [o6.wv (by st_omega) (by st_omega), o5.wv (by st_omega) (by st_omega), X₄]
  · unfold mw; rw [m6, word_writeW_self, okDE, Bool.not_or, Bool.and_assoc]

/-- A number of `n + k` words whose top `k` are zero. -/
theorem wv_top_zero {m : Mem} {B : Addr} {d n k : Nat} (h : wv m B (d + 8 * n) k = 0) :
    wv m B d (n + k) = wv m B d n := by
  rw [wv_add, h, Nat.mul_zero, Nat.add_zero]

/-- The low `n` words of a number of `n + k` words. -/
theorem wv_low_mod {m : Mem} {B : Addr} {d n k : Nat} : wv m B d n = wv m B d (n + k) % 2 ^ (64 * n) := by
  rw [wv_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wv_lt _ _ _ _)]

/-- Part of a zero number. -/
theorem wv_zero_sub {m : Mem} {B : Addr} {d n a k : Nat} (h : wv m B d n = 0) (hk : a + k ≤ n) :
    wv m B (d + 8 * a) k = 0 := by
  have h' := (wv_eq_zero_iff _ _ _ _).mp h
  refine (wv_eq_zero_iff _ _ _ _).mpr fun q hq => ?_
  rw [show d + 8 * a + 8 * q = d + 8 * (a + q) by omega_arith]
  exact h' _ (by omega_arith)

/-- The halvings' state after `64 w` steps from `n - 1`, `x mod 2^(64 w)` and `x`. -/
abbrev twosSt (w N X : Nat) : Nat × Nat × Nat :=
  (twoStep (64 * (2 * w + 2)))^[64 * w] (wsub (64 * w) N 1, X % 2 ^ (64 * w), X)

theorem mask_and1 (a b : Bool) : mask a &&& mask b = mask (a && b) := by cases a <;> cases b <;> decide

theorem sub8_ofNat {a : Nat} (h : 8 ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - 8 = BitVec.ofNat 64 (a - 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]
  omega_arith

/-- `setEl`: `e`'s length `4 w - 8`, for `Recover.prod`. -/
theorem setEl_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block setEl) s fun t =>
      t.mem = s.mem.writeW (off B (8 * Impl.Bignum.X86_64.Public.sElen)) (BitVec.ofNat 64 (4 * w - 8)) ∧
        Keep [.r12, .r9, .rax] s t := by
  have h256 := h.h256
  have hw2 := h.w2
  have hw1 := h.w1
  unfold setEl
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, _, m₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (8 * Impl.Bignum.X86_64.Public.sElen))
    (BitVec.ofNat 64 (4 * w - 8))) ?_ rfl) fun t ⟨mt, k₂⟩ => ⟨mt, (k₁.trans k₂).mono (by simp)⟩
  have hs₁ := h.scr.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  xrun [State.ea, hdr, hdi₁, hdrOff, h12, hs₁.st (d := 8 * Impl.Bignum.X86_64.Public.sElen)
    (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega_arith), m₁, ofNat_dbl]
  rw [show 2 * (2 * w) = 4 * w by omega_arith, sub8_ofNat (by omega_arith) (by omega_arith)]

/-- `andNz`: the mask in `rbp` and'ed into `sMask`. -/
theorem andNz_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {b c : Bool} (hm : mw s.mem B = mask c)
    (hb : s.gpr .rbp = mask b) :
    WP isa (.block andNz) s fun t =>
      t.mem = s.mem.writeW (off B (8 * Impl.Bignum.X86_64.Public.sMask)) (mask (c && b)) ∧ Keep [.rbp] s t := by
  have h256 := h.h256
  refine WP.keep [.rbp] (Q := fun t => t.mem = s.mem.writeW (off B (8 * Impl.Bignum.X86_64.Public.sMask))
    (mask (c && b))) ?_ rfl
  unfold andNz
  unfold mw at hm
  xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by st_omega),
    h.scr.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by st_omega), hm, hb]
  rw [mask_and1, Bool.and_comm]

/-- `gcdW`: `gcdN` at the width `w`. -/
theorem gcdW_ok [InvLaw] {s : State} {B : Addr} {Z w iU iV iM : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (hw20 : w < 2 ^ 20) (hU : iU < 16) (hV : iV < 16) (hM : iM < 16) :
    WP isa (gcdW iU iV iM) s fun t =>
      Frm B [(slot w iV, 8 * w), (slot w 16, 80 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t ∧
      (wv s.mem B (slot w iM) w % 2 = 1 →
        wv t.mem B (slot w iV) w = Nat.gcd (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w)) := by
  unfold gcdW
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9₁, m₁, k₁⟩ => ?_))
  refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 w ∧ t.mem = s₁.mem) (by xrun [h12]) rfl)
    fun s₂ ⟨⟨r13₂, m₂⟩, k₂⟩ => ?_
  have hm : s₂.mem = s.mem := by rw [m₂, m₁]
  have h₂ : Ws s₂ B Z w := h.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (k₁.trans k₂) (by decide)
  refine WP.mono (InvLaw.gcdN_ok h₂ hZ ((k₂.gpr (by decide)).trans h9₁) r13₂ (by have := h.w1; omega_arith)
    (Nat.le_refl _) hw20 hU hV hM) fun t ⟨dt, ft, kt, ht⟩ => ⟨by rw [← hm]; exact ft, ?_, by rw [← hm]; exact ht⟩
  have k := ((k₁.trans k₂).trans kt).mono (rs' := .rdi :: [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11,
    .r12, .r13, .r14, .r15]) (by decide)
  refine ⟨fun x hx => ?_, k.2⟩
  by_cases e : x = .rdi
  · subst e; exact dt.trans h.rdi.symm
  · exact k.1 x fun hm => (List.mem_cons.mp hm).elim e hx

end VG.Proof.Rsa.X86_64.Rd
