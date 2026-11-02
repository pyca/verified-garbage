module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Sqrt
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Rsa.X86_64.RpProd
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

/-! ## The halvings and the GCD (narrow) -/

theorem ofNat_shl6 {a : Nat} (h : 64 * a < 2 ^ 64) : BitVec.ofNat 64 a <<< 6 = BitVec.ofNat 64 (64 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega_arith)]
  rw [show 2 ^ 6 = 64 from rfl, Nat.mul_comm]

/-- `countN`: `64 w` into the count. -/
theorem countN_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block countN) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sCt)) (BitVec.ofNat 64 (64 * w)) ∧ Keep [.r12, .r9, .rax] s t := by
  have h256 := h.h256
  have hw2 := h.w2
  unfold countN
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, _, m₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sCt))
    (BitVec.ofNat 64 (64 * w))) ?_ rfl) fun t ⟨mt, k₂⟩ => ⟨mt, (k₁.trans k₂).mono (by simp)⟩
  have hs₁ := h.scr.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  xrun [State.ea, hdr, hdi₁, hdrOff, h12, hs₁.st (d := 8 * sCt) (by simp only [sCt, sFn]; omega_arith), m₁,
    ofNat_shl6 (show 64 * w < 2 ^ 64 by omega_arith)]

/-- `countW`: `64 (w + 1)` into the count. -/
theorem countW_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block countW) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sCt)) (BitVec.ofNat 64 (64 * (w + 1))) ∧ Keep [.r12, .r9, .rax] s t := by
  have h256 := h.h256
  have hw2 := h.w2
  unfold countW
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, _, m₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sCt))
    (BitVec.ofNat 64 (64 * (w + 1)))) ?_ rfl) fun t ⟨mt, k₂⟩ => ⟨mt, (k₁.trans k₂).mono (by simp)⟩
  have hs₁ := h.scr.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  xrun [State.ea, hdr, hdi₁, hdrOff, h12, hs₁.st (d := 8 * sCt) (by simp only [sCt, sFn]; omega_arith), m₁,
    ofNat_add_one, ofNat_shl6 (show 64 * (w + 1) < 2 ^ 64 by omega_arith)]

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

/-- What the halvings and the GCD change. -/
def TgP (w y : Nat) : Prop := (slot w 4 ≤ y ∧ y < slot w 8) ∨ (slot w 12 ≤ y ∧ y < slot w 26) ∨ (200 ≤ y ∧ y < 224)

macro "tg_omega" : tactic =>
  `(tactic| (simp only [TgP, TwosP, DOk, Bignum.slot, hdrBytes, sCt, sU, sB2, sFn]; omega_arith))

/-- `twosInit`, the halvings and the GCD: `x` (wide array 2) doubled as `twoStep`
says, and `g = gcd(u, x₂)` in wide array 6 (narrow 12 and 13). -/
theorem twosG_ok [InvLaw] {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ26 : slot w 26 ≤ Z)
    (hw20 : w < 2 ^ 20) {N X : Nat} (hN : wv s.mem B (slot w 0) w = N) (hN2 : 2 ≤ N)
    (hone : wv s.mem B (slot w 2) w = 1) (hX : wv s.mem B (slot w 4) (2 * w + 2) = X) :
    WP isa (seqs (twosInit ++ [.loop twosBody .ne, inverse 6 12 15 7])) s fun t =>
      wv t.mem B (slot w 4) (2 * w + 2) = (twosSt w N X).2.2 ∧
      wv t.mem B (slot w 12) (2 * (w + 2)) = Nat.gcd (twosSt w N X).1 (twosSt w N X).2.1 ∧
      FrmP B (TgP w) s.mem t.mem ∧ Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13,
        .r14, .r15] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 26 * (8 * (w + 2)) ≤ Z := hZ26
  have hw1 := h.w1
  have hNlt : N < 2 ^ (64 * w) := hN ▸ wv_lt _ _ _ _
  simp only [twosInit, List.cons_append, List.nil_append, seqs]
  -- `x₂ := x mod 2^(64 w)`, its top words zero.
  refine WP.seq (WP.mono (zeroA_ok h (j := 6) (by decide)) fun t₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (by tg_omega) k1 (by simp)
  refine WP.seq (WP.mono (copyA_ok h₁ (o := 6) (a := 4) (by decide) (by decide) (by decide)) fun t₂ ⟨v2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by tg_omega) k2 (by simp)
  -- `u := n - 1`, its top words zero.
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := 7) (by decide)) fun t₃ ⟨z3, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by tg_omega) k3 (by simp)
  refine WP.seq (WP.mono (subA_ok h₃ (t := 7) (a := 0) (b := 2) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₄ ⟨_, e4, o4, k4⟩ => ?_)
  have h₄ := h₃.congrO o4 (by tg_omega) k4 (by simp)
  -- `g`'s arrays cleared, and the count.
  refine WP.seq (WP.mono (zeroA_ok h₄ (j := 12) (by decide)) fun t₅ ⟨z5, o5, k5⟩ => ?_)
  have h₅ := h₄.congrO o5 (by tg_omega) k5 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₅ (j := 13) (by decide)) fun t₆ ⟨z6, o6, k6⟩ => ?_)
  have h₆ := h₅.congrO o6 (by tg_omega) k6 (by simp)
  refine WP.seq (WP.mono (countN_ok h₆) fun t₇ ⟨m7, k7⟩ => ?_)
  have h₇ := h₆.congrW m7 (by tg_omega) (by decide) k7 (by simp)
  have o7 : Outside B (8 * sCt) 8 t₆.mem t₇.mem := by rw [m7]; exact writeW_outside _ _ _ (by tg_omega)
  -- The values before the halvings.
  have X₁ : wv t₁.mem B (slot w 4) (2 * w + 2) = X := by rw [o1.wv (by tg_omega) (by tg_omega), hX]
  have U₇ : wv t₇.mem B (slot w 7) w = wsub (64 * w) N 1 := by
    rw [o7.wv (by tg_omega) (by tg_omega), o6.wv (by tg_omega) (by tg_omega), o5.wv (by tg_omega) (by tg_omega)]
    have eN : wv t₃.mem B (slot w 0) w = N := by
      rw [o3.wv (by tg_omega) (by tg_omega), o2.wv (by tg_omega) (by tg_omega), o1.wv (by tg_omega) (by tg_omega), hN]
    have e1 : wv t₃.mem B (slot w 2) w = 1 := by
      rw [o3.wv (by tg_omega) (by tg_omega), o2.wv (by tg_omega) (by tg_omega), o1.wv (by tg_omega) (by tg_omega), hone]
    rw [eN, e1] at e4
    exact wsub_of_eq e4 (wv_lt _ _ _ _) hNlt (Nat.one_lt_two_pow (by omega_arith))
  have X2₇ : wv t₇.mem B (slot w 6) w = X % 2 ^ (64 * w) := by
    rw [o7.wv (by tg_omega) (by tg_omega), o6.wv (by tg_omega) (by tg_omega), o5.wv (by tg_omega) (by tg_omega),
      o4.wv (by tg_omega) (by tg_omega), o3.wv (by tg_omega) (by tg_omega), v2, ← X₁,
      show 2 * w + 2 = w + (w + 2) by omega_arith]
    exact wv_low_mod
  have X₇ : wv t₇.mem B (slot w 4) (2 * w + 2) = X := by
    rw [o7.wv (by tg_omega) (by tg_omega), o6.wv (by tg_omega) (by tg_omega), o5.wv (by tg_omega) (by tg_omega),
      o4.wv (by tg_omega) (by tg_omega), o3.wv (by tg_omega) (by tg_omega), o2.wv (by tg_omega) (by tg_omega), X₁]
  have z7₇ : word t₇.mem B (slot w 7 + 8 * w) = 0 := by
    rw [o7.word (by tg_omega) (by tg_omega), o6.word (by tg_omega) (by tg_omega), o5.word (by tg_omega) (by tg_omega),
      o4.word (by tg_omega) (by tg_omega)]
    have := wv_zero_sub (a := w) (k := 1) z3 (by omega_arith)
    exact BitVec.eq_of_toNat_eq (by simpa [wv] using this)
  have z6₇ : word t₇.mem B (slot w 6 + 8 * w) = 0 := by
    rw [o7.word (by tg_omega) (by tg_omega), o6.word (by tg_omega) (by tg_omega), o5.word (by tg_omega) (by tg_omega),
      o4.word (by tg_omega) (by tg_omega), o3.word (by tg_omega) (by tg_omega), o2.word (by tg_omega) (by tg_omega)]
    have := wv_zero_sub (a := w) (k := 1) z1 (by omega_arith)
    exact BitVec.eq_of_toNat_eq (by simpa [wv] using this)
  have hct : word t₇.mem B (8 * sCt) = BitVec.ofNat 64 (64 * w) := by rw [m7, word_writeW_self]
  -- The halvings.
  refine WP.seq (WP.mono (twosLoop_ok h₇ hct z7₇ z6₇) fun t₈ hI => ?_)
  rw [U₇, X2₇, X₇] at hI
  have h₈ := hI.ws
  have hv8 := hI.val
  -- The GCD.
  refine WP.mono (InvLaw.inverse_ok h₈ hZ26 hw20 (iU := 6) (iV := 12) (iX₂ := 15) (iM := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t₉ ⟨_, f9, k9, hg9⟩ => ?_
  have uodd : wv t₈.mem B (slot w 7) w % 2 = 1 := by
    have := congrArg Prod.fst hv8
    simp only at this
    rw [this]
    exact (twos_odd _ _ (by rw [wsub_of_le hNlt (by omega_arith)]; omega_arith)
      (by rw [wsub_of_le hNlt (by omega_arith)]; omega_arith)).1
  obtain ⟨hg, -⟩ := hg9 uodd
  have f9' : FrmP B (fun y => (slot w 12 ≤ y ∧ y < slot w 12 + 8 * w) ∨ (slot w 15 ≤ y ∧ y < slot w 15 + 8 * w) ∨
      (slot w 16 ≤ y ∧ y < slot w 16 + 80 * (w + 2))) t₈.mem t₉.mem := FrmP.of_frm f9 fun r hr y h1 h2 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨h1, h2⟩
    · exact .inr (.inl ⟨h1, h2⟩)
    · exact .inr (.inr ⟨h1, h2⟩)
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → TgP w y) →
      FrmP B (TgP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨?_, ?_, ?_, (((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans
    hI.keep).trans k9 |>.mono (by simp)⟩
  · rw [f9'.wv_eq (fun y => by tg_omega) (by tg_omega)]
    exact congrArg (fun p => p.2.2) hv8
  · -- `g`'s top words are still zero.
    have zt : wv t₉.mem B (slot w 12 + 8 * w) (w + 4) = 0 := by
      rw [f9'.wv_eq (fun y => by tg_omega) (by tg_omega), hI.frm.wv_eq (fun y => by tw_omega) (by tg_omega),
        o7.wv (by tg_omega) (by tg_omega)]
      have z5' : wv t₆.mem B (slot w 12) (w + 2) = 0 := by rw [o6.wv (by tg_omega) (by tg_omega)]; exact z5
      rw [show w + 4 = 2 + (w + 2) by omega_arith, wv_add, wv_zero_sub (a := w) (k := 2) z5' (by omega_arith),
        show slot w 12 + 8 * w + 8 * 2 = slot w 13 by simp only [slot, hdrBytes]; omega_arith, z6]
    rw [show 2 * (w + 2) = w + (w + 4) by omega_arith, wv_top_zero zt, hg, Nat.gcd_comm]
    have e1 := congrArg Prod.fst hv8
    have e2 := congrArg (fun p => p.2.1) hv8
    simp only at e1 e2
    rw [e1, e2]
  · exact ((((((((fr o1 fun y => by tg_omega).trans (fr o2 fun y => by tg_omega)).trans (fr o3 fun y => by tg_omega)).trans
      (fr o4 fun y => by tg_omega)).trans (fr o5 fun y => by tg_omega)).trans (fr o6 fun y => by tg_omega)).trans
      (fr o7 fun y => by tg_omega)).trans (hI.frm.mono fun y => by tg_omega)).trans
      (f9'.mono fun y => by tg_omega)

/-! ## `a`, `m`, `r` and whether `m < n` (wide) -/

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

/-- What `divA` changes: `e`'s length, the mask, and the wide arrays from 6 on. -/
def DaP (w y : Nat) : Prop := (160 ≤ y ∧ y < 168) ∨ (176 ≤ y ∧ y < 184) ∨ (slot w 6 ≤ y ∧ y < slot w 16)

macro "da_omega" : tactic =>
  `(tactic| (simp only [DaP, DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask,
    Impl.Bignum.X86_64.Public.sElen, sFn, ar]; omega_arith))

/-- `divA` (wide, `w = 2 v + 2`): `a = g x mod 2^(64 w)` for `g` (wide array 6,
below `2^(64 v)`) and `x` (wide array 2), `m = a / n` into wide array 7 and
`r = a mod n` into wide array 6, and the mask and'ed with whether `m < n`. -/
theorem divA_ok {s : State} {B : Addr} {Z w v : Nat} (h : Ws s B Z w) (hwv : w = 2 * v + 2) (hv1 : 1 ≤ v) {N G X : Nat}
    {c : Bool} (hN : wv s.mem B (slot w 0) w = N) (hN0 : 0 < N) (hG : wv s.mem B (slot w 6) w = G)
    (hGv : G < 2 ^ (64 * v)) (hX : wv s.mem B (slot w 2) w = X) (hm : mw s.mem B = mask c) :
    WP isa (seqs divA) s fun t =>
      wv t.mem B (slot w 7) w = X * G % 2 ^ (64 * w) / N ∧ wv t.mem B (slot w 6) w = X * G % 2 ^ (64 * w) % N ∧
      mw t.mem B = mask (c && decide (X * G % 2 ^ (64 * w) / N < N)) ∧
      FrmP B (DaP w) s.mem t.mem ∧ Keep [.r12, .r9, .rax, .rsi, .rbx, .r14, .r8, .r10, .r15, .r11, .r13, .rdx,
        .rbp, .rcx] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have hw4 : (4 * w - 8 + 7) / 8 = v := by omega_arith
  simp only [divA, List.cons_append, List.nil_append, seqs]
  -- `e`'s length, `g` and `x` as `Recover.prod` takes them.
  refine WP.seq (WP.mono (setEl_ok h) fun t₁ ⟨m1, k1⟩ => ?_)
  have h₁ := h.congrW m1 (by da_omega) (by decide) k1 (by simp)
  have o1 : Outside B (8 * Impl.Bignum.X86_64.Public.sElen) 8 s.mem t₁.mem := by
    rw [m1]; exact writeW_outside _ _ _ (by da_omega)
  refine WP.seq (WP.mono (copyA_ok h₁ (o := 8) (a := 6) (by decide) (by decide) (by decide)) fun t₂ ⟨v2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by da_omega) k2 (by simp)
  refine WP.seq (WP.mono (copyA_ok h₂ (o := 9) (a := 2) (by decide) (by decide) (by decide)) fun t₃ ⟨v3, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by da_omega) k3 (by simp)
  have G₃ : wv t₃.mem B (slot w 8) w = G := by
    rw [o3.wv (by da_omega) (by da_omega), v2, o1.wv (by da_omega) (by da_omega), hG]
  have X₃ : wv t₃.mem B (slot w 9) w = X := by
    rw [v3, o2.wv (by da_omega) (by da_omega), o1.wv (by da_omega) (by da_omega), hX]
  have el₃ : word t₃.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * w - 8) := by
    rw [o3.word (by da_omega) (by da_omega), o2.word (by da_omega) (by da_omega), m1, word_writeW_self]
  -- `a = x g`.
  refine wp_seqs_append (by simp [Recover.prod]) (by simp) (WP.mono (prod_ok h₃ el₃ (by omega_arith) (by omega_arith)
    (by rw [hw4]; show wv t₃.mem B (slot w 8) w < _; rw [G₃]; exact hGv)) fun t₄ ⟨v4, o4, k4⟩ => ?_)
  simp only [Recover.aE, Recover.aD, Recover.aM] at v4 o4
  rw [G₃, X₃] at v4
  have h₄ := h₃.congrO o4 (by da_omega) k4 (by simp)
  have N₄ : wv t₄.mem B (slot w 0) w = N := by
    rw [o4.wv (by da_omega) (by da_omega), o3.wv (by da_omega) (by da_omega), o2.wv (by da_omega) (by da_omega),
      o1.wv (by da_omega) (by da_omega), hN]
  have A₄ : wv t₄.mem B (slot w 10) w = X * G % 2 ^ (64 * w) := by
    rw [← v4, show 2 * (w + 2) = w + (w + 4) by omega_arith]; exact wv_low_mod
  -- `m` and `r`.
  simp only [seqs]
  refine WP.seq (WP.mono (divmod_ok h₄.scr h₄.rdi h₄.hw h₄.hS (by omega_arith) hw2 hZ (iQ := 10) (iR := 12) (iD := 0)
    (iT := 13) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t₅ ⟨_, f5, k5, hq5⟩ => ?_)
  rw [N₄, A₄] at hq5
  obtain ⟨r5, q5⟩ := hq5 hN0
  have f5' : FrmP B (fun y => slot w 10 ≤ y ∧ y < slot w 14) t₄.mem t₅.mem := FrmP.of_frm f5 fun r hr y h1 h2 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [Bignum.slot, hdrBytes] at h1 h2 ⊢ <;> omega_arith
  have h₅ := h₄.congrP f5' (fun y => by da_omega) k5 (by decide)
  have N₅ : wv t₅.mem B (slot w 0) w = N := by rw [f5'.wv_eq (fun y => by da_omega) (by da_omega), N₄]
  -- Whether `m < n`.
  refine WP.seq (WP.mono (subA_ok h₅ (t := 14) (a := 10) (b := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₆ ⟨hb6, _, o6, k6⟩ => ?_)
  rw [q5, N₅] at hb6
  have h₆ := h₅.congrO o6 (by da_omega) k6 (by simp)
  have hm₆ : mw t₆.mem B = mask c := by
    unfold mw at hm ⊢
    rw [o6.word (by da_omega) (by da_omega), f5'.word_eq (fun y => by da_omega) (by da_omega),
      o4.word (by da_omega) (by da_omega), o3.word (by da_omega) (by da_omega), o2.word (by da_omega) (by da_omega),
      o1.word (by da_omega) (by da_omega), hm]
  refine WP.seq (WP.mono (andNz_ok h₆ hm₆ hb6) fun t₇ ⟨m7, k7⟩ => ?_)
  have h₇ := h₆.congrW m7 (by da_omega) (by decide) k7 (by simp)
  have o7 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₆.mem t₇.mem := by
    rw [m7]; exact writeW_outside _ _ _ (by da_omega)
  -- `m` and `r` into wide arrays 7 and 6.
  refine WP.seq (WP.mono (copyA_ok h₇ (o := 7) (a := 10) (by decide) (by decide) (by decide)) fun t₈ ⟨v8, o8, k8⟩ => ?_)
  have h₈ := h₇.congrO o8 (by da_omega) k8 (by simp)
  refine WP.mono (copyA_ok h₈ (o := 6) (a := 12) (by decide) (by decide) (by decide)) fun t ⟨v9, o9, k9⟩ => ?_
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → DaP w y) →
      FrmP B (DaP w) m m' := fun ho hP => FrmP.of_out ho hP
  have hNw : N < 2 ^ (64 * w) := hN ▸ wv_lt _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [o9.wv (by da_omega) (by da_omega), v8, o7.wv (by da_omega) (by da_omega), o6.wv (by da_omega) (by da_omega), q5]
  · rw [v9, o8.wv (by da_omega) (by da_omega), o7.wv (by da_omega) (by da_omega), o6.wv (by da_omega) (by da_omega),
      wv_low_of_lt (v := w) (w := w + 1) (by omega_arith) (by rw [r5]; exact Nat.lt_trans (Nat.mod_lt _ hN0) hNw), r5]
  · unfold mw
    rw [o9.word (by da_omega) (by da_omega), o8.word (by da_omega) (by da_omega), m7, word_writeW_self]
  · exact (((((((((fr o1 fun y => by da_omega).trans (fr o2 fun y => by da_omega)).trans (fr o3 fun y => by da_omega)).trans
      (fr o4 fun y => by da_omega)).trans (f5'.mono fun y => by da_omega)).trans (fr o6 fun y => by da_omega)).trans
      (fr o7 fun y => by da_omega)).trans (fr o8 fun y => by da_omega)).trans (fr o9 fun y => by da_omega))
  · exact ((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9).mono
      (by simp [stepRegs])

/-! ## `m + 1`, `n - r`, `b` (narrow) -/

/-- What `divB` changes: arrays 4 to 9, and the mask. -/
def DbP (w y : Nat) : Prop := (slot w 4 ≤ y ∧ y < slot w 10) ∨ (176 ≤ y ∧ y < 184)

macro "db_omega" : tactic =>
  `(tactic| (simp only [DbP, DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask, sFn, ar]; omega_arith))

/-- `divB` (narrow): `m₁ = (m mod 2^(64 w) + 1) mod 2^(64 w)` and `d = n - r`
(modulo `2^(64 w)`), from the low words of `m` (array 14) and `r` (array
12); the quotient `q` and remainder of `d` by `m₁` where `m₁ > 0`; the mask
and'ed with whether the remainder is zero; `b = (q + 1) mod 2^(64 w)` in
wide array 4 (narrow 8 and 9). -/
theorem divB_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {N Ml Rl : Nat} {c : Bool}
    (hN : wv s.mem B (slot w 0) w = N) (hone : wv s.mem B (slot w 2) w = 1) (hz : wv s.mem B (slot w 3) w = 0)
    (hM : wv s.mem B (slot w 14) w = Ml) (hR : wv s.mem B (slot w 12) w = Rl) (hm : mw s.mem B = mask c) :
    WP isa (seqs divB) s fun t => ∃ q rem : Nat,
      (0 < (Ml + 1) % 2 ^ (64 * w) → q = wsub (64 * w) N Rl / ((Ml + 1) % 2 ^ (64 * w)) ∧
        rem = wsub (64 * w) N Rl % ((Ml + 1) % 2 ^ (64 * w))) ∧
      wv t.mem B (slot w 8) (2 * (w + 2)) = (q + 1) % 2 ^ (64 * w) ∧
      mw t.mem B = mask (c && decide (rem = 0)) ∧
      FrmP B (DbP w) s.mem t.mem ∧ Keep [.r12, .r9, .r8, .rax, .r14, .r15, .rbp, .r10, .rbx, .rsi, .r11, .r13, .rdx]
        s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have hNw : N < 2 ^ (64 * w) := hN ▸ wv_lt _ _ _ _
  simp only [divB, List.cons_append, List.nil_append, seqs]
  -- `m₁`.
  refine WP.seq (WP.mono (zeroA_ok h (j := 4) (by decide)) fun t₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (by db_omega) k1 (by simp)
  refine WP.seq (WP.mono (addA_ok h₁ (o := 4) (a := 14) (b := 2) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₂ ⟨v2, o2, k2⟩ => ?_)
  rw [o1.wv (by db_omega) (by db_omega), o1.wv (by db_omega) (by db_omega), hM, hone] at v2
  have h₂ := h₁.congrO o2 (by db_omega) k2 (by simp)
  -- `d`.
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := 5) (by decide)) fun t₃ ⟨z3, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by db_omega) k3 (by simp)
  refine WP.seq (WP.mono (subA_ok h₃ (t := 5) (a := 0) (b := 12) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₄ ⟨_, e4, o4, k4⟩ => ?_)
  have N₃ : wv t₃.mem B (slot w 0) w = N := by
    rw [o3.wv (by db_omega) (by db_omega), o2.wv (by db_omega) (by db_omega), o1.wv (by db_omega) (by db_omega), hN]
  have R₃ : wv t₃.mem B (slot w 12) w = Rl := by
    rw [o3.wv (by db_omega) (by db_omega), o2.wv (by db_omega) (by db_omega), o1.wv (by db_omega) (by db_omega), hR]
  rw [N₃, R₃] at e4
  have D₄ := wsub_of_eq e4 (wv_lt _ _ _ _) hNw (hR ▸ wv_lt _ _ _ _)
  have h₄ := h₃.congrO o4 (by db_omega) k4 (by simp)
  have M1₄ : wv t₄.mem B (slot w 4) w = (Ml + 1) % 2 ^ (64 * w) := by
    rw [o4.wv (by db_omega) (by db_omega), o3.wv (by db_omega) (by db_omega), v2]
  -- `q` and the remainder.
  refine WP.seq (WP.mono (divmod_ok h₄.scr h₄.rdi h₄.hw h₄.hS (by omega_arith) hw2 hZ (iQ := 5) (iR := 6) (iD := 4)
    (iT := 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t₅ ⟨_, f5, k5, hq5⟩ => ?_)
  rw [M1₄, D₄] at hq5
  have f5' : FrmP B (fun y => slot w 5 ≤ y ∧ y < slot w 8) t₄.mem t₅.mem := FrmP.of_frm f5 fun r hr y h1 h2 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [Bignum.slot, hdrBytes] at h1 h2 ⊢ <;> omega_arith
  have h₅ := h₄.congrP f5' (fun y => by db_omega) k5 (by decide)
  -- Whether the remainder is zero.
  have hz₅ : wv t₅.mem B (slot w 3) w = 0 := by
    rw [f5'.wv_eq (fun y => by db_omega) (by db_omega), o4.wv (by db_omega) (by db_omega),
      o3.wv (by db_omega) (by db_omega), o2.wv (by db_omega) (by db_omega), o1.wv (by db_omega) (by db_omega), hz]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h₅ (a := 6) (b := 3) (by decide) (by decide))
    fun t₆ ⟨hz6, m6, k6⟩ => ?_)
  rw [hz₅] at hz6
  have h₆ := h₅.congrP (FrmP.of_eq (P := fun _ => False) m6) (fun y hy => hy.elim) k6 (by simp)
  have hm₆ : mw t₆.mem B = mask c := by
    unfold mw at hm ⊢
    rw [m6, f5'.word_eq (fun y => by db_omega) (by db_omega), o4.word (by db_omega) (by db_omega),
      o3.word (by db_omega) (by db_omega), o2.word (by db_omega) (by db_omega), o1.word (by db_omega) (by db_omega), hm]
  simp only [seqs]
  refine WP.seq (WP.mono (andZero_ok h₆ hm₆ hz6) fun t₇ ⟨m7, k7⟩ => ?_)
  have h₇ := h₆.congrW m7 (by db_omega) (by decide) k7 (by simp)
  have o7 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₆.mem t₇.mem := by
    rw [m7]; exact writeW_outside _ _ _ (by db_omega)
  -- `b = q + 1`.
  refine WP.seq (WP.mono (zeroA_ok h₇ (j := 8) (by decide)) fun t₈ ⟨z8, o8, k8⟩ => ?_)
  have h₈ := h₇.congrO o8 (by db_omega) k8 (by simp)
  refine WP.seq (WP.mono (addA_ok h₈ (o := 8) (a := 5) (b := 2) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₉ ⟨v9, o9, k9⟩ => ?_)
  have h₉ := h₈.congrO o9 (by db_omega) k9 (by simp)
  refine WP.mono (zeroA_ok h₉ (j := 9) (by decide)) fun t ⟨z10, o10, k10⟩ => ?_
  have one₈ : wv t₈.mem B (slot w 2) w = 1 := by
    rw [o8.wv (by db_omega) (by db_omega), o7.wv (by db_omega) (by db_omega), m6, f5'.wv_eq (fun y => by db_omega)
      (by db_omega), o4.wv (by db_omega) (by db_omega), o3.wv (by db_omega) (by db_omega),
      o2.wv (by db_omega) (by db_omega), o1.wv (by db_omega) (by db_omega), hone]
  rw [one₈, o8.wv (by db_omega) (by db_omega), o7.wv (by db_omega) (by db_omega), m6] at v9
  refine ⟨wv t₅.mem B (slot w 5) w, wv t₅.mem B (slot w 6) w, fun hpos => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r5, q5⟩ := hq5 hpos
    refine ⟨q5, ?_⟩
    have l1 := Nat.mod_lt (wsub (64 * w) N Rl) hpos
    have l2 := Nat.mod_lt (Ml + 1) (Nat.two_pow_pos (64 * w))
    have l3 : wv t₅.mem B (slot w 6) (w + 1) < 2 ^ (64 * w) := by rw [r5]; omega_arith
    rw [wv_low_of_lt (v := w) (w := w + 1) (by omega_arith) l3, r5]
  · -- `b`'s top words are zero.
    have zt : wv t.mem B (slot w 8 + 8 * w) (w + 4) = 0 := by
      rw [show w + 4 = 2 + (w + 2) by omega_arith, wv_add,
        show slot w 8 + 8 * w + 8 * 2 = slot w 9 by simp only [Bignum.slot, hdrBytes]; omega_arith, z10,
        o10.wv (by db_omega) (by db_omega), o9.wv (by db_omega) (by db_omega)]
      rw [wv_zero_sub (a := w) (k := 2) z8 (by omega_arith)]
    rw [show 2 * (w + 2) = w + (w + 4) by omega_arith, wv_top_zero zt, o10.wv (by db_omega) (by db_omega), v9,
      Nat.add_comm]
  · unfold mw
    rw [o10.word (by db_omega) (by db_omega), o9.word (by db_omega) (by db_omega), o8.word (by db_omega) (by db_omega),
      m7, word_writeW_self]
  · have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → DbP w y) →
        FrmP B (DbP w) m m' := fun ho hP => FrmP.of_out ho hP
    exact ((((((((((fr o1 fun y => by db_omega).trans (fr o2 fun y => by db_omega)).trans (fr o3 fun y => by db_omega)).trans
      (fr o4 fun y => by db_omega)).trans (f5'.mono fun y => by db_omega)).trans (FrmP.of_eq m6)).trans
      (fr o7 fun y => by db_omega)).trans (fr o8 fun y => by db_omega)).trans (fr o9 fun y => by db_omega)).trans
      (fr o10 fun y => by db_omega))
  · exact (((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9).trans k10).mono
      (by simp [stepRegs])

/-! ## `b² - 4 n` (wide) -/

/-- What `minus4n` changes: wide arrays 0 and 7 to 15, and the mask. -/
def MnP (w y : Nat) : Prop := (slot w 0 ≤ y ∧ y < slot w 1) ∨ (slot w 7 ≤ y ∧ y < slot w 16) ∨ (176 ≤ y ∧ y < 184)

macro "mn_omega" : tactic =>
  `(tactic| (simp only [MnP, DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask,
    Impl.Bignum.X86_64.Public.sElen, sFn, ar]; omega_arith))

/-- `minus4n` (wide, `w = 2 v + 2`): `b²` (`b` in wide array 4, below
`2^(64 v)`), `4 n` (`n` in wide array 0, doubled twice in place), `X = b² - 4 n`
into wide array 7, and the mask and'ed with `b² > 4 n` as `ok4Of` says. -/
theorem minus4n_ok {s : State} {B : Addr} {Z w v : Nat} (h : Ws s B Z w) (hwv : w = 2 * v + 2) (hv1 : 1 ≤ v)
    {N b : Nat} {c : Bool} (hN : wv s.mem B (slot w 0) w = N) (hone : wv s.mem B (slot w 1) w = 1)
    (hb : wv s.mem B (slot w 4) w = b) (hbv : b < 2 ^ (64 * v))
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * w - 8))
    (hm : mw s.mem B = mask c) :
    WP isa (seqs minus4n) s fun t =>
      wv t.mem B (slot w 7) w = xOf (64 * v) (64 * w) N b ∧ mw t.mem B = mask (c && ok4Of (64 * v) (64 * w) N b) ∧
      FrmP B (MnP w) s.mem t.mem ∧ Keep [.r12, .r9, .rax, .rsi, .rbx, .r14, .r8, .r10, .r15, .r11, .r13, .rdx,
        .rbp, .rcx] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have hw4 : (4 * w - 8 + 7) / 8 = v := by omega_arith
  have hbw : b < 2 ^ (64 * w) := hb ▸ wv_lt _ _ _ _
  have hNw : N < 2 ^ (64 * w) := hN ▸ wv_lt _ _ _ _
  simp only [minus4n, List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.mono (copyA_ok h (o := 8) (a := 4) (by decide) (by decide) (by decide)) fun t₁ ⟨v1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (by mn_omega) k1 (by simp)
  refine WP.seq (WP.mono (copyA_ok h₁ (o := 9) (a := 4) (by decide) (by decide) (by decide)) fun t₂ ⟨v2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by mn_omega) k2 (by simp)
  have E₂ : wv t₂.mem B (slot w 8) w = b := by rw [o2.wv (by mn_omega) (by mn_omega), v1, hb]
  have D₂ : wv t₂.mem B (slot w 9) w = b := by rw [v2, o1.wv (by mn_omega) (by mn_omega), hb]
  have el₂ : word t₂.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * w - 8) := by
    rw [o2.word (by mn_omega) (by mn_omega), o1.word (by mn_omega) (by mn_omega), hel]
  -- `b²`.
  refine wp_seqs_append (by simp [Recover.prod]) (by simp) (WP.mono (prod_ok h₂ el₂ (by omega_arith) (by omega_arith)
    (by rw [hw4]; show wv t₂.mem B (slot w 8) w < _; rw [E₂]; exact hbv)) fun t₃ ⟨v3, o3, k3⟩ => ?_)
  simp only [Recover.aE, Recover.aD, Recover.aM] at v3 o3
  rw [E₂, D₂] at v3
  have h₃ := h₂.congrO o3 (by mn_omega) k3 (by simp)
  have S₃ : wv t₃.mem B (slot w 10) w = b * b % 2 ^ (64 * w) := by
    rw [← v3, show 2 * (w + 2) = w + (w + 4) by omega_arith]; exact wv_low_mod
  -- `4 n`.
  simp only [seqs]
  refine WP.seq (WP.mono (shlA_ok h₃ false (j := 0) (c₀ := false) (by decide) (shlPre_mask h₃ maskZero))
    fun t₄ ⟨_, _, e4, o4, k4⟩ => ?_)
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at e4 o4
  have h₄ := h₃.congrO o4 (by mn_omega) k4 (by simp)
  refine WP.seq (WP.mono (shlA_ok h₄ false (j := 0) (c₀ := false) (by decide) (shlPre_mask h₄ maskZero))
    fun t₅ ⟨_, _, e5, o5, k5⟩ => ?_)
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at e5 o5
  have h₅ := h₄.congrO o5 (by mn_omega) k5 (by simp)
  have N₃ : wv t₃.mem B (slot w 0) w = N := by
    rw [o3.wv (by mn_omega) (by mn_omega), o2.wv (by mn_omega) (by mn_omega), o1.wv (by mn_omega) (by mn_omega), hN]
  have F₅ : wv t₅.mem B (slot w 0) w = fourN (64 * w) N := by
    rw [N₃] at e4
    obtain ⟨v4', _⟩ := dbl_val e4 (wv_lt _ _ _ _)
    obtain ⟨v5', _⟩ := dbl_val e5 (wv_lt _ _ _ _)
    rw [v5', v4']
    simp only [Bool.toNat_false, Nat.add_zero, fourN]
  have S₅ : wv t₅.mem B (slot w 10) w = sqOf (64 * v) (64 * w) b := by
    rw [o5.wv (by mn_omega) (by mn_omega), o4.wv (by mn_omega) (by mn_omega), S₃]
    unfold sqOf
    rw [prod_iter _ _ _ hbw]
    simp only
    rw [Nat.mod_eq_of_lt hbv]
  -- `X = b² - 4 n` and the checks.
  refine WP.seq (WP.mono (subA_ok h₅ (t := 12) (a := 10) (b := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₆ ⟨hb6, e6, o6, k6⟩ => ?_)
  rw [S₅, F₅] at hb6 e6
  have h₆ := h₅.congrO o6 (by mn_omega) k6 (by simp)
  have hm₆ : mw t₆.mem B = mask c := by
    unfold mw at hm ⊢
    rw [o6.word (by mn_omega) (by mn_omega), o5.word (by mn_omega) (by mn_omega), o4.word (by mn_omega) (by mn_omega),
      o3.word (by mn_omega) (by mn_omega), o2.word (by mn_omega) (by mn_omega), o1.word (by mn_omega) (by mn_omega), hm]
  refine WP.seq (WP.mono (andB_ok h₆ hm₆ hb6) fun t₇ ⟨m7, k7⟩ => ?_)
  have h₇ := h₆.congrW m7 (by mn_omega) (by decide) k7 (by simp)
  have o7 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₆.mem t₇.mem := by
    rw [m7]; exact writeW_outside _ _ _ (by mn_omega)
  have X₇ : wv t₇.mem B (slot w 12) w = xOf (64 * v) (64 * w) N b := by
    rw [o7.wv (by mn_omega) (by mn_omega)]
    exact wsub_of_eq e6 (wv_lt _ _ _ _) (S₅ ▸ wv_lt _ _ _ _) (F₅ ▸ wv_lt _ _ _ _)
  have one₇ : wv t₇.mem B (slot w 1) w = 1 := by
    rw [o7.wv (by mn_omega) (by mn_omega), o6.wv (by mn_omega) (by mn_omega), o5.wv (by mn_omega) (by mn_omega),
      o4.wv (by mn_omega) (by mn_omega), o3.wv (by mn_omega) (by mn_omega), o2.wv (by mn_omega) (by mn_omega),
      o1.wv (by mn_omega) (by mn_omega), hone]
  refine WP.seq (WP.mono (subA_ok h₇ (t := 13) (a := 12) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₈ ⟨hb8, _, o8, k8⟩ => ?_)
  rw [X₇, one₇] at hb8
  have h₈ := h₇.congrO o8 (by mn_omega) k8 (by simp)
  have hm₈ : mw t₈.mem B = mask (c && !decide (sqOf (64 * v) (64 * w) b < fourN (64 * w) N)) := by
    unfold mw
    rw [o8.word (by mn_omega) (by mn_omega), m7, word_writeW_self]
  refine WP.seq (WP.mono (andB_ok h₈ hm₈ hb8) fun t₉ ⟨m9, k9⟩ => ?_)
  have h₉ := h₈.congrW m9 (by mn_omega) (by decide) k9 (by simp)
  have o9 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₈.mem t₉.mem := by
    rw [m9]; exact writeW_outside _ _ _ (by mn_omega)
  refine WP.mono (copyA_ok h₉ (o := 7) (a := 12) (by decide) (by decide) (by decide)) fun t ⟨v10, o10, k10⟩ => ?_
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → MnP w y) →
      FrmP B (MnP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [v10, o9.wv (by mn_omega) (by mn_omega), o8.wv (by mn_omega) (by mn_omega), X₇]
  · unfold mw
    rw [o10.word (by mn_omega) (by mn_omega), m9, word_writeW_self, ok4Of, Bool.not_or, Bool.and_assoc]
  · exact (((((((((fr o1 fun y => by mn_omega).trans (fr o2 fun y => by mn_omega)).trans (fr o3 fun y => by mn_omega)).trans
      (fr o4 fun y => by mn_omega)).trans (fr o5 fun y => by mn_omega)).trans (fr o6 fun y => by mn_omega)).trans
      (fr o7 fun y => by mn_omega)).trans (fr o8 fun y => by mn_omega)).trans (fr o9 fun y => by mn_omega)).trans
      (fr o10 fun y => by mn_omega)
  · exact (((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9).trans k10).mono
      (by simp)

end VG.Proof.Rsa.X86_64.Rd
