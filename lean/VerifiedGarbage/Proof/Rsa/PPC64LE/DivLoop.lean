module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.Div
public import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The division of the RSA key operations on PPC64LE

`step_ok`: a step of `div q r d t` is `Proof/Rsa/KeyMath.lean`'s `divStep`
of the divisor `D = [d]` (its `w + 1` digits) and `K = 32 w`, on the
quotient `[q]` and the remainder `[r]` (its `w + 1` digits), when `D > 0`;
for `D = 0` it runs all the same. `div_ok`: the `32 w` steps from `(0, N)`,
the quotient `N / D` and the remainder `N mod D`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Proof.Rsa (divStep divIter divIter_inv divIter_done borrow_iff)
open VG.Impl.Rsa.PPC64LE.Div (div init step)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj ranges)

/-- The `w + 1` digits of an array outside the frame. -/
theorem keep_num1 {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ 160) (fit : arr w j + S w ≤ 2 ^ 64) : num1 m' B w j = num1 m B w j := by
  refine Outs.val32 h (fun r hr => ?_) (by simp only [S] at fit; omega_arith)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj k hk); dsimp only; simp only [S] at *; omega_arith
  · have := hd d hd'; have : 160 ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega_arith

/-- The registers a step changes. -/
abbrev stepRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The numbers of a step: from the shift's equations and the subtraction's,
the step is `divStep`. -/
theorem step_arith {D R Q Q1 R1 T c c' β P1 P2 H : Nat} (hD : 0 < D) (hR : R < D)
    (hDP : D < P1) (hP1 : P1 = 2 * H) (hP2 : P2 = 4294967296 * P1) (hQ1 : Q1 < P1) (hT : T < P2)
    (hc : c ≤ 1) (hβ : β ≤ 1) (e1 : Q1 + P1 * c = 2 * Q) (e2 : R1 + P2 * c' = 2 * R + c)
    (e3 : T + D = R1 + P2 * β) :
    R1 = 2 * R + Q / H ∧ Q1 = 2 * Q % P1 ∧ (β = 0 ↔ D ≤ R1) ∧ (β = 0 → T = R1 - D) := by
  have hH : 0 < H := by omega_arith
  have hc' : c' = 0 := by
    rcases Nat.eq_zero_or_pos c' with z | z
    · exact z
    · have : P2 ≤ P2 * c' := Nat.le_mul_of_pos_right _ z
      omega_arith
  subst hc'
  have hcQ : c = Q / H := by
    have : 2 * Q / P1 = c := by
      rw [← e1, Nat.add_mul_div_left _ _ (by omega_arith), Nat.div_eq_of_lt hQ1, Nat.zero_add]
    rw [← this, hP1, Nat.mul_div_mul_left _ _ (by decide)]
  have hmod : Q1 = 2 * Q % P1 := by
    rw [← e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQ1]
  have hb := borrow_iff e3 hT hβ
  refine ⟨by omega_arith, hmod, hb, fun h0 => ?_⟩
  rw [h0, Nat.mul_zero, Nat.add_zero] at e3
  omega_arith

/-- A step of the division. -/
theorem step_ok {s : State} {B : Addr} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    {D N₀ k : Nat} (hk : k < 32 * w) (hN₀ : N₀ < 2 ^ (32 * w)) (hD : num1 s.mem B w d = D)
    (hDw : D < 2 ^ (32 * w))
    (vals : 0 < D → num s.mem B w q = (divIter D (32 * w) k (0, N₀)).2 ∧
      num1 s.mem B w r = (divIter D (32 * w) k (0, N₀)).1) :
    WP isa (step q r d t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [q, r, t] [] s.mem u.mem ∧
      u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1 ∧ Keep stepRegs s u ∧
      (0 < D → num u.mem B w q = (divIter D (32 * w) (k + 1) (0, N₀)).2 ∧
        num1 u.mem B w r = (divIter D (32 * w) (k + 1) (0, N₀)).1) := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have ft := h.arr_fit ht
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  rw [step, WP.seq_iff]
  refine WP.mono (shift_ok h hq hr hN hqr) fun s1 ⟨h1, km1, ⟨c, hc, eq1, c', hc', er1⟩, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (subtract_ok h1 hr hd ht hN (Ne.symm hrt) (Ne.symm hdt))
    fun s2 ⟨h2, km2, eT, hβ, k2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (bit_ok hβ) fun s3 ⟨⟨r10, r9, m3⟩, k3⟩ => ?_
  have h3 : Ws s3 B Z w N := h2.of_keep k3
  rw [WP.seq_iff]
  refine WP.mono (keep_ok h3 hr ht hN hrt (b := decide ((s2.gpr .r9).toNat = 0))
    (by rw [r9]; by_cases z : (s2.gpr .r9).toNat = 0 <;> simp [z])) fun s4 ⟨h4, km4, eR, k4⟩ => ?_
  have e10 : s4.gpr .r10 = s3.gpr .r10 := k4.gpr _ (by decide)
  -- The quotient after the shift, through the subtraction and the selection.
  have q2 : num s2.mem B w q = num s1.mem B w q :=
    KeyWorkspace.Keep.num km2 (by simp; omega_arith) (by simp) (by omega_arith)
  have q4 : num s4.mem B w q = num s1.mem B w q := by
    rw [KeyWorkspace.Keep.num km4 (by simp; omega_arith) (by simp) (by omega_arith), m3, q2]
  have even : num s4.mem B w q % 2 = 0 := by
    rw [q4]
    have : 2 ∣ 2 ^ (32 * w) * c :=
      Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero (Nat.pow_mod 2 (32 * w) 2 ▸ by
        rw [Nat.mod_self, Nat.zero_pow (by omega_arith)])) _
    omega_arith
  refine WP.mono (setBit_ok h4 hq hN even (by rw [e10, r10]; split <;> decide))
    fun u ⟨hu, km5, eQ, u4, k5⟩ => ?_
  have kr : Keep stepRegs s u := ((((k1.trans k2).trans k3).trans k4).trans k5).mono
  have k12 : KeyWorkspace.Keep B w [q, r, t] [] s.mem s2.mem := KeyWorkspace.Keep.join km1 km2
  have k45 : KeyWorkspace.Keep B w [q, r, t] [] s2.mem u.mem := by
    rw [← m3]; exact KeyWorkspace.Keep.join km4 km5
  refine ⟨hu, k12.trans k45, ?_, kr, fun hD0 => ?_⟩
  · rw [u4, k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]
  · obtain ⟨vq, vr⟩ := vals hD0
    obtain ⟨_, hR, -, -, -⟩ := divIter_inv hD0 hN₀ k (by omega_arith)
    have es : divIter D (32 * w) (k + 1) (0, N₀) = divStep D (32 * w) (divIter D (32 * w) k (0, N₀)) := rfl
    -- The divisor and the shifted remainder, through the writes.
    have d1 : num1 s1.mem B w d = D := by
      rw [keep_num1 km1 (by simp; omega_arith) (by simp) (by omega_arith), hD]
    have d2 : num1 s2.mem B w d = D := by
      rw [keep_num1 km2 (by simp; omega_arith) (by simp) (by omega_arith), d1]
    have r2 : num1 s2.mem B w r = num1 s1.mem B w r := keep_num1 km2 (by simp; omega_arith) (by simp) (by omega_arith)
    have t3 : num1 s3.mem B w t = num1 s2.mem B w t := by rw [m3]
    have ur : num1 u.mem B w r = num1 s4.mem B w r := keep_num1 km5 (by simp; omega_arith) (by simp) (by omega_arith)
    have hP2 : 2 ^ (32 * (w + 1)) = 4294967296 * 2 ^ (32 * w) := by
      rw [show 32 * (w + 1) = 32 + 32 * w by omega_arith, Nat.pow_add]
    have hP1 : 2 ^ (32 * w) = 2 * 2 ^ (32 * w - 1) := by
      obtain ⟨j, hj⟩ : ∃ j, 32 * w = j + 1 := ⟨32 * w - 1, by omega_arith⟩
      rw [hj, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
    have hQ1 : num s1.mem B w q < 2 ^ (32 * w) := val32_lt _ _ _ _
    have hT : num1 s2.mem B w t < 2 ^ (32 * (w + 1)) := val32_lt _ _ _ _
    rw [d1] at eT
    have hR' : num1 s.mem B w r < D := by rw [vr]; exact hR
    obtain ⟨eR1, eQ1, hb, hTv⟩ := step_arith hD0 hR' hDw hP1 hP2 hQ1 hT hc hβ eq1 er1 eT
    have ep : divIter D (32 * w) k (0, N₀) = (num1 s.mem B w r, num s.mem B w q) :=
      Prod.ext vr.symm vq.symm
    rw [es, ep]
    simp only [divStep]
    rw [ur, eR, t3, m3, r2, eQ, e10, r10, q4, ← eR1, ← eQ1]
    by_cases hl : num1 s1.mem B w r < D
    · have hβ1 : (s2.gpr .r9).toNat ≠ 0 := fun z => absurd (hb.mp z) (by omega_arith)
      simp only [hl, hβ1, ↓reduceIte, decide_false]
      exact ⟨by simp, rfl⟩
    · have hβ0 : (s2.gpr .r9).toNat = 0 := hb.mpr (by omega_arith)
      simp only [hl, hβ0, ↓reduceIte, decide_true]
      exact ⟨by simp, hTv hβ0⟩

/-- `init r`: the remainder's `w + 1` digits := 0, and `32 w` steps to count in `r4`. -/
theorem init_ok {s : State} {B : Addr} {Z w N r : Nat} (h : Ws s B Z w N) (hr : r < N)
    (hN : N ≤ 256) :
    WP isa (init r) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [r] [] s.mem u.mem ∧
      num1 u.mem B w r = 0 ∧ u.gpr .r4 = BitVec.ofNat 64 (32 * w) ∧ Keep [.r0, .r4, .r5, .r8] s u := by
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [init, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega_arith) ?_
  have hb : WP isa (.block [.addi .r8 .r29 1, .li .r0 0]) (s.write .r5 (off B (arr w r))) fun u =>
      (u.gpr .r5 = off B (arr w r) ∧ u.gpr .r8 = BitVec.ofNat 64 (w + 1) ∧ u.gpr .r0 = 0 ∧
        u.mem = s.mem) ∧ Keep [.r0, .r8] (s.write .r5 (off B (arr w r))) u := by
    refine WP.keep _ ?_ (by decide)
    prun [h.r29, BitVec.ofNat_add]
    rfl
  refine WP.mono hb fun u ⟨⟨u5, u8, u0, mu⟩, ku⟩ => ?_
  have k₁ : Keep [.r0, .r4, .r5, .r8] s u := ((Keep.write _ _ _).trans ku).mono
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [WP.seq_iff]
  refine WP.mono (zeroLoop_ok hu.scr u5 u8 u0 (by omega_arith) (by omega_arith) (by omega_arith)) fun v ⟨z, out, kv⟩ => ?_
  have hv : Ws v B Z w N := hu.of_keep kv
  have hl : WP isa (.block [.lsl .r4 .r29 5]) v fun x =>
      (x.gpr .r4 = BitVec.ofNat 64 (32 * w) ∧ x.mem = v.mem) ∧ Keep [.r4] v x := by
    refine WP.keep _ ?_ (by decide)
    have e : BitVec.ofNat 64 w <<< 5 = BitVec.ofNat 64 (32 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_arith
    prun [hv.r29, e]
  refine WP.mono hl fun x ⟨⟨x4, xm⟩, kx⟩ => ⟨hv.of_keep kx, ?_, ?_, x4, (k₁.trans (kv.trans kx)).mono⟩
  · rw [xm, ← mu]
    exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa using out) (by omega_arith) (by simp)
  · rw [xm]
    exact Proof.Bignum.PPC64LE.val32_zero fun j hj => z j hj

/-- `div q r d t`: `[q] := [q] / [d]` and the `w + 1` digits of `[r]` := `[q] mod [d]`,
for a divisor whose extra digit is 0, when it is not 0. -/
theorem div_ok {s : State} {B : Addr} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hdz : w32 s.mem B (arr w d + 4 * w) = 0) :
    WP isa (div q r d t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [q, r, t] [] s.mem u.mem ∧
      Keep stepRegs s u ∧
      (0 < num s.mem B w d → num u.mem B w q = num s.mem B w q / num s.mem B w d ∧
        num1 u.mem B w r = num s.mem B w q % num s.mem B w d) := by
  have fd := h.arr_fit hd
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  -- The divisor's `w + 1` digits are its number.
  have hD : num1 s.mem B w d = num s.mem B w d := by
    have e := val32_append s.mem B (arr w d) w 1
    have e1 : val32 s.mem B (arr w d + 4 * w) 1 = 0 := by
      simp only [val32, hdz, Nat.mul_zero, Nat.add_zero]
    change val32 _ _ _ (w + 1) = val32 _ _ _ w
    rw [e, e1, Nat.mul_zero, Nat.add_zero]
  have hDw : num s.mem B w d < 2 ^ (32 * w) := val32_lt _ _ _ _
  have hN₀ : num s.mem B w q < 2 ^ (32 * w) := val32_lt _ _ _ _
  rw [div, WP.seq_iff]
  refine WP.mono (init_ok h hr hN) fun u ⟨hu, km, z, u4, ku⟩ => ?_
  let D := num s.mem B w d
  let N₀ := num s.mem B w q
  let Inv : Nat → State → Prop := fun i x =>
    Ws x B Z w N ∧ KeyWorkspace.Keep B w [q, r, t] [] s.mem x.mem ∧ Keep stepRegs s x ∧
      (0 < D → num x.mem B w q = (divIter D (32 * w) i (0, N₀)).2 ∧
        num1 x.mem B w r = (divIter D (32 * w) i (0, N₀)).1)
  have i0 : Inv 0 u := ⟨hu, km.mono, ku.mono, fun _ => ⟨KeyWorkspace.Keep.num km (by simp; omega_arith)
    (by simp) (by have := h.fit64 hq; omega_arith), z⟩⟩
  refine WP.mono (VG.Proof.Bignum.PPC64LE.wp_countdown (body := step q r d t) (cnt := .r4) (N := 32 * w)
    (by omega_arith) (by omega_arith) Inv (fun i hi x ⟨hx, kx, rx, vx⟩ _ => ?_) i0 u4) fun x ⟨hx, kx, rx, vx⟩ => ?_
  · have dx : num1 x.mem B w d = D := by
      rw [keep_num1 kx (by simp; omega_arith) (by simp) (by omega_arith), hD]
    refine WP.mono (step_ok hx hq hr hd ht hN hqr hqd hqt hrd hrt hdt hi hN₀ dx hDw vx)
      fun y ⟨hy, ky, y4, ry, vy⟩ => ⟨⟨hy, kx.trans ky, rx.trans' ry, vy⟩, y4⟩
  · refine ⟨hx, kx, rx, fun hD0 => ?_⟩
    obtain ⟨e1, e2⟩ := vx hD0
    rw [divIter_done hD0 hN₀] at e1 e2
    exact ⟨e1, e2⟩

end VG.Proof.Rsa.PPC64LE.Keys
