module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSSetup
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.PPC64LE.DivN
public import VerifiedGarbage.Proof.Rsa.PPC64LE.DivLoop
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Rsa.PPC64LE.Shifts
import VerifiedGarbage.Proof.Rsa.PPC64LE.EvenW
import VerifiedGarbage.Proof.Rsa.PPC64LE.WordLoops
import VerifiedGarbage.Proof.Rsa.PPC64LE.Loops
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry

/-! # DSA parameter generation on PPC64LE: the division in the key working space

`DivN.div_ok`: `Impl/Dsa/PPC64LE/DivN.lean`'s `div q r d t v` leaves
`[q] / [d]` in `[q]` and `[q] mod [d]` in `[r]`, for `0 < [d] < 2^(32 v)` and
`v + 1 < w`. Its steps are `Proof/Rsa/KeyMath.lean`'s `divStep` of `D = [d]`
and `K = 32 w`, as those of `Impl/Rsa/PPC64LE/Div.lean`'s division
(`Proof/Rsa/PPC64LE/DivLoop.lean`), with the remainder over `v + 1` digits
(`numV`) instead of `w + 1`.

`div_vp`: that division in the key working space, the temporary `t` lost.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.DivN

open VG VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.PPC64LE hiding Keep WP.keep
open VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa (divStep divIter divIter_inv divIter_done borrow_iff)
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop subBody selBody)
open VG.Impl.Rsa.PPC64LE.Div (shlBody shlWBody init)
open VG.Impl.Dsa.PPC64LE.DivN (shiftQ shiftR shift subtract keep step zeroHi div)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj ranges)

/-- The `v + 1` digits of array `j`. -/
abbrev numV (m : Mem) (B : Addr) (w v j : Nat) : Nat := val32 m B (arr w j) (v + 1)

/-- The low `k` digits of a number below `2^(32 k)`. -/
theorem val32_low {m : Mem} {B : Addr} {d k n : Nat} (hk : k ≤ n) (h : val32 m B d n < 2 ^ (32 * k)) :
    val32 m B d k = val32 m B d n := by
  have e := val32_append m B d k (n - k)
  rw [Nat.add_sub_cancel' hk] at e
  rw [e] at h ⊢
  have : val32 m B (d + 4 * k) (n - k) = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * k) (n - k)) with z | z
    · exact z
    · have := Nat.mul_le_mul_left (2 ^ (32 * k)) z; omega_arith
  rw [this, Nat.mul_zero, Nat.add_zero]

/-- Two distinct arrays, over `v + 1 ≤ w + 1` digits, are each ahead of the other. -/
theorem aheadV {w v o a : Nat} (hv : v ≤ w) (h : o ≠ a) : Ahead (arr w o) (arr w a) (v + 1) := by
  have := arr_disj (w := w) h
  simp only [S] at this
  unfold Ahead; omega_arith

/-- The `v + 1` digits of an array outside the frame. -/
theorem keep_numV {B : Addr} {w v : Nat} {js ds : List Nat} {m m' : Mem}
    (h : VG.Proof.Rsa.KeyWorkspace.Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ 160) (hv : v ≤ w) (fit : arr w j + S w ≤ 2 ^ 64) :
    numV m' B w v j = numV m B w v j := by
  refine Outs.val32 h (fun r hr => ?_) (by simp only [S] at fit; omega_arith)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj k hk); dsimp only; simp only [S] at *; omega_arith
  · have := hd d hd'; have : 160 ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega_arith

/-- `shiftQ q`: `[q]' + 2^(32 w) c = 2 [q]`, the carry `c` in `r9`. -/
theorem shiftQ_ok {s : State} {B : Addr} {Z w N q : Nat} (h : Ws s B Z w N) (hq : q < N) (hN : N ≤ 256) :
    WP isa (shiftQ q) s fun v => Ws v B Z w N ∧ Keep opRegs s v ∧ (v.gpr .r9).toNat ≤ 1 ∧
      Outside B (arr w q) (4 * w) s.mem v.mem ∧
      num v.mem B w q + 2 ^ (32 * w) * (v.gpr .r9).toNat = 2 * num s.mem B w q := by
  have fq := h.arr_fit hq
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  rw [shiftQ, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show q < 2 ^ 15 by omega_arith) ?_
  have k₀ : Keep opRegs s (s.write .r5 (off B (arr w q))) := (Keep.write _ _ _).mono
  refine WP.mono (WP.keep [.r9] (Q := fun u => u.gpr .r5 = off B (arr w q) ∧ u.gpr .r9 = 0 ∧ u.mem = s.mem)
    (by prun; rfl) (by decide)) fun u ⟨⟨u5, u9, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := k₀.trans' ku.mono
  have hu : Ws u B Z w N := h.of_keep k₁
  refine evenW_ok hu (fun hev x mx kx => ?_) (fun hodd x mx kx => ?_)
  · have hx := hu.of_keep kx
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w q) ∧
      y.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ y.gpr .r9 = 0 ∧ y.mem = u.mem)
      (by prun [kx.gpr (r := .r5) (by decide), kx.gpr (r := .r9) (by decide), u5, u9, hx.r29, mx,
        lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]) (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
    have hy := hx.of_keep ky
    refine WP.mono (shlWLoop_ok hy.scr y5 y8 (by rw [y9]; decide) (by omega_arith) (by omega_arith) (by omega_arith))
      fun t ⟨c9, vq, tout, kt, _⟩ => ⟨hy.of_keep kt, Keep.mono (rs' := opRegs) (((k₁.trans kx).trans ky).trans kt)
        (by decide), c9, by rw [ym, um] at tout; simpa only [show 8 * (w / 2) = 4 * w by omega_arith] using tout, ?_⟩
    rw [ym, um, y9, show 64 * (w / 2) = 32 * w by omega_arith] at vq
    rw [num_words _ _ hev, num_words _ _ hev]; simpa using vq
  · have hx := hu.of_keep kx
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w q) ∧
      y.gpr .r8 = BitVec.ofNat 64 w ∧ y.gpr .r9 = 0 ∧ y.mem = u.mem)
      (by prun [kx.gpr (r := .r5) (by decide), kx.gpr (r := .r9) (by decide), u5, u9, hx.r29, mx,
        BitVec.add_zero]) (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
    have hy := hx.of_keep ky
    refine WP.mono (shlLoop_ok hy.scr y5 y8 (by rw [y9]; decide) (by omega_arith) (by omega_arith) (by omega_arith))
      fun t ⟨c9, vq, tout, kt⟩ => ⟨hy.of_keep kt, Keep.mono (rs' := opRegs) (((k₁.trans kx).trans ky).trans kt)
        (by decide), c9, by rw [ym, um] at tout; exact tout, ?_⟩
    rw [ym, um, y9] at vq; simpa using vq

/-- `shiftR r v`: `[r]' + 2^(32 (v + 1)) c' = 2 [r] + r9`, over `v + 1` digits. -/
theorem shiftR_ok {s : State} {B : Addr} {Z w N r v : Nat} (h : Ws s B Z w N) (hr : r < N) (hN : N ≤ 256) (hv : v ≤ w)
    (c9 : (s.gpr .r9).toNat ≤ 1) :
    WP isa (shiftR r v) s fun t => Ws t B Z w N ∧ Outside B (arr w r) (4 * (v + 1)) s.mem t.mem ∧
      (∃ c' ≤ 1, numV t.mem B w v r + 2 ^ (32 * (v + 1)) * c' = 2 * numV s.mem B w v r + (s.gpr .r9).toNat) ∧
      Keep opRegs s t := by
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [shiftR, WP.seq_iff, ← List.append_nil (ptr .r5 r)]
  refine ptr_ok h (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega_arith) (WP.block_nil ?_)
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w r) ∧
    y.gpr .r8 = BitVec.ofNat 64 (v + 1) ∧ y.gpr .r9 = s.gpr .r9 ∧ y.mem = s.mem)
    (by prun [exec_li (show v + 1 < 2 ^ 15 by omega_arith)]) rfl rfl) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
  have k₁ : Keep opRegs s y := ((Keep.write _ _ _).trans ky).mono (by decide)
  have hy : Ws y B Z w N := h.of_keep k₁
  refine WP.mono (shlLoop_ok hy.scr y5 y8 (by rw [y9]; exact c9) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨c9', vr, tout, kt⟩ => ⟨hy.of_keep kt, by rw [← ym]; exact tout, ⟨_, c9', ?_⟩, k₁.trans' kt⟩
  rw [ym, y9] at vr; exact vr

/-- `shift q r v`: the quotient and the remainder shifted together. -/
theorem shift_ok {s : State} {B : Addr} {Z w N q r v : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hN : N ≤ 256) (hqr : q ≠ r) (hv : v ≤ w) :
    WP isa (shift q r v) s fun t => Ws t B Z w N ∧ VG.Proof.Rsa.KeyWorkspace.Keep B w [q, r] [] s.mem t.mem ∧
      (∃ c ≤ 1, num t.mem B w q + 2 ^ (32 * w) * c = 2 * num s.mem B w q ∧
        ∃ c' ≤ 1, numV t.mem B w v r + 2 ^ (32 * (v + 1)) * c' = 2 * numV s.mem B w v r + c) ∧
      Keep opRegs s t := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have dqr := arr_disj (w := w) hqr
  rw [shift, WP.seq_iff]
  refine WP.mono (shiftQ_ok h hq hN) fun u ⟨hu, ku, c9, uout, uq⟩ => ?_
  refine WP.mono (shiftR_ok hu hr hN hv c9) fun t ⟨ht, tout, ⟨c', hc', er⟩, kt⟩ => ⟨ht, ?_, ⟨_, c9, ?_, c', hc', ?_⟩,
    (ku.trans kt).mono (by decide)⟩
  · exact (VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (o := q) (d := 0) (by simpa using uout) (by omega_arith) (by simp)).trans
      (VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (o := r) (d := 0) (by simpa using tout) (by omega_arith) (by simp))
  · rw [show num t.mem B w q = num u.mem B w q from tout.val32 (by omega_arith) (by omega_arith)]; exact uq
  · rw [show numV u.mem B w v r = numV s.mem B w v r from uout.val32 (by omega_arith) (by omega_arith)] at er
    exact er

/-- `subtract r d t v`: `[t] + [d] = [r] + 2^(32 (v + 1)) β`, over `v + 1` digits. -/
theorem subtract_ok {s : State} {B : Addr} {Z w N r d t v : Nat} (h : Ws s B Z w N)
    (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256) (htr : t ≠ r) (htd : t ≠ d) (hv : v ≤ w) :
    WP isa (subtract r d t v) s fun u => Ws u B Z w N ∧ VG.Proof.Rsa.KeyWorkspace.Keep B w [t] [] s.mem u.mem ∧
      numV u.mem B w v t + numV s.mem B w v d = numV s.mem B w v r + 2 ^ (32 * (v + 1)) * (u.gpr .r9).toNat ∧
      (u.gpr .r9).toNat ≤ 1 ∧ Keep opRegs s u := by
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have nw := h.nowrap
  rw [subtract]
  refine ptr3_ok' h (by omega_arith) (by omega_arith) (by omega_arith) fun x p5 p6 p7 kx mx => ?_
  have hb : WP isa (.block [.li .r8 (v + 1), .li .r9 0]) x fun y =>
      (y.gpr .r5 = off B (arr w t) ∧ y.gpr .r6 = off B (arr w r) ∧ y.gpr .r7 = off B (arr w d) ∧
        y.gpr .r8 = BitVec.ofNat 64 (v + 1) ∧ y.gpr .r9 = 0 ∧ y.mem = x.mem) ∧ Keep [.r8, .r9] x y := by
    refine WP.keep _ ?_ rfl rfl
    prun [p5, p6, p7, exec_li (show v + 1 < 2 ^ 15 by omega_arith)]
    rfl
  rw [WP.seq_iff]
  refine WP.mono hb fun y ⟨⟨y5, y6, y7, y8, y9, ym⟩, ky⟩ => ?_
  have k₁ : Keep opRegs s y := (kx.trans ky).mono (by decide)
  have hy : Ws y B Z w N := h.of_keep k₁
  refine WP.mono (subLoop_ok hy.scr y5 y6 y7 y8 (by rw [y9]; decide) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (aheadV hv htr) (aheadV hv htd)) ?_
  intro u ⟨b9, vv, out, ku⟩
  rw [y9, ym, mx] at vv
  rw [ym, mx] at out
  exact ⟨hy.of_keep ku, VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega_arith) (by simp), by simpa using vv, b9, k₁.trans' ku⟩

/-- `keep r t v`: `[r] := b ? [t] : [r]` over `v + 1` digits, the mask of `b` in `r9`. -/
theorem keep_ok {s : State} {B : Addr} {Z w N r t v : Nat} (h : Ws s B Z w N)
    (hr : r < N) (ht : t < N) (hN : N ≤ 256) (hrt : r ≠ t) (hv : v ≤ w) {b : Bool}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) :
    WP isa (keep r t v) s fun u => Ws u B Z w N ∧ VG.Proof.Rsa.KeyWorkspace.Keep B w [r] [] s.mem u.mem ∧
      numV u.mem B w v r = (if b then numV s.mem B w v t else numV s.mem B w v r) ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8] s u := by
  have fr := h.arr_fit hr
  have ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have nw := h.nowrap
  rw [keep]
  refine ptr3_ok' h (by omega_arith) (by omega_arith) (by omega_arith) fun x p5 p6 p7 kx mx => ?_
  have x9 : x.gpr .r9 = s.gpr .r9 := kx.gpr _ (by decide)
  have hb : WP isa (.block [.li .r8 (v + 1)]) x fun y =>
      (y.gpr .r5 = off B (arr w r) ∧ y.gpr .r6 = off B (arr w r) ∧ y.gpr .r7 = off B (arr w t) ∧
        y.gpr .r8 = BitVec.ofNat 64 (v + 1) ∧ y.gpr .r9 = s.gpr .r9 ∧ y.mem = x.mem) ∧ Keep [.r8] x y := by
    refine WP.keep _ ?_ rfl rfl
    prun [p5, p6, p7, x9, exec_li (show v + 1 < 2 ^ 15 by omega_arith)]
  rw [WP.seq_iff]
  refine WP.mono hb fun y ⟨⟨y5, y6, y7, y8, y9, ym⟩, ky⟩ => ?_
  have k₁ : Keep [.r0, .r5, .r6, .r7, .r8] s y := (kx.trans ky).mono (by decide)
  have hy : Ws y B Z w N := h.of_keep k₁
  refine WP.mono (selLoop_ok hy.scr y5 y6 y7 y8 (by rw [y9, h9]) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (Or.inl (Nat.le_refl _)) (aheadV hv hrt)) ?_
  intro u ⟨vv, out, ku⟩
  rw [ym, mx] at vv out
  exact ⟨hy.of_keep ku, VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega_arith) (by simp), vv, (k₁.trans ku).mono (by decide)⟩

/-- The numbers of a step, as `Proof/Rsa/PPC64LE/DivLoop.lean`'s `step_arith`
with the divisor below `Pd` rather than `P1`. -/
theorem step_arith {D R Q Q1 R1 T c c' β P1 Pd P2 H : Nat} (hD : 0 < D) (hR : R < D)
    (hDP : D < Pd) (hP1 : P1 = 2 * H) (hP2 : P2 = 4294967296 * Pd) (hQ1 : Q1 < P1) (hT : T < P2)
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
theorem step_ok {s : State} {B : Addr} {Z w N q r d t v : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t) (hv : v ≤ w)
    {D N₀ k : Nat} (hk : k < 32 * w) (hN₀ : N₀ < 2 ^ (32 * w)) (hD : numV s.mem B w v d = D)
    (hDw : D < 2 ^ (32 * v))
    (vals : 0 < D → num s.mem B w q = (divIter D (32 * w) k (0, N₀)).2 ∧
      numV s.mem B w v r = (divIter D (32 * w) k (0, N₀)).1) :
    WP isa (step q r d t v) s fun u => Ws u B Z w N ∧ VG.Proof.Rsa.KeyWorkspace.Keep B w [q, r, t] [] s.mem u.mem ∧
      u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1 ∧ Keep stepRegs s u ∧
      (0 < D → num u.mem B w q = (divIter D (32 * w) (k + 1) (0, N₀)).2 ∧
        numV u.mem B w v r = (divIter D (32 * w) (k + 1) (0, N₀)).1) := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have ft := h.arr_fit ht
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  rw [step, WP.seq_iff]
  refine WP.mono (shift_ok h hq hr hN hqr hv) fun s1 ⟨h1, km1, ⟨c, hc, eq1, c', hc', er1⟩, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (subtract_ok h1 hr hd ht hN (Ne.symm hrt) (Ne.symm hdt) hv)
    fun s2 ⟨h2, km2, eT, hβ, k2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (bit_ok hβ) fun s3 ⟨⟨r10, r9, m3⟩, k3⟩ => ?_
  have h3 : Ws s3 B Z w N := h2.of_keep k3
  rw [WP.seq_iff]
  refine WP.mono (keep_ok h3 hr ht hN hrt hv (b := decide ((s2.gpr .r9).toNat = 0))
    (by rw [r9]; by_cases z : (s2.gpr .r9).toNat = 0 <;> simp [z])) fun s4 ⟨h4, km4, eR, k4⟩ => ?_
  have e10 : s4.gpr .r10 = s3.gpr .r10 := k4.gpr _ (by decide)
  have q2 : num s2.mem B w q = num s1.mem B w q :=
    VG.Proof.Rsa.KeyWorkspace.Keep.num km2 (by simp; omega_arith) (by simp) (by omega_arith)
  have q4 : num s4.mem B w q = num s1.mem B w q := by
    rw [VG.Proof.Rsa.KeyWorkspace.Keep.num km4 (by simp; omega_arith) (by simp) (by omega_arith), m3, q2]
  have even : num s4.mem B w q % 2 = 0 := by
    rw [q4]
    have : 2 ∣ 2 ^ (32 * w) * c :=
      Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero (Nat.pow_mod 2 (32 * w) 2 ▸ by
        rw [Nat.mod_self, Nat.zero_pow (by omega_arith)])) _
    omega_arith
  refine WP.mono (setBit_ok h4 hq hN even (by rw [e10, r10]; split <;> decide))
    fun u ⟨hu, km5, eQ, u4, k5⟩ => ?_
  have kr : Keep stepRegs s u := ((((k1.trans k2).trans k3).trans k4).trans k5).mono
  have k12 : VG.Proof.Rsa.KeyWorkspace.Keep B w [q, r, t] [] s.mem s2.mem := VG.Proof.Rsa.KeyWorkspace.Keep.join km1 km2
  have k45 : VG.Proof.Rsa.KeyWorkspace.Keep B w [q, r, t] [] s2.mem u.mem := by
    rw [← m3]; exact VG.Proof.Rsa.KeyWorkspace.Keep.join km4 km5
  refine ⟨hu, k12.trans k45, ?_, kr, fun hD0 => ?_⟩
  · rw [u4, k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]
  · obtain ⟨vq, vr⟩ := vals hD0
    obtain ⟨_, hR, -, -, -⟩ := divIter_inv hD0 hN₀ k (by omega_arith)
    have es : divIter D (32 * w) (k + 1) (0, N₀) = divStep D (32 * w) (divIter D (32 * w) k (0, N₀)) := rfl
    have d1 : numV s1.mem B w v d = D := by
      rw [keep_numV km1 (by simp; omega_arith) (by simp) hv (by omega_arith), hD]
    have r2 : numV s2.mem B w v r = numV s1.mem B w v r :=
      keep_numV km2 (by simp; omega_arith) (by simp) hv (by omega_arith)
    have t3 : numV s3.mem B w v t = numV s2.mem B w v t := by rw [m3]
    have ur : numV u.mem B w v r = numV s4.mem B w v r :=
      keep_numV km5 (by simp; omega_arith) (by simp) hv (by omega_arith)
    have hP2 : 2 ^ (32 * (v + 1)) = 4294967296 * 2 ^ (32 * v) := by
      rw [show 32 * (v + 1) = 32 + 32 * v by omega_arith, Nat.pow_add]
    have hP1 : 2 ^ (32 * w) = 2 * 2 ^ (32 * w - 1) := by
      obtain ⟨j, hj⟩ : ∃ j, 32 * w = j + 1 := ⟨32 * w - 1, by omega_arith⟩
      rw [hj, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
    have hQ1 : num s1.mem B w q < 2 ^ (32 * w) := val32_lt _ _ _ _
    have hT : numV s2.mem B w v t < 2 ^ (32 * (v + 1)) := val32_lt _ _ _ _
    rw [d1] at eT
    have hR' : numV s.mem B w v r < D := by rw [vr]; exact hR
    obtain ⟨eR1, eQ1, hb, hTv⟩ := step_arith hD0 hR' hDw hP1 hP2 hQ1 hT hc hβ eq1 er1 eT
    have ep : divIter D (32 * w) k (0, N₀) = (numV s.mem B w v r, num s.mem B w q) :=
      Prod.ext vr.symm vq.symm
    rw [es, ep]
    simp only [divStep]
    rw [ur, eR, t3, m3, r2, eQ, e10, r10, q4, ← eR1, ← eQ1]
    by_cases hl : numV s1.mem B w v r < D
    · have hβ1 : (s2.gpr .r9).toNat ≠ 0 := fun z => absurd (hb.mp z) (by omega_arith)
      simp only [hl, hβ1, ↓reduceIte, decide_false]
      exact ⟨by simp, rfl⟩
    · have hβ0 : (s2.gpr .r9).toNat = 0 := hb.mpr (by omega_arith)
      simp only [hl, hβ0, ↓reduceIte, decide_true]
      exact ⟨by simp, hTv hβ0⟩

/-- `zeroHi r v`: the remainder's digits `v + 1` to `w − 1` := 0. -/
theorem zeroHi_ok {s : State} {B : Addr} {Z w N r v : Nat} (h : Ws s B Z w N) (hr : r < N) (hN : N ≤ 256)
    (hv : v + 1 < w) :
    WP isa (zeroHi r v) s fun u => Ws u B Z w N ∧
      Outside B (arr w r + 4 * (v + 1)) (4 * (w - (v + 1))) s.mem u.mem ∧
      val32 u.mem B (arr w r + 4 * (v + 1)) (w - (v + 1)) = 0 ∧ Keep [.r0, .r5, .r8] s u := by
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [zeroHi, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega_arith) ?_
  have e8 : BitVec.ofNat 64 w - BitVec.ofNat 64 (v + 1) = BitVec.ofNat 64 (w - (v + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  have e5 : off B (arr w r) + BitVec.ofNat 64 (4 * (v + 1)) = off B (arr w r + 4 * (v + 1)) := by
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  have hb : WP isa (.block [.addi .r5 .r5 (4 * (v + 1)), .subi .r8 .r29 (v + 1), .li .r0 0])
      (s.write .r5 (off B (arr w r))) fun u =>
      (u.gpr .r5 = off B (arr w r + 4 * (v + 1)) ∧ u.gpr .r8 = BitVec.ofNat 64 (w - (v + 1)) ∧
        u.gpr .r0 = 0 ∧ u.mem = s.mem) ∧ Keep [.r0, .r5, .r8] (s.write .r5 (off B (arr w r))) u := by
    refine WP.keep _ ?_ rfl rfl
    prun [h.r29, e8, e5, exec_addi (d := .r5) (show Reg.r5 ≠ .r0 by decide) (show 4 * (v + 1) < 2 ^ 15 by omega_arith),
      exec_subi (d := .r8) (show Reg.r29 ≠ .r0 by decide) (show v + 1 ≤ 2 ^ 15 by omega_arith)]
    rfl
  refine WP.mono hb fun u ⟨⟨u5, u8, u0, mu⟩, ku⟩ => ?_
  have k₁ : Keep [.r0, .r5, .r8] s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (zeroLoop_ok hu.scr u5 u8 u0 (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨z, out, kt⟩ => ⟨hu.of_keep kt, by rw [← mu]; exact out, Proof.Bignum.PPC64LE.val32_zero fun j hj => z j hj,
      (k₁.trans kt).mono (by decide)⟩

/-- `div q r d t v`: `[q] := [q] / [d]` and `[r] := [q] mod [d]`, for `[d] < 2^(32 v)`
and `v + 1 < w`, when `[d]` is not 0. -/
theorem div_ok {s : State} {B : Addr} {Z w N q r d t v : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 256)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t) (hv : v + 1 < w)
    (hDv : num s.mem B w d < 2 ^ (32 * v)) :
    WP isa (div q r d t v) s fun u => Ws u B Z w N ∧ VG.Proof.Rsa.KeyWorkspace.Keep B w [q, r, t] [] s.mem u.mem ∧
      Keep stepRegs s u ∧
      (0 < num s.mem B w d → num u.mem B w q = num s.mem B w q / num s.mem B w d ∧
        num u.mem B w r = num s.mem B w q % num s.mem B w d) := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have hv' : v ≤ w := by omega_arith
  have hD : numV s.mem B w v d = num s.mem B w d :=
    val32_low (by omega_arith) (Nat.lt_of_lt_of_le hDv (Nat.pow_le_pow_right (by decide) (by omega_arith)))
  have hN₀ : num s.mem B w q < 2 ^ (32 * w) := val32_lt _ _ _ _
  rw [div, WP.seq_iff]
  refine WP.mono (init_ok h hr hN) fun u ⟨hu, km, z, u4, ku⟩ => ?_
  let D := num s.mem B w d
  let N₀ := num s.mem B w q
  let Inv : Nat → State → Prop := fun i x =>
    Ws x B Z w N ∧ VG.Proof.Rsa.KeyWorkspace.Keep B w [q, r, t] [] s.mem x.mem ∧ Keep stepRegs s x ∧
      (0 < D → num x.mem B w q = (divIter D (32 * w) i (0, N₀)).2 ∧
        numV x.mem B w v r = (divIter D (32 * w) i (0, N₀)).1)
  have z' : numV u.mem B w v r = 0 := by
    have := val32_low (m := u.mem) (B := B) (d := arr w r) (k := v + 1) (n := w + 1) (by omega_arith)
      (by change num1 u.mem B w r < _; rw [z]; exact Nat.two_pow_pos _)
    change val32 _ _ _ _ = 0; rw [this]; exact z
  have i0 : Inv 0 u := ⟨hu, km.mono, ku.mono, fun _ => ⟨VG.Proof.Rsa.KeyWorkspace.Keep.num km (by simp; omega_arith)
    (by simp) (by have := h.fit64 hq; omega_arith), z'⟩⟩
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Bignum.PPC64LE.wp_countdown (body := step q r d t v) (cnt := .r4) (N := 32 * w)
    (by omega_arith) (by omega_arith) Inv (fun i hi x ⟨hx, kx, rx, vx⟩ _ => ?_) i0 u4) fun x ⟨hx, kx, rx, vx⟩ => ?_
  · have dx : numV x.mem B w v d = D := by
      rw [keep_numV kx (by simp; omega_arith) (by simp) hv' (by omega_arith), hD]
    refine WP.mono (step_ok hx hq hr hd ht hN hqr hqd hqt hrd hrt hdt hv' hi hN₀ dx hDv vx)
      fun y ⟨hy, ky, y4, ry, vy⟩ => ⟨⟨hy, kx.trans ky, rx.trans' ry, vy⟩, y4⟩
  · refine WP.mono (zeroHi_ok hx hr hN hv) fun y ⟨hy, yout, yz, ky⟩ => ⟨hy, ?_, (rx.trans ky).mono (by decide), fun hD0 => ?_⟩
    · exact kx.trans (VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (o := r) yout (by omega_arith) (by simp))
    obtain ⟨e1, e2⟩ := vx hD0
    rw [divIter_done hD0 hN₀] at e1 e2
    refine ⟨?_, ?_⟩
    · exact (yout.val32 (by have := arr_disj (w := w) hqr; simp only [S] at this; omega_arith) (by omega_arith)).trans e1
    · have ea := val32_append y.mem B (arr w r) (v + 1) (w - (v + 1))
      rw [Nat.add_sub_cancel' (by omega_arith : v + 1 ≤ w)] at ea
      change val32 _ _ _ w = _
      rw [ea, yz, Nat.mul_zero, Nat.add_zero]
      exact (yout.val32 (by omega_arith) (by omega_arith)).trans e2

end VG.Proof.Dsa.PPC64LE.DivN

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws stepRegs)
open VG.Proof.Dsa.PPC64LE.DivN (div_ok)
open VG.Impl.Dsa.PPC64LE.Generation

/-- The stage after the division. -/
abbrev divCfg (c : Cfg) (q r d : Nat) : Cfg :=
  { c with A := KU (KU c.A q (c.A q / c.A d)) r (c.A q % c.A d), live := q :: r :: c.live }

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The division: `[q] := [q] / [d]`, `[r] := [q] mod [d]`, the temporary `t` lost. -/
theorem div_vp {q r d t v : Nat} (cert : CertK (VG.Impl.Dsa.PPC64LE.DivN.div q r d t v))
    (hq : q < nArrs) (hr : r < nArrs) (hd : d < nArrs) (ht : t < nArrs)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hqL : q ∈ c.live) (hdL : d ∈ c.live) (htL : t ∉ c.live) (hpos : 0 < c.A d)
    (hv : v + 1 < G.w) (hDv : c.A d < 2 ^ (32 * v)) :
    VP (KSt G c X) (VG.Impl.Dsa.PPC64LE.DivN.div q r d t v) (KSt G (divCfg c q r d) X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get hqL
  have vd := h.arrs.get hdL
  refine h.ksWP rfl (div_ok hw hq hr hd ht (by decide) hqr hqd hqt hrd hrt hdt hv (by simp only [GP.ksState, State.withRegions_mem]; rw [vd]; exact hDv))
    fun u ⟨_, k, R, v⟩ hr' hw' f => ?_
  have R' : Keep stepRegs s u := ⟨R.gpr, hr', hw'⟩
  simp only [GP.ksState, State.withRegions_mem] at v k
  rw [vd] at v
  obtain ⟨vq, vr'⟩ := v hpos
  rw [va] at vq vr'
  refine ⟨⟨h.of_ks R' R.sp f (fun j hj => ?_) (fun j hj => ?_) (fun e he => ?_) h.kslOk, x⟩, kr.of_keep R'⟩
  · show num u.mem G.KB G.w j = VG.Proof.Rsa.KeyWorkspace.upd (VG.Proof.Rsa.KeyWorkspace.upd c.A q
      (c.A q / c.A d)) r (c.A q % c.A d) j
    by_cases ejr : j = r
    · subst ejr; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact vr'
    rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ ejr]
    by_cases ejq : j = q
    · subst ejq; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact vq
    rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ ejq]
    have jl : j ∈ c.live := by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd rfl ejq
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd rfl ejr
      · exact hj
    have ejt : j ≠ t := fun e => htL (e ▸ jl)
    rw [k.num (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro k' (rfl | rfl | rfl) <;> omega)
      (by simp) (hw.fit64 (h.liveOk j jl))]
    exact h.arrs.get jl
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact hq
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hr
    · exact h.liveOk j hj
  · rw [k.slot (h.kslOk e he).1 (by simp)]; exact h.ksl e he

end

end VG.Proof.Dsa.PPC64LE.Gen
