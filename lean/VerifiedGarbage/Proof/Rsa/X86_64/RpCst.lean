import VerifiedGarbage.Proof.Rsa.X86_64.RpMont

/-!
# `vg_rsa_recover_primes` on x86-64: the candidates' constants

`Cst`: what the candidates read and never change: the working space,
`-n⁻¹`, `n`, `R² mod n`, 1, `R mod n` and `n - R mod n` (the Montgomery forms
of 1 and `-1`), `e`'s length, `r` and `t`. A piece that changes other arrays
and slots keeps it (`Cst.congr`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)

/-- The constants of the candidates, for `n = N`, `e_len = el`, and `m = 2^t r`. -/
structure Cst (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N el r t : Nat) : Prop where
  ws : Ws s B Z w
  hmv : word s.mem B (8 * sMinv) = minv
  hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  hn : wv s.mem B (slot w aN) w = N
  hr2lt : wv s.mem B (slot w aR2) w < N
  hr2 : wv s.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N
  hone : wv s.mem B (slot w aOne) w = 1
  ho : wv s.mem B (slot w aO) w = 2 ^ (64 * w) % N
  hng : wv s.mem B (slot w aNg) w = N - 2 ^ (64 * w) % N
  hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el
  hm : wv s.mem B (slot w aM) (w + (el + 7) / 8) = r
  ht : word s.mem B (8 * sT) = BitVec.ofNat 64 t
  odd : N % 2 = 1
  lo : 2 ^ (64 * (w - 1)) ≤ N
  e1 : 1 ≤ el
  e2 : el ≤ 8 * w
  t1 : 1 ≤ t
  t2 : t < 64 * (w + (el + 7) / 8)

/-- The arrays the candidates keep. -/
def cArr : List Nat := [aN, aR2, aOne, aO, aNg, aM, aM + 1]

theorem Cst.congr {s u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (h : Cst s B Z w minv N el r t) {js hs : List Nat} (hf : Frm B (rg w js hs) s.mem u.mem)
    (hjs : ∀ j ∈ cArr, j ∉ js) (hhs : ∀ i ∈ hs, rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT) {regs : List Reg}
    (k : Keep regs s u) (hr : .rdi ∉ regs) : Cst u B Z w minv N el r t := by
  have hw := h.ws
  have hZ16 : slot w 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
  have h32 : ∀ i ∈ hs, i < 32 := fun i hi => by
    have := (hhs i hi).1; simp only [rSlot, Bool.or_eq_true, beq_iff_eq] at this; omega
  have hwv : ∀ j ∈ cArr, j < 16 → wv u.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj hj' =>
    hf.rg_wv hZ16 h32 hj' (hjs j hj) (by omega)
  have hsl : ∀ i, i < 32 → rSlot i = false → word u.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hr =>
    hf.rg_word hi fun hm => by have := (hhs i hm).1; rw [hr] at this; cases this
  refine ⟨hw.congrG hf (fun i hi => (hhs i hi).1) k hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.odd, h.lo, h.e1, h.e2, h.t1, h.t2⟩
  · rw [hf.rg_word (by decide) fun hm => (hhs _ hm).2.1 rfl]; exact h.hmv
  · rw [hf.rg_word0 hZ16 h32 (by decide) (hjs aN (by decide))]; exact h.hinv
  · rw [hwv aN (by decide) (by decide)]; exact h.hn
  · rw [hwv aR2 (by decide) (by decide)]; exact h.hr2lt
  · rw [hwv aR2 (by decide) (by decide)]; exact h.hr2
  · rw [hwv aOne (by decide) (by decide)]; exact h.hone
  · rw [hwv aO (by decide) (by decide)]; exact h.ho
  · rw [hwv aNg (by decide) (by decide)]; exact h.hng
  · rw [hsl _ (by decide) (by decide)]; exact h.hel
  · rw [hf.rg_wv2 hZ16 h32 (by decide) (hjs aM (by decide)) (hjs (aM + 1) (by decide))
      (by have := h.e2; omega)]; exact h.hm
  · rw [hf.rg_word (by decide) fun hm => (hhs _ hm).2.2 rfl]; exact h.ht

theorem Cst.hZ16 {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (h : Cst s B Z w minv N el r t) : slot w 16 ≤ 2 ^ 64 := by
  have := h.ws.scr.nowrap; have := h.ws.hZ; omega

theorem Cst.good {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (h : Cst s B Z w minv N el r t) : Good s B Z w minv ∧ slot w 8 ≤ Z := by
  have := h.ws.good; rw [h.hmv] at this; exact this

theorem Cst.n1 {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (h : Cst s B Z w minv N el r t) : 2 ^ 64 ≤ N := by
  have := h.ws.w1
  have : 2 ^ 64 ≤ 2 ^ (64 * (w - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  have := h.lo
  omega

theorem Cst.coprime {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (h : Cst s B Z w minv N el r t) : Nat.Coprime (2 ^ (64 * w)) N :=
  VG.Proof.Bignum.coprime_pow2 h.odd _

end VG.Proof.Rsa.X86_64
