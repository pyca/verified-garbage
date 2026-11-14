module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtChecks
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PrivPre
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Spec.Rsa

/-!
# An RSA private key's precomputed values on PPC64LE: `p q = n` at the factors' widths

`checkPQs_ok`: `PrivPre.checkPQs` is a check of `p q = n` as
`Crt.checksAWith_ok` needs it (`Crt.PQOk`), when `p` and `q` fit in `w_p`
(`r5`) and `w_q` (`r7`) words, `w_p + w_q ≤ W`:

* `rowWord_ok`, `row_ok`: a row of the schoolbook product, `t += a q`
  over `q`'s `w_q` words, its carry into the word after them (`mac_arith`);
* `rows_ok`: `w_p` rows, `t = p q` over `w_p + w_q` words, from `t = 0`;
* `checkPQs_ok`: array 6 zeroed, `p q` into it, then `Crt.pqEq_ok`;
* `pqLens_ok`: `w_p` and `w_q` from the header's lengths, which `p` and
  `q` fit in (`fit`): `checkPQs` is then a check of `p q = n`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PrivPre
open VG.Proof.Bignum.PPC64LE
open VG.Proof.Bignum (slot wv word Outside off ofs)

/-- The arithmetic of a word of a row: `a q + t + c` as its low word and the
next carry, the high word of `a q` plus the carries of the two additions. -/
theorem mac_arith (a q x c : BitVec 64) :
    (BitVec.ofNat 64 ((BitVec.ofNat 64 ((a * q).toNat + x.toNat)).toNat + c.toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 ((BitVec.ofNat 64 ((BitVec.ofNat 64 (a.toNat * q.toNat / 2 ^ 64)).toNat +
        (decide (2 ^ 64 ≤ (a * q).toNat + x.toNat)).toNat)).toNat +
        (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((a * q).toNat + x.toNat)).toNat + c.toNat)).toNat)).toNat =
      a.toNat * q.toNat + x.toNat + c.toNat := by
  have ha := a.isLt; have hq := q.isLt; have hx := x.isLt; have hc := c.isLt
  have hP : a.toNat * q.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have hd := Nat.div_add_mod (a.toNat * q.toNat) (2 ^ 64)
  have e0 : (a * q).toNat = a.toNat * q.toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  have hhi : a.toNat * q.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
    have := Nat.div_le_div_right (c := 2 ^ 64) hP
    have h2 : (2 ^ 64 - 1) * (2 ^ 64 - 1) / 2 ^ 64 = 2 ^ 64 - 2 := by decide
    omega_arith
  rw [e0]
  generalize a.toNat * q.toNat = P at hP hd hhi ⊢
  generalize x.toNat = X at hx ⊢
  generalize c.toNat = C at hc ⊢
  have hm := Nat.mod_lt P (show 0 < 2 ^ 64 by decide)
  generalize P % 2 ^ 64 = L at hm hd ⊢
  generalize P / 2 ^ 64 = H at hhi hd ⊢
  subst hd
  simp only [BitVec.toNat_ofNat]
  by_cases h1 : 2 ^ 64 ≤ L + X <;> by_cases h2 : 2 ^ 64 ≤ (L + X) % 2 ^ 64 + C <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-! ## A row -/

/-- What a row keeps after `j` words, from `s`, with the multiplier `a`
(`r12`): the pointers, the carry `c` (`r3`), with
`t_{<j} + 2^(64 j) c = t₀_{<j} + a q_{<j}`, and the words from `j` on. -/
def RowI (s : State) (B : Addr) (dA dQ : Nat) (a : BitVec 64) (j : Nat) (t : State) : Prop :=
  t.gpr .r14 = off B (dA + 8 * j) ∧ t.gpr .r15 = off B (dQ + 8 * j) ∧ t.gpr .r12 = a ∧
    Outside B dA (8 * j) s.mem t.mem ∧
    wv t.mem B dA j + 2 ^ (64 * j) * (t.gpr .r3).toNat = wv s.mem B dA j + a.toNat * wv s.mem B dQ j ∧
    Keep [.r0, .r3, .r4, .r6, .r14, .r15, .r16] s t

theorem rowWord_ok {s : State} {B : Addr} {Z dA dQ wq : Nat} {a : BitVec 64} (hs : Scr s B Z)
    (hA : dA + 8 * wq ≤ Z) (hQ : dQ + 8 * wq ≤ Z) (dAQ : dQ + 8 * wq ≤ dA ∨ dA + 8 * wq ≤ dQ)
    {j : Nat} (hj : j < wq) {t : State} (hI : RowI s B dA dQ a j t) :
    WP isa (.block (rowWord ++ ([.subi .r16 .r16 1] : List Instr))) t fun t' =>
      RowI s B dA dQ a (j + 1) t' ∧ t'.gpr .r16 = t.gpr .r16 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j14, j15, j12, jout, jv, jk⟩ := hI
  have hs' := hs.congr jk.wr
  have wT : word t.mem B (dA + 8 * j) = word s.mem B (dA + 8 * j) := jout.word (by omega_arith) (by omega_arith)
  have wQ : word t.mem B (dQ + 8 * j) = word s.mem B (dQ + 8 * j) := jout.word (by omega_arith) (by omega_arith)
  generalize hq : word s.mem B (dQ + 8 * j) = q at wQ
  generalize hx : word s.mem B (dA + 8 * j) = x at wT
  have rQ : t.mem.readW (off B (dQ + 8 * j)) 64 = q := wQ
  have rT : t.mem.readW (off B (dA + 8 * j)) 64 = x := wT
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r6, .r14, .r15, .r16] (Q := fun t' =>
      t'.gpr .r14 = off B (dA + 8 * j + 8) ∧ t'.gpr .r15 = off B (dQ + 8 * j + 8) ∧
      t'.gpr .r16 = t.gpr .r16 - BitVec.ofNat 64 1 ∧
      ∃ lo : BitVec 64, t'.mem = t.mem.writeW (off B (dA + 8 * j)) lo ∧
        lo.toNat + 2 ^ 64 * (t'.gpr .r3).toNat = q.toNat * a.toNat + x.toNat + (t.gpr .r3).toNat) ?_
    (by decide)) fun t' ⟨⟨u14, u15, u16, lo, um, ua⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' uk⟩, u16⟩
  · unfold rowWord
    mcrun [j14, j15, j12, rQ, rT, hs'.ld (show dQ + 8 * j + 8 ≤ Z by omega_arith),
      hs'.ld (show dA + 8 * j + 8 ≤ Z by omega_arith), hs'.st (show dA + 8 * j + 8 ≤ Z by omega_arith)]
    exact ⟨_, rfl, mac_arith q a x (t.gpr .r3)⟩
  · rw [u14, show dA + 8 * j + 8 = dA + 8 * (j + 1) by omega_arith]
  · rw [u15, show dQ + 8 * j + 8 = dQ + 8 * (j + 1) by omega_arith]
  · rw [uk.gpr .r12 (by decide), j12]
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside t.mem B (d := dA + 8 * j) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · rw [um, wv_writeW_top _ _ _ _ _ (by omega_arith), VG.Proof.Bignum.wv, VG.Proof.Bignum.wv, hq, hx,
      Nat.mul_succ, Nat.pow_add]
    generalize (t'.gpr .r3).toNat = c' at ua ⊢
    generalize (t.gpr .r3).toNat = c at ua jv
    generalize 2 ^ (64 * j) = P at jv ⊢
    generalize wv t.mem B dA j = Wt at jv ⊢
    generalize wv s.mem B dA j = Ws at jv ⊢
    generalize wv s.mem B dQ j = Qs at jv ⊢
    have := congrArg (P * ·) ua
    grind

/-- The registers a row writes. -/
def rowRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r12, .r14, .r15, .r16]

/-- A row, `p_i` at `dP + 8 i` (`r8`), the product's words from `i` at `dA`
(`r9`), `q`'s `w_q` words (`r7`) in array 5, and the product's word
`i + w_q` (which the row overwrites): `t := t + p_i q` over `w_q + 1`
words, and the next row's pointers and count. -/
theorem row_ok {s : State} {B : Addr} {Z w dP dA wq i : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (dP + 8 * i)) (h9 : s.gpr .r9 = off B dA) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h7 : s.gpr .r7 = BitVec.ofNat 64 wq) (hwq : 1 ≤ wq)
    (hwq' : wq < 2 ^ 31) (hPZ : dP + 8 * i + 8 ≤ Z)
    (hA : dA + 8 * (wq + 1) ≤ Z) (hQ : slot w 5 + 8 * wq ≤ Z)
    (dAQ : slot w 5 + 8 * wq ≤ dA ∨ dA + 8 * (wq + 1) ≤ slot w 5)
    (dAP : dP + 8 * i + 8 ≤ dA ∨ dA + 8 * (wq + 1) ≤ dP + 8 * i) :
    WP isa (.seq (.block rowHead) (.seq (Precompute.countLoop .r16 rowWord) (.block rowTail))) s fun t =>
      (wv t.mem B dA (wq + 1) = wv s.mem B dA wq +
          (word s.mem B (dP + 8 * i)).toNat * wv s.mem B (slot w 5) wq ∧
        Outside B dA (8 * (wq + 1)) s.mem t.mem ∧ t.gpr .r8 = off B (dP + 8 * i + 8) ∧
        t.gpr .r9 = off B (dA + 8) ∧ t.gpr .r5 = s.gpr .r5 - BitVec.ofNat 64 1) ∧ Keep rowRegs s t := by
  have hnw := hs.nowrap
  unfold rowHead
  generalize hp : word s.mem B (dP + 8 * i) = pw
  have rP : s.mem.readW (off B (dP + 8 * i)) 64 = pw := hp
  -- The row's start.
  have head : WP isa (.block (([.load .d .r12 .r8 0, .addi .r14 .r9 0] : List Instr) ++
      PublicChecked.base .r15 5)) s
      fun t => (t.gpr .r12 = pw ∧ t.gpr .r14 = off B dA ∧ t.gpr .r15 = off B (slot w 5) ∧ t.mem = s.mem) ∧
        Keep [.r12, .r14, .r15] s t := by
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.r12, .r14] (Q := fun t => t.gpr .r12 = pw ∧ t.gpr .r14 = off B dA ∧ t.mem = s.mem)
      (by prun [h8, h9, rP, BitVec.add_zero, hs.ld (show dP + 8 * i + 8 ≤ Z by omega_arith)]) (by decide))
      fun s₁ ⟨⟨a12, a14, m1⟩, k1⟩ => ?_
    refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k1.gpr .r10 (by decide)).trans h10)
      ((k1.gpr .r29 (by decide)).trans h29) 5) fun s₂ ⟨⟨a15, m2⟩, k2⟩ =>
        ⟨⟨by rw [k2.gpr .r12 (by decide), a12], by rw [k2.gpr .r14 (by decide), a14], a15, by rw [m2, m1]⟩,
          (k1.trans k2).mono⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono head fun s₂ ⟨⟨a12, a14, a15, m2⟩, k2⟩ => ?_
  refine WP.mono (WP.keep [.r16, .r3] (Q := fun t => t.gpr .r16 = BitVec.ofNat 64 wq ∧ t.gpr .r3 = 0 ∧
      t.mem = s₂.mem)
    (by prun [(k2.gpr .r7 (by decide)).trans h7, BitVec.add_zero]; rfl) (by decide))
    fun s₃ ⟨⟨a16, a3, m3⟩, k3⟩ => ?_
  have k23 := k2.trans k3
  have I0 : RowI s₃ B dA (slot w 5) pw 0 s₃ := ⟨by rw [k3.gpr .r14 (by decide), a14]; rfl,
    by rw [k3.gpr .r15 (by decide), a15]; rfl, by rw [k3.gpr .r12 (by decide), a12], Outside.refl _ _ _ _,
    by simp [VG.Proof.Bignum.wv, a3], Keep.refl _ _⟩
  have hs₃ := hs.congr k23.wr
  -- The words.
  refine WP.seq (WP.mono (wp_countdown (cnt := .r16) (N := wq) (by omega_arith) (by omega_arith)
    (RowI s₃ B dA (slot w 5) pw)
    (fun j hj t hI _ => rowWord_ok hs₃ (by omega_arith) hQ (by omega_arith) hj hI) I0 a16)
    fun t ⟨j14, _, _, jout, jv, jk⟩ => ?_)
  have k3t := k23.trans jk
  have hst := hs.congr k3t.wr
  -- The carry, and the next row.
  refine WP.mono (WP.keep [.r5, .r8, .r9] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (dA + 8 * wq)) (t.gpr .r3) ∧ t'.gpr .r8 = off B (dP + 8 * i + 8) ∧
        t'.gpr .r9 = off B (dA + 8) ∧ t'.gpr .r5 = s.gpr .r5 - BitVec.ofNat 64 1) (by
    unfold rowTail
    prun [j14, k3t.gpr .r8 (by decide), k3t.gpr .r9 (by decide), k3t.gpr .r5 (by decide), h8, h9,
      hst.st (show dA + 8 * wq + 8 ≤ Z by omega_arith)])
    (by decide)) fun u ⟨⟨um, u8, u9, u5⟩, uk⟩ => ⟨⟨?_, ?_, u8, u9, u5⟩, (k3t.trans uk).mono⟩
  · rw [m3, m2] at jv
    rw [um, wv_writeW_top _ _ _ _ _ (by omega_arith), jv]
  · rw [m3, m2] at jout
    rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside t.mem B (d := dA + 8 * wq) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-! ## The rows -/

/-- What the rows keep after `i` rows, from `s`: the pointers, the product
`p_{<i} q` over the first `i + w_q` words of array 6, and memory elsewhere. -/
def RowsI (s : State) (B : Addr) (w wq : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .r8 = off B (slot w 4 + 8 * i) ∧ t.gpr .r9 = off B (slot w 6 + 8 * i) ∧
    wv t.mem B (slot w 6) (i + wq) = wv s.mem B (slot w 4) i * wv s.mem B (slot w 5) wq ∧
    Outside B (slot w 6) (8 * (i + wq)) s.mem t.mem ∧ Keep rowRegs s t

/-- `rows`, from array 6's first `w_p + w_q ≤ w` words zero, `p` (array 4)
at `r8` and the product (array 6) at `r9`, `w_p` in `r5` and `w_q` in `r7`:
array 6's first `w_p + w_q` words := `p_{<w_p} q_{<w_q}`, changing only
them. -/
theorem rows_ok {s : State} {B : Addr} {Z w wp wq : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 4)) (h9 : s.gpr .r9 = off B (slot w 6)) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h5 : s.gpr .r5 = BitVec.ofNat 64 wp)
    (h7 : s.gpr .r7 = BitVec.ofNat 64 wq) (hwp : 1 ≤ wp) (hwq : 1 ≤ wq) (hpq : wp + wq ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (hz : ∀ k < w, word s.mem B (slot w 6 + 8 * k) = 0) :
    WP isa rows s fun t =>
      (wv t.mem B (slot w 6) (wp + wq) = wv s.mem B (slot w 4) wp * wv s.mem B (slot w 5) wq ∧
        Outside B (slot w 6) (8 * (wp + wq)) s.mem t.mem) ∧ Keep rowRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have I0 : RowsI s B w wq 0 s := ⟨by rw [h8]; rfl, by rw [h9]; rfl,
    by rw [Nat.zero_add, (VG.Proof.Bignum.wv_eq_zero_iff _ _ _ _).mpr (fun k hk => hz k (by omega_arith))]
       simp [VG.Proof.Bignum.wv], Outside.refl _ _ _ _, Keep.refl _ _⟩
  refine WP.mono (wp_countdown (cnt := .r5) (N := wp) (by omega_arith) (by omega_arith) (RowsI s B w wq)
    (fun i hi t ⟨j8, j9, jv, jout, jk⟩ _ => ?_) I0 h5) fun t ⟨_, _, tv, tout, tk⟩ => ⟨⟨tv, tout⟩, tk⟩
  have hst := hs.congr jk.wr
  refine WP.mono (row_ok (dP := slot w 4) (dA := slot w 6 + 8 * i) (i := i) (wq := wq) hst j8
    (by rw [j9]) ((jk.gpr .r10 (by decide)).trans h10) ((jk.gpr .r29 (by decide)).trans h29)
    ((jk.gpr .r7 (by decide)).trans h7) hwq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith))
    fun t' ⟨⟨rv, rout, r8, r9, r5⟩, rk⟩ => ⟨⟨by rw [r8, show slot w 4 + 8 * i + 8 = slot w 4 + 8 * (i + 1) by omega_arith],
      by rw [r9, show slot w 6 + 8 * i + 8 = slot w 6 + 8 * (i + 1) by omega_arith], ?_, ?_, jk.trans' rk⟩, r5⟩
  · have wP : word t.mem B (slot w 4 + 8 * i) = word s.mem B (slot w 4 + 8 * i) :=
      jout.word (by omega_arith) (by omega_arith)
    have wQ : wv t.mem B (slot w 5) wq = wv s.mem B (slot w 5) wq := jout.wv (by omega_arith) (by omega_arith)
    have wL : wv t'.mem B (slot w 6) i = wv t.mem B (slot w 6) i := rout.wv (by omega_arith) (by omega_arith)
    have a1 := VG.Proof.Bignum.wv_add t'.mem B (slot w 6) i (wq + 1)
    have a2 := VG.Proof.Bignum.wv_add t.mem B (slot w 6) i wq
    rw [show i + (wq + 1) = i + 1 + wq by omega_arith, wL, rv, wP, wQ] at a1
    rw [a1, show wv s.mem B (slot w 4) (i + 1) = wv s.mem B (slot w 4) i +
      2 ^ (64 * i) * (word s.mem B (slot w 4 + 8 * i)).toNat from rfl]
    rw [a2] at jv
    generalize 2 ^ (64 * i) = P at jv ⊢
    generalize wv t.mem B (slot w 6) i = A at jv ⊢
    generalize wv t.mem B (slot w 6 + 8 * i) wq = Bv at jv ⊢
    generalize (word s.mem B (slot w 4 + 8 * i)).toNat = pi
    generalize wv s.mem B (slot w 5) wq = Q at jv ⊢
    generalize wv s.mem B (slot w 4) i = Pi at jv ⊢
    grind
  · exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (rout.mono (by omega_arith) (by omega_arith))

/-! ## `p q = n` -/

/-- `checkPQs` is a check of `p q = n` for `Crt.checksAWith_ok`, from `s` with
`w_p` in `r5` and `w_q` in `r7`, `p` and `q` (arrays 4 and 5) of `w_p` and
`w_q` words, `w_p + w_q ≤ W`, and the words `W` of arrays 6 and 1 zero. -/
theorem checkPQs_ok {s : State} {BX : Addr} {Z w wp wq : Nat} (hs : Scr s BX Z) (hZ : slot w 8 ≤ Z)
    (hw' : w < 2 ^ 31) (h5 : s.gpr .r5 = BitVec.ofNat 64 wp) (h7 : s.gpr .r7 = BitVec.ofNat 64 wq)
    (hwp : 1 ≤ wp) (hwq : 1 ≤ wq) (hpq : wp + wq ≤ w)
    (hp : wv s.mem BX (slot w 4) w = wv s.mem BX (slot w 4) wp)
    (hq : wv s.mem BX (slot w 5) w = wv s.mem BX (slot w 5) wq)
    (h6top : word s.mem BX (slot w 6 + 8 * w) = 0) (h1top : word s.mem BX (slot w 1 + 8 * w) = 0) :
    Crt.PQOk checkPQs BX Z w s := by
  intro t ht t10 t21 t29 t11 tk to
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5
  have e6 := e 6; have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have t5' : t.gpr .r5 = BitVec.ofNat 64 wp := (tk.gpr .r5 (by decide)).trans h5
  have t7' : t.gpr .r7 = BitVec.ofNat 64 wq := (tk.gpr .r7 (by decide)).trans h7
  have O0 : Outside BX (slot w 3) (8 * w) s.mem t.mem := fun x hx => to x hx
  have wv' : ∀ {j}, j ≠ 3 → j < 8 → ∀ k ≤ w, wv t.mem BX (slot w j) k = wv s.mem BX (slot w j) k :=
    fun hj hj' k hk => O0.wv (by have := VG.Proof.Bignum.slot_sep (w := w) hj; omega_arith)
      (by have := VG.Proof.Bignum.slot_le (w := w) hj'; omega_arith)
  unfold checkPQs
  -- Array 6 := 0.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) t10 t29 6) fun u₁ ⟨⟨b14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (ht.congr k1.wr) b14 ((k1.gpr .r11 (by decide)).trans t11)
    (by omega_arith) hw' (by omega_arith)) fun u₂ ⟨⟨_, z2, o2'⟩, k2⟩ => ?_)
  have o2 : Outside BX (slot w 6) (8 * w) u₁.mem u₂.mem := fun x hx => o2' x hx
  have k12 := k1.trans k2
  -- The pointers.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k12.gpr .r10 (by decide)).trans t10)
    ((k12.gpr .r29 (by decide)).trans t29) 4) fun u₃ ⟨⟨b8, m3⟩, k3⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide)
    ((k3.gpr .r10 (by decide)).trans ((k12.gpr .r10 (by decide)).trans t10))
    ((k3.gpr .r29 (by decide)).trans ((k12.gpr .r29 (by decide)).trans t29)) 6) fun u₄ ⟨⟨b9, m4⟩, k4⟩ => ?_
  have k14 := k12.trans (k3.trans k4)
  have m24 : u₄.mem = u₂.mem := by rw [m4, m3]
  -- The rows.
  refine WP.seq (WP.mono (rows_ok (wp := wp) (wq := wq) (ht.congr k14.wr) (by rw [k4.gpr .r8 (by decide), b8])
    b9 ((k14.gpr .r10 (by decide)).trans t10) ((k14.gpr .r29 (by decide)).trans t29)
    ((k14.gpr .r5 (by decide)).trans t5') ((k14.gpr .r7 (by decide)).trans t7') hwp hwq hpq hw' hZ
    (fun k hk => by rw [m24]; exact z2 k hk))
    fun u₅ ⟨⟨r6, o5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  have O : Outside BX (slot w 6) (8 * w) t.mem u₅.mem := by
    rw [m1] at o2
    exact o2.trans (by rw [m24] at o5; exact o5.mono (Nat.le_refl _) (by omega_arith))
  -- `p q = n`?
  refine WP.mono (Crt.pqEq_ok (ht.congr k15.wr) (by omega_arith) hw' hZ ((k15.gpr .r10 (by decide)).trans t10)
    ((k15.gpr .r21 (by decide)).trans t21) ((k15.gpr .r29 (by decide)).trans t29)
    ((k15.gpr .r11 (by decide)).trans t11)
    ((O.word (Or.inr (by omega_arith)) (by omega_arith)).trans
      ((O0.word (Or.inr (by omega_arith)) (by omega_arith)).trans h6top))
    ((O.word (Or.inl (by omega_arith)) (by omega_arith)).trans
      ((O0.word (Or.inl (by omega_arith)) (by omega_arith)).trans h1top)))
    fun u ⟨⟨u26, uo, u10⟩, uk⟩ => ⟨⟨?_, ?_, u10⟩, (k15.trans uk).mono⟩
  · -- The product over `W` words.
    have hz : ∀ k < w - (wp + wq), word u₅.mem BX (slot w 6 + 8 * (wp + wq) + 8 * k) = 0 := fun k hk => by
      rw [o5.word (Or.inr (by omega_arith)) (by omega_arith), m24,
        show slot w 6 + 8 * (wp + wq) + 8 * k = slot w 6 + 8 * (wp + wq + k) by omega_arith]
      exact z2 _ (by omega_arith)
    have hP : wv u₅.mem BX (slot w 6) w = wv s.mem BX (slot w 4) w * wv s.mem BX (slot w 5) w := by
      have a := VG.Proof.Bignum.wv_add u₅.mem BX (slot w 6) (wp + wq) (w - (wp + wq))
      rw [show wp + wq + (w - (wp + wq)) = w by omega_arith, (VG.Proof.Bignum.wv_eq_zero_iff _ _ _ _).mpr hz,
        Nat.mul_zero, Nat.add_zero, r6, m24, o2.wv (Or.inl (by omega_arith)) (by omega_arith),
        o2.wv (Or.inl (by omega_arith)) (by omega_arith), m1,
        wv' (by decide) (by decide) wp (by omega_arith), wv' (by decide) (by decide) wq (by omega_arith)] at a
      rw [a, hp, hq]
    have e6v : Mont.val32 u₅.mem BX (slot w 6) (2 * w) =
        Mont.val32 s.mem BX (slot w 4) (2 * w) * Mont.val32 s.mem BX (slot w 5) (2 * w) := by
      rw [Pre.val32_eq_wv, Pre.val32_eq_wv, Pre.val32_eq_wv, hP]
    have e1v : Mont.val32 u₅.mem BX (slot w 1) (2 * w) = Mont.val32 s.mem BX (slot w 1) (2 * w) := by
      rw [Pre.val32_eq_wv, Pre.val32_eq_wv, O.wv (Or.inl (by omega_arith)) (by omega_arith),
        wv' (by decide) (by decide) w (Nat.le_refl _)]
    rw [u26, e6v, e1v, k15.gpr .r26 (by decide), Crt.bmask_decide]
  · intro x hx
    have hx3 : ofs BX x < slot w 3 ∨ slot w 3 + 8 * w ≤ ofs BX x := by
      have := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)); simp only [Mont.ofs, ofs] at this ⊢
      omega_arith
    have hx6 : ofs BX x < slot w 6 ∨ slot w 6 + 8 * w ≤ ofs BX x := by
      have := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      simp only [Mont.ofs, ofs] at this ⊢; omega_arith
    rw [uo x hx3, O x hx6]

/-! ## The factors' widths -/

/-- `⌈L / 8⌉`, as `PrivPre.pqLens` computes it. -/
theorem len_words (L : Nat) (hL : L < 2 ^ 32) :
    (BitVec.ofNat 64 L + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((L + 7) / 8) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := L) (by omega_arith),
      Nat.mod_eq_of_lt (a := L + 7) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)])

/-- A number of `L` bytes in `w` words is its first `⌈L / 8⌉` words. -/
theorem fit {m : Mem} {B : Addr} {d w L : Nat} {bs : List Byte} (hl : bs.length = L) (hLw : (L + 7) / 8 ≤ w)
    (hv : Mont.val32 m B d (2 * w) = Spec.Rsa.os2ip bs) : wv m B d w = wv m B d ((L + 7) / 8) := by
  rw [Pre.val32_eq_wv] at hv
  have hlt : Spec.Rsa.os2ip bs < 2 ^ (64 * ((L + 7) / 8)) := by
    have := VG.Proof.Bignum.os2ip_lt bs
    rw [hl, VG.Proof.Bignum.pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have a := VG.Proof.Bignum.wv_add m B d ((L + 7) / 8) (w - (L + 7) / 8)
  rw [show (L + 7) / 8 + (w - (L + 7) / 8) = w by omega_arith] at a
  rw [a] at hv ⊢
  have hpos := Nat.two_pow_pos (64 * ((L + 7) / 8))
  rcases Nat.eq_zero_or_pos (wv m B (d + 8 * ((L + 7) / 8)) (w - (L + 7) / 8)) with h | h
  · rw [h, Nat.mul_zero, Nat.add_zero]
  · have := Nat.le_mul_of_pos_right (2 ^ (64 * ((L + 7) / 8))) h; omega_arith

/-- `pqLens`, from the header's lengths `p_len`, `q_len` of `p` and `q`
(arrays 4 and 5, of as many bytes), `⌈p_len / 8⌉ + ⌈q_len / 8⌉ ≤ W`, and the
words `W` of arrays 1 and 6 zero: then `checkPQs` is a check of `p q = n`. -/
theorem pqLens_ok {s : State} {BX : Addr} {Z w pL qL : Nat} {P Qb : List Byte} (hs : Scr s BX Z)
    (hZ : slot w 8 ≤ Z) (hw' : w < 2 ^ 31) (h23 : s.gpr .r23 = BX)
    (hPL : word s.mem BX Crt.oPLen = BitVec.ofNat 64 pL) (hQL : word s.mem BX Crt.oQLen = BitVec.ofNat 64 qL)
    (hp1 : 1 ≤ pL) (hq1 : 1 ≤ qL) (hpL : pL < 2 ^ 32) (hqL : qL < 2 ^ 32)
    (hpq : (pL + 7) / 8 + (qL + 7) / 8 ≤ w) (lP : P.length = pL) (lQ : Qb.length = qL)
    (v4 : Mont.val32 s.mem BX (slot w 4) (2 * w) = Spec.Rsa.os2ip P)
    (v5 : Mont.val32 s.mem BX (slot w 5) (2 * w) = Spec.Rsa.os2ip Qb)
    (t1 : word s.mem BX (slot w 1 + 8 * w) = 0) (t6 : word s.mem BX (slot w 6 + 8 * w) = 0) :
    WP isa (.block pqLens) s fun s₂ => (s₂.mem = s.mem ∧ Crt.PQOk checkPQs BX Z w s₂) ∧ Keep [.r5, .r7] s s₂ := by
  have hnw := hs.nowrap
  have h23' : s.gpr .r23 = off BX 0 := h23.trans (BitVec.add_zero BX).symm
  have rPL : s.mem.readW (off BX 40) 64 = BitVec.ofNat 64 pL := hPL
  have rQL : s.mem.readW (off BX 56) 64 = BitVec.ofNat 64 qL := hQL
  refine WP.mono (WP.keep [.r5, .r7] (Q := fun t => t.gpr .r5 = BitVec.ofNat 64 ((pL + 7) / 8) ∧
      t.gpr .r7 = BitVec.ofNat 64 ((qL + 7) / 8) ∧ t.mem = s.mem) (by
    unfold pqLens
    prun [Crt.oPLen, Crt.oQLen, h23', rPL, rQL, len_words pL hpL, len_words qL hqL,
      hs.ld (show 40 + 8 ≤ Z by unfold slot hdrBytes at hZ; omega_arith),
      hs.ld (show 56 + 8 ≤ Z by unfold slot hdrBytes at hZ; omega_arith)]) (by decide))
    fun t ⟨⟨l5, l7, lm⟩, kl⟩ => ⟨⟨lm, ?_⟩, kl⟩
  rw [← lm] at v4 v5 t1 t6
  exact checkPQs_ok (hs.congr kl.wr) hZ hw' l5 l7 (by omega_arith) (by omega_arith) hpq
    (fit lP (by omega_arith) v4) (fit lQ (by omega_arith) v5) t6 t1

end VG.Proof.Bignum.PPC64LE.PrivPre
