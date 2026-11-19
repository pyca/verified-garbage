module

-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreFront
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseA
public import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPre
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PrivPre
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Rsa

/-! ### `Bignum.PPC64LE.PrivPrePQ`, which this module and modules that import it used -/

section

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
  obtain ha := a.isLt; have hq := q.isLt; have hx := x.isLt; have hc := c.isLt
  obtain hP : a.toNat * q.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  obtain hd := Nat.div_add_mod (a.toNat * q.toNat) (2 ^ 64)
  obtain e0 : (a * q).toNat = a.toNat * q.toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  obtain hhi : a.toNat * q.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
    have := Nat.div_le_div_right (c := 2 ^ 64) hP
    obtain h2 : (2 ^ 64 - 1) * (2 ^ 64 - 1) / 2 ^ 64 = 2 ^ 64 - 2 := by decide
    omega_arith
  rw [e0]
  generalize a.toNat * q.toNat = P at hP hd hhi ⊢
  generalize x.toNat = X at hx ⊢
  generalize c.toNat = C at hc ⊢
  obtain hm := Nat.mod_lt P (show 0 < 2 ^ 64 by decide)
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
  obtain hs' := hs.congr jk.wr
  obtain wT : word t.mem B (dA + 8 * j) = word s.mem B (dA + 8 * j) := jout.word (by omega_arith) (by omega_arith)
  obtain wQ : word t.mem B (dQ + 8 * j) = word s.mem B (dQ + 8 * j) := jout.word (by omega_arith) (by omega_arith)
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
  obtain head : WP isa (.block (([.load .d .r12 .r8 0, .addi .r14 .r9 0] : List Instr) ++
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
  obtain k23 := k2.trans k3
  obtain I0 : RowI s₃ B dA (slot w 5) pw 0 s₃ := ⟨by rw [k3.gpr .r14 (by decide), a14]; rfl,
    by rw [k3.gpr .r15 (by decide), a15]; rfl, by rw [k3.gpr .r12 (by decide), a12], Outside.refl _ _ _ _,
    by simp [VG.Proof.Bignum.wv, a3], Keep.refl _ _⟩
  obtain hs₃ := hs.congr k23.wr
  -- The words.
  refine WP.seq (WP.mono (wp_countdown (cnt := .r16) (N := wq) (by omega_arith) (by omega_arith)
    (RowI s₃ B dA (slot w 5) pw)
    (fun j hj t hI _ => rowWord_ok hs₃ (by omega_arith) hQ (by omega_arith) hj hI) I0 a16)
    fun t ⟨j14, _, _, jout, jv, jk⟩ => ?_)
  obtain k3t := k23.trans jk
  obtain hst := hs.congr k3t.wr
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
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  obtain e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  obtain I0 : RowsI s B w wq 0 s := ⟨by rw [h8]; rfl, by rw [h9]; rfl,
    by rw [Nat.zero_add, (VG.Proof.Bignum.wv_eq_zero_iff _ _ _ _).mpr (fun k hk => hz k (by omega_arith))]
       simp [VG.Proof.Bignum.wv], Outside.refl _ _ _ _, Keep.refl _ _⟩
  refine WP.mono (wp_countdown (cnt := .r5) (N := wp) (by omega_arith) (by omega_arith) (RowsI s B w wq)
    (fun i hi t ⟨j8, j9, jv, jout, jk⟩ _ => ?_) I0 h5) fun t ⟨_, _, tv, tout, tk⟩ => ⟨⟨tv, tout⟩, tk⟩
  obtain hst := hs.congr jk.wr
  refine WP.mono (row_ok (dP := slot w 4) (dA := slot w 6 + 8 * i) (i := i) (wq := wq) hst j8
    (by rw [j9]) ((jk.gpr .r10 (by decide)).trans h10) ((jk.gpr .r29 (by decide)).trans h29)
    ((jk.gpr .r7 (by decide)).trans h7) hwq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith))
    fun t' ⟨⟨rv, rout, r8, r9, r5⟩, rk⟩ => ⟨⟨by rw [r8, show slot w 4 + 8 * i + 8 = slot w 4 + 8 * (i + 1) by omega_arith],
      by rw [r9, show slot w 6 + 8 * i + 8 = slot w 6 + 8 * (i + 1) by omega_arith], ?_, ?_, jk.trans' rk⟩, r5⟩
  · have wP : word t.mem B (slot w 4 + 8 * i) = word s.mem B (slot w 4 + 8 * i) :=
      jout.word (by omega_arith) (by omega_arith)
    obtain wQ : wv t.mem B (slot w 5) wq = wv s.mem B (slot w 5) wq := jout.wv (by omega_arith) (by omega_arith)
    obtain wL : wv t'.mem B (slot w 6) i = wv t.mem B (slot w 6) i := rout.wv (by omega_arith) (by omega_arith)
    obtain a1 := VG.Proof.Bignum.wv_add t'.mem B (slot w 6) i (wq + 1)
    obtain a2 := VG.Proof.Bignum.wv_add t.mem B (slot w 6) i wq
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
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5
  obtain e6 := e 6; have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  obtain t5' : t.gpr .r5 = BitVec.ofNat 64 wp := (tk.gpr .r5 (by decide)).trans h5
  obtain t7' : t.gpr .r7 = BitVec.ofNat 64 wq := (tk.gpr .r7 (by decide)).trans h7
  obtain O0 : Outside BX (slot w 3) (8 * w) s.mem t.mem := fun x hx => to x hx
  obtain wv' : ∀ {j}, j ≠ 3 → j < 8 → ∀ k ≤ w, wv t.mem BX (slot w j) k = wv s.mem BX (slot w j) k :=
    fun hj hj' k hk => O0.wv (by have := VG.Proof.Bignum.slot_sep (w := w) hj; omega_arith)
      (by have := VG.Proof.Bignum.slot_le (w := w) hj'; omega_arith)
  unfold checkPQs
  -- Array 6 := 0.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) t10 t29 6) fun u₁ ⟨⟨b14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (ht.congr k1.wr) b14 ((k1.gpr .r11 (by decide)).trans t11)
    (by omega_arith) hw' (by omega_arith)) fun u₂ ⟨⟨_, z2, o2'⟩, k2⟩ => ?_)
  obtain o2 : Outside BX (slot w 6) (8 * w) u₁.mem u₂.mem := fun x hx => o2' x hx
  obtain k12 := k1.trans k2
  -- The pointers.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k12.gpr .r10 (by decide)).trans t10)
    ((k12.gpr .r29 (by decide)).trans t29) 4) fun u₃ ⟨⟨b8, m3⟩, k3⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide)
    ((k3.gpr .r10 (by decide)).trans ((k12.gpr .r10 (by decide)).trans t10))
    ((k3.gpr .r29 (by decide)).trans ((k12.gpr .r29 (by decide)).trans t29)) 6) fun u₄ ⟨⟨b9, m4⟩, k4⟩ => ?_
  obtain k14 := k12.trans (k3.trans k4)
  obtain m24 : u₄.mem = u₂.mem := by rw [m4, m3]
  -- The rows.
  refine WP.seq (WP.mono (rows_ok (wp := wp) (wq := wq) (ht.congr k14.wr) (by rw [k4.gpr .r8 (by decide), b8])
    b9 ((k14.gpr .r10 (by decide)).trans t10) ((k14.gpr .r29 (by decide)).trans t29)
    ((k14.gpr .r5 (by decide)).trans t5') ((k14.gpr .r7 (by decide)).trans t7') hwp hwq hpq hw' hZ
    (fun k hk => by rw [m24]; exact z2 k hk))
    fun u₅ ⟨⟨r6, o5⟩, k5⟩ => ?_)
  obtain k15 := k14.trans k5
  obtain O : Outside BX (slot w 6) (8 * w) t.mem u₅.mem := by
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
    obtain hz : ∀ k < w - (wp + wq), word u₅.mem BX (slot w 6 + 8 * (wp + wq) + 8 * k) = 0 := fun k hk => by
      rw [o5.word (Or.inr (by omega_arith)) (by omega_arith), m24,
        show slot w 6 + 8 * (wp + wq) + 8 * k = slot w 6 + 8 * (wp + wq + k) by omega_arith]
      exact z2 _ (by omega_arith)
    obtain hP : wv u₅.mem BX (slot w 6) w = wv s.mem BX (slot w 4) w * wv s.mem BX (slot w 5) w := by
      obtain a := VG.Proof.Bignum.wv_add u₅.mem BX (slot w 6) (wp + wq) (w - (wp + wq))
      rw [show wp + wq + (w - (wp + wq)) = w by omega_arith, (VG.Proof.Bignum.wv_eq_zero_iff _ _ _ _).mpr hz,
        Nat.mul_zero, Nat.add_zero, r6, m24, o2.wv (Or.inl (by omega_arith)) (by omega_arith),
        o2.wv (Or.inl (by omega_arith)) (by omega_arith), m1,
        wv' (by decide) (by decide) wp (by omega_arith), wv' (by decide) (by decide) wq (by omega_arith)] at a
      rw [a, hp, hq]
    obtain e6v : Mont.val32 u₅.mem BX (slot w 6) (2 * w) =
        Mont.val32 s.mem BX (slot w 4) (2 * w) * Mont.val32 s.mem BX (slot w 5) (2 * w) := by
      rw [Pre.val32_eq_wv, Pre.val32_eq_wv, Pre.val32_eq_wv, hP]
    obtain e1v : Mont.val32 u₅.mem BX (slot w 1) (2 * w) = Mont.val32 s.mem BX (slot w 1) (2 * w) := by
      rw [Pre.val32_eq_wv, Pre.val32_eq_wv, O.wv (Or.inl (by omega_arith)) (by omega_arith),
        wv' (by decide) (by decide) w (Nat.le_refl _)]
    rw [u26, e6v, e1v, k15.gpr .r26 (by decide), Crt.bmask_decide]
  · intro x hx
    obtain hx3 : ofs BX x < slot w 3 ∨ slot w 3 + 8 * w ≤ ofs BX x := by
      have := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)); simp only [Mont.ofs, ofs] at this ⊢
      omega_arith
    obtain hx6 : ofs BX x < slot w 6 ∨ slot w 6 + 8 * w ≤ ofs BX x := by
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
  obtain hlt : Spec.Rsa.os2ip bs < 2 ^ (64 * ((L + 7) / 8)) := by
    have := VG.Proof.Bignum.os2ip_lt bs
    rw [hl, VG.Proof.Bignum.pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_arith))
  obtain a := VG.Proof.Bignum.wv_add m B d ((L + 7) / 8) (w - (L + 7) / 8)
  rw [show (L + 7) / 8 + (w - (L + 7) / 8) = w by omega_arith] at a
  rw [a] at hv ⊢
  obtain hpos := Nat.two_pow_pos (64 * ((L + 7) / 8))
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
  obtain h23' : s.gpr .r23 = off BX 0 := h23.trans (BitVec.add_zero BX).symm
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

end

end

/-!
# An RSA private key's precomputed values on PPC64LE: the checks

`partA_ok`: from the entry, `save`, `args`, `zeroIn`, `setupX` and
`vg_rsa_private_crt`'s `loadX` and `checksWith`, with `p q = n` checked at
the factors' widths (`pqLens`, `checkPQs`: `pqLens_ok`), with `pre` (its first words
zero) as the input and `qInv`: the mask of `n` valid and `p q = n`
(`privMask`, `crtMask_zero`) in `r26`, and `p` and `q` (or 3) in `X`'s arrays
4 and 5 (`A`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The mask of `vg_rsa_private_precompute`: `n` valid and `p q = n`. -/
def privMask (N k P Q : Nat) : Bool := Spec.Rsa.modulusValid N k && decide (P * Q = N)

/-- With the input and `qInv` zero, the CRT's checks are `n` valid and
`p q = n`. -/
theorem crtMask_zero (N k P Q : Nat) : Crt.crtMask N k 0 P Q 0 = privMask N k P Q := by
  unfold Crt.crtMask privMask
  cases hv : Spec.Rsa.modulusValid N k
  · simp
  · have hN : 2 ^ 511 ≤ N := by
      unfold Spec.Rsa.modulusValid at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
      exact hv.1.1.2
    by_cases h : P * Q = N
    · have hP : 0 < P := Nat.pos_of_ne_zero fun e => by
        rw [e, Nat.zero_mul] at h; have := Nat.one_le_two_pow (n := 511); omega_arith
      simp [h, hP, show 0 < N by omega_arith]
    · simp [h]

/-- The bytes of zero words are zero. -/
theorem os2ip_zero_words {m : Mem} {P : Addr} {w k : Nat} (hz : ∀ i < w, word m P (8 * i) = 0)
    (hk : k ≤ 8 * w) : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m P k) = 0 := by
  obtain hb : ∀ i < k, m (P + BitVec.ofNat 64 i) = 0 := fun i hi => by
    obtain hw := hz (i / 8) (by omega_arith)
    have := Mem.extractLsb'_read m (P + BitVec.ofNat 64 (8 * (i / 8))) (n := 8) (j := i % 8) (Nat.mod_lt _ (by decide))
    simp only [word, off] at hw
    rw [show m.read (P + BitVec.ofNat 64 (8 * (i / 8))) 8 = m.readW (P + BitVec.ofNat 64 (8 * (i / 8))) 64 from rfl, hw,
      Offset.add_add, show 8 * (i / 8) + i % 8 = i by omega_arith] at this
    rw [← this]; exact BitVec.eq_of_toNat_eq (by simp)
  simp only [Spec.Rsa.bytesAt, Spec.Rsa.os2ip]
  suffices ∀ (l : List Nat) (x : Nat), (∀ i ∈ l, i < k) →
      (l.map fun i => m (P + BitVec.ofNat 64 i)).foldl (fun x b => 256 * x + b.toNat) x = 256 ^ l.length * x by
    have := this (List.range k) 0 (fun i hi => List.mem_range.mp hi)
    rw [this, Nat.mul_zero]
  intro l
  induction l with
  | nil => intro x _; simp
  | cons i l ih =>
    intro x hl
    simp only [List.map_cons, List.foldl_cons]
    rw [hb i (hl i (List.mem_cons_self ..)), ih _ fun j hj => hl j (List.mem_cons_of_mem _ hj)]
    rw [List.length_cons, Nat.pow_succ, Nat.mul_assoc]; rfl


/-- `X`'s words. -/
abbrev cwX (s : State) : Nat := 2 * cw s
/-- `p`'s and `q`'s lengths. -/
abbrev cpL (s : State) : Nat := (s.gpr .r8).toNat
abbrev cqL (s : State) : Nat := (s.gpr .r10).toNat
/-- `n`, `p` and `q` as numbers. -/
abbrev cN (s : State) : Nat := Spec.Rsa.os2ip (nB s)
abbrev cP (s : State) : Nat := Spec.Rsa.os2ip (pB s)
abbrev cQ (s : State) : Nat := Spec.Rsa.os2ip (qB s)
/-- The mask. -/
abbrev cb (s : State) : Bool := privMask (cN s) (ck s) (cP s) (cQ s)

/-- The registers written up to the checks. -/
def aRegs : List Reg :=
  [.r11, .r23] ++ [.r0, .r14, .r17, .r11] ++ [.r0, .r3, .r4, .r5, .r10, .r11, .r21, .r27, .r28, .r29] ++
    (Crt.loadXRegs ++ Crt.checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg))

/-- What holds after the checks, from the entry state `s₀`. -/
structure A (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : word s.mem (cS s₀) oOut = s₀.gpr .r3
  hN : word s.mem (cS s₀) oN = s₀.gpr .r5
  hNL : word s.mem (cS s₀) oNLen = s₀.gpr .r6
  hPL : word s.mem (cS s₀) oPLen = s₀.gpr .r8
  hQL : word s.mem (cS s₀) oQLen = s₀.gpr .r10
  hBP : word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : word s.mem (cS s₀) oBQ = off (cS s₀) (slot (cwX s₀) 8 + slot (wsWords (cpL s₀)) 24)
  r23 : s.gpr .r23 = cS s₀
  r26 : s.gpr .r26 = Crt.bmask (cb s₀)
  r27 : s.gpr .r27 = off (cS s₀) (slot (cwX s₀) 0)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  x4 : val32 s.mem (cS s₀) (slot (cwX s₀) 4) (2 * cwX s₀) = if cb s₀ then cP s₀ else 3
  x5 : val32 s.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = if cb s₀ then cQ s₀ else 3
  keep : Keep aRegs s₀ s
  sav : ∀ i < 18, s.mem.readW (off (Crt.savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

/-- What the precondition gives. -/
structure PF (s₀ : State) : Prop where
  k64 : 64 ≤ ck s₀
  k1024 : ck s₀ ≤ 1024
  p1 : 1 ≤ cpL s₀
  pk : cpL s₀ < ck s₀
  q1 : 1 ≤ cqL s₀
  qk : cqL s₀ < ck s₀
  room : slot (cwX s₀) 8 + slot (wsWords (cpL s₀)) 24 + slot (wsWords (cqL s₀)) 24 ≤ cZ s₀
  pq : wsWords (cpL s₀) + wsWords (cqL s₀) ≤ cwX s₀
  nw : (cS s₀).toNat + cZ s₀ ≤ 2 ^ 64
  preLen : (s₀.gpr .r4).toNat = 2 * cw s₀ + wsWords (cpL s₀) + wsWords (cqL s₀)
  pre : Scr s₀ (s₀.gpr .r3) ((s₀.gpr .r4).toNat * 8)
  sepPre : ∀ x, ofs (s₀.gpr .r3) x < (s₀.gpr .r4).toNat * 8 → cZ s₀ ≤ ofs (cS s₀) x
  rN : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r5) i) 1
  sN : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .r5) i ≠ x
  rP : ∀ i < cpL s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r7) i) 1
  sP : ∀ i < cpL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .r7) i ≠ x
  rQ : ∀ i < cqL s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r9) i) 1
  sQ : ∀ i < cqL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .r9) i ≠ x
  rPre : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r3) i) 1
  sPre : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .r3) i ≠ x
  dN : ∀ r ∈ [preR s₀, scrR s₀], (nR s₀).Disjoint r

theorem wsWords_eq (len : Nat) : wsWords len = Spec.Rsa.primeWords len := by
  unfold wsWords Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega_arith

theorem pre_facts {s₀ : State} (h : fnContract.pre s₀) : PF s₀ := by
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords,
    ← wsWords_eq] at hpl
  obtain hk8 : ck s₀ ≤ (s₀.gpr .r4).toNat * 8 := by
    show (s₀.gpr .r6).toNat ≤ _; rw [hpl]; omega_arith
  have dPS' : (⟨s₀.gpr .r3, (s₀.gpr .r4).toNat * 8⟩ : Region).Disjoint ⟨cS s₀, cZ s₀⟩ := dPS
  refine ⟨hk, hk', hp1, hpk, hq1, hqk, ?_, ?_, nwS, hpl,
    Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..) nwPre,
    Pub.sep_of_disjoint dPS',
    Crt.rd_of_mem (by rw [hrd]; exact List.mem_cons_self ..) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dNS (Nat.le_of_lt (BitVec.isLt _)),
    Crt.rd_of_mem (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dpS (Nat.le_of_lt (BitVec.isLt _)),
    Crt.rd_of_mem (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dqS (Nat.le_of_lt (BitVec.isLt _)),
    fun i hi => ⟨preR s₀, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self ..),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun i hi => Pub.ne_of_disjoint dPS' (by omega_arith) i (by omega_arith), fun r hr => ?_⟩
  · show slot (2 * (((s₀.gpr .r6).toNat + 7) / 8)) 8 + slot (wsWords (s₀.gpr .r8).toNat) 24 +
      slot (wsWords (s₀.gpr .r10).toNat) 24 ≤ (stackArg s₀ 1).toNat * 8
    unfold slot wsWords hdrBytes; omega_arith
  · show wsWords (s₀.gpr .r8).toNat + wsWords (s₀.gpr .r10).toNat ≤ 2 * (((s₀.gpr .r6).toNat + 7) / 8)
    unfold wsWords; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dPN.symm
    · exact dNS

/-- A buffer apart from what changed is as it was. -/
theorem bytes_frame {m m' : Mem} {rs : List Region} (F : Frame rs m m') {A : Addr} {L : Nat}
    (hd : ∀ r ∈ rs, (⟨A, L⟩ : Region).Disjoint r) (hL : L ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' A L = Spec.Rsa.bytesAt m A L := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => F.bytes (R := ⟨A, L⟩) hd hL (List.mem_range.mp hi)

theorem saved_ne11 : ∀ i < 18, Crt.saved i ≠ .r11 := by decide

/-- The registers written up to `setupX`. -/
def a0Regs : List Reg := [.r11, .r23] ++ [.r0, .r14, .r17, .r11] ++ [.r0, .r3, .r4, .r5, .r10, .r11, .r21, .r27, .r28, .r29]

/-- What holds after `setupX`, from the entry state `s₀`. -/
structure A0 (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : word s.mem (cS s₀) oOut = s₀.gpr .r3
  hN : word s.mem (cS s₀) oN = s₀.gpr .r5
  hNL : word s.mem (cS s₀) oNLen = s₀.gpr .r6
  hIn : word s.mem (cS s₀) oIn = s₀.gpr .r3
  hP : word s.mem (cS s₀) oP = s₀.gpr .r7
  hPL : word s.mem (cS s₀) oPLen = s₀.gpr .r8
  hQ : word s.mem (cS s₀) oQ = s₀.gpr .r9
  hQL : word s.mem (cS s₀) oQLen = s₀.gpr .r10
  hQI : word s.mem (cS s₀) oQInv = s₀.gpr .r3
  hBP : word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : word s.mem (cS s₀) oBQ = off (cS s₀) (slot (cwX s₀) 8 + slot (wsWords (cpL s₀)) 24)
  r23 : s.gpr .r23 = cS s₀
  r10 : s.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0)
  r21 : s.gpr .r21 = off (cS s₀) (slot (cwX s₀) 0)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  r11 : s.gpr .r11 = BitVec.ofNat 64 (2 * cwX s₀)
  r27 : s.gpr .r27 = off (cS s₀) (slot (cwX s₀) 0)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  keep : Keep a0Regs s₀ s
  sav : ∀ i < 18, s.mem.readW (off (Crt.savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem
  wz : ∀ i < cw s₀, word s.mem (s₀.gpr .r3) (8 * i) = 0

/-- From the entry to `setupX`. -/
theorem partA0_ok {s₀ : State} (h : fnContract.pre s₀) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ x, A0 s₀ x → WP isa c x Q) :
    WP isa (.seq (.block (PrivPre.save ++ PrivPre.args)) (.seq PrivPre.zeroIn (.seq (.block setupX) c))) s₀ Q := by
  have hpre0 := h
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] at hpl
  obtain hscr : Scr s₀ (cS s₀) (cZ s₀) := Scr.of_mem (by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)) nwS
  obtain hpre : Scr s₀ (s₀.gpr .r3) ((s₀.gpr .r4).toNat * 8) := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..) nwPre
  have hn := hscr.nowrap
  obtain hZ : 128 * ck s₀ + 256 ≤ cZ s₀ := by
    show 128 * (s₀.gpr .r6).toNat + 256 ≤ (stackArg s₀ 1).toNat * 8; omega_arith
  obtain hargs : argsR s₀ ∈ s₀.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  obtain hst : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 8 :=
    ⟨_, List.mem_append_left _ hargs, by
      have := Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩
  obtain hsavR : ∀ i < 18, (⟨cS s₀, cZ s₀⟩ : Region).Contains (off (Crt.savW (cS s₀)) (8 * i)) 8 := fun i hi => by
    rw [off, Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s₀ hst fun i hi => ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), hsavR i hi⟩)
    fun t ⟨s₁, a11, m1, k1, hSv⟩ => ?_
  obtain kt := k1.trans hSv.keep
  obtain t23 : t.gpr .r23 = cS s₀ := hSv.r23.trans a11
  obtain fr : Frame [Crt.savR (Crt.savW (cS s₀))] s₀.mem t.mem := by
    have := hSv.frame; rw [a11, m1] at this; exact this
  refine WP.mono (args_ok (hscr.congr kt.wr) (by omega_arith) t23)
    fun u ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, Ou⟩, ku⟩ => ?_
  obtain ktu := kt.trans ku
  -- Changes within the working space or `pre`, as frames.
  obtain frS : ∀ {m m' : Mem} {o n : Nat}, Outside (cS s₀) o n m m' → o + n ≤ cZ s₀ →
      Frame [preR s₀, scrR s₀] m m' := fun {m m' o n} h hon x hx => by
    refine h x ?_
    have := hx (scrR s₀) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only [Region.Contains, ofs, cS, cZ] at this hon ⊢
    omega_arith
  obtain frP : ∀ {m m' : Mem} {o n : Nat}, Outside (s₀.gpr .r3) o n m m' → o + n ≤ (s₀.gpr .r4).toNat * 8 →
      Frame [preR s₀, scrR s₀] m m' := fun {m m' o n} h hon x hx => by
    refine h x ?_
    have := hx (preR s₀) (List.mem_cons_self ..)
    simp only [Region.Contains, ofs] at this ⊢
    omega_arith
  -- The working space's addresses are apart from `pre`'s.
  obtain hPS : ∀ x, Mont.ofs (cS s₀) x < cZ s₀ → (s₀.gpr .r4).toNat * 8 ≤ Mont.ofs (s₀.gpr .r3) x := fun x hx => by
    by_contra hc
    exact dPS x (by simp only [Region.Contains]; simp only [Mont.ofs] at hc; omega_arith)
      (by simp only [Region.Contains]; simp only [Mont.ofs, cS, cZ] at hx; omega_arith)
  obtain F1 : Frame [preR s₀, scrR s₀] s₀.mem u.mem := by
    refine (fr.sub fun r hr => ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (frS Ou (by omega_arith))
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Crt.savR, Crt.savW]
    rw [show cS s₀ + BitVec.ofNat 64 112 = off (cS s₀) 112 from rfl]
    exact Offset.sub_base _ (by omega_arith)
  -- `zeroIn`.
  obtain hw1 : 1 ≤ cw s₀ := by simp only [cw, ck]; omega_arith
  have hcw : cw s₀ = ((s₀.gpr .r6).toNat + 7) / 8 := rfl
  have hcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  refine WP.seq ?_
  obtain u6 : u.gpr .r6 = BitVec.ofNat 64 (ck s₀) := by
    rw [ktu.gpr .r6 (by decide)]; exact (ofNat_toNat64 _).symm
  obtain ⟨K, hK⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  rw [hK] at u6
  have hK' : (s₀.gpr .r6).toNat = K := hK
  refine WP.seq (WP.mono (WP.keep [.r14, .r11] (Q := fun v => v.gpr .r14 = off (s₀.gpr .r3) 0 ∧
      v.gpr .r11 = BitVec.ofNat 64 (2 * cw s₀) ∧ v.mem = u.mem) (by
        prun [ktu.gpr .r3 (by decide), u6, BitVec.add_zero,
          Pre.ofNat_add7_shr3 K (show K < 2 ^ 32 by omega_using [hK', hk']), Pre.ofNat_shl1]
        rw [hcw, hK']) rfl) fun v₁ ⟨⟨z14, z11, zm⟩, zk⟩ => ?_)
  refine WP.mono (zeroWords_ok (hpre.congr (ktu.trans zk).wr) z14 z11 hw1 (by omega_arith) (by omega_arith))
    fun v ⟨⟨_, vz, vo⟩, vk⟩ => ?_
  rw [zm] at vo
  obtain kv := (ktu.trans zk).trans vk
  obtain hhv : ∀ d, d + 8 ≤ cZ s₀ → word v.mem (cS s₀) d = word u.mem (cS s₀) d := fun d hd =>
    Mem.readW_congr fun i hi => vo _ (Or.inr (by
      have := hPS (off (cS s₀) d + BitVec.ofNat 64 i) (by rw [Mont.ofs_off _ (by omega_arith)]; omega_arith)
      omega_arith))
  obtain F2 : Frame [preR s₀, scrR s₀] s₀.mem v.mem := F1.trans (frP vo (by omega_arith))
  -- `setupX`.
  refine WP.seq (WP.mono (Crt.setupX_ok (k := ck s₀) (pL := cpL s₀) (hscr.congr kv.wr) (by omega_arith)
    (((zk.trans vk).gpr _ (by decide)).trans ((ku.gpr _ (by decide)).trans t23))
    (by rw [kv.gpr _ (by decide)]; exact (ofNat_toNat64 _).symm) hk'
    (by rw [hhv _ (by simp only [oPLen]; omega_arith), w5, kt.gpr _ (by decide)]; exact (ofNat_toNat64 _).symm) hp1
    (by show (s₀.gpr .r8).toNat < 2 ^ 60; omega_arith))
    fun x ⟨⟨x10, x21, x29, x11, x27, x28, xBP, xBQ, Ox⟩, kx⟩ => ?_)
  obtain kx' := kv.trans kx
  obtain F3 : Frame [preR s₀, scrR s₀] s₀.mem x.mem := F2.trans (frS Ox (by omega_arith))
  obtain hP := pre_facts hpre0
  obtain hx : ∀ d, d + 8 ≤ 96 → word x.mem (cS s₀) d = word u.mem (cS s₀) d := fun d hd => by
    rw [Ox.word (Or.inl hd) (by omega_arith), hhv d (by omega_arith)]
  refine hc x ⟨hscr.congr kx'.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, xBP, xBQ,
    (kx.gpr _ (by decide)).trans (((zk.trans vk).gpr _ (by decide)).trans ((ku.gpr _ (by decide)).trans t23)),
    x10, x21, x29, x11, x27, x28, kx'.mono (by decide), fun i hi => ?_, F3, fun i hi => ?_⟩
  · rw [hx _ (by decide), w0, kt.gpr _ (by decide)]
  · rw [hx _ (by decide), w1, kt.gpr _ (by decide)]
  · rw [hx _ (by decide), w2, kt.gpr _ (by decide)]
  · rw [hx _ (by decide), w3, kt.gpr _ (by decide)]
  · rw [hx _ (by decide), w4, kt.gpr _ (by decide)]
  · rw [hx _ (by decide), w5, kt.gpr _ (by decide)]
  · rw [hx _ (by decide), w6, kt.gpr _ (by decide)]
  · rw [hx _ (by decide), w7, kt.gpr _ (by decide)]
  · rw [hx _ (by decide), w8, kt.gpr _ (by decide)]
  · have e : Mont.off (Crt.savW (cS s₀)) (8 * i) = Mont.off (cS s₀) (112 + 8 * i) := by
      simp only [Mont.off, Crt.savW]; rw [Offset.add_add]
    obtain h1 := hSv.saved i hi
    rw [a11, k1.gpr _ (fun h => saved_ne11 i hi (List.mem_singleton.mp h))] at h1
    change t.mem.readW (Mont.off (Crt.savW (cS s₀)) (8 * i)) 64 = _ at h1
    change x.mem.readW (Mont.off (Crt.savW (cS s₀)) (8 * i)) 64 = _
    rw [e] at h1 ⊢
    change word x.mem (cS s₀) (112 + 8 * i) = _
    change word t.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [Ox.word (Or.inr (by omega_arith)) (by omega_arith), hhv _ (by omega_arith),
      Ou.word (Or.inr (by omega_arith)) (by omega_arith)]
    exact h1
  · rw [← vz i hi, Nat.zero_add]
    refine Mem.readW_congr fun j hj => Ox _ (Or.inr ?_)
    have := hP.sepPre (off (s₀.gpr .r3) (8 * i) + BitVec.ofNat 64 j) (by
      simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith)
    simp only [ofs, cS, cZ] at this ⊢
    omega_arith

/-- Two programs then two more, regrouped. -/
theorem wp_reassoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q := by
  obtain ⟨t, s', hx, hq⟩ := h
  cases hx with
  | seq h1 h2 =>
    cases h1 with
    | seq ha hbc =>
      cases hbc with
      | seq hb hc => exact ⟨_, _, .seq ha (.seq hb (.seq hc h2)), hq⟩

/-- From the entry to the checks. -/
theorem partA_ok {s₀ : State} (h : fnContract.pre s₀) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ t, A s₀ t → WP isa c t Q) :
    WP isa (.seq (.block (PrivPre.save ++ PrivPre.args)) (.seq PrivPre.zeroIn (.seq (.block setupX)
      (.seq Crt.loadX (.seq (.block PrivPre.pqLens) (.seq (Crt.checksWith PrivPre.checkPQs) c)))))) s₀ Q := by
  have hpre0 := h
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl⟩ := h
  obtain hP := pre_facts hpre0
  have hn := hP.nw
  refine partA0_ok hpre0 fun x X => ?_
  obtain rd0 : x.rd ++ x.wr = s₀.rd ++ s₀.wr := by rw [X.keep.rd, X.keep.wr]
  obtain z : ∀ a : Addr, a = off a 0 := fun a => (BitVec.add_zero a).symm
  obtain e6 : s₀.gpr .r6 = BitVec.ofNat 64 (ck s₀) := (ofNat_toNat64 _).symm
  obtain e8 : s₀.gpr .r8 = BitVec.ofNat 64 (cpL s₀) := (ofNat_toNat64 _).symm
  obtain e10 : s₀.gpr .r10 = BitVec.ofNat 64 (cqL s₀) := (ofNat_toNat64 _).symm
  refine wp_reassoc3 (WP.seq (WP.mono (Crt.phaseAWith_ok (pre := PrivPre.pqLens) (pq := PrivPre.checkPQs) (Na := s₀.gpr .r5) (Pa := s₀.gpr .r7) (Qa := s₀.gpr .r9)
    (Ia := s₀.gpr .r3) (QIa := s₀.gpr .r3) (k := ck s₀) (pL := cpL s₀) (qL := cqL s₀)
    X.scr (by have := hP.room; simp only [cwX, cw] at this; omega_arith) hP.k64 hP.k1024
    X.r23 X.r10 X.r21 X.r29 X.r11
    (by rw [X.hN]; exact z _) (by rw [X.hNL]; exact e6) (by rw [X.hP]; exact z _) (by rw [X.hPL]; exact e8)
    (by rw [X.hQ]; exact z _) (by rw [X.hQL]; exact e10) (by rw [X.hIn]; exact z _) (by rw [X.hQI]; exact z _)
    hP.p1 hP.pk hP.q1 hP.qk
    (by rw [rd0]; exact hP.rN) hP.sN (by rw [rd0]; exact hP.rP) hP.sP (by rw [rd0]; exact hP.rQ) hP.sQ
    (by rw [rd0]; exact hP.rPre) hP.sPre (fun i hi => by rw [rd0]; exact hP.rPre i (by have := hP.pk; omega_arith))
    (fun i hi => hP.sPre i (by have := hP.pk; omega_arith))
    fun s₁ hs₁ h23₁ hd _ _ v4 v5 t1 t6 => pqLens_ok hs₁
      (by have := hP.room; simp (config := { failIfUnchanged := false }) only [cwX, cw, slot, hdrBytes] at this ⊢
          omega_arith)
      (by have := hP.k1024; omega_arith) h23₁ ((hd _ (by decide)).trans (X.hPL.trans e8))
      ((hd _ (by decide)).trans (X.hQL.trans e10)) hP.p1 hP.q1 (by have := hP.pk; have := hP.k1024; omega_arith)
      (by have := hP.qk; have := hP.k1024; omega_arith)
      (by have := hP.pk; have := hP.qk; have := hP.k1024; omega_arith)
      (VG.Proof.Bignum.bytesAt_length _ _ _) (VG.Proof.Bignum.bytesAt_length _ _ _) v4 v5 t1 t6)
    fun y ⟨⟨t26, _, _, v4, v5, _, O1, _⟩, kT⟩ => ?_))
  have room := hP.room
  simp only [cwX, cw] at room
  obtain frS : ∀ {m m' : Mem} {o n : Nat}, Outside (cS s₀) o n m m' → o + n ≤ cZ s₀ →
      Frame [preR s₀, scrR s₀] m m' := fun {m m' o n} h hon x hx => by
    refine h x ?_
    have := hx (scrR s₀) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only [Region.Contains, ofs, cS, cZ] at this hon ⊢
    omega_arith
  obtain F4 : Frame [preR s₀, scrR s₀] s₀.mem y.mem := X.frame.trans (frS O1 (by unfold slot hdrBytes at room ⊢; omega_arith))
  obtain kA := X.keep.trans kT
  obtain dis : ∀ {A : Addr} {L : Nat}, (preR s₀).Disjoint ⟨A, L⟩ → (⟨A, L⟩ : Region).Disjoint (scrR s₀) →
      ∀ r ∈ [preR s₀, scrR s₀], (⟨A, L⟩ : Region).Disjoint r := fun h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h1.symm
    · exact h2
  obtain bN : Spec.Rsa.bytesAt x.mem (s₀.gpr .r5) (ck s₀) = nB s₀ := bytes_frame X.frame (dis dPN dNS) (Nat.le_of_lt (BitVec.isLt _))
  obtain bP : Spec.Rsa.bytesAt x.mem (s₀.gpr .r7) (cpL s₀) = pB s₀ := bytes_frame X.frame (dis dPP dpS) (Nat.le_of_lt (BitVec.isLt _))
  obtain bQ : Spec.Rsa.bytesAt x.mem (s₀.gpr .r9) (cqL s₀) = qB s₀ := bytes_frame X.frame (dis dPQ dqS) (Nat.le_of_lt (BitVec.isLt _))
  have wz := X.wz
  obtain bI : Spec.Rsa.os2ip (Spec.Rsa.bytesAt x.mem (s₀.gpr .r3) (ck s₀)) = 0 :=
    os2ip_zero_words wz (by simp only [cw]; omega_arith)
  obtain bQI : Spec.Rsa.os2ip (Spec.Rsa.bytesAt x.mem (s₀.gpr .r3) (cpL s₀)) = 0 :=
    os2ip_zero_words wz (by simp only [cw]; have := hP.pk; omega_arith)
  rw [bN, bP, bQ, bI, bQI, crtMask_zero] at t26 v4 v5
  obtain ht : ∀ d, d + 8 ≤ 256 → word y.mem (cS s₀) d = word x.mem (cS s₀) d := fun d hd =>
    O1.word (Or.inl hd) (by omega_arith)
  refine hc y ⟨X.scr.congr kT.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, t26, ?_, ?_, v4, v5, kA.mono (by decide), ?_, F4⟩
  · rw [ht _ (by decide), X.hOut]
  · rw [ht _ (by decide), X.hN]
  · rw [ht _ (by decide), X.hNL]
  · rw [ht _ (by decide), X.hPL]
  · rw [ht _ (by decide), X.hQL]
  · rw [ht _ (by decide), X.hBP]
  · rw [ht _ (by decide), X.hBQ]
  · rw [kT.gpr _ (by decide), X.r23]
  · rw [kT.gpr _ (by decide), X.r27]
  · rw [kT.gpr _ (by decide), X.r28]
  · intro i hi
    obtain e : Mont.off (Crt.savW (cS s₀)) (8 * i) = Mont.off (cS s₀) (112 + 8 * i) := by
      simp only [Mont.off, Crt.savW]; rw [Offset.add_add]
    obtain h1 := X.sav i hi
    change x.mem.readW (Mont.off (Crt.savW (cS s₀)) (8 * i)) 64 = _ at h1
    change y.mem.readW (Mont.off (Crt.savW (cS s₀)) (8 * i)) 64 = _
    rw [e] at h1 ⊢
    change word y.mem (cS s₀) (112 + 8 * i) = _
    change word x.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [ht _ (by omega_arith)]
    exact h1

end VG.Proof.Bignum.PPC64LE.PrivPre
