module

-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreFront
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtLoad
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PreFn
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Bignum.RISCV64.PrivPre
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPower
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PrimeR2
import VerifiedGarbage.Proof.Framework.ModArith

/-! ### `Bignum.RISCV64.PrivPreR2`, which the modules that import this one used -/

section

/-!
# An RSA private key's precomputed values on RISC-V: a factor's `R² mod p` from `R_n² mod n`

`r2Fast_ok`: `PrivPre.r2Fast` in a prime's working space (`Win.WCtx`), from
`x`, `X`'s array 6: `1` into array 1, `S := 0`, the steps of the reduction
(`chunkStep1_ok`, with the invariant `S R^i + x_i ≡ 0` for `x_i` the first
`i` chunks of `x`, as `Crt.chunkStep`'s), `-S` (`negS_ok`), then the
doublings (`dblAny_ok`, of any value below `p`) and six Montgomery squares.
The value is `R² mod p` when `x ≡ R_n² = 2^(128 w_n)` modulo `p`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Win

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays)
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp)

/-! ## The doublings, of any value -/

theorem mul_pow_mod_double {x j N : Nat} : 2 * (x * 2 ^ j % N) % N = x * 2 ^ (j + 1) % N := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm 2 (2 ^ j)]

/-- `M` doublings counted by `a1`, of `x < N` in array 1, for `N` in array
0: `x := x 2^M mod N`, changing only arrays 1–3 (as `r2Dbl_ok`). -/
theorem dblAny_ok {s : State} {B : Addr} {Z w N x M : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B (slot w 2)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (h2 : s.gpr .a2 = off B (slot w 1))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hN : wordsVal s.mem B (slot w 0) w = N) (hx : wordsVal s.mem B (slot w 1) w = x) (hxN : x < N)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 M) (hM : 0 < M) (hM' : M < 2 ^ 64) :
    WP isa (.loop (.seq Precompute.doubleMod64 (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)) s fun t =>
      wordsVal t.mem B (slot w 1) w = x * 2 ^ M % N ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep dblLoopRegs s t := by
  have hnw := hs.nowrap
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  obtain hN0 : 0 < N := by omega_using [hxN]
  let Inv : Nat → State → Prop := fun j t =>
    wordsVal t.mem B (slot w 1) w = x * 2 ^ j % N ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep dblLoopRegs s t
  refine wp_countdown (cnt := .a1) (N := M) hM' hM Inv (fun j _ t ⟨tx, to, tk⟩ _ => ?_)
    ⟨by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hxN]; exact hx, Outside.refl _ _ _ _, Keep.refl _ _⟩ h1
  obtain n0 : wordsVal t.mem B (slot w 0) w = N := by rw [Outside.wordsVal to (by omega_using [e0, e1]) (by omega_using [hw', e0, hh]), hN]
  refine WP.seq (WP.mono (doubleMod64_ok (hs.congr tk.2.2) ((tk.gpr (by decide)).trans h5)
    ((tk.gpr (by decide)).trans h6) ((tk.gpr (by decide)).trans h7) ((tk.gpr (by decide)).trans h2)
    ((tk.gpr (by decide)).trans ht0) hw hw' hZ (by rw [tx, n0]; exact Nat.mod_lt _ hN0))
    fun t₁ ⟨d1, od, kd⟩ => ?_)
  refine WP.mono (dec_ok t₁ .a1) fun t₂ e2 => ?_
  subst e2
  refine ⟨⟨?_, by rw [mem_write]; exact Outside.trans to od,
    Keep.trans' tk ((kd.trans (Keep.write _ _ _)).mono (by decide))⟩, ?_⟩
  · rw [mem_write, d1, tx, n0, mul_pow_mod_double]
  · gsimp; rw [kd.gpr (by decide)]

/-! ## `S := S - T mod p` -/

/-- The registers `PrivPre.subST` writes. -/
def subRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `PrivPre.subST`: `S := S - T mod p`, for `S < p` in array 4 and `T < p`
in array 7, changing only arrays 3 and 4. -/
theorem subST_ok {t : State} {B : Addr} {Z w N : Nat} (h : WCtx t B Z w N)
    (hra : t.gpr .ra = off B (slot w 0)) (hS : A t.mem B w 4 < N) (hT : A t.mem B w 7 < N) :
    WP isa PrivPre.subST t fun u =>
      (WCtx u B Z w N ∧ u.gpr .ra = off B (slot w 0) ∧
        A u.mem B w 4 = (A t.mem B w 4 + N - A t.mem B w 7) % N ∧
        (∀ j < 24, j ≠ 3 → j ≠ 4 → A u.mem B w j = A t.mem B w j) ∧ WinO B w t.mem u.mem) ∧
      Keep subRegs t u := by
  have hn := h.nw
  have hw := h.w2
  have hw' := h.w31
  obtain hNR : N < 2 ^ (64 * w) := h.n ▸ wordsVal_lt _ _ _ _
  obtain e24 := slot24 w
  obtain sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  obtain s34 := slot_lt (w := w) (show 3 < 4 by decide)
  obtain s37 := slot_lt (w := w) (show 3 < 7 by decide)
  obtain s03 := slot_lt (w := w) (show 0 < 3 by decide)
  obtain s45 := slot_lt (w := w) (show 4 < 5 by decide)
  obtain s424 := slot_lt (w := w) (show 4 < 24 by decide)
  unfold PrivPre.subST
  -- `S - T` into array 3.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (top0_ok h (j := 4) (by decide)) fun t₇ ⟨m7, k7⟩ => ?_
  obtain ow7 : Outside B (slot w 4) (8 * (w + 1)) t.mem t₇.mem := by
    rw [m7]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)
  obtain c7 := h.of k7 (by decide) (arrO_n ow7 (by omega_arith) (by decide) (by decide))
  obtain u7 : ∀ j < 24, j ≠ 4 → A t₇.mem B w j = A t.mem B w j := fun j hj hne => arr_n ow7 (by omega_arith) hj hne hn
  obtain s7 : A t₇.mem B w 4 = A t.mem B w 4 := by
    rw [m7]; exact Outside.wordsVal (writeW_outside _ _ _ (by omega_arith)) (Or.inl (Nat.le_refl _)) (by omega_arith)
  obtain top7 : Mont.word t₇.mem B (slot w 4 + 8 * w) = 0 := by rw [m7]; exact word_writeW_self _ _ _ _
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) c7.a7 c7.s5 4) fun t₈ ⟨⟨a5, m8⟩, k8⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k8.gpr (by decide)).trans c7.a7)
    ((k8.gpr (by decide)).trans c7.s5) 3) fun t₉ ⟨⟨a6, m9⟩, k9⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a7) (by decide) ((k9.gpr (by decide)).trans ((k8.gpr (by decide)).trans c7.a7))
    ((k9.gpr (by decide)).trans ((k8.gpr (by decide)).trans c7.s5)) 7) fun t₁₀ ⟨⟨a7, m10⟩, k10⟩ => ?_
  obtain hm10 : t₁₀.mem = t₇.mem := by rw [m10, m9, m8]
  obtain k810 := (k8.trans k9).trans k10
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 4) (dT := slot w 3) (dM := slot w 7)
    (c7.scr.congr k810.2.2) ((k10.gpr (by decide)).trans ((k9.gpr (by decide)).trans a5))
    ((k10.gpr (by decide)).trans a6) a7 ((k810.gpr (by decide)).trans c7.t0) (by omega_arith) hw'
    (slot_al w 4) (slot_al w 3) (slot_al w 7) (by have := sl 4 (by decide); omega_arith)
    (by have := sl 3 (by decide); omega_arith) (by have := sl 7 (by decide); omega_arith)
    (Or.inl (by omega_arith)) (Or.inl (by omega_arith))) fun t₁₁ ⟨⟨c, hc, hD, h4⟩, o11, k11⟩ => ?_)
  rw [hm10] at hD h4 o11
  rw [top7] at h4
  obtain k711 := (k7.trans k810).trans k11
  obtain ra11 : t₁₁.gpr .ra = off B (slot w 0) := by rw [k711.gpr (by decide), hra]
  -- `p` added back under the borrow.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.a7] (Q := fun u => u.gpr .a7 = off B (slot w 0) ∧ u.mem = t₁₁.mem)
    (by brun [ra11, BitVec.add_zero]) (by rfl) (by rfl)) fun t₁₂ ⟨⟨b7, m12⟩, k12'⟩ => ?_
  obtain o12 : WinO B w t₇.mem t₁₂.mem := by rw [m12]; exact arrO o11 (by decide) (by decide)
  obtain c12 : WCtx t₁₂ B Z w N := by
    exact c7.of7 ((k810.trans k11).trans k12') (by decide) b7 o12
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c12.a7 c12.s5 3) fun t₁₃ ⟨⟨b3, m13⟩, k13⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k13.gpr (by decide)).trans c12.a7)
    ((k13.gpr (by decide)).trans c12.s5) 0) fun t₁₄ ⟨⟨b4, m14⟩, k14'⟩ => ?_
  obtain k1314 := k13.trans k14'
  obtain hm14 : t₁₄.mem = t₁₂.mem := by rw [m14, m13]
  obtain c14 := c12.regs k1314 (by decide) hm14
  obtain hm : t₁₄.gpr .s4 = if decide (0 < c) then BitVec.allOnes 64 else 0 := by
    rw [k1314.gpr (by decide), k12'.gpr (by decide), h4]; simp
  refine WP.seq (WP.mono (ModArith.addMask64_ok (b := decide (0 < c)) c14.scr ((k14'.gpr (by decide)).trans b3) b4
    c14.t0 hm (slot_al w 3) (slot_al w 0) (by omega_arith) hw' (by have := sl 3 (by decide); omega_arith)
    (by have := sl 0 (by decide); omega_arith) (Or.inr (by omega_arith))) fun t₁₅ ⟨d15, o15, k15⟩ => ?_)
  rw [hm14, m12] at d15
  rw [hm14] at o15
  obtain c15 := c14.of k15 (by decide) (by rw [hm14]; exact arrO o15 (by decide) (by decide))
  -- Back into array 4.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c15.a7 c15.s5 4) fun t₁₆ ⟨⟨d3, m16⟩, k16⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k16.gpr (by decide)).trans c15.a7)
    ((k16.gpr (by decide)).trans c15.s5) 3) fun t₁₇ ⟨⟨d4, m17⟩, k17⟩ => ?_
  obtain k1617 := k16.trans k17
  obtain hm17 : t₁₇.mem = t₁₅.mem := by rw [m17, m16]
  obtain c17 := c15.regs k1617 (by decide) hm17
  refine WP.mono (copySame_ok (dS := slot w 3) (dD := slot w 4) c17.scr d4 ((k17.gpr (by decide)).trans d3)
    c17.t0 (by omega_arith) hw' (slot_al w 3) (slot_al w 4) (by have := sl 3 (by decide); omega_arith)
    (by have := sl 4 (by decide); omega_arith) (Or.inl (by omega_arith))) fun u ⟨⟨c18, o18⟩, k18⟩ => ?_
  rw [hm17] at c18 o18
  obtain cu := c17.of k18 (by decide) (by rw [hm17]; exact arrO o18 (by decide) (by decide))
  obtain kall := (((((k7.trans k810).trans k11).trans k12').trans k1314).trans k15).trans (k1617.trans k18)
  obtain hN11 : wordsVal t₁₁.mem B (slot w 0) w = N := by
    rw [← c7.n]; exact arr_out o11 (by decide) (by decide) hn
  refine ⟨⟨cu, by rw [kall.gpr (by decide), hra], ?_, ?_, ?_⟩, kall.mono (by decide)⟩
  · show wordsVal _ _ _ _ = _
    rw [wv_words c18, d15, hN11]
    simp only [decide_eq_true_eq]
    replace hD : wordsVal t₁₁.mem B (slot w 3) w + A t₇.mem B w 7 = A t₇.mem B w 4 + 2 ^ (64 * w) * c := hD
    rw [u7 7 (by decide) (by decide), s7] at hD
    exact sub_add_mod hS hT hNR (wordsVal_lt _ _ _ _) hc hD
  · intro j hj h3 h4'
    rw [arr_out o18 hj h4' hn, arr_out o15 hj h3 hn, m12, arr_out o11 hj h3 hn, u7 j hj h4']
  · refine (arrO_n ow7 (by omega_arith) (by decide) (by decide)).trans (o12.trans ?_)
    exact ((arrO o15 (by decide) (by decide))).trans (arrO o18 (by decide) (by decide))

/-! ## A step of the reduction -/

/-- `S' ≡ S R⁻¹`, `T ≡ C R⁻¹` and `S R^i + V ≡ 0` give `(S' - T) R^(i+1) + V + R^i C ≡ 0`. -/
theorem chunk1_s {R N S S' T C V i : Nat}
    (hS : (S * R ^ i + V) % N = 0) (hS' : S' * R % N = S * 1 % N) (hT : T * R % N = C * 1 % N) (hTN : T < N) :
    ((S' + N - T) % N * R ^ (i + 1) + (V + R ^ i * C)) % N = 0 := by
  obtain h0 : ((S' + N - T) % N * R ^ (i + 1) + (V + R ^ i * C)) % N =
      ((S' + N - T) * R ^ (i + 1) + (V + R ^ i * C)) % N := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  rw [h0, ← Nat.zero_mod N]
  obtain d1 := VG.ModArith.dvd_sub_of_mod_eq hS'
  obtain d2 := VG.ModArith.dvd_sub_of_mod_eq hT
  obtain d3 := VG.ModArith.dvd_sub_of_mod_eq (show (S * R ^ i + V) % N = 0 % N by rw [hS, Nat.zero_mod])
  refine VG.ModArith.mod_eq_of_dvd_sub ?_
  obtain hle : T ≤ S' + N := by omega_using [hTN]
  obtain e : ((0 : Nat) : Int) - (((S' + N - T) * R ^ (i + 1) + (V + R ^ i * C) : Nat) : Int) =
      ((R ^ i : Nat) : Int) * (((S * 1 : Nat) : Int) - ((S' * R : Nat) : Int)) -
        ((R ^ i : Nat) : Int) * (((C * 1 : Nat) : Int) - ((T * R : Nat) : Int)) +
        (((0 : Nat) : Int) - ((S * R ^ i + V : Nat) : Int)) - (N : Int) * ((R ^ (i + 1) : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.ofNat_sub hle, Int.natCast_zero,
      Int.natCast_one, Int.pow_succ]
    grind
  rw [e]
  exact Int.dvd_sub (Int.dvd_add (Int.dvd_sub (Int.dvd_trans d1 (Int.dvd_mul_left _ _))
    (Int.dvd_trans d2 (Int.dvd_mul_left _ _))) d3) (Int.dvd_mul_right _ _)

/-- Between the steps of the reduction, after `i` of them: in `p`'s working
space at `B` (`N`), 1 in array 1 and `S` in array 4 with
`S R^i + x_i ≡ 0` for `x_i` the first `w i` words of `X`'s array 6 (at
`BX`); the next chunk at `s9`, `K - w i` in `s10`. -/
structure ChunkJ (s : State) (B BX : Addr) (Z w wX K N i : Nat) (t : State) : Prop where
  ctx : WCtx t B Z w N
  ra : t.gpr .ra = off B (slot w 0)
  s9 : t.gpr .s9 = off BX (slot wX 6 + 8 * (w * i))
  s10 : t.gpr .s10 = BitVec.ofNat 64 K - BitVec.ofNat 64 (w * i)
  one : A t.mem B w 1 = 1
  slt : A t.mem B w 4 < N
  sv : (A t.mem B w 4 * (2 ^ (64 * w)) ^ i + wordsVal s.mem BX (slot wX 6) (w * i)) % N = 0
  fix : ∀ j < 24, 7 < j → A t.mem B w j = A s.mem B w j
  out : WinO B w s.mem t.mem
  keep : Keep redRegs s t

/-- One step of the reduction. -/
theorem chunkStep1_ok {s t : State} {B BX : Addr} {Z ZX w wX K N i : Nat} (hx : Scr s BX ZX)
    (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x) (hX : slot wX 6 + 8 * (w * nChunks K w) ≤ ZX)
    (hK : 1 ≤ K) (hK' : K < 2 ^ 40) (hN2 : 2 ≤ N) (hi : i < nChunks K w)
    (I : ChunkJ s B BX Z w wX K N i t) :
    WP isa PrivPre.chunkStep1 t fun u => ChunkJ s B BX Z w wX K N (i + 1) u ∧
      ((u.gpr .t2).toNat ≠ 0 ↔ i + 1 ≠ nChunks K w) := by
  have h := I.ctx
  have hn := h.nw
  have hw := h.w2
  have hw' := h.w31
  obtain hxt := hx.congr I.keep.2.2
  have hxn := hx.nowrap
  obtain hwi : w * i + w ≤ w * nChunks K w := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  obtain sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  unfold PrivPre.chunkStep1
  -- The chunk into array 6, and `s9` past it.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h.a7 h.s5 6) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = t₁.gpr .s9 ∧ u.mem = t₁.mem)
    (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun t₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  obtain hm2 : t₂.mem = t.mem := by rw [m2, m1]
  obtain hx2 := hxt.congr k12.2.2
  refine WP.seq (WP.mono (Pub.copyIn_ok (B := B) (P := BX) (Zp := ZX) (dS := slot wX 6 + 8 * (w * i))
    (dD := slot w 6) (w := w) (h.scr.congr k12.2.2) hxn (fun j hj => hx2.ld (by omega_arith))
    (fun j hj => hx2.al8 (by omega_arith) (by have := slot_al wX 6; omega_arith))
    (by rw [a4, k1.gpr (by decide), I.s9]) ((k2.gpr (by decide)).trans a3) ((k12.gpr (by decide)).trans h.t0)
    (by omega_arith) hw' (slot_al w 6) (by omega_arith) (by have := sl 6 (by decide); omega_arith) hsep)
    fun t₃ ⟨⟨_, a4', c3, o3⟩, k3⟩ => ?_)
  rw [hm2] at c3 o3
  refine WP.seq (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = t₃.gpr .t4 ∧ u.mem = t₃.mem)
    (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun t₄ ⟨⟨a9, m4⟩, k4⟩ => ?_)
  obtain k14 := (k12.trans k3).trans k4
  obtain o4 : Outside B (slot w 6) (8 * w) t.mem t₄.mem := by rw [m4]; exact o3
  obtain c4 := h.of k14 (by decide) (arrO o4 (by decide) (by decide))
  obtain v6 : A t₄.mem B w 6 = wordsVal s.mem BX (slot wX 6 + 8 * (w * i)) w := by
    show wordsVal _ _ _ _ = _
    rw [m4, wv_words c3]
    exact x_wv I.out hsep h.hZ hxn (by omega_arith)
  obtain u4 : ∀ j < 24, j ≠ 6 → A t₄.mem B w j = A t.mem B w j := fun j hj hne => arr_out o4 hj hne hn
  obtain one4 : A t₄.mem B w 1 = 1 := by rw [u4 1 (by decide) (by decide), I.one]
  -- `T := C 1 R⁻¹`.
  refine WP.seq (WP.mono (c4.mont (o := 7) (a := 6) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [one4]; omega_arith))
    fun t₅ ⟨⟨c5, l5, e5, v5, o5⟩, k5⟩ => ?_)
  rw [v6, one4] at e5
  obtain one5 : A t₅.mem B w 1 = 1 := by
    rw [v5 1 (by decide) (by decide) (by decide) (by decide), one4]
  -- `S := S 1 R⁻¹`.
  refine WP.seq (WP.mono (c5.mont (o := 4) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [one5]; omega_arith))
    fun t₆ ⟨⟨c6, l6, e6, v6', o6⟩, k6⟩ => ?_)
  obtain s5' : A t₅.mem B w 4 = A t.mem B w 4 := by
    rw [v5 4 (by decide) (by decide) (by decide) (by decide), u4 4 (by decide) (by decide)]
  rw [one5, s5'] at e6
  obtain T6 : A t₆.mem B w 7 = A t₅.mem B w 7 := v6' 7 (by decide) (by decide) (by decide) (by decide)
  obtain ra6 : t₆.gpr .ra = off B (slot w 0) := by
    rw [k6.gpr (by decide), k5.gpr (by decide), k14.gpr (by decide), I.ra]
  -- `S := S - T mod p`.
  refine WP.seq (WP.mono (subST_ok c6 ra6 l6 (by rw [T6]; exact l5)) fun t₇ ⟨⟨c7, ra7, e7, v7, o7⟩, k7⟩ => ?_)
  -- The count.
  refine WP.mono (WP.keep [.s10, .t2] (Q := fun u => u.gpr .s10 = t₇.gpr .s10 - BitVec.ofNat 64 w ∧
      u.gpr .t2 = (t₇.gpr .s10 - BitVec.ofNat 64 w - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1 ∧
      u.mem = t₇.mem)
    (by brun [c7.t0]) (by rfl) (by rfl)) fun u ⟨⟨f10, f2, mu⟩, kf⟩ => ?_
  obtain cu := c7.regs kf (by decide) mu
  obtain k5f := ((k5.trans k6).trans k7).trans kf
  obtain hwi1 : w * (i + 1) = w * i + w := Nat.mul_succ _ _
  obtain hpow : (2 ^ (64 * w)) ^ i = 2 ^ (64 * (w * i)) := by rw [← Nat.pow_mul, Nat.mul_assoc]
  obtain hU : ∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ 4 → j ≠ 6 → j ≠ 7 → A u.mem B w j = A t.mem B w j := by
    intro j hj h2 h3 h4' h6 h7
    rw [mu, v7 j hj h3 h4', v6' j hj h2 h3 h4', v5 j hj h2 h3 h7, u4 j hj h6]
  refine ⟨⟨cu, by rw [kf.gpr (by decide), ra7], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [k5f.gpr (by decide), a9, a4', hwi1, Nat.mul_add, Nat.add_assoc]
  · rw [f10, ((k5.trans k6).trans k7).gpr (by decide), k14.gpr (by decide), I.s10, sub_flag, hwi1]
  · rw [hU 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I.one]
  · rw [mu, e7]; exact Nat.mod_lt _ (by omega_arith)
  · rw [mu, e7, T6, hwi1, fios_wordsVal_append, ← hpow]
    have := chunk1_s (R := 2 ^ (64 * w)) (N := N) (S := A t.mem B w 4) (S' := A t₆.mem B w 4)
      (T := A t₅.mem B w 7) (C := wordsVal s.mem BX (slot wX 6 + 8 * (w * i)) w)
      (V := wordsVal s.mem BX (slot wX 6) (w * i)) (i := i) I.sv
      (by rw [Nat.mul_one] at e6 ⊢; exact e6) e5 l5
    exact this
  · intro j hj h7
    rw [hU j hj (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
    exact I.fix j hj h7
  · rw [mu]
    exact I.out.trans ((((arrO o4 (by decide) (by decide)).trans o5).trans o6).trans o7)
  · exact Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within I.keep
      k1 (by decide)) k2 (by decide)) k3 (by decide)) k4 (by decide)) k5 (by decide)) k6 (by decide))
      (k7.trans kf) (by decide)
  · rw [f2, flag_ne_zero, ((k5.trans k6).trans k7).gpr (by decide), k14.gpr (by decide), I.s10, sub_flag, ← hwi1]
    exact flag_iff (by omega_arith) hK hK' (by omega_arith) hi

/-! ## `r2Fast` -/

/-- `r2Fast` with `c` in place of its reduction and what follows. -/
abbrev r2FastP (c : Prog isa) : Prog isa :=
  .seq (.block [.addi .t3 .a2 0]) (.seq Precompute.zeroWords
  (.seq (.block ([.li .s0 1, .store .d .s0 .a2 0] ++ base .t3 4)) (.seq Precompute.zeroWords
  (.seq (.block (Crt.xb .s9 6 ++ ([.shift .srl .d .s10 .s11 4, .addi .s10 .s10 (-1)] : List Instr))) c))))

/-- `w` from `X`'s arrays' size `8 (2 w + 2) = 16 (w + 1)`. -/
theorem w_of_s11 {W : Nat} (hW : W < 2 ^ 40) :
    BitVec.ofNat 64 (8 * (2 * W + 2)) >>> 4 - 1#64 = BitVec.ofNat 64 W := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- `r2Fast` up to its reduction: the first step's invariant, for `K = W`, `n`'s words. -/
theorem r2FastA_ok {s : State} {B BX : Addr} {Z ZX w wX W N : Nat} (h : WCtx s B Z w N)
    (hra : s.gpr .ra = off B (slot w 0)) (h2 : s.gpr .a2 = off B (slot w 1))
    (hx : Scr s BX ZX)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hwX : wX = 2 * W) (hW' : W < 2 ^ 40) (hN : 2 ≤ N)
    {c : Prog isa} {Q : State → Prop}
    (hc : ∀ u, ChunkJ s B BX Z w wX W N 0 u → WP isa c u Q) :
    WP isa (r2FastP c) s Q := by
  have hn := h.nw
  have hw := h.w2
  have hw' := h.w31
  have hxn := hx.nowrap
  obtain e24 := slot24 w
  obtain sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  obtain s14 := slot_lt (w := w) (show 1 < 4 by decide)
  obtain s424 := slot_lt (w := w) (show 4 < 24 by decide)
  unfold r2FastP
  -- `x := 1`.
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = off B (slot w 1) ∧ t.mem = s.mem)
    (by brun [h2, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (h.scr.congr k1.2.2) a3 ((k1.gpr (by decide)).trans h.t0) (by omega_arith)
    hw' (slot_al w 1) (by have := sl 1 (by decide); omega_arith)) fun s₂ ⟨⟨_, hz, o2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  obtain hs₂ := h.scr.congr k12.2.2
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.s0] (Q := fun t => t.mem = s₂.mem.writeW (off B (slot w 1)) (BitVec.ofNat 64 1))
    (by brun [Pub.pub_li1, (k12.gpr (by decide)).trans h2, BitVec.add_zero,
      hs₂.st (d := slot w 1) (n := 8) (by have := sl 1 (by decide); omega_arith),
      hs₂.al8 (d := slot w 1) (by have := sl 1 (by decide); omega_arith) (slot_al w 1)])
    (by rfl) (by rfl)) fun s₃ ⟨m3, k3⟩ => ?_
  obtain k13 := k12.trans k3
  obtain x3 : A s₃.mem B w 1 = 1 := by
    rw [m3]; exact Pub.one_word _ _ _ (by omega_arith) (by omega_arith) hz
  obtain o3 : Outside B (slot w 1) (8 * w) s.mem s₃.mem := by
    rw [m3]; rw [m1] at o2
    exact o2.trans ((writeW_outside s₂.mem B (d := slot w 1) _ (by omega_arith)).mono (by omega_arith)
      (by omega_arith))
  obtain c3 := h.of k13 (by decide) (arrO o3 (by decide) (by decide))
  -- `S := 0`.
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c3.a7 c3.s5 4) fun s₄ ⟨⟨d3, m4⟩, k4⟩ => ?_
  refine WP.seq (WP.mono (zeroWords_ok (c3.scr.congr k4.2.2) d3 ((k4.gpr (by decide)).trans c3.t0) (by omega_arith)
    hw' (slot_al w 4) (by have := sl 4 (by decide); omega_arith)) fun s₅ ⟨⟨_, z5, o5⟩, k5⟩ => ?_)
  rw [m4] at o5
  obtain c5 := c3.of (k4.trans k5) (by decide) (arrO o5 (by decide) (by decide))
  obtain v4 : A s₅.mem B w 4 = 0 := wordsVal_zero z5
  obtain u5 : ∀ j < 24, j ≠ 4 → A s₅.mem B w j = A s₃.mem B w j := fun j hj hne => arr_out o5 hj hne hn
  obtain u3 : ∀ j < 24, j ≠ 1 → A s₃.mem B w j = A s.mem B w j := fun j hj hne => arr_out o3 hj hne hn
  -- `s9` and `s10`.
  obtain k15 := (k13.trans k4).trans k5
  obtain o05 : WinO B w s.mem s₅.mem := (arrO o3 (by decide) (by decide)).trans (arrO o5 (by decide) (by decide))
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (xbase_ok (rd := .s9) (by decide) ((k15.gpr (by decide)).trans h6)
    ((k15.gpr (by decide)).trans h11) 6) fun s₆ ⟨⟨a9, m6⟩, k6⟩ => ?_
  refine WP.mono (WP.keep [.s10] (Q := fun u => u.gpr .s10 = BitVec.ofNat 64 W ∧ u.mem = s₆.mem)
    (by
      brun [(k6.gpr (by decide)).trans ((k15.gpr (by decide)).trans h11)]
      rw [hwX, w_of_s11 hW'])
    (by rfl) (by rfl)) fun s₇ ⟨⟨a10, m7⟩, k7⟩ => ?_
  obtain hm7 : s₇.mem = s₅.mem := by rw [m7, m6]
  refine hc s₇ ⟨c5.regs (k6.trans k7) (by decide) hm7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm7]; exact o05, ?_⟩
  · rw [(k6.trans k7).gpr (by decide), k15.gpr (by decide), hra]
  · rw [k7.gpr (by decide), a9, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
  · rw [a10, Nat.mul_zero]; exact (BitVec.sub_zero _).symm
  · rw [hm7, u5 1 (by decide) (by decide), x3]
  · rw [hm7, v4]; omega_arith
  · rw [hm7, v4, Nat.mul_zero]; rfl
  · intro j hj h7
    rw [hm7, u5 j hj (by omega_arith), u3 j hj (by omega_arith)]
  · exact Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within
      (Keep.refl redRegs s) k1 (by decide)) k2 (by decide)) k3 (by decide)) k4 (by decide)) k5 (by decide))
      k6 (by decide)) k7 (by decide)

/-! ## The negation, and the rest -/

/-- `PrivPre.negS`: `S := -S mod p`, for `S < p` in array 4, changing only
arrays 3, 4 and 7. -/
theorem negS_ok {t : State} {B : Addr} {Z w N : Nat} (h : WCtx t B Z w N)
    (hra : t.gpr .ra = off B (slot w 0)) (hS : A t.mem B w 4 < N) :
    WP isa PrivPre.negS t fun u =>
      (WCtx u B Z w N ∧ u.gpr .ra = off B (slot w 0) ∧ A u.mem B w 4 = (0 + N - A t.mem B w 4) % N ∧
        (∀ j < 24, j ≠ 3 → j ≠ 4 → j ≠ 7 → A u.mem B w j = A t.mem B w j) ∧ WinO B w t.mem u.mem) ∧
      Keep subRegs t u := by
  have hn := h.nw
  have hw := h.w2
  have hw' := h.w31
  obtain sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  obtain s47 := slot_lt (w := w) (show 4 < 7 by decide)
  unfold PrivPre.negS
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h.a7 h.s5 7) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h.a7)
    ((k1.gpr (by decide)).trans h.s5) 4) fun t₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  obtain hm2 : t₂.mem = t.mem := by rw [m2, m1]
  obtain c2 := h.regs k12 (by decide) hm2
  refine WP.seq (WP.mono (copySame_ok (dS := slot w 4) (dD := slot w 7) c2.scr a4 ((k2.gpr (by decide)).trans a3)
    c2.t0 (by omega_arith) hw' (slot_al w 4) (slot_al w 7) (by have := sl 4 (by decide); omega_arith)
    (by have := sl 7 (by decide); omega_arith) (Or.inl (by omega_arith))) fun t₃ ⟨⟨c3, o3⟩, k3⟩ => ?_)
  rw [hm2] at c3 o3
  obtain c3' := c2.of k3 (by decide) (by rw [hm2]; exact arrO o3 (by decide) (by decide))
  obtain v7 : A t₃.mem B w 7 = A t.mem B w 4 := by show wordsVal _ _ _ _ = _; rw [wv_words c3]
  obtain u3 : ∀ j < 24, j ≠ 7 → A t₃.mem B w j = A t.mem B w j := fun j hj hne => arr_out o3 hj hne hn
  -- `S := 0`.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .t3) (by decide) c3'.a7 c3'.s5 4) fun t₄ ⟨⟨d3, m4⟩, k4⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (c3'.scr.congr k4.2.2) d3 ((k4.gpr (by decide)).trans c3'.t0) (by omega_arith)
    hw' (slot_al w 4) (by have := sl 4 (by decide); omega_arith)) fun t₅ ⟨⟨_, z5, o5⟩, k5⟩ => ?_)
  rw [m4] at o5
  obtain c5 := c3'.of (k4.trans k5) (by decide) (arrO o5 (by decide) (by decide))
  obtain v4 : A t₅.mem B w 4 = 0 := wordsVal_zero z5
  obtain u5 : ∀ j < 24, j ≠ 4 → A t₅.mem B w j = A t₃.mem B w j := fun j hj hne => arr_out o5 hj hne hn
  obtain k15 := (k12.trans k3).trans ((k4.trans k5))
  refine WP.mono (subST_ok c5 (by rw [k15.gpr (by decide), hra]) (by rw [v4]; omega_arith)
    (by rw [u5 7 (by decide) (by decide), v7]; exact hS)) fun u ⟨⟨cu, rau, eu, vu, ou⟩, ku⟩ => ?_
  refine ⟨⟨cu, rau, by rw [eu, v4, u5 7 (by decide) (by decide), v7], fun j hj h3 h4 h7 => ?_, ?_⟩, ?_⟩
  · rw [vu j hj h3 h4, u5 j hj h4, u3 j hj h7]
  · exact ((arrO o3 (by decide) (by decide)).trans (arrO o5 (by decide) (by decide))).trans ou
  · exact Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.refl subRegs t)
      k1 (by decide)) k2 (by decide)) k3 (by decide)) k4 (by decide)) k5 (by decide)) ku (by decide)

/-- `S R + V ≡ 0`, `Y = -S mod N` and `V ≡ 2^E R` give `Y ≡ 2^E`, for `R`
prime to `N`. -/
theorem neg_val {R N S V Y E : Nat} (hR : Nat.Coprime R N) (hSN : S < N)
    (hS : (S * R + V) % N = 0) (hY : Y = (0 + N - S) % N) (hV : V % N = 2 ^ E * R % N) : Y % N = 2 ^ E % N := by
  refine VG.ModArith.mod_eq_of_mul_mod_eq hR ?_
  obtain hYS : (Y + S) % N = 0 := by
    subst hY
    rcases Nat.eq_zero_or_pos S with rfl | hpos
    · simp
    · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega_using [hSN, hpos] : N - S < N), Nat.sub_add_cancel (by omega_using [hSN]), Nat.mod_self]
  obtain d1 := VG.ModArith.dvd_sub_of_mod_eq (show (Y + S) % N = 0 % N by rw [hYS, Nat.zero_mod])
  obtain d2 := VG.ModArith.dvd_sub_of_mod_eq (show (S * R + V) % N = 0 % N by rw [hS, Nat.zero_mod])
  obtain d3 := VG.ModArith.dvd_sub_of_mod_eq hV
  refine VG.ModArith.mod_eq_of_dvd_sub ?_
  obtain e : (((2 ^ E * R : Nat) : Int) - ((Y * R : Nat) : Int)) =
      ((((2 ^ E * R : Nat) : Int) - (V : Int)) - (((0 : Nat) : Int) - ((S * R + V : Nat) : Int))) +
        (R : Int) * (((0 : Nat) : Int) - ((Y + S : Nat) : Int)) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.natCast_zero]
    grind
  rw [e]
  exact Int.dvd_add (Int.dvd_sub d3 d2) (Int.dvd_trans d1 (Int.dvd_mul_left _ _))

/-- The registers `r2Fast` writes. -/
def r2FRegs : List Reg := redRegs ++ r2PRegs

/-! ## The further reductions -/

/-- `r3 = (a - e) >> 63` is not zero iff `e > a`. -/
theorem gt_flag {a e : Nat} (ha : a < 2 ^ 62) (he : e < 2 ^ 62) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 e) >>> 63).toNat ≠ 0 ↔ a < e := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega_using [ha]), Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega_using [he])]
  constructor
  · intro h
    refine Nat.lt_of_not_le fun hc => h ?_
    rw [show 2 ^ 64 - e + a = (a - e) + 2 ^ 64 by omega_using [ha, hc], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [ha])]
    exact Nat.div_eq_of_lt (by omega_using [ha])
  · intro h
    rw [Nat.mod_eq_of_lt (by omega_using [ha, h])]
    exact Nat.ne_of_gt (Nat.div_pos (by omega_using [he]) (by decide))

theorem gt_bne {a e : Nat} (ha : a < 2 ^ 62) (he : e < 2 ^ 62) :
    (((BitVec.ofNat 64 a - BitVec.ofNat 64 e) >>> 63) != 0) = decide (a < e) := by
  obtain hg := gt_flag ha he
  by_cases h : a < e
  · have hv : (BitVec.ofNat 64 a - BitVec.ofNat 64 e) >>> 63 ≠ 0#64 := fun h' => hg.mpr h (by rw [h']; rfl)
    simp [hv, h]
  · have hv : (BitVec.ofNat 64 a - BitVec.ofNat 64 e) >>> 63 = 0#64 :=
      BitVec.eq_of_toNat_eq (by have := mt hg.mp h; simpa using this)
    simp [hv, h]

theorem nz_bne {c : Nat} (hc : c < 2 ^ 64) : (BitVec.ofNat 64 c != 0) = decide (c ≠ 0) := by
  by_cases h : c = 0
  · subst h; rfl
  · have hv : BitVec.ofNat 64 c ≠ 0#64 := fun he => h (by
      have := congrArg BitVec.toNat he; simpa [Nat.mod_eq_of_lt hc] using this)
    simp [hv, h]

/-- `2 w - e` and the like as words, for `e ≤ 2 w`. -/
theorem sub_ofNat {a b : Nat} (h : b ≤ a) : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

theorem shl_ofNat (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (2 ^ k * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

theorem z_s {R N S S' V m : Nat} (hS : (S * R ^ m + V) % N = 0) (hS' : S' * R % N = S * 1 % N) :
    (S' * R ^ (m + 1) + V) % N = 0 := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm, Nat.add_mod, Nat.mul_mod, hS', ← Nat.mul_mod, Nat.mul_one,
    ← Nat.add_mod, hS]

/-- The further reductions' state after `j` of them, from `t₀`:
`S R^(m + j) + V ≡ 0` and `e - w j` in `s10`. -/
structure ZJ (t₀ : State) (B : Addr) (Z w N m V e j : Nat) (t : State) : Prop where
  ctx : WCtx t B Z w N
  ra : t.gpr .ra = off B (slot w 0)
  one : A t.mem B w 1 = 1
  slt : A t.mem B w 4 < N
  sv : (A t.mem B w 4 * (2 ^ (64 * w)) ^ (m + j) + V) % N = 0
  s10 : t.gpr .s10 = BitVec.ofNat 64 (e - w * j)
  fix : ∀ j < 24, 7 < j → A t.mem B w j = A t₀.mem B w j
  out : WinO B w t₀.mem t.mem
  keep : Keep redRegs t₀ t

/-- The further reductions while more than `2 w` of the `e` words are left:
`Zc` of them. -/
theorem zLoop_ok {t : State} {B : Addr} {Z w N m V e Zc : Nat} (h : WCtx t B Z w N)
    (hra : t.gpr .ra = off B (slot w 0)) (hN2 : 2 ≤ N) (he : e < 2 ^ 40) (hZc : 0 < Zc) (hZe : w * Zc ≤ e)
    (hstep : ∀ j < Zc, (2 * w < e - w * (j + 1) ↔ j + 1 < Zc))
    (h1 : A t.mem B w 1 = 1) (hS : A t.mem B w 4 < N) (hsv : (A t.mem B w 4 * (2 ^ (64 * w)) ^ m + V) % N = 0)
    (h10 : t.gpr .s10 = BitVec.ofNat 64 e) :
    WP isa (.loop PrivPre.zStep (.nonzero .t2)) t (ZJ t B Z w N m V e Zc) := by
  have hw := h.w2
  have hw' := h.w31
  refine count_loop (cr := .t2) hZc (ZJ t B Z w N m V e) (fun j hj u I => ?_)
    ⟨h, hra, h1, hS, by rw [Nat.add_zero]; exact hsv, by rw [h10, Nat.mul_zero, Nat.sub_zero], fun _ _ _ => rfl,
      Outside.refl _ _ _ _, Keep.refl _ _⟩
  unfold PrivPre.zStep
  refine WP.seq (WP.mono (I.ctx.mont (o := 4) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [I.one]; omega_arith))
    fun v ⟨⟨cv, lv, ev, uv, ov⟩, kv⟩ => ?_)
  rw [I.one] at ev
  obtain hmj : w * (j + 1) ≤ e := Nat.le_trans (Nat.mul_le_mul_left _ hj) hZe
  obtain e10 : v.gpr .s10 - BitVec.ofNat 64 w = BitVec.ofNat 64 (e - w * (j + 1)) := by
    rw [kv.gpr (by decide), I.s10, sub_ofNat (by rw [Nat.mul_succ] at hmj; omega_arith)]
    congr 1; rw [Nat.mul_succ]; omega_arith
  refine WP.mono (WP.keep [.s10, .t2] (Q := fun x => x.gpr .s10 = BitVec.ofNat 64 (e - w * (j + 1)) ∧
      x.gpr .t2 = (BitVec.ofNat 64 (2 * w) - BitVec.ofNat 64 (e - w * (j + 1))) >>> 63 ∧ x.mem = v.mem)
    (by
      have t0 := cv.t0
      brun [t0, e10]
      rw [shl_ofNat, Nat.pow_one]) (by rfl) (by rfl)) fun x ⟨⟨x10, x2, xm⟩, kx⟩ => ?_
  refine ⟨⟨cv.regs kx (by decide) xm, by rw [kx.gpr (by decide), kv.gpr (by decide), I.ra],
    by rw [xm, uv 1 (by decide) (by decide) (by decide) (by decide), I.one], by rw [xm]; exact lv,
    by rw [xm, ← Nat.add_assoc]; exact z_s I.sv (by rw [Nat.mul_one] at ev ⊢; exact ev), x10,
    fun j' hj' h7 => by rw [xm, uv j' hj' (by omega_arith) (by omega_arith) (by omega_arith)]; exact I.fix j' hj' h7,
    by rw [xm]; exact I.out.trans ov, Keep.within (Keep.within I.keep kv (by decide)) kx (by decide)⟩, ?_⟩
  rw [x2]
  have := (gt_flag (a := 2 * w) (e := e - w * (j + 1)) (by omega_arith) (by omega_arith)).trans (hstep j hj)
  exact this.trans ⟨Nat.ne_of_lt, fun h' => Nat.lt_of_le_of_ne hj h'⟩

/-! ## The tail -/

theorem sq_pow {R N x y a : Nat} (hR : Nat.Coprime R N) (hx : x % N = 2 ^ a * R % N)
    (hy : y * R % N = x * x % N) : y % N = 2 ^ (2 * a) * R % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [hy, Nat.mul_mod, hx, ← Nat.mul_mod, Nat.two_mul, Nat.pow_add]
  congr 1
  grind

/-- Six squares (`s7 := 6`, `sqrOp 1 1 4`): `2^w R` to `2^(64 w) R = R² mod N`, under `G`. -/
theorem sq6R_ok {u s : State} {B : Addr} {Z w N : Nat} {G : Prop} (c : WCtx u B Z w N) (hodd : N % 2 = 1)
    (hra : u.gpr .ra = off B (slot w 0)) (hl : A u.mem B w 1 < N)
    (hx : G → A u.mem B w 1 % N = 2 ^ w * 2 ^ (64 * w) % N) (hfix : ∀ j < 24, 7 < j → A u.mem B w j = A s.mem B w j)
    (ho : WinO B w s.mem u.mem) (hk : Keep r2FRegs s u) :
    WP isa (.seq (.block [.li .s7 6]) (.loop (.seq (ModExp.sqrOp 1 1 4) (.block [.addi .s7 .s7 (-1)])) (.nonzero .s7)))
      u fun t =>
      (WCtx t B Z w N ∧ t.gpr .ra = off B (slot w 0) ∧ A t.mem B w 1 < N ∧
        (G → A t.mem B w 1 = 2 ^ (128 * w) % N) ∧
        (∀ j < 24, 7 < j → A t.mem B w j = A s.mem B w j) ∧ WinO B w s.mem t.mem) ∧ Keep r2FRegs s t := by
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  obtain hra' : s.gpr .ra = off B (slot w 0) := (hk.gpr (by decide)).symm.trans hra
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun x => x.gpr .s7 = BitVec.ofNat 64 6 ∧ x.mem = u.mem)
    (by brun [exec_li6]) (by rfl) (by rfl)) fun t₁₀ ⟨⟨a7, m10⟩, k10⟩ => ?_)
  let Inv : Nat → State → Prop := fun j x =>
    WCtx x B Z w N ∧ A x.mem B w 1 < N ∧ (G → A x.mem B w 1 % N = 2 ^ (w * 2 ^ j) * 2 ^ (64 * w) % N) ∧
      (∀ j < 24, 7 < j → A x.mem B w j = A s.mem B w j) ∧ WinO B w s.mem x.mem ∧ Keep r2FRegs s x
  refine WP.mono (wp_countdown (cnt := .s7) (N := 6) (by decide) (by decide) Inv
    (fun j _ x ⟨cu, lu, xu, fu, ou, ku⟩ _ => ?_)
    ⟨c.regs k10 (by decide) m10, by rw [m10]; exact hl, fun g => by rw [m10, Nat.pow_zero, Nat.mul_one]; exact hx g,
      fun j hj h7 => by rw [m10]; exact hfix j hj h7, by rw [m10]; exact ho,
      Keep.within hk k10 (by decide)⟩ a7) fun t' ⟨ct, lt, xt, ft, ot, kt⟩ => ?_
  · refine WP.seq (WP.mono (cu.sqr (o := 1) (a := 1) (p := 4) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) lu)
      fun u₁ ⟨⟨c1', l1, e1', v1', o1'⟩, k1'⟩ => ?_)
    refine WP.mono (dec_ok u₁ .s7) fun u₂ e2 => ?_
    subst e2
    obtain he : w * 2 ^ (j + 1) = 2 * (w * 2 ^ j) := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2]
    refine ⟨⟨c1'.regs (Keep.write _ _ _) (by decide) (by rw [mem_write]), by rw [mem_write]; exact l1, ?_, ?_,
      by rw [mem_write]; exact ou.trans o1', Keep.trans' ku ((k1'.trans (Keep.write _ _ _)).mono (by decide))⟩, ?_⟩
    · intro g
      rw [mem_write, he]
      exact sq_pow hR (xu g) e1'
    · intro j' hj' h7
      rw [mem_write, v1' j' hj' (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
      exact fu j' hj' h7
    · gsimp; rw [k1'.gpr (by decide)]
  · refine ⟨⟨ct, by rw [kt.gpr (by decide), hra'], lt, fun g => ?_, ft, ot⟩, kt⟩
    obtain h6' : w * 2 ^ 6 = 64 * w := by rw [show (2 : Nat) ^ 6 = 64 from rfl, Nat.mul_comm]
    rw [← Nat.mod_eq_of_lt lt, xt g, h6', ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega_arith]

theorem r2Fast_eq : PrivPre.r2Fast = r2FastP (.seq (.loop PrivPre.chunkStep1 (.nonzero .t2))
    (.seq (.block [.shift .srl .d .t2 .s11 4, .addi .t2 .t2 (-1), .add .s10 .s10 .t2, .shift .sll .d .t2 .t0 1,
      .sub .t2 .t2 .s10, .shift .srl .d .t2 .t2 63])
    (.seq (.ite (.nonzero .t2) (.loop PrivPre.zStep (.nonzero .t2)) (.block []))
    (.seq PrivPre.negS
    (.seq (.block (base .t3 1 ++ base .t4 4)) (.seq Crt.copyN
    (.seq (.block (base .a2 1 ++ base .a5 2 ++ base .a6 3 ++ ([.sub .t2 .t0 .s10, .shift .srl .d .t2 .t2 63] : List Instr)))
      (.ite (.nonzero .t2)
        (.seq (.block [.shift .sll .d .a1 .t0 1, .sub .a1 .a1 .s10, .shift .sll .d .a1 .a1 6])
          (.ite (.nonzero .a1) PrivPre.dblLoop (.block [])))
        (.seq (.block [.sub .a1 .t0 .s10, .shift .sll .d .a1 .a1 6, .add .a1 .a1 .t0]) (.seq PrivPre.dblLoop
          (.seq (.block [.li .s7 6])
            (.loop (.seq (ModExp.sqrOp 1 1 4) (.block [.addi .s7 .s7 (-1)])) (.nonzero .s7))))))))))))) := rfl

/-- `r2Fast`'s tail, from `Y = -S` in array 1, `Y ≡ 2^(64 E)` under `G`:
the doublings to `2^(128 w)` if `w < E`, else to `2^(64 w + w)` and six squares. -/
theorem r2Tail_ok {s u : State} {B : Addr} {Z w N E : Nat} {G : Prop} (c : WCtx u B Z w N) (hodd : N % 2 = 1)
    (hN : 2 ≤ N) (hra : u.gpr .ra = off B (slot w 0)) (h10 : u.gpr .s10 = BitVec.ofNat 64 E) (hE2 : E ≤ 2 * w)
    (hl : A u.mem B w 1 < N) (hx : G → A u.mem B w 1 % N = 2 ^ (64 * E) % N)
    (hfix : ∀ j < 24, 7 < j → A u.mem B w j = A s.mem B w j)
    (ho : WinO B w s.mem u.mem) (hk : Keep r2FRegs s u) :
    WP isa (.seq (.block (base .a2 1 ++ base .a5 2 ++ base .a6 3 ++
        ([.sub .t2 .t0 .s10, .shift .srl .d .t2 .t2 63] : List Instr)))
      (.ite (.nonzero .t2)
        (.seq (.block [.shift .sll .d .a1 .t0 1, .sub .a1 .a1 .s10, .shift .sll .d .a1 .a1 6])
          (.ite (.nonzero .a1) PrivPre.dblLoop (.block [])))
        (.seq (.block [.sub .a1 .t0 .s10, .shift .sll .d .a1 .a1 6, .add .a1 .a1 .t0]) (.seq PrivPre.dblLoop
          (.seq (.block [.li .s7 6])
            (.loop (.seq (ModExp.sqrOp 1 1 4) (.block [.addi .s7 .s7 (-1)])) (.nonzero .s7))))))) u fun t =>
      (WCtx t B Z w N ∧ t.gpr .ra = off B (slot w 0) ∧ A t.mem B w 1 < N ∧
        (G → A t.mem B w 1 = 2 ^ (128 * w) % N) ∧
        (∀ j < 24, 7 < j → A t.mem B w j = A s.mem B w j) ∧ WinO B w s.mem t.mem) ∧ Keep r2FRegs s t := by
  have hn := c.nw
  have hw := c.w2
  have hw' := c.w31
  obtain sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => c.sl hj
  obtain hN0 : 0 < N := by omega_arith
  -- The bases, and whether `w < E`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) c.a7 c.s5 1) fun t₅ ⟨⟨b2, m5⟩, k5⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k5.gpr (by decide)).trans c.a7)
    ((k5.gpr (by decide)).trans c.s5) 2) fun t₆ ⟨⟨b5, m6⟩, k6⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) (((k5.trans k6).gpr (by decide)).trans c.a7)
    (((k5.trans k6).gpr (by decide)).trans c.s5) 3) fun t₇ ⟨⟨b6, m7⟩, k7⟩ => ?_
  obtain k57 := (k5.trans k6).trans k7
  refine WP.mono (WP.keep [.t2] (Q := fun v =>
      v.gpr .t2 = (BitVec.ofNat 64 w - BitVec.ofNat 64 E) >>> 63 ∧ v.mem = t₇.mem)
    (by brun [(k57.gpr (by decide)).trans h10, (k57.gpr (by decide)).trans c.t0]) (by rfl) (by rfl))
    fun t₈ ⟨⟨f2, m8⟩, k8⟩ => ?_
  obtain hm8 : t₈.mem = u.mem := by rw [m8, m7, m6, m5]
  obtain k58 := k57.trans k8
  obtain c8 := c.regs k58 (by decide) hm8
  obtain a2' : t₈.gpr .a2 = off B (slot w 1) :=
    (k8.gpr (by decide)).trans ((k7.gpr (by decide)).trans ((k6.gpr (by decide)).trans b2))
  obtain a5' : t₈.gpr .a5 = off B (slot w 2) := (k8.gpr (by decide)).trans ((k7.gpr (by decide)).trans b5)
  obtain a6' : t₈.gpr .a6 = off B (slot w 3) := (k8.gpr (by decide)).trans b6
  obtain ra8 : t₈.gpr .ra = off B (slot w 0) := (k58.gpr (by decide)).trans hra
  obtain h10' : t₈.gpr .s10 = BitVec.ofNat 64 E := (k58.gpr (by decide)).trans h10
  obtain k8' : Keep r2FRegs s t₈ := Keep.within hk k58 (by decide)
  obtain hl8 : A t₈.mem B w 1 < N := by rw [hm8]; exact hl
  obtain hx8 : G → A t₈.mem B w 1 % N = 2 ^ (64 * E) % N := by rw [hm8]; exact hx
  obtain fix8 : ∀ j < 24, 7 < j → A t₈.mem B w j = A s.mem B w j := fun j hj h7 => by rw [hm8]; exact hfix j hj h7
  obtain o8 : WinO B w s.mem t₈.mem := by rw [hm8]; exact ho
  -- `M` doublings of `Y`.
  obtain dbl : ∀ (v : State) (M : Nat), WCtx v B Z w N → v.mem = t₈.mem → Keep r2FRegs s v →
      v.gpr .a1 = BitVec.ofNat 64 M → 0 < M → M < 2 ^ 64 → v.gpr .a2 = off B (slot w 1) →
      v.gpr .a5 = off B (slot w 2) → v.gpr .a6 = off B (slot w 3) → v.gpr .ra = off B (slot w 0) →
      WP isa PrivPre.dblLoop v fun t => (WCtx t B Z w N ∧ t.gpr .ra = off B (slot w 0) ∧
        A t.mem B w 1 = A t₈.mem B w 1 * 2 ^ M % N ∧
        (∀ j < 24, 7 < j → A t.mem B w j = A s.mem B w j) ∧ WinO B w s.mem t.mem) ∧ Keep r2FRegs s t := by
    intro v M cv mv kv d1 hM hM' v2 v5 v6 vra
    refine WP.mono (dblAny_ok (x := A t₈.mem B w 1) cv.scr v5 v6 cv.a7 v2 cv.t0 (by omega_arith) hw'
      (by have := sl 3 (by decide); have := slot_lt (w := w) (show 3 < 4 by decide); unfold slot at *; omega_arith)
      cv.n (by rw [mv]) hl8 d1 hM hM') fun t ⟨x9, o9, k9⟩ => ?_
    obtain O9 : WinO B w v.mem t.mem := o9.mono (Nat.le_refl _) (by omega_arith)
    refine ⟨⟨cv.of k9 (by decide) O9, by rw [k9.gpr (by decide), vra], x9, fun j hj h7 => ?_,
      by rw [← mv] at o8; exact o8.trans O9⟩, Keep.within kv k9 (by decide)⟩
    have := slot_lt (w := w) hj
    have es : slot w j = hdrBytes + j * (8 * (w + 2)) := rfl
    obtain es1 : slot w 1 = hdrBytes + 8 * (w + 2) := by unfold slot; omega_arith
    obtain h8 := Nat.mul_le_mul_right (8 * (w + 2)) (show 8 ≤ j by omega_arith)
    rw [show A t.mem B w j = A v.mem B w j from
      Outside.wordsVal o9 (Or.inr (by omega_arith)) (by omega_arith), mv]
    exact fix8 j hj h7
  refine WP.ite (decide (w < E)) (by rw [Steps.eval_nonzero, f2, gt_bne (by omega_arith) (by omega_arith)])
    (fun hb => ?_) (fun hb => ?_)
  · -- `64 (2 w - E)` doublings.
    obtain hwE : w < E := of_decide_eq_true hb
    refine WP.seq (WP.mono (WP.keep [.a1] (Q := fun v =>
        v.gpr .a1 = BitVec.ofNat 64 (64 * (2 * w - E)) ∧ v.mem = t₈.mem)
      (by
        brun [c8.t0, h10']
        rw [shl_ofNat, Nat.pow_one, sub_ofNat (by omega_arith), shl_ofNat]) (by rfl) (by rfl)) fun t₉ ⟨⟨d1, m9⟩, k9⟩ => ?_)
    obtain c9 := c8.regs k9 (by decide) m9
    obtain k9' : Keep r2FRegs s t₉ := Keep.within k8' k9 (by decide)
    obtain hexp : 64 * E + 64 * (2 * w - E) = 128 * w := by omega_arith
    refine WP.ite (decide (64 * (2 * w - E) ≠ 0)) (by rw [Steps.eval_nonzero, d1, nz_bne (by omega_arith)])
      (fun hz => ?_) (fun hz => ?_)
    · refine WP.mono (dbl t₉ _ c9 m9 k9' d1 (Nat.pos_of_ne_zero (of_decide_eq_true hz)) (by omega_arith)
        ((k9.gpr (by decide)).trans a2') ((k9.gpr (by decide)).trans a5') ((k9.gpr (by decide)).trans a6')
        ((k9.gpr (by decide)).trans ra8)) fun t ⟨⟨ct, rt, xt, ft, ot⟩, kt⟩ =>
        ⟨⟨ct, rt, by rw [xt]; exact Nat.mod_lt _ hN0, fun g => ?_, ft, ot⟩, kt⟩
      rw [xt, Nat.mul_mod, hx8 g, ← Nat.mul_mod, ← Nat.pow_add, hexp]
    · have hE : E = 2 * w := by have := of_decide_eq_false hz; omega_arith
      refine WP.block_nil ⟨⟨c9, (k9.gpr (by decide)).trans ra8, by rw [m9]; exact hl8, fun g => ?_,
        fun j hj h7 => by rw [m9]; exact fix8 j hj h7, by rw [m9]; exact o8⟩, k9'⟩
      rw [m9, ← Nat.mod_eq_of_lt hl8, hx8 g, hE, show 64 * (2 * w) = 128 * w by omega_arith]
  · -- `64 (w - E) + w` doublings, then six squares.
    obtain hEw : E ≤ w := by have := of_decide_eq_false hb; omega_arith
    refine WP.seq (WP.mono (WP.keep [.a1] (Q := fun v =>
        v.gpr .a1 = BitVec.ofNat 64 (64 * (w - E) + w) ∧ v.mem = t₈.mem)
      (by
        brun [c8.t0, h10']
        rw [sub_ofNat hEw, shl_ofNat, BitVec.ofNat_add_ofNat]) (by rfl) (by rfl)) fun t₉ ⟨⟨d1, m9⟩, k9⟩ => ?_)
    obtain c9 := c8.regs k9 (by decide) m9
    obtain k9' : Keep r2FRegs s t₉ := Keep.within k8' k9 (by decide)
    refine WP.seq (WP.mono (dbl t₉ _ c9 m9 k9' d1 (by omega_arith) (by omega_arith)
      ((k9.gpr (by decide)).trans a2') ((k9.gpr (by decide)).trans a5') ((k9.gpr (by decide)).trans a6')
      ((k9.gpr (by decide)).trans ra8)) fun t ⟨⟨ct, rt, xt, ft, ot⟩, kt⟩ => ?_)
    refine sq6R_ok ct hodd rt (by rw [xt]; exact Nat.mod_lt _ hN0) (fun g => ?_) ft ot kt
    rw [xt, Nat.mod_mod, Nat.mul_mod, hx8 g, ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_add,
      show 64 * E + (64 * (w - E) + w) = w + 64 * w by omega_arith]

/-- `(W - b) + W = 2 W - b` as words, for `b ≤ 2 W`. -/
theorem e0_word {W b : Nat} (hb : b ≤ 2 * W) :
    BitVec.ofNat 64 W - BitVec.ofNat 64 b + BitVec.ofNat 64 W = BitVec.ofNat 64 (2 * W - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- `PrivPre.r2Fast`: `R² mod N` in array 1 if `x`, the `w ⌈W / w⌉` words of
`X`'s array 6, is `2^(128 W)` modulo `N` (`G`). -/
theorem r2Fast_ok {s : State} {B BX : Addr} {Z ZX w wX W N : Nat} (h : WCtx s B Z w N)
    (hra : s.gpr .ra = off B (slot w 0)) (h2 : s.gpr .a2 = off B (slot w 1))
    (hx : Scr s BX ZX) (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hwX : wX = 2 * W) (hW' : W < 2 ^ 40) (hwW : w ≤ W)
    (hXZ : slot wX 6 + 8 * (w * nChunks W w) ≤ ZX) (hN : 2 ≤ N) (hodd : N % 2 = 1)
    {G : Prop} (hG : G → wordsVal s.mem BX (slot wX 6) (w * nChunks W w) % N = 2 ^ (128 * W) % N) :
    WP isa PrivPre.r2Fast s fun t =>
      (WCtx t B Z w N ∧ t.gpr .ra = off B (slot w 0) ∧ A t.mem B w 1 < N ∧
        (G → A t.mem B w 1 = 2 ^ (128 * w) % N) ∧
        (∀ j < 24, 7 < j → A t.mem B w j = A s.mem B w j) ∧ WinO B w s.mem t.mem) ∧ Keep r2FRegs s t := by
  have hn := h.nw
  have hw := h.w2
  have hw' := h.w31
  obtain sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  obtain hN0 : 0 < N := by omega_arith
  obtain hw1 : 1 ≤ w := by omega_arith
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  obtain ⟨hE1, hE2, hEs⟩ := VG.Proof.Bignum.r2E_spec (w := W) (wx := w) hw1 hwW
  rw [r2Fast_eq]
  refine r2FastA_ok h hra h2 hx h6 h11 hwX hW' hN fun u I0 => ?_
  obtain hK1 : 1 ≤ W := by omega_arith
  obtain hc0 : 0 < nChunks W w := nChunks_pos hw1 hK1
  obtain hKn : W ≤ w * nChunks W w := by
    have := le_nChunks_mul (K := W) (w := w) hw1; rw [Nat.mul_comm]; exact this
  obtain hnK : w * nChunks W w < W + w := by
    have := nChunks_mul_lt (K := W) (w := w) hw1 hK1; rw [Nat.mul_comm]; exact this
  -- The reduction by `x`'s chunks.
  refine WP.seq (WP.mono (count_loop (cr := .t2) hc0 (fun j u => ChunkJ s B BX Z w wX W N j u)
    (fun j hj u I => chunkStep1_ok hx hsep hXZ hK1 hW' hN hj I) I0) fun t I => ?_)
  obtain he0 : VG.Proof.Bignum.r2E0 W w = 2 * W - w * nChunks W w := by
    unfold VG.Proof.Bignum.r2E0; rw [Nat.mul_comm w]
  obtain hZE : VG.Proof.Bignum.r2E W w = VG.Proof.Bignum.r2E0 W w - w * VG.Proof.Bignum.r2Z W w := by
    unfold VG.Proof.Bignum.r2E; rw [Nat.mul_comm w]
  obtain hZe : w * VG.Proof.Bignum.r2Z W w ≤ VG.Proof.Bignum.r2E0 W w := by omega_arith
  obtain hstep : ∀ j < VG.Proof.Bignum.r2Z W w,
      (2 * w < VG.Proof.Bignum.r2E0 W w - w * (j + 1) ↔ j + 1 < VG.Proof.Bignum.r2Z W w) := fun j hj => by
    rw [Nat.mul_comm w]; exact VG.Proof.Bignum.r2Z_step hw1 hj
  have hEs' : (nChunks W w + VG.Proof.Bignum.r2Z W w) * w + VG.Proof.Bignum.r2E W w = 2 * W := hEs
  generalize hnc : nChunks W w = n at I hXZ hG hKn hnK he0 hEs'
  generalize hE0 : VG.Proof.Bignum.r2E0 W w = e0 at he0 hZE hZe hstep
  -- `e₀`, and whether further reductions follow.
  obtain h11t : t.gpr .s11 = BitVec.ofNat 64 (8 * (2 * W + 2)) := by
    rw [← hwX]; exact (I.keep.gpr (by decide)).trans h11
  refine WP.seq (WP.mono (WP.keep [.t2, .s10] (Q := fun v => v.gpr .s10 = BitVec.ofNat 64 e0 ∧
      v.gpr .t2 = (BitVec.ofNat 64 (2 * w) - BitVec.ofNat 64 e0) >>> 63 ∧ v.mem = t.mem)
    (by
      brun [I.s10, h11t, I.ctx.t0]
      refine ⟨?_, ?_⟩
      · rw [w_of_s11 hW', e0_word (by omega_arith), he0]
      · rw [w_of_s11 hW', e0_word (by omega_arith), he0, shl_ofNat, Nat.pow_one])
    (by rfl) (by rfl)) fun t₁ ⟨⟨e10, f2, m1⟩, k1⟩ => ?_)
  obtain c1 := I.ctx.regs k1 (by decide) m1
  obtain ra1 : t₁.gpr .ra = off B (slot w 0) := (k1.gpr (by decide)).trans I.ra
  obtain one1 : A t₁.mem B w 1 = 1 := by rw [m1]; exact I.one
  obtain slt1 : A t₁.mem B w 4 < N := by rw [m1]; exact I.slt
  obtain sv1 : (A t₁.mem B w 4 * (2 ^ (64 * w)) ^ n + wordsVal s.mem BX (slot wX 6) (w * n)) % N = 0 := by
    rw [m1]; exact I.sv
  obtain hz : WP isa (.ite (.nonzero .t2) (.loop PrivPre.zStep (.nonzero .t2)) (.block [])) t₁
      (ZJ t₁ B Z w N n (wordsVal s.mem BX (slot wX 6) (w * n)) e0 (VG.Proof.Bignum.r2Z W w)) := by
    refine WP.ite (decide (2 * w < e0)) (by rw [Steps.eval_nonzero, f2, gt_bne (by omega_arith) (by omega_arith)])
      (fun hb => ?_) (fun hb => ?_)
    · exact zLoop_ok c1 ra1 hN (by omega_arith)
        ((VG.Proof.Bignum.r2Z_pos hw1).mpr (by rw [hE0]; exact of_decide_eq_true hb)) hZe hstep one1 slt1 sv1 e10
    · have hz0 : VG.Proof.Bignum.r2Z W w = 0 := by
        have := mt (VG.Proof.Bignum.r2Z_pos (w := W) hw1).mp (by rw [hE0]; exact of_decide_eq_false hb)
        omega_arith
      rw [hz0]
      exact WP.block_nil ⟨c1, ra1, one1, slt1, by rw [Nat.add_zero]; exact sv1,
        by rw [e10, Nat.mul_zero, Nat.sub_zero], fun _ _ _ => rfl, Outside.refl _ _ _ _, Keep.refl _ _⟩
  refine WP.seq (WP.mono hz fun t₂ J => ?_)
  -- `-S`.
  refine WP.seq (WP.mono (negS_ok J.ctx J.ra J.slt) fun t₃ ⟨⟨c3, ra3, e3, v3, o3⟩, k3⟩ => ?_)
  -- Into array 1.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c3.a7 c3.s5 1) fun t₄ ⟨⟨a3, m4⟩, k4⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k4.gpr (by decide)).trans c3.a7)
    ((k4.gpr (by decide)).trans c3.s5) 4) fun t₅ ⟨⟨a4, m5⟩, k5⟩ => ?_
  obtain k45 := k4.trans k5
  obtain hm5 : t₅.mem = t₃.mem := by rw [m5, m4]
  obtain c5 := c3.regs k45 (by decide) hm5
  refine WP.seq (WP.mono (copySame_ok (dS := slot w 4) (dD := slot w 1) c5.scr a4 ((k5.gpr (by decide)).trans a3)
    c5.t0 (by omega_arith) hw' (slot_al w 4) (slot_al w 1) (by have := sl 4 (by decide); omega_arith)
    (by have := sl 1 (by decide); omega_arith)
    (Or.inr (by have := slot_lt (w := w) (show 1 < 4 by decide); omega_arith))) fun t₆ ⟨⟨c6, o6⟩, k6⟩ => ?_)
  rw [hm5] at c6 o6
  obtain c6' := c5.of k6 (by decide) (by rw [hm5]; exact arrO o6 (by decide) (by decide))
  obtain y6 : A t₆.mem B w 1 = (0 + N - A t₂.mem B w 4) % N := by
    show wordsVal _ _ _ _ = _; rw [wv_words c6]; exact e3
  obtain u6 : ∀ j < 24, j ≠ 1 → A t₆.mem B w j = A t₃.mem B w j := fun j hj hne => arr_out o6 hj hne hn
  obtain k36 := (k3.trans k45).trans k6
  -- The value, if `x ≡ 2^(128 W)`.
  obtain hval : G → A t₆.mem B w 1 % N = 2 ^ (64 * VG.Proof.Bignum.r2E W w) % N := fun g => by
    refine neg_val (R := (2 ^ (64 * w)) ^ (n + VG.Proof.Bignum.r2Z W w)) (Nat.Coprime.pow_left _ hR)
      J.slt J.sv y6 ?_
    rw [hG g, ← Nat.pow_mul, ← Nat.pow_add]
    obtain e : 64 * w * (n + VG.Proof.Bignum.r2Z W w) = 64 * ((n + VG.Proof.Bignum.r2Z W w) * w) := by
      rw [Nat.mul_assoc, Nat.mul_comm w]
    rw [e, show 64 * VG.Proof.Bignum.r2E W w + 64 * ((n + VG.Proof.Bignum.r2Z W w) * w) = 128 * W by
      omega_arith]
  refine r2Tail_ok (s := s) c6' hodd hN ((k36.gpr (by decide)).trans J.ra)
    (by rw [k36.gpr (by decide), J.s10, ← hZE]) hE2 (by rw [y6]; exact Nat.mod_lt _ hN0) hval
    (fun j hj h7 => ?_) ?_ ?_
  · rw [u6 j hj (by omega_arith), v3 j hj (by omega_arith) (by omega_arith) (by omega_arith), J.fix j hj h7, m1]
    exact I.fix j hj h7
  · exact (((I.out.trans (by rw [m1]; exact Outside.refl _ _ _ _)).trans J.out).trans o3).trans
      (arrO o6 (by decide) (by decide))
  · exact Keep.within (Keep.within (Keep.within (I.keep.mono (by decide) : Keep r2FRegs s t) k1 (by decide))
      J.keep (by decide)) k36 (by decide)

/-! ## A factor's working space -/

/-- `power`'s start with `r2Fast` (`PrivPre.prime`'s), then `c`. -/
abbrev powerPF (xj : Nat) (c : Prog isa) : Prog isa :=
  .seq (.block ([.addi .t3 .a7 0] ++ Crt.xb .t4 xj)) (.seq Crt.copyN
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3)) (.seq PrivPre.r2Fast c)))

/-- The registers `powerPF` writes. -/
def powerFRegs : List Reg := powerRegs ++ r2FRegs

/-- `powerPF`: the factor `Pv` from `X`'s array `xj` into array 0, `-p⁻¹
mod 2⁶⁴`, and array 1 below `Pv`, `R² mod Pv` if `G` (`r2Fast_ok`). -/
theorem powerAF_ok {s : State} {B BX : Addr} {Z ZX w wX xj Pv k : Nat} {c : Prog isa} {Q : State → Prop}
    {G : Prop} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 24 ≤ Z)
    (h7 : s.gpr .a7 = off B (slot w 0)) (hra : s.gpr .ra = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hx : Scr s BX ZX) (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2))) (hxj : slot wX xj + 8 * w ≤ ZX)
    (hP : wordsVal s.mem BX (slot wX xj) w = Pv) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1)
    (hwX : wX = 2 * ((k + 7) / 8)) (hk' : k < 2 ^ 40) (hwk : w ≤ (k + 7) / 8)
    (hXZ : slot wX 6 + 8 * (w * nChunks ((k + 7) / 8) w) ≤ ZX)
    (hG : G → wordsVal s.mem BX (slot wX 6) (w * nChunks ((k + 7) / 8) w) % Pv =
      2 ^ (128 * ((k + 7) / 8)) % Pv)
    (hc : ∀ u, WCtx u B Z w Pv → (G → A u.mem B w 1 = 2 ^ (128 * w) % Pv) → PFr B w s.mem u.mem →
      Keep powerFRegs s u → WP isa c u Q) :
    WP isa (powerPF xj c) s Q := by
  obtain hn : B.toNat + slot w 24 ≤ 2 ^ 64 := by have := hs.nowrap; omega_arith
  have hxn := hx.nowrap
  obtain e24 := slot24' w
  obtain s01 := slot_lt (w := w) (show 0 < 1 by decide)
  unfold powerPF
  -- The prime into array 0.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = off B (slot w 0) ∧ u.mem = s.mem)
    (by brun [h7, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (xbase_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h6)
    ((k1.gpr (by decide)).trans h11) xj) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  obtain hm2 : s₂.mem = s.mem := by rw [m2, m1]
  obtain hx2 := hx.congr k12.2.2
  refine WP.seq (WP.mono (Pub.copyIn_ok (B := B) (P := BX) (Zp := ZX) (dS := slot wX xj) (dD := slot w 0) (w := w)
    (hs.congr k12.2.2) hxn (fun j hj => hx2.ld (by omega_arith))
    (fun j hj => hx2.al8 (by omega_arith) (by have := slot_al wX xj; omega_arith)) a4
    ((k2.gpr (by decide)).trans a3) ((k12.gpr (by decide)).trans ht0) (by omega_arith) hw' (slot_al w 0) hxj
    (by omega_arith) hsep) fun s₃ ⟨⟨_, _, c3, o3⟩, k3⟩ => ?_)
  rw [hm2] at c3 o3
  obtain v0 : wordsVal s₃.mem B (slot w 0) w = Pv := by rw [wv_words c3, hP]
  obtain k13 := k12.trans k3
  obtain h7' : s₃.gpr .a7 = off B (slot w 0) := (k13.gpr (by decide)).trans h7
  obtain h5' : s₃.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) := (k13.gpr (by decide)).trans h5
  -- `-p⁻¹ mod 2⁶⁴` and the bases.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (minv_ok (hs.congr k13.2.2) h7' (slot_al w 0) (by omega_arith)
    (low_odd (w := w) (by omega_arith) (by rw [v0]; exact hodd))) fun s₄ ⟨⟨inv4, m4⟩, k4⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k4.gpr (by decide)).trans h7')
    ((k4.gpr (by decide)).trans h5') 1) fun s₅ ⟨⟨a2, m5⟩, k5⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k5.gpr (by decide)).trans ((k4.gpr (by decide)).trans h7'))
    ((k5.gpr (by decide)).trans ((k4.gpr (by decide)).trans h5')) 2) fun s₆ ⟨⟨a5, m6⟩, k6⟩ => ?_
  obtain k46 := (k4.trans k5).trans k6
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k46.gpr (by decide)).trans h7')
    ((k46.gpr (by decide)).trans h5') 3) fun s₇ ⟨⟨a6, m7⟩, k7⟩ => ?_
  obtain k37 := k46.trans k7
  obtain hm7 : s₇.mem = s₃.mem := by rw [m7, m6, m5, m4]
  obtain c7 : WCtx s₇ B Z w Pv := ⟨hs.congr (k13.trans k37).2.2, hw2, hw', hZ, (k37.gpr (by decide)).trans h7',
    (k37.gpr (by decide)).trans h5', (k37.gpr (by decide)).trans ((k13.gpr (by decide)).trans ht0),
    by rw [((k5.trans k6).trans k7).gpr (by decide), hm7]; exact inv4, by rw [hm7]; exact v0⟩
  obtain k17 := k13.trans k37
  obtain F7 : PFr B w s.mem s₇.mem := by rw [hm7]; exact o3.mono (Nat.le_refl _) (by omega_arith)
  -- `R² mod p`, by `r2Fast`.
  refine WP.seq (WP.mono (r2Fast_ok (G := G) (W := (k + 7) / 8) (wX := wX) c7 ((k17.gpr (by decide)).trans hra)
    (((k6.trans k7).gpr (by decide)).trans a2) (hx.congr k17.2.2) hsep ((k17.gpr (by decide)).trans h6)
    ((k17.gpr (by decide)).trans h11)
    hwX (by omega_arith) hwk hXZ hP2 hodd (fun g => by rw [x_wv' F7 hsep (by omega_arith) hxn hXZ]; exact hG g))
    fun s₈ ⟨⟨c8, _, _, r8, _, o8⟩, k8⟩ => ?_)
  obtain F8 : PFr B w s.mem s₈.mem := F7.trans (PFr.of_win o8)
  exact hc s₈ c8 r8 F8 (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within
    (Keep.within (Keep.within (Keep.refl powerFRegs s) k1 (by decide)) k2 (by decide)) k3 (by decide))
    k4 (by decide)) k5 (by decide)) k6 (by decide)) k7 (by decide)) k8 (by decide))

theorem prime_powerPF (xj : Nat) : PrivPre.prime xj = powerPF xj (.seq (.block (base .t4 1 ++
    ([.load .d .t3 .s6 Crt.oDP, .load .d .t1 .s6 Crt.oMask, .addi .t5 .t0 0] : List Instr)))
    (.seq (countLoop .t5 [.load .d .s0 .t4 0, .logic .and .s0 .s0 .t1, .store .d .s0 .t3 0,
      .addi .t3 .t3 8, .addi .t4 .t4 8]) (.block [.store .d .t3 .s6 Crt.oDP]))) := rfl

end VG.Proof.Bignum.RISCV64.Win

end

end

/-! ### `Bignum.RISCV64.PrivPrePQ`, which this module and modules that import it used -/

section

/-!
# An RSA private key's precomputed values on RISC-V: `p q = n` at the factors' widths

`checkPQs_ok`: `PrivPre.checkPQs` is a check of `p q = n` as
`Crt.checksWith` needs it (`Crt.PQOk`), when `p` and `q` fit in `w_p` (`a3`)
and `w_q` (`t1`) words, `w_p + w_q ≤ W`:

* `rowWord_ok`, `row_ok`: a row of the schoolbook product, `t += a q`
  over `q`'s `w_q` words, its carry into the word after them (`mac_arith`);
* `rows_ok`: `w_p` rows, `t = p q` over `w_p + w_q` words, from `t = 0`;
* `checkPQs_ok`: array 6 zeroed, `p q` into it, then `Crt.pqEq_ok`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PrivPre
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays)

/-- `a + b` words: the first `a`, and `2^(64 a)` times the `b` after them. -/
theorem wordsVal_app (m : Mem) (B : Addr) (d a : Nat) : ∀ b,
    wordsVal m B d (a + b) = wordsVal m B d a + 2 ^ (64 * a) * wordsVal m B (d + 8 * a) b
  | 0 => by simp [wordsVal]
  | b + 1 => by
    rw [← Nat.add_assoc, wordsVal_succ_top, wordsVal_app m B d a b, wordsVal_succ_top,
      show d + 8 * (a + b) = d + 8 * a + 8 * b by omega_arith, show 64 * (a + b) = 64 * a + 64 * b by omega_arith,
      Nat.pow_add, Nat.mul_add (2 ^ (64 * a)), Nat.mul_assoc, Nat.add_assoc]

/-- `x + y` as its low word and the carry `sltu` computes. -/
theorem add_carry (x y : BitVec 64) :
    (x + y).toNat + 2 ^ 64 * (if x + y < y then (1 : BitVec 64) else 0).toNat = x.toNat + y.toNat := by
  obtain hx := x.isLt; have hy := y.isLt
  by_cases h : x + y < y
  · rw [ite_eq_left h]; rw [BitVec.lt_def, BitVec.toNat_add] at h
    rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl]; omega_arith
  · rw [ite_eq_right h]; rw [BitVec.lt_def, BitVec.toNat_add] at h
    rw [BitVec.toNat_add, show (0 : BitVec 64).toNat = 0 from rfl]; omega_arith

/-- The arithmetic of a word of a row: `a q + t + c` as its low word and the
next carry, the high word of `a q` plus the carries of the two additions. -/
theorem mac_arith (a q t c : BitVec 64) :
    (a * q + t + c).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * q.toNat / 2 ^ 64) +
      (if a * q + t < t then 1 else 0) + (if a * q + t + c < c then 1 else 0)).toNat =
      a.toNat * q.toNat + t.toNat + c.toNat := by
  obtain ha := a.isLt; have hq := q.isLt; have ht := t.isLt; have hc := c.isLt
  obtain hP : a.toNat * q.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  obtain hd := Nat.div_add_mod (a.toNat * q.toNat) (2 ^ 64)
  obtain e0 : (a * q).toNat = a.toNat * q.toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  obtain e1 := add_carry (a * q) t
  obtain e2 := add_carry (a * q + t) c
  obtain hhi : a.toNat * q.toNat / 2 ^ 64 < 2 ^ 64 := by
    have := Nat.div_le_div_right (c := 2 ^ 64) hP; omega_arith
  generalize (if a * q + t < t then (1 : BitVec 64) else 0) = c1 at e1 ⊢
  generalize (if a * q + t + c < c then (1 : BitVec 64) else 0) = c2 at e2 ⊢
  obtain hc1 : c1.toNat ≤ 1 := by
    have := (a * q + t).isLt; have := (a * q).isLt; rw [e0] at e1
    rcases Nat.lt_or_ge c1.toNat 2 with h | h
    · omega_arith
    · have := Nat.mul_le_mul_left (2 ^ 64) h; omega_arith
  obtain hc2 : c2.toNat ≤ 1 := by
    have := (a * q + t + c).isLt; have := (a * q + t).isLt
    rcases Nat.lt_or_ge c2.toNat 2 with h | h
    · omega_arith
    · have := Nat.mul_le_mul_left (2 ^ 64) h; omega_arith
  obtain hsum : a.toNat * q.toNat / 2 ^ 64 + c1.toNat + c2.toNat < 2 ^ 64 := by
    obtain hl := (a * q + t + c).isLt
    obtain hb : a.toNat * q.toNat + t.toNat + c.toNat ≤ 2 ^ 128 - 1 := by omega_arith
    rw [e0] at e1
    rcases Nat.lt_or_ge (a.toNat * q.toNat / 2 ^ 64 + c1.toNat + c2.toNat) (2 ^ 64) with h | h
    · exact h
    · have := Nat.mul_le_mul_left (2 ^ 64) h; omega_arith
  rw [BitVec.toNat_add (BitVec.ofNat 64 _ + c1) c2, BitVec.toNat_add (BitVec.ofNat 64 _) c1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hhi,
    Nat.mod_eq_of_lt (show a.toNat * q.toNat / 2 ^ 64 + c1.toNat < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt hsum]
  rw [e0] at e1
  omega_arith

/-- `⌈L / 8⌉`, as `PrivPre.pqLens` computes it. -/
theorem len_words (L : Nat) (hL : L < 2 ^ 32) :
    (BitVec.ofNat 64 L + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((L + 7) / 8) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := L) (by omega_arith),
      Nat.mod_eq_of_lt (a := L + 7) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)])

/-! ## A row -/

/-- What a row keeps after `j` words, from `s`, with the multiplier `a`
(`a6`): the pointers, the carry `c` (`s1`), with
`t_{<j} + 2^(64 j) c = t₀_{<j} + a q_{<j}`, and the words from `j` on. -/
def RowI (s : State) (B : Addr) (dA dQ : Nat) (a : BitVec 64) (j : Nat) (t : State) : Prop :=
  t.gpr .t3 = off B (dA + 8 * j) ∧ t.gpr .t4 = off B (dQ + 8 * j) ∧ t.gpr .a6 = a ∧
    Outside B dA (8 * j) s.mem t.mem ∧
    wordsVal t.mem B dA j + 2 ^ (64 * j) * (t.gpr .s1).toNat = wordsVal s.mem B dA j + a.toNat * wordsVal s.mem B dQ j ∧
    Keep [.s0, .s1, .s2, .s3, .t3, .t4, .t5] s t

theorem rowWord_ok {s : State} {B : Addr} {Z dA dQ wq : Nat} {a : BitVec 64} (hs : Scr s B Z) (hA8 : dA % 8 = 0)
    (hQ8 : dQ % 8 = 0) (hA : dA + 8 * wq ≤ Z) (hQ : dQ + 8 * wq ≤ Z) (dAQ : dQ + 8 * wq ≤ dA ∨ dA + 8 * wq ≤ dQ)
    {j : Nat} (hj : j < wq) {t : State} (hI : RowI s B dA dQ a j t) :
    WP isa (.block (rowWord ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      RowI s B dA dQ a (j + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j3, j4, j6, jout, jv, jk⟩ := hI
  obtain hs' := hs.congr jk.2.2
  obtain wT : Mont.word t.mem B (dA + 8 * j) = Mont.word s.mem B (dA + 8 * j) := jout.word (by omega_using []) (by omega_using [hA, hj, hnw])
  obtain wQ : Mont.word t.mem B (dQ + 8 * j) = Mont.word s.mem B (dQ + 8 * j) := jout.word (by omega_using [dAQ, hj]) (by omega_using [hQ, hj, hnw])
  generalize hq : Mont.word s.mem B (dQ + 8 * j) = q at wQ
  generalize hx : Mont.word s.mem B (dA + 8 * j) = x at wT
  have rQ : t.mem.readW (off B (dQ + 8 * j)) 64 = q := wQ
  have rT : t.mem.readW (off B (dA + 8 * j)) 64 = x := wT
  refine WP.mono (WP.keep [.s0, .s1, .s2, .s3, .t3, .t4, .t5] (Q := fun t' =>
      t'.gpr .t3 = off B (dA + 8 * j + 8) ∧ t'.gpr .t4 = off B (dQ + 8 * j + 8) ∧
      t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
      t'.gpr .s1 = BitVec.ofNat 64 ((t.gpr .a6).toNat * q.toNat / 2 ^ 64) +
        (if t.gpr .a6 * q + x < x then 1 else 0) + (if t.gpr .a6 * q + x + t.gpr .s1 < t.gpr .s1 then 1 else 0) ∧
      t'.mem = t.mem.writeW (off B (dA + 8 * j)) (t.gpr .a6 * q + x + t.gpr .s1)) (by
    unfold rowWord
    brun [j3, j4, rQ, rT, BitVec.add_zero, hs'.ld (show dQ + 8 * j + 8 ≤ Z by omega_using [hQ, hj]),
      hs'.al8 (show dQ + 8 * j + 8 ≤ Z by omega_using [hQ, hj]) (by omega_using [hQ8]), hs'.ld (show dA + 8 * j + 8 ≤ Z by omega_using [hA, hj]),
      hs'.al8 (show dA + 8 * j + 8 ≤ Z by omega_using [hA, hj]) (by omega_using [hA8]), hs'.st (show dA + 8 * j + 8 ≤ Z by omega_using [hA, hj])])
    (by rfl) (by rfl)) fun t' ⟨⟨u3, u4, u5, u1, um⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk uk⟩, u5⟩
  · rw [u3, show dA + 8 * j + 8 = dA + 8 * (j + 1) by omega_using []]
  · rw [u4, show dQ + 8 * j + 8 = dQ + 8 * (j + 1) by omega_using []]
  · rw [uk.gpr (by decide), j6]
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside t.mem B (d := dA + 8 * j) _ (by omega_using [hA, hj, hnw])).mono (by omega_using []) (by omega_using []))
  · have km := mac_arith (t.gpr .a6) q x (t.gpr .s1)
    rw [um, u1, fin64_wordsVal_write_top _ _ _ _ _ (by omega_using [hA, hj, hnw]), wordsVal_succ_top s.mem B dA j,
      wordsVal_succ_top s.mem B dQ j, hq, hx, j6, Nat.mul_succ, Nat.pow_add]
    rw [j6] at km
    generalize (a * q + x + t.gpr .s1).toNat = lo at km ⊢
    generalize (BitVec.ofNat 64 (a.toNat * q.toNat / 2 ^ 64) + (if a * q + x < x then 1 else 0) +
      (if a * q + x + t.gpr .s1 < t.gpr .s1 then 1 else 0)).toNat = c' at km ⊢
    generalize (t.gpr .s1).toNat = c at km jv
    generalize 2 ^ (64 * j) = P at jv ⊢
    generalize wordsVal t.mem B dA j = Wt at jv ⊢
    generalize wordsVal s.mem B dA j = Ws at jv ⊢
    generalize wordsVal s.mem B dQ j = Qs at jv ⊢
    have := congrArg (P * ·) km
    grind

/-- The registers a row writes. -/
def rowRegs : List Reg := [.a0, .a1, .a3, .a6, .s0, .s1, .s2, .s3, .t3, .t4, .t5]

/-- A row, `p_i` at `dP + 8 i` (`a0`), the product's words from `i` at `dA`
(`a1`), `q`'s `w_q` words (`t1`) in array 5, and the product's word
`i + w_q` (which the row overwrites): `t := t + p_i q` over `w_q + 1`
words, and the next row's pointers and count. -/
theorem row_ok {s : State} {B : Addr} {Z w dP dA wq i : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .a0 = off B (dP + 8 * i)) (h1 : s.gpr .a1 = off B dA) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht1 : s.gpr .t1 = BitVec.ofNat 64 wq) (hwq : 1 ≤ wq)
    (hwq' : wq < 2 ^ 31) (hP8 : dP % 8 = 0) (hA8 : dA % 8 = 0) (hPZ : dP + 8 * i + 8 ≤ Z)
    (hA : dA + 8 * (wq + 1) ≤ Z) (hQ : slot w 5 + 8 * wq ≤ Z)
    (dAQ : slot w 5 + 8 * wq ≤ dA ∨ dA + 8 * (wq + 1) ≤ slot w 5)
    (dAP : dP + 8 * i + 8 ≤ dA ∨ dA + 8 * (wq + 1) ≤ dP + 8 * i) :
    WP isa (.seq (.block rowHead) (.seq (countLoop .t5 rowWord) (.block rowTail))) s fun t =>
      (wordsVal t.mem B dA (wq + 1) = wordsVal s.mem B dA wq +
          (Mont.word s.mem B (dP + 8 * i)).toNat * wordsVal s.mem B (slot w 5) wq ∧
        Outside B dA (8 * (wq + 1)) s.mem t.mem ∧ t.gpr .a0 = off B (dP + 8 * (i + 1)) ∧
        t.gpr .a1 = off B (dA + 8) ∧ t.gpr .a3 = s.gpr .a3 - BitVec.ofNat 64 1) ∧ Keep rowRegs s t := by
  have hnw := hs.nowrap
  obtain al := VG.Proof.Bignum.RISCV64.slot_al8 w
  unfold rowHead
  generalize hp : Mont.word s.mem B (dP + 8 * i) = pw
  have rP : s.mem.readW (off B (dP + 8 * i)) 64 = pw := hp
  -- The row's start.
  obtain head : WP isa (.block (([.load .d .a6 .a0 0, .addi .t3 .a1 0] : List Instr) ++ PublicChecked.base .t4 5)) s
      fun t => (t.gpr .a6 = pw ∧ t.gpr .t3 = off B dA ∧ t.gpr .t4 = off B (slot w 5) ∧ t.mem = s.mem) ∧
        Keep [.a6, .t3, .t4] s t := by
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.a6, .t3] (Q := fun t => t.gpr .a6 = pw ∧ t.gpr .t3 = off B dA ∧ t.mem = s.mem)
      (by brun [h0, h1, rP, BitVec.add_zero, hs.ld (show dP + 8 * i + 8 ≤ Z by omega),
        hs.al8 (show dP + 8 * i + 8 ≤ Z by omega) (by omega)]) (by rfl) (by rfl)) fun s₁ ⟨⟨a6, a3, m1⟩, k1⟩ => ?_
    refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h7)
      ((k1.gpr (by decide)).trans h5) 5) fun s₂ ⟨⟨a4, m2⟩, k2⟩ =>
        ⟨⟨by rw [k2.gpr (by decide), a6], by rw [k2.gpr (by decide), a3], a4, by rw [m2, m1]⟩, (k1.trans k2).mono (by decide)⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono head fun s₂ ⟨⟨a6, a3, a4, m2⟩, k2⟩ => ?_
  refine WP.mono (WP.keep [.t5, .s1] (Q := fun t => t.gpr .t5 = BitVec.ofNat 64 wq ∧ t.gpr .s1 = 0 ∧ t.mem = s₂.mem)
    (by brun [(k2.gpr (by decide)).trans ht1, BitVec.add_zero, exec_li_zero']; rfl) (by rfl) (by rfl))
    fun s₃ ⟨⟨a5, a1', m3⟩, k3⟩ => ?_
  obtain k23 := k2.trans k3
  obtain I0 : RowI s₃ B dA (slot w 5) pw 0 s₃ := ⟨by rw [k3.gpr (by decide), a3]; rfl,
    by rw [k3.gpr (by decide), a4]; rfl, by rw [k3.gpr (by decide), a6], Outside.refl _ _ _ _,
    by simp [wordsVal, a1'], Keep.refl _ _⟩
  obtain hs₃ := hs.congr k23.2.2
  -- The words.
  refine WP.seq (WP.mono (wp_countdown (cnt := .t5) (N := wq) (by omega) (by omega) (RowI s₃ B dA (slot w 5) pw)
    (fun j hj t hI _ => rowWord_ok hs₃ hA8 (al 5) (by omega) hQ (by omega) hj hI) I0 a5)
    fun t ⟨j3, _, _, jout, jv, jk⟩ => ?_)
  obtain k3t := k23.trans jk
  obtain hst := hs.congr k3t.2.2
  -- The carry, and the next row.
  refine WP.mono (WP.keep [.a0, .a1, .a3] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (dA + 8 * wq)) (t.gpr .s1) ∧ t'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 8 ∧
        t'.gpr .a1 = s.gpr .a1 + BitVec.ofNat 64 8 ∧ t'.gpr .a3 = s.gpr .a3 - BitVec.ofNat 64 1) (by
    unfold rowTail
    brun [j3, k3t.gpr (r := .a0) (by decide), k3t.gpr (r := .a1) (by decide), k3t.gpr (r := .a3) (by decide),
      hst.st (show dA + 8 * wq + 8 ≤ Z by omega), hst.al8 (show dA + 8 * wq + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun u ⟨⟨um, u0, u1, u3⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, u3⟩, (k3t.trans uk).mono (by decide)⟩
  · rw [m3, m2] at jv
    rw [um, fin64_wordsVal_write_top _ _ _ _ _ (by omega), jv]
  · rw [m3, m2] at jout
    rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dA + 8 * wq) _ (by omega)).mono (by omega) (by omega))
  · rw [u0, h0, off_add, show dP + 8 * i + 8 = dP + 8 * (i + 1) by omega]
  · rw [u1, h1, off_add]

/-! ## The rows -/

/-- What the rows keep after `i` rows, from `s`: the pointers, the product
`p_{<i} q` over the first `i + w_q` words of array 6, and memory elsewhere. -/
def RowsI (s : State) (B : Addr) (w wq : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .a0 = off B (slot w 4 + 8 * i) ∧ t.gpr .a1 = off B (slot w 6 + 8 * i) ∧
    wordsVal t.mem B (slot w 6) (i + wq) = wordsVal s.mem B (slot w 4) i * wordsVal s.mem B (slot w 5) wq ∧
    Outside B (slot w 6) (8 * (i + wq)) s.mem t.mem ∧ Keep rowRegs s t

/-- `rows`, from array 6's first `w_p + w_q ≤ w` words zero, `p` (array 4)
at `a0` and the product (array 6) at `a1`, `w_p` in `a3` and `w_q` in `t1`:
array 6's first `w_p + w_q` words := `p_{<w_p} q_{<w_q}`, changing only
them. -/
theorem rows_ok {s : State} {B : Addr} {Z w wp wq : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .a0 = off B (slot w 4)) (h1 : s.gpr .a1 = off B (slot w 6)) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h3 : s.gpr .a3 = BitVec.ofNat 64 wp)
    (ht1 : s.gpr .t1 = BitVec.ofNat 64 wq) (hwp : 1 ≤ wp) (hwq : 1 ≤ wq) (hpq : wp + wq ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (hz : ∀ k < w, Mont.word s.mem B (slot w 6 + 8 * k) = 0) :
    WP isa rows s fun t =>
      (wordsVal t.mem B (slot w 6) (wp + wq) = wordsVal s.mem B (slot w 4) wp * wordsVal s.mem B (slot w 5) wq ∧
        Outside B (slot w 6) (8 * (wp + wq)) s.mem t.mem) ∧ Keep rowRegs s t := by
  have hnw := hs.nowrap
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  obtain e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  obtain al := VG.Proof.Bignum.RISCV64.slot_al8 w
  obtain I0 : RowsI s B w wq 0 s := ⟨by rw [h0]; rfl, by rw [h1]; rfl,
    by rw [Nat.zero_add, wordsVal_zero (fun k hk => hz k (by omega_using [hpq, hk]))]; simp [wordsVal], Outside.refl _ _ _ _,
    Keep.refl _ _⟩
  refine WP.mono (wp_countdown (cnt := .a3) (N := wp) (by omega_using [hpq, hw']) (by omega_using [hwp]) (RowsI s B w wq)
    (fun i hi t ⟨j0, j1, jv, jout, jk⟩ _ => ?_) I0 h3) fun t ⟨_, _, tv, tout, tk⟩ => ⟨⟨tv, tout⟩, tk⟩
  obtain hst := hs.congr jk.2.2
  refine WP.mono (row_ok (dP := slot w 4) (dA := slot w 6 + 8 * i) (i := i) (wq := wq) hst j0
    (by rw [j1]) ((jk.gpr (by decide)).trans h7) ((jk.gpr (by decide)).trans h5) ((jk.gpr (by decide)).trans ht1)
    hwq (by omega_using [hpq, hw']) (al 4) (by have := al 6; omega_using [this]) (by omega_using [hpq, hZ, e4, e8, hi]) (by omega_using [hpq, hZ, e6, e8, hi]) (by omega_using [hpq, hZ, e5, e8]) (by omega_using [hpq, e5, e6]) (by omega_using [e4, e6]))
    fun t' ⟨⟨rv, rout, r0, r1, r3⟩, rk⟩ => ⟨⟨r0, by rw [r1, show slot w 6 + 8 * i + 8 = slot w 6 + 8 * (i + 1) by omega_using []], ?_, ?_, Keep.trans' jk rk⟩, r3⟩
  · have wP : Mont.word t.mem B (slot w 4 + 8 * i) = Mont.word s.mem B (slot w 4 + 8 * i) :=
      jout.word (by omega_using [hpq, e4, e6, hi]) (by omega_using [hpq, hw', e4, hh, hi])
    obtain wQ : wordsVal t.mem B (slot w 5) wq = wordsVal s.mem B (slot w 5) wq :=
      Outside.wordsVal jout (by omega_using [hpq, e5, e6]) (by omega_using [hpq, hw', e5, hh])
    obtain wL : wordsVal t'.mem B (slot w 6) i = wordsVal t.mem B (slot w 6) i :=
      Outside.wordsVal rout (by omega_using []) (by omega_using [hpq, hw', e6, hh, hi])
    obtain a1 := wordsVal_app t'.mem B (slot w 6) i (wq + 1)
    obtain a2 := wordsVal_app t.mem B (slot w 6) i wq
    rw [show i + (wq + 1) = i + 1 + wq by omega_using [], wL, rv, wP, wQ] at a1
    rw [a1, wordsVal_succ_top s.mem B (slot w 4) i]
    rw [a2] at jv
    generalize 2 ^ (64 * i) = P at jv ⊢
    generalize wordsVal t.mem B (slot w 6) i = A at jv ⊢
    generalize wordsVal t.mem B (slot w 6 + 8 * i) wq = Bv at jv ⊢
    generalize (Mont.word s.mem B (slot w 4 + 8 * i)).toNat = pi
    generalize wordsVal s.mem B (slot w 5) wq = Q at jv ⊢
    generalize wordsVal s.mem B (slot w 4) i = Pi at jv ⊢
    grind
  · exact (jout.mono (Nat.le_refl _) (by omega_using [])).trans (rout.mono (by omega_using []) (by omega_using []))

/-! ## `p q = n` -/

/-- `checkPQs` is a check of `p q = n` for `Crt.checksWith`, from `s` with
`w_p` in `a3` and `w_q` in `t1`, `p` and `q` (arrays 4 and 5) of `w_p` and
`w_q` words, `w_p + w_q ≤ W`, and the words `W` of arrays 6 and 1 zero. -/
theorem checkPQs_ok {s : State} {S : Addr} {Z w wp wq : Nat} (hs : Scr s S Z) (hZ : slot w 8 ≤ Z)
    (hw' : w < 2 ^ 31) (h3 : s.gpr .a3 = BitVec.ofNat 64 wp) (ht1 : s.gpr .t1 = BitVec.ofNat 64 wq)
    (hwp : 1 ≤ wp) (hwq : 1 ≤ wq) (hpq : wp + wq ≤ w)
    (hp : wordsVal s.mem S (slot w 4) w = wordsVal s.mem S (slot w 4) wp)
    (hq : wordsVal s.mem S (slot w 5) w = wordsVal s.mem S (slot w 5) wq)
    (h6top : Mont.word s.mem S (slot w 6 + 8 * w) = 0) (h1top : Mont.word s.mem S (slot w 1 + 8 * w) = 0) :
    Crt.PQOk checkPQs S Z w s := by
  intro t ht t7 tra t5 t0 tk to
  have hnw := hs.nowrap
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  obtain e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  obtain al := VG.Proof.Bignum.RISCV64.slot_al8 w
  obtain t3' : t.gpr .a3 = BitVec.ofNat 64 wp := (tk.gpr (by decide)).trans h3
  obtain t1' : t.gpr .t1 = BitVec.ofNat 64 wq := (tk.gpr (by decide)).trans ht1
  obtain wv : ∀ {j}, j ≠ 3 → j < 8 → ∀ k ≤ w, wordsVal t.mem S (slot w j) k = wordsVal s.mem S (slot w j) k :=
    fun hj hj' k hk => Outside.wordsVal to (by have := VG.Proof.Bignum.slot_sep (w := w) hj; omega_using [hk, this])
      (by have := VG.Proof.Bignum.slot_le (w := w) hj'; omega_using [hZ, hnw, hk, this])
  unfold checkPQs
  -- Array 6 := 0.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .t3) (by decide) t7 t5 6) fun u₁ ⟨⟨b3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr (tk.trans k1).2.2) b3 ((k1.gpr (by decide)).trans t0)
    (by omega_using [hwp, hpq]) hw' (al 6) (by omega_using [hZ, e6, e8])) fun u₂ ⟨⟨_, z2, o2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  -- The pointers.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a0) (by decide) ((k12.gpr (by decide)).trans t7)
    ((k12.gpr (by decide)).trans t5) 4) fun u₃ ⟨⟨b0, m3⟩, k3⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a1) (by decide) ((k3.gpr (by decide)).trans ((k12.gpr (by decide)).trans t7))
    ((k3.gpr (by decide)).trans ((k12.gpr (by decide)).trans t5)) 6) fun u₄ ⟨⟨b1, m4⟩, k4⟩ => ?_
  obtain k14 := k12.trans (k3.trans k4)
  obtain m24 : u₄.mem = u₂.mem := by rw [m4, m3]
  -- The rows.
  refine WP.seq (WP.mono (rows_ok (wp := wp) (wq := wq) (hs.congr (tk.trans k14).2.2) (by rw [k4.gpr (by decide), b0])
    b1 ((k14.gpr (by decide)).trans t7) ((k14.gpr (by decide)).trans t5) ((k14.gpr (by decide)).trans t3')
    ((k14.gpr (by decide)).trans t1') hwp hwq hpq hw' hZ (fun k hk => by rw [m24]; exact z2 k hk))
    fun u₅ ⟨⟨r6, o5⟩, k5⟩ => ?_)
  obtain k15 := k14.trans k5
  obtain O : Outside S (slot w 6) (8 * w) t.mem u₅.mem := by
    rw [m1] at o2
    exact o2.trans (by rw [m24] at o5; exact o5.mono (Nat.le_refl _) (by omega_using [hpq]))
  -- `p q = n`?
  refine WP.mono (Crt.pqEq_ok (hs.congr (tk.trans k15).2.2) (by omega_using [hwp, hpq]) hw' hZ ((k15.gpr (by decide)).trans t7)
    ((k15.gpr (by decide)).trans tra) ((k15.gpr (by decide)).trans t5) ((k15.gpr (by decide)).trans t0)
    ((Mont.Outside.word O (by omega_using []) (by omega_using [hw', e6, hh])).trans ((Mont.Outside.word to (by omega_using [e3, e6]) (by omega_using [hw', e6, hh])).trans h6top))
    ((Mont.Outside.word O (by omega_using [e1, e6]) (by omega_using [hw', e1, hh])).trans ((Mont.Outside.word to (by omega_using [e1, e3]) (by omega_using [hw', e1, hh])).trans h1top)))
    fun u ⟨⟨u9, uo, u7⟩, uk⟩ => ⟨⟨?_, ?_, u7⟩, (k15.trans uk).mono (by decide)⟩
  · -- The product over `W` words.
    obtain hz : ∀ k < w - (wp + wq), Mont.word u₅.mem S (slot w 6 + 8 * (wp + wq) + 8 * k) = 0 := fun k hk => by
      rw [Mont.Outside.word o5 (by omega_using []) (by omega_using [hw', e6, hh, hk]), m24, show slot w 6 + 8 * (wp + wq) + 8 * k = slot w 6 + 8 * (wp + wq + k)
        by omega_using []]
      exact z2 _ (by omega_using [hk])
    obtain hP : wordsVal u₅.mem S (slot w 6) w = wordsVal s.mem S (slot w 4) w * wordsVal s.mem S (slot w 5) w := by
      obtain a := wordsVal_app u₅.mem S (slot w 6) (wp + wq) (w - (wp + wq))
      rw [show wp + wq + (w - (wp + wq)) = w by omega_using [hpq], wordsVal_zero hz, Nat.mul_zero, Nat.add_zero, r6, m24,
        Outside.wordsVal o2 (by omega_using [hpq, e4, e6]) (by omega_using [hw', hpq, e4, hh]), Outside.wordsVal o2 (by omega_using [hpq, e5, e6]) (by omega_using [hw', hpq, e5, hh]), m1,
        wv (by decide) (by decide) wp (by omega_using [hpq]), wv (by decide) (by decide) wq (by omega_using [hpq])] at a
      rw [a, hp, hq]
    obtain h1 : wordsVal u₅.mem S (slot w 1) w = wordsVal s.mem S (slot w 1) w := by
      rw [Outside.wordsVal O (by omega_using [e1, e6]) (by omega_using [hw', e1, hh]), wv (by decide) (by decide) w (Nat.le_refl _)]
    rw [u9, hP, h1, k15.gpr (r := .s9) (by decide)]
  · intro x hx
    obtain hx3 : ofs S x < slot w 3 ∨ slot w 3 + 8 * w ≤ ofs S x := by have := hx 3 (by simp); omega_using [this]
    obtain hx6 : ofs S x < slot w 6 ∨ slot w 6 + 8 * w ≤ ofs S x := by have := hx 6 (by simp); omega_using [this]
    rw [uo x hx3, O x hx6]

end VG.Proof.Bignum.RISCV64.PrivPre

end

end

/-!
# An RSA private key's precomputed values on RISC-V: the checks

`partA_ok`: from the entry, `save`, `args`, `zeroIn`, `setupX` and
`vg_rsa_private_crt`'s `loadX` and `checks`, with `pre` (its first words
zero) as the input and `qInv`: the mask of `n` valid and `p q = n`
(`privMask`, `crtMask_zero`) in the header's `oMask`, and `p` and `q` (or 3)
in `X`'s arrays 4 and 5 (`A`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Frm)
open VG.Proof.Bignum.RISCV64.Crt (wordsOf wordsOf_ge wordsOf_le two_le_wordsOf Buf crtMask checksWith_ok loadX_ok
  setupX_ok Chk chkRegs loadXRegs frm_mid bytesAt_out savW)

/-- The mask of `vg_rsa_private_precompute`: `n` valid and `p q = n`. -/
def privMask (N k P Q : Nat) : Bool := Spec.Rsa.modulusValid N k && decide (P * Q = N)

/-- With the input and `qInv` zero, the CRT's checks are `n` valid and
`p q = n`. -/
theorem crtMask_zero (N k P Q : Nat) : crtMask N k 0 P Q 0 = privMask N k P Q := by
  unfold crtMask privMask
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
theorem os2ip_zero_words {m : Mem} {P : Addr} {w k : Nat} (hz : ∀ i < w, Mont.word m P (8 * i) = 0)
    (hk : k ≤ 8 * w) : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m P k) = 0 := by
  obtain hb : ∀ i < k, m (P + BitVec.ofNat 64 i) = 0 := fun i hi => by
    obtain hw := hz (i / 8) (by omega_arith)
    have := Mem.extractLsb'_read m (P + BitVec.ofNat 64 (8 * (i / 8))) (n := 8) (j := i % 8) (Nat.mod_lt _ (by decide))
    simp only [Mont.word, Mont.off] at hw
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
abbrev cpL (s : State) : Nat := (s.gpr .a5).toNat
abbrev cqL (s : State) : Nat := (s.gpr .a7).toNat
/-- `n`, `p` and `q` as numbers. -/
abbrev cN (s : State) : Nat := Spec.Rsa.os2ip (nB s)
abbrev cP (s : State) : Nat := Spec.Rsa.os2ip (pB s)
abbrev cQ (s : State) : Nat := Spec.Rsa.os2ip (qB s)
/-- The mask. -/
abbrev cb (s : State) : Bool := privMask (cN s) (ck s) (cP s) (cQ s)

/-- What the precondition gives. -/
structure PF (s₀ : State) : Prop where
  k64 : 64 ≤ ck s₀
  k1024 : ck s₀ ≤ 1024
  p1 : 1 ≤ cpL s₀
  pk : cpL s₀ < ck s₀
  q1 : 1 ≤ cqL s₀
  qk : cqL s₀ < ck s₀
  room : slot (cwX s₀) 8 + slot (wordsOf (cpL s₀)) 24 + slot (wordsOf (cqL s₀)) 24 ≤ cZ s₀
  nw : (cS s₀).toNat + cZ s₀ ≤ 2 ^ 64
  al : (cS s₀).toNat % 8 = 0
  preLen : (s₀.gpr .a1).toNat = 2 * cw s₀ + wordsOf (cpL s₀) + wordsOf (cqL s₀)
  pre : Scr s₀ (s₀.gpr .a0) ((s₀.gpr .a1).toNat * 8)
  sepPre : ∀ x, ofs (s₀.gpr .a0) x < (s₀.gpr .a1).toNat * 8 → cZ s₀ ≤ ofs (cS s₀) x
  rN : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a2) i) 1
  sN : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a2) i ≠ x
  rP : ∀ i < cpL s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a4) i) 1
  sP : ∀ i < cpL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a4) i ≠ x
  rQ : ∀ i < cqL s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a6) i) 1
  sQ : ∀ i < cqL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a6) i ≠ x
  rPre : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a0) i) 1
  sPre : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a0) i ≠ x
  dN : ∀ r ∈ [preR s₀, scrR s₀], (nR s₀).Disjoint r

theorem wordsOf_eq (len : Nat) : wordsOf len = Spec.Rsa.primeWords len := by
  unfold wordsOf Spec.Rsa.primeWords Spec.Rsa.modulusWords; split <;> omega_arith

theorem pre_facts {s₀ : State} (h : fnContract.pre s₀) : PF s₀ := by
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl, alPre, alS, alSp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords,
    ← wordsOf_eq] at hpl
  obtain hk8 : ck s₀ ≤ (s₀.gpr .a1).toNat * 8 := by
    show (s₀.gpr .a3).toNat ≤ _; rw [hpl]; have := wordsOf_ge (l := (s₀.gpr .a5).toNat); omega_arith
  have dPS' : (⟨s₀.gpr .a0, (s₀.gpr .a1).toNat * 8⟩ : Region).Disjoint ⟨cS s₀, cZ s₀⟩ := dPS
  refine ⟨hk, hk', hp1, hpk, hq1, hqk, ?_, nwS, alS, hpl,
    Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..) nwPre alPre,
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
  · show slot (2 * (((s₀.gpr .a3).toNat + 7) / 8)) 8 + slot (wordsOf (s₀.gpr .a5).toNat) 24 +
      slot (wordsOf (s₀.gpr .a7).toNat) 24 ≤ (stackArg s₀ 1).toNat * 8
    have := wordsOf_le (l := (s₀.gpr .a5).toNat)
    have := wordsOf_le (l := (s₀.gpr .a7).toNat)
    unfold slot hdrBytes; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dPN.symm
    · exact dNS

/-- The registers written up to `setupX`. -/
def a0Regs : List Reg := [.t0, .s6, .t3, .s0, .t5, .t2, .t4, .a7, .ra, .s5, .s11]

/-- What holds after `setupX`, from the entry state `s₀`. -/
structure A0 (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : Mont.word s.mem (cS s₀) oOut = s₀.gpr .a0
  hN : Mont.word s.mem (cS s₀) oN = s₀.gpr .a2
  hNL : Mont.word s.mem (cS s₀) oNLen = s₀.gpr .a3
  hIn : Mont.word s.mem (cS s₀) oIn = s₀.gpr .a0
  hP : Mont.word s.mem (cS s₀) oP = s₀.gpr .a4
  hPL : Mont.word s.mem (cS s₀) oPLen = s₀.gpr .a5
  hQ : Mont.word s.mem (cS s₀) oQ = s₀.gpr .a6
  hQL : Mont.word s.mem (cS s₀) oQLen = s₀.gpr .a7
  hQI : Mont.word s.mem (cS s₀) oQInv = s₀.gpr .a0
  hBP : Mont.word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : Mont.word s.mem (cS s₀) oBQ =
    Mont.off (cS s₀) (slot (2 * ((ck s₀ + 7) / 8)) 8 + hdrBytes + 24 * (8 * (wordsOf (cpL s₀) + 2)))
  s6 : s.gpr .s6 = cS s₀
  a7 : s.gpr .a7 = off (cS s₀) (slot (cwX s₀) 0)
  ra : s.gpr .ra = off (cS s₀) (slot (cwX s₀) 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  s11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 (cwX s₀)
  keep : Keep a0Regs s₀ s
  sav : ∀ i < 13, s.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem
  wz : ∀ i < cw s₀, Mont.word s.mem (s₀.gpr .a0) (8 * i) = 0

/-- From the entry to `setupX`. -/
theorem partA0_ok {s₀ : State} (h : fnContract.pre s₀) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ x, A0 s₀ x → WP isa c x Q) :
    WP isa (.seq (.block (PrivPre.save ++ PrivPre.args)) (.seq PrivPre.zeroIn (.seq (.block setupX) c))) s₀ Q := by
  have hpre0 := h
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl, alPre, alS, alSp⟩ := h
  obtain hP := pre_facts hpre0
  have room := hP.room
  obtain hscr : Scr s₀ (cS s₀) (cZ s₀) :=
    Scr.of_mem (by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)) nwS alS
  have hn := hscr.nowrap
  obtain hZ : 256 + 112 ≤ cZ s₀ := by unfold slot hdrBytes at room; omega_arith
  have hZ' : 368 ≤ (stackArg s₀ 1).toNat * 8 := hZ
  obtain hargs : argsR s₀ ∈ s₀.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  obtain hst : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 8 :=
    ⟨_, List.mem_append_left _ hargs, by
      have := Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩
  obtain esav : ∀ i, off (savW (cS s₀)) (8 * i) = off (cS s₀) (112 + 8 * i) := fun i => by
    simp only [off, savW]; rw [Offset.add_add]
  obtain hsavR : ∀ i < 13, (scrR s₀).Contains (off (savW (cS s₀)) (8 * i)) 8 := fun i hi => by
    rw [esav]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain hsavA : ∀ i < 13, (off (savW (cS s₀)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [esav]; exact hscr.al8 (by omega_arith) (by omega_arith)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s₀ rfl hst (by omega_arith)
    (fun i hi => ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), hsavR i hi⟩) hsavA)
    fun t hSv => ?_
  have kt := hSv.keep
  refine WP.mono (args_ok (hscr.congr kt.2.2) (by omega_arith) (by rw [hSv.s6]; exact (BitVec.add_zero _).symm))
    fun u ⟨⟨hA, Ou⟩, ku⟩ => ?_
  obtain ktu := kt.trans ku
  obtain g : ∀ r, r ∉ [Reg.t0, .s6] → t.gpr r = s₀.gpr r := fun r hr => kt.gpr hr
  -- Changes within the working space or `pre`, as frames.
  obtain frS : ∀ {m m' : Mem} {o n : Nat}, Outside (cS s₀) o n m m' → o + n ≤ cZ s₀ →
      Frame [preR s₀, scrR s₀] m m' := fun {m m' o n} h hon x hx => by
    refine h x ?_
    have := hx (scrR s₀) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only [Region.Contains, ofs, cS, cZ] at this hon ⊢
    omega_arith
  obtain frP : ∀ {m m' : Mem} {o n : Nat}, Outside (s₀.gpr .a0) o n m m' → o + n ≤ (s₀.gpr .a1).toNat * 8 →
      Frame [preR s₀, scrR s₀] m m' := fun {m m' o n} h hon x hx => by
    refine h x ?_
    have := hx (preR s₀) (List.mem_cons_self ..)
    simp only [Region.Contains, ofs] at this ⊢
    omega_arith
  obtain F1 : Frame [preR s₀, scrR s₀] s₀.mem u.mem := by
    refine (hSv.frame.sub fun r hr => ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (frS Ou (by omega_arith))
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Crt.savR, savW]
    rw [show cS s₀ + BitVec.ofNat 64 112 = off (cS s₀) 112 from rfl]
    exact Offset.sub_base _ (by omega_arith)
  -- `zeroIn`.
  obtain hw1 : 1 ≤ cw s₀ := by simp only [cw, ck]; omega_arith
  have hcw : cw s₀ = ((s₀.gpr .a3).toNat + 7) / 8 := rfl
  obtain u0 : u.gpr .a0 = s₀.gpr .a0 := (ku.gpr (by decide)).trans (g _ (by decide))
  obtain u3 : u.gpr .a3 = BitVec.ofNat 64 (ck s₀) := by
    rw [ku.gpr (by decide), g _ (by decide)]; exact (Pre.ofNat_toNat64 _).symm
  obtain ⟨K, hK⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  rw [hK] at u3
  have hK' : (s₀.gpr .a3).toNat = K := hK
  refine WP.seq ?_
  unfold PrivPre.zeroIn
  refine WP.seq (WP.mono (WP.keep [.t3, .t0] (Q := fun v => v.gpr .t3 = off (s₀.gpr .a0) 0 ∧
      v.gpr .t0 = BitVec.ofNat 64 (2 * cw s₀) ∧ v.mem = u.mem) (by
        brun [u0, u3, BitVec.ofNat_add_ofNat, Pre.ofNat_add7_shr3 K (by omega_arith),
          Crt.ofNat_shl _ _ (show 1 < 64 by decide), Nat.reducePow]
        rw [Crt.ofNat_shr3 (K + 7) (by omega_arith), Crt.ofNat_shl _ _ (show 1 < 64 by decide)]
        exact congrArg _ (by simp only [cw, hK])) (by rfl) (by rfl)) fun v₁ ⟨⟨z3, z0, zm⟩, zk⟩ => ?_)
  refine WP.mono (zeroWords_ok (hP.pre.congr (ktu.trans zk).2.2) z3 z0 (by omega_arith) (by omega_arith)
    (by decide) (by rw [hP.preLen]; omega_arith))
    fun v ⟨⟨_, vz, vo⟩, vk⟩ => ?_
  rw [zm] at vo
  obtain kv := (ktu.trans zk).trans vk
  obtain hPS : ∀ x, ofs (cS s₀) x < cZ s₀ → (s₀.gpr .a1).toNat * 8 ≤ ofs (s₀.gpr .a0) x := fun x hx => by
    by_contra hc
    exact dPS x (by simp only [Region.Contains]; simp only [ofs] at hc; omega_arith)
      (by simp only [Region.Contains]; simp only [ofs, cS, cZ] at hx; omega_arith)
  obtain hhv : ∀ d, d + 8 ≤ cZ s₀ → Mont.word v.mem (cS s₀) d = Mont.word u.mem (cS s₀) d := fun d hd =>
    Mem.readW_congr fun i hi => vo _ (Or.inr (by
      have := hPS (off (cS s₀) d + BitVec.ofNat 64 i) (by rw [ofs_off _ (by omega_arith)]; omega_arith)
      rw [hP.preLen] at this
      exact Nat.le_trans (by omega_arith) this))
  obtain F2 : Frame [preR s₀, scrR s₀] s₀.mem v.mem := F1.trans (frP vo (by rw [hP.preLen]; omega_arith))
  -- `setupX`.
  obtain v6 : v.gpr .s6 = cS s₀ := by
    rw [vk.gpr (by decide), zk.gpr (by decide), ku.gpr (by decide)]; exact hSv.s6
  refine WP.seq (WP.mono (setupX_ok (k := ck s₀) (pl := cpL s₀) (hscr.congr kv.2.2) (by omega_arith)
    (by rw [v6]; exact (BitVec.add_zero _).symm)
    (by rw [kv.gpr (by decide)]; exact (Pre.ofNat_toNat64 _).symm) (by omega_arith) hk'
    (by rw [hhv _ (by unfold oPLen; omega_arith), hA.pLen, g _ (by decide)]; exact (Pre.ofNat_toNat64 _).symm)
    hp1 (by show (s₀.gpr .a5).toNat ≤ 1024; omega_arith))
    fun x ⟨⟨x7, xra, x5, x11, x0, xBP, xBQ, Ox⟩, kx⟩ => ?_)
  obtain kx' := kv.trans kx
  obtain F3 : Frame [preR s₀, scrR s₀] s₀.mem x.mem := F2.trans (frS Ox (by unfold oBP; omega_arith))
  obtain hx : ∀ d, d + 8 ≤ 96 → Mont.word x.mem (cS s₀) d = Mont.word u.mem (cS s₀) d := fun d hd => by
    rw [Ox.word (Or.inl (by unfold oBP; omega_arith)) (by omega_arith), hhv d (by omega_arith)]
  refine hc x ⟨hscr.congr kx'.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, xBP, xBQ,
    (kx.gpr (by decide)).trans v6, x7, xra, x5, x11, x0, kx'.mono (by decide), fun i hi => ?_, F3, fun i hi => ?_⟩
  · rw [hx _ (by decide), hA.out, g _ (by decide)]
  · rw [hx _ (by decide), hA.n, g _ (by decide)]
  · rw [hx _ (by decide), hA.nLen, g _ (by decide)]
  · rw [hx _ (by decide), hA.inp, g _ (by decide)]
  · rw [hx _ (by decide), hA.p, g _ (by decide)]
  · rw [hx _ (by decide), hA.pLen, g _ (by decide)]
  · rw [hx _ (by decide), hA.q, g _ (by decide)]
  · rw [hx _ (by decide), hA.qLen, g _ (by decide)]
  · rw [hx _ (by decide), hA.qinv, g _ (by decide)]
  · have h1 := hSv.saved i hi
    change x.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = _
    change t.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = _ at h1
    rw [esav] at h1 ⊢
    change Mont.word x.mem (cS s₀) (112 + 8 * i) = _
    change Mont.word t.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [Ox.word (Or.inr (by unfold oBP; omega_arith)) (by omega_arith), hhv _ (by omega_arith),
      Ou.word (Or.inr (by omega_arith)) (by omega_arith)]
    exact h1
  · rw [← vz i (by omega_arith), Nat.zero_add]
    refine Mem.readW_congr fun j hj => Ox _ (Or.inr ?_)
    have := hP.sepPre (off (s₀.gpr .a0) (8 * i) + BitVec.ofNat 64 j) (by
      rw [ofs_off _ (by omega_arith), hP.preLen]; omega_arith)
    exact Nat.le_trans (by unfold oBP; omega_arith) this

/-- A buffer apart from what changed is as it was. -/
theorem bytes_frame {m m' : Mem} {rs : List Region} (F : Frame rs m m') {A : Addr} {L : Nat}
    (hd : ∀ r ∈ rs, (⟨A, L⟩ : Region).Disjoint r) (hL : L ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' A L = Spec.Rsa.bytesAt m A L := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => F.bytes (R := ⟨A, L⟩) hd hL (List.mem_range.mp hi)

/-- Changes within the working space, as a frame. -/
theorem frame_of_frm {s₀ : State} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (cS s₀) rs m m')
    (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ cZ s₀) : Frame [preR s₀, scrR s₀] m m' := fun x hx =>
  h x fun r hr => Or.inr (by
    obtain h1 := hx (scrR s₀) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    obtain h2 := hZ r hr
    simp only [Region.Contains, ofs, cS, cZ] at h1 h2 ⊢
    omega_arith)

theorem frame_of_outside {s₀ : State} {o n : Nat} {m m' : Mem} (h : Outside (cS s₀) o n m m')
    (hZ : o + n ≤ cZ s₀) : Frame [preR s₀, scrR s₀] m m' :=
  frame_of_frm (rs := [(o, n)]) (Frm.of_outside h (List.mem_singleton_self _))
    fun r hr => by rw [List.mem_singleton.mp hr]; exact hZ

/-- The registers written up to the checks. -/
def aRegs : List Reg := a0Regs ++ loadXRegs ++ [.a3, .t1] ++ chkRegs

/-- What holds after the checks, from the entry state `s₀`. -/
structure A (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : Mont.word s.mem (cS s₀) oOut = s₀.gpr .a0
  hN : Mont.word s.mem (cS s₀) oN = s₀.gpr .a2
  hNL : Mont.word s.mem (cS s₀) oNLen = s₀.gpr .a3
  hPL : Mont.word s.mem (cS s₀) oPLen = s₀.gpr .a5
  hQL : Mont.word s.mem (cS s₀) oQLen = s₀.gpr .a7
  hBP : Mont.word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : Mont.word s.mem (cS s₀) oBQ =
    Mont.off (cS s₀) (slot (2 * ((ck s₀ + 7) / 8)) 8 + hdrBytes + 24 * (8 * (wordsOf (cpL s₀) + 2)))
  hMask : Mont.word s.mem (cS s₀) oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  s6 : s.gpr .s6 = cS s₀
  s11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  x4 : wordsVal s.mem (cS s₀) (slot (cwX s₀) 4) (cwX s₀) = if cb s₀ then cP s₀ else 3
  x5 : wordsVal s.mem (cS s₀) (slot (cwX s₀) 5) (cwX s₀) = if cb s₀ then cQ s₀ else 3
  keep : Keep aRegs s₀ s
  sav : ∀ i < 13, s.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

/-- From the entry to the checks. -/
theorem partA_ok {s₀ : State} (h : fnContract.pre s₀) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ t, A s₀ t → WP isa c t Q) :
    WP isa (.seq (.block (PrivPre.save ++ PrivPre.args)) (.seq PrivPre.zeroIn (.seq (.block setupX)
      (.seq Crt.loadX (.seq (.block PrivPre.pqLens) (.seq (Crt.checksWith PrivPre.checkPQs) c)))))) s₀ Q := by
  have hpre0 := h
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl, alPre, alS, alSp⟩ := h
  obtain hP := pre_facts hpre0
  have hn := hP.nw
  have room := hP.room
  refine partA0_ok hpre0 fun x X => ?_
  have dck : ck s₀ = (s₀.gpr .a3).toNat := rfl
  have dcpL : cpL s₀ = (s₀.gpr .a5).toNat := rfl
  have dcqL : cqL s₀ = (s₀.gpr .a7).toNat := rfl
  have dcw : cw s₀ = ((s₀.gpr .a3).toNat + 7) / 8 := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX8 := e (cwX s₀) 8
  obtain eX2 := e (cwX s₀) 2
  have hcw : cwX s₀ = 2 * (((s₀.gpr .a3).toNat + 7) / 8) := rfl
  obtain hwP := wordsOf_ge (l := cpL s₀)
  obtain hwQ := wordsOf_ge (l := cqL s₀)
  obtain hZ8 : slot (cwX s₀) 8 ≤ cZ s₀ := by omega_arith
  obtain hwX : cwX s₀ < 2 ^ 31 := by omega_arith
  obtain rd0 : x.rd ++ x.wr = s₀.rd ++ s₀.wr := by rw [X.keep.2.1, X.keep.2.2]
  obtain z : ∀ a : Addr, a = off a 0 := fun a => (BitVec.add_zero a).symm
  obtain dis : ∀ {A : Addr} {L : Nat}, (preR s₀).Disjoint ⟨A, L⟩ → (⟨A, L⟩ : Region).Disjoint (scrR s₀) →
      ∀ r ∈ [preR s₀, scrR s₀], (⟨A, L⟩ : Region).Disjoint r := fun h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h1.symm
    · exact h2
  obtain bN : Spec.Rsa.bytesAt x.mem (s₀.gpr .a2) (ck s₀) = nB s₀ :=
    bytes_frame X.frame (dis dPN dNS) (Nat.le_of_lt (BitVec.isLt _))
  obtain bP : Spec.Rsa.bytesAt x.mem (s₀.gpr .a4) (cpL s₀) = pB s₀ :=
    bytes_frame X.frame (dis dPP dpS) (Nat.le_of_lt (BitVec.isLt _))
  obtain bQ : Spec.Rsa.bytesAt x.mem (s₀.gpr .a6) (cqL s₀) = qB s₀ :=
    bytes_frame X.frame (dis dPQ dqS) (Nat.le_of_lt (BitVec.isLt _))
  obtain bI : Spec.Rsa.os2ip (Spec.Rsa.bytesAt x.mem (s₀.gpr .a0) (ck s₀)) = 0 :=
    os2ip_zero_words X.wz (by simp only [cw]; omega_arith)
  obtain bQI : Spec.Rsa.os2ip (Spec.Rsa.bytesAt x.mem (s₀.gpr .a0) (cpL s₀)) = 0 :=
    os2ip_zero_words X.wz (by simp only [cw]; omega_arith)
  -- `X`'s arrays.
  refine WP.seq (WP.mono (loadX_ok (Na := s₀.gpr .a2) (Pa := s₀.gpr .a4) (Qa := s₀.gpr .a6) (Ia := s₀.gpr .a0)
    (QIa := s₀.gpr .a0) (k := ck s₀) (pL := cpL s₀) (qL := cqL s₀) X.scr hZ8 (by omega_arith) hwX
    (by rw [X.s6]; exact z _) X.a7 X.ra X.s5 X.t0 (by rw [X.hN]; exact z _)
    (by rw [X.hNL]; exact (Pre.ofNat_toNat64 _).symm) (by rw [X.hP]; exact z _)
    (by rw [X.hPL]; exact (Pre.ofNat_toNat64 _).symm) (by rw [X.hQ]; exact z _)
    (by rw [X.hQL]; exact (Pre.ofNat_toNat64 _).symm) (by rw [X.hIn]; exact z _) (by rw [X.hQI]; exact z _)
    (by omega_arith) (by omega_arith) hp1 (by omega_arith) hq1 (by omega_arith)
    ⟨by rw [rd0]; exact hP.rN, hP.sN⟩ ⟨by rw [rd0]; exact hP.rP, hP.sP⟩ ⟨by rw [rd0]; exact hP.rQ, hP.sQ⟩
    ⟨by rw [rd0]; exact hP.rPre, hP.sPre⟩
    ⟨fun i hi => by rw [rd0]; exact hP.rPre i (by omega_arith), fun i hi => hP.sPre i (by omega_arith)⟩)
    fun t₁ ⟨⟨v0, w0, v1, v4, v5, v6, v7, t1, t4, t5, t6, t7, O1, a7₁⟩, k1⟩ => ?_)
  rw [bN] at v1
  rw [bP] at v4
  rw [bQ] at v5
  rw [bI] at v6
  rw [bQI] at v7
  obtain F1 : Frame [preR s₀, scrR s₀] s₀.mem t₁.mem := X.frame.trans (frame_of_outside O1 (by omega_arith))
  obtain hQb := Crt.os2ip_lt' (qB s₀) (VG.Proof.Bignum.bytesAt_length _ _ _)
  obtain hPb := Crt.os2ip_lt' (pB s₀) (VG.Proof.Bignum.bytesAt_length _ _ _)
  obtain hw16 : 16 * ck s₀ ≤ 64 * cwX s₀ := by omega_arith
  obtain hd1 : ∀ d, d + 8 ≤ 256 → Mont.word t₁.mem (cS s₀) d = Mont.word x.mem (cS s₀) d := fun d hd =>
    O1.word (Or.inl hd) (by omega_arith)
  -- The factors' widths.
  obtain hs₁ := X.scr.congr k1.2.2
  obtain r6 : t₁.gpr .s6 = cS s₀ := (k1.gpr (by decide)).trans X.s6
  obtain rPL : t₁.mem.readW (off (cS s₀) oPLen) 64 = BitVec.ofNat 64 (cpL s₀) := by
    rw [show t₁.mem.readW (off (cS s₀) oPLen) 64 = Mont.word t₁.mem (cS s₀) oPLen from rfl,
      hd1 _ (by unfold oPLen; omega_arith), X.hPL]; exact (Pre.ofNat_toNat64 _).symm
  obtain rQL : t₁.mem.readW (off (cS s₀) oQLen) 64 = BitVec.ofNat 64 (cqL s₀) := by
    rw [show t₁.mem.readW (off (cS s₀) oQLen) 64 = Mont.word t₁.mem (cS s₀) oQLen from rfl,
      hd1 _ (by unfold oQLen; omega_arith), X.hQL]; exact (Pre.ofNat_toNat64 _).symm
  refine WP.seq (WP.mono (WP.keep [.a3, .t1] (Q := fun t => t.gpr .a3 = BitVec.ofNat 64 ((cpL s₀ + 7) / 8) ∧
      t.gpr .t1 = BitVec.ofNat 64 ((cqL s₀ + 7) / 8) ∧ t.mem = t₁.mem) (by
    unfold PrivPre.pqLens
    have rPL' : t₁.mem.readW (off (cS s₀) 40) 64 = BitVec.ofNat 64 (cpL s₀) := rPL
    have rQL' : t₁.mem.readW (off (cS s₀) 56) 64 = BitVec.ofNat 64 (cqL s₀) := rQL
    brun [oPLen, oQLen, r6, rPL', rQL', len_words (cpL s₀) (by omega_arith), len_words (cqL s₀) (by omega_arith),
      hs₁.ld (show 40 + 8 ≤ cZ s₀ by omega_arith), hs₁.al8 (show 40 + 8 ≤ cZ s₀ by omega_arith) (by decide),
      hs₁.ld (show 56 + 8 ≤ cZ s₀ by omega_arith), hs₁.al8 (show 56 + 8 ≤ cZ s₀ by omega_arith) (by decide)])
    (by rfl) (by rfl))
    fun t₁' ⟨⟨l3, l1, lm⟩, kl⟩ => ?_)
  obtain k1' := k1.trans kl
  rw [← lm] at v0 w0 v1 v4 v5 v6 v7 t1 t6 t7
  obtain hd1' : ∀ d, d + 8 ≤ 256 → Mont.word t₁'.mem (cS s₀) d = Mont.word x.mem (cS s₀) d := fun d hd => by
    rw [lm]; exact hd1 d hd
  -- `p` and `q` fit in their widths.
  obtain fit : ∀ {j L : Nat} {bs : List Byte}, bs.length = L → 1 ≤ L → L < ck s₀ →
      wordsVal t₁'.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) = Spec.Rsa.os2ip bs →
      wordsVal t₁'.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) =
        wordsVal t₁'.mem (cS s₀) (slot (cwX s₀) j) ((L + 7) / 8) := fun {j L bs} hl hL1 hLk hv => by
    obtain hlt : Spec.Rsa.os2ip bs < 2 ^ (64 * ((L + 7) / 8)) := by
      refine Nat.lt_of_lt_of_le (Crt.os2ip_lt' bs hl) ?_
      rw [VG.Proof.Bignum.pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
    obtain a := wordsVal_app t₁'.mem (cS s₀) (slot (cwX s₀) j) ((L + 7) / 8) (cwX s₀ - (L + 7) / 8)
    rw [show (L + 7) / 8 + (cwX s₀ - (L + 7) / 8) = cwX s₀ by omega_arith] at a
    rw [a] at hv ⊢
    obtain hpos := Nat.two_pow_pos (64 * ((L + 7) / 8))
    rcases Nat.eq_zero_or_pos (wordsVal t₁'.mem (cS s₀) (slot (cwX s₀) j + 8 * ((L + 7) / 8))
      (cwX s₀ - (L + 7) / 8)) with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero]
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * ((L + 7) / 8))) h; omega_arith
  -- The checks.
  refine WP.seq (WP.mono (checksWith_ok (pq := PrivPre.checkPQs) (Na := s₀.gpr .a2) (k := ck s₀) (nb := nB s₀)
    (hs₁.congr kl.2.2) hZ8 (by omega_arith) hwX ((k1'.gpr (by decide)).trans X.s6)
    ((kl.gpr (by decide)).trans a7₁)
    ((k1'.gpr (by decide)).trans X.ra) ((k1'.gpr (by decide)).trans X.s5) ((k1'.gpr (by decide)).trans X.t0)
    (by rw [hd1' _ (by unfold oN; omega_arith), X.hN]; exact z _)
    (by rw [hd1' _ (by unfold oNLen; omega_arith), X.hNL]; exact (Pre.ofNat_toNat64 _).symm) hk hk'
    (VG.Proof.Bignum.bytesAt_length _ _ _) (fun i hi => by rw [k1'.2.1, k1'.2.2, rd0]; exact hP.rN i hi)
    (fun i hi => by
      rw [lm, F1.bytes (R := ⟨s₀.gpr .a2, ck s₀⟩) (dis dPN dNS) (Nat.le_of_lt (BitVec.isLt _)) hi]
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range])
    v1 t6 t7
    (checkPQs_ok (hs₁.congr kl.2.2) hZ8 hwX l3 l1 (by omega_arith) (by omega_arith) (by omega_arith)
      (fit (VG.Proof.Bignum.bytesAt_length _ _ _) hp1 hpk v4) (fit (VG.Proof.Bignum.bytesAt_length _ _ _) hq1 hqk v5)
      t6 t1))
    fun t₂ ⟨X2, k2⟩ => ?_)
  rw [v6, v4, v5, v7, crtMask_zero] at X2
  obtain k12 := k1'.trans k2
  obtain Xfr : Frm (cS s₀) (Crt.chkR (cwX s₀)) t₁.mem t₂.mem := lm ▸ X2.fr
  obtain F2 : Frame [preR s₀, scrR s₀] s₀.mem t₂.mem := F1.trans (frame_of_frm Xfr fun r hr => by
    simp only [Crt.chkR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [oMask] <;> omega_arith)
  obtain hd2 : ∀ d, d + 8 ≤ oMask → Mont.word t₂.mem (cS s₀) d = Mont.word x.mem (cS s₀) d := fun d hd => by
    exact (Frm.word_eq Xfr (fun r hr => by
      simp only [Crt.chkR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [oMask] at hd ⊢ <;> omega_arith) (by unfold oMask at hd; omega_arith)).trans
      (hd1 d (by unfold oMask at hd; omega_arith))
  obtain hd3 : ∀ d, oMask + 8 ≤ d → d + 8 ≤ 256 → Mont.word t₂.mem (cS s₀) d = Mont.word x.mem (cS s₀) d :=
    fun d hd hd' => by
      exact (Frm.word_eq Xfr (fun r hr => by
        simp only [Crt.chkR, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [oMask] at hd ⊢ <;> omega_arith) (by omega_arith)).trans (hd1 d hd')
  refine hc t₂ ⟨X.scr.congr k12.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, X2.msk,
    (k12.gpr (by decide)).trans X.s6, (k12.gpr (by decide)).trans X.s11, by rw [X2.v4, v4], by rw [X2.v5, v5], (X.keep.trans k12).mono (by decide), fun i hi => ?_, F2⟩
  · rw [hd2 _ (by decide), X.hOut]
  · rw [hd2 _ (by decide), X.hN]
  · rw [hd2 _ (by decide), X.hNL]
  · rw [hd2 _ (by decide), X.hPL]
  · rw [hd2 _ (by decide), X.hQL]
  · rw [hd3 _ (by decide) (by decide), X.hBP]
  · rw [hd3 _ (by decide) (by decide), X.hBQ]
  · have esav : off (savW (cS s₀)) (8 * i) = off (cS s₀) (112 + 8 * i) := by
      simp only [off, savW]; rw [Offset.add_add]
    obtain h1 := X.sav i hi
    change x.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = _ at h1
    change t₂.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = _
    rw [esav] at h1 ⊢
    change Mont.word t₂.mem (cS s₀) (112 + 8 * i) = _
    change Mont.word x.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [hd3 _ (by unfold oMask; omega_arith) (by omega_arith)]
    exact h1

end VG.Proof.Bignum.RISCV64.PrivPre
