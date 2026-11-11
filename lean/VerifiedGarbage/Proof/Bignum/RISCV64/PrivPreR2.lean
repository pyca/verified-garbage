module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPower
public import VerifiedGarbage.Impl.Bignum.RISCV64.PrivPre
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PrimeR2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.ModArith

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
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have hN0 : 0 < N := by omega
  let Inv : Nat → State → Prop := fun j t =>
    wordsVal t.mem B (slot w 1) w = x * 2 ^ j % N ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep dblLoopRegs s t
  refine wp_countdown (cnt := .a1) (N := M) hM' hM Inv (fun j _ t ⟨tx, to, tk⟩ _ => ?_)
    ⟨by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hxN]; exact hx, Outside.refl _ _ _ _, Keep.refl _ _⟩ h1
  have n0 : wordsVal t.mem B (slot w 0) w = N := by rw [Outside.wordsVal to (by omega) (by omega), hN]
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
  have hNR : N < 2 ^ (64 * w) := h.n ▸ wordsVal_lt _ _ _ _
  have e24 := slot24 w
  have sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  have s34 := slot_lt (w := w) (show 3 < 4 by decide)
  have s37 := slot_lt (w := w) (show 3 < 7 by decide)
  have s03 := slot_lt (w := w) (show 0 < 3 by decide)
  have s45 := slot_lt (w := w) (show 4 < 5 by decide)
  have s424 := slot_lt (w := w) (show 4 < 24 by decide)
  unfold PrivPre.subST
  -- `S - T` into array 3.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (top0_ok h (j := 4) (by decide)) fun t₇ ⟨m7, k7⟩ => ?_
  have ow7 : Outside B (slot w 4) (8 * (w + 1)) t.mem t₇.mem := by
    rw [m7]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)
  have c7 := h.of k7 (by decide) (arrO_n ow7 (by omega_arith) (by decide) (by decide))
  have u7 : ∀ j < 24, j ≠ 4 → A t₇.mem B w j = A t.mem B w j := fun j hj hne => arr_n ow7 (by omega_arith) hj hne hn
  have s7 : A t₇.mem B w 4 = A t.mem B w 4 := by
    rw [m7]; exact Outside.wordsVal (writeW_outside _ _ _ (by omega_arith)) (Or.inl (Nat.le_refl _)) (by omega_arith)
  have top7 : Mont.word t₇.mem B (slot w 4 + 8 * w) = 0 := by rw [m7]; exact word_writeW_self _ _ _ _
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) c7.a7 c7.s5 4) fun t₈ ⟨⟨a5, m8⟩, k8⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k8.gpr (by decide)).trans c7.a7)
    ((k8.gpr (by decide)).trans c7.s5) 3) fun t₉ ⟨⟨a6, m9⟩, k9⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a7) (by decide) ((k9.gpr (by decide)).trans ((k8.gpr (by decide)).trans c7.a7))
    ((k9.gpr (by decide)).trans ((k8.gpr (by decide)).trans c7.s5)) 7) fun t₁₀ ⟨⟨a7, m10⟩, k10⟩ => ?_
  have hm10 : t₁₀.mem = t₇.mem := by rw [m10, m9, m8]
  have k810 := (k8.trans k9).trans k10
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 4) (dT := slot w 3) (dM := slot w 7)
    (c7.scr.congr k810.2.2) ((k10.gpr (by decide)).trans ((k9.gpr (by decide)).trans a5))
    ((k10.gpr (by decide)).trans a6) a7 ((k810.gpr (by decide)).trans c7.t0) (by omega_arith) hw'
    (slot_al w 4) (slot_al w 3) (slot_al w 7) (by have := sl 4 (by decide); omega_arith)
    (by have := sl 3 (by decide); omega_arith) (by have := sl 7 (by decide); omega_arith)
    (Or.inl (by omega_arith)) (Or.inl (by omega_arith))) fun t₁₁ ⟨⟨c, hc, hD, h4⟩, o11, k11⟩ => ?_)
  rw [hm10] at hD h4 o11
  rw [top7] at h4
  have k711 := (k7.trans k810).trans k11
  have ra11 : t₁₁.gpr .ra = off B (slot w 0) := by rw [k711.gpr (by decide), hra]
  -- `p` added back under the borrow.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.a7] (Q := fun u => u.gpr .a7 = off B (slot w 0) ∧ u.mem = t₁₁.mem)
    (by brun [ra11, BitVec.add_zero]) (by rfl) (by rfl)) fun t₁₂ ⟨⟨b7, m12⟩, k12'⟩ => ?_
  have o12 : WinO B w t₇.mem t₁₂.mem := by rw [m12]; exact arrO o11 (by decide) (by decide)
  have c12 : WCtx t₁₂ B Z w N := by
    exact c7.of7 ((k810.trans k11).trans k12') (by decide) b7 o12
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c12.a7 c12.s5 3) fun t₁₃ ⟨⟨b3, m13⟩, k13⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k13.gpr (by decide)).trans c12.a7)
    ((k13.gpr (by decide)).trans c12.s5) 0) fun t₁₄ ⟨⟨b4, m14⟩, k14'⟩ => ?_
  have k1314 := k13.trans k14'
  have hm14 : t₁₄.mem = t₁₂.mem := by rw [m14, m13]
  have c14 := c12.regs k1314 (by decide) hm14
  have hm : t₁₄.gpr .s4 = if decide (0 < c) then BitVec.allOnes 64 else 0 := by
    rw [k1314.gpr (by decide), k12'.gpr (by decide), h4]; simp
  refine WP.seq (WP.mono (ModArith.addMask64_ok (b := decide (0 < c)) c14.scr ((k14'.gpr (by decide)).trans b3) b4
    c14.t0 hm (slot_al w 3) (slot_al w 0) (by omega_arith) hw' (by have := sl 3 (by decide); omega_arith)
    (by have := sl 0 (by decide); omega_arith) (Or.inr (by omega_arith))) fun t₁₅ ⟨d15, o15, k15⟩ => ?_)
  rw [hm14, m12] at d15
  rw [hm14] at o15
  have c15 := c14.of k15 (by decide) (by rw [hm14]; exact arrO o15 (by decide) (by decide))
  -- Back into array 4.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c15.a7 c15.s5 4) fun t₁₆ ⟨⟨d3, m16⟩, k16⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k16.gpr (by decide)).trans c15.a7)
    ((k16.gpr (by decide)).trans c15.s5) 3) fun t₁₇ ⟨⟨d4, m17⟩, k17⟩ => ?_
  have k1617 := k16.trans k17
  have hm17 : t₁₇.mem = t₁₅.mem := by rw [m17, m16]
  have c17 := c15.regs k1617 (by decide) hm17
  refine WP.mono (copySame_ok (dS := slot w 3) (dD := slot w 4) c17.scr d4 ((k17.gpr (by decide)).trans d3)
    c17.t0 (by omega_arith) hw' (slot_al w 3) (slot_al w 4) (by have := sl 3 (by decide); omega_arith)
    (by have := sl 4 (by decide); omega_arith) (Or.inl (by omega_arith))) fun u ⟨⟨c18, o18⟩, k18⟩ => ?_
  rw [hm17] at c18 o18
  have cu := c17.of k18 (by decide) (by rw [hm17]; exact arrO o18 (by decide) (by decide))
  have kall := (((((k7.trans k810).trans k11).trans k12').trans k1314).trans k15).trans (k1617.trans k18)
  have hN11 : wordsVal t₁₁.mem B (slot w 0) w = N := by
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
  have h0 : ((S' + N - T) % N * R ^ (i + 1) + (V + R ^ i * C)) % N =
      ((S' + N - T) * R ^ (i + 1) + (V + R ^ i * C)) % N := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  rw [h0, ← Nat.zero_mod N]
  have d1 := VG.ModArith.dvd_sub_of_mod_eq hS'
  have d2 := VG.ModArith.dvd_sub_of_mod_eq hT
  have d3 := VG.ModArith.dvd_sub_of_mod_eq (show (S * R ^ i + V) % N = 0 % N by rw [hS, Nat.zero_mod])
  refine VG.ModArith.mod_eq_of_dvd_sub ?_
  have hle : T ≤ S' + N := by omega
  have e : ((0 : Nat) : Int) - (((S' + N - T) * R ^ (i + 1) + (V + R ^ i * C) : Nat) : Int) =
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
  have hxt := hx.congr I.keep.2.2
  have hxn := hx.nowrap
  have hwi : w * i + w ≤ w * nChunks K w := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  unfold PrivPre.chunkStep1
  -- The chunk into array 6, and `s9` past it.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h.a7 h.s5 6) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = t₁.gpr .s9 ∧ u.mem = t₁.mem)
    (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun t₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : t₂.mem = t.mem := by rw [m2, m1]
  have hx2 := hxt.congr k12.2.2
  refine WP.seq (WP.mono (Pub.copyIn_ok (B := B) (P := BX) (Zp := ZX) (dS := slot wX 6 + 8 * (w * i))
    (dD := slot w 6) (w := w) (h.scr.congr k12.2.2) hxn (fun j hj => hx2.ld (by omega_arith))
    (fun j hj => hx2.al8 (by omega_arith) (by have := slot_al wX 6; omega_arith))
    (by rw [a4, k1.gpr (by decide), I.s9]) ((k2.gpr (by decide)).trans a3) ((k12.gpr (by decide)).trans h.t0)
    (by omega_arith) hw' (slot_al w 6) (by omega_arith) (by have := sl 6 (by decide); omega_arith) hsep)
    fun t₃ ⟨⟨_, a4', c3, o3⟩, k3⟩ => ?_)
  rw [hm2] at c3 o3
  refine WP.seq (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = t₃.gpr .t4 ∧ u.mem = t₃.mem)
    (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun t₄ ⟨⟨a9, m4⟩, k4⟩ => ?_)
  have k14 := (k12.trans k3).trans k4
  have o4 : Outside B (slot w 6) (8 * w) t.mem t₄.mem := by rw [m4]; exact o3
  have c4 := h.of k14 (by decide) (arrO o4 (by decide) (by decide))
  have v6 : A t₄.mem B w 6 = wordsVal s.mem BX (slot wX 6 + 8 * (w * i)) w := by
    show wordsVal _ _ _ _ = _
    rw [m4, wv_words c3]
    exact x_wv I.out hsep h.hZ hxn (by omega_arith)
  have u4 : ∀ j < 24, j ≠ 6 → A t₄.mem B w j = A t.mem B w j := fun j hj hne => arr_out o4 hj hne hn
  have one4 : A t₄.mem B w 1 = 1 := by rw [u4 1 (by decide) (by decide), I.one]
  -- `T := C 1 R⁻¹`.
  refine WP.seq (WP.mono (c4.mont (o := 7) (a := 6) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [one4]; omega_arith))
    fun t₅ ⟨⟨c5, l5, e5, v5, o5⟩, k5⟩ => ?_)
  rw [v6, one4] at e5
  have one5 : A t₅.mem B w 1 = 1 := by
    rw [v5 1 (by decide) (by decide) (by decide) (by decide), one4]
  -- `S := S 1 R⁻¹`.
  refine WP.seq (WP.mono (c5.mont (o := 4) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [one5]; omega_arith))
    fun t₆ ⟨⟨c6, l6, e6, v6', o6⟩, k6⟩ => ?_)
  have s5' : A t₅.mem B w 4 = A t.mem B w 4 := by
    rw [v5 4 (by decide) (by decide) (by decide) (by decide), u4 4 (by decide) (by decide)]
  rw [one5, s5'] at e6
  have T6 : A t₆.mem B w 7 = A t₅.mem B w 7 := v6' 7 (by decide) (by decide) (by decide) (by decide)
  have ra6 : t₆.gpr .ra = off B (slot w 0) := by
    rw [k6.gpr (by decide), k5.gpr (by decide), k14.gpr (by decide), I.ra]
  -- `S := S - T mod p`.
  refine WP.seq (WP.mono (subST_ok c6 ra6 l6 (by rw [T6]; exact l5)) fun t₇ ⟨⟨c7, ra7, e7, v7, o7⟩, k7⟩ => ?_)
  -- The count.
  refine WP.mono (WP.keep [.s10, .t2] (Q := fun u => u.gpr .s10 = t₇.gpr .s10 - BitVec.ofNat 64 w ∧
      u.gpr .t2 = (t₇.gpr .s10 - BitVec.ofNat 64 w - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1 ∧
      u.mem = t₇.mem)
    (by brun [c7.t0]) (by rfl) (by rfl)) fun u ⟨⟨f10, f2, mu⟩, kf⟩ => ?_
  have cu := c7.regs kf (by decide) mu
  have k5f := ((k5.trans k6).trans k7).trans kf
  have hwi1 : w * (i + 1) = w * i + w := Nat.mul_succ _ _
  have hpow : (2 ^ (64 * w)) ^ i = 2 ^ (64 * (w * i)) := by rw [← Nat.pow_mul, Nat.mul_assoc]
  have hU : ∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ 4 → j ≠ 6 → j ≠ 7 → A u.mem B w j = A t.mem B w j := by
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
  have e24 := slot24 w
  have sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  have s14 := slot_lt (w := w) (show 1 < 4 by decide)
  have s424 := slot_lt (w := w) (show 4 < 24 by decide)
  unfold r2FastP
  -- `x := 1`.
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = off B (slot w 1) ∧ t.mem = s.mem)
    (by brun [h2, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (h.scr.congr k1.2.2) a3 ((k1.gpr (by decide)).trans h.t0) (by omega_arith)
    hw' (slot_al w 1) (by have := sl 1 (by decide); omega_arith)) fun s₂ ⟨⟨_, hz, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have hs₂ := h.scr.congr k12.2.2
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.s0] (Q := fun t => t.mem = s₂.mem.writeW (off B (slot w 1)) (BitVec.ofNat 64 1))
    (by brun [Pub.pub_li1, (k12.gpr (by decide)).trans h2, BitVec.add_zero,
      hs₂.st (d := slot w 1) (n := 8) (by have := sl 1 (by decide); omega_arith),
      hs₂.al8 (d := slot w 1) (by have := sl 1 (by decide); omega_arith) (slot_al w 1)])
    (by rfl) (by rfl)) fun s₃ ⟨m3, k3⟩ => ?_
  have k13 := k12.trans k3
  have x3 : A s₃.mem B w 1 = 1 := by
    rw [m3]; exact Pub.one_word _ _ _ (by omega_arith) (by omega_arith) hz
  have o3 : Outside B (slot w 1) (8 * w) s.mem s₃.mem := by
    rw [m3]; rw [m1] at o2
    exact o2.trans ((writeW_outside s₂.mem B (d := slot w 1) _ (by omega_arith)).mono (by omega_arith)
      (by omega_arith))
  have c3 := h.of k13 (by decide) (arrO o3 (by decide) (by decide))
  -- `S := 0`.
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c3.a7 c3.s5 4) fun s₄ ⟨⟨d3, m4⟩, k4⟩ => ?_
  refine WP.seq (WP.mono (zeroWords_ok (c3.scr.congr k4.2.2) d3 ((k4.gpr (by decide)).trans c3.t0) (by omega_arith)
    hw' (slot_al w 4) (by have := sl 4 (by decide); omega_arith)) fun s₅ ⟨⟨_, z5, o5⟩, k5⟩ => ?_)
  rw [m4] at o5
  have c5 := c3.of (k4.trans k5) (by decide) (arrO o5 (by decide) (by decide))
  have v4 : A s₅.mem B w 4 = 0 := wordsVal_zero z5
  have u5 : ∀ j < 24, j ≠ 4 → A s₅.mem B w j = A s₃.mem B w j := fun j hj hne => arr_out o5 hj hne hn
  have u3 : ∀ j < 24, j ≠ 1 → A s₃.mem B w j = A s.mem B w j := fun j hj hne => arr_out o3 hj hne hn
  -- `s9` and `s10`.
  have k15 := (k13.trans k4).trans k5
  have o05 : WinO B w s.mem s₅.mem := (arrO o3 (by decide) (by decide)).trans (arrO o5 (by decide) (by decide))
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (xbase_ok (rd := .s9) (by decide) ((k15.gpr (by decide)).trans h6)
    ((k15.gpr (by decide)).trans h11) 6) fun s₆ ⟨⟨a9, m6⟩, k6⟩ => ?_
  refine WP.mono (WP.keep [.s10] (Q := fun u => u.gpr .s10 = BitVec.ofNat 64 W ∧ u.mem = s₆.mem)
    (by
      brun [(k6.gpr (by decide)).trans ((k15.gpr (by decide)).trans h11)]
      rw [hwX, w_of_s11 hW'])
    (by rfl) (by rfl)) fun s₇ ⟨⟨a10, m7⟩, k7⟩ => ?_
  have hm7 : s₇.mem = s₅.mem := by rw [m7, m6]
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
  have sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  have s47 := slot_lt (w := w) (show 4 < 7 by decide)
  unfold PrivPre.negS
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h.a7 h.s5 7) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h.a7)
    ((k1.gpr (by decide)).trans h.s5) 4) fun t₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : t₂.mem = t.mem := by rw [m2, m1]
  have c2 := h.regs k12 (by decide) hm2
  refine WP.seq (WP.mono (copySame_ok (dS := slot w 4) (dD := slot w 7) c2.scr a4 ((k2.gpr (by decide)).trans a3)
    c2.t0 (by omega_arith) hw' (slot_al w 4) (slot_al w 7) (by have := sl 4 (by decide); omega_arith)
    (by have := sl 7 (by decide); omega_arith) (Or.inl (by omega_arith))) fun t₃ ⟨⟨c3, o3⟩, k3⟩ => ?_)
  rw [hm2] at c3 o3
  have c3' := c2.of k3 (by decide) (by rw [hm2]; exact arrO o3 (by decide) (by decide))
  have v7 : A t₃.mem B w 7 = A t.mem B w 4 := by show wordsVal _ _ _ _ = _; rw [wv_words c3]
  have u3 : ∀ j < 24, j ≠ 7 → A t₃.mem B w j = A t.mem B w j := fun j hj hne => arr_out o3 hj hne hn
  -- `S := 0`.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .t3) (by decide) c3'.a7 c3'.s5 4) fun t₄ ⟨⟨d3, m4⟩, k4⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (c3'.scr.congr k4.2.2) d3 ((k4.gpr (by decide)).trans c3'.t0) (by omega_arith)
    hw' (slot_al w 4) (by have := sl 4 (by decide); omega_arith)) fun t₅ ⟨⟨_, z5, o5⟩, k5⟩ => ?_)
  rw [m4] at o5
  have c5 := c3'.of (k4.trans k5) (by decide) (arrO o5 (by decide) (by decide))
  have v4 : A t₅.mem B w 4 = 0 := wordsVal_zero z5
  have u5 : ∀ j < 24, j ≠ 4 → A t₅.mem B w j = A t₃.mem B w j := fun j hj hne => arr_out o5 hj hne hn
  have k15 := (k12.trans k3).trans ((k4.trans k5))
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
  have hYS : (Y + S) % N = 0 := by
    subst hY
    rcases Nat.eq_zero_or_pos S with rfl | hpos
    · simp
    · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : N - S < N), Nat.sub_add_cancel (by omega), Nat.mod_self]
  have d1 := VG.ModArith.dvd_sub_of_mod_eq (show (Y + S) % N = 0 % N by rw [hYS, Nat.zero_mod])
  have d2 := VG.ModArith.dvd_sub_of_mod_eq (show (S * R + V) % N = 0 % N by rw [hS, Nat.zero_mod])
  have d3 := VG.ModArith.dvd_sub_of_mod_eq hV
  refine VG.ModArith.mod_eq_of_dvd_sub ?_
  have e : (((2 ^ E * R : Nat) : Int) - ((Y * R : Nat) : Int)) =
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
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega)]
  constructor
  · intro h
    refine Nat.lt_of_not_le fun hc => h ?_
    rw [show 2 ^ 64 - e + a = (a - e) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    exact Nat.div_eq_of_lt (by omega)
  · intro h
    rw [Nat.mod_eq_of_lt (by omega)]
    exact Nat.ne_of_gt (Nat.div_pos (by omega) (by decide))

theorem gt_bne {a e : Nat} (ha : a < 2 ^ 62) (he : e < 2 ^ 62) :
    (((BitVec.ofNat 64 a - BitVec.ofNat 64 e) >>> 63) != 0) = decide (a < e) := by
  have hg := gt_flag ha he
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
  have hmj : w * (j + 1) ≤ e := Nat.le_trans (Nat.mul_le_mul_left _ hj) hZe
  have e10 : v.gpr .s10 - BitVec.ofNat 64 w = BitVec.ofNat 64 (e - w * (j + 1)) := by
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
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hra' : s.gpr .ra = off B (slot w 0) := (hk.gpr (by decide)).symm.trans hra
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
    have he : w * 2 ^ (j + 1) = 2 * (w * 2 ^ j) := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2]
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
    have h6' : w * 2 ^ 6 = 64 * w := by rw [show (2 : Nat) ^ 6 = 64 from rfl, Nat.mul_comm]
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
  have sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => c.sl hj
  have hN0 : 0 < N := by omega_arith
  -- The bases, and whether `w < E`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) c.a7 c.s5 1) fun t₅ ⟨⟨b2, m5⟩, k5⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k5.gpr (by decide)).trans c.a7)
    ((k5.gpr (by decide)).trans c.s5) 2) fun t₆ ⟨⟨b5, m6⟩, k6⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) (((k5.trans k6).gpr (by decide)).trans c.a7)
    (((k5.trans k6).gpr (by decide)).trans c.s5) 3) fun t₇ ⟨⟨b6, m7⟩, k7⟩ => ?_
  have k57 := (k5.trans k6).trans k7
  refine WP.mono (WP.keep [.t2] (Q := fun v =>
      v.gpr .t2 = (BitVec.ofNat 64 w - BitVec.ofNat 64 E) >>> 63 ∧ v.mem = t₇.mem)
    (by brun [(k57.gpr (by decide)).trans h10, (k57.gpr (by decide)).trans c.t0]) (by rfl) (by rfl))
    fun t₈ ⟨⟨f2, m8⟩, k8⟩ => ?_
  have hm8 : t₈.mem = u.mem := by rw [m8, m7, m6, m5]
  have k58 := k57.trans k8
  have c8 := c.regs k58 (by decide) hm8
  have a2' : t₈.gpr .a2 = off B (slot w 1) :=
    (k8.gpr (by decide)).trans ((k7.gpr (by decide)).trans ((k6.gpr (by decide)).trans b2))
  have a5' : t₈.gpr .a5 = off B (slot w 2) := (k8.gpr (by decide)).trans ((k7.gpr (by decide)).trans b5)
  have a6' : t₈.gpr .a6 = off B (slot w 3) := (k8.gpr (by decide)).trans b6
  have ra8 : t₈.gpr .ra = off B (slot w 0) := (k58.gpr (by decide)).trans hra
  have h10' : t₈.gpr .s10 = BitVec.ofNat 64 E := (k58.gpr (by decide)).trans h10
  have k8' : Keep r2FRegs s t₈ := Keep.within hk k58 (by decide)
  have hl8 : A t₈.mem B w 1 < N := by rw [hm8]; exact hl
  have hx8 : G → A t₈.mem B w 1 % N = 2 ^ (64 * E) % N := by rw [hm8]; exact hx
  have fix8 : ∀ j < 24, 7 < j → A t₈.mem B w j = A s.mem B w j := fun j hj h7 => by rw [hm8]; exact hfix j hj h7
  have o8 : WinO B w s.mem t₈.mem := by rw [hm8]; exact ho
  -- `M` doublings of `Y`.
  have dbl : ∀ (v : State) (M : Nat), WCtx v B Z w N → v.mem = t₈.mem → Keep r2FRegs s v →
      v.gpr .a1 = BitVec.ofNat 64 M → 0 < M → M < 2 ^ 64 → v.gpr .a2 = off B (slot w 1) →
      v.gpr .a5 = off B (slot w 2) → v.gpr .a6 = off B (slot w 3) → v.gpr .ra = off B (slot w 0) →
      WP isa PrivPre.dblLoop v fun t => (WCtx t B Z w N ∧ t.gpr .ra = off B (slot w 0) ∧
        A t.mem B w 1 = A t₈.mem B w 1 * 2 ^ M % N ∧
        (∀ j < 24, 7 < j → A t.mem B w j = A s.mem B w j) ∧ WinO B w s.mem t.mem) ∧ Keep r2FRegs s t := by
    intro v M cv mv kv d1 hM hM' v2 v5 v6 vra
    refine WP.mono (dblAny_ok (x := A t₈.mem B w 1) cv.scr v5 v6 cv.a7 v2 cv.t0 (by omega_arith) hw'
      (by have := sl 3 (by decide); have := slot_lt (w := w) (show 3 < 4 by decide); unfold slot at *; omega_arith)
      cv.n (by rw [mv]) hl8 d1 hM hM') fun t ⟨x9, o9, k9⟩ => ?_
    have O9 : WinO B w v.mem t.mem := o9.mono (Nat.le_refl _) (by omega_arith)
    refine ⟨⟨cv.of k9 (by decide) O9, by rw [k9.gpr (by decide), vra], x9, fun j hj h7 => ?_,
      by rw [← mv] at o8; exact o8.trans O9⟩, Keep.within kv k9 (by decide)⟩
    have := slot_lt (w := w) hj
    have es : slot w j = hdrBytes + j * (8 * (w + 2)) := rfl
    have es1 : slot w 1 = hdrBytes + 8 * (w + 2) := by unfold slot; omega_arith
    have h8 := Nat.mul_le_mul_right (8 * (w + 2)) (show 8 ≤ j by omega_arith)
    rw [show A t.mem B w j = A v.mem B w j from
      Outside.wordsVal o9 (Or.inr (by omega_arith)) (by omega_arith), mv]
    exact fix8 j hj h7
  refine WP.ite (decide (w < E)) (by rw [Steps.eval_nonzero, f2, gt_bne (by omega_arith) (by omega_arith)])
    (fun hb => ?_) (fun hb => ?_)
  · -- `64 (2 w - E)` doublings.
    have hwE : w < E := of_decide_eq_true hb
    refine WP.seq (WP.mono (WP.keep [.a1] (Q := fun v =>
        v.gpr .a1 = BitVec.ofNat 64 (64 * (2 * w - E)) ∧ v.mem = t₈.mem)
      (by
        brun [c8.t0, h10']
        rw [shl_ofNat, Nat.pow_one, sub_ofNat (by omega_arith), shl_ofNat]) (by rfl) (by rfl)) fun t₉ ⟨⟨d1, m9⟩, k9⟩ => ?_)
    have c9 := c8.regs k9 (by decide) m9
    have k9' : Keep r2FRegs s t₉ := Keep.within k8' k9 (by decide)
    have hexp : 64 * E + 64 * (2 * w - E) = 128 * w := by omega_arith
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
    have hEw : E ≤ w := by have := of_decide_eq_false hb; omega_arith
    refine WP.seq (WP.mono (WP.keep [.a1] (Q := fun v =>
        v.gpr .a1 = BitVec.ofNat 64 (64 * (w - E) + w) ∧ v.mem = t₈.mem)
      (by
        brun [c8.t0, h10']
        rw [sub_ofNat hEw, shl_ofNat, BitVec.ofNat_add_ofNat]) (by rfl) (by rfl)) fun t₉ ⟨⟨d1, m9⟩, k9⟩ => ?_)
    have c9 := c8.regs k9 (by decide) m9
    have k9' : Keep r2FRegs s t₉ := Keep.within k8' k9 (by decide)
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
  have sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  have hN0 : 0 < N := by omega_arith
  have hw1 : 1 ≤ w := by omega_arith
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  obtain ⟨hE1, hE2, hEs⟩ := VG.Proof.Bignum.r2E_spec (w := W) (wx := w) hw1 hwW
  rw [r2Fast_eq]
  refine r2FastA_ok h hra h2 hx h6 h11 hwX hW' hN fun u I0 => ?_
  have hK1 : 1 ≤ W := by omega_arith
  have hc0 : 0 < nChunks W w := nChunks_pos hw1 hK1
  have hKn : W ≤ w * nChunks W w := by
    have := le_nChunks_mul (K := W) (w := w) hw1; rw [Nat.mul_comm]; exact this
  have hnK : w * nChunks W w < W + w := by
    have := nChunks_mul_lt (K := W) (w := w) hw1 hK1; rw [Nat.mul_comm]; exact this
  -- The reduction by `x`'s chunks.
  refine WP.seq (WP.mono (count_loop (cr := .t2) hc0 (fun j u => ChunkJ s B BX Z w wX W N j u)
    (fun j hj u I => chunkStep1_ok hx hsep hXZ hK1 hW' hN hj I) I0) fun t I => ?_)
  have he0 : VG.Proof.Bignum.r2E0 W w = 2 * W - w * nChunks W w := by
    unfold VG.Proof.Bignum.r2E0; rw [Nat.mul_comm w]
  have hZE : VG.Proof.Bignum.r2E W w = VG.Proof.Bignum.r2E0 W w - w * VG.Proof.Bignum.r2Z W w := by
    unfold VG.Proof.Bignum.r2E; rw [Nat.mul_comm w]
  have hZe : w * VG.Proof.Bignum.r2Z W w ≤ VG.Proof.Bignum.r2E0 W w := by omega_arith
  have hstep : ∀ j < VG.Proof.Bignum.r2Z W w,
      (2 * w < VG.Proof.Bignum.r2E0 W w - w * (j + 1) ↔ j + 1 < VG.Proof.Bignum.r2Z W w) := fun j hj => by
    rw [Nat.mul_comm w]; exact VG.Proof.Bignum.r2Z_step hw1 hj
  have hEs' : (nChunks W w + VG.Proof.Bignum.r2Z W w) * w + VG.Proof.Bignum.r2E W w = 2 * W := hEs
  generalize hnc : nChunks W w = n at I hXZ hG hKn hnK he0 hEs'
  generalize hE0 : VG.Proof.Bignum.r2E0 W w = e0 at he0 hZE hZe hstep
  -- `e₀`, and whether further reductions follow.
  have h11t : t.gpr .s11 = BitVec.ofNat 64 (8 * (2 * W + 2)) := by
    rw [← hwX]; exact (I.keep.gpr (by decide)).trans h11
  refine WP.seq (WP.mono (WP.keep [.t2, .s10] (Q := fun v => v.gpr .s10 = BitVec.ofNat 64 e0 ∧
      v.gpr .t2 = (BitVec.ofNat 64 (2 * w) - BitVec.ofNat 64 e0) >>> 63 ∧ v.mem = t.mem)
    (by
      brun [I.s10, h11t, I.ctx.t0]
      refine ⟨?_, ?_⟩
      · rw [w_of_s11 hW', e0_word (by omega_arith), he0]
      · rw [w_of_s11 hW', e0_word (by omega_arith), he0, shl_ofNat, Nat.pow_one])
    (by rfl) (by rfl)) fun t₁ ⟨⟨e10, f2, m1⟩, k1⟩ => ?_)
  have c1 := I.ctx.regs k1 (by decide) m1
  have ra1 : t₁.gpr .ra = off B (slot w 0) := (k1.gpr (by decide)).trans I.ra
  have one1 : A t₁.mem B w 1 = 1 := by rw [m1]; exact I.one
  have slt1 : A t₁.mem B w 4 < N := by rw [m1]; exact I.slt
  have sv1 : (A t₁.mem B w 4 * (2 ^ (64 * w)) ^ n + wordsVal s.mem BX (slot wX 6) (w * n)) % N = 0 := by
    rw [m1]; exact I.sv
  have hz : WP isa (.ite (.nonzero .t2) (.loop PrivPre.zStep (.nonzero .t2)) (.block [])) t₁
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
  have k45 := k4.trans k5
  have hm5 : t₅.mem = t₃.mem := by rw [m5, m4]
  have c5 := c3.regs k45 (by decide) hm5
  refine WP.seq (WP.mono (copySame_ok (dS := slot w 4) (dD := slot w 1) c5.scr a4 ((k5.gpr (by decide)).trans a3)
    c5.t0 (by omega_arith) hw' (slot_al w 4) (slot_al w 1) (by have := sl 4 (by decide); omega_arith)
    (by have := sl 1 (by decide); omega_arith)
    (Or.inr (by have := slot_lt (w := w) (show 1 < 4 by decide); omega_arith))) fun t₆ ⟨⟨c6, o6⟩, k6⟩ => ?_)
  rw [hm5] at c6 o6
  have c6' := c5.of k6 (by decide) (by rw [hm5]; exact arrO o6 (by decide) (by decide))
  have y6 : A t₆.mem B w 1 = (0 + N - A t₂.mem B w 4) % N := by
    show wordsVal _ _ _ _ = _; rw [wv_words c6]; exact e3
  have u6 : ∀ j < 24, j ≠ 1 → A t₆.mem B w j = A t₃.mem B w j := fun j hj hne => arr_out o6 hj hne hn
  have k36 := (k3.trans k45).trans k6
  -- The value, if `x ≡ 2^(128 W)`.
  have hval : G → A t₆.mem B w 1 % N = 2 ^ (64 * VG.Proof.Bignum.r2E W w) % N := fun g => by
    refine neg_val (R := (2 ^ (64 * w)) ^ (n + VG.Proof.Bignum.r2Z W w)) (Nat.Coprime.pow_left _ hR)
      J.slt J.sv y6 ?_
    rw [hG g, ← Nat.pow_mul, ← Nat.pow_add]
    have e : 64 * w * (n + VG.Proof.Bignum.r2Z W w) = 64 * ((n + VG.Proof.Bignum.r2Z W w) * w) := by
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
  have hn : B.toNat + slot w 24 ≤ 2 ^ 64 := by have := hs.nowrap; omega_arith
  have hxn := hx.nowrap
  have e24 := slot24' w
  have s01 := slot_lt (w := w) (show 0 < 1 by decide)
  unfold powerPF
  -- The prime into array 0.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = off B (slot w 0) ∧ u.mem = s.mem)
    (by brun [h7, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (xbase_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h6)
    ((k1.gpr (by decide)).trans h11) xj) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  have hx2 := hx.congr k12.2.2
  refine WP.seq (WP.mono (Pub.copyIn_ok (B := B) (P := BX) (Zp := ZX) (dS := slot wX xj) (dD := slot w 0) (w := w)
    (hs.congr k12.2.2) hxn (fun j hj => hx2.ld (by omega_arith))
    (fun j hj => hx2.al8 (by omega_arith) (by have := slot_al wX xj; omega_arith)) a4
    ((k2.gpr (by decide)).trans a3) ((k12.gpr (by decide)).trans ht0) (by omega_arith) hw' (slot_al w 0) hxj
    (by omega_arith) hsep) fun s₃ ⟨⟨_, _, c3, o3⟩, k3⟩ => ?_)
  rw [hm2] at c3 o3
  have v0 : wordsVal s₃.mem B (slot w 0) w = Pv := by rw [wv_words c3, hP]
  have k13 := k12.trans k3
  have h7' : s₃.gpr .a7 = off B (slot w 0) := (k13.gpr (by decide)).trans h7
  have h5' : s₃.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) := (k13.gpr (by decide)).trans h5
  -- `-p⁻¹ mod 2⁶⁴` and the bases.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (minv_ok (hs.congr k13.2.2) h7' (slot_al w 0) (by omega_arith)
    (low_odd (w := w) (by omega_arith) (by rw [v0]; exact hodd))) fun s₄ ⟨⟨inv4, m4⟩, k4⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k4.gpr (by decide)).trans h7')
    ((k4.gpr (by decide)).trans h5') 1) fun s₅ ⟨⟨a2, m5⟩, k5⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k5.gpr (by decide)).trans ((k4.gpr (by decide)).trans h7'))
    ((k5.gpr (by decide)).trans ((k4.gpr (by decide)).trans h5')) 2) fun s₆ ⟨⟨a5, m6⟩, k6⟩ => ?_
  have k46 := (k4.trans k5).trans k6
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k46.gpr (by decide)).trans h7')
    ((k46.gpr (by decide)).trans h5') 3) fun s₇ ⟨⟨a6, m7⟩, k7⟩ => ?_
  have k37 := k46.trans k7
  have hm7 : s₇.mem = s₃.mem := by rw [m7, m6, m5, m4]
  have c7 : WCtx s₇ B Z w Pv := ⟨hs.congr (k13.trans k37).2.2, hw2, hw', hZ, (k37.gpr (by decide)).trans h7',
    (k37.gpr (by decide)).trans h5', (k37.gpr (by decide)).trans ((k13.gpr (by decide)).trans ht0),
    by rw [((k5.trans k6).trans k7).gpr (by decide), hm7]; exact inv4, by rw [hm7]; exact v0⟩
  have k17 := k13.trans k37
  have F7 : PFr B w s.mem s₇.mem := by rw [hm7]; exact o3.mono (Nat.le_refl _) (by omega_arith)
  -- `R² mod p`, by `r2Fast`.
  refine WP.seq (WP.mono (r2Fast_ok (G := G) (W := (k + 7) / 8) (wX := wX) c7 ((k17.gpr (by decide)).trans hra)
    (((k6.trans k7).gpr (by decide)).trans a2) (hx.congr k17.2.2) hsep ((k17.gpr (by decide)).trans h6)
    ((k17.gpr (by decide)).trans h11)
    hwX (by omega_arith) hwk hXZ hP2 hodd (fun g => by rw [x_wv' F7 hsep (by omega_arith) hxn hXZ]; exact hG g))
    fun s₈ ⟨⟨c8, _, _, r8, _, o8⟩, k8⟩ => ?_)
  have F8 : PFr B w s.mem s₈.mem := F7.trans (PFr.of_win o8)
  exact hc s₈ c8 r8 F8 (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within
    (Keep.within (Keep.within (Keep.refl powerFRegs s) k1 (by decide)) k2 (by decide)) k3 (by decide))
    k4 (by decide)) k5 (by decide)) k6 (by decide)) k7 (by decide)) k8 (by decide))

theorem prime_powerPF (xj : Nat) : PrivPre.prime xj = powerPF xj (.seq (.block (base .t4 1 ++
    ([.load .d .t3 .s6 Crt.oDP, .load .d .t1 .s6 Crt.oMask, .addi .t5 .t0 0] : List Instr)))
    (.seq (countLoop .t5 [.load .d .s0 .t4 0, .logic .and .s0 .s0 .t1, .store .d .s0 .t3 0,
      .addi .t3 .t3 8, .addi .t4 .t4 8]) (.block [.store .d .t3 .s6 Crt.oDP]))) := rfl

end VG.Proof.Bignum.RISCV64.Win
