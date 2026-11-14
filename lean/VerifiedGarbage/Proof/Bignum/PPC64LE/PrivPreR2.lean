module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PrivPre
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Prime
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Fast
import VerifiedGarbage.Proof.Bignum.PPC64LE.Double64
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.PrimeR2
import VerifiedGarbage.Proof.Bignum.CrtGPow
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.ModArith

/-!
# An RSA private key's precomputed values on PPC64LE: a factor's `R² mod p` from `R² mod n`

`PrivPre.r2Fast` in a factor's working space at `off BX oA`, from `x = R² mod n`
in `X`'s array 6: `1` into array 1, `S := 0`, the steps of the reduction
(`chunkStep1_ok`, with the invariant `S R^i + x_i ≡ 0` for `x_i` the first `i`
chunks of `x`, as `Crt.chunkStep`'s), the further ones (`zStep`), `-S`
(`negS_ok`), then the doublings (of any value below `p`) and, for few words
left, six Montgomery squares.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE VG.Proof.Bignum.PPC64LE.Crt

/-! ## `S := S - T mod p` -/

/-- The registers `PrivPre.subST` writes. -/
def subRegs : List Reg := [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20, .r24]

/-- `PrivPre.subST`: `S := S - T mod p`, for `S < p` in array 4 and `T < p` in
array 7 of the working space at `B` (array 0 in `r10` and `r21`), changing
only arrays 3 and 4. -/
theorem subST_ok {t : State} {B : Addr} {Z w Pv : Nat} (hs : Scr t B Z) (hZ : slot w 8 ≤ Z) (hw2 : 2 ≤ w)
    (hw' : w < 2 ^ 31) (h10 : t.gpr .r10 = off B (slot w 0)) (h21 : t.gpr .r21 = off B (slot w 0))
    (h29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hP : val32 t.mem B (slot w 0) (2 * w) = Pv) (hS : val32 t.mem B (slot w 4) (2 * w) < Pv)
    (hT : val32 t.mem B (slot w 7) (2 * w) < Pv) :
    WP isa PrivPre.subST t fun u =>
      (val32 u.mem B (slot w 4) (2 * w) =
          (val32 t.mem B (slot w 4) (2 * w) + Pv - val32 t.mem B (slot w 7) (2 * w)) % Pv ∧
        Mont.Outside B (slot w 3) (2 * (8 * (w + 2))) t.mem u.mem ∧ u.gpr .r10 = off B (slot w 0)) ∧
      Keep subRegs t u := by
  have hn := hs.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e3 := e 3; have e4 := e 4; have e5 := e 5; have e8 := e 8
  unfold PrivPre.subST
  refine recP2aFrom_ok (bj := 7) hs hZ (by decide) (by decide) (by decide) hw2 hw' h10
    (fun t' kt' => WP.keep _ (by prun [(kt'.gpr _ (by decide)).trans h21, BitVec.add_zero]) (by decide))
    h29 h11 hP rfl rfl hT hS fun t₇ v3 o7 a10 k7 => ?_
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) a10 ((k7.gpr _ (by decide)).trans h29) 4)
    fun t₈ ⟨⟨a14, m8⟩, k8⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k8.gpr _ (by decide)).trans a10)
    ((k8.gpr _ (by decide)).trans ((k7.gpr _ (by decide)).trans h29)) 3) fun t₉ ⟨⟨a15, m9⟩, k9⟩ => ?_
  have k79 := (k7.trans k8).trans k9
  have r11_9 : t₉.gpr .r11 = BitVec.ofNat 64 (2 * w) := by rw [k79.gpr .r11 (by decide), h11]
  refine WP.mono (copySub_ok (a := slot w 3) (b := slot w 4) (w := w) ((hs.congr k7.wr).congr (k8.trans k9).wr) a15
    ((k9.gpr _ (by decide)).trans a14) r11_9 (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun u ⟨⟨c10, o10⟩, k10⟩ => ?_
  have hm9 : t₉.mem = t₇.mem := by rw [m9, m8]
  rw [hm9] at c10 o10
  refine ⟨⟨?_, ?_, ?_⟩, (k79.trans k10).mono (by decide)⟩
  · rw [Pre.val32_eq_wv, wv_congr2 fun j hj => c10 j hj, ← Pre.val32_eq_wv, v3]
  · intro x hx
    simp only [Mont.ofs] at hx
    rw [o10 x (by simp only [VG.Proof.Bignum.ofs]; omega_arith)]
    exact o7 x fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [Mont.ofs] <;> omega_arith
  · rw [k10.gpr .r10 (by decide), k9.gpr .r10 (by decide), k8.gpr .r10 (by decide), a10]

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
  have hle : T ≤ S' + N := by omega_using [hTN]
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

/-- The registers `PrivPre.chunkStep1` writes. -/
def chunk1Regs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24, .r25, .r31]

/-- Between the steps of the reduction, after `i` of them: in `p`'s working
space `off BX oA` of `w` words, `p` (`Pv`), 1 in array 1 and `S` in array 4
with `S R^i + x_i ≡ 0` for `x_i` the first `w i` words of `X`'s array 6; the
next chunk at `r25`, `K - w i` in `r31`. -/
structure ChunkJ (s : State) (BX : Addr) (Z oA w wX K Pv i : Nat) (t : State) : Prop where
  scr : Scr t BX Z
  r10 : t.gpr .r10 = off (off BX oA) (slot w 0)
  r21 : t.gpr .r21 = off (off BX oA) (slot w 0)
  r29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))
  r11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w)
  r12 : (t.gpr .r12).toNat < 2 ^ 32
  inv : (w32 t.mem (off BX oA) (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  r25 : t.gpr .r25 = off BX (slot wX 6 + 8 * (w * i))
  r31 : t.gpr .r31 = BitVec.ofNat 64 K - BitVec.ofNat 64 (w * i)
  p0 : val32 t.mem (off BX oA) (slot w 0) (2 * w) = Pv
  p1 : val32 t.mem (off BX oA) (slot w 1) (2 * w) = 1
  slt : val32 t.mem (off BX oA) (slot w 4) (2 * w) < Pv
  sv : (val32 t.mem (off BX oA) (slot w 4) (2 * w) * (2 ^ (64 * w)) ^ i + wv s.mem BX (slot wX 6) (w * i)) % Pv = 0
  out : Outside BX oA (slot w 24) s.mem t.mem
  wk : Mont.Outside (off BX oA) (slot w 2) (7 * (8 * (w + 2))) s.mem t.mem
  keep : Keep chunk1Regs s t

/-- One step of the reduction. -/
theorem chunkStep1_ok {s t : State} {BX : Addr} {Z oA w wX K Pv i : Nat}
    (hA : oA + slot w 24 ≤ Z) (hX : slot wX 6 + 8 * (w * nChunks K w) ≤ oA) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hK : 1 ≤ K) (hK' : K < 2 ^ 40) (hP2 : 2 ≤ Pv) (hi : i < nChunks K w)
    (I : ChunkJ s BX Z oA w wX K Pv i t) :
    WP isa PrivPre.chunkStep1 t fun u => ChunkJ s BX Z oA w wX K Pv (i + 1) u ∧
      ((u.gpr .r3).toNat ≠ 0 ↔ i + 1 ≠ nChunks K w) := by
  have hn := I.scr.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5
  have e6 := e 6; have e7 := e 7; have e8 := e 8; have e9 := e 9; have e24 := e 24
  have eX6 : slot wX 6 = 256 + 6 * (8 * (wX + 2)) := rfl
  have hwi : w * i + w ≤ w * nChunks K w := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have hsA := I.scr.sub hA
  -- The chunk into array 6, and `r25` past it.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) I.r10 I.r29 6) fun t₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r15] (Q := fun u => u.gpr .r15 = t₁.gpr .r25 ∧ u.mem = t₁.mem) (by prun [BitVec.add_zero])
    (by decide)) fun t₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copyAdv_ok (a := slot wX 6 + 8 * (w * i)) (b := oA + slot w 6) (w := w) (I.scr.congr k12.wr)
    (by rw [a15, (k1.gpr _ (by decide)).trans I.r25]) (by rw [k2.gpr _ (by decide), a14, off_off])
    ((k12.gpr _ (by decide)).trans I.r11) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun t₃ ⟨⟨c3, o3, a15'⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.r25] (Q := fun u => u.gpr .r25 = t₃.gpr .r15 ∧ u.mem = t₃.mem)
    (by prun [BitVec.add_zero]) (by decide)) fun t₄ ⟨⟨a25, m4⟩, k4⟩ => ?_)
  have k14 := (k12.trans k3).trans k4
  have hm2 : t₂.mem = t.mem := by rw [m2, m1]
  rw [hm2] at c3 o3
  have o3' : Mont.Outside (off BX oA) (slot w 6) (8 * w) t.mem t₄.mem := by
    rw [m4]; exact out_rebase o3 (by omega_arith)
  have W4 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t.mem t₄.mem :=
    o3'.mono (by omega_arith) (by omega_arith)
  -- The chunk's value.
  let C := wv s.mem BX (slot wX 6 + 8 * (w * i)) w
  have v6 : val32 t₄.mem (off BX oA) (slot w 6) (2 * w) = C := by
    rw [Pre.val32_eq_wv, wv_off, m4, wv_congr2 fun j hj => c3 j hj]
    exact I.out.wv (Or.inl (by omega_arith)) (by omega_arith)
  have v0 : val32 t₄.mem (off BX oA) (slot w 0) (2 * w) = Pv := by
    rw [W4.val32 (Or.inl (by omega_arith)) (by omega_arith), I.p0]
  have v1 : val32 t₄.mem (off BX oA) (slot w 1) (2 * w) = 1 := by
    rw [W4.val32 (Or.inl (by omega_arith)) (by omega_arith), I.p1]
  have v4 : val32 t₄.mem (off BX oA) (slot w 4) (2 * w) = val32 t.mem (off BX oA) (slot w 4) (2 * w) :=
    o3'.val32 (Or.inl (by omega_arith)) (by omega_arith)
  have w0 : w32 t₄.mem (off BX oA) (slot w 0) = w32 t.mem (off BX oA) (slot w 0) :=
    W4.w32 (Or.inl (by omega_arith)) (by omega_arith)
  have g : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r29, .r31], t₄.gpr r = t.gpr r := fun r hr =>
    k14.gpr r (by revert r hr; decide)
  -- `T := C 1 R⁻¹`.
  refine WP.seq (WP.mono (Pub.montOpN_ok (n := 9) (o := 7) (a := 6) (b := 1) (hsA.congr k14.wr) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by omega_arith)
    ((g .r10 (by decide)).trans I.r10) ((g .r29 (by decide)).trans I.r29) ((g .r11 (by decide)).trans I.r11)
    (by rw [g .r12 (by decide)]; exact I.r12) (by rw [g .r12 (by decide), w0]; exact I.inv)
    (by rw [v1, v0]; omega_arith)) fun t₅ ⟨⟨T5, T5e, o5⟩, k5⟩ => ?_)
  rw [v0, v6, v1] at T5e
  rw [v0] at T5
  have W5 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₄.mem t₅.mem :=
    outs_work o5 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp only [e] <;> omega_arith)
  have u5 : ∀ j, j = 0 ∨ j = 1 ∨ j = 4 →
      val32 t₅.mem (off BX oA) (slot w j) (2 * w) = val32 t₄.mem (off BX oA) (slot w j) (2 * w) := fun j hj =>
    outs_val32 o5 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> rcases hj with rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
      (by rcases hj with rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
  have w0' : w32 t₅.mem (off BX oA) (slot w 0) = w32 t.mem (off BX oA) (slot w 0) := by
    rw [W5.w32 (Or.inl (by omega_arith)) (by omega_arith), w0]
  have g5 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r25, .r29, .r31], t₅.gpr r = t₄.gpr r := fun r hr =>
    k5.gpr r (by revert r hr; decide)
  -- `S := S 1 R⁻¹`.
  refine WP.seq (WP.mono (Pub.montOpN_ok (n := 9) (o := 4) (a := 4) (b := 1) (hsA.congr (k14.trans k5).wr) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by omega_arith)
    ((g5 .r10 (by decide)).trans ((g .r10 (by decide)).trans I.r10))
    ((g5 .r29 (by decide)).trans ((g .r29 (by decide)).trans I.r29))
    ((g5 .r11 (by decide)).trans ((g .r11 (by decide)).trans I.r11))
    (by rw [g5 .r12 (by decide), g .r12 (by decide)]; exact I.r12)
    (by rw [g5 .r12 (by decide), g .r12 (by decide), w0']; exact I.inv)
    (by rw [u5 1 (by decide), u5 0 (by decide), v1, v0]; omega_arith)) fun t₆ ⟨⟨S6, S6e, o6⟩, k6⟩ => ?_)
  rw [u5 0 (by decide), v0, u5 4 (by decide), v4, u5 1 (by decide), v1] at S6e
  rw [u5 0 (by decide), v0] at S6
  have W6 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₅.mem t₆.mem :=
    outs_work o6 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp only [e] <;> omega_arith)
  have u6 : ∀ j, j = 0 ∨ j = 1 ∨ j = 7 →
      val32 t₆.mem (off BX oA) (slot w j) (2 * w) = val32 t₅.mem (off BX oA) (slot w j) (2 * w) := fun j hj =>
    outs_val32 o6 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> rcases hj with rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
      (by rcases hj with rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
  have g6 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r29, .r31], t₆.gpr r = t.gpr r := fun r hr => by
    rw [k6.gpr r (by revert r hr; decide), g5 r (by revert r hr; decide), g r (by revert r hr; decide)]
  have k16 := (k14.trans k5).trans k6
  have b25 : t₆.gpr .r25 = off BX (slot wX 6 + 8 * (w * i) + 8 * w) := by
    rw [k6.gpr .r25 (by decide), g5 .r25 (by decide), a25, a15']
  have w0'' : w32 t₆.mem (off BX oA) (slot w 0) = w32 t.mem (off BX oA) (slot w 0) := by
    rw [W6.w32 (Or.inl (by omega_arith)) (by omega_arith), w0']
  -- `S := S - T mod p`.
  refine WP.seq (WP.mono (subST_ok (hsA.congr k16.wr) (by omega_arith) hw2 hw' ((g6 .r10 (by decide)).trans I.r10)
    ((g6 .r21 (by decide)).trans I.r21) ((g6 .r29 (by decide)).trans I.r29) ((g6 .r11 (by decide)).trans I.r11)
    (by rw [u6 0 (by decide), u5 0 (by decide), v0]) S6 (by rw [u6 7 (by decide)]; exact T5))
    fun t₇ ⟨⟨s7, o7, a10⟩, k7⟩ => ?_)
  rw [u6 7 (by decide)] at s7
  refine WP.mono (tick_ok (t := t₇) ((k7.gpr _ (by decide)).trans ((g6 .r11 (by decide)).trans I.r11)) (by omega_arith))
    fun u ⟨⟨b31, b3, mu⟩, ku⟩ => ?_
  have kall := (k16.trans k7).trans ku
  have W7 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₆.mem u.mem := by
    rw [mu]; exact o7.mono (by omega_arith) (by omega_arith)
  have Wt : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t.mem u.mem :=
    ((W4.trans W5).trans W6).trans W7
  have gu : ∀ r ∈ [Reg.r11, .r12, .r21, .r29], u.gpr r = t.gpr r := fun r hr => by
    rw [ku.gpr r (by revert r hr; decide), k7.gpr r (by revert r hr; decide), g6 r (by revert r hr; decide)]
  have hwi1 : w * (i + 1) = w * i + w := Nat.mul_succ _ _
  have hpow : (2 ^ (64 * w)) ^ i = 2 ^ (64 * (w * i)) := by rw [← Nat.pow_mul, Nat.mul_assoc]
  refine ⟨⟨I.scr.congr kall.wr, ?_, by rw [gu .r21 (by decide)]; exact I.r21,
    by rw [gu .r29 (by decide)]; exact I.r29, by rw [gu .r11 (by decide)]; exact I.r11,
    by rw [gu .r12 (by decide)]; exact I.r12,
    by rw [gu .r12 (by decide), Wt.w32 (Or.inl (by omega_arith)) (by omega_arith)]; exact I.inv, ?_, ?_,
    by rw [Wt.val32 (Or.inl (by omega_arith)) (by omega_arith)]; exact I.p0,
    by rw [Wt.val32 (Or.inl (by omega_arith)) (by omega_arith)]; exact I.p1,
    by rw [mu, s7]; exact Nat.mod_lt _ (by omega_arith), ?_,
    I.out.trans (out_sub (fun x hx => Wt x hx) (by omega_arith) (by omega_arith) (by omega_arith)),
    I.wk.trans (Wt.mono (by omega_arith) (by omega_arith)),
    (I.keep.trans kall).mono (by decide +kernel)⟩, ?_⟩
  · rw [ku.gpr .r10 (by decide), a10]
  · rw [ku.gpr .r25 (by decide), k7.gpr .r25 (by decide), b25, hwi1, Nat.mul_add, Nat.add_assoc]
  · rw [b31, k7.gpr .r31 (by decide), g6 .r31 (by decide), I.r31, hwi1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  · rw [mu, s7, hwi1, wv_add, ← hpow]
    exact chunk1_s I.sv S6e T5e T5
  · have hx : t₇.gpr .r31 - BitVec.ofNat 64 w = BitVec.ofNat 64 K - BitVec.ofNat 64 (w * (i + 1)) := by
      rw [k7.gpr .r31 (by decide), g6 .r31 (by decide), I.r31, hwi1]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_arith
    rw [b3, flag_ne_zero, hx]
    exact flag_iff (by omega_arith) hK hK' (by omega_arith) hi

/-! ## The working space after the reduction -/

/-- A factor's working space at `B` of `w` words (`Z` bytes): `p` (`Pv`) in
array 0, its address in `r10` and `r21`, the arrays' size in `r29`, `2 w` in
`r11` and `-p⁻¹ mod 2³²` in `r12`. -/
structure WsC (t : State) (B : Addr) (Z w Pv : Nat) : Prop where
  scr : Scr t B Z
  r10 : t.gpr .r10 = off B (slot w 0)
  r21 : t.gpr .r21 = off B (slot w 0)
  r29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))
  r11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w)
  r12 : (t.gpr .r12).toNat < 2 ^ 32
  inv : (w32 t.mem B (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  p0 : val32 t.mem B (slot w 0) (2 * w) = Pv

/-- `WsC` after a run that keeps its registers and array 0. -/
theorem WsC.of {t u : State} {B : Addr} {Z w Pv : Nat} {rs : List Reg} (h : WsC t B Z w Pv) (k : Keep rs t u)
    (hr : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r29], r ∉ rs) (hw : 1 ≤ w) (hZ : slot w 1 ≤ Z) {o n : Nat}
    (ho : Mont.Outside B o n t.mem u.mem) (ho' : slot w 1 ≤ o) : WsC u B Z w Pv := by
  have hn := h.scr.nowrap
  have e0 : slot w 1 = slot w 0 + 8 * (w + 2) := by unfold slot; omega_using []
  have v0 : val32 u.mem B (slot w 0) (2 * w) = val32 t.mem B (slot w 0) (2 * w) :=
    ho.val32 (Or.inl (by omega_using [ho', e0])) (by omega)
  have w0 : w32 u.mem B (slot w 0) = w32 t.mem B (slot w 0) := by
    have := ho.val32 (d := slot w 0) (k := 1) (Or.inl (by omega_using [ho', e0])) (by omega)
    simpa [val32] using this
  exact ⟨h.scr.congr k.wr, (k.gpr _ (hr _ (by decide))).trans h.r10, (k.gpr _ (hr _ (by decide))).trans h.r21,
    (k.gpr _ (hr _ (by decide))).trans h.r29, (k.gpr _ (hr _ (by decide))).trans h.r11,
    by rw [k.gpr _ (hr _ (by decide))]; exact h.r12, by rw [k.gpr .r12 (hr _ (by decide)), w0]; exact h.inv,
    v0.trans h.p0⟩

/-- `WsC.of` for a run that puts array 0's address back into `r10`. -/
theorem WsC.of10 {t u : State} {B : Addr} {Z w Pv : Nat} {rs : List Reg} (h : WsC t B Z w Pv) (k : Keep rs t u)
    (hr : ∀ r ∈ [Reg.r11, .r12, .r21, .r29], r ∉ rs) (h10 : u.gpr .r10 = off B (slot w 0)) (hw : 1 ≤ w)
    (hZ : slot w 1 ≤ Z) {o n : Nat} (ho : Mont.Outside B o n t.mem u.mem) (ho' : slot w 1 ≤ o) : WsC u B Z w Pv := by
  have hn := h.scr.nowrap
  have e0 : slot w 1 = slot w 0 + 8 * (w + 2) := by unfold slot; omega_using []
  have v0 : val32 u.mem B (slot w 0) (2 * w) = val32 t.mem B (slot w 0) (2 * w) :=
    ho.val32 (Or.inl (by omega_using [ho', e0])) (by omega)
  have w0 : w32 u.mem B (slot w 0) = w32 t.mem B (slot w 0) := by
    have := ho.val32 (d := slot w 0) (k := 1) (Or.inl (by omega_using [ho', e0])) (by omega)
    simpa [val32] using this
  exact ⟨h.scr.congr k.wr, h10, (k.gpr _ (hr _ (by decide))).trans h.r21,
    (k.gpr _ (hr _ (by decide))).trans h.r29, (k.gpr _ (hr _ (by decide))).trans h.r11,
    by rw [k.gpr _ (hr _ (by decide))]; exact h.r12, by rw [k.gpr .r12 (hr _ (by decide)), w0]; exact h.inv,
    v0.trans h.p0⟩

/-- `r3 = (2 w - e) >> 63` is not zero iff `e > 2 w`. -/
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

/-- The registers `zStep` writes. -/
def zRegs : List Reg := Pub.montRegs ++ [.r3, .r31]

/-- A further reduction (`zStep`): `S := S 1 R⁻¹`, `e := e - w` in `r31`, and
whether `e > 2 w` in `r3`. -/
theorem zStep_ok {t : State} {B : Addr} {Z w Pv : Nat} (C : WsC t B Z w Pv) (hZ : slot w 9 ≤ Z) (hw2 : 2 ≤ w)
    (hw' : w < 2 ^ 31) (h1 : val32 t.mem B (slot w 1) (2 * w) = 1) (hP2 : 2 ≤ Pv) :
    WP isa PrivPre.zStep t fun u =>
      (WsC u B Z w Pv ∧ val32 u.mem B (slot w 4) (2 * w) < Pv ∧
        val32 u.mem B (slot w 4) (2 * w) * 2 ^ (64 * w) % Pv = val32 t.mem B (slot w 4) (2 * w) * 1 % Pv ∧
        val32 u.mem B (slot w 1) (2 * w) = 1 ∧ u.gpr .r31 = t.gpr .r31 - BitVec.ofNat 64 w ∧
        u.gpr .r3 = (BitVec.ofNat 64 (2 * w) - (t.gpr .r31 - BitVec.ofNat 64 w)) >>> 63 ∧
        Mont.Outside B (slot w 2) (3 * (8 * (w + 2))) t.mem u.mem) ∧ Keep zRegs t u := by
  have hn := C.scr.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e9 := e 9
  unfold PrivPre.zStep
  refine WP.seq (WP.mono (Pub.montOpN_ok (n := 9) (o := 4) (a := 4) (b := 1) C.scr (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ
    C.r10 C.r29 C.r11 C.r12 C.inv (by rw [h1, C.p0]; omega_arith)) fun t₁ ⟨⟨S1, S1e, o1⟩, k1⟩ => ?_)
  rw [C.p0, h1] at S1e
  rw [C.p0] at S1
  have W1 : Mont.Outside B (slot w 2) (3 * (8 * (w + 2))) t.mem t₁.mem := fun x hx => o1 x fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [Mont.ofs] at hx
    rcases hr with rfl | rfl | rfl <;> simp only [Mont.ofs] <;> omega_arith
  have C1 := C.of k1 (by decide) (by omega_arith) (by omega_arith) W1 (by omega_arith)
  have v1 : val32 t₁.mem B (slot w 1) (2 * w) = 1 := by
    rw [W1.val32 (Or.inl (by omega_arith)) (by omega_arith), h1]
  refine WP.mono (WP.keep [.r3, .r31] (Q := fun u => u.gpr .r31 = t₁.gpr .r31 - BitVec.ofNat 64 w ∧
      u.gpr .r3 = (BitVec.ofNat 64 (2 * w) - (t₁.gpr .r31 - BitVec.ofNat 64 w)) >>> 63 ∧ u.mem = t₁.mem)
    (by prun [C1.r11, shr1_ofNat (show w < 2 ^ 62 by omega_arith)]) (by decide)) fun u ⟨⟨a31, a3, mu⟩, ku⟩ => ?_
  have g31 : t₁.gpr .r31 = t.gpr .r31 := k1.gpr _ (by decide)
  refine ⟨⟨C1.of ku (o := slot w 1) (n := 0) (by decide) (by omega_arith) (by omega_arith)
    (by rw [mu]; exact Mont.Outside.refl _ _ _ _)
    (Nat.le_refl _), by rw [mu]; exact S1, by rw [mu]; exact S1e, by rw [mu]; exact v1, by rw [a31, g31],
    by rw [a3, g31], by rw [mu]; exact W1⟩, k1.trans ku⟩

/-- The further reductions' state after `j` of them: `S R^(m + j) + V ≡ 0`
and `e - w j` in `r31`. -/
structure ZJ (t₀ : State) (B : Addr) (Z w Pv m V e j : Nat) (t : State) : Prop where
  ctx : WsC t B Z w Pv
  one : val32 t.mem B (slot w 1) (2 * w) = 1
  slt : val32 t.mem B (slot w 4) (2 * w) < Pv
  sv : (val32 t.mem B (slot w 4) (2 * w) * (2 ^ (64 * w)) ^ (m + j) + V) % Pv = 0
  r31 : t.gpr .r31 = BitVec.ofNat 64 (e - w * j)
  out : Mont.Outside B (slot w 2) (3 * (8 * (w + 2))) t₀.mem t.mem
  keep : Keep zRegs t₀ t

/-- `S R^(m + j) + V ≡ 0` and `S' R ≡ S` give `S' R^(m + j + 1) + V ≡ 0`. -/
theorem z_s {R N S S' V m : Nat} (hS : (S * R ^ m + V) % N = 0) (hS' : S' * R % N = S * 1 % N) :
    (S' * R ^ (m + 1) + V) % N = 0 := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm, Nat.add_mod, Nat.mul_mod, hS', ← Nat.mul_mod, Nat.mul_one,
    ← Nat.add_mod, hS]

/-- The further reductions, while more than `2 w` of the `e` words are left:
`Zc` of them, for `Zc` from `PrimeR2`'s `r2Z`. -/
theorem zLoop_ok {t : State} {B : Addr} {Z w Pv m V e Zc : Nat} (C : WsC t B Z w Pv) (hZ : slot w 9 ≤ Z)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hP2 : 2 ≤ Pv) (he : e < 2 ^ 40) (hZc : 0 < Zc) (hZe : w * Zc ≤ e)
    (hstep : ∀ j < Zc, (2 * w < e - w * (j + 1) ↔ j + 1 < Zc))
    (h1 : val32 t.mem B (slot w 1) (2 * w) = 1) (hS : val32 t.mem B (slot w 4) (2 * w) < Pv)
    (hsv : (val32 t.mem B (slot w 4) (2 * w) * (2 ^ (64 * w)) ^ m + V) % Pv = 0)
    (h31 : t.gpr .r31 = BitVec.ofNat 64 e) :
    WP isa (.loop PrivPre.zStep (.nonzero .d .r3)) t (ZJ t B Z w Pv m V e Zc) := by
  refine count_loop (cr := .r3) hZc (ZJ t B Z w Pv m V e) (fun j hj u I => ?_)
    ⟨C, h1, hS, by rw [Nat.add_zero]; exact hsv, by rw [h31, Nat.mul_zero, Nat.sub_zero],
      Mont.Outside.refl _ _ _ _, Keep.refl _ _⟩
  refine WP.mono (zStep_ok I.ctx hZ hw2 hw' I.one hP2) fun v ⟨⟨Cv, sl, se, v1, a31, a3, ov⟩, kv⟩ => ?_
  have hmj : w * (j + 1) ≤ e := Nat.le_trans (Nat.mul_le_mul_left _ hj) hZe
  have e31 : u.gpr .r31 - BitVec.ofNat 64 w = BitVec.ofNat 64 (e - w * (j + 1)) := by
    rw [I.r31]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [Nat.mul_succ] at hmj ⊢
    omega_arith
  refine ⟨⟨Cv, v1, sl, by rw [← Nat.add_assoc]; exact z_s I.sv se, by rw [a31, e31], I.out.trans ov,
    I.keep.trans' kv⟩, ?_⟩
  rw [a3, e31, gt_flag (by omega_arith) (by omega_arith)]
  exact (hstep j hj).trans ⟨Nat.ne_of_lt, fun h => Nat.lt_of_le_of_ne hj h⟩

/-! ## `-S`, the doublings and the squares -/

/-- `PrivPre.negS`: `S := -S mod p` (array 4), changing only arrays 3–7. -/
theorem negS_ok {t : State} {B : Addr} {Z w Pv : Nat} (C : WsC t B Z w Pv) (hZ : slot w 9 ≤ Z) (hw2 : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hS : val32 t.mem B (slot w 4) (2 * w) < Pv) :
    WP isa PrivPre.negS t fun u =>
      (WsC u B Z w Pv ∧ val32 u.mem B (slot w 4) (2 * w) = (0 + Pv - val32 t.mem B (slot w 4) (2 * w)) % Pv ∧
        Mont.Outside B (slot w 3) (5 * (8 * (w + 2))) t.mem u.mem) ∧ Keep subRegs t u := by
  have hn := C.scr.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e7 := e 7; have e8 := e 8; have e9 := e 9
  unfold PrivPre.negS
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) C.r10 C.r29 7) fun t₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans C.r10)
    ((k1.gpr _ (by decide)).trans C.r29) 4) fun t₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (a := slot w 4) (b := slot w 7) (w := w) (C.scr.congr k12.wr) a15
    ((k2.gpr _ (by decide)).trans a14) ((k12.gpr _ (by decide)).trans C.r11) (by omega_arith) hw' (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t₃ ⟨⟨c3, o3⟩, k3⟩ => ?_)
  have hm2 : t₂.mem = t.mem := by rw [m2, m1]
  rw [hm2] at c3 o3
  have k13 := k12.trans k3
  have C3 := C.of k13 (by decide) (by omega_arith) (by omega_arith) (o := slot w 7) (n := 8 * w) o3 (by omega_arith)
  have v7 : val32 t₃.mem B (slot w 7) (2 * w) = val32 t.mem B (slot w 4) (2 * w) := by
    rw [Pre.val32_eq_wv, wv_congr2 fun j hj => c3 j hj, ← Pre.val32_eq_wv]
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) C3.r10 C3.r29 4) fun t₄ ⟨⟨b14, m4⟩, k4⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (C3.scr.congr k4.wr) b14 ((k4.gpr _ (by decide)).trans C3.r11) (by omega_arith)
    hw' (by omega_arith)) fun t₅ ⟨⟨_, z5, o5⟩, k5⟩ => ?_)
  rw [m4] at o5
  have k35 := k4.trans k5
  have C5 := C3.of k35 (by decide) (by omega_arith) (by omega_arith) (o := slot w 4) (n := 8 * w) o5 (by omega_arith)
  have v4 : val32 t₅.mem B (slot w 4) (2 * w) = 0 := by
    rw [Pre.val32_eq_wv]; exact (wv_eq_zero_iff _ _ _ _).mpr z5
  have v7' : val32 t₅.mem B (slot w 7) (2 * w) = val32 t.mem B (slot w 4) (2 * w) := by
    rw [o5.val32 (Or.inr (by omega_arith)) (by omega_arith), v7]
  refine WP.mono (subST_ok C5.scr (by omega_arith) hw2 hw' C5.r10 C5.r21 C5.r29 C5.r11 C5.p0
    (by rw [v4]; omega_arith) (by rw [v7']; exact hS)) fun u ⟨⟨s4, o6, a10⟩, k6⟩ => ?_
  rw [v4, v7'] at s4
  have O : Mont.Outside B (slot w 3) (5 * (8 * (w + 2))) t.mem u.mem :=
    ((o3.mono (by omega_arith) (by omega_arith)).trans (o5.mono (by omega_arith) (by omega_arith))).trans
      (o6.mono (by omega_arith) (by omega_arith))
  exact ⟨⟨C.of10 ((k13.trans k35).trans k6) (by decide) a10 (by omega_arith) (by omega_arith) O (by omega_arith), s4, O⟩,
    ((k13.trans k35).trans k6).mono (by decide)⟩

theorem mul_pow_mod_double {x j N : Nat} : 2 * (x * 2 ^ j % N) % N = x * 2 ^ (j + 1) % N := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm 2 (2 ^ j)]

/-- The registers `dblLoop` writes. -/
def dblRegs : List Reg := [.r0, .r14, .r17, .r4, .r3, .r15, .r16, .r20]

/-- `M` doublings counted by `r4` (`dblLoop`), of `x < N` in array 1, for `N`
in array 0 (as `Pre.r2Dbl64_ok`): `x := x 2^M mod N`, changing only arrays 1–3. -/
theorem dblAny_ok {s : State} {B : Addr} {Z w N x M : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hN : val32 s.mem B (slot w 0) (2 * w) = N) (hx : val32 s.mem B (slot w 1) (2 * w) = x) (hxN : x < N)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 M) (hM : 0 < M) (hM' : M < 2 ^ 64) :
    WP isa PrivPre.dblLoop s fun t =>
      val32 t.mem B (slot w 1) (2 * w) = x * 2 ^ M % N ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep dblRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have hN0 : 0 < N := by omega_using [hxN]
  let Inv : Nat → State → Prop := fun j t =>
    val32 t.mem B (slot w 1) (2 * w) = x * 2 ^ j % N ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep dblRegs s t
  refine wp_countdown (cnt := .r4) (N := M) hM' hM Inv (fun j _ t ⟨tx, to, tk⟩ _ => ?_)
    ⟨by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (by omega_using [hxN])]; exact hx, Mont.Outside.refl _ _ _ _,
      Keep.refl _ _⟩ h4
  have n0 : val32 t.mem B (slot w 0) (2 * w) = N := by rw [to.val32 (by omega_using [e0, e1]) (by omega_using [hw', e0, hh]), hN]
  refine WP.seq (WP.mono (doubleMod64_ok (hs.congr tk.wr) ((tk.gpr _ (by decide)).trans h8)
    ((tk.gpr _ (by decide)).trans h9) ((tk.gpr _ (by decide)).trans h10) ((tk.gpr _ (by decide)).trans h5)
    ((tk.gpr _ (by decide)).trans h11) hw hw' hZ (by rw [tx, n0]; exact Nat.mod_lt _ hN0))
    fun t₁ ⟨d1, od, kd⟩ => ?_)
  refine WP.mono (subi_ok t₁ .r4 (by decide)) fun t₂ e2 => ?_
  subst e2
  refine ⟨⟨?_, by rw [mem_write]; exact to.trans od, ((tk.trans kd).trans (Keep.write _ _ _)).mono (by decide)⟩, ?_⟩
  · rw [mem_write, d1, tx, n0, mul_pow_mod_double]
  · gsimp; rw [kd.gpr .r4 (by decide)]

/-- What holds between the squares, with `x ≡ 2^e R (mod N)` under `G`. -/
structure SqG (s : State) (B : Addr) (Z w N e : Nat) (G : Prop) (t : State) : Prop where
  scr : Scr t B Z
  r10 : t.gpr .r10 = off B (slot w 0)
  r11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w)
  r12 : (t.gpr .r12).toNat < 2 ^ 32
  inv : (w32 t.mem B (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  n : val32 t.mem B (slot w 0) (2 * w) = N
  lt : val32 t.mem B (slot w 1) (2 * w) < N
  x : G → val32 t.mem B (slot w 1) (2 * w) % N = 2 ^ e * 2 ^ (64 * w) % N
  out : Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem
  keep : Keep Pre.r2PrimeRegs s t

theorem sqG_step {s t : State} {B : Addr} {Z w N e : Nat} {G : Prop} (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (hodd : N % 2 = 1) (h : SqG s B Z w N e G t) :
    WP isa Precompute.r2Sq t fun u => SqG s B Z w N (2 * e) G u ∧ u.gpr .r24 = t.gpr .r24 := by
  have hnw := h.scr.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  refine WP.mono (Pre.r2Sq_ok h.scr hw2 hw' hZ h.r10 h.r11 h.r12 h.inv (by rw [h.n]; exact h.lt))
    fun u ⟨⟨ul, ue, uo⟩, k⟩ => ?_
  rw [h.n] at ul ue
  have uo' : Mont.Outside B (slot w 1) (24 * (w + 2)) t.mem u.mem := fun x hx => uo x fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [Mont.ofs] at hx
    rcases hr with rfl | rfl | rfl <;> simp only [Mont.ofs] <;> omega_arith
  have n0 : val32 u.mem B (slot w 0) (2 * w) = N := by rw [uo'.val32 (by omega_using [e0, e1]) (by omega_using [hw', e0, hh]), h.n]
  have w0 : w32 u.mem B (slot w 0) = w32 t.mem B (slot w 0) := by
    have := uo'.val32 (d := slot w 0) (k := 1) (by omega_using [e0, e1]) (by omega_using [e0, hh])
    simpa [val32] using this
  have g : ∀ r ∈ [Reg.r10, .r11, .r12], u.gpr r = t.gpr r := fun r hr => k.gpr r (by revert r hr; decide)
  exact ⟨⟨h.scr.congr k.wr, (g .r10 (by decide)).trans h.r10, (g .r11 (by decide)).trans h.r11,
    by rw [g .r12 (by decide)]; exact h.r12, by rw [g .r12 (by decide), w0]; exact h.inv, n0, ul,
    fun hg => Pub.sq_step hR (h.x hg) ue, h.out.trans uo', (h.keep.trans k).mono⟩, k.gpr .r24 (by decide)⟩

theorem SqG.of_keep {s t u : State} {B : Addr} {Z w N e : Nat} {G : Prop} (h : SqG s B Z w N e G t)
    (k : Keep [.r24] t u) (hm : u.mem = t.mem) : SqG s B Z w N e G u :=
  ⟨h.scr.congr k.wr, (k.gpr _ (by decide)).trans h.r10, (k.gpr _ (by decide)).trans h.r11,
    by rw [k.gpr .r12 (by decide)]; exact h.r12, by rw [k.gpr .r12 (by decide), hm]; exact h.inv,
    by rw [hm]; exact h.n, by rw [hm]; exact h.lt, fun g => by rw [hm]; exact h.x g, by rw [hm]; exact h.out,
    (h.keep.trans k).mono⟩

/-- Six squares (`r24 := 6`, `r2Sq`): from `2^w R` to `2^(64 w) R = R² mod N`, under `G`. -/
theorem sq6_ok {s : State} {B : Addr} {Z w N : Nat} {G : Prop} (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (hodd : N % 2 = 1) (I0 : SqG s B Z w N w G s) :
    WP isa (.seq (.block [.li .r24 6]) (.loop (.seq Precompute.r2Sq (.block [.subi .r24 .r24 1])) (.nonzero .d .r24)))
      s fun t => (val32 t.mem B (slot w 1) (2 * w) < N ∧ (G → val32 t.mem B (slot w 1) (2 * w) = 2 ^ (128 * w) % N) ∧
        Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep Pre.r2PrimeRegs s t ∧
        t.gpr .r10 = off B (slot w 0) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ (t.gpr .r12).toNat < 2 ^ 32 ∧
        (w32 t.mem B (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 ∧ val32 t.mem B (slot w 0) (2 * w) = N) := by
  refine WP.seq (WP.mono (WP.keep [.r24] (Q := fun u => u.gpr .r24 = BitVec.ofNat 64 6 ∧ u.mem = s.mem)
    (by prun) (by decide)) fun s₄ ⟨⟨a24, m4⟩, k4⟩ => ?_)
  let Inv : Nat → State → Prop := fun j u => SqG s B Z w N (w * 2 ^ j) G u
  refine WP.mono (wp_countdown (cnt := .r24) (N := 6) (by decide) (by decide) Inv
    (fun j _ u I _ => ?_) (by simp only [Inv, Nat.pow_zero, Nat.mul_one]; exact I0.of_keep k4 m4) a24)
    fun t I6 => ?_
  · refine WP.seq (WP.mono (sqG_step hw2 hw' hZ hodd I) fun u₁ ⟨I1, g24⟩ => ?_)
    refine WP.mono (subi_ok u₁ .r24 (by decide)) fun u₂ e2 => ?_
    subst e2
    have he : w * 2 ^ (j + 1) = 2 * (w * 2 ^ j) := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2]
    refine ⟨?_, by simp only [gpr_write, ↓reduceIte, g24]⟩
    show SqG s B Z w N (w * 2 ^ (j + 1)) G _
    rw [he]
    exact I1.of_keep (Keep.write _ _ _) (mem_write _ _ _)
  refine ⟨I6.lt, fun g => ?_, I6.out, I6.keep, I6.r10, I6.r11, I6.r12, I6.inv, I6.n⟩
  have h6 : w * 2 ^ 6 = 64 * w := by rw [show (2 : Nat) ^ 6 = 64 from rfl, Nat.mul_comm]
  rw [← Nat.mod_eq_of_lt I6.lt, I6.x g, h6, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega_using []]

/-! ## `r2Fast` -/

/-- `w` from `X`'s arrays' size `8 (2 w + 2) = 16 (w + 1)`. -/
theorem w_of_x28 {W : Nat} (hW : W < 2 ^ 40) :
    BitVec.ofNat 64 (8 * (2 * W + 2)) >>> 4 - BitVec.ofNat 64 1 = BitVec.ofNat 64 W := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- `r2Fast` up to its reduction's end, then `c`: from the state `s₁` after
`x := 1`, the reduction's invariant after its `⌈W / w⌉` steps. -/
theorem r2A_ok {s : State} {BX : Addr} {Z oA w wX W Pv : Nat} {c : Prog isa} {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot w 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hwW : w ≤ W) (hW' : W < 2 ^ 31) (hWX : wX = 2 * W)
    (h10 : s.gpr .r10 = off (off BX oA) (slot w 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem (off BX oA) (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (h5 : s.gpr .r5 = off (off BX oA) (slot w 1))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hP : val32 s.mem (off BX oA) (slot w 0) (2 * w) = Pv) (hP2 : 2 ≤ Pv)
    (hc : ∀ s₁ t, Mont.Outside (off BX oA) (slot w 1) (8 * w) s.mem s₁.mem → Keep [.r0, .r14, .r17] s s₁ →
      ChunkJ s₁ BX Z oA w wX W Pv (nChunks W w) t → WP isa c t Q) :
    WP isa (.seq Precompute.one (.seq (.block (PublicChecked.base .r14 4)) (.seq Precompute.zeroWords
      (.seq (.block (xb .r25 6 ++ ([.lsr .d .r31 .r28 4, .subi .r31 .r31 1] : List Instr)))
      (.seq (.loop PrivPre.chunkStep1 (.nonzero .d .r3)) c))))) s Q := by
  have hn := hs.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e4 := e 4; have e5 := e 5; have e9 := e 9
  have e24 := e 24
  have eX6 : slot wX 6 = 256 + 6 * (8 * (wX + 2)) := rfl
  have eX8 : slot wX 8 = 256 + 8 * (8 * (wX + 2)) := rfl
  have hsA := hs.sub hA
  have hK := nChunks_mul_lt (K := W) (w := w) (by omega_arith) (by omega_arith)
  have hK1 := le_nChunks_mul (K := W) (w := w) (by omega_arith)
  have hKw : w * nChunks W w < W + w := by rw [Nat.mul_comm]; exact hK
  have hX6 : slot wX 6 + 8 * (w * nChunks W w) ≤ oA := by omega_arith
  -- `x := 1`.
  refine WP.seq (WP.mono (one_ok hsA h5 h11 (by omega_arith) hw' (by omega_arith)) fun s₁ ⟨x1, o1, k1⟩ => ?_)
  have v0 : val32 s₁.mem (off BX oA) (slot w 0) (2 * w) = Pv := by
    rw [o1.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  have w0 : w32 s₁.mem (off BX oA) (slot w 0) = w32 s.mem (off BX oA) (slot w 0) := by
    have := o1.val32 (d := slot w 0) (k := 1) (Or.inl (by omega_arith)) (by omega_arith)
    simpa [val32] using this
  -- `S := 0`.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) 4) fun s₂ ⟨⟨a14, m2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hsA.congr (k1.trans k2).wr) a14
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h11)) (by omega_arith) hw' (by omega_arith))
    fun s₃ ⟨⟨_, z3, o3⟩, k3⟩ => ?_)
  rw [m2] at o3
  have k13 := k2.trans k3
  -- `r25` and `r31`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .r25) (by decide) (by decide) (((k1.trans k13).gpr _ (by decide)).trans h27)
    (((k1.trans k13).gpr _ (by decide)).trans h28) 6) fun s₄ ⟨⟨a25, m4⟩, k4⟩ => ?_
  refine WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = BitVec.ofNat 64 W ∧ u.mem = s₄.mem)
    (by
      prun [((k4.gpr _ (by decide)).trans (((k1.trans k13).gpr _ (by decide)).trans h28))]
      rw [hWX]; exact w_of_x28 (by omega_arith)) (by decide)) fun s₅ ⟨⟨a31, m5⟩, k5⟩ => ?_
  have k15 := (k13.trans k4).trans k5
  have hm5 : s₅.mem = s₃.mem := by rw [m5, m4]
  have O5 : Mont.Outside (off BX oA) (slot w 4) (8 * w) s₁.mem s₅.mem := by rw [hm5]; exact o3
  have g : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r29], s₅.gpr r = s.gpr r := fun r hr => by
    rw [k15.gpr r (by revert r hr; decide), k1.gpr r (by revert r hr; decide)]
  have I0 : ChunkJ s₁ BX Z oA w wX W Pv 0 s₅ := by
    refine ⟨hs.congr (k1.trans k15).wr, (g .r10 (by decide)).trans h10, (g .r21 (by decide)).trans h21,
      (g .r29 (by decide)).trans h29, (g .r11 (by decide)).trans h11, by rw [g .r12 (by decide)]; exact h12,
      by rw [g .r12 (by decide), O5.w32 (Or.inl (by omega_arith)) (by omega_arith), w0]; exact hinv,
      by rw [(k5.gpr _ (by decide)).trans a25, Nat.mul_zero, Nat.mul_zero, Nat.add_zero],
      by rw [a31, Nat.mul_zero]; exact (BitVec.sub_zero _).symm,
      by rw [O5.val32 (Or.inl (by omega_arith)) (by omega_arith), v0],
      by rw [O5.val32 (Or.inl (by omega_arith)) (by omega_arith), x1],
      by rw [hm5, Pre.val32_eq_wv, (wv_eq_zero_iff _ _ _ _).mpr z3]; omega_arith,
      by rw [hm5, Pre.val32_eq_wv, (wv_eq_zero_iff _ _ _ _).mpr z3, Nat.mul_zero]; rfl,
      out_sub (fun x hx => O5 x (by simp only [Mont.ofs] at hx ⊢; omega_arith)) (by omega_arith) (by omega_arith)
        (by omega_arith),
      O5.mono (by omega_arith) (by omega_arith), k15.mono (by decide)⟩
  refine WP.seq (WP.mono (count_loop (cr := .r3) (nChunks_pos (by omega_arith) (by omega_arith))
    (fun j u => ChunkJ s₁ BX Z oA w wX W Pv j u)
    (fun j hj u I => chunkStep1_ok hA hX6 hw2 hw' (by omega_arith) (by omega_arith) hP2 hj I) I0)
    fun t I => hc s₁ t o1 k1 I)

/-- `(a - b) + a = 2 a - b`, as words, for `b ≤ 2 a`. -/
theorem e0_ofNat {a b : Nat} (hb : b ≤ 2 * a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b + BitVec.ofNat 64 a = BitVec.ofNat 64 (2 * a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- `-S ≡ x R^(-m)` from `S R^m + x ≡ 0`. -/
theorem neg_val {S X V N : Nat} (hS : (S * X + V) % N = 0) (hSN : S < N) :
    (0 + N - S) % N * X % N = V % N := by
  have hN : 0 < N := by omega_using [hSN]
  rw [Nat.zero_add, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  have h1 : (N - S) * X + S * X = N * X := by rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hSN)]
  have h2 : ((N - S) * X + (S * X + V)) % N = V % N := by
    rw [← Nat.add_assoc, h1, Nat.mul_add_mod]
  rw [Nat.add_mod, hS, Nat.add_zero, Nat.mod_mod] at h2
  exact h2

/-- After the reduction's steps: the further ones and `-S`, from the words
left `e₀ = 2 W - ⌈W / w⌉ w` to `e = r2E W w`: `Y R^(K + Z) ≡ x` in array 4. -/
theorem r2B_ok {s₁ t : State} {BX : Addr} {Z oA w wX W Pv : Nat} {c : Prog isa} {Q : State → Prop}
    (hA : oA + slot w 24 ≤ Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hwW : w ≤ W) (hW' : W < 2 ^ 31) (hWX : wX = 2 * W)
    (hP2 : 2 ≤ Pv) (h28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (I : ChunkJ s₁ BX Z oA w wX W Pv (nChunks W w) t)
    (hc : ∀ u, WsC u (off BX oA) (slot w 24) w Pv →
      (val32 u.mem (off BX oA) (slot w 4) (2 * w) * (2 ^ (64 * w)) ^ (nChunks W w + VG.Proof.Bignum.r2Z W w)) %
        Pv = wv s₁.mem BX (slot wX 6) (w * nChunks W w) % Pv →
      val32 u.mem (off BX oA) (slot w 4) (2 * w) < Pv →
      u.gpr .r31 = BitVec.ofNat 64 (VG.Proof.Bignum.r2E W w) →
      Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t.mem u.mem →
      Keep (([.r3, .r31] : List Reg) ++ zRegs ++ subRegs) t u → WP isa c u Q) :
    WP isa (.seq (.block [.lsr .d .r3 .r28 4, .subi .r3 .r3 1, .add .r31 .r31 .r3, .sub .r3 .r11 .r31,
        .lsr .d .r3 .r3 63])
      (.seq (.ite (.nonzero .d .r3) (.loop PrivPre.zStep (.nonzero .d .r3)) (.block [])) (.seq PrivPre.negS c))) t Q := by
  have hn := I.scr.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e2 := e 2; have e3 := e 3; have e8 := e 8; have e9 := e 9; have e24 := e 24
  have hsA := I.scr.sub hA
  have hwx1 : 1 ≤ w := by omega_arith
  obtain ⟨hk1, hk2⟩ := VG.Proof.Bignum.kBounds (w := W) hwx1
  obtain ⟨hE1, hE2, hE3⟩ := VG.Proof.Bignum.r2E_spec (w := W) hwx1 hwW
  have dK : nChunks W w = (W + w - 1) / w := rfl
  have dE0 : VG.Proof.Bignum.r2E0 W w = 2 * W - (W + w - 1) / w * w := rfl
  have dE : VG.Proof.Bignum.r2E W w = VG.Proof.Bignum.r2E0 W w - VG.Proof.Bignum.r2Z W w * w := rfl
  have C0 : WsC t (off BX oA) (slot w 24) w Pv := ⟨hsA, I.r10, I.r21, I.r29, I.r11, I.r12, I.inv, I.p0⟩
  -- `e₀` into `r31`, and whether it is more than `2 w`.
  refine WP.seq (WP.mono (WP.keep [.r3, .r31] (Q := fun u =>
      u.gpr .r31 = BitVec.ofNat 64 (VG.Proof.Bignum.r2E0 W w) ∧
      u.gpr .r3 = (BitVec.ofNat 64 (2 * w) - BitVec.ofNat 64 (VG.Proof.Bignum.r2E0 W w)) >>> 63 ∧ u.mem = t.mem)
    (by
      have e31 : BitVec.ofNat 64 W - BitVec.ofNat 64 (w * nChunks W w) + BitVec.ofNat 64 W =
          BitVec.ofNat 64 (VG.Proof.Bignum.r2E0 W w) := by
        rw [e0_ofNat (by rw [Nat.mul_comm, dK]; omega_arith), dE0, dK, Nat.mul_comm w]
      prun [h28, hWX, w_of_x28 (show W < 2 ^ 40 by omega_arith), I.r31, I.r11, e31]) (by decide))
    fun t₁ ⟨⟨a31, a3, m1⟩, k1⟩ => ?_)
  have C1 := C0.of k1 (by decide) hwx1 (by omega_arith) (o := slot w 1) (n := 0) (by rw [m1]; exact Mont.Outside.refl _ _ _ _)
    (Nat.le_refl _)
  have v1 : val32 t₁.mem (off BX oA) (slot w 1) (2 * w) = 1 := by rw [m1]; exact I.p1
  have v4 : val32 t₁.mem (off BX oA) (slot w 4) (2 * w) = val32 t.mem (off BX oA) (slot w 4) (2 * w) := by rw [m1]
  -- The further reductions.
  have hsv : (val32 t₁.mem (off BX oA) (slot w 4) (2 * w) * (2 ^ (64 * w)) ^ nChunks W w +
      wv s₁.mem BX (slot wX 6) (w * nChunks W w)) % Pv = 0 := by rw [v4]; exact I.sv
  refine WP.seq (WP.mono (Q := ZJ t₁ (off BX oA) (slot w 24) w Pv (nChunks W w) (wv s₁.mem BX (slot wX 6) (w * nChunks W w))
      (VG.Proof.Bignum.r2E0 W w) (VG.Proof.Bignum.r2Z W w)) ?_ fun t₂ J => ?_)
  · have hf : ∀ x : Nat, x < 2 ^ 62 →
        (((BitVec.ofNat 64 (2 * w) - BitVec.ofNat 64 x) >>> 63) != 0) = decide (2 * w < x) := fun x hx => by
      have hg := gt_flag (a := 2 * w) (e := x) (by omega_arith) hx
      by_cases h : 2 * w < x
      · have hv : (BitVec.ofNat 64 (2 * w) - BitVec.ofNat 64 x) >>> 63 ≠ 0#64 := fun he => hg.mpr h (by rw [he]; rfl)
        simp [hv, h]
      · have hv : (BitVec.ofNat 64 (2 * w) - BitVec.ofNat 64 x) >>> 63 = 0#64 :=
          BitVec.eq_of_toNat_eq (by have := mt hg.mp h; simpa using this)
        simp [hv, h]
    have hev : isa.eval (.nonzero .d .r3) t₁ = some (decide (2 * w < VG.Proof.Bignum.r2E0 W w)) := by
      rw [eval_nonzero, a3, hf _ (by omega_arith)]
    by_cases hz : 2 * w < VG.Proof.Bignum.r2E0 W w
    · refine WP.ite true (by rw [hev, decide_eq_true hz]) (fun _ => ?_) (by simp)
      have hZ0 := (VG.Proof.Bignum.r2Z_pos (w := W) hwx1).mpr hz
      refine zLoop_ok C1 (by omega_arith) hw2 hw' hP2 (by omega_arith) hZ0 (by rw [Nat.mul_comm]; omega_arith)
        (fun j hj => ?_) v1 (by rw [v4]; exact I.slt) hsv a31
      have := VG.Proof.Bignum.r2Z_step (w := W) hwx1 hj
      rw [Nat.mul_comm w]; exact this
    · refine WP.ite false (by rw [hev, decide_eq_false hz]) (by simp) (fun _ => ?_)
      have hZ0 : VG.Proof.Bignum.r2Z W w = 0 :=
        Nat.eq_zero_of_not_pos fun h => hz ((VG.Proof.Bignum.r2Z_pos (w := W) hwx1).mp h)
      rw [WP.block_nil_iff, hZ0]
      exact ⟨C1, v1, by rw [v4]; exact I.slt, by rw [Nat.add_zero]; exact hsv,
        by rw [a31, Nat.mul_zero, Nat.sub_zero], Mont.Outside.refl _ _ _ _, (Keep.refl [] _).mono (by decide)⟩
  -- `-S`.
  refine WP.seq (WP.mono (negS_ok J.ctx (by omega_arith) hw2 hw' J.slt) fun u ⟨⟨Cu, yu, ou⟩, ku⟩ => ?_)
  refine hc u Cu ?_ (by rw [yu]; exact Nat.mod_lt _ (by omega_arith)) ?_ ?_ ?_
  · rw [yu]; exact neg_val J.sv J.slt
  · rw [ku.gpr .r31 (by decide), J.r31, dE, Nat.mul_comm]
  · rw [← m1]
    exact (J.out.mono (by omega_arith) (by omega_arith)).trans (ou.mono (by omega_arith) (by omega_arith))
  · exact ((k1.trans J.keep).trans ku).mono (by decide)

/-- The registers `r2Fast`'s tail writes. -/
def tailRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24]

/-- `r4 := 64 (2 w - e)` from `r11 = 2 w`, `r31 = e`. -/
theorem cnt_hi {w e : Nat} (he : e ≤ 2 * w) :
    (BitVec.ofNat 64 (2 * w) - BitVec.ofNat 64 e) <<< 6 = BitVec.ofNat 64 (64 * (2 * w - e)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- `r4 := 64 (w - e) + w` from `r11 = 2 w`, `r31 = e`. -/
theorem cnt_lo {w e : Nat} (he : e ≤ w) :
    (BitVec.ofNat 64 w - BitVec.ofNat 64 e) <<< 6 + BitVec.ofNat 64 w = BitVec.ofNat 64 (64 * (w - e) + w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- `r2Fast` after `-S`, from `Y` in array 4 with `Y ≡ 2^(64 e) (mod p)` under
`G`, `e` in `r31`, `1 ≤ e ≤ 2 w`: `Y` into array 1, then the doublings (`r2C`),
and the squares if `e ≤ w`. -/
theorem r2T_ok {u : State} {B : Addr} {Z w Pv e : Nat} {G : Prop} (C : WsC u B Z w Pv) (hZ : slot w 9 ≤ Z)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1) (he1 : 1 ≤ e) (he2 : e ≤ 2 * w)
    (hY : val32 u.mem B (slot w 4) (2 * w) < Pv)
    (hYG : G → val32 u.mem B (slot w 4) (2 * w) % Pv = 2 ^ (64 * e) % Pv)
    (h31 : u.gpr .r31 = BitVec.ofNat 64 e) :
    WP isa (.seq (.block (PublicChecked.base .r14 1 ++ PublicChecked.base .r15 4)) (.seq copyN
      (.seq (.block (PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3 ++
          ([.lsr .d .r4 .r11 1, .sub .r3 .r4 .r31, .lsr .d .r3 .r3 63] : List Instr)))
        (.ite (.nonzero .d .r3)
          (.seq (.block [.sub .r4 .r11 .r31, .lsl .r4 .r4 6]) (.ite (.nonzero .d .r4) PrivPre.dblLoop (.block [])))
          (.seq (.block [.lsr .d .r4 .r11 1, .sub .r3 .r4 .r31, .lsl .r3 .r3 6, .add .r4 .r3 .r4])
            (.seq PrivPre.dblLoop (.seq (.block [.li .r24 6])
              (.loop (.seq Precompute.r2Sq (.block [.subi .r24 .r24 1])) (.nonzero .d .r24)))))))))
      u fun t =>
      (val32 t.mem B (slot w 1) (2 * w) < Pv ∧ (G → val32 t.mem B (slot w 1) (2 * w) = 2 ^ (128 * w) % Pv) ∧
        Mont.Outside B (slot w 1) (24 * (w + 2)) u.mem t.mem ∧ t.gpr .r10 = off B (slot w 0) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧
        val32 t.mem B (slot w 0) (2 * w) = Pv) ∧ Keep tailRegs u t := by
  have hn := C.scr.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := es 0; have e1 := es 1; have e2 := es 2; have e3 := es 3; have e4 := es 4; have e8 := es 8; have e9 := es 9
  have hP0 : 0 < Pv := by omega_arith
  -- `Y` into array 1.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) C.r10 C.r29 1) fun t₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans C.r10)
    ((k1.gpr _ (by decide)).trans C.r29) 4) fun t₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (a := slot w 4) (b := slot w 1) (w := w) (C.scr.congr k12.wr) a15
    ((k2.gpr _ (by decide)).trans a14) ((k12.gpr _ (by decide)).trans C.r11) (by omega_arith) hw' (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t₃ ⟨⟨c3, o3⟩, k3⟩ => ?_)
  have hm2 : t₂.mem = u.mem := by rw [m2, m1]
  rw [hm2] at c3 o3
  have k13 := k12.trans k3
  have C3 := C.of k13 (by decide) (by omega_arith) (by omega_arith) (o := slot w 1) (n := 8 * w) o3 (Nat.le_refl _)
  have y1 : val32 t₃.mem B (slot w 1) (2 * w) = val32 u.mem B (slot w 4) (2 * w) := by
    rw [Pre.val32_eq_wv, wv_congr2 fun j hj => c3 j hj, ← Pre.val32_eq_wv]
  -- The bases, and whether `e > w`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) C3.r10 C3.r29 1) fun t₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k4.gpr _ (by decide)).trans C3.r10)
    ((k4.gpr _ (by decide)).trans C3.r29) 2) fun t₅ ⟨⟨a8, m5⟩, k5⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) (((k4.trans k5).gpr _ (by decide)).trans C3.r10)
    (((k4.trans k5).gpr _ (by decide)).trans C3.r29) 3) fun t₆ ⟨⟨a9, m6⟩, k6⟩ => ?_
  have k46 := (k4.trans k5).trans k6
  have h31' : t₆.gpr .r31 = BitVec.ofNat 64 e := by rw [k46.gpr .r31 (by decide), k13.gpr .r31 (by decide), h31]
  refine WP.mono (WP.keep [.r4, .r3] (Q := fun v =>
      v.gpr .r3 = (BitVec.ofNat 64 w - BitVec.ofNat 64 e) >>> 63 ∧ v.mem = t₆.mem)
    (by prun [(k46.gpr _ (by decide)).trans C3.r11, h31', shr1_ofNat (show w < 2 ^ 62 by omega_arith)]) (by decide))
    fun t₇ ⟨⟨a3, m7⟩, k7⟩ => ?_
  have k47 := k46.trans k7
  have hm7 : t₇.mem = t₃.mem := by rw [m7, m6, m5, m4]
  have C7 := C3.of k47 (by decide) (by omega_arith) (by omega_arith) (o := slot w 1) (n := 0)
    (by rw [hm7]; exact Mont.Outside.refl _ _ _ _) (Nat.le_refl _)
  have b5 : t₇.gpr .r5 = off B (slot w 1) := by rw [k7.gpr _ (by decide), (k5.trans k6).gpr _ (by decide), a5]
  have b8 : t₇.gpr .r8 = off B (slot w 2) := by rw [k7.gpr _ (by decide), k6.gpr _ (by decide), a8]
  have b9 : t₇.gpr .r9 = off B (slot w 3) := by rw [k7.gpr _ (by decide), a9]
  have b31 : t₇.gpr .r31 = BitVec.ofNat 64 e := by rw [k7.gpr _ (by decide), h31']
  have y7 : val32 t₇.mem B (slot w 1) (2 * w) = val32 u.mem B (slot w 4) (2 * w) := by rw [hm7, y1]
  have hYG' : G → val32 t₇.mem B (slot w 1) (2 * w) = 2 ^ (64 * e) % Pv := fun g => by
    rw [y7, ← hYG g, Nat.mod_eq_of_lt hY]
  have O3 : Mont.Outside B (slot w 1) (24 * (w + 2)) u.mem t₇.mem := by
    rw [hm7]; exact o3.mono (Nat.le_refl _) (by omega_arith)
  have hfl : ∀ a x : Nat, a < 2 ^ 62 → x < 2 ^ 62 →
      (((BitVec.ofNat 64 a - BitVec.ofNat 64 x) >>> 63) != 0) = decide (a < x) := fun a x ha hx => by
    have hg := gt_flag (a := a) (e := x) ha hx
    by_cases h : a < x
    · have hv : (BitVec.ofNat 64 a - BitVec.ofNat 64 x) >>> 63 ≠ 0#64 := fun he => hg.mpr h (by rw [he]; rfl)
      simp [hv, h]
    · have hv : (BitVec.ofNat 64 a - BitVec.ofNat 64 x) >>> 63 = 0#64 :=
        BitVec.eq_of_toNat_eq (by have := mt hg.mp h; simpa using this)
      simp [hv, h]
  have hev : isa.eval (.nonzero .d .r3) t₇ = some (decide (w < e)) := by
    rw [eval_nonzero, a3, hfl _ _ (by omega_arith) (by omega_arith)]
  have ke : ∀ {v : State} {rs : List Reg}, Keep rs t₇ v → (∀ r ∈ [Reg.r10, .r11, .r29], r ∉ rs) →
      v.gpr .r10 = off B (slot w 0) ∧ v.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧
        v.gpr .r11 = BitVec.ofNat 64 (2 * w) := fun k hr =>
    ⟨(k.gpr _ (hr _ (by decide))).trans C7.r10, (k.gpr _ (hr _ (by decide))).trans C7.r29,
      (k.gpr _ (hr _ (by decide))).trans C7.r11⟩
  have hnz : ∀ c, c < 2 ^ 64 → (BitVec.ofNat 64 c != 0) = decide (c ≠ 0) := fun c hc => by
    by_cases h : c = 0
    · subst h; rfl
    · have hv : BitVec.ofNat 64 c ≠ 0#64 := fun he => h (by
        have := congrArg BitVec.toNat he; simpa [Nat.mod_eq_of_lt hc] using this)
      simp [hv, h]
  by_cases hwe : w < e
  · -- `2^(128 w)` by doublings alone.
    refine WP.ite true (by rw [hev, decide_eq_true hwe]) (fun _ => ?_) (by simp)
    refine WP.seq (WP.mono (WP.keep [.r4] (Q := fun v => v.gpr .r4 = BitVec.ofNat 64 (64 * (2 * w - e)) ∧
        v.mem = t₇.mem) (by prun [C7.r11, b31, cnt_hi he2]) (by decide)) fun t₈ ⟨⟨a4, m8⟩, k8⟩ => ?_)
    have v8 : val32 t₈.mem B (slot w 0) (2 * w) = Pv := by rw [m8]; exact C7.p0
    by_cases hc0 : 64 * (2 * w - e) = 0
    · refine WP.ite false (by rw [eval_nonzero, a4, hc0]; rfl) (by simp) (fun _ => ?_)
      rw [WP.block_nil_iff]
      have he' : e = 2 * w := by omega_arith
      obtain ⟨x10, x29, x11⟩ := ke (k8 : Keep [.r4] t₇ t₈) (by decide)
      refine ⟨⟨by rw [m8, y7]; exact hY, fun g => by rw [m8, hYG' g, he', ← Nat.mul_assoc], by rw [m8]; exact O3,
        x10, x29, x11, v8⟩, (((k13.trans k47).trans k8)).mono (by decide)⟩
    · refine WP.ite true (by rw [eval_nonzero, a4, hnz _ (by omega_arith), decide_eq_true hc0]) (fun _ => ?_) (by simp)
      refine WP.mono (dblAny_ok (x := val32 t₈.mem B (slot w 1) (2 * w)) (C7.scr.congr k8.wr)
        ((k8.gpr _ (by decide)).trans b8) ((k8.gpr _ (by decide)).trans b9) ((k8.gpr _ (by decide)).trans C7.r10)
        ((k8.gpr _ (by decide)).trans b5) ((k8.gpr _ (by decide)).trans C7.r11) (by omega_arith) hw' (by omega_arith)
        v8 rfl (by rw [m8, y7]; exact hY) a4 (by omega_arith) (by omega_arith)) fun t ⟨x9, o9, k9⟩ => ?_
      have v9 : val32 t.mem B (slot w 0) (2 * w) = Pv := by rw [o9.val32 (by omega_arith) (by omega_arith), v8]
      obtain ⟨x10, x29, x11⟩ := ke ((k8.trans k9) : Keep _ t₇ t) (by decide)
      refine ⟨⟨by rw [x9]; exact Nat.mod_lt _ hP0, fun g => ?_, by rw [← m8] at O3; exact O3.trans o9,
        x10, x29, x11, v9⟩, (((k13.trans k47).trans k8).trans k9).mono (by decide)⟩
      rw [x9, m8, hYG' g, Nat.mod_mul_mod, ← Nat.pow_add]
      congr 2
      omega_arith
  · -- `2^(64 w + w)`, then six squares.
    refine WP.ite false (by rw [hev, decide_eq_false hwe]) (by simp) (fun _ => ?_)
    have hwe' : e ≤ w := Nat.le_of_not_lt hwe
    refine WP.seq (WP.mono (WP.keep [.r4, .r3] (Q := fun v => v.gpr .r4 = BitVec.ofNat 64 (64 * (w - e) + w) ∧
        v.mem = t₇.mem)
      (by prun [C7.r11, b31, shr1_ofNat (show w < 2 ^ 62 by omega_arith), cnt_lo hwe']) (by decide))
      fun t₈ ⟨⟨a4, m8⟩, k8⟩ => ?_)
    have v8 : val32 t₈.mem B (slot w 0) (2 * w) = Pv := by rw [m8]; exact C7.p0
    refine WP.seq (WP.mono (dblAny_ok (x := val32 t₈.mem B (slot w 1) (2 * w)) (C7.scr.congr k8.wr)
      ((k8.gpr _ (by decide)).trans b8) ((k8.gpr _ (by decide)).trans b9) ((k8.gpr _ (by decide)).trans C7.r10)
      ((k8.gpr _ (by decide)).trans b5) ((k8.gpr _ (by decide)).trans C7.r11) (by omega_arith) hw' (by omega_arith)
      v8 rfl (by rw [m8, y7]; exact hY) a4 (by omega_arith) (by omega_arith)) fun t₉ ⟨x9, o9, k9⟩ => ?_)
    have v9 : val32 t₉.mem B (slot w 0) (2 * w) = Pv := by rw [o9.val32 (by omega_arith) (by omega_arith), v8]
    have k89 := k8.trans k9
    have w9 : w32 t₉.mem B (slot w 0) = w32 t₇.mem B (slot w 0) := by
      have := o9.val32 (d := slot w 0) (k := 1) (by omega_arith) (by omega_arith)
      rw [m8] at this
      simpa [val32] using this
    have I0 : SqG t₉ B Z w Pv w G t₉ := ⟨C7.scr.congr k89.wr, (k89.gpr _ (by decide)).trans C7.r10,
      (k89.gpr _ (by decide)).trans C7.r11, by rw [k89.gpr .r12 (by decide)]; exact C7.r12,
      by rw [k89.gpr .r12 (by decide), w9]; exact C7.inv, v9, by rw [x9]; exact Nat.mod_lt _ hP0,
      fun g => by
        rw [x9, m8, hYG' g, Nat.mod_mod, Nat.mod_mul_mod, ← Nat.pow_add, ← Nat.pow_add]
        congr 2
        omega_arith,
      Mont.Outside.refl _ _ _ _, Keep.refl _ _⟩
    refine WP.mono (sq6_ok hw2 hw' (by omega_arith) hodd I0) fun t ⟨tl, tx, to, tk, t10, t11, _, _, tn⟩ => ?_
    have t29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := by
      rw [tk.gpr _ (by decide), k89.gpr _ (by decide), C7.r29]
    refine ⟨⟨tl, tx, by rw [← m8] at O3; exact (O3.trans o9).trans to, t10, t29, t11, tn⟩,
      ((((k13.trans k47).trans k8).trans k9).trans tk).mono (by decide)⟩

/-- The registers `r2Fast` writes. -/
def r2FRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24, .r25, .r31]

theorem r2Fast_eq : PrivPre.r2Fast =
    .seq Precompute.one (.seq (.block (PublicChecked.base .r14 4)) (.seq Precompute.zeroWords
    (.seq (.block (xb .r25 6 ++ ([.lsr .d .r31 .r28 4, .subi .r31 .r31 1] : List Instr)))
    (.seq (.loop PrivPre.chunkStep1 (.nonzero .d .r3))
    (.seq (.block [.lsr .d .r3 .r28 4, .subi .r3 .r3 1, .add .r31 .r31 .r3, .sub .r3 .r11 .r31, .lsr .d .r3 .r3 63])
    (.seq (.ite (.nonzero .d .r3) (.loop PrivPre.zStep (.nonzero .d .r3)) (.block []))
    (.seq PrivPre.negS
    (.seq (.block (PublicChecked.base .r14 1 ++ PublicChecked.base .r15 4)) (.seq copyN
    (.seq (.block (PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3 ++
        ([.lsr .d .r4 .r11 1, .sub .r3 .r4 .r31, .lsr .d .r3 .r3 63] : List Instr)))
      (.ite (.nonzero .d .r3)
        (.seq (.block [.sub .r4 .r11 .r31, .lsl .r4 .r4 6]) (.ite (.nonzero .d .r4) PrivPre.dblLoop (.block [])))
        (.seq (.block [.lsr .d .r4 .r11 1, .sub .r3 .r4 .r31, .lsl .r3 .r3 6, .add .r4 .r3 .r4]) (.seq PrivPre.dblLoop
          (.seq (.block [.li .r24 6])
            (.loop (.seq Precompute.r2Sq (.block [.subi .r24 .r24 1])) (.nonzero .d .r24)))))))))))))))) := rfl

/-- `PrivPre.r2Fast` in a factor's working space at `off BX oA` of `w` words,
for `p` (`Pv`) in its array 0, `-p⁻¹ mod 2³²` in `r12` and the base of array 1
in `r5`, from `x` in `X`'s array 6 (`2 W` words, at `r27`, `r28`): `R² mod p`
into array 1 when `x ≡ 2^(128 W)` modulo `p` (`G`); only the working space's
arrays 1–8 changed. -/
theorem r2Fast_ok {s : State} {BX : Addr} {Z oA w wX W Pv : Nat} {G : Prop}
    (hs : Scr s BX Z) (hA : oA + slot w 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hwW : w ≤ W) (hW' : W < 2 ^ 31) (hWX : wX = 2 * W)
    (h10 : s.gpr .r10 = off (off BX oA) (slot w 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem (off BX oA) (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (h5 : s.gpr .r5 = off (off BX oA) (slot w 1))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hP : val32 s.mem (off BX oA) (slot w 0) (2 * w) = Pv) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1)
    (hG : G → wv s.mem BX (slot wX 6) (w * nChunks W w) % Pv = 2 ^ (128 * W) % Pv) :
    WP isa PrivPre.r2Fast s fun t =>
      (val32 t.mem (off BX oA) (slot w 1) (2 * w) < Pv ∧
        (G → val32 t.mem (off BX oA) (slot w 1) (2 * w) = 2 ^ (128 * w) % Pv) ∧
        Outside BX oA (slot w 24) s.mem t.mem ∧ t.gpr .r10 = off (off BX oA) (slot w 0) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧
        val32 t.mem (off BX oA) (slot w 0) (2 * w) = Pv) ∧ Keep r2FRegs s t := by
  have hn := hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := es 1; have e2 := es 2; have e9 := es 9; have e24 := es 24
  have eX6 : slot wX 6 = 256 + 6 * (8 * (wX + 2)) := rfl
  have eX8 : slot wX 8 = 256 + 8 * (8 * (wX + 2)) := rfl
  have hwx1 : 1 ≤ w := by omega_arith
  have hK := nChunks_mul_lt (K := W) (w := w) hwx1 (by omega_arith)
  have hKw : w * nChunks W w < W + w := by rw [Nat.mul_comm]; exact hK
  obtain ⟨hE1, hE2, hE3⟩ := VG.Proof.Bignum.r2E_spec (w := W) hwx1 hwW
  rw [r2Fast_eq]
  refine r2A_ok hs hA hXA hw2 hw' hwW hW' hWX h10 h21 h29 h11 h12 hinv h5 h27 h28 hP hP2
    fun s₁ t o1 k1 I => ?_
  have h28' : t.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)) := by
    rw [I.keep.gpr _ (by decide), k1.gpr _ (by decide), h28]
  refine r2B_ok hA hw2 hw' hwW hW' hWX hP2 h28' I fun u Cu sv slt u31 ou ku => ?_
  have O1 : Outside BX oA (slot w 24) s.mem s₁.mem :=
    out_sub (fun x hx => o1 x (by simp only [Mont.ofs] at hx ⊢; omega_arith)) (by omega_arith) (by omega_arith)
      (by omega_arith)
  have hV : wv s₁.mem BX (slot wX 6) (w * nChunks W w) = wv s.mem BX (slot wX 6) (w * nChunks W w) :=
    O1.wv (Or.inl (by omega_arith)) (by omega_arith)
  have hYG : G → val32 u.mem (off BX oA) (slot w 4) (2 * w) % Pv = 2 ^ (64 * VG.Proof.Bignum.r2E W w) % Pv :=
    fun g => VG.Proof.Bignum.r2_reduced hwx1 hwW hodd (by
      rw [Nat.pow_mul, sv, hV, hG g])
  refine WP.mono (r2T_ok Cu (by omega_arith) hw2 hw' hP2 hodd hE1 hE2 slt hYG u31)
    fun t' ⟨⟨tl, tx, to, t10, t29, t11, t0⟩, tk⟩ => ⟨⟨tl, tx, ?_, t10, t29, t11, t0⟩, ?_⟩
  · have Ou : Outside BX oA (slot w 24) t.mem u.mem :=
      out_sub (fun x hx => ou x (by simp only [Mont.ofs] at hx ⊢; omega_arith)) (by omega_arith) (by omega_arith)
        (by omega_arith)
    have Ot : Outside BX oA (slot w 24) u.mem t'.mem :=
      out_sub (fun x hx => to x (by simp only [Mont.ofs] at hx ⊢; omega_arith)) (by omega_arith) (by omega_arith)
        (by omega_arith)
    exact ((O1.trans I.out).trans Ou).trans Ot
  · exact (((k1.trans I.keep).trans ku).trans tk).mono (by decide)

end VG.Proof.Bignum.PPC64LE.PrivPre
