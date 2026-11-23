module

public import VerifiedGarbage.Proof.MlKem.X86.NttInv
public import VerifiedGarbage.Proof.MlKem.X86.Leaf
public import VerifiedGarbage.Impl.MlKem.X86.Ntt
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlKem.Ntt
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseWord
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.MlKem.X86.NttInv
meta import VerifiedGarbage.Proof.MlKem.X86.Leaf
meta import VerifiedGarbage.Impl.MlKem.X86.Ntt
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.Ntt
meta import VerifiedGarbage.Proof.MlKem.PolyContract
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.SseWord
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_multiply_ntts`

The vector code of `Impl/MlKem/X86/Ntt.lean`, against the contract the
scalar code it replaces had.

* `baseW` is the arithmetic of a pair, on words (as x86-64's
  `Proof/MlKem/X86_64/Mul.lean` has it), and `mul_lanes` the four pairs of
  a register: the even word of a doubleword is a pair's first coefficient
  and the odd word its second (`mulV`, `mergeV`, `swapV`).
* `mulCore_wp` runs the code of four pairs, an instruction at a time
  (`mulLoad_wp`, `wmontG_wp`, `mulMerge_wp`, `mulOut_wp`), and `mstep` is a
  step of the loop (`MI`), after the constants and the table of the `γᵢ`
  (`consts_wp`, `table_wp`).

The function (`verified`) is its body inside a frame that saves `ebx`
(`Piece.frame`) inside the MCDT frame (`Piece.mcdt`), constant time by the
analysis of general and XMM registers (`Piece.sse`) from `esp` and the
four pointers.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.W

open VG VG.X86 VG.Proof.MlKem
open VG.Spec.MlKem (Zq)

/-- `R² mod q`, in a word. -/
def r2W : BitVec 16 := 1353#16

/-- `montW d z` for `d ∈ (-2q, 2q)` and `z ∈ (-q, q)`. -/
theorem mont_small {d z : BitVec 16} (hd1 : -(2 * 3329) < d.toInt) (hd2 : d.toInt < 2 * 3329)
    (hz1 : -3329 < z.toInt) (hz2 : z.toInt < 3329) :
    -3329 < (montW d z).toInt ∧ (montW d z).toInt < 3329 ∧
      3329 ∣ (montW d z).toInt * 65536 - d.toInt * z.toInt := by
  obtain hn : (d.toInt * z.toInt).natAbs ≤ 6657 * 3328 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by bdd_omega) (by bdd_omega)
  obtain h1 := Int.le_natAbs (a := d.toInt * z.toInt)
  obtain h2 := Int.le_natAbs (a := -(d.toInt * z.toInt))
  rw [Int.natAbs_neg] at h2
  obtain ⟨m1, m2, m3⟩ := montW_spec (d := d) (z := z) (by bdd_omega) (by bdd_omega)
  exact ⟨m1, m2, Int.dvd_of_emod_eq_zero m3⟩

theorem toInt_lt_q {a : BitVec 16} {x : Zq} (h : a.toNat = x.val) : a.toInt = x.val ∧ 0 ≤ a.toInt ∧ a.toInt < 3329 := by
  have hx := x.isLt
  obtain e := toInt_of_lt (a := a) (by rw [h]; exact hx)
  rw [h] at e
  exact ⟨e, by rw [e]; exact Int.natCast_nonneg _, by rw [e]; exact Int.ofNat_lt.mpr hx⟩

/-- The value of a word in `[0, q)` from its value modulo `q`. -/
theorem cadd_val {m : BitVec 16} (h1 : -3329 < m.toInt) (h2 : m.toInt < 3329) {T : Int} {v : Zq}
    (hd : 3329 ∣ m.toInt - T) (hv : (v.val : Int) = T % 3329) : (caddW m).toNat = v.val := by
  obtain c := caddW_spec (Int.le_of_lt h1) h2
  obtain n := toNat_of_toInt (a := caddW m) (by rw [c]; exact Int.emod_nonneg _ (by decide))
  rw [c] at n
  obtain ⟨k, hk⟩ := hd
  omega_using [hv, n, hk]

theorem mulmod (a b n : Nat) : a % n * b % n = a * b % n := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem r2W_toInt : r2W.toInt = 1353 := by decide

/-- The two words of `BaseCaseMultiply` (`vbase`), from the words `a₀, a₁,
b₀, b₁` and `γ · 2¹⁶ mod q`. -/
theorem baseW {a0 a1 b0 b1 g : BitVec 16} {x0 x1 y0 y1 γ : Zq} (ha0 : a0.toNat = x0.val)
    (ha1 : a1.toNat = x1.val) (hb0 : b0.toNat = y0.val) (hb1 : b1.toNat = y1.val)
    (hg : g.toNat = γ.val * 65536 % 3329) :
    (caddW (montW (montW a0 b0 + montW (montW a1 b1) g) r2W)).toNat = (x0 * y0 + x1 * y1 * γ).val ∧
      (caddW (montW (montW a0 b1 + montW a1 b0) r2W)).toNat = (x0 * y1 + x1 * y0).val := by
  obtain ⟨A0, A0l, A0h⟩ := toInt_lt_q ha0
  obtain ⟨A1, A1l, A1h⟩ := toInt_lt_q ha1
  obtain ⟨B0, B0l, B0h⟩ := toInt_lt_q hb0
  obtain ⟨B1, B1l, B1h⟩ := toInt_lt_q hb1
  obtain hgl : g.toNat < 3329 := by rw [hg]; exact Nat.mod_lt _ (by decide)
  obtain G := toInt_of_lt hgl
  rw [hg] at G
  obtain Gl : 0 ≤ g.toInt ∧ g.toInt < 3329 := by
    rw [G]; exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (Nat.mod_lt _ (by decide))⟩
  have hγ := γ.isLt
  obtain kG : ∃ k : Int, g.toInt - (γ.val : Int) * 65536 = 3329 * k :=
    ⟨-((γ.val : Int) * 65536 / 3329), by rw [G]; omega_using []⟩
  obtain ⟨kG, hkG⟩ := kG
  obtain r2l : -3329 < r2W.toInt ∧ r2W.toInt < 3329 := by rw [r2W_toInt]; decide
  -- the products
  obtain ⟨m1l, m1h, ⟨k1, d1⟩⟩ := mont_small (d := a1) (z := b1) (by omega_using [A1l]) (by omega_using [A1h])
    (by omega_using [B1l]) (by omega_using [B1h])
  obtain ⟨m2l, m2h, ⟨k2, d2⟩⟩ := mont_small (d := montW a1 b1) (z := g) (by omega_using [m1l])
    (by omega_using [m1h]) (by omega_using [Gl]) (by omega_using [Gl])
  obtain ⟨m3l, m3h, ⟨k3, d3⟩⟩ := mont_small (d := a0) (z := b0) (by omega_using [A0l]) (by omega_using [A0h])
    (by omega_using [B0l]) (by omega_using [B0h])
  obtain ⟨n1l, n1h, ⟨j1, e1⟩⟩ := mont_small (d := a0) (z := b1) (by omega_using [A0l]) (by omega_using [A0h])
    (by omega_using [B1l]) (by omega_using [B1h])
  obtain ⟨n2l, n2h, ⟨j2, e2⟩⟩ := mont_small (d := a1) (z := b0) (by omega_using [A1l]) (by omega_using [A1h])
    (by omega_using [B0l]) (by omega_using [B0h])
  obtain S1 := toInt_add16 (a := montW a0 b0) (b := montW (montW a1 b1) g) (by omega_using [m3l, m2l])
    (by omega_using [m3h, m2h])
  obtain S2 := toInt_add16 (a := montW a0 b1) (b := montW a1 b0) (by omega_using [n1l, n2l])
    (by omega_using [n1h, n2h])
  obtain ⟨m4l, m4h, ⟨k4, d4⟩⟩ := mont_small (d := montW a0 b0 + montW (montW a1 b1) g) (z := r2W)
    (by rw [S1]; omega_using [m3l, m2l]) (by rw [S1]; omega_using [m3h, m2h]) r2l.1 r2l.2
  obtain ⟨n4l, n4h, ⟨j4, e4⟩⟩ := mont_small (d := montW a0 b1 + montW a1 b0) (z := r2W)
    (by rw [S2]; omega_using [n1l, n2l]) (by rw [S2]; omega_using [n1h, n2h]) r2l.1 r2l.2
  rw [S1, r2W_toInt] at d4
  rw [S2, r2W_toInt] at e4
  simp only [A0, A1, B0, B1] at d1 d3 e1 e2
  refine ⟨cadd_val m4l m4h (T := ((x0.val * y0.val + x1.val * y1.val * γ.val : Nat) : Int)) ?_ ?_,
    cadd_val n4l n4h (T := ((x0.val * y1.val + x1.val * y0.val : Nat) : Int)) ?_ ?_⟩
  · generalize (montW (montW a0 b0 + montW (montW a1 b1) g) r2W).toInt = M4 at *
    generalize (montW (montW a1 b1) g).toInt = M2 at *
    generalize (montW a0 b0).toInt = M3 at *
    generalize (montW a1 b1).toInt = M1 at *
    generalize g.toInt = Gi at *
    refine ⟨-3327 * M4 + 169 * k4 + 49 * (M3 + M2) + k3 + k2 + M1 * kG + γ.val * k1, ?_⟩
    simp only [Int.natCast_add, Int.natCast_mul]
    grind
  · rw [val_add', val_mul, val_mul, val_mul, mulmod, ← Nat.add_mod]; exact Int.natCast_emod _ _
  · generalize (montW (montW a0 b1 + montW a1 b0) r2W).toInt = M4 at *
    generalize (montW a0 b1).toInt = N1 at *
    generalize (montW a1 b0).toInt = N2 at *
    refine ⟨-3327 * M4 + 169 * j4 + 49 * (N1 + N2) + j1 + j2, ?_⟩
    simp only [Int.natCast_add, Int.natCast_mul]
    grind
  · rw [val_add', val_mul, val_mul, ← Nat.add_mod]; exact Int.natCast_emod _ _

end VG.Proof.MlKem.X86.W

/-! ## The words of a pair -/

namespace VG.Proof.MlKem.X86.Vec

open VG VG.X86 VG.X86.Lanes VG.Impl.MlKem.X86
open VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.X86.W

theorem ext16_shr (d : BitVec 32) : (d >>> 16).extractLsb' 0 16 = d.extractLsb' 16 16 ∧
    (d >>> 16).extractLsb' 16 16 = 0 := by
  have := d.isLt
  have z : (0 : BitVec 16).toNat = 0 := rfl
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow] <;>
    omega_using [this, z]

theorem ext16_shl (d : BitVec 32) : (d <<< 16).extractLsb' 0 16 = 0 ∧
    (d <<< 16).extractLsb' 16 16 = d.extractLsb' 0 16 := by
  have := d.isLt
  have z : (0 : BitVec 16).toNat = 0 := rfl
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      Nat.reducePow] <;>
    omega_using [this, z]

/-- The words of `psrld` by 16. -/
theorem word_psrld16 (a : BitVec 128) {j : Nat} (hj : j < 4) :
    word (XShiftOp.eval .psrld a 16) (2 * j) = word a (2 * j + 1) ∧
      word (XShiftOp.eval .psrld a 16) (2 * j + 1) = 0 := by
  have h0 := word_dword (XShiftOp.eval .psrld a 16) j 0 (by decide)
  have h1 := word_dword (XShiftOp.eval .psrld a 16) j 1 (by decide)
  rw [dword_psrld a 16 (by decide) hj] at h0 h1
  rw [Nat.add_zero] at h0
  exact ⟨h0.trans (((ext16_shr _).1).trans (word_dword a j 1 (by decide)).symm), h1.trans (ext16_shr _).2⟩

/-- The words of `pslld` by 16. -/
theorem word_pslld16 (a : BitVec 128) {j : Nat} (hj : j < 4) :
    word (XShiftOp.eval .pslld a 16) (2 * j) = 0 ∧
      word (XShiftOp.eval .pslld a 16) (2 * j + 1) = word a (2 * j) := by
  have h0 := word_dword (XShiftOp.eval .pslld a 16) j 0 (by decide)
  have h1 := word_dword (XShiftOp.eval .pslld a 16) j 1 (by decide)
  have h2 := word_dword a j 0 (by decide)
  rw [dword_pslld a 16 (by decide) hj] at h0 h1
  rw [Nat.add_zero] at h0 h2
  exact ⟨h0.trans (ext16_shl _).1, h1.trans (((ext16_shl _).2).trans h2.symm)⟩

theorem or_zero16 (x : BitVec 16) : x ||| 0 = x := BitVec.or_zero

theorem zero_or16 (x : BitVec 16) : 0 ||| x = x := BitVec.zero_or

theorem word_por (a b : BitVec 128) (i : Nat) : word (XBinOp.eval .por a b) i = word a i ||| word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [XBinOp.eval, BitVec.getLsbD_or, getLsbD_word _ _ _ hj]

/-- `2³² mod q` in each word. -/
def r2V : BitVec 128 := bc 0x05490549#32

theorem word_r2V {i : Nat} (hi : i < 8) : word r2V i = r2W := by
  rw [r2V, word_bc _ hi]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> rw [h] <;> rfl

/-- The pair `b` swapped: what `pshuflw` and `pshufhw` with `0xB1` leave. -/
def swapV (b : BitVec 128) : BitVec 128 := shufHighWords (shufLowWords b 0xB1) 0xB1

/-- The sums of a pair, as the two words of a doubleword: from
`P = mont(a, b)`, `T = mont(P, γ)` and `Q = mont(a, b')`. -/
def mergeV (P T Q : BitVec 128) : BitVec 128 :=
  XBinOp.eval .por
    (XShiftOp.eval .psrld (XShiftOp.eval .pslld (XBinOp.eval .paddw P (XShiftOp.eval .psrld T 16)) 16) 16)
    (XShiftOp.eval .pslld (XBinOp.eval .paddw Q (XShiftOp.eval .psrld Q 16)) 16)

/-- The words `mulCore` leaves of the pairs `A` and `B` and the `γ`s `G`. -/
def mulV (A B G : BitVec 128) : BitVec 128 :=
  caddV (montV (mergeV (montV A B) (montV (montV A B) G) (montV A (swapV B))) r2V)

/-- The four pairs of `mulV`. -/
theorem mul_lanes {A B G : BitVec 128} {x0 x1 y0 y1 γ : Nat → Zq}
    (ha : ∀ j < 4, (word A (2 * j)).toNat = (x0 j).val ∧ (word A (2 * j + 1)).toNat = (x1 j).val)
    (hb : ∀ j < 4, (word B (2 * j)).toNat = (y0 j).val ∧ (word B (2 * j + 1)).toNat = (y1 j).val)
    (hg : ∀ j < 4, (word G (2 * j + 1)).toNat = (γ j).val * 65536 % 3329) :
    ∀ j < 4, (word (mulV A B G) (2 * j)).toNat = (x0 j * y0 j + x1 j * y1 j * γ j).val ∧
      (word (mulV A B G) (2 * j + 1)).toNat = (x0 j * y1 j + x1 j * y0 j).val := by
  intro j hj
  have h0 : 2 * j < 8 := by omega_using [hj]
  have h1 : 2 * j + 1 < 8 := by omega_using [hj]
  have sw0 : word (swapV B) (2 * j) = word B (2 * j + 1) := by
    rw [swapV, word_rot16 _ h0]
    rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl
  have sw1 : word (swapV B) (2 * j + 1) = word B (2 * j) := by
    rw [swapV, word_rot16 _ h1]
    rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl
  have m0 : word (mergeV (montV A B) (montV (montV A B) G) (montV A (swapV B))) (2 * j) =
      montW (word A (2 * j)) (word B (2 * j)) +
        montW (montW (word A (2 * j + 1)) (word B (2 * j + 1))) (word G (2 * j + 1)) := by
    rw [mergeV, word_por, (word_pslld16 _ hj).1, or_zero16, (word_psrld16 _ hj).1, (word_pslld16 _ hj).2,
      word_paddw _ _ h0, (word_psrld16 _ hj).1, word_montV _ _ h0, word_montV _ _ h1, word_montV _ _ h1]
  have m1 : word (mergeV (montV A B) (montV (montV A B) G) (montV A (swapV B))) (2 * j + 1) =
      montW (word A (2 * j)) (word B (2 * j + 1)) + montW (word A (2 * j + 1)) (word B (2 * j)) := by
    rw [mergeV, word_por, (word_psrld16 _ hj).2, zero_or16, (word_pslld16 _ hj).2, word_paddw _ _ h0,
      (word_psrld16 _ hj).1, word_montV _ _ h0, word_montV _ _ h1, sw0, sw1]
  have key := baseW (ha j hj).1 (ha j hj).2 (hb j hj).1 (hb j hj).2 (hg j hj)
  rw [mulV, word_caddV _ h0, word_montV _ _ h0, word_caddV _ h1, word_montV _ _ h1, word_r2V h0, word_r2V h1, m0, m1]
  exact key

end VG.Proof.MlKem.X86.Vec

/-! ## The code of four pairs -/

namespace VG.Proof.MlKem.X86.Vec

open VG VG.X86 VG.X86.Lanes VG.Impl.MlKem.X86
open VG.Proof.MlKem VG.Spec.MlKem

variable {s : State}

/-- `wmont` on the registers `mulCore` multiplies in. -/
theorem wmontG_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d z : XReg} (hm : 0 < s.mcdt)
    (hc : VK f)
    (hdz : (d = .xmm3 ∧ z = .xmm5) ∨ (d = .xmm0 ∧ z = .xmm1) ∨ (d = .xmm1 ∧ z = .xmm5) ∨ (d = .xmm0 ∧ z = .xmm4))
    (k : ∀ g : XReg → BitVec 128, g d = montV (f d) (f z) → (∀ r, r ≠ d → r ≠ .xmm2 → g r = f r) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (wmont d z .xmm2 ++ is)) { s with xmm := f } Q := by
  rcases hdz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    refine wp_xs rfl (wp_ml hm (wp_ml hm (wp_mh hm (wp_mh hm (wp_xs rfl (k _ ?_ ?_))))))
    · simp only [montV]
      rw [← hc.q, ← hc.qi]
      rfl
    · intro r h0 h2
      simp only [h0, h2, ite_false]

/-- The instructions of `mulCore` that load four pairs of `f` and of `g`. -/
def mulLoad : List Instr :=
  [.movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 16), wb .packssdw .xmm0 .xmm2,
    .movdquLoad .xmm1 (at_ .ecx 0), .movdquLoad .xmm2 (at_ .ecx 16), wb .packssdw .xmm1 .xmm2,
    .xop (.pshuflw .xmm5 .xmm1 0xB1), .xop (.pshufhw .xmm5 .xmm5 0xB1), wmov .xmm3 .xmm0]

/-- Those that merge the sums. -/
def mulMerge : List Instr :=
  [.xop (.shift .psrld .xmm1 16), wb .paddw .xmm0 .xmm1, wmov .xmm1 .xmm3, .xop (.shift .psrld .xmm1 16),
    wb .paddw .xmm3 .xmm1, .xop (.shift .pslld .xmm0 16), .xop (.shift .psrld .xmm0 16),
    .xop (.shift .pslld .xmm3 16), wb .por .xmm0 .xmm3]

/-- Those that store four pairs of `h`. -/
def mulOut : List Instr :=
  [wmov .xmm1 .xmm0, wb .pxor .xmm2 .xmm2, wb .punpcklwd .xmm0 .xmm2, wb .punpckhwd .xmm1 .xmm2,
    .movdquStore (at_ .ebx 0) .xmm0, .movdquStore (at_ .ebx 16) .xmm1]

theorem mulCore_eq (is : List Instr) : mulCore ++ is =
    mulLoad ++ (wmont .xmm3 .xmm5 .xmm2 ++ (wmont .xmm0 .xmm1 .xmm2 ++ (zl2 ++ (wmov .xmm1 .xmm0 ::
      (wmont .xmm1 .xmm5 .xmm2 ++ (mulMerge ++ (wmont .xmm0 .xmm4 .xmm2 ++ (wcadd .xmm0 .xmm2 ++
        (mulOut ++ is))))))))) := by
  simp only [mulCore, mulLoad, mulMerge, mulOut, List.append_assoc, List.cons_append, List.nil_append]

theorem mulLoad_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {PF PF' PG PG' : Addr}
    (eF : s.ea (at_ .eax 0) = PF) (eF' : s.ea (at_ .eax 16) = PF') (eG : s.ea (at_ .ecx 0) = PG)
    (eG' : s.ea (at_ .ecx 16) = PG') (iF : InRegions (s.rd ++ s.wr) PF 16) (iF' : InRegions (s.rd ++ s.wr) PF' 16)
    (iG : InRegions (s.rd ++ s.wr) PG 16) (iG' : InRegions (s.rd ++ s.wr) PG' 16)
    (k : ∀ g : XReg → BitVec 128,
      g .xmm0 = XBinOp.eval .packssdw (s.mem.readW PF 128) (s.mem.readW PF' 128) →
      g .xmm3 = XBinOp.eval .packssdw (s.mem.readW PF 128) (s.mem.readW PF' 128) →
      g .xmm1 = XBinOp.eval .packssdw (s.mem.readW PG 128) (s.mem.readW PG' 128) →
      g .xmm5 = swapV (XBinOp.eval .packssdw (s.mem.readW PG 128) (s.mem.readW PG' 128)) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → r ≠ .xmm5 → g r = f r) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (mulLoad ++ is)) { s with xmm := f } Q := by
  refine wp_ld eF iF (wp_ld eF' iF' (wp_xs rfl (wp_ld eG iG (wp_ld eG' iG' (wp_xs rfl (wp_xs rfl (wp_xs rfl
    (wp_xs rfl (k _ rfl rfl rfl rfl ?_)))))))))
  intro r h0 h1 h2 h3 h5
  simp only [h0, h1, h2, h3, h5, ite_false]

theorem mulMerge_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = mergeV (f .xmm0) (f .xmm1) (f .xmm3) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm3 → g r = f r) → WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (mulMerge ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl
    (k _ rfl ?_)))))))))
  intro r h0 h1 h3
  simp only [h0, h1, h3, ite_false]

theorem mulOut_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {PH PH' : Addr}
    (eH : s.ea (at_ .ebx 0) = PH) (eH' : s.ea (at_ .ebx 16) = PH') (iH : InRegions s.wr PH 16)
    (iH' : InRegions s.wr PH' 16)
    (k : ∀ (g : XReg → BitVec 128) (L H : BitVec 128), L = XBinOp.eval .punpcklwd (f .xmm0) 0 →
      H = XBinOp.eval .punpckhwd (f .xmm0) 0 → (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → g r = f r) →
      WP isa (.block is) { ({ s with mem := (s.mem.writeW PH L).writeW PH' H } : State) with xmm := g } Q) :
    WP isa (.block (mulOut ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_st eH iH (wp_st eH' iH' (k _ _ _ ?_ ?_ ?_))))))
  · show XBinOp.eval .punpcklwd (f .xmm0) (XBinOp.eval .pxor (f .xmm2) (f .xmm2)) = _
    rw [pxor_self]
  · show XBinOp.eval .punpckhwd (f .xmm0) (XBinOp.eval .pxor (f .xmm2) (f .xmm2)) = _
    rw [pxor_self]
  · intro r h0 h1 h2
    simp only [h0, h1, h2, ite_false]

/-- `mulCore`: from the vectors at `[eax]`, `[eax + 16]`, `[ecx]` and
`[ecx + 16]` and the `γ`s at `[edx]`, it stores at `[ebx]` and
`[ebx + 16]` the `u32`s of the words of `mulV`. -/
theorem mulCore_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hm : 0 < s.mcdt) (hc : VK f)
    (h4 : f .xmm4 = r2V) {PF PF' PG PG' PT PH PH' : Addr}
    (eF : s.ea (at_ .eax 0) = PF) (eF' : s.ea (at_ .eax 16) = PF') (eG : s.ea (at_ .ecx 0) = PG)
    (eG' : s.ea (at_ .ecx 16) = PG') (eT : s.ea (at_ .edx 0) = PT) (eH : s.ea (at_ .ebx 0) = PH)
    (eH' : s.ea (at_ .ebx 16) = PH') (iF : InRegions (s.rd ++ s.wr) PF 16)
    (iF' : InRegions (s.rd ++ s.wr) PF' 16) (iG : InRegions (s.rd ++ s.wr) PG 16)
    (iG' : InRegions (s.rd ++ s.wr) PG' 16) (iT : InRegions (s.rd ++ s.wr) PT 8) (iH : InRegions s.wr PH 16)
    (iH' : InRegions s.wr PH' 16)
    (k : ∀ (g : XReg → BitVec 128) (V L H : BitVec 128),
      V = mulV (XBinOp.eval .packssdw (s.mem.readW PF 128) (s.mem.readW PF' 128))
        (XBinOp.eval .packssdw (s.mem.readW PG 128) (s.mem.readW PG' 128)) (zsel2 s.mem PT) →
      L = XBinOp.eval .punpcklwd V 0 → H = XBinOp.eval .punpckhwd V 0 → VK g → g .xmm4 = r2V →
      WP isa (.block is) { ({ s with mem := (s.mem.writeW PH L).writeW PH' H } : State) with xmm := g } Q) :
    WP isa (.block (mulCore ++ is)) { s with xmm := f } Q := by
  rw [mulCore_eq]
  refine mulLoad_wp eF eF' eG eG' iF iF' iG iG' fun g₀ a0 a3 b1 b5 r₀ => ?_
  have c₀ : VK g₀ := hc.of_eq (r₀ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (r₀ _ (by decide) (by decide) (by decide) (by decide) (by decide))
  refine wmontG_wp hm c₀ (.inl ⟨rfl, rfl⟩) fun g₁ v₁ r₁ => ?_
  have c₁ : VK g₁ := c₀.of_eq (r₁ _ (by decide) (by decide)) (r₁ _ (by decide) (by decide))
  refine wmontG_wp hm c₁ (.inr (.inl ⟨rfl, rfl⟩)) fun g₂ v₂ r₂ => ?_
  have c₂ : VK g₂ := c₁.of_eq (r₂ _ (by decide) (by decide)) (r₂ _ (by decide) (by decide))
  have P2 : g₂ .xmm0 = montV (g₀ .xmm0) (g₀ .xmm1) := by
    rw [v₂, r₁ _ (by decide) (by decide), r₁ _ (by decide) (by decide)]
  have Q2 : g₂ .xmm3 = montV (g₀ .xmm3) (g₀ .xmm5) := by rw [r₂ _ (by decide) (by decide), v₁]
  have R2 : g₂ .xmm4 = r2V := by
    rw [r₂ _ (by decide) (by decide), r₁ _ (by decide) (by decide),
      r₀ _ (by decide) (by decide) (by decide) (by decide) (by decide), h4]
  refine zl2_ok _ _ _ _ _ eT iT fun g₃ z₃ r₃ => wp_xs rfl ?_
  have c₃ : VK g₃ := c₂.of_eq (r₃ _ (by decide)) (r₃ _ (by decide))
  refine wmontG_wp hm (c₃.of_eq rfl rfl) (.inr (.inr (.inl ⟨rfl, rfl⟩))) fun g₄ v₄ r₄ => ?_
  have T4 : g₄ .xmm1 = montV (g₃ .xmm0) (g₃ .xmm5) := v₄
  have P4 : g₄ .xmm0 = g₃ .xmm0 := r₄ _ (by decide) (by decide)
  have Q4 : g₄ .xmm3 = g₃ .xmm3 := r₄ _ (by decide) (by decide)
  have R4 : g₄ .xmm4 = g₃ .xmm4 := r₄ _ (by decide) (by decide)
  have c₄ : VK g₄ := c₃.of_eq (r₄ _ (by decide) (by decide)) (r₄ _ (by decide) (by decide))
  refine mulMerge_wp fun g₅ v₅ r₅ => ?_
  have c₅ : VK g₅ := c₄.of_eq (r₅ _ (by decide) (by decide) (by decide)) (r₅ _ (by decide) (by decide) (by decide))
  refine wmontG_wp hm c₅ (.inr (.inr (.inr ⟨rfl, rfl⟩))) fun g₆ v₆ r₆ => ?_
  have c₆ : VK g₆ := c₅.of_eq (r₆ _ (by decide) (by decide)) (r₆ _ (by decide) (by decide))
  refine wcadd_wp (.inl rfl) c₆ fun g₇ v₇ r₇ => ?_
  have c₇ : VK g₇ := c₆.of_eq (r₇ _ (by decide) (by decide)) (r₇ _ (by decide) (by decide))
  have R7 : g₇ .xmm4 = r2V := by
    rw [r₇ .xmm4 (by decide) (by decide), r₆ .xmm4 (by decide) (by decide),
      r₅ .xmm4 (by decide) (by decide) (by decide), R4, r₃ .xmm4 (by decide), R2]
  have H7 : g₇ .xmm0 = mulV (XBinOp.eval .packssdw (s.mem.readW PF 128) (s.mem.readW PF' 128))
      (XBinOp.eval .packssdw (s.mem.readW PG 128) (s.mem.readW PG' 128)) (zsel2 s.mem PT) := by
    rw [v₇, v₆, v₅, r₅ .xmm4 (by decide) (by decide) (by decide), R4, r₃ .xmm4 (by decide), R2, T4, P4, Q4,
      r₃ .xmm0 (by decide), r₃ .xmm3 (by decide), z₃, P2, Q2, a0, a3, b1, b5]
    rfl
  refine mulOut_wp eH eH' iH iH' fun g₈ L H eL eHh r₈ => ?_
  exact k g₈ _ L H rfl (by rw [eL, H7]) (by rw [eHh, H7])
    (c₇.of_eq (r₈ _ (by decide) (by decide) (by decide)) (r₈ _ (by decide) (by decide) (by decide)))
    ((r₈ _ (by decide) (by decide) (by decide)).trans R7)

end VG.Proof.MlKem.X86.Vec

/-! ## `vg_mlkem_multiply_ntts` -/

namespace VG.Proof.MlKem.X86.Mul

open VG VG.X86 VG.X86.Lanes VG.Impl.MlKem.X86
open VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Vec
open VG.Proof.MlKem.X86.Piece (sse)

section
variable (s₀ : State)
abbrev hP : BitVec 32 := arg s₀ 0
abbrev fP : BitVec 32 := arg s₀ 1
abbrev gP : BitVec 32 := arg s₀ 2
abbrev sP : BitVec 32 := arg s₀ 3
abbrev hA : Addr := (hP s₀).setWidth 64
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev gA : Addr := (gP s₀).setWidth 64
abbrev sA : Addr := (sP s₀).setWidth 64
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
abbrev Fp : Poly := polyAt s₀.mem (fA s₀)
abbrev Gp : Poly := polyAt s₀.mem (gA s₀)
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (fA s₀), polyRegion (gA s₀)]
  wr : s₀.wr = [polyRegion (hA s₀), polyRegion (sA s₀), aR s₀]
  h_f : (polyRegion (hA s₀)).Disjoint (polyRegion (fA s₀))
  h_g : (polyRegion (hA s₀)).Disjoint (polyRegion (gA s₀))
  h_s : (polyRegion (hA s₀)).Disjoint (polyRegion (sA s₀))
  h_a : (polyRegion (hA s₀)).Disjoint (aR s₀)
  f_s : (polyRegion (fA s₀)).Disjoint (polyRegion (sA s₀))
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  g_s : (polyRegion (gA s₀)).Disjoint (polyRegion (sA s₀))
  g_a : (polyRegion (gA s₀)).Disjoint (aR s₀)
  s_a : (polyRegion (sA s₀)).Disjoint (aR s₀)
  ret_h : (retR s₀).Disjoint (polyRegion (hA s₀))
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_g : (retR s₀).Disjoint (polyRegion (gA s₀))
  ret_s : (retR s₀).Disjoint (polyRegion (sA s₀))
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_h : (stkR s₀).Disjoint (polyRegion (hA s₀))
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_g : (stkR s₀).Disjoint (polyRegion (gA s₀))
  stk_s : (stkR s₀).Disjoint (polyRegion (sA s₀))
  stk_a : (stkR s₀).Disjoint (aR s₀)
  h_fit : (hP s₀).toNat + 1024 ≤ 2 ^ 32
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  g_fit : (gP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (sP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (fA s₀)
  g_red : Reduced s₀.mem (gA s₀)

theorem Pre.of {s₀ : State} (h : (mulContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

theorem Pre.arg_in {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) : (aR s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp'
  simp only [argAddr, Region.Contains, E0] at this ⊢
  bv_omega

theorem arg_sep {s₀ : State} (hp : Pre s₀) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) :
    Mem.Sep (argAddr s₀ i) 4 (argAddr s₀ j) 4 := by
  have := hp.sp'
  intro x h₁ h₂
  simp only [argAddr, E0] at this h₁ h₂
  have : i < j ∨ j < i := by omega_using [h]
  bv_omega

/-- The regions the function writes, apart from its frame. -/
abbrev W (s₀ : State) : List Region := [polyRegion (hA s₀), polyRegion (sA s₀), aR s₀]

section
variable (s₀ : State)
/-- The state the body starts in: after the MCDT frame's push and the push of `ebx`. -/
abbrev B0 : State := pushed [.ebx] (M0 s₀)
/-- The slot of `ebx`. -/
abbrev bR : Region := below (E0 s₀ - 12) 4
end

theorem sp12 {s₀ : State} (hp : Pre s₀) : 12 ≤ (E0 s₀).toNat := by have := hp.sp; omega_using [this]

theorem B0_esp {s₀ : State} (hp : Pre s₀) : (B0 s₀).gpr .esp = E0 s₀ - 16 := by
  rw [pushed_esp, M0_esp]
  have := hp.sp
  simp only [List.length_cons, List.length_nil]
  bv_omega

theorem B0_wr (s₀ : State) :
    (B0 s₀).wr = below ((M0 s₀).gpr .esp) (4 * [Reg.ebx].length) :: ⟨(E0 s₀ - 12).setWidth 64, 9⟩ :: s₀.wr := rfl

theorem mcdt_disj {s₀ : State} (hp : Pre s₀) {R : Region} (h : (stkR s₀).Disjoint R) :
    (mcdtR s₀).Disjoint R := by
  intro a h₁ h₂
  refine h a ?_ h₂
  have := hp.sp
  have := (E0 s₀).isLt
  simp only [Region.Contains] at h₁ ⊢
  bv_omega

theorem slot_disj {s₀ : State} (hp : Pre s₀) {R : Region} (h : (stkR s₀).Disjoint R) : (bR s₀).Disjoint R := by
  intro a h₁ h₂
  refine h a ?_ h₂
  have := hp.sp
  have := (E0 s₀).isLt
  simp only [Region.Contains] at h₁ ⊢
  bv_omega

theorem M0_B0 {s₀ : State} (hp : Pre s₀) : Frame [bR s₀] (M0 s₀).mem (B0 s₀).mem := by
  have h := pushed_frame (rs := [.ebx]) (s := M0 s₀) (by decide) (by
    rw [M0_esp]; have := hp.sp; simp only [List.length_cons, List.length_nil]; bv_omega)
  rwa [M0_esp] at h

theorem B0_frame {s₀ : State} (hp : Pre s₀) : Frame [mcdtR s₀, bR s₀] s₀.mem (B0 s₀).mem :=
  ((M0_frame s₀ (sp12 hp)).mono (by simp)).trans ((M0_B0 hp).mono (by simp))

/-- The arguments, at `[esp + 20 + 4i]` in the body. -/
theorem arg_B0 {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) :
    ((B0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      (B0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  refine ⟨?_, ?_⟩
  · rw [B0_esp hp]; simp only [argAddr, E0]; congr 1; have := hp.sp; have := hp.sp'; bv_omega
  · exact (B0_frame hp).readW (hp.arg_in hi) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (mcdt_disj hp hp.stk_a).symm
      · exact (slot_disj hp hp.stk_a).symm) (by decide)

theorem in_w {s₀ : State} (hp : Pre s₀) {s : State} (hw : s.wr = (B0 s₀).wr) {R : Region} (hR : R ∈ W s₀)
    {a : Addr} {n : Nat} (hc : R.Contains a n) : InRegions s.wr a n :=
  ⟨R, by rw [hw, B0_wr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR), hc⟩

theorem in_r {s₀ : State} (hp : Pre s₀) {s : State} (hr' : s.rd = (B0 s₀).rd) {R : Region}
    (hR : R ∈ [polyRegion (fA s₀), polyRegion (gA s₀)]) {a : Addr} {n : Nat} (hc : R.Contains a n) :
    InRegions (s.rd ++ s.wr) a n :=
  ⟨R, List.mem_append_left _ (by rw [hr', pushed_rd, M0_rd, hp.rd]; exact hR), hc⟩

/-- `f` and `g` keep their values. -/
theorem keep {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame (W s₀) (B0 s₀).mem m) {p : Addr}
    (hd : ∀ r ∈ mcdtR s₀ :: bR s₀ :: W s₀, (polyRegion p).Disjoint r) {i : Nat} (hi : i < 256) :
    coeffAt m p i = coeffAt s₀.mem p i :=
  coeffAt_congr (fun j hj => bytes_frame (((B0_frame hp).mono (by simp)).trans (hf.mono (by simp))) hd
    (by decide) j hj) (by rw [n_eq]; exact hi)

theorem f_keep {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame (W s₀) (B0 s₀).mem m) {i : Nat} (hi : i < 256) :
    coeffAt m (fA s₀) i = coeffAt s₀.mem (fA s₀) i := by
  refine keep hp hf (fun r hr => ?_) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (mcdt_disj hp hp.stk_f).symm
  · exact (slot_disj hp hp.stk_f).symm
  · exact hp.h_f.symm
  · exact hp.f_s
  · exact hp.f_a

theorem g_keep {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame (W s₀) (B0 s₀).mem m) {i : Nat} (hi : i < 256) :
    coeffAt m (gA s₀) i = coeffAt s₀.mem (gA s₀) i := by
  refine keep hp hf (fun r hr => ?_) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (mcdt_disj hp hp.stk_g).symm
  · exact (slot_disj hp hp.stk_g).symm
  · exact hp.h_g.symm
  · exact hp.g_s
  · exact hp.g_a

theorem montGammas_getD {k : Nat} (hk : k < 128) : montGammas.getD k 0 = (gamma k).val * 65536 % 3329 := by
  have h1 : gammaTable.getD k 0 = (gamma k).val := gammas_getD hk
  rw [← h1, montGammas, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (show k < gammaTable.length by
      rw [show gammaTable.length = 128 from gammas_length]; exact hk)]
  rfl

theorem montGammas_lt {k : Nat} (hk : k < 128) : montGammas.getD k 0 < 65536 := by
  rw [montGammas_getD hk]; exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)

/-- Before group `k` of four pairs. -/
structure MI (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (B0 s₀).gpr .esp
  rd : s.rd = (B0 s₀).rd
  wr : s.wr = (B0 s₀).wr
  mcdt : s.mcdt = s₀.mcdt + 1
  saved : ∀ r ∈ [Reg.esi, .edi, .ebp], s.gpr r = s₀.gpr r
  frame : Frame (W s₀) (B0 s₀).mem s.mem
  vk : VK s.xmm
  r2 : s.xmm .xmm4 = r2V
  eax : s.gpr .eax = fP s₀ + BitVec.ofNat 32 (16 * (2 * k))
  ecx : s.gpr .ecx = gP s₀ + BitVec.ofNat 32 (16 * (2 * k))
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (2 * (4 * k))
  ebx : s.gpr .ebx = hP s₀ + BitVec.ofNat 32 (16 * (2 * k))
  tbl : ∀ j < 128, wAt s.mem (sA s₀) j = BitVec.ofNat 16 (montGammas.getD j 0)
  slot : s.mem.readW (argAddr s₀ 3) 32 = hP s₀ + 1024
  out : ∀ i < 8 * k, (coeffAt s.mem (hA s₀) i).toNat = ((multiplyNTTs (Fp s₀) (Gp s₀))[i]!).val

/-- The eight coefficients of a reduced polynomial at `p + 32k`, as the words `packssdw` makes of them. -/
theorem pack_lanes {m m₀ : Mem} {p : Addr} (hk : ∀ i < 256, coeffAt m p i = coeffAt m₀ p i) (hr : Reduced m₀ p)
    {k : Nat} (hk32 : k < 32) {e : Nat} (he : e < 8) :
    (word (XBinOp.eval .packssdw (m.readW (p + BitVec.ofNat 64 (16 * (2 * k))) 128)
      (m.readW (p + BitVec.ofNat 64 (16 * (2 * k + 1))) 128)) e).toNat = ((polyAt m₀ p)[8 * k + e]!).val := by
  have small : ∀ u, u < 64 → ∀ j < 4,
      (dword (m.readW (p + BitVec.ofNat 64 (16 * u)) 128) j).toNat = ((polyAt m₀ p)[4 * u + j]!).val ∧
        (dword (m.readW (p + BitVec.ofNat 64 (16 * u)) 128) j).toNat < 32768 := fun u hu j hj => by
    have hi : 4 * u + j < n := by rw [n_eq]; omega_using [hu, hj]
    have h := hr _ hi
    rw [dword_rd16 _ _ _ hj, hk _ hi, polyAt_val hr hi]
    exact ⟨rfl, Nat.lt_trans h (by decide)⟩
  rw [word_packssdw_small _ _ he (fun j hj => (small _ (by omega_using [hk32]) j hj).2)
    (fun j hj => (small _ (by omega_using [hk32]) j hj).2)]
  by_cases h4 : e < 4
  · rw [ite_eq_left h4, (small _ (by omega_using [hk32]) e h4).1]
    exact congrArg (fun i : Nat => ((polyAt m₀ p)[i]!).val) (by omega_using [])
  · rw [ite_eq_right h4, (small _ (by omega_using [hk32]) (e - 4) (by omega_using [he, h4])).1]
    exact congrArg (fun i : Nat => ((polyAt m₀ p)[i]!).val) (by omega_using [h4])

theorem mstep {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 32) {s : State} (h : MI s₀ k s) :
    WP isa (.block (mulCore ++ mulEnd)) s fun s' =>
      MI s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 32)) := by
  have ff := hp.f_fit
  have gf := hp.g_fit
  have hf' := hp.h_fit
  have sf := hp.s_fit
  have eF : s.ea (at_ .eax 0) = fA s₀ + BitVec.ofNat 64 (16 * (2 * k)) := by
    rw [Vec.ea_at h.eax (by omega_using [ff, hk]), Nat.add_zero]
  have eF' : s.ea (at_ .eax 16) = fA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1)) := by
    rw [Vec.ea_at h.eax (by omega_using [ff, hk])]
    exact congrArg (fun j => fA s₀ + BitVec.ofNat 64 j) (by omega_using [])
  have eG : s.ea (at_ .ecx 0) = gA s₀ + BitVec.ofNat 64 (16 * (2 * k)) := by
    rw [Vec.ea_at h.ecx (by omega_using [gf, hk]), Nat.add_zero]
  have eG' : s.ea (at_ .ecx 16) = gA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1)) := by
    rw [Vec.ea_at h.ecx (by omega_using [gf, hk])]
    exact congrArg (fun j => gA s₀ + BitVec.ofNat 64 j) (by omega_using [])
  have eT : s.ea (at_ .edx 0) = sA s₀ + BitVec.ofNat 64 (2 * (4 * k)) := by
    rw [Vec.ea_at h.edx (by omega_using [sf, hk]), Nat.add_zero]
  have eH : s.ea (at_ .ebx 0) = hA s₀ + BitVec.ofNat 64 (16 * (2 * k)) := by
    rw [Vec.ea_at h.ebx (by omega_using [hf', hk]), Nat.add_zero]
  have eH' : s.ea (at_ .ebx 16) = hA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1)) := by
    rw [Vec.ea_at h.ebx (by omega_using [hf', hk])]
    exact congrArg (fun j => hA s₀ + BitVec.ofNat 64 j) (by omega_using [])
  have hm : 0 < s.mcdt := by rw [h.mcdt]; exact Nat.succ_pos _
  have hcon : (polyRegion (hA s₀)).Contains (hA s₀ + BitVec.ofNat 64 (16 * (2 * k))) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  have hcon' : (polyRegion (hA s₀)).Contains (hA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1))) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  show WP isa (.block (mulCore ++ mulEnd)) { s with xmm := s.xmm } _
  refine mulCore_wp hm h.vk h.r2 eF eF' eG eG' eT eH eH'
    (in_r hp h.rd (R := polyRegion (fA s₀)) (by simp)
      (Offset.contains_base (fA s₀) (by omega_using [hk]) (by omega_using [hk])))
    (in_r hp h.rd (R := polyRegion (fA s₀)) (by simp)
      (Offset.contains_base (fA s₀) (by omega_using [hk]) (by omega_using [hk])))
    (in_r hp h.rd (R := polyRegion (gA s₀)) (by simp)
      (Offset.contains_base (gA s₀) (by omega_using [hk]) (by omega_using [hk])))
    (in_r hp h.rd (R := polyRegion (gA s₀)) (by simp)
      (Offset.contains_base (gA s₀) (by omega_using [hk]) (by omega_using [hk])))
    (inRdN (in_w hp h.wr (R := polyRegion (sA s₀)) (by simp)
      (Offset.contains_base (sA s₀) (by omega_using [hk]) (by omega_using [hk]))))
    (in_w hp h.wr (R := polyRegion (hA s₀)) (by simp) hcon) (in_w hp h.wr (R := polyRegion (hA s₀)) (by simp) hcon') fun g V L H eV eL eH₂ cg g4 => ?_
  subst eL eH₂
  have lanes : ∀ e < 8, (word V e).toNat = ((multiplyNTTs (Fp s₀) (Gp s₀))[8 * k + e]!).val := by
    have key := mul_lanes (A := XBinOp.eval .packssdw (s.mem.readW (fA s₀ + BitVec.ofNat 64 (16 * (2 * k))) 128)
        (s.mem.readW (fA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1))) 128))
      (B := XBinOp.eval .packssdw (s.mem.readW (gA s₀ + BitVec.ofNat 64 (16 * (2 * k))) 128)
        (s.mem.readW (gA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1))) 128))
      (G := zsel2 s.mem (sA s₀ + BitVec.ofNat 64 (2 * (4 * k))))
      (x0 := fun j => (Fp s₀)[2 * (4 * k + j)]!) (x1 := fun j => (Fp s₀)[2 * (4 * k + j) + 1]!)
      (y0 := fun j => (Gp s₀)[2 * (4 * k + j)]!) (y1 := fun j => (Gp s₀)[2 * (4 * k + j) + 1]!)
      (γ := fun j => gamma (4 * k + j))
      (fun j hj => ⟨by
          rw [pack_lanes (fun i hi => f_keep hp h.frame hi) hp.f_red hk (by omega_using [hj])]
          exact congrArg (fun i : Nat => ((Fp s₀)[i]!).val) (by omega_using []), by
          rw [pack_lanes (fun i hi => f_keep hp h.frame hi) hp.f_red hk (by omega_using [hj])]
          exact congrArg (fun i : Nat => ((Fp s₀)[i]!).val) (by omega_using [])⟩)
      (fun j hj => ⟨by
          rw [pack_lanes (fun i hi => g_keep hp h.frame hi) hp.g_red hk (by omega_using [hj])]
          exact congrArg (fun i : Nat => ((Gp s₀)[i]!).val) (by omega_using []), by
          rw [pack_lanes (fun i hi => g_keep hp h.frame hi) hp.g_red hk (by omega_using [hj])]
          exact congrArg (fun i : Nat => ((Gp s₀)[i]!).val) (by omega_using [])⟩)
      (fun j hj => by
        rw [word_zsel2 _ _ _ (by omega_using [hj]), show 4 * k + (2 * j + 1) / 2 = 4 * k + j by omega_using [],
          h.tbl _ (by omega_using [hk, hj]), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (montGammas_lt (by omega_using [hk, hj])), montGammas_getD (by omega_using [hk, hj])])
    intro e he
    rw [eV]
    rcases Nat.mod_two_eq_zero_or_one e with h0 | h1
    · have := (key (e / 2) (by omega_using [he])).1
      rw [show 2 * (e / 2) = e by omega_using [h0]] at this
      rw [this, show 8 * k + e = 2 * (4 * k + e / 2) by omega_using [h0],
        multiplyNTTs_even _ _ (by omega_using [hk, he])]
    · have := (key (e / 2) (by omega_using [he])).2
      rw [show 2 * (e / 2) + 1 = e by omega_using [h1]] at this
      rw [this, show 8 * k + e = 2 * (4 * k + e / 2) + 1 by omega_using [h1],
        multiplyNTTs_odd _ _ (by omega_using [hk, he])]
  have vL : ∀ j < 4, (dword (XBinOp.eval .punpcklwd V 0) j).toNat =
      ((multiplyNTTs (Fp s₀) (Gp s₀))[8 * k + j]!).val :=
    fun j hj => by rw [dword_punpcklwd0 _ hj]; exact lanes j (by omega_using [hj])
  have vH : ∀ j < 4, (dword (XBinOp.eval .punpckhwd V 0) j).toNat =
      ((multiplyNTTs (Fp s₀) (Gp s₀))[8 * k + (4 + j)]!).val :=
    fun j hj => by rw [dword_punpckhwd0 _ hj]; exact lanes (4 + j) (by omega_using [hj])
  have hfr : Frame [polyRegion (hA s₀)] s.mem ((s.mem.writeW (hA s₀ + BitVec.ofNat 64 (16 * (2 * k)))
      (XBinOp.eval .punpcklwd V 0)).writeW (hA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1)))
      (XBinOp.eval .punpckhwd V 0)) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ hcon).writeW (List.mem_singleton_self _) _ hcon'
  obtain ⟨a₃, -⟩ := arg_B0 hp (i := 3) (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at a₃
  have ea : (s.gpr .esp + BitVec.ofNat 32 32).setWidth 64 = argAddr s₀ 3 := by rw [h.esp]; exact a₃
  have i₃ : InRegions (s.rd ++ s.wr) (argAddr s₀ 3) 4 :=
    inRdN (in_w hp h.wr (R := aR s₀) (by simp) (hp.arg_in (by decide)))
  have sl : ((s.mem.writeW (hA s₀ + BitVec.ofNat 64 (16 * (2 * k))) (XBinOp.eval .punpcklwd V 0)).writeW
      (hA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1))) (XBinOp.eval .punpckhwd V 0)).readW (argAddr s₀ 3) 32 =
      hP s₀ + 1024 := by
    rw [hfr.readW (hp.arg_in (by decide)) (by simpa using hp.h_a.symm) (by decide)]; exact h.slot
  have e1 : s.gpr .ebx + 32 = hP s₀ + BitVec.ofNat 32 (16 * (2 * (k + 1))) := by
    rw [h.ebx, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, add_ofNat_add]
    exact congrArg (fun j => hP s₀ + BitVec.ofNat 32 j) (by omega_using [])
  apply WP.of_runBlock
  simp only [mulEnd, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, ea, i₃, sl, reduceCtorEq, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.esp, h.rd, h.wr, h.mcdt, fun r hr => ?_, h.frame.trans (hfr.mono (by simp)), cg, g4, ?_, ?_, ?_, e1,
    fun j hj => ?_, sl, fun i hi => ?_⟩, ?_⟩
  · have := h.saved r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact this
  · show s.gpr .eax + 32 = _
    rw [h.eax, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, add_ofNat_add]
    exact congrArg (fun j => fP s₀ + BitVec.ofNat 32 j) (by omega_using [])
  · show s.gpr .ecx + 32 = _
    rw [h.ecx, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, add_ofNat_add]
    exact congrArg (fun j => gP s₀ + BitVec.ofNat 32 j) (by omega_using [])
  · show s.gpr .edx + 8 = _
    rw [h.edx, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_add]
    exact congrArg (fun j => sP s₀ + BitVec.ofNat 32 j) (by omega_using [])
  · show (Mem.writeW (Mem.writeW s.mem _ _) _ _).readW (sA s₀ + BitVec.ofNat 64 (2 * j)) 16 = _
    rw [hfr.readW (r := polyRegion (sA s₀)) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (by simpa using hp.h_s.symm) (by decide)]
    exact h.tbl j hj
  · show (coeffAt (Mem.writeW (Mem.writeW s.mem _ _) _ _) (hA s₀) i).toNat = _
    rw [cAt_write16 _ _ _ (by omega_using [hk]) (by omega_using [hi, hk]),
      cAt_write16 _ _ _ (by omega_using [hk]) (by omega_using [hi, hk])]
    by_cases h2 : 8 * k + 4 ≤ i
    · rw [ite_eq_left (by omega_using [h2, hi]), vH _ (by omega_using [h2, hi])]
      exact congrArg (fun j : Nat => ((multiplyNTTs (Fp s₀) (Gp s₀))[j]!).val) (by omega_using [h2])
    · rw [ite_eq_right (by omega_using [h2])]
      by_cases h1 : 8 * k ≤ i
      · rw [ite_eq_left (by omega_using [h1, h2]), vL _ (by omega_using [h1, h2])]
        exact congrArg (fun j : Nat => ((multiplyNTTs (Fp s₀) (Gp s₀))[j]!).val) (by omega_using [h1])
      · rw [ite_eq_right (by omega_using [h1])]; exact h.out i (by omega_using [h1])
  · show (some (s.gpr .ebx + 32 - (hP s₀ + 1024) == 0) : Option Bool).map (!·) = _
    rw [e1, NttLoop.end_cmp _ (by omega_using [hk])]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h1 : k + 1 < 32
    · rw [decide_eq_true h1, decide_eq_false (by omega_using [h1])]; rfl
    · rw [decide_eq_false h1, decide_eq_true (by omega_using [hk, h1])]; rfl

/-- After the constants: `eax` is `scratch`. -/
structure S1 (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (B0 s₀).gpr .esp
  eax : s.gpr .eax = sP s₀
  rd : s.rd = (B0 s₀).rd
  wr : s.wr = (B0 s₀).wr
  mem : s.mem = (B0 s₀).mem
  mcdt : s.mcdt = s₀.mcdt + 1
  saved : ∀ r ∈ [Reg.esi, .edi, .ebp], s.gpr r = s₀.gpr r
  vk : VK s.xmm
  r2 : s.xmm .xmm4 = r2V

theorem consts_wp {s₀ : State} (hp : Pre s₀) : WP isa (.block mulConsts) (B0 s₀) (S1 s₀) := by
  obtain ⟨a₃, v₃⟩ := arg_B0 hp (i := 3) (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at a₃
  have i₃ : InRegions ((B0 s₀).rd ++ (B0 s₀).wr) (argAddr s₀ 3) 4 :=
    inRdN (in_w hp rfl (R := aR s₀) (by simp) (hp.arg_in (by decide)))
  apply WP.of_runBlock
  simp only [mulConsts, wconst, at_, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, State.setXmm, readSrc, State.ea, State.load32, State.setReg, a₃, i₃, v₃, Option.map_some,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => ?_, ⟨bc_eq _, bc_eq _⟩, bc_eq _⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rfl

theorem table_wp {s₀ : State} (hp : Pre s₀) {s : State} (h : S1 s₀ s) :
    WP isa (.block mulTable) s (MI s₀ 0) := by
  have sf := hp.s_fit
  obtain ⟨a₀, v₀⟩ := arg_B0 hp (i := 0) (by decide)
  obtain ⟨a₁, v₁⟩ := arg_B0 hp (i := 1) (by decide)
  obtain ⟨a₂, v₂⟩ := arg_B0 hp (i := 2) (by decide)
  obtain ⟨a₃, -⟩ := arg_B0 hp (i := 3) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a₀ a₁ a₂ a₃
  rw [mulTable, wtable_eq]
  refine wtableN_spec montGammas (p := sA s₀) 64 _ _ _ (Nat.le_refl _) (fun k hk => ?_) (fun k hk => ?_)
    fun s₂ o₂ f₂ c₂ => ?_
  · show (s.gpr .eax + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
    rw [h.eax]
    exact ea_off (by omega_using [sf, hk])
  · exact in_w hp h.wr (R := polyRegion (sA s₀)) (by simp) (Offset.contains_base (sA s₀) (by omega_using [hk]) (by omega_using [hk]))
  have esp₂ : s₂.gpr .esp = (B0 s₀).gpr .esp := (o₂.gpr .esp (by decide)).trans h.esp
  have eax₂ : s₂.gpr .eax = sP s₀ := (o₂.gpr .eax (by decide)).trans h.eax
  have rd₂ : s₂.rd = (B0 s₀).rd := o₂.rd.trans h.rd
  have wr₂ : s₂.wr = (B0 s₀).wr := o₂.wr.trans h.wr
  have f₂' : Frame [polyRegion (sA s₀)] (B0 s₀).mem s₂.mem := h.mem ▸ f₂
  have e20 : (s₂.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by rw [esp₂]; exact a₀
  have e24 : (s₂.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by rw [esp₂]; exact a₁
  have e28 : (s₂.gpr .esp + BitVec.ofNat 32 28).setWidth 64 = argAddr s₀ 2 := by rw [esp₂]; exact a₂
  have e32 : (s₂.gpr .esp + BitVec.ofNat 32 32).setWidth 64 = argAddr s₀ 3 := by rw [esp₂]; exact a₃
  have in0 : InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ 0) 4 := inRdN (in_w hp wr₂ (R := aR s₀) (by simp) (hp.arg_in (by decide)))
  have in1 : InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ 1) 4 := inRdN (in_w hp wr₂ (R := aR s₀) (by simp) (hp.arg_in (by decide)))
  have in2 : InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ 2) 4 := inRdN (in_w hp wr₂ (R := aR s₀) (by simp) (hp.arg_in (by decide)))
  have in3 : InRegions s₂.wr (argAddr s₀ 3) 4 := in_w hp wr₂ (R := aR s₀) (by simp) (hp.arg_in (by decide))
  have hsa : ∀ r ∈ [polyRegion (sA s₀)], (aR s₀).Disjoint r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hp.s_a.symm
  have w0 : s₂.mem.readW (argAddr s₀ 0) 32 = hP s₀ := by
    rw [f₂'.readW (hp.arg_in (by decide)) hsa (by decide)]; exact v₀
  have w1 : (s₂.mem.writeW (argAddr s₀ 3) (hP s₀ + 1024)).readW (argAddr s₀ 1) 32 = fP s₀ := by
    rw [Mem.readW_writeW_sep (arg_sep hp (by decide) (by decide) (by decide)) (by decide),
      f₂'.readW (hp.arg_in (by decide)) hsa (by decide)]; exact v₁
  have w2 : (s₂.mem.writeW (argAddr s₀ 3) (hP s₀ + 1024)).readW (argAddr s₀ 2) 32 = gP s₀ := by
    rw [Mem.readW_writeW_sep (arg_sep hp (by decide) (by decide) (by decide)) (by decide),
      f₂'.readW (hp.arg_in (by decide)) hsa (by decide)]; exact v₂
  apply WP.of_runBlock
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
    State.store32, State.setReg, arithFlags, State.setFlags, Option.map_some, Option.bind_some, e20, e24, e28, e32,
    in0, in1, in2, in3, w0, w1, w2, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  have fr : Frame (W s₀) (B0 s₀).mem (s₂.mem.writeW (argAddr s₀ 3) (hP s₀ + 1024)) :=
    (f₂'.mono fun r hr => by simp at hr ⊢; exact .inr (.inl hr)).writeW (by simp) _ (hp.arg_in (by decide))
  refine ⟨esp₂, rd₂, wr₂, o₂.mcdt.trans h.mcdt, fun r hr => ?_, fr, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_,
    fun i hi => absurd hi (by omega_using [])⟩
  · have e : s₂.gpr r = s.gpr r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact o₂.gpr _ (by decide)
    have e' := h.saved r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact e.trans e'
  · show VK s₂.xmm
    rw [o₂.xmm]; exact h.vk
  · show s₂.xmm .xmm4 = _
    rw [o₂.xmm]; exact h.r2
  · exact (BitVec.add_zero _).symm
  · exact (BitVec.add_zero _).symm
  · show s₂.gpr .eax = _
    rw [eax₂]; exact (BitVec.add_zero _).symm
  · exact (BitVec.add_zero _).symm
  · show (s₂.mem.writeW (argAddr s₀ 3) (hP s₀ + 1024)).readW _ 16 = _
    rw [Mem.readW_writeW_sep (Region.Disjoint.sep hp.s_a (Offset.contains_base _ (by omega_using [hj])
      (by omega_using [hj])) (hp.arg_in (by decide))) (by decide)]
    exact tbl_words (fun k hk => montGammas_lt hk) c₂ j hj
  · exact Mem.readW_writeW_self32 _ _ _

theorem pub_esp {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : Pub s₀ s₀') :
    (B0 s₀).gpr .esp = (B0 s₀').gpr .esp := by
  rw [B0_esp hp, B0_esp hp', hq.1]

theorem body_of {h₁ h₂ h₃ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block mulConsts) h₁).isSome = true)
    (t₂ : (VG.X86.sseTaint.check (τr [.esp, .eax]) (.block mulTable) h₂).isSome = true)
    (t₃ : (VG.X86.sseTaint.check (τr [.esp, .eax, .ecx, .edx, .ebx]) (.block (mulCore ++ mulEnd)) h₃).isSome = true) :
    Piece Pre Pub (fun s₀ s => s = B0 s₀) (fun s₀ s => MI s₀ 32 s)
      (.seq (.block mulConsts) (.seq (.block mulTable) (.loop (.block (mulCore ++ mulEnd)) .ne))) := by
  refine Piece.seq (B := fun s₀ s => S1 s₀ s)
    (sse [.esp] (fun s₀ s hp e => e ▸ consts_wp hp) (fun s₀ s₀' s s' hp hp' hq e e' r hr => ?_) t₁)
    (Piece.seq (B := fun s₀ s => MI s₀ 0 s)
      (sse [.esp, .eax] (fun s₀ s hp h => table_wp hp h) (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₂)
      (Piece.loop (fun k s₀ s => MI s₀ k s) (by decide) fun k hk =>
        sse [.esp, .eax, .ecx, .edx, .ebx] (fun s₀ s hp h => mstep hp hk h)
          (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₃))
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', pub_esp hp hp' hq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, pub_esp hp hp' hq]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2.2.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h.esp, h'.esp, pub_esp hp hp' hq]
    · rw [h.eax, h'.eax, fP, fP, hq.2.2.1]
    · rw [h.ecx, h'.ecx, gP, gP, hq.2.2.2.1]
    · rw [h.edx, h'.edx, sP, sP, hq.2.2.2.2]
    · rw [h.ebx, h'.ebx, hP, hP, hq.2.1]

theorem body_piece : Piece Pre Pub (fun s₀ s => s = B0 s₀) (fun s₀ s => MI s₀ 32 s)
    (.seq (.block mulConsts) (.seq (.block mulTable) (.loop (.block (mulCore ++ mulEnd)) .ne))) :=
  body_of (by taint_decide) (by taint_decide) (by taint_decide)

/-- What the function leaves: the coefficients of the product at `h`. -/
def FinOk (s₀ : State) (s : State) : Prop :=
  ∀ i < 256, (coeffAt s.mem (hA s₀) i).toNat = ((multiplyNTTs (Fp s₀) (Gp s₀))[i]!).val

theorem slot_mcdt (s₀ : State) (h : 16 ≤ (E0 s₀).toNat) :
    (mcdtR s₀).Disjoint (bR s₀) ∧ (retR s₀).Disjoint (bR s₀) := by
  have := h
  refine ⟨?_, ?_⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    have := (E0 s₀).isLt
    bv_omega

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => McdtPost (FinOk s₀) s₀ s')
    Impl.MlKem.X86.multiplyNTTs := by
  refine Piece.mcdt (fun s₀ => bR s₀ :: W s₀) (NoSp.of_all (by lit_decide)) (fun _ hp => sp12 hp)
    (fun s₀ hp r hr => ?_) (fun _ _ _ _ hq => hq.1) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact slot_mcdt s₀ hp.sp
    · exact ⟨mcdt_disj hp hp.stk_h, hp.ret_h⟩
    · exact ⟨mcdt_disj hp hp.stk_s, hp.ret_s⟩
    · exact ⟨mcdt_disj hp hp.stk_a, hp.ret_a⟩
  refine Piece.frame (by decide) (by decide) (by decide) (NoSp.of_all (by lit_decide)) (fun s₀ s hp e => ?_)
    (fun s₀ s₀' s s' _ _ hq e e' => by rw [e, e', M0_esp, M0_esp, hq.1]) (fun s₀ => E0 s₀ - 12)
    (fun s₀ s _ e => by rw [e, M0_esp])
    (body_piece.mono (fun s₀ s _ ⟨s₁, e₁, e⟩ => by rw [e, e₁]) fun s₀ s₂ hp h m u fl => ?_)
  · rw [e, M0_esp]; have := hp.sp; simp only [List.length_cons, List.length_nil]; bv_omega
  · have slot : s₂.mem.readW ((s₂.gpr .esp).setWidth 64) 32 = s₀.gpr .ebx := by
      have hw := pushed_word (rs := [.ebx]) (s := M0 s₀) (by decide) (by
        rw [M0_esp]; have := hp.sp; simp only [List.length_cons, List.length_nil]; bv_omega) (i := 0) (by decide)
      rw [Nat.mul_zero, BitVec.add_zero] at hw
      rw [h.esp, h.frame.readW (r := bR s₀) (by
          rw [B0_esp hp]; simp only [Region.Contains]; have := hp.sp; have := (E0 s₀).isLt; bv_omega)
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact slot_disj hp hp.stk_h
          · exact slot_disj hp hp.stk_s
          · exact slot_disj hp hp.stk_a) (by decide)]
      exact hw
    refine ⟨⟨?_, ?_, ?_, ?_, h.mcdt, fun r hr => ?_⟩, fun i hi => ?_⟩
    · exact ((M0_B0 hp).mono (by simp)).trans ((h.frame.mono (by simp)).trans (fl.mono (by simp)))
    · show s₂.gpr .esp + 4 = _
      rw [h.esp, pushed_esp]
      exact BitVec.sub_add_cancel _ _
    · show s₂.rd = _
      rw [h.rd, pushed_rd]
    · show s₂.wr.tail = _
      rw [h.wr]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact slot
      · exact h.saved _ (by simp)
      · exact h.saved _ (by simp)
      · exact h.saved _ (by simp)
    · show (m.readW (coeffAddr (hA s₀) i) 32).toNat = _
      rw [fl.readW (r := polyRegion (hA s₀)) (coeff_contains _ (by rw [n_eq]; exact hi))
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact (slot_disj hp hp.stk_h).symm) (by decide)]
      exact h.out i (by omega_using [hi])

/-- Memory with the arguments `0`, `0x400`, `0x800` and `0xc00` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 4 else if a = 0x500d then 8 else if a = 0x5011 then 0xc else 0

theorem verified : Verified X86.target Impl.MlKem.X86.multiplyNTTs (mulContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := Pre.of h₀
    refine polyIs_frame hm (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (mcdt_disj hp hp.stk_h).symm) ?_
    exact polyIs_of_toNat fun i hi => hinv i hi
  · let st := satState satMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0xc00, 1024⟩, ⟨0x5004, 16⟩]
    obtain a0 : arg st 0 = 0 := by decide
    obtain a1 : arg st 1 = 0x400 := by decide
    obtain a2 : arg st 2 = 0x800 := by decide
    obtain a3 : arg st 3 = 0xc00 := by decide
    obtain e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, by decide, by decide, by decide, by decide, reduced_below (fun a ha => ?_) 0x400 (by decide),
      reduced_below (fun a ha => ?_) 0x800 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | (show satMem a = 0
         simp only [satMem]
         rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha]),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha]),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha])])

end VG.Proof.MlKem.X86.Mul
