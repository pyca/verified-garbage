module

import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
public import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
public import VerifiedGarbage.Impl.MlKem.X86_64.Sample4
public import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the vector sampling

Four iterations of `SampleNTT`'s loop, from fewer than 249 coefficients,
append the candidates less than `q` of their 12 bytes (`sampleAfter_four`).
The code computes the eight candidates in the doublewords of `ymm0`
(`cand_dword`) and their mask in `eax` (`vcand_ok`), and stores the
doublewords that the table's entry for the mask selects (`vput_ok`): those of
the candidates less than `q`, in order (`setBits_bsum`).
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- Candidate `k < 8` of the four chunks of `out` from byte `p`: `d₁` (`k`
even) or `d₂` (`k` odd) of chunk `k / 2`. -/
def cand4 (out : Nat → Byte) (p k : Nat) : Nat :=
  if k % 2 = 0 then (out (p + 3 * (k / 2))).toNat + 256 * ((out (p + 3 * (k / 2) + 1)).toNat % 16)
  else (out (p + 3 * (k / 2) + 1)).toNat / 16 + 16 * (out (p + 3 * (k / 2) + 2)).toNat

/-- The candidates less than `q` of the four chunks from byte `p`, as coefficients. -/
def acc4 (out : Nat → Byte) (p : Nat) : List Zq :=
  ((List.range 8).filter fun k => decide (cand4 out p k < q)).map fun k => ofNat (cand4 out p k)

/-- The coefficients a chunk adds, if there is room for two. -/
def pair (c₀ c₁ c₂ : Byte) : List Zq :=
  (if c₀.toNat + 256 * (c₁.toNat % 16) < q then [ofNat (c₀.toNat + 256 * (c₁.toNat % 16))] else []) ++
    (if c₁.toNat / 16 + 16 * c₂.toNat < q then [ofNat (c₁.toNat / 16 + 16 * c₂.toNat)] else [])

theorem pair_length (c₀ c₁ c₂ : Byte) : (pair c₀ c₁ c₂).length ≤ 2 := by
  unfold pair; split <;> split <;> simp

theorem sampleStepCap_room {a : List Zq} (h : a.length + 2 ≤ n) (c₀ c₁ c₂ : Byte) :
    sampleStepCap a c₀ c₁ c₂ = a ++ pair c₀ c₁ c₂ := by
  unfold sampleStepCap sampleStep pair
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by bdd_omega))]
  dsimp only
  split <;> split <;> simp_all <;> omega

theorem fm2 {α : Type} (p : Nat → Bool) (f : Nat → α) (k : Nat) :
    ([k, k + 1].filter p).map f = (if p k then [f k] else []) ++ (if p (k + 1) then [f (k + 1)] else []) := by
  simp only [List.filter_cons, List.filter_nil]
  cases p k <;> cases p (k + 1) <;> rfl

theorem acc4_eq (out : Nat → Byte) (p : Nat) : acc4 out p =
    pair (out p) (out (p + 1)) (out (p + 2)) ++ pair (out (p + 3)) (out (p + 4)) (out (p + 5)) ++
      pair (out (p + 6)) (out (p + 7)) (out (p + 8)) ++ pair (out (p + 9)) (out (p + 10)) (out (p + 11)) := by
  rw [acc4, show List.range 8 = [0, 0 + 1] ++ [2, 2 + 1] ++ [4, 4 + 1] ++ [6, 6 + 1] from rfl]
  simp only [List.filter_append, List.map_append, fm2, decide_eq_true_eq, pair, cand4]
  simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul, ite_true, Nat.add_zero, Nat.add_assoc,
    Nat.zero_add, show (1 % 2 = 0) = False from by decide, ite_false, List.append_assoc, decide_eq_true_eq]

theorem sampleAfter_four {a : List Zq} {out : Nat → Byte} {t : Nat}
    (h : (sampleAfter a out t).length + 8 ≤ n) :
    sampleAfter a out (t + 4) = sampleAfter a out t ++ acc4 out (3 * t) := by
  have p0 := pair_length (out (3 * t)) (out (3 * t + 1)) (out (3 * t + 2))
  have p1 := pair_length (out (3 * (t + 1))) (out (3 * (t + 1) + 1)) (out (3 * (t + 1) + 2))
  have p2 := pair_length (out (3 * (t + 2))) (out (3 * (t + 2) + 1)) (out (3 * (t + 2) + 2))
  rw [sampleAfter_succ, sampleAfter_succ, sampleAfter_succ, sampleAfter_succ,
    sampleStepCap_room (a := sampleAfter a out t) (by bdd_omega),
    sampleStepCap_room (a := sampleAfter a out t ++ _) (by simp only [List.length_append]; omega),
    sampleStepCap_room (a := sampleAfter a out t ++ _ ++ _) (by simp only [List.length_append]; omega),
    sampleStepCap_room (a := sampleAfter a out t ++ _ ++ _ ++ _) (by simp only [List.length_append]; omega),
    acc4_eq]
  simp only [List.append_assoc, show 3 * (t + 1) = 3 * t + 3 by bdd_omega, show 3 * (t + 2) = 3 * t + 6 by bdd_omega,
    show 3 * (t + 3) = 3 * t + 9 by bdd_omega, Nat.add_assoc, Nat.reduceAdd]

end VG.Proof.MlKem

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Spec.MlKem

/-- The coefficients `L ++ A` are stored after a write of eight coefficients
`V` at `a[|L|]`, whose first `|A|` are `A`. -/
theorem stored_write8 {w16 : Bool} {m : Mem} {aP : Addr} {L A : List Zq} (h : Stored w16 m aP L)
    (hl : L.length + 8 ≤ 256) (hA : A.length ≤ 8) (V : BitVec (8 * cw w16))
    (hV : ∀ i < A.length, (V.extractLsb' (cw w16 * i) (cw w16)).toNat = (A.getD i 0).val) :
    Stored w16 (m.writeW (cAddr w16 aP L.length) V) aP (L ++ A) := by
  intro k hk
  rw [List.length_append] at hk
  rw [coeffAtW_eq]
  have hb := cw_bytes w16
  have e8 : cw w16 = 8 * (cw w16 / 8) := by cases w16 <;> rfl
  by_cases hkL : k < L.length
  · have := readW_writeW_off m aP V (d := cw w16 / 8 * k) (e := cw w16 / 8 * L.length) (n := cw w16 / 8)
      (by cases w16 <;> simp only [cw, Bool.false_eq_true, ↓reduceIte] <;> bdd_omega)
      (by cases w16 <;> simp only [cw, Bool.false_eq_true, ↓reduceIte] <;> bdd_omega)
      (by cases w16 <;> simp only [cw, Bool.false_eq_true, ↓reduceIte] <;> bdd_omega)
    rw [← e8] at this
    rw [this, show (L ++ A).getD k 0 = L.getD k 0 by simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hkL]]
    exact h k hkL
  · have e := readW_writeW_inside m (cAddr w16 aP L.length) V (k := cw w16 / 8 * (k - L.length)) (n := cw w16 / 8)
      (by cases w16 <;> simp only [cw, Bool.false_eq_true, ↓reduceIte] <;> bdd_omega) (by cases w16 <;> decide)
    rw [← e8, cAddr, Offset.add_add, show cw w16 / 8 * L.length + cw w16 / 8 * (k - L.length) = cw w16 / 8 * k by
      rw [← Nat.mul_add]; congr 1; bdd_omega] at e
    rw [e, show 8 * (cw w16 / 8 * (k - L.length)) = cw w16 * (k - L.length) by rw [← Nat.mul_assoc, ← e8],
      hV _ (by bdd_omega), show (L ++ A).getD k 0 = A.getD (k - L.length) 0 by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show L.length ≤ k by bdd_omega)]]

end VG.Proof.MlKem.X86_64

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64
open VG.Impl.MlKem.X86_64.Sample4 (vcand vput vstore tabE aV setBits tblWords tblName oNum)
open VG.Proof.Sha3.X86_64 (WP.cons Upd)

def shuf0 : BitVec 128 := 0x80800504808004038080020180800100#128
def shuf1 : BitVec 128 := 0x80800b0a80800a098080080780800706#128
def shV : BitVec 128 := 0x00000004000000000000000400000000#128
def maskV : BitVec 128 := 0x00000fff00000fff00000fff00000fff#128

/-- The first byte of candidate `k`'s pair: `3 (k / 2) + k % 2`. -/
abbrev cb (k : Nat) : Nat := 3 * (k / 2) + k % 2

/-- Candidate `k` of the bytes `b`. -/
def candN (b : Nat → Nat) (k : Nat) : Nat :=
  if k % 2 = 0 then b (cb k) + 256 * (b (cb k + 1) % 16) else b (cb k) / 16 + 16 * b (cb k + 1)

theorem gb {f : Nat → BitVec 8} {a b c d : Nat} (h1 : a = c) (h2 : b = d) :
    (f a).getLsbD b = (f c).getLsbD d := by subst h1 h2; rfl

theorem toNat_dword_ofBytes (f : Nat → BitVec 8) {j : Nat} (hj : j < 4) :
    (dword (ofBytes f) j).toNat = (f (4 * j)).toNat + 256 * (f (4 * j + 1)).toNat +
      65536 * (f (4 * j + 2)).toNat + 16777216 * (f (4 * j + 3)).toNat := by
  have e : dword (ofBytes f) j = f (4 * j + 3) ++ f (4 * j + 2) ++ f (4 * j + 1) ++ f (4 * j) := by
    apply BitVec.eq_of_getLsbD_eq; intro m hm
    rw [getLsbD_dword_ofBytes _ hj hm]
    simp only [BitVec.getLsbD_append]
    have h8 := Nat.mod_lt m (show 8 > 0 by decide)
    by_cases a : m < 8
    · simp only [a, ite_true]; exact gb (by bdd_omega) (by bdd_omega)
    by_cases b : m - 8 < 8
    · simp only [a, b, ite_true, ite_false]; exact gb (by bdd_omega) (by bdd_omega)
    by_cases c : m - 8 - 8 < 8
    · simp only [a, b, c, ite_true, ite_false]; exact gb (by bdd_omega) (by bdd_omega)
    · simp only [a, b, c, ite_false]; exact gb (by bdd_omega) (by bdd_omega)
  rw [e]
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j + 2)).isLt, ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j + 1)).isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j)).isLt]
  simp only [Nat.shiftLeft_eq]
  have := (f (4 * j)).isLt; have := (f (4 * j + 1)).isLt; have := (f (4 * j + 2)).isLt
  have := (f (4 * j + 3)).isLt
  omega

theorem pshufb_shuf0 (a : BitVec 128) : XBinOp.eval .pshufb a shuf0 =
    ofBytes fun i => if i % 4 < 2 then byte a (cb (i / 4) + i % 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_shuf1 (a : BitVec 128) : XBinOp.eval .pshufb a shuf1 =
    ofBytes fun i => if i % 4 < 2 then byte a (6 + cb (i / 4) + i % 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

/-- The `vpshufb` mask of lane `l`. -/
abbrev shuf (l : Nat) : BitVec 128 := if l = 0 then shuf0 else shuf1

/-- The candidates in lane `l` of `ymm0`, from `a`, the 16 bytes in both. -/
abbrev candV (a : BitVec 128) (l : Nat) : BitVec 128 :=
  XBinOp.eval .pand (VVarOp.eval .vpsrlvd (XBinOp.eval .pshufb a (shuf l)) shV) maskV

theorem toNat_and_fff (x : BitVec 32) : (x &&& 0xfff#32).toNat = x.toNat % 4096 := by
  rw [BitVec.toNat_and, show (0xfff#32).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The value of an even candidate from its two bytes. -/
theorem cand_lo {x y : Nat} (hx : x < 256) (_hy : y < 256) :
    (x + 256 * y) / 2 ^ 0 % 4096 = (x + 256 * (y % 16)) % 2 ^ 32 := by
  omega

/-- The value of an odd candidate from its two bytes. -/
theorem cand_hi {x y : Nat} (hx : x < 256) (hy : y < 256) :
    (x + 256 * y) / 2 ^ 4 % 4096 = (x / 16 + 16 * y) % 2 ^ 32 := by
  omega

theorem cand_dword (a : BitVec 128) {l j : Nat} (hl : l < 2) (hj : j < 4) :
    dword (candV a l) j = BitVec.ofNat 32 (candN (fun i => (byte a i).toNat) (4 * l + j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [dword_pand, (show ∀ i < 4, dword maskV i = 0xfff#32 by decide) j hj, toNat_and_fff]
  have hb : ∀ i, (byte a i).toNat < 256 := fun i => (byte a i).isLt
  rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;>
  simp only [shuf, VVarOp.eval, pshufb_shuf0, pshufb_shuf1, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, ↓reduceIte, show (dword shV 0).toNat = 0 from rfl, show (dword shV 1).toNat = 4 from rfl,
    show (dword shV 2).toNat = 0 from rfl, show (dword shV 3).toNat = 4 from rfl, Nat.reduceLT,
    BitVec.toNat_ushiftRight,
    toNat_dword_ofBytes _ (show 0 < 4 by decide), toNat_dword_ofBytes _ (show 1 < 4 by decide),
    toNat_dword_ofBytes _ (show 2 < 4 by decide), toNat_dword_ofBytes _ (show 3 < 4 by decide),
    candN, cb, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceEqDiff, Nat.add_zero] <;>
  first | exact cand_lo (hb _) (hb _) | exact cand_hi (hb _) (hb _)

def qV4 : BitVec 128 := 0x00000d0100000d0100000d0100000d01#128
def sign0 : BitVec 128 := 0x0f0b0703808080808080808080808080#128
def sign1 : BitVec 128 := 0x8080808080808080808080800f0b0703#128

theorem pshufb_sign0 (a : BitVec 128) : XBinOp.eval .pshufb a sign0 =
    ofBytes fun i => if 12 ≤ i then byte a (4 * (i - 12) + 3) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_sign1 (a : BitVec 128) : XBinOp.eval .pshufb a sign1 =
    ofBytes fun i => if i < 4 then byte a (4 * i + 3) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

/-- `∑ i < n, f i · 2ⁱ`. -/
def bsum (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => bsum f n + (f n).toNat * 2 ^ n

theorem bsum_lt (f : Nat → Bool) : ∀ n, bsum f n < 2 ^ n
  | 0 => by simp [bsum]
  | n + 1 => by
    have := bsum_lt f n
    simp only [bsum, Nat.pow_succ]
    cases f n <;> simp <;> omega

theorem byteMask_eq (x : BitVec 256) {n : Nat} (hn : n ≤ 64) :
    byteMask x n = BitVec.ofNat 64 (bsum (fun i => x.getLsbD (8 * i + 7)) n) := by
  unfold byteMask
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih (by bdd_omega), List.foldl_cons, List.foldl_nil, bsum]
    have hl := bsum_lt (fun i => x.getLsbD (8 * i + 7)) n
    have h1 : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by bdd_omega)
    cases x.getLsbD (8 * n + 7)
    · simp
    · simp only [ite_true, Bool.toNat_true, Nat.one_mul]
      apply BitVec.eq_of_toNat_eq
      have h2 : 2 ^ n ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by bdd_omega)
      have e := Nat.two_pow_add_eq_or_of_lt hl 1
      rw [Nat.mul_one] at e
      rw [BitVec.toNat_or, BitVec.toNat_twoPow, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt (by bdd_omega), Nat.mod_eq_of_lt (by bdd_omega), Nat.or_comm, ← e, Nat.add_comm]

theorem bsum_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = g i) : bsum f n = bsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bsum, bsum, ih fun i hi => h i (by bdd_omega), h n (by bdd_omega)]

theorem itT {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem itF {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

theorem byte3_bit7 (X : BitVec 128) (j : Nat) : (byte X (4 * j + 3)).getLsbD 7 = (dword X j).getLsbD 31 := by
  rw [byte, BitVec.getLsbD_extractLsb', getLsbD_dword]
  simp only [show 7 < 8 by decide, show 31 < 32 by decide, decide_true, Bool.true_and]
  exact congrArg _ (by bdd_omega)

/-- Bit 7 of byte `i` of the two lanes after the `vpshufb` with the sign masks. -/
theorem sign_bit (X0 X1 : BitVec 128) {i : Nat} (hi : i < 32) :
    (XBinOp.eval .pshufb X1 sign1 ++ XBinOp.eval .pshufb X0 sign0).getLsbD (8 * i + 7) =
      if 12 ≤ i ∧ i < 16 then (dword X0 (i - 12)).getLsbD 31
      else if 16 ≤ i ∧ i < 20 then (dword X1 (i - 16)).getLsbD 31 else false := by
  rw [BitVec.getLsbD_append, pshufb_sign0, pshufb_sign1]
  by_cases h : i < 16
  · have h7 : 8 * i + 7 < 128 := by bdd_omega
    rw [itT h7, getLsbD_ofBytes _ h (by decide)]
    by_cases h' : 12 ≤ i
    · rw [itT h', itT (show 12 ≤ i ∧ i < 16 from ⟨h', h⟩), byte3_bit7]
    · rw [itF h', itF (show ¬ (12 ≤ i ∧ i < 16) by bdd_omega), itF (show ¬ (16 ≤ i ∧ i < 20) by bdd_omega)]; rfl
  · have h7 : ¬ 8 * i + 7 < 128 := by bdd_omega
    have hk : i - 16 < 16 := by bdd_omega
    rw [itF h7, show 8 * i + 7 - 128 = 8 * (i - 16) + 7 by bdd_omega, getLsbD_ofBytes _ hk (by decide),
      itF (show ¬ (12 ≤ i ∧ i < 16) by bdd_omega)]
    by_cases h' : i < 20
    · rw [itT (show i - 16 < 4 by bdd_omega), itT (show 16 ≤ i ∧ i < 20 from ⟨by bdd_omega, h'⟩), byte3_bit7]
    · rw [itF (show ¬ i - 16 < 4 by bdd_omega), itF (show ¬ (16 ≤ i ∧ i < 20) by bdd_omega)]; rfl

theorem bsum_add (f : Nat → Bool) (n : Nat) :
    ∀ m, bsum f (n + m) = bsum f n + 2 ^ n * bsum (fun i => f (n + i)) m
  | 0 => by rw [Nat.add_zero, bsum, Nat.mul_zero, Nat.add_zero]
  | m + 1 => by
    rw [← Nat.add_assoc, bsum, bsum_add f n m, bsum, Nat.pow_add, Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm]

theorem bsum_false {f : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = false) : bsum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bsum, ih fun i hi => h i (by bdd_omega), h n (by bdd_omega), Bool.toNat_false, Nat.zero_mul]

theorem mask_bsum (X0 X1 : BitVec 128) :
    bsum (fun i => (XBinOp.eval .pshufb X1 sign1 ++ XBinOp.eval .pshufb X0 sign0).getLsbD (8 * i + 7)) 32 =
      4096 * bsum (fun k => if k < 4 then (dword X0 k).getLsbD 31 else (dword X1 (k - 4)).getLsbD 31) 8 := by
  rw [bsum_congr fun i hi => sign_bit X0 X1 hi, show ∀ g, bsum g 32 = bsum g (12 + 8 + 12) from fun _ => rfl,
    bsum_add, bsum_add]
  have h0 : ∀ i < 12, (if 12 ≤ i ∧ i < 16 then (dword X0 (i - 12)).getLsbD 31
      else if 16 ≤ i ∧ i < 20 then (dword X1 (i - 16)).getLsbD 31 else false) = false := fun i hi => by
    rw [itF (show ¬ (12 ≤ i ∧ i < 16) by bdd_omega), itF (show ¬ (16 ≤ i ∧ i < 20) by bdd_omega)]
  have h2 : ∀ i < 12, (if 12 ≤ 12 + 8 + i ∧ 12 + 8 + i < 16 then (dword X0 (12 + 8 + i - 12)).getLsbD 31
      else if 16 ≤ 12 + 8 + i ∧ 12 + 8 + i < 20 then (dword X1 (12 + 8 + i - 16)).getLsbD 31 else false) = false :=
    fun i _ => by
      rw [itF (show ¬ (12 ≤ 12 + 8 + i ∧ 12 + 8 + i < 16) by bdd_omega),
        itF (show ¬ (16 ≤ 12 + 8 + i ∧ 12 + 8 + i < 20) by bdd_omega)]
  have h1 : ∀ k < 8, (if 12 ≤ 12 + k ∧ 12 + k < 16 then (dword X0 (12 + k - 12)).getLsbD 31
      else if 16 ≤ 12 + k ∧ 12 + k < 20 then (dword X1 (12 + k - 16)).getLsbD 31 else false) =
      if k < 4 then (dword X0 k).getLsbD 31 else (dword X1 (k - 4)).getLsbD 31 := fun k _ => by
    by_cases h : k < 4
    · rw [itT (show 12 ≤ 12 + k ∧ 12 + k < 16 by bdd_omega), itT h, show 12 + k - 12 = k by bdd_omega]
    · rw [itF (show ¬ (12 ≤ 12 + k ∧ 12 + k < 16) by bdd_omega), itT (show 16 ≤ 12 + k ∧ 12 + k < 20 by bdd_omega), itF h,
        show 12 + k - 16 = k - 4 by bdd_omega]
  rw [bsum_false h0, bsum_false h2, bsum_congr h1, Nat.zero_add, Nat.mul_zero, Nat.add_zero]

theorem dword_qV4 {j : Nat} (hj : j < 4) : dword qV4 j = 3329#32 := by
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

/-- The sign of `c - q`: whether `c < q`. -/
theorem sign_sub_q {c : Nat} (hc : c < 4096) : (BitVec.ofNat 32 c - 3329#32).getLsbD 31 = decide (c < 3329) := by
  rw [BitVec.getLsbD, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  exact decide_eq_decide.mpr (by bdd_omega)

/-- Word `i` of `x ++ y`, for a word `y`. -/
theorem ext_last {w : Nat} (x : BitVec w) (y : BitVec 32) (i : Nat) :
    (x ++ y).extractLsb' (32 * i) 32 = if i = 0 then y else x.extractLsb' (32 * (i - 1)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases h : i = 0
  · rw [itT h, itT (show 32 * i + j < 32 by bdd_omega)]; exact congrArg _ (by bdd_omega)
  · rw [itF h, itF (show ¬ 32 * i + j < 32 by bdd_omega), BitVec.getLsbD_extractLsb', decide_eq_true hj,
      Bool.true_and]
    exact congrArg _ (by bdd_omega)

theorem ext_last0 {w : Nat} (x : BitVec w) (y : BitVec 32) : (x ++ y).extractLsb' 0 32 = y := by
  have h := ext_last x y 0
  rwa [Nat.mul_zero, itT rfl] at h

theorem ext_app8 (a : Nat → BitVec 32) {i : Nat} (hi : i < 8) :
    (a 7 ++ a 6 ++ a 5 ++ a 4 ++ a 3 ++ a 2 ++ a 1 ++ a 0).extractLsb' (32 * i) 32 = a i := by
  rcases (by bdd_omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [ext_last, ext_last0, Nat.reduceEqDiff, Nat.reduceSub, ite_false, Nat.mul_zero,
    BitVec.extractLsb'_eq_self]

theorem dw8_permDwords (idx x : BitVec 256) {i : Nat} (hi : i < 8) :
    (permDwords idx x).extractLsb' (32 * i) 32 = x.extractLsb' (32 * (idx.extractLsb' (32 * i) 3).toNat) 32 :=
  ext_app8 (fun k => x.extractLsb' (32 * (idx.extractLsb' (32 * k) 3).toNat) 32) hi

def nib0 : BitVec 128 := 0x0000000c000000080000000400000000#128
def nib1 : BitVec 128 := 0x0000001c000000180000001400000010#128

/-- The indices: `E` shifted right by `4 i` in doubleword `i`. -/
abbrev idxV (E : BitVec 32) : BitVec 256 :=
  VVarOp.eval .vpsrlvd (ofDwords E E E E) nib1 ++ VVarOp.eval .vpsrlvd (ofDwords E E E E) nib0

theorem ext_app2 (h l : BitVec 128) {i : Nat} (hi : i < 8) :
    (h ++ l).extractLsb' (32 * i) 32 = dword (if i < 4 then l else h) (i % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', getLsbD_dword, hj, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases h4 : i < 4
  · rw [itT (show 32 * i + j < 128 by bdd_omega), itT h4]; exact congrArg _ (by bdd_omega)
  · rw [itF (show ¬ 32 * i + j < 128 by bdd_omega), itF h4]; exact congrArg _ (by bdd_omega)

theorem nib_dword {l j : Nat} (hl : l < 2) (hj : j < 4) :
    (dword (if l = 0 then nib0 else nib1) j).toNat = 4 * (4 * l + j) := by
  rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

theorem idx_toNat (E : BitVec 32) {i : Nat} (hi : i < 8) :
    ((idxV E).extractLsb' (32 * i) 3).toNat = E.toNat / 16 ^ i % 8 := by
  rw [show (idxV E).extractLsb' (32 * i) 3 = ((idxV E).extractLsb' (32 * i) 32).extractLsb' 0 3 by
      rw [extract_extract _ _ _ _ _ (by bdd_omega), Nat.add_zero], ext_app2 _ _ hi]
  have hn : ∀ l < 2, ∀ j < 4, dword (VVarOp.eval .vpsrlvd (ofDwords E E E E) (if l = 0 then nib0 else nib1)) j =
      E >>> (4 * (4 * l + j)) := by
    intro l hl j hj
    have e := nib_dword hl hj
    rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp only [VVarOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, e,
      itT (show 4 * (4 * l + 0) < 32 by bdd_omega), itT (show 4 * (4 * l + 1) < 32 by bdd_omega),
      itT (show 4 * (4 * l + 2) < 32 by bdd_omega), itT (show 4 * (4 * l + 3) < 32 by bdd_omega)]
  have e : dword (if i < 4 then VVarOp.eval .vpsrlvd (ofDwords E E E E) nib0
      else VVarOp.eval .vpsrlvd (ofDwords E E E E) nib1) (i % 4) = E >>> (4 * i) := by
    by_cases h4 : i < 4
    · rw [itT h4]; have := hn 0 (by decide) (i % 4) (by bdd_omega); rw [itT rfl] at this
      rw [this]; congr 1; omega
    · rw [itF h4]; have := hn 1 (by decide) (i % 4) (by bdd_omega); rw [itF (by decide)] at this
      rw [this]; congr 1; omega
  rw [e, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

/-- `s'` is `s` with the two lanes of `d` set to `v 0` and `v 1` (flags aside). -/
structure LUpd (s s' : State) (d : XReg) (v : Nat → BitVec 128) : Prop where
  val : ∀ l < 2, s'.lane d l = v l
  other : ∀ r, r ≠ d → ∀ l < 2, s'.lane r l = s.lane r l
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

theorem LUpd.setV256 (s : State) (d : XReg) (lo hi : BitVec 128) :
    LUpd s (s.setV .l256 d lo hi) d fun l => if l = 0 then lo else hi :=
  ⟨fun l _ => by rw [State.lane_setV256, ite_eq_left rfl], fun r hr l _ => by rw [State.lane_setV256, ite_eq_right hr],
    rfl, rfl, rfl, rfl, rfl⟩

theorem LUpd.setV128 (s : State) (d : XReg) (lo hi : BitVec 128) :
    LUpd s (s.setV .l128 d lo hi) d fun l => if l = 0 then lo else 0 :=
  ⟨fun l _ => by rw [State.lane_setV128, ite_eq_left rfl], fun r hr l _ => by rw [State.lane_setV128, ite_eq_right hr],
    rfl, rfl, rfl, rfl, rfl⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vbin {op : VBinOp} {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => op.sse.eval (s.lane a l) (s.lane b l)) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vbin op .l256 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (by
    have h := LUpd.setV256 s d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1))
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vvar {op : VVarOp} {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => op.eval (s.lane a l) (s.lane b l)) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vvar op .l256 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (op.eval (s.lane a 0) (s.lane b 0)) (op.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (by
    have h := LUpd.setV256 s d (op.eval (s.lane a 0) (s.lane b 0)) (op.eval (s.lane a 1) (s.lane b 1))
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vpbcastd {d a : XReg}
    (k : ∀ s', LUpd s s' d (fun _ => let v := dword (s.lane a 0) 0; ofDwords v v v v) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpbroadcastd .l256 d a) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (let v := dword (s.xmm a) 0; ofDwords v v v v)
      (let v := dword (s.xmm a) 0; ofDwords v v v v)) rfl (k _ (by
    have h := LUpd.setV256 s d (let v := dword (s.xmm a) 0; ofDwords v v v v)
      (let v := dword (s.xmm a) 0; ofDwords v v v v)
    exact ⟨fun l hl => by rw [h.val l hl]; split <;> rfl, h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vpermd {d i a : XReg}
    (k : ∀ s', LUpd s s' d (fun l => (permDwords (s.ymm i) (s.ymm a)).extractLsb' (128 * l) 128) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpermd d i a) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 0 128)
      ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 128 128)) rfl (k _ (by
    have h := LUpd.setV256 s d ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 0 128)
      ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 128 128)
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vbcast128 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', LUpd s s' d (fun _ => s.mem.readW a 128) → WP isa (.block is) s' Q) :
    WP isa (.block (.vbroadcasti128 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d (s.mem.readW a 128) (s.mem.readW a 128))
    (by simp [exec, ha, State.load128, hin]) (k _ ?_)
  have h := LUpd.setV256 s d (s.mem.readW a 128) (s.mem.readW a 128)
  exact ⟨fun l hl => by rw [h.val l hl]; split <;> rfl, h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩

theorem wp_vld128 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then s.mem.readW a 128 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquLoad .l128 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l128 d (s.mem.readW a 128) 0)
    (by simp [exec, ha, State.load128, hin]) (k _ (LUpd.setV128 s d _ _))

theorem wp_vld256 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 32)
    (k : ∀ s', LUpd s s' d (fun l => (s.mem.readW a 256).extractLsb' (128 * l) 128) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquLoad .l256 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d ((s.mem.readW a 256).extractLsb' 0 128)
    ((s.mem.readW a 256).extractLsb' 128 128)) (by simp [exec, ha, State.load256, hin]) (k _ ?_)
  have h := LUpd.setV256 s d ((s.mem.readW a 256).extractLsb' 0 128) ((s.mem.readW a 256).extractLsb' 128 128)
  exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
    h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩

theorem wp_vst256 {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 32)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.ymm r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l256 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.ymm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store256, ha, hout]

theorem wp_vst128 {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.xmm r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l128 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.xmm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store128, ha, hout]

/-- `wp_vst256`, keeping the statics' addresses. -/
theorem wp_vst256s {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 32)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.ymm r) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l256 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.ymm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl rfl)
  simp [exec, State.store256, ha, hout]

/-- `wp_vst128`, keeping the statics' addresses. -/
theorem wp_vst128s {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.xmm r) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l128 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.xmm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl rfl)
  simp [exec, State.store128, ha, hout]

theorem wp_vbin128 {op : VBinOp} {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then op.sse.eval (s.lane a 0) (s.lane b 0) else 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vbin op .l128 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l128 d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (LUpd.setV128 s d _ _))

theorem wp_vext128 {d r : XReg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then s.lane r 1 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vextracti128 d r 1) :: is)) s Q :=
  WP.cons (s' := s.setV .l128 d (s.lane r 1) 0) rfl (k _ (LUpd.setV128 s d _ _))

/-- `s'` is `s` with register `d` set to `v`, the vector registers as they were (flags aside). -/
structure GUpd (s s' : State) (d : Reg) (v : BitVec 64) : Prop extends Upd s s' d v where
  lane : ∀ x l, s'.lane x l = s.lane x l
  syms : s'.syms = s.syms

theorem GUpd.setReg (s : State) (d : Reg) (v : BitVec 64) : GUpd s (s.setReg d v) d v :=
  ⟨Upd.setReg s d v, fun _ _ => rfl, rfl⟩

theorem GUpd.withFlags (s : State) (cf o zf sf : Option Bool) (d : Reg) (v : BitVec 64) :
    GUpd s ((s.setFlags cf o zf sf).setReg d v) d v :=
  ⟨Upd.withFlags s cf o zf sf d v, fun _ _ => rfl, rfl⟩

theorem wp_vpmovmskb {d : Reg} {r : XReg}
    (k : ∀ s', GUpd s s' d (byteMask (s.ymm r) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.vpmovmskb .l256 d r :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.setReg _ _ _))

theorem wp_shr32 {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 31)
    (k : ∀ s', GUpd s s' d ((((s.gpr d).setWidth 32) >>> n).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift32 .shr d n :: is)) s Q := by
  let a := (s.gpr d).setWidth 32
  refine WP.cons (s' := (s.setFlags (some (a.getLsbD (n - 1))) (if n = 1 then some a.msb else none)
    (some (a >>> n == 0)) (some (a >>> n).msb)).setReg d ((a >>> n).setWidth 64)) ?_
    (k _ (GUpd.withFlags _ _ _ _ _ _ _))
  simp only [exec, execShift32, h₁, h₂, and_self, ite_true, State.setReg32]
  rfl

theorem wp_add32m {d : Reg} {m : MemOp} {a' : Addr} (ha : s.ea m = a') (hin : InRegions (s.rd ++ s.wr) a' 4)
    (k : ∀ s', GUpd s s' d (((s.gpr d).setWidth 32 + s.mem.readW a' 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .add d (.mem m) :: is)) s Q := by
  let a := (s.gpr d).setWidth 32
  let b := s.mem.readW a' 32
  refine WP.cons (s' := (arithFlags s (a + b) (2 ^ 32 ≤ a.toNat + b.toNat) (addOverflow a b (a + b))).setReg d
    ((a + b).setWidth 64)) ?_ (k _ (GUpd.withFlags _ _ _ _ _ _ _))
  simp [exec, execAlu32, readSrc32, State.load32, ha, hin, State.setReg32, a, b]

theorem wp_addi' {d : Reg} {v : BitVec 32}
    (k : ∀ s', GUpd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.withFlags _ _ _ _ _ _ _))

/-- `vmovdquTbl` of words `o` to `o + 3` of the static `name`. -/
theorem wp_vtbl {d : XReg} {m : MemOp} {name : String} {ws : List (BitVec 64)} {o : Nat}
    (hb : s.gpr m.base = s.syms name) (ho : (s.ea m - s.syms name).toNat = 8 * o) (hl : o + 4 ≤ ws.length)
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then ws.getD (o + 1) 0 ++ ws.getD o 0
      else ws.getD (o + 3) 0 ++ ws.getD (o + 2) 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquTbl d m name ws :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d (ws.getD (o + 1) 0 ++ ws.getD o 0) (ws.getD (o + 3) 0 ++ ws.getD (o + 2) 0))
    ?_ (k _ (LUpd.setV256 _ _ _ _))
  have h8 : 8 * o % 8 = 0 := by omega
  have hd : 8 * o / 8 = o := by omega
  simp only [exec, hb, ho, h8, hd, hl, and_self, ite_true, Nat.add_zero]

/-- `add d, QWORD PTR [m]` of word `o` of the static `name` (`aluTbl`). -/
theorem wp_addTbl {d : Reg} {m : MemOp} {name : String} {ws : List (BitVec 64)} {o : Nat}
    (hb : s.gpr m.base = s.syms name) (ho : (s.ea m - s.syms name).toNat = 8 * o) (hl : o < ws.length)
    (k : ∀ s', GUpd s s' d (s.gpr d + ws.getD o 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.aluTbl .add d m name ws :: is)) s Q := by
  let a := s.gpr d
  let b := ws.getD o 0
  refine WP.cons (s' := (arithFlags s (a + b) (2 ^ 64 ≤ a.toNat + b.toNat) (addOverflow a b (a + b))).setReg d
    (a + b)) ?_ (k _ (GUpd.withFlags _ _ _ _ _ _ _))
  have h8 : 8 * o % 8 = 0 := by omega
  have hd : 8 * o / 8 = o := by omega
  simp only [exec, hb, ho, h8, hd, hl, and_self, ite_true, execAluW, a, b]

end


/-! ## The candidates and their mask -/

abbrev sgn (l : Nat) : BitVec 128 := if l = 0 then sign0 else sign1
abbrev nib (l : Nat) : BitVec 128 := if l = 0 then nib0 else nib1

/-- The constants of the vector code in `ymm8` to `ymm13`. -/
structure VC (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = shuf l
  c9 : ∀ l < 2, s.lane .xmm9 l = shV
  c10 : ∀ l < 2, s.lane .xmm10 l = maskV
  c11 : ∀ l < 2, s.lane .xmm11 l = qV4
  c12 : ∀ l < 2, s.lane .xmm12 l = sgn l
  c13 : ∀ l < 2, s.lane .xmm13 l = nib l

theorem VC.lupd {s s' : State} (h : VC s) {d : XReg} {v : Nat → BitVec 128} (hu : LUpd s s' d v)
    (hd : d = .xmm0 ∨ d = .xmm1) : VC s' := by
  have e : ∀ r, r = XReg.xmm8 ∨ r = .xmm9 ∨ r = .xmm10 ∨ r = .xmm11 ∨ r = .xmm12 ∨ r = .xmm13 →
      ∀ l < 2, s'.lane r l = s.lane r l := fun r hr l hl => hu.other r (by
    rcases hd with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) l hl
  exact ⟨fun l hl => by rw [e _ (by simp) l hl, h.c8 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c9 l hl],
    fun l hl => by rw [e _ (by simp) l hl, h.c10 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c11 l hl],
    fun l hl => by rw [e _ (by simp) l hl, h.c12 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c13 l hl]⟩

theorem VC.gupd {s s' : State} (h : VC s) {d : Reg} {v : BitVec 64} (hu : GUpd s s' d v) : VC s' :=
  ⟨fun l hl => by rw [hu.lane, h.c8 l hl], fun l hl => by rw [hu.lane, h.c9 l hl],
    fun l hl => by rw [hu.lane, h.c10 l hl], fun l hl => by rw [hu.lane, h.c11 l hl],
    fun l hl => by rw [hu.lane, h.c12 l hl], fun l hl => by rw [hu.lane, h.c13 l hl]⟩

theorem candN_lt (b : Nat → Nat) (hb : ∀ i, b i < 256) (k : Nat) : candN b k < 4096 := by
  unfold candN; have := hb (cb k); have := hb (cb k + 1); split <;> omega

/-- The mask of the candidates less than `q`. -/
abbrev maskN (b : Nat → Nat) : Nat := bsum (fun k => decide (candN b k < 3329)) 8

theorem vcand_ok {s : State} (hc : VC s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16) :
    WP isa (.block vcand) s fun s' =>
      s'.gpr .rax = BitVec.ofNat 64 (maskN fun i => (byte (s.mem.readW (s.gpr .rsi) 128) i).toNat) ∧
      (∀ l < 2, s'.lane .xmm0 l = candV (s.mem.readW (s.gpr .rsi) 128) l) ∧ VC s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  open VG.Proof.MlKem.X86_64 (ea_at add_ofNat_zero) in
  refine wp_vbcast128 (a := s.gpr .rsi) (by rw [ea_at, add_ofNat_zero]) hin fun s1 u1 => ?_
  refine wp_vbin fun s2 u2 => wp_vvar fun s3 u3 => wp_vbin fun s4 u4 => wp_vbin fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_vpmovmskb fun s7 u7 => wp_shr32 (by decide) (by decide) fun s8 u8 => WP.block_nil ?_
  have c1 := hc.lupd u1 (.inl rfl)
  have c2 := c1.lupd u2 (.inl rfl)
  have c3 := c2.lupd u3 (.inl rfl)
  have c4 := c3.lupd u4 (.inl rfl)
  have c5 := c4.lupd u5 (.inr rfl)
  have c6 := c5.lupd u6 (.inr rfl)
  have c7 := c6.gupd u7
  generalize s.mem.readW (s.gpr .rsi) 128 = L at u1 ⊢
  have h4 : ∀ l < 2, s4.lane .xmm0 l = candV L l := fun l hl => by
    rw [u4.val l hl, u3.val l hl, u2.val l hl, u1.val l hl, c1.c8 l hl, c2.c9 l hl, c3.c10 l hl]; rfl
  have h6 : ∀ l < 2, s6.lane .xmm1 l = XBinOp.eval .pshufb (XBinOp.eval .psubd (candV L l) qV4) (sgn l) :=
    fun l hl => by rw [u6.val l hl, u5.val l hl, h4 l hl, c4.c11 l hl, c5.c12 l hl]; rfl
  have h0 : ∀ l < 2, s8.lane .xmm0 l = candV L l := fun l hl => by
    rw [u8.lane, u7.lane, u6.other _ (by decide) l hl, u5.other _ (by decide) l hl, h4 l hl]
  have hb : ∀ i, (byte L i).toNat < 256 := fun i => (byte L i).isLt
  have hm : byteMask (s6.ymm .xmm1) 32 = BitVec.ofNat 64 (4096 * maskN fun i => (byte L i).toNat) := by
    rw [State.ymm_eq, h6 1 (by decide), h6 0 (by decide), byteMask_eq _ (by decide)]
    simp only [sgn, show (1 : Nat) ≠ 0 by decide, ite_false, ite_true]
    rw [mask_bsum, maskN]
    congr 2
    apply bsum_congr
    intro k hk
    by_cases h : k < 4
    · rw [itT h, dword_psubd _ _ h, dword_qV4 h, cand_dword _ (show 0 < 2 by decide) h,
        sign_sub_q (candN_lt _ hb _), Nat.mul_zero, Nat.zero_add]
    · rw [itF h, dword_psubd _ _ (by bdd_omega), dword_qV4 (by bdd_omega), cand_dword _ (show 1 < 2 by decide) (by bdd_omega),
        sign_sub_q (candN_lt _ hb _), show 4 * 1 + (k - 4) = k by bdd_omega]
  have hM : maskN (fun i => (byte L i).toNat) < 2 ^ 8 := bsum_lt _ 8
  refine ⟨?_, h0, c7.gupd u8, by rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem],
    by rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr], fun r hr => ?_⟩
  · rw [u8.gpr, u7.gpr, hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · rw [u8.other r hr, u7.other r hr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]

/-! ## The compaction -/

theorem ymm_halves (x : BitVec 256) : x.extractLsb' 128 128 ++ x.extractLsb' 0 128 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 128
  · rw [itT h]; simp [h]
  · rw [itF h]; simp only [show j - 128 < 128 by bdd_omega, decide_true, Bool.true_and]; exact congrArg _ (by bdd_omega)

/-- The table's entry for `M`, its doubleword of indices. -/
def tabLo (M : Nat) : BitVec 32 := dword (tblWords.getD (M + 1) 0 ++ tblWords.getD M 0) 0

theorem tblWords_length : tblWords.length = 536 := by simp [tblWords]

theorem ea_tbl {s : State} {M : Nat} (d : Nat) (h : s.gpr .rax = BitVec.ofNat 64 M)
    (ht : s.gpr .r11 = s.syms tblName) (hb : 8 * M + d < 2 ^ 64) :
    (s.ea { tabE with disp := d } - s.syms tblName).toNat = 8 * M + d := by
  simp only [State.ea, tabE, h, ht, show BitVec.ofInt 64 (d : Int) = BitVec.ofNat 64 d from rfl]
  rw [BitVec.add_assoc, VG.Offset.add_sub_cancel_left]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem ea_aV (w16 : Bool) (s : State) :
    s.ea (aV w16) = s.gpr .rbp + BitVec.ofNat 64 (cw w16 / 8 * (s.gpr .rdi).toNat) := by
  simp only [State.ea, aV, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  cases w16 <;> simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, cw, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The table's entry for the mask, and the candidates it selects to the
doublewords of `ymm0`: candidate `E / 16ⁱ mod 8` in doubleword `i`. -/
theorem vpre_ok {is : List Instr} {Q : State → Prop} {s : State} (hc : VC s) {L : BitVec 128}
    (h0 : ∀ l < 2, s.lane .xmm0 l = candV L l) {M : Nat} (hrax : s.gpr .rax = BitVec.ofNat 64 M)
    (hM : M < 256) (ht : s.gpr .r11 = s.syms tblName)
    (k : ∀ s4, VC s4 → s4.gpr = s.gpr → s4.mem = s.mem → s4.rd = s.rd → s4.wr = s.wr → s4.syms = s.syms →
      (∀ i < 8, (s4.ymm .xmm0).extractLsb' (32 * i) 32 = BitVec.ofNat 32 (candN (fun i => (byte L i).toNat)
          ((tabLo M).toNat / 16 ^ i % 8))) →
      WP isa (.block is) s4 Q) :
    WP isa (.block (.vmovdquTbl .xmm1 tabE tblName tblWords :: .vop (.vpbroadcastd .l256 .xmm1 .xmm1) ::
      .vop (.vvar .vpsrlvd .l256 .xmm1 .xmm1 .xmm13) :: .vop (.vpermd .xmm0 .xmm1 .xmm0) :: is)) s Q := by
  have he : (s.ea tabE - s.syms tblName).toNat = 8 * M := ea_tbl 0 hrax ht (by omega)
  refine wp_vtbl (o := M) ht he (by rw [tblWords_length]; omega) fun s1 u1 => wp_vpbcastd fun s2 u2 => wp_vvar fun s3 u3 => wp_vpermd fun s4 u4 => ?_
  have c4 : VC s4 := ((hc.lupd u1 (.inr rfl)).lupd u2 (.inr rfl)).lupd u3 (.inr rfl) |>.lupd u4 (.inl rfl)
  refine k s4 c4 (by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr]) (by rw [u4.mem, u3.mem, u2.mem, u1.mem])
    (by rw [u4.rd, u3.rd, u2.rd, u1.rd]) (by rw [u4.wr, u3.wr, u2.wr, u1.wr])
    (by rw [u4.syms, u3.syms, u2.syms, u1.syms]) fun i hi => ?_
  have hy4 : s4.ymm .xmm0 = permDwords (s3.ymm .xmm1) (s3.ymm .xmm0) := by
    rw [State.ymm_eq, u4.val 1 (by decide), u4.val 0 (by decide), Nat.mul_one, Nat.mul_zero, ymm_halves]
  have hx3 : s3.ymm .xmm0 = candV L 1 ++ candV L 0 := by
    rw [State.ymm_eq, u3.other .xmm0 (by decide) 1 (by decide), u3.other .xmm0 (by decide) 0 (by decide),
      u2.other .xmm0 (by decide) 1 (by decide), u2.other .xmm0 (by decide) 0 (by decide),
      u1.other .xmm0 (by decide) 1 (by decide), u1.other .xmm0 (by decide) 0 (by decide), h0 1 (by decide),
      h0 0 (by decide)]
  have hi3 : s3.ymm .xmm1 = idxV (tabLo M) := by
    rw [State.ymm_eq, u3.val 1 (by decide), u3.val 0 (by decide), u2.val 1 (by decide), u2.val 0 (by decide),
      u2.other .xmm13 (by decide) 1 (by decide), u2.other .xmm13 (by decide) 0 (by decide),
      u1.other .xmm13 (by decide) 1 (by decide), u1.other .xmm13 (by decide) 0 (by decide),
      u1.val 0 (by decide), hc.c13 1 (by decide), hc.c13 0 (by decide)]
    rfl
  rw [hy4, dw8_permDwords _ _ hi, hi3, idx_toNat _ hi, hx3]
  have hp : (tabLo M).toNat / 16 ^ i % 8 < 8 :=
    Nat.mod_lt _ (by decide)
  rw [ext_app2 _ _ hp]
  by_cases h4 : (tabLo M).toNat / 16 ^ i % 8 < 4
  · rw [itT h4, cand_dword _ (show 0 < 2 by decide) (Nat.mod_lt _ (by decide))]
    congr 2; omega
  · rw [itF h4, cand_dword _ (show 1 < 2 by decide) (Nat.mod_lt _ (by decide))]
    congr 2; omega

theorem satSignedWord_small {x : BitVec 32} (h : x.toNat < 32768) : satSignedWord x = x.setWidth 16 := by
  have e : x.toInt = x.toNat := by rw [BitVec.toInt_eq_toNat_cond, ite_eq_left (by bdd_omega)]
  rw [satSignedWord, ite_eq_right (by bdd_omega), ite_eq_right (by bdd_omega)]

/-- What `vput` leaves, of either width: the candidates the table's entry selects
stored at `a[j]`, and `j` and `rsi` advanced. -/
def VPut (w16 : Bool) (s : State) (L : BitVec 128) (M : Nat) (s' : State) : Prop :=
  (∃ V : BitVec (8 * cw w16), s'.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (cw w16 / 8 * (s.gpr .rdi).toNat)) V ∧
    ∀ i < 8, (V.extractLsb' (cw w16 * i) (cw w16)).toNat = candN (fun i => (byte L i).toNat)
      ((tabLo M).toNat / 16 ^ i % 8)) ∧
  s'.gpr .rdi = s.gpr .rdi + tblWords.getD (280 + M) 0 ∧
  s'.gpr .rsi = s.gpr .rsi + 12 ∧ VC s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
  ∀ r, r ≠ .rdi → r ≠ .rsi → s'.gpr r = s.gpr r

theorem vput_ok (w16 : Bool) {s : State} (hc : VC s) {L : BitVec 128} (h0 : ∀ l < 2, s.lane .xmm0 l = candV L l)
    {M : Nat} (hrax : s.gpr .rax = BitVec.ofNat 64 M) (hM : M < 256) (ht : s.gpr .r11 = s.syms tblName)
    (hout : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (cw w16 / 8 * (s.gpr .rdi).toNat)) (cw w16)) :
    WP isa (.block (vput w16)) s (VPut w16 s L M) := by
  have hb : ∀ i, (byte L i).toNat < 256 := fun i => (byte L i).isLt
  -- the stores, then the tail: `j` advanced by the entry's count, and `rsi` by 12
  have tail : ∀ s5 : State, s5.gpr = s.gpr → (∀ x l, s5.lane x l = s.lane x l → True) → VC s5 →
      s5.rd = s.rd → s5.wr = s.wr → s5.syms = s.syms →
      WP isa (.block [.aluTbl .add .rdi { tabE with disp := oNum } tblName tblWords, .alu .add .rsi (.imm 12)]) s5
        fun s' => s'.mem = s5.mem ∧ s'.gpr .rdi = s.gpr .rdi + tblWords.getD (280 + M) 0 ∧
          s'.gpr .rsi = s.gpr .rsi + 12 ∧ VC s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
          ∀ r, r ≠ .rdi → r ≠ .rsi → s'.gpr r = s.gpr r := by
    intro s5 g5 _ c5 r5 w5 y5
    have he : (s5.ea { tabE with disp := oNum } - s5.syms tblName).toNat = 8 * (280 + M) := by
      rw [ea_tbl oNum (by rw [g5]; exact hrax) (by rw [g5, y5]; exact ht) (by simp only [oNum]; omega)]
      simp only [oNum]; omega
    refine wp_addTbl (o := 280 + M) (by rw [g5, y5]; exact ht) he (by rw [tblWords_length]; omega) fun s6 u6 =>
      wp_addi' fun s7 u7 => WP.block_nil ?_
    refine ⟨by rw [u7.mem, u6.mem], by rw [u7.other _ (by decide), u6.gpr, g5], by rw [u7.gpr, u6.other _ (by decide), g5]; rfl,
      (c5.gupd u6).gupd u7, by rw [u7.rd, u6.rd, r5], by rw [u7.wr, u6.wr, w5], by rw [u7.syms, u6.syms, y5],
      fun r h1 h2 => by rw [u7.other r h2, u6.other r h1, g5]⟩
  cases w16
  · simp only [vput, vstore, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
    refine vpre_ok hc h0 hrax hM ht fun s4 c4 g4 m4 r4 w4 y4 hv => ?_
    refine wp_vst256s (a := s.gpr .rbp + BitVec.ofNat 64 (cw false / 8 * (s.gpr .rdi).toNat))
      (by rw [ea_aV false, g4]) (by rw [w4]; exact hout) fun s5 g5 l5 m5 r5 w5 y5 => ?_
    have c5 : VC s5 := ⟨fun l hl => by rw [l5, c4.c8 l hl], fun l hl => by rw [l5, c4.c9 l hl],
      fun l hl => by rw [l5, c4.c10 l hl], fun l hl => by rw [l5, c4.c11 l hl], fun l hl => by rw [l5, c4.c12 l hl],
      fun l hl => by rw [l5, c4.c13 l hl]⟩
    refine WP.mono (tail s5 (g5.trans g4) (fun _ _ _ => trivial) c5 (r5.trans r4) (w5.trans w4) (y5.trans y4))
      fun s' ⟨hm, hdi, hsi, hc', hr, hw, hy, ho⟩ => ⟨⟨s4.ymm .xmm0, by rw [hm, m5, m4], fun i hi => ?_⟩, hdi, hsi, hc', hr, hw, hy, ho⟩
    · show (BitVec.extractLsb' (32 * i) 32 (s4.ymm .xmm0)).toNat = _
      rw [hv i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
        have := candN_lt _ hb ((tabLo M).toNat / 16 ^ i % 8); omega)]
  · simp only [vput, vstore, ↓reduceIte, List.cons_append, List.nil_append]
    refine vpre_ok hc h0 hrax hM ht fun s4 c4 g4 m4 r4 w4 y4 hv => ?_
    refine wp_vext128 fun s5 u5 => wp_vbin128 fun s6 u6 => ?_
    have g6 : s6.gpr = s.gpr := by rw [u6.gpr, u5.gpr, g4]
    refine wp_vst128s (a := s.gpr .rbp + BitVec.ofNat 64 (cw true / 8 * (s.gpr .rdi).toNat))
      (by rw [ea_aV true, g6]) (by rw [u6.wr, u5.wr, w4]; exact hout) fun s7 g7 l7 m7 r7 w7 y7 => ?_
    have c6 : VC s6 := (c4.lupd u5 (.inr rfl)).lupd u6 (.inl rfl)
    have c7 : VC s7 := ⟨fun l hl => by rw [l7, c6.c8 l hl], fun l hl => by rw [l7, c6.c9 l hl],
      fun l hl => by rw [l7, c6.c10 l hl], fun l hl => by rw [l7, c6.c11 l hl], fun l hl => by rw [l7, c6.c12 l hl],
      fun l hl => by rw [l7, c6.c13 l hl]⟩
    have hm7 : s7.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (cw true / 8 * (s.gpr .rdi).toNat)) (s6.xmm .xmm0) := by
      rw [m7, u6.mem, u5.mem, m4]
    refine WP.mono (tail s7 (g7.trans g6) (fun _ _ _ => trivial) c7 (by rw [r7, u6.rd, u5.rd, r4])
      (by rw [w7, u6.wr, u5.wr, w4]) (by rw [y7, u6.syms, u5.syms, y4]))
      fun s' ⟨hm, hdi, hsi, hc', hr, hw, hy, ho⟩ => ⟨⟨s6.xmm .xmm0, by rw [hm, hm7], fun i hi => ?_⟩, hdi, hsi, hc', hr, hw, hy, ho⟩
    · -- word `i` of the packed halves is doubleword `i` of `ymm0`
      have hlo : s5.lane .xmm0 0 = s4.lane .xmm0 0 := u5.other .xmm0 (by decide) 0 (by decide)
      have hhi : s5.lane .xmm1 0 = s4.lane .xmm0 1 := by rw [u5.val 0 (by decide)]; rfl
      have hx : s6.xmm .xmm0 = XBinOp.eval .packssdw (s5.lane .xmm0 0) (s5.lane .xmm1 0) := by
        have := u6.val 0 (by decide); rw [ite_eq_left rfl] at this; exact this
      have hdw : ∀ j < 8, (s4.ymm .xmm0).extractLsb' (32 * j) 32 =
          dword (if j < 4 then s4.lane .xmm0 0 else s4.lane .xmm0 1) (j % 4) := fun j hj => by
        rw [State.ymm_eq, ext_app2 _ _ hj]
      have small : ∀ j < 8, ((s4.ymm .xmm0).extractLsb' (32 * j) 32).toNat < 32768 := fun j hj => by
        rw [hv j hj, BitVec.toNat_ofNat]
        have := candN_lt _ hb ((tabLo M).toNat / 16 ^ j % 8)
        omega
      show (word (s6.xmm .xmm0) i).toNat = _
      rw [hx, hlo, hhi, word_packssdw _ _ hi]
      have hv' := hv i hi
      have hs := small i hi
      rw [hdw i hi] at hv' hs
      by_cases h4 : i < 4
      · rw [itT h4] at hv' hs ⊢
        rw [Nat.mod_eq_of_lt h4] at hv' hs
        rw [satSignedWord_small hs, BitVec.toNat_setWidth, hv', BitVec.toNat_ofNat]
        rw [hv', BitVec.toNat_ofNat] at hs
        have := candN_lt _ hb ((tabLo M).toNat / 16 ^ i % 8)
        omega
      · rw [itF h4] at hv' hs ⊢
        rw [show i % 4 = i - 4 by omega] at hv' hs
        rw [satSignedWord_small hs, BitVec.toNat_setWidth, hv', BitVec.toNat_ofNat]
        rw [hv', BitVec.toNat_ofNat] at hs
        have := candN_lt _ hb ((tabLo M).toNat / 16 ^ i % 8)
        omega

theorem bsum8_bit (f : Nat → Bool) {k : Nat} (hk : k < 8) : bsum f 8 / 2 ^ k % 2 = (f k).toNat := by
  have e : bsum f 8 = bsum f k + 2 ^ k * bsum (fun i => f (k + i)) (1 + (7 - k)) := by
    rw [← bsum_add, show k + (1 + (7 - k)) = 8 by bdd_omega]
  rw [e, bsum_add _ 1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt (bsum_lt f k),
    Nat.zero_add, Nat.pow_one, Nat.add_mul_mod_self_left]
  simp only [bsum, Nat.add_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  exact Nat.mod_eq_of_lt (Bool.toNat_lt _)

theorem setBits_bsum (f : Nat → Bool) : setBits (bsum f 8) = (List.range 8).filter f := by
  unfold setBits
  apply List.filter_congr
  intro k hk
  rw [bsum8_bit f (List.mem_range.mp hk)]
  cases f k <;> rfl

end VG.Proof.MlKem.X86_64.S4
