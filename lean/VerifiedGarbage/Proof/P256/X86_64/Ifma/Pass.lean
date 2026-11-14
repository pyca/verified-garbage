module

-- separate module: its proofs (about 5 s, a digit's entry and addition) are not checked again when `VLoop` changes

public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCache
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafDigitRead
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafAddress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedEntryW
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedLoad
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Framework.X86_64.ZVecKeep
public import VerifiedGarbage.Proof.X25519.X86_64.Step
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.TabOk
public import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
public import VerifiedGarbage.Proof.Weierstrass.JacCoZ
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Proof.Weierstrass.Comb
public import VerifiedGarbage.Spec.P256

/-!
# P-256 on x86-64 with AVX512_IFMA: a digit of the loop

The table of `Q`'s odd multiples as limbs (`vtab_ok`), whose triples are a
function of `Q`'s coordinates (`tabQ`, `tabQ_pts`), and a digit that is not
zero: its sign, its point's entry, loaded from that table (`qEntry_ok`) or
made of the words of the generator's (`convG_ok`), and its addition to the
accumulator (`add_ok`), or the accumulator set to it (`set_ok`).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

/-!
## What the accumulator stands for

The vectors' accumulator `(xn, un, z)` is the Jacobian triple
`(4 xn, 4 un, 2 z)`. A doubling or an addition of distinct points keeps it a
triple of the point (`pinv_dbl`, `pinv_add`, `pinv_set`), and otherwise
makes its `z` zero, which every block keeps zero (`Pinv`): where `z` is not
zero at the end, the triple is the sum's.
-/

section

open VG VG.Impl.P256.X86_64.Ifma
open Spec.Weierstrass VG.Proof.Weierstrass

/-- P-256. -/
abbrev Cv : Curve := Spec.P256.curve

/-- `2²⁵⁶` over `2²⁶⁰`: a sixteenth, which the number of a field element's words stands for times. -/
def kap : Fin pN := Fin.ofNat pN (2 ^ 256) * rinv pN (2 ^ 260)

theorem kap16 : 16 * kap = 1 := by
  have h := mul_rinv unitR
  have e : Fin.ofNat pN (2 ^ 260) = 16 * Fin.ofNat pN (2 ^ 256) := by decide +kernel
  rw [e] at h
  unfold kap
  grind

/-- `kap`, as an element of the curve's field. -/
def kapC : Fe Cv := kap

theorem kapC16 : 16 * kapC = 1 := kap16

/-- The number of the words of a field element stands for a sixteenth of it. -/
theorem D_words (w : Nat) : D (w : Int) = toM pN (2 ^ 256) w * kap := by
  have h := mul_rinv (unitMod_pow_two (m := pN) (by decide) 256)
  unfold D dec toM kap
  rw [ofI_natCast]
  grind

/-- The accumulator `(xn, un, z)` stands for `A`, or its `z` is zero. -/
def Pinv (xn un z : Fe Cv) (A : Point Cv) : Prop := z = 0 ∨ InvJ Cv (4 * xn) (4 * un) (2 * z) A

theorem two_ne : (2 : Fe Cv) ≠ 0 := by decide

theorem one_ne : (1 : Fe Cv) ≠ 0 := by decide

/-- A doubling. -/
theorem pinv_dbl (hC : Law Cv) (ha : AM3 Cv) {xn un z : Fe Cv} {A : Point Cv} (hA : onCurve Cv A = true)
    (h : Pinv xn un z A) : Pinv (fX3 xn un z) (fU xn un z) (fZ3 un z) (Spec.Weierstrass.add A A) := by
  rcases h with rfl | h
  · exact Or.inl (by simp only [fZ3, fS, fB]; grind)
  · have h' := InvJ.dbl hC ha hA h
    have e := dbl_jac xn un z
    simp only [Prod.mk.injEq] at e
    exact Or.inr (h'.rescale hC two_ne one_ne (by grind) (by grind) (by grind))

/-- An addition of the entry of the triple `(ex, y, ez)` of `B`, or of its negative. -/
theorem pinv_add (hC : Law Cv) (ha : AM3 Cv) {p : AP (Fe Cv)} {y : Fe Cv} {A B : Point Cv} (hA : onCurve Cv A = true)
    (hB : onCurve Cv B = true) (h : Pinv p.xn p.un p.z A) (he : InvJ Cv p.ex y p.ez B) (hy : p.ey = 2 * y)
    (hzz : p.ezz = p.ez * p.ez) (hzzz : p.ezzz = p.ez * p.ez * p.ez) :
    Pinv p.X3 p.Un p.Z3 (Spec.Weierstrass.add A (if p.neg then negPt B else B)) := by
  by_cases hz : p.z = 0
  · exact Or.inl (by simp only [AP.Z3, hz]; grind)
  by_cases hez : p.ez = 0
  · exact Or.inl (by simp only [AP.Z3, hez]; grind)
  by_cases hH : p.H = 0
  · exact Or.inl (by simp only [AP.Z3, hH]; grind)
  rcases h with h | h
  · exact absurd h hz
  have hB' : onCurve Cv (if p.neg then negPt B else B) = true := by
    split
    · exact onCurve_negPt hB
    · exact hB
  have he' : InvJ Cv p.ex (if p.neg then 0 - y else y) p.ez (if p.neg then negPt B else B) := by
    split
    · have := he.negY
      rw [show (0 : Fe Cv) - y = -y by grind]
      exact this
    · exact he
  have hj := InvJ.add_ne hC ha hA hB' h he' (hC.mul_ne_zero two_ne hz) hez (by
    intro h0
    apply hH
    simp only [AP.H, hzz]
    have : (4 : Fe Cv) * (p.z * p.z * p.ex - p.xn * (p.ez * p.ez)) = 0 := by grind
    rcases (by by_contra hn; exact hC.mul_ne_zero (by decide : (4 : Fe Cv) ≠ 0) hn this :
      p.z * p.z * p.ex - p.xn * (p.ez * p.ez) = 0) with h1
    exact h1)
  have e := add_jac p y hy hzz hzzz
  dsimp only at hj
  rw [e] at hj
  exact Or.inr (hj.rescale hC one_ne two_ne (by grind) (by grind) (by grind))

/-- The entry of the triple `(ex, y, ez)` of `B`, or of its negative, as the accumulator. -/
theorem pinv_set (hC : Law Cv) {ex ey ez y : Fe Cv} {B : Point Cv} (neg : Bool) (he : InvJ Cv ex y ez B)
    (hy : ey = 2 * y) : Pinv ex (if neg then 0 - ey else ey) ez (if neg then negPt B else B) := by
  have he' : InvJ Cv ex (if neg then 0 - y else y) ez (if neg then negPt B else B) := by
    split
    · have := he.negY
      rw [show (0 : Fe Cv) - y = -y by grind]
      exact this
    · exact he
  refine Or.inr (he'.rescale hC two_ne one_ne (by grind) ?_ (by grind))
  cases neg <;> simp only [hy, Bool.false_eq_true, ↓reduceIte] <;> grind

end


/-!
## Entries of the tables' points

What the vectors' code reads through `rcx` and `rdx` is the words of field
elements of the working space or of the generator's table (`wv_ld`), and
the entry `convQ` makes of the words of a Jacobian triple with its `Z²` and
`Z³` is that triple's, scaled by a half (`entQ`).
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Mont (wordsVal off)
open Spec.Weierstrass VG.Proof.Weierstrass

theorem wordsVal4 (m : Mem) (base : Addr) (d : Nat) : wordsVal m base d 4 =
    (Mont.word m base d).toNat + 2 ^ 64 * ((Mont.word m base (d + 8)).toNat + 2 ^ 64 *
      ((Mont.word m base (d + 8 + 8)).toNat + 2 ^ 64 * ((Mont.word m base (d + 8 + 8 + 8)).toNat + 2 ^ 64 * 0))) := rfl

/-- The number of the words read through `b` at `d` is that of the four words there. -/
theorem wv_ld (s : State) (b : Reg) (hb : uBase b = true) (d : Nat) :
    wv (envOf s) (.ld b d) = (wordsVal s.mem (s.gpr b) d 4 : Nat) := by
  have e (k : Nat) : (T.ld b d).int (envOf s) k =
      ((s.mem.readW (s.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64).toNat : Int) := by
    simp only [T.int, envOf, hb, ite_true]
  rw [wordsVal4]
  unfold wv
  rw [e 0, e 1, e 2, e 3]
  unfold Mont.word off
  rw [show d + 8 + 8 = d + 8 * 2 by omega_using [], show d + 8 * 2 + 8 = d + 8 * 3 by omega_using [], show d + 8 * 0 = d by omega_using [],
    show d + 8 * 1 = d + 8 by omega_using []]
  omega_using []

/-- The words at `x + d` from `base` are those at `d` from `base + x`. -/
theorem wordsVal_off (m : Mem) (base : Addr) (x d : Nat) : ∀ k, wordsVal m (off base x) d k = wordsVal m base (x + d) k
  | 0 => rfl
  | k + 1 => by
    simp only [wordsVal]
    rw [wordsVal_off m base x (d + 8) k, Nat.add_assoc]
    simp only [Mont.word, off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The fields of the entry of the Jacobian triple `(X, Y, Z)`, a half of it: `X / 4`, `Y / 4`
(twice `Y / 8`), `Z / 2`, and the latter's square and cube. -/
def entQ (X Y Z : Fe Cv) (neg : Bool) (xn un z : Fe Cv) : AP (Fe Cv) :=
  ⟨xn, un, z, 4 * kapC * X, 4 * kapC * Y, 8 * kapC * Z, 4 * kapC * (Z * Z), 2 * kapC * (Z * Z * Z), neg⟩

theorem entQ_zz (X Y Z : Fe Cv) (neg : Bool) (xn un z : Fe Cv) :
    (entQ X Y Z neg xn un z).ezz = (entQ X Y Z neg xn un z).ez * (entQ X Y Z neg xn un z).ez := by
  have := kapC16
  simp only [entQ]
  grind

theorem entQ_zzz (X Y Z : Fe Cv) (neg : Bool) (xn un z : Fe Cv) :
    (entQ X Y Z neg xn un z).ezzz =
      (entQ X Y Z neg xn un z).ez * (entQ X Y Z neg xn un z).ez * (entQ X Y Z neg xn un z).ez := by
  have := kapC16
  simp only [entQ]
  grind

/-- The entry's triple is the point's. -/
theorem entQ_inv (hC : Law Cv) {X Y Z : Fe Cv} {B : Point Cv} (h : InvJ Cv X Y Z B) (neg : Bool) (xn un z : Fe Cv) :
    InvJ Cv (entQ X Y Z neg xn un z).ex (2 * kapC * Y) (entQ X Y Z neg xn un z).ez B ∧
      (entQ X Y Z neg xn un z).ey = 2 * (2 * kapC * Y) := by
  have k := kapC16
  refine ⟨h.rescale hC one_ne two_ne ?_ ?_ ?_, ?_⟩
  · simp only [entQ]; grind
  · grind
  · simp only [entQ]; grind
  · simp only [entQ]; grind

/-- `entQ`, with the field's elements as numbers modulo `pN`. -/
def entQN (X Y Z : Fin pN) (neg : Bool) (xn un z : Fin pN) : AP (Fin pN) :=
  ⟨xn, un, z, 4 * kap * X, 4 * kap * Y, 8 * kap * Z, 4 * kap * (Z * Z), 2 * kap * (Z * Z * Z), neg⟩

theorem entQN_eq (X Y Z : Fin pN) (neg : Bool) (xn un z : Fin pN) :
    entQN X Y Z neg xn un z = entQ X Y Z neg xn un z := rfl

/-- A small multiple of the number of a field element's words. -/
theorem D_mul_words (n : Nat) (w : Nat) {X : Fin pN} (h : toM pN (2 ^ 256) w = X) :
    D ((n : Int) * (w : Int)) = Fin.ofNat pN n * kap * X := by
  rw [show D ((n : Int) * (w : Int)) = Fin.ofNat pN n * D (w : Int) from dec_nat_mul n _, D_words, h]
  grind

/-- The entry that `convQ` makes of the words of `X`, `Y`, `Z`, `Z²` and `Z³`. -/
theorem entOk_Q {E : Env} {ta tb : F5 T} {wx wy wz wzz wzzz : Int} {nx ny nz nzz nzzz : Nat} {X Y Z : Fin pN}
    (c0 : Car E 0 ta (D (4 * wzz))) (c1 : Car E 1 ta (D (4 * wx))) (c2 : Car E 2 ta (D (8 * wz)))
    (c3 : Car E 3 ta (D (4 * wy))) (cb : Ent E 0 tb (D (2 * wzzz)))
    (ex : wx = (nx : Nat)) (ey : wy = (ny : Nat)) (ez : wz = (nz : Nat)) (ezz : wzz = (nzz : Nat))
    (ezzz : wzzz = (nzzz : Nat))
    (hx : toM pN (2 ^ 256) nx = X) (hy : toM pN (2 ^ 256) ny = Y) (hz : toM pN (2 ^ 256) nz = Z)
    (hzz : toM pN (2 ^ 256) nzz = Z * Z) (hzzz : toM pN (2 ^ 256) nzzz = Z * Z * Z) (neg : Bool) (xn un z : Fin pN) :
    EntOk E ta tb (entQN X Y Z neg xn un z) := by
  subst ex ey ez ezz ezzz
  have nb : Nb ≤ 2 ^ 259 := by simp only [Nb]; omega_using []
  have d0 := D_mul_words 4 nzz hzz
  have d1 := D_mul_words 4 nx hx
  have d2 := D_mul_words 8 nz hz
  have d3 := D_mul_words 4 ny hy
  have d4 := D_mul_words 2 nzzz hzzz
  exact ⟨⟨c0.c, Int.lt_of_lt_of_le c0.hi nb, c0.d.trans d0⟩, ⟨c1.c, Int.lt_of_lt_of_le c1.hi nb, c1.d.trans d1⟩,
    ⟨c2.c, Int.lt_of_lt_of_le c2.hi nb, c2.d.trans d2⟩, ⟨c3.c, Int.lt_of_lt_of_le c3.hi nb, c3.d.trans d3⟩,
    ⟨cb.c, cb.hi, cb.d.trans d4⟩⟩

theorem D_cHalf : D (cHalf : Nat) = 8 * kap := by
  have e : Fin.ofNat pN cHalf = 8 * Fin.ofNat pN (2 ^ 256) := by decide +kernel
  unfold D dec kap
  rw [ofI_natCast, e]
  grind

theorem D_cQuarter : D (cQuarter : Nat) = 4 * kap := by
  have e : Fin.ofNat pN cQuarter = 4 * Fin.ofNat pN (2 ^ 256) := by decide +kernel
  unfold D dec kap
  rw [ofI_natCast, e]
  grind

theorem D_cEighth : D (cEighth : Nat) = 2 * kap := by
  have e : Fin.ofNat pN cEighth = 2 * Fin.ofNat pN (2 ^ 256) := by decide +kernel
  unfold D dec kap
  rw [ofI_natCast, e]
  grind

/-- The entry that `convG` makes of the words of `x` and `y`: that of the triple `(x, y, 1)`. -/
theorem entOk_G {E : Env} {ta tb : F5 T} {wx wy : Int} {nx ny : Nat} {x y : Fin pN}
    (c0 : Ent E 0 ta (D (cQuarter : Nat))) (c1 : Ent E 1 ta (D (4 * wx))) (c2 : Ent E 2 ta (D (cHalf : Nat)))
    (c3 : Ent E 3 ta (D (4 * wy))) (cb : Ent E 0 tb (D (cEighth : Nat)))
    (ex : wx = (nx : Nat)) (ey : wy = (ny : Nat))
    (hx : toM pN (2 ^ 256) nx = x) (hy : toM pN (2 ^ 256) ny = y) (neg : Bool) (xn un z : Fin pN) :
    EntOk E ta tb (entQN x y 1 neg xn un z) := by
  subst ex ey
  have d1 := D_mul_words 4 nx hx
  have d3 := D_mul_words 4 ny hy
  exact ⟨⟨c0.c, c0.hi, c0.d.trans (by rw [D_cQuarter]; simp only [entQN]; grind)⟩, ⟨c1.c, c1.hi, c1.d.trans d1⟩,
    ⟨c2.c, c2.hi, c2.d.trans (by rw [D_cHalf]; simp only [entQN]; grind)⟩, ⟨c3.c, c3.hi, c3.d.trans d3⟩,
    ⟨cb.c, cb.hi, cb.d.trans (by rw [D_cEighth]; simp only [entQN]; grind)⟩⟩

/-! ### The mask of an entry's sign -/

/-- The quadwords of the mask of a sign among the constants: all ones in the lanes 0 and 1 for a
negative entry, else zero. -/
theorem sgn_m {s : State} (hc : Ctx par s) (neg : Bool)
    (h9 : s.gpr .r9 = s.gpr .r10 + BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if neg then 3 else 0))))
    (k : Nat) (hk : k < 4) : (envOf s).m .r9 0 k = if neg = true ∧ k < 2 then -1 else 0 := by
  have e : (envOf s).m .r9 0 k = (s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (0 + 8 * k)) 64).toInt := rfl
  have key : ∀ neg : Bool, ∀ k < 4, 4 * poolLit.idxOf (K4.lanes (if neg then 3 else 0)) + k < par.cst.length ∧
      (BitVec.ofNat 64 (par.cst.getD (4 * poolLit.idxOf (K4.lanes (if neg then 3 else 0)) + k) 0)).toInt =
        (if neg = true ∧ k < 2 then -1 else 0) := by decide +kernel
  obtain ⟨hl, hv⟩ := key neg k hk
  have c : s.mem.readW (s.gpr .r10 + BitVec.ofNat 64
      (8 * (4 * poolLit.idxOf (K4.lanes (if neg then 3 else 0)) + k))) 64 = _ := hc.cst _ hl
  rw [e, h9, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 32 * poolLit.idxOf (K4.lanes (if neg then 3 else 0)) + (0 + 8 * k) =
      8 * (4 * poolLit.idxOf (K4.lanes (if neg then 3 else 0)) + k) by omega_using [], c]
  exact hv

/-- Bounds with the mask of a sign at `r9`. -/
theorem envOK_sgn {s : State} {B : Bnds} (h : EnvOK s B) {neg : Bool}
    (hm : ∀ k, k < 4 → (envOf s).m .r9 0 k = if neg = true ∧ k < 2 then -1 else 0) : EnvOK s (sgnB B) := by
  refine ⟨h.v, fun b d k hk => ?_⟩
  simp only [sgnB]
  by_cases hb : b = .r9 ∧ d = 0
  · obtain ⟨rfl, rfl⟩ := hb
    simp only [and_self, ite_true]
    rw [hm k hk]
    split <;> split <;> omega
  · simp only [hb, ite_false]
    exact h.m b d k hk

theorem sgnOk_of {E : Env} {neg : Bool} (hm : ∀ k, k < 4 → E.m .r9 0 k = if neg = true ∧ k < 2 then -1 else 0) :
    SgnOk E sgnT.l0 neg := by
  have h0 := hm 0 (by decide); have h1 := hm 1 (by decide); have h2 := hm 2 (by decide); have h3 := hm 3 (by decide)
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show E.m .r9 0 0 = _
    rw [h0]; cases neg <;> rfl
  · show E.m .r9 0 1 = _
    rw [h1]; cases neg <;> rfl
  · show E.m .r9 0 2 = _
    rw [h2]; cases neg <;> rfl
  · show E.m .r9 0 3 = _
    rw [h3]; cases neg <;> rfl

end

/-! ### The table in vectors: the points of its blocks -/

section

open Spec.Weierstrass VG.Proof.Weierstrass

/-- `dblu`'s points: from `Q`'s triple `(x, y, z)` with `z` a half, as its entry has it (`y' = 2 y`,
`zz = z²`), `2 Q` and `Q` with one `Z`, which is `y'`. -/
theorem dp_pts (hC : Law Cv) (hO : PrimeOrder Cv) (ha : AM3 Cv) (h3 : 3 ≤ Cv.n) {Q : Point Cv}
    (hQ : onCurve Cv Q = true) (hQ0 : Q ≠ .infinity) {x y y' z : Fe Cv} (hj : InvJ Cv x y z Q) (hz : 2 * z = 1)
    (hy : y' = 2 * y) :
    InvJ Cv (DP.XT ⟨x, y', z * z⟩) (DP.YT ⟨x, y', z * z⟩) y' (mul 2 Q) ∧
      InvJ Cv (4 * DP.S ⟨x, y', z * z⟩) (4 * DP.YY2 ⟨x, y', z * z⟩) y' Q ∧ y' ≠ 0 := by
  have j2 := InvJ.dbl hC ha hQ hj
  rw [show Spec.Weierstrass.add Q Q = mul 2 Q by
    rw [show Spec.Weierstrass.add Q Q = Spec.Weierstrass.add (mul 1 Q) (mul 1 Q) by rw [mul_one_pt],
      hC.add_mul_mul hQ]] at j2
  have jT : InvJ Cv (DP.XT ⟨x, y', z * z⟩) (DP.YT ⟨x, y', z * z⟩) y' (mul 2 Q) := by
    refine j2.rescale hC (l := 2) (m := 1) two_ne one_ne ?_ ?_ ?_
    · simp only [dblJF, DP.XT, DP.MM, DP.M, DP.XX, DP.ZZ, DP.S, DP.YY, hy]; grind
    · simp only [dblJF, DP.YT, DP.w, DP.YY2, DP.MM, DP.M, DP.XX, DP.ZZ, DP.S, DP.YY, hy]; grind
    · simp only [dblJF, hy]; grind
  have hy0 : y' ≠ 0 := fun h0 =>
    CoZTable.two_ne_zero_pt hO hQ hQ0 h3 ((jT.z_zero_iff hC).mp h0)
  refine ⟨jT, hj.rescale hC (l := 2 * y') (m := 1) (hC.mul_ne_zero two_ne hy0) one_ne ?_ ?_ ?_, hy0⟩
  · simp only [DP.S, DP.YY]; grind
  · simp only [DP.YY2, DP.YY, hy]; grind
  · grind

/-- `zaddu`'s points: from `2 Q` and `[2 k + 1]Q` with one `Z`, `[2 k + 3]Q` and `2 Q` with the sum's. -/
theorem zp_pts (hC : Law Cv) (hO : PrimeOrder Cv) (ha : AM3 Cv) (hn : 17 ≤ Cv.n) {Q : Point Cv}
    (hQ : onCurve Cv Q = true) (hQ0 : Q ≠ .infinity) {k : Nat} (hk : k ≤ 6) {p : ZP (Fe Cv)}
    (h1 : InvJ Cv p.x1 p.y1 p.z (mul 2 Q)) (h2 : InvJ Cv p.x2 p.y2 p.z (mul (2 * k + 1) Q)) (hz : p.z ≠ 0) :
    InvJ Cv p.x3 (p.Ev - p.A1) p.z3 (mul (2 * (k + 1) + 1) Q) ∧ InvJ Cv p.W1 p.A1 p.z3 (mul 2 Q) ∧ p.z3 ≠ 0 := by
  have hx := CoZTable.coz_x hC hO hn hQ hQ0 hk h1 h2 hz
  obtain ⟨js, jd⟩ := InvJ.zaddu hC ha (hC.onCurve_mul hQ 2) (hC.onCurve_mul hQ _) h1 h2 hz hx
  rw [hC.add_mul_mul hQ, zp_zadduF] at js
  rw [zp_zadduF] at jd
  have js' : InvJ Cv p.x3 (p.Ev - p.A1) p.z3 (mul (2 * (k + 1) + 1) Q) := by
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega_using []]; exact js
  exact ⟨js', jd, fun hh => Window5.mul_ne_infinity hO hQ hQ0 (m := 2 * (k + 1) + 1) (by omega_using []) (by omega_using [hn, hk])
    ((js'.z_zero_iff hC).mp hh)⟩

end

/-!
## Between the vectors' blocks

The loop's instructions between the blocks change general registers and
flags only (`SKeep`): what is known of the vectors (`AccOk`, `EnvOK`) and
of what the blocks may read and write (`Ctx`) is kept by them.
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)

/-- A step that changes only flags and the general registers `rs`. -/
structure SKeep (rs : List Reg) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  xmm : t.xmm = s.xmm
  ymmHi : t.ymmHi = s.ymmHi
  ymmH : t.ymmH = s.ymmH

theorem SKeep.refl (rs : List Reg) (s : State) : SKeep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SKeep.trans {rs : List Reg} {s t u : State} (h₁ : SKeep rs s t) (h₂ : SKeep rs t u) : SKeep rs s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.xmm.trans h₁.xmm, h₂.ymmHi.trans h₁.ymmHi, h₂.ymmH.trans h₁.ymmH⟩

theorem SKeep.mono {rs rs' : List Reg} {s t : State} (h : SKeep rs s t) (hs : ∀ r ∈ rs, r ∈ rs') : SKeep rs' s t :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.xmm, h.ymmHi, h.ymmH⟩

/-- The vector registers' quadwords are kept. -/
theorem SKeep.v {rs : List Reg} {s t : State} (h : SKeep rs s t) (r k : Nat) : (envOf t).v r k = (envOf s).v r k := by
  have e : t.vy (vreg r) = s.vy (vreg r) := by
    cases vreg r with
    | lo x => simp only [State.vy, State.ymm, h.xmm, h.ymmHi]
    | hi x => simp only [State.vy, h.ymmH]
  simp only [envOf, VG.Proof.Bignum.X86_64.Ifma.qv, e]

/-- What is read through a register that is kept. -/
theorem SKeep.m {rs : List Reg} {s t : State} (h : SKeep rs s t) {b : Reg} (hb : b ∉ rs) (d k : Nat) :
    (envOf t).m b d k = (envOf s).m b d k := by
  simp only [envOf, h.mem, h.gpr b hb]

/-- Scalar code that keeps memory and the registers but `rs` keeps the vector registers too. -/
theorem WP.skeep {c : Prog isa} (hc : scalCode c = true) {s : State} {Q : State → Prop} {rs : List Reg}
    (h : WP isa c s fun t => Q t ∧ VG.Proof.X25519.X86_64.Keeps rs s t) : WP isa c s fun t => Q t ∧ SKeep rs s t :=
  WP.mono (WP.hvecKeep hc (WP.vecKeep hc h)) fun _ ⟨⟨⟨q, k⟩, x, y⟩, yh⟩ =>
    ⟨q, ⟨k.1, k.2.1, k.2.2.1, k.2.2.2, x, y, yh⟩⟩

/-! ### What the vectors stand for depends only on the vector registers -/

theorem vI_t5_congr {E E' : Env} (h : ∀ r k, E'.v r k = E.v r k) (r k : Nat) : vI E' k (t5 r) = vI E k (t5 r) := by
  simp only [vI, t5, T.int, h]

theorem carried_t5_congr {E E' : Env} (h : ∀ r k, E'.v r k = E.v r k) {r k : Nat} (hc : Carried E k (t5 r)) :
    Carried E' k (t5 r) := by
  simp only [Carried, t5, T.int, h] at hc ⊢
  exact hc

theorem Lim.congr {E E' : Env} (h : ∀ r k, E'.v r k = E.v r k) {bd : Int} {r k : Nat} {x : Fin pN}
    (hl : Lim bd E k (t5 r) x) : Lim bd E' k (t5 r) x :=
  ⟨carried_t5_congr h hl.c, by rw [vI_t5_congr h]; exact hl.hi, by rw [vI_t5_congr h]; exact hl.d⟩

theorem Val.congr {E E' : Env} (h : ∀ r k, E'.v r k = E.v r k) {bd : Int} {r k : Nat} {x : Fin pN}
    (hl : Val bd E k (t5 r) x) : Val bd E' k (t5 r) x :=
  ⟨by rw [vI_t5_congr h]; exact hl.lo, by rw [vI_t5_congr h]; exact hl.hi, by rw [vI_t5_congr h]; exact hl.d⟩

theorem AccOk.congr {E E' : Env} (h : ∀ r k, E'.v r k = E.v r k) {xn un z : Fin pN}
    (ha : AccOk E (t5 0) (t5 5) (t5 10) (t5 15) xn un z) : AccOk E' (t5 0) (t5 5) (t5 10) (t5 15) xn un z :=
  ⟨by rw [vI_t5_congr h]; exact ha.ul, by rw [vI_t5_congr h]; exact ha.uh, by rw [vI_t5_congr h]; exact ha.du,
    ha.zn.congr h, ha.a.congr h, ha.x.congr h, ha.aa.congr h, ha.xx.congr h⟩

theorem EntOk.congr {E E' : Env} (h : ∀ r k, E'.v r k = E.v r k) {p : AP (Fin pN)}
    (he : EntOk E (t5 20) (t5 25) p) : EntOk E' (t5 20) (t5 25) p :=
  ⟨he.zz.congr h, he.x.congr h, he.z.congr h, he.y.congr h, he.zzz.congr h⟩

/-- The bounds of the places of a block's start are kept where the slots' register is. -/
theorem envOK_skeep {rs : List Reg} {s t : State} (h : SKeep rs s t) (hdi : Reg.rdi ∉ rs) {L : List Loc} {bt : BT}
    (hB : EnvOK s (bndsOf L bt)) : EnvOK t (bndsOf L bt) := by
  refine ⟨fun r k hk => by rw [h.v]; exact hB.v r k hk, fun b d k hk => ?_⟩
  by_cases hb : b ∈ rs
  · have hne : b ≠ .rdi := fun e => hdi (e ▸ hb)
    simp only [bndsOf]
    by_cases hu : uBase b = true
    · simp only [hu, ite_true, envOf]
      have := (t.mem.readW (t.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64).isLt
      omega_using []
    · have hm : (envOf t).m b d k = (t.mem.readW (t.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64).toInt := by
        simp only [envOf, hu, Bool.false_eq_true, ite_false]
      simp only [hu, Bool.false_eq_true, ite_false, hne, hm]
      exact toInt_range _
  · rw [h.m hb]
    exact hB.m b d k hk

/-- What the blocks may read and write is kept, given what the changed registers of `rcx`, `rdx` and `r9` are at. -/
theorem ctx_skeep {rs : List Reg} {s t : State} (hc : Ctx par s) (h : SKeep rs s t) (hdi : Reg.rdi ∉ rs)
    (h10 : Reg.r10 ∉ rs)
    (hp : ∀ b d, b ∈ rs → d + 32 ≤ par.lim b → InRegions (s.rd ++ s.wr) (t.gpr b + BitVec.ofNat 64 d) 32 ∧
      Mem.Sep (t.gpr b + BitVec.ofNat 64 d) 32 (s.gpr .rdi + BitVec.ofNat 64 par.lo) (par.win - par.lo)) :
    Ctx par t := by
  have gdi := h.gpr .rdi hdi
  have g10 : t.gpr par.cb = s.gpr par.cb := h.gpr .r10 h10
  refine ⟨?_, hc.small, ?_, ?_, ?_, ?_, ?_, hc.cb⟩
  · intro d hd; rw [h.wr, gdi]; exact hc.win d hd
  · intro b d hb hcb hd
    rw [h.rd, h.wr]
    by_cases hbr : b ∈ rs
    · exact (hp b d hbr hd).1
    · rw [h.gpr b hbr]; exact hc.rd b d hb hcb hd
  · intro b d hb hcb hd
    rw [gdi]
    by_cases hbr : b ∈ rs
    · exact (hp b d hbr hd).2
    · rw [h.gpr b hbr]; exact hc.sep b d hb hcb hd
  · intro d hd; rw [h.rd, h.wr, g10]; exact hc.crd d hd
  · intro d hd; rw [gdi, g10]; exact hc.csep d hd
  · intro i hi; rw [h.mem, g10]; exact hc.cst i hi

end


open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64 VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass (Unch toM InvJ Law PrimeOrder AM3 mul_one_pt)
open VG.Proof.Bignum.X86_64.Ifma (qv)
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)

/-- `r9` at constant `k` of the blocks' constants. -/
theorem signPtr_ok (s : State) (neg : Bool) :
    WP isa (.block (signPtr neg)) s fun t =>
      t.gpr .r9 = s.gpr .r10 + BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if neg then 3 else 0))) ∧
        Keeps [.r9] s t := by
  have ht : 32 * poolLit.idxOf (K4.lanes (if neg then 3 else 0)) < 2 ^ 31 := by
    cases neg <;> decide +kernel
  apply WP.of_runBlock
  simp only [signPtr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, imm32_sext ht,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, Option.map_some, Option.bind_some, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- A register takes another's value. -/
theorem mov_ok (s : State) (d r : Reg) :
    WP isa (.block [.mov d (.reg r)]) s fun t => t.gpr d = s.gpr r ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg, Option.map_some,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r' hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem setWidth8 (b : BitVec 8) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The magnitude of a digit of `Q`'s scalar. -/
def qMag (b : BitVec 8) : Nat := if b.toNat < 128 then b.toNat else 256 - b.toNat

/-- The sign of a digit of `Q`'s scalar: its magnitude in `r8`, and `r9` at the mask of its sign. -/
theorem qSign_ok (s : State) {b : BitVec 8} (h8 : s.gpr .r8 = b.setWidth 64) :
    WP isa (.seq (.block [.alu .cmp .r8 (.imm 128)]) (.ite .b (.block (signPtr false))
      (.block (([.mov32 .rax (.imm 256), .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax)] : List Instr) ++ signPtr true)))) s
      fun t => t.gpr .r8 = BitVec.ofNat 64 (qMag b) ∧
        t.gpr .r9 = s.gpr .r10 +
          BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if decide (b.toNat < 128) = false then 3 else 0))) ∧
        SKeep [.rax, .r8, .r9] s t := by
  apply WP.seq
  refine WP.mono (WP.skeep rfl (nafSign_ok s h8)) fun u ⟨hu, ku⟩ => ?_
  have u8 : u.gpr .r8 = b.setWidth 64 := (ku.gpr .r8 (by decide)).trans h8
  have u10 : u.gpr .r10 = s.gpr .r10 := ku.gpr .r10 (by decide)
  refine WP.ite (decide (b.toNat < 128)) hu (fun hb => ?_) (fun hb => ?_)
  · have hp : b.toNat < 128 := of_decide_eq_true hb
    refine WP.mono (WP.skeep rfl (signPtr_ok u false)) fun t ⟨ht, kt⟩ => ⟨?_, ?_, ?_⟩
    · rw [kt.gpr .r8 (by decide), u8, setWidth8]
      simp only [qMag, hp, ↓reduceIte]
    · rw [ht, u10]
      simp only [hp, decide_true, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
    · exact (ku.mono (by decide)).trans (kt.mono (by decide))
  · have hp : ¬b.toNat < 128 := of_decide_eq_false hb
    rw [WP.block_append_iff]
    refine WP.mono (WP.skeep rfl (nafAbs_ok u u8)) fun w ⟨hw, kw⟩ => ?_
    refine WP.mono (WP.skeep rfl (signPtr_ok w true)) fun t ⟨ht, kt⟩ => ⟨?_, ?_, ?_⟩
    · rw [kt.gpr .r8 (by decide), hw]
      simp only [qMag, hp, ↓reduceIte]
    · rw [ht, kw.gpr .r10 (by decide), u10]
      simp only [hp, decide_false, ↓reduceIte]
    · exact ((ku.mono (by decide)).trans (kw.mono (by decide))).trans (kt.mono (by decide))

/-- What a digit's code keeps: the registers but those it works with, the regions, and memory but the slots. -/
structure LKeep (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r11] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Unch (s.gpr .rdi) [(cfg.sbase, slotsLen)] s.mem t.mem

theorem LKeep.refl (s : State) : LKeep s s := ⟨fun _ _ => rfl, rfl, rfl, Unch.refl _ _ _⟩

theorem LKeep.trans {s t u : State} (h₁ : LKeep s t) (h₂ : LKeep t u) : LKeep s u := by
  refine ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_⟩
  have := h₂.mem
  rw [h₁.gpr .rdi (by decide)] at this
  exact (h₁.mem.trans this).mono (by decide)

theorem LKeep.of_skeep {rs : List Reg} {s t : State} (h : SKeep rs s t)
    (hr : (rs.all fun r => [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r11].contains r) = true := by decide) :
    LKeep s t :=
  ⟨fun r h' => h.gpr r fun hin => h' (List.contains_iff_mem.mp (List.all_eq_true.mp hr r hin)), h.rd, h.wr,
    by rw [h.mem]; exact Unch.refl _ _ _⟩

theorem LKeep.of_kept {s t : State} (h : Kept s t) : LKeep s t :=
  ⟨fun r _ => congrFun h.gpr r, by rw [← h.eq]; rfl, by rw [← h.eq]; rfl, h.mem⟩

theorem lim_other {r : Reg} (h1 : r ≠ .rcx) (h2 : r ≠ .rdx) (h3 : r ≠ .r9) : par.lim r = 0 := by
  simp only [par, h1, h2, h3, ite_false]

/-! ### `Q`'s multiples kept as limbs -/

/-- The entry `(x, 2 y, z)` of the table, with `z²` and `z³`, is that of the triple `(4 x, 8 y, 2 z)`. -/
theorem entQN_virt (x y z : Fin pN) (neg : Bool) (xn un z0 : Fin pN) :
    entQN (4 * x) (8 * y) (2 * z) neg xn un z0 = ⟨xn, un, z0, x, 2 * y, z, z * z, z * (z * z), neg⟩ := by
  have := kap16
  simp only [entQN, AP.mk.injEq, true_and, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- The first `n` entries of `Q`'s table kept as limbs, from `TOFF` of the working space: entry `a` is that
of the triple `Tq a`. -/
def LTabN (Tq : Nat → Fin pN × Fin pN × Fin pN) (n : Nat) (m : Mem) (base : Addr) : Prop :=
  ∀ a, a < n → LEnt m (off base (TOFF + 200 * a)) (entQN (Tq a).1 (Tq a).2.1 (Tq a).2.2 false 0 0 0)

/-- The eight entries kept as limbs. -/
abbrev LTab (Tq : Nat → Fin pN × Fin pN × Fin pN) (m : Mem) (base : Addr) : Prop := LTabN Tq 8 m base

/-- The triples of the first `n` entries are those of `Q`'s odd multiples. -/
def QPts (Tq : Nat → Fin pN × Fin pN × Fin pN) (n : Nat) (Q : Spec.Weierstrass.Point Cv) : Prop :=
  ∀ a, a < n → InvJ Cv (Tq a).1 (Tq a).2.1 (Tq a).2.2 (Spec.Weierstrass.mul (2 * a + 1) Q)

/-- An entry kept as limbs is kept by what leaves its bytes. -/
theorem LEnt.unch {m m' : Mem} {base : Addr} {o : Nat} {P : AP (Fin pN)} {W : List (Nat × Nat)}
    (h : LEnt m (off base o) P) (hu : Unch base W m m') (hW : ∀ w ∈ W, o + 200 ≤ w.1 ∨ w.1 + w.2 ≤ o)
    (ho : o + 200 ≤ 2 ^ 64) : LEnt m' (off base o) P := by
  refine h.congr fun d k hd => ?_
  have := hu.word (d := o + (d + 8 * k)) (fun w hw => by have := hW w hw; omega_using [hd, this]) (by omega_using [ho, hd])
  simp only [Mont.word, off] at this
  rw [off, Offset.add_add]
  exact this

/-- The entries kept as limbs are kept by what leaves them. -/
theorem LTabN.unch {Tq : Nat → Fin pN × Fin pN × Fin pN} {n : Nat} {m m' : Mem} {base : Addr} {W : List (Nat × Nat)}
    (h : LTabN Tq n m base) (hu : Unch base W m m') (hn : n ≤ 8)
    (hW : ∀ w ∈ W, TOFF + 200 * n ≤ w.1 ∨ w.1 + w.2 ≤ TOFF) : LTabN Tq n m' base := by
  intro a ha
  exact (h a ha).unch hu (fun w hw => by have := hW w hw; simp only [TOFF] at *; omega_using [ha, this]) (by simp only [TOFF]; omega_using [hn, ha])

/-- The vector registers are kept. -/
theorem SKeep.qv {rs : List Reg} {s t : State} (h : SKeep rs s t) (r k : Nat) :
    qv t (vreg r) k = qv s (vreg r) k := by
  have e : t.vy (vreg r) = s.vy (vreg r) := by
    cases vreg r with
    | lo x => simp only [State.vy, State.ymm, h.xmm, h.ymmHi]
    | hi x => simp only [State.vy, h.ymmH]
  unfold VG.Proof.Bignum.X86_64.Ifma.qv
  rw [e]

/-- `rcx`, `rdx` and `rbp` at offsets of the working space. -/
theorem ptr3_ok (s : State) {e z p : Nat} (he : e < 2 ^ 31) (hz : z < 2 ^ 31) (hp : p < 2 ^ 31) :
    WP isa (.block [.mov .rcx (.reg .rdi), .alu .add .rcx (.imm (BitVec.ofNat 32 e)),
      .mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 z)),
      .mov .rbp (.reg .rdi), .alu .add .rbp (.imm (BitVec.ofNat 32 p))]) s fun t =>
      (t.gpr .rcx = s.gpr .rdi + BitVec.ofNat 64 e ∧ t.gpr .rdx = s.gpr .rdi + BitVec.ofNat 64 z ∧
        t.gpr .rbp = s.gpr .rdi + BitVec.ofNat 64 p) ∧ Keeps [.rcx, .rdx, .rbp] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, imm32_sext he, imm32_sext hz,
    imm32_sext hp, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, Option.map_some, Option.bind_some, ite_true, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨⟨trivial, trivial, trivial⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `rbp` moved on to the next entry's place. -/
theorem add200_ok (s : State) :
    WP isa (.block [.alu .add .rbp (.imm 200)]) s fun t =>
      t.gpr .rbp = s.gpr .rbp + BitVec.ofNat 64 200 ∧ Keeps [.rbp] s t := by
  have e : (200 : BitVec 32).signExtend 64 = BitVec.ofNat 64 200 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, e, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, Option.bind_some, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The count of the entries after the first, in `rax`. -/
theorem cnt7_ok (s : State) :
    WP isa (.block [.mov32 .rax (.imm 7)]) s fun t => t.gpr .rax = BitVec.ofNat 64 7 ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, RegUpd.gpr_setReg,
    Option.map_some, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- The count one less, and whether it is zero. -/
theorem decRax_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j ≤ 7) (h : s.gpr .rax = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .sub .rax (.imm 1)]) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 (j - 1) ∧ t.zf = some (decide (j - 1 = 0))) ∧ Keeps [.rax] s t := by
  have key' : ∀ j, j < 8 → 1 ≤ j →
      BitVec.ofNat 64 j - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (j - 1) ∧
        (BitVec.ofNat 64 (j - 1) == (0 : BitVec 64)) = decide (j - 1 = 0) := by decide
  have key : ∀ j, 1 ≤ j → j ≤ 7 →
      BitVec.ofNat 64 j - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (j - 1) ∧
        (BitVec.ofNat 64 (j - 1) == (0 : BitVec 64)) = decide (j - 1 = 0) := fun j h1 h7 => key' j (by omega_using [h7]) h1
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', h, (key j hj hj').1, RegUpd.gpr_setReg_self, RegUpd.zf_setReg,
    RegUpd.zf_arithFlags, (key j hj hj').2]
  refine ⟨⟨trivial, trivial⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- What the table's code keeps: the registers but those it reads through, stores through and counts
in, and memory but the vectors' slots and the entries. -/
structure TKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rbp] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Unch base [(cfg.sbase, slotsLen), (TOFF, 1624)] s.mem t.mem

theorem TKeep.refl (base : Addr) (s : State) : TKeep base s s := ⟨fun _ _ => rfl, rfl, rfl, Unch.refl _ _ _⟩

theorem TKeep.trans {base : Addr} {s t u : State} (h₁ : TKeep base s t) (h₂ : TKeep base t u) : TKeep base s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    (h₁.mem.trans h₂.mem).mono fun _ hw => (List.mem_append.mp hw).elim id id⟩

theorem TKeep.of_kept {base : Addr} {s t : State} (hdi : s.gpr .rdi = base) (k : Kept s t) : TKeep base s t :=
  ⟨fun r _ => congrFun k.gpr r, k.rd, k.wr, by
    have := k.mem
    rw [hdi] at this
    exact this.mono fun _ hw => by rw [List.mem_singleton.mp hw]; exact List.mem_cons_self⟩

theorem TKeep.of_skeep {base : Addr} {rs : List Reg} {s t : State} (k : SKeep rs s t)
    (hr : (rs.all fun r => [Reg.rax, .rcx, .rdx, .rbp].contains r) = true := by decide) : TKeep base s t :=
  ⟨fun r h' => k.gpr r fun hin => h' (List.contains_iff_mem.mp (List.all_eq_true.mp hr r hin)), k.rd, k.wr,
    by rw [k.mem]; exact Unch.refl _ _ _⟩

/-- What storing an entry keeps of the vector registers: all but the last three lanes of `ymm5`. -/
def RKeep (s t : State) : Prop :=
  ∀ r, r < 20 → ∀ k, k < 4 → (r = 5 → k = 0) → qv t (vreg r) k = qv s (vreg r) k

/-- What the blocks may read and write, after a change of memory that keeps their constants. -/
theorem ctx_mem {s t : State} (hc : Ctx par s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hm : ∀ i, i < par.cst.length → t.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (8 * i)) 64 =
      s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (8 * i)) 64) : Ctx par t := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := hc
  exact ⟨by rw [hg, hwr]; exact a, b, by rw [hg, hrd, hwr]; exact c, by rw [hg]; exact d,
    by rw [hg, hrd, hwr]; exact e, by rw [hg]; exact f, fun i hi => by rw [hg]; exact (hm i hi).trans (g i hi), h⟩

theorem vI_t5_on {E E' : Env} {r k : Nat} (h : ∀ i, i < 5 → E'.v (r + i) k = E.v (r + i) k) :
    vI E' k (t5 r) = vI E k (t5 r) := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide)
  rw [Nat.add_zero] at h0
  simp only [vI, t5, T.int, h0, h1, h2, h3, h4]

theorem carried_t5_on {E E' : Env} {r k : Nat} (h : ∀ i, i < 5 → E'.v (r + i) k = E.v (r + i) k)
    (hc : Carried E k (t5 r)) : Carried E' k (t5 r) := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide)
  rw [Nat.add_zero] at h0
  simp only [Carried, t5, T.int, h0, h1, h2, h3, h4] at hc ⊢
  exact hc

/-- The registers of five limbs at lane `k`, after an entry is stored. -/
theorem RKeep.v {s t : State} (h : RKeep s t) {r k : Nat} (hr : r + 5 ≤ 20) (hk : k < 4)
    (h5 : r ≤ 5 → 5 < r + 5 → k = 0) (i : Nat) (hi : i < 5) : (envOf t).v (r + i) k = (envOf s).v (r + i) k :=
  congrArg BitVec.toInt (h (r + i) (by omega_using [hr, hi]) k hk (fun e => h5 (by omega_using [e]) (by omega_using [hi, e])))

theorem Lim.rkeep {s t : State} (h : RKeep s t) {bd : Int} {r k : Nat} {x : Fin pN} (hr : r + 5 ≤ 20) (hk : k < 4)
    (h5 : r ≤ 5 → 5 < r + 5 → k = 0) (hl : Lim bd (envOf s) k (t5 r) x) : Lim bd (envOf t) k (t5 r) x :=
  ⟨carried_t5_on (h.v hr hk h5) hl.c, by rw [vI_t5_on (h.v hr hk h5)]; exact hl.hi,
    by rw [vI_t5_on (h.v hr hk h5)]; exact hl.d⟩

theorem Chn.rkeep {s t : State} (h : RKeep s t) {r k : Nat} {x : Fin pN} (hr : r + 5 ≤ 20) (hk : k < 4)
    (h5 : r ≤ 5 → 5 < r + 5 → k = 0) (hl : Chn (envOf s) k (t5 r) x) : Chn (envOf t) k (t5 r) x :=
  ⟨by rw [vI_t5_on (h.v hr hk h5)]; exact hl.lo, by rw [vI_t5_on (h.v hr hk h5)]; exact hl.hi,
    by rw [vI_t5_on (h.v hr hk h5)]; exact hl.d⟩

theorem ChainOk.rkeep {s t : State} (h : RKeep s t) {p : ZP (Fin pN)}
    (hc : ChainOk (envOf s) (t5 10) (t5 15) p) : ChainOk (envOf t) (t5 10) (t5 15) p :=
  ⟨hc.x1.rkeep h (by decide) (by decide) (fun h' => absurd h' (by decide)),
    hc.y1.rkeep h (by decide) (by decide) (fun h' => absurd h' (by decide)),
    hc.y2.rkeep h (by decide) (by decide) (fun h' => absurd h' (by decide)),
    hc.z.rkeep h (by decide) (by decide) (fun h' => absurd h' (by decide)),
    hc.x2.rkeep h (by decide) (by decide) (fun h' => absurd h' (by decide))⟩

/-- The bounds of the first `N` registers are kept with the lanes they bound. -/
theorem envOK_regsN {N : Nat} {bt : BT} {s t : State} (hB : EnvOK s (bndsOf ((List.range N).map Loc.reg) bt))
    (hi : ∀ n, n < N → locIdx ((List.range N).map Loc.reg) (.reg n) = some n)
    (hr : ∀ r, r < N → ∀ k, k < 4 → (bt.get (r / 5) k).isSome = true → qv t (vreg r) k = qv s (vreg r) k) :
    EnvOK t (bndsOf ((List.range N).map Loc.reg) bt) := by
  refine envOK_of fun n l hl k hk b hb => ?_
  have hn : n < N ∧ l = .reg n := by
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
    obtain ⟨m, hm, rfl⟩ := hl
    obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.mp hm
    rw [List.length_range] at hlt
    rw [List.getElem_range] at e
    exact ⟨hlt, by rw [e]⟩
  obtain ⟨hn, rfl⟩ := hn
  have e : ints t (.reg n) k = ints s (.reg n) k := by
    show (qv t (vreg n) k).toInt = (qv s (vreg n) k).toInt
    rw [hr n hn k hk (by rw [hb]; rfl)]
  rw [e]
  have := hB.v n k hk
  simp only [bndsOf, hi n hn, bndAt, hb, Option.getD_some] at this
  exact this

/-- The bounds between the table's blocks, after an entry is stored. -/
theorem envOK_tab {s t : State} (hB : EnvOK s (bndsOf regs20 tabBT)) (h : RKeep s t) :
    EnvOK t (bndsOf regs20 tabBT) := by
  have key : ∀ k, k < 4 → (tabBT.get 1 k).isSome = true → k = 0 := by decide
  refine envOK_regsN (N := 20) hB (by decide) fun r hr k hk hb => h r hr k hk fun e => ?_
  subst e
  exact key k hk hb

/-- The bounds of an entry's registers, after it is stored. -/
theorem envOK_ent {s t : State} (hB : EnvOK s (bndsOf regs10 entBT)) (h : RKeep s t) :
    EnvOK t (bndsOf regs10 entBT) := by
  have key : ∀ k, k < 4 → (entBT.get 1 k).isSome = true → k = 0 := by decide
  refine envOK_regsN (N := 10) hB (by decide) fun r hr k hk hb => h r (by omega_using [hr]) k hk fun e => ?_
  subst e
  exact key k hk hb

/-- The registers of an entry's seven vectors, at their offsets. -/
def entRegs : List (Nat × VReg) :=
  [(0, vreg 0), (32, vreg 1), (64, vreg 2), (96, vreg 3), (128, vreg 4), (160, vreg 5), (192, vreg 9)]

/-- An entry's seven vectors stored where `rbp` is, at `o` of the working space. -/
theorem storeEnt_ok {s : State} {base : Addr} {size o : Nat} (hs : Scr s base size)
    (hp : s.gpr .rbp = base + BitVec.ofNat 64 o) (ho : o + 224 ≤ 8192) (hsize : 8192 ≤ size) :
    WP isa (.block storeEnt) s fun t =>
      t = { s with mem := t.mem } ∧ Unch base [(o, 224)] s.mem t.mem ∧
        (∀ i, i < 5 → ∀ k, k < 4 →
          t.mem.readW (base + BitVec.ofNat 64 (o + 32 * i + 8 * k)) 64 = qv s (vreg i) k) ∧
        (∀ k, k < 4 → t.mem.readW (base + BitVec.ofNat 64 (o + 160 + 8 * k)) 64 = qv s (vreg 5) k) ∧
        t.mem.readW (base + BitVec.ofNat 64 (o + 192 + 8 * 0)) 64 = qv s (vreg 9) 0 := by
  have hnw := hs.nowrap
  have hin : ∀ e ∈ entRegs, InRegions s.wr (base + BitVec.ofNat 64 (o + e.1)) 32 := by
    intro e he
    have : e.1 + 32 ≤ 224 := by
      simp only [entRegs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨_, hs.wr, hs.contains (by omega_using [ho, hsize, this]) (by decide)⟩
  refine WP.mono (evStores_ok .rbp base o entRegs s hp hin) fun t ht => ?_
  subst ht
  have hal : ∀ e ∈ entRegs.map fun e => (o + e.1, s.vy e.2), e.1 % 32 = o % 32 ∧ e.1 < 2 ^ 62 := by
    intro e he
    simp only [entRegs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_using [ho]
  have hpw : (entRegs.map fun e => (o + e.1, s.vy e.2)).Pairwise (fun a b => a.1 ≠ b.1) := by
    rw [List.pairwise_map]
    exact (by decide : entRegs.Pairwise (fun a b => a.1 ≠ b.1)).imp (fun h => by dsimp only; omega_using [h])
  refine ⟨rfl, ?_, fun i hi k hk => ?_, fun k hk => ?_, ?_⟩
  · exact wr32_unch base (by omega_using [ho]) _ s.mem (fun e he => by
      simp only [entRegs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_using [])
  · have hm : (o + 32 * i, s.vy (vreg i)) ∈ entRegs.map fun e => (o + e.1, s.vy e.2) := by
      rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> simp [entRegs]
    exact wr32_read base hk _ s.mem hal hpw _ _ hm
  · exact wr32_read base hk _ s.mem hal hpw _ _ (by simp [entRegs])
  · exact wr32_read base (by decide) _ s.mem hal hpw _ _ (by simp [entRegs])

/-- The entry in `ymm0`–`ymm9` stored where `rbp` is, at `TOFF + 200 a` of the working space, and `rbp`
at the next entry's place. -/
theorem putEnt_ok {s : State} {base : Addr} {size a : Nat} (ha : a < 8) (hs : Scr s base size) (hc : Ctx par s)
    (h10 : s.gpr .r10 = off base KB) (hp : s.gpr .rbp = off base (TOFF + 200 * a)) (hsize : 8192 ≤ size)
    {P : AP (Fin pN)} (hE : EntOk (envOf s) (t5 0) (t5 5) P) :
    WP isa (.block putEnt) s fun t =>
      Ctx par t ∧ RKeep s t ∧ LEnt t.mem (off base (TOFF + 200 * a)) P ∧
        t.gpr .rbp = off base (TOFF + 200 * (a + 1)) ∧ (∀ r, r ≠ .rbp → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ Unch base [(TOFF + 200 * a, 224)] s.mem t.mem := by
  have hnw := hs.nowrap
  have hto : TOFF = 2752 := rfl
  have hkb : KB = 6432 := rfl
  rw [putEnt, WP.block_append_iff]
  refine WP.mono (pack_ok hc) fun u ⟨eu, um, hru, h5u⟩ => ?_
  have ug : u.gpr = s.gpr := by rw [← eu]; rfl
  have uwr : u.wr = s.wr := by rw [← eu]; rfl
  have urd : u.rd = s.rd := by rw [← eu]; rfl
  have hsu : Scr u base size := ⟨by rw [ug]; exact hs.rdi, by rw [uwr]; exact hs.wr, hnw⟩
  rw [WP.block_append_iff]
  refine WP.mono (storeEnt_ok (o := TOFF + 200 * a) hsu (by rw [ug]; exact hp) (by omega_using [ha, hto]) hsize)
    fun v ⟨ev, uv, m1, m2, m3⟩ => ?_
  have vg : v.gpr = s.gpr := by rw [ev]; exact ug
  have vrd : v.rd = s.rd := by rw [ev]; exact urd
  have vwr : v.wr = s.wr := by rw [ev]; exact uwr
  have vq (r k : Nat) : qv v (vreg r) k = qv u (vreg r) k := by rw [ev]; rfl
  have sv : Unch base [(TOFF + 200 * a, 224)] s.mem v.mem := by rw [← um]; exact uv
  have hcv : Ctx par v := ctx_mem hc vg vrd vwr fun i hi => by
    rw [par_cst_length] at hi
    have := sv.word (d := KB + 8 * i) (fun w hw => by
      rw [List.mem_singleton] at hw; subst hw; exact Or.inr (by dsimp only; omega_using [ha, hto, hkb])) (by omega_using [hkb, hi])
    simp only [Mont.word, off] at this
    rw [h10, off, Offset.add_add]
    exact this
  refine WP.mono (WP.skeep rfl (add200_ok v)) fun t ⟨tp, kt⟩ => ?_
  refine ⟨ctx_skeep hcv kt (by decide) (by decide) (fun r d hr hd => by
      rw [List.mem_singleton] at hr; subst hr
      rw [lim_other (by decide) (by decide) (by decide)] at hd; omega),
    fun r hr k hk h => ?_, ?_, ?_, fun r hr => ?_, kt.rd.trans vrd, kt.wr.trans vwr, by rw [kt.mem]; exact sv⟩
  · rw [kt.qv, vq]
    by_cases h' : r = 5
    · subst h'; rw [h rfl]; exact h5u 0 (by decide)
    · exact hru r hr h' k hk
  · rw [kt.mem]
    refine lent_of hE (fun i hi k hk => ?_) (fun k hk => ?_) ?_
    · rw [off, Offset.add_add, ← Nat.add_assoc, m1 i hi k hk]
      exact hru i (by omega_using [hi]) (by omega_using [hi]) k hk
    · rw [off, Offset.add_add, ← Nat.add_assoc, m2 k hk]
      exact h5u k hk
    · rw [off, Offset.add_add, ← Nat.add_assoc, m3]
      exact hru 9 (by decide) (by decide) 0 (by decide)
  · rw [tp, vg, hp, off, off, Offset.add_add, show TOFF + 200 * a + 200 = TOFF + 200 * (a + 1) by omega_using []]
  · rw [kt.gpr r (by rw [List.mem_singleton]; exact hr), vg]

/-- `2 Q` and `[2 k + 1] Q` with one `Z`, after entry `k` of the table of the point `(X, Y)`: what `dblu`
leaves of `Q`'s entry, and then what each `zaddu` does. -/
def chainZ (X Y : Fin pN) : Nat → ZP (Fin pN)
  | 0 => (⟨(entQN X Y 1 false 0 0 0).ex, (entQN X Y 1 false 0 0 0).ey, (entQN X Y 1 false 0 0 0).ezz⟩ :
      DP (Fin pN)).out
  | k + 1 => ⟨(chainZ X Y k).W1, (chainZ X Y k).A1, (chainZ X Y k).x3, (chainZ X Y k).Ev - (chainZ X Y k).A1,
      (chainZ X Y k).z3⟩

/-- The triples of the table of the odd multiples of the point `(X, Y)`. -/
def tabQ (X Y : Fin pN) : Nat → Fin pN × Fin pN × Fin pN
  | 0 => (X, Y, 1)
  | a + 1 => (4 * (chainZ X Y a).x3, 8 * ((chainZ X Y a).Ev - (chainZ X Y a).A1), 2 * (chainZ X Y a).z3)

/-- The pairs between the table's blocks are `2 Q` and the odd multiples of `Q`. -/
theorem chainZ_pts (hC : Law Cv) (hO : PrimeOrder Cv) (ha : AM3 Cv) {Q : Spec.Weierstrass.Point Cv}
    (hQ : Spec.Weierstrass.onCurve Cv Q = true) {X Y : Fin pN} (hJ : InvJ Cv X Y 1 Q) :
    ∀ k, k ≤ 7 → InvJ Cv (chainZ X Y k).x1 (chainZ X Y k).y1 (chainZ X Y k).z (Spec.Weierstrass.mul 2 Q) ∧
      InvJ Cv (chainZ X Y k).x2 (chainZ X Y k).y2 (chainZ X Y k).z (Spec.Weierstrass.mul (2 * k + 1) Q) ∧
      (chainZ X Y k).z ≠ 0
  | 0, _ => by
    have hQ0 : Q ≠ .infinity := fun e => one_ne ((hJ.z_zero_iff hC).mpr e)
    obtain ⟨hi, hy2⟩ := entQ_inv hC hJ false 0 0 0
    have h2z : 2 * (entQ X Y 1 false 0 0 0).ez = 1 := by
      have := kapC16
      simp only [entQ]
      grind
    have dp := dp_pts hC hO ha (by decide) hQ hQ0 hi h2z hy2
    rw [← entQ_zz X Y 1 false 0 0 0] at dp
    obtain ⟨d1, d2, d3⟩ := dp
    refine ⟨d1, ?_, d3⟩
    rw [Nat.mul_zero, Nat.zero_add, mul_one_pt]
    exact d2
  | k + 1, hk => by
    have hQ0 : Q ≠ .infinity := fun e => one_ne ((hJ.z_zero_iff hC).mpr e)
    obtain ⟨j1, j2, hz⟩ := chainZ_pts hC hO ha hQ hJ k (by omega_using [hk])
    obtain ⟨js, jd, hz3⟩ := zp_pts hC hO ha (by decide) hQ hQ0 (k := k) (by omega_using [hk]) j1 j2 hz
    exact ⟨jd, js, hz3⟩

/-- The table's triples are those of `Q`'s odd multiples. -/
theorem tabQ_pts (hC : Law Cv) (hO : PrimeOrder Cv) (ha : AM3 Cv) {Q : Spec.Weierstrass.Point Cv}
    (hQ : Spec.Weierstrass.onCurve Cv Q = true) {X Y : Fin pN} (hJ : InvJ Cv X Y 1 Q) : QPts (tabQ X Y) 8 Q := by
  intro a ha'
  cases a with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_add, mul_one_pt]
    exact hJ
  | succ k =>
    have hQ0 : Q ≠ .infinity := fun e => one_ne ((hJ.z_zero_iff hC).mpr e)
    obtain ⟨j1, j2, hz⟩ := chainZ_pts hC hO ha hQ hJ k (by omega_using [ha'])
    obtain ⟨js, -, -⟩ := zp_pts hC hO ha (by decide) hQ hQ0 (k := k) (by omega_using [ha']) j1 j2 hz
    have e1 : 4 * (chainZ X Y k).x3 * (1 * 1) = (chainZ X Y k).x3 * (2 * 2) := by grind
    have e2 : 8 * ((chainZ X Y k).Ev - (chainZ X Y k).A1) * (1 * 1 * 1) =
        ((chainZ X Y k).Ev - (chainZ X Y k).A1) * (2 * 2 * 2) := by grind
    have e3 : 2 * (chainZ X Y k).z3 * 1 = (chainZ X Y k).z3 * 2 := by grind
    exact js.rescale hC (l := 2) (m := 1) two_ne one_ne e1 e2 e3

/-- After entry `k` of the table of the point `(X, Y)`: the entries so far are kept as limbs, `rbp` is at
the next one's place, and the registers hold `2 Q` and `[2 k + 1] Q` with one `Z`. -/
structure TabInv (base : Addr) (size : Nat) (X Y : Fin pN) (s₀ : State) (k : Nat) (t : State) : Prop where
  scr : Scr t base size
  ctx : Ctx par t
  env : EnvOK t (bndsOf regs20 tabBT)
  r10 : t.gpr .r10 = off base KB
  rbp : t.gpr .rbp = off base (TOFF + 200 * (k + 1))
  keep : TKeep base s₀ t
  tab : LTabN (tabQ X Y) (k + 1) t.mem base
  chain : ChainOk (envOf t) (t5 10) (t5 15) (chainZ X Y k)

theorem tkeep_store {base : Addr} {s t : State} {a : Nat} (ha : a < 8) (hg : ∀ r, r ≠ .rbp → t.gpr r = s.gpr r)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hu : Unch base [(TOFF + 200 * a, 224)] s.mem t.mem) :
    TKeep base s t :=
  ⟨fun r hr => hg r fun e => hr (by rw [e]; decide), hrd, hwr, hu.cover fun w hw => by
    rw [List.mem_singleton] at hw; subst hw
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only; omega_using [], by dsimp only; omega_using [ha]⟩⟩

/-- The next odd multiple of `Q`, stored as entry `k + 1`, and the count of those left. -/
theorem tabStep_ok {X Y : Fin pN} {s₀ s : State} {base : Addr} {size k j : Nat} (hsize : 8192 ≤ size) (hk : k ≤ 6)
    (hj : 1 ≤ j) (hj' : j ≤ 7) (h : TabInv base size X Y s₀ k s) (hax : s.gpr .rax = BitVec.ofNat 64 j) :
    WP isa (.block vtabStep) s fun t =>
      (TabInv base size X Y s₀ (k + 1) t ∧ t.gpr .rax = BitVec.ofNat 64 (j - 1)) ∧
        t.zf = some (decide (j - 1 = 0)) := by
  have hto : TOFF = 2752 := rfl
  have hsb : cfg.sbase = 5056 := rfl
  have hsl : slotsLen = 288 := rfl
  rw [vtabStep, WP.block_append_iff]
  refine WP.mono (zaddu_ok h.ctx h.env h.chain) fun v ⟨hcv, kv, hBv, zo⟩ => ?_
  have vdi : v.gpr .rdi = base := by rw [kv.gpr, h.scr.rdi]
  have hsv : Scr v base size := ⟨vdi, by rw [kv.wr]; exact h.scr.wr, h.scr.nowrap⟩
  have hE : EntOk (envOf v) (t5 0) (t5 5)
      (entQN (tabQ X Y (k + 1)).1 (tabQ X Y (k + 1)).2.1 (tabQ X Y (k + 1)).2.2 false 0 0 0) := by
    simp only [tabQ]
    rw [entQN_virt]
    exact ⟨zo.ent.ezz, zo.ent.ex, zo.ent.ez, zo.ent.ey, zo.ent.ezzz⟩
  rw [WP.block_append_iff]
  refine WP.mono (putEnt_ok (a := k + 1) (by omega_using [hk]) hsv hcv (by rw [kv.gpr]; exact h.r10)
    (by rw [kv.gpr]; exact h.rbp) hsize hE) fun w ⟨hcw, rk, le, wp, wg, wrd, wwr, uw⟩ => ?_
  have kvm : Unch base [(cfg.sbase, slotsLen)] s.mem v.mem := by
    have := kv.mem; rw [h.scr.rdi] at this; exact this
  have ks : TKeep base s w := (TKeep.of_kept h.scr.rdi kv).trans (tkeep_store (by omega_using [hk]) wg wrd wwr uw)
  have wax : w.gpr .rax = BitVec.ofNat 64 j := by rw [wg _ (by decide), kv.gpr]; exact hax
  refine WP.mono (WP.skeep rfl (decRax_ok w hj hj' wax)) fun t ⟨⟨tax, tz⟩, kt⟩ => ?_
  refine ⟨⟨⟨⟨by rw [kt.gpr .rdi (by decide), wg _ (by decide)]; exact vdi, by rw [kt.wr, wwr]; exact hsv.wr,
      h.scr.nowrap⟩,
    ctx_skeep hcw kt (by decide) (by decide) (fun r d hr hd => by
      rw [List.mem_singleton] at hr; subst hr
      rw [lim_other (by decide) (by decide) (by decide)] at hd; omega),
    envOK_skeep kt (by decide) (envOK_tab hBv rk),
    by rw [kt.gpr .r10 (by decide), wg _ (by decide), kv.gpr]; exact h.r10,
    by rw [kt.gpr .rbp (by decide)]; exact wp, (h.keep.trans ks).trans (TKeep.of_skeep kt), fun a ha' => ?_, ?_⟩,
    tax⟩, tz⟩
  · rw [kt.mem]
    by_cases e : a = k + 1
    · subst e
      exact le
    · refine (h.tab a (by omega_using [ha', e])).unch (kvm.trans uw) (fun x hx => ?_) (by omega_using [hk, hto, ha'])
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> dsimp only <;> omega_arith
  · have c := zo.chain.rkeep rk
    exact ⟨⟨by rw [vI_t5_congr kt.v]; exact c.x1.lo, by rw [vI_t5_congr kt.v]; exact c.x1.hi,
        by rw [vI_t5_congr kt.v]; exact c.x1.d⟩,
      ⟨by rw [vI_t5_congr kt.v]; exact c.y1.lo, by rw [vI_t5_congr kt.v]; exact c.y1.hi,
        by rw [vI_t5_congr kt.v]; exact c.y1.d⟩,
      ⟨by rw [vI_t5_congr kt.v]; exact c.y2.lo, by rw [vI_t5_congr kt.v]; exact c.y2.hi,
        by rw [vI_t5_congr kt.v]; exact c.y2.d⟩, c.z.congr kt.v, c.x2.congr kt.v⟩

/-- The table of `Q`'s odd multiples as limbs, from `Q`'s affine coordinates in `c.K.P`. -/
theorem vtab_ok {c : Joint.Cfg} {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hc : Ctx par s)
    (hB : EnvOK s stB) (h10 : s.gpr .r10 = off base KB) (hsize : 8192 ≤ size)
    (hpx : c.K.P.x + 96 ≤ TOFF) (hpy : c.K.P.y + 64 ≤ TOFF) {X Y : Fin pN}
    (hx : toM pN (2 ^ 256) (wordsVal s.mem base c.K.P.x 4) = X)
    (hy : toM pN (2 ^ 256) (wordsVal s.mem base c.K.P.y 4) = Y) :
    WP isa (vtab c) s fun t => Ctx par t ∧ TKeep base s t ∧ LTab (tabQ X Y) t.mem base := by
  have hnw := hs.nowrap
  have hlo : par.lo = 5056 := rfl
  have hwin : par.win = 5920 := rfl
  have hto : TOFF = 2752 := rfl
  have hsb : cfg.sbase = 5056 := rfl
  have hsl : slotsLen = 288 := rfl
  rw [vtab]
  apply WP.seq
  rw [vtabHead, WP.block_append_iff]
  refine WP.mono (WP.skeep rfl (ptr3_ok s (e := c.K.P.x) (z := c.K.P.y) (p := TOFF) (by omega_using [hpx, hto]) (by omega_using [hpy, hto])
    (by omega_using [hto]))) fun u ⟨⟨ucx, udx, ubp⟩, ku⟩ => ?_
  rw [hs.rdi] at ucx udx ubp
  have hcu : Ctx par u := by
    refine ctx_skeep hc ku (by decide) (by decide) fun r d hr hd => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have hd' : d + 32 ≤ 96 := hd
      rw [ucx, Offset.add_add, hs.rdi]
      exact ⟨⟨_, List.mem_append_right _ hs.wr, hs.contains (by omega_using [hsize, hpx, hto, hd']) (by decide)⟩,
        Offset.sep base (Or.inl (by omega_using [hpx, hlo, hto, hd'])) (by omega_using [hpx, hto, hd']) (by omega_using [hlo, hwin])⟩
    · have hd' : d + 32 ≤ 64 := hd
      rw [udx, Offset.add_add, hs.rdi]
      exact ⟨⟨_, List.mem_append_right _ hs.wr, hs.contains (by omega_using [hsize, hpy, hto, hd']) (by decide)⟩,
        Offset.sep base (Or.inl (by omega_using [hpy, hlo, hto, hd'])) (by omega_using [hpy, hto, hd']) (by omega_using [hlo, hwin])⟩
    · rw [lim_other (by decide) (by decide) (by decide)] at hd; omega
  have hBu : EnvOK u stB := envOK_skeep ku (by decide) hB
  rw [WP.block_append_iff]
  refine WP.mono (tabG_ok hcu hBu) fun v ⟨hcv, kv, hBv, c0, c1, c2, c3, cb⟩ => ?_
  have w (r : Reg) (hr : uBase r = true) (d x : Nat) (hx : u.gpr r = off base x) :
      wv (envOf u) (.ld r d) = (wordsVal s.mem base (x + d) 4 : Nat) := by
    rw [wv_ld u r hr d, hx, wordsVal_off, ku.mem]
  have hEv := entOk_G c0 c1 c2 c3 cb (w .rcx rfl 0 _ ucx) (w .rdx rfl 0 _ udx) hx hy false 0 0 0
  have udi : u.gpr .rdi = base := (ku.gpr .rdi (by decide)).trans hs.rdi
  have vdi : v.gpr .rdi = base := by rw [kv.gpr, udi]
  have v10 : v.gpr .r10 = off base KB := by rw [kv.gpr, ku.gpr .r10 (by decide), h10]
  have hsv : Scr v base size := ⟨vdi, by rw [kv.wr, ku.wr]; exact hs.wr, hnw⟩
  rw [WP.block_append_iff]
  refine WP.mono (putEnt_ok (a := 0) (by decide) hsv hcv v10 (by rw [kv.gpr]; exact ubp) hsize hEv)
    fun t ⟨hct, rk, le, tp, tg, trd, twr, ut⟩ => ?_
  have hst : Scr t base size := ⟨by rw [tg _ (by decide)]; exact vdi, by rw [twr]; exact hsv.wr, hnw⟩
  have kst : TKeep base s t :=
    ((TKeep.of_skeep ku).trans (TKeep.of_kept udi kv)).trans (tkeep_store (by decide) tg trd twr ut)
  rw [WP.block_append_iff]
  refine WP.mono (dblu_ok hct (envOK_ent hBv rk)
    (p := ⟨(entQN X Y 1 false 0 0 0).ex, (entQN X Y 1 false 0 0 0).ey, (entQN X Y 1 false 0 0 0).ezz⟩)
    (hEv.zz.rkeep rk (by decide) (by decide) (fun _ h' => absurd h' (by decide)))
    (hEv.x.rkeep rk (by decide) (by decide) (fun _ h' => absurd h' (by decide)))
    (hEv.y.rkeep rk (by decide) (by decide) (fun _ h' => absurd h' (by decide))))
    fun x ⟨hcx, kx, hBx, hch⟩ => ?_
  have xdi : x.gpr .rdi = base := by rw [kx.gpr]; exact hst.rdi
  refine WP.mono (WP.skeep rfl (cnt7_ok x)) fun y ⟨yax, ky⟩ => ?_
  have h1 : TabInv base size X Y s 0 y := by
    refine ⟨⟨(ky.gpr .rdi (by decide)).trans xdi, by rw [ky.wr, kx.wr]; exact hst.wr, hnw⟩,
      ctx_skeep hcx ky (by decide) (by decide) (fun r d hr hd => by
        rw [List.mem_singleton] at hr; subst hr
        rw [lim_other (by decide) (by decide) (by decide)] at hd; omega),
      envOK_skeep ky (by decide) hBx, by rw [ky.gpr .r10 (by decide), kx.gpr, tg _ (by decide)]; exact v10,
      by rw [ky.gpr .rbp (by decide), kx.gpr]; exact tp,
      (kst.trans (TKeep.of_kept hst.rdi kx)).trans (TKeep.of_skeep ky), fun a ha' => ?_, ?_⟩
    · have ea : a = 0 := by omega_using [ha']
      subst ea
      have kxm := kx.mem
      rw [hst.rdi] at kxm
      rw [ky.mem]
      exact le.unch kxm (fun w hw => by
        rw [List.mem_singleton] at hw; subst hw; exact Or.inl (by dsimp only; omega_using [hto, hsb])) (by omega_using [hto])
    · exact ⟨⟨by rw [vI_t5_congr ky.v]; exact hch.x1.lo, by rw [vI_t5_congr ky.v]; exact hch.x1.hi,
          by rw [vI_t5_congr ky.v]; exact hch.x1.d⟩,
        ⟨by rw [vI_t5_congr ky.v]; exact hch.y1.lo, by rw [vI_t5_congr ky.v]; exact hch.y1.hi,
          by rw [vI_t5_congr ky.v]; exact hch.y1.d⟩,
        ⟨by rw [vI_t5_congr ky.v]; exact hch.y2.lo, by rw [vI_t5_congr ky.v]; exact hch.y2.hi,
          by rw [vI_t5_congr ky.v]; exact hch.y2.d⟩, hch.z.congr ky.v, hch.x2.congr ky.v⟩
  -- the seven entries after the first
  refine countLoop_ok (Inv := fun j t => TabInv base size X Y s (7 - j) t ∧ t.gpr .rax = BitVec.ofNat 64 j)
    (n := 7) (fun j a hj1 hj ⟨hi, hax⟩ => ?_) (fun t ht => ⟨ht.1.ctx, ht.1.keep, ht.1.tab⟩) (by decide) ⟨h1, yax⟩
  have e : 7 - j + 1 = 7 - (j - 1) := by omega_using [hj1, hj]
  rw [← e]
  exact tabStep_ok hsize (by omega_using [hj1]) hj1 hj hi hax

/-- `rcx` at the limbs of the odd multiple of `Q` whose magnitude is in `r8`, and `rdx` at its fourth vector. -/
theorem entryT_ok (s : State) {base : Addr} {a : Nat} (hb : s.gpr .rdi = base) (h8 : s.gpr .r8 = BitVec.ofNat 64 a)
    (ha : 1 ≤ a) (ha' : a ≤ 15) :
    WP isa (.block entryT) s fun t =>
      (t.gpr .rcx = off base (TOFF + 100 * (a - 1)) ∧ t.gpr .rdx = off base (TOFF + 100 * (a - 1) + 96)) ∧
        Keeps [.rax, .rcx, .rdx] s t := by
  have e1 : (BitVec.ofNat 32 (TOFF - 100)).signExtend 64 = BitVec.ofNat 64 (TOFF - 100) := by decide
  have e2 : (96 : BitVec 32).signExtend 64 = BitVec.ofNat 64 96 := by decide
  have key : ∀ a, a ≤ 15 → BitVec.ofNat 64 a <<< 2 + (BitVec.ofNat 64 a <<< 2) <<< 3 +
      ((BitVec.ofNat 64 a <<< 2) <<< 3) <<< 1 = BitVec.ofNat 64 (100 * a) := by decide
  apply WP.of_runBlock
  simp only [entryT, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift, e1, e2,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, Option.map_some, Option.bind_some, ite_true,
    ite_false, reduceCtorEq, h8, hb, show 1 ≤ 2 ∧ 2 ≤ 63 from by decide, show 1 ≤ 3 ∧ 3 ≤ 63 from by decide,
    show 1 ≤ 1 ∧ 1 ≤ 63 from by decide, and_self, Option.some.injEq, exists_eq_left']
  have hc : BitVec.ofNat 64 a <<< 2 + (BitVec.ofNat 64 a <<< 2) <<< 3 + ((BitVec.ofNat 64 a <<< 2) <<< 3) <<< 1 +
      base + BitVec.ofNat 64 (TOFF - 100) = off base (TOFF + 100 * (a - 1)) := by
    rw [key a ha', BitVec.add_comm _ base, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    simp only [TOFF]; omega_using [ha]
  refine ⟨⟨hc, ?_⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hc, off, off, BitVec.add_assoc, ← BitVec.ofNat_add]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `rdx` moved on to the entry's sixth vector. -/
theorem add64_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 64)]) s fun t =>
      t.gpr .rdx = s.gpr .rdx + BitVec.ofNat 64 64 ∧ Keeps [.rdx] s t := by
  have e : (64 : BitVec 32).signExtend 64 = BitVec.ofNat 64 64 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, e, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, Option.bind_some, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The entry of a digit of `Q`'s scalar that is not zero: in `ymm20`–`ymm29`, with the mask of its
sign at `r9`, from the limbs of the digit's multiple of `Q`. -/
theorem qEntry_ok {s : State} {base : Addr} {size : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hc : Ctx par s) (hB : EnvOK s stB) (h8 : s.gpr .r8 = b.setWidth 64)
    (ha : 1 ≤ qMag b) (ha' : qMag b ≤ 15) (hsize : 8192 ≤ size) {X Y Z : Fin pN}
    (hE : LEnt s.mem (off base (TOFF + 100 * (qMag b - 1))) (entQN X Y Z false 0 0 0)) :
    WP isa (.seq (.seq (.block [.alu .cmp .r8 (.imm 128)]) (.ite .b (.block (signPtr false))
      (.block (([.mov32 .rax (.imm 256), .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax)] : List Instr) ++ signPtr true))))
      (.seq (.block (entryT ++ loadAPieces.flatten))
        (.block (([.alu .add .rdx (.imm 64)] : List Instr) ++ loadBPieces.flatten)))) s fun t =>
      Ctx par t ∧ EnvOK t addB ∧ SgnOk (envOf t) sgnT.l0 (!decide (b.toNat < 128)) ∧
        (∀ xn un z, AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) xn un z →
          AccOk (envOf t) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) ∧
        (∀ xn un z, EntOk (envOf t) (t5 20) (t5 25) (entQN X Y Z (!decide (b.toNat < 128)) xn un z)) ∧
        t.gpr .r11 = s.gpr .r11 ∧ LKeep s t := by
  have hnw := hs.nowrap
  have hlo : par.lo = 5056 := rfl
  have hwin : par.win = 5920 := rfl
  have hto : TOFF = 2752 := rfl
  apply WP.seq
  refine WP.mono (qSign_ok s h8) fun u ⟨u8, u9', ku⟩ => ?_
  have u9 : u.gpr .r9 = s.gpr .r10 +
      BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if (!decide (b.toNat < 128)) = true then 3 else 0))) := by
    rw [u9']
    cases decide (b.toNat < 128) <;> rfl
  have udi : u.gpr .rdi = base := (ku.gpr .rdi (by decide)).trans hs.rdi
  have kb : ∀ neg : Bool, 32 * poolLit.idxOf (K4.lanes (if neg = true then 3 else 0)) + 32 ≤ 8 * par.cst.length := by
    decide +kernel
  -- what the blocks read through `r9` after the sign
  have h9 (e : State) (ke : SKeep [.rax, .rcx, .rdx, .rbp, .r8, .r9] s e)
      (e9 : e.gpr .r9 = s.gpr .r10 +
        BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if (!decide (b.toNat < 128)) = true then 3 else 0)))) (d : Nat)
      (hd : d + 32 ≤ 32) : InRegions (s.rd ++ s.wr) (e.gpr .r9 + BitVec.ofNat 64 d) 32 ∧
        Mem.Sep (e.gpr .r9 + BitVec.ofNat 64 d) 32 (s.gpr .rdi + BitVec.ofNat 64 par.lo) (par.win - par.lo) := by
    have hk := kb (!decide (b.toNat < 128))
    rw [e9, Offset.add_add]
    exact ⟨hc.crd _ (by omega_using [hd, hk]), hc.csep _ (by omega_using [hd, hk])⟩
  have hoff : TOFF + 100 * (qMag b - 1) + 200 ≤ 5056 := by omega_using [ha', hto]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.skeep rfl (entryT_ok u udi u8 ha ha')) fun e ⟨⟨ecx, edx⟩, ke⟩ => ?_
  have kse : SKeep [.rax, .rcx, .rdx, .rbp, .r8, .r9] s e := (ku.mono (by decide)).trans (ke.mono (by decide))
  have e9 := (ke.gpr .r9 (by decide)).trans u9
  have hce : Ctx par e := by
    refine ctx_skeep hc kse (by decide) (by decide) fun r d hr hd => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [lim_other (by decide) (by decide) (by decide)] at hd; omega
    · have hd' : d + 32 ≤ 96 := hd
      rw [ecx, Offset.add_add, hs.rdi]
      exact ⟨⟨_, List.mem_append_right _ hs.wr, hs.contains (by omega_using [ha', hsize, hto, hd']) (by decide)⟩,
        Offset.sep base (Or.inl (by omega_using [ha', hlo, hto, hd'])) (by omega_using [ha', hto, hd']) (by omega_using [hlo, hwin])⟩
    · have hd' : d + 32 ≤ 64 := hd
      rw [edx, Offset.add_add, hs.rdi]
      exact ⟨⟨_, List.mem_append_right _ hs.wr, hs.contains (by omega_using [ha', hsize, hto, hd']) (by decide)⟩,
        Offset.sep base (Or.inl (by omega_using [ha', hlo, hto, hd'])) (by omega_using [ha', hto, hd']) (by omega_using [hlo, hwin])⟩
    · rw [lim_other (by decide) (by decide) (by decide)] at hd; omega
    · rw [lim_other (by decide) (by decide) (by decide)] at hd; omega
    · exact h9 e kse e9 d hd
  have hBe : EnvOK e stB := envOK_skeep kse (by decide) hB
  have hEe : LEnt e.mem (off base (TOFF + 100 * (qMag b - 1))) (entQN X Y Z false 0 0 0) := by
    rw [kse.mem]; exact hE
  refine WP.mono (loadA_ok hce hBe (by rw [ecx]; exact (BitVec.add_zero _).symm)
    (by rw [edx, off, off, BitVec.add_assoc, ← BitVec.ofNat_add]) hEe) fun f ⟨hcf, kf, hBf, hacf, a0, a1, a2, a3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.skeep rfl (add64_ok f)) fun g ⟨gdx, kg⟩ => ?_
  have fdi : f.gpr .rdi = base := by rw [kf.gpr, kse.gpr .rdi (by decide), hs.rdi]
  have gdx' : g.gpr .rdx = off base (TOFF + 100 * (qMag b - 1)) + BitVec.ofNat 64 160 := by
    rw [gdx, kf.gpr, edx, off, off, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  have hcg : Ctx par g := by
    refine ctx_skeep hcf kg (by decide) (by decide) fun r d hr hd => ?_
    rw [List.mem_singleton] at hr; subst hr
    have hd' : d + 32 ≤ 64 := hd
    rw [gdx', off, Offset.add_add, Offset.add_add, fdi, kf.rd, kf.wr, kse.rd, kse.wr]
    exact ⟨⟨_, List.mem_append_right _ hs.wr, hs.contains (by omega_using [ha', hsize, hto, hd']) (by decide)⟩,
      Offset.sep base (Or.inl (by omega_using [ha', hlo, hto, hd'])) (by omega_using [ha', hto, hd']) (by omega_using [hlo, hwin])⟩
  have hBg := envOK_skeep kg (by decide) hBf
  have hEg : LEnt g.mem (off base (TOFF + 100 * (qMag b - 1))) (entQN X Y Z false 0 0 0) := by
    rw [kg.mem]
    have hu := kf.mem
    rw [kse.gpr .rdi (by decide), hs.rdi] at hu
    exact hEe.unch hu (fun w hw => by
      rw [List.mem_singleton] at hw; subst hw; exact Or.inl hoff) (by omega_using [ha', hto])
  refine WP.mono (loadB_ok hcg hBg gdx' hEg) fun t ⟨hct, kt, hEt, hact, hta, hb⟩ => ?_
  have t9 : t.gpr .r9 = t.gpr .r10 +
      BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if (!decide (b.toNat < 128)) = true then 3 else 0))) := by
    rw [kt.gpr, kg.gpr .r9 (by decide), kg.gpr .r10 (by decide), kf.gpr, e9, kse.gpr .r10 (by decide)]
  have hm := sgn_m hct (!decide (b.toNat < 128)) t9
  exact ⟨hct, envOK_sgn hEt hm, sgnOk_of hm,
    fun xn un z h => hact xn un z ((hacf xn un z (h.congr kse.v)).congr kg.v),
    fun xn un z => ⟨hta 0 (by decide) _ (a0.congr kg.v), hta 1 (by decide) _ (a1.congr kg.v),
      hta 2 (by decide) _ (a2.congr kg.v), hta 3 (by decide) _ (a3.congr kg.v), hb⟩,
    by rw [kt.gpr, kg.gpr .r11 (by decide), kf.gpr, kse.gpr .r11 (by decide)],
    (((LKeep.of_skeep kse).trans (LKeep.of_kept kf)).trans (LKeep.of_skeep kg)).trans (LKeep.of_kept kt)⟩

/-! ### The entry added, or the accumulator set -/

/-- Whether a register is zero. -/
theorem test_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .test r (.reg r)]) s fun t => t.zf = some (s.gpr r == 0) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.zf_arithFlags, BitVec.and_self, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- `r11` set to one. -/
theorem flag_ok (s : State) :
    WP isa (.block [.mov32 .r11 (.imm 1)]) s fun t => t.gpr .r11 = 1 ∧ Keeps [.r11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, RegUpd.gpr_setReg,
    Option.map_some, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem entQN_zz (X Y Z : Fin pN) (neg : Bool) (xn un z : Fin pN) :
    (entQN X Y Z neg xn un z).ezz = (entQN X Y Z neg xn un z).ez * (entQN X Y Z neg xn un z).ez := by
  have := kap16
  simp only [entQN]
  grind

/-- The accumulator of the vectors: not set yet (`r11` zero), or standing for a triple. -/
def AccSt (s : State) : Option (Fin pN × Fin pN × Fin pN) → Prop
  | none => s.gpr .r11 = 0
  | some a => s.gpr .r11 = 1 ∧ AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) a.1 a.2.1 a.2.2

/-- The accumulator after the entry of `(X, Y, Z)`, or of its negative. -/
def accStep (X Y Z : Fin pN) (neg : Bool) : Option (Fin pN × Fin pN × Fin pN) → Fin pN × Fin pN × Fin pN
  | none => ((entQN X Y Z neg 0 0 0).ex,
      if neg then 0 - (entQN X Y Z neg 0 0 0).ey else (entQN X Y Z neg 0 0 0).ey, (entQN X Y Z neg 0 0 0).ez)
  | some a => ((entQN X Y Z neg a.1 a.2.1 a.2.2).X3, (entQN X Y Z neg a.1 a.2.1 a.2.2).Un,
      (entQN X Y Z neg a.1 a.2.1 a.2.2).Z3)

/-- The entry in `ymm20`–`ymm29` added to the accumulator, or the accumulator set to it. -/
theorem addOrSet_ok {s : State} (hc : Ctx par s) (hB : EnvOK s addB) {X Y Z : Fin pN} {neg : Bool}
    (hs : SgnOk (envOf s) sgnT.l0 neg)
    (he : ∀ xn un z, EntOk (envOf s) (t5 20) (t5 25) (entQN X Y Z neg xn un z))
    {acc : Option (Fin pN × Fin pN × Fin pN)} (ha : AccSt s acc) :
    WP isa addOrSet s fun t =>
      Ctx par t ∧ EnvOK t stB ∧ AccSt t (some (accStep X Y Z neg acc)) ∧ LKeep s t := by
  rw [addOrSet]
  apply WP.seq
  refine WP.mono (WP.skeep rfl (test_ok s .r11)) fun u ⟨hz, ku⟩ => ?_
  have hcu : Ctx par u := ctx_skeep hc ku (by decide) (by decide) (fun _ _ hr => absurd hr List.not_mem_nil)
  have hBu : EnvOK u addB := by
    refine ⟨fun r k hk => by rw [ku.v]; exact hB.v r k hk, fun b d k hk => ?_⟩
    rw [ku.m List.not_mem_nil]; exact hB.m b d k hk
  have hsu : SgnOk (envOf u) sgnT.l0 neg := by
    refine ⟨hs.b, ?_, ?_, ?_, ?_⟩
    · exact (ku.m (b := .r9) List.not_mem_nil 0 0).trans hs.s0
    · exact (ku.m (b := .r9) List.not_mem_nil 0 1).trans hs.s1
    · exact (ku.m (b := .r9) List.not_mem_nil 0 2).trans hs.s2
    · exact (ku.m (b := .r9) List.not_mem_nil 0 3).trans hs.s3
  have heu := fun xn un z => (he xn un z).congr ku.v
  cases acc with
  | none =>
    have h0 : s.gpr .r11 = 0 := ha
    refine WP.ite true (by show u.zf = _; rw [hz, h0]; rfl) (fun _ => ?_) (fun h => nomatch h)
    rw [WP.block_append_iff]
    have e := heu 0 0 0
    refine WP.mono (set_ok hcu hBu (p := entQN X Y Z neg 0 0 0) (by rw [← entQN_zz]; exact e.zz) e.x e.z e.y hsu)
      fun v ⟨hcv, kv, hBv, hav⟩ => ?_
    refine WP.mono (WP.skeep rfl (flag_ok v)) fun t ⟨ht, kt⟩ => ?_
    exact ⟨ctx_skeep hcv kt (by decide) (by decide)
        (fun b d hb hd => by
          rw [List.mem_singleton] at hb; subst hb
          rw [lim_other (by decide) (by decide) (by decide)] at hd; omega),
      envOK_skeep kt (by decide) hBv, ⟨ht, hav.congr kt.v⟩,
      ((LKeep.of_skeep ku).trans (LKeep.of_kept kv)).trans (LKeep.of_skeep kt)⟩
  | some a =>
    obtain ⟨h1, hacc⟩ := ha
    refine WP.ite false (by show u.zf = _; rw [hz, h1]; rfl) (fun h => nomatch h) (fun _ => ?_)
    refine WP.mono (add_ok hcu hBu (p := entQN X Y Z neg a.1 a.2.1 a.2.2) (hacc.congr ku.v) (heu _ _ _) hsu)
      fun t ⟨hct, kt, hBt, hat⟩ => ?_
    exact ⟨hct, hBt, ⟨by rw [kt.gpr, ku.gpr .r11 List.not_mem_nil, h1], hat⟩,
      (LKeep.of_skeep ku).trans (LKeep.of_kept kt)⟩

/-- A digit of `Q`'s scalar that is not zero: its multiple of `Q` added to the accumulator, or the
accumulator set to it. -/
theorem qDigit_ok {s : State} {base : Addr} {size : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hc : Ctx par s) (hB : EnvOK s stB) (h8 : s.gpr .r8 = b.setWidth 64)
    (ha : 1 ≤ qMag b) (ha' : qMag b ≤ 15) (hodd : qMag b % 2 = 1) (hsize : 8192 ≤ size)
    {Tq : Nat → Fin pN × Fin pN × Fin pN} (hq : LTab Tq s.mem base)
    {acc : Option (Fin pN × Fin pN × Fin pN)} (hacc : AccSt s acc) :
    WP isa (.seq (.block [.alu .cmp .r8 (.imm 128)]) (.seq (.ite .b (.block (signPtr false))
      (.block (([.mov32 .rax (.imm 256), .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax)] : List Instr) ++ signPtr true)))
      (.seq (.seq (.block (entryT ++ loadAPieces.flatten))
          (.block (([.alu .add .rdx (.imm 64)] : List Instr) ++ loadBPieces.flatten))) addOrSet))) s fun t =>
      Ctx par t ∧ EnvOK t stB ∧ AccSt t (some (accStep (Tq ((qMag b - 1) / 2)).1 (Tq ((qMag b - 1) / 2)).2.1
        (Tq ((qMag b - 1) / 2)).2.2 (!decide (b.toNat < 128)) acc)) ∧ LKeep s t := by
  have hE := hq ((qMag b - 1) / 2) (by omega_using [ha'])
  rw [show 200 * ((qMag b - 1) / 2) = 100 * (qMag b - 1) by omega_using [hodd]] at hE
  apply WP.assoc
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp (qEntry_ok hs hc hB h8 ha ha' hsize hE))
    fun _ h₁ => WP.seq (WP.mono h₁ fun u ⟨hcu, hBu, hsu, hau, heu, h11, ku⟩ => ?_)
  have haccu : AccSt u acc := by
    cases acc with
    | none => exact h11.trans hacc
    | some a => exact ⟨h11.trans hacc.1, hau _ _ _ hacc.2⟩
  exact WP.mono (addOrSet_ok hcu hBu hsu heu haccu) fun t ⟨hct, hBt, hat, kt⟩ => ⟨hct, hBt, hat, ku.trans kt⟩

/-! ### A digit of the generator's scalar -/

/-- The magnitude of a digit of the generator's scalar. -/
def gMag (w : BitVec 16) : Nat := if w.toNat < 256 then w.toNat else 65536 - w.toNat

theorem setWidth16 (w : BitVec 16) : w.setWidth 64 = BitVec.ofNat 64 w.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The sign of a digit of the generator's scalar: its magnitude in `r8`, and `r9` at the mask of its sign. -/
theorem gSign_ok (s : State) {w : BitVec 16} (h8 : s.gpr .r8 = w.setWidth 64) :
    WP isa (.seq (.block [.alu .cmp .r8 (.imm 256)]) (.ite .b (.block (signPtr false))
      (.block (([.mov32 .rax (.imm 65536), .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax)] : List Instr) ++ signPtr true)))) s
      fun t => t.gpr .r8 = BitVec.ofNat 64 (gMag w) ∧
        t.gpr .r9 = s.gpr .r10 +
          BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if decide (w.toNat < 256) = false then 3 else 0))) ∧
        SKeep [.rax, .r8, .r9] s t := by
  apply WP.seq
  refine WP.mono (WP.skeep rfl (nafSignW_ok s h8)) fun u ⟨hu, ku⟩ => ?_
  have u8 : u.gpr .r8 = w.setWidth 64 := (ku.gpr .r8 (by decide)).trans h8
  have u10 : u.gpr .r10 = s.gpr .r10 := ku.gpr .r10 (by decide)
  refine WP.ite (decide (w.toNat < 256)) hu (fun hb => ?_) (fun hb => ?_)
  · have hp : w.toNat < 256 := of_decide_eq_true hb
    refine WP.mono (WP.skeep rfl (signPtr_ok u false)) fun t ⟨ht, kt⟩ => ⟨?_, ?_, ?_⟩
    · rw [kt.gpr .r8 (by decide), u8, setWidth16]
      simp only [gMag, hp, ↓reduceIte]
    · rw [ht, u10]
      simp only [hp, decide_true, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
    · exact (ku.mono (by decide)).trans (kt.mono (by decide))
  · have hp : ¬w.toNat < 256 := of_decide_eq_false hb
    rw [WP.block_append_iff]
    refine WP.mono (WP.skeep rfl (nafAbsW_ok u u8)) fun x ⟨hx, kx⟩ => ?_
    refine WP.mono (WP.skeep rfl (signPtr_ok x true)) fun t ⟨ht, kt⟩ => ⟨?_, ?_, ?_⟩
    · rw [kt.gpr .r8 (by decide), hx]
      simp only [gMag, hp, ↓reduceIte]
    · rw [ht, kx.gpr .r10 (by decide), u10]
      simp only [hp, decide_false, ↓reduceIte]
    · exact ((ku.mono (by decide)).trans (kx.mono (by decide))).trans (kt.mono (by decide))

/-- The address of the words of the multiple of the generator of magnitude `a`. -/
theorem gAddr_ok {c : Joint.Cfg} (hn : c.K.M.n = 4) (s : State) {a : Nat} {T : Addr} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 31)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hT : s.syms c.tsym = T) :
    WP isa (.block (entryG c)) s fun t => t.gpr .rdx = off T (64 * (a - 1)) ∧ SKeep [.rax, .rdx] s t := by
  rw [entryG, hn]
  have hk : ∀ i ∈ instrs (.block (Joint.fixedAddress 4 c.tsym) : Prog isa), Taint.clobbers i .rcx = false := by
    intro i hi
    simp only [instrs, Joint.fixedAddress, Joint.fixedOffset, ↓reduceIte, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl
  have h := WP.mono (WP.gpr (jointFixedAddress_ok ha ha' (by decide) h8 hT) hk)
    fun t (h : (t.gpr .rdx = off T (16 * 4 * (a - 1)) ∧ Keeps [.rax, .rcx, .rdx] s t) ∧ t.gpr .rcx = s.gpr .rcx) =>
      (⟨⟨h.1.1, h.2⟩, h.1.2⟩ : (t.gpr .rdx = off T (16 * 4 * (a - 1)) ∧ t.gpr .rcx = s.gpr .rcx) ∧
        Keeps [.rax, .rcx, .rdx] s t)
  refine WP.mono (WP.skeep rfl h) fun t ⟨⟨hd, kc⟩, kt⟩ => ⟨hd, ?_⟩
  refine ⟨fun r hr => ?_, kt.mem, kt.rd, kt.wr, kt.xmm, kt.ymmHi, kt.ymmH⟩
  by_cases hrc : r = .rcx
  · rw [hrc]; exact kc
  · exact kt.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨hr.1, hrc, hr.2⟩)

/-- A digit of the generator's scalar that is not zero: its multiple of the generator, from the
table at `T`, added to the accumulator, or the accumulator set to it. -/
theorem gDigit_ok {c : Joint.Cfg} (hn : c.K.M.n = 4) {s : State} {T : Addr} {w : BitVec 16}
    (hc : Ctx par s) (hB : EnvOK s stB) (h8 : s.gpr .r8 = w.setWidth 64) (hT : s.syms c.tsym = T)
    (ha : 1 ≤ gMag w)
    (hrd : ∀ d, d + 32 ≤ 64 → InRegions (s.rd ++ s.wr) (off T (64 * (gMag w - 1)) + BitVec.ofNat 64 d) 32 ∧
      Mem.Sep (off T (64 * (gMag w - 1)) + BitVec.ofNat 64 d) 32 (s.gpr .rdi + BitVec.ofNat 64 par.lo)
        (par.win - par.lo)) {x y : Fin pN}
    (hx : toM pN (2 ^ 256) (wordsVal s.mem (off T (64 * (gMag w - 1))) 0 4) = x)
    (hy : toM pN (2 ^ 256) (wordsVal s.mem (off T (64 * (gMag w - 1))) 32 4) = y)
    {acc : Option (Fin pN × Fin pN × Fin pN)} (hacc : AccSt s acc) :
    WP isa (.seq (.block [.alu .cmp .r8 (.imm 256)]) (.seq (.ite .b (.block (signPtr false))
      (.block (([.mov32 .rax (.imm 65536), .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax)] : List Instr) ++ signPtr true)))
      (.seq (.block (entryG c ++ convGPieces.flatten)) addOrSet))) s fun t =>
      Ctx par t ∧ EnvOK t stB ∧ AccSt t (some (accStep x y 1 (!decide (w.toNat < 256)) acc)) ∧ LKeep s t := by
  have hmag : gMag w ≤ 2 ^ 31 := by
    have := w.isLt
    unfold gMag
    split <;> omega_using []
  apply WP.assoc
  apply WP.assoc
  apply WP.seq
  apply WP.seq
  refine WP.mono_syms (gSign_ok s h8) fun u ⟨u8, u9, ku⟩ su => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAddr_ok hn u (T := T) ha hmag u8 (by rw [su]; exact hT)) fun e ⟨edx, ke⟩ => ?_
  have kse : SKeep [.rax, .rdx, .r8, .r9] s e := (ku.mono (by decide)).trans (ke.mono (by decide))
  have e9 : e.gpr .r9 = s.gpr .r10 +
      BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if (!decide (w.toNat < 256)) = true then 3 else 0))) := by
    rw [ke.gpr .r9 (by decide), u9]
    cases decide (w.toNat < 256) <;> rfl
  have kb : ∀ neg : Bool, 32 * poolLit.idxOf (K4.lanes (if neg = true then 3 else 0)) + 32 ≤ 8 * par.cst.length := by
    decide +kernel
  have hce : Ctx par e := by
    refine ctx_skeep hc kse (by decide) (by decide) fun r d hr hd => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [lim_other (by decide) (by decide) (by decide)] at hd; omega
    · have hd' : d + 32 ≤ 64 := hd
      rw [edx]
      exact hrd d hd'
    · rw [lim_other (by decide) (by decide) (by decide)] at hd; omega
    · have hd' : d + 32 ≤ 32 := hd
      have hk := kb (!decide (w.toNat < 256))
      rw [e9, Offset.add_add]
      exact ⟨hc.crd _ (by omega_using [hd', hk]), hc.csep _ (by omega_using [hd', hk])⟩
  have hBe : EnvOK e stB := envOK_skeep kse (by decide) hB
  refine WP.mono (convG_ok hce hBe) fun t ⟨hct, kt, hEt, hav, c0, c1, c2, c3, cb⟩ => ?_
  have wd (d : Nat) : wv (envOf e) (.ld .rdx d) = (wordsVal s.mem (off T (64 * (gMag w - 1))) d 4 : Nat) := by
    rw [wv_ld e .rdx rfl d, edx, kse.mem]
  have t9 : t.gpr .r9 = t.gpr .r10 +
      BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if (!decide (w.toNat < 256)) = true then 3 else 0))) := by
    rw [kt.gpr, e9, kse.gpr .r10 (by decide)]
  have hm := sgn_m hct (!decide (w.toNat < 256)) t9
  have h11 : t.gpr .r11 = s.gpr .r11 := by rw [kt.gpr, kse.gpr .r11 (by decide)]
  have hacct : AccSt t acc := by
    cases acc with
    | none => exact h11.trans hacc
    | some a => exact ⟨h11.trans hacc.1, hav _ _ _ (hacc.2.congr kse.v)⟩
  exact WP.mono (addOrSet_ok hct (envOK_sgn hEt hm) (sgnOk_of hm)
    (fun xn un z => entOk_G c0 c1 c2 c3 cb (wd 0) (wd 32) hx hy _ xn un z) hacct)
    fun v ⟨hcv, hBv, hav', kv⟩ => ⟨hcv, hBv, hav', ((LKeep.of_skeep kse).trans (LKeep.of_kept kt)).trans kv⟩

end VG.Proof.P256.X86_64.Ifma
