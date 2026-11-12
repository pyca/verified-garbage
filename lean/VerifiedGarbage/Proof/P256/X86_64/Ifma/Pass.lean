module

-- separate module: its proofs (about 5 s, a digit's entry and addition) are not checked again when `VLoop` changes

public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCache
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafDigitRead
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafAddress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedEntryW
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedLoad
import VerifiedGarbage.Proof.Framework.X86_64.Inline
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
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.ConvOk
public import VerifiedGarbage.Proof.Weierstrass.JacCoZ
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Proof.Weierstrass.Comb
public import VerifiedGarbage.Spec.P256

/-!
# P-256 on x86-64 with AVX512_IFMA: a digit of the loop

A digit that is not zero: its sign, the addresses of its point's words, the
point's entry (`convQ_ok`, `convG_ok`), and its addition to the accumulator
(`add_ok`), or the accumulator set to it (`set_ok`).
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
  rw [show d + 8 + 8 = d + 8 * 2 by omega, show d + 8 * 2 + 8 = d + 8 * 3 by omega, show d + 8 * 0 = d by omega,
    show d + 8 * 1 = d + 8 by omega]
  omega

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
  have nb : Nb ≤ 2 ^ 259 := by simp only [Nb]; omega
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
      8 * (4 * poolLit.idxOf (K4.lanes (if neg then 3 else 0)) + k) by omega, c]
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
      omega
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
open VG.Proof.Weierstrass (Unch toM)

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

/-- The addresses of the words of the odd multiple of `Q` of magnitude `a`, and of its `Z²` and `Z³`. -/
theorem qAddr_ok {c : Joint.Cfg} (hn : c.K.M.n = 4) (s : State) {base : Addr} {a : Nat} (hb : s.gpr .rdi = base)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (ha : 1 ≤ a) (ha' : a ≤ 15) (hodd : a % 2 = 1) (ht : c.K.tbl < 2 ^ 31)
    (hcache : c.cache < 2 ^ 31) :
    WP isa (.block (entryQ c)) s fun t =>
      t.gpr .rcx = off base (c.K.tbl + 96 * ((a - 1) / 2)) ∧ t.gpr .rdx = off base (c.cache + 64 * ((a - 1) / 2)) ∧
        SKeep [.rax, .rcx, .rdx, .rbp] s t := by
  rw [entryQ, hn, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.skeep rfl (nafIndex_ok s ha ha' h8)) fun u ⟨hu, ku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.skeep rfl (nafAddress_ok u ((ku.gpr .rdi (by decide)).trans hb) hu ht (by decide)))
    fun v ⟨hv, kv⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.skeep rfl (mov_ok v .rbp .rdx)) fun w ⟨hw, kw⟩ => ?_
  have w8 : w.gpr .r8 = BitVec.ofNat 64 a :=
    (kw.gpr .r8 (by decide)).trans ((kv.gpr .r8 (by decide)).trans ((ku.gpr .r8 (by decide)).trans h8))
  have wdi : w.gpr .rdi = base :=
    (kw.gpr .rdi (by decide)).trans ((kv.gpr .rdi (by decide)).trans ((ku.gpr .rdi (by decide)).trans hb))
  rw [WP.block_append_iff]
  refine WP.mono (WP.skeep rfl (nafCacheAddress_ok wdi w8 ha ha' hodd hcache (by decide))) fun x ⟨hx, kx⟩ => ?_
  refine WP.mono (WP.skeep rfl (mov_ok x .rcx .rbp)) fun t ⟨ht', kt⟩ => ⟨?_, ?_, ?_⟩
  · rw [ht', kx.gpr .rbp (by decide), hw, hv]
  · rw [kt.gpr .rdx (by decide), hx]
  · exact ((((ku.mono (by decide)).trans (kv.mono (by decide))).trans (kw.mono (by decide))).trans
      (kx.mono (by decide))).trans (kt.mono (by decide))

/-- What a digit's code keeps: the registers but those it works with, the regions, and memory but the slots. -/
structure LKeep (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r11] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Unch (s.gpr .rdi) [(cfg.sbase, par.win - cfg.sbase)] s.mem t.mem

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

/-- The entry of a digit of `Q`'s scalar that is not zero: in `ymm20`–`ymm29`, with the mask of its
sign at `r9`, from the words of the digit's multiple of `Q` in the table. -/
theorem qEntry_ok {c : Joint.Cfg} (hn : c.K.M.n = 4) {s : State} {base : Addr} {size : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hc : Ctx par s) (hB : EnvOK s stB) (h8 : s.gpr .r8 = b.setWidth 64)
    (ha : 1 ≤ qMag b) (ha' : qMag b ≤ 15) (hodd : qMag b % 2 = 1)
    (ht : c.K.tbl + 768 ≤ 4512) (hcache : c.cache + 512 ≤ 4512) (hsize : 5408 ≤ size) {X Y Z : Fin pN}
    (hx : toM pN (2 ^ 256) (wordsVal s.mem base (c.K.tbl + 96 * ((qMag b - 1) / 2) + 0) 4) = X)
    (hy : toM pN (2 ^ 256) (wordsVal s.mem base (c.K.tbl + 96 * ((qMag b - 1) / 2) + 32) 4) = Y)
    (hz : toM pN (2 ^ 256) (wordsVal s.mem base (c.K.tbl + 96 * ((qMag b - 1) / 2) + 64) 4) = Z)
    (hzz : toM pN (2 ^ 256) (wordsVal s.mem base (c.cache + 64 * ((qMag b - 1) / 2) + 0) 4) = Z * Z)
    (hzzz : toM pN (2 ^ 256) (wordsVal s.mem base (c.cache + 64 * ((qMag b - 1) / 2) + 32) 4) = Z * Z * Z) :
    WP isa (.seq (.seq (.block [.alu .cmp .r8 (.imm 128)]) (.ite .b (.block (signPtr false))
      (.block (([.mov32 .rax (.imm 256), .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax)] : List Instr) ++ signPtr true))))
      (.block (entryQ c ++ convQPieces.flatten))) s fun t =>
      Ctx par t ∧ EnvOK t addB ∧ SgnOk (envOf t) sgnT.l0 (!decide (b.toNat < 128)) ∧
        (∀ xn un z, AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) xn un z →
          AccOk (envOf t) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) ∧
        (∀ xn un z, EntOk (envOf t) (t5 20) (t5 25) (entQN X Y Z (!decide (b.toNat < 128)) xn un z)) ∧
        t.gpr .r11 = s.gpr .r11 ∧ LKeep s t := by
  have hnw := hs.nowrap
  have hlo : par.lo = 4512 := rfl
  have hwin : par.win = 5408 := rfl
  apply WP.seq
  refine WP.mono (qSign_ok s h8) fun u ⟨u8, u9, ku⟩ => ?_
  rw [WP.block_append_iff]
  have udi : u.gpr .rdi = base := (ku.gpr .rdi (by decide)).trans hs.rdi
  refine WP.mono (qAddr_ok hn u udi u8 ha ha' hodd (by omega) (by omega)) fun e ⟨ecx, edx, ke⟩ => ?_
  have kse : SKeep [.rax, .rcx, .rdx, .rbp, .r8, .r9] s e := (ku.mono (by decide)).trans (ke.mono (by decide))
  have e9 : e.gpr .r9 = s.gpr .r10 +
      BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if (!decide (b.toNat < 128)) = true then 3 else 0))) := by
    rw [ke.gpr .r9 (by decide), u9]
    cases decide (b.toNat < 128) <;> rfl
  have kb : ∀ neg : Bool, 32 * poolLit.idxOf (K4.lanes (if neg = true then 3 else 0)) + 32 ≤ 8 * par.cst.length := by
    decide +kernel
  have hce : Ctx par e := by
    refine ctx_skeep hc kse (by decide) (by decide) fun r d hr hd => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [lim_other (by decide) (by decide) (by decide)] at hd; omega
    · have hd' : d + 32 ≤ 96 := hd
      rw [ecx, Offset.add_add, hs.rdi]
      exact ⟨⟨_, List.mem_append_right _ hs.wr, hs.contains (by omega) (by decide)⟩,
        Offset.sep base (Or.inl (by omega)) (by omega) (by omega)⟩
    · have hd' : d + 32 ≤ 64 := hd
      rw [edx, Offset.add_add, hs.rdi]
      exact ⟨⟨_, List.mem_append_right _ hs.wr, hs.contains (by omega) (by decide)⟩,
        Offset.sep base (Or.inl (by omega)) (by omega) (by omega)⟩
    · rw [lim_other (by decide) (by decide) (by decide)] at hd; omega
    · rw [lim_other (by decide) (by decide) (by decide)] at hd; omega
    · have hd' : d + 32 ≤ 32 := hd
      have hk := kb (!decide (b.toNat < 128))
      rw [e9, Offset.add_add]
      exact ⟨hc.crd _ (by omega), hc.csep _ (by omega)⟩
  have hBe : EnvOK e stB := envOK_skeep kse (by decide) hB
  refine WP.mono (convQ_ok hce hBe) fun t ⟨hct, kt, hEt, hacc, c0, c1, c2, c3, cb⟩ => ?_
  have w (r : Reg) (hr : uBase r = true) (d x : Nat) (hx : e.gpr r = off base x) :
      wv (envOf e) (.ld r d) = (wordsVal s.mem base (x + d) 4 : Nat) := by
    rw [wv_ld e r hr d, hx, wordsVal_off, kse.mem]
  have t9 : t.gpr .r9 = t.gpr .r10 +
      BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if (!decide (b.toNat < 128)) = true then 3 else 0))) := by
    rw [kt.gpr, e9, kse.gpr .r10 (by decide)]
  have hm := sgn_m hct (!decide (b.toNat < 128)) t9
  exact ⟨hct, envOK_sgn hEt hm, sgnOk_of hm, fun xn un z h => hacc xn un z (h.congr kse.v),
    fun xn un z => entOk_Q c0 c1 c2 c3 cb (w .rcx rfl 0 _ ecx) (w .rcx rfl 32 _ ecx) (w .rcx rfl 64 _ ecx)
      (w .rdx rfl 0 _ edx) (w .rdx rfl 32 _ edx) hx hy hz hzz hzzz _ xn un z,
    by rw [kt.gpr, kse.gpr .r11 (by decide)], (LKeep.of_skeep kse).trans (LKeep.of_kept kt)⟩

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
theorem qDigit_ok {c : Joint.Cfg} (hn : c.K.M.n = 4) {s : State} {base : Addr} {size : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hc : Ctx par s) (hB : EnvOK s stB) (h8 : s.gpr .r8 = b.setWidth 64)
    (ha : 1 ≤ qMag b) (ha' : qMag b ≤ 15) (hodd : qMag b % 2 = 1)
    (ht : c.K.tbl + 768 ≤ 4512) (hcache : c.cache + 512 ≤ 4512) (hsize : 5408 ≤ size) {X Y Z : Fin pN}
    (hx : toM pN (2 ^ 256) (wordsVal s.mem base (c.K.tbl + 96 * ((qMag b - 1) / 2) + 0) 4) = X)
    (hy : toM pN (2 ^ 256) (wordsVal s.mem base (c.K.tbl + 96 * ((qMag b - 1) / 2) + 32) 4) = Y)
    (hz : toM pN (2 ^ 256) (wordsVal s.mem base (c.K.tbl + 96 * ((qMag b - 1) / 2) + 64) 4) = Z)
    (hzz : toM pN (2 ^ 256) (wordsVal s.mem base (c.cache + 64 * ((qMag b - 1) / 2) + 0) 4) = Z * Z)
    (hzzz : toM pN (2 ^ 256) (wordsVal s.mem base (c.cache + 64 * ((qMag b - 1) / 2) + 32) 4) = Z * Z * Z)
    {acc : Option (Fin pN × Fin pN × Fin pN)} (hacc : AccSt s acc) :
    WP isa (.seq (.block [.alu .cmp .r8 (.imm 128)]) (.seq (.ite .b (.block (signPtr false))
      (.block (([.mov32 .rax (.imm 256), .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax)] : List Instr) ++ signPtr true)))
      (.seq (.block (entryQ c ++ convQPieces.flatten)) addOrSet))) s fun t =>
      Ctx par t ∧ EnvOK t stB ∧ AccSt t (some (accStep X Y Z (!decide (b.toNat < 128)) acc)) ∧ LKeep s t := by
  apply WP.assoc
  apply WP.assoc
  apply WP.seq
  refine WP.mono (qEntry_ok hn hs hc hB h8 ha ha' hodd ht hcache hsize hx hy hz hzz hzzz)
    fun u ⟨hcu, hBu, hsu, hau, heu, h11, ku⟩ => ?_
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
    split <;> omega
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
      exact ⟨hc.crd _ (by omega), hc.csep _ (by omega)⟩
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
