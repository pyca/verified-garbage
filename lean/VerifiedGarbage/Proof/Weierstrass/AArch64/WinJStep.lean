module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.CopyKeep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
public import VerifiedGarbage.Impl.Weierstrass.AArch64.WindowJ
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
import VerifiedGarbage.Proof.Weierstrass.WindowJ
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Weierstrass.JacMadd
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.WindowJA
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Weierstrass.AArch64.WinJNorm`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.AArch64.WinJBuild`, which this module and modules that import it used -/

section

/-!
# Windows in Jacobian coordinates on AArch64: the slots

The field programs of the Jacobian window method are on slots that are apart
(`WinLay.rcbApart_winJ`), and the table is apart from what the loop writes
(`tbl_apart_loopW`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The slots the Jacobian window method's field programs use are apart:
the doublings between `R` and `D`, and `fromJ` from `R` into `D` (`z` the
slots of zero). -/
theorem _root_.VG.Proof.Weierstrass.WinLay.rcbApart_winJ {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    RcbApart K.S K.R K.R K.D ∧ RcbApart K.S K.D K.D K.R ∧
      RcbApart K.S K.R ⟨K.zero, K.zero, K.zero⟩ K.D :=
  ⟨hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 13, 14, 15]) (lr := [16, 17, 0, 1, 2, 0, 1, 2]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 0, 1, 2]) (lr := [16, 17, 13, 14, 15, 13, 14, 15]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 13, 14, 15]) (lr := [16, 17, 0, 1, 2, 18, 18, 18]) rfl rfl⟩

/-- A table slot is apart from what the loop's field programs write. -/
theorem tbl_apart_loopW {K : WinCfg} {size : Nat} (hL : WinLay K size) {j : Nat} (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    {x : Nat} (hx : x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z]) :
    ∀ w ∈ loopW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K hj1 hj8 x hx
  intro w hw
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact (hL.tbl_apart (List.mem_append_right _ hy) hi).symm
  · exact hL.lay.tmp _ (by simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi))

/-- The slots of a point, written. -/
theorem pt_other {K : WinCfg} {p : Pt} (h : p = K.R ∨ p = K.E ∨ p = K.D) :
    ∀ x ∈ [p.x, p.y, p.z], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases h with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> win_mem

end VG.Proof.Weierstrass.AArch64

end

end

/-!
# Windows in Jacobian coordinates on AArch64: the table into affine coordinates

`normTbl` (Montgomery's trick) on the table `build` leaves (`TblOk`): the
prefix products `c_m = Z_1 ⋯ Z_m` (`prod_ok`), `c_8^(p-2)` by the inversion,
then back from entry `8` (`back_ok`): `Z_m^(p-2) = c_m^(p-2) c_{m-1}` and
`c_{m-1}^(p-2) = c_m^(p-2) Z_m` (`trick_step`), each entry's `X` and `Y` by its
`Z^(p-2)`, and every `Z` set to one: a table of `RepA` (`normTbl_ok`), for
entries other than `O`. Each product is `slotMul_ok`, on the window's slots.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- One product on the window's slots, writing a slot written: the other
slots keep their numbers. -/
theorem slotMul_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) {o a b : Nat} (ho : o ∈ winOther K)
    (ha : a ∈ winRo K ++ winOther K) (hb : b ∈ winRo K ++ winOther K)
    (hla : wordsVal s.mem base a K.M.n < C.p) (hlb : wordsVal s.mem base b K.M.n < C.p) :
    WP isa (opProg K.M (.mul o a b)) s fun s' => Scr s' base size ∧
      KeepRegs (clob K.M.n) s s' ∧ Unch base (winW K) s.mem s'.mem ∧
      ModOkA K.M size C.p s'.mem base ∧ wordsVal s'.mem base o K.M.n < C.p ∧
      tmv C K.M.n base s' o = tmv C K.M.n base s a * tmv C K.M.n base s b ∧
      ∀ x ∈ winSlots K, x ≠ o → wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
  obtain hS : ∀ x ∈ winRo K ++ winOther K, x ∈ winSlots K := fun x hx => by
    simp only [winSlots, List.mem_append] at hx ⊢; exact Or.inl hx
  obtain hoS : o ∈ winSlots K := winOther_mem ho
  obtain I : Inv K.M base size C.p (· ∈ winSlots K) [a, b] (tmv C K.M.n base s) s := by
    refine ⟨hs, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hS _ ha
      · exact hS _ hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hla
      · exact hlb
  obtain hin : ∀ x ∈ (FOp.mul o a b).out :: (FOp.mul o a b).ins, x ∈ winRo K ++ winOther K := by
    intro x hx
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact List.mem_append_right _ ho
    · exact ha
    · exact hb
  refine WP.mono (opProg_ok hL.lay hA.al hp I (op := .mul o a b) (fun x hx => hS x (hin x hx))
    (hA.low hin) (fun x hx => hx)) fun s' ⟨k, I'⟩ => ?_
  have hn := hs.nowrap
  obtain U : Unch base [(o, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem :=
    fun x hx => k.mem x (hx _ (List.mem_cons_self ..)) (hx (K.M.tmp, 8 * K.M.n) (by simp))
  refine ⟨I'.scr, ⟨k.gpr, k.rd, k.wr, k.sp⟩, U.mono fun w hw => ?_, I'.mod, I'.lt o (List.mem_cons_self ..),
    ?_, fun x hx hxo => U.wordsVal (fun w hw => ?_) (by have := hL.lay.le x hx; omega_arith)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [winW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl
    · exact Or.inl ⟨o, winOther_ws K o ho, rfl⟩
    · exact Or.inr rfl
  · have v := I'.val o (List.mem_cons_self ..)
    simp only [FOp.run, Function.update_self] at v
    exact v
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hL.lay.apart x o hx hoS hxo
    · exact hL.lay.tmp x hx

/-- Straight-line code made of `N` pieces, by an invariant of the pieces done. -/
theorem block_range_ok {f : Nat → List Instr} {N : Nat} {Inv : Nat → State → Prop}
    (step : ∀ i < N, ∀ s, Inv i s → WP isa (.block (f i)) s (Inv (i + 1))) :
    ∀ i ≤ N, ∀ s, Inv 0 s → WP isa (.block ((List.range i).flatMap f)) s (Inv i)
  | 0, _, s, h => by simpa using (WP.block_nil h : WP isa (.block []) s (Inv 0))
  | i + 1, hi, s, h => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (block_range_ok step i (by omega_arith) s h) fun t ht => ?_
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using step i (by omega_arith) t ht

/-! ## Code in pieces -/

/-- `seqRange`, by an invariant of the pieces done. -/
theorem seqRange_ok {f : Nat → Prog isa} {N : Nat} {Inv : Nat → State → Prop}
    (step : ∀ i < N, ∀ s, Inv i s → WP isa (f i) s (Inv (i + 1))) :
    ∀ i ≤ N, ∀ s, Inv 0 s → WP isa (WinCfg.seqRange f i) s (Inv i)
  | 0, _, _, h => WP.block_nil h
  | i + 1, hi, s, h =>
    WP.seq (WP.mono (seqRange_ok step i (by omega_arith) s h) fun t ht => step i (by omega_arith) t ht)

/-! ## The slots of the prefix products -/

/-- The slots holding `c_2 … c_8`, then `D.x`, `E.x`, `D.y` (where the table's
operands are copied) and `D.z` (`c_1`): written, and distinct. -/
def normW (K : WinCfg) : List Nat :=
  [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.R.z, K.D.x, K.E.x, K.D.y, K.D.z, K.neg]

theorem normW_other (K : WinCfg) : ∀ x ∈ normW K, x ∈ winOther K := by
  intro x hx
  simp only [normW, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem

theorem normW_nodup {K : WinCfg} {size : Nat} (hL : WinLay K size) : (normW K).Nodup := by
  have hnd := hL.nodup
  simp only [winOther, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  simp only [normW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true]
  grind

/-- The index of `c_j`'s slot in `normW`. -/
def pIdx (j : Nat) : Nat := if j = 1 then 10 else j - 2

theorem prodSl_eq (K : WinCfg) {j : Nat} (h1 : 1 ≤ j) (h8 : j ≤ 8) :
    WinCfg.prodSl K j = (normW K)[pIdx j]'(by simp only [normW, pIdx]; split <;> simp <;> omega_arith) := by
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 by omega_arith) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem prodSl_one (K : WinCfg) : WinCfg.prodSl K 1 = K.D.z := rfl

theorem prodSl_other {K : WinCfg} {j : Nat} (h1 : 1 ≤ j) (h8 : j ≤ 8) : WinCfg.prodSl K j ∈ winOther K := by
  rw [prodSl_eq K h1 h8]; exact normW_other K _ (List.getElem_mem ..)

theorem normW_ne {K : WinCfg} {size : Nat} (hL : WinLay K size) {i i' : Nat} (hi : i < (normW K).length)
    (hi' : i' < (normW K).length) (h : i ≠ i') : (normW K)[i] ≠ (normW K)[i'] := by
  obtain hp := List.pairwise_iff_getElem.mp (normW_nodup hL)
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact hp i i' hi hi' h
  · exact fun e => hp i' i hi' hi h e.symm

theorem prodSl_inj {K : WinCfg} {size : Nat} (hL : WinLay K size) {j j' : Nat} (h1 : 1 ≤ j) (h8 : j ≤ 8)
    (h1' : 1 ≤ j') (h8' : j' ≤ 8) (h : WinCfg.prodSl K j = WinCfg.prodSl K j') : j = j' := by
  rw [prodSl_eq K h1 h8, prodSl_eq K h1' h8'] at h
  exact Classical.byContradiction fun hne => normW_ne hL _ _ (by simp only [pIdx]; split <;> split <;> omega_arith) h

/-- `c_j`'s slot is not `D.x`, `E.x` or `D.y`. -/
theorem prodSl_ne_DE {K : WinCfg} {size : Nat} (hL : WinLay K size) {j : Nat} (h1 : 1 ≤ j) (h8 : j ≤ 8) :
    WinCfg.prodSl K j ≠ K.D.x ∧ WinCfg.prodSl K j ≠ K.E.x ∧ WinCfg.prodSl K j ≠ K.D.y := by
  rw [prodSl_eq K h1 h8]
  have hD : K.D.x = (normW K)[7]'(by simp [normW]) := rfl
  have hE : K.E.x = (normW K)[8]'(by simp [normW]) := rfl
  have hY : K.D.y = (normW K)[9]'(by simp [normW]) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hD]; exact normW_ne hL _ _ (by simp only [pIdx]; split <;> omega_arith)
  · rw [hE]; exact normW_ne hL _ _ (by simp only [pIdx]; split <;> omega_arith)
  · rw [hY]; exact normW_ne hL _ _ (by simp only [pIdx]; split <;> omega_arith)

/-- `c_j`'s slot is not `neg`, which the inversion may write. -/
theorem prodSl_ne_neg {K : WinCfg} {size : Nat} (hL : WinLay K size) {j : Nat} (h1 : 1 ≤ j) (h8 : j ≤ 8) :
    WinCfg.prodSl K j ≠ K.neg := by
  rw [prodSl_eq K h1 h8]
  have hN : K.neg = (normW K)[11]'(by simp [normW]) := rfl
  rw [hN]; exact normW_ne hL _ _ (by simp only [pIdx]; split <;> omega_arith)

/-- `D.x`, `E.x` and `D.y` are distinct. -/
theorem DE_ne {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    K.D.x ≠ K.E.x ∧ K.D.y ≠ K.D.x ∧ K.D.y ≠ K.E.x := by
  have hD : K.D.x = (normW K)[7]'(by simp [normW]) := rfl
  have hE : K.E.x = (normW K)[8]'(by simp [normW]) := rfl
  have hY : K.D.y = (normW K)[9]'(by simp [normW]) := rfl
  rw [hD, hE, hY]
  exact ⟨normW_ne hL _ _ (by decide), normW_ne hL _ _ (by decide), normW_ne hL _ _ (by decide)⟩

/-- A slot written but the table's is not a table slot. -/
theorem other_ne_tbl {K : WinCfg} {size : Nat} (hL : WinLay K size) {x : Nat} (hx : x ∈ winOther K)
    {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8) {y : Nat} (hy : y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z]) :
    x ≠ y := by
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 y hy
  exact hL.tbl_ne (List.mem_append_right _ hx) hi

/-- `D.y` is not a table slot. -/
theorem Dy_tbl {K : WinCfg} {size : Nat} (hL : WinLay K size) {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8)
    {y : Nat} (hy : y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z]) : y ≠ K.D.y :=
  (other_ne_tbl hL (by win_mem) h1 h8 hy).symm

theorem tmv_congr {C : Curve} {n : Nat} {base : Addr} {s t : State} {x : Nat}
    (h : wordsVal t.mem base x n = wordsVal s.mem base x n) : tmv C n base t x = tmv C n base s x := by
  show toM _ _ _ = toM _ _ _; rw [h]

theorem tmv_eq {C : Curve} {n : Nat} {base : Addr} {s t : State} {x y : Nat}
    (h : wordsVal t.mem base x n = wordsVal s.mem base y n) : tmv C n base t x = tmv C n base s y := by
  show toM _ _ _ = toM _ _ _; rw [h]

/-! ## Products of the table's numbers, through `D.y` -/

theorem winW_append {K : WinCfg} : ∀ w ∈ winW K ++ winW K, w ∈ winW K := fun _ hw =>
  (List.mem_append.mp hw).elim id id

/-- A copy into a slot written: the other slots keep their numbers. -/
theorem slotCopy_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) {s : State} (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base) {o a : Nat}
    (ho : o ∈ winWs K) (ha : a ∈ winSlots K) (hoa : o ≠ a) :
    WP isa (.block (copy K.M.n o a)) s fun s' => Scr s' base size ∧ KeepRegs (clob K.M.n) s s' ∧
      Unch base (winW K) s.mem s'.mem ∧ ModOkA K.M size C.p s'.mem base ∧
      wordsVal s'.mem base o K.M.n = wordsVal s.mem base a K.M.n ∧
      ∀ x ∈ winSlots K, x ≠ o → wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
  have hn := hs.nowrap
  obtain hoS := winWs_slots K o ho
  obtain sep := hL.lay.apart o a hoS ha hoa
  refine WP.mono (copy_ok (size := size) K.M.n hs (hL.lay.le o hoS) (hL.lay.le a ha) (hA.sl o hoS)
    (hA.sl a ha) (by omega_arith)) fun s' ⟨v, k, O⟩ => ?_
  obtain U : Unch base (winW K) s.mem s'.mem := O.unch.mono fun w hw => by
    rw [List.mem_singleton.mp hw]
    simp only [winW, List.mem_append, List.mem_map]
    exact Or.inl ⟨o, ho, rfl⟩
  refine ⟨hs.of_keepRegs k (by decide), k.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; simp [clob], U,
    hM.unch U (winW_mo hL hM) hn, v, fun x hx hxo => ?_⟩
  exact O.unch.wordsVal (fun w hw => by rw [List.mem_singleton.mp hw]; exact hL.lay.apart x o hx hoS hxo)
    (by have := hL.lay.le x hx; omega_arith)

/-- A product as a one-product program. -/
theorem slotMul1_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) {o a b : Nat} (ho : o ∈ winOther K)
    (ha : a ∈ winRo K ++ winOther K) (hb : b ∈ winRo K ++ winOther K) (hla : wordsVal s.mem base a K.M.n < C.p)
    (hlb : wordsVal s.mem base b K.M.n < C.p) :
    WP isa (fprogB K.M [.mul o a b]) s fun s' => Scr s' base size ∧
      KeepRegs (clob K.M.n) s s' ∧ Unch base (winW K) s.mem s'.mem ∧
      ModOkA K.M size C.p s'.mem base ∧ wordsVal s'.mem base o K.M.n < C.p ∧
      tmv C K.M.n base s' o = tmv C K.M.n base s a * tmv C K.M.n base s b ∧
      ∀ x ∈ winSlots K, x ≠ o → wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
  slotMul_ok hL hA hp hs hM ho ha hb hla hlb

/-- `o = a [b]` through `D.y` (`mulTb`): the slots but `o` and `D.y` keep
their numbers. -/
theorem mulTb_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) {o a b : Nat} (ho : o ∈ winOther K) (ha : a ∈ winOther K)
    (hb : b ∈ winSlots K) (hay : a ≠ K.D.y) (hby : b ≠ K.D.y) (hla : wordsVal s.mem base a K.M.n < C.p)
    (hlb : wordsVal s.mem base b K.M.n < C.p) :
    WP isa (WinCfg.mulTb K o a b) s fun s' => Scr s' base size ∧
      KeepRegs (clob K.M.n) s s' ∧ Unch base (winW K) s.mem s'.mem ∧
      ModOkA K.M size C.p s'.mem base ∧ wordsVal s'.mem base o K.M.n < C.p ∧
      tmv C K.M.n base s' o = tmv C K.M.n base s a * tmv C K.M.n base s b ∧
      ∀ x ∈ winSlots K, x ≠ o → x ≠ K.D.y → wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
  obtain Dy : K.D.y ∈ winWs K := winOther_ws K _ (by win_mem)
  obtain haS := winOther_mem ha
  refine WP.seq (WP.mono (slotCopy_ok hL hA hs hM Dy hb hby.symm) fun s₁ ⟨s₁s, k₁, U₁, M₁, v₁, e₁⟩ => ?_)
  refine WP.mono (slotMul1_ok hL hA hp s₁s M₁ ho (List.mem_append_right _ ha)
    (List.mem_append_right _ (by win_mem)) (by rw [e₁ a haS hay]; exact hla)
    (by rw [v₁]; exact hlb)) fun s₂ ⟨s₂s, k₂, U₂, M₂, l₂, v₂, e₂⟩ => ?_
  refine ⟨s₂s, k₁.trans k₂, (U₁.trans U₂).mono winW_append, M₂, l₂, ?_, fun x hx hxo hxy => ?_⟩
  · rw [v₂, tmv_congr (e₁ a haS hay), tmv_eq v₁]
  · rw [e₂ x hx hxo, e₁ x hx hxy]

/-- `[x] = [x] d` through `D.y` (`mulTx`): the slots but `x` and `D.y` keep
their numbers. -/
theorem mulTx_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) {x d : Nat} (hx : x ∈ winWs K) (hdo : d ∈ winOther K)
    (hxy : x ≠ K.D.y) (hdy : d ≠ K.D.y) (hlx : wordsVal s.mem base x K.M.n < C.p)
    (hld : wordsVal s.mem base d K.M.n < C.p) :
    WP isa (WinCfg.mulTx K x d) s fun s' => Scr s' base size ∧
      KeepRegs (clob K.M.n) s s' ∧ Unch base (winW K) s.mem s'.mem ∧
      ModOkA K.M size C.p s'.mem base ∧ wordsVal s'.mem base x K.M.n < C.p ∧
      tmv C K.M.n base s' x = tmv C K.M.n base s x * tmv C K.M.n base s d ∧
      ∀ y ∈ winSlots K, y ≠ x → y ≠ K.D.y → wordsVal s'.mem base y K.M.n = wordsVal s.mem base y K.M.n := by
  obtain Dy : K.D.y ∈ winWs K := winOther_ws K _ (by win_mem)
  obtain DyS := winWs_slots K _ Dy
  obtain xS := winWs_slots K _ hx
  obtain hd := winOther_mem hdo
  refine WP.seq (WP.mono (slotCopy_ok hL hA hs hM Dy xS hxy.symm) fun s₁ ⟨s₁s, k₁, U₁, M₁, v₁, e₁⟩ => ?_)
  refine WP.seq (WP.mono (slotMul1_ok hL hA hp s₁s M₁ (by win_mem) (List.mem_append_right _ (by win_mem))
    (List.mem_append_right _ hdo) (by rw [v₁]; exact hlx)
    (by rw [e₁ d hd hdy]; exact hld)) fun s₂ ⟨s₂s, k₂, U₂, M₂, l₂, v₂, e₂⟩ => ?_)
  refine WP.mono (slotCopy_ok hL hA s₂s M₂ hx DyS hxy) fun s₃ ⟨s₃s, k₃, U₃, M₃, v₃, e₃⟩ => ?_
  refine ⟨s₃s, k₁.trans (k₂.trans k₃), (U₁.trans (U₂.trans U₃)).mono fun w hw => ?_, M₃,
    by rw [v₃]; exact l₂, ?_, fun y hy hyx hyy => ?_⟩
  · simp only [List.mem_append] at hw; rcases hw with hw | hw | hw <;> exact hw
  · rw [tmv_eq v₃, v₂, tmv_eq v₁, tmv_congr (e₁ d hd hdy)]
  · rw [e₃ y hy hyx, e₂ y hy hyy, e₁ y hy hyy]

/-! ## The prefix products -/

/-- The prefix products of `Z`: `c_1 = Z_1`, `c_{j+1} = c_j Z_{j+1}`. -/
def cprod {C : Curve} (Z : Nat → Fe C) : Nat → Fe C
  | 0 => Z 1
  | 1 => Z 1
  | j + 2 => cprod Z (j + 1) * Z (j + 2)

/-- The table's `Z` in a state. -/
abbrev tz (K : WinCfg) (C : Curve) (base : Addr) (s : State) (j : Nat) : Fe C :=
  tmv C K.M.n base s (K.tblPt j).z

/-- After `c_1` and the products `c_2 … c_{i+1}`, from `s₀`: they in their
slots, and the other slots but `D.y` as in `s₀`. -/
structure PreInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (s₀ : State) (i : Nat)
    (t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs (clob K.M.n) s₀ t
  unch : Unch base (winW K) s₀.mem t.mem
  mod : ModOkA K.M size C.p t.mem base
  lt : ∀ j, 1 ≤ j → j ≤ i + 1 → wordsVal t.mem base (WinCfg.prodSl K j) K.M.n < C.p
  val : ∀ j, 1 ≤ j → j ≤ i + 1 → tmv C K.M.n base t (WinCfg.prodSl K j) = cprod (tz K C base s₀) j
  same : ∀ x ∈ winSlots K, (∀ j, 1 ≤ j → j ≤ i + 1 → x ≠ WinCfg.prodSl K j) → x ≠ K.D.y →
    wordsVal t.mem base x K.M.n = wordsVal s₀.mem base x K.M.n

/-- A table `Z` is not the slot of a prefix product. -/
theorem tz_same {K : WinCfg} {size : Nat} (hL : WinLay K size) {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8) :
    (K.tblPt m).z ∈ winSlots K ∧ (K.tblPt m).z ≠ K.D.y ∧
      ∀ j, 1 ≤ j → j ≤ 8 → (K.tblPt m).z ≠ WinCfg.prodSl K j :=
  ⟨(tblPt_slots K h1 h8 _ (by simp)).1, Dy_tbl hL h1 h8 (by simp), fun j h1' h8' h =>
    other_ne_tbl hL (prodSl_other h1' h8') h1 h8 (y := (K.tblPt m).z) (by simp) h.symm⟩

/-- `c_1`: `Z_1` copied into `D.z`. -/
theorem prod0_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size) (hA : WinA K)
    {s₀ : State} (hs : Scr s₀ base size) (hM : ModOkA K.M size C.p s₀.mem base)
    (hz : wordsVal s₀.mem base (K.tblPt 1).z K.M.n < C.p) :
    WP isa (.block (copy K.M.n K.D.z (K.tblPt 1).z)) s₀ (PreInv K C base size s₀ 0) := by
  obtain Dz : K.D.z ∈ winWs K := winOther_ws K _ (by win_mem)
  obtain z1 := tz_same hL (m := 1) (Nat.le_refl _) (by omega_arith)
  refine WP.mono (slotCopy_ok hL hA hs hM Dz z1.1 (z1.2.2 1 (Nat.le_refl _) (by omega_arith)).symm)
    fun s₁ ⟨s₁s, k₁, U₁, M₁, v₁, e₁⟩ => ⟨s₁s, k₁, U₁, M₁, fun j h1 h0 => ?_, fun j h1 h0 => ?_,
      fun x hx hne _ => e₁ x hx (hne 1 (Nat.le_refl _) (Nat.le_refl _))⟩
  · obtain rfl : j = 1 := by omega_arith
    rw [prodSl_one, v₁]; exact hz
  · obtain rfl : j = 1 := by omega_arith
    rw [prodSl_one, tmv_eq v₁]; rfl

/-- `c_2 … c_8`, from the table's `Z`. -/
theorem prod_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {P : Point C} {s₀ s₁ : State} (hT : TblOk K C base P 8 s₀)
    (I₀ : PreInv K C base size s₀ 0 s₁) :
    WP isa (WinCfg.seqRange (WinCfg.prodStep K) 7) s₁ (PreInv K C base size s₀ 7) := by
  refine seqRange_ok (N := 7) (fun i hi t I => ?_) 7 (Nat.le_refl _) s₁ I₀
  obtain hsa := tz_same hL (m := i + 2) (by omega_arith) (by omega_arith)
  obtain ltb : wordsVal t.mem base (K.tblPt (i + 2)).z K.M.n < C.p := by
    rw [I.same _ hsa.1 (fun j h1 hj => hsa.2.2 j h1 (by omega_arith)) hsa.2.1]
    exact (hT (i + 2) (by omega_arith) (by omega_arith)).1 _ (by simp)
  obtain hoW : WinCfg.prodSl K (i + 2) ∈ winOther K := prodSl_other (by omega_arith) (by omega_arith)
  obtain haS : WinCfg.prodSl K (i + 1) ∈ winOther K := prodSl_other (by omega_arith) (by omega_arith)
  refine WP.mono (mulTb_ok hL hA hp I.scr I.mod hoW haS hsa.1
    (prodSl_ne_DE hL (j := i + 1) (by omega_arith) (by omega_arith)).2.2 hsa.2.1
    (I.lt (i + 1) (by omega_arith) (by omega_arith)) ltb)
    fun u ⟨su, ku, Uu, Mu, lu, vu, eu⟩ => ?_
  obtain ne : ∀ j, 1 ≤ j → j ≤ i + 1 → WinCfg.prodSl K j ≠ WinCfg.prodSl K (i + 2) := fun j h1 hj h =>
    absurd (prodSl_inj hL h1 (by omega_arith) (by omega_arith) (by omega_arith) h) (by omega_arith)
  obtain ny : ∀ j, 1 ≤ j → j ≤ 8 → WinCfg.prodSl K j ≠ K.D.y := fun j h1 h8 =>
    (prodSl_ne_DE hL h1 h8).2.2
  refine ⟨su, I.keep.trans ku, (I.unch.trans Uu).mono winW_append, Mu, fun j h1 hj => ?_,
    fun j h1 hj => ?_, fun x hx hne hxy => ?_⟩
  · rcases Nat.lt_or_ge j (i + 2) with hj' | hj'
    · rw [eu _ (winOther_mem (prodSl_other h1 (by omega_arith))) (ne j h1 (by omega_arith))
        (ny j h1 (by omega_arith))]
      exact I.lt j h1 (by omega_arith)
    · obtain rfl : j = i + 2 := by omega_arith
      exact lu
  · rcases Nat.lt_or_ge j (i + 2) with hj' | hj'
    · rw [tmv_congr (eu _ (winOther_mem (prodSl_other h1 (by omega_arith))) (ne j h1 (by omega_arith))
        (ny j h1 (by omega_arith)))]
      exact I.val j h1 (by omega_arith)
    · obtain rfl : j = i + 2 := by omega_arith
      rw [vu, I.val (i + 1) (by omega_arith) (by omega_arith),
        tmv_congr (I.same _ hsa.1 (fun j h1 hj => hsa.2.2 j h1 (by omega_arith)) hsa.2.1)]
      rfl
  · rw [eu x hx (hne _ (by omega_arith) (by omega_arith)) hxy]
    exact I.same x hx (fun j h1 hj => hne j h1 (by omega_arith)) hxy

/-! ## Back from entry `8` -/

section Coords
variable {K : WinCfg} {size : Nat} (hL : WinLay K size)
include hL

theorem txy {m m' : Nat} : (K.tblPt m).x ≠ (K.tblPt m').y := by
  rw [tblPt_x, tblPt_y]; exact hL.tbl_ne₂ (by omega_arith)

theorem tyx {m m' : Nat} : (K.tblPt m).y ≠ (K.tblPt m').x := fun h => txy hL h.symm

theorem txx {m m' : Nat} (h1 : 1 ≤ m) (h1' : 1 ≤ m') (h : m ≠ m') : (K.tblPt m).x ≠ (K.tblPt m').x := by
  rw [tblPt_x, tblPt_x]; exact hL.tbl_ne₂ (by omega_arith)

theorem tyy {m m' : Nat} (h1 : 1 ≤ m) (h1' : 1 ≤ m') (h : m ≠ m') : (K.tblPt m).y ≠ (K.tblPt m').y := by
  rw [tblPt_y, tblPt_y]; exact hL.tbl_ne₂ (by omega_arith)

theorem tzx {m m' : Nat} : (K.tblPt m).z ≠ (K.tblPt m').x := by
  rw [tblPt_z, tblPt_x]; exact hL.tbl_ne₂ (by omega_arith)

theorem tzy {m m' : Nat} : (K.tblPt m).z ≠ (K.tblPt m').y := by
  rw [tblPt_z, tblPt_y]; exact hL.tbl_ne₂ (by omega_arith)

/-- `D.x`, `E.x` and `D.y` are not table slots. -/
theorem DE_tbl {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8) :
    ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], K.D.x ≠ y ∧ K.E.x ≠ y ∧ K.D.y ≠ y := fun y hy =>
  ⟨other_ne_tbl hL (by win_mem) h1 h8 hy, other_ne_tbl hL (by win_mem) h1 h8 hy,
    other_ne_tbl hL (by win_mem) h1 h8 hy⟩

/-- The slot of `c_j`: not `D.x`, `E.x`, `D.y` or a table slot. -/
theorem prodSl_ne {j : Nat} (h1 : 1 ≤ j) (h8 : j ≤ 8) {m : Nat} (hm1 : 1 ≤ m) (hm8 : m ≤ 8) :
    WinCfg.prodSl K j ≠ K.D.x ∧ WinCfg.prodSl K j ≠ K.E.x ∧ WinCfg.prodSl K j ≠ K.D.y ∧
      WinCfg.prodSl K j ≠ (K.tblPt m).x ∧ WinCfg.prodSl K j ≠ (K.tblPt m).y ∧
      WinCfg.prodSl K j ≠ (K.tblPt m).z := by
  obtain o := prodSl_other (K := K) h1 h8
  obtain d := prodSl_ne_DE hL h1 h8
  exact ⟨d.1, d.2.1, d.2.2, other_ne_tbl hL o hm1 hm8 (by simp), other_ne_tbl hL o hm1 hm8 (by simp),
    other_ne_tbl hL o hm1 hm8 (by simp)⟩

end Coords

theorem prodSl_slots {K : WinCfg} {j : Nat} (h1 : 1 ≤ j) (h8 : j ≤ 8) : WinCfg.prodSl K j ∈ winSlots K :=
  winOther_mem (prodSl_other h1 h8)

theorem cprod_succ {C : Curve} (Z : Nat → Fe C) {m : Nat} (h : 2 ≤ m) :
    cprod Z m = cprod Z (m - 1) * Z m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega_arith⟩
  rfl

theorem cprod_ne_zero {C : Curve} (hC : Law C) {Z : Nat → Fe C} (hZ : ∀ j, 1 ≤ j → j ≤ 8 → Z j ≠ 0) :
    ∀ m, 1 ≤ m → m ≤ 8 → cprod Z m ≠ 0
  | 0, h, _ => absurd h (by omega_arith)
  | 1, _, _ => hZ 1 (Nat.le_refl _) (by omega_arith)
  | j + 2, _, h8 => hC.mul_ne_zero (cprod_ne_zero hC hZ (j + 1) (by omega_arith) (by omega_arith)) (hZ _ (by omega_arith) h8)

/-- The table and the products as the inversion leaves them: `c_1 … c_7`, and
the entries' `X`, `Y`, `Z` (nonzero). -/
structure BackStart (K : WinCfg) (C : Curve) (base : Addr) (u₀ : State) (X Y Z : Nat → Fe C) : Prop where
  c : ∀ j, 1 ≤ j → j ≤ 7 → wordsVal u₀.mem base (WinCfg.prodSl K j) K.M.n < C.p ∧
    tmv C K.M.n base u₀ (WinCfg.prodSl K j) = cprod Z j
  x : ∀ j, 1 ≤ j → j ≤ 8 → wordsVal u₀.mem base (K.tblPt j).x K.M.n < C.p ∧
    tmv C K.M.n base u₀ (K.tblPt j).x = X j
  y : ∀ j, 1 ≤ j → j ≤ 8 → wordsVal u₀.mem base (K.tblPt j).y K.M.n < C.p ∧
    tmv C K.M.n base u₀ (K.tblPt j).y = Y j
  z : ∀ j, 1 ≤ j → j ≤ 8 → wordsVal u₀.mem base (K.tblPt j).z K.M.n < C.p ∧
    tmv C K.M.n base u₀ (K.tblPt j).z = Z j
  nz : ∀ j, 1 ≤ j → j ≤ 8 → Z j ≠ 0

/-- After entries `8 … 9 - i`: `c_{8-i}^(p-2)` in `E.x`, those entries' `X`,
`Y` by their `Z^(p-2)`, and the other slots but `D.x` and `D.y` as at `u₀`. -/
structure BackInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (u₀ : State) (X Y Z : Nat → Fe C)
    (i : Nat) (t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs (clob K.M.n) u₀ t
  unch : Unch base (winW K) u₀.mem t.mem
  mod : ModOkA K.M size C.p t.mem base
  ex_lt : wordsVal t.mem base K.E.x K.M.n < C.p
  ex : tmv C K.M.n base t K.E.x = cprod Z (8 - i) ^ (C.p - 2)
  done : ∀ j, 8 - i < j → j ≤ 8 →
    wordsVal t.mem base (K.tblPt j).x K.M.n < C.p ∧ wordsVal t.mem base (K.tblPt j).y K.M.n < C.p ∧
    tmv C K.M.n base t (K.tblPt j).x = X j * Z j ^ (C.p - 2) ∧
    tmv C K.M.n base t (K.tblPt j).y = Y j * Z j ^ (C.p - 2)
  same : ∀ x ∈ winSlots K, x ≠ K.D.x → x ≠ K.E.x → x ≠ K.D.y →
    (∀ j, 8 - i < j → j ≤ 8 → x ≠ (K.tblPt j).x ∧ x ≠ (K.tblPt j).y) →
    wordsVal t.mem base x K.M.n = wordsVal u₀.mem base x K.M.n

/-- Entry `m = 8 - i` (`2 ≤ m`). -/
theorem back_step {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {u₀ : State} {X Y Z : Nat → Fe C}
    (B : BackStart K C base u₀ X Y Z) {i : Nat} (hi : i < 7) {t : State}
    (I : BackInv K C base size u₀ X Y Z i t) :
    WP isa (WinCfg.backStep K (8 - i)) t (BackInv K C base size u₀ X Y Z (i + 1)) := by
  generalize hm : 8 - i = m
  have hm2 : 2 ≤ m := by omega_arith
  have hm8 : m ≤ 8 := by omega_arith
  have hmi : 8 - (i + 1) = m - 1 := by omega_arith
  have dDE := DE_ne hL
  have tm := DE_tbl hL (m := m) (by omega_arith) hm8
  have pc := prodSl_ne hL (j := m - 1) (by omega_arith) (by omega_arith) (m := m) (by omega_arith) hm8
  have Dw : K.D.x ∈ winWs K := winOther_ws K _ (by win_mem)
  have Ew : K.E.x ∈ winWs K := winOther_ws K _ (by win_mem)
  have st := tblPt_slots K (m := m) (by omega_arith) hm8
  have xw := (st _ (by simp : (K.tblPt m).x ∈ _)).2
  have yw := (st _ (by simp : (K.tblPt m).y ∈ _)).2
  have zS := (st _ (by simp : (K.tblPt m).z ∈ _)).1
  -- What is not done at `t`.
  have nd : ∀ {x}, x ∈ winSlots K → x ≠ K.D.x → x ≠ K.E.x → x ≠ K.D.y → (∀ j, m < j → j ≤ 8 →
      x ≠ (K.tblPt j).x ∧ x ≠ (K.tblPt j).y) → wordsVal t.mem base x K.M.n = wordsVal u₀.mem base x K.M.n :=
    fun hx h1 h2 h3 h4 => I.same _ hx h1 h2 h3 fun j hj hj' => h4 j (by omega_arith) hj'
  have cS := prodSl_slots (K := K) (j := m - 1) (by omega_arith) (by omega_arith)
  have ec : wordsVal t.mem base (WinCfg.prodSl K (m - 1)) K.M.n =
      wordsVal u₀.mem base (WinCfg.prodSl K (m - 1)) K.M.n :=
    nd cS pc.1 pc.2.1 pc.2.2.1 fun j hj hj' =>
      have h := prodSl_ne hL (j := m - 1) (by omega_arith) (by omega_arith) (m := j) (by omega_arith) hj'
      ⟨h.2.2.2.1, h.2.2.2.2.1⟩
  have ez : wordsVal t.mem base (K.tblPt m).z K.M.n = wordsVal u₀.mem base (K.tblPt m).z K.M.n :=
    nd zS (tm _ (by simp)).1.symm (tm _ (by simp)).2.1.symm (tm _ (by simp)).2.2.symm
      fun j _ _ => ⟨tzx hL, tzy hL⟩
  have ex0 : wordsVal t.mem base (K.tblPt m).x K.M.n = wordsVal u₀.mem base (K.tblPt m).x K.M.n :=
    nd (winWs_slots K _ xw) (tm _ (by simp)).1.symm (tm _ (by simp)).2.1.symm (tm _ (by simp)).2.2.symm
      fun j hj _ => ⟨txx hL (by omega_arith) (by omega_arith) (by omega_arith), txy hL⟩
  have ey0 : wordsVal t.mem base (K.tblPt m).y K.M.n = wordsVal u₀.mem base (K.tblPt m).y K.M.n :=
    nd (winWs_slots K _ yw) (tm _ (by simp)).1.symm (tm _ (by simp)).2.1.symm (tm _ (by simp)).2.2.symm
      fun j hj _ => ⟨tyx hL, tyy hL (by omega_arith) (by omega_arith) (by omega_arith)⟩
  have hcm := cprod_succ Z hm2
  have nz := cprod_ne_zero hC B.nz (m - 1) (by omega_arith) (by omega_arith)
  obtain ⟨tr1, tr2⟩ := trick_step hC nz (B.nz m (by omega_arith) hm8)
  rw [← hcm] at tr1 tr2
  rw [WinCfg.backStep]
  -- `D.x = E.x c_{m-1}`.
  refine WP.seq (WP.mono (slotMul1_ok hL hA hp I.scr I.mod (by win_mem) (List.mem_append_right _ (by win_mem))
    (List.mem_append_right _ (prodSl_other (by omega_arith) (by omega_arith))) I.ex_lt
    (by rw [ec]; exact (B.c _ (by omega_arith) (by omega_arith)).1)) fun t₁ ⟨s₁, k₁, U₁, M₁, l₁, v₁, e₁⟩ => ?_)
  have ex₁ := e₁ _ (winWs_slots K _ Ew) (Ne.symm dDE.1)
  -- `E.x = E.x Z_m`.
  refine WP.seq (WP.mono (mulTb_ok hL hA hp s₁ M₁ (by win_mem) (by win_mem) zS dDE.2.2.symm
    (tm _ (by simp)).2.2.symm (by rw [ex₁]; exact I.ex_lt)
    (by rw [e₁ _ zS (tm _ (by simp)).1.symm, ez]; exact (B.z m (by omega_arith) hm8).1))
    fun t₂ ⟨s₂, k₂, U₂, M₂, l₂, v₂, e₂⟩ => ?_)
  have dx₂ := e₂ _ (winWs_slots K _ Dw) dDE.1 dDE.2.1.symm
  have xx₂ : wordsVal t₂.mem base (K.tblPt m).x K.M.n = wordsVal u₀.mem base (K.tblPt m).x K.M.n := by
    rw [e₂ _ (winWs_slots K _ xw) (tm _ (by simp)).2.1.symm (tm _ (by simp)).2.2.symm,
      e₁ _ (winWs_slots K _ xw) (tm _ (by simp)).1.symm, ex0]
  -- `X_m = X_m D.x`.
  refine WP.seq (WP.mono (mulTx_ok hL hA hp s₂ M₂ xw (by win_mem) (tm _ (by simp)).2.2.symm
    dDE.2.1.symm (by rw [xx₂]; exact (B.x m (by omega_arith) hm8).1) (by rw [dx₂]; exact l₁))
    fun t₃ ⟨s₃, k₃, U₃, M₃, l₃, v₃, e₃⟩ => ?_)
  have dx₃ := e₃ _ (winWs_slots K _ Dw) (tm _ (by simp)).1 dDE.2.1.symm
  have yy₃ : wordsVal t₃.mem base (K.tblPt m).y K.M.n = wordsVal u₀.mem base (K.tblPt m).y K.M.n := by
    rw [e₃ _ (winWs_slots K _ yw) (tyx hL) (tm _ (by simp)).2.2.symm,
      e₂ _ (winWs_slots K _ yw) (tm _ (by simp)).2.1.symm (tm _ (by simp)).2.2.symm,
      e₁ _ (winWs_slots K _ yw) (tm _ (by simp)).1.symm, ey0]
  -- `Y_m = Y_m D.x`.
  refine WP.mono (mulTx_ok hL hA hp s₃ M₃ yw (by win_mem) (tm _ (by simp)).2.2.symm
    dDE.2.1.symm (by rw [yy₃]; exact (B.y m (by omega_arith) hm8).1)
    (by rw [dx₃, dx₂]; exact l₁)) fun t₄ ⟨s₄, k₄, U₄, M₄, l₄, v₄, e₄⟩ => ?_
  -- Every slot but the five written keeps its number.
  have keep4 : ∀ x ∈ winSlots K, x ≠ K.D.x → x ≠ K.E.x → x ≠ K.D.y → x ≠ (K.tblPt m).x →
      x ≠ (K.tblPt m).y → wordsVal t₄.mem base x K.M.n = wordsVal t.mem base x K.M.n :=
    fun x hx h1 h2 hy h3 h4 => by rw [e₄ x hx h4 hy, e₃ x hx h3 hy, e₂ x hx h2 hy, e₁ x hx h1]
  have vD : tmv C K.M.n base t₁ K.D.x = Z m ^ (C.p - 2) := by
    rw [v₁, I.ex, hm, tmv_congr ec, (B.c _ (by omega_arith) (by omega_arith)).2]; exact tr1
  have vE : tmv C K.M.n base t₂ K.E.x = cprod Z (m - 1) ^ (C.p - 2) := by
    rw [v₂, tmv_congr ex₁, I.ex, hm, tmv_congr (e₁ _ zS (tm _ (by simp)).1.symm), tmv_congr ez,
      (B.z m (by omega_arith) hm8).2]; exact tr2
  have ex₄ : wordsVal t₄.mem base K.E.x K.M.n = wordsVal t₂.mem base K.E.x K.M.n := by
    rw [e₄ _ (winWs_slots K _ Ew) (tm _ (by simp)).2.1 dDE.2.2.symm,
      e₃ _ (winWs_slots K _ Ew) (tm _ (by simp)).2.1 dDE.2.2.symm]
  have xx₄ : wordsVal t₄.mem base (K.tblPt m).x K.M.n = wordsVal t₃.mem base (K.tblPt m).x K.M.n :=
    e₄ _ (winWs_slots K _ xw) (txy hL) (tm _ (by simp)).2.2.symm
  refine ⟨s₄, I.keep.trans (k₁.trans (k₂.trans (k₃.trans k₄))),
    (I.unch.trans (U₁.trans (U₂.trans (U₃.trans U₄)))).mono fun w hw => ?_, M₄,
    by rw [ex₄]; exact l₂, by rw [hmi, tmv_congr ex₄, vE], fun j hj hj8 => ?_, fun x hx h1 h2 hy h3 => ?_⟩
  · simp only [List.mem_append] at hw; rcases hw with hw | hw | hw | hw | hw <;> exact hw
  · rcases Nat.lt_or_ge m j with hj' | hj'
    · obtain ⟨a1, a2, a3, a4⟩ := I.done j (by omega_arith) hj8
      have tj := DE_tbl hL (m := j) (by omega_arith) hj8
      have ex : wordsVal t₄.mem base (K.tblPt j).x K.M.n = wordsVal t.mem base (K.tblPt j).x K.M.n :=
        keep4 _ (tblPt_slots K (m := j) (by omega_arith) hj8 _ (by simp)).1 (tj _ (by simp)).1.symm
          (tj _ (by simp)).2.1.symm (tj _ (by simp)).2.2.symm
          (txx hL (by omega_arith) (by omega_arith) (by omega_arith)) (txy hL)
      have ey : wordsVal t₄.mem base (K.tblPt j).y K.M.n = wordsVal t.mem base (K.tblPt j).y K.M.n :=
        keep4 _ (tblPt_slots K (m := j) (by omega_arith) hj8 _ (by simp)).1 (tj _ (by simp)).1.symm
          (tj _ (by simp)).2.1.symm (tj _ (by simp)).2.2.symm
          (tyx hL) (tyy hL (by omega_arith) (by omega_arith) (by omega_arith))
      exact ⟨by rw [ex]; exact a1, by rw [ey]; exact a2, by rw [tmv_congr ex]; exact a3,
        by rw [tmv_congr ey]; exact a4⟩
    · obtain rfl : j = m := by omega_arith
      refine ⟨by rw [xx₄]; exact l₃, l₄, ?_, ?_⟩
      · rw [tmv_congr xx₄, v₃, tmv_congr xx₂, (B.x j (by omega_arith) hj8).2, tmv_congr dx₂, vD]
      · rw [v₄, tmv_congr yy₃, (B.y j (by omega_arith) hj8).2, tmv_congr dx₃, tmv_congr dx₂, vD]
  · have hm' := h3 m (by omega_arith) hm8
    rw [keep4 x hx h1 h2 hy hm'.1 hm'.2]
    exact I.same x hx h1 h2 hy fun j hj hj' => h3 j (by omega_arith) hj'

/-- The entries' `X` and `Y` by their `Z^(p-2)`: entries `8 … 2`, from
`c_8^(p-2)` in `E.x`. -/
theorem back_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {u₀ : State} {X Y Z : Nat → Fe C}
    (B : BackStart K C base u₀ X Y Z) (hs : Scr u₀ base size) (hM : ModOkA K.M size C.p u₀.mem base)
    (hel : wordsVal u₀.mem base K.E.x K.M.n < C.p)
    (hev : tmv C K.M.n base u₀ K.E.x = cprod Z 8 ^ (C.p - 2)) :
    WP isa (WinCfg.seqRange (fun i => WinCfg.backStep K (8 - i)) 7) u₀
      (BackInv K C base size u₀ X Y Z 7) :=
  seqRange_ok (N := 7) (fun i hi t I => back_step hL hA hp hC B hi I) 7 (Nat.le_refl _) u₀
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, hM, hel, hev, fun j hj hj' => absurd hj' (by omega_arith),
      fun _ _ _ _ _ _ => rfl⟩

/-- Entry `1`, by `E.x = Z_1^(p-2)`: every entry's `X` and `Y` by its `Z^(p-2)`. -/
theorem backOne_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {u₀ : State} {X Y Z : Nat → Fe C}
    (B : BackStart K C base u₀ X Y Z) {t : State} (I : BackInv K C base size u₀ X Y Z 7 t) :
    WP isa (WinCfg.backOne K) t fun t => Scr t base size ∧
      KeepRegs (clob K.M.n) u₀ t ∧ Unch base (winW K) u₀.mem t.mem ∧ ModOkA K.M size C.p t.mem base ∧
      ∀ j, 1 ≤ j → j ≤ 8 →
        wordsVal t.mem base (K.tblPt j).x K.M.n < C.p ∧ wordsVal t.mem base (K.tblPt j).y K.M.n < C.p ∧
        tmv C K.M.n base t (K.tblPt j).x = X j * Z j ^ (C.p - 2) ∧
        tmv C K.M.n base t (K.tblPt j).y = Y j * Z j ^ (C.p - 2) := by
  obtain dDE := DE_ne hL
  obtain Ew : K.E.x ∈ winWs K := winOther_ws K _ (by win_mem)
  obtain st := tblPt_slots K (m := 1) (Nat.le_refl _) (by omega_arith)
  obtain xw := (st _ (by simp : (K.tblPt 1).x ∈ _)).2
  obtain yw := (st _ (by simp : (K.tblPt 1).y ∈ _)).2
  obtain t1 := DE_tbl hL (m := 1) (Nat.le_refl _) (by omega_arith)
  obtain ex1 : wordsVal t.mem base (K.tblPt 1).x K.M.n = wordsVal u₀.mem base (K.tblPt 1).x K.M.n :=
    I.same _ (winWs_slots K _ xw) (t1 _ (by simp)).1.symm (t1 _ (by simp)).2.1.symm (t1 _ (by simp)).2.2.symm
      fun j hj _ => ⟨txx hL (by omega_arith) (by omega_arith) (by omega_arith), txy hL⟩
  obtain ey1 : wordsVal t.mem base (K.tblPt 1).y K.M.n = wordsVal u₀.mem base (K.tblPt 1).y K.M.n :=
    I.same _ (winWs_slots K _ yw) (t1 _ (by simp)).1.symm (t1 _ (by simp)).2.1.symm (t1 _ (by simp)).2.2.symm
      fun j hj _ => ⟨tyx hL, tyy hL (by omega_arith) (by omega_arith) (by omega_arith)⟩
  rw [WinCfg.backOne]
  refine WP.seq (WP.mono (mulTx_ok hL hA hp I.scr I.mod xw (by win_mem) (t1 _ (by simp)).2.2.symm
    dDE.2.2.symm (by rw [ex1]; exact (B.x 1 (Nat.le_refl _) (by omega_arith)).1) I.ex_lt)
    fun t₁ ⟨s₁, k₁, U₁, M₁, l₁, v₁, e₁⟩ => ?_)
  obtain ee₁ := e₁ _ (winWs_slots K _ Ew) (t1 _ (by simp)).2.1 dDE.2.2.symm
  refine WP.mono (mulTx_ok hL hA hp s₁ M₁ yw (by win_mem) (t1 _ (by simp)).2.2.symm
    dDE.2.2.symm
    (by rw [e₁ _ (winWs_slots K _ yw) (tyx hL) (t1 _ (by simp)).2.2.symm, ey1];
        exact (B.y 1 (Nat.le_refl _) (by omega_arith)).1)
    (by rw [ee₁]; exact I.ex_lt)) fun t₂ ⟨s₂, k₂, U₂, M₂, l₂, v₂, e₂⟩ => ?_
  refine ⟨s₂, I.keep.trans (k₁.trans k₂), (I.unch.trans (U₁.trans U₂)).mono fun w hw => ?_, M₂,
    fun j hj hj8 => ?_⟩
  · simp only [List.mem_append] at hw; rcases hw with hw | hw | hw <;> exact hw
  · rcases Nat.lt_or_ge 1 j with hj' | hj'
    · obtain ⟨a1, a2, a3, a4⟩ := I.done j (by omega_arith) hj8
      obtain tj := DE_tbl hL (m := j) (by omega_arith) hj8
      obtain ex : wordsVal t₂.mem base (K.tblPt j).x K.M.n = wordsVal t.mem base (K.tblPt j).x K.M.n := by
        obtain h := (tblPt_slots K (m := j) (by omega_arith) hj8 _ (by simp : (K.tblPt j).x ∈ _)).1
        rw [e₂ _ h (txy hL) (tj _ (by simp)).2.2.symm,
          e₁ _ h (txx hL (by omega_arith) (by omega_arith) (by omega_arith)) (tj _ (by simp)).2.2.symm]
      obtain ey : wordsVal t₂.mem base (K.tblPt j).y K.M.n = wordsVal t.mem base (K.tblPt j).y K.M.n := by
        obtain h := (tblPt_slots K (m := j) (by omega_arith) hj8 _ (by simp : (K.tblPt j).y ∈ _)).1
        rw [e₂ _ h (tyy hL (by omega_arith) (by omega_arith) (by omega_arith)) (tj _ (by simp)).2.2.symm,
          e₁ _ h (tyx hL) (tj _ (by simp)).2.2.symm]
      exact ⟨by rw [ex]; exact a1, by rw [ey]; exact a2, by rw [tmv_congr ex]; exact a3,
        by rw [tmv_congr ey]; exact a4⟩
    · obtain rfl : j = 1 := by omega_arith
      obtain xx₂ := e₂ _ (winWs_slots K _ xw) (txy hL) (t1 _ (by simp)).2.2.symm
      refine ⟨by rw [xx₂]; exact l₁, l₂, ?_, ?_⟩
      · rw [tmv_congr xx₂, v₁, tmv_congr ex1, (B.x 1 (Nat.le_refl _) (by omega_arith)).2, I.ex]; rfl
      · rw [v₂, tmv_congr (e₁ _ (winWs_slots K _ yw) (tyx hL) (t1 _ (by simp)).2.2.symm), tmv_congr ey1,
          (B.y 1 (Nat.le_refl _) (by omega_arith)).2, tmv_congr ee₁, I.ex]; rfl

/-! ## Every `Z` one, and the table -/

/-- The entries' `Z` set to one: those of `1 … i`. -/
theorem ones_ok {K : WinCfg} {size : Nat} (hL : WinLay K size) (hA : WinA K) {base : Addr} {x : Nat}
    (hx : x < 2 ^ (64 * K.M.n)) :
    ∀ i ≤ 8, ∀ s : State, Scr s base size →
      WP isa (.block ((List.range i).flatMap fun j => setConst K.M.n (K.tblPt (j + 1)).z x)) s fun t =>
        Scr t base size ∧ KeepRegs [.x1] s t ∧ Unch base (winW K) s.mem t.mem ∧
        (∀ j, 1 ≤ j → j ≤ i → wordsVal t.mem base (K.tblPt j).z K.M.n = x) ∧
        ∀ y ∈ winSlots K, (∀ j, 1 ≤ j → j ≤ i → y ≠ (K.tblPt j).z) →
          wordsVal t.mem base y K.M.n = wordsVal s.mem base y K.M.n := by
  intro i hi s hs
  refine block_range_ok (N := 8) (Inv := fun i t => Scr t base size ∧ KeepRegs [.x1] s t ∧
      Unch base (winW K) s.mem t.mem ∧ (∀ j, 1 ≤ j → j ≤ i → wordsVal t.mem base (K.tblPt j).z K.M.n = x) ∧
      ∀ y ∈ winSlots K, (∀ j, 1 ≤ j → j ≤ i → y ≠ (K.tblPt j).z) →
        wordsVal t.mem base y K.M.n = wordsVal s.mem base y K.M.n)
    (fun i hi t ⟨st, kt, Ut, vt, et⟩ => ?_) i hi s
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, fun j h1 h0 => absurd h1 (by omega_arith), fun _ _ _ => rfl⟩
  obtain zs := tblPt_slots K (m := i + 1) (by omega_arith) (by omega_arith) _ (by simp : (K.tblPt (i + 1)).z ∈ _)
  refine WP.mono (setConst_ok st (n := K.M.n) (o := (K.tblPt (i + 1)).z) (hL.lay.le _ zs.1) (hA.sl _ zs.1) hx)
    fun u ⟨eu, ku, Ou⟩ => ?_
  have hn := st.nowrap
  obtain same : ∀ y ∈ winSlots K, y ≠ (K.tblPt (i + 1)).z →
      wordsVal u.mem base y K.M.n = wordsVal t.mem base y K.M.n := fun y hy hne =>
    Ou.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact hL.lay.apart y _ hy zs.1 hne) (by have := hL.lay.le y hy; omega_arith)
  refine ⟨st.of_keepRegs ku (by decide), kt.trans ku, (Ut.trans Ou.unch).mono fun w hw => ?_,
    fun j h1 hj => ?_, fun y hy hne => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · rw [List.mem_singleton.mp hw]
      simp only [winW, List.mem_append, List.mem_map]
      exact Or.inl ⟨_, zs.2, rfl⟩
  · rcases Nat.lt_or_ge j (i + 1) with hj' | hj'
    · rw [same _ (tblPt_slots K (m := j) h1 (by omega_arith) _ (by simp : (K.tblPt j).z ∈ _)).1
        (fun h => by rw [tblPt_z, tblPt_z] at h; exact hL.tbl_ne₂ (by omega_arith) h)]
      exact vt j h1 (by omega_arith)
    · obtain rfl : j = i + 1 := by omega_arith
      exact eu
  · rw [same y hy (hne _ (by omega_arith) (Nat.le_refl _))]
    exact et y hy fun j h1 hj => hne j h1 (by omega_arith)

/-- What the inversion `inv` does: `E.x = R.z^(p-2)`, writing `IW`: `E.x`, the
temporary area, and areas apart from the modulus and the window's slots. -/
structure InvSpecW (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (inv : Prog isa)
    (RC : List Reg) (IW : List (Nat × Nat)) : Prop where
  ok : ∀ t : State, Scr t base size → ModOkA K.M size C.p t.mem base →
    wordsVal t.mem base K.R.z K.M.n < C.p → WP isa inv t fun t' =>
      KeepRegs RC t t' ∧ Unch base IW t.mem t'.mem ∧
      wordsVal t'.mem base K.E.x K.M.n < C.p ∧
      tmv C K.M.n base t' K.E.x = tmv C K.M.n base t K.R.z ^ (C.p - 2)
  w : ∀ w ∈ IW, w = (K.E.x, 8 * K.M.n) ∨ w = (K.M.tmp, 8 * K.M.n) ∨ w = (K.neg, 8 * K.M.n) ∨
    ((K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo) ∧
      ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
  bits : ∀ w ∈ IW, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits

theorem InvSpecW.same {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} {inv : Prog isa}
    {RC : List Reg} {IW : List (Nat × Nat)} (h : InvSpecW K C base size inv RC IW) (hL : WinLay K size) {m m' : Mem}
    (hU : Unch base IW m m') (hn : base.toNat + size ≤ 2 ^ 64) {x : Nat} (hx : x ∈ winSlots K)
    (hne : x ≠ K.E.x) (hneg : x ≠ K.neg) : wordsVal m' base x K.M.n = wordsVal m base x K.M.n :=
  hU.wordsVal (fun w hw => by
    rcases h.w w hw with rfl | rfl | rfl | ⟨-, h⟩
    · exact hL.lay.apart x _ hx (winOther_mem (by win_mem)) hne
    · exact hL.lay.tmp x hx
    · exact hL.lay.apart x _ hx (winOther_mem (by win_mem)) hneg
    · exact h x hx) (by have := hL.lay.le x hx; omega_arith)

theorem InvSpecW.mo {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} {inv : Prog isa}
    {RC : List Reg} {IW : List (Nat × Nat)} (h : InvSpecW K C base size inv RC IW) (hL : WinLay K size) {mem : Mem}
    (hM : ModOkA K.M size C.p mem base) : ∀ w ∈ IW, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  rcases h.w w hw with rfl | rfl | rfl | ⟨h, -⟩
  · have := hL.lay.mo K.E.x (winOther_mem (by win_mem)); dsimp only; omega_arith
  · have := hM.sep; dsimp only; omega_arith
  · have := hL.lay.mo K.neg (winOther_mem (by win_mem)); dsimp only; omega_arith
  · exact h

/-- The table into affine coordinates, for entries other than `O`. -/
theorem normTbl_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size) (hA : WinA K)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C} (hpn : C.p < 2 ^ (64 * K.M.n))
    (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hne : ∀ m, 1 ≤ m → m ≤ 8 → mul m P ≠ .infinity) {inv : Prog isa} {RC : List Reg}
    {IW : List (Nat × Nat)} (hI : InvSpecW K C base size inv RC IW) (hRC : ∀ r ∈ clob K.M.n, r ∈ RC)
    (hx1 : Reg.x1 ∈ RC) (hx0 : Reg.x0 ∉ RC) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) (hT : TblOk K C base P 8 s) :
    WP isa (WinCfg.normTbl K inv) s fun s' => Scr s' base size ∧ KeepRegs RC s s' ∧
      Unch base (winW K ++ IW) s.mem s'.mem ∧ ModOkA K.M size C.p s'.mem base ∧
      TblOkR K C base (RepA C) P 8 s' := by
  have hn := hs.nowrap
  rw [WinCfg.normTbl]
  refine WP.seq (WP.mono (prod0_ok hL hA hs hM ((hT 1 (Nat.le_refl _) (by omega_arith)).1 _ (by simp)))
    fun s₁ I₀ => ?_)
  refine WP.seq (WP.mono (prod_ok hL hA hp hT I₀) fun t₇ I₇ => ?_)
  refine WP.seq (WP.mono (hI.ok t₇ I₇.scr I₇.mod (I₇.lt 8 (by omega_arith) (by omega_arith)))
    fun u₀ ⟨Ku, Uu, lu, vu⟩ => ?_)
  obtain hsu := I₇.scr.of_keepRegs Ku hx0
  obtain Mu := I₇.mod.unch Uu (hI.mo hL I₇.mod) hn
  -- The table and the products at `u₀`.
  obtain tsame : ∀ {m}, 1 ≤ m → m ≤ 8 → ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z],
      wordsVal u₀.mem base y K.M.n = wordsVal s.mem base y K.M.n := fun h1 h8 y hy => by
    obtain ys := (tblPt_slots K h1 h8 y hy).1
    rw [hI.same hL Uu hn ys (DE_tbl hL h1 h8 y hy).2.1.symm
      (other_ne_tbl hL (by win_mem) h1 h8 hy).symm]
    exact I₇.same y ys (fun j h1' hj => (other_ne_tbl hL (prodSl_other h1' (by omega_arith)) h1 h8 hy).symm)
      (DE_tbl hL h1 h8 y hy).2.2.symm
  obtain B : BackStart K C base u₀ (fun j => tmv C K.M.n base s (K.tblPt j).x)
      (fun j => tmv C K.M.n base s (K.tblPt j).y) (tz K C base s) := by
    refine ⟨fun j h1 h7 => ?_, fun j h1 h8 => ?_, fun j h1 h8 => ?_, fun j h1 h8 => ?_, fun j h1 h8 => ?_⟩
    · have e := hI.same hL Uu hn (prodSl_slots h1 (by omega_arith)) (prodSl_ne_DE hL h1 (by omega_arith)).2.1
        (prodSl_ne_neg hL h1 (by omega_arith))
      rw [e, tmv_congr e]
      exact ⟨I₇.lt j h1 (by omega_arith), I₇.val j h1 (by omega_arith)⟩
    · have e := tsame h1 h8 (K.tblPt j).x (by simp)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h8).1 _ (by simp), rfl⟩
    · have e := tsame h1 h8 (K.tblPt j).y (by simp)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h8).1 _ (by simp), rfl⟩
    · have e := tsame h1 h8 (K.tblPt j).z (by simp)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h8).1 _ (by simp), rfl⟩
    · exact fun h0 => hne j h1 h8 (((hT j h1 h8).2.z_eq_zero_iff).mp h0)
  refine WP.seq (WP.mono (back_ok hL hA hp hC B hsu Mu lu
    (by rw [vu]; exact congrArg (· ^ (C.p - 2)) (I₇.val 8 (by omega_arith) (Nat.le_refl _)))) fun t' I' => ?_)
  refine WP.seq (WP.mono (backOne_ok hL hA hp B I') fun v ⟨sv, kv, Uv, Mv, dv⟩ => ?_)
  refine WP.mono (ones_ok hL hA (x := K.one) (Nat.lt_trans hone_lt hpn) 8 (Nat.le_refl _) v sv)
    fun w ⟨sw, kw, Uw, ow, ew⟩ => ?_
  obtain c1 : ∀ r ∈ [Reg.x1], r ∈ RC := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hx1
  have c2 : ∀ r ∈ clob K.M.n, r ∈ RC := hRC
  obtain U : Unch base (winW K ++ IW) s.mem w.mem :=
    (I₇.unch.trans (Uu.trans (Uv.trans Uw))).mono fun x hx => by
      simp only [List.mem_append] at hx ⊢; rcases hx with hx | hx | hx | hx <;> simp [hx]
  refine ⟨sw, ((I₇.keep.mono c2).trans Ku).trans ((kv.mono c2).trans (kw.mono c1)), U,
    Mv.unch Uw (fun x hx => winW_mo hL Mv x hx) hn, fun j h1 h8 => ?_⟩
  obtain ⟨l1, l2, v1, v2⟩ := dv j h1 h8
  obtain zs := tblPt_slots K (m := j) h1 h8
  obtain ex : wordsVal w.mem base (K.tblPt j).x K.M.n = wordsVal v.mem base (K.tblPt j).x K.M.n :=
    ew _ (zs _ (by simp)).1 fun j' _ _ h => tzx hL h.symm
  obtain ey : wordsVal w.mem base (K.tblPt j).y K.M.n = wordsVal v.mem base (K.tblPt j).y K.M.n :=
    ew _ (zs _ (by simp)).1 fun j' _ _ h => tzy hL h.symm
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex]; exact l1
    · rw [ey]; exact l2
    · rw [ow j h1 h8]; exact hone_lt
  · have hz : tmv C K.M.n base w (K.tblPt j).z = 1 := by
      show toM _ _ _ = 1; rw [ow j h1 h8]; exact hone
    rw [tmv_congr ex, tmv_congr ey, v1, v2, hz]
    exact RepA.of_rep hC (hT j h1 h8).2 (hne j h1 h8)

end VG.Proof.Weierstrass.AArch64

end

end

/-!
# Windows in Jacobian coordinates on AArch64: an iteration

The loop's state with the table affine (`WinStR`), `R = 16 R` in place in
Jacobian coordinates (`quadJ_ok`: two pairs of doublings between `R` and
`D`), and the mixed addition of the affine entry `E` into `D` with the
selection of `E`, `R` or `D` (`sumJ_ok`), for an iteration but the last
(`winStepJ_ok`): as on x86-64 (`Proof/Weierstrass/X86_64/WinJStep.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- `x ∈ l₂` from `h : x ∈ l₁`, for literal lists with `l₁`'s elements in `l₂`: not by
`omega` on the disjunctions, which splits cases exponentially. -/
macro "sub_mem " h:term : tactic => `(tactic| plain_simp_names (
                   refine (show (_ : List _) ⊆ _ from ?_) $h
                   simp only [List.cons_subset, List.nil_subset, List.mem_cons, eq_self_iff_true, true_or,
                     or_true, and_true, and_self]))

/-! ## The loop's state, with the table by any representation -/

/-- The table survives what the loop writes. -/
theorem TblOkR.unch {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {P : Point C} {s s' : State}
    (hT : TblOkR K C base Rp P 8 s) (hU : Unch base (loopW K) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : TblOkR K C base Rp P 8 s' := by
  intro j h1 h8
  obtain T := hT j h1 h8
  obtain e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    obtain hs := (tblPt_slots K h1 h8 x hx).1
    exact hU.wordsVal (tbl_apart_loopW hL h1 h8 hx) (by have := hL.lay.le _ hs; omega_using [hn, this])
  refine ⟨fun x hx => by rw [e x hx]; exact T.1 x hx, ?_⟩
  obtain ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [e x hx]
  rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
  exact T.2

/-- `WinSt`, with the table's entries represented by `Rp`. -/
structure WinStR (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (Rp : Fe C → Fe C → Fe C → Point C → Prop) (P : Point C) (s₀ s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs (combClob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkA K.M size C.p s.mem base
  tbl : TblOkR K C base Rp P 8 s

/-- The state after a change of `loopW` only. -/
theorem WinStR.next {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {P : Point C} {s₀ s s' : State}
    (h : WinStR K C base size Rp P s₀ s) (hs' : Scr s' base size)
    (hk : KeepRegs (combClob K.M.n) s s') (hU : Unch base (loopW K) s.mem s'.mem) :
    WinStR K C base size Rp P s₀ s' :=
  ⟨hs', h.keep.trans hk, (h.unch.trans hU).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact loopW_sub K w hw,
    h.mod.unch hU (fun w hw => winW_mo hL h.mod w (loopW_sub K w hw)) h.scr.nowrap,
    h.tbl.unch hL hU h.scr.nowrap⟩

theorem WinStR.ro_tmv {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {P : Point C} {s₀ s : State}
    (h : WinStR K C base size Rp P s₀ s) (hF : WinFixed K C base s₀ P k) :
    tmv C K.M.n base s K.S.a = Fin.ofNat C.p C.a ∧ tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p C.b ∧
      (∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p) ∧ wordsVal s.mem base K.zero K.M.n = 0 := by
  have hn := h.scr.nowrap
  refine ⟨?_, ?_, fun x hx => ?_, ?_⟩
  · rw [hL.ro_tmv h.unch hn (by simp [winRo])]; exact hF.a
  · rw [hL.ro_tmv h.unch hn (by simp [winRo])]; exact hF.b
  · rw [hL.ro_val h.unch hn hx]; exact hF.ro_lt x hx
  · rw [hL.ro_val h.unch hn (by simp [winRo])]; exact hF.zero

/-! ## Four doublings in place -/

/-- The slots the doublings keep in the environment: `R` and the constants. -/
def dblVR (K : WinCfg) : List Nat := [K.R.x, K.R.y, K.R.z, K.S.a, K.S.b3, K.zero]

/-- What a window's doubling from `p` into `o` must do, the slots `V`
holding their values: change only the registers `combClob` and the loop's
slots, and leave `o` holding `2p` by the numbered doubling. -/
def DblSpec (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (prog : Prog isa) (p o : Pt)
    (V : List Nat) : Prop :=
  ∀ (E : Nat → Fe C) (s : State), Inv K.M base size C.p (· ∈ winSlots K) V E s →
    WP isa prog s fun s' => KeepRegs (clob K.M.n ++ winSaved K.M.n) s s' ∧ Unch base (loopW K) s.mem s'.mem ∧
      ∃ E' : Nat → Fe C, Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
      (E' o.x, E' o.y, E' o.z) = (runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 6,
        runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 7,
        runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 8)

/-- The doublings a window is given (`WinCfg.dblRD`, `dblDR`) do what the
field programs do. -/
def DblsOk (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (dd : Option (Prog isa × Prog isa)) : Prop :=
  ∀ d, dd = some d → DblSpec K C base size d.1 K.R K.D (dblVR K) ∧
    DblSpec K C base size d.2 K.D K.R ([K.D.x, K.D.y, K.D.z] ++ dblVR K)

/-- What a window's mixed addition must do, `R` and `E` holding their values:
change only the registers `combClob` and the loop's slots, and leave `D`
holding `R + E` by the mixed addition. -/
def MaddSpec (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (prog : Prog isa) : Prop :=
  ∀ (E : Nat → Fe C) (s : State), Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) E s →
    WP isa prog s fun s' => KeepRegs (clob K.M.n ++ winSaved K.M.n) s s' ∧ Unch base (loopW K) s.mem s'.mem ∧
      ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) ([K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.R K.E) E' s' ∧
      (∀ x, x ∉ rcbW K.S K.D → E' x = E x) ∧
      (E' K.D.x, E' K.D.y, E' K.D.z) = maddJF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)

/-- The mixed addition a window is given (`WinCfg.maddRD`) does what the
field program does. -/
def MaddOk (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (ma : Option (Prog isa)) : Prop :=
  ∀ m, ma = some m → MaddSpec K C base size m

theorem MaddOk.none {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} : MaddOk K C base size none :=
  fun _ h => by cases h

/-- The field program's doubling from `p` into `o`, on the window's slots. -/
theorem dblN_spec {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt} (hAp : RcbApart K.S p p o)
    (hw : (∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ winSlots K) ∧ (∀ x ∈ rcbW K.S o, x ∈ winOther K) ∧
      ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ winRo K ++ winOther K) {V : List Nat}
    (hV : ∀ x ∈ rcbR K.S p p, x ∈ V) :
    DblSpec K C base size (fprogB K.M (WinCfg.double K p o)) p o V := by
  intro E s hI
  simp only [WinCfg.double, dblJChoice_eq]
  exact WP.mono (winN_ok hL hA hp (dblJChoiceN_ok (K.M.n == 4)) hAp hw.1 hw.2.1 hw.2.2 hI hV)
    fun s' ⟨k, U, E', I, _, v⟩ => ⟨k.mono fun _ h => List.mem_append_left _ h, U, E', I, v⟩

/-- Two doublings, `R` to `D` and back, and one less to count. -/
theorem dblPair_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State}
    {dd : Option (Prog isa × Prog isa)} (hD : DblsOk K C base size dd)
    (hS : WinStR K C base size Rp P s₀ s) {j c e : Nat}
    (hj : j < 2 ^ 32) (hc : 1 ≤ c) (hc2 : c ≤ 2)
    (hx : s.gpr .x19 = BitVec.ofNat 64 (j + 2 ^ 32 * c)) {E : Nat → Fe C}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) E s)
    (hJ : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul e P)) :
    WP isa (WinCfg.jacPair K dd) s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .x19 = BitVec.ofNat 64 (j + 2 ^ 32 * (c - 1)) ∧
      s'.gpr .x2 = BitVec.ofNat 64 (c - 1) ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) E' s' ∧
      InvJ C (E' K.R.x) (E' K.R.y) (E' K.R.z) (mul (4 * e) P) := by
  obtain ⟨aRD, aDR, -⟩ := hL.rcbApart_winJ
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  obtain oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  obtain sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    List.mem_append_right (winRo K) (h x hx)
  obtain w2 := winJ_sl oD (sl _ oR) (sl _ oR)
  obtain w3 := winJ_sl oR (sl _ oD) (sl _ oD)
  obtain hQ := fun (a : Nat) => hC.onCurve_mul hP a
  obtain hRD : DblSpec K C base size (WinCfg.dblRD K dd) K.R K.D (dblVR K) := by
    cases dd with
    | some d => exact (hD d rfl).1
    | none =>
      exact dblN_spec hL hA hp aRD w2
        (by intro x hx; simp only [rcbR, dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
            rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true])
  obtain hDR : DblSpec K C base size (WinCfg.dblDR K dd) K.D K.R ([K.D.x, K.D.y, K.D.z] ++ dblVR K) := by
    cases dd with
    | some d => exact (hD d rfl).2
    | none =>
      exact dblN_spec hL hA hp aDR w3
        (by intro x hx; simp only [rcbR, dblVR, List.cons_append, List.nil_append, List.mem_cons,
              List.not_mem_nil, or_false] at hx ⊢
            rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true])
  rw [WinCfg.jacPair]
  refine WP.seq (WP.mono (hRD E s hI) fun s₂ ⟨k₂, U₂, E₂, I₂, v₂⟩ => ?_)
  obtain S₂ := hS.next hL I₂.scr (k₂.mono fun _ h => winSaved_combClob h) U₂
  obtain J₂ := InvJ.dbl' hC hM3 (hQ e) hJ (v₂.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP] at J₂
  refine WP.seq (WP.mono (hDR E₂ s₂ I₂) fun s₃ ⟨k₃, U₃, E₃, I₃, v₃⟩ => ?_)
  obtain S₃ := S₂.next hL I₃.scr (k₃.mono fun _ h => winSaved_combClob h) U₃
  obtain J₃ := InvJ.dbl' hC hM3 (hQ _) J₂ (v₃.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP, show 2 * (2 * e) = 4 * e by omega_using []] at J₃
  obtain x₃ : s₃.gpr .x19 = BitVec.ofNat 64 (j + 2 ^ 32 * ((c - 1) + 1)) := by
    obtain n19 : Reg.x19 ∉ clob K.M.n ++ winSaved K.M.n := fun h =>
      (List.mem_append.mp h).elim (x19_not_clob _) (not_mem_winSaved (by decide))
    rw [k₃.gpr _ n19, k₂.gpr _ n19, hx, Nat.sub_add_cancel hc]
  refine WP.mono (dblCnt_ok s₃ hj (by omega_using [hc2, hc]) x₃) fun s₄ ⟨x₄, y₄, k₄⟩ => ?_
  obtain hs₄ := S₃.scr.of_keeps k₄ (by decide)
  obtain cc : ∀ r ∈ [Reg.x2, .x19], r ∈ combClob K.M.n := by
    intro r hr
    simp only [combClob, clob, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  refine ⟨S₃.next hL hs₄ ((Keeps.regs k₄).mono cc) (by rw [k₄.mem]; exact Unch.refl _ _ _), x₄, y₄,
    E₃, (I₃.of_mem hs₄ k₄.mem).sub ?_, J₃⟩
  intro x hx
  simp only [dblVR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx ⊢
  rcases hx with h | h | h | h | h | h <;> simp only [h, true_or, or_true]

/-- `R = 16 R` in Jacobian coordinates, in place: from `(X : Y : Z)` standing
for `[e]P` (or with `Z = 0`) to a triple standing for `[16 e]P`. -/
theorem quadJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State}
    {dd : Option (Prog isa × Prog isa)} (hD : DblsOk K C base size dd)
    (hF : WinFixed K C base s₀ P k) (hS : WinStR K C base size Rp P s₀ s) {j : Nat} (hj : j < 2 ^ 32)
    (hx : s.gpr .x19 = BitVec.ofNat 64 j) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.quadJ K dd) s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .x19 = s.gpr .x19 ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (16 * e) P) := by
  obtain ⟨-, -, ro_lt, -⟩ := hS.ro_tmv hL hF
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  obtain V0 : ∀ x ∈ dblVR K, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    all_goals exact ⟨by win_in, ro_lt _ (by simp [winRo])⟩
  obtain I₀ : Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  obtain cc : ∀ r ∈ [Reg.x2, .x19], r ∈ combClob K.M.n := by
    intro r hr
    simp only [combClob, clob, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  rw [WinCfg.quadJ]
  refine WP.seq (WP.mono (dblSet_ok s hx) fun s₂ ⟨x₂, k₂⟩ => ?_)
  obtain hs₂ := hS.scr.of_keeps k₂ (by decide)
  obtain S₂ := hS.next hL hs₂ ((Keeps.regs k₂).mono cc) (by rw [k₂.mem]; exact Unch.refl _ _ _)
  refine WP.mono (WP.loop (M := isa) (fun c t => 1 ≤ c ∧ c ≤ 2 ∧ WinStR K C base size Rp P s₀ t ∧
      t.gpr .x19 = BitVec.ofNat 64 (j + 2 ^ 32 * c) ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) E' t ∧
      InvJ C (E' K.R.x) (E' K.R.y) (E' K.R.z) (mul (4 ^ (2 - c) * e) P))
    (Q := fun t => WinStR K C base size Rp P s₀ t ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) E' t ∧
      InvJ C (E' K.R.x) (E' K.R.y) (E' K.R.z) (mul (16 * e) P))
    (fun c t ⟨hc, hc2, St, xt, Et, It, Jt⟩ => ?_) 2 s₂
    ⟨by decide, Nat.le_refl _, S₂, x₂, tmv C K.M.n base s, (I₀.of_mem hs₂ k₂.mem), by simpa using hR⟩)
    fun s₅ ⟨S₅, x₅, E₅, I₅, J₅⟩ => ?_
  · refine WP.mono (dblPair_ok hL hA hp hC hM3 hP hD St hj hc hc2 xt It Jt)
      fun t' ⟨St', xt', yt', E', It', Jt'⟩ => ?_
    obtain ev : isa.eval (.nonzero .x .x2) t' = some (decide (c - 1 ≠ 0)) := by
      show some (t'.read .x .x2 != 0) = _
      rw [read_x, yt']
      rcases (by omega_using [hc, hc2] : c = 1 ∨ c = 2) with rfl | rfl <;> rfl
    rcases (by omega_using [hc, hc2] : c = 1 ∨ c = 2) with rfl | rfl
    · refine Or.inl ⟨ev, St', by simpa using xt', E', It', ?_⟩
      rw [show 16 * e = 4 * (4 ^ (2 - 1) * e) by simp only [Nat.reduceSub, Nat.reducePow]; omega_using []]
      exact Jt'
    · refine Or.inr ⟨ev, 1, by decide, Nat.le_refl _, by decide, St', xt', E', It', by simpa using Jt'⟩
  · have hRV : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ dblVR K := by
      intro x hx; simp only [dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h]
    refine ⟨S₅, by rw [x₅, hx], fun x hx => I₅.lt x (hRV x hx), ?_⟩
    show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [I₅.val _ (hRV _ (by simp)), I₅.val _ (hRV _ (by simp)), I₅.val _ (hRV _ (by simp))]
    exact J₅

/-! ## The Jacobian sum, selected -/

/-- `R`, `E` and `D`: in the working space and apart, as the selection after
the sum needs. -/
theorem winRED_lay {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size) ∧
    ((K.D.x + 8 * K.M.n ≤ K.D.y ∨ K.D.y + 8 * K.M.n ≤ K.D.x) ∧
      (K.D.x + 8 * K.M.n ≤ K.D.z ∨ K.D.z + 8 * K.M.n ≤ K.D.x) ∧
      (K.D.y + 8 * K.M.n ≤ K.D.z ∨ K.D.z + 8 * K.M.n ≤ K.D.y)) ∧
    ((K.R.x + 8 * K.M.n ≤ K.R.y ∨ K.R.y + 8 * K.M.n ≤ K.R.x) ∧
      (K.R.x + 8 * K.M.n ≤ K.R.z ∨ K.R.z + 8 * K.M.n ≤ K.R.x) ∧
      (K.R.y + 8 * K.M.n ≤ K.R.z ∨ K.R.z + 8 * K.M.n ≤ K.R.y)) ∧
    (∀ d ∈ [K.D.x, K.D.y, K.D.z], ∀ e ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      d + 8 * K.M.n ≤ e ∨ e + 8 * K.M.n ≤ d) ∧
    (∀ d ∈ [K.R.x, K.R.y, K.R.z], ∀ e ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ e ∨ e + 8 * K.M.n ≤ d) := by
  -- The nine slots by index, apart by `Nodup` of a sublist (not by rewriting `Nodup` per pair).
  let L : List Nat := [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z]
  obtain sub : L.Sublist (winOther K) := by
    simp only [L, winOther, rcbW, List.cons_append, List.nil_append]
    repeat first | exact List.nil_sublist _ | apply List.Sublist.cons_cons | apply List.Sublist.cons
  obtain nd := sub.nodup hL.nodup
  obtain hw : ∀ x ∈ L, x ∈ winWs K := fun x hx => winOther_ws K x (sub.subset hx)
  obtain A : ∀ i j (hi : i < 9) (hj : j < 9), i ≠ j → L[i] + 8 * K.M.n ≤ L[j] ∨ L[j] + 8 * K.M.n ≤ L[i] :=
    fun i j hi hj h => hL.apart₂ (hw _ (List.getElem_mem _)) (hw _ (List.getElem_mem _))
      (fun e => h ((nd.getElem_inj (hi := hi) (hj := hj)).mp e))
  refine ⟨fun x hx => hL.lay.le _ (winWs_slots K _ (hw _ hx)),
    ⟨A 6 7 (by decide) (by decide) (by decide), A 6 8 (by decide) (by decide) (by decide),
      A 7 8 (by decide) (by decide) (by decide)⟩,
    ⟨A 0 1 (by decide) (by decide) (by decide), A 0 2 (by decide) (by decide) (by decide),
      A 1 2 (by decide) (by decide) (by decide)⟩, ?_, ?_⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨A 6 0 (by decide) (by decide) (by decide), A 6 1 (by decide) (by decide) (by decide),
        A 6 2 (by decide) (by decide) (by decide), A 6 3 (by decide) (by decide) (by decide),
        A 6 4 (by decide) (by decide) (by decide), A 6 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 7 0 (by decide) (by decide) (by decide), A 7 1 (by decide) (by decide) (by decide),
        A 7 2 (by decide) (by decide) (by decide), A 7 3 (by decide) (by decide) (by decide),
        A 7 4 (by decide) (by decide) (by decide), A 7 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 8 0 (by decide) (by decide) (by decide), A 8 1 (by decide) (by decide) (by decide),
        A 8 2 (by decide) (by decide) (by decide), A 8 3 (by decide) (by decide) (by decide),
        A 8 4 (by decide) (by decide) (by decide), A 8 5 (by decide) (by decide) (by decide)⟩⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨A 0 3 (by decide) (by decide) (by decide), A 0 4 (by decide) (by decide) (by decide),
        A 0 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 1 3 (by decide) (by decide) (by decide), A 1 4 (by decide) (by decide) (by decide),
        A 1 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 2 3 (by decide) (by decide) (by decide), A 2 4 (by decide) (by decide) (by decide),
        A 2 5 (by decide) (by decide) (by decide)⟩⟩

/-- The value `selSum` leaves in a coordinate of `R`: `E`'s where `R` is
`O` (`Z = 0`), else `R`'s where `E` is `O`, else `D`'s. -/
def selValJ (m : Mem) (base : Addr) (K : WinCfg) (r e d : Nat) : Nat :=
  if wordsVal m base K.R.z K.M.n = 0 then wordsVal m base e K.M.n
  else if wordsVal m base K.E.z K.M.n = 0 then wordsVal m base r K.M.n else wordsVal m base d K.M.n

/-- `D = R` where `E` is `O`, then `R = E` where `R` is `O`, else `D`. -/
theorem selSum_ok {K : WinCfg} {size : Nat} (hL : WinLay K size) (hA : WinA K) {s : State}
    {base : Addr} (hs : Scr s base size) :
    WP isa (.block (WinCfg.selSum K)) s fun s' =>
      wordsVal s'.mem base K.R.x K.M.n = selValJ s.mem base K K.R.x K.E.x K.D.x ∧
      wordsVal s'.mem base K.R.y K.M.n = selValJ s.mem base K K.R.y K.E.y K.D.y ∧
      wordsVal s'.mem base K.R.z K.M.n = selValJ s.mem base K K.R.z K.E.z K.D.z ∧
      KeepRegs [.x1, .x2, .x3, .x7, .x16] s s' ∧ Unch base (loopW K) s.mem s'.mem := by
  have hn := hs.nowrap
  obtain ⟨le, aD, aR, dRE, rE⟩ := winRED_lay hL
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  obtain oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  obtain oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  obtain al : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], x % 8 = 0 :=
    fun x hx => hA.sl x (winOther_mem (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> win_in))
  obtain hin : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      x + 8 * K.M.n ≤ size ∧ x % 8 = 0 := fun x hx => ⟨le x hx, al x hx⟩
  rw [WinCfg.selSum]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs hL.n0 (le K.E.z (by simp)) (al K.E.z (by simp))) fun s₁ ⟨c₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.mem
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₁ (decide (wordsVal s.mem base K.E.z K.M.n ≠ 0))
    (by rw [c₁]; simp only [mask, decide_eq_true_eq]) (o := K.D) (a := K.R)
    (fun d hd => hin d (by sub_mem hd)) aD
    (fun d hd e he => dRE d hd e (by sub_mem he))) fun s₂ ⟨d2x, d2y, d2z, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [m₁] at d2x d2y d2z O₂
  obtain UD : Unch base [(K.D.x, 8 * K.M.n), (K.D.y, 8 * K.M.n), (K.D.z, 8 * K.M.n)] s.mem s₂.mem :=
    fun x hx => O₂ x (hx _ (List.mem_cons_self ..)) (hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  obtain keepD : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₂.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    refine UD.wordsVal (fun w hw => ?_) (by have := le x (by sub_mem hx); omega_using [hn, this])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> dsimp only <;> exact (dRE _ (by simp) x hx).symm
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs₂ hL.n0 (le K.R.z (by simp)) (al K.R.z (by simp))) fun s₃ ⟨c₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  have m₃ : s₃.mem = s₂.mem := k₃.mem
  refine WP.mono (selPt_ok hs₃ (decide (wordsVal s₂.mem base K.R.z K.M.n ≠ 0))
    (by rw [c₃]; simp only [mask, decide_eq_true_eq]) (o := K.R) (a := K.E) (b := K.D)
    (fun d hd => hin d (by sub_mem hd)) aR (fun d hd e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact rE d hd _ (by simp)
      · exact rE d hd _ (by simp)
      · exact rE d hd _ (by simp)
      · exact (dRE _ (by simp) d (by sub_mem hd)).symm
      · exact (dRE _ (by simp) d (by sub_mem hd)).symm
      · exact (dRE _ (by simp) d (by sub_mem hd)).symm))
    fun s₄ ⟨r4x, r4y, r4z, k₄, O₄⟩ => ?_
  rw [m₃] at r4x r4y r4z O₄
  obtain UR : Unch base [(K.R.x, 8 * K.M.n), (K.R.y, 8 * K.M.n), (K.R.z, 8 * K.M.n)] s₂.mem s₄.mem :=
    fun x hx => O₄ x (hx _ (List.mem_cons_self ..)) (hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  obtain inL : ∀ {P : Pt}, (∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) →
      ∀ w ∈ [(P.x, 8 * K.M.n), (P.y, 8 * K.M.n), (P.z, 8 * K.M.n)], w ∈ loopW K := by
    intro P hP w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
  obtain rz := keepD K.R.z (by simp)
  have ez : wordsVal s.mem base K.E.z K.M.n = wordsVal s.mem base K.E.z K.M.n := rfl
  refine ⟨?_, ?_, ?_, ?_, (UD.trans UR).mono fun w hw => ?_⟩
  · rw [r4x, d2x, rz, keepD K.E.x (by simp), selValJ]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;>
      by_cases h2 : wordsVal s.mem base K.E.z K.M.n = 0 <;> simp [h1, h2]
  · rw [r4y, d2y, rz, keepD K.E.y (by simp), selValJ]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;>
      by_cases h2 : wordsVal s.mem base K.E.z K.M.n = 0 <;> simp [h1, h2]
  · rw [r4z, d2z, rz, keepD K.E.z (by simp), selValJ]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;>
      by_cases h2 : wordsVal s.mem base K.E.z K.M.n = 0 <;> simp [h1, h2]
  · exact ((Keeps.regs k₁).mono (by decide)).trans ((k₂.mono (by decide)).trans
      (((Keeps.regs k₃).mono (by decide)).trans (k₄.mono (by decide))))
  · rcases List.mem_append.mp hw with h | h
    · exact inL oD w h
    · exact inL oR w h

theorem toM_iteJ {m R : Nat} [NeZero m] (p : Prop) [Decidable p] (a b : Nat) :
    toM m R (if p then a else b) = if p then toM m R a else toM m R b := by
  split <;> rfl

/-- `selValJ` in the field. -/
theorem toM_selValJ {C : Curve} {K : WinCfg} {m : Mem} {base : Addr} (hp : UnitMod C.p (2 ^ (64 * K.M.n)))
    {r e d : Nat} {Z1 Z2 a b c : Fe C}
    (hz1 : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base K.R.z K.M.n) = Z1)
    (hl1 : wordsVal m base K.R.z K.M.n < C.p)
    (hz2 : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base K.E.z K.M.n) = Z2)
    (hl2 : wordsVal m base K.E.z K.M.n < C.p)
    (ha : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base r K.M.n) = a)
    (hb : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base e K.M.n) = b)
    (hc : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base d K.M.n) = c) :
    toM C.p (2 ^ (64 * K.M.n)) (selValJ m base K r e d) = if Z1 = 0 then b else if Z2 = 0 then a else c := by
  obtain i1 : wordsVal m base K.R.z K.M.n = 0 ↔ Z1 = 0 := by rw [← hz1]; exact (toM_eq_zero_iff hp hl1).symm
  obtain i2 : wordsVal m base K.E.z K.M.n = 0 ↔ Z2 = 0 := by rw [← hz2]; exact (toM_eq_zero_iff hp hl2).symm
  unfold selValJ
  rw [toM_iteJ, toM_iteJ, ha, hb, hc]
  simp only [i1, i2]

/-- `R = R + E` for `R` in Jacobian coordinates and `E` affine (or `O`), by
the mixed addition into `D`, with `R = E` where `R` is `O` and `R` kept where
`E` is `O`: for `R` and `E` standing for points not equal unless one is `O`. -/
theorem sumJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinStR K C base size Rp P s₀ s) {QR QE : Point C} (hQR : onCurve C QR = true)
    (hQE : onCurve C QE = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) QR)
    (hE : RepA C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) QE)
    (hsep : QR ≠ .infinity → QE ≠ .infinity → QR ≠ QE) {ma : Option (Prog isa)}
    (hM : MaddOk K C base size ma) :
    WP isa (WinCfg.sumJ K ma) s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .x19 = s.gpr .x19 ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (Spec.Weierstrass.add QR QE) := by
  obtain ⟨-, -, ro_lt, -⟩ := hS.ro_tmv hL hF
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  obtain oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  obtain oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  obtain sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    List.mem_append_right (winRo K) (h x hx)
  obtain w1 := winJ_sl oD (sl _ oR) (sl _ oE)
  obtain V0 : ∀ x ∈ rcbR K.S K.R K.E, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by win_in, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_in, ro_lt _ (by simp [winRo])⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
  obtain I₀ : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  obtain hM' : MaddSpec K C base size (WinCfg.maddRD K ma) := by
    cases ma with
    | some m => exact hM m rfl
    | none =>
      intro E s hI
      rw [WinCfg.maddRD, maddJ_eq]
      exact WP.mono (winN_ok hL hA hp maddJN_ok (hL.rcbApart_D (Or.inr rfl)) w1.1 w1.2.1 w1.2.2 hI
        (fun x hx => hx)) fun s' ⟨k, U, E', I, o, v⟩ =>
        ⟨k.mono fun _ h => List.mem_append_left _ h, U, E', I, o, v.trans (maddJN_run _)⟩
  rw [WinCfg.sumJ]
  refine WP.seq (WP.mono (hM' _ s I₀) fun s₁ ⟨k₁, U₁, E₁, I₁, o₁, v₁⟩ => ?_)
  obtain S₁ := hS.next hL I₁.scr (k₁.mono fun _ h => winSaved_combClob h) U₁
  obtain ⟨-, -, -, hRo, -, -, -, hEo, -, -⟩ := hL.other_ne
  obtain nD : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z], x ∉ rcbW K.S K.D := by
    intro x hx h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain h1 : ∀ y ∈ [K.R.x, K.R.y, K.R.z], y ∉ rcbW K.S K.D := fun y hy h =>
      hRo y hy (List.mem_append_right _ h)
    obtain h2 : ∀ y ∈ [K.E.x, K.E.y, K.E.z], y ∉ rcbW K.S K.D := fun y hy h =>
      hEo y hy (List.mem_cons_of_mem _ h)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1 _ (by simp) h
    · exact h1 _ (by simp) h
    · exact h1 _ (by simp) h
    · exact h2 _ (by simp) h
    · exact h2 _ (by simp) h
    · exact h2 _ (by simp) h
  obtain inV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.R K.E := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h | h <;> simp [h]
  obtain v₁' : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base x K.M.n) = tmv C K.M.n base s x := fun x hx => by
    rw [I₁.val x (inV x (by sub_mem hx)), o₁ x (nD x hx)]
  obtain lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      wordsVal s₁.mem base x K.M.n < C.p := fun x hx => I₁.lt x (inV x hx)
  obtain vD : (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.x K.M.n),
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.y K.M.n),
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.z K.M.n)) =
      maddJF (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
        (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) := by
    refine Eq.trans ?_ v₁
    rw [I₁.val _ (inV _ (by simp)), I₁.val _ (inV _ (by simp)), I₁.val _ (inV _ (by simp))]
  obtain jx := congrArg Prod.fst vD
  obtain jy := congrArg (fun t => t.2.1) vD
  obtain jz := congrArg (fun t => t.2.2) vD
  dsimp only at jx jy jz
  refine WP.mono (selSum_ok hL hA I₁.scr) fun s₂ ⟨r2x, r2y, r2z, k₂, U₂⟩ => ?_
  obtain c : ∀ r ∈ [Reg.x1, .x2, .x3, .x7, .x16], r ∈ combClob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [combClob, clob]
  obtain S₂ := S₁.next hL (I₁.scr.of_keepRegs k₂ (by decide)) (k₂.mono c) U₂
  obtain tz1 := v₁' K.R.z (by simp)
  obtain tz2 := v₁' K.E.z (by simp)
  obtain l1 := lt₁ K.R.z (by simp)
  obtain l2 := lt₁ K.E.z (by simp)
  obtain n19 : Reg.x19 ∉ clob K.M.n ++ winSaved K.M.n := fun h =>
    (List.mem_append.mp h).elim (x19_not_clob _) (not_mem_winSaved (by decide))
  refine ⟨S₂, by rw [k₂.gpr _ (by decide), k₁.gpr _ n19], fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [r2x, selValJ]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
    · rw [r2y, selValJ]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
    · rw [r2z, selValJ]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
  · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [r2x, r2y, r2z, toM_selValJ hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jx,
      toM_selValJ hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jy,
      toM_selValJ hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jz]
    exact InvJ.sumSelM hC hM3 hQR hQE hR hE hsep

/-! ## An iteration but the last -/

/-- `x4 = x19 - 1`. -/
theorem subX4_ok (s : State) {j : Nat} (hx : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.subImm .x .x4 .x19 1]) s fun t =>
      t.gpr .x4 = BitVec.ofNat 64 j - BitVec.ofNat 64 1 ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show 1 < 4096 by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    hx, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The Jacobian loop's invariant at `x19 = j`: `R` stands for `[winE k J j]P`
in Jacobian coordinates, the table affine. -/
structure WinInvJ (K : WinCfg) (C : Curve) (base : Addr) (size k : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) : Prop where
  st : WinStR K C base size (RepA C) P s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (winE k K.J j) P)

/-- What the entry's selection writes is in `loopW`. -/
theorem entryW_loopW (K : WinCfg) : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], w ∈ loopW K := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inr rfl

/-- `R` is apart from what the entry's selection writes. -/
theorem R_apart_entry {K : WinCfg} {size : Nat} (hL : WinLay K size) {x : Nat}
    (hx : x ∈ [K.R.x, K.R.y, K.R.z]) :
    ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  obtain ⟨-, -, -, hRo, -⟩ := hL.other_ne
  obtain hxw : x ∈ winWs K := winOther_ws K x (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  obtain hne : ∀ y ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ≠ y := fun y hy e => hRo x hx (by
    rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> simp)
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.lay.tmp x (winWs_slots K x hxw)

/-- An iteration but the last, `x19 = j ≥ 2` to `j - 1`: adds digit `j - 1`;
then `x4 = j - 2`. -/
theorem winStepJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixed K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {j : Nat} (hj : 2 ≤ j) (hjn : j ≤ K.J)
    (hb : 16 * winE k K.J j + 8 < C.n) {s : State} (hI : WinInvJ K C base size k P s₀ s j)
    {dd : Option (Prog isa × Prog isa)} (hD : DblsOk K C base size dd) {ma : Option (Prog isa)}
    (hM : MaddOk K C base size ma) {sl : Option (List Instr)} (hS : SelOk K size (WinCfg.selOf K sl)) :
    WP isa (WinCfg.stepJ K dd ma sl) s fun s' =>
      WinInvJ K C base size k P s₀ s' (j - 1) ∧
        s'.gpr .x4 = BitVec.ofNat 64 (j - 1) - BitVec.ofNat 64 1 := by
  have hJ := hL.J
  rw [WinCfg.stepJ]
  refine WP.seq (WP.mono (decCounter_ok s (by omega_using [hj]) (by omega_using [hjn, hJ]) hI.x19)
    fun s₁ ⟨b₁, k₁⟩ => ?_)
  obtain hS₁ := hI.st.next hL (hI.st.scr.of_keeps k₁ (by decide))
    ((Keeps.regs k₁).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [combClob]))
    (by rw [k₁.mem]; exact Unch.refl _ _ _)
  obtain lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.mem]; exact hI.lt
  obtain rep₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J j) P) := by
    obtain e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.mem]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quadJ_ok hL hA hp hC hM3 hP hD hF hS₁ (j := j - 1) (by omega_using [hjn, hJ]) b₁ lt₁ rep₁)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  obtain hx₅ : s₅.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [x₅, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  obtain hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega_using [ht, this]) (by have := S₅.scr.nowrap; omega_arith)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntryR_ok hL hA (RepA.infinity hC) RepA.negY (P := P) hpn hone_lt hone
    S₅.scr S₅.mod (i := j - 1) (by omega_using [hjn, hJ]) hx₅ hbits₅ hz₅ S₅.tbl hS) fun s₇ E₇ => ?_)
  have hn := S₅.scr.nowrap
  obtain S₇ := S₅.next hL E₇.scr E₇.keep (E₇.unch.mono (entryW_loopW K))
  obtain eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base x K.M.n :=
    fun x hx => E₇.unch.wordsVal (R_apart_entry hL hx) (by
      have := hL.lay.le x (winOther_mem (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)); omega_using [hn, this])
  obtain lt₇ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  obtain rep₇ : InvJ C (tmv C K.M.n base s₇ K.R.x) (tmv C K.M.n base s₇ K.R.y)
      (tmv C K.M.n base s₇ K.R.z) (mul (16 * winE k K.J j) P) := by
    obtain e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₇ x = tmv C K.M.n base s₅ x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [eR x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact r₅
  obtain hsep := win_sep hC hO hP hP0 (k := k) (J := K.J) (j := j - 1)
    (by rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)]; exact hb)
  rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)] at hsep
  refine WP.seq (WP.mono (sumJ_ok hL hA hp hC hM3 hF S₇ (hC.onCurve_mul hP _)
    (onCurve_winPt hC hP k (j - 1)) lt₇ E₇.lt rep₇ E₇.rep (fun h1 _ => (hsep h1).1) hM)
    fun s₈ ⟨S₈, x₈, l₈, r₈⟩ => ?_)
  obtain hadd := win_add hC hP (k := k) (J := K.J) (j := j - 1) hk8 (by omega_using [hjn, hJ])
  rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)] at hadd
  rw [hadd] at r₈
  obtain hx₇ : s₇.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [E₇.x19, hx₅]
  obtain hx₈ : s₈.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [x₈, hx₇]
  refine WP.mono (subX4_ok s₈ hx₈) fun s₉ ⟨z₉, k₉⟩ => ⟨?_, z₉⟩
  refine ⟨S₈.next hL (S₈.scr.of_keeps k₉ (by decide))
      ((Keeps.regs k₉).mono (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        simp [combClob, clob]))
      (by rw [k₉.mem]; exact Unch.refl _ _ _), by rw [k₉.gpr _ (by decide), hx₈],
    by rw [k₉.mem]; exact l₈, ?_⟩
  obtain e : ∀ x, tmv C K.M.n base s₉ x = tmv C K.M.n base s₈ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₉.mem]
  rw [e, e, e]; exact r₈

end VG.Proof.Weierstrass.AArch64
