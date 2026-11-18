module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Impl.MlKem.AArch64.AddSubW
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec12W
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Lanes
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopState
public import VerifiedGarbage.Impl.MlKem.AArch64.DotW
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

/-! ### `MlKem.AArch64.DotW.Loop`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.DotW.Lane`, which this module and modules that import it used -/

section

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: lanes

The halfwords of a vector of 16-bit coefficients (`hlanes_coeffs`), the even
and odd coefficients of eight pairs (UZP1, UZP2: `gatherW_lanes`), and the
products of halfwords accumulated in words (UMLAL, UMLAL2: `umlal_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem

/-- The halfwords of `x` are `f`. -/
def HLanes (x : BitVec 128) (f : Nat → Nat) : Prop := ∀ e < 8, (vhalf x e).toNat = f e

theorem lanes_ofVWords {g : Nat → BitVec 32} {F : Nat → Nat} (h : ∀ e < 4, (g e).toNat = F e) :
    Lanes (ofVWords (g 0) (g 1) (g 2) (g 3)) F := fun e he => by
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_using [he]) with rfl | rfl | rfl | rfl <;> exact h _ (by decide)

/-- Eight 16-bit coefficients from `j` in a vector. -/
theorem hlanes_coeffs (m : Mem) (p : Addr) (j : Nat) {F : Nat → Nat}
    (h : ∀ e < 8, (coeffAtW 16 m p (j + e)).toNat = F e) :
    HLanes (m.read (p + BitVec.ofNat 64 (2 * j)) 16) F := fun e he => by
  rw [vhalf_read_coeff m p j he]; exact h e he

/-- The even and odd coefficients of eight pairs, from two vectors of sixteen. -/
theorem gatherW_lanes {x y : BitVec 128} {A : Nat → Nat}
    (hx : HLanes x A) (hy : HLanes y (fun e => A (8 + e))) :
    HLanes (VPermOp.eval .uzp1 .h8 x y) (fun e => A (2 * e)) ∧
    HLanes (VPermOp.eval .uzp2 .h8 x y) (fun e => A (2 * e + 1)) := by
  constructor
  · intro e he
    rw [Ntt16.vhalf_perm_h8 _ _ _ he]
    dsimp only
    split
    · exact hx _ (by omega_arith)
    · rw [hy _ (by omega_using [he])]; dsimp only; congr 1; omega_arith
  · intro e he
    rw [Ntt16.vhalf_perm_h8 _ _ _ he]
    dsimp only
    split
    · exact hx _ (by omega_arith)
    · rw [hy _ (by omega_using [he])]; dsimp only; congr 1; omega_arith

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `umlal d, n, m` (or `umlal2`): lanes `p + e` of the halfwords' products added to the words
of `d`, `p = 4` for `umlal2`. -/
theorem umlal_ok {hi : Bool} {d n m : VReg} {A X Y : Nat → Nat}
    (ha : Lanes (s.v d) A) (hx : HLanes (s.v n) X) (hy : HLanes (s.v m) Y)
    (hlt : ∀ e < 4, A e + X ((if hi then 4 else 0) + e) * Y ((if hi then 4 else 0) + e) < 2 ^ 32)
    (k : ∀ s', VChg [d] s s' →
      Lanes (s'.v d) (fun e => A e + X ((if hi then 4 else 0) + e) * Y ((if hi then 4 else 0) + e)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.vop (.umlalH hi d n m) :: rest)) s Q := by
  refine wp_vop rfl fun s' h => k s' h.chg ?_
  rw [h.v]
  refine lanes_ofVWords (g := fun e => vword (s.v d) e +
    (vhalf (s.v n) ((if hi then 4 else 0) + e)).setWidth 32 *
      (vhalf (s.v m) ((if hi then 4 else 0) + e)).setWidth 32) fun e he => ?_
  have hp : (if hi then 4 else 0) + e < 8 := by split <;> omega_using [he]
  have hl := hlt e he
  have hX := hx _ hp
  have hY := hy _ hp
  have hx16 := (vhalf (s.v n) ((if hi then 4 else 0) + e)).isLt
  have hy16 := (vhalf (s.v m) ((if hi then 4 else 0) + e)).isLt
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, ha e he]
  rw [Nat.mod_eq_of_lt (a := (vhalf (s.v n) _).toNat) (by omega_using []),
    Nat.mod_eq_of_lt (a := (vhalf (s.v m) _).toNat) (by omega_using []), hX, hY,
    Nat.mod_eq_of_lt (show X _ * Y _ < 2 ^ 32 by omega_using [hl]), Nat.mod_eq_of_lt hl]

end

end VG.Proof.MlKem.AArch64.DotW

end

end

/-! ### `MlKem.AArch64.DotW.Store`, which this module and modules that import it used -/

section

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: the store

`storeW`: the even and odd results of pairs `0 … 3` (`v21`, `v23`) and
`4 … 7` (`v25`, `v27`), words less than `q`, narrowed to halfwords (UZP1)
and interleaved (ZIP1, ZIP2) into sixteen coefficients (`storeW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem

/-- The low halfwords of the words of `x`, then of `y`. -/
theorem narrow_lanes {x y : BitVec 128} {A B : Nat → Nat} (hx : Lanes x A) (hy : Lanes y B)
    (ba : ∀ e < 4, A e < 2 ^ 16) (bb : ∀ e < 4, B e < 2 ^ 16) :
    HLanes (VPermOp.eval .uzp1 .h8 x y) (fun e => if e < 4 then A e else B (e - 4)) := fun e he => by
  rw [Ntt16.vhalf_perm_h8 _ _ _ he]
  dsimp only
  by_cases c : e < 4
  · rw [ite_eq_left c, ite_eq_left c, ← Ntt16.vword_lo, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      hx e c, Nat.mod_eq_of_lt (ba e c)]
  · rw [ite_eq_right c, ite_eq_right c, show 2 * e - 8 = 2 * (e - 4) by omega_using [], ← Ntt16.vword_lo,
      BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hy _ (by omega_using [he]), Nat.mod_eq_of_lt (bb _ (by omega_using [he]))]

/-- The sixteen coefficients from the even (`A`, `A'`) and odd (`B`, `B'`) results of pairs
`0 … 3` and `4 … 7`. -/
def outW (A B A' B' : Nat → Nat) (e : Nat) : Nat :=
  if e < 8 then (if e % 2 = 0 then A (e / 2) else B (e / 2))
  else (if e % 2 = 0 then A' ((e - 8) / 2) else B' ((e - 8) / 2))

theorem storeW_ok {s : State} {p : Addr} {j : Nat} {A B A' B' : Nat → Nat}
    (hx0 : s.gpr .x0 = p + BitVec.ofNat 64 (2 * j)) (hj : j + 16 ≤ 256)
    (hw : ∀ i < 2, InRegions s.wr (p + BitVec.ofNat 64 (2 * (j + 8 * i))) 16)
    (hc : VConsts s) (ha : Lanes (s.v .v21) A) (hb : Lanes (s.v .v23) B)
    (ha' : Lanes (s.v .v25) A') (hb' : Lanes (s.v .v27) B')
    (ba : ∀ e < 4, A e < 3329) (bb : ∀ e < 4, B e < 3329)
    (ba' : ∀ e < 4, A' e < 3329) (bb' : ∀ e < 4, B' e < 3329)
    {O old : Nat → BitVec 16} (ho : CoeffsInW s.mem p (· < j) O old)
    (hv : ∀ e < 16, (O (j + e)).toNat = outW A B A' B' e) :
    WP isa (.block Impl.MlKem.AArch64.DotW.storeW) s fun s' => Keep [] s s' ∧ VConsts s' ∧
      Frame [⟨p, 512⟩] s.mem s'.mem ∧ CoeffsInW s'.mem p (· < j + 16) O old := by
  simp only [Impl.MlKem.AArch64.DotW.storeW]
  refine wp_vop (d := .v0) rfl fun s₁ h₁ => wp_vop (d := .v1) rfl fun s₂ h₂ =>
    wp_vop (d := .v2) rfl fun s₃ h₃ => wp_vop (d := .v3) rfl fun s₄ h₄ => ?_
  have E := narrow_lanes ha ha' (fun e he => by have := ba e he; omega_using [this]) (fun e he => by have := ba' e he; omega_using [this])
  have Od := narrow_lanes hb hb' (fun e he => by have := bb e he; omega_using [this]) (fun e he => by have := bb' e he; omega_using [this])
  have v0 : s₄.v .v0 = VPermOp.eval .uzp1 .h8 (s.v .v21) (s.v .v25) := by
    rw [h₄.get .v0, h₃.get .v0, h₂.get .v0, h₁.v]
  have v1 : s₄.v .v1 = VPermOp.eval .uzp1 .h8 (s.v .v23) (s.v .v27) := by
    rw [h₄.get .v1, h₃.get .v1, h₂.v, h₁.get .v23, h₁.get .v27]
  refine wp_strq (a := p + BitVec.ofNat 64 (2 * j)) (by decide)
    (by rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, hx0, BitVec.add_zero])
    (by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]; simpa only [Nat.mul_zero, Nat.add_zero] using hw 0 (by decide))
    fun s₅ h₅ => ?_
  refine wp_strq (a := p + BitVec.ofNat 64 (2 * (j + 8))) (by decide)
    (by rw [h₅.gpr, h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, hx0, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2)
    (by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact hw 1 (by decide)) fun s₆ h₆ => wp_nil ?_
  have x2 : ∀ e < 8, vhalf (s₄.v .v2) e = O (j + e) := fun e he => by
    apply BitVec.eq_of_toNat_eq
    rw [h₄.get .v2, h₃.v, Ntt16.vhalf_perm_h8 _ _ _ he, hv e (by omega_using [he]), outW, ite_eq_left he]
    dsimp only
    rw [← h₃.get .v0, ← h₄.get .v0, ← h₃.get .v1, ← h₄.get .v1, v0, v1]
    split
    · rw [E _ (by omega_using [he])]; dsimp only; rw [ite_eq_left (show e / 2 < 4 by omega_using [he])]
    · rw [Od _ (by omega_using [he])]; dsimp only; rw [ite_eq_left (show e / 2 < 4 by omega_using [he])]
  have x3 : ∀ e < 8, vhalf (s₄.v .v3) e = O (j + 8 + e) := fun e he => by
    apply BitVec.eq_of_toNat_eq
    rw [h₄.v, Ntt16.vhalf_perm_h8 _ _ _ he, Nat.add_assoc, hv (8 + e) (by omega_using [he]), outW,
      ite_eq_right (show ¬(8 + e < 8) by omega_using []), show 8 + e - 8 = e by omega_using [],
      show (8 + e) % 2 = e % 2 by omega_using []]
    dsimp only
    rw [← h₄.get .v0, ← h₄.get .v1, v0, v1]
    split
    · rw [E _ (by omega_using [he])]; dsimp only
      rw [ite_eq_right (show ¬(4 + e / 2 < 4) by omega_using []), show 4 + e / 2 - 4 = e / 2 by omega_using []]
    · rw [Od _ (by omega_using [he])]; dsimp only
      rw [ite_eq_right (show ¬(4 + e / 2 < 4) by omega_using []), show 4 + e / 2 - 4 = e / 2 by omega_using []]
  have hm : s₆.mem = (s.mem.write (p + BitVec.ofNat 64 (2 * j)) 16 (s₄.v .v2)).write
      (p + BitVec.ofNat 64 (2 * (j + 8))) 16 (s₄.v .v3) := by
    rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, h₅.v]
  refine ⟨(((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep).mono,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [h₆.v, h₅.v, h₄.get .v16, h₃.get .v16, h₂.get .v16, h₁.get .v16]; exact hc.q
  · rw [h₆.v, h₅.v, h₄.get .v17, h₃.get .v17, h₂.get .v17, h₁.get .v17]; exact hc.m
  · rw [hm]
    exact ((Frame.refl _ _).write (List.mem_singleton_self _) _ (contains_off (by omega_using [hj]) (by decide))).write
      (List.mem_singleton_self _) _ (contains_off (by omega_using [hj]) (by decide))
  · rw [hm]
    exact (ho.write16 (S' := (· < j + 8)) (by omega_using [hj]) x2 fun i _ => by omega_using []).write16 (by omega_using [hj])
      (fun e he => by rw [x3 e he, Nat.add_assoc]) fun i _ => by omega_using []

end VG.Proof.MlKem.AArch64.DotW

end

end

/-! ### `MlKem.AArch64.DotW.Term`, which only this module used -/

section

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: a term

`termW bf bg fg` (pointers to `bf` and `bg` plus the offsets `fg`, the loads, `gatherW` and `accumulateW`)
adds the products of the eight pairs of 16 coefficients of `F` and `G` to
the sums of pairs `0 … 3` (`v21`–`v23`) and `4 … 7` (`v25`–`v27`):
`fullTermW_ok`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

def gatherW : List Instr :=
  [.vop (.perm .uzp1 .h8 .v6 .v0 .v1), .vop (.perm .uzp2 .h8 .v7 .v0 .v1),
   .vop (.perm .uzp1 .h8 .v19 .v4 .v5), .vop (.perm .uzp2 .h8 .v20 .v4 .v5)]

def accumulateW : List Instr :=
  [.vop (.umlalH false .v21 .v6 .v19), .vop (.umlalH true .v25 .v6 .v19),
   .vop (.umlalH false .v22 .v7 .v20), .vop (.umlalH true .v26 .v7 .v20),
   .vop (.umlalH false .v23 .v6 .v20), .vop (.umlalH true .v27 .v6 .v20),
   .vop (.umlalH false .v23 .v7 .v19), .vop (.umlalH true .v27 .v7 .v19)]

/-- `x1` and `x2` to the coefficients of a term: `bf` and `bg` plus its offsets, plus `x12`. -/
def pointersW (bf bg : Reg) (fg : Nat × Nat) : List Instr :=
  Impl.MlKem.AArch64.ptrTo .x1 bf fg.1 ++ Impl.MlKem.AArch64.ptrTo .x2 bg fg.2 ++ [.add .x .x1 .x1 .x12, .add .x .x2 .x2 .x12]

theorem not_mem_x12 {r : Reg} (h : r ∉ clob) : r ∉ [Reg.x1, .x2] := fun e => h (by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at e
  rcases e with rfl | rfl <;> decide)

theorem pointersW_ok {s : State} {bf bg : Reg} {fg : Nat × Nat} (hbf : bf ∉ clob) (hbg : bg ∉ clob)
    (hf : fg.1 < 65536) (hg : fg.2 < 65536) :
    WP isa (.block (pointersW bf bg fg)) s fun s' =>
      Only [.x1, .x2] s s' ∧ s'.v = s.v ∧
      s'.gpr .x1 = s.gpr bf + BitVec.ofNat 64 fg.1 + s.gpr .x12 ∧
      s'.gpr .x2 = s.gpr bg + BitVec.ofNat 64 fg.2 + s.gpr .x12 := by
  have n1 : ∀ r, r ∉ clob → r ≠ .x1 := fun r h e => h (by rw [e]; decide)
  have n2 : ∀ r, r ∉ clob → r ≠ .x2 := fun r h e => h (by rw [e]; decide)
  refine WP.mono (WP.keepV (Q := fun s' => Only [.x1, .x2] s s' ∧
    s'.gpr .x1 = s.gpr bf + BitVec.ofNat 64 fg.1 + s.gpr .x12 ∧
    s'.gpr .x2 = s.gpr bg + BitVec.ofNat 64 fg.2 + s.gpr .x12) ?_ ?_) ?_
  · simp only [pointersW, Impl.MlKem.AArch64.ptrTo]
    split <;> split <;> rfl
  · simp only [pointersW, List.append_assoc]
    refine wp_ptrTo (n1 bf hbf).symm hf fun s₁ h₁ e₁ => wp_ptrTo (n2 bg hbg).symm hg fun s₂ h₂ e₂ =>
      wp_add fun s₃ h₃ e₃ => wp_add fun s₄ h₄ e₄ => wp_nil ?_
    refine ⟨(((h₁.trans h₂).trans h₃).trans h₄).mono, ?_, ?_⟩
    · rw [h₄.get .x1, e₃, h₂.get .x1, e₁, h₂.get .x12, h₁.get .x12]
    · rw [e₄, h₃.get .x2, e₂, h₁.get bg (by simpa using n1 bg hbg), h₃.get .x12, h₂.get .x12,
        h₁.get .x12]
  · intro s' h
    exact ⟨h.1.1, h.2, h.1.2⟩

theorem termW_partition (bf bg : Reg) (fg : Nat × Nat) :
    Impl.MlKem.AArch64.DotW.termW bf bg fg = pointersW bf bg fg ++ (loads ++ gatherW ++ accumulateW) := by
  simp only [Impl.MlKem.AArch64.DotW.termW, pointersW, loads, gatherW, accumulateW,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The sums of pairs `0 … 3` (`lo`, as `dot`'s `Accum`) and `4 … 7` (`hi`). -/
def AccumW (s : State) (lo hi : Nat → Sums) : Prop :=
  Accum s lo ∧ Lanes (s.v .v25) (fun e => (hi e).even) ∧
    Lanes (s.v .v26) (fun e => (hi e).odd) ∧ Lanes (s.v .v27) (fun e => (hi e).cross)

section
variable {rest : List Instr} {Q : State → Prop}

theorem gatherW_ok {s : State} {F G : Nat → Nat}
    (f0 : HLanes (s.v .v0) F) (f1 : HLanes (s.v .v1) (fun e => F (8 + e)))
    (g0 : HLanes (s.v .v4) G) (g1 : HLanes (s.v .v5) (fun e => G (8 + e)))
    (k : ∀ s', VChg [.v6, .v7, .v19, .v20] s s' →
      HLanes (s'.v .v6) (fun e => F (2 * e)) → HLanes (s'.v .v7) (fun e => F (2 * e + 1)) →
      HLanes (s'.v .v19) (fun e => G (2 * e)) → HLanes (s'.v .v20) (fun e => G (2 * e + 1)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (gatherW ++ rest)) s Q := by
  simp only [gatherW, List.cons_append, List.nil_append]
  refine wp_vop (d := .v6) rfl fun s₁ h₁ => wp_vop (d := .v7) rfl fun s₂ h₂ =>
    wp_vop (d := .v19) rfl fun s₃ h₃ => wp_vop (d := .v20) rfl fun s₄ h₄ => ?_
  refine k s₄ (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).mono ?_ ?_ ?_ ?_
  · rw [h₄.get .v6, h₃.get .v6, h₂.get .v6, h₁.v]; exact (gatherW_lanes f0 f1).1
  · rw [h₄.get .v7, h₃.get .v7, h₂.v, h₁.get .v0, h₁.get .v1]
    exact (gatherW_lanes f0 f1).2
  · rw [h₄.get .v19, h₃.v, h₂.get .v4, h₂.get .v5, h₁.get .v4, h₁.get .v5]
    exact (gatherW_lanes g0 g1).1
  · rw [h₄.v, h₃.get .v4, h₃.get .v5, h₂.get .v4, h₂.get .v5, h₁.get .v4, h₁.get .v5]
    exact (gatherW_lanes g0 g1).2

theorem accumulateW_ok {s : State} {lo hi : Nat → Sums} {FE FO GE GO : Nat → Nat}
    (ha : AccumW s lo hi)
    (hfe : HLanes (s.v .v6) FE) (hfo : HLanes (s.v .v7) FO)
    (hge : HLanes (s.v .v19) GE) (hgo : HLanes (s.v .v20) GO)
    (blo : ∀ e < 4, ((lo e).next (FE e) (FO e) (GE e) (GO e)).even < 2 ^ 32 ∧
      ((lo e).next (FE e) (FO e) (GE e) (GO e)).odd < 2 ^ 32 ∧
      ((lo e).next (FE e) (FO e) (GE e) (GO e)).cross < 2 ^ 32)
    (bhi : ∀ e < 4, ((hi e).next (FE (4 + e)) (FO (4 + e)) (GE (4 + e)) (GO (4 + e))).even < 2 ^ 32 ∧
      ((hi e).next (FE (4 + e)) (FO (4 + e)) (GE (4 + e)) (GO (4 + e))).odd < 2 ^ 32 ∧
      ((hi e).next (FE (4 + e)) (FO (4 + e)) (GE (4 + e)) (GO (4 + e))).cross < 2 ^ 32)
    (k : ∀ s', VChg [.v21, .v25, .v22, .v26, .v23, .v27] s s' →
      AccumW s' (fun e => (lo e).next (FE e) (FO e) (GE e) (GO e))
        (fun e => (hi e).next (FE (4 + e)) (FO (4 + e)) (GE (4 + e)) (GO (4 + e))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (accumulateW ++ rest)) s Q := by
  obtain ⟨⟨a21, a22, a23⟩, a25, a26, a27⟩ := ha
  simp only [accumulateW, List.cons_append, List.nil_append]
  simp only [Sums.next] at blo bhi
  refine umlal_ok (hi := false) a21 hfe hge (fun e he => by simpa using (blo e he).1) fun s₁ c₁ l₁ => ?_
  refine umlal_ok (hi := true) (by rw [c₁.get .v25]; exact a25) (by rw [c₁.get .v6]; exact hfe)
    (by rw [c₁.get .v19]; exact hge) (fun e he => by simpa [Nat.add_comm] using (bhi e he).1)
    fun s₂ c₂ l₂ => ?_
  refine umlal_ok (hi := false) (by rw [c₂.get .v22, c₁.get .v22]; exact a22)
    (by rw [c₂.get .v7, c₁.get .v7]; exact hfo) (by rw [c₂.get .v20, c₁.get .v20]; exact hgo)
    (fun e he => by simpa using (blo e he).2.1) fun s₃ c₃ l₃ => ?_
  refine umlal_ok (hi := true) (by rw [c₃.get .v26, c₂.get .v26, c₁.get .v26]; exact a26)
    (by rw [c₃.get .v7, c₂.get .v7, c₁.get .v7]; exact hfo)
    (by rw [c₃.get .v20, c₂.get .v20, c₁.get .v20]; exact hgo)
    (fun e he => by simpa [Nat.add_comm] using (bhi e he).2.1) fun s₄ c₄ l₄ => ?_
  have C₄ := ((c₁.trans c₂).trans c₃).trans c₄
  refine umlal_ok (hi := false) (by rw [C₄.get .v23]; exact a23)
    (by rw [C₄.get .v6]; exact hfe) (by rw [C₄.get .v20]; exact hgo)
    (fun e he => by have := (blo e he).2.2; simp only [Nat.zero_add, Bool.false_eq_true, ite_false]; omega_using [this])
    fun s₅ c₅ l₅ => ?_
  refine umlal_ok (hi := true) (by rw [c₅.get .v27, C₄.get .v27]; exact a27)
    (by rw [c₅.get .v6, C₄.get .v6]; exact hfe) (by rw [c₅.get .v20, C₄.get .v20]; exact hgo)
    (fun e he => by have := (bhi e he).2.2; simp only [ite_true, Nat.add_comm 4 e] at this ⊢; omega_using [this])
    fun s₆ c₆ l₆ => ?_
  have C₆ := (C₄.trans c₅).trans c₆
  refine umlal_ok (hi := false) (by rw [c₆.get .v23]; exact l₅)
    (by rw [C₆.get .v7]; exact hfo) (by rw [C₆.get .v19]; exact hge)
    (fun e he => by have := (blo e he).2.2; simp only [Nat.zero_add, Bool.false_eq_true, ite_false]; omega_using [this])
    fun s₇ c₇ l₇ => ?_
  refine umlal_ok (hi := true) (by rw [c₇.get .v27]; exact l₆)
    (by rw [c₇.get .v7, C₆.get .v7]; exact hfo) (by rw [c₇.get .v19, C₆.get .v19]; exact hge)
    (fun e he => by have := (bhi e he).2.2; simp only [ite_true, Nat.add_comm 4 e] at this ⊢; omega_using [this])
    fun s₈ c₈ l₈ => ?_
  have C₈ := (C₆.trans c₇).trans c₈
  refine k s₈ C₈.mono ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [c₈.get .v21, c₇.get .v21, c₆.get .v21, c₅.get .v21, c₄.get .v21, c₃.get .v21, c₂.get .v21]
    exact l₁.congr fun e he => by simp [Sums.next]
  · rw [c₈.get .v22, c₇.get .v22, c₆.get .v22, c₅.get .v22, c₄.get .v22]
    exact l₃.congr fun e he => by simp [Sums.next]
  · rw [c₈.get .v23]
    exact l₇.congr fun e he => by simp [Sums.next]
  · rw [c₈.get .v25, c₇.get .v25, c₆.get .v25, c₅.get .v25, c₄.get .v25, c₃.get .v25]
    exact l₂.congr fun e he => by simp [Sums.next, Nat.add_comm]
  · rw [c₈.get .v26, c₇.get .v26, c₆.get .v26, c₅.get .v26]
    exact l₄.congr fun e he => by simp [Sums.next, Nat.add_comm]
  · exact l₈.congr fun e he => by simp [Sums.next, Nat.add_comm]

end

end VG.Proof.MlKem.AArch64.DotW

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

/-- What a term needs: sixteen coefficients of each polynomial, at `bf` (or `bg`) plus its
offset plus `x12`, base registers the loop keeps. -/
structure TermInputW (s : State) (bf bg : Reg) (fg : Nat × Nat) (F G : Nat → Nat) : Prop where
  baseF : bf ∉ clob
  baseG : bg ∉ clob
  offF : fg.1 < 65536
  offG : fg.2 < 65536
  boundF : ∀ e < 16, F e < 3329
  boundG : ∀ e < 16, G e < 3329
  valueF : ∀ e < 16, (coeffAtW 16 s.mem (s.gpr bf + BitVec.ofNat 64 fg.1 + s.gpr .x12) e).toNat = F e
  valueG : ∀ e < 16, (coeffAtW 16 s.mem (s.gpr bg + BitVec.ofNat 64 fg.2 + s.gpr .x12) e).toNat = G e
  readF : ∀ i < 2, InRegions (s.rd ++ s.wr)
    (s.gpr bf + BitVec.ofNat 64 fg.1 + s.gpr .x12 + BitVec.ofNat 64 (16 * i)) 16
  readG : ∀ i < 2, InRegions (s.rd ++ s.wr)
    (s.gpr bg + BitVec.ofNat 64 fg.2 + s.gpr .x12 + BitVec.ofNat 64 (16 * i)) 16

theorem TermInputW.keep {s s' : State} {bf bg : Reg} {fg : Nat × Nat} {F G : Nat → Nat}
    (h : TermInputW s bf bg fg F G) (hk : Only [.x1, .x2] s s') : TermInputW s' bf bg fg F G := by
  refine ⟨h.baseF, h.baseG, h.offF, h.offG, h.boundF, h.boundG, ?_, ?_, ?_, ?_⟩
  · rw [hk.mem, hk.get bf (not_mem_x12 h.baseF), hk.get .x12]; exact h.valueF
  · rw [hk.mem, hk.get bg (not_mem_x12 h.baseG), hk.get .x12]; exact h.valueG
  · rw [hk.rd, hk.wr, hk.get bf (not_mem_x12 h.baseF), hk.get .x12]; exact h.readF
  · rw [hk.rd, hk.wr, hk.get bg (not_mem_x12 h.baseG), hk.get .x12]; exact h.readG

/-- The coefficients `8 … 15`. -/
abbrev upper (F : Nat → Nat) : Nat → Nat := fun i => F (8 + i)

theorem fullTermW_ok {s : State} {bf bg : Reg} {fg : Nat × Nat} {lo hi : Nat → Sums} {F G : Nat → Nat}
    {n : Nat} (h : TermInputW s bf bg fg F G) (hc : VConsts s) (ha : AccumW s lo hi)
    (hlo : ∀ e < 4, (lo e).Bounded n) (hhi : ∀ e < 4, (hi e).Bounded n) (hn : n < 4) :
    WP isa (.block (Impl.MlKem.AArch64.DotW.termW bf bg fg)) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧
        AccumW s' (advance lo F G) (advance hi (upper F) (upper G)) := by
  rw [termW_partition, WP.block_append_iff]
  refine WP.mono (pointersW_ok h.baseF h.baseG h.offF h.offG) fun s₁ ⟨h₁, v₁, e₁, e₂⟩ => ?_
  have hc₁ : VConsts s₁ := ⟨by rw [v₁]; exact hc.q, by rw [v₁]; exact hc.m⟩
  have ha₁ : AccumW s₁ lo hi := by simpa only [AccumW, Accum, v₁] using ha
  have nlo : ∀ e < 4, (advance lo F G e).Bounded (n + 1) := fun e he =>
    (hlo e he).next (h.boundF _ (by omega_using [he])) (h.boundF _ (by omega_using [he])) (h.boundG _ (by omega_using [he]))
      (h.boundG _ (by omega_using [he]))
  have nhi : ∀ e < 4, (advance hi (upper F) (upper G) e).Bounded (n + 1) := fun e he =>
    (hhi e he).next (h.boundF _ (by omega_using [he])) (h.boundF _ (by omega_using [he])) (h.boundG _ (by omega_using [he]))
      (h.boundG _ (by omega_using [he]))
  rw [List.append_assoc, ← List.append_nil accumulateW]
  refine loads_ok (fun i hi => by rw [h₁.rd, h₁.wr, e₁]; exact h.readF i hi)
    (fun i hi => by rw [h₁.rd, h₁.wr, e₂]; exact h.readG i hi) fun s₂ c₂ l0 l1 l4 l5 => ?_
  have f0 : HLanes (s₂.v .v0) F := by
    rw [l0, e₁, h₁.mem, ← BitVec.add_zero (s.gpr bf + BitVec.ofNat 64 fg.1 + s.gpr .x12),
      show (0#64 : BitVec 64) = BitVec.ofNat 64 (2 * 0) from rfl]
    exact hlanes_coeffs _ _ 0 fun e he => by rw [Nat.zero_add]; exact h.valueF e (by omega_using [he])
  have f1 : HLanes (s₂.v .v1) (upper F) := by
    rw [l1, e₁, h₁.mem, show BitVec.ofNat 64 16 = BitVec.ofNat 64 (2 * 8) from rfl]
    exact hlanes_coeffs _ _ 8 fun e he => h.valueF (8 + e) (by omega_using [he])
  have g0 : HLanes (s₂.v .v4) G := by
    rw [l4, e₂, h₁.mem, ← BitVec.add_zero (s.gpr bg + BitVec.ofNat 64 fg.2 + s.gpr .x12),
      show (0#64 : BitVec 64) = BitVec.ofNat 64 (2 * 0) from rfl]
    exact hlanes_coeffs _ _ 0 fun e he => by rw [Nat.zero_add]; exact h.valueG e (by omega_using [he])
  have g1 : HLanes (s₂.v .v5) (upper G) := by
    rw [l5, e₂, h₁.mem, show BitVec.ofNat 64 16 = BitVec.ofNat 64 (2 * 8) from rfl]
    exact hlanes_coeffs _ _ 8 fun e he => h.valueG (8 + e) (by omega_using [he])
  refine gatherW_ok f0 f1 g0 g1 fun s₃ c₃ fe fo ge go => ?_
  have ha₃ : AccumW s₃ lo hi := by
    obtain ⟨⟨a1, a2, a3⟩, a5, a6, a7⟩ := ha₁
    exact ⟨⟨by rw [c₃.get .v21, c₂.get .v21]; exact a1, by rw [c₃.get .v22, c₂.get .v22]; exact a2,
      by rw [c₃.get .v23, c₂.get .v23]; exact a3⟩, by rw [c₃.get .v25, c₂.get .v25]; exact a5,
      by rw [c₃.get .v26, c₂.get .v26]; exact a6, by rw [c₃.get .v27, c₂.get .v27]; exact a7⟩
  have wl : ∀ e < 4, ∀ {x : Sums}, x.Bounded (n + 1) → x.even < 2 ^ 32 ∧ x.odd < 2 ^ 32 ∧ x.cross < 2 ^ 32 :=
    fun e _ x hx => by
      have := hx.noWrap (by omega_using [hn])
      exact ⟨by omega_using [this], by omega_using [this], by omega_using [this]⟩
  refine accumulateW_ok ha₃ fe fo ge go (fun e he => wl e he (nlo e he))
    (fun e he => wl e he (by
      have := nhi e he
      simp only [advance, upper] at this
      rw [show 8 + 2 * e = 2 * (4 + e) by omega_using [], show 8 + (2 * e + 1) = 2 * (4 + e) + 1 by omega_using []] at this
      exact this)) fun s₄ c₄ a₄ => wp_nil ?_
  have eqhi : (fun e => (hi e).next (F (2 * (4 + e))) (F (2 * (4 + e) + 1)) (G (2 * (4 + e)))
      (G (2 * (4 + e) + 1))) = advance hi (upper F) (upper G) := by
    funext e
    simp only [advance, upper]
    rw [show 8 + 2 * e = 2 * (4 + e) by omega_using [], show 8 + (2 * e + 1) = 2 * (4 + e) + 1 by omega_using []]
  rw [eqhi] at a₄
  have C := (c₂.trans c₃).trans c₄
  refine ⟨?_, hc₁.chg C, a₄⟩
  exact ⟨fun r hr => by rw [C.gpr]; exact h₁.gpr r hr, C.mem.trans h₁.mem, C.rd.trans h₁.rd,
    C.wr.trans h₁.wr, C.sp.trans h₁.sp, fun r hr => by rw [C.v r (by revert r hr; decide +kernel)]; exact h₁.vcs r hr⟩

end VG.Proof.MlKem.AArch64.DotW

end

end

/-! ### `MlKem.AArch64.DotW.Compute`, which only this module used -/

section

/-! ### `MlKem.AArch64.DotW.Finish`, which only this module used -/

section

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: the terms and the finish

All the terms (`termsW_ok`), and the reduction of each group of sums
(`finishR_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Dot

theorem termsW_ok {bf bg : Reg} (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Nat → Nat}
    {s : State} {lo hi : Nat → Sums} {n : Nat}
    (hc : VConsts s) (ha : AccumW s lo hi) (hlo : ∀ e < 4, (lo e).Bounded n)
    (hhi : ∀ e < 4, (hi e).Bounded n) (hn : n + terms.length ≤ 4)
    (hin : ∀ fg ∈ terms, TermInputW s bf bg fg (F fg) (G fg)) :
    WP isa (.block (terms.flatMap (Impl.MlKem.AArch64.DotW.termW bf bg))) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧
        AccumW s' (sumTerms terms F G lo) (sumTerms terms (fun fg => upper (F fg)) (fun fg => upper (G fg)) hi) := by
  induction terms generalizing s lo hi n with
  | nil => exact wp_nil ⟨Only.refl _ _, hc, ha⟩
  | cons fg terms ih =>
    simp only [List.length_cons] at hn
    rw [List.flatMap_cons, WP.block_append_iff]
    have h := hin fg (by simp)
    refine WP.mono (fullTermW_ok h hc ha hlo hhi (by omega_using [hn])) fun s₁ ⟨hk, hc₁, ha₁⟩ => ?_
    refine WP.mono (ih hc₁ ha₁ (n := n + 1)
      (fun e he => (hlo e he).next (h.boundF _ (by omega_using [he])) (h.boundF _ (by omega_using [he]))
        (h.boundG _ (by omega_using [he])) (h.boundG _ (by omega_using [he])))
      (fun e he => (hhi e he).next (h.boundF _ (by omega_using [he])) (h.boundF _ (by omega_using [he]))
        (h.boundG _ (by omega_using [he])) (h.boundG _ (by omega_using [he])))
      (by omega_using [hn]) (fun fg hf => (hin fg (by simp [hf])).keep hk)) fun s₂ ⟨hk₂, hc₂, ha₂⟩ => ?_
    exact ⟨(hk.trans hk₂).mono (by simp), hc₂, ha₂⟩

section
variable {rest : List Instr} {Q : State → Prop}

/-- `sqdmulh t, d, M; mls d, t, q; vcsub d t`: `d mod q`, for lanes less than `2³¹`. -/
theorem reduceR_ok {s : State} {d t : VReg} (hdt : d ≠ t := by decide) (ht16 : t ≠ .v16 := by decide)
    (ht17 : t ≠ .v17 := by decide) (hd16 : d ≠ .v16 := by decide) (hd17 : d ≠ .v17 := by decide)
    (hc : VConsts s) {f : Nat → Nat} (hf : Lanes (s.v d) f) (hlt : ∀ e < 4, f e < 2 ^ 31)
    (k : ∀ s', VChg [t, d] s s' → Lanes (s'.v d) (fun e => f e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block ([.vop (.sqdmulh t d .v17), .vop (.mls d t .v16)] ++ vcsub d t ++ rest)) s Q := by
  simp only [List.cons_append, List.nil_append]
  refine vbar_ok hdt ht16 ht17 (hc := hc) (hf := hf) (hlt := hlt) (k := fun s₁ h₁ l₁ b₁ => ?_)
  have c₁ := hc.chg h₁ (by simp [hd16.symm, ht16.symm]) (by simp [hd17.symm, ht17.symm])
  refine vcsub_ok hdt c₁.q l₁ (fun e he => (b₁ e he).1) fun s₂ h₂ l₂ => ?_
  exact k s₂ ((h₁.trans h₂).mono (by simp)) (l₂.congr fun e he => (b₁ e he).2)

/-- `finishR a b c g t`: `(A + B · Γ) mod q` in `a` and `C mod q` in `c`. -/
theorem finishR_ok {s : State} {a b c g t : VReg}
    (hab : a ≠ b := by decide) (hac : a ≠ c := by decide) (hat : a ≠ t := by decide)
    (hbc : b ≠ c := by decide) (hbt : b ≠ t := by decide) (hct : c ≠ t := by decide)
    (hgb : g ≠ b := by decide) (hgt : g ≠ t := by decide)
    (ha16 : a ≠ .v16 := by decide) (ha17 : a ≠ .v17 := by decide)
    (hb16 : b ≠ .v16 := by decide) (hb17 : b ≠ .v17 := by decide)
    (hc16 : c ≠ .v16 := by decide) (hc17 : c ≠ .v17 := by decide)
    (ht16 : t ≠ .v16 := by decide) (ht17 : t ≠ .v17 := by decide)
    (hc : VConsts s) {A B C G : Nat → Nat}
    (la : Lanes (s.v a) A) (lb : Lanes (s.v b) B) (lc : Lanes (s.v c) C) (lg : Lanes (s.v g) G)
    (ba : ∀ e < 4, A e ≤ 4 * 3329 * 3329) (bb : ∀ e < 4, B e ≤ 4 * 3329 * 3329)
    (bc : ∀ e < 4, C e ≤ 8 * 3329 * 3329) (bg : ∀ e < 4, G e < 3329)
    (k : ∀ s', VChg ([t, b] ++ [a] ++ [t, a] ++ [t, c]) s s' →
      Lanes (s'.v a) (fun e => (A e + B e * G e) % 3329) →
      Lanes (s'.v c) (fun e => C e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.MlKem.AArch64.DotW.finishR a b c g t ++ rest)) s Q := by
  simp only [Impl.MlKem.AArch64.DotW.finishR, List.append_assoc, List.cons_append, List.nil_append]
  refine vbar_ok (d := b) (t := t) hbt ht16 ht17 (hc := hc) (hf := lb)
    (hlt := fun e he => by have := bb e he; omega_using [this]) (k := fun s₁ h₁ l₁ b₁ => ?_)
  have a₁ : Lanes (s₁.v a) A := by rw [h₁.get a (by simp [hat, hab])]; exact la
  have g₁ : Lanes (s₁.v g) G := by rw [h₁.get g (by simp [hgt, hgb])]; exact lg
  let R := fun e => B e - B e * 645083 / 2 ^ 31 * 3329
  try rewrite [show fun e => B e - B e * 645083 / 2 ^ 31 * 3329 = R from rfl] at *
  have br : ∀ e < 4, R e * G e ≤ 2 * 3329 * 3329 := fun e he =>
    Nat.mul_le_mul (Nat.le_of_lt (b₁ e he).1) (Nat.le_of_lt (bg e he))
  have bylt : ∀ e < 4, A e + R e * G e < 2 ^ 31 := fun e he => by
    have := ba e he; have := br e he; omega_arith
  refine wp_vop (d := a) rfl fun s₂ h₂ => ?_
  have l₂ : Lanes (s₂.v a) (fun e => A e + R e * G e) := by
    rw [h₂.v]
    exact (lanes_mla a₁ l₁ g₁).congr fun e he => by
      have := bylt e he
      rw [Nat.mod_eq_of_lt (show R e * G e < 2 ^ 32 by omega_using [this]),
        Nat.mod_eq_of_lt (show A e + R e * G e < 2 ^ 32 by omega_using [this])]
  have c₂ := (hc.chg h₁ (by simp [hb16.symm, ht16.symm]) (by simp [hb17.symm, ht17.symm])).chg h₂.chg
    (by simp [ha16.symm]) (by simp [ha17.symm])
  rw [← List.cons_append, ← List.cons_append]
  refine reduceR_ok (d := a) (t := t) hat ht16 ht17 ha16 ha17 c₂ l₂ bylt fun s₃ h₃ l₃ => ?_
  have c₃ := c₂.chg h₃ (by simp [ha16.symm, ht16.symm]) (by simp [ha17.symm, ht17.symm])
  have cval : Lanes (s₃.v c) C := by
    rw [h₃.get c (by simp [hct, hac.symm]), h₂.get c hac.symm, h₁.get c (by simp [hct, hbc.symm])]
    exact lc
  rw [← List.cons_append, ← List.cons_append]
  refine reduceR_ok (d := c) (t := t) hct ht16 ht17 hc16 hc17 c₃ cval
    (fun e he => by have := bc e he; omega_using [this]) fun s₄ h₄ l₄ => ?_
  refine k s₄ (((h₁.trans h₂.chg).trans h₃).trans h₄) ?_ l₄
  rw [h₄.get a (by simp [hat, hac])]
  refine l₃.congr fun e he => ?_
  rw [Nat.add_mod, Nat.mul_mod, (b₁ e he).2, ← Nat.mul_mod, ← Nat.add_mod]

end

end VG.Proof.MlKem.AArch64.DotW

end

end


/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: an iteration's sums

`clearW`, the terms, the two tables of `γ` and the two finishes (`computeW_ok`):
the even and odd results of pairs `0 … 3` in `v21`, `v23` and of pairs `4 … 7`
in `v25`, `v27`, as `dot`'s `evenResult` and `oddResult`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

section
variable {rest : List Instr} {Q : State → Prop}

theorem clearW_ok {s : State}
    (k : ∀ s', VChg [.v21, .v22, .v23, .v25, .v26, .v27] s s' → AccumW s' zeroSums zeroSums →
      WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.MlKem.AArch64.DotW.clearW ++ rest)) s Q := by
  simp only [Impl.MlKem.AArch64.DotW.clearW, List.cons_append, List.nil_append]
  refine wp_vop (d := .v21) rfl fun s₁ h₁ => wp_vop (d := .v22) rfl fun s₂ h₂ =>
    wp_vop (d := .v23) rfl fun s₃ h₃ => wp_vop (d := .v25) rfl fun s₄ h₄ =>
    wp_vop (d := .v26) rfl fun s₅ h₅ => wp_vop (d := .v27) rfl fun s₆ h₆ => ?_
  refine k s₆ (((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans h₅.chg).trans h₆.chg).mono
    ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [h₆.get .v21, h₅.get .v21, h₄.get .v21, h₃.get .v21, h₂.get .v21, h₁.v]; exact zeroLanes
  · rw [h₆.get .v22, h₅.get .v22, h₄.get .v22, h₃.get .v22, h₂.v]; exact zeroLanes
  · rw [h₆.get .v23, h₅.get .v23, h₄.get .v23, h₃.v]; exact zeroLanes
  · rw [h₆.get .v25, h₅.get .v25, h₄.v]; exact zeroLanes
  · rw [h₆.get .v26, h₅.v]; exact zeroLanes
  · rw [h₆.v]; exact zeroLanes

end

def computeW (bf bg : Reg) (terms : List (Nat × Nat)) : List Instr :=
  Impl.MlKem.AArch64.DotW.clearW ++ terms.flatMap (Impl.MlKem.AArch64.DotW.termW bf bg) ++
    [.ldrq .v18 .x3 0, .ldrq .v28 .x3 16] ++
    Impl.MlKem.AArch64.DotW.finishR .v21 .v22 .v23 .v18 .v24 ++
    Impl.MlKem.AArch64.DotW.finishR .v25 .v26 .v27 .v28 .v24

theorem computeW_ok {s : State} {rF rG : Reg} (terms : List (Nat × Nat))
    {F G : (Nat × Nat) → Nat → Nat} {Γ Γ' : Nat → Nat}
    (hc : VConsts s) (hn : terms.length ≤ 4)
    (hin : ∀ fg ∈ terms, TermInputW s rF rG fg (F fg) (G fg))
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * i)) 16)
    (hg : Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 0) 16) Γ)
    (hg' : Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 16) 16) Γ')
    (bg : ∀ e < 4, Γ e < 3329) (bg' : ∀ e < 4, Γ' e < 3329) :
    WP isa (.block (computeW rF rG terms)) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧
      Lanes (s'.v .v21) (evenResult terms F G Γ) ∧ Lanes (s'.v .v23) (oddResult terms F G) ∧
      Lanes (s'.v .v25) (evenResult terms (fun fg => upper (F fg)) (fun fg => upper (G fg)) Γ') ∧
      Lanes (s'.v .v27) (oddResult terms (fun fg => upper (F fg)) (fun fg => upper (G fg))) := by
  simp only [computeW, List.append_assoc]
  refine clearW_ok fun s₁ h₁ a₁ => ?_
  have k₁ := only_vchg h₁
  have input₁ : ∀ fg ∈ terms, TermInputW s₁ rF rG fg (F fg) (G fg) :=
    fun fg hf => (hin fg hf).keep (k₁.mono (by simp))
  rw [WP.block_append_iff]
  have z : ∀ e < 4, (zeroSums e).Bounded 0 := fun _ _ => by simp only [zeroSums, Sums.Bounded]; decide
  refine WP.mono (termsW_ok terms (hc.chg h₁) a₁ z z (by simpa only [Nat.zero_add] using hn) input₁)
    fun s₂ ⟨k₂, c₂, a₂⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrq (by decide) rfl
    (by rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr, k₂.get .x3, k₁.get .x3]; exact hr 0 (by decide)) fun s₃ h₃ => ?_
  refine wp_ldrq (by decide) rfl
    (by rw [h₃.rd, h₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr, h₃.gpr, k₂.get .x3, k₁.get .x3]; exact hr 1 (by decide))
    fun s₄ h₄ => ?_
  have g₄ : Lanes (s₄.v .v18) Γ := by
    rw [h₄.get .v18, h₃.v, k₂.mem, k₁.mem, k₂.get .x3, k₁.get .x3]; exact hg
  have g₄' : Lanes (s₄.v .v28) Γ' := by
    rw [h₄.v, h₃.mem, k₂.mem, k₁.mem, h₃.gpr, k₂.get .x3, k₁.get .x3]; exact hg'
  have blo : ∀ e < 4, (sumTerms terms F G zeroSums e).Bounded terms.length := by
    simpa only [Nat.zero_add] using sumTerms_bound terms (n := 0) (a := zeroSums) z
      (fun fg hf e he => (hin fg hf).boundF e (by omega_using [he])) (fun fg hf e he => (hin fg hf).boundG e (by omega_using [he]))
  have bhi : ∀ e < 4, (sumTerms terms (fun fg => upper (F fg)) (fun fg => upper (G fg)) zeroSums e).Bounded
      terms.length := by
    simpa only [Nat.zero_add] using sumTerms_bound terms (n := 0) (a := zeroSums) z
      (fun fg hf e he => (hin fg hf).boundF (8 + e) (by omega_using [he]))
      (fun fg hf e he => (hin fg hf).boundG (8 + e) (by omega_using [he]))
  have C₄ := h₃.chg.trans h₄.chg
  obtain ⟨⟨a21, a22, a23⟩, a25, a26, a27⟩ := a₂
  have c₄ := c₂.chg C₄
  refine finishR_ok (a := .v21) (b := .v22) (c := .v23) (g := .v18) (t := .v24) (hc := c₄)
    (la := by rw [C₄.get .v21]; exact a21) (lb := by rw [C₄.get .v22]; exact a22)
    (lc := by rw [C₄.get .v23]; exact a23) (lg := g₄)
    (ba := fun e he => ((blo e he).machine hn).1) (bb := fun e he => ((blo e he).machine hn).2.1)
    (bc := fun e he => ((blo e he).machine hn).2.2) (bg := bg) (k := fun s₅ h₅ l21 l23 => ?_)
  rw [← List.append_nil (Impl.MlKem.AArch64.DotW.finishR _ _ _ _ _)]
  refine finishR_ok (a := .v25) (b := .v26) (c := .v27) (g := .v28) (t := .v24) (hc := c₄.chg h₅)
    (la := by rw [h₅.get .v25, C₄.get .v25]; exact a25) (lb := by rw [h₅.get .v26, C₄.get .v26]; exact a26)
    (lc := by rw [h₅.get .v27, C₄.get .v27]; exact a27) (lg := by rw [h₅.get .v28]; exact g₄')
    (ba := fun e he => ((bhi e he).machine hn).1) (bb := fun e he => ((bhi e he).machine hn).2.1)
    (bc := fun e he => ((bhi e he).machine hn).2.2) (bg := bg') (k := fun s₆ h₆ l25 l27 => wp_nil ?_)
  exact ⟨((((k₁.trans k₂).trans (only_vchg C₄)).trans (only_vchg h₅)).trans (only_vchg h₆)).mono (by simp),
    (c₄.chg h₅).chg h₆, by rw [h₆.get .v21]; exact l21, by rw [h₆.get .v23]; exact l23, l25, l27⟩

end VG.Proof.MlKem.AArch64.DotW

end

end


/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64

Sixteen iterations of 16 coefficients (`loopW_ok`), each one `dot`'s blocks
`2c` and `2c + 1` (`stepW_ok`): `dotW out terms` writes `Σ F ∘ G` with 16-bit
coefficients to `bo + out` (`dotW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

theorem coeffAtW16_shift (m : Mem) (p : Addr) (j e : Nat) :
    coeffAtW 16 m (p + BitVec.ofNat 64 (2 * j)) e = coeffAtW 16 m p (j + e) := by
  simp only [coeffAtW]
  rw [ptr_add, show 2 * j + 16 / 8 * e = 16 / 8 * (j + e) by omega_using []]

/-- What the loop needs, from the state before it: the polynomials of each term, the output
apart from them and from the table of `γ`. -/
structure LoopDataW (s₀ : State) (bf bg : Reg) (p t : Addr) (terms : List (Nat × Nat))
    (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat) : Prop where
  baseF : bf ∉ clob
  baseG : bg ∉ clob
  count : terms.length ≤ 4
  offF : ∀ fg ∈ terms, fg.1 < 65536
  offG : ∀ fg ∈ terms, fg.2 < 65536
  boundF : ∀ fg ∈ terms, ∀ i < 256, F fg i < 3329
  boundG : ∀ fg ∈ terms, ∀ i < 256, G fg i < 3329
  valueF : ∀ fg ∈ terms, ∀ i < 256,
    (coeffAtW 16 s₀.mem (s₀.gpr bf + BitVec.ofNat 64 fg.1) i).toNat = F fg i
  valueG : ∀ fg ∈ terms, ∀ i < 256,
    (coeffAtW 16 s₀.mem (s₀.gpr bg + BitVec.ofNat 64 fg.2) i).toNat = G fg i
  apartF : ∀ fg ∈ terms, (⟨p, 512⟩ : Region).Disjoint ⟨s₀.gpr bf + BitVec.ofNat 64 fg.1, 512⟩
  apartG : ∀ fg ∈ terms, (⟨p, 512⟩ : Region).Disjoint ⟨s₀.gpr bg + BitVec.ofNat 64 fg.2, 512⟩
  readF : ∀ fg ∈ terms, ∀ o, o + 16 ≤ 512 →
    InRegions (s₀.rd ++ s₀.wr) (s₀.gpr bf + BitVec.ofNat 64 fg.1 + BitVec.ofNat 64 o) 16
  readG : ∀ fg ∈ terms, ∀ o, o + 16 ≤ 512 →
    InRegions (s₀.rd ++ s₀.wr) (s₀.gpr bg + BitVec.ofNat 64 fg.2 + BitVec.ofNat 64 o) 16
  write : ∀ o, o + 16 ≤ 512 → InRegions s₀.wr (p + BitVec.ofNat 64 o) 16
  tableApart : (⟨p, 512⟩ : Region).Disjoint ⟨t, 512⟩
  tableRead : ∀ c < 32, InRegions (s₀.rd ++ s₀.wr) (t + BitVec.ofNat 64 (16 * c)) 16
  tableValue : ∀ c < 32, Lanes (s₀.mem.read (t + BitVec.ofNat 64 (16 * c)) 16) (blockGamma Γ c)
  tableBound : ∀ i < 128, Γ i < 3329

/-- After `c` iterations. -/
structure LoopInvW (s₀ : State) (p t : Addr) (O : Nat → BitVec 16) (c : Nat) (s : State) : Prop where
  keep : Keep clob s₀ s
  frame : Frame [⟨p, 512⟩] s₀.mem s.mem
  constants : VConsts s
  x0 : s.gpr .x0 = p + BitVec.ofNat 64 (2 * (16 * c))
  x3 : s.gpr .x3 = t + BitVec.ofNat 64 (32 * c)
  x12 : s.gpr .x12 = BitVec.ofNat 64 (32 * c)
  x11 : (s.gpr .x11).toNat = 16 - c
  out : CoeffsInW s.mem p (· < 16 * c) O (fun i => coeffAtW 16 s₀.mem p i)

/-- The coefficients of the result, as 16-bit values. -/
def resultW (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat) (j : Nat) :
    BitVec 16 :=
  BitVec.ofNat 16 (result terms F G Γ j).toNat

/-- A 16-bit coefficient of a polynomial apart from the frame. -/
theorem coeffAtW16_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {q : Addr}
    (hd : ∀ r ∈ rs, (⟨q, 512⟩ : Region).Disjoint r) {i : Nat} (hi : i < 256) :
    coeffAtW 16 m' q i = coeffAtW 16 m q i :=
  hf.readW (r := ⟨q, 512⟩) (contains_off (show 2 * i + 16 / 8 ≤ 512 by omega_using [hi]) (by decide)) hd (by decide)

theorem loop_inputW {s₀ s : State} {bf bg : Reg} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {O : Nat → BitVec 16} {c : Nat}
    (hd : LoopDataW s₀ bf bg p t terms F G Γ) (hc : c < 16) (h : LoopInvW s₀ p t O c s)
    {fg : Nat × Nat} (hf : fg ∈ terms) :
    TermInputW s bf bg fg (blockValues F (2 * c) fg) (blockValues G (2 * c) fg) := by
  have addr (b : Reg) (hb : b ∉ clob) (off : Nat) : s.gpr b + BitVec.ofNat 64 off + s.gpr .x12 =
      s₀.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (2 * (16 * c)) := by
    rw [h.keep.get b hb, h.x12, show 32 * c = 2 * (16 * c) by omega_using []]
  refine ⟨hd.baseF, hd.baseG, hd.offF fg hf, hd.offG fg hf, fun e he => hd.boundF fg hf _ (by omega_using [hc, he]),
    fun e he => hd.boundG fg hf _ (by omega_using [hc, he]), fun e he => ?_, fun e he => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [addr bf hd.baseF, coeffAtW16_shift, coeffAtW16_frame h.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hd.apartF fg hf).symm) (by omega_using [hc, he]), hd.valueF fg hf _ (by omega_using [hc, he])]
    simp only [blockValues]; congr 1; omega_using []
  · rw [addr bg hd.baseG, coeffAtW16_shift, coeffAtW16_frame h.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hd.apartG fg hf).symm) (by omega_using [hc, he]), hd.valueG fg hf _ (by omega_using [hc, he])]
    simp only [blockValues]; congr 1; omega_using []
  · rw [h.keep.rd, h.keep.wr, addr bf hd.baseF, ptr_add]
    exact hd.readF fg hf _ (by omega_using [hc, hi])
  · rw [h.keep.rd, h.keep.wr, addr bg hd.baseG, ptr_add]
    exact hd.readG fg hf _ (by omega_using [hc, hi])

theorem loop_gammaW {s₀ s : State} {bf bg : Reg} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {O : Nat → BitVec 16} {c : Nat}
    (hd : LoopDataW s₀ bf bg p t terms F G Γ) (hc : c < 16) (h : LoopInvW s₀ p t O c s) {i : Nat} (hi : i < 2) :
    Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * i)) 16) (blockGamma Γ (2 * c + i)) := by
  rw [h.x3, ptr_add, h.frame.read (r := ⟨t, 512⟩) (contains_off (by omega_using [hc, hi]) (by decide))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.tableApart.symm) (by decide),
    show 32 * c + 16 * i = 16 * (2 * c + i) by omega_using []]
  exact hd.tableValue _ (by omega_using [hc, hi])

theorem upper_block (F : (Nat × Nat) → Nat → Nat) (c : Nat) :
    (fun fg => upper (blockValues F (2 * c) fg)) = blockValues F (2 * c + 1) := by
  funext fg i
  simp only [upper, blockValues]
  congr 1; omega_using []

/-- A 16-bit result coefficient, from `dot`'s block and its pairs. -/
theorem resultW_toNat (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat)
    (c : Nat) {e : Nat} (he : e < 8) :
    (resultW terms F G Γ (8 * c + e)).toNat =
      if e % 2 = 0 then evenResult terms (blockValues F c) (blockValues G c) (blockGamma Γ c) (e / 2)
      else oddResult terms (blockValues F c) (blockValues G c) (e / 2) := by
  rw [resultW, result_block terms F G Γ c he, interleave, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  split
  · simp only [evenResult]; omega_using []
  · simp only [oddResult]; omega_using []

theorem bodyW_partition (bf bg : Reg) (terms : List (Nat × Nat)) :
    Impl.MlKem.AArch64.DotW.bodyW bf bg terms =
      computeW bf bg terms ++ Impl.MlKem.AArch64.DotW.storeW ++ Impl.MlKem.AArch64.DotW.bumpW := by
  simp only [Impl.MlKem.AArch64.DotW.bodyW, computeW, List.append_assoc]

theorem bumpW_ok (s : State) : WP isa (.block Impl.MlKem.AArch64.DotW.bumpW) s fun s' =>
    Only [.x0, .x3, .x12, .x11] s s' ∧ s'.v = s.v ∧
    s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 32 ∧
    s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 32 ∧
    s'.gpr .x12 = s.gpr .x12 + BitVec.ofNat 64 32 ∧
    s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 := by
  refine WP.mono (WP.keepV (Q := fun s' => Only [.x0, .x3, .x12, .x11] s s' ∧
    s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 32 ∧
    s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 32 ∧
    s'.gpr .x12 = s.gpr .x12 + BitVec.ofNat 64 32 ∧
    s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1) (by decide) ?_) ?_
  · refine wp_addImm (by decide) fun s₁ h₁ e₁ => wp_addImm (by decide) fun s₂ h₂ e₂ =>
      wp_addImm (by decide) fun s₃ h₃ e₃ => wp_subImm (by decide) fun s₄ h₄ e₄ => wp_nil ?_
    exact ⟨(((h₁.trans h₂).trans h₃).trans h₄).mono,
      by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁],
      by rw [h₄.get .x3, h₃.get .x3, e₂, h₁.get .x3],
      by rw [h₄.get .x12, e₃, h₂.get .x12, h₁.get .x12],
      by rw [e₄, h₃.get .x11, h₂.get .x11, h₁.get .x11]⟩
  · intro s' h; exact ⟨h.1.1, h.2, h.1.2⟩

theorem stepW_ok {s₀ s : State} {bf bg : Reg} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {c : Nat}
    (hd : LoopDataW s₀ bf bg p t terms F G Γ) (hc : c < 16)
    (h : LoopInvW s₀ p t (resultW terms F G Γ) c s) :
    WP isa (.block (Impl.MlKem.AArch64.DotW.bodyW bf bg terms)) s fun s' =>
      LoopInvW s₀ p t (resultW terms F G Γ) (c + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ c + 1 ≠ 16) := by
  rw [bodyW_partition, List.append_assoc, WP.block_append_iff]
  refine WP.mono (computeW_ok terms (Γ := blockGamma Γ (2 * c)) (Γ' := blockGamma Γ (2 * c + 1))
    h.constants hd.count (fun _ hf => loop_inputW hd hc h hf)
    (fun i hi => by
      rw [h.keep.rd, h.keep.wr, h.x3, ptr_add, show 32 * c + 16 * i = 16 * (2 * c + i) by omega_using []]
      exact hd.tableRead _ (by omega_using [hc, hi]))
    (by simpa only [Nat.mul_zero, Nat.add_zero] using loop_gammaW hd hc h (i := 0) (by decide))
    (by simpa only [Nat.mul_one] using loop_gammaW hd hc h (i := 1) (by decide))
    (fun e he => show Γ _ < 3329 from hd.tableBound _ (by omega_using [hc, he]))
    (fun e he => show Γ _ < 3329 from hd.tableBound _ (by omega_using [hc, he]))) fun s₁ ⟨k₁, c₁, l21, l23, l25, l27⟩ => ?_
  rw [upper_block, upper_block] at l25 l27
  rw [WP.block_append_iff]
  refine WP.mono (storeW_ok (p := p) (j := 16 * c) (O := resultW terms F G Γ)
    (old := fun i => coeffAtW 16 s₀.mem p i) (by rw [k₁.get .x0]; exact h.x0) (by omega_using [hc])
    (fun i hi => by rw [k₁.wr, h.keep.wr]; exact hd.write _ (by omega_using [hc, hi])) c₁ l21 l23 l25 l27
    (fun e he => Nat.mod_lt _ (by decide)) (fun e he => Nat.mod_lt _ (by decide))
    (fun e he => Nat.mod_lt _ (by decide)) (fun e he => Nat.mod_lt _ (by decide))
    (by rw [k₁.mem]; exact h.out) fun e he => ?_) fun s₂ ⟨k₂, c₂, f₂, o₂⟩ => ?_
  · unfold outW
    by_cases c8 : e < 8
    · rw [ite_eq_left c8, show 16 * c + e = 8 * (2 * c) + e by omega_using [], resultW_toNat _ _ _ _ _ c8]
    · rw [ite_eq_right c8, show 16 * c + e = 8 * (2 * c + 1) + (e - 8) by omega_using [c8],
        resultW_toNat _ _ _ _ _ (by omega_using [he]), show (e - 8) % 2 = e % 2 by omega_using [c8]]
  refine WP.mono (bumpW_ok s₂) fun s₃ ⟨k₃, v₃, e0, e3, e12, e11⟩ => ?_
  have counter : (s₃.gpr .x11).toNat = 16 - (c + 1) := by
    rw [e11, k₂.get .x11, k₁.get .x11, toNat_sub_n (by rw [h.x11]; simp only [BitVec.toNat_ofNat]; omega_using [hc]), h.x11]
    simp only [BitVec.toNat_ofNat]
    omega_using []
  refine ⟨⟨((h.keep.trans ((k₁.keep.trans k₂).trans k₃.keep)).mono), h.frame.trans ?_,
    ⟨by rw [v₃]; exact c₂.q, by rw [v₃]; exact c₂.m⟩, ?_, ?_, ?_, counter, ?_⟩, by rw [counter]; omega_using [hc]⟩
  · rw [k₃.mem, ← k₁.mem]; exact f₂
  · rw [e0, k₂.get .x0, k₁.get .x0, h.x0, ptr_add, show 2 * (16 * c) + 32 = 2 * (16 * (c + 1)) by omega_using []]
  · rw [e3, k₂.get .x3, k₁.get .x3, h.x3, ptr_add, show 32 * c + 32 = 32 * (c + 1) by omega_using []]
  · rw [e12, k₂.get .x12, k₁.get .x12, h.x12, ← BitVec.ofNat_add, show 32 * c + 32 = 32 * (c + 1) by omega_using []]
  · rw [k₃.mem, show 16 * (c + 1) = 16 * c + 16 by omega_using []]; exact o₂

theorem loopW_ok {s₀ s : State} {bf bg : Reg} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat}
    (hd : LoopDataW s₀ bf bg p t terms F G Γ) (h : LoopInvW s₀ p t (resultW terms F G Γ) 0 s) :
    WP isa (.loop (.block (Impl.MlKem.AArch64.DotW.bodyW bf bg terms)) (.nonzero .x .x11)) s
      (LoopInvW s₀ p t (resultW terms F G Γ) 16) :=
  count_loop (by decide) (LoopInvW s₀ p t (resultW terms F G Γ)) (fun _ hc _ hi => stepW_ok hd hc hi) h

end VG.Proof.MlKem.AArch64.DotW

end

end

/-! ### `MlKem.AArch64.Kem16.DotReady`, which the modules that import this one used -/

section

/-! ### `MlKem.AArch64.DotW`, which the modules that import this one used -/

section

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64

`Impl.MlKem.AArch64.DotW.dotW bo bf bg out terms` writes `Σ F ∘ G`
(`polySum`) with 16-bit coefficients to `bo + out` (`dotW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Dot

def setupW (bo : Reg) (out : Nat) : List Instr := ptrTo .x0 bo out ++ vconsts ++
  [.adrSym .x3 "VG_MLKEM_GAMMA", .movz .x .x11 16 0, .movz .x .x12 0 0]

theorem setupW_ok {s : State} {bo : Reg} (hbo : bo ≠ .x0) {out : Nat} (ho : out < 65536)
    (O : Nat → BitVec 16) :
    WP isa (.block (setupW bo out)) s
      (LoopInvW s (s.gpr bo + BitVec.ofNat 64 out) (s.syms "VG_MLKEM_GAMMA") O 0) := by
  unfold setupW
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (wp_ptrTo' (d := .x0) (b := bo) (s := s)
    (Q := fun s' => Only [.x0] s s' ∧ s'.gpr .x0 = s.gpr bo + BitVec.ofNat 64 out)
    hbo.symm ho (fun _ hk hx => ⟨hk, hx⟩)) ?_
  intro s₁ h₁ sy₁
  rw [WP.block_append_iff]
  refine WP.mono_syms (Ntt.vconsts_ok s₁) ?_
  intro s₂ ⟨k₂, m₂, c₂, _⟩ sy₂
  refine WP.mono (WP.keepV (Q := fun s₃ => Only [.x3, .x11, .x12] s₂ s₃ ∧
    s₃.gpr .x3 = s₂.syms "VG_MLKEM_GAMMA" ∧ s₃.gpr .x11 = BitVec.ofNat 64 16 ∧ s₃.gpr .x12 = 0)
    (by rfl) (wp_x (by rfl) fun s₃ k₃ e₃ => wp_movz fun s₄ k₄ e₄ =>
      wp_movz fun s₅ k₅ e₅ => wp_nil ⟨((k₃.trans k₄).trans k₅).mono,
        by rw [k₅.get .x3, k₄.get .x3, e₃], by rw [k₅.get .x11, e₄]; rfl, by rw [e₅]; rfl⟩))
    fun s₃ ⟨⟨k₃, e₃, e11, e12⟩, v₃⟩ => ?_
  have hm : s₃.mem = s.mem := k₃.mem.trans (m₂.trans h₁.1.mem)
  refine ⟨((h₁.1.keep.trans k₂).trans k₃.keep).mono,
    by rw [hm]; exact Frame.refl _ _, ⟨by rw [v₃]; exact c₂.q, by rw [v₃]; exact c₂.m⟩,
    ?_, ?_, e12, ?_, ?_⟩
  · rw [k₃.get .x0, k₂.get .x0, h₁.2]; exact (BitVec.add_zero _).symm
  · rw [e₃, sy₂, sy₁]; exact (BitVec.add_zero _).symm
  · rw [e11]; rfl
  · rw [hm]; intro i _; rw [ite_eq_right (by omega_using [])]

theorem dotW_partition (bo bf bg : Reg) (out : Nat) (terms : List (Nat × Nat)) :
    Impl.MlKem.AArch64.DotW.dotW bo bf bg out terms =
      .seq (.block (setupW bo out))
        (.loop (.block (Impl.MlKem.AArch64.DotW.bodyW bf bg terms)) (.nonzero .x .x11)) := by
  simp only [Impl.MlKem.AArch64.DotW.dotW, setupW, List.append_assoc]

theorem dotW_ok {s : State} {bo bf bg : Reg} (hbo : bo ≠ .x0) {out : Nat} (ho : out < 65536)
    (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Poly}
    (hd : LoopDataW s bf bg (s.gpr bo + BitVec.ofNat 64 out) (s.syms "VG_MLKEM_GAMMA") terms
      (polyValues F) (polyValues G) gammaValues) :
    WP isa (Impl.MlKem.AArch64.DotW.dotW bo bf bg out terms) s fun s' =>
      Keep clob s s' ∧ Frame [⟨s.gpr bo + BitVec.ofNat 64 out, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr bo + BitVec.ofNat 64 out) (polySum terms F G) := by
  rw [dotW_partition]
  refine WP.seq (WP.mono (setupW_ok hbo ho (resultW terms (polyValues F) (polyValues G) gammaValues))
    fun s₁ h₁ => ?_)
  refine WP.mono (loopW_ok hd h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.keep, h₂.frame, h₂.out.polyIs (fun i hi => by omega_using [hi]) fun i hi => ?_⟩
  rw [resultW, result_field terms F G hi, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : ((polySum terms F G)[i]!).val < 3329 := Fin.isLt _
  change _ % 2 ^ 32 % 2 ^ 16 = _
  omega_using [this]

end VG.Proof.MlKem.AArch64.DotW

end

end

/-! # The fused dot product of 16-bit polynomials in 1024-byte buffers

`ReadyW`: what the fused dot product needs of polynomials stored with 16 bits
in the first half of
buffers of 1024 bytes, from which `ReadyW.data` gives `dotW`'s `LoopDataW`. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

structure ReadyW (s : State) (p t : Addr) (terms : List (Nat × Nat))
    (F G : (Nat × Nat) → Poly) : Prop where
  count : terms.length ≤ 4
  offF : ∀ fg ∈ terms, fg.1 < 65536
  offG : ∀ fg ∈ terms, fg.2 < 65536
  inputF : ∀ fg ∈ terms, PolyIsW 16 s.mem (s.gpr .x28+BitVec.ofNat 64 fg.1) (F fg)
  inputG : ∀ fg ∈ terms, PolyIsW 16 s.mem (s.gpr .x28+BitVec.ofNat 64 fg.2) (G fg)
  apartF : ∀ fg ∈ terms, (polyRegion p).Disjoint (polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.1))
  apartG : ∀ fg ∈ terms, (polyRegion p).Disjoint (polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.2))
  readF : ∀ fg ∈ terms, Covers [polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.1)] (s.rd++s.wr)
  readG : ∀ fg ∈ terms, Covers [polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.2)] (s.rd++s.wr)
  write : Covers [polyRegion p] s.wr
  tableApart : (polyRegion p).Disjoint ⟨t,512⟩
  tableRead : Covers [⟨t,512⟩] (s.rd++s.wr)
  table : GammaArtifact s.mem t

theorem half_sub (p : Addr) : Region.Sub ⟨p, 512⟩ (polyRegion p) := Region.sub_prefix (by decide)

theorem ReadyW.data {s : State} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Poly} (h : ReadyW s p t terms F G) :
    LoopDataW s .x28 .x28 p t terms (polyValues F) (polyValues G) gammaValues := by
  refine ⟨by decide, by decide, h.count, h.offF, h.offG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (h.tableApart.sub_left (half_sub p)), ?_, ?_, ?_⟩
  · intro fg _ i _; exact ((F fg)[i]!).isLt
  · intro fg _ i _; exact ((G fg)[i]!).isLt
  · intro fg hf i hi; exact polyIsW_toNat (h.inputF fg hf) hi
  · intro fg hf i hi; exact polyIsW_toNat (h.inputG fg hf) hi
  · intro fg hf; exact ((h.apartF fg hf).sub_left (half_sub p)).sub_right (half_sub _)
  · intro fg hf; exact ((h.apartG fg hf).sub_left (half_sub p)).sub_right (half_sub _)
  · intro fg hf o ho
    exact h.readF fg hf _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [ho]) (by decide)))
  · intro fg hf o ho
    exact h.readG fg hf _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [ho]) (by decide)))
  · intro o ho
    exact h.write _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [ho]) (by decide)))
  · intro c hc
    exact h.tableRead _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hc]) (by decide)))
  · intro c hc; exact h.table.lanes hc
  · intro i _; exact (gamma i).isLt

end VG.Proof.MlKem.AArch64.DotW

end

end

/-! ### `MlKem.AArch64.AddSubW`, which the modules that import this one used -/

section

/-! ### `MlKem.AArch64.Codec12W.Enc`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Codec16.EncLoop`, which only this module used -/

section

/-! ### `MlKem.AArch64.Codec16.Bytes`, which this module and modules that import it used -/

section

/-! # Contiguous stores in the 384-byte encoding -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64

theorem bytes_write {m : Mem} {p : Addr} {t n : Nat} {L old : Nat → Byte}
    (h : BytesUpTo m p 384 t L old) (hn : t+n ≤ 384) {x : BitVec (8*n)}
    (hx : ∀ i < n, x.extractLsb' (8*i) 8 = L (t+i)) :
    BytesUpTo (m.write (p+BitVec.ofNat 64 t) n x) p 384 (t+n) L old := by
  intro j hj
  have d : ((p+BitVec.ofNat 64 j)-(p+BitVec.ofNat 64 t)).toNat =
      if t ≤ j then j-t else 2^64+j-t := by
    exact Offset.sub_toNat' p (by omega_using [hn]) (by omega_using [hj])
  rw [Mem.write,d]
  by_cases ht : t ≤ j
  · rw [ite_eq_left ht]
    by_cases hnj : j-t<n
    · rw [ite_eq_left hnj,ite_eq_left (by omega_using [hnj]),hx _ hnj]
      congr 1; omega_using [ht]
    · rw [ite_eq_right hnj,h j hj,ite_eq_right (by omega_using [ht]),ite_eq_right (by omega_using [ht, hnj])]
  · rw [ite_eq_right ht,ite_eq_right (by omega_using [hn]),h j hj,ite_eq_left (by omega_using [ht]),ite_eq_left (by omega_using [ht])]

end VG.Proof.MlKem.AArch64.Codec16

end

end

/-! ### `MlKem.AArch64.Codec16.EncMath`, which this module and modules that import it used -/

section

/-! # Encoding arithmetic block -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Codec16 (encMath)

theorem math_ok (s : State) (hm : s.v .v16 = encMask) :
    WP isa (.block encMath) s fun t =>
      t.gpr .x9 = (tbl (packed (s.v .v0) (s.v .v1)) encMask).extractLsb' 0 64 ∧
      t.gpr .x10 = (tbl (packed (s.v .v0) (s.v .v1)) encMask).extractLsb' 64 64 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧ t.v .v16 = s.v .v16 := by
  unfold encMath
  rrun [hm,VShiftOp.eval,packed,tbl,RegUpd.sp_setV,RegUpd.sp_write]
  refine ⟨by rfl,by rfl,?_⟩
  intro r h9 h10
  simp only [h9,h10,ite_false]

end VG.Proof.MlKem.AArch64.Codec16

end

end

/-! # ML-KEM encoding eight coefficients at a time -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Codec16 (encMath maskVec)
open VG.Proof.Rc4.AArch64

theorem low_byte (v : BitVec 128) {j : Nat} (hj : j<8) :
    (v.extractLsb' 0 64).extractLsb' (8*j) 8 = vbyte v j := by
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega_using [hj])]
  rfl

theorem high_byte (v : BitVec 128) {j : Nat} (hj : j<4) :
    ((v.extractLsb' 64 64).setWidth 32).extractLsb' (8*j) 8 = vbyte v (8+j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte,BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,hi,decide_true,
    Bool.true_and,show 8*j+i<32 by omega_using [hj, hi],show 8*j+i<64 by omega_using [hj, hi]]
  exact congrArg _ (by omega_using [])


theorem encMask_value : encMask = 0xffffffff0e0d0c0a0908060504020100#128 := by
  apply vbyte_ext
  exact (by decide +kernel : ∀ e<16, vbyte encMask e = vbyte 0xffffffff0e0d0c0a0908060504020100#128 e)

end VG.Proof.MlKem.AArch64.Codec16

end

end

/-!
# ByteEncode₁₂ of a polynomial stored with 16 bits, on AArch64

`Impl.MlKem.AArch64.Codec12W.encW` writes `ByteEncode₁₂(P)` to the 384 bytes
at `x1`, for the polynomial `P` stored with 16 bits at `x0` (`encW_ok`): each
iteration widens eight coefficients to words (`vword_zip_zero`) and packs
them as `Codec16.math_ok` does.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec12W

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Codec16
open VG.Impl.MlKem.AArch64.Codec12W (encBodyW encW)
open VG.Impl.MlKem.AArch64.Codec16 (maskVec)
open VG.Proof.Rc4.AArch64

/-- Code that writes none of `preservedV` keeps their low halves. -/
theorem WP.vcs {c : Prog isa} {s : State} {Q : State → Prop}
    (hc : (instrs c).all (fun i => preservedV.all fun r => vdstOf i != some r) = true)
    (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => ?_⟩
  rw [Exec.vec (r := r) (fun i hi h' => ?_) he]
  have := List.all_eq_true.mp hc i hi
  have := List.all_eq_true.mp this r hr
  simp [h'] at this

/-- Code that writes no lane of `r` keeps it. -/
theorem WP.keepVR {c : Prog isa} {s : State} {Q : State → Prop} {r : VReg}
    (hc : ∀ i ∈ instrs c, vdstOf i ≠ some r) (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.v r = s.v r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.vec hc he⟩

/-- The registers `encW` writes. -/
abbrev encClob : List Reg := [.x0, .x1, .x9, .x10, .x11]

/-- What `encW` needs: the polynomial `P` stored with 16 bits at `p`, readable, and 384 writable
bytes at `o` apart from it. -/
structure EncData (s₀ : State) (p o : Addr) (P : Poly) : Prop where
  poly : PolyIsW 16 s₀.mem p P
  read : ∀ j, j + 16 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 j) 16
  write : ∀ j n, j + n ≤ 384 → InRegions s₀.wr (o + BitVec.ofNat 64 j) n
  apart : (⟨p, 512⟩ : Region).Disjoint ⟨o, 384⟩

/-- After `k` iterations. -/
structure EncInv (s₀ : State) (p o : Addr) (P : Poly) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ encClob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = p + BitVec.ofNat 64 (16 * k)
  x1 : s.gpr .x1 = o + BitVec.ofNat 64 (12 * k)
  count : (s.gpr .x11).toNat = 32 - k
  mask : s.v .v16 = encMask
  zero : s.v .v17 = 0
  out : BytesUpTo s.mem o 384 (12 * k) (fun j => (encode12 P)[j]!) (fun j => s₀.mem (o + BitVec.ofNat 64 j))
  frame : Frame [⟨o, 384⟩] s₀.mem s.mem

/-- Four words of the coefficients `j … j + 3` of `P`, from halfwords widened by `zip1` or
`zip2` with zero. -/
theorem zip_lanes {m : Mem} {p : Addr} {P : Poly} (hp : PolyIsW 16 m p P) {j : Nat} (hj : j + 8 ≤ 256)
    {z : BitVec 128} (hz : z = 0) :
    Lanes (VPermOp.eval .zip1 .h8 (m.read (p + BitVec.ofNat 64 (2 * j)) 16) z) (fun e => (P[j + e]!).val) ∧
    Lanes (VPermOp.eval .zip2 .h8 (m.read (p + BitVec.ofNat 64 (2 * j)) 16) z)
      (fun e => (P[j + (4 + e)]!).val) := by
  have hz' : ∀ e < 8, vhalf z e = 0 := fun e _ => by subst hz; simp [vhalf]
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [(Ntt16.vword_zip_zero hz' he).1, vhalf_read_coeff _ _ _ (by omega_arith), polyIsW16_toNat hp (by omega_arith)]
  · rw [(Ntt16.vword_zip_zero hz' he).2, vhalf_read_coeff _ _ _ (by omega_arith), polyIsW16_toNat hp (by omega_arith)]

theorem enc_step {s₀ : State} {p o : Addr} {P : Poly} (hd : EncData s₀ p o P) {k : Nat} (hk : k < 32)
    {s : State} (h : EncInv s₀ p o P k s) : WP isa (.block encBodyW) s fun t =>
      EncInv s₀ p o P (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 32) := by
  have hpoly : PolyIsW 16 s.mem p P := by
    refine ⟨fun i hi => ?_, Vector.ext fun i hi => ?_⟩
    · have hi' : i < 256 := hi
      rw [coeffAtW, h.frame.readW (r := ⟨p, 512⟩) (contains_off (by omega_arith) (by decide))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.apart) (by decide)]
      exact hd.poly.1 i hi
    · rw [← hd.poly.2]
      simp only [polyAtW, Vector.getElem_ofFn, coeffAtW]
      have hi' : i < 256 := hi
      rw [h.frame.readW (r := ⟨p, 512⟩) (contains_off (by omega_arith) (by decide))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.apart) (by decide)]
  unfold encBodyW
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrq (a := p + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [h.x0, BitVec.add_zero]; congr 2; omega_arith)
    (by rw [h.rd, h.wr]; exact hd.read _ (by omega_arith)) fun s₁ h₁ => ?_
  refine wp_vop (d := .v0) rfl fun s₂ h₂ => wp_vop (d := .v1) rfl fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepVR (r := .v17) (by decide)
    (math_ok s₃ (by rw [h₃.get .v16, h₂.get .v16, h₁.get .v16]; exact h.mask))) ?_
  intro s₄ ⟨⟨x9, x10, m₄, rd₄, wr₄, sp₄, g₄, v₄⟩, v17₄⟩
  have z₁ : s₁.v .v17 = 0 := by rw [h₁.get .v17]; exact h.zero
  have L := zip_lanes (j := 8 * k) hpoly (by omega_arith) z₁
  let v := tbl (packed (s₃.v .v0) (s₃.v .v1)) encMask
  have bytes : ∀ j < 12, vbyte v j = (encode12 P)[12 * k + j]! := by
    intro j hj
    apply enc_spec P hk (j := j) _ _ hj
    · rw [h₃.get .v0, h₂.v, h₁.v]; exact L.1
    · rw [h₃.v, h₂.get .v4, h₂.get .v17, h₁.v]; exact L.2
  have g₃ : s₃.gpr = s.gpr := by rw [h₃.gpr, h₂.gpr, h₁.gpr]
  have g40 : s₄.gpr .x0 = s.gpr .x0 := by rw [g₄ .x0 (by decide) (by decide), g₃]
  have g41 : s₄.gpr .x1 = s.gpr .x1 := by rw [g₄ .x1 (by decide) (by decide), g₃]
  have g411 : s₄.gpr .x11 = s.gpr .x11 := by rw [g₄ .x11 (by decide) (by decide), g₃]
  have mem₄ : s₄.mem = s.mem := by rw [m₄, h₃.mem, h₂.mem, h₁.mem]
  have wrs₄ : s₄.wr = s.wr := by rw [wr₄, h₃.wr, h₂.wr, h₁.wr]
  have scalar : WP isa (.block [.str .x .x9 .x1 0, .str .w .x10 .x1 8,
      .addImm .x .x0 .x0 16, .addImm .x .x1 .x1 12, .subImm .x .x11 .x11 1]) s₄ fun t =>
      (∀ r, r ∉ [Reg.x0, .x1, .x11] → t.gpr r = s₄.gpr r) ∧ t.rd = s₄.rd ∧ t.wr = s₄.wr ∧ t.sp = s₄.sp ∧
      t.gpr .x0 = s₄.gpr .x0 + 16 ∧ t.gpr .x1 = s₄.gpr .x1 + 12 ∧
      (t.gpr .x11).toNat = 32 - (k + 1) ∧
      t.mem = (s₄.mem.write (o + BitVec.ofNat 64 (12 * k)) 8 (v.extractLsb' 0 64)).write
        (o + BitVec.ofNat 64 (12 * k + 8)) 4 ((v.extractLsb' 64 64).setWidth 32) := by
    refine wp_strx (a := o + BitVec.ofNat 64 (12 * k)) (by decide)
      (by rw [g41, h.x1, BitVec.add_zero]) ?_ fun s₅ h₅ => ?_
    · rw [wrs₄, h.wr]; exact hd.write _ _ (by omega_arith)
    refine wp_strw (a := o + BitVec.ofNat 64 (12 * k + 8)) (by decide)
      (by rw [h₅.gpr, g41, h.x1, ptr_add]) ?_ fun s₆ h₆ => ?_
    · rw [h₅.wr, wrs₄, h.wr]; exact hd.write _ _ (by omega_arith)
    refine wp_addImm (by decide) fun s₇ h₇ e₇ => wp_addImm (by decide) fun s₈ h₈ e₈ =>
      wp_subImm (by decide) fun s₉ h₉ e₉ => wp_nil ?_
    refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [h₉.get r (by simpa using hr.2.2), h₈.get r (by simpa using hr.2.1), h₇.get r (by simpa using hr.1),
        h₆.gpr, h₅.gpr]
    · rw [h₉.rd, h₈.rd, h₇.rd, h₆.rd, h₅.rd]
    · rw [h₉.wr, h₈.wr, h₇.wr, h₆.wr, h₅.wr]
    · rw [h₉.sp, h₈.sp, h₇.sp, h₆.sp, h₅.sp]
    · rw [h₉.get .x0, h₈.get .x0, e₇, h₆.gpr, h₅.gpr]; rfl
    · rw [h₉.get .x1, e₈, h₇.get .x1, h₆.gpr, h₅.gpr]; rfl
    · have c : (s₈.gpr .x11).toNat = 32 - k := by
        rw [h₈.get .x11, h₇.get .x11, h₆.gpr, h₅.gpr, g411, h.count]
      rw [e₉, toNat_sub_n (by rw [c]; simp; omega_arith), c]; simp; omega_arith
    · rw [h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₅.gpr, x9, x10]; rfl
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨og, ord, owr, osp, p0, p1, ct, mt⟩, vt⟩
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ct, ?_, ?_, ?_, ?_⟩, by rw [ct]; omega_arith⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [og r (by simp [hr.1, hr.2.1, hr.2.2.2.2]),
      g₄ r hr.2.2.1 hr.2.2.2.1, g₃, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  · rw [ord, rd₄, h₃.rd, h₂.rd, h₁.rd, h.rd]
  · rw [owr, wrs₄, h.wr]
  · rw [osp, sp₄, h₃.sp, h₂.sp, h₁.sp, h.sp]
  · rw [p0, g40, h.x0, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ptr_add]; congr 2
  · rw [p1, g41, h.x1, show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, ptr_add]; congr 2
  · rw [vt, v₄, h₃.get .v16, h₂.get .v16, h₁.get .v16, h.mask]
  · rw [vt, v17₄, h₃.get .v17, h₂.get .v17, z₁]
  · rw [mt, mem₄, show 12 * (k + 1) = 12 * k + 8 + 4 by omega_arith]
    refine bytes_write (bytes_write h.out (by omega_arith) ?_) (by omega_arith) ?_
    · intro j hj; rw [low_byte _ hj]; exact bytes j (by omega_arith)
    · intro j hj; rw [high_byte _ hj]
      simpa only [Nat.add_assoc] using bytes (8 + j) (by omega_arith)
  · rw [mt, mem₄]
    exact (h.frame.write (n := 8) (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by decide))).write
      (n := 4) (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by decide))

theorem enc_init {s : State} {p o : Addr} (P : Poly) (h0 : s.gpr .x0 = p) (h1 : s.gpr .x1 = o) :
    WP isa (.block (maskVec .v16 [0,1,2,4,5,6,8,9,10,12,13,14] ++
      ([.vop (.movi0 .v17), .movz .x .x11 32 0] : List Instr))) s (EncInv s p o P 0) := by
  dsimp [maskVec, VG.Impl.MlKem.AArch64.movImm]
  rrun [RegUpd.sp_write, RegUpd.sp_setV]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setV, RegUpd.gpr_write, hr.2.2.1, hr.2.2.2.2, ite_false]
  · change s.gpr .x0 = p + BitVec.ofNat 64 (16 * 0); rw [h0]; exact (BitVec.add_zero _).symm
  · change s.gpr .x1 = o + BitVec.ofNat 64 (12 * 0); rw [h1]; exact (BitVec.add_zero _).symm
  · rw [encMask_value]; rfl
  · exact BytesUpTo.zero _
  · exact Frame.refl _ _

theorem encW_ok {s : State} {p o : Addr} {P : Poly} (h0 : s.gpr .x0 = p) (h1 : s.gpr .x1 = o)
    (hd : EncData s p o P) :
    WP isa encW s fun s' => Keep encClob s s' ∧ Frame [⟨o, 384⟩] s.mem s'.mem ∧
      Spec.Sha3.bytesAt s'.mem o 384 = encode12 P := by
  refine WP.mono (WP.vcs (by decide +kernel) (WP.seq (WP.mono (enc_init P h0 h1) fun s₁ h₁ =>
    count_loop (by decide) (EncInv s p o P) (fun k hk t ht => enc_step hd hk ht) h₁)))
    fun s' ⟨h', vcs⟩ => ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, vcs⟩, h'.frame,
      (show BytesUpTo s'.mem o 384 384 _ _ from h'.out).eq (encode12_length _) fun _ _ => rfl⟩

end VG.Proof.MlKem.AArch64.Codec12W

end

end

/-!
# Sums of polynomials stored with 16 bits, on AArch64

`accW op` is proven once for any step `op` that computes a function `F` of
two coefficients less than `q` in halfwords (`HOpSpec`): `haddOp` computes
`(a + b) mod q`, and `accW_ok` writes `G f g` to `f` for the `G` whose
coefficients `F` computes (`addW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.AddSubW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.AddSubW
open VG.Proof.MlKem.AArch64.Codec12W (WP.vcs)
open VG.Proof.MlKem.AArch64.DotW (HLanes hlanes_coeffs)

section
variable {rest : List Instr} {Q : State → Prop}

theorem hlanes_map2 {s : State} {f : (w : Nat) → BitVec w → BitVec w → BitVec w} {n m : VReg}
    {A B C : Nat → Nat} (hn : HLanes (s.v n) A) (hm : HLanes (s.v m) B)
    (hf : ∀ e < 8, (f 16 (BitVec.ofNat 16 (A e)) (BitVec.ofNat 16 (B e))).toNat = C e) :
    HLanes (VArr.h8.map2 f (s.v n) (s.v m)) C := fun e he => by
  have a : vhalf (s.v n) e = BitVec.ofNat 16 (A e) := by
    apply BitVec.eq_of_toNat_eq; rw [hn e he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hn e he ▸ (vhalf _ e).isLt)]
  have b : vhalf (s.v m) e = BitVec.ofNat 16 (B e) := by
    apply BitVec.eq_of_toNat_eq; rw [hm e he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hm e he ▸ (vhalf _ e).isLt)]
  rw [Ntt16.vhalf_map2 _ _ _ he, a, b, hf e he]

/-- `hcsub`: `x mod q` of halfwords `x < 2q`. -/
theorem hcsub_ok {s : State} (hq : HLanes (s.v .v16) fun _ => 3329) {X : Nat → Nat}
    (hx : HLanes (s.v .v2) X) (hb : ∀ e < 8, X e < 2 * 3329)
    (k : ∀ s', VChg [.v3, .v2] s s' → HLanes (s'.v .v2) (fun e => X e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (hcsub ++ rest)) s Q := by
  simp only [hcsub, List.cons_append, List.nil_append]
  refine wp_vop (d := .v3) rfl fun s₁ h₁ => wp_vop (d := .v3) rfl fun s₂ h₂ =>
    wp_vop (d := .v2) rfl fun s₃ h₃ => k s₃ ((h₁.chg.trans h₂.chg).trans h₃.chg |>.mono) ?_
  intro e he
  have b := hb e he
  rw [h₃.v, Ntt16.vhalf_map2 _ _ _ he, h₂.v, h₂.get .v2, h₁.get .v2]
  dsimp only
  have va : ∀ x y : BitVec 128, vhalf (x &&& y) e = vhalf x e &&& vhalf y e := fun x y => by
    simp only [vhalf, BitVec.extractLsb'_and]
  rw [va,
    h₁.get .v16, h₁.v, Ntt16.vhalf_map2 _ _ _ he]
  have hx' := hx e he
  have hq' := hq e he
  split
  · rename_i c
    simp only [VCmpOp.test, hx', hq', decide_eq_true_eq] at c
    simp only [BitVec.allOnes_and, BitVec.toNat_sub, hx', hq']
    omega_arith
  · rename_i c
    simp only [VCmpOp.test, hx', hq', decide_eq_true_eq] at c
    have z : (0 : BitVec 16) &&& vhalf (s.v .v16) e = 0 := by ext; simp
    rw [z, BitVec.toNat_sub, hx']; simp
    omega_arith

/-- `op` computes `F a b` in the halfwords of `v2` from those of `v0 = a` and `v1 = b`, with `q`
in the halfwords of `v16`, changing only `v2` and `v3`. -/
def HOpSpec (op : List Instr) (F : Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (Q : State → Prop) (A B : Nat → Nat), (∀ e < 8, A e < 3329) →
    (∀ e < 8, B e < 3329) → HLanes (s.v .v0) A → HLanes (s.v .v1) B → HLanes (s.v .v16) (fun _ => 3329) →
    (∀ s', VChg [.v2, .v3] s s' → HLanes (s'.v .v2) (fun e => F (A e) (B e)) → WP isa (.block is) s' Q) →
    WP isa (.block (op ++ is)) s Q

theorem haddOp_spec : HOpSpec haddOp fun a b => (a + b) % 3329 := by
  intro is s Q A B hA hB lA lB hq k
  simp only [haddOp, List.cons_append]
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => ?_
  have l₁ : HLanes (s₁.v .v2) fun e => A e + B e := by
    rw [h₁.v]
    refine hlanes_map2 lA lB fun e he => ?_
    have := hA e he; have := hB e he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  refine hcsub_ok (by rw [h₁.get .v16]; exact hq) l₁ (fun e he => by have := hA e he; have := hB e he; omega_arith)
    fun s₂ h₂ l₂ => k s₂ ((h₁.chg.trans h₂).mono) l₂

end

/-! ## The loop -/

/-- What `accW` needs of the state `s₀` it starts in: the reduced polynomials at `x0`, which
it can write, and at `x1`, apart. -/
structure AccData (s₀ : State) : Prop where
  rf : ∀ j, j + 16 ≤ 512 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 j) 16
  rg : ∀ j, j + 16 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 j) 16
  apart : (⟨s₀.gpr .x0, 512⟩ : Region).Disjoint ⟨s₀.gpr .x1, 512⟩
  f : ReducedW 16 s₀.mem (s₀.gpr .x0)
  g : ReducedW 16 s₀.mem (s₀.gpr .x1)

/-- The registers `accW` writes. -/
abbrev accClob : List Reg := [.x0, .x1, .x9, .x11]

/-- Coefficient `i` of the result. -/
def newW (F : Nat → Nat → Nat) (s₀ : State) (i : Nat) : BitVec 16 :=
  BitVec.ofNat 16 (F (coeffAtW 16 s₀.mem (s₀.gpr .x0) i).toNat (coeffAtW 16 s₀.mem (s₀.gpr .x1) i).toNat)

/-- After `k` iterations. -/
structure AccInv (F : Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ accClob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (16 * k)
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (16 * k)
  count : (s.gpr .x11).toNat = 32 - k
  q : HLanes (s.v .v16) fun _ => 3329
  out : CoeffsInW s.mem (s₀.gpr .x0) (· < 8 * k) (newW F s₀) fun i => coeffAtW 16 s₀.mem (s₀.gpr .x0) i
  frame : Frame [⟨s₀.gpr .x0, 512⟩] s₀.mem s.mem

theorem acc_step {op : List Instr} {F : Nat → Nat → Nat} (hop : HOpSpec op F)
    (hF : ∀ a < 3329, ∀ b < 3329, F a b < 2 ^ 16) {s₀ : State} (hd : AccData s₀) {k : Nat} (hk : k < 32)
    {s : State} (h : AccInv F s₀ k s) :
    WP isa (.block (accBodyW op)) s fun s' => AccInv F s₀ (k + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 32) := by
  simp only [accBodyW, List.cons_append, List.nil_append]
  refine wp_ldrq (a := s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [h.x0, BitVec.add_zero]; congr 2; omega_arith)
    (by rw [h.rd, h.wr]; exact in_rd_wr (hd.rf _ (by omega_arith))) fun s₁ h₁ => ?_
  refine wp_ldrq (a := s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [h₁.gpr, h.x1, BitVec.add_zero]; congr 2; omega_arith)
    (by rw [h₁.rd, h₁.wr, h.rd, h.wr]; exact hd.rg _ (by omega_arith)) fun s₂ h₂ => ?_
  have cf : ∀ e < 8, (coeffAtW 16 s.mem (s₀.gpr .x0) (8 * k + e)) = coeffAtW 16 s₀.mem (s₀.gpr .x0) (8 * k + e) :=
    fun e he => by rw [h.out _ (by omega_arith), ite_eq_right (by omega_arith)]
  have cg : ∀ e < 8, (coeffAtW 16 s.mem (s₀.gpr .x1) (8 * k + e)) = coeffAtW 16 s₀.mem (s₀.gpr .x1) (8 * k + e) :=
    fun e he => h.frame.readW (r := ⟨s₀.gpr .x1, 512⟩) (contains_off (by omega_arith) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.apart.symm) (by decide)
  have lA : HLanes (s₂.v .v0) fun e => (coeffAtW 16 s₀.mem (s₀.gpr .x0) (8 * k + e)).toNat := by
    rw [h₂.get .v0, h₁.v]; exact hlanes_coeffs _ _ _ fun e he => by rw [cf e he]
  have lB : HLanes (s₂.v .v1) fun e => (coeffAtW 16 s₀.mem (s₀.gpr .x1) (8 * k + e)).toNat := by
    rw [h₂.v, h₁.mem]; exact hlanes_coeffs _ _ _ fun e he => by rw [cg e he]
  refine hop _ s₂ _ _ _ (fun e _ => hd.f _ (by show _ < 256; omega_arith)) (fun e _ => hd.g _ (by show _ < 256; omega_arith))
    lA lB (by rw [h₂.get .v16, h₁.get .v16]; exact h.q) fun s₃ h₃ l₃ => ?_
  have g₃ : s₃.gpr = s.gpr := by rw [h₃.gpr, h₂.gpr, h₁.gpr]
  refine wp_strq (a := s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [g₃, h.x0, BitVec.add_zero]; congr 2; omega_arith)
    (by rw [h₃.wr, h₂.wr, h₁.wr, h.wr]; exact hd.rf _ (by omega_arith)) fun s₄ h₄ => ?_
  refine WP.mono (WP.keepV (Q := fun w' => Only [.x0, .x1, .x11] s₄ w' ∧
      w'.gpr .x0 = s₄.gpr .x0 + BitVec.ofNat 64 16 ∧ w'.gpr .x1 = s₄.gpr .x1 + BitVec.ofNat 64 16 ∧
      w'.gpr .x11 = s₄.gpr .x11 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun s₅ h₅ e₅ => wp_addImm (by decide) fun s₆ h₆ e₆ =>
      wp_subImm (by decide) fun s₇ h₇ e₇ => wp_nil ⟨((h₅.trans h₆).trans h₇).mono,
        by rw [h₇.get .x0, h₆.get .x0, e₅], by rw [h₇.get .x1, e₆, h₅.get .x1],
        by rw [e₇, h₆.get .x11, h₅.get .x11]⟩))
    fun s' ⟨⟨k', e0, e1, e11⟩, hv⟩ => ?_
  have g₄ : s₄.gpr = s.gpr := by rw [h₄.gpr, g₃]
  have c11 : (s₄.gpr .x11).toNat = 32 - k := by rw [g₄, h.count]
  have v11 : (s'.gpr .x11).toNat = 32 - (k + 1) := by
    rw [e11, toNat_sub_n (by rw [c11]; simp; omega_arith), c11]; simp; omega_arith
  have mm : s'.mem = s.mem.write (s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) 16 (s₃.v .v2) := by
    rw [k'.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, v11, ?_, ?_, ?_⟩, by rw [v11]; omega_arith⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k'.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2]), g₄, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  · rw [k'.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, h.rd]
  · rw [k'.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, h.wr]
  · rw [k'.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp, h.sp]
  · rw [e0, g₄, h.x0, ptr_add]; congr 2
  · rw [e1, g₄, h.x1, ptr_add]; congr 2
  · rw [hv, h₄.v, h₃.v .v16 (by decide), h₂.get .v16, h₁.get .v16]; exact h.q
  · rw [mm]
    refine h.out.write16 (by omega_arith) (fun e he => BitVec.eq_of_toNat_eq ?_) (fun i _ => by omega_arith)
    rw [l₃ e he, newW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hF _ (hd.f _ (by show _ < 256; omega_arith)) _
      (hd.g _ (by show _ < 256; omega_arith)))]
  · rw [mm]; exact h.frame.write (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by decide))

theorem acc_init (F : Nat → Nat → Nat) (s : State) :
    WP isa (.block [.movz .x .x9 3329 0, .vop (.dup .h8 .v16 .x9), .movz .x .x11 32 0]) s (AccInv F s 0) := by
  show WP isa (.block ([Instr.movz .x .x9 3329 0] ++ (.vop (.dup .h8 .v16 .x9) ::
    (([.movz .x .x11 32 0] : List Instr) ++ [])))) s _
  refine wp_scalar (by decide) (P := fun s₁ => Only [.x9] s s₁ ∧ (s₁.gpr .x9).toNat = 3329)
    (wp_movz fun s₁ h₁ e₁ => wp_nil ⟨h₁, by rw [e₁]; rfl⟩) fun s₁ ⟨k₁, e9⟩ _ => ?_
  refine wp_vop (d := .v16) rfl fun s₂ h₂ => ?_
  refine wp_scalar (by decide) (P := fun s₃ => Only [.x11] s₂ s₃ ∧ (s₃.gpr .x11).toNat = 32)
    (wp_movz fun s₃ h₃ e₃ => wp_nil ⟨h₃, by rw [e₃]; rfl⟩) fun s₃ ⟨k₃, e11⟩ hv₃ => wp_nil ?_
  have m : s₃.mem = s.mem := by rw [k₃.mem, h₂.mem, k₁.mem]
  have k₃ := (k₁.keep.trans h₂.keep).trans k₃.keep
  refine ⟨fun r hr => k₃.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, List.append_nil, List.cons_append,
      List.nil_append] at hr ⊢
    exact ⟨hr.2.2.1, hr.2.2.2⟩), k₃.rd, k₃.wr, k₃.sp,
    by rw [k₃.get .x0]; exact (BitVec.add_zero _).symm, by rw [k₃.get .x1]; exact (BitVec.add_zero _).symm,
    e11, fun e he => ?_, fun i _ => by rw [m, ite_eq_right (by omega_arith)], by rw [m]; exact Frame.refl _ _⟩
  rw [hv₃, h₂.v, Ntt16.vhalf_ofVHalves _ he]
  simp only [BitVec.toNat_setWidth, e9]

theorem accW_ok {op : List Instr} {F : Nat → Nat → Nat} (hop : HOpSpec op F)
    (hF : ∀ a < 3329, ∀ b < 3329, F a b < 3329) {G : Poly → Poly → Poly}
    (hG : ∀ P R : Poly, ∀ i < 256, ((G P R)[i]!).val = F (P[i]!).val (R[i]!).val)
    (hv : (instrs (accW op)).all (fun i => preservedV.all fun r => vdstOf i != some r) = true)
    {s : State} (hd : AccData s) :
    WP isa (accW op) s fun s' => Keep accClob s s' ∧ Frame [⟨s.gpr .x0, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr .x0) (G (polyAtW 16 s.mem (s.gpr .x0)) (polyAtW 16 s.mem (s.gpr .x1))) := by
  refine WP.mono (WP.vcs hv (WP.seq (WP.mono (acc_init F s) fun s₁ h₁ =>
    count_loop (by decide) (AccInv F s) (fun k hk t ht => acc_step hop (fun a ha b hb => by
      have := hF a ha b hb; omega_arith) hd hk ht) h₁)))
    fun s' ⟨h', vcs⟩ => ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, vcs⟩, h'.frame,
      h'.out.polyIs (fun i hi => by omega_arith) fun i hi => ?_⟩
  · have hl : i < 256 := hi
    rw [newW, BitVec.toNat_ofNat, hG _ _ i hl, Nat.mod_eq_of_lt (by have := hF _ (hd.f i hl) _ (hd.g i hl); omega_arith)]
    simp only [polyAtW]
    rw [getElem!_eq _ hl, getElem!_eq _ hl, Vector.getElem_ofFn, Vector.getElem_ofFn, val_ofNat, val_ofNat,
      Nat.mod_eq_of_lt (hd.f i hl), Nat.mod_eq_of_lt (hd.g i hl)]

theorem addW_ok {s : State} (hd : AccData s) :
    WP isa addW s fun s' => Keep accClob s s' ∧ Frame [⟨s.gpr .x0, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr .x0) (add (polyAtW 16 s.mem (s.gpr .x0)) (polyAtW 16 s.mem (s.gpr .x1))) :=
  accW_ok haddOp_spec (fun a _ b _ => Nat.mod_lt _ (by decide))
    (fun P R i hi => by
      have : (P[i]!).val < 3329 := Fin.isLt _
      have : (R[i]!).val < 3329 := Fin.isLt _
      have hq : q = 3329 := rfl
      rw [add_get _ _ hi, val_add, condSub]; split <;> omega_arith) (by decide +kernel) hd

end VG.Proof.MlKem.AArch64.AddSubW

end

end

/-! # Fused accumulators compute the existing K-PKE dot product -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.Spec.MlKem VG.Proof.MlKem

theorem polySum_dotK (offsets : Nat → Nat × Nat) (F G : (Nat × Nat) → Poly)
    (a b : Nat → Poly) {k : Nat}
    (hf : ∀ j<k, F (offsets j)=a j) (hg : ∀ j<k, G (offsets j)=b j) :
    Dot.polySum ((List.range k).map offsets) F G = KPke.dotK a b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hrec := ih (fun j hj => hf j (by omega_using [hj])) (fun j hj => hg j (by omega_using [hj]))
    unfold Dot.polySum at *
    rw [List.range_succ,List.map_append,List.foldl_append,List.map_cons,List.map_nil,
      List.foldl_cons,List.foldl_nil,hrec,hf k (by omega_using []),hg k (by omega_using [])]
    exact (KPke.foldK_succ zero_add_poly (fun j => multiplyNTTs (a j) (b j)) k).symm

end VG.Proof.MlKem.AArch64.Optimized
