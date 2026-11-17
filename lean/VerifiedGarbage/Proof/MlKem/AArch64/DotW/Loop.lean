module

import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.Sha3.AArch64.Callers.Sums
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopState
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Lane
public import VerifiedGarbage.Impl.MlKem.AArch64.DotW
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec

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
