module

public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Impl.X448.AArch64.Field56
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Impl.Ed448.AArch64.Point56
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-! ### `Ed448.AArch64.Window.Dbl`, which the modules that import this one used -/

section

/-!
# Ed448 verification on AArch64: doubling with the register-resident arithmetic

Untrusted: everything here is checked by Lean. `dblOps x y z`
(`Impl/Ed448/AArch64/VerifyWindow.lean`) on the slots of a point with every
slot's limbs below `Ib` and `Z`'s below `Mb` (`dblOps_ok`): the environment
afterwards is `dblEnv` of the one before, which for the point's slots is
`double` of the point when slot 20 holds 1 (`dblPt_eq`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.X448.AArch64.Fast (ops codeOf)
open VG.Proof.X448.AArch64.Base (mulS subS addSubS pt temps)
open VG.Spec.Ed448 (Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The environment after `dblOps x y z`. -/
def dblEnv (x y z : Index) (e : Env) : Env :=
  mulS z 13 17 <| mulS x 16 17 <| mulS y 13 14 <| subS 17 15 18 <| addSubS 16 17 10 10 <|
  mulS 15 13 20 <| addSubS 13 14 11 12 <| mulS 18 z 16 <| mulS 12 y y <| mulS 11 x x <|
  mulS 10 x y <| addSubS 16 17 z z e

theorem dblOps_eq (x y z : Index) :
    Impl.Ed448.AArch64.dblOps (slot x.val) (slot y.val) (slot z.val) =
    [.addSub (slot (16 : Index).val) (slot (17 : Index).val) (slot z.val) (slot z.val),
     .mul (slot (10 : Index).val) (slot x.val) (slot y.val),
     .mul (slot (11 : Index).val) (slot x.val) (slot x.val),
     .mul (slot (12 : Index).val) (slot y.val) (slot y.val),
     .mul (slot (18 : Index).val) (slot z.val) (slot (16 : Index).val),
     .addSub (slot (13 : Index).val) (slot (14 : Index).val) (slot (11 : Index).val) (slot (12 : Index).val),
     .mul (slot (15 : Index).val) (slot (13 : Index).val) (slot (20 : Index).val),
     .addSub (slot (16 : Index).val) (slot (17 : Index).val) (slot (10 : Index).val) (slot (10 : Index).val),
     .sub (slot (17 : Index).val) (slot (15 : Index).val) (slot (18 : Index).val),
     .mul (slot y.val) (slot (13 : Index).val) (slot (14 : Index).val),
     .mul (slot x.val) (slot (16 : Index).val) (slot (17 : Index).val),
     .mul (slot z.val) (slot (13 : Index).val) (slot (17 : Index).val)] := rfl

section
variable {s : State} {base : Addr}

/-- **Doubling** the point in slots `x`, `y`, `z` (all below slot 10, `Z`'s limbs below `Mb`),
with the temporaries in slots 10–18 and 1 in slot 20. -/
theorem dblOps_ok (x y z : Index) (hx : x.val < 10) (hy : y.val < 10) (hz : z.val < 10)
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) (hs : Scr s base) (hb : BEnv s.mem base)
    (hzb : Bnd Mb s.mem base (slot z.val)) :
    WP isa (ops (Impl.Ed448.AArch64.dblOps (slot x.val) (slot y.val) (slot z.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base (temps ++ [x, y, z]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot x.val) ∧ Bnd Mb t.mem base (slot y.val) ∧ Bnd Mb t.mem base (slot z.val) ∧
      EV t.mem base = dblEnv x y z (EV s.mem base) := by
  have n : ∀ {i : Index}, i.val < 10 → ∀ k : Index, 10 ≤ k.val → k ≠ i := fun hi k hk h => by
    rw [h] at hk; omega_using [hi, hk]
  have nn' : ∀ {i j : Index}, i ≠ j → i ∉ [j] := fun h hm => h (List.mem_singleton.mp hm)
  rw [dblOps_eq]
  refine addSubOp (o₁ := 16) (o₂ := 17) (a := z) (b := z) hs hb hzb hzb (by decide)
    (n hz 16 (by decide)) (n hz 16 (by decide)) (n hz 17 (by decide)) (n hz 17 (by decide))
    fun t1 k1 b1 s1 e1 => ?_
  have hs1 := k1.scr hs
  refine mulOp hs1 b1 10 x y (Or.inr (n hy 10 (by decide))) fun t2 k2 b2 m10 s2 e2 => ?_
  have hs2 := k2.scr hs1
  refine mulOp hs2 b2 11 x x (Or.inl rfl) fun t3 k3 b3 m11 s3 e3 => ?_
  have hs3 := k3.scr hs2
  refine mulOp hs3 b3 12 y y (Or.inl rfl) fun t4 k4 b4 m12 s4 e4 => ?_
  have hs4 := k4.scr hs3
  refine mulOp hs4 b4 18 z 16 (Or.inr (by decide)) fun t5 k5 b5 m18 s5 e5 => ?_
  have hs5 := k5.scr hs4
  refine addSubOp (o₁ := 13) (o₂ := 14) (a := 11) (b := 12) hs5 b5
    (s5.bnd (by decide) (s4.bnd (by decide) m11)) (s5.bnd (by decide) m12)
    (by decide) (by decide) (by decide) (by decide) (by decide) fun t6 k6 b6 s6 e6 => ?_
  have hs6 := k6.scr hs5
  refine mulOp hs6 b6 15 13 20 (Or.inr (by decide)) fun t7 k7 b7 m15 s7 e7 => ?_
  have hs7 := k7.scr hs6
  have m10' : Bnd Mb t7.mem base (slot (10 : Index).val) :=
    s7.bnd (by decide) (s6.bnd (by decide) (s5.bnd (by decide) (s4.bnd (by decide) (s3.bnd (by decide) m10))))
  refine addSubOp (o₁ := 16) (o₂ := 17) (a := 10) (b := 10) hs7 b7 m10' m10'
    (by decide) (by decide) (by decide) (by decide) (by decide) fun t8 k8 b8 s8 e8 => ?_
  have hs8 := k8.scr hs7
  refine subOp (o := 17) (a := 15) (b := 18) hs8 b8 (s8.bnd (by decide) m15)
    (s8.bnd (by decide) (s7.bnd (by decide) (s6.bnd (by decide) m18))) (by decide) (by decide)
    fun t9 k9 b9 s9 e9 => ?_
  have hs9 := k9.scr hs8
  refine mulOp hs9 b9 y 13 14 (Or.inr (n hy 14 (by decide)).symm) fun t10 k10 b10 my s10 e10 => ?_
  have hs10 := k10.scr hs9
  refine mulOp hs10 b10 x 16 17 (Or.inr (n hx 17 (by decide)).symm) fun t11 k11 b11 mx s11 e11 => ?_
  have hs11 := k11.scr hs10
  refine mulOp hs11 b11 z 13 17 (Or.inr (n hz 17 (by decide)).symm) fun t12 k12 b12 mz s12 e12 => ?_
  refine WP.block_nil ⟨k1.trans (k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans (k8.trans
    (k9.trans (k10.trans (k11.trans k12)))))))))), b12, ?_, ?_, ?_, mz, ?_⟩
  · refine VG.Proof.X448.AArch64.Base.Same.mono
      (s1.append (s2.append (s3.append (s4.append (s5.append (s6.append (s7.append (s8.append (s9.append
        (s10.append (s11.append s12)))))))))))
      fun i hi => ?_
    simp only [temps, List.cons_append, List.nil_append] at hi ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp
  · exact s12.bnd (nn' hzx.symm) mx
  · exact s12.bnd (nn' hzy.symm) (s11.bnd (nn' hxy.symm) my)
  · exact e12.trans <| congrArg (mulS z 13 17) <| e11.trans <| congrArg (mulS x 16 17) <| e10.trans <|
      congrArg (mulS y 13 14) <| e9.trans <| congrArg (subS 17 15 18) <| e8.trans <|
      congrArg (addSubS 16 17 10 10) <| e7.trans <| congrArg (mulS 15 13 20) <| e6.trans <|
      congrArg (addSubS 13 14 11 12) <| e5.trans <| congrArg (mulS 18 z 16) <| e4.trans <|
      congrArg (mulS 12 y y) <| e3.trans <| congrArg (mulS 11 x x) <| e2.trans <|
      congrArg (mulS 10 x y) <| e1

end

/-- What `dblOps` computes from `(X : Y : Z)`, with `one` in slot 20. -/
def dblPt (p : Point) (one : Spec.X448.Fe) : Point :=
  let c := p.X * p.X
  let dd := p.Y * p.Y
  let e := c + dd
  let j := e * one - p.Z * (p.Z + p.Z)
  let pp := p.X * p.Y
  ⟨(pp + pp) * j, e * (c - dd), e * j⟩

theorem dblEnv_345 (e : Env) : pt (dblEnv 3 4 5 e) 3 4 5 = dblPt (pt e 3 4 5) (e 20) := rfl
theorem dblPt_eq (p : Point) : dblPt p 1 = VG.Proof.Ed448.double p := by
  simp only [dblPt, VG.Proof.Ed448.double]
  congr 1 <;> refine Ed448.toZ_inj.1 ?_ <;>
    simp only [Ed448.toZ_add, Ed448.toZ_sub, Ed448.toZ_mul, Ed448.toZ_one] <;> ring

end VG.Proof.Ed448.AArch64.Window

end

end

/-!
# Ed448 on AArch64: field code as a function

Untrusted: everything here is checked by Lean. `asFn_ok`: code that writes no
lane where `asFn` keeps the callee-saved registers (`keptRegs`), run as a
function, starts from `ws` in `x3` and the mask in `x12`, and ends with every
register it keeps (outside `rs`) or that `asFn` keeps restored. The lanes are
set by `insOf_ok`, kept by the code (`Exec.vec`), and read back by `umovOf_ok`
(`Proof/Framework/AArch64/LaneSave.lean`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64

/-- `x3 := x0` (the working space) and `x12 := 2²⁸ - 1`. -/
theorem regs_ok (s : State) :
    WP isa (.block ([.addImm .x .x3 .x0 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] : List Instr)) s
      fun t => t.gpr .x3 = s.gpr .x0 ∧ t.gpr .x12 = 0x0fffffff ∧
        (∀ r, r ≠ .x3 → r ≠ .x12 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.v = s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, by decide, fun r h3 h12 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [h3, h12, ite_false]

theorem keptRegs_lanes (c : Bool) : ∀ k ∈ keptRegs c, k.2.2 < 2 := by cases c <;> decide

theorem keptRegs_nodup_lanes (c : Bool) : ((keptRegs c).map fun k => (k.2.1, k.2.2)).Nodup := by
  cases c <;> decide

theorem keptRegs_nodup (c : Bool) : ((keptRegs c).map Prod.fst).Nodup := by cases c <;> decide

/-- `body` as a function: from `s`, `body` runs with `ws` (from `x0`) in `x3`, the mask in
`x12` and every other register as in `s`; if it changes no register outside `rs` (which holds
neither `x3` nor `x12`) and no lane `asFn` keeps registers in, and ends in memory satisfying `Q`,
then so does `asFn c body`, which keeps every register outside `rs`, or kept, but `x3` and
`x12`, and leaves `ws` in `x3` and the mask in `x12`. -/
theorem asFn_ok {c : Bool} {body : Prog isa} {rs : List Reg} {s : State} {Q : Mem → Prop}
    (h3 : .x3 ∉ rs) (h12 : .x12 ∉ rs)
    (hv : body.allInstrs (fun i => (keptRegs c).all fun k => vdstOf i != some k.2.1) = true)
    (hbody : ∀ s₁ : State, s₁.gpr .x3 = s.gpr .x0 → s₁.gpr .x12 = 0x0fffffff →
      (∀ r, r ≠ .x3 → r ≠ .x12 → s₁.gpr r = s.gpr r) → s₁.mem = s.mem → s₁.rd = s.rd →
      s₁.wr = s.wr → WP isa body s₁ fun t =>
        (∀ r, r ∉ rs → t.gpr r = s₁.gpr r) ∧ t.rd = s₁.rd ∧ t.wr = s₁.wr ∧ Q t.mem) :
    WP isa (asFn c body) s fun u =>
      (∀ r, (r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst) → r ≠ .x3 → r ≠ .x12 → u.gpr r = s.gpr r) ∧
      u.gpr .x3 = s.gpr .x0 ∧ u.gpr .x12 = 0x0fffffff ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Q u.mem := by
  unfold asFn
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (regs_ok s) fun s₀ ⟨g3, g12, gk, gm, gr, gw, gsp, gv⟩ => ?_
  refine WP.mono (insOf_ok (keptRegs c) s₀ (keptRegs_lanes c) (keptRegs_nodup_lanes c))
    fun s₁ ⟨hg, hm, hr, hw, hsp, hls, _⟩ => ?_
  rw [WP.seq_iff]
  obtain ⟨tb, t, he, hk, htr, htw, hq⟩ := hbody s₁ (by rw [hg, g3]) (by rw [hg, g12])
    (fun r h3' h12' => by rw [hg, gk r h3' h12']) (hm.trans gm) (hr.trans gr) (hw.trans gw)
  refine ⟨tb, t, he, ?_⟩
  have tl : ∀ k ∈ keptRegs c, laneOf t k.2.1 k.2.2 = s.gpr k.1 := fun k hk' => by
    have hk3 : ∀ k ∈ keptRegs c, k.1 ≠ .x3 ∧ k.1 ≠ .x12 := by cases c <;> decide
    have hv' : ∀ i ∈ instrs body, vdstOf i ≠ some k.2.1 := fun i hi => by
      rw [Code.allInstrs_eq] at hv
      have := List.all_eq_true.mp (List.all_eq_true.mp hv i hi) k hk'
      simpa using this
    rw [laneOf, Exec.vec hv' he, ← laneOf, hls k hk', gk _ (hk3 k hk').1 (hk3 k hk').2]
  refine WP.mono (umovOf_ok (keptRegs c) t (keptRegs_lanes c) (keptRegs_nodup c))
    fun u ⟨um, ur, uw, usp, uls, uoth⟩ => ?_
  have kept3 : .x3 ∉ (keptRegs c).map Prod.fst := by cases c <;> decide
  have kept12 : .x12 ∉ (keptRegs c).map Prod.fst := by cases c <;> decide
  have t3 : t.gpr .x3 = s₁.gpr .x3 := hk _ h3
  have t12 : t.gpr .x12 = s₁.gpr .x12 := hk _ h12
  refine ⟨fun r hr' h3' h12' => ?_, by rw [uoth _ kept3, t3, hg, g3], by rw [uoth _ kept12, t12, hg, g12],
    by rw [ur, htr, hr, gr], by rw [uw, htw, hw, gw], by rw [usp, Exec.sp he, hsp, gsp], by rw [um]; exact hq⟩
  by_cases hm' : r ∈ (keptRegs c).map Prod.fst
  · obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hm'
    rw [uls k hk', tl k hk']
  · rw [uoth r hm', hk r (hr'.resolve_right hm'), hg, gk r h3' h12']

end VG.Proof.Ed448.AArch64.Point56
