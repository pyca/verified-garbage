import VerifiedGarbage.Proof.Ed448.Arm.BaseStep
import VerifiedGarbage.Proof.X448.Arm.Square
import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation

/-!
# Ed448 verification's equation on ARMv7: field programs

The field programs of `vg_ed448_verify_equation` (`Impl/Ed448/Arm/
VerifyEquation.lean`) as X448's slot operations (`FieldOp`), evaluated on the
slots: the doubling and the addition at the slots they are used with (RFC 8032
§5.2.4's formulas, as for base-point multiplication), and the steps of
decoding. `VKeep` is what the checks and decoding may change: the field
operations' registers, the counter `r11` and `BAD` (`r10`), and the working
space from `SIGN` to the slots' end and from X448's `ACC`.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Impl.X448.Arm (slot X2 ACC)

/-! ## The frame -/

structure VKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.r10 :: .r11 :: workRegs) s t
  mem : Outside2 base 32 2848 ACC 512 s.mem t.mem

theorem VKeep.trans {base : Addr} {s t u : State} (h : VKeep base s t) (h' : VKeep base t u) :
    VKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem VKeep.scr {base : Addr} {s t : State} (h : VKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem Outside2.widen {base : Addr} {m m' : Mem} (h : Outside2 base 64 2816 ACC 512 m m') :
    Outside2 base 32 2848 ACC 512 m m' :=
  fun p h1 h2 => h p (by rcases h1 with h1 | h1 <;> [exact Or.inl (by omega); exact Or.inr (by omega)]) h2

theorem IKeep.toV {base : Addr} {s t : State} (h : IKeep base s t) : VKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), Outside2.widen h.mem⟩

theorem Keep.toV {base : Addr} {s t : State} (h : Keep base s t) : VKeep base s t := IKeep.toV h.ikeep

/-- What the comparisons may change: `VKeep`'s registers, and the slots and `ACC`. -/
structure CKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.r10 :: .r11 :: workRegs) s t
  mem : Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem CKeep.toV {base : Addr} {s t : State} (h : CKeep base s t) : VKeep base s t :=
  ⟨h.regs, Outside2.widen h.mem⟩

theorem CKeep.scr {base : Addr} {s t : State} (h : CKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem CKeep.trans {base : Addr} {s t u : State} (h : CKeep base s t) (h' : CKeep base t u) :
    CKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem IKeep.toC {base : Addr} {s t : State} (h : IKeep base s t) : CKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), h.mem⟩

theorem Keep.toC {base : Addr} {s t : State} (h : Keep base s t) : CKeep base s t := IKeep.toC h.ikeep

/-! ## Operations and where they write -/

def fdest : FieldOp → Index
  | .mul o _ _ | .add o _ _ | .sub o _ _ | .mulSmall o _ | .copy o _ => o

theorem fop_apply_keep (op : FieldOp) (e : Env) {i : Index} (h : fdest op ≠ i) :
    op.apply e i = e i := by
  cases op <;> exact Function.update_of_ne (Ne.symm h) _ _

theorem applyOps_keep (xs : List FieldOp) (e : Env) {i : Index} (h : i ∉ xs.map fdest) :
    applyOps xs e i = e i := by
  induction xs generalizing e with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [applyOps, ih _ h.2, fop_apply_keep _ _ (Ne.symm h.1)]

theorem applyOps_append (a b : List FieldOp) (e : Env) :
    applyOps (a ++ b) e = applyOps b (applyOps a e) := by
  induction a generalizing e with
  | nil => rfl
  | cons op rest ih => exact ih _

/-! ## The programs -/

def doubleF (x y z : Index) : List FieldOp := [
  .add 12 x y, .mul 12 12 12, .mul 13 x x, .mul 14 y y, .add 15 13 14, .mul 16 z z,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul x 18 17, .sub 19 13 14, .mul y 15 19,
  .mul z 15 17]

def addF (x y : Index) : List FieldOp := [
  .mul 12 2 10, .mul 13 12 12, .mul 14 0 x, .mul 15 21 y, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 21, .add 20 x y, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

def decodeUVF (yo xo : Index) : List FieldOp :=
  [.mul 12 yo yo, .sub 13 12 10, .mul 3 11 12, .sub 3 3 10, .mul 4 13 3, .mul 4 4 4,
    .mul 5 13 13, .mul 5 5 13, .mul xo 5 3, .mul 12 xo 4]

def decodeXF (xo : Index) : List FieldOp := [.mul xo xo 1, .mul 12 xo xo, .mul 12 3 12]

def negXF (xo : Index) : List FieldOp := [.sub 12 xo xo, .sub 12 12 xo]

theorem doubleF_impl (x y z : Index) :
    (doubleF x y z).map FieldOp.impl = doubleAt x.val y.val z.val := rfl
theorem addF_impl (x y : Index) : (addF x y).map FieldOp.impl = addAt x.val y.val := rfl
theorem decodeUVF_impl (yo xo : Index) :
    (decodeUVF yo xo).map FieldOp.impl = decodeUV yo.val xo.val := rfl
theorem decodeXF_impl (xo : Index) : (decodeXF xo).map FieldOp.impl = decodeX xo.val := rfl
theorem negXF_impl (xo : Index) : (negXF xo).map FieldOp.impl = negX xo.val := rfl

/-! ## Their values -/

theorem pt_congr' {e e' : Env} {a b c : Index} (ha : e' a = e a) (hb : e' b = e b) (hc : e' c = e c) :
    pt e' a b c = pt e a b c := by
  simp only [pt, ha, hb, hc]


theorem doubleF_eval0 (e : Env) :
    pt (applyOps (doubleF 0 21 2) e) 0 21 2 = Proof.Ed448.double (pt e 0 21 2) := rfl

theorem doubleF_eval8 (e : Env) :
    pt (applyOps (doubleF 8 9 10) e) 8 9 10 = Proof.Ed448.double (pt e 8 9 10) := rfl

theorem addF_eval8 (e : Env) :
    pt (applyOps (addF 8 9) e) 3 4 5 = addWith (e 11) (pt e 0 21 2) (pt e 8 9 10) := rfl

theorem addF_eval6 (e : Env) :
    pt (applyOps (addF 6 7) e) 3 4 5 = addWith (e 11) (pt e 0 21 2) (pt e 6 7 10) := rfl

theorem doubleF_keep0 (e : Env) (i : Index)
    (hi : 3 ≤ i.val ∧ i.val < 12 ∨ i.val = 1 ∨ i.val = 20) :
    applyOps (doubleF 0 21 2) e i = e i := by
  refine applyOps_keep _ _ ?_
  revert i; decide

theorem doubleF_keep8 (e : Env) (i : Index)
    (hi : i.val < 8 ∨ i.val = 11 ∨ i.val = 20 ∨ i.val = 21) :
    applyOps (doubleF 8 9 10) e i = e i := by
  refine applyOps_keep _ _ ?_
  revert i; decide

theorem addF_keep (e : Env) (x y : Index) (hx : x.val = 6 ∧ y.val = 7 ∨ x.val = 8 ∧ y.val = 9) (i : Index)
    (hi : i.val < 3 ∨ (6 ≤ i.val ∧ i.val < 12) ∨ i.val = 21) :
    applyOps (addF x y) e i = e i := by
  refine applyOps_keep _ _ ?_
  have hx' : (x = 6 ∧ y = 7) ∨ (x = 8 ∧ y = 9) := by
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
    · exact Or.inr ⟨Fin.ext h1, Fin.ext h2⟩
  rcases hx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert i <;> decide

end VG.Proof.Ed448.Arm
