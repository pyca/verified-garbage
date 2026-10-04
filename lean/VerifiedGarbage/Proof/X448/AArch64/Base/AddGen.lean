import VerifiedGarbage.Proof.X448.AArch64.Base.AddEnv

/-!
# X448 of the base point on AArch64: the complete addition

Untrusted: everything here is checked by Lean. `addOps` (`Impl/X448/AArch64/Base.lean`),
scalar field operations only, for the four doublings and the last addition: the
environment afterwards is `genEnv` of the one before, which for the slots used is
`addPt` of the two points (`genEnv_dbl`, `genEnv_add`, `genPt_eq`).
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.X448.AArch64.Fast (ops codeOf)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- One operation's update of the environment. -/
def mulS (o a b : Index) (e : Env) : Env := Function.update e o (e a * e b)
def smallS (o a c : Index) (e : Env) : Env := Function.update e o (e a + Spec.X448.a24 * e c)
def subS (o a b : Index) (e : Env) : Env := Function.update e o (e a - e b)
def addSubS (o₁ o₂ a b : Index) (e : Env) : Env :=
  Function.update (Function.update e o₁ (e a + e b)) o₂ (e a - e b)

/-- The environment after `addOps x1 y1 z1 x2 y2 z2`. -/
def genEnv (x1 y1 z1 x2 y2 z2 : Index) (e : Env) : Env :=
  mulS z1 15 11 <| mulS y1 13 16 <| mulS 13 10 11 <| mulS x1 12 17 <| mulS 12 10 15 <|
  addSubS 14 16 13 12 <| addSubS 17 18 14 16 <| mulS 16 y1 x2 <| mulS 14 x1 y2 <|
  smallS 11 11 16 <| subS 16 19 14 <| smallS 15 11 14 <| mulS 14 12 13 <| mulS 13 y1 y2 <|
  mulS 12 x1 x2 <| mulS 11 10 10 <| mulS 10 z1 z2 e

theorem addOps_eq (x1 y1 z1 x2 y2 z2 : Index) :
    Impl.X448.AArch64.Base.addOps (slot x1.val) (slot y1.val) (slot z1.val) (slot x2.val) (slot y2.val)
      (slot z2.val) =
    [.mul (slot (10 : Index).val) (slot z1.val) (slot z2.val),
     .mul (slot (11 : Index).val) (slot (10 : Index).val) (slot (10 : Index).val),
     .mul (slot (12 : Index).val) (slot x1.val) (slot x2.val),
     .mul (slot (13 : Index).val) (slot y1.val) (slot y2.val),
     .mul (slot (14 : Index).val) (slot (12 : Index).val) (slot (13 : Index).val),
     .small (slot (15 : Index).val) (slot (11 : Index).val) (slot (14 : Index).val),
     .sub (slot (16 : Index).val) (slot (19 : Index).val) (slot (14 : Index).val),
     .small (slot (11 : Index).val) (slot (11 : Index).val) (slot (16 : Index).val),
     .mul (slot (14 : Index).val) (slot x1.val) (slot y2.val),
     .mul (slot (16 : Index).val) (slot y1.val) (slot x2.val),
     .addSub (slot (17 : Index).val) (slot (18 : Index).val) (slot (14 : Index).val) (slot (16 : Index).val),
     .addSub (slot (14 : Index).val) (slot (16 : Index).val) (slot (13 : Index).val) (slot (12 : Index).val),
     .mul (slot (12 : Index).val) (slot (10 : Index).val) (slot (15 : Index).val),
     .mul (slot x1.val) (slot (12 : Index).val) (slot (17 : Index).val),
     .mul (slot (13 : Index).val) (slot (10 : Index).val) (slot (11 : Index).val),
     .mul (slot y1.val) (slot (13 : Index).val) (slot (16 : Index).val),
     .mul (slot z1.val) (slot (15 : Index).val) (slot (11 : Index).val)] := rfl

theorem ne_of_lt10 {i : Index} (hi : i.val < 10) (k : Nat) (hk : 10 ≤ k) (hk' : k < 22) :
    (⟨k, hk'⟩ : Index) ≠ i := fun h => by rw [← h] at hi; exact absurd hi (by simp; omega)

section
variable {s : State} {base : Addr}

/-- **The complete addition** of the points in slots `x2, y2, z2` to those in `x1, y1, z1`
(which may be the same, to double), all below slot 10, given zero's bound in slot 19. -/
theorem addOps_ok (x1 y1 z1 x2 y2 z2 : Index) (hx1 : x1.val < 10) (hy1 : y1.val < 10) (hz1 : z1.val < 10)
    (hx2 : x2.val < 10) (hy2 : y2.val < 10) (hz2 : z2.val < 10) (hxy : x1 ≠ y1) (hzx : z1 ≠ x1)
    (hzy : z1 ≠ y1) (hs : Scr s base) (hb : BEnv s.mem base) (h19 : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa (ops (Impl.X448.AArch64.Base.addOps (slot x1.val) (slot y1.val) (slot z1.val) (slot x2.val)
        (slot y2.val) (slot z2.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base (temps ++ [x1, y1, z1]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot x1.val) ∧ Bnd Mb t.mem base (slot y1.val) ∧ Bnd Mb t.mem base (slot z1.val) ∧
      EV t.mem base = genEnv x1 y1 z1 x2 y2 z2 (EV s.mem base) := by
  -- Every temporary differs from every point slot.
  have n : ∀ {i : Index}, i.val < 10 → ∀ k : Index, 10 ≤ k.val → k ≠ i := fun hi k hk h => by
    rw [h] at hk; omega
  have nn : ∀ {i : Index}, i.val < 10 → ∀ k : Index, 10 ≤ k.val → i ∉ [k] := fun hi k hk h => by
    rw [List.mem_singleton] at h; exact n hi k hk h.symm
  have nn' : ∀ {i j : Index}, i ≠ j → i ∉ [j] := fun h hm => h (List.mem_singleton.mp hm)
  rw [addOps_eq]
  refine mulOp hs hb 10 z1 z2 (Or.inr (n hz2 10 (by decide))) fun t1 k1 b1 _ s1 e1 => ?_
  have hs1 := k1.scr hs
  refine mulOp hs1 b1 11 10 10 (Or.inl rfl) fun t2 k2 b2 m2 s2 e2 => ?_
  have hs2 := k2.scr hs1
  refine mulOp hs2 b2 12 x1 x2 (Or.inr (n hx2 12 (by decide))) fun t3 k3 b3 m3 s3 e3 => ?_
  have hs3 := k3.scr hs2
  refine mulOp hs3 b3 13 y1 y2 (Or.inr (n hy2 13 (by decide))) fun t4 k4 b4 m4 s4 e4 => ?_
  have hs4 := k4.scr hs3
  refine mulOp hs4 b4 14 12 13 (Or.inr (by decide)) fun t5 k5 b5 m5 s5 e5 => ?_
  have hs5 := k5.scr hs4
  have m2' : Bnd Mb t5.mem base (slot (11 : Index).val) :=
    s5.bnd (by decide) (s4.bnd (by decide) (s3.bnd (by decide) m2))
  refine smallOp (o := 15) (a := 11) (e := 14) hs5 b5 m2' fun t6 k6 b6 s6 e6 => ?_
  have hs6 := k6.scr hs5
  have z6 : Bnd Mb t6.mem base (slot (19 : Index).val) :=
    s6.bnd (by decide) (s5.bnd (by decide) (s4.bnd (by decide) (s3.bnd (by decide) (s2.bnd (by decide)
      (s1.bnd (by decide) h19)))))
  refine subOp (o := 16) (a := 19) (b := 14) hs6 b6 z6 (s6.bnd (by decide) m5) (by decide) (by decide)
    fun t7 k7 b7 s7 e7 => ?_
  have hs7 := k7.scr hs6
  refine smallOp (o := 11) (a := 11) (e := 16) hs7 b7 (s7.bnd (by decide) (s6.bnd (by decide) m2'))
    fun t8 k8 b8 s8 e8 => ?_
  have hs8 := k8.scr hs7
  refine mulOp hs8 b8 14 x1 y2 (Or.inr (n hy2 14 (by decide))) fun t9 k9 b9 m9 s9 e9 => ?_
  have hs9 := k9.scr hs8
  refine mulOp hs9 b9 16 y1 x2 (Or.inr (n hx2 16 (by decide))) fun t10 k10 b10 m10 s10 e10 => ?_
  have hs10 := k10.scr hs9
  refine addSubOp (o₁ := 17) (o₂ := 18) (a := 14) (b := 16) hs10 b10 (s10.bnd (by decide) m9) m10
    (by decide) (by decide) (by decide) (by decide) (by decide) fun t11 k11 b11 s11 e11 => ?_
  have hs11 := k11.scr hs10
  have m4' : Bnd Mb t11.mem base (slot (13 : Index).val) :=
    s11.bnd (by decide) (s10.bnd (by decide) (s9.bnd (by decide) (s8.bnd (by decide) (s7.bnd (by decide)
      (s6.bnd (by decide) (s5.bnd (by decide) m4))))))
  have m3' : Bnd Mb t11.mem base (slot (12 : Index).val) :=
    s11.bnd (by decide) (s10.bnd (by decide) (s9.bnd (by decide) (s8.bnd (by decide) (s7.bnd (by decide)
      (s6.bnd (by decide) (s5.bnd (by decide) (s4.bnd (by decide) m3)))))))
  refine addSubOp (o₁ := 14) (o₂ := 16) (a := 13) (b := 12) hs11 b11 m4' m3'
    (by decide) (by decide) (by decide) (by decide) (by decide) fun t12 k12 b12 s12 e12 => ?_
  have hs12 := k12.scr hs11
  refine mulOp hs12 b12 12 10 15 (Or.inr (by decide)) fun t13 k13 b13 _ s13 e13 => ?_
  have hs13 := k13.scr hs12
  refine mulOp hs13 b13 x1 12 17 (Or.inr (n hx1 17 (by decide)).symm) fun t14 k14 b14 m14 s14 e14 => ?_
  have hs14 := k14.scr hs13
  refine mulOp hs14 b14 13 10 11 (Or.inr (by decide)) fun t15 k15 b15 _ s15 e15 => ?_
  have hs15 := k15.scr hs14
  refine mulOp hs15 b15 y1 13 16 (Or.inr (n hy1 16 (by decide)).symm) fun t16 k16 b16 m16 s16 e16 => ?_
  have hs16 := k16.scr hs15
  refine mulOp hs16 b16 z1 15 11 (Or.inr (n hz1 11 (by decide)).symm) fun t17 k17 b17 m17 s17 e17 => ?_
  refine WP.block_nil ⟨k1.trans (k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans (k8.trans
    (k9.trans (k10.trans (k11.trans (k12.trans (k13.trans (k14.trans (k15.trans (k16.trans k17))))))))))))))),
    b17, ?_, ?_, ?_, m17, ?_⟩
  · refine VG.Proof.X448.AArch64.Base.Same.mono
      (s1.append (s2.append (s3.append (s4.append (s5.append (s6.append (s7.append (s8.append (s9.append
        (s10.append (s11.append (s12.append (s13.append (s14.append (s15.append (s16.append s17))))))))))))))))
      fun i hi => ?_
    simp only [temps, List.cons_append, List.nil_append] at hi ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp
  · exact s17.bnd (nn' hzx.symm) (s16.bnd (nn' hxy) (s15.bnd (nn hx1 13 (by decide)) m14))
  · exact s17.bnd (nn' hzy.symm) m16
  · exact e17.trans <| congrArg (mulS z1 15 11) <| e16.trans <| congrArg (mulS y1 13 16) <| e15.trans <|
      congrArg (mulS 13 10 11) <| e14.trans <| congrArg (mulS x1 12 17) <| e13.trans <|
      congrArg (mulS 12 10 15) <| e12.trans <| congrArg (addSubS 14 16 13 12) <| e11.trans <|
      congrArg (addSubS 17 18 14 16) <| e10.trans <| congrArg (mulS 16 y1 x2) <| e9.trans <|
      congrArg (mulS 14 x1 y2) <| e8.trans <| congrArg (smallS 11 11 16) <| e7.trans <|
      congrArg (subS 16 19 14) <| e6.trans <| congrArg (smallS 15 11 14) <| e5.trans <|
      congrArg (mulS 14 12 13) <| e4.trans <| congrArg (mulS 13 y1 y2) <| e3.trans <|
      congrArg (mulS 12 x1 x2) <| e2.trans <| congrArg (mulS 11 10 10) <| e1

end

/-- What `addOps` computes from `(X₁ : Y₁ : Z₁)` and `(X₂ : Y₂ : Z₂)`, with `z0` (zero) in slot 19. -/
def genPt (p q : Point) (z0 : Spec.X448.Fe) : Point :=
  let a := p.Z * q.Z
  let b := a * a
  let c := p.X * q.X
  let e := p.Y * q.Y
  let f := b + Spec.X448.a24 * (c * e)
  let g := b + Spec.X448.a24 * (z0 - c * e)
  ⟨a * f * (p.X * q.Y + p.Y * q.X), a * g * (e - c), f * g⟩

theorem genEnv_dbl (e : Env) : pt (genEnv 0 1 2 0 1 2 e) 0 1 2 = genPt (pt e 0 1 2) (pt e 0 1 2) (e 19) := rfl

theorem genEnv_add (e : Env) : pt (genEnv 0 1 2 3 4 5 e) 0 1 2 = genPt (pt e 0 1 2) (pt e 3 4 5) (e 19) := rfl

theorem genPt_eq (p q : Point) : genPt p q 0 = addPt p q := rfl

end VG.Proof.X448.AArch64.Base
