import VerifiedGarbage.Proof.Ed448.AArch64.Window.Window
import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit

/-!
# Ed448 verification on AArch64: the points compared

Untrusted: everything here is checked by Lean. `wcross`, after the windows:
`Q = [S]B + [k](-A)` (slots 0–2 plus slots 3–5, `addOps`), `R` from `RX` and
`RY` into slots 6–8 (`Z = 1`), both doubled twice (`dblOps`), and the products
`X_Q Z_R`, `X_R Z_Q`, `Y_Q Z_R`, `Y_R Z_Q` into slots 12–15 (`wcross_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot limb)
open VG.Impl.X448.AArch64.Fast (ops codeOf)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same block_codeOf ops_append mulOp)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genEnv genPt temps addOps_ok zero_env constSlot_ok bnd_of_words F_of_words)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

/-- Two doublings. -/
def dbl2 (p : Point) : Point := VG.Proof.Ed448.double (VG.Proof.Ed448.double p)

/-- What `wcross` leaves in slots 12–15, for `Q` and `R`. -/
structure Cross (Q R : Point) (e : Env) : Prop where
  c12 : e 12 = (dbl2 Q).X * (dbl2 R).Z
  c13 : e 13 = (dbl2 R).X * (dbl2 Q).Z
  c14 : e 14 = (dbl2 Q).Y * (dbl2 R).Z
  c15 : e 15 = (dbl2 R).Y * (dbl2 Q).Z

/-- The doublings and the products, from slots 0–2 and 6–8. -/
theorem crossOps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (h2 : Bnd Mb s.mem base (slot (2 : Index).val)) (h8 : Bnd Mb s.mem base (slot (8 : Index).val))
    (h20 : EV s.mem base 20 = 1) :
    WP isa (.block (codeOf (dblOps (slot 0) (slot 1) (slot 2) ++ dblOps (slot 0) (slot 1) (slot 2) ++
      dblOps (slot 6) (slot 7) (slot 8) ++ dblOps (slot 6) (slot 7) (slot 8) ++
      ([.mul (slot 12) (slot 0) (slot 8), .mul (slot 13) (slot 6) (slot 2),
        .mul (slot 14) (slot 1) (slot 8), .mul (slot 15) (slot 7) (slot 2)] : List Impl.X448.AArch64.Fast.Op)))) s
      fun t => FKeep base s t ∧ Cross (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 6 7 8) (EV t.mem base) ∧
        (∀ i : Index, 12 ≤ i.val → i.val < 16 → Bnd Mb t.mem base (slot i.val)) := by
  refine block_codeOf (ops_append _ _ (ops_append _ _ (ops_append _ _ (ops_append _ _ ?_))))
  refine WP.mono (dblOps_ok 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs hb h2)
    fun t1 ⟨k1, b1, s1, _, _, m2, e1⟩ => ?_
  have hs1 := k1.scr hs
  refine WP.mono (dblOps_ok 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1 b1 m2)
    fun t2 ⟨k2, b2, s2, m0', m1', m2', e2⟩ => ?_
  have hs2 := k2.scr hs1
  have b8 : Bnd Mb t2.mem base (slot (8 : Index).val) := s2.bnd (by decide) (s1.bnd (by decide) h8)
  refine WP.mono (dblOps_ok 6 7 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs2 b2 b8)
    fun t3 ⟨k3, b3, s3, _, _, m8, e3⟩ => ?_
  have hs3 := k3.scr hs2
  refine WP.mono (dblOps_ok 6 7 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs3 b3 m8)
    fun t4 ⟨k4, b4, s4, _, _, _, e4⟩ => ?_
  have hs4 := k4.scr hs3
  refine mulOp hs4 b4 12 0 8 (Or.inr (by decide)) fun t5 k5 b5 m12 s5 e5 => ?_
  have hs5 := k5.scr hs4
  refine mulOp hs5 b5 13 6 2 (Or.inr (by decide)) fun t6 k6 b6 m13 s6 e6 => ?_
  have hs6 := k6.scr hs5
  refine mulOp hs6 b6 14 1 8 (Or.inr (by decide)) fun t7 k7 b7 m14 s7 e7 => ?_
  have hs7 := k7.scr hs6
  refine mulOp hs7 b7 15 7 2 (Or.inr (by decide)) fun t8 k8 b8' m15 s8 e8 => WP.block_nil ?_
  -- The points after the doublings.
  have one1 : EV t1.mem base 20 = 1 := by rw [Same.env s1 (i := 20) (by decide)]; exact h20
  have one2 : EV t2.mem base 20 = 1 := by rw [Same.env s2 (i := 20) (by decide)]; exact one1
  have one3 : EV t3.mem base 20 = 1 := by rw [Same.env s3 (i := 20) (by decide)]; exact one2
  have q2 : pt (EV t2.mem base) 0 1 2 = dbl2 (pt (EV s.mem base) 0 1 2) := by
    rw [e2, dblEnv_012, one1, dblPt_eq, e1, dblEnv_012, h20, dblPt_eq]; rfl
  have r2 : pt (EV t2.mem base) 6 7 8 = pt (EV s.mem base) 6 7 8 := by
    simp only [pt]
    rw [Same.env s2 (i := 6) (by decide), Same.env s2 (i := 7) (by decide), Same.env s2 (i := 8) (by decide),
      Same.env s1 (i := 6) (by decide), Same.env s1 (i := 7) (by decide), Same.env s1 (i := 8) (by decide)]
  have r4 : pt (EV t4.mem base) 6 7 8 = dbl2 (pt (EV s.mem base) 6 7 8) := by
    rw [e4, dblEnv_678, one3, dblPt_eq, e3, dblEnv_678, one2, dblPt_eq, r2]; rfl
  have q4 : pt (EV t4.mem base) 0 1 2 = dbl2 (pt (EV s.mem base) 0 1 2) := by
    rw [← q2]; simp only [pt]
    rw [Same.env s4 (i := 0) (by decide), Same.env s4 (i := 1) (by decide), Same.env s4 (i := 2) (by decide),
      Same.env s3 (i := 0) (by decide), Same.env s3 (i := 1) (by decide), Same.env s3 (i := 2) (by decide)]
  have qx : EV t4.mem base 0 = (dbl2 (pt (EV s.mem base) 0 1 2)).X := congrArg Point.X q4
  have qy : EV t4.mem base 1 = (dbl2 (pt (EV s.mem base) 0 1 2)).Y := congrArg Point.Y q4
  have qz : EV t4.mem base 2 = (dbl2 (pt (EV s.mem base) 0 1 2)).Z := congrArg Point.Z q4
  have rx : EV t4.mem base 6 = (dbl2 (pt (EV s.mem base) 6 7 8)).X := congrArg Point.X r4
  have ry : EV t4.mem base 7 = (dbl2 (pt (EV s.mem base) 6 7 8)).Y := congrArg Point.Y r4
  have rz : EV t4.mem base 8 = (dbl2 (pt (EV s.mem base) 6 7 8)).Z := congrArg Point.Z r4
  refine ⟨k1.trans (k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans k8)))))), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Same.env s8 (i := 12) (by decide), Same.env s7 (i := 12) (by decide), Same.env s6 (i := 12) (by decide),
      e5, Function.update_self, qx, rz]
  · rw [Same.env s8 (i := 13) (by decide), Same.env s7 (i := 13) (by decide), e6, Function.update_self,
      Same.env s5 (i := 6) (by decide), Same.env s5 (i := 2) (by decide), rx, qz]
  · rw [Same.env s8 (i := 14) (by decide), e7, Function.update_self, Same.env s6 (i := 1) (by decide),
      Same.env s5 (i := 1) (by decide), Same.env s6 (i := 8) (by decide), Same.env s5 (i := 8) (by decide), qy, rz]
  · rw [e8, Function.update_self, Same.env s7 (i := 7) (by decide), Same.env s6 (i := 7) (by decide),
      Same.env s5 (i := 7) (by decide), Same.env s7 (i := 2) (by decide), Same.env s6 (i := 2) (by decide),
      Same.env s5 (i := 2) (by decide), ry, qz]
  · intro i h1 h2
    have hi : i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by
      rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at h1 h2 ⊢; omega
    rcases hi with rfl | rfl | rfl | rfl
    · exact s8.bnd (by decide) (s7.bnd (by decide) (s6.bnd (by decide) m12))
    · exact s8.bnd (by decide) (s7.bnd (by decide) m13)
    · exact s8.bnd (by decide) m14
    · exact m15

theorem wcross_eq : wcross =
    codeOf (Impl.X448.AArch64.Base.addOps (slot (0 : Index).val) (slot (1 : Index).val) (slot (2 : Index).val)
      (slot (3 : Index).val) (slot (4 : Index).val) (slot (5 : Index).val)) ++
    (Impl.Curve448.AArch64.copy (slot 6) RX ++ (Impl.Curve448.AArch64.copy (slot 7) RY ++ (constSlot (slot 8) 1 ++
    codeOf (dblOps (slot 0) (slot 1) (slot 2) ++ dblOps (slot 0) (slot 1) (slot 2) ++
      dblOps (slot 6) (slot 7) (slot 8) ++ dblOps (slot 6) (slot 7) (slot 8) ++
      ([.mul (slot 12) (slot 0) (slot 8), .mul (slot 13) (slot 6) (slot 2),
        .mul (slot 14) (slot 1) (slot 8), .mul (slot 15) (slot 7) (slot 2)] : List Impl.X448.AArch64.Fast.Op))))) := by
  simp only [wcross, List.append_assoc]; rfl

/-- The registers `wcross` may write. -/
def crossClob : List Reg := .x4 :: VG.Proof.Curve448.AArch64.Fast.clob ++ VG.Proof.X448.AArch64.clob

/-- **The points compared**: `Q = [S]B + [k](-A)` and `R` (from `RX` and `RY`), doubled twice,
cross-multiplied into slots 12–15. -/
theorem wcross_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hz : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0) (h20 : EV s.mem base 20 = 1)
    (hrx : ∀ i < 8, limbs s.mem base RX i < Ib) (hry : ∀ i < 8, limbs s.mem base RY i < Ib) :
    WP isa (.block wcross) s fun t =>
      Scr t base ∧ Keeps crossClob s t ∧ Outside2 base 64 2816 ACC 1152 s.mem t.mem ∧
      Cross (addPt (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 3 4 5)) ⟨FV s.mem base RX, FV s.mem base RY, 1⟩
        (EV t.mem base) ∧
      (∀ i : Index, 12 ≤ i.val → i.val < 16 → Bnd Mb t.mem base (slot i.val)) := by
  rw [wcross_eq, WP.block_append_iff]
  refine WP.mono (block_codeOf (addOps_ok 0 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hs hb (zero_env hz).2))
    fun t1 ⟨k1, b1, s1, _, _, m2, e1⟩ => ?_
  have hs1 := k1.scr hs
  have rx1 : ∀ i < 8, limbs t1.mem base RX i = limbs s.mem base RX i := fun i hi =>
    congrArg BitVec.toNat (k1.mem.word (Or.inr (by simp only [RX]; omega)) (Or.inr (by simp only [RX, ACC]; omega))
      (by simp only [RX]; omega))
  have ry1 : ∀ i < 8, limbs t1.mem base RY i = limbs s.mem base RY i := fun i hi =>
    congrArg BitVec.toNat (k1.mem.word (Or.inr (by simp only [RY, CAN]; omega)) (Or.inr (by simp only [RY, CAN, ACC]; omega))
      (by simp only [RY, CAN]; omega))
  rw [WP.block_append_iff]
  refine WP.mono (copyS_ok hs1 (o := slot 6) (a := RX) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨v2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyS_ok hs2 (o := slot 7) (a := RY) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t3 ⟨v3, o3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok hs3 (o := slot 8) (by decide) (by decide) 1) fun t4 ⟨v4, o4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  -- The slots after the loads: 6–8 the point `R`, every other one kept.
  have keep : ∀ i : Index, i ≠ 6 → i ≠ 7 → i ≠ 8 → ∀ j < 8,
      limbs t4.mem base (slot i.val) j = limbs t1.mem base (slot i.val) j := fun i h6 h7 h8 j hj => by
    have := i.isLt
    have n6 : i.val ≠ 6 := fun e => h6 (Fin.ext e)
    have n7 : i.val ≠ 7 := fun e => h7 (Fin.ext e)
    have n8 : i.val ≠ 8 := fun e => h8 (Fin.ext e)
    rw [o4.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o3.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o2.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)]
  have l6 : ∀ j < 8, limbs t4.mem base (slot 6) j = limbs s.mem base RX j := fun j hj => by
    rw [o4.limbs (by decide) (by decide) (by omega), o3.limbs (by decide) (by decide) (by omega), v2 j hj, rx1 j hj]
  have l7 : ∀ j < 8, limbs t4.mem base (slot 7) j = limbs s.mem base RY j := fun j hj => by
    rw [o4.limbs (by decide) (by decide) (by omega), v3 j hj,
      o2.limbs (by simp only [RY, CAN]; decide) (by simp only [RY, CAN]; decide) (by omega), ry1 j hj]
  have b4 : BEnv t4.mem base := by
    intro i
    by_cases h6 : i = 6
    · subst h6; exact fun j hj => by show limbs t4.mem base (slot 6) j < Ib; rw [l6 j hj]; exact hrx j hj
    by_cases h7 : i = 7
    · subst h7; exact fun j hj => by show limbs t4.mem base (slot 7) j < Ib; rw [l7 j hj]; exact hry j hj
    by_cases h8 : i = 8
    · subst h8; exact bnd_of_words v4
    · exact fun j hj => by rw [keep i h6 h7 h8 j hj]; exact b1 i j hj
  have e4 : ∀ i : Index, i ≠ 6 → i ≠ 7 → i ≠ 8 → EV t4.mem base i = EV t1.mem base i := fun i h6 h7 h8 =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (keep i h6 h7 h8))
  have p8 : pt (EV t4.mem base) 6 7 8 = ⟨FV s.mem base RX, FV s.mem base RY, 1⟩ := by
    show (⟨FV t4.mem base (slot 6), FV t4.mem base (slot 7), FV t4.mem base (slot 8)⟩ : Point) = _
    rw [FV_of_limbs l6, FV_of_limbs l7, F_of_words v4]
  have q1 : pt (EV t1.mem base) 0 1 2 = addPt (pt (EV s.mem base) 0 1 2) (pt (EV s.mem base) 3 4 5) := by
    rw [e1, VG.Proof.X448.AArch64.Base.genEnv_add, (zero_env hz).1, VG.Proof.X448.AArch64.Base.genPt_eq]
  have q4 : pt (EV t4.mem base) 0 1 2 = pt (EV t1.mem base) 0 1 2 := by
    simp only [pt]; rw [e4 0 (by decide) (by decide) (by decide), e4 1 (by decide) (by decide) (by decide),
      e4 2 (by decide) (by decide) (by decide)]
  have one4 : EV t4.mem base 20 = 1 := by
    rw [e4 20 (by decide) (by decide) (by decide), Same.env s1 (i := 20) (by decide)]; exact h20
  have m2' : Bnd Mb t4.mem base (slot (2 : Index).val) := fun j hj => by
    rw [keep 2 (by decide) (by decide) (by decide) j hj]; exact m2 j hj
  have m8 : Bnd Mb t4.mem base (slot (8 : Index).val) := fun j hj => by
    show (word t4.mem base (slot 8 + 8 * j)).toNat < Mb
    rw [v4 j hj]; exact Nat.lt_of_lt_of_le (VG.Proof.X448.AArch64.Base.limb_lt _ _) (by decide)
  refine WP.mono (crossOps_ok hs4 b4 m2' m8 one4) fun t ⟨kt, ct, bt⟩ => ⟨kt.scr hs4, ?_, ?_, ?_, bt⟩
  · exact ((((k1.regs.mono (fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr))).trans
      (k2.mono (fun r hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr)))).trans
      (k3.mono (fun r hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr)))).trans
      (k4.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self))).trans
      (kt.regs.mono (fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr)))
  · have o24 : Outside2 base 64 2816 ACC 1152 t1.mem t4.mem := fun x a _ => by
      rw [o4 x (by simp only [slot] at a ⊢; omega), o3 x (by simp only [slot] at a ⊢; omega),
        o2 x (by simp only [slot] at a ⊢; omega)]
    exact (k1.mem.trans o24).trans kt.mem
  · rw [← q1, ← q4, ← p8]; exact ct

end VG.Proof.Ed448.AArch64.Window
