module

import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
import VerifiedGarbage.Proof.X448.AArch64.Fast.Weave
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Dbl
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Table
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Ed448 verification on AArch64: the points compared

Untrusted: everything here is checked by Lean. What the comparison of `Q` and
`R` leaves, both doubled twice (`dbl2`): the products `X_Q Z_R`, `X_R Z_Q`,
`Y_Q Z_R`, `Y_R Z_Q` in slots 12–15 (`Cross`), the registers it may write
(`crossClob`), and copies of slots (`copy3_ok`, `pt_of_limbs`, `bnd_copy`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot limb)
open VG.Impl.X448.AArch64.Fast (ops codeOf)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same block_codeOf ops_append mulOp)
open VG.Proof.Ed448.AArch64.Point56 (mulOpK)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genEnv genPt temps addOps_ok zero_env constSlot_ok bnd_of_words F_of_words)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- Two doublings. -/
def dbl2 (p : Point) : Point := VG.Proof.Ed448.double (VG.Proof.Ed448.double p)

/-- What the comparison leaves in slots 12–15, for `Q` and `R`. -/
structure Cross (Q R : Point) (e : Env) : Prop where
  c12 : e 12 = (dbl2 Q).X * (dbl2 R).Z
  c13 : e 13 = (dbl2 R).X * (dbl2 Q).Z
  c14 : e 14 = (dbl2 Q).Y * (dbl2 R).Z
  c15 : e 15 = (dbl2 R).Y * (dbl2 Q).Z

/-- Three slots copied from three others, among bounded ones: the copies' limbs, and every
other slot's kept. -/
theorem copy3_ok {s : State} {base : Addr} (hs : Scr s base) (o a : Nat) (ho : o + 3 ≤ 22) (ha : a + 3 ≤ 22)
    (hsep : o + 3 ≤ a ∨ a + 3 ≤ o) :
    WP isa (.block (Impl.Curve448.AArch64.copy (slot o) (slot a) ++ Impl.Curve448.AArch64.copy (slot (o + 1))
        (slot (a + 1)) ++ Impl.Curve448.AArch64.copy (slot (o + 2)) (slot (a + 2)))) s fun t =>
      (∀ c < 3, ∀ j < 8, limbs t.mem base (slot (o + c)) j = limbs s.mem base (slot (a + c)) j) ∧
      (∀ i : Index, (i.val < o ∨ o + 3 ≤ i.val) → ∀ j < 8, limbs t.mem base (slot i.val) j =
        limbs s.mem base (slot i.val) j) ∧
      Outside base (slot o) 384 s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyS_ok hs (o := slot o) (a := slot a) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)) fun t1 ⟨v1, o1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (copyS_ok hs1 (o := slot (o + 1)) (a := slot (a + 1)) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith)) fun t2 ⟨v2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  refine WP.mono (copyS_ok hs2 (o := slot (o + 2)) (a := slot (a + 2)) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith)) fun t ⟨v3, o3, k3⟩ => ⟨fun c hc j hj => ?_, fun i hi j hj => ?_, ?_,
      (k1.trans k2).trans k3⟩
  · rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega_arith) with rfl | rfl | rfl
    · rw [o3.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
        o2.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith), Nat.add_zero, v1 j hj,
        Nat.add_zero]
    · rw [o3.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith), v2 j hj,
        o1.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith)]
    · rw [v3 j hj, o2.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
        o1.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith)]
  · have := i.isLt
    rw [o3.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
      o2.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
      o1.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith)]
  · intro x hx
    rw [o3 x (by simp only [slot] at hx ⊢; omega_arith), o2 x (by simp only [slot] at hx ⊢; omega_arith),
      o1 x (by simp only [slot] at hx ⊢; omega_arith)]

theorem pt_of_limbs {m m' : Mem} {base : Addr} {o a : Nat}
    (h : ∀ c < 3, ∀ j < 8, limbs m' base (slot (o + c)) j = limbs m base (slot (a + c)) j)
    {x y z x' y' z' : Index} (hx : x.val = o) (hy : y.val = o + 1) (hz : z.val = o + 2) (hx' : x'.val = a)
    (hy' : y'.val = a + 1) (hz' : z'.val = a + 2) : pt (EV m' base) x y z = pt (EV m base) x' y' z' := by
  simp only [pt, VG.Proof.X448.AArch64.Weak.E]
  rw [hx, hy, hz, hx', hy', hz']
  rw [FV_of_limbs (o := slot a) (o' := slot o) (fun j hj => by simpa using h 0 (by decide) j hj),
    FV_of_limbs (h 1 (by decide)), FV_of_limbs (h 2 (by decide))]

/-- The registers the comparison may write. -/
def crossClob : List Reg := .x30 :: .x4 :: VG.Proof.Curve448.AArch64.Fast.clob ++ VG.Proof.X448.AArch64.clob

theorem crossClob_ckeep {s t : State} {base : Addr} (h : Point56.CKeep base s t) : Keeps crossClob s t :=
  h.regs.mono fun _ hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hr))

theorem crossClob_clob {s t : State} (h : Keeps VG.Proof.X448.AArch64.clob s t) : Keeps crossClob s t :=
  h.mono fun _ hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hr))

theorem bnd_copy {m m' : Mem} {base : Addr} {o a : Nat} {n : Nat}
    (h : ∀ j < 8, limbs m' base o j = limbs m base a j) (hb : Bnd n m base a) : Bnd n m' base o := fun j hj => by
  rw [h j hj]; exact hb j hj

end VG.Proof.Ed448.AArch64.Window
