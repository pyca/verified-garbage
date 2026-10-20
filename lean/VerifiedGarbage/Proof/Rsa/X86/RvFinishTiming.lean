module
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Rsa.X86.RvInputs
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Rsa.X86.RvStoresTiming
import VerifiedGarbage.Proof.Rsa.X86.RvLoopTiming
import VerifiedGarbage.Proof.Rsa.X86.RvFactors
import VerifiedGarbage.Proof.Rsa.X86.RvFinishY
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Computing and exporting factors keeps recovered values secret -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem fin_relCT (g : CallGeometry) (s0 t0 : State) (A B AW BW V W : Nat → Nat)
    (m k c : Nat) (st tt : Nat × Bool × Bool)
    (left : Inputs g s0) (right : Inputs g t0) (sp : s0.gpr .esp = t0.gpr .esp)
    (valueA : A mBase = m) (valueB : B mBase = m)
    (modA : A aN = m) (modB : B aN = m) (bound : m < 2 ^ (64 * g.n))
    (invA : (m * V sInv + 1) % 2 ^ 32 = 0) (invB : (m * W sInv + 1) % 2 ^ 32 = 0)
    (odd : m % 2 = 1) (large : 1 < m)
    (zeroA : A aZ = 0) (zeroB : B aZ = 0) (oneA : A aOne = 1) (oneB : B aOne = 1)
    (yl : st.1 < m) (zl : tt.1 < m) :
    RelCT isa (fun s t => SI g.toGeo s0 A AW V m k c st s ∧ SI g.toGeo t0 B BW W m k c tt t)
      (fin g.n) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := ((finY_workspace g.n).trace _ _ _ _ _ _ (ks_agree hs ht) e1 f1).1
      have cs := wp_result (finY_ok hs valueA bound invA odd large oneA yl) e1
      have ds := wp_result (finY_ok ht valueB bound invB odd large oneB zl) f1
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          have eq2 := ((factors_workspace g.n).trace _ _ _ _ _ _ (ks_agree cs ds) e2 f2).1
          have cx := wp_result (factors_ok cs
            (by simpa only [upd_ne _ _ (by decide : aN ≠ mY)] using modA)
            (by rw [upd_self]) (by simpa only [upd_ne _ _ (by decide : aZ ≠ mY)] using zeroA)
            (by simpa only [upd_ne _ _ (by decide : aOne ≠ mY)] using oneA) odd large) e2
          have dx := wp_result (factors_ok ds
            (by simpa only [upd_ne _ _ (by decide : aN ≠ mY)] using modB)
            (by rw [upd_self]) (by simpa only [upd_ne _ _ (by decide : aZ ≠ mY)] using zeroB)
            (by simpa only [upd_ne _ _ (by decide : aOne ≠ mY)] using oneB) odd large) f2
          have pair : Pair g x y := ⟨left.of_KS cx, right.of_KS dx,
            (cx.rest.1 _ (by decide)).trans (sp.trans (dx.rest.1 _ (by decide)).symm)⟩
          have readyC : Ready g x := ⟨by rw [cx.arrs aZero (by simp)]; rfl,
            st.2.2, cx.sl sMask (by simp)⟩
          have readyD : Ready g y := ⟨by rw [dx.arrs aZero (by simp)]; rfl,
            tt.2.2, dx.sl sMask (by simp)⟩
          have eq3 := (stores_relCT g _ _ _ _ _ _ ⟨pair, readyC, readyD⟩ e3 f3).1
          exact ⟨by rw [eq1, eq2, eq3], trivial⟩

end VG.Proof.Rsa.X86.Recover
