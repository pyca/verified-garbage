module

public import VerifiedGarbage.Proof.X448.AArch64.Fast.SaveX

public import VerifiedGarbage.Proof.X448.AArch64.Fast.Inv
public import VerifiedGarbage.Proof.X448.AArch64.Weak.Setup
public import VerifiedGarbage.Proof.X448.AArch64.Fast.VSave
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Curve448.AArch64.Legacy
public import VerifiedGarbage.Proof.X448.AArch64.Counters
public import VerifiedGarbage.Proof.X448.AArch64.Freeze
public import VerifiedGarbage.Proof.X448.AArch64.FreezePrep
public import VerifiedGarbage.Proof.X448.AArch64.Output
public import VerifiedGarbage.Proof.X448.AArch64.Select
public import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Proof.Curve448.AArch64.AccumSquareBody
import VerifiedGarbage.Proof.Curve448.AArch64.AddEval
import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
import VerifiedGarbage.Proof.Curve448.AArch64.Collect
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Butterfly
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.ColEnd
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sqr
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Arith
import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
import VerifiedGarbage.Proof.Curve448.AArch64.Product
import VerifiedGarbage.Proof.Curve448.AArch64.Stage
import VerifiedGarbage.Proof.Curve448.AArch64.SymmetricColumn
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X448.AArch64.AddSub
import VerifiedGarbage.Proof.X448.AArch64.BitStep
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.X448.AArch64.Bits
import VerifiedGarbage.Proof.X448.AArch64.Carry
import VerifiedGarbage.Proof.X448.AArch64.Columns
import VerifiedGarbage.Proof.X448.AArch64.Copy
import VerifiedGarbage.Proof.X448.AArch64.Decode
import VerifiedGarbage.Proof.X448.AArch64.DecodeAll
import VerifiedGarbage.Proof.X448.AArch64.DecodeStore
import VerifiedGarbage.Proof.X448.AArch64.Finish
import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.X448.AArch64.Initial
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.X448.AArch64.Normalize
import VerifiedGarbage.Proof.X448.AArch64.PointwiseFused
import VerifiedGarbage.Proof.X448.AArch64.Row
import VerifiedGarbage.Proof.X448.AArch64.Small
import VerifiedGarbage.Proof.X448.AArch64.Step
import VerifiedGarbage.Proof.X448.AArch64.Weak.BitStep
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.Wide.AccumSquareBody
import VerifiedGarbage.Proof.X448.Wide.AddCoefficient
import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
import VerifiedGarbage.Proof.X448.Wide.Columns
import VerifiedGarbage.Proof.X448.Wide.Fold
import VerifiedGarbage.Proof.X448.Wide.LoadCached
import VerifiedGarbage.Proof.X448.Wide.Mul
import VerifiedGarbage.Proof.X448.Wide.Normalize
import VerifiedGarbage.Proof.X448.Wide.Pack
import VerifiedGarbage.Proof.X448.Wide.Pass
import VerifiedGarbage.Proof.X448.Wide.PassInit
import VerifiedGarbage.Proof.X448.Wide.Reduce
import VerifiedGarbage.Proof.X448.Wide.SymmetricColumn
import VerifiedGarbage.Proof.X448.Wide.TailMul
import VerifiedGarbage.Proof.X448.Wide.TailSquare
import VerifiedGarbage.Proof.X448.Wide.TailStep
import VerifiedGarbage.Proof.X448.Wide.Term
import VerifiedGarbage.Proof.X448.Wide.UnpackRegs

/-!
# X448 on AArch64: setup, saving `x21`–`x28` and `v8`–`v15`

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot SWAP BITS ACC)
open VG.Impl.X448.AArch64.Fast (SAVE VSAVE saved save restore vsave)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot Saved)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib stw_ok)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem saved_not_setup : ∀ k < 8, saved k ∉ VG.Proof.X448.AArch64.Weak.setupRegs := by decide

theorem weak_bnd {m : Mem} {base : Addr} {o : Nat} (h : VG.Proof.Curve448.AArch64.Bounded m base o) :
    Bnd Mb m base o := fun i hi => Nat.lt_of_lt_of_le (h i hi) (by decide)

theorem setup0_ok {s : State} {base p : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block (Impl.X448.AArch64.Weak.setup ++ save)) s fun t =>
      Scr t base ∧ BEnv t.mem base ∧ (∀ i : Index, Bnd Mb t.mem base (slot i.val)) ∧
      t.gpr .x20 = s.gpr .x0 ∧ Keeps VG.Proof.X448.AArch64.Weak.setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ Saved base s.gpr t.mem ∧ SavedX base s.gpr t.mem ∧
      EV t.mem base 0 = VG.Proof.X448.toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      EV t.mem base 1 = 1 ∧ EV t.mem base 2 = 0 ∧
      EV t.mem base 3 = EV t.mem base 0 ∧ EV t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setup_ok hc hw hn hp hr hd)
    fun u ⟨us, ub, ux, uk, um, uv, u0, u1, u2, u3, u4, uw⟩ => ?_
  refine WP.mono (save_ok us) fun t ⟨tv, tO, tg, tr, tw⟩ => ?_
  have sl : ∀ i : Index, ∀ j < 8, limbs t.mem base (slot i.val) j = limbs u.mem base (slot i.val) j := by
    intro i j hj
    have hi := i.isLt
    have hS : SAVE = 2880 := rfl
    exact tO.limbs (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega) (by omega)
  have sm : Same base [] u.mem t.mem := fun i _ j hj => sl i j hj
  have red : ∀ i : Index, Bnd Mb t.mem base (slot i.val) := fun i => sm.bnd (by simp) (weak_bnd (ub i))
  have ug : ∀ r, t.gpr r = u.gpr r := fun r => by rw [tg]
  refine ⟨⟨(ug _).trans us.x3, (ug _).trans us.mask, tw ▸ us.wr, us.nowrap⟩,
    fun i j hj => Nat.lt_of_lt_of_le (red i j hj) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib, red, (ug _).trans ux,
    ⟨fun r hr => (ug r).trans (uk.1 r hr), tr.trans uk.2.1, tw.trans uk.2.2⟩,
    um.trans ?_, uv.outside tO (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact tO x (by simp only [SAVE]; omega)
  · intro k hk; rw [tv k hk, uk.1 _ (saved_not_setup k hk)]
  · rw [sm.env (by simp)]; exact u0
  · rw [sm.env (by simp)]; exact u1
  · rw [sm.env (by simp)]; exact u2
  · rw [sm.env (by simp), sm.env (by simp)]; exact u3
  · rw [sm.env (by simp)]; exact u4
  · rw [tO.word (Or.inl (by decide)) (by decide)]; exact uw

theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block Impl.X448.AArch64.Fast.setup) s fun t =>
      Scr t base ∧ BEnv t.mem base ∧ (∀ i : Index, Bnd Mb t.mem base (slot i.val)) ∧
      t.gpr .x20 = s.gpr .x0 ∧ Keeps VG.Proof.X448.AArch64.Weak.setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ Saved base s.gpr t.mem ∧ SavedX base s.gpr t.mem ∧
      EV t.mem base 0 = VG.Proof.X448.toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      EV t.mem base 1 = 1 ∧ EV t.mem base 2 = 0 ∧
      EV t.mem base 3 = EV t.mem base 0 ∧ EV t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 ∧
      SavedV base s.v t.mem := by
  have hV : VSAVE = 4736 := rfl
  rw [Impl.X448.AArch64.Fast.setup, WP.block_append_iff]
  refine WP.mono (WP.preservedV (setup0_ok hc hw hn hp hr hd) (by lit_decide))
    fun u ⟨⟨us, ub, red, ux, uk, uo, sv, svx, u0, u1, u2, u3, u4, uw⟩, uv⟩ => ?_
  refine WP.mono (vsave_ok us) fun t ⟨tv, tO, tg, tr, tw⟩ => ?_
  have sl : ∀ i : Index, ∀ j < 8, limbs t.mem base (slot i.val) j = limbs u.mem base (slot i.val) j := by
    intro i j hj
    have hi := i.isLt
    exact tO.limbs (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega) (by omega)
  have sm : Same base [] u.mem t.mem := fun i _ j hj => sl i j hj
  refine ⟨VG.Proof.Curve448.AArch64.Neon.scr_of us tg tw, fun i => sm.bnd (by simp) (ub i), fun i => sm.bnd (by simp) (red i), tg ▸ ux,
    ⟨fun r hr => (congrFun tg r).trans (uk.1 r hr), tr.trans uk.2.1, tw.trans uk.2.2⟩,
    uo.trans fun x hx => tO x (by omega), sv.outside tO (by decide), svx.outside tO (by decide),
    by rw [sm.env (by simp)]; exact u0, by rw [sm.env (by simp)]; exact u1, by rw [sm.env (by simp)]; exact u2,
    by rw [sm.env (by simp), sm.env (by simp)]; exact u3, by rw [sm.env (by simp)]; exact u4,
    by rw [tO.word (Or.inl (by decide)) (by decide)]; exact uw, fun k hk => ?_⟩
  rw [tv k hk]
  exact uv _ (by rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

end VG.Proof.X448.AArch64.Fast
