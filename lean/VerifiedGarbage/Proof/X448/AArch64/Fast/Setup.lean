module

public import VerifiedGarbage.Proof.X448.AArch64.Fast.VSave
public import VerifiedGarbage.Proof.X448.AArch64.Weak.Setup
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Curve448.AArch64.Legacy
public import VerifiedGarbage.Proof.X448.AArch64.Freeze
public import VerifiedGarbage.Proof.X448.AArch64.FreezePrep
public import VerifiedGarbage.Proof.X448.AArch64.Finish
import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
import VerifiedGarbage.Proof.Curve448.AArch64.Stage
import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sqr
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Value
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
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.X448.AArch64.Bits
import VerifiedGarbage.Proof.X448.AArch64.Carry
import VerifiedGarbage.Proof.X448.AArch64.Copy
import VerifiedGarbage.Proof.X448.AArch64.Setup
import VerifiedGarbage.Proof.X448.AArch64.Mul
import VerifiedGarbage.Proof.X448.AArch64.Initial
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.X448.AArch64.Step
import VerifiedGarbage.Proof.X448.AArch64.Weak.Iter
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.Wide.Pass
import VerifiedGarbage.Proof.X448.Wide.Fold
import VerifiedGarbage.Proof.X448.Wide.Pack
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.X448.Limbs
import VerifiedGarbage.Proof.X448.AArch64.Swap
import VerifiedGarbage.Impl.X448.AArch64
import VerifiedGarbage.Proof.X448.AArch64.Mem
import Batteries.Logic
import VerifiedGarbage.Impl.X448.AArch64.Symmetric
import VerifiedGarbage.Proof.X448.Wide.Product
import VerifiedGarbage.Proof.X448.Wide.Word
import VerifiedGarbage.Proof.X448.Wide.Memory
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Ladder
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Chain
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulSlots

/-! ### `X448.AArch64.Fast.Inv`, which this module and modules that import it used -/

section

/-!
# X448 on AArch64: inversion

Untrusted: everything here is checked by Lean. `z` (slot 2) copied to slot 12,
a call of `vg_gf448_r56_pow_p34` (`powCall_ok`) with the return address kept in a
lane of `v8` (`call_spec`), and the power squared twice and multiplied by `z` (a call of
`vg_gf448_r56_mul`, `mulCallKI`):
slot 21 ends as `z^(p-2)` (`invEnv_eval`), since `z^(p-2) = (z^((p-3)/4))^4 z`
(`invert_rootPow`). It keeps what the inlined chain did (`IKeep`).
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Keeps Scr)
open VG.Proof.X448.AArch64.Weak (Index Env FieldOp applyOps opMul opCopy opSqn)
open VG.Proof.Ed448.AArch64 (rootEnv rootEnv_eval rootEnv_keep)
open VG.Proof.Ed448.AArch64.Point56 (CKeep powCall_ok)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `z^(p-2)` is `(z^((p-3)/4))^4 z`. -/
theorem invert_rootPow (z : Spec.X448.Fe) :
    Proof.X448.sqn (Proof.Ed448.rootPow z) 2 * z = Proof.X448.invert z := by
  have e : (Spec.X448.P - 3) / 4 * 2 ^ 2 + 1 = Spec.X448.P - 2 := by decide +kernel
  calc Proof.X448.sqn (Proof.Ed448.rootPow z) 2 * z
      = Proof.X448.sqn (Proof.X448.pw z ((Spec.X448.P - 3) / 4)) 2 * Proof.X448.pw z 1 := by
        rw [Proof.Ed448.rootPow_eq, Proof.X448.pow_pw, Proof.X448.pw_one]
    _ = Proof.X448.pw z ((Spec.X448.P - 3) / 4 * 2 ^ 2 + 1) := by
        rw [Proof.X448.sqn_pw, Proof.X448.pw_mul]
    _ = Proof.X448.pw z (Spec.X448.P - 2) := congrArg (Proof.X448.pw z) e
    _ = Proof.X448.invert z := by rw [Proof.X448.invert_eq, Proof.X448.pow_pw]

/-- The call, with the return address kept in `v8`: the slots as after `root 12`. -/
theorem call_spec (base : Addr) : ISpec base Impl.X448.AArch64.Fast.powCallKeep rootEnv := by
  intro s hs hb
  rw [Impl.X448.AArch64.Fast.powCallKeep, WP.seq_iff]
  refine WP.mono (insOf_ok [(.x30, .v8, 0)] s (by decide) (by decide))
    fun t₁ ⟨g₁, m₁, r₁, w₁, _, l₁, _⟩ => ?_
  have hs₁ : Scr t₁ base := hs.of_keeps (rs := []) ⟨fun r _ => by rw [g₁], r₁, w₁⟩ (by decide)
  rw [WP.seq_iff]
  refine WP.mono (powCall_ok hs₁ (m₁ ▸ hb)) fun t ⟨ck, pb, pe, _⟩ => ?_
  refine WP.mono (umovOf_ok [(.x30, .v8, 0)] t (by decide) (by decide))
    fun u ⟨um, ur, uw, _, ul, uo⟩ => ?_
  have l30 : u.gpr .x30 = s.gpr .x30 := by
    rw [ul _ List.mem_cons_self, ← l₁ _ List.mem_cons_self]
    exact ck.v .v8 (by decide)
  refine ⟨⟨⟨fun r hr => ?_, by rw [ur, ck.regs.2.1, r₁], by rw [uw, ck.regs.2.2, w₁]⟩,
    by rw [um, ← m₁]; exact ck.mem⟩, by rw [um]; exact pb, by rw [um, pe, m₁]⟩
  by_cases h30 : r = .x30
  · rw [h30]; exact l30
  · rw [uo r (by simpa using h30), ck.regs.1 r fun h => hr ((List.mem_cons.mp h).resolve_left h30 |> List.mem_cons_of_mem _), g₁]

/-- The slots after the inversion. -/
def invEnv (e : Env) : Env :=
  applyOps [.mul 21 21 2] (opSqn 21 2 (rootEnv (applyOps [.copy 12 2] e)))

theorem invert_spec (base : Addr) : ISpec base Impl.X448.AArch64.Fast.invert invEnv := by
  have h : ISpec base _ _ :=
    (opsI base [.copy 12 2] (by simp [MulCopy])).seq <| (call_spec base).seq <|
      (sqnI base 21 (n := 2) (by decide) (by decide)).seq
        (VG.Proof.Ed448.AArch64.Point56.mulCallKI base 21 21 2 (by decide))
  exact h

theorem invEnv_eq (e : Env) :
    invEnv e = opMul 21 21 2 (opSqn 21 2 (rootEnv (opCopy 12 2 e))) := rfl

theorem invEnv_eval (e : Env) : invEnv e 21 = Proof.X448.invert (e 2) := by
  have h2 : rootEnv (opCopy 12 2 e) 2 = e 2 := by
    rw [rootEnv_keep _ 2 (by decide)]; rfl
  have h21 : rootEnv (opCopy 12 2 e) 21 = Proof.Ed448.rootPow (e 2) := by
    rw [rootEnv_eval]; rfl
  rw [invEnv_eq]
  simp only [opMul, opSqn, Function.update_self, Function.update_of_ne (show (2 : Index) ≠ 21 by decide),
    h2, h21]
  exact invert_rootPow (e 2)

theorem invEnv_keep (e : Env) (i : Index) (hi : i.val < 12) : invEnv e i = e i := by
  have h12 : i ≠ 12 := fun h => absurd hi (by rw [h]; decide)
  have h21 : i ≠ 21 := fun h => absurd hi (by rw [h]; decide)
  rw [invEnv_eq]
  simp only [opMul, opSqn, opCopy, Function.update_of_ne h21, rootEnv_keep _ i (by omega_using [hi]),
    Function.update_of_ne h12]

theorem invEnv_x2 (e : Env) : invEnv e 1 = e 1 := invEnv_keep e 1 (by decide)

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa Impl.X448.AArch64.Fast.invert s fun t =>
      IKeep base s t ∧ BEnv t.mem base ∧ EV t.mem base = invEnv (EV s.mem base) :=
  invert_spec base s hs hb

end VG.Proof.X448.AArch64.Fast

end

end

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
    exact tO.limbs (Or.inl (by simp only [slot]; omega_using [hS])) (by simp only [slot]; omega_using []) (by omega_using [hj])
  have sm : Same base [] u.mem t.mem := fun i _ j hj => sl i j hj
  have red : ∀ i : Index, Bnd Mb t.mem base (slot i.val) := fun i => sm.bnd (by simp) (weak_bnd (ub i))
  have ug : ∀ r, t.gpr r = u.gpr r := fun r => by rw [tg]
  refine ⟨⟨(ug _).trans us.x3, (ug _).trans us.mask, tw ▸ us.wr, us.nowrap⟩,
    fun i j hj => Nat.lt_of_lt_of_le (red i j hj) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib, red, (ug _).trans ux,
    ⟨fun r hr => (ug r).trans (uk.1 r hr), tr.trans uk.2.1, tw.trans uk.2.2⟩,
    um.trans ?_, uv.outside tO (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact tO x (by simp only [SAVE]; omega_using [hx])
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
    exact tO.limbs (Or.inl (by simp only [slot]; omega_using [hV])) (by simp only [slot]; omega_using []) (by omega_using [hj])
  have sm : Same base [] u.mem t.mem := fun i _ j hj => sl i j hj
  refine ⟨VG.Proof.Curve448.AArch64.Neon.scr_of us tg tw, fun i => sm.bnd (by simp) (ub i), fun i => sm.bnd (by simp) (red i), tg ▸ ux,
    ⟨fun r hr => (congrFun tg r).trans (uk.1 r hr), tr.trans uk.2.1, tw.trans uk.2.2⟩,
    uo.trans fun x hx => tO x (by omega_using [hV, hx]), sv.outside tO (by decide), svx.outside tO (by decide),
    by rw [sm.env (by simp)]; exact u0, by rw [sm.env (by simp)]; exact u1, by rw [sm.env (by simp)]; exact u2,
    by rw [sm.env (by simp), sm.env (by simp)]; exact u3, by rw [sm.env (by simp)]; exact u4,
    by rw [tO.word (Or.inl (by decide)) (by decide)]; exact uw, fun k hk => ?_⟩
  rw [tv k hk]
  exact uv _ (by rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega_using [hk])
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

end VG.Proof.X448.AArch64.Fast
