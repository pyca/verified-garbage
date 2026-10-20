module

import VerifiedGarbage.Proof.Ed448.AArch64.Point56.AsFn
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Conv
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Dbl
public import VerifiedGarbage.Proof.Ed448.AArch64.VerifyRoot
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Lit
meta import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Lit
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.X448.AArch64.Field56
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Env

/-!
# Ed448 on AArch64: what the functions compute

Untrusted: everything here is checked by Lean. From `ws` in `x0`, with every
slot's limbs below `Ib` (`BEnv`): `vg_ed448_r56_point_double` doubles slots
3–5 (`doubleFn_ok`, by `dblOps_ok`), `vg_ed448_r56_point_add` adds slots 6–8
to them (`addFn_ok`, by `addOps_ok`), and `vg_gf448_r56_pow_p34` writes
`rootPow` of slot 12 to slot 21 (`powFn_ok`, by `root_spec`), as functions
(`asFn_ok`). Each stores only to the slots it writes and the products'
coefficients (`dblOk`, by `Exec.storeFrame`; the power, whose products are calls of
`vg_gf448_r56_mul`, by `root_spec`), and leaves `ws` in `x3` and the mask in `x12`.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Outside2)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same fclob ISpec IKeep)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genEnv genPt temps addOps_ok zero_env)
open VG.Proof.Ed448.AArch64.Window (dblOps_ok dblEnv dblEnv_345 dblPt_eq)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- Where doubling and addition store: slots 3–5 and 10–18, and the products' coefficients. -/
def dblOk (d : Nat) : Bool :=
  (448 ≤ d && d + 8 ≤ 832) || (1344 ≤ d && d + 8 ≤ 2496) || (3584 ≤ d && d + 8 ≤ 4736)

/-- What the functions start from: `ws` in `x0`, writable for its 8192 bytes, without wrapping,
and every slot's limbs below `Ib`. -/
structure FnPre (s : State) : Prop where
  wr : (⟨s.gpr .x0, 8192⟩ : Region) ∈ s.wr
  nowrap : (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64
  env : BEnv s.mem (s.gpr .x0)

/-- What the functions end in, from `s`, with `Q` of the memory: every register outside `rs` or
kept restored, but `x3` (`ws`) and `x12` (the mask). -/
abbrev FnPost (c : Bool) (rs : List Reg) (s u : State) (Q : Mem → Prop) : Prop :=
  (∀ r, (r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst) → r ≠ .x3 → r ≠ .x12 → u.gpr r = s.gpr r) ∧
    u.gpr .x3 = s.gpr .x0 ∧ u.gpr .x12 = 0x0fffffff ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
    Q u.mem

theorem scr_of {s s₁ : State} (h : FnPre s) (h3 : s₁.gpr .x3 = s.gpr .x0) (h12 : s₁.gpr .x12 = 0x0fffffff)
    (hw : s₁.wr = s.wr) : Scr s₁ (s.gpr .x0) :=
  ⟨h3, h12, by rw [hw]; exact h.wr, h.nowrap⟩

theorem dblStores : ∀ i ∈ instrs (Impl.X448.AArch64.Fast.ops (dblOps (slot 3) (slot 4) (slot 5))),
    storesAt dblOk i = true := by
  rw [← List.all_eq_true, ← Code.allInstrs_eq]; lit_decide

theorem addStores : ∀ i ∈ instrs (Impl.X448.AArch64.Fast.ops
    (Impl.X448.AArch64.Base.addOps (slot 3) (slot 4) (slot 5) (slot 6) (slot 7) (slot 8))),
    storesAt dblOk i = true := by
  rw [← List.all_eq_true, ← Code.allInstrs_eq]; lit_decide

/-- The memory doubling and addition leave, from `m`, the slots 3–5 being `f` of the environment. -/
abbrev PtMem (base : Addr) (f : Env → Env) (m m' : Mem) : Prop :=
  BEnv m' base ∧ Same base (temps ++ [3, 4, 5]) m m' ∧ Bnd Mb m' base (slot 3) ∧ Bnd Mb m' base (slot 4) ∧
    Bnd Mb m' base (slot 5) ∧ EV m' base = f (EV m base) ∧ ∀ a, Unstored dblOk base a → m' a = m a

/-- The memory the power leaves, from `m`: every byte outside slots 14–21 and the products'
coefficients kept. -/
abbrev PowMem (base : Addr) (m m' : Mem) : Prop :=
  BEnv m' base ∧ EV m' base = rootEnv (EV m base) ∧ Outside2 base 1856 1024 ACC 1152 m m'

/-- No instruction of the functions writes `v8`–`v15`. -/
theorem addFn_keepsV : Point56.addFn.allInstrs keepsV = true := by lit_decide
theorem doubleFn_keepsV : Point56.doubleFn.allInstrs keepsV = true := by lit_decide
theorem powFn_keepsV : Point56.powFn.allInstrs keepsV = true := by lit_decide

/-- **Doubling** slots 3–5, as a function. -/
theorem doubleFn_ok {s : State} (h : FnPre s) (hz : Bnd Mb s.mem (s.gpr .x0) (slot 5)) :
    WP isa Point56.doubleFn s fun u => FnPost false fclob s u (PtMem (s.gpr .x0) (dblEnv 3 4 5) s.mem) := by
  unfold Point56.doubleFn FnPost
  refine asFn_ok (rs := fclob) (Q := PtMem (s.gpr .x0) (dblEnv 3 4 5) s.mem) (by decide) (by decide) ?hv fun s₁ h3 h12 _ hm _ hw => ?_
  case hv => lit_decide
  obtain ⟨tr, t, he, k, b, sm, b3, b4, b5, e⟩ := dblOps_ok 3 4 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (scr_of h h3 h12 hw) (hm ▸ h.env) (hm ▸ hz)
  obtain ⟨-, hf⟩ := Exec.storeFrame dblStores he
  refine ⟨tr, t, he, k.regs.1, k.regs.2.1, k.regs.2.2, b, hm ▸ sm, b3, b4, b5, hm ▸ e, fun a ha => ?_⟩
  rw [← hm]; exact hf a (by rw [h3]; exact ha)

/-- **Addition** of slots 6–8 to slots 3–5, as a function. -/
theorem addFn_ok {s : State} (h : FnPre s) (hz : Bnd Mb s.mem (s.gpr .x0) (slot 19)) :
    WP isa Point56.addFn s fun u => FnPost false fclob s u (PtMem (s.gpr .x0) (genEnv 3 4 5 6 7 8) s.mem) := by
  unfold Point56.addFn FnPost
  refine asFn_ok (rs := fclob) (Q := PtMem (s.gpr .x0) (genEnv 3 4 5 6 7 8) s.mem) (by decide) (by decide) ?hv fun s₁ h3 h12 _ hm _ hw => ?_
  case hv => lit_decide
  obtain ⟨tr, t, he, k, b, sm, b3, b4, b5, e⟩ := addOps_ok 3 4 5 6 7 8 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (scr_of h h3 h12 hw) (hm ▸ h.env) (hm ▸ hz)
  obtain ⟨-, hf⟩ := Exec.storeFrame addStores he
  refine ⟨tr, t, he, k.regs.1, k.regs.2.1, k.regs.2.2, b, hm ▸ sm, b3, b4, b5, hm ▸ e, fun a ha => ?_⟩
  rw [← hm]; exact hf a (by rw [h3]; exact ha)

/-- **The square root's power**, slot 12 to slot 21, as a function. -/
theorem powFn_ok {s : State} (h : FnPre s) :
    WP isa Point56.powFn s fun u => FnPost true Point56.pclob s u (PowMem (s.gpr .x0) s.mem) := by
  unfold Point56.powFn FnPost
  refine asFn_ok (rs := Point56.pclob) (Q := PowMem (s.gpr .x0) s.mem) (by decide) (by decide) ?hv
    fun s₁ h3 h12 _ hm _ hw => ?_
  case hv => lit_decide
  obtain ⟨tr, t, he, k, b, e, f⟩ := root_spec (s.gpr .x0) s₁ (scr_of h h3 h12 hw) (hm ▸ h.env)
  exact ⟨tr, t, he, k.1, k.2.1, k.2.2, b, hm ▸ e, hm ▸ f⟩

end VG.Proof.Ed448.AArch64.Point56
