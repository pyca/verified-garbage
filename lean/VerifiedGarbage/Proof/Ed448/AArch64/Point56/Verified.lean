module

public import VerifiedGarbage.Proof.Ed448.Point56Contract
public import VerifiedGarbage.Proof.X448.Field56Contract
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
meta import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Curve448.AArch64.AccumSquareBody
meta import VerifiedGarbage.Proof.Curve448.AArch64.AddEval
meta import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
meta import VerifiedGarbage.Proof.Curve448.AArch64.Collect
meta import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Butterfly
meta import VerifiedGarbage.Proof.Curve448.AArch64.Fast.ColEnd
meta import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sqr
meta import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
meta import VerifiedGarbage.Proof.Curve448.AArch64.Product
meta import VerifiedGarbage.Proof.Curve448.AArch64.Stage
meta import VerifiedGarbage.Proof.Curve448.AArch64.SymmetricColumn
meta import VerifiedGarbage.Proof.Ed448.Scalar
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.AArch64.AddSub
meta import VerifiedGarbage.Proof.X448.AArch64.Carry
meta import VerifiedGarbage.Proof.X448.AArch64.Columns
meta import VerifiedGarbage.Proof.X448.AArch64.Copy
meta import VerifiedGarbage.Proof.X448.AArch64.Init
meta import VerifiedGarbage.Proof.X448.AArch64.Normalize
meta import VerifiedGarbage.Proof.X448.AArch64.PointwiseFused
meta import VerifiedGarbage.Proof.X448.AArch64.Row
meta import VerifiedGarbage.Proof.X448.AArch64.Small
meta import VerifiedGarbage.Proof.X448.AArch64.Step
meta import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.X448.Wide.AccumSquareBody
meta import VerifiedGarbage.Proof.X448.Wide.AddCoefficient
meta import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
meta import VerifiedGarbage.Proof.X448.Wide.Columns
meta import VerifiedGarbage.Proof.X448.Wide.Fold
meta import VerifiedGarbage.Proof.X448.Wide.LoadCached
meta import VerifiedGarbage.Proof.X448.Wide.Mul
meta import VerifiedGarbage.Proof.X448.Wide.Normalize
meta import VerifiedGarbage.Proof.X448.Wide.Pack
meta import VerifiedGarbage.Proof.X448.Wide.Pass
meta import VerifiedGarbage.Proof.X448.Wide.PassInit
meta import VerifiedGarbage.Proof.X448.Wide.Reduce
meta import VerifiedGarbage.Proof.X448.Wide.SymmetricColumn
meta import VerifiedGarbage.Proof.X448.Wide.TailMul
meta import VerifiedGarbage.Proof.X448.Wide.TailSquare
meta import VerifiedGarbage.Proof.X448.Wide.TailStep
meta import VerifiedGarbage.Proof.X448.Wide.Term
meta import VerifiedGarbage.Proof.X448.Wide.UnpackRegs
meta import VerifiedGarbage.Proof.X448.BaseAdd
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Body
meta import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Body
public import Init.Data.BitVec.BasicAux
meta import Init.Data.BitVec.BasicAux
public import Init.Data.Fin.Basic
meta import Init.Data.Fin.Basic
public import Init.Data.List.Basic
meta import Init.Data.List.Basic
public import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Conv
meta import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Conv

/-!
# `vg_ed448_r56_point_add`, `vg_ed448_r56_point_double` and `vg_gf448_r56_pow_p34` on AArch64, verified

Each function meets its contract of `Proof/Ed448/Point56Contract.lean` or
`Proof/X448/Field56Contract.lean`, with no stack: the proof against `addF` (`doubleF`,
`powF`), the contract's facts by register, from `addFn_ok` (`doubleFn_ok`,
`powFn_ok`). The elements as the contracts read them are the proofs'
(`Conv.lean`); the results are `addPt` (`pointAdd`), `double` (`pointDouble`)
and `rootPow` (`pow` to `(p - 3) / 4`); the bytes kept are those no store
covers (`keeps_of_unstored`). The callee-saved registers are restored (`FnPost`)
and no instruction writes `v8`–`v15`. Constant time by taint tracking: only the
pointer, in `x0`, is public, and every address is `ws` plus a constant.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd fclob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genEnv genPt)
open VG.Proof.Ed448.AArch64.Window (dblEnv dblEnv_345 dblPt_eq)
open VG.Proof.X448.Field56 (slotAt elemAt Bounded Res)
open VG.Proof.Ed448.Point56 (pointAt ResPoint pointDouble written)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The working space's facts: `ws` in `x0`, its 8192 bytes the only region. -/
def fPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 8192⟩] ∧ (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64

/-- What two runs agree on: the pointer and the stack pointer. -/
def fPub (s₁ s₂ : State) : Prop := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

def addF : Contract AArch64.isa where
  pre s := fPre s ∧ Bounded s.mem (s.gpr .x0) ∧ Res s.mem (s.gpr .x0) 19 ∧
    elemAt s.mem (s.gpr .x0) (slotAt 19) = 0
  post s s' := Bounded s'.mem (s.gpr .x0) ∧ ResPoint s'.mem (s.gpr .x0) ∧
    pointAt s'.mem (s.gpr .x0) 3 = Spec.Ed448.pointAdd (pointAt s.mem (s.gpr .x0) 3) (pointAt s.mem (s.gpr .x0) 6) ∧
    Proof.X448.Field56.Keeps (s.gpr .x0) written s.mem s'.mem
  pub := fPub

def doubleF : Contract AArch64.isa where
  pre s := fPre s ∧ Bounded s.mem (s.gpr .x0) ∧ Res s.mem (s.gpr .x0) 5 ∧
    elemAt s.mem (s.gpr .x0) (slotAt 20) = 1
  post s s' := Bounded s'.mem (s.gpr .x0) ∧ ResPoint s'.mem (s.gpr .x0) ∧
    pointAt s'.mem (s.gpr .x0) 3 = pointDouble (pointAt s.mem (s.gpr .x0) 3) ∧
    Proof.X448.Field56.Keeps (s.gpr .x0) written s.mem s'.mem
  pub := fPub

def powF : Contract AArch64.isa where
  pre s := fPre s ∧ Bounded s.mem (s.gpr .x0)
  post s s' := Bounded s'.mem (s.gpr .x0) ∧
    elemAt s'.mem (s.gpr .x0) (slotAt 21) = Spec.X448.pow (elemAt s.mem (s.gpr .x0) (slotAt 12)) ((Spec.X448.P - 3) / 4) ∧
    Proof.X448.Field56.Keeps (s.gpr .x0) (Proof.X448.Field56.powSlots :: Proof.X448.Field56.own) s.mem s'.mem
  pub := fPub

theorem fnPre_of {s : State} (h : fPre s) (hb : Bounded s.mem (s.gpr .x0)) : FnPre s :=
  ⟨by rw [h.2.1]; exact List.mem_singleton_self _, h.2.2, (bounded_iff _ _).mp hb⟩

theorem pointAt_eq (m : Mem) (ws : Addr) : pointAt m ws 3 = pt (EV m ws) 3 4 5 := by
  simp only [pointAt, pt]
  rw [show (3 + 1 : Nat) = (4 : Index).val from rfl, show (3 + 2 : Nat) = (5 : Index).val from rfl,
    show (3 : Nat) = (3 : Index).val from rfl, elemAt_eq, elemAt_eq, elemAt_eq]

theorem pointAt_eq6 (m : Mem) (ws : Addr) : pointAt m ws 6 = pt (EV m ws) 6 7 8 := by
  simp only [pointAt, pt]
  rw [show (6 + 1 : Nat) = (7 : Index).val from rfl, show (6 + 2 : Nat) = (8 : Index).val from rfl,
    show (6 : Nat) = (6 : Index).val from rfl, elemAt_eq, elemAt_eq, elemAt_eq]

theorem dblOk_written : ∀ d, dblOk d = true → d + 8 ≤ 8192 ∧ ∃ r ∈ written, r.1 ≤ d ∧ d + 8 ≤ r.2 := by
  intro d hd
  simp only [dblOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd
  simp only [written, Proof.X448.Field56.own, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, slotAt, Proof.Ed448.Point56.pSlot, Proof.X448.Field56.accAt,
    Proof.X448.Field56.accEnd]
  omega

/-- `Field56.Keeps` of the power's slots and the products' coefficients, from the bytes kept
outside them. -/
theorem keeps_of_outside2 {ws : Addr} {m m' : Mem}
    (h : VG.Proof.X448.AArch64.Outside2 ws 1856 1024 VG.Impl.X448.AArch64.ACC 1152 m m') :
    Proof.X448.Field56.Keeps ws (Proof.X448.Field56.powSlots :: Proof.X448.Field56.own) m m' := by
  intro i hi hr
  have h1 := hr _ List.mem_cons_self
  have h2 := hr _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hW : Proof.X448.Field56.wsBytes = 8192 := rfl
  simp only [Proof.X448.Field56.powSlots, slotAt] at h1
  simp only [Proof.X448.Field56.accAt, Proof.X448.Field56.accEnd] at h2
  rw [hW] at hi
  have ho : VG.Proof.X448.AArch64.ofs ws (ws + BitVec.ofNat 64 i) = i := by
    have := VG.Proof.X448.AArch64.ofs_off ws (d := 0) (i := i) (by omega)
    simp only [VG.Proof.X448.AArch64.off, BitVec.add_zero, Nat.zero_add] at this
    exact this
  exact h _ (by rw [ho]; omega) (by rw [ho]; simp only [VG.Impl.X448.AArch64.ACC]; omega)

theorem abi_of {c : Bool} {rs : List Reg} {s u : State} {Q : Mem → Prop} (h : FnPost c rs s u Q)
    (hr : ∀ r ∈ preserved, (r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst) ∧ r ≠ .x3 ∧ r ≠ .x12) :
    (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ u.sp = s.sp :=
  ⟨fun r hp => h.1 r (hr r hp).1 (hr r hp).2.1 (hr r hp).2.2, h.2.2.2.2.2.1⟩

theorem resPoint_of {m : Mem} {ws : Addr} (h3 : Bnd Mb m ws (slot 3)) (h4 : Bnd Mb m ws (slot 4))
    (h5 : Bnd Mb m ws (slot 5)) : ResPoint m ws := ⟨h3, h4, h5⟩

theorem add_arm (s : State) (hs : addF.pre s) :
    ∃ t s', Exec isa Point56.addFn s t s' ∧ abiPreserved s s' ∧ addF.post s s' := by
  obtain ⟨hp, hb, hr, hz⟩ := hs
  have hz' : EV s.mem (s.gpr .x0) 19 = 0 := by rw [← hz]; exact (elemAt_eq _ _ 19).symm
  obtain ⟨t, u, he, hpost, hv⟩ := WP.preservedV (addFn_ok (fnPre_of hp hb) hr) addFn_keepsV
  obtain ⟨b, -, b3, b4, b5, e, hf⟩ := hpost.2.2.2.2.2.2
  obtain ⟨hg, hsp⟩ := abi_of hpost (by decide)
  refine ⟨t, u, he, ⟨hg, hsp, hv⟩, (bounded_iff _ _).mpr b, ⟨b3, b4, b5⟩, ?_,
    keeps_of_unstored dblOk_written hf⟩
  rw [pointAt_eq, pointAt_eq, pointAt_eq6, e, genEnv_pt, hz',
    VG.Proof.X448.AArch64.Base.genPt_eq, VG.Proof.X448.addPt_eq]

theorem double_eq (p : Spec.Ed448.Point) : VG.Proof.Ed448.double p = pointDouble p := rfl

theorem double_arm (s : State) (hs : doubleF.pre s) :
    ∃ t s', Exec isa Point56.doubleFn s t s' ∧ abiPreserved s s' ∧ doubleF.post s s' := by
  obtain ⟨hp, hb, hr, h1⟩ := hs
  have h1' : EV s.mem (s.gpr .x0) 20 = 1 := by rw [← h1]; exact (elemAt_eq _ _ 20).symm
  obtain ⟨t, u, he, hpost, hv⟩ := WP.preservedV (doubleFn_ok (fnPre_of hp hb) hr) doubleFn_keepsV
  obtain ⟨b, -, b3, b4, b5, e, hf⟩ := hpost.2.2.2.2.2.2
  obtain ⟨hg, hsp⟩ := abi_of hpost (by decide)
  refine ⟨t, u, he, ⟨hg, hsp, hv⟩, (bounded_iff _ _).mpr b, ⟨b3, b4, b5⟩, ?_,
    keeps_of_unstored dblOk_written hf⟩
  rw [pointAt_eq, pointAt_eq, e, dblEnv_345, h1', dblPt_eq, double_eq]

theorem pow_arm (s : State) (hs : powF.pre s) :
    ∃ t s', Exec isa Point56.powFn s t s' ∧ abiPreserved s s' ∧ powF.post s s' := by
  obtain ⟨hp, hb⟩ := hs
  obtain ⟨t, u, he, hpost, hv⟩ := WP.preservedV (powFn_ok (fnPre_of hp hb)) powFn_keepsV
  obtain ⟨b, e, hf⟩ := hpost.2.2.2.2.2.2
  obtain ⟨hg, hsp⟩ := abi_of hpost (by decide)
  refine ⟨t, u, he, ⟨hg, hsp, hv⟩, (bounded_iff _ _).mpr b, ?_, keeps_of_outside2 hf⟩
  rw [show (21 : Nat) = (21 : Index).val from rfl, show (12 : Nat) = (12 : Index).val from rfl,
    elemAt_eq, elemAt_eq, e, rootEnv_eval, VG.Proof.Ed448.rootPow_eq]

/-! ## Constant time -/

theorem add_ct : ConstantTime isa addF.pre addF.pub Point56.addFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ hp => ⟨hp.2, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.1⟩) (by taint_decide)

theorem double_ct : ConstantTime isa doubleF.pre doubleF.pub Point56.doubleFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ hp => ⟨hp.2, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.1⟩) (by taint_decide)

theorem pow_ct : ConstantTime isa powF.pre powF.pub Point56.powFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ hp => ⟨hp.2, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.1⟩) (by taint_decide)

/-! ## The shared contracts -/

/-- The memory of `satState`: 1 in slot 20 of the working space at `0x1000`, and zeros
elsewhere. -/
def satMem : Mem := fun a => if a = 0x1000 + 2624 then 1 else 0

/-- A state satisfying the preconditions: `ws` at `0x1000`, every element 0 but 1 in slot 20,
and the stack at `0x10000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_bounded : Bounded satMem 0x1000 := by
  unfold Bounded; decide +kernel

theorem sat_res (n : Nat) (hn : n < 22) : Res satMem 0x1000 n := by
  revert n; unfold Res; decide +kernel

theorem sat_zero : elemAt satMem 0x1000 (slotAt 19) = 0 := by decide +kernel

theorem sat_one : elemAt satMem 0x1000 (slotAt 20) = 1 := by decide +kernel

theorem addFn_verified :
    Verified AArch64.target Point56.addFn (Proof.Ed448.Point56.addContract AArch64.abi) :=
  Verified.of_correct add_arm add_ct
    { pre := by sig_implies_pre [Proof.Ed448.Point56.addContract, Proof.Ed448.Point56.sig, Proof.Ed448.Point56.zeroSlot, Proof.Ed448.Point56.oneSlot,
        Proof.Ed448.Point56.pSlot, Proof.Ed448.Point56.qSlot, addF, fPre, fPub,
        AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.Ed448.Point56.addContract, Proof.Ed448.Point56.sig, Proof.Ed448.Point56.zeroSlot, Proof.Ed448.Point56.oneSlot,
        Proof.Ed448.Point56.pSlot, Proof.Ed448.Point56.qSlot, addF, fPre, fPub, AArch64.abi,
          AArch64.argRegs]
        exact h
      pub := by sig_implies_pub [Proof.Ed448.Point56.addContract, Proof.Ed448.Point56.sig, Proof.Ed448.Point56.zeroSlot, Proof.Ed448.Point56.oneSlot,
        Proof.Ed448.Point56.pSlot, Proof.Ed448.Point56.qSlot, addF, fPre, fPub,
        AArch64.abi, AArch64.argRegs]
      sat := ⟨satState, by
        unfold Proof.Ed448.Point56.addContract
        exact Sig.contract_pre_of_check (by decide +kernel) (by
          sig_reduce [Sig.wfPre, Proof.Ed448.Point56.sig, Proof.Ed448.Point56.zeroSlot, Proof.Ed448.Point56.oneSlot,
        Proof.Ed448.Point56.pSlot, Proof.Ed448.Point56.qSlot, AArch64.abi, AArch64.argRegs, satState]
          exact ⟨by decide, sat_bounded, sat_res 19 (by decide), sat_zero⟩)⟩ }

theorem doubleFn_verified :
    Verified AArch64.target Point56.doubleFn (Proof.Ed448.Point56.doubleContract AArch64.abi) :=
  Verified.of_correct double_arm double_ct
    { pre := by sig_implies_pre [Proof.Ed448.Point56.doubleContract, Proof.Ed448.Point56.sig, Proof.Ed448.Point56.zeroSlot, Proof.Ed448.Point56.oneSlot,
        Proof.Ed448.Point56.pSlot, Proof.Ed448.Point56.qSlot, doubleF, fPre,
        fPub, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.Ed448.Point56.doubleContract, Proof.Ed448.Point56.sig, Proof.Ed448.Point56.zeroSlot, Proof.Ed448.Point56.oneSlot,
        Proof.Ed448.Point56.pSlot, Proof.Ed448.Point56.qSlot, doubleF, fPre, fPub, AArch64.abi,
          AArch64.argRegs]
        exact h
      pub := by sig_implies_pub [Proof.Ed448.Point56.doubleContract, Proof.Ed448.Point56.sig, Proof.Ed448.Point56.zeroSlot, Proof.Ed448.Point56.oneSlot,
        Proof.Ed448.Point56.pSlot, Proof.Ed448.Point56.qSlot, doubleF, fPre,
        fPub, AArch64.abi, AArch64.argRegs]
      sat := ⟨satState, by
        unfold Proof.Ed448.Point56.doubleContract
        exact Sig.contract_pre_of_check (by decide +kernel) (by
          sig_reduce [Sig.wfPre, Proof.Ed448.Point56.sig, Proof.Ed448.Point56.zeroSlot, Proof.Ed448.Point56.oneSlot,
        Proof.Ed448.Point56.pSlot, Proof.Ed448.Point56.qSlot, AArch64.abi, AArch64.argRegs, satState]
          exact ⟨by decide, sat_bounded, sat_res 5 (by decide), sat_one⟩)⟩ }

theorem powFn_verified :
    Verified AArch64.target Point56.powFn (Proof.X448.Field56.powContract AArch64.abi) :=
  Verified.of_correct pow_arm pow_ct
    { pre := by sig_implies_pre [Proof.X448.Field56.powContract, Proof.X448.Field56.sig, powF, fPre, fPub,
        AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [Proof.X448.Field56.powContract, Proof.X448.Field56.sig, powF, fPre, fPub,
        AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [Proof.X448.Field56.powContract, Proof.X448.Field56.sig, powF, fPre, fPub,
        AArch64.abi, AArch64.argRegs]
      sat := ⟨satState, by
        unfold Proof.X448.Field56.powContract
        exact Sig.contract_pre_of_check (by decide +kernel) (by
          sig_reduce [Sig.wfPre, Proof.X448.Field56.sig, AArch64.abi, AArch64.argRegs, satState]
          exact ⟨by decide, sat_bounded⟩)⟩ }

end VG.Proof.Ed448.AArch64.Point56
