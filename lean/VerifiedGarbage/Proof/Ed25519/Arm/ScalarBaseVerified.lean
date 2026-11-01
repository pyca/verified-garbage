module

public import VerifiedGarbage.Proof.Ed25519.Contract
public import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
meta import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.Arm.CombLoop
meta import VerifiedGarbage.Proof.Ed25519.Arm.CombLoop
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
meta import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom
public import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarFinish
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarFinish
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Ed25519.Arm.PointKeep
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Ed25519.Arm.LrSlot
meta import VerifiedGarbage.Proof.Ed25519.Arm.LrSlot
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Ed25519.Arm.Points
meta import VerifiedGarbage.Proof.Ed25519.Arm.Points
import VerifiedGarbage.Proof.Ed25519.Arm.PackField
meta import VerifiedGarbage.Proof.Ed25519.Arm.PackField
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Ed25519.Arm.PointMulBody
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTBody
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.X25519.Arm.Cswap
meta import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
meta import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
meta import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointMulBody
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTBody
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.Arm.AddSub
meta import VerifiedGarbage.Proof.X25519.Arm.Cswap
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointKeep
meta import VerifiedGarbage.Proof.Framework.Contract

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseEngine`. -/

@[expose] public section

section
/-! All input scalar bits, exact point multiplication, and canonical encoding compose. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def encodedValue (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val +
    ((p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val % 2) * 2 ^ 255

theorem encodedValue_spec (p : Spec.Ed25519.Point) :
    Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (encodedValue p) := rfl

theorem scalarBaseEngine_ok {s : State} {base ptr T : BitVec 32} (hc : Ctx base s)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa scalarBaseEngine s fun t => PointKeep base s t ∧ Lim t.mem (State.addr base) FR ∧
      V t.mem (State.addr base) FR = encodedValue
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32)) Spec.Ed25519.basePoint) := by
  have fa : (FA base).Sub ⟨State.addr base, 8192⟩ := Offset.sub_base _ (by decide)
  refine WP.seq (WP.mono_syms (initFields_rest hc) fun a ⟨ak, ar, al, _⟩ sya => ?_)
  have hca := ak.ctx hc
  have up : a.gpr .r12 = ptr := (ar.gpr _ (by decide)).trans hp
  have ur : ∀ i < 32, InRegions (a.rd ++ a.wr) (State.addr ptr + BitVec.ofNat 64 i) 1 := by
    rw [ak.rest.rd, ak.rest.wr]; exact hr
  have uv : Spec.Ed25519.bytesAt a.mem (State.addr ptr) 32 = Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 := by
    unfold Spec.Ed25519.bytesAt
    exact List.map_congr_left fun n hn => ak.frame.bytes (R := ⟨State.addr ptr, 32⟩)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hsep.sub_right fa)
      (show (32 : Nat) ≤ 2 ^ 64 by decide) (List.mem_range.mp hn)
  have hTa : TblAt a T := hT.of_frame (by rw [ak.rest.rd, ak.rest.wr]) ak.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right fa
  rw [WP.seq_iff]
  refine WP.mono (combMultiply_ok hca al up hfit ur hsep hTa (by rw [sya]; exact hsym) apart)
    fun v ⟨vk, vl, vrep⟩ => ?_
  refine WP.mono (pointEncode_ok (vk.ctx hca) vl) fun t ⟨tk, tl, tv⟩ => ?_
  refine ⟨(PointKeep.of_keep ak).trans (vk.trans (PointKeep.of_ikeep tk)), tl, ?_⟩
  change V t.mem (State.addr base) FR = encodedValue (point (env v.mem base) 0 1 2 3) at tv
  rw [tv, ← uv]
  have hm := pointMul_rep (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem (State.addr ptr) 32))
    basePoint_rep
  unfold encodedValue
  rw [vrep.affine_x, vrep.affine_y, hm.affine_x, hm.affine_y]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCTEngine`. -/
section
/-! Initialization, secret scalar multiplication, and encoding have public traces. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BaseCTPre (b p T : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ s.gpr .r12 = p ∧ p.toNat + 32 ≤ 2 ^ 32 ∧
    (∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩ ∧
    TblAt s T ∧ s.syms combSym = T ∧ (TBL T).Disjoint ⟨State.addr b, 8192⟩

/-- What the comb needs, in each run. -/
def CombCTPre (b p T : BitVec 32) (s : State) : Prop := BaseCTPre b p T s ∧ AllLim s.mem b

/-- Each run's loop state, from its own start. -/
def CombRun (b T : BitVec 32) (j : Nat) (s : State) : Prop :=
  ∃ s₀ p S, CombEnv s₀ b p T ∧ CombInv s₀ b p T S j s

/-- A step's result, in each run. -/
def StepPost (b T : BitVec 32) (j : Nat) (t : State) : Prop :=
  isa.eval .ne t = some (decide (j + 1 ≠ 64)) ∧ CombRun b T (j + 1) t

def initFieldsCT : Prog isa := .block initFields

materialize_code initFieldsCT
materialize_code combPrepare
materialize_code combStep

/-- A step from public `r0`, counter `r11` and table address: the digits only reach masks. -/
theorem combStep_ct (b T : BitVec 32) (j : Nat) :
    CT (fun x y => CombRun b T j x ∧ CombRun b T j y) combStep (fun _ _ => True) := by
  apply RelCT.taint (A := taintSym [combSym]) (Taint.ofRegs [.r0, .r11]) _ (by native_taint_decide)
  rintro x y ⟨⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩
  refine ⟨Taint.agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.ctx.r0.trans hy.ctx.r0.symm
    · exact hx.r11.trans hy.r11.symm
  · rw [List.mem_singleton.mp hn, hx.syms, hy.syms]

theorem combLoop_ct (b T : BitVec 32) :
    CT (fun x y => CombRun b T 0 x ∧ CombRun b T 0 y) (.loop combStep .ne)
      (fun x y => Ctx b x ∧ Ctx b y) := by
  refine (RelCT.loop (M := isa) (Q := fun x y => Ctx b x ∧ Ctx b y)
    (fun n x y => 0 < n ∧ n ≤ 64 ∧ CombRun b T (64 - n) x ∧ CombRun b T (64 - n) y)
    (fun n => ?_) 64).mono (fun x y h => ⟨by decide, le_rfl, by simpa using h⟩) fun _ _ h => h
  by_cases hn : 0 < n ∧ n ≤ 64
  · have step : ∀ x, CombRun b T (64 - n) x → WP isa combStep x (StepPost b T (64 - n)) :=
      fun x ⟨s₀, p, S, E, h⟩ => WP.mono (combStep_ok E h (by omega)) fun t ⟨e, h'⟩ => ⟨e, s₀, p, S, E, h'⟩
    refine ((combStep_ct b T (64 - n)).wp (F₁ := StepPost b T (64 - n)) (F₂ := StepPost b T (64 - n))
      (fun x y h => ⟨step x h.1, step y h.2⟩)).mono
      (fun x y h => ⟨h.2.2.1, h.2.2.2⟩) fun u v h => ?_
    obtain ⟨-, ⟨eu, ru⟩, ⟨ev, rv⟩⟩ := h
    refine ⟨by rw [eu, ev], fun _ => ?_, fun ht => ?_⟩
    · obtain ⟨_, _, _, _, hu⟩ := ru
      obtain ⟨_, _, _, _, hv⟩ := rv
      exact ⟨hu.ctx, hv.ctx⟩
    · rw [eu] at ht
      have hn1 : 64 - n + 1 ≠ 64 := by simpa using ht
      refine ⟨n - 1, by omega, by omega, by omega, ?_, ?_⟩
      · rw [show 64 - (n - 1) = 64 - n + 1 by omega]; exact ru
      · rw [show 64 - (n - 1) = 64 - n + 1 by omega]; exact rv
  · exact RelCT.of_false fun x y h => hn ⟨h.1, h.2.1⟩

theorem combMultiply_ct (b p T : BitVec 32) :
    CT (fun x y => CombCTPre b p T x ∧ CombCTPre b p T y) combMultiply
      (fun x y => Ctx b x ∧ Ctx b y) := by
  have hp : CT (fun x y => CombCTPre b p T x ∧ CombCTPre b p T y) combPrepare
      (fun x y => CombRun b T 0 x ∧ CombRun b T 0 y) := by
    apply ctBoth
    · apply ctRegs [.r0, .r12] _ (by native_taint_decide)
      intro x y h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.1.r0.trans h.2.1.1.r0.symm
      · exact h.1.1.2.1.trans h.2.1.2.1.symm
    · intro s ⟨⟨hc, hp, hf, hr, hsep, hT, hsym, apart⟩, hl⟩
      exact WP.mono (combPrepare_ok hc hl hp hf hr hsep hT hsym apart) fun w ⟨_, E, I⟩ =>
        ⟨w, _, _, E, I⟩
  rw [combMultiply]
  exact RelCT.seq hp (combLoop_ct b T)

theorem scalarBaseEngine_ct (base ptr T : BitVec 32) :
    CT (fun x y => BaseCTPre base ptr T x ∧ BaseCTPre base ptr T y)
      scalarBaseEngine (fun _ _ => True) := by
  have hi : CT (fun x y => BaseCTPre base ptr T x ∧ BaseCTPre base ptr T y) initFieldsCT
      (fun x y => CombCTPre base ptr T x ∧ CombCTPre base ptr T y) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by native_taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · intro s ⟨hc, hp, hfit, hr, hsep, hT, hsym, apart⟩
      have fa : (FA base).Sub ⟨State.addr base, 8192⟩ := Offset.sub_base _ (by decide)
      refine WP.mono_syms (initFields_rest hc) fun a ⟨ak, ar, al, _⟩ sya => ⟨⟨ak.ctx hc,
        (ar.gpr _ (by decide)).trans hp, hfit, by rw [ak.rest.rd, ak.rest.wr]; exact hr, hsep, ?_,
        by rw [sya]; exact hsym, apart⟩, al⟩
      exact hT.of_frame (by rw [ak.rest.rd, ak.rest.wr]) ak.frame fun r hr => by
        rw [List.mem_singleton.mp hr]; exact apart.sub_right fa
  have he : CT (fun x y => Ctx base x ∧ Ctx base y) pointEncode (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by native_taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.r0.trans h.2.r0.symm
  exact RelCT.seq hi (RelCT.seq (combMultiply_ct base ptr T) he)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseSetup`. -/
section
/-! The base-point multiplication wrapper's local contract and scratch setup. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def scalarBaseLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let scalar : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [scalar, TBL (s.syms combSym)] ∧ s.wr = [out, ws] ∧ out.Disjoint scalar ∧ out.Disjoint ws ∧
      scalar.Disjoint ws ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.syms combSym).toNat + 98304 ≤ 2 ^ 32 ∧
      (∀ j < 64 * 192, s.mem.readW (State.addr (s.syms combSym) + BitVec.ofNat 64 (8 * j)) 64 = combWord j) ∧
      (TBL (s.syms combSym)).Disjoint out ∧ (TBL (s.syms combSym)).Disjoint ws
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.syms combSym = t.syms combSym

structure ScalarBasePre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 32⟩, TBL (s.syms combSym)]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r2), 8192⟩]
  out_scalar : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 32⟩
  out_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  scalar_ws : (⟨State.addr (s.gpr .r1), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  tfit : (s.syms combSym).toNat + 98304 ≤ 2 ^ 32
  words : ∀ j < 64 * 192, s.mem.readW (State.addr (s.syms combSym) + BitVec.ofNat 64 (8 * j)) 64 = combWord j
  tbl_out : (TBL (s.syms combSym)).Disjoint ⟨State.addr (s.gpr .r0), 32⟩
  tbl_ws : (TBL (s.syms combSym)).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩

theorem ScalarBasePre.of {s : State} (h : scalarBaseLocal.pre s) : ScalarBasePre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

theorem ScalarBasePre.tbl {s : State} (h : ScalarBasePre s) : TblAt s (s.syms combSym) :=
  ⟨h.tfit, ⟨_, by rw [h.rd]; simp, Region.contains_self _ _⟩, h.words⟩

/-- The table after code that writes only the workspace. -/
theorem ScalarBasePre.tbl_of {s t : State} (h : ScalarBasePre s) (hr : t.rd ++ t.wr = s.rd ++ s.wr)
    (hf : Frame [⟨State.addr (s.gpr .r2), 8192⟩] s.mem t.mem) : TblAt t (s.syms combSym) :=
  h.tbl.of_frame hr hf fun r hr => by rw [List.mem_singleton.mp hr]; exact h.tbl_ws

theorem scalarBaseSetup_ok {s : State} (h : ScalarBasePre s) :
    WP isa (.block scalarBaseSetup) s fun t =>
      Ctx (s.gpr .r2) t ∧ t.gpr .r12 = s.gpr .r1 ∧
      ScalarSaved (State.addr (s.gpr .r2)) s.gpr t.mem ∧
      t.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) 32 = s.gpr .r0 ∧
      t.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 LRS) 32 = s.gpr .lr ∧
      Rest [.r0, .r12] s t ∧ Frame [⟨State.addr (s.gpr .r2), 8192⟩] s.mem t.mem := by
  have hw : (⟨State.addr (s.gpr .r2), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  rw [scalarBaseSetup]
  simp only [List.append_assoc]
  refine WP.append (scalarSave_ok rfl h.f2 hw) fun u ⟨su, fu, gu, ku⟩ => ?_
  refine wp_str (a := State.addr (s.gpr .r2) + BitVec.ofNat 64 48) (by decide)
    (by rw [gu]; exact addr_add (by have := h.f2; omega))
    (by rw [ku.wr]; exact in_base hw (by decide) (by decide)) fun v hv => ?_
  refine wp_mov (op2_reg _ _) fun w hw' => ?_
  have kw : Rest [.r0] s w := (ku.mono (by decide)).trans ((hv.rest _).trans (hw'.rest (by decide)))
  have hcw : Ctx (s.gpr .r2) w := ⟨by rw [hw'.gpr, hv.gpr, gu], h.f2, by rw [kw.wr]; exact hw⟩
  show WP isa (.block ((scratchAddr LRS ++ ([.str .lr .r12 0] : List Instr)) ++
    ([.mov .r12 (.reg .r1)] : List Instr))) w _
  refine WP.append (saveLr_ok hcw) fun x ⟨xr, xm⟩ => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r12] s t :=
    (kw.mono (by decide)).trans ((xr.mono (by decide)).trans (ht.rest (by decide)))
  have mt : t.mem = (u.mem.writeW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) (s.gpr .r0)).writeW
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 LRS) (s.gpr .lr) := by
    rw [ht.mem, xm, kw.gpr _ (by decide), hw'.mem, hv.mem, gu]
  have hS : LRS = 8172 := rfl
  refine ⟨⟨?_, h.f2, by rw [kt.wr]; exact hw⟩, ?_, ?_, ?_, ?_, kt, ?_⟩
  · rw [ht.other _ (by decide), xr.gpr _ (by decide)]; exact hcw.r0
  · rw [ht.gpr, xr.gpr _ (by decide), hw'.other _ (by decide), hv.gpr, gu]
  · intro i hi
    rw [mt, Mem.readW_writeW_sep (Offset.sep _ (d := 4 * i) (e := LRS) (n := 4) (k := 4) (by omega) (by omega)
      (by omega)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (d := 4 * i) (e := 48) (n := 4) (k := 4)
      (by omega) (by omega) (by omega)) (by decide)]
    exact su i hi
  · rw [mt, Mem.readW_writeW_sep (Offset.sep _ (d := 48) (e := LRS) (n := 4) (k := 4) (by omega) (by omega)
      (by omega)) (by decide), Mem.readW_writeW_self32]
  · rw [mt, Mem.readW_writeW_self32]
  · rw [mt]
    exact ((fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCT`. -/
section
/-! The public ABI pointers survive the secret base-point computation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BaseWrapCTPre (b p out T : BitVec 32) (s : State) : Prop :=
  scalarBaseLocal.pre s ∧ s.gpr .r0 = out ∧ s.gpr .r1 = p ∧ s.gpr .r2 = b ∧ s.syms combSym = T

def BaseWorkCTPre (b p out T : BitVec 32) (s : State) : Prop :=
  BaseCTPre b p T s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = out

def BaseFinishCTPre (b out : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = out

theorem scalarBaseSetup_ct (b p out T : BitVec 32) :
    CT (fun x y => BaseWrapCTPre b p out T x ∧ BaseWrapCTPre b p out T y)
      (.block scalarBaseSetup) (fun x y => BaseWorkCTPre b p out T x ∧ BaseWorkCTPre b p out T y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r1, .r2] _ (by native_taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.1.trans h.2.2.2.2.1.symm
  · intro s ⟨h, ho, hp, hb, hT⟩
    have hs := ScalarBasePre.of h
    refine WP.mono_syms (scalarBaseSetup_ok hs) fun t ⟨hc, hptr, _, hout, _, hr, hf⟩ syt => ?_
    have hi : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hs.rd]; simp
    have ht : BaseWorkCTPre (s.gpr .r2) (s.gpr .r1) (s.gpr .r0) (s.syms combSym) t := by
      refine ⟨⟨hc, hptr, hs.f1, ?_, hs.scalar_ws, hs.tbl_of (by rw [hr.rd, hr.wr]) hf, by rw [syt],
        hs.tbl_ws⟩, hout⟩
      intro i hib
      rw [hr.rd, hr.wr]
      exact in_base hi (by omega) (by omega)
    rw [ho, hp, hb, hT] at ht
    exact ht

theorem scalarBaseWork_ct (b p out T : BitVec 32) :
    CT (fun x y => BaseWorkCTPre b p out T x ∧ BaseWorkCTPre b p out T y)
      scalarBaseEngine (fun x y => BaseFinishCTPre b out x ∧ BaseFinishCTPre b out y) := by
  apply ctBoth
  · exact (scalarBaseEngine_ct b p T).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)
  · intro s ⟨⟨hc, hp, hf, hr, hsep, hT, hsym, apart⟩, ho⟩
    refine WP.mono (scalarBaseEngine_ok hc hp hf hr hsep hT hsym apart) fun t ⟨tk, _, _⟩ => ?_
    exact ⟨tk.ctx hc, (tk.word 48 (.inl rfl) (by decide)).trans ho⟩

theorem scalarBaseFinish_ct (b out : BitVec 32) :
    CT (fun x y => BaseFinishCTPre b out x ∧ BaseFinishCTPre b out y)
      (.block scalarBaseFinish) (fun _ _ => True) := by
  have hh : CT (fun x y => BaseFinishCTPre b out x ∧ BaseFinishCTPre b out y)
      (.block ((scratchAddr LRS ++ ([.ldr .lr .r12 0] : List Instr)) ++ ([.ldr .r12 .r0 48] : List Instr)))
      (fun x y => (x.gpr .r0 = b ∧ x.gpr .r12 = out) ∧ (y.gpr .r0 = b ∧ y.gpr .r12 = out)) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by native_taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · intro s ⟨hc, ho⟩
      refine WP.append (loadLr_ok hc) fun u ⟨ur, um, _⟩ => ?_
      refine ldr0_ok (hc.of_rest ur (by decide)) (by decide) fun t ht => WP.block_nil ?_
      exact ⟨(ht.other _ (by decide)).trans ((ur.gpr _ (by decide)).trans hc.r0), ht.gpr.trans (um ▸ ho)⟩
  change CT _ (.block (((scratchAddr LRS ++ ([.ldr .lr .r12 0] : List Instr)) ++
    ([.ldr .r12 .r0 48] : List Instr)) ++ (packField FR 0 ++ scalarRestore))) _
  refine ctBlockAppend hh ?_
  apply ctRegs [.r0, .r12] _ (by native_taint_decide)
  intro x y h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  have hct (b p out T : BitVec 32) :
      CT (fun x y => BaseWrapCTPre b p out T x ∧ BaseWrapCTPre b p out T y) scalarBase (fun _ _ => True) :=
    RelCT.seq (scalarBaseSetup_ct b p out T)
      (RelCT.seq (scalarBaseWork_ct b p out T) (scalarBaseFinish_ct b out))
  intro s t tx ty u v hs ht ⟨_, h0, h1, h2, hT⟩ ex ey
  exact (hct (s.gpr .r2) (s.gpr .r1) (s.gpr .r0) (s.syms combSym) _ _ _ _ _ _
    ⟨⟨hs, rfl, rfl, rfl, rfl⟩, ⟨ht, h0.symm, h1.symm, h2.symm, hT.symm⟩⟩ ex ey).1

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseMain`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarBaseFinish`. -/
section
/-! Canonical point output and restoration of the saved registers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarBaseFinish_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) FR) (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = p)
    (hfit : p.toNat + 32 ≤ 2 ^ 32) (hw : (⟨State.addr p, 32⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block scalarBaseFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧ Rest (.lr :: scalarFinishClob) s t ∧
      t.gpr .lr = s.mem.readW (State.addr b + BitVec.ofNat 64 LRS) 32 ∧
      Frame [⟨State.addr p, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr p) 32 = Spec.Ed25519.encodeLE 32 (V s.mem (State.addr b) FR) := by
  change WP isa (.block ((scratchAddr LRS ++ ([.ldr .lr .r12 0] : List Instr)) ++
    (.ldr .r12 .r0 48 :: (packField FR 0 ++ scalarRestore)))) s _
  refine WP.append (loadLr_ok hc) fun s0 ⟨r0', m0, l0⟩ => ?_
  have hc0 : Ctx b s0 := hc.of_rest r0' (by decide)
  rw [← m0] at hl hp hs l0
  rw [← m0]
  have hw0 : (⟨State.addr p, 32⟩ : Region) ∈ s0.wr := by rw [r0'.wr]; exact hw
  clear hw
  refine ldr0_ok hc0 (by decide) fun u hu => ?_
  have hcu := hc0.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.append (packField_ok (p := p) (a := FR) (dst := 0) hcu (by decide) (hu.mem ▸ hl) (by decide)
    (hu.gpr.trans hp) (by omega)
    (fun i hi => by rw [hu.wr]; simpa only [Nat.zero_add] using in_base hw0 (by omega) (by omega))
    (by simpa only [BitVec.add_zero] using
      hsep.symm.sub_left (Offset.sub_base _ (by decide : FR + 64 ≤ 8192))))
    fun v ⟨kv, fv, vv⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  have hs' : ScalarSaved (State.addr b) g v.mem :=
    (hu.mem ▸ hs).frame fv fun r hr i hi => by
      rw [List.mem_singleton.mp hr, BitVec.add_zero]
      exact hsep.symm.sub_left (Offset.sub_base _ (by omega))
  refine WP.mono (scalarRestore_ok hcv hs') fun t ⟨saved, kt, mt⟩ => ?_
  refine ⟨saved, (r0'.mono (by decide)).trans ((hu.rest (by decide)).trans ((kv.mono (by decide)).trans
    (kt.mono (by decide)))), ?_, ?_, ?_⟩
  · rw [kt.gpr _ (by decide), kv.gpr _ (by decide), hu.other _ (by decide), l0]
  · rw [mt, ← hu.mem]; simpa only [BitVec.add_zero] using fv
  · rw [mt, scalar_packed_encode, ← hu.mem]
    have e : packedV v.mem (State.addr p) = V u.mem (State.addr b) FR := by
      simpa only [BitVec.add_zero] using vv
    exact congrArg (Spec.Ed25519.encodeLE 32) e

end VG.Proof.Ed25519.Arm
end

/-! Base-point multiplication, output encoding, and the complete ARM ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarBase_correct {s : State} (h : ScalarBasePre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  refine WP.seq (WP.mono_syms (scalarBaseSetup_ok h) fun u ⟨hcu, pu, su, ou, lu, ku, fu⟩ syu => ?_)
  have input : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine WP.seq (WP.mono (scalarBaseEngine_ok hcu pu h.f1
    (fun n hn => by rw [ku.rd, ku.wr]; exact in_base input (by omega) (by omega)) h.scalar_ws
    (h.tbl_of (by rw [ku.rd, ku.wr]) fu) (by rw [syu]) h.tbl_ws)
    fun v ⟨kv, lv, vv⟩ => ?_)
  have sv : ScalarSaved (State.addr (s.gpr .r2)) s.gpr v.mem :=
    su.frame kv.frame fun r hr i hi => by
      simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  have ov : v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) 32 = s.gpr .r0 :=
    (kv.word 48 (.inl rfl) (by decide)).trans ou
  refine WP.mono (scalarBaseFinish_ok (kv.ctx hcu) lv ov h.f0
    (by rw [kv.rest.wr, ku.wr, h.wr]; simp) h.out_ws sv) fun t ⟨gt, kt, lt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kv.rest.sp, ku.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [lt, kv.word LRS (.inr (by decide)) (by decide), lu]
  · have hb : Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r1)) 32 =
        Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32 := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun n hn => fu.bytes (R := ⟨State.addr (s.gpr .r1), 32⟩)
        (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hn)
      rw [List.mem_singleton.mp hr]
      exact h.scalar_ws.sub_right (Region.sub_prefix (by decide))
    change Spec.Ed25519.bytesAt t.mem _ 32 = Spec.Ed25519.scalarBase _
    rw [bt, vv, hb, Spec.Ed25519.scalarBase, encodedValue_spec]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseLit`. -/
section
namespace VG.Impl.Ed25519.Arm
materialize_code scalarBase
end VG.Impl.Ed25519.Arm
end

/-! The complete base-point multiplier meets the merged specification,
preserves the ABI, and keeps all scalar bytes secret. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem combWords_length : combWords.length = 64 * 192 := by simp [combWords]

theorem combWords_getD {j : Nat} (hj : j < 64 * 192) : combWords.getD j 0 = combWord j := by
  simp [combWords, List.getD_eq_getElem?_getD, hj]

abbrev scalarBaseSpec : Contract isa := Proof.Ed25519.scalarBaseContract (Arm.abi.withConsts combConsts)

theorem scalarBase_abi_pre {s : State} (h : (Proof.Ed25519.scalarBaseContract Arm.abi).pre s) :
    s.rd = [⟨State.addr (s.gpr .r1), 32⟩] ∧ s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r2), 8192⟩] ∧
      (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 32⟩ ∧
      (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩ ∧
      (⟨State.addr (s.gpr .r1), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩ ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32 := by
  sig_pre [Proof.Ed25519.scalarBaseContract, Proof.Ed25519.scalarBaseSig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
  exact h.2

theorem combConsts_eq : combConsts = [(combSym, combWords)] := rfl

theorem combConsts_regs (s : State) : constRegs combConsts s = [TBL (s.syms combSym)] := by
  simp only [constRegs, Abi.constRegions, combConsts_eq, List.map_cons, List.map_nil, combWords_length]
  rfl

theorem scalarBase_pre {s : State} (h : scalarBaseSpec.pre s) : scalarBaseLocal.pre s := by
  have hp : (Proof.Ed25519.scalarBaseContract Arm.abi).pre (stripConsts combConsts s) ∧
      ConstsOk combConsts 0 s := pre_consts.mp h
  obtain ⟨rd, wr, d1, d2, d3, f0, f1, f2⟩ := scalarBase_abi_pre hp.1
  simp only [stripConsts, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr] at rd wr d1 d2 d3 f0 f1 f2
  have hk := hp.2
  have mem : (combSym, combWords) ∈ combConsts := List.mem_singleton_self _
  have fit := hk.fit mem
  rw [combWords_length] at fit
  have dj : ∀ r ∈ s.wr, (TBL (s.syms combSym)).Disjoint r :=
    (hk.2.2.1 _ (by rw [combConsts_regs]; exact List.mem_singleton_self _)).2.1
  refine ⟨?_, wr, d1, d2, d3, f0, f1, f2, fit, fun j hj => ?_,
    dj _ (by rw [wr]; exact List.mem_cons_self), dj _ (by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · have e1 := hk.1
    rw [combConsts_regs] at e1
    have hl : combConsts.length = 1 := rfl
    rw [hl] at e1 rd
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, e1, rd, List.singleton_append]
  · have hw := hk.2.1 _ mem j (by rw [combWords_length]; exact hj)
    dsimp only at hw
    rw [combWords_getD hj] at hw
    exact hw

/-- The tables at `0x100000`, zero elsewhere (irreducible: unfolding it in a definitional check
would evaluate the tables). -/
@[irreducible] def baseSatMem : Mem := constMem 0x100000 combWords

theorem baseSatMem_held : ∀ i < combWords.length,
    baseSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  unfold baseSatMem
  exact constMem_held _ _ (by rw [combWords_length]; decide)

def baseSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := baseSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x100000, 98304⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]
  syms _ := 0x100000

theorem scalarBase_sat : scalarBaseSpec.pre baseSatState := by
  have held := baseSatMem_held
  generalize eqs : baseSatState = s
  sig_pre [Proof.Ed25519.scalarBaseContract, Proof.Ed25519.scalarBaseSig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  rw [combWords_length]
  rw [combWords_length] at held
  refine ⟨by decide, by decide, held, by decide, ?_, by decide, by decide, by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide⟩
  intro r hr
  change r ∈ [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' :=
  scalarBase_correct (ScalarBasePre.of hs)

theorem scalarBase_implies : scalarBaseLocal.Implies scalarBaseSpec where
  pre _ h := scalarBase_pre h
  post := by
    intro s s' _ h
    sig_post [Proof.Ed25519.scalarBaseContract, Proof.Ed25519.scalarBaseSig, Spec.Ed25519.scratchWords,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Ed25519.scalarBaseContract, Proof.Ed25519.scalarBaseSig, Spec.Ed25519.scratchWords,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, combConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨baseSatState, scalarBase_sat⟩

theorem scalarBase_verified : Verified Arm.target scalarBase scalarBaseSpec :=
  Verified.of_correct scalarBase_ok scalarBase_ct scalarBase_implies

end VG.Proof.Ed25519.Arm
