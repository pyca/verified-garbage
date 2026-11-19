module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputsPublic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadPrime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageCover
import VerifiedGarbage.Proof.Rsa.WordRanges
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Inverse
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddModulus
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Prepare
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DOddTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DEvenTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DOnePublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Primes
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrimesPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LcmTiming
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.SmallPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.KeyPartTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseCall
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArrayDivision
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
import VerifiedGarbage.Proof.Rsa.X86.KeyBits
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
import VerifiedGarbage.Proof.Mont.WriteWord32
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.RsaKeyGen.X86.DisjointBounds
public import VerifiedGarbage.Proof.Framework.X86.Inline

/-! ### `RsaKeyGen.X86.KeyRuntime.InputTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.StartPair`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.CoreReadonlyTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.ArgumentTaint`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.Readonly`, which this module and modules that import it used -/

section

/-! # Arithmetic writes only the workspace, keeping the original arguments read-only -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (RtWs)
open VG.Proof.Bignum.X86 (CallArgument)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

def readonly (s : State) (B : Addr) (Z : Nat) : State :=
  s.withRegions (s.rd ++ s.wr) [⟨B, Z⟩]

theorem readonly_read {s : State} {B : Addr} {Z : Nat} :
    Covers (s.rd ++ s.wr) ((readonly s B Z).rd ++ (readonly s B Z).wr) :=
  Covers.of_mem fun _ hr => List.mem_append_left _ hr

theorem argument_readonly {s : State} {B : Addr} {Z i : Nat} {v : BitVec 32}
    (h : CallArgument s B Z i v) : CallArgument (readonly s B Z) B Z i v :=
  ⟨⟨readonly_read _ _ h.stack.read, h.stack.apart⟩, h.value⟩

theorem rtws_readonly {L : VG.Impl.Rsa.X86.KeyRt.Lay} {s : State} {B : Addr} {Z len N : Nat}
    (h : RtWs L s B Z len N) : RtWs L (readonly s B Z) B Z len N := by
  refine ⟨?_, h.lenArg.imp fun _ ⟨a, l, c⟩ => ⟨a, l, argument_readonly c⟩,
    argument_readonly h.wsArg, h.lenLe, h.layLen⟩
  exact { h.ws with workspace := { h.ws.workspace with wr := List.mem_singleton_self _ } }

theorem Ws.readonly {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) :
    Ws (readonly s B Z) B Z n N :=
  ⟨rtws_readonly h.full, rtws_readonly h.prime, rtws_readonly h.exponent, h.width, h.size, h.deep⟩

theorem context_readonly {s : State} {B : Addr} {Z : Nat} {p : BitVec 32} {args : Nat → BitVec 32}
    (C : Context B Z p args s) : Context B Z p args (readonly s B Z) := by
  refine ⟨{ C.scratch with wr := List.mem_singleton_self _ }, C.header, C.sp, C.fit, C.separate, ?_, C.deep⟩
  intro i hi
  exact VG.X86.readSrc_widen readonly_read (C.read i hi)

theorem readonly_covers {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) :
    Covers ((readonly s B Z).rd ++ (readonly s B Z).wr) (s.rd ++ s.wr) ∧
      Covers (readonly s B Z).wr s.wr := by
  have write : Covers (readonly s B Z).wr s.wr := Covers.of_mem (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.old.workspace.wr)
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right write), write⟩

theorem trace_readonly_of_wp {c : Prog isa} {s t : State} {B : Addr} {Z n N : Nat} {Q : State → Prop}
    (h : Ws s B Z n N) (run : WP isa c (readonly s B Z) Q)
    {trace : List Leak} (E : Exec isa c s trace t) :
    ∃ u, Exec isa c (readonly s B Z) trace u := by
  obtain ⟨trace', u, EU, _⟩ := run
  obtain ⟨read, write⟩ := readonly_covers h
  have EW := VG.X86.Exec.widen EU read write
  simp only [readonly, State.withRegions_withRegions, State.withRegions_self] at EW
  obtain ⟨rfl, _⟩ := Exec.det E EW
  exact ⟨u, EU⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # Public original arguments in a workspace-only arithmetic run -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)

theorem context_argumentWindow {s : State} {B : Addr} {Z : Nat} {p : BitVec 32} {args : Nat → BitVec 32}
    (C : Context B Z p args s) (large : 160 ≤ Z) :
    (⟨VG.X86.Taint.argByte s 16, 76⟩ : Region).Disjoint ⟨B, Z⟩ := by
  have fit := C.fit
  have nowrap := C.scratch.nowrap
  have nat20 : (argsRegion p).base.toNat = p.toNat + 20 := by
    simp only [argsRegion, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [fit]
  have nat16 : (VG.X86.Taint.argByte s 16).toNat = p.toNat + 16 := by
    simp only [VG.X86.Taint.argByte, C.sp, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have bound := p.isLt
    omega_using []
  have bounds := VG.Proof.RsaKeyGen.X86.Key.disjoint_bounds (by decide : 0 < 72) (by omega_using [large]) C.separate
  change (argsRegion p).base.toNat + 72 ≤ B.toNat ∨ B.toNat + Z ≤ (argsRegion p).base.toNat at bounds
  rw [nat20] at bounds
  have stack := C.scratch.stk
  rw [C.sp] at stack
  rcases stack.2 with before | after
  · have above : p.toNat + 92 ≤ B.toNat := by omega_using [large, bounds, before]
    apply Offset.disjoint_of_le
    · change (VG.X86.Taint.argByte s 16).toNat + 76 ≤ B.toNat
      rw [nat16]
      omega_using [above]
    · change B.toNat + Z ≤ 2 ^ 64
      omega_using [nowrap]
  · apply Region.Disjoint.symm
    apply Offset.disjoint_of_le
    · change B.toNat + Z ≤ (VG.X86.Taint.argByte s 16).toNat
      rw [nat16]
      omega_using [after]
    · change (VG.X86.Taint.argByte s 16).toNat + 76 ≤ 2 ^ 64
      rw [nat16]
      omega_using []

theorem readonly_wf {s : State} {B : Addr} {Z : Nat} {p : BitVec 32} {args : Nat → BitVec 32}
    (C : Context B Z p args s) (large : 160 ≤ Z) : VG.X86.Taint.Wf runtimeTaint (readonly s B Z) := by
  have fit := C.fit
  refine {
    lens := fun h => False.elim (h rfl)
    bases := by intro p hp; cases hp
    wbases := by intro p hp; cases hp
    args := ?_
    argBases := by intro p hp; cases hp
    stk := ?_
    frames := by intro p hp; cases hp
    room := by intro h; cases h }
  · intro _
    refine ⟨?_, ?_⟩
    · change (s.gpr .esp).toNat + 16 + 76 ≤ 2 ^ 32
      rw [C.sp]
      omega_using [fit]
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      change (⟨VG.X86.Taint.argByte s 16, 76⟩ : Region).Disjoint ⟨B, Z⟩
      exact context_argumentWindow C large
  · change (s.gpr .esp).toNat + 16 < 2 ^ 32
    rw [C.sp]
    omega_using [fit]

theorem readonly_agree {s t : State} {B : Addr} {Z : Nat} {p : BitVec 32} {args : Nat → BitVec 32}
    (S : Context B Z p args s) (T : Context B Z p args t) (large : 160 ≤ Z)
    (esi : s.gpr .esi = t.gpr .esi) :
    VG.X86.Taint.Agree runtimeTaint (readonly s B Z) (readonly t B Z) := by
  have sp : s.gpr .esp = t.gpr .esp := S.sp.trans T.sp.symm
  have fitS : (s.gpr .esp).toNat + 92 ≤ 2 ^ 32 := by rw [S.sp]; exact S.fit
  have fitT : (t.gpr .esp).toNat + 92 ≤ 2 ^ 32 := by rw [T.sp]; exact T.fit
  refine {
    rf := ⟨?_, by intro h; cases h⟩
    wr := fun h => False.elim (h rfl)
    wf₁ := readonly_wf S large
    wf₂ := readonly_wf T large
    ok := VG.X86.Taint.slotsOk_empty
    slots := VG.X86.Taint.slotsAgree_empty
    sp := fun _ => sp
    argMem := ?_ }
  · intro r hr
    simp only [runtimeTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact BitVec.eq_of_toNat_eq (S.scratch.edi_toNat.trans T.scratch.edi_toNat.symm)
    · exact esi
    · exact sp
  · intro k h4 hk
    change k < 76 at hk
    change s.mem (VG.X86.Taint.argByte s (16 + k)) = t.mem (VG.X86.Taint.argByte t (16 + k))
    rw [VG.X86.Taint.argByte_eq fitS (by omega_using []) (by omega_using [hk]),
      VG.X86.Taint.argByte_eq fitT (by omega_using []) (by omega_using [hk]),
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide : 0 < 4)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide : 0 < 4))]
    have index : (16 + k - 4) / 4 = (k - 4) / 4 + 4 := by omega_using [h4]
    have same := (context_argument S (i := (k - 4) / 4) (by change k < 76 at hk; omega_using [hk])).value.trans
      (context_argument T (i := (k - 4) / 4) (by change k < 76 at hk; omega_using [hk])).value.symm
    change arg s ((k - 4) / 4 + 4) = arg t ((k - 4) / 4 + 4) at same
    rw [index]
    exact congrArg _ same

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.InputStage`, which this module and modules that import it used -/

section

/-! # A stage that calls `vg_rsa_keygen_inverse` keeps the key's inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment Input)

/-- `Input.afterStage`, through a stage that calls `vg_rsa_keygen_inverse`. -/
theorem input_afterStage {E : Environment} {s t : State} {regs : List Reg} {js : List Nat}
    (h : Input E s) (Hs : Ws s E.base E.size E.n 32) (ws : VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32)
    (K : Keeps regs s t)
    (O : OutsS E.base (s.gpr .esp) (VG.Proof.RsaKeyGen.X86.Key.stageRanges E.n js) s.mem t.mem) : Input E t := by
  apply h.keep ws K
  intro d hd
  apply BitVec.eq_of_toNat_eq
  have H := Hs.read_val32 (d := d) (k := 1) (by unfold VG.Impl.Rsa.X86.Keys.hdr; omega_using [hd]) O
    (VG.Proof.RsaKeyGen.X86.Key.stage_preserves_header (n := E.n) (d := d) (count := 1)
      (by change d + 4 ≤ VG.Impl.RsaKeyGen.X86.Key.kOk; unfold VG.Impl.RsaKeyGen.X86.Key.kOk; omega_using [hd]))
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.Derive`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.SmallMask`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.SmallConstant`, which only this module used -/

section

/-! # Construct the private-exponent retry bound at the runtime width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep S)
open VG.Proof.Mont.X86.Rt (PtrAt)
open VG.Impl.Rsa.X86.Keys (aT1)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem smallConstant_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa smallConstant s fun t => Ws t B Z n 32 ∧ Keep B n [aT1] [] s.mem t.mem ∧
      num t.mem B n aT1 = 2 ^ (16 * n) + 1 ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fit := h.arr_fit (j := aT1) (by decide)
  have nowrap := h.old.workspace.nowrap
  have positive := h.wpos
  have width := h.width
  have half : 32 * (n / 2) = 16 * n := by omega_arith
  unfold smallConstant
  refine WP.seq (WP.mono (constant_ok h (by decide) (1 : BitVec 32)) fun u ⟨hu, Ou, one, Ku⟩ => ?_)
  change num u.mem B n aT1 = 1 at one
  refine hu.ptr_ok (arr aT1) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold S at fit; omega_arith)
    fun v Kv mv Pv => ?_
  have hv := hu.keep Kv (by rw [mv]; exact Outside.refl _ _ _ _)
  refine hv.bytes_ok .prime .edx fun w Kw mw count => ?_
  change (w.gpr .edx).toNat = 4 * (n / 2) at count
  refine wp_addS rfl fun x X _ => wp_movS rfl fun y Y _ => ?_
  have K : Keeps [.eax, .ecx, .edx, .ebp] u y := (Kv.mono (by decide)).trans
    ((Kw.mono (by decide)).trans ((X.keeps.mono (by decide)).trans (Y.keeps.mono (by decide))))
  have memory : y.mem = u.mem := Y.mem.trans (X.mem.trans (mw.trans mv))
  have hy := hu.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  have Py : PtrAt y B .ebp (VG.Proof.Rsa.X86.Keys.arr n aT1 + 4 * (n / 2)) := by
    rw [PtrAt, Y.other _ (by decide), X.gpr, VG.Proof.Mont.X86.Rt.ptr_add]
    · rw [count]
    · rw [PtrAt, Kw.1 _ (by decide)]; exact Pv
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr hy.full.rt Py (d := 0)
    (by unfold S at fit; omega_arith)) (VG.Proof.Mont.X86.Rt.ws_write hy.full.rt
      (by unfold S at fit; omega_arith)) fun t T => WP.block_nil ?_
  have mem : t.mem = u.mem.writeW
      (off B (VG.Proof.Rsa.X86.Keys.arr n aT1 + 4 * (n / 2))) (1 : BitVec 32) := by
    rw [T.mem, memory, Y.gpr, Nat.add_zero]
  have Ot : Outside B (VG.Proof.Rsa.X86.Keys.arr n aT1 + 4 * (n / 2)) 4 u.mem t.mem := by
    rw [mem]; exact writeW32_outside _ _ _ (by unfold S at fit; omega_arith)
  have frame := Ou.trans (VG.Proof.Rsa.X86.Keys.Keep.of_arr Ot
    (by unfold S; omega_arith) (by simp))
  have value : num t.mem B n aT1 = 2 ^ (16 * n) + 1 := by
    rw [num, mem, VG.Proof.Mont.val32_write_word _ _ _ (by omega_arith : n / 2 < n)
      (by unfold S at fit; omega_arith)]
    · change num u.mem B n aT1 + 2 ^ (32 * (n / 2)) * 1 = _
      rw [one, half, Nat.mul_one, Nat.add_comm]
    · change num u.mem B n aT1 < _
      rw [one]
      have bound := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega_arith : 1 ≤ 32 * (n / 2))
      omega_arith
  have Kt := Ku.trans (K.trans (T.keeps _))
  exact ⟨h.afterKeep Kt frame (by decide) (by simp), frame, value, Kt⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end


/-! # Detect the specified private-exponent retry bound -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aD kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem smallMask_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) :
    WP isa smallMask s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [] s.mem t.mem ∧
      isa.eval .e t = some (decide (¬(slot s.mem B kOk = 1 ∧ num s.mem B n aD ≤ 2 ^ (16 * n)))) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have head := h.hdr_le
  unfold smallMask seqs
  refine WP.seq (WP.mono (smallConstant_ok h)
    fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  have Du : num u.mem B n aD = num s.mem B n aD :=
    Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, subtract, borrowBit, Kv⟩ => ?_)
  rw [Du, constant] at subtract
  have borrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) borrowBit
  have borrowOne : (v.gpr .ebx).toNat = 1 ↔ num s.mem B n aD ≤ 2 ^ (16 * n) := by omega_using [borrowBit, borrow]
  have maskV : slot v.mem B kOk = slot s.mem B kOk :=
    (Ov.slot (by decide) (by simp)).trans (Ou.slot (by decide) (by simp))
  refine wp_movS (readSrc_sc hv.old.workspace (by unfold kOk hdr at *; omega_using [head])) fun w W _ => ?_
  refine wp_logicS (.inl rfl) rfl fun a A => ?_
  refine wp_cmpS rfl fun t T flag => WP.block_nil ?_
  have Ktail : Keeps [.eax] v t := (W.keeps.trans A.keeps).trans (T.keeps _)
  have memory : t.mem = v.mem := T.mem.trans (A.mem.trans W.mem)
  refine ⟨hv.keep Ktail (by rw [memory]; exact Outside.refl _ _ _ _), ?_, ?_, (Ku.mono (by decide)).trans (Kv.trans (Ktail.mono (by decide)))⟩
  · rw [memory]
    exact Ou.join Ov (js := [aT1, aT2]) (ds := [])
  · change t.zf = _
    rw [flag]
    change some (a.gpr .eax - 0#32 == 0#32) = _
    rw [BitVec.sub_zero, A.gpr, W.gpr, W.other _ (by decide)]
    change some ((v.mem.readW (off B kOk) 32 &&& v.gpr .ebx) == 0#32) = _
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_zero]
    rw [VG.Proof.Rsa.KeyBits32.bv_and_bits (by change slot v.mem B kOk ≤ 1; rw [maskV]; exact bit) borrowBit]
    change (if slot v.mem B kOk = 1 ∧ (v.gpr .ebx).toNat = 1 then 1 else 0) = 0 ↔ _
    simpa only [maskV, borrowOne] using
      (show (if slot s.mem B kOk = 1 ∧ num s.mem B n aD ≤ 2 ^ (16 * n) then 1 else 0) = 0 ↔
        ¬(slot s.mem B kOk = 1 ∧ num s.mem B n aD ≤ 2 ^ (16 * n)) from by split <;> simp_all)

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyFinalMask`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.KeyMaskFlag`, which this module and modules that import it used -/

section

/-! # Combine a checked bit with the persistent RSA validity mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem maskFlag_preserves_e {m m' : Mem} {B : Addr} {n : Nat}
    (O : Keep B n [] [kFlag, kOk] m m') : val32 m' B kEv 2 = val32 m B kEv 2 := by
  apply O.val32 _ (by decide)
  intro r hr
  change r ∈ [] ++ [(kFlag, 4), (kOk, 4)] at hr
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  all_goals exact Or.inl (by decide)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.TopWord32`, which this module and modules that import it used -/

section

/-! # The modulus's high native word detects its required top bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.WordBounds32
open VG VG.Proof.Mont

theorem top_div {m : Mem} {B : Addr} {out n : Nat} (positive : 0 < n) :
    val32 m B out n / 2 ^ (32 * n - 1) = w32 m B (out + 4 * (n - 1)) / 2 ^ 31 := by
  have parts := val32_append m B out (n - 1) 1
  rw [show n - 1 + 1 = n by omega_using [positive]] at parts
  change val32 m B out n = val32 m B out (n - 1) + 2 ^ (32 * (n - 1)) * w32 m B (out + 4 * (n - 1)) at parts
  have top : val32 m B out n / 2 ^ (32 * (n - 1)) = w32 m B (out + 4 * (n - 1)) := by
    rw [parts, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (val32_lt _ _ _ _), Nat.zero_add]
  rw [show 32 * n - 1 = 32 * (n - 1) + 31 by omega_using [positive], Nat.pow_add, ← Nat.div_div_eq_div_mul, top]

end VG.Proof.RsaKeyGen.WordBounds32

end

end

/-! # The final native mask is exactly the RSA key shape check -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem mask_bit (P : Prop) [Decidable P] : (if P then 1 else 0 : Nat) ≤ 1 := by
  split <;> decide

theorem mask_ite_one (P : Prop) [Decidable P] : (if P then 1 else 0 : Nat) = 1 ↔ P := by
  by_cases H : P <;> simp [H]

/-- The flag the final checks leave, as the conjunction of the checks: a
lemma about numbers, so that `KeyRuntime.finalMask_ok` does not normalize the
condition among facts about memory. -/
theorem finalMask_cond (m k N P Q e : Nat) :
    (if 3 ≤ e ∧ (if (if (if (if (if m = 1 ∧ (if k ≤ N then 1 else 0) = 1 then 1 else 0) = 1 ∧
        P % 2 = 1 then 1 else 0) = 1 ∧ Q % 2 = 1 then 1 else 0) = 1 ∧ e % 2 = 1 then 1 else 0) = 1 ∧
        (if e < 2 ^ 33 then 1 else 0) = 1 then 1 else 0) = 1 then 1 else 0 : Nat) =
      if m = 1 ∧ k ≤ N ∧ P % 2 = 1 ∧ Q % 2 = 1 ∧ Spec.Rsa.exponentValid e = true then 1 else 0 := by
  simp only [mask_ite_one, Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc, and_comm, and_left_comm]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.KeyPart`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.Qinv`, which only this module used -/

section

/-! # The CRT coefficient uses a prime-width native inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aDen aQi kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (safePrime qinvArrays stageRanges stage_keep stage_inverse stage_outside
  inverse_workspace inverse_array_layout inverse_end_le InverseLayout)

theorem qinvPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (bit : slot s.mem B kOk ≤ 1) :
    WP isa qinvPart s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (stageRanges n qinvArrays) s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧
        Nat.gcd (num s.mem B n aQa) (safePrime (num s.mem B n aPa)) = 1 then 1 else 0) ∧
      num t.mem B n aQi < safePrime (num s.mem B n aPa) ∧
      (safePrime (num s.mem B n aPa) : Int) ∣
        (num t.mem B n aQi : Int) * num s.mem B n aQa -
          Nat.gcd (num s.mem B n aQa) (safePrime (num s.mem B n aPa)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let P := num s.mem B n aPa
  let Q := num s.mem B n aQa
  let M := safePrime P
  obtain small : k ≤ n := by omega_using [width]
  obtain half : n / 2 = k := by omega_using [width]
  obtain mo : M % 2 = 1 := by
    unfold M safePrime
    split
    · next H => exact H.1
    · decide
  obtain ml : 1 < M := by unfold M safePrime; split <;> omega_arith
  obtain threeBound : 3 < 2 ^ (32 * k) := by
    obtain H := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 32 ≤ 32 * k by omega_using [positive])
    omega_using [H]
  obtain mb : M < 2 ^ (32 * k) := by
    unfold M safePrime
    split
    · exact boundP
    · exact threeBound
  unfold qinvPart seqs
  refine WP.seq (WP.mono (oddModulus_ok h (by decide) (by decide) (by decide))
    fun u ⟨hu, Ou, _, modulus, Ku⟩ => ?_)
  change num u.mem B n aDen = M at modulus
  obtain Qu : num u.mem B n aQa = Q := Ou.num (by decide) (by decide) (h.fit64 (by decide))
  obtain maskU : slot u.mem B kOk = slot s.mem B kOk := Ou.slot (by decide) (by decide)
  obtain lowQ : val32 u.mem B (arr n aQa) k = Q :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq small (by change num u.mem B n aQa < _; rw [Qu]; exact boundQ)).trans Qu
  obtain lowM : val32 u.mem B (arr n aDen) k = M :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq small (by change num u.mem B n aDen < _; rw [modulus]; exact mb)).trans modulus
  obtain hk := inverse_workspace hu.old positive small
  obtain layout := inverse_array_layout hu.old small (a := aQa) (b := aDen)
    (by decide) (by decide) (by decide) (by decide)
  obtain layout' : InverseLayout Z (Width.prime.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aQa).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen).offset n) := by
    simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, half] using layout
  refine WP.seq (WP.mono (inverseFrom_ok hu (by decide) (by decide) layout' 
    (by change val32 u.mem B (arr n aDen) (n / 2) % 2 = 1; rw [half, lowM]; exact mo)
    (by change 1 < val32 u.mem B (arr n aDen) (n / 2); rw [half, lowM]; exact ml))
    fun v ⟨hv, Ov, gcd, congruence, boundX, Kv⟩ => ?_)
  simp only [Width.words, half, VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array] at Ov gcd congruence boundX
  obtain hvSmall := inverse_workspace hv.old positive small
  change num v.mem B k 1 = Nat.gcd (val32 u.mem B (arr n aQa) k) (val32 u.mem B (arr n aDen) k) at gcd
  change (val32 u.mem B (arr n aDen) k : Int) ∣ (num v.mem B k 3 : Int) * val32 u.mem B (arr n aQa) k - num v.mem B k 1 at congruence
  change num v.mem B k 3 < val32 u.mem B (arr n aDen) k at boundX
  rw [lowQ, lowM] at gcd congruence
  rw [lowM] at boundX
  rw [gcd] at congruence
  obtain maskV : slot v.mem B kOk = slot s.mem B kOk :=
    (hu.inverse_slot (by decide) Ov).trans maskU
  refine WP.seq (WP.mono (gcdIsOne_ok (w := .prime) hv (by decide) (by decide))
    fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  simp only [Width.words, half] at Ow
  change slot w.mem B kFlag = (if num v.mem B (n / 2) 1 = 1 then 1 else 0) at flag
  rw [half, gcd] at flag
  obtain Xw : num w.mem B k 3 = num v.mem B k 3 :=
    Ow.num (by decide) (by decide) (hvSmall.fit64 (by decide))
  obtain maskW : slot w.mem B kOk = slot s.mem B kOk :=
    (Ow.slot (by decide) (by decide)).trans maskV
  refine WP.seq (WP.mono (andS_ok hw (by decide) (by decide) (by decide)
    (by rw [maskW]; exact bit) (by rw [flag]; split <;> omega_using []))
    fun a ⟨ha, Oa, maskA, Ka⟩ => ?_)
  rw [maskW, flag] at maskA
  obtain Xa : num a.mem B k 3 = num v.mem B k 3 := by
    obtain F := hvSmall.fit64 (j := 3) (by decide)
    obtain same : val32 a.mem B (arr k 3) k = val32 w.mem B (arr k 3) k := by
      apply Oa.val32 _ (by unfold S at F; omega_using [F])
      intro r hr
      change r ∈ [] ++ [(kOk, 4)] at hr
      obtain E : r = (kOk, 4) := by simpa only [List.nil_append, List.mem_singleton] using hr
      subst r
      exact Or.inr (Nat.le_trans (by decide : kOk + 4 ≤ hdr) (Nat.le_add_right ..))
    exact same.trans Xw
  obtain sourceBound : arr k 3 + 4 * k ≤ Z := by
    obtain F := hk.arr_fit (j := 3) (by decide)
    unfold S at F
    omega_using [F]
  obtain before : arr k 3 + 4 * k ≤ arr n aQi := by
    obtain F := arr_end (w := k) (show 3 < 15 by decide)
    obtain E := inverse_end_le small (j := aQi) (by decide)
    unfold S at F
    omega_using [F, E]
  obtain widening := widen_ok ha .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aQi)
    (.array .prime 3) (by change n / 2 ≤ n; omega_using []) (ha.arr_fit (by decide))
    (by simpa only [offset_array, Width.words, half] using sourceBound)
    (Or.inl (by simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, half] using before))
  simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, half] at widening
  refine WP.mono widening
    fun t ⟨ht, Ot, _, coefficient, Kt⟩ => ?_
  obtain X : num t.mem B n aQi = num v.mem B k 3 := coefficient.trans Xa
  obtain maskT : slot t.mem B kOk = slot a.mem B kOk :=
    Ot.w32 (Nat.le_trans (by decide : kOk + 4 ≤ hdr) (Nat.le_add_right ..) |> Or.inl) (by decide)
  obtain frameU : Outs B (stageRanges n qinvArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  obtain spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  obtain frameV : OutsS B (s.gpr .esp) (stageRanges n qinvArrays) u.mem v.mem := by
    rw [← spU]
    exact OutsS.lift (fun _ _ => stage_inverse small) Ov
  obtain frameW : Outs B (stageRanges n qinvArrays) v.mem w.mem :=
    stage_keep small (by
      intro j hj
      left
      obtain H : ∀ j ∈ [aT2, aT1], j < 15 := by decide
      exact H j hj) (by decide) Ow
  obtain frameA : Outs B (stageRanges n qinvArrays) w.mem a.mem :=
    stage_keep (Nat.le_refl n) (by simp) (by decide) Oa
  refine ⟨ht, ((((OutsS.of_outs frameU).trans frameV).trans (OutsS.of_outs frameW)).trans
      (OutsS.of_outs frameA)).trans (OutsS.of_outs (stage_outside (by decide) Ot)),
    ?_, ?_, ?_, (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans
      ((Ka.mono (by decide)).trans (Kt.mono (by decide)))))⟩
  · rw [maskT, maskA]
    change (if slot s.mem B kOk = 1 ∧ (if Nat.gcd Q M = 1 then 1 else 0) = 1 then 1 else 0) =
      (if slot s.mem B kOk = 1 ∧ Nat.gcd Q M = 1 then 1 else 0)
    by_cases G : Nat.gcd Q M = 1 <;> simp [G]
  · rw [X]
    exact boundX
  · rw [X]
    exact congruence

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.FinalMask`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.TopBit`, which only this module used -/

section

/-! # Read the high modulus word through its public runtime address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Proof.Mont.X86.Rt (PtrAt)
open VG.Impl.RsaKeyGen.X86.Key (aN kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem topBit_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block topBit) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if 2 ^ (32 * n - 1) ≤ num s.mem B n aN then 1 else 0) ∧
      Keeps [.eax, .edx, .ebp] s t := by
  obtain fits := h.arr_fit (j := aN) (by decide)
  have positive := h.wpos
  have nowrap := h.old.workspace.nowrap
  unfold topBit
  refine h.ptr_ok (arr aN) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fits; omega_using [fits, nowrap])
    fun u Ku mu Pu => ?_
  obtain hu := h.keep Ku (by rw [mu]; exact Outside.refl _ _ _ _)
  refine hu.bytes_ok .modulus .edx fun v Kv mv count => ?_
  change (v.gpr .edx).toNat = 4 * n at count
  refine wp_addS rfl fun w W _ => wp_subS rfl fun x X _ => ?_
  obtain Kx : Keeps [.ebp, .edx] s x := (Ku.trans (Kv.mono (by decide))).trans
    ((W.keeps.mono (by decide)).trans (X.keeps.mono (by decide)))
  obtain mx : x.mem = s.mem := X.mem.trans (W.mem.trans (mv.trans mu))
  obtain hx := h.keep Kx (by rw [mx]; exact Outside.refl _ _ _ _)
  obtain Px : PtrAt x B .ebp (VG.Proof.Rsa.X86.Keys.arr n aN + 4 * (n - 1)) := by
    rw [PtrAt, X.gpr, W.gpr, BitVec.toNat_sub, BitVec.toNat_add,
      Kv.1 _ (by decide), Pu, count]
    simp only [arr, offset_array, Width.words] at *
    simp only [show (4 : BitVec 32).toNat = 4 by rfl]
    unfold VG.Proof.Rsa.X86.Keys.S at fits
    omega_using [positive]
  refine wp_movS (VG.Proof.Mont.X86.Rt.readSrc_ptr hx.full.rt Px (d := 0)
    (by unfold VG.Proof.Rsa.X86.Keys.S at fits; omega_using [fits])) fun y Y _ => ?_
  refine wp_shr (by decide) fun z Zf _ => ?_
  obtain K : Keeps [.eax, .edx, .ebp] s z := (Kx.mono (by decide)).trans
    ((Y.keeps.mono (by decide)).trans (Zf.keeps.mono (by decide)))
  obtain memory : z.mem = s.mem := Zf.mem.trans (Y.mem.trans mx)
  obtain hz := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  refine WP.mono (store_slot hz (d := kFlag) (by decide) .eax) fun t ⟨ht, O, flag, Kt⟩ => ?_
  rw [memory] at O
  refine ⟨ht, O, ?_, K.trans (Kt.mono (by decide))⟩
  rw [flag, Zf.gpr, Y.gpr, mx, Nat.add_zero,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change w32 s.mem B (VG.Proof.Rsa.X86.Keys.arr n aN + 4 * (n - 1)) / 2 ^ 31 = _
  rw [← VG.Proof.RsaKeyGen.WordBounds32.top_div positive]
  change num s.mem B n aN / 2 ^ (32 * n - 1) = _
  obtain bound := val32_lt s.mem B (VG.Proof.Rsa.X86.Keys.arr n aN) n
  change num s.mem B n aN < 2 ^ (32 * n) at bound
  obtain factor : 2 ^ (32 * n) = 2 ^ (32 * n - 1) * 2 := by
    calc
      2 ^ (32 * n) = 2 ^ ((32 * n - 1) + 1) := congrArg (2 ^ ·) (by omega_using [positive])
      _ = _ := Nat.pow_succ ..
  rw [factor] at bound
  split
  · next H => exact Nat.div_eq_of_lt_le (by simpa only [Nat.one_mul] using H) (by omega_using [bound])
  · next H => exact Nat.div_eq_of_lt (by omega_using [H])

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # The final native mask is exactly the RSA key shape check -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/MaskFlag.lean`, which only this module imported.
section

/-! # Combine a checked bit with the persistent RSA validity mask -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem withFlag_ok {s : State} {B : Addr} {Z n value : Nat} {c : Prog isa} {rs : List Reg}
    (bit : slot s.mem B kOk ≤ 1) (valueBit : value ≤ 1)
    (correct : WP isa c s fun u => Ws u B Z n 32 ∧ Keep B n [] [kFlag] s.mem u.mem ∧
      slot u.mem B kFlag = value ∧ Keeps rs s u) (eax : .eax ∈ rs := by decide) :
    WP isa (withFlag c) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧ value = 1 then 1 else 0) ∧ Keeps rs s t := by
  unfold withFlag
  refine WP.seq (WP.mono correct fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  obtain maskU : slot u.mem B kOk = slot s.mem B kOk := Ou.slot (by decide) (by decide)
  refine WP.mono (andS_ok hu (by decide) (by decide) (by decide)
    (by rw [maskU]; exact bit) (by rw [flag]; exact valueBit)) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  exact ⟨ht, Ou.join Ot (js := []) (ds := [kFlag, kOk]), by rw [mask, maskU, flag], Ku.trans (Kt.mono (by simpa using eax))⟩


end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/FinalExponent.lean`, which only this module imported.
section

/-! # The lower bound on the runtime public exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aE kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem exponentAtLeastThree_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) :
    WP isa exponentAtLeastThree s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if 3 ≤ num s.mem B n aE ∧ slot s.mem B kOk = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold exponentAtLeastThree seqs
  refine WP.seq (WP.mono (constant_ok h (by decide) (3 : BitVec 32)) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  change num u.mem B n aT1 = 3 at constant
  obtain E : num u.mem B n aE = num s.mem B n aE := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, subtract, borrow, Kv⟩ => ?_)
  rw [E, constant] at subtract
  obtain iffBorrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) borrow
  obtain maskV : slot v.mem B kOk = slot s.mem B kOk :=
    (Ov.slot (by decide) (by simp)).trans (Ou.slot (by decide) (by simp))
  refine WP.seq (WP.mono (saveSlot_ok hv (by decide) (by decide)) fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  rw [maskV] at flag
  obtain borrowW : (w.gpr .ebx).toNat = (v.gpr .ebx).toNat := congrArg BitVec.toNat (Kw.1 .ebx (by decide))
  refine WP.mono (borrowMask_ok hw (by rw [borrowW]; exact borrow)
    (by rw [flag]; exact bit)) fun t ⟨ht, Ot, value, Kt⟩ => ?_
  refine ⟨ht, ((Ou.join Ov (js := [aT1, aT2]) (ds := [])).join Ow
    (js := [aT1, aT2]) (ds := [kFlag])).join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk]), ?_,
    (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  simpa only [borrowW, iffBorrow, flag] using value

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aN aE kOk kFlag kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (mask_bit mask_ite_one maskFlag_preserves_e)

theorem finalMask_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa finalMask s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧
        2 ^ (32 * n - 1) ≤ num s.mem B n aN ∧
        num s.mem B n aPa % 2 = 1 ∧ num s.mem B n aQa % 2 = 1 ∧
        Spec.Rsa.exponentValid (val32 s.mem B kEv 2) = true then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold finalMask seqs
  refine WP.seq (WP.mono (withFlag_ok bit (by split <;> omega_arith) (topBit_ok h))
    fun u ⟨hu, Ou, Mu, Ku⟩ => ?_)
  obtain Pu : num u.mem B n aPa = num s.mem B n aPa := Ou.num (by simp) (by decide) (h.fit64 (by decide))
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mu]; exact mask_bit _)
    (show num u.mem B n aPa % 2 ≤ 1 by omega_arith) (bitOf_ok hu (by decide) (by decide)))
    fun v ⟨hv, Ov, Mv, Kv⟩ => ?_)
  rw [Pu, Mu] at Mv
  obtain Fv := Ou.trans Ov
  obtain Qv : num v.mem B n aQa = num s.mem B n aQa := Fv.num (by simp) (by decide) (h.fit64 (by decide))
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mv]; exact mask_bit _)
    (show num v.mem B n aQa % 2 ≤ 1 by omega_arith) (bitOf_ok hv (by decide) (by decide)))
    fun w ⟨hw, Ow, Mw, Kw⟩ => ?_)
  rw [Qv, Mv] at Mw
  obtain Fw := Fv.trans Ow
  obtain Ew : num w.mem B n aE = val32 s.mem B kEv 2 :=
    (Fw.num (by simp) (by decide) (h.fit64 (by decide))).trans loaded
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mw]; exact mask_bit _)
    (show num w.mem B n aE % 2 ≤ 1 by omega_arith) (bitOf_ok hw (by decide) (by decide)))
    fun a ⟨ha, Oa, Ma, Ka⟩ => ?_)
  rw [Ew, Mw] at Ma
  obtain Fa := Fw.trans Oa
  obtain Ea : val32 a.mem B kEv 2 = val32 s.mem B kEv 2 := maskFlag_preserves_e Fa
  refine WP.seq (WP.mono (withFlag_ok (by rw [Ma]; exact mask_bit _)
    (by split <;> omega_arith) (exponentUpper_ok ha)) fun b ⟨hb, Ob, Mb, Kb⟩ => ?_)
  rw [Ea, Ma] at Mb
  obtain Fb := Fa.trans Ob
  obtain Eb : num b.mem B n aE = val32 s.mem B kEv 2 :=
    (Fb.num (by simp) (by decide) (h.fit64 (by decide))).trans loaded
  refine WP.mono (exponentAtLeastThree_ok hb (by rw [Mb]; exact mask_bit _))
    fun t ⟨ht, Ot, Mt, Kt⟩ => ?_
  rw [Eb, Mb] at Mt
  refine ⟨ht, Fb.join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk]), ?_,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans
      ((Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans Kt))))⟩
  exact Mt.trans (Key.finalMask_cond _ _ _ _ _ _)

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # Complete native arithmetic after the small-private-exponent check -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Divisor.lean`, which only this module imported.
section

/-! # A safe CRT divisor, including zero factor predecessors -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aDen aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem divisorOf_ok {s : State} {B : Addr} {Z n input : Nat} (h : Ws s B Z n 32)
    (hi : input < 32) (ip : 16 ≤ input) (one : num s.mem B n aOne = 1) :
    WP isa (divisorOf input) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2, aDen] [sT, kFlag] s.mem t.mem ∧
      num t.mem B n aDen = (if num s.mem B n input = 0 then 1 else num s.mem B n input) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  obtain fi := h.fit64 hi
  obtain fo := h.fit64 (j := aOne) (by decide)
  unfold divisorOf seqs
  refine WP.seq (WP.mono (constant_ok h (by decide) (0 : BitVec 32))
    fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  change num u.mem B n aT1 = 0 at zero
  obtain Iu : num u.mem B n input = num s.mem B n input :=
    Ou.num (by simp only [List.mem_singleton]; unfold aT1; omega) (by simp) fi
  obtain oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by simp) fo).trans one
  refine WP.seq (WP.mono (eq_ok hu (by decide) hi (by decide)
    (by unfold aT2; omega) (by decide) (by decide)) fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  rw [Iu, zero] at flag
  obtain Iv : num v.mem B n input = num s.mem B n input :=
    (Ov.num (by simp only [List.mem_singleton]; unfold aT2; omega) (by decide) fi).trans Iu
  obtain oneV : num v.mem B n aOne = 1 :=
    (Ov.num (by decide) (by decide) fo).trans oneU
  obtain bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (sel_ok hv (by decide) hi (by decide) (by decide) bit (by right; decide))
    fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  refine ⟨ht, (Ou.join Ov (js := [aT1, aT2, aDen]) (ds := [sT, kFlag])).join Ot
    (js := [aT1, aT2, aDen]) (ds := [sT, kFlag]), ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  rw [selected, flag, Iv, oneV]
  by_cases I : num s.mem B n input = 0 <;> simp [I]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Crt.lean`, which only this module imported.
section

/-! # Compute both CRT exponents with safe fixed-schedule division -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aD aQm aPm aOne aDp aDq aDen kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (stageRanges stage_keep stage_preserves_num crtArrays crtDivisor)

theorem crtPart_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (one : num s.mem B n aOne = 1) :
    WP isa crtPart s fun t =>
      Ws t B Z n 32 ∧ Outs B (stageRanges n crtArrays) s.mem t.mem ∧
      num t.mem B n aDp = num s.mem B n aD % crtDivisor (num s.mem B n aPm) ∧
      num t.mem B n aDq = num s.mem B n aD % crtDivisor (num s.mem B n aQm) ∧
      slot t.mem B kOk = slot s.mem B kOk ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  obtain fd := h.fit64 (j := aD) (by decide)
  obtain fq := h.fit64 (j := aQm) (by decide)
  obtain fo := h.fit64 (j := aOne) (by decide)
  obtain fp := h.fit64 (j := aDp) (by decide)
  unfold crtPart VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (divisorOf_ok h (by decide) (by decide) one)
    fun u ⟨hu, Ou, divisorP, Ku⟩ => ?_)
  obtain frameU : Outs B (stageRanges n crtArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  obtain Du : num u.mem B n aD = num s.mem B n aD :=
    Ou.num (by decide) (by decide) fd
  obtain divP : 0 < num u.mem B n aDen := by rw [divisorP]; split <;> omega
  refine WP.seq (WP.mono (arrayDivision_ok hu (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) divP)
    fun v ⟨hv, Ov, _, P, Kv⟩ => ?_)
  rw [Du, divisorP] at P
  obtain frameV : Outs B (stageRanges n crtArrays) u.mem v.mem := stage_division (by decide) (by decide) Ov
  obtain prefixFrame := frameU.trans frameV
  obtain Qv : num v.mem B n aQm = num s.mem B n aQm :=
    stage_preserves_num (by decide) (by decide) fq prefixFrame
  obtain Dv : num v.mem B n aD = num s.mem B n aD :=
    stage_preserves_num (by decide) (by decide) fd prefixFrame
  obtain oneV : num v.mem B n aOne = 1 :=
    (stage_preserves_num (by decide) (by decide) fo prefixFrame).trans one
  refine WP.seq (WP.mono (divisorOf_ok hv (by decide) (by decide) oneV)
    fun w ⟨hw, Ow, divisorQ, Kw⟩ => ?_)
  rw [Qv] at divisorQ
  obtain frameW : Outs B (stageRanges n crtArrays) v.mem w.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ow
  obtain Dw : num w.mem B n aD = num s.mem B n aD :=
    (Ow.num (by decide) (by decide) fd).trans Dv
  obtain Pw : num w.mem B n aDp = num v.mem B n aDp := Ow.num (by decide) (by decide) fp
  obtain divQ : 0 < num w.mem B n aDen := by rw [divisorQ]; split <;> omega
  refine WP.mono (arrayDivision_ok hw (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) divQ)
    fun t ⟨ht, Ot, _, Q, Kt⟩ => ?_
  rw [Dw, divisorQ] at Q
  obtain frameT : Outs B (stageRanges n crtArrays) w.mem t.mem := stage_division (by decide) (by decide) Ot
  exact ⟨ht, (prefixFrame.trans frameW).trans frameT,
    ((arrayDivision_preserves_num (by decide) (by decide) (by decide) fp Ot).trans Pw).trans P,
    Q, (arrayDivision_preserves_slot (by decide) Ot).trans ((Ow.slot (by decide) (by decide)).trans
      ((arrayDivision_preserves_slot (by decide) Ov).trans (Ou.slot (by decide) (by decide)))),
    (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans Kt))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aPm aQm aOne aQi aN aE kEv kOk kFlag kStatus)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyPartResult keyPartArrays stageRanges stage_preserves_num
  stage_preserves_e stage_mono stage_keep safePrime mask_bit mask_ite_one)

theorem keyPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (bit : slot s.mem B kOk ≤ 1) (loaded : num s.mem B n aE = val32 s.mem B kEv 2)
    (one : num s.mem B n aOne = 1) :
    WP isa keyPart s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (stageRanges n keyPartArrays) s.mem t.mem ∧
      KeyPartResult B n s.mem t ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold keyPart seqs
  refine WP.seq (WP.mono (qinvPart_ok h width positive boundP boundQ bit)
    fun u ⟨hu, Ou, Mu, boundQi, congruence, Ku⟩ => ?_)
  obtain oneU : num u.mem B n aOne = 1 :=
    (h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans one
  obtain Du : num u.mem B n aD = num s.mem B n aD :=
    h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  obtain Pmu : num u.mem B n aPm = num s.mem B n aPm :=
    h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  obtain Qmu : num u.mem B n aQm = num s.mem B n aQm :=
    h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  obtain frameU : OutsS B (s.gpr .esp) (stageRanges n keyPartArrays) s.mem u.mem :=
    OutsS.lift (fun _ _ => stage_mono (by decide)) Ou
  refine WP.seq (WP.mono (crtPart_ok hu oneU) fun v ⟨hv, Ov, Dp, Dq, Mv, Kv⟩ => ?_)
  rw [Du, Pmu] at Dp
  rw [Du, Qmu] at Dq
  rw [Mu] at Mv
  obtain qiV : num v.mem B n aQi = num u.mem B n aQi :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ov
  obtain frameV : Outs B (stageRanges n keyPartArrays) u.mem v.mem := stage_mono (by decide) Ov
  obtain prefixFrame := frameU.trans (OutsS.of_outs frameV)
  obtain Pv : num v.mem B n aPa = num s.mem B n aPa :=
    h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  obtain Qv : num v.mem B n aQa = num s.mem B n aQa :=
    h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  refine WP.seq (WP.mono (primeProduct_ok hv width positive even (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [Pv]; exact boundP) (by rw [Qv]; exact boundQ))
    fun w ⟨hw, Ow, N, Kw⟩ => ?_)
  rw [Pv, Qv] at N
  obtain frameW : Outs B (stageRanges n keyPartArrays) v.mem w.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ow
  obtain fullPrefix := prefixFrame.trans (OutsS.of_outs frameW)
  obtain Pw : num w.mem B n aPa = num s.mem B n aPa :=
    h.read_num (by decide) fullPrefix (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  obtain Qw : num w.mem B n aQa = num s.mem B n aQa :=
    h.read_num (by decide) fullPrefix (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  obtain Ew : val32 w.mem B kEv 2 = val32 s.mem B kEv 2 := h.read_val32 (by decide) fullPrefix stage_preserves_e
  obtain loadedW : num w.mem B n aE = val32 w.mem B kEv 2 :=
    (h.read_num (by decide) fullPrefix (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans (loaded.trans Ew.symm)
  obtain Mw : slot w.mem B kOk = (if slot s.mem B kOk = 1 ∧
      Nat.gcd (num s.mem B n aQa) (safePrime (num s.mem B n aPa)) = 1 then 1 else 0) :=
    (Ow.slot (by decide) (by decide)).trans Mv
  refine WP.seq (WP.mono (finalMask_ok hw (by rw [Mw]; exact mask_bit _) loadedW)
    fun a ⟨ha, Oa, Ma, Ka⟩ => ?_)
  rw [Mw, N, Pw, Qw, Ew] at Ma
  simp only [mask_ite_one, and_assoc] at Ma
  refine WP.mono (saveSlot_ok ha (by decide) (by decide)) fun t ⟨ht, Ot, status, Kt⟩ => ?_
  obtain last : Keep B n [aT1, aT2] [kFlag, kOk, kStatus] w.mem t.mem :=
    Oa.join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk, kStatus])
  obtain tail : Keep B n [aN, aT1, aT2] (productScalars ++ [kFlag, kOk, kStatus]) v.mem t.mem :=
    Ow.join last (js := [aN, aT1, aT2]) (ds := (productScalars ++ [kFlag, kOk, kStatus]))
      (by decide) (by decide) (by decide) (by decide)
  obtain qiT : num t.mem B n aQi = num u.mem B n aQi :=
    (tail.num (by decide) (by decide) (h.fit64 (by decide))).trans qiV
  obtain frameA : Outs B (stageRanges n keyPartArrays) w.mem a.mem :=
    stage_keep (Nat.le_refl n) (by
      intro j hj
      left
      obtain H : ∀ j ∈ [aT1, aT2], j < 15 := by decide
      exact H j hj) (by decide) Oa
  obtain frameT : Outs B (stageRanges n keyPartArrays) a.mem t.mem :=
    stage_keep (Nat.le_refl n) (by simp) (by decide) Ot
  obtain maskT : slot t.mem B kOk = slot a.mem B kOk := Ot.slot (by decide) (by decide)
  refine ⟨ht, (fullPrefix.trans (OutsS.of_outs frameA)).trans (OutsS.of_outs frameT), ⟨?_, ?_, ?_, ?_, ?_, maskT.trans Ma, ?_⟩,
    Ku.trans (Kv.trans ((Kw.mono (by decide)).trans ((Ka.mono (by decide)).trans (Kt.mono (by decide)))))⟩
  · exact (last.num (by decide) (by decide) (h.fit64 (by decide))).trans N
  · exact (tail.num (by decide) (by decide) (h.fit64 (by decide))).trans Dp
  · exact (tail.num (by decide) (by decide) (h.fit64 (by decide))).trans Dq
  · rw [qiT]
    exact boundQi
  · rw [qiT]
    exact congruence
  · exact status.trans maskT.symm

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end


/-! # Complete native numeric RSA derivation, including all failure cases -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE aOne kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady CoreOutcome deriveArrays stageRanges stage_keep stage_mono
  stage_preserves_num stage_preserves_e)

theorem deriveLoaded_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (lower : 16 ≤ n) (upper : n ≤ 256)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa deriveLoaded s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (stageRanges n deriveArrays) s.mem t.mem ∧
      CoreOutcome B n (val32 s.mem B kEv 2) (num s.mem B n aPa) (num s.mem B n aQa) t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  obtain boundP' : num s.mem B n aPa < 2 ^ (16 * n) := by rw [show 16 * n = 32 * k by omega_using [width]]; exact boundP
  obtain boundQ' : num s.mem B n aQa < 2 ^ (16 * n) := by rw [show 16 * n = 32 * k by omega_using [width]]; exact boundQ
  unfold deriveLoaded
  refine WP.seq (WP.mono (prepareLoaded_ok h width positive even boundP boundQ zero one loaded)
    fun u ⟨hu, Ou, R, Ku⟩ => ?_)
  obtain frameU : OutsS B (s.gpr .esp) (stageRanges n deriveArrays) s.mem u.mem :=
    OutsS.lift (fun _ _ => stage_mono (by decide)) Ou
  obtain spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  refine WP.seq (WP.mono (smallMask_ok hu R.bit) fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  obtain ready := KeyReady.small hu.old R Ov
  obtain maskV : slot v.mem B kOk = slot u.mem B kOk := Ov.slot (by decide) (by simp)
  obtain DV : num v.mem B n aD = num u.mem B n aD := Ov.num (by decide) (by simp) (h.fit64 (by decide))
  obtain frameV : Outs B (stageRanges n deriveArrays) u.mem v.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by simp) Ov
  obtain branch : isa.eval .ne v = some (decide (slot u.mem B kOk = 1 ∧ num u.mem B n aD ≤ 2 ^ (16 * n))) := by
    change v.zf.map Bool.not = _
    change v.zf = some (decide (¬(slot u.mem B kOk = 1 ∧ num u.mem B n aD ≤ 2 ^ (16 * n)))) at flag
    rw [flag]
    by_cases small : slot u.mem B kOk = 1 ∧ num u.mem B n aD ≤ 2 ^ (16 * n) <;> simp [small]
  refine WP.ite _ branch (fun retryBit => ?_) (fun normalBit => ?_)
  · have small := of_decide_eq_true retryBit
    refine WP.mono (retry_ok hv) fun t ⟨ht, Ot, mask, status, Kt⟩ => ?_
    obtain frameT : Outs B (stageRanges n deriveArrays) v.mem t.mem :=
      stage_keep (Nat.le_refl n) (by simp) (by decide) Ot
    exact ⟨ht, (frameU.trans (OutsS.of_outs frameV)).trans (OutsS.of_outs frameT), R.retry small.1 small.2 mask status,
      Ku.trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))⟩
  · have notSmall : ¬(slot v.mem B kOk = 1 ∧ num v.mem B n aD ≤ 2 ^ (16 * n)) := by
      rw [maskV, DV]
      exact of_decide_eq_false normalBit
    obtain pBound : num v.mem B n aPa < 2 ^ (32 * k) := by
      rw [ready.pValue]
      exact Nat.max_lt.mpr ⟨boundP, boundQ⟩
    obtain qBound : num v.mem B n aQa < 2 ^ (32 * k) := by
      rw [ready.qValue]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
    refine WP.mono (keyPart_ok hv width positive even pBound qBound ready.bit
      (ready.loaded.trans ready.exponent.symm) ready.one) fun t ⟨ht, Ot, result, Kt⟩ => ?_
    obtain spV : v.gpr .esp = s.gpr .esp := by rw [Kv.1 .esp (by decide), spU]
    obtain frameT : OutsS B (s.gpr .esp) (stageRanges n deriveArrays) v.mem t.mem := by
      rw [← spV]
      exact OutsS.lift (fun _ _ => stage_mono (by decide)) Ot
    exact ⟨ht, (frameU.trans (OutsS.of_outs frameV)).trans frameT,
      KeyReady.part_of lower upper boundP' boundQ' ready notSmall
        (hv.read_num (by decide) Ot (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide))))
        (hv.read_num (by decide) Ot (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide))))
        (hv.read_num (by decide) Ot (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide))))
        (hv.read_val32 (by decide) Ot stage_preserves_e) result,
      Ku.trans ((Kv.mono (by decide)).trans Kt)⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.CorePair`, which only this module used -/

section

/-! # Two secret factor pairs reach the retry comparison with the same public state -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/DSelectTiming.lean`, which only this module imported.
section

/-! # Public exponent branches compose with secret native arithmetic -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key (kEv aE equalExponent parityExponent)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

structure ExponentPair (B : Addr) (Z n e : Nat) (s t : State) : Prop where
  left : Ws s B Z n 32
  right : Ws t B Z n 32
  agree : VG.X86.Taint.Agree runtimeTaint s t
  exponentLeft : val32 s.mem B kEv 2 = e
  exponentRight : val32 t.mem B kEv 2 = e
  loadedLeft : num s.mem B n aE = e
  loadedRight : num t.mem B n aE = e

def ExponentTest (B : Addr) (Z n e : Nat) (bit : Bool) (s t : State) : Prop :=
  ExponentPair B Z n e s t ∧ isa.eval .e s = some bit ∧ isa.eval .e t = some bit

theorem equalExponent_trace (B : Addr) (Z n e : Nat) (value : BitVec 32) :
    RelCT isa (ExponentPair B Z n e) (.block (equalExponent value))
      (ExponentTest B Z n e (decide (e = value.toNat))) := by
  have checked : Public (.block (equalExponent value)) := by
    refine ⟨(VG.Taint.hintOf taint runtimeTaint (Code.erase (.block (equalExponent 0) : Prog isa))),
        runtimeTaint, ?_, rfl⟩
    exact (check_of_erase_eq (.block (equalExponent value)) (.block (equalExponent 0) : Prog isa) runtimeTaint
      (VG.Taint.hintOf taint runtimeTaint (Code.erase (.block (equalExponent 0) : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := public_trace checked _ _ _ _ _ _ P.agree A C
  obtain ⟨hu, Mu, flagU, _⟩ := wp_result (equalExponent_ok P.left value) A
  obtain ⟨hv, Mv, flagV, _⟩ := wp_result (equalExponent_ok P.right value) C
  rw [P.exponentLeft] at flagU
  rw [P.exponentRight] at flagV
  exact ⟨trace, ⟨hu, hv, agree, by rw [Mu]; exact P.exponentLeft,
    by rw [Mv]; exact P.exponentRight, by rw [Mu]; exact P.loadedLeft, by rw [Mv]; exact P.loadedRight⟩,
    flagU, flagV⟩

theorem parityExponent_trace (B : Addr) (Z n e : Nat) :
    RelCT isa (ExponentPair B Z n e) (.block parityExponent)
      (ExponentTest B Z n e (decide (e % 2 = 0))) := by
  have checked : Public (.block parityExponent) := ⟨.block [], runtimeTaint, rfl, rfl⟩
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := public_trace checked _ _ _ _ _ _ P.agree A C
  obtain ⟨hu, Mu, flagU, _⟩ := wp_result (parityExponent_ok P.left) A
  obtain ⟨hv, Mv, flagV, _⟩ := wp_result (parityExponent_ok P.right) C
  rw [P.exponentLeft] at flagU
  rw [P.exponentRight] at flagV
  exact ⟨trace, ⟨hu, hv, agree, by rw [Mu]; exact P.exponentLeft,
    by rw [Mv]; exact P.exponentRight, by rw [Mu]; exact P.loadedLeft, by rw [Mv]; exact P.loadedRight⟩,
    flagU, flagV⟩

/-- A public branch on the exponent, each side related when it is the one taken. -/
theorem exponent_branch_trace {B : Addr} {Z n e : Nat} {bit : Bool} {th el : Prog isa}
    (first : bit = true → RelCT isa (ExponentPair B Z n e) th (VG.X86.Taint.Agree runtimeTaint))
    (second : bit = false → RelCT isa (ExponentPair B Z n e) el (VG.X86.Taint.Agree runtimeTaint)) :
    RelCT isa (ExponentTest B Z n e bit) (.ite .e th el) (VG.X86.Taint.Agree runtimeTaint) := by
  apply RelCT.ite (fun _ _ P => P.2.1.trans P.2.2.symm)
  · intro s t tr ur u v P
    have taken : bit = true := by
      have := P.1.2.1.symm.trans P.2
      simpa using this
    exact first taken s t tr ur u v P.1.1
  · intro s t tr ur u v P
    have taken : bit = false := by
      have := P.1.2.1.symm.trans P.2
      simpa using this
    exact second taken s t tr ur u v P.1.1

theorem dSelect_trace (B : Addr) (Z n e : Nat) :
    RelCT isa (ExponentPair B Z n e) dSelect (VG.X86.Taint.Agree runtimeTaint) := by
  have even := (dEven_trace B Z n).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) => ⟨P.left, P.right, P.agree⟩) (fun _ _ P => P)
  have one := (public_trace dOne_public).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) => P.agree) (fun _ _ P => P)
  have zero := (public_trace dZero_public).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) => P.agree) (fun _ _ P => P)
  unfold dSelect
  refine RelCT.seq (equalExponent_trace B Z n e 0) (exponent_branch_trace (fun _ => zero) fun e0 => ?_)
  refine RelCT.seq (equalExponent_trace B Z n e 1) (exponent_branch_trace (fun _ => one) fun e1 => ?_)
  refine RelCT.seq (parityExponent_trace B Z n e) (exponent_branch_trace (fun _ => even) fun eo => ?_)
  have ne0 : e ≠ 0 := by simpa using e0
  have ne1 : e ≠ 1 := by simpa using e1
  have odd : e % 2 = 1 := by simp at eo; omega
  exact (dOdd_trace B Z n e (by omega) odd).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) =>
      ⟨⟨P.left, P.exponentLeft, P.loadedLeft⟩, ⟨P.right, P.exponentRight, P.loadedRight⟩, P.agree⟩)
    (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/PrepareExponent.lean`, which only this module imported.
section

/-! # Factor preparation retains the imported public exponent before branching -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aOne aE kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (stageRanges prepareArrays stage_keep stage_mono stage_preserves_e
  stage_preserves_num)

theorem beforeExponent_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1) :
    WP isa (.seq primes lcmPart) s fun t =>
      Ws t B Z n 32 ∧ val32 t.mem B kEv 2 = val32 s.mem B kEv 2 ∧ num t.mem B n aE = num s.mem B n aE := by
  have small : k ≤ n := by omega
  have pBound : max (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) := Nat.max_lt.mpr ⟨boundP, boundQ⟩
  have qBound : min (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) :=
    Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
  refine WP.seq (WP.mono (primes_ok h width positive even boundP boundQ zero one)
    fun u ⟨hu, Ou, _, _, Pm, Qm, product, Ku⟩ => ?_)
  have oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans one
  have frameU : Outs B (stageRanges n prepareArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  refine WP.mono (lcmPart_ok hu width positive
    (by rw [Pm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) pBound)
    (by rw [Qm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) qBound) product oneU)
    fun t ⟨ht, Ot, _, _⟩ => ?_
  have spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  have frameT : OutsS B (s.gpr .esp) (stageRanges n prepareArrays) u.mem t.mem := by
    rw [← spU]
    exact OutsS.lift (fun _ _ O => stage_mono (by decide) (lcm_stage_frame small O)) Ot
  exact ⟨ht, h.read_val32 (by decide) ((OutsS.of_outs frameU).trans frameT) stage_preserves_e,
    h.read_num (by decide) ((OutsS.of_outs frameU).trans frameT)
      (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/PrepareTiming.lean`, which only this module imported.
section

/-! # Sorted factors and LCM feed only the public exponent into control flow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aOne aE kEv aPm aQm aPhi)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

structure Preparation (B : Addr) (Z n k e : Nat) (s : State) : Prop where
  workspace : Ws s B Z n 32
  pBound : num s.mem B n aPa < 2 ^ (32 * k)
  qBound : num s.mem B n aQa < 2 ^ (32 * k)
  zero : num s.mem B n aZero = 0
  one : num s.mem B n aOne = 1
  exponent : val32 s.mem B kEv 2 = e
  loaded : num s.mem B n aE = e

def PreparationPair (B : Addr) (Z n k e : Nat) (s t : State) : Prop :=
  Preparation B Z n k e s ∧ Preparation B Z n k e t ∧ VG.X86.Taint.Agree runtimeTaint s t

theorem beforeExponent_trace (B : Addr) (Z n k e : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0) :
    RelCT isa (PreparationPair B Z n k e) (.seq primes lcmPart) (VG.X86.Taint.Agree runtimeTaint) := by
  refine RelCT.seq (step_trace (Q := LcmStart B Z n k) primes_public fun s P =>
    WP.mono (primes_ok P.workspace width positive even P.pBound P.qBound P.zero P.one)
      fun u ⟨hu, _, _, _, Pm, Qm, product, _⟩ => ?_) (lcm_trace B Z n k width positive)
  refine ⟨hu, ?_, ?_, product⟩
  · rw [Pm]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.max_lt.mpr ⟨P.pBound, P.qBound⟩)
  · rw [Qm]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt (Nat.min_le_left ..) P.pBound)

theorem prepareLoaded_trace (B : Addr) (Z n k e : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0) :
    RelCT isa (PreparationPair B Z n k e) prepareLoaded
      (VG.X86.Taint.Agree runtimeTaint) := by
  intro s t tr ur u v P A C
  obtain ⟨Ps, Pt, agree⟩ := P
  unfold prepareLoaded seqs at A C
  cases A with
  | seq Ap Ar =>
    cases Ar with
    | seq Al Ad =>
      cases C with
      | seq Cp Cr =>
        cases Cr with
        | seq Cl Cd =>
          have leftPrefix := Exec.seq Ap Al
          have rightPrefix := Exec.seq Cp Cl
          obtain ⟨prefixTrace, prefixAgree⟩ :=
            beforeExponent_trace B Z n k e width positive even _ _ _ _ _ _ ⟨Ps, Pt, agree⟩ leftPrefix rightPrefix
          obtain ⟨leftWs, leftE, leftL⟩ := wp_result
            (beforeExponent_ok Ps.workspace width positive even Ps.pBound Ps.qBound Ps.zero Ps.one) leftPrefix
          obtain ⟨rightWs, rightE, rightL⟩ := wp_result
            (beforeExponent_ok Pt.workspace width positive even Pt.pBound Pt.qBound Pt.zero Pt.one) rightPrefix
          obtain ⟨lastTrace, finalAgree⟩ := dSelect_trace B Z n e _ _ _ _ _ _
            ⟨leftWs, rightWs, prefixAgree, leftE.trans Ps.exponent, rightE.trans Pt.exponent,
              leftL.trans Ps.loaded, rightL.trans Pt.loaded⟩ Ad Cd
          refine ⟨?_, finalAgree⟩
          simp only [← List.append_assoc, prefixTrace, lastTrace]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady)

structure CoreStart (B : Addr) (Z n k e p q : Nat) (s : State) : Prop extends Preparation B Z n k e s where
  pValue : num s.mem B n aPa = p
  qValue : num s.mem B n aQa = q

structure ReadyPair (B : Addr) (Z n e p q p' q' : Nat) (s t : State) : Prop where
  left : Ws s B Z n 32
  right : Ws t B Z n 32
  agree : VG.X86.Taint.Agree runtimeTaint s t
  leftReady : KeyReady B n e p q s.mem
  rightReady : KeyReady B n e p' q' t.mem

theorem prepareReady_trace (B : Addr) (Z n k e p q p' q' : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0) :
    RelCT isa (fun s t => CoreStart B Z n k e p q s ∧ CoreStart B Z n k e p' q' t ∧
      VG.X86.Taint.Agree runtimeTaint s t)
      prepareLoaded (ReadyPair B Z n e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨Ps, Pt, agree⟩ := P
  obtain ⟨trace, finalAgree⟩ := prepareLoaded_trace B Z n k e width positive even
    _ _ _ _ _ _ ⟨Ps.toPreparation, Pt.toPreparation, agree⟩ A C
  obtain ⟨leftWs, _, leftReady, _⟩ := wp_result
    (prepareLoaded_ok Ps.workspace width positive even Ps.pBound Ps.qBound Ps.zero Ps.one
      (Ps.loaded.trans Ps.exponent.symm)) A
  obtain ⟨rightWs, _, rightReady, _⟩ := wp_result
    (prepareLoaded_ok Pt.workspace width positive even Pt.pBound Pt.qBound Pt.zero Pt.one
      (Pt.loaded.trans Pt.exponent.symm)) C
  rw [Ps.exponent, Ps.pValue, Ps.qValue] at leftReady
  rw [Pt.exponent, Pt.pValue, Pt.qValue] at rightReady
  exact ⟨trace, leftWs, rightWs, finalAgree, leftReady, rightReady⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # The shared arithmetic trace is unchanged by the caller's wider permissions -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/RetryTiming.lean`, which only this module imported.
section

/-! # The native retry branch is public through the shared released result -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady)

def RetryTest (B : Addr) (Z n e p q p' q' : Nat) (s t : State) : Prop :=
  ReadyPair B Z n e p q p' q' s t ∧ isa.eval .ne s = isa.eval .ne t

theorem retry_eval {B : Addr} {n : Nat} {m : Mem} {s : State}
    (flag : s.zf = some (decide (¬(slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n))))) :
    isa.eval .ne s = some (decide (slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n))) := by
  change s.zf.map Bool.not = _
  rw [flag]
  by_cases small : slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n) <;> simp [small]

theorem smallMask_trace (B : Addr) (Z n e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p' q' = .inr ())) :
    RelCT isa (ReadyPair B Z n e p q p' q') smallMask (RetryTest B Z n e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := public_trace smallMask_public _ _ _ _ _ _ P.agree A C
  obtain ⟨leftWs, leftFrame, leftFlag, _⟩ := wp_result (smallMask_ok P.left P.leftReady.bit) A
  obtain ⟨rightWs, rightFrame, rightFlag, _⟩ := wp_result (smallMask_ok P.right P.rightReady.bit) C
  have leftEval := retry_eval leftFlag
  have rightEval := retry_eval rightFlag
  refine ⟨trace, ⟨leftWs, rightWs, agree, P.leftReady.small P.left.old leftFrame,
    P.rightReady.small P.right.old rightFrame⟩, ?_⟩
  rw [leftEval, rightEval]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact P.leftReady.retry_iff.trans (release.trans P.rightReady.retry_iff.symm)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/DeriveTiming.lean`, which only this module imported.
section

/-! # Complete native numeric key derivation is constant time modulo the released retry status -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady)

theorem deriveLoaded_trace (B : Addr) (Z n k e p q p' q' : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p' q' = .inr ())) :
    RelCT isa (fun s t => CoreStart B Z n k e p q s ∧ CoreStart B Z n k e p' q' t ∧
      VG.X86.Taint.Agree runtimeTaint s t)
      deriveLoaded (VG.X86.Taint.Agree runtimeTaint) := by
  intro s t tr ur u v P E F
  have bound₁ : max p q < 2 ^ (32 * k) := by
    rw [← P.1.pValue, ← P.1.qValue]
    exact Nat.max_lt.mpr ⟨P.1.pBound, P.1.qBound⟩
  have bound₂ : max p' q' < 2 ^ (32 * k) := by
    rw [← P.2.1.pValue, ← P.2.1.qValue]
    exact Nat.max_lt.mpr ⟨P.2.1.pBound, P.2.1.qBound⟩
  refine (?_ : RelCT isa (fun s t => CoreStart B Z n k e p q s ∧ CoreStart B Z n k e p' q' t ∧
    VG.X86.Taint.Agree runtimeTaint s t) deriveLoaded (VG.X86.Taint.Agree runtimeTaint)) s t tr ur u v P E F
  unfold deriveLoaded
  apply RelCT.seq (prepareReady_trace B Z n k e p q p' q' width positive even)
  apply RelCT.seq (smallMask_trace B Z n e p q p' q' release)
  apply RelCT.ite (fun _ _ P => P.2)
  · exact (public_trace retry_public).mono (fun _ _ P => P.1.1.agree) (fun _ _ P => P)
  · exact (keyPart_trace B Z n k width positive).mono (fun _ _ P =>
      ⟨⟨P.1.1.left, by rw [P.1.1.leftReady.pValue]; exact bound₁⟩,
        ⟨P.1.1.right, by rw [P.1.1.rightReady.pValue]; exact bound₂⟩, P.1.1.agree⟩) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86
open VG.Proof.Mont.X86.Dynamic (workspaceTaint)
open VG.Proof.RsaKeyGen.X86.Key (Environment Input ImportedPair OutputPair core_mask_bit)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

structure RuntimeImported (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop where
  imported : ImportedPair E e p q p' q' s t
  left : Ws s E.base E.size E.n 32
  right : Ws t E.base E.size E.n 32
  leftArgs : Context E.base E.size sp E.argument s
  rightArgs : Context E.base E.size sp E.argument t

theorem coreStart {s : State} {B : Addr} {Z n k e p q : Nat} (H : Ws s B Z n 32)
    (C : VG.Proof.RsaKeyGen.X86.Key.CoreStart B Z n k e p q s) : CoreStart B Z n k e p q s :=
  ⟨⟨H, C.pBound, C.qBound, C.zero, C.one, C.exponent, C.loaded⟩, C.pValue, C.qValue⟩

theorem deriveOutput_ok {E : Environment} {s : State} {e p q : Nat} (h : Input E s)
    (H : Ws s E.base E.size E.n 32) (C : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p q s) :
    WP isa VG.Impl.RsaKeyGen.X86.KeyRuntime.deriveLoaded s fun t => Input E t ∧
      VG.Proof.Rsa.X86.Keys.slot t.mem E.base VG.Impl.RsaKeyGen.X86.Key.kOk ≤ 1 ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  refine WP.mono (deriveLoaded_ok H widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1 widths.1 widths.2.1
    C.pBound C.qBound C.zero C.one (C.loaded.trans C.exponent.symm))
    fun t ⟨ht, O, result, K⟩ => ?_
  exact ⟨input_afterStage h H ht.old K O, core_mask_bit result, K⟩

theorem deriveOutput_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (RuntimeImported E sp e p q p' q') VG.Impl.RsaKeyGen.X86.KeyRuntime.deriveLoaded (OutputPair E) := by
  intro s t tr ur u v P A C
  have widths := P.imported.inputs.left.valid.widths
  have runS := deriveLoaded_ok P.left.readonly widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
    widths.1 widths.2.1 P.imported.left.pBound P.imported.left.qBound P.imported.left.zero
    P.imported.left.one (P.imported.left.loaded.trans P.imported.left.exponent.symm)
  have runT := deriveLoaded_ok P.right.readonly widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
    widths.1 widths.2.1 P.imported.right.pBound P.imported.right.qBound P.imported.right.zero
    P.imported.right.one (P.imported.right.loaded.trans P.imported.right.exponent.symm)
  obtain ⟨u', AS⟩ := trace_readonly_of_wp P.left runS A
  obtain ⟨v', CT⟩ := trace_readonly_of_wp P.right runT C
  have oldS : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p q
      (readonly s E.base E.size) :=
    { P.imported.left with workspace := P.left.readonly.old }
  have oldT : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p' q'
      (readonly t E.base E.size) :=
    { P.imported.right with workspace := P.right.readonly.old }
  have agree := readonly_agree P.leftArgs P.rightArgs P.left.hdr_le
    (P.imported.agree.reg (by rfl : VG.X86.Taint.pub (workspaceTaint true) .esi = true))
  obtain ⟨trace, agreeOut⟩ := deriveLoaded_trace E.base E.size E.n E.k e p q p' q'
    widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1 release _ _ _ _ _ _
    ⟨coreStart P.left.readonly oldS, coreStart P.right.readonly oldT, agree⟩ AS CT
  obtain ⟨sRead, sWrite⟩ := readonly_covers P.left
  obtain ⟨tRead, tWrite⟩ := readonly_covers P.right
  have widenedS := VG.X86.Exec.widen AS sRead sWrite
  have widenedT := VG.X86.Exec.widen CT tRead tWrite
  simp only [readonly, State.withRegions_withRegions, State.withRegions_self] at widenedS widenedT
  have endS := (Exec.det A widenedS).2
  have endT := (Exec.det C widenedT).2
  have publicOut : VG.X86.Taint.Agree (workspaceTaint true) u v := by
    change VG.X86.Taint.Agree (τr [.edi, .esi]) u v
    apply agree_regs
    intro r hr
    rw [endS, endT]
    change u'.gpr r = v'.gpr r
    apply agreeOut.reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  obtain ⟨leftInput, leftBit, leftKeeps⟩ := wp_result (deriveOutput_ok P.imported.inputs.left P.left P.imported.left) A
  obtain ⟨rightInput, rightBit, rightKeeps⟩ := wp_result (deriveOutput_ok P.imported.inputs.right P.right P.imported.right) C
  refine ⟨trace, ⟨leftInput, rightInput, ?_⟩, publicOut, leftBit, rightBit⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.imported.inputs.stack

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # The two runs' starting states: inputs, workspaces and argument records -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment SizedStart OutputPair)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

structure RuntimeStart (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop where
  start : SizedStart E e p q p' q' s t
  left : Ws s E.base E.size E.n 32
  right : Ws t E.base E.size E.n 32
  leftArgs : Context E.base E.size sp E.argument s
  rightArgs : Context E.base E.size sp E.argument t

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.LoadInputs`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.LoadExponent`, which this module and modules that import it used -/

section

/-! # The public exponent imported through its argument pointer and length -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (arr S num)
open VG.Proof.Bignum.X86 (byteAddr)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (kEv aE)

/-- `Key.loadExponent_ok` with the pointer and length from arguments 14 and 15. -/
theorem loadExponent_ok {s : State} {B : Addr} {Z n len : Nat} {p : BitVec 32}
    (h : Ws s B Z n 32) (positive : 0 < len) (bound : len ≤ 8)
    (pointer : VG.Proof.Bignum.X86.CallArgument s B Z 18 p)
    (length : VG.Proof.Bignum.X86.CallArgument s B Z 19 (BitVec.ofNat 32 len))
    (fit : p.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (byteAddr p) len)
    (separate : Region.Disjoint ⟨byteAddr p, len⟩ ⟨off B kEv, 8⟩) :
    WP isa loadExponent s fun t =>
      Ws t B Z n 32 ∧ Outs B (VG.Proof.RsaKeyGen.X86.Key.loadExponentRanges n) s.mem t.mem ∧
      val32 t.mem B kEv 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr p) len) ∧
      num t.mem B n aE = val32 t.mem B kEv 2 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have head := h.hdr_le
  have nBound := h.old.wle
  have size := h.size
  unfold loadExponent VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (wp_movS pointer.readSrc fun u U _ => ?_)
  refine wp_movS (length.keep U.keeps (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)).readSrc
    fun v V _ => WP.block_nil ?_
  have K : Keeps [.esi, .ecx] s v := (U.keeps.mono (by decide)).trans (V.keeps.mono (by decide))
  have memory : v.mem = s.mem := V.mem.trans U.mem
  have hv := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  have source : v.gpr .esi = p := by rw [V.other _ (by decide), U.gpr]
  have count : v.gpr .ecx = BitVec.ofNat 32 len := V.gpr
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.loadBE_ok hv.old.workspace (by decide)
    (by unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega_using [head]) positive bound (by rw [source]; exact fit) count
    (by rw [source, K.2.1, K.2.2]; exact readable) (by rw [source]; exact separate))
    fun w ⟨value, Ow, Kw⟩ => ?_)
  have hw := hv.keep Kw (Ow.mono (Nat.zero_le _) (by unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega_using [head]))
  rw [memory, source, wordsVal_eq_val32] at value
  change val32 w.mem B kEv 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr p) len) at value
  have eFit := h.arr_fit (j := aE) (by decide)
  unfold S at eFit
  have eStart := VG.Proof.Rsa.X86.Keys.arr_end (w := n) (show 0 < aE by decide)
  have hdrArr : VG.Impl.Rsa.X86.Keys.hdr ≤ arr n 0 := by unfold VG.Proof.Rsa.X86.Keys.arr; omega_using []
  refine WP.mono (widen_ok hw .exponent (arr aE) (.fixed kEv) (by simp only [Width.words]; omega_using [size])
    (by change arr n aE + _ ≤ Z; omega_using [eFit])
    (by change kEv + 4 * 2 ≤ Z; unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega_using [head])
    (Or.inl (by change kEv + 4 * 2 ≤ arr n aE; unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega_using [eStart, hdrArr])))
    fun t ⟨ht, Ot, _, copied, Kt⟩ => ?_
  change Outside B (arr n aE) (4 * (n + 2)) w.mem t.mem at Ot
  change val32 t.mem B (arr n aE) n = val32 w.mem B kEv 2 at copied
  have exponent : val32 t.mem B kEv 2 = val32 w.mem B kEv 2 :=
    Ot.val32 (Or.inl (by unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega_using [eStart, hdrArr])) (by decide)
  refine ⟨ht, ?_, exponent.trans value, copied.trans exponent.symm,
    (K.mono (by decide)).trans (Kw.trans (Kt.mono (by decide)))⟩
  have first : Outs B (VG.Proof.RsaKeyGen.X86.Key.loadExponentRanges n) s.mem w.mem := by
    rw [← memory]
    exact Outs.of_outside Ow (by simp [VG.Proof.RsaKeyGen.X86.Key.loadExponentRanges])
  exact first.trans (Outs.of_outside (Ot.mono (o' := arr n aE) (n' := S n) (Nat.le_refl _) (by unfold S; omega_using []))
    (by simp [VG.Proof.RsaKeyGen.X86.Key.loadExponentRanges]))

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.LoadPrime`, which this module and modules that import it used -/

section

/-! # A prime imported at the run-time width, through its argument pointer -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (arr S num)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt (PtrAt)

/-- `Key.loadPrime_ok` for the prime at argument `i`. -/
theorem loadPrime_ok {s : State} {B : Addr} {Z n k i out : Nat} {p : BitVec 32}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (ho : out < 32) (persistent : 15 ≤ out)
    (A : VG.Proof.Bignum.X86.CallArgument s B Z (i + 4) p)
    (fit : p.toNat + 4 * k ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (p.setWidth 64) (4 * k))
    (separate : Region.Disjoint ⟨p.setWidth 64, 4 * k⟩ ⟨B, Z⟩) :
    WP isa (loadPrime i out) s fun t =>
      Ws t B Z n 32 ∧ Outs B (VG.Proof.RsaKeyGen.X86.Key.loadPrimeRanges n k out) s.mem t.mem ∧
      num t.mem B n out = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (4 * k)) ∧
      num t.mem B n out < 2 ^ (32 * k) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  obtain small : k ≤ n := by omega_using [width]
  have nBound := h.old.wle
  obtain words : Width.prime.words n = k := by simp only [Width.words]; omega_using [width]
  obtain space : arr n 0 + 4 * k ≤ Z := by
    obtain F := h.arr_fit (j := 0) (by decide)
    unfold S at F
    omega_using [small, F]
  have noWrap := h.old.workspace.nowrap
  unfold loadPrime VG.Impl.Rsa.X86.Keys.seqs
  simp only [List.cons_append]
  refine WP.seq (wp_movS A.readSrc fun u U _ => ?_)
  obtain hu := h.keep U.keeps (by rw [U.mem]; exact Outside.refl _ _ _ _)
  refine hu.ptr_ok (arr 0) (r := .ebx) (t := .edx) (by decide) (by decide) (by change arr n 0 < _; omega_using [positive, space, noWrap])
    fun a Ka ma Pa => ?_
  obtain ha := hu.keep Ka (by rw [ma]; exact Outside.refl _ _ _ _)
  refine ha.bytes_ok .prime .ecx fun b Kb mb eb => ?_
  refine wp_addS rfl fun c Cc _ => wp_subS rfl fun d D _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide)
    fun e Ee => WP.block_nil ?_
  obtain Ke : Keeps [.esi, .ebx, .edx, .ecx] s e :=
    (((U.keeps.mono (by decide)).trans (Ka.mono (by decide))).trans (Kb.mono (by decide))).trans
      (((Cc.keeps.mono (by decide)).trans (D.keeps.mono (by decide))).trans (Ee.keeps.mono (by decide)))
  obtain me : e.mem = s.mem := by rw [Ee.mem, D.mem, Cc.mem, mb, ma, U.mem]
  obtain he := h.keep Ke (by rw [me]; exact Outside.refl _ _ _ _)
  obtain ebx_b : PtrAt b B .ebx (arr n 0) := by rw [PtrAt, Kb.1 _ (by decide)]; exact Pa
  obtain ecx_b : (b.gpr .ecx).toNat = 4 * k := by rw [eb, words]
  have edi_s : (s.gpr .edi).toNat = B.toNat := h.old.workspace.edi_toNat
  obtain edi_e : e.gpr .edi = s.gpr .edi := Ke.1 _ (by decide)
  -- The import's geometry: from `p` to array 0, `k` words.
  obtain context := VG.Proof.RsaKeyGen.X86.Import.context_workspace (out := arr n 0) he.old.workspace positive space fit
    (by rw [Ke.2.1, Ke.2.2]; exact readable) separate
  obtain source : e.gpr .esi = (⟨p, e.gpr .edi + BitVec.ofNat 32 (arr n 0), k⟩ : VG.Proof.RsaKeyGen.X86.Import.Geometry).sourcePtr 0 := by
    rw [Ee.other _ (by decide), D.other _ (by decide), Cc.other _ (by decide), Kb.1 _ (by decide), Ka.1 _ (by decide),
      U.gpr]
    simp only [VG.Proof.RsaKeyGen.X86.Import.Geometry.sourcePtr, Nat.mul_zero, BitVec.add_zero]
  obtain destination : e.gpr .ebx = (⟨p, e.gpr .edi + BitVec.ofNat 32 (arr n 0), k⟩ : VG.Proof.RsaKeyGen.X86.Import.Geometry).destPtr 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [Ee.other _ (by decide), D.gpr, Cc.gpr]
    unfold VG.Proof.RsaKeyGen.X86.Import.Geometry.destPtr
    rw [Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.sub_zero, BitVec.toNat_sub, BitVec.toNat_add,
      BitVec.toNat_add, BitVec.toNat_add, ebx_b, ecx_b, edi_e, edi_s, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (4 : BitVec 32).toNat = 4 from rfl]
    dsimp only
    omega_using [positive]
  obtain count : e.gpr .ecx = BitVec.ofNat 32 k := by
    apply BitVec.eq_of_toNat_eq
    rw [Ee.gpr, BitVec.toNat_ushiftRight, D.other _ (by decide), Cc.other _ (by decide), ecx_b,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [fit])]
    omega_using []
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.Import.code_ok context source destination count)
    fun v T => ?_)
  have value := T.os2ip
  have F := T.frame
  have Kv := T.keeps
  obtain dest : (e.gpr .edi + BitVec.ofNat 32 (arr n 0)).setWidth 64 = off B (arr n 0) :=
    he.old.workspace.ea (d := arr n 0) (by omega_using [positive, space])
  change (v.mem.read ((e.gpr .edi + BitVec.ofNat 32 (arr n 0)).setWidth 64) (4 * k)).toNat =
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt e.mem (p.setWidth 64) (4 * k)) at value
  rw [dest, me] at value
  obtain imported : val32 v.mem B (arr n 0) k = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (4 * k)) := by
    rw [← VG.Proof.Bignum.read_eq_val32]
    exact value
  change Frame [⟨(e.gpr .edi + BitVec.ofNat 32 (arr n 0)).setWidth 64, 4 * k⟩] e.mem v.mem at F
  rw [dest, me] at F
  obtain Ov : Outside B (arr n 0) (4 * k) s.mem v.mem := VG.Proof.RsaKeyGen.frame_outside F (by omega_using [space, noWrap])
  obtain Kev : Keeps [.eax, .ebx, .ecx, .edx, .esi] s v := (Ke.mono (by decide)).trans (Kv.mono (by decide))
  obtain hv := h.keep Kev (Ov.mono (Nat.zero_le _) (by omega_using [space]))
  obtain before : arr n 0 + 4 * k ≤ arr n out := by
    obtain H := VG.Proof.Rsa.X86.Keys.arr_end (w := n) (show 0 < out by omega_using [persistent])
    unfold S at H
    omega_using [small, H]
  obtain outFit := h.arr_fit (j := out) ho
  unfold S at outFit
  refine WP.mono (widen_ok hv .prime (arr out) (arr 0) (by rw [words]; exact small)
    (by change arr n out + _ ≤ Z; omega_using [outFit]) (by change arr n 0 + _ ≤ Z; rw [words]; exact space)
    (Or.inl (by change arr n 0 + _ ≤ arr n out; rw [words]; exact before)))
    fun t ⟨ht, Ot, _, copied, Kt⟩ => ?_
  change Outside B (arr n out) (4 * (n + 2)) v.mem t.mem at Ot
  change val32 t.mem B (arr n out) n = val32 v.mem B (arr n 0) (Width.prime.words n) at copied
  rw [words] at copied
  refine ⟨ht, ?_, copied.trans imported, ?_,
    (Kev.mono (by decide)).trans (Kt.mono (by decide))⟩
  · exact (Outs.of_outside Ov (by simp [VG.Proof.RsaKeyGen.X86.Key.loadPrimeRanges])).trans
      (Outs.of_outside (Ot.mono (o' := arr n out) (n' := S n) (Nat.le_refl _) (by unfold S; omega_using []))
        (by simp [VG.Proof.RsaKeyGen.X86.Key.loadPrimeRanges]))
  · change val32 t.mem B (arr n out) n < _
    rw [copied]
    exact val32_lt _ _ _ _

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.ClearInputs`, which this module and modules that import it used -/

section

/-! # Every array cleared and one set, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (arr S num)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (aOne)

/-- `clearInputs`: every array cleared and `aOne` set to 1, at the run-time width. -/
theorem clearInputs_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa clearInputs s fun t =>
      Ws t B Z n 32 ∧ Outs B [(VG.Impl.Rsa.X86.Keys.hdr, 32 * S n)] s.mem t.mem ∧
      num t.mem B n aOne = 1 ∧ (∀ j, j < 32 → j ≠ aOne → num t.mem B n j = 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  have oneFit := h.arr_fit (j := aOne) (by decide)
  unfold S at oneFit
  unfold clearInputs
  refine WP.seq (WP.mono (clear_ok h .modulus (by decide) (k := 32) (by decide) (by decide))
    fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  have lowZero (j : Nat) (hj : j < 32) : num u.mem B n j = 0 := by
    have H := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zero j hj) (a := 0) (c := n) (by simp only [Width.words]; omega_using [])
    simp only [Nat.mul_zero, Nat.add_zero] at H
    exact H
  refine WP.mono (small_ok hu .modulus 1 (j := aOne) (by change arr n aOne + _ ≤ Z; simp only [Width.words]; omega_using [oneFit]))
    fun t ⟨ht, Ot, value, Kt⟩ => ?_
  change Outside B (arr n aOne) (4 * (n + 2)) u.mem t.mem at Ot
  change val32 t.mem B (arr n aOne) (n + 2) = 1 at value
  have outer : Outside B VG.Impl.Rsa.X86.Keys.hdr (4 * (32 * (n + 2))) s.mem u.mem := by
    simpa only [Width.words] using Ou
  refine ⟨ht, ?_, ?_, ?_, Ku.trans (Kt.mono (by decide))⟩
  · refine (Outs.of_outside (outer.mono (Nat.le_refl _) (by unfold S; omega_using [])) (List.mem_singleton_self _)).trans
      (Outs.of_outside (Ot.mono (o' := VG.Impl.Rsa.X86.Keys.hdr) (n' := 32 * S n) ?_ ?_) (List.mem_singleton_self _))
    · unfold VG.Proof.Rsa.X86.Keys.arr; omega_using []
    · unfold VG.Proof.Rsa.X86.Keys.arr S aOne; omega_using []
  · change val32 t.mem B (arr n aOne) n = 1
    rw [VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_using [] : n ≤ n + 2)
      (by rw [value]; exact Nat.one_lt_two_pow (by have := h.size; omega_using [this])), value]
  · intro j hj different
    change val32 t.mem B (arr n j) n = 0
    have D := VG.Proof.Rsa.X86.Keys.arr_disj (w := n) different
    have fit := h.arr_fit hj
    unfold S at D fit
    rw [Ot.val32 (by omega_using [D]) (by omega_using [nowrap, fit])]
    exact lowZero j hj

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyLoadFrames`, which this module and modules that import it used -/

section

/-! # Import frames preserve initialized constants and other persistent inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem loadPrime_preserves_num {m m' : Mem} {B : Addr} {n k out j : Nat}
    (width : k ≤ n) (positive : 1 ≤ j) (different : j ≠ out) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (loadPrimeRanges n k out) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega_using [fit])
  intro r hr
  simp only [loadPrimeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have last := arr_end (w := n) (show 0 < j by omega_using [positive])
    unfold S at last
    exact Or.inr (by omega_using [width, last])
  · have D := arr_disj (w := n) different
    simp only at D ⊢
    unfold S at D ⊢
    omega_using [D]

theorem loadPrime_stage_frame {m m' : Mem} {B : Addr} {n k out : Nat} (width : k ≤ n)
    (O : Outs B (loadPrimeRanges n k out) m m') : Outs B (stageRanges n [out]) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [loadPrimeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact stage_cover_temp (by simp only [arr, Nat.zero_mul, Nat.add_zero]; exact Nat.le_refl _) (by unfold arr S; omega_using [width])
  · exact stage_cover_array (by simp) (Nat.le_refl _)

theorem loadExponent_scratch_frame {s : VG.X86.State} {B : Addr} {Z n : Nat} {m m' : Mem}
    (h : Ws s B Z n 32) (O : Outs B (loadExponentRanges n) m m') : Frame [⟨B, Z⟩] m m' := by
  have head := h.hdr_le
  apply outs_scratch_frame (by have := h.workspace.nowrap; omega_using [this]) O
  intro r hr
  simp only [loadExponentRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · unfold kEv hdr at *
    omega_using [head]
  · exact h.arr_fit (by decide)

theorem Input.afterExponent {E : Environment} {s t : VG.X86.State} {regs : List VG.X86.Reg}
    (h : Input E s) (ws : Ws t E.base E.size E.n 32) (K : VG.Proof.Mont.X86.Keeps regs s t)
    (O : Outs E.base (loadExponentRanges E.n) s.mem t.mem) : Input E t := by
  apply h.afterOuts ws K ?_ O
  intro r hr
  simp only [loadExponentRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · decide
  · exact Nat.le_trans (by decide : 72 ≤ hdr) (Nat.le_add_right ..)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The inputs at the run-time width establish the shared arithmetic's inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aOne aE kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment Input)

structure Loaded (E : Environment) (m : Mem) (s : State) : Prop where
  input : Input E s
  pValue : num s.mem E.base E.n aPa = Spec.Rsa.os2ip
    (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len)
  qValue : num s.mem E.base E.n aQa = Spec.Rsa.os2ip
    (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)
  eValue : val32 s.mem E.base kEv 2 = Spec.Rsa.os2ip
    (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len)
  pBound : num s.mem E.base E.n aPa < 2 ^ (32 * E.k)
  qBound : num s.mem E.base E.n aQa < 2 ^ (32 * E.k)
  one : num s.mem E.base E.n aOne = 1
  zero : num s.mem E.base E.n aZero = 0
  loaded : num s.mem E.base E.n aE = val32 s.mem E.base kEv 2

theorem loadInputs_ok {E : Environment} {p : BitVec 32} {s : State} (h : Input E s)
    (H : Ws s E.base E.size E.n 32) (C : VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size p E.argument s) :
    WP isa loadInputs s fun t => Loaded E s.mem t ∧ Ws t E.base E.size E.n 32 ∧
      Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  obtain small : E.k ≤ E.n := by omega_using [widths]
  have head := h.ws.hdr_le
  unfold loadInputs VG.Impl.Rsa.X86.Keys.seqs
  -- The arrays cleared, and one.
  refine WP.seq (WP.mono (clearInputs_ok H) fun u ⟨Hu, Ou, one, zero, Ku⟩ => ?_)
  obtain hu : Input E u := h.afterOuts Hu.old Ku (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (by decide : 72 ≤ hdr)) Ou
  obtain Fu : Frame [E.workspaceRegion] s.mem u.mem :=
    VG.Proof.RsaKeyGen.X86.Key.outs_scratch_frame (by have := h.ws.workspace.nowrap; omega_using [this]) Ou
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.ws.fits)
  obtain Cu := C.keep Ku Fu
  -- A prime at argument `2 i`.
  have prime {a : State} (ha : Input E a) (Ha : Ws a E.base E.size E.n 32)
      (Ca : VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size p E.argument a) {i out : Nat}
      (index : i = 2 ∨ i = 3) (ho : out < 32) (persistent : 15 ≤ out) :
      WP isa (loadPrime (2 * i) out) a fun t =>
        Input E t ∧ Ws t E.base E.size E.n 32 ∧ Frame [E.workspaceRegion] a.mem t.mem ∧
        num t.mem E.base E.n out = Spec.Rsa.os2ip
          (Spec.Rsa.bytesAt a.mem (E.outputRegion i).base (E.outputRegion i).len) ∧
        num t.mem E.base E.n out < 2 ^ (32 * E.k) ∧
        (∀ j, 1 ≤ j → j < 32 → j ≠ out → num t.mem E.base E.n j = num a.mem E.base E.n j) ∧
        Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] a t := by
    obtain hi : i < 7 := by omega_using [index]
    obtain len : E.outputLength i = 4 * E.k := by
      unfold Environment.outputLength
      split <;> omega
    obtain A : VG.Proof.Bignum.X86.CallArgument a E.base E.size (2 * i + 4) (E.out i) := by
      obtain H := context_argument Ca (i := 2 * i) (by omega_using [index])
      rcases index with rfl | rfl <;> exact H
    obtain readable : InRegions (a.rd ++ a.wr) ((E.out i).setWidth 64) (4 * E.k) := by
      obtain ⟨r, hr, contains⟩ := ha.outWrite i hi
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      change r.Contains ((E.out i).setWidth 64) (E.outputLength i) at contains
      rwa [len] at contains
    refine WP.mono (loadPrime_ok Ha widths.2.2.1 widths.2.2.2.1 ho persistent A
      (by rw [← len]; exact ha.valid.outFit i hi) readable
      (by simpa only [Environment.outputRegion, Environment.workspaceRegion, len] using ha.valid.outputScratch i hi))
      fun t ⟨ht, O, value, bound, K⟩ => ?_
    obtain frame := VG.Proof.RsaKeyGen.X86.Key.loadPrime_stage_frame small O
    refine ⟨ha.afterStage ht.old K frame, ht, VG.Proof.RsaKeyGen.X86.Key.stage_scratch_frame ha.ws
      (by simp only [List.mem_singleton]; rintro j rfl; exact ho) frame, ?_, bound, ?_, K⟩
    · simpa only [Environment.outputRegion, len] using value
    · intro j positive hj different
      exact VG.Proof.RsaKeyGen.X86.Key.loadPrime_preserves_num small positive different (ha.ws.fit64 hj) O
  refine WP.seq (WP.mono (prime hu Hu Cu (i := 2) (out := aPa) (Or.inl rfl) (by decide) (by decide))
    fun v ⟨hv, Hv, Fv, pValue, pBound, pv, Kv⟩ => ?_)
  rw [h.output_preserved (by decide : 2 < 7) Fu] at pValue
  obtain oneV : num v.mem E.base E.n aOne = 1 := (pv _ (by decide) (by decide) (by decide)).trans one
  obtain zeroV : num v.mem E.base E.n aZero = 0 :=
    (pv _ (by decide) (by decide) (by decide)).trans (zero _ (by decide) (by decide))
  obtain Fsv := Fu.trans Fv
  obtain Cv := Cu.keep Kv Fv
  refine WP.seq (WP.mono (prime hv Hv Cv (i := 3) (out := aQa) (Or.inr rfl) (by decide) (by decide))
    fun w ⟨hw, Hw, Fw, qValue, qBound, qw, Kw⟩ => ?_)
  rw [h.output_preserved (by decide : 3 < 7) Fsv] at qValue
  obtain pValueW := (qw aPa (by decide) (by decide) (by decide)).trans pValue
  obtain pBoundW : num w.mem E.base E.n aPa < 2 ^ (32 * E.k) := by
    rw [qw aPa (by decide) (by decide) (by decide)]
    exact pBound
  obtain oneW := (qw aOne (by decide) (by decide) (by decide)).trans oneV
  obtain zeroW := (qw aZero (by decide) (by decide) (by decide)).trans zeroV
  obtain Fsw := Fsv.trans Fw
  obtain Cw := Cv.keep Kw Fw
  -- The exponent.
  refine WP.mono (loadExponent_ok Hw h.valid.exponentLength.1 h.valid.exponentLength.2
    (context_argument Cw (i := 14) (by decide)) (context_argument Cw (i := 15) (by decide)) hw.valid.exponentFit
    hw.exponentRead (hw.valid.exponentScratch.sub_right (Offset.sub_base _ (by unfold kEv hdr at *; omega_using [head]))))
    fun x ⟨Hx, O, eValue, loaded, Kx⟩ => ?_
  obtain hx : Input E x := hw.afterExponent Hx.old Kx O
  obtain Fx := VG.Proof.RsaKeyGen.X86.Key.loadExponent_scratch_frame hw.ws O
  have ex (j : Nat) (hj : j < 32) (different : j ≠ aE) : num x.mem E.base E.n j = num w.mem E.base E.n j :=
    VG.Proof.RsaKeyGen.X86.Key.loadExponent_preserves_num different (hw.ws.fit64 hj) O
  change val32 x.mem E.base kEv 2 = Spec.Rsa.os2ip
    (Spec.Rsa.bytesAt w.mem E.exponentRegion.base E.exponentRegion.len) at eValue
  rw [h.exponent_preserved Fsw] at eValue
  obtain pValueX := (ex aPa (by decide) (by decide)).trans pValueW
  obtain qValueX := (ex aQa (by decide) (by decide)).trans qValue
  obtain pBoundX : num x.mem E.base E.n aPa < 2 ^ (32 * E.k) := by
    rw [ex aPa (by decide) (by decide)]
    exact pBoundW
  obtain qBoundX : num x.mem E.base E.n aQa < 2 ^ (32 * E.k) := by
    rw [ex aQa (by decide) (by decide)]
    exact qBound
  obtain oneX := (ex aOne (by decide) (by decide)).trans oneW
  obtain zeroX := (ex aZero (by decide) (by decide)).trans zeroW
  exact ⟨⟨hx, pValueX, qValueX, eValue, pBoundX, qBoundX, oneX, zeroX, loaded⟩, Hx, Fsw.trans Fx,
    (Ku.mono (by decide)).trans (Kv.trans (Kw.trans (Kx.mono (by decide))))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # The inputs load in time that depends only on the arguments -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/LoadInputsRuns.lean`, which only this module imported.
section

/-! # The inputs load from any state that can read them: the read-only view of the arithmetic -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

/-- `loadInputs` runs from a state that reads the primes and the exponent, wherever it may write. -/
theorem loadInputs_runs {E : Environment} {p : BitVec 32} {s : State} (valid : E.Valid)
    (H : Ws s E.base E.size E.n 32) (C : Context E.base E.size p E.argument s)
    (primes : ∀ i, i = 2 ∨ i = 3 → InRegions (s.rd ++ s.wr) (E.outputRegion i).base (E.outputRegion i).len)
    (exponent : InRegions (s.rd ++ s.wr) E.exponentRegion.base E.exponentRegion.len) :
    WP isa loadInputs s fun _ => True := by
  have widths := valid.widths
  have small : E.k ≤ E.n := by omega
  have head := H.hdr_le
  unfold loadInputs VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (clearInputs_ok H) fun u ⟨Hu, Ou, _, _, Ku⟩ => ?_)
  have Fu : Frame [E.workspaceRegion] s.mem u.mem :=
    VG.Proof.RsaKeyGen.X86.Key.outs_scratch_frame (by have := H.old.workspace.nowrap; omega) Ou
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.old.fits)
  have Cu := C.keep Ku Fu
  have prime {a : State} (Ha : Ws a E.base E.size E.n 32) (Ca : Context E.base E.size p E.argument a)
      (ra : a.rd ++ a.wr = s.rd ++ s.wr) {i out : Nat} (index : i = 2 ∨ i = 3) (ho : out < 32)
      (persistent : 15 ≤ out) :
      WP isa (loadPrime (2 * i) out) a fun t => Ws t E.base E.size E.n 32 ∧
        Frame [E.workspaceRegion] a.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] a t := by
    have hi : i < 7 := by omega
    have len : E.outputLength i = 4 * E.k := by
      unfold Environment.outputLength
      split <;> omega
    have A : VG.Proof.Bignum.X86.CallArgument a E.base E.size (2 * i + 4) (E.out i) := by
      have H := context_argument Ca (i := 2 * i) (by omega)
      rcases index with rfl | rfl <;> exact H
    have readable : InRegions (a.rd ++ a.wr) ((E.out i).setWidth 64) (4 * E.k) := by
      rw [ra]
      have R := primes i index
      change InRegions _ ((E.out i).setWidth 64) (E.outputLength i) at R
      rwa [len] at R
    refine WP.mono (loadPrime_ok Ha widths.2.2.1 widths.2.2.2.1 ho persistent A
      (by rw [← len]; exact valid.outFit i hi) readable
      (by simpa only [Environment.outputRegion, Environment.workspaceRegion, len] using valid.outputScratch i hi))
      fun t ⟨ht, O, _, _, K⟩ => ?_
    exact ⟨ht, VG.Proof.RsaKeyGen.X86.Key.stage_scratch_frame Ha.old
      (by simp only [List.mem_singleton]; rintro j rfl; exact ho)
      (VG.Proof.RsaKeyGen.X86.Key.loadPrime_stage_frame small O), K⟩
  have ru : u.rd ++ u.wr = s.rd ++ s.wr := by rw [Ku.2.1, Ku.2.2]
  refine WP.seq (WP.mono (prime Hu Cu ru (i := 2) (out := aPa) (Or.inl rfl) (by decide) (by decide))
    fun v ⟨Hv, Fv, Kv⟩ => ?_)
  have rv : v.rd ++ v.wr = s.rd ++ s.wr := by rw [Kv.2.1, Kv.2.2, ru]
  have Cv := Cu.keep Kv Fv
  refine WP.seq (WP.mono (prime Hv Cv rv (i := 3) (out := aQa) (Or.inr rfl) (by decide) (by decide))
    fun w ⟨Hw, Fw, Kw⟩ => ?_)
  have rw' : w.rd ++ w.wr = s.rd ++ s.wr := by rw [Kw.2.1, Kw.2.2, rv]
  have Cw := Cv.keep Kw Fw
  refine WP.mono (loadExponent_ok Hw valid.exponentLength.1 valid.exponentLength.2
    (context_argument Cw (i := 14) (by decide)) (context_argument Cw (i := 15) (by decide)) valid.exponentFit
    (by rw [rw']; exact exponent)
    (valid.exponentScratch.sub_right (Offset.sub_base _ (by unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega))))
    fun _ _ => trivial

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment SizedStart ImportedPair InputPair)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

/-- `readonly_agree` before the inputs, whose `esi` may differ. -/
theorem input_agree {s t : State} {B : Addr} {Z : Nat} {p : BitVec 32} {args : Nat → BitVec 32}
    (S : Context B Z p args s) (T : Context B Z p args t) (large : 160 ≤ Z) :
    VG.X86.Taint.Agree inputTaint (readonly s B Z) (readonly t B Z) := by
  have sp : s.gpr .esp = t.gpr .esp := S.sp.trans T.sp.symm
  have fitS : (s.gpr .esp).toNat + 92 ≤ 2 ^ 32 := by rw [S.sp]; exact S.fit
  have fitT : (t.gpr .esp).toNat + 92 ≤ 2 ^ 32 := by rw [T.sp]; exact T.fit
  refine {
    rf := ⟨?_, by intro h; cases h⟩
    wr := fun h => False.elim (h rfl)
    wf₁ := (readonly_wf S large).mono (Or.inl rfl) (fun _ h => h) (fun _ h => ⟨h, rfl⟩)
      (Or.inr ⟨rfl, rfl⟩) (fun _ h => ⟨h, rfl, rfl⟩) (Or.inl ⟨rfl, Nat.le_refl _⟩)
    wf₂ := (readonly_wf T large).mono (Or.inl rfl) (fun _ h => h) (fun _ h => ⟨h, rfl⟩)
      (Or.inr ⟨rfl, rfl⟩) (fun _ h => ⟨h, rfl, rfl⟩) (Or.inl ⟨rfl, Nat.le_refl _⟩)
    ok := VG.X86.Taint.slotsOk_empty
    slots := VG.X86.Taint.slotsAgree_empty
    sp := fun _ => sp
    argMem := ?_ }
  · intro r hr
    simp only [inputTaint, runtimeTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (S.scratch.edi_toNat.trans T.scratch.edi_toNat.symm)
    · exact sp
  · intro k h4 hk
    change k < 76 at hk
    change s.mem (VG.X86.Taint.argByte s (16 + k)) = t.mem (VG.X86.Taint.argByte t (16 + k))
    rw [VG.X86.Taint.argByte_eq fitS (by omega_using []) (by omega_using [hk]),
      VG.X86.Taint.argByte_eq fitT (by omega_using []) (by omega_using [hk]),
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide : 0 < 4)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide : 0 < 4))]
    have index : (16 + k - 4) / 4 = (k - 4) / 4 + 4 := by omega_using [h4]
    have same := (context_argument S (i := (k - 4) / 4) (by omega_using [hk])).value.trans
      (context_argument T (i := (k - 4) / 4) (by omega_using [hk])).value.symm
    change arg s ((k - 4) / 4 + 4) = arg t ((k - 4) / 4 + 4) at same
    rw [index]
    exact congrArg _ same

theorem readonly_inputs {E : Environment} {s : State} (h : VG.Proof.RsaKeyGen.X86.Key.Input E s)
    (H : Ws s E.base E.size E.n 32) {p : BitVec 32} (C : Context E.base E.size p E.argument s) :
    WP isa loadInputs (readonly s E.base E.size) fun _ => True := by
  have widen {b : Addr} {l : Nat} (R : InRegions (s.rd ++ s.wr) b l) :
      InRegions ((readonly s E.base E.size).rd ++ (readonly s E.base E.size).wr) b l := by
    obtain ⟨r, hr, contains⟩ := R
    exact ⟨r, List.mem_append_left _ hr, contains⟩
  refine loadInputs_runs h.valid H.readonly (context_readonly C) ?_ (widen h.exponentRead)
  intro i hi
  obtain ⟨r, hr, contains⟩ := h.outWrite i (by omega_using [hi])
  exact widen ⟨r, List.mem_append_right _ hr, contains⟩

theorem loaded_core {E : Environment} {m : Mem} {s : State} {e p q : Nat} (L : Loaded E m s)
    (H : Ws s E.base E.size E.n 32) (he : VG.Proof.RsaKeyGen.X86.Key.inputExponent E m = e)
    (hp : VG.Proof.RsaKeyGen.X86.Key.inputPrime E m 2 = p) (hq : VG.Proof.RsaKeyGen.X86.Key.inputPrime E m 3 = q) :
    VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p q s :=
  ⟨⟨H.old, L.pBound, L.qBound, L.zero, L.one, L.eValue.trans he, L.loaded.trans (L.eValue.trans he)⟩,
    L.pValue.trans hp, L.qValue.trans hq⟩

theorem runtime_input_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) :
    RelCT isa (RuntimeStart E sp e p q p' q') loadInputs (RuntimeImported E sp e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨u', AS⟩ := trace_readonly_of_wp P.left (readonly_inputs P.start.inputs.left P.left P.leftArgs) A
  obtain ⟨v', CT⟩ := trace_readonly_of_wp P.right (readonly_inputs P.start.inputs.right P.right P.rightArgs) C
  obtain ⟨hint, out, checked, lower⟩ := loadInputs_public
  obtain ⟨trace, agreeOut⟩ := VG.Taint.check_sound checked
    (input_agree P.leftArgs P.rightArgs P.left.hdr_le) AS CT
  have agreeRt := sseTaint.le_sound lower agreeOut
  obtain ⟨sRead, sWrite⟩ := readonly_covers P.left
  obtain ⟨tRead, tWrite⟩ := readonly_covers P.right
  have widenedS := VG.X86.Exec.widen AS sRead sWrite
  have widenedT := VG.X86.Exec.widen CT tRead tWrite
  simp only [readonly, State.withRegions_withRegions, State.withRegions_self] at widenedS widenedT
  have endS := (Exec.det A widenedS).2
  have endT := (Exec.det C widenedT).2
  have publicOut : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint true) u v := by
    change VG.X86.Taint.Agree (τr [.edi, .esi]) u v
    apply agree_regs
    intro r hr
    rw [endS, endT]
    change u'.gpr r = v'.gpr r
    apply agreeRt.reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  obtain ⟨LS, HS, FS, KS⟩ := wp_result (loadInputs_ok P.start.inputs.left P.left P.leftArgs) A
  obtain ⟨LT, HT, FT, KT⟩ := wp_result (loadInputs_ok P.start.inputs.right P.right P.rightArgs) C
  have stack : u.gpr .esp = v.gpr .esp := by
    rw [KS.1 .esp (by decide), KT.1 .esp (by decide)]
    exact P.start.inputs.stack
  exact ⟨trace, ⟨⟨LS.input, LT.input, stack⟩,
      loaded_core LS HS P.start.leftExponent P.start.leftP P.start.leftQ,
      loaded_core LT HT P.start.rightExponent P.start.rightP P.start.rightQ, publicOut⟩,
    HS, HT, P.leftArgs.keep KS FS, P.rightArgs.keep KT FT⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # Workspace code whose taint check starts with `esi` secret has public timing -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

/-- The check of `c` from `inputTaint` succeeds, at least as public as `τ`. -/
def FromInputs (c : Prog isa) (τ : VG.X86.Taint.T) : Prop := ∃ hint out,
  VG.Taint.check sseTaint inputTaint c hint = some out ∧ sseTaint.le τ out = true

theorem fromInputs_of_any {c : Prog isa} {τ : VG.X86.Taint.T} {hint : VG.Taint.Hint VG.X86.Taint.T}
    (checked : (VG.Taint.check sseTaint inputTaint c hint).any (sseTaint.le τ) = true) : FromInputs c τ := by
  cases result : VG.Taint.check sseTaint inputTaint c hint with
  | none => rw [result] at checked; cases checked
  | some out => exact ⟨hint, out, result, by simpa only [result, Option.any_some] using checked⟩

/-- Two runs of workspace code that also runs on the read-only views have one trace, and agree on
the registers `τ` makes public. -/
theorem readonly_trace {c : Prog isa} {τ : VG.X86.Taint.T} (H : FromInputs c τ)
    {B : Addr} {Z n : Nat} {sp : BitVec 32} {args : Nat → BitVec 32} {s t u v : State} {tr ur : List Leak}
    (Hs : Ws s B Z n 32) (Ht : Ws t B Z n 32) (Cs : Context B Z sp args s) (Ct : Context B Z sp args t)
    (runS : WP isa c (readonly s B Z) fun _ => True) (runT : WP isa c (readonly t B Z) fun _ => True)
    (A : Exec isa c s tr u) (C : Exec isa c t ur v) :
    tr = ur ∧ ∀ r, VG.X86.Taint.pub τ r = true → u.gpr r = v.gpr r := by
  obtain ⟨u', AS⟩ := trace_readonly_of_wp Hs runS A
  obtain ⟨v', CT⟩ := trace_readonly_of_wp Ht runT C
  obtain ⟨hint, out, checked, lower⟩ := H
  obtain ⟨trace, agreeOut⟩ := VG.Taint.check_sound checked (input_agree Cs Ct Hs.hdr_le) AS CT
  have agree := sseTaint.le_sound lower agreeOut
  obtain ⟨sRead, sWrite⟩ := readonly_covers Hs
  obtain ⟨tRead, tWrite⟩ := readonly_covers Ht
  have widenedS := VG.X86.Exec.widen AS sRead sWrite
  have widenedT := VG.X86.Exec.widen CT tRead tWrite
  simp only [readonly, State.withRegions_withRegions, State.withRegions_self] at widenedS widenedT
  have endS := (Exec.det A widenedS).2
  have endT := (Exec.det C widenedT).2
  refine ⟨trace, fun r hr => ?_⟩
  rw [endS, endT]
  exact agree.reg hr

end VG.Proof.RsaKeyGen.X86.KeyRuntime
