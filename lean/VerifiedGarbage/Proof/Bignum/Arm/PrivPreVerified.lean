module

public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreFn
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Bignum.Arm.PrivPreFrameCT
import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Bignum.Arm.PrivPreFn
meta import VerifiedGarbage.Proof.Bignum.Arm.PrivPreFrameCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PcPush
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Sig

/-! # ARMv7 `vg_rsa_private_precompute` is verified against its contract

Timing depends on the stack pointer, the pointers and lengths of the
arguments, and the modulus' bytes: the factors and whether `p q = n` stay
secret.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.PrivPreFn

theorem pp_loadArgs_ct : RelCT isa (fun s t => s.sp = t.sp) (.block loadArgs) (fun s t => s.sp = t.sp) := by
  have loads : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.ldrSp .r0 0, .ldrSp .r1 12, .ldrSp .r2 56, .ldrSp .r3 60, .ldrSp .r4 64, .ldrSp .r5 68])
      (fun s t => s.sp = t.sp) :=
    stackLoads_ct [(.r0, 0), (.r1, 12), (.r2, 56), (.r3, 60), (.r4, 64), (.r5, 68)]
  have movs : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.mov .r6 (.reg .r2), .mov .r7 (.reg .r3), .mov .r8 (.reg .r4), .mov .r9 (.reg .r5),
        .mov .r10 (.reg .r0), .mov .r11 (.reg .r3)]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append (M := isa)
    (l₁ := ([.ldrSp .r0 0, .ldrSp .r1 12, .ldrSp .r2 56, .ldrSp .r3 60, .ldrSp .r4 64, .ldrSp .r5 68] : List Instr))
    (loads.seq (RelCT.block_append (M := isa)
      (l₁ := ([.mov .r6 (.reg .r2), .mov .r7 (.reg .r3), .mov .r8 (.reg .r4), .mov .r9 (.reg .r5),
        .mov .r10 (.reg .r0), .mov .r11 (.reg .r3)] : List Instr)) (movs.seq (loadStack_ct .r12 72))))

theorem pp_argsFrame_ct (s0 t0 : State) (hs : PpFnInput s0) (ht : PpFnInput t0) {B : Addr} {P : Nat}
    (Ls : PpLayout s0 B P) (Lt : PpLayout t0 B P) (geo : ppGeometry s0 = ppGeometry t0)
    (bytes : ppBytes s0 0 = ppBytes t0 0) :
    RelCT isa (fun a b => PpLoaded s0 P a ∧ PpLoaded t0 P b ∧ a.sp = b.sp) argsFrame (fun _ _ => True) := by
  unfold argsFrame
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v hp e1 e2
  obtain ⟨x, y, ⟨hx, hy, sp⟩, px, py⟩ := hp
  have fitX : 56 ≤ x.sp.toNat := by
    rw [hx.rest.sp]; change 56 ≤ (s0.sp - BitVec.ofNat 32 56).toNat
    rw [FrameStack.sub_toNat' (by have := hs.stackFit; omega)]; have := hs.stackFit; omega
  have fitY : 56 ≤ y.sp.toNat := by
    rw [hy.rest.sp]; change 56 ≤ (t0.sp - BitVec.ofNat 32 56).toNat
    rw [FrameStack.sub_toNat' (by have := ht.stackFit; omega)]; have := ht.stackFit; omega
  have ex : pcPushed x = a := Option.some.inj ((push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) fitX).symm.trans px)
  have ey : pcPushed y = b := Option.some.inj ((push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) fitY).symm.trans py)
  subst ex; subst ey
  have callCT : RelCT isa (fun a b => a = pcPushed x ∧ b = pcPushed y ∧ a.sp = b.sp) (.block callArgs)
      (fun _ _ => True) :=
    (stackLoads_ct [(.r0, 56), (.r2, 64), (.r3, 68)]).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have frameCT : RelCT isa (fun a b => PpCalled s0 B P a ∧ PpCalled t0 B P b ∧ a.sp = b.sp) crtFrame
      (fun _ _ => True) := by
    refine (pp_crtFrame_ct (g := ppGeometry s0) bytes).mono ?_ (fun _ _ _ => trivial)
    intro a b h
    have i2 := h.2.1.input
    have c2 := h.2.1.call
    rw [← geo] at i2 c2
    exact ⟨⟨h.1.input, h.1.call⟩, ⟨i2, c2⟩, h.2.2⟩
  exact crt_seq_ct callCT (fun a h => h ▸ pp_call_ok s0 hs Ls x hx) (fun b h => h ▸ pp_call_ok t0 ht Lt y hy) frameCT
    _ _ _ _ _ _ ⟨rfl, rfl, by simp only [pcPushed, pushed_sp, sp]⟩ e1 e2

theorem ppFn_ct (s0 t0 : State) (hs : PpFnInput s0) (ht : PpFnInput t0) (sp : s0.sp = t0.sp)
    (geo : ppGeometry s0 = ppGeometry t0) (bytes : ppBytes s0 0 = ppBytes t0 0) :
    RelCT isa (fun s t => s = s0 ∧ t = t0) code (fun _ _ => True) := by
  have Ls := pp_layout s0 hs
  have Lt := pp_layout t0 ht
  rw [← sp, ← geo] at Lt
  generalize ppPreWords (ppGeometry s0) = P at Ls Lt
  generalize State.addr s0.sp - BitVec.ofNat 64 168 = B at Ls Lt
  have out : s0.gpr .r0 = t0.gpr .r0 := congrArg CrtGeometry.output geo
  unfold code
  apply RelCT.frame (fun _ _ h => by rw [h.1, h.2]; exact sp)
  intro a b tr1 tr2 u v hp e1 e2
  obtain ⟨x, y, ⟨rfl, rfl⟩, px, py⟩ := hp
  have ex : pcPushed x = a := Option.some.inj ((push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide)
    (by show 56 ≤ _; have := hs.stackFit; omega)).symm.trans px)
  have ey : pcPushed y = b := Option.some.inj ((push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide)
    (by show 56 ≤ _; have := ht.stackFit; omega)).symm.trans py)
  subst ex; subst ey
  have zaCT : RelCT isa (fun a b => a = pcPushed x ∧ b = pcPushed y ∧ a.sp = b.sp) (.block zeroArgs)
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _
    exact Taint.agree_ofRegs (by simp)
  have zCT : RelCT isa (fun a b => PpZeroReady x P a ∧ PpZeroReady y P b ∧ a.sp = b.sp) zero (fun _ _ => True) := by
    intro a b tr1 tr2 u v h e1 e2
    exact ⟨zero_ct a b tr1 tr2 u v trivial trivial ⟨h.1.1.trans (out.trans h.2.1.1.symm), h.1.2.1.trans h.2.1.2.1.symm⟩
      e1 e2, trivial⟩
  have lCT : RelCT isa (fun a b => PpZeroed x P a ∧ PpZeroed y P b ∧ a.sp = b.sp) (.block loadArgs)
      (fun s t => s.sp = t.sp) := pp_loadArgs_ct.mono (fun _ _ h => h.2.2) (fun _ _ h => h)
  have argsCT := relCT_keep_sp (pp_argsFrame_ct x y hs ht Ls Lt geo bytes) (fun _ _ h => h.2.2)
  have restore : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.restore) (fun s t => s.sp = t.sp) :=
    stackLoads_ct pcCalleeSaved
  have tail := (lCT.wp (F₁ := PpLoaded x P) (F₂ := PpLoaded y P)
      (fun a b h => ⟨pp_load_ok x hs Ls a h.1, pp_load_ok y ht Lt b h.2.1⟩)).seq
    ((argsCT.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)).seq restore)
  have tail' : RelCT isa (fun a b => PpZeroed x P a ∧ PpZeroed y P b ∧ a.sp = b.sp)
      (.seq (.block loadArgs) (.seq argsFrame (.block PcFn.restore))) (fun _ _ => True) :=
    tail.mono (fun _ _ h => h) (fun _ _ _ => trivial)
  exact crt_seq_ct zaCT (fun a h => h ▸ pp_zeroArgs_ok x Ls) (fun b h => h ▸ pp_zeroArgs_ok y Lt)
    (crt_seq_ct zCT (fun a h => pp_zero_ok x hs Ls a h) (fun b h => pp_zero_ok y ht Lt b h) tail')
    _ _ _ _ _ _ ⟨rfl, rfl, by simp only [pcPushed, pushed_sp, sp]⟩ e1 e2

theorem pp_contract_ct : ConstantTime isa (Spec.Rsa.privatePrecomputeContract abi 168).pre
    (Spec.Rsa.privatePrecomputeContract abi 168).pub code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := pp_contract_pre s hs
  have it := pp_contract_pre t ht
  sig_pub [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, a0, a1, a2, a3, a4, a5⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have geo : ppGeometry s = ppGeometry t := by
    simp only [ppGeometry, p0, p2, p3, a0, a1, a2, a3, a4, a5]
  have nb : ppBytes s 0 = ppBytes t 0 := by
    rw [ppBytes_other s 0 (by decide) (by decide), ppBytes_other t 0 (by decide) (by decide)]
    exact byteEq
  exact (ppFn_ct s t is it sp geo nb s t tr1 tr2 u v ⟨rfl, rfl⟩ e1 e2).1

/-- A 64-byte modulus, 32-byte factors, and separate buffers. -/
def ppSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 24 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else
    if a = 0x8004 then 0x20 else
    if a = 0x8009 then 0x31 else
    if a = 0x800c then 0x20 else
    if a = 0x8011 then 0x40 else
    if a = 0x8014 then 0x20 else
    if a = 0x8015 then 0x4 else
    0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x3100, 32⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x1000, 192⟩, ⟨0x4000, 8448⟩]

theorem pp_contract_sat : ∃ s, (Spec.Rsa.privatePrecomputeContract abi 168).pre s := by
  sig_implies_sat [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
    [ppSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords,
      Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords, Spec.Rsa.modulusWords]
    using ppSatState

theorem privPre_verified : Verified target code (Spec.Rsa.privatePrecomputeContract abi 168) :=
  ⟨pp_contract_correct, pp_contract_ct, pp_contract_sat⟩

end VG.Proof.Bignum.Arm
