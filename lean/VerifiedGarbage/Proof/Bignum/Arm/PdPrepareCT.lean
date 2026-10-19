module
public import VerifiedGarbage.Impl.Bignum.Arm.PdFn
public import VerifiedGarbage.Proof.Bignum.Arm.PdBodyInput
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.PdFn
meta import VerifiedGarbage.Proof.Bignum.Arm.PdBodyInput
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Public RSA workspace setup has a public trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pdPrepareCore_ct {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PdBodyInput base dst np ep xp len k eLen N R eb xb1 s ∧
      PdBodyInput base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PublicFn.prepare (fun _ _ => True) := by
  let P := fun (s t : State) => PdBodyInput base dst np ep xp len k eLen N R eb xb1 s ∧
    PdBodyInput base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp
  have head : RelCT isa P (.block PcFn.head) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) {xb : List Byte} (h : PdBodyInput base dst np ep xp len k eLen N R eb xb s) :
      WP isa (.block PcFn.head) s (fun t => t.gpr .r0 = base) := by
    unfold PcFn.head
    refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u a => ?_
    refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_lsr (by decide)) fun v b => ?_
    refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t c => WP.block_nil ?_
    exact (c.other .r0 (by decide)).trans ((b.other .r0 (by decide)).trans ((a.other .r0 (by decide)).trans h.ptr))
  have headReady := (relCT_keep_sp head (fun _ _ h => h.2.2)).wp (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have setupTrace : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .r0 = base ∧ t.gpr .r0 = base)
      setup (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h.1)
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.2.1.trans h.2.2.symm) e1 e2, trivial⟩
  have inputs : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.inputs) (fun s t => s.sp = t.sp) :=
    stackLoads_ct [(.r4, 8), (.r6, 12)]
  exact (headReady.seq (setupTrace.seq inputs)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem pdPrepare_ct {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PdBodyInput base dst pp ep xp len k eLen N R eb xb1 s ∧
      PdBodyInput base dst pp ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PdFn.prepare (fun _ _ => True) := by
  have wp (s : State) {xb : List Byte} (h : PdBodyInput base dst pp ep xp len k eLen N R eb xb s) :
      WP isa (.block PcFn.inputs) s (PdBodyInput base dst pp ep xp len k eLen N R eb xb) := by
    refine WP.mono (pcInputs_ok s h.stack.pcStack) ?_
    rintro t ⟨_, _, mem, rest⟩
    exact h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
  exact crt_seq_ct ((stackLoads_ct [(.r4, 8), (.r6, 12)]).mono
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) (fun s h => wp s h) (fun s h => wp s h) pdPrepareCore_ct

end VG.Proof.Bignum.Arm
