module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitialStore
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowApplyCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
meta import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitial
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitial

/-! Public generator initialization and the first two table exports have fixed traces. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (wp_mov op2_imm)

def InitialInput (p : Inputs) (sp : BitVec 32) (s : State) : Prop :=
  Memory p sp s ∧ numAt s.mem (State.addr p.base) p.w 0=p.P ∧
    numAt s.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P

private theorem moveZero_ct : RelCT isa (fun _ _ => True)
    (.block [.mov .r3 (.imm 0)]) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

private theorem moveOne_ct : RelCT isa (fun _ _ => True)
    (.block [.mov .r3 (.imm 1)]) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

private theorem move_ready (digit : BitVec 32) (enc : VG.Arm.encodable digit=true)
    (s : State) {p : Inputs} {sp : BitVec 32} (h : Memory p sp s) :
    WP isa (.block [.mov .r3 (.imm digit)]) s fun t => Memory p sp t ∧ t.gpr .r3=digit := by
  refine wp_mov (op2_imm enc) fun t moved => WP.block_nil ?_
  have rest := moved.rest (by simp [roundClobbers] : .r3∈roundClobbers)
  have ready := h.ready.of_mem moved.mem rest ((moved.other .r0 (by decide)).trans h.ready.ptr)
  exact ⟨h.after_arithmetic ready (by rw [moved.mem]; exact Frame.refl _ _) rest,moved.gpr⟩

theorem initialValues_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} (odd : p.P%2=1) :
    RelCT isa (fun s t => InitialInput p sp s ∧ InitialInput p sp t ∧ s.sp=t.sp)
      (.seq (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32)
        (VG.Impl.Bignum.Arm.SharedWindow.init (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))
      (fun _ _ => True) := by
  let K := TwoExp.sharedMontgomery p.base sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have timing : TwoExp.MontgomeryTiming K := TwoExp.sharedMontgomeryTiming p.base sp p.len p.w
    backend.name backend.mul (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb)
    backend.stackOk (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
  let Ready := fun s : State => ExpInitReady p.base p.len p.w s ∧ TwoExp.CallReady p.base sp p.len s
  have imported (s : State) (h : InitialInput p sp s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32) s Ready := by
    refine WP.mono (importAt_ok s 1 56 32 h.1.context (by decide) (by simp [slots]) (by simp [slots])
      h.1.ready (by decide) (by decide) h.1.context.gBytes
      (by rw [p.gLength]; have := p.minLength; omega)
      (by rw [p.gLength]; exact p.width.2.2.2.1) (by change BitVec.ofNat 32 p.k=_; rw [p.gLength])) ?_
    rintro u ⟨_,ready,_,keeps,frame,rest⟩
    have memory := h.1.after_arithmetic ready (frame.mono (by simp)) rest
    have fit := h.1.ready.width ▸ h.1.ready.layout.2.2.1
    have modulus := (keeps_array_num keeps fit (by simp [Proof.Rsa.Mont.Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]) (by decide : 0≠1)).trans h.2.1
    have r2 := (keeps_array_num keeps fit (by simp [Proof.Rsa.Mont.Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]) (by decide : 4≠1)).trans h.2.2
    exact ⟨⟨ready,by rw [r2,modulus]; exact Nat.mod_lt _ (by have := ready.modulus; rw [modulus] at this; omega)⟩,
      memory.calls.stack,memory.fixed⟩
  exact relCT_chain ((importAt_ct (p:=p) (slots:=slots) (k:=p.k) (by decide) (by simp [slots])
    (by simp [slots]) rfl (by decide : 1<8)).mono
    (fun _ _ h => ⟨⟨h.1.1.context,h.1.1.ready⟩,⟨h.2.1.1.context,h.2.1.1.ready⟩,h.2.2⟩) (fun _ _ h => h))
    imported imported (SharedWindow.init_ct K timing)

theorem initial_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} (odd : p.P%2=1) :
    RelCT isa (fun s t => InitialInput p sp s ∧ InitialInput p sp t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.initial (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have values (s : State) (h : InitialInput p sp s) :
      WP isa (.seq (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32)
        (VG.Impl.Bignum.Arm.SharedWindow.init (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) s
        (Memory p sp) := WP.mono (initialValues_ok backend s h.1 h.2.1 h.2.2 odd) (fun _ h => h.1)
  have store (o digit : Nat) (ho : o<8) (hd : digit<32) (s : State)
      (h : Memory p sp s ∧ s.gpr .r3=BitVec.ofNat 32 digit) :
      WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.store o) s (Memory p sp) :=
    WP.mono (combStoreMemory_ok s h.1 hd ho h.2) (fun _ h => h.1)
  apply RelCT.assoc
  refine relCT_chain (initialValues_ct backend odd) values values ?_
  refine relCT_chain (moveZero_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h))
    (fun s h => move_ready 0 (by decide) s h) (fun s h => move_ready 0 (by decide) s h) ?_
  refine relCT_chain (store_ct (digit:=0) (by decide : 6<8)) (store 6 0 (by decide) (by decide))
    (store 6 0 (by decide) (by decide)) ?_
  exact relCT_chain (moveOne_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h))
    (fun s h => move_ready 1 (by decide) s h) (fun s h => move_ready 1 (by decide) s h)
    (store_ct (digit:=1) (by decide : 5<8))

end VG.Proof.Ffdh.Arm.CombBuilder
