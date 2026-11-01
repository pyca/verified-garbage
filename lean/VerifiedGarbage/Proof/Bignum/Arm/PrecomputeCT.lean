module

public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnCT
import VerifiedGarbage.Proof.Bignum.Arm.InitInverseCT
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.InverseArgs
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnCT
meta import VerifiedGarbage.Proof.Bignum.Arm.InitInverseCT
meta import VerifiedGarbage.Proof.Bignum.Arm.R2CT
meta import VerifiedGarbage.Proof.Bignum.Arm.InverseArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Modulus precomputation reveals no modulus-dependent execution trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_mov op2_imm)

theorem importModulus_ct {base src : BitVec 32} {len w k : Nat} :
    RelCT isa (fun s t => PrecomputeInput base src len w k s ∧
      PrecomputeInput base src len w k t ∧ s.sp = t.sp) importModulus (fun _ _ => True) := by
  let P := fun (s t : State) => PrecomputeInput base src len w k s ∧
    PrecomputeInput base src len w k t ∧ s.sp = t.sp
  have args : RelCT isa P (.block [.mov .r2 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : PrecomputeInput base src len w k s) :
      WP isa (.block [.mov .r2 (.imm 0)]) s (LoadFnReady base src len w 0 k) := by
    refine wp_mov (op2_imm (by decide)) fun u moved => WP.block_nil ?_
    refine ⟨⟨h.workspace.congr moved.wr, ?_, ?_, ?_, moved.gpr⟩, ?_, ?_⟩
    · rw [moved.mem]; exact h.layout
    · rw [moved.mem]; exact h.width
    · exact (moved.other .r0 (by decide)).trans h.ptr
    · exact (moved.other .r4 (by decide)).trans h.source
    · exact (moved.other .r6 (by decide)).trans h.count
  have setup := (relCT_keep_sp args (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact (setup.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq (loadBEFn_ct (by decide))

theorem precomputeInverse_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => PrecomputeModulus base len w s ∧ PrecomputeModulus base len w t)
      precomputeInverse (fun _ _ => True) := by
  let P := PrecomputeModulus base len w
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w 0) ∧ s.gpr .r12 = base
  have args : RelCT isa (fun s t => P s ∧ P t) (.block inverseArgs) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block inverseArgs) s Q :=
    WP.mono (inverseArgs_ok s h.workspace h.layout h.width h.ptr) (fun _ h => ⟨h.1, h.2.1⟩)
  refine (pair_posts args wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨initInverse_ct s t tr1 tr2 u v trivial trivial
    ⟨h.1.1.trans h.2.1.symm, h.1.2.trans h.2.2.symm⟩ e1 e2, trivial⟩

theorem precompute_ct {base src : BitVec 32} {len w k : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => PrecomputeInput base src len w k s ∧
      PrecomputeInput base src len w k t ∧ s.sp = t.sp) precompute (fun _ _ => True) := by
  have imported := (relCT_keep_sp (importModulus_ct (base := base) (src := src) (len := len) (w := w) (k := k))
    (fun _ _ h => h.2.2)).wp (fun s t h => ⟨importModulus_ready s h.1, importModulus_ready t h.2.1⟩)
  have inverse := relCT_keep_sp ((precomputeInverse_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PrecomputeModulus base len w s ∧ PrecomputeModulus base len w t)
    (fun _ _ h => h.2) (fun _ _ h => h)) (fun _ _ h => h.1)
  have ready := inverse.wp (fun s t h => ⟨precomputeInverse_ready s h.2.1, precomputeInverse_ready t h.2.2⟩)
  exact imported.seq ((ready.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq (r2_ct countFits))

end VG.Proof.Bignum.Arm
