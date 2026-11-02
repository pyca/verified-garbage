module

import VerifiedGarbage.Proof.Bignum.Arm.LoadBECT
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
public import VerifiedGarbage.Impl.Bignum.Arm.LoadBEFn
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.LoadBECT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
meta import VerifiedGarbage.Impl.Bignum.Arm.LoadBEFn
meta import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Shared-array import has public pointers and lengths -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

structure LoadFnReady (base src : BitVec 32) (len w o k : Nat) (s : State) : Prop extends
    SmallFnReady base len w o s where
  source : s.gpr .r4 = src
  count : s.gpr .r6 = BitVec.ofNat 32 k

theorem loadBEFnBody_ct {base src : BitVec 32} {len w o k : Nat} (ho : o < 8) :
    RelCT isa (fun s t => LoadFnReady base src len w o k s ∧ LoadFnReady base src len w o k t)
      loadBEFnBody (fun _ _ => True) := by
  let P := LoadFnReady base src len w o k
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w o) ∧
    s.gpr .r4 = src ∧ s.gpr .r5 = base + BitVec.ofNat 32 (arrAt w o) ∧
    s.gpr .r6 = BitVec.ofNat 32 k ∧ s.gpr .lr = BitVec.ofNat 32 (2 * w)
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block loadBEFnArgs) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.ptr.trans h.2.ptr.symm
    · exact h.1.index.trans h.2.index.symm
  have wp (s : State) (h : P s) : WP isa (.block loadBEFnArgs) s Q := by
    have fits := h.layout.2.2.1
    have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    refine WP.mono (loadBEFnArgs_ok s h.workspace size header ho h.ptr h.index) ?_
    rintro u ⟨ptr, dst, limbs, _, _, rest⟩
    exact ⟨ptr, (rest.gpr .r4 (by simp)).trans h.source, dst,
      (rest.gpr .r6 (by simp)).trans h.count, limbs⟩
  refine (pair_posts ct wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨loadBE_ct s t tr1 tr2 u v trivial trivial
    ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm,
      h.1.2.2.1.trans h.2.2.2.1.symm, h.1.2.2.2.1.trans h.2.2.2.2.1.symm,
      h.1.2.2.2.2.trans h.2.2.2.2.2.symm⟩ e1 e2, trivial⟩

theorem loadBEFn_ct {base src : BitVec 32} {len w o k : Nat} (ho : o < 8) :
    RelCT isa (fun s t => LoadFnReady base src len w o k s ∧
      LoadFnReady base src len w o k t ∧ s.sp = t.sp) loadBEFn (fun _ _ => True) := by
  have body := relCT_keep_sp
    ((loadBEFnBody_ct (base := base) (src := src) (len := len) (w := w) (k := k) ho).mono
      (P' := fun (s t : State) => LoadFnReady base src len w o k s ∧
        LoadFnReady base src len w o k t ∧ s.sp = t.sp)
      (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
  exact (body.seq (loadStack_ct .r0 0)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
