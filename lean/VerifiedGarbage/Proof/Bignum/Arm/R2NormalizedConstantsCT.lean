module

import VerifiedGarbage.Proof.Bignum.Arm.R2NormalizedConstants
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

/-! Normalized initialization touches only public workspace addresses. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (wp_ldr)

theorem r2TopBit_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t)
      (.block r2TopBit) (fun _ _ => True) := by
  let pre : List Instr := [.ldr .r4 .r0 96, .ldr .r1 .r0 48]
  let Q := fun s : State => s.gpr .r4 = base + BitVec.ofNat 32 (arrAt w 4) ∧
    s.gpr .r1 = BitVec.ofNat 32 w
  have ct : RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t)
      (.block pre) (fun _ _ => True) := by
    unfold pre
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h.1.ptr.trans h.2.ptr.symm)
  have post (s : State) (h : ArithmeticReady base len w s) : WP isa (.block pre) s Q := by
    have fits := h.layout.2.2.1
    have size : 100 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    unfold pre
    refine wp_ldr (a := off (State.addr base) 96) (by decide)
      (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega))
      (h.workspace.read (by omega)) fun u hu => ?_
    refine wp_ldr (a := off (State.addr base) 48) (by decide)
      (by rw [hu.other .r0 (by decide), h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega))
      (by rw [hu.rd, hu.wr]; exact h.workspace.read (off := 48) (by omega)) fun t ht => WP.block_nil ?_
    exact ⟨(ht.other .r4 (by decide)).trans (hu.gpr.trans (header.array 4 (by decide))),
      ht.gpr.trans (by rw [hu.mem]; exact header.count)⟩
  have setup := (ct.wp (fun s t h => ⟨post s h.1, post t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  unfold r2TopBit
  change RelCT isa _ (.block (pre ++ _)) _
  apply RelCT.block_append
  refine setup.seq (RelCT.taint (A := taint) (Taint.ofRegs [.r4, .r1]) ?_ (by taint_decide))
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem r2NormalizedConstants_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      r2NormalizedConstants (fun _ _ => True) := by
  let Z := fun s : State => ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 4 = 0
  have first := relCT_keep_sp
    (smallConst_ct (base := base) (len := len) (w := w) (o := 4) 0
      (by decide) (by decide) (by decide)) (fun _ _ h => h.2.2)
  have wp (s : State) (h : ArithmeticReady base len w s) : WP isa (smallConst 4 0) s Z :=
    WP.mono (smallConst_ok s 0 h (o := 4) (by decide) (by decide) (by decide) (by decide))
      (fun _ h => ⟨h.1, h.2.1⟩)
  have setup := (first.wp (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)).mono
    (Q' := fun (s t : State) => Z s ∧ Z t ∧ s.sp = t.sp)
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)
  have top := relCT_keep_sp ((r2TopBit_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) => Z s ∧ Z t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
  have topReady := (top.wp (fun s t h =>
    ⟨WP.mono (r2TopBitReady_ok s h.1.1 h.1.2) (fun _ h => h.1),
      WP.mono (r2TopBitReady_ok t h.2.1.1 h.2.1.2) (fun _ h => h.1)⟩)).mono
    (Q' := fun (s t : State) => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)
  exact setup.seq (topReady.seq (smallConst_ct 2 (o := 7) (by decide) (by decide) (by decide)))

end VG.Proof.Bignum.Arm
