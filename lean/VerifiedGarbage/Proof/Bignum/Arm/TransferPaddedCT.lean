module

public import VerifiedGarbage.Proof.Bignum.Arm.TransferPadded
meta import VerifiedGarbage.Impl.Bignum.Arm.TransferArray
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.TransferArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Moving a residue from a narrower workspace reveals only the public addresses and widths -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem transferPadded_ct {base src : BitVec 32} {len slen w v o a : Nat} (ho : o < 8) (ha : a < 8) :
    RelCT isa (fun s t => TransferPaddedCtx base src len slen w v s ∧
      TransferPaddedCtx base src len slen w v t ∧ s.sp = t.sp) (transferArray o a) (fun _ _ => True) := by
  let P := TransferPaddedCtx base src len slen w v
  let Q := fun s : State => SmallFnReady src slen v a s ∧
    s.gpr .r4 = base + BitVec.ofNat 32 (arrAt w o)
  have args : RelCT isa (fun s t => P s ∧ P t) (.block (transferArrayArgs o a)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0, .r1])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.destination.ptr.trans h.2.destination.ptr.symm
    · exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block (transferArrayArgs o a)) s Q := by
    have fits := h.destination.layout.2.2.1
    have small : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.destination.workspace.nowrap (Nat.le_refl _) h.destination.layout
    rw [h.destination.width] at header
    refine WP.mono (transferArrayArgs_ok s h.destination.workspace small ho ha h.destination.ptr h.ptr (header.array o ho)) ?_
    rintro t ⟨ptr, output, index, mem, rest⟩
    exact ⟨⟨h.source.congr rest.wr, by rw [mem]; exact h.layout.layout,
      by rw [mem]; exact h.layout.width, ptr, index⟩, output⟩
  have copy : RelCT isa (fun s t => Q s ∧ Q t) exportArray (fun _ _ => True) :=
    (exportArray_ct (base := src) (dst := base + BitVec.ofNat 32 (arrAt w o)) (len := slen) (w := v) ha).mono
      (fun _ _ h => ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩) (fun _ _ _ => trivial)
  have body := relCT_keep_sp (((pair_posts args wp).seq copy).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ => trivial)) (fun _ _ h => h.2.2)
  exact ((body.seq (loadStack_ct .r0 0)).assoc).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
