module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivRestore
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivFinal
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_private_checked` on PPC64LE: correctness

The blocks and calls in order (`code_correct`), from the frame's push to its
pop, to the outcome (`final_ok`), on the registers and the stack (`fnPost`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenOutcome s'.mem (s.gpr .r3) (s.gpr .r6).toNat ((s'.gpr .r3).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

theorem freed_sp (b : Nat) (s : State) : (freed b s).sp = s.sp + BitVec.ofNat 64 b := rfl
theorem freed_lr (b : Nat) (s : State) : (freed b s).lr = s.lr := rfl
theorem freed_gpr (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl
theorem freed_mem (b : Nat) (s : State) : (freed b s).mem = s.mem := rfl

theorem code_correct (s : State) (hpre : (Spec.Rsa.privateCheckedContract abi frameBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa code s fun t => abiPreserved s t ∧ fnPost s t
  have h := preP_of hpre
  have hk := h.k2
  unfold code
  refine WP.alloc ⟨by decide, by decide, by decide⟩ h.sp1 ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (crtCall_ok h A fun t₂ M C => ?_)
  refine WP.seq (WP.mono (preArgs_ok h M C) fun t₃ P => ?_)
  refine WP.seq (preCall_ok h P fun t₄ Q4 => ?_)
  refine WP.seq (WP.mono (pubArgs_ok h Q4) fun t₅ R => ?_)
  refine WP.seq (pubCall_ok h R fun t₆ C6 => ?_)
  refine WP.seq (WP.mono (cmpArgs_ok h C6) fun t₇ L => ?_)
  refine WP.seq (WP.mono (compare_ok h L) fun t₈ ⟨a8, m8, k8⟩ => ?_)
  have L8 : Late s t₈ := L.toLate.keep k8 m8
  have iSt : InRegions (t₈.rd ++ t₈.wr) (fb s + BitVec.ofNat 64 oSt) 8 := by
    rw [L8.wr]; exact in_fr' s _ _ (by decide) (by decide)
  have iEs : InRegions (t₈.rd ++ t₈.wr) (fb s + BitVec.ofNat 64 oEs) 8 := by
    rw [L8.wr]; exact in_fr' s _ _ (by decide) (by decide)
  refine WP.seq (WP.mono (result_ok (cs := t₇.mem.readW (fb s + BitVec.ofNat 64 oSt) 64)
    (es := t₇.mem.readW (fb s + BitVec.ofNat 64 oEs) 64) L8.sp iSt iEs (by rw [m8]) (by rw [m8]) a8 (cmpAcc_lt _ _ _ _) L8.r24 L8.r26)
    fun t₉ ⟨⟨r3, r9, r6, r7, r8, m9⟩, k9⟩ => ?_)
  have L9 : Late s t₉ := L8.keep k9 m9
  refine WP.seq (WP.mono (release_ok h L9 (fun b => Proof.Rsa.low_and_mask b _ _) r6 r7 r8 r9)
    fun t₁₀ ⟨hout, f10, k10⟩ => ?_)
  have L10 := L9.release h k10 f10
  refine WP.mono (restore_ok L10) fun v ⟨vp, vl, vs, vm, v3⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [freed_gpr]; exact vp r hr
  · rw [freed_sp, vs]; exact BitVec.sub_add_cancel _ _
  · rw [freed_lr]; exact vl
  · unfold fnPost
    rw [freed_mem, freed_gpr, vm, v3, k10.gpr .r3 (by decide), r3]
    have m97 : t₉.mem = t₇.mem := m9.trans m8
    rw [m97] at hout
    have hx : Spec.Rsa.bytesAt t₇.mem (s.gpr .r9) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat :=
      bytes_of_frame L.mem (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have ei : (⟨s.gpr .r9, (s.gpr .r6).toNat⟩ : Region) = iR s := by simp only [iR, h.h10]
        rw [ei]
        rcases hr with rfl | rfl | rfl
        · exact h.ki.symm
        · exact h.oi.symm
        · exact h.is) (by have := h.wi; rw [h.h10] at this; omega)
    refine final_ok (Proof.Rsa.bytesAt_length' _ _ _) (Proof.Rsa.bytesAt_length' _ _ _) L.crt L.pub ?_ hout
    rw [cmpAcc_eq_zero, ← hx, Proof.Rsa.bytesAt_eq_iff]

end VG.Proof.Rsa.PPC64LE.Priv
