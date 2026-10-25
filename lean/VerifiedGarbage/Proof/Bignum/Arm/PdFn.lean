module
public import VerifiedGarbage.Proof.Bignum.Arm.PdChecked
public import VerifiedGarbage.Proof.Bignum.Arm.PdInput

import VerifiedGarbage.Proof.Bignum.Arm.PublicSaved
import VerifiedGarbage.Proof.Bignum.Arm.PdBody
import VerifiedGarbage.Proof.Bignum.Arm.PdEntryReady
import VerifiedGarbage.Proof.Framework.Block

/-! # Callable ARMv7 checked public RSA preserves AAPCS and implements the shared result -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem pdFn_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdFnInput base dst np ep xp len k eLen N R eb xb s) :
    WP isa PdFn.code s fun t => abiPreserved s t ∧
      (if Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) then PdOutput dst k N R eb xb t
       else t.gpr .r0 = 0 ∧ Spec.Rsa.bytesAt t.mem (State.addr dst) k = List.replicate k 0) := by
  unfold PdFn.code
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (pd_entry_ready s h) ?_
  rintro u ⟨ready, _, savedU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (pdBody_ok u ready) ?_
  rintro v ⟨result, frameV, restV⟩
  have spV : v.sp = s.sp - BitVec.ofNat 32 56 := restV.sp.trans restU.sp
  have wrV : v.wr = (pcPushed s).wr := restV.wr.trans restU.wr
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr pcCalleeSaved := by
    rw [restV.sp]
    apply public_callee_saved savedU frameV
    · rw [restU.sp]; exact h.stackWorkspace
    · rw [restU.sp]; exact h.stackOutput
  have fit : v.sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' h.stackFit]
    have := s.sp.isLt
    omega
  have read : InRegions (v.rd ++ v.wr) (State.addr v.sp) 56 := by
    refine ⟨⟨State.addr v.sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (pc_restore_ok v s.gpr fit read saved) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = v.gpr .r0 := restT.gpr .r0 (by decide)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by decide)
    · exact restored (.r5, 20) (by decide)
    · exact restored (.r6, 24) (by decide)
    · exact restored (.r7, 28) (by decide)
    · exact restored (.r8, 32) (by decide)
    · exact restored (.r9, 36) (by decide)
    · exact restored (.r10, 40) (by decide)
    · exact restored (.r11, 44) (by decide)
    · exact restored (.lr, 52) (by decide)
  · rw [popped_sp, restT.sp, spV]
    exact BitVec.sub_add_cancel _ _
  · unfold PdOutput at result ⊢
    simp only [popped_gpr (by decide : Reg.r0 ≠ .r12), popped_mem, memT, ret]
    exact result

end VG.Proof.Bignum.Arm
