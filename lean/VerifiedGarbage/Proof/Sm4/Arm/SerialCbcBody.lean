module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcLoop
import VerifiedGarbage.Proof.Sm4.Arm.Core
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4.Arm.SerialCbc
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sm4.Arm.BatchChain
import VerifiedGarbage.Proof.Sm4.Arm.BatchEntry
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Cbc

/-! # Functional composition of the prepared, serial SM4-CBC encryption implementation -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.SerialCbcBody

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR)
open VG.Proof.Sm4.Arm.BatchXor
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchEntry VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.SerialCbcLoop VG.Proof.Sm4.Arm.BatchGroup
open VG.Spec.Aes (bytesAt)

structure Post (s₀ s : State) : Prop where
  regs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  data : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) =
    Spec.Cbc.encrypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀))))
      (bytesAt s₀.mem (State.addr (Iv s₀)) 16) (Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀))
  iv : bytesAt s.mem (State.addr (Iv s₀)) 16 =
    Spec.Cbc.next (bytesAt s₀.mem (State.addr (Iv s₀)) 16)
      (Spec.Cbc.encrypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀))))
        (bytesAt s₀.mem (State.addr (Iv s₀)) 16)
        (Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀)))
  sp : s.sp = s₀.sp

theorem body_wp {s₀ : State} (hp : Pre s₀) : WP isa SerialCbc.encrypt s₀ (Post s₀) := by
  have hw := hp.writable (r := wsR s₀) (by simp)
  have hd := hp.writable (r := dataR s₀) (by simp)
  have hi := hp.writable (r := ivR s₀) (by simp)
  refine WP.seq (WP.mono (prologue_wp hp) fun s₁ p => ?_)
  have blocks₁ : Spec.Cbc.blocksAt s₁.mem (State.addr (Dp s₀)) (N s₀) =
      Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀) := by
    unfold Spec.Cbc.blocksAt
    apply List.map_congr_left
    intro j hj
    apply bytes_frame (P := dataAddr (Dp s₀) j) p.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ds.sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; change 16 * j + 16 ≤ 16 * N s₀; omega))
  refine WP.seq (WP.mono (loopOrEmpty_wp (s₀.gpr .r3).isLt p.base p.data p.left p.z hp.fitB hp.fitD
    (by rw [p.wr]; exact hw) (by rw [p.wr]; exact hd) hp.ds p.table p.counter) fun s₂ l => ?_)
  have base₂ : s₂.gpr sb = Sc s₀ := (l.regs _ (by simp [sb])).trans p.base
  have iv₂ : s₂.gpr .r5 = Iv s₀ := (l.regs _ (by simp)).trans p.iv
  have saved₂ := p.saved.frame mode_slots l.frame (fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (d := 1456) (n := 36) (k := 4 * slots) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact hp.ds.symm.sub_left (Offset.sub_base _ (by decide)))
  have cp : ChainPre s₂ (Sc s₀) (Iv s₀) :=
    ⟨base₂, iv₂, hp.fitB, hp.fitI, by rw [l.wr, p.wr]; exact hw,
      by rw [l.wr, p.wr]; exact hi, hp.ivs⟩
  have output := loop_output l
  rw [blocks₁] at output
  apply (WP.block_append_iff (M := isa) (l₁ := BatchCtr.copyCounterOut)
    (l₂ := ([movR .r12 sb] : List Instr) ++ BatchCtr.restore)).mpr
  refine WP.mono (counterOut_wp cp) fun s₃ c => ?_
  have saved₃ := saved₂.frame mode_slots c.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ivs.symm.sub_left (Offset.sub_base _ (by decide)))
  have blocks₃ : Spec.Cbc.blocksAt s₃.mem (State.addr (Dp s₀)) (N s₀) =
      Spec.Cbc.blocksAt s₂.mem (State.addr (Dp s₀)) (N s₀) := by
    unfold Spec.Cbc.blocksAt
    apply List.map_congr_left
    intro j hj
    apply bytes_frame (P := dataAddr (Dp s₀) j) c.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.id.symm.sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; change 16 * j + 16 ≤ 16 * N s₀; omega))
  refine WP.mono (restore_wp ((c.regs _ (by decide) (by decide)).trans base₂) hp.fitB
    (by rw [c.wr, l.wr, p.wr]; exact hw) saved₃) fun s₄ ⟨regs, mem, _, _, sp⟩ => ?_
  refine ⟨regs, ?_, ?_, sp.trans (c.sp.trans (l.sp.trans p.sp))⟩
  · rw [mem, blocks₃]; exact output
  · rw [mem, c.block, l.counter, chain_next, blocks₁]

end VG.Proof.Sm4.Arm.SerialCbcBody
