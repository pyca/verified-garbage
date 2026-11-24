module

-- separate module: The AES-GCM output equations transport the source across initialization independently of register restoration.

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Buffers
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Tag
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.Proof.Gcm.StreamTo

/-! # The shared POWER payload under public caller bounds -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

theorem bound_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s e t u : State} (h : CallLayout s) (g : Positions s u) (oa : ReadyData s e t u) :
    WP isa VG.Impl.AesGcm.PPC64LE.Contiguous.payload u
      (fun v => Tagged u v (ctxH s.mem (s.gpr .r3)) (ivBytes s) (aadBytes s)) := by
  have sp := g.space h (by rw [oa.env.r29,oa.env.r30,oa.env.r31];exact oa.env.perm)
  have R : roundsOf u=10 ∨ roundsOf u=12 ∨ roundsOf u=14 := by rw [roundsOf,g.rounds];exact h.rounds
  refine payload_wp (sp.core R) R ?_ ?_ ?_ ?_ ?_ sp.ctx sp.counter (SealFused.data_tag_disjoint sp.bounds.dst.ok)
  · exact Proof.Gcm.ctr_zero _ _ _ _ (by rw [oa.env.r30];exact oa.cb)
  · rw [oa.env.r30];exact oa.abs
  · rw [g.aadLen];exact (length_bytesAt ..).symm
  · rw [oa.env.r29,ctxH_eq];exact oa.hH
  · rw [oa.env.r30];exact oa.j

abbrev ptBytes (s : State) := bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
abbrev ctBytes (s y : State) := bytesAt y.mem (s.gpr .r10) (stackArg s 0).toNat
abbrev cipherOf (s : State) := ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat

theorem ready_frame {s e t u : State} (p : Args s e) (q : Started e (work s) t) (oa : ReadyData s e t u) :
    Frame [stack s] s.mem u.mem := by
  refine (p.enteredFrame q).trans (oa.frame.sub fun r hr => ?_)
  rw [q.stream,q.scratch] at hr
  rcases List.mem_cons.mp hr with rfl|hr
  · exact ⟨_,List.mem_singleton_self _,fun addr mem => work_sub s addr ((Offset.sub_base _ (by decide : 16+80≤1152)) addr mem)⟩
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,fun addr mem => work_sub s addr ((Offset.sub_base _ (by decide : 96+16≤1152)) addr mem)⟩

structure Output (s t : State) : Prop where
  data : ctBytes s t = gctr (cipherOf s) (inc32 (j0 (ctxH s.mem (s.gpr .r3)) (ivBytes s))) (ptBytes s)
  tag : bytesAt t.mem (work s) 16=fullTag (cipherOf s) (ctxH s.mem (s.gpr .r3)) (ivBytes s) (aadBytes s) (ctBytes s t)

theorem tagged_output {s u v : State} (h : CallLayout s) (g : Positions s u) (f : Frame [stack s] s.mem u.mem)
    (o : Tagged u v (ctxH s.mem (s.gpr .r3)) (ivBytes s) (aadBytes s)) : Output s v := by
  have sep {r : Region} (hr : r∈argsRegions s) : ∀ x∈[stack s],r.Disjoint x := by
    intro x hx;obtain rfl := List.mem_singleton.mp hx;exact (stack_disjoint h hr).symm
  have keep := ciph_frame f (sep (r:=ctxR s) (by simp [argsRegions])) h.rounds
  have read := bytesAt_frame f (sep (r:=srcR s) (by simp [argsRegions])) (Nat.le_of_lt (stackArg s 0).isLt)
  have c : ctxCiph u.mem (u.gpr .r29) (roundsOf u)=cipherOf s := by rw [g.key,roundsOf,g.rounds];exact keep
  have att := o.tag
  have out := o.data
  rw [c,g.work,datLen,g.len,g.dst] at att
  rw [c,datLen,g.len,g.dst,g.src,read] at out
  exact ⟨by rw [Proof.Gcm.gctr_eq];exact out,att⟩

end VG.Proof.AesGcm.PPC64LE.Contiguous
