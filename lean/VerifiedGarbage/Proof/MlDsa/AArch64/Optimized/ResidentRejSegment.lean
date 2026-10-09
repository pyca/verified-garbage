import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBytes

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def segmentResult (s : State) (k off n : Nat) (L : List Zq) : List Zq :=
 rnFold L (bytesAt s.mem (segmentInput s k off) (3*n))

/-- A complete segment updates only its coefficient array and remaining
count slot; its output is the shared rejection fold of exactly its bytes. -/
theorem segment_ok (v k off n : Nat) (hk : k<4) (ho : off<4096) (hn : n<65536)
    {s : State} {L : List Zq} (hL : L.length≤256) (hmod : n%4=0)
    (hl : StreamLayout s (segmentInput s k off) (segmentOutput s k) n)
    (hr : InRegions (s.rd++s.wr) (countAddress s k) 8)
    (hw : InRegions s.wr (countAddress s k) 8)
    (hc : (s.mem.readW (countAddress s k) 64).toNat=256-L.length)
    (hst : Stored s.mem (segmentOutput s k) L)
    (hsep : (polyR (segmentOutput s k)).Disjoint ⟨countAddress s k,8⟩) :
    WP isa (segment v k off n) s fun t =>
      Keep parseRegs s t ∧
      Frame [polyR (segmentOutput s k),⟨countAddress s k,8⟩] s.mem t.mem ∧
      (t.mem.readW (countAddress s k) 64).toNat=256-(segmentResult s k off n L).length ∧
      Stored t.mem (segmentOutput s k) (segmentResult s k off n L) := by
  refine WP.seq (WP.mono (setup_ok k off n hk ho hn hL hr hc) fun a ⟨ha,h2,h3,h4,h5,h9⟩ => ?_)
  have hla : StreamLayout a (segmentInput s k off) (segmentOutput s k) n := by
    refine ⟨hl.bound,?_,?_,?_,?_,hl.disjoint⟩
    · intro j hj; rw [ha.rd,ha.wr]; exact hl.read16 j hj
    · intro j hj; rw [ha.rd,ha.wr]; exact hl.read4 j hj
    · intro j hj; rw [ha.wr]; exact hl.write4 j hj
    · intro j hj; rw [ha.wr]; exact hl.write16 j hj
  refine WP.seq (WP.mono (parse_ok v hla hmod hL h2 h3 h4 h5 h9
    (by rw [ha.mem]; exact hst)) fun b ⟨hb,hf,_,hcount,hstored⟩ => ?_)
  rw [ha.mem,candidateBytes_eq_bytesAt] at hcount hstored
  change (b.gpr .x4).toNat=256-(segmentResult s k off n L).length at hcount
  change Stored b.mem (segmentOutput s k) (segmentResult s k off n L) at hstored
  refine wp_strx (a := countAddress s k) (by unfold counts; constructor <;> omega)
    (by rw [hb.get .x19,ha.get .x19]; rfl)
    (by rw [hb.wr,ha.wr]; exact hw) fun t ht => wp_nil ?_
  have hs : Frame [⟨countAddress s k,8⟩] b.mem t.mem := by
    rw [ht.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)
  refine ⟨((ha.keep.trans hb).trans ht.keep).mono (by decide),?_,?_,?_⟩
  · have hfirst : Frame [polyR (segmentOutput s k),⟨countAddress s k,8⟩] s.mem b.mem := by
      rw [←ha.mem]
      exact hf.mono (by simp)
    exact hfirst.trans (hs.mono (by simp))
  · rw [ht.mem,Mem.readW_writeW_self64]
    exact hcount
  · exact stored_frame hs (by intro r hr; rw [List.mem_singleton.mp hr]; exact hsep)
      hstored (rnFold_length_le hL _)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
