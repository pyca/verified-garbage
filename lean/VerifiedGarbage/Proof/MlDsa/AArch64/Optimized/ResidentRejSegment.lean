module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLoopState

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBytes
import Mathlib.Tactic.SplitIfs

/-! ## From `ResidentRejSetup.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (movQ_ok)
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def segmentInput (s : State) (k off : Nat) : Addr := s.gpr .x19+BitVec.ofNat 64 (840+1008*k+off)
def segmentOutput (s : State) (k : Nat) : Addr := s.gpr .x21+BitVec.ofNat 64 (1024*k)
def countAddress (s : State) (k : Nat) : Addr := s.gpr .x19+BitVec.ofNat 64 (counts+8*k)

/-- Segment setup recovers the existing accepted-prefix length from its
count slot and points to the next unfilled coefficient. -/
theorem setup_ok (n : Nat) (hn : n<65536) {s : State} {b p c : Addr} {L : List Zq}
    (hL : L.length≤256) (h24 : s.gpr .x24=b) (h25 : s.gpr .x25=p) (h26 : s.gpr .x26=c)
    (hr : InRegions (s.rd++s.wr) c 8) (hc : (s.mem.readW c 64).toNat=256-L.length) :
    WP isa (.block (setup n)) s fun t =>
      Only [.x2,.x3,.x4,.x5,.x6,.x9,.x10] s t ∧
      t.gpr .x2=b ∧ t.gpr .x3=coeffAddr p L.length ∧
      (t.gpr .x4).toNat=256-L.length ∧ (t.gpr .x5).toNat=n ∧
      (t.gpr .x9).toNat=q := by
  unfold setup
  refine wp_mov fun a ha ea => wp_mov fun b' hb eb =>
    wp_ldrx (a := c) (by decide)
      (by rw [hb.get .x26,ha.get .x26,h26]; exact BitVec.add_zero _)
      (by rw [hb.rd,ha.rd,hb.wr,ha.wr]; exact hr)
      fun d hd ed => wp_movz fun e he ee => wp_sub fun f hf ef =>
      wp_lsl (by decide) fun g hg eg => wp_add fun h hh eh =>
      wp_movz fun i hi ei => movQ_ok fun j hj ej => wp_movz fun t ht _ => wp_nil ?_
  have hcount : (d.gpr .x4).toNat=256-L.length := by
    rw [ed,hb.mem,ha.mem]
    exact hc
  have he6 : e.gpr .x6=256 := by rw [ee]; rfl
  have hf6 : (f.gpr .x6).toNat=L.length := by
    rw [ef,toNat_sub_n (by rw [he6,he.get .x4,hcount]; change 256-L.length≤256; omega),he6,
      he.get .x4,hcount]
    change 256-(256-L.length)=L.length
    omega
  have hg6 : g.gpr .x6=BitVec.ofNat 64 (4*L.length) := by
    apply BitVec.eq_of_toNat_eq
    rw [eg,toNat_lsl_n (by rw [hf6]; omega),hf6,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨(((((((((ha.trans hb).trans hd).trans he).trans hf).trans hg).trans hh).trans hi).trans hj).trans ht).mono (by decide),?_,?_,?_,?_,?_⟩
  · rw [ht.get .x2,hj.get .x2,hi.get .x2,hh.get .x2,hg.get .x2,hf.get .x2,
      he.get .x2,hd.get .x2,hb.get .x2,ea,h24]
  · rw [ht.get .x3,hj.get .x3,hi.get .x3,eh,hg.get .x3,hf.get .x3,he.get .x3,
      hd.get .x3,eb,ha.get .x25,h25,hg6]
  · rw [ht.get .x4,hj.get .x4,hi.get .x4,hh.get .x4,hg.get .x4,hf.get .x4,he.get .x4]
    exact hcount
  · rw [ht.get .x5,hj.get .x5,ei]
    simp only [BitVec.toNat_setWidth,BitVec.natCast_eq_ofNat,BitVec.toNat_ofNat]
    omega
  · rw [ht.get .x9]; exact ej

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSegment.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def segmentResult (s : State) (b : Addr) (n : Nat) (L : List Zq) : List Zq :=
 rnFold L (bytesAt s.mem b (3*n))

/-- A complete segment updates only its coefficient array and remaining
count slot; its output is the shared rejection fold of exactly its bytes.
It leaves x24, x25 and x26 at the next stream's segment and counts x27 down. -/
theorem segment_ok (v n : Nat) (hn : n<65536) {s : State} {b p c : Addr} {L : List Zq}
    (hL : L.length≤256) (hmod : n%4=0)
    (h24 : s.gpr .x24=b) (h25 : s.gpr .x25=p) (h26 : s.gpr .x26=c)
    (hl : StreamLayout s b p n)
    (hr : InRegions (s.rd++s.wr) c 8) (hw : InRegions s.wr c 8)
    (hc : (s.mem.readW c 64).toNat=256-L.length)
    (hst : Stored s.mem p L) (hsep : (polyR p).Disjoint ⟨c,8⟩) :
    WP isa (segment v n) s fun t =>
      Keep (parseRegs++([.x24,.x25,.x26,.x27] : List Reg)) s t ∧
      t.gpr .x24=b+BitVec.ofNat 64 1008 ∧ t.gpr .x25=p+BitVec.ofNat 64 1024 ∧
      t.gpr .x26=c+BitVec.ofNat 64 8 ∧ t.gpr .x27=s.gpr .x27-BitVec.ofNat 64 1 ∧
      Frame [polyR p,⟨c,8⟩] s.mem t.mem ∧
      (t.mem.readW c 64).toNat=256-(segmentResult s b n L).length ∧
      Stored t.mem p (segmentResult s b n L) := by
  refine WP.seq (WP.mono (setup_ok n hn hL h24 h25 h26 hr hc) fun a ⟨ha,h2,h3,h4,h5,h9⟩ => ?_)
  have hla : StreamLayout a b p n := by
    refine ⟨hl.bound,?_,?_,?_,?_,hl.disjoint⟩
    · intro j hj; rw [ha.rd,ha.wr]; exact hl.read16 j hj
    · intro j hj; rw [ha.rd,ha.wr]; exact hl.read4 j hj
    · intro j hj; rw [ha.wr]; exact hl.write4 j hj
    · intro j hj; rw [ha.wr]; exact hl.write16 j hj
  refine WP.seq (WP.mono (parse_ok v hla hmod hL h2 h3 h4 h5 h9
    (by rw [ha.mem]; exact hst)) fun d ⟨hd,hf,_,hcount,hstored⟩ => ?_)
  rw [ha.mem,candidateBytes_eq_bytesAt] at hcount hstored
  change (d.gpr .x4).toNat=256-(segmentResult s b n L).length at hcount
  change Stored d.mem p (segmentResult s b n L) at hstored
  unfold segmentNext
  refine wp_strx (a := c) (by decide)
    (by rw [hd.get .x26,ha.get .x26,h26]; exact BitVec.add_zero _)
    (by rw [hd.wr,ha.wr]; exact hw) fun e he => wp_addImm (by decide) fun f hf2 ef =>
    wp_addImm (by decide) fun g hg eg => wp_addImm (by decide) fun h hh eh =>
    wp_subImm (by decide) fun t ht et => wp_nil ?_
  have hs : Frame [⟨c,8⟩] d.mem t.mem := by
    rw [ht.mem,hh.mem,hg.mem,hf2.mem,he.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)
  have hm : t.mem=d.mem.writeW c (d.gpr .x4) := by rw [ht.mem,hh.mem,hg.mem,hf2.mem,he.mem]
  refine ⟨((((((ha.keep.trans hd).trans he.keep).trans hf2.keep).trans hg.keep).trans
    hh.keep).trans ht.keep).mono (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.get .x24,hh.get .x24,hg.get .x24,ef,he.gpr,hd.get .x24,ha.get .x24,h24]
  · rw [ht.get .x25,hh.get .x25,eg,hf2.get .x25,he.gpr,hd.get .x25,ha.get .x25,h25]
  · rw [ht.get .x26,eh,hg.get .x26,hf2.get .x26,he.gpr,hd.get .x26,ha.get .x26,h26]
  · rw [et,hh.get .x27,hg.get .x27,hf2.get .x27,he.gpr,hd.get .x27,ha.get .x27]
  · have hfirst : Frame [polyR p,⟨c,8⟩] s.mem d.mem := by
      rw [←ha.mem]
      exact hf.mono (by simp)
    exact hfirst.trans (hs.mono (by simp))
  · rw [hm,Mem.readW_writeW_self64]
    exact hcount
  · exact stored_frame hs (by intro r hr; rw [List.mem_singleton.mp hr]; exact hsep)
      hstored (rnFold_length_le hL _)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
