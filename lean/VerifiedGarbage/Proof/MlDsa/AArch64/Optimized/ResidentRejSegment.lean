import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBytes

/-! ## From `ResidentRejSetup.lean` -/

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
theorem setup_ok (k off n : Nat) (hk : k<4) (ho : off<4096) (hn : n<65536)
    {s : State} {L : List Zq} (hL : L.length≤256)
    (hr : InRegions (s.rd++s.wr) (countAddress s k) 8)
    (hc : (s.mem.readW (countAddress s k) 64).toNat=256-L.length) :
    WP isa (.block (setup k off n)) s fun t =>
      Only [.x2,.x3,.x4,.x5,.x6,.x9,.x10] s t ∧
      t.gpr .x2=segmentInput s k off ∧
      t.gpr .x3=coeffAddr (segmentOutput s k) L.length ∧
      (t.gpr .x4).toNat=256-L.length ∧ (t.gpr .x5).toNat=n ∧
      (t.gpr .x9).toNat=q := by
  unfold setup
  refine wp_addImm (by omega) fun a ha ea => wp_addImm ho fun b hb eb =>
    wp_addImm (by omega) fun c hcc ec =>
    wp_ldrx (a := countAddress s k) (by unfold counts; constructor <;> omega)
      (by rw [hcc.get .x19,hb.get .x19,ha.get .x19]; rfl)
      (by rw [hcc.rd,hb.rd,ha.rd,hcc.wr,hb.wr,ha.wr]; exact hr)
      fun d hd ed => wp_movz fun e he ee => wp_sub fun f hf ef =>
      wp_lsl (by decide) fun g hg eg => wp_add fun h hh eh =>
      wp_movz fun i hi ei => movQ_ok fun j hj ej => wp_movz fun t ht _ => wp_nil ?_
  have hcount : (d.gpr .x4).toNat=256-L.length := by
    rw [ed,hcc.mem,hb.mem,ha.mem]
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
  refine ⟨((((((((((ha.trans hb).trans hcc).trans hd).trans he).trans hf).trans hg).trans hh).trans hi).trans hj).trans ht).mono (by decide),?_,?_,?_,?_,?_⟩
  · rw [ht.get .x2,hj.get .x2,hi.get .x2,hh.get .x2,hg.get .x2,hf.get .x2,
      he.get .x2,hd.get .x2,hcc.get .x2,eb,ea,Offset.add_add]
    rfl
  · rw [ht.get .x3,hj.get .x3,hi.get .x3,eh,hg.get .x3,hf.get .x3,he.get .x3,
      hd.get .x3,ec,hb.get .x21,ha.get .x21,hg6]
    rfl
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

end
