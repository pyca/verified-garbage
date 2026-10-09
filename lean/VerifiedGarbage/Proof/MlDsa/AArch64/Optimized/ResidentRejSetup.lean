import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse

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
