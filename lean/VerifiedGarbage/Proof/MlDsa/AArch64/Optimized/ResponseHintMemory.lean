import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintInit

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

structure HintData where
  mem : Mem
  counts : BitVec 128
  flags : BitVec 128

def hintCtAt (m : Mem) (a : Addr) (j e : Nat) : BitVec 32 :=
  reduceWord (vword (m.read (a+BitVec.ofNat 64 (16*j)) 16) e)
def hintAt (B : BitVec 32) (m : Mem) (p a h : Addr) (j e : Nat) : BitVec 32 :=
  hintWord B (hintCtAt m a j e+vword (m.read (p+BitVec.ofNat 64 (16*j)) 16) e)
    (vword (m.read (h+BitVec.ofNat 64 (16*j)) 16) e)
def hintStep (B : BitVec 32) (p a h : Addr) (j : Nat) (d : HintData) : HintData :=
  { mem := d.mem.write (p+BitVec.ofNat 64 (16*j)) 16 (laneVector (hintAt B d.mem p a h j))
    counts := laneVector fun e => vword d.counts e+hintAt B d.mem p a h j e
    flags := laneVector fun e => vword d.flags e ||| normMask (hintCtAt d.mem a j e) (B-1) (B+(B-1)) }
def hintRun (m : Mem) (B : BitVec 32) (p a h : Addr) : Nat → HintData
  | 0 => ⟨m,0,0⟩
  | j+1 => hintStep B p a h j (hintRun m B p a h j)

theorem hintGroup_step {B : BitVec 32} {s : State} {d : HintData} {p a h : Addr} {u i : Nat}
    (hi : i<4) (hr : HintReady B s) (hm : s.mem=d.mem)
    (hf : s.v .v31=d.flags) (hc : s.v .v30=d.counts)
    (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u)) (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u))
    (h2 : s.gpr .x2=h+BitVec.ofNat 64 (64*u))
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hd : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (16*i)) 16)
    (hw : InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (hintGroup (16*i))) s fun t =>
      StepKeep [.v0,.v2,.v3,.v4,.v6,.v30,.v31] s t ∧ HintReady B t ∧
      t.mem=(hintStep B p a h (4*u+i) d).mem ∧
      t.v .v31=(hintStep B p a h (4*u+i) d).flags ∧
      t.v .v30=(hintStep B p a h (4*u+i) d).counts := by
  have addr (r : Reg) (q : Addr) (hv : s.gpr r=q+BitVec.ofNat 64 (64*u)) :
      s.gpr r+BitVec.ofNat 64 (16*i)=q+BitVec.ofNat 64 (16*(4*u+i)) := by
    rw [hv,BitVec.add_assoc,← BitVec.ofNat_add,show 64*u+16*i=16*(4*u+i) by omega]
  have hct : hintCt s (16*i)=hintCtAt d.mem a (4*u+i) := by
    funext e; simp only [hintCt,hintCtAt,hm,addr _ _ h1]
  have hout : ∀e<4,hintOutput s (16*i) e=hintAt B d.mem p a h (4*u+i) e := by
    intro e he
    simp only [hintOutput,hintInput,hintAt,hct,hm,addr _ _ h0,addr _ _ h2,hr.gamma e he]
  have houtv : laneVector (hintOutput s (16*i))=laneVector (hintAt B d.mem p a h (4*u+i)) := by
    apply vec_ext; intro e he
    rw [laneVector_word _ he,laneVector_word _ he,hout e he]
  rw [←List.append_nil (hintGroup (16*i))]
  refine hintGroup_ok (by omega) ha hb hd hw hr.q hr.c
    (by intro e he; rw [hr.negGamma e he,hr.gamma e he]) hr.zero
    fun t hk hmem hcount hflag => WP.block_nil_iff.mpr ?_
  refine ⟨hk,hr.frame hk.vec (by decide),?_,?_,?_⟩
  · simpa only [hintStep,hm,addr _ _ h0,houtv] using hmem
  · apply vec_ext; intro e he
    rw [hflag e he,hct,hr.lo e he,hr.width e he,hf]
    dsimp only [hintStep]
    rw [laneVector_word _ he]
  · apply vec_ext; intro e he
    rw [hcount e he,hout e he,hc]
    dsimp only [hintStep]
    rw [laneVector_word _ he]

end VG.Proof.MlDsa.AArch64.Optimized.Response
