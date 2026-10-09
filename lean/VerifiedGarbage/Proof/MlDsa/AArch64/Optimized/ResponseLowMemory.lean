import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowReady

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round (IsG)

structure LowData where
  mem : Mem
  flags : BitVec 128

def lowInput (m : Mem) (p a : Addr) (j e : Nat) : BitVec 32 :=
  Inverse.signCorrected (reduceWord (vword (m.read (p+BitVec.ofNat 64 (16*j)) 16) e-
    vword (m.read (a+BitVec.ofNat 64 (16*j)) 16) e))
def lowOutput (g : Nat) (m : Mem) (p a : Addr) (j e : Nat) : BitVec 32 :=
  lowWord (lowInput m p a j e) (HighPack.highWord g (lowInput m p a j e)) (BitVec.ofNat 32 (2*g))
def lowStep (g B : Nat) (p a l : Addr) (j : Nat) (d : LowData) : LowData :=
  { mem := (d.mem.write (p+BitVec.ofNat 64 (16*j)) 16
      (laneVector (fun e => HighPack.highWord g (lowInput d.mem p a j e)))).write
        (l+BitVec.ofNat 64 (16*j)) 16 (laneVector (lowOutput g d.mem p a j))
    flags := laneVector fun e => vword d.flags e ||| normMask (lowOutput g d.mem p a j e)
      (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1)) }
def lowRun (m : Mem) (g B : Nat) (p a l : Addr) : Nat → LowData
  | 0 => ⟨m,0⟩
  | j+1 => lowStep g B p a l j (lowRun m g B p a l j)

theorem subInput_shift {s : State} {m : Mem} {p a : Addr} {u i : Nat}
    (hm : s.mem=m) (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u))
    (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u)) :
    subInput s (16*i)=lowInput m p a (4*u+i) := by
  funext e
  simp only [subInput,lowInput,hm,h0,h1,BitVec.add_assoc,← BitVec.ofNat_add]
  rw [show 64*u+16*i=16*(4*u+i) by omega]

theorem subGroup_step {g B : Nat} (hg : IsG g) {s : State} {d : LowData} {p a l : Addr} {u i : Nat}
    (hi : i<4) (hr : LowReady g B s) (hm : s.mem=d.mem) (hf : s.v .v31=d.flags)
    (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u)) (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u))
    (h2 : s.gpr .x2=l+BitVec.ofNat 64 (64*u))
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hl : InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (subGroup g (16*i))) s fun t =>
      StepKeep [.v0,.v1,.v2,.v6,.v7,.v31] s t ∧ LowReady g B t ∧
      t.mem=(lowStep g B p a l (4*u+i) d).mem ∧ t.v .v31=(lowStep g B p a l (4*u+i) d).flags := by
  have hinput := subInput_shift (i:=i) hm h0 h1
  have hout : ∀e<4,subLow g s (16*i) e=lowOutput g d.mem p a (4*u+i) e := by
    intro e he
    simp only [subLow,lowOutput,hinput,hr.twiceG e he]
  have houtv : laneVector (subLow g s (16*i))=laneVector (lowOutput g d.mem p a (4*u+i)) := by
    apply vec_ext; intro e he
    rw [laneVector_word _ he,laneVector_word _ he,hout e he]
  have addr (r : Reg) (q : Addr) (h : s.gpr r=q+BitVec.ofNat 64 (64*u)) :
      s.gpr r+BitVec.ofNat 64 (16*i)=q+BitVec.ofNat 64 (16*(4*u+i)) := by
    rw [h,BitVec.add_assoc,← BitVec.ofNat_add,show 64*u+16*i=16*(4*u+i) by omega]
  rw [← List.append_nil (subGroup g (16*i))]
  refine subGroup_ok hg (by omega) ha hb hw hl hr.q hr.round32 hr.halfQ hr.toHighConstants
    fun t hk hmem hflag => WP.block_nil_iff.mpr ?_
  refine ⟨hk,hr.group hk,?_,?_⟩
  · simpa only [lowStep,hm,addr _ _ h0,addr _ _ h2,hinput,houtv] using hmem
  · apply vec_ext
    intro e he
    rw [hflag e he,hr.normLo e he,hr.normWidth e he,hf,hout e he]
    dsimp only [lowStep]
    rw [laneVector_word _ he]

end VG.Proof.MlDsa.AArch64.Optimized.Response
