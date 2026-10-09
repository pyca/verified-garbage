import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

structure ZData where
  mem : Mem
  flags : BitVec 128

def zWords (m : Mem) (p a : Addr) (j e : Nat) : BitVec 32 :=
  reduceWord (vword (m.read (p+BitVec.ofNat 64 (16*j)) 16) e+
    vword (m.read (a+BitVec.ofNat 64 (16*j)) 16) e)
def zStep (p a : Addr) (B : BitVec 32) (j : Nat) (d : ZData) : ZData :=
  { mem := d.mem.write (p+BitVec.ofNat 64 (16*j)) 16 (laneVector (zWords d.mem p a j))
    flags := laneVector fun e => vword d.flags e ||| normMask (zWords d.mem p a j e) (B-1) (B+(B-1)) }
def zRun (m : Mem) (p a : Addr) (B : BitVec 32) : Nat → ZData
  | 0 => ⟨m,0⟩
  | j+1 => zStep p a B j (zRun m p a B j)

theorem zRun_next (m : Mem) (p a : Addr) (B : BitVec 32) (j : Nat) :
    zRun m p a B (j+1)=zStep p a B j (zRun m p a B j) := rfl

theorem addInput_shift {s : State} {m : Mem} {p a : Addr} {u i : Nat}
    (hm : s.mem=m) (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u))
    (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u)) :
    addInput s (16*i)=zWords m p a (4*u+i) := by
  funext e
  simp only [addInput,zWords,hm,h0,h1,BitVec.add_assoc,← BitVec.ofNat_add]
  rw [show 64*u+16*i=16*(4*u+i) by omega]

theorem addGroup_step {s : State} {d : ZData} {p a : Addr} {B : BitVec 32} {u i : Nat}
    (hi : i<4) (hr : ZReady B s) (hm : s.mem=d.mem) (hf : s.v .v31=d.flags)
    (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u)) (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u))
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (addGroup (16*i))) s fun t =>
      StepKeep [.v0,.v1,.v2,.v6,.v31] s t ∧ ZReady B t ∧
      t.mem=(zStep p a B (4*u+i) d).mem ∧ t.v .v31=(zStep p a B (4*u+i) d).flags := by
  have hinput := addInput_shift (i := i) hm h0 h1
  have haddr : s.gpr .x0+BitVec.ofNat 64 (16*i)=p+BitVec.ofNat 64 (16*(4*u+i)) := by
    rw [h0,BitVec.add_assoc,← BitVec.ofNat_add,show 64*u+16*i=16*(4*u+i) by omega]
  rw [← List.append_nil (addGroup (16*i))]
  refine addGroup_ok (by omega) ha hb hw hr.q hr.c fun t hk hmem hflag => WP.block_nil_iff.mpr ?_
  refine ⟨hk,hr.frame (by decide) hk.vec,?_,?_⟩
  · simpa only [zStep,hm,haddr,hinput] using hmem
  · apply vec_ext
    intro e he
    rw [hflag e he,hr.lo e he,hr.width e he,hf,hinput]
    simp only [zStep,laneVector_word _ he]

end VG.Proof.MlDsa.AArch64.Optimized.Response
