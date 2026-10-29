module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFlags
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit

import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintFlags
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
/-! ## From `ResponseZSemantic.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/ResponseZMemory.lean`, which only this module imported.
section

@[expose] public section

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
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16 vword_read16 vector_contains)

theorem zWords_coeff (m : Mem) (p a : Addr) (j : Nat) {e : Nat} (he : e<4) :
    zWords m p a j e=reduceWord (coeffAt m p (4*j+e)+coeffAt m a (4*j+e)) := by
  unfold zWords
  rw [show 16*j=4*(4*j) by omega]
  change reduceWord (vword (m.read (coeffAddr p (4*j)) 16) e+
    vword (m.read (coeffAddr a (4*j)) 16) e)=_
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,coeffAddr_add]
  rfl

theorem zStep_coeff (d : ZData) (p a : Addr) (B : BitVec 32) {j k : Nat}
    (hj : j<64) (hk : k<256) :
    coeffAt (zStep p a B j d).mem p k =
      if 4*j≤k ∧ k<4*j+4 then reduceWord (coeffAt d.mem p k+coeffAt d.mem a k)
      else coeffAt d.mem p k := by
  simp only [zStep]
  rw [show 16*j=4*(4*j) by omega]
  change coeffAt (d.mem.write (coeffAddr p (4*j)) 16 _) p k=_
  rw [coeffAt_write16 _ _ (by omega) _ hk]
  split
  · rename_i h
    rw [laneVector_word _ (by omega),zWords_coeff _ _ _ _ (by omega),show 4*j+(k-4*j)=k by omega]
  · rfl

theorem zRun_frame (m : Mem) (p a : Addr) (B : BitVec 32) {j : Nat} (hj : j≤64) :
    Frame [pR p] m (zRun m p a B j).mem := by
  induction j with
  | zero => exact Frame.refl _ _
  | succ j ih =>
    rw [zRun_next]
    simp only [zStep]
    rw [show 16*j=4*(4*j) by omega]
    change Frame [pR p] m ((zRun m p a B j).mem.write (coeffAddr p (4*j)) 16 _)
    exact (ih (by omega)).write (by simp) _ (vector_contains p (by omega))

def ZPrefix (initial current : Mem) (p a : Addr) (done : Nat) : Prop :=
  ∀k<256,coeffAt current p k=if k<done then
    reduceWord (coeffAt initial p k+coeffAt initial a k) else coeffAt initial p k

theorem zRun_prefix (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) {j : Nat} (hj : j≤64) :
    ZPrefix m (zRun m p a B j).mem p a (4*j) := by
  induction j with
  | zero => intro k hk; simp [zRun]
  | succ j ih =>
    have hp := ih (by omega)
    have ha : ∀k<256,coeffAt (zRun m p a B j).mem a k=coeffAt m a k := by
      intro k hk
      exact coeffAt_frame (zRun_frame m p a B (by omega)) (by simpa using hd.symm) hk
    intro k hk
    rw [zRun_next,zStep_coeff _ _ _ _ (by omega) hk]
    by_cases before : k<4*j
    · rw [ite_eq_right (by omega),hp k hk,ite_eq_left before,ite_eq_left (by omega)]
    · by_cases inside : k<4*j+4
      · rw [ite_eq_left (by omega),hp k hk,ite_eq_right before,ha k hk,ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega),hp k hk,ite_eq_right before,ite_eq_right (by omega)]

theorem zRun_coeff (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) {k : Nat} (hk : k<256) :
    coeffAt (zRun m p a B 64).mem p k=reduceWord (coeffAt m p k+coeffAt m a k) := by
  rw [zRun_prefix m p a B hd (by decide) k hk,ite_eq_left hk]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZFlags.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)

def zBad (m : Mem) (p a : Addr) (B j e : Nat) : Bool :=
  decide (B≤normZq (ofInt (((coeffAt m p (4*j+e)).toNat:Int)+(coeffAt m a (4*j+e)).toInt)))

theorem addReduced_mask (a b : BitVec 32) (B : Nat) (ha : a.toNat<8380417)
    (hb : -8380417<b.toInt ∧ b.toInt<2*8380417) (hB : 1≤B) (hB' : B≤524288) :
    normMask (reduceWord (a+b)) (BitVec.ofNat 32 B-1)
      (BitVec.ofNat 32 B+(BitVec.ofNat 32 B-1))=
      maskWord (decide (B≤normZq (ofInt ((a.toNat:Int)+b.toInt)))) := by
  have hlo : BitVec.ofNat 32 B-1=BitVec.ofNat 32 (B-1) := by bv_omega
  have hwidth : BitVec.ofNat 32 B+(BitVec.ofNat 32 B-1)=BitVec.ofNat 32 (2*B-1) := by bv_omega
  have hn := addReduced_norm a b B ha hb hB hB'
  unfold normMask maskWord
  rw [hwidth,hlo,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  by_cases h : B≤normZq (ofInt ((a.toNat:Int)+b.toInt))
  · rw [decide_eq_true h,ite_eq_left (by have := mt hn.mp (show ¬normZq (ofInt ((a.toNat:Int)+b.toInt))<B by omega); omega)]
    rfl
  · rw [decide_eq_false h,ite_eq_right (by have := hn.mpr (by omega); omega)]
    rfl

theorem zWords_current (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) {j e : Nat} (hj : j<64) (he : e<4) :
    zWords (zRun m p a B j).mem p a j e=
      reduceWord (coeffAt m p (4*j+e)+coeffAt m a (4*j+e)) := by
  rw [zWords_coeff _ _ _ _ he,zRun_prefix m p a B hd (by omega) _ (by omega),ite_eq_right (by omega)]
  rw [coeffAt_frame (zRun_frame m p a B (by omega)) (by simpa using hd.symm) (by rw [n_eq]; omega)]

theorem zRun_flags (m : Mem) (p a : Addr) (B : Nat)
    (hd : (pR p).Disjoint (pR a)) (hB : 1≤B) (hB' : B≤524288)
    (ha : ∀k<256,(coeffAt m p k).toNat<8380417)
    (hb : ∀k<256,-8380417<(coeffAt m a k).toInt ∧ (coeffAt m a k).toInt<2*8380417)
    {j : Nat} (hj : j≤64) :
    ∀e<4,vword (zRun m p a (BitVec.ofNat 32 B) j).flags e=maskWord (flagBad (zBad m p a B) j e) := by
  induction j with
  | zero => intro e he; simp [zRun,flagBad,maskWord,vword]
  | succ j ih =>
    intro e he
    rw [zRun_next]
    simp only [zStep,laneVector_word _ he]
    rw [ih (by omega) e he,zWords_current m p a _ hd (by omega) he,
      addReduced_mask _ _ B (ha _ (by omega)) (hb _ (by omega)) hB hB',maskWord_or]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
