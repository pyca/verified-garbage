module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFlags
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
public import VerifiedGarbage.Proof.MlDsa.ResponseZContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation

/-! ### `MlDsa.AArch64.Optimized.ResponseZCallTiming`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResponseZVerified`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResponseZFlags`, which only this module used -/

section

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
  rw [show 64*u+16*i=16*(4*u+i) by omega_using []]

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
    rw [h0,BitVec.add_assoc,← BitVec.ofNat_add,show 64*u+16*i=16*(4*u+i) by omega_using []]
  rw [← List.append_nil (addGroup (16*i))]
  refine addGroup_ok (by omega_using [hi]) ha hb hw hr.q hr.c fun t hk hmem hflag => WP.block_nil_iff.mpr ?_
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
  rw [show 16*j=4*(4*j) by omega_using []]
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
  rw [show 16*j=4*(4*j) by omega_using []]
  change coeffAt (d.mem.write (coeffAddr p (4*j)) 16 _) p k=_
  rw [coeffAt_write16 _ _ (by omega_using [hj]) _ hk]
  split
  · rename_i h
    rw [laneVector_word _ (by omega_using [h]),zWords_coeff _ _ _ _ (by omega_using [h]),show 4*j+(k-4*j)=k by omega_using [h]]
  · rfl

theorem zRun_frame (m : Mem) (p a : Addr) (B : BitVec 32) {j : Nat} (hj : j≤64) :
    Frame [pR p] m (zRun m p a B j).mem := by
  induction j with
  | zero => exact Frame.refl _ _
  | succ j ih =>
    rw [zRun_next]
    simp only [zStep]
    rw [show 16*j=4*(4*j) by omega_using []]
    change Frame [pR p] m ((zRun m p a B j).mem.write (coeffAddr p (4*j)) 16 _)
    exact (ih (by omega_using [hj])).write (by simp) _ (vector_contains p (by omega_using [hj]))

def ZPrefix (initial current : Mem) (p a : Addr) (done : Nat) : Prop :=
  ∀k<256,coeffAt current p k=if k<done then
    reduceWord (coeffAt initial p k+coeffAt initial a k) else coeffAt initial p k

theorem zRun_prefix (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) {j : Nat} (hj : j≤64) :
    ZPrefix m (zRun m p a B j).mem p a (4*j) := by
  induction j with
  | zero => intro k hk; simp [zRun]
  | succ j ih =>
    have hp := ih (by omega_using [hj])
    have ha : ∀k<256,coeffAt (zRun m p a B j).mem a k=coeffAt m a k := by
      intro k hk
      exact coeffAt_frame (zRun_frame m p a B (by omega_using [hj])) (by simpa using hd.symm) hk
    intro k hk
    rw [zRun_next,zStep_coeff _ _ _ _ (by omega_using [hj]) hk]
    by_cases before : k<4*j
    · rw [ite_eq_right (by omega_using [before]),hp k hk,ite_eq_left before,ite_eq_left (by omega_using [before])]
    · by_cases inside : k<4*j+4
      · rw [ite_eq_left (by omega_using [before, inside]),hp k hk,ite_eq_right before,ha k hk,ite_eq_left (by omega_using [inside])]
      · rw [ite_eq_right (by omega_using [inside]),hp k hk,ite_eq_right before,ite_eq_right (by omega_using [inside])]

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
  rw [hwidth,hlo,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [hB'])]
  by_cases h : B≤normZq (ofInt ((a.toNat:Int)+b.toInt))
  · rw [decide_eq_true h,ite_eq_left (by have := mt hn.mp (show ¬normZq (ofInt ((a.toNat:Int)+b.toInt))<B by omega_using [h]); omega_using [hn, h])]
    rfl
  · rw [decide_eq_false h,ite_eq_right (by have := hn.mpr (by omega_using [h]); omega_using [hn, h])]
    rfl

theorem zWords_current (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) {j e : Nat} (hj : j<64) (he : e<4) :
    zWords (zRun m p a B j).mem p a j e=
      reduceWord (coeffAt m p (4*j+e)+coeffAt m a (4*j+e)) := by
  rw [zWords_coeff _ _ _ _ he,zRun_prefix m p a B hd (by omega_using [hj]) _ (by omega_using [hj, he]),ite_eq_right (by omega_using [])]
  rw [coeffAt_frame (zRun_frame m p a B (by omega_using [hj])) (by simpa using hd.symm) (by rw [n_eq]; omega_using [hj, he])]

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
    rw [ih (by omega_using [hj]) e he,zWords_current m p a _ hd (by omega_using [hj]) he,
      addReduced_mask _ _ B (ha _ (by omega_using [hj, he])) (hb _ (by omega_using [hj, he])) hB hB',maskWord_or]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

end


/-! ## From `ResponseZLoop.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg)

def addBody : List Instr := [0,16,32,48].flatMap addGroup

theorem addBody_ok {s : State} {m : Mem} {p a : Addr} {B : BitVec 32} {u : Nat}
    (hr : ZReady B s) (hm : s.mem=(zRun m p a B (4*u)).mem) (hf : s.v .v31=(zRun m p a B (4*u)).flags)
    (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u)) (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u))
    (ha : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hb : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block addBody) s fun t =>
      StepKeep [.v0,.v1,.v2,.v6,.v31] s t ∧ ZReady B t ∧
      t.mem=(zRun m p a B (4*(u+1))).mem ∧ t.v .v31=(zRun m p a B (4*(u+1))).flags := by
  let I := fun i t => StepKeep [.v0,.v1,.v2,.v6,.v31] s t ∧ ZReady B t ∧
    t.mem=(zRun m p a B (4*u+i)).mem ∧ t.v .v31=(zRun m p a B (4*u+i)).flags
  have hinit : I 0 s := ⟨StepKeep.ofChg (VChg.refl _ _) (by decide),hr,hm,hf⟩
  have hstep : ∀i<4,∀t,I i t → WP isa (.block (addGroup (16*i))) t (I (i+1)) := by
    intro i hi t ⟨hk,hready,hmem,hflags⟩
    refine WP.mono (addGroup_step hi hready hmem hflags
      ((hk.keep.get .x0).trans h0) ((hk.keep.get .x1).trans h1) ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv⟩ => ?_
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x0] using ha i hi
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x1] using hb i hi
    · simpa only [hk.keep.wr,hk.keep.get .x0] using hw i hi
    · refine ⟨(hk.trans hv).mono (by decide),hrv,?_,?_⟩
      · change v.mem=(zRun m p a B (4*u+(i+1))).mem
        rw [show 4*u+(i+1)=4*u+i+1 by omega_arith,zRun_next]
        exact hmv
      · change v.v .v31=(zRun m p a B (4*u+(i+1))).flags
        rw [show 4*u+(i+1)=4*u+i+1 by omega_arith,zRun_next]
        exact hfv
  have h := fourGroups_ok addGroup I hinit hstep
  simpa only [I,addBody,show 4*u+4=4*(u+1) by omega_arith] using h

theorem addLoop_ok {s : State} (hr : ZReady ((s.gpr .x2).setWidth 32) s)
    (hc : s.gpr .x10=16) (hf : s.v .v31=0)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa (.loop (.block (addBody++advance [.x0,.x1])) (.nonzero .x .x10)) s fun t =>
      Keep [.x0,.x1,.x10] s t ∧ ZReady ((s.gpr .x2).setWidth 32) t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+1024 ∧
      t.mem=(zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).mem ∧
      t.v .v31=(zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).flags := by
  let B := (s.gpr .x2).setWidth 32
  let I := fun u t => Keep [.x0,.x1,.x10] s t ∧ ZReady B t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (64*u) ∧ t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (64*u) ∧
    t.mem=(zRun s.mem (s.gpr .x0) (s.gpr .x1) B (4*u)).mem ∧
    t.v .v31=(zRun s.mem (s.gpr .x0) (s.gpr .x1) B (4*u)).flags
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 16) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ⟨hk,hready,h0,h1,hm,hf⟩ _
    rw [WP.block_append_iff]
    refine WP.mono (addBody_ok hready hm hf h0 h1 ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv⟩ => ?_
    · intro i hi
      simp only [hk.rd,hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact ha _ (by omega_arith)
    · intro i hi
      simp only [hk.rd,hk.wr,h1,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hb _ (by omega_arith)
    · intro i hi
      simp only [hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hw _ (by omega_arith)
    · refine WP.mono (advance2_ok v) fun w ⟨⟨⟨hw0,hw1,hw10,hwm⟩,hkw⟩,hvw⟩ => ?_
      refine ⟨⟨((hk.trans hv.keep).trans hkw).mono,?_,?_,?_,hwm.trans hmv,?_⟩,?_⟩
      · exact hrv.frame (rs := []) (by simp) (by intro r _; exact congrFun hvw r)
      · rw [hw0,hv.keep.get .x0,h0,show 64*(u+1)=64*u+64 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw1,hv.keep.get .x1,h1,show 64*(u+1)=64*u+64 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hvw,hfv]
      · rw [hw10,hv.keep.get .x10]; rfl
  · exact ⟨Keep.refl _ _,hr,by simp,by simp,rfl,hf⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)

theorem addNorm_eq : VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm=
    .seq (.block addInit) (.seq (.seq (.block [.movz .x .x10 16 0])
      (.loop (.block (addBody++advance [.x0,.x1])) (.nonzero .x .x10)))
      VG.Impl.MlDsa.AArch64.Optimized.Response.finish) := rfl

theorem addNorm_words_ok (s : State)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm s fun t =>
      Keep [.x0,.x1,.x9,.x10] s t ∧
      t.mem=(zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).mem ∧
      t.gpr .x0=finishValue (zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).flags := by
  rw [addNorm_eq]
  apply WP.seq
  refine WP.mono (addInit_ok s) fun a ⟨hsa,hready,hzero⟩ => ?_
  have hka := setup_keep hsa (by decide)
  apply WP.seq
  apply WP.seq
  refine WP.mono (counter_ok a) fun b ⟨⟨⟨hcount,hmem⟩,hkb⟩,hvec⟩ => ?_
  have hksb := hka.trans hkb
  have hrb : ZReady ((b.gpr .x2).setWidth 32) b := by
    rw [hkb.get .x2,hka.get .x2]
    exact hready.frame (rs := []) (by simp) (fun r _=>congrFun hvec r)
  refine WP.mono (addLoop_ok hrb hcount (by rw [hvec,hzero]) ?_ ?_ ?_) fun c ⟨hkc,hrc,h0,h1,hmc,hfc⟩ => ?_
  · simpa only [hkb.rd,hkb.wr,hkb.get .x0,hka.rd,hka.wr,hka.get .x0] using ha
  · simpa only [hkb.rd,hkb.wr,hkb.get .x1,hka.rd,hka.wr,hka.get .x1] using hb
  · simpa only [hkb.wr,hkb.get .x0,hka.wr,hka.get .x0] using hw
  · refine WP.mono (finish_ok c) fun t ⟨⟨⟨hout,hmt⟩,hkt⟩,hvt⟩ => ?_
    refine ⟨((hksb.trans hkc).trans hkt).mono,?_,?_⟩
    · rw [hmt,hmc,hmem,hsa.mem,hkb.get .x0,hka.get .x0,hkb.get .x1,hka.get .x1,hkb.get .x2,hka.get .x2]
    · rw [hout,hfc,hmem,hsa.mem,hkb.get .x0,hka.get .x0,hkb.get .x1,hka.get .x1,hkb.get .x2,hka.get .x2]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem ofInt_nat (v : Nat) : ofInt (v:Int)=ofNat v := by
  apply Fin.ext
  change ((v:Int) % (q:Int)).toNat%q=v%q
  rw [← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]

theorem zSum_coeff (m : Mem) (p a : Addr) {k : Nat} (hk : k<n) :
    (add (polyAt m p) (signedPolyAt m a))[k]! =
      ofInt (((coeffAt m p k).toNat:Int)+(coeffAt m a k).toInt) := by
  rw [add_get _ _ hk,polyAt_get _ _ hk,ofInt_add,ofInt_nat]
  congr 1
  rw [getElem!_eq _ hk]
  simp only [signedPolyAt,Vector.getElem_ofFn]

theorem zRun_centered (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) (ha : Reduced m p) (hb : RawReduced m a) :
    CenteredReduced (zRun m p a B 64).mem p := by
  intro k hk
  rw [zRun_coeff m p a B hd hk,addReduced_int _ _ (ha k hk) (hb k hk)]
  have hak : (coeffAt m p k).toNat<8380417 := ha k hk
  have hbk : -8380417<(coeffAt m a k).toInt ∧ (coeffAt m a k).toInt<16760834 := hb k hk
  have := reduce32_bounds (x := ((coeffAt m p k).toNat:Int)+(coeffAt m a k).toInt)
    (by omega_arith) (by omega_arith)
  change -8380417<_ ∧ _<8380417
  omega_arith

theorem zRun_poly (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) (ha : Reduced m p) (hb : RawReduced m a) :
    signedPolyAt (zRun m p a B 64).mem p=add (polyAt m p) (signedPolyAt m a) := by
  apply ext_getElem!
  intro k hk
  rw [zSum_coeff _ _ _ hk,getElem!_eq _ hk]
  simp only [signedPolyAt,Vector.getElem_ofFn]
  rw [zRun_coeff m p a B hd hk,addReduced_int _ _ (ha k hk) (hb k hk)]
  unfold ofInt
  congr 1
  exact congrArg Int.toNat (reduce32_mod _)

theorem zRun_finish (m : Mem) (p a : Addr) (B : Nat)
    (hd : (pR p).Disjoint (pR a)) (ha : Reduced m p) (hb : RawReduced m a)
    (hB : 1≤B) (hB' : B≤524288) :
    finishValue (zRun m p a (BitVec.ofNat 32 B) 64).flags=
      if normRq [add (polyAt m p) (signedPolyAt m a)]<B then 1 else 0 := by
  have hf := zRun_flags m p a B hd hB hB' ha hb (by decide : 64≤64)
  have he := finishValue_flags hf
  have hr := finishValue_flags_range hf
  have hn : (∀i<64,∀e<4,zBad m p a B i e=false) ↔ normRq [add (polyAt m p) (signedPolyAt m a)]<B := by
    rw [VG.Proof.MlDsa.Round.normRq_lt]
    constructor
    · intro h k hk
      have hg := h (k/4) (by change k<256 at hk; omega_arith) (k%4) (by omega_arith)
      simp only [zBad,decide_eq_false_iff_not,Nat.not_le] at hg
      rw [show 4*(k/4)+k%4=k by omega_arith] at hg
      rw [zSum_coeff _ _ _ hk]
      exact hg
    · intro h i hi e he
      simp only [zBad,decide_eq_false_iff_not,Nat.not_le]
      have hk : 4*i+e<n := by rw [n_eq]; omega_arith
      rw [← zSum_coeff _ _ _ hk]
      exact h _ hk
  rw [hn] at he
  split
  · exact he.mpr ‹_›
  · rcases hr with hr|hr
    · exact hr
    · exact False.elim (‹¬_› (he.mp hr))

theorem addNorm_ok (s : State)
    (hd : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)))
    (hay : Reduced s.mem (s.gpr .x0)) (hbs : RawReduced s.mem (s.gpr .x1))
    (hB : 1≤((s.gpr .x2).setWidth 32).toNat) (hB' : ((s.gpr .x2).setWidth 32).toNat≤524288)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm s fun t =>
      VG.Proof.MlKem.AArch64.Keep [.x0,.x1,.x9,.x10] s t ∧
      CenteredReduced t.mem (s.gpr .x0) ∧
      signedPolyAt t.mem (s.gpr .x0)=add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1)) ∧
      t.gpr .x0=if normRq [add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1))]<
        ((s.gpr .x2).setWidth 32).toNat then 1 else 0 := by
  refine WP.mono (addNorm_words_ok s ha hb hw) fun t ⟨hk,hm,hret⟩ => ?_
  refine ⟨hk,?_,?_,?_⟩
  · rw [hm]; exact zRun_centered _ _ _ _ hd hay hbs
  · rw [hm]; exact zRun_poly _ _ _ _ hd hay hbs
  · rw [hret]
    have h := zRun_finish s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32).toNat hd hay hbs hB hB'
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using h

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)

def addNormK : Contract isa where
  pre s := s.wr=[polyRegion (s.gpr .x0)] ∧ s.rd=[polyRegion (s.gpr .x1)] ∧
    (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x1)) ∧
    Reduced s.mem (s.gpr .x0) ∧ RawReduced s.mem (s.gpr .x1) ∧
    1≤((s.gpr .x2).setWidth 32).toNat ∧ ((s.gpr .x2).setWidth 32).toNat≤524288
  post s t := CenteredReduced t.mem (s.gpr .x0) ∧
    signedPolyAt t.mem (s.gpr .x0)=add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1)) ∧
    (t.gpr .x0).setWidth 32=if normRq [add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1))]<
      ((s.gpr .x2).setWidth 32).toNat then 1 else 0
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.sp=t.sp

theorem addNorm_correct (s : State) (hp : addNormK.pre s) :
    ∃trace t,Exec isa VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm s trace t ∧
      abiPreserved s t ∧ addNormK.post s t := by
  obtain ⟨hw,hr,hd,ha,hb,hB,hB'⟩ := hp
  have hwrite : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    rw [hw]
    exact ⟨polyRegion (s.gpr .x0),List.mem_singleton_self _,Offset.contains_base _ ho (by omega_arith)⟩
  have hread : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    obtain ⟨r,hr,hc⟩ := hwrite off ho
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  have hinput : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
    intro off ho
    rw [hr]
    exact ⟨polyRegion (s.gpr .x1),by simp,Offset.contains_base _ ho (by omega_arith)⟩
  obtain ⟨tr,t,he,hk,hcenter,hpoly,hret⟩ := addNorm_ok s hd ha hb hB hB' hread hinput hwrite
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hcenter,hpoly,?_⟩
  · intro r hr
    apply hk.gpr r
    simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hret]
    split <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa

theorem addNorm_contract_ct : ConstantTime isa addNormK.pre addNormK.pub
    VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply addNorm_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.2 ?_,by simp⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hp.1
  · exact hp.2.1

def addNormSat : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 1 else 0
  sp := 65536
  mem _ := 0
  rd := [⟨8192,1024⟩]
  wr := [⟨4096,1024⟩]

theorem addNorm_verified : Verified target VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
    (addNormContract abi) := by
  refine Verified.of_correct addNorm_correct addNorm_contract_ct ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · intro s h
    sig_pre [addNormContract,addNormSig,abi,argRegs] at h
    sig_split h
    exact ⟨by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,h⟩
  · sig_implies_post [addNormContract,addNormSig,addNormK,abi,argRegs]
  · sig_implies_pub [addNormContract,addNormSig,addNormK,abi,argRegs]
  · refine ⟨addNormSat,?_⟩
    sig_pre [addNormContract,addNormSig,abi,argRegs]
    sig_and_intros
    all_goals first
      | rfl
      | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
      | exact Region.disjoint_of_sep (by decide)
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

end


/-! ## From `ResponseZCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem addNorm_callee (S : Nat) : CalleeOk S VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
    (addNormContract abi) := ⟨addNorm_verified.1,addNorm_verified.2.1,Nat.zero_le _⟩

abbrev addNormArgs (y cs : Ptr) (B : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr y),(.x1,.ptr cs),(.x2,.imm B)]

structure AddNormReady (y cs : Ptr) (B : Nat) (s : State) : Prop where
  yFit : (pa s y).toNat+1024≤2^64
  csFit : (pa s cs).toNat+1024≤2^64
  apart : (polyRegion (pa s y)).Disjoint (polyRegion (pa s cs))
  canonical : Reduced s.mem (pa s y)
  raw : RawReduced s.mem (pa s cs)
  boundPos : 1≤B
  boundMax : B≤524288
  readable : Covers [polyRegion (pa s cs),polyRegion (pa s y)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s y)] s.wr

theorem addNormAt_pre {s s1 : State} {y cs : Ptr} {B : Nat}
    (h : AddNormReady y cs B s) (h1 : Args (addNormArgs y cs B) s s1) :
    (addNormContract abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s cs)] [polyRegion (pa s y)]) := by
  sig_pre [addNormContract,addNormSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1,Arg.val]
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega_arith
  rw [hB]
  exact ⟨trivial,trivial,h.apart,h.yFit,h.csFit,h.canonical,h.raw,h.boundPos,h.boundMax⟩

theorem addNormArgs_ok {y cs : Ptr} {B : Nat}
    (hy : (Arg.ptr y).Ok) (hc : (Arg.ptr cs).Ok) :
    ∀x∈addNormArgs y cs B,x.2.Ok ∧ x.1∈argRegs := by
  simp only [addNormArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl|rfl|rfl
  · exact ⟨hy,by simp⟩
  · exact ⟨hc,by simp⟩
  · exact ⟨trivial,by simp⟩

theorem addNormAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {y cs : Ptr} {B : Nat}
    (hy : (Arg.ptr y).Ok) (hc : (Arg.ptr cs).Ok) (h : AddNormReady y cs B s) :
    WP isa (callAt nm VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm (addNormArgs y cs B)) s fun t =>
      Post S s t [polyRegion (pa s y)] ∧ CenteredReduced t.mem (pa s y) ∧
      signedPolyAt t.mem (pa s y)=add (polyAt s.mem (pa s y)) (signedPolyAt s.mem (pa s cs)) ∧
      (t.gpr .x0).setWidth 32=if normRq [add (polyAt s.mem (pa s y)) (signedPolyAt s.mem (pa s cs))]<B then 1 else 0 := by
  refine WP.mono (callAtSyms_ok hS (addNorm_callee S) (addNormArgs_ok hy hc) (by simp)
    (fun s1 h1 _=>addNormAt_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ?_
  sig_post [addNormContract,addNormSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega_arith
  simpa only [Arg.val,hB] using And.intro hP hq

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem addNormAt_tr {S : Nat} {nm : String} {y cs : Ptr} {B : Nat}
    (hy : (Arg.ptr y).Ok) (hc : (Arg.ptr cs).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x z,Q x z → AddNormReady y cs B x ∧ AddNormReady y cs B z ∧
      pa x y=pa z y ∧ pa x cs=pa z cs ∧ x.sp=z.sp) :
    RelCT isa Q (callAt nm VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
      (addNormArgs y cs B)) fun _ _=>True := by
  refine callAtSyms_tr (addNorm_callee S) (addNormArgs_ok hy hc) (by simp)
    fun x z x1 z1 hp h1 h2 _ _ => ?_
  obtain ⟨rx,rz,ey,ec,esp⟩ := hQ x z hp
  refine ⟨[polyRegion (pa x cs)],[polyRegion (pa x y)],addNormAt_pre rx h1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ey,ec]; exact addNormAt_pre rz h2
  · sig_pub [addNormContract,addNormSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,ey,ec,rfl⟩
  · rw [ey,ec]; exact rz.readable
  · rw [ey]; exact rz.writable

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- The response remains signed through all strict rejection checks. -/
theorem centered_signed {m : Mem} {p : Addr} {f : Poly}
    (hb : CenteredReduced m p) (hv : signedPolyAt m p=f) :
    SignedPolyIs m p f (-(q:Int)+1) ((q:Int)-1) := by
  refine ⟨?_,?_⟩
  · intro i hi
    have := hb i hi
    omega_using [this]
  · intro i hi
    rw [← hv,VG.Proof.MlDsa.Arith.getElem!_eq _ hi]
    simp only [signedPolyAt,Vector.getElem_ofFn]

theorem addNormReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {y cs : Ptr} {B : Nat}
    (hy : inB (rbs++wbs) y 1024=true) (hc : inB (rbs++wbs) cs 1024=true)
    (hwy : inB wbs y 1024=true) (hd : sepB rbs wbs y 1024 cs 1024=true)
    (ha : Reduced s.mem (pa s y)) (hb : RawReduced s.mem (pa s cs))
    (hB : 1≤B) (hB' : B≤524288) : Response.AddNormReady y cs B s := by
  exact ⟨L.nwp hy,L.nwp hc,L.disj hd,ha,hb,hB,hB',Covers.cons (L.cR hc) (L.cR hy),L.cW hwy⟩

theorem addNormAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {y cs : Ptr} {B : Nat}
    (hy : inB (rbs++wbs) y 1024=true) (hc : inB (rbs++wbs) cs 1024=true)
    (h : Response.AddNormReady y cs B s) :
    WP isa (callAt "vg_mldsa_signed_add_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
      (Response.addNormArgs y cs B)) s fun t =>
      PPostB S s t [(y,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      SignedPolyIs t.mem (pa s y) (add (polyAt s.mem (pa s y)) (signedPolyAt s.mem (pa s cs)))
        (-(q:Int)+1) ((q:Int)-1) ∧
      (t.gpr .x0).setWidth 32=if normRq [add (polyAt s.mem (pa s y)) (signedPolyAt s.mem (pa s cs))]<B then 1 else 0 := by
  refine WP.mono (Response.addNormAt_ok L.s64 (ptr_ok (L.ptrBs hy)) (ptr_ok (L.ptrBs hc)) h)
    fun t ⟨hp,hcenter,hpoly,hret⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),centered_signed hcenter hpoly,hret⟩

theorem addNormAt_field_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {y cs : Ptr} {B : Nat} {f g : Poly}
    (hy : inB (rbs++wbs) y 1024=true) (hc : inB (rbs++wbs) cs 1024=true)
    (h : Response.AddNormReady y cs B s) (hf : PolyIs s.mem (pa s y) f) (hg : RawPolyIs s.mem (pa s cs) g) :
    WP isa (callAt "vg_mldsa_signed_add_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
      (Response.addNormArgs y cs B)) s fun t =>
      PPostB S s t [(y,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      SignedPolyIs t.mem (pa s y) (add f g) (-(q:Int)+1) ((q:Int)-1) ∧
      (t.gpr .x0).setWidth 32=if normRq [add f g]<B then 1 else 0 := by
  refine WP.mono (addNormAt_layout L hy hc h) fun t ⟨hp,h24,hv,hr⟩ => ?_
  exact ⟨hp,h24,by simpa only [hf.2,hg.2] using hv,by simpa only [hf.2,hg.2] using hr⟩

end VG.Proof.MlDsa.AArch64.Sign
