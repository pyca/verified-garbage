module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.ResponseZContract
meta import VerifiedGarbage.Proof.MlDsa.ResponseZContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoad
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec

/-! ### `MlDsa.AArch64.Optimized.ResponseLowVerified`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResponseLowCore`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResponseLowReady`, which only this module used -/

section

/-! ## From `ResponseLowGroup.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq wp_strq wp_vop)
open VG.Proof.MlDsa.AArch64.Round (IsG)

def subInput (s : State) (off e : Nat) : BitVec 32 :=
  Inverse.signCorrected (reduceWord (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e-
    vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 off) 16) e))
def subHead (g off : Nat) : List Instr :=
  [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,.vop (.sub .s4 .v0 .v0 .v1)] ++
    Impl.MlDsa.AArch64.Optimized.Response.reduce .v0 ++
    Impl.MlDsa.AArch64.Optimized.Response.cadd .v0 ++
    Impl.MlDsa.AArch64.Optimized.HighPack.hb g .v1 .v0

theorem subHead_ok {g : Nat} (hg : IsG g) {s : State} {off : Nat}
    (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v25) e=4194304#32) (hh : HighPack.HighConstants g s)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v0,.v1,.v6,.v7] s t →
      (∀e<4,vword (t.v .v0) e=subInput s off e) →
      (∀e<4,vword (t.v .v1) e=HighPack.highWord g (subInput s off e)) →
      WP isa (.block rest) t Q) : WP isa (.block (subHead g off++rest)) s Q := by
  unfold subHead
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl ha fun a h1 => ?_
  refine wp_ldrq ho rfl (by simpa only [h1.chg.rd,h1.chg.wr,h1.chg.gpr] using hb) fun b h2 => ?_
  refine wp_vop (d:=.v0) rfl fun c h3 => ?_
  have hk : VChg [.v0,.v1] s c := ((h1.chg.trans h2.chg).trans h3.chg).mono (by decide)
  refine reduce_ok (by decide : VReg.v0≠.v6)
    (by intro e he; rw [hk.get .v16 (by decide)]; exact hq e he)
    (by intro e he; rw [hk.get .v25 (by decide)]; exact hc e he) fun d hd hv => ?_
  have hd' : VChg [.v0,.v1,.v6] s d := (hk.trans hd).mono (by decide)
  refine cadd_ok (by decide : VReg.v0≠.v7)
    (by intro e he; rw [hd'.get .v16 (by decide)]; exact hq e he) fun u hu huv => ?_
  have hu' : VChg [.v0,.v1,.v6,.v7] s u := (hd'.trans hu).mono (by decide)
  have hval : ∀e<4,vword (u.v .v0) e=subInput s off e := by
    intro e he
    rw [huv e he,hv e he,h3.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get .v0,h1.v,h2.v,h1.chg.mem,h1.chg.gpr]
    rfl
  have cu := hh.chg hu' (by decide) (by decide) (by decide) (by decide)
  refine HighPack.hb_ok hg (by decide : VReg.v1≠.v7) (by decide) (by decide) (by decide)
    cu.add cu.mul cu.round cu.modulus fun t ht hw => ?_
  exact k t ((hu'.trans ht).mono (by decide))
    (fun e he => by rw [ht.get .v0 (by decide)]; exact hval e he)
    (fun e he => by rw [hw e he,hval e he])

def subGroup (g off : Nat) : List Instr := subHead g off ++ [.strq .v1 .x0 off] ++
  lowCorrection ++ [.strq .v0 .x2 off] ++ Impl.MlDsa.AArch64.Optimized.Response.testNorm

def subLow (g : Nat) (s : State) (off e : Nat) : BitVec 32 :=
  lowWord (subInput s off e) (HighPack.highWord g (subInput s off e)) (vword (s.v .v21) e)

theorem subGroup_ok {g : Nat} (hg : IsG g) {s : State} {off : Nat}
    (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v25) e=4194304#32)
    (hh : ∀e<4,vword (s.v .v26) e=4190208#32) (hr : HighPack.HighConstants g s)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepKeep [.v0,.v1,.v2,.v6,.v7,.v31] s t →
      t.mem=(s.mem.write (s.gpr .x0+BitVec.ofNat 64 off) 16
        (laneVector (fun e => HighPack.highWord g (subInput s off e)))).write
          (s.gpr .x2+BitVec.ofNat 64 off) 16 (laneVector (subLow g s off)) →
      (∀e<4,vword (t.v .v31) e=vword (s.v .v31) e |||
        normMask (subLow g s off e) (vword (s.v .v27) e) (vword (s.v .v24) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (subGroup g off++rest)) s Q := by
  unfold subGroup
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine subHead_ok hg ho ha hb hq hc hr fun a ha h0 h1 => ?_
  refine wp_strq ho rfl (by simpa only [ha.wr,ha.gpr] using hw) fun b hb => ?_
  refine lowCorrection_ok
    (by intro e he; rw [hb.v,ha.get .v16 (by decide)]; exact hq e he)
    (by intro e he; rw [hb.v,ha.get .v26 (by decide)]; exact hh e he) fun c hc hv => ?_
  have hk : StepKeep [.v0,.v1,.v6,.v7] s c :=
    (((StepKeep.ofChg ha (by decide)).trans (StepKeep.ofMem hb)).trans
      (StepKeep.ofChg hc (by decide))).mono (by decide)
  have vl : c.v .v0=laneVector (subLow g s off) := by
    apply vec_ext; intro e he
    rw [laneVector_word _ he,hv e he,hb.v,h0 e he,h1 e he,ha.get .v21 (by decide)]
    rfl
  have vh : a.v .v1=laneVector (fun e => HighPack.highWord g (subInput s off e)) := by
    apply vec_ext; intro e he; rw [laneVector_word _ he,h1 e he]
  refine wp_strq ho rfl (by simpa only [hk.keep.wr,hk.keep.get .x2] using hl) fun d hd => ?_
  refine norm_ok fun t ht hn => ?_
  refine k t ?_ ?_ ?_
  · exact ((hk.trans (StepKeep.ofMem hd)).trans (StepKeep.ofChg ht (by decide))).mono (by decide)
  · rw [ht.mem,hd.mem,hk.keep.get .x2,vl,hc.mem,hb.mem,ha.mem,ha.gpr,vh]
  · intro e he
    rw [hn e he,hd.v,vl,laneVector_word _ he,hk.vec .v31 (by decide),hk.vec .v27 (by decide),hk.vec .v24 (by decide)]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowReady.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

structure LowReady (g B : Nat) (s : State) : Prop extends HighPack.HighConstants g s where
  q : ∀e<4,vword (s.v .v16) e=8380417#32
  round32 : ∀e<4,vword (s.v .v25) e=4194304#32
  halfQ : ∀e<4,vword (s.v .v26) e=4190208#32
  twiceG : ∀e<4,vword (s.v .v21) e=BitVec.ofNat 32 (2*g)
  normLo : ∀e<4,vword (s.v .v27) e=BitVec.ofNat 32 (B-1)
  normWidth : ∀e<4,vword (s.v .v24) e=BitVec.ofNat 32 (2*B-1)

theorem LowReady.frame {g B : Nat} {s t : State} {rs : List VReg} (h : LowReady g B s)
    (hv : ∀r,r∉rs → t.v r=s.v r)
    (hc : ∀r∈[VReg.v16,.v17,.v18,.v19,.v20,.v21,.v24,.v25,.v26,.v27],r∉rs) : LowReady g B t := by
  constructor
  · constructor
    · rw [hv .v17 (hc _ (by decide))]; exact h.add
    · rw [hv .v18 (hc _ (by decide))]; exact h.mul
    · rw [hv .v19 (hc _ (by decide))]; exact h.round
    · rw [hv .v20 (hc _ (by decide))]; exact h.modulus
  · rw [hv .v16 (hc _ (by decide))]; exact h.q
  · rw [hv .v25 (hc _ (by decide))]; exact h.round32
  · rw [hv .v26 (hc _ (by decide))]; exact h.halfQ
  · rw [hv .v21 (hc _ (by decide))]; exact h.twiceG
  · rw [hv .v27 (hc _ (by decide))]; exact h.normLo
  · rw [hv .v24 (hc _ (by decide))]; exact h.normWidth

theorem LowReady.group {g B : Nat} {s t : State} (h : LowReady g B s)
    (hk : StepKeep [.v0,.v1,.v2,.v6,.v7,.v31] s t) : LowReady g B t := h.frame hk.vec (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

end

/-! ### `MlDsa.AArch64.Optimized.ResponseLowSemantic`, which only this module used -/

section

/-! ## From `ResponseLowStore.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/ResponseLowMemory.lean`, which only this module imported.
section

@[expose] public section

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
  rw [show 64*u+16*i=16*(4*u+i) by omega_using []]

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
    rw [h,BitVec.add_assoc,← BitVec.ofNat_add,show 64*u+16*i=16*(4*u+i) by omega_using []]
  rw [← List.append_nil (subGroup g (16*i))]
  refine subGroup_ok hg (by omega_using [hi]) ha hb hw hl hr.q hr.round32 hr.halfQ hr.toHighConstants
    fun t hk hmem hflag => WP.block_nil_iff.mpr ?_
  refine ⟨hk,hr.group hk,?_,?_⟩
  · simpa only [lowStep,hm,addr _ _ h0,addr _ _ h2,hinput,houtv] using hmem
  · apply vec_ext
    intro e he
    rw [hflag e he,hr.normLo e he,hr.normWidth e he,hf,hout e he]
    dsimp only [lowStep]
    rw [laneVector_word _ he]

end VG.Proof.MlDsa.AArch64.Optimized.Response
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlDsa (coeffAt)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

theorem lowStep_frame (g B : Nat) (p a l : Addr) {j : Nat} (hj : j<64) (d : LowData) :
    Frame [polyRegion p,polyRegion l] d.mem (lowStep g B p a l j d).mem := by
  have hp : (polyRegion p).Contains (p+BitVec.ofNat 64 (16*j)) 16 :=
    Offset.contains_base p (by omega_using [hj]) (by omega_using [hj])
  have hl : (polyRegion l).Contains (l+BitVec.ofNat 64 (16*j)) 16 :=
    Offset.contains_base l (by omega_using [hj]) (by omega_using [hj])
  exact ((Frame.refl _ _).write (by simp) _ hp).write (by simp) _ hl

theorem coeffAt_write16_other {m : Mem} {p l : Addr} {j i : Nat} (hj : j<64) (hi : i<256)
    (hd : (polyRegion p).Disjoint (polyRegion l)) (v : BitVec 128) :
    coeffAt (m.write (l+BitVec.ofNat 64 (16*j)) 16 v) p i=coeffAt m p i := by
  have hl : (polyRegion l).Contains (l+BitVec.ofNat 64 (16*j)) 16 :=
    Offset.contains_base l (by omega_using [hj]) (by omega_using [hj])
  have hf : Frame [polyRegion l] m (m.write (l+BitVec.ofNat 64 (16*j)) 16 v) :=
    (Frame.refl _ _).write (by simp) _ hl
  exact coeffAt_frame hf (by intro r hr; simpa using (List.mem_singleton.mp hr ▸ hd)) hi

theorem lowStep_high {g B : Nat} {p a l : Addr} {j i : Nat} (hj : j<64) (hi : i<256)
    (hd : (polyRegion p).Disjoint (polyRegion l)) (d : LowData) :
    coeffAt (lowStep g B p a l j d).mem p i=
      if 4*j≤i ∧ i<4*j+4 then HighPack.highWord g (lowInput d.mem p a j (i-4*j))
      else coeffAt d.mem p i := by
  dsimp only [lowStep]
  rw [coeffAt_write16_other hj hi hd]
  have ha : p+BitVec.ofNat 64 (16*j)=coeffAddr p (4*j) := by congr 2; omega_using []
  rw [ha,coeffAt_write16 _ _ (by omega_using [hj]) _ hi]
  split
  · rename_i h; rw [laneVector_word _ (by omega_using [h])]
  · rfl

theorem lowStep_low {g B : Nat} {p a l : Addr} {j i : Nat} (hj : j<64) (hi : i<256)
    (hd : (polyRegion p).Disjoint (polyRegion l)) (d : LowData) :
    coeffAt (lowStep g B p a l j d).mem l i=
      if 4*j≤i ∧ i<4*j+4 then lowOutput g d.mem p a j (i-4*j)
      else coeffAt d.mem l i := by
  dsimp only [lowStep]
  have ha : l+BitVec.ofNat 64 (16*j)=coeffAddr l (4*j) := by congr 2; omega_using []
  rw [ha,coeffAt_write16 _ _ (by omega_using [hj]) _ hi]
  split
  · rename_i h; rw [laneVector_word _ (by omega_using [h])]
  · exact coeffAt_write16_other hj hi hd.symm _

theorem lowRun_frame (m : Mem) (g B : Nat) (p a l : Addr) {j : Nat} (hj : j≤64) :
    Frame [polyRegion p,polyRegion l] m (lowRun m g B p a l j).mem := by
  induction j with
  | zero => exact Frame.refl _ _
  | succ j ih => exact (ih (by omega_using [hj])).trans (lowStep_frame g B p a l (by omega_using [hj]) _)

theorem lowRun_input {m : Mem} {g B : Nat} {p a l : Addr} {j i : Nat} (hj : j≤64) (hi : i<256)
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l)) :
    coeffAt (lowRun m g B p a l j).mem a i=coeffAt m a i := by
  apply coeffAt_frame (lowRun_frame m g B p a l hj) _ hi
  intro r hr
  rcases (show r=polyRegion p ∨ r=polyRegion l by simpa using hr) with rfl|rfl
  · exact hap
  · exact hal

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlDsa (coeffAt)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

def lowCanonical (m : Mem) (p a : Addr) (i : Nat) : BitVec 32 :=
  Inverse.signCorrected (reduceWord (coeffAt m p i-coeffAt m a i))
def lowHigh (m : Mem) (g : Nat) (p a : Addr) (i : Nat) : BitVec 32 :=
  HighPack.highWord g (lowCanonical m p a i)
def lowSigned (m : Mem) (g : Nat) (p a : Addr) (i : Nat) : BitVec 32 :=
  lowWord (lowCanonical m p a i) (lowHigh m g p a i) (BitVec.ofNat 32 (2*g))

theorem lowInput_coeff (m : Mem) (p a : Addr) (j : Nat) {e : Nat} (he : e<4) :
    lowInput m p a j e=lowCanonical m p a (4*j+e) := by
  unfold lowInput lowCanonical
  rw [show 16*j=4*(4*j) by omega_using []]
  change Inverse.signCorrected (reduceWord (vword (m.read (coeffAddr p (4*j)) 16) e-
    vword (m.read (coeffAddr a (4*j)) 16) e))=_
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,coeffAddr_add]
  rfl

theorem lowOutput_coeff (m : Mem) (g : Nat) (p a : Addr) (j : Nat) {e : Nat} (he : e<4) :
    lowOutput g m p a j e=lowSigned m g p a (4*j+e) := by
  simp only [lowOutput,lowInput_coeff _ _ _ _ he,lowSigned,lowHigh]

def LowPrefix (initial current : Mem) (g : Nat) (p a l : Addr) (done : Nat) : Prop :=
  (∀i<256,coeffAt current p i=if i<done then lowHigh initial g p a i else coeffAt initial p i) ∧
  (∀i<256,coeffAt current l i=if i<done then lowSigned initial g p a i else coeffAt initial l i)

theorem lowRun_prefix (m : Mem) (g B : Nat) (p a l : Addr)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    {j : Nat} (hj : j≤64) : LowPrefix m (lowRun m g B p a l j).mem g p a l (4*j) := by
  induction j with
  | zero => constructor <;> intro i hi <;> simp [lowRun]
  | succ j ih =>
    have hp := ih (by omega_using [hj])
    have ha := fun (i : Nat) (hi : i<256) => lowRun_input (m:=m) (g:=g) (B:=B) (j:=j) (i:=i) (by omega_using [hj]) hi hap hal
    have hh (i : Nat) (hi : i<256) (hn : ¬i<4*j) :
        lowCanonical (lowRun m g B p a l j).mem p a i=lowCanonical m p a i := by
      simp only [lowCanonical,hp.1 i hi,ite_eq_right hn,ha i hi]
    constructor
    · intro i hi
      rw [lowRun,lowStep_high (by omega_using [hj]) hi hpl]
      by_cases before : i<4*j
      · rw [ite_eq_right (by omega_using [before]),hp.1 i hi,ite_eq_left before,ite_eq_left (by omega_using [before])]
      · by_cases inside : i<4*j+4
        · rw [ite_eq_left (by omega_using [before, inside]),lowInput_coeff _ _ _ _ (by omega_using [inside]),
            show 4*j+(i-4*j)=i by omega_using [before],hh i hi before,ite_eq_left (by omega_using [inside])]
          rfl
        · rw [ite_eq_right (by omega_using [inside]),hp.1 i hi,ite_eq_right before,ite_eq_right (by omega_using [inside])]
    · intro i hi
      rw [lowRun,lowStep_low (by omega_using [hj]) hi hpl]
      by_cases before : i<4*j
      · rw [ite_eq_right (by omega_using [before]),hp.2 i hi,ite_eq_left before,ite_eq_left (by omega_using [before])]
      · by_cases inside : i<4*j+4
        · rw [ite_eq_left (by omega_using [before, inside]),lowOutput_coeff _ _ _ _ _ (by omega_using [inside]),
            show 4*j+(i-4*j)=i by omega_using [before],ite_eq_left (by omega_using [inside])]
          simp only [lowSigned,lowHigh,hh i hi before]
        · rw [ite_eq_right (by omega_using [inside]),hp.2 i hi,ite_eq_right before,ite_eq_right (by omega_using [inside])]

theorem lowRun_coeff (m : Mem) (g B : Nat) (p a l : Addr)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    {i : Nat} (hi : i<256) :
    coeffAt (lowRun m g B p a l 64).mem p i=lowHigh m g p a i ∧
    coeffAt (lowRun m g B p a l 64).mem l i=lowSigned m g p a i := by
  have h := lowRun_prefix m g B p a l hpl hap hal (by decide : 64≤64)
  exact ⟨by rw [h.1 i hi,ite_eq_left hi],by rw [h.2 i hi,ite_eq_left hi]⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

end

/-! ### `MlDsa.AArch64.Optimized.ResponseLowInit`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)

def lowInit (g : Nat) : List Instr :=
  VG.Impl.MlDsa.AArch64.Optimized.HighPack.constants g ++
  VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v25 4194304 ++
  VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v26 4190208 ++
  [.vop (.dup .s4 .v24 .x4),.vop (.movi0 .v31)] ++
  VG.Impl.MlDsa.AArch64.Optimized.Response.normConstants

theorem lowInit_ok {g B : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (hB : 1≤B) {s : State} (hb : (s.gpr .x4).setWidth 32=BitVec.ofNat 32 B) :
    WP isa (.block (lowInit g)) s fun t =>
      SetupKeep [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v25,.v26,.v24,.v31,.v27] s t ∧
      LowReady g B t ∧ t.v .v31=0 := by
  unfold lowInit
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.constants_ok s g) fun a ⟨hka,h16,h17,h18,h19,h20,h21,_,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok a .v25 4194304) fun b hb25 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok b .v26 4190208) fun c hc26 => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v24) rfl fun d hd => wp_vop (d := .v31) rfl fun e he => ?_
  refine WP.mono (normConstants_ok e) fun t ⟨ht,hlo,hw⟩ => ?_
  have hat : SetupKeep [.v25,.v26,.v24,.v31,.v27] a t := setup_mono
    ((((SetupKeep.ofConst hb25.1).trans (SetupKeep.ofConst hc26.1)).trans
      (setup_ofChg (hd.chg.trans he.chg))).trans ht) (by decide)
  have hbound : ∀i<4,vword (e.v .v24) i=BitVec.ofNat 32 B := by
    intro i hi
    rw [he.other .v24 (by decide),hd.v,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ hi,
      hc26.1.gpr .x4 (by decide),hb25.1.gpr .x4 (by decide),hka.gpr .x4 (by decide)]
    rcases (show i=0∨i=1∨i=2∨i=3 by omega_using [hi]) with rfl|rfl|rfl|rfl <;> exact hb
  have hsub : BitVec.ofNat 32 B-(1 : BitVec 32)=BitVec.ofNat 32 (B-1) := by
    bv_omega_arith
  refine ⟨setup_mono (hka.trans hat) (by decide),?_,?_⟩
  · constructor
    · constructor
      · intro i hi; rw [hat.vec .v17 (by decide),h17,HighPack.repeatedWord_lane _ hi]
      · intro i hi; rw [hat.vec .v18 (by decide),h18,HighPack.repeatedWord_lane _ hi]
        rcases hg with rfl|rfl <;> rfl
      · intro i hi; rw [hat.vec .v19 (by decide),h19,HighPack.repeatedWord_lane _ hi]
        rcases hg with rfl|rfl <;> rfl
      · intro i hi; rw [hat.vec .v20 (by decide),h20,HighPack.repeatedWord_lane _ hi]
    · intro i hi; rw [hat.vec .v16 (by decide),h16,HighPack.repeatedWord_lane _ hi]
    · intro i hi
      rw [ht.vec .v25 (by decide),he.other .v25 (by decide),hd.other .v25 (by decide),
        hc26.1.vec .v25 (by decide),hb25.2,HighPack.repeatedWord_lane _ hi]
    · intro i hi
      rw [ht.vec .v26 (by decide),he.other .v26 (by decide),hd.other .v26 (by decide),
        hc26.2,HighPack.repeatedWord_lane _ hi]
    · intro i hi; rw [hat.vec .v21 (by decide),h21,HighPack.repeatedWord_lane _ hi]
    · intro i hi; rw [hlo i hi,hbound i hi,hsub]
    · intro i hi
      rw [hw i hi,hbound i hi,hsub,← BitVec.ofNat_add]
      congr 1; omega_using []
  · rw [ht.vec .v31 (by decide),he.v]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end


/-! ## From `ResponseLowFlags.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def lowBad (m : Mem) (g : Nat) (p a : Addr) (B j e : Nat) : Bool :=
  decide (B≤normZq (ofInt (lowBits g (ofInt
    (((coeffAt m p (4*j+e)).toNat:Int)-(coeffAt m a (4*j+e)).toInt)))))

theorem lowOutput_current (m : Mem) (g B : Nat) (p a l : Addr)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    {j e : Nat} (hj : j<64) (he : e<4) :
    lowOutput g (lowRun m g B p a l j).mem p a j e=lowSigned m g p a (4*j+e) := by
  rw [lowOutput_coeff _ _ _ _ _ he]
  simp only [lowSigned,lowHigh,lowCanonical]
  rw [(lowRun_prefix m g B p a l hpl hap hal (by omega_arith)).1 _ (by omega_arith),ite_eq_right (by omega_arith),
    lowRun_input (by omega_arith) (by omega_arith) hap hal]

theorem lowSigned_mask {g B : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (m : Mem) (p a : Addr) (i : Nat) (ha : (coeffAt m p i).toNat<8380417)
    (hb : -8380417<(coeffAt m a i).toInt ∧ (coeffAt m a i).toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    normMask (lowSigned m g p a i) (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      maskWord (decide (B≤normZq (ofInt (lowBits g (ofInt (((coeffAt m p i).toNat:Int)-(coeffAt m a i).toInt)))))) := by
  rw [lowSigned,lowHigh,lowCanonical,subLow_norm hg ha hb.1 hb.2 hB hB']
  unfold maskWord
  split <;> rename_i h
  · rw [decide_eq_false (by omega_arith)]; rfl
  · rw [decide_eq_true (by omega_arith)]; rfl

theorem lowRun_flags (m : Mem) (g B : Nat) (p a l : Addr)
    (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    (hB : 1≤B) (hB' : B≤524288)
    (ha : ∀i<256,(coeffAt m p i).toNat<8380417)
    (hb : ∀i<256,-8380417<(coeffAt m a i).toInt ∧ (coeffAt m a i).toInt<2*8380417)
    {j : Nat} (hj : j≤64) :
    ∀e<4,vword (lowRun m g B p a l j).flags e=maskWord (flagBad (lowBad m g p a B) j e) := by
  induction j with
  | zero => intro e he; simp [lowRun,flagBad,maskWord,vword]
  | succ j ih =>
    intro e he
    rw [lowRun]
    simp only [lowStep,laneVector_word _ he]
    rw [ih (by omega_arith) e he,lowOutput_current m g B p a l hpl hap hal (by omega_arith) he,
      lowSigned_mask hg m p a _ (ha _ (by omega_arith)) (hb _ (by omega_arith)) hB hB',maskWord_or]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg)

def lowBody (g : Nat) : List Instr := [0,16,32,48].flatMap (subGroup g)

theorem lowBody_ok {g B : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {s : State} {m : Mem} {p a l : Addr} {u : Nat}
    (hr : LowReady g B s) (hm : s.mem=(lowRun m g B p a l (4*u)).mem) (hf : s.v .v31=(lowRun m g B p a l (4*u)).flags)
    (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u)) (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u))
    (h2 : s.gpr .x2=l+BitVec.ofNat 64 (64*u))
    (ha : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hb : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hl : ∀i<4,InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (lowBody g)) s fun t =>
      StepKeep [.v0,.v1,.v2,.v6,.v7,.v31] s t ∧ LowReady g B t ∧
      t.mem=(lowRun m g B p a l (4*(u+1))).mem ∧ t.v .v31=(lowRun m g B p a l (4*(u+1))).flags := by
  let I := fun i t => StepKeep [.v0,.v1,.v2,.v6,.v7,.v31] s t ∧ LowReady g B t ∧
    t.mem=(lowRun m g B p a l (4*u+i)).mem ∧ t.v .v31=(lowRun m g B p a l (4*u+i)).flags
  have hinit : I 0 s := ⟨StepKeep.ofChg (VChg.refl _ _) (by decide),hr,hm,hf⟩
  have hstep : ∀i<4,∀t,I i t → WP isa (.block (subGroup g (16*i))) t (I (i+1)) := by
    intro i hi t ⟨hk,hready,hmem,hflags⟩
    refine WP.mono (subGroup_step hg hi hready hmem hflags
      ((hk.keep.get .x0).trans h0) ((hk.keep.get .x1).trans h1) ((hk.keep.get .x2).trans h2) ?_ ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv⟩ => ?_
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x0] using ha i hi
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x1] using hb i hi
    · simpa only [hk.keep.wr,hk.keep.get .x0] using hw i hi
    · simpa only [hk.keep.wr,hk.keep.get .x2] using hl i hi
    · refine ⟨(hk.trans hv).mono (by decide),hrv,?_,?_⟩
      · rw [show 4*u+(i+1)=4*u+i+1 by omega_arith,lowRun]
        with_reducible exact hmv
      · rw [show 4*u+(i+1)=4*u+i+1 by omega_arith,lowRun]
        with_reducible exact hfv
  have h := fourGroups_ok (subGroup g) I hinit hstep
  simpa only [I,lowBody,show 4*u+4=4*(u+1) by omega_arith] using h

theorem lowLoop_ok {g B : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {s : State} (hr : LowReady g B s)
    (hc : s.gpr .x10=16) (hf : s.v .v31=0)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa (.loop (.block (lowBody g++advance [.x0,.x1,.x2])) (.nonzero .x .x10)) s fun t =>
      Keep [.x0,.x1,.x2,.x10] s t ∧ LowReady g B t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+1024 ∧ t.gpr .x2=s.gpr .x2+1024 ∧
      t.mem=(lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).mem ∧
      t.v .v31=(lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).flags := by
  let I := fun u t => Keep [.x0,.x1,.x2,.x10] s t ∧ LowReady g B t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (64*u) ∧ t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (64*u) ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (64*u) ∧
    t.mem=(lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (4*u)).mem ∧
    t.v .v31=(lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (4*u)).flags
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 16) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ⟨hk,hready,h0,h1,h2,hm,hf⟩ _
    rw [WP.block_append_iff]
    refine WP.mono (lowBody_ok hg hready hm hf h0 h1 h2 ?_ ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv⟩ => ?_
    · intro i hi
      simp only [hk.rd,hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact ha _ (by omega_arith)
    · intro i hi
      simp only [hk.rd,hk.wr,h1,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hb _ (by omega_arith)
    · intro i hi
      simp only [hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hw _ (by omega_arith)
    · intro i hi
      simp only [hk.wr,h2,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hl _ (by omega_arith)
    · refine WP.mono (advance3_ok v) fun w ⟨⟨⟨hw0,hw1,hw2,hw10,hwm⟩,hkw⟩,hvw⟩ => ?_
      refine ⟨⟨((hk.trans hv.keep).trans hkw).mono,?_,?_,?_,?_,hwm.trans hmv,?_⟩,?_⟩
      · exact hrv.frame (rs := []) (by intro r _; exact congrFun hvw r) (by simp)
      · rw [hw0,hv.keep.get .x0,h0,show 64*(u+1)=64*u+64 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw1,hv.keep.get .x1,h1,show 64*(u+1)=64*u+64 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw2,hv.keep.get .x2,h2,show 64*(u+1)=64*u+64 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hvw,hfv]
      · rw [hw10,hv.keep.get .x10]; rfl
  · exact ⟨Keep.refl _ _,hr,by simp,by simp,by simp,rfl,hf⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Round

def lowArm (g : Nat) : Prog isa :=
  .seq (.block (lowInit g)) (.seq (.seq (.block [.movz .x .x10 16 0])
    (.loop (.block (lowBody g++advance [.x0,.x1,.x2])) (.nonzero .x .x10)))
    VG.Impl.MlDsa.AArch64.Optimized.Response.finish)

theorem subLowNorm_eq : VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm=
    VG.Impl.MlDsa.AArch64.Round.zext .x3 (VG.Impl.MlDsa.AArch64.Round.onGamma .x3 .x5 lowArm) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
  congr 1

theorem lowArm_words_ok {g B : Nat} (hg : IsG g) (hB : 1≤B) (s : State)
    (hbound : (s.gpr .x4).setWidth 32=BitVec.ofNat 32 B)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa (lowArm g) s fun t =>
      Keep [.x0,.x1,.x2,.x9,.x10] s t ∧
      t.mem=(lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).mem ∧
      t.gpr .x0=finishValue (lowRun s.mem g B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).flags := by
  unfold lowArm
  apply WP.seq
  refine WP.mono (lowInit_ok hg hB hbound) fun a ⟨hsa,hready,hzero⟩ => ?_
  have hka := setup_keep hsa (by decide)
  apply WP.seq
  apply WP.seq
  refine WP.mono (counter_ok a) fun b ⟨⟨⟨hcount,hmem⟩,hkb⟩,hvec⟩ => ?_
  have hksb := hka.trans hkb
  have hrb : LowReady g B b := hready.frame (rs:=[]) (fun r _=>congrFun hvec r) (by simp)
  refine WP.mono (lowLoop_ok hg hrb hcount (by rw [hvec,hzero]) ?_ ?_ ?_ ?_) fun c ⟨hkc,_,_,_,_,hmc,hfc⟩ => ?_
  · simpa only [hkb.rd,hkb.wr,hkb.get .x0,hka.rd,hka.wr,hka.get .x0] using ha
  · simpa only [hkb.rd,hkb.wr,hkb.get .x1,hka.rd,hka.wr,hka.get .x1] using hb
  · simpa only [hkb.wr,hkb.get .x0,hka.wr,hka.get .x0] using hw
  · simpa only [hkb.wr,hkb.get .x2,hka.wr,hka.get .x2] using hl
  · refine WP.mono (finish_ok c) fun t ⟨⟨⟨hout,hmt⟩,hkt⟩,_⟩ => ?_
    refine ⟨((hksb.trans hkc).trans hkt).mono,?_,?_⟩
    · rw [hmt,hmc,hmem,hsa.mem,hkb.get .x0,hka.get .x0,hkb.get .x1,hka.get .x1,hkb.get .x2,hka.get .x2]
    · rw [hout,hfc,hmem,hsa.mem,hkb.get .x0,hka.get .x0,hkb.get .x1,hka.get .x1,hkb.get .x2,hka.get .x2]

theorem subLowNorm_words_ok {B : Nat} (s : State) (hg : IsG (arg32 s .x3)) (hB : 1≤B)
    (hbound : (s.gpr .x4).setWidth 32=BitVec.ofNat 32 B)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm s fun t =>
      Keep [.x0,.x1,.x2,.x3,.x5,.x9,.x10] s t ∧
      t.mem=(lowRun s.mem (arg32 s .x3) B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).mem ∧
      t.gpr .x0=finishValue (lowRun s.mem (arg32 s .x3) B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64).flags := by
  rw [subLowNorm_eq]
  apply zext_ok
  have hz := zextS_keep .x3 s
  refine onGamma_ok (by decide) (by rw [zextS_toNat]; exact hg) fun g hge a hka hma => ?_
  have he : g=arg32 s .x3 := by rw [zextS_toNat] at hge; exact hge.symm
  rw [he]
  have hks := hz.trans hka
  refine WP.mono (lowArm_words_ok hg hB a ?_ ?_ ?_ ?_ ?_) fun t ⟨hkt,hmt,hout⟩ => ?_
  · rw [hks.get .x4 (by decide)]; exact hbound
  · simpa only [hks.rd,hks.wr,hks.get .x0 (by decide)] using ha
  · simpa only [hks.rd,hks.wr,hks.get .x1 (by decide)] using hb
  · simpa only [hks.wr,hks.get .x0 (by decide)] using hw
  · simpa only [hks.wr,hks.get .x2 (by decide)] using hl
  · refine ⟨(hks.trans hkt).mono,?_,?_⟩
    · rw [hmt,hma,zextS_mem,hks.get .x0 (by decide),hks.get .x1 (by decide),hks.get .x2 (by decide)]
    · rw [hout,hma,zextS_mem,hks.get .x0 (by decide),hks.get .x1 (by decide),hks.get .x2 (by decide)]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

end

/-! ### `MlDsa.ResponseLowContract`, which this module and modules that import it used -/

section

/-!
# ML-DSA: the contract of the response low bits and their norm

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- The field difference of a canonical coefficient and a signed coefficient. -/
def responseDifference (m : Mem) (w cs : Addr) (i : Nat) : Zq :=
  ofInt (((coeffAt m w i).toNat:Int)-(coeffAt m cs i).toInt)

def responseLowPass (m : Mem) (w cs : Addr) (g B : Nat) : Prop :=
  ∀i<n,normZq (ofInt (lowBits g (responseDifference m w cs i)))<B

instance (m : Mem) (w cs : Addr) (g B : Nat) : Decidable (responseLowPass m w cs g B) :=
  Nat.decidableBallLT n (fun i _ => normZq (ofInt (lowBits g (responseDifference m w cs i)))<B)

def subLowNormSig : Sig where
  params := [("w",.array true .u32 256),("cs",.array false .u32 256),
    ("low",.array true .u32 256),("gamma2",.int .u32 true),("bound",.int .u32 false)]
  ret := some .u32

/-- Decompose the difference and check its low-part norm. Both outputs are exact
on acceptance and rejection; low coefficients are stored as signed integers. -/
def subLowNormContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  subLowNormSig.contract A
    (pre := fun w cs _low gamma2 bound m => Reduced m w ∧ RawReduced m cs ∧
      gamma2.toNat∈gamma2s ∧ 1≤bound.toNat ∧ bound.toNat≤524288)
    (post := fun w cs low gamma2 bound m m' r =>
      (∀i<n,(coeffAt m' w i).toNat=(highBits gamma2.toNat (responseDifference m w cs i)).toNat) ∧
      (∀i<n,(coeffAt m' low i).toInt=lowBits gamma2.toNat (responseDifference m w cs i)) ∧
      r=if responseLowPass m w cs gamma2.toNat bound.toNat then 1 else 0)
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa

end

end

/-! ## From `ResponseLowCorrect.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Round

theorem lowRun_return (m : Mem) (g B : Nat) (p a l : Addr) (hg : IsG g)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    (hB : 1≤B) (hB' : B≤524288) (ha : Reduced m p) (hb : RawReduced m a) :
    finishValue (lowRun m g B p a l 64).flags=if responseLowPass m p a g B then 1 else 0 := by
  have hflags := lowRun_flags m g B p a l hg hpl hap hal hB hB' ha hb (by decide : 64≤64)
  have hf := finishValue_flags hflags
  have he : (∀i<64,∀e<4,lowBad m g p a B i e=false) ↔ responseLowPass m p a g B := by
    simp only [lowBad,responseLowPass,responseDifference]
    constructor
    · intro h i hi
      change i<256 at hi
      have hh := h (i/4) (by omega_using [hi]) (i%4) (by omega_using [])
      rw [show 4*(i/4)+i%4=i by omega_using []] at hh
      exact Nat.lt_of_not_ge (of_decide_eq_false hh)
    · intro h i hi e he
      have hh := h (4*i+e) (by change 4*i+e<256; omega_using [hi, he])
      exact decide_eq_false (by omega_using [hh])
  have hr := finishValue_flags_range hflags
  by_cases h : responseLowPass m p a g B
  · rw [ite_eq_left h]; exact hf.mpr (he.mpr h)
  · rw [ite_eq_right h]
    exact hr.resolve_right (fun hone => h (he.mp (hf.mp hone)))

theorem subLowNorm_ok (s : State) (hg : IsG (arg32 s .x3))
    (hB : 1≤arg32 s .x4) (hB' : arg32 s .x4≤524288)
    (hcan : Reduced s.mem (s.gpr .x0)) (hraw : RawReduced s.mem (s.gpr .x1))
    (hpl : (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x2)))
    (hap : (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x0)))
    (hal : (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x2)))
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm s fun t =>
      Keep [.x0,.x1,.x2,.x3,.x5,.x9,.x10] s t ∧
      (∀i<n,(coeffAt t.mem (s.gpr .x0) i).toNat=
        (highBits (arg32 s .x3) (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)).toNat) ∧
      (∀i<n,(coeffAt t.mem (s.gpr .x2) i).toInt=
        lowBits (arg32 s .x3) (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)) ∧
      t.gpr .x0=if responseLowPass s.mem (s.gpr .x0) (s.gpr .x1) (arg32 s .x3) (arg32 s .x4) then 1 else 0 := by
  refine WP.mono (subLowNorm_words_ok s hg hB (by simp only [arg32,BitVec.ofNat_toNat,BitVec.setWidth_eq]) ha hb hw hl) fun t ⟨hk,hm,hret⟩ => ?_
  refine ⟨hk,?_,?_,?_⟩
  · intro i hi
    rw [hm,(lowRun_coeff _ _ _ _ _ _ hpl hap hal hi).1]
    exact subHigh_word hg (hcan i hi) (hraw i hi).1 (hraw i hi).2
  · intro i hi
    rw [hm,(lowRun_coeff _ _ _ _ _ _ hpl hap hal hi).2]
    exact subLow_word hg (hcan i hi) (hraw i hi).1 (hraw i hi).2
  · rw [hret,lowRun_return _ _ _ _ _ _ hg hpl hap hal hB hB' hcan hraw]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)
open VG.Proof.MlDsa.AArch64.Round

def subLowNormK : Contract isa where
  pre s := s.rd=[polyRegion (s.gpr .x1)] ∧ s.wr=[polyRegion (s.gpr .x0),polyRegion (s.gpr .x2)] ∧
    (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x2)) ∧
    (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x0)) ∧
    (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x2)) ∧
    Reduced s.mem (s.gpr .x0) ∧ RawReduced s.mem (s.gpr .x1) ∧
    IsG (arg32 s .x3) ∧ 1≤arg32 s .x4 ∧ arg32 s .x4≤524288
  post s t :=
    (∀i<n,(coeffAt t.mem (s.gpr .x0) i).toNat=(highBits (arg32 s .x3)
      (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)).toNat) ∧
    (∀i<n,(coeffAt t.mem (s.gpr .x2) i).toInt=lowBits (arg32 s .x3)
      (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)) ∧
    (t.gpr .x0).setWidth 32=if responseLowPass s.mem (s.gpr .x0) (s.gpr .x1) (arg32 s .x3) (arg32 s .x4) then 1 else 0
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x2=t.gpr .x2 ∧
    (s.gpr .x3).setWidth 32=(t.gpr .x3).setWidth 32 ∧ s.sp=t.sp

theorem subLowNorm_correct (s : State) (hp : subLowNormK.pre s) :
    ∃ trace t,Exec isa VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm s trace t ∧
      abiPreserved s t ∧ subLowNormK.post s t := by
  obtain ⟨hr,hw,hpl,hap,hal,hcan,hraw,hg,hB,hB'⟩ := hp
  have hwrite (r : Reg) (hm : polyRegion (s.gpr r)∈s.wr) :
      ∀off,off+16≤1024 → InRegions s.wr (s.gpr r+BitVec.ofNat 64 off) 16 := by
    intro off ho
    exact ⟨_,hm,Offset.contains_base _ ho (by omega_using [ho])⟩
  have hw0 := hwrite .x0 (by rw [hw]; simp)
  have hw2 := hwrite .x2 (by rw [hw]; simp)
  have hr0 : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    obtain ⟨r,hm,hc⟩ := hw0 off ho
    exact ⟨r,List.mem_append_right _ hm,hc⟩
  have hr1 : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
    intro off ho
    exact ⟨polyRegion (s.gpr .x1),by rw [hr]; simp,Offset.contains_base _ ho (by omega_using [ho])⟩
  obtain ⟨tr,t,he,hk,hh,hl,hn⟩ := subLowNorm_ok s hg hB hB' hcan hraw hpl hap hal hr0 hr1 hw0 hw2
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hh,hl,?_⟩
  · intro r hp
    apply hk.gpr r
    simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · rw [hn]
    split <;> rfl

theorem subLowNorm_contract_ct : ConstantTime isa subLowNormK.pre subLowNormK.pub
    VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
  apply zext_ct (τ:=Taint.ofRegs [.x0,.x1,.x2,.x3]) ?_ (by taint_decide)
  intro s t hp
  have h := agree_zext (gr:=.x3) (rs:=[.x0,.x1,.x2]) hp.2.2.2.2 hp.2.2.2.1 ?_
  · exact ⟨h.1,fun r hr=>h.2 r (by simpa [Taint.mem_ofRegs,List.mem_cons,or_comm,or_left_comm,or_assoc] using hr)⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2.1

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

def subLowNormSat : State where
  gpr r := match r with
    | .x0 => 4096 | .x1 => 8192 | .x2 => 12288 | .x3 => 95232 | .x4 => 1 | _ => 0
  sp := 65536
  mem _ := 0
  rd := [⟨8192,1024⟩]
  wr := [⟨4096,1024⟩,⟨12288,1024⟩]

theorem subLowNorm_verified : Verified target VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
    (subLowNormContract abi) := by
  refine Verified.of_correct subLowNorm_correct subLowNorm_contract_ct ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · intro s h
    sig_pre [subLowNormContract,subLowNormSig,abi,argRegs] at h
    sig_split h
    refine ⟨by assumption,by assumption,by assumption,?_,?_,by assumption,by assumption,?_,by assumption,h⟩
    · exact Region.Disjoint.symm (by assumption)
    · with_reducible assumption
    · exact isG_of_mem (by assumption)
  · sig_implies_post [subLowNormContract,subLowNormSig,subLowNormK,arg32,abi,argRegs]
  · sig_implies_pub [subLowNormContract,subLowNormSig,subLowNormK,abi,argRegs]
  · refine ⟨subLowNormSat,?_⟩
    sig_pre [subLowNormContract,subLowNormSig,abi,argRegs]
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

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem subLowNorm_callee (S : Nat) : CalleeOk S VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
    (subLowNormContract abi) := CalleeOk.of_ct subLowNorm_verified.1 subLowNorm_verified.2.1 (by lit_decide) (fun _ _ h => h) (Nat.zero_le _)

abbrev subLowNormArgs (w cs low : Ptr) (g B : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr w),(.x1,.ptr cs),(.x2,.ptr low),(.x3,.imm g),(.x4,.imm B)]

structure SubLowNormReady (w cs low : Ptr) (g B : Nat) (s : State) : Prop where
  wFit : (pa s w).toNat+1024≤2^64
  csFit : (pa s cs).toNat+1024≤2^64
  lowFit : (pa s low).toNat+1024≤2^64
  wCs : (polyRegion (pa s w)).Disjoint (polyRegion (pa s cs))
  wLow : (polyRegion (pa s w)).Disjoint (polyRegion (pa s low))
  csLow : (polyRegion (pa s cs)).Disjoint (polyRegion (pa s low))
  canonical : Reduced s.mem (pa s w)
  raw : RawReduced s.mem (pa s cs)
  gamma : g∈gamma2s
  boundPos : 1≤B
  boundMax : B≤524288
  readable : Covers [polyRegion (pa s cs),polyRegion (pa s w),polyRegion (pa s low)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s w),polyRegion (pa s low)] s.wr

theorem SubLowNormReady.gamma_lt {w cs low : Ptr} {g B : Nat} {s : State}
    (h : SubLowNormReady w cs low g B s) : g<2^32 := by
  have hg := VG.Proof.MlDsa.AArch64.Round.isG_of_mem h.gamma
  rcases hg with rfl|rfl <;> decide

theorem subLowNormAt_pre {s s1 : State} {w cs low : Ptr} {g B : Nat}
    (h : SubLowNormReady w cs low g B s) (h1 : Args (subLowNormArgs w cs low g B) s s1) :
    (subLowNormContract abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s cs)] [polyRegion (pa s w),polyRegion (pa s low)]) := by
  sig_pre [subLowNormContract,subLowNormSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,Args.mem h1,Arg.val]
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega_arith
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega_arith
  rw [hg,hB]
  exact ⟨trivial,trivial,h.wCs,h.wLow,h.csLow,h.wFit,h.csFit,h.lowFit,h.canonical,h.raw,h.gamma,h.boundPos,h.boundMax⟩

theorem subLowNormArgs_ok {w cs low : Ptr} {g B : Nat}
    (hw : (Arg.ptr w).Ok) (hc : (Arg.ptr cs).Ok) (hl : (Arg.ptr low).Ok) :
    ∀x∈subLowNormArgs w cs low g B,x.2.Ok ∧ x.1∈argRegs := by
  simp only [subLowNormArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl|rfl|rfl|rfl|rfl
  · exact ⟨hw,by simp⟩
  · exact ⟨hc,by simp⟩
  · exact ⟨hl,by simp⟩
  · exact ⟨trivial,by simp⟩
  · exact ⟨trivial,by simp⟩

def SubLowNormPost (g B : Nat) (m m' : Mem) (w cs low : Addr) (r : BitVec 32) : Prop :=
  (∀i<n,(coeffAt m' w i).toNat=(highBits g (responseDifference m w cs i)).toNat) ∧
  (∀i<n,(coeffAt m' low i).toInt=lowBits g (responseDifference m w cs i)) ∧
  r=if responseLowPass m w cs g B then 1 else 0

theorem subLowNormAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {w cs low : Ptr} {g B : Nat}
    (hw : (Arg.ptr w).Ok) (hc : (Arg.ptr cs).Ok) (hl : (Arg.ptr low).Ok)
    (h : SubLowNormReady w cs low g B s) :
    WP isa (callAt nm VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm (subLowNormArgs w cs low g B)) s fun t =>
      Post S s t [polyRegion (pa s w),polyRegion (pa s low)] ∧
      SubLowNormPost g B s.mem t.mem (pa s w) (pa s cs) (pa s low) ((t.gpr .x0).setWidth 32) := by
  refine WP.mono (callAtSyms_ok hS (subLowNorm_callee S)
    (subLowNormArgs_ok hw hc hl) (by simp)
    (fun s1 h1 _=>subLowNormAt_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ?_
  sig_post [subLowNormContract,subLowNormSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,Args.mem h1] at hq
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega_arith
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega_arith
  simpa only [SubLowNormPost,Arg.val,hg,hB] using And.intro hP hq

end VG.Proof.MlDsa.AArch64.Optimized.Response
