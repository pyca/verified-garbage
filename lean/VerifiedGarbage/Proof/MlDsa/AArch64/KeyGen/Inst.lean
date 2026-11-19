module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSelected
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSelected
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenRound
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Power2Round
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenRound
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Power2Round
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-! ### `MlDsa.AArch64.Optimized.KeygenRoundVerified`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.KeygenRoundSemantic`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.KeygenRoundMemory`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.KeygenRoundWord`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64 VG.Spec.MlDsa

def highWord (x : BitVec 32) : BitVec 32 := (x+4095#32)>>>13
def rawWord (x : BitVec 32) : BitVec 32 := x-(highWord x<<<13)
def lowWord (x : BitVec 32) : BitVec 32 := Inverse.signCorrected (rawWord x)

theorem highWord_nat {x : BitVec 32} (hx : x.toNat<q) :
    (highWord x).toNat=(x.toNat+4095)/8192 := by
  change x.toNat<8380417 at hx
  simp only [highWord,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_add]
  change ((x.toNat+4095)%4294967296)/8192=(x.toNat+4095)/8192
  rw [Nat.mod_eq_of_lt (by omega_using [hx])]

theorem rawWord_int {x : BitVec 32} (hx : x.toNat<q) :
    (rawWord x).toInt=((x.toNat+4095)%8192:Int)-4095 := by
  have hh := highWord_nat hx
  have hx' : x.toNat<8380417 := hx
  have he := BitVec.toInt_eq_toNat_cond (rawWord x)
  have hv : (rawWord x).toNat=(2^32-(((x.toNat+4095)/8192*8192)%2^32)+x.toNat)%2^32 := by
    simp only [rawWord,BitVec.toNat_sub,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,hh]
  rw [hv] at he
  omega_using [he]

theorem highWord_eq {x : BitVec 32} (hx : x.toNat<q) :
    highWord x=VG.Proof.MlDsa.AArch64.Round.t1V x := by
  apply BitVec.eq_of_toNat_eq
  rw [highWord_nat hx,VG.Proof.MlDsa.AArch64.Round.t1V_toNat hx]

theorem lowWord_eq {x : BitVec 32} (hx : x.toNat<q) :
    lowWord x=VG.Proof.MlDsa.AArch64.Round.t0V x := by
  have hr := rawWord_int hx
  have hb : (x.toNat+4095)%8192<8192 := Nat.mod_lt _ (by decide)
  have he := Inverse.signCorrected_int (rawWord x) (by omega_using [hr]) (by omega_using [hr])
  have hv := BitVec.toInt_eq_toNat_cond (lowWord x)
  change (lowWord x).toInt=_ at he
  rw [hr] at he
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.MlDsa.AArch64.Round.t0V_toNat hx]
  change (lowWord x).toNat=if (x.toNat+4095)%8192<4095 then (x.toNat+4095)%8192+8380417-4095 else (x.toNat+4095)%8192-4095
  split <;> split at he <;> omega

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end

end


/-! ## From `KeygenRoundVec.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenRound

theorem cadd_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (k : ∀t,VChg [.v0,.v7] s t →
      (∀e<4,vword (t.v .v0) e=Inverse.signCorrected (vword (s.v .v0) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (cadd .v0++rest)) s Q := by
  refine wp_vop (d:=.v7) rfl fun a ha => wp_vop (d:=.v7) rfl fun b hb =>
    wp_vop (d:=.v0) rfl fun t ht => ?_
  refine k t ((ha.chg.trans hb.chg).trans ht.chg |>.mono (by simp)) ?_
  intro e he
  rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.get .v0 (by decide),ha.get .v0 (by decide),
    hb.v,Inverse.word_and,ha.v,VG.AArch64.vword_map2 _ _ _ he,ha.get .v16 (by decide),hq e he]
  rfl

theorem arithmetic_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v17) e=4095#32)
    (k : ∀t,VChg [.v0,.v1,.v2,.v7] s t →
      (∀e<4,vword (t.v .v1) e=highWord (vword (s.v .v0) e)) →
      (∀e<4,vword (t.v .v0) e=lowWord (vword (s.v .v0) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (arithmetic++rest)) s Q := by
  simp only [arithmetic,List.cons_append,List.nil_append]
  refine wp_vop (d:=.v1) rfl fun a ha => wp_vop (d:=.v1) rfl fun b hb =>
    wp_vop (d:=.v2) rfl fun c hc' => wp_vop (d:=.v0) rfl fun d hd => ?_
  have hk : VChg [.v0,.v1,.v2] s d := (((ha.chg.trans hb.chg).trans hc'.chg).trans hd.chg).mono (by simp)
  have high : ∀e<4,vword (d.v .v1) e=highWord (vword (s.v .v0) e) := by
    intro e he
    rw [hd.get .v1 (by decide),hc'.get .v1 (by decide),hb.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.v,VG.AArch64.vword_map2 _ _ _ he,hc e he]
    rfl
  have raw : ∀e<4,vword (d.v .v0) e=rawWord (vword (s.v .v0) e) := by
    intro e he
    rw [hd.v,VG.AArch64.vword_map2 _ _ _ he,hc'.get .v0 (by decide),hb.get .v0 (by decide),ha.get .v0 (by decide),
      hc'.v,VG.AArch64.vword_map2 _ _ _ he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.v,VG.AArch64.vword_map2 _ _ _ he,hc e he]
    rfl
  refine cadd_ok (by intro e he; rw [hk.get .v16 (by decide)]; exact hq e he) fun t ht hv =>
    k t ((hk.trans ht).mono (by simp)) ?_ ?_
  · intro e he; rw [ht.get .v1 (by decide)]; exact high e he
  · intro e he; rw [hv e he,raw e he]; rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end

/-! ## From `KeygenRoundMem.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq wp_strq)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenRound

def wordVector (f : Nat → BitVec 32) : BitVec 128 := ofVWords (f 0) (f 1) (f 2) (f 3)
theorem wordVector_word (f : Nat → BitVec 32) {e : Nat} (he : e<4) : vword (wordVector f) e=f e := by
  rw [wordVector,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  have h : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega_using [he]
  rcases h with rfl|rfl|rfl|rfl <;> rfl

def highVector (v : BitVec 128) : BitVec 128 := wordVector fun e=>highWord (vword v e)
def lowVector (v : BitVec 128) : BitVec 128 := wordVector fun e=>lowWord (vword v e)

theorem body_ok {s : State} {off : Nat} (ho : off%16=0 ∧ off<65536)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hh : InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hl : InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v17) e=4095#32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepKeep [.v0,.v1,.v2,.v7] s t →
      t.mem=(s.mem.write (s.gpr .x1+BitVec.ofNat 64 off) 16
        (highVector (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16))).write
          (s.gpr .x2+BitVec.ofNat 64 off) 16 (lowVector (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (body off++rest)) s Q := by
  simp only [body,List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl hr fun a ha => ?_
  refine arithmetic_ok (by intro e he; rw [ha.get .v16 (by decide)]; exact hq e he)
    (by intro e he; rw [ha.get .v17 (by decide)]; exact hc e he) fun b hb hhigh hlow => ?_
  have hk : VChg [.v0,.v1,.v2,.v7] s b := (ha.chg.trans hb).mono (by simp)
  have eh : b.v .v1=highVector (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) := by
    apply vec_ext
    intro e he
    rw [hhigh e he,ha.v]
    exact (wordVector_word (fun e=>highWord (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e)) he).symm
  have el : b.v .v0=lowVector (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) := by
    apply vec_ext
    intro e he
    rw [hlow e he,ha.v]
    exact (wordVector_word (fun e=>lowWord (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e)) he).symm
  refine wp_strq ho rfl (by simpa only [hk.wr,hk.gpr] using hh) fun c hcs => ?_
  refine wp_strq ho rfl (by simpa only [hcs.wr,hcs.gpr,hk.wr,hk.gpr] using hl) fun d hds => ?_
  refine k d (((StepKeep.ofChg hk (by decide)).trans (StepKeep.ofMem hcs)).trans (StepKeep.ofMem hds) |>.mono (by simp)) ?_
  simp only [hds.mem,hcs.mem,hcs.gpr,hcs.v,hk.mem,hk.gpr,eh,el]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end

/-! ## From `KeygenRoundMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenRound

structure Ready (s : State) : Prop where
  q : ∀e<4,vword (s.v .v16) e=8380417#32
  bias : ∀e<4,vword (s.v .v17) e=4095#32

theorem Ready.frame {s t : State} (h : Ready s) (hk : StepKeep [.v0,.v1,.v2,.v7] s t) : Ready t :=
  ⟨by intro e he; rw [hk.vec .v16 (by decide)]; exact h.q e he,
   by intro e he; rw [hk.vec .v17 (by decide)]; exact h.bias e he⟩

def roundStep (input high low : Addr) (j : Nat) (m : Mem) : Mem :=
  let v := m.read (input+BitVec.ofNat 64 (16*j)) 16
  (m.write (high+BitVec.ofNat 64 (16*j)) 16 (highVector v)).write
    (low+BitVec.ofNat 64 (16*j)) 16 (lowVector v)
def roundRun (m : Mem) (input high low : Addr) : Nat → Mem
  | 0 => m
  | j+1 => roundStep input high low j (roundRun m input high low j)

theorem roundRun_next (m : Mem) (input high low : Addr) (j : Nat) :
    roundRun m input high low (j+1)=roundStep input high low j (roundRun m input high low j) := rfl

theorem body_step {s : State} {input high low : Addr} {u i : Nat}
    (hi : i<4) (hr : Ready s)
    (h0 : s.gpr .x0=input+BitVec.ofNat 64 (64*u))
    (h1 : s.gpr .x1=high+BitVec.ofNat 64 (64*u))
    (h2 : s.gpr .x2=low+BitVec.ofNat 64 (64*u))
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hh : InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hl : InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (body (16*i))) s fun t =>
      StepKeep [.v0,.v1,.v2,.v7] s t ∧ Ready t ∧ t.mem=roundStep input high low (4*u+i) s.mem := by
  rw [←List.append_nil (body (16*i))]
  refine body_ok (by omega_using [hi]) ha hh hl hr.q hr.bias fun t hk hm => WP.block_nil_iff.mpr ⟨hk,hr.frame hk,?_⟩
  simpa only [roundStep,h0,h1,h2,BitVec.add_assoc,←BitVec.ofNat_add,
    show 64*u+16*i=16*(4*u+i) by omega_using []] using hm

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16 vword_read16 vector_contains)

theorem readWord (m : Mem) (p : Addr) (j : Nat) {e : Nat} (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (16*j)) 16) e=coeffAt m p (4*j+e) := by
  rw [show 16*j=4*(4*j) by omega_using []]
  change vword (m.read (coeffAddr p (4*j)) 16) e=_
  rw [VG.AArch64.vword_read16 _ _ he,coeffAddr_add]
  rfl

theorem writeOther {m : Mem} {p o : Addr} {j k : Nat} {v : BitVec 128}
    (hd : (pR p).Disjoint (pR o)) (hj : j<64) (hk : k<256) :
    coeffAt (m.write (o+BitVec.ofNat 64 (16*j)) 16 v) p k=coeffAt m p k := by
  have hf : Frame [pR o] m (m.write (o+BitVec.ofNat 64 (16*j)) 16 v) := by
    rw [show 16*j=4*(4*j) by omega_using []]
    exact (Frame.refl _ _).write (by simp) _ (vector_contains o (by omega_using [hj]))
  exact coeffAt_frame hf (by simpa using hd) hk

theorem roundStep_high {m : Mem} {input high low : Addr} {j k : Nat}
    (hd : (pR high).Disjoint (pR low)) (hj : j<64) (hk : k<256) :
    coeffAt (roundStep input high low j m) high k=
      if 4*j≤k ∧ k<4*j+4 then highWord (coeffAt m input k) else coeffAt m high k := by
  unfold roundStep
  rw [writeOther hd hj hk,show 16*j=4*(4*j) by omega_using []]
  change coeffAt (m.write (coeffAddr high (4*j)) 16 _) high k=_
  rw [coeffAt_write16 _ _ (by omega_using [hj]) _ hk]
  split
  · rename_i h
    change vword (wordVector _) (k-4*j)=_
    rw [wordVector_word _ (by omega_using [h])]
    have hr := readWord m input j (e:=k-4*j) (by omega_using [h])
    rw [show 16*j=4*(4*j) by omega_using [],show 4*j+(k-4*j)=k by omega_using [h]] at hr
    rw [hr]
  · rfl

theorem roundStep_low {m : Mem} {input high low : Addr} {j k : Nat}
    (hd : (pR high).Disjoint (pR low)) (hj : j<64) (hk : k<256) :
    coeffAt (roundStep input high low j m) low k=
      if 4*j≤k ∧ k<4*j+4 then lowWord (coeffAt m input k) else coeffAt m low k := by
  unfold roundStep
  rw [show 16*j=4*(4*j) by omega_using []]
  rw [coeffAt_write16 _ _ (by omega_using [hj]) _ hk]
  split
  · rename_i h
    change vword (wordVector _) (k-4*j)=_
    rw [wordVector_word _ (by omega_using [h])]
    have hr := readWord m input j (e:=k-4*j) (by omega_using [h])
    rw [show 16*j=4*(4*j) by omega_using [],show 4*j+(k-4*j)=k by omega_using [h]] at hr
    rw [hr]
  · simpa only [show 16*j=4*(4*j) by omega_using []] using
      (writeOther (m:=m) (p:=low) (o:=high) (j:=j) (k:=k)
        (v:=highVector (m.read (input+BitVec.ofNat 64 (4*(4*j))) 16)) hd.symm hj hk)

theorem roundRun_frame (m : Mem) (input high low : Addr) {j : Nat} (hj : j≤64) :
    Frame [pR high,pR low] m (roundRun m input high low j) := by
  induction j with
  | zero => exact Frame.refl _ _
  | succ j ih =>
    rw [roundRun_next]
    unfold roundStep
    rw [show 16*j=4*(4*j) by omega_using []]
    exact ((ih (by omega_using [hj])).write (by simp) _ (vector_contains high (by omega_using [hj]))).write
      (by simp) _ (vector_contains low (by omega_using [hj]))

theorem roundRun_prefix (m : Mem) (input high low : Addr)
    (hih : (pR input).Disjoint (pR high)) (hil : (pR input).Disjoint (pR low))
    (hhl : (pR high).Disjoint (pR low)) {j : Nat} (hj : j≤64) :
    ∀k<256,
      (coeffAt (roundRun m input high low j) high k=if k<4*j then highWord (coeffAt m input k) else coeffAt m high k) ∧
      (coeffAt (roundRun m input high low j) low k=if k<4*j then lowWord (coeffAt m input k) else coeffAt m low k) := by
  induction j with
  | zero => intro k hk; simp [roundRun]
  | succ j ih =>
    have hp := ih (by omega_using [hj])
    have input_kept : ∀k<256,coeffAt (roundRun m input high low j) input k=coeffAt m input k := by
      intro k hk
      exact coeffAt_frame (roundRun_frame m input high low (by omega_using [hj]))
        (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl; exact hih; exact hil) hk
    intro k hk
    rw [roundRun_next,roundStep_high hhl (by omega_using [hj]) hk,roundStep_low hhl (by omega_using [hj]) hk]
    rw [(hp k hk).1,(hp k hk).2,input_kept k hk]
    by_cases before : k<4*j
    · simp only [ite_eq_right (by omega_using [before] : ¬(4*j≤k ∧ k<4*j+4)),ite_eq_left before,ite_eq_left (by omega_using [before] : k<4*(j+1))]
      exact ⟨trivial,trivial⟩
    · by_cases inside : k<4*j+4
      · simp only [ite_eq_left (by omega_using [before, inside] : 4*j≤k ∧ k<4*j+4),ite_eq_left (by omega_using [inside] : k<4*(j+1))]
        exact ⟨trivial,trivial⟩
      · simp only [ite_eq_right (by omega_using [inside] : ¬(4*j≤k ∧ k<4*j+4)),ite_eq_right before,ite_eq_right (by omega_using [inside] : ¬k<4*(j+1))]
        exact ⟨trivial,trivial⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end

end

/-! ## From `KeygenRoundLoop.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep fourGroups_ok advance advance3_ok)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenRound

def fourBody : List Instr := [0,16,32,48].flatMap body

theorem fourBody_ok {s : State} {m : Mem} {input high low : Addr} {u : Nat}
    (hr : Ready s) (hm : s.mem=roundRun m input high low (4*u))
    (h0 : s.gpr .x0=input+BitVec.ofNat 64 (64*u))
    (h1 : s.gpr .x1=high+BitVec.ofNat 64 (64*u))
    (h2 : s.gpr .x2=low+BitVec.ofNat 64 (64*u))
    (ha : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hh : ∀i<4,InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hl : ∀i<4,InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block fourBody) s fun t =>
      StepKeep [.v0,.v1,.v2,.v7] s t ∧ Ready t ∧ t.mem=roundRun m input high low (4*(u+1)) := by
  let I := fun i t=>StepKeep [.v0,.v1,.v2,.v7] s t ∧ Ready t ∧ t.mem=roundRun m input high low (4*u+i)
  have hinit : I 0 s := ⟨StepKeep.ofChg (VChg.refl _ _) (by decide),hr,hm⟩
  have hstep : ∀i<4,∀t,I i t → WP isa (.block (body (16*i))) t (I (i+1)) := by
    intro i hi t ⟨hk,hready,hmem⟩
    refine WP.mono (body_step hi hready ((hk.keep.get .x0).trans h0)
      ((hk.keep.get .x1).trans h1) ((hk.keep.get .x2).trans h2) ?_ ?_ ?_) fun v ⟨hv,hrv,hmv⟩ => ?_
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x0] using ha i hi
    · simpa only [hk.keep.wr,hk.keep.get .x1] using hh i hi
    · simpa only [hk.keep.wr,hk.keep.get .x2] using hl i hi
    · refine ⟨(hk.trans hv).mono (by decide),hrv,?_⟩
      change v.mem=roundRun m input high low (4*u+(i+1))
      rw [show 4*u+(i+1)=4*u+i+1 by omega_arith,roundRun_next,←hmem]
      exact hmv
  simpa only [I,fourBody,show 4*u+4=4*(u+1) by omega_arith] using fourGroups_ok body I hinit hstep

theorem roundLoop_ok {s : State} (hr : Ready s) (hc : s.gpr .x10=16)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hh : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa (.loop (.block (fourBody++advance [.x0,.x1,.x2])) (.nonzero .x .x10)) s fun t =>
      Keep [.x0,.x1,.x2,.x10] s t ∧ Ready t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+1024 ∧ t.gpr .x2=s.gpr .x2+1024 ∧
      t.mem=roundRun s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64 := by
  let I := fun u t=>Keep [.x0,.x1,.x2,.x10] s t ∧ Ready t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (64*u) ∧
    t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (64*u) ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (64*u) ∧
    t.mem=roundRun s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (4*u)
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N:=16) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ⟨hk,hready,h0,h1,h2,hm⟩ _
    rw [WP.block_append_iff]
    refine WP.mono (fourBody_ok hready hm h0 h1 h2 ?_ ?_ ?_) fun v ⟨hv,hrv,hmv⟩ => ?_
    · intro i hi
      simp only [hk.rd,hk.wr,h0,BitVec.add_assoc,←BitVec.ofNat_add]
      exact ha _ (by omega_arith)
    · intro i hi
      simp only [hk.wr,h1,BitVec.add_assoc,←BitVec.ofNat_add]
      exact hh _ (by omega_arith)
    · intro i hi
      simp only [hk.wr,h2,BitVec.add_assoc,←BitVec.ofNat_add]
      exact hl _ (by omega_arith)
    · refine WP.mono (advance3_ok v) fun w ⟨⟨⟨hw0,hw1,hw2,hw10,hwm⟩,hkw⟩,hvw⟩ => ?_
      refine ⟨⟨((hk.trans hv.keep).trans hkw).mono,?_,?_,?_,?_,hwm.trans hmv⟩,?_⟩
      · exact ⟨by rw [hvw]; exact hrv.q,by rw [hvw]; exact hrv.bias⟩
      · rw [hw0,hv.keep.get .x0,h0,show 64*(u+1)=64*u+64 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw1,hv.keep.get .x1,h1,show 64*(u+1)=64*u+64 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw2,hv.keep.get .x2,h2,show 64*(u+1)=64*u+64 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw10,hv.keep.get .x10]; rfl
  · exact ⟨Keep.refl _ _,hr,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end

/-! ## From `KeygenRoundCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.KeygenRound
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep repeatedWord_lane)

theorem setup_ok (s : State) :
    WP isa (.block (vc .v16 8380417 ++ vc .v17 4095)) s fun t =>
      SetupKeep [.v16,.v17] s t ∧ Ready t := by
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s .v16 8380417) fun a ha => ?_
  refine WP.mono (HighPack.vc_ok a .v17 4095) fun t ht => ?_
  refine ⟨(SetupKeep.ofConst ha.1).trans (SetupKeep.ofConst ht.1),?_,?_⟩
  · intro e he
    rw [ht.1.vec .v16 (by decide),ha.2,repeatedWord_lane _ he]
  · intro e he
    rw [ht.2,repeatedWord_lane _ he]

theorem run_ok (s : State)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hh : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa power2Round s fun t =>
      t.mem=roundRun s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64 := by
  unfold power2Round loop
  refine WP.seq (WP.mono (setup_ok s) fun a ⟨hk,hr⟩ => ?_)
  refine WP.seq (WP.mono (Response.counter_ok a) fun b ⟨⟨hc,hm⟩,hv⟩ => ?_)
  have hb : Ready b := ⟨by rw [hv]; exact hr.q,by rw [hv]; exact hr.bias⟩
  have h0 : b.gpr .x0=s.gpr .x0 := (hm.get .x0).trans (hk.gpr .x0 (by decide))
  have h1 : b.gpr .x1=s.gpr .x1 := (hm.get .x1).trans (hk.gpr .x1 (by decide))
  have h2 : b.gpr .x2=s.gpr .x2 := (hm.get .x2).trans (hk.gpr .x2 (by decide))
  refine WP.mono (roundLoop_ok hb hc.1 ?_ ?_ ?_) fun t ht => ?_
  · simpa only [hm.rd,hm.wr,hk.rd,hk.wr,h0] using ha
  · simpa only [hm.wr,hk.wr,h1] using hh
  · simpa only [hm.wr,hk.wr,h2] using hl
  · simpa only [h0,h1,h2,hc.2,hk.mem] using ht.2.2.2.2.2

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end

/-! ## From `KeygenRoundVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Round (power2RoundK p2rSat)
open VG.Proof.MlDsa.Round (natPolyIs_of_toNat map_get)
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem correct (s : State) (hp : power2RoundK.pre s) :
    ∃tr t, Exec isa VG.Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round s tr t ∧
      abiPreserved s t ∧ power2RoundK.post s t := by
  obtain ⟨tr,t,he,hm⟩ := run_ok s (fun off ho =>
    ⟨pR (s.gpr .x0),by rw [hp.1]; simp,Offset.contains_base _ ho (by omega_arith)⟩)
    (fun off ho => ⟨pR (s.gpr .x1),by rw [hp.2.1]; simp,Offset.contains_base _ ho (by omega_arith)⟩)
    (fun off ho => ⟨pR (s.gpr .x2),by rw [hp.2.1]; simp,Offset.contains_base _ ho (by omega_arith)⟩)
  have hfield := roundRun_prefix s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
    hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 (by decide : 64≤64)
  have hr := hp.2.2.2.2.2
  refine ⟨tr,t,he,VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he,?_,?_⟩
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hm,(hfield k hk).1,ite_eq_left (by omega_arith),highWord_eq (hr k hk),map_get _ _ hk,
      Round.t1V_toNat (hr k hk),VG.Proof.MlDsa.Round.power2Round_eq,←polyAt_val hr hk]
    exact (Int.toNat_natCast _).symm
  · refine polyIs_of_toNat fun k hk => ?_
    rw [hm,(hfield k hk).2,ite_eq_left (by omega_arith),lowWord_eq (hr k hk),map_get _ _ hk,
      Round.t0V_toNat (hr k hk),VG.Proof.MlDsa.Round.power2Round_t0,polyAt_val hr hk]

theorem constantTime : ConstantTime isa power2RoundK.pre power2RoundK.pub
    VG.Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ hp => VG.Proof.MlDsa.AArch64.Arith.agree_regs hp.2.2.2 fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      exacts [hp.1,hp.2.1,hp.2.2.1]) (by taint_decide)

theorem power2Round_verified : Verified target
    VG.Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round (power2RoundContract abi) :=
  Verified.of_correct correct constantTime (by
    mldsa_implies [power2RoundContract,power2RoundSig,power2RoundK,abi,argRegs] [p2rSat] using p2rSat)

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end

end

end

/-!
# ML-DSA key generation on AArch64, with this library's primitives

The AArch64 implementations of the primitives (`primsWith`), with any
implementation of the Keccak permutation, are verified with at most 16 bytes
of stack, and their frames use at most that (`prims_okWith`), which key
generation (`KeyGen/OptimizedVerified.lean`), signing and verification
with them take.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen

theorem prims_okWith : PrimsOk (primsWith keccak.callee) 16 where
  s16 := Nat.le_refl _
  sl := by decide
  ntt := by
    have h := Arith.Neon.ntt_verified
    unfold Proof.MlDsa.nttContract Proof.MlDsa.inPlaceContract at h ⊢
    exact CalleeOk.of_verified (by decide) h (by decide) (by dsimp only [primsWith]; decide) (by dsimp only [primsWith]; lit_decide)
  add := CalleeOk.of_verified (by decide) Optimized.AddSub.add_verified (by decide) (by dsimp only [primsWith]; decide) (by dsimp only [primsWith]; lit_decide)
  rejNtt := CalleeOk.of_verified (by decide) (Sample.rejNTT_verifiedWith keccak) (by decide) (by simp [primsWith, Sample.rejNTT_depth keccak]) (VG.Proof.MlDsa.AArch64.Sample.rejNTT_noDit keccak)
  rej4 := CalleeOk.of_verified (by decide) (Optimized.ResidentRej.selected_verified keccak.callee.pairedSha3) (by decide)
    (by simp only [primsWith,Optimized.ResidentRej.selected_depth,Nat.mul_zero]; decide) (VG.Proof.MlDsa.AArch64.Optimized.ResidentRej.selected_noDit _)
  ball := CalleeOk.of_verified (by decide) (Optimized.Ball.selected_verified keccak) (by decide) (by simp [primsWith, Optimized.Ball.selected_depth keccak]) (VG.Proof.MlDsa.AArch64.Optimized.Ball.selected_noDit keccak)
  power2Round := CalleeOk.of_verified (by decide) Optimized.KeygenRound.power2Round_verified (by decide) (by dsimp only [primsWith]; decide) (by dsimp only [primsWith]; lit_decide)
  normLt := CalleeOk.of_verified (by decide) Round.normLt_verified (by decide) (by dsimp only [primsWith]; decide) (by dsimp only [primsWith]; lit_decide)
  simpleBitPack := CalleeOk.of_verified (by decide) Optimized.KeygenPack.simple_verified (by decide) (by dsimp only [primsWith]; decide) (by dsimp only [primsWith]; lit_decide)
  bitPack := CalleeOk.of_verified (by decide) Optimized.KeygenPack.signed_verified (by decide) (by dsimp only [primsWith]; decide) (by dsimp only [primsWith]; lit_decide)
  bitUnpack := CalleeOk.of_verified (by decide) Pack.bitUnpack_verified (by decide) (by dsimp only [primsWith]; decide) (by dsimp only [primsWith]; lit_decide)
  unpackT1 := CalleeOk.of_verified (by decide) Pack.unpackT1_verified (by decide) (by dsimp only [primsWith]; decide) (by dsimp only [primsWith]; lit_decide)
  hintUnpack := CalleeOk.of_verified (by decide) Pack.hintBitUnpack_verified (by decide) (by dsimp only [primsWith]; decide) (by dsimp only [primsWith]; lit_decide)

end VG.Proof.MlDsa.AArch64.KeyGen
