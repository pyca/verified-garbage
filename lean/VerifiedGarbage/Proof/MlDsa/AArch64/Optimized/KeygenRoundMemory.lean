import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenRound
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

/-! ## From `KeygenRoundVec.lean` -/

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
  have h : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
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
  refine body_ok (by omega) ha hh hl hr.q hr.bias fun t hk hm => WP.block_nil_iff.mpr ⟨hk,hr.frame hk,?_⟩
  simpa only [roundStep,h0,h1,h2,BitVec.add_assoc,←BitVec.ofNat_add,
    show 64*u+16*i=16*(4*u+i) by omega] using hm

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

end
