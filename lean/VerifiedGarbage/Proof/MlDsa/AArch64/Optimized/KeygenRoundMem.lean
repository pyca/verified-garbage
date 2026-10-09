import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

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
