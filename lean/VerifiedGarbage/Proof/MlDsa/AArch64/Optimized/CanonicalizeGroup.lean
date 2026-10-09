import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq wp_strq)

def canonicalizeGroup (off : Nat) : List Instr :=
  [.ldrq .v0 .x0 off] ++ VG.Impl.MlDsa.AArch64.Optimized.Response.cadd .v0 ++ [.strq .v0 .x0 off]

def canonicalizeVector (v : BitVec 128) : BitVec 128 :=
  laneVector fun e => Inverse.signCorrected (vword v e)

def canonicalizeGroupMem (m : Mem) (p : Addr) : Mem :=
  m.write p 16 (canonicalizeVector (m.read p 16))

/-- Exact read/modify/write semantics for four accepted response coefficients. -/
theorem canonicalizeGroup_ok {s : State} {off : Nat} (ho : off%16=0 ∧ off<4096*16)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepKeep [.v0,.v7] s t →
      t.mem=canonicalizeGroupMem s.mem (s.gpr .x0+BitVec.ofNat 64 off) →
      WP isa (.block rest) t Q) :
    WP isa (.block (canonicalizeGroup off++rest)) s Q := by
  unfold canonicalizeGroup
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl hr fun a ha => ?_
  refine cadd_ok (by decide : VReg.v0≠.v7)
    (by intro e he; rw [ha.get .v16]; exact hq e he) fun b hb hv => ?_
  have hk : VChg [.v0,.v7] s b := (ha.chg.trans hb).mono (by decide)
  have hval : b.v .v0=canonicalizeVector (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) := by
    apply vec_ext
    intro e he
    rw [canonicalizeVector,laneVector_word _ he,hv e he,ha.v]
  refine wp_strq ho rfl (by simpa only [hk.wr,hk.gpr] using hw) fun t ht => ?_
  refine k t ((StepKeep.ofChg hk (by decide)).trans (StepKeep.ofMem ht) |>.mono (by decide)) ?_
  rw [ht.mem,hk.mem,hk.gpr,hval]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
