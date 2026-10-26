module
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Impl.Dsa.AArch64.Random

import VerifiedGarbage.Proof.Dsa.AArch64.SignificantCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomScan
import VerifiedGarbage.Proof.Dsa.AArch64.RandomClear
import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
meta import VerifiedGarbage.Impl.Dsa.AArch64.Random
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignificantCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomClear
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Preparing the sampler leaks public pointers and lengths only. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure RandomPreparePublic where
  B : Addr
  Q : Addr
  bytes : List Byte

def RandomPreparePre (p : RandomPreparePublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.sp = p.B ∧
  word s.mem p.B Random.oQ = p.Q ∧ word s.mem p.B Random.oQLen = BitVec.ofNat 64 p.bytes.length ∧
  Src s p.B Random.frameBytes p.Q p.bytes ∧ 0 < p.bytes.length ∧ p.bytes.length < 2 ^ 64

def RandomPrepareRegs (p : RandomPreparePublic) (s : State) : Prop :=
  s.sp = p.B ∧ s.gpr .x12 = p.Q ∧ s.gpr .x9 = BitVec.ofNat 64 p.bytes.length ∧
  Src s p.B Random.frameBytes p.Q p.bytes ∧ 0 < p.bytes.length ∧ p.bytes.length < 2 ^ 64

private theorem header_ok {p : RandomPreparePublic} {s : State} (h : RandomPreparePre p s) :
    WP isa (.block (Random.clearNonce ++ ([.ldrSp .x12 Random.oQ, .ldrSp .x9 Random.oQLen] : List Instr))) s (RandomPrepareRegs p) := by
  obtain ⟨hs, hsp, hq, hl, hsrc, hpos, hbound⟩ := h
  rw [WP.block_append_iff]
  refine WP.mono (random_clear_ok hs hsp) fun t ⟨hm, hk⟩ => ?_
  have hts := hs.congr hk.wr
  have htsp := hk.sp.trans hsp
  have htq : word t.mem p.B Random.oQ = p.Q := by
    rw [hm, (random_clear_outside _ _).word (by decide) (by decide)]; exact hq
  have htl : word t.mem p.B Random.oQLen = BitVec.ofNat 64 p.bytes.length := by
    rw [hm, (random_clear_outside _ _).word (by decide) (by decide)]; exact hl
  refine WP.mono (WP.keep [.x12, .x9] (Q := fun u => u.mem = t.mem ∧
      u.gpr .x12 = p.Q ∧ u.gpr .x9 = BitVec.ofNat 64 p.bytes.length) (by
    brun [exec_ldrSp (show Random.oQ % 8 = 0 ∧ Random.oQ < 32768 by decide),
      exec_ldrSp (show Random.oQLen % 8 = 0 ∧ Random.oQLen < 32768 by decide), htsp, hts.ld (d := Random.oQ) (by decide),
      hts.ld (d := Random.oQLen) (by decide), htq, htl]) rfl rfl rfl) fun u ⟨⟨hum, hup, hul⟩, hku⟩ => ?_
  refine ⟨hku.sp.trans htsp, hup, hul, hsrc.congrK ?_ (hk.trans hku), hpos, hbound⟩
  rw [hum, hm]
  exact InScr.of_outside (random_clear_outside _ _) (by decide)

private theorem scan_ct : RelCT isa (Two RandomPrepareRegs) Random.significant (fun _ _ => True) := by
  unfold Random.significant
  refine RelCT.seq (two_piece (Ψ := fun p s => ScanPre ⟨p.B, Random.frameBytes, p.Q, p.bytes⟩ s)
    [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_) ?_
  · intro p s ⟨_, hp, hl, hsrc, hpos, hbound⟩
    refine WP.mono (WP.keep [.x1, .x13] (Q := fun t => t.mem = s.mem ∧
      t.gpr .x1 = p.Q ∧ t.gpr .x9 = BitVec.ofNat 64 p.bytes.length)
      (by brun [hp, hl]) rfl rfl rfl) fun t ⟨⟨hm, ht1, ht2⟩, hk⟩ => ?_
    exact ⟨ht1, ht2, hsrc.congrK (by rw [hm]; exact InScr.refl _ _ _) hk, hpos, hbound⟩
  · refine RelCT.seq (two_post (Ψ := fun (_ : RandomPreparePublic) (_ : State) => True)
      (significant_ct.mono (fun _ _ ⟨p, hs, ht, hsp⟩ =>
        ⟨⟨p.B, Random.frameBytes, p.Q, p.bytes⟩, hs, ht, hsp⟩) (fun _ _ _ => trivial)) ?_) ?_
    · intro p s h
      exact WP.mono (significant_ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
        (fun _ _ => trivial)
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

theorem random_prepare_ct : RelCT isa (Two RandomPreparePre) Random.prepare (fun _ _ => True) := by
  unfold Random.prepare
  refine RelCT.seq (two_piece (Ψ := RandomPrepareRegs) [] ?_ (by taint_decide)
    (fun _ _ h => header_ok h)) ?_
  · intro _ _ _ _ _ _ h; cases h
  · refine RelCT.seq (two_post (Ψ := fun p s => s.sp = p.B) scan_ct ?_) ?_
    · intro p s ⟨hsp, hp, hl, hsrc, hpos, hbound⟩
      exact WP.mono (random_significant_ok hp hl hsrc hpos hbound)
        (fun _ ⟨_, _, _, _, hk⟩ => hk.sp.trans hsp)
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.AArch64
