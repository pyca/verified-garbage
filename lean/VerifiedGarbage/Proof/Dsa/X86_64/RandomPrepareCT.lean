module
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Impl.Dsa.X86_64.Random

import VerifiedGarbage.Proof.Dsa.X86_64.SignificantCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
import VerifiedGarbage.Proof.Dsa.X86_64.RandomClear
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
meta import VerifiedGarbage.Impl.Dsa.X86_64.Random
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignificantCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomClear
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Preparing the sampler leaks public pointers and lengths only. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomPreparePublic where
  B : Addr
  Q : Addr
  bytes : List Byte

def RandomPreparePre (p : RandomPreparePublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  word s.mem p.B Random.oQ = p.Q ∧ word s.mem p.B Random.oQLen = BitVec.ofNat 64 p.bytes.length ∧
  Src s p.B Random.frameBytes p.Q p.bytes ∧ 0 < p.bytes.length ∧ p.bytes.length < 2 ^ 64

def RandomPrepareRegs (p : RandomPreparePublic) (s : State) : Prop :=
  s.gpr .rsp = p.B ∧ s.gpr .r10 = p.Q ∧ s.gpr .r11 = BitVec.ofNat 64 p.bytes.length ∧
  Src s p.B Random.frameBytes p.Q p.bytes ∧ 0 < p.bytes.length ∧ p.bytes.length < 2 ^ 64

private theorem header_ok {p : RandomPreparePublic} {s : State} (h : RandomPreparePre p s) :
    WP isa (.block (Random.clearNonce ++ ([.mov .r10 (.mem (Random.sp Random.oQ)),
      .mov .r11 (.mem (Random.sp Random.oQLen))] : List Instr))) s (RandomPrepareRegs p) := by
  obtain ⟨hs, hsp, hq, hl, hsrc, hpos, hbound⟩ := h
  rw [WP.block_append_iff]
  refine WP.mono (random_clear_ok hs hsp) fun t ⟨hm, hk⟩ => ?_
  have hts := hs.congr hk.2.2
  have htsp := (hk.gpr (by decide)).trans hsp
  have htq : word t.mem p.B Random.oQ = p.Q := by
    rw [hm, (random_clear_outside _ _).word (by decide) (by decide)]; exact hq
  have htl : word t.mem p.B Random.oQLen = BitVec.ofNat 64 p.bytes.length := by
    rw [hm, (random_clear_outside _ _).word (by decide) (by decide)]; exact hl
  refine WP.mono (WP.keep [.r10, .r11] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r10 = p.Q ∧ u.gpr .r11 = BitVec.ofNat 64 p.bytes.length) (by
    xrun [random_ea_sp, htsp, hts.ld (d := Random.oQ) (by decide),
      hts.ld (d := Random.oQLen) (by decide), htq, htl]) rfl) fun u ⟨⟨hum, hup, hul⟩, hku⟩ => ?_
  refine ⟨(hku.gpr (by decide)).trans htsp, hup, hul, hsrc.congrK ?_ (hk.trans hku), hpos, hbound⟩
  rw [hum, hm]
  exact InScr.of_outside (random_clear_outside _ _) (by decide)

private theorem scan_ct : RelCT isa (Two RandomPrepareRegs) Random.significant (fun _ _ => True) := by
  unfold Random.significant
  refine RelCT.seq (two_piece (Ψ := fun p s => ScanPre ⟨p.B, Random.frameBytes, p.Q, p.bytes⟩ s)
    [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_) ?_
  · intro p s ⟨_, hp, hl, hsrc, hpos, hbound⟩
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.mem = s.mem ∧
      t.gpr .rsi = p.Q ∧ t.gpr .rcx = BitVec.ofNat 64 p.bytes.length)
      (by xrun [hp, hl]) rfl) fun t ⟨⟨hm, ht1, ht2⟩, hk⟩ => ?_
    exact ⟨ht1, ht2, hsrc.congrK (by rw [hm]; exact InScr.refl _ _ _) hk, hpos, hbound⟩
  · refine RelCT.seq (significant_ct.mono ?_ (fun _ _ _ => trivial)) ?_
    · intro s t ⟨p, hs, ht⟩
      exact ⟨⟨p.B, Random.frameBytes, p.Q, p.bytes⟩, hs, ht⟩
    · exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
        (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
        (fun _ _ _ => ⟨(), trivial, trivial⟩) (fun _ _ _ => trivial)

theorem random_prepare_ct : RelCT isa (Two RandomPreparePre) Random.prepare (fun _ _ => True) := by
  unfold Random.prepare
  refine RelCT.seq (two_piece (Ψ := RandomPrepareRegs) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => header_ok h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.2.1.trans ht.2.1.symm
  · refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .rsp = p.B) scan_ct ?_) ?_
    · intro p s ⟨hsp, hp, hl, hsrc, hpos, hbound⟩
      exact WP.mono (random_significant_ok hp hl hsrc hpos hbound)
        (fun _ ⟨_, _, _, _, hk⟩ => (hk.gpr (by decide)).trans hsp)
    · apply two_taint [.rsp] ?_ (by taint_decide)
      intro p s t hs ht r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hs.trans ht.symm

end VG.Proof.Dsa.X86_64
