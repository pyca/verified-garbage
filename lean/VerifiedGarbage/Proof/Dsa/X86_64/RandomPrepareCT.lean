module
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

import VerifiedGarbage.Proof.Dsa.X86_64.SignificantCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignificantCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
import VerifiedGarbage.Proof.Dsa.X86_64.RandomClear
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomClear
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepare
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareFinish
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareFinish
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaPss.Params

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
