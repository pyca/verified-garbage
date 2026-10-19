module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawPublic
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomRangeCT
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCheck
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawPublic
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomRangeCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
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
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
import VerifiedGarbage.Proof.Dsa.X86_64.Failure
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.RandomBorrow
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyWhole
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDraw
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.Zero
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.X86_64.Failure
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomBorrow
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCandidate
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyWhole
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDraw
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCheck
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
meta import VerifiedGarbage.Proof.Dsa.Zero
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

/-! The copy-and-check prefix leaks only public addresses and widths. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def RandomDrawPublic.range (p : RandomDrawPublic) : RandomRangePublic :=
  ⟨p.B, p.Q + BitVec.ofNat 64 (p.qBytes.length - p.width), p.qBytes.length, p.width⟩

def RandomDrawCheckMid (p : RandomDrawPublic) (s : State) : Prop :=
  RandomRangePre p.range s ∧ word s.mem p.B Random.oUsed = BitVec.ofNat 64 p.used

theorem random_draw_copy_ct : RelCT isa (Two RandomDrawFullPre) Random.copy (fun _ _ => True) := by
  refine two_map (fun p => (⟨p.B, p.R, p.used, p.qBytes.length, p.width⟩ : RandomCopyPublic)) ?_ random_copy_ct
  intro p s ⟨⟨rand, hlen, m, hr⟩, hfull⟩
  have hn := VG.Proof.Dsa.significant_fits p.qBytes
  have hq := p.qlen
  have hp := p.positive
  refine ⟨hr.scr, hr.sp, hr.rand, hr.usedWord, hr.qLen, hr.width, hp, by dsimp only [RandomDrawPublic.width]; omega, ?_, ?_⟩
  · have hh := hr.randSrc.rd p.used (by dsimp only [RandomDrawPublic.context]; rw [hlen]; dsimp only [RandomDrawPublic.width] at hfull; omega)
    exact hh
  · change InRegions s.wr (off p.B Random.oNonce + BitVec.ofNat 64 p.qBytes.length - BitVec.ofNat 64 p.width) 1
    unfold RandomDrawPublic.width
    rw [random_nonce_addr p.B hn]
    exact hr.scr.st8 (by dsimp only [Random.frameBytes, RandomDrawPublic.width]; omega)

private theorem copy_mid {p : RandomDrawPublic} {s : State} (h : RandomDrawFullPre p s) :
    WP isa Random.copy s (RandomDrawCheckMid p) := by
  obtain ⟨⟨rand, hlen, m, hr⟩, hfull⟩ := h
  have hn := VG.Proof.Dsa.significant_fits p.qBytes
  have hq := p.qlen
  refine WP.mono (random_copy_draw_ok hr.scr hr.sp hr.rand hr.usedWord hr.width hr.qLen hr.mask
    hr.randSrc hq p.positive (by dsimp only [RandomDrawPublic.context]; rw [hlen]; exact hfull)) fun t ⟨_, _, _, _, hf, hk⟩ => ?_
  dsimp only [RandomDrawPublic.context] at hf
  have hf' : Outside p.B 200 32 s.mem t.mem := hf.mono (by omega) (by omega)
  have hw (d : Nat) (hd : d + 8 ≤ 200) : word t.mem p.B d = word s.mem p.B d :=
    hf'.word (Or.inl hd) (by omega)
  exact ⟨⟨hr.scr.congr hk.2.2, (hk.gpr (by decide)).trans hr.sp,
    (hw _ (by decide)).trans hr.qLen, (hw _ (by decide)).trans hr.width,
    (hw _ (by decide)).trans hr.q⟩, (hw _ (by decide)).trans hr.usedWord⟩

private theorem used_range {p : RandomDrawPublic} {s : State} (h : RandomDrawCheckMid p s) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oUsed)),
      .alu .add .rax (.mem (Random.sp Random.oWidth)), .store (Random.sp Random.oUsed) .rax]) s
      (RandomRangePre p.range) := by
  obtain ⟨⟨hs, hsp, hl, hn, hq⟩, hu⟩ := h
  refine WP.mono (random_used_ok hs hsp hu hn) fun t ⟨hm, hk⟩ => ?_
  have hw (d : Nat) (hd : d + 8 ≤ 144 ∨ 152 ≤ d) (hb : d + 8 ≤ 2 ^ 64) :
      word t.mem p.B d = word s.mem p.B d := by
    rw [hm]
    exact (writeW_outside _ p.B _ (by decide)).word hd hb
  exact ⟨hs.congr hk.2.2, (hk.gpr (by decide)).trans hsp,
    (hw _ (by decide) (by decide)).trans hl,
    (hw _ (by decide) (by decide)).trans hn,
    (hw _ (by decide) (by decide)).trans hq⟩

theorem random_drawCheck_ct : RelCT isa (Two RandomDrawFullPre) randomDrawCheck (fun _ _ => True) := by
  unfold randomDrawCheck
  refine RelCT.seq (two_post random_draw_copy_ct (fun _ _ h => copy_mid h)) ?_
  refine RelCT.seq (two_piece (Ψ := fun p s => RandomRangePre p.range s) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => used_range h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.1.2.1.trans ht.1.2.1.symm
  · exact two_map RandomDrawPublic.range (fun _ _ h => h) random_inRange_ct

end VG.Proof.Dsa.X86_64
