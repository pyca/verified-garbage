module
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded

import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFixedCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFixedCT
meta import VerifiedGarbage.Impl.Rsa.AArch64.Folded
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedTest
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedCounter
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedDispatch
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedExp
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFixed
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedStep
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedCounter
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFixed
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem pExpPre_mem {a : EPub} {s t : State} (h : PExpPre a s)
    {rs : List Reg} (hm : t.mem = s.mem) (hk : Keep rs s t) (h0 : .x0 ∉ rs) :
    PExpPre a t := by
  obtain ⟨X,x,hc,hf,he,hl,hL,hs⟩ := h
  refine ⟨X,x,hc.mem hm hk h0,hf,by rw [hm]; exact he,by rw [hm]; exact hl,hL,?_⟩
  exact ⟨hs.1,hs.2.1,by rw [hk.rd,hk.wr]; exact hs.2.2.1,
    by rw [hm]; exact hs.2.2.2.1,hs.2.2.2.2⟩

theorem pins_exp : Pins PExpPre [.x0] := by
  intro a s t ⟨_,_,hs,_⟩ ⟨_,_,ht,_⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  rw [hs.good.x0,ht.good.x0]

theorem lengthTest_ct : RelCT isa (Two PExpPre) (.block Folded.lengthTest)
    (Two fun a s => PExpPre a s ∧ isa.eval (.zero .x .x3) s = some (decide (a.len=3))) := by
  refine two_piece [.x0] pins_exp (by taint_decide) ?_
  intro a s h
  have orig := h
  obtain ⟨X,x,hc,hf,he,hl,hL,hs⟩ := h
  exact WP.mono (lengthTest_ok hc.good hf.1 hs.2.1 hl) fun t ⟨ht,hm,hk⟩ =>
    ⟨pExpPre_mem orig hm hk (by decide),ht⟩

/-- The byte addresses are derived solely from the public exponent pointer. -/
theorem bytesTest_ct : RelCT isa (Two PExpPre) (.block Folded.bytesTest) (fun _ _ => True) := by
  change RelCT isa (Two PExpPre) (.block ([ldh .x8 sE] ++
    [.ldrb .x3 .x8 0,.subImm .x .x3 .x3 1,.ldrb .x4 .x8 1,
     .logic .orr .x .x3 .x3 .x4,.ldrb .x4 .x8 2,.subImm .x .x4 .x4 1,
     .logic .orr .x .x3 .x3 .x4])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun (a : EPub) t => t.gpr .x8 = a.ep)
    [.x0] pins_exp (by taint_decide) ?_)
    (two_taint [.x8] (fun a s t hs ht r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact hs.trans ht.symm) (by taint_decide))
  rintro a s ⟨_,_,hc,hf,he,_⟩
  have bound : 8*sE+8 ≤ a.L.Z := by
    have := hdr_lt_slot a.L.w 8 (show sE < 32 by decide); have := hf.1; omega
  brun [hc.good.x0,hdr_enc (show sE < 32 by decide),hc.good.scr.ld bound,he]

theorem bytesTest_fw (a : EPub) (s : State) (h : PExpPre a s) (h3 : a.len=3) :
    WP isa (.block Folded.bytesTest) s fun t => PExpPre a t ∧
      isa.eval (.zero .x .x3) t = some (decide (Spec.Rsa.os2ip a.eb=65537)) := by
  have orig := h
  obtain ⟨X,x,hc,hf,he,hl,hL,hs⟩ := h
  have hel : a.eb.length=3 := hs.1.trans h3
  have heb := List.eq_getElem_of_length_eq_three a.eb hel
  refine WP.mono (bytesTest_ok hc.good hf.1 he (a.eb[0]'(by omega)) (a.eb[1]'(by omega)) (a.eb[2]'(by omega)) (by rw [← h3]; exact hs.2.2.1)
    (by simpa only [BitVec.add_zero] using hs.bytes 0 (by omega))
    (hs.bytes 1 (by omega)) (hs.bytes 2 (by omega))) fun t ⟨ht,hm,hk⟩ => ?_
  refine ⟨pExpPre_mem orig hm hk (by decide),?_⟩
  simpa only [← heb] using ht

theorem fastLoop_ct (M : Mont) :
    RelCT isa (Two PExpPre) (Folded.fastLoop M.mm) (fun _ _ => True) := by
  unfold Folded.fastLoop
  refine RelCT.seq lengthTest_ct (two_ite (fun _ _ _ hs ht => by rw [hs.2,ht.2]) ?_ ?_)
  · refine RelCT.seq (two_post (Ψ := fun a s => PExpPre a s ∧ isa.eval (.zero .x .x3) s = some (decide (Spec.Rsa.os2ip a.eb=65537))) (two_map id (fun _ _ h => h.1.1) bytesTest_ct) ?_) ?_
    · intro a s h
      have eq := h.2
      rw [h.1.2] at eq
      exact bytesTest_fw a s h.1.1 (by simpa using eq)
    · refine two_ite (fun _ _ _ hs ht => by rw [hs.2,ht.2]) ?_ ?_
      · exact two_map (fun a : EPub => (⟨a.L,a.N⟩ : PublicData))
          (fun _ _ ⟨⟨⟨X,x,hc,hf,_⟩,_⟩,_⟩ =>
            ⟨X,x,hc,⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩,hf.2.2.2.2.1,hf.2.2.2.2.2⟩)
          (fixedLoop_ct M)
      · exact (two_map id (fun _ _ h => h.1.1) (pExpLoop_ct (M := M))).mono
          (fun _ _ h => h) (fun _ _ _ => trivial)
  · exact (two_map id (fun _ _ h => h.1.1) (pExpLoop_ct (M := M))).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.AArch64.FoldedPublic
