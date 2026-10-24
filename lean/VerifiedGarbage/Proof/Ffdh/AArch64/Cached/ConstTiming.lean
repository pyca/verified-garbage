module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Const
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTN
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Initializing an array has no dependence on the value being initialized. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem const_ct (a n : Nat) (ha : a<8)
 {hc hd : VG.Taint.Hint VG.AArch64.Taint.T}
 (head : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW,movi .x9 n,movi .x13 0]) hc).isSome=true)
 (tail : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x8 (sArr a),movi .x7 0]) hd).isSome=true) :
 RelCT isa (Two GoodW) (VG.Impl.Ffdh.AArch64.Cached.const a n) (fun _ _ => True) := by
 unfold VG.Impl.Ffdh.AArch64.Cached.const
 refine RelCT.seq (two_piece (Ψ:=fun L s => SWPre (L,0) s) [.x0] pins_goodW
  head ?_) ?_
 · rintro L s ⟨mi,good,room⟩
   refine WP.mono (WP.keep [.x9,.x12,.x13] (Q:=fun t =>
    t.gpr .x12=BitVec.ofNat 64 L.w ∧ t.gpr .x13=0#64 ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [good.x0,hdr_enc (show sW<32 by decide),good.scr.ld (d:=8*sW)
      (by have := hdr_lt_slot L.w 8 (show sW<32 by decide);omega),good.hdr.hw]
   · rintro t ⟨⟨count,index,mem⟩,rest⟩
     exact ⟨⟨mi,⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,room⟩,count,index⟩
 · exact two_map (fun L => (L,0)) (fun _ _ h => h) (setWord_ct ha tail)

end VG.Proof.Ffdh.AArch64.Cached
