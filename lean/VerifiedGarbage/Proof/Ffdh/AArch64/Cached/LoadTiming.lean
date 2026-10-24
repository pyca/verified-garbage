module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadArray
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Big-endian array loading reveals pointers and lengths, never the loaded limbs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure LoadPublic where
 workspace : Ws
 src : Addr
 k : Nat

def LoadReady (p : LoadPublic) (s : State) : Prop :=
 GoodW p.workspace s ∧ s.gpr .x1=p.src ∧ s.gpr .x2=BitVec.ofNat 64 p.k

theorem load_ct {a : Nat} (array : a<8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
 (check : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x8 (sArr a),ldh .x12 sW]) hc).isSome=true) :
 RelCT isa (Two LoadReady) (VG.Impl.Ffdh.AArch64.Cached.load a) (fun _ _ =>True) := by
 unfold VG.Impl.Ffdh.AArch64.Cached.load
 refine RelCT.seq (two_piece (Ψ:=fun p s =>s.gpr .x8=off p.workspace.B (slot p.workspace.w a) ∧
  s.gpr .x12=BitVec.ofNat 64 p.workspace.w ∧ s.gpr .x1=p.src ∧ s.gpr .x2=BitVec.ofNat 64 p.k)
  [.x0] (fun _ s t hs ht =>pins_goodW _ s t hs.1 ht.1) check ?_)
  (two_taint [.x8,.x12,.x1,.x2] ?_ (by taint_decide))
 · rintro p s ⟨⟨mi,good,room⟩,ptr,len⟩
   brun [good.x0,hdr_enc (show sArr a<32 by unfold sArr;omega),hdr_enc (show sW<32 by decide),
    header_read good room (show sArr a<32 by unfold sArr;omega),header_read good room (show sW<32 by decide),
    good.hdr.harr a array,good.hdr.hw,ptr,len]
 · intro p s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.1.trans ht.2.2.1.symm
   · exact hs.2.2.2.trans ht.2.2.2.symm

end VG.Proof.Ffdh.AArch64.Cached
