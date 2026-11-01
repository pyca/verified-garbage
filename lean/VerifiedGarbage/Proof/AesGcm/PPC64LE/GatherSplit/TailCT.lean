module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Correct
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.GatherSplit
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: suffix gathering has the shared loop's descriptor-public trace.
/-! # Constant time of gathering the suffix -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.Gather.PPC64LE (GatherPre Eq2 TT rel_seq rel_taint gather_rel desc_word)


theorem first_agree {a b : State} {S D : Addr} {count total : Nat}
    (hd : ∀ j<count*16,a.mem (S+BitVec.ofNat 64 j)=b.mem (S+BitVec.ofNat 64 j))
    (ha : GatherPre a S D count total) (hb : GatherPre b S D count total) (hc : 0<count) :
    a.mem.readW S 64=b.mem.readW S 64 ∧ firstLen a=firstLen b := by
  constructor
  · have hh := desc_word hd (d := 0) (by omega)
    simpa only [BitVec.add_zero] using hh
  · rw [firstLen,firstLen,ha.r7,hb.r7]
    exact desc_word hd (d := 8) (by omega)


theorem tail_rel {a b : State} {S D : Addr} {count total : Nat}
    (hd : ∀ j<count*16,a.mem (S+BitVec.ofNat 64 j)=b.mem (S+BitVec.ofNat 64 j))
    (ha : GatherPre a S D count total) (hb : GatherPre b S D count total) (hc : 0<count)
    (hsp : a.sp=b.sp) :
    RelCT isa (Eq2 a b) (.seq (.block Impl.AesGcm.PPC64LE.GatherSplit.skip) Impl.Gather.PPC64LE.gather) TT := by
  refine rel_seq (rel_taint [.r7] hsp (by simp [ha.r7,hb.r7]) (by taint_decide))
    (skip_ok ha hc) (skip_ok hb hc) fun u v hu hv => ?_
  subst u v
  have hl := (first_agree hd ha hb hc).2
  have ga := tail_pre ha hc
  have gb := tail_pre hb hc
  rw [← hl] at gb
  apply gather_rel (h₁ := ga) (h₂ := gb) (hsp := hsp)
  intro j hj
  change a.mem (S+16#64+BitVec.ofNat 64 j)=b.mem (S+16#64+BitVec.ofNat 64 j)
  rw [Offset.add_add]
  exact hd (16+j) (by omega)

end VG.Proof.AesGcm.PPC64LE.GatherSplit
