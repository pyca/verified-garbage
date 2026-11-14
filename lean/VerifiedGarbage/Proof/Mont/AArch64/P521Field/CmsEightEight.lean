module

-- separate module: The 8A+8B fused limb/carry instruction replay (cms_eight_eight_ok) costs 2.94s of proof versus 1.29s of imports; DoubleCms38 composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsEightPair
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsLow
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsAndWords
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsHigh
import VerifiedGarbage.Proof.Framework.Block

/-! Eight-limb shifted complement accumulation and the middle AND invariant. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def cmsEightEightClob : List Reg := [.x0,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x15,.x20,.x21,.x22,.x23]
def cmsEightEight (b : Nat) : List Instr := cmsEightFirst b++
  (cmsEightPair 0 (b+16)++(cmsEightPair 1 (b+32)++cmsEightPair 2 (b+48)))

theorem cms_eight_eight_ok {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+64≤size) (hb8 : b%8=0) (hz : s.gpr .x2=0) :
    WP isa (.block (cmsEightEight b)) s fun t =>
      regsVal t cmsLowOut+2^512*((mulHi 8 (t.gpr .x23)).toNat+t.c.toNat)+8*wordsVal s.mem p b 8=
        regsVal s cmsLowOut+8*(2^512-1) ∧
      t.gpr .x23= ~~~word s.mem p (b+56) ∧
      t.gpr .x15=cmsAndWords (cmsMiddleRegs.map t.gpr) ∧ Keeps cmsEightEightClob s t := by
  rw [cmsEightEight,WP.block_append_iff]
  refine WP.mono (cms_eight_first_loaded hp (by omega_arith) hb8 hz) fun u ⟨eu,cu,ku⟩ => ?_
  have hpu := hp.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cms_eight_pair_loaded 0 (by decide) hpu (by omega_arith) (by omega_arith) ((ku.gpr .x2 (by decide)).trans hz)) fun v ⟨ev,cv,mv,kv⟩ => ?_
  have hpv := hpu.of_keeps kv (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cms_eight_pair_loaded 1 (by decide) hpv (by omega_arith) (by omega_arith) ((kv.gpr .x2 (by decide)).trans ((ku.gpr .x2 (by decide)).trans hz))) fun w ⟨ew,cw,mw,kw⟩ => ?_
  have hpw := hpv.of_keeps kw (by decide)
  refine WP.mono (cms_eight_pair_loaded 2 (by decide) hpw (by omega_arith) (by omega_arith) ((kw.gpr .x2 (by decide)).trans ((kv.gpr .x2 (by decide)).trans ((ku.gpr .x2 (by decide)).trans hz)))) fun t ⟨et,ct,mt,kt⟩ => ?_
  have keptV : Keeps [.x0,.x3,.x4,.x5,.x6,.x15,.x20,.x21,.x22,.x23] s v :=
    (ku.mono (by decide)).trans (kv.mono (by decide))
  have keptW : Keeps [.x0,.x3,.x4,.x5,.x6,.x7,.x8,.x15,.x20,.x21,.x22,.x23] s w :=
    (keptV.mono (by decide)).trans (kw.mono (by decide))
  have tailU : Keeps [.x0,.x5,.x6,.x7,.x8,.x9,.x10,.x15,.x20,.x21,.x22,.x23] u t :=
    (kv.mono (by decide)).trans ((kw.mono (by decide)).trans (kt.mono (by decide)))
  have tailV : Keeps [.x0,.x7,.x8,.x9,.x10,.x15,.x20,.x21,.x22,.x23] v t :=
    (kw.mono (by decide)).trans (kt.mono (by decide))
  have new0 : regsVal t [.x3,.x4]=regsVal u [.x3,.x4] := regsVal_congr fun r h =>
    tailU.gpr r ((by decide : ∀r∈[Reg.x3,.x4],r∉[Reg.x0,.x5,.x6,.x7,.x8,.x9,.x10,.x15,.x20,.x21,.x22,.x23]) r h)
  have new1 : regsVal t [.x5,.x6]=regsVal v [.x5,.x6] := regsVal_congr fun r h =>
    tailV.gpr r ((by decide : ∀r∈[Reg.x5,.x6],r∉[Reg.x0,.x7,.x8,.x9,.x10,.x15,.x20,.x21,.x22,.x23]) r h)
  have new2 : regsVal t [.x7,.x8]=regsVal w [.x7,.x8] := regsVal_congr fun r h =>
    kt.gpr r ((by decide : ∀r∈[Reg.x7,.x8],r∉cmsEightPairClob 2) r h)
  have old1 : regsVal u [.x5,.x6]=regsVal s [.x5,.x6] := regsVal_congr fun r h =>
    ku.gpr r ((by decide : ∀r∈[Reg.x5,.x6],r∉cmsEightFirstClob) r h)
  have old2 : regsVal v [.x7,.x8]=regsVal s [.x7,.x8] := regsVal_congr fun r h =>
    keptV.gpr r ((by decide : ∀r∈[Reg.x7,.x8],r∉[Reg.x0,.x3,.x4,.x5,.x6,.x15,.x20,.x21,.x22,.x23]) r h)
  have old3 : regsVal w [.x9,.x10]=regsVal s [.x9,.x10] := regsVal_congr fun r h =>
    keptW.gpr r ((by decide : ∀r∈[Reg.x9,.x10],r∉[Reg.x0,.x3,.x4,.x5,.x6,.x7,.x8,.x15,.x20,.x21,.x22,.x23]) r h)
  simp only [cmsOneR0,cmsOneR1,cmsOnePrev,cmsEightPrev,cmsEightIn1] at ev ew et mv mw mt
  rw [←new0] at eu
  rw [←new1,old1,ku.mem] at ev
  rw [←new2,old2,keptV.mem] at ew
  rw [old3,keptW.mem] at et
  refine ⟨?_,?_,?_,(ku.mono (by decide)).trans ((kv.mono (by decide)).trans
    ((kw.mono (by decide)).trans (kt.mono (by decide))))⟩
  · simp only [cmsLowOut,regsVal,wordsVal,Nat.mul_zero,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,Nat.mul_add] at eu ev ew et ⊢
    omega_using [eu,ev,ew,et]
  · simpa only [cmsEightIn1,Nat.add_assoc,Nat.reduceAdd,keptW.mem] using ct
  · rw [mw,mv] at mt
    rw [←tailU.gpr .x4 (by decide),←tailV.gpr .x5 (by decide),←tailV.gpr .x6 (by decide),
      ←kt.gpr .x7 (by decide),←kt.gpr .x8 (by decide)] at mt
    rw [mt]
    simp only [cmsMiddleRegs,List.map_cons,List.map_nil,cmsAndWords,BitVec.and_allOnes,BitVec.and_assoc]

end VG.Proof.Mont.AArch64.P521Field
