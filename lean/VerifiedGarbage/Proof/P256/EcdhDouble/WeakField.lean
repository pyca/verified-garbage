module
public import VerifiedGarbage.Impl.P256.VerifySparse
public import VerifiedGarbage.Proof.P256.EcdhJac.State
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate

import VerifiedGarbage.Proof.P256.EcdhDouble.LinearField
import VerifiedGarbage.Proof.P256.VerifySparse.Fprog
import VerifiedGarbage.Proof.P256.Linear.WeakAdd

@[expose] public section

namespace VG.Proof.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open EcdhJac (C K M)

def weakMulCode : List Instr := Impl.P256.Linear.weakAdd 864 512 800 ++
  Impl.P256.VerifySparse.op (.mul 896 864 896)

theorem weakMul_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
    (h864 : Sl 864) (h896 : Sl 896) {base : Addr} {s : State} {V : List Nat} {E : Nat→Fin C.p}
    (hm : UnitMod C.p (2^256)) (hi : Inv M base 8192 C.p Sl V E s)
    (h512 : 512∈V) (h800 : 800∈V) (hv896 : 896∈V) (hn : 864∉V) :
    WP isa (.block weakMulCode) s fun t =>
      ProgKeep M base [864,896] s t ∧
      Inv M base 8192 C.p Sl (896::V) (Function.update E 896 ((E 512+E 800)*E 896)) t := by
  rw [weakMulCode,WP.block_append_iff]
  refine WP.mono (Linear.weakAdd_ok hi.scr (hi.lt 512 h512) (hi.lt 800 h800))
    fun u ⟨kr,ko,_,hv⟩ => ?_
  have ku : OpKeep M base 864 s u := linearKeep kr ko
  have iu := inv_keep_unused layout hi h864 hn ku
  have eu : toM C.p (2^256) (wordsVal u.mem base 864 4)=E 512+E 800 := by
    rw [←toM_mod,hv,toM_add]
    exact congrArg₂ (·+·) (hi.val 512 h512) (hi.val 800 h800)
  refine WP.mono (VerifySparse.mulOp_ok (M:=M) (m:=C.p) iu.scr rfl rfl iu.mod aligned.mod
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (iu.lt 896 hv896))
    fun t ⟨kt,hlt,he⟩ => ?_
  refine ⟨⟨fun r hr => (kt.gpr r hr).trans (ku.gpr r hr),kt.rd.trans ku.rd,
    kt.wr.trans ku.wr,kt.sp.trans ku.sp,fun x hx ht => ?_⟩,
    iu.update layout h896 kt hlt ?_⟩
  · rw [kt.mem x (hx 896 (by simp)) ht,ku.mem x (hx 864 (by simp)) ht]
  · change toM C.p (2^256) (wordsVal t.mem base 896 4)=_
    have ee := toM_mul hm he
    change toM C.p (2^256) (wordsVal t.mem base 896 4)=toM C.p (2^256) (wordsVal u.mem base 864 4)*toM C.p (2^256) (wordsVal u.mem base 896 4) at ee
    rw [ee,eu]
    exact congrArg ((E 512+E 800)*·) (iu.val 896 hv896)
end VG.Proof.P256.EcdhDouble
