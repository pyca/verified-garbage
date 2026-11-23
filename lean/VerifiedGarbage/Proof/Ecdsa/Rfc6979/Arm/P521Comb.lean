module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.CombGenerator
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P521.ArmComb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.CombGenerator
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.CombLit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P521.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Umaal
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.X25519.Field
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Umaal
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Main
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.Memory32
meta import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Impl.Ecdsa.P521.Arm
meta import VerifiedGarbage.Impl.Ecdsa.P521.Arm

/-! ### `Ecdsa.Rfc6979.Arm.P521`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: P-521

P-521 as the proof's curve (`p521`): scalars of 9 64-bit words and 66
bytes, longer than any hash function's output (`wide`), the order `n` of
521 bits, so that the signature drops 7 bits of a 66-byte digest, and
`vg_ecdsa_p521_sign_k`, proven correct (given the group law) and constant time
against its contract (`coreK` at P-521's sizes, which is
`Proof.Ecdsa.Arm.P521.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm


end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! Deterministic P-521 signing through the generator comb: the comb
signer as RFC 6979's core (`p521CombCurve`), and the contract with its table. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P521

theorem p521_comb_core_pre {u : Bool} {s : State}
    (h : (coreK Impl.Ecdsa.Arm.p521 (combSignK u)).pre s) : combSignPre u s := by
  have hk := constsOk_of_core h
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,-⟩ := h
  exact ⟨⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,fun _ => tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) (by rw [wr]; simp)⟩,hk⟩

theorem p521_comb_core_ctWith (u : Bool)
    (hct : ConstantTime isa (combSignPre u) (combSignPub u) (Impl.Ecdsa.Arm.signP521CombWith u)) : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p521 (combSignK u)).pre
    (coreK Impl.Ecdsa.Arm.p521 (combSignK u)).pub (Impl.Ecdsa.Arm.signP521CombWith u) := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact hct s t ts tt s' t' (p521_comb_core_pre hs) (p521_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy (p521Comb.tsym, p521CombWords) List.mem_cons_self,
      sy ((Impl.Ecdsa.Arm.p521With u).constSym, (Impl.Ecdsa.Arm.p521With u).constTbl)
        (List.mem_append_right _ (List.mem_singleton_self _))⟩ e1 e2

/-- P-521 with the generator comb, with the group law `hL`, calling
`vg_ecdsa_p521_sign_k`, or with `u` its `_umaal` variant. -/
def p521CombCurveWith (hL : Weierstrass.Law Spec.P521.curve) (u : Bool) : RfcCurve where
  E := Impl.Ecdsa.Arm.p521
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  big := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.Arm.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.Arm.P521.p521_sh
  coreN := if u then "vg_ecdsa_p521_sign_k" ++ "_umaal" else "vg_ecdsa_p521_sign_k"
  coreConsts := combSignK u
  coreC := Impl.Ecdsa.Arm.signP521CombWith u
  coreX := by
    intro s hs
    obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := u) (p521_comb_core_pre hs)
    refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
    simp only [coreK,coreSigOf]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  coreCT := p521_comb_core_ctWith u (by cases u; exacts [combSign_ct, combSignU_ct])
  coreStack := by cases u <;> lit_decide
  blk := by rfcT_decide

/-- P-521 with the generator comb, with the group law `hL`. -/
def p521CombCurve (hL : Weierstrass.Law Spec.P521.curve) : RfcCurve := p521CombCurveWith hL false

/-- `p521CombCurve`, calling `vg_ecdsa_p521_sign_umaal`. -/
def p521CombCurveU (hL : Weierstrass.Law Spec.P521.curve) : RfcCurve := p521CombCurveWith hL true

/-! ## With the tables of every hash function with HMAC -/

theorem p521T_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified Arm.target (signCodeT (p521CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 (p521CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.P521.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

theorem p521UT_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified Arm.target (signCodeT (p521CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 (p521CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.P521.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

end VG.Proof.Ecdsa.Rfc6979.Arm
