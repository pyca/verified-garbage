module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
meta import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombGenerator
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Main
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombGenerator
meta import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.NatPairs
import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.Arm
public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Proof.Weierstrass.PointContract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.NatPairs
meta import Mathlib.Logic.Function.Basic
meta import VerifiedGarbage.Spec.Ecdsa.Secp256k1
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.Arm
meta import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! ### `Ecdsa.Arm.Secp256k1.CombContract`, which only this module used -/

section

/-! The existing ECDSA contract with its read-only comb table. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm

/-- The tables signing reads: the comb's, and the setup's constants. -/
abbrev combSignK (u : Bool) : List (String × List (BitVec 64)) := secp256k1CombConsts ++ (secp256k1With u).constsK

def combSignPre (u : Bool) (s : State) : Prop :=
  Pre (secp256k1With u) s (constRegs (combSignK u) s) ∧ ConstsOk (combSignK u) 0 s

end VG.Proof.Ecdsa.Arm.Secp256k1

end

end

/-! ### `Ecdsa.Arm.Secp256k1.CombCT`, which only this module used -/

section

/-! The generator comb remains constant time inside the complete signing function. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm

def combSignPub (u : Bool) (s t : State) : Prop :=
  signArm.pub s t ∧ s.syms secp256k1Comb.tsym=t.syms secp256k1Comb.tsym ∧ s.syms (secp256k1With u).constSym=t.syms (secp256k1With u).constSym

theorem combSign_agree {u : Bool} {s t : State} (hs : combSignPre u s) (ht : combSignPre u t)
    (pub : combSignPub u s t) :
    VG.Arm.Taint.Agree τ₁ s t ∧ ∀ n ∈ [secp256k1Comb.tsym,(secp256k1With u).constSym], s.syms n = t.syms n :=
  ⟨agree₁ (agree₀ hs.1 ht.1 pub.1),fun n hn => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl
    exacts [pub.2.1,pub.2.2]⟩

theorem combSign_ct : ConstantTime isa (combSignPre false) (combSignPub false) signSecp256k1Comb :=
  VG.Taint.constantTime (A := taintSym [secp256k1Comb.tsym,(secp256k1With false).constSym]) τ₁
    (fun _ _ hs ht pub => combSign_agree hs ht pub) (by native_taint_decide)

theorem combSignU_ct : ConstantTime isa (combSignPre true) (combSignPub true) signSecp256k1CombU :=
  VG.Taint.constantTime (A := taintSymU [secp256k1Comb.tsym,(secp256k1With true).constSym]) τ₁
    (fun _ _ hs ht pub => combSign_agree hs ht pub) (by taint_decide)

end VG.Proof.Ecdsa.Arm.Secp256k1

end

end

/-! ### `Ecdsa.Arm.Secp256k1.CombMain`, which only this module used -/

section

/-! Signing through the shared pipeline with the checked fixed-base comb. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb

theorem combSign_ok (hC : Law Spec.Secp256k1.curve) {u : Bool} {s₀ : State} (hp : combSignPre u s₀) :
    WP isa (signSecp256k1CombWith u) s₀ fun t => SignKeep (secp256k1With u) s₀ t ∧ SignPost (secp256k1With u) s₀ t := by
  have member : (secp256k1Comb.tsym,secp256k1CombWords)∈combSignK u := List.mem_cons_self
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show scR s₀∈s₀.wr by rw [hp.1.wr]; simp)
  exact signWith_ok (secp256k1With_ok u) hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

end VG.Proof.Ecdsa.Arm.Secp256k1

end

end

/-! ### `Ecdsa.Rfc6979.Arm.Secp256k1`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: secp256k1

secp256k1 as the proof's curve (`secp256k1`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_secp256k1_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at secp256k1's sizes, which is `Proof.Ecdsa.Arm.Secp256k1.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem secp256k1_nBits : Spec.Ecdsa.nBits Spec.Secp256k1.curve = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.Secp256k1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Secp256k1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! RFC 6979 calls the same comb signer as the raw signing API. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.Secp256k1

theorem comb_core_pre {u : Bool} {s : State}
    (h : (coreK Impl.Ecdsa.Arm.secp256k1 (combSignK u)).pre s) : combSignPre u s := by
  have hk := constsOk_of_core h
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,-⟩ := h
  exact ⟨⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,fun _ => tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) (by rw [wr]; simp)⟩,hk⟩

theorem comb_core_ctWith (u : Bool)
    (hct : ConstantTime isa (combSignPre u) (combSignPub u) (Impl.Ecdsa.Arm.signSecp256k1CombWith u)) : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.secp256k1 (combSignK u)).pre
    (coreK Impl.Ecdsa.Arm.secp256k1 (combSignK u)).pub (Impl.Ecdsa.Arm.signSecp256k1CombWith u) := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact hct s t ts tt s' t' (comb_core_pre hs) (comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy (secp256k1Comb.tsym, secp256k1CombWords) List.mem_cons_self,
      sy ((Impl.Ecdsa.Arm.secp256k1With u).constSym, (Impl.Ecdsa.Arm.secp256k1With u).constTbl)
        (List.mem_append_right _ (List.mem_singleton_self _))⟩ e1 e2

/-- secp256k1 with the generator comb, with the group law `hL`, calling
`vg_ecdsa_secp256k1_sign_k`, or with `u` its `_umaal` variant. -/
def secp256k1CombCurveWith (hL : Weierstrass.Law Spec.Secp256k1.curve) (u : Bool) : RfcCurve where
  E := Impl.Ecdsa.Arm.secp256k1
  inst := Spec.Ecdsa.Secp256k1.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, secp256k1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.Secp256k1.curve = 0; rw [secp256k1_nBits]
  coreN := if u then "vg_ecdsa_secp256k1_sign_k" ++ "_umaal" else "vg_ecdsa_secp256k1_sign_k"
  coreConsts := combSignK u
  coreC := Impl.Ecdsa.Arm.signSecp256k1CombWith u
  coreX := by
    intro s hs
    obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := u) (comb_core_pre hs)
    refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
    simp only [coreK,coreSigOf]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  coreCT := comb_core_ctWith u (by cases u; exacts [combSign_ct, combSignU_ct])
  coreStack := by cases u <;> lit_decide
  blk := by rfcT_decide

/-- secp256k1 with the generator comb, with the group law `hL`. -/
def secp256k1CombCurve (hL : Weierstrass.Law Spec.Secp256k1.curve) : RfcCurve := secp256k1CombCurveWith hL false

/-- `secp256k1CombCurve`, calling `vg_ecdsa_secp256k1_sign_umaal`. -/
def secp256k1CombCurveU (hL : Weierstrass.Law Spec.Secp256k1.curve) : RfcCurve := secp256k1CombCurveWith hL true

/-! ## With the tables of every hash function with HMAC -/

theorem secp256k1T_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target (signCodeT (secp256k1CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 (secp256k1CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.Secp256k1.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

theorem secp256k1UT_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target (signCodeT (secp256k1CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 (secp256k1CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.Secp256k1.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

end VG.Proof.Ecdsa.Rfc6979.Arm
