module

public import VerifiedGarbage.Proof.Dsa.X86_64.FinishCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ProductCallCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCallCT
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Add
import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import Mathlib.Tactic.Finiteness.Attr

/-! # Retaining public result bindings across arithmetic calls -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem FinishPre.work {p : BPub} {s t : State} {minv : BitVec 64}
    (h : FinishPre p s) (hc : SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv)
    (ht : SubCtx t p.x.B p.x.Z p.x.o p.x.w p.x.wx minv)
    (hf : Frm (off p.x.B p.x.o) (workRanges p.x.wx) s.mem t.mem) (hk : Keep mmRegs s t) :
    FinishPre p t := by
  obtain ⟨⟨_, _, hp, hl⟩, h1, h31, hw, hout, hpre⟩ := h
  exact ⟨⟨minv, ht, (work_parent hc hf (by decide)).trans hp,
    (work_parent hc hf (by decide)).trans hl⟩, h1, h31, hw,
    fun j hj => by rw [hk.2.2]; exact hout j hj, hpre⟩

structure PowerFinishPublic extends PowerCallPublic where
  output : Addr
  outputLen : Nat

def PowerFinishPublic.result (p : PowerFinishPublic) : BPub := ⟨p.x, p.output, p.outputLen⟩

def PowerFinishPre (p : PowerFinishPublic) (s : State) : Prop :=
  PowerCallPre p.toPowerCallPublic s ∧ FinishPre p.result s

theorem powerFinish_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerFinishPre)
    (.seq (Arithmetic.power Sq.mm M.mm arg argLen arg2 arg2Len) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.result s)
    (two_map PowerFinishPublic.toPowerCallPublic (fun _ _ h => h.1) (powerCall_ct M Sq)) ?_)
    (two_map PowerFinishPublic.result (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hf⟩
  exact WP.mono (power_ok M Sq hc p.lower p.width48 p.fits p.upper p.greater p.odd
    hm.modulus hm.inverse (by decide) (by decide) (by decide) (by decide)
    hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
    hep hel he (helen ▸ p.expPositive) (helen ▸ p.expLimit))
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

structure ProductFinishPublic extends ProductCallPublic where
  output : Addr
  outputLen : Nat

def ProductFinishPublic.result (p : ProductFinishPublic) : BPub := ⟨p.x, p.output, p.outputLen⟩

def ProductFinishPre (p : ProductFinishPublic) (s : State) : Prop :=
  PowerCallPre p.toPowerCallPublic s ∧ FinishPre p.result s

theorem productFinish_ct (M : Mont) : RelCT isa (Two ProductFinishPre)
    (.seq (Arithmetic.product M.mm arg argLen arg2 arg2Len) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.result s)
    (two_map ProductFinishPublic.toProductCallPublic (fun _ _ h => h.1) (productCall_ct M)) ?_)
    (two_map ProductFinishPublic.result (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hf⟩
  exact WP.mono (product_ok M hc p.lower p.width48 p.fits p.upper p.greater p.odd
    hm.modulus hm.inverse (by decide) (by decide) (by decide) (by decide)
    hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
    hep hel he (helen ▸ p.expPositive) (helen ▸ p.secondFits))
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

structure ReduceFinishPublic extends ReducePublic where
  output : Addr
  outputLen : Nat

def ReduceFinishPublic.result (p : ReduceFinishPublic) : BPub := ⟨p.bytes.x, p.output, p.outputLen⟩

def ReduceFinishPre (p : ReduceFinishPublic) (s : State) : Prop :=
  ReduceCallPre p.toReducePublic s ∧ FinishPre p.result s

theorem reduceFinish_ct (M : Mont) : RelCT isa (Two ReduceFinishPre)
    (.seq (Arithmetic.reduce M.mm arg argLen) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.result s)
    (two_map ReduceFinishPublic.toReducePublic (fun _ _ h => h.1) (reduceCall_ct M)) ?_)
    (two_map ReduceFinishPublic.result (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨⟨⟨hc, hm⟩, hw⟩, bs, hlen, hp, hl, hs⟩, hf⟩
  exact WP.mono (reduce_ok M hc p.lower hw p.greater255 p.odd hm.modulus hm.inverse
    (by decide) (by decide) hp hl hs (hlen ▸ p.lengthBound))
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

theorem sourceBytes_eq {s : State} {B ptr : Addr} {Z : Nat} {bs : List Byte}
    (h : Src s B Z ptr bs) : Spec.Rsa.bytesAt s.mem ptr bs.length = bs := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · intro i hi hj
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.val i hj

def AddFinishPre (p : ProductFinishPublic) (s : State) : Prop := ProductFinishPre p s ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.base p.baseLen) < p.modulus ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.bytes.ptr p.bytes.len) < p.modulus

theorem addFinish_ct : RelCT isa (Two AddFinishPre)
    (.seq (seqs [Arithmetic.load aX arg argLen, Arithmetic.load aXm arg2 arg2Len,
      VG.Impl.Rsa.X86_64.Crt.addMod aY aX aXm]) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.result s)
    (two_map ProductFinishPublic.toProductCallPublic (fun _ _ h => h.1.1) addCall_ct) ?_)
    (two_map ProductFinishPublic.result (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hf⟩, hbr, her⟩
  rw [← hbl, sourceBytes_eq hb] at hbr
  rw [← helen, sourceBytes_eq he] at her
  exact WP.mono (add_ok hc hm p.lower p.width48 p.fits p.upper
    (by decide) (by decide) (by decide) (by decide)
    hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
    hep hel he (helen ▸ p.expPositive) (helen ▸ p.secondFits) hbr her)
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

end VG.Proof.Dsa.X86_64
