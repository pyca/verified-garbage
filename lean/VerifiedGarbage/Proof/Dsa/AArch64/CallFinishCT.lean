module

public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.AArch64.Add
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Core
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Impl.Dsa.Layout
meta import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInitCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInitCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Add
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
public import VerifiedGarbage.Proof.Dsa.AArch64.PowerCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.PowerCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceByte
public import VerifiedGarbage.Proof.Dsa.AArch64.PowerCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceByte
meta import VerifiedGarbage.Proof.Dsa.AArch64.PowerCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT

/-! ### `Dsa.AArch64.ReduceByteCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.ReduceStepCT`, which only this module used -/

section

/-! # Timing of the multiply-and-add reduction step -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Impl.Dsa.AArch64

/-- The accumulator is reduced; its value need not agree between runs. -/
theorem reduceStep_ct (M : Mont) : RelCT isa (Two (Reduced [aY]))
    (Arithmetic.reduceStep M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceStep
  refine RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aY] (by decide) (by decide)) ?_
  exact two_map (fun p : ProductPublic => p.layout.ws)
    (fun p _ h => ⟨_, h.1.good, p.fits⟩)
    (addMod_ct (by decide) (by decide) (by decide) (by taint_decide))

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ReduceReadCT`, which only this module used -/

section

/-! # Constant-time reads of secret reduction input bytes -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ReduceReadPublic where
  layout : Lay
  pointer : Addr

def ReduceReadPre (p : ReduceReadPublic) (s : State) : Prop :=
  GoodL p.layout s ∧ word s.mem p.layout.B (8 * Crt.sSrc) = p.pointer ∧
  InRegions (s.rd ++ s.wr) p.pointer 1

def ReduceReadHead (p : ReduceReadPublic) (s : State) : Prop :=
  GoodL p.layout s ∧ s.gpr .x1 = p.pointer ∧ InRegions (s.rd ++ s.wr) p.pointer 1

def ReduceReadStore (p : ReduceReadPublic) (s : State) : Prop :=
  s.gpr .x0 = p.layout.B ∧ s.gpr .x1 = p.pointer ∧
  s.gpr .x8 = off p.layout.B (slot p.layout.w aX)

theorem reduceRead_ct : RelCT isa (Two ReduceReadPre) (.block Arithmetic.reduceRead)
    (fun _ _ => True) := by
  change RelCT isa (Two ReduceReadPre) (.block (
    ([ldh .x1 Crt.sSrc] : List Instr) ++
    ([.ldrb .x3 .x1 0, ldh .x8 (sArr aX)] : List Instr) ++
    [st .x3 .x8, .addImm .x .x1 .x1 1, sth .x1 Crt.sSrc])) _
  rw [List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := ReduceReadHead) [.x0]
    (fun p s t hs ht => pins_good p.layout s t hs.1 ht.1) (by taint_decide) ?_) ?_
  · intro p s ⟨hg, hp, hr⟩
    refine WP.mono (WP.keep [.x1] (Q := fun t => t.gpr .x1 = p.pointer ∧ t.mem = s.mem)
      ?_ rfl rfl rfl) fun t ⟨⟨hsi, hm⟩, hk⟩ =>
      ⟨⟨⟨hg.1.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.1.x0, hm ▸ hg.1.hdr⟩, hg.2⟩,
        hsi, by simpa only [hk.rd, hk.wr] using hr⟩
    brun [hg.1.x0, hdr_enc (show Crt.sSrc < 32 by decide), hp,
      hg.1.scr.ld (show 8 * Crt.sSrc + 8 ≤ p.layout.Z by
        have := hdr_lt_slot p.layout.w 8 (show Crt.sSrc < 32 by decide); have := hg.2; omega_arith)]
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := ReduceReadStore) [.x0, .x1]
    (pins_of (fun p r => if r = .x0 then p.layout.B else p.pointer) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.x0
      · exact h.2.1)) (by taint_decide) ?_) ?_
  · intro p s ⟨hg, hsi, hr⟩
    refine WP.mono (WP.keep [.x3, .x8] (Q := fun t =>
      t.gpr .x8 = off p.layout.B (slot p.layout.w aX)) ?_ rfl rfl rfl)
      fun t ⟨hbx, hk⟩ => ⟨(hk.gpr .x0 (by decide)).trans hg.1.x0,
        (hk.gpr .x1 (by decide)).trans hsi, hbx⟩
    brun [hsi, hr, hg.1.x0, hdr_enc (show sArr aX < 32 by decide),
      hg.1.hdr.harr aX (by decide),
      hg.1.scr.ld (show 8 * sArr aX + 8 ≤ p.layout.Z by
        have := hdr_lt_slot p.layout.w 8 (show sArr aX < 32 by decide); have := hg.2; omega_arith)]
  exact two_taint [.x0, .x1, .x8]
    (pins_of (fun p r => if r = .x0 then p.layout.B else if r = .x1 then p.pointer else
      off p.layout.B (slot p.layout.w aX)) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of one complete streaming reduction byte -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ReducePublic extends PowerPublic where
  greater255 : 255 < modulus
  lengthBound : bytes.len < 2 ^ 64

/-- Source bytes and the accumulator are secret; only their address and
length appear in the public descriptor. -/
def ReduceBytePre (p : ReducePublic) (s : State) : Prop :=
  ∃ (bs : List Byte) (acc : Nat), bs.length = p.bytes.len ∧ 0 < bs.length ∧
    ReduceState s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx
      p.modulus p.minv p.bytes.ptr bs acc

def ReduceArithmeticPre (p : ReducePublic) (s : State) : Prop :=
  SubCtx s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx p.minv ∧
  ModCtx s (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx 8) p.bytes.x.wx p.minv p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aY) p.bytes.x.wx < p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aX) p.bytes.x.wx < p.modulus

theorem reduceRead_arithmetic {p : ReducePublic} {s : State} (h : ReduceBytePre p s) :
    WP isa (.block Arithmetic.reduceRead) s (ReduceArithmeticPre p) := by
  obtain ⟨bs, acc, hlen, hpos, h⟩ := h
  have hr := h.source.rd 0 hpos
  simp only [BitVec.add_zero] at hr
  refine WP.mono (reduceRead_context h.ctx h.modulus (by have := p.lower; omega_using [this])
    h.pointer hr h.high) fun t ⟨hc, hm, hbyte, harr, _⟩ => ?_
  refine ⟨hc, hm, ?_, ?_⟩
  · rw [harr aY (by decide) (by decide), h.value]
    exact h.reduced
  · rw [hbyte]
    have := (s.mem p.bytes.ptr).isLt
    have := p.greater255
    omega_using [this]

theorem reduceArithmetic_ct (M : Mont) : RelCT isa (Two ReduceArithmeticPre)
    (Arithmetic.reduceStep M.mm) (fun _ _ => True) :=
  two_map (fun p : ReducePublic => p.toPowerPublic.product) (fun _ _ h =>
    ⟨h.2.1, fun j hj => by obtain rfl := List.mem_singleton.mp hj; exact h.2.2.1⟩) (reduceStep_ct M)

/-- Only the header address is needed for the counter block's trace.
The loop proof separately establishes that the resulting flag is public. -/
theorem reduceByte_ct (M : Mont) : RelCT isa (Two ReduceBytePre)
    (Arithmetic.reduceByte M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceByte seqs
  refine RelCT.seq (two_post (Ψ := ReduceArithmeticPre)
    (two_map (fun p : ReducePublic =>
      (⟨p.toPowerPublic.product.layout, p.bytes.ptr⟩ : ReduceReadPublic)) ?_ reduceRead_ct)
    (fun _ _ h => reduceRead_arithmetic h)) ?_
  · intro p s ⟨bs, acc, hlen, hpos, h⟩
    refine ⟨⟨h.ctx.good, Nat.le_refl _⟩, h.pointer, ?_⟩
    simpa using h.source.rd 0 hpos
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .x0 = off p.bytes.x.B p.bytes.x.o)
    (reduceArithmetic_ct M) ?_) ?_
  · intro p s ⟨hc, hm, hred, hb⟩
    unfold Arithmetic.reduceStep
    refine WP.seq (WP.mono (mont_step M hm (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega_arith) (by unfold MmUse; decide) hred)
      fun u ⟨hmu, hlt, _, hf, _⟩ => ?_)
    have hxu := (hf.wv_of_not_mem (show aX < 8 by decide) (by decide) hc.good.scr.nowrap)
    refine WP.mono (addMod_ok hmu.good.scr hmu.good.x0 hmu.good.hdr (Nat.le_refl _)
      p.lower (by have := p.fits; have := p.upper; omega_arith)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hmu.modulus]; exact hlt)
      (by rw [hmu.modulus, hxu]; exact hb)) fun t ⟨_, _, hk⟩ =>
        (hk.gpr .x0 (by decide)).trans hmu.good.x0
  exact two_taint [.x0] (pins_x0B (fun p => off p.bytes.x.B p.bytes.x.o) (fun _ _ h => h))
    (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ProductCallCT`, which this module and modules that import it used -/

section

/-! # Constant time of the complete ordinary modular product -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Both product inputs fit the workspace. The shared call description
contains public pointers and lengths, never operand values. -/
structure ProductCallPublic extends PowerCallPublic where
  secondFits : (bytes.len + 7) / 8 ≤ bytes.x.wx

/-- Loading either input leaves the public call description and prepared
Montgomery constants intact. -/
theorem productCall_load {p : ProductCallPublic} {s : State}
    {a sp sl : Nat} {ptr : Addr} {bs : List Byte}
    (ha : a < 8) (han : a ≠ aN) (hao : a ≠ aOne) (har : a ≠ aR2)
    (hsp : sp < 32) (hsl : sl < 32)
    (h : PowerCallPrepared p.toPowerCallPublic s)
    (hp : word s.mem p.x.B (8 * sp) = ptr)
    (hl : word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hs : Src s p.x.B p.x.Z ptr bs) (h1 : 1 ≤ bs.length)
    (hfit : (bs.length + 7) / 8 ≤ p.x.wx) :
    WP isa (Arithmetic.load a sp sl) s (PowerCallPrepared p.toPowerCallPublic) := by
  obtain ⟨⟨hc, hm, hb⟩, hone, hr2⟩ := h
  have hlen : bs.length < 2 ^ 31 := by
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hfit, hw48]
  refine WP.mono (load_ok hc p.lower p.fits p.upper ha hsp hsl hp hl hs h1 hlen hfit)
    fun t ⟨hct, _, hf, hk⟩ => ?_
  have hfa : Arrays (off p.x.B p.x.o) p.x.wx [a] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self a) hf (Nat.le_refl _) (Nat.le_refl _)
  have hz := hc.good.scr.nowrap
  have hmn : aN ∉ [a] := by simpa using Ne.symm han
  have hmo : aOne ∉ [a] := by simpa using Ne.symm hao
  have hmr : aR2 ∉ [a] := by simpa using Ne.symm har
  have hmt : ModCtx t (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus := by
    refine ⟨hct.good, (hfa.wv_of_not_mem (by decide) hmn hz).trans hm.modulus, ?_⟩
    rw [hfa.word0_of_not_mem (by decide) hmn hz (by have := p.lower; omega_using [h1, hfit])]
    exact hm.inverse
  exact ⟨⟨hct, hmt, hb.frame hc (arrays_work hfa (by intro j hj; obtain rfl := List.mem_singleton.mp hj; exact ha)) hk⟩,
    (hfa.wv_of_not_mem (by decide) hmo hz).trans hone,
    (hfa.wv_of_not_mem (by decide) hmr hz).trans hr2⟩

theorem productCall_ct (M : Mont) :
    RelCT isa (Two (fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic))
      (Arithmetic.product M.mm arg argLen arg2 arg2Len) (fun _ _ => True) := by
  unfold Arithmetic.product seqs
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPrepared p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => p.toPowerPublic.product)
      (fun p _ h => ⟨h.2.1, p.width48, p.greater, p.odd⟩) (constants_ct M))
    (fun _ _ h => powerCall_prepare M h)) ?_
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPrepared p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => (⟨p.x, p.base, p.baseLen⟩ : BPub)) ?_
      (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨⟨hc, _, bb, _, hp, hl, _, _, hbl, _, hb, _⟩, _⟩
    refine ⟨p.minv, bb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.basePositive, ?_, hbl ▸ p.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  · intro p s h
    obtain ⟨bb, _, hp, hl, _, _, hbl, _, hb, _⟩ := h.1.2.2
    exact productCall_load (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPrepared p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => p.bytes) ?_
      (loadArr_ct (j := aXm) (sp := arg2) (sl := arg2Len) (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨⟨hc, _, _, eb, _, _, hp, hl, _, hel, _, hb⟩, _⟩
    refine ⟨p.minv, eb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hel, hb, hel ▸ p.expPositive, ?_, hel ▸ p.secondFits⟩
    have hbw : (eb.length + 7) / 8 ≤ p.x.wx := hel ▸ p.secondFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  · intro p s h
    obtain ⟨_, eb, _, _, hp, hl, _, hel, _, hb⟩ := h.1.2.2
    exact productCall_load (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h hp hl hb (hel ▸ p.expPositive) (hel ▸ p.secondFits)
  exact two_map (fun p : ProductCallPublic => p.toPowerPublic.product) (fun p s ⟨⟨_, hm, _⟩, hone, hr2⟩ => by
    refine ⟨hm, ?_⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · dsimp only [PowerPublic.product]
      rw [hr2]
      exact Nat.mod_lt _ (by have := p.greater; omega_using [this])
    · dsimp only [PowerPublic.product]
      rw [hone]
      exact p.greater) (productCore_ct M)

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.AddCallCT`, which only this module used -/

section

/-! # Constant time of loading and adding DSA scalars -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem callLoad_context {p : PowerCallPublic} {s : State} {a sp sl : Nat}
    {ptr : Addr} {bs : List Byte} (ha : a < 8) (han : a ≠ aN) (hsp : sp < 32) (hsl : sl < 32)
    (h : PowerCallPre p s) (hp : word s.mem p.x.B (8 * sp) = ptr)
    (hl : word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hs : Src s p.x.B p.x.Z ptr bs) (h1 : 1 ≤ bs.length)
    (hfit : (bs.length + 7) / 8 ≤ p.x.wx) :
    WP isa (Arithmetic.load a sp sl) s (PowerCallPre p) := by
  have hlen : bs.length < 2 ^ 31 := by
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hfit, hw48]
  exact WP.mono (load_mod_ok h.1 h.2.1 p.lower p.fits p.upper ha han hsp hsl hp hl hs h1 hlen hfit)
    fun t ⟨hc, hm, _, _, hf, hk⟩ => ⟨hc, hm, h.2.2.frame h.1 hf hk⟩

theorem addCall_ct :
    RelCT isa (Two (fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic))
      (seqs [Arithmetic.load aX arg argLen, Arithmetic.load aXm arg2 arg2Len, Crt.addMod aY aX aXm])
      (fun _ _ => True) := by
  unfold seqs
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => (⟨p.x, p.base, p.baseLen⟩ : BPub)) ?_
      (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨hc, _, bb, _, hp, hl, _, _, hbl, _, hb, _⟩
    refine ⟨p.minv, bb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.basePositive, ?_, hbl ▸ p.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  · intro p s h
    obtain ⟨bb, _, hp, hl, _, _, hbl, _, hb, _⟩ := h.2.2
    exact callLoad_context (by decide) (by decide) (by decide) (by decide)
      h hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => p.bytes) ?_
      (loadArr_ct (j := aXm) (sp := arg2) (sl := arg2Len) (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨hc, _, _, eb, _, _, hp, hl, _, hel, _, hb⟩
    refine ⟨p.minv, eb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hel, hb, hel ▸ p.expPositive, ?_, hel ▸ p.secondFits⟩
    have hbw : (eb.length + 7) / 8 ≤ p.x.wx := hel ▸ p.secondFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  · intro p s h
    obtain ⟨_, eb, _, _, hp, hl, _, hel, _, hb⟩ := h.2.2
    exact callLoad_context (by decide) (by decide) (by decide) (by decide)
      h hp hl hb (hel ▸ p.expPositive) (hel ▸ p.secondFits)
  exact two_map (fun p : ProductCallPublic => p.x.ws)
    (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩)
    (addMod_ct (by decide) (by decide) (by decide) (by taint_decide))

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ReduceCallCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.ReduceLoopCT`, which only this module used -/

section

/-! # Constant time of nonempty streaming reduction -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ReducePublic.remaining (p : ReducePublic) (j : Nat) : ReducePublic :=
  { p with bytes := { p.bytes with ptr := p.bytes.ptr + BitVec.ofNat 64 j, len := p.bytes.len - j }
           lengthBound := Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.lengthBound }

def ReduceLoopPre (p : ReducePublic) (j : Nat) (s : State) : Prop :=
  ∃ (bs : List Byte) (acc : Nat), bs.length = p.bytes.len - j ∧
    ReduceState s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx
      p.modulus p.minv (p.bytes.ptr + BitVec.ofNat 64 j) bs acc

theorem reduceLoop_step (M : Mont) {p : ReducePublic} {j : Nat} {s : State}
    (hj : j < p.bytes.len) (h : ReduceLoopPre p j s) :
    WP isa (Arithmetic.reduceByte M.mm) s fun t =>
      isa.eval (.nonzero .x .x3) t = some (decide (j + 1 < p.bytes.len)) ∧ ReduceLoopPre p (j + 1) t := by
  obtain ⟨bs, acc, hlen, h⟩ := h
  cases bs with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons b bs =>
    refine WP.mono (reduceByte_ok M h p.lower (by have := p.fits; have := p.upper; omega_arith)
      p.greater255 p.odd (by have := p.lengthBound; omega_using [hlen, this]))
      fun t ⟨ht, hz, _, _⟩ => ?_
    have hpos : p.bytes.ptr + BitVec.ofNat 64 j + 1 = p.bytes.ptr + BitVec.ofNat 64 (j + 1) := by
      rw [BitVec.add_assoc]
      congr 1
      exact (BitVec.ofNat_add j 1).symm
    refine ⟨?_, bs, _, ?_, hpos ▸ ht⟩
    · change some (t.gpr .x3 != (0#64)) = some (decide (j + 1 < p.bytes.len))
      rw [hz]
      have hb : bs.length < 2 ^ 64 := by have := p.lengthBound; simp only [List.length_cons] at hlen; omega_using [hlen, this]
      have he : (BitVec.ofNat 64 bs.length = (0#64)) ↔ bs.length = 0 := by
        constructor
        · intro h
          have hv := congrArg BitVec.toNat h
          change bs.length % 2 ^ 64 = 0 at hv
          rwa [Nat.mod_eq_of_lt hb] at hv
        · intro h; rw [h]
      have hj' : (bs.length ≠ 0) ↔ j + 1 < p.bytes.len := by
        simp only [List.length_cons] at hlen
        omega_using [hlen]
      simp only [bne]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq]
      exact (not_congr he).trans hj'
    · simp only [List.length_cons] at hlen
      omega_using [hlen]

theorem reduceLoop_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < p.bytes.len ∧ ReduceLoopPre p 0 s)
      (.loop (Arithmetic.reduceByte M.mm) (.nonzero .x .x3)) (fun _ _ => True) := by
  have hct := two_map (Φ := fun (p : ReducePublic × Nat) s => p.2 < p.1.bytes.len ∧ ReduceLoopPre p.1 p.2 s)
    (fun p : ReducePublic × Nat => p.1.remaining p.2)
    (fun p s ⟨hj, bs, acc, hlen, h⟩ =>
      ⟨bs, acc, hlen, by omega_using [hj, hlen], h⟩) (reduceByte_ct M)
  refine (two_loop (Φ := ReduceLoopPre) (Ψ := fun _ _ => True) (fun p => p.bytes.len) hct ?_).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  intro p j s hj hs
  exact WP.mono (reduceLoop_step M hj hs) fun t ⟨hz, ht⟩ => ⟨hz, fun _ => ht, fun _ => trivial⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ReduceSetupCT`, which only this module used -/

section

/-! # Constant time of streaming-reduction setup -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ReduceContext (p : ReducePublic) (s : State) : Prop :=
  SubCtx s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx p.minv ∧
  ModCtx s (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx 8) p.bytes.x.wx p.minv p.modulus

def ReduceSetupPre (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ p.bytes.x.wx ≤ 48

theorem reduceSetup_ct (M : Mont) : RelCT isa (Two ReduceSetupPre)
    (Arithmetic.reduceSetup M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceSetup seqs
  refine RelCT.seq (two_post (Ψ := fun p s => ReduceContext p s ∧
    wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx < p.modulus)
    (two_map (fun p : ReducePublic => p.toPowerPublic.product)
      (fun p s h => ⟨h.1.2, h.2, p.greater, p.odd⟩) (constants_ct M)) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hw⟩
    exact WP.mono (prepare_ok M hc p.lower hw p.greater p.odd hm.modulus hm.inverse)
      fun t ⟨hct, hmt, _, hr, _⟩ => ⟨⟨hct, hmt⟩, hr ▸ Nat.mod_lt _ (by have := p.greater; omega_using [this])⟩
  refine RelCT.seq (two_post (Ψ := fun p s => ReduceContext p s ∧
    wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx < p.modulus)
    (two_map (fun p : ReducePublic => p.toPowerPublic.product.layout)
      (fun _ _ h => ⟨h.1.1.good, Nat.le_refl _⟩)
      (small256_ct (by decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hr⟩
    refine WP.mono (small_ok hc.good (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega_arith) (by decide) (value := 256) (by decide))
      fun t ⟨hg, _, hf, hk⟩ => ?_
    have ht := arrays_context hc hf (by decide) hk
    have hz := hc.good.scr.nowrap
    refine ⟨⟨ht, ⟨hg, (hf.wv_of_not_mem (by decide) (by decide) hz).trans hm.modulus, ?_⟩⟩, ?_⟩
    · rw [hf.word0_of_not_mem (by decide) (by decide) hz (by have := p.lower; omega_using [this])]
      exact hm.inverse
    · rw [hf.wv_of_not_mem (by decide) (by decide) hz]
      exact hr
  refine RelCT.seq (two_post (Ψ := ReduceContext)
    (two_map (fun p : ReducePublic => p.bytes.x.ws)
      (fun _ _ h => ⟨_, h.1.1.good, Nat.le_refl _⟩) (M.ct (by unfold MmUse; decide))) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hr⟩
    exact WP.mono (mont_step M hm (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega_arith) (by unfold MmUse; decide) hr)
      fun t ⟨ht, _, _, hf, hk⟩ => ⟨arrays_context hc hf (by decide) hk, ht⟩
  refine RelCT.seq (two_post (Ψ := ReduceContext)
    (two_map (fun p : ReducePublic => p.bytes.x.ws)
      (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩)
      (zeroArr_ct (by decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨hc, hm⟩
    exact WP.mono (clear_mod_ok hc hm p.lower (by have := p.fits; have := p.upper; omega_arith)
      (by decide) (by decide)) fun t ⟨hct, hmt, _⟩ => ⟨hct, hmt⟩
  exact two_map (fun p : ReducePublic => p.bytes.x.ws)
    (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩)
    (zeroArr_ct (by decide) (by taint_decide))

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of complete DSA streaming reduction, including empty inputs -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ReduceCallBytes (p : ReducePublic) (s : State) : Prop := ∃ bs : List Byte,
  bs.length = p.bytes.len ∧ word s.mem p.bytes.x.B (8 * arg) = p.bytes.ptr ∧
  word s.mem p.bytes.x.B (8 * argLen) = BitVec.ofNat 64 bs.length ∧
  Src s p.bytes.x.B p.bytes.x.Z p.bytes.ptr bs

def ReduceCallPre (p : ReducePublic) (s : State) : Prop := ReduceSetupPre p s ∧ ReduceCallBytes p s

def ReduceCallPrepared (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ ReduceCallBytes p s ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aXm) p.bytes.x.wx =
    256 * 2 ^ (64 * p.bytes.x.wx) % p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aY) p.bytes.x.wx = 0 ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aX) p.bytes.x.wx = 0

def ReduceStart (p : ReducePublic) (s : State) : Prop :=
  ReduceLoopPre p 0 s ∧ s.gpr .x3 = BitVec.ofNat 64 p.bytes.len

theorem reduceCall_setup (M : Mont) {p : ReducePublic} {s : State} (h : ReduceCallPre p s) :
    WP isa (Arithmetic.reduceSetup M.mm) s (ReduceCallPrepared p) := by
  obtain ⟨⟨⟨hc, hm⟩, hw⟩, bs, hlen, hp, hl, hs⟩ := h
  refine WP.mono (reduceSetup_ok M hc p.lower hw p.greater p.odd hm.modulus hm.inverse)
    fun t ⟨hct, hmt, hr, hy, hx, hf, hk⟩ => ?_
  exact ⟨⟨hct, hmt⟩, ⟨bs, hlen, (work_parent hc hf (by decide)).trans hp,
    (work_parent hc hf (by decide)).trans hl, work_source hc hf hk hs⟩, hr, hy, hx⟩

theorem reduceCall_init {p : ReducePublic} {s : State} (h : ReduceCallPrepared p s) :
    WP isa (.block (Arithmetic.reduceInit arg argLen)) s (ReduceStart p) := by
  obtain ⟨⟨hc, hm⟩, ⟨bs, hlen, hp, hl, hs⟩, hr, hy, hx⟩ := h
  refine WP.mono (reduceInit_ok hc hm (by decide) (by decide) hp hl (hlen ▸ p.lengthBound))
    fun t ⟨hct, hmt, harr, hptr, hrem, hz, hf, hk⟩ => ?_
  have ht : ReduceState t p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx
      p.modulus p.minv p.bytes.ptr bs 0 :=
    ⟨hct, hmt, (harr aXm (by decide)).trans hr,
      fun i hi _ => (wv_eq_zero_iff _ _ _ _).mp ((harr aX (by decide)).trans hx) i hi,
      (harr aY (by decide)).trans hy, by have := p.greater; omega_using [this], hptr, hrem,
      work_source hc hf hk hs⟩
  refine ⟨⟨bs, 0, ?_, ?_⟩, ?_⟩
  · simpa only [Nat.sub_zero] using hlen
  · simpa only [BitVec.add_zero] using ht
  · simpa only [hlen] using hz

theorem reduceCall_ct (M : Mont) : RelCT isa (Two ReduceCallPre)
    (Arithmetic.reduce M.mm arg argLen) (fun _ _ => True) := by
  unfold Arithmetic.reduce seqs
  refine RelCT.seq (two_post (Ψ := ReduceCallPrepared)
    (two_map (fun p : ReducePublic => p) (fun _ _ h => h.1) (reduceSetup_ct M))
    (fun _ _ h => reduceCall_setup M h)) ?_
  refine RelCT.seq (two_post (Ψ := ReduceStart)
    (two_map (fun p : ReducePublic => p.bytes.x) (fun _ _ h => ⟨_, h.1.1⟩) reduceInit_ct)
    (fun _ _ h => reduceCall_init h)) ?_
  refine two_ite (fun p s t hs ht => by
    change some (s.gpr .x3 == (0#64)) = some (t.gpr .x3 == (0#64))
    rw [hs.2, ht.2]) ?_ ?_
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)
  · exact two_map (fun p : ReducePublic => p) (fun p s h => by
      refine ⟨?_, h.1.1⟩
      have hz := h.1.2
      have he := h.2
      change some (s.gpr .x3 == (0#64)) = some false at he
      rw [hz] at he
      by_contra hn
      have hl : p.bytes.len = 0 := by omega
      simp [hl] at he) (reduceLoop_ct M)

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.FinishCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.StoreCT`, which only this module used -/

section

/-! # Constant-time encoding of an arithmetic result -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def StorePre (p : BPub) (s : State) : Prop := ∃ minv,
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧
  word s.mem p.x.B (8 * result) = p.ptr ∧ word s.mem p.x.B (8 * resultLen) = BitVec.ofNat 64 p.len

def StoreRegs (p : BPub) (s : State) : Prop :=
  s.gpr .x8 = off (off p.x.B p.x.o) (slot p.x.wx aY) ∧
  s.gpr .x1 = p.ptr + BitVec.ofNat 64 p.len ∧ s.gpr .x9 = BitVec.ofNat 64 p.len

theorem store_ct : RelCT isa (Two StorePre) (Arithmetic.store aY result resultLen) (fun _ _ => True) := by
  unfold Arithmetic.store seqs
  refine RelCT.seq (RelCT.block_append (l₁ := ([ldh .x5 Crt.sLink] : List Instr))
    (RelCT.seq (two_piece (Ψ := fun p s => StorePre p s ∧ s.gpr .x5 = p.x.B) [.x0]
      (pins_of (fun p _ => off p.x.B p.x.o) (by
        intro p s ⟨_, hc, _⟩ r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hc.x0)) (by taint_decide) ?_)
      (two_piece (Ψ := StoreRegs) [.x0, .x5]
        (pins_of (fun p r => if r = .x0 then off p.x.B p.x.o else p.x.B) (by
          intro p s ⟨⟨_, hc, _⟩, ha⟩ r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hc.x0
          · exact ha)) (by taint_decide) ?_))) ?_
  · intro p s ⟨minv, hc, hp, hl⟩
    refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.x.B ∧ t.mem = s.mem)
      ?_ rfl rfl rfl) fun t ⟨⟨ha, hm⟩, hk⟩ =>
      ⟨⟨minv, hc.mem hm hk (by decide), hm ▸ hp, hm ▸ hl⟩, ha⟩
    drun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.link,
      hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot p.x.wx 8 by
        have := hdr_lt_slot p.x.wx 8 (show Crt.sLink < 32 by decide); omega_using [this])]
  · intro p s ⟨⟨minv, hc, hp, hl⟩, ha⟩
    have hsmall : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off p.x.B p.x.o) (8 * i)) 8 :=
      fun i hi => hc.good.scr.ld (by have := hdr_lt_slot p.x.wx 8 hi; omega_using [this])
    have hlarge : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.x.B (8 * i)) 8 :=
      fun i hi => hc.scr.ld (by
        have := hc.lo; have := hc.hi
        have : 256 ≤ slot p.x.w 8 := by unfold slot hdrBytes; omega_using []
        omega_arith)
    drun [StoreRegs, Crt.ldw, hc.x0, ha, hdr_enc (show result < 32 by decide),
      hdr_enc (show resultLen < 32 by decide), hdr_enc (show sArr aY < 32 by decide),
      hlarge result (by decide), hlarge resultLen (by decide), hp, hl,
      hsmall (sArr aY) (by decide), hc.hdr.harr aY (by decide)]
  exact two_taint [.x8, .x1, .x9]
    (pins_of (fun p r => if r = .x8 then off (off p.x.B p.x.o) (slot p.x.wx aY)
      else if r = .x1 then p.ptr + BitVec.ofNat 64 p.len else BitVec.ofNat 64 p.len) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of arithmetic result storage and return -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def FinishPre (p : BPub) (s : State) : Prop := StorePre p s ∧
  1 ≤ p.len ∧ p.len < 2 ^ 31 ∧ p.x.wx = (p.len + 7) / 8 ∧
  (∀ j < p.len, InRegions s.wr (p.ptr + BitVec.ofNat 64 j) 1) ∧
  (∀ j < p.len, p.x.Z ≤ ofs p.x.B (p.ptr + BitVec.ofNat 64 j))

theorem finish_ct : RelCT isa (Two FinishPre) (seqs Core.finish) (fun _ _ => True) := by
  unfold Core.finish seqs
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .x0 = off p.x.B p.x.o)
    (two_map (fun p : BPub => p) (fun _ _ h => h.1) store_ct) ?_) ?_
  · intro p s ⟨⟨minv, hc, hp, hl⟩, h1, h31, hw, hout, hpre⟩
    exact WP.mono (storeSuffix_ok hc (by decide) (by decide) (by decide) hp hl h1 h31 hw hout hpre)
      fun t ⟨hct, _⟩ => hct.x0
  exact two_taint [.x0]
    (pins_of (fun p _ => off p.x.B p.x.o) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h)) (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

/-! # Retaining public result bindings across arithmetic calls -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem FinishPre.work {p : BPub} {s t : State} {minv : BitVec 64}
    (h : FinishPre p s) (hc : SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv)
    (ht : SubCtx t p.x.B p.x.Z p.x.o p.x.w p.x.wx minv)
    (hf : Frm (off p.x.B p.x.o) (workRanges p.x.wx) s.mem t.mem) (hk : Keep mmRegs s t) :
    FinishPre p t := by
  obtain ⟨⟨_, _, hp, hl⟩, h1, h31, hw, hout, hpre⟩ := h
  exact ⟨⟨minv, ht, (work_parent hc hf (by decide)).trans hp,
    (work_parent hc hf (by decide)).trans hl⟩, h1, h31, hw,
    fun j hj => by rw [hk.wr]; exact hout j hj, hpre⟩

structure PowerFinishPublic extends PowerCallPublic where
  output : Addr
  outputLen : Nat

def PowerFinishPublic.result (p : PowerFinishPublic) : BPub := ⟨p.x, p.output, p.outputLen⟩

def PowerFinishPre (p : PowerFinishPublic) (s : State) : Prop :=
  PowerCallPre p.toPowerCallPublic s ∧ FinishPre p.result s

theorem powerFinish_ct (M : Mont) : RelCT isa (Two PowerFinishPre)
    (.seq (Arithmetic.power M.mm arg argLen arg2 arg2Len) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.result s)
    (two_map PowerFinishPublic.toPowerCallPublic (fun _ _ h => h.1) (powerCall_ct M)) ?_)
    (two_map PowerFinishPublic.result (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hf⟩
  exact WP.mono (power_ok M hc p.lower p.width48 p.fits p.upper p.greater p.odd
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
      VG.Impl.Rsa.AArch64.Crt.addMod aY aX aXm]) (seqs Core.finish)) (fun _ _ => True) := by
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

end VG.Proof.Dsa.AArch64
