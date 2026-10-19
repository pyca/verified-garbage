module

public import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Frame
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Power
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Constant time of setup, load and complete DSA exponentiation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure PowerCallPublic extends PowerPublic where
  base : Addr
  baseLen : Nat
  width48 : bytes.x.wx ≤ 48
  basePositive : 1 ≤ baseLen
  baseFits : (baseLen + 7) / 8 ≤ bytes.x.wx
  expPositive : 1 ≤ bytes.len
  expLimit : bytes.len ≤ 1024

abbrev PowerCallPublic.x (p : PowerCallPublic) : XPub := p.bytes.x

def PowerCallBytes (p : PowerCallPublic) (s : State) : Prop := ∃ bb eb : List Byte,
  word s.mem p.x.B (8 * arg) = p.base ∧ word s.mem p.x.B (8 * argLen) = BitVec.ofNat 64 bb.length ∧
  word s.mem p.x.B (8 * arg2) = p.bytes.ptr ∧ word s.mem p.x.B (8 * arg2Len) = BitVec.ofNat 64 eb.length ∧
  bb.length = p.baseLen ∧ eb.length = p.bytes.len ∧
  Src s p.x.B p.x.Z p.base bb ∧ Src s p.x.B p.x.Z p.bytes.ptr eb

def PowerCallPre (p : PowerCallPublic) (s : State) : Prop :=
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv ∧
  ModCtx s (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus ∧ PowerCallBytes p s

def PowerCallPrepared (p : PowerCallPublic) (s : State) : Prop := PowerCallPre p s ∧
  wv s.mem (off p.x.B p.x.o) (slot p.x.wx aOne) p.x.wx = 1 ∧
  wv s.mem (off p.x.B p.x.o) (slot p.x.wx aR2) p.x.wx = 2 ^ (128 * p.x.wx) % p.modulus

theorem PowerCallBytes.frame {p : PowerCallPublic} {s t : State} (h : PowerCallBytes p s)
    (hc : SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv)
    (hf : Frm (off p.x.B p.x.o) (workRanges p.x.wx) s.mem t.mem) (hk : Keep mmRegs s t) :
    PowerCallBytes p t := by
  obtain ⟨bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩ := h
  exact ⟨bb, eb, (work_parent hc hf (by decide)).trans hp, (work_parent hc hf (by decide)).trans hl,
    (work_parent hc hf (by decide)).trans hep, (work_parent hc hf (by decide)).trans hel,
    hbl, helen, work_source hc hf hk hb, work_source hc hf hk he⟩

theorem powerCall_prepare (M : Mont) {p : PowerCallPublic} {s : State} (h : PowerCallPre p s) :
    WP isa (Arithmetic.constants M.mm) s (PowerCallPrepared p) := by
  refine WP.mono (prepare_ok M h.1 p.lower p.width48 p.greater p.odd h.2.1.modulus h.2.1.inverse)
    fun t ⟨hc, hm, hone, hr2, hf, hk⟩ => ?_
  exact ⟨⟨hc, hm, h.2.2.frame h.1 hf hk⟩, hone, hr2⟩

theorem powerCall_load {p : PowerCallPublic} {s : State} (h : PowerCallPrepared p s) :
    WP isa (Arithmetic.load aX arg argLen) s (PowerCorePre p.toPowerPublic) := by
  obtain ⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hone, hr2⟩ := h
  have hb1 : 1 ≤ bb.length := hbl ▸ p.basePositive
  have hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
  have hb31 : bb.length < 2 ^ 31 := by
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega
  refine WP.mono (load_ok hc p.lower p.fits p.upper (by decide) (by decide) (by decide) hp hl hb hb1 hb31 hbw)
    fun t ⟨hct, _, hf, hk⟩ => ?_
  have hfa : Arrays (off p.x.B p.x.o) p.x.wx [aX] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self aX) hf (Nat.le_refl _) (Nat.le_refl _)
  have hfw := arrays_work hfa (by decide)
  have hz := hc.good.scr.nowrap
  have hmt : ModCtx t (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus := by
    refine ⟨hct.good, (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hm.modulus, ?_⟩
    rw [hfa.word0_of_not_mem (by decide) (by decide) hz (by have := p.lower; omega)]
    exact hm.inverse
  refine ⟨eb, ⟨hct, hmt, (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hone,
    (work_parent hc hfw (by decide)).trans hep, (work_parent hc hfw (by decide)).trans hel,
    helen, helen ▸ p.expPositive, helen ▸ p.expLimit, work_source hc hfw hk he⟩,
    (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hr2⟩

theorem powerCall_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerCallPre)
    (Arithmetic.power Sq.mm M.mm arg argLen arg2 arg2Len) (fun _ _ => True) := by
  unfold Arithmetic.power
  refine RelCT.seq (two_post (Ψ := PowerCallPrepared)
    (two_map (fun p : PowerCallPublic => p.toPowerPublic.product) (fun p s h =>
      ⟨h.2.1, p.width48, p.greater, p.odd⟩) (constants_ct M)) (fun _ _ h => powerCall_prepare M h)) ?_
  refine RelCT.seq (two_post (Ψ := fun p s => PowerCorePre p.toPowerPublic s)
    (two_map (fun p : PowerCallPublic => (⟨p.x, p.base, p.baseLen⟩ : BPub)) ?_
      (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => powerCall_load h)) ?_
  · intro p s ⟨⟨hc, _, bb, _, hp, hl, _, _, hbl, _, hb, _⟩, _⟩
    refine ⟨p.minv, bb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.basePositive, ?_, hbl ▸ p.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega
  · exact two_map PowerCallPublic.toPowerPublic (fun _ _ h => h) (powerCore_ct M Sq)

end VG.Proof.Dsa.X86_64
