module

public import VerifiedGarbage.Proof.Dsa.X86_64.PublicPowerCT
public import VerifiedGarbage.Proof.Dsa.X86_64.PowerCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicPowerCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PowerCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Public exponent bytes across Montgomery setup and input loading -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

def PowerCallBytes (p : PowerCallPublic × List Byte) (s : State) : Prop := ∃ bb : List Byte,
  word s.mem p.1.x.B (8 * arg) = p.1.base ∧ word s.mem p.1.x.B (8 * argLen) = BitVec.ofNat 64 bb.length ∧
  word s.mem p.1.x.B (8 * arg2) = p.1.bytes.ptr ∧ word s.mem p.1.x.B (8 * arg2Len) = BitVec.ofNat 64 p.2.length ∧
  bb.length = p.1.baseLen ∧ p.2.length = p.1.bytes.len ∧
  Src s p.1.x.B p.1.x.Z p.1.base bb ∧ Src s p.1.x.B p.1.x.Z p.1.bytes.ptr p.2

def PowerCallPre (p : PowerCallPublic × List Byte) (s : State) : Prop :=
  SubCtx s p.1.x.B p.1.x.Z p.1.x.o p.1.x.w p.1.x.wx p.1.minv ∧
  ModCtx s (off p.1.x.B p.1.x.o) (slot p.1.x.wx 8) p.1.x.wx p.1.minv p.1.modulus ∧ PowerCallBytes p s

def PowerCallPrepared (p : PowerCallPublic × List Byte) (s : State) : Prop := PowerCallPre p s ∧
  wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx aOne) p.1.x.wx = 1 ∧
  wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx aR2) p.1.x.wx = 2 ^ (128 * p.1.x.wx) % p.1.modulus

theorem PowerCallBytes.frame {p : PowerCallPublic × List Byte} {s t : State} (h : PowerCallBytes p s)
    (hc : SubCtx s p.1.x.B p.1.x.Z p.1.x.o p.1.x.w p.1.x.wx p.1.minv)
    (hf : Frm (off p.1.x.B p.1.x.o) (workRanges p.1.x.wx) s.mem t.mem) (hk : Keep mmRegs s t) :
    PowerCallBytes p t := by
  obtain ⟨bb, hp, hl, hep, hel, hbl, helen, hb, he⟩ := h
  exact ⟨bb, (work_parent hc hf (by decide)).trans hp, (work_parent hc hf (by decide)).trans hl,
    (work_parent hc hf (by decide)).trans hep, (work_parent hc hf (by decide)).trans hel,
    hbl, helen, work_source hc hf hk hb, work_source hc hf hk he⟩

theorem powerCall_prepare (M : Mont) {p : PowerCallPublic × List Byte} {s : State} (h : PowerCallPre p s) :
    WP isa (Arithmetic.constants M.mm) s (PowerCallPrepared p) := by
  refine WP.mono (prepare_ok M h.1 p.1.lower p.1.width48 p.1.greater p.1.odd h.2.1.modulus h.2.1.inverse)
    fun t ⟨hc, hm, hone, hr2, hf, hk⟩ => ?_
  exact ⟨⟨hc, hm, h.2.2.frame h.1 hf hk⟩, hone, hr2⟩

theorem powerCall_load {p : PowerCallPublic × List Byte} {s : State} (h : PowerCallPrepared p s) :
    WP isa (Arithmetic.load aX arg argLen) s (PowerCorePre (p.1.toPowerPublic, p.2)) := by
  obtain ⟨⟨hc, hm, bb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hone, hr2⟩ := h
  have hb1 : 1 ≤ bb.length := hbl ▸ p.1.basePositive
  have hbw : (bb.length + 7) / 8 ≤ p.1.x.wx := hbl ▸ p.1.baseFits
  have hb31 : bb.length < 2 ^ 31 := by
    have hw48 : p.1.x.wx ≤ 48 := p.1.width48
    omega
  refine WP.mono (load_ok hc p.1.lower p.1.fits p.1.upper (by decide) (by decide) (by decide) hp hl hb hb1 hb31 hbw)
    fun t ⟨hct, _, hf, hk⟩ => ?_
  have hfa : Arrays (off p.1.x.B p.1.x.o) p.1.x.wx [aX] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self aX) hf (Nat.le_refl _) (Nat.le_refl _)
  have hfw := arrays_work hfa (by decide)
  have hz := hc.good.scr.nowrap
  have hmt : ModCtx t (off p.1.x.B p.1.x.o) (slot p.1.x.wx 8) p.1.x.wx p.1.minv p.1.modulus := by
    refine ⟨hct.good, (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hm.modulus, ?_⟩
    rw [hfa.word0_of_not_mem (by decide) (by decide) hz (by have := p.1.lower; omega)]
    exact hm.inverse
  refine ⟨⟨hct, hmt, (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hone,
    (work_parent hc hfw (by decide)).trans hep, (work_parent hc hfw (by decide)).trans hel,
    helen, helen ▸ p.1.expPositive, helen ▸ p.1.expLimit, work_source hc hfw hk he⟩,
    (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hr2⟩

theorem powerCall_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerCallPre)
    (VG.Impl.Dsa.X86_64.PublicPower.power Sq.mm M.mm arg argLen arg2 arg2Len) (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86_64.PublicPower.power
  refine RelCT.seq (two_post (Ψ := PowerCallPrepared)
    (two_map (fun p : PowerCallPublic × List Byte => p.1.toPowerPublic.product) (fun p s h =>
      ⟨h.2.1, p.1.width48, p.1.greater, p.1.odd⟩) (constants_ct M)) (fun _ _ h => powerCall_prepare M h)) ?_
  refine RelCT.seq (two_post (Ψ := fun p s => PowerCorePre (p.1.toPowerPublic, p.2) s)
    (two_map (fun p : PowerCallPublic × List Byte => (⟨p.1.x, p.1.base, p.1.baseLen⟩ : BPub)) ?_
      (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => powerCall_load h)) ?_
  · intro p s ⟨⟨hc, _, bb, hp, hl, _, _, hbl, _, hb, _⟩, _⟩
    refine ⟨p.1.minv, bb, hc, p.1.lower, p.1.fits, p.1.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.1.basePositive, ?_, hbl ▸ p.1.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.1.x.wx := hbl ▸ p.1.baseFits
    have hw48 : p.1.x.wx ≤ 48 := p.1.width48
    omega
  · exact two_map (fun p : PowerCallPublic × List Byte => (p.1.toPowerPublic, p.2)) (fun _ _ h => h) (powerCore_ct M Sq)

end VG.Proof.Dsa.X86_64.PublicPower
