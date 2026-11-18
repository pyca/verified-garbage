module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProductCallCT
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.Add
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.Core
meta import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Impl.Dsa.Layout
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInitCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInitCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceByteCT
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceByteCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Dsa.X86_64.AddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ProductCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.AddCT

/-! ### `Dsa.X86_64.AddCallCT`, which only this module used -/

section

/-! # Constant time of loading and adding DSA scalars -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
    (fun p _ h => ⟨⟨_, h.1.good, Nat.le_refl _⟩,
      by change 1 ≤ p.x.wx; have hw : 2 ≤ p.x.wx := p.lower; omega_using [hw],
      by change p.x.wx < 2 ^ 31; have hw : p.x.wx ≤ p.x.w := p.fits; have hw' : p.x.w < 2 ^ 30 := p.upper; omega_using [hw, hw']⟩)
    (addCode_ct (by decide) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide))

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ReduceCallCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.ReduceLoopCT`, which only this module used -/

section

/-! # Constant time of nonempty streaming reduction -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
      isa.eval .ne t = some (decide (j + 1 < p.bytes.len)) ∧ ReduceLoopPre p (j + 1) t := by
  obtain ⟨bs, acc, hlen, h⟩ := h
  cases bs with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons b bs =>
    refine WP.mono (reduceByte_ok M h p.lower (by have := p.fits; have := p.upper; omega_arith)
      p.greater255 p.odd (by have := p.lengthBound; omega_using [hlen, this]))
      fun t ⟨ht, hz, _, _⟩ => ?_
    have hpos : p.bytes.ptr + BitVec.ofNat 64 j + 1 = p.bytes.ptr + BitVec.ofNat 64 (j + 1) := by
      rw [BitVec.add_assoc, ofNat_add_one]
    refine ⟨?_, bs, _, ?_, hpos ▸ ht⟩
    · change VG.X86_64.eval .ne t = _
      simp only [VG.X86_64.eval, hz, Option.map_some]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      by_cases he : bs.length = 0
      · simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, decide_eq_true_eq, false_iff]
        simp only [List.length_cons] at hlen
        omega_using [hlen, he]
      · simp only [he, decide_false, Bool.not_false, decide_eq_true_eq, true_iff]
        simp only [List.length_cons] at hlen
        omega_using [hlen, he]
    · simp only [List.length_cons] at hlen
      omega_using [hlen]

theorem reduceLoop_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < p.bytes.len ∧ ReduceLoopPre p 0 s)
      (.loop (Arithmetic.reduceByte M.mm) .ne) (fun _ _ => True) := by
  have hct := two_map (Φ := fun (p : ReducePublic × Nat) s => p.2 < p.1.bytes.len ∧ ReduceLoopPre p.1 p.2 s)
    (fun p : ReducePublic × Nat => p.1.remaining p.2)
    (fun p s ⟨hj, bs, acc, hlen, h⟩ =>
      ⟨bs, acc, hlen, by omega_using [hj, hlen], h⟩) (reduceByte_ct M)
  refine (two_loop (Φ := ReduceLoopPre) (Ψ := fun _ _ => True) (fun p => p.bytes.len) hct ?_).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  intro p j s hj hs
  exact WP.mono (reduceLoop_step M hj hs) fun t ⟨hz, ht⟩ => ⟨hz, fun _ => ht, fun _ => trivial⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ReduceSetupCT`, which only this module used -/

section

/-! # Constant time of streaming-reduction setup -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ReduceContext (p : ReducePublic) (s : State) : Prop :=
  SubCtx s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx p.minv ∧
  ModCtx s (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx 8) p.bytes.x.wx p.minv p.modulus

def ReduceSetupPre (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ p.bytes.x.wx ≤ 48

def ReduceDoublePre (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx < p.modulus

theorem reduceSetup_ct (M : Mont) : RelCT isa (Two ReduceSetupPre)
    (Arithmetic.reduceSetup M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceSetup seqs
  refine RelCT.seq (two_post (Ψ := fun p s => ReduceContext p s ∧
    wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aOne) p.bytes.x.wx = 1)
    (two_map (fun p : ReducePublic => p.toPowerPublic.product)
      (fun p s h => ⟨h.1.2, h.2, p.greater, p.odd⟩) (constants_ct M)) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hw⟩
    exact WP.mono (prepare_ok M hc p.lower hw p.greater p.odd hm.modulus hm.inverse)
      fun t ⟨hct, hmt, hone, _⟩ => ⟨⟨hct, hmt⟩, hone⟩
  refine RelCT.seq (two_post (Ψ := ReduceDoublePre)
    (two_map (fun p : ReducePublic => p.bytes.x.ws)
      (fun _ _ h => ⟨_, h.1.1.good, Nat.le_refl _⟩) (M.ct (by unfold MmUse; decide))) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hone⟩
    exact WP.mono (mont_step M hm (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega_arith) (by unfold MmUse; decide)
      (by rw [hone]; exact p.greater)) fun t ⟨hmt, hlt, _, hf, hk⟩ =>
        ⟨⟨arrays_context hc hf (by decide) hk, hmt⟩, hlt⟩
  refine RelCT.seq (two_piece (Ψ := fun p s => ReduceDoublePre p s ∧ s.gpr .rcx = 8) []
    (by intro p s t hs ht r hr; cases hr) (by taint_decide) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hlt⟩
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = 8 ∧ t.mem = s.mem)
      (by xrun) rfl) fun t ⟨⟨hcx, hmem⟩, hk⟩ => ?_
    have hct := hc.of_keep hmem hk (by decide)
    exact ⟨⟨⟨hct, ⟨hct.good, hmem ▸ hm.modulus, hmem ▸ hm.inverse⟩⟩, hmem ▸ hlt⟩, hcx⟩
  refine RelCT.seq (two_post (Ψ := ReduceContext)
    (two_map (fun p : ReducePublic => (⟨p.toPowerPublic.product.layout, 8⟩ : DblPub)) ?_
      ((doubles_ct (mo := aN) (acc := aAcc) (tmp := aTmp) (o := aR2) (sl := sCnt) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)).mono
          (fun _ _ h => h) (fun _ _ _ => True.intro))) ?_) ?_
  · intro p s ⟨⟨⟨hc, hm⟩, hlt⟩, hcx⟩
    exact ⟨⟨hc.good, Nat.le_refl _⟩, p.lower,
      by change p.bytes.x.wx < 2 ^ 31; have := p.fits; have := p.upper; omega_arith,
      by change 1 ≤ 8; decide, by change 8 < 2 ^ 31; decide, hcx, by
        change wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx <
          wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aN) p.bytes.x.wx
        rw [hm.modulus]; exact hlt⟩
  · intro p s ⟨⟨⟨hc, hm⟩, hlt⟩, hcx⟩
    exact WP.mono (double_mod_ok hc hm p.lower (by have := p.fits; have := p.upper; omega_arith)
      (by decide) (by decide) (c := 8) hcx hlt) fun t ⟨hct, hmt, _⟩ => ⟨hct, hmt⟩
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

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of complete DSA streaming reduction, including empty inputs -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ReduceCallBytes (p : ReducePublic) (s : State) : Prop := ∃ bs : List Byte,
  bs.length = p.bytes.len ∧ word s.mem p.bytes.x.B (8 * arg) = p.bytes.ptr ∧
  word s.mem p.bytes.x.B (8 * argLen) = BitVec.ofNat 64 bs.length ∧
  Src s p.bytes.x.B p.bytes.x.Z p.bytes.ptr bs

def ReduceCallPre (p : ReducePublic) (s : State) : Prop := ReduceSetupPre p s ∧ ReduceCallBytes p s

def ReduceCallPrepared (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ ReduceCallBytes p s ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx =
    256 * 2 ^ (64 * p.bytes.x.wx) % p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aY) p.bytes.x.wx = 0 ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aX) p.bytes.x.wx = 0

def ReduceStart (p : ReducePublic) (s : State) : Prop :=
  ReduceLoopPre p 0 s ∧ s.zf = some (decide (p.bytes.len = 0))

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
    ⟨hct, hmt, (harr aR2 (by decide)).trans hr,
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
  refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)
  · exact two_map (fun p : ReducePublic => p) (fun p s h => by
      refine ⟨?_, h.1.1⟩
      have hz := h.1.2
      have he := h.2
      change VG.X86_64.eval .e s = some false at he
      simp only [VG.X86_64.eval, hz, Option.some.injEq, decide_eq_false_iff_not] at he
      omega_using [he]) (reduceLoop_ct M)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.FinishCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.StoreCT`, which only this module used -/

section

/-! # Constant-time encoding of an arithmetic result -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def StorePre (p : BPub) (s : State) : Prop := ∃ minv,
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧
  word s.mem p.x.B (8 * result) = p.ptr ∧ word s.mem p.x.B (8 * resultLen) = BitVec.ofNat 64 p.len

def StoreRegs (p : BPub) (s : State) : Prop :=
  s.gpr .rbx = off (off p.x.B p.x.o) (slot p.x.wx aY) ∧
  s.gpr .rsi = p.ptr ∧ s.gpr .rcx = BitVec.ofNat 64 p.len

theorem store_ct : RelCT isa (Two StorePre) (Arithmetic.store aY result resultLen) (fun _ _ => True) := by
  unfold Arithmetic.store seqs
  refine RelCT.seq (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr Crt.sLink))] : List Instr))
    (RelCT.seq (two_piece (Ψ := fun p s => StorePre p s ∧ s.gpr .rax = p.x.B) [.rdi]
      (pins_of (fun p _ => off p.x.B p.x.o) (by
        intro p s ⟨_, hc, _⟩ r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hc.rdi)) (by taint_decide) ?_)
      (two_piece (Ψ := StoreRegs) [.rdi, .rax]
        (pins_of (fun p r => if r = .rdi then off p.x.B p.x.o else p.x.B) (by
          intro p s ⟨⟨_, hc, _⟩, ha⟩ r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hc.rdi
          · exact ha)) (by taint_decide) ?_))) ?_
  · intro p s ⟨minv, hc, hp, hl⟩
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.x.B ∧ t.mem = s.mem)
      ?_ rfl) fun t ⟨⟨ha, hm⟩, hk⟩ =>
      ⟨⟨minv, hc.mem hm hk (by decide), hm ▸ hp, hm ▸ hl⟩, ha⟩
    xrun [State.ea, hdr, hc.rdi, hdrOff, hc.link,
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
    xrun [StoreRegs, State.ea, hdr, Crt.ws, hc.rdi, ha, hdrOff,
      hlarge result (by decide), hlarge resultLen (by decide), hp, hl,
      hsmall (sArr aY) (by decide), hc.hdr.harr aY (by decide)]
  exact two_taint [.rbx, .rsi, .rcx]
    (pins_of (fun p r => if r = .rbx then off (off p.x.B p.x.o) (slot p.x.wx aY)
      else if r = .rsi then p.ptr else BitVec.ofNat 64 p.len) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of arithmetic result storage and return -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def FinishPre (p : BPub) (s : State) : Prop := StorePre p s ∧
  1 ≤ p.len ∧ p.len < 2 ^ 31 ∧ p.x.wx = (p.len + 7) / 8 ∧
  (∀ j < p.len, InRegions s.wr (p.ptr + BitVec.ofNat 64 j) 1) ∧
  (∀ j < p.len, p.x.Z ≤ ofs p.x.B (p.ptr + BitVec.ofNat 64 j))

theorem finish_ct : RelCT isa (Two FinishPre) (seqs Core.finish) (fun _ _ => True) := by
  unfold Core.finish seqs
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .rdi = off p.x.B p.x.o)
    (two_map (fun p : BPub => p) (fun _ _ h => h.1) store_ct) ?_) ?_
  · intro p s ⟨⟨minv, hc, hp, hl⟩, h1, h31, hw, hout, hpre⟩
    exact WP.mono (storeSuffix_ok hc (by decide) (by decide) (by decide) hp hl h1 h31 hw hout hpre)
      fun t ⟨hct, _⟩ => hct.rdi
  exact two_taint [.rdi]
    (pins_of (fun p _ => off p.x.B p.x.o) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h)) (by taint_decide)

end VG.Proof.Dsa.X86_64

end

end

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
