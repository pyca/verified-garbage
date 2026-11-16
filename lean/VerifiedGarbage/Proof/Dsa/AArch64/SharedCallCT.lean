module
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedPowerCT
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedCall
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.FinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.Call
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedPowerCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.FinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Call
meta import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The shared exponentiation's call is constant time in the secret exponent -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Proof.Dsa.AArch64

/-- The call's public data, and the public exponent's. -/
structure SCallPublic extends Call3Public where
  qp : Addr
  qb : List Byte
  qlen : qb.length = bytes.len
  wide : 8 ≤ bytes.x.wx
  tiles : bytes.x.wx % 8 = 0

abbrev SCallPublic.body (p : SCallPublic) : SPub :=
  { p.toPowerCallPublic with qp := p.qp, qb := p.qb, qlen := p.qlen, wide := p.wide, tiles := p.tiles }

def SCallPre (a b output : Operand) (p : SCallPublic) (s : State) : Prop :=
  Call3Pre a b output p.toCall3Public s ∧ p.x.o = pWorkspace ∧
  word s.mem p.x.B Field.q.offset = p.qp ∧ Src s p.x.B p.x.Z p.qp p.qb

/-- The call up to its return to the parent workspace. -/
theorem sharedCall_ct (M : Mont) {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (callHead a b output pWorkspace)) hc).isSome = true) :
    RelCT isa (Two (SCallPre a b output))
      (.seq (.block (callHead a b output pWorkspace)) (.seq (SharedPower.power M.mm) (seqs Core.finish)))
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun (p : SCallPublic) s => SPre p.body s ∧ FinishPre p.result s)
    (two_map SCallPublic.toCall3Public (fun _ _ h => h.1) (callHead_ct hT)) ?_) ?_
  · intro p s ⟨h, heq, hq, hqs⟩
    rw [← heq]
    refine WP.mono (callHead_run ha hb ho h) fun t ⟨⟨hpre, hfin⟩, hf, hk⟩ => ?_
    have hqo : Field.q.offset = 264 := rfl
    have hz : 176 ≤ p.x.Z := Nat.le_trans (by decide) p.extent
    exact ⟨⟨hpre, (hf.word_eq (fun r hr => by
        simp only [argumentRanges, List.mem_singleton] at hr; subst hr; right; omega_using [hqo])
        (by omega_using [hqo, hz])).trans hq, arguments_source hf hk hz hqs⟩, hfin⟩
  refine RelCT.seq (two_post (Ψ := fun (p : SCallPublic) s => FinishPre p.result s)
    (two_map SCallPublic.body (fun _ _ h => h.1) (power_ct M)) ?_)
    (two_map (fun p : SCallPublic => p.result) (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hq, hqs⟩, hf⟩
  exact WP.mono (power_ok M hc p.wide p.width48 p.tiles p.fits p.upper p.greater p.odd
    hm.modulus hm.inverse hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
    hep hel he (helen ▸ p.expPositive) (helen ▸ p.expLimit) hq hqs (p.qlen.trans helen.symm))
    fun t ⟨hct, _, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

/-- The whole call: the bases' and the secret exponent's bytes do not show
in what it leaks. -/
theorem sharedPow_ct (M : Mont) {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (callHead a b output pWorkspace)) hc).isSome = true) :
    RelCT isa (Two (SCallPre a b output)) (SharedPower.pow M.mm a b output) (fun _ _ => True) := by
  unfold SharedPower.pow
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post
    (Ψ := fun (p : SCallPublic) s => s.gpr .x0 = p.x.B) (sharedCall_ct M ha hb ho hT) ?_) ?_)
  · intro p s ⟨⟨hg, child, ⟨ba, bb, has, hbs, hbl, hel⟩, hp, hep, hop, hol, hout, hprefix⟩, heq, hq, hqs⟩
    have hlo := p.childLow
    have hhi := p.childHigh
    rw [heq] at hlo hhi child
    refine WP.mono (powCall_ok M hg child p.extent hlo hhi p.wide p.width48 p.tiles p.fits p.upper p.greater
      p.odd a b output ha hb ho has hbs (hq ▸ hqs) (p.qlen.trans hel.symm) (hbl ▸ p.basePositive)
      (hbl ▸ p.baseFits) (hel ▸ p.expPositive) (hel ▸ p.expLimit) hol p.outputPositive p.outputBound
      p.outputWidth (hop ▸ hout) (hop ▸ hprefix)) fun t h => h.1.1.x0
  · simp only [seqs]
    exact x0_ct (fun p : SCallPublic => p.x.B) (fun _ _ h => h) (by unfold Checks.accumulate; taint_decide)

/-! ## In DSA's execution context -/

/-- The call's public data in DSA's execution context: the domain's `q` is
public, of the secret exponent's length. -/
structure ReadySharedPublic (d : Nat) extends ReadyCallPublic .p d where
  qb : List Byte
  qlen : qb.length = exponentLen

theorem pWide (L : ExecutionLayout) : 8 ≤ L.pWords ∧ L.pWords % 8 = 0 := by
  rcases L.lengths with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [ExecutionLayout.pWords, h1] <;> decide

def ReadySharedPublic.call {d : Nat} (p : ReadySharedPublic d) (a b : Operand) : SCallPublic :=
  { p.toReadyCallPublic.call a b with
    qp := p.layout.fields .q, qb := p.qb, qlen := p.qlen, wide := (pWide p.layout).1, tiles := (pWide p.layout).2 }

def ReadySharedPre (d : Nat) (a b : Operand) (p : ReadySharedPublic d) (s : State) : Prop :=
  ReadyCallPre .p d a b p.toReadyCallPublic s ∧ Src s p.layout.base activeBytes (p.layout.fields .q) p.qb

theorem readySharedPow_ct (M : Mont) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer) (hd : d < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a b ⟨.local d, .pLen⟩ pWorkspace)) hc).isSome = true) :
    RelCT isa (Two (ReadySharedPre d a b)) (SharedPower.pow M.mm a b ⟨.local d, .pLen⟩) (fun _ _ => True) :=
  two_map (fun p : ReadySharedPublic d => p.call a b)
    (fun _ _ h => ⟨readyCall_pre hpa hpb h.1, rfl, h.1.1.fields .q (by decide), h.2⟩)
    (sharedPow_ct M ha hb hd hT)

end VG.Proof.Dsa.AArch64.SharedPower
