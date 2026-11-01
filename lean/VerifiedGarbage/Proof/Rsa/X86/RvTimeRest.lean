module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvTimePrepare
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateData
public import VerifiedGarbage.Proof.Rsa.X86.RvNumbers
public import VerifiedGarbage.Proof.Rsa.X86.RvSearchState

import VerifiedGarbage.Proof.Rsa.X86.RvPrepared
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Rsa.X86.RvTimeSearch
import VerifiedGarbage.Proof.Rsa.X86.RvSearchLoop
import VerifiedGarbage.Proof.Rsa.X86.RvFinishY
import VerifiedGarbage.Proof.Rsa.X86.RvFactors
import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.Taint
import Init.Data.Option.Basic
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Rsa.X86.RvBatchGcd
import VerifiedGarbage.Proof.Rsa.X86.RvBatchTimeCheck
public import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Time
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Base
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
import VerifiedGarbage.Proof.Rsa.X86.RvArguments
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.X86.RvGcdSet
/-! # The recovery after the size checks leaks only the declared attempt count

Two runs from their numbers over the same geometry, with the same modulus
and the same number of attempts, leak the same trace through the halvings,
the Montgomery setup, the candidate search and the factors' computation and
export.
-/

-- Public: Appendix C.2's timing (`Rd/Time.lean`) relates its GCD through them too.
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa.X86.Keys

/-- A stage's state is what the batched GCD's timing starts from, in the wide layout. -/
theorem KS.gcdPre {g : Geo} (pg : PubG g) {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) :
    VG.Proof.Rsa.X86.InvBatchRt.Time.Pre0 VG.Impl.Rsa.X86.RecoverRt.wid g.B g.Z (16 * g.n + 24) 22 g.args g.sp s :=
  ⟨h.rtW, by decide, ⟨h.argsOk pg, h.sp, fun i hi => h.arg (h.start.2 i hi).1 (by
    change i < 12 at hi; omega)⟩⟩

theorem gcdFits {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) :
    VG.Proof.Rsa.X86.GcdBatchRt.Time.GFits g.Z (16 * g.n + 24) := by
  have lo := h.lower; have up := h.upper
  have f := h.rtW.ws.fits
  have en : VG.Proof.Rsa.X86.InvBatchRt.nw (16 * g.n + 24) = 2 * g.n + 3 := by
    simp only [VG.Proof.Rsa.X86.InvBatchRt.nw, VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords]; omega
  have ek := VG.Proof.Rsa.X86.InvBatchRt.kw_eq (16 * g.n + 24)
  simp only [arr, S, hdr] at f
  rw [en] at ek
  rw [ek] at f
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> rw [en]
  · generalize 2 * g.n + 3 = q at *; omega
  all_goals omega

end VG.Proof.Rsa.X86.Recover
end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvBatchGcdTime.lean`, which only this module imported.
section

/-! # Constant-time execution of recovery GCD -/

section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32)

omit rsaBatchLaw in
theorem batchGcd_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {V W : Nat → Nat} {m y z : Nat} :
    RelCT isa (fun s t =>
      KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s ∧
      KS g t0 (AG g.w m z) liveG (fun _ => 0) [] W [sMask] t)
      (VG.Impl.Rsa.X86.GcdBatchRt.body VG.Impl.Rsa.X86.RecoverRt.wid) (fun _ _ => True) :=
  fun _ _ _ _ _ _ ⟨hs, ht⟩ es et =>
    ⟨(VG.Proof.Rsa.X86.GcdBatchRt.Time.relBody (gcdFits hs) _ _ _ _ _ _ ⟨hs.gcdPre pg, ht.gcdPre pg⟩ es et).1,
      trivial⟩

 theorem factors_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {A B V W : Nat → Nat}
    {m y z : Nat} (modA : A aN=m) (modB : B aN=m)
    (valueA : A mY=y) (valueB : B mY=z) (zeroA : A aZ=0) (zeroB : B aZ=0)
    (oneA : A aOne=1) (oneB : B aOne=1) (odd : m%2=1) :
    RelCT isa (fun s t =>
      KS g s0 A [mY,aN,aZ,aOne] (fun _ => 0) [] V [sMask] s ∧
      KS g t0 B [mY,aN,aZ,aOne] (fun _ => 0) [] W [sMask] t)
      VG.Impl.Rsa.X86.RecoverRt.factors (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.factors
  simp only [seqs]
  refine VG.RelCT.seq (pub_relCT pg gcdSetCheck.choose_spec (fun _ h => KS.stage h) (fun _ h => KS.stage h)
    (fun _ h => gcdSet_ok h modA valueA zeroA oneA)
    (fun _ h => gcdSet_ok h modB valueB zeroB oneB)) ?_
  refine VG.RelCT.seq (stage_relCT (batchGcd_relCT pg)
    (fun _ h => batchGcd_ok h odd) (fun _ h => batchGcd_ok h odd)) ?_
  exact pub_relCT' pg factorTailCheck.choose_spec (fun _ h => KS.stage h) (fun _ h => KS.stage h)

end VG.Proof.Rsa.X86.Recover
end

end

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (recoverPrimes)

theorem fin_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {A B AW BW V W : Nat → Nat}
    {m k c : Nat} {st tt : Nat × Bool × Bool}
    (valueA : A mBase = m) (valueB : B mBase = m)
    (modA : A aN = m) (modB : B aN = m) (bound : m < 2 ^ (64 * g.n))
    (invA : (m * V sInv + 1) % 2 ^ 32 = 0) (invB : (m * W sInv + 1) % 2 ^ 32 = 0)
    (odd : m % 2 = 1) (large : 1 < m)
    (zeroA : A aZ = 0) (zeroB : B aZ = 0) (oneA : A aOne = 1) (oneB : B aOne = 1)
    (yl : st.1 < m) (zl : tt.1 < m) :
    RelCT isa (fun s t => SI g s0 A AW V m k c st s ∧ SI g t0 B BW W m k c tt t)
      VG.Impl.Rsa.X86.RecoverRt.fin (fun _ _ => True) := by
  have pre : ∀ {s0 : State} {A AW V : Nat → Nat} {st : Nat × Bool × Bool} {s : State},
      A mBase = m → (m * V sInv + 1) % 2 ^ 32 = 0 →
      KS g s0 (upd (upd A mY (st.1 * 2 ^ (64 * g.n) % m)) mXm 1) (mXm :: liveSq) AW [wR]
        (upd (VS V k c st) sMask (b2n st.2.2)) (sMask :: slotsSq) s → MulPre g mY mY mXm s := by
    intro s0 A AW V st s value inverse h
    have mr := h.montReady (m := m) (by simp [liveSq, liveM]) (by simp [slotsSq])
      (by simpa only [upd_ne _ _ (by decide : mBase ≠ mXm),
        upd_ne _ _ (by decide : mBase ≠ mY)] using value) bound
      (by simpa [VS, upd, sInv, sMask, sK, sCnt, sDone, sOk] using inverse)
    exact ⟨_, _, _, _, _, _, _, _, h, mr, by simp [liveSq], by simp,
      by simpa only [upd_ne _ _ (by decide : mY ≠ mXm), upd_self] using
        Nat.mod_lt (st.1 * 2 ^ (64 * g.n)) (by omega : 0 < m),
      by simpa only [upd_self] using large, by decide, by decide⟩
  have finY : RelCT isa (fun s t => SI g s0 A AW V m k c st s ∧ SI g t0 B BW W m k c tt t)
      VG.Impl.Rsa.X86.RecoverRt.finY (fun _ _ => True) := by
    unfold VG.Impl.Rsa.X86.RecoverRt.finY
    intro s t tr ur sf tf ⟨hs, ht⟩ es et
    cases es with
    | @seq _ _ _ u _ _ _ ea eb =>
      cases et with
      | @seq _ _ _ v _ _ _ fa fb =>
        have eqA := pub_trace pg finHeadCheck (show KS .. from hs) (show KS .. from ht) ea fa
        have ha := wp_result (finHead_ok hs oneA) ea
        have hb := wp_result (finHead_ok ht oneB) fa
        have eqB := (mmul_relCT pg (by decide) (by decide) (by decide) (by decide) mulArgs_mY_mY_mXmCheck
          ⟨_, clrTop_mYCheck⟩ _ _ _ _ _ _ ⟨pre valueA invA ha, pre valueB invB hb⟩ eb fb).1
        exact ⟨by rw [eqA, eqB], trivial⟩
  unfold VG.Impl.Rsa.X86.RecoverRt.fin
  simp only [seqs]
  refine VG.RelCT.seq (R := fun s t =>
      KS g s0 (upd A mY st.1) [mY, aN, aZ, aOne] (fun _ => 0) [] (fun _ => b2n st.2.2) [sMask] s ∧
      KS g t0 (upd B mY tt.1) [mY, aN, aZ, aOne] (fun _ => 0) [] (fun _ => b2n tt.2.2) [sMask] t)
    (stage_relCT finY (fun _ hs => finY_ok hs valueA bound invA odd large oneA yl)
      (fun _ ht => finY_ok ht valueB bound invB odd large oneB zl)) ?_
  refine VG.RelCT.seq (stage_relCT (factors_relCT pg
      (by simpa only [upd_ne _ _ (by decide : aN ≠ mY)] using modA)
      (by simpa only [upd_ne _ _ (by decide : aN ≠ mY)] using modB)
      (by rw [upd_self]) (by rw [upd_self])
      (by simpa only [upd_ne _ _ (by decide : aZ ≠ mY)] using zeroA)
      (by simpa only [upd_ne _ _ (by decide : aZ ≠ mY)] using zeroB)
      (by simpa only [upd_ne _ _ (by decide : aOne ≠ mY)] using oneA)
      (by simpa only [upd_ne _ _ (by decide : aOne ≠ mY)] using oneB) odd)
    (fun _ cs => factors_ok cs
      (by simpa only [upd_ne _ _ (by decide : aN ≠ mY)] using modA)
      (by rw [upd_self]) (by simpa only [upd_ne _ _ (by decide : aZ ≠ mY)] using zeroA)
      (by simpa only [upd_ne _ _ (by decide : aOne ≠ mY)] using oneA) odd large)
    (fun _ ds => factors_ok ds
      (by simpa only [upd_ne _ _ (by decide : aN ≠ mY)] using modB)
      (by rw [upd_self]) (by simpa only [upd_ne _ _ (by decide : aZ ≠ mY)] using zeroB)
      (by simpa only [upd_ne _ _ (by decide : aOne ≠ mY)] using oneB) odd large))
    (pub_relCT' pg storesCheck (fun _ hs => KS.stage hs) (fun _ ht => KS.stage ht))

/-- Two runs ready for `fin`: the squares' states over the same modulus and attempt, with what
`fin_relCT` needs of each. -/
def FinPair (g : Geo) (s t : State) : Prop :=
  ∃ (s0 t0 : State) (A B AW BW V W : Nat → Nat) (m k c : Nat) (st tt : Nat × Bool × Bool),
    SI g s0 A AW V m k c st s ∧ SI g t0 B BW W m k c tt t ∧
    A mBase = m ∧ B mBase = m ∧ A aN = m ∧ B aN = m ∧ m < 2 ^ (64 * g.n) ∧
    (m * V sInv + 1) % 2 ^ 32 = 0 ∧ (m * W sInv + 1) % 2 ^ 32 = 0 ∧ m % 2 = 1 ∧ 1 < m ∧
    A aZ = 0 ∧ B aZ = 0 ∧ A aOne = 1 ∧ B aOne = 1 ∧ st.1 < m ∧ tt.1 < m

theorem finPair_relCT {g : Geo} (pg : PubG g) :
    RelCT isa (FinPair g) VG.Impl.Rsa.X86.RecoverRt.fin (fun _ _ => True) := by
  rintro s t tr ur sf tf ⟨s0, t0, A, B, AW, BW, V, W, m, k, c, st, tt, hs, ht, vA, vB, mA, mB, bd, iA, iB, od, lg,
    zA, zB, oA, oB, yl, zl⟩ e f
  exact fin_relCT pg vA vB mA mB bd iA iB od lg zA zB oA oB yl zl _ _ _ _ _ _ ⟨hs, ht⟩ e f

omit rsaBatchLaw in
theorem CandidateData.search_ok {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen)
    {s : State} (h : KS g C.s0 C.A liveM C.AW [wR] C.V [sInv, sTc, sCnt] s)
    (vc : C.V sCnt = 0) (tc : 1 ≤ C.V sTc) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.candLoop s (SearchResult g C.s0 C.A C.AW C.V m (8 * (dLen + eLen))) :=
  candLoop_ok C.zero C.value C.bound C.inverse C.odd C.large C.one C.neg C.r2
    C.ae C.ad C.tc C.rb C.count C.limit C.wide h vc tc

omit rsaBatchLaw in
theorem rest_relCT (g : CallGeometry) (pg : PubG g.toGeo) (s0 t0 : State)
    (left : Inputs g s0) (right : Inputs g t0)
    (goS : GoOn (product g s0.mem)) (goT : GoOn (product g t0.mem))
    (boundS : inputValue g s0.mem 0 < 2 ^ (64 * g.n))
    (boundT : inputValue g t0.mem 0 < 2 ^ (64 * g.n))
    (oddS : inputValue g s0.mem 0 % 2 = 1) (oddT : inputValue g t0.mem 0 % 2 = 1)
    (largeS : 101 < inputValue g s0.mem 0) (largeT : 101 < inputValue g t0.mem 0)
    (modulus : inputValue g s0.mem 0 = inputValue g t0.mem 0)
    (tries : (recoverPrimes (inputValue g s0.mem 0) (inputValue g s0.mem 1) (inputValue g s0.mem 2)).2 =
      (recoverPrimes (inputValue g t0.mem 0) (inputValue g t0.mem 1) (inputValue g t0.mem 2)).2) :
    RelCT isa (fun s t => NumbersState g s0 s ∧ NumbersState g t0 t) VG.Impl.Rsa.X86.RecoverRt.rest
      (FinPair g.toGeo) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
  cases et with
  | @seq _ _ _ v _ _ _ f1 fr =>
  cases er with
  | @seq _ _ _ x _ _ _ e2 er =>
  cases fr with
  | @seq _ _ _ y _ _ _ f2 fr =>
  obtain ⟨eq1, is, it⟩ := halving_relCT g pg s0 t0 left right _ _ _ _ _ _ ⟨hs, ht⟩ e1 f1
  have eq2 := (mont_relCT pg (s0 := s0) (t0 := t0) (A := fun _ => inputValue g s0.mem 0)
    (B := fun _ => inputValue g t0.mem 0) rfl rfl boundS boundT oddS oddT (by omega) (by omega)
    _ _ _ _ _ _ ⟨is, it⟩ e2 f2).1
  obtain ⟨p⟩ := wp_result (prepare_ok left hs goS boundS oddS largeS) (Exec.seq e1 e2)
  obtain ⟨q⟩ := wp_result (prepare_ok right ht goT boundT oddT largeT) (Exec.seq f1 f2)
  rw [← modulus] at q
  have tries' := tries
  rw [← modulus] at tries'
  have attempts : p.context.tries = q.context.tries :=
    p.attempts.trans (tries'.trans q.attempts.symm)
  have eq3 := (candLoop_relCT pg p.context q.context p.counter q.counter
    p.twos q.twos attempts _ _ _ _ _ _ ⟨p.state, q.state⟩ er fr).1
  obtain ⟨j, st, _, cs, smallS, _, _⟩ := wp_result (p.context.search_ok p.state p.counter p.twos) er
  obtain ⟨l, tt, _, ds, smallT, _, _⟩ := wp_result (q.context.search_ok q.state q.counter q.twos) fr
  exact ⟨by rw [eq1, eq2, eq3], _, _, _, _, _, _, _, _, _, _, _, _, _, cs, ds, p.context.value, q.context.value,
    p.modulus, q.modulus, p.context.bound,
    (by simpa [VJ, upd, sInv, sCand, sCnt] using p.context.inverse),
    (by simpa [VJ, upd, sInv, sCand, sCnt] using q.context.inverse),
    p.context.odd, (by have := p.context.large; omega), p.context.zero, q.context.zero, p.unit, q.unit,
    smallS, smallT⟩

end VG.Proof.Rsa.X86.Recover
