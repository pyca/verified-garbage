module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvABI
public import VerifiedGarbage.Proof.Rsa.X86.RvResult
public import VerifiedGarbage.Proof.Rsa.X86.RvPair
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeSized
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Rsa.X86.RvModulusTiming
import VerifiedGarbage.Proof.Rsa.X86.RvFailureTiming
import VerifiedGarbage.Proof.Rsa.X86.RvEntryTiming
import VerifiedGarbage.Proof.Rsa.X86.RvInstalled
import VerifiedGarbage.Proof.Rsa.X86.RvReturn
import VerifiedGarbage.Proof.Rsa.X86.RvBuffers
import VerifiedGarbage.Proof.Rsa.X86.RvResources
import VerifiedGarbage.Proof.Rsa.X86.RvArgumentsEq
import VerifiedGarbage.Proof.Bignum.X86.PublicEntryTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeCheck
public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeSteps
import VerifiedGarbage.Proof.Rsa.X86.RvTimeRest
import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Time
import VerifiedGarbage.Proof.Rsa.X86.Rd.Product
import VerifiedGarbage.Proof.Rsa.X86.Rd.Stages
import VerifiedGarbage.Proof.Rsa.X86.Rd.Stages2
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Sized
import VerifiedGarbage.Proof.Rsa.X86.RvFailure
import VerifiedGarbage.Proof.Rsa.X86.RvSatisfiable
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset

/-! # Prime recovery by Appendix C.2 on i686 leaks only the modulus's and exponents' lengths

Its traces depend on the arguments alone: past the modulus check, which reads
the modulus (public: the contract's leak is the modulus and the public
exponent), every piece is checked by the taint analysis or runs a public count
of times (`det_relCT`). As for prime recovery by Appendix C.1, the pieces'
checks take the arguments public, which needs the writable regions apart from
them: `sizedD_relCT` from states whose writable regions are narrowed to the
working space and the outputs, and `sizedNarrowD_relCT` from the states
themselves.
-/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys

/-- Two runs agreeing on `τA`, each meeting its own predicate. -/
def RA (P Q : State → Prop) (s t : State) : Prop := VG.X86.Taint.Agree τA s t ∧ P s ∧ Q t

theorem PubA.trace {c : Prog isa} (h : PubA c) {s t : State} (ag : VG.X86.Taint.Agree τA s t)
    {tr ur : List Leak} {sf tf : State} (es : Exec isa c s tr sf) (et : Exec isa c t ur tf) :
    tr = ur ∧ VG.X86.Taint.Agree τA sf tf := by
  obtain ⟨hint, hh⟩ := h
  obtain ⟨τ', hc, hle⟩ := Option.map_eq_some_iff.mp hh
  obtain ⟨e, a⟩ := VG.Taint.check_sound hc ag es et
  exact ⟨e, sseTaint.le_sound hle a⟩

theorem PubA.relCT {c : Prog isa} (h : PubA c) {P Q P' Q' : State → Prop}
    (wl : ∀ s, P s → WP isa c s P') (wr : ∀ t, Q t → WP isa c t Q') :
    RelCT isa (RA P Q) c (RA P' Q') := by
  intro s t tr ur sf tf ⟨ag, hp, hq⟩ es et
  obtain ⟨e, a⟩ := h.trace ag es et
  exact ⟨e, a, wp_result (wl s hp) es, wp_result (wr t hq) et⟩

/-- The same, forgetting the runs' stages. -/
theorem PubA.relCT' {c : Prog isa} (h : PubA c) {P Q : State → Prop} :
    RelCT isa (RA P Q) c (RA (fun _ => True) (fun _ => True)) := by
  intro s t tr ur sf tf ⟨ag, _, _⟩ es et
  obtain ⟨e, a⟩ := h.trace ag es et
  exact ⟨e, a, trivial, trivial⟩

/-- Straight pieces, then `last`: each run from where its first pieces leave it. -/
theorem pubs_relCT {last : Prog isa} {P Q : State → Prop} {R : State → State → Prop}
    (hl : RelCT isa (RA P Q) last R) : ∀ {c : Prog isa} {cs : List (Prog isa)}, PubA c → (∀ d ∈ cs, PubA d) →
    RelCT isa (RA (fun s => WP isa (seqs (c :: cs)) s P) (fun t => WP isa (seqs (c :: cs)) t Q))
      (seqs (c :: cs ++ [last])) R
  | _, [], hc, _ => VG.RelCT.seq (hc.relCT (fun _ h => h) (fun _ h => h)) hl
  | _, d :: _, hc, hcs => VG.RelCT.seq (hc.relCT (fun _ h => WP.seq_iff.mp h) (fun _ h => WP.seq_iff.mp h))
      (pubs_relCT hl (hcs d (List.mem_cons_self ..)) (fun e he => hcs e (List.mem_cons_of_mem _ he)))

/-- A loop counted down from `K`, its body checked, from two runs' invariants. -/
theorem loopA {g : Geo} (pg : PubG g) {body : Prog isa} {K : Nat} (I : Nat → State → Prop) (pos : 0 < K)
    (hb : PubA body) (hI : ∀ k s, I k s → MulPost g s)
    (step : ∀ k s, k < K → I k s → WP isa body s fun v => I (k + 1) v ∧ v.zf = some (decide (K - k - 1 = 0))) :
    RelCT isa (RA (I 0) (I 0)) (.loop body .ne) (RA (I K) (I K)) := by
  have L := fixedLoop_relCT (body := body) (c := K) I I pos
    (fun k _ s t _ _ _ _ ⟨hs, ht⟩ es et => by
      obtain ⟨_, _, _, _, _, _, _, h⟩ := hI k s hs
      obtain ⟨_, _, _, _, _, _, _, j⟩ := hI k t ht
      exact ⟨(hb.trace (ks_agree pg h j) es et).1, trivial⟩)
    (fun k s hk h => WP.mono (step k s hk h) fun v ⟨a, b⟩ => ⟨a, by rw [b, Nat.sub_sub]⟩)
    (fun k s hk h => WP.mono (step k s hk h) fun v ⟨a, b⟩ => ⟨a, by rw [b, Nat.sub_sub]⟩)
  refine L.mono (fun s t h => ⟨h.2.1, h.2.2⟩) fun s t ⟨hs, ht⟩ => ?_
  obtain ⟨_, _, _, _, _, _, _, h⟩ := hI K s hs
  obtain ⟨_, _, _, _, _, _, _, j⟩ := hI K t ht
  exact ⟨ks_agree pg h j, hs, ht⟩

theorem twI_stage {g : Geo} {k : Nat} {s : State} (h : TwI g k s) : MulPost g s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := h
  exact KS.stage h

theorem pI_stage {g : Geo} {y x a z k : Nat} {live liveW ls : List Nat}
    {F : (Nat → Nat) → (Nat → Nat) → Prop} {s : State}
    (h : PI g y x a z live liveW ls F k s) : MulPost g s := by
  obtain ⟨_, _, _, _, _, _, _, h⟩ := h
  exact KS.stage h

theorem sqI_stage {g : Geo} {k : Nat} {s : State} (h : SqI g k s) : MulPost g s := by
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  exact KS.stage h

theorem w_pos (g : Geo) : 0 < 32 * g.w := by change 0 < 32 * (2 * g.n + 2); omega

theorem W_pos (g : Geo) : 0 < 16 * g.W := by change 0 < 16 * (2 * (2 * g.n + 2) + 2); omega

/-- A product, from two runs' stages before it. -/
theorem product_relCT {g : Geo} (pg : PubG g) {y x a t z : Nat} {live liveW ls : List Nat}
    {F : (Nat → Nat) → (Nat → Nat) → Prop} (I : ProdIdx y x a t z live liveW ls)
    (hb : PubA (productStep y x a t z)) :
    RelCT isa (RA (PP g a z live liveW ls F) (PP g a z live liveW ls F)) (VG.Impl.Rsa.X86.RecoverDetRt.product y x a t z)
      (RA (PI g y x a z live liveW ls F (32 * g.w)) (PI g y x a z live liveW ls F (32 * g.w))) :=
  VG.RelCT.seq (countNPub.relCT (fun _ h => prodCount_step h) (fun _ h => prodCount_step h))
    (loopA pg _ (w_pos g) hb (fun _ _ h => pI_stage h) fun _ _ hk h => prodBody_step I hk h)

section
variable [VG.Proof.Rsa.X86.BatchLaw]

theorem gcdA {g : Geo} (pg : PubG g) :
    RelCT isa (RA (Gpre g) (Gpre g)) (VG.Impl.Rsa.X86.GcdBatchRt.body wid) (RA (Gpost g) (Gpost g)) := by
  intro s t tr ur sf tf ⟨_, hs, ht⟩ es et
  have ps := wp_result (gcd_step hs) es
  have pt := wp_result (gcd_step ht) et
  obtain ⟨_, _, _, _, hs', _⟩ := hs
  obtain ⟨_, _, _, _, ht', _⟩ := ht
  have e := (VG.Proof.Rsa.X86.GcdBatchRt.Time.relBody (gcdFits hs') _ _ _ _ _ _
    ⟨hs'.gcdPre pg, ht'.gcdPre pg⟩ es et).1
  refine ⟨e, ?_, ps, pt⟩
  obtain ⟨_, _, _, _, ks, _⟩ := ps
  obtain ⟨_, _, _, _, kt, _⟩ := pt
  exact ks_agree pg ks kt

theorem det_relCT {g : Geo} (pg : PubG g) :
    RelCT isa (RA (D0 g) (D0 g)) det (RA (fun _ => True) (fun _ => True)) := by
  unfold det
  simp only [seqs]
  refine VG.RelCT.seq (deMinusPub.relCT (fun _ h => deMinus_step h) (fun _ h => deMinus_step h)) ?_
  -- The halvings.
  refine VG.RelCT.seq (R := RA (TwI g (32 * g.w)) (TwI g (32 * g.w))) ?_ ?_
  · have shape : twos = seqs (twosInit :: [.block countN] ++ [.loop twosBody .ne]) := rfl
    rw [shape]
    exact (pubs_relCT (loopA pg (TwI g) (w_pos g) twosBodyPub (fun _ _ h => twI_stage h)
      fun _ _ hk h => twosBody_step hk h) twosInitPub
      fun d hd => by rw [List.mem_singleton.mp hd]; exact countNPub).mono
      (fun s t ⟨a, hs, ht⟩ => ⟨a, twosHead_step hs, twosHead_step ht⟩) fun _ _ h => h
  -- The GCD.
  refine VG.RelCT.seq (gcdSetPub.relCT (fun _ h => gcdSet_step h) (fun _ h => gcdSet_step h)) ?_
  refine VG.RelCT.seq (gcdA pg) ?_
  -- The product.
  refine VG.RelCT.seq (R := RA
    (PI g aG wX3 wA wZ2 [1, aZero, VG.Impl.Rsa.X86.Recover.aN] [wA, wZ2, wX3] [sOkDE] (FA g) (32 * g.w))
    (PI g aG wX3 wA wZ2 [1, aZero, VG.Impl.Rsa.X86.Recover.aN] [wA, wZ2, wX3] [sOkDE] (FA g) (32 * g.w))) ?_ ?_
  · have shape : aProduct = seqs (VG.Impl.Rsa.X86.KeyRt.zeroWide wid wZ2 ::
        [VG.Impl.Rsa.X86.KeyRt.zeroWide wid wA] ++ [VG.Impl.Rsa.X86.RecoverDetRt.product aG wX3 wA wT wZ2]) := rfl
    rw [shape]
    exact (pubs_relCT (product_relCT pg aProductIdx stepAPub) zeroWZ2Pub
      fun d hd => by rw [List.mem_singleton.mp hd]; exact zeroWAPub).mono
      (fun s t ⟨a, hs, ht⟩ => ⟨a, aProductHead_step hs, aProductHead_step ht⟩) fun _ _ h => h
  -- The divisions.
  refine VG.RelCT.seq (divAPub.relCT (fun _ h => divA_step h) (fun _ h => divA_step h)) ?_
  refine VG.RelCT.seq (divBPub.relCT (fun _ h => divB_step h) (fun _ h => divB_step h)) ?_
  -- `b²`.
  refine VG.RelCT.seq (R := RA
    (PI g aBy wB wA wZ2 [aBy, aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN] [wA, wB, wN, wZ2]
      [sExact, sLt, sOkDE] FS (32 * g.w))
    (PI g aBy wB wA wZ2 [aBy, aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN] [wA, wB, wN, wZ2]
      [sExact, sLt, sOkDE] FS (32 * g.w))) ?_ ?_
  · have shape : square = seqs (VG.Impl.Rsa.X86.KeyRt.chain nar .adc aD aD aOne1 false ::
        [VG.Impl.Rsa.X86.KeyRt.copy nar aBy aD, VG.Impl.Rsa.X86.KeyRt.zeroWide wid wB,
          VG.Impl.Rsa.X86.KeyRt.copy nar (2 * wB) aD, VG.Impl.Rsa.X86.KeyRt.zeroWide wid wA] ++
        [VG.Impl.Rsa.X86.RecoverDetRt.product aBy wB wA wT wZ2]) := rfl
    rw [shape]
    refine (pubs_relCT (product_relCT pg squareIdx stepBPub) incPub fun d hd => ?_).mono
      (fun s t ⟨a, hs, ht⟩ => ⟨a, squareHead_step hs, squareHead_step ht⟩) fun _ _ h => h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    exacts [copyByPub, zeroWBPub, copyBPub, zeroWAPub]
  -- `b² - 4 n`, its square root and the factors.
  refine VG.RelCT.seq (minus4nPub.relCT (fun _ h => minus4n_step h) (fun _ h => minus4n_step h)) ?_
  refine VG.RelCT.seq (R := RA (fun _ => True) (fun _ => True)) ?_ factorsPub.relCT'
  have shape : sqrt = seqs (VG.Impl.Rsa.X86.KeyRt.copy nar aRm aZero ::
      [VG.Impl.Rsa.X86.KeyRt.copy nar aY aZero, .block countW] ++
      [.seq (.loop sqrtBody .ne) (VG.Impl.Rsa.X86.KeyRt.eqSFast nar sOk5 aRm aZero)]) := rfl
  rw [shape]
  refine (pubs_relCT (VG.RelCT.seq (loopA pg (SqI g) (W_pos g) sqrtBodyPub (fun _ _ h => sqI_stage h)
    fun _ _ hk h => sqrtBody_step hk h) eqOk5Pub.relCT') copyRmPub fun d hd => ?_).mono
    (fun s t ⟨a, hs, ht⟩ => ⟨a, sqrtHead_step hs, sqrtHead_step ht⟩) fun _ _ h => h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  exacts [copyYPub, countWPub]

end

end VG.Proof.Rsa.X86.Recover
end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Recover

theorem abiD_of {s : State} (h : (Spec.Rsa.recoverPrimesDetContract abi 96).pre s) :
    ABI s ∧ (arg s 7).toNat ≤ 8 := by
  sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  have rd : s.rd = [(caller s).buffer 4, (caller s).buffer 6, (caller s).buffer 8] := by
    dsimp only [caller, CallGeometry.buffer, byteAddr]
    with_reducible assumption
  have lengths : Spec.Rsa.lenValid (arg s 5).toNat := by with_reducible assumption
  have lo := lengths.1
  have hi := lengths.2
  refine ⟨?_, by omega⟩
  constructor
  all_goals try simp only [rd, bodyRegions, lowR, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  all_goals try dsimp only [caller, CallGeometry.buffer, byteAddr]
  all_goals repeat' apply And.intro
  all_goals first | with_reducible assumption | omega |
    exact Region.Disjoint.symm (by with_reducible assumption)

theorem calculatedD_entry {s t : State} (a : ABI s)
    (o : Outside (caller s).B 0 (caller s).Z s.mem t.mem) :
    calculatedD (caller s) t.mem = calculatedD (caller s) s.mem := by
  have same (i : Fin 3) : inputBytes (caller s) t.mem i = inputBytes (caller s) s.mem i := by
    exact scratch_bytes o (by have := (a.inputLength i).2; have := a.width.2.1; omega)
      (a.inApart _ (a.inputMember i) _ (by simp))
  unfold calculatedD
  rw [same 0, same 1, same 2]

theorem satisfiableD : ∃ s, (Spec.Rsa.recoverPrimesDetContract abi 96).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 16384 := by decide
  have a5 : arg satState 5 = 64 := by decide
  have a6 : arg satState 6 = 20480 := by decide
  have a7 : arg satState 7 = 1 := by decide
  have a8 : arg satState 8 = 24576 := by decide
  have a9 : arg satState 9 = 1 := by decide
  have a10 : arg satState 10 = 65536 := by decide
  have a11 : arg satState 11 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes,
    stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, e, esp, satState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using satState

end VG.Proof.Rsa.X86.Recover

section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Recover

theorem bodyD_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) (eSmall : (g.buffer 6).len ≤ 8) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.body s fun t => Inputs g t ∧ WrittenD g s.mem t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.Rsa.X86.RecoverDetRt.body VG.Impl.Rsa.X86.CrtValues.inputArgs
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 4 (by decide)).readSrc (h.arguments 5 (by decide)).readSrc)
    fun u ⟨p, c, m, k⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u len.lower len.upper
    (by rw [p]; exact h.inputFit 0)
    (by rw [p, k.2.1, k.2.2]; exact h.inputRead 0)
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using c)) fun v ⟨z, mv, kv⟩ => ?_)
  rw [p, m] at z
  have mem : v.mem = s.mem := mv.trans m
  have keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (k.mono (by decide)).trans (kv.mono (by decide))
  have hv := h.after keeps (by decide) (by decide) (by rw [mem]; exact Frame.refl _ _)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s.mem 0)) (g.args 5).toNat) z ?_ ?_
  · intro accepted
    have modulus : Spec.Rsa.modulusValid (inputValue g v.mem 0)
        (inputBytes g v.mem 0).length = true := by
      rw [mem]
      simp only [inputValue, inputBytes, bytesAt_length, CallGeometry.buffer]
      exact accepted
    have pLen : (g.buffer 0).len = (inputBytes g v.mem 0).length := by
      simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.pLen
    have qLen : (g.buffer 2).len = (inputBytes g v.mem 0).length := by
      simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.qLen
    refine WP.mono (sizedD_ok hv len modulus pLen qLen eSmall)
      fun t ⟨ht, result, frame, rest⟩ => ?_
    exact ⟨ht, mem ▸ result, mem ▸ frame, keeps.trans rest⟩
  · intro rejected
    have failed : calculatedD g s.mem = none := by
      unfold calculatedD Spec.Rsa.primesKeyDet
      dsimp only
      have ln : (inputBytes g s.mem 0).length = (g.args 5).toNat := bytesAt_length _ _ _
      rw [ln, rejected]
      rfl
    refine WP.mono (failure_ok hv) fun t ⟨ht, p, q, status, frame, rest⟩ => ?_
    exact ⟨ht, writtenD_failure failed p q status, mem ▸ frame, keeps.trans (rest.mono (by decide))⟩

theorem operationD_ok {s : State} (a : ABI s) (eSmall : (arg s 7).toNat ≤ 8) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.code s fun t => WrittenD (caller s) s.mem t ∧ abiPreserved s t := by
  have low : 16 ≤ (caller s).Z := by have := a.used; omega
  have high : (caller s).Z ≤ 2 ^ 64 := by have := a.scratchBound; omega
  unfold VG.Impl.Rsa.X86.RecoverDetRt.code
  refine WP.seq (WP.mono (installed_ok a) fun u ⟨inputs, saved, k, o⟩ => ?_)
  refine WP.seq (WP.mono (bodyD_ok inputs a.lengths_ok eSmall) fun v ⟨iv, written, frame, kv⟩ => ?_)
  have saveV := bodyFrame_saved inputs frame saved
  have whole : Frame (caller s).writes s.mem v.mem := by
    have start := outside_frame o (by omega)
    simp only [off, BitVec.add_zero] at start
    exact (start.mono (by simp [CallGeometry.writes])).trans (bodyFrame_full low frame)
  have ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 :=
    whole.readW (Region.contains_self _ 4) a.retApartW (by decide)
  refine WP.mono (entryRestore_ok iv.ws.workspace low saveV) fun t restored => ?_
  refine ⟨?_, publicRestored_abi restored ((kv.1 _ (by decide)).trans (k.1 _ (by decide))) ret⟩
  unfold WrittenD at written ⊢
  rw [calculatedD_entry a o] at written
  rw [restored.mem, restored.other .eax (by decide)]
  exact written

theorem correctD (s : State) (h : (Spec.Rsa.recoverPrimesDetContract abi 96).pre s) :
    ∃ trace t, Exec isa VG.Impl.Rsa.X86.RecoverDetRt.code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.recoverPrimesDetContract abi 96).post s t := by
  obtain ⟨a, eSmall⟩ := abiD_of h
  obtain ⟨trace, t, run, written, preserved⟩ := operationD_ok a eSmall
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold WrittenD outputBuffersD calculatedD inputBytes CallGeometry.buffer caller at written
  change Spec.Rsa.writtenAll t.mem
    [(VG.Proof.Dsa.X86.argumentPointer s 0, (arg s 1).toNat),
      (VG.Proof.Dsa.X86.argumentPointer s 2, (arg s 3).toNat)] (t.gpr .eax) _ at written
  rw [a.pLen, a.qLen] at written
  exact written

end VG.Proof.Rsa.X86.Recover
end


@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

theorem argumentsD_eq {s t : State} (h : (Spec.Rsa.recoverPrimesDetContract abi 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 12, arg s i = arg t i := by
  sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes] at h
  sig_split h
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem modulusD_eq {s t : State} (h : (Spec.Rsa.recoverPrimesDetContract abi 96).pub s t) :
    inputBytes (caller s) s.mem 0 = inputBytes (caller t) t.mem 0 := by
  have args := (argumentsD_eq h).2
  have leak : (inputBytes (caller s) s.mem 0 ++ inputBytes (caller s) s.mem 1).map (·.toNat) =
      (inputBytes (caller t) t.mem 0 ++ inputBytes (caller t) t.mem 1).map (·.toNat) := by
    sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes] at h
    exact h.2.1
  have lenN : (inputBytes (caller s) s.mem 0).length = (inputBytes (caller t) t.mem 0).length := by
    simp only [inputBytes, VG.Proof.Bignum.bytesAt_length, caller, CallGeometry.buffer]
    exact congrArg BitVec.toNat (args 5 (by decide))
  have both := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp leak
  exact (List.append_inj both lenN).1

end VG.Proof.Rsa.X86.Recover
end

section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (relCT_narrow)

/-- Two runs of `sized` over the same geometry, its writable regions apart from the arguments. -/
def SizedPairD (g : CallGeometry) (s t : State) : Prop :=
  Inputs g s ∧ Inputs g t ∧ PubG g.toGeo ∧
  Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true ∧
  Spec.Rsa.modulusValid (inputValue g t.mem 0) (inputBytes g t.mem 0).length = true

theorem sizedD_relCT (g : CallGeometry) (len : Lengths g) :
    RelCT isa (SizedPairD g) VG.Impl.Rsa.X86.RecoverDetRt.sized (fun _ _ => True) := by
  have shape : VG.Impl.Rsa.X86.RecoverDetRt.sized = VG.Impl.Rsa.X86.Keys.seqs
      (VG.Impl.Rsa.X86.RecoverRt.loads :: [VG.Impl.Rsa.X86.RecoverRt.prod] ++
        [.seq VG.Impl.Rsa.X86.RecoverDetRt.det VG.Impl.Rsa.X86.RecoverRt.stores]) := rfl
  rw [shape]
  intro s t tr ur sf tf ⟨hs, ht, pg, vs, vt⟩ es et
  have rel := pubs_relCT (VG.RelCT.seq (det_relCT pg) storesPub.relCT') loadsPub
    (fun d hd => by rw [List.mem_singleton.mp hd]; exact prodPub)
  exact ⟨(rel _ _ _ _ _ _ ⟨inputs_agree pg hs ht, pre_step hs len vs, pre_step ht len vt⟩ es et).1, trivial⟩

/-- Two runs of `sized` from the states themselves: the arguments apart from the working space and the
outputs. -/
def SizedAtD (g : CallGeometry) (s t : State) : Prop :=
  Inputs g s ∧ Inputs g t ∧ (∀ r ∈ narrowW g, Region.Disjoint ⟨g.sp.setWidth 64, 52⟩ r) ∧
  Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true ∧
  Spec.Rsa.modulusValid (inputValue g t.mem 0) (inputBytes g t.mem 0).length = true

theorem sizedNarrowD_relCT (g : CallGeometry) (len : Lengths g) (eSmall : (g.buffer 6).len ≤ 8) :
    RelCT isa (SizedAtD g) VG.Impl.Rsa.X86.RecoverDetRt.sized (fun _ _ => True) := by
  have len' : Lengths (narrowG g) :=
    ⟨len.lower, len.upper, len.width, len.scratch, len.bytes, len.pLen, len.qLen⟩
  refine relCT_narrow (Pn := SizedPairD (narrowG g)) (fun s => s.rd ++ s.wr)
    (fun _ => narrowW g) (fun s₁ s₂ ⟨h₁, h₂, apart, v₁, v₂⟩ => ?_)
    (sizedD_relCT (narrowG g) len')
  have cov : ∀ {s : State}, Inputs g s → Covers (narrowW g) s.wr := by
    intro s h
    refine Covers.cons (Covers.of_mem fun r hr => ?_) (Covers.cons (Covers.one (h.outputWrite 0))
      (Covers.cons (Covers.one (h.outputWrite 1)) Covers.nil))
    rw [List.mem_singleton.mp hr]
    exact h.ws.workspace.wr
  have pLen : (g.buffer 0).len = (g.args 5).toNat := congrArg BitVec.toNat len.pLen
  have qLen : (g.buffer 2).len = (g.args 5).toNat := congrArg BitVec.toNat len.qLen
  have wp : ∀ {s : State}, Inputs g s →
      Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true →
      ∃ F, WP isa VG.Impl.Rsa.X86.RecoverDetRt.sized (s.withRegions (s.rd ++ s.wr) (narrowW g)) F :=
    fun h v => ⟨_, sizedD_ok (narrow_inputs h) len' v
      (by simp only [inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer] at pLen ⊢; exact pLen)
      (by simp only [inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer] at qLen ⊢; exact qLen)
      eSmall⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov h₁)), cov h₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov h₂)), cov h₂, wp h₁ v₁, wp h₂ v₂,
    narrow_inputs h₁, narrow_inputs h₂, ⟨h₁.top, apart⟩, v₁, v₂⟩

/-- Recovery needs only the public modulus bytes. -/
def BodyPairD (g : CallGeometry) (s t : State) : Prop :=
  Pair g s t ∧ (∀ r ∈ narrowW g, Region.Disjoint ⟨g.sp.setWidth 64, 52⟩ r) ∧
    inputBytes g s.mem 0 = inputBytes g t.mem 0

theorem bodyD_relCT (g : CallGeometry) (len : Lengths g) (eSmall : (g.buffer 6).len ≤ 8) :
    RelCT isa (BodyPairD g) VG.Impl.Rsa.X86.RecoverDetRt.body (fun _ _ => True) := by
  let r := fun s t => BodyPairD g s t ∧
    s.zf = some (Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length) ∧
    t.zf = some (Spec.Rsa.modulusValid (inputValue g t.mem 0) (inputBytes g t.mem 0).length)
  have branch : RelCT isa r (.ite .e VG.Impl.Rsa.X86.RecoverDetRt.sized VG.Impl.Rsa.X86.Recover.failure)
      (fun _ _ => True) := by
    have flags : ∀ s t, r s t → isa.eval .e s = isa.eval .e t := by
      intro s t h
      change s.zf = t.zf
      rw [h.2.1, h.2.2]
      unfold inputValue
      rw [h.1.2.2]
    apply VG.RelCT.ite (M := isa) (c := .e) (P := r) flags
    · apply (sizedNarrowD_relCT g len eSmall).mono
      · intro s t ⟨h, cond⟩
        have vs := Option.some.inj (h.2.1.symm.trans cond)
        have vt := Option.some.inj (h.2.2.symm.trans ((flags s t h).symm.trans cond))
        exact ⟨h.1.1.left, h.1.1.right, h.1.2.1, vs, vt⟩
      · intro s t h; exact h
    · exact (failure_relCT g).mono (fun _ _ h => h.1.1.1) (fun _ _ h => h)
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨pair, apart, modulus⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := (modulus_relCT g _ _ _ _ _ _ pair e1 f1).1
      obtain ⟨zs, ms, ks⟩ := wp_result (modulus_ok pair.left len) e1
      obtain ⟨zt, mt, kt⟩ := wp_result (modulus_ok pair.right len) f1
      have next : BodyPairD g u v := by
        refine ⟨pair.keepMem ks kt (by decide) (by decide) ms mt, ?_⟩
        rw [ms, mt]
        exact ⟨apart, modulus⟩
      have vs : u.zf = some (Spec.Rsa.modulusValid (inputValue g u.mem 0) (inputBytes g u.mem 0).length) := by
        rw [ms]
        simp only [inputValue, inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer]
        exact zs
      have vt : v.zf = some (Spec.Rsa.modulusValid (inputValue g v.mem 0) (inputBytes g v.mem 0).length) := by
        rw [mt]
        simp only [inputValue, inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer]
        exact zt
      have eq2 := (branch _ _ _ _ _ _ ⟨next, vs, vt⟩ e2 f2).1
      exact ⟨by rw [eq1, eq2], trivial⟩

theorem operationD_trace {s t : State} (a : ABI s) (b : ABI t) (eSmall : (arg s 7).toNat ≤ 8)
    (args : ∀ i < 12, arg s i = arg t i) (sp : s.gpr .esp = t.gpr .esp)
    (modulus : inputBytes (caller s) s.mem 0 = inputBytes (caller t) t.mem 0)
    {tr ur : List Leak} {sf tf : State} (es : Exec isa VG.Impl.Rsa.X86.RecoverDetRt.code s tr sf)
    (et : Exec isa VG.Impl.Rsa.X86.RecoverDetRt.code t ur tf) :
    tr = ur := by
  have a4 := args 4 (by decide)
  have a5 := args 5 (by decide)
  have a10 := args 10 (by decide)
  have a11 := args 11 (by decide)
  have a0 := args 0 (by decide)
  have a1 := args 1 (by decide)
  have a2 := args 2 (by decide)
  have a3 := args 3 (by decide)
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := (entry_relCT _ _ _ _ _ _
        ⟨sp, a10, (a.stackArgument (by decide : 10 < 12)).readSrc,
          (b.stackArgument (by decide : 10 < 12)).readSrc⟩ e1 f1).1
      obtain ⟨hs, _, ks, os⟩ := wp_result (installed_ok a) e1
      obtain ⟨ht, _, kt, ot⟩ := wp_result (installed_ok b) f1
      have hv : Inputs (caller s) v := by
        refine ht.geoEq (by simp only [caller, argumentPointer, a10]) (by simp only [caller, a11])
          (by simp only [caller, a5]) sp ?_ fun i hi => args i hi
        change s.wr = t.wr
        rw [a.wr, b.wr]
        simp only [caller, CallGeometry.buffer, argumentPointer, argAddr, a0, a1, a2, a3, a10, a11, sp]
      have pair : Pair (caller s) u v :=
        ⟨hs, hv, (ks.1 _ (by decide)).trans (sp.trans (kt.1 _ (by decide)).symm)⟩
      have same : inputBytes (caller s) u.mem 0 = inputBytes (caller s) v.mem 0 := by
        have ns := VG.Proof.Bignum.scratch_bytes os (by have := a.lengths.2; change (arg s 5).toNat ≤ _; omega)
          (a.inApart _ (a.inputMember 0) _ (by simp))
        have nt := VG.Proof.Bignum.scratch_bytes ot (by have := b.lengths.2; change (arg t 5).toNat ≤ _; omega)
          (b.inApart _ (b.inputMember 0) _ (by simp))
        change inputBytes (caller s) u.mem 0 = inputBytes (caller s) s.mem 0 at ns
        change inputBytes (caller t) v.mem 0 = inputBytes (caller t) t.mem 0 at nt
        have align : inputBytes (caller s) v.mem 0 = inputBytes (caller t) v.mem 0 := by
          simp only [inputBytes, caller, CallGeometry.buffer]
          change Spec.Rsa.bytesAt v.mem (byteAddr (arg s 4)) (arg s 5).toNat =
            Spec.Rsa.bytesAt v.mem (byteAddr (arg t 4)) (arg t 5).toNat
          rw [a4, a5]
        exact ns.trans (modulus.trans (align.trans nt).symm)
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          have apart : ∀ r ∈ narrowW (caller s),
              Region.Disjoint ⟨(caller s).sp.setWidth 64, 52⟩ r := fun r hr =>
            VG.X86.Taint.frame_disjoint (n := 48)
              (by change (s.gpr .esp).toNat + 4 + 48 ≤ _; have := a.stackBound; omega) (a.retApart r hr)
              (a.argsApart r hr)
          have eq2 := (bodyD_relCT (caller s) a.lengths_ok eSmall _ _ _ _ _ _ ⟨pair, apart, same⟩ e2 f2).1
          obtain ⟨hx, _, _, kx⟩ := wp_result (bodyD_ok hs a.lengths_ok eSmall) e2
          obtain ⟨hy, _, _, ky⟩ := wp_result (bodyD_ok hv a.lengths_ok eSmall) f2
          have next := pair.after hx hy kx ky (by decide)
          have eq3 := (publicRestore_relCT _ _ _ _ _ _ next.workspace e3 f3).1
          rw [eq1, eq2, eq3]

theorem constantTimeD : ConstantTime isa (Spec.Rsa.recoverPrimesDetContract abi 96).pre
    (Spec.Rsa.recoverPrimesDetContract abi 96).pub VG.Impl.Rsa.X86.RecoverDetRt.code := by
  intro s t tr ur sf tf hs ht h es et
  have args := argumentsD_eq h
  obtain ⟨a, eSmall⟩ := abiD_of hs
  exact operationD_trace a (abiD_of ht).1 eSmall args.2 args.1 (modulusD_eq h) es et

theorem verifiedD : Verified target VG.Impl.Rsa.X86.RecoverDetRt.code (Spec.Rsa.recoverPrimesDetContract abi 96) :=
  ⟨correctD, constantTimeD, satisfiableD⟩

end VG.Proof.Rsa.X86.Recover
end
