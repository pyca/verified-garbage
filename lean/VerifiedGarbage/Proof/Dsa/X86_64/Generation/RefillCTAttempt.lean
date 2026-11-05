module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTWindow
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillAttempt
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterCTState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccessCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroupCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPhaseStableCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTWindow
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillAttempt
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccessCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroupCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPhaseStableCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Timing of one seed of the refillable-tape search

A seed's attempt (`Refill.refillAttempt`) is the finite search's
(`seedAttempt_ct`) with the window around its generator search: the window
(`window_ct`), the candidates' octets counted as consumed, and the status of
a window cut short. Each branches only on the status word and the window's
length, which the seed's public inputs fix. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Mgf1.X86_64 (sp)

variable {checkName : String}

theorem domainFinishBefore_frame {pLen qLen : Nat} {d : DomainFinishPublic} {s t : State}
    (h : DomainFinishBefore pLen qLen d s) {W : Nat → BitVec 64} (hm : GenerationMemory d.context W t)
    (hf : Frame [⟨d.context.geo.F, frameBytes⟩] s.mem t.mem) : DomainFinishBefore pLen qLen d t := by
  obtain ⟨_, bp, bq, bg, hp, hq⟩ := h
  have pn : d.context.geo.pLen ≤ 384 := by rcases d.context.geo.width with hh | hh | hh <;> omega
  have qn : d.context.geo.qLen ≤ 32 := by rcases d.context.geo.qWidth with hh | hh <;> omega
  refine ⟨⟨W, hm⟩, ?_, ?_, ?_, hp, hq⟩
  · rw [ctFrame_bytes hf (d.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega))]; exact bp
  · rw [ctFrame_bytes hf (d.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega))]; exact bq
  · rw [ctFrame_bytes hf (d.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega))]; exact bg

theorem seedGeneratorAfter_pins (pLen qLen : Nat) : Pins (SeedGeneratorAfter pLen qLen) [.rsp] := by
  intro g s t ⟨⟨_, hs, _⟩, _⟩ ⟨⟨_, ht, _⟩, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.layout.rsp.trans ht.layout.rsp.symm

/-! ## The candidates' octets consumed -/

theorem consumed_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorAfter pLen qLen g s) :
    WP isa (.block Impl.Dsa.X86_64.Generation.Refill.windowConsumed) s (SeedGeneratorAfter pLen qLen g) := by
  obtain ⟨⟨W, hm, h19⟩, next⟩ := h
  refine WP.mono (refillConsumed_ok hm) fun t ⟨mt, ft, _, _⟩ => ?_
  exact ⟨⟨_, mt, by simpa [upd] using h19⟩, fun hs => domainFinishBefore_frame (next hs) mt ft⟩

theorem consumed_ct (pLen qLen : Nat) :
    RelCT isa (Two (SeedGeneratorAfter pLen qLen)) (.block Impl.Dsa.X86_64.Generation.Refill.windowConsumed)
      (Two (SeedGeneratorAfter pLen qLen)) :=
  two_piece [.rsp] (seedGeneratorAfter_pins pLen qLen) (by taint_decide) fun _ _ h => consumed_ready h

/-! ## A window cut short -/

/-- The status after `windowShort`: a window shorter than `windowBytes`
without a generator ran out. -/
def SeedGeneratorPublic.shortStatus (g : SeedGeneratorPublic) : BitVec 64 :=
  if g.status = 1 then 1 else
    if g.seed.context.hs.bytes.length < Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen
    then 0 else g.status

def ShortAfter (pLen qLen : Nat) (g : SeedGeneratorPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory g.seed.context W s ∧ W 19 = g.shortStatus) ∧
  (g.shortStatus = 1 → DomainFinishBefore pLen qLen g.finish s)

def ShortChecked (pLen qLen : Nat) (g : SeedGeneratorPublic) (s : State) : Prop :=
  SeedGeneratorAfter pLen qLen g s ∧ isa.eval .e s = some (g.status == 1)

def ShortCompared (pLen qLen : Nat) (g : SeedGeneratorPublic) (s : State) : Prop :=
  SeedGeneratorAfter pLen qLen g s ∧ g.status ≠ 1 ∧
  isa.eval .b s = some (decide (g.seed.context.hs.bytes.length <
    Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen))

theorem seedGeneratorAfter_keep {pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorAfter pLen qLen g s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    SeedGeneratorAfter pLen qLen g t :=
  seedGeneratorAfter_congr h hm hk

theorem shortStatus_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorAfter pLen qLen g s) :
    WP isa (.block successStatus) s (ShortChecked pLen qLen g) := by
  obtain ⟨⟨W, hm, h19⟩, _⟩ := id h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (successStatus_ok hm.layout R) fun t ⟨hz, he, hk⟩ => ?_
  exact ⟨seedGeneratorAfter_keep h he hk, by simp only [eval, hz, h19]⟩

theorem shortLength_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : ShortChecked pLen qLen g s) (he : isa.eval .e s = some false) :
    WP isa (.block [.mov .rax (.mem (sp 96)), .alu .cmp .rax (.imm (BitVec.ofNat 32
        (Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)))]) s
      (ShortCompared pLen qLen g) := by
  obtain ⟨hg, hs⟩ := h
  obtain ⟨⟨W, hm, _⟩, _⟩ := id hg
  obtain ⟨V, R⟩ := hm.rep
  have pn : g.seed.context.geo.pLen ≤ 384 := by rcases g.seed.context.geo.width with hh | hh | hh <;> omega
  have h12 : W 12 = BitVec.ofNat 64 g.seed.context.hs.bytes.length :=
    (hm.slots 12 (by simp [generationSlots])).trans g.seed.context.hLengthSlot
  have ne : g.status ≠ 1 := by
    intro e; have := hs.symm.trans he; simp [e] at this
  refine WP.mono (shortCheck_ok hm.layout R h12 g.seed.context.hs.size (windowBytes_lt _ pn))
    fun t ⟨hc, hmt, kt⟩ => ?_
  exact ⟨seedGeneratorAfter_keep hg hmt kt, ne, by simp only [eval, hc]⟩

theorem seedGeneratorPublic_status (g : SeedGeneratorPublic) : g.status = 1 ∨ g.status = 3 := by
  unfold SeedGeneratorPublic.status; split <;> simp

theorem shortAccepted_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : ShortChecked pLen qLen g s) (he : isa.eval .e s = some true) :
    WP isa (.block []) s (ShortAfter pLen qLen g) := by
  obtain ⟨⟨⟨W, hm, h19⟩, next⟩, hs⟩ := h
  have e : g.status = 1 := by
    have := hs.symm.trans he; simpa using this
  have sh : g.shortStatus = 1 := by
    unfold SeedGeneratorPublic.shortStatus; rw [ite_eq_left e]
  exact WP.block_nil ⟨⟨W, hm, h19.trans (e.trans sh.symm)⟩, fun _ => next e⟩

theorem shortRanOut_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : ShortCompared pLen qLen g s) (hb : isa.eval .b s = some true) :
    WP isa (.block (stackStatus 0)) s (ShortAfter pLen qLen g) := by
  obtain ⟨⟨⟨W, hm, h19⟩, _⟩, ne, hc⟩ := h
  have short : g.seed.context.hs.bytes.length <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen := by
    have := hc.symm.trans hb; simpa using this
  have sh : g.shortStatus = 0 := by
    unfold SeedGeneratorPublic.shortStatus; rw [ite_eq_right ne, ite_eq_left short]
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (stackStatus_ok hm.layout R 0 (by decide)) fun t ⟨Lt, Rt, ot, kt⟩ => ?_
  have mt := hm.frame Lt ⟨V, Rt⟩ (fun k hk => by
    have : k ≠ 19 := by rintro rfl; exact absurd hk (by decide)
    simp [upd, this]) (GenerationContext.status_frame ot) kt.2.1 kt.2.2
  exact ⟨⟨_, mt, by simp [upd, sh]⟩, fun h1 => by rw [sh] at h1; exact absurd h1 (by decide)⟩

theorem shortFull_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : ShortCompared pLen qLen g s) (hb : isa.eval .b s = some false) :
    WP isa (.block []) s (ShortAfter pLen qLen g) := by
  obtain ⟨⟨⟨W, hm, h19⟩, _⟩, ne, hc⟩ := h
  have full : ¬ g.seed.context.hs.bytes.length <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen := by
    have := hc.symm.trans hb; simpa using this
  have sh : g.shortStatus = g.status := by
    unfold SeedGeneratorPublic.shortStatus; rw [ite_eq_right ne, ite_eq_right full]
  exact WP.block_nil ⟨⟨W, hm, h19.trans sh.symm⟩, fun h1 => absurd (sh.symm.trans h1) ne⟩

theorem shortChecked_pins (pLen qLen : Nat) : Pins (ShortChecked pLen qLen) [.rsp] :=
  fun g s t hs ht => seedGeneratorAfter_pins pLen qLen g s t hs.1 ht.1

theorem shortCompared_pins (pLen qLen : Nat) : Pins (ShortCompared pLen qLen) [.rsp] :=
  fun g s t hs ht => seedGeneratorAfter_pins pLen qLen g s t hs.1 ht.1

theorem windowShort_ct (pLen qLen : Nat) (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two fun g s => SeedGeneratorAfter pLen qLen g s ∧ g.seed.context.geo.pLen = pLen)
      (Impl.Dsa.X86_64.Generation.Refill.windowShort pLen)
      (Two fun g s => ShortAfter pLen qLen g s) := by
  have tc : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (sp 96)), .alu .cmp .rax
      (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.windowBytes pLen)))]) hc).isSome = true := by
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold Impl.Dsa.X86_64.Generation.Refill.windowShort
  refine RelCT.seq (two_piece (Ψ := fun g s => ShortChecked pLen qLen g s ∧ g.seed.context.geo.pLen = pLen)
    [.rsp] (fun g s t hs ht => seedGeneratorAfter_pins pLen qLen g s t hs.1 ht.1) (by taint_decide)
    fun g s h => WP.mono (shortStatus_ready h.1) fun _ ht => ⟨ht, h.2⟩) ?_
  refine two_ite (fun g s t hs ht => hs.1.2.trans ht.1.2.symm) ?_ ?_
  · exact two_post (two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide))
      fun g s h => shortAccepted_ready h.1.1 h.2
  refine RelCT.seq (two_piece (Ψ := ShortCompared pLen qLen) [.rsp]
    (fun g s t hs ht => shortChecked_pins pLen qLen g s t hs.1.1 ht.1.1) tc.choose_spec fun g s h => ?_) ?_
  · obtain ⟨⟨hc, hp⟩, he⟩ := h
    subst pLen
    exact shortLength_ready hc he
  refine two_ite (fun g s t hs ht => hs.2.2.trans ht.2.2.symm) ?_ ?_
  · exact two_piece [.rsp] (fun g s t hs ht => shortCompared_pins pLen qLen g s t hs.1 ht.1) (by taint_decide)
      fun g s h => shortRanOut_ready h.1 h.2
  · exact two_post (two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide))
      fun g s h => shortFull_ready h.1 h.2

/-! ## After the seed's `p`: the window, the generator and the parameters -/

theorem shortAfter_congr {pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (h : ShortAfter pLen qLen g s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) : ShortAfter pLen qLen g t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  refine ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => ?_⟩
  obtain ⟨⟨Wt, ht⟩, bp, bq, bg, hp, hq⟩ := next ha
  exact ⟨⟨Wt, ht.congr hm hk⟩, hm ▸ bp, hm ▸ bq, hm ▸ bg, hp, hq⟩

theorem refillTail_ct (M : Mont) (Sq : MontS) (n pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedGeneratorBefore n pLen qLen))
      (VG.Impl.Bignum.X86_64.seqs [Impl.Dsa.X86_64.Generation.Refill.window pLen,
        generatorSearch Sq.mm M.mm pLen, .block Impl.Dsa.X86_64.Generation.Refill.windowConsumed,
        Impl.Dsa.X86_64.Generation.Refill.windowShort pLen,
        onSuccess (finishDomain (checkName := checkName) Sq.mm M.mm pLen qLen)]) (fun _ _ => True) := by
  have width : pLen = 128 ∨ pLen = 256 ∨ pLen = 384 := by
    rcases sizes with h | h | h <;> simp [h.1]
  unfold VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs
    VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs
  refine RelCT.seq (window_ct n pLen qLen width) (two_map SeedGeneratorPublic.windowed (fun _ _ h => h) ?_)
  refine RelCT.seq (two_post (Ψ := fun g s => SeedGeneratorAfter pLen qLen g s ∧ g.seed.context.geo.pLen = pLen)
    (seedGenerator_ct M Sq n pLen qLen width)
    (fun g s h => WP.mono (seedGenerator_after M Sq h) fun _ ht => ⟨ht, seedGeneratorBefore_pLen h⟩)) ?_
  refine RelCT.seq (two_piece (Ψ := fun g s => SeedGeneratorAfter pLen qLen g s ∧ g.seed.context.geo.pLen = pLen)
    [.rsp] (fun g s t hs ht => seedGeneratorAfter_pins pLen qLen g s t hs.1 ht.1) (by taint_decide)
    fun g s h => WP.mono (consumed_ready h.1) fun _ ht => ⟨ht, h.2⟩) ?_
  refine RelCT.seq (windowShort_ct pLen qLen width) ?_
  apply onSuccess_ct (Φ := ShortAfter pLen qLen) (fun g : SeedGeneratorPublic => g.seed.context)
    SeedGeneratorPublic.shortStatus (fun _ _ h => h.1) (fun _ _ _ h hm hk => shortAfter_congr h hm hk)
  exact two_map SeedGeneratorPublic.finish (fun _ _ h => h.1.2 h.2)
    (finishDomain_ct (checkName := checkName) M Sq pLen qLen sizes)

/-! ## The seed -/

theorem refillPrimeFinish_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore n pLen qLen))
      (.seq (primeSearch H.sha1 H.sha256 T.run pLen qLen)
        (onSuccess (VG.Impl.Bignum.X86_64.seqs [Impl.Dsa.X86_64.Generation.Refill.window pLen,
          generatorSearch Sq.mm M.mm pLen, .block Impl.Dsa.X86_64.Generation.Refill.windowConsumed,
          Impl.Dsa.X86_64.Generation.Refill.windowShort pLen,
          onSuccess (finishDomain (checkName := checkName) Sq.mm M.mm pLen qLen)])))
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (seedPrime_ct H T n hn pLen qLen sizes)
    (fun _ _ h => seedPrime_after H T h)) ?_
  apply onSuccess_ct (Φ := SeedPrimeAfter n pLen qLen) SeedPublic.context SeedPublic.primeStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedPrimeAfter_congr h hm hk)
  exact (refillTail_ct (checkName := checkName) M Sq n pLen qLen sizes).mono
    (fun _ _ h => seedPrimeAfter_related h) (fun _ _ h => h)

theorem refillAttempt_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedAttemptBefore n pLen qLen))
      (Impl.Dsa.X86_64.Generation.Refill.refillAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run
        pLen qLen) (fun _ _ => True) := by
  have width : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  unfold Impl.Dsa.X86_64.Generation.Refill.refillAttempt
  refine RelCT.seq (two_post
    (two_map (fun p : SeedPublic => p) (fun _ _ h => h.1) (seedSubgroup_ct H T n hn qLen width))
    (fun _ _ h => seedSubgroup_after H T h.1 h.2)) ?_
  apply onSuccess_ct (Φ := SeedSubgroupAfter n pLen qLen) SeedPublic.context SeedPublic.subgroupStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedSubgroupAfter_congr h hm hk)
  exact two_map SeedPublic.afterSubgroup (fun _ _ h => h.1.2 h.2)
    (refillPrimeFinish_ct (checkName := checkName) H M Sq T n hn pLen qLen sizes)

end VG.Proof.Dsa.X86_64.Generation
