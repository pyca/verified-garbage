module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCTFinish
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCorrect
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Dispatch
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySpill
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCTFinish
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCorrect
meta import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Dispatch
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch

-- separate module: its proofs build in parallel with the correctness ones, `RefillCorrect`

/-! # The refillable-tape search on AArch64 is constant time

`refill_ct`: two runs from states whose public data agree (the arguments
in registers, the stack pointer, `state`'s four words and the whole tape
`rand`) leak the same trace. The search's public state on entry
(`EntryPub`) is a function of that data (`entryPub_eq`); the entry, the
dispatch on the width, the controller (`controller_ct`) and the end
(`finish_ct`) keep the two runs' states related. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation.Refill
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 (upd)
open VG.Proof.Dsa.AArch64.Generation

/-! ## Public data -/

/-- What two runs' public data agree on. -/
structure RefillAgree (s t : State) : Prop where
  sp : s.sp = t.sp
  regs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], s.gpr r = t.gpr r
  seeds : (s.mem.readW (s.gpr .x7) 64).toNat = (t.mem.readW (t.gpr .x7) 64).toNat
  width : refillPLen s = refillPLen t
  rand : Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .x3) (t.gpr .x4).toNat

theorem refill_wordsAt_four (m : Mem) (p : Addr) : (Spec.Rsa.wordsAt m p 4).map (·.toNat) =
    [(m.readW (p + BitVec.ofNat 64 0) 64).toNat, (m.readW (p + 8) 64).toNat, (m.readW (p + 16) 64).toNat,
      (m.readW (p + 24) 64).toNat] := rfl

theorem refill_agree {s t : State} (h : (Spec.Dsa.parameterSearchContract abi refillStack).pub s t) :
    RefillAgree s t := by
  sig_pub [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [refill_wordsAt_four, refill_wordsAt_four] at hl
  have hp := List.append_inj hl rfl
  simp only [List.cons.injEq] at hp
  refine ⟨hsp, ?_, by simpa only [BitVec.add_zero] using hp.1.1, hp.1.2.1,
    (List.map_inj_right fun a b e => BitVec.eq_of_toNat_eq e).mp hp.2⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem GenerationTape.heq_of {p q : GenerationGeometry} {a : GenerationTape p} {b : GenerationTape q}
    (hg : p = q) (hp : a.ptr = b.ptr) (hb : a.bytes = b.bytes) : HEq a b := by
  cases hg; cases a; cases b; cases hp; cases hb; rfl

theorem GenerationContext.ext' {a b : GenerationContext} (hg : a.geo = b.geo) (hs : HEq a.seeds b.seeds)
    (hh : HEq a.hs b.hs) (hr : HEq a.rand b.rand) (hw : a.saved = b.saved) : a = b := by
  cases a; cases b; cases hg; cases hs; cases hh; cases hr; cases hw; rfl

theorem refillContext_eq {pBytes : Nat} {s t : State} (hs : RefillABI pBytes s) (ht : RefillABI pBytes t)
    (a : RefillAgree s t) : refillContext hs = refillContext ht := by
  have hg : refillGeometry hs = refillGeometry ht := by
    have ext : ∀ {x y : GenerationGeometry}, x.B = y.B → x.F = y.F → x.pLen = y.pLen → x.qLen = y.qLen → x = y := by
      intro x y hB hF hp hq
      cases x; cases y
      dsimp only at hB hF hp hq
      subst hB; subst hF; subst hp; subst hq; rfl
    exact ext (a.regs .x5 (by simp)) (by simp only [refillGeometry, refillBase, a.sp]) rfl rfl
  have tape : HEq (randTape hs) (randTape ht) :=
    GenerationTape.heq_of hg (a.regs .x3 (by simp)) a.rand
  refine GenerationContext.ext' hg tape ?_ tape ?_
  · refine GenerationTape.heq_of hg ?_ ?_
    · show off (s.gpr .x3) 0 = off (t.gpr .x3) 0
      rw [a.regs .x3 (by simp)]
    · show ((randTape hs).bytes.drop 0).take 0 = ((randTape ht).bytes.drop 0).take 0
      simp only [List.take_zero]
  · funext k
    show refillWords pBytes s k = refillWords pBytes t k
    unfold refillWords
    split <;> simp only [a.regs .x0 (by simp), a.regs .x1 (by simp), a.regs .x3 (by simp),
      a.regs .x4 (by simp), a.regs .x5 (by simp)]

/-! ## The entry -/

/-- The search's public state on entry. -/
structure EntryPub where
  pBytes : Nat
  ctx : GenerationContext
  n₀ : Nat
  st : BitVec 64
  us : BitVec 64

def entryPub {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀) : EntryPub :=
  ⟨pBytes, refillContext h, (s₀.mem.readW (s₀.gpr .x7) 64).toNat, s₀.gpr .x7, s₀.gpr .x2⟩

def EntryAt (E : EntryPub) (u : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI E.pBytes s₀), RefillAllocated h u ∧ refillContext h = E.ctx ∧
    s₀.gpr .x7 = E.st ∧ s₀.gpr .x2 = E.us ∧ (s₀.mem.readW (s₀.gpr .x7) 64).toNat = E.n₀

def Entered (E : EntryPub) (v : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI E.pBytes s₀) (W : Nat → BitVec 64), EntryDone h W v ∧ refillContext h = E.ctx ∧
    s₀.gpr .x7 = E.st ∧ s₀.gpr .x2 = E.us ∧ (s₀.mem.readW (s₀.gpr .x7) 64).toNat = E.n₀

theorem entered_wp {E : EntryPub} {u : State} (hi : EntryAt E u) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.entryHeader ++ Impl.Dsa.AArch64.Generation.entryDerived)) u
      (Entered E) := by
  obtain ⟨s₀, h, a, hc, p7, p2, hn⟩ := hi
  exact WP.mono (entry_ok h a) fun v ⟨W, D, _, _⟩ => ⟨s₀, h, W, D, hc, p7, p2, hn⟩

/-- The width's search, from the entry's words. -/
theorem search_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) (pLen : Nat)
    (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two fun E v => Entered E v ∧ E.pBytes = pLen)
      (Impl.Dsa.AArch64.Generation.Refill.search H.sha1 H.sha256 G.run T.run pLen (Spec.Dsa.generationQLen pLen))
      (Two fun (_ : Unit) (_ : State) => True) := by
  have sizes : GenerationSizes pLen (Spec.Dsa.generationQLen pLen) := by
    rcases hp with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  have header : ∀ (E : EntryPub) (v : State), Entered E v ∧ E.pBytes = pLen →
      WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.widthHeader (Spec.Dsa.generationQLen pLen))) v
        (LoopAt pLen ⟨E.ctx, E.n₀, 0, E.st, E.us⟩) := by
    rintro ⟨pB, ctx, n₀, st, us⟩ v ⟨⟨s₀, h, W, D, hc, p7, p2, hn⟩, hpl⟩
    change pB = pLen at hpl
    subst hpl
    refine WP.mono (widthHeader_ok D rfl) fun w ⟨hm, h16, h10, c0, c1, c2, _, kw⟩ => ?_
    have l := loop_initial h hm (v := w) (by simpa [upd] using h16) (by simpa [upd] using h10) c0 c1 c2
    change (s₀.mem.readW (s₀.gpr .x7) 64).toNat = n₀ at hn
    rw [hn] at l
    exact ⟨s₀, h, w, hc, ⟨p7, p2⟩, kw.wr.trans D.wr, l⟩
  unfold Impl.Dsa.AArch64.Generation.Refill.search
  simp only [VG.Impl.Bignum.AArch64.seqs]
  have hq : Spec.Dsa.generationQLen pLen = 20 ∨ Spec.Dsa.generationQLen pLen = 32 := by
    unfold Spec.Dsa.generationQLen; split <;> simp
  have ht : ∃ hc, (taint.check (Taint.ofRegs [])
      (.block (Impl.Dsa.AArch64.Generation.Refill.widthHeader (Spec.Dsa.generationQLen pLen))) hc).isSome = true := by
    rcases hq with hq | hq <;> rw [hq] <;> exact ⟨_, by taint_decide⟩
  refine RelCT.seq (two_map (fun E : EntryPub => (⟨E.ctx, E.n₀, 0, E.st, E.us⟩ : LoopPub)) (Φ' := fun P v => ∃ E,
      (⟨E.ctx, E.n₀, 0, E.st, E.us⟩ : LoopPub) = P ∧ Entered E v ∧ E.pBytes = pLen) (fun E v h => ⟨E, rfl, h⟩) ?_)
    (RelCT.seq (controller_ct H G T pLen sizes) (two_sp (finish_ct pLen hp)))
  exact two_piece [] (nopin _) ht.choose_spec fun P v ⟨E, e, hE⟩ => e ▸ header E v hE

/-- After the width test against `len`. -/
def Tested (len : Nat) (E : EntryPub) (t : State) : Prop :=
  Entered E t ∧ isa.eval (.zero .x .x4) t = some (BitVec.ofNat 64 E.pBytes == BitVec.ofNat 64 len)

theorem Entered.congr {E : EntryPub} {v t : State} (he : Entered E v) (hm : t.mem = v.mem)
    (hk : Keep [.x3, .x4] v t) : Entered E t := by
  obtain ⟨s₀, h, W, D, rest⟩ := he
  exact ⟨s₀, h, W, D.congr hm hk, rest⟩

theorem Entered.lengths {E : EntryPub} {v : State} (he : Entered E v) :
    E.pBytes = 128 ∨ E.pBytes = 256 ∨ E.pBytes = 384 := by
  obtain ⟨s₀, h, -⟩ := he
  have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega

theorem tested128_wp {E : EntryPub} {u : State} (he : Entered E u) :
    WP isa (.block [.ldrSp .x3 136, .subImm .x .x4 .x3 128]) u fun t =>
      Tested 128 E t ∧ t.gpr .x3 = BitVec.ofNat 64 E.pBytes := by
  have he' := he
  obtain ⟨s₀, h, W, D, -⟩ := he
  obtain ⟨V, R⟩ := D.rep
  have h17 : W 17 = BitVec.ofNat 64 E.pBytes := D.slots 17 (by simp [generationSlots]) (by decide) (by decide)
  exact WP.mono (lengthTest_ok D.layout R) fun t ⟨x3, ev, hm, hk⟩ =>
    ⟨⟨he'.congr hm hk, ev.trans (by rw [h17])⟩, x3.trans h17⟩

theorem tested_ne {len : Nat} {E : EntryPub} {t : State} (h : Tested len E t)
    (hb : isa.eval (.zero .x .x4) t = some false) : E.pBytes ≠ len := by
  intro e
  have e' := Option.some.inj (h.2.symm.trans hb)
  rw [e] at e'
  simp at e'

theorem tested256_wp {E : EntryPub} {u : State}
    (he : (Tested 128 E u ∧ u.gpr .x3 = BitVec.ofNat 64 E.pBytes) ∧ isa.eval (.zero .x .x4) u = some false) :
    WP isa (.block [.subImm .x .x4 .x3 256]) u fun t => Tested 256 E t ∧ E.pBytes ≠ 128 := by
  have n := tested_ne he.1.1 he.2
  obtain ⟨⟨⟨e, -⟩, x3⟩, -⟩ := he
  exact WP.mono lengthTest256_ok fun t ⟨ev, hm, hk⟩ =>
    ⟨⟨e.congr hm hk, ev.trans (by rw [x3])⟩, n⟩

theorem tested_eq {len : Nat} {E : EntryPub} {t : State} (h : Tested len E t)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) (hb : isa.eval (.zero .x .x4) t = some true) : E.pBytes = len := by
  have e := Option.some.inj (h.2.symm.trans hb)
  have hp := h.1.lengths
  rw [beq_iff_eq] at e
  rcases hp with h₁ | h₁ | h₁ <;> rcases hl with h₂ | h₂ | h₂ <;> rw [h₁, h₂] at e ⊢ <;> first | rfl | cases e

theorem dispatch_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) :
    RelCT isa (Two Entered) (Impl.Dsa.AArch64.Generation.dispatch H.sha1 H.sha256 G.run T.run)
      (Two fun (_ : Unit) (_ : State) => True) := by
  unfold Impl.Dsa.AArch64.Generation.dispatch
  refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => tested128_wp h)
    (two_ite (fun _ _ _ hs ht => hs.1.2.trans ht.1.2.symm) ?_ ?_)
  · exact two_map id (fun E v h => ⟨h.1.1.1, tested_eq h.1.1 (Or.inl rfl) h.2⟩) (search_ct H G T 128 (Or.inl rfl))
  · refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => tested256_wp h)
      (two_ite (fun _ _ _ hs ht => hs.1.2.trans ht.1.2.symm) ?_ ?_)
    · exact two_map id (fun E v h => ⟨h.1.1.1, tested_eq h.1.1 (Or.inr (Or.inl rfl)) h.2⟩)
        (search_ct H G T 256 (Or.inr (Or.inl rfl)))
    · refine two_map id (fun E v h => ⟨h.1.1.1, ?_⟩) (search_ct H G T 384 (Or.inr (Or.inr rfl)))
      have n256 := tested_ne h.1.1 h.2
      rcases h.1.1.1.lengths with e | e | e
      · exact absurd e h.1.2
      · exact absurd e n256
      · exact e

/-! ## The function -/

theorem saves_ct : RelCT isa (fun s t => s.sp = t.sp) (.block Impl.Dsa.AArch64.Generation.entrySave)
    (fun _ _ => True) := by
  apply (two_taint (Φ := fun (_ : Unit) (_ : State) => True) [] (nopin _) (by taint_decide)).mono
  · intro s t h
    exact ⟨(), True.intro, True.intro, h⟩
  · exact fun _ _ _ => True.intro

theorem tail_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) :
    RelCT isa (Two EntryAt)
      (.seq (.block (Impl.Dsa.AArch64.Generation.entryHeader ++ Impl.Dsa.AArch64.Generation.entryDerived))
        (.seq (Impl.Dsa.AArch64.Generation.dispatch H.sha1 H.sha256 G.run T.run)
          (.block Impl.Dsa.AArch64.Generation.entryRestore))) (fun _ _ => True) :=
  RelCT.seq (two_piece [.x7] (fun E s t ⟨_, _, a, _, p, _⟩ ⟨_, _, a', _, p', _⟩ r hr => by
      obtain rfl := List.mem_singleton.mp hr
      rw [a.regs .x7 (by simp), a'.regs .x7 (by simp), p, p']) (by taint_decide) fun _ _ h => entered_wp h)
    (RelCT.seq (dispatch_ct H G T) (two_taint [] (nopin _) (by taint_decide)))

theorem saved_state {s t : State} {tr : List Leak}
    (h : Exec isa (.block Impl.Dsa.AArch64.Generation.entrySave) (allocState 480 s) tr t) : t = linkState s := by
  obtain ⟨_, u, e, hu⟩ := entrySave_ok s
  obtain ⟨_, rfl⟩ := Exec.det h e
  exact hu

theorem body_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) {s t u v : State}
    (hs : (Spec.Dsa.parameterSearchContract abi refillStack).pre s)
    (ht : (Spec.Dsa.parameterSearchContract abi refillStack).pre t) (agree : RefillAgree s t) {xs ys : List Leak}
    (es : Exec isa (Impl.Dsa.AArch64.Generation.entryBody H.sha1 H.sha256 G.run T.run) (allocState 480 s) xs u)
    (et : Exec isa (Impl.Dsa.AArch64.Generation.entryBody H.sha1 H.sha256 G.run T.run) (allocState 480 t) ys v) :
    xs = ys := by
  have ha := refillABI_of hs
  have hb : RefillABI (refillPLen s) t := by rw [agree.width]; exact refillABI_of ht
  have hsp : s.sp - BitVec.ofNat 64 480 = t.sp - BitVec.ofNat 64 480 := by rw [agree.sp]
  cases es with
  | seq sa ba =>
    cases et with
    | seq sb bb =>
      have saves := (saves_ct _ _ _ _ _ _ hsp sa sb).1
      obtain rfl := saved_state sa
      obtain rfl := saved_state sb
      have E₁ : EntryAt (entryPub ha) (linkState s) := ⟨s, ha, linkAllocated ha, rfl, rfl, rfl, rfl⟩
      have E₂ : EntryAt (entryPub ha) (linkState t) :=
        ⟨t, hb, linkAllocated hb, (refillContext_eq ha hb agree).symm, (agree.regs .x7 (by simp)).symm,
          (agree.regs .x2 (by simp)).symm, agree.seeds.symm⟩
      have tail := (tail_ct H G T _ _ _ _ _ _ ⟨entryPub ha, E₁, E₂, hsp⟩ ba bb).1
      exact congrArg₂ List.append saves tail

theorem refill_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) :
    ConstantTime isa (Spec.Dsa.parameterSearchContract abi refillStack).pre
      (Spec.Dsa.parameterSearchContract abi refillStack).pub
      (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) := by
  intro s t xs ys u v hs ht hp es et
  have ct : RelCT isa (fun s t => (Spec.Dsa.parameterSearchContract abi refillStack).pre s ∧
      (Spec.Dsa.parameterSearchContract abi refillStack).pre t ∧ RefillAgree s t)
      (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) (fun _ _ => True) := by
    apply RelCT.alloc
    rintro a b xa xb u v ⟨s, t, ⟨hs, ht, hp⟩, rfl, rfl⟩ ea eb
    exact ⟨body_ct H G T hs ht hp ea eb, True.intro⟩
  exact (ct _ _ _ _ _ _ ⟨hs, ht, refill_agree hp⟩ es et).1

end VG.Proof.Dsa.AArch64.Generation.Refill
