module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Cached
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Contract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Implies
public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptFn
import VerifiedGarbage.Proof.Ffdh.CachedSat
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptFn
meta import VerifiedGarbage.Proof.Ffdh.CachedSat
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinBase
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.WinBase
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.CT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.CT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
meta import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
meta import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
meta import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Loop
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.CTCode
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Loop
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.CTCode
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Writes
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Writes
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.Cached
public import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

/-! ### `Ffdh.PPC64LE.Cached.SearchProof.CT`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.Cached.SearchProof.Correct`, which this module and modules that import it used -/

section

/-! # The key-generation controller's correctness (PPC64LE)

The link register is moved to `r0`, which the frame around the loop saves
(`WP.frameRegAny`), and back; `finish` then stores the octets consumed,
returns the status and restores `r31`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.GenerationSearch
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search (ldf stf entry arguments terminal zeroOut zeroOutputs exhausted advance
  rejectedScalar rejectedPublic test classify request room finish)
open VG.Impl.Ffdh.PPC64LE.Cached.Search

/-! ## Returning -/

theorem KeyInput.used_scr {p : KeyPublic} {s : State} (h : KeyInput p s) {t : State}
    (hw : t.wr = s.wr) : Scr t p.up 8 := by
  refine Scr.of_mem (by rw [hw, h.1.2.2.2.1, ← h.2]; simp [inWrites, inUsed, keyOfState]) ?_
  rw [← h.2]
  exact h.nowrap (r := inUsed s) (by simp [inWrites])

/-- The word for the octets consumed is apart from the outputs and the
controller's words. -/
theorem KeyInput.used_disjoint {p : KeyPublic} {s : State} (h : KeyInput p s) :
    (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧ (⟨p.yp, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧
      (⟨p.control, 128⟩ : Region).Disjoint ⟨p.up, 8⟩ := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  have hu : inUsed s = ⟨p.up, 8⟩ := by rw [← h.2]; rfl
  have hc : inCtl s = ⟨p.control, 128⟩ := by rw [← h.2]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← h.x_eq, ← hu]; exact hpw.1.2.1
  · rw [← h.y_eq, ← hu]; exact hpw.2.1.1
  · rw [← hc, ← hu]; exact hpw.2.2.1.2.symm

theorem key_finish_values {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block finish) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 result.status ∧ t.gpr .r31 = original.gpr .r31 ∧
        t.mem = s.mem.writeW p.up (BitVec.ofNat 64 result.used)) ∧
      Keep [.r3, .r4, .r5, .r31] s t := by
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hup : InRegions s.wr p.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_scr h.wr).st (d := 0) (by decide)
  have hu := h.usedPtr
  have hd := h.used
  have hs := h.status
  have hx := h.savedR31
  simp only [Bignum.word, off] at hu hd hs hx
  have hf : Frame [⟨p.up, 8⟩] s.mem (s.mem.writeW p.up (BitVec.ofNat 64 result.used)) :=
    Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hx' : (s.mem.writeW p.up (BitVec.ofNat 64 result.used)).readW (p.control + BitVec.ofNat 64 32) 64 =
      original.gpr .r31 :=
    (hf.readW (r := ⟨p.control, 128⟩) (Offset.contains_base _ (by decide) (by decide))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.used_disjoint.2.2)
      (by decide)).trans hx
  refine WP.keep [.r3, .r4, .r5, .r31] ?_ (by decide)
  unfold finish
  prun [ldf, h.r31, hu, hd, hs, hx', hup, hl 120 (by decide), hl 88 (by decide), hl 112 (by decide),
    hl 32 (by decide), BitVec.add_zero]

/-- What the search returns, for its result. -/
def KeyReturned (p : KeyPublic) (result : Spec.Ffdh.KeySearchResult) (t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = result.status ∧ KeyOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.control 4 = p.policy result ∧
    Spec.Rsa.wordsAt t.mem p.up 1 = [BitVec.ofNat 64 result.used]

theorem key_finish {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block finish) s fun t => KeyReturned p result t ∧
      (∀ reg ∈ preserved, t.gpr reg = original.gpr reg) ∧ t.sp = s.sp ∧ t.lr = s.lr := by
  refine WP.mono (key_finish_values h) fun t ⟨⟨ha, hr31, hm⟩, k⟩ => ?_
  have hd := h.input.used_disjoint
  have hk := h.input.len_lt
  have hf : Frame [⟨p.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hb : ∀ q : Addr, (⟨q, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ →
      Spec.Rsa.bytesAt t.mem q p.len = Spec.Rsa.bytesAt s.mem q p.len := by
    intro q hq
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hq)
      (show p.len ≤ 2 ^ 64 by omega_using [hk]) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.2.2) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.sp, k.lr⟩
  · rw [ha]
    have := key_status_lt result
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [this]
  · have ho := h.output
    unfold KeyOutput at ho ⊢
    rw [hb _ hd.1, hb _ hd.2.1]
    exact ho
  · have he : Spec.Rsa.wordsAt t.mem p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
      change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
        word t.mem p.control (8 * 3)] = [word s.mem p.control (8 * 0), word s.mem p.control (8 * 1),
        word s.mem p.control (8 * 2), word s.mem p.control (8 * 3)]
      rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
    exact he.trans h.policy
  · change [word t.mem p.up 0] = [_]
    rw [hm]
    congr 1
    simpa only [Bignum.word, off, BitVec.add_zero] using
      Mem.readW_writeW_self64 s.mem p.up (BitVec.ofNat 64 result.used)
  · intro reg hreg
    by_cases he : reg = .r31
    · subst he; exact hr31
    · exact (k.gpr reg (by revert reg hreg he; decide)).trans (h.saved reg hreg he)

/-! ## The search's frame -/

theorem iteration_depth (a : Attempt) : sdepth (iteration a.call) ≤ 144 := by
  have := a.stack
  simp only [iteration, branch, attemptOrRequest, attemptRun, exhausted, zeroOutputs, zeroOut, classify,
    request, Impl.Bignum.PPC64LE.countLoop, sdepth, Attempt.call, Instr.frameBytes]
  omega_using [this]

/-- After the frame: a finished search, with `r0` and the stack pointer
back. -/
theorem KeyDone.popped {p : KeyPublic} {original s : State} {r : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) (v sp : BitVec 64) :
    KeyDone p original r { s.write .r0 v with sp := sp } := by
  refine ⟨h.input, h.rd, h.wr, ?_, fun reg hr h31 => ?_, h.savedR31, h.usedPtr, h.used,
    h.status, h.policy, h.output⟩
  · show (s.write .r0 v).gpr .r31 = _
    rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; exact h.r31
  · show (s.write .r0 v).gpr reg = _
    rw [RegUpd.gpr_write_of_ne _ _ (fun e => by subst e; exact absurd hr (by decide))]
    exact h.saved reg hr h31

/-- A finished search, whatever a region of the stack holds: the control
block and the outputs lie apart from the stack. -/
theorem KeyDone.lost {p : KeyPublic} {original s : State} {r : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) {L : Region} {m : Mem} (u : Nat → BitVec 64) (fl : Frame [L] s.mem m)
    (hL : Region.Sub L (below original.sp stackUse)) :
    KeyDone p original r { s with mem := m, unknowns := u } := by
  have hi := h.input
  obtain hf : Frame (KeyInput.callChanges original) s.mem m :=
    fl.sub fun q hq => by rw [List.mem_singleton.mp hq]; exact ⟨_, by simp [KeyInput.callChanges], hL⟩
  obtain hc : ∀ j < 16, word m p.control (8 * j) = word s.mem p.control (8 * j) :=
    fun j hj => hi.control_frame hf j hj
  obtain hbx : Spec.Rsa.bytesAt m p.xp p.len = Spec.Rsa.bytesAt s.mem p.xp p.len :=
    List.map_congr_left fun i hi' => lost_byte fl (R := ⟨p.xp, p.len⟩)
      (by rw [← hi.x_eq]; exact ((hi.stack_disjoint (r := inX original) (by simp [inWrites])).sub_left hL).symm)
      (List.mem_range.mp hi')
  obtain hby : Spec.Rsa.bytesAt m p.yp p.len = Spec.Rsa.bytesAt s.mem p.yp p.len :=
    List.map_congr_left fun i hi' => lost_byte fl (R := ⟨p.yp, p.len⟩)
      (by rw [← hi.y_eq]; exact ((hi.stack_disjoint (r := inY original) (by simp [inWrites])).sub_left hL).symm)
      (List.mem_range.mp hi')
  obtain he : Spec.Rsa.wordsAt m p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
    change [word m p.control (8 * 0), word m p.control (8 * 1), word m p.control (8 * 2),
      word m p.control (8 * 3)] = [word s.mem p.control (8 * 0), word s.mem p.control (8 * 1),
      word s.mem p.control (8 * 2), word s.mem p.control (8 * 3)]
    rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
  refine ⟨hi, h.rd, h.wr, h.r31, h.saved, (hc 4 (by decide)).trans h.savedR31,
    (hc 15 (by decide)).trans h.usedPtr, (hc 11 (by decide)).trans h.used, (hc 14 (by decide)).trans h.status,
    he.trans h.policy, ?_⟩
  have ho := h.output
  show KeyOutput p r m
  unfold KeyOutput at ho ⊢
  rw [hbx, hby]
  exact ho

theorem KeyInput.tail_eq {p : KeyPublic} {s : State} (h : KeyInput p s) :
    keyResult s = p.tail (keyRand s) 0 p.keys p.scalars := by
  cases h.2
  simp only [keyResult, KeyPublic.tail, keyTail, after, GenerationPolicy.search, keyOfState, KeyPublic.a, List.drop_zero,
    Nat.zero_add]

theorem key_body {p : KeyPublic} {s t : State} (a : Attempt) (h : KeyInput p s)
    (hx : t.gpr .r31 = p.control)
    (hm : t.mem = Proof.Ffdh.Control.writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) :
    WP isa (search a.call) t fun u =>
      KeyDone p s (keyResult s) u ∧ u.lr = s.lr ∧ u.sp = s.sp := by
  unfold search
  refine WP.seq (WP.mono (WP.keep [.r0] (Q := fun t₁ => t₁.gpr .r0 = t.lr ∧ t₁.mem = t.mem) (by
    prun [exec_mflr]) (by decide)) fun t₁ ⟨⟨h0, hm₁⟩, k₁⟩ => ?_)
  have k' : Keep entryRegs s t₁ := k.trans' (k₁.mono (by decide))
  have hl := key_start h (by rw [k₁.gpr _ (by decide)]; exact hx) (hm₁.trans hm) k'
  have hsp : 48 ≤ t₁.sp.toNat := by rw [k'.sp, ← h.sp_eq]; have := h.sp_room; omega_using [this]
  refine WP.seq (WP.mono (WP.frameRegAny (r := .r0)
    (Q := fun u => KeyDone p s (keyResult s) u ∧ u.gpr .r0 = s.lr ∧ u.sp = s.sp) hsp ?_ ?_ ?_)
    fun u ⟨hd, h0', hsp'⟩ => ?_)
  · intro R hR
    rw [k'.wr, h.1.2.2.2.1] at hR
    have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
    refine hd.sub_left ?_
    rw [k'.sp, show s.sp - 48 + 32 = s.sp - BitVec.ofNat 64 16 by bv_omega]
    exact Offset.sub_below s.sp (a := 16) (b := 192) (by decide) (by decide)
  · refine WP.mono (key_loop a (expected := keyResult s) (n := 128 * p.keys + p.scalars + 1)
      ⟨0, p.keys, p.scalars, rfl, hl, by rw [h.tail_eq], by rw [h.tail_eq]⟩)
      fun u hu m uu fl => ⟨(hu.lost uu fl (by
        rw [k'.sp]; exact Offset.sub_below s.sp (a := 48) (b := 192) (by decide) (by decide))).popped _ _, ?_, k'.sp⟩
    show (u.write .r0 (t₁.gpr .r0)).gpr .r0 = _
    rw [RegUpd.gpr_write_self, h0, k.lr]
  · have := iteration_depth a
    simp only [sdepth]
    omega_using [this]
  · prun [exec_mtlr]
    exact ⟨⟨hd.input, hd.rd, hd.wr, hd.r31, hd.saved, hd.savedR31, hd.usedPtr, hd.used, hd.status,
      hd.policy, hd.output⟩, h0', hsp'⟩

theorem KeyReturned.post {s t : State} (h : KeyReturned (keyOfState s) (keyResult s) t) : keyPost s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem key_correct_ok (a : Attempt) {s : State} (h : keyPre s) :
    WP isa (code a.call) s fun t => keyPost s t ∧ abiPreserved s t := by
  let p := keyOfState s
  have hp : KeyInput p s := ⟨h, rfl⟩
  unfold code
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨⟨hx, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (key_body a hp hx hm k) fun u ⟨hd, hlr, hsp⟩ => ?_)
  refine WP.mono (key_finish hd) fun q ⟨hr, hg, hqsp, hqlr⟩ => ?_
  exact ⟨hr.post, hg, hqsp.trans hsp, hqlr.trans hlr⟩

theorem key_correct (a : Attempt) (s : State) (h : keyContract.pre s) :
    ∃ tr t, Exec isa (code a.call) s tr t ∧ abiPreserved s t ∧ keyContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := key_correct_ok a h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

end

end

/-! ### `Ffdh.PPC64LE.Cached.SearchProof.BranchCT`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.Cached.SearchProof.AttemptCT`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.Cached.SearchProof.LeafCT`, which only this module used -/

section

/-! # Public positions in the key search, and its exits and rejections (PPC64LE)

Two runs agree on the public descriptor, the octets consumed, the budgets
left and the statuses of the attempts still to come, which the search from
there gives for each run's own tape. The exits and rejections use only
public addresses.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.PPC64LE.Taint
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search (ldf stf entry arguments terminal zeroOut zeroOutputs exhausted advance
  rejectedScalar rejectedPublic test classify request room finish)
open VG.Impl.Ffdh.PPC64LE.Cached.Search

/-- Some loop state of the search with the public descriptor `p`. -/
def KeyAny (p : KeyPublic) (s : State) : Prop :=
  ∃ original used keys scalars, KeyLive p original used keys scalars s

structure KeyPoint where
  inputs : KeyPublic
  used : Nat
  keys : Nat
  scalars : Nat
  statuses : List Nat

def KeyCTL (q : KeyPoint) (s : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses

theorem KeyCTL.any {q : KeyPoint} {s : State} (h : KeyCTL q s) : KeyAny q.inputs s :=
  let ⟨original, h, _⟩ := h; ⟨original, _, _, _, h⟩

theorem key_any_pins : Pins KeyAny [.r31] := by
  intro p s t ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

theorem key_ctl_pins : Pins KeyCTL [.r31] :=
  fun _ _ _ h₁ h₂ => key_any_pins _ _ _ h₁.any h₂.any

theorem key_no_pins {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

/-! ## Zeros at the outputs -/

/-- Before a zeroing's loop: its pointer and count. -/
def KeyZeroCT (j : Nat) (p : KeyPublic) (s : State) : Prop :=
  KeyAny p s ∧ s.gpr .r3 = (if j = 5 then p.xp else p.yp) ∧ s.gpr .r4 = BitVec.ofNat 64 p.len

private theorem zero_header (j : Nat) (hj : j = 5 ∨ j = 6) (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [ldf .r3 j, ldf .r4 2, .li .r5 0]) s (KeyZeroCT j p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  have a := h.access
  have hk : word s.mem p.control 16 = BitVec.ofNat 64 p.len :=
    h.header (j := 2) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hk
  rcases hj with rfl | rfl <;>
  refine WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun t => (t.gpr .r3 = (if _ = 5 then p.xp else p.yp) ∧
    t.gpr .r4 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by decide))
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨⟨original, used, keys, scalars, h.keep k hm⟩, hr⟩
  · have hp : word s.mem p.control 40 = p.xp := h.header (j := 5) (by simp [KeyPublic.headers])
    simp only [Bignum.word, off] at hp
    prun [ldf, h.r31, hp, hk, a.ld 40 (by decide), a.ld 16 (by decide)]
  · have hp : word s.mem p.control 48 = p.yp := h.header (j := 6) (by simp [KeyPublic.headers])
    simp only [Bignum.word, off] at hp
    prun [ldf, h.r31, hp, hk, a.ld 48 (by decide), a.ld 16 (by decide)]

private theorem zero_ct (j : Nat) (hj : j = 5 ∨ j = 6) :
    RelCT isa (Two KeyAny) (zeroOut j) (fun _ _ => True) := by
  rcases hj with rfl | rfl <;> unfold zeroOut <;>
  · refine RelCT.seq (two_post (two_taint [.r31] key_any_pins (by taint_decide))
      (zero_header _ (by decide))) ?_
    exact two_taint [.r3, .r4] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem zero_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (zeroOut 5) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_zero_out h (j := 5) (.inl rfl) (by simp [KeyPublic.headers]) h.input.x_mem
    h.input.x_ne_ctl) fun _ ⟨ht, _⟩ => ⟨original, used, keys, scalars, ht⟩

theorem key_zero_outputs_ct : RelCT isa (Two KeyAny) zeroOutputs (fun _ _ => True) := by
  unfold zeroOutputs
  exact RelCT.seq (two_post (zero_ct 5 (.inl rfl)) zero_ready) (zero_ct 6 (.inr rfl))

private theorem terminal_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block (terminal 3)) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_terminal_live h (.inr rfl)) fun _ ⟨ht, _⟩ => ⟨original, used, 0, 0, ht⟩

theorem key_exhausted_ct : RelCT isa (Two KeyAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_post (two_taint [.r31] key_any_pins (by taint_decide)) terminal_ready)
    key_zero_outputs_ct

private theorem request_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [ldf .r10 2, .li .r11 0, stf .r10 3, stf .r11 14]) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_request_live h) fun _ ⟨ht, _⟩ => ⟨original, used, keys, scalars, ht⟩

theorem key_request_ct : RelCT isa (Two KeyAny) request (fun _ _ => True) := by
  unfold request
  exact RelCT.seq (two_post (two_taint [.r31] key_any_pins (by taint_decide)) request_ready)
    key_zero_outputs_ct

theorem key_accepted_ct : RelCT isa (Two KeyAny) (.block (terminal 1)) (fun _ _ => True) :=
  two_taint [.r31] key_any_pins (by taint_decide)

theorem key_rejected_scalar_ct : RelCT isa (Two KeyAny) (.block rejectedScalar) (fun _ _ => True) :=
  two_taint [.r31] key_any_pins (by taint_decide)

theorem key_rejected_public_ct : RelCT isa (Two KeyAny) (.block rejectedPublic) (fun _ _ => True) :=
  two_taint [.r31] key_any_pins (by taint_decide)

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

end

end

/-! # An attempt leaks only its public arguments, the domain and its status (PPC64LE)

The attempt's timing may depend on its arguments, the domain and its status
(`gkContract.pub`). Two runs at the same point agree on all of them: the
status is the first of the statuses still to come.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.PPC64LE.Taint
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.Control (writeController)
open VG.Proof.Ffdh.PPC64LE.Cached (cgContract cgLeak cgScalar cgA cgDom)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search (ldf stf entry arguments terminal zeroOut zeroOutputs exhausted advance
  rejectedScalar rejectedPublic test classify request room finish)
open VG.Impl.Ffdh.PPC64LE.Cached.Search

/-- A loop state at which the controller attempts a key. -/
def KeyReady (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocated 144 s

/-- The attempt's entry, before the call. -/
def KeyCallCT (q : KeyPoint) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    KeyArgs q.inputs q.used u ∧
    u.mem = writeController (allocated 144 s).mem (callSp q.inputs) (callValues q.inputs) ∧
    Keep argRegsW (allocated 144 s) u

/-- After the attempt. -/
def KeyAttempted (q : KeyPoint) (t : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars t ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    AttemptPost q.inputs (keyRand original) q.used t

theorem key_allocated_pins : Pins KeyAllocated [.r31] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

private theorem arguments_ready (q : KeyPoint) (u : State) (h : KeyAllocated q u) :
    WP isa (.block cachedArguments) u (KeyCallCT q) := by
  obtain ⟨s, ⟨⟨original, h, hst⟩, hk, hs, hr⟩, rfl⟩ := h
  exact WP.mono (key_arguments_ok h) fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩

theorem key_attempt_ready (a : Attempt) (q : KeyPoint) (s : State) (h : KeyReady q s) :
    WP isa (attemptRun a.call) s (KeyAttempted q) := by
  obtain ⟨⟨original, h, hst⟩, hk, hs, hr⟩ := h
  exact WP.mono (key_attempt_run a h hr) fun _ ⟨ht, hp⟩ => ⟨original, ht, hst, hk, hs, hr, hp⟩

/-- The status of the attempt at a point: the first still to come. -/
def KeyPoint.status (q : KeyPoint) : Nat := q.statuses.head?.getD 0

/-- The attempt's status at a point, for each run's tape. -/
theorem attempt_status {q : KeyPoint} {original s : State}
    (h : KeyLive q.inputs original q.used q.keys q.scalars s)
    (hst : (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses)
    (hk : q.keys ≠ 0) (hs : q.scalars ≠ 0) (hr : q.used + q.inputs.len ≤ q.inputs.randLen) :
    attemptStatus .cached q.inputs.a q.inputs.len ((keyRand original).drop q.used) = q.status := by
  have hhead := keyTail_statuses_head (policy := .cached) (a := q.inputs.a) (len := q.inputs.len)
    (rand := keyRand original) (used := q.used) hk hs (by rw [h.rand_length]; omega_using [hr])
  rw [hst] at hhead
  simp only [KeyPoint.status, hhead, Option.getD_some]

/-- What the attempt sees at its entry, in terms of the point alone. -/
private theorem call_view {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    (callState q.inputs q.used u).sp = callSp q.inputs ∧
    cgLeak (callState q.inputs q.used u) = q.inputs.dom.map (·.toNat) ++ [q.status] ∧
    KeyArgs q.inputs q.used (callState q.inputs q.used u) ∧
    stackArg (callState q.inputs q.used u) 0 = BitVec.ofNat 64 q.inputs.len ∧
    stackArg (callState q.inputs q.used u) 1 = q.inputs.B ∧
    stackArg (callState q.inputs q.used u) 2 = BitVec.ofNat 64 (q.inputs.Z / 8) ∧
    stackArg (callState q.inputs q.used u) 3 = q.inputs.ctx ∧
    stackArg (callState q.inputs q.used u) 4 = BitVec.ofNat 64 q.inputs.ctxLen := by
  obtain ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by
    rw [k.sp]; show s.sp - BitVec.ofNat 64 144 = _; rw [h.sp]
  have hf := h.callFacts hr
  obtain ⟨hdom, hrand, h9⟩ := call_inputs h hr hf hm hu ha
  have he := attempt_status h hst hk hs hr
  obtain ⟨h0, h1, h2, h3, h4⟩ := call_args hu hm
  refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hu], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cgLeak, cgScalar, cgA, cgDom, hdom, hrand, h9]
    rw [← he]
    rfl
  · obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
    exact ⟨(call_gpr (by decide)).trans r3, (call_gpr (by decide)).trans r4, (call_gpr (by decide)).trans r5,
      (call_gpr (by decide)).trans r6, (call_gpr (by decide)).trans r7, (call_gpr (by decide)).trans r8,
      (call_gpr (by decide)).trans r9, (call_gpr (by decide)).trans r10⟩
  · rw [call_stackArg, h0]
  · rw [call_stackArg, h1]
  · rw [call_stackArg, h2]
  · rw [call_stackArg, h3]
  · rw [call_stackArg, h4]

private theorem call_pub {q : KeyPoint} {u₁ u₂ : State} (h₁ : KeyCallCT q u₁) (h₂ : KeyCallCT q u₂) :
    cgContract.pub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩, d₀, d₁, d₂, d₃, d₄⟩ := call_view h₁
  obtain ⟨a₂, b₂, ⟨e3, e4, e5, e6, e7, e8, e9, e10⟩, f₀, f₁, f₂, f₃, f₄⟩ := call_view h₂
  exact ⟨a₁.trans a₂.symm, b₁.trans b₂.symm, c3.trans e3.symm, c4.trans e4.symm, c5.trans e5.symm,
    c6.trans e6.symm, c7.trans e7.symm, c8.trans e8.symm, c9.trans e9.symm, c10.trans e10.symm,
    d₀.trans f₀.symm, d₁.trans f₁.symm, d₂.trans f₂.symm, d₃.trans f₃.symm, d₄.trans f₄.symm⟩

private theorem call_ready {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    cgContract.pre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  obtain ⟨original, s, h, _, _, _, hr, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by
    rw [k.sp]; show s.sp - BitVec.ofNat 64 144 = _; rw [h.sp]
  exact ⟨call_attempt_pre h hr (h.callFacts hr) hu ha hm, call_covers_reads h hr k.rd k.wr,
    call_covers_writes h k.wr⟩

theorem key_attempt_call_ct (a : Attempt) :
    RelCT isa (Two KeyCallCT) a.call (fun _ _ => True) := by
  refine RelCT.callEx a.correct a.ct fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := call_ready h₁
  obtain ⟨p₂, c₂, w₂⟩ := call_ready h₂
  exact ⟨_, _, _, _, p₁, p₂, call_pub h₁ h₂, c₁, w₁, c₂, w₂⟩

theorem key_attempt_run_ct (a : Attempt) :
    RelCT isa (Two KeyReady) (attemptRun a.call) (fun _ _ => True) := by
  unfold attemptRun
  apply RelCT.alloc
  · rintro _ _ ⟨_, _, _, hsp⟩; exact hsp
  refine (RelCT.seq (two_post (two_taint [.r31] key_allocated_pins (by taint_decide)) arguments_ready)
    (key_attempt_call_ct a)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

end

end

/-! # An iteration of the key search branches on its public point alone (PPC64LE)

The attempt's classification branches on its status, the first of the
statuses still to come; the guards on the budgets and the tape, which the
point fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.PPC64LE.Taint
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (two_ite)
open VG.Proof.Ffdh.GenerationSearch
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search (ldf stf entry arguments terminal zeroOut zeroOutputs exhausted advance
  rejectedScalar rejectedPublic test classify request room finish)
open VG.Impl.Ffdh.PPC64LE.Cached.Search

/-! ## The classification -/

theorem key_attempted_pins : Pins KeyAttempted [.r31] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

/-- The status in `x9`, compared with `k` in `x10`. -/
def KeyGuard (k : Nat) (q : KeyPoint) (t : State) : Prop :=
  KeyAny q.inputs t ∧ t.gpr .r9 = BitVec.ofNat 64 q.status ∧
    isa.eval (.zero .d .r10) t = some (decide (q.status = k)) ∧ q.status < 4

private theorem first_ready (q : KeyPoint) (s : State) (h : KeyAttempted q s) :
    WP isa (.block (advance ++ test 1)) s (KeyGuard 1 q) := by
  obtain ⟨original, h, hst, hk, hs, hr, hp⟩ := h
  have he := attempt_status h hst hk hs hr
  have h4 : q.status < 4 := by
    rw [← he]
    rcases attemptStatus_cases (policy := .cached) q.inputs.a q.inputs.len ((keyRand original).drop q.used) with
      h | h | h <;> omega_using [h]
  refine WP.mono (key_classify_head h hr hp) fun t ⟨ht, _, hax, hev⟩ => ?_
  exact ⟨⟨original, _, _, _, ht⟩, by rw [hax, he], by rw [hev, he], h4⟩

private theorem next_ready (j k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 3) (q : KeyPoint) (s : State)
    (h : KeyGuard j q s ∧ isa.eval (.zero .d .r10) s = some false) :
    WP isa (.block (test k)) s (KeyGuard k q) := by
  obtain ⟨⟨⟨o, u, a, c, hl⟩, ha, _, h4⟩, _⟩ := h
  refine WP.mono (test_ok ha h4 hk) fun t ⟨⟨he, hm⟩, kt⟩ => ?_
  exact ⟨⟨o, u, a, c, hl.keep kt hm⟩, (kt.gpr .r9 (by decide)).trans ha, he, h4⟩

private theorem leaf {k : Nat} {b : Bool} {c : Prog isa} (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two fun q s => KeyGuard k q s ∧ isa.eval (.zero .d .r10) s = some b) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, h₁.1.1, h₂.1.1, hsp⟩) fun _ _ h => h

private theorem guard_eq (k : Nat) (q : KeyPoint) (s₁ s₂ : State) (h₁ : KeyGuard k q s₁)
    (h₂ : KeyGuard k q s₂) : isa.eval (.zero .d .r10) s₁ = isa.eval (.zero .d .r10) s₂ :=
  h₁.2.2.1.trans h₂.2.2.1.symm

theorem key_classify_ct : RelCT isa (Two KeyAttempted) classify (fun _ _ => True) := by
  unfold classify
  refine RelCT.seq (two_post (two_taint [.r31] key_attempted_pins (by taint_decide)) first_ready) ?_
  refine two_ite (guard_eq 1) (leaf key_accepted_ct) ?_
  refine RelCT.seq (two_post (two_taint [] key_no_pins (by taint_decide))
    (next_ready 1 2 (.inr (.inl rfl)))) ?_
  refine two_ite (guard_eq 2) (leaf key_rejected_scalar_ct) ?_
  refine RelCT.seq (two_post (two_taint [] key_no_pins (by taint_decide))
    (next_ready 2 3 (.inr (.inr rfl)))) ?_
  exact two_ite (guard_eq 3) (leaf key_rejected_public_ct) (leaf key_exhausted_ct)

/-! ## The guards -/

/-- Whether the search goes on after an iteration from `q`: it attempts, and
the attempt is rejected. -/
def keyContinues (q : KeyPoint) : Prop :=
  q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.inputs.len ≤ q.inputs.randLen - q.used ∧ q.status ≠ 1

instance (q : KeyPoint) : Decidable (keyContinues q) := inferInstanceAs
  (Decidable (q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.inputs.len ≤ q.inputs.randLen - q.used ∧ q.status ≠ 1))

/-- The point after a rejected attempt. -/
def nextKeyPoint (q : KeyPoint) : KeyPoint :=
  if q.status = 2 then ⟨q.inputs, q.used + q.inputs.len, q.keys, q.scalars - 1, q.statuses.tail⟩
  else ⟨q.inputs, q.used + q.inputs.len, q.keys - 1, 128, q.statuses.tail⟩

theorem nextKeyPoint_inputs (q : KeyPoint) : (nextKeyPoint q).inputs = q.inputs := by
  unfold nextKeyPoint; split <;> rfl

theorem nextKeyPoint_measure {q : KeyPoint} (h : keyContinues q) :
    128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars < 128 * q.keys + q.scalars := by
  obtain ⟨hk, hs, -, -⟩ := h
  unfold nextKeyPoint; split <;> dsimp only <;> omega_arith

/-- After the guards, the attempt and its classification. -/
def KeyBranchResult (q : KeyPoint) (t : State) : Prop :=
  if keyContinues q then KeyCTL (nextKeyPoint q) t ∧ word t.mem q.inputs.control 112 = 4
  else ∃ original r, KeyDone q.inputs original r t

theorem branch_r31 {q : KeyPoint} {t : State} (h : KeyBranchResult q t) :
    t.gpr .r31 = q.inputs.control := by
  by_cases hc : keyContinues q
  · simp only [KeyBranchResult, hc, ite_true] at h
    obtain ⟨⟨_, hl, _⟩, _⟩ := h
    rw [hl.r31, nextKeyPoint_inputs]
  · simp only [KeyBranchResult, hc, ite_false] at h
    obtain ⟨_, _, hd⟩ := h
    exact hd.r31

def KeysGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ isa.eval (.zero .d .r9) s = some (decide (q.keys = 0))

def ScalarsGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ isa.eval (.zero .d .r9) s = some (decide (q.scalars = 0))

def RoomGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧
    isa.eval (.zero .d .r12) s = some (decide (q.inputs.len ≤ q.inputs.randLen - q.used))

theorem keys_ready (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (.block [ldf .r9 0]) s (KeysGuard q) := by
  obtain ⟨original, h, hst⟩ := h
  exact WP.mono (keys_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, he⟩

theorem scalars_ready (q : KeyPoint) (s : State) (h : KeysGuard q s ∧ isa.eval (.zero .d .r9) s = some false) :
    WP isa (.block [ldf .r9 1]) s (ScalarsGuard q) := by
  obtain ⟨⟨⟨original, h, hst⟩, he⟩, hf⟩ := h
  have hk : q.keys ≠ 0 := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact WP.mono (scalars_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, hk, he⟩

theorem room_ready (q : KeyPoint) (s : State) (h : ScalarsGuard q s ∧ isa.eval (.zero .d .r9) s = some false) :
    WP isa (.block room) s (RoomGuard q) := by
  obtain ⟨⟨⟨original, h, hst⟩, hk, he⟩, hf⟩ := h
  have hs : q.scalars ≠ 0 := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact WP.mono (room_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, hk, hs, he⟩

theorem attempt_of_room {q : KeyPoint} {s : State}
    (h : RoomGuard q s ∧ isa.eval (.zero .d .r12) s = some true) : KeyReady q s := by
  obtain ⟨⟨⟨original, hl, hst⟩, hk, hs, he⟩, hf⟩ := h
  have hr := of_decide_eq_true (Option.some.inj (he.symm.trans hf))
  exact ⟨⟨original, hl, hst⟩, hk, hs, by have := hl.used_le; omega_using [hr, this]⟩

theorem key_branch_ready (a : Attempt) (q : KeyPoint) (s : State) (h : KeysGuard q s) :
    WP isa (branch a.call) s (KeyBranchResult q) := by
  obtain ⟨⟨original, hl, hst⟩, he⟩ := h
  have done : ∀ (t : State) (r : Spec.Ffdh.KeySearchResult), ¬keyContinues q →
      KeyDone q.inputs original r t → KeyBranchResult q t := fun t r hn hd => by
    simp only [KeyBranchResult, hn, ite_false]; exact ⟨original, r, hd⟩
  unfold branch
  refine WP.ite (decide (q.keys = 0)) he ?_ ?_
  · intro hz
    exact WP.mono (key_exhausted hl) fun t ht => done t _ (fun hc => hc.1 (of_decide_eq_true hz)) ht
  intro hnz
  have hk : q.keys ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (scalars_guard hl) fun u ⟨hu, he2⟩ => ?_)
  refine WP.ite (decide (q.scalars = 0)) he2 ?_ ?_
  · intro hz
    exact WP.mono (key_exhausted hu) fun t ht => done t _ (fun hc => hc.2.1 (of_decide_eq_true hz)) ht
  intro hnz2
  have hs : q.scalars ≠ 0 := of_decide_eq_false hnz2
  unfold attemptOrRequest
  refine WP.seq (WP.mono (room_guard hu) fun u ⟨hu3, hb⟩ => ?_)
  refine WP.ite _ hb ?_ ?_
  swap
  · intro hshort
    have := of_decide_eq_false hshort
    exact WP.mono (key_request hu3) fun t ht => done t _ (fun hc => by have := hc.2.2.1; omega_arith) ht
  intro hlong
  have hroom : q.used + q.inputs.len ≤ q.inputs.randLen := by
    have := of_decide_eq_true hlong; have := hl.used_le; omega_arith
  refine WP.seq (WP.mono (key_attempt_run a hu3 hroom) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (key_classify ht hroom (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hs) hp)
    fun r hq => ?_
  have hstat := attempt_status hl hst hk hs hroom
  have hr : q.inputs.len ≤ (keyRand original).length - q.used := by rw [hl.rand_length]; omega_using [hroom]
  rcases attemptStatus_cases (policy := .cached) q.inputs.a q.inputs.len ((keyRand original).drop q.used) with h1 | h2 | h3
  · simp only [KeyClassified, h1, ite_true] at hq
    exact done r _ (fun hc => hc.2.2.2 (by rw [← hstat, h1])) hq
  · simp only [KeyClassified, h2, Nat.reduceEqDiff, ite_true, ite_false] at hq
    have hc : keyContinues q := ⟨hk, hs, by omega_using [hroom], by rw [← hstat, h2]; decide⟩
    have hn : nextKeyPoint q = ⟨q.inputs, q.used + q.inputs.len, q.keys, q.scalars - 1, q.statuses.tail⟩ := by
      simp only [nextKeyPoint, ← hstat, h2, ite_true]
    simp only [KeyBranchResult, hc, ite_true, hn]
    refine ⟨⟨original, hq.1, ?_⟩, hq.2⟩
    rw [← hst]
    simp only [KeyPublic.tail, keyTail_scalar hk hs hr h2, List.tail_cons]
  · simp only [KeyClassified, h3, Nat.reduceEqDiff, ite_false] at hq
    have hc : keyContinues q := ⟨hk, hs, by omega_using [hroom], by rw [← hstat, h3]; decide⟩
    have hn : nextKeyPoint q = ⟨q.inputs, q.used + q.inputs.len, q.keys - 1, 128, q.statuses.tail⟩ := by
      simp only [nextKeyPoint, ← hstat, h3, Nat.reduceEqDiff, ite_false]
    simp only [KeyBranchResult, hc, ite_true, hn]
    refine ⟨⟨original, hq.1, ?_⟩, hq.2⟩
    rw [← hst]
    simp only [KeyPublic.tail, keyTail_public hk hs hr h3, List.tail_cons]

private theorem leafB {Φ : KeyPoint → State → Prop} {c : Prog isa}
    (hΦ : ∀ q s, Φ q s → KeyAny q.inputs s) (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

theorem key_branch_ct (a : Attempt) :
    RelCT isa (Two KeysGuard) (branch a.call) (fun _ _ => True) := by
  unfold branch
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  refine RelCT.seq (two_post (two_taint [.r31] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide)) scalars_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  unfold attemptOrRequest
  refine RelCT.seq (two_post (two_taint [.r31] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide)) room_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_
    (leafB (fun _ _ h => h.1.1.any) key_request_ct)
  exact RelCT.seq (two_post ((key_attempt_run_ct a).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, attempt_of_room h₁, attempt_of_room h₂, hsp⟩) fun _ _ h => h)
    fun q s h => key_attempt_ready a q s (attempt_of_room h)) key_classify_ct

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

end

end

/-! # The key search's timing depends on its public descriptor and statuses (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.PPC64LE.Taint
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (two_map)
open VG.Proof.Ffdh.PPC64LE.Generation (relCT_pushR0)
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search (ldf stf entry arguments terminal zeroOut zeroOutputs exhausted advance
  rejectedScalar rejectedPublic test classify request room finish)
open VG.Impl.Ffdh.PPC64LE.Cached.Search

/-! ## The loop -/

theorem key_iteration_ct (a : Attempt) :
    RelCT isa (Two KeyCTL) (iteration a.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_post (two_taint [.r31] key_ctl_pins (by taint_decide)) keys_ready) ?_
  exact RelCT.seq (two_post (key_branch_ct a) (key_branch_ready a))
    (two_taint [.r31] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_r31 h₁).trans (branch_r31 h₂).symm) (by taint_decide))

def KeyCTStep (q : KeyPoint) (s : State) : Prop :=
  if keyContinues q then isa.eval (.zero .d .r9) s = some true ∧ KeyCTL (nextKeyPoint q) s
  else isa.eval (.zero .d .r9) s = some false

theorem key_ct_step (a : Attempt) (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (iteration a.call) s (KeyCTStep q) := by
  unfold iteration
  refine WP.seq (WP.mono (keys_ready q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (key_branch_ready a q u hu) fun t ht => ?_)
  by_cases hc : keyContinues q
  · simp only [KeyBranchResult, hc, ite_true] at ht
    obtain ⟨⟨original, hl, hst⟩, hw⟩ := ht
    rw [← nextKeyPoint_inputs q] at hw
    refine WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ?_
    simp only [KeyCTStep, hc, ite_true]
    exact ⟨hz, original, hzl, hst⟩
  · simp only [KeyBranchResult, hc, ite_false] at ht
    obtain ⟨_, _, hd⟩ := ht
    refine WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => ?_
    simp only [KeyCTStep, hc, ite_false]
    exact hz

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s ∧ KeyCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (a : Attempt) (n : Nat) :
    RelCT isa (LoopPair n) (iteration a.call) fun s t =>
      isa.eval (.zero .d .r9) s = isa.eval (.zero .d .r9) t ∧
      (isa.eval (.zero .d .r9) s = some false → True) ∧
      (isa.eval (.zero .d .r9) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : KeyPoint) (s : State) (h : n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s) :
      WP isa (iteration a.call) s fun t => n = 128 * q.keys + q.scalars + 1 ∧ KeyCTStep q t :=
    WP.mono (key_ct_step a q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((key_iteration_ct a).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  by_cases hb : keyContinues q
  · simp only [KeyCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars + 1, ?_, nextKeyPoint q, rfl,
      h₁.2, h₂.2, hsp⟩
    have := nextKeyPoint_measure hb
    omega_using [hn, this]
  · simp only [KeyCTStep, hb, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => absurd (ht.symm.trans h₁) (by decide)⟩

theorem key_loop_ct (a : Attempt) :
    RelCT isa (Two KeyCTL) (.loop (iteration a.call) (.zero .d .r9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration a.call) (c := .zero .d .r9)
    (Q := fun _ _ => True) LoopPair (iteration_pair a) (128 * q.keys + q.scalars + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

/-! ## Entry and return -/

/-- A run's entry, with its public descriptor and its result's statuses. -/
def KeyStart (a : KeyPublic × List Nat) (s : State) : Prop :=
  KeyInput a.1 s ∧ (keyResult s).statuses = a.2

private theorem entry_pointer (p : KeyPublic) (s : State) (h : KeyInput p s) :
    WP isa (.block (entry.take 2)) s fun t =>
      t.gpr .r12 = p.control ∧ t.gpr .r11 = p.sp + BitVec.ofNat 64 96 := by
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 32) 64 = p.control :=
    (arg_value s 4).trans (congrArg KeyPublic.control h.2)
  have ha4 := input_args h 4 (by decide)
  have hd' := hd
  have ha4' := ha4
  simp only [Nat.reduceMul] at ha4 ha4'
  rw [VG.Offset.add_add] at hd' ha4'
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  unfold entry
  simp only [List.take_succ_cons, List.take_zero]
  prun [ea, hd, ha4, hd', ha4', h.sp_eq]

private theorem pins_E2 : Pins (fun (p : KeyPublic) (t : State) =>
    t.gpr .r12 = p.control ∧ t.gpr .r11 = p.sp + BitVec.ofNat 64 96) [.r11, .r12] := by
  rintro p s t ⟨a12, a11⟩ ⟨b12, b11⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a11, b11]
  · rw [a12, b12]

private theorem entry_ct : RelCT isa (Two KeyInput) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two KeyInput) (.block (entry.take 2 ++ entry.drop 2)) _
  exact RelCT.block_append (RelCT.seq (two_post (two_taint [] key_no_pins (by taint_decide)) entry_pointer)
    (two_taint _ pins_E2 (by taint_decide)))

/-- After the entry: the controller's words written. -/
def KeyEntered (a : KeyPublic × List Nat) (t : State) : Prop :=
  ∃ s, KeyStart a s ∧ t.gpr .r31 = a.1.control ∧
    t.mem = writeController s.mem a.1.control (entryValues s) ∧ Keep entryRegs s t

private theorem entry_ready (a : KeyPublic × List Nat) (s : State) (h : KeyStart a s) :
    WP isa (.block entry) s (KeyEntered a) :=
  WP.mono (entry_ok h.1) fun _ ⟨⟨hx, hm⟩, k⟩ => ⟨s, h, hx, hm, k⟩

private def initialPoint (a : KeyPublic × List Nat) : KeyPoint := ⟨a.1, 0, a.1.keys, a.1.scalars, a.2⟩

private theorem entered_ctl {a : KeyPublic × List Nat} {t : State} (h : KeyEntered a t) :
    KeyCTL (initialPoint a) (framed .r0 t) := by
  rcases a with ⟨p, l⟩
  obtain ⟨s, ⟨hi, hst⟩, hx, hm, k⟩ := h
  refine ⟨s, key_start hi hx hm k, ?_⟩
  show (p.tail (keyRand s) 0 p.keys p.scalars).statuses = l
  change (keyResult s).statuses = l at hst
  change KeyInput p s at hi
  rw [← hst, hi.tail_eq]

/-- `mflr r0` keeps the state after the entry. -/
private theorem mflr_ready (a : KeyPublic × List Nat) (t : State) (h : KeyEntered a t) :
    WP isa (.block [.mflr .r0]) t (KeyEntered a) := by
  obtain ⟨s, hi, hx, hm, k⟩ := h
  refine WP.mono (WP.keep [.r0] (Q := fun u => u.mem = t.mem) (by prun [exec_mflr]) (by decide))
    fun u ⟨hu, ku⟩ => ⟨s, hi, (ku.gpr _ (by decide)).trans hx, hu.trans hm, k.trans' (ku.mono (by decide))⟩

def KeyCTDone (p : KeyPublic) (s : State) : Prop := ∃ original r, KeyDone p original r s

private theorem frame_ct (a : Attempt) : RelCT isa (Two KeyEntered)
    (.frame (.push .r0) (.loop (iteration a.call) (.zero .d .r9)) (.pop .r0)) fun x y => x.sp = y.sp := by
  refine relCT_pushR0 (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨q, h₁, h₂, _⟩ => ?_) ?_
  · obtain ⟨original, hl, -⟩ := entered_ctl h₁
    obtain ⟨original', hl', -⟩ := entered_ctl h₂
    obtain ⟨t, s', e, -⟩ := key_loop a (n := 128 * q.1.keys + q.1.scalars + 1)
      (expected := (initialPoint q).inputs.tail (keyRand original) 0 q.1.keys q.1.scalars)
      ⟨0, _, _, rfl, hl, rfl, rfl⟩
    obtain ⟨t', s'', e', -⟩ := key_loop a (n := 128 * q.1.keys + q.1.scalars + 1)
      (expected := (initialPoint q).inputs.tail (keyRand original') 0 q.1.keys q.1.scalars)
      ⟨0, _, _, rfl, hl', rfl, rfl⟩
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · refine (key_loop_ct a).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨initialPoint q, entered_ctl h₁, entered_ctl h₂, by simp only [framed, hsp]⟩

private theorem search_ct (a : Attempt) : RelCT isa (Two KeyEntered) (search a.call) (fun _ _ => True) := by
  unfold search
  refine RelCT.seq (two_post (two_taint [] key_no_pins (by taint_decide)) mflr_ready)
    (RelCT.seq (frame_ct a) ?_)
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) [] key_no_pins (by taint_decide)).mono
    (fun _ _ hsp => ⟨(), trivial, trivial, hsp⟩) fun _ _ h => h

private theorem search_ready (a : Attempt) (q : KeyPublic × List Nat) (t : State) (h : KeyEntered q t) :
    WP isa (search a.call) t (KeyCTDone q.1) := by
  obtain ⟨s, ⟨hi, _⟩, hx, hm, k⟩ := h
  exact WP.mono (key_body a hi hx hm k) fun _ ⟨hd, _, _⟩ => ⟨s, _, hd⟩

private theorem finish_pointer (p : KeyPublic) (s : State) (h : KeyCTDone p s) :
    WP isa (.block (finish.take 3)) s fun t => t.gpr .r4 = p.up ∧ t.gpr .r31 = p.control := by
  obtain ⟨original, r, h⟩ := h
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hu := h.usedPtr
  simp only [Bignum.word, off] at hu
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  prun [ldf, h.r31, hu, hl 120 (by decide), hl 88 (by decide), hl 112 (by decide)]

private theorem finish_ct : RelCT isa (Two KeyCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two KeyCTDone) (.block (finish.take 3 ++ finish.drop 3)) _
  refine RelCT.block_append (RelCT.seq (two_post (two_taint [.r31] ?_ (by taint_decide)) finish_pointer) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.r31.trans h₂.r31.symm
  · exact two_taint [.r4, .r31] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

theorem key_code_ct (a : Attempt) :
    RelCT isa (Two KeyStart) (code a.call) (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (two_post (two_map Prod.fst (fun _ _ h => h.1) entry_ct) entry_ready)
    (RelCT.seq (two_post (search_ct a) (search_ready a))
      (two_map Prod.fst (fun _ _ h => h) finish_ct))

private theorem key_public_descriptor {s t : State} (h : keyPub s t) : keyOfState s = keyOfState t := by
  obtain ⟨hsp, hr, ha, hdom, hw, -⟩ := h
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r3, -, r5, -, r7, r8, r9, r10⟩ := hr
  change [word s.mem (stackArg s 4) 0, word s.mem (stackArg s 4) 8, word s.mem (stackArg s 4) 16,
    word s.mem (stackArg s 4) 24] = [word t.mem (stackArg t 4) 0, word t.mem (stackArg t 4) 8,
      word t.mem (stackArg t 4) 16, word t.mem (stackArg t 4) 24] at hw
  have h0 : s.mem.readW (stackArg s 4) 64 = t.mem.readW (stackArg t 4) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  have h1 : s.mem.readW (stackArg s 4 + 8) 64 = t.mem.readW (stackArg t 4 + 8) 64 := by
    have := (List.cons.inj (List.cons.inj hw).2).1
    simp only [Bignum.word, off] at this
    exact this
  unfold keyOfState
  rw [keyRetries, keyRetries, h0, h1, hdom, hsp, r3, r5, r7, r8, keyLen, keyLen, r9, r10,
    ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide)]

theorem key_constantTime (a : Attempt) :
    ConstantTime isa keyContract.pre keyContract.pub (code a.call) := by
  refine RelCT.constantTime ((key_code_ct a).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨(keyOfState s, (keyResult s).statuses), ⟨⟨hs, rfl⟩, rfl⟩,
    ⟨⟨ht, (key_public_descriptor hp).symm⟩, hp.2.2.2.2.2.symm⟩, hp.1⟩

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

end

end

/-! ### `Ffdh.PPC64LE.Cached.AttemptVerified`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.Cached.AttemptCTBody`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.Cached.AttemptBI`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.GenerateKey.CT`, which only this module used -/

section

/-!
# `vg_ffdh_generate_key` on PPC64LE: constant time

The public data `GD` is `vg_ffdh_derive_public`'s (`Derive.DD`) for x's and
`y`'s buffers, the bound and whether x is within it, and `rand`'s address.
x's mask runs without a branch (`KM1`, `KM2`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- The exchange's data of a run: the domain and g, x's and `y`'s buffers. -/
def gxOf (s : State) : XD := ⟨gcOf s, s.gpr .r5, s.gpr .r3, (s.gpr .r9).toNat⟩

/-- The public data of a run. -/
structure GD where
  d : DD
  R : Addr

/-! ## The predicates -/

/-! ## Pins -/

/-! ## The front and p's check -/

/-! ## x's cut -/

/-! ## After x's cut -/

/-- After `vg_ffdh_derive_public`'s body: the registers and the header's word
of x's mask, and the status. -/
def K6 (g : GD) (s : State) : Prop :=
  (s.gpr .r23 = g.d.x.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 g.d.x.c.k) ∧
    s.mem.readW (off g.d.x.c.S 64) 64 = off g.d.x.X 0 ∧ InRegions (s.rd ++ s.wr) (off g.d.x.c.S 64) 8 ∧
    Scr s g.d.x.X g.d.x.c.k ∧ (1 ≤ g.d.x.c.k ∧ g.d.x.c.k < 2 ^ 32) ∧
    ∃ st, s.gpr .r3 = BitVec.ofNat 64 st ∧ 1 ≤ st ∧ st < 4

/-- Before x's masked loop. -/
def K7 (g : GD) (s : State) : Prop :=
  (s.gpr .r25 = off g.d.x.X 0 ∧ s.gpr .r6 = BitVec.ofNat 64 g.d.x.c.k) ∧ s.gpr .r23 = g.d.x.c.S ∧
    Scr s g.d.x.X g.d.x.c.k ∧ (1 ≤ g.d.x.c.k ∧ g.d.x.c.k < 2 ^ 32) ∧ ∃ c, s.gpr .r17 = mask c

theorem pins_K6 : Pins K6 [.r23, .r28] := by
  intro g s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.1.1, h₂.1.1]
  · rw [h₁.1.2, h₂.1.2]

theorem pins_K7 : Pins K7 [.r25, .r6] := by
  intro g s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.1.1, h₂.1.1]
  · rw [h₁.1.2, h₂.1.2]

theorem KM1 {g : GD} {s : State} (h : K6 g s) :
    WP isa (.block (statusMask ++ ([.load .d .r25 .r23 64, .addi .r6 .r28 0] : List Instr))) s (K7 g) := by
  obtain ⟨⟨h23, h28⟩, hX, hrd, hx, hk, st, h3, hst1, hst⟩ := h
  refine WP.mono (WP.keep [.r0, .r6, .r12, .r17, .r25] (Q := fun t => t.gpr .r25 = off g.d.x.X 0 ∧
      t.gpr .r17 = mask (decide (st = 1)) ∧ t.gpr .r6 = BitVec.ofNat 64 g.d.x.c.k ∧ t.mem = s.mem) (by
    unfold statusMask
    prun [h3, h23, h28, hrd, hX, BitVec.add_zero, status_mask st hst hst1]) (by decide))
    fun t ⟨⟨a25, a17, a6, _⟩, k⟩ => ⟨⟨a25, a6⟩, (k.gpr .r23 (by decide)).trans h23, hx.congr k.wr, hk, _, a17⟩

theorem KM2 {g : GD} {s : State} (h : K7 g s) :
    WP isa (countLoop .r6 [.lbz .r16 .r25 0, .logic .and .r16 .r16 .r17, .stb .r16 .r25 0, .addi .r25 .r25 1]) s
      (fun t => CF g.d.x.c t) := by
  obtain ⟨⟨h25, h6⟩, h23, hx, hk, c, h17⟩ := h
  exact WP.mono (masked_ok hk.1 hk.2 hx h25 h17 h6) fun t ⟨_, kt⟩ => (kt.gpr .r23 (by decide)).trans h23

/-! ## Constant time -/

end VG.Proof.Ffdh.PPC64LE.GenerateKey

end

end

/-!
# `vg_ffdh_generate_key_cached` on PPC64LE: the public data, and the body's entry

The public data of an attempt (`CG`): `vg_ffdh_generate_key`'s (`GD`), with
x's range for x cut to the context's width, the context's address and the
width. `cg_toBI`: after the front, p's load and check reach the body with
what it needs (`BI`, `bodyC_ok`'s hypotheses), as `cg_correct` shows.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Ffdh.PPC64LE.GenerateKey (gcOf gxOf GD)
open VG.Proof.Ffdh.KeyScalar (cut)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot)

/-- x's value as the attempt cuts it from `rand`'s `k` octets at `R`. -/
abbrev cgX (k bits : Nat) (m : Mem) (R : Addr) : Nat :=
  Spec.Rsa.os2ip (cut (Spec.Rsa.bytesAt m R k) (k - (bits + 7) / 8) (tbOf bits))

/-- The public data of an attempt. -/
structure CG where
  g : GD
  C : Addr
  bits : Nat

abbrev CG.c (q : CG) : CD := q.g.d.x.c

def cgOf (s : State) : CG :=
  ⟨⟨⟨gxOf s, Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p,
    decide (0 < cgX (s.gpr .r9).toNat (Spec.Ffdh.generationScalarBits (cgA s)) s.mem (s.gpr .r10) ∧
      cgX (s.gpr .r9).toNat (Spec.Ffdh.generationScalarBits (cgA s)) s.mem (s.gpr .r10) <
        Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p)⟩, s.gpr .r10⟩,
    stackArg s 3, Spec.Ffdh.generationScalarBits (cgA s)⟩

/-- What the body needs (`bodyC_ok`'s hypotheses), and x's range. -/
structure BI (S D X O R C : Addr) (Z k L p bits : Nat) (v : Bool) (s : State) : Prop where
  env : Env s S Z ((k + 7) / 8)
  h23 : s.gpr .r23 = S
  h21 : s.gpr .r21 = D
  h27 : s.gpr .r27 = BitVec.ofNat 64 L
  h28 : s.gpr .r28 = BitVec.ofNat 64 k
  hk : 64 ≤ k
  hk' : k ≤ 1024
  hL : L = 2 * k ∨ L = 3 * k
  hX : s.mem.readW (off S 64) 64 = off X 0
  hXL : s.mem.readW (off S 72) 64 = BitVec.ofNat 64 k
  hO : s.mem.readW (off S 80) 64 = off O 0
  hR : s.mem.readW (off S 88) 64 = off R 0
  hbw : s.mem.readW (off S hBits) 64 = BitVec.ofNat 64 bits
  hyw : s.mem.readW (off S hBytes) 64 = BitVec.ofNat 64 ((bits + 7) / 8)
  hRw : s.mem.readW (off S hRows) 64 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)
  hCw : s.mem.readW (off S hCtx) 64 = C
  hc : CtxRd s S Z C ((k + 7) / 8)
  hsepCX : ∀ y, ofs C y < 8 * ctxWords ((k + 7) / 8) → k ≤ ofs X y
  hents : ∀ a < 32, ent s.mem C ((k + 7) / 8) a =
    combM (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p ((k + 7) / 8)
      (Spec.Rsa.FixedBaseComb.exponent bits a)
  hr2 : val32 s.mem C (rowOff ((k + 7) / 8) 1) (2 * ((k + 7) / 8)) =
    2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % p
  hb1 : 1 ≤ bits
  hbk : bits ≤ 8 * k
  hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1
  hsepD : ∀ i < L, ∀ x, ofs S x < Z → off D i ≠ x
  hrdR : ∀ i < k, InRegions (s.rd ++ s.wr) (off R i) 1
  hx : Scr s X k
  hsepX : ∀ i < k, ∀ y, ofs S y < Z → off X i ≠ y
  hsepBX : ∀ y, ofs S y < Z → k ≤ ofs X y
  hsepRX : ∀ i < k, ∀ y, ofs X y < k → off R i ≠ y
  hsepDX : ∀ i < L, ∀ y, ofs X y < k → off D i ≠ y
  hsepXO : ∀ i < k, ∀ y, ofs O y < k → off X i ≠ y
  hsepOX : ∀ i < k, ∀ y, ofs X y < k → off O i ≠ y
  ho : Scr s O k
  hsepO : ∀ x, ofs O x < k → Z ≤ ofs S x
  hsepB : ∀ x, ofs S x < Z → k ≤ ofs O x
  hP : arr s.mem S ((k + 7) / 8) 0 = p
  hp2 : 2 ≤ p
  hodd : p % 2 = 1
  hpk : p < 256 ^ k
  hv : (0 < cgX k bits s.mem R ∧ cgX k bits s.mem R < Derive.bnd s.mem D k L p) ↔ v = true

/-- `BI` of the public data. -/
abbrev BIq (q : CG) (s : State) : Prop :=
  BI q.c.S q.c.D q.g.d.x.X q.g.d.x.O q.g.R q.C q.c.Z q.c.k q.c.L q.c.p q.bits q.g.d.v s

/-- After p's check: whether p is valid, the working space, and, if it is,
what the body needs. -/
def A4 (q : CG) (s : State) : Prop :=
  ((s.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid q.c.p q.c.k = true) ∧ s.gpr .r23 = q.c.S) ∧
    (s.gpr .r0 = 0 → BIq q s)

/-- The front, then p's load and check, reach the body with `BI`. -/
theorem cg_toBI {s : State} (h : cgContract.pre s) :
    WP isa (.block front) s fun s₁ => Base (gcOf s) s₁ ∧ WP isa loadP s₁ (A4 (cgOf s)) := by
  have hpre := h
  obtain ⟨-, hrd, hwr, dXY, dXD, dXR, dXS, dXC, -, dYD, -, dYS, dYC, -, dDS, dRS, dSC, -, nwX, nwY, -, nwR, nwS, nwC,
    ⟨hk64, hk1024⟩, hL, hxl, hyl, hrl, hsl, hdv, hctx⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  rw [hxl] at hwr dXY dXD dXR dXS dXC nwX
  rw [hyl] at hwr dXY dYD dYS dYC nwY
  rw [hrl] at hrd dXR dRS nwR
  obtain hcl : (stackArg s 4).toNat = 3 + 34 * (((s.gpr .r9).toNat + 7) / 8) := by
    rw [hctx.1]
    simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
    omega_using []
  have hctxw := hctx.2
  rw [hcl] at nwC hctxw dXC dYC dSC hrd
  refine WP.mono (cg_front hpre) fun s₁ ⟨hb, w8, w9, w10, w11, _, wc0, wc8, wc16, wc24, hby, k1⟩ => ⟨hb, ?_⟩
  have hk := hb.k64
  have hk' := hb.k1024
  have hLk := hb.hL
  have hZ := hb.env.hZ
  obtain e0 := Domain.slot_eq (gcOf s).w 0
  obtain e28 := Domain.slot_eq (gcOf s).w 28
  refine WP.mono (loadP_ok hb.env hb.r21 hb.r28 rfl hk hk' (fun i hi => hb.rdD i (by
      rcases hLk with h | h <;> omega_using [hi, h])) (fun i hi => hb.sepD i (by rcases hLk with h | h <;> omega_using [hi, h])))
    fun s₂ ⟨⟨p2, c2, b2⟩, k2⟩ => ?_
  obtain hb2 := hb.keep k2 b2
  obtain k12 := k1.trans k2
  obtain hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off Q i ≠ y) →
      Spec.Rsa.bytesAt s₂.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq => by
    rw [b2.bytesAt hZ hq]; exact hby Q n hq
  have sepD : ∀ i < (s.gpr .r8).toNat, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off (s.gpr .r7) i ≠ y :=
    hb.sepD
  have hL' : (s.gpr .r8).toNat = 2 * (s.gpr .r9).toNat ∨ (s.gpr .r8).toNat = 3 * (s.gpr .r9).toNat := hLk
  obtain ep : (gcOf s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := by
    show Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat).take (s.gpr .r9).toNat) = _
    rw [Proof.Ffdh.take_bytesAt _ _ (by omega_using [hL'])]
  obtain eD : Spec.Rsa.bytesAt s₁.mem (s.gpr .r7) (s.gpr .r9).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat := hby _ _ fun i hi => sepD i (by omega_using [hL', hi])
  rw [show (gcOf s).D = s.gpr .r7 from rfl, show (gcOf s).k = (s.gpr .r9).toNat from rfl, eD] at p2 c2
  refine ⟨⟨by show _ ↔ Spec.Rsa.modulusValid (gcOf s).p _ = true; rw [ep]; exact c2, hb2.r23⟩, fun hz => ?_⟩
  obtain hmodP := c2.mp hz
  show BI (stackArg s 1) (s.gpr .r7) (s.gpr .r3) (s.gpr .r5) (s.gpr .r10) (stackArg s 3)
    ((stackArg s 2).toNat * 8) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p
    (Spec.Ffdh.generationScalarBits (cgA s)) (decide (0 < cgX (s.gpr .r9).toNat
      (Spec.Ffdh.generationScalarBits (cgA s)) s.mem (s.gpr .r10) ∧
      cgX (s.gpr .r9).toNat (Spec.Ffdh.generationScalarBits (cgA s)) s.mem (s.gpr .r10) <
        Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p)) s₂
  rw [ep]
  obtain hlenD : (s.gpr .r9).toNat ≤ (cgDom s).length := by
    rw [VG.Proof.Bignum.bytesAt_length]; rcases hL' with h | h <;> omega_using [h]
  obtain hmod := VG.Proof.Ffdh.domainValid_mod hdv
  obtain hpd : (cgA s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := by
    rw [VG.Proof.Ffdh.domainOf_p _ _ (by rcases hL' with h | h <;> omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hlenD, h])]
  obtain hbits := genBits_facts hdv
  obtain hwv : Spec.Rsa.wordsAt s.mem (stackArg s 3) (3 + 34 * (((s.gpr .r9).toNat + 7) / 8)) =
      VG.Proof.Ffdh.generationValues (s.gpr .r9).toNat (cgDom s) := by
    obtain e := VG.Proof.Ffdh.generationPrecompute_eq hlenD hmod
    rw [hctxw] at e; exact Option.some.inj e
  obtain sepCSi := sep_of_disjoint dSC.symm (by omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hL', hlenD, hbits])
  obtain hcm : ∀ i < 8 * (3 + 34 * (((s.gpr .r9).toNat + 7) / 8)), s₂.mem (stackArg s 3 + BitVec.ofNat 64 i) =
      s.mem (stackArg s 3 + BitVec.ofNat 64 i) := fun i hi =>
    byte_of_bytesAt (hsep _ (8 * (3 + 34 * (((s.gpr .r9).toNat + 7) / 8))) fun j hj => sepCSi j (by omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hL', hlenD, hbits, hi, hj])) hi
  obtain hwv2 : Spec.Rsa.wordsAt s₂.mem (stackArg s 3) (3 + 34 * (((s.gpr .r9).toNat + 7) / 8)) =
      VG.Proof.Ffdh.generationValues (s.gpr .r9).toNat (cgDom s) := by rw [wordsAt_congr hcm, hwv]
  obtain hpk : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) < 256 ^ (s.gpr .r9).toNat := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  obtain hf := modulus_facts hmodP
  obtain hpw : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) <
      2 ^ (64 * (((s.gpr .r9).toNat + 7) / 8)) := Nat.lt_of_lt_of_le hpk (by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega_using []))
  obtain ⟨cb, cy, cr, -, -⟩ := ctx_facts hwv (by rw [hpd]; omega_using [hf]) (by rw [hpd]; exact hpw)
  obtain ⟨-, -, -, cr2, cent⟩ := ctx_facts hwv2 (by rw [hpd]; omega_using [hf]) (by rw [hpd]; exact hpw)
  rw [hpd] at cr2 cent
  obtain hg : (cgA s).g = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off (s.gpr .r7) (s.gpr .r9).toNat)
      (s.gpr .r9).toNat) := by
    rw [VG.Proof.Ffdh.domainOf_g _ _ (by rcases hL' with h | h <;> omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hlenD, hbits, h]), hsep _ _ fun i hi => by
      rw [off_off']; exact sepD _ (by rcases hL' with h | h <;> omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hlenD, hbits, hi, h])]
  rw [hg] at cent
  obtain hw2 : ∀ d, d + 8 ≤ 256 → word s₂.mem (stackArg s 1) d = word s₁.mem (stackArg s 1) d := fun d hd => by
    have b2' : Body (stackArg s 1) (gcOf s).w s₁.mem s₂.mem := b2
    rw [Outside.word b2' (by omega_using [e0, hd]) (by omega_using [hd])]
  obtain h4 : s.gpr .r4 = BitVec.ofNat 64 (s.gpr .r9).toNat := by
    rw [← hxl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain eR : Spec.Rsa.bytesAt s₂.mem (s.gpr .r10) (s.gpr .r9).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r10) (s.gpr .r9).toNat := hsep _ _ (sep_of_disjoint dRS (by omega_using []))
  obtain eb : Derive.bnd s₂.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat =
      Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat := by
    funext P
    unfold Derive.bnd
    by_cases hq : (s.gpr .r8).toNat = 3 * (s.gpr .r9).toNat
    · rw [ite_eq_left hq, ite_eq_left hq, hsep _ _ fun i hi => by rw [off_off']; exact sepD _ (by omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hL', hlenD, hbits, hq, hi])]
    · rw [ite_eq_right hq, ite_eq_right hq]
  have g23 : s₂.gpr .r23 = stackArg s 1 := hb2.r23
  have e2 : Env s₂ (stackArg s 1) ((stackArg s 2).toNat * 8) (((s.gpr .r9).toNat + 7) / 8) := hb2.env
  exact {
    env := e2
    h23 := g23
    h21 := hb2.r21
    h27 := hb2.r27
    h28 := hb2.r28
    hk := hk
    hk' := hk'
    hL := hL'
    hX := by show word s₂.mem _ 64 = _; rw [hw2 64 (by omega_using []), w8]; simp [off]
    hXL := by show word s₂.mem _ 72 = _; rw [hw2 72 (by omega_using []), w9, h4]
    hO := by show word s₂.mem _ 80 = _; rw [hw2 80 (by omega_using []), w10]; simp [off]
    hR := by show word s₂.mem _ 88 = _; rw [hw2 88 (by omega_using []), w11]; simp [off]
    hbw := by show word s₂.mem _ 8 = _; rw [hw2 8 (by omega_using []), wc8]; exact cb
    hyw := by show word s₂.mem _ 16 = _; rw [hw2 16 (by omega_using []), wc16]; exact cy
    hRw := by show word s₂.mem _ 24 = _; rw [hw2 24 (by omega_using []), wc24]; exact cr
    hCw := by rw [show hCtx = 0 from rfl]; exact (hw2 0 (by omega_using [])).trans wc0
    hc := ⟨by have := nwC; unfold ctxWords; omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hL', hlenD, hbits, this], fun d hd => by
        rw [k12.rd, k12.wr]
        exact ⟨⟨stackArg s 3, (3 + 34 * (((s.gpr .r9).toNat + 7) / 8)) * 8⟩,
          List.mem_append_left _ (by rw [hrd]; simp),
          Offset.contains_base _ (by unfold ctxWords at hd; omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hL', hlenD, hbits, hd]) (by unfold ctxWords at hd; omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hL', hlenD, hbits, hd])⟩,
      fun x hx => by
        have := Pub.sep_of_disjoint dSC.symm x (by
          simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs, ctxWords] at hx ⊢; omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hL', hlenD, hbits, hx])
        simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs] at this ⊢; omega_using [this]⟩
    hsepCX := fun y hy => by
      have := Pub.sep_of_disjoint dXC.symm y (by
        simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs, ctxWords] at hy ⊢; omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hL', hlenD, hbits, hy])
      simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs] at this ⊢; omega_using [nwX, nwY, nwR, nwC, hk64, hk1024, hxl, hyl, hrl, hsl, hcl, hL', hlenD, hbits, this]
    hents := cent
    hr2 := cr2
    hb1 := hbits.1
    hbk := hbits.2
    hrdD := hb2.rdD
    hsepD := sepD
    hrdR := by
      rw [k12.rd, k12.wr]
      exact rd_of_mem (s := s) (D := s.gpr .r10) (L := (s.gpr .r9).toNat) (by rw [hrd]; simp) (by omega_using [])
    hx := Scr.of_mem (by rw [k12.wr, hwr]; simp) nwX
    hsepX := sep_of_disjoint dXS (by omega_using [])
    hsepBX := Pub.sep_of_disjoint dXS.symm
    hsepRX := sep_of_disjoint dXR.symm (by omega_using [])
    hsepDX := sep_of_disjoint dXD.symm (by omega_using [])
    hsepXO := sep_of_disjoint dXY (by omega_using [])
    hsepOX := sep_of_disjoint dXY.symm (by omega_using [])
    ho := Scr.of_mem (by rw [k12.wr, hwr]; simp) nwY
    hsepO := Pub.sep_of_disjoint dYS
    hsepB := Pub.sep_of_disjoint dYS.symm
    hP := p2
    hp2 := hf.1
    hodd := hf.2
    hpk := hpk
    hv := by simp only [cgX]; rw [eR, eb, decide_eq_true_iff] }

end VG.Proof.Ffdh.PPC64LE.Cached

end

end

/-!
# `vg_ffdh_generate_key_cached` on PPC64LE: the body in constant time

From `BI`, each piece of the body runs from a predicate that fixes the
registers it computes addresses and branches from as functions of the public
data `CG`, and states that the rest reaches the next such predicate, by
correctness (`stage1_ok`, `bad_ok`, `good_ok`); between them, the taint
checker. The values loaded from memory (the header's words, the context's)
are pinned after the block that loads them.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Impl.Ffdh.PPC64LE.GenerateKey (cutBody)
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Ffdh.PPC64LE.GenerateKey (GD K6 K7 KM1 KM2 pins_K6 pins_K7)
open VG.Proof.Ffdh.KeyScalar (cut)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE.Win (mask)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint two_taintR)
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (two_ite')

section
variable {S D X O R C : Addr} {Z k L p bits : Nat} {v : Bool}

/-- The registers and header words x's range reads. -/
structure LF (S D X : Addr) (Z k L : Nat) (s : State) : Prop where
  env : Env s S Z ((k + 7) / 8)
  h23 : s.gpr .r23 = S
  h21 : s.gpr .r21 = D
  h27 : s.gpr .r27 = BitVec.ofNat 64 L
  h28 : s.gpr .r28 = BitVec.ofNat 64 k
  hX : s.mem.readW (off S 64) 64 = off X 0
  hXL : s.mem.readW (off S 72) 64 = BitVec.ofNat 64 k

/-- After x's cut and range, from `s₀`: `scalarC_ok`'s and `xRange_ok`'s
results. -/
def XI (S D X R : Addr) (k L bits : Nat) (s₀ u : State) : Prop :=
  ∃ s₃, ((Spec.Rsa.bytesAt s₃.mem X k = cut (Spec.Rsa.bytesAt s₀.mem R k) (k - (bits + 7) / 8) (tbOf bits) ∧
      Outside X 0 k s₀.mem s₃.mem) ∧ Keep scalarCRegs s₀ s₃) ∧
    ((u.gpr .r26 = mask (decide (0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₃.mem X k) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₃.mem X k) <
          Derive.bnd s₃.mem D k L (arr s₃.mem S ((k + 7) / 8) 0))) ∧
      arr u.mem S ((k + 7) / 8) 0 = arr s₃.mem S ((k + 7) / 8) 0 ∧ Body S ((k + 7) / 8) s₃.mem u.mem ∧
      u.gpr .r10 = off S (slot ((k + 7) / 8) 0)) ∧ Keep Derive.xRangeRegs s₃ u)

/-- x's cut, by correctness, with x's range to come. -/
theorem stage1_ok {s : State} (h : BI S D X O R C Z k L p bits v s) :
    WP isa scalar s fun s₃ => LF S D X Z k L s₃ ∧ WP isa Derive.xRange s₃ (XI S D X R k L bits s) := by
  have hZ := h.env.hZ
  obtain e0 := Domain.slot_eq ((k + 7) / 8) 0
  obtain e28 := Domain.slot_eq ((k + 7) / 8) 28
  have hk := h.hk
  have hk' := h.hk'
  refine WP.mono (scalarC_ok h.env h.h23 h.h28 (by omega_using [hk]) h.hk' h.hb1 h.hbk h.hbw h.hyw h.hX h.hR h.hrdR h.hx
    h.hsepRX) fun s₃ ⟨⟨xb, xout⟩, k3⟩ => ?_
  obtain osc := GenerateKey.out_scr xout h.hsepBX
  obtain hw3 : ∀ d, d + 8 ≤ 256 → word s₃.mem S d = word s.mem S d := fun d hd =>
    Outside.word osc (Or.inl (by omega_using [hZ, e28, hd])) (by omega_using [hd])
  obtain hp3 : arr s₃.mem S ((k + 7) / 8) 0 = p := by
    rw [arr, Outside.val32 osc (Or.inl (by omega_using [hZ, e0, e28])) (by omega_using [e0, hk'])]; exact h.hP
  obtain e3 := h.env.keep k3 (by decide)
  obtain g23 : s₃.gpr .r23 = S := (k3.gpr .r23 (by decide)).trans h.h23
  obtain g21 : s₃.gpr .r21 = D := (k3.gpr .r21 (by decide)).trans h.h21
  obtain g27 : s₃.gpr .r27 = BitVec.ofNat 64 L := (k3.gpr .r27 (by decide)).trans h.h27
  obtain g28 : s₃.gpr .r28 = BitVec.ofNat 64 k := (k3.gpr .r28 (by decide)).trans h.h28
  obtain hX3 : s₃.mem.readW (off S 64) 64 = off X 0 := by
    show word s₃.mem S 64 = _; rw [hw3 64 (by omega_using [])]; exact h.hX
  obtain hXL3 : s₃.mem.readW (off S 72) 64 = BitVec.ofNat 64 k := by
    show word s₃.mem S 72 = _; rw [hw3 72 (by omega_using [])]; exact h.hXL
  obtain rdQ : L = 3 * k → ∀ i < k, InRegions (s₃.rd ++ s₃.wr) (off (off D (2 * k)) i) 1 := fun hq i hi => by
    rw [Domain.off_off', k3.rd, k3.wr]; exact h.hrdD _ (by omega_using [hq, hi])
  obtain sepQ : L = 3 * k → ∀ i < k, ∀ x, ofs S x < Z → off (off D (2 * k)) i ≠ x := fun hq i hi => by
    rw [Domain.off_off']; exact h.hsepD _ (by omega_using [hq, hi])
  refine ⟨⟨e3, g23, g21, g27, g28, hX3, hXL3⟩, WP.mono (Derive.xRange_ok (xl := k) e3 g23 g21 g27 g28 (by omega_using [hk])
    (by omega_using []) (by rcases h.hL with e | e <;> omega_using [hk', e]) (by omega_using [hk']) (by omega_using [hk]) (Nat.le_refl _) hX3 hXL3
    (fun i hi => (h.hx.congr k3.wr).ld (d := i) (n := 1) (by omega_using [hi])) h.hsepX rdQ sepQ (by rw [hp3]; have := h.hp2; omega_using [this]))
    fun u hu => ⟨s₃, ⟨⟨xb, xout⟩, k3⟩, hu⟩⟩

end

/-! ## x's cut -/

/-- The shift of the first octet's mask. -/
abbrev shiftOf (bits : Nat) : BitVec 64 := BitVec.ofNat 64 (8 * ((bits + 7) / 8) - bits)

/-- Before x's range. -/
def PX' (q : CG) (s₀ t : State) : Prop :=
  LF q.c.S q.c.D q.g.d.x.X q.c.Z q.c.k q.c.L t ∧
    WP isa Derive.xRange t (XI q.c.S q.c.D q.g.d.x.X q.g.R q.c.k q.c.L q.bits s₀)

def PX (q : CG) (t : State) : Prop := ∃ s₀, BIq q s₀ ∧ PX' q s₀ t

/-- After `maskByte`, with the rest of x's cut to come. -/
def B2' (q : CG) (s₀ t : State) : Prop :=
  (t.mem = s₀.mem ∧ Keep [.r14, .r17, .r18] s₀ t) ∧
    WP isa (.seq (.block sbBlock) (Precompute.countLoop .r6 cutBody)) t (PX' q s₀)

def B2 (q : CG) (t : State) : Prop := ∃ s₀, BIq q s₀ ∧ B2' q s₀ t

/-- After `maskByte`'s block: the shift in `r17`. -/
def B1 (q : CG) (t : State) : Prop :=
  ∃ s₀, BIq q s₀ ∧ t.gpr .r17 = shiftOf q.bits ∧ WP isa mbIte t (B2' q s₀)

/-- After `sbBlock`: `rand`'s and x's addresses, the count and the index. -/
def B3 (q : CG) (t : State) : Prop :=
  ∃ s₀, BIq q s₀ ∧ (t.gpr .r24 = off q.g.R 0 ∧ t.gpr .r25 = off q.g.d.x.X 0 ∧
    t.gpr .r6 = BitVec.ofNat 64 q.c.k ∧ t.gpr .r4 = BitVec.ofNat 64 0) ∧
    WP isa (Precompute.countLoop .r6 cutBody) t (PX' q s₀)

/-- After `xLoadPre`: `Derive.R1`'s registers. -/
def R1c (q : CG) (t : State) : Prop :=
  ∃ s₀, BIq q s₀ ∧ (t.gpr .r10 = off q.c.S (slot q.c.w 4) ∧ t.gpr .r12 = off q.g.d.x.X 0 ∧
    t.gpr .r6 = BitVec.ofNat 64 q.c.k ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * q.c.w) ∧ t.gpr .r21 = q.c.D ∧
    t.gpr .r23 = q.c.S ∧ t.gpr .r27 = BitVec.ofNat 64 q.c.L ∧ t.gpr .r28 = BitVec.ofNat 64 q.c.k ∧
    t.gpr .r29 = BitVec.ofNat 64 (8 * (q.c.w + 2)) ∧ t.gpr .r31 = q.c.S) ∧
    WP isa (.seq Derive.xLoadRest Derive.xMask) t
      (XI q.c.S q.c.D q.g.d.x.X q.g.R q.c.k q.c.L q.bits s₀)

/-- After x's range. -/
def XIc (q : CG) (u : State) : Prop :=
  ∃ s₀, BIq q s₀ ∧ XI q.c.S q.c.D q.g.d.x.X q.g.R q.c.k q.c.L q.bits s₀ u

theorem pins_BI : Pins BIq [.r23] := by
  intro q s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr; subst hr; rw [h₁.h23, h₂.h23]

theorem pins_B1 : Pins B1 [.r17] := by
  rintro q s₁ s₂ ⟨_, _, a, _⟩ ⟨_, _, b, _⟩ r hr
  rw [List.mem_singleton] at hr; subst hr; rw [a, b]

theorem pins_B2 : Pins B2 [.r23, .r28] := by
  rintro q s₁ s₂ ⟨a₀, ha, ⟨-, ka⟩, -⟩ ⟨b₀, hb, ⟨-, kb⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [ka.gpr .r23 (by decide), kb.gpr .r23 (by decide), ha.h23, hb.h23]
  · rw [ka.gpr .r28 (by decide), kb.gpr .r28 (by decide), ha.h28, hb.h28]

theorem pins_B3 : Pins B3 [.r24, .r25, .r6, .r4] := by
  rintro q s₁ s₂ ⟨_, _, ⟨a24, a25, a6, a4⟩, _⟩ ⟨_, _, ⟨b24, b25, b6, b4⟩, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a24, b24]
  · rw [a25, b25]
  · rw [a6, b6]
  · rw [a4, b4]

theorem pins_PX : Pins PX [.r23] := by
  rintro q s₁ s₂ ⟨_, _, a, _⟩ ⟨_, _, b, _⟩ r hr
  rw [List.mem_singleton] at hr; subst hr; rw [a.h23, b.h23]

theorem pins_R1c : Pins R1c [.r6, .r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29, .r31] := by
  rintro q s₁ s₂ ⟨_, _, ⟨a10, a12, a6, a11, a21, a23, a27, a28, a29, a31⟩, _⟩
    ⟨_, _, ⟨b10, b12, b6, b11, b21, b23, b27, b28, b29, b31⟩, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a6, b6]
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a12, b12]
  · rw [a21, b21]
  · rw [a23, b23]
  · rw [a27, b27]
  · rw [a28, b28]
  · rw [a29, b29]
  · rw [a31, b31]

theorem BI_B1 {q : CG} {s : State} (h : BIq q s) : WP isa (.block mbBlock) s (B1 q) := by
  have hZ := h.env.hZ
  obtain hw := Domain.slot_eq ((q.c.k + 7) / 8) 28
  obtain hs1 := stage1_ok h
  rw [scalar_eq] at hs1
  obtain hm := WP.and (maskByte_ok h.env.hs (by omega_using [hZ, hw]) h.h23 h.hbw h.hyw (by have := h.hbk; have := h.hk'; omega_arith))
    (WP.seq_iff.mp hs1)
  rw [maskByte_eq] at hm
  exact WP.mono (WP.and (mb_ok h.env.hs (by omega_using [hZ, hw]) h.h23 h.hbw h.hyw (by have := h.hbk; have := h.hk'; omega_arith))
    (WP.seq_iff.mp hm)) fun t ⟨⟨⟨a17, _⟩, _⟩, hw⟩ => ⟨s, h, a17,
      WP.mono hw fun u ⟨⟨⟨_, um⟩, uk⟩, hu⟩ => ⟨⟨um, uk⟩, hu⟩⟩

theorem B2_B3 {q : CG} {s : State} (h : B2 q s) : WP isa (.block sbBlock) s (B3 q) := by
  obtain ⟨s₀, h₀, ⟨hm, hk⟩, hw⟩ := h
  have hZ := h₀.env.hZ
  obtain hw28 := Domain.slot_eq ((q.c.k + 7) / 8) 28
  refine WP.mono (WP.and (sb_ok (bits := q.bits) (X := q.g.d.x.X) (R := q.g.R) (h₀.env.hs.congr hk.wr) (by omega_using [hZ, hw28])
    ((hk.gpr .r23 (by decide)).trans h₀.h23) ((hk.gpr .r28 (by decide)).trans h₀.h28)
    (by have := h₀.hbk; omega_using [this]) (by have := h₀.hk'; omega_using [this])
    (by rw [hm]; exact h₀.hyw) (by rw [hm]; exact h₀.hX) (by rw [hm]; exact h₀.hR)) (WP.seq_iff.mp hw))
    fun t ⟨⟨⟨_, a24, a25, a6, a4, _⟩, _⟩, hw'⟩ => ⟨s₀, h₀, ⟨a24, a25, a6, a4⟩, hw'⟩

theorem PX_R1c {q : CG} {s : State} (h : PX q s) : WP isa (.block Derive.xLoadPre) s (R1c q) := by
  obtain ⟨s₀, h₀, hl, hw⟩ := h
  unfold Derive.xRange at hw
  refine WP.mono (WP.and (Derive.xLoadPre_ok hl.env hl.h23 hl.hX hl.hXL) (WP.seq_iff.mp hw))
    fun t ⟨⟨⟨a10, a12, a6, _⟩, kt⟩, hw'⟩ => ⟨s₀, h₀, ⟨a10, a12, a6, (kt.gpr .r11 (by decide)).trans hl.env.h11,
      (kt.gpr .r21 (by decide)).trans hl.h21, (kt.gpr .r23 (by decide)).trans hl.h23,
      (kt.gpr .r27 (by decide)).trans hl.h27, (kt.gpr .r28 (by decide)).trans hl.h28,
      (kt.gpr .r29 (by decide)).trans hl.env.h29, (kt.gpr .r31 (by decide)).trans hl.env.h31⟩, hw'⟩

/-- x's cut. -/
theorem scalar_rel : RelCT isa (Two BIq) scalar (Two PX) := by
  rw [scalar_eq, maskByte_eq]
  exact RelCT.seq (R := Two B2) (RelCT.seq (R := Two B1)
    (two_post (two_taint _ pins_BI (by taint_decide)) fun _ _ h => BI_B1 h)
    (two_post (two_taint _ pins_B1 (by taint_decide)) fun _ _ ⟨s₀, h₀, _, hw⟩ =>
      WP.mono hw fun _ hu => ⟨s₀, h₀, hu⟩))
    (RelCT.seq (R := Two B3) (two_post (two_taint _ pins_B2 (by taint_decide)) fun _ _ h => B2_B3 h)
      (two_post (two_taint _ pins_B3 (by taint_decide)) fun _ _ ⟨s₀, h₀, _, hw⟩ =>
        WP.mono hw fun _ hu => ⟨s₀, h₀, hu⟩))

/-- x's range. -/
theorem xRange_rel : RelCT isa (Two PX) Derive.xRange (Two XIc) := by
  unfold Derive.xRange
  exact RelCT.seq (R := Two R1c) (two_post (two_taint _ pins_PX (by taint_decide)) fun _ _ h => PX_R1c h)
    (two_post (two_taint _ pins_R1c (by taint_decide)) fun _ _ ⟨s₀, h₀, _, hw⟩ =>
      WP.mono hw fun _ hu => ⟨s₀, h₀, hu⟩)

/-! ## After x's range -/

section
variable {S D X O R C : Addr} {Z k L p bits : Nat} {v : Bool}

/-- What holds after x's range, from `BI`. -/
structure XF (S D X R C : Addr) (Z k p bits : Nat) (v : Bool) (s₀ u : State) : Prop where
  env : Env u S Z ((k + 7) / 8)
  h23 : u.gpr .r23 = S
  h28 : u.gpr .r28 = BitVec.ofNat 64 k
  hw : ∀ d, d + 8 ≤ 256 → word u.mem S d = word s₀.mem S d
  xb : Spec.Rsa.bytesAt u.mem X k = cut (Spec.Rsa.bytesAt s₀.mem R k) (k - (bits + 7) / 8) (tbOf bits)
  hp : arr u.mem S ((k + 7) / 8) 0 = p
  keep : Keep (scalarCRegs ++ Derive.xRangeRegs) s₀ u
  cx : Outside C (8 * ctxWords ((k + 7) / 8)) (2 ^ 64) s₀.mem u.mem
  r26 : (u.gpr .r26 == 0) = !v

theorem xf_of {s₀ u : State} (h : BI S D X O R C Z k L p bits v s₀) (hx : XI S D X R k L bits s₀ u) :
    XF S D X R C Z k p bits v s₀ u := by
  obtain ⟨s₃, ⟨⟨xb, xout⟩, k3⟩, ⟨a26, p4, b4, a10⟩, k4⟩ := hx
  have hZ := h.env.hZ
  have hnw := h.env.hs.nowrap
  have hk := h.hk
  obtain e0 := Domain.slot_eq ((k + 7) / 8) 0
  obtain e28 := Domain.slot_eq ((k + 7) / 8) 28
  obtain osc := GenerateKey.out_scr xout h.hsepBX
  obtain hw3 : ∀ d, d + 8 ≤ 256 → word s₃.mem S d = word s₀.mem S d := fun d hd =>
    Outside.word osc (Or.inl (by omega_using [hZ, e28, hd])) (by omega_using [hd])
  obtain hp3 : arr s₃.mem S ((k + 7) / 8) 0 = p := by
    rw [arr, Outside.val32 osc (Or.inl (by omega_using [hZ, e0, e28])) (by omega)]; exact h.hP
  obtain hbD : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs X y < k → off Q i ≠ y) →
      Spec.Rsa.bytesAt s₃.mem Q n = Spec.Rsa.bytesAt s₀.mem Q n := fun Q n hq =>
    Domain.outside_bytesAt xout (by omega_using []) hq
  obtain eb : Derive.bnd s₃.mem D k L p = Derive.bnd s₀.mem D k L p := by
    unfold Derive.bnd
    by_cases hq : L = 3 * k
    · rw [ite_eq_left hq, ite_eq_left hq, hbD _ _ fun i hi => by
        rw [Domain.off_off']; exact h.hsepDX _ (by omega_using [hq, hi])]
    · rw [ite_eq_right hq, ite_eq_right hq]
  obtain cx3 := ctx_of_x (n := 8 * ctxWords ((k + 7) / 8)) xout h.hsepCX
  obtain e3 := h.env.keep k3 (by decide)
  obtain k34 := k3.trans k4
  rw [xb, hp3, eb] at a26
  rw [hp3] at p4
  refine ⟨⟨h.env.hs.congr k34.wr, a10, (k34.gpr .r29 (by decide)).trans h.env.h29,
    (k34.gpr .r11 (by decide)).trans h.env.h11, (k34.gpr .r31 (by decide)).trans h.env.h31, h.env.hw, h.env.hw', hZ⟩,
    (k34.gpr .r23 (by decide)).trans h.h23, (k34.gpr .r28 (by decide)).trans h.h28,
    fun d hd => by rw [Outside.word b4 (by omega_using [e0, hd]) (by omega_using [hd]), hw3 d hd],
    by rw [Domain.Body.bytesAt b4 hZ h.hsepX, xb], p4, k34,
    cx3.trans (outs_ctx (body_att b4) (attOut_fit e3) h.hc.sep), ?_⟩
  rw [a26, Domain.mask_beq_zero]
  congr 1
  cases hv : v
  · exact decide_eq_false fun hc => absurd (h.hv.mp hc) (by simp [hv])
  · exact decide_eq_true (h.hv.mpr hv)

end

/-! ## The two branches -/

/-- Before the output: `exOut_split`'s registers. -/
def X7p (q : CG) (t : State) : Prop :=
  t.gpr .r27 = off q.g.d.x.O 0 ∧ t.gpr .r10 = off q.c.S (slot q.c.w 0) ∧
    t.gpr .r29 = BitVec.ofNat 64 (8 * (q.c.w + 2)) ∧ t.gpr .r28 = BitVec.ofNat 64 q.c.k ∧ t.gpr .r23 = q.c.S ∧
    t.gpr .r11 = BitVec.ofNat 64 (2 * q.c.w)

/-- Before `exOutPre`: its registers. -/
def X6p (q : CG) (t : State) : Prop :=
  t.gpr .r10 = off q.c.S (slot q.c.w 0) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * (q.c.w + 2)) ∧
    t.gpr .r11 = BitVec.ofNat 64 (2 * q.c.w) ∧ t.gpr .r23 = q.c.S ∧ t.gpr .r28 = BitVec.ofNat 64 q.c.k

/-- After the comb's first block: the comb's registers. -/
def HP (q : CG) (t : State) : Prop :=
  t.gpr .r30 = q.C ∧ t.gpr .r27 = off q.g.d.x.X 0 ∧
    t.gpr .r21 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.bits) ∧ t.gpr .r3 = BitVec.ofNat 64 1 ∧ X6p q t

/-- Before the status's last block, which reaches x's mask. -/
def FinB (q : CG) (c : List Instr) (t : State) : Prop := t.gpr .r23 = q.c.S ∧ WP isa (.block c) t (K6 q.g)

def GD3 (q : CG) (t : State) : Prop := X7p q t ∧ WP isa PublicChecked.output t (FinB q Derive.status)

def GD2 (q : CG) (t : State) : Prop := X6p q t ∧ WP isa exOutPre t (GD3 q)

def GD1 (q : CG) (t : State) : Prop := HP q t ∧ WP isa combRest t (GD2 q)

def BD1 (q : CG) (t : State) : Prop := X7p q t ∧ WP isa PublicChecked.output t (FinB q [.li .r3 2])

theorem pins_X7p {Φ : CG → State → Prop} (h : ∀ q s, Φ q s → X7p q s) :
    Pins Φ [.r10, .r11, .r23, .r27, .r28, .r29] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨a27, a10, a29, a28, a23, a11⟩ := h _ _ h₁
  obtain ⟨b27, b10, b29, b28, b23, b11⟩ := h _ _ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a23, b23]
  · rw [a27, b27]
  · rw [a28, b28]
  · rw [a29, b29]

theorem pins_X6p {Φ : CG → State → Prop} (h : ∀ q s, Φ q s → X6p q s) :
    Pins Φ [.r10, .r11, .r23, .r28, .r29] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨a10, a29, a11, a23, a28⟩ := h _ _ h₁
  obtain ⟨b10, b29, b11, b23, b28⟩ := h _ _ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a23, b23]
  · rw [a28, b28]
  · rw [a29, b29]

theorem pins_GD1 : Pins GD1 [.r3, .r10, .r11, .r21, .r23, .r27, .r28, .r29, .r30] := by
  rintro q s₁ s₂ ⟨⟨a30, a27, a21, a3, a10, a29, a11, a23, a28⟩, -⟩
    ⟨⟨b30, b27, b21, b3, b10, b29, b11, b23, b28⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a3, b3]
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a21, b21]
  · rw [a23, b23]
  · rw [a27, b27]
  · rw [a28, b28]
  · rw [a29, b29]
  · rw [a30, b30]

theorem pins_FinB (c : List Instr) : Pins (fun q s => FinB q c s) [.r23] := by
  rintro q s₁ s₂ ⟨a, -⟩ ⟨b, -⟩ r hr
  rw [List.mem_singleton] at hr; subst hr; rw [a, b]

theorem pins_XIc {Φ : CG → State → Prop} (h : ∀ q s, Φ q s → XIc q s) : Pins Φ [.r23] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨a₀, ha, hxa⟩ := h _ _ h₁
  obtain ⟨b₀, hb, hxb⟩ := h _ _ h₂
  rw [List.mem_singleton] at hr; subst hr
  rw [(xf_of ha hxa).h23, (xf_of hb hxb).h23]

/-- x's mask's predicate, at the end of either branch. -/
theorem k6_of {q : CG} {s₀ u t : State} {rs : List Reg} (h₀ : BIq q s₀) (hx : XF q.c.S q.c.D q.g.d.x.X q.g.R q.C
    q.c.Z q.c.k q.c.p q.bits q.g.d.v s₀ u) (k : Keep rs u t) (h23 : .r23 ∉ rs) (h28 : .r28 ∉ rs)
    (hw : word t.mem q.c.S 64 = word u.mem q.c.S 64) {st : Nat} (h3 : t.gpr .r3 = BitVec.ofNat 64 st)
    (hst1 : 1 ≤ st) (hst : st < 4) : K6 q.g t := by
  have hZ := h₀.env.hZ
  obtain e28 := Domain.slot_eq ((q.c.k + 7) / 8) 28
  have hk := h₀.hk
  have hk' := h₀.hk'
  obtain kk := hx.keep.trans k
  exact ⟨⟨(k.gpr _ h23).trans hx.h23, (k.gpr _ h28).trans hx.h28⟩,
    by show word t.mem _ 64 = _; rw [hw, hx.hw 64 (by omega_using [])]; exact h₀.hX,
    by rw [kk.rd, kk.wr]; exact h₀.env.hs.ld (d := 64) (n := 8) (by omega_using [hZ, e28]), h₀.hx.congr kk.wr,
    ⟨show 1 ≤ q.c.k by omega_using [hk], show q.c.k < 2 ^ 32 by omega_using [hk']⟩, st, h3, hst1, hst⟩

/-- Out of range: zeros to `y`, the status 2. -/
theorem bad_ok {q : CG} {u : State} (h : XIc q u) (hv : q.g.d.v = false) :
    WP isa (.block [.load .d .r27 .r23 80]) u (BD1 q) := by
  obtain ⟨s₀, h₀, hx⟩ := h
  obtain xf := xf_of h₀ hx
  have hZ := h₀.env.hZ
  have hnw := h₀.env.hs.nowrap
  have hk := h₀.hk
  have hk' := h₀.hk'
  obtain e8 := Domain.slot_eq ((q.c.k + 7) / 8) 8
  obtain e28 := Domain.slot_eq ((q.c.k + 7) / 8) 28
  obtain hO : u.mem.readW (off q.c.S 80) 64 = off q.g.d.x.O 0 := (xf.hw 80 (by omega_using [])).trans h₀.hO
  refine WP.mono (WP.keep [.r27] (Q := fun t => t.gpr .r27 = off q.g.d.x.O 0 ∧ t.mem = u.mem) (by
      prun [xf.h23, xf.env.hs.ld (d := 80) (n := 8) (by omega_using [hZ, e28]), hO]) (by decide)) fun t ⟨⟨a27, mt⟩, kt⟩ => ?_
  obtain k10 := (kt.gpr .r10 (by decide)).trans xf.env.h10
  obtain k29 := (kt.gpr .r29 (by decide)).trans xf.env.h29
  obtain k28 := (kt.gpr .r28 (by decide)).trans xf.h28
  obtain k23 := (kt.gpr .r23 (by decide)).trans xf.h23
  obtain k11 := (kt.gpr .r11 (by decide)).trans xf.env.h11
  obtain ka := xf.keep.trans kt
  obtain h26 : t.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [kt.gpr .r26 (by decide)]
    have e := xf.r26
    rw [hv] at e
    exact (beq_iff_eq.mp e).trans rfl
  refine ⟨⟨a27, k10, k29, k28, k23, k11⟩, WP.mono (Pub.output_ok (b := false) (xf.env.hs.congr kt.wr)
    (h₀.ho.congr ka.wr) k10 k29 k28 a27 h26 (by omega_using [hk]) (by omega_using []) (by omega_using [hZ, e8, e28]) h₀.hsepO)
    fun t' ⟨⟨_, ot, _⟩, kt'⟩ => ⟨(kt'.gpr .r23 (by decide)).trans k23, WP.mono (li_ok t' 2 (by decide))
      fun t'' ⟨⟨u3, um⟩, ku⟩ => k6_of h₀ xf ((kt.trans kt').trans ku) (by decide) (by decide) ?_ u3
        (by decide) (by decide)⟩⟩
  rw [um]
  refine (Pub.Outside.word_apart (d := 64) ot h₀.hsepB (by omega_using []) (by omega_using [hZ, e28]) hnw).trans ?_
  show word t.mem _ 64 = word u.mem _ 64
  rw [mt]

/-- In range: the comb, then z or zeros to `y`, the status 1 or 3 (whatever x's range). -/
theorem good_ok {q : CG} {u : State} (h : XIc q u) :
    WP isa (.block headBlock) u (GD1 q) := by
  obtain ⟨s₀, h₀, hx⟩ := h
  obtain xf := xf_of h₀ hx
  have hZ := h₀.env.hZ
  have hnw := h₀.env.hs.nowrap
  have hk := h₀.hk
  have hk' := h₀.hk'
  obtain hw := h₀.env.hw; have hw' := h₀.env.hw'
  obtain e0 := Domain.slot_eq ((q.c.k + 7) / 8) 0
  obtain e28 := Domain.slot_eq ((q.c.k + 7) / 8) 28
  obtain hl4 : (Spec.Rsa.bytesAt u.mem q.g.d.x.X q.c.k).length = q.c.k := VG.Proof.Bignum.bytesAt_length _ _ _
  obtain xv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem q.g.d.x.X q.c.k) < 2 ^ q.bits := by
    rw [xf.xb, scalarC_value (by simp [Spec.Rsa.bytesAt]) h₀.hb1 h₀.hbk]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ci : CombIn u q.c.S q.C q.g.d.x.X q.c.Z ((q.c.k + 7) / 8) (Spec.Rsa.bytesAt u.mem q.g.d.x.X q.c.k) q.c.p
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (off q.c.D q.c.k) q.c.k)) q.bits := by
    refine ⟨xf.env, xf.h23, by rw [xf.h28, hl4], by rw [show hCtx = 0 from rfl]; exact (xf.hw 0 (by omega_using [])).trans h₀.hCw,
      h₀.hc.congr xf.keep.rd xf.keep.wr, fun a ha => ?_, ?_, xf.hp,
      by rw [show hRows = 24 from rfl]; exact (xf.hw 24 (by omega_using [])).trans h₀.hRw,
      by rw [show u.mem.readW (off q.c.S 64) 64 = word u.mem q.c.S 64 from rfl, xf.hw 64 (by omega_using [])]
         exact h₀.hX.trans (BitVec.add_zero _),
      fun n hn => (h₀.hx.congr xf.keep.wr).ld (d := n) (n := 1) (by omega_using [hl4, hn]), fun n hn => h₀.hsepX n (by omega_using [hl4, hn]),
      fun n hn => by simp [Spec.Rsa.bytesAt, off],
      ⟨h₀.hodd, by have := h₀.hp2; omega_using [this], (Rsa.FixedBaseComb.rows_small (show q.bits ≤ 8192 by have := h₀.hbk; omega_using [hk', this])).1,
        by rw [hl4]; omega_using [hk']⟩, h₀.hb1⟩
    · rw [← h₀.hents a ha]
      exact Outside.val32 xf.cx (Or.inl (by have := row_fits (w := (q.c.k + 7) / 8) ha; omega_using [this]))
        (by have := row_fits (w := (q.c.k + 7) / 8) ha; have := h₀.hc.hn; omega_arith)
    · rw [← h₀.hr2]
      exact Outside.val32 xf.cx (Or.inl (by have := row1_fits ((q.c.k + 7) / 8); omega_using [this]))
        (by have := row1_fits ((q.c.k + 7) / 8); have := h₀.hc.hn; omega_arith)
  obtain hP : 0 < q.c.p := by have := h₀.hp2; omega_using [this]
  obtain hc : WP isa comb u (GD2 q) := by
    refine WP.mono (comb_ok ci) fun t ⟨⟨z1, p1, o1, r10⟩, k1⟩ => ?_
    generalize hz : Spec.Rsa.powMod (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (off q.c.D q.c.k) q.c.k))
      (Rsa.FixedBaseComb.high q.bits (Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem q.g.d.x.X q.c.k)) 0) q.c.p = z at z1
    obtain hzP : z < q.c.p := by rw [← hz, VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hP
    obtain t29 := (k1.gpr .r29 (by decide)).trans xf.env.h29
    obtain t11 := (k1.gpr .r11 (by decide)).trans xf.env.h11
    obtain t23 := (k1.gpr .r23 (by decide)).trans xf.h23
    obtain t28 := (k1.gpr .r28 (by decide)).trans xf.h28
    refine ⟨⟨r10, t29, t11, t23, t28⟩, WP.mono (Domain.exOut_split (O := q.g.d.x.O) (k := q.c.k)
      (xf.env.hs.congr k1.wr) (h₀.ho.congr (xf.keep.trans k1).wr) r10 t29 t11 t23 t28 hw hw' hZ (by omega_using [hk]) (by omega_using [])
      (by rw [hdr_of_comb o1 (by decide)]; exact (xf.hw 80 (by omega_using [])).trans h₀.hO) h₀.hsepO
      (by rw [p1]; omega_using [hP]) (by rw [z1, p1]; exact hzP) (by rw [p1]; exact h₀.hpk))
      fun t₃ ⟨p3, hw3⟩ => ⟨p3, WP.mono hw3 fun t₄ ⟨⟨_, o2, m, bm, om⟩, k4⟩ => ⟨(k4.gpr .r23 (by decide)).trans t23,
        WP.mono (Derive.status_ok t₄ _ o2) fun t₅ ⟨⟨t3, tm⟩, k5⟩ =>
          k6_of h₀ xf ((k1.trans k4).trans k5) (by decide) (by decide) ?_ t3
            (by split <;> decide) (by split <;> decide)⟩⟩⟩
    rw [tm]
    refine (Pub.Outside.word_apart (d := 64) om h₀.hsepB (by omega_using []) (by omega_using [hZ, e28]) hnw).trans ?_
    show word m _ 64 = word u.mem _ 64
    rw [Outside.word bm (Or.inl (by omega_using [e0])) (by omega_using [])]
    exact hdr_of_comb o1 (by decide)
  rw [comb_eq] at hc
  refine WP.mono (WP.and (head_ok xf.env.hs (by omega_using [hZ, e28]) xf.h23 ci.hC ci.hX ci.hRw) (WP.seq_iff.mp hc))
    fun t ⟨⟨⟨a30, a27, a21, a3, _⟩, kt⟩, hw⟩ => ⟨⟨a30, a27.trans (BitVec.add_zero _).symm, a21, a3,
      (kt.gpr .r10 (by decide)).trans xf.env.h10, (kt.gpr .r29 (by decide)).trans xf.env.h29,
      (kt.gpr .r11 (by decide)).trans xf.env.h11, (kt.gpr .r23 (by decide)).trans xf.h23,
      (kt.gpr .r28 (by decide)).trans xf.h28⟩, hw⟩

/-- After x's range: out of range or in range, to x's mask. -/
theorem ite_rel : RelCT isa (Two XIc) (.ite (.zero .d .r26) Derive.dpBad good) (Two fun (q : CG) s => K6 q.g s) := by
  refine two_ite' (fun q : CG => !q.g.d.v) (fun q u ⟨s₀, h₀, hx⟩ => by rw [eval_zero, (xf_of h₀ hx).r26]) ?_ ?_
  · unfold Derive.dpBad
    exact RelCT.seq (R := Two BD1) (two_post (two_taint _ (pins_XIc fun _ _ h => h.1) (by taint_decide))
        fun _ _ ⟨h, hv⟩ => bad_ok h (by simpa using hv))
      (RelCT.seq (R := Two fun (q : CG) s => FinB q [.li .r3 2] s)
        (two_post (two_taint _ (pins_X7p fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2)
        (two_post (two_taint _ (pins_FinB [.li .r3 2]) (by taint_decide)) fun _ _ h => h.2))
  · unfold good exOut
    rw [comb_eq]
    exact RelCT.seq (R := Two GD2) (RelCT.seq (R := Two GD1)
        (two_post (two_taint _ (pins_XIc fun _ _ h => h.1) (by taint_decide)) fun _ _ ⟨h, _⟩ =>
          good_ok h)
        (two_post (two_taintR _ pins_GD1 (by taint_decide_rel)) fun _ _ h => h.2))
      (RelCT.seq (R := Two fun (q : CG) s => FinB q Derive.status s) (RelCT.seq (R := Two GD3)
          (two_post (two_taint _ (pins_X6p fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2)
          (two_post (two_taint _ (pins_X7p fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2))
        (two_post (two_taint _ (pins_FinB Derive.status) (by taint_decide)) fun _ _ h => h.2))

/-- x's mask. -/
theorem maskX_rel : RelCT isa (Two fun (q : CG) s => K6 q.g s) VG.Impl.Ffdh.PPC64LE.GenerateKey.maskX
    (Two fun (q : CG) s => CF q.c s) := by
  unfold VG.Impl.Ffdh.PPC64LE.GenerateKey.maskX
  exact RelCT.seq (R := Two fun (q : CG) s => K7 q.g s)
    (two_post (two_taint _ (fun q => pins_K6 q.g) (by taint_decide)) fun _ _ h => KM1 h)
    (two_post (two_taint _ (fun q => pins_K7 q.g) (by taint_decide)) fun _ _ h => KM2 h)

/-- The body. -/
theorem body_rel : RelCT isa (Two BIq) body (Two fun (q : CG) s => CF q.c s) := by
  unfold body
  exact RelCT.seq (R := Two PX) scalar_rel (RelCT.seq (R := Two fun (q : CG) s => K6 q.g s)
    (RelCT.seq (R := Two XIc) xRange_rel ite_rel) maskX_rel)

end VG.Proof.Ffdh.PPC64LE.Cached

end

end

/-! ### `Ffdh.PPC64LE.Cached.AttemptImplies`, which only this module used -/

section

/-!
# `vg_ffdh_generate_key_cached` on PPC64LE: the shared contract

`cgContract` states the shared contract on the registers and the stack
(`cg_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE

theorem cgStackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] :=
  rfl

theorem cg_pre {s : State} (h : (Proof.Ffdh.cachedGenerateKeyContract abi).pre s) : cgContract.pre s := by
  sig_pre [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argRegs, cgContract, cgStackArgs_five, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid,
    Spec.Ffdh.domainLenValid, List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil,
    List.filterMap_cons, List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append,
    List.nil_append, List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true,
    Bool.or_false, List.range, List.range.loop] at h
  sig_split h
  sig_reduce [cgContract, cgDom, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Ffdh.generationContextAt,
    List.range, List.range.loop]
  sig_and_intros
  sig_close
  all_goals first
    | with_reducible assumption
    | sig_disjoint_symm
    | omega
    | (sig_simp_only [Nat.mul_comm] at *
       first | with_reducible assumption | sig_disjoint_symm)
    | (simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.or_true, Bool.or_false,
        Bool.cond_true, Bool.cond_false, Sig.conj_cons, List.nil_append, List.cons_append] at *
       simp_all only [cgStack])

/-- The stack's bytes: `rand_len` 64, `scratch` `0x4000`, `scratch_len`
1056, `ctx` `0x100000` and `ctx_len` 275, at `0x9060`. -/
private def attemptBase (a : Addr) : Byte :=
  if a = 0x9060 then 0x40 else if a = 0x9069 then 0x40 else if a = 0x9070 then 0x20
  else if a = 0x9071 then 0x04 else if a = 0x907a then 0x10 else if a = 0x9080 then 0x13
  else if a = 0x9081 then 0x01 else CachedSat.domainMem a

/-- A state meeting the contract: the domain at `0x3000`, x at `0x1000`, `y`
at `0x1100`, `rand` at `0x7000`, the working space at `0x4000` and the
context at `0x100000`. -/
private def attemptState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1100 | .r6 => 64 | .r7 => 0x3000 | .r8 => 128 | .r9 => 64
    | .r10 => 0x7000 | _ => 0
  lr := 0
  sp := 0x9000
  mem := CachedSat.withContext attemptBase
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 64⟩, ⟨0x100000, 2200⟩, ⟨0x9060, 40⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x4000, 8448⟩]

private theorem attempt_arg (i : Nat) (hi : i < 5) :
    stackArg attemptState i = Mem.readW attemptBase (0x9000 + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 := by
  unfold stackArg stackArgAddr
  rw [show attemptState.sp = 0x9000 from rfl]
  refine CachedSat.readW_outside _ ?_
  have small : ∀ i < 5, ((0x9000 : BitVec 64) + BitVec.ofNat 64 (32 + 8 * (8 + i))).toNat + 64 / 8 ≤ 0x100000 := by
    decide
  exact small i hi

private theorem a0 : stackArg attemptState 0 = 64 := by rw [attempt_arg 0 (by decide)]; decide
private theorem a1 : stackArg attemptState 1 = 0x4000 := by rw [attempt_arg 1 (by decide)]; decide
private theorem a2 : stackArg attemptState 2 = 1056 := by rw [attempt_arg 2 (by decide)]; decide
private theorem a3 : stackArg attemptState 3 = 0x100000 := by rw [attempt_arg 3 (by decide)]; decide
private theorem a4 : stackArg attemptState 4 = 275 := by rw [attempt_arg 4 (by decide)]; decide

private theorem attempt_args : List.map (stackArg attemptState) (List.range 5) =
    [64, 0x4000, 1056, 0x100000, 275] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append,
    a0, a1, a2, a3, a4]

private theorem attempt_domain : Spec.Rsa.bytesAt attemptState.mem 0x3000 128 = CachedSat.domain := by
  rw [show attemptState.mem = CachedSat.withContext attemptBase from rfl, CachedSat.domain_unchanged]
  apply CachedSat.bytesAt_eq
  have : ∀ i < 128, attemptBase (0x3000 + BitVec.ofNat 64 i) = CachedSat.domainMem (0x3000 + BitVec.ofNat 64 i) := by
    decide
  exact this

theorem attempt_sat : ∃ s, (Proof.Ffdh.cachedGenerateKeyContract abi).pre s := by
  refine ⟨attemptState, ?_⟩
  sig_pre [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Ffdh.generationContextAt, abi, argRegs, attempt_args]
  simp only [a0, a1, a2, a3, a4]
  repeat' apply And.intro
  all_goals first
    | rfl
    | decide
    | (apply Region.disjoint_of_sep; decide)
    | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt attemptState.mem 0x3000 128) = true
       rw [attempt_domain]; exact CachedSat.domain_valid)
    | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt attemptState.mem 0x3000 128) =
          some (Spec.Rsa.wordsAt attemptState.mem 0x100000 275)
       rw [attempt_domain]; exact (CachedSat.canonical attemptBase).2)

theorem cg_post {s t : State} (h : cgContract.post s t) : (Proof.Ffdh.cachedGenerateKeyContract abi).post s t := by
  sig_post [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argRegs, cgStackArgs_five, List.getD_cons_succ, List.getD_cons_zero, List.append_eq]
  sig_reduce [cgContract, cgDom, cgA, cgScalar] at h
  exact h

theorem cg_pub {s₁ s₂ : State} (h : (Proof.Ffdh.cachedGenerateKeyContract abi).pub s₁ s₂) : cgContract.pub s₁ s₂ := by
  sig_pub [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argRegs, cgStackArgs_five, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  exact h

theorem cg_implies : cgContract.Implies (Proof.Ffdh.cachedGenerateKeyContract abi) where
  pre _ h := cg_pre h
  post _ _ _ h := cg_post h
  pub _ _ _ _ h := cg_pub h
  sat := attempt_sat

end VG.Proof.Ffdh.PPC64LE.Cached

end

end

/-!
# `vg_ffdh_generate_key_cached` on PPC64LE: constant time, and verified

The front loads the working space's and the context's addresses from the
stack and runs without a branch; p's load and check are as
`vg_ffdh_generate_key`'s, from `Base` alone (r9 holds `p_len`, not g's
address, here); then the body (`body_rel`) or the status 0, and the
registers' restore. Runs with the same public arguments and leakage have
the same public data (`cgOf_eq`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Ffdh.PPC64LE.GenerateKey (gcOf gxOf GD)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (two_ite' two_mono)

/-! ## The front -/

def T0 (q : CG) (s : State) : Prop := cgContract.pre s ∧ cgOf s = q

/-- After the front: `Base`, and p's load and check to come. -/
def A3 (q : CG) (s : State) : Prop := Base q.c s ∧ WP isa loadP s (A4 q)

/-- The front after the two loads. -/
abbrev frontRest : List Instr :=
  save .r11 ++ ctxHdr ++ ([.store .d .r3 .r23 64, .store .d .r4 .r23 72, .store .d .r5 .r23 80,
    .store .d .r10 .r23 88, .addi .r3 .r7 0, .addi .r4 .r8 0, .addi .r5 .r9 0] : List Instr) ++ setup

theorem front_eq : front = ([.addSp .r11 104, .load .d .r11 .r11 0] : List Instr) ++
    (([.addSp .r12 120, .load .d .r12 .r12 0] : List Instr) ++ frontRest) := by
  simp only [front, frontRest, List.append_assoc]

/-- After the working space's address. -/
def T1 (q : CG) (s : State) : Prop :=
  (∃ s₀, T0 q s₀ ∧ s.gpr .r11 = stackArg s₀ 1 ∧ s.mem = s₀.mem ∧ Keep [.r11] s₀ s) ∧
    WP isa (.block (([.addSp .r12 120, .load .d .r12 .r12 0] : List Instr) ++ frontRest)) s (A3 q)

/-- After the context's address. -/
def T2 (q : CG) (s : State) : Prop :=
  (s.gpr .r11 = q.c.S ∧ s.gpr .r12 = q.C) ∧ WP isa (.block frontRest) s (A3 q)

theorem pins_T0 : Pins T0 ([] : List Reg) := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem pins_T1 : Pins T1 ([] : List Reg) := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem pins_T2 : Pins T2 [.r11, .r12] := by
  rintro q s₁ s₂ ⟨⟨a11, a12⟩, -⟩ ⟨⟨b11, b12⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a11, b11]
  · rw [a12, b12]

theorem stackArg_rd {s : State} (h : cgContract.pre s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := by
  refine ⟨cgStack s, List.mem_append_left _ (by rw [h.2.1]; simp), ?_⟩
  rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
    simp only [stackArgAddr, Offset.add_add]; congr 2; omega_using []]
  exact Offset.contains_base _ (by have := h.1; omega_using [hi]) (by omega_using [hi])

theorem T0_T1 {q : CG} {s : State} (h : T0 q s) :
    WP isa (.block ([.addSp .r11 104, .load .d .r11 .r11 0] : List Instr)) s (T1 q) := by
  obtain ⟨hpre, rfl⟩ := h
  have hf := cg_toBI hpre
  rw [front_eq, WP.block_append_iff] at hf
  exact WP.mono (WP.and (loadS1_ok s (stackArg_rd hpre (by decide))) hf)
    fun t ⟨⟨⟨a11, m⟩, k⟩, hw⟩ => ⟨⟨s, ⟨hpre, rfl⟩, a11, m, k⟩, WP.mono hw fun _ h => h⟩

theorem T1_T2 {q : CG} {s : State} (h : T1 q s) :
    WP isa (.block ([.addSp .r12 120, .load .d .r12 .r12 0] : List Instr)) s (T2 q) := by
  obtain ⟨⟨s₀, ⟨hpre, rfl⟩, a11, m, k⟩, hw⟩ := h
  rw [WP.block_append_iff] at hw
  have hrd : InRegions (s.rd ++ s.wr) (stackArgAddr s 3) 8 := by
    rw [k.rd, k.wr, show stackArgAddr s 3 = stackArgAddr s₀ 3 by simp only [stackArgAddr, k.sp]]
    exact stackArg_rd hpre (by decide)
  exact WP.mono (WP.and (loadC_ok s hrd) hw) fun t ⟨⟨⟨a12, _⟩, kt⟩, hw'⟩ =>
    ⟨⟨(kt.gpr .r11 (by decide)).trans a11, a12.trans (show stackArg s 3 = stackArg s₀ 3 by simp only [stackArg, stackArgAddr, m, k.sp])⟩, hw'⟩

/-! ## p's load and check, from `Base` -/

/-- With `loadN`'s arguments. -/
def Y1 (c : CD) (s : State) : Prop := Base c s ∧ s.gpr .r12 = off c.D 0 ∧ s.gpr .r6 = BitVec.ofNat 64 c.k

/-- After `check1`. -/
def Y3 (c : CD) (s : State) : Prop :=
  Base c s ∧ arr s.mem c.S c.w 0 = c.p ∧ s.gpr .r6 = BitVec.ofNat 64 c.k ∧
    s.gpr .r15 = BitVec.ofNat 64 ((c.db.take c.k).getD 0 0).toNat ∧ s.gpr .r18 = 1 ∧
    (s.gpr .r0 = 0 ↔ ((c.db.take c.k).getD (c.k - 1) 0).toNat % 2 = 1)

theorem YA {c : CD} {s : State} (h : Base c s) : WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (Y1 c) := by
  refine WP.mono (WP.keep [.r6, .r12] (Q := fun t => t.gpr .r12 = off c.D 0 ∧ t.gpr .r6 = BitVec.ofNat 64 c.k ∧
    t.mem = s.mem) (by prun [h.r21, h.r28, BitVec.add_zero]) (by decide)) fun t ⟨⟨a12, a6, m⟩, k⟩ =>
      ⟨h.same k m, a12, a6⟩

theorem YL {c : CD} {s : State} (h : Y1 c s) :
    WP isa Precompute.loadN s fun t => Y1 c t ∧ arr t.mem c.S c.w 0 = c.p := by
  obtain ⟨hb, h12, h6⟩ := h
  have hwd : c.w = (c.k + 7) / 8 := rfl
  have hZ := hb.env.hZ
  have hk := hb.k64
  have hk' := hb.k1024
  have e28 := Domain.slot_eq c.w 28
  refine WP.mono (loadN_ok (dA := slot c.w 0) hb.env.hs hb.env.h10 h12 h6 hb.env.h11 (by omega_arith) (by omega_arith)
    (by omega_arith) (by rw [Domain.slot_eq]; omega_arith) (by rw [Domain.slot_eq] at hZ ⊢; omega_arith)
    (fun i hi => hb.rdD i (by rcases hb.hL with h | h <;> omega_arith))
    (fun i hi => hb.sepD i (by rcases hb.hL with h | h <;> omega_arith))) fun t ⟨hv, out, k⟩ => ?_
  have hm : Body c.S c.w s.mem t.mem := Body.of out (Nat.le_refl _) (by rw [Domain.slot_eq] at hZ ⊢; omega_arith)
  refine ⟨⟨hb.keep k hm, (k.gpr .r12 (by decide)).trans h12, (k.gpr .r6 (by decide)).trans h6⟩, ?_⟩
  rw [arr, hv, ← Proof.Ffdh.take_bytesAt _ _ (show c.k ≤ c.L by rcases hb.hL with h | h <;> omega_arith), hb.bD]

theorem YC1 {c : CD} {s : State} (h : Y1 c s ∧ arr s.mem c.S c.w 0 = c.p) :
    WP isa (.block Precompute.check1) s (Y3 c) := by
  obtain ⟨⟨hb, h12, h6⟩, hp⟩ := h
  have hl := hb.take_len
  have hk := hb.k64
  refine WP.mono (check1_ok (N := c.D) (nb := c.db.take c.k) h12 h6 hk hl
    (fun i hi => hb.rdD i (by have := hb.kL; omega_arith)) fun i hi => hb.take_byte hi)
    fun t ⟨⟨i0, i15, i18, im⟩, k⟩ => ⟨hb.same k im, by rw [arr, im]; exact hp,
      (k.gpr .r6 (by decide)).trans h6, by rw [i15, getD_of_lt' (by omega_arith)], i18,
      by rw [i0, getD_of_lt' (by omega_arith)]⟩

/-- With `loadN`'s arguments, and p's load and check to come. -/
def P1 (q : CG) (s : State) : Prop := Y1 q.c s ∧ WP isa (.seq Precompute.loadN Precompute.check) s (A4 q)

def P2 (q : CG) (s : State) : Prop := (Y1 q.c s ∧ arr s.mem q.c.S q.c.w 0 = q.c.p) ∧ WP isa Precompute.check s (A4 q)

def P3 (q : CG) (s : State) : Prop := Y3 q.c s ∧ WP isa Precompute.check2 s (A4 q)

theorem pins_A3 : Pins A3 baseRegs := fun _ _ _ h₁ h₂ => h₁.1.pins h₂.1

theorem pins_Y1 {Φ : CG → State → Prop} (h : ∀ q s, Φ q s → Y1 q.c s) :
    Pins Φ (baseRegs ++ ([.r12, .r6] : List Reg)) := by
  intro q s₁ s₂ h₁ h₂ r hr
  have h₁ := h _ _ h₁
  have h₂ := h _ _ h₂
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.pins h₂.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]

theorem pins_P3 : Pins P3 (baseRegs ++ ([.r6, .r15, .r18] : List Reg)) := by
  intro q s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.1.pins h₂.1.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.2.2.1, h₂.1.2.2.1]
    · rw [h₁.1.2.2.2.1, h₂.1.2.2.2.1]
    · rw [h₁.1.2.2.2.2.1, h₂.1.2.2.2.2.1]

theorem pins_A4 {Φ : CG → State → Prop} (h : ∀ q s, Φ q s → A4 q s) : Pins Φ [.r23] := by
  intro q s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr; subst hr
  rw [(h _ _ h₁).1.2, (h _ _ h₂).1.2]

theorem pins_CF : Pins (fun (q : CG) s => CF q.c s) [.r23] := by
  intro q s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr; subst hr
  exact h₁.trans h₂.symm

/-! ## Constant time -/

theorem cg_rel : RelCT isa (Two T0) Generate.code fun _ _ => True := by
  unfold Generate.code
  rw [front_eq]
  refine RelCT.seq (R := Two A3) (RelCT.block_append (RelCT.seq (R := Two T1)
      (two_post (two_taint _ pins_T0 (by taint_decide)) fun _ _ h => T0_T1 h)
      (RelCT.block_append (RelCT.seq (R := Two T2)
        (two_post (two_taint _ pins_T1 (by taint_decide)) fun _ _ h => T1_T2 h)
        (two_post (two_taint _ pins_T2 (by taint_decide)) fun _ _ h => h.2)))))
    (RelCT.seq (R := Two A4) ?_
      (RelCT.seq (R := Two fun (q : CG) s => CF q.c s) ?_ (two_taint _ pins_CF (by taint_decide))))
  · unfold loadP Precompute.check
    exact RelCT.seq (R := Two P1)
      (two_post (two_taint _ pins_A3 (by taint_decide)) fun _ _ h => Derive.wp_split (YA h.1) h.2)
      (RelCT.seq (R := Two P2) (two_post (two_taint _ (pins_Y1 fun _ _ h => h.1) (by taint_decide))
          fun _ _ h => Derive.wp_split (YL h.1) h.2)
        (RelCT.seq (R := Two P3) (two_post (two_taint _ (pins_Y1 fun _ _ h => h.1.1) (by taint_decide))
            fun _ _ h => Derive.wp_split (YC1 h.1) h.2)
          (two_post (two_taint _ pins_P3 (by taint_decide)) fun _ _ h => h.2)))
  · refine two_ite' (fun q : CG => Spec.Rsa.modulusValid q.c.p q.c.k) (fun q s h => by
        rw [eval_zero]; congr 1
        cases hv : Spec.Rsa.modulusValid q.c.p q.c.k
        · exact beq_false_of_ne fun e => by simpa [hv] using h.1.1.mp e
        · exact beq_iff_eq.mpr (h.1.1.mpr hv)) ?_ ?_
    · exact two_mono (fun q s ⟨h, hv⟩ => h.2 (h.1.1.mpr hv)) body_rel
    · exact two_post (two_taint _ (pins_A4 fun _ _ h => h.1) (by taint_decide)) fun _ _ ⟨h, _⟩ =>
        WP.mono (li_ok _ 0 (by decide)) fun t ⟨_, kt⟩ => (kt.gpr .r23 (by decide)).trans h.1.2

/-! ## The public data -/

/-- The attempt's scalar, as the code cuts it. -/
theorem cgScalar_eq {s : State} (h : cgContract.pre s) :
    cgScalar s = cgX (s.gpr .r9).toNat (Spec.Ffdh.generationScalarBits (cgA s)) s.mem (s.gpr .r10) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrl, -, hdv, -⟩ := h
  have hb := genBits_facts hdv
  unfold cgScalar
  rw [Spec.Ffdh.vettedScalarOfOctets, hrl, cgX, scalarC_value (VG.Proof.Bignum.bytesAt_length _ _ _) hb.1 hb.2]

/-- Runs with the same public arguments and leakage have the same public
data. -/
theorem cgOf_eq {s t : State} (hs : cgContract.pre s) (ht : cgContract.pre t) (h3 : s.gpr .r3 = t.gpr .r3)
    (h5 : s.gpr .r5 = t.gpr .r5) (h7 : s.gpr .r7 = t.gpr .r7) (h8 : s.gpr .r8 = t.gpr .r8)
    (h9 : s.gpr .r9 = t.gpr .r9) (h10 : s.gpr .r10 = t.gpr .r10) (a1 : stackArg s 1 = stackArg t 1)
    (a2 : stackArg s 2 = stackArg t 2) (a3 : stackArg s 3 = stackArg t 3) (hl : cgLeak s = cgLeak t) :
    cgOf s = cgOf t := by
  have hsc := cgScalar_eq hs
  have htc := cgScalar_eq ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, -⟩, hL, -⟩ := hs
  simp only [Spec.Ffdh.domainLenValid] at hL
  simp only [cgLeak] at hl
  obtain ⟨e1, e2⟩ := List.append_inj hl (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h8])
  have ed : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .r7) (s.gpr .r8).toNat := by
    have := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
    simp only [cgDom] at this
    rw [← h7, ← h8] at this; exact this
  have sl : ∀ o, o + (s.gpr .r9).toNat ≤ (s.gpr .r8).toNat →
      Spec.Rsa.bytesAt s.mem (s.gpr .r7 + BitVec.ofNat 64 o) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt t.mem (s.gpr .r7 + BitVec.ofNat 64 o) (s.gpr .r9).toNat := fun o ho => by
    rw [← VG.Proof.Dsa.bytesAt_slice s.mem _ ho, ← VG.Proof.Dsa.bytesAt_slice t.mem _ ho, ed]
  have hgx : gxOf s = gxOf t := by
    have e1 : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat =
        Spec.Rsa.bytesAt t.mem (t.gpr .r7) (t.gpr .r8).toNat := by rw [← h7, ← h8]; exact ed
    have e2 : Spec.Rsa.bytesAt s.mem (off (s.gpr .r7) (s.gpr .r9).toNat) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt t.mem (off (t.gpr .r7) (t.gpr .r9).toNat) (t.gpr .r9).toNat := by
      rw [← h7, ← h9]; exact sl _ (by omega_using [hL])
    unfold gxOf gcOf
    rw [e1, e2, h3, h5, h7, h8, h9, a1, a2]
  have hp : ∀ m : Mem, Spec.Rsa.os2ip ((Spec.Rsa.bytesAt m (s.gpr .r7) (s.gpr .r8).toNat).take (s.gpr .r9).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (s.gpr .r7) (s.gpr .r9).toNat) := fun m => by
    rw [Proof.Ffdh.take_bytesAt _ _ (by omega_using [hL])]
  have hbT : ∀ P, Derive.bnd t.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat P =
      Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat P := fun P =>
    Derive.bnd_congr fun hq => (sl _ (by omega_using [hq])).symm
  have hpT : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (s.gpr .r7) (s.gpr .r9).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := by rw [← hp, ← hp, ed]
  have hA : cgA t = cgA s := by
    show Spec.Ffdh.domainOf (t.gpr .r9).toNat (Spec.Rsa.bytesAt t.mem (t.gpr .r7) (t.gpr .r8).toNat) =
      Spec.Ffdh.domainOf (s.gpr .r9).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
    rw [← h7, ← h8, ← h9, ← ed]
  have e3 := (Derive.keyStatus_two _ _).symm.trans
    ((iff_of_eq (congrArg (· = 2) (List.cons.inj e2).1)).trans (Derive.keyStatus_two _ _))
  rw [hsc, htc, hA] at e3
  simp only [cgA, cgDom, ← h9, ← h10] at e3
  rw [Derive.privateValid_dom (by omega_using [hk]) (by omega_using [hL]), Derive.privateValid_dom (by omega_using [hk]) (by omega_using [hL])] at e3
  have hv := Derive.bool_eq_of_false_iff e3
  have hgp : (gcOf t).p = (gcOf s).p := congrArg (fun x : XD => x.c.p) hgx.symm
  have ep : (gcOf s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := hp s.mem
  simp only [cgOf, CG.mk.injEq, GD.mk.injEq, Derive.DD.mk.injEq]
  refine ⟨⟨⟨hgx, ?_, ?_⟩, h10⟩, a3, by rw [hA]⟩
  · rw [← h7, ← h8, ← h9, hgp, hbT]
  · rw [hA, ← h7, ← h8, ← h9, ← h10, hgp, hbT, ep]
    simp only [cgA, cgDom] at hv ⊢
    exact hv

theorem cg_ct : ConstantTime isa cgContract.pre cgContract.pub Generate.code :=
  RelCT.constantTime (cg_rel.mono (fun s _ ⟨hs, ht, hsp, hl, h3, _, h5, _, h7, h8, h9, h10, _, a1, a2, a3, _⟩ =>
    ⟨cgOf s, ⟨hs, rfl⟩, ⟨ht, (cgOf_eq hs ht h3 h5 h7 h8 h9 h10 a1 a2 a3 hl).symm⟩, hsp⟩) fun _ _ h => h)

/-- `vg_ffdh_generate_key_cached`. -/
theorem cg_verified : Verified target Generate.code (Proof.Ffdh.cachedGenerateKeyContract abi) :=
  Verified.of_correct cg_correct cg_ct cg_implies

end VG.Proof.Ffdh.PPC64LE.Cached

end

end

/-! # The verified cached key search (PPC64LE)

For any cached attempt that uses no stack of its own (`key_verified_of`),
and for `vg_ffdh_generate_key_cached` (`cachedAttempt`, `search_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE

theorem key_verified_of (a : Attempt) :
    Verified target (Impl.Ffdh.PPC64LE.Cached.Search.code a.call)
      (Spec.Ffdh.cachedKeySearchContract abi stackUse) :=
  Verified.of_correct (key_correct a) (key_constantTime a) key_implies

/-- `vg_ffdh_generate_key_cached`, which has no frames. -/
def cachedAttempt : Attempt where
  name := "vg_ffdh_generate_key_cached"
  code := Impl.Ffdh.PPC64LE.Cached.Generate.code
  stack := by decide +kernel
  correct := Cached.cg_correct
  ct := Cached.cg_ct

/-- The cached key search calling it. -/
abbrev keyCode : Prog isa := Impl.Ffdh.PPC64LE.Cached.Search.code cachedAttempt.call

theorem search_verified : Verified target keyCode (Spec.Ffdh.cachedKeySearchContract abi stackUse) :=
  key_verified_of cachedAttempt

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof
