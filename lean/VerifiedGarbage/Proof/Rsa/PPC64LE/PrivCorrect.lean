module

import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivResult
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPubCall
public import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCmp
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Rsa.Contract

/-! ### `Rsa.PPC64LE.PrivRestore`, which only this module used -/

section

/-!
# `vg_rsa_private_checked` on PPC64LE: the restores

`Late` through the blocks after the public operation (`Late.keep`,
`Late.release`), and the restores of our caller's registers and return
address (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

theorem Late.keep {s t u : State} (L : Late s t) {rs : List Reg} (k : Keep rs t u) (hm : u.mem = t.mem)
    (hrs : ∀ r ∈ preserved, r ∉ rs := by decide) : Late s u :=
  ⟨k.sp.trans L.sp, k.rd.trans L.rd, k.wr.trans L.wr, (k.gpr _ (hrs _ (by decide))).trans L.r24,
    (k.gpr _ (hrs _ (by decide))).trans L.r25, (k.gpr _ (hrs _ (by decide))).trans L.r26,
    (k.gpr _ (hrs _ (by decide))).trans L.r27, (k.gpr _ (hrs _ (by decide))).trans L.r28,
    (k.gpr _ (hrs _ (by decide))).trans L.r29,
    fun r hr => (k.gpr r (hrs r (by revert r; decide))).trans (L.hi r hr), hm ▸ L.mem, hm ▸ L.sv, hm ▸ L.ls⟩

/-- The frame's words are apart from `out` and `m`. -/
theorem slot_apart {s : State} (h : PreP pc s) {d : Nat} (hd : d + 8 ≤ oM) {r : Region} (hr : r ∈ [oR s, mR s]) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ko.sub_left (frame_sub s (by unfold oM frameBytes at *; omega_using [hd]))
  · exact Offset.disjoint _ (.inl hd) (by unfold oM at hd; omega_using [hd]) (by have := h.k2; unfold oM; omega_using [this])

theorem Late.release {s t u : State} (h : PreP pc s) (L : Late s t) (k : Keep [.r0, .r6, .r7, .r8] t u)
    (hf : Frame [oR s, mR s] t.mem u.mem) : Late s u := by
  have mk : Region.Sub (mR s) (kR s) := frame_sub s (by have := h.k2; unfold oM frameBytes; omega_using [this])
  refine ⟨k.sp.trans L.sp, k.rd.trans L.rd, k.wr.trans L.wr, (k.gpr _ (by decide)).trans L.r24,
    (k.gpr _ (by decide)).trans L.r25, (k.gpr _ (by decide)).trans L.r26, (k.gpr _ (by decide)).trans L.r27,
    (k.gpr _ (by decide)).trans L.r28, (k.gpr _ (by decide)).trans L.r29,
    fun r hr => (k.gpr r (by revert r; decide)).trans (L.hi r hr), L.mem.trans (hf.sub fun r hr => ?_),
    L.sv.frame hf fun p hp r hr => slot_apart h (by have := saved_offs p hp; unfold oSave oM at *; omega_using [this]) hr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., mk⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => slot_apart h (by decide) hr) (by decide)]; exact L.ls

/-- The restores. -/
theorem restore_ok {s w : State} (L : Late s w) :
    WP isa (.block restore) w fun v =>
      (∀ r ∈ preserved, v.gpr r = s.gpr r) ∧ v.lr = s.lr ∧ v.sp = fb s ∧ v.mem = w.mem ∧ v.gpr .r3 = w.gpr .r3 := by
  have iLr : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 oLr) 8 := by
    rw [L.wr]; exact in_fr' s _ _ (by decide) (by decide)
  have c1 : oLr < 2 ^ 15 := by decide
  have c2 : oLr % 4 = 0 := by decide
  rw [restore_eq]
  refine WP.block_append_iff.mpr (WP.mono (Q := fun v => v = { ((w.write .r12 w.sp).write .r0
      (w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64)) with lr := w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 })
    ?_ fun v e => ?_)
  · prun [exec_addSp0, L.sp, iLr, c1, c2, exec_mtlr]
  · subst e
    refine WP.mono (Spill.restore_wp (b := .r12) (B := fb s) (by decide) (by simp [State.write, L.sp])
      saved_ho (by decide) (fun p hp => by
        have := saved_offs p hp
        show InRegions (w.rd ++ w.wr) _ 8
        rw [L.wr]; exact in_fr' s _ _ (by unfold oSave at this; omega_using [this]) (by unfold oSave at this; unfold frameBytes; omega_using [this]))
      L.sv) fun v R => ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · rcases preserved_split hr with hs | hs
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
        exact R.gpr p hp
      · have : r ∉ saved.map Prod.fst := by revert r; decide
        rw [R.other r this]
        have h12 : r ≠ .r12 := by revert r; decide
        have h0 : r ≠ .r0 := by revert r; decide
        simp only [State.write, h12, h0, ite_false]
        exact L.hi r hs
    · rw [R.lr]; exact L.ls
    · rw [R.sp]; exact L.sp
    · rw [R.mem]; rfl
    · rw [R.other _ (by decide)]; simp [State.write]

end VG.Proof.Rsa.PPC64LE.Priv
end

end

/-! ### `Rsa.PPC64LE.PrivFinal`, which only this module used -/

section

/-!
# `vg_rsa_private_checked` on PPC64LE: the outcome

The outcome from what the calls returned and wrote (`final_ok`): the check's
logic on every target (`Proof.Rsa.check_logic`, `Proof.Rsa.outcome_eq`),
without the status of `vg_rsa_public_precompute`, which this check does not
read: `n`'s values are invalid only when `n` is, and then so is the CRT's
result.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.Proof.Rsa

theorem final_ok {m m' : Mem} {O M : Addr} {k : Nat} {cs es acc : BitVec 64}
    {nB eB xB pB qB dPB dQB qInvB : List Byte} (hn : nB.length = k) (hx : xB.length = k)
    (hcrt : Spec.Rsa.written m M k (cs.setWidth 32) (Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB))
    (hpub : ∀ ws, Spec.Rsa.publicPrecompute nB = some ws →
      Spec.Rsa.written m O k (es.setWidth 32) (Spec.Rsa.publicOpChecked nB eB (Spec.Rsa.bytesAt m M k)))
    (heq : acc = 0#64 ↔ Spec.Rsa.bytesAt m O k = xB)
    (hout : Spec.Rsa.bytesAt m' O k =
      if cs &&& es &&& 1 = 1 ∧ decide (acc = 0#64) = true then Spec.Rsa.bytesAt m M k else List.replicate k 0) :
    Spec.Rsa.writtenOutcome m' O k ((result (cs &&& es &&& 1) (decide (acc = 0#64))).setWidth 32)
      (Spec.Rsa.privateChecked nB eB xB pB qB dPB dQB qInvB) := by
  let r₃ : BitVec 64 := if (Spec.Rsa.publicPrecompute nB).isSome then 1 else 0
  have hv : cs &&& es &&& 1 = gOf es cs r₃ := by
    by_cases hp : (Spec.Rsa.publicPrecompute nB).isSome
    · simp only [gOf, r₃, hp, ↓reduceIte]
      rw [BitVec.and_assoc (es &&& cs) 1 1, BitVec.and_self, BitVec.and_comm cs es]
    · have hm : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length = false := by
        rw [← precompute_isSome]; simpa using hp
      have hc : Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB = none := by
        simp only [Spec.Rsa.privateCrt, hm]; rfl
      rw [hc] at hcrt
      have h1 : cs &&& 1 = 0 := by
        rcases gOf_cases cs cs 1 with h | h <;> simp only [gOf] at h
        all_goals
          have := and1_of_setWidth_zero hcrt.1
          have e : cs &&& cs &&& 1 &&& 1 = cs &&& 1 := by
            rw [BitVec.and_self, BitVec.and_assoc, BitVec.and_self]
          rw [e] at h
          first | exact h | exact absurd h this
      simp only [gOf, r₃, hp, Bool.false_eq_true, ↓reduceIte]
      rw [show cs &&& es &&& 1 = (cs &&& 1) &&& es by ac_rfl, h1]
      rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.zero_and, BitVec.and_zero, BitVec.zero_and]
  have h3 : match Spec.Rsa.publicPrecompute nB with
      | some _ => r₃.setWidth 32 = 1
      | none => r₃.setWidth 32 = 0 := by
    cases hpc : Spec.Rsa.publicPrecompute nB <;> simp [r₃, hpc]
  have h2 : (Spec.Rsa.publicPrecompute nB).isSome = true →
      match Spec.Rsa.publicOpChecked nB eB (Spec.Rsa.bytesAt m M k) with
      | some y => es.setWidth 32 = 1 ∧ Spec.Rsa.bytesAt m O k = y
      | none => es.setWidth 32 = 0 := by
    intro hs
    obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp hs
    have := hpub ws hws
    cases hpo : Spec.Rsa.publicOpChecked nB eB (Spec.Rsa.bytesAt m M k) <;>
      simp only [hpo, Spec.Rsa.written] at this ⊢
    · exact this.1
    · exact this
  have hL := check_logic (r₁ := cs) (xB := xB) h3 h2
  have hd : decide (acc = 0#64) = decide (Spec.Rsa.bytesAt m O k = xB) := decide_eq_decide.mpr heq
  refine outcome_eq hn hx hcrt (by rw [hv, hd]; exact hL.1) ?_
  have hc : (gOf es cs r₃ = 1 ∧ decide (Spec.Rsa.bytesAt m O k = xB) = true) ↔
      released cs nB eB xB (Spec.Rsa.bytesAt m M k) := by
    rw [decide_eq_true_eq]; exact hL.2
  rw [hout, hv, hd]
  by_cases hr : released cs nB eB xB (Spec.Rsa.bytesAt m M k)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hc.mpr hr)), ite_eq_left_of_eq_true _ _ (eq_true hr)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hr (hc.mp h)), ite_eq_right_of_eq_false _ _ (eq_false hr)]

end VG.Proof.Rsa.PPC64LE.Priv

end

end


/-!
# `vg_rsa_private_checked` on PPC64LE: correctness

The blocks and calls in order (`code_correct`), from the frame's push to its
pop, to the outcome (`final_ok`), on the registers and the stack (`fnPost`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenOutcome s'.mem (s.gpr .r3) (s.gpr .r6).toNat ((s'.gpr .r3).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

theorem freed_sp (b : Nat) (s : State) : (freed b s).sp = s.sp + BitVec.ofNat 64 b := rfl
theorem freed_lr (b : Nat) (s : State) : (freed b s).lr = s.lr := rfl
theorem freed_gpr (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl
theorem freed_mem (b : Nat) (s : State) : (freed b s).mem = s.mem := rfl

/-- The CRT's result in the frame, from the state after the setup. -/
def CrtOk (pc : Bool) (s : State) : Prop :=
  ∀ t (Q : State → Prop), AtCrt s t → (∀ u, Mid s u → crtOut s u → Q u) → WP isa (crtStep pc) t Q

/-- `n`'s values put in the frame, from the state after `vg_rsa_private_crt`. -/
def StepOk (pc : Bool) (s : State) : Prop :=
  ∀ t (c : Prog isa) (Q : State → Prop), Mid s t → crtOut s t → (∀ u, AtPub pc s u → WP isa c u Q) →
    WP isa (.seq (preStep pc) c) t Q

/-- `n`'s values in the frame are its precomputed values, if they are valid. -/
abbrev PreValOk (pc : Bool) (s : State) : Prop :=
  ∀ ws, Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) = some ws →
    preVal pc s = ws

theorem codeG_correct {pc : Bool} (s : State) (h : PreP pc s) (hcrt : CrtOk pc s) (hstep : StepOk pc s) :
    WP isa (.frame (.alloc frameBytes) (bodyG pc) (.free frameBytes)) s fun t =>
      abiPreserved s t ∧ (PreValOk pc s → fnPost s t) := by
  have hk := h.k2
  refine WP.alloc ⟨by decide, by decide, by decide⟩ h.sp1 ?_
  unfold bodyG
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (hcrt t₁ _ A fun t₂ M C => ?_)
  refine hstep t₂ _ _ M C fun t₄ Q4 => ?_
  refine WP.seq (WP.mono (pubArgs_ok h Q4) fun t₅ R => ?_)
  refine WP.seq (pubCall_ok h R fun t₆ C6 => ?_)
  refine WP.seq (WP.mono (cmpArgs_ok h C6) fun t₇ L => ?_)
  refine WP.seq (WP.mono (compare_ok h L) fun t₈ ⟨a8, m8, k8⟩ => ?_)
  have L8 : Late s t₈ := L.toLate.keep k8 m8
  have iSt : InRegions (t₈.rd ++ t₈.wr) (fb s + BitVec.ofNat 64 oSt) 8 := by
    rw [L8.wr]; exact in_fr' s _ _ (by decide) (by decide)
  have iEs : InRegions (t₈.rd ++ t₈.wr) (fb s + BitVec.ofNat 64 oEs) 8 := by
    rw [L8.wr]; exact in_fr' s _ _ (by decide) (by decide)
  refine WP.seq (WP.mono (result_ok (cs := t₇.mem.readW (fb s + BitVec.ofNat 64 oSt) 64)
    (es := t₇.mem.readW (fb s + BitVec.ofNat 64 oEs) 64) L8.sp iSt iEs (by rw [m8]) (by rw [m8]) a8 (cmpAcc_lt _ _ _ _) L8.r24 L8.r26)
    fun t₉ ⟨⟨r3, r9, r6, r7, r8, m9⟩, k9⟩ => ?_)
  have L9 : Late s t₉ := L8.keep k9 m9
  refine WP.seq (WP.mono (release_ok h L9 (fun b => Proof.Rsa.low_and_mask b _ _) r6 r7 r8 r9)
    fun t₁₀ ⟨hout, f10, k10⟩ => ?_)
  have L10 := L9.release h k10 f10
  refine WP.mono (restore_ok L10) fun v ⟨vp, vl, vs, vm, v3⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun hv => ?_⟩
  · rw [freed_gpr]; exact vp r hr
  · rw [freed_sp, vs]; exact BitVec.sub_add_cancel _ _
  · rw [freed_lr]; exact vl
  · unfold fnPost
    rw [freed_mem, freed_gpr, vm, v3, k10.gpr .r3 (by decide), r3]
    have m97 : t₉.mem = t₇.mem := m9.trans m8
    rw [m97] at hout
    have hx : Spec.Rsa.bytesAt t₇.mem (s.gpr .r9) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat :=
      bytes_of_frame L.mem (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have ei : (⟨s.gpr .r9, (s.gpr .r6).toNat⟩ : Region) = iR s := by simp only [iR, h.h10]
        rw [ei]
        rcases hr with rfl | rfl | rfl
        · exact h.ki.symm
        · exact h.oi.symm
        · exact h.is) (by have := h.wi; rw [h.h10] at this; omega_using [])
    refine final_ok (Proof.Rsa.bytesAt_length' _ _ _) (Proof.Rsa.bytesAt_length' _ _ _) L.crt (fun ws hw => L.pub ws hw (hv ws hw)) ?_ hout
    rw [cmpAcc_eq_zero, ← hx, Proof.Rsa.bytesAt_eq_iff]

theorem step_false (s : State) (h : PreP false s) : StepOk false s := fun _ _ _ M C hc =>
  WP.seq (WP.seq (WP.mono (preArgs_ok h M C) fun _ P => preCall_ok h P hc))

theorem code_correct (s : State) (hpre : (Proof.Rsa.privateCheckedContract abi frameBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  have h := preP_of hpre
  exact WP.mono (codeG_correct s h (fun _ _ A hQ => crtCall_ok h A hQ) (step_false s h)) fun t ⟨ha, hf⟩ =>
    ⟨ha, hf fun ws hw => by simp only [preVal, Bool.false_eq_true, ↓reduceIte, hw, Option.getD_some]⟩

end VG.Proof.Rsa.PPC64LE.Priv
