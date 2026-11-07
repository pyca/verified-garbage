module

-- separate module: its proofs build in parallel with `RndCorrect`'s, which `RndVerified` also imports

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndReject
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndTaint
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE: constant time

Two runs from entry states that agree with an anchor `a` on the public data
(`PR`) read the same octets of the tape and keep as many of them: the scan
reads `scanLen` octets of `a`'s tape in both (`N`), each read octet is zero in
one run exactly when it is in the other, and so is each count of kept octets
(`Proof/RsaPkcs1Enc/RandomCT.lean`). So the branch on each octet, the index
of each store and the end of the loop are the same in both runs; the taint
analysis checks the rest (`RndTaint.lean`), with the registers holding
public data, which correctness fixes, public; the call is constant time by
its contract, whose public data both runs share.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Random VG.Proof.RsaPkcs1Sig.PPC64LE

/-- The trace of drawing `PS`. -/
abbrev trace (s : State) : List Nat := (Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)).trace

/-- The public data, by name: `s`'s is the anchor `a`'s. -/
def pub (a s : State) : Prop :=
  a.sp = s.sp ∧ (∀ r ∈ argRegs, a.gpr r = s.gpr r) ∧ (∀ j < 7, stackArg a j = stackArg s j) ∧
    nB a = nB s ∧ eB a = eB s ∧ preW a = preW s ∧ trace a = trace s

theorem pub_refl (s : State) : pub s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- An entry state meeting the precondition with the anchor's public data. -/
def PR (a s : State) : Prop := (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre s ∧ pub a s

theorem PR.pre {a s : State} (h : PR a s) : RPre s := pre_of h.1

theorem PR.spEq {a s : State} (h : PR a s) : s.sp = a.sp := h.2.1.symm

theorem PR.gprEq {a s : State} (h : PR a s) {r : Reg} (hr : r ∈ argRegs := by decide) : s.gpr r = a.gpr r :=
  (h.2.2.1 r hr).symm

theorem PR.argEq {a s : State} (h : PR a s) {j : Nat} (hj : j < 7 := by decide) : stackArg s j = stackArg a j :=
  (h.2.2.2.1 j hj).symm

theorem PR.fbEq {a s : State} (h : PR a s) : fb s = fb a := by simp only [fb, h.spEq]

theorem PR.psEq {a s : State} (h : PR a s) : psLen s = psLen a := by
  unfold psLen kOf; rw [h.gprEq (r := .r7), h.argEq (j := 0)]

theorem PR.rlEq {a s : State} (h : PR a s) : rl s = rl a := by simp only [rl, h.argEq (j := 2)]

theorem PR.traceEq {a s : State} (h : PR a s) :
    (Spec.RsaPkcs1Enc.padSearch (psLen a) (randB s)).trace =
      (Spec.RsaPkcs1Enc.padSearch (psLen a) (randB a)).trace := by
  have := h.2.2.2.2.2.2.2
  simp only [trace, h.psEq] at this
  exact this.symm

/-- The octets the scan reads, the anchor's. -/
abbrev N (a : State) : Nat := VG.Proof.RsaPkcs1Enc.scanLen (psLen a) (randB a)

theorem PR.scanEq {a s : State} (h : PR a s) :
    VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) = N a := by
  rw [h.psEq]; exact VG.Proof.RsaPkcs1Enc.scanLen_eq h.traceEq

theorem PR.keptEq {a s : State} (h : PR a s) {j : Nat} (hj : j ≤ N a) :
    (kept s j).length = (kept a j).length := by
  have := VG.Proof.RsaPkcs1Enc.nz_take_length_eq h.traceEq j (by rw [← h.psEq, h.scanEq]; exact hj)
  exact this

theorem PR.zeroIff {a s : State} (h : PR a s) {j : Nat} (hj : j < N a) :
    (randB s).getD j 0 = 0 ↔ (randB a).getD j 0 = 0 :=
  VG.Proof.RsaPkcs1Enc.zero_iff h.traceEq (by rw [← h.psEq, h.scanEq]; exact hj)

theorem PR.nLe {a s : State} (h : PR a s) : N a ≤ rl s := by
  have := VG.Proof.RsaPkcs1Enc.scanLen_le (psLen s) (randB s)
  rw [randB_length, h.scanEq] at this; exact this

/-! ## Loops of the same number of iterations -/

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨g a, h _ _ h₁, h _ _ h₂⟩) fun _ _ h => h

/-- A loop of `N a` iterations, its `j`-th from a state satisfying `Φ a j`,
whose condition after iteration `j` is whether `j + 1 < N a`. -/
theorem two_loop {α : Type} {Φ : α → Nat → State → Prop} {Ψ : α → State → Prop} (N : α → Nat)
    {body : Prog isa} {cond : isa.Cond}
    (hct : RelCT isa (Two fun (p : α × Nat) s => p.2 < N p.1 ∧ Φ p.1 p.2 s) body fun _ _ => True)
    (hw : ∀ a j s, j < N a → Φ a j s → WP isa body s fun s' =>
      isa.eval cond s' = some (decide (j + 1 < N a)) ∧ (j + 1 < N a → Φ a (j + 1) s') ∧
      (j + 1 = N a → Ψ a s')) :
    RelCT isa (Two fun a s => 0 < N a ∧ Φ a 0 s) (.loop body cond) (Two Ψ) := by
  have key := RelCT.loop (M := isa) (body := body) (c := cond) (Q := Two Ψ)
    (fun n s₁ s₂ => ∃ a j, n = N a - j ∧ j < N a ∧ Φ a j s₁ ∧ Φ a j s₂) (fun n => by
      have hp := two_post (Φ := fun (p : α × Nat) s => p.2 < N p.1 ∧ n = N p.1 - p.2 ∧ Φ p.1 p.2 s)
        (Ψ := fun p s' => p.2 < N p.1 ∧ n = N p.1 - p.2 ∧ isa.eval cond s' = some (decide (p.2 + 1 < N p.1)) ∧
          (p.2 + 1 < N p.1 → Φ p.1 (p.2 + 1) s') ∧ (p.2 + 1 = N p.1 → Ψ p.1 s'))
        (two_map id (fun p s h => ⟨h.1, h.2.2⟩) hct)
        fun p s h => WP.mono (hw p.1 p.2 s h.1 h.2.2) fun s' h' => ⟨h.1, h.2.1, h'⟩
      refine hp.mono (fun s₁ s₂ ⟨a, j, hn, hj, h₁, h₂⟩ => ⟨(a, j), ⟨hj, hn, h₁⟩, hj, hn, h₂⟩) ?_
      rintro s₁ s₂ ⟨⟨a, j⟩, ⟨hj, hn, e₁, f₁, g₁⟩, ⟨-, -, e₂, f₂, g₂⟩⟩
      refine ⟨by rw [e₁, e₂], fun h => ?_, fun h => ?_⟩
      · have : ¬ j + 1 < N a := by rw [e₁] at h; simpa using h
        have hjN : j + 1 = N a := by simp only at hj this; omega
        exact ⟨a, g₁ hjN, g₂ hjN⟩
      · have hlt : j + 1 < N a := by rw [e₁] at h; simpa using h
        exact ⟨N a - (j + 1), by simp only at hn; omega, a, j + 1, rfl, hlt, f₁ hlt, f₂ hlt⟩)
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨a, ⟨h0, h₁⟩, ⟨-, h₂⟩⟩ := hp
  exact key (N a - 0) _ _ _ _ _ _ ⟨a, 0, rfl, h0, h₁, h₂⟩ e₁ e₂

/-! ## The scan -/

/-- Before octet `j` of the scan. -/
def LoopPt (p : State × Nat) (u : State) : Prop :=
  ∃ s M, PR p.1 s ∧ Mm s M ∧ At s M p.2 u ∧ p.2 < rl s ∧ (kept s p.2).length < psLen s ∧ p.2 < N p.1

/-- After the load of octet `j`. -/
def LoadPtA (p : State × Nat) (v : State) : Prop :=
  ∃ s M, PR p.1 s ∧ Mm s M ∧ LoadPt s M p.2 v ∧ p.2 < rl s ∧ (kept s p.2).length < psLen s ∧ p.2 < N p.1

/-- After octet `j`. -/
def NextPt (p : State × Nat) (w : State) : Prop :=
  ∃ s M, PR p.1 s ∧ Mm s M ∧ At s M (p.2 + 1) w ∧ p.2 < N p.1

theorem load_two : RelCT isa (Two LoopPt) (.block load) (Two LoadPtA) := by
  refine two_post (load_taint fun p u₁ u₂ ⟨s₁, M₁, S₁, _, I₁, _⟩ ⟨s₂, M₂, S₂, _, I₂, _⟩ =>
    ⟨by rw [I₁.sp, I₂.sp, S₁.fbEq, S₂.fbEq], fun r hr => ?_⟩) fun p u ⟨s, M, S, hM, I, hi, hc, hN⟩ =>
      WP.mono (load_ok S.pre hM I hi) fun v h => ⟨s, M, S, hM, h, hi, hc, hN⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [I₁.r3, I₂.r3, S₁.argEq, S₂.argEq]
  · rw [I₁.r4, I₂.r4]

theorem LoadPt.r0 {s : State} {M : Mem} {j : Nat} {v : State} (h : LoadPt s M j v) :
    isa.eval (.nonzero .d .r0) v = some (!decide ((randB s).getD j 0 = 0)) := by
  obtain ⟨u, _, _, h0, _⟩ := h
  rw [eval_nonzero, h0, byte_ne]

theorem branch_two : RelCT isa (Two LoadPtA) (.ite (.nonzero .d .r0) (.block keep) (.block [])) (Two NextPt) := by
  have pins : ∀ p v₁ v₂, LoadPtA p v₁ → LoadPtA p v₂ →
      v₁.sp = v₂.sp ∧ ∀ r ∈ [Reg.r5, .r7], v₁.gpr r = v₂.gpr r := by
    rintro p v₁ v₂ ⟨s₁, M₁, S₁, _, ⟨u₁, I₁, o₁, _⟩, _, _, hN⟩ ⟨s₂, M₂, S₂, _, ⟨u₂, I₂, o₂, _⟩, _, _, _⟩
    refine ⟨by rw [o₁.sp, o₂.sp, I₁.sp, I₂.sp, S₁.fbEq, S₂.fbEq], fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [o₁.get .r5, o₂.get .r5, I₁.r5, I₂.r5, S₁.keptEq (Nat.le_of_lt hN), S₂.keptEq (Nat.le_of_lt hN)]
    · rw [o₁.get .r7, o₂.get .r7, I₁.r7, I₂.r7]; show fb s₁ + _ = fb s₂ + _; rw [S₁.fbEq, S₂.fbEq]
  refine two_post (two_ite (fun p v₁ v₂ ⟨s₁, _, S₁, _, L₁, _, _, hN⟩ ⟨s₂, _, S₂, _, L₂, _, _, _⟩ => ?_)
    (keep_taint fun p v₁ v₂ h₁ h₂ => pins p v₁ v₂ h₁.1 h₂.1)
    (nil_taint fun p v₁ v₂ h₁ h₂ => ⟨(pins p v₁ v₂ h₁.1 h₂.1).1, fun _ h => absurd h List.not_mem_nil⟩)) ?_
  · rw [L₁.r0, L₂.r0]
    congr 2
    exact decide_eq_decide.mpr ((S₁.zeroIff hN).trans (S₂.zeroIff hN).symm)
  · intro p v ⟨s, M, S, hM, L, hi, hc, hN⟩
    exact WP.mono (branch_ok S.pre L hi hc) fun w h => ⟨s, M, S, hM, h, hN⟩

theorem more_two : RelCT isa (Two NextPt) more fun _ _ => True :=
  more_taint fun p w₁ w₂ ⟨s₁, _, S₁, _, I₁, hN⟩ ⟨s₂, _, S₂, _, I₂, _⟩ =>
    ⟨by rw [I₁.sp, I₂.sp, S₁.fbEq, S₂.fbEq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [I₁.r4, I₂.r4]
      · rw [I₁.r5, I₂.r5, S₁.keptEq hN, S₂.keptEq hN]
      · rw [I₁.r11, I₂.r11, S₁.argEq, S₂.argEq]
      · rw [I₁.r28, I₂.r28, S₁.psEq, S₂.psEq]⟩

theorem step_two : RelCT isa (Two LoopPt) step fun _ _ => True :=
  RelCT.seq load_two (RelCT.seq branch_two more_two)

/-- At the end of the scan: all `N a` octets read. -/
def ScanDone (a u : State) : Prop := ∃ s M, PR a s ∧ Mm s M ∧ At s M (N a) u

theorem loop_two : RelCT isa (Two fun a s => 0 < N a ∧ LoopPt (a, 0) s) (.loop step (.nonzero .d .r12))
    (Two ScanDone) := by
  refine two_loop (Φ := fun a j s => LoopPt (a, j) s) N
    (step_two.mono (fun _ _ ⟨p, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨p, h₁, h₂⟩) fun _ _ h => h) ?_
  intro a j u hj ⟨s, M, S, hM, I, hi, hc, _⟩
  change At s M j u at I
  change j < rl s at hi
  change (kept s j).length < psLen s at hc
  have hs : VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) = N a := S.scanEq
  refine WP.mono (step_ok S.pre hM I hi hc) fun u' ⟨I', hz⟩ => ?_
  have hst : ((kept s (j + 1)).length = psLen s ∨ j + 1 = rl s) ↔ N a = j + 1 := by
    have := VG.Proof.RsaPkcs1Enc.stop_iff (n := psLen s) (r := randB s) (j := j) (by rw [hs]; exact hj) hc
    rw [randB_length, hs] at this; exact this
  have hk := I'.hc
  refine ⟨?_, fun hlt => ⟨s, M, S, hM, I', ?_, ?_, hlt⟩, fun he => ⟨s, M, S, hM, he ▸ I'⟩⟩
  · rw [eval_nonzero, hz]
    by_cases h : (kept s (j + 1)).length = psLen s ∨ j + 1 = rl s
    · rw [decide_eq_true h, decide_eq_false (by have := hst.mp h; omega)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by
        have : N a ≠ j + 1 := fun e => h (hst.mpr e)
        omega)]; rfl
  · show j + 1 < rl s
    have := S.nLe; omega
  · show (kept s (j + 1)).length < psLen s
    by_cases hn : (kept s (j + 1)).length = psLen s
    · have := hst.mp (.inl hn); omega
    · omega

/-- Before the scan. -/
def ScanPt (a t : State) : Prop := ∃ s, PR a s ∧ Mm s t.mem ∧ At s t.mem 0 t

theorem scan_two : RelCT isa (Two ScanPt) scan (Two ScanDone) := by
  refine two_ite (fun a t₁ t₂ ⟨s₁, S₁, _, I₁⟩ ⟨s₂, S₂, _, I₂⟩ => by
    rw [eval_nonzero, eval_nonzero, I₁.r11, I₂.r11, S₁.argEq, S₂.argEq]) ?_ ?_
  · refine loop_two.mono (fun t₁ t₂ ⟨a, ⟨⟨s₁, S₁, M₁, I₁⟩, e₁⟩, ⟨⟨s₂, S₂, M₂, I₂⟩, _⟩⟩ => ?_) fun _ _ h => h
    have hl : stackArg s₁ 2 ≠ 0 := by
      intro h0; rw [eval_nonzero, I₁.r11, h0] at e₁; cases e₁
    have hl' : 0 < rl s₁ := by
      rcases Nat.eq_zero_or_pos (rl s₁) with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa [rl] using h)) hl
      · exact h
    have hP₁ := S₁.pre.ps
    have hP₂ := S₂.pre.ps
    have hN : 0 < N a := by
      rw [← S₁.scanEq]
      exact VG.Proof.RsaPkcs1Enc.lt_scanLen (i := 0)
        (show (kept s₁ 0).length < psLen s₁ by rw [kept_zero, List.length_nil]; omega)
        (by rw [randB_length]; exact hl')
    refine ⟨a, ⟨hN, s₁, t₁.mem, S₁, M₁, I₁, hl', by rw [kept_zero, List.length_nil]; omega, hN⟩,
      ⟨hN, s₂, t₂.mem, S₂, M₂, I₂, by rw [S₂.rlEq, ← S₁.rlEq]; exact hl',
        by rw [kept_zero, List.length_nil]; omega, hN⟩⟩
  · refine two_post (nil_taint fun a t₁ t₂ ⟨⟨s₁, S₁, _, I₁⟩, _⟩ ⟨⟨s₂, S₂, _, I₂⟩, _⟩ =>
      ⟨by rw [I₁.sp, I₂.sp, S₁.fbEq, S₂.fbEq], fun _ h => absurd h List.not_mem_nil⟩)
      fun a t ⟨⟨s, S, hM, I⟩, e⟩ => WP.block_nil ⟨s, t.mem, S, hM, ?_⟩
    have h0 : stackArg s 2 = 0 := by
      rw [eval_nonzero, I.r11] at e
      by_cases h : stackArg s 2 = 0
      · exact h
      · rw [show (stackArg s 2 != 0) = true from bne_iff_ne.mpr h] at e; cases e
    have : N a = 0 := by
      have := S.nLe
      simp only [rl, h0] at this
      simpa using this
    rw [this]; exact I

/-! ## The call -/

/-- The callee's public data, from the caller's. -/
theorem callE_bytes {s w : State} (hp : RPre s) {i : Nat} (A : Args s i w) :
    Spec.Rsa.bytesAt (callE s w).mem ((callE s w).gpr .r5) ((callE s w).gpr .r6).toNat = nB s ∧
    Spec.Rsa.bytesAt (callE s w).mem ((callE s w).gpr .r7) ((callE s w).gpr .r8).toNat = eB s ∧
    Spec.Rsa.wordsAt (callE s w).mem (stackArg (callE s w) 4) (stackArg (callE s w) 5).toNat = preW s := by
  obtain ⟨-, -, -, -, a4, a5⟩ := callE_arg A
  rw [callE_gpr s w (r := .r5), callE_gpr s w (r := .r6), callE_gpr s w (r := .r7), callE_gpr s w (r := .r8),
    A.g5, A.g6, A.g7, A.g8, a4, a5]
  simp only [callArg]
  refine ⟨bytes_frame A.fr (fun r hr => ?_) (by have := hp.wN; omega),
    bytes_frame A.fr (fun r hr => ?_) (by have := hp.wE; omega), words_frame A.fr fun r hr => ?_⟩ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> first
      | exact hp.dKn.symm | exact hp.dTn.symm | exact hp.dKe.symm | exact hp.dTe.symm
      | exact hp.dKq.symm | exact hp.dTq.symm

/-- After the call's arguments. -/
def ArgsPt (a w : State) : Prop := ∃ s, PR a s ∧ Args s (N a) w

/-- After the call. -/
def AfterPt (a y : State) : Prop := ∃ s, PR a s ∧ AfterCall s (N a) y

theorem call_two : RelCT isa (Two ArgsPt) encCall fun _ _ => True := by
  unfold encCall
  refine RelCT.callEx (k := encK) Enc.code_verified.1 Enc.code_verified.2.1
    fun w₁ w₂ ⟨a, ⟨s₁, S₁, A₁⟩, ⟨s₂, S₂, A₂⟩⟩ => ?_
  have h₁ := S₁.pre
  have h₂ := S₂.pre
  obtain ⟨a0₁, a1₁, a2₁, a3₁, a4₁, a5₁⟩ := callE_arg A₁
  obtain ⟨a0₂, a1₂, a2₂, a3₂, a4₂, a5₂⟩ := callE_arg A₂
  obtain ⟨n₁, e₁, q₁⟩ := callE_bytes h₁ A₁
  obtain ⟨n₂, e₂, q₂⟩ := callE_bytes h₂ A₂
  refine ⟨callRd s₁, callWr s₁, callRd s₂, callWr s₂, enc_pre (preE_entry h₁ A₁), enc_pre (preE_entry h₂ A₂),
    enc_pub (by rw [callE_sp A₁, callE_sp A₂, S₁.fbEq, S₂.fbEq]) (fun r hr => ?_) (fun j hj => ?_)
      (by rw [n₁, n₂, ← S₁.2.2.2.2.1, ← S₂.2.2.2.2.1]) (by rw [e₁, e₂, ← S₁.2.2.2.2.2.1, ← S₂.2.2.2.2.2.1])
      (by rw [q₁, q₂, ← S₁.2.2.2.2.2.2.1, ← S₂.2.2.2.2.2.2.1]),
    (call_covers h₁ A₁).1, (call_covers h₁ A₁).2, (call_covers h₂ A₂).1, (call_covers h₂ A₂).2⟩
  · rw [callE_gpr s₁ w₁ (fun h => by revert r; decide), callE_gpr s₂ w₂ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.g3, A₂.g3, S₁.gprEq, S₂.gprEq]
    · rw [A₁.g4, A₂.g4, S₁.gprEq, S₂.gprEq]
    · rw [A₁.g5, A₂.g5, S₁.gprEq, S₂.gprEq]
    · rw [A₁.g6, A₂.g6, S₁.gprEq, S₂.gprEq]
    · rw [A₁.g7, A₂.g7, S₁.gprEq, S₂.gprEq]
    · rw [A₁.g8, A₂.g8, S₁.gprEq, S₂.gprEq]
    · rw [A₁.g9, A₂.g9, S₁.gprEq, S₂.gprEq]
    · rw [A₁.g10, A₂.g10, S₁.argEq, S₂.argEq]
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a0₁, a0₂]; simp only [callArg, pb, S₁.fbEq, S₂.fbEq]
    · rw [a1₁, a1₂]; simp only [callArg, S₁.psEq, S₂.psEq]
    · rw [a2₁, a2₂]; simp only [callArg, S₁.argEq (j := 3), S₂.argEq (j := 3)]
    · rw [a3₁, a3₂]; simp only [callArg, S₁.argEq (j := 4), S₂.argEq (j := 4)]
    · rw [a4₁, a4₂]; simp only [callArg, S₁.argEq (j := 5), S₂.argEq (j := 5)]
    · rw [a5₁, a5₂]; simp only [callArg, S₁.argEq (j := 6), S₂.argEq (j := 6)]

/-! ## The body -/

/-- Whether `PS` is full, after the scan. -/
def FullPt (a v : State) : Prop :=
  ∃ s M, PR a s ∧ Mm s M ∧ At s M (N a) v ∧
    isa.eval (.zero .d .r12) v = some (decide (psLen s = (kept s (N a)).length))

/-- In the frame. -/
def EndPt (a x : State) : Prop := ∃ s, PR a s ∧ x.sp = fb s

theorem accept_sp {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} {u : State} (hI : At s M i u)
    (hf : (kept s i).length = psLen s) : WP isa accept u fun x => x.sp = fb s := by
  unfold accept
  exact WP.seq (WP.mono (prep_ok hp hM hI hf) fun w A => WP.seq (WP.mono (call_ok hp A) fun y C =>
    WP.mono (accTail_ok hp C) fun x h => h.1.sp))

theorem accept_two : RelCT isa (Two fun a v => FullPt a v ∧ isa.eval (.zero .d .r12) v = some true) accept
    (Two EndPt) := by
  have full : ∀ {a v : State}, FullPt a v ∧ isa.eval (.zero .d .r12) v = some true →
      ∃ s M, PR a s ∧ Mm s M ∧ At s M (N a) v ∧ (kept s (N a)).length = psLen s :=
    fun ⟨⟨s, M, S, hM, I, ev⟩, e⟩ => ⟨s, M, S, hM, I, by
      rw [ev] at e; exact (of_decide_eq_true (Option.some.inj e)).symm⟩
  refine two_post ?_ fun a v h => by
    obtain ⟨s, M, S, hM, I, hf⟩ := full h
    exact WP.mono (accept_sp S.pre hM I hf) fun x hx => ⟨s, S, hx⟩
  unfold accept
  refine RelCT.seq (two_post (Ψ := ArgsPt) (prep_taint fun a v₁ v₂ h₁ h₂ => ?_) fun a v h => ?_) ?_
  · obtain ⟨s₁, _, S₁, _, I₁, _⟩ := full h₁
    obtain ⟨s₂, _, S₂, _, I₂, _⟩ := full h₂
    exact ⟨by rw [I₁.sp, I₂.sp, S₁.fbEq, S₂.fbEq], fun r hr => by
      rw [List.mem_singleton.mp hr, I₁.r30, I₂.r30, S₁.gprEq, S₂.gprEq]⟩
  · obtain ⟨s, M, S, hM, I, hf⟩ := full h
    exact WP.mono (prep_ok S.pre hM I hf) fun w A => ⟨s, S, A⟩
  refine RelCT.seq (two_post (Ψ := AfterPt) call_two fun a w ⟨s, S, A⟩ =>
    WP.mono (call_ok S.pre A) fun y C => ⟨s, S, C⟩) ?_
  exact accTail_taint fun a y₁ y₂ ⟨s₁, S₁, C₁⟩ ⟨s₂, S₂, C₂⟩ =>
    ⟨by rw [C₁.sp, C₂.sp, S₁.fbEq, S₂.fbEq], fun r hr => by
      rw [List.mem_singleton.mp hr, C₁.r28, C₂.r28, S₁.psEq, S₂.psEq]⟩

theorem reject_two : RelCT isa (Two fun a v => FullPt a v ∧ isa.eval (.zero .d .r12) v = some false) reject
    (Two EndPt) := by
  have rej : ∀ {a v : State}, FullPt a v ∧ isa.eval (.zero .d .r12) v = some false →
      ∃ s M, PR a s ∧ Mm s M ∧ At s M (N a) v ∧ N a = rl s ∧ (kept s (N a)).length < psLen s :=
    fun {a v} ⟨⟨s, M, S, hM, I, ev⟩, e⟩ => by
      have hne : psLen s ≠ (kept s (N a)).length := by
        rw [ev] at e; exact of_decide_eq_false (Option.some.inj e)
      have hc : (kept s (N a)).length < psLen s := by have := I.hc; omega
      refine ⟨s, M, S, hM, I, ?_, hc⟩
      have hle := S.nLe
      by_contra hlt
      have := VG.Proof.RsaPkcs1Enc.lt_scanLen (n := psLen s) (rand := randB s) (i := N a) hc
        (by rw [randB_length]; omega)
      rw [S.scanEq] at this; omega
  refine two_post (reject_taint fun a v₁ v₂ h₁ h₂ => ?_) fun a v h => ?_
  · obtain ⟨s₁, _, S₁, _, I₁, -, -⟩ := rej h₁
    obtain ⟨s₂, _, S₂, _, I₂, -, -⟩ := rej h₂
    refine ⟨by rw [I₁.sp, I₂.sp, S₁.fbEq, S₂.fbEq], fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [I₁.r4, I₂.r4]
    · rw [I₁.r5, I₂.r5, S₁.keptEq (Nat.le_refl _), S₂.keptEq (Nat.le_refl _)]
    · rw [I₁.r28, I₂.r28, S₁.psEq, S₂.psEq]
    · rw [I₁.r29, I₂.r29, S₁.gprEq, S₂.gprEq]
    · rw [I₁.r30, I₂.r30, S₁.gprEq, S₂.gprEq]
    · rw [I₁.r31, I₂.r31, S₁.gprEq, S₂.gprEq]
  · obtain ⟨s, M, S, hM, I, hN, hc⟩ := rej h
    rw [hN] at I hc
    exact WP.mono (reject_ok S.pre hM I hc) fun x F => ⟨s, S, F.sv.sp⟩

/-- On entry to the frame's body. -/
def AllocPt (a u : State) : Prop := ∃ s, PR a s ∧ u = allocated frameBytes s

theorem body_two : RelCT isa (Two AllocPt) body fun _ _ => True := by
  unfold body
  refine RelCT.seq (two_post (Ψ := ScanPt) (setup_taint fun a u₁ u₂ ⟨s₁, S₁, e₁⟩ ⟨s₂, S₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show fb s₁ = fb s₂; rw [S₁.fbEq, S₂.fbEq], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨s, S, e⟩ => by
      subst e; exact WP.mono (setup_ok S.pre) fun t ⟨hM, I⟩ => ⟨s, S, hM, I⟩) ?_
  refine RelCT.seq scan_two ?_
  refine RelCT.seq (two_post (Ψ := FullPt) (full_taint fun a u₁ u₂ ⟨s₁, _, S₁, _, I₁⟩ ⟨s₂, _, S₂, _, I₂⟩ =>
      ⟨by rw [I₁.sp, I₂.sp, S₁.fbEq, S₂.fbEq], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨s, M, S, hM, I⟩ => WP.mono (full_ok S.pre I) fun v ⟨I', ev⟩ => ⟨s, M, S, hM, I', ev⟩) ?_
  refine RelCT.seq (two_ite (fun a v₁ v₂ ⟨s₁, _, S₁, _, _, e₁⟩ ⟨s₂, _, S₂, _, _, e₂⟩ => by
      rw [e₁, e₂, S₁.psEq, S₂.psEq, S₁.keptEq (Nat.le_refl _), S₂.keptEq (Nat.le_refl _)])
    accept_two reject_two) ?_
  exact restore_taint fun a x₁ x₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ =>
    ⟨by rw [h₁, h₂, S₁.fbEq, S₂.fbEq], fun _ h => absurd h List.not_mem_nil⟩

theorem code_ct : ConstantTime isa (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre pub code := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold code
  refine (two_alloc (Φ := PR) (R := fun _ _ => True) (fun a s₁ s₂ S₁ S₂ =>
      ⟨by rw [S₁.spEq, S₂.spEq], fun _ h => absurd h List.not_mem_nil⟩)
    (body_two.mono (fun u₁ u₂ ⟨a, ⟨s₁, S₁, e₁⟩, s₂, S₂, e₂⟩ => ⟨a, ⟨s₁, S₁, e₁⟩, ⟨s₂, S₂, e₂⟩⟩)
      fun _ _ h => h)).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨s₁, ⟨h₁, pub_refl s₁⟩, ⟨h₂, hp⟩⟩) fun _ _ h => h

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd
