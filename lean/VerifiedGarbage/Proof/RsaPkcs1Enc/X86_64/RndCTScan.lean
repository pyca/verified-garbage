module

-- separate module: its proofs build in parallel with `RndHeads`

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndContract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomCT
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndContract
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86-64: the scan in constant time

Two runs from entry states that agree with an anchor `a` on the public data
(`PR`) read the same octets of the tape and keep as many of them: the scan
reads `scanLen` octets of `a`'s tape in both (`N`), each read octet is zero in
one run exactly when it is in the other, and so is each count of kept octets
(`Proof/RsaPkcs1Enc/RandomCT.lean`). So the branch on each octet, the index
of each store and the end of the loop are the same in both runs; the taint
analysis checks the rest, with these registers public.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- An entry state meeting the precondition with the anchor's public data. -/
def PR (a s : State) : Prop := contract.pre s ∧ pub a s

theorem PR.pre {a s : State} (h : PR a s) : RPre s := pre_of h.1

theorem PR.gprEq {a s : State} (h : PR a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9]) :
    s.gpr r = a.gpr r := (h.2.2.1 r hr).symm

theorem PR.rspEq {a s : State} (h : PR a s) : s.gpr .rsp = a.gpr .rsp := h.2.1.symm

theorem PR.argEq {a s : State} (h : PR a s) {j : Nat} (hj : j < 9) : stackArg s j = stackArg a j :=
  (h.2.2.2.1 j hj).symm

theorem PR.fbEq {a s : State} (h : PR a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _; rw [h.rspEq]

theorem PR.psEq {a s : State} (h : PR a s) : psLen s = psLen a := by
  unfold psLen kOf; rw [h.gprEq (r := .r8) (by decide), h.argEq (j := 2) (by decide)]

theorem PR.lenEq {a s : State} (h : PR a s) : (stackArg s 4).toNat = (stackArg a 4).toNat := by
  rw [h.argEq (by decide)]

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

/-! ## The loop -/

/-- Before octet `j` of the scan. -/
def LoopPt (p : State × Nat) (u : State) : Prop :=
  ∃ s t₀, PR p.1 s ∧ Before s t₀ ∧ At s t₀ p.2 u ∧ p.2 < (stackArg s 4).toNat ∧
    (kept s p.2).length < psLen s ∧ p.2 < N p.1

/-- After the load of octet `j`. -/
def LoadPtA (p : State × Nat) (v : State) : Prop :=
  ∃ s t₀, PR p.1 s ∧ Before s t₀ ∧ LoadPt s t₀ p.2 v ∧ p.2 < (stackArg s 4).toNat ∧
    (kept s p.2).length < psLen s ∧ p.2 < N p.1

/-- After octet `j`, before the comparison. -/
def NextPt (p : State × Nat) (w : State) : Prop :=
  ∃ s t₀, PR p.1 s ∧ Before s t₀ ∧ At s t₀ (p.2 + 1) w ∧ p.2 < N p.1

/-- After the comparison of the count with `psLen`. -/
def CmpPt (p : State × Nat) (x : State) : Prop :=
  ∃ s t₀, PR p.1 s ∧ Before s t₀ ∧ At s t₀ (p.2 + 1) x ∧ p.2 < N p.1 ∧
    x.zf = some (decide ((kept s (p.2 + 1)).length = psLen s))

theorem load_two : RelCT isa (Two LoopPt) (.block load) (Two LoadPtA) := by
  refine two_piece [.rsp, .rsi, .rcx] (fun p u₁ u₂ ⟨s₁, t₁, S₁, B₁, I₁, _⟩ ⟨s₂, t₂, S₂, B₂, I₂, _⟩ r hr => ?_)
    (by taint_decide) fun p u ⟨s, t₀, S, B, I, hi, hc, hN⟩ =>
      WP.mono (load_ok S.pre B I hi hc) fun v h => ⟨s, t₀, S, B, h, hi, hc, hN⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [(I₁.keep.gpr (by decide)).trans B₁.rsp, (I₂.keep.gpr (by decide)).trans B₂.rsp, S₁.fbEq, S₂.fbEq]
  · rw [(I₁.keep.gpr (by decide)).trans B₁.rsi, (I₂.keep.gpr (by decide)).trans B₂.rsi,
      S₁.argEq (by decide), S₂.argEq (by decide)]
  · rw [I₁.rcx, I₂.rcx]

theorem branch_two : RelCT isa (Two LoadPtA) (.ite .ne (.block keep) (.block [])) (Two NextPt) := by
  refine two_post (two_ite (fun p v₁ v₂ ⟨s₁, t₁, S₁, B₁, ⟨u₁, I₁, _, _, _, z₁, _⟩, _, _, hN₁⟩
      ⟨s₂, t₂, S₂, B₂, ⟨u₂, I₂, _, _, _, z₂, _⟩, _, _, _⟩ => ?_) ?_ ?_) ?_
  · rw [eval_ne z₁, eval_ne z₂]
    congr 2
    exact decide_eq_decide.mpr ((S₁.zeroIff hN₁).trans (S₂.zeroIff hN₁).symm)
  · refine two_taint [.rdi, .rdx] (fun p v₁ v₂ ⟨⟨s₁, t₁, S₁, B₁, ⟨u₁, I₁, _, _, _, _, k₁⟩, _, _, hN⟩, _⟩
        ⟨⟨s₂, t₂, S₂, B₂, ⟨u₂, I₂, _, _, _, _, k₂⟩, _, _, _⟩, _⟩ r hr => ?_) (by taint_decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(k₁.gpr (by decide)).trans ((I₁.keep.gpr (by decide)).trans B₁.rdi),
        (k₂.gpr (by decide)).trans ((I₂.keep.gpr (by decide)).trans B₂.rdi), S₁.fbEq, S₂.fbEq]
    · rw [(k₁.gpr (by decide)).trans I₁.rdx, (k₂.gpr (by decide)).trans I₂.rdx,
        S₁.keptEq (Nat.le_of_lt hN), S₂.keptEq (Nat.le_of_lt hN)]
  · exact two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  · intro p v ⟨s, t₀, S, B, L, hi, hc, hN⟩
    exact WP.mono (branch_ok S.pre B L hi hc) fun w h => ⟨s, t₀, S, B, h, hN⟩

/-- `full_ok`'s comparison, which keeps `At`. -/
theorem cmpAt_ok {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u) :
    WP isa (.block [.alu .cmp .rdx (.mem (sp oPs))]) u fun v => At s t₀ i v ∧
      v.zf = some (decide ((kept s i).length = psLen s)) :=
  WP.mono (full_ok hp hb hI) fun w ⟨hm, kw, hd, hzw⟩ =>
    ⟨⟨(hI.keep.trans kw).mono (by decide), hm ▸ hI.out, hm ▸ hI.buf, (kw.gpr (by decide)).trans hI.rcx,
      hd.trans hI.rdx, hI.hi, hI.hc⟩, hzw⟩

theorem cmp_two : RelCT isa (Two NextPt) (.block [.alu .cmp .rdx (.mem (sp oPs))]) (Two CmpPt) := by
  refine two_piece [.rsp] (fun p u₁ u₂ ⟨s₁, t₁, S₁, B₁, I₁, _⟩ ⟨s₂, t₂, S₂, B₂, I₂, _⟩ r hr => ?_)
    (by taint_decide) fun p u ⟨s, t₀, S, B, I, hN⟩ =>
      WP.mono (cmpAt_ok S.pre B I) fun v ⟨h, hz⟩ => ⟨s, t₀, S, B, h, hN, hz⟩
  rw [List.mem_singleton.mp hr, (I₁.keep.gpr (by decide)).trans B₁.rsp, (I₂.keep.gpr (by decide)).trans B₂.rsp,
    S₁.fbEq, S₂.fbEq]

theorem more_two : RelCT isa (Two NextPt) more fun _ _ => True := by
  refine RelCT.seq cmp_two (two_ite (fun p x₁ x₂ ⟨s₁, t₁, S₁, B₁, I₁, hN, z₁⟩ ⟨s₂, t₂, S₂, B₂, I₂, _, z₂⟩ => ?_)
    (two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide))
    (two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)))
  rw [eval_e z₁, eval_e z₂, S₁.keptEq hN, S₂.keptEq hN, S₁.psEq, S₂.psEq]

theorem step_two : RelCT isa (Two LoopPt) step fun _ _ => True :=
  RelCT.seq load_two (RelCT.seq branch_two more_two)

/-- At the end of the scan: all `N a` octets read. -/
def ScanDone (a u : State) : Prop := ∃ s t₀, PR a s ∧ Before s t₀ ∧ At s t₀ (N a) u

theorem loop_two : RelCT isa (Two fun a s => 0 < N a ∧ LoopPt (a, 0) s) (.loop step .ne) (Two ScanDone) := by
  refine two_loop (Φ := fun a j s => LoopPt (a, j) s) N
    (step_two.mono (fun _ _ ⟨p, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨p, h₁, h₂⟩) fun _ _ h => h) ?_
  intro a j u hj ⟨s, t₀, S, B, I, hi, hc, _⟩
  change j < (stackArg s 4).toNat at hi
  change (kept s j).length < psLen s at hc
  change At s t₀ j u at I
  have hs : VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) = N a := S.scanEq
  refine WP.mono (step_ok S.pre B I hi hc) fun u' ⟨I', hz⟩ => ?_
  have hst : ((kept s (j + 1)).length = psLen s ∨ j + 1 = (stackArg s 4).toNat) ↔ N a = j + 1 := by
    have := VG.Proof.RsaPkcs1Enc.stop_iff (n := psLen s) (r := randB s) (j := j) (by rw [hs]; exact hj) hc
    rw [randB_length, hs] at this; exact this
  have hk := I'.hc
  refine ⟨?_, fun hlt => ⟨s, t₀, S, B, I', ?_, ?_, hlt⟩, fun he => ⟨s, t₀, S, B, he ▸ I'⟩⟩
  · rw [eval_ne hz]
    by_cases h : (kept s (j + 1)).length = psLen s ∨ j + 1 = (stackArg s 4).toNat
    · rw [decide_eq_true h, decide_eq_false (by have := hst.mp h; omega)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by
        have : N a ≠ j + 1 := fun e => h (hst.mpr e)
        omega)]; rfl
  · show j + 1 < (stackArg s 4).toNat
    have := VG.Proof.RsaPkcs1Enc.scanLen_le (psLen s) (randB s)
    rw [randB_length, hs] at this; omega
  · show (kept s (j + 1)).length < psLen s
    by_cases hn : (kept s (j + 1)).length = psLen s
    · have := hst.mp (.inl hn); omega
    · omega

theorem at_zero {s t : State} (hp : RPre s) (hcx : t.gpr .rcx = 0) (hdx : t.gpr .rdx = 0) : At s t 0 t :=
  have hP := hp.ps
  ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun j hj => absurd hj (by simp [kept_zero]),
    hcx, by rw [hdx, kept_zero]; rfl, Nat.zero_le _, by rw [kept_zero]; simp⟩

/-- Before the scan. -/
def ScanPt (a t : State) : Prop :=
  ∃ s, PR a s ∧ Before s t ∧ t.gpr .rcx = 0 ∧ t.gpr .rdx = 0 ∧ t.zf = some (stackArg s 4 == 0)

theorem scan_two : RelCT isa (Two ScanPt) scan (Two ScanDone) := by
  refine two_ite (fun a t₁ t₂ ⟨s₁, S₁, _, _, _, z₁⟩ ⟨s₂, S₂, _, _, _, z₂⟩ => by
    rw [eval_ne z₁, eval_ne z₂, S₁.argEq (by decide), S₂.argEq (by decide)]) ?_ ?_
  · refine loop_two.mono (fun t₁ t₂ ⟨a, ⟨⟨s₁, S₁, B₁, c₁, d₁, z₁⟩, e₁⟩, ⟨⟨s₂, S₂, B₂, c₂, d₂, z₂⟩, _⟩⟩ => ?_)
      fun _ _ h => h
    have hl : stackArg s₁ 4 ≠ 0 := by
      intro h0; rw [eval_ne z₁, h0] at e₁; cases e₁
    have hl' : 0 < (stackArg s₁ 4).toNat := by
      rcases Nat.eq_zero_or_pos (stackArg s₁ 4).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hl
      · exact h
    have hP₁ := S₁.pre.ps
    have hP₂ := S₂.pre.ps
    have hN : 0 < N a := by
      rw [← S₁.scanEq]
      exact VG.Proof.RsaPkcs1Enc.lt_scanLen (i := 0)
        (show (kept s₁ 0).length < psLen s₁ by rw [kept_zero, List.length_nil]; omega)
        (by rw [randB_length]; exact hl')
    refine ⟨a, ⟨hN, s₁, t₁, S₁, B₁, at_zero S₁.pre c₁ d₁, hl', by rw [kept_zero, List.length_nil]; omega, hN⟩,
      ⟨hN, s₂, t₂, S₂, B₂, at_zero S₂.pre c₂ d₂, by rw [S₂.lenEq, ← S₁.lenEq]; exact hl',
        by rw [kept_zero, List.length_nil]; omega, hN⟩⟩
  · refine two_piece [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
      fun a t ⟨⟨s, S, B, hcx, hdx, z⟩, e⟩ => WP.block_nil ⟨s, t, S, B, ?_⟩
    have h0 : stackArg s 4 = 0 := by
      rw [eval_ne z] at e
      by_cases h : stackArg s 4 = 0
      · exact h
      · rw [beq_false_of_ne h] at e; cases e
    have : N a = 0 := by
      rw [← S.scanEq]
      have := VG.Proof.RsaPkcs1Enc.scanLen_le (psLen s) (randB s)
      rw [randB_length, h0] at this
      simpa using this
    rw [this]; exact at_zero S.pre hcx hdx

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd
