module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# The x86 RSA padding functions: pieces proven correct and constant time at once

As on ARMv7 (`Proof/Rsa/Arm/RvVP.lean`): `VP F c G`: from any state at the
stage `F σ` of a run from `σ`, `c` ends at the stage `G σ` (`wp`), and two
runs, each at the stage `F` of its own run, leak the same trace and end at
the stages `G` (`ct`). The stages carry the public parameters both runs
share, so that a piece checked by the taint analysis needs only that the
registers it takes as public are determined by them (`VP.taint`), and
pieces compose by `seq`, `ite` and `loop` (whose number of iterations is
public). A call of verified code (`VP.call`), and a call in a frame of its
arguments (`VP.callWith`), are pieces when their contract holds in every
state of the stage and its public data agrees in two.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86

/-- Two runs, each at the stage `F` of its own run from `σ`. -/
def Two (F : State → State → Prop) (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, F σ₁ s₁ ∧ F σ₂ s₂

structure VP (F : State → State → Prop) (c : Prog isa) (G : State → State → Prop) : Prop where
  wp : ∀ σ s, F σ s → WP isa c s (G σ)
  ct : RelCT isa (Two F) c (Two G)

namespace VP

variable {F G H : State → State → Prop}

/-- From a relation of any two runs and correctness of each. -/
theorem of_ct {c : Prog isa}
    (ct : ∀ σ₁ σ₂, RelCT isa (fun s₁ s₂ => F σ₁ s₁ ∧ F σ₂ s₂) c (fun _ _ => True))
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G := by
  refine ⟨wp, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, h₁, h₂⟩ e₁ e₂
  have r := ((ct σ₁ σ₂).wp (F₁ := G σ₁) (F₂ := G σ₂) fun s t h => ⟨wp _ _ h.1, wp _ _ h.2⟩)
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, σ₁, σ₂, r.2.2.1, r.2.2.2⟩

/-- A piece the taint analysis checks with the registers `rs` public. -/
theorem taint {c : Prog isa} (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.check VG.X86.taint (τr rs) c hc).isSome = true)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G := by
  obtain ⟨_, hc⟩ := cert
  exact of_ct (fun σ₁ σ₂ => RelCT.taint (A := VG.X86.taint) (τr rs)
    (fun s t h => agree_regs (regs _ _ _ _ h.1 h.2)) hc) wp

theorem mono {F' G' : State → State → Prop} {c : Prog isa} (h : VP F c G)
    (hF : ∀ σ s, F' σ s → F σ s) (hG : ∀ σ s, G σ s → G' σ s) : VP F' c G' :=
  ⟨fun σ s hs => WP.mono (h.wp σ s (hF σ s hs)) (hG σ),
    h.ct.mono (fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, hF _ _ h₁, hF _ _ h₂⟩)
      fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, hG _ _ h₁, hG _ _ h₂⟩⟩

theorem seq {c₁ c₂ : Prog isa} (h₁ : VP F c₁ G) (h₂ : VP G c₂ H) : VP F (.seq c₁ c₂) H :=
  ⟨fun σ s hs => WP.seq (WP.mono (h₁.wp σ s hs) fun t ht => h₂.wp σ t ht), RelCT.seq h₁.ct h₂.ct⟩

theorem block_append {l₁ l₂ : List Instr} (h₁ : VP F (.block l₁) G) (h₂ : VP G (.block l₂) H) :
    VP F (.block (l₁ ++ l₂)) H :=
  ⟨fun σ s hs => WP.block_append (WP.mono (h₁.wp σ s hs) fun t ht => h₂.wp σ t ht),
    RelCT.block_append (RelCT.seq h₁.ct h₂.ct)⟩

theorem block_nil (h : ∀ σ s, F σ s → G σ s) : VP F (.block []) G :=
  ⟨fun σ s hs => WP.block_nil (h σ s hs),
    RelCT.block_nil fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, h _ _ h₁, h _ _ h₂⟩⟩

/-- A branch on a condition both runs agree on, and that is defined. -/
theorem ite {c : Cond} {t e : Prog isa}
    (hd : ∀ σ s, F σ s → ∃ b, isa.eval c s = some b)
    (hc : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : VP (fun σ s => F σ s ∧ isa.eval c s = some true) t G)
    (he : VP (fun σ s => F σ s ∧ isa.eval c s = some false) e G) : VP F (.ite c t e) G := by
  refine ⟨fun σ s hs => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hd σ s hs
    exact WP.ite b hb (fun h => ht.wp σ s ⟨hs, by rw [hb, h]⟩) (fun h => he.wp σ s ⟨hs, by rw [hb, h]⟩)
  · refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => hc _ _ _ _ h₁ h₂) ?_ ?_
    · exact ht.ct.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨h₁, e⟩, h₂, (hc _ _ _ _ h₁ h₂).symm.trans e⟩) fun _ _ h => h
    · exact he.ct.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨h₁, e⟩, h₂, (hc _ _ _ _ h₁ h₂).symm.trans e⟩) fun _ _ h => h

/-- A loop whose iterations left, `n + 1` at the stage `I (n + 1)`, both
runs share: each iteration goes on iff `n > 0`. -/
theorem loop {I : Nat → State → State → Prop} {body : Prog isa} {c : Cond} {Q : State → State → Prop}
    (hb : ∀ n, VP (I (n + 1)) body fun σ s =>
      isa.eval c s = some (decide (0 < n)) ∧ (n = 0 → Q σ s) ∧ (0 < n → I n σ s))
    (n : Nat) : VP (I (n + 1)) (.loop body c) Q := by
  refine ⟨fun σ s hs => ?_, ?_⟩
  · refine WP.loop (M := isa) (fun m u => I (m + 1) σ u) (fun m u hu => ?_) n s hs
    refine WP.mono ((hb m).wp σ u hu) fun u' ⟨he, hq, hi⟩ => ?_
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · exact .inl ⟨by rw [he, h0]; rfl, hq h0⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .inr ⟨by rw [he]; simp, k, by omega, hi hp⟩
  · refine RelCT.loop (M := isa) (fun m => Two (I (m + 1))) (fun m => ?_) n
    refine (hb m).ct.mono (fun _ _ h => h) fun s₁ s₂ ⟨σ₁, σ₂, ⟨e₁, q₁, i₁⟩, ⟨e₂, q₂, i₂⟩⟩ =>
      ⟨e₁.trans e₂.symm, fun hf => ?_, fun ht => ?_⟩
    · have h0 : m = 0 := by rw [e₁] at hf; simpa using hf
      exact ⟨σ₁, σ₂, q₁ h0, q₂ h0⟩
    · have hp : 0 < m := by rw [e₁] at ht; simpa using ht
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact ⟨k, by omega, σ₁, σ₂, i₁ hp, i₂ hp⟩

/-- A call of verified code `c`, given the regions `rd` and `wr`, the same
in both runs, with the same `esp`. -/
theorem call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (rd wr : List Region)
    (pre : ∀ σ s, F σ s → k.pre (s.callEntry.withRegions rd wr))
    (cov : ∀ σ s, F σ s → Covers (rd ++ wr) (s.rd ++ s.wr) ∧ Covers wr s.wr)
    (room : ∀ σ s, F σ s → stackUse c + 4 ≤ (s.gpr .esp).toNat)
    (esp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.gpr .esp = s₂.gpr .esp)
    (pub : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ →
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr))
    (post : ∀ σ s s', F σ s → s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .esp → s₂.gpr r = s'.gpr r) ∧
        k.post (s.callEntry.withRegions rd wr) s₂) → G σ s') :
    VP F (.call n c) G :=
  of_ct (fun _ _ => RelCT.call hv hct rd wr fun _ _ h =>
      ⟨pre _ _ h.1, pre _ _ h.2, pub _ _ _ _ h.1 h.2, (cov _ _ h.1).1, (cov _ _ h.1).2, (cov _ _ h.2).1,
        (cov _ _ h.2).2, esp _ _ _ _ h.1 h.2⟩)
    fun σ s h => WP.call hv hsp (room σ s h) (pre σ s h) (cov σ s h).1 (cov σ s h).2
      fun s' r w cs f _ po => post σ s s' h r w cs f po

/-- A call of verified code `c` in a frame of its arguments `rs`, given the
regions `rd` and `wr`, the same in both runs, with the same `esp`. -/
theorem callWith {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    (rd wr : List Region)
    (pre : ∀ σ s, F σ s → CallPre k rs rd wr s)
    (room : ∀ σ s, F σ s → 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat)
    (esp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.gpr .esp = s₂.gpr .esp)
    (pub : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ →
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr))
    (post : ∀ σ s s', F σ s → s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ k.post ((pushed rs s).callEntry.withRegions rd wr) s₂) → G σ s') :
    VP F (.frame (.push rs) (.call n c) (.pop .eax rs.length)) G :=
  of_ct (fun _ _ => RelCT.callWith hv hct rd wr fun _ _ h =>
      ⟨pre _ _ h.1, pre _ _ h.2, esp _ _ _ _ h.1 h.2, pub _ _ _ _ h.1 h.2⟩)
    fun σ s h => WP.callWith hv hsp hne hrs (room σ s h) (pre σ s h)
      fun s' r w cs f po => post σ s s' h r w cs f po

end VP

/-! ## Code that keeps `esp` -/

theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := fun i hi => by
  rcases List.mem_append.mp hi with h | h
  exacts [ha i h, hb i h]

theorem noSp_loop {c : Cond} {b : Prog isa} (hb : NoSp b) : NoSp (.loop b c) := hb

theorem noSp_call {n : String} {c : Prog isa} (hc : NoSp c) : NoSp (.call n c) := hc

/-- A frame whose entry and exit keep `esp` as instructions (push, pop, allocation). -/
theorem noSp_frame {i j : Instr} {b : Prog isa} (hi : Taint.clobbers i .esp = false)
    (hj : Taint.clobbers j .esp = false) (hb : NoSp b) : NoSp (.frame i b j) := fun x hx => by
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | hx) | rfl
  · exact hi
  · exact hb x hx
  · exact hj

/-- A call in a frame of its arguments. -/
theorem noSp_pushCall {rs : List Reg} {k : Nat} {n : String} {c : Prog isa} (hc : NoSp c) :
    NoSp (.frame (.push rs) (.call n c) (.pop .eax k)) := fun i hi => by
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact hc i hi
  · rfl

end VG.Proof.RsaPkcs1Sig.X86
