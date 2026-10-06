import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Top

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (sample4K relInv taintRel relStart Rel2 ofNat64_pred ofNat64_beq_zero RelCT.postDep)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' pre_of pub_scr pub_aP pub_B env_rbx start_ct)
open VG.Proof.MlDsa.X86_64.Sample (nil_regs WP.all')
open VG.Proof.MlDsa.X86_64.Sample.RejNttCT (BPre BRel body_ct)
open VG.Spec.MlKem (poly4)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (parse segment batch)

/-- Two runs at iteration `t` of a half of seed `K`, from states with `X`,
`n = count - t` iterations from its end. -/
def HI (X : State → State → Prop) (K h off count n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ s₀₁ s₀₂ t, sample4K.pre σ₁ ∧ sample4K.pre σ₂ ∧ sample4K.pub σ₁ σ₂ ∧ n = count - t ∧ t < count ∧
    X σ₁ s₀₁ ∧ X σ₂ s₀₂ ∧ HAt σ₁ s₀₁ K h off count t s₁ ∧ HAt σ₂ s₀₂ K h off count t s₂

theorem hbpre {σ : State} (hp : Pre σ) {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hspan : off + count ≤ 168) (ht : t < count) {s : State}
    (hI : HAt σ s₀ K h off count t s) : BPre s (poly4 (aP σ) K) (Lt σ K (168 * h + off + t)) :=
  ⟨hI.rbp, hI.rdi, Lt_length_le σ K _, coeffsWr hp hK hI.env, hI.stored,
    by simpa using hat_regions hp hK hspan hI (j := 0) (by omega), hat_regions hp hK hspan hI (by omega),
    hat_regions hp hK hspan hI (by omega)⟩

theorem hi_brel {X : State → State → Prop} {K h off count n : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) {s₁ s₂ : State}
    (H : HI X K h off count n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, hq, _, ht, _, _, l₁, l₂⟩ := H
  refine ⟨poly4 (aP σ₁) K, Lt σ₁ K (168 * h + off + t), hbpre (pre_of p₁) hK hspan ht l₁,
    by rw [pub_aP hq, pub_Lt4 hq hK]; exact hbpre (pre_of p₂) hK hspan ht l₂,
    by rw [l₁.rsi, l₂.rsi, at', at', pub_scr hq], by rw [l₁.rcx, l₂.rcx], fun k hk => ?_⟩
  rw [hat_byte hh hspan l₁ (by omega), hat_byte hh hspan l₂ (by omega)]
  simp only [Xb, pub_B hq hK]

/-- The loop of a half. -/
theorem hloop_ct {X : State → State → Prop} {K h off count : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) (n : Nat) :
    RelCT isa (HI X K h off count n) (.loop rnBody .ne) (R4 fun σ s => ∃ s₀, X σ s₀ ∧ HAt σ s₀ K h off count count s) := by
  refine RelCT.loop (M := isa) (HI X K h off count) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × State × Nat, sample4K.pre p.1 ∧ p.2.2 < count ∧
      HAt p.1 p.2.1 K h off count p.2.2 x →
        HAt p.1 p.2.1 K h off count (p.2.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (count - p.2.2) - 1 == 0))
    (RelCT.mono body_ct (fun x y H => hi_brel hK hh hspan H) fun _ _ _ => trivial) (fun x y H => ?_) ?_
  · obtain ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, _, _, ht, _, _, l₁, l₂⟩ := H
    exact ⟨WP.all' (fun p hp' => hat_step (pre_of hp'.1) hK hh hspan hp'.2.1 hp'.2.2) ⟨(σ₁, s₀₁, t), p₁, ht, l₁⟩,
      WP.all' (fun p hp' => hat_step (pre_of hp'.1) hK hh hspan hp'.2.1 hp'.2.2) ⟨(σ₂, s₀₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, hq, hn, ht, x₁, x₂, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, s₀₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, s₀₂, t) ⟨p₂, ht, l₂⟩
    have ez : (BitVec.ofNat 64 (count - t) - 1 == 0) = decide (t + 1 = count) := by
      rw [ofNat64_pred (by omega) (by omega), ofNat64_beq_zero (by omega)]
      exact decide_eq_decide.mpr (by omega)
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = count := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁'⟩, ⟨s₀₂, x₂, l₂'⟩⟩
    · have : t + 1 ≠ count := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨count - (t + 1), by omega, σ₁, σ₂, s₀₁, s₀₂, t + 1, p₁, p₂, hq, rfl, by omega, x₁, x₂, l₁', l₂'⟩

/-- A half of seed `K` from states with `X`, given the taint analysis of its setup. -/
theorem parse_ct {X : State → State → Prop} {K h off count : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) (hpos : 0 < count)
    (hX : ∀ σ s, sample4K.pre σ → X σ s → HPre σ K h off count s) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.setup K off count)) hc).isSome = true) :
    RelCT isa (R4 X) (parse K off count) (R4 fun σ s => ∃ s₀, X σ s₀ ∧ HAt σ s₀ K h off count count s) := by
  unfold VG.Impl.MlDsa.X86_64.Sample.Rej5.parse
  refine RelCT.seq (RelCT.mono (relInv (I' := fun σ s => ∃ s₀, X σ s₀ ∧ HAt σ s₀ K h off count 0 s)
      (fun σ s hp hx => WP.mono (setup_ok (pre_of hp) hK hspan (hX σ s hp hx)) fun _ h' => ⟨s, hx, h'⟩)
      (taintRel [.rbx, .r13] (fun x y ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ r hr => by
        have e₁ := (hX σ₁ x p₁ h₁).env
        have e₂ := (hX σ₂ y p₂ h₂).env
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact env_rbx hq e₁ e₂
        · rw [e₁.r13, e₂.r13, pub_aP hq]) c)) (fun _ _ h => h)
      (Q' := HI X K h off count count) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁⟩, ⟨s₀₂, x₂, l₂⟩⟩ =>
        ⟨σ₁, σ₂, s₀₁, s₀₂, 0, p₁, p₂, hq, rfl, hpos, x₁, x₂, l₁, l₂⟩) (hloop_ct hK hh hspan count)

theorem segment_ct {n off count K : Nat} (hn : n ≤ 3) (hK : K < 4)
    (hspan : off + count ≤ 168) (hpos : 0 < count) (hbuf : 3 * (off + count) ≤ 168 * n)
    {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13])
      (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.setup K off count)) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx])
      (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) h₂).isSome = true) :
    RelCT isa (R4 fun σ s => Batch σ n off count K s) (segment K off count)
      (R4 fun σ s => Batch σ n off count (K + 1) s) :=
  RelCT.seq (parse_ct hK (by decide) hspan hpos (fun _ _ _ h => hpre hK hbuf h) c₁)
    (relInv (fun σ s hp ⟨_, h₀, hA⟩ => segmentEnd_ok (pre_of hp) hn hK h₀ hA)
      (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, a₁⟩, ⟨_, _, a₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq a₁.env a₂.env) c₂))

end VG.Proof.MlDsa.X86_64.Rej4.Segment
