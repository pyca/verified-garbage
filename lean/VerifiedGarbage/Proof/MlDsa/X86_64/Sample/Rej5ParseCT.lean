module
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Batch

import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Batch
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (sample4K relInv taintRel relStart Rel2 ofNat64_pred ofNat64_beq_zero RelCT.postDep Keep WP.keep)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' pre_of pub_scr pub_aP pub_B env_rbx start_ct RX relInvX bsum bsum_congr)
open VG.Proof.MlDsa.X86_64.Sample (nil_regs WP.all')
open VG.Proof.MlDsa.X86_64.Sample.RejNttCT (BPre BRel body_ct)
open VG.Proof.MlKem (poly4)

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

/-! ## Groups of eight candidates -/

/-- Two runs at group `t` of a segment, with `r10 = c`, each from a state with `X`. -/
abbrev RG (X : State → State → Prop) (K h off count t : Nat) (c : BitVec 64) : State → State → Prop :=
  RX X fun σ s₀ s => GB σ s₀ K h off count t s ∧ s.gpr .r10 = c

/-- The mask of the candidates less than `q` of lane `l` of the bytes `g`. -/
abbrev maskG (g : Nat → Byte) (l : Nat) : Nat := bsum (fun i => decide (Vec.candG g (4 * l + i) < Spec.MlDsa.q)) 4

theorem maskL_eq {X : BitVec 256} {g : Nat → Byte} {l : Nat} (hc : Vec.CandOf X g l) : Vec.maskL X l = maskG g l :=
  bsum_congr fun i hi => by rw [hc i hi]

/-- The registers `vput` reads, after `vcand`, are the same in both runs. -/
theorem vi_regs {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {s₀₁ s₀₂ : State} {K h off count t : Nat} (hK : K < 4)
    (hh : h < 2) (hspan : off + count ≤ 168) (ht : t + 8 ≤ count) {x y : State}
    (h₁ : VI σ₁ s₀₁ K h off count t x) (h₂ : VI σ₂ s₀₂ K h off count t y) :
    ∀ r ∈ [Reg.rax, .rbp, .rdi, .rsi], x.gpr r = y.gpr r := by
  obtain ⟨u₁, l₁, -, a₁, -, -, -, -, -, -, g₁⟩ := h₁
  obtain ⟨u₂, l₂, -, a₂, -, -, -, -, -, -, g₂⟩ := h₂
  have c₁ := gb_cand hh hspan ht l₁
  have c₂ := gb_cand hh hspan ht l₂
  have ex : Xb σ₁ K = Xb σ₂ K := by unfold Xb; rw [pub_B hq hK]
  have eg : gOf σ₁ K h off t = gOf σ₂ K h off t := by unfold gOf; rw [ex]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    rw [a₁, a₂, maskL_eq (c₁ 0 (by decide)), maskL_eq (c₁ 1 (by decide)), maskL_eq (c₂ 0 (by decide)),
      maskL_eq (c₂ 1 (by decide)), eg]
  · rw [g₁ _ (by decide), g₂ _ (by decide), l₁.rbp, l₂.rbp, pub_aP hq]
  · rw [g₁ _ (by decide), g₂ _ (by decide), l₁.rdi, l₂.rdi, pub_Lt4 hq hK]
  · rw [g₁ _ (by decide), g₂ _ (by decide), l₁.rsi, l₂.rsi, at', at', pub_scr hq]

/-- The registers `vputB` reads, after `vputA`, are the same in both runs. -/
theorem vp_regs {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {s₀₁ s₀₂ : State} {K h off count t : Nat} (hK : K < 4)
    (hh : h < 2) (hspan : off + count ≤ 168) (ht : t + 8 ≤ count) {x y : State}
    (h₁ : VP σ₁ s₀₁ K h off count t x) (h₂ : VP σ₂ s₀₂ K h off count t y) :
    ∀ r ∈ [Reg.rax, .rbp, .rdi, .rsi], x.gpr r = y.gpr r := by
  obtain ⟨u₁, v₁, l₁, -, f₁, p₁⟩ := h₁
  obtain ⟨u₂, v₂, l₂, -, f₂, p₂⟩ := h₂
  have g₁ := f₁.2.2.2.2.2.2.2
  have g₂ := f₂.2.2.2.2.2.2.2
  have c₁ := gb_cand hh hspan ht l₁
  have c₂ := gb_cand hh hspan ht l₂
  have ex : Xb σ₁ K = Xb σ₂ K := by unfold Xb; rw [pub_B hq hK]
  have eg : gOf σ₁ K h off t = gOf σ₂ K h off t := by unfold gOf; rw [ex]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    rw [p₁.rax, p₂.rax, maskL_eq (c₁ 1 (by decide)), maskL_eq (c₂ 1 (by decide)), eg]
  · rw [p₁.gpr _ (by decide) (by decide) (by decide), p₂.gpr _ (by decide) (by decide) (by decide), g₁ _ (by decide),
      g₂ _ (by decide), l₁.rbp, l₂.rbp, pub_aP hq]
  · apply BitVec.eq_of_toNat_eq
    rw [p₁.rdi, p₂.rdi, g₁ _ (by decide), g₂ _ (by decide), l₁.rdi, l₂.rdi, Vec.cntL_eq (c₁ 0 (by decide)),
      Vec.cntL_eq (c₂ 0 (by decide)), eg, pub_Lt4 hq hK]
  · rw [p₁.gpr _ (by decide) (by decide) (by decide), p₂.gpr _ (by decide) (by decide) (by decide), g₁ _ (by decide),
      g₂ _ (by decide), l₁.rsi, l₂.rsi, at', at', pub_scr hq]

/-- Eight candidates with the vector code. -/
theorem vec_ct {X : State → State → Prop} {K h off count t : Nat} {c : BitVec 64} (hK : K < 4) (hh : h < 2)
    (hspan : off + count ≤ 168) (ht : t + 8 ≤ count) :
    RelCT isa (RX X fun σ s₀ s => GB σ s₀ K h off count t s ∧ (Lt σ K (168 * h + off + t)).length ≤ 248 ∧
      s.gpr .r10 = c) (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.vcand ++ (VG.Impl.MlDsa.X86_64.Sample.Rej5.vputA ++ VG.Impl.MlDsa.X86_64.Sample.Rej5.vputB))) (RG X K h off count (t + 8) c) :=
  RelCT.block_append (RelCT.seq
    (relInvX (I' := fun σ s₀ s => VI σ s₀ K h off count t s ∧ s.gpr .r10 = c)
      (fun σ s₀ s hp _ h' => WP.mono (vec1_ok (pre_of hp) hK hspan ht h'.1 h'.2.1) fun _ ⟨hi, h10⟩ =>
        ⟨hi, by rw [h10]; exact h'.2.2⟩)
      (taintRel [.rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rsi, h₂.1.rsi, at', at', pub_scr hq])
        (by taint_decide)))
    (RelCT.block_append (RelCT.seq
      (relInvX (I' := fun σ s₀ s => VP σ s₀ K h off count t s ∧ s.gpr .r10 = c)
        (fun σ s₀ s hp _ h' => WP.mono (vec2a_ok (pre_of hp) hK h'.1) fun _ ⟨hv, h10⟩ =>
          ⟨hv, by rw [h10]; exact h'.2⟩)
        (taintRel [.rax, .rbp, .rdi, .rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ =>
          vi_regs hq hK hh hspan ht h₁.1 h₂.1) (by taint_decide)))
      (relInvX (fun σ s₀ s hp _ h' => WP.mono (vec2b_ok (pre_of hp) hK hh hspan ht h'.1) fun _ ⟨l, h10⟩ =>
          ⟨l, by rw [h10]; exact h'.2⟩)
        (taintRel [.rax, .rbp, .rdi, .rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ =>
          vp_regs hq hK hh hspan ht h₁.1 h₂.1) (by taint_decide))))))

/-- The states after `mov ecx, 8` of a group with more than 248 coefficients. -/
def SX (X : State → State → Prop) (K h off count t : Nat) (c : BitVec 64) (σ s₁ : State) : Prop :=
  ∃ s₀ s, X σ s₀ ∧ GB σ s₀ K h off count t s ∧ 248 < (Lt σ K (168 * h + off + t)).length ∧ s.gpr .r10 = c ∧
    s₁.mem = s.mem ∧ Keep [.rcx] s s₁ ∧ s₁.gpr .rcx = BitVec.ofNat 64 8

/-- Eight candidates with the scalar loop. -/
theorem sca_ct {X : State → State → Prop} {K h off count t : Nat} {c : BitVec 64} (hK : K < 4) (hh : h < 2)
    (hspan : off + count ≤ 168) (ht : t + 8 ≤ count) :
    RelCT isa (RX X fun σ s₀ s => GB σ s₀ K h off count t s ∧ 248 < (Lt σ K (168 * h + off + t)).length ∧
      s.gpr .r10 = c) VG.Impl.MlDsa.X86_64.Sample.Rej5.sca8 (RG X K h off count (t + 8) c) := by
  have h₁ : RelCT isa (RX X fun σ s₀ s => GB σ s₀ K h off count t s ∧ 248 < (Lt σ K (168 * h + off + t)).length ∧
      s.gpr .r10 = c) (.block [.mov32 .rcx (.imm 8)]) (R4 (SX X K h off count t c)) :=
    relInv (fun σ s _ ⟨s₀, hx, hI, hl, h10⟩ => WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧
        s'.gpr .rcx = BitVec.ofNat 64 8) (by xrun) rfl) fun s₁ ⟨⟨hm, hc⟩, k⟩ => ⟨s₀, s, hx, hI, hl, h10, hm, k, hc⟩)
      (taintRel [] nil_regs (by taint_decide))
  have h₂ : RelCT isa (HI (SX X K h off count t c) K h (off + t) 8 8) (.loop rnBody .ne)
      (R4 fun σ s => ∃ s₀, SX X K h off count t c σ s₀ ∧ HAt σ s₀ K h (off + t) 8 8 s) :=
    hloop_ct hK hh (by omega) 8
  show RelCT isa _ (.seq (.block [.mov32 .rcx (.imm 8)]) (.loop rnBody .ne)) _
  refine RelCT.seq (RelCT.mono h₁ (fun _ _ h => h) fun x y hxy => ?_) (RelCT.mono h₂ (fun _ _ h => h) fun x y hxy => ?_)
  · obtain ⟨σ₁, σ₂, p₁, p₂, hq, x₁, x₂⟩ := hxy
    obtain ⟨_, _, _, l₁, _, _, m₁, k₁, c₁⟩ := id x₁
    obtain ⟨_, _, _, l₂, _, _, m₂, k₂, c₂⟩ := id x₂
    exact ⟨σ₁, σ₂, x, y, 0, p₁, p₂, hq, rfl, by decide, x₁, x₂, hat0_of ht l₁ m₁ k₁ c₁, hat0_of ht l₂ m₂ k₂ c₂⟩
  · obtain ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₁, x₁, a₁⟩, ⟨s₂, x₂, a₂⟩⟩ := hxy
    obtain ⟨s₀₁, u₁, y₁, l₁, d₁, r₁, m₁, k₁, -⟩ := x₁
    obtain ⟨s₀₂, u₂, y₂, l₂, d₂, r₂, m₂, k₂, -⟩ := x₂
    obtain ⟨g₁, e₁⟩ := gb_of_hat (pre_of p₁) hK hh hspan ht l₁ m₁ k₁ a₁ d₁
    obtain ⟨g₂, e₂⟩ := gb_of_hat (pre_of p₂) hK hh hspan ht l₂ m₂ k₂ a₂ d₂
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, y₁, g₁, by rw [e₁, r₁]⟩, ⟨s₀₂, y₂, g₂, by rw [e₂, r₂]⟩⟩

/-- A group of eight candidates. -/
theorem vgrp_ct {X : State → State → Prop} {K h off count t : Nat} {c : BitVec 64} (hK : K < 4) (hh : h < 2)
    (hspan : off + count ≤ 168) (ht : t + 8 ≤ count) :
    RelCT isa (RG X K h off count t c) VG.Impl.MlDsa.X86_64.Sample.Rej5.vgrp
      (RX X fun σ s₀ s => GB σ s₀ K h off count (t + 8) s ∧ s.gpr .r10 = c - 1 ∧ s.zf = some (c - 1 == 0)) := by
  have hcmp : RelCT isa (RG X K h off count t c) (.block [.alu .cmp .rdi (.imm 249)])
      (RX X fun σ s₀ s => (GB σ s₀ K h off count t s ∧ s.gpr .r10 = c) ∧
        s.cf = some (decide ((Lt σ K (168 * h + off + t)).length < 249))) :=
    relInvX (fun σ s₀ s _ _ h' => by
        have hlen := Lt_length_le σ K (168 * h + off + t)
        refine WP.mono_syms (cmp249_ok s) fun s' ⟨hcf, hm, hg, hrd, hwr, hl⟩ sy => ?_
        exact ⟨⟨h'.1.same hg hm hrd hwr sy hl, by rw [hg]; exact h'.2⟩,
          by rw [hcf, h'.1.rdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]⟩)
      (taintRel [.rdi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rdi, h₂.1.rdi, pub_Lt4 hq hK])
        (by taint_decide))
  have hite : RelCT isa (RX X fun σ s₀ s => (GB σ s₀ K h off count t s ∧ s.gpr .r10 = c) ∧
        s.cf = some (decide ((Lt σ K (168 * h + off + t)).length < 249)))
      (.ite .b (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.vcand ++ (VG.Impl.MlDsa.X86_64.Sample.Rej5.vputA ++ VG.Impl.MlDsa.X86_64.Sample.Rej5.vputB))) VG.Impl.MlDsa.X86_64.Sample.Rej5.sca8) (RG X K h off count (t + 8) c) := by
    refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => by
        show x.cf = y.cf; rw [h₁.2, h₂.2, pub_Lt4 hq hK]) ?_ ?_
    · refine RelCT.mono (vec_ct hK hh hspan ht) ?_ fun _ _ h => h
      rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, ⟨l₁, d₁⟩, f₁⟩, ⟨s₀₂, x₂, ⟨l₂, d₂⟩, f₂⟩⟩, hb⟩
      have hb₁ : (Lt σ₁ K (168 * h + off + t)).length < 249 := by
        have : x.cf = some true := hb
        rw [f₁] at this; simpa using this
      have hb₂ : (Lt σ₂ K (168 * h + off + t)).length < 249 := by rw [← pub_Lt4 hq hK]; exact hb₁
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, by omega, d₁⟩, ⟨s₀₂, x₂, l₂, by omega, d₂⟩⟩
    · refine RelCT.mono (sca_ct hK hh hspan ht) ?_ fun _ _ h => h
      rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, ⟨l₁, d₁⟩, f₁⟩, ⟨s₀₂, x₂, ⟨l₂, d₂⟩, f₂⟩⟩, hb⟩
      have hb₁ : ¬ (Lt σ₁ K (168 * h + off + t)).length < 249 := by
        have : x.cf = some false := hb
        rw [f₁] at this; simpa using this
      have hb₂ : ¬ (Lt σ₂ K (168 * h + off + t)).length < 249 := by rw [← pub_Lt4 hq hK]; exact hb₁
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, by omega, d₁⟩, ⟨s₀₂, x₂, l₂, by omega, d₂⟩⟩
  have hsub : RelCT isa (RG X K h off count (t + 8) c) (.block [.alu .sub .r10 (.imm 1)])
      (RX X fun σ s₀ s => GB σ s₀ K h off count (t + 8) s ∧ s.gpr .r10 = c - 1 ∧ s.zf = some (c - 1 == 0)) :=
    relInvX (fun σ s₀ s _ _ h' => WP.mono_syms (sub10_ok s) fun s' ⟨⟨hm, h10, hz, hl⟩, k⟩ sy =>
        ⟨⟨h'.1.env.keep hm k (by decide), by rw [k.gpr (by decide), h'.1.rsi], by rw [k.gpr (by decide), h'.1.rdi],
          by rw [k.gpr (by decide), h'.1.rbp], by rw [hm]; exact h'.1.out, by rw [hm]; exact h'.1.stored,
          by rw [hm]; exact h'.1.fr, (h'.1.kp.trans k).mono (by simp),
          fun hv => ⟨(h'.1.vec hv).1.same hl, by rw [k.gpr (by decide), sy]; exact (h'.1.vec hv).2⟩⟩,
          by rw [h10, h'.2], by rw [hz, h'.2]⟩)
      (taintRel [.r10] (fun x y ⟨σ₁, σ₂, _, _, _, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) (by taint_decide))
  exact RelCT.seq hcmp (RelCT.seq hite hsub)

/-- Two runs at group `i` of a loop of `N` groups, `n = N - i` from its end. -/
def LI (X : State → State → Prop) (K h off count N n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ i, n = N - i ∧ i < N ∧ RG X K h off count (8 * i) (BitVec.ofNat 64 (N - i)) s₁ s₂

theorem loop_ct {X : State → State → Prop} {K h off count : Nat} (hK : K < 4) (hh : h < 2)
    (hspan : off + count ≤ 168) (h8 : count % 8 = 0) (n : Nat) :
    RelCT isa (LI X K h off count (count / 8) n) (.loop VG.Impl.MlDsa.X86_64.Sample.Rej5.vgrp .ne)
      (RX X fun σ s₀ s => GB σ s₀ K h off count count s) := by
  refine RelCT.loop (M := isa) (LI X K h off count (count / 8)) (fun n => ?_) n
  refine RelCT.mono (P := fun s₁ s₂ => ∃ i, n = count / 8 - i ∧ i < count / 8 ∧
      RG X K h off count (8 * i) (BitVec.ofNat 64 (count / 8 - i)) s₁ s₂)
    (RelCT.exists_ fun i => ?_) (fun _ _ h => by unfold LI at h; exact h) fun _ _ h => h
  by_cases hi : i < count / 8 ∧ n = count / 8 - i
  · obtain ⟨hi, hn⟩ := hi
    refine RelCT.mono (P := RG X K h off count (8 * i) (BitVec.ofNat 64 (count / 8 - i)))
      (vgrp_ct hK hh hspan (by omega))
      (fun _ _ h => h.2.2) fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, d₁, z₁⟩, ⟨s₀₂, x₂, l₂, d₂, z₂⟩⟩ => ?_
    rw [ofNat64_pred (by omega) (by omega)] at d₁ d₂ z₁ z₂
    rw [ofNat64_beq_zero (by omega)] at z₁ z₂
    rw [show 8 * i + 8 = 8 * (i + 1) by omega] at l₁ l₂
    refine ⟨by show x.zf.map _ = y.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht => ?_⟩
    · have : count / 8 - i - 1 = 0 := by
        have : x.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [show 8 * (i + 1) = count by omega] at l₁ l₂
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁⟩, ⟨s₀₂, x₂, l₂⟩⟩
    · have : count / 8 - i - 1 ≠ 0 := by
        have : x.zf.map (!·) = some true := ht
        rw [z₁] at this; simpa using this
      exact ⟨count / 8 - (i + 1), by omega, i + 1, rfl, by omega, σ₁, σ₂, p₁, p₂, hq,
        ⟨s₀₁, x₁, l₁, by rw [d₁]; congr 1⟩, ⟨s₀₂, x₂, l₂, by rw [d₂]; congr 1⟩⟩
  · exact RelCT.of_false fun _ _ h => hi ⟨h.2.1, h.1⟩

/-- A segment of seed `K` from states with `X`, given the taint analysis of its setup. -/
theorem parse_ct {X : State → State → Prop} {K h off count : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (hpos : 0 < count) (h8 : count % 8 = 0)
    (hX : ∀ σ s, sample4K.pre σ → X σ s → HPre σ K h off count s) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.setup K off count)) hc).isSome = true) :
    RelCT isa (R4 X) (parse K off count) (R4 fun σ s => ∃ s₀, X σ s₀ ∧ GB σ s₀ K h off count count s) := by
  unfold VG.Impl.MlDsa.X86_64.Sample.Rej5.parse
  refine RelCT.seq (RelCT.mono (relInv (I' := fun σ s => ∃ s₀, X σ s₀ ∧ GB σ s₀ K h off count 0 s ∧
        s.gpr .r10 = BitVec.ofNat 64 (count / 8))
      (fun σ s hp hx => WP.mono (setup_ok (pre_of hp) hK hspan (hX σ s hp hx)) fun _ h' => ⟨s, hx, h'⟩)
      (taintRel [.rbx, .r13] (fun x y ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ r hr => by
        have e₁ := (hX σ₁ x p₁ h₁).env
        have e₂ := (hX σ₂ y p₂ h₂).env
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact env_rbx hq e₁ e₂
        · rw [e₁.r13, e₂.r13, pub_aP hq]) c)) (fun _ _ h => h)
      (Q' := LI X K h off count (count / 8) (count / 8)) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁⟩, ⟨s₀₂, x₂, l₂⟩⟩ =>
        ⟨0, by omega, by omega, σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁.1, by rw [l₁.2]; rfl⟩,
          ⟨s₀₂, x₂, l₂.1, by rw [l₂.2]; rfl⟩⟩)
    (RelCT.mono (loop_ct hK hh hspan h8 (count / 8)) (fun _ _ h => h) fun _ _ h => h)

theorem segment_ct {n off count K : Nat} (hn : n ≤ 3) (hK : K < 4)
    (hspan : off + count ≤ 168) (hpos : 0 < count) (h8 : count % 8 = 0) (hbuf : 3 * (off + count) ≤ 168 * n)
    {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13])
      (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.setup K off count)) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx])
      (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) h₂).isSome = true) :
    RelCT isa (R4 fun σ s => Batch σ n off count K s) (segment K off count)
      (R4 fun σ s => Batch σ n off count (K + 1) s) :=
  RelCT.seq (parse_ct hK (by decide) hspan hpos h8 (fun _ _ _ h => hpre hK hbuf h) c₁)
    (relInv (fun σ s hp ⟨_, h₀, hA⟩ => segmentEnd_ok (pre_of hp) hn hK h₀ hA)
      (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, a₁⟩, ⟨_, _, a₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq a₁.env a₂.env) c₂))

/-- The first 168 candidates of seed `K`, given the taint analysis of their setup and count's store. -/
theorem segment0_ct {K : Nat} (hK : K < 4) {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.setup K 0 168)) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) h₂).isSome =
      true) :
    RelCT isa (R4 fun σ s => P1 σ K s) (segment K 0 168) (R4 fun σ s => P1 σ (K + 1) s) :=
  RelCT.seq (parse_ct hK (by decide) (by decide) (by decide) (by decide) (fun _ _ _ h => hpre0 hK h) c₁)
    (relInv (fun σ s hp ⟨_, h₀, hA⟩ => segment0End_ok (pre_of hp) hK h₀ hA)
      (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, a₁⟩, ⟨_, _, a₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq a₁.env a₂.env) c₂))

end VG.Proof.MlDsa.X86_64.Rej4.Segment
