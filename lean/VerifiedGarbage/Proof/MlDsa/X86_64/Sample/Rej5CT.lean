module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlDsa.Sample.Hash
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Batch
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlDsa.Sample.Hash
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Batch
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! ### `MlDsa.X86_64.Sample.Rej5ParseCT`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (sample4K relInv taintRel relStart Rel2 ofNat64_pred ofNat64_beq_zero RelCT.postDep Keep WP.keep)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' pre_of pub_scr pub_aP pub_B env_rbx start_ct RX relInvX bsum bsum_congr)
open VG.Proof.MlDsa.X86_64.Sample (nil_regs WP.all')
open VG.Proof.MlDsa.X86_64.Sample.RejNttCT (BPre BRel body_ct)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (parse segment batch)

/-- Two runs at iteration `t` of a half of seed `K`, from states with `X`,
`n = count - t` iterations from its end. -/
def HI (X : State → State → Prop) (K h off count n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ s₀₁ s₀₂ t, sample4K.pre σ₁ ∧ sample4K.pre σ₂ ∧ sample4K.pub σ₁ σ₂ ∧ n = count - t ∧ t < count ∧
    X σ₁ s₀₁ ∧ X σ₂ s₀₂ ∧ HAt σ₁ s₀₁ K h off count t s₁ ∧ HAt σ₂ s₀₂ K h off count t s₂

theorem hbpre {σ : State} (hp : Pre σ) {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hspan : off + count ≤ 168) (ht : t < count) {s : State}
    (hI : HAt σ s₀ K h off count t s) : BPre s (Proof.MlKem.poly4 (aP σ) K) (Lt σ K (168 * h + off + t)) :=
  ⟨hI.rbp, hI.rdi, Lt_length_le σ K _, coeffsWr hp hK hI.env, hI.stored,
    by simpa using hat_regions hp hK hspan hI (j := 0) (by omega_using [ht]), hat_regions hp hK hspan hI (by omega_using [ht]),
    hat_regions hp hK hspan hI (by omega_using [ht])⟩

theorem hi_brel {X : State → State → Prop} {K h off count n : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) {s₁ s₂ : State}
    (H : HI X K h off count n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, hq, _, ht, _, _, l₁, l₂⟩ := H
  refine ⟨Proof.MlKem.poly4 (aP σ₁) K, Lt σ₁ K (168 * h + off + t), hbpre (pre_of p₁) hK hspan ht l₁,
    by rw [pub_aP hq, pub_Lt4 hq hK]; exact hbpre (pre_of p₂) hK hspan ht l₂,
    by rw [l₁.rsi, l₂.rsi, at', at', pub_scr hq], by rw [l₁.rcx, l₂.rcx], fun k hk => ?_⟩
  rw [hat_byte hh hspan l₁ (by omega_using [ht, hk]), hat_byte hh hspan l₂ (by omega_using [ht, hk])]
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
      rw [ofNat64_pred (by omega_using [ht]) (by omega_using [hspan]), ofNat64_beq_zero (by omega_using [hspan])]
      exact decide_eq_decide.mpr (by omega_using [ht])
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
      exact ⟨count - (t + 1), by omega_using [hn, ht], σ₁, σ₂, s₀₁, s₀₂, t + 1, p₁, p₂, hq, rfl, by omega_using [ht, this], x₁, x₂, l₁', l₂'⟩

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
    hloop_ct hK hh (by omega_using [hspan, ht]) 8
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
          by rw [hcf, h'.1.rdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hlen])]⟩)
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
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, by omega_using [hb₁], d₁⟩, ⟨s₀₂, x₂, l₂, by omega_using [hb₂], d₂⟩⟩
    · refine RelCT.mono (sca_ct hK hh hspan ht) ?_ fun _ _ h => h
      rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, ⟨l₁, d₁⟩, f₁⟩, ⟨s₀₂, x₂, ⟨l₂, d₂⟩, f₂⟩⟩, hb⟩
      have hb₁ : ¬ (Lt σ₁ K (168 * h + off + t)).length < 249 := by
        have : x.cf = some false := hb
        rw [f₁] at this; simpa using this
      have hb₂ : ¬ (Lt σ₂ K (168 * h + off + t)).length < 249 := by rw [← pub_Lt4 hq hK]; exact hb₁
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, by omega_using [hb₁], d₁⟩, ⟨s₀₂, x₂, l₂, by omega_using [hb₂], d₂⟩⟩
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
      (vgrp_ct hK hh hspan (by omega_using [hi]))
      (fun _ _ h => h.2.2) fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, d₁, z₁⟩, ⟨s₀₂, x₂, l₂, d₂, z₂⟩⟩ => ?_
    rw [ofNat64_pred (by omega_using [hi]) (by omega_using [hspan])] at d₁ d₂ z₁ z₂
    rw [ofNat64_beq_zero (by omega_using [hspan])] at z₁ z₂
    rw [show 8 * i + 8 = 8 * (i + 1) by omega_using []] at l₁ l₂
    refine ⟨by show x.zf.map _ = y.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht => ?_⟩
    · have : count / 8 - i - 1 = 0 := by
        have : x.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [show 8 * (i + 1) = count by omega_using [h8, hi, this]] at l₁ l₂
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁⟩, ⟨s₀₂, x₂, l₂⟩⟩
    · have : count / 8 - i - 1 ≠ 0 := by
        have : x.zf.map (!·) = some true := ht
        rw [z₁] at this; simpa using this
      exact ⟨count / 8 - (i + 1), by omega_using [hi, hn], i + 1, rfl, by omega_using [this], σ₁, σ₂, p₁, p₂, hq,
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
        ⟨0, by omega_using [], by omega_using [hpos, h8], σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁.1, by rw [l₁.2]; rfl⟩,
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

end

end

/-! ### `MlDsa.X86_64.Sample.Rej5Top`, which only this module used -/

section

/-! ### `MlDsa.X86_64.Sample.Rej5Flags`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlDsa (Zq G)
open VG.Proof.MlDsa (PolyIs)
open VG.Proof.MlKem (xofByte)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (segment batch)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (flags)

/-- A saturated rejection fold is unchanged by the sixth block. -/
theorem full_after_five (σ : State) (k : Nat) (h : (Lt σ k 280).length = 256) :
    Lt σ k 336 = Lt σ k 280 := by
  have e : G (B σ k) 1008 = G (B σ k) 840 ++ (G (B σ k) 1008).drop 840 := by
    rw [← VG.Proof.MlDsa.Sample.G_take (B σ k) (by decide : 840 ≤ 1008), List.take_append_drop]
  have hl : Lt σ k 280 = rnFold [] (G (B σ k) 840) := by
    simp only [Lt, show 3 * 280 = 840 by rfl]
    rw [VG.Proof.MlDsa.Sample.G_take _ (by decide)]
  rw [Lt_336, hl, e, VG.Proof.MlDsa.Sample.rnFold_append _ _ _ (by rw [G_length]),
    VG.Proof.MlDsa.Sample.rnFold_full (by rwa [hl] at h)]

def allFull (σ : State) (n : Nat) : Bool :=
  (List.range 4).all fun k => (Lt σ k n).length == 256

section
variable {σ : State} (hp : Pre σ)
include hp

theorem flags_ok {n : Nat} {s : State} (env : EnvK σ s)
    (j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k n).length) :
    WP isa (.block flags) s fun s' =>
      (s'.gpr .r14 = (if allFull σ n then 1 else 0) ∧ s'.mem = s.mem) ∧ Keep [.rax, .r14] s s' := by
  have hin : ∀ k < 4, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oJ + 8 * k)) 8 :=
    fun k hk => in_scr' hp env.rd env.wr (by simp only [oJ]; omega_using [hk])
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide)
  have h2 := hin 2 (by decide); have h3 := hin 3 (by decide)
  have j0 := j 0 (by decide); have j1 := j 1 (by decide)
  have j2 := j 2 (by decide); have j3 := j 3 (by decide)
  simp only [oJ, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 j0 j1 j2 j3
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  change WP isa (.block ([.mov32 .r14 (.imm 1),
    .mov .rax (.mem (at_ .rbx 4424)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4432)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4440)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4448)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)])) s _
  xrun [env.rbx, h0, h1, h2, h3, j0, j1, j2, j3]
  simp only [full_bit (Lt_length_le σ _ _)]
  unfold allFull
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and]
  cases (Lt σ 0 n).length == 256 <;> cases (Lt σ 1 n).length == 256 <;>
    cases (Lt σ 2 n).length == 256 <;> cases (Lt σ 3 n).length == 256 <;> rfl

end
end VG.Proof.MlDsa.X86_64.Rej4.Segment

end

end


@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlDsa (Zq G)
open VG.Proof.MlDsa (PolyIs)
open VG.Proof.MlKem (xofByte)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (flags fallback finish)

structure Done (σ s : State) : Prop where
  env : EnvK σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ 4)
  st : ∀ k < 4, Stored s.mem (Proof.MlKem.poly4 (aP σ) k) (Lt σ k 336)

theorem Batch.restore {σ s s' : State} {n off count K : Nat} (h : Batch σ n off count K s)
    (hm : s'.mem = s.mem) (hk : Keep [.rax, .r14] s s') (hr : s'.gpr .r14 = 1) : Batch σ n off count K s' :=
  ⟨⟨h.sq.env.keep hm hk (by simp), hr, by rw [hm]; exact h.sq.rc,
    by rw [hm]; exact h.sq.lanes, by rw [hm]; exact h.sq.buf⟩,
    by rw [hm]; exact h.j, by rw [hm]; exact h.st⟩

section
variable {σ : State} (hp : Pre σ)
include hp

/-- The return value, and the callee-saved registers restored. -/
theorem end_ok {s : State} (h : Done σ s) :
    WP isa (.block epi) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega_using [hi])
  rw [epi_eq]
  refine WP.mono (WP.keep [.rax, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      (s'.gpr .rax).setWidth 32 = (s.gpr .r14).setWidth 32 ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, hax, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨⟨?_, fun k hk e => ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, okN]
    simp only [Lt_336]
    split <;> rfl
  · rw [hm]
    have := h.st k hk
    rw [Lt_336] at this
    exact stored_polyIs this e
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega_using [])⟩)
      (by decide)


/-- Clear upper vector lanes before restoring the caller's registers. -/
theorem end_vec_ok {s : State} (h : Done σ s) :
    WP isa (.block (([.vop .vzeroupper] : List Instr) ++ epi)) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  apply WP.block_append
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s.mem) (by xrun; rfl) rfl) fun s' ⟨hm, hk⟩ => ?_
  exact end_ok hp ⟨h.env.keep hm hk (by simp), by rw [hk.gpr (by simp)]; exact h.r14,
    by rw [hm]; exact h.st⟩

theorem last_flags_ok {s : State} (h : Batch σ 3 112 56 4 s) : WP isa (.block flags) s (Done σ) := by
  have hj : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 336).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  refine WP.mono (flags_ok hp h.sq.env hj) fun s' ⟨⟨hr, hm⟩, hk⟩ =>
    ⟨h.sq.env.keep hm hk (by simp), ?_, fun k hk' => ?_⟩
  · rw [hr]; unfold allFull okN; split <;> rfl
  · rw [hm]; simpa only [ite_eq_left hk'] using h.st k hk'

theorem fallback_ok {fast : Bool} {s s₀ : State} (h : Batch σ 2 0 112 4 s₀)
    (hm : s.mem = s₀.mem) (hk : Keep [.rax, .r14] s₀ s) : WP isa (fallback fast) s (Done σ) := by
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = 1)
    (by xrun) (by decide)) fun s' ⟨⟨hm', hr⟩, hk'⟩ => ?_)
  have hb := h.restore (hm'.trans hm) ((hk.trans hk').mono (by simp)) hr
  exact WP.seq (WP.mono (squeeze_last_ok (fast := fast) hp hb) fun _ h₁ =>
    WP.seq (WP.mono (batch_ok hp (by decide) (by decide) (by decide) (by decide) (by decide) h₁)
      fun _ h₂ => last_flags_ok hp h₂))

omit hp in
theorem early_done {s s₀ : State} (h : Batch σ 2 0 112 4 s₀)
    (hm : s.mem = s₀.mem) (hk : Keep [.rax, .r14] s₀ s)
    (hr : s.gpr .r14 = 1) (hf : allFull σ 280 = true) : Done σ s := by
  have hfull : ∀ k < 4, (Lt σ k 280).length = 256 := by
    simpa only [allFull, List.all_eq_true, List.mem_range, beq_iff_eq] using hf
  have he : ∀ k < 4, Lt σ k 336 = Lt σ k 280 := fun k hk => full_after_five σ k (hfull k hk)
  refine ⟨h.sq.env.keep hm hk (by simp), ?_, fun k hk' => ?_⟩
  · have hf' : (List.range 4).all (fun k => (Lt σ k 336).length == 256) = true := by
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
      intro k hk; rw [he k hk]; exact hfull k hk
    rw [hr, okN, hf']; rfl
  · rw [hm, he k hk']; simpa only [ite_eq_left hk'] using h.st k hk'

theorem finish_ok {fast : Bool} {s : State} (h : Batch σ 2 0 112 4 s) :
    WP isa (finish fast) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hj : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 280).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  apply WP.seq
  apply WP.block_append
  refine WP.mono (flags_ok hp h.sq.env hj) fun s₁ ⟨⟨hr, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.r14] (Q := fun s₂ => s₂.mem = s₁.mem ∧ s₂.gpr .r14 = s₁.gpr .r14 ∧
    s₂.zf = some ((s₁.gpr .r14).setWidth 32 == 0)) (by xrun; simp) (by decide))
    fun s₂ ⟨⟨hm', hr', hz⟩, hk'⟩ => ?_
  apply WP.seq
  apply WP.mono (Q := Done σ) ?_ (fun _ hd => end_vec_ok hp hd)
  have hkeep : Keep [.rax, .r14] s s₂ := (hk.trans hk').mono (by simp)
  cases hf : allFull σ 280 with
  | false =>
    have hz' : s₂.zf = some true := by rw [hz, hr, hf]; rfl
    exact WP.ite true hz' (fun _ => fallback_ok (fast := fast) hp h (hm'.trans hm) hkeep)
      (fun hb => absurd hb (by decide))
  | true =>
    have hz' : s₂.zf = some false := by rw [hz, hr, hf]; rfl
    refine WP.ite false hz' (fun hb => absurd hb (by decide)) (fun _ => WP.block_nil ?_)
    exact early_done h (hm'.trans hm) hkeep (by rw [hr', hr, hf]; rfl) hf

/-- Everything after the prologue, the round constants and the padded seeds. -/
theorem body_ok {fast : Bool} {s : State} (h : SqInv σ 0 s) :
    WP isa (.seq (squeezes 0 3 fast) (.seq (.block zeroJ)
      (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.segment 0 0 168) (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.segment 1 0 168)
        (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.segment 2 0 168) (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.segment 3 0 168)
        (.seq (squeezes 0 2 fast) (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.batch 0 112) (finish fast))))))))) s
      fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (sqTs_ok (fast := fast) hp (by decide) (by decide) (sqT_of h)) fun s₃ ⟨q₃, _⟩ =>
      WP.seq (WP.mono (zeroJ_ok hp q₃) fun s₄ p₀ => ?_))
  refine WP.seq (WP.mono (segment0_ok hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (segment0_ok hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (segment0_ok hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (segment0_ok hp (by decide) p₃) fun _ p₄ => ?_))))
  exact WP.seq (WP.mono (sqM_ok (fast := fast) hp (by decide) (by decide) (m2_of p₄)) fun _ m₂ =>
      WP.seq (WP.mono (batch_ok hp (by decide) (by decide) (by decide) (by decide) (by decide) (batch_of_m2 m₂))
        fun _ b => finish_ok (fast := fast) hp b))

end
theorem correct {fast : Bool} (σ : State) (hs : r4K.pre σ) :
    ∃ t s', Exec isa (VG.Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 fast) σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s' := by
  have hp := pre_of (by dsimp only [r4K] at hs; exact hs)
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (start_ok hp) fun _ h => body_ok (fast := fast) hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by cases fast <;> decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Rej4.Segment

end

end

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (sample4K relInv taintRel relStart Rel2 ofNat64_pred ofNat64_beq_zero RelCT.postDep)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' pre_of pub_scr pub_aP pub_B env_rbx start_ct)
open VG.Proof.MlDsa.X86_64.Sample (nil_regs WP.all')
open VG.Proof.MlDsa.X86_64.Sample.RejNttCT (BPre BRel body_ct)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (batch flags fallback finish)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem batch2_ct : RelCT isa (R4 fun σ s => Batch σ 2 0 112 0 s)
    (batch 0 112) (R4 fun σ s => Batch σ 2 0 112 4 s) := by
  refine RelCT.seq (segment_ct (K := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  exact (segment_ct (K := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))

theorem batch3_ct : RelCT isa (R4 fun σ s => Batch σ 3 112 56 0 s)
    (batch 112 56) (R4 fun σ s => Batch σ 3 112 56 4 s) := by
  refine RelCT.seq (segment_ct (K := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  exact (segment_ct (K := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))

structure Checked (σ s : State) : Prop where
  prior : ∃ start, Batch σ 2 0 112 4 start ∧ s.mem = start.mem ∧ Keep [.rax, .r14] start s
  r14 : s.gpr .r14 = if allFull σ 280 then 1 else 0
  zf : s.zf = some (!allFull σ 280)

theorem check_ok {σ s : State} (hp : Pre σ) (h : Batch σ 2 0 112 4 s) :
    WP isa (.block (flags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) s (Checked σ) := by
  have hj : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 280).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  apply WP.block_append
  refine WP.mono (flags_ok hp h.sq.env hj) fun s₁ ⟨⟨hr, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.r14] (Q := fun s₂ => s₂.mem = s₁.mem ∧ s₂.gpr .r14 = s₁.gpr .r14 ∧
    s₂.zf = some ((s₁.gpr .r14).setWidth 32 == 0)) (by xrun; simp) (by decide))
    fun s₂ ⟨⟨hm', hr', hz⟩, hk'⟩ => ?_
  refine ⟨⟨s, h, hm'.trans hm, (hk.trans hk').mono (by simp)⟩, hr'.trans hr, ?_⟩
  rw [hz, hr]; cases allFull σ 280 <;> rfl

theorem check_ct : RelCT isa (R4 fun σ s => Batch σ 2 0 112 4 s)
    (.block (flags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) (R4 Checked) :=
  relInv (fun σ s hp h => check_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem reset_ok {σ s : State} (h : Checked σ s) :
    WP isa (.block [.mov32 .r14 (.imm 1)]) s (Batch σ 2 0 112 4) := by
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = 1)
    (by xrun) (by decide)) fun s' ⟨⟨hm, hr⟩, hk⟩ => ?_
  obtain ⟨_, hb, hm₀, hk₀⟩ := h.prior
  exact hb.restore (hm.trans hm₀) ((hk₀.trans hk).mono (by simp)) hr

theorem fallback_ct {fast : Bool} : RelCT isa (R4 Checked) (fallback fast) (R4 Done) := by
  have c : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezes 2 1 fast) hc).isSome = true := by
    cases fast <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, c⟩ := c
  refine RelCT.seq (relInv (fun σ s _ h => reset_ok h) (taintRel [] nil_regs (by taint_decide))) ?_
  refine RelCT.seq (relInv (fun σ s hp h => squeeze_last_ok (fast := fast) (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) c)) ?_
  refine RelCT.seq batch3_ct ?_
  exact relInv (fun σ s hp h => last_flags_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem pub_allFull {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) (n : Nat) :
    allFull σ₁ n = allFull σ₂ n := by
  simp only [allFull, List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.true_and]
  rw [pub_Lt4 hq (K := 0) (by decide), pub_Lt4 hq (K := 1) (by decide),
    pub_Lt4 hq (K := 2) (by decide), pub_Lt4 hq (K := 3) (by decide)]


theorem branch_ct {fast : Bool} : RelCT isa (R4 Checked) (.ite .e (fallback fast) (.block [])) (R4 Done) := by
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
    show x.zf = y.zf; rw [h₁.zf, h₂.zf, pub_allFull hq])
    (RelCT.mono (fallback_ct (fast := fast)) (fun _ _ h => h.1) (fun _ _ h => h)) ?_
  have empty : RelCT isa (R4 fun σ s => Checked σ s ∧ allFull σ 280 = true) (.block []) (R4 Done) :=
    relInv (fun σ s _ ⟨h, hf⟩ => by
      obtain ⟨_, hb, hm, hk⟩ := h.prior
      exact WP.block_nil (early_done hb hm hk (by rw [h.r14, hf]; rfl) hf))
      (taintRel [] nil_regs (by taint_decide))
  refine RelCT.mono empty (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_) (fun _ _ h => h)
  have hz : x.zf = some false := hb
  have hf : allFull σ₁ 280 = true := by rw [h₁.zf] at hz; simpa using hz
  exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hf⟩, ⟨h₂, by rw [← pub_allFull hq]; exact hf⟩⟩

theorem finish_ct {fast : Bool} : RelCT isa (R4 fun σ s => Batch σ 2 0 112 4 s) (finish fast) (fun _ _ => True) :=
  RelCT.seq check_ct (RelCT.seq (branch_ct (fast := fast))
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)))

theorem ct {fast : Bool} : ConstantTime isa r4K.pre r4K.pub (VG.Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 fast) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (start_ct (w16 := false)) (RelCT.seq (RelCT.mono
    (sqT_ct (fast := fast) (t := 0) (by decide) (by decide) (by cases fast <;> exact ⟨_, by taint_decide⟩))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, sqT_of h₁, sqT_of h₂⟩) fun _ _ h => h) ?_))
  refine RelCT.seq (relInv (fun σ s hp h => zeroJ_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide))) ?_
  refine RelCT.seq (segment0_ct (K := 0) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment0_ct (K := 1) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment0_ct (K := 2) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment0_ct (K := 3) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (RelCT.mono (sqM_ct (fast := fast) (by decide) (by decide) (by cases fast <;> exact ⟨_, by taint_decide⟩))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, m2_of h₁, m2_of h₂⟩) fun _ _ h => h) ?_
  exact RelCT.seq (RelCT.mono batch2_ct
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, batch_of_m2 h₁, batch_of_m2 h₂⟩) (fun _ _ h => h)) finish_ct

end VG.Proof.MlDsa.X86_64.Rej4.Segment
