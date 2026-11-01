module

import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
public import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Loop
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Run
meta import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.MlKem.X86_64.FragCall
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.MlKem.X86_64.Frag
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragCall
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Loop
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Run
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, constant time but for the seeds

Two runs whose seeds (the declared leak) and pointers agree leak the same. The
code but for the loops of the runs and the check of the counts is proven by
the taint analysis, from the pointers. Both runs read the same XOF output, so
in the loops they are at the same iteration with the same coefficients
sampled: each group of eight iterations takes the same branch (on `j < 241`,
`vgrp_ct`); the vector code computes the same mask of the candidates in `eax`
(`VIW.rax`), so it loads the same entry of the table, stores to the same
address and counts the same (the taint analysis, from `rax`, `rbx`, `rbp`,
`rdi` and `rsi`), and `vg_mlkem_sample_ntt`'s loop runs as in that function
(`body_ct`). The check of the counts gives both runs the same flags, so they
both squeeze the two more blocks and run the 112 more iterations, or neither
does (`branch_ct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Two runs related by `I`, from entry states that agree on what is public. -/
abbrev R4W (w16 : Bool) (I : State → State → Prop) : State → State → Prop := Rel2 (sample4KW w16).pre (sample4KW w16).pub I

/-- `R4W` with 32-bit coefficients. -/
abbrev R4 := R4W false

section
variable {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂)
include hq

theorem pub_scr : scr σ₁ = scr σ₂ := hq.2.2.1
theorem pub_aP : aP σ₁ = aP σ₂ := hq.2.1
theorem pub_sd : sd σ₁ = sd σ₂ := hq.1
theorem pub_sp : σ₁.gpr .rsp = σ₂.gpr .rsp := hq.2.2.2.1

theorem pub_B {k : Nat} (hk : k < 4) : B σ₁ k = B σ₂ k := by
  have e := hq.2.2.2.2
  simp only [B, seed4, sd, bytesAt] at e ⊢
  rw [← hq.1] at e ⊢
  apply List.ext_getElem (by simp)
  intro i h₁ _
  have := congrArg (fun L => L[34 * k + i]?) e
  simp only [List.getElem?_map, List.getElem?_range (show 34 * k + i < 136 by simp at h₁; omega),
    Option.map_some, Option.some.injEq] at this
  simp only [List.getElem_map, List.getElem_range, Offset.add_add]
  exact this

end

theorem start_ct : RelCT isa (R4W w16 fun σ s => s = σ)
    (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4)) (R4W w16 fun σ s => SqInvW w16 σ 0 s) :=
  relInv (fun σ s hp h => by subst h; exact start_ok (preW_of hp))
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))


theorem env_rbx {σ₁ σ₂ s₁ s₂ : State} (hq : sample4K.pub σ₁ σ₂) (e₁ : EnvW w16 σ₁ s₁) (e₂ : EnvW w16 σ₂ s₂) :
    s₁.gpr .rbx = s₂.gpr .rbx := by rw [e₁.rbx, e₂.rbx, pub_scr hq]

/-- Squeezes, after `t` blocks, given their taint analysis. -/
theorem sqT_ct {fast : Bool} {t b n : Nat} (hn : 0 < n) (hbn : b + n ≤ 3) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezes b n fast) hc).isSome = true) :
    RelCT isa (R4W w16 fun σ s => SqTW w16 σ t b s) (squeezes b n fast) (R4W w16 fun σ s => SqTW w16 σ t (b + n) s) :=
  relInv (fun σ s hp h => WP.mono (sqTs_ok (fast := fast) (preW_of hp) hn hbn h) fun _ h' => h'.1)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) c)

/-- The first squeezes. -/
theorem sq_ct {fast : Bool} :
    RelCT isa (R4W w16 fun σ s => SqInvW w16 σ 0 s) (squeezes 0 3 fast) (R4W w16 fun σ s => SqTW w16 σ 0 3 s) := by
  have h : RelCT isa (R4W w16 fun σ s => SqTW w16 σ 0 0 s) (squeezes 0 3 fast) (R4W w16 fun σ s => SqTW w16 σ 0 (0 + 3) s) := by
    cases fast
    · exact sqT_ct (by decide) (by decide) (by taint_decide)
    · exact sqT_ct (by decide) (by decide) (by taint_decide)
  exact RelCT.mono h (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, sqT_of h₁, sqT_of h₂⟩)
    fun _ _ h => h

/-! ## The groups of eight iterations -/

theorem pub_Lt {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {K : Nat} (hK : K < 4) (t : Nat) :
    Lt σ₁ K t = Lt σ₂ K t := by simp only [Lt, pub_B hq hK]

/-- Two runs related by `I`, each from a state with `X`. -/
abbrev RXW (w16 : Bool) (X : State → State → Prop) (I : State → State → State → Prop) : State → State → Prop :=
  R4W w16 fun σ s => ∃ s₀, X σ s₀ ∧ I σ s₀ s

/-- `RXW` with 32-bit coefficients. -/
abbrev RX := RXW false

theorem relInvX {X : State → State → Prop} {I I' : State → State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s₀ s, (sample4KW w16).pre σ → X σ s₀ → I σ s₀ s → WP isa c s (I' σ s₀))
    (ht : RelCT isa (RXW w16 X I) c fun _ _ => True) : RelCT isa (RXW w16 X I) c (RXW w16 X I') :=
  relInv (fun σ s hp ⟨s₀, hx, hi⟩ => WP.mono (hw σ s₀ s hp hx hi) fun _ h' => ⟨s₀, hx, h'⟩) ht

theorem bpre {σ : State} (hp : (sample4KW w16).pre σ) {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t < 168) {s : State}
    (h : LAtW w16 σ s₀ K b t s) : BPre w16 s (poly4W w16 (aP σ) K) (Lt σ K (b + t)) := by
  have hp' := preW_of hp
  refine ⟨h.rbp, h.rdi, sampleAfter_length_le (a := []) (by simp) _ (b + t), fun j hj => ?_, h.stored,
    by simpa using lat_regions hp' hK h (j := 0) (by bdd_omega), lat_regions hp' hK h (by bdd_omega),
    lat_regions hp' hK h (by bdd_omega)⟩
  rw [h.lb.env.wr, hp'.wr]
  refine ⟨aRW w16 σ, by simp, ?_⟩
  rw [cAddr, poly4W, Offset.add_add]
  exact Offset.contains_base _ (by wd_omega) (by wd_omega)

/-- Two runs at iteration `b + t + u` of the scalar group from iteration `b + t`, from states with `X`,
`n = 4 - u` iterations from its end. -/
def GIW (w16 : Bool) (X : State → State → Prop) (K b t : Nat) (c : BitVec 64) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ s₀₁ s₀₂ u, (sample4KW w16).pre σ₁ ∧ (sample4KW w16).pre σ₂ ∧ (sample4KW w16).pub σ₁ σ₂ ∧ n = 8 - u ∧ u < 8 ∧
    X σ₁ s₀₁ ∧ X σ₂ s₀₂ ∧ LAtW w16 σ₁ s₀₁ K b (t + u) s₁ ∧ LAtW w16 σ₂ s₀₂ K b (t + u) s₂ ∧
    s₁.gpr .rcx = BitVec.ofNat 64 (8 - u) ∧ s₂.gpr .rcx = BitVec.ofNat 64 (8 - u) ∧ s₁.gpr .r10 = c ∧
    s₂.gpr .r10 = c ∧ (w16 = true → ¬ (Lt σ₁ K (b + t)).length < 241) ∧
    (w16 = true → ¬ (Lt σ₂ K (b + t)).length < 241)

/-- `GIW` with 32-bit coefficients. -/
abbrev GI := GIW false

theorem gi_brel {X : State → State → Prop} {K b t : Nat} {c : BitVec 64} {n : Nat} (hK : K < 4) (ht : t + 8 ≤ 168)
    (hbt : b + t + 8 ≤ 280) {s₁ s₂ : State} (h : GIW w16 X K b t c n s₁ s₂) : BRel w16 s₁ s₂ := by
  obtain ⟨σ₁, σ₂, s₀₁, s₀₂, u, p₁, p₂, hq, _, hu, _, _, l₁, l₂, c₁, c₂, -⟩ := h
  refine ⟨poly4W w16 (aP σ₁) K, Lt σ₁ K (b + (t + u)), bpre p₁ hK (by bdd_omega) l₁,
    by rw [pub_aP hq, pub_Lt hq hK]; exact bpre p₂ hK (by bdd_omega) l₂,
    by rw [l₁.rsi, l₂.rsi, at', at', pub_scr hq], by rw [c₁, c₂], fun k hk => ?_⟩
  rw [out_byte l₁ (by bdd_omega) (by bdd_omega), out_byte l₂ (by bdd_omega) (by bdd_omega), pub_B hq hK]

/-- The eight iterations of `vg_mlkem_sample_ntt`'s loop. -/
theorem iloop_ct {X : State → State → Prop} {K b t : Nat} {c : BitVec 64} (hK : K < 4) (ht : t + 8 ≤ 168)
    (hbt : b + t + 8 ≤ 280) (n : Nat) :
    RelCT isa (GIW w16 X K b t c n) (.loop (snBody w16) .ne)
      (RXW w16 X fun σ s₀ s => LAtW w16 σ s₀ K b (t + 8) s ∧ s.gpr .r10 = c ∧
        (w16 = true → ¬ (Lt σ K (b + t)).length < 241)) := by
  refine RelCT.loop (M := isa) (GIW w16 X K b t c) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × State × Nat, (sample4KW w16).pre p.1 ∧ p.2.2 < 8 ∧
      LAtW w16 p.1 p.2.1 K b (t + p.2.2) x → (LAtW w16 p.1 p.2.1 K b (t + p.2.2 + 1) x' ∧ x'.gpr .rcx = x.gpr .rcx - 1 ∧
        x'.zf = some (x.gpr .rcx - 1 == 0)) ∧ x'.gpr .r10 = x.gpr .r10)
    (RelCT.mono (body_ct w16) (fun x y h => gi_brel hK ht hbt h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, s₀₁, s₀₂, u, p₁, p₂, _, _, hu, _, _, l₁, l₂, _⟩ := h
    exact ⟨WP.all (fun p hp' => WP.gpr (lat_step (preW_of hp'.1) hK (by bdd_omega) (by bdd_omega) hp'.2.2)
        (r := .r10) (by cases w16 <;> decide)) ⟨(σ₁, s₀₁, u), p₁, hu, l₁⟩,
      WP.all (fun p hp' => WP.gpr (lat_step (preW_of hp'.1) hK (by bdd_omega) (by bdd_omega) hp'.2.2)
        (r := .r10) (by cases w16 <;> decide)) ⟨(σ₂, s₀₂, u), p₂, hu, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, s₀₁, s₀₂, u, p₁, p₂, hq, hn, hu, x₁, x₂, l₁, l₂, c₁, c₂, d₁, d₂, v₁, v₂⟩ f₁ f₂
    obtain ⟨⟨l₁', r₁, z₁⟩, e₁⟩ := f₁ (σ₁, s₀₁, u) ⟨p₁, hu, l₁⟩
    obtain ⟨⟨l₂', r₂, z₂⟩, e₂⟩ := f₂ (σ₂, s₀₂, u) ⟨p₂, hu, l₂⟩
    rw [c₁, SampleNtt.zf_last (by decide) hu] at z₁
    rw [c₂, SampleNtt.zf_last (by decide) hu] at z₂
    rw [c₁, ofNat64_pred (by bdd_omega) (by bdd_omega)] at r₁
    rw [c₂, ofNat64_pred (by bdd_omega) (by bdd_omega)] at r₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : u + 1 = 8 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [Nat.add_assoc, this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁', by rw [e₁, d₁], v₁⟩, ⟨s₀₂, x₂, l₂', by rw [e₂, d₂], v₂⟩⟩
    · have : u + 1 ≠ 8 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨8 - (u + 1), by bdd_omega, σ₁, σ₂, s₀₁, s₀₂, u + 1, p₁, p₂, hq, rfl, by bdd_omega, x₁, x₂,
        by rw [← Nat.add_assoc]; exact l₁', by rw [← Nat.add_assoc]; exact l₂', by rw [r₁]; congr 1,
        by rw [r₂]; congr 1, by rw [e₁, d₁], by rw [e₂, d₂], v₁, v₂⟩

/-- The relation of two runs at a group: iteration `b + t`, the constants in place for 16-bit
coefficients while there are fewer than 241, and `r10 = c`. -/
abbrev RVW (w16 : Bool) (X : State → State → Prop) (K b t : Nat) (c : BitVec 64) : State → State → Prop :=
  RXW w16 X fun σ s₀ s => LVW w16 σ s₀ K b t s ∧ s.gpr .r10 = c

/-- `RVW` with 32-bit coefficients. -/
abbrev RV := RVW false

theorem cmpG_ok {σ s₀ : State} {K b t : Nat} {c : BitVec 64} {s : State} (h : LVW w16 σ s₀ K b t s ∧ s.gpr .r10 = c) :
    WP isa (.block [.alu .cmp .rdi (.imm 241)]) s fun s' => (LVW w16 σ s₀ K b t s' ∧ s'.gpr .r10 = c) ∧
      s'.cf = some (decide ((Lt σ K (b + t)).length < 241)) := by
  have hlen : (Lt σ K (b + t)).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ (b + t)
  refine WP.mono_syms (cmp241_ok s) fun s' ⟨hcf, hm, hg, hrd, hwr, hl⟩ sy => ?_
  exact ⟨⟨⟨h.1.lat.same hg hm hrd hwr sy, fun hw h' => (h.1.vc hw h').same hl⟩, by rw [hg]; exact h.2⟩,
    by rw [hcf, h.1.lat.rdi, ofNat64_toNat (by bdd_omega)]⟩

/-- Eight iterations of `vg_mlkem_sample_ntt`'s loop. -/
theorem sca_ct {X : State → State → Prop} {K b t : Nat} {c : BitVec 64} (hK : K < 4) (ht : t + 8 ≤ 168)
    (hbt : b + t + 8 ≤ 280) :
    RelCT isa (RXW w16 X fun σ s₀ s => LAtW w16 σ s₀ K b t s ∧ (w16 = true → ¬ (Lt σ K (b + t)).length < 241) ∧
      s.gpr .r10 = c) (sca8 w16) (RVW w16 X K b (t + 8) c) := by
  refine RelCT.seq (relInvX (I' := fun σ s₀ s => (LAtW w16 σ s₀ K b t s ∧
      (w16 = true → ¬ (Lt σ K (b + t)).length < 241) ∧ s.gpr .r10 = c) ∧ s.gpr .rcx = BitVec.ofNat 64 8) ?_ ?_) ?_
  · intro σ s₀ s _ _ h
    refine WP.mono_syms (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 8)
      (by xrun) (by decide)) fun s' ⟨⟨hm, hc⟩, k⟩ sy => ?_
    exact ⟨⟨h.1.same' hm k sy, h.2.1, by rw [k.gpr (by decide)]; exact h.2.2⟩, hc⟩
  · exact taintRel [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)
  · refine RelCT.mono (iloop_ct (X := X) (c := c) hK ht hbt 8) ?_ ?_
    · rintro x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, ⟨l₁, v₁, d₁⟩, c₁⟩, ⟨s₀₂, x₂, ⟨l₂, v₂, d₂⟩, c₂⟩⟩
      exact ⟨σ₁, σ₂, s₀₁, s₀₂, 0, p₁, p₂, hq, rfl, by decide, x₁, x₂, l₁, l₂, c₁, c₂, d₁, d₂, v₁, v₂⟩
    · rintro x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, d₁, v₁⟩, ⟨s₀₂, x₂, l₂, d₂, v₂⟩⟩
      exact ⟨σ₁, σ₂, p₁, p₂, hq,
        ⟨s₀₁, x₁, ⟨l₁, fun hw h' => absurd (Nat.lt_of_le_of_lt (Lt_mono σ₁ K (b + t) 8) (by rwa [Nat.add_assoc])) (v₁ hw)⟩, d₁⟩,
        ⟨s₀₂, x₂, ⟨l₂, fun hw h' => absurd (Nat.lt_of_le_of_lt (Lt_mono σ₂ K (b + t) 8) (by rwa [Nat.add_assoc])) (v₂ hw)⟩, d₂⟩⟩

/-- Eight iterations with `snBody` while there are fewer than 256 coefficients,
and otherwise only `rsi` moved past their 24 bytes: `j` is the same in both
runs, and so is the branch. -/
theorem scaG_ct {X : State → State → Prop} {K b t : Nat} {c : BitVec 64} (hK : K < 4) (ht : t + 8 ≤ 168)
    (hbt : b + t + 8 ≤ 280) :
    RelCT isa (RXW w16 X fun σ s₀ s => LAtW w16 σ s₀ K b t s ∧ (w16 = true → ¬ (Lt σ K (b + t)).length < 241) ∧
      s.gpr .r10 = c) (scaG w16) (RVW w16 X K b (t + 8) c) := by
  refine RelCT.seq (relInvX (I' := fun σ s₀ s => (LAtW w16 σ s₀ K b t s ∧
      (w16 = true → ¬ (Lt σ K (b + t)).length < 241) ∧ s.gpr .r10 = c) ∧
      s.cf = some (decide ((Lt σ K (b + t)).length < 256))) (fun σ s₀ s _ _ h => ?_)
    (taintRel [.rdi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rdi, h₂.1.rdi, pub_Lt hq hK])
      (by taint_decide))) (RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => by
        show x.cf = y.cf; rw [h₁.2, h₂.2, pub_Lt hq hK]) ?_ ?_)
  · have hlen : (Lt σ K (b + t)).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ (b + t)
    refine WP.mono_syms (cmp256_ok s) fun s' ⟨hcf, hm, hg, hrd, hwr, _⟩ sy => ?_
    exact ⟨⟨h.1.same hg hm hrd hwr sy, h.2.1, by rw [hg]; exact h.2.2⟩,
      by rw [hcf, h.1.rdi, ofNat64_toNat (by bdd_omega)]⟩
  · -- with `snBody`
    exact RelCT.mono (sca_ct hK ht hbt) (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, i₁, _⟩, ⟨s₀₂, x₂, i₂, _⟩⟩, _⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, i₁⟩, ⟨s₀₂, x₂, i₂⟩⟩) fun _ _ h => h
  · -- past the 24 bytes
    refine RelCT.mono
      (P := RXW w16 X fun σ s₀ s => LAtW w16 σ s₀ K b t s ∧ (Lt σ K (b + t)).length = 256 ∧ s.gpr .r10 = c)
      (relInvX (fun σ s₀ s _ _ h => WP.mono (skip_ok h.1 h.2.1) fun s' ⟨l', h10⟩ =>
          ⟨⟨l', fun _ h' => absurd (Nat.lt_of_le_of_lt (Lt_mono σ K (b + t) 8) (by rwa [Nat.add_assoc]))
            (by rw [h.2.1]; decide)⟩, by rw [h10]; exact h.2.2⟩)
        (taintRel [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide))) ?_ fun _ _ h => h
    rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, ⟨l₁, -, d₁⟩, f₁⟩, ⟨s₀₂, x₂, ⟨l₂, -, d₂⟩, f₂⟩⟩, hb⟩
    have hb₁ : ¬ (Lt σ₁ K (b + t)).length < 256 := by
      have : x.cf = some false := hb
      rw [f₁] at this; simpa using this
    have hb₂ : ¬ (Lt σ₂ K (b + t)).length < 256 := by rw [← pub_Lt hq hK]; exact hb₁
    have e₁ : (Lt σ₁ K (b + t)).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ (b + t)
    have e₂ : (Lt σ₂ K (b + t)).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ (b + t)
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, by omega, d₁⟩, ⟨s₀₂, x₂, l₂, by omega, d₂⟩⟩

/-- The registers `vput` reads, after `vcand`, are the same in both runs. -/
theorem viw_regs {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {s₀₁ s₀₂ : State} {K b t : Nat} (hK : K < 4)
    (ht : t + 8 ≤ 168) (hbt : b + t + 8 ≤ 280) {x y : State} (h₁ : VIW w16 σ₁ s₀₁ K b t x)
    (h₂ : VIW w16 σ₂ s₀₂ K b t y) : ∀ r ∈ [Reg.rax, .rbp, .rdi, .rsi], x.gpr r = y.gpr r := by
  obtain ⟨u₁, l₁, -, a₁, -, -, -, -, -, -, g₁⟩ := h₁
  obtain ⟨u₂, l₂, -, a₂, -, -, -, -, -, -, g₂⟩ := h₂
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    rw [a₁, a₂, maskL_eq ht hbt l₁ (l := 0) (by decide), maskL_eq ht hbt l₁ (l := 1) (by decide),
      maskL_eq ht hbt l₂ (l := 0) (by decide), maskL_eq ht hbt l₂ (l := 1) (by decide), pub_B hq hK]
  · rw [g₁ _ (by decide), g₂ _ (by decide), l₁.rbp, l₂.rbp, pub_aP hq]
  · rw [g₁ _ (by decide), g₂ _ (by decide), l₁.rdi, l₂.rdi, pub_Lt hq hK]
  · rw [g₁ _ (by decide), g₂ _ (by decide), l₁.rsi, l₂.rsi, at', at', pub_scr hq]

/-- The registers `vputB` reads, after `vputA`, are the same in both runs. -/
theorem vpw_regs {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {s₀₁ s₀₂ : State} {K b t : Nat} (hK : K < 4)
    (ht : t + 8 ≤ 168) (hbt : b + t + 8 ≤ 280) {x y : State} (h₁ : VPW w16 σ₁ s₀₁ K b t x)
    (h₂ : VPW w16 σ₂ s₀₂ K b t y) : ∀ r ∈ [Reg.rax, .rbp, .rdi, .rsi], x.gpr r = y.gpr r := by
  obtain ⟨u₁, v₁, l₁, -, f₁, p₁⟩ := h₁
  obtain ⟨u₂, v₂, l₂, -, f₂, p₂⟩ := h₂
  have g₁ := f₁.2.2.2.2.2.2.2
  have g₂ := f₂.2.2.2.2.2.2.2
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    rw [p₁.rax, p₂.rax, maskL_eq ht hbt l₁ (l := 1) (by decide), maskL_eq ht hbt l₂ (l := 1) (by decide), pub_B hq hK]
  · rw [p₁.gpr _ (by decide) (by decide) (by decide), p₂.gpr _ (by decide) (by decide) (by decide), g₁ _ (by decide),
      g₂ _ (by decide), l₁.rbp, l₂.rbp, pub_aP hq]
  · apply BitVec.eq_of_toNat_eq
    have d₁ := p₁.rdi; have d₂ := p₂.rdi
    unfold cntL at d₁ d₂
    rw [d₁, d₂, g₁ _ (by decide), g₂ _ (by decide), l₁.rdi, l₂.rdi, maskL_eq ht hbt l₁ (l := 0) (by decide),
      maskL_eq ht hbt l₂ (l := 0) (by decide), pub_B hq hK, pub_Lt hq hK]
  · rw [p₁.gpr _ (by decide) (by decide) (by decide), p₂.gpr _ (by decide) (by decide) (by decide), g₁ _ (by decide),
      g₂ _ (by decide), l₁.rsi, l₂.rsi, at', at', pub_scr hq]

/-- A group of eight iterations. -/
theorem vgrp_ct {X : State → State → Prop} {K b t : Nat} {c : BitVec 64} (hK : K < 4) (ht : t + 8 ≤ 168)
    (hbt : b + t + 8 ≤ 280) : RelCT isa (RVW w16 X K b t c) (vgrp w16) (RVW w16 X K b (t + 8) c) := by
  cases w16 with
  | false =>
    exact RelCT.mono (scaG_ct hK ht hbt) (fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, d₁⟩, ⟨s₀₂, x₂, l₂, d₂⟩⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁.lat, fun hw => absurd hw (by decide), d₁⟩,
        ⟨s₀₂, x₂, l₂.lat, fun hw => absurd hw (by decide), d₂⟩⟩) fun _ _ h => h
  | true =>
  show RelCT isa _ (.seq (.block [.alu .cmp .rdi (.imm 241)]) (.ite .b (.seq (.block vcand) (.block vput)) (scaG true))) _
  refine RelCT.seq (relInvX (I' := fun σ s₀ s => (LVW true σ s₀ K b t s ∧ s.gpr .r10 = c) ∧
      s.cf = some (decide ((Lt σ K (b + t)).length < 241))) (fun σ s₀ s _ _ h => cmpG_ok h)
    (taintRel [.rdi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.lat.rdi, h₂.1.lat.rdi, pub_Lt hq hK])
      (by taint_decide))) (RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => by
        show x.cf = y.cf; rw [h₁.2, h₂.2, pub_Lt hq hK]) ?_ ?_)
  · -- with the vector code
    refine RelCT.mono
      (P := RXW true X fun σ s₀ s => LAtW true σ s₀ K b t s ∧ VC s ∧ (Lt σ K (b + t)).length < 241 ∧ s.gpr .r10 = c)
      (RelCT.seq (relInvX (I' := fun σ s₀ s => VIW true σ s₀ K b t s ∧ s.gpr .r10 = c)
          (fun σ s₀ s hp _ h => WP.mono (vec1_ok (preW_of hp) hK ht h.1 h.2.1 h.2.2.1) fun _ ⟨hi, h10⟩ =>
            ⟨hi, by rw [h10]; exact h.2.2.2⟩)
          (taintRel [.rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rsi, h₂.1.rsi, at', at', pub_scr hq])
            (by taint_decide)))
        (RelCT.block_append (RelCT.seq
          (relInvX (I' := fun σ s₀ s => VPW true σ s₀ K b t s ∧ s.gpr .r10 = c)
            (fun σ s₀ s hp _ h => WP.mono (vec2a_ok (preW_of hp) rfl hK h.1) fun _ ⟨hv, h10⟩ =>
              ⟨hv, by rw [h10]; exact h.2⟩)
            (taintRel [.rax, .rbp, .rdi, .rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ =>
              viw_regs hq hK ht hbt h₁.1 h₂.1) (by taint_decide)))
          (relInvX (fun σ s₀ s hp _ h => WP.mono (vec2b_ok (preW_of hp) rfl hK ht hbt h.1) fun _ ⟨l, v, h10⟩ =>
              ⟨⟨l, fun _ _ => v⟩, by rw [h10]; exact h.2⟩)
            (taintRel [.rax, .rbp, .rdi, .rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ =>
              vpw_regs hq hK ht hbt h₁.1 h₂.1) (by taint_decide))))))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, ⟨⟨l₁, v₁⟩, d₁⟩, f₁⟩, ⟨s₀₂, x₂, ⟨⟨l₂, v₂⟩, d₂⟩, f₂⟩⟩, hb⟩ => ?_)
      fun _ _ h => h
    have hb' : (Lt σ₁ K (b + t)).length < 241 := by
      have : x.cf = some true := hb
      rw [f₁] at this; simpa using this
    have hb'' : (Lt σ₂ K (b + t)).length < 241 := by rw [← pub_Lt hq hK]; exact hb'
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, v₁ rfl hb', hb', d₁⟩, ⟨s₀₂, x₂, l₂, v₂ rfl hb'', hb'', d₂⟩⟩
  · -- with `scaG`
    refine RelCT.mono (scaG_ct hK ht hbt) ?_ fun _ _ h => h
    rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, ⟨⟨l₁, -⟩, d₁⟩, f₁⟩, ⟨s₀₂, x₂, ⟨⟨l₂, -⟩, d₂⟩, f₂⟩⟩, hb⟩
    have hb' : ¬ (Lt σ₁ K (b + t)).length < 241 := by
      have : x.cf = some false := hb
      rw [f₁] at this; simpa using this
    have hb'' : ¬ (Lt σ₂ K (b + t)).length < 241 := by rw [← pub_Lt hq hK]; exact hb'
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, fun _ => hb', d₁⟩, ⟨s₀₂, x₂, l₂, fun _ => hb'', d₂⟩⟩

/-! ## The calls of the baseline implementation -/

/-- The call of `vg_mlkem_sample_ntt` on seed `K`, with `X σ` of the memory, which its writes keep. -/
theorem call_ct {X : State → Mem → Prop} {K : Nat} (hK : K < 4)
    (hX : ∀ σ, (sample4KW w16).pre σ → ∀ m m', Frame (cWrW w16 σ K ++ [stkR σ]) m m' → X σ m → X σ m') :
    RelCT isa (R4W w16 fun σ s => ArgIW w16 (X σ) σ K s)
      (.call (if w16 then "vg_mlkem16_sample_ntt" else "vg_mlkem_sample_ntt") (sampleNTTW w16))
      (R4W w16 fun σ s => CallIW w16 (X σ) σ K s) :=
  relInv (fun σ s hp h => callK_ok (preW_of hp) hK (hX σ hp) h) (RelCT.callEx (sampleW_correct w16) (sampleW_ct w16)
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      have hsp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.pinv.env.rsp, h₂.pinv.env.rsp, pub_sp hq]
      refine ⟨_, _, _, _, argK_pre (preW_of p₁) hK h₁, argK_pre (preW_of p₂) hK h₂, ?_,
        (cov (preW_of p₁) h₁.pinv.env hK).1, (cov (preW_of p₁) h₁.pinv.env hK).2,
        (cov (preW_of p₂) h₂.pinv.env hK).1, (cov (preW_of p₂) h₂.pinv.env hK).2, hsp⟩
      simp only [sampleKW, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi, h₁.rdx, h₂.rdx]
      rw [ce_bytesAt24 s₁ (n := 34) (by decide) (argK_kS (preW_of p₁) hK h₁),
        ce_bytesAt24 s₂ (n := 34) (by decide) (argK_kS (preW_of p₂) hK h₂),
        seed_bytes (preW_of p₁) hK h₁.pinv.env.frame, seed_bytes (preW_of p₂) hK h₂.pinv.env.frame, pub_B hq hK]
      simp only [pub_sd hq, pub_aP hq, at', pub_scr hq, hsp, and_self])

/-- The arguments of the call on seed `K`, given their taint analysis. -/
theorem args_ct {X : State → Mem → Prop} {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (pBytes w16 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (R4W w16 fun σ s => PCW w16 (X σ) σ K s)
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (pBytes w16 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) (R4W w16 fun σ s => ArgIW w16 (X σ) σ K s) :=
  relInv (fun σ s _ h => argsK_ok hK h) (taintRel [.r12, .r13, .rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.env.r12, h₂.env.r12, pub_sd hq]
    · rw [h₁.env.r13, h₂.env.r13, pub_aP hq]
    · exact env_rbx hq h₁.env h₂.env) c)

theorem and_ct {X : State → Mem → Prop} {K : Nat} :
    RelCT isa (R4W w16 fun σ s => CallIW w16 (X σ) σ K s) (.block [.alu32 .and .r14 (.reg .rax)])
      (R4W w16 fun σ s => PCW w16 (X σ) σ (K + 1) s) :=
  relInv (fun σ s _ h => andK_ok h) (taintRel [] SampleNtt.nil_regs (by taint_decide))

/-! ## The loops -/

/-- Two runs at group `2 i` of a loop of `N` iterations of its body, `n = N - i` from its end. -/
def LI (w16 : Bool) (X : State → State → Prop) (K b N n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ i, n = N - i ∧ i < N ∧ RVW w16 X K b (8 * i) (BitVec.ofNat 64 (N - i)) s₁ s₂

theorem sub10_ct {X : State → State → Prop} {K b t : Nat} {c : BitVec 64} :
    RelCT isa (RVW w16 X K b t c) (.block [.alu .sub .r10 (.imm 1)])
      (RXW w16 X fun σ s₀ s => LVW w16 σ s₀ K b t s ∧ s.gpr .r10 = c - 1 ∧ s.zf = some (c - 1 == 0)) :=
  relInvX (fun σ s₀ s _ _ h => WP.mono_syms (sub10_ok s) fun s' ⟨⟨hm, h10, hz, hl⟩, k⟩ sy =>
      ⟨⟨h.1.lat.same' hm k sy, fun hw h' => (h.1.vc hw h').same hl⟩, by rw [h10, h.2], by rw [hz, h.2]⟩)
    (taintRel [.r10] (fun x y ⟨σ₁, σ₂, _, _, _, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) (by taint_decide))

theorem loopV_ct {X : State → State → Prop} {K b N : Nat} (hK : K < 4) (hN' : 8 * N ≤ 168) (hbN : b + 8 * N ≤ 280)
    (n : Nat) : RelCT isa (LI w16 X K b N n) (.loop (Sample4.vbody w16) .ne) (RXW w16 X fun σ s₀ s => LAtW w16 σ s₀ K b (8 * N) s) := by
  refine RelCT.loop (M := isa) (LI w16 X K b N) (fun n => ?_) n
  refine RelCT.mono (P := fun s₁ s₂ => ∃ i, n = N - i ∧ i < N ∧ RVW w16 X K b (8 * i) (BitVec.ofNat 64 (N - i)) s₁ s₂)
    (RelCT.exists_ fun i => ?_) (fun _ _ h => by unfold LI at h; exact h) fun _ _ h => h
  by_cases hi : i < N ∧ n = N - i
  · obtain ⟨hi, hn⟩ := hi
    refine RelCT.mono (P := RVW w16 X K b (8 * i) (BitVec.ofNat 64 (N - i)))
      (RelCT.seq (vgrp_ct hK (by bdd_omega) (by bdd_omega)) sub10_ct)
      (fun _ _ h => h.2.2) fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, d₁, z₁⟩, ⟨s₀₂, x₂, l₂, d₂, z₂⟩⟩ => ?_
    rw [ofNat64_pred (by bdd_omega) (by bdd_omega)] at d₁ d₂ z₁ z₂
    rw [ofNat64_beq_zero (by bdd_omega)] at z₁ z₂
    rw [show 8 * i + 8 = 8 * (i + 1) by bdd_omega] at l₁ l₂
    refine ⟨by show x.zf.map _ = y.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht => ?_⟩
    · have : N - i - 1 = 0 := by
        have : x.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [show i + 1 = N by bdd_omega] at l₁ l₂
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁.lat⟩, ⟨s₀₂, x₂, l₂.lat⟩⟩
    · have : N - i - 1 ≠ 0 := by
        have : x.zf.map (!·) = some true := ht
        rw [z₁] at this; simpa using this
      exact ⟨N - (i + 1), by bdd_omega, i + 1, rfl, by bdd_omega, σ₁, σ₂, p₁, p₂, hq,
        ⟨s₀₁, x₁, l₁, by rw [d₁]; congr 1⟩, ⟨s₀₂, x₂, l₂, by rw [d₂]; congr 1⟩⟩
  · exact RelCT.of_false fun _ _ h => hi ⟨h.2.1, h.1⟩

/-- A run of `N` iterations of the loop's body on seed `K`, from states with `X`, given the taint
analysis of its setup and of its count's store. -/
theorem run_ct {X : State → State → Prop} {Y : State → State → Prop} {K b N : Nat} (hK : K < 4) (hN : 0 < N)
    (hN' : 8 * N ≤ 168) (hbN : b + 8 * N ≤ 280) {set : List Instr}
    (hset : ∀ σ s, (sample4KW w16).pre σ → X σ s → EnvW w16 σ s ∧
      WP isa (.block set) s fun s' => LVW w16 σ s K b 0 s' ∧ s'.gpr .r10 = BitVec.ofNat 64 N)
    (hend : ∀ σ s₀ s, (sample4KW w16).pre σ → X σ s₀ → LAtW w16 σ s₀ K b (8 * N) s →
      WP isa (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) s (Y σ))
    {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block set) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) h₂).isSome = true) :
    RelCT isa (R4W w16 X) (.seq (.block set) (.seq (.loop (vbody w16) .ne) (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi])))
      (R4W w16 Y) := by
  refine RelCT.seq (RelCT.mono (relInv (I' := fun σ s => ∃ s₀, X σ s₀ ∧ LVW w16 σ s₀ K b 0 s ∧ s.gpr .r10 = BitVec.ofNat 64 N)
      (fun σ s hp h => WP.mono (hset σ s hp h).2 fun _ h' => ⟨s, h, h'⟩)
      (taintRel [.rbx, .r13] (fun x y ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ r hr => by
        have e₁ := (hset σ₁ x p₁ h₁).1
        have e₂ := (hset σ₂ y p₂ h₂).1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact env_rbx hq e₁ e₂
        · rw [e₁.r13, e₂.r13, pub_aP hq]) c₁)) (fun _ _ h => h)
      (Q' := LI w16 X K b N N) fun x y h => ⟨0, by omega, hN, h⟩)
    (RelCT.seq (loopV_ct hK hN' hbN N)
      (relInv (I := fun σ s => ∃ s₀, X σ s₀ ∧ LAtW w16 σ s₀ K b (8 * N) s) (fun σ s hp ⟨s₀, h₀, hA⟩ => hend σ s₀ s hp h₀ hA)
        (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, a₁⟩, ⟨_, _, a₂⟩⟩ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq a₁.lb.env a₂.lb.env) c₂)))

/-- The taint analysis of the setups of the runs, of either width. -/
theorem setup_taint {K : Nat} (hK : K < 4) (w16 : Bool) :
    (∃ h : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (setup K w16 ++ cstLoad)) h).isSome = true) ∧
    ∃ h : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (contSetup K w16 ++ cstLoad)) h).isSome = true := by
  rcases (by omega : K = 0 ∨ K = 1 ∨ K = 2 ∨ K = 3) with rfl | rfl | rfl | rfl <;> cases w16 <;>
    exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem run1_ct {K : Nat} (hK : K < 4) {h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) h₂).isSome = true) :
    RelCT isa (R4W w16 fun σ s => P1W w16 σ K s) (run1 K w16) (R4W w16 fun σ s => P1W w16 σ (K + 1) s) := by
  obtain ⟨⟨_, c₁⟩, _⟩ := setup_taint hK w16
  exact run_ct (N := 21) hK (by decide) (by decide) (by decide)
    (fun σ s hp h => ⟨h.sq.env, setup_ok (preW_of hp) hK (lb1 hK h)⟩)
    (fun σ s₀ s hp h₀ hA => run1End_ok (preW_of hp) hK h₀ hA) c₁ c₂

theorem run2_ct {K : Nat} (hK : K < 4) {h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) h₂).isSome = true) :
    RelCT isa (R4W w16 fun σ s => P2W w16 σ K s) (run2 K w16) (R4W w16 fun σ s => P2W w16 σ (K + 1) s) := by
  obtain ⟨_, ⟨_, c₁⟩⟩ := setup_taint hK w16
  exact run_ct (N := 14) hK (by decide) (by decide) (by decide)
    (fun σ s hp h => ⟨h.sq.env, contSetup_ok (preW_of hp) hK (lb2 hK h)
      (by rw [h.j K hK, ite_eq_right (by omega)]) (by have := h.st K hK; rwa [ite_eq_right (by omega)] at this)⟩)
    (fun σ s₀ s hp h₀ hA => run2End_ok (preW_of hp) hK h₀ hA) c₁ c₂

theorem tab_ct : RelCT isa (R4W w16 fun σ s => SqTW w16 σ 0 3 s) (.block tabAddr) (R4W w16 fun σ s => P1W w16 σ 0 s) :=
  relInv (fun σ s _ h => p1_zero_ok h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide))

/-! ## The check and the second runs -/

theorem pub_allFull {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) (t : Nat) : allFull σ₁ t = allFull σ₂ t := by
  simp only [allFull, List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.true_and]
  rw [pub_Lt hq (K := 0) (by decide), pub_Lt hq (K := 1) (by decide), pub_Lt hq (K := 2) (by decide),
    pub_Lt hq (K := 3) (by decide)]

theorem check_ct : RelCT isa (R4W w16 fun σ s => P1W w16 σ 4 s)
    (.block (cntFlags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) (R4W w16 (CheckedW w16)) :=
  relInv (fun σ s hp h => check_ok (preW_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem more4_ct {fast : Bool} : RelCT isa (R4W w16 (CheckedW w16)) (more4 fast w16) (R4W w16 (DoneW w16)) := by
  unfold more4
  refine RelCT.seq (relInv (fun σ s _ h => reset_ok h) (taintRel [] SampleNtt.nil_regs (by taint_decide))) ?_
  have hsq : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezes 0 2 fast) hc).isSome = true := by
    cases fast
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, csq⟩ := hsq
  refine RelCT.seq (relInv (fun σ s hp h => sqM_ok (fast := fast) (preW_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) csq)) ?_
  refine RelCT.seq (relInv (fun σ s _ h => tab2_ok h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))) ?_
  refine RelCT.seq (run2_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run2_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run2_ct (K := 2) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run2_ct (K := 3) (by decide) (by taint_decide)) ?_
  exact relInv (fun σ s hp h => last_ok (preW_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem branch_ct {fast : Bool} : RelCT isa (R4W w16 (CheckedW w16)) (.ite .e (more4 fast w16) (.block [])) (R4W w16 (DoneW w16)) := by
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
    show x.zf = y.zf; rw [h₁.zf, h₂.zf, pub_allFull hq])
    (RelCT.mono more4_ct (fun _ _ h => h.1) (fun _ _ h => h)) ?_
  have empty : RelCT isa (R4W w16 fun σ s => CheckedW w16 σ s ∧ allFull σ 168 = true) (.block []) (R4W w16 (DoneW w16)) :=
    relInv (fun σ s _ ⟨h, hf⟩ => WP.block_nil (DoneW.of_full h hf)) (taintRel [] SampleNtt.nil_regs (by taint_decide))
  refine RelCT.mono empty (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_) (fun _ _ h => h)
  have hz : x.zf = some false := hb
  have hf : allFull σ₁ 168 = true := by rw [h₁.zf] at hz; simpa using hz
  exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hf⟩, ⟨h₂, by rw [← pub_allFull hq]; exact hf⟩⟩

theorem tail4_ct {fast : Bool} : RelCT isa (R4W w16 fun σ s => P1W w16 σ 4 s) (tail4 fast w16) (fun _ _ => True) := by
  unfold tail4
  exact RelCT.seq check_ct (RelCT.seq branch_ct
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)))

theorem ct {fast : Bool} :
    ConstantTime isa (sample4KW w16).pre (sample4KW w16).pub (Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 fast w16) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq start_ct (RelCT.seq (sq_ct (fast := fast))
    (RelCT.seq tab_ct ?_)))
  refine RelCT.seq (run1_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1_ct (K := 2) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1_ct (K := 3) (by decide) (by taint_decide)) ?_
  exact tail4_ct

end VG.Proof.MlKem.X86_64.S4
