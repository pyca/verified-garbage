module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Run
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, correctness

The pieces, in order: the prologue, the round constants and the padded seeds
(`S4Absorb.lean`), three squeezes (`S4Squeeze.lean`, `S4SqT.lean`), the table
(`S4Tab.lean`), the first 168 iterations on each seed, and if one needs them,
two more squeezes and 112 more iterations on each (`S4Run.lean`, `S4Loop.lean`),
and the epilogue, which returns whether every seed sampled its polynomial.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.Sha3.X86_64.X4 (la)

section
variable {σ : State} (hp : PreW w16 σ)
include hp

/-- The prologue, the round constants and the padded seeds. -/
theorem start_ok : WP isa (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4)) σ (SqInvW w16 σ 0) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pro_ok hp) fun s₁ h₁ => WP.mono (rc_ok hp h₁.env) fun s₂ h₂ => ?_
  have he₂ : EnvW w16 σ s₂ := EnvW.low h₁.env (rs := [⟨at' σ oRc, 768⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [oRc, oSave]; omega))
    h₂.frame h₂.keep.2.1 h₂.keep.2.2 fun r hr => h₂.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.mono (absorb_ok hp (m₁ := s₂.mem) ⟨he₂, by rw [h₂.keep.gpr (by decide), h₁.r14], Frame.refl _ _⟩)
    fun s₃ ⟨a₃, b₃⟩ => ⟨a₃.env, a₃.r14, fun r hr k hk => ?_, lanes_A0 b₃, fun _ _ p hp' => absurd hp' (by omega)⟩
  rw [a₃.frame.readW (Region.contains_self _ _) (by
    simpa using Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega))
    (by decide)]
  exact h₂.rc r hr k hk

omit hp in
theorem epi_eq : epi = [.mov32 .rax (.reg .r14), .mov .r14 (.mem (at_ .rbx 4416)), .mov .r13 (.mem (at_ .rbx 4408)),
    .mov .r12 (.mem (at_ .rbx 4400)), .mov .rbp (.mem (at_ .rbx 4392)), .mov .rbx (.mem (at_ .rbx 4384))] := rfl

/-- The return value, and the callee-saved registers restored. -/
theorem end_ok {X : Mem → Prop} {s : State} (h : PCW w16 X σ 4 s) :
    WP isa (.block epi) s fun s' => (sample4KW w16).post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
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
  refine ⟨⟨?_, fun k hk f e => ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, okN]
    split <;> rfl
  · rw [hm]; exact h.polys k hk f e
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
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega)⟩)
      (by decide)

/-- Everything after the prologue, the round constants and the padded seeds. -/
theorem body_ok {fast : Bool} {s : State} (h : SqInvW w16 σ 0 s) :
    WP isa (.seq (squeezes 0 3 fast) (.seq (.block tabBuild)
      (.seq (run1 0 w16) (.seq (run1 1 w16) (.seq (run1 2 w16) (.seq (run1 3 w16) (tail4 fast w16))))))) s fun s' =>
      (sample4KW w16).post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (sqTs_ok (fast := fast) hp (by decide) (by decide) (sqT_of h)) fun _ ⟨q₃, _⟩ =>
    WP.seq (WP.mono (p1_zero_ok hp q₃) fun _ p₀ => ?_))
  refine WP.seq (WP.mono (run1_ok hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (run1_ok hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (run1_ok hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (run1_ok hp (by decide) p₃) fun _ p₄ => ?_))))
  unfold tail4
  refine WP.seq (WP.mono (check_ok hp p₄) fun _ c => WP.seq (WP.mono (branch_ok hp c) fun s₅ d => ?_))
  exact WP.block_append (WP.mono (vz_ok s₅) fun _ ⟨hm, hk⟩ => end_ok hp (d.pc.keep hm hk (by decide)))

end

theorem correct {fast : Bool} (σ : State) (hs : (sample4KW w16).pre σ) :
    ∃ t s', Exec isa (Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 fast w16) σ t s' ∧ abiPreserved σ s' ∧
      (sample4KW w16).post σ s' := by
  have hp := preW_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (start_ok hp) fun _ h => body_ok (fast := fast) hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by cases fast <;> cases w16 <;> decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlKem.X86_64.S4
