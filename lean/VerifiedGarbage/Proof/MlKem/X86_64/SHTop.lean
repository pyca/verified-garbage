module

public import VerifiedGarbage.Proof.MlKem.X86_64.SHRun
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ML-KEM on x86-64: `Sample4.sampleH`, correctness

The fragment's contract (`sampleHK`): `vg_mlkem_sample_ntt4`'s precondition
and public data (`sample4K`), and as postcondition its result and
polynomials for the first three seeds, and the sponge's state at
`scratch + 6720` after absorbing the three blocks from `scratch + 6920`
(`habs`). The pieces in order (`correct`): the prologue, the round constants
and the padded seeds (`startF_ok`); the sponge's state to the fourth state
(`hload_ok`); the three squeezes absorbing the blocks (`squeezesH_ok`); the
fourth state back (`hsave_ok`); the table and the runs on the three seeds,
with the two more squeezes if one needs them (`SHRun.lean`); and the
epilogue (`end3_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (stateAt bytesAt)

/-- The contract of `Sample4.sampleH`: `vg_mlkem_sample_ntt4`'s on the first
three seeds, and the sponge of `H` at `scratch + 6720` absorbing the three
blocks at `scratch + 6920`. -/
def sampleHK : Contract isa where
  pre := sample4K.pre
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (List.range 3).all fun k => (sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k)).isSome
          then 1 else 0) ∧
      (∀ k < 3, ∀ f, sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k) = some f →
        PolyIs s'.mem (poly4 (s.gpr .rsi) k) f) ∧
      stateAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 Impl.MlKem.X86_64.Sample4.oHS) =
        SH.habs (stateAt s.mem (s.gpr .rdx + BitVec.ofNat 64 Impl.MlKem.X86_64.Sample4.oHS))
          (fun i => bytesAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (Impl.MlKem.X86_64.Sample4.oHB + 136 * i)) 136) 3
  pub := sample4K.pub

namespace SH

open VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4

section
variable {σ : State} (hp : Pre σ)
include hp

/-- The return value, and the callee-saved registers restored. -/
theorem end3_ok {s : State} (h : Done3 σ (hst σ 3) s) :
    WP isa (.block epi) s fun s' => sampleHK.post σ s' ∧ gprPreserved σ s' := by
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
  refine ⟨⟨?_, fun k hk f e => ?_, ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, okN]
    split <;> rfl
  · rw [hm]; exact polyIs_of (h.st k hk) f e
  · rw [hm]; exact h.hs
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

/-- After the squeezes, with the sponge's state stored back. -/
theorem run3_ok {fast : Bool} {s : State} (h : SqY σ (hst σ 3) 0 3 s) (hs : HS σ (hst σ 3) s.mem) :
    WP isa (.seq (.block tabBuild) (.seq (run1 0) (.seq (run1 1) (.seq (run1 2) (tail3 fast))))) s fun s' =>
      sampleHK.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (tabY_ok hp h hs) fun _ p₀ => ?_)
  refine WP.seq (WP.mono (run1Y_ok hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (run1Y_ok hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (run1Y_ok hp (by decide) p₂) fun _ p₃ => ?_)))
  unfold tail3
  refine WP.seq (WP.mono (check3_ok hp p₃) fun _ c => WP.seq (WP.mono (branch3_ok hp c) fun s₅ d => ?_))
  exact WP.block_append (WP.mono (vz_ok s₅) fun _ ⟨hm, hk⟩ => end3_ok hp
    ⟨d.env.keep hm hk (by decide), by rw [hk.gpr (by decide), d.r14], by rw [hm]; exact d.st,
      by unfold HS; rw [hm]; exact d.hs⟩)

end

theorem correct {fast : Bool} (σ : State) (hs : sampleHK.pre σ) :
    ∃ t s', Exec isa (sampleH fast) σ t s' ∧ abiPreserved σ s' ∧ sampleHK.post σ s' := by
  have hp := pre_of (w16 := false) hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (startF_ok hp) fun s₁ ⟨h₁, r₁⟩ =>
    WP.seq (WP.mono (hload_ok hp h₁ r₁) fun s₂ ⟨h₂, r₂⟩ =>
      WP.seq (WP.mono (squeezesH_ok (fast := fast) hp h₂ r₂) fun s₃ ⟨h₃, _⟩ =>
        WP.seq (WP.mono (hsave_ok hp h₃) fun s₄ ⟨h₄, e₄⟩ => run3_ok (fast := fast) hp h₄ e₄))))
  exact ⟨t, s', he, abiPreserved_of_exec (by cases fast <;> decide +kernel) he hF.2, hF.1⟩

end SH

end VG.Proof.MlKem.X86_64
