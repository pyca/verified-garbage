module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Round
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTRegion
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Lit
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Lit
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Round
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTRegion
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# The IFMA Miller–Rabin round: constant time

`code_ct`: the dispatch reads the candidate's word count, which `roundPub`
makes equal in both runs, so both take the same branch; each layout's round
is a frame (`RelCT.frame`) around code whose addresses and branches depend
on `rdi` and `rsp` alone (the taint analysis, `body_t`), and the fallback is
`round mul`'s (`RoundArith.round_ct`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Bignum.X86_64 (Two Pins two_taint two_piece two_map two_ite)
open VG.Proof.Bignum.X86_64.Ifma (TOk)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Rsa.X86_64.PubIfma (pay1024 pay1536 pay2048 pay3072 pay4096)
open VG.Impl.MillerRabin.X86_64.Ifma

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The frame's body passes the taint analysis from `rdi` and `rsp`. -/
theorem body_t (hl : MrOk l) :
    TOk [.rdi, .rsp] (VG.Impl.Bignum.X86_64.seqs (setup l ++ [vec l, .block (finish l)])) := by
  rcases hl with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- A layout's round leaks the same in runs with the same `rsp` and `rdi`. -/
theorem ifma_ct (hl : MrOk l) :
    RelCT isa (fun s₁ s₂ => s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi) (ifma l)
      fun _ _ => True := by
  obtain ⟨_, hT⟩ := body_t hl
  unfold ifma
  refine RelCT.frame (fun _ _ h => h.1) ((two_taint (Φ := fun (p : Addr × Addr) u =>
      u.gpr .rdi = p.1 ∧ u.gpr .rsp = p.2) [.rdi, .rsp] (fun p s₁ s₂ h₁ h₂ r hr => ?_) hT).mono ?_ fun _ _ h => h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2, h₂.2]
  · rintro a b ⟨s₁, s₂, ⟨hsp, hdi⟩, rfl, rfl⟩
    exact ⟨(s₁.gpr .rdi, (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s₁).gpr .rsp),
      ⟨pushed_gpr _ _ (by decide), rfl⟩,
      ⟨by rw [pushed_gpr _ _ (by decide), hdi], by rw [pushed_rsp, pushed_rsp, hsp]⟩⟩

/-- A state of the dispatch: the round's precondition, with the public data
`a` (`rsp`, `rdi`, `rsi` and `w`). -/
def CP (a : Addr × Addr × BitVec 64 × Nat) (s : State) : Prop :=
  roundPre s ∧ s.gpr .rsp = a.1 ∧ s.gpr .rdi = a.2.1 ∧ s.gpr .rsi = a.2.2.1 ∧
    Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) = a.2.2.2

theorem cp_rdi : Pins CP [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  rw [List.mem_singleton.mp hr, h₁.2.2.1, h₂.2.2.1]

/-- `cmp w, n`: `w` is public. -/
theorem isW_ct (n : Nat) (hn : n < 2 ^ 31) (hT : TOk [.rdi] (.block (isW n))) :
    RelCT isa (Two CP) (.block (isW n)) (Two fun a u => CP a u ∧ u.zf = some (decide (a.2.2.2 = n))) := by
  obtain ⟨_, hT⟩ := hT
  refine two_piece [.rdi] cp_rdi hT fun a s h => ?_
  obtain ⟨hdim, bm, hctx, -⟩ := initial_ctx h.1
  have hw31 : Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) < 2 ^ 31 := by have := hdim.w128; omega_arith
  refine WP.mono (isW_ok n hctx.good hdim.z hn hw31) fun u ⟨z, m, k⟩ => ?_
  have hdi : u.gpr .rdi = s.gpr .rdi := k.gpr (by decide)
  refine ⟨⟨pre_congr m k h.1, (k.gpr (by decide)).trans h.2.1, hdi.trans h.2.2.1,
    (k.gpr (by decide)).trans h.2.2.2.1, by rw [m, hdi]; exact h.2.2.2.2⟩, ?_⟩
  rw [z, h.2.2.2.2]

/-- A step of the dispatch: `cmp w, n`, then `th` if `w = n`, else `el`. -/
theorem step_ct (n : Nat) (hn : n < 2 ^ 31) (hT : TOk [.rdi] (.block (isW n))) {th el : Prog isa}
    (ht : RelCT isa (Two CP) th fun _ _ => True) (he : RelCT isa (Two CP) el fun _ _ => True) :
    RelCT isa (Two CP) (.seq (.block (isW n)) (.ite .e th el)) fun _ _ => True :=
  RelCT.seq (isW_ct n hn hT) (two_ite (fun _ _ _ h₁ h₂ => by
      show _root_.VG.X86_64.State.zf _ = _root_.VG.X86_64.State.zf _; rw [h₁.2, h₂.2])
    (two_map id (fun _ _ h => h.1.1) ht) (two_map id (fun _ _ h => h.1.1) he))

theorem ifma_ct' (hl : MrOk l) : RelCT isa (Two CP) (ifma l) fun _ _ => True :=
  (ifma_ct hl).mono (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm⟩)
    fun _ _ h => h

theorem round_ct' (v : RoundArith) :
    RelCT isa (Two CP) (VG.Impl.MillerRabin.X86_64.round v.mm) fun _ _ => True :=
  fun _ _ _ _ _ _ ⟨_, h₁, h₂⟩ e₁ e₂ => ⟨v.round_ct _ _ _ _ _ _ h₁.1 h₂.1
    ⟨h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.trans h₂.2.2.2.2.symm⟩ e₁ e₂, trivial⟩

/-- The round with the IFMA layouts, `round mul` otherwise, is constant time. -/
theorem code_ct (v : RoundArith) : ConstantTime isa roundPre roundPub (code v.mm) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ((step_ct 16 (by decide) ⟨_, by taint_decide⟩ (ifma_ct' (.inl rfl))
    (step_ct 24 (by decide) ⟨_, by taint_decide⟩ (ifma_ct' (.inr (.inl rfl)))
      (step_ct 32 (by decide) ⟨_, by taint_decide⟩ (ifma_ct' (.inr (.inr (.inl rfl))))
        (step_ct 48 (by decide) ⟨_, by taint_decide⟩ (ifma_ct' (.inr (.inr (.inr (.inl rfl)))))
          (step_ct 64 (by decide) ⟨_, by taint_decide⟩ (ifma_ct' (.inr (.inr (.inr (.inr rfl))))) (round_ct' v)))))).mono ?_
    fun _ _ h => h)
  rintro s₁ s₂ ⟨h₁, h₂, hsp, hdi, hsi, hw⟩
  exact ⟨(s₁.gpr .rsp, s₁.gpr .rdi, s₁.gpr .rsi, Proof.Rsa.Mont.wOf s₁.mem (s₁.gpr .rdi)),
    ⟨h₁, rfl, rfl, rfl, rfl⟩, ⟨h₂, hsp.symm, hdi.symm, hsi.symm, hw.symm⟩⟩

end VG.Proof.MillerRabin.X86_64.Ifma
