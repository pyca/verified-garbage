module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.Fn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.Fn
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT

/-!
# AES-GCM decryption out of place, by a copy, RISC-V: constant time

Untrusted: everything here is checked by Lean. Two runs whose stack pointer,
arguments and leak agree (`toPub`) leak the same trace, related piece by
piece from the states the correctness proof describes (`Gather.RISCV64.Eq2`):
the frame's allocation leaks nothing (`relCT_alloc`); the entry, the load of
the call's argument and of the return address are at the stack pointer,
our frame or our stack arguments; the copy is constant time by the taint
analysis from its arguments `src`, `len` and `dst`; the call is constant
time by its callee's contract, whose public data (its arguments and whether
it succeeds, `Ready.leak`) agree; the branch after it is on whether the tag
is right, our leak (`tested_wp`); and `wipe`'s loop runs on `dst` and `len`.
As on PPC64LE (`Proof/AesGcm/PPC64LE/OpenTo/CT.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.RISCV64.OpenTo

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64.OpenTo
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint rel_ite ct_of)

/-- Two runs of a frame allocating `bytes` bytes leak the same trace when the
runs of its body, from the states after the allocation, do: `alloc` and
`free` leak no address. -/
theorem relCT_alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocd bytes s ∧ b = allocd bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocd bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨by simp only [addrs], trivial⟩

/-- The call's public data, from the arguments. -/
theorem Ready.leak {s c : State} (h : Lay s) (hc : Ready s c) : callLeak (xS s c) = toLeak s := by
  obtain ⟨-, c4, -⟩ := hc.callGpr (rdC s) (wrC s)
  simp only [callLeak, toLeak, hc.xres h, c4]

theorem resNone {σ₁ σ₂ : State} (p₁ : ToPre σ₁) (p₂ : ToPre σ₂) (ql : toLeak σ₁ = toLeak σ₂) :
    (res σ₁).isNone = (res σ₂).isNone := by
  simp only [toLeak, p₁.hR, p₂.hR, not_true_eq_false, ↓reduceIte, List.cons.injEq, and_true] at ql
  revert ql
  cases res σ₁ <;> cases res σ₂ <;> simp

theorem openTo_ct (hv : OpenOk)
    (hct : ConstantTime isa (Proof.AesGcm.openRoundsContract RISCV64.abi 4640).pre
      (Proof.AesGcm.openRoundsContract RISCV64.abi 4640).pub openCode) :
    ConstantTime isa ToPre toPub openTo := by
  refine ct_of fun s₁ s₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qsp, ql, q3, q4, q5, q6, q7, q8, q9, q10, qa⟩ := hq
  have hP : Pf s₁ = Pf s₂ := by simp only [Pf, Bs, qsp]
  unfold openTo
  refine (relCT_alloc (P := Eq2 s₁ s₂) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocd 32 s₁) (allocd 32 s₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst s t; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
      (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (show s₁.sp - BitVec.ofNat 64 32 = s₂.sp - BitVec.ofNat 64 32 by rw [qsp])
    (by simp) (by taint_decide)) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The copy, from the same arguments.
  refine rel_seq (rel_taint [.t0, .t1, .a6] (by rw [he₁.sp, he₂.sp, hP])
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨by rw [he₁.t0, he₂.t0, Src, Src, q9], by rw [he₁.t1, he₂.t1, q10],
        by rw [he₁.a6, he₂.a6, Dst, Dst, qa 0 (by decide)]⟩)
    (by taint_decide)) (copied_wp h₁ he₁) (copied_wp h₂ he₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call's argument.
  refine rel_seq (rel_taint [] (by rw [hc₁.sp, hc₂.sp, hP]) (by simp) (by taint_decide))
    (ready_wp h₁ hc₁) (ready_wp h₂ hc₂) fun r₁ r₂ hr₁ hr₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC s₂ = rdC s₁ := by
    simp only [rdC, kR, nR, aR, tR, C, Nn, NL, Ad, AL, Tg, TL, Pf, Bs, q3, q5, q6, q7, q8,
      qa 2 (by decide), qa 3 (by decide), qsp]
  have hwr : wrC s₂ = wrC s₁ := by simp only [wrC, dR, Dst, L, qa 0 (by decide), q10]
  have hx₂ : xS s₂ r₂ = r₂.callEntry.withRegions (rdC s₁) (wrC s₁) := by rw [← hrd, ← hwr]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hr₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hr₂.call h₂
  have lk₁ := hr₁.leak h₁
  have lk₂ := hr₂.leak h₂
  rw [hx₂] at cp₂ lk₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  obtain ⟨g3₁, g4₁, g5₁, g6₁, g7₁, g8₁, g9₁, g10₁⟩ := hr₁.callGpr (rdC s₁) (wrC s₁)
  obtain ⟨g3₂, g4₂, g5₂, g6₂, g7₂, g8₂, g9₂, g10₂⟩ := hr₂.callGpr (rdC s₁) (wrC s₁)
  obtain ⟨a0₁, a1₁⟩ := hr₁.args h₁ (rdC s₁) (wrC s₁)
  obtain ⟨a0₂, a1₂⟩ := hr₂.args h₂ (rdC s₁) (wrC s₁)
  refine rel_seq (RelCT.call hv hct (rdC s₁) (wrC s₁) fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨openSpec_pre cp₁, openSpec_pre cp₂, openSpec_pub ⟨?_, by rw [lk₁, lk₂, ql], ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩, cv₁, cw₁, cv₂, cw₂⟩
      · simp only [State.withRegions_sp, State.callEntry_sp, hr₁.sp, hr₂.sp, hP]
      · rw [g3₁, g3₂, C, C, q3]
      · rw [g4₁, g4₂, q4]
      · rw [g5₁, g5₂, Nn, Nn, q5]
      · rw [g6₁, g6₂, q6]
      · rw [g7₁, g7₂, Ad, Ad, q7]
      · rw [g8₁, g8₂, q8]
      · rw [g9₁, g9₂, Dst, Dst, qa 0 (by decide)]
      · rw [g10₁, g10₂, q10]
      · rw [a0₁, a0₂, Tg, Tg, qa 2 (by decide)]
      · rw [a1₁, a1₂, qa 3 (by decide)])
    (called_wp hv h₁ hr₁) (called_wp hv h₂ hr₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- After the call: the same branch in both runs.
  have hn := resNone p₁ p₂ ql
  refine rel_seq ?_ (after_wp h₁ hz₁) (after_wp h₂ hz₂) fun u₁ u₂ hu₁ hu₂ => ?_
  · unfold after
    refine rel_seq (rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by simp) (by taint_decide))
      (tested_wp hz₁) (tested_wp hz₂) fun y₁ y₂ ⟨hy₁, ev₁⟩ ⟨hy₂, ev₂⟩ => ?_
    rw [← hn] at ev₂
    refine rel_ite ev₁ ev₂ (fun _ => ?_) fun _ => ?_
    swap
    · exact rel_taint [] (by rw [hy₁.sp, hy₂.sp, hP]) (by simp) (by taint_decide)
    -- `wipe`, from the same public arguments.
    unfold wipe
    refine rel_seq (rel_taint [] (by rw [hy₁.sp, hy₂.sp, hP]) (by simp) (by taint_decide))
      (wipeArgs_wp h₁ hy₁) (wipeArgs_wp h₂ hy₂) fun w₁ w₂ hw₁ hw₂ => ?_
    exact rel_taint [.t2, .t3] (by rw [hw₁.sp, hw₂.sp, hy₁.sp, hy₂.sp, hP])
      (by
        simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        exact ⟨by rw [hw₁.t2, hw₂.t2, Dst, Dst, qa 0 (by decide)], by rw [hw₁.t3, hw₂.t3, L, L, q10]⟩)
      (by taint_decide)
  -- Our return address.
  exact rel_taint [] (by rw [hu₁.sp, hu₂.sp, hP]) (by simp) (by taint_decide)

end VG.Proof.AesGcm.RISCV64.OpenTo
