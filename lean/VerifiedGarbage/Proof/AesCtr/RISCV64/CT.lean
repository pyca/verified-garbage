module

import VerifiedGarbage.Proof.AesCtr.RISCV64.Iter
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Iter
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Body
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# AES-CTR on RISC-V: constant time

As on PPC64LE (`Proof/AesCtr/PPC64LE/CT.lean`): two runs from states that
agree on the public arguments and on the last 32 bits of the counter block
(`ctrPub`, which the contract's `leak` declares) are related piece by piece
(`RelCT`): the taint analysis covers the code between the call and the
branches, from the registers the correctness proof pins to the public
arguments and the stack pointer; the call is constant time by its own proof
(`ctr_rel`), with the same arguments in both runs, since the number of blocks
it takes depends only on the public data (`mOf_eq`); and the branches (the
carry, the loop) are on facts the correctness proof gives in terms of the
public data (`After.ev`, `iter_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64

open VG VG.RISCV64 VG.Impl.AesCtr.RISCV64
open VG.Proof.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat)

/-- What two runs agree on: the public arguments, and the last 32 bits of the
counter block. -/
def ctrPub (s₀ s₀' : State) : Prop :=
  (modeRISCV64 AesCtr.ctrMode).pub s₀ s₀' ∧ AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀')

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block (count ++ args)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem adv_taint : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6]) (.block adv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem carry_taint : ∃ h, (taint.check (Taint.ofRegs [.s3]) (.block carry) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (hq : (modeRISCV64 AesCtr.ctrMode).pub s₀ s₀')
  (hl : AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀'))
include hq hl

omit hq in
theorem lo32_next_eq (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) = AesCtr.lo32 (next (iv0 s₀') k) := by
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)]
  unfold AesCtr.lo32 at hl
  omega

theorem mOf_eq (k : Nat) : mOf s₀ k = mOf s₀' k := by
  have e := lo32_next_eq hl k
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)] at e
  unfold mOf
  rw [e, pub_N hq]

/-- One iteration, in two runs. -/
theorem body_rel (hp : UPre s₀) (hp' : UPre s₀') {k : Nat} (hk : k < N s₀) :
    RelCT isa (fun a b => LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b) body
      fun a b => LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) a ∧ LInv AesCtr.ctrMode s₀' (k + mOf s₀' k) b := by
  have hk' : k < N s₀' := by rw [← pub_N hq]; exact hk
  obtain ⟨_, t1⟩ := pre_taint
  obtain ⟨_, t3⟩ := adv_taint
  obtain ⟨_, tc⟩ := carry_taint
  obtain ⟨_, tn⟩ := nil_taint
  -- The code before the call.
  have p1 := (taintRegs (P := fun a b => LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b) vars
    (fun _ _ h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], LInv.agree hq h.1 h.2⟩) t1).wp
    (F₁ := fun (s₁ : State) => ∃ s, LInv AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s s₁)
    (F₂ := fun (s₁ : State) => ∃ s, LInv AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s s₁)
    fun a b h => ⟨WP.mono (pre_wp hp hk h.1) fun _ x => ⟨a, h.1, x⟩,
      WP.mono (pre_wp hp' hk' h.2) fun _ x => ⟨b, h.2, x⟩⟩
  -- The call, with the same arguments in both runs.
  have p2 := (ctr_rel (K := W s₀) (C := Iv s₀) (D := blk s₀ k) (S := S s₀) (R := R s₀) (n := mOf s₀ k)
    (P := fun a b => (∃ s, LInv AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s a) ∧
      (∃ s, LInv AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s b)) fun a b h => by
    obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
    refine ⟨pa.call, ?_, by rw [pa.sp, pb.sp, hs.sp, ht.sp, pub_sp hq]⟩
    rw [pub_W hq, pub_Iv hq, pub_blk hq, pub_S hq, pub_R hq, mOf_eq hq hl]; exact pb.call).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun a b h => by
      obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
      exact ⟨mid_wp hp hk hs pa, mid_wp hp' hk' ht pb⟩
  -- On past the call's blocks.
  have p3 := (taintRegs (P := fun a b => Mid s₀ k a ∧ Mid s₀' k b)
    [.s3, .s4, .s5, .s6] (fun a b h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.s3, h.2.s3, pub_Iv hq]
      · rw [h.1.s4, h.2.s4, pub_blk hq]
      · rw [h.1.s5, h.2.s5, pub_N hq]
      · rw [h.1.s6, h.2.s6, pub_S hq]⟩) t3).wp
    (F₁ := fun (s₂ : State) => ∃ s, Mid s₀ k s ∧ After s₀ k s s₂)
    (F₂ := fun (s₂ : State) => ∃ s, Mid s₀' k s ∧ After s₀' k s s₂)
    fun a b h => ⟨WP.mono (adv_wp' hp hk h.1) fun _ x => ⟨a, h.1, x⟩,
      WP.mono (adv_wp' hp' hk' h.2) fun _ x => ⟨b, h.2, x⟩⟩
  -- The carry if the counter wrapped around in both runs.
  have p4 : RelCT isa (fun a b => (∃ s, Mid s₀ k s ∧ After s₀ k s a) ∧ (∃ s, Mid s₀' k s ∧ After s₀' k s b))
      (.ite (.zero .t1) (.block carry) (.block [])) fun _ _ => True := by
    refine RelCT.ite (fun a b h => ?_) (taintRegs [.s3] (fun a b h => ?_) tc)
      (taintRegs [] (fun a b h => ?_) tn)
    · obtain ⟨⟨s, hs, xa⟩, ⟨t, ht, xb⟩⟩ := h
      rw [xa.ev, xb.ev, lo32_next_eq hl, mOf_eq hq hl]
    · obtain ⟨⟨⟨s, hs, xa⟩, ⟨t, ht, xb⟩⟩, _⟩ := h
      refine ⟨by rw [xa.sp, xb.sp, hs.sp, ht.sp, pub_sp hq], fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst hr
      rw [xa.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide),
        xb.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), hs.s3, ht.s3, pub_Iv hq]
    · obtain ⟨⟨⟨s, hs, xa⟩, ⟨t, ht, xb⟩⟩, _⟩ := h
      exact ⟨by rw [xa.sp, xb.sp, hs.sp, ht.sp, pub_sp hq], fun r hr => by simp at hr⟩
  have p5 := p4.wp (F₁ := LInv AesCtr.ctrMode s₀ (k + mOf s₀ k))
    (F₂ := LInv AesCtr.ctrMode s₀' (k + mOf s₀' k)) fun a b h => by
      obtain ⟨⟨s, hs, xa⟩, ⟨t, ht, xb⟩⟩ := h
      exact ⟨fin_wp hp hk hs xa, fin_wp hp' hk' ht xb⟩
  exact (p1.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((p2.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((p3.mono (fun _ _ h => h) fun _ _ h => h.2).seq (p5.mono (fun _ _ h => h) fun _ _ h => h.2)))

/-- The loop's relation, with the number of blocks left. -/
def CRel (s₀ s₀' : State) (n : Nat) (a b : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b

theorem loop_rel (hp : UPre s₀) (hp' : UPre s₀') (n : Nat) :
    RelCT isa (CRel s₀ s₀' n) (.loop body (.nonzero .s5))
      fun a b => LInv AesCtr.ctrMode s₀ (N s₀) a ∧ LInv AesCtr.ctrMode s₀' (N s₀') b := by
  refine RelCT.loop (M := isa) (CRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hb₀ := (s₀.gpr .a4).isLt
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : CRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have hm := mOf_eq hq hl k
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  refine (body_rel hq hl hp hp' hk).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun s₁ s₂ ⟨l₁, l₂⟩ => ?_
  rw [← hm] at l₂
  have bd : N s₀ - (k + mOf s₀ k) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb₀
  have e₁ := Steps.eval_nonzero_ofNat s₁ .s5 bd l₁.s5
  have e₂ := Steps.eval_nonzero_ofNat s₂ .s5 (k := N s₀ - (k + mOf s₀ k)) bd (by rw [l₂.s5, hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + mOf s₀ k = N s₀ := by
      have : N s₀ - (k + mOf s₀ k) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + mOf s₀ k) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + mOf s₀ k), by omega, k + mOf s₀ k, rfl, by omega, l₁, l₂⟩

end

/-- The whole function, in two runs that agree on the public data. -/
theorem crypt_rel {s₀ s₀' : State} (h0 : (modeRISCV64 AesCtr.ctrMode).pre s₀)
    (h0' : (modeRISCV64 AesCtr.ctrMode).pre s₀') (hq : ctrPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') crypt fun _ _ => True :=
  ends_rel h0 h0' hq.1 fun hp hp' hN =>
    (loop_rel hq.1 hq.2 hp hp' (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hN, h.1, h.2⟩) fun _ _ h => h

theorem crypt_ct : ConstantTime isa (modeRISCV64 AesCtr.ctrMode).pre ctrPub crypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (crypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCtr.RISCV64
