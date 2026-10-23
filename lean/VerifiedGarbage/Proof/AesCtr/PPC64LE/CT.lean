module

import VerifiedGarbage.Proof.AesCtr.PPC64LE.Iter
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.AesCtr.PPC64LE.Iter
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Body

/-!
# AES-CTR on PPC64LE: constant time

As on x86-64 (`Proof/AesCtr/X86_64/CT.lean`): two runs from states that
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

namespace VG.Proof.AesCtr.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCtr.PPC64LE
open VG.Proof.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat)

/-- What two runs agree on: the public arguments, and the last 32 bits of the
counter block. -/
def ctrPub (s₀ s₀' : State) : Prop :=
  (modePPC64LE AesCtr.ctrMode).pub s₀ s₀' ∧ AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀')

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block (count ++ args)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem adv_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block adv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem carry_taint : ∃ h, (taint.check (Taint.ofRegs [.r16]) (.block carry) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (hq : (modePPC64LE AesCtr.ctrMode).pub s₀ s₀')
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
    RelCT isa (fun a b => LS AesCtr.ctrMode s₀ k a ∧ LS AesCtr.ctrMode s₀' k b) body
      fun a b => LS AesCtr.ctrMode s₀ (k + mOf s₀ k) a ∧ LS AesCtr.ctrMode s₀' (k + mOf s₀' k) b := by
  have hk' : k < N s₀' := by rw [← pub_N hq]; exact hk
  obtain ⟨_, t1⟩ := pre_taint
  obtain ⟨_, t3⟩ := adv_taint
  obtain ⟨_, tc⟩ := carry_taint
  obtain ⟨_, tn⟩ := nil_taint
  -- The code before the call.
  have p1 := (taintRegs (P := fun a b => LS AesCtr.ctrMode s₀ k a ∧ LS AesCtr.ctrMode s₀' k b) vars
    (fun _ _ h => ⟨by rw [h.1.2, h.2.2, pub_sp hq], LInv.agree hq h.1.1 h.2.1⟩) t1).wp
    (F₁ := fun (s₁ : State) => ∃ s, LS AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s s₁ ∧ s₁.sp = s.sp)
    (F₂ := fun (s₁ : State) => ∃ s, LS AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s s₁ ∧ s₁.sp = s.sp)
    fun a b h => ⟨WP.mono (wp_sp (pre_wp hp hk h.1.1)) fun _ ⟨x, e⟩ => ⟨a, h.1, x, e⟩,
      WP.mono (wp_sp (pre_wp hp' hk' h.2.1)) fun _ ⟨x, e⟩ => ⟨b, h.2, x, e⟩⟩
  -- The call, with the same arguments in both runs.
  have p2 := (ctr_rel (K := W s₀) (C := Iv s₀) (D := blk s₀ k) (S := S s₀) (R := R s₀) (n := mOf s₀ k)
    (P := fun a b => (∃ s, LS AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s a ∧ a.sp = s.sp) ∧
      (∃ s, LS AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s b ∧ b.sp = s.sp)) fun a b h => by
    obtain ⟨⟨s, hs, pa, ea⟩, ⟨t, ht, pb, eb⟩⟩ := h
    refine ⟨pa.call, ?_, by rw [ea, eb, hs.2, ht.2, pub_sp hq]⟩
    rw [pub_W hq, pub_Iv hq, pub_blk hq, pub_S hq, pub_R hq, mOf_eq hq hl]; exact pb.call).wp
    (F₁ := fun (s : State) => Mid s₀ k s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => Mid s₀' k s ∧ s.sp = s₀'.sp) fun a b h => by
      obtain ⟨⟨s, hs, pa, ea⟩, ⟨t, ht, pb, eb⟩⟩ := h
      exact ⟨WP.mono (wp_sp (mid_wp hp hk hs.1 pa)) fun _ ⟨x, e⟩ => ⟨x, e.trans (ea.trans hs.2)⟩,
        WP.mono (wp_sp (mid_wp hp' hk' ht.1 pb)) fun _ ⟨x, e⟩ => ⟨x, e.trans (eb.trans ht.2)⟩⟩
  -- On past the call's blocks.
  have p3 := (taintRegs (P := fun a b => (Mid s₀ k a ∧ a.sp = s₀.sp) ∧ (Mid s₀' k b ∧ b.sp = s₀'.sp))
    [.r16, .r17, .r18, .r19] (fun a b h => ⟨by rw [h.1.2, h.2.2, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.1.r16, h.2.1.r16, pub_Iv hq]
      · rw [h.1.1.r17, h.2.1.r17, pub_blk hq]
      · rw [h.1.1.r18, h.2.1.r18, pub_N hq]
      · rw [h.1.1.r19, h.2.1.r19, pub_S hq]⟩) t3).wp
    (F₁ := fun (s₂ : State) => ∃ s, (Mid s₀ k s ∧ s.sp = s₀.sp) ∧ After s₀ k s s₂ ∧ s₂.sp = s.sp)
    (F₂ := fun (s₂ : State) => ∃ s, (Mid s₀' k s ∧ s.sp = s₀'.sp) ∧ After s₀' k s s₂ ∧ s₂.sp = s.sp)
    fun a b h => ⟨WP.mono (wp_sp (adv_wp' hp hk h.1.1)) fun _ ⟨x, e⟩ => ⟨a, h.1, x, e⟩,
      WP.mono (wp_sp (adv_wp' hp' hk' h.2.1)) fun _ ⟨x, e⟩ => ⟨b, h.2, x, e⟩⟩
  -- The carry if the counter wrapped around in both runs.
  have p4 : RelCT isa (fun a b => (∃ s, (Mid s₀ k s ∧ s.sp = s₀.sp) ∧ After s₀ k s a ∧ a.sp = s.sp) ∧
      (∃ s, (Mid s₀' k s ∧ s.sp = s₀'.sp) ∧ After s₀' k s b ∧ b.sp = s.sp))
      (.ite (.zero .d .r9) (.block carry) (.block [])) fun _ _ => True := by
    refine RelCT.ite (fun a b h => ?_) (taintRegs [.r16] (fun a b h => ?_) tc)
      (taintRegs [] (fun a b h => ?_) tn)
    · obtain ⟨⟨s, hs, xa, -⟩, ⟨t, ht, xb, -⟩⟩ := h
      rw [xa.ev, xb.ev, lo32_next_eq hl, mOf_eq hq hl]
    · obtain ⟨⟨⟨s, hs, xa, ea⟩, ⟨t, ht, xb, eb⟩⟩, _⟩ := h
      refine ⟨by rw [ea, eb, hs.2, ht.2, pub_sp hq], fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst hr
      rw [xa.gpr _ (by decide) (by decide) (by decide) (by decide),
        xb.gpr _ (by decide) (by decide) (by decide) (by decide), hs.1.r16, ht.1.r16, pub_Iv hq]
    · obtain ⟨⟨⟨s, hs, xa, ea⟩, ⟨t, ht, xb, eb⟩⟩, _⟩ := h
      exact ⟨by rw [ea, eb, hs.2, ht.2, pub_sp hq], fun r hr => by simp at hr⟩
  have p5 := p4.wp (F₁ := LS AesCtr.ctrMode s₀ (k + mOf s₀ k)) (F₂ := LS AesCtr.ctrMode s₀' (k + mOf s₀' k))
    fun a b h => by
      obtain ⟨⟨s, hs, xa, ea⟩, ⟨t, ht, xb, eb⟩⟩ := h
      exact ⟨WP.mono (wp_sp (fin_wp hp hk hs.1 xa)) fun _ ⟨x, e⟩ => ⟨x, e.trans (ea.trans hs.2)⟩,
        WP.mono (wp_sp (fin_wp hp' hk' ht.1 xb)) fun _ ⟨x, e⟩ => ⟨x, e.trans (eb.trans ht.2)⟩⟩
  exact (p1.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((p2.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((p3.mono (fun _ _ h => h) fun _ _ h => h.2).seq (p5.mono (fun _ _ h => h) fun _ _ h => h.2)))

/-- The loop's relation, with the number of blocks left. -/
def CRel (s₀ s₀' : State) (n : Nat) (a b : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LS AesCtr.ctrMode s₀ k a ∧ LS AesCtr.ctrMode s₀' k b

theorem loop_rel (hp : UPre s₀) (hp' : UPre s₀') (n : Nat) :
    RelCT isa (CRel s₀ s₀' n) (.loop body (.nonzero .d .r18))
      fun a b => LS AesCtr.ctrMode s₀ (N s₀) a ∧ LS AesCtr.ctrMode s₀' (N s₀') b := by
  refine RelCT.loop (M := isa) (CRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hb₀ := (s₀.gpr .r7).isLt
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
  have e₁ := eval_nonzero_ofNat' s₁ .r18 bd l₁.1.r18
  have e₂ := eval_nonzero_ofNat' s₂ .r18 (k := N s₀ - (k + mOf s₀ k)) bd (by rw [l₂.1.r18, hN])
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
theorem crypt_rel {s₀ s₀' : State} (h0 : (modePPC64LE AesCtr.ctrMode).pre s₀)
    (h0' : (modePPC64LE AesCtr.ctrMode).pre s₀') (hq : ctrPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') crypt fun _ _ => True :=
  ends_rel h0 h0' hq.1 fun hp hp' hN =>
    (loop_rel hq.1 hq.2 hp hp' (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hN, h.1, h.2⟩) fun _ _ h => h

theorem crypt_ct : ConstantTime isa (modePPC64LE AesCtr.ctrMode).pre ctrPub crypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (crypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCtr.PPC64LE
