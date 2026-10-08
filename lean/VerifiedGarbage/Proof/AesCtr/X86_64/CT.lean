import VerifiedGarbage.Proof.AesCtr.X86_64.Iter
import VerifiedGarbage.Proof.AesCbc.X86_64.CT

/-!
# AES-CTR on x86-64: constant time

Two runs from states that agree on the public arguments and on the last 32
bits of the counter block (`ctrPub`, which the contract's `leak` declares)
are related piece by piece (`RelCT`): the taint analysis covers the code
between the call and the branches, from the registers the correctness proof
pins to the public arguments; the call is constant time by its own proof
(AES-GCM's `ctr_rel`), with the same arguments in both runs, since the
number of blocks it takes depends only on the public data (`mOf_eq`); and
the branches (the carry, the loop) are on facts the correctness proof gives
in terms of the public data (`After.zf`, `iter_wp`).
-/

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (save setup restore)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.AesGcm.X86_64 (ctr_rel)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat)

/-- What two runs agree on: the public arguments, and the last 32 bits of the
counter block. -/
def ctrPub (s₀ s₀' : State) : Prop :=
  (modeX86_64 AesCtr.ctrMode).pub s₀ s₀' ∧ AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀')

/-- A piece of code the taint analysis checks from the registers `rs`, which
agree in two runs, with what each run reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true)
    (ha : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := taint) (P := P) _ (fun s₁ s₂ h => Taint.agree_ofRegs (ha s₁ s₂ h)) ht).wp hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
    (.block (count ++ args)) h).isSome = true := ⟨_, by taint_decide⟩

theorem adv_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15, .rsp]) (.block adv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem carry_taint : ∃ h, (taint.check (Taint.ofRegs [.r12]) (.block carry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩

theorem test_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block [.alu .test .r14 (.reg .r14)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (hq : (modeX86_64 AesCtr.ctrMode).pub s₀ s₀')
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
theorem body_rel (v : Ctr32Impl) (hp : UPre s₀) (hp' : UPre s₀') {k : Nat} (hk : k < N s₀) :
    RelCT isa (fun a b => LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b) (body v.callee)
      fun a b => (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) a ∧ a.zf = some (decide (k + mOf s₀ k = N s₀))) ∧
        (LInv AesCtr.ctrMode s₀' (k + mOf s₀' k) b ∧ b.zf = some (decide (k + mOf s₀' k = N s₀'))) := by
  have hk' : k < N s₀' := by rw [← pub_N hq]; exact hk
  -- The code before the call.
  have p1 := taint_rel _ pre_taint (P := fun a b => LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b)
    (fun _ _ h => LInv.agree hq h.1 h.2)
    (F₁ := fun s₁ => ∃ s, LInv AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s s₁)
    (F₂ := fun s₁ => ∃ s, LInv AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s s₁)
    fun a b h => ⟨WP.mono (pre_wp hp hk h.1) fun _ x => ⟨a, h.1, x⟩,
      WP.mono (pre_wp hp' hk' h.2) fun _ x => ⟨b, h.2, x⟩⟩
  -- The call, with the same arguments in both runs.
  have p2 := (ctr_rel v (P := fun a b => (∃ s, LInv AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s a) ∧
      (∃ s, LInv AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s b)) fun a b h => by
    obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
    refine ⟨_, _, _, _, _, _, pa.call, ?_, ?_⟩
    · rw [pub_W hq, pub_Iv hq, pub_blk hq, pub_S hq, pub_R hq, mOf_eq hq hl]; exact pb.call
    · rw [pa.saved .rsp (by simp [calleeSaved]), pb.saved .rsp (by simp [calleeSaved]), hs.rsp, ht.rsp,
        pub_rsp hq]).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun a b h => by
      obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
      exact ⟨mid_wp hp v hk hs pa, mid_wp hp' v hk' ht pb⟩
  -- On past the call's blocks.
  have p3 := taint_rel _ adv_taint (P := fun a b => Mid s₀ k a ∧ Mid s₀' k b)
    (fun a b h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.r12, h.2.r12, pub_Iv hq]
      · rw [h.1.r13, h.2.r13, pub_blk hq]
      · rw [h.1.r14, h.2.r14, pub_N hq]
      · rw [h.1.r15, h.2.r15, pub_S hq]
      · rw [h.1.rsp, h.2.rsp, pub_rsp hq])
    (F₁ := fun s₂ => ∃ s, Mid s₀ k s ∧ After s₀ k s s₂) (F₂ := fun s₂ => ∃ s, Mid s₀' k s ∧ After s₀' k s s₂)
    fun a b h => ⟨WP.mono (adv_wp hp hk h.1) fun _ x => ⟨a, h.1, x⟩,
      WP.mono (adv_wp hp' hk' h.2) fun _ x => ⟨b, h.2, x⟩⟩
  -- The carry if the counter wrapped around in both runs, and the test.
  have p4 : RelCT isa (fun a b => (∃ s, Mid s₀ k s ∧ After s₀ k s a) ∧ (∃ s, Mid s₀' k s ∧ After s₀' k s b))
      (.seq (.ite .e (.block carry) (.block [])) (.block [.alu .test .r14 (.reg .r14)])) fun _ _ => True := by
    obtain ⟨_, hc⟩ := carry_taint
    obtain ⟨_, hn⟩ := nil_taint
    obtain ⟨_, ht⟩ := test_taint
    refine RelCT.seq (R := fun _ _ => True) (RelCT.ite (fun a b h => ?_)
      (RelCT.taint (A := taint) _ (fun a b h => Taint.agree_ofRegs fun r hr => ?_) hc)
      (RelCT.taint (A := taint) _ (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hn))
      (RelCT.taint (A := taint) _ (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) ht)
    · obtain ⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩ := h
      show a.zf = b.zf
      rw [xa.zf, xb.zf, lo32_next_eq hl, mOf_eq hq hl]
    · obtain ⟨⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩, _⟩ := h
      simp only [List.mem_singleton] at hr; subst hr
      rw [xa.gpr _ (by decide) (by decide) (by decide), xb.gpr _ (by decide) (by decide) (by decide), hs.r12, ht'.r12,
        pub_Iv hq]
  have p5 := p4.wp
    (F₁ := fun (s' : State) => LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) s' ∧ s'.zf = some (decide (k + mOf s₀ k = N s₀)))
    (F₂ := fun (s' : State) => LInv AesCtr.ctrMode s₀' (k + mOf s₀' k) s' ∧ s'.zf = some (decide (k + mOf s₀' k = N s₀')))
    fun a b h => by
      obtain ⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩ := h
      exact ⟨fin_wp hp hk hs xa, fin_wp hp' hk' ht' xb⟩
  exact p1.seq ((p2.mono (fun _ _ h => h) fun _ _ h => h.2).seq (p3.seq (p5.mono (fun _ _ h => h) fun _ _ h => h.2)))

/-- The loop's relation, with the number of blocks left. -/
def LRel (s₀ s₀' : State) (n : Nat) (a b : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b

theorem loop_rel (v : Ctr32Impl) (hp : UPre s₀) (hp' : UPre s₀') (n : Nat) :
    RelCT isa (LRel s₀ s₀' n) (.loop (body v.callee) .ne)
      fun a b => LInv AesCtr.ctrMode s₀ (N s₀) a ∧ LInv AesCtr.ctrMode s₀' (N s₀') b := by
  refine RelCT.loop (M := isa) (LRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
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
  refine (body_rel hq hl v hp hp' hk).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩)
    fun s₁ s₂ ⟨⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  rw [← hm] at l₂
  rw [← hm, ← hN] at z₂
  have e₁ : isa.eval .ne s₁ = some !decide (k + mOf s₀ k = N s₀) := by
    show VG.X86_64.eval .ne s₁ = _; simp [VG.X86_64.eval, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (k + mOf s₀ k = N s₀) := by
    show VG.X86_64.eval .ne s₂ = _; simp [VG.X86_64.eval, z₂]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + mOf s₀ k = N s₀ := by simpa using hf
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : k + mOf s₀ k ≠ N s₀ := by simpa using ht
    exact ⟨N s₀ - (k + mOf s₀ k), by omega, k + mOf s₀ k, rfl, by omega, l₁, l₂⟩

end

/-- The whole function, in two runs that agree on the public data. -/
theorem crypt_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : (modeX86_64 AesCtr.ctrMode).pre s₀)
    (h0' : (modeX86_64 AesCtr.ctrMode).pre s₀') (hq : ctrPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (crypt v.callee) fun _ _ => True :=
  ends_rel h0 h0' hq.1 fun hp hp' hN =>
    (loop_rel hq.1 hq.2 v hp hp' (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hN, h.1, h.2⟩) fun _ _ h => h

theorem crypt_ct (v : Ctr32Impl) :
    ConstantTime isa (modeX86_64 AesCtr.ctrMode).pre ctrPub (crypt v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (crypt_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCtr.X86_64
