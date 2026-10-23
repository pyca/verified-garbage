module

public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Update
import VerifiedGarbage.Proof.CmacAes.PPC64LE.Finalize
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.CmacAes.PPC64LE.Update
meta import VerifiedGarbage.Proof.CmacAes.PPC64LE.Finalize
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys
meta import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys
public import VerifiedGarbage.Impl.CmacAes.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Contract

/-!
# AES-CMAC on PPC64LE: constant time

As for AES-CBC (`Proof/AesCbc/PPC64LE/CT.lean`): two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proofs pin to public values and the stack pointer, which no code
changes (`wp_sp`), and each call of `vg_aes_encrypt_blocks` is constant time
by its own proof (`blk_rel`). The branches of `update` are on `n`, and of
`finalize` on `last_len`, which are public.
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE
open VG.Impl.AesCbc.PPC64LE (save setup restore encCall)
open VG.Proof.AesCbc.PPC64LE (W R Iv Dp N S blk vars CallPre CallPost blk_call blk_rel taintRegs wp_sp)

/-! ## `vg_cmac_aes_subkeys` -/

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysPPC64LE.pre s₀) (h0' : subkeysPPC64LE.pre s₀')
    (hq : subkeysPPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') subkeys fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : SPre s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r15]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨q5, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) => SkMid s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => SkMid s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat s ∧
      s.sp = s₀'.sp)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (subkeysPre_wp hp), wp_sp (subkeysPre_wp hp')⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
      Proof.Aes.PPC64LE.encryptBlocks_ct (P := fun s₁ s₂ =>
      (SkMid s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat s₁ ∧ s₁.sp = s₀.sp) ∧
      (SkMid s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat s₂ ∧ s₂.sp = s₀'.sp)) fun s₁ s₂ h =>
      ⟨h.1.1.pre, h.2.1.pre, by rw [h.1.2, h.2.2, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r14 = s₀.gpr .r5 ∧ s.gpr .r15 = s₀.gpr .r6 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .r14 = s₀.gpr .r5 ∧ s.gpr .r15 = s₀.gpr .r6 ∧ s.sp = s₀'.sp)
    fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.1.1.pre)
        fun _ hc => ⟨by rw [hc.saved .r14 (by decide), h.1.1.r14], by rw [hc.saved .r15 (by decide), h.1.1.r15],
          by rw [hc.sp, h.1.2]⟩,
       WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.2.1.pre)
        fun _ hc => ⟨by rw [hc.saved .r14 (by decide), h.2.1.r14], by rw [hc.saved .r15 (by decide), h.2.1.r15],
          by rw [hc.sp, h.2.2]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .r14 = s₀.gpr .r5 ∧ s₁.gpr .r15 = s₀.gpr .r6 ∧ s₁.sp = s₀.sp) ∧
      (s₂.gpr .r14 = s₀.gpr .r5 ∧ s₂.gpr .r15 = s₀.gpr .r6 ∧ s₂.sp = s₀'.sp)) [.r14, .r15]
    (fun s₁ s₂ h => ⟨by rw [h.1.2.2, h.2.2.2, q5], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_ct : ConstantTime isa subkeysPPC64LE.pre subkeysPPC64LE.pub subkeys :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `vg_cmac_aes_finalize` -/

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizePPC64LE.pre s₀) (h0' : finalizePPC64LE.pre s₀')
    (hq : finalizePPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finalize fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : FPre s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat
      (s₀.gpr .r4).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14])
      (.block (finSaved.map (fun (r, d) => Instr.load .d r .r14 d) ++ [.mtlr .r0])) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6, .r7, .r8]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨q7, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) =>
      FMid s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat s ∧
        s.sp = s₀.sp)
    (F₂ := fun (s : State) =>
      FMid s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat s ∧
        s.sp = s₀'.sp)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (finPre_wp hp), wp_sp (finPre_wp hp')⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
      Proof.Aes.PPC64LE.encryptBlocks_ct (P := fun s₁ s₂ =>
      (FMid s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat s₁ ∧
        s₁.sp = s₀.sp) ∧
      (FMid s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat s₂ ∧
        s₂.sp = s₀'.sp)) fun s₁ s₂ h => ⟨h.1.1.pre, h.2.1.pre, by rw [h.1.2, h.2.2, q7]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r14 = s₀.gpr .r8 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .r14 = s₀.gpr .r8 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.1.1.pre)
        fun _ hc => ⟨by rw [hc.saved .r14 (by decide), h.1.1.r14], by rw [hc.sp, h.1.2]⟩,
       WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.2.1.pre)
        fun _ hc => ⟨by rw [hc.saved .r14 (by decide), h.2.1.r14], by rw [hc.sp, h.2.2]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .r14 = s₀.gpr .r8 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .r14 = s₀.gpr .r8 ∧ s₂.sp = s₀'.sp))
    [.r14] (fun s₁ s₂ h => ⟨by rw [h.1.2, h.2.2, q7], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finalize_ct : ConstantTime isa finalizePPC64LE.pre finalizePPC64LE.pub finalize :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `vg_cmac_aes_update` -/

section
variable {s₀ s₀' : State} (hq : updatePPC64LE.pub s₀ s₀')
include hq

theorem upub_W : W s₀ = W s₀' := hq.1
theorem upub_r4 : s₀.gpr .r4 = s₀'.gpr .r4 := hq.2.1
theorem upub_R : R s₀ = R s₀' := by rw [R, R, upub_r4 hq]
theorem upub_Iv : Iv s₀ = Iv s₀' := hq.2.2.1
theorem upub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem upub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem upub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem upub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2
theorem upub_blk (k : Nat) : blk s₀ k = blk s₀' k := by rw [blk, blk, upub_Dp hq]

theorem UInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : UInv s₀ k s₁) (h₂ : UInv s₀' k s₂) :
    ∀ r ∈ vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r14, h₂.r14, upub_W hq]
  · rw [h₁.r15, h₂.r15, upub_r4 hq]
  · rw [h₁.r16, h₂.r16, upub_Iv hq]
  · rw [h₁.r17, h₂.r17, upub_blk hq]
  · rw [h₁.r18, h₂.r18, upub_N hq]
  · rw [h₁.r19, h₂.r19, upub_S hq]

end

/-- The invariant, and the stack pointer on entry. -/
def US (s₀ : State) (k : Nat) (s : State) : Prop := UInv s₀ k s ∧ s.sp = s₀.sp

/-- What is known between the code before the call and the call. -/
structure UMid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : CallPre s (W s₀) (Iv s₀) (S s₀) (R s₀)
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp

/-- What is known after the call. -/
structure UAfter (s₀ : State) (k : Nat) (s : State) : Prop where
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp

theorem upd_body_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updatePPC64LE.pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ US s₀ k s₁ ∧ US s₀' k s₂) body fun s₁ s₂ =>
      US s₀ (k + 1) s₁ ∧ US s₀' (k + 1) s₂ := by
  have hN := upub_N hq
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs vars) (.block (Impl.AesCbc.PPC64LE.xorInto .r16 .r17 ++ updArgs))
    h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r17, .r18]) (.block Impl.AesCbc.PPC64LE.advance) h).isSome =
    true := ⟨_, by taint_decide⟩
  have mid (t : State) (ht : UPre t) (hk : k < N t) {s : State} (h : US t k s) :
      WP isa (.block (Impl.AesCbc.PPC64LE.xorInto .r16 .r17 ++ updArgs)) s (UMid t k) :=
    WP.mono (wp_sp (bodyPre_wp ht hk h.1)) fun s' ⟨⟨c, g, _, _, _⟩, e⟩ =>
      ⟨c, by rw [g _ (by decide), h.1.r17], by rw [g _ (by decide), h.1.r18], e.trans h.2⟩
  have a := (taintRegs (P := fun s₁ s₂ => k < N s₀ ∧ US s₀ k s₁ ∧ US s₀' k s₂) vars
    (fun _ _ h => ⟨by rw [h.2.1.2, h.2.2.2, upub_sp hq], UInv.agree hq h.2.1.1 h.2.2.1⟩) hA).wp
    (F₁ := UMid s₀ k) (F₂ := UMid s₀' k) fun _ _ h =>
      ⟨mid s₀ hp h.1 h.2.1, mid s₀' hp' (by rw [← hN]; exact h.1) h.2.2⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
    Proof.Aes.PPC64LE.encryptBlocks_ct (P := fun s₁ s₂ => UMid s₀ k s₁ ∧ UMid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [upub_W hq, upub_Iv hq, upub_S hq, upub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, upub_sp hq]⟩).wp
    (F₁ := UAfter s₀ k) (F₂ := UAfter s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.1.pre)
        fun _ hc => ⟨by rw [hc.saved .r17 (by decide), h.1.r17], by rw [hc.saved .r18 (by decide), h.1.r18],
          hc.sp.trans h.1.sp⟩,
       WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.2.pre)
        fun _ hc => ⟨by rw [hc.saved .r17 (by decide), h.2.r17], by rw [hc.saved .r18 (by decide), h.2.r18],
          hc.sp.trans h.2.sp⟩⟩
  have b := taintRegs (P := fun s₁ s₂ => UAfter s₀ k s₁ ∧ UAfter s₀' k s₂) [.r17, .r18]
    (fun s₁ s₂ h => ⟨by rw [h.1.sp, h.2.sp, upub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r17, h.2.r17, upub_blk hq]
      · rw [h.1.r18, h.2.r18, upub_N hq]⟩) hB
  have whole := (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)
  exact (whole.wp (F₁ := US s₀ (k + 1)) (F₂ := US s₀' (k + 1)) fun s₁ s₂ h =>
    ⟨WP.mono (wp_sp (body_ok hp h.1 h.2.1.1)) fun _ ⟨l, e⟩ => ⟨l, e.trans h.2.1.2⟩,
     WP.mono (wp_sp (body_ok hp' (by rw [← hN]; exact h.1) h.2.2.1)) fun _ ⟨l, e⟩ => ⟨l, e.trans h.2.2.2⟩⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- The loop's relation, with the number of iterations left. -/
def URel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ US s₀ k s₁ ∧ US s₀' k s₂

theorem upd_loop_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updatePPC64LE.pub s₀ s₀') (n : Nat) :
    RelCT isa (URel s₀ s₀' n) (.loop body (.nonzero .d .r18))
      fun s₁ s₂ => US s₀ (N s₀) s₁ ∧ US s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (URel s₀ s₀') (fun n => ?_) n
  have hN := upub_N hq
  have hb₀ := (s₀.gpr .r7).isLt
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : URel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  refine (upd_body_ct hp hp' hq k).mono (fun _ _ h => h.2) fun s₁ s₂ ⟨l₁, l₂⟩ => ?_
  have bd : N s₀ - (k + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb₀
  have e₁ := eval_nonzero_ofNat' s₁ .r18 bd l₁.1.r18
  have e₂ := eval_nonzero_ofNat' s₂ .r18 (k := N s₀ - (k + 1)) bd (by rw [l₂.1.r18, hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, by omega, l₁, l₂⟩

theorem update_rel {s₀ s₀' : State} (h0 : updatePPC64LE.pre s₀) (h0' : updatePPC64LE.pre s₀')
    (hq : updatePPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') update fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := upub_N hq
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.r19]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩
  have pro := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6, .r7, .r8]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨upub_sp hq, fun r hr => ?_⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := US s₀ 0) (F₂ := US s₀' 0)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨wp_sp (prologue_wp hp), wp_sp (prologue_wp hp')⟩
  have ev {t : State} {s : State} (h : US t 0 s) : isa.eval (.zero .d .r18) s = some (decide (N t = 0)) := by
    have := eval_zero_ofNat s .r18 (k := N t - 0) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (t.gpr .r7).isLt)
      h.1.r18
    rwa [Nat.sub_zero] at this
  have nil := taintRegs (P := fun a b => (US s₀ 0 a ∧ US s₀' 0 b) ∧ isa.eval (.zero .d .r18) a = some true) []
    (fun _ _ h => ⟨by rw [h.1.1.2, h.1.2.2, upub_sp hq], fun r hr => by simp at hr⟩) hnil
  have mid : RelCT isa (fun a b => US s₀ 0 a ∧ US s₀' 0 b)
      (.ite (.zero .d .r18) (.block []) (.loop body (.nonzero .d .r18)))
      (fun a b => US s₀ (N s₀) a ∧ US s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1, ev h.2, hN]) ?_ ?_
    · refine (nil.wp (F₁ := US s₀ (N s₀)) (F₂ := US s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (RelCT.exists_ (P := fun (_ : 0 < N s₀) a b => US s₀ 0 a ∧ US s₀' 0 b) fun hn =>
          (upd_loop_ct hp hp' hq (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hn, h.1, h.2⟩) fun _ _ h => h).mono
        (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := taintRegs (P := fun a b => US s₀ (N s₀) a ∧ US s₀' (N s₀') b) [.r19]
    (fun a b h => ⟨by rw [h.1.2, h.2.2, upub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1.r19, h.2.1.r19, upub_S hq]⟩) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem update_ct : ConstantTime isa updatePPC64LE.pre updatePPC64LE.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.PPC64LE
