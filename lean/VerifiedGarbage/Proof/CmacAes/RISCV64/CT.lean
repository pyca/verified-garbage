module

public import VerifiedGarbage.Proof.CmacAes.RISCV64.Update
import VerifiedGarbage.Proof.CmacAes.RISCV64.Finalize
import VerifiedGarbage.Proof.CmacAes.RISCV64.Subkeys
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
meta import VerifiedGarbage.Proof.CmacAes.RISCV64.Update
meta import VerifiedGarbage.Proof.CmacAes.RISCV64.Finalize
meta import VerifiedGarbage.Proof.CmacAes.RISCV64.Subkeys
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Impl.CmacAes.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.CmacAes.RISCV64.Contract

/-!
# AES-CMAC on RISC-V: constant time

As on PPC64LE (`Proof/CmacAes/PPC64LE/CT.lean`): two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proofs pin to public values and the stack pointer, which no code
changes (`wp_sp`), and each call of `vg_aes_encrypt_blocks` is constant time
by its own proof (`blk_rel`). The branches of `update` are on `n`, and of
`finalize` on `last_len`, which are public.
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64 VG.Impl.CmacAes.RISCV64
open VG.Impl.AesCbc.RISCV64 (save setup restore encCall)
open VG.Proof.AesCbc.RISCV64 (W R Iv Dp N S vars CallPre CallPost blk_call blk_rel taintRegs wp_sp
  encryptBlocks_noFrames)

/-! ## `vg_cmac_aes_subkeys` -/

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysRISCV64.pre s₀) (h0' : subkeysRISCV64.pre s₀')
    (hq : subkeysRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') subkeys fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : SPre s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨q5, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := SkMid s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat)
    (F₂ := SkMid s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨subkeysPre_wp hp, subkeysPre_wp hp'⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
      Proof.Aes.RISCV64.encryptBlocks_ct (P := fun s₁ s₂ =>
      SkMid s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat s₁ ∧
      SkMid s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = s₀.gpr .a2 ∧ s.gpr .s2 = s₀.gpr .a3 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = s₀.gpr .a2 ∧ s.gpr .s2 = s₀.gpr .a3 ∧ s.sp = s₀'.sp)
    fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames h.1.pre)
        fun _ hc => ⟨by rw [hc.saved .s1 (by decide), h.1.s1], by rw [hc.saved .s2 (by decide), h.1.s2],
          by rw [hc.sp, h.1.sp]⟩,
       WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames h.2.pre)
        fun _ hc => ⟨by rw [hc.saved .s1 (by decide), h.2.s1], by rw [hc.saved .s2 (by decide), h.2.s2],
          by rw [hc.sp, h.2.sp]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .s1 = s₀.gpr .a2 ∧ s₁.gpr .s2 = s₀.gpr .a3 ∧ s₁.sp = s₀.sp) ∧
      (s₂.gpr .s1 = s₀.gpr .a2 ∧ s₂.gpr .s2 = s₀.gpr .a3 ∧ s₂.sp = s₀'.sp)) [.s1, .s2]
    (fun s₁ s₂ h => ⟨by rw [h.1.2.2, h.2.2.2, q5], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_ct : ConstantTime isa subkeysRISCV64.pre subkeysRISCV64.pub subkeys :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `vg_cmac_aes_finalize` -/

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizeRISCV64.pre s₀) (h0' : finalizeRISCV64.pre s₀')
    (hq : finalizeRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finalize fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : FPre s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat
      (s₀.gpr .a1).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1]) (.block finRestore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4, .a5]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨q7, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := FMid s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat)
    (F₂ := FMid s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
      Proof.Aes.RISCV64.encryptBlocks_ct (P := fun s₁ s₂ =>
      FMid s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat s₁ ∧
      FMid s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat s₂)
      fun s₁ s₂ h => ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q7]⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = s₀.gpr .a5 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = s₀.gpr .a5 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames h.1.pre)
        fun _ hc => ⟨by rw [hc.saved .s1 (by decide), h.1.s1], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames h.2.pre)
        fun _ hc => ⟨by rw [hc.saved .s1 (by decide), h.2.s1], by rw [hc.sp, h.2.sp]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .s1 = s₀.gpr .a5 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .s1 = s₀.gpr .a5 ∧ s₂.sp = s₀'.sp))
    [.s1] (fun s₁ s₂ h => ⟨by rw [h.1.2, h.2.2, q7], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finalize_ct : ConstantTime isa finalizeRISCV64.pre finalizeRISCV64.pub finalize :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `vg_cmac_aes_update` -/

section
variable {s₀ s₀' : State} (hq : updateRISCV64.pub s₀ s₀')
include hq

theorem upub_W : W s₀ = W s₀' := hq.1
theorem upub_a1 : s₀.gpr .a1 = s₀'.gpr .a1 := hq.2.1
theorem upub_R : R s₀ = R s₀' := by rw [R, R, upub_a1 hq]
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
  · rw [h₁.s1, h₂.s1, upub_W hq]
  · rw [h₁.s2, h₂.s2, upub_a1 hq]
  · rw [h₁.s3, h₂.s3, upub_Iv hq]
  · rw [h₁.s4, h₂.s4, upub_blk hq]
  · rw [h₁.s5, h₂.s5, upub_N hq]
  · rw [h₁.s6, h₂.s6, upub_S hq]

end

/-- What is known between the code before the call and the call. -/
structure UMid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : CallPre s (W s₀) (Iv s₀) (S s₀) (R s₀)
  s4 : s.gpr .s4 = blk s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp

/-- What is known after the call. -/
structure UAfter (s₀ : State) (k : Nat) (s : State) : Prop where
  s4 : s.gpr .s4 = blk s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp

theorem upd_body_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updateRISCV64.pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ UInv s₀ k s₁ ∧ UInv s₀' k s₂) body fun s₁ s₂ =>
      UInv s₀ (k + 1) s₁ ∧ UInv s₀' (k + 1) s₂ := by
  have hN := upub_N hq
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs vars) (.block (Impl.AesCbc.RISCV64.xorInto .s3 .s4 ++ updArgs))
    h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s4, .s5]) (.block Impl.AesCbc.RISCV64.advance) h).isSome =
    true := ⟨_, by taint_decide⟩
  have mid (t : State) (ht : UPre t) (hk : k < N t) {s : State} (h : UInv t k s) :
      WP isa (.block (Impl.AesCbc.RISCV64.xorInto .s3 .s4 ++ updArgs)) s (UMid t k) :=
    WP.mono (bodyPre_wp ht hk h) fun s' ⟨c, g, _, _, _, _, sp'⟩ =>
      ⟨c, by rw [g _ (by decide), h.s4], by rw [g _ (by decide), h.s5], sp'.trans h.sp⟩
  have a := (taintRegs (P := fun s₁ s₂ => k < N s₀ ∧ UInv s₀ k s₁ ∧ UInv s₀' k s₂) vars
    (fun _ _ h => ⟨by rw [h.2.1.sp, h.2.2.sp, upub_sp hq], UInv.agree hq h.2.1 h.2.2⟩) hA).wp
    (F₁ := UMid s₀ k) (F₂ := UMid s₀' k) fun _ _ h =>
      ⟨mid s₀ hp h.1 h.2.1, mid s₀' hp' (by rw [← hN]; exact h.1) h.2.2⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
    Proof.Aes.RISCV64.encryptBlocks_ct (P := fun s₁ s₂ => UMid s₀ k s₁ ∧ UMid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [upub_W hq, upub_Iv hq, upub_S hq, upub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, upub_sp hq]⟩).wp
    (F₁ := UAfter s₀ k) (F₂ := UAfter s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames h.1.pre)
        fun _ hc => ⟨by rw [hc.saved .s4 (by decide), h.1.s4], by rw [hc.saved .s5 (by decide), h.1.s5],
          hc.sp.trans h.1.sp⟩,
       WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames h.2.pre)
        fun _ hc => ⟨by rw [hc.saved .s4 (by decide), h.2.s4], by rw [hc.saved .s5 (by decide), h.2.s5],
          hc.sp.trans h.2.sp⟩⟩
  have b := taintRegs (P := fun s₁ s₂ => UAfter s₀ k s₁ ∧ UAfter s₀' k s₂) [.s4, .s5]
    (fun s₁ s₂ h => ⟨by rw [h.1.sp, h.2.sp, upub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.s4, h.2.s4, upub_blk hq]
      · rw [h.1.s5, h.2.s5, upub_N hq]⟩) hB
  have whole : RelCT isa (fun s₁ s₂ => k < N s₀ ∧ UInv s₀ k s₁ ∧ UInv s₀' k s₂) body fun _ _ => True :=
    (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)
  exact (whole.wp (F₁ := UInv s₀ (k + 1)) (F₂ := UInv s₀' (k + 1)) fun s₁ s₂ h =>
    ⟨(body_ok hp h.1 h.2.1 : WP isa body _ _), (body_ok hp' (by rw [← hN]; exact h.1) h.2.2 : WP isa body _ _)⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- The loop's relation, with the number of iterations left. -/
def URel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ UInv s₀ k s₁ ∧ UInv s₀' k s₂

theorem upd_loop_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updateRISCV64.pub s₀ s₀') (n : Nat) :
    RelCT isa (URel s₀ s₀' n) (.loop body (.nonzero .s5))
      fun s₁ s₂ => UInv s₀ (N s₀) s₁ ∧ UInv s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (URel s₀ s₀') (fun n => ?_) n
  have hN := upub_N hq
  have hb₀ := (s₀.gpr .a4).isLt
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
  have e₁ := Steps.eval_nonzero_ofNat s₁ .s5 bd l₁.s5
  have e₂ := Steps.eval_nonzero_ofNat s₂ .s5 (k := N s₀ - (k + 1)) bd (by rw [l₂.s5, hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, by omega, l₁, l₂⟩

theorem update_rel {s₀ s₀' : State} (h0 : updateRISCV64.pre s₀) (h0' : updateRISCV64.pre s₀')
    (hq : updateRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') update fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := upub_N hq
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
    (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.s6]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩
  have pro := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4, .a5]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨upub_sp hq, fun r hr => ?_⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := UInv s₀ 0) (F₂ := UInv s₀' 0)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have ev {t : State} {s : State} (h : UInv t 0 s) : isa.eval (.zero .s5) s = some (decide (N t = 0)) := by
    have := Steps.eval_zero_ofNat s .s5 (k := N t - 0) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (t.gpr .a4).isLt)
      h.s5
    rwa [Nat.sub_zero] at this
  have nil := taintRegs (P := fun a b => (UInv s₀ 0 a ∧ UInv s₀' 0 b) ∧ isa.eval (.zero .s5) a = some true) []
    (fun _ _ h => ⟨by rw [h.1.1.sp, h.1.2.sp, upub_sp hq], fun r hr => by simp at hr⟩) hnil
  have mid : RelCT isa (fun a b => UInv s₀ 0 a ∧ UInv s₀' 0 b)
      (.ite (.zero .s5) (.block []) (.loop body (.nonzero .s5)))
      (fun a b => UInv s₀ (N s₀) a ∧ UInv s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1, ev h.2, hN]) ?_ ?_
    · refine (nil.wp (F₁ := UInv s₀ (N s₀)) (F₂ := UInv s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (RelCT.exists_ (P := fun (_ : 0 < N s₀) a b => UInv s₀ 0 a ∧ UInv s₀' 0 b) fun hn =>
          (upd_loop_ct hp hp' hq (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hn, h.1, h.2⟩) fun _ _ h => h).mono
        (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := taintRegs (P := fun a b => UInv s₀ (N s₀) a ∧ UInv s₀' (N s₀') b) [.s6]
    (fun a b h => ⟨by rw [h.1.sp, h.2.sp, upub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.s6, h.2.s6, upub_S hq]⟩) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem update_ct : ConstantTime isa updateRISCV64.pre updateRISCV64.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.RISCV64
