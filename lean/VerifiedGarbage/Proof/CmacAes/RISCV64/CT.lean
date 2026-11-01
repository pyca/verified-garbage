module

import VerifiedGarbage.Proof.CmacAes.RISCV64.Finalize
import VerifiedGarbage.Proof.CmacAes.RISCV64.Subkeys
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
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
changes, and each call of `vg_aes_encrypt_blocks` is constant time by its
own proof (`blk_rel`). The branches of `finalize` are on `last_len`, which
is public. (`update`, a call of the chain, is constant time by
`Proof.AesCbc.RISCV64.wrap_ct`: `Verified.lean`.)
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64 VG.Impl.CmacAes.RISCV64
open VG.Proof.AesCbc.RISCV64 (blk_call blk_rel taintRegs encryptBlocks_noFrames)

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

end VG.Proof.CmacAes.RISCV64
