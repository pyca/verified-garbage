module

import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignTail
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignCall

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: correctness

The blocks and the call in order (`code_correct`), from the frame's push to
its pop, to the outcome of `signId` on the registers and the stack
(`fnPost`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenOutcome s'.mem (s.gpr .r3) (s.gpr .r6).toNat ((s'.gpr .r3).setWidth 32)
    (Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
      ((s.gpr .r9).setWidth 32).toNat (hashOf s))

/-- `signId` from the encoding. -/
theorem signId_eq (s : State) :
    Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
      ((s.gpr .r9).setWidth 32).toNat (hashOf s) =
    match encOut s with
    | some em => Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) em
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
    | none => .invalid := by
  simp only [Spec.RsaPkcs1Sig.signId, encOut, RsaPkcs1Sig.PPC64LE.encodeId, Spec.RsaPkcs1Sig.sign,
    Proof.RsaPkcs1Sig.bytesAt_length]
  cases Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .r9).setWidth 32).toNat with
  | none => rfl
  | some h => cases Spec.RsaPkcs1Sig.encode h (hashOf s) (s.gpr .r6).toNat <;> rfl

theorem freed_sp (b : Nat) (s : State) : (freed b s).sp = s.sp + BitVec.ofNat 64 b := rfl
theorem freed_lr (b : Nat) (s : State) : (freed b s).lr = s.lr := rfl
theorem freed_gpr (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl
theorem freed_mem (b : Nat) (s : State) : (freed b s).mem = s.mem := rfl

/-- After the encoding: zeros and 0 if it failed, else the signature, and `EM`
overwritten. -/
theorem afterEnc_ok {s u : State} (h : SPre s) (B : AtAft s u) :
    WP isa afterEnc u fun v => Fr2 s v ∧ fnPost s v := by
  unfold afterEnc fnPost
  rw [signId_eq]
  have he := B.enc
  revert he
  cases encOut s with
  | none =>
    intro h3
    refine WP.ite true (by rw [eval_zero, h3]; rfl) (fun _ => WP.mono (zeroOut_ok h B h3)
      fun v ⟨F, v3, vb⟩ => ⟨F, by rw [v3]; exact ⟨rfl, vb⟩⟩) (fun h => absurd h (by decide))
  | some em =>
    intro ⟨h3, hb⟩
    refine WP.ite false (by rw [eval_zero, h3]; rfl) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq (WP.mono (callArgs_ok h B hb) fun t₃ C => ?_)
    refine WP.seq (call_ok h C fun t₄ R => WP.mono (wipe_ok h R) fun v ⟨F, o⟩ => ⟨F, o⟩)

theorem code_correct (s : State) (hpre : (Spec.RsaPkcs1Sig.signContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa code s fun t => abiPreserved s t ∧ fnPost s t
  have h := sPre_of hpre
  have hk := h.k2
  unfold code
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.sp1; unfold stackBytes at this; omega) ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (WP.mono (enc_ok h A) fun t₂ B => ?_)
  refine WP.seq (Q := fun _ => _) (WP.mono (Q := fun v => Fr2 s v ∧ fnPost s v) ?_ fun v ⟨F, hp⟩ =>
    WP.mono (restore_ok F) fun w ⟨wp, wl, ws, wm, w3⟩ => ?_)
  · exact afterEnc_ok h B
  · refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
    · rw [freed_gpr]; exact wp r hr
    · rw [freed_sp, ws]; exact BitVec.sub_add_cancel _ _
    · rw [freed_lr]; exact wl
    · unfold fnPost at hp ⊢
      rw [freed_mem, freed_gpr, wm, w3]; exact hp

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
