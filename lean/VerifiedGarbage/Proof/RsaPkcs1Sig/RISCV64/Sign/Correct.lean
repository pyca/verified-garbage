module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# `vg_rsa_pkcs1_sign` on RISC-V: correctness

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/SignTail.lean`, `SignCorrect.lean`): zeros to
`out` once the encoding failed (`zeroOut_ok`), `EM` overwritten after the call
(`wipe_ok`), and the function's outcome (`fnPost`, `code_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Sign

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Sign VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.RISCV64 (W Buf fillLoop_ok)

theorem gpr_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

theorem W_nil (s : State) : W s [] s :=
  ⟨Kept.refl _ _, (writeBytes_nil _ _).symm, by rw [List.length_nil, BitVec.add_zero]⟩

/-- Zeros to `out`, once the encoding failed. -/
theorem zeroOut_ok {s u : State} (h : SPre s) (A : AtAft s u) (h0 : u.gpr .a0 = 0) :
    WP isa zeroOut u fun v => SMid [oR s, sR s] s v ∧ v.gpr .a0 = 0 ∧
      Spec.Rsa.bytesAt v.mem (s.gpr .a0) (s.gpr .a3).toNat = List.replicate (s.gpr .a3).toNat 0 := by
  have hk := h.k2
  have hk1 := h.k1
  unfold zeroOut
  refine WP.seq (wp_mov fun w₁ o₁ e₁ => wp_mov fun w₂ o₂ e₂ => wp_li (imm := 0) (by decide) fun w o₃ e₃ =>
    wp_nil ?_)
  have P : Only [.a1, .t5, .t0] u w := (o₁.trans (o₂.trans o₃)).mono
  have w1 : w.gpr .a1 = s.gpr .a0 := by rw [o₃.get .a1, o₂.get .a1, e₁, A.s1]
  have w5 : w.gpr .t5 = BitVec.ofNat 64 (s.gpr .a3).toNat := by rw [o₃.get .t5, e₂, o₁.get .s3, A.s3, ← gpr_ofNat]
  have hb : Buf w (s.gpr .a3).toNat := fun i hi => by
    rw [P.wr, A.wr, h.hwr, w1]
    exact ⟨oR s, by simp, Offset.contains_base _ (by rw [h.h1]; omega) (by have := h.wo; omega)⟩
  refine WP.mono (fillLoop_ok hb (by omega) (acc := []) (by omega) (by simp) (W_nil w) 0
    (by rw [e₃]; rfl) w5) fun v ⟨⟨_, hm, _⟩, hk2⟩ => ?_
  rw [List.nil_append, w1] at hm
  have hO : (oR s).Contains (s.gpr .a0) (List.replicate (s.gpr .a3).toNat (0 : Byte)).length := by
    rw [List.length_replicate, ← h.h1]; exact Region.contains_self _ _
  have fo : Frame [oR s] u.mem v.mem := by rw [hm, P.mem]; exact writeBytes_frame _ _ _ hO
  refine ⟨A.toMid.keep (P.keep.trans hk2) (A.mem.sub (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩) |>.trans (fo.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩))
    (A.sv.frame fo fun p hp r hr => by
      rw [List.mem_singleton.mp hr]
      exact h.ko.sub_left (frame_sub s (by have := saved_offs p hp; unfold oRa frameBytes at *; omega))), ?_, ?_⟩
  · rw [hk2.get .a0, P.get .a0]; exact h0
  · rw [hm, P.mem]
    have := Proof.RsaPkcs1Sig.bytesAt_writeBytes u.mem (s.gpr .a0) (List.replicate (s.gpr .a3).toNat (0 : Byte))
      (by simp; omega)
    rwa [List.length_replicate] at this

theorem wo_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.writtenOutcome m out k r o) :
    Spec.Rsa.writtenOutcome m' out k r o := by
  cases o <;> simp only [Spec.Rsa.writtenOutcome, hb] at h ⊢ <;> exact h

/-- `EM` overwritten with zeros, after the call. -/
theorem wipe_ok {s u : State} {em : List Byte} (h : SPre s) (R : AtRet s u em) :
    WP isa wipe u fun v => SMid [oR s, sR s] s v ∧ privOut s em v := by
  have hk := h.k2
  have hk1 := h.k1
  unfold wipe
  refine WP.seq (wp_addSp (imm := 0) fun w₁ o₁ e₁ => wp_addi (imm := oEM) (fun w₂ o₂ e₂ => wp_mov fun w₃ o₃ e₃ =>
    wp_li (imm := 0) (by decide) fun w o₄ e₄ => wp_nil ?_) (by decide))
  rw [R.sp, BitVec.add_zero] at e₁
  have P : Only [.t0, .a1, .t5, .t0] u w := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have w1 : w.gpr .a1 = fb s + BitVec.ofNat 64 oEM := by rw [o₄.get .a1, o₃.get .a1, e₂, e₁]
  have w5 : w.gpr .t5 = BitVec.ofNat 64 (s.gpr .a3).toNat := by
    rw [o₄.get .t5, e₃, o₂.get .s3, o₁.get .s3, R.s3, ← gpr_ofNat]
  have hb : Buf w (s.gpr .a3).toNat := fun i hi => by rw [P.wr, R.wr, w1]; exact em_in h _ hi
  refine WP.mono (fillLoop_ok hb (by omega) (acc := []) (by omega) (by simp) (W_nil w) 0
    (by rw [e₄]; rfl) w5) fun v ⟨⟨_, hm, _⟩, hk2⟩ => ?_
  rw [List.nil_append, w1] at hm
  have hE : (emR s).Contains (fb s + BitVec.ofNat 64 oEM) (List.replicate (s.gpr .a3).toNat (0 : Byte)).length := by
    rw [List.length_replicate]; exact Region.contains_self _ _
  have fe : Frame [emR s] u.mem v.mem := by rw [hm, P.mem]; exact writeBytes_frame _ _ _ hE
  have hf := R.frameMem (f := oEM) (n := (s.gpr .a3).toNat) (.inl (by decide)) (by unfold oEM frameBytes; omega) fe
  refine ⟨R.toMid.keep (S' := [oR s, sR s]) (P.keep.trans hk2) hf.1 hf.2, ?_⟩
  have hb : Spec.Rsa.bytesAt v.mem (s.gpr .a0) (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a3).toNat :=
    bytes_of_frame (s := u) fe (fun r hr => by
      rw [List.mem_singleton.mp hr, show (⟨s.gpr .a0, (s.gpr .a3).toNat⟩ : Region) = oR s by simp only [oR, h.h1]]
      exact (h.ko.sub_left (em_sub h)).symm) (by omega)
  show Spec.Rsa.writtenOutcome _ _ _ ((v.gpr .a0).setWidth 32) _
  rw [hk2.get .a0, P.get .a0]
  exact wo_congr hb R.out

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenOutcome s'.mem (s.gpr .a0) (s.gpr .a3).toNat ((s'.gpr .a0).setWidth 32)
    (Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
      (hid s) (hashOf s))

/-- `signId` from the encoding. -/
theorem signId_eq (s : State) :
    Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
      (hid s) (hashOf s) =
    match encOut s with
    | some em => Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) em
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
    | none => .invalid := by
  simp only [Spec.RsaPkcs1Sig.signId, encOut, RsaPkcs1Sig.RISCV64.encodeId, Spec.RsaPkcs1Sig.sign,
    Proof.RsaPkcs1Sig.bytesAt_length]
  cases Spec.RsaPkcs1Sig.Hash.ofId (hid s) with
  | none => rfl
  | some h => cases Spec.RsaPkcs1Sig.encode h (hashOf s) (s.gpr .a3).toNat <;> rfl

/-- After the encoding: zeros and 0 if it failed, else the signature, and `EM`
overwritten. -/
theorem afterEnc_ok {s u : State} (h : SPre s) (B : AtAft s u) :
    WP isa afterEnc u fun v => SMid [oR s, sR s] s v ∧ fnPost s v := by
  unfold afterEnc fnPost
  rw [signId_eq]
  have he := B.enc
  revert he
  cases encOut s with
  | none =>
    intro h0
    refine WP.ite true (by rw [eval_zero, h0]; rfl) (fun _ => WP.mono (zeroOut_ok h B h0)
      fun v ⟨M, v0, vb⟩ => ⟨M, by rw [v0]; exact ⟨rfl, vb⟩⟩) (fun h => absurd h (by decide))
  | some em =>
    intro ⟨h1, hb⟩
    refine WP.ite false (by rw [eval_zero, h1]; rfl) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq (WP.mono (callArgs_ok h B hb) fun t₃ C => ?_)
    exact WP.seq (call_ok h C fun t₄ R => WP.mono (wipe_ok h R) fun v ⟨M, o⟩ => ⟨M, o⟩)

theorem code_correct (s : State) (hpre : (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa code s fun t => abiPreserved s t ∧ fnPost s t
  have h := sPre_of hpre
  unfold code
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ (by have := h.sp1; unfold stackBytes at this; omega) ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (WP.mono (enc_ok h A) fun t₂ B => ?_)
  refine WP.seq (WP.mono (afterEnc_ok h B) fun v ⟨M, hp⟩ => WP.mono (restore_ok h M.saves)
    fun w ⟨wa, w0, wm⟩ => ⟨wa, ?_⟩)
  unfold fnPost at hp ⊢
  simp only [freed]
  rw [wm, w0]; exact hp

end VG.Proof.RsaPkcs1Sig.RISCV64.Sign
