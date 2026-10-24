module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_pkcs1_recover_precomputed` on PPC64LE: `Verified`

Correctness (`code_correct`), constant time (`code_ct`: the code between
the call and the branches checked by the taint analysis, from the stack
pointer and the registers holding public values; the call of
`vg_rsa_public_precomputed_checked` by its contract, `pdCallCT`; the length
check's branch, on public lengths) and a state meeting the precondition.
As `vg_rsa_pkcs1_verify_precomputed`'s (`VerifyVerified.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the pointers
and lengths, `hash`, the bytes of `n`, `e` and the signature, and the
precomputed values. -/
structure PubR (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r10], s.gpr r = a.gpr r
  h9 : (s.gpr .r9).setWidth 32 = (a.gpr .r9).setWidth 32
  args : ∀ i < 5, stackArg s i = stackArg a i
  be : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r7) (a.gpr .r8).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 3) (stackArg a 4).toNat

theorem leak_eq3W {a b c a' b' c' : List Byte} {w w' : List (BitVec 64)} (ha : a.length = a'.length)
    (hb : b.length = b'.length) (hc : c.length = c'.length)
    (h : (a ++ b ++ c).map (·.toNat) ++ w.map (·.toNat) = (a' ++ b' ++ c').map (·.toNat) ++ w'.map (·.toNat)) :
    b = b' ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb, hc])
  have hi : a ++ b ++ c = a' ++ b' ++ c' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  obtain ⟨h₃, -⟩ := List.append_inj hi (by simp [ha, hb])
  obtain ⟨-, e⟩ := List.append_inj h₃ ha
  exact ⟨e, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

theorem pubR_of {S : Nat} {s₁ s₂ : State}
    (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi S).pub s₁ s₂) : PubR s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4⟩ := h
  obtain ⟨he, hw⟩ := leak_eq3W (by simp [bytesAt_length, h6]) (by simp [bytesAt_length, h8])
    (by simp [bytesAt_length, a0]) hl
  refine ⟨hsp.symm, fun r hr => ?_, h9.symm, fun i hi => ?_, he.symm, hw.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h10.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm]

/-- An entry state with the anchor's public data. -/
def E (a s : State) : Prop := PreR s ∧ PubR a s

/-! ## Constant time -/

theorem fb_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) : fb s₁ = fb s₂ := by
  simp only [fb, h₁.2.sp, h₂.2.sp]

theorem gpr_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {r : Reg}
    (hr : r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r10] := by decide) : s₁.gpr r = s₂.gpr r :=
  (h₁.2.g r hr).trans (h₂.2.g r hr).symm

theorem arg_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {i : Nat} (hi : i < 5 := by decide) :
    stackArg s₁ i = stackArg s₂ i :=
  (h₁.2.args i hi).trans (h₂.2.args i hi).symm

/-- A call's stack arguments, from a state with its stack pointer and memory. -/
theorem stackArg_congr {t u : State} (hsp : t.sp = u.sp) (hm : t.mem = u.mem) (i : Nat) :
    stackArg t i = stackArg u i := by
  simp only [stackArg, stackArgAddr, hsp, hm]

/-- Two calls of `vg_rsa_public_precomputed_checked` from `AtCall` agree on
what the callee may leak. -/
theorem call_ct :
    RelCT isa (Two fun a t => ∃ s, E a s ∧ stackArg s 0 = s.gpr .r6 ∧ AtCall s t) pubCall fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, h₁, g₁, c₁⟩, ⟨s₂, h₂, g₂, c₂⟩⟩ => ⟨pdOk_of h₁.1 c₁ g₁,
    pdOk_of h₂.1 c₂ g₂, ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, fb_eq h₁ h₂]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g3, c₂.g3, fb_eq h₁ h₂]
    · rw [c₁.g4, c₂.g4, gpr_eq h₁ h₂]
    · rw [c₁.g5, c₂.g5, arg_eq h₁ h₂]
    · rw [c₁.g6, c₂.g6, arg_eq h₁ h₂]
    · rw [c₁.g7, c₂.g7, gpr_eq h₁ h₂]
    · rw [c₁.g8, c₂.g8, gpr_eq h₁ h₂]
    · rw [c₁.g9, c₂.g9, gpr_eq h₁ h₂]
    · rw [c₁.g10, c₂.g10, gpr_eq h₁ h₂]
  · rw [c₁.a0, c₂.a0, arg_eq h₁ h₂]
  · rw [c₁.a1, c₂.a1, arg_eq h₁ h₂]
  · rw [c₁.g5, c₂.g5, c₁.g6, c₂.g6, words_of_frame c₁.mem h₁.1.kp h₁.1.sp h₁.1.wp,
      words_of_frame c₂.mem h₂.1.kp h₂.1.sp h₂.1.wp, h₁.2.w, h₂.2.w]
  · rw [c₁.g7, c₂.g7, c₁.g8, c₂.g8, bytes_of_frame c₁.mem h₁.1.ke h₁.1.es.symm (by have := h₁.1.we; omega),
      bytes_of_frame c₂.mem h₂.1.ke h₂.1.es.symm (by have := h₂.1.we; omega), h₁.2.be, h₂.2.be]

theorem code_ct : RelCT isa (Two E) code fun _ _ => True := by
  unfold code
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ Only [.r12, .r11] s t ∧
      t.gpr .r11 = stackArg s 0 - s.gpr .r6)
    (lenCheck_taint fun _ _ _ h₁ h₂ => ⟨by rw [h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a s h => WP.mono (lenCheck_ok h.1) fun t ht => ⟨s, h, ht⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, e₁⟩ ⟨s₂, h₂, _, e₂⟩ => by
      rw [eval_len e₁, eval_len e₂, arg_eq h₁ h₂ (i := 0), gpr_eq h₁ h₂ (r := .r6)])
    (zeroArgs_taint fun _ _ _ ⟨⟨s₁, h₁, o₁, _⟩, _⟩ ⟨⟨s₂, h₂, o₂, _⟩, _⟩ =>
      ⟨by rw [o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [o₁.get .r3, o₂.get .r3, gpr_eq h₁ h₂]
        · rw [o₁.get .r4, o₂.get .r4, gpr_eq h₁ h₂]⟩) ?_
  refine two_alloc (R := fun _ _ => True)
    (fun _ _ _ ⟨⟨s₁, h₁, o₁, _⟩, _⟩ ⟨⟨s₂, h₂, o₂, _⟩, _⟩ =>
      ⟨by rw [o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ stackArg s 0 = s.gpr .r6 ∧ AtCall s t)
    (pubArgs_taint fun _ _ _ ⟨u₁, ⟨⟨s₁, h₁, o₁, _⟩, _⟩, e₁⟩ ⟨u₂, ⟨⟨s₂, h₂, o₂, _⟩, _⟩, e₂⟩ =>
      ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp],
        fun _ h => absurd h List.not_mem_nil⟩) fun a u ⟨t, ⟨⟨s, h, o, e⟩, hb⟩, hu⟩ => ?_) ?_
  · have hsig : stackArg s 0 = s.gpr .r6 := by
      rw [eval_len e] at hb; simpa using hb
    subst hu
    have fr₁ : frameR frameBytes t = fr s := by rw [frameR_eq]; unfold fr fb; rw [o.sp]
    exact WP.mono (pubArgs_ok h.1 (by rw [allocated_sp, o.sp]) (by rw [allocated_wr, fr₁, o.wr])
      (by rw [allocated_rd, o.rd])
      (by rw [allocated_mem, o.mem, o.sp]
          exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s))
      (fun r hr => by
        rw [allocated_gpr]
        exact o.gpr r fun h => hr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; exact h.symm))
      (by rw [allocated_lr, o.lr])) fun t ht => ⟨s, h, hsig, ht⟩
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ stackArg s 0 = s.gpr .r6 ∧ AfterCall s t) call_ct
    fun a t ⟨s, h, g, ht⟩ => WP.mono (call_ok h.1 ht g) fun w hw => ⟨s, h, g, hw⟩) ?_
  refine afterPub_taint fun _ _ _ ⟨s₁, h₁, _, a₁⟩ ⟨s₂, h₂, _, a₂⟩ => ⟨?_, fun r hr => ?_⟩
  · rw [a₁.sp, a₂.sp, fb_eq h₁ h₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a₁.r28, a₂.r28, gpr_eq h₁ h₂]
    · rw [a₁.r29, a₂.r29, gpr_eq h₁ h₂]
    · rw [a₁.r30, a₂.r30, gpr_eq h₁ h₂]
    · rw [a₁.r31, a₂.r31, h₁.2.h9, h₂.2.h9]

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes).pre
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes).pub code :=
  RelCT.constantTime (code_ct.mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preR_of h₁, ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl⟩⟩, preR_of h₂, pubR_of hp⟩)
    fun _ _ h => h)

end VG.Proof.RsaPkcs1Sig.PPC64LE.Rec


namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE

/-! ## A state meeting the precondition -/

/-- `out` of 16 bytes (MD5's, hash 0) at `0x6000`, a modulus of 64 bytes at
`0x1000`, `e` and the signature of a byte each, 112 words of working space
and 16 precomputed words; the stack arguments at `sp + 96`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x6000 | .r4 => 16 | .r5 => 0x1000 | .r6 => 64 | .r7 => 0x2000 | .r8 => 1 | .r10 => 0x4000
    | _ => 0
  lr := 0
  sp := 0x10000000000
  mem a := bif Nat.beq a.toNat 0x10000000060 then 1
    else bif Nat.beq a.toNat 0x1000000006A then 1 else bif Nat.beq a.toNat 0x10000000070 then 0x70
    else bif Nat.beq a.toNat 0x10000000079 then 0x50 else bif Nat.beq a.toNat 0x10000000080 then 16 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x4000, 1⟩, ⟨0x5000, 128⟩, ⟨0x10000000060, 40⟩]
  wr := [⟨0x6000, 16⟩, ⟨0x10000, 896⟩]

theorem sat_args : stackArg satState 0 = 1 ∧ stackArg satState 1 = 0x10000 ∧ stackArg satState 2 = 112 ∧
    stackArg satState 3 = 0x5000 ∧ stackArg satState 4 = 16 := by
  decide

theorem sat : ∃ s, (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes).pre s := by
  refine ⟨satState, ?_⟩
  have e : frameBytes = 2223 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4⟩ := sat_args
  have ha : stackArgAddr satState 0 = 0x10000000060 := by decide
  simp only [a0, a1, a2, a3, a4, ha]
  exact ⟨by decide, by decide, by decide, by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide, by unfold Spec.Rsa.lenValid; decide,
    by decide, by decide, ⟨.md5, by decide, by decide⟩, by decide, by decide⟩

theorem code_verified : Verified PPC64LE.target RecoverPrecomputed.code
    (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes) :=
  ⟨code_correct, code_constantTime, sat⟩

end VG.Proof.RsaPkcs1Sig.PPC64LE.Rec
