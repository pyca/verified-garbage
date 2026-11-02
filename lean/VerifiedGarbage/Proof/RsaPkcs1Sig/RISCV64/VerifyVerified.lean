module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_pkcs1_verify_precomputed` on RISC-V: `Verified`

Correctness (`code_correct`), constant time (`code_ct`: the code between
the call and the branches checked by the taint analysis, from the stack
pointer and the registers holding public values; the call of
`vg_rsa_public_precomputed_checked` by its contract, `pdCallCT`; the length
check's branch, on public lengths) and a state meeting the precondition.
As on PPC64LE (`Proof/RsaPkcs1Sig/PPC64LE/VerifyVerified.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Ver

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Precomputed
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the pointers
and lengths, `hash`, the bytes of `n`, `e`, the hash value and the
signature, and the precomputed values. -/
structure PubV (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a5, .a6, .a7], s.gpr r = a.gpr r
  h4 : (s.gpr .a4).setWidth 32 = (a.gpr .a4).setWidth 32
  args : ∀ i < 5, stackArg s i = stackArg a i
  be : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a2) (a.gpr .a3).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 3) (stackArg a 4).toNat

theorem leak_eqW {a b c d a' b' c' d' : List Byte} {w w' : List (BitVec 64)} (ha : a.length = a'.length)
    (hb : b.length = b'.length) (hc : c.length = c'.length) (hd : d.length = d'.length)
    (h : (a ++ b ++ c ++ d).map (·.toNat) ++ w.map (·.toNat) =
      (a' ++ b' ++ c' ++ d').map (·.toNat) ++ w'.map (·.toNat)) :
    b = b' ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb, hc, hd])
  have hi : a ++ b ++ c ++ d = a' ++ b' ++ c' ++ d' :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  obtain ⟨h₃, -⟩ := List.append_inj hi (by simp [ha, hb, hc])
  obtain ⟨h₄, -⟩ := List.append_inj h₃ (by simp [ha, hb])
  obtain ⟨-, e⟩ := List.append_inj h₄ ha
  exact ⟨e, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

theorem pubV_of {S : Nat} {s₁ s₂ : State}
    (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi S).pub s₁ s₂) : PubV s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4⟩ := h
  obtain ⟨he, hw⟩ := leak_eqW (by simp [bytesAt_length, h4]) (by simp [bytesAt_length, h6])
    (by simp [bytesAt_length, h9]) (by simp [bytesAt_length, a0]) hl
  refine ⟨hsp.symm, fun r hr => ?_, h7.symm, fun i hi => ?_, he.symm, hw.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm]

/-- An entry state with the anchor's public data. -/
def E (a s : State) : Prop := PreV s ∧ PubV a s

/-! ## Constant time -/

theorem fb_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) : fb s₁ = fb s₂ := by
  simp only [fb, h₁.2.sp, h₂.2.sp]

theorem gpr_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {r : Reg}
    (hr : r ∈ [Reg.a0, .a1, .a2, .a3, .a5, .a6, .a7] := by decide) : s₁.gpr r = s₂.gpr r :=
  (h₁.2.g r hr).trans (h₂.2.g r hr).symm

theorem arg_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {i : Nat} (hi : i < 5 := by decide) :
    stackArg s₁ i = stackArg s₂ i :=
  (h₁.2.args i hi).trans (h₂.2.args i hi).symm

/-- Two calls of `vg_rsa_public_precomputed_checked` from `AtCall` agree on
what the callee may leak. -/
theorem call_ct :
    RelCT isa (Two fun a t => ∃ s, E a s ∧ stackArg s 0 = s.gpr .a1 ∧ AtCall s t) pubCall fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, h₁, g₁, c₁⟩, ⟨s₂, h₂, g₂, c₂⟩⟩ => ⟨pdOk_of h₁.1 c₁ g₁,
    pdOk_of h₂.1 c₂ g₂, ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, fb_eq h₁ h₂]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g0, c₂.g0, fb_eq h₁ h₂]
    · rw [c₁.g1, c₂.g1, gpr_eq h₁ h₂]
    · rw [c₁.g2, c₂.g2, arg_eq h₁ h₂]
    · rw [c₁.g3, c₂.g3, arg_eq h₁ h₂]
    · rw [c₁.g4, c₂.g4, gpr_eq h₁ h₂]
    · rw [c₁.g5, c₂.g5, gpr_eq h₁ h₂]
    · rw [c₁.g6, c₂.g6, gpr_eq h₁ h₂]
    · rw [c₁.g7, c₂.g7, gpr_eq h₁ h₂]
  · rw [c₁.sa0, c₂.sa0, arg_eq h₁ h₂]
  · rw [c₁.sa1, c₂.sa1, arg_eq h₁ h₂]
  · rw [c₁.g2, c₂.g2, c₁.g3, c₂.g3, words_of_frame c₁.mem h₁.1.kp h₁.1.sp h₁.1.wp,
      words_of_frame c₂.mem h₂.1.kp h₂.1.sp h₂.1.wp, h₁.2.w, h₂.2.w]
  · rw [c₁.g4, c₂.g4, c₁.g5, c₂.g5, bytes_of_frame c₁.mem h₁.1.ke h₁.1.es.symm (by have := h₁.1.we; omega),
      bytes_of_frame c₂.mem h₂.1.ke h₂.1.es.symm (by have := h₂.1.we; omega), h₁.2.be, h₂.2.be]

theorem code_ct : RelCT isa (Two E) code fun _ _ => True := by
  unfold code
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ Only [.t0] s t ∧
      t.gpr .t0 = stackArg s 0 - s.gpr .a1)
    (lenCheck_taint fun _ _ _ h₁ h₂ => ⟨by rw [h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a s h => WP.mono (lenCheck_ok h.1) fun t ht => ⟨s, h, ht⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, e₁⟩ ⟨s₂, h₂, _, e₂⟩ => by
      rw [eval_len e₁, eval_len e₂, arg_eq h₁ h₂ (i := 0), gpr_eq h₁ h₂ (r := .a1)])
    (ret0_taint fun _ _ _ ⟨⟨s₁, h₁, o₁, _⟩, _⟩ ⟨⟨s₂, h₂, o₂, _⟩, _⟩ =>
      ⟨by rw [o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩) ?_
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ stackArg s 0 = s.gpr .a1 ∧ AtCall s t)
    (pubArgs_taint fun _ _ _ ⟨u₁, ⟨⟨s₁, h₁, o₁, _⟩, _⟩, e₁⟩ ⟨u₂, ⟨⟨s₂, h₂, o₂, _⟩, _⟩, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show u₁.sp - _ = u₂.sp - _; rw [o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp],
        fun _ h => absurd h List.not_mem_nil⟩) fun a u ⟨t, ⟨⟨s, h, o, e⟩, hb⟩, hu⟩ => ?_) ?_
  · have hsig : stackArg s 0 = s.gpr .a1 := by
      rw [eval_len e] at hb; simpa using hb
    subst hu
    exact WP.mono (pubArgs_ok h.1 (by show t.sp - _ = _; rw [o.sp])
      (by show (⟨t.sp - _, _⟩ :: t.wr) = _; rw [o.sp, o.wr])
      (by show t.rd = _; rw [o.rd])
      (by show Frame _ _ t.mem; rw [o.mem]; exact Frame.refl _ _)
      (fun r hr => o.gpr r hr)) fun t ht => ⟨s, h, hsig, ht⟩
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ stackArg s 0 = s.gpr .a1 ∧ AfterCall s t) call_ct
    fun a t ⟨s, h, g, ht⟩ => WP.mono (call_ok h.1 ht g) fun w hw => ⟨s, h, g, hw⟩) ?_
  refine afterPub_taint fun _ _ _ ⟨s₁, h₁, _, a₁⟩ ⟨s₂, h₂, _, a₂⟩ => ⟨?_, fun r hr => ?_⟩
  · rw [a₁.sp, a₂.sp, fb_eq h₁ h₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a₁.s1, a₂.s1, gpr_eq h₁ h₂]
    · rw [a₁.s2, a₂.s2, zx, zx, h₁.2.h4, h₂.2.h4]
    · rw [a₁.s3, a₂.s3, gpr_eq h₁ h₂]
    · rw [a₁.s4, a₂.s4, gpr_eq h₁ h₂]

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pre
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pub code :=
  RelCT.constantTime (code_ct.mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preV_of h₁, ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl⟩⟩, preV_of h₂, pubV_of hp⟩)
    fun _ _ h => h)

/-! ## A state meeting the precondition -/

/-- A modulus of 64 bytes at `0x1000`, `e`, the hash value and the signature
of a byte each, 112 words of working space and 16 precomputed words; the
stack arguments at `sp`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 1 | .a5 => 0x3000 | .a6 => 1 | .a7 => 0x4000
    | _ => 0
  sp := 0x10000000000
  mem a := bif Nat.beq a.toNat 0x10000000000 then 1
    else bif Nat.beq a.toNat 0x1000000000A then 1 else bif Nat.beq a.toNat 0x10000000010 then 0x70
    else bif Nat.beq a.toNat 0x10000000019 then 0x50 else bif Nat.beq a.toNat 0x10000000020 then 16 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x5000, 128⟩, ⟨0x10000000000, 40⟩]
  wr := [⟨0x10000, 896⟩]

theorem sat_args : stackArg satState 0 = 1 ∧ stackArg satState 1 = 0x10000 ∧ stackArg satState 2 = 112 ∧
    stackArg satState 3 = 0x5000 ∧ stackArg satState 4 = 16 := by
  decide

theorem sat : ∃ s, (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pre s := by
  refine ⟨satState, ?_⟩
  have e : frameBytes = 2127 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4⟩ := sat_args
  have ha : stackArgAddr satState 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, a3, a4, ha]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide, by unfold Spec.Rsa.lenValid; decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem code_verified : Verified RISCV64.target Precomputed.code
    (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes) :=
  ⟨code_correct, code_constantTime, sat⟩

end VG.Proof.RsaPkcs1Sig.RISCV64.Ver
