module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: `Verified`

Correctness (`code_correct`), constant time (`code_ct`: the code around the
call by the taint analysis, from registers holding public values, which the
correctness proofs pin after the setup and the call; the call of
`vg_rsa_public_precomputed_checked` by its contract, `pdCallCT`) and a state
meeting the precondition. As `vg_rsa_pkcs1_verify_precomputed`'s
(`Proof/RsaPkcs1Sig/PPC64LE/VerifyVerified.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed
open VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the pointers
and lengths, the bytes of `n` and `e`, and the precomputed values. -/
structure PubE (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  args : ∀ i < 6, stackArg s i = stackArg a i
  be : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r7) (a.gpr .r8).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 4) (stackArg a 5).toNat

theorem leak_eq2W {a b a' b' : List Byte} {w w' : List (BitVec 64)} (ha : a.length = a'.length)
    (hb : b.length = b'.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (a' ++ b').map (·.toNat) ++ w'.map (·.toNat)) :
    b = b' ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = a' ++ b' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  obtain ⟨-, e⟩ := List.append_inj hi ha
  exact ⟨e, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

theorem pubE_of {S : Nat} {s₁ s₂ : State}
    (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi S).pub s₁ s₂) : PubE s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5⟩ := h
  obtain ⟨he, hw⟩ := leak_eq2W (by simp [bytesAt_length, h6]) (by simp [bytesAt_length, h8]) hl
  refine ⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, he.symm, hw.symm⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm]

/-- An entry state with the anchor's public data. -/
def E (a s : State) : Prop := PreE s ∧ PubE a s

/-! ## Constant time -/

theorem fb_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) : fb s₁ = fb s₂ := by
  simp only [fb, h₁.2.sp, h₂.2.sp]

theorem gpr_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {r : Reg} (hr : r ∈ argRegs := by decide) :
    s₁.gpr r = s₂.gpr r :=
  (h₁.2.g r hr).trans (h₂.2.g r hr).symm

theorem arg_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {i : Nat} (hi : i < 6 := by decide) :
    stackArg s₁ i = stackArg s₂ i :=
  (h₁.2.args i hi).trans (h₂.2.args i hi).symm

theorem call_ct : RelCT isa (Two fun a t => ∃ s, E a s ∧ AtCall s t) pubCall fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, h₁, c₁⟩, ⟨s₂, h₂, c₂⟩⟩ => ⟨pdOk_of h₁.1 c₁,
    pdOk_of h₂.1 c₂, ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, fb_eq h₁ h₂]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g3, c₂.g3, gpr_eq h₁ h₂]
    · rw [c₁.g4, c₂.g4, gpr_eq h₁ h₂]
    · rw [c₁.g5, c₂.g5, arg_eq h₁ h₂]
    · rw [c₁.g6, c₂.g6, arg_eq h₁ h₂]
    · rw [c₁.g7, c₂.g7, gpr_eq h₁ h₂]
    · rw [c₁.g8, c₂.g8, gpr_eq h₁ h₂]
    · rw [c₁.g9, c₂.g9, emA, fb_eq h₁ h₂]
    · rw [c₁.g10, c₂.g10, gpr_eq h₁ h₂]
  · rw [c₁.a0, c₂.a0, arg_eq h₁ h₂]
  · rw [c₁.a1, c₂.a1, arg_eq h₁ h₂]
  · rw [c₁.g5, c₂.g5, c₁.g6, c₂.g6, words_of_frame c₁.mem h₁.1.kp h₁.1.sp h₁.1.wp,
      words_of_frame c₂.mem h₂.1.kp h₂.1.sp h₂.1.wp, h₁.2.w, h₂.2.w]
  · rw [c₁.g7, c₂.g7, c₁.g8, c₂.g8, bytes_of_frame c₁.mem h₁.1.ke h₁.1.es.symm (by have := h₁.1.we; omega),
      bytes_of_frame c₂.mem h₂.1.ke h₂.1.es.symm (by have := h₂.1.we; omega), h₁.2.be, h₂.2.be]

theorem code_ct : RelCT isa (Two E) code fun _ _ => True := by
  unfold code
  refine two_alloc (R := fun _ _ => True)
    (fun _ _ _ h₁ h₂ => ⟨by rw [h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, E a s ∧ Setup s w)
    (setup_taint fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    exact WP.mono (setup_ok h.1 (by rw [allocated_sp]) (by rw [allocated_wr, frameR_eq]) (by rw [allocated_rd])
      (by rw [allocated_mem]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s))
      (fun r _ => by rw [allocated_gpr]) (by rw [allocated_lr])) fun w hw => ⟨s, h, hw⟩
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ AtCall s t)
    (preCall_taint fun _ _ _ ⟨s₁, h₁, w₁⟩ ⟨s₂, h₂, w₂⟩ => ⟨by rw [w₁.sp, w₂.sp, fb_eq h₁ h₂], fun r hr => ?_⟩)
    fun a w ⟨s, h, hw⟩ => WP.mono (preCall_ok h.1 hw) fun t ht => ⟨s, h, ht⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [w₁.g4, w₂.g4, arg_eq h₁ h₂]
    · rw [w₁.g9, w₂.g9, gpr_eq h₁ h₂]
    · rw [w₁.g10, w₂.g10, gpr_eq h₁ h₂]
    · rw [w₁.g11, w₂.g11, fb_eq h₁ h₂]
    · rw [w₁.g12, w₂.g12, arg_eq h₁ h₂]
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ AfterCall s t) call_ct
    fun a t ⟨s, h, ht⟩ => WP.mono (call_ok h.1 ht) fun w hw => ⟨s, h, hw⟩) ?_
  refine tail_taint fun _ _ _ ⟨s₁, h₁, a₁⟩ ⟨s₂, h₂, a₂⟩ => ⟨?_, fun r hr => ?_⟩
  · rw [a₁.sv.sp, a₂.sv.sp, fb_eq h₁ h₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a₁.r28, a₂.r28, gpr_eq h₁ h₂]
    · rw [a₁.r29, a₂.r29, gpr_eq h₁ h₂]

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pre
      (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pub code :=
  RelCT.constantTime (code_ct.mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preE_of h₁, ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩⟩, preE_of h₂, pubE_of hp⟩)
    fun _ _ h => h)

/-! ## A state meeting the precondition -/

/-- `out` and a modulus of 64 bytes at `0x6000` and `0x1000`, `e` and the
message of a byte each, `PS` of 60 bytes, 112 words of working space and 16
precomputed words; the stack arguments at `sp + 96`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x6000 | .r4 => 64 | .r5 => 0x1000 | .r6 => 64 | .r7 => 0x2000 | .r8 => 1 | .r9 => 0x3000
    | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x10000000000
  mem a := bif Nat.beq a.toNat 0x10000000061 then 0x40
    else bif Nat.beq a.toNat 0x10000000068 then 60 else bif Nat.beq a.toNat 0x10000000072 then 1
    else bif Nat.beq a.toNat 0x10000000078 then 0x70 else bif Nat.beq a.toNat 0x10000000081 then 0x50
    else bif Nat.beq a.toNat 0x10000000088 then 16 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 60⟩, ⟨0x5000, 128⟩, ⟨0x10000000060, 48⟩]
  wr := [⟨0x6000, 64⟩, ⟨0x10000, 896⟩]

theorem sat_args : stackArg satState 0 = 0x4000 ∧ stackArg satState 1 = 60 ∧ stackArg satState 2 = 0x10000 ∧
    stackArg satState 3 = 112 ∧ stackArg satState 4 = 0x5000 ∧ stackArg satState 5 = 16 := by
  decide

theorem sat : ∃ s, (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pre s := by
  refine ⟨satState, ?_⟩
  have e : frameBytes = 2223 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := sat_args
  have ha : stackArgAddr satState 0 = 0x10000000060 := by decide
  simp only [a0, a1, a2, a3, a4, a5, ha]
  exact ⟨by decide, by decide, by decide, by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by unfold Spec.Rsa.lenValid; decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem code_verified : Verified PPC64LE.target code (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes) :=
  ⟨code_correct, code_constantTime, sat⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc
