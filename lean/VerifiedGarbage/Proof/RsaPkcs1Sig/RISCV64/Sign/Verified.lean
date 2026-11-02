module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Correct
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Call
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Correct
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Call
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
meta import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# `vg_rsa_pkcs1_sign` on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness (`code_correct`),
constant time and a state meeting the precondition. As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/SignTaint.lean`, `SignCT.lean`,
`SignVerified.lean`), two runs with the same public data (`Two E`): the
blocks by the taint analysis, from the stack pointer and the registers that
hold public values; the branch on the encoding's result, which only the
lengths and `hash` decide (`isSome_same`); and the call by
`vg_rsa_private_checked`'s constant time (`RelCT.callEx`), whose public data
at the call the correctness facts fix (`priv_pub`, by `Priv.pub_of`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Sign

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Sign
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite two_alloc)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The taint checks -/

section
variable {α : Type} {Φ : α → State → Prop}

theorem setup_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (save ++ encArgs)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem encode_taint (h : Pins Φ [.a1, .a2, .a3, .a4, .a5]) :
    RelCT isa (Two Φ) Impl.RsaPkcs1Sig.RISCV64.encode fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem zeroOut_taint (h : Pins Φ [.s1, .s3]) : RelCT isa (Two Φ) zeroOut fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem callArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block callArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem wipe_taint (h : Pins Φ [.s3]) : RelCT isa (Two Φ) wipe fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the pointers
and lengths, `hash`, our stack arguments and the bytes of `n` and `e`. -/
structure PubS (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a7], s.gpr r = a.gpr r
  h6 : (s.gpr .a6).setWidth 32 = (a.gpr .a6).setWidth 32
  args : ∀ i < 13, stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a2) (a.gpr .a3).toNat
  e : Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a4) (a.gpr .a5).toNat

theorem pubS_of {s₁ s₂ : State} (h : (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes).pub s₁ s₂) :
    PubS s₁ s₂ := by
  have e : stackBytes = 4415 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_thirteen, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  rw [List.map_append, List.map_append] at hl
  obtain ⟨hn, he⟩ := List.append_inj hl (by simp [bytesAt_length, h6])
  refine ⟨hsp.symm, fun r hr => ?_, h9.symm, fun i hi => ?_,
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn).symm,
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he).symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h10.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm]

/-- An entry state with the anchor's public data. -/
def E (a s : State) : Prop := SPre s ∧ PubS a s

section
variable {a s₁ s₂ : State}

theorem fb_same (h₁ : E a s₁) (h₂ : E a s₂) : fb s₁ = fb s₂ := by simp only [fb, h₁.2.sp, h₂.2.sp]

theorem gpr_same (h₁ : E a s₁) (h₂ : E a s₂) {r : Reg}
    (hr : r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a7] := by decide) : s₁.gpr r = s₂.gpr r :=
  (h₁.2.g r hr).trans (h₂.2.g r hr).symm

theorem arg_same (h₁ : E a s₁) (h₂ : E a s₂) {i : Nat} (hi : i < 13 := by decide) :
    stackArg s₁ i = stackArg s₂ i :=
  (h₁.2.args i hi).trans (h₂.2.args i hi).symm

theorem hid_same (h₁ : E a s₁) (h₂ : E a s₂) : hid s₁ = hid s₂ := by
  simp only [hid, h₁.2.h6, h₂.2.h6]

/-- Whether the encoding succeeds depends only on `hash`, the lengths of the
hash value and `k`. -/
theorem isSome_same (h₁ : E a s₁) (h₂ : E a s₂) : (encOut s₁).isSome = (encOut s₂).isSome := by
  unfold encOut RsaPkcs1Sig.RISCV64.encodeId
  rw [hid_same h₁ h₂, gpr_same h₁ h₂ (r := .a3)]
  cases Spec.RsaPkcs1Sig.Hash.ofId (hid s₂) with
  | none => rfl
  | some h =>
    simp only [Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo, List.length_append, hashOf,
      bytesAt_length, arg_same h₁ h₂ (i := 0)]
    split <;> rfl

end

theorem AtAft.a0_eq {s u : State} (B : AtAft s u) : u.gpr .a0 = if (encOut s).isSome then 1 else 0 := by
  have := B.enc
  revert this
  cases encOut s with
  | none => intro h; exact h
  | some _ => intro h; exact h.1

/-! ## The call -/

theorem priv_pub {a s₁ s₂ t₁ t₂ : State} {em₁ em₂ : List Byte} (h₁ : E a s₁) (h₂ : E a s₂)
    (A₁ : AtCall s₁ t₁ em₁) (A₂ : AtCall s₂ t₂ em₂) :
    (Spec.Rsa.privateCheckedContract RISCV64.abi Impl.Rsa.RISCV64.Priv.frameBytes).pub (callE s₁ t₁)
      (callE s₂ t₂) := by
  have hn : ∀ {s t : State} {em : List Byte}, SPre s → AtCall s t em →
      Spec.Rsa.bytesAt (callE s t).mem ((callE s t).gpr .a2) ((callE s t).gpr .a3).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat := fun h A => by
    rw [callE_gpr, callE_gpr, A.a2, A.a3]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kn.symm)
      (by have := h.wn; omega)
  have he : ∀ {s t : State} {em : List Byte}, SPre s → AtCall s t em →
      Spec.Rsa.bytesAt (callE s t).mem ((callE s t).gpr .a4) ((callE s t).gpr .a5).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat := fun h A => by
    rw [callE_gpr, callE_gpr, A.a4, A.a5]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ke.symm)
      (by have := h.we; omega)
  refine Rsa.RISCV64.Priv.pub_of (by rw [show (callE s₁ t₁).sp = fb s₁ from A₁.sp,
      show (callE s₂ t₂).sp = fb s₂ from A₂.sp, fb_same h₁ h₂]) (fun r hr => ?_) (fun i hi => ?_)
    (by rw [hn h₁.1 A₁, hn h₂.1 A₂, h₁.2.n, h₂.2.n]) (by rw [he h₁.1 A₁, he h₂.1 A₂, h₁.2.e, h₂.2.e])
  · rw [callE_gpr s₁ t₁ (fun h => by revert r; decide), callE_gpr s₂ t₂ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.a0, A₂.a0, gpr_same h₁ h₂]
    · rw [A₁.a1, A₂.a1, gpr_same h₁ h₂]
    · rw [A₁.a2, A₂.a2, gpr_same h₁ h₂]
    · rw [A₁.a3, A₂.a3, gpr_same h₁ h₂]
    · rw [A₁.a4, A₂.a4, gpr_same h₁ h₂]
    · rw [A₁.a5, A₂.a5, gpr_same h₁ h₂]
    · rw [A₁.a6, A₂.a6, fb_same h₁ h₂]
    · rw [A₁.a7, A₂.a7, gpr_same h₁ h₂]
  · rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, arg_same h₁ h₂ (by omega)]

theorem priv_rel : RelCT isa (Two fun a t => ∃ s em, E a s ∧ AtCall s t em) privCall fun _ _ => True := by
  unfold privCall
  refine RelCT.callEx (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
    Rsa.RISCV64.Priv.code_ct fun u₁ u₂ ⟨_, ⟨s₁, _, h₁, A₁⟩, ⟨s₂, _, h₂, A₂⟩⟩ => ?_
  exact ⟨callRd s₁, callWr s₁, callRd s₂, callWr s₂, Rsa.RISCV64.Priv.pre_of_preP (preP_entry h₁.1 A₁),
    Rsa.RISCV64.Priv.pre_of_preP (preP_entry h₂.1 A₂), priv_pub h₁ h₂ A₁ A₂,
    (call_covers h₁.1 A₁).1, (call_covers h₁.1 A₁).2, (call_covers h₂.1 A₂).1, (call_covers h₂.1 A₂).2⟩

/-! ## The chain -/

theorem sign_rel :
    RelCT isa (Two fun a t => (∃ s, E a s ∧ AtAft s t) ∧ isa.eval (.zero .a0) t = some false)
      (.seq (.block callArgs) (.seq privCall wipe)) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, E a s ∧ AtCall s t em)
    (callArgs_taint fun _ _ _ ⟨⟨s₁, h₁, B₁⟩, _⟩ ⟨⟨s₂, h₂, B₂⟩, _⟩ =>
      ⟨by rw [B₁.sp, B₂.sp, fb_same h₁ h₂], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨⟨s, h, B⟩, hz⟩ => ?_) ?_
  · have he := B.enc
    rw [eval_zero, B.a0_eq] at hz
    revert he
    cases hc : encOut s with
    | none => rw [hc] at hz; simp at hz
    | some em => intro ⟨_, hb⟩; exact WP.mono (callArgs_ok h.1 B hb) fun v C => ⟨s, em, h, C⟩
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, E a s ∧ AtRet s t em) priv_rel
    fun a u ⟨s, em, h, C⟩ => call_ok h.1 C fun v R => ⟨s, em, h, R⟩) ?_
  exact wipe_taint fun _ _ _ ⟨s₁, _, h₁, R₁⟩ ⟨s₂, _, h₂, R₂⟩ =>
    ⟨by rw [R₁.sp, R₂.sp, fb_same h₁ h₂], fun r hr => by
      rw [List.mem_singleton.mp hr, R₁.s3, R₂.s3, gpr_same h₁ h₂]⟩

theorem aft_rel : RelCT isa (Two fun a t => ∃ s, E a s ∧ AtAft s t) afterEnc fun _ _ => True := by
  unfold afterEnc
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, B₁⟩ ⟨s₂, h₂, B₂⟩ => by
      rw [eval_zero, eval_zero, B₁.a0_eq, B₂.a0_eq, isSome_same h₁ h₂])
    (zeroOut_taint fun _ _ _ ⟨⟨s₁, h₁, B₁⟩, _⟩ ⟨⟨s₂, h₂, B₂⟩, _⟩ => ⟨by rw [B₁.sp, B₂.sp, fb_same h₁ h₂],
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [B₁.s1, B₂.s1, gpr_same h₁ h₂]
        · rw [B₁.s3, B₂.s3, gpr_same h₁ h₂]⟩) sign_rel

theorem code_ct : RelCT isa (Two E) code fun _ _ => True := by
  unfold code
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ AtEnc s t)
    (setup_taint fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show s₁.sp - _ = s₂.sp - _; rw [h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨s, h, hu⟩ => hu ▸ WP.mono (setup_ok h.1) fun t ht => ⟨s, h, ht⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ AtAft s t)
    (encode_taint fun _ _ _ ⟨s₁, h₁, A₁⟩ ⟨s₂, h₂, A₂⟩ => ⟨by rw [A₁.sp, A₂.sp, fb_same h₁ h₂], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [A₁.a1, A₂.a1, fb_same h₁ h₂]
      · rw [A₁.a2, A₂.a2, gpr_same h₁ h₂]
      · exact BitVec.eq_of_toNat_eq (by rw [A₁.a3, A₂.a3, hid_same h₁ h₂])
      · rw [A₁.a4, A₂.a4, gpr_same h₁ h₂]
      · rw [A₁.a5, A₂.a5, arg_same h₁ h₂]⟩)
    fun a t ⟨s, h, A⟩ => WP.mono (enc_ok h.1 A) fun u B => ⟨s, h, B⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ SMid [oR s, sR s] s t) aft_rel
    fun a t ⟨s, h, B⟩ => WP.mono (afterEnc_ok h.1 B) fun v ⟨M, _⟩ => ⟨s, h, M⟩) ?_
  exact restore_taint fun _ _ _ ⟨s₁, h₁, M₁⟩ ⟨s₂, h₂, M₂⟩ =>
    ⟨by rw [M₁.sp, M₂.sp, fb_same h₁ h₂], fun _ h => absurd h List.not_mem_nil⟩

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes).pre
      (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes).pub code :=
  RelCT.constantTime (code_ct.mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨sPre_of h₁, ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl⟩⟩, sPre_of h₂, pubS_of hp⟩)
    fun _ _ h => h)

/-! ## A state meeting the precondition -/

/-- A modulus of 64 bytes, `e`, the hash value, the primes, exponents and
`qInv` of a byte each, 1056 words of working space; our stack arguments at
`sp`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a7 => 0x5000
    | _ => 0
  sp := 0x10000
  mem a :=
    bif Nat.beq a.toNat 0x10000 then 1 else bif Nat.beq a.toNat 0x10009 then 0x41
    else bif Nat.beq a.toNat 0x10010 then 1 else bif Nat.beq a.toNat 0x10019 then 0x42
    else bif Nat.beq a.toNat 0x10020 then 1 else bif Nat.beq a.toNat 0x10029 then 0x43
    else bif Nat.beq a.toNat 0x10030 then 1 else bif Nat.beq a.toNat 0x10039 then 0x44
    else bif Nat.beq a.toNat 0x10040 then 1 else bif Nat.beq a.toNat 0x10049 then 0x45
    else bif Nat.beq a.toNat 0x10050 then 1 else bif Nat.beq a.toNat 0x1005A then 0x02
    else bif Nat.beq a.toNat 0x10060 then 0x20 else bif Nat.beq a.toNat 0x10061 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x5000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x10000, 104⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem sat_args : stackArg satState 0 = 1 ∧ stackArg satState 1 = 0x4100 ∧ stackArg satState 2 = 1 ∧
    stackArg satState 3 = 0x4200 ∧ stackArg satState 4 = 1 ∧ stackArg satState 5 = 0x4300 ∧
    stackArg satState 6 = 1 ∧ stackArg satState 7 = 0x4400 ∧ stackArg satState 8 = 1 ∧
    stackArg satState 9 = 0x4500 ∧ stackArg satState 10 = 1 ∧ stackArg satState 11 = 0x20000 ∧
    stackArg satState 12 = 1056 := by
  decide

theorem sat : ∃ s, (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes).pre s := by
  refine ⟨satState, ?_⟩
  have e : stackBytes = 4415 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_thirteen, List.append_eq, List.range, List.range.loop]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := sat_args
  have ha : stackArgAddr satState 0 = 0x10000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, ha]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by unfold Spec.Rsa.lenValid; decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem code_verified : Verified RISCV64.target code (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes) :=
  ⟨code_correct, code_constantTime, sat⟩

end VG.Proof.RsaPkcs1Sig.RISCV64.Sign
