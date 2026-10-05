import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
import VerifiedGarbage.Impl.MlDsa.X86.Verify.Verify
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Proof.MlKem.X86.Decaps
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.X86.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.X86.Sample.BallTop
import VerifiedGarbage.Proof.MlDsa.X86.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86.Round.HintF
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackEnd

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Prim`. -/
section

/-!
# ML-DSA on x86 (32-bit): calls of the primitives verification calls

As `KeyGen/Prim.lean`, for the signatures of `vg_mldsa_sample_in_ball`,
`vg_mldsa_use_hint`, `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1`,
`vg_mldsa_hint_bit_unpack` and `vg_mldsa_norm_lt` (which may not write its
arguments: `callPR_pieceRO`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.KeyGen (Arg argRegs setArgs callP callPR)
open VG.Spec.MlDsa (Poly Reduced PolyIs polyAt)

variable {Y : VG.Proof.MlKem.X86.Top.Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-! ## `vg_mldsa_sample_in_ball` -/

theorem ball_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.sampleInBallContract X86.abi stk)
    (da dO L τ aa ao wa wo : Nat) (hb : (L, τ) ∈ Spec.MlDsa.ballParams)
    (hk : (Y.ok ⟨da, dO, L⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨wa, wo, 2048⟩ && Y.sep ⟨da, dO, L⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, L⟩ ⟨wa, wo, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨wa, wo, 2048⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨da, dO, L⟩, .imm L, .imm τ, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩]))
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, L⟩) L = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, L⟩) L)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] 80) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Spec.MlDsa.Outcome (fun b => (Spec.MlDsa.sampleInBall τ b.ball
        (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, L⟩) L)).map Spec.MlDsa.toRq) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callPR Y.sc "vg_mldsa_sample_in_ball" c
        [.buf ⟨da, dO, L⟩, .imm L, .imm τ, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hD, hAw⟩, hW⟩, dDA⟩, dDW⟩, dAW⟩ := hk
  have hA₁ := (Lay.okW_iff.mp hAw).1
  have hW₁ := (Lay.okW_iff.mp hW).1
  have hbnd : L < 2 ^ 32 ∧ τ < 2 ^ 32 := by
    simp only [Spec.MlDsa.ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb; omega
  have eL : (BitVec.ofNat 32 L).toNat = L := KeyGen.toNat_ofNat32 hbnd.1
  have eτ : (BitVec.ofNat 32 τ).toNat = τ := KeyGen.toNat_ofNat32 hbnd.2
  refine callPR_piece _ [⟨da, dO, L⟩] [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hD, hA₁, hW₁, hbnd]) hN (by simp [hD]) (by simp [hAw, hW]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨b₁, b₂, b₃, b₄⟩ := he.buf hp hN (by simp) hD hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hA₁ hK
    obtain ⟨w₁, w₂, w₃, w₄⟩ := he.buf hp hN (by simp) hW₁ hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hD hA₁ dDA
    have d₂ := Buf.disj hp hD hW₁ dDW
    have d₃ := Buf.disj hp hA₁ hW₁ dAW
    have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eL, eτ] at *
    have := hb
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hD, hA₁, hW₁, hbnd]) he he'
    have hs := hseed s₀ s₀' s s' hp hp' hq ha ha'
    have a₀ := he.arg 0 (by simp)
    have a₀' := he'.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₁' := he'.arg 1 (by simp)
    rw [← Proof.MlKem.bytesAt_congr (he.mem _ hD), ← Proof.MlKem.bytesAt_congr (he'.mem _ hD)] at hs
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Arg.val] at a₀ a₀' a₁ a₁'
    simp only [Buf.addr, ← a₀, ← a₀'] at hs
    simp only [arg_withRegions]
    refine ⟨esp, ?_, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
    rw [a₁, a₁', eL, hs]
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂, g₂,
      sw_app, eL, eτ] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hD)] at post
    exact hQ s₀ s s' hp ha h' fr post.1 post.2

/-! ## `vg_mldsa_use_hint` -/

theorem useHint_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.useHintContract X86.abi stk)
    (ha hao ra ro g oa oo : Nat) (hg : g ∈ Spec.MlDsa.gamma2s)
    (hk : (Y.ok ⟨ha, hao, 1024⟩ && Y.ok ⟨ra, ro, 1024⟩ && Y.okW ⟨oa, oo, 1024⟩ && Y.sep ⟨ha, hao, 1024⟩ ⟨oa, oo, 1024⟩ &&
      Y.sep ⟨ra, ro, 1024⟩ ⟨oa, oo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ha, hao, 1024⟩, .buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨oa, oo, 1024⟩]))
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ [⟨oa, oo, 1024⟩] 80) s.mem s'.mem →
      Spec.MlDsa.NatPolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        (Vector.zipWith (fun hj rj => (Spec.MlDsa.useHint g hj rj).toNat)
          ((Spec.MlDsa.hintAt s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩) 1).headD (Vector.replicate Spec.MlDsa.n false))
          (polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc "vg_mldsa_use_hint" c [.buf ⟨ha, hao, 1024⟩, .buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨oa, oo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨hH, hR⟩, hOw⟩, dHO⟩, dRO⟩ := hk
  have hO := (Lay.okW_iff.mp hOw).1
  have hgb : g < 2 ^ 32 := by
    simp only [Spec.MlDsa.gamma2s, Spec.MlDsa.q, List.mem_cons, List.not_mem_nil, or_false] at hg; omega
  have eg : (BitVec.ofNat 32 g).toNat = g := KeyGen.toNat_ofNat32 hgb
  refine callP_piece _ [⟨ha, hao, 1024⟩, ⟨ra, ro, 1024⟩] [⟨oa, oo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hH, hR, hO, hgb]) hN (by simp [hH, hR]) (by simp [hOw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨r₁, r₂, r₃, r₄⟩ := he.buf hp hN (by simp) hR hK
    obtain ⟨o₁, o₂, o₃, o₄⟩ := he.buf hp hN (by simp) hO hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hH hO dHO
    have d₂ := Buf.disj hp hR hO dRO
    have rr := ent_reduced he hR (hA s₀ s hp ha).2
    have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.useHintContract, Spec.MlDsa.useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eg] at *
    have := hg
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hH, hR, hO, hgb]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.useHintContract, Spec.MlDsa.useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.useHintContract, Spec.MlDsa.useHintSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂,
      eg] at post
    rw [ent_polyAt he hR, Proof.MlDsa.Pack.hintAt_congr (fun t ht =>
      Proof.MlDsa.KeyGen.coeffAt_congr (he.mem _ hH) (by simp only [Spec.MlDsa.n]; omega))] at post
    exact hQ s₀ s s' hp ha h' fr post

/-! ## `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1` -/

theorem bu_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.bitUnpackContract X86.abi stk)
    (va vo L a b fa fo : Nat) (hab : (a, b) ∈ Spec.MlDsa.bitPackParams) (hL : L = 32 * Spec.MlDsa.bitlen (a + b))
    (hk : (Y.ok ⟨va, vo, L⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨va, vo, L⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨va, vo, L⟩, .imm L, .imm a, .imm b, .buf ⟨fa, fo, 1024⟩])) ht).isSome
      = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨va, vo, L⟩) L) a b)) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc "vg_mldsa_bit_unpack" c [.buf ⟨va, vo, L⟩, .imm L, .imm a, .imm b, .buf ⟨fa, fo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hV, hFw⟩, dVF⟩ := hk
  have hF := (Lay.okW_iff.mp hFw).1
  obtain ⟨hav, hbv, hL'⟩ := bp_bounds (a, b) hab
  rw [← hL] at hL'
  have ea : (BitVec.ofNat 32 a).toNat = a := KeyGen.toNat_ofNat32 hav
  have eb : (BitVec.ofNat 32 b).toNat = b := KeyGen.toNat_ofNat32 hbv
  have eL : (BitVec.ofNat 32 L).toNat = L := KeyGen.toNat_ofNat32 hL'
  refine callP_piece _ [⟨va, vo, L⟩] [⟨fa, fo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hV, hav, hbv, hL']) hN (by simp [hV]) (by simp [hFw]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨v₁, v₂, v₃, v₄⟩ := he.buf hp hN (by simp) hV hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hV hF dVF
    have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.bitUnpackContract, Spec.MlDsa.bitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, ea, eb,
      eL] at *
    have := hab
    have := hL
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hF, hV, hav, hbv, hL']) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.bitUnpackContract, Spec.MlDsa.bitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.bitUnpackContract, Spec.MlDsa.bitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, a₄, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂,
      ea, eb, eL] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hV)] at post
    exact hQ s₀ s s' hp ha h' fr post

theorem t1_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.unpackT1Contract X86.abi stk)
    (va vo fa fo : Nat)
    (hk : (Y.ok ⟨va, vo, 320⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨va, vo, 320⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨va, vo, 320⟩, .buf ⟨fa, fo, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        ((Spec.MlDsa.simpleBitUnpack (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨va, vo, 320⟩) 320) Spec.MlDsa.t1Max).map
          fun c => Spec.MlDsa.ofInt (c * 2 ^ Spec.MlDsa.d : Nat)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc "vg_mldsa_unpack_t1" c [.buf ⟨va, vo, 320⟩, .buf ⟨fa, fo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hV, hFw⟩, dVF⟩ := hk
  have hF := (Lay.okW_iff.mp hFw).1
  refine callP_piece _ [⟨va, vo, 320⟩] [⟨fa, fo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hV]) hN (by simp [hV]) (by simp [hFw]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨v₁, v₂, v₃, v₄⟩ := he.buf hp hN (by simp) hV hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hV hF dVF
    have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.unpackT1Contract, Spec.MlDsa.unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hF, hV]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.unpackT1Contract, Spec.MlDsa.unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.unpackT1Contract, Spec.MlDsa.unpackT1Sig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hV)] at post
    exact hQ s₀ s s' hp ha h' fr post

/-! ## `vg_mldsa_hint_bit_unpack` -/

theorem hu_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.hintBitUnpackContract X86.abi stk)
    (ya yo ω k ha ho : Nat) (hwk : (ω, k) ∈ Spec.MlDsa.hintParams)
    (hk : (Y.ok ⟨ya, yo, ω + k⟩ && Y.okW ⟨ha, ho, 256 * k * 4⟩ && Y.sep ⟨ya, yo, ω + k⟩ ⟨ha, ho, 256 * k * 4⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ya, yo, ω + k⟩, .imm (ω + k), .imm ω, .buf ⟨ha, ho, 256 * k * 4⟩,
        .imm (256 * k)])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ya, yo, ω + k⟩) (ω + k) =
        Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨ya, yo, ω + k⟩) (ω + k))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ [⟨ha, ho, 256 * k * 4⟩] 80) s.mem s'.mem →
      (match Spec.MlDsa.hintBitUnpack ω k (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ya, yo, ω + k⟩) (ω + k)) with
        | some hint => s'.gpr .eax = 1 ∧ Spec.MlDsa.HintIs s'.mem (Buf.addr s₀ ⟨ha, ho, 256 * k * 4⟩) k hint
        | none => s'.gpr .eax = 0) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callPR Y.sc "vg_mldsa_hint_bit_unpack" c [.buf ⟨ya, yo, ω + k⟩, .imm (ω + k), .imm ω,
        .buf ⟨ha, ho, 256 * k * 4⟩, .imm (256 * k)]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hYb, hHw⟩, dYH⟩ := hk
  have hH := (Lay.okW_iff.mp hHw).1
  have hb : ω + k < 2 ^ 32 ∧ ω < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
    simp only [Spec.MlDsa.hintParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwk; omega
  have e1 : (BitVec.ofNat 32 (ω + k)).toNat = ω + k := KeyGen.toNat_ofNat32 hb.1
  have e2 : (BitVec.ofNat 32 ω).toNat = ω := KeyGen.toNat_ofNat32 hb.2.1
  have e3 : (BitVec.ofNat 32 (256 * k)).toNat = 256 * k := KeyGen.toNat_ofNat32 hb.2.2
  have e4 : ω + k - ω = k := by omega
  refine callPR_piece _ [⟨ya, yo, ω + k⟩] [⟨ha, ho, 256 * k * 4⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hYb, hH, hb]) hN (by simp [hYb]) (by simp [hHw]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨y₁, y₂, y₃, y₄⟩ := he.buf hp hN (by simp) hYb hK
    obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hYb hH dYH
    have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.hintBitUnpackContract, Spec.MlDsa.hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, e1, e2, e3,
      e4] at *
    have := hwk
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hYb, hH, hb]) he he'
    have hs := hseed s₀ s₀' s s' hp hp' hq ha ha'
    have a₀ := he.arg 0 (by simp)
    have a₀' := he'.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₁' := he'.arg 1 (by simp)
    rw [← Proof.MlKem.bytesAt_congr (he.mem _ hYb), ← Proof.MlKem.bytesAt_congr (he'.mem _ hYb)] at hs
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.hintBitUnpackContract, Spec.MlDsa.hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Arg.val] at a₀ a₀' a₁ a₁'
    simp only [Buf.addr, ← a₀, ← a₀'] at hs
    simp only [arg_withRegions]
    refine ⟨esp, ?_, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
    rw [a₁, a₁', e1, hs]
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.hintBitUnpackContract, Spec.MlDsa.hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂, g₂,
      sw_app, e1, e2, e4] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hYb)] at post
    exact hQ s₀ s s' hp ha h' fr post

/-! ## `vg_mldsa_norm_lt` -/

theorem normLt_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.normLtContract X86.abi stk)
    (fa fo bd : Nat) (hbd : bd < 2 ^ 32) (hk : Y.ok ⟨fa, fo, 1024⟩ = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .imm bd])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ [] 80) s.mem s'.mem →
      s'.gpr .eax = (if Spec.MlDsa.normRq [polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)] < bd then 1 else 0) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (VG.Impl.MlDsa.X86.KeyGen.callPR Y.sc "vg_mldsa_norm_lt" c [.buf ⟨fa, fo, 1024⟩, .imm bd]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  have eb : (BitVec.ofNat 32 bd).toNat = bd := KeyGen.toNat_ofNat32 hbd
  refine callPR_pieceRO _ [⟨fa, fo, 1024⟩] [] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hk, hbd]) hN (by simp [hk]) (by simp) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hk hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have rf := ent_reduced he hk (hA s₀ s hp ha).2
    have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eb] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hk, hbd]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, g₂, sw_app,
      eb] at post
    rw [ent_polyAt he hk] at post
    exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Base`. -/
section

/-!
# ML-DSA verification on x86 (32-bit): the setting

Verification is proven for any implementations of the primitives it calls that
are verified against their contracts (`PrimsOk`), as key generation
(`Proof/MlDsa/X86/KeyGen/`): the contract's precondition gives the layout of
the arguments (`YV p`: `pk`, `mu`, `sig` and `scratch`, and 96 bytes of stack;
`pre_of`), and its public data the pointers and the inputs, as bytes (`lkV`,
`pub_of`). What the proof uses of a parameter set is `VFacts`; `layv` proves
the checks of buffers against the layout.
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-- Verified implementations of the primitives verification calls. -/
structure PrimsOk (P : Prims) : Prop where
  ntt : Callee P.ntt (fun stk => Spec.MlDsa.nttContract X86.abi stk)
  invNtt : Callee P.invNtt (fun stk => Spec.MlDsa.nttInvContract X86.abi stk)
  mul : Callee P.mul (fun stk => Spec.MlDsa.mulContract X86.abi stk)
  mulAdd : Callee P.mulAdd (fun stk => Spec.MlDsa.mulAddContract X86.abi stk)
  sub : Callee P.sub (fun stk => Spec.MlDsa.subContract X86.abi stk)
  rejNtt : Callee P.rejNtt (fun stk => Spec.MlDsa.rejNTTContract X86.abi stk)
  ball : Callee P.ball (fun stk => Spec.MlDsa.sampleInBallContract X86.abi stk)
  useHint : Callee P.useHint (fun stk => Spec.MlDsa.useHintContract X86.abi stk)
  simpleBitPack : Callee P.simpleBitPack (fun stk => Spec.MlDsa.simpleBitPackContract X86.abi stk)
  bitUnpack : Callee P.bitUnpack (fun stk => Spec.MlDsa.bitUnpackContract X86.abi stk)
  unpackT1 : Callee P.unpackT1 (fun stk => Spec.MlDsa.unpackT1Contract X86.abi stk)
  hintUnpack : Callee P.hintUnpack (fun stk => Spec.MlDsa.hintBitUnpackContract X86.abi stk)
  normLt : Callee P.normLt (fun stk => Spec.MlDsa.normLtContract X86.abi stk)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure VFacts (p : Params) : Prop where
  k : 1 ≤ p.k ∧ p.k ≤ 8
  l : 1 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : 4 ≤ p.k * p.ℓ ∧ p.k * p.ℓ ≤ 56
  ct : 32 ≤ p.ctildeLen ∧ p.ctildeLen ≤ 64
  lz : 576 ≤ lenZ p ∧ lenZ p ≤ 640
  w1 : 128 ≤ w1Len p ∧ 512 ≤ p.k * w1Len p ∧ p.k * w1Len p ≤ 1024
  scr : 8192 + 1024 * (20 + 8 * p.k) ≤ scratchWords p * 8
  pk : p.pkLen = 32 + 320 * p.k
  sig : p.sigLen = p.ctildeLen + lenZ p * p.ℓ + p.ω + p.k
  sw : scratchWords p = 128 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32)
  om : p.ω ≤ 80
  hint : (p.ω, p.k) ∈ Spec.MlDsa.hintParams
  ball : (p.ctildeLen, p.τ) ∈ Spec.MlDsa.ballParams
  g1 : p.γ₁ ∈ Proof.MlDsa.Verify.gamma1s
  bp : (p.γ₁ - 1, p.γ₁) ∈ Spec.MlDsa.bitPackParams ∧ lenZ p = 32 * Spec.MlDsa.bitlen (p.γ₁ - 1 + p.γ₁)
  beta : 0 < p.γ₁ - p.β ∧ p.γ₁ - p.β < 2 ^ 32
  g2 : p.γ₂ ∈ Spec.MlDsa.gamma2s
  sbp : w1Max p ∈ Spec.MlDsa.simpleBitPackBounds ∧ w1Len p = 32 * Spec.MlDsa.bitlen (w1Max p)

theorem vfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VG.Proof.MlDsa.X86.Verify.VFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, rfl,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## The layout -/

/-- The size of `scratch`, in bytes. -/
abbrev scrLenV (p : Params) : Nat := scratchWords p * 8

/-- `pk`, `mu` and `sig` (read), `scratch` (written); 96 bytes of stack. -/
def YV (p : Params) : VG.Proof.MlKem.X86.Top.Lay := ⟨[(p.pkLen, false), (64, false), (p.sigLen, false), (VG.Proof.MlDsa.X86.Verify.scrLenV p, true)], 3, 96⟩

theorem YV_sc (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).sc = vS := rfl
theorem YV_stk (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).stk = 96 := rfl
theorem stkV {p : Params} {N : Nat} (h : N + 16 ≤ 96) : N + 16 ≤ (VG.Proof.MlDsa.X86.Verify.YV p).stk := h
theorem YV_n (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).n = 4 := rfl
theorem YV_alen0 (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).alen 0 = p.pkLen := rfl
theorem YV_alen1 (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).alen 1 = 64 := rfl
theorem YV_alen2 (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).alen 2 = p.sigLen := rfl
theorem YV_alen3 (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).alen 3 = VG.Proof.MlDsa.X86.Verify.scrLenV p := rfl
theorem YV_awr0 (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).awr 0 = false := rfl
theorem YV_awr1 (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).awr 1 = false := rfl
theorem YV_awr2 (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).awr 2 = false := rfl
theorem YV_awr3 (p : Params) : (VG.Proof.MlDsa.X86.Verify.YV p).awr 3 = true := rfl

/-! ### Checks of buffers, as arithmetic -/

/-- The result, a word of `scratch`. -/
abbrev accB (Y : VG.Proof.MlKem.X86.Top.Lay) : Buf := ⟨Y.sc, oACC, 4⟩

theorem okS {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ scratchWords p * 8) :
    (VG.Proof.MlDsa.X86.Verify.YV p).ok ⟨3, o, l⟩ = true := Lay.ok_iff.mpr ⟨show 3 < 4 by decide, h₁, h₂⟩

theorem okWS {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ scratchWords p * 8) :
    (VG.Proof.MlDsa.X86.Verify.YV p).okW ⟨3, o, l⟩ = true := Lay.okW_iff.mpr ⟨VG.Proof.MlDsa.X86.Verify.okS h₁ h₂, rfl⟩

theorem okPk {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ p.pkLen) : (VG.Proof.MlDsa.X86.Verify.YV p).ok ⟨0, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨show 0 < 4 by decide, h₁, h₂⟩

theorem okMu {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ 64) : (VG.Proof.MlDsa.X86.Verify.YV p).ok ⟨1, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨show 1 < 4 by decide, h₁, h₂⟩

theorem okSig {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ p.sigLen) : (VG.Proof.MlDsa.X86.Verify.YV p).ok ⟨2, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨show 2 < 4 by decide, h₁, h₂⟩

theorem sepS {p : Params} {o₁ l₁ o₂ l₂ : Nat} (h : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (VG.Proof.MlDsa.X86.Verify.YV p).sep ⟨3, o₁, l₁⟩ ⟨3, o₂, l₂⟩ = true := by
  unfold Lay.sep
  simp only [ite_true, Bool.or_eq_true, decide_eq_true_eq]
  exact h

theorem sepRS {p : Params} {a o₁ l₁ o₂ l₂ : Nat} (ha : a < 3) : (VG.Proof.MlDsa.X86.Verify.YV p).sep ⟨a, o₁, l₁⟩ ⟨3, o₂, l₂⟩ = true := by
  unfold Lay.sep
  rw [ite_eq_right_iff.mpr fun h => absurd h (show a ≠ 3 by omega)]
  exact Bool.or_eq_true_iff.mpr (.inr rfl)

theorem sepSR {p : Params} {a o₁ l₁ o₂ l₂ : Nat} (ha : a < 3) : (VG.Proof.MlDsa.X86.Verify.YV p).sep ⟨3, o₁, l₁⟩ ⟨a, o₂, l₂⟩ = true := by
  unfold Lay.sep
  rw [ite_eq_right_iff.mpr fun h => absurd h (show 3 ≠ a by omega)]
  exact Bool.or_eq_true_iff.mpr (.inl rfl)

theorem apart_nil' {Y : VG.Proof.MlKem.X86.Top.Lay} {b : Buf} (h : Y.ok b = true) : Y.apart b [] = true := by
  simp [Lay.apart, h]

theorem apart_cons' {Y : VG.Proof.MlKem.X86.Top.Lay} {b c : Buf} {bs : List Buf} (h₁ : Y.apart b bs = true) (h₂ : Y.ok c = true)
    (h₃ : Y.sep b c = true) : Y.apart b (c :: bs) = true := by
  simp only [Lay.apart, List.all_cons, Bool.and_eq_true] at h₁ ⊢
  exact ⟨h₁.1, ⟨h₂, h₃⟩, h₁.2⟩

/-- Rows of `z` in the signature, and of `w₁` in `scratch`. -/
theorem mul_row {a i n : Nat} (hi : i < n) : a * i + a ≤ a * n := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-- Proves checks of buffers against the layout (`ok`, `okW`, `sep`, `apart`),
from arithmetic on their offsets closed by `omega`, with the facts of the
parameter set `hF : VFacts p` and those in the context. -/
syntax "lv " term:max : tactic
macro_rules
  | `(tactic| lv $hF) => `(tactic| (
      try simp only [Bool.and_eq_true, VG.Proof.MlDsa.X86.Verify.accB, VG.Proof.MlDsa.X86.Verify.YV_sc,
        VG.Proof.MlDsa.X86.KeyGen.chk3]
      try and_intros
      repeat' (first
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.apart_cons'
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.apart_nil'
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.okWS | with_reducible apply VG.Proof.MlDsa.X86.Verify.okS
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.okPk | with_reducible apply VG.Proof.MlDsa.X86.Verify.okMu
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.okSig | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepS
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepRS
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepSR)
      all_goals (
        have := ($hF).k; have := ($hF).l; have := ($hF).ct; have := ($hF).om; have := ($hF).lz
        have := ($hF).w1; have := ($hF).scr; have := ($hF).pk; have := ($hF).sig
        try simp only [VG.Impl.MlDsa.X86.Verify.oP, VG.Impl.MlDsa.X86.Verify.oSB, VG.Impl.MlDsa.X86.Verify.oB,
          VG.Impl.MlDsa.X86.Verify.oCT, VG.Impl.MlDsa.X86.Verify.oACC, VG.Impl.MlDsa.X86.Verify.oSS,
          VG.Impl.MlDsa.X86.Verify.oHint]
        omega_arith)))

/-! ## The inputs -/

section
variable (p : Params) (s₀ : State)

abbrev vPk : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen
abbrev vMu : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64
abbrev vSig : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨2, 0, p.sigLen⟩) p.sigLen

/-- What verification may leak, its inputs. -/
def lkV : List Byte := VG.Proof.MlDsa.X86.Verify.vPk p s₀ ++ VG.Proof.MlDsa.X86.Verify.vMu s₀ ++ VG.Proof.MlDsa.X86.Verify.vSig p s₀

/-- The result so far. -/
abbrev accV (s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (sb oACC 4)) 32

end

/-- A piece of verification. -/
abbrev VP (p : Params) := Piece (TPre (VG.Proof.MlDsa.X86.Verify.YV p)) (TPub (VG.Proof.MlDsa.X86.Verify.YV p) (VG.Proof.MlDsa.X86.Verify.lkV p))

theorem inputs_pub {p : Params} {s₀ s₀' : State} (hq : TPub (VG.Proof.MlDsa.X86.Verify.YV p) (VG.Proof.MlDsa.X86.Verify.lkV p) s₀ s₀') :
    VG.Proof.MlDsa.X86.Verify.vPk p s₀ = VG.Proof.MlDsa.X86.Verify.vPk p s₀' ∧ VG.Proof.MlDsa.X86.Verify.vMu s₀ = VG.Proof.MlDsa.X86.Verify.vMu s₀' ∧ VG.Proof.MlDsa.X86.Verify.vSig p s₀ = VG.Proof.MlDsa.X86.Verify.vSig p s₀' := by
  have h := hq.2.2
  simp only [VG.Proof.MlDsa.X86.Verify.lkV] at h
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [Proof.MlKem.bytesAt_length])
  obtain ⟨h₃, h₄⟩ := List.append_inj h₁ (by simp [Proof.MlKem.bytesAt_length])
  exact ⟨h₃, h₄, h₂⟩

/-! ## The contract -/

theorem pre_of {p : Params} {s₀ : State} (h : (Spec.MlDsa.verifyContract p X86.abi 96).pre s₀) :
    TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀ := by
  sig_pre [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h17 h18 h19 h20 h21
  have c4 : ∀ i, i < (VG.Proof.MlDsa.X86.Verify.YV p).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    rw [VG.Proof.MlDsa.X86.Verify.YV_n] at hi; omega
  refine ⟨h1, by rw [VG.Proof.MlDsa.X86.Verify.YV_stk]; omega, by rw [VG.Proof.MlDsa.X86.Verify.YV_n]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h21, ?_, by rw [VG.Proof.MlDsa.X86.Verify.YV_sc, VG.Proof.MlDsa.X86.Verify.YV_n]; decide⟩
  · intro i hi hw
    rw [h3]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · simp [VG.Proof.MlKem.X86.Top.argR, Lay.alen, VG.Proof.MlDsa.X86.Verify.YV]
    · simp [VG.Proof.MlKem.X86.Top.argR, Lay.alen, VG.Proof.MlDsa.X86.Verify.YV]
    · simp [VG.Proof.MlKem.X86.Top.argR, Lay.alen, VG.Proof.MlDsa.X86.Verify.YV]
    · simp [VG.Proof.MlDsa.X86.Verify.YV, Lay.awr] at hw
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    any_goals simp [VG.Proof.MlDsa.X86.Verify.YV, Lay.awr] at hw
    simp [VG.Proof.MlKem.X86.Top.argR, Lay.alen, VG.Proof.MlDsa.X86.Verify.YV, VG.Proof.MlDsa.X86.Verify.scrLenV]
  · rw [h4]; simp [VG.Proof.MlKem.X86.Top.gR, Lay.n, VG.Proof.MlDsa.X86.Verify.YV]
  · intro i hi j hj hne hw
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | skip
    all_goals simp only [VG.Proof.MlDsa.X86.Verify.YV_awr0, VG.Proof.MlDsa.X86.Verify.YV_awr1, VG.Proof.MlDsa.X86.Verify.YV_awr2, VG.Proof.MlDsa.X86.Verify.YV_awr3, Bool.or_false, Bool.or_true,
      Bool.false_eq_true] at hw
    all_goals simp only [VG.Proof.MlKem.X86.Top.argR, VG.Proof.MlDsa.X86.Verify.YV_alen0, VG.Proof.MlDsa.X86.Verify.YV_alen1, VG.Proof.MlDsa.X86.Verify.YV_alen2, VG.Proof.MlDsa.X86.Verify.YV_alen3, VG.Proof.MlDsa.X86.Verify.scrLenV]
    exacts [h5, h7, h9, h5.symm, h7.symm, h9.symm]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.MlKem.X86.Top.argR, VG.Proof.MlKem.X86.Top.gR, VG.Proof.MlDsa.X86.Verify.YV_n, VG.Proof.MlDsa.X86.Verify.YV_alen0, VG.Proof.MlDsa.X86.Verify.YV_alen1, VG.Proof.MlDsa.X86.Verify.YV_alen2, VG.Proof.MlDsa.X86.Verify.YV_alen3, VG.Proof.MlDsa.X86.Verify.scrLenV]
    · exact h6.symm
    · exact h8.symm
    · exact h10.symm
    · exact h11.symm
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.MlKem.X86.Top.argR, VG.Proof.MlDsa.X86.Verify.YV_alen0, VG.Proof.MlDsa.X86.Verify.YV_alen1, VG.Proof.MlDsa.X86.Verify.YV_alen2, VG.Proof.MlDsa.X86.Verify.YV_alen3, VG.Proof.MlDsa.X86.Verify.scrLenV]
    · exact h12
    · exact h13
    · exact h14
    · exact h15
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.MlKem.X86.Top.argR, VG.Proof.MlDsa.X86.Verify.YV_stk, VG.Proof.MlDsa.X86.Verify.YV_alen0, VG.Proof.MlDsa.X86.Verify.YV_alen1, VG.Proof.MlDsa.X86.Verify.YV_alen2, VG.Proof.MlDsa.X86.Verify.YV_alen3, VG.Proof.MlDsa.X86.Verify.scrLenV]
    · exact h17
    · exact h18
    · exact h19
    · exact h20
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [VG.Proof.MlDsa.X86.Verify.YV_alen0, VG.Proof.MlDsa.X86.Verify.YV_alen1, VG.Proof.MlDsa.X86.Verify.YV_alen2, VG.Proof.MlDsa.X86.Verify.YV_alen3, VG.Proof.MlDsa.X86.Verify.scrLenV]
    · exact h22
    · exact h23
    · exact h24
    · exact h25

theorem pub_of {p : Params} {s₀ s₀' : State} (h : (Spec.MlDsa.verifyContract p X86.abi 96).pub s₀ s₀') :
    TPub (VG.Proof.MlDsa.X86.Verify.YV p) (VG.Proof.MlDsa.X86.Verify.lkV p) s₀ s₀' := by
  sig_pub [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · rw [VG.Proof.MlDsa.X86.Verify.YV_n] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · simp only [VG.Proof.MlDsa.X86.Verify.lkV, VG.Proof.MlDsa.X86.Verify.vPk, VG.Proof.MlDsa.X86.Verify.vMu, VG.Proof.MlDsa.X86.Verify.vSig, VG.Proof.MlDsa.X86.KeyGen.addr0]
    exact Proof.MlDsa.KeyGen.leakBytes_inj e₂

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Local`. -/
section

/-!
# ML-DSA verification on x86 (32-bit): the code between the calls

The result ANDed with `eax` (`accAnd_piece`); a branch on the result so far
(`ifOk_piece`), whose condition must be public; and the result ANDed with the
equality of two byte strings, compared without a branch on them
(`cmpAnd_piece`): `edx` is the OR of the XORs of their bytes (`Decaps.accB`),
and `sub edx, 1; sbb eax, eax` all ones exactly when it is 0.
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.Sha3 (bytesAt)

variable {Y : VG.Proof.MlKem.X86.Top.Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-! ## The result ANDed with `eax` -/

theorem accAnd_wp {s₀ s : State} (hp : TPre Y s₀) (hc : Y.okW (VG.Proof.MlDsa.X86.Verify.accB Y) = true) (h : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    {Q : State → Prop}
    (k : ∀ s', VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) (s.mem.readW (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) 32 &&& s.gpr .eax) → Q s') :
    WP isa (.block accAnd) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := 4) (Nat.le_refl _)
  simp only [BitVec.add_zero] at hcr
  have hin : InRegions s.wr (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) 4 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  have hinR : InRegions (s.rd ++ s.wr) (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) 4 := by
    have := Buf.inRegR hp hc₁ h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  have ea : s.ea (at_ .esi oACC) = Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y) := by simp only [State.ea, at_]; rw [h.esi]
  refine wp_movm' (by rw [ea]; exact hinR) fun s₁ o₁ v₁ => ?_
  have h₁ := h.only o₁ (by decide) (by decide)
  refine wp_andr fun s₂ o₂ v₂ => ?_
  have h₂ := h₁.only o₂ (by decide) (by decide)
  have ea₂ : s₂.ea (at_ .esi oACC) = Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y) := by simp only [State.ea, at_]; rw [h₂.esi]
  refine wp_store' (by rw [ea₂, h₂.wr, ← h.wr]; exact hin) fun s₃ g₃ r₃ w₃ m₃ => WP.block_nil_iff.mpr ?_
  refine k _ ⟨by rw [g₃]; exact h₂.esp, by rw [r₃]; exact h₂.rd, by rw [w₃]; exact h₂.wr,
    by rw [g₃]; exact h₂.esi, ?_⟩ ?_
  · rw [m₃, ea₂]; exact h₂.frame.writeW hr _ hcr
  · rw [m₃, ea₂, o₂.mem, o₁.mem, v₂, v₁, ea, o₁.gpr .eax (by decide)]

theorem accAnd_piece (hc : Y.okW (VG.Proof.MlDsa.X86.Verify.accB Y) = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block accAnd) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) (s.mem.readW (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) 32 &&& s.gpr .eax) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block accAnd) :=
  Piece.taint [.esi] (fun s₀ s hp ha => VG.Proof.MlDsa.X86.Verify.accAnd_wp hp hc (hA s₀ s hp ha) fun s' c' m' => hQ s₀ s s' hp ha c' m')
    (fun s₀ s₀' s s' hp _ hq ha ha' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]) tt

/-- The result set to `eax`. -/
theorem stAcc_piece (hc : Y.okW (VG.Proof.MlDsa.X86.Verify.accB Y) = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block [.store (at_ .esi oACC) .eax]) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → s'.gpr = s.gpr →
      s'.mem = s.mem.writeW (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) (s.gpr .eax) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block [.store (at_ .esi oACC) .eax]) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := 4) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcr
    have hin : InRegions s.wr (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) 4 := by
      have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    have ea : s.ea (at_ .esi oACC) = Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y) := by simp only [State.ea, at_]; rw [h.esi]
    refine wp_store' (by rw [ea]; exact hin) fun s₁ g₁ r₁ w₁ m₁ => WP.block_nil_iff.mpr ?_
    refine hQ s₀ s _ hp ha ⟨by rw [g₁]; exact h.esp, by rw [r₁]; exact h.rd, by rw [w₁]; exact h.wr,
      by rw [g₁]; exact h.esi, ?_⟩ (funext g₁) (by rw [m₁, ea])
    rw [m₁, ea]; exact h.frame.writeW hr _ hcr
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## A branch on the result -/

/-- The empty block. -/
theorem nil_piece {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop}
    (h : ∀ s₀ s, Pre s₀ → A s₀ s → B s₀ s) : Piece Pre Pub A B (.block []) :=
  ⟨fun s₀ s h₀ ha => WP.block_nil_iff.mpr (h s₀ s h₀ ha), fun _ _ _ _ _ => RelCT.nil fun _ _ _ => trivial⟩

theorem ifOk_piece {c : Prog isa} (b : State → Bool) (hc : Y.ok (VG.Proof.MlDsa.X86.Verify.accB Y) = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block [.mov .eax (.mem (at_ .esi oACC)), .alu .test .eax (.reg .eax)])
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hA' : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → s'.mem = s.mem → A s₀ s')
    (hb : ∀ s₀ s, TPre Y s₀ → A s₀ s → (s.mem.readW (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) 32 != 0) = b s₀)
    (hbp : ∀ s₀ s₀', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → b s₀ = b s₀')
    (ht : Piece (TPre Y) (TPub Y lk) (fun s₀ s => A s₀ s ∧ b s₀ = true) B c)
    (he : ∀ s₀ s, TPre Y s₀ → A s₀ s → b s₀ = false → B s₀ s) :
    Piece (TPre Y) (TPub Y lk) A B (VG.Impl.MlDsa.X86.Verify.ifOk c) := by
  unfold VG.Impl.MlDsa.X86.Verify.ifOk
  refine Piece.seq (B := fun s₀ s₁ => A s₀ s₁ ∧ isa.eval .ne s₁ = some (b s₀))
    (Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt)
    (Piece.ite b (fun _ _ _ h => h.2) hbp (ht.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
      (VG.Proof.MlDsa.X86.Verify.nil_piece fun s₀ s hp h => he s₀ s hp h.1.1 h.2))
  · have h := hA s₀ s hp ha
    have hinR : InRegions (s.rd ++ s.wr) (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) 4 := by
      have := Buf.inRegR hp hc h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    have ea : s.ea (at_ .esi oACC) = Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y) := by simp only [State.ea, at_]; rw [h.esi]
    refine wp_movm' (by rw [ea]; exact hinR) fun s₁ o₁ v₁ => ?_
    have h₁ := h.only o₁ (by decide) (by decide)
    refine Wp.wp_test fun s₂ f₂ z₂ => WP.block_nil_iff.mpr ⟨hA' s₀ s s₂ hp ha
      (h₁.same (by rw [f₂.gpr]) (by rw [f₂.gpr]) f₂.rd f₂.wr f₂.mem) (by rw [f₂.mem, o₁.mem]), ?_⟩
    show s₂.zf.map (!·) = _
    rw [z₂, v₁, ea, BitVec.and_self, ← hb s₀ s hp ha]
    rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## The result ANDed with an equality -/

/-- Two byte strings of `n` bytes are equal exactly when `accB` of all their bytes is 0. -/
theorem accB_zero {c c' : List Byte} {n : Nat} (h₁ : c.length = n) (h₂ : c'.length = n) :
    c = c' ↔ Decaps.accB c c' n = 0 := by
  rw [Decaps.accB_eq c c' n (by omega) (by omega), List.take_of_length_le (by omega),
    List.take_of_length_le (by omega)]
  exact eq_iff_foldl_or_xor (by omega)

/-- The comparison, from the setup. -/
structure CL (s₀ : State) (a b : Buf) (m : Mem) (k : Nat) (u : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx Y s₀ u
  mem : u.mem = m
  edi : u.gpr .edi = a.ptr s₀ + BitVec.ofNat 32 k
  ebp : u.gpr .ebp = b.ptr s₀ + BitVec.ofNat 32 k
  ecx : u.gpr .ecx = BitVec.ofNat 32 (a.len - k)
  edx : u.gpr .edx = (Decaps.accB (bytesAt m (Buf.addr s₀ a) a.len) (bytesAt m (Buf.addr s₀ b) a.len) k).setWidth 32

theorem cmp_step {s₀ : State} (hp : TPre Y s₀) {a b : Buf} (ha : Y.ok a = true) (hb : Y.ok b = true)
    (hl : a.len = b.len) (hn : a.len < 2 ^ 32) {m : Mem} {k : Nat} (hk : k < a.len) {u : State}
    (h : VG.Proof.MlDsa.X86.Verify.CL (Y := Y) s₀ a b m k u) :
    WP isa (.block Impl.MlDsa.X86.Verify.cmpBody) u fun u' => VG.Proof.MlDsa.X86.Verify.CL (Y := Y) s₀ a b m (k + 1) u' ∧
      isa.eval .ne u' = some (decide (k + 1 < a.len)) := by
  have fa := Buf.fit hp ha
  have fb := Buf.fit hp hb
  have e₁ : u.ea (at_ .edi 0) = Buf.addr s₀ a + BitVec.ofNat 64 k := by
    simp only [State.ea, at_, h.edi]; rw [ea_add (by omega)]; rfl
  have e₂ : u.ea (at_ .ebp 0) = Buf.addr s₀ b + BitVec.ofNat 64 k := by
    simp only [State.ea, at_, h.ebp]; rw [ea_add (by omega)]; rfl
  have i₁ := Buf.inRegR (o := k) (n := 1) hp ha h.ctx.rd h.ctx.wr (show k + 1 ≤ a.len by omega)
  refine Decaps.wp_movzx' (by rw [e₁]; exact i₁) fun u₁ o₁ v₁ => ?_
  have c₁ := h.ctx.only o₁ (by decide) (by decide)
  have e₂' : u₁.ea (at_ .ebp 0) = Buf.addr s₀ b + BitVec.ofNat 64 k := by
    rw [← e₂]; simp only [State.ea, at_, o₁.gpr .ebp (by decide)]
  have i₂ := Buf.inRegR (o := k) (n := 1) hp hb c₁.rd c₁.wr (show k + 1 ≤ b.len by omega)
  refine Decaps.wp_movzx' (by rw [e₂']; exact i₂) fun u₂ o₂ v₂ => ?_
  refine Decaps.wp_xorr fun u₃ o₃ v₃ => Decaps.wp_orr fun u₄ o₄ v₄ => wp_addi fun u₅ o₅ v₅ =>
    wp_addi fun u₆ o₆ v₆ => wp_subi_last fun u₇ o₇ v₇ z₇ => ?_
  have c₇ := (((((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide)
    (by decide)).only o₅ (by decide) (by decide)).only o₆ (by decide) (by decide)).only o₇ (by decide) (by decide)
  have m₁ : u₁.mem = m := o₁.mem.trans h.mem
  have x₁ : u.mem (Buf.addr s₀ a + BitVec.ofNat 64 k) = (bytesAt m (Buf.addr s₀ a) a.len).getD k 0 := by
    rw [h.mem, bytesAt_getD _ _ hk]
  have x₂ : u₁.mem (Buf.addr s₀ b + BitVec.ofNat 64 k) = (bytesAt m (Buf.addr s₀ b) a.len).getD k 0 := by
    rw [m₁, bytesAt_getD _ _ hk]
  have ex : u₆.gpr .ecx = BitVec.ofNat 32 (a.len - k) := by
    rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
      o₂.gpr _ (by decide), o₁.gpr _ (by decide), h.ecx]
  refine ⟨⟨c₇, by rw [o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, m₁], ?_, ?_, by rw [v₇, ex]; exact cnt_next hk,
    ?_⟩, ?_⟩
  · rw [o₇.gpr .edi (by decide), o₆.gpr .edi (by decide), v₅, o₄.gpr .edi (by decide), o₃.gpr .edi (by decide),
      o₂.gpr .edi (by decide), o₁.gpr .edi (by decide), h.edi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₇.gpr .ebp (by decide), v₆, o₅.gpr .ebp (by decide), o₄.gpr .ebp (by decide), o₃.gpr .ebp (by decide),
      o₂.gpr .ebp (by decide), o₁.gpr .ebp (by decide), h.ebp,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₇.gpr .edx (by decide), o₆.gpr .edx (by decide), o₅.gpr .edx (by decide), v₄, v₃, o₃.gpr .edx (by decide),
      o₂.gpr .edx (by decide), o₂.gpr .eax (by decide), v₂, o₁.gpr .edx (by decide), v₁, h.edx, e₁, e₂', x₁, x₂,
      Decaps.accB, BitVec.setWidth_or, BitVec.setWidth_xor]
  · show u₇.zf.map (!·) = _
    rw [z₇, ex]; exact cnt_ne hk hn

/-- The result ANDed with all ones if the bytes of `a` and `b` are equal, and zero otherwise. -/
theorem cmpAnd_piece (hsc : Y.sc = vS) {a b : Buf} (hc : Y.okW (VG.Proof.MlDsa.X86.Verify.accB Y) = true) (ha : Y.ok a = true)
    (hb : Y.ok b = true) (hl : a.len = b.len) (hn : a.len < 2 ^ 32)
    {h₁ h₂ h₃ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .edi a ++ ptrTo Y.sc .ebp b ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 a.len)), .mov .edx (.imm 0)] : List Instr))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.edi, .ebp, .ecx]) (.loop (.block Impl.MlDsa.X86.Verify.cmpBody) .ne) h₂).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esi])
      (.block (([.alu .sub .edx (.imm 1), .alu .sbb .eax (.reg .eax)] : List Instr) ++ accAnd)) h₃).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) (s.mem.readW (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB Y)) 32 &&&
        Decaps.mask (bytesAt s.mem (Buf.addr s₀ a) a.len = bytesAt s.mem (Buf.addr s₀ b) a.len)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (cmpAnd a b a.len) := by
  unfold cmpAnd
  rw [← hsc]
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup_piece (fun s₀ s₁ => s₁.gpr .edi = a.ptr s₀ ∧ s₁.gpr .ebp = b.ptr s₀ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 a.len ∧ s₁.gpr .edx = 0) (fun s₀ s hp h => ?_) hA t₁) ?_
  · simp only [List.append_assoc]
    refine ptrTo_ok hp h ha fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine ptrTo_ok hp c₁ hb fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ => VG.Proof.MlKem.X86.Top.wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    have c₄ := (c₂.only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)
    exact ⟨c₄, o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  refine Piece.seq (B := fun s₀ u => ∃ s, A s₀ s ∧ VG.Proof.MlDsa.X86.Verify.CL (Y := Y) s₀ a b s.mem a.len u)
    (Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, hs, c₁, m₁, e₁, e₂, e₃, e₄⟩ => ?_)
      (fun s₀ s₀' s s' hp hp' hq ⟨_, _, _, _, e₁, e₂, e₃, _⟩ ⟨_, _, _, _, e₁', e₂', e₃', _⟩ r hr => ?_) t₂) ?_
  · by_cases h0 : a.len = 0
    · exact absurd (Lay.ok_iff.mp ha).2.1 (by omega)
    refine (wp_count (N := a.len) (by omega) (VG.Proof.MlDsa.X86.Verify.CL (Y := Y) s₀ a b s.mem) ⟨c₁, m₁, by rw [e₁]; simp,
      by rw [e₂]; simp, by rw [e₃]; simp, by rw [e₄]; rfl⟩ fun k hk u h =>
        VG.Proof.MlDsa.X86.Verify.cmp_step hp ha hb hl hn hk h).mono fun u h => ⟨s, hs, h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁, e₁', hq.ptr ha]
    · rw [e₂, e₂', hq.ptr hb]
    · rw [e₃, e₃']
  refine Piece.taint [.esi] (fun s₀ u hp ⟨s, hs, h⟩ => ?_) (fun s₀ s₀' u u' hp _ hq ⟨s, hs, h⟩ ⟨s', hs', h'⟩ r hr => ?_)
    t₃
  · refine Decaps.wp_subi fun u₁ o₁ v₁ f₁ => Decaps.wp_sbbself f₁ fun u₂ o₂ v₂ => ?_
    have c₂ := (h.ctx.only o₁ (by decide) (by decide)).only o₂ (by decide) (by decide)
    refine VG.Proof.MlDsa.X86.Verify.accAnd_wp hp hc c₂ fun s' c' m' => hQ s₀ s s' hp hs c' ?_
    have mu : u₂.mem = s.mem := by rw [o₂.mem, o₁.mem, h.mem]
    rw [m', mu, v₂, CheckEk.sbb_mask, h.edx, Decaps.mask]
    congr 2
    have hl₁ : (bytesAt s.mem (Buf.addr s₀ a) a.len).length = a.len := bytesAt_length _ _ _
    have hl₂ : (bytesAt s.mem (Buf.addr s₀ b) a.len).length = a.len := bytesAt_length _ _ _
    have lt := (Decaps.accB (bytesAt s.mem (Buf.addr s₀ a) a.len) (bytesAt s.mem (Buf.addr s₀ b) a.len) a.len).isLt
    by_cases e : bytesAt s.mem (Buf.addr s₀ a) a.len = bytesAt s.mem (Buf.addr s₀ b) a.len
    · have z := (VG.Proof.MlDsa.X86.Verify.accB_zero hl₁ hl₂).mp e
      rw [ite_eq_left e, z]; rfl
    · have z : Decaps.accB (bytesAt s.mem (Buf.addr s₀ a) a.len) (bytesAt s.mem (Buf.addr s₀ b) a.len) a.len ≠ 0 :=
        fun z => e ((VG.Proof.MlDsa.X86.Verify.accB_zero hl₁ hl₂).mpr z)
      rw [ite_eq_right e]
      have : ¬ ((Decaps.accB (bytesAt s.mem (Buf.addr s₀ a) a.len) (bytesAt s.mem (Buf.addr s₀ b) a.len)
          a.len).setWidth 32).toNat < (1 : BitVec 32).toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        intro h'
        exact z (BitVec.eq_of_toNat_eq (by simp at h'; simp [h']))
      simp only [this, decide_false]
      rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.ctx.esi, h'.ctx.esi, hq.sc hp]

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Hint`. -/
section

/-!
# ML-DSA verification on x86 (32-bit): the hint and `z`

The pieces of the signature and of the public key are the bytes of their
arguments (`sig_slice`, `pk_slice`), which no piece writes. `HintBitUnpack`
gives the result: 1 with the hint stored (`HOk`), or 0 if it is malformed
(`hint_piece`); then each `z[i]` is unpacked and the result ANDed with
`‖z[i]‖∞ < γ₁ - β` (`zOne_piece`, `ZI`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly PolyIs Reduced polyAt toRq normRq HintIs)
open VG.Proof.MlDsa.Verify (vZ vHint)
open VG.Spec.Sha3 (bytesAt)

theorem lenZ_eq (p : Params) : lenZ p = Proof.MlDsa.Verify.lenZ p := rfl
theorem accB_YV (p : Params) : VG.Proof.MlDsa.X86.Verify.accB (VG.Proof.MlDsa.X86.Verify.YV p) = sb oACC 4 := rfl

/-! ## The inputs -/

section
variable {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p) {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s)
include hF hp h

theorem sig_slice {o l : Nat} (hok : (VG.Proof.MlDsa.X86.Verify.YV p).ok ⟨2, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨2, o, l⟩) l = ((VG.Proof.MlDsa.X86.Verify.vSig p s₀).drop o).take l := by
  obtain ⟨-, -, hl⟩ := Lay.ok_iff.mp hok
  have e := bytes_sub hp s₀.mem (a := 2) (o := 0) (k := o) (c := l) (L := p.sigLen) hl (by lv hF)
    (by rw [Nat.zero_add]; exact hok)
  rw [Nat.zero_add] at e
  exact (h.roBytes hp hok rfl).trans e

theorem pk_slice {o l : Nat} (hok : (VG.Proof.MlDsa.X86.Verify.YV p).ok ⟨0, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨0, o, l⟩) l = ((VG.Proof.MlDsa.X86.Verify.vPk p s₀).drop o).take l := by
  obtain ⟨-, -, hl⟩ := Lay.ok_iff.mp hok
  have e := bytes_sub hp s₀.mem (a := 0) (o := 0) (k := o) (c := l) (L := p.pkLen) hl (by lv hF)
    (by rw [Nat.zero_add]; exact hok)
  rw [Nat.zero_add] at e
  exact (h.roBytes hp hok rfl).trans e

end

/-! ## The hint -/

section
variable (p : Params) (s₀ : State)

/-- The hint of the signature, or `⊥`. -/
abbrev hOf : Option (List (Vector Bool Spec.MlDsa.n)) := vHint p (VG.Proof.MlDsa.X86.Verify.vSig p s₀)

/-- The hint, well formed and stored. -/
def HOk (s : State) : Prop := ∃ h, VG.Proof.MlDsa.X86.Verify.hOf p s₀ = some h ∧ HintIs s.mem (Buf.addr s₀ (hB p.k)) p.k h

/-- After `HintBitUnpack`: the result 1 and the hint stored, or 0 if it is malformed. -/
def H1 (s : State) : Prop :=
  VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s ∧ ((VG.Proof.MlDsa.X86.Verify.accV s₀ s = 1 ∧ VG.Proof.MlDsa.X86.Verify.HOk p s₀ s) ∨ (VG.Proof.MlDsa.X86.Verify.accV s₀ s = 0 ∧ VG.Proof.MlDsa.X86.Verify.hOf p s₀ = none))

/-- The postcondition, at the end. -/
def VFin (s : State) : Prop :=
  VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s ∧ ((VG.Proof.MlDsa.X86.Verify.accV s₀ s = 1 ∧ ∃ b, Spec.MlDsa.verifyMu p b (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vMu s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) = some true) ∨
    (VG.Proof.MlDsa.X86.Verify.accV s₀ s = 0 ∧ Spec.MlDsa.verifyMu p Spec.MlDsa.minBounds (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vMu s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) ≠ some true))

end

theorem keepHint {p : Params} {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96)
    (hs : (VG.Proof.MlDsa.X86.Verify.YV p).apart (hB p.k) bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m')
    {h : List (Vector Bool Spec.MlDsa.n)} (hh : HintIs m (Buf.addr s₀ (hB p.k)) p.k h) :
    HintIs m' (Buf.addr s₀ (hB p.k)) p.k h :=
  Proof.MlDsa.Verify.hintIs_congr (fun i hi => Top.keep hp (VG.Proof.MlDsa.X86.Verify.stkV hN) hs fr i (by show i < 256 * p.k * 4; omega)) hh

theorem HOk.keep {p : Params} {s₀ s s' : State} (h : VG.Proof.MlDsa.X86.Verify.HOk p s₀ s) (hp : TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (hs : (VG.Proof.MlDsa.X86.Verify.YV p).apart (hB p.k) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) :
    VG.Proof.MlDsa.X86.Verify.HOk p s₀ s' := by
  obtain ⟨hh, e, hi⟩ := h
  exact ⟨hh, e, VG.Proof.MlDsa.X86.Verify.keepHint hp hN hs fr hi⟩

theorem acc_keepV {p : Params} {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (hs : (VG.Proof.MlDsa.X86.Verify.YV p).apart (sb oACC 4) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) :
    VG.Proof.MlDsa.X86.Verify.accV s₀ s' = VG.Proof.MlDsa.X86.Verify.accV s₀ s :=
  keepW hp (VG.Proof.MlDsa.X86.Verify.stkV hN) hs fr

theorem acc_write {p : Params} {s₀ : State} (m : Mem) (v : BitVec 32) :
    (m.writeW (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.accB (VG.Proof.MlDsa.X86.Verify.YV p))) v).readW (Buf.addr s₀ (sb oACC 4)) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p)
include hP hF

theorem hint_piece : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p)) (VG.Proof.MlDsa.X86.Verify.H1 p) (hint P p) := by
  unfold hint
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s ∧ ((s.gpr .eax = 1 ∧ VG.Proof.MlDsa.X86.Verify.HOk p s₀ s) ∨
      (s.gpr .eax = 0 ∧ VG.Proof.MlDsa.X86.Verify.hOf p s₀ = none)))
    (VG.Proof.MlDsa.X86.Verify.hu_piece hP.hintUnpack 2 (oHint p) p.ω p.k vS (VG.Impl.MlDsa.X86.Verify.oP 0) hF.hint (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
      (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h)
      (fun s₀ s₀' s s' hp hp' hq h h' => by
        rw [VG.Proof.MlDsa.X86.Verify.sig_slice hF hp h (by lv hF), VG.Proof.MlDsa.X86.Verify.sig_slice hF hp' h' (by lv hF), (VG.Proof.MlDsa.X86.Verify.inputs_pub hq).2.2])
      fun s₀ s s' hp h h' fr post => ⟨h', ?_⟩) ?_
  · rw [VG.Proof.MlDsa.X86.Verify.sig_slice hF hp h (by lv hF)] at post
    change (match vHint p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) with
      | some hint => s'.gpr .eax = 1 ∧ HintIs s'.mem (Buf.addr s₀ (hB p.k)) p.k hint
      | none => s'.gpr .eax = 0) at post
    cases e : vHint p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) with
    | none => rw [e] at post; exact .inr ⟨post, e⟩
    | some hh => rw [e] at post; exact .inl ⟨post.1, hh, e, post.2⟩
  refine VG.Proof.MlDsa.X86.Verify.stAcc_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) (by lv hF) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
    fun s₀ s s' hp h h' g m' => ⟨h', ?_⟩
  have ea : VG.Proof.MlDsa.X86.Verify.accV s₀ s' = s.gpr .eax := by rw [VG.Proof.MlDsa.X86.Verify.accV, m', VG.Proof.MlDsa.X86.Verify.acc_write]
  have fr : Frame (FR s₀ [sb oACC 4] 0) s.mem s'.mem := by rw [m']; exact frW32 (Y := VG.Proof.MlDsa.X86.Verify.YV p)
  rcases h.2 with ⟨e, ho⟩ | ⟨e, hn⟩
  · exact .inl ⟨by rw [ea, e], ho.keep hp (N := 0) (by omega) (by lv hF) fr⟩
  · exact .inr ⟨by rw [ea, e], hn⟩

end

/-! ## `z` -/

section
variable (p : Params) (s₀ : State)

/-- The first `i` norms of `z` are within the bound. -/
abbrev NormsOk (i : Nat) : Prop := ∀ j < i, normRq [toRq (vZ p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) j)] < p.γ₁ - p.β

/-- After the first `i` entries of `z`. -/
structure ZI (i : Nat) (s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s
  hint : VG.Proof.MlDsa.X86.Verify.HOk p s₀ s
  z : ∀ j < i, PolyIs s.mem (Buf.addr s₀ (pZ j)) (toRq (vZ p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) j))
  acc : VG.Proof.MlDsa.X86.Verify.accV s₀ s = if VG.Proof.MlDsa.X86.Verify.NormsOk p s₀ i then 1 else 0

end

theorem ZI.keep {p : Params} {i : Nat} {s₀ s s' : State} (h : VG.Proof.MlDsa.X86.Verify.ZI p s₀ i s) (hp : TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀) {bs : List Buf}
    {N : Nat} (hN : N + 16 ≤ 96) (sh : (VG.Proof.MlDsa.X86.Verify.YV p).apart (hB p.k) bs = true) (sa : (VG.Proof.MlDsa.X86.Verify.YV p).apart (sb oACC 4) bs = true)
    (sz : ∀ j < i, (VG.Proof.MlDsa.X86.Verify.YV p).apart (pZ j) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s') : VG.Proof.MlDsa.X86.Verify.ZI p s₀ i s' :=
  ⟨h', h.hint.keep hp hN sh fr, fun j hj => keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV hN) (sz j hj) fr (h.z j hj),
    by rw [VG.Proof.MlDsa.X86.Verify.acc_keepV hp hN sa fr]; exact h.acc⟩

theorem ite_and_ite {P Q : Prop} [Decidable P] [Decidable Q] :
    ((if P then 1 else 0 : BitVec 32) &&& (if Q then 1 else 0)) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem normsOk_succ {p : Params} {s₀ : State} {i : Nat} :
    (VG.Proof.MlDsa.X86.Verify.NormsOk p s₀ i ∧ normRq [toRq (vZ p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) i)] < p.γ₁ - p.β) ↔ VG.Proof.MlDsa.X86.Verify.NormsOk p s₀ (i + 1) := by
  constructor
  · rintro ⟨h₁, h₂⟩ j hj
    rcases (by omega : j < i ∨ j = i) with hj | rfl
    exacts [h₁ j hj, h₂]
  · intro h
    exact ⟨fun j hj => h j (by omega), h i (by omega)⟩

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p)
include hP hF

theorem zOne_piece {i : Nat} (hi : i < p.ℓ) : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.ZI p · i) (VG.Proof.MlDsa.X86.Verify.ZI p · (i + 1)) (zOne P p i) := by
  have hzr := VG.Proof.MlDsa.X86.Verify.mul_row (a := lenZ p) hi
  unfold zOne
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Verify.ZI p s₀ i s ∧ PolyIs s.mem (Buf.addr s₀ (pZ i)) (toRq (vZ p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) i)))
    (VG.Proof.MlDsa.X86.Verify.bu_piece hP.bitUnpack 2 (p.ctildeLen + lenZ p * i) (lenZ p) (p.γ₁ - 1) p.γ₁ vS (VG.Impl.MlDsa.X86.Verify.oP (8 + i)) hF.bp.1 hF.bp.2
      (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.ctx)
      fun s₀ s s' hp h h' fr post => ⟨h.keep hp (N := 80) (by omega) (by lv hF) (by lv hF)
        (fun j hj => by lv hF) fr h', ?_⟩) ?_
  · rw [VG.Proof.MlDsa.X86.Verify.sig_slice hF hp h.ctx (by lv hF)] at post
    exact post
  refine Piece.seq (B := fun s₀ s => (VG.Proof.MlDsa.X86.Verify.ZI p s₀ i s ∧ PolyIs s.mem (Buf.addr s₀ (pZ i)) (toRq (vZ p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) i))) ∧
      s.gpr .eax = if normRq [toRq (vZ p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) i)] < p.γ₁ - p.β then 1 else 0)
    (VG.Proof.MlDsa.X86.Verify.normLt_piece hP.normLt vS (VG.Impl.MlDsa.X86.Verify.oP (8 + i)) (p.γ₁ - p.β) hF.beta.2 (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
      (ht := .block []) (by kernel_rfl) (fun _ _ _ h => ⟨h.1.ctx, h.2.1⟩)
      fun s₀ s s' hp h h' fr e => ⟨⟨h.1.keep hp (N := 80) (by omega) (by lv hF) (by lv hF)
        (fun j hj => by lv hF) fr h', keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr h.2⟩, ?_⟩) ?_
  · rw [e, h.2.2]
  refine VG.Proof.MlDsa.X86.Verify.accAnd_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) (by lv hF) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1.1.ctx)
    fun s₀ s s' hp h h' m' => ?_
  have fr : Frame (FR s₀ [sb oACC 4] 0) s.mem s'.mem := by rw [m']; exact frW32 (Y := VG.Proof.MlDsa.X86.Verify.YV p)
  obtain ⟨⟨hz, hzi⟩, he⟩ := h
  refine ⟨h', hz.hint.keep hp (N := 0) (by omega) (by lv hF) fr, fun j hj => ?_, ?_⟩
  · rcases (by omega : j < i ∨ j = i) with hj | rfl
    · have : (VG.Proof.MlDsa.X86.Verify.YV p).apart (pZ j) [sb oACC 4] = true := by lv hF
      exact keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) this fr (hz.z j hj)
    · have : (VG.Proof.MlDsa.X86.Verify.YV p).apart (pZ j) [sb oACC 4] = true := by lv hF
      exact keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) this fr hzi
  · rw [VG.Proof.MlDsa.X86.Verify.accV, m', VG.Proof.MlDsa.X86.Verify.acc_write, VG.Proof.MlDsa.X86.Verify.accB_YV, ← VG.Proof.MlDsa.X86.Verify.accV, hz.acc, he, VG.Proof.MlDsa.X86.Verify.ite_and_ite]
    exact ite_congr (propext VG.Proof.MlDsa.X86.Verify.normsOk_succ) (fun _ => rfl) (fun _ => rfl)

end

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Samp`. -/
section

/-!
# ML-DSA verification on x86 (32-bit): the samplers

Once the hint is well formed and the norms of `z` within the bound (`VB`), `ρ`
is copied to the seed, and each entry `e = 8r + s` of `Â` sampled from `ρ ‖ s
‖ r` (`aOne_piece`), the sampler's result ANDed into the result and the
polynomial masked with it, as in key generation; then `c` from `c̃`
(`samples_piece`). The result is 1 if the samplers' outputs are those of the
standard for some bounds, and 0 if verification is not true within the least
bounds (`GA`, `GC`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly sampleInBall PolyIs Reduced polyAt toRq)
open VG.Proof.MlDsa.Verify (vZ vHint vRho vCt aSeed)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params) (s₀ : State)

/-- After `z`: the hint and `z` stored, and the norms of `z` within the bound. -/
structure VB (s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s
  hint : VG.Proof.MlDsa.X86.Verify.HOk p s₀ s
  z : ∀ j < p.ℓ, PolyIs s.mem (Buf.addr s₀ (pZ j)) (toRq (vZ p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) j))
  norms : VG.Proof.MlDsa.X86.Verify.NormsOk p s₀ p.ℓ

/-- Verification is not true within the least bounds. -/
abbrev VFail : Prop := Spec.MlDsa.verifyMu p minBounds (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vMu s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) ≠ some true

/-- The entries `(r, s)` of `Â` before `e = 8r + s`. -/
abbrev Before (e r s : Nat) : Prop := s < p.ℓ ∧ 8 * r + s < e

/-- The result after the entries of `Â` before `e`, those of `A`. -/
def GA (e : Nat) (A : Nat → Nat → VG.Spec.MlDsa.Poly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, ∀ r s, VG.Proof.MlDsa.X86.Verify.Before p e r s → rejNTTPoly b.rejNTT (aSeed (VG.Proof.MlDsa.X86.Verify.vPk p s₀) r s) = some (A r s)) ∨
    (v = 0 ∧ VG.Proof.MlDsa.X86.Verify.VFail p s₀)

/-- After the entries of `Â` before `e`. -/
structure SA (e : Nat) (s : State) : Prop where
  vb : VG.Proof.MlDsa.X86.Verify.VB p s₀ s
  rho : bytesAt s.mem (Buf.addr s₀ (sb oSB 32)) 32 = vRho (VG.Proof.MlDsa.X86.Verify.vPk p s₀)
  ex : ∃ A : Nat → Nat → VG.Spec.MlDsa.Poly, (∀ r s', VG.Proof.MlDsa.X86.Verify.Before p e r s' → PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.Verify.pA r s')) (A r s')) ∧
    VG.Proof.MlDsa.X86.Verify.GA p s₀ e A (VG.Proof.MlDsa.X86.Verify.accV s₀ s)

/-- The result after `Â` and `c`, those of `A` and `C`. -/
def GC (A : Nat → Nat → VG.Spec.MlDsa.Poly) (C : VG.Spec.MlDsa.Poly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ (b : Bounds) (c : IPoly), (∀ r < p.k, ∀ s < p.ℓ,
      rejNTTPoly b.rejNTT (aSeed (VG.Proof.MlDsa.X86.Verify.vPk p s₀) r s) = some (A r s)) ∧
      VG.Spec.MlDsa.sampleInBall p.τ b.ball (vCt p (VG.Proof.MlDsa.X86.Verify.vSig p s₀)) = some c ∧ toRq c = C) ∨
    (v = 0 ∧ VG.Proof.MlDsa.X86.Verify.VFail p s₀)

/-- After `Â` and `c`. -/
structure SC (s : State) : Prop where
  vb : VG.Proof.MlDsa.X86.Verify.VB p s₀ s
  ex : ∃ (A : Nat → Nat → VG.Spec.MlDsa.Poly) (C : VG.Spec.MlDsa.Poly), (∀ r < p.k, ∀ s' < p.ℓ, PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.Verify.pA r s')) (A r s')) ∧
    PolyIs s.mem (Buf.addr s₀ pC) C ∧ VG.Proof.MlDsa.X86.Verify.GC p s₀ A C (VG.Proof.MlDsa.X86.Verify.accV s₀ s)

end

/-! ## Keeping the facts -/

theorem VB.keep {p : Params} {s₀ s s' : State} (h : VG.Proof.MlDsa.X86.Verify.VB p s₀ s) (hp : TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (sh : (VG.Proof.MlDsa.X86.Verify.YV p).apart (hB p.k) bs = true) (sz : ∀ j < p.ℓ, (VG.Proof.MlDsa.X86.Verify.YV p).apart (pZ j) bs = true)
    (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s') : VG.Proof.MlDsa.X86.Verify.VB p s₀ s' :=
  ⟨h', h.hint.keep hp hN sh fr, fun j hj => keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV hN) (sz j hj) fr (h.z j hj), h.norms⟩

theorem SA.keep {p : Params} {e : Nat} {s₀ s s' : State} (h : VG.Proof.MlDsa.X86.Verify.SA p s₀ e s) (hp : TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀) {bs : List Buf}
    {N : Nat} (hN : N + 16 ≤ 96) (sh : (VG.Proof.MlDsa.X86.Verify.YV p).apart (hB p.k) bs = true)
    (sz : ∀ j < p.ℓ, (VG.Proof.MlDsa.X86.Verify.YV p).apart (pZ j) bs = true) (sr : (VG.Proof.MlDsa.X86.Verify.YV p).apart (sb oSB 32) bs = true)
    (sa : (VG.Proof.MlDsa.X86.Verify.YV p).apart (sb oACC 4) bs = true) (sA : ∀ r s, VG.Proof.MlDsa.X86.Verify.Before p e r s → (VG.Proof.MlDsa.X86.Verify.YV p).apart (VG.Impl.MlDsa.X86.Verify.pA r s) bs = true)
    (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s') : VG.Proof.MlDsa.X86.Verify.SA p s₀ e s' := by
  obtain ⟨A, hA, hG⟩ := h.ex
  refine ⟨h.vb.keep hp hN sh sz fr h', by rw [keepBytes hp (VG.Proof.MlDsa.X86.Verify.stkV hN) sr fr]; exact h.rho,
    A, fun r s hb => keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV hN) (sA r s hb) fr (hA r s hb), ?_⟩
  rw [VG.Proof.MlDsa.X86.Verify.acc_keepV hp hN sa fr]; exact hG

theorem SA.congr {p : Params} {e e' : Nat} {s₀ s : State} (h : VG.Proof.MlDsa.X86.Verify.SA p s₀ e s)
    (he : ∀ r s, s < p.ℓ → (8 * r + s < e ↔ 8 * r + s < e')) : VG.Proof.MlDsa.X86.Verify.SA p s₀ e' s := by
  obtain ⟨A, hA, hG⟩ := h.ex
  refine ⟨h.vb, h.rho, A, fun r s hb => hA r s ⟨hb.1, (he r s hb.1).mpr hb.2⟩, ?_⟩
  rcases hG with ⟨h1, b, hb⟩ | h0
  · exact .inl ⟨h1, b, fun r s hb' => hb r s ⟨hb'.1, (he r s hb'.1).mpr hb'.2⟩⟩
  · exact .inr h0

/-! ## An entry of `Â` -/

theorem aSeed_eq (pk : List Byte) (r s : Nat) :
    aSeed pk r s = vRho pk ++ ([BitVec.ofNat 8 s] ++ [BitVec.ofNat 8 r]) := by
  simp only [aSeed, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]

theorem pA_eq (e : Nat) : VG.Impl.MlDsa.X86.Verify.pA (e / 8) (e % 8) = pB (20 + e) := by
  show pB (20 + 8 * (e / 8) + e % 8) = pB (20 + e)
  rw [show 20 + 8 * (e / 8) + e % 8 = 20 + e by omega]

section
variable (p : Params)

/-- After the first byte of the seed of entry `e`. -/
abbrev SA1 (e : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86.Verify.SA p s₀ e s ∧ bytesAt s.mem (Buf.addr s₀ (sb (oSB + 32) 1)) 1 = [BitVec.ofNat 8 (e % 8)]

/-- With the seed of entry `e`. -/
abbrev SA2 (e : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86.Verify.SA p s₀ e s ∧ bytesAt s.mem (Buf.addr s₀ (sb oSB 34)) 34 = aSeed (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (e / 8) (e % 8)

/-- After `RejNTTPoly` for entry `e`. -/
structure SA3 (e : Nat) (s₀ s : State) : Prop where
  vb : VG.Proof.MlDsa.X86.Verify.VB p s₀ s
  rho : bytesAt s.mem (Buf.addr s₀ (sb oSB 32)) 32 = vRho (VG.Proof.MlDsa.X86.Verify.vPk p s₀)
  ex : ∃ A : Nat → Nat → VG.Spec.MlDsa.Poly, (∀ r s', VG.Proof.MlDsa.X86.Verify.Before p e r s' → PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.Verify.pA r s')) (A r s')) ∧
    VG.Proof.MlDsa.X86.Verify.GA p s₀ e A (VG.Proof.MlDsa.X86.Verify.accV s₀ s)
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (pB (20 + e)))
  out : Spec.MlDsa.Outcome (fun b => rejNTTPoly b.rejNTT (aSeed (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (e / 8) (e % 8))) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (pB (20 + e))))

end

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p) {e : Nat} (he : e < 8 * p.k)
  (hel : e % 8 < p.ℓ)
include hF he

theorem sa_st1 : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.SA p · e) (VG.Proof.MlDsa.X86.Verify.SA1 p e) (.block (st8 (oSB + 32) (e % 8))) :=
  st8_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) (oSB + 32) (e % 8) (by lv hF) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => h.vb.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hp (N := 0) (by omega) (by lv hF) (fun j hj => by lv hF) (by lv hF) (by lv hF)
        (fun r s hb => by have := hb.1; have := hb.2; lv hF) (m' ▸ frW8 (Y := VG.Proof.MlDsa.X86.Verify.YV p)) h',
        by rw [m']; exact st8_bytes _ _ _ _ _⟩

theorem sa_st2 : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.SA1 p e) (VG.Proof.MlDsa.X86.Verify.SA2 p e) (.block (st8 (oSB + 33) (e / 8))) :=
  st8_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) (oSB + 33) (e / 8) (by lv hF) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => h.1.vb.ctx) fun s₀ s s' hp h h' m' => by
      have fr : Frame (FR s₀ [sb (oSB + 33) 1] 0) s.mem s'.mem := m' ▸ frW8 (Y := VG.Proof.MlDsa.X86.Verify.YV p)
      refine ⟨h.1.keep hp (N := 0) (by omega) (by lv hF) (fun j hj => by lv hF) (by lv hF) (by lv hF)
        (fun r s hb => by have := hb.1; have := hb.2; lv hF) fr h', ?_⟩
      have k32 := keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (b := sb oSB 32) (by lv hF) fr
      have k1 := keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (b := sb (oSB + 32) 1) (by lv hF) fr
      rw [show (34 : Nat) = 32 + (1 + 1) from rfl, bytes_cat hp _ (l₁ := 32) (by lv hF) (by lv hF),
        bytes_cat hp _ (l₁ := 1) (l₂ := 1) (by lv hF) (by lv hF), k32, k1, h.1.rho, h.2, VG.Proof.MlDsa.X86.Verify.aSeed_eq, m']
      exact congrArg (fun x => vRho (VG.Proof.MlDsa.X86.Verify.vPk p s₀) ++ ([BitVec.ofNat 8 (e % 8)] ++ x)) (st8_bytes _ _ _ _ _)

include hP in
theorem sa_rej : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.SA2 p e) (VG.Proof.MlDsa.X86.Verify.SA3 p e)
    (Impl.MlDsa.X86.KeyGen.callPR vS "vg_mldsa_rej_ntt_poly" P.rejNtt
      [.buf (sb oSB 34), .buf (pB (20 + e)), .buf (ssB 2048)]) :=
  rejNtt_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) hP.rejNtt vS oSB vS (VG.Impl.MlDsa.X86.Verify.oP (20 + e)) vS oSS (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1.vb.ctx)
    (fun s₀ s₀' s s' _ _ hq h h' => by rw [h.2, h'.2, (VG.Proof.MlDsa.X86.Verify.inputs_pub hq).1])
    fun s₀ s s' hp h h' fr red out => by
      obtain ⟨A, hA, hG⟩ := h.1.ex
      refine ⟨h.1.vb.keep hp (N := 80) (by omega) (by lv hF) (fun j hj => by lv hF) fr h',
        by rw [keepBytes hp (N := 80) (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr]; exact h.1.rho,
        ⟨A, fun r s hb => keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by have := hb.1; have := hb.2; lv hF) fr (hA r s hb), ?_⟩,
        red, by rw [← h.2]; exact out⟩
      rw [VG.Proof.MlDsa.X86.Verify.acc_keepV hp (N := 80) (by omega) (by lv hF) fr]; exact hG

include hel in
theorem sa_mask : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.SA3 p e) (VG.Proof.MlDsa.X86.Verify.SA p · (e + 1)) (maskA oACC (VG.Impl.MlDsa.X86.Verify.oP (20 + e))) := by
  have hl := hF.l
  refine maskA_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) oACC (VG.Impl.MlDsa.X86.Verify.oP (20 + e)) (by lv hF) (maskA_tt _) (fun _ _ _ h => h.vb.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_
  simp only [VG.Proof.MlDsa.X86.Verify.YV_sc] at fr ha hc
  obtain ⟨A, hA, hG⟩ := h.ex
  have r01 : s.gpr .eax = 0 ∨ s.gpr .eax = 1 := by
    rcases h.out with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨m1, m0⟩ := Proof.MlDsa.KeyGen.masked r01 hc
  have a01 : VG.Proof.MlDsa.X86.Verify.accV s₀ s = 0 ∨ VG.Proof.MlDsa.X86.Verify.accV s₀ s = 1 := by
    rcases hG with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨-, aiff⟩ := Proof.MlDsa.KeyGen.acc_and a01 r01
  have fr' : Frame (FR s₀ [sb oACC 4, pB (20 + e)] 0) s.mem s'.mem := fr2 fr
  have ea : VG.Proof.MlDsa.X86.Verify.accV s₀ s' = VG.Proof.MlDsa.X86.Verify.accV s₀ s &&& s.gpr .eax := ha
  have hr : e / 8 < p.k := by omega
  have hq : 8 * (e / 8) + e % 8 = e := Nat.div_add_mod e 8
  refine ⟨h.vb.keep hp (N := 0) (by omega) (by lv hF) (fun j hj => by lv hF) fr' h',
    by rw [keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr']; exact h.rho,
    fun r s => if r = e / 8 ∧ s = e % 8 then polyAt s'.mem (Buf.addr s₀ (pB (20 + e))) else A r s,
    fun r s hb => ?_, ?_⟩
  · dsimp only
    by_cases hrs : r = e / 8 ∧ s = e % 8
    · obtain ⟨rfl, rfl⟩ := hrs
      rw [VG.Proof.MlDsa.X86.KeyGen.ifp ⟨rfl, rfl⟩, VG.Proof.MlDsa.X86.Verify.pA_eq e]
      refine ⟨?_, rfl⟩
      rcases r01 with e0 | e1
      · exact (m0 e0).1
      · exact (m1 e1).2.2 (h.red e1)
    · rw [VG.Proof.MlDsa.X86.KeyGen.ifn hrs]
      have hb' : VG.Proof.MlDsa.X86.Verify.Before p e r s := ⟨hb.1, by
        have := hb.2
        rcases (by omega : 8 * r + s < e ∨ 8 * r + s = e) with h | h
        · exact h
        · exact absurd ⟨by omega, by omega⟩ hrs⟩
      exact keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by have := hb'.1; have := hb'.2; lv hF) fr' (hA r s hb')
  · rw [ea]
    rcases hG with ⟨h1, b, hb⟩ | ⟨h0, hn⟩
    · rcases h.out with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · refine .inl ⟨aiff.mpr ⟨h1, ho⟩, Proof.MlDsa.Verify.bmax b b', fun r s hb₁ => ?_⟩
        dsimp only
        by_cases hrs : r = e / 8 ∧ s = e % 8
        · obtain ⟨rfl, rfl⟩ := hrs
          rw [VG.Proof.MlDsa.X86.KeyGen.ifp ⟨rfl, rfl⟩, (m1 ho).2.1]
          exact Proof.MlDsa.Verify.rejNTTPoly_mono (Proof.MlDsa.Verify.bmax_right b b').rejNTT hb'
        · rw [VG.Proof.MlDsa.X86.KeyGen.ifn hrs]
          refine Proof.MlDsa.Verify.rejNTTPoly_mono (Proof.MlDsa.Verify.bmax_left b b').rejNTT (hb r s ⟨hb₁.1, ?_⟩)
          have := hb₁.2
          rcases (by omega : 8 * r + s < e ∨ 8 * r + s = e) with h | h
          · exact h
          · exact absurd ⟨by omega, by omega⟩ hrs
      · rw [ho, h1]
        obtain ⟨hh, ehh, -⟩ := h.vb.hint
        exact .inr ⟨by decide, by
          show Spec.MlDsa.verifyMu p minBounds (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vMu s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) ≠ some true
          rw [Proof.MlDsa.Verify.verifyMu_rej_none minBounds _ _ ehh hr hel hn]; exact fun h => nomatch h⟩
    · rw [h0]
      exact .inr ⟨BitVec.zero_and, hn⟩

include hP hel in
theorem aOne_piece : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.SA p · e) (VG.Proof.MlDsa.X86.Verify.SA p · (e + 1)) (aOne P e) := by
  unfold aOne
  exact (VG.Proof.MlDsa.X86.Verify.sa_st1 hF he).seq ((VG.Proof.MlDsa.X86.Verify.sa_st2 hF he).seq ((VG.Proof.MlDsa.X86.Verify.sa_rej hP hF he).seq (VG.Proof.MlDsa.X86.Verify.sa_mask hF he hel)))

end

/-! ## `Â` and `c` -/

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p)
include hP hF

theorem aRow_piece {r : Nat} (hr : r < p.k) : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.SA p · (8 * r)) (VG.Proof.MlDsa.X86.Verify.SA p · (8 * (r + 1))) (aRow P p r) := by
  have hl := hF.l
  unfold aRow
  refine (seqR_piece (I := fun e => (VG.Proof.MlDsa.X86.Verify.SA p · e)) p.ℓ (8 * r) fun e h₁ h₂ =>
    VG.Proof.MlDsa.X86.Verify.aOne_piece hP hF (by omega) (by omega)).mono (fun _ _ _ h => h) fun _ _ _ h => h.congr fun r' s hs => ?_
  omega

end

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Ball`. -/
section

/-!
# ML-DSA verification on x86 (32-bit): `Â` and `c`

`ρ` copied to the seed, the rows of `Â` (`aRow_piece`), then `c =
SampleInBall(c̃)` masked with its result (`samples_piece`): from the result 1
to `SC`.
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly sampleInBall PolyIs Reduced polyAt toRq)
open VG.Proof.MlDsa.Verify (vZ vHint vRho vCt aSeed)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- After `SampleInBall`. -/
structure SB (s₀ s : State) : Prop where
  vb : VG.Proof.MlDsa.X86.Verify.VB p s₀ s
  ex : ∃ A : Nat → Nat → VG.Spec.MlDsa.Poly, (∀ r s', VG.Proof.MlDsa.X86.Verify.Before p (8 * p.k) r s' → PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.Verify.pA r s')) (A r s')) ∧
    VG.Proof.MlDsa.X86.Verify.GA p s₀ (8 * p.k) A (VG.Proof.MlDsa.X86.Verify.accV s₀ s)
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ pC)
  out : Spec.MlDsa.Outcome (fun b => (VG.Spec.MlDsa.sampleInBall p.τ b.ball (vCt p (VG.Proof.MlDsa.X86.Verify.vSig p s₀))).map toRq) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ pC))

end

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p)
include hF

theorem rho_piece : VG.Proof.MlDsa.X86.Verify.VP p (fun s₀ s => VG.Proof.MlDsa.X86.Verify.VB p s₀ s ∧ VG.Proof.MlDsa.X86.Verify.accV s₀ s = 1) (VG.Proof.MlDsa.X86.Verify.SA p · 0) (copyW vS ⟨0, 0, 32⟩ (sb oSB 32) 8) :=
  copyW_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) 0 0 vS oSB 8 (by decide) (by decide) (by lv hF) (h₁ := .block []) (by kernel_rfl)
    (by taint_decide) (fun _ _ _ h => h.1.ctx) fun s₀ s s' hp h h' fr cp => by
      have fr' : Frame (FR s₀ [sb oSB 32] 0) s.mem s'.mem := fr1 fr
      refine ⟨h.1.keep hp (N := 0) (by omega) (by lv hF) (fun j hj => by lv hF) fr' h', ?_,
        fun _ _ => toRq Proof.MlDsa.KeyGen.zeroI, fun r s hb => absurd hb.2 (by omega),
        .inl ⟨by rw [VG.Proof.MlDsa.X86.Verify.acc_keepV hp (N := 0) (by omega) (by lv hF) fr']; exact h.2, minBounds,
          fun r s hb => absurd hb.2 (by omega)⟩⟩
      rw [show (32 : Nat) = 4 * 8 from rfl, cp, ← show (32 : Nat) = 4 * 8 from rfl,
        VG.Proof.MlDsa.X86.Verify.pk_slice hF hp h.1.ctx (by lv hF), List.drop_zero]
      rfl

include hP

theorem ball_call : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.SA p · (8 * p.k)) (VG.Proof.MlDsa.X86.Verify.SB p)
    (Impl.MlDsa.X86.KeyGen.callPR vS "vg_mldsa_sample_in_ball" P.ball
      [.buf ⟨2, 0, p.ctildeLen⟩, .imm p.ctildeLen, .imm p.τ, .buf pC, .buf (ssB 2048)]) :=
  VG.Proof.MlDsa.X86.Verify.ball_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) hP.ball 2 0 p.ctildeLen p.τ vS (VG.Impl.MlDsa.X86.Verify.oP 15) vS oSS hF.ball (by lv hF)
    (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.vb.ctx)
    (fun s₀ s₀' s s' hp hp' hq h h' => by
      rw [VG.Proof.MlDsa.X86.Verify.sig_slice hF hp h.vb.ctx (by lv hF), VG.Proof.MlDsa.X86.Verify.sig_slice hF hp' h'.vb.ctx (by lv hF), (VG.Proof.MlDsa.X86.Verify.inputs_pub hq).2.2])
    fun s₀ s s' hp h h' fr red out => by
      obtain ⟨A, hA, hG⟩ := h.ex
      refine ⟨h.vb.keep hp (N := 80) (by omega) (by lv hF) (fun j hj => by lv hF) fr h',
        ⟨A, fun r s hb => keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by have := hb.1; have := hb.2; lv hF) fr (hA r s hb), ?_⟩,
        red, ?_⟩
      · rw [VG.Proof.MlDsa.X86.Verify.acc_keepV hp (N := 80) (by omega) (by lv hF) fr]; exact hG
      · rw [VG.Proof.MlDsa.X86.Verify.sig_slice hF hp h.vb.ctx (by lv hF), List.drop_zero] at out
        exact out

omit hP in
theorem ball_mask : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.SB p) (VG.Proof.MlDsa.X86.Verify.SC p) (maskA oACC (VG.Impl.MlDsa.X86.Verify.oP 15)) := by
  have hl := hF.l
  refine maskA_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) oACC (VG.Impl.MlDsa.X86.Verify.oP 15) (by lv hF) (maskA_tt _) (fun _ _ _ h => h.vb.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_
  simp only [VG.Proof.MlDsa.X86.Verify.YV_sc] at fr ha hc
  obtain ⟨A, hA, hG⟩ := h.ex
  have r01 : s.gpr .eax = 0 ∨ s.gpr .eax = 1 := by
    rcases h.out with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨m1, m0⟩ := Proof.MlDsa.KeyGen.masked r01 hc
  have a01 : VG.Proof.MlDsa.X86.Verify.accV s₀ s = 0 ∨ VG.Proof.MlDsa.X86.Verify.accV s₀ s = 1 := by
    rcases hG with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨-, aiff⟩ := Proof.MlDsa.KeyGen.acc_and a01 r01
  have fr' : Frame (FR s₀ [sb oACC 4, pC] 0) s.mem s'.mem := fr2 fr
  have ea : VG.Proof.MlDsa.X86.Verify.accV s₀ s' = VG.Proof.MlDsa.X86.Verify.accV s₀ s &&& s.gpr .eax := ha
  have bf : ∀ r < p.k, ∀ s < p.ℓ, VG.Proof.MlDsa.X86.Verify.Before p (8 * p.k) r s := fun r hr s hs => ⟨hs, by omega⟩
  refine ⟨h.vb.keep hp (N := 0) (by omega) (by lv hF) (fun j hj => by lv hF) fr' h', A,
    polyAt s'.mem (Buf.addr s₀ pC), fun r hr s hs => keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr'
      (hA r s (bf r hr s hs)), ⟨?_, rfl⟩, ?_⟩
  · rcases r01 with e0 | e1
    · exact (m0 e0).1
    · exact (m1 e1).2.2 (h.red e1)
  · rw [ea]
    rcases hG with ⟨h1, b, hb⟩ | ⟨h0, hn⟩
    · rcases h.out with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · obtain ⟨c, hc, hcC⟩ := Option.map_eq_some_iff.mp hb'
        refine .inl ⟨aiff.mpr ⟨h1, ho⟩, Proof.MlDsa.Verify.bmax b b', c, fun r hr s hs =>
          Proof.MlDsa.Verify.rejNTTPoly_mono (Proof.MlDsa.Verify.bmax_left b b').rejNTT (hb r s (bf r hr s hs)),
          Proof.MlDsa.Verify.sampleInBall_mono (Proof.MlDsa.Verify.bmax_right b b').ball hc, ?_⟩
        rw [hcC, (m1 ho).2.1]
      · rw [ho, h1]
        obtain ⟨hh, ehh, -⟩ := h.vb.hint
        refine .inr ⟨by decide, ?_⟩
        show Spec.MlDsa.verifyMu p minBounds (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vMu s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) ≠ some true
        rw [Proof.MlDsa.Verify.verifyMu_ball_none minBounds _ _ ehh (Option.map_eq_none_iff.mp hn)]
        exact fun h => nomatch h
    · rw [h0]
      exact .inr ⟨BitVec.zero_and, hn⟩

theorem samples_piece : VG.Proof.MlDsa.X86.Verify.VP p (fun s₀ s => VG.Proof.MlDsa.X86.Verify.VB p s₀ s ∧ VG.Proof.MlDsa.X86.Verify.accV s₀ s = 1) (VG.Proof.MlDsa.X86.Verify.SC p) (samples P p) := by
  unfold samples
  refine (VG.Proof.MlDsa.X86.Verify.rho_piece hF).seq ?_
  refine Piece.seq (B := (VG.Proof.MlDsa.X86.Verify.SA p · (8 * p.k))) ((seqR_piece (I := fun r => (VG.Proof.MlDsa.X86.Verify.SA p · (8 * r))) p.k 0
    fun r _ hr => VG.Proof.MlDsa.X86.Verify.aRow_piece hP hF (by omega)).mono (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  exact (VG.Proof.MlDsa.X86.Verify.ball_call hP hF).seq (VG.Proof.MlDsa.X86.Verify.ball_mask hF)

end

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Compute`. -/
section

/-!
# ML-DSA verification on x86 (32-bit): what holds while computing `w′₁`

From the hint `h`, `Â` (`A`) and `c` (`C`) the samplers gave, `CX` says what
`scratch` holds while computing: `ẑ[i]` for `i < j` (and `z[i]` for the
others), `ĉ` once `cd`, and the packed rows `w₁[r]` for `r < nr`; and the
result (`GC`). It is kept by pieces that write only buffers apart from those
(`SafeC`, `CX.keep`). The NTTs of `z` and `c` (`nttZ_piece`, `nttC_piece`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly IPoly PolyIs Reduced polyAt toRq ntt HintIs simpleBitPack)
open VG.Proof.MlDsa.Verify (vZ vHint zHat w1Row)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params) (s₀ : State)

/-- The row `r` of `w₁` packed in `scratch`. -/
abbrev wB (r : Nat) : Buf := sb (oB + w1Len p * r) (w1Len p)

/-- While computing `w′₁`, with the hint `h`, `Â` and `c` of the samplers. -/
structure CX (h : List (Vector Bool Spec.MlDsa.n)) (A : Nat → Nat → VG.Spec.MlDsa.Poly) (C : VG.Spec.MlDsa.Poly) (j : Nat) (cd : Bool)
    (nr : Nat) (s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s
  norms : VG.Proof.MlDsa.X86.Verify.NormsOk p s₀ p.ℓ
  hh : VG.Proof.MlDsa.X86.Verify.hOf p s₀ = some h
  hint : HintIs s.mem (Buf.addr s₀ (hB p.k)) p.k h
  a : ∀ r < p.k, ∀ s' < p.ℓ, PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.Verify.pA r s')) (A r s')
  z : ∀ i < p.ℓ, PolyIs s.mem (Buf.addr s₀ (pZ i))
    (if i < j then zHat p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) i else toRq (vZ p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) i))
  c : PolyIs s.mem (Buf.addr s₀ pC) (if cd then VG.Spec.MlDsa.ntt C else C)
  gc : VG.Proof.MlDsa.X86.Verify.GC p s₀ A C (VG.Proof.MlDsa.X86.Verify.accV s₀ s)
  w : ∀ r < nr, bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlDsa.X86.Verify.wB p r)) (w1Len p) =
    VG.Spec.MlDsa.simpleBitPack (w1Row p (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A (VG.Spec.MlDsa.ntt C) h r) (w1Max p)

/-- While computing `w′₁`. -/
def CI (j : Nat) (cd : Bool) (nr : Nat) (s : State) : Prop :=
  ∃ h A C, VG.Proof.MlDsa.X86.Verify.CX p s₀ h A C j cd nr s

end

/-- The buffers of `CX` but `z` and `c` are apart from `bs`. -/
structure SafeC (p : Params) (nr : Nat) (bs : List Buf) : Prop where
  h : (VG.Proof.MlDsa.X86.Verify.YV p).apart (hB p.k) bs = true
  a : ∀ r < p.k, ∀ s < p.ℓ, (VG.Proof.MlDsa.X86.Verify.YV p).apart (VG.Impl.MlDsa.X86.Verify.pA r s) bs = true
  acc : (VG.Proof.MlDsa.X86.Verify.YV p).apart (sb oACC 4) bs = true
  w : ∀ r < nr, (VG.Proof.MlDsa.X86.Verify.YV p).apart (VG.Proof.MlDsa.X86.Verify.wB p r) bs = true

/-- `CX` after a piece that writes only `bs`, with `z` and `c` as they are after it. -/
theorem CX.update {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → VG.Spec.MlDsa.Poly} {C : VG.Spec.MlDsa.Poly} {j : Nat}
    {cd : Bool} {nr : Nat} {s₀ s s' : State} (hc : VG.Proof.MlDsa.X86.Verify.CX p s₀ h A C j cd nr s) (hp : TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀)
    {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96) (sf : VG.Proof.MlDsa.X86.Verify.SafeC p nr bs) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s') {j' : Nat} {cd' : Bool}
    (hz : ∀ i < p.ℓ, PolyIs s'.mem (Buf.addr s₀ (pZ i))
      (if i < j' then zHat p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) i else toRq (vZ p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) i)))
    (hcc : PolyIs s'.mem (Buf.addr s₀ pC) (if cd' then VG.Spec.MlDsa.ntt C else C)) : VG.Proof.MlDsa.X86.Verify.CX p s₀ h A C j' cd' nr s' :=
  ⟨h', hc.norms, hc.hh, VG.Proof.MlDsa.X86.Verify.keepHint hp hN sf.h fr hc.hint,
    fun r hr s hs => keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV hN) (sf.a r hr s hs) fr (hc.a r hr s hs), hz, hcc,
    by rw [VG.Proof.MlDsa.X86.Verify.acc_keepV hp hN sf.acc fr]; exact hc.gc,
    fun r hr => by rw [keepBytes hp (VG.Proof.MlDsa.X86.Verify.stkV hN) (sf.w r hr) fr]; exact hc.w r hr⟩

/-- `CX` after a piece that writes only `bs`, apart from `z` and `c`. -/
theorem CX.keep {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → VG.Spec.MlDsa.Poly} {C : VG.Spec.MlDsa.Poly} {j : Nat}
    {cd : Bool} {nr : Nat} {s₀ s s' : State} (hc : VG.Proof.MlDsa.X86.Verify.CX p s₀ h A C j cd nr s) (hp : TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀)
    {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96) (sf : VG.Proof.MlDsa.X86.Verify.SafeC p nr bs)
    (sz : ∀ i < p.ℓ, (VG.Proof.MlDsa.X86.Verify.YV p).apart (pZ i) bs = true) (sc : (VG.Proof.MlDsa.X86.Verify.YV p).apart pC bs = true)
    (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Verify.YV p) s₀ s') : VG.Proof.MlDsa.X86.Verify.CX p s₀ h A C j cd nr s' :=
  hc.update hp hN sf fr h' (fun i hi => keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV hN) (sz i hi) fr (hc.z i hi))
    (keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV hN) sc fr hc.c)

theorem w_row {p : Params} {r : Nat} (hr : r < p.k) : w1Len p * r + w1Len p ≤ p.k * w1Len p := by
  rw [Nat.mul_comm p.k]; exact VG.Proof.MlDsa.X86.Verify.mul_row hr

theorem w_rows {p : Params} {r nr : Nat} (hr : r < nr) (hnr : nr ≤ p.k) :
    w1Len p * r + w1Len p ≤ w1Len p * nr ∧ w1Len p * r + w1Len p ≤ p.k * w1Len p :=
  ⟨VG.Proof.MlDsa.X86.Verify.mul_row hr, VG.Proof.MlDsa.X86.Verify.w_row (Nat.lt_of_lt_of_le hr hnr)⟩

/-- Proves `SafeC` for buffers checked by `lv`, with `hnr : nr ≤ p.k`. -/
macro "safeC " hF:term:max hnr:term:max : tactic => `(tactic| exact
  ⟨by lv $hF, fun r hr s hs => by lv $hF, by lv $hF, fun r hr => by
    have := VG.Proof.MlDsa.X86.Verify.w_rows hr $hnr
    lv $hF⟩)

theorem apart_append {Y : VG.Proof.MlKem.X86.Top.Lay} {b : Buf} {bs₁ bs₂ : List Buf} (h₁ : Y.apart b bs₁ = true)
    (h₂ : Y.apart b bs₂ = true) : Y.apart b (bs₁ ++ bs₂) = true := by
  simp only [Lay.apart, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁.1, h₁.2, h₂.2⟩

/-- `SafeC` of two lists of buffers, for both. -/
theorem SafeC.append {p : Params} {nr : Nat} {bs₁ bs₂ : List Buf} (h₁ : VG.Proof.MlDsa.X86.Verify.SafeC p nr bs₁) (h₂ : VG.Proof.MlDsa.X86.Verify.SafeC p nr bs₂) :
    VG.Proof.MlDsa.X86.Verify.SafeC p nr (bs₁ ++ bs₂) :=
  ⟨VG.Proof.MlDsa.X86.Verify.apart_append h₁.h h₂.h, fun r hr s hs => VG.Proof.MlDsa.X86.Verify.apart_append (h₁.a r hr s hs) (h₂.a r hr s hs),
    VG.Proof.MlDsa.X86.Verify.apart_append h₁.acc h₂.acc, fun r hr => VG.Proof.MlDsa.X86.Verify.apart_append (h₁.w r hr) (h₂.w r hr)⟩

/-- `SafeC` of a buffer of `scratch` below `Â`, apart from the hint, the result and the rows of `w₁`
so far, proved once for any buffer (`safeC` on a literal list of buffers costs seconds). -/
theorem SafeC.sc {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p) {nr : Nat} (hnr : nr ≤ p.k) {o l : Nat} (h0 : 0 < l)
    (h1 : o + l ≤ oACC ∨ oACC + 4 ≤ o) (h2 : o + l ≤ oB ∨ oB + w1Len p * nr ≤ o) (h3 : o + l ≤ VG.Impl.MlDsa.X86.Verify.oP 0 ∨ VG.Impl.MlDsa.X86.Verify.oP 8 ≤ o)
    (h4 : o + l ≤ VG.Impl.MlDsa.X86.Verify.oP 20) : VG.Proof.MlDsa.X86.Verify.SafeC p nr [sb o l] := by
  simp only [oACC, oB, VG.Impl.MlDsa.X86.Verify.oP] at h1 h2 h3 h4
  safeC hF hnr

/-- `SafeC` of no buffers. -/
theorem SafeC.nil {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p) {nr : Nat} (hnr : nr ≤ p.k) : VG.Proof.MlDsa.X86.Verify.SafeC p nr [] := by
  safeC hF hnr

theorem SafeC.cons_sc {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p) {nr : Nat} (hnr : nr ≤ p.k) {o l : Nat} {bs : List Buf}
    (h0 : 0 < l) (h1 : o + l ≤ oACC ∨ oACC + 4 ≤ o) (h2 : o + l ≤ oB ∨ oB + w1Len p * nr ≤ o ∨ oB + 1024 ≤ o)
    (h3 : o + l ≤ VG.Impl.MlDsa.X86.Verify.oP 0 ∨ VG.Impl.MlDsa.X86.Verify.oP 8 ≤ o) (h4 : o + l ≤ VG.Impl.MlDsa.X86.Verify.oP 20) (h : VG.Proof.MlDsa.X86.Verify.SafeC p nr bs) : VG.Proof.MlDsa.X86.Verify.SafeC p nr (sb o l :: bs) := by
  have : w1Len p * nr ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) hnr; rw [Nat.mul_comm (w1Len p) p.k] at this; have := hF.w1; omega
  exact (SafeC.sc hF hnr h0 h1 (by omega) h3 h4).append (bs₁ := [_]) h

/-- Proves `SafeC` of a list of buffers of `scratch` below `Â` by `SafeC.cons_sc`, with `hnr : nr ≤ p.k`. -/
macro "safeCs " hF:term:max hnr:term:max : tactic => `(tactic| (
  repeat' (first
    | with_reducible exact VG.Proof.MlDsa.X86.Verify.SafeC.nil $hF $hnr
    | apply VG.Proof.MlDsa.X86.Verify.SafeC.cons_sc $hF $hnr)
  all_goals (
    have := ($hF).w1; have := ($hF).k; have := ($hF).l; have := ($hF).ct
    try simp only [VG.Impl.MlDsa.X86.Verify.oP, VG.Impl.MlDsa.X86.Verify.oB, VG.Impl.MlDsa.X86.Verify.oACC,
      VG.Impl.MlDsa.X86.Verify.oSS, VG.Impl.MlDsa.X86.Verify.oCT]
    omega_arith)))

theorem ci_of_sc {p : Params} {s₀ s : State} (h : VG.Proof.MlDsa.X86.Verify.SC p s₀ s) : VG.Proof.MlDsa.X86.Verify.CI p s₀ 0 false 0 s := by
  obtain ⟨hh, ehh, hi⟩ := h.vb.hint
  obtain ⟨A, C, hA, hC, hG⟩ := h.ex
  exact ⟨hh, A, C, h.vb.ctx, h.vb.norms, ehh, hi, hA, fun i hi => by
    rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.not_lt_zero _)]; exact h.vb.z i hi, hC, hG,
    fun r hr => absurd hr (Nat.not_lt_zero _)⟩

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p)
include hP hF

theorem nttZ_piece {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.CI p · j false 0) (VG.Proof.MlDsa.X86.Verify.CI p · (j + 1) false 0) (nttAt P (pZ j)) :=
  inPlace_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) hP.ntt vS (VG.Impl.MlDsa.X86.Verify.oP (8 + j)) vS oSS (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h⟩ => ⟨h.ctx, by have := (h.z j hj).1; exact this⟩)
    fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr post => by
      refine ⟨hh, A, C, h.update hp (N := 80) (by omega) (by safeCs hF (Nat.zero_le p.k)) fr h' (fun i hi => ?_)
        (keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr h.c)⟩
      rcases (by omega : i < j ∨ i = j ∨ j < i) with hij | rfl | hij
      · have e := keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr (h.z i hi)
        simp only [hij, show i < j + 1 by omega, ite_true] at e ⊢
        exact e
      · rw [ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self i) h]
        have e := (h.z i hi).2
        rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.lt_irrefl _)] at e
        rw [e] at post
        exact post
      · have e := keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr (h.z i hi)
        simp only [show ¬ i < j by omega, show ¬ i < j + 1 by omega, ite_false] at e ⊢
        exact e

theorem nttC_piece : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.CI p · p.ℓ false 0) (VG.Proof.MlDsa.X86.Verify.CI p · p.ℓ true 0) (nttAt P pC) :=
  inPlace_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) hP.ntt vS (VG.Impl.MlDsa.X86.Verify.oP 15) vS oSS (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h⟩ => ⟨h.ctx, h.c.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr post => by
      refine ⟨hh, A, C, h.update hp (N := 80) (by omega) (by safeCs hF (Nat.zero_le p.k)) fr h'
        (fun i hi => keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr (h.z i hi)) ?_⟩
      have e := h.c.2
      simp only [Bool.false_eq_true, ite_false] at e
      rw [e] at post
      simpa using post

end

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Row`. -/
section

/-!
# ML-DSA verification on x86 (32-bit): a row of `w′₁`

Row `r`, step by step, with what the temporaries hold (`RI`): `w′ = Σₛ Â[r, s]
ẑ[s]` (`dotAcc`), `t₁[r]` unpacked and its NTT, `ĉ t̂₁[r]`, `w′ = NTT⁻¹(… - ĉ
t̂₁[r])` (`wRow`), its `UseHint`s with `h[r]` (`w1Row`), and their
`SimpleBitPack` to row `r` of `w1Encode(w′₁)` (`row_piece`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Impl.MlDsa.X86.KeyGen (callP)
open VG.Spec.MlDsa (Params Poly IPoly PolyIs NatPolyIs Reduced polyAt toRq ntt nttInv HintIs simpleBitPack)
open VG.Proof.MlDsa.Verify (vZ vHint zHat dotAcc t1Hat wRow w1Row vT1)
open VG.Spec.Sha3 (bytesAt)

/-- In row `r`, with the facts `Q` about the temporaries. -/
def RI (p : Params) (r : Nat)
    (Q : List (Vector Bool Spec.MlDsa.n) → (Nat → Nat → VG.Spec.MlDsa.Poly) → VG.Spec.MlDsa.Poly → State → Mem → Prop) (s₀ s : State) : Prop :=
  ∃ h A C, VG.Proof.MlDsa.X86.Verify.CX p s₀ h A C p.ℓ true r s ∧ Q h A C s₀ s.mem

theorem CX.zh {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → VG.Spec.MlDsa.Poly} {C : VG.Spec.MlDsa.Poly} {cd : Bool}
    {nr : Nat} {s₀ s : State} (hc : VG.Proof.MlDsa.X86.Verify.CX p s₀ h A C p.ℓ cd nr s) {i : Nat} (hi : i < p.ℓ) :
    PolyIs s.mem (Buf.addr s₀ (pZ i)) (zHat p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) i) := by
  have e := hc.z i hi
  simp only [hi, ite_true] at e
  exact e

theorem CX.ch {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → VG.Spec.MlDsa.Poly} {C : VG.Spec.MlDsa.Poly} {j nr : Nat}
    {s₀ s : State} (hc : VG.Proof.MlDsa.X86.Verify.CX p s₀ h A C j true nr s) : PolyIs s.mem (Buf.addr s₀ pC) (VG.Spec.MlDsa.ntt C) := by
  have e := hc.c
  simp only [ite_true] at e
  exact e

theorem natPoly_le {m : Mem} {a : Addr} {f : Vector Nat Spec.MlDsa.n} (h : NatPolyIs m a f) {b : Nat}
    (hb : ∀ i (hi : i < Spec.MlDsa.n), f[i] ≤ b) : ∀ i < Spec.MlDsa.n, (Spec.MlDsa.coeffAt m a i).toNat ≤ b :=
  fun i hi => by
    have e := congrArg (·[i]'hi) h
    simp only [Spec.MlDsa.natPolyAt, Vector.getElem_ofFn] at e
    rw [e]; exact hb i hi

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p) {r : Nat} (hr : r < p.k)
include hP hF hr

theorem mulW_row : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.CI p · p.ℓ true r)
    (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r 1))
    (callP vS "vg_mldsa_multiply_ntt" P.mul [.buf pW, .buf (VG.Impl.MlDsa.X86.Verify.pA r 0), .buf (pZ 0)]) := by
  have hl := hF.l
  refine VG.Proof.MlDsa.X86.KeyGen.mul_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) _ _ _ _ _ _ hP.mul (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨_, _, _, h⟩ => ⟨h.ctx, (h.a r hr 0 (by omega)).1, (h.zh (by omega)).1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h', ?_⟩
  rw [(h.a r hr 0 (by omega)).2, (h.zh (by omega)).2] at out
  show PolyIs _ _ (Spec.MlDsa.add Spec.MlDsa.zero _)
  rw [Proof.MlDsa.Verify.add_zero_left]
  exact out

theorem mulAddW_row {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r j))
      (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r (j + 1)))
      (mulAddS P r j) := by
  have hl := hF.l
  refine mulAdd_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) _ _ _ _ _ _ hP.mulAdd (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, hw.1, (h.a r hr j hj).1, (h.zh hj).1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h', ?_⟩
  rw [hw.2, (h.a r hr j hj).2, (h.zh hj).2] at out
  exact out

theorem t1_row : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r p.ℓ))
    (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT) ((vT1 (VG.Proof.MlDsa.X86.Verify.vPk p s₀) r).map fun c => Spec.MlDsa.ofInt (c * 2 ^ Spec.MlDsa.d : Nat)))
    (callP vS "vg_mldsa_unpack_t1" P.unpackT1 [.buf ⟨0, 32 + 320 * r, 320⟩, .buf pT]) :=
  VG.Proof.MlDsa.X86.Verify.t1_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) hP.unpackT1 0 (32 + 320 * r) vS (VG.Impl.MlDsa.X86.Verify.oP 16) (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, _⟩ => h.ctx)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h',
      keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr hw, by rw [VG.Proof.MlDsa.X86.Verify.pk_slice hF hp h.ctx (by lv hF)] at out; exact out⟩

theorem nttT_row : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT) ((vT1 (VG.Proof.MlDsa.X86.Verify.vPk p s₀) r).map fun c => Spec.MlDsa.ofInt (c * 2 ^ Spec.MlDsa.d : Nat)))
    (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT) (t1Hat (VG.Proof.MlDsa.X86.Verify.vPk p s₀) r))
    (nttAt P pT) :=
  inPlace_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) hP.ntt vS (VG.Impl.MlDsa.X86.Verify.oP 16) vS oSS (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, _, ht⟩ => ⟨h.ctx, ht.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw, ht⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h',
      keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr hw, by rw [ht.2] at out; exact out⟩

theorem mulT_row : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT) (t1Hat (VG.Proof.MlDsa.X86.Verify.vPk p s₀) r))
    (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT2) (Spec.MlDsa.multiplyNTT (VG.Spec.MlDsa.ntt C) (t1Hat (VG.Proof.MlDsa.X86.Verify.vPk p s₀) r)))
    (callP vS "vg_mldsa_multiply_ntt" P.mul [.buf pT2, .buf pC, .buf pT]) :=
  VG.Proof.MlDsa.X86.KeyGen.mul_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) _ _ _ _ _ _ hP.mul (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, _, ht⟩ => ⟨h.ctx, h.ch.1, ht.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw, ht⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h',
      keepPolyD hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr hw, by rw [h.ch.2, ht.2] at out; exact out⟩

theorem sub_row : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT2) (Spec.MlDsa.multiplyNTT (VG.Spec.MlDsa.ntt C) (t1Hat (VG.Proof.MlDsa.X86.Verify.vPk p s₀) r)))
    (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (Spec.MlDsa.sub (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r p.ℓ)
      (Spec.MlDsa.multiplyNTT (VG.Spec.MlDsa.ntt C) (t1Hat (VG.Proof.MlDsa.X86.Verify.vPk p s₀) r))))
    (callP vS "vg_mldsa_sub" P.sub [.buf pW, .buf pT2]) :=
  acc_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) hP.sub _ _ _ _ (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, hw, ht⟩ => ⟨h.ctx, hw.1, ht.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw, ht⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h', by rw [hw.2, ht.2] at out; exact out⟩

theorem inv_rowV : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (Spec.MlDsa.sub
      (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r p.ℓ) (Spec.MlDsa.multiplyNTT (VG.Spec.MlDsa.ntt C) (t1Hat (VG.Proof.MlDsa.X86.Verify.vPk p s₀) r))))
    (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (wRow p (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A (VG.Spec.MlDsa.ntt C) r))
    (callP vS "vg_mldsa_inv_ntt" P.invNtt [.buf pW, .buf (ssB 1024)]) :=
  inPlace_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) hP.invNtt vS (VG.Impl.MlDsa.X86.Verify.oP 18) vS oSS (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, hw.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h', by rw [hw.2] at out; exact out⟩

omit hP in
theorem addr_pB {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Verify.YV p) s₀) :
    Buf.addr s₀ (pB r) = Buf.addr s₀ (hB p.k) + BitVec.ofNat 64 (1024 * r) := by
  rw [Buf.addr_eq hp (b := pB r) (by lv hF), Buf.addr_eq hp (b := hB p.k) (by lv hF), BitVec.add_assoc,
    ← BitVec.ofNat_add]
  simp only [VG.Impl.MlDsa.X86.Verify.oP]

theorem hint_row : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (wRow p (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A (VG.Spec.MlDsa.ntt C) r))
    (VG.Proof.MlDsa.X86.Verify.RI p r fun h A C s₀ m => NatPolyIs m (Buf.addr s₀ pW1) (w1Row p (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A (VG.Spec.MlDsa.ntt C) h r))
    (callP vS "vg_mldsa_use_hint" P.useHint [.buf (pB r), .buf pW, .imm p.γ₂, .buf pW1]) :=
  VG.Proof.MlDsa.X86.Verify.useHint_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) hP.useHint vS (VG.Impl.MlDsa.X86.Verify.oP r) vS (VG.Impl.MlDsa.X86.Verify.oP 18) p.γ₂ vS (VG.Impl.MlDsa.X86.Verify.oP 19) hF.g2 (by lv hF)
    (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm) (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, hw.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h', by
        have e := VG.Proof.MlDsa.X86.Verify.addr_pB hF hr hp
        simp only [pB, sb] at e
        rw [hw.2, e, Proof.MlDsa.Verify.hintAt_row h.hint hr] at out
        exact out⟩

theorem pack_row : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.RI p r fun h A C s₀ m =>
      NatPolyIs m (Buf.addr s₀ pW1) (w1Row p (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A (VG.Spec.MlDsa.ntt C) h r))
    (VG.Proof.MlDsa.X86.Verify.CI p · p.ℓ true (r + 1))
    (callP vS "vg_mldsa_simple_bit_pack" P.simpleBitPack
      [.buf pW1, .imm (w1Max p), .buf (sb (oB + w1Len p * r) (w1Len p)), .imm (w1Len p)]) := by
  have hwr := VG.Proof.MlDsa.X86.Verify.w_row hr
  refine sbp_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) hP.simpleBitPack vS (VG.Impl.MlDsa.X86.Verify.oP 19) (w1Max p) vS (oB + w1Len p * r) (w1Len p) hF.sbp.1
    hF.sbp.2 (by lv hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.Verify.YV_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, VG.Proof.MlDsa.X86.Verify.natPoly_le hw fun i hi => by
      simp only [w1Row, Vector.getElem_zipWith]
      exact Proof.MlDsa.Verify.useHint_le hF.g2 _ _⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, ?_⟩
  have hc := h.keep hp (N := 80) (by omega) (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h'
  refine ⟨hc.ctx, hc.norms, hc.hh, hc.hint, hc.a, hc.z, hc.c, hc.gc, fun r' hr' => ?_⟩
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · have := VG.Proof.MlDsa.X86.Verify.w_rows hr' (Nat.le_of_lt hr)
    rw [keepBytes hp (VG.Proof.MlDsa.X86.Verify.stkV (by omega)) (by lv hF) fr]; exact h.w r' hr'
  · rw [hw] at out; exact out

theorem row_piece : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.CI p · p.ℓ true r) (VG.Proof.MlDsa.X86.Verify.CI p · p.ℓ true (r + 1)) (row P p r) := by
  have hl := hF.l
  unfold row
  refine (VG.Proof.MlDsa.X86.Verify.mulW_row hP hF hr).seq ?_
  refine Piece.seq (B := VG.Proof.MlDsa.X86.Verify.RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r p.ℓ))
    ((seqR_piece (I := fun j => VG.Proof.MlDsa.X86.Verify.RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A r j))
      (p.ℓ - 1) 1 fun j _ hj => VG.Proof.MlDsa.X86.Verify.mulAddW_row hP hF hr (by omega)).mono (fun _ _ _ h => h)
      fun _ _ _ h => by rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h) ?_
  exact (VG.Proof.MlDsa.X86.Verify.t1_row hP hF hr).seq ((VG.Proof.MlDsa.X86.Verify.nttT_row hP hF hr).seq ((VG.Proof.MlDsa.X86.Verify.mulT_row hP hF hr).seq ((VG.Proof.MlDsa.X86.Verify.sub_row hP hF hr).seq
    ((VG.Proof.MlDsa.X86.Verify.inv_rowV hP hF hr).seq ((VG.Proof.MlDsa.X86.Verify.hint_row hP hF hr).seq (VG.Proof.MlDsa.X86.Verify.pack_row hP hF hr))))))

end

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Final`. -/
section

/-!
# ML-DSA verification on x86 (32-bit): `c̃′` and the result

`c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` (`hash_piece`), and the result ANDed with
`c̃′ = c̃` (`cmp_piece`): with the samplers' outputs those of the standard for
bounds `b`, the result is 1 exactly when `verifyMu` is true for `b`
(`verifyMu_rows`), and it stays 0 if verification is not true within the least
bounds, which is the contract's postcondition (`VFin`, `compute_piece`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly IPoly PolyIs polyAt toRq ntt HintIs simpleBitPack minBounds)
open VG.Proof.MlDsa.Verify (vZ vHint vCt w1Row)
open VG.Spec.Sha3 (bytesAt)

theorem flatMap_congr_mem' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      VG.Proof.MlDsa.X86.Verify.flatMap_congr_mem' fun y hy => h y (List.mem_cons_of_mem _ hy)]

section
variable (p : Params) (s₀ : State)

/-- `c̃′`, with the hint `h`, `Â` and `c` of the samplers. -/
abbrev ctOf (h : List (Vector Bool Spec.MlDsa.n)) (A : Nat → Nat → VG.Spec.MlDsa.Poly) (C : VG.Spec.MlDsa.Poly) : List Byte :=
  Spec.MlDsa.H (VG.Proof.MlDsa.X86.Verify.vMu s₀ ++ (List.range p.k).flatMap fun r =>
    VG.Spec.MlDsa.simpleBitPack (w1Row p (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) A (VG.Spec.MlDsa.ntt C) h r) (w1Max p)) p.ctildeLen

/-- After the hash. -/
def CH (s : State) : Prop :=
  ∃ h A C, VG.Proof.MlDsa.X86.Verify.CX p s₀ h A C p.ℓ true p.k s ∧ bytesAt s.mem (Buf.addr s₀ (sb oCT p.ctildeLen)) p.ctildeLen = VG.Proof.MlDsa.X86.Verify.ctOf p s₀ h A C

end

section
variable {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p)
include hF

theorem hash_piece : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.CI p · p.ℓ true p.k) (VG.Proof.MlDsa.X86.Verify.CH p)
    (hash2 vS 0 200 136 0x1f ⟨1, 0, 64⟩ (sb oB (p.k * w1Len p)) (sb oCT p.ctildeLen)) := by
  have hw := hF.w1; have hct := hF.ct
  refine hash2_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) 0 200 136 0x1f ⟨1, 0, 64⟩ (sb oB (p.k * w1Len p)) (sb oCT p.ctildeLen)
    Proof.MlKem.rate136 (by lv hF) (by rw [VG.Proof.MlDsa.X86.Verify.YV_stk]; omega) (by decide) (by show p.k * w1Len p < 2 ^ 32; omega)
    (by show p.ctildeLen < 2 ^ 32; omega) (by taint_decide) (h₁ := .block []) (by kernel_rfl)
    (h₂ := .block []) (by kernel_rfl) (h₃ := .block []) (by kernel_rfl) (h₄ := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h⟩ => h.ctx) fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr out => ⟨hh, A, C,
      h.keep hp (N := 40) (by omega) (by safeCs hF (Nat.le_refl p.k)) (fun i hi => by lv hF) (by lv hF) fr h', ?_⟩
  rw [out, sponge_H, Ctx.roBytes hp h.ctx (b := ⟨1, 0, 64⟩) (by lv hF) rfl]
  refine congrArg (fun x => Spec.MlDsa.H (VG.Proof.MlDsa.X86.Verify.vMu s₀ ++ x) p.ctildeLen) ?_
  have a0 := Buf.addr_eq hp (b := sb oB (p.k * w1Len p)) (by lv hF)
  show bytesAt s.mem (Buf.addr s₀ (sb oB (p.k * w1Len p))) (p.k * w1Len p) = _
  rw [a0, Nat.mul_comm, Proof.MlDsa.KeyGen.bytesAt_pieces]
  refine VG.Proof.MlDsa.X86.Verify.flatMap_congr_mem' fun r hr => ?_
  have hr := List.mem_range.mp hr
  have := VG.Proof.MlDsa.X86.Verify.w_rows hr (Nat.le_refl _)
  rw [← Buf.addr_eq hp (b := VG.Proof.MlDsa.X86.Verify.wB p r) (by lv hF)]
  exact h.w r hr

omit hF in
theorem mask_and {P : Prop} [Decidable P] {x : Bool} (hx : x = true ↔ P) :
    (1 : BitVec 32) &&& Proof.MlKem.X86.Decaps.mask P = if x then 1 else 0 := by
  by_cases hP : P
  · rw [show x = true from hx.mpr hP]; simp [Proof.MlKem.X86.Decaps.mask, hP]
  · rw [show x = false by cases x <;> simp_all]; simp [Proof.MlKem.X86.Decaps.mask, hP]

theorem cmp_piece' : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.CH p) (VG.Proof.MlDsa.X86.Verify.VFin p) (cmpAnd (sb oCT p.ctildeLen) ⟨2, 0, p.ctildeLen⟩ p.ctildeLen) := by
  have hct := hF.ct
  refine VG.Proof.MlDsa.X86.Verify.cmpAnd_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) (a := sb oCT p.ctildeLen) (b := ⟨2, 0, p.ctildeLen⟩) rfl (by lv hF) (by lv hF)
    (by lv hF) rfl (by show p.ctildeLen < 2 ^ 32; omega) (h₁ := .block []) (by kernel_rfl) (by taint_decide)
    (by taint_decide) (fun _ _ _ ⟨_, _, _, h, _⟩ => h.ctx) fun s₀ s s' hp ⟨hh, A, C, h, hct'⟩ h' m' => ⟨h', ?_⟩
  have ea : VG.Proof.MlDsa.X86.Verify.accV s₀ s' = VG.Proof.MlDsa.X86.Verify.accV s₀ s &&& Proof.MlKem.X86.Decaps.mask
      (VG.Proof.MlDsa.X86.Verify.ctOf p s₀ hh A C = vCt p (VG.Proof.MlDsa.X86.Verify.vSig p s₀)) := by
    rw [VG.Proof.MlDsa.X86.Verify.accV, m', VG.Proof.MlDsa.X86.Verify.acc_write]
    show _ &&& Proof.MlKem.X86.Decaps.mask (bytesAt s.mem (Buf.addr s₀ (sb oCT p.ctildeLen)) p.ctildeLen =
      bytesAt s.mem (Buf.addr s₀ ⟨2, 0, p.ctildeLen⟩) p.ctildeLen) = _
    rw [hct', VG.Proof.MlDsa.X86.Verify.sig_slice hF hp h.ctx (by lv hF), List.drop_zero]
    rfl
  rw [ea]
  rcases h.gc with ⟨h1, b, c, hA, hc, rfl⟩ | ⟨h0, hn⟩
  · have hv := Proof.MlDsa.Verify.verifyMu_rows p b (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vMu s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) h.hh h.hint.1 hA hc
    have hn : decide (Spec.MlDsa.normR ((List.range p.ℓ).map (vZ p (VG.Proof.MlDsa.X86.Verify.vSig p s₀))) < p.γ₁ - p.β) = true :=
      decide_eq_true ((Proof.MlDsa.Verify.normR_vZ_iff hF.beta.1 p hF.g1 _).mpr h.norms)
    rw [hn, Bool.true_and] at hv
    rw [h1]
    exact Proof.MlDsa.Verify.post_of_value (fun _ _ _ h₁ h₂ h => Proof.MlDsa.Verify.verifyMu_mono h₁ h₂ h) hv _
      (VG.Proof.MlDsa.X86.Verify.mask_and (by rw [beq_iff_eq]; exact eq_comm))
  · rw [h0]
    exact .inr ⟨BitVec.zero_and, hn⟩

end

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p)
include hP hF

theorem compute_piece : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.SC p) (VG.Proof.MlDsa.X86.Verify.VFin p) (compute P p) := by
  have hl := hF.l; have hk := hF.k
  unfold compute
  refine Piece.seq (B := (VG.Proof.MlDsa.X86.Verify.CI p · p.ℓ false 0)) ((seqR_piece (I := fun j => (VG.Proof.MlDsa.X86.Verify.CI p · j false 0)) p.ℓ 0
    fun j _ hj => VG.Proof.MlDsa.X86.Verify.nttZ_piece hP hF (by omega)).mono (fun _ _ _ h => VG.Proof.MlDsa.X86.Verify.ci_of_sc h)
      fun _ _ _ h => by simpa using h) ?_
  refine (VG.Proof.MlDsa.X86.Verify.nttC_piece hP hF).seq ?_
  refine Piece.seq (B := (VG.Proof.MlDsa.X86.Verify.CI p · p.ℓ true p.k)) ((seqR_piece (I := fun r => (VG.Proof.MlDsa.X86.Verify.CI p · p.ℓ true r)) p.k 0
    fun r _ hr => VG.Proof.MlDsa.X86.Verify.row_piece hP hF (by omega)).mono (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  exact (VG.Proof.MlDsa.X86.Verify.hash_piece hF).seq (VG.Proof.MlDsa.X86.Verify.cmp_piece' hF)

end

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Top`. -/
section

/-!
# ML-DSA verification on x86 (32-bit): the body

The body, piece by piece (`body_piece`), for any parameter set of Table 1 and
any verified implementations of the primitives: `HintBitUnpack`, a branch on
its result (which depends only on the signature), `z` and its norms, a branch
on them (which depend only on the signature), the samplers and the rest; it
returns the result, as the contract says (`VFin`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Impl.MlDsa.X86.KeyGen (seqR)
open VG.Spec.MlDsa (Params minBounds)
open VG.Spec.Sha3 (bytesAt)

/-- The body's end: the postcondition, and `eax` the result. -/
abbrev Done (p : Params) (s₀ s : State) : Prop := VG.Proof.MlDsa.X86.Verify.VFin p s₀ s ∧ s.gpr .eax = VG.Proof.MlDsa.X86.Verify.accV s₀ s

theorem hOf_pub {p : Params} {s₀ s₀' : State} (hq : TPub (VG.Proof.MlDsa.X86.Verify.YV p) (VG.Proof.MlDsa.X86.Verify.lkV p) s₀ s₀') : VG.Proof.MlDsa.X86.Verify.hOf p s₀ = VG.Proof.MlDsa.X86.Verify.hOf p s₀' := by
  simp only [VG.Proof.MlDsa.X86.Verify.hOf, (VG.Proof.MlDsa.X86.Verify.inputs_pub hq).2.2]

theorem norms_pub {p : Params} {s₀ s₀' : State} (hq : TPub (VG.Proof.MlDsa.X86.Verify.YV p) (VG.Proof.MlDsa.X86.Verify.lkV p) s₀ s₀') :
    decide (VG.Proof.MlDsa.X86.Verify.NormsOk p s₀ p.ℓ) = decide (VG.Proof.MlDsa.X86.Verify.NormsOk p s₀' p.ℓ) := by
  simp only [VG.Proof.MlDsa.X86.Verify.NormsOk, (VG.Proof.MlDsa.X86.Verify.inputs_pub hq).2.2]

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.Verify.VFacts p)
include hP hF

/-- Once the norms of `z` are within the bound. -/
theorem ok2_piece : VG.Proof.MlDsa.X86.Verify.VP p (fun s₀ s => VG.Proof.MlDsa.X86.Verify.ZI p s₀ p.ℓ s ∧ decide (VG.Proof.MlDsa.X86.Verify.NormsOk p s₀ p.ℓ) = true) (VG.Proof.MlDsa.X86.Verify.VFin p)
    (.seq (samples P p) (compute P p)) :=
  ((VG.Proof.MlDsa.X86.Verify.samples_piece hP hF).mono (fun _ _ _ ⟨h, hn⟩ => by
    have hn := of_decide_eq_true hn
    exact ⟨⟨h.ctx, h.hint, h.z, hn⟩, by rw [h.acc, VG.Proof.MlDsa.X86.KeyGen.ifp hn _ _]⟩) fun _ _ _ h => h).seq (VG.Proof.MlDsa.X86.Verify.compute_piece hP hF)

/-- Once the hint is well formed. -/
theorem ok1_piece : VG.Proof.MlDsa.X86.Verify.VP p (fun s₀ s => VG.Proof.MlDsa.X86.Verify.H1 p s₀ s ∧ (VG.Proof.MlDsa.X86.Verify.hOf p s₀).isSome = true) (VG.Proof.MlDsa.X86.Verify.VFin p)
    (.seq (seqR (zOne P p) 0 p.ℓ) (VG.Impl.MlDsa.X86.Verify.ifOk (.seq (samples P p) (compute P p)))) := by
  refine Piece.seq (B := (VG.Proof.MlDsa.X86.Verify.ZI p · p.ℓ)) ((seqR_piece (I := fun i => (VG.Proof.MlDsa.X86.Verify.ZI p · i)) p.ℓ 0
    fun i _ hi => VG.Proof.MlDsa.X86.Verify.zOne_piece hP hF (by omega)).mono (fun s₀ s _ ⟨h, hs⟩ => ?_) fun _ _ _ h => by simpa using h) ?_
  · rcases h.2 with ⟨e, ho⟩ | ⟨_, hn⟩
    · exact ⟨h.1, ho, fun j hj => absurd hj (Nat.not_lt_zero _), by
        rw [e, VG.Proof.MlDsa.X86.KeyGen.ifp (fun j hj => absurd hj (Nat.not_lt_zero _)) _ _]⟩
    · rw [hn] at hs; exact absurd hs (by decide)
  refine VG.Proof.MlDsa.X86.Verify.ifOk_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) (fun s₀ => decide (VG.Proof.MlDsa.X86.Verify.NormsOk p s₀ p.ℓ)) (by lv hF) (by taint_decide)
    (fun _ _ _ h => h.ctx) (fun s₀ s s' _ h h' m => ⟨h', ?_, ?_, ?_⟩) (fun s₀ s _ h => ?_)
    (fun _ _ _ _ hq => VG.Proof.MlDsa.X86.Verify.norms_pub hq) (VG.Proof.MlDsa.X86.Verify.ok2_piece hP hF) fun s₀ s _ h hn => ⟨h.ctx, .inr ⟨?_, ?_⟩⟩
  · obtain ⟨hh, e, hi⟩ := h.hint; exact ⟨hh, e, by rw [m]; exact hi⟩
  · intro j hj; rw [m]; exact h.z j hj
  · rw [VG.Proof.MlDsa.X86.Verify.accV, m]; exact h.acc
  · show (VG.Proof.MlDsa.X86.Verify.accV s₀ s != 0) = _
    rw [h.acc]
    by_cases hn : VG.Proof.MlDsa.X86.Verify.NormsOk p s₀ p.ℓ
    · rw [VG.Proof.MlDsa.X86.KeyGen.ifp hn _ _, decide_eq_true hn]; rfl
    · rw [VG.Proof.MlDsa.X86.KeyGen.ifn hn _ _, decide_eq_false hn]; rfl
  · rw [h.acc, VG.Proof.MlDsa.X86.KeyGen.ifn (of_decide_eq_false hn) _ _]
  · obtain ⟨hh, e, -⟩ := h.hint
    show Spec.MlDsa.verifyMu p minBounds (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vMu s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) ≠ some true
    exact Proof.MlDsa.Verify.verifyMu_norm minBounds _ _ e fun hlt =>
      of_decide_eq_false hn ((Proof.MlDsa.Verify.normR_vZ_iff hF.beta.1 p hF.g1 _).mp hlt)

omit hP in
theorem ret_piece : VG.Proof.MlDsa.X86.Verify.VP p (VG.Proof.MlDsa.X86.Verify.VFin p) (VG.Proof.MlDsa.X86.Verify.Done p) (.block [.mov .eax (.mem (at_ .esi oACC))]) :=
  ld32_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) oACC (by lv hF) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
    fun s₀ s s' _ h h' m e => ⟨⟨h', by rw [VG.Proof.MlDsa.X86.Verify.accV, m]; exact h.2⟩, by rw [e, VG.Proof.MlDsa.X86.Verify.accV, m]; rfl⟩

theorem body_piece : VG.Proof.MlDsa.X86.Verify.VP p (fun s₀ s => s = P0 s₀) (VG.Proof.MlDsa.X86.Verify.Done p) (body P p) := by
  unfold body
  refine (ldsc_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) (ht := .block []) (by kernel_rfl)).seq ((VG.Proof.MlDsa.X86.Verify.hint_piece hP hF).seq ?_)
  refine Piece.seq (VG.Proof.MlDsa.X86.Verify.ifOk_piece (Y := VG.Proof.MlDsa.X86.Verify.YV p) (fun s₀ => (VG.Proof.MlDsa.X86.Verify.hOf p s₀).isSome) (by lv hF) (by taint_decide)
    (fun _ _ _ h => h.1) (fun s₀ s s' _ h h' m => ⟨h', ?_⟩) (fun s₀ s _ h => ?_) (fun _ _ _ _ hq => by
      rw [VG.Proof.MlDsa.X86.Verify.hOf_pub hq]) (VG.Proof.MlDsa.X86.Verify.ok1_piece hP hF) fun s₀ s _ h hn => ⟨h.1, .inr ⟨?_, ?_⟩⟩) (VG.Proof.MlDsa.X86.Verify.ret_piece hF)
  · rcases h.2 with ⟨e, hh, eh, hi⟩ | ⟨e, hn⟩
    · exact .inl ⟨by rw [VG.Proof.MlDsa.X86.Verify.accV, m]; exact e, hh, eh, by rw [m]; exact hi⟩
    · exact .inr ⟨by rw [VG.Proof.MlDsa.X86.Verify.accV, m]; exact e, hn⟩
  · show (VG.Proof.MlDsa.X86.Verify.accV s₀ s != 0) = _
    rcases h.2 with ⟨e, _, eh, _⟩ | ⟨e, hn⟩
    · rw [e, eh]; rfl
    · rw [e, hn]; rfl
  · rcases h.2 with ⟨_, _, eh, _⟩ | ⟨e, _⟩
    · rw [eh] at hn; simp at hn
    · exact e
  · have e : VG.Proof.MlDsa.X86.Verify.hOf p s₀ = none := by
      cases e : VG.Proof.MlDsa.X86.Verify.hOf p s₀ with
      | none => rfl
      | some _ => rw [e] at hn; simp at hn
    show Spec.MlDsa.verifyMu p minBounds (VG.Proof.MlDsa.X86.Verify.vPk p s₀) (VG.Proof.MlDsa.X86.Verify.vMu s₀) (VG.Proof.MlDsa.X86.Verify.vSig p s₀) ≠ some true
    rw [Proof.MlDsa.Verify.verifyMu_hint_none minBounds _ _ e]
    exact fun h => nomatch h

end

/-! ## The stack -/

theorem NoSp.ite {cnd : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite cnd a b) := fun i hi => by
  simp only [VG.instrs, List.mem_append] at hi
  rcases hi with h | h
  exacts [ha i h, hb i h]

theorem NoSp.ifOk {c : Prog isa} (hc : NoSp c) : NoSp (VG.Impl.MlDsa.X86.Verify.ifOk c) :=
  NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.ite hc (NoSp.of_all (by kernel_rfl)))

theorem body_nosp {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) (p : Params) : NoSp (body P p) := by
  unfold body
  refine NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq ?_ (NoSp.seq (NoSp.ifOk (NoSp.seq (NoSp.seqR (fun i => ?_) _ _)
    (NoSp.ifOk (NoSp.seq ?_ ?_)))) (NoSp.of_all (by kernel_rfl))))
  · unfold hint
    exact NoSp.seq (NoSp.callPR hP.hintUnpack.nosp) (NoSp.of_all (by kernel_rfl))
  · unfold zOne
    exact NoSp.seq (NoSp.callP hP.bitUnpack.nosp) (NoSp.seq (NoSp.callPR hP.normLt.nosp) (NoSp.of_all (by kernel_rfl)))
  · unfold samples
    refine NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.seqR (fun r => NoSp.seqR (fun e => ?_) _ _) _ _)
      (NoSp.seq (NoSp.callPR hP.ball.nosp) (NoSp.of_all (by kernel_rfl))))
    unfold aOne
    exact NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.of_all (by kernel_rfl))
      (NoSp.seq (NoSp.callPR hP.rejNtt.nosp) (NoSp.of_all (by kernel_rfl))))
  · unfold compute
    refine NoSp.seq (NoSp.seqR (fun i => NoSp.callP hP.ntt.nosp) _ _) (NoSp.seq (NoSp.callP hP.ntt.nosp)
      (NoSp.seq (NoSp.seqR (fun r => ?_) _ _) (NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.of_all (by kernel_rfl)))))
    unfold row
    exact NoSp.seq (NoSp.callP hP.mul.nosp) (NoSp.seq (NoSp.seqR (fun j => NoSp.callP hP.mulAdd.nosp) _ _)
      (NoSp.seq (NoSp.callP hP.unpackT1.nosp) (NoSp.seq (NoSp.callP hP.ntt.nosp) (NoSp.seq (NoSp.callP hP.mul.nosp)
        (NoSp.seq (NoSp.callP hP.sub.nosp) (NoSp.seq (NoSp.callP hP.invNtt.nosp) (NoSp.seq
          (NoSp.callP hP.useHint.nosp) (NoSp.callP hP.simpleBitPack.nosp))))))))

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified`. -/
section

/-!
# ML-DSA verification on x86 (32-bit): the contract

`vg_mldsa*_verify` of the parameter sets of Table 1 meets `verifyContract`
with 96 bytes of stack (`verify_verified`), for any verified implementations
of the primitives it calls (`PrimsOk`): the body, as a leaf (`topLeaf`), from
the contract's precondition and public data (`pre_of`, `pub_of`), to its
postcondition (`VFin`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params)

/-- Memory with the arguments `0`, `0x1000`, `0x3000` and `0x10000` at `0x5004`. -/
def satMemV : Mem := fun a => if a = 0x5009 then 0x10 else if a = 0x500d then 0x30 else if a = 0x5012 then 1 else 0

/-- A state satisfying the precondition. -/
def verifySat (p : Params) : State :=
  VG.Proof.MlKem.X86.satState VG.Proof.MlDsa.X86.Verify.satMemV [⟨0, p.pkLen⟩, ⟨0x1000, 64⟩, ⟨0x3000, p.sigLen⟩] [⟨0x10000, VG.Proof.MlDsa.X86.Verify.scrLenV p⟩, ⟨0x5004, 16⟩]

theorem verify_verified {P : Prims} (hP : VG.Proof.MlDsa.X86.Verify.PrimsOk P) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified X86.target (verify P p) (Spec.MlDsa.verifyContract p X86.abi 96) := by
  have hF := VG.Proof.MlDsa.X86.Verify.vfacts hp
  refine Piece.verified (((topLeaf (VG.Proof.MlDsa.X86.Verify.body_nosp hP p) ((VG.Proof.MlDsa.X86.Verify.body_piece hP hF).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨h.1.1, h⟩)).pre_mono (fun _ h => VG.Proof.MlDsa.X86.Verify.pre_of h)
    fun _ _ _ _ h => VG.Proof.MlDsa.X86.Verify.pub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, ⟨⟨-, hd⟩, hax⟩, hm, hax'⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [sw_app, hax', hax]
    simp only [VG.Proof.MlDsa.X86.Verify.vPk, VG.Proof.MlDsa.X86.Verify.vMu, VG.Proof.MlDsa.X86.Verify.vSig, addr0] at hd
    exact hd
  · rcases hp with rfl | rfl | rfl
    · exact ⟨VG.Proof.MlDsa.X86.Verify.verifySat Spec.MlDsa.mlDsa44, by sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.Verify.verifySat, VG.Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.Verify.satMemV]⟩
    · exact ⟨VG.Proof.MlDsa.X86.Verify.verifySat Spec.MlDsa.mlDsa65, by sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.Verify.verifySat, VG.Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.Verify.satMemV]⟩
    · exact ⟨VG.Proof.MlDsa.X86.Verify.verifySat Spec.MlDsa.mlDsa87, by sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.Verify.verifySat, VG.Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.Verify.satMemV]⟩

end VG.Proof.MlDsa.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst`. -/
section

/-!
# ML-DSA verification on x86 (32-bit), with this library's primitives

The x86 primitives (`Impl.MlDsa.X86.Verify.prims`) are verified against their
contracts, use at most 56 bytes of stack and write `esp` only by frames and
calls (`prims_ok`), so `vg_mldsa{44,65,87}_verify` meet theirs
(`verify44_verified`, …).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify (prims verify44 verify65 verify87)

theorem prims_ok : VG.Proof.MlDsa.X86.Verify.PrimsOk VG.Impl.MlDsa.X86.Verify.prims where
  ntt := ⟨⟨15, by decide, Arith.NttFwd.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  invNtt := ⟨⟨15, by decide, Arith.NttInvP.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  mul := ⟨⟨15, by decide, Arith.mul_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  mulAdd := ⟨⟨15, by decide, Arith.mulAdd_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  sub := ⟨⟨15, by decide, Arith.sub_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  rejNtt := ⟨⟨55, by decide, Sample.RejNtt.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  ball := ⟨⟨55, by decide, Sample.Ball.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  useHint := ⟨⟨15, by decide, Round.useHint_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  simpleBitPack := ⟨⟨15, by decide, Pack.SimpleBitPack.verified⟩, by decide +kernel,
    NoSp.of_all (by decide +kernel)⟩
  bitUnpack := ⟨⟨15, by decide, Pack.Unpack.BU.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  unpackT1 := ⟨⟨15, by decide, Pack.Unpack.T1.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  hintUnpack := ⟨⟨15, by decide, Pack.Hint.hintBitUnpack_verified⟩, by decide +kernel,
    NoSp.of_all (by decide +kernel)⟩
  normLt := ⟨⟨15, by decide, Round.normLt_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩

theorem verify44_verified :
    Verified X86.target verify44 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 X86.abi 96) :=
  VG.Proof.MlDsa.X86.Verify.verify_verified VG.Proof.MlDsa.X86.Verify.prims_ok _ (.inl rfl)

theorem verify65_verified :
    Verified X86.target verify65 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 X86.abi 96) :=
  VG.Proof.MlDsa.X86.Verify.verify_verified VG.Proof.MlDsa.X86.Verify.prims_ok _ (.inr (.inl rfl))

theorem verify87_verified :
    Verified X86.target verify87 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 X86.abi 96) :=
  VG.Proof.MlDsa.X86.Verify.verify_verified VG.Proof.MlDsa.X86.Verify.prims_ok _ (.inr (.inr rfl))

end VG.Proof.MlDsa.X86.Verify

end
