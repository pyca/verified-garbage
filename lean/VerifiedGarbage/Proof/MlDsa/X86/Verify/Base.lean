module

public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Samp
public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Verify
public import VerifiedGarbage.Proof.MlDsa.Verify.Spec
public import VerifiedGarbage.Proof.MlDsa.Verify.Final
public import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
public import VerifiedGarbage.Proof.MlDsa.Verify.Norm
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
public import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
public import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
public import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
public import VerifiedGarbage.Proof.MlDsa.Verify.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlKem.X86.Pack
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Call
public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlDsa.X86.Verify.Prim`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86 (32-bit): calls of the primitives verification calls

As `KeyGen/Prim.lean`, for the signatures of `vg_mldsa_sample_in_ball`,
`vg_mldsa_use_hint`, `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1`,
`vg_mldsa_hint_bit_unpack` and `vg_mldsa_norm_lt` (which may not write its
arguments: `callPR_pieceRO`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.KeyGen (Arg argRegs setArgs callP callPR)
open VG.Spec.MlDsa (Poly)
open VG.Proof.MlDsa (Reduced PolyIs polyAt)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-! ## `vg_mldsa_sample_in_ball` -/

theorem ball_piece {c : Prog isa} (hc : Callee c fun stk => Proof.MlDsa.sampleInBallContract X86.abi stk)
    (da dO L τ aa ao wa wo : Nat) (hb : (L, τ) ∈ Proof.MlDsa.ballParams)
    (hk : (Y.ok ⟨da, dO, L⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨wa, wo, 2048⟩ && Y.sep ⟨da, dO, L⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, L⟩ ⟨wa, wo, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨wa, wo, 2048⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨da, dO, L⟩, .imm L, .imm τ, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩]))
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, L⟩) L = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, L⟩) L)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] 80) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Spec.MlDsa.Outcome (fun b => (Spec.MlDsa.sampleInBall τ b.ball
        (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, L⟩) L)).map Spec.MlDsa.toRq) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callPR Y.sc "vg_mldsa_sample_in_ball" c
        [.buf ⟨da, dO, L⟩, .imm L, .imm τ, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hD, hAw⟩, hW⟩, dDA⟩, dDW⟩, dAW⟩ := hk
  obtain hA₁ := (Lay.okW_iff.mp hAw).1
  obtain hW₁ := (Lay.okW_iff.mp hW).1
  obtain hbnd : L < 2 ^ 32 ∧ τ < 2 ^ 32 := by
    simp only [Proof.MlDsa.ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb; omega_using [hb]
  obtain eL : (BitVec.ofNat 32 L).toNat = L := KeyGen.toNat_ofNat32 hbnd.1
  obtain eτ : (BitVec.ofNat 32 τ).toNat = τ := KeyGen.toNat_ofNat32 hbnd.2
  refine callPR_piece _ [⟨da, dO, L⟩] [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hD, hA₁, hW₁, hbnd]) hN (by simp [hD]) (by simp [hAw, hW]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨b₁, b₂, b₃, b₄⟩ := he.buf hp hN (by simp) hD hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hA₁ hK
    obtain ⟨w₁, w₂, w₃, w₄⟩ := he.buf hp hN (by simp) hW₁ hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    obtain d₁ := Buf.disj hp hD hA₁ dDA
    obtain d₂ := Buf.disj hp hD hW₁ dDW
    obtain d₃ := Buf.disj hp hA₁ hW₁ dAW
    have := (E1 s₀).isLt
    obtain a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    obtain a₂ := he.arg 2 (by simp)
    obtain a₃ := he.arg 3 (by simp)
    obtain a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eL, eτ] at *
    have := hb
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hD, hA₁, hW₁, hbnd]) he he'
    obtain hs := hseed s₀ s₀' s s' hp hp' hq ha ha'
    obtain a₀ := he.arg 0 (by simp)
    obtain a₀' := he'.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    obtain a₁' := he'.arg 1 (by simp)
    rw [← Proof.MlKem.bytesAt_congr (he.mem _ hD), ← Proof.MlKem.bytesAt_congr (he'.mem _ hD)] at hs
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Arg.val] at a₀ a₀' a₁ a₁'
    simp only [Buf.addr, ← a₀, ← a₀'] at hs
    simp only [arg_withRegions]
    refine ⟨esp, ?_, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
    rw [a₁, a₁', eL, hs]
  · have a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    obtain a₂ := he.arg 2 (by simp)
    obtain a₃ := he.arg 3 (by simp)
    generalize e = e' at *
    sig_post [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, g₂,
      sw_app, eL, eτ] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hD)] at post
    obtain kA := (lostK hp h' (by simp) hN m₂ hA₁)
    exact hQ s₀ s s' hp ha h' fr (fun e => Proof.MlDsa.KeyGen.reduced_congr kA (post.1 e))
      (by rw [Proof.MlDsa.KeyGen.polyAt_congr kA]; exact post.2)

/-! ## `vg_mldsa_use_hint` -/

theorem useHint_piece {c : Prog isa} (hc : Callee c fun stk => Proof.MlDsa.useHintContract X86.abi stk)
    (ha hao ra ro g oa oo : Nat) (hg : g ∈ Proof.MlDsa.gamma2s)
    (hk : (Y.ok ⟨ha, hao, 1024⟩ && Y.ok ⟨ra, ro, 1024⟩ && Y.okW ⟨oa, oo, 1024⟩ && Y.sep ⟨ha, hao, 1024⟩ ⟨oa, oo, 1024⟩ &&
      Y.sep ⟨ra, ro, 1024⟩ ⟨oa, oo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ha, hao, 1024⟩, .buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨oa, oo, 1024⟩]))
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨oa, oo, 1024⟩] 80) s.mem s'.mem →
      Proof.MlDsa.NatPolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        (Vector.zipWith (fun hj rj => (Spec.MlDsa.useHint g hj rj).toNat)
          ((Proof.MlDsa.hintAt s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩) 1).headD (Vector.replicate Spec.MlDsa.n false))
          (polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_use_hint" c [.buf ⟨ha, hao, 1024⟩, .buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨oa, oo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨hH, hR⟩, hOw⟩, dHO⟩, dRO⟩ := hk
  obtain hO := (Lay.okW_iff.mp hOw).1
  obtain hgb : g < 2 ^ 32 := by
    simp only [Proof.MlDsa.gamma2s, Spec.MlDsa.q, List.mem_cons, List.not_mem_nil, or_false] at hg; omega_using [hg]
  obtain eg : (BitVec.ofNat 32 g).toNat = g := KeyGen.toNat_ofNat32 hgb
  refine callP_piece _ [⟨ha, hao, 1024⟩, ⟨ra, ro, 1024⟩] [⟨oa, oo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hH, hR, hO, hgb]) hN (by simp [hH, hR]) (by simp [hOw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨r₁, r₂, r₃, r₄⟩ := he.buf hp hN (by simp) hR hK
    obtain ⟨o₁, o₂, o₃, o₄⟩ := he.buf hp hN (by simp) hO hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    obtain d₁ := Buf.disj hp hH hO dHO
    obtain d₂ := Buf.disj hp hR hO dRO
    obtain rr := ent_reduced he hR (hA s₀ s hp ha).2
    have := (E1 s₀).isLt
    obtain a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    obtain a₂ := he.arg 2 (by simp)
    obtain a₃ := he.arg 3 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eg] at *
    have := hg
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hH, hR, hO, hgb]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    obtain a₂ := he.arg 2 (by simp)
    obtain a₃ := he.arg 3 (by simp)
    generalize e = e' at *
    sig_post [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val,
      eg] at post
    rw [ent_polyAt he hR, Proof.MlDsa.Pack.hintAt_congr (fun t ht =>
      Proof.MlDsa.KeyGen.coeffAt_congr (he.mem _ hH) (by simp only [Spec.MlDsa.n]; omega_using [ht]))] at post
    exact hQ s₀ s s' hp ha h' fr ((Proof.MlDsa.KeyGen.natPolyAt_congr (lostK hp h' (by simp) hN m₂ hO)).trans post)

/-! ## `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1` -/

theorem bu_piece {c : Prog isa} (hc : Callee c fun stk => Proof.MlDsa.bitUnpackContract X86.abi stk)
    (va vo L a b fa fo : Nat) (hab : (a, b) ∈ Proof.MlDsa.bitPackParams) (hL : L = 32 * Spec.MlDsa.bitlen (a + b))
    (hk : (Y.ok ⟨va, vo, L⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨va, vo, L⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨va, vo, L⟩, .imm L, .imm a, .imm b, .buf ⟨fa, fo, 1024⟩])) ht).isSome
      = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨va, vo, L⟩) L) a b)) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_bit_unpack" c [.buf ⟨va, vo, L⟩, .imm L, .imm a, .imm b, .buf ⟨fa, fo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hV, hFw⟩, dVF⟩ := hk
  obtain hF := (Lay.okW_iff.mp hFw).1
  obtain ⟨hav, hbv, hL'⟩ := bp_bounds (a, b) hab
  rw [← hL] at hL'
  obtain ea : (BitVec.ofNat 32 a).toNat = a := KeyGen.toNat_ofNat32 hav
  obtain eb : (BitVec.ofNat 32 b).toNat = b := KeyGen.toNat_ofNat32 hbv
  obtain eL : (BitVec.ofNat 32 L).toNat = L := KeyGen.toNat_ofNat32 hL'
  refine callP_piece _ [⟨va, vo, L⟩] [⟨fa, fo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hV, hav, hbv, hL']) hN (by simp [hV]) (by simp [hFw]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨v₁, v₂, v₃, v₄⟩ := he.buf hp hN (by simp) hV hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    obtain d₁ := Buf.disj hp hV hF dVF
    have := (E1 s₀).isLt
    obtain a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    obtain a₂ := he.arg 2 (by simp)
    obtain a₃ := he.arg 3 (by simp)
    obtain a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Proof.MlDsa.bitUnpackContract, Proof.MlDsa.bitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
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
    sig_pub [Proof.MlDsa.bitUnpackContract, Proof.MlDsa.bitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    obtain a₂ := he.arg 2 (by simp)
    obtain a₃ := he.arg 3 (by simp)
    obtain a₄ := he.arg 4 (by simp)
    generalize e = e' at *
    sig_post [Proof.MlDsa.bitUnpackContract, Proof.MlDsa.bitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, a₄, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val,
      ea, eb, eL] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hV)] at post
    exact hQ s₀ s s' hp ha h' fr (Proof.MlDsa.KeyGen.polyIs_congr (lostK hp h' (by simp) hN m₂ hF) post)

theorem t1_piece {c : Prog isa} (hc : Callee c fun stk => Proof.MlDsa.unpackT1Contract X86.abi stk)
    (va vo fa fo : Nat)
    (hk : (Y.ok ⟨va, vo, 320⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨va, vo, 320⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨va, vo, 320⟩, .buf ⟨fa, fo, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        ((Spec.MlDsa.simpleBitUnpack (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨va, vo, 320⟩) 320) Spec.MlDsa.t1Max).map
          fun c => Spec.MlDsa.ofInt (c * 2 ^ Spec.MlDsa.d : Nat)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_unpack_t1" c [.buf ⟨va, vo, 320⟩, .buf ⟨fa, fo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hV, hFw⟩, dVF⟩ := hk
  obtain hF := (Lay.okW_iff.mp hFw).1
  refine callP_piece _ [⟨va, vo, 320⟩] [⟨fa, fo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hV]) hN (by simp [hV]) (by simp [hFw]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨v₁, v₂, v₃, v₄⟩ := he.buf hp hN (by simp) hV hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    obtain d₁ := Buf.disj hp hV hF dVF
    have := (E1 s₀).isLt
    obtain a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Proof.MlDsa.unpackT1Contract, Proof.MlDsa.unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hF, hV]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Proof.MlDsa.unpackT1Contract, Proof.MlDsa.unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    generalize e = e' at *
    sig_post [Proof.MlDsa.unpackT1Contract, Proof.MlDsa.unpackT1Sig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hV)] at post
    exact hQ s₀ s s' hp ha h' fr (Proof.MlDsa.KeyGen.polyIs_congr (lostK hp h' (by simp) hN m₂ hF) post)

/-! ## `vg_mldsa_hint_bit_unpack` -/

theorem hu_piece {c : Prog isa} (hc : Callee c fun stk => Proof.MlDsa.hintBitUnpackContract X86.abi stk)
    (ya yo ω k ha ho : Nat) (hwk : (ω, k) ∈ Proof.MlDsa.hintParams)
    (hk : (Y.ok ⟨ya, yo, ω + k⟩ && Y.okW ⟨ha, ho, 256 * k * 4⟩ && Y.sep ⟨ya, yo, ω + k⟩ ⟨ha, ho, 256 * k * 4⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ya, yo, ω + k⟩, .imm (ω + k), .imm ω, .buf ⟨ha, ho, 256 * k * 4⟩,
        .imm (256 * k)])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ya, yo, ω + k⟩) (ω + k) =
        Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨ya, yo, ω + k⟩) (ω + k))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨ha, ho, 256 * k * 4⟩] 80) s.mem s'.mem →
      (match Spec.MlDsa.hintBitUnpack ω k (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ya, yo, ω + k⟩) (ω + k)) with
        | some hint => s'.gpr .eax = 1 ∧ Proof.MlDsa.HintIs s'.mem (Buf.addr s₀ ⟨ha, ho, 256 * k * 4⟩) k hint
        | none => s'.gpr .eax = 0) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callPR Y.sc "vg_mldsa_hint_bit_unpack" c [.buf ⟨ya, yo, ω + k⟩, .imm (ω + k), .imm ω,
        .buf ⟨ha, ho, 256 * k * 4⟩, .imm (256 * k)]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hYb, hHw⟩, dYH⟩ := hk
  obtain hH := (Lay.okW_iff.mp hHw).1
  obtain hb : ω + k < 2 ^ 32 ∧ ω < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
    simp only [Proof.MlDsa.hintParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwk; omega_using [hwk]
  obtain e1 : (BitVec.ofNat 32 (ω + k)).toNat = ω + k := KeyGen.toNat_ofNat32 hb.1
  obtain e2 : (BitVec.ofNat 32 ω).toNat = ω := KeyGen.toNat_ofNat32 hb.2.1
  obtain e3 : (BitVec.ofNat 32 (256 * k)).toNat = 256 * k := KeyGen.toNat_ofNat32 hb.2.2
  obtain e4 : ω + k - ω = k := by omega_using []
  refine callPR_piece _ [⟨ya, yo, ω + k⟩] [⟨ha, ho, 256 * k * 4⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hYb, hH, hb]) hN (by simp [hYb]) (by simp [hHw]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨y₁, y₂, y₃, y₄⟩ := he.buf hp hN (by simp) hYb hK
    obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    obtain d₁ := Buf.disj hp hYb hH dYH
    have := (E1 s₀).isLt
    obtain a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    obtain a₂ := he.arg 2 (by simp)
    obtain a₃ := he.arg 3 (by simp)
    obtain a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Proof.MlDsa.hintBitUnpackContract, Proof.MlDsa.hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, e1, e2, e3,
      e4] at *
    have := hwk
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hYb, hH, hb]) he he'
    obtain hs := hseed s₀ s₀' s s' hp hp' hq ha ha'
    obtain a₀ := he.arg 0 (by simp)
    obtain a₀' := he'.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    obtain a₁' := he'.arg 1 (by simp)
    rw [← Proof.MlKem.bytesAt_congr (he.mem _ hYb), ← Proof.MlKem.bytesAt_congr (he'.mem _ hYb)] at hs
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Proof.MlDsa.hintBitUnpackContract, Proof.MlDsa.hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Arg.val] at a₀ a₀' a₁ a₁'
    simp only [Buf.addr, ← a₀, ← a₀'] at hs
    simp only [arg_withRegions]
    refine ⟨esp, ?_, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
    rw [a₁, a₁', e1, hs]
  · have a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    obtain a₂ := he.arg 2 (by simp)
    obtain a₃ := he.arg 3 (by simp)
    obtain a₄ := he.arg 4 (by simp)
    generalize e = e' at *
    sig_post [Proof.MlDsa.hintBitUnpackContract, Proof.MlDsa.hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, g₂,
      sw_app, e1, e2, e4] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hYb)] at post
    obtain kH := (lostK hp h' (by simp) hN m₂ hH)
    refine hQ s₀ s s' hp ha h' fr ?_
    generalize Spec.MlDsa.hintBitUnpack ω k (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ya, yo, ω + k⟩) (ω + k)) = hb
      at post ⊢
    cases hb with
    | none => exact post
    | some hint =>
      exact ⟨post.1, VG.Proof.MlDsa.Verify.hintIs_congr (fun i hi => kH i (by simp only; omega_arith)) post.2⟩

/-! ## `vg_mldsa_norm_lt` -/

theorem normLt_piece {c : Prog isa} (hc : Callee c fun stk => Proof.MlDsa.normLtContract X86.abi stk)
    (fa fo bd : Nat) (hbd : bd < 2 ^ 32) (hk : Y.ok ⟨fa, fo, 1024⟩ = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .imm bd])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [] 80) s.mem s'.mem →
      s'.gpr .eax = (if Spec.MlDsa.normRq [polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)] < bd then 1 else 0) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callPR Y.sc "vg_mldsa_norm_lt" c [.buf ⟨fa, fo, 1024⟩, .imm bd]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  obtain eb : (BitVec.ofNat 32 bd).toNat = bd := KeyGen.toNat_ofNat32 hbd
  refine callPR_pieceRO _ [⟨fa, fo, 1024⟩] [] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hk, hbd]) hN (by simp [hk]) (by simp) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hk hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    obtain rf := ent_reduced he hk (hA s₀ s hp ha).2
    have := (E1 s₀).isLt
    obtain a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eb] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hk, hbd]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    obtain a₁ := he.arg 1 (by simp)
    generalize e = e' at *
    sig_post [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, g₂, sw_app,
      eb] at post
    rw [ent_polyAt he hk] at post
    exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlDsa.X86.Verify

end

end

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

@[expose] public section

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-- Verified implementations of the primitives verification calls. -/
structure PrimsOk (P : Prims) : Prop where
  ntt : Callee P.ntt (fun stk => Proof.MlDsa.nttContract X86.abi stk)
  invNtt : Callee P.invNtt (fun stk => Proof.MlDsa.nttInvContract X86.abi stk)
  mul : Callee P.mul (fun stk => Proof.MlDsa.mulContract X86.abi stk)
  mulAdd : Callee P.mulAdd (fun stk => Proof.MlDsa.mulAddContract X86.abi stk)
  sub : Callee P.sub (fun stk => Proof.MlDsa.subContract X86.abi stk)
  rejNtt : Callee P.rejNtt (fun stk => Proof.MlDsa.rejNTTContract X86.abi stk)
  ball : Callee P.ball (fun stk => Proof.MlDsa.sampleInBallContract X86.abi stk)
  useHint : Callee P.useHint (fun stk => Proof.MlDsa.useHintContract X86.abi stk)
  simpleBitPack : Callee P.simpleBitPack (fun stk => Proof.MlDsa.simpleBitPackContract X86.abi stk)
  bitUnpack : Callee P.bitUnpack (fun stk => Proof.MlDsa.bitUnpackContract X86.abi stk)
  unpackT1 : Callee P.unpackT1 (fun stk => Proof.MlDsa.unpackT1Contract X86.abi stk)
  hintUnpack : Callee P.hintUnpack (fun stk => Proof.MlDsa.hintBitUnpackContract X86.abi stk)
  normLt : Callee P.normLt (fun stk => Proof.MlDsa.normLtContract X86.abi stk)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure VFacts (p : Params) : Prop where
  k : 1 ≤ p.k ∧ p.k ≤ 8
  l : 1 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : 4 ≤ p.k * p.ℓ ∧ p.k * p.ℓ ≤ 56
  ct : 32 ≤ p.ctildeLen ∧ p.ctildeLen ≤ 64
  lz : 576 ≤ lenZ p ∧ lenZ p ≤ 640
  w1 : 128 ≤ w1Len p ∧ 512 ≤ p.k * w1Len p ∧ p.k * w1Len p ≤ 1024
  scr : 8192 + 1024 * (20 + 8 * p.k) ≤ scratchWords p * 8 - 1024 * p.k
  pk : p.pkLen = 32 + 320 * p.k
  sig : p.sigLen = p.ctildeLen + lenZ p * p.ℓ + p.ω + p.k
  sw : scratchWords p = 128 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32)
  om : p.ω ≤ 80
  hint : (p.ω, p.k) ∈ Proof.MlDsa.hintParams
  ball : (p.ctildeLen, p.τ) ∈ Proof.MlDsa.ballParams
  g1 : p.γ₁ ∈ Proof.MlDsa.Verify.gamma1s
  bp : (p.γ₁ - 1, p.γ₁) ∈ Proof.MlDsa.bitPackParams ∧ lenZ p = 32 * Spec.MlDsa.bitlen (p.γ₁ - 1 + p.γ₁)
  beta : 0 < p.γ₁ - p.β ∧ p.γ₁ - p.β < 2 ^ 32
  g2 : p.γ₂ ∈ Proof.MlDsa.gamma2s
  sbp : w1Max p ∈ Proof.MlDsa.simpleBitPackBounds ∧ w1Len p = 32 * Spec.MlDsa.bitlen (w1Max p)
  /-- Which parameter set: a check about one can be decided for each (`lvd`). -/
  mem : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

theorem vfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VFacts p := by
  have hm := hp
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, rfl,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, hm⟩

/-! ## The layout -/

/-- The size of `scratch`, in bytes: that of the external functions but the
`1024 k` bytes `vg_mldsa*_verify` computes `t̂₁` in. -/
abbrev scrLenV (p : Params) : Nat := scratchWords p * 8 - 1024 * p.k

/-- `pk`, `mu` and `sig` (read), `scratch` (written), `t1` (read); 96 bytes of stack. -/
def YV (p : Params) : Lay :=
  ⟨[(p.pkLen, false), (64, false), (p.sigLen, false), (scrLenV p, true), (1024 * p.k, false)], 3, 96⟩

theorem YV_sc (p : Params) : (YV p).sc = vS := rfl
theorem YV_stk (p : Params) : (YV p).stk = 96 := rfl
theorem stkV {p : Params} {N : Nat} (h : N + 16 ≤ 96) : N + 16 ≤ (YV p).stk := h
theorem YV_n (p : Params) : (YV p).n = 5 := rfl
theorem YV_alen0 (p : Params) : (YV p).alen 0 = p.pkLen := rfl
theorem YV_alen1 (p : Params) : (YV p).alen 1 = 64 := rfl
theorem YV_alen2 (p : Params) : (YV p).alen 2 = p.sigLen := rfl
theorem YV_alen3 (p : Params) : (YV p).alen 3 = scrLenV p := rfl
theorem YV_awr0 (p : Params) : (YV p).awr 0 = false := rfl
theorem YV_awr1 (p : Params) : (YV p).awr 1 = false := rfl
theorem YV_awr2 (p : Params) : (YV p).awr 2 = false := rfl
theorem YV_awr3 (p : Params) : (YV p).awr 3 = true := rfl
theorem YV_alen4 (p : Params) : (YV p).alen 4 = 1024 * p.k := rfl
theorem YV_awr4 (p : Params) : (YV p).awr 4 = false := rfl

/-! ### Checks of buffers, as arithmetic -/

/-- The result, a word of `scratch`. -/
abbrev accB (Y : Lay) : Buf := ⟨Y.sc, oACC, 4⟩

theorem okS {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ scratchWords p * 8 - 1024 * p.k) :
    (YV p).ok ⟨3, o, l⟩ = true := Lay.ok_iff.mpr ⟨show 3 < 5 by decide, h₁, h₂⟩

theorem okWS {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ scratchWords p * 8 - 1024 * p.k) :
    (YV p).okW ⟨3, o, l⟩ = true := Lay.okW_iff.mpr ⟨okS h₁ h₂, rfl⟩

theorem okPk {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ p.pkLen) : (YV p).ok ⟨0, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨show 0 < 5 by decide, h₁, h₂⟩

theorem okMu {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ 64) : (YV p).ok ⟨1, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨show 1 < 5 by decide, h₁, h₂⟩

theorem okSig {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ p.sigLen) : (YV p).ok ⟨2, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨show 2 < 5 by decide, h₁, h₂⟩

theorem okT {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ 1024 * p.k) : (YV p).ok ⟨4, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨show 4 < 5 by decide, h₁, h₂⟩

theorem sepS {p : Params} {o₁ l₁ o₂ l₂ : Nat} (h : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (YV p).sep ⟨3, o₁, l₁⟩ ⟨3, o₂, l₂⟩ = true := by
  unfold Lay.sep
  simp only [ite_true, Bool.or_eq_true, decide_eq_true_eq]
  exact h

theorem sepRS {p : Params} {a o₁ l₁ o₂ l₂ : Nat} (ha : a < 3 ∨ a = 4) : (YV p).sep ⟨a, o₁, l₁⟩ ⟨3, o₂, l₂⟩ = true := by
  unfold Lay.sep
  rw [ite_eq_right_iff.mpr fun h => absurd h (show a ≠ 3 by omega_using [ha])]
  exact Bool.or_eq_true_iff.mpr (.inr rfl)

theorem sepSR {p : Params} {a o₁ l₁ o₂ l₂ : Nat} (ha : a < 3 ∨ a = 4) : (YV p).sep ⟨3, o₁, l₁⟩ ⟨a, o₂, l₂⟩ = true := by
  unfold Lay.sep
  rw [ite_eq_right_iff.mpr fun h => absurd h (show 3 ≠ a by omega_using [ha])]
  exact Bool.or_eq_true_iff.mpr (.inl rfl)

theorem apart_nil' {Y : Lay} {b : Buf} (h : Y.ok b = true) : Y.apart b [] = true := by
  simp [Lay.apart, h]

theorem apart_cons' {Y : Lay} {b c : Buf} {bs : List Buf} (h₁ : Y.apart b bs = true) (h₂ : Y.ok c = true)
    (h₃ : Y.sep b c = true) : Y.apart b (c :: bs) = true := by
  simp only [Lay.apart, List.all_cons, Bool.and_eq_true] at h₁ ⊢
  exact ⟨h₁.1, ⟨h₂, h₃⟩, h₁.2⟩

/-- Rows of `z` in the signature, and of `w₁` in `scratch`. -/
theorem mul_row {a i n : Nat} (hi : i < n) : a * i + a ≤ a * n := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

-- Select layout rules by the outer form; the full tactic retains its original fallback.
open Lean Elab Tactic in
elab "lv_step" : tactic => withMainContext do
  let some (_, lhs, _) := (← getMainTarget).eq? | throwError "not a layout equality"
  match lhs.getAppFn.constName? with
  | some ``VG.Proof.MlKem.X86.Top.Lay.apart =>
    evalTactic (← `(tactic| first
      | with_reducible apply VG.Proof.MlDsa.X86.Verify.apart_cons'
      | with_reducible apply VG.Proof.MlDsa.X86.Verify.apart_nil'))
  | some ``VG.Proof.MlKem.X86.Top.Lay.okW =>
    evalTactic (← `(tactic| with_reducible apply VG.Proof.MlDsa.X86.Verify.okWS))
  | some ``VG.Proof.MlKem.X86.Top.Lay.ok =>
    evalTactic (← `(tactic| first
      | with_reducible apply VG.Proof.MlDsa.X86.Verify.okS
      | with_reducible apply VG.Proof.MlDsa.X86.Verify.okPk
      | with_reducible apply VG.Proof.MlDsa.X86.Verify.okMu
      | with_reducible apply VG.Proof.MlDsa.X86.Verify.okSig
      | with_reducible apply VG.Proof.MlDsa.X86.Verify.okT))
  | some ``VG.Proof.MlKem.X86.Top.Lay.sep =>
    evalTactic (← `(tactic| first
      | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepS
      | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepRS
      | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepSR))
  | _ => throwError "not a layout check"

syntax "lv_core " term:max " using " tactic : tactic
macro_rules
  | `(tactic| lv_core $hF using $step:tactic) => do
    let steps ← `(tacticSeq| $step:tactic)
    `(tactic| (
      try simp only [Bool.and_eq_true, VG.Proof.MlDsa.X86.Verify.accB, VG.Proof.MlDsa.X86.Verify.YV_sc,
        VG.Proof.MlDsa.X86.KeyGen.chk3]
      try and_intros
      repeat' ($steps)
      all_goals (
        have := ($hF).k; have := ($hF).l; have := ($hF).ct; have := ($hF).om; have := ($hF).lz
        have := ($hF).w1; have := ($hF).scr; have := ($hF).pk; have := ($hF).sig
        try simp only [VG.Impl.MlDsa.X86.Verify.oP, VG.Impl.MlDsa.X86.Verify.oSB, VG.Impl.MlDsa.X86.Verify.oB,
          VG.Impl.MlDsa.X86.Verify.oCT, VG.Impl.MlDsa.X86.Verify.oACC, VG.Impl.MlDsa.X86.Verify.oSS,
          VG.Impl.MlDsa.X86.Verify.oHint]
        omega_arith)))

/-- A check about the layout that mentions no variable but the parameter set and
bounded indices, decided for each parameter set (`decide_at`): cheaper than
`lv`, which unfolds it into arithmetic on the parameters for `omega`, unless
there are many indices to try. -/
tactic_template "lvd" : tactic => `(tactic| (
      have hmem := (‹VG.Proof.MlDsa.X86.Verify.VFacts _›).mem; decide_at hmem))

/-- Proves checks of buffers against the layout (`ok`, `okW`, `sep`, `apart`),
from arithmetic on their offsets closed by `omega`, with the facts of the
parameter set `hF : VFacts p` and those in the context. -/
tactic_template "lv " hF:term:max : tactic => `(tactic| first
      | lv_core $hF using lv_step
      | lv_core $hF using (first
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.apart_cons'
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.apart_nil'
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.okWS | with_reducible apply VG.Proof.MlDsa.X86.Verify.okS
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.okPk | with_reducible apply VG.Proof.MlDsa.X86.Verify.okMu
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.okSig | with_reducible apply VG.Proof.MlDsa.X86.Verify.okT
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepS
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepRS
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepSR))

/-! ## The inputs -/

section
variable (p : Params) (s₀ : State)

abbrev vPk : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen
abbrev vMu : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64
abbrev vSig : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨2, 0, p.sigLen⟩) p.sigLen

/-- What verification may leak, its inputs. -/
def lkV : List Byte := vPk p s₀ ++ vMu s₀ ++ vSig p s₀

/-- The result so far. -/
abbrev accV (s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (sb oACC 4)) 32

end

/-- A piece of verification. -/
abbrev VP (p : Params) := Piece (TPre (YV p)) (TPub (YV p) (lkV p))

theorem inputs_pub {p : Params} {s₀ s₀' : State} (hq : TPub (YV p) (lkV p) s₀ s₀') :
    vPk p s₀ = vPk p s₀' ∧ vMu s₀ = vMu s₀' ∧ vSig p s₀ = vSig p s₀' := by
  have h := hq.2.2
  simp only [lkV] at h
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [Proof.MlKem.bytesAt_length])
  obtain ⟨h₃, h₄⟩ := List.append_inj h₁ (by simp [Proof.MlKem.bytesAt_length])
  exact ⟨h₃, h₄, h₂⟩

/-! ## The contract of `vg_mldsa*_verify_core`

Not trusted: the contract of the internal function that `vg_mldsa*_verify`
and `vg_mldsa*_verify_prepared` share. It is `verifyContract`, with `scratch`
`1024 k` bytes shorter and a further argument `t1` holding the polynomials
`preparedPublicPolys` of `pk` (`T1In`). -/

/-- The `k` polynomials of `t1` are `preparedPublicPolys` of the public key `pk`. -/
def T1In (p : Params) (m : Mem) (t1 : Addr) (pk : List Byte) : Prop :=
  ∀ r < p.k, PolyIs m (t1 + BitVec.ofNat 64 (1024 * r)) (Spec.MlDsa.preparedPublicPolys p pk)[r]!

/-- `vg_mldsa*_verify_core(pk, mu, sig, scratch, t1) -> u32`. -/
def verifyCoreSig (p : Params) : Sig where
  params := [("pk", .array false .u8 p.pkLen), ("mu", .array false .u8 64),
    ("sig", .array false .u8 p.sigLen), ("scratch", .array true .u64 (scratchWords p - 128 * p.k)),
    ("t1", .array false .u8 (1024 * p.k))]
  ret := some .u32

/-- `verifyContract`, with `t̂₁` given in `t1`. -/
def verifyCoreContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (verifyCoreSig p).contract A
    (pre := fun pk _mu _sig _scratch t1 m => T1In p m t1 (bytesAt m pk p.pkLen))
    (post := fun pk mu sig _scratch _t1 m _m' r =>
      let v := fun b => Spec.MlDsa.verifyMu p b (bytesAt m pk p.pkLen) (bytesAt m mu 64) (bytesAt m sig p.sigLen)
      (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v Spec.MlDsa.minBounds ≠ some true))
    (writeArgs := true) (stack := stack)
    (leak := some fun pk mu sig _scratch _t1 m =>
      Spec.MlDsa.leakBytes (bytesAt m pk p.pkLen ++ bytesAt m mu 64 ++ bytesAt m sig p.sigLen))

theorem pre_of {p : Params} {s₀ : State} (h : (verifyCoreContract p X86.abi 96).pre s₀) :
    TPre (YV p) s₀ ∧ T1In p s₀.mem ((arg s₀ 4).setWidth 64) (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) := by
  sig_pre [verifyCoreContract, verifyCoreSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, d0s, d0g, d1s, d1g, d2s, d2g, ds4, dsg, d4g, r0, r1, r2, r3, r4, rg,
    s0, s1, s2, s3, s4, sg, f0, f1, f2, f3, f4, kp⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at s0 s1 s2 s3 s4 sg
  have c5 : ∀ i, i < (YV p).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    rw [YV_n] at hi; omega_using [hi]
  have e3 : (scratchWords p - 128 * p.k) * 8 = scrLenV p := by simp only [scrLenV]; omega_using []
  rw [e3] at h4 d0s d1s d2s ds4 dsg r3 s3 f3
  refine ⟨⟨h1, by rw [YV_stk]; omega_using [], by rw [YV_n]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, sg, ?_, by rw [YV_sc, YV_n]; decide⟩, kp⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · simp [argR, Lay.alen, YV]
    · simp [argR, Lay.alen, YV]
    · simp [argR, Lay.alen, YV]
    · simp [YV, Lay.awr] at hw
    · simp [argR, Lay.alen, YV]
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    any_goals simp [YV, Lay.awr] at hw
    simp [argR, Lay.alen, YV]
  · rw [h4]; simp [gR, Lay.n, YV]
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | skip
    all_goals simp only [YV_awr0, YV_awr1, YV_awr2, YV_awr3, YV_awr4, Bool.or_false, Bool.or_true,
      Bool.false_eq_true] at hw
    all_goals simp only [argR, YV_alen0, YV_alen1, YV_alen2, YV_alen3, YV_alen4]
    exacts [d0s, d1s, d2s, d0s.symm, d1s.symm, d2s.symm, ds4, ds4.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;>
      simp only [argR, gR, YV_n, YV_alen0, YV_alen1, YV_alen2, YV_alen3, YV_alen4]
    · exact d0g.symm
    · exact d1g.symm
    · exact d2g.symm
    · exact dsg.symm
    · exact d4g.symm
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;>
      simp only [argR, YV_alen0, YV_alen1, YV_alen2, YV_alen3, YV_alen4]
    exacts [r0, r1, r2, r3, r4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;>
      simp only [argR, YV_stk, YV_alen0, YV_alen1, YV_alen2, YV_alen3, YV_alen4]
    exacts [s0, s1, s2, s3, s4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> simp only [YV_alen0, YV_alen1, YV_alen2, YV_alen3, YV_alen4]
    exacts [f0, f1, f2, f3, f4]

theorem pub_of {p : Params} {s₀ s₀' : State} (h : (verifyCoreContract p X86.abi 96).pub s₀ s₀') :
    TPub (YV p) (lkV p) s₀ s₀' := by
  sig_pub [verifyCoreContract, verifyCoreSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · rw [YV_n] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆, e₇]
  · simp only [lkV, vPk, vMu, vSig, addr0]
    exact Proof.MlDsa.KeyGen.leakBytes_inj e₂

end VG.Proof.MlDsa.X86.Verify
