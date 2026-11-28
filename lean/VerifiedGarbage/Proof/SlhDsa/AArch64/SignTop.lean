module

-- separate module: the contract and the branch on ctx_len, which the body's proofs do not change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.Contracts
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Sz
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Shake
public import VerifiedGarbage.Spec.SlhDsa.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-!
# SLH-DSA (SHAKE) on AArch64, `sign`, correct

`sign(sk = x0, msg = x1, msg_len = x2, ctx = x3, ctx_len = x4, addrnd = x5,
sig = x6, scratch = x7)` (`Impl.SlhDsa.AArch64.Shake.sign`): `ctx_len`
against 256 (`ctx_len ≫ 8`); if it is below, the body, which writes
`slh_sign_internal` of the formatted message to `sig` and returns 1
(`BodyPost`); otherwise 2 (`sign_wp`, against `sgK`, the contract spelled
out a fact at a time).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Sign

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract, as the proof uses it -/

/-- `signContract`'s precondition, a fact at a time. -/
structure SG (p : Params) (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
    ⟨s.gpr .x5, p.n⟩]
  wr : s.wr = [⟨s.gpr .x6, p.sigLen⟩, ⟨s.gpr .x7, scratchLen⟩]
  sk_sig : Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x6, p.sigLen⟩
  sk_scr : Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x7, scratchLen⟩
  msg_sig : Region.Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩ ⟨s.gpr .x6, p.sigLen⟩
  msg_scr : Region.Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩ ⟨s.gpr .x7, scratchLen⟩
  ctx_sig : Region.Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ⟨s.gpr .x6, p.sigLen⟩
  ctx_scr : Region.Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ⟨s.gpr .x7, scratchLen⟩
  rnd_sig : Region.Disjoint ⟨s.gpr .x5, p.n⟩ ⟨s.gpr .x6, p.sigLen⟩
  rnd_scr : Region.Disjoint ⟨s.gpr .x5, p.n⟩ ⟨s.gpr .x7, scratchLen⟩
  sig_scr : Region.Disjoint ⟨s.gpr .x6, p.sigLen⟩ ⟨s.gpr .x7, scratchLen⟩
  stk_sk : (below s.sp 16).Disjoint ⟨s.gpr .x0, p.skLen⟩
  stk_msg : (below s.sp 16).Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  stk_ctx : (below s.sp 16).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  stk_rnd : (below s.sp 16).Disjoint ⟨s.gpr .x5, p.n⟩
  stk_sig : (below s.sp 16).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  stk_scr : (below s.sp 16).Disjoint ⟨s.gpr .x7, scratchLen⟩
  f_sk : (s.gpr .x0).toNat + p.skLen ≤ 2 ^ 64
  f_msg : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  f_ctx : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  f_rnd : (s.gpr .x5).toNat + p.n ≤ 2 ^ 64
  f_sig : (s.gpr .x6).toNat + p.sigLen ≤ 2 ^ 64
  f_scr : (s.gpr .x7).toNat + scratchLen ≤ 2 ^ 64

/-- What `sign` returns and writes, from the entry state `s`. -/
def sgOut (p : Params) (s : State) (m' : Mem) (r : BitVec 32) : Prop :=
  match formatMessage (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) with
  | none => r = 2 ∧ bytesAt m' (s.gpr .x6) p.sigLen = bytesAt s.mem (s.gpr .x6) p.sigLen
  | some M' => r = 1 ∧ bytesAt m' (s.gpr .x6) p.sigLen = signInternal p M' (bytesAt s.mem (s.gpr .x0) p.skLen)
      (bytesAt s.mem (s.gpr .x5) p.n)

def sgK (p : Params) : Contract isa where
  pre s := SG p s
  post s s' := sgOut p s s'.mem ((s'.gpr .x0).setWidth 32)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧
    s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp

/-- The formatted message `M′` of the entry state `σ`, for `ctx_len < 256`. -/
abbrev mPrime (σ : State) : List Byte :=
  [0, BitVec.ofNat 8 (σ.gpr .x4).toNat] ++ bytesAt σ.mem (σ.gpr .x3) (σ.gpr .x4).toNat ++
    bytesAt σ.mem (σ.gpr .x1) (σ.gpr .x2).toNat

/-- What the body does, from the entry state `σ`. -/
structure BodyPost (p : Params) (σ s' : State) : Prop where
  abi : abiPreserved σ s'
  ret : (s'.gpr .x0).setWidth 32 = 1
  sig : bytesAt s'.mem (σ.gpr .x6) p.sigLen =
    signInternal p (mPrime σ) (bytesAt σ.mem (σ.gpr .x0) p.skLen) (bytesAt σ.mem (σ.gpr .x5) p.n)

/-! ## The function -/

theorem bytesAt_length' (m : Mem) (a : Addr) (n : Nat) : (bytesAt m a n).length = n := by simp [bytesAt]

theorem fmt_some {ctx M : List Byte} (h : ctx.length ≤ 255) :
    formatMessage ctx M = some ([0, BitVec.ofNat 8 ctx.length] ++ ctx ++ M) := by
  simp only [formatMessage, show ¬ ctx.length > 255 by omega, ite_false]
  simp [toByte]

theorem fmt_none {ctx M : List Byte} (h : 255 < ctx.length) : formatMessage ctx M = none := by
  simp only [formatMessage, h, ite_true]

theorem lsr8_eq (x : BitVec 64) : (x >>> 8 != 0) = decide (256 ≤ x.toNat) := by
  have h : (x >>> 8).toNat = x.toNat / 256 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases hx : 256 ≤ x.toNat
  · have : x >>> 8 ≠ 0 := fun e => by rw [e] at h; simp at h; omega
    simp [hx]; exact this
  · have : x >>> 8 = 0 := BitVec.eq_of_toNat_eq (by rw [h]; simp; omega)
    simp [this, hx]

/-- `sign` from `sgK`'s precondition: its postcondition and the calling
convention, given the body's. -/
theorem sign_wp {p : Params} {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hbody : ∀ σ s, SG p σ → (σ.gpr .x4).toNat < 256 → MlKem.AArch64.Only [.x9] σ s →
      WP isa (Impl.SlhDsa.AArch64.Shake.signBody p f) s (BodyPost p σ))
    {σ : State} (hK : SG p σ) :
    WP isa (Impl.SlhDsa.AArch64.Shake.sign p f) σ fun s' => abiPreserved σ s' ∧ (sgK p).post σ s' := by
  unfold Impl.SlhDsa.AArch64.Shake.sign
  refine WP.seq (MlKem.AArch64.wp_lsr (by decide) fun s₁ o₁ e₁ => MlKem.AArch64.wp_nil ?_)
  have hl : (bytesAt σ.mem (σ.gpr .x3) (σ.gpr .x4).toNat).length = (σ.gpr .x4).toNat := bytesAt_length' _ _ _
  refine WP.ite _ (MlKem.AArch64.eval_nonzero s₁ .x9) (fun hc => ?_) (fun hc => ?_)
  · -- `ctx_len ≥ 256`
    rw [e₁, lsr8_eq, decide_eq_true_eq] at hc
    refine MlKem.AArch64.wp_movz fun s₂ o₂ e₂ => MlKem.AArch64.wp_nil ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · rw [o₂.get r (by revert r; decide), o₁.get r (by revert r; decide)]
    · rw [o₂.sp, o₁.sp]
    · rw [o₂.vcs r hr, o₁.vcs r hr]
    · show sgOut p σ s₂.mem ((s₂.gpr .x0).setWidth 32)
      simp only [sgOut]
      rw [fmt_none (by rw [hl]; omega), o₂.mem, o₁.mem, e₂]
      exact ⟨rfl, rfl⟩
  · -- `ctx_len < 256`: the body
    rw [e₁, lsr8_eq, decide_eq_false_iff_not] at hc
    refine WP.mono (hbody σ s₁ hK (by omega) o₁) fun s' h => ⟨h.abi, ?_⟩
    · show sgOut p σ s'.mem ((s'.gpr .x0).setWidth 32)
      simp only [sgOut]
      rw [fmt_some (by rw [hl]; omega), hl]
      refine ⟨h.ret, ?_⟩
      exact h.sig

end VG.Proof.SlhDsa.AArch64.Sign
