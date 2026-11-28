module

-- separate module: the contract and the length checks, which the body's proofs do not change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignTop
public import VerifiedGarbage.Proof.SlhDsa.VerifyTopSpec
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Verify
import VerifiedGarbage.Proof.SlhDsa.AArch64.TopShared
import VerifiedGarbage.Proof.SlhDsa.AArch64.KeyGenPro
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `verify`, correct

`verify(pk = x0, msg = x1, msg_len = x2, ctx = x3, ctx_len = x4, sig = x5,
sig_len = x6, scratch = x7)` (`Impl.SlhDsa.AArch64.Verify.verify`):
`(ctx_len ≫ 8) ∨ (sig_len - sigLen)`; if it is not zero, 0; otherwise the
body, which returns 1 if the root the signature gives is `PK.root` and 0 if
not (`BodyPost`, `vOk`): `verify_wp`, against `vgK`, the contract spelled out
a fact at a time. The values of a run are functions of its entry state `σ`
(`PKs`, `PKr`, `Rv`, `Dv`, `Tv`, `Iv`, `sigF`, `pkF`, `sigH`), and `vOk σ`
is `slh_verify` of its inputs (`verify_eq`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.VerifyTop

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.SlhDsa (layerTree forsAdrs)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar htFold)
open VG.Proof.SlhDsa.AArch64.Sign (mPrime)

/-! ## The contract, as the proof uses it -/

/-- `verifyContract`'s precondition, a fact at a time. -/
structure VG (p : Params) (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .x0, p.pkLen⟩, ⟨s.gpr .x1, (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
    ⟨s.gpr .x5, (s.gpr .x6).toNat⟩]
  wr : s.wr = [⟨s.gpr .x7, scratchLen⟩]
  pk_scr : Region.Disjoint ⟨s.gpr .x0, p.pkLen⟩ ⟨s.gpr .x7, scratchLen⟩
  msg_scr : Region.Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩ ⟨s.gpr .x7, scratchLen⟩
  ctx_scr : Region.Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ⟨s.gpr .x7, scratchLen⟩
  sig_scr : Region.Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩ ⟨s.gpr .x7, scratchLen⟩
  stk_pk : (below s.sp 16).Disjoint ⟨s.gpr .x0, p.pkLen⟩
  stk_msg : (below s.sp 16).Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  stk_ctx : (below s.sp 16).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  stk_sig : (below s.sp 16).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  stk_scr : (below s.sp 16).Disjoint ⟨s.gpr .x7, scratchLen⟩
  f_pk : (s.gpr .x0).toNat + p.pkLen ≤ 2 ^ 64
  f_msg : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  f_ctx : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  f_sig : (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64
  f_scr : (s.gpr .x7).toNat + scratchLen ≤ 2 ^ 64

/-- The inputs of the entry state `s`. -/
abbrev pkI (p : Params) (s : State) : List Byte := bytesAt s.mem (s.gpr .x0) p.pkLen
abbrev msgI (s : State) : List Byte := bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat
abbrev ctxI (s : State) : List Byte := bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat
abbrev sigI (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat

def vgK (p : Params) : Contract isa where
  pre s := VG p s
  post s s' := (s'.gpr .x0).setWidth 32 = if verify p (msgI s) (sigI s) (ctxI s) (pkI p s) then 1 else 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧
    s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧
    pkI p s₁ = pkI p s₂ ∧ msgI s₁ = msgI s₂ ∧ ctxI s₁ = ctxI s₂ ∧ sigI s₁ = sigI s₂

/-! ## The values of a run, from its entry state `σ` -/

/-- `PK.seed`, `PK.root`, `R`, the digest and its indices. -/
abbrev PKs (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x0) p.n
abbrev PKr (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x0 + BitVec.ofNat 64 p.n) p.n
abbrev Rv (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x5) p.n
abbrev Dv (p : Params) (σ : State) : List Byte :=
  Spec.Sha3.shake256 (Rv p σ ++ PKs p σ ++ PKr p σ ++ mPrime σ) p.m
abbrev Tv (p : Params) (σ : State) : Nat := (splitDigest p (Dv p σ)).2.1
abbrev Iv (p : Params) (σ : State) : Nat := (splitDigest p (Dv p σ)).2.2

/-- FORS's signature and the public key it gives; the hypertree's signature. -/
abbrev sigF (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x5 + BitVec.ofNat 64 p.n) p.forsSigLen
abbrev pkF (p : Params) (σ : State) : List Byte :=
  forsPkFromSig p (sigF p σ) (splitDigest p (Dv p σ)).1 (PKs p σ) (forsAdrs (layerTree 0 (Tv p σ)) (Iv p σ))
abbrev sigH (p : Params) (σ : State) : List Byte :=
  bytesAt σ.mem (σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen)) (p.d * p.xmssSigLen)

/-- The root, tree and leaf index before layer `j`. -/
abbrev htV (p : Params) (σ : State) (j : Nat) : List Byte × Nat × Nat :=
  htFold p (pkF p σ) (sigH p σ) (PKs p σ) (Tv p σ) (Iv p σ) j

/-- Whether the signature is valid, as the code computes it. -/
def vOk (p : Params) (σ : State) : Bool := (htV p σ p.d).1 == PKr p σ

/-- What the body does, from the entry state `σ`. -/
structure BodyPost (p : Params) (σ s' : State) : Prop where
  abi : abiPreserved σ s'
  ret : (s'.gpr .x0).setWidth 32 = if vOk p σ then 1 else 0

/-! ## `slh_verify` as the code computes it -/

theorem bytesAt_len (m : Mem) (a : Addr) (k : Nat) : (bytesAt m a k).length = k := by simp [bytesAt]

theorem bytesAt_take (m : Mem) (a : Addr) {k L : Nat} (h : k ≤ L) : (bytesAt m a L).take k = bytesAt m a k := by
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro i h₁ h₂
  simp [bytesAt]

theorem bytesAt_drop (m : Mem) (a : Addr) {k L : Nat} (h : k ≤ L) :
    (bytesAt m a L).drop k = bytesAt m (a + BitVec.ofNat 64 k) (L - k) := by
  have e := KeyGen.bytesAt_add' m a k (L - k)
  rw [Nat.add_sub_cancel' h] at e
  rw [e, List.drop_left' (bytesAt_len _ _ _)]

theorem verify_eq {p : Params} (hp : VPar p) {σ : State} (h4 : (σ.gpr .x4).toNat < 256)
    (hsl : (σ.gpr .x6).toNat = p.sigLen) :
    verify p (msgI σ) (sigI σ) (ctxI σ) (pkI p σ) = vOk p σ := by
  have hsg := hp.sigLen
  have hpk := hp.pk
  unfold verify
  rw [Sign.fmt_some (by rw [bytesAt_len]; omega)]
  dsimp only
  rw [bytesAt_len, X86_64.VerifyTop.verifyInternal_eq hp _ _ _ (by rw [bytesAt_len, hsl])]
  dsimp only [sigI]
  rw [hsl, bytesAt_take _ _ (show p.n ≤ p.sigLen by omega), bytesAt_drop _ _ (show p.n ≤ p.sigLen by omega),
    bytesAt_take _ _ (show p.forsSigLen ≤ p.sigLen - p.n by omega),
    bytesAt_drop _ _ (show p.n + p.forsSigLen ≤ p.sigLen by omega),
    show p.sigLen - (p.n + p.forsSigLen) = p.d * p.xmssSigLen by omega]
  dsimp only [pkI]
  rw [hpk, KeyGen.chunk_bytesAt _ _ (show 0 < 2 by decide), KeyGen.chunk_bytesAt _ _ (show 1 < 2 by decide),
    Nat.mul_zero, Nat.mul_one, BitVec.add_zero]
  rfl

/-! ## The function -/

theorem or_eq_zero (a b : BitVec 64) : (a ||| b != 0) = (a != 0 || b != 0) := by
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq]
  by_cases ha : a = 0#64 <;> simp [ha]

theorem sub_ne_zero (a b : BitVec 64) : (a - b != 0) = decide (a ≠ b) := by
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · exact fun h e => h (by rw [e, BitVec.sub_self]; rfl)
  · intro h e
    have := BitVec.sub_add_cancel a b
    rw [e] at this
    exact h (by simpa using this.symm)

/-- `verify` from `vgK`'s precondition: its postcondition and the calling
convention, given the body's. -/
theorem verify_wp {p : Params} (hp : VPar p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    {g : Impl.SlhDsa.AArch64.Verify.VFns}
    (hbody : ∀ σ s, VG p σ → (σ.gpr .x4).toNat < 256 → (σ.gpr .x6).toNat = p.sigLen →
      MlKem.AArch64.Only [.x9, .x10] σ s →
      WP isa (Impl.SlhDsa.AArch64.Verify.verifyBody p f g) s (BodyPost p σ))
    {σ : State} (hK : VG p σ) :
    WP isa (Impl.SlhDsa.AArch64.Verify.verify p f g) σ fun s' => abiPreserved σ s' ∧ (vgK p).post σ s' := by
  have hsl := hp.sigLt
  unfold Impl.SlhDsa.AArch64.Verify.verify
  simp only [List.cons_append, List.append_assoc]
  refine WP.seq (MlKem.AArch64.wp_lsr (by decide) fun s₁ o₁ e₁ => movV_ok (by omega) fun s₂ o₂ e₂ =>
    MlKem.AArch64.wp_sub fun s₃ o₃ e₃ => MlKem.AArch64.wp_orr fun s₄ o₄ e₄ => MlKem.AArch64.wp_nil ?_)
  have o : MlKem.AArch64.Only [.x9, .x10] σ s₄ := (((o₁.trans o₂).trans o₃).trans o₄).mono (by decide)
  have e : s₄.gpr .x9 = (σ.gpr .x4 >>> 8) ||| (σ.gpr .x6 - BitVec.ofNat 64 p.sigLen) := by
    rw [e₄, o₃.get .x9, o₂.get .x9, e₁, e₃, e₂, o₂.get .x6, o₁.get .x6]
  have hl : (bytesAt σ.mem (σ.gpr .x3) (σ.gpr .x4).toNat).length = (σ.gpr .x4).toNat := bytesAt_len _ _ _
  refine WP.ite _ (MlKem.AArch64.eval_nonzero _ .x9) (fun hc => ?_) (fun hc => ?_)
  · -- `ctx_len ≥ 256` or `sig_len ≠ sigLen`: 0
    rw [e, or_eq_zero, Sign.lsr8_eq, sub_ne_zero] at hc
    refine MlKem.AArch64.wp_movz fun s₅ o₅ e₅ => MlKem.AArch64.wp_nil ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · rw [o₅.get r (by revert r; decide), o.get r (by revert r; decide)]
    · rw [o₅.sp, o.sp]
    · rw [o₅.vcs r hr, o.vcs r hr]
    · show (s₅.gpr .x0).setWidth 32 = _
      have hv : verify p (msgI σ) (sigI σ) (ctxI σ) (pkI p σ) = false := by
        by_cases h4 : (σ.gpr .x4).toNat < 256
        · have h6 : σ.gpr .x6 ≠ BitVec.ofNat 64 p.sigLen := by
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hc; exact hc.resolve_left (by omega)
          have h6' : (σ.gpr .x6).toNat ≠ p.sigLen := fun h => h6 (by
            apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
          unfold verify
          rw [Sign.fmt_some (by rw [hl]; omega)]
          simp only [verifyInternal, sigI, bytesAt_len, ne_eq, h6', not_false_eq_true, ite_true]
        · unfold verify
          rw [Sign.fmt_none (by rw [hl]; omega)]
      rw [hv, e₅]; rfl
  · rw [e, or_eq_zero, Sign.lsr8_eq, sub_ne_zero] at hc
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Decidable.not_not] at hc
    have h6 : (σ.gpr .x6).toNat = p.sigLen := by rw [hc.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine WP.mono (hbody σ s₄ hK (by omega) h6 o) fun s' h => ⟨h.abi, ?_⟩
    show (s'.gpr .x0).setWidth 32 = _
    rw [verify_eq hp (by omega) h6]; exact h.ret

end VG.Proof.SlhDsa.AArch64.VerifyTop
