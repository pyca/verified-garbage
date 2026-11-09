module

public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Prim
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
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Mask32
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
  rw [ite_eq_right_iff.mpr fun h => absurd h (show a ≠ 3 by omega)]
  exact Bool.or_eq_true_iff.mpr (.inr rfl)

theorem sepSR {p : Params} {a o₁ l₁ o₂ l₂ : Nat} (ha : a < 3 ∨ a = 4) : (YV p).sep ⟨3, o₁, l₁⟩ ⟨a, o₂, l₂⟩ = true := by
  unfold Lay.sep
  rw [ite_eq_right_iff.mpr fun h => absurd h (show 3 ≠ a by omega)]
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
    rw [YV_n] at hi; omega
  have e3 : (scratchWords p - 128 * p.k) * 8 = scrLenV p := by simp only [scrLenV]; omega
  rw [e3] at h4 d0s d1s d2s ds4 dsg r3 s3 f3
  refine ⟨⟨h1, by rw [YV_stk]; omega, by rw [YV_n]; omega, ?_, ?_, ?_, ?_, ?_,
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
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    exacts [e₃, e₄, e₅, e₆, e₇]
  · simp only [lkV, vPk, vMu, vSig, addr0]
    exact Proof.MlDsa.KeyGen.leakBytes_inj e₂

end VG.Proof.MlDsa.X86.Verify
