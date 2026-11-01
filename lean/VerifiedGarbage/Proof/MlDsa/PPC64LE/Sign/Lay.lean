module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Lay
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sign.Sign
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.OmegaAll

/-!
# ML-DSA signing on PPC64LE: its parameters, precondition and buffers

As key generation's and verification's (`KeyGen/Lay.lean`, `Verify/Lay.lean`):
the facts about the parameter sets the proof uses (`SFacts`); the
precondition of the shared contract, evaluated (`SPre`, `spre_of`); and the
buffers of the function. `rnd` is read only by the hash of `ρ″`, and `sig`
written only at the end, so they take turns in the same buffer (4, in
`r28`): first `scratch`, the stack, `sk`, `mu` and `rnd` (`slay1`), of which
only `scratch` and the stack are written, and the inputs, only read, may
overlap each other; then the same with `sig` for `rnd` (`slay2`), written
too. `ssep` proves the facts about the offsets of pointers into them by
`omega`, for any parameter set.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn inB reg)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87 bitlen)
open VG.Proof.MlDsa (gamma2s simpleBitPackBounds ballParams hintParams bitPackParams)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure SFacts (p : Params) : Prop where
  k : 4 ≤ p.k ∧ p.k ≤ 8
  l : 4 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  eta : (p.η = 2 ∧ sLen p = 96) ∨ (p.η = 4 ∧ sLen p = 128)
  sk : p.skLen = 128 + sLen p * (p.ℓ + p.k) + 416 * p.k
  sig : p.sigLen = sigH p + (p.ω + p.k)
  ct : (cLen p = 32 ∨ cLen p = 48 ∨ cLen p = 64)
  lz : (zLen p = 576 ∨ zLen p = 640)
  om : 55 ≤ p.ω ∧ p.ω ≤ 80
  w1 : p.k * w1Len p ≤ 1024 ∧ 0 < p.k * w1Len p
  w1l : w1Len p = 128 ∨ (w1Len p = 192 ∧ p.k ≤ 5)
  g1 : p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19
  g2 : p.γ₂ ∈ gamma2s
  sbp : w1Max p ∈ simpleBitPackBounds
  bp : (cLen p, p.τ) ∈ ballParams
  tau : p.τ < 2 ^ 31
  hip : (p.ω, p.k) ∈ hintParams
  zbp : (p.γ₁ - 1, p.γ₁) ∈ bitPackParams
  zl : zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)

theorem sfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : SFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem SFacts.scr {p : Params} (hF : SFacts p) :
    5120 + 1024 * (5 + 4 * p.k + 3 * p.ℓ + p.k * p.ℓ) ≤ scrLen p ∧ 32768 ≤ scrLen p ∧ scrLen p < 2 ^ 31 := by
  have := hF.k; have := hF.l; have := hF.kl
  simp only [scrLen, scratchWords]; omega

theorem SFacts.lens {p : Params} (hF : SFacts p) : p.skLen < 32768 ∧ p.sigLen < 32768 := by
  have := hF.k; have := hF.l; have := hF.om
  refine ⟨?_, ?_⟩
  · rw [hF.sk]; rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> omega
  · rw [hF.sig, sigH]; rcases hF.ct with e | e | e <;> rcases hF.lz with e' | e' <;> rw [e, e'] <;> omega

/-- The slot of `Â[0, 0]`; entry `e = ℓi + j` is in slot `aBase + e`. -/
abbrev aBase (p : Params) : Nat := 5 + 4 * p.k + 3 * p.ℓ

theorem sptr_ok {r : Reg} (hr : KeyGen.baseReg r = true) {o : Nat} (h : o < 2 ^ 31) :
    KeyGen.argOk (.ptr (r, o)) = true := by
  simp only [KeyGen.argOk, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hr, h⟩

/-! ## The precondition -/

section
variable (σ : State)

abbrev sSk : Addr := σ.gpr .r3
abbrev sMu : Addr := σ.gpr .r4
abbrev sRnd : Addr := σ.gpr .r5
abbrev sSig : Addr := σ.gpr .r6
abbrev sScr : Addr := σ.gpr .r7

end

/-- The precondition of `signContract` with `STK` bytes of stack. -/
structure SPre (p : Params) (STK : Nat) (σ : State) : Prop where
  stk : STK ≤ σ.sp.toNat
  rd : σ.rd = [reg (sSk σ) p.skLen, reg (sMu σ) 64, reg (sRnd σ) 32]
  wr : σ.wr = [reg (sSig σ) p.sigLen, reg (sScr σ) (scrLen p)]
  d_kg : (reg (sSk σ) p.skLen).Disjoint (reg (sSig σ) p.sigLen)
  d_kc : (reg (sSk σ) p.skLen).Disjoint (reg (sScr σ) (scrLen p))
  d_mg : (reg (sMu σ) 64).Disjoint (reg (sSig σ) p.sigLen)
  d_mc : (reg (sMu σ) 64).Disjoint (reg (sScr σ) (scrLen p))
  d_rg : (reg (sRnd σ) 32).Disjoint (reg (sSig σ) p.sigLen)
  d_rc : (reg (sRnd σ) 32).Disjoint (reg (sScr σ) (scrLen p))
  d_gc : (reg (sSig σ) p.sigLen).Disjoint (reg (sScr σ) (scrLen p))
  b_k : (below σ.sp STK).Disjoint (reg (sSk σ) p.skLen)
  b_m : (below σ.sp STK).Disjoint (reg (sMu σ) 64)
  b_r : (below σ.sp STK).Disjoint (reg (sRnd σ) 32)
  b_g : (below σ.sp STK).Disjoint (reg (sSig σ) p.sigLen)
  b_c : (below σ.sp STK).Disjoint (reg (sScr σ) (scrLen p))
  f_k : (sSk σ).toNat + p.skLen ≤ 2 ^ 64
  f_m : (sMu σ).toNat + 64 ≤ 2 ^ 64
  f_r : (sRnd σ).toNat + 32 ≤ 2 ^ 64
  f_g : (sSig σ).toNat + p.sigLen ≤ 2 ^ 64
  f_c : (sScr σ).toNat + scrLen p ≤ 2 ^ 64

theorem spre_of {p : Params} {n : Nat} {σ : State} (h : (Spec.MlDsa.signContract p PPC64LE.abi (n + 1)).pre σ) :
    SPre p (n + 1) σ := by
  sig_pre [Spec.MlDsa.signContract, Spec.MlDsa.signSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

/-! ## The buffers -/

/-- `scratch` (0), the stack (1), `sk` (2), `mu` (3) and `rnd` (4). -/
def slay1 (p : Params) (STK : Nat) (σ : State) : Lay :=
  ⟨fun i => [sScr σ, σ.sp - BitVec.ofNat 64 STK, sSk σ, sMu σ, sRnd σ].getD i 0,
    [scrLen p, STK, p.skLen, 64, 32]⟩

/-- `scratch` (0), the stack (1), `sk` (2), `mu` (3) and `sig` (4). -/
def slay2 (p : Params) (STK : Nat) (σ : State) : Lay :=
  ⟨fun i => [sScr σ, σ.sp - BitVec.ofNat 64 STK, sSk σ, sMu σ, sSig σ].getD i 0,
    [scrLen p, STK, p.skLen, 64, p.sigLen]⟩

theorem slay1_sizes (p : Params) (STK : Nat) (σ : State) :
    (slay1 p STK σ).sizes = [scrLen p, STK, p.skLen, 64, 32] := rfl

theorem slay2_sizes (p : Params) (STK : Nat) (σ : State) :
    (slay2 p STK σ).sizes = [scrLen p, STK, p.skLen, 64, p.sigLen] := rfl

theorem slay1_size0 (p : Params) (STK : Nat) (σ : State) : (slay1 p STK σ).size 0 = scrLen p := rfl
theorem slay2_size0 (p : Params) (STK : Nat) (σ : State) : (slay2 p STK σ).size 0 = scrLen p := rfl

/-- The buffers written before the signature: `scratch` and the stack. -/
abbrev sWb1 : List Nat := [0, 1]
/-- The buffers written at the end: `scratch`, the stack and `sig`. -/
abbrev sWb2 : List Nat := [0, 1, 4]

/-- Closes a goal that two buffers are disjoint from the precondition `hp`. -/
macro "sdisj " hp:term:max es:term:max : tactic => `(tactic| first
  | exact ($hp).d_kg | exact ($hp).d_kg.symm | exact ($hp).d_kc | exact ($hp).d_kc.symm
  | exact ($hp).d_mg | exact ($hp).d_mg.symm | exact ($hp).d_mc | exact ($hp).d_mc.symm
  | exact ($hp).d_rg | exact ($hp).d_rg.symm | exact ($hp).d_rc | exact ($hp).d_rc.symm
  | exact ($hp).d_gc | exact ($hp).d_gc.symm
  | (rw [$es:term]; first
      | exact ($hp).b_k | exact ($hp).b_k.symm | exact ($hp).b_m | exact ($hp).b_m.symm
      | exact ($hp).b_r | exact ($hp).b_r.symm | exact ($hp).b_g | exact ($hp).b_g.symm
      | exact ($hp).b_c | exact ($hp).b_c.symm))

theorem stk_fit {p : Params} {STK : Nat} {σ : State} (hp : SPre p STK σ) :
    (σ.sp - BitVec.ofNat 64 STK).toNat + STK ≤ 2 ^ 64 := by
  have := hp.stk; have := σ.sp.isLt; bv_omega

theorem slay1_ok {p : Params} {STK : Nat} {σ : State} (hp : SPre p STK σ) : OkW (slay1 p STK σ) sWb1 := by
  have es : (⟨σ.sp - BitVec.ofNat 64 STK, STK⟩ : Region) = below σ.sp STK := rfl
  refine ⟨fun i hi => ?_, fun i hi j hj hij hw => ?_⟩
  · simp only [slay1, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    exacts [hp.f_c, stk_fit hp, hp.f_k, hp.f_m, hp.f_r]
  · simp only [slay1, List.length_cons, List.length_nil] at hi hj
    simp only [sWb1, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Lay.buf, slay1, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | sdisj hp es

theorem slay2_ok {p : Params} {STK : Nat} {σ : State} (hp : SPre p STK σ) : OkW (slay2 p STK σ) sWb2 := by
  have es : (⟨σ.sp - BitVec.ofNat 64 STK, STK⟩ : Region) = below σ.sp STK := rfl
  refine ⟨fun i hi => ?_, fun i hi j hj hij hw => ?_⟩
  · simp only [slay2, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    exacts [hp.f_c, stk_fit hp, hp.f_k, hp.f_m, hp.f_g]
  · simp only [slay2, List.length_cons, List.length_nil] at hi hj
    simp only [sWb2, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Lay.buf, slay2, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | sdisj hp es

/-- Decides a fact about offsets in the buffers, for any parameter set with
the facts `hF`. -/
syntax "ssep " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ssep $hF) => `(tactic| ssep $hF [])
  | `(tactic| ssep $hF [$ls,*]) => `(tactic| plain_simp_names (
                       have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).lens
                       have := ($hF).eta; have := ($hF).sk; have := ($hF).sig; have := ($hF).ct; have := ($hF).lz
                       have := ($hF).om; have := ($hF).w1; have := ($hF).w1l
                       try dsimp only [$ls,*]
                       try dsimp only [sepB, sepAll, inB, tri, ix, sc, pS, cP, t1P, t2P, t3P, t4P, hP, yP, yhP, wP,
                         s1P, s2P, t0P, aP, oP, oSIG, oRS, oMS, oCT, oW1, oPS, skS1, skS2, skT0, sigZ, sigH, aBase]
                       set_option linter.unusedSimpArgs false in
                       simp (config := { decide := true }) only [sepB, sepAll, inB, slay1_sizes, slay2_sizes,
                         List.getD_cons_zero, List.getD_cons_succ, List.length_cons, List.length_nil, List.all_cons,
                         List.all_nil, tri, ix, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
                         ne_eq, Bool.and_true, Bool.true_and, true_and, and_true, true_or, or_true, Nat.zero_add,
                         sc, pS, cP, t1P, t2P, t3P, t4P, hP, yP, yhP, wP, s1P, s2P, t0P, aP, oP, oSIG, oRS, oMS, oCT,
                         oW1, oPS, skS1, skS2, skT0, sigZ, sigH, aBase, false_or, or_false, decide_eq_true_iff, $ls,*]
                       focus (and_intros; all_omega_arith)))

/-- Proves that an offset into the buffers is below `2³¹`, for any parameter
set with the facts `hF`. -/
syntax "slt " term:max : tactic
macro_rules
  | `(tactic| slt $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).lens; have := ($hF).eta
      have := ($hF).sk; have := ($hF).sig; have := ($hF).ct; have := ($hF).lz; have := ($hF).om
      have := ($hF).w1; have := ($hF).w1l
      try dsimp only [VG.Impl.MlDsa.PPC64LE.Sign.oP, VG.Impl.MlDsa.PPC64LE.Sign.oSIG,
        VG.Impl.MlDsa.PPC64LE.Sign.oRS, VG.Impl.MlDsa.PPC64LE.Sign.oMS, VG.Impl.MlDsa.PPC64LE.Sign.oCT,
        VG.Impl.MlDsa.PPC64LE.Sign.oW1, VG.Impl.MlDsa.PPC64LE.Sign.oPS, VG.Impl.MlDsa.PPC64LE.Sign.skS1,
        VG.Impl.MlDsa.PPC64LE.Sign.skS2, VG.Impl.MlDsa.PPC64LE.Sign.skT0, VG.Impl.MlDsa.PPC64LE.Sign.sigZ,
        VG.Impl.MlDsa.PPC64LE.Sign.sigH, VG.Proof.MlDsa.PPC64LE.Sign.aBase]
      omega))

end VG.Proof.MlDsa.PPC64LE.Sign
