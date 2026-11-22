module

import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.LitAdx
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Lit
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.LitAdx
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Lit
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified

/-! ### `Ecdsa.Rfc6979.X86_64.P521`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86-64: P-521

P-521 as the proof's curve (`p521`): scalars of 9 words and 66 bytes, longer
than any hash function's output (`big`), the order `n` of 521 bits, so that
the signature drops 7 bits of a 66-byte digest, and `vg_ecdsa_p521_sign`,
proven correct (given the group law and the comb's tables) and constant time
against its contract (`coreK` at P-521's sizes, which is
`Proof.Ecdsa.X86_64.P521.signX86_64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- `coreK` at P-521's sizes is `Proof.Ecdsa.X86_64.P521.signX86_64` (by rewriting, as
deciding it would evaluate the tables' length). -/
theorem coreK_p521 : coreK Impl.Ecdsa.X86_64.p521 = Proof.Ecdsa.X86_64.P521.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.P521.p521_combConsts, Proof.Ecdsa.X86_64.P521.p521_constRegions,
    Abi.constsHeld, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, Proof.Ecdsa.X86_64.P521.signX86_64, Proof.Ecdsa.X86_64.P521.TblHeld]
  rfl

/-! ## The curve's blocks -/

theorem p521_blk : RfcT (cfgC Impl.Ecdsa.X86_64.p521 true 7) := by rfcT_decide


/-- P-521, with the group law `hL`, the comb's tables `hT` and the inversions'
soundness `hI`. -/
def p521 (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p521
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  big := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.X86_64.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.X86_64.P521.p521_sh
  coreN := "vg_ecdsa_p521_sign_k"
  coreC := Impl.Ecdsa.X86_64.signP521
  coreX := by rw [coreK_p521]; exact Proof.Ecdsa.X86_64.P521.sign_call_x86 hL hT hI
  coreCT := by rw [coreK_p521]; exact Proof.Ecdsa.X86_64.P521.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  blk := p521_blk

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

/-!
# Deterministic ECDSA on x86-64: P-521 with BMI2 and ADX

As `P521.lean`, with `vg_ecdsa_p521_sign_adx` (`p521x`, P-521 multiplying
modulo `p` with BMI2 and ADX), proven correct and constant time against the
same contract; `p521Of` is either.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- `coreK` is the same for `p521x` as for `p521`, the same curve. -/
theorem coreK_p521x : coreK Impl.Ecdsa.X86_64.p521x = Proof.Ecdsa.X86_64.P521.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.P521.p521x_combConsts, Proof.Ecdsa.X86_64.P521.p521_constRegions,
    Proof.Ecdsa.X86_64.P521.p521x_C,
    Abi.constsHeld, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, Proof.Ecdsa.X86_64.P521.signX86_64, Proof.Ecdsa.X86_64.P521.TblHeld]
  rfl

/-- P-521 with BMI2 and ADX, with the group law `hL`, the comb's tables `hT`
and the inversions' soundness `hI`. -/
def p521x (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p521x
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  big := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.X86_64.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.X86_64.P521.p521x_sh
  coreN := "vg_ecdsa_p521_sign_k" ++ "_adx"
  coreC := Impl.Ecdsa.X86_64.signP521Adx
  coreX := by rw [coreK_p521x]; exact Proof.Ecdsa.X86_64.P521.sign_call_x86_adx hL hT hI
  coreCT := by rw [coreK_p521x]; exact Proof.Ecdsa.X86_64.P521.sign_ct_adx
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  blk := by exact p521_blk

/-- P-521 with BMI2 and ADX (`adx`) or without. -/
def p521Of (adx : Bool) (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve :=
  bif adx then p521x hL hT hI else p521 hL hT hI


/-- `vg_ecdsa_p521_sign` (`_adx`, with BMI2 and ADX), with the tables of `vs`. -/
theorem p521T_verified (adx : Bool) (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (h : OK vs ∧ "VG_P521_COMB" ∉ Proof.HmacTable.X86_64.names vs) :
    Verified X86_64.target (signCodeT (p521Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Ecdsa.X86_64.p521.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p521) h.1 Proof.Ecdsa.X86_64.P521.satMem h.2
    (by rw [Proof.Ecdsa.X86_64.P521.p521W_length]; decide) Proof.Ecdsa.X86_64.P521.satMem_held (by decide) rfl
  cases adx
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat


/-! ## The function as emitted -/

theorem p521_stub (adx : Bool) (hL : Weierstrass.Law Spec.P521.curve) (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) (hI : Weierstrass.X86_64.InvSounds) : SignStub (p521Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p521.tries := by
  cases adx <;> (dsimp only [SignStub, cfgS, cfgT, p521Of, cond, p521, p521x]; exact ⟨by lit_decide, by lit_decide⟩)

/-- `vg_ecdsa_p521_sign`, with the tables of `vs`, as emitted (`Impl.Ecdsa.Rfc6979.X86_64.Fn.sign`), its
cleanup included, meets its contract in constant time and returns without secret residue. -/
theorem p521T_scrubbed (adx : Bool) (hL : Weierstrass.Law Spec.P521.curve) (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) (hI : Weierstrass.X86_64.InvSounds) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (h : OK vs ∧ "VG_P521_COMB" ∉ Proof.HmacTable.X86_64.names vs)
    (hu : ∀ w ∈ vs, Proof.HmacTable.X86_64.HmacUp w) :
    VerifiedScrubbed X86_64.target (Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (cfgT (p521Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs))
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Ecdsa.X86_64.p521.combConsts vs) 32 :=
  sign_scrubbed (api := Spec.Ecdsa.Rfc6979.Curves.p521SignApi)
    { tables := [("hmac", Proof.HmacTable.X86_64.tables vs)]
      code := signCodeT (p521Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs
      verified := p521T_verified adx hL hT hI vs h
      spSafe := signCode_sp _ _ _ }
    (signOut _ Impl.Ecdsa.X86_64.p521.combConsts _ _) rfl rfl hu (p521_stub adx hL hT hI)

theorem p521T_spSafe (adx : Bool) (hL : Weierstrass.Law Spec.P521.curve) (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) (hI : Weierstrass.X86_64.InvSounds) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) :
    (Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (cfgT (p521Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs)).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (signCode_sp _ _ _)

end VG.Proof.Ecdsa.Rfc6979.X86_64
