module

import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Lit
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.X86_64.InstrBits

/-!
# Deterministic ECDSA on x86-64: brainpoolP512r1

brainpoolp512r1 as the proof's curve (`brainpoolp512r1`): scalars of 64 bytes in 8 words, the order `n` of exactly 512 bits with `2^512 < 2 n`, and `vg_ecdsa_brainpoolp512r1_sign`,
proven correct (given the group law and the inversions'
soundness) and constant time against its contract (`coreK` at brainpoolP512r1's sizes,
which is `Proof.Ecdsa.X86_64.BrainpoolP512r1.signX86_64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem coreK_brainpoolp512r1 : coreK Impl.Ecdsa.X86_64.brainpoolp512r1S = Proof.Ecdsa.X86_64.BrainpoolP512r1.signX86_64 :=
  rfl

/-! ## The comb's tables -/

/-- The words of the comb's tables (`VG_BRAINPOOLP512R1_COMB`). -/
abbrev brainpoolp512r1W : List (BitVec 64) :=
  Impl.Ecdsa.X86_64.brainpoolp512r1S.combWords Impl.Ecdsa.X86_64.brainpoolp512r1Comb

theorem brainpoolp512r1_comb7_len : Impl.BrainpoolP512r1.comb7.length = 74 := by decide

theorem brainpoolp512r1_comb7_lenH : ∀ j < 74, (Impl.BrainpoolP512r1.comb7.getD j []).length = 64 := by
  decide

/-- `brainpoolp512r1W` has `74 · 64 · 16` words. -/
theorem brainpoolp512r1W_length : brainpoolp512r1W.length = 75776 :=
  (Proof.Weierstrass.tcombWords_length (n := 8) (R := Impl.Ecdsa.X86_64.brainpoolp512r1S.R) (p := Spec.BrainpoolP512r1.curve.p)
    (H := 64) (tbl := Impl.BrainpoolP512r1.comb7) brainpoolp512r1_comb7_len brainpoolp512r1_comb7_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def brainpoolp512r1SatMem : Mem := constMem 0x100000 brainpoolp512r1W

theorem brainpoolp512r1SatMem_held : ∀ i < brainpoolp512r1W.length,
    brainpoolp512r1SatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = brainpoolp512r1W.getD i 0 := by
  unfold brainpoolp512r1SatMem
  exact constMem_held _ _ (by rw [brainpoolp512r1W_length]; omega_using [])

/-! ## The curve's blocks -/

theorem brainpoolp512r1_blk : RfcT (cfgC Impl.Ecdsa.X86_64.brainpoolp512r1S false 0) := by rfcT_decide


/-- The tests of the instructions of `sign_k`'s code: one walk of it, and one
match for each instruction (`Proof/Framework/X86_64/InstrBits.lean`). -/
theorem brainpoolp512r1_bits :
    Impl.Ecdsa.X86_64.signBrainpoolP512r1.allInstrs (hasBits (bMx + bSp + bNs)) = true := by
  lit_decide

/-- brainpoolp512r1, with the group law `hL` and the inversions'
soundness `hI`. -/
def brainpoolp512r1 (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.brainpoolp512r1S
  inst := Spec.Ecdsa.BrainpoolP512r1.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, Proof.Ecdsa.X86_64.BrainpoolP512r1.brainpoolp512r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.BrainpoolP512r1.brainpoolp512r1S_sh
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  coreC := Impl.Ecdsa.X86_64.signBrainpoolP512r1
  coreX := by rw [coreK_brainpoolp512r1]; exact Proof.Ecdsa.X86_64.BrainpoolP512r1.sign_call_x86 hL hI
  coreCT := by rw [coreK_brainpoolp512r1]; exact Proof.Ecdsa.X86_64.BrainpoolP512r1.sign_ct
  coreNs := Code.noRsp_of_bits rfl brainpoolp512r1_bits
  coreSp := Code.sp_of_bits rfl brainpoolp512r1_bits
  coreMx := Code.noMx_of_bits rfl brainpoolp512r1_bits
  coreD := by lit_decide
  blk := brainpoolp512r1_blk


/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`. -/
theorem brainpoolp512r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve)
    (hI : Weierstrass.X86_64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash)
    (h : OK vs ∧ "VG_BRAINPOOLP512R1_COMB" ∉ Proof.HmacTable.X86_64.names vs) :
    Verified X86_64.target (signCodeT (brainpoolp512r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 Impl.Ecdsa.X86_64.brainpoolp512r1S.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1) h.1 brainpoolp512r1SatMem h.2
    (by rw [brainpoolp512r1W_length]; decide) brainpoolp512r1SatMem_held (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat


/-! ## The function as emitted -/

theorem brainpoolp512r1_stub (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.X86_64.InvSounds) : SignStub (brainpoolp512r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries := by
  dsimp only [SignStub, cfgS, cfgT, brainpoolp512r1]; exact ⟨by lit_decide, by lit_decide⟩

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`, as emitted (`Impl.Ecdsa.Rfc6979.X86_64.Fn.sign`), its
cleanup included, meets its contract in constant time and returns without secret residue. -/
theorem brainpoolp512r1T_scrubbed (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.X86_64.InvSounds) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (h : OK vs ∧ "VG_BRAINPOOLP512R1_COMB" ∉ Proof.HmacTable.X86_64.names vs)
    (hu : ∀ w ∈ vs, Proof.HmacTable.X86_64.HmacUp w) :
    VerifiedScrubbed X86_64.target (Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (cfgT (brainpoolp512r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs))
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 Impl.Ecdsa.X86_64.brainpoolp512r1S.combConsts vs) 32 :=
  sign_scrubbed (api := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi)
    { tables := [("hmac", Proof.HmacTable.X86_64.tables vs)]
      code := signCodeT (brainpoolp512r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs
      verified := brainpoolp512r1T_verified hL hI vs h
      spSafe := signCode_sp _ _ _ }
    (signOut _ Impl.Ecdsa.X86_64.brainpoolp512r1S.combConsts _ _) rfl rfl hu (brainpoolp512r1_stub hL hI)

theorem brainpoolp512r1T_spSafe (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.X86_64.InvSounds) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) :
    (Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (cfgT (brainpoolp512r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs)).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (signCode_sp _ _ _)

end VG.Proof.Ecdsa.Rfc6979.X86_64
