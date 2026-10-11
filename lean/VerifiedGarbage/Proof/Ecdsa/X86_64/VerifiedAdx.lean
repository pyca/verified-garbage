import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

/-!
# ECDSA over P-256 on x86-64 with BMI2 and ADX: `Verified`

`p256x` is `p256` multiplying with BMI2 and ADX (`Mod.adx`), which the proof
of `sign_ok` covers as it covers any multiplication (`Proof/Mont/X86_64/Adx.lean`):
the same curve, so the same facts (`p256x_ok`, from `p256_ok` but for the
inversions' constants, decided again) and the same precondition.
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-- How P-256's field elements and scalars are multiplied, for the notes of
its functions: with BMI2 and ADX (`adx`) or not. -/
def mulNote (adx : Bool) : String :=
  "multiplied by word-by-word Montgomery multiplication (CIOS; as `p ≡ -1 (mod 2⁶⁴)`, each \
  reduction step modulo `p` adds `t₀ (p + 1) / 2⁶⁴` to the words above the low word `t₀`, two \
  products" ++ (if adx then "; each row of products by BMI2's `mulx`, its low halves added \
  through OF (`adox`) and its high halves through CF (`adcx`), two carry chains that do not wait \
  for each other" else "") ++ ") with a final conditional subtraction"

theorem p256x_ok (hI : InvSounds) : CfgOk p256x :=
  have h := p256_ok hI
  { h with
    comb := fun d h => by cases h; exact ⟨by decide, by decide, by decide⟩
    inv := fun _ => ⟨by decide, @hI _ p256.C.p_ne_zero Proof.P256.p_prime,
      InvOk.ofMod (by decide +kernel) (by decide)⟩
    inv_n := fun _ _ => ⟨@hI _ p256.C.n_ne_zero Proof.P256.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩ }

theorem sign_x86_adx (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP256Adx s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  sign_x86_of (p256x_ok hI) hL (p256_tbls hL hT) (fun h => absurd h (by decide)) (fun _ h => { pre_of h with }) (fun _ _ => id) rfl
    (by lit_decide) (by lit_decide) (by lit_decide) s hs

/-- `signP256Adx` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def signP256AdxErased : Prog isa := Code.erase signP256Adx

materialize_shared signP256AdxErased

theorem sign_ct_adx : ConstantTime isa signX86_64.pre signX86_64.pub signP256Adx :=
  VG.Taint.constantTime_mapBlocks (c' := signP256AdxErased) (taintSym_eraseInv ["VG_P256_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) rfl
    (fun _ _ _ _ ⟨_, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    rfl (by taint_decide)

theorem sign_verified_adx (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : InvSounds) :
    Verified X86_64.target signP256Adx
      (Spec.Ecdsa.P256.inst.signContract (X86_64.abi.withConsts p256.combConsts)) :=
  Verified.of_correct (sign_x86_adx hL hT hI) sign_ct_adx implies

end VG.Proof.Ecdsa.X86_64
