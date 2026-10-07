import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx

/-!
# ECDSA over P-384 on x86-64 with BMI2 and ADX: `Verified`

`p384x` is `p384` multiplying modulo `p` and `n` with BMI2 and ADX
(`Mod.adx`) and selecting the comb's entries with AVX2, which the proof of
`sign_ok` covers as it covers any multiplication (`Proof/Mont/X86_64/Adx.lean`)
and either selection (`selPassV_ok`): the same curve, so the same facts
(`p384x_ok`, from `p384_ok`) and the same precondition.
-/

namespace VG.Proof.Ecdsa.X86_64.P384

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-- How P-384's field elements and scalars are multiplied, for the notes of its
functions: with BMI2 and ADX (`adx`) or not. -/
def mulNote (adx : Bool) : String :=
  if adx then
    "multiplied by Montgomery multiplication by rows (operand scanning) of BMI2's `mulx`, each \
    product's low half added through OF (`adox`) and its high half through CF (`adcx`), two \
    carry chains that do not wait for each other, each row followed by the reduction's row by \
    the modulus (its multiplier `u = t₀ (-m⁻¹) mod 2⁶⁴`), with a final conditional subtraction"
  else
    "multiplied by word-by-word Montgomery multiplication (CIOS) with a final conditional \
    subtraction"

/-- How the comb's entries are selected, for the notes of its functions: with
AVX2 (`adx`) or not. -/
def selNote (adx : Bool) : String :=
  if adx then
    "32 bytes at a time with AVX2, and keeping (`vpand`, `vpor`, under the mask of `vpcmpeqd` \
    of a counter and the magnitude, broadcast)"
  else "16 bytes at a time, and keeping (`pand`, `por`)"

/-! `p384x` is `p384` but for `adx` and `avx2`: its other fields, rewritten rather than
compared by unfolding (which would evaluate the order's bits). -/

theorem p384x_C : p384x.C = p384.C := rfl
theorem p384x_n : p384x.n = p384.n := rfl
theorem p384x_comb : p384x.comb = p384.comb := rfl

theorem p384x_sh : p384x.sh = 0 := by
  unfold Cfg.sh
  rw [p384x_C]
  exact p384_sh

theorem p384x_combConsts : p384x.combConsts = [("VG_P384_COMB", p384W)] := by
  unfold Cfg.combConsts Cfg.combWords Cfg.R
  rw [p384x_comb, p384x_C, p384x_n]
  rfl

theorem p384x_ok (hI : InvSounds) : CfgOk p384x where
  n0 := by decide
  n10 := by decide
  onG := Proof.P384.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  red_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  n_len := by decide +kernel
  n_bits := by decide +kernel
  nbits_le := by decide
  mask h := absurd h (by decide)
  sh := by rw [p384x_sh]; decide
  comb d h := by cases h; exact ⟨by decide, by decide⟩
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.P384.curve.p
    rw [show Spec.P384.curve.p =
      39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
      by decide +kernel]
    exact Proof.P384.prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n h := absurd h (by decide)
  am3 := by unfold AM3; decide +kernel
  even _ := by decide

theorem p384x_tbls (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    CombTbls p384x := fun d h => by cases h; exact ⟨hT, fun h => absurd h (by decide)⟩

theorem pre_of_x {s : State} (h : signX86_64.pre s) : Pre p384x s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p384x_combConsts, p384x_C, show p384.C.len = 48 from rfl]; simp only [Abi.constRegions,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, ?_⟩
  rw [TblsHeld, p384x_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [Abi.constRegions, List.map_cons, List.map_nil, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

theorem sign_x86_adx (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP384Adx s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p384x_ok hI) hL (p384x_tbls hT) (pre_of_x hs)
  have hsp : ∀ i ∈ instrs signP384Adx, Taint.clobbers i .rsp = false := by
    have h : signP384Adx.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hro
      · exact hrs) (by decide)

theorem sign_ct_adx : ConstantTime isa signX86_64.pre signX86_64.pub signP384Adx :=
  VG.Taint.constantTime (A := taintSym ["VG_P384_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    (fun _ _ _ _ ⟨_, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide)

theorem sign_verified_adx (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds) :
    Verified X86_64.target signP384Adx
      (Spec.Ecdsa.P384.inst.signContract (X86_64.abi.withConsts p384.combConsts)) :=
  Verified.of_correct (sign_x86_adx hL hT hI) sign_ct_adx implies

end VG.Proof.Ecdsa.X86_64.P384
