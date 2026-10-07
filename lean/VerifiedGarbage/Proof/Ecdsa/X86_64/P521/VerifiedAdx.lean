import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.LitAdx
import VerifiedGarbage.Proof.P521.X86_64.TaintSumsAdx

/-!
# ECDSA over P-521 on x86-64 with BMI2 and ADX: `Verified`

`p521x` is `p521` multiplying modulo `p` with BMI2 and ADX (`Mod.adx`), which
the proof of `sign_ok` covers as it covers any multiplication
(`Proof/Mont/X86_64/MulPX.lean`): the same curve, so the same facts
(`p521x_ok`, from `p521_ok`) and the same precondition.
-/

namespace VG.Proof.Ecdsa.X86_64.P521

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-- How P-521's field elements are multiplied modulo `p`, for the notes of its
functions: with BMI2 and ADX (`adx`) or not. -/
def mulNote (adx : Bool) : String :=
  if adx then
    "multiplied modulo `p` by Montgomery multiplication by rows (operand scanning) of BMI2's \
    `mulx`, each product's low half added through OF (`adox`) and its high half through CF \
    (`adcx`), two carry chains that do not wait for each other, into nine registers, each row's \
    low word stored once final; as `p = 2⁵²¹ - 1 ≡ -1 (mod 2⁶⁴)`, the reduction's multipliers \
    are the product's low words (the ninth plus 512 times the first, modulo 2⁶⁴), and a row of \
    products by 512 adds `512 U` eight words up, which leaves `(a b + U p) / 2⁵⁷⁶ < 2p`; that is \
    reduced below `p` by adding 1, whose bit 521 is whether it is at least `p`, subtracting 1 \
    less that bit, and clearing the bits from 521 up"
  else
    "multiplied modulo `p` by Montgomery multiplication by columns (product scanning, the \
    accumulator in three registers; as `p = 2⁵²¹ - 1 ≡ -1 (mod 2⁶⁴)`, each reduction's \
    multiplier is its column's low word, added 512 times eight columns up; a square computes \
    each product of two different words once and adds it twice) with a final conditional \
    subtraction"

/-! `p521x` is `p521` but for `adx`: its other fields, rewritten rather than
compared by unfolding (which would evaluate the order's bits). -/

theorem p521x_C : p521x.C = p521.C := rfl
theorem p521x_n : p521x.n = p521.n := rfl
theorem p521x_comb : p521x.comb = p521.comb := rfl

theorem p521x_sh : p521x.sh = 7 := by
  unfold Cfg.sh
  rw [p521x_C]
  exact p521_sh

theorem p521x_combConsts : p521x.combConsts = [("VG_P521_COMB", p521W)] := by
  unfold Cfg.combConsts Cfg.combWords Cfg.R
  rw [p521x_comb, p521x_C, p521x_n]
  rfl

theorem p521x_ok (hI : InvSounds) : CfgOk p521x where
  n0 := by decide
  n10 := by decide
  onG := Proof.P521.onCurve_G
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
  sh := by rw [p521x_sh]; decide
  comb d h := by cases h; exact ⟨by decide, by decide⟩
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.P521.curve.p
    rw [show Spec.P521.curve.p =
      6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151
      by decide +kernel]
    exact Proof.P521.prime_6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ p521x.C.n_ne_zero Proof.P521.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  am3 := by unfold AM3; decide +kernel
  even h := absurd h (by decide)

theorem p521x_tbls (hT : CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    CombTbls p521x := fun d h => by cases h; exact ⟨hT, fun h => absurd h (by decide)⟩

theorem pre_of_x {s : State} (h : signX86_64.pre s) : Pre p521x s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p521x_combConsts, p521_constRegions, p521x_C, show p521.C.len = 66 from rfl]; simp only [
    List.cons_append, List.nil_append], h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, ?_⟩
  rw [TblsHeld, p521x_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [p521_constRegions, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

theorem sign_x86_adx (hL : Law Spec.P521.curve)
    (hT : CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP521Adx s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p521x_ok hI) hL (p521x_tbls hT) (pre_of_x hs)
  have hsp : ∀ i ∈ instrs signP521Adx, Taint.clobbers i .rsp = false := by
    have h : signP521Adx.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
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

theorem sign_ct_adx : ConstantTime isa signX86_64.pre signX86_64.pub signP521Adx := by
  obtain ⟨_, hc⟩ : ∃ h, ((taintSym ["VG_P521_COMB"]).check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) signP521Adx h).isSome = true := by
    taint_decide_sum [Proof.P521.X86_64.combGXSum, Proof.P521.X86_64.invPXSum]
  refine VG.Taint.constantTime (A := taintSym ["VG_P521_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) ?_ hc
  exact fun _ _ _ _ ⟨_, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩

theorem sign_verified_adx (hL : Law Spec.P521.curve)
    (hT : CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : InvSounds) :
    Verified X86_64.target signP521Adx
      (Spec.Ecdsa.P521.inst.signContract (X86_64.abi.withConsts p521.combConsts)) :=
  Verified.of_correct (sign_x86_adx hL hT hI) sign_ct_adx implies

end VG.Proof.Ecdsa.X86_64.P521
