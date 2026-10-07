import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lit
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.P256.Order

/-!
# ECDSA over P-256 on x86-64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the
registration file supplies: `Proof.P256.law`, `Proof.P256.combOk7` and the
variant's `inv`), so `sign_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `out` or `scratch`, which the return address
is apart from (`abiPreserved`). Constant time by taint tracking with the
address of the comb's static public (`taintSym`): the only branches are on
loop counters, and every address is an argument or the static's address
plus a constant or a counter.
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p256_nBits : 64 * p256.n ≤ Spec.Ecdsa.nBits p256.C := by
  show 256 ≤ Spec.P256.curve.n.log2 + 1
  have : 255 ≤ Spec.P256.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `32` bytes is dropped. -/
theorem p256_sh : p256.sh = 0 := by
  have h : 64 * 4 ≤ Spec.Ecdsa.nBits p256.C := p256_nBits
  show 8 * 32 - Spec.Ecdsa.nBits p256.C = 0; omega

theorem p256_ok (hI : InvSounds) : CfgOk p256 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P256.onCurve_G
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
  sh := by rw [p256_sh]; decide
  comb d h := by cases h; exact ⟨by decide, by decide⟩
  inv _ := ⟨by decide, @hI _ p256.C.p_ne_zero Proof.P256.p_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ p256.C.n_ne_zero Proof.P256.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  am3 := by unfold AM3; decide +kernel
  even _ := by decide

theorem p256_tbls (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    CombTbls p256 := fun d h => by cases h; exact ⟨hT, fun _ => Proof.P256.booth hL⟩

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p256_combConsts, show p256.C.len = 32 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, ?_⟩
  rw [TblsHeld, p256_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

/-- The signature `code` of a curve `c` (P-256, with either multiplication) that
the proof supports, whose precondition the contract's gives (`hpre`), never
writing `rsp`, calling or loading MXCSR (which its literal decides). -/
theorem sign_x86_of {c : Cfg} {code : Prog isa} (hc : CfgOk c) (hL : Law c.C) (hT : CombTbls c)
    (hpre : ∀ s, signX86_64.pre s → Pre c s) (hpost : ∀ s s', SignPost c s s' → signX86_64.post s s')
    (hcode : c.sign = code) (hsp : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true)
    (hnc : code.noCalls = true) (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  subst hcode
  obtain ⟨t, s', he, hsv, hpost'⟩ := sign_ok hc hL hT (hpre s hs)
  have hsp : ∀ i ∈ instrs c.sign, Taint.clobbers i .rsp = false := by
    rw [Code.allInstrs_eq, List.all_eq_true] at hsp
    intro i hi
    simpa using hsp i hi
  have F := (Exec.regions he hnc).2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨fun r hr => ?_, ?_⟩, hpost _ _ hpost'⟩
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

theorem sign_x86 (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP256 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  sign_x86_of (p256_ok hI) hL (p256_tbls hL hT) (fun _ => pre_of) (fun _ _ => id) rfl (by lit_decide)
    (by lit_decide) (by lit_decide) s hs

theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signP256 :=
  VG.Taint.constantTime (A := taintSym ["VG_P256_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    (fun _ _ _ _ ⟨_, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide)

theorem sign_verified (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : InvSounds) :
    Verified X86_64.target signP256
      (Spec.Ecdsa.P256.inst.signContract (X86_64.abi.withConsts p256.combConsts)) :=
  Verified.of_correct (sign_x86 hL hT hI) sign_ct implies

end VG.Proof.Ecdsa.X86_64
