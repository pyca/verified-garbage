import VerifiedGarbage.Proof.EcKey.X86_64.P384.Verified
import VerifiedGarbage.Proof.EcKey.X86_64.P384.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx

/-!
# P-384 public keys on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p384x` (`p384` multiplying modulo `p` with BMI2 and
ADX and selecting the comb's entries with AVX2): the same curve, so the same
precondition and postcondition.
-/

namespace VG.Proof.EcKey.X86_64.P384

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P384

theorem pre_of_x {s : State} (h : pkX86_64.pre s) : PkPre p384x s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p384x_combConsts, p384x_C, show p384.C.len = 48 from rfl]; simp only [Abi.constRegions,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h8, h9, ?_⟩
  rw [TblsHeld, p384x_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [Abi.constRegions, List.map_cons, List.map_nil, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

theorem post_of_x {s s' : State} (h : PkPost p384x s s') : pkX86_64.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 97 = Spec.EcKey.encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 97 = List.replicate 97 0
  revert h
  generalize hq : pk s.mem (s.gpr .rsi) = q
  rw [show Spec.EcKey.publicKey p384x.C (dk p384x s) = pk s.mem (s.gpr .rsi) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_x86_adx (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyP384Adx s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := wp_of_inline (by lit_decide) <| publicKey_ok (p384x_ok hI) hL (p384x_tbls hT) (pre_of_x hs)
  have hsp : ∀ i ∈ instrs publicKeyP384Adx, Taint.clobbers i .rsp = false := by
    have h : publicKeyP384Adx.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, post_of_x hpost⟩
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

theorem pk_ct_adx : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyP384Adx :=
  VG.Taint.constantTime (A := taintSym ["VG_P384_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx])
    (fun _ _ _ _ ⟨_, h1, h2, h3, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide)

theorem pk_verified_adx (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyP384Adx
      (Spec.EcKey.P384.inst.publicKeyContract (X86_64.abi.withConsts p384.combConsts)) :=
  Verified.of_correct (pk_x86_adx hL hT hI) pk_ct_adx implies

end VG.Proof.EcKey.X86_64.P384
