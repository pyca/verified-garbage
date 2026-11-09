module

public import VerifiedGarbage.Proof.AesXts.X86_64.VaesTo.Crypt
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.AesXts.X86_64.VaesTo.Crypt
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# One-pass XTS-AES on x86-64, out of place: `Verified`

Correctness from `crypt_wp`, for the VAES loop and the AES-NI loop; constant
time by the taint analysis of the whole function, from the public arguments
(pointers, `rounds` and `n`), with the scratch buffer's slot that keeps
`src - dst` public (`τ₀`: the writable regions' lengths and the scratch
buffer's base, `agree`); and the two `To.ToImpl` the variants
`vaesVpclmul` and `aesniPclmul` give their out-of-place callers.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.VaesTo

open VG VG.X86_64

/-- The taint the analysis starts from. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .rsp], flags := false, lens := [16, 0, 2176],
    bases := [(.r9, 2, 0)] }

/-- `τ₀` holds in two runs with the same public arguments. -/
theorem wf {s : State} (hp : UPre s) : X86_64.Taint.Wf τ₀ s := by
  have := hp.n_lt
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hq => ?_⟩
  · rw [hp.wr]; exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · rw [hp.wr]
    refine .cons (fun r hr => ?_) (.cons (fun r hr => ?_) (.cons (fun r hr => absurd hr (by simp)) .nil))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.iv_data
      · exact hp.iv_scr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hp.data_scr
  · rw [hp.wr]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · show 16 ≤ 2 ^ 64; decide
    · show 16 * N s ≤ 2 ^ 64; omega
    · show 2176 ≤ 2 ^ 64; decide
  · simp only [τ₀, List.mem_singleton] at hq; subst hq
    simp only [X86_64.Taint.region, hp.wr, List.getD_cons_succ, List.getD_cons_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero]

theorem agree {enc : Bool} {s₁ s₂ : State} (h₁ : (To.xtsToX86_64 enc).pre s₁) (h₂ : (To.xtsToX86_64 enc).pre s₂)
    (hq : (To.xtsToX86_64 enc).pub s₁ s₂) : X86_64.Taint.Agree τ₀ s₁ s₂ := by
  have p₁ := UPre.of h₁
  have p₂ := UPre.of h₂
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hq
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => ?_, wf p₁, wf p₂,
    fun sl hsl => absurd hsl (by simp [τ₀]), fun sl hsl => absurd hsl (by simp [τ₀]),
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [p₁.wr, p₂.wr]; simp only [ivR, dataR, scrR, Iv, Dp, N, S]; rw [e3, e5, e6, e7]

theorem encryptVaes_mx : Impl.AesXts.X86_64VaesTo.encryptVaes.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem encryptVaes_spSafe : Impl.AesXts.X86_64VaesTo.encryptVaes.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem encryptVaes_nosp : NoSp Impl.AesXts.X86_64VaesTo.encryptVaes := by
  have h : Impl.AesXts.X86_64VaesTo.encryptVaes.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem encryptVaes_depth : Impl.AesXts.X86_64VaesTo.encryptVaes.depth ≤ 2 := by decide +kernel

theorem encryptVaes_correct (s : State) (hs : (To.xtsToX86_64 true).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64VaesTo.encryptVaes s t s' ∧ abiPreserved s s' ∧ (To.xtsToX86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encryptVaes_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec encryptVaes_mx he hg, hp⟩

theorem encryptVaes_ct : ConstantTime isa (To.xtsToX86_64 true).pre (To.xtsToX86_64 true).pub Impl.AesXts.X86_64VaesTo.encryptVaes :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hq => agree h₁ h₂ hq) (by taint_decide)

theorem decryptVaes_mx : Impl.AesXts.X86_64VaesTo.decryptVaes.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem decryptVaes_spSafe : Impl.AesXts.X86_64VaesTo.decryptVaes.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem decryptVaes_nosp : NoSp Impl.AesXts.X86_64VaesTo.decryptVaes := by
  have h : Impl.AesXts.X86_64VaesTo.decryptVaes.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem decryptVaes_depth : Impl.AesXts.X86_64VaesTo.decryptVaes.depth ≤ 2 := by decide +kernel

theorem decryptVaes_correct (s : State) (hs : (To.xtsToX86_64 false).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64VaesTo.decryptVaes s t s' ∧ abiPreserved s s' ∧ (To.xtsToX86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decryptVaes_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec decryptVaes_mx he hg, hp⟩

theorem decryptVaes_ct : ConstantTime isa (To.xtsToX86_64 false).pre (To.xtsToX86_64 false).pub Impl.AesXts.X86_64VaesTo.decryptVaes :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hq => agree h₁ h₂ hq) (by taint_decide)

theorem encryptAesNi_mx : Impl.AesXts.X86_64VaesTo.encryptAesNi.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem encryptAesNi_spSafe : Impl.AesXts.X86_64VaesTo.encryptAesNi.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem encryptAesNi_nosp : NoSp Impl.AesXts.X86_64VaesTo.encryptAesNi := by
  have h : Impl.AesXts.X86_64VaesTo.encryptAesNi.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem encryptAesNi_depth : Impl.AesXts.X86_64VaesTo.encryptAesNi.depth ≤ 2 := by decide +kernel

theorem encryptAesNi_correct (s : State) (hs : (To.xtsToX86_64 true).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64VaesTo.encryptAesNi s t s' ∧ abiPreserved s s' ∧ (To.xtsToX86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encryptAesNi_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec encryptAesNi_mx he hg, hp⟩

theorem encryptAesNi_ct : ConstantTime isa (To.xtsToX86_64 true).pre (To.xtsToX86_64 true).pub Impl.AesXts.X86_64VaesTo.encryptAesNi :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hq => agree h₁ h₂ hq) (by taint_decide)

theorem decryptAesNi_mx : Impl.AesXts.X86_64VaesTo.decryptAesNi.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem decryptAesNi_spSafe : Impl.AesXts.X86_64VaesTo.decryptAesNi.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem decryptAesNi_nosp : NoSp Impl.AesXts.X86_64VaesTo.decryptAesNi := by
  have h : Impl.AesXts.X86_64VaesTo.decryptAesNi.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem decryptAesNi_depth : Impl.AesXts.X86_64VaesTo.decryptAesNi.depth ≤ 2 := by decide +kernel

theorem decryptAesNi_correct (s : State) (hs : (To.xtsToX86_64 false).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64VaesTo.decryptAesNi s t s' ∧ abiPreserved s s' ∧ (To.xtsToX86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decryptAesNi_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec decryptAesNi_mx he hg, hp⟩

theorem decryptAesNi_ct : ConstantTime isa (To.xtsToX86_64 false).pre (To.xtsToX86_64 false).pub Impl.AesXts.X86_64VaesTo.decryptAesNi :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hq => agree h₁ h₂ hq) (by taint_decide)

/-- The one-pass out-of-place functions with VAES and VPCLMULQDQ,
`vg_aes_xts_encrypt_to_vaes_vpclmul` and `vg_aes_xts_decrypt_to_vaes_vpclmul`. -/
def toVaes : To.ToImpl where
  enc := ⟨"vg_aes_xts_encrypt_to" ++ "_vaes_vpclmul", Impl.AesXts.X86_64VaesTo.encryptVaes⟩
  encDepth := encryptVaes_depth
  encOk := encryptVaes_correct
  encCt := encryptVaes_ct
  encNosp := encryptVaes_nosp
  encMxcsr := encryptVaes_mx
  encSpSafe := encryptVaes_spSafe
  dec := ⟨"vg_aes_xts_decrypt_to" ++ "_vaes_vpclmul", Impl.AesXts.X86_64VaesTo.decryptVaes⟩
  decDepth := decryptVaes_depth
  decOk := decryptVaes_correct
  decCt := decryptVaes_ct
  decNosp := decryptVaes_nosp
  decMxcsr := decryptVaes_mx
  decSpSafe := decryptVaes_spSafe

/-- The one-pass out-of-place functions with AES-NI and PCLMULQDQ,
`vg_aes_xts_encrypt_to_aesni_pclmul` and `vg_aes_xts_decrypt_to_aesni_pclmul`. -/
def toAesNi : To.ToImpl where
  enc := ⟨"vg_aes_xts_encrypt_to" ++ "_aesni_pclmul", Impl.AesXts.X86_64VaesTo.encryptAesNi⟩
  encDepth := encryptAesNi_depth
  encOk := encryptAesNi_correct
  encCt := encryptAesNi_ct
  encNosp := encryptAesNi_nosp
  encMxcsr := encryptAesNi_mx
  encSpSafe := encryptAesNi_spSafe
  dec := ⟨"vg_aes_xts_decrypt_to" ++ "_aesni_pclmul", Impl.AesXts.X86_64VaesTo.decryptAesNi⟩
  decDepth := decryptAesNi_depth
  decOk := decryptAesNi_correct
  decCt := decryptAesNi_ct
  decNosp := decryptAesNi_nosp
  decMxcsr := decryptAesNi_mx
  decSpSafe := decryptAesNi_spSafe

end VG.Proof.AesXts.X86_64.VaesTo
