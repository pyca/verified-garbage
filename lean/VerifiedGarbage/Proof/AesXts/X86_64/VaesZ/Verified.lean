module

public import VerifiedGarbage.Proof.AesXts.X86_64.VaesZ.Crypt
public import VerifiedGarbage.Proof.AesXts.X86_64.VaesTo.Verified
public import VerifiedGarbage.Proof.AesCbc.X86_64.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.AesXts.X86_64.VaesZ.Crypt
meta import VerifiedGarbage.Proof.AesXts.X86_64.VaesTo.Verified
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Call
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# XTS-AES with AVX-512 VAES on x86-64: `Verified`

The four functions of `Impl/AesXts/X86_64VaesZ.lean`: correct by
`VaesZ.encrypt_wp`, `decrypt_wp`, `VaesTo.encryptTo_wp` and `decryptTo_wp`;
constant time by the taint analysis of the whole function, from the public
arguments (pointers, `rounds` and `n`), as the functions of
`Vaes/Verified.lean` and `VaesTo/Verified.lean` are (for those out of place,
from `VaesTo.τ₀`); never writing the stack pointer, `mxcsr` or calling
anything. `toZ`: the out-of-place pair, for the variant's `XtsImpl.to`.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.VaesZ

open VG VG.X86_64
open VG.Proof.AesCbc.X86_64 (modeX86_64)

theorem encrypt_mx : Impl.AesXts.X86_64VaesZ.encrypt.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem encrypt_spSafe : Impl.AesXts.X86_64VaesZ.encrypt.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem encrypt_nosp : NoSp Impl.AesXts.X86_64VaesZ.encrypt := by
  have h : Impl.AesXts.X86_64VaesZ.encrypt.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem encrypt_depth : Impl.AesXts.X86_64VaesZ.encrypt.depth = 0 := by decide +kernel

theorem encrypt_correct (s : State) (hs : (modeX86_64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64VaesZ.encrypt s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec encrypt_mx he hg, hp⟩

theorem encrypt_ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode true)).pre (modeX86_64 (AesXts.xtsMode true)).pub Impl.AesXts.X86_64VaesZ.encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decrypt_mx : Impl.AesXts.X86_64VaesZ.decrypt.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem decrypt_spSafe : Impl.AesXts.X86_64VaesZ.decrypt.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem decrypt_nosp : NoSp Impl.AesXts.X86_64VaesZ.decrypt := by
  have h : Impl.AesXts.X86_64VaesZ.decrypt.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem decrypt_depth : Impl.AesXts.X86_64VaesZ.decrypt.depth = 0 := by decide +kernel

theorem decrypt_correct (s : State) (hs : (modeX86_64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64VaesZ.decrypt s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec decrypt_mx he hg, hp⟩

theorem decrypt_ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode false)).pre (modeX86_64 (AesXts.xtsMode false)).pub Impl.AesXts.X86_64VaesZ.decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptTo_mx : Impl.AesXts.X86_64VaesZ.encryptTo.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem encryptTo_spSafe : Impl.AesXts.X86_64VaesZ.encryptTo.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem encryptTo_nosp : NoSp Impl.AesXts.X86_64VaesZ.encryptTo := by
  have h : Impl.AesXts.X86_64VaesZ.encryptTo.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem encryptTo_depth : Impl.AesXts.X86_64VaesZ.encryptTo.depth = 0 := by decide +kernel

theorem encryptTo_correct (s : State) (hs : (To.xtsToX86_64 true).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64VaesZ.encryptTo s t s' ∧ abiPreserved s s' ∧ (To.xtsToX86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VaesTo.encryptTo_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec encryptTo_mx he hg, hp⟩

theorem encryptTo_ct : ConstantTime isa (To.xtsToX86_64 true).pre (To.xtsToX86_64 true).pub Impl.AesXts.X86_64VaesZ.encryptTo :=
  VG.Taint.constantTime (A := taint) VaesTo.τ₀ (fun _ _ h₁ h₂ hq => VaesTo.agree h₁ h₂ hq) (by taint_decide)

theorem decryptTo_mx : Impl.AesXts.X86_64VaesZ.decryptTo.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem decryptTo_spSafe : Impl.AesXts.X86_64VaesZ.decryptTo.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem decryptTo_nosp : NoSp Impl.AesXts.X86_64VaesZ.decryptTo := by
  have h : Impl.AesXts.X86_64VaesZ.decryptTo.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem decryptTo_depth : Impl.AesXts.X86_64VaesZ.decryptTo.depth = 0 := by decide +kernel

theorem decryptTo_correct (s : State) (hs : (To.xtsToX86_64 false).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64VaesZ.decryptTo s t s' ∧ abiPreserved s s' ∧ (To.xtsToX86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VaesTo.decryptTo_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec decryptTo_mx he hg, hp⟩

theorem decryptTo_ct : ConstantTime isa (To.xtsToX86_64 false).pre (To.xtsToX86_64 false).pub Impl.AesXts.X86_64VaesZ.decryptTo :=
  VG.Taint.constantTime (A := taint) VaesTo.τ₀ (fun _ _ h₁ h₂ hq => VaesTo.agree h₁ h₂ hq) (by taint_decide)

/-- The out-of-place functions with AVX-512 VAES,
`vg_aes_xts_encrypt_to_vaes_vpclmul_avx512` and
`vg_aes_xts_decrypt_to_vaes_vpclmul_avx512`. -/
def toZ : To.ToImpl where
  enc := ⟨"vg_aes_xts_encrypt_to" ++ "_vaes_vpclmul_avx512", Impl.AesXts.X86_64VaesZ.encryptTo⟩
  encDepth := by rw [encryptTo_depth]; decide
  encOk := encryptTo_correct
  encCt := encryptTo_ct
  encNosp := encryptTo_nosp
  encMxcsr := encryptTo_mx
  encSpSafe := encryptTo_spSafe
  dec := ⟨"vg_aes_xts_decrypt_to" ++ "_vaes_vpclmul_avx512", Impl.AesXts.X86_64VaesZ.decryptTo⟩
  decDepth := by rw [decryptTo_depth]; decide
  decOk := decryptTo_correct
  decCt := decryptTo_ct
  decNosp := decryptTo_nosp
  decMxcsr := decryptTo_mx
  decSpSafe := decryptTo_spSafe

end VG.Proof.AesXts.X86_64.VaesZ
