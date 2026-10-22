module

public import VerifiedGarbage.Proof.RsaOaep.X86.Base
meta import VerifiedGarbage.Proof.RsaOaep.X86.Base
public meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # RSAES-OAEP on x86: the taint checks of each digest length, and the hash functions of RSASSA-PSS -/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86 VG.Impl.RsaOaep.X86
open VG.Proof.RsaPss.X86 (PssHash)

theorem certs20 : OCerts (dShape 20) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, NoSp.of_all (by decide +kernel)⟩ <;>
    exact ⟨_, by taint_decide⟩

theorem certs28 : OCerts (dShape 28) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, NoSp.of_all (by decide +kernel)⟩ <;>
    exact ⟨_, by taint_decide⟩

theorem certs32 : OCerts (dShape 32) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, NoSp.of_all (by decide +kernel)⟩ <;>
    exact ⟨_, by taint_decide⟩

theorem certs48 : OCerts (dShape 48) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, NoSp.of_all (by decide +kernel)⟩ <;>
    exact ⟨_, by taint_decide⟩

theorem certs64 : OCerts (dShape 64) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, NoSp.of_all (by decide +kernel)⟩ <;>
    exact ⟨_, by taint_decide⟩

/-- The certificates of a digest length the library's hash functions have. -/
theorem certsOf {D : Nat} (h : D = 20 ∨ D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : OCerts (dShape D) := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  exacts [certs20, certs28, certs32, certs48, certs64]

/-- The RSASSA-PSS hash function's streaming functions. -/
def OHash.ofPss (h : PssHash) (hD : h.H.D = 20 ∨ h.H.D = 28 ∨ h.H.D = 32 ∨ h.H.D = 48 ∨ h.H.D = 64) : OHash :=
  ⟨h.H.st, h.ok.hH, h.G, h.hash, h.glen, h.valid, OCerts.of_shape (certsOf hD)⟩

end VG.Proof.RsaOaep.X86
