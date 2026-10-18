module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
public import VerifiedGarbage.Impl.RsaPss.X86_64

/-!
# RSASSA-PSS on x86-64: the pieces that keep `rsp`, MXCSR and the stack

Each piece that verification and signing run around their calls of the
streaming hash functions is `Good` (`Proof/RsaOaep/X86_64/Stack.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.RsaOaep.X86_64 (Good)

theorem mPrefix_good : Good mPrefix := ⟨rfl, rfl, by decide⟩
theorem hashPrefix_good : Good hashPrefix := ⟨rfl, rfl, by decide⟩
theorem hashM_good : Good hashM := ⟨rfl, rfl, by decide⟩
theorem putSalt_good : Good putSalt := ⟨rfl, rfl, by decide⟩
theorem putH_good : Good putH := ⟨rfl, rfl, by decide⟩
theorem copyDb_good : Good copyDb := ⟨rfl, rfl, by decide⟩
theorem cmpH_good : Good cmpH := ⟨rfl, rfl, by decide⟩
theorem selCand_good : Good selCand := ⟨rfl, rfl, by decide⟩
theorem copyQ_good (a b : Nat) : Good (copyQ a b) := ⟨rfl, rfl, by simp [copyQ, Code.depth]⟩

end VG.Proof.RsaPss.X86_64
