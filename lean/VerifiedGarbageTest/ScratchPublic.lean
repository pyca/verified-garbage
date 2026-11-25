module

import VerifiedGarbage.Proof.Zeroize.Wiped
import VerifiedGarbage.Spec.AesEcb.Contract
import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Spec.MlKem.EncapsH

/-!
# Which bytes of scratch are wiped is public (#6404)

`Zeroize.scrubbed` lets each byte of scratch be unchanged or zero, so it allows a
choice among them that depends on a secret; the bytes left (`Zeroize.left`) tell
such a choice, and the `Api`s say that those are public (`Api.publicOut`), which
every artifact proves. A fixed choice leaves the same bytes.
-/

namespace VG.Test.ScratchPublic

open VG Spec.Zeroize

/-- Scratch on entry: ones. -/
def entry : Mem := fun _ => 1

/-- Scratch on return, its first byte kept or zeroed by a secret bit. -/
def exit (secret : Bool) : Mem := fun a => if a = 0 && !secret then 0 else 1

/-- Both are scrubbed. -/
theorem exit_scrubbed (secret : Bool) : scrubbed entry (exit secret) 0 16 := by
  intro a _
  unfold exit entry
  split
  · exact .inr rfl
  · exact .inl rfl

/-- What they leave tells the bit. -/
theorem exit_left : left (exit false) 0 16 ≠ left (exit true) 0 16 := fun h => by
  have := congrArg (·.headD 0) h
  revert this
  decide

/-- A choice that does not depend on it leaves the same bytes. -/
theorem fixed_left {S : Nat → Bool} {m m₁ m₂ : Mem} {p : Addr} {len : Nat}
    (h₁ : Proof.Zeroize.WipedBy S m m₁ p len) (h₂ : Proof.Zeroize.WipedBy S m m₂ p len) :
    left m₁ p len = left m₂ p len := h₁.left h₂ rfl

/-! Every `Api` whose contract has `scrubbed` declares it. -/

example : Spec.AesEcb.encryptApi.publicOut = some Spec.AesEcb.scratchOut := rfl
example : Spec.AesEcb.decryptApi.publicOut = some Spec.AesEcb.scratchOut := rfl
example : Spec.Cbc.aesEncryptApi.publicOut = some Spec.Cbc.aesScratchOut := rfl
example : Spec.Cbc.aesDecryptApi.publicOut = some Spec.Cbc.aesScratchOut := rfl
example : Spec.MlKem.keyGenApi.publicOut = some Spec.MlKem.keyGenOut := rfl
example : Spec.MlKem.encapsApi.publicOut = some Spec.MlKem.encapsOut := rfl
example : Spec.MlKem.encapsHApi.publicOut = some Spec.MlKem.encapsHOut := rfl
example : Spec.MlKem.decapsApi.publicOut = some Spec.MlKem.decapsOut := rfl
example : Spec.MlKem1024.keyGenApi.publicOut = some Spec.MlKem1024.keyGenOut := rfl
example : Spec.MlKem1024.encapsApi.publicOut = some Spec.MlKem1024.encapsOut := rfl
example : Spec.MlKem1024.encapsHApi.publicOut = some Spec.MlKem1024.encapsHOut := rfl
example : Spec.MlKem1024.decapsApi.publicOut = some Spec.MlKem1024.decapsOut := rfl

end VG.Test.ScratchPublic
