module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubUpFill
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# The checked private RSA operation as RSA's padding calls it, for its callers' cleanup (x86-64)

`vg_rsa_private_checked_precomputed` over any implementation of the CRT
operation (`CrtImpl`), `Proof.RsaPkcs1Enc.X86_64.privCodeP`, is its code over
stubs of the CRT and public operations with the implementation's
(`privCodeP_eq`): what the cleanup of the padding functions that call it
needs of it (`priv_side`, and at the level `sse`, `priv_up`) follows from
the kernel's evaluation of the stub, once, and what the implementation
proves of its code (`CrtImpl.sideP`, `CrtImpl.upP`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.PrivScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl)

/-- The level of the cleanup of the padding functions over `c`. -/
def level (c : CrtImpl) : VecLevel := c.level.join c.pubOp.level

theorem level_sse {c : CrtImpl} (h : level c = .sse) : c.level = .sse ∧ c.pubOp.level = .sse := by
  unfold level at h
  revert h; cases c.level <;> cases c.pubOp.level <;> simp [VecLevel.join]

/-- The checked private operation over stubs of the CRT and public operations. -/
def privStub : Prog isa := Impl.Rsa.X86_64.PrivChecked.codeP "crt" (.block []) "pub" (.block [])

/-- The CRT and public operations of `c`, by the names the stub calls them by. -/
def privSigma (c : CrtImpl) (f : String) : Option (String × Prog isa) :=
  if f = "crt" then some (c.nameP, c.codeP) else if f = "pub" then some (c.pubOp.name, c.pubOp.code) else none

/-- The stack the CRT operation (called, 8 bytes) and the public operation (called) need. -/
def privStack : String → Nat := fun s => if s = "crt" then 16 else 8

theorem privCodeP_eq (c : CrtImpl) : Proof.RsaPkcs1Enc.X86_64.privCodeP c = fillCallsG (privSigma c) privStub := by
  unfold Proof.RsaPkcs1Enc.X86_64.privCodeP privStub; kernel_rfl

theorem priv_stub : stubCalleeG privStub VecLevel.sse.level privStack 3256 = true := by lit_decide

theorem priv_stubUp :
    (decide (depthG privStack privStub ≤ 3256) && privStub.allInstrs (fun i => decide (i.vecLevel ≤ 1)) &&
      UpperLock.up privStub true && (UpperLock.inames privStub).isEmpty) = true := by
  rw [← upF_eq]; lit_decide

/-- What the cleanup of a padding function at a level `k` at least `c`'s needs of its call. -/
theorem priv_side (c : CrtImpl) {k : Nat} (hk : (level c).level ≤ k) :
    calleeSide (Proof.RsaPkcs1Enc.X86_64.privCodeP c) k 3256 = true := by
  rw [privCodeP_eq]
  refine calleeSide_of_fillG (fillG_of ?_ _) (Nat.zero_le _) priv_stub
  intro f g d h
  unfold privSigma at h
  split at h
  · rename_i hf; subst hf
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [show privStack "crt" = 8 + 8 from rfl]
    exact FillG.calleeSide_call _
      (calleeSide_mono (Nat.le_trans (level_join_left _ _) hk) (Nat.le_refl _) c.sideP)
  split at h
  · rename_i hf; subst hf
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [show privStack "pub" = 0 + 8 from rfl]
    exact FillG.calleeSide_call _
      (calleeSide_mono (Nat.le_trans (level_join_right _ _) hk) (Nat.le_refl _) c.pubOp.side)
  cases h

/-- What the cleanup of a padding function at the level `sse` needs of its call. -/
theorem priv_up (c : CrtImpl) (hl : level c = .sse) :
    upCallee (Proof.RsaPkcs1Enc.X86_64.privCodeP c) 3256 = true := by
  obtain ⟨h1, h2⟩ := level_sse hl
  rw [privCodeP_eq]
  refine upCallee_fillCallsG ?_ _ priv_stubUp
  intro f g d h
  unfold privSigma at h
  split at h
  · rename_i hf; subst hf
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [show privStack "crt" = 8 + 8 from rfl]; exact upCallee_call _ (c.upP h1)
  split at h
  · rename_i hf; subst hf
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [show privStack "pub" = 0 + 8 from rfl]; exact upCallee_call _ (c.pubOp.up h2)
  cases h

/-- The checked private operation over `c`, by the name `priv`. -/
def callSigma (c : CrtImpl) (f : String) : Option (String × Prog isa) :=
  if f = "priv" then some (Proof.RsaPkcs1Enc.X86_64.privNameP c, Proof.RsaPkcs1Enc.X86_64.privCodeP c) else none

/-- The stack the checked private operation (called) needs. -/
def callStack : String → Nat := fun _ => 3264

theorem callSigma_up (c : CrtImpl) (hl : level c = .sse) :
    ∀ f g d, callSigma c f = some (g, d) → upCallee (.call g d) (callStack f) = true := by
  intro f g d h
  unfold callSigma at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact upCallee_call (m := 3256) _ (priv_up c hl)
  cases h

theorem callSigma_side (c : CrtImpl) (_hl : level c ≠ .sse) :
    ∀ f g d, callSigma c f = some (g, d) → calleeSide (.call g d) (level c).level (callStack f) = true := by
  intro f g d h
  unfold callSigma at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact FillG.calleeSide_call (m := 3256) _ (priv_side c (Nat.le_refl _))
  cases h

end VG.Proof.Rsa.X86_64.PrivScrub

namespace VG.Proof.Rsa.X86_64.PubScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- The public operation `c`, by the name `pub`. -/
def pubSigma (c : PublicImpl) (f : String) : Option (String × Prog isa) :=
  if f = "pub" then some (c.name, c.code) else none

/-- The stack the public operation (called) needs. -/
def pubStack : String → Nat := fun _ => 8

theorem pubSigma_up (c : PublicImpl) (hl : c.level = .sse) :
    ∀ f g d, pubSigma c f = some (g, d) → upCallee (.call g d) (pubStack f) = true := by
  intro f g d h
  unfold pubSigma at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact upCallee_call (m := 0) _ (c.up hl)
  cases h

theorem pubSigma_side (c : PublicImpl) (_hl : c.level ≠ .sse) :
    ∀ f g d, pubSigma c f = some (g, d) → calleeSide (.call g d) c.level.level (pubStack f) = true := by
  intro f g d h
  unfold pubSigma at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact FillG.calleeSide_call (m := 0) _ c.side
  cases h

end VG.Proof.Rsa.X86_64.PubScrub
