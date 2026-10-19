module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
public import VerifiedGarbage.Proof.X25519.Invert
public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep

/-!
# Ed25519 and X25519 on AArch64: the inversion by divsteps

Untrusted: everything here is checked by Lean. `Divstep.invert` leaves
`[slot 15] ≡ [slot 2]^(p - 2)` (`invert_ok`), given `Sound`: its proof, from
the batches' invariant (`Inv/`), the divsteps' termination and Fermat, is in
`DivstepSound`, so that the modules that call the inversion import none of the
algebra it takes.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64 (KeepRegs)

variable {large : Bool}

instance : NeZero Spec.X25519.P := ⟨by decide⟩

/-- The inversion by divsteps is correct: `DivstepSound.lean`. -/
class Sound : Prop where
  invert_ok : ∀ {large : Bool} {s : State} {base : Addr}, Scr s base large →
    WP isa VG.Impl.Ed25519.AArch64.Divstep.invert s fun t =>
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) ∧
      KeepRegs (.x19 :: VG.Proof.Mont.AArch64.clob 4 ++ ([.x2, .x20] : List Reg)) s t ∧
      t.gpr .x1 = s.gpr .x1 ∧ Outside base 192 512 s.mem t.mem

/-- `[slot 15] = [slot 2]^(p - 2)`. -/
theorem invert_ok [Sound] {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa VG.Impl.Ed25519.AArch64.Divstep.invert s fun t =>
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) ∧
      KeepRegs (.x19 :: VG.Proof.Mont.AArch64.clob 4 ++ ([.x2, .x20] : List Reg)) s t ∧
      t.gpr .x1 = s.gpr .x1 ∧ Outside base 192 512 s.mem t.mem :=
  Sound.invert_ok hs

end VG.Proof.Ed25519.AArch64.Divstep
