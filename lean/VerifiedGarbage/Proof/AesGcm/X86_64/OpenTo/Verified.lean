module

public import VerifiedGarbage.Proof.AesGcm.Flag
-- separate module: the proof, which needs none of the variants' instances (`Instances.lean`), so that a change to them does not rebuild it

public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.CT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# AES-GCM decryption out of place, x86-64: states satisfying the contracts

Untrusted: everything here is checked by Lean. States satisfying the
preconditions of `vg_aes_gcm_open_to`'s contracts (`toSat`, and with a
prepared key context, `toSatP` and `toSatF`), which `OpenToSplit/Verified.lean`
and `Flag.lean` extend to theirs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenTo

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width)
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

theorem stackArgs_six (s : State) : List.map (stackArg s) (List.range 6) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5] := rfl

/-- A state satisfying the precondition of `vg_aes_gcm_open_to`: no nonce,
additional data, text or tag; `src`, `dst` and `tag` at `0x4000`, `0x5000`
and `0x6000`. -/
def toSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x9000 ≤ a.toNat then
    (if a = 0x9009 then 0x40 else if a = 0x9019 then 0x50 else if a = 0x9029 then 0x60 else 0) else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 48⟩]
  wr := [⟨0x5000, 0⟩]

/-- The key context at `0x1000` is below the stack arguments. -/
theorem ctx_low {i : Nat} (hi : i < 128 * 8) : ¬ (0x9000 ≤ (0x1000 + BitVec.ofNat 64 i : Addr).toNat) := by
  have h : (0x1000 : Addr).toNat = 4096 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), h]
  omega

/-- `toSat`, with a key context of 1024 bytes. -/
def toSatP : State :=
  { toSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 48⟩] }

theorem ctx_lowF {i : Nat} (hi : i < 129 * 8) : ¬ (0x9000 ≤ (0x1000 + BitVec.ofNat 64 i : Addr).toNat) := by
  have h : (0x1000 : Addr).toNat = 4096 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), h]
  omega

/-- `toSat`, with a prepared key context of 1032 bytes. -/
def toSatF : State :=
  { toSat with
    mem := fun a => if a = 0x1400 then 48 else toSat.mem a
    rd := [⟨0x1000, 1032⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 48⟩] }

end VG.Proof.AesGcm.X86_64.OpenTo
