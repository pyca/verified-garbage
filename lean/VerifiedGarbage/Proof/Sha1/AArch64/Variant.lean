module

public import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Md
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Init
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SHA-1 compression backends on AArch64

Each backend supplies its verified compression code and the mechanically
checked constant-time, register and frame facts for the generic streaming
wrappers. The functional streaming proofs are shared by every backend.
HMAC and PBKDF2 consume the resulting streaming functions through `MdHash`.
-/

@[expose] public section

namespace VG.Proof.Sha1.AArch64

open VG.AArch64 VG.Proof.MdStream.AArch64
open VG.Impl.MdStream.AArch64

/-- The one-shot digest, calling the compression function `code` named
`name`. -/
def oneShotWith (name : String) (code : Prog isa) : Prog isa :=
  Impl.MdStream.AArch64.OneShot.digest Stream.params Impl.Sha1.AArch64.Stream.init name code

/-- The one-shot digest is constant time. -/
abbrev OneShotCT (name : String) (code : Prog isa) : Prop :=
  ConstantTime isa (MdStream.AArch64.OneShot.oneK (P := Stream.params) md Spec.Sha1.H0 20).pre
    (MdStream.AArch64.OneShot.oneK (P := Stream.params) md Spec.Sha1.H0 20).pub (oneShotWith name code)

structure Compress where
  name : String
  code : Prog isa
  verified : Verified AArch64.target code Proof.Sha1.compressAArch64
  noFrames : code.noFrames = true
  /-- Current streaming wrappers require untouched callee-saved SIMD registers. -/
  keepsV : code.allInstrs keepsV = true
  suffix : String
  features : List String
  updateCT : ConstantTime isa (updK (P := Stream.params) md).pre
    (updK (P := Stream.params) md).pub (update Stream.params name code)
  finalizeCT : ConstantTime isa (finK (P := Stream.params) md).pre
    (finK (P := Stream.params) md).pub (finalize Stream.params name code)
  updateKeeps : ((instrs (updateMain Stream.params name code)).all fun i =>
    untouched.all fun r => !clobbers i r) = true
  finalizeKeeps : ((instrs (finalizeMain Stream.params name code)).all fun i =>
    untouched.all fun r => !clobbers i r) = true
  updateDepth : (updateMain Stream.params name code).aarch64Depth = 0
  finalizeDepth : (finalizeMain Stream.params name code).aarch64Depth = 0
  /-- The one-shot digest. -/
  oneShot : OneShotCT name code

/-! ## The one-shot digest's common facts -/

namespace OneShot

open MdStream.AArch64.OneShot (initK Fits)

theorem fits : Fits Stream.params := ⟨by decide⟩

theorem init_ok :
    ∀ s, (initK (P := Stream.params) md Spec.Sha1.H0).pre s → ∃ t s',
      Exec isa Impl.Sha1.AArch64.Stream.init s t s' ∧ abiPreserved s s' ∧
        (initK (P := Stream.params) md Spec.Sha1.H0).post s s' := fun s h => by
  obtain ⟨t, s', he, h⟩ := Stream.init_correct h
  exact ⟨t, s', he, h⟩

theorem init_writes :
    ∀ r, r ≠ .x9 → r ≠ .x10 → ∀ i ∈ instrs Impl.Sha1.AArch64.Stream.init, clobbers i r = false := by
  intro r h9 _ i hi
  simp only [Impl.Sha1.AArch64.Stream.init, instrs, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  obtain ⟨_, _, rfl | rfl | rfl⟩ := hi <;> simp [clobbers, dstOf, Ne.symm h9]

theorem init_keepsV : Impl.Sha1.AArch64.Stream.init.allInstrs VG.AArch64.keepsV = true := by
  rw [Code.allInstrs_eq]
  simp only [Impl.Sha1.AArch64.Stream.init, instrs, List.all_eq_true, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ ⟨_, _, rfl | rfl | rfl⟩ <;> rfl

/-- A state satisfying the precondition: an empty message at `0x1000`, the
digest at `0x2000` and the stack pointer at `0x10000`. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 0⟩]
  wr := [⟨0x2000, 20⟩]

theorem sat_pre : MdStream.AArch64.OneShot.Pre Stream.params 20 sat where
  rd := rfl
  wr := rfl
  d_o := show Region.Disjoint ⟨0x1000, 0⟩ ⟨0x2000, 20⟩ from
    Offset.disjoint_of_le (show 4096 + 0 ≤ 8192 by decide) (by decide)
  sp := show Impl.MdStream.AArch64.OneShot.frameBytes Stream.params ≤ (0x10000 : BitVec 64).toNat by decide
  f_d := show Region.Disjoint ⟨0x10000 - BitVec.ofNat 64 (Impl.MdStream.AArch64.OneShot.frameBytes Stream.params),
      Impl.MdStream.AArch64.OneShot.frameBytes Stream.params⟩ ⟨0x1000, 0⟩ from
    (Offset.disjoint_of_le (by decide) (by decide)).symm
  f_o := show Region.Disjoint ⟨0x10000 - BitVec.ofNat 64 (Impl.MdStream.AArch64.OneShot.frameBytes Stream.params),
      Impl.MdStream.AArch64.OneShot.frameBytes Stream.params⟩ ⟨0x2000, 20⟩ from
    (Offset.disjoint_of_le (by decide) (by decide)).symm

end OneShot

namespace Compress

variable (v : Compress)

def update : Prog isa := Impl.MdStream.AArch64.update Stream.params v.name v.code
def finalize : Prog isa := Impl.MdStream.AArch64.finalize Stream.params v.name v.code

theorem callee : CalleeOk (P := Stream.params) md v.code := ⟨v.verified.1, v.noFrames, v.keepsV⟩

theorem update_verified : Verified AArch64.target v.update Proof.Sha1.updateAArch64 := by
  have h := MdStream.AArch64.Update.verified Stream.dims v.callee v.updateCT v.updateKeeps
    (by rw [v.updateDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr hc,
    fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified : Verified AArch64.target v.finalize Proof.Sha1.finalizeAArch64 := by
  have h := MdStream.AArch64.Finalize.verified Stream.dims Stream.shape v.callee v.finalizeCT
    v.finalizeKeeps (by rw [v.finalizeDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr trivial hc,
    fun _ _ _ _ h => h, h.2.2⟩

/-- The one-shot digest. -/
theorem oneShot_verified :
    Verified AArch64.target (oneShotWith v.name v.code)
      (MdStream.AArch64.OneShot.oneK (P := Stream.params) md Spec.Sha1.H0 20) :=
  MdStream.AArch64.OneShot.verified OneShot.fits Stream.dims Stream.shape.toD v.callee OneShot.init_ok
    OneShot.init_writes rfl OneShot.init_keepsV v.oneShot ⟨_, OneShot.sat_pre⟩

end Compress
end VG.Proof.Sha1.AArch64
