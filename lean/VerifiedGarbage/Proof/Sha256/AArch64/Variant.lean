module

public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Md
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SHA-256 compression backends on AArch64

Each backend supplies its verified compression code and the mechanically
checked constant-time, register and frame facts for the generic streaming
wrappers. The functional streaming proofs are shared by every backend.
HMAC and PBKDF2 consume the resulting streaming functions through `MdHash`.
-/

@[expose] public section

namespace VG.Proof.Sha256.AArch64

open VG.AArch64 VG.Proof.MdStream.AArch64
open VG.Impl.MdStream.AArch64

/-- The one-shot digest with the digest code's parameters `PF`, from the
initial hash value `iv`, calling the compression function `code` named
`name`. -/
def oneShotWith (PF : Params) (iv : Spec.Sha256.HashValue) (name : String) (code : Prog isa) :
    Prog isa :=
  Impl.MdStream.AArch64.OneShot.digest Stream.params PF (Impl.Sha256.AArch64.Stream.initWith iv) name code

/-- The one-shot digest is constant time. -/
abbrev OneShotCT (PF : Params) (D : Nat) (iv : Spec.Sha256.HashValue) (name : String) (code : Prog isa) :
    Prop :=
  ConstantTime isa (MdStream.AArch64.OneShot.oneK (P := Stream.params) md iv D).pre
    (MdStream.AArch64.OneShot.oneK (P := Stream.params) md iv D).pub
    (oneShotWith PF iv name code)

structure Compress where
  name : String
  code : Prog isa
  verified : Verified AArch64.target code Proof.Sha256.compressAArch64
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
  /-- SHA-224's `finalize`, writing its 28-byte digest: as `finalizeCT`,
  `finalizeKeeps` and `finalizeDepth`. -/
  finalize224CT : ConstantTime isa (finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28).pre
    (finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28).pub
    (finalize Impl.Sha256.AArch64.Stream.params224 name code)
  finalize224Keeps : ((instrs (finalizeMain Impl.Sha256.AArch64.Stream.params224 name code)).all fun i =>
    untouched.all fun r => !clobbers i r) = true
  finalize224Depth : (finalizeMain Impl.Sha256.AArch64.Stream.params224 name code).aarch64Depth = 0
  /-- The one-shot digests of SHA-256 and SHA-224. -/
  oneShot256 : OneShotCT Stream.params 32 Spec.Sha256.H0 name code
  oneShot224 : OneShotCT Impl.Sha256.AArch64.Stream.params224 28 Spec.Sha256.H0_224 name code

/-! ## The one-shot digests' common facts -/

namespace OneShot

open MdStream.AArch64.OneShot (oneK initK Fits)

theorem fits : Fits Stream.params := ⟨by decide, by decide, by decide⟩

theorem init_ok (iv : Spec.Sha256.HashValue) :
    ∀ s, (initK (P := Stream.params) md iv).pre s → ∃ t s',
      Exec isa (Impl.Sha256.AArch64.Stream.initWith iv) s t s' ∧ abiPreserved s s' ∧
        (initK (P := Stream.params) md iv).post s s' :=
  fun s h => by
    obtain ⟨t, s', he, h⟩ := Stream.init_correct iv h
    exact ⟨t, s', he, h⟩

theorem init_writes (iv : Spec.Sha256.HashValue) :
    ∀ r, r ≠ .x9 → ∀ i ∈ instrs (Impl.Sha256.AArch64.Stream.initWith iv), clobbers i r = false := by
  intro r hr i hi
  simp only [Impl.Sha256.AArch64.Stream.initWith, instrs, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨k, -, hi⟩ := hi
  rcases hi with rfl | rfl | rfl <;> simp [clobbers, dstOf, Ne.symm hr]

theorem init_keepsV (iv : Spec.Sha256.HashValue) :
    (Impl.Sha256.AArch64.Stream.initWith iv).allInstrs VG.AArch64.keepsV = true := by
  rw [Code.allInstrs_eq]
  simp [Impl.Sha256.AArch64.Stream.initWith, instrs, VG.AArch64.keepsV, vdstOf]

/-- A state satisfying the precondition: an empty message at `0x1000`, the
digest at `0x2000` and the stack pointer at `0x10000`. -/
def sat (D : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 0⟩]
  wr := [⟨0x2000, D⟩]

theorem sat_pre {D : Nat} (hD : D ≤ 64) : MdStream.AArch64.OneShot.Pre Stream.params D (sat D) where
  rd := rfl
  wr := rfl
  d_o := show Region.Disjoint ⟨0x1000, 0⟩ ⟨0x2000, D⟩ from
    Offset.disjoint_of_le (show 4096 + 0 ≤ 8192 by decide) (show 8192 + D ≤ 2 ^ 64 by omega)
  sp := show Impl.MdStream.AArch64.OneShot.frameBytes Stream.params ≤ (0x10000 : BitVec 64).toNat by decide
  f_d := show Region.Disjoint ⟨0x10000 - BitVec.ofNat 64 (Impl.MdStream.AArch64.OneShot.frameBytes Stream.params),
      Impl.MdStream.AArch64.OneShot.frameBytes Stream.params⟩ ⟨0x1000, 0⟩ from
    (Offset.disjoint_of_le (by decide) (by decide)).symm
  f_o := show Region.Disjoint ⟨0x10000 - BitVec.ofNat 64 (Impl.MdStream.AArch64.OneShot.frameBytes Stream.params),
      Impl.MdStream.AArch64.OneShot.frameBytes Stream.params⟩ ⟨0x2000, D⟩ from
    (Offset.disjoint_of_le (show 8192 + D ≤ _ by
      have : 8256 ≤ (0x10000 - BitVec.ofNat 64 (Impl.MdStream.AArch64.OneShot.frameBytes Stream.params) :
        BitVec 64).toNat := by decide
      dsimp only; omega) (by decide)).symm

end OneShot

namespace Compress

variable (v : Compress)

def update : Prog isa := Impl.MdStream.AArch64.update Stream.params v.name v.code
def finalize : Prog isa := Impl.MdStream.AArch64.finalize Stream.params v.name v.code
def finalize224 : Prog isa := Impl.MdStream.AArch64.finalize Impl.Sha256.AArch64.Stream.params224 v.name v.code

theorem callee : CalleeOk (P := Stream.params) md v.code := ⟨v.verified.1, v.noFrames, v.keepsV⟩

theorem update_verified : Verified AArch64.target v.update Proof.Sha256.updateAArch64 := by
  have h := MdStream.AArch64.Update.verified Stream.dims v.callee v.updateCT v.updateKeeps
    (by rw [v.updateDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr hc,
    fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified : Verified AArch64.target v.finalize Proof.Sha256.finalizeAArch64 := by
  have h := MdStream.AArch64.Finalize.verified Stream.dims Stream.shape v.callee v.finalizeCT
    v.finalizeKeeps (by rw [v.finalizeDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr trivial hc,
    fun _ _ _ _ h => h, h.2.2⟩

theorem finalize224_verified :
    Verified AArch64.target v.finalize224 (finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28) :=
  MdStream.AArch64.Finalize.verifiedD (P := Impl.Sha256.AArch64.Stream.params224)
    ⟨Stream.dims.1, Stream.dims.2, Stream.dims.3, Stream.dims.4⟩ Stream.shape224
    (v.callee.withOut _) v.finalize224CT v.finalize224Keeps (by rw [v.finalize224Depth]; decide)

/-- The one-shot digest with the digest code's parameters `PF` (writing `D`
bytes), from `iv`. -/
theorem oneShot_verified {PF : Params} {D : Nat} {iv : Spec.Sha256.HashValue} (hD : D ≤ 64)
    (hPF : PF = { Stream.params with out := PF.out })
    (hs : ShapeD (P := { Stream.params with out := PF.out }) md D)
    (hk : ((instrs (finalizeMain PF v.name v.code)).all fun i =>
      untouched.all fun r => !clobbers i r) = true)
    (hct : OneShotCT PF D iv v.name v.code) :
    Verified AArch64.target (oneShotWith PF iv v.name v.code)
      (MdStream.AArch64.OneShot.oneK (P := Stream.params) md iv D) := by
  rw [hPF] at hk hct ⊢
  exact MdStream.AArch64.OneShot.verified OneShot.fits Stream.dims hs v.callee (OneShot.init_ok iv)
    (OneShot.init_writes iv) rfl (OneShot.init_keepsV iv) v.updateKeeps hk hct
    ⟨_, OneShot.sat_pre hD⟩

end Compress
end VG.Proof.Sha256.AArch64
