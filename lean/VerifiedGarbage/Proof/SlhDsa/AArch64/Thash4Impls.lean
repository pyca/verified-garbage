module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Impl
public import VerifiedGarbage.Proof.Sha3.AArch64.X2Variant
import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Correct
import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4CT
import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

-- separate module: the variant list (`Proof/Variants/SlhDsaThash4/AArch64.lean`) only names the implementations; their records and the facts they are built from are the algorithm's proofs.

/-!
# SLH-DSA on AArch64: the implementations of `thash4`

`Thash4.thash4 n sha3` meets `thash4Contract n` for `n` 16, 24 and 32
(`thash4_verified`): its correctness (`Thash4.correct`), its constant time
(`Thash4.ct`) and a state its precondition holds in. An implementation for
each two-way Keccak-f[1600] (`X2Permutation`, `Proof/Variants/KeccakX2/AArch64.lean`)
is `ofX2`, named with the permutation's suffix.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64

open VG VG.AArch64

/-- A state `thash4`'s precondition holds in, for outputs of `n` bytes. -/
def thash4Sat (n : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 128 | .x2 => 8 | .x3 => BitVec.ofNat 64 (0x10000 + n + 32) | .x4 => 0x20000
    | _ => 0
  sp := 0x40000
  mem _ := 0
  rd := []
  wr := [⟨0x10000, 512⟩, ⟨0x20000, 1024⟩]

theorem thash4Sat_pre (n : Nat) (hn : n = 16 ∨ n = 24 ∨ n = 32) : Thash4Pre n (thash4Sat n) := by
  rcases hn with rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide, by decide,
      by decide, by decide⟩

/-- `thash4` for outputs of `n` bytes, over the two-way permutation with
FEAT_SHA3 (`sha3`) or in general registers, meets its contract. -/
theorem thash4_verified (n : Nat) (hn : n = 16 ∨ n = 24 ∨ n = 32) (sha3 : Bool) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Thash4.thash4 n sha3) (thash4Contract n) :=
  ⟨fun _ hs => Thash4.correct hs (by rcases hn with rfl | rfl | rfl <;> decide)
      (by rcases hn with rfl | rfl | rfl <;> decide) sha3,
    Thash4.ct n hn sha3, ⟨_, thash4Sat_pre n hn⟩⟩

theorem thash4_noFrames (n : Nat) (hn : n = 16 ∨ n = 24 ∨ n = 32) (sha3 : Bool) :
    (Impl.SlhDsa.AArch64.Thash4.thash4 n sha3).noFrames = true := by
  rcases hn with rfl | rfl | rfl <;> cases sha3 <;> lit_decide

theorem thash4_side (n : Nat) (hn : n = 16 ∨ n = 24 ∨ n = 32) (sha3 : Bool) :
    Scrub.sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Thash4.thash4 n sha3) = true := by
  rcases hn with rfl | rfl | rfl <;> cases sha3 <;> lit_decide

theorem thash4_depth (n : Nat) (hn : n = 16 ∨ n = 24 ∨ n = 32) (sha3 : Bool) :
    (Impl.SlhDsa.AArch64.Thash4.thash4 n sha3).aarch64Depth = 0 := by
  rcases hn with rfl | rfl | rfl <;> cases sha3 <;> lit_decide

/-- `thash4` for outputs of `n` bytes over the two-way permutation `v`,
named with its suffix. -/
def Thash4Impl.ofX2 (n : Nat) (hn : n = 16 ∨ n = 24 ∨ n = 32) (v : Proof.Sha3.AArch64.X2Permutation) :
    Thash4Impl n where
  sfx := v.suffix
  sha3 := v.sha3
  code := Impl.SlhDsa.AArch64.Thash4.thash4 n v.sha3
  code_eq := rfl
  verified := thash4_verified n hn v.sha3
  noFrames := thash4_noFrames n hn v.sha3
  side := thash4_side n hn v.sha3
  depth := thash4_depth n hn v.sha3

end VG.Proof.SlhDsa.AArch64
