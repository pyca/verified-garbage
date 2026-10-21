module

public import VerifiedGarbage.Impl.P256.X86_64.Joint
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P256.GTable9Shape
import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables

/-!
# ECDSA verification over P-256 on x86-64: the table of the generator's multiples in a static

What the verifier's contract says of its one table, `p256GTab` (`TblHeldG`):
held at the address of the static `VG_P256_GTAB`, not wrapping around, and
apart from the writable regions and the return address; its length
(`p256GW_length`, from the table's shape alone); and a memory holding it, for
the contract's witness (`satMemG`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64
open VG.Impl.Ecdsa.X86_64 (Cfg)
open VG.Impl.P256.X86_64 (p256v p256vx p256GTab)

/-- The words of the verifier's table. -/
abbrev p256GW : List (BitVec 64) := p256v.combWords p256GTab

theorem p256v_gtab : p256v.gtab = some p256GTab := rfl

theorem p256vx_gtab : p256vx.gtab = some p256GTab := rfl

theorem p256v_combConsts : p256v.combConsts = [("VG_P256_GTAB", p256GW)] := rfl

theorem p256vx_combConsts : p256vx.combConsts = [("VG_P256_GTAB", p256GW)] := rfl

/-- The table at the static `VG_P256_GTAB`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeldG (s : State) (wr : List Region) : Prop :=
  (∀ i < p256GW.length, s.mem.readW (s.syms "VG_P256_GTAB" + BitVec.ofNat 64 (8 * i)) 64 = p256GW.getD i 0) ∧
  (s.syms "VG_P256_GTAB").toNat + 8 * p256GW.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_P256_GTAB", 8 * p256GW.length⟩ r

/-- `p256GW` has `256 · 8` words. -/
theorem p256GW_length : p256GW.length = 2048 :=
  (Proof.Weierstrass.tcombWords_length (n := p256v.n) (R := p256v.R) (p := p256v.C.p)
    (H := 256) (tbl := Impl.P256.p256G9) Proof.P256.p256G9_length Proof.P256.p256G9_rows).trans rfl

/-- The table's region, `8 · 2048` bytes at the static's address (see
`p256_constRegions`). -/
theorem p256G_constRegions (f : String → BitVec 64) :
    Abi.constRegions f [("VG_P256_GTAB", p256GW)] = [⟨f "VG_P256_GTAB", 16384⟩] := by
  rw [Proof.Ecdsa.X86_64.constRegions_single, p256GW_length]

/-- The memory of the contract's witness: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMemG : Mem := constMem 0x100000 p256GW

theorem satMemG_held : ∀ i < p256GW.length,
    satMemG.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p256GW.getD i 0 := by
  unfold satMemG
  exact constMem_held _ _ (by rw [p256GW_length]; omega)

end VG.Proof.Ecdsa.Verify.X86_64
