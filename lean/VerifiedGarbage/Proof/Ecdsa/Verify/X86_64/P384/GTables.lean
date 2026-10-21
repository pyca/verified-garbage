module

public import VerifiedGarbage.Impl.P384.X86_64.Joint
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P384.GTable9Shape
import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables

/-!
# ECDSA verification over P-384 on x86-64: the table of the generator's multiples in a static

What the verifier's contract says of its one table, `p384GTab` (`TblHeldG`):
held at the address of the static `VG_P384_GTAB`, not wrapping around, and
apart from the writable regions and the return address; its length
(`p384GW_length`, from the table's shape alone); and a memory holding it, for
the contract's witness (`satMemG`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P384

open VG VG.X86_64
open VG.Impl.Ecdsa.X86_64 (Cfg)
open VG.Impl.P384.X86_64 (p384v p384vx p384GTab)

/-- The words of the verifier's table. -/
abbrev p384GW : List (BitVec 64) := p384v.combWords p384GTab

theorem p384v_gtab : p384v.gtab = some p384GTab := rfl

theorem p384vx_gtab : p384vx.gtab = some p384GTab := rfl

/-- The fields of `p384v` and `p384vx` the tables of constants read,
rewritten rather than compared by unfolding (which would evaluate `R`). -/
theorem p384v_comb : p384v.comb = none := rfl

theorem p384vx_comb : p384vx.comb = none := rfl

theorem p384vx_Cv : p384vx.C = p384v.C := rfl

theorem p384vx_nv : p384vx.n = p384v.n := rfl

theorem p384vx_combWords : p384vx.combWords p384GTab = p384GW := by
  unfold p384GW Cfg.combWords Cfg.R
  rw [p384vx_Cv, p384vx_nv]

theorem p384v_combConsts : p384v.combConsts = [("VG_P384_GTAB", p384GW)] := by
  unfold Cfg.combConsts
  rw [p384v_comb, p384v_gtab]
  rfl

theorem p384vx_combConsts : p384vx.combConsts = [("VG_P384_GTAB", p384GW)] := by
  unfold Cfg.combConsts
  rw [p384vx_comb, p384vx_gtab]
  exact congrArg (fun w => [("VG_P384_GTAB", w)]) p384vx_combWords

/-- The table at the static `VG_P384_GTAB`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeldG (s : State) (wr : List Region) : Prop :=
  (∀ i < p384GW.length, s.mem.readW (s.syms "VG_P384_GTAB" + BitVec.ofNat 64 (8 * i)) 64 = p384GW.getD i 0) ∧
  (s.syms "VG_P384_GTAB").toNat + 8 * p384GW.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_P384_GTAB", 8 * p384GW.length⟩ r

/-- `p384GW` has `256 · 12` words. -/
theorem p384GW_length : p384GW.length = 3072 :=
  (Proof.Weierstrass.tcombWords_length (n := p384v.n) (R := p384v.R) (p := p384v.C.p)
    (H := 256) (tbl := Impl.P384.p384G9) Proof.P384.p384G9_length Proof.P384.p384G9_rows).trans rfl

/-- The table's region, `8 · 3072` bytes at the static's address (see
`p384_constRegions`). -/
theorem p384G_constRegions (f : String → BitVec 64) :
    Abi.constRegions f [("VG_P384_GTAB", p384GW)] = [⟨f "VG_P384_GTAB", 24576⟩] := by
  rw [Proof.Ecdsa.X86_64.constRegions_single, p384GW_length]

/-- The memory of the contract's witness: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMemG : Mem := constMem 0x100000 p384GW

theorem satMemG_held : ∀ i < p384GW.length,
    satMemG.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p384GW.getD i 0 := by
  unfold satMemG
  exact constMem_held _ _ (by rw [p384GW_length]; omega)

end VG.Proof.Ecdsa.Verify.X86_64.P384
