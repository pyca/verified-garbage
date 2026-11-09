module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Pre
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Args
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on AArch64, `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. The first `scratchWords p`
words of `scratch` it is given (`sScr`), the arguments of the call on the
key, `μ` at `X + 840`, `rnd` and `sig` (`signArgs`), and where `μ` lies
in `scratch` (`mu_sScr`, `mu_within`, `mu_nowrap`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The size of the working space of the signing function on `μ`. -/
abbrev sScr (p : Params) : Nat := scratchWords p * 8

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs : List (Reg × Arg) := [(.x0, .slot fKey), (.x1, .off oMU), (.x2, .slot fRnd), (.x3, .slot fSig),
  (.x4, .slot fScr)]

section
variable {p : Params} {s : State}

theorem gpr_ce (t : State) {r : Reg} {rd wr : List Region} (h : r ∉ linkRegs := by decide) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- The working space of the signing function on `μ`: the start of `scratch`. -/
theorem sScr_sub (p : Params) (s : State) :
    Region.Sub ⟨s.gpr .x7, sScr p⟩ ⟨s.gpr .x7, mScrLen p⟩ :=
  Region.sub_prefix (by rw [mScr_eq]; simp only [sScr, oE]; omega_arith)

/-- The saves are apart from it. -/
theorem sv_sScr {p : Params} (hp : p ∈ params) (s : State) {d n : Nat} (hd : d + n ≤ 88) :
    Region.Disjoint ⟨(slay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .x7, sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x7 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ _
  rw [add_add, add_add]
  have := oE_lt hp
  exact Offset.disjoint_base _ (by simp only [sScr, oE]; omega_arith) (by omega_arith)

theorem mu_sScr {p : Params} (hp : p ∈ params) (s : State) :
    Region.Disjoint ⟨(slay p s).MU, 64⟩ ⟨s.gpr .x7, sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x7 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 840, 64⟩ _
  rw [add_add]
  have := oE_lt hp
  exact Offset.disjoint_base _ (by simp only [sScr, oE]; omega_arith) (by omega_arith)

theorem mu_within (p : Params) (s : State) : Within ⟨(slay p s).MU, 64⟩ ⟨s.gpr .x7, mScrLen p⟩ :=
  (within_off (slay p s).X (d := 840) (n := 64) (k := 1024) (by omega_arith)).trans (slay_X p s)

theorem mu_nowrap {L : Lay} (hL : L.Ok) : L.MU.toNat + 64 ≤ 2 ^ 64 := by
  have := hL.nX
  show (L.X + BitVec.ofNat 64 840).toNat + 64 ≤ 2 ^ 64
  rw [toNat_add_ofNat (by omega_arith)]; omega_arith

end

end VG.Proof.MlDsa.AArch64.Message
