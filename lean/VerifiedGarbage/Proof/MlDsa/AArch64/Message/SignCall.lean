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
key, `μ` at `X + 840`, `rnd` and `sig` (`signArgs`), its precondition
(`signC_pre`), and the regions it may read and write (`signRd`, `signWr`).
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

/-- The precondition of `signContract p AArch64.abi 16`, from its facts. -/
theorem signC_pre {p : Params} {s : State} (sp : 16 ≤ s.sp.toNat)
    (rd : s.rd = [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩])
    (wr : s.wr = [⟨s.gpr .x3, p.sigLen⟩, ⟨s.gpr .x4, sScr p⟩])
    (d03 : Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x3, p.sigLen⟩)
    (d04 : Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x4, sScr p⟩)
    (d13 : Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x3, p.sigLen⟩)
    (d14 : Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x4, sScr p⟩)
    (d23 : Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x3, p.sigLen⟩)
    (d24 : Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x4, sScr p⟩)
    (d34 : Region.Disjoint ⟨s.gpr .x3, p.sigLen⟩ ⟨s.gpr .x4, sScr p⟩)
    (k0 : (rStk s).Disjoint ⟨s.gpr .x0, p.skLen⟩) (k1 : (rStk s).Disjoint ⟨s.gpr .x1, 64⟩)
    (k2 : (rStk s).Disjoint ⟨s.gpr .x2, 32⟩) (k3 : (rStk s).Disjoint ⟨s.gpr .x3, p.sigLen⟩)
    (k4 : (rStk s).Disjoint ⟨s.gpr .x4, sScr p⟩)
    (n0 : (s.gpr .x0).toNat + p.skLen ≤ 2 ^ 64) (n1 : (s.gpr .x1).toNat + 64 ≤ 2 ^ 64)
    (n2 : (s.gpr .x2).toNat + 32 ≤ 2 ^ 64) (n3 : (s.gpr .x3).toNat + p.sigLen ≤ 2 ^ 64)
    (n4 : (s.gpr .x4).toNat + sScr p ≤ 2 ^ 64) :
    (signContract p AArch64.abi 16).pre s := by
  sig_pre [signContract, signSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
  exact ⟨sp, rd, wr, d03, d04, d13, d14, d23, d24, d34, k0, k1, k2, k3, k4, n0, n1, n2, n3, n4⟩

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

/-- The regions the signing function on `μ` reads and writes. -/
abbrev signRd (p : Params) (s : State) : List Region :=
  [⟨s.gpr .x0, p.skLen⟩, ⟨(slay p s).MU, 64⟩, ⟨s.gpr .x5, 32⟩]
abbrev signWr (p : Params) (s : State) : List Region := [⟨s.gpr .x6, p.sigLen⟩, ⟨s.gpr .x7, sScr p⟩]

/-- The registers after the moves of the arguments. -/
theorem signRegs_of {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t1 : State}
    (hc : Ctx (slay p s) g vv m₀ t) (hm : (∀ da ∈ signArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .x0 = s.gpr .x0 ∧ t1.gpr .x1 = (slay p s).MU ∧ t1.gpr .x2 = s.gpr .x5 ∧ t1.gpr .x3 = s.gpr .x6 ∧
      t1.gpr .x4 = s.gpr .x7 := by
  have e0 := hm (.x0, .slot fKey) (by simp)
  have e1 := hm (.x1, .off oMU) (by simp)
  have e2 := hm (.x2, .slot fRnd) (by simp)
  have e3 := hm (.x3, .slot fSig) (by simp)
  have e4 := hm (.x4, .slot fScr) (by simp)
  rw [hc.slotV (f := fKey) (j := 0) rfl (by omega_arith)] at e0
  rw [hc.off] at e1
  rw [hc.slotV (f := fRnd) (j := 5) rfl (by omega_arith)] at e2
  rw [hc.slotV (f := fSig) (j := 6) rfl (by omega_arith)] at e3
  rw [hc.slotV (f := fScr) (j := 7) rfl (by omega_arith)] at e4
  simp only [Lay.vals, slay, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3 e4
  exact ⟨e0, e1, e2, e3, e4⟩

end

end VG.Proof.MlDsa.AArch64.Message
