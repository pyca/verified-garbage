module

public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public meta import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
public meta import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Cast5.Rounds
public meta import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public meta import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub
public meta import VerifiedGarbage.Impl.Residue.AArch64.Scrub
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueScrub
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueScrub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

-- separate module: only the registrations need it, and it imports the proofs of the modes, which the residue analysis would otherwise be built with

/-!
# CAST5-OFB on AArch64 returns without secret residue

`vg_cast5_ofb` and `vg_cast5_ofb_final` run their mode in a 112-byte frame
whose scratch words they zero (`withStackScratchWiped 112 .x5 13`). After it,
they clear what the analysis through calls and frames (`rtaintF`) finds
secret in their registers (`ofbCleared`: the halves of the block, the
S-box lookups, the vector registers that held the keystream and the flags,
from `x4`), and then the 112 bytes of stack their frame used (`withScrub`).
`RTaintF.noResidue_withScrub` proves they then leave nothing secret. Their
postconditions read the memory on return only within the buffers: the data
and the chaining block (`ofbOut`, `ofbFinalOut`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.FbResidue

open VG VG.AArch64 VG.Impl.Residue.AArch64 VG.AArch64.RTaintF

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

theorem agree_le (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

theorem bytesAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact agree_le h hn _ (List.mem_range.mp hi)

theorem cbcBlocksAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 8 ≤ L) :
    Spec.Cast5.cbcBlocksAt m₂ p n = Spec.Cast5.cbcBlocksAt m₁ p n := by
  simp only [Spec.Cast5.cbcBlocksAt, Spec.Cast5.blocksAt]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  apply Vector.ext
  intro j hj
  simp only [Spec.Cast5.blockAt, Vector.getElem_ofFn]
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega_using [this, hj])

end

/-! ## Postconditions -/

theorem ofbScrubOk :
    ScrubOk (Spec.Cast5.ofbContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 112 :=
  scrubOk_consts (sig := Spec.Cast5.ofbSig) (c₀ := (Impl.Cast5.s1234Sym, Impl.Cast5.s1234)) (cs := [])
    (W := 112) (by decide) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      obtain ⟨h₁, h₂⟩ := h key hk
      exact ⟨(cbcBlocksAt_of0 hb.2.2 (Nat.le_refl _)).trans h₁,
        (bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)).trans h₂⟩

/-! ## The code -/

/-- `c`, then what CAST5-OFB leaves in its registers cleared. -/
abbrev ofbCleared (c : Prog isa) : Prog isa :=
  withClears [.x4, .x6, .x7, .x10, .x13, .x14, .x15]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v16, .v17, .v18, .v19] (some .x4) c

abbrev ofbBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.ofb)

abbrev ofbCode : Prog isa := withScrub 112 ofbBase

theorem ofbBase_verified : Verified AArch64.target ofbBase
    (Spec.Cast5.ofbContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  Clears.Verified.withClears_of (Proof.Cast5.ofb_keyed Proof.Cast5.AArch64.ofb_framed)
    (fun hq hm hx => post_consts.mpr (Clears.post_congr (post_consts.mp hq) hm hx)) (by decide)

theorem ofbCode_verified : Verified AArch64.target ofbCode
    (Spec.Cast5.ofbContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  RTaintF.Verified.withScrubK ofbBase_verified ⟨by decide, by decide, by decide⟩ ofbScrubOk

theorem ofbCode_noResidue : NoResidue ofbCode
    (Spec.Cast5.ofbContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 0 :=
  RTaintF.noResidue_withScrub ofbBase_verified ⟨by decide, by decide, by decide⟩ ofbScrubOk.sp
    ⟨_, by taint_decide_ct⟩

theorem ofbFinalScrubOk :
    ScrubOk (Spec.Cast5.ofbFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 112 :=
  scrubOk_consts (sig := Spec.Cast5.ofbFinalSig) (c₀ := (Impl.Cast5.s1234Sym, Impl.Cast5.s1234)) (cs := [])
    (W := 112) (by decide) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      obtain ⟨h₁, h₂⟩ := h key hk
      exact ⟨(bytesAt_of0 hb.2.2 (Nat.le_of_eq (Nat.mul_one _).symm)).trans h₁,
        (bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)).trans h₂⟩

abbrev ofbFinalBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.ofbFinal)

abbrev ofbFinalCode : Prog isa := withScrub 112 ofbFinalBase

theorem ofbFinalBase_verified : Verified AArch64.target ofbFinalBase
    (Spec.Cast5.ofbFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  Clears.Verified.withClears_of (Proof.Cast5.ofbFinal_keyed Proof.Cast5.AArch64.ofbFinal_framed)
    (fun hq hm hx => post_consts.mpr (Clears.post_congr (post_consts.mp hq) hm hx)) (by decide)

theorem ofbFinalCode_verified : Verified AArch64.target ofbFinalCode
    (Spec.Cast5.ofbFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  RTaintF.Verified.withScrubK ofbFinalBase_verified ⟨by decide, by decide, by decide⟩ ofbFinalScrubOk

theorem ofbFinalCode_noResidue : NoResidue ofbFinalCode
    (Spec.Cast5.ofbFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 0 :=
  RTaintF.noResidue_withScrub ofbFinalBase_verified ⟨by decide, by decide, by decide⟩
    ofbFinalScrubOk.sp ⟨_, by taint_decide_ct⟩

end VG.Proof.Cast5.AArch64.FbResidue
