module

-- separate module: cache the constant-time and ABI checks independently of RFC 6979 table composition
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.Correct
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP512r1Literals
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
meta import VerifiedGarbage.Proof.Weierstrass.CombW
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.Correct
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP512r1Literals
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.AArch64.Comb
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.AArch64.Comb
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ecdsa.AArch64.BrainpoolP512r1.Comb.Contract`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.AArch64.BrainpoolP512r1.Comb.Tables`, which this module and modules that import it used -/

section

/-!
# ECDSA over brainpoolP512r1 on AArch64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `combCfg.tsym`, not wrapping
around, and apart from the writable regions; their length
(`combCfg_combWords_length`, from the tables' shape alone); and a memory
holding them, for the contracts' witnesses (`satMem`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb

open VG VG.AArch64
open VG.Impl.Ecdsa.AArch64.BrainpoolP512r1 (combCfg)

/-- The comb's tables at the static `combCfg.tsym`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < combCfg.combWords.length,
    s.mem.readW (s.syms combCfg.tsym + BitVec.ofNat 64 (8 * i)) 64 = combCfg.combWords.getD i 0) ∧
  (s.syms combCfg.tsym).toNat + 8 * combCfg.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms combCfg.tsym, 8 * combCfg.combWords.length⟩ r

theorem combCfg_tbl_len : Impl.BrainpoolP512r1.comb7.length = 74 :=
  by decide +kernel

theorem combCfg_tbl_lenH : ∀ j < 74, (Impl.BrainpoolP512r1.comb7.getD j []).length = 64 :=
  by decide +kernel

/-- `combCfg.combWords` has `74 · 64 · 16` words. -/
theorem combCfg_combWords_length : combCfg.combWords.length = 75776 :=
  (Proof.Weierstrass.tcombWords_length (n := combCfg.n) (R := combCfg.R) (p := combCfg.C.p)
    (H := 64) (tbl := combCfg.tbl) combCfg_tbl_len combCfg_tbl_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 combCfg.combWords

theorem satMem_held : ∀ i < combCfg.combWords.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combCfg.combWords.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [combCfg_combWords_length]; omega_using [])

end VG.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb

end

end

/-!
# ECDSA over brainpoolP512r1 on AArch64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst` for AArch64, under the
calling convention with the comb's tables (`Abi.withConsts combCfg.combConsts`),
by name: `vg_ecdsa_combCfg_sign(out = x0, d = x1, digest = x2, k = x3,
scratch = x4)`, the result in `w0`, and the tables at the address of the
static `combCfg.tsym`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.AArch64.BrainpoolP512r1 (combCfg)

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.BrainpoolP512r1.curve (ofBytes (bytesAt m d 64)) (hashToInt Spec.BrainpoolP512r1.curve (bytesAt m digest 64))
    (ofBytes (bytesAt m k 64))

def signAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 128⟩
    let d : Region := ⟨s.gpr .x1, 64⟩
    let digest : Region := ⟨s.gpr .x2, 64⟩
    let k : Region := ⟨s.gpr .x3, 64⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k, ⟨s.syms combCfg.tsym, 8 * combCfg.combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch]
  post s s' :=
    match sig s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 128 = encode Spec.BrainpoolP512r1.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 128 = List.replicate 128 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    s₁.syms combCfg.tsym = s₂.syms combCfg.tsym

end VG.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb

end

end

/-! # brainpoolP512r1 fixed-base signing: correctness, ABI and constant time

The generic signing proof composes the general-curve comb with the existing
input validation, inversions, scalar arithmetic and output masking.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP512r1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem pre_of {s : State} (h : signAArch64.pre s) : Pre combCfg s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem sign_a64 (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.AArch64.InvSounds)
    (s : State)
    (hs : signAArch64.pre s) :
    ∃ t s', Exec isa signComb s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := signWith_ok (cfg_ok hI) hL comb (correct hL hI) (pre_of hs)
  exact ⟨t, s', he, abiPreserved_ofK he (by lit_decide) hsv, hpost⟩

theorem sign_ct : ConstantTime isa signAArch64.pre signAArch64.pub signComb :=
  VG.Taint.constantTime (A := taintS [combCfg.tsym]) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

end VG.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb
