module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Lit
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
meta import VerifiedGarbage.Proof.Weierstrass.CombW
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.AArch64.Comb
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.AArch64.Comb
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
import VerifiedGarbage.Proof.BrainpoolP256r1.Comb7
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombGeneral
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
meta import VerifiedGarbage.Proof.BrainpoolP256r1.Comb7
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombGeneral

/-! ### `Ecdsa.AArch64.BrainpoolP256r1.Comb.Correct`, which only this module used -/

section

/-! # brainpoolP256r1 signing: the general-curve comb computes [k]G -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP256r1
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

theorem cfg_ok (hI : InvSounds) : BaseCfgOk combCfg where
  n0 := (brainpoolp256r1_ok hI).n0
  n10 := (brainpoolp256r1_ok hI).n10
  onG := (brainpoolp256r1_ok hI).onG
  p_odd := (brainpoolp256r1_ok hI).p_odd
  n_odd := (brainpoolp256r1_ok hI).n_odd
  p_lt := (brainpoolp256r1_ok hI).p_lt
  n_lt := (brainpoolp256r1_ok hI).n_lt
  p_ge := (brainpoolp256r1_ok hI).p_ge
  n_ge := (brainpoolp256r1_ok hI).n_ge
  p_lt_2n := (brainpoolp256r1_ok hI).p_lt_2n
  minv_p := (brainpoolp256r1_ok hI).minv_p
  minv_n := (brainpoolp256r1_ok hI).minv_n
  red_p := (brainpoolp256r1_ok hI).red_p
  red_n := (brainpoolp256r1_ok hI).red_n
  len8 := (brainpoolp256r1_ok hI).len8
  len_lo := (brainpoolp256r1_ok hI).len_lo
  len_hi := (brainpoolp256r1_ok hI).len_hi
  sh := (brainpoolp256r1_ok hI).sh
  n4 := (brainpoolp256r1_ok hI).n4
  sound_p := (brainpoolp256r1_ok hI).sound_p
  inv_p := (brainpoolp256r1_ok hI).inv_p
  inv_n := (brainpoolp256r1_ok hI).inv_n
  chain_n := (brainpoolp256r1_ok hI).chain_n
  call_p := (brainpoolp256r1_ok hI).call_p
  call_n := (brainpoolp256r1_ok hI).call_n
  inv_at := (brainpoolp256r1_ok hI).inv_at
  inv_fn := (brainpoolp256r1_ok hI).inv_fn
  check_fn := (brainpoolp256r1_ok hI).check_fn
  padd := fun h => absurd rfl h

theorem correct (hC : Law Spec.BrainpoolP256r1.curve) (hI : InvSounds) :
    CombCorrect combCfg comb := by
  have hc := cfg_ok hI
  intro base k T s hs hm hf
  exact WP.mono (generalComb_ok (tcombLay hc) (combA hc) hC b3 (mont_lt hc _)
    (by
      show toM combCfg.C.p (2 ^ (64 * combCfg.n)) (combCfg.mont (3 * combCfg.C.b)) = _
      rw [toM_cmont hc]; rfl) hc.onG
    (tcombVals hc hC (Proof.BrainpoolP256r1.combOk7 hC)) hc.p_lt hs hm hf)
    fun s' ⟨K,U,M,L,R⟩ => ⟨K,U.mono fun w hw => List.mem_append_left _ hw,M,L,R⟩

end VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb

end

end

/-! ### `Ecdsa.AArch64.BrainpoolP256r1.Comb.Contract`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.AArch64.BrainpoolP256r1.Comb.Tables`, which this module and modules that import it used -/

section

/-!
# ECDSA over brainpoolP256r1 on AArch64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `combCfg.tsym`, not wrapping
around, and apart from the writable regions; their length
(`combCfg_combWords_length`, from the tables' shape alone); and a memory
holding them, for the contracts' witnesses (`satMem`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb

open VG VG.AArch64
open VG.Impl.Ecdsa.AArch64.BrainpoolP256r1 (combCfg)

/-- The comb's tables at the static `combCfg.tsym`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < combCfg.combWords.length,
    s.mem.readW (s.syms combCfg.tsym + BitVec.ofNat 64 (8 * i)) 64 = combCfg.combWords.getD i 0) ∧
  (s.syms combCfg.tsym).toNat + 8 * combCfg.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms combCfg.tsym, 8 * combCfg.combWords.length⟩ r

theorem combCfg_tbl_len : Impl.BrainpoolP256r1.comb7.length = 37 :=
  by decide +kernel

theorem combCfg_tbl_lenH : ∀ j < 37, (Impl.BrainpoolP256r1.comb7.getD j []).length = 64 :=
  by decide +kernel

/-- `combCfg.combWords` has `37 · 64 · 8` words. -/
theorem combCfg_combWords_length : combCfg.combWords.length = 18944 :=
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

end VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb

end

end

/-!
# ECDSA over brainpoolP256r1 on AArch64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP256r1.inst` for AArch64, under the
calling convention with the comb's tables (`Abi.withConsts combCfg.combConsts`),
by name: `vg_ecdsa_combCfg_sign(out = x0, d = x1, digest = x2, k = x3,
scratch = x4)`, the result in `w0`, and the tables at the address of the
static `combCfg.tsym`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.AArch64.BrainpoolP256r1 (combCfg)

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.BrainpoolP256r1.curve (ofBytes (bytesAt m d 32)) (hashToInt Spec.BrainpoolP256r1.curve (bytesAt m digest 32))
    (ofBytes (bytesAt m k 32))

def signAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 64⟩
    let d : Region := ⟨s.gpr .x1, 32⟩
    let digest : Region := ⟨s.gpr .x2, 32⟩
    let k : Region := ⟨s.gpr .x3, 32⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k, ⟨s.syms combCfg.tsym, 8 * combCfg.combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch]
  post s s' :=
    match sig s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 64 = encode Spec.BrainpoolP256r1.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    s₁.syms combCfg.tsym = s₂.syms combCfg.tsym

end VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb

end

end

/-! # brainpoolP256r1 fixed-base signing: correctness, ABI and constant time

The generic signing proof composes the general-curve comb with the existing
input validation, inversions, scalar arithmetic and output masking.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP256r1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem pre_of {s : State} (h : signAArch64.pre s) : Pre combCfg s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem sign_a64 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds)
    (s : State)
    (hs : signAArch64.pre s) :
    ∃ t s', Exec isa signComb s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := signWith_ok (cfg_ok hI) hL comb (correct hL hI) (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, hpost⟩

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

end VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb
