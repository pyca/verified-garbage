module

public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly

/-! ### `MlDsa.AArch64.Optimized.ResponseHintWord`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResponseHintMath`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round

/-- Exact hint predicate, including the exceptional negative boundary at high zero. -/
abbrev hintPredicate (g : Nat) (t high : Int) : Prop :=
  (g:Int)<t ∨ t< -(g:Int) ∨ (t= -(g:Int) ∧ high≠0)

/-- `f mod m`, without the modulus: `f ≤ m`. -/
theorem hbF_mod_hbM {g a : Nat} (hg : IsG g) (ha : a < q) :
    hbF g a % hbM g = if hbF g a = hbM g then 0 else hbF g a := by
  split
  · rename_i h; rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_ne (hbF_le (mem_of_isG hg) ha) ‹_›)

/-- By cases on whether `r` and `r + c` are at the top of their range (`f = m`), for
each `γ₂`, and the carry of `r + c` past `q`: with no `%` left, `omega` decides
each case on a few linear facts (splitting on the sign of `c` only in the cases
that need it, which halves the cases and their certificates). -/
theorem hint_high_change {g : Nat} (hg : IsG g) (r : Zq) (c : Int)
    (hc : -4202495≤c ∧ c≤4210685) :
    highBits g (r+ofInt c)≠highBits g r ↔
      hintPredicate g (lowBits g r+c) (highBits g r) := by
  have hgm := mem_of_isG hg
  rw [highBits_eq hgm, highBits_eq hgm, lowBits_eq hgm, VG.Proof.MlDsa.Round.val_add,
    hbF_mod_hbM hg r.isLt, hbF_mod_hbM hg (Nat.mod_lt _ (by decide))]
  have hv := VG.Proof.MlDsa.KeyGen.ofInt_val c
  have hr := r.isLt
  have hx := (ofInt c).isLt
  generalize r.val = a at *
  generalize (ofInt c).val = x at *
  unfold hintPredicate
  by_cases hf : hbF g a = hbM g <;> simp only [hf, ite_true, ite_false] <;>
  by_cases hn : hbF g ((a + x) % q) = hbM g <;> simp only [hn, ite_true, ite_false] <;>
  rcases hg with rfl | rfl <;>
    simp only [hbF, hbM, q, Impl.MlDsa.AArch64.Round.g32, Impl.MlDsa.AArch64.Round.g88, Nat.reduceMul,
      Nat.reduceSub, Nat.reduceDiv] at * <;>
    simp (disch := decide) only [Nat.add_sub_assoc, Nat.reduceSub] at * <;>
    rcases Nat.lt_or_ge (a + x) 8380417 with hs | hs <;>
    (first | rw [Nat.mod_eq_of_lt hs] at * | rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega_using [hr, hv])] at *) <;>
    first | omega | (rcases Int.lt_or_le c 0 with hc0 | hc0 <;> omega_arith)

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

def hintWord (g t high : BitVec 32) : BitVec 32 :=
  ((((g-t) ||| (t-(-g))).sshiftRight 31) |||
    ((if t= -g then -1 else 0) &&& ~~~(if high=0 then -1 else 0))) >>> 31

theorem signedMask (x : BitVec 32) :
    x.sshiftRight 31=if x.toInt<0 then -1 else 0 := by
  rw [ResidentMask.signMask32]
  have hx := BitVec.toInt_eq_toNat_cond x
  split <;> split <;> first | rfl | omega_arith

theorem hintWord_value {g : Nat} (hg : 1≤g) (hg' : g≤524288)
    (t high : BitVec 32) (hl : -8380417<t.toInt) (hh : t.toInt<8380417) :
    hintWord (BitVec.ofNat 32 g) t high=
      if hintPredicate g t.toInt high.toInt then 1 else 0 := by
  have gi : (BitVec.ofNat 32 g).toInt=(g:Int) := by
    change (BitVec.ofInt 32 (g:Int)).toInt=(g:Int)
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega_arith
  have gn : (-(BitVec.ofNat 32 g)).toInt= -(g:Int) := by
    change (-BitVec.ofInt 32 (g:Int)).toInt= -(g:Int)
    rw [←BitVec.ofInt_neg]
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega_arith
  have l := subWord_int (BitVec.ofNat 32 g) t (by rw [gi]; omega_using [hh]) (by rw [gi]; omega_using [hg', hl])
  have r := subWord_int t (-(BitVec.ofNat 32 g)) (by rw [gn]; omega_using [hl]) (by rw [gn]; omega_using [hg', hh])
  have te : t= -(BitVec.ofNat 32 g) ↔ t.toInt= -(g:Int) := by
    constructor
    · intro h; rw [h,gn]
    · intro h; exact BitVec.eq_of_toInt_eq (h.trans gn.symm)
  have he : high=0 ↔ high.toInt=0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toInt_eq h
  unfold hintWord
  rw [BitVec.sshiftRight_or_distrib,signedMask,signedMask,l,r,gi,gn]
  simp only [te,he]
  unfold hintPredicate
  split <;> split <;> split <;> split <;>
    try simp only [ite_true,ite_false]
  all_goals split <;> first | rfl | omega

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

theorem word_or (a b : BitVec 128) (e : Nat) :
    vword (a ||| b) e=vword a e ||| vword b e := by
  simp only [vword,BitVec.extractLsb'_or]

theorem word_not (a : BitVec 128) {e : Nat} (he : e<4) :
    vword (~~~a) e = ~~~vword a e := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [vword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_not]
  simp (disch := omega_arith) only [decide_eq_true,Bool.true_and]

end VG.Proof.MlDsa.AArch64.Optimized.Response
