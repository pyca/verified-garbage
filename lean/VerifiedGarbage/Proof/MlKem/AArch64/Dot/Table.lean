module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.MlKem.Ntt
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `MlKem.AArch64.Dot.LoopState`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Dot.Step`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Dot.Bounds`, which this module and modules that import it used -/

section

/-! Bounds for the unreduced accumulators. No arithmetic wraps for at most
four canonical polynomial terms. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot

structure Sums where
  even : Nat
  odd : Nat
  cross : Nat

def Sums.next (s : Sums) (fe fo ge go : Nat) : Sums :=
  ⟨s.even + fe*ge, s.odd + fo*go, s.cross + fe*go + fo*ge⟩

def Sums.Bounded (s : Sums) (n : Nat) : Prop :=
  s.even ≤ n*(3329*3329) ∧ s.odd ≤ n*(3329*3329) ∧ s.cross ≤ 2*n*(3329*3329)

theorem Sums.Bounded.next {s : Sums} {n fe fo ge go : Nat} (h : s.Bounded n)
    (hf : fe < 3329) (ho : fo < 3329) (hg : ge < 3329) (hp : go < 3329) :
    (s.next fe fo ge go).Bounded (n+1) := by
  have a : fe*ge ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt hf) (Nat.le_of_lt hg)
  have b : fo*go ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt ho) (Nat.le_of_lt hp)
  have c : fe*go ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt hf) (Nat.le_of_lt hp)
  have d : fo*ge ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt ho) (Nat.le_of_lt hg)
  simp only [Sums.Bounded, Sums.next] at *
  bdd_omega

theorem Sums.Bounded.machine {s : Sums} {n : Nat} (h : s.Bounded n) (hn : n ≤ 4) :
    s.even ≤ 4*3329*3329 ∧ s.odd ≤ 4*3329*3329 ∧ s.cross ≤ 8*3329*3329 := by
  change s.even ≤ 4*(3329*3329) ∧ s.odd ≤ 4*(3329*3329) ∧ s.cross ≤ 8*(3329*3329)
  exact ⟨Nat.le_trans h.1 (Nat.mul_le_mul_right _ hn),
    Nat.le_trans h.2.1 (Nat.mul_le_mul_right _ hn),
    Nat.le_trans h.2.2 (Nat.mul_le_mul_right _ (show 2*n ≤ 8 by omega_using [hn]))⟩

theorem Sums.Bounded.noWrap {s : Sums} {n : Nat} (h : s.Bounded n) (hn : n ≤ 4) :
    s.even < 2^31 ∧ s.odd < 2^31 ∧ s.cross < 2^31 := by
  have := h.machine hn
  bdd_omega

end VG.Proof.MlKem.AArch64.Dot

end

end

/-! ### `MlKem.AArch64.Dot.Gather`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

def loads : List Instr := [.ldrq .v0 .x1 0, .ldrq .v1 .x1 16, .ldrq .v4 .x2 0, .ldrq .v5 .x2 16]

theorem loads_ok {rest : List Instr} {s : State} {Q : State → Prop}
    (hf : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16*i)) 16)
    (hg : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16*i)) 16)
    (k : ∀ s', VChg [.v0, .v1, .v4, .v5] s s' →
      s'.v .v0 = s.mem.read (s.gpr .x1) 16 →
      s'.v .v1 = s.mem.read (s.gpr .x1 + BitVec.ofNat 64 16) 16 →
      s'.v .v4 = s.mem.read (s.gpr .x2) 16 →
      s'.v .v5 = s.mem.read (s.gpr .x2 + BitVec.ofNat 64 16) 16 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loads ++ rest)) s Q := by
  simp only [loads, List.cons_append, List.nil_append]
  refine wp_ldrq (by decide) rfl (hf 0 (by decide)) fun s₁ h₁ => ?_
  refine wp_ldrq (by decide) rfl (by rw [h₁.rd, h₁.wr, h₁.gpr]; exact hf 1 (by decide)) fun s₂ h₂ => ?_
  refine wp_ldrq (by decide) rfl (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, h₂.gpr, h₁.gpr]; exact hg 0 (by decide)) fun s₃ h₃ => ?_
  refine wp_ldrq (by decide) rfl (by rw [h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr, h₃.gpr, h₂.gpr, h₁.gpr]; exact hg 1 (by decide)) fun s₄ h₄ => ?_
  refine k s₄ (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).mono ?_ ?_ ?_ ?_
  · rw [h₄.get .v0, h₃.get .v0, h₂.get .v0, h₁.v]; simp only [BitVec.add_zero]
  · rw [h₄.get .v1, h₃.get .v1, h₂.v, h₁.mem, h₁.gpr]
  · rw [h₄.get .v4, h₃.v, h₂.mem, h₁.mem, h₂.gpr, h₁.gpr]; simp only [BitVec.add_zero]
  · rw [h₄.v, h₃.mem, h₂.mem, h₁.mem, h₃.gpr, h₂.gpr, h₁.gpr]

end VG.Proof.MlKem.AArch64.Dot

end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Store.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def interleave (A B : Nat → Nat) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (if i % 2 = 0 then A (i/2) else B (i/2))

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Term.lean`, which only this module imported.

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Pointer.lean`, which only this module imported.

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/FullTerm.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def Accum (s : State) (a : Nat → Sums) : Prop :=
  Lanes (s.v .v21) (fun e => (a e).even) ∧
  Lanes (s.v .v22) (fun e => (a e).odd) ∧
  Lanes (s.v .v23) (fun e => (a e).cross)

def advance (a : Nat → Sums) (F G : Nat → Nat) : Nat → Sums :=
  fun e => (a e).next (F (2*e)) (F (2*e+1)) (G (2*e)) (G (2*e+1))

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Terms.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def sumTerms (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat)
    (a : Nat → Sums) : Nat → Sums :=
  terms.foldl (fun a fg => advance a (F fg) (G fg)) a

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Init.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

def zeroSums : Nat → Sums := fun _ => ⟨0,0,0⟩
theorem zeroLanes : Lanes 0 (fun _ => 0) := by
  intro e he
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_using [he]) with rfl | rfl | rfl | rfl <;> rfl

theorem sumTerms_bound (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Nat → Nat}
    {a : Nat → Sums} {n : Nat} (ha : ∀ e < 4, (a e).Bounded n)
    (hF : ∀ fg ∈ terms, ∀ e < 8, F fg e < 3329)
    (hG : ∀ fg ∈ terms, ∀ e < 8, G fg e < 3329) :
    ∀ e < 4, (sumTerms terms F G a e).Bounded (n+terms.length) := by
  induction terms generalizing a n with
  | nil => simpa only [sumTerms, List.foldl_nil, List.length_nil, Nat.add_zero] using ha
  | cons fg terms ih =>
    have hb : ∀ e < 4, (advance a (F fg) (G fg) e).Bounded (n+1) := fun e he =>
      (ha e he).next (hF fg (by simp) _ (by omega_using [he])) (hF fg (by simp) _ (by omega_using [he]))
        (hG fg (by simp) _ (by omega_using [he])) (hG fg (by simp) _ (by omega_using [he]))
    have hr := ih hb (fun fg hf => hF fg (by simp [hf])) (fun fg hf => hG fg (by simp [hf]))
    simpa only [sumTerms, List.foldl_cons, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 terms.length] using hr

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Compute.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

theorem only_vchg {s s' : State} {rs : List VReg} (h : VChg rs s s')
    (hp : ∀ r ∈ preservedV, r ∉ rs := by decide +kernel) : Only [] s s' :=
  ⟨fun _ _ => congrFun h.gpr _, h.mem, h.rd, h.wr, h.sp,
    fun r hr => by rw [h.get r (hp r hr)]⟩

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Advance.lean`, which only this module imported.
section

@[expose] public section
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

abbrev clob : List Reg := [.x0,.x1,.x2,.x3,.x9,.x10,.x11,.x12]

def evenResult (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat) : Nat → Nat :=
  fun e => ((sumTerms terms F G zeroSums e).even + (sumTerms terms F G zeroSums e).odd * Γ e) % 3329

def oddResult (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) : Nat → Nat :=
  fun e => (sumTerms terms F G zeroSums e).cross % 3329

end VG.Proof.MlKem.AArch64.Dot

end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def blockValues (F : (Nat × Nat) → Nat → Nat) (c : Nat) : (Nat × Nat) → Nat → Nat :=
  fun fg e => F fg (8*c+e)

def blockGamma (Γ : Nat → Nat) (c : Nat) : Nat → Nat := fun e => Γ (4*c+e)

def result (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat)
    (j : Nat) : BitVec 32 :=
  interleave (evenResult terms (blockValues F (j/8)) (blockValues G (j/8)) (blockGamma Γ (j/8)))
    (oddResult terms (blockValues F (j/8)) (blockValues G (j/8))) (j%8)

theorem result_block (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat)
    (c : Nat) {e : Nat} (he : e < 8) :
    result terms F G Γ (8*c+e) =
      interleave (evenResult terms (blockValues F c) (blockValues G c) (blockGamma Γ c))
        (oddResult terms (blockValues F c) (blockValues G c)) e := by
  unfold result
  rw [show (8*c+e)/8 = c by omega_using [he], show (8*c+e)%8 = e by omega_using [he]]

end VG.Proof.MlKem.AArch64.Dot

end

end

/-! ### `MlKem.AArch64.Ntt16.Readonly.Words`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16
open VG.Impl.MlKem.AArch64.Ntt16.Readonly

theorem forward_length : (words 16 tableHalves).length = 64 := by lit_decide
theorem gamma_length : (words 32 gammaTable).length = 64 := by lit_decide

theorem forward_words : ∀ i < 64, (words 16 tableHalves).getD i 0 = hw4 tableHalves i := by lit_decide

theorem gamma_low : ∀ i < 64,
    ((words 32 gammaTable).getD i 0).extractLsb' 0 32 = BitVec.ofNat 32 (gammaTable.getD (2*i) 0) := by lit_decide

theorem gamma_high : ∀ i < 64,
    ((words 32 gammaTable).getD i 0).extractLsb' 32 32 = BitVec.ofNat 32 (gammaTable.getD (2*i+1) 0) := by lit_decide

end VG.Proof.MlKem.AArch64.Ntt16.Readonly

end

end

/-! ### `MlKem.AArch64.Dot.Result`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Dot.Field`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.Spec.MlKem VG.Proof.MlKem

def polySum (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Poly) (P : Poly := zero) : Poly :=
  terms.foldl (fun p fg => add p (multiplyNTTs (F fg) (G fg))) P

def polyValues (F : (Nat × Nat) → Poly) : (Nat × Nat) → Nat → Nat := fun fg i => ((F fg)[i]!).val

def PairRel (a : Sums) (P : Poly) (i : Nat) : Prop :=
  (a.even + a.odd * (gamma i).val) % q = (P[2*i]!).val ∧
  a.cross % q = (P[2*i+1]!).val

theorem next_even (s : Sums) (fe fo ge go g : Nat) :
    ((s.next fe fo ge go).even + (s.next fe fo ge go).odd*g)%q =
      ((s.even+s.odd*g)%q + (fe*ge+fo*go*g)%q)%q := by
  rw [←Nat.add_mod]
  change (s.even+fe*ge+(s.odd+fo*go)*g)%q = _
  rw [Nat.add_mul]
  congr 1
  omega_using []

theorem next_cross (s : Sums) (fe fo ge go : Nat) :
    (s.next fe fo ge go).cross%q = (s.cross%q + (fe*go+fo*ge)%q)%q := by
  rw [←Nat.add_mod]
  change (s.cross+fe*go+fo*ge)%q = _
  rw [Nat.add_assoc]

theorem multiply_even_val (F G : Poly) {i : Nat} (hi : i < 128) :
    ((multiplyNTTs F G)[2*i]!).val =
      ((F[2*i]!).val*(G[2*i]!).val + (F[2*i+1]!).val*(G[2*i+1]!).val*(gamma i).val)%q := by
  rw [multiplyNTTs_even F G hi,val_add',val_mul,val_mul,val_mul,Nat.mod_mul_mod,←Nat.add_mod]

theorem multiply_odd_val (F G : Poly) {i : Nat} (hi : i < 128) :
    ((multiplyNTTs F G)[2*i+1]!).val =
      ((F[2*i]!).val*(G[2*i+1]!).val + (F[2*i+1]!).val*(G[2*i]!).val)%q := by
  rw [multiplyNTTs_odd F G hi,val_add',val_mul,val_mul,←Nat.add_mod]

theorem PairRel.next {a : Sums} {P F G : Poly} {i : Nat} (hi : i < 128) (h : PairRel a P i) :
    PairRel (a.next (F[2*i]!).val (F[2*i+1]!).val (G[2*i]!).val (G[2*i+1]!).val)
      (add P (multiplyNTTs F G)) i := by
  constructor
  · rw [next_even,h.1,add_get _ _ (by change 2*i < 256; omega_using [hi]),val_add',multiply_even_val _ _ hi]
  · rw [next_cross,h.2,add_get _ _ (by change 2*i+1 < 256; omega_using [hi]),val_add',multiply_odd_val _ _ hi]

theorem sumTerms_field (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Poly)
    {c e : Nat} (hc : c < 32) (he : e < 4) {a : Nat → Sums} {P : Poly}
    (h : PairRel (a e) P (4*c+e)) :
    PairRel (sumTerms terms (blockValues (polyValues F) c) (blockValues (polyValues G) c) a e)
      (polySum terms F G P) (4*c+e) := by
  induction terms generalizing a P with
  | nil => exact h
  | cons fg terms ih =>
    apply ih
    have hn := h.next (F := F fg) (G := G fg) (by omega_using [hc, he])
    simpa only [advance,blockValues,polyValues,show 8*c+2*e = 2*(4*c+e) by omega_using [],
      show 8*c+(2*e+1) = 2*(4*c+e)+1 by omega_using []] using hn

end VG.Proof.MlKem.AArch64.Dot

end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.Spec.MlKem VG.Proof.MlKem

def gammaValues (i : Nat) : Nat := (gamma i).val

theorem zero_pair {i : Nat} (hi : i < 128) : PairRel (zeroSums 0) zero i := by
  constructor
  · rw [zero_get (by change 2*i<256; omega_using [hi])]
    simp only [zeroSums,Nat.zero_mul,Nat.add_zero,Nat.zero_mod,val_zero]
  · rw [zero_get (by change 2*i+1<256; omega_using [hi])]; rfl

theorem result_field (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Poly)
    {j : Nat} (hj : j < 256) :
    result terms (polyValues F) (polyValues G) gammaValues j =
      BitVec.ofNat 32 ((polySum terms F G)[j]!).val := by
  have hc : j/8 < 32 := by omega_using [hj]
  have he : j%8/2 < 4 := by omega_using []
  have hh := sumTerms_field terms F G hc he (a := zeroSums) (P := zero)
    (zero_pair (i := 4*(j/8)+j%8/2) (by omega_using [hj]))
  unfold result interleave
  split <;> rename_i hp
  · have ji : j = 2*(4*(j/8)+j%8/2) := by omega_using [hp]
    change BitVec.ofNat 32 (((sumTerms terms (blockValues (polyValues F) (j/8))
      (blockValues (polyValues G) (j/8)) zeroSums (j%8/2)).even +
      (sumTerms terms (blockValues (polyValues F) (j/8)) (blockValues (polyValues G) (j/8)) zeroSums (j%8/2)).odd *
      (gamma (4*(j/8)+j%8/2)).val)%q) = _
    rw [hh.1,←ji]
  · have ji : j = 2*(4*(j/8)+j%8/2)+1 := by omega_using [hp]
    change BitVec.ofNat 32 ((sumTerms terms (blockValues (polyValues F) (j/8))
      (blockValues (polyValues G) (j/8)) zeroSums (j%8/2)).cross%q) = _
    rw [hh.2,←ji]

end VG.Proof.MlKem.AArch64.Dot

end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16.Readonly

/-- The emitted readonly gamma artifact, as its 64 doublewords. -/
def GammaArtifact (m : Mem) (p : Addr) : Prop :=
  ∀ i < 64, m.readW (p+BitVec.ofNat 64 (8*i)) 64 = (words 32 gammaTable).getD i 0

theorem GammaArtifact.word {m : Mem} {p : Addr} (h : GammaArtifact m p)
    {k : Nat} (hk : k < 128) :
    m.readW (p+BitVec.ofNat 64 (4*k)) 32 = BitVec.ofNat 32 (gammaValues k) := by
  have hi : k/2 < 64 := by omega_using [hk]
  have hv := h (k/2) hi
  have hr : k%2=0 ∨ k%2=1 := by omega_using []
  have hg : gammaTable.getD k 0 = gammaValues k := by
    rw [gammaTable_eq,gammas_getD hk]; rfl
  rw [←hg]
  rcases hr with hr | hr
  · have he : k=2*(k/2) := by omega_using [hr]
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 0 32) hv
    rw [readW64_lo,Ntt16.Readonly.gamma_low _ hi] at hx
    simpa only [show 8*(k/2)=4*k by omega_using [hr],←he] using hx
  · have he : k=2*(k/2)+1 := by omega_using [hr]
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 32 32) hv
    rw [readW64_hi,Ntt16.Readonly.gamma_high _ hi,BitVec.add_assoc,
      ←BitVec.ofNat_add (8*(k/2)) 4] at hx
    simpa only [show 8*(k/2)+4=4*k by omega_using [hr],←he] using hx

theorem GammaArtifact.lanes {m : Mem} {p : Addr} (h : GammaArtifact m p)
    {c : Nat} (hc : c < 32) :
    Lanes (m.read (p+BitVec.ofNat 64 (16*c)) 16) (blockGamma gammaValues c) := by
  have hs : p+BitVec.ofNat 64 (16*c) = coeffAddr p (4*c) := by
    unfold coeffAddr; congr 2; omega_using []
  rw [hs]
  apply lanes_coeffs (m:=m) (p:=p) (j:=4*c)
  intro e he
  change (m.readW (p+BitVec.ofNat 64 (4*(4*c+e))) 32).toNat = gammaValues (4*c+e)
  rw [h.word (by omega_using [hc, he]),BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  exact Nat.lt_trans (gamma (4*c+e)).isLt (by decide)

end VG.Proof.MlKem.AArch64.Dot
