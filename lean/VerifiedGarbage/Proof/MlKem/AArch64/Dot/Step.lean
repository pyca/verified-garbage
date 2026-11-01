module

public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Bounds
public import VerifiedGarbage.Impl.MlKem.AArch64.Dot
public import VerifiedGarbage.Proof.MlKem.PolyContract
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Arithmetic

import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Gather
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Accumulate
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.Contract

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Store.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def store : List Instr :=
  [.vop (.perm .zip1 .s4 .v0 .v21 .v23), .vop (.perm .zip2 .s4 .v1 .v21 .v23),
   .strq .v0 .x0 0, .strq .v1 .x0 16]

def interleave (A B : Nat → Nat) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (if i % 2 = 0 then A (i/2) else B (i/2))

theorem zip1_values {x y : BitVec 128} {A B : Nat → Nat}
    (hx : Lanes x A) (hy : Lanes y B) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip1 .s4 x y) e = interleave A B e := by
  rw [vword_zip1_s4' _ _ he]
  unfold interleave
  split <;> rename_i h
  · exact BitVec.eq_of_toNat_eq (by rw [hx _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hx.lt (by omega))])
  · exact BitVec.eq_of_toNat_eq (by rw [hy _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hy.lt (by omega))])

theorem zip2_values {x y : BitVec 128} {A B : Nat → Nat}
    (hx : Lanes x A) (hy : Lanes y B) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip2 .s4 x y) e = interleave A B (4+e) := by
  rw [vword_zip2_s4 _ _ he]
  unfold interleave
  have hm : (4+e)%2 = e%2 := by omega
  have hd : (4+e)/2 = 2+e/2 := by omega
  rw [hm,hd]
  split <;> rename_i h
  · exact BitVec.eq_of_toNat_eq (by rw [hx _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hx.lt (by omega))])
  · exact BitVec.eq_of_toNat_eq (by rw [hy _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hy.lt (by omega))])

theorem store_ok {s : State} {p : Addr} {j : Nat} {A B : Nat → Nat}
    (hx0 : s.gpr .x0 = coeffAddr p j) (hj : j+8 ≤ 256)
    (hw : ∀ i < 2, InRegions s.wr (coeffAddr p (j+4*i)) 16)
    (hc : VConsts s) (ha : Lanes (s.v .v21) A) (hb : Lanes (s.v .v23) B)
    {O D : Nat → BitVec 32} (ho : CoeffsUpTo s.mem p j O D)
    (hv : ∀ e < 8, O (j+e) = interleave A B e) :
    WP isa (.block store) s fun s' => Keep [] s s' ∧ VConsts s' ∧
      Frame [polyRegion p] s.mem s'.mem ∧ CoeffsUpTo s'.mem p (j+8) O D := by
  simp only [store]
  refine wp_vop (d := .v0) rfl fun s₁ h₁ => wp_vop (d := .v1) rfl fun s₂ h₂ => ?_
  refine wp_strq (a := coeffAddr p j) (by decide)
    (by rw [h₂.gpr,h₁.gpr,hx0,ptr_zero])
    (by rw [h₂.wr,h₁.wr]; simpa only [Nat.mul_zero,Nat.add_zero] using hw 0 (by decide)) fun s₃ h₃ => ?_
  refine wp_strq (a := coeffAddr p (j+4)) (by decide)
    (by rw [h₃.gpr,h₂.gpr,h₁.gpr,hx0,coeffAddr_step])
    (by rw [h₃.wr,h₂.wr,h₁.wr]; exact hw 1 (by decide)) fun s₄ h₄ => wp_nil ?_
  have hm : s₄.mem = (s.mem.write (coeffAddr p j) 16
      (VPermOp.eval .zip1 .s4 (s.v .v21) (s.v .v23))).write (coeffAddr p (j+4)) 16
      (VPermOp.eval .zip2 .s4 (s.v .v21) (s.v .v23)) := by
    rw [h₄.mem,h₃.mem,h₂.mem,h₁.mem,h₃.v,h₂.v,h₁.get .v21,h₁.get .v23,h₂.get .v0,h₁.v]
  refine ⟨(((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).mono,
    ⟨?_,?_⟩, ?_, ?_⟩
  · rw [h₄.v,h₃.v,h₂.get .v16,h₁.get .v16]; exact hc.q
  · rw [h₄.v,h₃.v,h₂.get .v17,h₁.get .v17]; exact hc.m
  · rw [hm]; exact frame16 (frame16 (Frame.refl _ _) (by omega) _) (by omega) _
  · rw [hm,show j+8 = j+4+4 by omega]
    refine CoeffsUpTo.write16 (CoeffsUpTo.write16 ho (by omega) (fun e he => ?_)) (by omega) (fun e he => ?_)
    · rw [hv e (by omega)]; exact zip1_values ha hb he
    · rw [show j+4+e = j+(4+e) by omega,hv (4+e) (by omega)]; exact zip2_values ha hb he

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Term.lean`, which only this module imported.
section

section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def termCore : List Instr := loads ++ gather ++ accumulate
abbrev termClob : List VReg := [.v0, .v1, .v4, .v5, .v6, .v7, .v19, .v20, .v21, .v22, .v23]

theorem termCore_ok {rest : List Instr} {s : State} {Q : State → Prop}
    {F G A B C : Nat → Nat}
    (hrf : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16*i)) 16)
    (hrg : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16*i)) 16)
    (hf : ∀ e < 8, (coeffAt s.mem (s.gpr .x1) e).toNat = F e)
    (hg : ∀ e < 8, (coeffAt s.mem (s.gpr .x2) e).toNat = G e)
    (ha : Lanes (s.v .v21) A) (hb : Lanes (s.v .v22) B) (hc : Lanes (s.v .v23) C)
    (ba : ∀ e < 4, A e + F (2*e) * G (2*e) < 2 ^ 32)
    (bb : ∀ e < 4, B e + F (2*e+1) * G (2*e+1) < 2 ^ 32)
    (bc : ∀ e < 4, C e + F (2*e) * G (2*e+1) + F (2*e+1) * G (2*e) < 2 ^ 32)
    (k : ∀ s', VChg termClob s s' →
      Lanes (s'.v .v21) (fun e => A e + F (2*e) * G (2*e)) →
      Lanes (s'.v .v22) (fun e => B e + F (2*e+1) * G (2*e+1)) →
      Lanes (s'.v .v23) (fun e => C e + F (2*e) * G (2*e+1) + F (2*e+1) * G (2*e)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (termCore ++ rest)) s Q := by
  simp only [termCore, List.append_assoc]
  refine loads_ok hrf hrg fun s₁ h₁ l0 l1 l4 l5 => ?_
  have f0 : Lanes (s₁.v .v0) F := by
    rw [l0]
    simpa only [coeffAddr, Nat.mul_zero, BitVec.add_zero] using
      (lanes_coeffs (m := s.mem) (p := s.gpr .x1) (j := 0) (A := F) (fun e he => by simpa only [Nat.zero_add] using hf e (by omega)))
  have f1 : Lanes (s₁.v .v1) (fun e => F (4+e)) := by
    rw [l1]
    exact lanes_coeffs (m := s.mem) (p := s.gpr .x1) (j := 4) (fun e he => hf (4+e) (by omega))
  have g0 : Lanes (s₁.v .v4) G := by
    rw [l4]
    simpa only [coeffAddr, Nat.mul_zero, BitVec.add_zero] using
      (lanes_coeffs (m := s.mem) (p := s.gpr .x2) (j := 0) (A := G) (fun e he => by simpa only [Nat.zero_add] using hg e (by omega)))
  have g1 : Lanes (s₁.v .v5) (fun e => G (4+e)) := by
    rw [l5]
    exact lanes_coeffs (m := s.mem) (p := s.gpr .x2) (j := 4) (fun e he => hg (4+e) (by omega))
  refine gather_ok f0 f1 g0 g1 fun s₂ h₂ fe fo ge go => ?_
  have a₂ : Lanes (s₂.v .v21) A := by rw [h₂.get .v21, h₁.get .v21]; exact ha
  have b₂ : Lanes (s₂.v .v22) B := by rw [h₂.get .v22, h₁.get .v22]; exact hb
  have c₂ : Lanes (s₂.v .v23) C := by rw [h₂.get .v23, h₁.get .v23]; exact hc
  refine accumulate_ok a₂ b₂ c₂ fe fo ge go ba bb bc fun s₃ h₃ a₃ b₃ c₃ => ?_
  exact k s₃ ((h₁.trans h₂).trans h₃).mono a₃ b₃ c₃

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Pointer.lean`, which only this module imported.
section

section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Impl.MlKem.AArch64

def pointers (fg : Nat × Nat) : List Instr :=
  ptrTo .x1 .x28 fg.1 ++ ptrTo .x2 .x28 fg.2 ++
    [.add .x .x1 .x1 .x12, .add .x .x2 .x2 .x12]

theorem pointers_ok {s : State} {fg : Nat × Nat}
    (hf : fg.1 < 65536) (hg : fg.2 < 65536) :
    WP isa (.block (pointers fg)) s fun s' =>
      Only [.x1, .x2] s s' ∧ s'.v = s.v ∧
      s'.gpr .x1 = s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12 ∧
      s'.gpr .x2 = s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12 := by
  refine WP.mono (WP.keepV (Q := fun s' => Only [.x1, .x2] s s' ∧
    s'.gpr .x1 = s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12 ∧
    s'.gpr .x2 = s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12) ?_ ?_) ?_
  · simp only [pointers, ptrTo]
    split <;> split <;> rfl
  · simp only [pointers, List.append_assoc]
    refine wp_ptrTo (by decide) hf fun s₁ h₁ e₁ => wp_ptrTo (by decide) hg fun s₂ h₂ e₂ =>
      wp_add fun s₃ h₃ e₃ => wp_add fun s₄ h₄ e₄ => wp_nil ?_
    refine ⟨(((h₁.trans h₂).trans h₃).trans h₄).mono, ?_, ?_⟩
    · rw [h₄.get .x1, e₃, h₂.get .x1, e₁, h₂.get .x12, h₁.get .x12]
    · rw [e₄, h₃.get .x2, e₂, h₁.get .x28, h₃.get .x12, h₂.get .x12, h₁.get .x12]
  · intro s' h
    exact ⟨h.1.1, h.2, h.1.2⟩

theorem term_partition (fg : Nat × Nat) :
    Impl.MlKem.AArch64.Dot.dotTerm fg = pointers fg ++ termCore := by
  simp only [Impl.MlKem.AArch64.Dot.dotTerm, pointers, termCore, loads, gather,
    accumulate, List.append_assoc, List.cons_append, List.nil_append]

end VG.Proof.MlKem.AArch64.Dot
end

end

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

theorem fullTerm_ok {s : State} {fg : Nat × Nat} {a : Nat → Sums} {F G : Nat → Nat} {n : Nat}
    (hoF : fg.1 < 65536) (hoG : fg.2 < 65536)
    (hc : VConsts s) (ha : Accum s a) (hb : ∀ e < 4, (a e).Bounded n) (hn : n < 4)
    (bF : ∀ e < 8, F e < 3329) (bG : ∀ e < 8, G e < 3329)
    (hf : ∀ e < 8, (coeffAt s.mem (s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12) e).toNat = F e)
    (hg : ∀ e < 8, (coeffAt s.mem (s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12) e).toNat = G e)
    (rf : ∀ i < 2, InRegions (s.rd ++ s.wr)
      (s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12 + BitVec.ofNat 64 (16*i)) 16)
    (rg : ∀ i < 2, InRegions (s.rd ++ s.wr)
      (s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (Impl.MlKem.AArch64.Dot.dotTerm fg)) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧ Accum s' (advance a F G) := by
  rw [term_partition, WP.block_append_iff]
  refine WP.mono (pointers_ok hoF hoG) fun s₁ ⟨h₁,v₁,e₁,e₂⟩ => ?_
  have hc₁ : VConsts s₁ := ⟨by rw [v₁]; exact hc.q, by rw [v₁]; exact hc.m⟩
  have ha₁ : Accum s₁ a := by simpa only [Accum, v₁] using ha
  have bnext : ∀ e < 4, ((advance a F G) e).Bounded (n+1) := fun e he =>
    (hb e he).next (bF _ (by omega)) (bF _ (by omega)) (bG _ (by omega)) (bG _ (by omega))
  rw [← List.append_nil termCore]
  refine termCore_ok (F := F) (G := G) (fun i hi => by rw [h₁.rd,h₁.wr,e₁]; exact rf i hi)
    (fun i hi => by rw [h₁.rd,h₁.wr,e₂]; exact rg i hi)
    (fun e he => by rw [h₁.mem,e₁]; exact hf e he)
    (fun e he => by rw [h₁.mem,e₂]; exact hg e he)
    ha₁.1 ha₁.2.1 ha₁.2.2
    (fun e he => by have := (bnext e he).noWrap (by omega); exact Nat.lt_trans this.1 (by decide))
    (fun e he => by have := (bnext e he).noWrap (by omega); exact Nat.lt_trans this.2.1 (by decide))
    (fun e he => by have := (bnext e he).noWrap (by omega); exact Nat.lt_trans this.2.2 (by decide))
    fun s₂ h₂ l₁ l₂ l₃ => wp_nil ?_
  refine ⟨?_, hc₁.chg h₂, l₁, l₂, l₃⟩
  exact ⟨fun r hr => by rw [h₂.gpr]; exact h₁.gpr r hr,
    h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => by rw [h₂.v r (by revert r hr; decide +kernel)]; exact h₁.vcs r hr⟩

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Terms.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

structure TermInput (s : State) (fg : Nat × Nat) (F G : Nat → Nat) : Prop where
  offF : fg.1 < 65536
  offG : fg.2 < 65536
  boundF : ∀ e < 8, F e < 3329
  boundG : ∀ e < 8, G e < 3329
  valueF : ∀ e < 8, (coeffAt s.mem (s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12) e).toNat = F e
  valueG : ∀ e < 8, (coeffAt s.mem (s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12) e).toNat = G e
  readF : ∀ i < 2, InRegions (s.rd ++ s.wr)
    (s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12 + BitVec.ofNat 64 (16*i)) 16
  readG : ∀ i < 2, InRegions (s.rd ++ s.wr)
    (s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12 + BitVec.ofNat 64 (16*i)) 16

theorem TermInput.keep {s s' : State} {fg : Nat × Nat} {F G : Nat → Nat}
    (h : TermInput s fg F G) (hk : Only [.x1, .x2] s s') : TermInput s' fg F G := by
  refine ⟨h.offF, h.offG, h.boundF, h.boundG, ?_, ?_, ?_, ?_⟩
  · rw [hk.mem, hk.get .x28, hk.get .x12]; exact h.valueF
  · rw [hk.mem, hk.get .x28, hk.get .x12]; exact h.valueG
  · rw [hk.rd, hk.wr, hk.get .x28, hk.get .x12]; exact h.readF
  · rw [hk.rd, hk.wr, hk.get .x28, hk.get .x12]; exact h.readG

def sumTerms (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat)
    (a : Nat → Sums) : Nat → Sums :=
  terms.foldl (fun a fg => advance a (F fg) (G fg)) a

theorem terms_ok (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Nat → Nat}
    {s : State} {a : Nat → Sums} {n : Nat}
    (hc : VConsts s) (ha : Accum s a) (hb : ∀ e < 4, (a e).Bounded n)
    (hn : n + terms.length ≤ 4)
    (hin : ∀ fg ∈ terms, TermInput s fg (F fg) (G fg)) :
    WP isa (.block (terms.flatMap Impl.MlKem.AArch64.Dot.dotTerm)) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧ Accum s' (sumTerms terms F G a) := by
  induction terms generalizing s a n with
  | nil => exact wp_nil ⟨Only.refl _ _, hc, ha⟩
  | cons fg terms ih =>
    simp only [List.length_cons] at hn
    rw [List.flatMap_cons, WP.block_append_iff]
    have h := hin fg (by simp)
    refine WP.mono (fullTerm_ok h.offF h.offG hc ha hb (by omega)
      h.boundF h.boundG h.valueF h.valueG h.readF h.readG) fun s₁ ⟨hk,hc₁,ha₁⟩ => ?_
    refine WP.mono (ih hc₁ ha₁ (n := n+1) (fun e he => (hb e he).next
      (h.boundF _ (by omega)) (h.boundF _ (by omega))
      (h.boundG _ (by omega)) (h.boundG _ (by omega)))
      (by omega)
      (fun fg hf => (hin fg (by simp [hf])).keep hk)) fun s₂ ⟨hk₂,hc₂,ha₂⟩ => ?_
    exact ⟨(hk.trans hk₂).mono (by simp), hc₂, ha₂⟩

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Init.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

def zeroSums : Nat → Sums := fun _ => ⟨0,0,0⟩
def clear : List Instr := [.vop (.movi0 .v21), .vop (.movi0 .v22), .vop (.movi0 .v23)]

theorem zeroLanes : Lanes 0 (fun _ => 0) := by
  intro e he
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem clear_ok {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', VChg [.v21, .v22, .v23] s s' → Accum s' zeroSums → WP isa (.block rest) s' Q) :
    WP isa (.block (clear ++ rest)) s Q := by
  simp only [clear, List.cons_append, List.nil_append]
  refine wp_vop (d := .v21) rfl fun s₁ h₁ => wp_vop (d := .v22) rfl fun s₂ h₂ =>
    wp_vop (d := .v23) rfl fun s₃ h₃ => ?_
  refine k s₃ ((h₁.chg.trans h₂.chg).trans h₃.chg).mono ⟨?_,?_,?_⟩
  · rw [h₃.get .v21, h₂.get .v21, h₁.v]; exact zeroLanes
  · rw [h₃.get .v22, h₂.v]; exact zeroLanes
  · rw [h₃.v]; exact zeroLanes

theorem sumTerms_bound (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Nat → Nat}
    {a : Nat → Sums} {n : Nat} (ha : ∀ e < 4, (a e).Bounded n)
    (hF : ∀ fg ∈ terms, ∀ e < 8, F fg e < 3329)
    (hG : ∀ fg ∈ terms, ∀ e < 8, G fg e < 3329) :
    ∀ e < 4, (sumTerms terms F G a e).Bounded (n+terms.length) := by
  induction terms generalizing a n with
  | nil => simpa only [sumTerms, List.foldl_nil, List.length_nil, Nat.add_zero] using ha
  | cons fg terms ih =>
    have hb : ∀ e < 4, (advance a (F fg) (G fg) e).Bounded (n+1) := fun e he =>
      (ha e he).next (hF fg (by simp) _ (by omega)) (hF fg (by simp) _ (by omega))
        (hG fg (by simp) _ (by omega)) (hG fg (by simp) _ (by omega))
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

def compute (terms : List (Nat × Nat)) : List Instr :=
  clear ++ terms.flatMap Impl.MlKem.AArch64.Dot.dotTerm ++ [.ldrq .v18 .x3 0] ++ finish

theorem compute_ok {s : State} (terms : List (Nat × Nat))
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat}
    (hc : VConsts s) (hn : terms.length ≤ 4)
    (hin : ∀ fg ∈ terms, TermInput s fg (F fg) (G fg))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 0) 16)
    (hg : Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 0) 16) Γ)
    (bg : ∀ e < 4, Γ e < 3329) :
    WP isa (.block (compute terms)) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧
      Lanes (s'.v .v21) (fun e => ((sumTerms terms F G zeroSums e).even +
        (sumTerms terms F G zeroSums e).odd * Γ e) % 3329) ∧
      Lanes (s'.v .v23) (fun e => (sumTerms terms F G zeroSums e).cross % 3329) := by
  simp only [compute, List.append_assoc]
  refine clear_ok fun s₁ h₁ a₁ => ?_
  have k₁ := only_vchg h₁
  have input₁ : ∀ fg ∈ terms, TermInput s₁ fg (F fg) (G fg) :=
    fun fg hf => (hin fg hf).keep (k₁.mono (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (terms_ok terms (hc.chg h₁) a₁
    (n := 0) (fun _ _ => by simp only [zeroSums, Sums.Bounded]; decide)
    (by simpa only [Nat.zero_add] using hn) input₁) fun s₂ ⟨k₂,c₂,a₂⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrq (by decide) rfl
    (by rw [k₂.rd,k₂.wr,k₁.rd,k₁.wr,k₂.get .x3,k₁.get .x3]; exact hr) fun s₃ h₃ => ?_
  have g₃ : Lanes (s₃.v .v18) Γ := by
    rw [h₃.v,k₂.mem,k₁.mem,k₂.get .x3,k₁.get .x3]; exact hg
  have ab : ∀ e < 4, (sumTerms terms F G zeroSums e).Bounded terms.length := by
    simpa only [Nat.zero_add] using sumTerms_bound terms (n := 0)
      (a := zeroSums) (fun _ _ => by simp only [zeroSums, Sums.Bounded]; decide)
      (fun fg hf => (hin fg hf).boundF) (fun fg hf => (hin fg hf).boundG)
  have a₃ : Accum s₃ (sumTerms terms F G zeroSums) := by
    refine ⟨?_,?_,?_⟩
    · rw [h₃.get .v21]; exact a₂.1
    · rw [h₃.get .v22]; exact a₂.2.1
    · rw [h₃.get .v23]; exact a₂.2.2
  rw [← List.append_nil finish]
  refine finish_ok (c₂.chg h₃.chg) a₃.1 a₃.2.1 a₃.2.2 g₃
    (fun e he => ((ab e he).machine hn).1)
    (fun e he => ((ab e he).machine hn).2.1)
    (fun e he => ((ab e he).machine hn).2.2) bg fun s₄ h₄ l₁ l₂ => wp_nil ?_
  exact ⟨(((k₁.trans k₂).trans (only_vchg h₃.chg)).trans (only_vchg h₄)).mono (by simp),
    (c₂.chg h₃.chg).chg h₄, l₁, l₂⟩

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Advance.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

def bump : List Instr :=
  [.addImm .x .x0 .x0 32, .addImm .x .x3 .x3 16,
   .addImm .x .x12 .x12 32, .subImm .x .x11 .x11 1]

theorem bump_ok (s : State) : WP isa (.block bump) s fun s' =>
    Only [.x0,.x3,.x12,.x11] s s' ∧ s'.v = s.v ∧
    s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 32 ∧
    s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 16 ∧
    s'.gpr .x12 = s.gpr .x12 + BitVec.ofNat 64 32 ∧
    s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 := by
  refine WP.mono (WP.keepV (Q := fun s' => Only [.x0,.x3,.x12,.x11] s s' ∧
    s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 32 ∧
    s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 16 ∧
    s'.gpr .x12 = s.gpr .x12 + BitVec.ofNat 64 32 ∧
    s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1) (by decide) ?_) ?_
  · refine wp_addImm (by decide) fun s₁ h₁ e₁ => wp_addImm (by decide) fun s₂ h₂ e₂ =>
      wp_addImm (by decide) fun s₃ h₃ e₃ => wp_subImm (by decide) fun s₄ h₄ e₄ => wp_nil ?_
    exact ⟨(((h₁.trans h₂).trans h₃).trans h₄).mono,
      by rw [h₄.get .x0,h₃.get .x0,h₂.get .x0,e₁],
      by rw [h₄.get .x3,h₃.get .x3,e₂,h₁.get .x3],
      by rw [h₄.get .x12,e₃,h₂.get .x12,h₁.get .x12],
      by rw [e₄,h₃.get .x11,h₂.get .x11,h₁.get .x11]⟩
  · intro s' h; exact ⟨h.1.1,h.2,h.1.2⟩

def body (terms : List (Nat × Nat)) : List Instr := compute terms ++ store ++ bump

theorem dot_partition (out : Nat) (terms : List (Nat × Nat)) :
    Impl.MlKem.AArch64.Dot.dot out terms =
      .seq (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 out ++ Impl.MlKem.AArch64.vconsts ++
       ([.adrSym .x3 "VG_MLKEM_GAMMA", .movz .x .x11 32 0, .movz .x .x12 0 0] : List Instr)))
      (.loop (.block (body terms)) (.nonzero .x .x11)) := by
  simp only [Impl.MlKem.AArch64.Dot.dot,body,compute,clear,finish,store,bump,
    List.append_assoc,List.cons_append,List.nil_append,Impl.MlKem.AArch64.Dot.dotReduce]

end VG.Proof.MlKem.AArch64.Dot
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

structure StepPost (s : State) (p : Addr) (j : Nat) (O D : Nat → BitVec 32) (s' : State) : Prop where
  keep : Keep clob s s'
  constants : VConsts s'
  frame : Frame [polyRegion p] s.mem s'.mem
  out : CoeffsUpTo s'.mem p (j+8) O D
  x0 : s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 32
  x3 : s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 16
  x12 : s'.gpr .x12 = s.gpr .x12 + BitVec.ofNat 64 32
  x11 : s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1

theorem step_ok {s : State} (terms : List (Nat × Nat))
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {p : Addr} {j : Nat}
    (hc : VConsts s) (hn : terms.length ≤ 4)
    (hin : ∀ fg ∈ terms, TermInput s fg (F fg) (G fg))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 0) 16)
    (hg : Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 0) 16) Γ)
    (bg : ∀ e < 4, Γ e < 3329)
    (hx0 : s.gpr .x0 = coeffAddr p j) (hj : j+8 ≤ 256)
    (hw : ∀ i < 2, InRegions s.wr (coeffAddr p (j+4*i)) 16)
    {O D : Nat → BitVec 32} (ho : CoeffsUpTo s.mem p j O D)
    (hv : ∀ e < 8, O (j+e) = interleave (evenResult terms F G Γ) (oddResult terms F G) e) :
    WP isa (.block (body terms)) s (StepPost s p j O D) := by
  unfold body
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (compute_ok terms hc hn hin hr hg bg) fun s₁ ⟨k₁,c₁,l₁,l₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (store_ok (p := p) (j := j) (O := O) (D := D) (by rw [k₁.get .x0]; exact hx0) hj
    (fun i hi => by rw [k₁.wr]; exact hw i hi) c₁ l₁ l₂
    (by rw [k₁.mem]; exact ho) hv) fun s₂ ⟨k₂,c₂,f₂,o₂⟩ => ?_
  refine WP.mono (bump_ok s₂) fun s₃ ⟨k₃,v₃,e0,e3,e12,e11⟩ => ?_
  refine ⟨((k₁.keep.trans k₂).trans k₃.keep).mono, ⟨?_,?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₃]; exact c₂.q
  · rw [v₃]; exact c₂.m
  · rw [k₃.mem,←k₁.mem]; exact f₂
  · rw [k₃.mem]; exact o₂
  · rw [e0,k₂.get .x0,k₁.get .x0]
  · rw [e3,k₂.get .x3,k₁.get .x3]
  · rw [e12,k₂.get .x12,k₁.get .x12]
  · rw [e11,k₂.get .x11,k₁.get .x11]

end VG.Proof.MlKem.AArch64.Dot
