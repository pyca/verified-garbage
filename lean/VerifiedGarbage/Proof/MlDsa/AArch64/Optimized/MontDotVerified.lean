module

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontDot
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotField
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
public import VerifiedGarbage.Proof.MlDsa.FusedInverseContract
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontDot
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lanes
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotField
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
meta import VerifiedGarbage.Proof.MlDsa.FusedInverseContract
meta import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
meta import VerifiedGarbage.Proof.MlKem.AArch64.Vec
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `MlDsa.AArch64.Optimized.MontDotContract`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.MontDotLoad`, which only this module used -/

section

/-! ## From `MontDotVec.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

def reduce (d : VReg) : List Instr :=
  [.vop (.perm .uzp1 .s4 .v4 .v2 .v3),.vop (.mul .v4 .v4 .v17),
   .vop (.umlal false .v2 .v4 .v16),.vop (.umlal true .v3 .v4 .v16),
   .vop (.perm .uzp2 .s4 d .v2 .v3)]

theorem reduce_ok {d : VReg} {s : State} {rest : List Instr} {Q : State → Prop}
    (p : Nat → BitVec 64)
    (a₁ : s.v .v2=ofVDwords (p 0) (p 1)) (a₂ : s.v .v3=ofVDwords (p 2) (p 3))
    (hq : s.v .v16=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v17=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ t,VChg [.v2,.v3,.v4,d] s t →
      t.v d=ofVWords (redc (p 0)) (redc (p 1)) (redc (p 2)) (redc (p 3)) →
      WP isa (.block rest) t Q) : WP isa (.block (reduce d++rest)) s Q := by
  have eq_q : (BitVec.ofNat 32 q).setWidth 64=BitVec.ofNat 64 q := by decide
  refine wp_vop (d := .v4) rfl fun s₃ h₃ => ?_
  have a₃ : s₃.v .v4 = ofVWords ((p 0).extractLsb' 0 32) ((p 1).extractLsb' 0 32)
      ((p 2).extractLsb' 0 32) ((p 3).extractLsb' 0 32) := by
    rw [h₃.v, a₁, a₂]; exact unzip_wide false _ _ _ _
  refine wp_vop (d := .v4) rfl fun s₄ h₄ => ?_
  have a₄ : s₄.v .v4 = ofVWords (multiplier (p 0)) (multiplier (p 1))
      (multiplier (p 2)) (multiplier (p 3)) := by
    rw [h₄.v, a₃, h₃.get .v17, hqi, map2_words]
    rfl
  refine wp_vop (d := .v2) rfl fun s₅ h₅ => ?_
  have a₅ : s₅.v .v2 = ofVDwords
      (p 0 + (multiplier (p 0)).setWidth 64 * BitVec.ofNat 64 q)
      (p 1 + (multiplier (p 1)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₅.v, h₄.get .v2, h₃.get .v2, a₁, a₄,
      h₄.get .v16, h₃.get .v16, hq]
    simp only [ite_false, Bool.false_eq_true, Nat.zero_add, Nat.add_zero, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_0,
      vword_ofVWords_1, eq_q]
  refine wp_vop (d := .v3) rfl fun s₆ h₆ => ?_
  have a₆ : s₆.v .v3 = ofVDwords
      (p 2 + (multiplier (p 2)).setWidth 64 * BitVec.ofNat 64 q)
      (p 3 + (multiplier (p 3)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₆.v, h₅.get .v3, h₄.get .v3, h₃.get .v3, a₂, h₅.get .v4, a₄,
      h₅.get .v16, h₄.get .v16, h₃.get .v16, hq]
    simp only [ite_true, Nat.add_zero, Nat.reduceAdd, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_2,
      vword_ofVWords_3, eq_q]
  refine wp_vop (d := d) rfl fun s₇ h₇ => k s₇
    (VChg.mono (rs' := [.v2,.v3,.v4,d])
      ((((h₃.chg.trans h₄.chg).trans h₅.chg).trans h₆.chg).trans h₇.chg)
      (by simp (config := { contextual := true }) only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, true_or, or_true, implies_true, and_self, forall_eq_or_imp])) ?_
  rw [h₇.v, h₆.get .v2, a₅, a₆]
  exact unzip_wide true _ _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotAcc.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Arith.Neon

def dotAcc (first : Bool) : List Instr :=
  if first then [.vop (.umull false .v2 .v0 .v1),.vop (.umull true .v3 .v0 .v1)]
  else [.vop (.umlal false .v2 .v0 .v1),.vop (.umlal true .v3 .v0 .v1)]

def accWord (first : Bool) (p : BitVec 64) (a b : BitVec 32) : BitVec 64 :=
  if first then product a b else p+product a b

theorem dotAcc_ok (first : Bool) (p : Nat → BitVec 64) {s : State}
    (ha : first=false → s.v .v2=ofVDwords (p 0) (p 1)) (hb : first=false → s.v .v3=ofVDwords (p 2) (p 3))
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v2,.v3] s t →
      t.v .v2=ofVDwords (accWord first (p 0) (vword (s.v .v0) 0) (vword (s.v .v1) 0))
        (accWord first (p 1) (vword (s.v .v0) 1) (vword (s.v .v1) 1)) →
      t.v .v3=ofVDwords (accWord first (p 2) (vword (s.v .v0) 2) (vword (s.v .v1) 2))
        (accWord first (p 3) (vword (s.v .v0) 3) (vword (s.v .v1) 3)) →
      WP isa (.block rest) t Q) : WP isa (.block (dotAcc first++rest)) s Q := by
  cases first
  · refine wp_vop (d:=.v2) rfl fun a h1 => ?_
    have ea : a.v .v2=ofVDwords
        (p 0+product (vword (s.v .v0) 0) (vword (s.v .v1) 0))
        (p 1+product (vword (s.v .v0) 1) (vword (s.v .v1) 1)) := by
      rw [h1.v,ha rfl]
      simp only [Bool.false_eq_true,ite_false,Nat.zero_add,Nat.add_zero,
        vdword_ofVDwords_0,vdword_ofVDwords_1,product]
    refine wp_vop (d:=.v3) rfl fun b h2 => ?_
    refine k b ((h1.chg.trans h2.chg).mono (by simp)) ?_ ?_
    · rw [h2.get .v2,ea]; rfl
    · rw [h2.v,h1.get .v3,h1.get .v0,h1.get .v1,hb rfl]
      simp only [ite_true,Nat.add_zero,Nat.reduceAdd,vdword_ofVDwords_0,
        vdword_ofVDwords_1,accWord,Bool.false_eq_true,ite_false,product]
  · refine wp_vop (d:=.v2) rfl fun a h1 => ?_
    refine wp_vop (d:=.v3) rfl fun b h2 => ?_
    refine k b ((h1.chg.trans h2.chg).mono (by simp)) ?_ ?_
    · rw [h2.get .v2,h1.v]; rfl
    · rw [h2.v,h1.get .v0,h1.get .v1]; rfl

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotLoad.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Impl.MlDsa.AArch64.Optimized.MontDot

def dotTerm (off k : Nat) : List Instr :=
  [.ldrq .v0 .x1 (1024*k+off),.ldrq .v1 .x2 (1024*k+off)] ++
    dotAcc (decide (k=0))

def dotInput (s : State) (r : Reg) (off k e : Nat) : BitVec 32 :=
  vword (s.mem.read (s.gpr r+BitVec.ofNat 64 (1024*k+off)) 16) e

def dotAccum (s : State) (off n e : Nat) : BitVec 64 :=
  dotWord (fun k => dotInput s .x1 off k e) (fun k => dotInput s .x2 off k e) n

theorem dotInput_chg {s t : State} {rs : List VReg} (h : VChg rs s t) :
    dotInput t=dotInput s := by
  funext r off k e
  simp only [dotInput,h.mem,h.gpr]

theorem dotAccum_chg {s t : State} {rs : List VReg} (h : VChg rs s t) :
    dotAccum t=dotAccum s := by
  funext off n e
  simp only [dotAccum,dotInput_chg h]

theorem dotTerm_ok {s : State} {off k : Nat}
    (ho : (1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (1024*k+off)) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (1024*k+off)) 16)
    (h18 : k≠0 → s.v .v2=ofVDwords (dotAccum s off k 0) (dotAccum s off k 1))
    (h19 : k≠0 → s.v .v3=ofVDwords (dotAccum s off k 2) (dotAccum s off k 3))
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v0,.v1,.v2,.v3] s t →
      t.v .v2=ofVDwords (dotAccum s off (k+1) 0) (dotAccum s off (k+1) 1) →
      t.v .v3=ofVDwords (dotAccum s off (k+1) 2) (dotAccum s off (k+1) 3) →
      WP isa (.block rest) t Q) : WP isa (.block (dotTerm off k++rest)) s Q := by
  unfold dotTerm
  simp only [List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl ha fun a h1 => ?_
  have hb' : InRegions (a.rd++a.wr) (a.gpr .x2+BitVec.ofNat 64 (1024*k+off)) 16 := by
    rw [h1.chg.rd,h1.chg.wr,h1.chg.gpr]; exact hb
  refine wp_ldrq ho rfl hb' fun b h2 => ?_
  refine dotAcc_ok (decide (k=0)) (dotAccum s off k) ?_ ?_ fun t ht e18 e19 => ?_
  · intro hn
    rw [h2.get .v2,h1.get .v2]
    exact h18 (by simpa using hn)
  · intro hn
    rw [h2.get .v3,h1.get .v3]
    exact h19 (by simpa using hn)
  · have hc : VChg [.v0,.v1,.v2,.v3] s t :=
      ((h1.chg.trans h2.chg).trans ht).mono (by
        simp (config := { contextual := true }) only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, implies_true])
    have ev e : accWord (decide (k=0)) (dotAccum s off k e)
        (vword (b.v .v0) e) (vword (b.v .v1) e)=dotAccum s off (k+1) e := by
      rw [h2.get .v0,h1.v,h2.v,h1.chg.mem,h1.chg.gpr]
      change accWord (decide (k=0)) (dotAccum s off k e)
        (dotInput s .x1 off k e) (dotInput s .x2 off k e)=_
      simp only [dotAccum,dotWord_succ,accWord]
      by_cases hk : k=0
      · subst k; simp [dotWord_zero]
      · simp [hk]
    exact next t hc (by simpa only [ev] using e18) (by simpa only [ev] using e19)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

end

end

/-! ### `MlDsa.MontDotContract`, which this module and modules that import it used -/

section

/-!
# ML-DSA: the contract of Montgomery-scaled dot products

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- A canonical Montgomery-scaled sum, before the caller subtracts another
Montgomery product and performs the inverse transform. -/
def montDotSig (count : Nat) : Sig where
  params := [("out",.array true .u32 256),("a",.array false .u32 (256*count)),
    ("b",.array false .u32 (256*count))]

def montDotContract {M : ISA} (A : Abi M) (count : Nat) (stack : Nat := 0) : Contract M :=
  (montDotSig count).contract A
    (pre := fun _out a b m =>
      (∀j<count,PositiveReduced m (a+BitVec.ofNat 64 (1024*j))) ∧
      (∀j<count,PositiveReduced m (b+BitVec.ofNat 64 (1024*j))))
    (post := fun out a b m m' _ => PolyIs m' out
      ((dotNTT
        (fun j=>polyAt m (a+BitVec.ofNat 64 (1024*j)))
        (fun j=>polyAt m (b+BitVec.ofNat 64 (1024*j))) count).map (· * montgomeryRInv)))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa

end

end

/-! ### `MlDsa.AArch64.Optimized.MontDotMem`, which only this module used -/

section

/-! ## From `MontDotTerms.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

theorem dotTerms_ok (n : Nat) {s : State} {off : Nat}
    (ho : ∀k<n,(1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (1024*k+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v0,.v1,.v2,.v3] s t →
      (n≠0 → t.v .v2=ofVDwords (dotAccum s off n 0) (dotAccum s off n 1)) →
      (n≠0 → t.v .v3=ofVDwords (dotAccum s off n 2) (dotAccum s off n 3)) →
      WP isa (.block rest) t Q) :
    WP isa (.block ((List.range n).flatMap (dotTerm off)++rest)) s Q := by
  induction n generalizing s rest with
  | zero => exact next s (VChg.refl _ _) (by simp) (by simp)
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    refine ih (fun k hk => ho k (by omega_using [hk])) (fun k hk => hr k (by omega_using [hk])) fun a ha e18 e19 => ?_
    have hr' : InRegions (a.rd++a.wr) (a.gpr .x1+BitVec.ofNat 64 (1024*n+off)) 16 ∧
        InRegions (a.rd++a.wr) (a.gpr .x2+BitVec.ofNat 64 (1024*n+off)) 16 := by
      rw [ha.rd,ha.wr,ha.gpr]; exact hr n (by omega_using [])
    refine dotTerm_ok (ho n (by omega_using [])) hr'.1 hr'.2 ?_ ?_ fun t ht a18 a19 => ?_
    · rw [dotAccum_chg ha]; exact e18
    · rw [dotAccum_chg ha]; exact e19
    · refine next t ((ha.trans ht).mono (by simp)) (fun _ => ?_) (fun _ => ?_)
      · simpa only [dotAccum_chg ha] using a18
      · simpa only [dotAccum_chg ha] using a19

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotReduce.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg Lanes)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

/-- The selected five-instruction REDC and two-instruction correction produce
canonical Montgomery residues, including zero and values just above q. -/
theorem canonicalReduce_ok (p : Nat→BitVec 64) {s : State}
    (a₁ : s.v .v2=ofVDwords (p 0) (p 1)) (a₂ : s.v .v3=ofVDwords (p 2) (p 3))
    (hq : s.v .v16=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v17=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (hp : ∀e<4,(p e).toNat<q*2^32)
    {rest : List Instr} {Q : State→Prop}
    (next : ∀t,VChg [.v0,.v2,.v3,.v4] s t →
      Lanes (t.v .v0) (fun e=>mont (p e).toNat%q) → WP isa (.block rest) t Q) :
    WP isa (.block (reduce .v0++Impl.MlDsa.AArch64.Arith.Neon.csub .v0 .v4++rest)) s Q := by
  rw [List.append_assoc]
  refine reduce_ok p a₁ a₂ hq hqi fun a ha hv=>?_
  have hqa : Lanes (a.v .v16) (fun _=>q) := by
    rw [ha.get .v16 (by decide),hq]
    intro e he
    rcases (show e=0∨e=1∨e=2∨e=3 by omega_using [he]) with rfl|rfl|rfl|rfl <;> rfl
  have hl : Lanes (a.v .v0) (fun e=>mont (p e).toNat) := by
    rw [hv]
    intro e he
    have hr := redc_nat (p e) (hp e he)
    rcases (show e=0∨e=1∨e=2∨e=3 by omega_using [he]) with rfl|rfl|rfl|rfl <;>
      simpa only [vword_ofVWords_0,vword_ofVWords_1,vword_ofVWords_2,vword_ofVWords_3] using hr
  refine csub_ok (by decide) hqa hl (fun e he=>mont_lt (hp e he)) fun t ht hval=>?_
  exact next t ((ha.trans ht).mono (by simp)) hval

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotBlock.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg Lanes)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

 theorem product_eq (k : Nat) : Impl.MlDsa.AArch64.Optimized.MontDot.product k=dotTerm 0 k := by
  simp only [Impl.MlDsa.AArch64.Optimized.MontDot.product,dotTerm,Nat.add_zero,dotAcc]
  by_cases hk : k=0 <;> simp only [hk,decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true]

theorem block_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) {s : State}
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (1024*k)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (1024*k)) 16)
    (ha : ∀k<n,∀e<4,(dotInput s .x1 0 k e).toNat<3*q)
    (hb : ∀k<n,∀e<4,(dotInput s .x2 0 k e).toNat<3*q)
    (hq : s.v .v16=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v17=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    {rest : List Instr} {Q : State→Prop}
    (next : ∀t,VChg [.v0,.v1,.v2,.v3,.v4] s t →
      Lanes (t.v .v0) (fun e=>mont (dotAccum s 0 n e).toNat%q) → WP isa (.block rest) t Q) :
    WP isa (.block ((List.range n).flatMap Impl.MlDsa.AArch64.Optimized.MontDot.product++
      Impl.MlDsa.AArch64.Optimized.MontDot.reduce++Impl.MlDsa.AArch64.Arith.Neon.csub .v0 .v4++rest)) s Q := by
  rw [show Impl.MlDsa.AArch64.Optimized.MontDot.product=dotTerm 0 from funext product_eq]
  simp only [List.append_assoc]
  refine dotTerms_ok n (off:=0) ?_ ?_ fun a hA e2 e3=>?_
  · intro k hk
    constructor
    · omega_using []
    · omega_using [hn7, hk]
  · intro k hk
    simpa only [Nat.add_zero] using hr k hk
  · change WP isa (.block (reduce .v0++Impl.MlDsa.AArch64.Arith.Neon.csub .v0 .v4++rest)) a Q
    refine canonicalReduce_ok (dotAccum s 0 n) (e2 (by omega_using [hn])) (e3 (by omega_using [hn])) ?_ ?_ ?_ fun t ht hv=>?_
    · rw [hA.get .v16 (by decide)];exact hq
    · rw [hA.get .v17 (by decide)];exact hqi
    · intro e he
      have hw := dotWord_nat (fun k=>dotInput s .x1 0 k e) (fun k=>dotInput s .x2 0 k e) hn7
        (fun k hk=>ha k hk e he) (fun k hk=>hb k hk e he)
      unfold dotAccum
      rw [hw]
      exact dotNat_lt_qR _ _ hn7 (fun k hk=>ha k hk e he) (fun k hk=>hb k hk e he)
    · exact next t ((hA.trans ht).mono (by simp)) hv

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotMem.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_strq wp_nil Keep)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

theorem body_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) {s : State} (hc : VConsts s)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (1024*k)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (1024*k)) 16)
    (ha : ∀k<n,∀e<4,(dotInput s .x1 0 k e).toNat<3*q)
    (hb : ∀k<n,∀e<4,(dotInput s .x2 0 k e).toNat<3*q)
    (hw : InRegions s.wr (s.gpr .x0) 16) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.MontDot.body n)) s fun t=>
      ∃v,t.mem=s.mem.write (s.gpr .x0) 16 v ∧
      Lanes v (fun e=>mont (dotAccum s 0 n e).toNat%q) ∧ VConsts t ∧
      t.gpr .x0=s.gpr .x0+16 ∧ t.gpr .x1=s.gpr .x1+16 ∧ t.gpr .x2=s.gpr .x2+16 ∧
      t.gpr .x12=s.gpr .x12-1 ∧ Keep [.x0,.x1,.x2,.x12] s t := by
  unfold Impl.MlDsa.AArch64.Optimized.MontDot.body
  refine block_ok hn hn7 hr ha hb hc.q hc.qi fun a hA hv=>?_
  refine wp_strq (by decide) rfl (by simpa only [hA.wr,hA.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw) fun b hB=>?_
  have hk : StepKeep [.v0,.v1,.v2,.v3,.v4] s b :=
    (StepKeep.ofChg hA (by decide)).trans (StepKeep.ofMem hB)
  have hm : b.mem=s.mem.write (s.gpr .x0) 16 (a.v .v0) := by
    simp only [hB.mem,hA.mem,hA.gpr,BitVec.add_zero]
  have cb : VConsts b := ⟨by rw [hk.vec .v16 (by decide)];exact hc.q,
    by rw [hk.vec .v17 (by decide)];exact hc.qi⟩
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
      .addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1]) b fun u=>
      u.mem=b.mem ∧ u.v=b.v ∧ u.gpr .x0=b.gpr .x0+16 ∧ u.gpr .x1=b.gpr .x1+16 ∧
      u.gpr .x2=b.gpr .x2+16 ∧ u.gpr .x12=b.gpr .x12-1 := by
    arun [State.write,BitVec.ofNat_eq_ofNat]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x0,.x1,.x2,.x12] scalar (by decide))
    fun u ⟨⟨hum,huv,h0,h1,h2,h12⟩,ku⟩=>?_
  refine ⟨a.v .v0,hum.trans hm,hv,?_,?_,?_,?_,?_,(hk.keep.trans ku).mono⟩
  · exact ⟨by rw [huv];exact cb.q,by rw [huv];exact cb.qi⟩
  · simpa only [hk.keep.get .x0] using h0
  · simpa only [hk.keep.get .x1] using h1
  · simpa only [hk.keep.get .x2] using h2
  · simpa only [hk.keep.get .x12] using h12

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

end

end


/-! ## From `MontDotState.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep Lanes)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon

structure Inv (s₀ : State) (v : Nat→Nat) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0=coeffAddr (s₀.gpr .x0) (4*i)
  x1 : s.gpr .x1=coeffAddr (s₀.gpr .x1) (4*i)
  x2 : s.gpr .x2=coeffAddr (s₀.gpr .x2) (4*i)
  consts : VConsts s
  keep : Keep [.x0,.x1,.x2,.x9,.x10,.x12] s₀ s
  frame : Frame [pR (s₀.gpr .x0)] s₀.mem s.mem
  coeff : ∀k<256,(coeffAt s.mem (s₀.gpr .x0) k).toNat=
    if k<4*i then v k else (coeffAt s₀.mem (s₀.gpr .x0) k).toNat

theorem inv_step {s₀ s t : State} {v : Nat→Nat} {i : Nat}
    (hi : i<64) (h : Inv s₀ v i s) {x : BitVec 128}
    (hm : t.mem=s.mem.write (s.gpr .x0) 16 x) (hx : Lanes x (fun e=>v (4*i+e)))
    (hc : VConsts t) (h0 : t.gpr .x0=s.gpr .x0+16)
    (h1 : t.gpr .x1=s.gpr .x1+16) (h2 : t.gpr .x2=s.gpr .x2+16)
    (hk : Keep [.x0,.x1,.x2,.x12] s t) : Inv s₀ v (i+1) t where
  x0 := by rw [h0,h.x0];simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using coeffAddr_add (s₀.gpr .x0) (4*i) 4
  x1 := by rw [h1,h.x1];simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using coeffAddr_add (s₀.gpr .x1) (4*i) 4
  x2 := by rw [h2,h.x2];simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using coeffAddr_add (s₀.gpr .x2) (4*i) 4
  consts := hc
  keep := (h.keep.trans hk).mono
  frame := by
    rw [hm,h.x0]
    exact h.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  coeff k hk := by
    rw [hm,h.x0,coeffAt_write16 _ _ (by omega_arith) _ hk]
    by_cases he : 4*i≤k ∧ k<4*i+4
    · rw [ite_eq_left he,hx (k-4*i) (by omega_arith),ite_eq_left (by omega_arith)]
      exact congrArg v (by omega_arith)
    · rw [ite_eq_right he,h.coeff k hk]
      have hh : (k<4*(i+1))=(k<4*i) := propext (by omega_arith)
      simp only [hh]

theorem pro_ok (s₀ : State) (v : Nat→Nat) :
    WP isa (.block (Impl.MlDsa.AArch64.Arith.Neon.consts++([.movz .x .x12 64 0] : List Instr))) s₀
      fun s=>Inv s₀ v 0 s ∧ s.gpr .x12=BitVec.ofNat 64 64 := by
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₀) fun t ⟨hc,hm,hk⟩=>?_
  have scalar : WP isa (.block [.movz .x .x12 64 0]) t fun u=>
      u.gpr .x12=BitVec.ofNat 64 64 ∧ u.mem=t.mem ∧ u.v=t.v := by arun [State.write]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x12] scalar (by decide))
    fun u ⟨⟨h12,hum,huv⟩,ku⟩=>⟨?_,h12⟩
  have keep := hk.trans ku
  refine ⟨?_,?_,?_,?_,keep.mono,?_,?_⟩
  · rw [keep.get .x0];simp [coeffAddr]
  · rw [keep.get .x1];simp [coeffAddr]
  · rw [keep.get .x2];simp [coeffAddr]
  · exact ⟨by rw [huv];exact hc.q,by rw [huv];exact hc.qi⟩
  · rw [hum,hm];exact Frame.refl _ _
  · intro k _;rw [hum,hm];simp

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotReads.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon

/-- Each source polynomial is immutable and disjoint from the output. -/
structure Pre (n : Nat) (s : State) : Prop where
  output : pR (s.gpr .x0)∈s.wr
  input : ∀r∈[Reg.x1,.x2],∀j<n,InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 (1024*j)) 1024
  apart : ∀r∈[Reg.x1,.x2],∀j<n,(pR (s.gpr r+BitVec.ofNat 64 (1024*j))).Disjoint (pR (s.gpr .x0))
  bound : ∀r∈[Reg.x1,.x2],∀j<n,∀k<256,
    (coeffAt s.mem (s.gpr r+BitVec.ofNat 64 (1024*j)) k).toNat<3*q

def inputWord (s : State) (r : Reg) (j k : Nat) : BitVec 32 :=
  coeffAt s.mem (s.gpr r+BitVec.ofNat 64 (1024*j)) k

theorem input_current {s₀ s : State} {v : Nat→Nat} {i n : Nat} (hi : i<64)
    (hp : Pre n s₀) (h : Inv s₀ v i s) {r : Reg} (hr : r∈[Reg.x1,.x2]) {j e : Nat}
    (hj : j<n) (he : e<4) : dotInput s r 0 j e=inputWord s₀ r j (4*i+e) := by
  have ha : s.gpr r=coeffAddr (s₀.gpr r) (4*i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.x1
    · exact h.x2
  have addr : s.gpr r+BitVec.ofNat 64 (1024*j+0)=
      coeffAddr (s₀.gpr r+BitVec.ofNat 64 (1024*j)) (4*i) := by
    rw [ha]
    simp only [coeffAddr,Nat.add_zero]
    bv_omega
  unfold dotInput inputWord
  rw [addr,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq]
  exact coeffAt_frame h.frame (by intro r' hr';have hh:=List.mem_singleton.mp hr';subst r';exact hp.apart r hr j hj) (by change 4*i+e<256;omega_arith)

theorem reads {s₀ s : State} {v : Nat→Nat} {i n : Nat} (hi : i<64)
    (hp : Pre n s₀) (h : Inv s₀ v i s) {r : Reg} (hr : r∈[Reg.x1,.x2]) {j : Nat}
    (hj : j<n) : InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 (1024*j)) 16 := by
  have ha : s.gpr r=coeffAddr (s₀.gpr r) (4*i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.x1
    · exact h.x2
  rw [h.keep.rd,h.keep.wr,ha]
  have addr : coeffAddr (s₀.gpr r) (4*i)+BitVec.ofNat 64 (1024*j)=
      coeffAddr (s₀.gpr r+BitVec.ofNat 64 (1024*j)) (4*i) := by
    simp only [coeffAddr];bv_omega
  rw [addr]
  exact VG.CallLay.inRegions_sub (off:=4*(4*i)) (l:=16) (hp.input r hr j hj) (by omega_arith) (by omega_arith)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon

def result (s : State) (n k : Nat) : Nat :=
  mont (dotNat (fun j=>inputWord s .x1 j k) (fun j=>inputWord s .x2 j k) n)%q

theorem result_current {s₀ s : State} {v : Nat→Nat} {i n e : Nat}
    (hi : i<64) (hn : n≤7) (he : e<4) (hp : Pre n s₀) (h : Inv s₀ v i s) :
    mont (dotAccum s 0 n e).toNat%q=result s₀ n (4*i+e) := by
  have ha (j : Nat) (hj : j<n) :=  input_current hi hp h (r:=Reg.x1) (by simp) (j:=j) hj he
  have hb (j : Nat) (hj : j<n) :=  input_current hi hp h (r:=Reg.x2) (by simp) (j:=j) hj he
  have halt : ∀j<n,(dotInput s .x1 0 j e).toNat<3*q := by
    intro j hj;rw [ha j hj];exact hp.bound .x1 (by simp) j hj _ (by omega_arith)
  have hblt : ∀j<n,(dotInput s .x2 0 j e).toNat<3*q := by
    intro j hj;rw [hb j hj];exact hp.bound .x2 (by simp) j hj _ (by omega_arith)
  rw [dotAccum,dotWord_nat _ _ hn halt hblt,dotNat_congr _ _ _ _ n ha hb]
  rfl

theorem run_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) (s₀ : State) (hp : Pre n s₀) :
    WP isa (Impl.MlDsa.AArch64.Optimized.MontDot.dot n) s₀ (Inv s₀ (result s₀ n) 64) := by
  unfold Impl.MlDsa.AArch64.Optimized.MontDot.dot
  refine WP.seq (WP.mono (pro_ok s₀ (result s₀ n)) fun s ⟨hs,hcnt⟩=>?_)
  refine VG.Proof.MlDsa.AArch64.Arith.wp_countdown (cnt:=.x12) (N:=64)
    (by decide) (by decide) (Inv s₀ _) (fun i hi s h _=>?_) hs hcnt
  have hr (j : Nat) (hj : j<n) :=  And.intro (reads hi hp h (r:=Reg.x1) (by simp) (j:=j) hj)
    (reads hi hp h (r:=Reg.x2) (by simp) (j:=j) hj)
  have ha : ∀j<n,∀e<4,(dotInput s .x1 0 j e).toNat<3*q := by
    intro j hj e he
    rw [input_current hi hp h (r:=Reg.x1) (by simp) (j:=j) hj he]
    exact hp.bound .x1 (by simp) j hj _ (by omega_arith)
  have hb : ∀j<n,∀e<4,(dotInput s .x2 0 j e).toNat<3*q := by
    intro j hj e he
    rw [input_current hi hp h (r:=Reg.x2) (by simp) (j:=j) hj he]
    exact hp.bound .x2 (by simp) j hj _ (by omega_arith)
  have hw : InRegions s.wr (s.gpr .x0) 16 := by
    rw [h.keep.wr,h.x0]
    exact ⟨_,hp.output,Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.mono (body_ok hn hn7 h.consts hr ha hb hw) fun t ⟨x,hm,hx,hc,h0,h1,h2,h12,hk⟩=>?_
  refine ⟨inv_step hi h hm ?_ hc h0 h1 h2 hk,h12⟩
  intro e he
  exact (hx e he).trans (result_current hi hn7 he hp h)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

 theorem montCanonical_eq (a : Nat) : ofNat (mont a%q)=ofInt ((mont a:Int)-q) := by
  apply Fin.ext
  simp only [ofNat,Fin.val_ofNat,Nat.mod_mod]
  have h := VG.Proof.MlDsa.KeyGen.ofInt_val ((mont a:Int)-q)
  apply Int.ofNat_inj.mp
  rw [h,Int.natCast_emod]
  change (mont a:Int)%8380417=((mont a:Int)-8380417)%8380417
  omega_arith

def value (s : State) (n : Nat) : Poly :=
  (dotNTT (fun j=>polyAt s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j)))
    (fun j=>polyAt s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j))) n).map (· * montgomeryRInv)

theorem result_field (s : State) {n : Nat} (hn : n≤7) (hp : Pre n s) {i : Nat} (hi : i<256) :
    ofNat (result s n i)=(value s n)[i]! := by
  have ha : ∀j<n,(inputWord s .x1 j i).toNat<3*q := fun j hj=>hp.bound .x1 (by simp) j hj i hi
  have hb : ∀j<n,(inputWord s .x2 j i).toNat<3*q := fun j hj=>hp.bound .x2 (by simp) j hj i hi
  have hf := centeredDot_field (fun j=>inputWord s .x1 j i) (fun j=>inputWord s .x2 j i)
    (fun j=>polyAt s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j)))
    (fun j=>polyAt s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j))) hn ha hb hi
    (fun j _=>by rw [ofInt_nat_eq];exact (polyAt_get _ _ hi).symm)
    (fun j _=>by rw [ofInt_nat_eq];exact (polyAt_get _ _ hi).symm)
  rw [centeredDot_int _ _ hn ha hb] at hf
  rw [result,montCanonical_eq]
  exact hf

theorem result_value (s : State) {n : Nat} (hn : n≤7) (hp : Pre n s) {i : Nat} (hi : i<256) :
    result s n i=((value s n)[i]!).val := by
  have h := congrArg Fin.val (result_field s hn hp hi)
  rw [ofNat,Fin.val_ofNat,Nat.mod_eq_of_lt (show result s n i<q from Nat.mod_lt _ (by decide))] at h
  exact h

theorem output_ok {s₀ s : State} {n : Nat} (hn : n≤7) (hp : Pre n s₀)
    (h : Inv s₀ (result s₀ n) 64 s) : PolyIs s.mem (s₀.gpr .x0) (value s₀ n) := by
  apply polyIs_of_toNat
  intro i hi
  rw [h.coeff i hi,ite_eq_left (by change i<256;exact hi)]
  exact result_value s₀ hn hp hi

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Arith (pR)

def contract (n : Nat) : Contract isa where
  pre := Pre n
  post s t := PolyIs t.mem (s.gpr .x0) (value s n)
  pub s t := (∀r∈[Reg.x0,.x1,.x2],s.gpr r=t.gpr r) ∧ s.sp=t.sp

theorem pre {n : Nat} (hn : n≤7) {s : State} (h : (montDotContract abi n).pre s) : Pre n s := by
  sig_pre [montDotContract,montDotSig,abi,argRegs,stackBelow] at h
  have he : 256*n*4=1024*n := by omega_arith
  rw [he] at h
  obtain ⟨hr,hw,ha,hb,_,_,_,hpa,hpb⟩ := h
  refine ⟨by rw [hw];simp [pR],?_,?_,?_⟩
  · intro r hr' j hj
    apply VG.CallLay.inRegions_sub (n:=1024*n) (off:=1024*j) (l:=1024)
    · refine ⟨⟨s.gpr r,1024*n⟩,?_,by simp [Region.Contains]⟩
      rw [hr]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
      rcases hr' with rfl|rfl <;> simp
    · omega_arith
    · omega_arith
  · intro r hr' j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
    rcases hr' with rfl|rfl
    · exact ha.symm.sub_left (Offset.sub_base _ (by omega_arith))
    · exact hb.symm.sub_left (Offset.sub_base _ (by omega_arith))
  · intro r hr' j hj i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
    rcases hr' with rfl|rfl
    · exact hpa j hj i hi
    · exact hpb j hj i hi

theorem correct {n : Nat} (hc : n=4∨n=5∨n=7) (s : State) (hp : (contract n).pre s) :
    ∃tr t,Exec isa (VG.Impl.MlDsa.AArch64.Optimized.MontDot.dot n) s tr t ∧
      abiPreserved s t ∧ (contract n).post s t := by
  obtain ⟨tr,t,he,hi⟩ := run_ok (by omega_arith) (by omega_arith) s hp
  refine ⟨tr,t,he,?_,output_ok (by omega_arith) hp hi⟩
  rcases hc with rfl|rfl|rfl
  all_goals exact VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he (by decide +kernel)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.MontDot (dot)

def sat (n : Nat) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 16384 else if r=.x2 then 32768 else 0
  sp := 131072
  mem := fun _=>0
  rd := [⟨16384,1024*n⟩,⟨32768,1024*n⟩]
  wr := [⟨4096,1024⟩]

theorem sat_pre {n : Nat} (hn : n≤7) : (montDotContract abi n).pre (sat n) := by
  sig_pre [montDotContract,montDotSig,abi,argRegs,stackBelow,sat]
  have he : 256*n*4=1024*n := by omega_using []
  rw [he]
  refine ⟨rfl,?_,?_,by decide,?_,?_,?_,?_⟩
  · exact Region.disjoint_of_sep (by simp [Region.sep];omega_using [hn])
  · exact Region.disjoint_of_sep (by simp [Region.sep];omega_using [hn])
  · simp;omega_using [hn]
  · simp;omega_using [hn]
  all_goals intro j hj i hi; simp [coeffAt,Mem.readW,Mem.read,VG.Spec.MlDsa.q]

theorem pub {n : Nat} {s t : State} (h : (montDotContract abi n).pub s t) : (contract n).pub s t := by
  sig_pub [montDotContract,montDotSig,abi,argRegs] at h
  refine ⟨?_,h.1⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem ct {n : Nat} (hc : n=4∨n=5∨n=7) : ConstantTime isa (contract n).pre (contract n).pub (dot n) := by
  rcases hc with rfl|rfl|rfl
  all_goals
    exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2])
      (fun _ _ _ _ h=>VG.Proof.MlKem.AArch64.agree_of h.2 h.1) (by taint_decide)

theorem verified {n : Nat} (hc : n=4∨n=5∨n=7) : Verified target (dot n) (montDotContract abi n) := by
  refine Verified.of_correct (correct hc) (ct hc)
    {pre:=fun _ h=>pre (by omega_using [hc]) h,post:=?_,pub:=fun _ _ _ _ h=>pub h,sat:=⟨sat n,sat_pre (by omega_using [hc])⟩}
  intro s t _ h
  sig_post [montDotContract,montDotSig,abi,argRegs]
  exact h
end VG.Proof.MlDsa.AArch64.Optimized.MontDot
