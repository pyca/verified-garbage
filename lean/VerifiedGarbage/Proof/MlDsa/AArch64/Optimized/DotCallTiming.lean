module

public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.DotInverse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBank
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFirstLoop
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCore
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore
public import VerifiedGarbage.Proof.MlDsa.FusedInverseContract
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.InverseTable
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotField
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBatch
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductLoad
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Dot
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotWord
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Word
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec

/-! ### `MlDsa.AArch64.Optimized.DotContract`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.DotMemory`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.DotBatch`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.DotVec`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Impl.MlDsa.AArch64.Optimized

def dotMont (d : VReg) : List Instr := (dotReduce d).take 5

theorem dotMont_ok {d : VReg} {s : State} {rest : List Instr} {Q : State → Prop}
    (p : Nat → BitVec 64)
    (a₁ : s.v .v18=ofVDwords (p 0) (p 1)) (a₂ : s.v .v19=ofVDwords (p 2) (p 3))
    (hq : s.v .v31=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v30=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ t,VChg [.v18,.v19,.v20,d] s t →
      t.v d=ofVWords (redc (p 0)) (redc (p 1)) (redc (p 2)) (redc (p 3)) →
      WP isa (.block rest) t Q) : WP isa (.block (dotMont d++rest)) s Q := by
  have eq_q : (BitVec.ofNat 32 q).setWidth 64=BitVec.ofNat 64 q := by decide
  refine wp_vop (d := .v20) rfl fun s₃ h₃ => ?_
  have a₃ : s₃.v .v20 = ofVWords ((p 0).extractLsb' 0 32) ((p 1).extractLsb' 0 32)
      ((p 2).extractLsb' 0 32) ((p 3).extractLsb' 0 32) := by
    rw [h₃.v, a₁, a₂]; exact unzip_wide false _ _ _ _
  refine wp_vop (d := .v20) rfl fun s₄ h₄ => ?_
  have a₄ : s₄.v .v20 = ofVWords (multiplier (p 0)) (multiplier (p 1))
      (multiplier (p 2)) (multiplier (p 3)) := by
    rw [h₄.v, a₃, h₃.get .v30, hqi, map2_words]
    rfl
  refine wp_vop (d := .v18) rfl fun s₅ h₅ => ?_
  have a₅ : s₅.v .v18 = ofVDwords
      (p 0 + (multiplier (p 0)).setWidth 64 * BitVec.ofNat 64 q)
      (p 1 + (multiplier (p 1)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₅.v, h₄.get .v18, h₃.get .v18, a₁, a₄,
      h₄.get .v31, h₃.get .v31, hq]
    simp only [ite_false, Bool.false_eq_true, Nat.zero_add, Nat.add_zero, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_0,
      vword_ofVWords_1, eq_q]
  refine wp_vop (d := .v19) rfl fun s₆ h₆ => ?_
  have a₆ : s₆.v .v19 = ofVDwords
      (p 2 + (multiplier (p 2)).setWidth 64 * BitVec.ofNat 64 q)
      (p 3 + (multiplier (p 3)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₆.v, h₅.get .v19, h₄.get .v19, h₃.get .v19, a₂, h₅.get .v20, a₄,
      h₅.get .v31, h₄.get .v31, h₃.get .v31, hq]
    simp only [ite_true, Nat.add_zero, Nat.reduceAdd, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_2,
      vword_ofVWords_3, eq_q]
  refine wp_vop (d := d) rfl fun s₇ h₇ => k s₇
    (VChg.mono (rs' := [.v18,.v19,.v20,d])
      ((((h₃.chg.trans h₄.chg).trans h₅.chg).trans h₆.chg).trans h₇.chg)
      (by intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_
  rw [h₇.v, h₆.get .v18, a₅, a₆]
  exact unzip_wide true _ _ _ _


theorem dotReduce_ok {d : VReg} (hd : d≠.v31) {s : State} {rest : List Instr} {Q : State → Prop}
    (p : Nat → BitVec 64)
    (a₁ : s.v .v18=ofVDwords (p 0) (p 1)) (a₂ : s.v .v19=ofVDwords (p 2) (p 3))
    (hq : s.v .v31=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v30=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ t,VChg [.v18,.v19,.v20,d] s t →
      (∀e<4,vword (t.v d) e=redc (p e)-BitVec.ofNat 32 q) →
      WP isa (.block rest) t Q) : WP isa (.block (dotReduce d++rest)) s Q := by
  change WP isa (.block (dotMont d++(.vop (.sub .s4 d d .v31)::rest))) s Q
  refine dotMont_ok p a₁ a₂ hq hqi fun t ht hv => ?_
  refine wp_vop (d:=d) rfl fun u hu => ?_
  refine k u ((ht.trans hu.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [hu.v,VG.AArch64.vword_map2 _ _ _ he,ht.get .v31 (by simp [Ne.symm hd]),hv,hq]
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_using [he]) with rfl | rfl | rfl | rfl <;>
      simp only [vword_ofVWords_0,vword_ofVWords_1,vword_ofVWords_2,vword_ofVWords_3]

end VG.Proof.MlDsa.AArch64.Optimized

end

end


-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/DotTerms.lean`, which only this module imported.
section

/-! ## From `DotAcc.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Arith.Neon

def dotAcc (first : Bool) : List Instr :=
  if first then [.vop (.umull false .v18 .v16 .v17),.vop (.umull true .v19 .v16 .v17)]
  else [.vop (.umlal false .v18 .v16 .v17),.vop (.umlal true .v19 .v16 .v17)]

def accWord (first : Bool) (p : BitVec 64) (a b : BitVec 32) : BitVec 64 :=
  if first then product a b else p+product a b

theorem dotAcc_ok (first : Bool) (p : Nat → BitVec 64) {s : State}
    (ha : first=false → s.v .v18=ofVDwords (p 0) (p 1)) (hb : first=false → s.v .v19=ofVDwords (p 2) (p 3))
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v18,.v19] s t →
      t.v .v18=ofVDwords (accWord first (p 0) (vword (s.v .v16) 0) (vword (s.v .v17) 0))
        (accWord first (p 1) (vword (s.v .v16) 1) (vword (s.v .v17) 1)) →
      t.v .v19=ofVDwords (accWord first (p 2) (vword (s.v .v16) 2) (vword (s.v .v17) 2))
        (accWord first (p 3) (vword (s.v .v16) 3) (vword (s.v .v17) 3)) →
      WP isa (.block rest) t Q) : WP isa (.block (dotAcc first++rest)) s Q := by
  cases first
  · refine wp_vop (d:=.v18) rfl fun a h1 => ?_
    have ea : a.v .v18=ofVDwords
        (p 0+product (vword (s.v .v16) 0) (vword (s.v .v17) 0))
        (p 1+product (vword (s.v .v16) 1) (vword (s.v .v17) 1)) := by
      rw [h1.v,ha rfl]
      simp only [Bool.false_eq_true,ite_false,Nat.zero_add,Nat.add_zero,
        vdword_ofVDwords_0,vdword_ofVDwords_1,product]
    refine wp_vop (d:=.v19) rfl fun b h2 => ?_
    refine k b ((h1.chg.trans h2.chg).mono (by simp)) ?_ ?_
    · rw [h2.get .v18,ea]; rfl
    · rw [h2.v,h1.get .v19,h1.get .v16,h1.get .v17,hb rfl]
      simp only [ite_true,Nat.add_zero,Nat.reduceAdd,vdword_ofVDwords_0,
        vdword_ofVDwords_1,accWord,Bool.false_eq_true,ite_false,product]
  · refine wp_vop (d:=.v18) rfl fun a h1 => ?_
    refine wp_vop (d:=.v19) rfl fun b h2 => ?_
    refine k b ((h1.chg.trans h2.chg).mono (by simp)) ?_ ?_
    · rw [h2.get .v18,h1.v]; rfl
    · rw [h2.v,h1.get .v16,h1.get .v17]; rfl

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `DotLoad.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Impl.MlDsa.AArch64.Optimized

def dotInput (s : State) (r : Reg) (off k e : Nat) : BitVec 32 :=
  vword (s.mem.read (s.gpr r+BitVec.ofNat 64 (1024*k+off)) 16) e

def dotAccum (s : State) (off n e : Nat) : BitVec 64 :=
  dotWord (fun k => dotInput s .x13 off k e) (fun k => dotInput s .x14 off k e) n

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
    (ha : InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16)
    (h18 : k≠0 → s.v .v18=ofVDwords (dotAccum s off k 0) (dotAccum s off k 1))
    (h19 : k≠0 → s.v .v19=ofVDwords (dotAccum s off k 2) (dotAccum s off k 3))
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v16,.v17,.v18,.v19] s t →
      t.v .v18=ofVDwords (dotAccum s off (k+1) 0) (dotAccum s off (k+1) 1) →
      t.v .v19=ofVDwords (dotAccum s off (k+1) 2) (dotAccum s off (k+1) 3) →
      WP isa (.block rest) t Q) : WP isa (.block (dotTerm off k++rest)) s Q := by
  unfold dotTerm
  simp only [List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl ha fun a h1 => ?_
  have hb' : InRegions (a.rd++a.wr) (a.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16 := by
    rw [h1.chg.rd,h1.chg.wr,h1.chg.gpr]; exact hb
  refine wp_ldrq ho rfl hb' fun b h2 => ?_
  have he : (if k=0 then [Instr.vop (.umull false .v18 .v16 .v17),.vop (.umull true .v19 .v16 .v17)]
      else [.vop (.umlal false .v18 .v16 .v17),.vop (.umlal true .v19 .v16 .v17)])=dotAcc (decide (k=0)) := by
    simp [dotAcc]
  rw [he]
  refine dotAcc_ok (decide (k=0)) (dotAccum s off k) ?_ ?_ fun t ht e18 e19 => ?_
  · intro hn
    rw [h2.get .v18,h1.get .v18]
    exact h18 (by simpa using hn)
  · intro hn
    rw [h2.get .v19,h1.get .v19]
    exact h19 (by simpa using hn)
  · have hc : VChg [.v16,.v17,.v18,.v19] s t :=
      ((h1.chg.trans h2.chg).trans ht).mono (by
        simp (config := { contextual := true }) only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, implies_true])
    have ev e : accWord (decide (k=0)) (dotAccum s off k e)
        (vword (b.v .v16) e) (vword (b.v .v17) e)=dotAccum s off (k+1) e := by
      rw [h2.get .v16,h1.v,h2.v,h1.chg.mem,h1.chg.gpr]
      change accWord (decide (k=0)) (dotAccum s off k e)
        (dotInput s .x13 off k e) (dotInput s .x14 off k e)=_
      simp only [dotAccum,dotWord_succ,accWord]
      by_cases hk : k=0
      · subst k; simp [dotWord_zero]
      · simp [hk]
    exact next t hc (by simpa only [ev] using e18) (by simpa only [ev] using e19)

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `DotTerms.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized

theorem dotTerms_ok (n : Nat) {s : State} {off : Nat}
    (ho : ∀k<n,(1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v16,.v17,.v18,.v19] s t →
      (n≠0 → t.v .v18=ofVDwords (dotAccum s off n 0) (dotAccum s off n 1)) →
      (n≠0 → t.v .v19=ofVDwords (dotAccum s off n 2) (dotAccum s off n 3)) →
      WP isa (.block rest) t Q) :
    WP isa (.block ((List.range n).flatMap (dotTerm off)++rest)) s Q := by
  induction n generalizing s rest with
  | zero => exact next s (VChg.refl _ _) (by simp) (by simp)
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    refine ih (fun k hk => ho k (by omega_using [hk])) (fun k hk => hr k (by omega_using [hk])) fun a ha e18 e19 => ?_
    have hr' : InRegions (a.rd++a.wr) (a.gpr .x13+BitVec.ofNat 64 (1024*n+off)) 16 ∧
        InRegions (a.rd++a.wr) (a.gpr .x14+BitVec.ofNat 64 (1024*n+off)) 16 := by
      rw [ha.rd,ha.wr,ha.gpr]; exact hr n (by omega_using [])
    refine dotTerm_ok (ho n (by omega_using [])) hr'.1 hr'.2 ?_ ?_ fun t ht a18 a19 => ?_
    · rw [dotAccum_chg ha]; exact e18
    · rw [dotAccum_chg ha]; exact e19
    · refine next t ((ha.trans ht).mono (by simp)) (fun _ => ?_) (fun _ => ?_)
      · simpa only [dotAccum_chg ha] using a18
      · simpa only [dotAccum_chg ha] using a19

theorem dotLoad_ok {n : Nat} (hn : 0<n) {d : VReg} (h30 : d≠.v30) (h31 : d≠.v31)
    {s : State} (hc : ProductConstants s) {off : Nat}
    (ho : ∀k<n,(1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v16,.v17,.v18,.v19,.v20,d] s t → ProductConstants t →
      (∀e<4,vword (t.v d) e=centeredDot (fun k => dotInput s .x13 off k e)
        (fun k => dotInput s .x14 off k e) n) → WP isa (.block rest) t Q) :
    WP isa (.block (dotLoad n d off++rest)) s Q := by
  unfold dotLoad
  rw [List.append_assoc]
  refine dotTerms_ok n ho hr fun a ha e18 e19 => ?_
  have ca := hc.chg ha (by decide) (by decide)
  refine dotReduce_ok h31 (dotAccum s off n) (e18 (by omega_using [hn])) (e19 (by omega_using [hn])) ca.qv ca.qiv
    fun t ht ev => ?_
  have h : VChg [.v16,.v17,.v18,.v19,.v20,d] s t := (ha.trans ht).mono (by
    simp (config := { contextual := true }) only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, true_or, or_true, implies_true, and_self, forall_eq_or_imp])
  exact next t h (hc.chg h (by simp [Ne.symm h30]) (by simp [Ne.symm h31])) ev

end VG.Proof.MlDsa.AArch64.Optimized

end
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized

def dotResult (s : State) (n off e : Nat) : BitVec 32 :=
  centeredDot (fun k => dotInput s .x13 off k e) (fun k => dotInput s .x14 off k e) n

/-- Several direct product loads retain every destination while reusing the
same temporary registers. This is the raw inverse's resident input bank. -/
theorem dotBatch_ok {n : Nat} (hpos : 0<n) (ops : List (VReg × Nat))
    (hn : (ops.map Prod.fst).Nodup)
    (hd : ∀ d off, (d,off)∈ops → d∉productTemps ∧ d≠.v30 ∧ d≠.v31)
    {s : State} (hc : ProductConstants s)
    (hr : ∀ d off, (d,off)∈ops → ∀j<n,(1024*j+off)%16=0 ∧ 1024*j+off<4096*16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*j+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*j+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (productClobs ops) s t → ProductConstants t →
      (∀ d off, (d,off)∈ops → ∀ e<4, vword (t.v d) e=dotResult s n off e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ops.flatMap (fun p => dotLoad n p.1 p.2) ++ rest)) s Q := by
  induction ops generalizing s with
  | nil => exact k s (VChg.refl _ _) hc (by simp)
  | cons op ops ih =>
    rcases op with ⟨d,off⟩
    have hh := hd d off (by simp)
    have rr := hr d off (by simp)
    have nn := List.nodup_cons.mp hn
    simp only [List.flatMap_cons,List.append_assoc]
    refine dotLoad_ok hpos hh.2.1 hh.2.2 hc
      (fun j hj => ⟨(rr j hj).1,(rr j hj).2.1⟩)
      (fun j hj => (rr j hj).2.2) fun a ha ca va => ?_
    refine ih nn.2 (fun d off hm => hd d off (List.mem_cons_of_mem _ hm)) ca ?_ ?_
    · intro d off hm j hj
      rw [ha.rd,ha.wr,ha.gpr]
      exact hr d off (List.mem_cons_of_mem _ hm) j hj
    · intro t ht ct vt
      have hst : VChg (productClobs ((d,off)::ops)) s t := (ha.trans ht).mono (by
        intro r hm
        simp only [productClobs,productTemps,List.map_cons,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only)
      refine k t hst ct ?_
      intro d' off' hm e he
      rcases List.mem_cons.mp hm with h | h
      · cases h
        rw [ht.get d (by
          simp only [productClobs,List.mem_append]
          exact fun h => h.elim hh.1 nn.1),va e he]
        rfl
      · rw [vt d' off' h e he]
        simp only [dotResult,dotInput_chg ha]

end VG.Proof.MlDsa.AArch64.Optimized

end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/DotBankField.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (vword_read16)

def dotBankValues (s : State) (count : Nat) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => ofVWords
    (dotResult s count (16*j.val) 0) (dotResult s count (16*j.val) 1)
    (dotResult s count (16*j.val) 2) (dotResult s count (16*j.val) 3)

theorem dotBankValues_word (s : State) (count : Nat) (j : Fin 8) {e : Nat} (he : e<4) :
    vword (dotBankValues s count)[j.val] e=dotResult s count (16*j.val) e := by
  simp only [dotBankValues,Vector.getElem_ofFn]
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  have h : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega_using [he]
  rcases h with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64

def dotMemoryWord (m : Mem) (a b : Addr) (count off e : Nat) : BitVec 32 :=
  centeredDot (fun k => vword (m.read (a+BitVec.ofNat 64 (1024*k+off)) 16) e)
    (fun k => vword (m.read (b+BitVec.ofNat 64 (1024*k+off)) 16) e) count

def dotMemoryBank (m : Mem) (a b : Addr) (count : Nat) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => ofVWords (dotMemoryWord m a b count (16*j.val) 0)
    (dotMemoryWord m a b count (16*j.val) 1) (dotMemoryWord m a b count (16*j.val) 2)
    (dotMemoryWord m a b count (16*j.val) 3)

theorem dotMemoryBank_eq (s : State) (count : Nat) :
    dotMemoryBank s.mem (s.gpr .x13) (s.gpr .x14) count=dotBankValues s count := rfl

namespace Inverse

def dotPassMem (m : Mem) (p a b : Addr) (count : Nat) : Nat → Mem
  | 0 => m
  | u+1 => let prior := dotPassMem m p a b count u
           writeBank (fiveValues u (dotMemoryBank prior
             (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) count))
             (p+BitVec.ofNat 64 (128*u)) 16 prior

theorem dotPass_frame {m : Mem} {p a b : Addr} {count u : Nat} (hu : u≤8) :
    Frame [⟨p,1024⟩] m (dotPassMem m p a b count u) := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [dotPassMem]
    apply writeBank_frame _ _ _ (r:=⟨p,1024⟩) (by simp) ?_ (ih (by omega_using [hu]))
    intro i
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact VG.Offset.contains_base p (by omega_using [hu]) (by omega_using [hu])

end Inverse
end VG.Proof.MlDsa.AArch64.Optimized

end

end

/-! ### `MlDsa.AArch64.Optimized.DotCore`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.DotFive`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.DotBank`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized

/-- All eight inputs are loaded before any inverse layer starts. Memory and
input pointers are unchanged, and each lane is the original exact product. -/
theorem inverseDotLoads_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) {s : State} (hc : ProductConstants s)
    (hr : ∀ j<8,∀ k<n, InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+16*j)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+16*j)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (productClobs inverseProductOps) s t → ProductConstants t →
      (∀ j<8, ∀ e<4, vword (t.v (Inverse.vr j)) e=dotResult s n (16*j) e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (inverseDotLoads n ++ rest)) s Q := by
  have hnDistinct : (inverseProductOps.map Prod.fst).Nodup := by decide
  have hd d off (hm : (d,off)∈inverseProductOps) :
      d∉productTemps ∧ d≠.v30 ∧ d≠.v31 := by
    obtain ⟨j,hj,h⟩ := List.mem_map.mp hm
    cases h
    exact inverseProduct_safe (List.mem_range.mp hj)
  have hi d off (hm : (d,off)∈inverseProductOps) : ∀ k<n,
      (1024*k+off)%16=0 ∧ 1024*k+off<4096*16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16 := by
    obtain ⟨j,hj,h⟩ := List.mem_map.mp hm
    cases h
    have hj' := List.mem_range.mp hj
    intro k hk
    refine ⟨?_,by omega_using [hn7, hj', hk],hr j hj' k hk⟩
    omega_using []
  have eqcode : inverseProductOps.flatMap (fun p => dotLoad n p.1 p.2)=inverseDotLoads n := by
    simp only [inverseProductOps,inverseDotLoads,List.flatMap_map]
  rw [← eqcode]
  refine dotBatch_ok hn inverseProductOps hnDistinct hd hc hi fun t ht ct vt => k t ht ct ?_
  intro j hj e he
  exact vt _ _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩) e he

end VG.Proof.MlDsa.AArch64.Optimized

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized (inverseDotLoads)

theorem dotFirstArithmetic_eq :
    VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstArithmetic=fiveCode++firstStores := by
  kernel_rfl

theorem dot_initial_regs (j : Fin 8) :
    (regs 0)[j.val]=VG.Impl.MlDsa.AArch64.Optimized.Inverse.vr j.val := by
  decide +revert +kernel

/-- Raw product loads feed the inverse directly in registers. -/
def dotFiveCode (n : Nat) : List Instr := inverseDotLoads n ++ fiveCode ++ firstStores

theorem dotFive_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) (u : Nat) {s : State} {v : Vector (BitVec 128) 8}
    (hv : ∀ j : Fin 8, ∀ e<4, vword v[j.val] e=dotResult s n (16*j.val) e)
    (hc : ProductConstants s)
    (hp : PackedRoots s (packedRoot u)) (hl : TableRoots localOffset (localRoot u) s)
    (hr : ∀ j<8,∀ k<n, InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+16*j)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+16*j)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i.val)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧ VMem mid t
      (writeBank (fiveValues u v) (s.gpr .x0) 16 s.mem)) → WP isa (.block rest) t Q) :
    WP isa (.block (dotFiveCode n ++ rest)) s Q := by
  simp only [dotFiveCode,List.append_assoc]
  refine inverseDotLoads_ok hn hn7 hc hr fun s₁ hc₁ _ hv₁ => ?_
  have hc₁' : VChg runRegs s s₁ := hc₁.mono (by decide)
  have hb : Bank s₁ (regs 0) v := by
    intro i
    apply vec_ext
    intro e he
    have hr := dot_initial_regs i
    rw [hr,hv₁ i.val i.isLt e he,hv i e he]
  refine five_ok u hb (hp.frame (hc₁.mono (by decide))) (hl.frame hc₁' (by decide)) fun s₂ hc₂ hb₂ => ?_
  rw [firstStores_eq]
  refine storeBank_ok (regs 7) 16 .x0 (by intro i; omega_using []) hb₂ ?_ fun t hm => ?_
  · intro i
    simpa only [hc₂.wr,hc₂.gpr,hc₁.wr,hc₁.gpr] using hw i
  · refine k t ⟨s₂,(hc₁'.trans hc₂).mono (by simp),?_⟩
    simpa only [hc₂.mem,hc₂.gpr,hc₁.mem,hc₁.gpr] using hm

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end


/-! ## From `DotLoop.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized (DotInverse.firstAdvance)

def dotLoopRegs : List Reg := [.x0,.x1,.x11,.x13,.x14]

theorem dotAdvance_ok (s : State) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstAdvance) s fun t =>
      ((t.gpr .x0=s.gpr .x0+128 ∧ t.gpr .x1=s.gpr .x1+480 ∧ t.gpr .x11=s.gpr .x11-1 ∧
        t.gpr .x13=s.gpr .x13+128 ∧ t.gpr .x14=s.gpr .x14+128 ∧ t.mem=s.mem) ∧
        Keep dotLoopRegs s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  unfold VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstAdvance
  arun
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dotFirstBlock_eq (count : Nat) :
    VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock count=
      dotFiveCode count++VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstAdvance := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock,dotFirstArithmetic_eq,
    dotFiveCode,List.append_assoc]

/-- The complete first pass, retaining exact input/output cursors. -/
theorem dotLoop_ok {count : Nat} (hn : 0<count) (hn7 : count≤7) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,3904⟩ : Region).Disjoint ⟨s.gpr .x0,1024⟩)
    (hc : s.gpr .x11=8) (hq : ProductConstants s)
    (hrt : ∀off,off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀j<8,∀k<count,
      InRegions (s.rd++s.wr) ((s.gpr .x13+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*k+16*j)) 16 ∧
      InRegions (s.rd++s.wr) ((s.gpr .x14+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*k+16*j)) 16)
    (hw : ∀u<8,∀i : Fin 8,InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16) :
    WP isa (.loop (.block (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock count)) (.nonzero .x .x11)) s fun t =>
      Keep dotLoopRegs s t ∧ ProductConstants t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.gpr .x13=s.gpr .x13+1024 ∧ t.gpr .x14=s.gpr .x14+1024 ∧
      t.mem=dotPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count 8 := by
  rw [dotFirstBlock_eq]
  let I := fun u t => Keep dotLoopRegs s t ∧ ProductConstants t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (480*u) ∧
    t.gpr .x13=s.gpr .x13+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x14=s.gpr .x14+BitVec.ofNat 64 (128*u) ∧
    t.mem=dotPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N:=8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t hi _
    rcases hi with ⟨hk,hqt,hp0,hp1,hp13,hp14,hm⟩
    have ht' : InverseTable.Words t.mem (s.gpr .x1) := by
      rw [hm]
      exact tableWords_frame ht (dotPass_frame (by omega_arith)) (by
        intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hd)
    have hrt' : ∀off,off+16≤3904 → InRegions (t.rd++t.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
      simpa only [hk.rd,hk.wr] using hrt
    have hqv : ∀e<4,vword (t.v .v31) e=8380417#32 := by
      intro e he; rw [hqt.qv,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
      rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_arith) with rfl | rfl | rfl | rfl <;> rfl
    refine dotFive_ok hn hn7 u (v:=dotBankValues t count) (fun j e he => dotBankValues_word t count j he)
      hqt (packed_tableRoots hu ht' hrt' hp1 hqv) (local_tableRoots hu ht' hrt' hp1 hqv)
      ?_ ?_ fun t₁ ⟨v,hv,hv₁⟩ => ?_
    · intro j hj k hkc; simpa only [hk.rd,hk.wr,hp13,hp14] using hr u hu j hj k hkc
    · intro i; simpa only [hk.wr,hp0] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hv.keep.trans hv₁.keep).mono
      refine WP.mono (dotAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hp₃,hc₂,hp₁₃,hp₁₄,hm₂⟩,hk₂⟩,hvec₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_,?_,?_,?_⟩,?_⟩
      · constructor
        · rw [hvec₂,hv₁.v,hv.get .v31 (by decide)]; exact hqt.qv
        · rw [hvec₂,hv₁.v,hv.get .v30 (by decide)]; exact hqt.qiv
      · rw [hp₂,hk₁.get .x0,hp0]
        rw [show 128*(u+1)=128*u+128 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₃,hk₁.get .x1,hp1]
        rw [show 480*(u+1)=480*u+480 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₁₃,hk₁.get .x13,hp13]
        rw [show 128*(u+1)=128*u+128 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₁₄,hk₁.get .x14,hp14]
        rw [show 128*(u+1)=128*u+128 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hm₂,hv₁.mem,← dotMemoryBank_eq]
        simp only [hm,hp0,hp13,hp14,dotPassMem]
      · rw [hc₂,hk₁.get .x11]; rfl
  · exact ⟨Keep.refl _ _,hq,by simp,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep wp_vop wp_scalar)

def dotInitRegs : List Reg := [.x3,.x4,.x5,.x6,.x7,.x9,.x10,.x11]

theorem dotSetup_ok (s : State) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Optimized.DotInverse.setup) s fun t =>
      Keep dotInitRegs s t ∧ t.mem=s.mem ∧ t.gpr .x11=8 ∧ ProductConstants t := by
  change WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.movW .x10 4236238847 ++
    Instr.vop (.dup .s4 .v30 .x10)::
      (VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v31 8380417++firstSetup))) s _
  refine wp_scalar (by rfl) (VG.Proof.MlDsa.AArch64.Arith.movW_ok .x10 _ s)
    fun a ⟨⟨ha,hm⟩,hk⟩ hv => ?_
  refine wp_vop (d:=.v30) rfl fun b hb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok b .v31 8380417) fun c hc => ?_
  refine WP.mono (firstSetup_ok c) fun t ⟨⟨⟨h11,htm⟩,htk⟩,htv⟩ => ?_
  refine ⟨(((hk.trans hb.chg.keep).trans (constKeep_keep hc.1 (by decide))).trans htk).mono,
    htm.trans (hc.1.mem.trans (hb.mem.trans hm)),h11,?_,?_⟩
  · rw [htv,hc.2]; rfl
  · rw [htv,hc.1.vec .v30 (by decide),hb.v,ha]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def dotCoreRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x9,.x10,.x11,.x12,.x13,.x14]

def dotInverseMem (m : Mem) (p a b : Addr) (count : Nat) : Mem :=
  finalPassMem (dotPassMem m p a b count 8) p (HighPack.repeatedWord 8380417) 8

theorem dotCore_eq (count : Nat) : VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core count=
    .seq (.block VG.Impl.MlDsa.AArch64.Optimized.DotInverse.setup) (.seq
      (.loop (.block (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock count)) (.nonzero .x .x11))
      (.seq (.block middleCode) (.loop (.block (finalSliceCode++finalAdvance)) (.nonzero .x .x12)))) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core
  rw [finalBody_eq]
  rfl

/-- The standalone inverse executes the selected two-pass memory transform.
Only table and buffer accessibility are required at this machine boundary. -/
theorem dotCore_ok {count : Nat} (hn : 0<count) (hn7 : count≤7) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,3904⟩ : Region).Disjoint ⟨s.gpr .x0,1024⟩)
    (hrt : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hra : ∀ off, off+16≤1024*count → InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 off) 16)
    (hrb : ∀ off, off+16≤1024*count → InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16)
    (hr : ∀ off, off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hw : ∀ off, off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core count) s fun t =>
      Keep dotCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧ t.mem=dotInverseMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count := by
  rw [dotCore_eq]
  apply WP.seq
  refine WP.mono (dotSetup_ok s) fun a ⟨hka,hma,h11,hqa⟩ => ?_
  have ha0 : a.gpr .x0=s.gpr .x0 := hka.get .x0 (by decide)
  have ha1 : a.gpr .x1=s.gpr .x1 := hka.get .x1 (by decide)
  have ha13 : a.gpr .x13=s.gpr .x13 := hka.get .x13 (by decide)
  have ha14 : a.gpr .x14=s.gpr .x14 := hka.get .x14 (by decide)
  apply WP.seq
  refine WP.mono (dotLoop_ok hn hn7 (s := a) ?_ ?_ h11 hqa ?_ ?_ ?_) fun b ⟨hkb,hqb,hb0,hb1,_,_,hmb⟩ => ?_
  · simpa only [hma,ha1] using ht
  · simpa only [ha0,ha1] using hd
  · simpa only [hka.rd,hka.wr,ha1] using hrt
  · intro u hu j hj k hk
    simp only [hka.rd,hka.wr,ha13,ha14,BitVec.add_assoc,← BitVec.ofNat_add]
    exact ⟨hra _ (by omega_arith),hrb _ (by omega_arith)⟩
  · intro u hu i
    simp only [hka.wr,ha0,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hw _ (by omega_arith)
  · have hb0' : b.gpr .x0=s.gpr .x0+1024 := by simpa only [ha0] using hb0
    have hb1' : b.gpr .x1=s.gpr .x1+3840 := by simpa only [ha1] using hb1
    have hmb' : b.mem=dotPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count 8 := by simpa only [hma,ha0,ha13,ha14] using hmb
    have htb : InverseTable.Words b.mem (s.gpr .x1) := by
      rw [hmb']
      exact tableWords_frame ht (dotPass_frame (by decide)) (by
        intro r hr
        have he := List.mem_singleton.mp hr
        subst r
        exact hd)
    have hqbLane : ∀e<4,vword (b.v .v31) e=8380417#32 := by
      intro e he
      rw [hqb.qv]
      exact HighPack.repeatedWord_lane _ he
    apply WP.seq
    refine WP.mono (middle_ok (s := b) htb hb1' ?_ hqbLane) fun c ⟨hkc,hmc,hc0,hc2,hc12,hfc,hsc⟩ => ?_
    · intro off hoff
      simp only [hkb.rd,hkb.wr,hka.rd,hka.wr,hb1']
      change InRegions (s.rd++s.wr) ((s.gpr .x1+BitVec.ofNat 64 3840)+BitVec.ofNat 64 off) 16
      rw [BitVec.add_assoc,← BitVec.ofNat_add]
      apply hrt
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
      omega_arith
    · have hc0' : c.gpr .x0=s.gpr .x0 := by rw [hc0,hb0']; bv_omega
      have hc2' : c.gpr .x2=s.gpr .x0 := by rw [hc2,hb0']; bv_omega
      have hqv : c.v .v31=HighPack.repeatedWord 8380417 := (by apply VG.AArch64.vec_ext; intro e he; rw [hfc.q e he,HighPack.repeatedWord_lane _ he])
      refine WP.mono (finalLoop_ok hfc hsc hc12 ?_ ?_) fun t ⟨hkt,_,_,hmt⟩ => ?_
      · intro u hu i
        simp only [hkc.rd,hkc.wr,hkb.rd,hkb.wr,hka.rd,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hr _ (by omega_arith)
      · intro u hu i
        simp only [hkc.wr,hkb.wr,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hw _ (by omega_arith)
      · refine ⟨(((hka.trans hkb).trans hkc).trans hkt).mono,?_,?_⟩
        · rw [hkt.get .x0 (by decide),hc0']
        · simpa only [dotInverseMem,hmc,hmb',hc2',hqv] using hmt

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end

/-! ### `MlDsa.AArch64.Optimized.DotMemoryValues`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (vword_read16)

theorem dotMemoryBank_word (m : Mem) (a b : Addr) (count : Nat) (j : Fin 8) {e : Nat} (he : e<4) :
    vword (dotMemoryBank m a b count)[j.val] e=dotMemoryWord m a b count (16*j.val) e := by
  simp only [dotMemoryBank,Vector.getElem_ofFn]
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_using [he]) with rfl | rfl | rfl | rfl <;> rfl

theorem dotMemoryWord_offset (m : Mem) (a b : Addr) (count u j e : Nat) (he : e<4) :
    dotMemoryWord m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) count (16*j) e=
      centeredDot (fun k => coeffAt m (a+BitVec.ofNat 64 (1024*k)) (32*u+4*j+e))
        (fun k => coeffAt m (b+BitVec.ofNat 64 (1024*k)) (32*u+4*j+e)) count := by
  unfold dotMemoryWord
  congr 1 <;> funext k <;>
    rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he] <;>
    simp only [coeffAt,BitVec.add_assoc,← BitVec.ofNat_add] <;> congr 3 <;> omega_using []

theorem dotPass_bank_original {m : Mem} {p a b : Addr} {count u : Nat} (hu : u<8)
    (ha : ∀k<count,(polyRegion (a+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p))
    (hb : ∀k<count,(polyRegion (b+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p)) :
    dotMemoryBank (dotPassMem m p a b count u) (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) count=
    dotMemoryBank m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) count := by
  apply Vector.ext
  intro i hi
  apply vec_ext
  intro e he
  rw [dotMemoryBank_word _ _ _ _ ⟨i,hi⟩ he,dotMemoryBank_word _ _ _ _ ⟨i,hi⟩ he,
    dotMemoryWord_offset _ _ _ _ _ _ _ he,dotMemoryWord_offset _ _ _ _ _ _ _ he]
  apply centeredDot_congr
  · intro k hk
    exact coeffAt_frame (dotPass_frame (by omega_using [hu])) (by
      intro r hr; have hr' := List.mem_singleton.mp hr; subst r; exact ha k hk)
      (by change 32*u+4*i+e<256; omega_using [hu, hi, he])
  · intro k hk
    exact coeffAt_frame (dotPass_frame (by omega_using [hu])) (by
      intro r hr; have hr' := List.mem_singleton.mp hr; subst r; exact hb k hk)
      (by change 32*u+4*i+e<256; omega_using [hu, hi, he])

def dotMemStep (m : Mem) (p a b : Addr) (count u : Nat) : Mem :=
  writeBank (fiveValues u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
    (b+BitVec.ofNat 64 (128*u)) count)) (coeffAddr p (32*u)) 16 m

theorem dotPassMem_step (m : Mem) (p a b : Addr) (count u : Nat) :
    dotPassMem m p a b count (u+1)=dotMemStep (dotPassMem m p a b count u) p a b count u := by
  simp only [dotPassMem,dotMemStep,coeffAddr,show 4*(32*u)=128*u by omega_using []]

theorem dotMemStep_at (m : Mem) (p a b : Addr) (count : Nat) {u : Nat} (hu : u<8)
    (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (dotMemStep m p a b count u) p (32*u+4*i.val+e)=
      vword (fiveValues u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
        (b+BitVec.ofNat 64 (128*u)) count))[i.val] e := by
  exact writeBank_coeff_at _ m p (start:=32*u) (step:=4) (by decide) (by omega_using [hu]) i he

theorem dotMemStep_outside (m : Mem) (p a b : Addr) (count : Nat) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k<32*u ∨ 32*(u+1)≤k) :
    coeffAt (dotMemStep m p a b count u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start:=32*u) (step:=4) _ m p (by omega_using [hu]) hk
  intro i; omega_using [hout]

theorem dotPass_processed {m : Mem} {p a b : Addr} {count u k : Nat}
    (ha : ∀j<count,(polyRegion (a+BitVec.ofNat 64 (1024*j))).Disjoint (polyRegion p))
    (hb : ∀j<count,(polyRegion (b+BitVec.ofNat 64 (1024*j))).Disjoint (polyRegion p))
    (hu : u≤8) (hk : k<n) (hp : k/32<u) :
    coeffAt (dotPassMem m p a b count u) p k=
      vword (fiveValues (k/32) (dotMemoryBank m (a+BitVec.ofNat 64 (128*(k/32)))
        (b+BitVec.ofNat 64 (128*(k/32))) count))[(k%32)/4]! (k%4) := by
  induction u with
  | zero => omega
  | succ u ih =>
    rw [dotPassMem_step]
    by_cases he : k/32=u
    · have hi : (k%32)/4<8 := by omega_using []
      have hidx : 32*u+4*((k%32)/4)+k%4=k := by omega_using [he]
      have hx := dotMemStep_at (dotPassMem m p a b count u) p a b count (by omega_using [hu] : u<8)
        ⟨(k%32)/4,hi⟩ (e:=k%4) (by omega_using [])
      rw [hidx,dotPass_bank_original (by omega_using [hu]) ha hb] at hx
      simpa only [he,
        getElem!_pos (fiveValues u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
          (b+BitVec.ofNat 64 (128*u)) count)) ((k%32)/4) hi] using hx
    · rw [dotMemStep_outside _ _ _ _ _ (by omega_using [hu]) hk (by omega_using [he])]
      exact ih (by omega_using [hu]) (by omega_using [hp, he])

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end


/-! ## From `DotStatic.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlKem.AArch64 (mov)

def dotFamilyRegion (p : Addr) (count : Nat) : Region := ⟨p,1024*count⟩

theorem dotInverseMem_frame (m : Mem) (p a b : Addr) (count : Nat) :
    Frame [outputRegion p] m (dotInverseMem m p a b count) :=
  (dotPass_frame (m:=m) (p:=p) (a:=a) (b:=b) (count:=count) (by decide)).trans
    (finalPass_frame (by decide))

theorem dotCore_words_ok {count : Nat} (hn : 0<count) (hn7 : count≤7) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (htr : tableRegion (s.gpr .x1)∈s.rd++s.wr)
    (ha : dotFamilyRegion (s.gpr .x13) count∈s.rd++s.wr)
    (hb : dotFamilyRegion (s.gpr .x14) count∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core count) s fun t =>
      Keep dotCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=dotInverseMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count := by
  refine WP.mono (dotCore_ok hn hn7 ht hsep ?_ ?_ ?_ ?_ ?_) fun t ⟨hk,hp,hm⟩ => ?_
  · intro off ho; exact ⟨_,htr,VG.Offset.contains_base _ ho (by omega_arith)⟩
  · intro off ho; exact ⟨_,ha,VG.Offset.contains_base _ ho (by omega_arith)⟩
  · intro off ho; exact ⟨_,hb,VG.Offset.contains_base _ ho (by omega_arith)⟩
  · intro off ho; exact ⟨_,List.mem_append_right _ hw,VG.Offset.contains_base _ ho (by omega_arith)⟩
  · intro off ho; exact ⟨_,hw,VG.Offset.contains_base _ ho (by omega_arith)⟩
  · exact ⟨hk,hp,by rw [hm]; exact dotInverseMem_frame _ _ _ _ _,hm⟩

theorem dotStaticInit_ok (s : State) :
    WP isa (.block [mov .x13 .x1,mov .x14 .x2,.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) s fun t =>
      (t.gpr .x1=s.syms "VG_MLDSA_INV_FOLDED" ∧ t.gpr .x13=s.gpr .x1 ∧
        t.gpr .x14=s.gpr .x2 ∧ t.mem=s.mem) ∧ Keep [.x1,.x13,.x14] s t := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  unfold mov
  arun [exec_adrSym]
  rfl

/-- Exact selected dot4/5/7 inverse machine endpoint. The unused scratch
argument remains untouched; writes are confined to the output polynomial. -/
theorem dotStaticCode_words_ok {count : Nat} (hn : 0<count) (hn7 : count≤7) {s : State}
    (ht : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED"))
    (htr : tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr)
    (ha : dotFamilyRegion (s.gpr .x1) count∈s.rd++s.wr)
    (hb : dotFamilyRegion (s.gpr .x2) count∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode count) s fun t =>
      Keep dotCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=dotInverseMem s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) count := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode
  refine WP.seq (WP.mono (dotStaticInit_ok s) fun a ⟨⟨hp1,hp13,hp14,hm⟩,hk⟩ => ?_)
  have ht' : InverseTable.Words a.mem (a.gpr .x1) := by simpa only [hp1,hm] using ht.words
  refine WP.mono (dotCore_words_ok hn hn7 ht' ?_ ?_ ?_ ?_ ?_) fun t ⟨hkt,hpt,hft,hmt⟩ => ?_
  · simpa only [hp1,hk.rd,hk.wr] using htr
  · simpa only [hp13,hk.rd,hk.wr] using ha
  · simpa only [hp14,hk.rd,hk.wr] using hb
  · simpa only [hk.get .x0 (by decide),hk.wr] using hw
  · simpa only [hp1,hk.get .x0 (by decide)] using hsep
  · exact ⟨(hk.trans hkt).mono,hpt.trans (hk.get .x0 (by decide)),
      by simpa only [hm,hk.get .x0 (by decide)] using hft,
      by simpa only [hm,hp13,hp14,hk.get .x0 (by decide)] using hmt⟩

theorem dotCoreKeep_abi {s t : State} (h : Keep dotCoreRegs s t) : abiPreserved s t := by
  refine ⟨?_,h.sp,h.vcs⟩
  intro r hr
  apply h.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `FusedRepresentation.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem positiveReduced_iff {m : Mem} {p : Addr} :
    PositiveReduced m p ↔ PosPolyIs m p (polyAt m p) :=
  ⟨fun h => ⟨h,rfl⟩,fun h => h.bound⟩

/-- The inverse cancels the internal Montgomery factor for a whole matrix row. -/
theorem inverse_dotNTT (f g : Nat → Poly) (count : Nat) :
    montgomeryNttInv (Representation.encode true (dotPoly f g count))=
      nttInv (dotNTT f g count) :=
  Representation.inverse_encode true _

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `DotMemoryField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem dotMemoryBank_bound {m : Mem} {a b : Addr} {f g : Nat → Poly} {u count : Nat}
    (hu : u<8) (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k)) :
    BankBound (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) count) 8380417 := by
  intro j e he
  rw [dotMemoryBank_word _ _ _ _ j he,dotMemoryWord_offset _ _ _ _ _ _ _ he]
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega_arith
  have hbnd := centeredDot_bound _ _ hc
    (fun k hkc => (hf k hkc).bound _ hk) (fun k hkc => (hg k hkc).bound _ hk)
  exact ⟨hbnd.1,Int.le_of_lt hbnd.2⟩

theorem dotMemoryBank_field {m : Mem} {a b : Addr} {f g : Nat → Poly} {u count : Nat}
    (hu : u<8) (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k)) :
    InnerBankField u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) count) (Representation.encode true (dotPoly f g count)) := by
  intro j e he
  rw [dotMemoryBank_word _ _ _ _ j he,dotMemoryWord_offset _ _ _ _ _ _ _ he]
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega_arith
  refine centeredDot_field _ _ f g hc (fun k hkc => (hf k hkc).bound _ hk)
    (fun k hkc => (hg k hkc).bound _ hk) hk ?_ ?_
  · intro k hkc; rw [ofInt_nat_eq,← polyAt_get _ _ hk,(hf k hkc).value]; rfl
  · intro k hkc; rw [ofInt_nat_eq,← polyAt_get _ _ hk,(hg k hkc).value]; rfl

theorem dotPass_field {m : Mem} {p a b : Addr} {f g : Nat → Poly} {count : Nat}
    (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k))
    (ha : ∀k<count,(polyRegion (a+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p))
    (hb : ∀k<count,(polyRegion (b+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p)) :
    SignedPolyIs (dotPassMem m p a b count 8) p
      (InverseTraversal.run InverseTraversal.localSchedule (Representation.encode true (dotPoly f g count)))
      (-268173344) 268173344 := by
  have bank (u : Nat) (hu : u<8) := fiveValues_field _ _ hu
    (dotMemoryBank_bound hu hc hf hg) (dotMemoryBank_field hu hc hf hg)
  have hout (k : Nat) (hk : k<n) :
      -268173344≤(coeffAt (dotPassMem m p a b count 8) p k).toInt ∧
      (coeffAt (dotPassMem m p a b count 8) p k).toInt≤268173344 ∧
      ofInt (coeffAt (dotPassMem m p a b count 8) p k).toInt=
        (InverseTraversal.run InverseTraversal.localSchedule (Representation.encode true (dotPoly f g count)))[k]! := by
    have hu : k/32<8 := by change k<256 at hk; omega_arith
    have hi : (k%32)/4<8 := by omega_arith
    have he : k%4<4 := by omega_arith
    rw [dotPass_processed ha hb (by decide) hk hu,
      getElem!_pos (fiveValues (k/32) (dotMemoryBank m (a+BitVec.ofNat 64 (128*(k/32)))
        (b+BitVec.ofNat 64 (128*(k/32))) count)) ((k%32)/4) hi]
    have hbank := bank (k/32) hu
    refine ⟨(hbank.1 ⟨(k%32)/4,hi⟩ _ he).1,(hbank.1 ⟨(k%32)/4,hi⟩ _ he).2,?_⟩
    have hv := hbank.2 ⟨(k%32)/4,hi⟩ _ he
    have hidx : 32*(k/32)+4*((k%32)/4)+k%4=k := by omega_arith
    simp only [Traversal.innerLoc] at hv
    rw [hidx] at hv
    have hcoord := InverseTraversal.prefix_selected InverseTraversal.localSlice (fun k => k/32) 8
      (fun u hu => InverseTraversal.local_supported ⟨u,hu⟩)
      (Representation.encode true (dotPoly f g count)) hk hu
    exact hv.trans hcoord.symm
  exact ⟨fun k hk => ⟨(hout k hk).1,(hout k hk).2.1⟩,fun k hk => (hout k hk).2.2⟩

theorem dotInverseMem_field {m : Mem} {p a b : Addr} {f g : Nat → Poly} {count : Nat}
    (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k))
    (ha : ∀k<count,(polyRegion (a+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p))
    (hb : ∀k<count,(polyRegion (b+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p)) :
    PolyIs (dotInverseMem m p a b count) p (nttInv (dotNTT f g count)) := by
  have hp := finalPass_field (dotPass_field hc hf hg ha hb) (qv:=HighPack.repeatedWord 8380417)
    (fun e he => HighPack.repeatedWord_lane _ he)
  simpa only [dotInverseMem,InverseTraversal.traversal_montgomery,inverse_dotNTT] using hp

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def dotK (count : Nat) : Contract isa where
  pre s := tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr ∧
    dotFamilyRegion (s.gpr .x1) count∈s.rd++s.wr ∧ dotFamilyRegion (s.gpr .x2) count∈s.rd++s.wr ∧
    outputRegion (s.gpr .x0)∈s.wr ∧
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    (dotFamilyRegion (s.gpr .x1) count).Disjoint (outputRegion (s.gpr .x0)) ∧
    (dotFamilyRegion (s.gpr .x2) count).Disjoint (outputRegion (s.gpr .x0)) ∧
    InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED") ∧
    (∀j<count,PositiveReduced s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j))) ∧
    (∀j<count,PositiveReduced s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j)))
  post s t := PolyIs t.mem (s.gpr .x0) (nttInv (dotNTT
    (fun j => polyAt s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j)))
    (fun j => polyAt s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j))) count))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x2=t.gpr .x2 ∧
    s.sp=t.sp ∧ s.syms "VG_MLDSA_INV_FOLDED"=t.syms "VG_MLDSA_INV_FOLDED"

theorem dot_pre {count : Nat} {s : State}
    (h : (dotInverseContract count (abi.withConsts inverseConsts)).pre s) : (dotK count).pre s := by
  sig_pre [dotInverseContract,dotInverseSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,_,ht,hw,rest⟩ := h
  have hrd : s.rd=[dotFamilyRegion (s.gpr .x1) count,dotFamilyRegion (s.gpr .x2) count,
      tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    have he : count*256*4=1024*count := by omega_arith
    rw [he]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hrd]; simp,by rw [hrd]; simp,
    by rw [hw]; simp [outputRegion],?_,?_,?_,?_,?_,?_⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · have hh : (outputRegion (s.gpr .x0)).Disjoint (dotFamilyRegion (s.gpr .x1) count) := by
      dsimp only [outputRegion,dotFamilyRegion]; grind only
    exact hh.symm
  · have hh : (outputRegion (s.gpr .x0)).Disjoint (dotFamilyRegion (s.gpr .x2) count) := by
      dsimp only [outputRegion,dotFamilyRegion]; grind only
    exact hh.symm
  · intro i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (held i hi).trans (eq _ _ (by rw [InverseTable.expandedWords_length]; exact hi))
  · grind only
  · grind only

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end

/-! ### `MlDsa.AArch64.Optimized.DotVerified`, which only this module used -/

section

/-! ## From `DotCorrect.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.DotInverse

theorem dot_correct {count : Nat} (hn : 0<count) (hn7 : count≤7) (s : State) (hp : (dotK count).pre s) :
    ∃trace t,Exec isa (staticCode count) s trace t ∧ abiPreserved s t ∧ (dotK count).post s t := by
  obtain ⟨htr,ha,hb,hw,hsep,hoa,hob,ht,hfa,hfb⟩ := hp
  obtain ⟨tr,t,he,hk,_,_,hm⟩ := dotStaticCode_words_ok hn hn7 ht htr ha hb hw hsep
  have hv := dotInverseMem_field hn7
    (fun j hj => positiveReduced_iff.mp (hfa j hj)) (fun j hj => positiveReduced_iff.mp (hfb j hj))
    (fun j hj => hoa.sub_left (VG.Offset.sub_base _ (by omega_arith)))
    (fun j hj => hob.sub_left (VG.Offset.sub_base _ (by omega_arith)))
  rw [← hm] at hv
  exact ⟨tr,t,he,dotCoreKeep_abi hk,hv⟩

theorem dot_ct {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7) :
    ConstantTime isa (dotK count).pre (dotK count).pub (staticCode count) := by
  have ct : ConstantTime isa (fun _ => True)
      (Taint.AgreeS ["VG_MLDSA_INV_FOLDED"] (Taint.ofRegs [.x0,.x1,.x2])) (staticCode count) := by
    rcases hc with rfl | rfl | rfl
    · exact dot4Inverse_ct
    · exact dot5Inverse_ct
    · exact dot7Inverse_ct
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.2.2.1 ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2.1
  · intro name hn
    have he : name="VG_MLDSA_INV_FOLDED" := by simpa only [List.mem_singleton] using hn
    subst name; exact hp.2.2.2.2

theorem dot_pub {count : Nat} {s t : State}
    (h : (dotInverseContract count (abi.withConsts VG.Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts)).pub s t) :
    (dotK count).pub s t := by
  sig_pub [dotInverseContract,dotInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at h
  exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.1,h.2.1⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def dotSat (count : Nat) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 16384 else if r=.x2 then 32768 else if r=.x3 then 8192 else 0
  sp := 131072
  syms _ := 65536
  mem := constMem 65536 expandedWords
  rd := [⟨16384,1024*count⟩,⟨32768,1024*count⟩,⟨65536,3904⟩]
  wr := [⟨4096,1024⟩,⟨8192,1024⟩]

theorem dotSat_held (count : Nat) : ∀i<488,
    (dotSat count).mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0 := inverseSat_held

theorem dotSat_reduced (count : Nat) (p : Addr) (hp : p.toNat+1024≤65536) : Reduced (dotSat count).mem p := by
  intro i hi
  simp only [dotSat,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v:=(0#32)) ?_]
  · decide
  · intro j hj
    have ha : ¬ ((p+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*expandedWords.length := by
      rw [InverseTable.expandedWords_length]
      have hi' : i<256 := hi
      simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,
        show (65536:BitVec 64).toNat=65536 by decide]
      omega_arith
    simp only [constMem,ha,ite_false]
    simp

theorem dot_spec_pre {count : Nat} {s : State} (hc : count≤7)
    (hg0 : s.gpr .x0=4096) (hg1 : s.gpr .x1=16384) (hg2 : s.gpr .x2=32768)
    (hg3 : s.gpr .x3=8192) (hsym : s.syms "VG_MLDSA_INV_FOLDED"=65536)
    (hrd : s.rd=[⟨16384,1024*count⟩,⟨32768,1024*count⟩,⟨65536,3904⟩])
    (hwr : s.wr=[⟨4096,1024⟩,⟨8192,1024⟩])
    (held : ∀i<488,s.mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (ha : ∀j<count,PositiveReduced s.mem (16384+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<count,PositiveReduced s.mem (32768+BitVec.ofNat 64 (1024*j))) :
    (dotInverseContract count (abi.withConsts inverseConsts)).pre s := by
  sig_pre [dotInverseContract,dotInverseSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  rw [hg0,hg1,hg2,hg3,hsym,hrd,hwr]
  have he : count*256*4=1024*count := by omega_arith
  rw [he]
  refine ⟨rfl,held,by decide,?_,by decide,rfl,rfl,?_,?_,?_,?_,?_,by decide,?_,?_,by decide,ha,hb⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega_arith)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega_arith)
  · exact Region.disjoint_of_sep (by decide)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega_arith)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega_arith)
  · simp; omega_arith
  · simp; omega_arith

theorem dot_sat (count : Nat) (hc : count≤7) :
    (dotInverseContract count (abi.withConsts inverseConsts)).pre (dotSat count) := by
  apply dot_spec_pre hc rfl rfl rfl rfl rfl rfl rfl (dotSat_held count)
  · intro j hj i hi
    have hr := dotSat_reduced count (16384+BitVec.ofNat 64 (1024*j)) (by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat, show (16384:Addr).toNat=16384 by decide]; omega_arith) i hi
    change _<3*8380417
    change _<8380417 at hr
    omega_arith
  · intro j hj i hi
    have hr := dotSat_reduced count (32768+BitVec.ofNat 64 (1024*j)) (by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat, show (32768:Addr).toNat=32768 by decide]; omega_arith) i hi
    change _<3*8380417
    change _<8380417 at hr
    omega_arith

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.DotInverse
open VG.Impl.MlDsa.AArch64.Optimized.Inverse (inverseConsts)

/-- The selected fused dot/inverse kernels have canonical output and positive-lazy inputs. -/
theorem dot_verified {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7) :
    Verified target (staticCode count) (dotInverseContract count (abi.withConsts inverseConsts)) := by
  refine Verified.of_correct (dot_correct (by omega_arith) (by omega_arith)) (dot_ct hc)
    { pre := fun _ h => dot_pre h, post := ?_, pub := ?_, sat := ⟨dotSat count,dot_sat count (by omega_arith)⟩ }
  · intro s t _ h
    sig_post [dotInverseContract,dotInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq]
    exact h
  · intro s t _ _ h
    exact dot_pub h

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end


/-! ## From `DotCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.DotInverse
open VG.Impl.MlDsa.AArch64.Optimized.Inverse (inverseConsts expandedWords)

theorem dot_callee (S : Nat) {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7) :
    CalleeOk S (staticCode count) (dotInverseContract count (abi.withConsts inverseConsts)) := by
  refine CalleeOk.of_ct (dot_verified hc).1 (dot_verified hc).2.1 (by rcases hc with rfl|rfl|rfl <;> lit_decide) (fun _ _ h => h) ?_
  change 0≤S
  exact Nat.zero_le _

abbrev dotArgs (out a b scratch : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b),(.x3,.ptr scratch)]

structure DotCallReady (count : Nat) (out a b scratch : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  aFit : (pa s a).toNat+1024*count≤2^64
  bFit : (pa s b).toNat+1024*count≤2^64
  scratchFit : (pa s scratch).toNat+1024≤2^64
  held : ∀i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64
  tableApart : ∀r∈[outputRegion (pa s out),outputRegion (pa s scratch)],
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint r
  outA : (outputRegion (pa s out)).Disjoint (dotFamilyRegion (pa s a) count)
  outB : (outputRegion (pa s out)).Disjoint (dotFamilyRegion (pa s b) count)
  outScratch : (outputRegion (pa s out)).Disjoint (outputRegion (pa s scratch))
  aScratch : (dotFamilyRegion (pa s a) count).Disjoint (outputRegion (pa s scratch))
  bScratch : (dotFamilyRegion (pa s b) count).Disjoint (outputRegion (pa s scratch))
  positiveA : ∀j<count,PositiveReduced s.mem (pa s a+BitVec.ofNat 64 (1024*j))
  positiveB : ∀j<count,PositiveReduced s.mem (pa s b+BitVec.ofNat 64 (1024*j))
  readable : Covers ([dotFamilyRegion (pa s a) count,dotFamilyRegion (pa s b) count,
    tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]++[outputRegion (pa s out),outputRegion (pa s scratch)]) (s.rd++s.wr)
  writable : Covers [outputRegion (pa s out),outputRegion (pa s scratch)] s.wr
  tableAligned : (s.syms "VG_MLDSA_INV_FOLDED").toNat%64=0

theorem dotAt_pre {s s1 : State} {count : Nat} {out a b scratch : Ptr}
    (h : DotCallReady count out a b scratch s) (h1 : Args (dotArgs out a b scratch) s s1)
    (hy : s1.syms=s.syms) :
    (dotInverseContract count (abi.withConsts inverseConsts)).pre
      (s1.callEntry.withRegions [dotFamilyRegion (pa s a) count,dotFamilyRegion (pa s b) count,
        tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]
        [outputRegion (pa s out),outputRegion (pa s scratch)]) := by
  sig_pre [dotInverseContract,dotInverseSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,
    Args.mem h1,Arg.val]
  have he : count*256*4=1024*count := by omega_using []
  rw [he]
  exact ⟨rfl,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),h.tableAligned,rfl,rfl,h.outA,h.outB,h.outScratch,h.aScratch,
    h.bScratch,h.outFit,h.aFit,h.bFit,h.scratchFit,h.positiveA,h.positiveB⟩

theorem dotArgs_ok {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok) :
    ∀x∈dotArgs out a b scratch,x.2.Ok ∧ x.1∈argRegs := by
  simp only [dotArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩
  · exact ⟨hs,by simp⟩

theorem dotAt_ok {S : Nat} (hS : S<2^64) {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7)
    {nm : String} {s : State} {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok)
    (h : DotCallReady count out a b scratch s) :
    WP isa (callAt nm (staticCode count) (dotArgs out a b scratch)) s fun t =>
      Post S s t [outputRegion (pa s out),outputRegion (pa s scratch)] ∧
      PolyIs t.mem (pa s out) (nttInv (dotNTT
        (fun j => polyAt s.mem (pa s a+BitVec.ofNat 64 (1024*j)))
        (fun j => polyAt s.mem (pa s b+BitVec.ofNat 64 (1024*j))) count)) := by
  refine WP.mono (callAtSyms_ok hS (dot_callee S hc) (dotArgs_ok ho ha hb hs) (by simp)
    (fun s1 h1 hy => dotAt_pre h h1 hy) h.readable h.writable)
    fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [dotInverseContract,dotInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.DotInverse

/-- Dot-product coefficient values remain secret across the complete call. -/
theorem dotAt_tr {S : Nat} {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7)
    {nm : String} {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → DotCallReady count out a b scratch x ∧ DotCallReady count out a b scratch y ∧
      pa x out=pa y out ∧ pa x a=pa y a ∧ pa x b=pa y b ∧ pa x scratch=pa y scratch ∧
      x.sp=y.sp ∧ x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED") :
    RelCT isa Q (callAt nm (staticCode count) (dotArgs out a b scratch)) fun _ _ => True := by
  refine callAtSyms_tr (dot_callee S hc) (dotArgs_ok ho ha hb hs) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,eo,ea,eb,es,esp,et⟩ := hQ x y hp
  refine ⟨[dotFamilyRegion (pa x a) count,dotFamilyRegion (pa x b) count,
    tableRegion (x.syms "VG_MLDSA_INV_FOLDED")],[outputRegion (pa x out),outputRegion (pa x scratch)],
    dotAt_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ea,eb,es,et]
    exact dotAt_pre ry h2 hy2
  · sig_pub [dotInverseContract,dotInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq]
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.r3 h1,Args.r3 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,et,eo,ea,eb,es⟩
  · rw [eo,ea,eb,es,et]; exact ry.readable
  · rw [eo,es]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
