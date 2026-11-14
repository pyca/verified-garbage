module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBatch
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductLoad
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Dot
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotWord
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Word
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd

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
