module

import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductLoad
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStageRun
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPackedRoot
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedRun
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseLocalTable
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStore
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedShape
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `MlDsa.AArch64.Optimized.PairedFirst`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedLoad`, which only this module used -/

section

/-! ## From `PairedProduct.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

/-- The selected seven instructions produce four exact REDC values. -/
theorem productMont_ok {d : VReg} {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : s.v .v31 = ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v30 = ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ s', VChg [.v26,.v27,.v28,d] s s' →
      s'.v d = ofVWords (redc (product (vword (s.v .v24) 0) (vword (s.v .v25) 0)))
        (redc (product (vword (s.v .v24) 1) (vword (s.v .v25) 1)))
        (redc (product (vword (s.v .v24) 2) (vword (s.v .v25) 2)))
        (redc (product (vword (s.v .v24) 3) (vword (s.v .v25) 3))) →
      WP isa (.block rest) s' Q) : WP isa (.block (productMont d ++ rest)) s Q := by
  have eq_q : (BitVec.ofNat 32 q).setWidth 64 = BitVec.ofNat 64 q := by decide
  let p := fun e => product (vword (s.v .v24) e) (vword (s.v .v25) e)
  refine wp_vop (d := .v26) rfl fun s₁ h₁ => ?_
  have a₁ : s₁.v .v26 = ofVDwords (p 0) (p 1) := h₁.v
  refine wp_vop (d := .v27) rfl fun s₂ h₂ => ?_
  have a₂ : s₂.v .v27 = ofVDwords (p 2) (p 3) := by
    rw [h₂.v, h₁.get .v24, h₁.get .v25]
    rfl
  refine wp_vop (d := .v28) rfl fun s₃ h₃ => ?_
  have a₃ : s₃.v .v28 = ofVWords ((p 0).extractLsb' 0 32) ((p 1).extractLsb' 0 32)
      ((p 2).extractLsb' 0 32) ((p 3).extractLsb' 0 32) := by
    rw [h₃.v, h₂.get .v26, a₁, a₂]; exact unzip_wide false _ _ _ _
  refine wp_vop (d := .v28) rfl fun s₄ h₄ => ?_
  have a₄ : s₄.v .v28 = ofVWords (multiplier (p 0)) (multiplier (p 1))
      (multiplier (p 2)) (multiplier (p 3)) := by
    rw [h₄.v, a₃, h₃.get .v30, h₂.get .v30, h₁.get .v30, hqi, map2_words]
    rfl
  refine wp_vop (d := .v26) rfl fun s₅ h₅ => ?_
  have a₅ : s₅.v .v26 = ofVDwords
      (p 0 + (multiplier (p 0)).setWidth 64 * BitVec.ofNat 64 q)
      (p 1 + (multiplier (p 1)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₅.v, h₄.get .v26, h₃.get .v26, h₂.get .v26, a₁, a₄,
      h₄.get .v31, h₃.get .v31, h₂.get .v31, h₁.get .v31, hq]
    simp only [ite_false, Bool.false_eq_true, Nat.zero_add, Nat.add_zero, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_0,
      vword_ofVWords_1, eq_q]
  refine wp_vop (d := .v27) rfl fun s₆ h₆ => ?_
  have a₆ : s₆.v .v27 = ofVDwords
      (p 2 + (multiplier (p 2)).setWidth 64 * BitVec.ofNat 64 q)
      (p 3 + (multiplier (p 3)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₆.v, h₅.get .v27, h₄.get .v27, h₃.get .v27, a₂, h₅.get .v28, a₄,
      h₅.get .v31, h₄.get .v31, h₃.get .v31, h₂.get .v31, h₁.get .v31, hq]
    simp only [ite_true, Nat.add_zero, Nat.reduceAdd, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_2,
      vword_ofVWords_3, eq_q]
  refine wp_vop (d := d) rfl fun s₇ h₇ => k s₇
    (VChg.mono (rs' := [.v26,.v27,.v28,d])
      ((((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans h₅.chg).trans h₆.chg).trans h₇.chg)
      (by
        intro r hr
        simp only [List.mem_append, List.mem_cons,
        List.mem_nil_iff, or_false] at *
        rcases hr with (((((h | h) | h) | h) | h) | h) | h <;> simp [h])) ?_
  rw [h₇.v, h₆.get .v26, a₅, a₆]
  exact unzip_wide true _ _ _ _


/-- Subtracting q yields the signed lanes consumed by the first inverse layer. -/
theorem productCentered_ok {d : VReg} (hd : d ≠ .v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : s.v .v31 = ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v30 = ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ t, VChg [.v26,.v27,.v28,d] s t →
      (∀ e < 4, vword (t.v d) e = centeredProduct
        (vword (s.v .v24) e) (vword (s.v .v25) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (productCentered d ++ rest)) s Q := by
  unfold productCentered
  rw [List.append_assoc]
  refine productMont_ok hq hqi fun t ht hv => ?_
  refine wp_vop (d := d) rfl fun u hu => ?_
  refine k u ((ht.trans hu.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at *
    grind only
  · intro e he
    rw [hu.v, VG.AArch64.vword_map2 _ _ _ he,
      ht.get .v31 (by simp [Ne.symm hd]), hv, hq]
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_using [he]) with rfl | rfl | rfl | rfl <;>
      simp only [vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3, centeredProduct]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedLoad.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

/-- The common challenge vector remains resident while loading one secret
vector. This is the selected load-sharing optimization, without a reload. -/
theorem loaded_ok {d : VReg} (h30 : d≠.v30) (h31 : d≠.v31)
    {s : State} (hc : ProductConstants s) {off : Nat}
    (ho : off%16=0 ∧ off<4096*16)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v25,.v26,.v27,.v28,d] s t → ProductConstants t →
      (∀e<4,vword (t.v d) e=centeredProduct (vword (s.v .v24) e)
        (vword (s.mem.read (s.gpr .x14+BitVec.ofNat 64 off) 16) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.ldrq .v25 .x14 off::productCentered d++rest)) s Q := by
  refine wp_ldrq ho rfl hr fun a ha => ?_
  have ca := hc.chg ha.chg (by decide) (by decide)
  refine productCentered_ok h31 ca.qv ca.qiv fun t ht hv => ?_
  have h : VChg [.v25,.v26,.v27,.v28,d] s t := (ha.chg.trans ht).mono (by
    intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only)
  refine k t h (hc.chg h (by simp [Ne.symm h30]) (by simp [Ne.symm h31])) ?_
  intro e he
  rw [hv e he,ha.get .v24,ha.v]


theorem product_ok (j : Fin 8) {s : State} (hc : ProductConstants s)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j.val)) 16)
    (hs : ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j.val)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v24,.v25,.v26,.v27,.v28,vr j.val,vr (8+j.val)] s t → ProductConstants t →
      (∀p<2,∀e<4,vword (t.v (vr (8*p+j.val))) e=centeredProduct
        (vword (s.mem.read (s.gpr .x13+BitVec.ofNat 64 (16*j.val)) 16) e)
        (vword (s.mem.read (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j.val)) 16) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (product j.val++rest)) s Q := by
  have safe : vr j.val≠vr (8+j.val) ∧
      vr j.val∉([.v24,.v25,.v26,.v27,.v28,.v30,.v31] : List VReg) ∧
      vr (8+j.val)∉([.v24,.v25,.v26,.v27,.v28,.v30,.v31] : List VReg) := by
    exact (show ∀j:Fin 8,vr j.val≠vr (8+j.val) ∧
      vr j.val∉([.v24,.v25,.v26,.v27,.v28,.v30,.v31] : List VReg) ∧
      vr (8+j.val)∉([.v24,.v25,.v26,.v27,.v28,.v30,.v31] : List VReg) by decide) j
  have d0 : vr j.val≠.v30 ∧ vr j.val≠.v31 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at safe
    grind only
  have d1 : vr (8+j.val)≠.v30 ∧ vr (8+j.val)≠.v31 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at safe
    grind only
  simp only [product,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.cons_append,List.nil_append,
    Nat.mul_zero,Nat.zero_add,Nat.mul_one,List.append_assoc]
  refine wp_ldrq (by omega_using []) rfl hr fun a ha => ?_
  refine loaded_ok d0.1 d0.2 (hc.chg ha.chg (by decide) (by decide)) (by omega_using []) ?_ fun b hb cb vb => ?_
  · rw [ha.chg.rd,ha.chg.wr,ha.chg.gpr]
    simpa using hs 0 (by decide)
  · refine loaded_ok d1.1 d1.2 cb (by omega_using []) ?_ fun t ht ct vt => ?_
    · rw [hb.rd,hb.wr,hb.gpr,ha.chg.rd,ha.chg.wr,ha.chg.gpr]
      simpa using hs 1 (by decide)
    · refine k t (((ha.chg.trans hb).trans ht).mono ?_) ct ?_
      · intro r hr
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only
      · intro p hp e he
        have h0 : vr j.val∉[.v25,.v26,.v27,.v28,vr (8+j.val)] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at *
          grind only
        have h24 : VReg.v24∉[.v25,.v26,.v27,.v28,vr j.val] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at *
          grind only
        rcases (show p=0 ∨ p=1 by omega_using [hp]) with rfl | rfl
        · simp only [Nat.mul_zero,Nat.zero_add]
          rw [ht.get _ h0,vb e he,ha.v,ha.chg.mem,ha.chg.gpr]
        · simp only [Nat.mul_one]
          rw [vt e he,hb.get .v24 h24,ha.v,hb.mem,hb.gpr,ha.chg.mem,ha.chg.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedFive`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedPackedRun`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PackedRoots packedOffset packedValues packedRunValues packedSteps)

def workRegs : List VReg := (List.range 16).map vr++[.v24,.v25,.v26,.v27,.v28,.v29]

theorem packedRoots_frame {s t : State} {z : Nat → Nat → Nat → Int}
    (h : PackedRoots s z) (hc : VChg workRegs s t) : PackedRoots t z := by
  refine ⟨?_,h.range,?_,?_,?_⟩
  · intro e he
    rw [hc.get .v31 (by decide)]
    exact h.q e he
  · simpa only [hc.rd,hc.wr,hc.gpr] using h.read
  · simpa only [hc.mem,hc.gpr] using h.root
  · simpa only [hc.mem,hc.gpr] using h.recip

def packedGroupCode (g : Fin 4) (len : Nat) : List Instr :=
  rootPair (packedOffset g.val len)++packedBothCode ⟨2*g.val,by omega_using []⟩ ⟨2*g.val+1,by omega_using []⟩ len

theorem packedRoot_subset (i j : Fin 8) : packedRootClobs i j⊆workRegs := by
  exact (show ∀i j:Fin 8,packedRootClobs i j⊆workRegs by decide) i j

theorem packedGroup_ok (g : Fin 4) (len : Nat) (hl : len=1 ∨ len=2)
    {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Values} {z : Nat → Nat → Nat → Int}
    (hv : Banks s v) (hr : PackedRoots s z)
    (k : ∀t,VChg workRegs s t → PackedRoots t z →
      Banks t (fun p => packedValues (v p) ⟨2*g.val,by omega_using []⟩ ⟨2*g.val+1,by omega_using []⟩ len (z g.val len)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (packedGroupCode g len++rest)) s Q := by
  have ho : packedOffset g.val len%16=0 ∧ packedOffset g.val len+16<65536 := by
    rcases hl with rfl | rfl <;> simp [packedOffset] <;> omega_using []
  have rr : RootReady s (packedOffset g.val len) (z g.val len) :=
    ⟨ho.1,ho.2,by simpa only [Nat.add_zero] using hr.read g.val g.isLt len hl 0 (Or.inl rfl),
      hr.read g.val g.isLt len hl 16 (Or.inr rfl),hr.range g.val g.isLt len hl,
      hr.root g.val g.isLt len hl,hr.recip g.val g.isLt len hl⟩
  unfold packedGroupCode
  refine packedRoot_ok _ _ len _ (by intro h; have hh := congrArg Fin.val h; change 2*g.val=2*g.val+1 at hh; omega_using [hh])
    hv rr hr.q fun t ht hvt => ?_
  have hc : VChg workRegs s t := ht.mono (packedRoot_subset _ _)
  exact k t hc (packedRoots_frame hr hc) hvt

def packedCode (ps : List (Fin 4 × Nat)) : List Instr := ps.flatMap fun (g,len) => packedGroupCode g len

theorem packedRun_ok (ps : List (Fin 4 × Nat)) (hl : ∀p∈ps,p.2=1 ∨ p.2=2)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} {z : Nat → Nat → Nat → Int}
    (hv : Banks s v) (hr : PackedRoots s z)
    (k : ∀t,VChg workRegs s t → PackedRoots t z →
      Banks t (fun p => packedRunValues (v p) z ps) → WP isa (.block rest) t Q) :
    WP isa (.block (packedCode ps++rest)) s Q := by
  induction ps generalizing s v with
  | nil => exact k s (VChg.refl _ _) hr hv
  | cons op ps ih =>
    simp only [packedCode,List.flatMap_cons,List.append_assoc]
    refine packedGroup_ok op.1 op.2 (hl op (by simp)) hv hr fun a ha ra va => ?_
    refine ih (fun p hp => hl p (List.mem_cons_of_mem _ hp)) va ra fun t ht rt vt => ?_
    exact k t ((ha.trans ht).mono (by simp)) rt vt

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (packedSteps packedRunValues PackedRoots localOffset)

def fiveCode : List Instr := packedCode packedSteps++stageRunCode (fun i => localOffset i.val) (List.finRange 7)

theorem fiveCode_eq : fiveCode =
    ([1,2].flatMap fun len => (List.range 4).flatMap fun j =>
      rootPair ((if len=1 then 0 else 128)+32*j) ++
      [0,1].flatMap (fun p => packed (vr (8*p+2*j)) (vr (8*p+2*j+1)) len)) ++
    ([4,8,16].flatMap fun len => (List.range (16/len)).flatMap fun b =>
      rootPair ((if len=4 then 256 else if len=8 then 384 else 448)+32*b) ++
      (List.range (len/4)).flatMap (fun j => batchPair (b*len/2+j) (b*len/2+j+len/4))) := by
  kernel_rfl

theorem five_ok {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    {zp : Nat → Nat → Nat → Int} {zl : Nat → Nat → Int}
    (hv : Banks s v) (hp : PackedRoots s zp)
    (hl : ∀i:Fin 7,RootReady s (localOffset i.val) (zl i.val))
    (k : ∀t,VChg workRegs s t →
      Banks t (fun p => Inverse.runValues zl 0 7 (packedRunValues (v p) zp packedSteps)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (fiveCode++rest)) s Q := by
  simp only [fiveCode,List.append_assoc]
  refine packedRun_ok packedSteps (by decide) hv hp fun a ha hpa va => ?_
  refine stageRun_ok (List.finRange 7) (fun i => localOffset i.val) (fun i => zl i.val)
    va (fun i => (hl i).chg ha) hpa.q fun t ht vt => ?_
  have hc : VChg workRegs s t := (ha.trans ht).mono (by
    intro r hr
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · exact hr
    · exact (show stageRunRegs⊆workRegs by decide) hr)
  exact k t hc (by simpa only [stageRunValues_all] using vt)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end


/-! ## From `PairedBank.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def productTemps : List VReg := [.v24,.v25,.v26,.v27,.v28]
def productClobs (js : List (Fin 8)) : List VReg :=
  productTemps++js.flatMap (fun j => [vr j.val,vr (8+j.val)])
def productInput (s : State) (j p e : Nat) : BitVec 32 :=
  centeredProduct (vword (s.mem.read (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16) e)
    (vword (s.mem.read (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j)) 16) e)

theorem bank_not_clob {j : Fin 8} {js : List (Fin 8)} (hj : j∉js) {p : Nat} (hp : p<2) :
    vr (8*p+j.val)∉productClobs js := by
  intro h
  rcases List.mem_append.mp h with h | h
  · have hb := bank_safe (j := 8*p+j.val) (by omega_using [hp])
    apply hb
    simp only [productTemps,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · obtain ⟨i,hi,h⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    have he : j=i := by
      apply Fin.ext
      rcases h with h | h
      · have hx := bank_injective (by omega_using [hp]) (by omega_using []) h
        omega_using [hx]
      · have hx := bank_injective (by omega_using [hp]) (by omega_using []) h
        omega_using [hx]
    exact hj (he ▸ hi)

theorem productBank_ok (js : List (Fin 8)) (hn : js.Nodup)
    {s : State} (hc : ProductConstants s)
    (hr : ∀j∈js,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j.val)) 16 ∧
      ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j.val)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg (productClobs js) s t → ProductConstants t →
      (∀j∈js,∀p<2,∀e<4,vword (t.v (vr (8*p+j.val))) e=productInput s j.val p e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (js.flatMap (fun j => product j.val)++rest)) s Q := by
  induction js generalizing s with
  | nil => exact k s (VChg.refl _ _) hc (by simp)
  | cons j js ih =>
    have nn := List.nodup_cons.mp hn
    have rr := hr j (by simp)
    simp only [List.flatMap_cons,List.append_assoc]
    refine product_ok j hc rr.1 rr.2 fun a ha ca va => ?_
    refine ih nn.2 ca ?_ fun t ht ct vt => ?_
    · intro i hi
      rw [ha.rd,ha.wr,ha.gpr]
      exact hr i (List.mem_cons_of_mem _ hi)
    · refine k t ((ha.trans ht).mono ?_) ct ?_
      · intro r hm
        simp only [productClobs,productTemps,List.flatMap_cons,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false] at *
        grind only
      · intro i hi p hp e he
        rcases List.mem_cons.mp hi with rfl | hi
        · rw [ht.get _ (bank_not_clob nn.1 hp),va p hp e he]
          rfl
        · rw [vt i hi p hp e he]
          unfold productInput
          rw [ha.mem,ha.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedInputs.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def inputValues (s : State) : Values := fun p => Vector.ofFn fun j =>
  ofVWords (productInput s j.val p.val 0) (productInput s j.val p.val 1)
    (productInput s j.val p.val 2) (productInput s j.val p.val 3)

theorem inputValues_word (s : State) (p : Fin 2) (j : Fin 8) {e : Nat} (he : e<4) :
    vword ((inputValues s p)[j.val]) e=productInput s j.val p.val e := by
  simp only [inputValues,Vector.getElem_ofFn]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_using [he]) with rfl | rfl | rfl | rfl <;>
    simp only [vword_ofVWords_0,vword_ofVWords_1,vword_ofVWords_2,vword_ofVWords_3]

/-- Exact sixteen-vector initial state of the selected paired transform. -/
theorem inputs_ok {s : State} (hc : ProductConstants s)
    (hr : ∀j<8,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16 ∧
      ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg (productClobs (List.finRange 8)) s t → ProductConstants t →
      Banks t (inputValues s) → WP isa (.block rest) t Q) :
    WP isa (.block ((List.range 8).flatMap product++rest)) s Q := by
  have heq : (List.finRange 8).flatMap (fun j => product j.val)=(List.range 8).flatMap product := rfl
  rw [← heq]
  refine productBank_ok _ (List.nodup_finRange 8) hc (fun j _ => hr j.val j.isLt) fun t ht ct vt =>
    k t ht ct ?_
  intro p j
  apply vec_ext
  intro e he
  rw [inputValues_word s p j he]
  simpa only [bankRegs,Vector.getElem_ofFn] using vt j (List.mem_finRange j) p.val p.isLt e he

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedProductFive.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PackedRoots packedSteps packedRunValues localOffset)

def productFiveCode : List Instr := (List.range 8).flatMap product++fiveCode

theorem productFive_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {zp : Nat → Nat → Nat → Int} {zl : Nat → Nat → Int}
    (hc : ProductConstants s) (hp : PackedRoots s zp)
    (hl : ∀i:Fin 7,RootReady s (localOffset i.val) (zl i.val))
    (hr : ∀j<8,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16 ∧
      ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j)) 16)
    (k : ∀t,VChg workRegs s t → Banks t (fun p =>
      Inverse.runValues zl 0 7 (packedRunValues (inputValues s p) zp packedSteps)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (productFiveCode++rest)) s Q := by
  simp only [productFiveCode,List.append_assoc]
  refine inputs_ok hc hr fun a ha _ va => ?_
  have ha' : VChg workRegs s a := ha.mono (by decide)
  refine five_ok va (packedRoots_frame hp ha') (fun i => (hl i).chg ha) fun t ht vt => ?_
  exact k t ((ha'.trans ht).mono (by simp)) vt

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFirst.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PackedRoots packedRoot localRoot localOffset fiveValues)

def firstCode : List Instr := productFiveCode++(pairStores 16).map (fun p => Instr.strq p.1 .x0 p.2)
def firstAdvance : List Instr :=
  [.addImm .x .x13 .x13 128,.addImm .x .x14 .x14 128,.addImm .x .x0 .x0 128,
   .addImm .x .x1 .x1 480,.subImm .x .x11 .x11 1]

theorem firstBlock_eq : firstBlock=firstCode++firstAdvance := by
  unfold firstBlock firstCode productFiveCode
  rw [fiveCode_eq]
  rfl

theorem first_ok (u : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (hc : ProductConstants s) (hp : PackedRoots s (packedRoot u))
    (hl : ∀i:Fin 7,RootReady s (localOffset i.val) (localRoot u i.val))
    (hr : ∀j<8,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16 ∧
      ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j)) 16)
    (hw : ∀p:Fin 2,∀j:Fin 8,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (1024*p.val+16*j.val)) 16)
    (k : ∀t,(∃a,VChg workRegs s a ∧ VMem a t
      (writePair (fun p => fiveValues u (inputValues s p)) (s.gpr .x0) 16 s.mem)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (firstCode++rest)) s Q := by
  simp only [firstCode,List.append_assoc]
  refine productFive_ok hc hp hl hr fun a ha va => ?_
  refine storePair_ok 16 .x0 (by intro p j; constructor <;> omega_using []) va ?_ fun t ht => ?_
  · intro p j
    simpa only [ha.wr,ha.gpr] using hw p j
  · refine k t ⟨a,ha,?_⟩
    simpa only [ha.gpr,ha.mem,Inverse.fiveValues] using ht

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end


/-! ## From `PairedStoreMemory.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem writePair_split (v : Values) (base : Addr) (stride : Nat) (m : Mem) :
    writePair v base stride m=writeBank (v 1) (base+1024) stride (writeBank (v 0) base stride m) := by
  simp only [writePair,show List.finRange 2=[0,1] by rfl,List.foldl_cons,List.foldl_nil,
    Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.zero_add,Nat.mul_one,writeBank]
  simp only [BitVec.ofNat_add,BitVec.add_assoc,show (1024 : Addr)=1024#64 by rfl]

theorem writePair_frame (v : Values) (base : Addr) (stride : Nat)
    {m m₀ : Mem} {W : List Region} {r : Region} (hr : r∈W)
    (hc : ∀p:Fin 2,∀j:Fin 8,r.Contains (base+BitVec.ofNat 64 (1024*p.val+stride*j.val)) 16)
    (hf : Frame W m₀ m) : Frame W m₀ (writePair v base stride m) := by
  rw [writePair_split]
  refine writeBank_frame _ _ _ hr ?_ ?_
  · intro j
    simpa only [Fin.val_one,Nat.mul_one,BitVec.ofNat_add,BitVec.add_assoc,show (1024 : Addr)=1024#64 by rfl] using hc 1 j
  · refine writeBank_frame _ _ _ hr ?_ hf
    intro j
    simpa only [Fin.val_zero,Nat.mul_zero,Nat.zero_add] using hc 0 j

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFirstMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (fiveValues)

def valuesAt (m : Mem) (a b : Addr) : Values := fun p => Vector.ofFn fun j =>
  let aa := m.read (a+BitVec.ofNat 64 (16*j.val)) 16
  let bb := m.read (b+BitVec.ofNat 64 (1024*p.val+16*j.val)) 16
  ofVWords (centeredProduct (vword aa 0) (vword bb 0))
    (centeredProduct (vword aa 1) (vword bb 1))
    (centeredProduct (vword aa 2) (vword bb 2))
    (centeredProduct (vword aa 3) (vword bb 3))

theorem inputValues_eq (s : State) : inputValues s=valuesAt s.mem (s.gpr .x13) (s.gpr .x14) := rfl

def firstPassMem (m : Mem) (p a b : Addr) : Nat → Mem
  | 0 => m
  | u+1 =>
    let prev := firstPassMem m p a b u
    let v := valuesAt prev (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u))
    writePair (fun j => fiveValues u (v j)) (p+BitVec.ofNat 64 (128*u)) 16 prev

theorem firstPass_frame {m : Mem} {p a b : Addr} {u : Nat} (hu : u≤8) :
    Frame [⟨p,2048⟩] m (firstPassMem m p a b u) := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [firstPassMem]
    refine writePair_frame _ _ _ (r:=⟨p,2048⟩) (by simp) ?_ (ih (by omega_using [hu]))
    intro poly j
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact Offset.contains_base p (by omega_using [hu]) (by omega_using [hu])

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
