module
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Product
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductWord
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `MlDsa.AArch64.Optimized.ProductVec`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Impl.MlDsa.AArch64.Optimized

/-- The selected seven instructions produce four exact REDC values. -/
theorem productMont_ok {d : VReg} {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : s.v .v31 = ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v30 = ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ s', VChg [.v18,.v19,.v20,d] s s' →
      s'.v d = ofVWords (redc (product (vword (s.v .v16) 0) (vword (s.v .v17) 0)))
        (redc (product (vword (s.v .v16) 1) (vword (s.v .v17) 1)))
        (redc (product (vword (s.v .v16) 2) (vword (s.v .v17) 2)))
        (redc (product (vword (s.v .v16) 3) (vword (s.v .v17) 3))) →
      WP isa (.block rest) s' Q) : WP isa (.block (productMont d ++ rest)) s Q := by
  have eq_q : (BitVec.ofNat 32 q).setWidth 64 = BitVec.ofNat 64 q := by decide
  let p := fun e => product (vword (s.v .v16) e) (vword (s.v .v17) e)
  refine wp_vop (d := .v18) rfl fun s₁ h₁ => ?_
  have a₁ : s₁.v .v18 = ofVDwords (p 0) (p 1) := h₁.v
  refine wp_vop (d := .v19) rfl fun s₂ h₂ => ?_
  have a₂ : s₂.v .v19 = ofVDwords (p 2) (p 3) := by
    rw [h₂.v, h₁.get .v16, h₁.get .v17]
    rfl
  refine wp_vop (d := .v20) rfl fun s₃ h₃ => ?_
  have a₃ : s₃.v .v20 = ofVWords ((p 0).extractLsb' 0 32) ((p 1).extractLsb' 0 32)
      ((p 2).extractLsb' 0 32) ((p 3).extractLsb' 0 32) := by
    rw [h₃.v, h₂.get .v18, a₁, a₂]; exact unzip_wide false _ _ _ _
  refine wp_vop (d := .v20) rfl fun s₄ h₄ => ?_
  have a₄ : s₄.v .v20 = ofVWords (multiplier (p 0)) (multiplier (p 1))
      (multiplier (p 2)) (multiplier (p 3)) := by
    rw [h₄.v, a₃, h₃.get .v30, h₂.get .v30, h₁.get .v30, hqi, map2_words]
    rfl
  refine wp_vop (d := .v18) rfl fun s₅ h₅ => ?_
  have a₅ : s₅.v .v18 = ofVDwords
      (p 0 + (multiplier (p 0)).setWidth 64 * BitVec.ofNat 64 q)
      (p 1 + (multiplier (p 1)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₅.v, h₄.get .v18, h₃.get .v18, h₂.get .v18, a₁, a₄,
      h₄.get .v31, h₃.get .v31, h₂.get .v31, h₁.get .v31, hq]
    simp only [ite_false, Bool.false_eq_true, Nat.zero_add, Nat.add_zero, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_0,
      vword_ofVWords_1, eq_q]
  refine wp_vop (d := .v19) rfl fun s₆ h₆ => ?_
  have a₆ : s₆.v .v19 = ofVDwords
      (p 2 + (multiplier (p 2)).setWidth 64 * BitVec.ofNat 64 q)
      (p 3 + (multiplier (p 3)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₆.v, h₅.get .v19, h₄.get .v19, h₃.get .v19, a₂, h₅.get .v20, a₄,
      h₅.get .v31, h₄.get .v31, h₃.get .v31, h₂.get .v31, h₁.get .v31, hq]
    simp only [ite_true, Nat.add_zero, Nat.reduceAdd, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_2,
      vword_ofVWords_3, eq_q]
  refine wp_vop (d := d) rfl fun s₇ h₇ => k s₇
    (VChg.mono (rs' := [.v18,.v19,.v20,d])
      ((((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans h₅.chg).trans h₆.chg).trans h₇.chg)
      (by
        intro r hr
        simp only [List.mem_append, List.mem_cons,
        List.mem_nil_iff, or_false] at *
        rcases hr with (((((h | h) | h) | h) | h) | h) | h <;> simp [h])) ?_
  rw [h₇.v, h₆.get .v18, a₅, a₆]
  exact unzip_wide true _ _ _ _


/-- Subtracting q yields the signed lanes consumed by the first inverse layer. -/
theorem productCentered_ok {d : VReg} (hd : d ≠ .v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : s.v .v31 = ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v30 = ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ t, VChg [.v18,.v19,.v20,d] s t →
      (∀ e < 4, vword (t.v d) e = centeredProduct
        (vword (s.v .v16) e) (vword (s.v .v17) e)) → WP isa (.block rest) t Q) :
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

end VG.Proof.MlDsa.AArch64.Optimized

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Proof.MlDsa.Arith
open VG.Impl.MlDsa.AArch64.Optimized

structure ProductConstants (s : State) : Prop where
  qv : s.v .v31 = ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
    (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
  qiv : s.v .v30 = ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
    (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)

theorem ProductConstants.chg {s t : State} (h : ProductConstants s)
    {rs : List VReg} (k : VChg rs s t) (h30 : VReg.v30 ∉ rs) (h31 : VReg.v31 ∉ rs) :
    ProductConstants t := ⟨by rw [k.get _ h31]; exact h.qv, by rw [k.get _ h30]; exact h.qiv⟩

/-- The two loads and exact selected product preserve all memory, pointer
registers, and constants; output lanes refer to the original input buffers. -/
theorem productLoad_ok {d : VReg} (h30 : d ≠ .v30) (h31 : d ≠ .v31)
    {s : State} (hc : ProductConstants s) {off : Nat}
    (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v16,.v17,.v18,.v19,.v20,d] s t → ProductConstants t →
      (∀ e<4, vword (t.v d) e = centeredProduct
        (vword (s.mem.read (s.gpr .x13+BitVec.ofNat 64 off) 16) e)
        (vword (s.mem.read (s.gpr .x14+BitVec.ofNat 64 off) 16) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (productLoad d off ++ rest)) s Q := by
  unfold productLoad
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrq ho rfl ha fun a h1 => ?_
  have hb' : InRegions (a.rd++a.wr) (a.gpr .x14+BitVec.ofNat 64 off) 16 := by
    rw [h1.chg.rd,h1.chg.wr,h1.chg.gpr]; exact hb
  refine wp_ldrq ho rfl hb' fun b h2 => ?_
  have cb := (hc.chg h1.chg (by decide) (by decide)).chg h2.chg (by decide) (by decide)
  refine productCentered_ok h31 cb.qv cb.qiv fun t ht hv => ?_
  have h : VChg [.v16,.v17,.v18,.v19,.v20,d] s t :=
    ((h1.chg.trans h2.chg).trans ht).mono (by
      intro r hr
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
      grind only)
  refine k t h (hc.chg h (by simp [Ne.symm h30]) (by simp [Ne.symm h31])) ?_
  intro e he
  rw [hv e he,h2.get .v16,h1.v,h2.v,h1.chg.mem,h1.chg.gpr]

end VG.Proof.MlDsa.AArch64.Optimized
