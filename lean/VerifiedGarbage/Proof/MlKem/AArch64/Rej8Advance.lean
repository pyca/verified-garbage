module

public import VerifiedGarbage.Proof.MlKem.CoeffW
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Table
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem

/-! ### `MlKem.AArch64.Rej8Store`, which the modules that import this one used -/

section

/-! # Stable compaction and widening stores of an eight-candidate batch -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

def wideLo (x z : BitVec 128) : BitVec 128 := VPermOp.eval .zip1 .h8 x z
def wideHi (x z : BitVec 128) : BitVec 128 := VPermOp.eval .zip2 .h8 x z

def storeCode (w16 : Bool := false) : List Instr :=
 [.ldrq .v2 .x7 0,.vop (.tbl .v0 .v0 .v2)] ++
 (if w16 then [.strq .v0 .x3 0] else [.vop (.perm .zip1 .h8 .v1 .v0 .v21),
 .vop (.perm .zip2 .h8 .v2 .v0 .v21),.strq .v1 .x3 0,.strq .v2 .x3 16])

/-- With 16-bit coefficients, the compacted halfwords themselves. -/
structure StorePost16 (s t : State) (mask : Nat) : Prop where
  keep : Keep [] s t
  gpr : t.gpr=s.gpr
  other : ∀ r, r ∉ [.v0,.v1,.v2] → t.v r=s.v r
  mem : t.mem = s.mem.write (s.gpr .x3) 16 (compactValue (s.v .v0) mask)

theorem store16_ok (s : State) (mask : Nat)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x7) 16)
    (table : s.mem.read (s.gpr .x7) 16 = tableVec mask)
    (hw0 : InRegions s.wr (s.gpr .x3) 16) :
    WP isa (.block (storeCode true)) s (fun t => StorePost16 s t mask) := by
  refine wp_ldrq (a := s.gpr .x7) (by decide) (ptr_zero _) hr fun a ha =>
    wp_vop (d := .v0) rfl fun b hb => ?_
  have hv0 : b.v .v0 = compactValue (s.v .v0) mask := by
    rw [hb.v,ha.v,table,ha.get .v0]
    rfl
  refine wp_strq (a := s.gpr .x3) (by decide) (by rw [hb.gpr,ha.gpr]; exact ptr_zero _)
    (by rw [hb.wr,ha.wr]; exact hw0) fun t ht => wp_nil ?_
  have hc0 := (ha.chg.trans hb.chg).mono (rs' := [.v0,.v1,.v2]) (by decide)
  refine ⟨hc0.keep.trans ht.keep, ht.gpr.trans (hb.gpr.trans ha.gpr), ?_, ?_⟩
  · intro r hr
    rw [ht.v,hc0.v r hr]
  · rw [ht.mem,hv0,hb.mem,ha.mem]

structure StorePost (s t : State) (mask : Nat) : Prop where
  keep : Keep [] s t
  gpr : t.gpr=s.gpr
  other : ∀ r, r ∉ [.v0,.v1,.v2] → t.v r=s.v r
  mem : t.mem = (s.mem.write (s.gpr .x3) 16
      (wideLo (compactValue (s.v .v0) mask) (s.v .v21))).write (s.gpr .x3+16) 16
      (wideHi (compactValue (s.v .v0) mask) (s.v .v21))

theorem store_ok (s : State) (mask : Nat)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x7) 16)
    (table : s.mem.read (s.gpr .x7) 16 = tableVec mask)
    (hw0 : InRegions s.wr (s.gpr .x3) 16)
    (hw1 : InRegions s.wr (s.gpr .x3+16) 16) :
    WP isa (.block storeCode) s (fun t => StorePost s t mask) := by
  refine wp_ldrq (a := s.gpr .x7) (by decide) (ptr_zero _) hr fun a ha =>
    wp_vop (d := .v0) rfl fun b hb =>
    wp_vop (d := .v1) rfl fun c hc =>
    wp_vop (d := .v2) rfl fun d hd => ?_
  have hv0 : d.v .v1 = wideLo (compactValue (s.v .v0) mask) (s.v .v21) := by
    rw [hd.get .v1,hc.v,hb.v,ha.v,table,ha.get .v0,hb.get .v21,ha.get .v21]
    rfl
  have hv1 : d.v .v2 = wideHi (compactValue (s.v .v0) mask) (s.v .v21) := by
    rw [hd.v,hc.get .v0,hb.v,ha.v,table,ha.get .v0,hc.get .v21,hb.get .v21,ha.get .v21]
    rfl
  have hg : d.gpr=s.gpr := hd.gpr.trans (hc.gpr.trans (hb.gpr.trans ha.gpr))
  have hw : d.wr=s.wr := hd.wr.trans (hc.wr.trans (hb.wr.trans ha.wr))
  refine wp_strq (a := s.gpr .x3) (by decide) (by rw [hg]; exact ptr_zero _)
    (by rw [hw]; exact hw0) fun e he =>
    wp_strq (a := s.gpr .x3+16) (by decide) (by rw [he.gpr,hg]; rfl)
    (by rw [he.wr,hw]; exact hw1) fun t ht => wp_nil ?_
  have hc0 := (((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).mono
    (rs' := [.v0,.v1,.v2]) (by decide)
  refine ⟨(hc0.keep.trans he.keep).trans ht.keep,
    ht.gpr.trans (he.gpr.trans hg), ?_, ?_⟩
  · intro r hr
    rw [ht.v,he.v,hc0.v r hr]
  · rw [ht.mem,he.mem,he.v,hv0,hv1,hd.mem,hc.mem,hb.mem,ha.mem]

theorem widened_coeffs (x z : BitVec 128) {mask : Nat} (hm : mask<256)
    (hz : ∀ i<8,vhalf z i=0) {i : Nat} (hi : i<4) :
    (vword (wideLo (compactValue x mask) z) i).toNat =
      (if i < (Impl.MlKem.AArch64.Rej8.acceptedLanes mask).length then
        vhalf x ((Impl.MlKem.AArch64.Rej8.acceptedLanes mask).getD i 0) else 0).toNat ∧
    (vword (wideHi (compactValue x mask) z) i).toNat =
      (if 4+i < (Impl.MlKem.AArch64.Rej8.acceptedLanes mask).length then
        vhalf x ((Impl.MlKem.AArch64.Rej8.acceptedLanes mask).getD (4+i) 0) else 0).toNat := by
  have h := vword_zip_zero (x := compactValue x mask) hz hi
  rw [compact_half x hm (by omega_using [hi]),compact_half x hm (by omega_using [hi])] at h
  exact h

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! # Output and input advancement after stable vector compaction -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64

def advanceCode (w16 : Bool := false) : List Instr :=
 [.lsr .x .x6 .x6 8,.movz .x .x7 15 0,.logic .and .x .x6 .x6 .x7,
 .sub .x .x4 .x4 .x6,.lsl .x .x6 .x6 (if w16 then 1 else 2),.add .x .x3 .x3 .x6,
 .addImm .x .x2 .x2 12,.subImm .x .x5 .x5 4]

structure AdvancePost (w16 : Bool) (s t : State) (n : Nat) : Prop where
  only : Only [.x2,.x3,.x4,.x5,.x6,.x7] s t
  output : t.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 (VG.Proof.MlKem.cs w16*n)
  remain : (t.gpr .x4).toNat = (s.gpr .x4).toNat - n
  input : t.gpr .x2 = s.gpr .x2 + 12
  chunks : (t.gpr .x5).toNat = (s.gpr .x5).toNat - 4

theorem advance_ok (w16 : Bool) (s : State) {n : Nat} (hn : n≤8)
    (h4 : 8 ≤ (s.gpr .x4).toNat) (h5 : 4 ≤ (s.gpr .x5).toNat)
    (hc : ((s.gpr .x6 >>> 8) &&& 15).toNat = n) :
    WP isa (.block (advanceCode w16)) s (fun t => AdvancePost w16 s t n) := by
  refine wp_lsr (by decide) fun a ha ea => wp_movz fun b hb eb =>
    wp_and fun c hc0 ec => wp_sub fun d hd ed => wp_lsl (by cases w16 <;> decide) fun e he ee =>
    wp_add fun f hf ef => wp_addImm (by decide) fun g hg eg =>
    wp_subImm (by decide) fun t ht et => wp_nil ?_
  have cn : (c.gpr .x6).toNat=n := by
    rw [ec,hb.get .x6,ea,eb]
    exact hc
  have dn : (d.gpr .x6).toNat=n := by rw [hd.get .x6,cn]
  have en : e.gpr .x6=BitVec.ofNat 64 (VG.Proof.MlKem.cs w16*n) := by
    apply BitVec.eq_of_toNat_eq
    cases w16 <;>
    · rw [ee,toNat_lsl_n (by rw [dn]; simp only [Bool.false_eq_true, ite_false, ite_true]; omega_using [hn]),dn,
        BitVec.toNat_ofNat]
      simp only [VG.Proof.MlKem.cs_eq, Bool.false_eq_true, ite_false, ite_true]; omega_using [hn]
  refine ⟨(((((((ha.trans hb).trans hc0).trans hd).trans he).trans hf).trans hg).trans ht).mono
    (by decide),?_,?_,?_,?_⟩
  · rw [ht.get .x3,hg.get .x3,ef,en,he.get .x3,hd.get .x3,hc0.get .x3,hb.get .x3,ha.get .x3]
  · rw [ht.get .x4,hg.get .x4,hf.get .x4,he.get .x4,ed,
      hc0.get .x4,hb.get .x4,ha.get .x4,BitVec.toNat_sub,cn]
    have := (s.gpr .x4).isLt
    omega_using [hn, h4]
  · rw [ht.get .x2,eg,hf.get .x2,he.get .x2,hd.get .x2,hc0.get .x2,hb.get .x2,ha.get .x2]
    rfl
  · rw [et,hg.get .x5,hf.get .x5,he.get .x5,hd.get .x5,hc0.get .x5,hb.get .x5,ha.get .x5,
      BitVec.toNat_sub]
    have hb4 : (BitVec.ofNat 64 4).toNat=4 := rfl
    have := (s.gpr .x5).isLt
    simp only [hb4]
    omega_using [h5]

end VG.Proof.MlKem.AArch64.Rej8
