module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Table
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Parse

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
  rw [compact_half x hm (by omega),compact_half x hm (by omega)] at h
  exact h

end VG.Proof.MlKem.AArch64.Rej8
