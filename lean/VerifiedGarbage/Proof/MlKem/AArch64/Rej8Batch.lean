module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe

/-! # One complete eight-candidate rejection batch -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64

def acceptedCount (s : State) : Nat :=
  (Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).length

/-- The memory after the stores: with 32-bit coefficients the compacted halfwords widened to
words, with 16-bit ones the compacted halfwords. -/
def updatedMem (s : State) (w16 : Bool := false) : Mem :=
  if w16 then s.mem.write (s.gpr .x3) 16 (compactValue (candidatesAt s) (maskAt s))
  else (s.mem.write (s.gpr .x3) 16
    (wideLo (compactValue (candidatesAt s) (maskAt s)) (s.v .v21))).write (s.gpr .x3+16) 16
    (wideHi (compactValue (candidatesAt s) (maskAt s)) (s.v .v21))

structure BatchPostW (w16 : Bool) (s t : State) : Prop where
  keep : Keep [.x2,.x3,.x4,.x5,.x6,.x7] s t
  other : ∀ r, r ∉ [.v0,.v1,.v2] → t.v r=s.v r
  mem : t.mem=updatedMem s w16
  output : t.gpr .x3=s.gpr .x3+BitVec.ofNat 64 (VG.Proof.MlKem.cs w16*acceptedCount s)
  remain : (t.gpr .x4).toNat=(s.gpr .x4).toNat-acceptedCount s
  input : t.gpr .x2=s.gpr .x2+12
  chunks : (t.gpr .x5).toNat=(s.gpr .x5).toNat-4

theorem batch_ok (w16 : Bool) (s : State) (hc : Constants s)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 16)
    (h4 : 8≤(s.gpr .x4).toNat) (h5 : 4≤(s.gpr .x5).toNat)
    (hw0 : InRegions s.wr (s.gpr .x3) 16)
    (hw1 : w16 = false → InRegions s.wr (s.gpr .x3+16) 16)
    (hread : ∀ mask<256, InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16)
    (htbl : ∀ mask<256, s.mem.read (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16=tableVec mask) :
    WP isa (.block (Impl.MlKem.AArch64.Rej8.rejEight w16)) s (fun t => BatchPostW w16 s t) := by
  rw [show Impl.MlKem.AArch64.Rej8.rejEight w16=probeCode++storeCode w16++advanceCode w16 by
      cases w16 <;> rfl,
    WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (probe_ok s hc hr) fun a ha => ?_
  have hm : maskAt s<256 := acceptanceMask_bound _
  have adv : ∀ b : State, b.gpr = a.gpr → WP isa (.block (advanceCode w16)) b
      (fun t => AdvancePost w16 b t (acceptedCount s) ∧ t.v = b.v) := fun b hg =>
    WP.keepV (by cases w16 <;> rfl) (advance_ok w16 b (accepted_length _)
      (by rw [hg,ha.keep.get .x4]; exact h4)
      (by rw [hg,ha.keep.get .x5]; exact h5) (by rw [hg]; exact ha.count))
  cases w16
  · refine WP.mono (store_ok a (maskAt s)
      (by rw [ha.keep.rd,ha.keep.wr,ha.index]; exact hread _ hm)
      (by rw [ha.mem,ha.index]; exact htbl _ hm)
      (by rw [ha.keep.wr,ha.keep.get .x3]; exact hw0)
      (by rw [ha.keep.wr,ha.keep.get .x3]; exact hw1 rfl)) fun b hb => ?_
    refine WP.mono (adv b hb.gpr) fun t ⟨ht,htv⟩ => ?_
    refine ⟨((ha.keep.trans hb.keep).trans ht.only.keep).mono (by decide),?_,?_,?_,?_,?_,?_⟩
    · intro r hr0
      rw [htv,hb.other r hr0,ha.other r hr0]
    · rw [ht.only.mem,hb.mem,ha.mem,ha.keep.get .x3,ha.values,ha.other .v21 (by decide)]
      rfl
    · rw [ht.output,hb.gpr,ha.keep.get .x3]
    · rw [ht.remain,hb.gpr,ha.keep.get .x4]
    · rw [ht.input,hb.gpr,ha.keep.get .x2]
    · rw [ht.chunks,hb.gpr,ha.keep.get .x5]
  · refine WP.mono (store16_ok a (maskAt s)
      (by rw [ha.keep.rd,ha.keep.wr,ha.index]; exact hread _ hm)
      (by rw [ha.mem,ha.index]; exact htbl _ hm)
      (by rw [ha.keep.wr,ha.keep.get .x3]; exact hw0)) fun b hb => ?_
    refine WP.mono (adv b hb.gpr) fun t ⟨ht,htv⟩ => ?_
    refine ⟨((ha.keep.trans hb.keep).trans ht.only.keep).mono (by decide),?_,?_,?_,?_,?_,?_⟩
    · intro r hr0
      rw [htv,hb.other r hr0,ha.other r hr0]
    · rw [ht.only.mem,hb.mem,ha.mem,ha.keep.get .x3,ha.values]
      rfl
    · rw [ht.output,hb.gpr,ha.keep.get .x3]
    · rw [ht.remain,hb.gpr,ha.keep.get .x4]
    · rw [ht.input,hb.gpr,ha.keep.get .x2]
    · rw [ht.chunks,hb.gpr,ha.keep.get .x5]

end VG.Proof.MlKem.AArch64.Rej8
