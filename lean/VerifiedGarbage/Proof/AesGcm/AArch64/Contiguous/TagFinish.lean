module

-- separate module: The machine-state proof of the interleaved block is independent of the caller and tag byte representation.

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.TagLengths
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.TagMask
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tag
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tag
open VG VG.AArch64 VG.Impl.AesGcm.AArch64.Contiguous.Tag
open VG.Proof.Gcm.AArch64.Stitch (fps flatten_singles)

private theorem separate : ∀ nr ∈ [10, 12, 14],
    ((fps.blockFp (mask nr)).bind fun a =>
      (fps.blockFp lengths).map fun b => fps.indep a b) = some true := by
  decide +kernel

/-- Each supported key schedule commutes with the final GHASH block. -/
theorem woven_ok {nr : Nat} (hn : nr = 10 ∨ nr = 12 ∨ nr = 14) {s : State} {Q : State → Prop}
    (h : WP isa (.block (mask nr)) s fun t => WP isa (.block lengths) t Q) :
    WP isa (.block (Impl.Weave.weaveG ((mask nr).map (fun x => [x])) (lengths.map (fun x => [x])))) s Q := by
  refine Interleave.WP.weaveG (P := fps.Inv) ?_ trivial ?_
  · rw [flatten_singles, flatten_singles]
    exact fps.indeps_of_check (separate nr (by rcases hn with rfl | rfl | rfl <;> decide))
  · rwa [flatten_singles, flatten_singles]

end VG.Proof.AesGcm.AArch64.Contiguous.Tag

namespace VG.Proof.AesGcm.AArch64.Contiguous.Tag
open VG VG.AArch64 VG.Impl.AesGcm.AArch64.Contiguous.Tag
open VG.Proof.Gcm.AArch64.Pmull
open VG.Proof.Aes.AArch64.Aese (st)
open VG.Proof.Gcm.AArch64.Stitch (sch)
open VG.Impl.AesGcm.AArch64 (alenO)
open VG.Impl.Gcm.AArch64.Pmull (Y)

theorem finish_ok {nr : Nat} (hn : nr = 10 ∨ nr = 12 ∨ nr = 14) {s : State} {H y : Spec.Gcm.Block}
    (law : MulKey) (key : Fast.HKey H s) (hy : s.v Y = ext8 y y)
    (keys : keyReadable nr s) (j0 : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 0) 16)
    (rd : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 alenO) 8)
    (wr : InRegions s.wr (s.gpr .x28 + BitVec.ofNat 64 0) 16) :
    let z := Spec.Gcm.mul (y ^^^ Spec.Gcm.ofBytes (Proof.Gcm.lensBlock (aadLength s).toNat (s.gpr .x26).toNat)) H
    WP isa (finish nr) s fun t => ∃ maskWord,
      st maskWord = Spec.Aes.cipher nr (sch nr s) (st (s.mem.readW (s.gpr .x20) 128)) ∧
      t.mem = s.mem.write (s.gpr .x28) 16 (VRevOp.eval .rev64b (ext8 z z) ^^^ maskWord) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  rw [finish, WP.block_append_iff]
  apply woven_ok hn
  refine (mask_ok (by omega_using [hn]) s keys j0).mono ?_
  intro a ⟨enc,f⟩
  have ka : Fast.HKey H a := key.of_v (f.v _ (by decide)) (f.v _ (by decide)) (f.v _ (by decide))
  have ya := (f.v Y (by decide)).trans hy
  have ra : InRegions (a.rd ++ a.wr) (a.gpr .x19 + BitVec.ofNat 64 alenO) 8 := by
    rwa [f.rd,f.wr,f.gpr]
  refine (lengths_ok law ka ya ra).mono ?_
  intro b ⟨hash,g⟩
  have out := (g.gpr .x28 (by decide) (by decide)).trans (congrFun f.gpr .x28)
  have wb : InRegions b.wr (b.gpr .x28 + BitVec.ofNat 64 0) 16 := by rwa [g.wr,f.wr,out]
  refine WP.block_cons_iff.mpr ⟨_,exec_eor _ _ _ _,?_⟩
  refine WP.block_cons_iff.mpr ⟨_,exec_strq (s := b.setV Y (b.v Y ^^^ b.v .v28)) (by decide) (by decide) wb,WP.block_nil ?_⟩
  refine ⟨a.v .v28,enc,?_,fun r h j => (g.gpr r h j).trans (congrFun f.gpr r),
    g.sp.trans f.sp,g.rd.trans f.rd,g.wr.trans f.wr⟩
  change b.mem.write (b.gpr .x28 + BitVec.ofNat 64 0) 16 (b.v Y ^^^ b.v .v28) = _
  simp only [g.mem,f.mem,out,BitVec.add_zero,hash,g.mask,aadLength,f.gpr]

end VG.Proof.AesGcm.AArch64.Contiguous.Tag
