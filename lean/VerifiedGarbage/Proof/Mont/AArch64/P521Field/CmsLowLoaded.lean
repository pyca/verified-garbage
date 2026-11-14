module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsLow
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LoadWords
import VerifiedGarbage.Proof.Framework.Block

/-! The complemented low-product pass with its original operand reads. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR)
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (addWords)

def cmsLowLoaded (b : Nat) : List Instr := loadsR .x28 cmsLowIn b++cmsLowCode

theorem cms_low_loaded_words {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+64≤size) (hb8 : b%8=0) :
    WP isa (.block (cmsLowLoaded b)) s fun t =>
      cmsLowOut.map t.gpr=(addWords (cmsLowOut.map s.gpr) ((readWords s.mem p b 8).map fun x => 9 * (~~~x)) false).1 ∧
      t.c=(addWords (cmsLowOut.map s.gpr) ((readWords s.mem p b 8).map fun x => 9 * (~~~x)) false).2 ∧
      cmsLowIn.map t.gpr=(readWords s.mem p b 8).map (fun x => mulHi 9 (~~~x)) ∧
      t.gpr .x1=9 ∧ Keeps cmsLowClob s t := by
  rw [cmsLowLoaded,WP.block_append_iff]
  refine WP.mono (loadsR_each cmsLowIn hp (by simpa only [show cmsLowIn.length=8 from by decide] using hb)
    hb8 (by decide) (by decide)) fun u ⟨eu,ku,_⟩ => ?_
  simp only [show cmsLowIn.length=8 from by decide] at eu
  have ou : cmsLowOut.map u.gpr=cmsLowOut.map s.gpr := List.map_congr_left fun r h =>
    ku.gpr r ((by decide : ∀r∈cmsLowOut,r∉cmsLowIn) r h)
  refine WP.mono (cms_low_words u) fun t ⟨ot,ct,ht,k1,kt⟩ => ?_
  rw [eu,ou] at ot ct
  rw [eu] at ht
  exact ⟨ot,ct,ht,k1,(ku.mono (by decide)).trans kt⟩

end VG.Proof.Mont.AArch64.P521Field
