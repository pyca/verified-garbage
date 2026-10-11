import VerifiedGarbage.Proof.Dsa.X86_64.LoadRange
import VerifiedGarbage.Proof.Dsa.X86_64.MaskContext
import VerifiedGarbage.Proof.Dsa.X86_64.CallHeader

/-! # DSA range validation through the parent calling convention -/
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def RangeFrame (B : Addr) (o wx : Nat) (mem mem' : Mem) : Prop :=
  ∀ x, (∀ r ∈ callRanges arg argLen, ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x) →
    (∀ r ∈ workRanges wx, ofs (off B o) x < r.1 ∨ r.1 + r.2 ≤ ofs (off B o) x) →
    (ofs B x < Field.mask.offset ∨ Field.mask.offset + 8 ≤ ofs B x) → mem' x = mem x

/-- Range validation always completes the same load and scans, then combines
its result with the existing mask and returns to the parent workspace. -/
theorem range_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o) (hfield : 368 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z (pointerValue s.mem B a.pointer) bytes)
    (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx)
    (aboveOne : Bool) {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.range o a aboveOne) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      word t.mem B Field.mask.offset = mask (decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧
        Spec.Dsa.decodeBE bytes < m) && valid) ∧
      RangeFrame B o wx s.mem t.mem ∧ Keep coreRegs s t := by
  have hn := hg.scr.nowrap
  unfold Checks.range seqs
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ a ha (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hua, hul, hfields, hfu, hku⟩ => ?_
  have hchild := call_ready child hfu (by decide) (by decide) (by omega) (by omega)
  have hsrcu := call_source hfu hku (by decide) (by decide) (Nat.le_trans (by decide) hZ) hsrc
  refine WP.mono (enter_ok hgu hchild.header hlo hhi ho) fun v ⟨hcv, hvm, hkv⟩ => ?_
  have hmv : ModCtx v (off B o) (slot wx 8) wx minv m :=
    ⟨hcv.good, by rw [hvm]; exact hchild.modulus, by rw [hvm]; exact hchild.inverse⟩
  have hsv : Src v B Z (pointerValue s.mem B a.pointer) bytes :=
    hsrcu.congr (by rw [hvm]; exact InScr.refl _ _ _) hkv.2.1 hkv.2.2
  have run := loadRange_ok (sp := arg) (sl := argLen) hcv hmv hw2 hw48 hwx hw30 (by decide) (by decide)
    (by rw [hvm]; exact hua) (by rw [hvm]; exact hul.trans hlen) hsv h1 hfit aboveOne
  refine WP.seq (WP.mono (WP.seq_iff.mp run) fun z hz => WP.seq (WP.mono hz fun f ⟨hcf, hmf, hfmask, hff, hkf⟩ => ?_))
  change WP isa (.block ([Crt.leave] ++ Checks.accumulate)) f _
  rw [WP.block_append_iff]
  have hpm : word f.mem B (8 * sMinv) = parentMinv :=
    (work_parent hcv hff (by decide)).trans (by rw [hvm]; exact hgu.hdr.hminv)
  have hmaskf : word f.mem B Field.mask.offset = mask valid := by
    rw [hff.word_below (fun r hr => (workRanges_ok wx r hr).2) (by omega) (by omega)
      (show Field.mask.offset + 8 ≤ o from hfield), hvm, hfields .mask]
    exact hmask
  refine WP.mono (leave_ok hcf hpm) fun l ⟨hgl, hlm, hkl⟩ => ?_
  have hcl : ChildReady l.mem B o wx m minv :=
    ⟨by rw [hlm]; exact ⟨hcf.hdr, hcf.link⟩, by rw [hlm]; exact hmf.modulus,
      by rw [hlm]; exact hmf.inverse⟩
  refine WP.mono (accumulate_context (b := valid) hgl hcl hZ hfield (by omega)
    ((hkl.gpr (by decide)).trans hfmask) (by rw [hlm]; exact hmaskf))
    fun t ⟨hgt, hct, htmask, hft, hkt⟩ => ?_
  refine ⟨hgt, hct, htmask, ?_, ((((hku.trans hkv).trans hkf).trans hkl).trans hkt).mono (by decide)⟩
  intro x hxarg hxwork hxmask
  rw [hft x hxmask, hlm]
  exact (hff x hxwork).trans (by rw [hvm]; exact hfu x hxarg)

end VG.Proof.Dsa.X86_64
