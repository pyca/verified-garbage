module

import VerifiedGarbage.Proof.Dsa.X86_64.MaskContext
public import VerifiedGarbage.Proof.Dsa.X86_64.CheckFrame
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core

/-! # Returning DSA validation predicates through the parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- A verified check body returns its boolean mask to the parent and leaves
the modulus ready for the next operation. -/
theorem checkCall_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o) (hfield : 368 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (a : Operand) (ha : pointerFits a.pointer) {body : Prog isa} {accepted valid : Bool}
    (hmask : word s.mem B Field.mask.offset = mask valid)
    (run : ∀ u, SubCtx u B Z o w wx minv → ModCtx u (off B o) (slot wx 8) wx minv m →
      word u.mem B (8 * arg) = pointerValue s.mem B a.pointer →
      word u.mem B (8 * argLen) = word s.mem B a.length.offset →
      Frm B (callRanges arg argLen) s.mem u.mem → Keep coreRegs s u →
      WP isa body u fun v => SubCtx v B Z o w wx minv ∧ ModCtx v (off B o) (slot wx 8) wx minv m ∧
        v.gpr .rax = mask accepted ∧ Frm (off B o) (workRanges wx) u.mem v.mem ∧ Keep mmRegs u v) :
    WP isa (.seq (.block (Core.operand arg argLen a ++ Core.enter o))
      (.seq body (.block (([Crt.leave] : List Instr) ++ Checks.accumulate)))) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      word t.mem B Field.mask.offset = mask (accepted && valid) ∧
      RangeFrame B o wx s.mem t.mem ∧ Keep coreRegs s t := by
  have hn := hg.scr.nowrap
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ a ha (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hua, hul, hfields, hfu, hku⟩ => ?_
  have hchild := call_ready child hfu (by decide) (by decide) (by omega) (by omega)
  refine WP.mono (enter_ok hgu hchild.header hlo hhi ho) fun v ⟨hcv, hvm, hkv⟩ => ?_
  have hmv : ModCtx v (off B o) (slot wx 8) wx minv m :=
    ⟨hcv.good, by rw [hvm]; exact hchild.modulus, by rw [hvm]; exact hchild.inverse⟩
  have hks : Keep coreRegs s v := (hku.trans hkv).mono (by decide)
  have hfv : Frm B (callRanges arg argLen) s.mem v.mem := by rw [hvm]; exact hfu
  refine WP.seq (WP.mono (run v hcv hmv (by rw [hvm]; exact hua)
    (by rw [hvm]; exact hul) hfv hks) fun f ⟨hcf, hmf, hfmask, hff, hkf⟩ => ?_)
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
