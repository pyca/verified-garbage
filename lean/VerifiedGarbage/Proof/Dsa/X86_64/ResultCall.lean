module

public import VerifiedGarbage.Proof.Dsa.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import Mathlib.Tactic.Finiteness.Attr

/-! # DSA calls with a result binding and implicit modulus input -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem resultCall_ok {s : State} {B : Addr} {Z o w wx m value k : Nat}
    {minv parentMinv : BitVec 64} {body : Prog isa}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (output : Operand) (houtp : pointerFits output.pointer)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j))
    (run : ∀ u, SubCtx u B Z o w wx minv → ModCtx u (off B o) (slot wx 8) wx minv m →
      WP isa body u fun v => SubCtx v B Z o w wx minv ∧ ModCtx v (off B o) (slot wx 8) wx minv m ∧
        wv v.mem (off B o) (slot wx aY) wx = value ∧
        Frm (off B o) (workRanges wx) u.mem v.mem ∧ Keep mmRegs u v) :
    WP isa (.seq (.block (Core.operand result resultLen output ++ Core.enter o))
      (.seq body (seqs Core.finish))) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k = Spec.Dsa.encodeBE k value ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have hslot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  have hn := hg.scr.nowrap
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ output houtp (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hup, hul, _, hf, hk⟩ => ?_
  have hchild := call_ready child hf (by decide) (by decide) (by omega) (by omega)
  refine WP.mono (enter_ok hgu hchild.header hlo hhi ho) fun v ⟨hcv, hmem, hkv⟩ => ?_
  have hm : ModCtx v (off B o) (slot wx 8) wx minv m :=
    ⟨hcv.good, by rw [hmem]; exact hchild.modulus, by rw [hmem]; exact hchild.inverse⟩
  have hks : Keep coreRegs s v := (hk.trans hkv).mono (by decide)
  refine WP.mono (returnAfter_ok (parentMinv := parentMinv) hcv (run v hcv hm)
    (by rw [hmem]; exact hgu.hdr.hminv) (by rw [hmem]; exact hup) (by rw [hmem]; exact hul.trans hl)
    hk1 hk' hkw (fun j hj => by rw [hks.2.2]; exact hout j hj) hprefix)
    fun t ⟨hgt, hct, htout, _, hft, hkt⟩ => ?_
  refine ⟨hgt, hct, htout, ?_, (hks.trans hkt).mono (by decide)⟩
  intro x hx hc hxout
  rw [hft x hc hxout, hmem]
  apply (call_argument_frame hf (by decide) (by decide)) x
  intro r hr
  simp only [argumentRanges, List.mem_singleton] at hr
  subst r
  exact hx

end VG.Proof.Dsa.X86_64
