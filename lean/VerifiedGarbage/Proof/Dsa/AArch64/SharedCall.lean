module
public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Dsa.AArch64.Call
public import VerifiedGarbage.Proof.Dsa.AArch64.Return
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCalls
public import VerifiedGarbage.Proof.Dsa.AArch64.CheckEffects
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.AArch64.SharedPowerCT
import VerifiedGarbage.Proof.Dsa.AArch64.MaskContext
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.Finish
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract

/-! # The shared exponentiation as a call from the parent workspace

`SharedPower.pow` binds its operands, enters the workspace of `p`, computes
`g^x` and the mask of `g^q = 1`, writes `g^x` out, returns to the parent
workspace, and there takes the mask into the acceptance mask. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Proof.Dsa.AArch64

/-- The call up to its return: besides what `call3_ok` says of it, the mask
of `g^q = 1` is in the child's `sMaskX`, and the acceptance mask is as it was. -/
theorem powCall_ok (M : Mont) {s : State} {B : Addr} {Z w wx m k : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B pWorkspace wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ pWorkspace) (hhi : pWorkspace + slot wx 8 + tabBytes wx ≤ Z)
    (hw8 : 8 ≤ wx) (hw48 : wx ≤ 48) (hd8 : wx % 8 = 0) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb qb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (hqs : Src s B Z (word s.mem B Field.q.offset) qb) (hql : qb.length = bb.length)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx) (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (seqs (([.block (Core.operand arg argLen a ++ Core.operand arg2 arg2Len b ++
      Core.operand result resultLen output ++ Core.enter pWorkspace), SharedPower.power M.mm] : List (Prog isa)) ++
        Core.finish)) s fun t =>
      (Good t B Z w parentMinv ∧ ChildReady t.mem B pWorkspace wx m minv ∧
        Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
          Spec.Dsa.encodeBE k (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) m) ∧
        CallFrame B pWorkspace wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t) ∧
      word t.mem B (pWorkspace + 8 * Crt.sMaskX) =
        mask (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE qb) m = 1)) ∧
      word t.mem B Field.mask.offset = word s.mem B Field.mask.offset := by
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  have hslot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hn := hg.scr.nowrap
  have hqo : Field.q.offset = 264 := rfl
  have hmo : Field.mask.offset = 360 := rfl
  have hpw : pWorkspace = 3456 := rfl
  have hsm : Crt.sMaskX = 24 := rfl
  -- What the body gives, at any state the call's head leaves.
  have body : ∀ u, SubCtx u B Z pWorkspace w wx minv → ChildReady u.mem B pWorkspace wx m minv →
      Arguments u.mem s.mem B a b output → Frm B argumentRanges s.mem u.mem → Keep coreRegs s u →
      WP isa (SharedPower.power M.mm) u fun v => SubCtx v B Z pWorkspace w wx minv ∧
        wv v.mem (off B pWorkspace) (slot wx aY) wx =
          Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) m ∧
        word v.mem (off B pWorkspace) (8 * Crt.sMaskX) =
          mask (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE qb) m = 1)) ∧
        ModCtx v (off B pWorkspace) (slot wx 8) wx minv m ∧
        Frm (off B pWorkspace) (workRanges wx) u.mem v.mem ∧ Keep mmRegs u v := by
    intro u hc hchild hargs hf hk
    have hqu : word u.mem B Field.q.offset = word s.mem B Field.q.offset :=
      hf.word_eq (fun r hr => by
        simp only [argumentRanges, List.mem_singleton] at hr; subst hr; right; omega_using [hqo])
        (by omega_using [hqo])
    exact power_ok M hc hw8 hw48 hd8 hwx hw30 hm hodd hchild.modulus hchild.inverse
      hargs.1 (hargs.2.1.trans has.length) (arguments_source hf hk hz has.source) ha1 haw
      hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hf hk hz hbs.source) hb1 hb2
      hqu (arguments_source hf hk hz hqs) hql
  refine wp_and (call3_ok hg child hZ hlo hhi (by decide) a b output ha hb houtp hl hk1 hk' hkw hout hprefix
    fun u hc hchild hargs hf hk => WP.mono (body u hc hchild hargs hf hk)
      fun v ⟨hcv, hv, _, hmv, hfv, hkv⟩ => ⟨hcv, hmv, hv, hfv, hkv⟩) ?_
  -- The same run again, for the two words.
  change WP isa (.seq (.block _) (.seq (SharedPower.power M.mm) (seqs Core.finish))) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (arguments_ok hg child hZ (by omega_using [hlo, hslot]) (by omega_using [hhi]) a b output ha hb houtp)
    fun u ⟨hgu, hchild, hargs, hfields, hf, hk⟩ => ?_
  refine WP.mono (enter_ok hgu hchild.header hlo hhi (by decide)) fun v ⟨hcv, hmem, hkv⟩ => ?_
  have hfv : Frm B argumentRanges s.mem v.mem := by rw [hmem]; exact hf
  have hav : Arguments v.mem s.mem B a b output := by rw [hmem]; exact hargs
  have hchv : ChildReady v.mem B pWorkspace wx m minv := by rw [hmem]; exact hchild
  have hks : Keep coreRegs s v := (hk.trans hkv).mono (by decide)
  refine WP.seq (WP.mono (body v hcv hchv hav hfv hks) fun z ⟨hcz, _, hmaskz, _, hfz, hkz⟩ => ?_)
  refine WP.mono (finish_ok (parentMinv := parentMinv) hcz
    ((work_parent hcv hfz (by decide)).trans (by rw [hmem]; exact hgu.hdr.hminv))
    ((work_parent hcv hfz (by decide)).trans hav.2.2.2.2.1)
    ((work_parent hcv hfz (by decide)).trans (hav.2.2.2.2.2.trans hl)) hk1 hk' hkw
    (fun j hj => by rw [hkz.wr, hks.wr]; exact hout j hj) hprefix) fun y ⟨_, _, hyword, _, _⟩ => ⟨?_, ?_⟩
  · rw [hyword _ (by omega_using [hhi, h256, hpw, hsm]), ← word_off]
    exact hmaskz
  · rw [hyword _ (by omega_using [hZ, hmo, hpw]),
      hfz.word_below (fun r hr => (workRanges_ok wx r hr).2) (by omega_using [hn, hhi]) (by omega_using [hpw])
        (by omega_using [hmo, hpw]), hmem]
    exact hfields .mask

/-- The whole call, in DSA's execution context: `g^x` at the local `d`, and
`g^q = 1` in the acceptance mask. -/
theorem readySharedPow_ok (M : Mont) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (hm : 1 < L.modulus) (hodd : L.modulus % 2 = 1)
    (a b : Operand) {ba bb qb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (hqs : Src s L.base activeBytes (word s.mem L.base Field.q.offset) qb) (hql : qb.length = bb.length)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ L.pWords)
    (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + L.pLen ≤ usedBytes)
    {valid : Bool} (hmask : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (SharedPower.pow M.mm a b ⟨.local d, .pLen⟩) s fun t => ∃ u,
      CallResult L .p d (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) L.modulus) s u ∧
      CheckEffect L (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE qb) L.modulus = 1) && valid)
        u t := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := ModulusSide.p.bounds L
  have hw8 : 8 ≤ L.pWords ∧ L.pWords % 8 = 0 := by
    rcases L.lengths with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [ExecutionLayout.pWords, h1] <;> decide
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 16
    have : usedBytes < 2 ^ 16 := by decide
    omega_using [hend, this]
  unfold SharedPower.pow
  refine wp_seqs_append (by simp) (by simp) (WP.mono (powCall_ok M h.parent (h.child .p) (by decide) hlo hhi
    hw8.1 hw48 hw8.2 hw48 (by decide) hm hodd a b ⟨.local d, .pLen⟩ ha hb hdp has hbs hqs hql ha1 haw hb1 hb2
    (h.length .p) hk1 hk31 rfl (h.local_write hend) (h.local_out hd hend)) ?_)
  intro u ⟨⟨hp, hc, hv, hf, hk⟩, hq1, hmu⟩
  have hru : Ready L u := h.afterCall .p hp hc hf hk hd hend
  change WP isa (.block _) u _
  rw [WP.block_append_iff]
  have hx0 := hp.x0
  have hld := hp.scr.ld (d := pWorkspace + 8 * Crt.sMaskX) (by decide)
  refine WP.mono (WP.keep [.x3] (Q := fun v => v.gpr .x3 = word u.mem L.base (pWorkspace + 8 * Crt.sMaskX) ∧
    v.mem = u.mem) (by brun [hx0, hld]) rfl rfl rfl) fun v ⟨⟨h3, hvm⟩, hkv⟩ => ?_
  have hgv : Good v L.base activeBytes outerWords 0 :=
    ⟨hp.scr.congr hkv.wr, (hkv.gpr .x0 (by decide)).trans hp.x0, hvm ▸ hp.hdr⟩
  have hrv : Ready L v := ⟨hgv, hru.scratch.congr hkv.wr, by rw [hvm]; exact hru.fields,
    by rw [hvm]; exact hru.pChild, by rw [hvm]; exact hru.qChild⟩
  refine WP.mono (accumulate_context (a := decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE qb)
      L.modulus = 1)) (b := valid) hgv hrv.pChild (by decide) (by decide)
      (Nat.le_trans (Nat.le_add_right _ _) hhi) (h3.trans hq1) (by rw [hvm]; exact hmu.trans hmask))
    fun t ⟨hgt, _, hmt, hft, hkt⟩ => ?_
  have hkc : Keep coreRegs v t := hkt.mono (by decide)
  have hkuv : Keep coreRegs u v := hkv.mono (by decide)
  have hfu : Outside L.base Field.mask.offset 8 u.mem t.mem := by rw [← hvm]; exact hft
  exact ⟨u, ⟨hru, hv, hf, hk⟩, hrv.afterMask hgt hft hkc, hmt,
    hfu.mono (by decide) (by decide), (hkuv.trans hkc).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.SharedPower
