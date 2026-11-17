module

public import VerifiedGarbage.Proof.Dsa.AArch64.InitFrame
public import VerifiedGarbage.Impl.Dsa.AArch64.Workspace
import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
public import VerifiedGarbage.Proof.Dsa.AArch64.InitInverse
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Load

/-! ### `Dsa.AArch64.SealChild`, which only this module used -/

section

/-! # Finishing a child modulus and returning a reusable workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem sealChild_ok {s : State} {B : Addr} {Z o w wx m : Nat} {oldMinv parentMinv : BitVec 64}
    (hc : SubCtx s B Z o w wx oldMinv)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m) (hw : 1 ≤ wx) (hodd : m % 2 = 1)
    (hpm : word s.mem B (8 * sMinv) = parentMinv) :
    WP isa (.block (initInverse ++ [Crt.leave])) s fun t => ∃ mi : BitVec 64,
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m mi ∧
      Outside (off B o) (8 * sMinv) 8 s.mem t.mem ∧ Keep coreRegs s t := by
  have hi := hc.hi
  have hlo := hc.lo
  have hroot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  have hslot : 256 ≤ slot wx aN := by unfold slot hdrBytes; omega_using []
  have hN := slot_le (w := wx) (show aN < 8 by decide)
  have hodd' : (word s.mem (off B o) (slot wx aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ hw, hn, Nat.mod_mod_of_dvd _ (by decide)]
    exact hodd
  rw [WP.block_append_iff]
  refine WP.mono (initInverse_ok hc.good (Nat.le_refl _) hodd')
    fun u ⟨mi, hgu, hinv, hfu, hku⟩ => ?_
  have hff : Frm (off B o) [(8 * sMinv, 8)] s.mem u.mem := Frm.of_outside hfu (by simp)
  have hb : ∀ i < 32, word u.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi'
    exact hff.word_below (L := 64) (by intro r hr; rw [List.mem_singleton.mp hr]; decide)
      (by have := hc.scr.nowrap; omega_using [hi, hslot, hN, this]) (by have := hc.scr.nowrap; omega_using [hi, hN, this]) (by omega_using [hlo, hroot, hi'])
  have hcu : SubCtx u B Z o w wx mi :=
    ⟨hc.scr.congr hku.wr, hgu.x0, hgu.hdr,
      (hfu.word (Or.inr (by decide)) (by decide)).trans hc.link,
      (hb _ (by decide)).trans hc.nw,
      fun j hj => (hb _ (by unfold sArr; omega_using [hj])).trans (hc.narr j hj), hlo, hi⟩
  have hun : wv u.mem (off B o) (slot wx aN) wx = m := by
    rw [hfu.wv (Or.inr (by change 64 ≤ slot wx aN; omega_using [hslot])) (by have := hc.good.scr.nowrap; omega_using [hN, this])]
    exact hn
  have hui : ((word u.mem (off B o) (slot wx aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfu.word (Or.inr (by change 64 ≤ slot wx aN; omega_using [hslot])) (by have := hc.good.scr.nowrap; omega_using [hN, this])]
    exact hinv
  refine WP.mono (leave_ok hcu ((hb _ (by decide)).trans hpm)) fun t ⟨hgt, htm, hkt⟩ => ?_
  exact ⟨mi, hgt, ⟨by rw [htm]; exact ⟨hcu.hdr, hcu.link⟩,
    by rw [htm]; exact hun, by rw [htm]; exact hui⟩,
    by rw [htm]; exact hfu, (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Complete initialization of one DSA Montgomery workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem child_ok {s : State} {B p : Addr} {Z o w wx : Nat} {parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (hZ : pWorkspace ≤ Z)
    (ho : o < 2 ^ 16) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ Z)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hp : pointerValue s.mem B a.pointer = p)
    (hl : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z p bytes) (hk1 : 1 ≤ bytes.length) (hk31 : bytes.length < 2 ^ 31)
    (hkw : wx = (bytes.length + 7) / 8) (hodd : Spec.Dsa.decodeBE bytes % 2 = 1) :
    WP isa (SignVerify.child o a) s fun t => ∃ mi : BitVec 64,
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx (Spec.Dsa.decodeBE bytes) mi ∧
      Frm B (initRanges o wx) s.mem t.mem ∧ Keep coreRegs s t := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hroot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  have hbound : o + slot wx 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega_using [hhi, this]
  have hhead : 144 ≤ Z := Nat.le_trans (by decide) hZ
  unfold SignVerify.child seqs
  refine WP.seq ?_
  simp only [List.append_assoc]
  change WP isa (.block (Core.operand arg argLen a ++ (childCount o ++ childBases))) s _
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ a ha (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hup, hul, _, hfu, hku⟩ => ?_
  have hfui : Frm B (initRanges o wx) s.mem u.mem := init_call_frame hfu
  have husrc := init_source hfui hku hhead (by omega_using [hhi]) hsrc
  have hul' : word u.mem B (8 * argLen) = BitVec.ofNat 64 bytes.length := hul.trans hl
  refine WP.mono (newChild_ok hgu hZ ho (by omega_using [hk31]) hul' hlo (by rw [← hkw]; exact hhi))
    fun v ⟨oldMi, hcv, hfv, hkv⟩ => ?_
  rw [← hkw] at hcv
  have hfvi : Frm B (initRanges o wx) u.mem v.mem := init_child_frame hfv (by omega_using [hslot]) hbound
  have hfs := hfui.trans hfvi
  have hks := hku.trans hkv
  have hvsrc := init_source hfs hks hhead (by omega_using [hhi]) hsrc
  have hvword : ∀ i < 32, word v.mem B (8 * i) = word u.mem B (8 * i) := by
    intro i hi
    have hff : Frm (off B o) [(48, 88)] u.mem v.mem := Frm.of_outside hfv (by simp)
    exact hff.word_below (L := 136) (by intro r hr; rw [List.mem_singleton.mp hr]; decide)
      (by omega_using [ho]) (by omega_using [ho]) (by omega_using [hlo, hroot, hi])
  refine WP.seq (WP.mono (load_ok hcv hw2 hwx hw30 (j := aN) (by decide) (by decide) (by decide)
    ((hvword _ (by decide)).trans (hup.trans hp)) ((hvword _ (by decide)).trans hul')
    hvsrc hk1 hk31 (by omega_using [hkw])) fun z ⟨hcz, hzn, hfz, hkz⟩ => ?_)
  have hfzi : Frm B (initRanges o wx) v.mem z.mem :=
    init_child_frame hfz (slot_le (w := wx) (show aN < 8 by decide)) hbound
  have hfsz := hfs.trans hfzi
  have hpmz : word z.mem B (8 * sMinv) = parentMinv :=
    (init_word hfsz (by change 64 ≤ o; omega_using [hlo, hroot]) (Or.inl (by decide)) (by omega_using [ho])).trans hg.hdr.hminv
  have hcode : ([ldh .x3 (sArr aN), ld .x3 .x3] ++ (minv ++
      [sth .x15 sMinv, Crt.leave]) : List Instr) = initInverse ++ [Crt.leave] := by
    simp only [initInverse, List.append_assoc, List.cons_append, List.nil_append]
  change WP isa (.block _) z _
  rw [hcode]
  refine WP.mono (sealChild_ok hcz hzn (by omega_using [hw2]) hodd hpmz)
    fun t ⟨mi, hgt, hready, hft, hkt⟩ => ?_
  have hfti : Frm B (initRanges o wx) z.mem t.mem :=
    init_child_frame hft (by change 64 ≤ slot wx 8; omega_using [hslot]) hbound
  exact ⟨mi, hgt, hready, hfsz.trans hfti, ((hks.trans hkz).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
