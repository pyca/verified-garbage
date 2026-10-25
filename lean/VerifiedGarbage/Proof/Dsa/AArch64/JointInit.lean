module
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Proof.Dsa.AArch64.JointBuildContext
public import VerifiedGarbage.Proof.Dsa.AArch64.JointWindow

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Public exponent pointers for joint DSA verification -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def jointInitRanges : List (Nat × Nat) :=
  [(8 * Crt.sExp, 8), (8 * Joint.sExp2, 8), (8 * Crt.sExpLen, 8), (8 * Crt.sI, 8)]

theorem jointInit_ranges (w : Nat) : ∀ r ∈ jointInitRanges,
    136 ≤ r.1 ∧ r.1 + r.2 ≤ 256 ∧ r.1 + r.2 ≤ slot w 8 + tabBytes w := by
  have h : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  simp only [jointInitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [Crt.sExp, Joint.sExp2, Crt.sRem, Crt.sExpLen, Crt.sI, sFn] <;> omega

/-- The memory after `expInit`. -/
def jointInitMem (m : Mem) (B : Addr) (o L : Nat) : Mem :=
  (((m.writeW (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 L)).writeW
    (off (off B o) (8 * Crt.sExp)) (off B u)).writeW
    (off (off B o) (8 * Joint.sExp2)) (off B v)).writeW
    (off (off B o) (8 * Crt.sI)) (BitVec.ofNat 64 0)

theorem jointInit_raw {s : State} {B : Addr} {Z o w wx L : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hfield : 344 ≤ Z)
    (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 L) :
    WP isa (.block Joint.expInit) s fun t =>
      t.mem = jointInitMem s.mem B o L ∧ Keep [.x3, .x4, .x5] s t := by
  have hparent : InRegions (s.rd ++ s.wr) (off B Field.qLen.offset) 8 := hc.scr.ld hfield
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [Joint.expInit, jointInitMem, hc.x0, hdr_enc (show Crt.sLink < 32 by decide),
    hdr_enc (show Crt.sExp < 32 by decide), hdr_enc (show Joint.sExp2 < 32 by decide),
    hdr_enc (show Crt.sExpLen < 32 by decide), hdr_enc (show Crt.sI < 32 by decide),
    hc.ld' (show Crt.sLink < 32 by decide), hc.link', hparent, hl,
    hc.st' (show Crt.sExp < 32 by decide), hc.st' (show Joint.sExp2 < 32 by decide),
    hc.st' (show Crt.sExpLen < 32 by decide), hc.st' (show Crt.sI < 32 by decide), off_off]
  rfl

theorem jointInit_frame {s t : State} {B : Addr} {o L : Nat}
    (hm : t.mem = jointInitMem s.mem B o L) :
    Frm (off B o) jointInitRanges s.mem t.mem := by
  rw [hm]
  exact (((Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Crt.sExpLen) (by decide))
    (by simp [jointInitRanges])).trans
    (Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Crt.sExp) (by decide))
      (by simp [jointInitRanges]))).trans
    (Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Joint.sExp2) (by decide))
      (by simp [jointInitRanges]))).trans
    (Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Crt.sI) (by decide))
      (by simp [jointInitRanges]))

theorem jointInit_ok {s : State} {B : Addr} {Z o w wx L n g y : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hmctx : JointCtx s (off B o) wx n minv)
    (htab : JointTab s.mem (off B o) wx n g y) (hfield : 344 ≤ Z)
    (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 L) :
    WP isa (.block Joint.expInit) s fun t =>
      SubCtx t B Z o w wx minv ∧ JointCtx t (off B o) wx n minv ∧
      JointTab t.mem (off B o) wx n g y ∧
      (∀ j < 8, wv t.mem (off B o) (slot wx j) wx = wv s.mem (off B o) (slot wx j) wx) ∧
      word t.mem (off B o) (8 * Crt.sExp) = off B u ∧
      word t.mem (off B o) (8 * Joint.sExp2) = off B v ∧
      word t.mem (off B o) (8 * Crt.sExpLen) = BitVec.ofNat 64 L ∧
      word t.mem (off B o) (8 * Crt.sI) = BitVec.ofNat 64 0 ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (jointInit_raw hc hfield hl) fun t ⟨hm, hk⟩ => ?_
  have hf := jointInit_frame hm
  have hnow := hc.scrT.nowrap
  have hr := jointInit_ranges wx
  have harr : ∀ j < 24, wv t.mem (off B o) (slot wx j) wx =
      wv s.mem (off B o) (slot wx j) wx := by
    intro j hj
    have lo : 256 ≤ slot wx j := by unfold slot hdrBytes; omega
    have hi : slot wx j + 8 * (wx + 2) ≤ slot wx 8 + tabBytes wx := by
      by_cases hj8 : j < 8
      · have := slot_le (w := wx) hj8; omega
      · have := ent_le wx (show j - 8 < 16 by omega)
        rw [show 8 + (j - 8) = j by omega] at this
        exact this
    exact hf.wv_eq (fun r h => Or.inr (by have := hr r h; omega)) (by omega)
  have hct := hc.of_frmT hf (fun r h => ⟨(hr r h).1, (hr r h).2.2⟩) hk.wr (hk.gpr .x0 (by decide))
  have hinv : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf.word_eq (fun r h => Or.inr (by have := hr r h; unfold slot hdrBytes; omega)) (by
      have := slot_le (w := wx) (show aN < 8 by decide); omega)]
    exact hmctx.mod.inverse
  refine ⟨hct, ⟨⟨hct.good, (harr aN (by decide)).trans hmctx.mod.modulus, hinv⟩, hct.scrT⟩,
    ⟨?_, fun j hj => (harr (8 + j) (by omega)).symm ▸ htab.lt j hj,
      fun j hj => (harr (8 + j) (by omega)).symm ▸ htab.val j hj⟩,
    fun j hj => harr j (by omega), ?_, ?_, ?_, ?_, ?_, hk.mono (by decide)⟩
  · rw [hf.word_eq (by simp [jointInitRanges, Crt.sExp, Joint.sExp2, Crt.sRem, Crt.sExpLen,
      Crt.sI, Crt.sTab, sFn]) (by decide)]
    exact htab.tab
  · rw [hm, jointInitMem]
    simp (disch := decide) only [hdrStore_hdr, word_writeW_self]
  · rw [hm, jointInitMem]
    simp (disch := decide) only [hdrStore_hdr, word_writeW_self]
  · rw [hm, jointInitMem]
    simp (disch := decide) only [hdrStore_hdr, word_writeW_self]
  · rw [hm, jointInitMem, word_writeW_self]
  · intro x hx
    apply hf x
    intro r h
    have := hr r h
    have := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
    have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
    omega

end VG.Proof.Dsa.AArch64
