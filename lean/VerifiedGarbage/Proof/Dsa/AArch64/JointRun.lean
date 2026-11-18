module

public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Proof.Dsa.AArch64.JointBuildContext
public import VerifiedGarbage.Proof.Dsa.AArch64.JointWindow
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.JointByte
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Dsa.AArch64.JointInit`, which this module and modules that import it used -/

section

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
  have h : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  simp only [jointInitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [Crt.sExp, Joint.sExp2, Crt.sRem, Crt.sExpLen, Crt.sI, sFn] <;> omega_using [h]

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
    have lo : 256 ≤ slot wx j := by unfold slot hdrBytes; omega_using []
    have hi : slot wx j + 8 * (wx + 2) ≤ slot wx 8 + tabBytes wx := by
      by_cases hj8 : j < 8
      · have := slot_le (w := wx) hj8; omega_using [this]
      · have := ent_le wx (show j - 8 < 16 by omega_using [hj])
        rw [show 8 + (j - 8) = j by omega_using [hj8]] at this
        exact this
    exact hf.wv_eq (fun r h => Or.inr (by have := hr r h; omega_using [lo, this])) (by omega_using [hnow, hi])
  have hct := hc.of_frmT hf (fun r h => ⟨(hr r h).1, (hr r h).2.2⟩) hk.wr (hk.gpr .x0 (by decide))
  have hinv : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf.word_eq (fun r h => Or.inr (by have := hr r h; unfold slot hdrBytes; omega_using [this])) (by
      have := slot_le (w := wx) (show aN < 8 by decide); omega_using [hnow, this])]
    exact hmctx.mod.inverse
  refine ⟨hct, ⟨⟨hct.good, (harr aN (by decide)).trans hmctx.mod.modulus, hinv⟩, hct.scrT⟩,
    ⟨?_, fun j hj => (harr (8 + j) (by omega_using [hj])).symm ▸ htab.lt j hj,
      fun j hj => (harr (8 + j) (by omega_using [hj])).symm ▸ htab.val j hj⟩,
    fun j hj => harr j (by omega_using [hj]), ?_, ?_, ?_, ?_, ?_, hk.mono (by decide)⟩
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
    have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
    omega_arith

end VG.Proof.Dsa.AArch64

end

end

/-! # Joint exponentiation and conversion out of Montgomery representation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem joint_source_out {s : State} {B p : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {bs : List Byte} (hs : Src s B Z p bs) :
    ∀ i < bs.length, slot wx 8 + tabBytes wx ≤ ofs (off B o) (p + BitVec.ofNat 64 i) := by
  intro i hi
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have := hc.hi
  have := hc.scr.nowrap
  have := hs.out i hi
  rcases ofs_rebase B (p + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega_arith

theorem jointRun_ok (M : Mont) {s : State} {B : Addr} {Z o w wx n g y : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hmctx : JointCtx s (off B o) wx n minv)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hn : 1 < n) (hodd : n % 2 = 1)
    (htab : JointTab s.mem (off B o) wx n g y)
    (hy : wv s.mem (off B o) (slot wx aY) wx = 2 ^ (64 * wx) % n)
    (hone : wv s.mem (off B o) (slot wx aOne) wx = 1)
    {eb fb : List Byte} (he : Src s B Z (off B u) eb) (hf : Src s B Z (off B v) fb)
    (hlen : fb.length = eb.length) (hL0 : 0 < eb.length) (hL' : eb.length < 2 ^ 31)
    (hfield : 344 ≤ Z) (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length) :
    WP isa (Joint.run M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv n ∧
      wv t.mem (off B o) (slot wx aY) wx =
        (g ^ Spec.Dsa.decodeBE eb * y ^ Spec.Dsa.decodeBE fb) % n ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Joint.run seqs
  refine WP.seq (WP.mono (jointInit_ok hc hmctx htab hfield hl)
    fun s1 ⟨hc1, hm1, ht1, ha1, he1, hf1, hl1, hi1, hfrm1, hk1⟩ => ?_)
  have hsrc1 := work_source hc hfrm1 hk1 he
  have fsrc1 := work_source hc hfrm1 hk1 hf
  have hy1 := (ha1 aY (by decide)).trans hy
  have ho1 := (ha1 aOne (by decide)).trans hone
  have hR := coprime_pow2 hodd (64 * wx)
  have hI : JointByteInv s1 (off B o) wx minv n
      (wv s1.mem (off B o) (slot wx Crt.aXc) wx) g y (off B u) (off B v)
      eb.length eb fb 0 s1 := by
    refine ⟨hm1.exp, ht1, ?_, ?_, hi1, he1, hf1, hl1, Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hy1]; exact Nat.mod_lt _ (by omega_using [hn])
    · rw [hy1, Nat.mod_mod, pre_zero, pre_zero, Nat.pow_zero, Nat.pow_zero, Nat.one_mul]
  refine WP.seq (WP.mono (jointBytes_ok M hw hw' hR rfl hlen hL0 hL'
    hsrc1.rd hsrc1.val (joint_source_out hc1 hsrc1)
    (by simpa only [hlen] using fsrc1.rd) (by simpa only [hlen] using fsrc1.val)
    (by simpa only [hlen] using joint_source_out hc1 fsrc1) hI) fun s2 h2 => ?_)
  have hc2 := hc1.of_frmT h2.frm (crtExpRanges_ok wx) h2.keep.wr (h2.keep.gpr .x0 (by decide))
  have hm2 : ModCtx s2 (off B o) (slot wx 8) wx minv n := ⟨h2.ctx.good, h2.ctx.n, h2.ctx.inv⟩
  have hnow := hc1.good.scr.nowrap
  have honeSep := crtExpRanges_arr wx (j := aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
  have honeSlot := slot_le (w := wx) (show aOne < 8 by decide)
  have ho2 : wv s2.mem (off B o) (slot wx aOne) wx = 1 :=
    (h2.frm.wv_eq (fun r h => by have := honeSep r h; omega_using [this]) (by omega_using [hnow, honeSlot])).trans ho1
  refine WP.mono (mont_step M hm2 (Nat.le_refl _) hw (by omega_using [hw']) (by unfold MmUse; decide)
    (by rw [ho2]; exact hn)) fun t ⟨hmt, hlt, hv, hft, hkt⟩ => ?_
  have hv2 := h2.val
  rw [← hlen, pre_len] at hv2
  rw [hlen, pre_len] at hv2
  rw [ho2] at hv
  have hresult := VG.Proof.Dsa.mont_decode hR hv2 hv
  rw [Nat.mod_eq_of_lt hlt] at hresult
  refine ⟨arrays_context hc2 hft (by decide) hkt, hmt, ?_,
    (hfrm1.trans (exp_work h2.frm)).trans (arrays_work hft (by decide)),
    ((hk1.trans h2.keep).trans hkt).mono (by decide)⟩
  simpa only [VG.Proof.Dsa.decodeBE_os2ip] using hresult

end VG.Proof.Dsa.AArch64
