import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup

namespace VG.Proof.Bignum.X86_64.AdxHeader
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

def highPad (w : Nat) := slot w aAcc+16+16*w

theorem pads_bound {w Z : Nat} (hZ : slot w 8 ≤ Z) :
    slot w aAcc+16 ≤ highPad w ∧ highPad w+16 ≤ Z := by
  have := slot_le (w := w) (show aTmp < 8 by decide)
  unfold highPad slot aAcc aTmp at *; omega

theorem bases_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block AdxHeader.bases) s fun t =>
      t.gpr .r8 = off B (slot w aAcc) ∧ t.gpr .r9 = off B (highPad w) ∧
      t.mem = s.mem ∧ Keep [.r8,.r9] s t := by
  have hl : ∀ k < 32, InRegions (s.rd ++ s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega)
  have sh : BitVec.ofNat 64 w <<< (4 : Nat) = BitVec.ofNat 64 (16*w) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 w * BitVec.ofNat 64 16 = BitVec.ofNat 64 (16*w)
    rw [← BitVec.ofNat_mul,Nat.mul_comm]
  refine WP.mono (WP.keep [.r8,.r9] (Q := fun t =>
    t.gpr .r8 = off B (slot w aAcc) ∧ t.gpr .r9 = off B (highPad w) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨a,b,c⟩,k⟩ => ⟨a,b,c,k⟩
  unfold AdxHeader.bases
  xrun [State.ea,hdr,hd,hdrOff,hl (sArr aAcc) (by decide),hl sW (by decide),
    hh.harr aAcc (by decide),hh.hw,sh,show (16 : BitVec 32).signExtend 64 = 16 from rfl]
  simp only [highPad,off,BitVec.ofNat_add]
  rw [BitVec.add_comm (BitVec.ofNat 64 (16*w)),BitVec.add_assoc,BitVec.add_assoc]
  congr 1
  rw [BitVec.add_comm (BitVec.ofNat 64 (16*w))]
  simp only [BitVec.add_assoc]
  rfl

theorem save_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi) (hZ : slot w 8 ≤ Z) :
    WP isa AdxHeader.save s fun t =>
      (∀ q < 2, word t.mem B (slot w aAcc+8*q) = word s.mem B (8*sFn 12+8*q)) ∧
      (∀ q < 2, word t.mem B (highPad w+8*q) = word s.mem B (8*sFn 14+8*q)) ∧
      Frm B [(slot w aAcc,16),(highPad w,16)] s.mem t.mem ∧ Keep [.rax,.r8,.r9] s t := by
  have nowrap := hs.nowrap
  have pads := pads_bound hZ
  have head : hdrBytes ≤ slot w aAcc := by unfold slot; omega
  unfold AdxHeader.save
  refine WP.seq (WP.mono (bases_ok hs hd hh hZ) fun a ⟨lo,hi,ma,ka⟩ => ?_)
  have da : a.gpr .rdi = off B 0 := by
    rw [show off B 0 = B from BitVec.add_zero B]
    exact (ka.gpr (by decide)).trans hd
  refine WP.seq (WP.mono (copyPair_ok (hs.congr ka.2.2) da lo (by decide) (by decide)
    (by unfold sFn hdrBytes at *; omega) (by omega) (by unfold sFn hdrBytes at *; omega))
    fun b ⟨vb,ob,kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.mono (copyPair_ok (hs.congr kab.2.2) ((kb.gpr (by decide)).trans da)
    ((kb.gpr (by decide)).trans hi) (by decide) (by decide)
    (by unfold sFn hdrBytes at *; omega) (by omega) (by unfold sFn hdrBytes at *; omega))
    fun t ⟨vt,ot,kt⟩ => ?_
  simp only [Nat.add_zero,Nat.zero_add] at vb ob vt ot
  rw [ma] at vb ob
  refine ⟨?_,?_,(Frm.of_outside ob (by simp)).trans (Frm.of_outside ot (by simp)),
    (kab.trans kt).mono (by simp)⟩
  · intro q hq
    rw [ot.word (by omega) (by omega)]; exact vb q hq
  · intro q hq
    rw [vt q hq,ob.word (by unfold sFn hdrBytes at *; omega) (by unfold sFn; omega)]

end VG.Proof.Bignum.X86_64.AdxHeader
