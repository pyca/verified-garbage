module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxHeader
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory

/-! ### `Bignum.X86_64.AdxHeaderCopy`, which this module and modules that import it used -/

section

/-! Scalar copies preserve every byte outside their destination. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxHeader
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.MlKem.X86_64 (Keep)

theorem copyWord_ok {s : State} {B : Addr} {Z e d o : Nat} {src : MemOp} {dst : Reg}
    (hs : Scr s B Z) (he : s.ea src = off B e) (hd : s.gpr dst = off B d)
    (hne : dst ≠ .rax) (hE : e+8 ≤ Z) (hD : d+o+8 ≤ Z) :
    WP isa (AdxHeader.copyWord src dst o) s fun t =>
      word t.mem B (d+o) = word s.mem B e ∧ Outside B (d+o) 8 s.mem t.mem ∧ Keep [.rax] s t := by
  unfold AdxHeader.copyWord
  refine WP.seq (WP.mono (movMem_ok s (dst := .rax) (readSrc_word hs he hE))
    fun a ⟨va,_,_,ka⟩ => ?_)
  refine WP.mono (storeAt_ok (hs.congr ka.2.2.2) ((ka.gpr (by simpa)).trans hd) hD)
    fun t ⟨vt,ot,kt⟩ => ?_
  rw [ka.2.1] at ot
  exact ⟨vt.trans va,ot,(ka.keep.trans kt).mono (by simp)⟩

theorem copyPair_ok {s : State} {B : Addr} {Z e d a o : Nat} {src dst : Reg}
    (hs : Scr s B Z) (he : s.gpr src = off B e) (hd : s.gpr dst = off B d)
    (hsne : src ≠ .rax) (hdne : dst ≠ .rax) (hE : e+a+16 ≤ Z) (hD : d+o+16 ≤ Z)
    (hsep : e+a+16 ≤ d+o ∨ d+o+16 ≤ e+a) :
    WP isa (AdxHeader.copyPair src dst a o) s fun t =>
      (∀ q < 2, word t.mem B (d+o+8*q) = word s.mem B (e+a+8*q)) ∧
      Outside B (d+o) 16 s.mem t.mem ∧ Keep [.rax] s t := by
  have nowrap := hs.nowrap
  unfold AdxHeader.copyPair
  refine WP.seq (WP.mono (copyWord_ok hs (ea_at he a) hd hdne (by omega_using [hE]) (by omega_using [hD]))
    fun u ⟨vu,ou,ku⟩ => ?_)
  refine WP.mono (copyWord_ok (hs.congr ku.2.2)
    (ea_at ((ku.gpr (by simpa)).trans he) (a+8)) ((ku.gpr (by simpa)).trans hd)
    hdne (by omega_using [hE]) (by omega_using [hD])) fun t ⟨vt,ot,kt⟩ => ?_
  have hi : word u.mem B (e+(a+8)) = word s.mem B (e+(a+8)) := ou.word (by omega_using [hsep]) (by omega_using [hE, nowrap])
  rw [hi] at vt
  refine ⟨?_,(ou.mono (o' := d+o) (n' := 16) (by omega_using []) (by omega_using [])).trans
    (ot.mono (o' := d+o) (n' := 16) (by omega_using []) (by omega_using [])),(ku.trans kt).mono (by simp)⟩
  intro q hq
  rcases (show q=0 ∨ q=1 by omega_using [hq]) with rfl | rfl
  · simp only [Nat.mul_zero,Nat.add_zero]
    rw [ot.word (by omega_using []) (by omega_using [hD, nowrap])]; exact vu
  · simpa only [Nat.mul_one,Nat.add_assoc] using vt

end VG.Proof.Bignum.X86_64.AdxHeader

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxHeader
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

def highPad (w : Nat) := slot w aAcc+16+16*w

theorem pads_bound {w Z : Nat} (hZ : slot w 8 ≤ Z) :
    slot w aAcc+16 ≤ highPad w ∧ highPad w+16 ≤ Z := by
  have := slot_le (w := w) (show aTmp < 8 by decide)
  unfold highPad slot aAcc aTmp at *; omega_using [hZ]

theorem bases_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block AdxHeader.bases) s fun t =>
      t.gpr .r8 = off B (slot w aAcc) ∧ t.gpr .r9 = off B (highPad w) ∧
      t.mem = s.mem ∧ Keep [.r8,.r9] s t := by
  have hl : ∀ k < 32, InRegions (s.rd ++ s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega_using [hZ, this])
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
  refine congrArg (fun x : BitVec 64 => B + x) ?_
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
  have head : hdrBytes ≤ slot w aAcc := by unfold slot; omega_using []
  unfold AdxHeader.save
  refine WP.seq (WP.mono (bases_ok hs hd hh hZ) fun a ⟨lo,hi,ma,ka⟩ => ?_)
  have da : a.gpr .rdi = off B 0 := by
    rw [show off B 0 = B from BitVec.add_zero B]
    exact (ka.gpr (by decide)).trans hd
  refine WP.seq (WP.mono (copyPair_ok (hs.congr ka.2.2) da lo (by decide) (by decide)
    (by unfold sFn hdrBytes at *; omega_using [pads, head]) (by omega_using [pads]) (by unfold sFn hdrBytes at *; omega_using [head]))
    fun b ⟨vb,ob,kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.mono (copyPair_ok (hs.congr kab.2.2) ((kb.gpr (by decide)).trans da)
    ((kb.gpr (by decide)).trans hi) (by decide) (by decide)
    (by unfold sFn hdrBytes at *; omega_using [pads, head]) (by omega_using [pads]) (by unfold sFn hdrBytes at *; omega_using [pads, head]))
    fun t ⟨vt,ot,kt⟩ => ?_
  simp only [Nat.add_zero,Nat.zero_add] at vb ob vt ot
  rw [ma] at vb ob
  refine ⟨?_,?_,(Frm.of_outside ob (by simp)).trans (Frm.of_outside ot (by simp)),
    (kab.trans kt).mono (by simp)⟩
  · intro q hq
    rw [ot.word (by omega_using [pads, hq]) (by omega_using [nowrap, pads, hq])]; exact vb q hq
  · intro q hq
    rw [vt q hq,ob.word (by unfold sFn hdrBytes at *; omega_using [head, hq]) (by unfold sFn; omega_using [hq])]

end VG.Proof.Bignum.X86_64.AdxHeader
