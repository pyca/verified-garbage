import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave

namespace VG.Proof.Bignum.X86_64.AdxHeader
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.MlKem.X86_64 (Keep)

theorem clearHigh_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hp : s.gpr .r9 = off B e) (he : e+16 ≤ Z) :
    WP isa (.block AdxHeader.clearHigh) s fun t =>
      (∀ q < 2, word t.mem B (e+8*q) = 0) ∧ Outside B e 16 s.mem t.mem ∧ Keep [.rax] s t := by
  have nowrap := hs.nowrap
  unfold AdxHeader.clearHigh
  rw [show ([.mov32 .rax (.imm 0),.store (at_ .r9 0) .rax,.store (at_ .r9 8) .rax] : List Instr) =
    [.mov32 .rax (.imm 0)] ++ ([.store (at_ .r9 0) .rax] ++ [.store (at_ .r9 8) .rax]) from rfl,
    WP.block_append_iff]
  refine WP.mono (movZero_ok s .rax) fun a ⟨za,_,_,ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeAt_ok (hs.congr ka.2.2.2) ((ka.gpr (by decide)).trans hp) (by omega : e+0+8 ≤ Z))
    fun b ⟨vb,ob,kb⟩ => ?_
  have kab := ka.keep.trans kb
  refine WP.mono (storeAt_ok (hs.congr kab.2.2) ((kab.gpr (by decide)).trans hp) he)
    fun t ⟨vt,ot,kt⟩ => ?_
  simp only [Nat.add_zero] at vb ob
  rw [za] at vb
  rw [kb.gpr (r := .rax) (by simp),za] at vt
  rw [ka.2.1] at ob
  refine ⟨?_,(ob.mono (o' := e) (n' := 16) (by omega) (by omega)).trans
    (ot.mono (o' := e) (n' := 16) (by omega) (by omega)),(kab.trans kt).mono (by simp)⟩
  intro q hq
  rcases (show q=0 ∨ q=1 by omega) with rfl | rfl
  · simp only [Nat.mul_zero,Nat.add_zero]
    rw [ot.word (by omega) (by omega)]; exact vb
  · simpa only [Nat.mul_one] using vt

theorem restore_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi) (hZ : slot w 8 ≤ Z) :
    WP isa AdxHeader.restore s fun t =>
      (∀ q < 2, word t.mem B (8*sFn 12+8*q) = word s.mem B (slot w aAcc+8*q)) ∧
      (∀ q < 2, word t.mem B (8*sFn 14+8*q) = word s.mem B (highPad w+8*q)) ∧
      (∀ q < 2, word t.mem B (highPad w+8*q) = 0) ∧
      Frm B [(8*sFn 12,32),(highPad w,16)] s.mem t.mem ∧ Keep [.rax,.r8,.r9] s t := by
  have nowrap := hs.nowrap
  have pads := pads_bound hZ
  have head : hdrBytes ≤ slot w aAcc := by unfold slot; omega
  unfold AdxHeader.restore
  refine WP.seq (WP.mono (bases_ok hs hd hh hZ) fun a ⟨lo,hi,ma,ka⟩ => ?_)
  have da : a.gpr .rdi = off B 0 := by
    rw [show off B 0 = B from BitVec.add_zero B]
    exact (ka.gpr (by decide)).trans hd
  refine WP.seq (WP.mono (copyPair_ok (hs.congr ka.2.2) lo da (by decide) (by decide)
    (by omega) (by unfold sFn hdrBytes at *; omega) (by unfold sFn hdrBytes at *; omega))
    fun b ⟨vb,ob,kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.seq (WP.mono (copyPair_ok (hs.congr kab.2.2) ((kb.gpr (by decide)).trans hi)
    ((kb.gpr (by decide)).trans da) (by decide) (by decide)
    (by omega) (by unfold sFn hdrBytes at *; omega) (by unfold sFn hdrBytes at *; omega))
    fun c ⟨vc,oc,kc⟩ => ?_)
  have kabc := kab.trans kc
  refine WP.mono (clearHigh_ok (hs.congr kabc.2.2) (((kb.trans kc).gpr (by simp)).trans hi) pads.2)
    fun t ⟨zt,ot,kt⟩ => ?_
  simp only [Nat.add_zero,Nat.zero_add] at vb ob vc oc
  rw [ma] at vb ob
  have ob' := ob.mono (o' := 8*sFn 12) (n' := 32) (by omega) (by omega)
  have oc' := oc.mono (o' := 8*sFn 12) (n' := 32) (by unfold sFn; omega) (by unfold sFn; omega)
  refine ⟨?_,?_,zt,((Frm.of_outside ob' (by simp)).trans (Frm.of_outside oc' (by simp))).trans
    (Frm.of_outside ot (by simp)),(kabc.trans kt).mono (by simp)⟩
  · intro q hq
    rw [ot.word (by unfold sFn hdrBytes at *; omega) (by unfold sFn; omega),
      oc.word (by unfold sFn; omega) (by unfold sFn; omega)]
    exact vb q hq
  · intro q hq
    rw [ot.word (by unfold sFn hdrBytes at *; omega) (by unfold sFn; omega),vc q hq,
      ob.word (by unfold sFn hdrBytes at *; omega) (by omega)]

end VG.Proof.Bignum.X86_64.AdxHeader
