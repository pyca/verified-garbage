module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMain
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLeavePrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupContext
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete CRT workspace initialization preserves all three layouts -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_setupAll_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : CrtSetupContext base len w s) (ptr : s.gpr .r0 = base)
    (count : s.gpr .r7 = BitVec.ofNat 32 w) (zero : s.gpr .r3 = 0) :
    WP isa setupAll s fun t => CrtMainState base len w t.mem ∧
      CrtPrimeState (crtP base w) base len w t.mem ∧ CrtPrimeState (crtQ base w) base len w t.mem ∧
      t.gpr .r0 = base ∧ Frame (crtRegions base len w) s.mem t.mem ∧ Rest roundClobbers s t := by
  have size := h.size
  rw [setupAll, WP.seq_iff]
  refine WP.mono (crt_setupMain_ok s h.main h.width h.widthFit h.arraysFit ptr count zero) ?_
  rintro u ⟨mainU, ptrU, frameU, restU⟩
  have ctxU := h.congr restU.wr
  rw [WP.seq_iff]
  refine WP.mono (crt_setupPrime_ok u ctxU.main ctxU.p (by omega) (by omega : 224 + 4 ≤ 8 * len)
    (by decide) h.width h.widthFit h.arraysFit ptrU (mainU.toCrtLayoutState.nativeCount ctxU.main) mainU.p) ?_
  rintro v ⟨layoutP, widthP, ptrP, linkP, frameP, restP⟩
  have pV : CrtPrimeState (crtP base w) base len w v.mem := ⟨⟨layoutP, widthP⟩, linkP⟩
  have mainV := mainU.congr (h.main.eq_of_frame h.sepMP frameP)
  have restSV := restU.trans restP
  have ctxV := h.congr restSV.wr
  rw [WP.seq_iff]
  refine WP.mono (crt_leavePrime_ok v ctxV.p (by omega) ptrP linkP) ?_
  rintro z ⟨ptrZ, memZ, restZ⟩
  have mainZ : CrtMainState base len w z.mem := memZ ▸ mainV
  have restSZ := restSV.trans (restZ.mono (by simp [roundClobbers]))
  have ctxZ := h.congr restSZ.wr
  rw [WP.seq_iff]
  refine WP.mono (crt_setupPrime_ok z ctxZ.main ctxZ.q (by omega) (by omega : 228 + 4 ≤ 8 * len)
    (by decide) h.width h.widthFit h.arraysFit ptrZ (mainZ.toCrtLayoutState.nativeCount ctxZ.main) mainZ.q) ?_
  rintro r ⟨layoutQ, widthQ, ptrQ, linkQ, frameQ, restQ⟩
  have mainR := mainZ.congr (h.main.eq_of_frame h.sepMQ frameQ)
  have pZ : CrtPrimeState (crtP base w) base len w z.mem := memZ ▸ pV
  have pR := pZ.congr (h.p.eq_of_frame h.sepPQ frameQ)
  have qR : CrtPrimeState (crtQ base w) base len w r.mem := ⟨⟨layoutQ, widthQ⟩, linkQ⟩
  have restSR := restSZ.trans restQ
  refine WP.mono (crt_leavePrime_ok r (h.q.congr restSR.wr) (by omega) ptrQ linkQ) ?_
  rintro t ⟨ptrT, memT, restT⟩
  rw [memZ] at frameQ
  have frame : Frame (crtRegions base len w) s.mem r.mem := (frameU.mono (by simp [crtRegions])).trans
    ((frameP.mono (by simp [crtRegions])).trans (frameQ.mono (by simp [crtRegions])))
  exact ⟨memT ▸ mainR, memT ▸ pR, memT ▸ qR, ptrT, by rw [memT]; exact frame,
    restSR.trans (restT.mono (by simp [roundClobbers]))⟩

end VG.Proof.Bignum.Arm
