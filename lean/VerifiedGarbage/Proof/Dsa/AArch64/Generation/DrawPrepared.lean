module

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
public import VerifiedGarbage.Proof.Bignum.WorkFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Drawing witness bytes preserves the modulus and advances only the entropy cursor. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem drawPrepared_ok {s : State} {B rp op : Addr} {Z w N used drawBytes : Nat} {bs : List Byte}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hlen : bs.length ≤ drawBytes) (hmax : drawBytes < 4096)
    (hp : word s.mem B (8 * kRand) = rp)
    (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (ho : word s.mem B (8 * kOut) = op)
    (hsrc : Src s B Z (off rp (used + (drawBytes - bs.length))) bs)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hout : ∀ i < bs.length, Z ≤ ofs B (off op i))
    (hsep : ∀ i < bs.length, ∀ j < bs.length,
      off (off rp (used + (drawBytes - bs.length))) i ≠ off op j) :
    WP isa (Impl.Dsa.AArch64.Generation.drawCopy bs.length drawBytes) s fun t =>
      ModulusReady t B Z w N ∧ Spec.Rsa.bytesAt t.mem op bs.length = bs ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + drawBytes) ∧
      WorkFrame B [(8 * kUsed, 8)] [⟨op, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (drawCopy_ok h.ws hlen hmax hp hu ho hsrc.rd hwr hsrc.out hsep)
    fun t ⟨ht0, htbytes, hframe, hk⟩ => ?_
  let mid : State := {s with mem := s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))}
  have hmid : ModulusReady mid B Z w N := h.write_header _ hEZ (by decide)
  have hwords : ∀ d, d + 8 ≤ Z → word t.mem B d = word mid.mem B d :=
    words_outside_bytes (by have := h.ws.scr.nowrap; omega) hframe hout
  have kt : Keep mmRegs s t := by
    refine ⟨?_, hk.rd, hk.wr, hk.sp, hk.vcs⟩
    intro r hr
    by_cases he : r = .x0
    · subst r; exact ht0.trans h.ws.x0.symm
    · apply hk.gpr r
      cases r <;> simp_all [mmRegs]
  refine ⟨hmid.of_words hEZ hwords hk.wr ht0, ?_, ?_, ?_, kt⟩
  · apply List.ext_getElem
    · exact bytesAt_length _ _ _
    · intro i hi hi'
      have he := htbytes i hi'
      exact (by simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] using he.trans (hsrc.val i hi'))
  · rw [hwords _ (by have := h.ws.h256; simp only [kUsed, sFn]; omega)]
    exact word_writeW_self _ _ _ _
  · intro x hx hr
    rw [hframe x (fun i hi he => ?_)]
    · exact writeW_outside _ B _ (by decide) x (hr (8 * kUsed, 8) (by simp))
    · subst x
      apply hx ⟨op, bs.length⟩ (by simp)
      apply (Region.contains_self op bs.length).byte
      simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
      exact hi

end VG.Proof.Dsa.AArch64.Generation
