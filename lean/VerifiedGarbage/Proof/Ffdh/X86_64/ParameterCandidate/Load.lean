module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Load
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter candidates on x86-64: load without requiring byte normalization -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Load either candidate using its own word count. At the p/q width
boundary, the extra zero byte fits in aN's existing two spare words. -/
theorem loadNumber_ok {s : State} {B src : Addr} {Z w a : Nat} {mi : BitVec 64} {bs : List Byte}
    (ha : a < 8) (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hsi : s.gpr .rsi = src) (hcx : s.gpr .rcx = BitVec.ofNat 64 bs.length)
    (hk1 : 1 ≤ bs.length) (hk : bs.length < 2 ^ 31)
    (hw1 : w ≤ (bs.length + 7) / 8) (hw2 : (bs.length + 7) / 8 ≤ w + 1)
    (hval : Spec.Rsa.os2ip bs < 2 ^ (64 * w))
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off src i) 1)
    (hbytes : ∀ i (hi : i < bs.length), s.mem (off src i) = bs[i])
    (hsep : ∀ i < bs.length, ofs B (off src i) < slot w a ∨
      slot w a + 8 * ((bs.length + 7) / 8) ≤ ofs B (off src i)) :
    WP isa (loadNumber a) s fun t => wv t.mem B (slot w a) w = Spec.Rsa.os2ip bs ∧
      Good t B Z w mi ∧ Outside B (slot w a) (8 * ((bs.length + 7) / 8)) s.mem t.mem ∧
      Keep [.rbx, .rax, .rdx, .rbp, .r14] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr a)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sArr a < 32 by unfold sArr; omega); omega)
  have hbound : slot w a + 8 * ((bs.length + 7) / 8) ≤ Z := by
    have := slot_le (w := w) ha
    omega
  unfold loadNumber
  refine WP.seq (WP.mono (WP.keep [.rbx] (Q := fun u => u.gpr .rbx = off B (slot w a) ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.harr a ha]) rfl)
    fun u ⟨⟨hbx, hm⟩, k⟩ => ?_)
  refine WP.mono (loadBE_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hsi)
    ((k.gpr (by decide)).trans hcx) hbx rfl hk1 hk rfl hbound
    (fun i hi => by rw [k.2.1, k.2.2]; exact hrd i hi)
    (fun i hi => by rw [hm]; exact hbytes i hi) hsep) fun t ⟨hv, ho, k'⟩ => ?_
  have hmod : wv t.mem B (slot w a) ((bs.length + 7) / 8) % 2 ^ (64 * w) =
      wv t.mem B (slot w a) w := by
    conv_lhs => arg 1; rw [show (bs.length + 7) / 8 = w + ((bs.length + 7) / 8 - w) by omega, wv_add]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wv_lt _ _ _ _)]
  have ho' : Outside B (slot w a) (8 * ((bs.length + 7) / 8)) s.mem t.mem := by rw [← hm]; exact ho
  refine ⟨by rw [← hmod, hv, Nat.mod_eq_of_lt hval],
    ⟨hg.scr.congr (k'.2.2.trans k.2.2), ((k.trans k').gpr (by decide)).trans hg.rdi,
      hg.hdr.outside ho' (by unfold slot hdrBytes; omega)⟩,
    ho', (k.trans k').mono (by decide)⟩

/-- The modulus instance of the shared number loader. -/
theorem loadCandidate_ok {s : State} {B src : Addr} {Z w : Nat} {mi : BitVec 64} {bs : List Byte}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hsi : s.gpr .rsi = src) (hcx : s.gpr .rcx = BitVec.ofNat 64 bs.length)
    (hk1 : 1 ≤ bs.length) (hk : bs.length < 2 ^ 31)
    (hw1 : w ≤ (bs.length + 7) / 8) (hw2 : (bs.length + 7) / 8 ≤ w + 1)
    (hval : Spec.Rsa.os2ip bs < 2 ^ (64 * w))
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off src i) 1)
    (hbytes : ∀ i (hi : i < bs.length), s.mem (off src i) = bs[i])
    (hsep : ∀ i < bs.length, ofs B (off src i) < slot w aN ∨
      slot w aN + 8 * ((bs.length + 7) / 8) ≤ ofs B (off src i)) :
    WP isa loadCandidate s fun t => wv t.mem B (slot w aN) w = Spec.Rsa.os2ip bs ∧
      Good t B Z w mi ∧ Outside B (slot w aN) (8 * ((bs.length + 7) / 8)) s.mem t.mem ∧
      Keep [.rbx, .rax, .rdx, .rbp, .r14] s t := by
  simpa only [loadCandidate] using loadNumber_ok (by decide : aN < 8) hg hZ hsi hcx hk1 hk hw1 hw2 hval hrd hbytes hsep

end VG.Proof.Ffdh.X86_64.ParameterCandidate
