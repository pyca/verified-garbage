module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Load
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.CrtRedc
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Framework.Omega

/-! # Padded candidate and witness loads for the shared primality workspace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem loadPadded_ok {s : State} {B p : Addr} {Z w a sp sl : Nat} {mi : BitVec 64} {bs : List Byte}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw31 : w < 2 ^ 31)
    (ha : a < 8) (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = p) (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z p bs) (hk1 : 1 ≤ bs.length) (hk31 : bs.length < 2 ^ 31)
    (hkw : (bs.length + 7) / 8 ≤ w) :
    WP isa (Impl.Dsa.X86_64.Generation.loadPadded a sp sl) s fun t =>
      Good t B Z w mi ∧ wv t.mem B (slot w a) w = Spec.Rsa.os2ip bs ∧
      Outside B (slot w a) (8 * (w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hJ := slot_le (w := w) ha
  have hn := hg.scr.nowrap
  have hhdr : 256 ≤ slot w a := by simp only [slot, hdrBytes]; omega
  unfold Impl.Dsa.X86_64.Generation.loadPadded
  simp only [seqs]
  refine WP.seq (WP.mono (zeroArr_ok hg hZ hw hw31 ha) fun u ⟨hz, ho, ku⟩ => ?_)
  have hgu : Good u B Z w mi := ⟨hg.scr.congr ku.2.2, (ku.gpr (by decide)).trans hg.rdi,
    hg.hdr.outside ho hhdr⟩
  have hhu : ∀ i < 32, word u.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho.word (Or.inl (by omega)) (by omega)
  have hld : ∀ i < 32, InRegions (u.rd ++ u.wr) (off B (8 * i)) 8 := fun i hi =>
    hgu.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun v =>
      v.gpr .rsi = p ∧ v.gpr .rcx = BitVec.ofNat 64 bs.length ∧
      v.gpr .rbx = off B (slot w a) ∧ v.mem = u.mem) (by
        xrun [State.ea, hdr, hgu.rdi, hdrOff, hld sp hsp, hld sl hsl,
          hld (sArr a) (by unfold sArr; omega), hhu sp hsp, hhu sl hsl, hp, hl, hgu.hdr.harr a ha]) rfl)
    fun v ⟨⟨hsi, hcx, hbx, hm⟩, kv⟩ => ?_)
  have hrd : ∀ i < bs.length, InRegions (v.rd ++ v.wr) (off p i) 1 := fun i hi => by
    rw [kv.2.1, kv.2.2, ku.2.1, ku.2.2]; exact hsrc.rd i hi
  have hbytes : ∀ i (hi : i < bs.length), v.mem (off p i) = bs[i] := by
    intro i hi
    rw [hm, ho _ (Or.inr (by have h := hsrc.out i hi; change Z ≤ ofs B (off p i) at h; omega))]
    exact hsrc.val i hi
  refine WP.mono (loadBE_ok (hgu.scr.congr kv.2.2) hsi hcx hbx rfl hk1 hk31 rfl (by omega)
    hrd hbytes (fun i hi => Or.inr (by have h := hsrc.out i hi; omega))) fun t ⟨hv, hot, kt⟩ => ?_
  have hout : Outside B (slot w a) (8 * (w + 2)) s.mem t.mem := by
    intro x hx
    rw [hot x (by omega), hm, ho x hx]
  refine ⟨⟨hg.scr.congr (kt.2.2.trans (kv.2.2.trans ku.2.2)),
    ((ku.trans kv).trans kt).gpr (by decide) |>.trans hg.rdi, hg.hdr.outside hout hhdr⟩,
    ?_, hout, ((ku.trans kv).trans kt).mono (by decide)⟩
  have hzero : wv t.mem B (slot w a + 8 * ((bs.length + 7) / 8)) (w - (bs.length + 7) / 8) = 0 :=
    (wv_eq_zero_iff _ _ _ _).mpr fun j hj => by
      rw [hot.word (by omega) (by omega), hm,
        show slot w a + 8 * ((bs.length + 7) / 8) + 8 * j =
          slot w a + 8 * ((bs.length + 7) / 8 + j) by omega]
      exact (wv_eq_zero_iff _ _ _ _).mp hz _ (by omega)
  rw [wv_split _ _ _ (show (bs.length + 7) / 8 + (w - (bs.length + 7) / 8) = w by omega),
    hv, hzero, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Dsa.X86_64.Generation
