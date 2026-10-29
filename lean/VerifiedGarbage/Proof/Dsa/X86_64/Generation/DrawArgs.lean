module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Address and tape accounting for a complete witness draw -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem drawCopyArgs_ok {s : State} {B rp op : Addr} {Z w len drawBytes used : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hlen : len ≤ drawBytes)
    (hrp : word s.mem B (8 * kRand) = rp) (hop : word s.mem B (8 * kOut) = op)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (hdl : word s.mem B (8 * kLen) = BitVec.ofNat 64 drawBytes)
    (hll : word s.mem B (8 * kUsedP) = BitVec.ofNat 64 len) :
    WP isa (.block Impl.Dsa.X86_64.Generation.drawCopyArgs) s fun t =>
      t.gpr .r15 = B ∧ t.gpr .rsi = off rp (used + (drawBytes - len)) ∧ t.gpr .rdi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧
      t.mem = s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes)) ∧
      Keep [.r15, .rsi, .rax, .rdi, .rcx, .rdx] s t := by
  have hld : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hst : InRegions s.wr (off B (8 * kUsed)) 8 :=
    hg.scr.st (by have := hdr_lt_slot w 8 (show kUsed < 32 by decide); omega)
  have hout : word (s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))) B (8 * kOut) = op :=
    (hdrStore_hdr s.mem B _ (by decide : kUsed < 32) (by decide : kOut < 32) (by decide)).trans hop
  have hlen' : word (s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))) B (8 * kUsedP) =
      BitVec.ofNat 64 len :=
    (hdrStore_hdr s.mem B _ (by decide : kUsed < 32) (by decide : kUsedP < 32) (by decide)).trans hll
  refine WP.mono (WP.keep [.r15, .rsi, .rax, .rdi, .rcx, .rdx] (Q := fun t =>
    t.gpr .r15 = B ∧ t.gpr .rsi = off rp (used + (drawBytes - len)) ∧ t.gpr .rdi = op ∧
    t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧
    t.mem = s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))) ?_ rfl)
    fun _ ⟨⟨ha, hb, hc, hd, he, hf⟩, hk⟩ => ⟨ha, hb, hc, hd, he, hf, hk⟩
  xrun [Impl.Dsa.X86_64.Generation.drawCopyArgs, State.ea, hdr, hdrOff, hg.rdi,
    hld kRand (by decide), hld kUsed (by decide), hld kOut (by decide), hld kLen (by decide),
    hld kUsedP (by decide), hst, hrp, hus, hdl, ← BitVec.ofNat_add, hout, hlen']
  simp only [off, BitVec.ofNat_add]
  refine ⟨?_, ?_⟩
  · rw [← Offset.ofNat_sub_ofNat hlen]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega

end VG.Proof.Dsa.X86_64.Generation
