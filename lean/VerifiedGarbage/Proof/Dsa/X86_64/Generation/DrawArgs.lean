module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Address and tape accounting for a complete witness draw -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem drawCopyArgs_ok {s : State} {B rp op : Addr} {Z w len drawBytes used : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hlen : len ≤ drawBytes) (hd : drawBytes ≤ 1024)
    (hrp : word s.mem B (8 * kRand) = rp) (hop : word s.mem B (8 * kOut) = op)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.drawCopyArgs len drawBytes)) s fun t =>
      t.gpr .r15 = B ∧ t.gpr .rsi = off rp (used + (drawBytes - len)) ∧ t.gpr .rdi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧
      t.mem = s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes)) ∧
      Keep [.r15, .rsi, .rax, .rdi, .rcx, .rdx] s t := by
  have hld : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hst : InRegions s.wr (off B (8 * kUsed)) 8 :=
    hg.scr.st (by have := hdr_lt_slot w 8 (show kUsed < 32 by decide); omega)
  have hsmall : ∀ n ≤ 8192, (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n :=
    fun n hn => sx_ofNat (by omega)
  have hout : word (s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))) B (8 * kOut) = op :=
    (hdrStore_hdr s.mem B _ (by decide : kUsed < 32) (by decide : kOut < 32) (by decide)).trans hop
  refine WP.mono (WP.keep [.r15, .rsi, .rax, .rdi, .rcx, .rdx] (Q := fun t =>
    t.gpr .r15 = B ∧ t.gpr .rsi = off rp (used + (drawBytes - len)) ∧ t.gpr .rdi = op ∧
    t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧
    t.mem = s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))) ?_ rfl)
    fun _ ⟨⟨ha, hb, hc, hd, he, hf⟩, hk⟩ => ⟨ha, hb, hc, hd, he, hf, hk⟩
  xrun [Impl.Dsa.X86_64.Generation.drawCopyArgs, State.ea, hdr, hdrOff, hg.rdi,
    hld kRand (by decide), hld kUsed (by decide), hld kOut (by decide), hst, hrp, hus,
    hsmall (drawBytes - len) (by omega), hsmall drawBytes (by omega), ← BitVec.ofNat_add,
    hout]
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨trivial, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;> omega

end VG.Proof.Dsa.X86_64.Generation
