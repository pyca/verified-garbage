module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Caller
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.Omega

/-! # Save the shared caller's workspace in a preserved register -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller
open VG.Proof.MlKem.X86_64

def pad (w : Nat) : Nat := slot w aR1 + 8 * w

def savedMem (s : State) (B : Addr) (w : Nat) : Mem :=
  s.mem.writeW (off B (pad w)) (s.gpr .rbx)

theorem saved_outside (s : State) (B : Addr) (w : Nat) (hp : pad w + 8 ≤ 2 ^ 64) :
    Outside B (pad w) 8 s.mem (savedMem s B w) :=
  writeW_outside s.mem B (s.gpr .rbx) hp

theorem saved_rbx (s : State) (B : Addr) (w : Nat) :
    word (savedMem s B w) B (pad w) = s.gpr .rbx := by
  simp only [savedMem, word_writeW_self]

private theorem imul_low (a b : BitVec 64) :
    BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]

theorem save_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (h : Good s B Z w mi) (hZ : slot w 28 ≤ Z) :
    WP isa (.block save) s fun t =>
      t.mem = savedMem s B w ∧ t.gpr .rbx = B ∧
      t.gpr .rsi = BitVec.ofNat 64 (32 + 28 * (w + 2)) ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 :=
    h.scr.ld (by have := hdr_lt_slot w 28 (show sW < 32 by decide); omega_arith)
  have hp : pad w + 8 ≤ Z := by
    simp only [pad, slot, hdrBytes, aR1] at hZ ⊢
    omega_arith
  have hs : InRegions s.wr (off B (pad w)) 8 := h.scr.st hp
  have ha : BitVec.signExtend 64 (208 : BitVec 32) * BitVec.ofNat 64 w +
      BitVec.signExtend 64 (656 : BitVec 32) + B = off B (pad w) := by
    change 208#64 * BitVec.ofNat 64 w + 656#64 + B = off B (pad w)
    simp only [pad, slot, hdrBytes, aR1, off]
    bv_omega
  have hk : BitVec.ofNat 64 w * BitVec.signExtend 64 (28 : BitVec 32) +
      BitVec.signExtend 64 (88 : BitVec 32) = BitVec.ofNat 64 (32 + 28 * (w + 2)) := by
    change BitVec.ofNat 64 w * 28#64 + 88#64 = BitVec.ofNat 64 (32 + 28 * (w + 2))
    bv_omega
  refine WP.mono (WP.keep [.rax, .rbx, .rcx, .rdx, .rsi] (c := .block save)
    (Q := fun t => t.mem = savedMem s B w ∧ t.gpr .rbx = B ∧
      t.gpr .rsi = BitVec.ofNat 64 (32 + 28 * (w + 2))) ?_ rfl)
    fun t ⟨⟨hm, hb, hn⟩, hk⟩ => ⟨hm, hb, hn, hk⟩
  unfold save padAddress
  simp only [List.cons_append, List.nil_append]
  xrun [execImul, imul_low, BitVec.add_zero,
    show BitVec.signExtend 64 (208#32) = 208#64 from rfl,
    show BitVec.signExtend 64 (656#32) = 656#64 from rfl,
    show BitVec.signExtend 64 (28#32) = 28#64 from rfl,
    show BitVec.signExtend 64 (88#32) = 88#64 from rfl,
    show BitVec.ofInt 64 0 = 0#64 from rfl, State.ea, hdr, hdrOff, at0, h.rdi, hl, h.hdr.hw, ha, hs, savedMem, hk]

end VG.Proof.MillerRabin.X86_64.Caller
