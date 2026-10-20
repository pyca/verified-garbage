module
public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Rsa.X86.PrivCompare
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Rsa.PrivCheck

/-! # Byte-exact equality for two readable buffers without input-dependent branches -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem compareBuffer_ok (s : State) {a b : BitVec 32} {n : Nat}
    (hn : 0 < n) (hn' : n < 2 ^ 32) (aFit : a.toNat + n ≤ 2 ^ 32) (bFit : b.toNat + n ≤ 2 ^ 32)
    (aRead : InRegions (s.rd ++ s.wr) (byteAddr a) n) (bRead : InRegions (s.rd ++ s.wr) (byteAddr b) n)
    (first : s.gpr .esi = a) (second : s.gpr .edi = b) (count : s.gpr .ecx = BitVec.ofNat 32 n) (zero : s.gpr .ebp = 0) :
    WP isa compareBytes s fun t =>
      (t.gpr .ebp = 0 ↔ Spec.Rsa.bytesAt s.mem (byteAddr a) n = Spec.Rsa.bytesAt s.mem (byteAddr b) n) ∧
      t.mem = s.mem ∧ Keeps [.esi, .edi, .ebp, .eax, .edx, .ecx] s t := by
  have byte {p : BitVec 32} (fit : p.toNat + n ≤ 2 ^ 32) (read : InRegions (s.rd ++ s.wr) (byteAddr p) n)
      (i : Nat) (hi : i < n) : InRegions (s.rd ++ s.wr) (byteAddr (p + BitVec.ofNat 32 i)) 1 := by
    rw [byteAddr_add (by omega)]
    obtain ⟨r, hr, hc⟩ := read
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  have ctx : CompareCtx s a b n := ⟨hn', byte aFit aRead, byte bFit bRead⟩
  refine WP.mono (compareBytes_ok s ctx hn first second count zero) ?_
  intro t inv
  refine ⟨?_, inv.mem, inv.rest⟩
  rw [inv.equal, VG.Proof.Rsa.bytesAt_eq_iff]
  constructor
  · intro equal i hi
    have h := equal i hi
    rw [byteAddr_add (by omega), byteAddr_add (by omega)] at h
    exact h
  · intro equal i hi
    rw [byteAddr_add (by omega), byteAddr_add (by omega)]
    exact equal i hi
end VG.Proof.Rsa.X86.PrivChecked
