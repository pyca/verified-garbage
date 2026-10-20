module
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.X86.LoadBE

import VerifiedGarbage.Proof.Bignum.X86.LoadBEArgs
import VerifiedGarbage.Proof.Bignum.X86.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion

/-! # RSA integer import, including non-word-aligned input lengths -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem loadBE_ok {s : State} {base : Addr} {bytes n out len : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (ho : out + 8 * n ≤ bytes)
    (hl : 0 < len) (hlen : len ≤ 8 * n)
    (hp : (s.gpr .esi).toNat + len ≤ 2 ^ 32)
    (hc : s.gpr .ecx = BitVec.ofNat 32 len)
    (hr : InRegions (s.rd ++ s.wr) (byteAddr (s.gpr .esi)) len)
    (hd : Region.Disjoint ⟨byteAddr (s.gpr .esi), len⟩ ⟨off base out, 8 * n⟩) :
    WP isa (loadBE n out) s fun t =>
      wordsVal t.mem base out n = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (s.gpr .esi)) len) ∧
      Outside base out (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw := hs.nowrap
  have srcLen : len < 2 ^ 32 := by have := hs.size_lt; omega
  let dst := s.gpr .edi + BitVec.ofNat 32 out
  have dstAddr : byteAddr dst = off base out := hs.ea (by omega)
  have dstNat : dst.toNat = base.toNat + out := by
    dsimp only [dst]
    rw [BitVec.toNat_add, hs.edi_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show out < 2 ^ 32 by omega), Nat.mod_eq_of_lt (by omega)]
  have dstFit : dst.toNat + 8 * n ≤ 2 ^ 32 := by omega
  unfold loadBE
  refine WP.seq (WP.mono (zerosW_ok hs (k := 2 * n) (by omega) (by omega))
    fun u ⟨O, Z, K⟩ => ?_)
  refine WP.seq (WP.mono (loadBEArgs_ok u out hl (by rw [K.1 .ecx (by decide), hc]))
    fun v ⟨D, S, C, M, A⟩ => ?_)
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (K.mono (by decide)).trans (A.mono (by decide))
  have O' : Outside base out (8 * n) s.mem v.mem := by
    rw [M]
    simpa only [show 4 * (2 * n) = 8 * n by omega] using O
  have vr : InRegions (v.rd ++ v.wr) (byteAddr (s.gpr .esi)) len := by
    rw [keep.2.1, keep.2.2]; exact hr
  have vw : InRegions v.wr (byteAddr dst) len := by
    rw [keep.2.2, dstAddr]
    exact hs.write (by omega)
  have ctx := reverseCtx_of_regions v (s.gpr .esi) dst srcLen hp (by omega) vr vw
    (by rw [dstAddr]; exact hd.sub_right (Region.sub_prefix hlen))
  refine WP.mono (reverseBytes_ok v ctx hl
    (by rw [S, K.1 .esi (by decide)])
    (by rw [D, K.1 .edi (by decide)]) C) fun t I => ?_
  have Ot : Outside base out (8 * n) v.mem t.mem := by
    intro a ha
    apply I.outside a
    intro j hj he
    have ej : ofs base a = out + j := by
      rw [he, byteAddr_add (by omega), dstAddr]
      exact ofs_off base (by omega)
    omega
  have input : Spec.Rsa.bytesAt v.mem (byteAddr (s.gpr .esi)) len =
      Spec.Rsa.bytesAt s.mem (byteAddr (s.gpr .esi)) len := by
    apply VG.Proof.Dsa.outs_bytes (ranges := [(out, 8 * n)])
      (Outs.of_outside O' (by simp)) (by omega)
    · intro r hr'
      obtain rfl := List.mem_singleton.mp hr'
      omega
    · intro r hr'
      obtain rfl := List.mem_singleton.mp hr'
      exact hd
  have padding : ∀ j, len ≤ j → j < 8 * n → t.mem (off base out + BitVec.ofNat 64 j) = 0 := by
    intro j hj hjn
    rw [I.outside _ ?_, M]
    · exact byte_zero_of_val32 Z (by omega)
    · intro k hk he
      rw [byteAddr_add (by omega), dstAddr] at he
      have e := congrArg (fun a => (a - off base out).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega : j < 2 ^ 64),
        Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64)] at e
      omega
  refine ⟨?_, O'.trans Ot, keep.trans (I.rest.mono (by decide))⟩
  have value := I.os2ip hp (by omega : dst.toNat + len ≤ 2 ^ 32)
  rw [dstAddr, input] at value
  rw [wordsVal_eq_val32, ← read_eq_val32]
  have ext := val32_zero_extension t.mem (off base out) (n := 2 * n) (by omega : len ≤ 4 * (2 * n))
    (by intro j hj hjn; exact padding j hj (by omega))
  rw [← read_eq_val32] at ext
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext.trans value

end VG.Proof.Bignum.X86
