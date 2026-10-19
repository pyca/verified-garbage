module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeCopy

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeChecks

/-! # Input geometry and byte-string result of the i686 encoder -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.X86 Spec.RsaPkcs1Sig

def encodeId (x : BitVec 32) (H : List Byte) (k : Nat) : Option (List Byte) :=
  (Hash.ofId x.toNat).bind fun h => Spec.RsaPkcs1Sig.encode h H k

structure EPre (s0 : State) (x : BitVec 32) (k : Nat) : Prop where
  hash : s0.gpr .edx = x
  length : s0.gpr .ecx = BitVec.ofNat 32 k
  bound : k ≤ 1024
  buf : Buf s0 k
  digest : Digest s0 k (s0.gpr .ebp).toNat

def EOut (s0 t : State) : Option (List Byte) → Prop
  | some em => t.gpr .eax = 1 ∧ t.mem = writeBytes s0.mem (byteAddr (s0.gpr .edi)) em
  | none => t.gpr .eax = 0 ∧ t.mem = s0.mem

def EPost (s0 : State) (x : BitVec 32) (k : Nat) (t : State) : Prop :=
  Keeps clob s0 t ∧ EOut s0 t (encodeId x
    (Spec.Rsa.bytesAt s0.mem (byteAddr (s0.gpr .esi)) (s0.gpr .ebp).toNat) k)

theorem refuse_ok {s0 s : State} {x : BitVec 32} {k : Nat}
    (keep : Keeps clob s0 s) (mem : s.mem = s0.mem)
    (none : encodeId x (Spec.Rsa.bytesAt s0.mem (byteAddr (s0.gpr .esi)) (s0.gpr .ebp).toNat) k = none) :
    WP isa fail s (EPost s0 x k) := by
  refine WP.mono (fail_ok s) fun t ⟨kt, mt, ax⟩ => ?_
  refine ⟨keep.trans (kt.mono (by decide)), ?_⟩
  rw [none]
  exact ⟨ax, mt.trans mem⟩

theorem add11_toNat {n : Nat} (bound : n ≤ 83) :
    (BitVec.ofNat 32 n + 11).toNat = n + 11 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (11 : BitVec 32).toNat = 11 from rfl]
  omega

end VG.Proof.RsaPkcs1Sig.X86
