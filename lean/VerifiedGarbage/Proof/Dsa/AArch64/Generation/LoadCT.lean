module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront

/-! Candidate loads disclose only source pointers and byte lengths. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

structure LoadPublic where
  B : Addr
  Z : Nat
  w : Nat
  pointer : Addr
  bytes : List Byte

structure LoadState (ptrSlot lenSlot : Nat) (p : LoadPublic) (s : State) : Prop where
  ws : VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w
  pointer : word s.mem p.B (8 * ptrSlot) = p.pointer
  length : word s.mem p.B (8 * lenSlot) = BitVec.ofNat 64 p.bytes.length
  source : Src s p.B p.Z p.pointer p.bytes
  positive : 1 ≤ p.bytes.length
  fits : p.bytes.length ≤ 8 * p.w

theorem loadCandidate_ct {dst ptrSlot lenSlot : Nat} (hd : dst < 16) (hp : ptrSlot < 32) (hl : lenSlot < 32)
    {hc1 hc2 hc3 : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht1 : (taint.check (Taint.ofRegs [.x0, .x12, .x11])
      (.seq (.block (base dst .x8 ++ [movi .x7 0])) zeroAcc) hc1).isSome = true)
    (ht2 : (taint.check (Taint.ofRegs [.x0])
      (.block (ws ++ base dst .x8 ++ [VG.Impl.Bignum.AArch64.ldh .x1 ptrSlot, VG.Impl.Bignum.AArch64.ldh .x2 lenSlot])) hc2).isSome = true)
    (ht3 : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc3).isSome = true) :
    RelCT isa (Two (LoadState ptrSlot lenSlot)) (seqs (loadA dst ptrSlot lenSlot)) (fun _ _ => True) :=
  loadA_ct0 LoadPublic.B LoadPublic.Z LoadPublic.w hd hp hl LoadPublic.pointer (fun p => p.bytes.length)
    (fun _ _ h => ⟨h.ws, h.pointer, h.length⟩) ht1 ht2 ht3

end VG.Proof.Dsa.AArch64.Generation
