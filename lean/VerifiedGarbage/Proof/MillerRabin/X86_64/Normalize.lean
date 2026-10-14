module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Normalize only unused RSA bookkeeping for the shared round -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

def normalizedMem (m : Mem) (B : Addr) (w : Nat) : Mem :=
  zeroWords.foldl (fun m j => m.writeW (off B (8 * j)) (0#64))
    ((m.writeW (off B (8 * kLen)) (BitVec.ofNat 64 (8 * w))).writeW
      (off B (8 * kUsed)) (BitVec.ofNat 64 (8 * w)))

theorem normalize_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (h : Good s B Z w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block normalize) s fun t =>
      t.mem = normalizedMem s.mem B w ∧ Keep [.rax] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 :=
    h.scr.ld (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_arith)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    h.scr.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  have sh : BitVec.ofNat 64 w <<< (3 : Nat) = BitVec.ofNat 64 (8 * w) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 w * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * w)
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  refine WP.keep [.rax] ?_ rfl
  simp only [normalize, zeroWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  xrun [normalizedMem, zeroWords, List.foldl_cons, List.foldl_nil,
    kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kE, kI, kElen, kUsed, sFn,
    State.ea, hdr, hdrOff, h.rdi, hl, h.hdr.hw, sh,
    hs 17 (by decide), hs 25 (by decide), hs 16 (by decide), hs 18 (by decide),
    hs 23 (by decide), hs 24 (by decide), hs 19 (by decide), hs 20 (by decide)]
  rfl

end VG.Proof.MillerRabin.X86_64
