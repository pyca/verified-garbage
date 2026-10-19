module
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.RsaKeyGen.Table

import VerifiedGarbage.Proof.Framework.Omega

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

private theorem zero_fold_outside (B : Addr) (js : List Nat)
    (hj : ∀ j ∈ js, 16 ≤ j ∧ j < 32) (m : Mem) :
    Outside B 128 128 m (js.foldl (fun m j => m.writeW (off B (8 * j)) (0#64)) m) := by
  induction js generalizing m with
  | nil => exact Outside.refl _ _ _ _
  | cons j js ih =>
    obtain ⟨hj16, hj32⟩ := hj j List.mem_cons_self
    exact ((writeW_outside m B (0#64) (d := 8 * j) (by omega_arith)).mono
      (by omega_arith) (by omega_arith)).trans
      (ih (fun k hk => hj k (List.mem_cons_of_mem _ hk)) _)

theorem normalized_outside (m : Mem) (B : Addr) (w : Nat) :
    Outside B 128 128 m (normalizedMem m B w) := by
  unfold normalizedMem
  have hL := (writeW_outside m B (BitVec.ofNat 64 (8 * w))
    (d := 8 * kLen) (by decide)).mono (o' := 128) (n' := 128) (by decide : 128 ≤ 8 * kLen) (by decide : 8 * kLen + 8 ≤ 256)
  have hU := (writeW_outside (m.writeW (off B (8 * kLen)) (BitVec.ofNat 64 (8 * w))) B (BitVec.ofNat 64 (8 * w))
    (d := 8 * kUsed) (by decide)).mono (o' := 128) (n' := 128) (by decide : 128 ≤ 8 * kUsed) (by decide : 8 * kUsed + 8 ≤ 256)
  exact (hL.trans hU).trans (zero_fold_outside B zeroWords (by
    simp only [zeroWords, List.mem_cons, List.not_mem_nil, or_false]
    rintro j (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide) _)

theorem normalized_header (m : Mem) (B : Addr) (w : Nat) {j : Nat} (hj : j < 16) :
    word (normalizedMem m B w) B (8 * j) = word m B (8 * j) :=
  (normalized_outside m B w).word (Or.inl (by omega_arith)) (by omega_arith)

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
