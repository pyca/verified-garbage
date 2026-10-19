module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Init
public import VerifiedGarbage.Spec.Ffdh.Generation
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! # Native FFDH generation initialization: policy arithmetic -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Impl.Ffdh.X86_64.Generation

def initialized (m : Mem) (B : Addr) (bits : Nat) : Mem :=
  (((m.writeW B (BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits))).writeW
    (off B 8) (BitVec.ofNat 64 ((bits + 7) / 8))).writeW
    (off B 16) (BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits))).writeW
    (off B 24) (BitVec.ofNat 64 (512 * ((bits + 7) / 8)))

theorem shift_ofNat (n k : Nat) :
    (BitVec.ofNat 64 n) <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod,
    Nat.mod_mod]

private theorem width_value {bits : Nat} (hhi : bits ≤ 8192) :
    ((BitVec.ofNat 64 bits) + 7) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  change ((bits % 2 ^ 64 + 7) % 2 ^ 64) / 8 = ((bits + 7) / 8) % 2 ^ 64
  omega_using [hhi]

theorem initialize_ok {s : State} {B : Addr} {bits : Nat}
    (scr : Scr s B 128) (hdi : s.gpr .rdi = B)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 bits) (hhi : bits ≤ 8192) :
    WP isa initializeState s fun t => t.gpr .rax = 1 ∧ t.mem = initialized s.mem B bits := by
  have hstore : ∀ j < 4, InRegions s.wr (off B (8 * j)) 8 :=
    fun j hj => scr.st (by omega_using [hj])
  have hb : bits < 2 ^ 64 := by omega_using [hhi]
  have hc : BitVec.signExtend 64 (7 : BitVec 32) = (7 : BitVec 64) := by decide
  unfold initializeState initialized Spec.Ffdh.parameterAttempts Spec.Ffdh.parameterEntropy
  xrun [field, State.ea, off, BitVec.ofInt_natCast, hdi, hsi, hstore 0 (by decide), hstore 1 (by decide),
    hstore 2 (by decide), hstore 3 (by decide)]
  have hcap (n : Nat) : n * 32768 + n = 32769 * n := by omega
  simp only [hc, width_value hhi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, shift_ofNat,
    ← BitVec.ofNat_add, Nat.reducePow, Nat.reduceMul, BitVec.add_zero, hcap]
  simp only [Nat.mul_comm, Nat.mul_assoc]

theorem controller_store_word (m : Mem) (B : Addr) (v : BitVec 64) {i j : Nat}
    (hi : i < 16) (hj : j < 16) :
    word (m.writeW (off B (8 * i)) v) B (8 * j) =
      if j = i then v else word m B (8 * j) := by
  by_cases he : j = i
  · subst he
    rw [ite_eq_left rfl]
    exact word_writeW_self _ _ _ _
  · rw [ite_eq_right he]
    exact hdrStore_hdr _ _ _ (by omega_using [hi]) (by omega_using [hj]) (Ne.symm he)

theorem initialized_words (m : Mem) (B : Addr) (bits : Nat) :
    Spec.Rsa.wordsAt (initialized m B bits) B 4 =
      [BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits), BitVec.ofNat 64 ((bits + 7) / 8),
        BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits), BitVec.ofNat 64 (512 * ((bits + 7) / 8))] := by
  change [word (initialized m B bits) B 0, word (initialized m B bits) B 8,
    word (initialized m B bits) B 16, word (initialized m B bits) B 24] = _
  have hm : initialized m B bits =
      (((m.writeW (off B (8 * 0)) (BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits))).writeW
        (off B (8 * 1)) (BitVec.ofNat 64 ((bits + 7) / 8))).writeW
        (off B (8 * 2)) (BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits))).writeW
        (off B (8 * 3)) (BitVec.ofNat 64 (512 * ((bits + 7) / 8))) := by
    simp only [initialized, off, Nat.mul_zero, BitVec.add_zero]
  rw [hm]
  have hword (j : Nat) (hj : j < 16) :
      word
        ((((m.writeW (off B (8 * 0)) (BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits))).writeW
          (off B (8 * 1)) (BitVec.ofNat 64 ((bits + 7) / 8))).writeW
          (off B (8 * 2)) (BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits))).writeW
          (off B (8 * 3)) (BitVec.ofNat 64 (512 * ((bits + 7) / 8)))) B (8 * j) =
        if j = 3 then BitVec.ofNat 64 (512 * ((bits + 7) / 8)) else
        if j = 2 then BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits) else
        if j = 1 then BitVec.ofNat 64 ((bits + 7) / 8) else
        if j = 0 then BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits) else word m B (8 * j) := by
    rw [controller_store_word _ _ _ (i := 3) (by decide) hj,
      controller_store_word _ _ _ (i := 2) (by decide) hj,
      controller_store_word _ _ _ (i := 1) (by decide) hj,
      controller_store_word _ _ _ (i := 0) (by decide) hj]
  rw [hword 0 (by decide), hword 1 (by decide), hword 2 (by decide), hword 3 (by decide)]
  rfl

end VG.Proof.Ffdh.X86_64.Generation
