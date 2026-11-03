module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Checks
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPss.Params

/-!
# RSASSA-PSS signing on RISC-V: the outcome, by cases

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/Spec.lean`): `signOut G s`, what the contract asks
of a call from `s`. It is `invalid` if the modulus' first byte is zero
(`signOut_zero`) or the salt does not fit (`signOut_long`), and otherwise the
private operation (`privOut`) on the encoding `encEm`, with `lo` and the mask
`c` the code computes (`signOut_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64
open VG.Proof.RsaPss.RISCV64 (cmB byte_ok)

/-- The digest and the salt, from the entry state. -/
abbrev digB (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 8) D
abbrev saltB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat

variable (G : Spec.Mgf1.Hash)

/-- The private operation on `em`, with the entry's key. -/
def privOut (s : State) (em : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) em
    (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .a7).toNat)

/-- The outcome `signContract.post` asks for. -/
def signOut (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign G G (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .a7).toNat)
    (digB G.len s) (saltB s)

/-- `H = Hash(0⁸ ‖ mHash ‖ salt)`. -/
abbrev hS (s : State) : List Byte := G.hash (Spec.RsaPss.zeros 8 ++ digB G.len s ++ saltB s)

/-- `dbLen`. -/
abbrev dbS (s : State) : Nat := kk s - loN s - G.len - 1

/-- The mask of `maskedDB`'s first byte, as a byte. -/
abbrev cS (s : State) : Byte := (cmB (s.mem (s.gpr .a2))).setWidth 8

/-- The encoding, as `k` bytes. -/
def encEm (s : State) : List Byte :=
  (List.range (kk s)).map (RsaPss.emT (loN s) (dbS G s) (stackArg s 10).toNat (saltB s) (hS G s)
    (Spec.Mgf1.mgf1 G (hS G s) (dbS G s)) (cS s))

theorem bytesAt_cons (m : Mem) (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m p k = m p :: Spec.Rsa.bytesAt m (p + 1) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ => ?_⟩
  simp only [Function.comp, BitVec.add_assoc]
  rw [show (1 : Addr) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
    rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]; rfl]

theorem signOut_zero {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .a2) = 0) : signOut G s = .invalid := by
  unfold signOut
  rw [bytesAt_cons _ _ hk, h0]
  exact RsaPss.sign_zero G ..

theorem emLen_eq {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .a2) ≠ 0) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip
      (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (kk s))) - 1) = kk s - loN s := by
  rw [bytesAt_cons _ _ hk, RsaPss.emLength_eq _ h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  unfold loN
  split <;> omega

theorem signOut_long {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .a2) ≠ 0)
    (h : kk s - loN s < G.len + (stackArg s 10).toNat + 2) : signOut G s = .invalid := by
  unfold signOut
  refine RsaPss.sign_long G _ _ _ _ _ _ _ _ ?_
  rw [emLen_eq hk h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  exact h

theorem cS_eq {s : State} (h0 : s.mem (s.gpr .a2) ≠ 0) :
    cS s = if (s.mem (s.gpr .a2)).toNat = 1 then 0xFF
      else BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .a2)).toNat - 1) := by
  have hn : (s.mem (s.gpr .a2)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have := (byte_ok _ (s.mem (s.gpr .a2)).isLt hn).2
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  unfold cS
  rw [this]
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)

theorem signOut_eq (hG : Proof.Mgf1.Valid G) {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .a2) ≠ 0)
    (hfit : G.len + (stackArg s 10).toNat + 2 ≤ kk s - loN s) :
    signOut G s = privOut s (encEm G s) := by
  have hel := emLen_eq hk h0
  have hc := RsaPss.mask_eq (Spec.Rsa.bytesAt s.mem (s.gpr .a2 + 1) (kk s - 1)) h0
  unfold signOut privOut encEm
  generalize hnB : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = nB at hel ⊢
  rw [bytesAt_cons _ _ hk] at hnB
  subst hnB
  rw [RsaPss.sign_eq G hG h0 (lo := loN s) (db := dbS G s)
    (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _) rfl hel
    (by rw [List.length_cons, VG.Proof.RsaPkcs1Sig.bytesAt_length]; unfold loN; split <;> omega) rfl
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; exact hfit)]
  rw [hel] at hc
  rw [hc, ← cS_eq h0]
  simp only [List.length_cons, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  rw [Nat.sub_add_cancel hk]

end VG.Proof.RsaPss.RISCV64.Sg
