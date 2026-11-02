module

public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on PPC64LE: the witnesses, one draw at a time

`cw_short` and `cw_step`: `checkWitnesses` of a modulus `N` of `mb + 1`
bits (`bitLength (N − 1) = mb`) unfolded by one draw of `⌈mb / 8⌉` octets
at `u`, the witness `wA mb r u`, as the machine draws it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses drawWitness_eq)

/-- The witness drawn at offset `u` of the tape, for a modulus of `mb` bits. -/
def wA (mb : Nat) (r : List Byte) (u : Nat) : Nat := Spec.Rsa.os2ip ((r.drop u).take ((mb + 7) / 8)) % 2 ^ mb

theorem mr_round_eq {N : Nat} (a : Nat) (hN : 3 ≤ N) (ho : N % 2 = 1) :
    Proof.MillerRabin.Round.round N a = Spec.Ffdh.mrRound N a := by
  simpa only [Proof.MillerRabin.Round.round] using VG.Proof.Ffdh.rsa_round_eq a hN ho

theorem cw_short {N mb n : Nat} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hm : 1 ≤ mb) {r : List Byte} {u : Nat}
    (h : r.length < u + (mb + 7) / 8) : checkWitnesses N (n + 1) (r.drop u) = none := by
  have hw : Spec.Ffdh.witnessOctets N = (mb + 7) / 8 := by simp only [Spec.Ffdh.witnessOctets, hbl]
  have hd : Spec.Ffdh.drawWitness N (r.drop u) = none := by
    rw [drawWitness_eq (by rw [hw]; omega_arith), hw]
    have : ¬((mb + 7) / 8 ≤ (r.drop u).length) := by rw [List.length_drop]; omega_arith
    simp only [this, ↓reduceIte]
  simp only [checkWitnesses, hd, Option.bind_eq_bind, Option.bind_none]

theorem cw_step {N mb n : Nat} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hm : 1 ≤ mb) {r : List Byte} {u : Nat}
    (h : u + (mb + 7) / 8 ≤ r.length) :
    checkWitnesses N (n + 1) (r.drop u) =
      if 2 ≤ wA mb r u ∧ wA mb r u < N - 1 then
        (if Spec.Ffdh.mrRound N (wA mb r u) then checkWitnesses N n (r.drop (u + (mb + 7) / 8))
          else some (false, r.drop (u + (mb + 7) / 8)))
      else checkWitnesses N (n + 1) (r.drop (u + (mb + 7) / 8)) := by
  have hw : Spec.Ffdh.witnessOctets N = (mb + 7) / 8 := by simp only [Spec.Ffdh.witnessOctets, hbl]
  have hl : (mb + 7) / 8 ≤ (r.drop u).length := by rw [List.length_drop]; omega_arith
  have hd := drawWitness_eq (w := N) (by rw [hw]; omega_arith) (r.drop u)
  rw [hw, hbl] at hd
  simp only [hl, ↓reduceIte, List.drop_drop] at hd
  have ha : Spec.Rsa.os2ip ((r.drop u).take ((mb + 7) / 8)) % 2 ^ mb = wA mb r u := rfl
  rw [ha] at hd
  by_cases hr : 2 ≤ wA mb r u ∧ wA mb r u < N - 1
  · simp only [hr, and_self, ↓reduceIte] at hd ⊢
    simp only [checkWitnesses, hd, Option.bind_eq_bind, Option.bind_some]
  · simp only [hr, ↓reduceIte] at hd ⊢
    simp only [checkWitnesses, hd, Option.bind_eq_bind]

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
