module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Sampler
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on PPC64LE: the specification's input

`inpOf`: the specification's input of a call, on entry; its subgroup order
is q's octets' (`inp_q`), its draws are the sampler's (`draw_eq`), and a
nonce of zeros then the candidate is the candidate's encoding (`nonce_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput randomSignDraw randomSignRemaining significant)

/-- The specification's input, on entry. -/
def inpOf (L : RL) (m : Mem) : RandomSignInput :=
  ⟨L.pl, L.ql, Spec.Rsa.bytesAt m L.key L.kl, Spec.Rsa.bytesAt m L.dig L.dl, randOf L m⟩

theorem inp_q {L : RL} (hL : L.Ok) (m : Mem) :
    (Spec.Dsa.privateKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m L.key L.kl)).params.q =
      Spec.Dsa.decodeBE (qbOf L m) := by
  have := hL.ql
  simp only [Spec.Dsa.privateKeyBytes, Spec.Dsa.publicKeyBytes]
  rw [VG.Proof.Dsa.bytesAt_slice m L.key (by simp only [RL.kl]; omega)]

theorem draw_eq {L : RL} (hL : L.Ok) (m : Mem) (u : Nat) :
    randomSignDraw (inpOf L m) u = Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (qbOf L m)) 128 ((randOf L m).drop u) := by
  simp only [randomSignDraw, inpOf]
  rw [inp_q hL m]

theorem bytesAt_add' (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (off p a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The nonce: zeros, then a candidate `k` in its last `W` octets. -/
theorem nonce_eq {F : Addr} {m : Mem} {ql W k : Nat} (hW : W ≤ ql)
    (hz : ∀ j < ql - W, m (off F (oNonce + j)) = 0)
    (hk : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W) = k) :
    Spec.Rsa.bytesAt m (off F oNonce) ql = Spec.Dsa.encodeBE ql k := by
  have e1 : Spec.Rsa.bytesAt m (off F oNonce) (ql - W) = List.replicate (ql - W) 0 := by
    apply List.ext_getElem
    · simp [VG.Proof.Bignum.bytesAt_length]
    · intro j h₁ _
      rw [VG.Proof.Bignum.bytesAt_length] at h₁
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      rw [show off F oNonce + BitVec.ofNat 64 j = off F (oNonce + j) by simp only [off, BitVec.add_assoc,
        BitVec.ofNat_add]]
      exact hz j h₁
  have e2 : Spec.Rsa.bytesAt m (off F oNonce) ql = List.replicate (ql - W) 0 ++
      Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W := by
    rw [show ql = (ql - W) + W by omega, bytesAt_add', e1, Nat.add_sub_cancel]
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  rw [e2, ← hk, ← Dsa.decode_padding _ (ql - W)]
  have hl : (List.replicate (ql - W) 0 ++ Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W).length = ql := by
    simp [VG.Proof.Bignum.bytesAt_length]; omega
  have := Dsa.encodeBE_decodeBE (List.replicate (ql - W) 0 ++ Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W)
  rw [hl] at this
  exact this.symm

end VG.Proof.Dsa.PPC64LE.RS
