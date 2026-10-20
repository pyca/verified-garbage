module
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecScan
public import VerifiedGarbage.Proof.RsaOaep.Decode

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSAES-OAEP decryption on ARMv7: what the decoding returns

`decOut_eq`: when `k ≥ 2 hLen + 2`, decryption returns the message after
`T`'s padding if every check passes (`allOk`), the error otherwise, or the
private-key operation's own error, all in the terms the code computes
(`EM`'s bytes `V`, `EM` unmasked `V5`, `T`, `idx`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

variable (h g : OHash)

theorem take1_map_range (f : Nat → Byte) {n : Nat} (hn : 0 < n) : ((List.range n).map f).take 1 = [f 0] := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [List.range_succ_eq_map]

theorem lhB_length (P : EP) (σ : State) : (lhB h P σ).length = h.H.D := by
  rw [lhB, h.valid.2, h.glen]

/-- `lHash' = lHash`, as lists. -/
theorem lh_iff (P : EP) (σ : State) :
    srcB (V5 h g P σ) (1 + h.H.D) h.H.D = h.G.hash (labB P σ) ↔
      ∀ i < h.H.D, V5 h g P σ (1 + h.H.D + i) = (lhB h P σ).getD i 0 := by
  constructor
  · intro e i hi
    rw [← srcB_getD (V5 h g P σ) (1 + h.H.D) hi]; exact congrArg (fun l => l.getD i 0) e
  · intro e
    exact Proof.RsaOaep.srcB_eq (lhB_length h P σ) e

/-- `decode`, in the code's terms. -/
theorem decode_eq' (P : EP) (σ : State) (hfit : 2 * h.H.D + 2 ≤ P.K) :
    Spec.RsaOaep.decode h.G g.G (labB P σ) ((List.range P.K).map (V P σ)) =
      if allOk h g P σ then some ((sL (tN h P) (T h g P σ)).drop (idx h g P σ + 1)) else none := by
  have hD := h.D_pos
  have h5 := Proof.RsaOaep.chain_eq (G := g.G) (V := V P σ) (V1 := V P σ) (V3 := V3 h g P σ)
    (V5 := V5 h g P σ) hfit (fun _ _ => rfl) (fun x _ => by rw [Nat.sub_add_eq])
    (fun x _ => by rw [Nat.sub_add_eq])
  rw [Proof.RsaOaep.decode_eq g.valid (labB P σ) hfit h.glen h5,
    show srcB (V5 h g P σ) (1 + 2 * h.H.D) (P.K - (2 * h.H.D + 1)) = sL (tN h P) (T h g P σ) from rfl,
    RsaPss.dropWhile_lz, take1_map_range _ (by omega)]
  have hc : ([V P σ 0] = [0x00] ∧ srcB (V5 h g P σ) (1 + h.H.D) h.H.D = h.G.hash (labB P σ)) ↔ hdOk h g P σ := by
    simp only [lh_iff h g P σ, List.cons.injEq, and_true]
  have hl : RsaPss.lz (sL (tN h P) (T h g P σ)) ≤ tN h P := lzS_le (tN h P) (T h g P σ)
  by_cases hf : lzS (tN h P) (T h g P σ) < tN h P ∧ T h g P σ (lzS (tN h P) (T h g P σ)) = 1
  · have e : (sL (tN h P) (T h g P σ)).drop (lzS (tN h P) (T h g P σ)) =
        0x01 :: (sL (tN h P) (T h g P σ)).drop (idx h g P σ + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [sL_length]; exact hf.1)]
      simp only [sL, List.getElem_map, List.getElem_range, idx, pzS, ite_eq_left hf.1, hf.2]
    rw [e]
    split
    · rename_i m heq
      obtain ⟨-, rfl⟩ := List.cons.inj heq
      by_cases ho : hdOk h g P σ
      · rw [ifp (hc.mpr ho), ifp ⟨ho, hf⟩]
      · rw [ifn (fun h' => ho (hc.mp h')), ifn (fun h' => ho h'.1)]
    · rename_i hne; exact (hne _ rfl).elim
  · rw [ifn (fun h' => hf h'.2)]
    by_cases hlt : lzS (tN h P) (T h g P σ) < tN h P
    · rw [List.drop_eq_getElem_cons (by rw [sL_length]; exact hlt)]
      have hne : (sL (tN h P) (T h g P σ))[lzS (tN h P) (T h g P σ)]'(by rw [sL_length]; exact hlt) ≠ 0x01 := by
        simp only [sL, List.getElem_map, List.getElem_range]; exact fun e => hf ⟨hlt, e⟩
      split
      · rename_i heq; exact absurd (List.cons.inj heq).1 hne
      · rfl
    · rw [List.drop_eq_nil_of_le (by rw [sL_length]; show tN h P ≤ lzS (tN h P) (T h g P σ); omega)]

/-- What decryption returns, when `k ≥ 2 hLen + 2`. -/
theorem decOut_eq (P : EP) (σ : State) (hfit : 2 * h.H.D + 2 ≤ P.K) (hk : OcK P σ) :
    Proof.RsaOaep.decOut h.G g.G (labB P σ) (oc P σ) =
      if rV P σ = 1 then
        (if allOk h g P σ then .ok ((sL (tN h P) (T h g P σ)).drop (idx h g P σ + 1)) else .invalid)
      else if rV P σ = 2 then .fault else .invalid := by
  have hd := decode_eq' h g P σ hfit
  show _ = if rOf (oc P σ) = 1 then _ else if rOf (oc P σ) = 2 then _ else _
  have hV : ∀ i, V P σ i = (emL P.K (oc P σ)).getD i 0 := fun _ => rfl
  cases e : oc P σ with
  | invalid => simp [Proof.RsaOaep.decOut, rOf]
  | fault => simp [Proof.RsaOaep.decOut, rOf]
  | ok y =>
    have hem : (List.range P.K).map (V P σ) = y :=
      Proof.RsaOaep.range_ext (hk y e) fun i _ => by rw [hV, e]; rfl
    rw [hem] at hd
    simp only [Proof.RsaOaep.decOut, hd, rOf]
    rw [ifp trivial]
    by_cases ha : allOk h g P σ
    · rw [ifp ha, ifp ha]
    · rw [ifn ha, ifn ha]

end VG.Proof.RsaOaep.Arm.Dec
