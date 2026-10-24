module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.Proof.RsaOaep.Decode
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP decryption on PPC64LE: what the outputs say

Untrusted: everything here is checked by Lean. `dec_written`: from the
views of `EM` before and after its unmasking, `lHash` and the scan's
registers, the bytes of `out` (the buffer shifted by `idx + 1`, ANDed with
`ok`), `*msg_len` and the result are what `writtenDecrypt` asks of
`decOut`'s outcome.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG
open VG.Proof.RsaOaep (mixV srcB mk scanS accG zM decOut decode_eq scanS_inv accG_eq_zero or_eq_zero mk_eq_zero
  scan_found scan_fail out_list out_zero lk bad srcB_eq scanS_congr map_range_getD')
open VG.Proof.Mgf1 (ifp ifn)

/-- A byte ANDed with a mask. -/
def andB (b : Byte) (msk : BitVec 64) : Byte := (b.setWidth 64 &&& msk).setWidth 8

theorem andB_ones (b : Byte) : andB b (BitVec.allOnes 64) = b := by
  simp only [andB, BitVec.and_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by have := b.isLt; omega), Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem andB_zero (b : Byte) : andB b 0 = 0 := by
  simp only [andB]; rw [show BitVec.setWidth 64 b &&& 0 = 0 from BitVec.and_zero]; rfl

theorem mk_true {p : Prop} [Decidable p] (h : p) : mk p = BitVec.allOnes 64 := by simp [mk, h]
theorem mk_false {p : Prop} [Decidable p] (h : ¬ p) : mk p = 0 := by simp [mk, h]

theorem accG_congr (b : Byte) {f f' g g' : Nat → Byte} : ∀ n, (∀ i < n, f i = f' i) → (∀ i < n, g i = g' i) →
    accG b f g n = accG b f' g' n
  | 0, _, _ => rfl
  | n + 1, hf, hg => by
    simp only [accG]
    rw [accG_congr b n (fun i hi => hf i (by omega)) (fun i hi => hg i (by omega)), hf n (by omega), hg n (by omega)]

section
variable {Hs Gs : Spec.Mgf1.Hash} {D k : Nat} {lab : List Byte} {V0 V1 lh : Nat → Byte}
  {o : Spec.Rsa.Outcome} {mo : Mem} {out ml : Addr} {r : BitVec 64} {idx : Nat}

theorem dec_written (hGv : Proof.Mgf1.Valid Gs) (hHv : Proof.Mgf1.Valid Hs) (hHl : Hs.len = D) (hk : 2 * D + 2 ≤ k)
    (hk2 : k ≤ 1024)
    (h5 : ∀ x < k, V1 x = mixV (mixV V0 (Spec.Mgf1.mgf1 Gs (srcB V0 (1 + D) (k - D - 1)) D) 1 D)
      (Spec.Mgf1.mgf1 Gs (srcB (mixV V0 (Spec.Mgf1.mgf1 Gs (srcB V0 (1 + D) (k - D - 1)) D) 1 D) 1 D) (k - D - 1))
      (1 + D) (k - D - 1) x)
    (hlh : ∀ i < D, lh i = (Hs.hash lab).getD i 0)
    (hem : ∀ em, o = .ok em → em = (List.range k).map V0)
    (hidx : (scanS (fun i => V1 (1 + 2 * D + i)) (accG (V1 0) (fun i => V1 (1 + D + i)) lh D)
      (k - (2 * D + 1))).2.1 = BitVec.ofNat 64 idx)
    (hidx' : idx < k - (2 * D + 1) ∨ idx = 0)
    (hout : ∀ i < k, mo (out + BitVec.ofNat 64 i) =
      andB ((srcB V1 (1 + 2 * D) (k - (2 * D + 1))).getD (i + (idx + 1)) 0)
        (mk (rcOf o = 1 ∧ ((scanS (fun i => V1 (1 + 2 * D + i)) (accG (V1 0) (fun i => V1 (1 + D + i)) lh D)
          (k - (2 * D + 1))).2.2 ||| (scanS (fun i => V1 (1 + 2 * D + i))
            (accG (V1 0) (fun i => V1 (1 + D + i)) lh D) (k - (2 * D + 1))).1) = 0)))
    (hml : mo.readW ml 64 = (BitVec.ofNat 64 k - BitVec.ofNat 64 (2 * D + 2) - BitVec.ofNat 64 idx) &&&
      mk (rcOf o = 1 ∧ ((scanS (fun i => V1 (1 + 2 * D + i)) (accG (V1 0) (fun i => V1 (1 + D + i)) lh D)
          (k - (2 * D + 1))).2.2 ||| (scanS (fun i => V1 (1 + 2 * D + i))
            (accG (V1 0) (fun i => V1 (1 + D + i)) lh D) (k - (2 * D + 1))).1) = 0))
    (hr : r = (if rcOf o = 2 then 2#64 else 0#64) |||
      (mk (rcOf o = 1 ∧ ((scanS (fun i => V1 (1 + 2 * D + i)) (accG (V1 0) (fun i => V1 (1 + D + i)) lh D)
          (k - (2 * D + 1))).2.2 ||| (scanS (fun i => V1 (1 + 2 * D + i))
            (accG (V1 0) (fun i => V1 (1 + D + i)) lh D) (k - (2 * D + 1))).1) = 0) &&& 1#64)) :
    Spec.RsaOaep.writtenDecrypt mo out ml k (r.setWidth 32) (decOut Hs Gs lab o) := by
  generalize hT : srcB V1 (1 + 2 * D) (k - (2 * D + 1)) = T at hout
  have hTl : T.length = k - (2 * D + 1) := by rw [← hT]; simp [srcB]
  have hTg : ∀ i < k - (2 * D + 1), T.getD i 0 = V1 (1 + 2 * D + i) := fun i hi => by
    rw [← hT, srcB, map_range_getD' _ hi]
  generalize hc₀ : accG (V1 0) (fun i => V1 (1 + D + i)) lh D = c₀ at *
  have hsc2 : scanS (fun i => V1 (1 + 2 * D + i)) c₀ (k - (2 * D + 1)) =
      scanS (fun i => T.getD i 0) c₀ T.length := by
    rw [hTl]; exact scanS_congr _ _ fun i hi => (hTg i hi).symm
  rw [hsc2] at hidx hout hml hr
  generalize hsc : scanS (fun i => T.getD i 0) c₀ T.length = sc at *
  obtain ⟨i1, -, -, i4⟩ := scanS_inv (fun i => T.getD i 0) c₀ T.length
  rw [hsc] at i1 i4
  have hacc : sc.2.2 ||| sc.1 = 0 ↔ c₀ = 0 ∧ ¬ bad (fun i => T.getD i 0) T.length ∧
      ¬ lk (fun i => T.getD i 0) T.length := by
    rw [i4, i1, or_eq_zero, or_eq_zero, mk_eq_zero, mk_eq_zero, and_assoc]
  -- A mask of zero: zeros, the length 0, and the result `r = 2 ? 2 : 0`.
  have zero_out : mk (rcOf o = 1 ∧ sc.2.2 ||| sc.1 = 0) = 0 →
      Spec.Rsa.bytesAt mo out k = Spec.RsaOaep.zeros k ∧ mo.readW ml 64 = 0 ∧
      r.setWidth 32 = (if rcOf o = 2 then 2#64 else 0#64).setWidth 32 := fun h0 =>
    ⟨out_zero fun i hi => by rw [hout i hi, h0, andB_zero], by rw [hml, h0]; exact BitVec.and_zero,
      by rw [hr, h0]; split <;> decide⟩
  cases o with
  | fault =>
    obtain ⟨a, b, c⟩ := zero_out (mk_false fun h => by simp [rcOf] at h)
    exact ⟨by rw [c]; decide, a, b⟩
  | invalid =>
    obtain ⟨a, b, c⟩ := zero_out (mk_false fun h => by simp [rcOf] at h)
    exact ⟨by rw [c]; decide, a, b⟩
  | ok em =>
    have em_eq := hem em rfl
    subst em_eq
    have r1 : rcOf (.ok ((List.range k).map V0)) = 1 := rfl
    simp only [r1, true_and, ite_false, show (1 : Nat) ≠ 2 by decide] at hout hml hr zero_out
    rw [BitVec.zero_or] at hr
    simp only [decOut]
    rw [decode_eq hGv _ hk hHl h5, show k - (2 * D + 1) = k - (2 * D + 1) from rfl, hT]
    have hz : sc.2.2 ||| sc.1 ≠ 0 → _ := fun hne => zero_out (mk_false hne)
    by_cases hfd : ¬ lk (fun i => T.getD i 0) T.length ∧ ¬ bad (fun i => T.getD i 0) T.length
    · obtain ⟨j₀, hj₀, hsj, hdw⟩ := scan_found T c₀ hfd.1 hfd.2
      rw [hsc] at hsj
      have hij : idx = j₀ := by
        have := hidx.symm.trans hsj
        have := congrArg BitVec.toNat this
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at this
      subst hij
      rw [hdw, show (1 : Byte) = 1#8 from rfl]
      simp only []
      have hV0 : V1 0 = V0 0 := by
        rw [h5 0 (by omega), mixV, ifn (by omega), mixV, ifn (by omega)]
      have htake : ((List.range k).map V0).take 1 = [V0 0] := by
        rw [show k = (k - 1) + 1 by omega, List.range_succ_eq_map]; simp
      by_cases hc : ((List.range k).map V0).take 1 = [0x00] ∧ srcB V1 (1 + D) D = Hs.hash lab
      · rw [ifp hc]
        have hacc0 : sc.2.2 ||| sc.1 = 0 := hacc.mpr ⟨by
          rw [← hc₀]; exact (accG_eq_zero _ _ _ D).mpr ⟨by
            rw [hV0]; rw [htake] at hc; exact List.head_eq_of_cons_eq hc.1, fun i hi => by
            show V1 (1 + D + i) = lh i
            rw [hlh i hi, ← hc.2, srcB, map_range_getD' _ hi]⟩, hfd.2, hfd.1⟩
        rw [mk_true hacc0] at hout hml hr
        refine ⟨by rw [hr]; decide, out_list (by omega) hj₀ fun i hi => by rw [hout i hi, andB_ones], ?_⟩
        rw [hml, BitVec.and_allOnes, VG.Offset.ofNat_sub_ofNat (by omega), VG.Offset.ofNat_sub_ofNat (by omega),
          List.length_drop]
        congr 1; omega
      · rw [ifn hc]
        have hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => by
          have e := (accG_eq_zero _ _ _ D).mp (hc₀ ▸ (hacc.mp h0).1)
          obtain ⟨e0, e1⟩ := e
          refine hc ⟨by rw [htake, ← hV0, e0], ?_⟩
          refine srcB_eq (by rw [hHv.2, hHl]) fun i hi => ?_
          rw [← hlh i hi]; exact e1 i hi
        obtain ⟨a, b, c⟩ := hz hne
        exact ⟨by rw [c]; rfl, a, b⟩
    · have hfail := scan_fail T (by
        by_contra hc; exact hfd ⟨fun h => hc (.inl h), fun h => hc (.inr h)⟩)
      have hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => hfd ⟨(hacc.mp h0).2.2, (hacc.mp h0).2.1⟩
      obtain ⟨a, b, c⟩ := hz hne
      split
      · rename_i m heq
        split at heq
        · rename_i m' hm; exact absurd hm (hfail m')
        · cases heq
      · exact ⟨by rw [c]; rfl, a, b⟩

end

end VG.Proof.RsaOaep.PPC64LE.Dec
