module

public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Tables
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBlocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCorrect
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTTab
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Unmask
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Shift
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
public import VerifiedGarbage.Proof.RsaOaep.Decode
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfStepsT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base

/-! ### `RsaOaep.PPC64LE.Dc.Out`, which only this module used -/

section

/-! ### `RsaOaep.PPC64LE.Dc.Written`, which this module and modules that import it used -/

section

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
  rw [Nat.mod_eq_of_lt (by have := b.isLt; omega_using []), Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]

theorem andB_zero (b : Byte) : andB b 0 = 0 := by
  simp only [andB]; rw [show BitVec.setWidth 64 b &&& 0 = 0 from BitVec.and_zero]; rfl

theorem mk_true {p : Prop} [Decidable p] (h : p) : mk p = BitVec.allOnes 64 := by simp [mk, h]
theorem mk_false {p : Prop} [Decidable p] (h : ¬ p) : mk p = 0 := by simp [mk, h]

theorem accG_congr (b : Byte) {f f' g g' : Nat → Byte} : ∀ n, (∀ i < n, f i = f' i) → (∀ i < n, g i = g' i) →
    accG b f g n = accG b f' g' n
  | 0, _, _ => rfl
  | n + 1, hf, hg => by
    simp only [accG]
    rw [accG_congr b n (fun i hi => hf i (by omega_using [hi])) (fun i hi => hg i (by omega_using [hi])), hf n (by omega_using []), hg n (by omega_using [])]

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
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk2, hidx']),
          Nat.mod_eq_of_lt (by omega_using [hk2, hTl, hj₀])] at this
      subst hij
      rw [hdw, show (1 : Byte) = 1#8 from rfl]
      simp only []
      have hV0 : V1 0 = V0 0 := by
        rw [h5 0 (by omega_using [hk]), mixV, ifn (by omega_using []), mixV, ifn (by omega_using [])]
      have htake : ((List.range k).map V0).take 1 = [V0 0] := by
        rw [show k = (k - 1) + 1 by omega_using [hk], List.range_succ_eq_map]; simp
      by_cases hc : ((List.range k).map V0).take 1 = [0x00] ∧ srcB V1 (1 + D) D = Hs.hash lab
      · rw [ifp hc]
        have hacc0 : sc.2.2 ||| sc.1 = 0 := hacc.mpr ⟨by
          rw [← hc₀]; exact (accG_eq_zero _ _ _ D).mpr ⟨by
            rw [hV0]; rw [htake] at hc; exact List.head_eq_of_cons_eq hc.1, fun i hi => by
            show V1 (1 + D + i) = lh i
            rw [hlh i hi, ← hc.2, srcB, map_range_getD' _ hi]⟩, hfd.2, hfd.1⟩
        rw [mk_true hacc0] at hout hml hr
        refine ⟨by rw [hr]; decide, out_list (by omega_using [hTl]) hj₀ fun i hi => by rw [hout i hi, andB_ones], ?_⟩
        rw [hml, BitVec.and_allOnes, VG.Offset.ofNat_sub_ofNat (by omega_using [hk]), VG.Offset.ofNat_sub_ofNat (by omega_using [hidx']),
          List.length_drop]
        congr 1; omega_using [hTl]
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

end

end

/-!
# RSAES-OAEP decryption on PPC64LE: the outputs

Untrusted: everything here is checked by Lean. `okMask_ok`: `ok`, all ones
iff the private operation's result is 1 and the accumulator zero (`x ≠ 0`
from the top bit of `x ∨ -x`); `outLoop_ok`: the buffer's first `k` bytes
ANDed with it to `out`; `decRet_ok`: the length and the result;
`decFail_ok`: zeros, and the result `r = 2 ? 2 : 0`. From `out` on, `Base`
does not hold (`out` is not ours): the caller's registers in their slots
(`Saves`) do.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_mov wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor
  wp_lsr wp_lbz wp_stb wp_std wp_nil wp_countdown byte_setWidth64 ofNat_succ')
open VG.Proof.RsaPkcs1Sig (bytesAt_length writeBytes_out)
open VG.Proof.RsaOaep (mk)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## Bits -/

/-- `(x ∨ -x) >>> 63`: 0 if `x = 0`, 1 if not. -/
theorem nzbit (x : BitVec 64) : ((BitVec.ofNat 64 0 - x) ||| x) >>> 63 = if x = 0 then 0#64 else 1#64 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ifn hx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_or, Nat.shiftRight_eq_div_pow]
    have h0 : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hl := x.isLt
    have hs : (BitVec.ofNat 64 0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_using [h0]
    have h1 : 2 ^ 63 ≤ ((BitVec.ofNat 64 0 - x).toNat ||| x.toNat) := by
      rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h | h
      · exact Nat.le_trans (by rw [hs]; omega_using [h]) Nat.left_le_or
      · exact Nat.le_trans h Nat.right_le_or
    have h2 : ((BitVec.ofNat 64 0 - x).toNat ||| x.toNat) < 2 ^ 64 := Nat.or_lt_two_pow (BitVec.isLt _) hl
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega_using [h1]) (by omega_using [h2])]; rfl

/-- `ok` from the result `rc` and the accumulator `x`. -/
theorem okbits {rc : Nat} (hrc : rc ≤ 2) (x : BitVec 64) :
    BitVec.ofNat 64 0 - ((((BitVec.ofNat 64 rc ^^^ BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63) &&&
      ((((BitVec.ofNat 64 0 - x) ||| x) >>> 63) ^^^ BitVec.ofNat 64 1)) = mk (rc = 1 ∧ x = 0) := by
  rw [nzbit]
  by_cases hx : x = 0
  · rw [ifp hx, mk]
    rcases (by omega_using [hrc] : rc = 0 ∨ rc = 1 ∨ rc = 2) with rfl | rfl | rfl <;> simp only [hx] <;> decide
  · rw [ifn hx, mk, ifn (fun h => hx h.2)]
    rcases (by omega_using [hrc] : rc = 0 ∨ rc = 1 ∨ rc = 2) with rfl | rfl | rfl <;> decide

/-- The result's fault bit: 2 if `rc = 2`, 0 if not. -/
theorem faultbits {rc : Nat} (hrc : rc ≤ 2) :
    let f := ((BitVec.ofNat 64 rc ^^^ BitVec.ofNat 64 2) - BitVec.ofNat 64 1) >>> 63
    f + f = if rc = 2 then 2#64 else 0#64 := by
  rcases (by omega_using [hrc] : rc = 0 ∨ rc = 1 ∨ rc = 2) with rfl | rfl | rfl <;> decide

/-- `Saves` of the entry state with other memory is `Saves` of the entry state. -/
theorem Saves.ofMem {s t : State} {m : Mem} (h : Saves (withMem s m) t) : Saves s t := ⟨h.sp, h.wr, h.hi, h.sv, h.ls⟩

/-- `r6` bytes from `r4` to `r5`, each ANDed with `r26`, for `r6 > 0`. -/
theorem andCopy_ok {u : State} {p q : Addr} {n : Nat} {msk : BitVec 64} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : u.gpr .r4 = q) (h5 : u.gpr .r5 = p) (h6 : u.gpr .r6 = BitVec.ofNat 64 n) (h26 : u.gpr .r26 = msk)
    (hr : ∀ j < n, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions u.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    WP isa (.loop (.block [.lbz .r7 .r4 0, .logic .and .r7 .r7 .r26, .stb .r7 .r5 0, .addi .r4 .r4 1,
      .addi .r5 .r5 1, .subi .r6 .r6 1]) (.nonzero .d .r6)) u fun t => Keep [.r7, .r4, .r5, .r6] u t ∧
      t.mem = writeBytes u.mem p ((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk) := by
  refine WP.mono (wp_countdown (cnt := .r6) hn' hn
    (fun i t => Keep [.r7, .r4, .r5, .r6] u t ∧
      t.mem = writeBytes u.mem p (((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk).take i) ∧
      t.gpr .r5 = p + BitVec.ofNat 64 i ∧ t.gpr .r4 = q + BitVec.ofNat 64 i) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h5], by simp [h4]⟩ h6) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h5', h4'⟩ _
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .r4 + BitVec.ofNat 64 0) 1 := by
      rw [h4', hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hv : t.mem (q + BitVec.ofNat 64 i) = u.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, List.length_map, bytesAt_length]; omega_using [])]
    refine wp_lbz rfl hR fun s₁ o₁ e₁ => wp_and fun s₂ o₂ e₂ => ?_
    have hA : InRegions s₂.wr (s₂.gpr .r5 + BitVec.ofNat 64 0) 1 := by
      rw [o₂.wr, o₁.wr, o₂.get .r5, o₁.get .r5, h5', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_stb rfl hA fun s₃ m₃ => ?_
    refine wp_addi fun s₄ o₄ e₄ => ?_
    refine wp_addi fun s₅ o₅ e₅ => ?_
    refine wp_subi fun s₆ o₆ e₆ => wp_nil ?_
    have hK' : Keep [.r7, .r4, .r5, .r6] t s₆ :=
      (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans (o₅.keep.trans o₆.keep))))).mono
    have hlt : (((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk).take i).length = i := by
      simp [bytesAt_length]; omega_using [hi]
    have hget : ((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk)[i]'(by simp [bytesAt_length]; omega_using [hi]) =
        andB (u.mem (q + BitVec.ofNat 64 i)) msk := by
      simp [Spec.Rsa.bytesAt]
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₆.mem, o₅.mem, o₄.mem, m₃.mem, o₂.mem, o₁.mem, hm, List.take_succ_eq_append_getElem
        (by simp [bytesAt_length]; omega_using [hi]), writeBytes_snoc _ _ _ _ (by omega_using [hn', hi, hlt]), hlt, hget]
      congr 1
      · rw [o₂.get .r5, o₁.get .r5, h5', BitVec.add_zero]
      · rw [e₂, e₁, o₁.get .r26, hK.get .r26, h26, h4', BitVec.add_zero, hv]; rfl
    · rw [o₆.get .r5, e₅, o₄.get .r5, m₃.gpr, o₂.get .r5, o₁.get .r5, h5', ofNat_succ']
    · rw [o₆.get .r4, o₅.get .r4, e₄, m₃.gpr, o₂.get .r4, o₁.get .r4, h4', ofNat_succ']
    · rw [e₆, o₅.get .r6, o₄.get .r6, m₃.gpr, o₂.get .r6, o₁.get .r6]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} {rc : Nat}
include P

/-- `ok` (`r26`). -/
theorem okMask_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) (hrc : rc ≤ 2) :
    WP isa (.block okMask) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      (∀ r ∉ [Reg.r4, .r5, .r6, .r26], t'.gpr r = t.gpr r) ∧ t'.gpr .r26 = mk (rc = 1 ∧ t.gpr .r24 = 0) := by
  have PF := fitsM (m := m) P
  refine wp_li (by decide) fun t₁ o₁ e₁ => wp_xor fun t₂ o₂ e₂ => wp_subi fun t₃ o₃ e₃ =>
    wp_lsr fun t₄ o₄ e₄ => wp_li (by decide) fun t₅ o₅ e₅ => wp_sub fun t₆ o₆ e₆ => wp_or fun t₇ o₇ e₇ =>
    wp_lsr fun t₈ o₈ e₈ => wp_li (by decide) fun t₉ o₉ e₉ => wp_xor fun t₁₀ o₁₀ e₁₀ =>
    wp_and fun t₁₁ o₁₁ e₁₁ => wp_li (by decide) fun t₁₂ o₁₂ e₁₂ => wp_sub fun t₁₃ o₁₃ e₁₃ => wp_nil ?_
  have k : Only [.r4, .r5, .r6, .r26] t t₁₃ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans
      (o₁₁.trans (o₁₂.trans o₁₃)))))))))))).mono
  refine ⟨h.only PF k, k.mem, fun r hr => k.gpr r hr, ?_⟩
  rw [e₁₃, e₁₂, o₁₂.get .r4, e₁₁, o₁₀.get .r4, e₁₀, e₉, o₉.get .r5, o₉.get .r4, e₈, o₈.get .r4, e₇, o₇.get .r4,
    e₆, o₆.get .r24, o₆.get .r4, e₅, o₅.get .r24, o₅.get .r4, e₄, o₄.get .r24, e₃, o₃.get .r24, e₂, o₂.get .r24,
    e₁, o₁.get .r20, o₁.get .r24, Base.r20 h]
  exact okbits hrc _

/-- `out` is writable. -/
theorem out_w : ∀ i < kk s, InRegions (fr s :: s.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 :=
  fun i hi => by
    rw [P.hwr]
    exact ⟨oR s, by simp, Offset.contains_base _ (by have := P.ok; unfold kk at hi; omega_using [hi, this])
      (by have := P.k2; unfold kk at hi; omega_using [hi])⟩

/-- `*msg_len` is writable. -/
theorem ml_w : InRegions (fr s :: s.wr) (s.gpr .r5 + BitVec.ofNat 64 0) 8 := by
  rw [P.hwr, BitVec.add_zero]
  exact ⟨mlR s, by simp, Region.contains_self _ _⟩

omit P in
/-- The slots and a buffer apart from the stack. -/
theorem slR_dis {R : Region} (h : (kD s).Disjoint R) : (slR s).Disjoint R := h.sub_left fun a ha => kR_sub a (slR_sub s a ha)

/-- The buffer's first `k` bytes ANDed with `ok` to `out`. -/
theorem outLoop_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa outLoop t fun t' => Saves s t' ∧ t'.rd = s.rd ∧ (∀ r ∉ [Reg.r4, .r5, .r6, .r7], t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (s.gpr .r3)
        ((Spec.Rsa.bytesAt t.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t.gpr .r26)) := by
  have PF := fitsM (m := m) P
  have hk1 := P.k1
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have hB : oBuf = 2560 := rfl
  have hR : oRsa = 8192 := rfl
  have hw : t.wr = fr s :: s.wr := h.wr
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hsep : ∀ j < kk s, ∀ i < kk s, off (Sd s) oBuf + BitVec.ofNat 64 j ≠ s.gpr .r3 + BitVec.ofNat 64 i :=
    fun j hj i hi => ne_of_dis (A := scR s) (B := oR s) P.os.symm (by
      show (scR s).Contains (off (off (Sd s) oBuf) j) 1
      rw [off_off]; exact (sc_sub P) _ (sc_in (n := 1) (by omega_using [hk2, ek, hB, hR, hj]) _ (Region.contains_self _ _)))
      (Offset.contains_base _ (by have := P.ok; omega_using [ek, hi, this]) (by omega_using [ek, hi]))
  refine WP.mono (andCopy_ok (q := off (Sd s) oBuf) (p := s.gpr .r3) (n := kk s) (msk := t.gpr .r26) (by omega_using [hk1, ek])
    (by omega_using [ek]) (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14])
    (by rw [o₃.get .r5, e₂, o₁.get .r16, Base.r16 h])
    (by rw [e₃, o₂.get .r15, o₁.get .r15, Base.r15 h]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm)
    (by rw [k₃.get .r26])
    (fun j hj => by
      rw [k₃.rd, k₃.wr, hw]
      show InRegions _ (off (off (Sd s) oBuf) j) 1
      rw [off_off]; exact sc_inR PF (by omega_using [hk2, ek, hB, hR, hj]) _)
    (by rw [k₃.wr, hw]; exact out_w P) hsep) fun t' ⟨hK, hm⟩ => ?_
  have K : Keep [.r4, .r5, .r6, .r7] t t' := (k₃.keep.trans hK).mono
  have hm' : t'.mem = writeBytes t.mem (s.gpr .r3)
      ((Spec.Rsa.bytesAt t.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t.gpr .r26)) := by
    rw [hm, k₃.mem]
  have fr : Frame [oR s] t.mem t'.mem := by
    rw [hm']
    refine writeBytes_frame _ _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, List.length_map, bytesAt_length]
    have := P.ok; unfold kk; simp; omega_using [this]
  refine ⟨Saves.ofMem (h.sv.keep K fr fun r hr => by rw [List.mem_singleton.mp hr]; exact slR_dis P.ko),
    K.rd.trans h.rd, fun r hr => K.gpr r hr, hm'⟩

/-- The length and the result. -/
theorem decRet_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD64 : D ≤ 64) {u : State} (sv : Saves s u)
    (h15 : u.gpr .r15 = s.gpr .r7) (h17 : u.gpr .r17 = s.gpr .r5) (h20 : u.gpr .r20 = BitVec.ofNat 64 rc)
    (hrc : rc ≤ 2) {idx : Nat} (h25 : u.gpr .r25 = BitVec.ofNat 64 idx) :
    WP isa (.block (decRet H)) u fun u' => Saves s u' ∧ u'.rd = u.rd ∧
      u'.mem = u.mem.writeW (s.gpr .r5)
        ((s.gpr .r7 - BitVec.ofNat 64 (2 * D + 2) - BitVec.ofNat 64 idx) &&& u.gpr .r26) ∧
      u'.gpr .r3 = (if rc = 2 then 2#64 else 0#64) ||| (u.gpr .r26 &&& 1#64) := by
  subst hD
  refine wp_subi (h := by omega_using [hD64]) fun u₁ o₁ e₁ => wp_sub fun u₂ o₂ e₂ => wp_and fun u₃ o₃ e₃ => ?_
  have k₃ : Only [.r4] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_std (a := s.gpr .r5 + BitVec.ofNat 64 0) (by rw [k₃.get .r17, h17]) (by rw [k₃.wr, sv.wr]; exact ml_w P)
    fun u₄ m₄ => ?_
  refine wp_li (by decide) fun u₅ o₅ e₅ => wp_xor fun u₆ o₆ e₆ => wp_subi fun u₇ o₇ e₇ => wp_lsr fun u₈ o₈ e₈ =>
    wp_add fun u₉ o₉ e₉ => wp_li (by decide) fun u₁₀ o₁₀ e₁₀ => wp_and fun u₁₁ o₁₁ e₁₁ =>
    wp_or fun u₁₂ o₁₂ e₁₂ => wp_nil ?_
  have k₁₂ : Only [.r4, .r3] u₄ u₁₂ :=
    (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))))))).mono
  have K : Keep [.r4, .r3] u u₁₂ := (k₃.keep.trans (m₄.keep.trans k₁₂.keep)).mono
  have fm : Frame [mlR s] u.mem u₁₂.mem := by
    rw [k₁₂.mem, m₄.mem, k₃.mem, BitVec.add_zero]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨sv.keep K fm fun r hr => by rw [List.mem_singleton.mp hr]; exact slR_dis P.kml, K.rd, ?_, ?_⟩
  · rw [k₁₂.mem, m₄.mem, k₃.mem, BitVec.add_zero, e₃, e₂, e₁, o₁.get .r25, o₂.get .r26, o₁.get .r26, h25, h15]
  · rw [e₁₂, e₁₁, e₁₀, o₁₀.get .r26, o₉.get .r26, o₈.get .r26, o₇.get .r26, o₆.get .r26, o₅.get .r26, m₄.gpr,
      k₃.get .r26, o₁₁.get .r3, o₁₀.get .r3, e₉, e₈, e₇, e₆, e₅, o₅.get .r20, m₄.gpr, k₃.get .r20, h20]
    rw [faultbits hrc]

/-- Zeros to `out` and `*msg_len`, and the result `r = 2 ? 2 : 0`. -/
theorem decFail_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) (hrc : rc ≤ 2) :
    WP isa decFail t fun u' => Saves s u' ∧ u'.rd = s.rd ∧
      u'.mem = (writeBytes t.mem (s.gpr .r3) (List.replicate (kk s) 0)).writeW (s.gpr .r5) (0#64) ∧
      u'.gpr .r3 = if rc = 2 then 2#64 else 0#64 := by
  have hk1 := P.k1
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have hw : t.wr = fr s :: s.wr := h.wr
  refine WP.seq (WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_nil ?_))
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (zero_ok (p := s.gpr .r3) (n := kk s) (b := 0) (by omega_using [hk1, ek]) (by omega_using [ek])
    (by rw [o₃.get .r4, o₂.get .r4, e₁, Base.r16 h])
    (by rw [o₃.get .r5, e₂, o₁.get .r15, Base.r15 h]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm)
    (by rw [e₃]; rfl)
    (by rw [k₃.wr, hw]; exact out_w P)) fun t₄ ⟨hk, hm⟩ => ?_
  have K₄ : Keep [.r4, .r5, .r6] t t₄ := (k₃.keep.trans hk).mono
  have g6 : t₄.gpr .r6 = 0#64 := by rw [hk.get .r6, e₃]
  refine wp_std (a := s.gpr .r5 + BitVec.ofNat 64 0) (by rw [K₄.get .r17, Base.r17 h]) (by rw [K₄.wr, hw]; exact ml_w P)
    fun t₅ m₅ => ?_
  refine wp_li (by decide) fun u₅ o₅ e₅ => wp_xor fun u₆ o₆ e₆ => wp_subi fun u₇ o₇ e₇ => wp_lsr fun u₈ o₈ e₈ =>
    wp_add fun u₉ o₉ e₉ => wp_nil ?_
  have k₉ : Only [.r4, .r3] t₅ u₉ := (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉)))).mono
  have K : Keep [.r4, .r5, .r6, .r3] t u₉ := (K₄.trans (m₅.keep.trans k₉.keep)).mono
  have hm' : u₉.mem = (writeBytes t.mem (s.gpr .r3) (List.replicate (kk s) 0)).writeW (s.gpr .r5) (0#64) := by
    rw [k₉.mem, m₅.mem, hm, k₃.mem, BitVec.add_zero, g6]
  have fm : Frame [oR s, mlR s] t.mem u₉.mem := by
    rw [hm']
    refine ((writeBytes_frame _ _ _ ?_).mono fun r hr => by simp at hr ⊢; exact .inl hr).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
    simp only [Region.Contains, BitVec.sub_self, List.length_replicate]
    have := P.ok; unfold kk; simp; omega_using [this]
  refine ⟨Saves.ofMem (h.sv.keep K fm fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slR_dis P.ko
      · exact slR_dis P.kml), K.rd.trans h.rd, hm', ?_⟩
  rw [e₉, e₈, e₇, e₆, e₅, o₅.get .r20, m₅.gpr, K₄.get .r20, Base.r20 h, faultbits hrc]

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-! ### `RsaOaep.PPC64LE.Dc.Verified`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.PPC64LE.Dc.Scan`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: `lHash` and the scan

Untrusted: everything here is checked by Lean. `accLh_ok`: the accumulator
of `EM`'s first byte and `lHash' ⊕ lHash` (`accG`); `scan_ok`: the scan of
`T` (`scanS`, its masks from the top bits of `b - 1` and `(b ⊕ 1) - 1`),
then the accumulator ORed with `looking`. Both read our part of the working
space only, and keep `Base`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_mov wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor wp_lsr
  wp_lbz wp_nil wp_countdown)
open VG.Proof.RsaOaep (scanS accG zM mk zM_zx zM_zx1)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## A byte's masks -/

/-- `(b - 1) >>> 63`: 1 if `b = 0`, 0 if not. -/
theorem zbit (b : Byte) : (b.setWidth 64 - BitVec.ofNat 64 1) >>> 63 = if b = 0 then 1#64 else 0#64 := by
  have hb := b.isLt
  have e : b = BitVec.ofNat 8 b.toNat := (BitVec.ofNat_toNat _ b).trans (BitVec.setWidth_eq _) |>.symm
  generalize b.toNat = n at hb e
  subst e
  revert n; decide +kernel

/-- `((b ⊕ 1) - 1) >>> 63`: 1 if `b = 1`, 0 if not. -/
theorem obit (b : Byte) : ((b.setWidth 64 ^^^ BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63 =
    if b = 1 then 1#64 else 0#64 := by
  have hb := b.isLt
  have e : b = BitVec.ofNat 8 b.toNat := (BitVec.ofNat_toNat _ b).trans (BitVec.setWidth_eq _) |>.symm
  generalize b.toNat = n at hb e
  subst e
  revert n; decide +kernel

theorem masks (b : Byte) :
    ((if b = 0 then 1#64 else 0#64) ||| (if b = 1 then 1#64 else 0#64)) - BitVec.ofNat 64 1 =
      (zM (b.setWidth 64) ||| zM (b.setWidth 64 ^^^ 1)) ^^^ BitVec.allOnes 64 ∧
    BitVec.ofNat 64 0 - (if b = 1 then 1#64 else 0#64) = zM (b.setWidth 64 ^^^ 1) ∧
    (if b = 1 then 1#64 else 0#64) - BitVec.ofNat 64 1 = zM (b.setWidth 64 ^^^ 1) ^^^ BitVec.allOnes 64 := by
  rw [zM_zx, zM_zx1]
  by_cases h0 : b = 0
  · subst h0; simp only [mk]; decide
  by_cases h1 : b = 1
  · subst h1; simp only [mk]; decide
  simp only [mk, h0, h1, ite_false]; decide

/-! ## The scan's step -/

/-- The scan's registers after `i` bytes of `f`, at `b`. -/
structure ScanI (f : Nat → Byte) (c₀ : BitVec 64) (b : Addr) (i : Nat) (u : State) : Prop where
  r4 : u.gpr .r4 = off b i
  r6 : u.gpr .r6 = BitVec.ofNat 64 i
  r7 : u.gpr .r7 = (scanS f c₀ i).1
  r25 : u.gpr .r25 = (scanS f c₀ i).2.1
  r24 : u.gpr .r24 = (scanS f c₀ i).2.2

theorem scan_step {f : Nat → Byte} {c₀ : BitVec 64} {b : Addr} {i : Nat} {u u' : State} (I : ScanI f c₀ b i u)
    (z₁ o₁ zo : BitVec 64)
    (hz : z₁ = ((f i).setWidth 64 - BitVec.ofNat 64 1) >>> 63)
    (ho : o₁ = (((f i).setWidth 64 ^^^ BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63)
    (hzo : zo = (z₁ ||| o₁) - BitVec.ofNat 64 1)
    (h24 : u'.gpr .r24 = u.gpr .r24 ||| (zo &&& u.gpr .r7))
    (h25 : u'.gpr .r25 = u.gpr .r25 ||| ((u.gpr .r6 &&& u.gpr .r7) &&& (BitVec.ofNat 64 0 - o₁)))
    (h7 : u'.gpr .r7 = u.gpr .r7 &&& (o₁ - BitVec.ofNat 64 1))
    (h4 : u'.gpr .r4 = u.gpr .r4 + BitVec.ofNat 64 1) (h6 : u'.gpr .r6 = u.gpr .r6 + BitVec.ofNat 64 1) :
    ScanI f c₀ b (i + 1) u' := by
  obtain ⟨m1, m2, m3⟩ := masks (f i)
  rw [zbit] at hz
  rw [obit] at ho
  subst hz ho hzo
  refine ⟨by rw [h4, I.r4]; exact off_off _ _ _, by rw [h6, I.r6, BitVec.ofNat_add], ?_, ?_, ?_⟩
  · rw [h7, m3, I.r7]; rfl
  · rw [h25, m2, I.r25, I.r6, I.r7]; rfl
  · rw [h24, m1, I.r24, I.r7]; rfl

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} {rc : Nat}
include P

/-- `acc := EM[0] ∨ ⋁ (lHash'[i] ⊕ lHash[i])`, `lHash'` at `1 + D`, `lHash` at
`oDig`. -/
theorem accLh_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s)
    {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (accLh H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.gpr .r24 = accG (view t.mem (Sd s) 0) (fun i => view t.mem (Sd s) (1 + D + i))
        (fun i => view t.mem (Sd s) (oDig + i)) D := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have PF := fitsM (m := m) P
  subst hD
  have rdw : ∀ {u : State}, u.rd = t.rd → u.wr = t.wr → ∀ {o : Nat}, o + 1 ≤ oRsa →
      InRegions (u.rd ++ u.wr) (off (Sd s) o) 1 := fun hr hw _ ho => by
    rw [hr, hw, h.wr]; exact sc_inR PF ho _
  refine WP.seq (wp_addi (h := by unfold oEm; omega_using [hD64]) fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ =>
    wp_lbz (a := off (Sd s) 0) (by rw [o₂.get .r14, o₁.get .r14, h.r14, hE]) (rdw (o₁.rd ▸ o₂.rd) (o₁.wr ▸ o₂.wr)
      (by decide)) fun t₃ o₃ e₃ => wp_li (by omega_using [hD64]) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.r4, .r5, .r24, .r6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine WP.mono (wp_countdown (cnt := .r6) (N := H.D) (by omega_using [hD64]) hD0
    (fun i u => Only [.r4, .r5, .r6, .r7, .r8, .r24] t u ∧ u.gpr .r4 = off (Sd s) (1 + H.D + i) ∧
      u.gpr .r5 = off (Sd s) (oDig + i) ∧ u.gpr .r24 = accG (view t.mem (Sd s) 0)
        (fun i => view t.mem (Sd s) (1 + H.D + i)) (fun i => view t.mem (Sd s) (oDig + i)) i) ?_
    ⟨k₄.mono, by rw [o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.r14, hE]; rfl,
      by rw [o₄.get .r5, o₃.get .r5, e₂, o₁.get .r14, h.r14]; rfl,
      by rw [o₄.get .r24, e₃, o₂.mem, o₁.mem]; rfl⟩ (by rw [e₄]))
    fun u ⟨o, _, _, a⟩ => ⟨h.only PF o, o.mem, fun r hr => o.gpr r (by revert r; decide), a⟩
  intro i hi u ⟨o, r4, r5, a⟩ _
  refine wp_lbz (a := off (Sd s) (1 + H.D + i)) (by rw [r4, BitVec.add_zero])
    (rdw o.rd o.wr (by omega_using [hRs, hD64, hi])) fun u₁ p₁ f₁ => ?_
  refine wp_lbz (a := off (Sd s) (oDig + i)) (by rw [p₁.get .r5, r5, BitVec.add_zero])
    (rdw (p₁.rd.trans o.rd) (p₁.wr.trans o.wr) (by omega_using [hDg, hRs, hD64, hi])) fun u₂ p₂ f₂ => ?_
  refine wp_xor fun u₃ p₃ f₃ => wp_or fun u₄ p₄ f₄ => wp_addi fun u₅ p₅ f₅ => wp_addi fun u₆ p₆ f₆ =>
    wp_subi fun u₇ p₇ f₇ => wp_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (o.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇))))))).mono
  · rw [p₇.get .r4, p₆.get .r4, f₅, p₄.get .r4, p₃.get .r4, p₂.get .r4, p₁.get .r4, r4]
    show off (off (Sd s) (1 + H.D + i)) 1 = off (Sd s) (1 + H.D + i + 1); exact off_off _ _ _
  · rw [p₇.get .r5, f₆, p₅.get .r5, p₄.get .r5, p₃.get .r5, p₂.get .r5, p₁.get .r5, r5]
    show off (off (Sd s) (oDig + i)) 1 = off (Sd s) (oDig + i + 1); exact off_off _ _ _
  · rw [p₇.get .r24, p₆.get .r24, p₅.get .r24, f₄, p₃.get .r24, p₂.get .r24, p₁.get .r24, a, f₃, p₂.get .r7, f₁,
      f₂, p₁.mem, o.mem]; rfl
  · rw [f₇, p₆.get .r6, p₅.get .r6, p₄.get .r6, p₃.get .r6, p₂.get .r6, p₁.get .r6]

/-- The scan of `T` (`k - 2 D - 1` bytes at `1 + 2 D`), then `acc ∨= looking`. -/
theorem scan_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s)
    {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (scan H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.gpr .r24 = (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .r24) (kk s - (2 * D + 1))).2.2 |||
        (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .r24) (kk s - (2 * D + 1))).1 ∧
      t'.gpr .r25 = (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .r24) (kk s - (2 * D + 1))).2.1 := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have PF := fitsM (m := m) P
  subst hD
  refine WP.seq (wp_addi (h := by unfold oEm; omega_using [hD64]) fun t₁ o₁ e₁ => wp_subi (h := by omega_using [hD64]) fun t₂ o₂ e₂ =>
    wp_li (by decide) fun t₃ o₃ e₃ => wp_li (by decide) fun t₄ o₄ e₄ => wp_subi fun t₅ o₅ e₅ =>
    wp_li (by decide) fun t₆ o₆ e₆ => wp_nil ?_)
  have k₆ : Only [.r4, .r5, .r6, .r7, .r25] t t₆ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono
  generalize hf : (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) = f
  have I0 : ScanI f (t.gpr .r24) (off (Sd s) (1 + 2 * H.D)) 0 t₆ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [o₆.get .r4, o₅.get .r4, o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.r14, hE, Nat.zero_add]
      show _ = off (Sd s) (1 + 2 * H.D) + BitVec.ofNat 64 0
      rw [BitVec.add_zero]
    · rw [o₆.get .r6, o₅.get .r6, o₄.get .r6, e₃]
    · rw [o₆.get .r7, e₅, e₄]; rfl
    · rw [e₆]; rfl
    · rw [k₆.get .r24]; rfl
  refine WP.seq (WP.mono (wp_countdown (cnt := .r5) (N := kk s - (2 * H.D + 1)) (by omega_using [ek]) (by omega_using [hk])
    (fun i u => ScanI f (t.gpr .r24) (off (Sd s) (1 + 2 * H.D)) i u ∧
      Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r24, .r25] t₆ u) ?_
    ⟨I0, Only.refl _ _⟩ (by rw [o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5, e₂, o₁.get .r15, Base.r15 h,
      sub_ofNat (by omega_using [ek, hk])])) fun u ⟨I, o⟩ => ?_)
  · intro i hi u ⟨I, o⟩ _
    refine wp_lbz (a := off (Sd s) (1 + 2 * H.D + i)) (by rw [I.r4, BitVec.add_zero, off_off])
      (by rw [o.rd, o.wr, k₆.rd, k₆.wr, h.wr]; exact sc_inR PF (by omega_using [hRs, hk2, ek, hi]) _) fun u₁ p₁ f₁ => ?_
    refine wp_subi fun u₂ p₂ f₂ => wp_lsr fun u₃ p₃ f₃ => wp_li (by decide) fun u₄ p₄ f₄ =>
      wp_xor fun u₅ p₅ f₅ => wp_subi fun u₆ p₆ f₆ => wp_lsr fun u₇ p₇ f₇ => wp_or fun u₈ p₈ f₈ =>
      wp_subi fun u₉ p₉ f₉ => wp_and fun u₁₀ p₁₀ f₁₀ => wp_or fun u₁₁ p₁₁ f₁₁ => wp_li (by decide) fun u₁₂ p₁₂ f₁₂ =>
      wp_sub fun u₁₃ p₁₃ f₁₃ => wp_and fun u₁₄ p₁₄ f₁₄ => wp_and fun u₁₅ p₁₅ f₁₅ => wp_or fun u₁₆ p₁₆ f₁₆ =>
      wp_subi fun u₁₇ p₁₇ f₁₇ => wp_and fun u₁₈ p₁₈ f₁₈ => wp_addi fun u₁₉ p₁₉ f₁₉ => wp_addi fun u₂₀ p₂₀ f₂₀ =>
      wp_subi fun u₂₁ p₂₁ f₂₁ => wp_nil ?_
    have q : Only [.r10, .r8, .r9, .r24, .r3, .r25, .r7, .r4, .r6, .r5] u u₂₁ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans (p₉.trans (p₁₀.trans
        (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans (p₁₆.trans (p₁₇.trans (p₁₈.trans (p₁₉.trans
        (p₂₀.trans p₂₁)))))))))))))))))))).mono
    have hb : u₁.gpr .r10 = (f i).setWidth 64 := by
      rw [f₁, o.mem, k₆.mem, ← hf]; rfl
    have a9 : Only [.r10, .r8, .r9] u u₉ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans p₉)))))))).mono
    have a7 : Only [.r10, .r8, .r9] u u₇ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇)))))).mono
    have b12 : Only [.r8, .r24, .r3] u₇ u₁₂ := (p₈.trans (p₉.trans (p₁₀.trans (p₁₁.trans p₁₂)))).mono
    have b16 : Only [.r8, .r24, .r3, .r25] u₇ u₁₆ :=
      (b12.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans p₁₆)))).mono
    have a15 : Only [.r10, .r8, .r9, .r24, .r3] u u₁₅ :=
      (a9.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans p₁₅)))))).mono
    have a17 : Only [.r10, .r8, .r9, .r24, .r3, .r25] u u₁₇ := (a15.trans (p₁₆.trans p₁₇)).mono
    have c11 : Only [.r5, .r8, .r25, .r9, .r7, .r4, .r6, .r3] u₁₁ u₂₁ :=
      (p₁₂.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans (p₁₆.trans (p₁₇.trans (p₁₈.trans (p₁₉.trans (p₂₀.trans
        p₂₁))))))))).mono
    have c16 : Only [.r9, .r7, .r4, .r6, .r5] u₁₆ u₂₁ :=
      (p₁₇.trans (p₁₈.trans (p₁₉.trans (p₂₀.trans p₂₁)))).mono
    have c18 : Only [.r4, .r6, .r5] u₁₈ u₂₁ := (p₁₉.trans (p₂₀.trans p₂₁)).mono
    have a18 : Only [.r10, .r8, .r9, .r24, .r3, .r25, .r7] u u₁₈ := (a17.trans p₁₈).mono
    have a20 : Only [.r10, .r8, .r9, .r24, .r3, .r25, .r7, .r4, .r6] u u₂₀ := (a18.trans (p₁₉.trans p₂₀)).mono
    refine ⟨⟨scan_step I (u₃.gpr .r8) (u₇.gpr .r9) (u₉.gpr .r8) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, (o.trans q).mono⟩, ?_⟩
    · rw [f₃, f₂, hb]
    · rw [f₇, f₆, f₅, f₄, p₄.get .r10, p₃.get .r10, p₂.get .r10, hb]
    · rw [f₉, f₈, p₇.get .r8, p₆.get .r8, p₅.get .r8, p₄.get .r8]
    · rw [c11.get .r24, f₁₁, f₁₀, p₁₀.get .r24, a9.get .r24, a9.get .r7]
    · rw [c16.get .r25, f₁₆, f₁₅, f₁₄, p₁₄.get .r3, f₁₃, f₁₂, b12.get .r9, a15.get .r25, (a9.trans
        (p₁₀.trans (p₁₁.trans (p₁₂.trans p₁₃)))).get .r6, (a9.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans p₁₃)))).get .r7]
    · rw [c18.get .r7, f₁₈, f₁₇, b16.get .r9, a17.get .r7]
    · rw [p₂₁.get .r4, p₂₀.get .r4, f₁₉, a18.get .r4]
    · rw [p₂₁.get .r6, f₂₀, p₁₉.get .r6, a18.get .r6]
    · rw [f₂₁, a20.get .r5]
  refine wp_or fun w ow ew => wp_nil ?_
  have kk' : Only [.r4, .r5, .r6, .r7, .r25, .r3, .r8, .r9, .r10, .r24] t w := (k₆.trans (o.trans ow)).mono
  refine ⟨h.only PF kk', by rw [kk'.mem], fun r hr => kk'.gpr r (by revert r; decide), ?_, ?_⟩
  · rw [ew, I.r24, I.r7]
  · rw [ow.get .r25]; exact I.r25

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-! ### `RsaOaep.PPC64LE.Dc.CTMain`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.PPC64LE.Dc.Correct`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.PPC64LE.Dc.Main`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: the decoding

Untrusted: everything here is checked by Lean. `decMain_ok`: from the
private operation's outcome (`AfterPriv`), the decoding writes what
`decOut` (`Proof/RsaOaep/Decode.lean`) says to `out` and `*msg_len`, and
returns its code, as `writtenDecrypt` takes them.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes)
open VG.Proof.RsaOaep (mixV srcB mk scanS accG zM decOut decode_eq scanS_inv accG_eq_zero or_eq_zero mk_eq_zero
  scan_found scan_fail scan_idx out_list out_zero lk bad srcB_eq)
open VG.Proof.RsaPss.PPC64LE (shV shV_eq)
open VG.Proof.Mgf1 (ifp ifn)

/-- The label, from the entry state. -/
abbrev labB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < xs.length) (hl : xs.length < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) = xs.getD i 0 := by
  simp only [writeBytes, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hl] : i < 2 ^ 64)]
  rw [ifp hi]

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

theorem labB_eq {m : Mem} (hm : Frame [kD s, scR s] s.mem m) :
    Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat = labB s :=
  bytes_entry hm P.kl P.ls.symm (by have := (stackArg s 10).isLt; omega_using [])

/-- The decoding, after the private operation's outcome. -/
theorem decMain_ok {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
    (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
    {f : Fns} (T : TabS G f 16 (SD s) s (stackArg s 16)) (TL : TabS H f 15 (SD s) s (stackArg s 15)) {v : State}
    (A : AfterPriv s v) (hsy : v.syms = s.syms)
    (hk : 2 * H.D + 2 ≤ kk s) :
    WP isa (decMain H f) v fun u => Saves s u ∧ u.rd = s.rd ∧
      Spec.RsaOaep.writtenDecrypt u.mem (s.gpr .r3) (s.gpr .r5) (kk s) ((u.gpr .r3).setWidth 32)
        (decOut Hs Gs (labB s) (privO s)) := by
  have hD0 := hH.hD0
  have hDF := hH.hDF
  have hFD := hH.hFD64
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  obtain hrc := rcOf_le (privO s)
  obtain ⟨hE, hSt, hDg, hW, hB, hRs⟩ := offs'
  generalize hD : H.D = D at *
  generalize hO : privO s = o at *
  generalize hRC : rcOf o = rc at *
  have b0 := A.base
  rw [hO, hRC] at b0
  unfold decMain
  -- `EM` unmasked.
  refine unmask_ok P hG (tabS_wm P T A.mem) hGh hGl hGv hD hD0 (by omega_using [hFD, hDF]) (by omega_using [hk]) b0 hsy fun t₁ b₁ y₁ v₁ => ?_
  -- The label's hash, through its table.
  refine WP.seq (WP.mono (hashLabelT_ok P hH (tabS_wmL P TL A.mem) b₁ y₁) fun t₂ ⟨⟨b₂, _, s₂, h₂⟩, _⟩ => ?_)
  -- `lHash'` against `lHash`.
  refine WP.seq (WP.mono (accLh_ok P hD hD0 (by omega_using [hFD, hDF]) (by omega_using [hk]) b₂) fun t₃ ⟨b₃, m₃, g₃, a₃⟩ => ?_)
  -- The scan.
  refine WP.seq (WP.mono (scan_ok P hD (by omega_using [hFD, hDF]) (by omega_using [hk]) b₃) fun t₄ ⟨b₄, m₄, g₄, a₄, i₄⟩ => ?_)
  -- The buffer.
  refine WP.seq (WP.mono (clearBuf_ok P b₄) fun t₅ ⟨b₅, g₅, v₅⟩ => ?_)
  refine WP.seq (WP.mono (copyT_ok P hD (by omega_using [hFD, hDF]) (by omega_using [hk]) b₅) fun t₆ ⟨b₆, g₆, v₆⟩ => ?_)
  generalize hsc : scanS (fun i => view t₃.mem (Sd s) (1 + 2 * D + i)) (t₃.gpr .r24) (kk s - (2 * D + 1)) = sc at a₄ i₄
  obtain ⟨idx, hidx, hidx'⟩ := scan_idx (fun i => view t₃.mem (Sd s) (1 + 2 * D + i)) (t₃.gpr .r24)
    (kk s - (2 * D + 1))
  rw [hsc] at hidx
  obtain h25 : t₆.gpr .r25 = BitVec.ofNat 64 idx := by
    rw [g₆ .r25 (by simp), g₅ .r25 (by simp), i₄, hidx]
  refine WP.seq (WP.mono (shift_ok P b₆ h25 (by omega_using [hk2, ek, hidx'])) fun t₇ ⟨b₇, k₇, v₇⟩ => ?_)
  -- `ok`, `out`, the length and the result.
  refine WP.seq (WP.mono (okMask_ok P b₇ (by omega_using [hrc])) fun t₈ ⟨b₈, m₈, g₈, o₈⟩ => ?_)
  refine WP.seq (WP.mono (outLoop_ok P b₈) fun t₉ ⟨sv₉, rd₉, g₉, m₉⟩ => ?_)
  refine WP.mono (decRet_ok P hD (by omega_using [hFD, hDF]) (rc := rc) (idx := idx) sv₉ (by rw [g₉ .r15 (by simp), g₈ .r15 (by simp), Base.r15 b₇])
    (by rw [g₉ .r17 (by simp), g₈ .r17 (by simp), Base.r17 b₇]) (by rw [g₉ .r20 (by simp), g₈ .r20 (by simp),
      Base.r20 b₇]) (by omega_using [hrc]) (by rw [g₉ .r25 (by simp), g₈ .r25 (by simp), k₇.get .r25, h25])) fun u ⟨svu, rdu, mu, ru⟩ =>
    ⟨svu, rdu.trans rd₉, ?_⟩
  -- The views.
  obtain hS : ∀ {x}, x < oSt → ∀ p ∈ [(oSt, H.S), (oDig, H.FD), (oW, H.W)], x < p.1 ∨ p.1 + p.2 ≤ x :=
    fun hx p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact .inl (by simp only; omega_arith)
  obtain e2 : ∀ x < oSt, view t₂.mem (Sd s) x = view t₁.mem (Sd s) x := fun x hx => s₂ x (by omega_using [hSt, hRs, hx]) (hS hx)
  obtain hlab : Spec.Rsa.bytesAt v.mem (stackArg s 9) (stackArg s 10).toNat = labB s := labB_eq P A.mem
  rw [hlab] at h₂
  obtain hlh : ∀ i < D, view t₂.mem (Sd s) (oDig + i) = (Hs.hash (labB s)).getD i 0 := fun i hi => by
    have := congrArg (fun l => l.getD i 0) h₂
    rw [bytesAt_view, srcB, map_range_getD' _ (by omega_using [hDF, hi])] at this
    rw [this, hHh, hH.hashTake]
    simp [List.getD_eq_getElem?_getD, show i < H.D by omega_using [hD, hi]]
  -- `lHash'`, `lHash` and the scan, on the view after unmasking.
  obtain hc0 : t₃.gpr .r24 = accG (view t₁.mem (Sd s) 0) (fun i => view t₁.mem (Sd s) (1 + D + i))
      (fun i => view t₂.mem (Sd s) (oDig + i)) D := by
    rw [a₃, e2 0 (by omega_using [hSt])]
    exact accG_congr _ D (fun i hi => e2 _ (by omega_using [hFD, hSt, hDF, hi])) (fun _ _ => rfl)
  obtain hsc' : sc = scanS (fun i => view t₁.mem (Sd s) (1 + 2 * D + i)) (accG (view t₁.mem (Sd s) 0)
      (fun i => view t₁.mem (Sd s) (1 + D + i)) (fun i => view t₂.mem (Sd s) (oDig + i)) D) (kk s - (2 * D + 1)) := by
    rw [← hsc, hc0, m₃]
    exact scanS_congr _ _ fun i hi => e2 _ (by omega_using [hk2, ek, hSt, hi])
  rw [hsc'] at hidx
  obtain r24 : t₇.gpr .r24 = sc.2.2 ||| sc.1 := by
    rw [k₇.get .r24, g₆ .r24 (by simp), g₅ .r24 (by simp), a₄]
  obtain hok : t₉.gpr .r26 = mk (rcOf o = 1 ∧ (sc.2.2 ||| sc.1) = 0) := by
    rw [g₉ .r26 (by simp), o₈, r24, ← hRC]
  rw [hsc'] at hok
  -- The buffer.
  obtain hT : ∀ y < 2048, view t₆.mem (Sd s) (oBuf + y) =
      (srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD y 0 := by
    intro y hy
    rw [v₆ _ (by omega_using [hB, hRs, hy])]
    by_cases hyt : y < kk s - (2 * D + 1)
    · rw [ifp ⟨by omega_using [], by omega_using [hyt]⟩, show oBuf + y - oBuf = y by omega_using [], v₅ _ (by omega_using [hFD, hRs, hDF, hy]), ifn (by omega_using [hFD, hB, hDF, hy]), m₄, m₃,
        e2 _ (by omega_using [hk2, ek, hSt, hyt]), srcB, map_range_getD' _ hyt]
    · rw [ifn (by omega_using [hyt]), v₅ _ (by omega_using [hB, hRs, hy]), ifp ⟨by omega_using [], by omega_using [hy]⟩]
      simp [srcB, List.getD_eq_getElem?_getD, hyt]
  obtain hbuf : ∀ i < kk s, view t₇.mem (Sd s) (oBuf + i) =
      (srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD (i + (idx + 1)) 0 := by
    intro i hi
    rw [v₇ _ (by omega_using [hk2, ek, hB, hRs, hi]), shV_eq _ (by omega_using [hk2, ek, hidx']) (fun x h₁ h₂ => by
      rw [hT x (by omega_using [hk2, ek, h₂])]; simp [srcB, List.getD_eq_getElem?_getD, show ¬ x < kk s - (2 * D + 1) by omega_using [h₁]]) hi]
    by_cases hl : i + (idx + 1) < kk s
    · rw [ifp hl, hT _ (by omega_using [hk2, ek, hidx', hi])]
    · rw [ifn hl]; simp [srcB, List.getD_eq_getElem?_getD, show ¬ i + (idx + 1) < kk s - (2 * D + 1) by omega_using [hl]]
  -- `out`, `*msg_len` and the result.
  obtain hu : ∀ x, ¬ (mlR s).Contains x 1 → u.mem x = t₉.mem x := fun x hx => by
    rw [mu]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self (mlR s)) _ (Region.contains_self _ _)) x
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hx)
  obtain hlen : ((Spec.Rsa.bytesAt t₈.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t₈.gpr .r26)).length =
      kk s := by simp [bytesAt_length]
  obtain hout : ∀ i < kk s, u.mem (s.gpr .r3 + BitVec.ofNat 64 i) =
      andB ((srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD (i + (idx + 1)) 0) (t₉.gpr .r26) := by
    intro i hi
    rw [hu _ (fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega_using [ek, hi, this]) (by omega_using [ek, hi])) hc), m₉]
    rw [writeBytes_at _ _ _ (by rw [hlen]; exact hi) (by rw [hlen]; omega_using [ek]), List.getD_eq_getElem?_getD,
      List.getElem?_map, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some, Option.getD_some]
    rw [g₉ .r26 (by simp)]
    congr 1
    rw [m₈, ← hbuf i hi]; show t₇.mem (off (off (Sd s) oBuf) i) = _; rw [off_off]; rfl
  obtain hml : u.mem.readW (s.gpr .r5) 64 = (BitVec.ofNat 64 (kk s) - BitVec.ofNat 64 (2 * D + 2) -
      BitVec.ofNat 64 idx) &&& t₉.gpr .r26 := by
    rw [mu, Mem.readW_writeW_self64, show s.gpr .r7 = BitVec.ofNat 64 (kk s) from
      (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm]
  rw [hok] at hout hml ru

  exact dec_written hGv hHv hHl (by omega_using [hk]) hk2 v₁ hlh (fun em he => by
      have := A.em; rw [hO, he] at this; exact this.symm)
    hidx (by rcases hidx' with h | h; exact .inl h; exact .inr h) hout hml (by rw [ru, hRC])

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end


/-!
# RSAES-OAEP decryption on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The entry, the private
operation (`priv_ok`), the check of `k ≥ 2 hLen + 2` (public), then either
zeros and the result `r = 2 ? 2 : 0` (`decFail_ok`, which is what `decOut`
says for a too short `k`) or the decoding (`decMain_ok`), and the restores:
RSAES-OAEP-DECRYPT (RFC 8017 §7.1.2), with MGF1's hash function the
table's. `code_correct`: the function against its contract, for the tables
of `vs` (`tab_ofD`: the table is one of them, whose hash function it
names).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_sub wp_lsr wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes)
open VG.Proof.RsaOaep (decOut decOut_short)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.MdHashTable.PPC64LE (MVar tables fns3 Coh)

/-- The result and the outputs, from the entry state `s`. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ Spec.RsaOaep.writtenDecrypt s'.mem (s.gpr .r3) (s.gpr .r5) (kk s) ((s'.gpr .r3).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ Spec.RsaOaep.writtenDecrypt t.mem (s.gpr .r3) (s.gpr .r5) (kk s) ((t.gpr .r3).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

theorem AfterPriv.only {pc : Bool} {s v v' : State} {rs : List Reg} (A : AfterPriv s v) (P : PreD pc s) (o : Only rs v v')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : AfterPriv s v' := by
  have hm : v'.mem = v.mem := o.mem
  have b := A.base
  rw [← hm] at b
  exact ⟨b.only (fitsM P) o hrs, hm ▸ A.mem, hm ▸ A.em⟩

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem decTail_D {G G' : Hash} (hD : G.D = G'.D) (f : Fns) : decTail G f = decTail G' f := by
  simp only [Dec.decTail, Dec.decMain, Dec.chkK, Dec.accLh, Dec.scan, Dec.tArgs, Dec.copyT, Dec.decRet, seedArgs,
    dbArgs, hD]

/-- `EM` too short for the hash: what decryption returns, from the private
operation's result. -/
theorem decOut_short' {Hs Gs : Spec.Mgf1.Hash} {lab : List Byte} {o : Spec.Rsa.Outcome} {k : Nat}
    (hl : ∀ em, o = .ok em → em.length = k) (hk : k < 2 * Hs.len + 2) :
    decOut Hs Gs lab o = if rcOf o = 2 then .fault else .invalid := by
  rw [decOut_short hl hk]
  cases o <;> rfl

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
  {pc : Bool} {f : Fns} {s : State} (P : PreD pc s) (T : TabS G f 16 (SD s) s (stackArg s 16))
  (TL : TabS H f 15 (SD s) s (stackArg s 15))
include hH hG hHh hHl hHv hGh hGl hGv P T TL

omit hH hG hHh hHv hGh hGl hGv T TL in
theorem fail_done {v : State} (A : AfterPriv s v) (hk : kk s < 2 * H.D + 2) :
    WP isa decFail v (Done Hs Gs s) := by
  obtain hrc := rcOf_le (privO s)
  refine WP.mono (decFail_ok P A.base hrc) fun u ⟨sv, _, hm, h3⟩ => ⟨sv, ?_⟩
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  obtain hl : ∀ em, privO s = .ok em → em.length = kk s := fun em he => by
    have := A.em; rw [he] at this; simp only [emOf] at this; rw [← this, bytesAt_length]
  rw [decOut_short' hl (by rw [hHl]; exact hk)]
  obtain hout : Spec.Rsa.bytesAt u.mem (s.gpr .r3) (kk s) = List.replicate (kk s) 0 := by
    obtain e := bytesAt_writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0)
      (by rw [List.length_replicate]; omega_using [ek])
    rw [List.length_replicate] at e
    rw [← e, hm]
    obtain f : Frame [mlR s] (writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0))
        ((writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0)).writeW (s.gpr .r5) (0#64)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    exact f _ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega_using [ek, hi, this]) (by omega_using [ek, hi])) hc)
  obtain hml : u.mem.readW (s.gpr .r5) 64 = 0 := by rw [hm, Mem.readW_writeW_self64]; rfl
  obtain hrc2 := rcOf_le (privO s)
  by_cases h2 : rcOf (privO s) = 2
  · rw [ifp h2]; exact ⟨by rw [h3, ifp h2]; decide, hout, hml⟩
  · rw [ifn h2]; exact ⟨by rw [h3, ifn h2]; decide, hout, hml⟩

omit hH hG hHh hHl hHv hGh hGl hGv T TL in
/-- The check of `k`: in `r3`, whether it is too short. -/
theorem chk_ok (hD64 : H.D ≤ 64) {v : State} (A : AfterPriv s v) :
    WP isa (.block (Dec.chkK H)) v fun v' => AfterPriv s v' ∧ (v'.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2) := by
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  obtain e7 : s.gpr .r7 = BitVec.ofNat 64 (kk s) := ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  refine wp_li (by omega_using [hD64]) fun v₁ o₁ e₁ => wp_sub fun v₂ o₂ e₂ => wp_lsr fun v₃ o₃ e₃ => wp_nil ?_
  obtain k₃ : Only [.r3] v v₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨A.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, o₁.get .r15, Base.r15 A.base, e7]
  exact ne_zero_ltBit (by omega_using [hk2, ek]) (by omega_using [hD64])

/-- The branch on the check of `k`. -/
theorem ite_done {v : State} (A : AfterPriv s v) (hsy : v.syms = s.syms)
    (r3 : (v.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2)) :
    WP isa (.ite (.nonzero .d .r3) decFail (decMain H f)) v (Done Hs Gs s) :=
  WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P A (by rw [r3] at hc; simpa using hc))
    (fun hc => WP.mono (decMain_ok P hH hG hHh hHl hHv hGh hGl hGv T TL A hsy (by rw [r3] at hc; simp at hc; omega_using [hc]))
      fun u ⟨sv, _, hw⟩ => ⟨sv, hw⟩)

theorem checks_done {v : State} (A : AfterPriv s v) (hsy : v.syms = s.syms) :
    WP isa (.block (Dec.chkK H)) v fun v' =>
      WP isa (.ite (.nonzero .d .r3) decFail (decMain H f)) v' (Done Hs Gs s) :=
  WP.mono_syms (chk_ok P hH.hD64 A) fun _ ⟨A', r3⟩ y => ite_done hH hG hHh hHl hHv hGh hGl hGv P T TL A' (y.trans hsy) r3

omit hH hG hHh hHl hHv hGh hGl hGv P T TL in
/-- `writtenDecrypt` reads the memory only in the output and its length. -/
private theorem writtenDecrypt_lost {m m' : Mem} {out len : Addr} {k : Nat} {r r' : BitVec 32}
    {o : Spec.Rsa.Outcome} (hr : r' = r) (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k)
    (hl : m'.readW len 64 = m.readW len 64) (h : Spec.RsaOaep.writtenDecrypt m out len k r o) :
    Spec.RsaOaep.writtenDecrypt m' out len k r' o := by
  subst hr
  cases o <;> simp only [Spec.RsaOaep.writtenDecrypt, hb, hl] at h ⊢ <;> exact h

theorem code_ok (X : pc = true → PreXD s) (hl : H.D ∈ lens) : WP isa (decryptG pc f) s (Post Hs Gs s) := by
  have hD64 := hH.hD64
  refine WP.alloc (by decide) (by have := P.sp1; rw [stackBytes_eq] at this; unfold frameBytes; omega_using [this]) ?_
  refine WP.seq (WP.mono_syms (entry_ok P) fun t E y₁ => ?_)
  refine WP.seq (WP.mono_syms (priv_ok P X E) fun v A y₂ => ?_)
  -- The label's hash function's digest length to `r3`.
  obtain TL' := tabS_wmL P TL A.mem
  refine WP.seq (WP.of_syms ?_)
  show WP isa (.block (tword .r3 15 6 ++ [])) v _
  refine wp_tword TL' A.base (k := 6) (by decide) (d := .r3) (by decide) fun v₁ o₁ e₁ => wp_nil fun y₃ => ?_
  obtain e3 : v₁.gpr .r3 = BitVec.ofNat 64 H.D := e₁.trans TL'.d
  -- The code for that length.
  refine WP.seq (byLen_ok (D := H.D) (by omega_using [hD64])
    (F := fun u => AfterPriv s u ∧ u.syms = s.syms ∧ u.gpr .r3 = BitVec.ofNat 64 H.D)
    (fun _ h => h.2.2) (fun u u' ⟨A', y', r3'⟩ o y => ⟨A'.only P o, y.trans y', by rw [o.get .r3]; exact r3'⟩) ?_
    hl (fun x hx => (lens_certs x hx).1) v₁ ⟨A.only P o₁, y₃.trans (y₂.trans y₁), e3⟩)
  intro u ⟨A', y', _⟩
  rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
  -- The `free` loses the frame's bytes, which lie apart from the output and its length.
  have hsub : Region.Sub ⟨s.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩ (kD s) :=
    Offset.sub_below _ (by unfold stackBytes; omega_using []) (by unfold stackBytes; omega_using [])
  exact WP.seq (WP.mono (checks_done hH hG hHh hHl hHv hGh hGl hGv P T TL A' y') fun v' h => WP.mono h
    fun t' ⟨sv, res⟩ => WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ mL _ fl => ⟨abiPreserved_lost habi,
      writtenDecrypt_lost (m := (freed frameBytes w).mem) (r := ((freed frameBytes w).gpr .r3).setWidth 32) rfl
        (by
          rw [freed_mem]
          exact List.map_congr_left fun i hi => lost_byte fl (R := oR s) (P.ko.sub_left hsub).symm
            (by show i < (s.gpr .r4).toNat; have h₁ : i < (s.gpr .r7).toNat := List.mem_range.mp hi
                have h₂ := P.ok; omega_using [h₁, h₂]))
        (by
          rw [freed_mem]
          exact fl.readW (r := mlR s) (by simp only [Region.Contains]; rw [BitVec.sub_self]; decide)
            (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (P.kml.sub_left hsub).symm)
            (by decide))
        (by rw [freed_mem, freed_gpr, hm, h3]; exact res)⟩)

end

/-- The label's hash function's table, on entry, if it is `w`'s: what its
calls need of it. -/
theorem tabS_entryDL {vs : List MVar} (hc : Coh vs) {pc : Bool} {s : State} (P : PreD pc s)
    (hpw : (Proof.MdHashTable.PPC64LE.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : MVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (Proof.MdHashTable.PPC64LE.tableOf w))) :
    TabS w.H (fns3 vs) 15 (SD s) s (stackArg s 15) := by
  refine Proof.MdHashTable.PPC64LE.tabS_of (by decide) rfl (A := aR pc s) (by rw [P.hrd]; exact aR_mem)
    (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; exact List.mem_append_right _ (List.mem_cons_self ..)) (P.ktl.sub_left kR_sub)
    (P.stl.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by split <;> omega_using [])

/-- MGF1's table, on entry, if it is `w`'s: what MGF1 needs of it. -/
theorem tabS_entryD {vs : List MVar} (hc : Coh vs) {pc : Bool} {s : State} (P : PreD pc s)
    (hpw : (Proof.MdHashTable.PPC64LE.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : MVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s (Proof.MdHashTable.PPC64LE.tableOf w))) :
    TabS w.H (fns3 vs) 16 (SD s) s (stackArg s 16) := by
  refine Proof.MdHashTable.PPC64LE.tabS_of (by decide) rfl (A := aR pc s) (by rw [P.hrd]; exact aR_mem)
    (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (P.kt.sub_left kR_sub)
    (P.st.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by split <;> omega_using [])

/-- The tables, on entry: each one of the tables of `vs`, which names its
hash function and holds what the calls through it need. -/
theorem tab_ofD {vs : List MVar} (hc : Coh vs) {s : State} (h : (decSpec (tables vs)).pre s) :
    ∃ w₁ ∈ vs, ∃ w ∈ vs, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some w₁.l.G ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some w.l.G ∧
      TabS w₁.H (fns3 vs) 15 (SD s) s (stackArg s 15) ∧ TabS w.H (fns3 vs) 16 (SD s) s (stackArg s 16) := by
  obtain ⟨⟨T₁, hT₁, hh₁⟩, ⟨T, hT, hh⟩, hpw⟩ := spec_tabD h
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain hpw' := hpw.sublist (List.sublist_append_left _ _)
  obtain P := preD_of h
  exact ⟨w₁, hw₁, w, hw, Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh₁).2.2.2,
    Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh).2.2.2,
    tabS_entryDL hc P hpw' hw₁ hh₁, tabS_entryD hc P hpw' hw hh⟩

/-- The correctness of `vg_rsa_oaep_decrypt`, against its contract, for the
tables of `vs`. -/
theorem code_correct {vs : List MVar} (hc : Coh vs) (s : State) (h : (decSpec (tables vs)).pre s) :
    ∃ t s', Exec isa (decrypt (fns3 vs)) s t s' ∧ abiPreserved s s' ∧ (decSpec (tables vs)).post s s' := by
  obtain ⟨w₁, -, w, -, hH, hG, TL, T⟩ := tab_ofD hc h
  obtain P : PreD false s := preD_of h
  obtain ⟨t, s', he, habi, hr⟩ := code_ok w₁.l.ok w.l.ok w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len w.l.valid
    P T TL nofun w₁.l.lens_mem
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpec
  rw [e]
  sig_post [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Abi.withTables, abi, argRegs, stackArgs_seventeen, List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [Proof.RsaOaep.decrypt_eq (by rw [bytesAt_length, bytesAt_length])]
  exact hr

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-! ### `RsaOaep.PPC64LE.Dc.CTBase`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: two runs

Untrusted: everything here is checked by Lean. Two runs are compared through
an anchor `a`, the first run's entry state: `PubD a s` says the entry state
`s` has `a`'s public data (`pubD_of`, from the shared contract's). After the
private operation, `DX a t` says `t` has `Base` for the decoding from such an
entry state, whose working space and `k`, `out`, `msg_len` and the label in
`r14`–`r19` are then `a`'s (`DX.pins`), while `r20` holds that run's own
result. The shared code compares runs whose `Base` has the same functions
of the base state: the working space at `stackArg x 13` (`SX`) and the
values of `r15`–`r23` read from `x`, with the result in its `r0` (`VX`); the
base state of a run is its entry state with the memory after the private
operation and the result in `r0` (`bx`, `toX`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Pins)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The shared contract's public data, by name. -/
structure PubD (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = a.gpr r
  args : ∀ i < 17, stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r6) (a.gpr .r7).toNat
  e : Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat

/-- The contract's public data: `PubD`, the tables' functions at the same
addresses, and the same tables held at both tables' addresses. -/
theorem pubD_of {ts : List FnTable} {s₁ s₂ : State} (h : (decSpec ts).pub s₁ s₂) :
    PubD s₁ s₂ ∧ (∀ f ∈ (ts.map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 16) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 16) (FnTable.words isa s₂ T)) := by
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpec at h
  rw [e] at h
  sig_pub [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_seventeen, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htabL, htab, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16⟩ := h
  simp only [List.map_append] at hl
  obtain ⟨hn, he⟩ := List.append_inj hl (by simp [bytesAt_length, h7])
  have inj := fun {x y : List Byte} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm⟩,
    fun f hf => hsy f (List.mem_append_left _ hf), fun T hT => htabL _ _ rfl rfl T hT,
    fun T hT => htab _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm, a13.symm, a14.symm, a15.symm, a16.symm]

theorem pubD_refl (s : State) : PubD s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- With `pc`, `pre`'s public data: its address, its length and what the
call may leak of it. -/
def PubP (a s : State) : Prop :=
  stackArg s 17 = stackArg a 17 ∧ stackArg s 18 = stackArg a 18 ∧
    Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .r7).toNat =
      Spec.Rsa.privatePrecomputedLeak a.mem (stackArg a 17) (a.gpr .r7).toNat

/-- With `pc`, `pre`'s facts and public data. -/
abbrev XP (pc : Bool) (a s : State) : Prop := pc = true → PreXD s ∧ PubP a s

/-! ## The base state for the shared code -/

/-- The entry state `s` with memory `m` and `rc` in `r0`. -/
def bx (s : State) (m : Mem) (rc : Nat) : State :=
  { s with mem := m, gpr := fun r => if r = .r0 then BitVec.ofNat 64 rc else s.gpr r }

/-- The working space, of the base state. -/
abbrev SX : State → Addr := fun x => stackArg x 13

/-- `r15`–`r23`, of the base state. -/
def VX (x : State) : Reg → BitVec 64 := vD x (x.gpr .r0).toNat

/-- What the shared code needs of the base state. -/
def PreX (x : State) : Prop := Fits SX x

/-- The base state's public data: the stack pointer and the working space. -/
def PubX (a x : State) : Prop := x.sp = a.sp ∧ stackArg x 13 = stackArg a 13

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} (hm : Frame [kD s, scR s] s.mem m) (rc : Nat)
include P hm

/-- The stack arguments, in the base state. -/
theorem stackArg_bx {i : Nat} (hi : i < 17) : stackArg (bx s m rc) i = stackArg s i := by
  show m.readW (stackArgAddr s i) 64 = s.mem.readW (stackArgAddr s i) 64
  exact hm.readW (in_aR hi) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact P.ka.symm
    · exact P.sa.symm) (by decide)

/-- `Base` for the shared code, from the decoding's. -/
theorem toX (hrc : rc ≤ 2) {t : State} (b : Base (SD s) (VD s rc) (withMem s m) t) :
    PreX (bx s m rc) ∧ Base SX VX (bx s m rc) t := by
  have h13 : SX (bx s m rc) = Sd s := stackArg_bx P hm rc (i := 13) (by decide)
  have g : ∀ r, r ≠ .r0 → (bx s m rc).gpr r = s.gpr r := fun r hr => by simp [bx, hr]
  have f := fits P (s' := bx s m rc) rfl rfl
  have eSC : SC SX (bx s m rc) = SC (SD s) (withMem s m) := by simp only [SC, h13]
  refine ⟨⟨f.sp1, by rw [h13]; exact f.sc, by rw [eSC]; exact f.ksc, by rw [h13]; exact f.wS⟩,
    ⟨⟨b.sv.sp, b.sv.wr, fun r hr => by rw [g r (by revert r; decide)]; exact b.sv.hi r hr,
      fun p hp => (b.sv.sv p hp).trans (g p.1 (by revert p; decide)).symm, b.sv.ls⟩, b.rd, b.r14.trans h13.symm,
      fun r hr => ?_, by rw [eSC]; exact b.mem⟩⟩
  have e0 : ((bx s m rc).gpr .r0).toNat = rc := by
    show (BitVec.ofNat 64 rc).toNat = rc
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hrc])]
  rw [b.vs r hr]
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [VX, vD, e0, g _ (show Reg.r7 ≠ .r0 by decide), g _ (show Reg.r3 ≠ .r0 by decide),
      g _ (show Reg.r5 ≠ .r0 by decide), g _ (show Reg.r21 ≠ .r0 by decide), g _ (show Reg.r22 ≠ .r0 by decide),
      g _ (show Reg.r23 ≠ .r0 by decide), stackArg_bx P hm rc (i := 9) (by decide),
      stackArg_bx P hm rc (i := 10) (by decide)]

end

/-! ## After the private operation -/

/-- `t` has the decoding's `Base` from an entry state with `a`'s public data. -/
def DX (a t : State) : Prop :=
  ∃ pc s m, PreD pc s ∧ PubD a s ∧ Frame [kD s, scR s] s.mem m ∧
    Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t

/-- What `DX` fixes, from the anchor. -/
theorem DX.pins {a t : State} (h : DX a t) :
    t.sp = fb a ∧ t.gpr .r14 = stackArg a 13 ∧ t.gpr .r15 = a.gpr .r7 ∧ t.gpr .r16 = a.gpr .r3 ∧
      t.gpr .r17 = a.gpr .r5 ∧ t.gpr .r18 = stackArg a 9 ∧ t.gpr .r19 = stackArg a 10 := by
  obtain ⟨_, s, m, P, p, hm, b⟩ := h
  exact ⟨by rw [b.sp]; show fb s = fb a; rw [fb, fb, p.sp], b.r14.trans (p.args 13 (by decide)),
    by rw [Base.r15 b, p.g _ (by decide)], by rw [Base.r16 b, p.g _ (by decide)], by rw [Base.r17 b, p.g _ (by decide)],
    by rw [Base.r18 b, p.args 9 (by decide)], by rw [Base.r19 b, p.args 10 (by decide)]⟩

/-- The registers `DX` fixes are the same in both runs. -/
theorem dx_pins {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → DX (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ [Reg.r14, .r15, .r16, .r17, .r18, .r19] := by decide) : Pins Φ rs :=
  fun x t₁ t₂ h₁ h₂ => by
    obtain ⟨s₁, a₁, b₁, c₁, d₁, e₁, f₁⟩ := (h x t₁ h₁).pins
    obtain ⟨s₂, a₂, b₂, c₂, d₂, e₂, f₂⟩ := (h x t₂ h₂).pins
    refine ⟨s₁.trans s₂.symm, fun r hr => ?_⟩
    have := hrs r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm, d₁.trans d₂.symm, e₁.trans e₂.symm,
      f₁.trans f₂.symm]

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-! ### `RsaOaep.PPC64LE.Dc.CTLabel`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: the shared code's base state

Untrusted: everything here is checked by Lean. The shared code's base state
has the entry's public data (`pubX_bx`); the label's hash is through its table,
in two runs `hashLabelT_ct` (`Proof/RsaPss/PPC64LE/CTTab.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two two_post wp_li wp_addi wp_mov wp_nil)

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} (hm : Frame [kD s, scR s] s.mem m) {rc : Nat} (hrc : rc ≤ 2)
include P hm hrc

omit hrc in
theorem pubX_bx {a : State} (p : PubD a s) : PubX a (bx s m rc) :=
  ⟨p.sp, (stackArg_bx P hm rc (by decide)).trans (p.args 13 (by decide))⟩

end

theorem off13 {a s : State} (p : PubD a s) (o : Nat) : off (stackArg a 13) o = off (Sd s) o := by
  show off (stackArg a 13) o = off (stackArg s 13) o
  rw [p.args 13 (by decide)]

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-! ### `RsaOaep.PPC64LE.Dc.CTPriv`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: the private operation, twice

Untrusted: everything here is checked by Lean. `priv_ct`: two runs of the
private operation from entry states with the same public data leak alike:
its frame's arguments by the taint analysis, and the call of
`vg_rsa_private_checked` by its constant time (`RelCT.callEx`), whose public
data at the call (`priv_pub`) are the entry's: the pointers and lengths, the
modulus and the public exponent. Its result then differs between the runs,
in `r20` (`DX`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_alloc)

theorem psa_pub {a s : State} (p : PubD a s) {i : Nat} (hi : i < 12) : psa s i = psa a i := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p.g .r10 (by decide)
  · exact p.args 0 (by decide)
  · exact p.args 1 (by decide)
  · exact p.args 2 (by decide)
  · exact p.args 3 (by decide)
  · exact p.args 4 (by decide)
  · exact p.args 5 (by decide)
  · exact p.args 6 (by decide)
  · exact p.args 7 (by decide)
  · exact p.args 8 (by decide)
  · exact congrArg (· + BitVec.ofNat 64 oRsa) (p.args 13 (by decide))
  · exact congrArg (fun x : BitVec 64 => BitVec.ofNat 64 (x.toNat - 1024)) (p.args 14 (by decide))

/-- At the call, from an entry state with `a`'s public data. -/
def APriv (pc : Bool) (a u : State) : Prop := ∃ s, PreD pc s ∧ PubD a s ∧ AtPriv pc s u ∧ XP pc a s

/-- The public data at the call, but `pre`'s leak. -/
theorem priv_facts {pc : Bool} {a s₁ s₂ u₁ u₂ : State} (P₁ : PreD pc s₁) (p₁ : PubD a s₁) (A₁ : AtPriv pc s₁ u₁)
    (P₂ : PreD pc s₂) (p₂ : PubD a s₂) (A₂ : AtPriv pc s₂ u₂) :
    (callE pc s₁ u₁).sp = (callE pc s₂ u₂).sp ∧
      (∀ r ∈ argRegs, (callE pc s₁ u₁).gpr r = (callE pc s₂ u₂).gpr r) ∧
      (∀ i < 12, stackArg (callE pc s₁ u₁) i = stackArg (callE pc s₂ u₂) i) ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r5) ((callE pc s₁ u₁).gpr .r6).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r5) ((callE pc s₂ u₂).gpr .r6).toNat ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r7) ((callE pc s₁ u₁).gpr .r8).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r7) ((callE pc s₂ u₂).gpr .r8).toNat := by
  have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
  have hb := fun {s u : State} (A : AtPriv pc s u) {p : Addr} {len : Nat}
    (hd : (kD s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hl
  refine ⟨by rw [callE_sp, callE_sp, A₁.sp, A₂.sp, pb, pb, fb, fb, p₁.sp, p₂.sp], fun r hr => ?_,
    fun i hi => by rw [callE_stackArg A₁ (lt_nCall hi), callE_stackArg A₂ (lt_nCall hi), psa_pub p₁ hi,
      psa_pub p₂ hi], ?_, ?_⟩
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, Sd, Sd, p₁.args 13 (by decide), p₂.args 13 (by decide)]
    · rw [A₁.r4, A₂.r4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r5, A₂.r5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r6, A₂.r6, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r7, A₂.r7, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r8, A₂.r8, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r9, A₂.r9, p₁.args 11 (by decide), p₂.args 11 (by decide)]
    · rw [A₁.r10, A₂.r10, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [m, m, callE_gpr _ _ (r := .r5), callE_gpr _ _ (r := .r6), callE_gpr _ _ (r := .r5),
      callE_gpr _ _ (r := .r6), A₁.r5, A₁.r6, A₂.r5, A₂.r6, hb A₁ P₁.kn (by have := P₁.wn; omega_using []),
      hb A₂ P₂.kn (by have := P₂.wn; omega_using []), p₁.n, p₂.n]
  · rw [m, m, callE_gpr _ _ (r := .r7), callE_gpr _ _ (r := .r8), callE_gpr _ _ (r := .r7),
      callE_gpr _ _ (r := .r8), A₁.r7, A₁.r8, A₂.r7, A₂.r8, hb A₁ P₁.ke (by have := P₁.we; omega_using []),
      hb A₂ P₂.ke (by have := P₂.we; omega_using []), p₁.e, p₂.e]

/-- With `pc`, the call's two more stack arguments, `pre` and `pre_len`, are
the anchor's. -/
theorem psa_pubP {a s : State} (x : PubP a s) {i : Nat} (hi : 12 ≤ i) (hi' : i < 14) : psa s i = psa a i := by
  rcases (by omega_using [hi, hi'] : i = 12 ∨ i = 13) with rfl | rfl
  · exact x.1
  · exact x.2.1

/-- With `pc`, what the call may leak of `pre`, as on entry. -/
theorem pre_leak {s u : State} (X : PreXD s) (A : AtPriv true s u) :
    Spec.Rsa.privatePrecomputedLeak (callE true s u).mem (stackArg (callE true s u) 12)
        ((callE true s u).gpr .r6).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .r7).toNat := by
  have pwl : Spec.Rsa.precomputedWords (s.gpr .r7).toNat ≤ (stackArg s 18).toNat := by
    rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide), psa,
    callE_gpr (pc := true) s u (r := .r6), A.r6]
  refine congrArg (List.map _) ?_
  have subPre : Region.Sub ⟨stackArg s 17, 8 * Spec.Rsa.precomputedWords (s.gpr .r7).toNat⟩ (preR s) :=
    fun _ hx => by simp only [Region.Contains] at hx ⊢; omega_using [pwl, hx]
  exact VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact X.kP.symm.sub_left subPre) (by have := X.wP; omega_using [pwl, this])

theorem call_ct (pc : Bool) : RelCT isa (Two (APriv pc)) (privCall pc) fun _ _ => True := by
  cases pc with
  | false =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      Rsa.PPC64LE.Priv.code_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, P₁, p₁, A₁, -⟩ := h₁
    obtain ⟨s₂, P₂, p₂, A₂, -⟩ := h₂
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts P₁ p₁ A₁ P₂ p₂ A₂
    exact ⟨callRd false s₁, callWr s₁, callRd false s₂, callWr s₂, Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₂ A₂), Rsa.PPC64LE.Priv.pub_of hsp hr ha hn he,
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
  | true =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      Rsa.PPC64LE.Priv.codeP_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, P₁, p₁, A₁, x₁⟩ := h₁
    obtain ⟨s₂, P₂, p₂, A₂, x₂⟩ := h₂
    obtain ⟨X₁, q₁⟩ := x₁ rfl
    obtain ⟨X₂, q₂⟩ := x₂ rfl
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts P₁ p₁ A₁ P₂ p₂ A₂
    refine ⟨callRd true s₁, callWr s₁, callRd true s₂, callWr s₂,
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₁ A₁) (preX_at P₁ X₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₂ A₂) (preX_at P₂ X₂ A₂),
      Rsa.PPC64LE.Priv.pub_ofP hsp hr (fun i hi => ?_) hn he
        (by rw [pre_leak X₁ A₁, pre_leak X₂ A₂, q₁.2.2, q₂.2.2]),
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
    by_cases h12 : i < 12
    · exact ha i h12
    · rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, psa_pubP q₁ (by omega_using [h12]) hi, psa_pubP q₂ (by omega_using [h12]) hi]

/-- After the entry, from an entry state with `a`'s public data. -/
def AEnt (pc : Bool) (a t : State) : Prop := ∃ s, PreD pc s ∧ PubD a s ∧ Entered s t ∧ XP pc a s

theorem aEnt_sp {pc : Bool} {a t : State} (h : AEnt pc a t) : t.sp = fb a :=
  let ⟨_, _, p, E, _⟩ := h; by rw [E.sv.sp, fb, fb, p.sp]

/-- The private operation, from the entry to `DX`. -/
theorem priv_ct (pc : Bool) : RelCT isa (Two (AEnt pc)) (priv pc) fun _ _ => True := by
  unfold priv
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, PreD pc s ∧ PubD a s ∧ w.sp = fb s ∧
      WP isa (.block [.lsr .w .r20 .r3 0]) w (AfterPriv s))
    (two_alloc (R := fun _ _ => True) (fun a t₁ t₂ h₁ h₂ => ⟨(aEnt_sp h₁).trans (aEnt_sp h₂).symm, fun _ h => nomatch h⟩) ?_)
    fun a t ⟨s, P, p, E, x⟩ => WP.mono (privF_ok P (fun h => (x h).1) E) fun w h => ⟨s, P, p, h⟩)
    (lsr_taint fun a w₁ w₂ ⟨s₁, _, p₁, e₁, _⟩ ⟨s₂, _, p₂, e₂, _⟩ =>
      ⟨by rw [e₁, e₂, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  refine two_seq (Ψ := APriv pc) (privArgs_taint pc fun a u₁ u₂ ⟨t₁, h₁, e₁⟩ ⟨t₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, aEnt_sp h₁, aEnt_sp h₂], fun _ h => nomatch h⟩)
    (fun a u ⟨t, ⟨s, P, p, E, x⟩, e⟩ => by
      subst e; exact WP.mono (privArgsG_ok P E) fun u' A => ⟨s, P, p, A, x⟩)
    (call_ct pc)

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end


/-!
# RSAES-OAEP decryption on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data leak alike: the code between the calls by the
taint analysis (`Dc/CTBlocks`), the private operation by its constant time
(`priv_ct`), the hash functions' calls through the tables by their
contracts (`hashLabelT_ct`, MGF1's `mgfXorT_ctS`, with each table at the
same address and its functions at the same addresses: `DXT`), the branch on
the label's digest length (`byLen_ct`) and that on the public `k`
(`two_ite`); what each run satisfies between them follows from correctness. The scan's index,
the shift's count and the private operation's result differ between the
runs, but only as data.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi wp_nil
  eval_nonzero)
open VG.Proof.RsaOaep (scan_idx)

/-- `k` passed the check, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 ≤ (a.gpr .r7).toNat

theorem hk_s {D : Nat} {a s : State} (p : PubD a s) (h : HK D a) : 2 * D + 2 ≤ kk s := by
  show 2 * D + 2 ≤ (s.gpr .r7).toNat; rw [p.g .r7 (by decide)]; exact h

/-- `G`'s functions at the anchor's addresses. -/
def SymG (G : Hash) (a s : State) : Prop :=
  s.syms G.initN = a.syms G.initN ∧ s.syms G.updN = a.syms G.updN ∧ s.syms G.finN = a.syms G.finN

/-- Both tables on entry: MGF1's, `G`'s, and the label's hash function's,
`H`'s. -/
def TT (G H : Hash) (f : Fns) (s : State) : Prop :=
  TabS G f 16 (SD s) s (stackArg s 16) ∧ TabS H f 15 (SD s) s (stackArg s 15)

/-- Both tables' functions at the anchor's addresses. -/
def SymGH (G H : Hash) (a s : State) : Prop := SymG G a s ∧ SymG H a s

/-- `DX`, with both tables on entry, their functions at the anchor's
addresses, and the entry's addresses of statics. -/
def DXT (G H : Hash) (f : Fns) (a t : State) : Prop :=
  ∃ pc s m, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ Frame [kD s, scR s] s.mem m ∧
    Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t ∧ t.syms = s.syms

theorem DXT.dx {G H : Hash} {f : Fns} {a t : State} (h : DXT G H f a t) : DX a t :=
  let ⟨_, s, m, P, _, p, _, hm, b, _⟩ := h; ⟨_, s, m, P, p, hm, b⟩

theorem DXT.only {G H : Hash} {f : Fns} {a t t' : State} {rs : List Reg} (h : DXT G H f a t) (o : Only rs t t')
    (hy : t'.syms = t.syms) (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : DXT G H f a t' :=
  let ⟨_, s, m, P, T, p, y, hm, b, sy⟩ := h; ⟨_, s, m, P, T, p, y, hm, b.only (fitsM P) o hrs, hy.trans sy⟩

/-- The base state's precondition, with MGF1's table. -/
def PreXT (G : Hash) (f : Fns) (x : State) : Prop := PreX x ∧ TabS G f 16 SX x (stackArg x 16)

/-- The base state's public data, with MGF1's table's address and `G`'s
functions' addresses. -/
def PubXT (G : Hash) (a x : State) : Prop := PubX a x ∧ stackArg x 16 = stackArg a 16 ∧ SymG G a x

theorem okXT (G : Hash) (f : Fns) : OkS SX (PreXT G f) (PubXT G) := ⟨fun h => h.1, fun p => p.1.1, fun p => p.1.2⟩

theorem tabXT (G : Hash) (f : Fns) : TabA G f 16 SX (PreXT G f) (PubXT G) :=
  ⟨fun h => h.2, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2⟩

/-- What the label's hash needs of the base state: the label readable, apart
from what the hash function writes in `scratch` and from the stack. -/
def LabX (H : Hash) (x : State) : Prop :=
  (⟨stackArg x 9, (stackArg x 10).toNat⟩ : Region) ∈ x.rd ∧
    Region.Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ⟨off (SX x) oSt, H.S⟩ ∧
    Region.Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ⟨off (SX x) oW, H.W⟩ ∧
    (cR x).Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ∧ (stackArg x 10).toNat < 2 ^ 64

/-- The base state's precondition, with both tables and the label. -/
def PreXL (G H : Hash) (f : Fns) (x : State) : Prop :=
  PreXT G f x ∧ TabS H f 15 SX x (stackArg x 15) ∧ LabX H x

/-- The base state's public data, with both tables' addresses, their
functions' addresses, and the label. -/
def PubXL (G H : Hash) (a x : State) : Prop :=
  PubXT G a x ∧ stackArg x 15 = stackArg a 15 ∧ SymG H a x ∧ stackArg x 9 = stackArg a 9 ∧
    stackArg x 10 = stackArg a 10

theorem okXL (G H : Hash) (f : Fns) : OkS SX (PreXL G H f) (PubXL G H) :=
  ⟨fun h => h.1.1, fun p => p.1.1.1, fun p => p.1.1.2⟩

theorem tabXL (G H : Hash) (f : Fns) : TabA H f 15 SX (PreXL G H f) (PubXL G H) :=
  ⟨fun h => h.2.1, fun p => p.2.1, fun p => p.2.2.1.1, fun p => p.2.2.1.2.1, fun p => p.2.2.1.2.2⟩

/-- The base state of a run for the label's hash, from the decoding's. -/
theorem DXT.toL {G H : Hash} (hH : HashOK H) {f : Fns} {a t : State} (h : DXT G H f a t) :
    BT SX VX (PreXL G H f) (PubXL G H) a t := by
  obtain ⟨_, s, m, P, T, p, y, hm, b, sy⟩ := h
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  have a16 : stackArg (bx s m (rcOf (privO s))) 16 = stackArg s 16 := stackArg_bx P hm _ (by decide)
  have a15 : stackArg (bx s m (rcOf (privO s))) 15 = stackArg s 15 := stackArg_bx P hm _ (by decide)
  have a9 : stackArg (bx s m (rcOf (privO s))) 9 = stackArg s 9 := stackArg_bx P hm _ (by decide)
  have a10 : stackArg (bx s m (rcOf (privO s))) 10 = stackArg s 10 := stackArg_bx P hm _ (by decide)
  have h13 : SX (bx s m (rcOf (privO s))) = Sd s := stackArg_bx P hm _ (i := 13) (by decide)
  refine ⟨_, ⟨⟨pX, by rw [a16]; exact tabS_to P T.1 hm rfl rfl rfl (by simp only [SC, h13])⟩,
    by rw [a15]; exact tabS_toL P T.2 hm rfl rfl rfl (by simp only [SC, h13]), ?_⟩,
    ⟨⟨pubX_bx P hm p, a16.trans (p.args 16 (by decide)), y.1⟩, a15.trans (p.args 15 (by decide)), y.2,
      a9.trans (p.args 9 (by decide)), a10.trans (p.args 10 (by decide))⟩, bX, sy⟩
  show LabX H (bx s m (rcOf (privO s)))
  unfold LabX
  rw [a9, a10, h13]
  exact ⟨by show lR s ∈ s.rd; rw [P.hrd]; simp, (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)),
    (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)),
    P.kl.sub_left fun a ha => kR_sub a (cR_sub (withMem s m) a ha), BitVec.isLt _⟩

/-- `DXT` with the check passed. -/
def DK (G H : Hash) (f : Fns) (D : Nat) (a t : State) : Prop := DXT G H f a t ∧ HK D a

/-- MGF1's arguments, from the anchor. -/
def MgfD (G H : Hash) (f : Fns) (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  DXT G H f a t ∧ t.gpr .r24 = off (stackArg a 13) src ∧ t.gpr .r25 = BitVec.ofNat 64 srcLen ∧
    t.gpr .r26 = off (stackArg a 13) dst ∧ t.gpr .r27 = BitVec.ofNat 64 dstLen

theorem MgfD.toA {G H : Hash} {f : Fns} {src srcLen dst dstLen : Nat} {a t : State}
    (h : MgfD G H f src srcLen dst dstLen a t) : MgfAT SX VX (PreXT G f) (PubXT G) src srcLen dst dstLen a t := by
  obtain ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, h24, h25, h26, h27⟩ := h
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  have a16 : stackArg (bx s m (rcOf (privO s))) 16 = stackArg s 16 := stackArg_bx P hm _ (by decide)
  have h13 : SX (bx s m (rcOf (privO s))) = Sd s := stackArg_bx P hm _ (i := 13) (by decide)
  refine ⟨_, ⟨pX, ?_⟩, ⟨pubX_bx P hm p, a16.trans (p.args 16 (by decide)), y.1⟩, bX, sy, h24, h25, h26, h27⟩
  rw [a16]
  exact tabS_to P T.1 hm rfl rfl rfl (by simp only [SC, h13])

section
variable {G H : Hash} (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include cG hGh hGl hGv in
/-- `mgfXorT`, with its lengths and offsets the anchor's. -/
theorem mgf_anyD (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfD G H f (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXorT f 16) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT SX VX (PreXT G f) (PubXT G) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ctS (okXT G f) hG cG x.2 hGh hGl hGv (tabXT G f)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1.toA, h₂.1.toA⟩) fun _ _ h => h

include hGh hGl hGv in
theorem mgf_dx {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {a t : State}
    (h : MgfD G H f src srcLen dst dstLen a t) : WP isa (mgfXorT f 16) t (DXT G H f a) := by
  obtain ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, h24, h25, h26, h27⟩ := h
  exact WP.mono (mgfXorT_ok (fitsM P) hG (tabS_wm P T.1 hm) hGh hGl hGv hf b sy (h24.trans (off13 p _)) h25
    (h26.trans (off13 p _)) h27) fun _ h' => ⟨_, s, m, P, T, p, y, hm, h'.1.1, h'.2⟩

end

/-- `k` from the anchor. -/
abbrev kA (a : State) : Nat := (a.gpr .r7).toNat

theorem kA_le {a t : State} (h : DX a t) : kA a ≤ 1024 := by
  obtain ⟨_, s, m, P, p, -, -⟩ := h
  have := P.k2; rw [p.g .r7 (by decide)] at this; exact this

/-- The arguments of MGF1 of `maskedDB` into the seed. -/
theorem seed_wp {G H : Hash} {f : Fns} (hD0 : 0 < H.D) (hD64 : H.D ≤ 64) {a t : State} (h : DK G H f H.D a t) :
    WP isa (.block (seedArgs H)) t fun t' => (MgfD G H f (1 + H.D) (kA a - (H.D + 1)) 1 H.D a t' ∧
      MFit (1 + H.D) (kA a - (H.D + 1)) 1 H.D) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .r7).toNat := rfl
  obtain ⟨-, r14, r15, -, -, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (h := by omega_using [hD64, hE]) fun t₁ o₁ e₁ => wp_subi (h := by omega_using [hD64]) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega_using [hE]) fun t₃ o₃ e₃ => wp_li (by omega_using [hD64]) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega_using [hD64, hk2], by omega_using [hD64], .inr (by omega_using []), by omega_using [hD0]⟩⟩, hk⟩
  · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, r14, hE, Nat.zero_add]
  · rw [o₄.get .r25, o₃.get .r25, e₂, o₁.get .r15, r15, sub_r15 (by omega)]
  · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, r14, hE]
  · rw [e₄]

/-- The arguments of MGF1 of the seed into `maskedDB`. -/
theorem db_wp {G H : Hash} {f : Fns} (hD64 : H.D ≤ 64) {a t : State} (h : DK G H f H.D a t) :
    WP isa (.block (dbArgs H)) t fun t' => (MgfD G H f 1 H.D (1 + H.D) (kA a - (H.D + 1)) a t' ∧
      MFit 1 H.D (1 + H.D) (kA a - (H.D + 1))) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .r7).toNat := rfl
  obtain ⟨-, r14, r15, -, -, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (h := by omega_using [hE]) fun t₁ o₁ e₁ => wp_li (by omega_using [hD64]) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega_using [hD64, hE]) fun t₃ o₃ e₃ => wp_subi (h := by omega_using [hD64]) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega_using [hD64], by omega_using [hD64, hk2], .inl (by omega_using []), by omega⟩⟩, hk⟩
  · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, r14, hE]
  · rw [o₄.get .r25, o₃.get .r25, e₂]
  · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, r14, hE, Nat.zero_add]
  · rw [e₄, o₃.get .r15, o₂.get .r15, o₁.get .r15, r15, sub_r15 (by omega)]

/-- `DX` from an entry state with `a`'s public data, by the correctness
lemmas' `Base`. -/
theorem dk_wp {G H : Hash} {f : Fns} {D : Nat} {c : Prog isa} {a t : State} (h : DK G H f D a t)
    (hw : ∀ pc s m, PreD pc s → PubD a s → 2 * D + 2 ≤ kk s → Frame [kD s, scR s] s.mem m →
      Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t →
      WP isa c t fun t' => Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t') :
    WP isa c t (DK G H f D a) :=
  let ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩ := h
  WP.mono_syms (hw _ s m P p (hk_s p hk) hm b) fun _ b' y' => ⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩

/-- After the scan: the index, below the buffer's size. -/
def DI (G H : Hash) (f : Fns) (D : Nat) (a t : State) : Prop := DK G H f D a t ∧ ∃ idx < 1023, t.gpr .r25 = BitVec.ofNat 64 idx

theorem dk_pins {G H : Hash} {f : Fns} {D : Nat} {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → DK G H f D (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ [Reg.r14, .r15, .r16, .r17, .r18, .r19] := by decide) : Pins Φ rs :=
  dx_pins (fun x t hx => (h x t hx).1.dx) rs hrs

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include hH cH cG hGh hGl hGv in
theorem decMain_ct : RelCT isa (Two (DK G H f H.D)) (decMain H f) fun _ _ => True := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  unfold decMain
  -- The seed with MGF1 of `maskedDB`.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, kA a - (H.D + 1), 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfD G H f (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => seed_wp hD0 hD64 h) ?_
  refine two_seq (Ψ := DK G H f H.D) ((mgf_anyD hG cG hGh hGl hGv q₁).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `maskedDB` with MGF1 of the seed.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, kA a - (H.D + 1))
  refine two_seq (Ψ := fun a t => (MgfD G H f (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => db_wp hD64 h) ?_
  refine two_seq (Ψ := DK G H f H.D) ((mgf_anyD hG cG hGh hGl hGv q₂).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `lHash`, and `lHash'` against it.
  refine two_seq (Ψ := DK G H f H.D) ((hashLabelT_ct (vf := VX) (okXL G H f) hH cH (tabXL G H f) (rl := .r18)
      (rn := .r19)
      (L := fun x => stackArg x 9) (N := fun x => (stackArg x 10).toNat) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (fun {x t} _ b => ⟨b.vs .r18 (by decide), by
        rw [b.vs .r19 (by decide)]; show stackArg x 10 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩)
      (fun _ p => ⟨p.2.2.2.1, by rw [p.2.2.2.2]⟩) (fun P => P.2.2) (fun h => lab2_taint h)
      (fun h => lab3_taint h)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁.1.toL hH, h₂.1.toL hH⟩) fun _ _ h => h)
    (fun a t ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩ => WP.mono (hashLabelT_ok P hH (tabS_wmL P T.2 hm) b sy)
      fun t' ⟨⟨b', _⟩, y'⟩ => ⟨⟨_, s, m, P, T, p, y, hm, b', y'⟩, hk⟩) ?_
  refine two_seq (Ψ := DK G H f H.D) (accLh_taint H (dk_pins (an := id) (fun _ _ h => h) [.r14]))
    (fun a t h => dk_wp h fun _ s m P _ hk _ b => WP.mono (accLh_ok P rfl hD0 hD64 hk b) fun _ h' => h'.1) ?_
  -- The scan.
  refine two_seq (Ψ := DI G H f H.D) (scan_taint H (dk_pins (an := id) (fun _ _ h => h) [.r14, .r15]))
    (fun a t ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩ => ?_) ?_
  · have hk' := hk_s p hk
    have hk2 := P.k2
    refine WP.mono_syms (scan_ok P rfl hD64 hk' b) fun t' ⟨b', _, _, _, i'⟩ y' =>
      ⟨⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, ?_⟩
    obtain ⟨idx, he, hi⟩ := scan_idx (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) (t.gpr .r24)
      (kk s - (2 * H.D + 1))
    exact ⟨idx, by unfold kk at *; omega_using [hk2, hi], i'.trans he⟩
  -- The buffer.
  refine two_seq (Ψ := DI G H f H.D) (clearBuf_taint (dk_pins (an := id) (fun _ _ h => h.1) [.r14]))
    (fun a t ⟨⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h25⟩ => WP.mono_syms (clearBuf_ok P b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g' .r25 (by simp)).trans h25⟩) ?_
  refine two_seq (Ψ := DI G H f H.D) (copyT_taint H (dk_pins (an := id) (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t ⟨⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h25⟩ => WP.mono_syms (copyT_ok P rfl hD64 (hk_s p hk) b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g' .r25 (by simp)).trans h25⟩) ?_
  -- The shift, `ok`, `out`, the length and the result.
  refine two_seq (Ψ := DK G H f H.D) (shift_taint (dk_pins (an := id) (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t ⟨h, idx, hi, h25⟩ => dk_wp h fun _ s m P _ _ _ b => WP.mono (shift_ok P b h25 hi) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := DK G H f H.D) (okMask_taint (dk_pins (an := id) (fun _ _ h => h) []))
    (fun a t h => dk_wp h fun _ s m P _ _ _ b => WP.mono (okMask_ok P b (rcOf_le _)) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := fun a t => t.sp = fb a ∧ t.gpr .r17 = a.gpr .r5)
    (outLoop_taint (dk_pins (an := id) (fun _ _ h => h) [.r14, .r15, .r16])) (fun a t h => ?_) ?_
  · obtain ⟨-, -, -, -, r17, -, -⟩ := h.1.dx.pins
    obtain ⟨⟨_, s, m, P, -, p, -, hm, b, -⟩, -⟩ := h
    exact WP.mono (outLoop_ok P b) fun t' ⟨sv, _, g', _⟩ =>
      ⟨by rw [sv.sp, fb, fb, p.sp], (g' .r17 (by simp)).trans r17⟩
  exact decRet_taint H fun a t₁ t₂ h₁ h₂ => ⟨h₁.1.trans h₂.1.symm, fun r hr => by
    rw [List.mem_singleton.mp hr, h₁.2, h₂.2]⟩

end

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)

/-- After the entry, from an entry state with MGF1's table, `G`'s, and `a`'s
public data. -/
def AEntT (pc : Bool) (G H : Hash) (f : Fns) (a t : State) : Prop :=
  ∃ s, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ Entered s t ∧ t.syms = s.syms ∧ XP pc a s

/-- After the private operation, from such an entry state. -/
def AP (G H : Hash) (f : Fns) (a v : State) : Prop :=
  ∃ pc s, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ AfterPriv s v ∧ v.syms = s.syms

/-- After the check of `k`. -/
def AC (G H : Hash) (f : Fns) (D : Nat) (a v : State) : Prop :=
  ∃ pc s, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ AfterPriv s v ∧ v.syms = s.syms ∧
    (v.gpr .r3 != 0) = decide (kk s < 2 * D + 2)

theorem AC.dxt {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) : DXT G H f a v :=
  let ⟨_, s, P, T, p, y, A, sy, _⟩ := h; ⟨_, s, v.mem, P, T, p, y, A.mem, A.base, sy⟩

theorem AC.dx {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) : DX a v := h.dxt.dx

theorem AC.r3 {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) :
    (v.gpr .r3 != 0) = decide (kA a < 2 * D + 2) := by
  obtain ⟨_, s, _, _, p, _, _, _, r⟩ := h
  rw [r]; show decide ((s.gpr .r7).toNat < _) = _; rw [p.g .r7 (by decide)]

theorem AP.dxt {G H : Hash} {f : Fns} {a v : State} (h : AP G H f a v) : DXT G H f a v :=
  let ⟨_, s, P, T, p, y, A, sy⟩ := h; ⟨_, s, v.mem, P, T, p, y, A.mem, A.base, sy⟩

theorem AP.only {G H : Hash} {f : Fns} {a v v' : State} {rs : List Reg} (h : AP G H f a v) (o : Only rs v v')
    (y : v'.syms = v.syms) (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : AP G H f a v' :=
  let ⟨_, s, P, T, p, g, A, sy⟩ := h; ⟨_, s, P, T, p, g, A.only P o hrs, y.trans sy⟩

include hH cH hG cG hHh hHl hHv hGh hGl hGv in
theorem code_ct (pc : Bool) {f : Fns} (hl : H.D ∈ lens) :
    RelCT isa (Two fun a s => (PreD pc s ∧ TT G H f s) ∧ (PubD a s ∧ SymGH G H a s) ∧ XP pc a s) (decryptG pc f)
      fun _ _ => True := by
  have hD64 := hH.hD64
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.2.1.1.sp.trans h₂.2.1.1.sp.symm, fun _ h => nomatch h⟩) ?_
  refine two_seq (Ψ := AEntT pc G H f)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.1.1.sp,
      h₂.2.1.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨⟨P, T⟩, ⟨p, g⟩, x⟩, e⟩ => by
      subst e; exact WP.mono_syms (entry_ok P) fun t E y => ⟨s, P, T, p, g, E, y, x⟩) ?_
  refine two_seq (Ψ := AP G H f) ((priv_ct pc).mono
      (fun _ _ ⟨a, ⟨s₁, P₁, _, p₁, _, E₁, _, x₁⟩, ⟨s₂, P₂, _, p₂, _, E₂, _, x₂⟩⟩ =>
        ⟨a, ⟨s₁, P₁, p₁, E₁, x₁⟩, ⟨s₂, P₂, p₂, E₂, x₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, T, p, g, E, sy, x⟩ => WP.mono_syms (priv_ok P (fun h => (x h).1) E) fun v A y =>
      ⟨_, s, P, T, p, g, A, y.trans sy⟩) ?_
  -- The label's hash function's digest length to `r3`.
  let A₃ := fun (a v : State) => AP G H f a v ∧ v.gpr .r3 = BitVec.ofNat 64 H.D
  have hlen : RelCT isa (Two (AP G H f)) (.block (lenLoad 15)) (Two A₃) :=
    (tword_two (okXL G H f) (tabXL G H f) (Φ := fun (ac : State × Nat) t => AP G H f ac.1 t)
      (fun _ _ h => h.dxt.toL hH) (d := .r3) (.inr (.inr rfl)) (k := 6) (by decide)
      (v := fun _ => BitVec.ofNat 64 H.D) fun P _ => P.2.1.d).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁, h₂⟩)
      fun _ _ ⟨ac, ⟨t₁, h₁, o₁, z₁, e₁⟩, ⟨t₂, h₂, o₂, z₂, e₂⟩⟩ => ⟨ac.1, ⟨h₁.only o₁ z₁, e₁⟩, ⟨h₂.only o₂ z₂, e₂⟩⟩
  refine RelCT.seq hlen ?_
  -- The code for that length.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ pc s, PreD pc s ∧ PubD a s ∧ Saves s u)
    (byLen_ct (D := H.D) (Φ := A₃) (by omega_using [hD64]) (fun _ _ h => h.2)
      (fun _ _ _ h₁ h₂ => h₁.1.dxt.dx.pins.1.trans h₂.1.dxt.dx.pins.1.symm)
      (fun _ _ _ ⟨h, r3⟩ o y => ⟨h.only o y, by rw [o.get .r3]; exact r3⟩) ?_ hl lens_certs)
    fun a v ⟨⟨_, s, P, T, p, g, A, sy⟩, h3⟩ => ?_)
    (restore_taint fun a u₁ u₂ ⟨_, s₁, _, p₁, v₁⟩ ⟨_, s₂, _, p₂, v₂⟩ =>
      ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  · rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
    refine two_seq (Ψ := AC G H f H.D) (chkK_taint H (dx_pins (an := id) (fun _ _ h => h.1.dxt.dx) []))
      (fun a v ⟨⟨_, s, P, T, p, g, A, sy⟩, _⟩ => WP.mono_syms (chk_ok P hH.hD64 A) fun _ ⟨A', r⟩ y =>
        ⟨_, s, P, T, p, g, A', y.trans sy, r⟩) ?_
    refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.r3, h₂.r3])
      (decFail_taint (dx_pins (an := id) (fun _ _ h => h.1.dx) [.r15, .r16, .r17])) ?_
    refine (decMain_ct hH cH hG cG hGh hGl hGv).mono (fun _ _ ⟨a, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩ => ?_) fun _ _ h => h
    rw [eval_nonzero, h₁.r3] at c₁
    have hk : HK H.D a := by simp at c₁; omega
    exact ⟨a, ⟨h₁.dxt, hk⟩, ⟨h₂.dxt, hk⟩⟩
  · refine byLen_ok (D := H.D) (by omega_using [hD64])
      (F := fun u => AfterPriv s u ∧ u.syms = s.syms ∧ u.gpr .r3 = BitVec.ofNat 64 H.D)
      (fun _ h => h.2.2) (fun u u' ⟨A', y', r3'⟩ o y => ⟨A'.only P o, y.trans y', by rw [o.get .r3]; exact r3'⟩)
      ?_ hl (fun x hx => (lens_certs x hx).1) v ⟨A, sy, h3⟩
    intro u ⟨A', y', _⟩
    rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
    exact WP.seq (WP.mono (checks_done hH hG hHh hHl hHv hGh hGl hGv P T.1 T.2 A' y') fun v' h => WP.mono h
      fun _ d => ⟨_, s, P, p, d.1⟩)

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-!
# RSAES-OAEP decryption on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Constant time
(`code_constantTime`, from `code_ct`, for the tables of the first run, which
the public data makes the second's); a state meeting the precondition, with
both tables that of any `w` of `vs`, at `0x300000` (`dec_sat`); and
`dec_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)

open VG.Proof.MdHashTable.PPC64LE (MVar tables fns3 Coh)

theorem code_constantTime {vs : List MVar} (hc : Coh vs) :
    ConstantTime isa (decSpec (tables vs)).pre (decSpec (tables vs)).pub (decrypt (fns3 vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, hpw₁⟩ := spec_tabD h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, hsy, hiffL, hiff⟩ := pubD_of hp
  have hhL₂ := (hiffL _ hT₁).mp hhL₁
  have hh₂ := (hiff _ hT).mp hh₁
  have q₁ := hpw₁.sublist (List.sublist_append_left _ _)
  have q₂ := (spec_tabD h₂).2.2.sublist (List.sublist_append_left _ _)
  have hn := Proof.MdHashTable.PPC64LE.mem_names hw
  have hnL := Proof.MdHashTable.PPC64LE.mem_names hw₁
  have P₁ := preD_of h₁
  have P₂ := preD_of h₂
  exact code_ct w₁.l.ok w₁.l.ct w.l.ok w.l.ct w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len w.l.valid
    false w₁.l.lens_mem _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entryD hc P₁ q₁ hw hh₁, tabS_entryDL hc P₁ q₁ hw₁ hhL₁⟩, ⟨pubD_refl s₁, ⟨rfl, rfl, rfl⟩,
        ⟨rfl, rfl, rfl⟩⟩, nofun⟩,
      ⟨⟨P₂, tabS_entryD hc P₂ q₂ hw hh₂, tabS_entryDL hc P₂ q₂ hw₁ hhL₂⟩, ⟨p,
        ⟨(hsy _ hn.1).symm, (hsy _ hn.2.1).symm, (hsy _ hn.2.2.1).symm⟩,
        ⟨(hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm, (hsy _ hnL.2.2.1).symm⟩⟩, nofun⟩⟩ e₁ e₂

/-- `vg_rsa_oaep_decrypt` against its contract, for the tables of `vs`,
given a state meeting it. -/
theorem dec_verified {vs : List MVar} (hc : Coh vs) (hsat : ∃ s, (decSpec (tables vs)).pre s) :
    Verified PPC64LE.target (decrypt (fns3 vs)) (decSpec (tables vs)) :=
  ⟨code_correct hc, code_constantTime hc, hsat⟩

/-! ## A state meeting the precondition -/

/-- A state meeting decryption's contract, but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, an empty label, a
working space of 2080 words, the stack arguments at `sp + 96`, and both
tables' address `0x300000`. -/
def decSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1800 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x3000 | .r9 => 1
    | .r10 => 0x4200 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10060 then 1
    else bif Nat.beq a.toNat 0x10069 then 0x43 else bif Nat.beq a.toNat 0x10070 then 1
    else bif Nat.beq a.toNat 0x10079 then 0x44 else bif Nat.beq a.toNat 0x10080 then 1
    else bif Nat.beq a.toNat 0x10089 then 0x45 else bif Nat.beq a.toNat 0x10090 then 1
    else bif Nat.beq a.toNat 0x10099 then 0x46 else bif Nat.beq a.toNat 0x100A0 then 1
    else bif Nat.beq a.toNat 0x100A9 then 0x47 else bif Nat.beq a.toNat 0x100B9 then 0x41
    else bif Nat.beq a.toNat 0x100C0 then 64 else bif Nat.beq a.toNat 0x100CA then 0x02
    else bif Nat.beq a.toNat 0x100D0 then 0x20 else bif Nat.beq a.toNat 0x100D1 then 0x08
    else bif Nat.beq a.toNat 0x100DA then 0x30 else bif Nat.beq a.toNat 0x100E2 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10060, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List MVar} {w : MVar}

theorem stackArgAddr_dsat (j : Nat) (hj : j < 17) : (stackArgAddr decSatState j).toNat + 8 ≤ 0x300000 := by
  revert j; decide

theorem stackArg_dsat {j : Nat} {v : Addr} (hj : j < 17) (e : stackArg decSatState j = v) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) j = v :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_dsat j hj)).trans e

theorem dsat_args :
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 0 = 1 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 1 = 0x4300 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 2 = 1 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 3 = 0x4400 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 4 = 1 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 5 = 0x4500 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 6 = 1 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 7 = 0x4600 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 8 = 1 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 9 = 0x4700 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 10 = 0 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 11 = 0x4100 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 12 = 64 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 13 = 0x20000 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 14 = 2080 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 15 = 0x300000 ∧
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 16 = 0x300000 :=
  ⟨stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide)⟩

/-- A state meeting the contract, with both tables that of `w`, at
`0x300000`. -/
theorem dec_sat (hw : w ∈ vs) (hl : (Proof.MdHashTable.PPC64LE.names vs).length < 2 ^ 32) :
    ∃ s, (decSpec (tables vs)).pre s := by
  -- before the witness: each `cases` of this `obtain` reduces the goal, then the contract's precondition
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ :=
    dsat_args (vs := vs) (w := w)
  refine ⟨Proof.MdHashTable.PPC64LE.withTable decSatState vs w, ?_⟩
  have e : stackArgAddr (Proof.MdHashTable.PPC64LE.withTable decSatState vs w) 0 = 0x10060 :=
    show stackArgAddr decSatState 0 = _ by decide
  have e3792 : stackBytes = 3791 + 1 := rfl
  unfold decSpec
  rw [e3792]
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_seventeen, List.append_eq, List.range, List.range.loop]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    a13, a14, a15, a16, e]
  sig_and_intros
  all_goals first
    | exact ⟨Proof.MdHashTable.PPC64LE.tableOf w, List.mem_map_of_mem hw, Proof.MdHashTable.PPC64LE.held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.HashTable.symsOf_distinct2 hl
    | (unfold Spec.Rsa.lenValid; decide)
    | (unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords; decide)

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-!
# RSAES-OAEP decryption on PPC64LE: `vg_rsa_oaep_decrypt_precomputed`

Untrusted: everything here is checked by Lean. `decryptP`, the code of
`vg_rsa_oaep_decrypt` calling `vg_rsa_private_checked_precomputed`
(`decryptG true`), against `Spec.RsaOaep.decryptPrecomputedMdTablesContract`:
its precondition gives `PreD true` and `PreXD` (`preDP_of`), its public data
`PubD` and `PubP` (`pubDP_of`), and the proofs shared with
`vg_rsa_oaep_decrypt` (`code_ok`, `code_ct`) the rest. A state meeting the
precondition holds a real key (`decP_sat`, `Rsa.PreKey`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.MdHashTable.PPC64LE (MVar tables fns3 Coh)
open VG.Proof.Rsa.PreKey
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem stackArgs_nineteen (s : State) :
    List.map (stackArg s) (List.range 19) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17,
      stackArg s 18] := rfl

/-- The precomputed contract, with both hash functions each one of the
tables `ts`, and the stack of the frames and of
`vg_rsa_private_checked_precomputed`. -/
abbrev decSpecP (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract
    (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) stackBytes

/-- Unfolds the precomputed precondition at `h`. -/
macro "dec_preP" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpecP at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop] at $h:ident
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop] at $h:ident
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', Sig.pairFacts, List.filterMap_cons, List.filterMap_nil,
    Bool.cond_true, Bool.cond_false, Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj,
    List.append_nil] at $h:ident))

theorem preDP_of {ts : List FnTable} {s : State} (h : (decSpecP ts).pre s) : PreD true s ∧ PreXD s := by
  dec_preP at h
  sig_split h
  rename_i sp1 sp2 _ _ _ hrd hwr oml on oe op oq odp odq oqi ol oct os oP otl ot oa mln mle mlp mlq mldp mldq
    mlqi mll mlct mls mlP mltl mlt mla ns es ps qs dps dqs qis ls cts sP stl st sa ko kml kn ke kp kq kdp kdq
    kqi kl kct ks kP ktl kt ka wo wml wn we wp wq wdp wdq wqi wl wct wsc wP wtl wt h_k1_k2 ok oc e1 e2 p1 p2 q1
    q2 h4 h8 h6 hs hpl
  have hyp := h
  obtain ⟨k1, k2⟩ := h_k1_k2
  exact ⟨⟨sp1, by simp only [↓reduceIte]; omega_using [sp2], hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, otl, ot,
    oa, mln, mle, mlp, mlq, mldp, mldq, mlqi, mll, mlct, mls, mltl, mlt, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts,
    stl, st, sa, ko, kml, kn, ke, kp, kq, kdp, kdq, kqi, kl, kct, ks, ktl, kt, ka, wo, wml, wn, we, wp, wq, wdp, wdq,
    wqi, wl, wct, wsc, wtl, wt, k1, k2, ok, oc, e1, e2, p1, p2, q1, q2, h4, h8, h6, hs⟩,
    ⟨oP, mlP, sP, kP, wP, hpl, hyp⟩⟩

/-- The tables, as the contract gives them. -/
theorem spec_tabDP {ts : List FnTable} {s : State} (h : (decSpecP ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ (ts.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  dec_preP at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- The tables, on entry: each one of the tables of `vs`, which names its
hash function and holds what the calls through it need. -/
theorem tab_ofDP {vs : List MVar} (hc : Coh vs) {s : State} (h : (decSpecP (tables vs)).pre s) :
    ∃ w₁ ∈ vs, ∃ w ∈ vs, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some w₁.l.G ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some w.l.G ∧
      TabS w₁.H (fns3 vs) 15 (SD s) s (stackArg s 15) ∧ TabS w.H (fns3 vs) 16 (SD s) s (stackArg s 16) := by
  obtain ⟨⟨T₁, hT₁, hh₁⟩, ⟨T, hT, hh⟩, hpw⟩ := spec_tabDP h
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  have P := (preDP_of h).1
  exact ⟨w₁, hw₁, w, hw, Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh₁).2.2.2,
    Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh).2.2.2,
    tabS_entryDL hc P hpw' hw₁ hh₁, tabS_entryD hc P hpw' hw hh⟩

/-- The correctness of `vg_rsa_oaep_decrypt_precomputed`, against its
contract, for the tables of `vs`. -/
theorem code_correctP {vs : List MVar} (hc : Coh vs) (s : State) (h : (decSpecP (tables vs)).pre s) :
    ∃ t s', Exec isa (decryptP (fns3 vs)) s t s' ∧ abiPreserved s s' ∧ (decSpecP (tables vs)).post s s' := by
  obtain ⟨w₁, -, w, -, hH, hG, TL, T⟩ := tab_ofDP hc h
  obtain ⟨P, X⟩ := preDP_of h
  obtain ⟨t, s', he, habi, hr⟩ := code_ok w₁.l.ok w.l.ok w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len w.l.valid
    P T TL (fun _ => X) w₁.l.lens_mem
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpecP
  rw [e]
  sig_post [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Abi.withTables, abi, argRegs, stackArgs_nineteen,
    List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [Proof.RsaOaep.decrypt_eq (by rw [bytesAt_length, bytesAt_length])]
  exact hr

/-- The contract's public data: `PubD`, `pre`'s (`PubP`), the tables'
functions at the same addresses, and the same tables held at both tables'
addresses. -/
theorem pubDP_of {ts : List FnTable} {s₁ s₂ : State} (h : (decSpecP ts).pub s₁ s₂) :
    PubD s₁ s₂ ∧ PubP s₁ s₂ ∧ (∀ f ∈ (ts.map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 16) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 16) (FnTable.words isa s₂ T)) := by
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpecP at h
  rw [e] at h
  sig_pub [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htabL, htab, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
  obtain ⟨hne, hlk⟩ := List.append_inj hl (by simp [bytesAt_length, h7, h9])
  simp only [List.map_append] at hne
  obtain ⟨hn, he⟩ := List.append_inj hne (by simp [bytesAt_length, h7])
  have inj := fun {x y : List Byte} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm⟩,
    ⟨a17.symm, a18.symm, hlk.symm⟩,
    fun f hf => hsy f (List.mem_append_left _ hf), fun T hT => htabL _ _ rfl rfl T hT,
    fun T hT => htab _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm, a13.symm, a14.symm, a15.symm, a16.symm]

theorem pubP_refl (s : State) : PubP s s := ⟨rfl, rfl, rfl⟩

theorem code_constantTimeP {vs : List MVar} (hc : Coh vs) :
    ConstantTime isa (decSpecP (tables vs)).pre (decSpecP (tables vs)).pub (decryptP (fns3 vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, hpw₁⟩ := spec_tabDP h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, q, hsy, hiffL, hiff⟩ := pubDP_of hp
  have hhL₂ := (hiffL _ hT₁).mp hhL₁
  have hh₂ := (hiff _ hT).mp hh₁
  have q₁ := hpw₁.sublist (List.sublist_append_left _ _)
  have q₂ := (spec_tabDP h₂).2.2.sublist (List.sublist_append_left _ _)
  have hn := Proof.MdHashTable.PPC64LE.mem_names hw
  have hnL := Proof.MdHashTable.PPC64LE.mem_names hw₁
  obtain ⟨P₁, X₁⟩ := preDP_of h₁
  obtain ⟨P₂, X₂⟩ := preDP_of h₂
  exact code_ct w₁.l.ok w₁.l.ct w.l.ok w.l.ct w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len w.l.valid
    true w₁.l.lens_mem _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entryD hc P₁ q₁ hw hh₁, tabS_entryDL hc P₁ q₁ hw₁ hhL₁⟩, ⟨pubD_refl s₁, ⟨rfl, rfl, rfl⟩,
        ⟨rfl, rfl, rfl⟩⟩, fun _ => ⟨X₁, pubP_refl s₁⟩⟩,
      ⟨⟨P₂, tabS_entryD hc P₂ q₂ hw hh₂, tabS_entryDL hc P₂ q₂ hw₁ hhL₂⟩, ⟨p,
        ⟨(hsy _ hn.1).symm, (hsy _ hn.2.1).symm, (hsy _ hn.2.2.1).symm⟩,
        ⟨(hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm, (hsy _ hnL.2.2.1).symm⟩⟩, fun _ => ⟨X₂, q⟩⟩⟩ e₁ e₂

/-- `vg_rsa_oaep_decrypt_precomputed` against its contract, for the tables
of `vs`, given a state meeting it. -/
theorem decP_verified {vs : List MVar} (hc : Coh vs) (hsat : ∃ s, (decSpecP (tables vs)).pre s) :
    Verified PPC64LE.target (decryptP (fns3 vs)) (decSpecP (tables vs)) :=
  ⟨code_correctP hc, code_constantTimeP hc, hsat⟩

/-! ## A state meeting the precondition

`n`, `p` and `q` and the precomputed values at `keyMem`'s addresses (`n` of
64 octets at `0x2000`, `p` and `q` of 32 at `0x4200` and `0x4300`, `pre` of
24 words at `0x4800`); `out` at `0x1000`, `msg_len` at `0x1800`, `e` (one
octet) at `0x3000`, the ciphertext at `0x4100`, `dp`, `dq` and `qinv` at
`0x4400`–`0x4600`, an empty label at `0x4700`, a working space of 2080
words at `0x20000`, the stack arguments at `sp + 96`, and both tables'
address `0x300000`. -/

/-- The stack arguments that are not zero, by their bytes. -/
def argMemP (i : Nat) : Byte :=
  bif Nat.beq i 0x10060 then 0x20
  else bif Nat.beq i 0x10069 then 0x43 else bif Nat.beq i 0x10070 then 0x20
  else bif Nat.beq i 0x10079 then 0x44 else bif Nat.beq i 0x10080 then 0x20
  else bif Nat.beq i 0x10089 then 0x45 else bif Nat.beq i 0x10090 then 0x20
  else bif Nat.beq i 0x10099 then 0x46 else bif Nat.beq i 0x100A0 then 0x20
  else bif Nat.beq i 0x100A9 then 0x47 else bif Nat.beq i 0x100B9 then 0x41
  else bif Nat.beq i 0x100C0 then 64 else bif Nat.beq i 0x100CA then 0x02
  else bif Nat.beq i 0x100D0 then 0x20 else bif Nat.beq i 0x100D1 then 0x08
  else bif Nat.beq i 0x100DA then 0x30 else bif Nat.beq i 0x100E2 then 0x30
  else bif Nat.beq i 0x100E9 then 0x48 else bif Nat.beq i 0x100F0 then 24 else 0

def decSatStateP : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1800 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x3000 | .r9 => 1
    | .r10 => 0x4200 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif keyIn a.toNat then keyMem a else argMemP a.toNat
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10060, 152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

/-- `putWs` leaves the bytes below where it writes. -/
theorem putWs_below {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)},
    a.toNat < p.toNat → p.toNat + 8 * ws.length < 2 ^ 64 → Proof.HashTable.putWs m p ws a = m a
  | _, [], _, _ => rfl
  | p, w :: ws, h, hp => by
    simp only [List.length_cons] at hp
    have h8 := Proof.HashTable.add8_toNat (p := p) (by omega_using [hp])
    show Proof.HashTable.putWs (m.writeW p w) (p + 8) ws a = m a
    rw [putWs_below (by omega_using [h, h8]) (by omega_using [hp, h8])]
    refine Mem.write_apply ?_
    rw [BitVec.toNat_sub]
    have := a.isLt
    omega_using [h, hp]

section
variable {vs : List MVar} {w : MVar}

theorem satP_key {a : Addr} (h : keyIn a.toNat = true) :
    (Proof.MdHashTable.PPC64LE.withTable decSatStateP vs w).mem a = keyMem a := by
  have hb : a.toNat < 0x48C0 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h; omega
  show Proof.HashTable.putWs decSatStateP.mem 0x300000 (Proof.MdHashTable.PPC64LE.twL vs w) a = _
  rw [putWs_below (by show a.toNat < 0x300000; omega_using [hb]) (Proof.MdHashTable.PPC64LE.twL_room vs w)]
  show (bif keyIn a.toNat then keyMem a else argMemP a.toNat) = keyMem a
  rw [h]
  exact Bool.cond_true

theorem stackArgAddr_dsatP (j : Nat) (hj : j < 19) : (stackArgAddr decSatStateP j).toNat + 8 ≤ 0x300000 := by
  revert j; decide

theorem stackArg_dsatP {j : Nat} {v : Addr} (hj : j < 19) (e : stackArg decSatStateP j = v) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatStateP vs w) j = v :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_dsatP j hj)).trans e

/-- The stack arguments of `decSatStateP`. -/
def satArgsP (j : Nat) : BitVec 64 :=
  bif Nat.beq j 1 then 0x4300 else bif Nat.beq j 3 then 0x4400 else bif Nat.beq j 5 then 0x4500
  else bif Nat.beq j 7 then 0x4600 else bif Nat.beq j 9 then 0x4700 else bif Nat.beq j 10 then 0
  else bif Nat.beq j 11 then 0x4100 else bif Nat.beq j 12 then 64 else bif Nat.beq j 13 then 0x20000
  else bif Nat.beq j 14 then 2080 else bif Nat.beq j 15 then 0x300000 else bif Nat.beq j 16 then 0x300000
  else bif Nat.beq j 17 then 0x4800 else bif Nat.beq j 18 then 24 else 32

theorem dsatP_args : ∀ j < 19, stackArg decSatStateP j = satArgsP j := by decide

omit vs w in
/-- The precondition, from the facts of a state. -/
theorem pre_of_factsP {vs : List MVar} {s : State} (hg : s.gpr = decSatStateP.gpr) (hsp : s.sp = 0x10000)
    (ha : ∀ j < 19, stackArg s j = satArgsP j) (hrd : s.rd = decSatStateP.rd) (hwr : s.wr = decSatStateP.wr)
    (ht : ∃ T ∈ tables vs, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hsy : (((tables vs).map (fun T : FnTable => T.fns)).flatten ++
      ((tables vs).map (fun T : FnTable => T.fns)).flatten).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g))
    (hk : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (decSpecP (tables vs)).pre s := by
  have e : stackArgAddr s 0 = 0x10060 := by simp only [stackArgAddr, hsp]; rfl
  have e3792 : stackBytes = 3791 + 1 := rfl
  unfold decSpecP
  rw [e3792]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', ha 0 (by decide), ha 1 (by decide), ha 2 (by decide),
    ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide),
    ha 9 (by decide), ha 10 (by decide), ha 11 (by decide), ha 12 (by decide), ha 13 (by decide),
    ha 14 (by decide), ha 15 (by decide), ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), e, hg, hsp, hrd,
    hwr, satArgsP, decSatStateP]
  simp only [Nat.beq, Bool.cond_false, Bool.cond_true]
  sig_and_intros
  all_goals first
    | exact hk
    | exact ht
    | exact hsy
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (unfold Spec.Rsa.lenValid; decide)
    | (unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords; decide)

/-- A state meeting the contract, with both tables that of `w`, at
`0x300000`. -/
theorem decP_sat (hw : w ∈ vs) (hl : (Proof.MdHashTable.PPC64LE.names vs).length < 2 ^ 32) :
    ∃ s, (decSpecP (tables vs)).pre s :=
  ⟨Proof.MdHashTable.PPC64LE.withTable decSatStateP vs w, pre_of_factsP rfl rfl
    (fun j hj => stackArg_dsatP hj (dsatP_args j hj)) rfl rfl
    ⟨Proof.MdHashTable.PPC64LE.tableOf w, List.mem_map_of_mem hw, Proof.MdHashTable.PPC64LE.held_twL _ _ _ rfl⟩
    (Proof.HashTable.symsOf_distinct2 hl) (key_pre_of fun _ ha => satP_key ha)⟩

end

end VG.Proof.RsaOaep.PPC64LE.Dec
