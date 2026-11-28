module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopShared
public import VerifiedGarbage.Proof.SlhDsa.VerifyTopSpec
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.Bignum.ByteDigits
import VerifiedGarbage.Proof.SlhDsa.AArch64.TopLanes
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: the indices of the digest

`Shake.parseIdx p` reads the digest's `tmp_idx_tree` and `tmp_idx_leaf` as
big-endian words (`ldr` and `rev`) and leaves `idx_tree` and `idx_leaf` of
`splitDigest` in `x22` and `x23` (`parseIdx_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_x wp_ldrx wp_lsl wp_lsr wp_and wp_addImm)
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar os2ip_take os2ip_lt toInt_eq)

/-- A word read and byte-reversed is the big-endian number of its bytes. -/
theorem rev_read (m : Mem) (a : Addr) : rev64 (m.readW a 64) = BitVec.ofNat 64 (Spec.Rsa.os2ip (bytesAt m a 8)) := by
  refine Proof.Bignum.ByteDigits.eq_of_bytes fun j hj => ?_
  have hl : (bytesAt m a 8).length = 8 := by simp [bytesAt]
  have hb := Proof.Bignum.ByteDigits.os2ip_byte (bytesAt m a 8) (i := 7 - j) (by omega_using [hl, hj])
  rw [hl, show 8 - 1 - (7 - j) = j by omega_using [hj]] at hb
  rw [rev64_byte _ hj, MlKem.AArch64.KeyGen.readW64_byte _ _ (by omega_using [hj]),
    Proof.Bignum.ByteDigits.extract_nat _ hj, ← hb]
  simp [bytesAt]

theorem rev_read_toNat (m : Mem) (a : Addr) :
    (rev64 (m.readW a 64)).toNat = Spec.Rsa.os2ip (bytesAt m a 8) := by
  rw [rev_read, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := os2ip_lt (bytesAt m a 8)
  rw [show (bytesAt m a 8).length = 8 by simp [bytesAt]] at this
  exact Nat.lt_of_lt_of_le this (by decide)

theorem toNat_shl_shr (x : BitVec 64) {k : Nat} (hk : k ≤ 64) : ((x <<< k) >>> k).toNat = x.toNat % 2 ^ (64 - k) := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 64 = 2 ^ (64 - k) * 2 ^ k by rw [← Nat.pow_add]; congr 1; omega_using [hk],
    Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]

theorem tree_val {X : List Byte} (hX : X.length = 8) {tl tb : Nat} (h2 : tl ≤ 8) (h4 : tb ≤ 64)
    (x : BitVec 64) (hx : x.toNat = Spec.Rsa.os2ip X) :
    (if tb < 64 then ((if tl < 8 then x >>> (64 - 8 * tl) else x) <<< (64 - tb)) >>> (64 - tb)
      else (if tl < 8 then x >>> (64 - 8 * tl) else x)).toNat = Spec.Rsa.os2ip (X.take tl) % 2 ^ tb := by
  have hy : (if tl < 8 then x >>> (64 - 8 * tl) else x).toNat = Spec.Rsa.os2ip (X.take tl) := by
    split
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx, ← os2ip_take X tl, hX,
        show 64 - 8 * tl = 8 * (8 - tl) by omega_using [h2], Nat.pow_mul]
    · rename_i hc
      rw [List.take_of_length_le (by omega_using [hX, h2, hc]), hx]
  split
  · rename_i hc
    rw [toNat_shl_shr _ (by omega_using []), hy, show 64 - (64 - tb) = tb by omega_using [h4, hc]]
  · rename_i hc
    rw [hy, show tb = 64 by omega_using [h4, hc], Nat.mod_eq_of_lt]
    have := os2ip_lt (X.take tl)
    rw [List.length_take, hX] at this
    have hm : min tl 8 ≤ 8 := Nat.min_le_right _ _
    exact Nat.lt_of_lt_of_le this (Nat.le_trans (Nat.pow_le_pow_right (by decide) hm) (by decide))

theorem leaf_val {X : List Byte} (hX : X.length = 8) {ll hp : Nat} (h2 : ll ≤ 8) (h3 : hp ≤ 63)
    (x : BitVec 64) (hx : x.toNat = Spec.Rsa.os2ip X) :
    ((x >>> (64 - 8 * ll)) &&& BitVec.ofNat 64 (2 ^ hp - 1)).toNat = Spec.Rsa.os2ip (X.take ll) % 2 ^ hp := by
  have hp' : 2 ^ hp - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show hp ≤ 64 by omega_using [h3]); omega_using [this]
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx,
    ← os2ip_take X ll, hX, show 64 - 8 * ll = 8 * (8 - ll) by omega_using [h2], Nat.pow_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp', Nat.and_two_pow_sub_one_eq_mod]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_rev {d n : Reg} (k : ∀ s', Only [d] s s' → s'.gpr d = rev64 (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d n :: is)) s Q :=
  wp_x (v := rev64 (s.gpr n)) (by simp only [exec]; rw [read_x]) k

theorem wp_ifLsr {c : Prop} [Decidable c] {d : Reg} {k : Nat} (hk : c → k < 64)
    (h : ∀ s', Only [d] s s' → s'.gpr d = (if c then s.gpr d >>> k else s.gpr d) → WP isa (.block is) s' Q) :
    WP isa (.block ((if c then [Instr.lsr .x d d k] else []) ++ is)) s Q := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, List.singleton_append]
    exact wp_lsr (hk hc) fun s' o e => h s' o (by simp [hc, e])
  · simp only [hc, ↓reduceIte, List.nil_append]
    exact h s (Only.refl _ _) (by simp [hc])

theorem wp_ifMask {c : Prop} [Decidable c] {d : Reg} {k : Nat} (hk : c → k < 64)
    (h : ∀ s', Only [d] s s' → s'.gpr d = (if c then (s.gpr d <<< k) >>> k else s.gpr d) →
      WP isa (.block is) s' Q) :
    WP isa (.block ((if c then [Instr.lsl .x d d k, .lsr .x d d k] else []) ++ is)) s Q := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, List.cons_append, List.nil_append]
    exact wp_lsl (hk hc) fun s₁ o₁ e₁ => wp_lsr (hk hc) fun s₂ o₂ e₂ =>
      h s₂ ((o₁.trans o₂).mono (by simp)) (by rw [e₂, e₁]; simp [hc])
  · simp only [hc, ↓reduceIte, List.nil_append]
    exact h s (Only.refl _ _) (by simp [hc])

end

theorem bytesAt_take' (m : Mem) (a : Addr) {k L : Nat} (h : k ≤ L) : (bytesAt m a L).take k = bytesAt m a k := by
  have e := bytesAt_add m a k (L - k)
  rw [Nat.add_sub_cancel' h] at e
  rw [e, List.take_left' (by simp [bytesAt])]

theorem bytesAt_drop_take (m : Mem) (a : Addr) {d k L : Nat} (h : d + k ≤ L) :
    ((bytesAt m a L).drop d).take k = bytesAt m (a + BitVec.ofNat 64 d) k := by
  have e := bytesAt_add m a d (L - d)
  rw [Nat.add_sub_cancel' (by omega_using [h])] at e
  rw [e, List.drop_left' (by simp [bytesAt]), bytesAt_take' _ _ (by omega_using [h])]

theorem oDigest_eq : Layout.oDigest = 1792 := rfl

/-- `parseIdx`: `idx_tree` and `idx_leaf` of the digest at `oDigest` to `x22`
and `x23`. -/
theorem parseIdx_ok {p : Params} (hp : VPar p) {s : State} {S : Addr} (hS : s.gpr .x19 = S)
    (hw : (⟨S, scratchLen⟩ : Region) ∈ s.wr) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [.x9, .x10, .x22, .x11, .x23] s s' →
      s'.gpr .x22 = BitVec.ofNat 64 (splitDigest p (bytesAt s.mem (at' S Layout.oDigest) p.m)).2.1 →
      s'.gpr .x23 = BitVec.ofNat 64 (splitDigest p (bytesAt s.mem (at' S Layout.oDigest) p.m)).2.2 →
      WP isa (.block is) s' Q) :
    WP isa (.block (Shake.parseIdx p ++ is)) s Q := by
  have rd := hp.rd
  have hm := hp.m
  have hti := hp.ti8
  have hli := hp.li
  have hm64 := hp.m64
  have htb := hp.tb
  have htb' := hp.tb'
  have hhd := hp.hd
  have hp9 := hp.hp9
  simp only [Shake.parseIdx, List.append_assoc, List.cons_append, List.nil_append]
  refine lea_ok (.inl (by rw [oDigest_eq]; omega_using [rd])) (by rw [oDigest_eq]; omega_using [rd]) fun s₁ o₁ e₁ => ?_
  refine wp_ldrx (a := at' S (Layout.oDigest + p.mdLen)) ⟨by decide, by decide⟩
    (by rw [e₁, hS, BitVec.add_zero]) (by rw [o₁.rd, o₁.wr]; exact scr_in' hw (by rw [oDigest_eq]; omega_using [rd]))
    fun s₂ o₂ e₂ => wp_rev fun s₃ o₃ e₃ => ?_
  refine wp_ifLsr (c := p.treeIdxLen < 8) (k := 64 - 8 * p.treeIdxLen) (fun _ => by omega_using [hp.ti7]) fun s₄ o₄ e₄ => ?_
  refine wp_ifMask (c := p.h - p.h / p.d < 64) (k := 64 - (p.h - p.h / p.d)) (fun _ => by
    have h1 := hp.hgt; have h2 := hp.hp1; omega_using [htb, htb', hhd, h1, h2]) fun s₅ o₅ e₅ => ?_
  refine MlKem.AArch64.wp_mov fun s₆ o₆ e₆ => ?_
  have g19 : s₆.gpr .x19 = S := by
    rw [o₆.get .x19 (by simp), o₅.get .x19 (by simp), o₄.get .x19 (by simp), o₃.get .x19 (by simp),
      o₂.get .x19 (by simp), o₁.get .x19 (by simp), hS]
  refine lea_ok (.inl (by rw [oDigest_eq]; omega_using [rd])) (by rw [oDigest_eq]; omega_using [rd]) fun s₇ o₇ e₇ => ?_
  have m₇ : s₇.mem = s.mem := by rw [o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  refine wp_ldrx (a := at' S (Layout.oDigest + p.mdLen + p.treeIdxLen)) ⟨by decide, by decide⟩
    (by rw [e₇, g19, BitVec.add_zero])
    (by rw [o₇.rd, o₇.wr, o₆.rd, o₆.wr, o₅.rd, o₅.wr, o₄.rd, o₄.wr, o₃.rd, o₃.wr, o₂.rd, o₂.wr, o₁.rd, o₁.wr]
        exact scr_in' hw (by rw [oDigest_eq]; omega_using [rd]))
    fun s₈ o₈ e₈ => wp_rev fun s₉ o₉ e₉ => wp_lsr (by omega_using [hli]) fun s₁₀ o₁₀ e₁₀ => ?_
  refine movV_ok (d := .x11) (v := 2 ^ p.hp - 1) (by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp9; omega_using [this]) fun s₁₁ o₁₁ e₁₁ =>
    wp_and fun s₁₂ o₁₂ e₁₂ => k s₁₂ ?_ ?_ ?_
  · exact (((((((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans o₉).trans
      o₁₀).trans o₁₁).trans o₁₂).mono (by simp)
  · refine ofNat_of_toNat ?_
    rw [o₁₂.get .x22 (by simp), o₁₁.get .x22 (by simp), o₁₀.get .x22 (by simp), o₉.get .x22 (by simp),
      o₈.get .x22 (by simp), o₇.get .x22 (by simp), e₆, e₅, e₄, e₃, e₂, o₁.mem,
      tree_val (by simp [bytesAt]) hti (by omega_using [htb, htb']) _ (rev_read_toNat _ _), bytesAt_take' _ _ hti]
    simp only [splitDigest, toInt_eq]
    rw [bytesAt_drop_take _ _ (by omega_using [hm, rd]), addr_add,
      List.take_of_length_le (by simp [bytesAt])]
  · refine ofNat_of_toNat ?_
    rw [e₁₂, e₁₁, o₁₁.get .x10 (by simp), e₁₀, e₉, e₈, m₇,
      leaf_val (by simp [bytesAt]) (by omega_using [hli]) (by omega_using [hp9]) _ (rev_read_toNat _ _),
      bytesAt_take' _ _ (by omega_using [hli])]
    simp only [splitDigest, toInt_eq, hhd]
    rw [bytesAt_drop_take _ _ (by omega_using [hm, rd, hli]), addr_add, ← Nat.add_assoc,
      List.take_of_length_le (by simp [bytesAt])]

end VG.Proof.SlhDsa.AArch64
