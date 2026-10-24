module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Short
public import VerifiedGarbage.Proof.AesSiv.Long
import VerifiedGarbage.Proof.CmacAes.PPC64LE.FinSteps
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT

/-!
# AES-SIV on PPC64LE: finishing S2V with a string of a block or more

Untrusted: everything here is checked by Lean. For a last string `P` of
`L ≥ 16` bytes, `kBlock` computes `16 k` for the `k` blocks of `P` chained
before its tail (`AesSiv.kOf`), `tailCopy` copies the last `L − 16 k` bytes
(16 to 32) to the tail at `W + 32` and XORs `D` into its last 16
(`tailCopy_wp`, `AesSiv.xorend_mem`); `longMac` chains the `k` blocks of
`P`, then the first `j` blocks of the tail (`AesSiv.jOf`), and finalizes
the rest, into `W + out` (`longMac_wp`), which is S2V's end
(`AesSiv.long_spec`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE VG.WriteBytes
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Impl.Gather.PPC64LE (copyBytes)
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor Upd Mupd
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_subi wp_li wp_add wp_sub wp_lsr wp_lsl)
open VG.Proof.CmacAes.Stream.PPC64LE (UArgs upd_call FArgs)
open VG.Proof.AesCcm.PPC64LE (wp_mv)
open VG.Proof.Gather.PPC64LE (BytesPre copyBytes_wp Keeps)
open VG.Spec.Aes (bytesAt)

/-- `(L − 1) / 16` in `r9`. -/
theorem lenDiv_eq {s s₁ s₂ : State} {n : Nat} (hn : n < 2 ^ 64) (h1 : 1 ≤ n)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 n)
    (u₁ : Upd s s₁ .r9 (s.gpr .r20 - BitVec.ofNat 64 1)) (u₂ : Upd s₁ s₂ .r9 (s₁.gpr .r9 >>> 4)) :
    s₂.gpr .r9 = BitVec.ofNat 64 ((n - 1) / 16) := by
  rw [u₂.gpr, u₁.gpr, h20, ofNat_sub' h1 hn, ofNat_lsr4' (by omega)]

/-- `kBlock`: `16 k` in `r21`. -/
theorem kBlock_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h16 : 16 ≤ n) (h20 : s.gpr .r20 = BitVec.ofNat 64 n) :
    WP isa kBlock s fun s' => MacKeep s s' ∧ s'.mem = s.mem ∧ s'.gpr .r21 = BitVec.ofNat 64 (16 * kOf n) := by
  unfold kBlock
  refine WP.seq (wp_subi (by decide) (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ =>
    wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have K₃ : MacKeep s s₃ := (MacKeep.ofUpd u₁).trans ((MacKeep.ofUpd u₂).trans (MacKeep.ofUpd u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have h9 : s₃.gpr .r9 = BitVec.ofNat 64 ((n - 1) / 16) := by
    rw [u₃.other _ (by decide)]; exact lenDiv_eq hn (by omega) h20 u₁ u₂
  refine WP.ite (decide ((n - 1) / 16 = 0)) (VG.Proof.Gather.PPC64LE.eval_zero h9 (by omega)) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : (n - 1) / 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨K₃, m₃, by rw [u₃.gpr, kOf_lt (by omega)]⟩
  · have h0 : (n - 1) / 16 ≠ 0 := by simpa using hf
    refine wp_subi (by decide) (by decide) fun s₄ u₄ => wp_lsl (by decide) fun s₅ u₅ =>
      WP.block_nil ⟨K₃.trans ((MacKeep.ofUpd u₄).trans (MacKeep.ofUpd u₅)), by rw [u₅.mem, u₄.mem, m₃], ?_⟩
    rw [u₅.gpr, u₄.gpr, h9, ofNat_sub' (by omega) (by omega), ofNat_shl4 (by omega), kOf_ge (by omega)]

/-- `jBlock`: `j` in `r25`. -/
theorem jBlock_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h16 : 16 ≤ n) (h20 : s.gpr .r20 = BitVec.ofNat 64 n) :
    WP isa jBlock s fun s' => MacKeep s s' ∧ s'.mem = s.mem ∧ s'.gpr .r21 = s.gpr .r21 ∧
      s'.gpr .r25 = BitVec.ofNat 64 (jOf n) := by
  unfold jBlock
  refine WP.seq (wp_subi (by decide) (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ =>
    wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have K₃ : MacKeep s s₃ := (MacKeep.ofUpd u₁).trans ((MacKeep.ofUpd u₂).trans (MacKeep.ofUpd u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have r21₃ : s₃.gpr .r21 = s.gpr .r21 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have h9 : s₃.gpr .r9 = BitVec.ofNat 64 ((n - 1) / 16) := by
    rw [u₃.other _ (by decide)]; exact lenDiv_eq hn (by omega) h20 u₁ u₂
  refine WP.ite (decide ((n - 1) / 16 = 0)) (VG.Proof.Gather.PPC64LE.eval_zero h9 (by omega)) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : (n - 1) / 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨K₃, m₃, r21₃, by rw [u₃.gpr, show jOf n = 0 by unfold jOf; split <;> omega]⟩
  · have h0 : (n - 1) / 16 ≠ 0 := by simpa using hf
    refine wp_li (by decide) fun s₄ u₄ => WP.block_nil ⟨K₃.trans (MacKeep.ofUpd u₄), by rw [u₄.mem, m₃],
      by rw [u₄.other _ (by decide), r21₃], ?_⟩
    rw [u₄.gpr, show jOf n = 1 by unfold jOf; split <;> omega]

theorem xorD_eq : xorD = Proof.CmacAes.PPC64LE.xor2 .r11 .r14 .r11 16 dO 16 := rfl

/-- `r11 = W + T` and `D` XORed into the 16 bytes at `W + 16 + T`, but for
the stack pointer. -/
theorem xorTail_wp' {c : Cx} {s : State} (E : Env c s) {T : Nat} (hT : 16 ≤ T) (hT' : T ≤ 32)
    (h : s.gpr .r20 - s.gpr .r21 = BitVec.ofNat 64 T) :
    WP isa (.block (([.sub .r11 .r20 .r21, .add .r11 .r14 .r11] : List Instr) ++ xorD)) s fun s' => s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = Proof.Cmac.xor2Mem s.mem (c.W + BitVec.ofNat 64 (16 + T)) (c.W + BitVec.ofNat 64 (16 + T))
        (c.W + BitVec.ofNat 64 dO) := by
  simp only [List.cons_append, List.nil_append]
  refine wp_sub fun s₁ u₁ => wp_add fun s₂ u₂ => ?_
  have r11 : s₂.gpr .r11 = c.W + BitVec.ofNat 64 T := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), E.r14, h]
  have r14 : s₂.gpr .r14 = c.W := by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.r14]
  have rd₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  have wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  have P₂ := E.perm.of_eq rd₂ wr₂
  rw [xorD_eq, ← List.append_nil (Proof.CmacAes.PPC64LE.xor2 _ _ _ _ _ _)]
  refine Proof.CmacAes.PPC64LE.xor2_wp .r11 .r14 .r11 16 dO 16 (P := c.W + BitVec.ofNat 64 (16 + T))
    (Q := c.W + BitVec.ofNat 64 dO) (C := c.W + BitVec.ofNat 64 (16 + T)) ⟨by decide, by decide, by decide⟩
    (by decide) (by decide) (by decide) (by rw [r11, Offset.add_add, Nat.add_comm])
    (by rw [r11]; simp only [Offset.add_add]; congr 2; omega) (by rw [r14])
    (by rw [r14, Offset.add_add]) (by rw [r11, Offset.add_add, Nat.add_comm])
    (by rw [r11]; simp only [Offset.add_add]; congr 2; omega) (by decide)
    (P₂.wR (by omega)) (by rw [Offset.add_add]; exact P₂.wR (by omega)) (P₂.wR (by decide))
    (by rw [Offset.add_add]; exact P₂.wR (by decide)) (P₂.wW (by omega))
    (by rw [Offset.add_add]; exact P₂.wW (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ =>
      WP.block_nil ⟨by rw [rd₃, rd₂], by rw [wr₃, wr₂], fun r h9 h10 h11 => ?_, by rw [m₃, u₂.mem, u₁.mem]⟩
  rw [g₃ _ h9 h10, u₂.other _ h11, u₁.other _ h11]

/-- `tailCopy`: the last `T = L − 16 k` bytes of `P` copied to the tail,
with `D` XORed into their last 16. -/
theorem tailCopy_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n k : Nat} (hP : Buf c s P n)
    (hk : 16 * k ≤ n) (hT : 16 ≤ n - 16 * k) (hT' : n - 16 * k ≤ 32) (h19 : s.gpr .r19 = P)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 n) (h21 : s.gpr .r21 = BitVec.ofNat 64 (16 * k)) :
    WP isa tailCopy s fun s' => MacKeep s s' ∧ s'.gpr .r21 = s.gpr .r21 ∧
      Frame [⟨c.W + BitVec.ofNat 64 tailO, 32⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * k) =
        Spec.Siv.xorend (bytesAt s.mem (P + BitVec.ofNat 64 (16 * k)) (n - 16 * k))
          (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16) := by
  have hn := hP.lt
  have ww := L.ww
  have hQ := hP.drop hk
  unfold tailCopy
  have A : WP isa (.block [.add .r3 .r19 .r21, .addi .r9 .r14 tailO, .sub .r4 .r20 .r21]) s fun s₃ =>
      MacKeep s s₃ ∧ s₃.mem = s.mem ∧ s₃.gpr .r21 = s.gpr .r21 ∧
      BytesPre s₃ (P + BitVec.ofNat 64 (16 * k)) (c.W + BitVec.ofNat 64 tailO) (n - 16 * k) := by
    refine wp_add fun s₁ u₁ => wp_addi (by decide) (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ =>
      WP.block_nil ⟨(MacKeep.ofUpd u₁).trans ((MacKeep.ofUpd u₂).trans (MacKeep.ofUpd u₃)),
        by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide)], ?_⟩
    have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
    have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
    exact ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h19, h21],
      by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r14],
      by simp (disch := decide) only [u₃.gpr, u₂.other, u₁.other, h20, h21]; exact ofNat_sub' hk hn,
      by omega, by omega, by rw [rd₃, wr₃]; exact hQ.rd,
      by rw [wr₃]; exact Proof.Gather.PPC64LE.covers_prefix (E.perm.wC (d := tailO) (n := 32) (by decide)) hT',
      (hQ.wd (d := tailO) (k := 32) (by decide)).sub_right (Region.sub_prefix hT')⟩
  refine WP.seq (WP.mono A fun s₃ ⟨K₃, m₃, r21₃, hb⟩ => WP.seq (WP.mono (copyBytes_wp s₃ hb)
    fun s₄ ⟨m₄, _, k₄⟩ => ?_))
  have K₄ : MacKeep s₃ s₄ := ⟨PK.ofKeeps k₄, k₄.gpr _ (by decide), k₄.gpr _ (by decide), k₄.gpr _ (by decide),
    k₄.gpr _ (by decide)⟩
  have K₁₄ := K₃.trans K₄
  have E₄ := E.of_pk K₁₄.pk
  have r21₄ : s₄.gpr .r21 = s.gpr .r21 := by rw [k₄.gpr _ (by decide), r21₃]
  have hsub : s₄.gpr .r20 - s₄.gpr .r21 = BitVec.ofNat 64 (n - 16 * k) := by
    rw [K₁₄.r20, r21₄, h20, h21, ofNat_sub' hk hn]
  refine WP.mono (VG.Proof.AesCbc.PPC64LE.wp_sp (xorTail_wp' E₄ hT hT' hsub))
    fun s₅ ⟨⟨rd₅, wr₅, g₅, m₅⟩, sp₅⟩ => ?_
  have K₅ : MacKeep s₄ s₅ :=
    ⟨⟨rd₅, wr₅, sp₅, fun r hr => g₅ r (fun e => by subst e; exact absurd hr (by decide))
      (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))⟩,
      g₅ _ (by decide) (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide),
      g₅ _ (by decide) (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide)⟩
  refine ⟨K₁₄.trans K₅, by rw [g₅ _ (by decide) (by decide) (by decide), r21₄], ?_, ?_⟩
  -- The memory.
  · have hlen : (bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * k)) (n - 16 * k)).length = n - 16 * k :=
      Proof.Cmac.bytesAt_length _ _ _
    have fW : Frame [⟨c.W + BitVec.ofNat 64 tailO, 32⟩] s.mem s₄.mem := by
      rw [m₄, m₃]
      exact writeBytes_frame _ _ _ (by
        rw [m₃] at hlen; rw [hlen]
        simpa using Offset.contains_base (c.W + BitVec.ofNat 64 tailO) (d := 0) (n := n - 16 * k) (k := 32)
          (by omega) (by decide))
    rw [m₅]
    refine fW.trans ((Proof.Cmac.xor2Mem_frame _ _ _ _).sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have e : c.W + BitVec.ofNat 64 (16 + (n - 16 * k)) =
        c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 (n - 16 * k - 16) := by
      rw [Offset.add_add]; congr 2; simp only [tailO]; omega
    rw [e]
    exact Offset.sub_base _ (by omega)
  -- The tail.
  · have e : c.W + BitVec.ofNat 64 (16 + (n - 16 * k)) =
        c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 (n - 16 * k - 16) := by
      rw [Offset.add_add]; congr 2; simp only [tailO]; omega
    have dQ : (⟨c.W + BitVec.ofNat 64 tailO, n - 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 dO, 16⟩ :=
      L.w_w (.inl (by simp only [tailO, dO]; omega)) (by simp only [tailO]; omega) (by decide)
    rw [m₅, e, xorend_mem _ hT (by rw [L.wrapW (by decide)]; simp only [tailO]; omega) dQ, m₄, m₃]
    have xs := Proof.AesCcm.bytesAt_writeBytes_base s.mem (c.W + BitVec.ofNat 64 tailO)
      (bytesAt s.mem (P + BitVec.ofNat 64 (16 * k)) (n - 16 * k)) (n := n - 16 * k)
      (by rw [Proof.Cmac.bytesAt_length]) (by omega)
    rw [Proof.Cmac.bytesAt_length, List.drop_eq_nil_of_le (by rw [Proof.Cmac.bytesAt_length]),
      List.append_nil] at xs
    rw [xs]
    congr 1
    refine Proof.Cmac.bytesAt_frame (writeBytes_frame _ _ _ (R := ⟨c.W + BitVec.ofNat 64 tailO, 32⟩) (by
        rw [Proof.Cmac.bytesAt_length]
        simpa using Offset.contains_base (c.W + BitVec.ofNat 64 tailO) (d := 0) (n := n - 16 * k) (k := 32)
          (by omega) (by decide))) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact L.w_w (.inr (by decide)) (by decide) (by decide)

/-- The state at `W + out` is clear of the tail. -/
theorem out_tail {c : Cx} (L : Lay c) {out a k : Nat} (hout : out = 0 ∨ out = tO) (ha : 32 ≤ a) (hk : a + k ≤ 64) :
    (⟨c.W + BitVec.ofNat 64 a, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 out, 16⟩ := by
  rcases hout with rfl | rfl
  · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by simp only [tO]; omega)) (by omega) (by decide)

/-- `longMac`: the CMAC of the `k` blocks of `P` and the tail, into
`W + out`. -/
theorem longMac_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (h16 : 16 ≤ n) (h19 : s.gpr .r19 = P) (h20 : s.gpr .r20 = BitVec.ofNat 64 n)
    (h21 : s.gpr .r21 = BitVec.ofNat 64 (16 * kOf n)) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (longMac out) s fun s' => PK s s' ∧ Frame (macR c out) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 out) 16 =
        Spec.Siv.schedCiph s.mem c.C c.R (Spec.Cmac.xor
          (Spec.Cmac.lastBlock 16 (bytesAt s.mem (c.C + BitVec.ofNat 64 240) 16)
            (bytesAt s.mem (c.C + BitVec.ofNat 64 256) 16)
            ((bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * kOf n)).drop (16 * jOf n)))
          (Spec.Cmac.chain (Spec.Siv.schedCiph s.mem c.C c.R)
            (Spec.Cmac.chain (Spec.Siv.schedCiph s.mem c.C c.R) (Spec.Cmac.zeros 16)
              (Spec.Cmac.blocks 16 (bytesAt s.mem P (16 * kOf n))))
            (Spec.Cmac.blocks 16 ((bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * kOf n)).take
              (16 * jOf n))))) := by
  have hn := hP.lt
  have hRb := L.rb
  have hT := kOf_tail h16
  have hJ := jOf_rest h16
  have hj1 := jOf_le n
  have ho : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  have ho8 : out % 4 = 0 := by rcases hout with rfl | rfl <;> decide
  have hk : 16 * kOf n ≤ n := by omega
  generalize kOf n = k at hT hJ hk h21 ⊢
  -- The update over the `k` blocks of `P`.
  have A₁ : WP isa (.block (longArgs₁ out)) s fun s₁ => MacKeep s s₁ ∧ s₁.gpr .r21 = s.gpr .r21 ∧
      s₁.mem = Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 out) ∧
      UArgs s₁ c.C (c.W + BitVec.ofNat 64 out) P (c.W + BitVec.ofNat 64 384) c.R k := by
    unfold longArgs₁
    refine zero16_wp E (d := out) (by omega) ho8 fun s₀ pk₀ g₀ m₀ => ?_
    simp only [List.append_eq, List.cons_append, List.nil_append]
    refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by decide) (by omega) fun t₃ v₃ =>
      wp_addi (by decide) (by decide) fun t₄ v₄ => wp_mv fun t₅ v₅ => wp_lsr (by decide) fun t₆ v₆ =>
      WP.block_nil ?_
    have K₀ : MacKeep s s₀ := ⟨pk₀, g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide)⟩
    have K : MacKeep s₀ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
      ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
    have E₀ := E.of_pk pk₀
    have E₆ := E₀.of_pk K.pk
    have hq := (hP.take hk).of_eq (by rw [K.pk.rd, pk₀.rd]) (by rw [K.pk.wr, pk₀.wr])
    have r21₆ : t₆.gpr .r21 = s.gpr .r21 := by
      simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, g₀]
    refine ⟨K₀.trans K, r21₆, by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, m₀], ?_⟩
    exact uargs L E₆ ho hq.src (hq.wd (d := out) (k := 16) (by omega)) (by omega)
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.gpr, E₀.r15])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.gpr, v₁.other _ (by decide), E₀.r16])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
        v₂.other _ (by decide), v₁.other _ (by decide), E₀.r14])
      (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), g₀ _ (by decide), h19])
      (by
        simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, g₀, h21]
        rw [ofNat_lsr4' (by omega), show 16 * k / 16 = k by omega])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), E₀.r14]; rfl)
  unfold longMac
  refine WP.seq (WP.mono A₁ fun s₁ ⟨K₁, r21₁, m₁, U₁⟩ => ?_)
  refine WP.seq (WP.mono (upd_call U₁) fun s₂ h₂ => ?_)
  have K₂ : MacKeep s₁ s₂ := MacKeep.ofSaved h₂.rd h₂.wr h₂.sp h₂.saved
  have r21₂ : s₂.gpr .r21 = s.gpr .r21 := by rw [h₂.saved _ (by decide), r21₁]
  have K₁₂ := K₁.trans K₂
  refine WP.seq (WP.mono (jBlock_wp (s := s₂) hn h16 (by rw [K₁₂.r20, h20])) fun s₃ ⟨K₃, m₃, r21₃, r25₃⟩ => ?_)
  have K₁₃ := K₁₂.trans K₃
  have E₃ := E.of_pk K₁₃.pk
  have r21₃' : s₃.gpr .r21 = BitVec.ofNat 64 (16 * k) := by rw [r21₃, r21₂, h21]
  -- The update over the first `j` blocks of the tail.
  have A₂ : WP isa (.block (longArgs₂ out)) s₃ fun s₄ => MacKeep s₃ s₄ ∧ s₄.mem = s₃.mem ∧
      s₄.gpr .r21 = s₃.gpr .r21 ∧ s₄.gpr .r25 = s₃.gpr .r25 ∧
      UArgs s₄ c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 384) c.R
        (jOf n) := by
    unfold longArgs₂ macArgs
    simp only [List.cons_append, List.nil_append]
    refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by decide) (by omega) fun t₃ v₃ =>
      wp_addi (by decide) (by decide) fun t₄ v₄ => wp_addi (by decide) (by decide) fun t₅ v₅ =>
      wp_mv fun t₆ v₆ => WP.block_nil ?_
    have K : MacKeep s₃ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
      ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
    have E₆ := E₃.of_pk K.pk
    refine ⟨K, by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem],
      by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other],
      by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other], ?_⟩
    exact uargs L E₆ ho (L.srcW E₆.perm (t := tailO) (k := 16 * jOf n) (by simp only [tailO]; omega))
      (out_tail L hout (by decide) (by simp only [tailO]; omega)) (by omega)
      (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.gpr, E₃.r15])
      (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.gpr, v₁.other, E₃.r16])
      (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.gpr, v₂.other, v₁.other, E₃.r14])
      (by simp (disch := decide) only [v₆.other, v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, E₃.r14])
      (by simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, r25₃])
      (by simp (disch := decide) only [v₆.other, v₅.other, v₄.gpr, v₃.other, v₂.other, v₁.other, E₃.r14]; rfl)
  refine WP.seq (WP.mono A₂ fun s₄ ⟨K₄, m₄, r21₄, r25₄, U₂⟩ => ?_)
  refine WP.seq (WP.mono (upd_call U₂) fun s₅ h₅ => ?_)
  have K₅ : MacKeep s₄ s₅ := MacKeep.ofSaved h₅.rd h₅.wr h₅.sp h₅.saved
  have K₁₅ := K₁₃.trans (K₄.trans K₅)
  have E₅ := E.of_pk K₁₅.pk
  have r21₅ : s₅.gpr .r21 = BitVec.ofNat 64 (16 * k) := by rw [h₅.saved _ (by decide), r21₄, r21₃']
  have r25₅ : s₅.gpr .r25 = BitVec.ofNat 64 (jOf n) := by rw [h₅.saved _ (by decide), r25₄, r25₃]
  have r20₅ : s₅.gpr .r20 = BitVec.ofNat 64 n := by rw [K₁₅.r20, h20]
  -- The finalization of the rest of the tail.
  have A₃ : WP isa (.block (longArgs₃ out)) s₅ fun s₆ => MacKeep s₅ s₆ ∧ s₆.mem = s₅.mem ∧
      FArgs s₆ c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 (tailO + 16 * jOf n))
        (c.W + BitVec.ofNat 64 384) (n - 16 * k - 16 * jOf n) c.R := by
    unfold longArgs₃ macArgs
    simp only [List.cons_append, List.nil_append]
    refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by decide) (by omega) fun t₃ v₃ =>
      wp_addi (by decide) (by decide) fun t₄ v₄ => wp_addi (by decide) (by decide) fun t₅ v₅ =>
      wp_lsl (by decide) fun t₆ v₆ => wp_add fun t₇ v₇ => wp_sub fun t₈ v₈ => wp_sub fun t₉ v₉ =>
      WP.block_nil ?_
    have K : MacKeep s₅ t₉ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
      ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans ((MacKeep.ofUpd v₆).trans ((MacKeep.ofUpd v₇).trans
        ((MacKeep.ofUpd v₈).trans (MacKeep.ofUpd v₉))))))))
    have E₉ := E₅.of_pk K.pk
    have sh : t₆.gpr .r9 = BitVec.ofNat 64 (16 * jOf n) := by
      simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, r25₅]
      exact ofNat_shl4 (by omega)
    refine ⟨K, by rw [v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem], ?_⟩
    exact fargs L E₉ ho hJ.2.2 (L.srcW E₉.perm (t := tailO + 16 * jOf n) (k := n - 16 * k - 16 * jOf n)
        (by simp only [tailO]; omega))
      (out_tail L hout (by simp only [tailO]; omega) (by simp only [tailO]; omega))
      (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other,
        v₂.other, v₁.gpr, E₅.r15])
      (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other,
        v₂.gpr, v₁.other, E₅.r16])
      (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.gpr,
        v₂.other, v₁.other, E₅.r14])
      (by
        simp (disch := decide) only [v₉.other, v₈.other, v₇.gpr, v₆.other, sh]
        simp (disch := decide) only [v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, E₅.r14]
        exact Offset.add_add _ _ _)
      (by
        simp (disch := decide) only [v₉.gpr, v₈.gpr, v₈.other, v₇.other, sh]
        simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, r20₅, r21₅]
        rw [ofNat_sub' hk hn, ofNat_sub' (by omega) (by omega)])
      (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.gpr, v₃.other,
        v₂.other, v₁.other, E₅.r14]; rfl)
  refine WP.seq (WP.mono A₃ fun s₆ ⟨K₆, m₆, F⟩ => ?_)
  refine WP.mono (fin_call_raw F) fun s₇ h₇ => ?_
  have K₇ : MacKeep s₆ s₇ := MacKeep.ofSaved h₇.rd h₇.wr h₇.sp h₇.saved
  -- What each step writes.
  have f₁ : Frame (macR c out) s.mem s₁.mem := by
    rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  have f₄ : Frame (macR c out) s.mem s₄.mem := f₁.trans (by rw [m₄, m₃]; exact h₂.frame)
  have f₆ : Frame (macR c out) s.mem s₆.mem := f₄.trans (by rw [m₆]; exact h₅.frame)
  refine ⟨(K₁₅.trans (K₆.trans K₇)).pk, f₆.trans h₇.frame, ?_⟩
  -- What the calls read is as on entry.
  have dc : ∀ r ∈ macR c out, (⟨c.C, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.c0_w' (by decide) (by omega)
    · exact L.c0_w' (by decide) (by decide)
  have dt : ∀ r ∈ macR c out, (⟨c.W + BitVec.ofNat 64 tailO, 32⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact out_tail L hout (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have cK {d k : Nat} (hd : d + k ≤ 512) {m' : Mem} (hf : Frame (macR c out) s.mem m') :
      bytesAt m' (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame hf (fun r hr => (dc r hr).sub_left (Lay.cSub hd)) (by omega)
  have cT {d k : Nat} (hd : d + k ≤ 32) {m' : Mem} (hf : Frame (macR c out) s.mem m') :
      bytesAt m' (c.W + BitVec.ofNat 64 (tailO + d)) k = bytesAt s.mem (c.W + BitVec.ofNat 64 (tailO + d)) k :=
    Proof.Cmac.bytesAt_frame hf (fun r hr => (dt r hr).sub_left (by
      rw [← Offset.add_add]; exact Offset.sub_base _ hd)) (by omega)
  have k0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  have f₂ : Frame (macR c out) s.mem s₂.mem := by rw [← m₃, ← m₄]; exact f₄
  have f₅ : Frame (macR c out) s.mem s₅.mem := by rw [← m₆]; exact f₆
  have sch₁ := cK (d := 0) (k := 16 * (c.R + 1)) (by omega) f₁
  have sch₄ := cK (d := 0) (k := 16 * (c.R + 1)) (by omega) f₂
  have sch₆ := cK (d := 0) (k := 16 * (c.R + 1)) (by omega) f₅
  have k1 := cK (d := 240) (k := 16) (by decide) f₅
  have k2 := cK (d := 256) (k := 16) (by decide) f₅
  have tl₄ := cT (d := 0) (k := 16 * jOf n) (by omega) f₂
  have tl₆ := cT (d := 16 * jOf n) (k := n - 16 * k - 16 * jOf n) (by omega) f₅
  have pre₁ : bytesAt s₁.mem P (16 * k) = bytesAt s.mem P (16 * k) :=
    Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hP.take hk).wd (by omega)
      · exact (hP.take hk).wd (by decide)) (by omega)
  rw [k0] at sch₁ sch₄ sch₆
  rw [Nat.add_zero] at tl₄
  have hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  have hsplit : n - 16 * k = 16 * jOf n + (n - 16 * k - 16 * jOf n) := by omega
  have tk : (bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * k)).take (16 * jOf n) =
      bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) (16 * jOf n) := by
    rw [hsplit, take_bytesAt]
  have dr : (bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * k)).drop (16 * jOf n) =
      bytesAt s.mem (c.W + BitVec.ofNat 64 (tailO + 16 * jOf n)) (n - 16 * k - 16 * jOf n) := by
    rw [hsplit, drop_bytesAt, Offset.add_add, ← hsplit]
  have out₂ := h₂.out
  have out₅ := h₅.out
  have out₇ := h₇.out
  rw [m₆] at out₇
  rw [m₄, m₃] at out₅
  rw [out₇, out₅, out₂, Proof.CmacAes.PPC64LE.mn, Proof.CmacAes.PPC64LE.ciphAt, sch₆, k1, k2, tl₆,
    sch₄, Proof.Cmac.Stream.blocksAt_eq s₂.mem, tl₄, sch₁, hz, Proof.Cmac.Stream.blocksAt_eq s₁.mem, pre₁, tk, dr,
    Proof.Cmac.xor_comm]
  rfl

/-- S2V's end for a string `P` of a block or more, into `W + out`. -/
theorem long_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (h16 : 16 ≤ n) (h19 : s.gpr .r19 = P) (h20 : s.gpr .r20 = BitVec.ofNat 64 n) {out : Nat}
    (hout : out = 0 ∨ out = tO) :
    WP isa (.seq longTail (longMac out)) s fun s' => PK s s' ∧ Frame (oR c out) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
          (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16) (bytesAt s.mem P n) := by
  have hn := hP.lt
  have hRb := L.rb
  have hT := kOf_tail h16
  unfold longTail
  refine WP.seq (WP.seq (WP.mono (kBlock_wp hn h16 h20) fun s₁ ⟨K₁, m₁, r21₁⟩ => ?_))
  have hk : 16 * kOf n ≤ n := by omega
  refine WP.mono (tailCopy_wp L (E.of_pk K₁.pk) (hP.of_eq K₁.pk.rd K₁.pk.wr) hk hT.1 hT.2
    (by rw [K₁.r19, h19]) (by rw [K₁.r20, h20]) r21₁) fun s₂ ⟨K₂, r21₂, f₂, t₂⟩ => ?_
  have K₁₂ := K₁.trans K₂
  refine WP.mono (longMac_wp L (E.of_pk K₁₂.pk) (hP.of_eq K₁₂.pk.rd K₁₂.pk.wr) h16 (by rw [K₁₂.r19, h19])
    (by rw [K₁₂.r20, h20]) (by rw [r21₂, r21₁]) hout) fun s₃ ⟨pk₃, f₃, o₃⟩ => ⟨K₁₂.pk.trans pk₃, ?_, ?_⟩
  -- What it writes.
  · have f₁₂ : Frame (oR c out) s.mem s₂.mem := by
      rw [← m₁]
      refine f₂.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    refine f₁₂.trans (f₃.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  -- The result.
  · rw [m₁] at f₂ t₂
    have dt : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 tailO, 32⟩ : Region)], (⟨c.C, 512⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact L.c0_w' (by decide) (by decide)
    have cK {d k : Nat} (hd : d + k ≤ 512) :
        bytesAt s₂.mem (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => (dt r hr).sub_left (Lay.cSub hd)) (by omega)
    have sch := cK (d := 0) (k := 16 * (c.R + 1)) (by omega)
    rw [BitVec.add_zero] at sch
    have pre : bytesAt s₂.mem P (16 * kOf n) = bytesAt s.mem P (16 * kOf n) :=
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hP.take hk).wd (by decide)) (by omega)
    have hp : (bytesAt s.mem P n).length = n := Proof.Cmac.bytesAt_length _ _ _
    have hsplit : n = 16 * kOf n + (n - 16 * kOf n) := by omega
    have tk : (bytesAt s.mem P n).take (16 * kOf n) = bytesAt s.mem P (16 * kOf n) := by
      have := take_bytesAt s.mem P (a := 16 * kOf n) (b := n - 16 * kOf n)
      rwa [← hsplit] at this
    have dr : (bytesAt s.mem P n).drop (16 * kOf n) =
        bytesAt s.mem (P + BitVec.ofNat 64 (16 * kOf n)) (n - 16 * kOf n) := by
      have := drop_bytesAt s.mem P (a := 16 * kOf n) (b := n - 16 * kOf n)
      rwa [← hsplit] at this
    rw [o₃, Spec.Siv.schedCiph, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide),
      pre, t₂, Spec.Siv.ctxMac,
      ← long_spec _ _ _ _ _ (Proof.Cmac.bytesAt_length _ _ _) (by rw [hp]; exact h16), hp, tk, dr]
    rfl

/-- S2V's end, into `W + out`. -/
theorem finish_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (h19 : s.gpr .r19 = P) (h20 : s.gpr .r20 = BitVec.ofNat 64 n) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (finish out) s fun s' => PK s s' ∧ Frame (oR c out) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
          (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16) (bytesAt s.mem P n) := by
  have hn := hP.lt
  unfold finish
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have pk₁ : PK s s₁ := PK.ofUpd u₁
  have E₁ := E.of_pk pk₁
  have hP₁ := hP.of_eq pk₁.rd pk₁.wr
  have r19 : s₁.gpr .r19 = P := by rw [u₁.other _ (by decide), h19]
  have r20 : s₁.gpr .r20 = BitVec.ofNat 64 n := by rw [u₁.other _ (by decide), h20]
  have r9 : s₁.gpr .r9 = BitVec.ofNat 64 (n / 16) := by rw [u₁.gpr, h20, ofNat_lsr4' hn]
  have m₁ : s₁.mem = s.mem := u₁.mem
  refine WP.ite (decide (n / 16 = 0)) (VG.Proof.Gather.PPC64LE.eval_zero r9 (by omega)) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : n / 16 = 0 := by simpa using ht
    refine WP.mono (short_wp L E₁ hP₁ (by omega) r19 r20 hout) fun s' ⟨pk, f, o⟩ => ⟨pk₁.trans pk, ?_, ?_⟩
    · rw [← m₁]; exact f
    · rw [o, m₁]
  · have h0 : n / 16 ≠ 0 := by simpa using hf
    refine WP.mono (long_wp L E₁ hP₁ (by omega) r19 r20 hout) fun s' ⟨pk, f, o⟩ => ⟨pk₁.trans pk, ?_, ?_⟩
    · rw [← m₁]; exact f
    · rw [o, m₁]

end VG.Proof.AesSiv.PPC64LE
