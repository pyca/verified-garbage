module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.Short
public import VerifiedGarbage.Proof.AesSiv.Long
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesSiv.RISCV64.FinRaw
import VerifiedGarbage.Proof.CmacAes.RISCV64.Finalize

/-!
# AES-SIV on RISC-V: finishing S2V with a string of a block or more

Untrusted: everything here is checked by Lean. For a last string `P` of
`L ≥ 16` bytes, `kBlock` computes `16 k` for the `k` blocks of `P` chained
before its tail (`AesSiv.kOf`), `tailCopy` copies the last `L − 16 k` bytes
(16 to 32) to the tail at `W + 32` (AES-CCM's `copy`) and XORs `D` into its
last 16, at any alignment, a byte at a time (AES-CCM's `xorBytes`;
`tailCopy_wp`, `xorend_writeBytes`); `longMac` chains the `k` blocks of
`P`, then the first `j` blocks of the tail (`AesSiv.jOf`), and finalizes
the rest, into `W + out` (`longMac_wp`), which is S2V's end
(`AesSiv.long_spec`). As on PPC64LE (`Proof/AesSiv/PPC64LE/Long.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64 VG.WriteBytes
open VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Proof.CmacAes.Stream.RISCV64 (UArgs upd_call FArgs)
open VG.Proof.AesCcm.RISCV64 (BytesPre copy_wp xorBytes_wp xorL)
open VG.Spec.Aes (bytesAt)

/-- `(L − 1) / 16` in `t0`. -/
theorem lenDiv_eq {s s₁ s₂ : State} {n : Nat} (hn : n < 2 ^ 64) (h1 : 1 ≤ n)
    (h20 : s.gpr .s7 = BitVec.ofNat 64 n)
    (u₁ : Upd s s₁ .t0 (s.gpr .s7 - BitVec.ofNat 64 1)) (u₂ : Upd s₁ s₂ .t0 (s₁.gpr .t0 >>> 4)) :
    s₂.gpr .t0 = BitVec.ofNat 64 ((n - 1) / 16) := by
  rw [u₂.gpr, u₁.gpr, h20, ofNat_sub' h1 hn, ofNat_lsr4' (by omega)]

/-- `kBlock`: `16 k` in `s8`. -/
theorem kBlock_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h16 : 16 ≤ n) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa kBlock s fun s' => MacKeep s s' ∧ s'.mem = s.mem ∧ s'.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) := by
  unfold kBlock
  refine WP.seq (wp_subi (imm := 1) (by decide) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ =>
    wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have K₃ : MacKeep s s₃ := (MacKeep.ofUpd u₁).trans ((MacKeep.ofUpd u₂).trans (MacKeep.ofUpd u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have h9 : s₃.gpr .t0 = BitVec.ofNat 64 ((n - 1) / 16) := by
    rw [u₃.other _ (by decide)]; exact lenDiv_eq hn (by omega) h20 u₁ u₂
  refine WP.ite (decide ((n - 1) / 16 = 0)) (eval_zero_ofNat _ _ (by omega) h9) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : (n - 1) / 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨K₃, m₃, by rw [u₃.gpr, kOf_lt (by omega)]⟩
  · have h0 : (n - 1) / 16 ≠ 0 := by simpa using hf
    refine wp_subi (imm := 1) (by decide) fun s₄ u₄ => wp_sll (by decide) fun s₅ u₅ =>
      WP.block_nil ⟨K₃.trans ((MacKeep.ofUpd u₄).trans (MacKeep.ofUpd u₅)), by rw [u₅.mem, u₄.mem, m₃], ?_⟩
    rw [u₅.gpr, u₄.gpr, h9, ofNat_sub' (by omega) (by omega), ofNat_shl4 (by omega), kOf_ge (by omega)]

/-- `jBlock`: `j` in `s0`. -/
theorem jBlock_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h16 : 16 ≤ n) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa jBlock s fun s' => MacKeep s s' ∧ s'.mem = s.mem ∧ s'.gpr .s8 = s.gpr .s8 ∧
      s'.gpr .s0 = BitVec.ofNat 64 (jOf n) := by
  unfold jBlock
  refine WP.seq (wp_subi (imm := 1) (by decide) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ =>
    wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have K₃ : MacKeep s s₃ := (MacKeep.ofUpd u₁).trans ((MacKeep.ofUpd u₂).trans (MacKeep.ofUpd u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have r21₃ : s₃.gpr .s8 = s.gpr .s8 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have h9 : s₃.gpr .t0 = BitVec.ofNat 64 ((n - 1) / 16) := by
    rw [u₃.other _ (by decide)]; exact lenDiv_eq hn (by omega) h20 u₁ u₂
  refine WP.ite (decide ((n - 1) / 16 = 0)) (eval_zero_ofNat _ _ (by omega) h9) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : (n - 1) / 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨K₃, m₃, r21₃, by rw [u₃.gpr, show jOf n = 0 by unfold jOf; split <;> omega]⟩
  · have h0 : (n - 1) / 16 ≠ 0 := by simpa using hf
    refine wp_li (by decide) fun s₄ u₄ => WP.block_nil ⟨K₃.trans (MacKeep.ofUpd u₄), by rw [u₄.mem, m₃],
      by rw [u₄.other _ (by decide), r21₃], ?_⟩
    rw [u₄.gpr, show jOf n = 1 by unfold jOf; split <;> omega]

/-- The last 16 of `T ≥ 16` bytes at `B`, XORed with the 16 at `Q`, a byte
at a time: `xorend` of the bytes at `B` and those at `Q`. -/
theorem xorend_writeBytes (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64) :
    bytesAt (writeBytes m (B + BitVec.ofNat 64 (T - 16))
        (xorL (bytesAt m (B + BitVec.ofNat 64 (T - 16)) 16) (bytesAt m Q 16))) B T =
      Spec.Siv.xorend (bytesAt m B T) (bytesAt m Q 16) := by
  have e : T = (T - 16) + 16 := by omega
  have hx : (xorL (bytesAt m (B + BitVec.ofNat 64 (T - 16)) 16) (bytesAt m Q 16)).length = 16 := by
    simp [Proof.Cmac.bytesAt_length]
  have hs := Proof.Cmac.Stream.bytesAt_append (writeBytes m (B + BitVec.ofNat 64 (T - 16))
    (xorL (bytesAt m (B + BitVec.ofNat 64 (T - 16)) 16) (bytesAt m Q 16))) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  have tk := take_bytesAt m B (a := T - 16) (b := 16)
  have dr := drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, Proof.Cmac.bytesAt_frame (writeBytes_frame _ _ _ (R := ⟨B + BitVec.ofNat 64 (T - 16), 16⟩)
      (by rw [hx]; exact Region.contains_self _ _)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega) (by omega)) (by omega),
    Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [hx]) (by decide), hx,
    List.drop_eq_nil_of_le (by rw [Proof.Cmac.bytesAt_length]), List.append_nil]
  rfl

/-- `tailCopy`: the last `T = L − 16 k` bytes of `P` copied to the tail,
with `D` XORed into their last 16. -/
theorem tailCopy_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n k : Nat} (hP : Buf c s P n)
    (hk : 16 * k ≤ n) (hT : 16 ≤ n - 16 * k) (hT' : n - 16 * k ≤ 32) (h19 : s.gpr .s6 = P)
    (h20 : s.gpr .s7 = BitVec.ofNat 64 n) (h21 : s.gpr .s8 = BitVec.ofNat 64 (16 * k)) :
    WP isa tailCopy s fun s' => MacKeep s s' ∧ s'.gpr .s8 = s.gpr .s8 ∧
      Frame [⟨c.W + BitVec.ofNat 64 tailO, 32⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * k) =
        Spec.Siv.xorend (bytesAt s.mem (P + BitVec.ofNat 64 (16 * k)) (n - 16 * k))
          (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16) := by
  have hn := hP.lt
  have ww := L.ww
  have hQ := hP.drop hk
  unfold tailCopy
  have A : WP isa (.block [.add .a0 .s6 .s8, .addi .a1 .s1 (tailO : Int), .sub .a2 .s7 .s8]) s fun s₃ =>
      MacKeep s s₃ ∧ s₃.mem = s.mem ∧ s₃.gpr .s8 = s.gpr .s8 ∧
      BytesPre s₃ (P + BitVec.ofNat 64 (16 * k)) (c.W + BitVec.ofNat 64 tailO) (n - 16 * k) := by
    refine wp_add fun s₁ u₁ => wp_addi (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ =>
      WP.block_nil ⟨(MacKeep.ofUpd u₁).trans ((MacKeep.ofUpd u₂).trans (MacKeep.ofUpd u₃)),
        by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide)], ?_⟩
    have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
    have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
    have cw : Covers [⟨c.W + BitVec.ofNat 64 tailO, n - 16 * k⟩] s.wr :=
      VG.Proof.AesCcm.RISCV64.covers_prefix (E.perm.wC (d := tailO) (n := 32) (by decide)) hT'
    exact ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h19, h21],
      by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s1],
      by simp (disch := decide) only [u₃.gpr, u₂.other, u₁.other, h20, h21]; exact ofNat_sub' hk hn,
      by omega, by omega, by rw [rd₃, wr₃]; exact hQ.rd, by rw [wr₃]; exact cw,
      (hQ.wd (d := tailO) (k := 32) (by decide)).sub_right (Region.sub_prefix hT')⟩
  refine WP.seq (WP.mono A fun s₃ ⟨K₃, m₃, r21₃, hb⟩ => WP.seq (WP.mono (copy_wp s₃ hb)
    fun s₄ ⟨m₄, _, k₄⟩ => ?_))
  have K₄ : MacKeep s₃ s₄ := ⟨PK.ofKeeps k₄, k₄.gpr _ (by decide), k₄.gpr _ (by decide), k₄.gpr _ (by decide),
    k₄.gpr _ (by decide)⟩
  have K₁₄ := K₃.trans K₄
  have E₄ := E.of_pk K₁₄.pk
  have r21₄ : s₄.gpr .s8 = s.gpr .s8 := by rw [k₄.gpr _ (by decide), r21₃]
  have r20₄ : s₄.gpr .s7 = BitVec.ofNat 64 n := by rw [K₁₄.s7, h20]
  -- `xorBytes`' arguments: `D`, and the tail's last 16 bytes.
  have eT : c.W + BitVec.ofNat 64 (n - 16 * k) + BitVec.ofNat 64 16 =
      c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 (n - 16 * k - 16) := by
    rw [Offset.add_add, Offset.add_add]; congr 2; simp only [tailO]; omega
  have B : WP isa (.block xorDArgs) s₄ fun s₉ => MacKeep s₄ s₉ ∧ s₉.mem = s₄.mem ∧ s₉.gpr .s8 = s₄.gpr .s8 ∧
      BytesPre s₉ (c.W + BitVec.ofNat 64 dO) (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 (n - 16 * k - 16))
        16 := by
    unfold xorDArgs
    refine wp_addi (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ => wp_add fun s₇ u₇ =>
      wp_addi (by decide) fun s₈ u₈ => wp_li (by decide) fun s₉ u₉ =>
      WP.block_nil ⟨(MacKeep.ofUpd u₅).trans ((MacKeep.ofUpd u₆).trans ((MacKeep.ofUpd u₇).trans
        ((MacKeep.ofUpd u₈).trans (MacKeep.ofUpd u₉)))), by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem],
        by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide)], ?_⟩
    have rd₉ : s₉.rd = s₄.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd]
    have wr₉ : s₉.wr = s₄.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr]
    have hsub : s₄.gpr .s7 - s₄.gpr .s8 = BitVec.ofNat 64 (n - 16 * k) := by
      rw [r20₄, r21₄, h21, ofNat_sub' hk hn]
    refine ⟨by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.gpr, E₄.s1],
      by
        simp (disch := decide) only [u₉.other, u₈.gpr, u₇.gpr, u₆.gpr, u₆.other, u₅.other]
        rw [E₄.s1, hsub, eT],
      by rw [u₉.gpr], by decide, by decide, by rw [rd₉, wr₉]; exact E₄.perm.wCR (by decide), ?_, ?_⟩
    · rw [wr₉, Offset.add_add]
      exact E₄.perm.wC (by simp only [tailO]; omega)
    · rw [Offset.add_add]
      exact L.w_w (.inr (by simp only [tailO, dO]; omega)) (by decide) (by simp only [tailO]; omega)
  refine WP.seq (WP.mono B fun s₉ ⟨K₉, m₉, r21₉, hb'⟩ => WP.mono (xorBytes_wp s₉ hb') fun s₁₀ ⟨m₁₀, _, k₁₀⟩ => ?_)
  have K₁₀ : MacKeep s₉ s₁₀ := ⟨PK.ofKeeps k₁₀, k₁₀.gpr _ (by decide), k₁₀.gpr _ (by decide),
    k₁₀.gpr _ (by decide), k₁₀.gpr _ (by decide)⟩
  have hlen : (bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * k)) (n - 16 * k)).length = n - 16 * k :=
    Proof.Cmac.bytesAt_length _ _ _
  have fW : Frame [⟨c.W + BitVec.ofNat 64 tailO, 32⟩] s.mem s₄.mem := by
    rw [m₄, m₃]
    exact writeBytes_frame _ _ _ (by
      rw [m₃] at hlen; rw [hlen]
      simpa using Offset.contains_base (c.W + BitVec.ofNat 64 tailO) (d := 0) (n := n - 16 * k) (k := 32)
        (by omega) (by decide))
  have hx : ∀ m : Mem, (xorL (bytesAt m (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 (n - 16 * k - 16)) 16)
      (bytesAt m (c.W + BitVec.ofNat 64 dO) 16)).length = 16 := fun m => by simp [Proof.Cmac.bytesAt_length]
  refine ⟨K₁₄.trans (K₉.trans K₁₀), by rw [k₁₀.gpr _ (by decide), r21₉, r21₄], ?_, ?_⟩
  -- The memory.
  · rw [m₁₀, m₉]
    exact fW.trans (writeBytes_frame _ _ _ (by
      rw [hx]
      exact Offset.contains_base _ (d := n - 16 * k - 16) (n := 16) (k := 32) (by omega) (by omega)))
  -- The tail.
  · have dT : (⟨c.W + BitVec.ofNat 64 tailO, 32⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 dO, 16⟩ :=
      L.w_w (.inl (by decide)) (by decide) (by decide)
    have e : n - 16 * k - 16 = n - 16 * k - 16 := rfl
    rw [m₁₀, m₉, xorend_writeBytes _ hT (by rw [L.wrapW (by decide)]; simp only [tailO]; omega),
      Proof.Cmac.bytesAt_frame fW (p := c.W + BitVec.ofNat 64 dO) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dT.symm) (by decide), m₄,
      Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [hlen]) (by omega), hlen,
      List.drop_eq_nil_of_le (by rw [Proof.Cmac.bytesAt_length]), List.append_nil, m₃]

end VG.Proof.AesSiv.RISCV64
