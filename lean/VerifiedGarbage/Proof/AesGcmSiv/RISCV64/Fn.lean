module

import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Entry
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
import VerifiedGarbage.Proof.AesCcm.Compare
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes

/-!
# AES-GCM-SIV on RISC-V: the tags in and out, the comparison and the mask

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Fn.lean`): `recv` copies the received tag to `W`
and `tagOut` the computed one from `W` to `tag`, a byte at a time
(`recv_wp`, `tagOut_wp`); `cmp` leaves 1 in `s11` iff the tags at `W` and
`W + 240` are equal, without a branch (`cmp_wp`); `mask` ANDs every byte of
the data with `0 − s11` (`mask_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.WriteBytes VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_addi wp_subi wp_li wp_sub wp_ld wp_xor wp_or wp_srl wp_lbu wp_sb wp_mv)
open VG.Proof.AesCcm.RISCV64 (eval_z eval_nz)
open VG.Proof.AesGcm.RISCV64 (in_off covers_prefix)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)

/-! ## The tags in and out -/

/-- `recv`: the received tag copied to `W`. -/
theorem recv_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block recv) s fun s' => PK s s' ∧ bytesAt s'.mem c.W 16 = bytesAt s.mem c.T 16 ∧
      Frame [⟨c.W, 16⟩] s.mem s'.mem :=
  WP.mono (copy_wp (S := c.T) (D := c.W) (soff := 0) (doff := tagO) (n := 16) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [E.s8, BitVec.add_zero]) (by rw [E.s0]; exact BitVec.add_zero _)
    E.perm.t (covers_prefix E.perm.w (by decide)) (L.t_w.sub_right (Region.sub_prefix (by decide))))
    fun s' ⟨K, hb, hf⟩ => ⟨⟨K.rd, K.wr, K.sp, fun r hr => K.gpr r (by revert r hr; decide)⟩, hb, hf⟩

/-- `tagOut`: the tag copied from `W` to `tag`. -/
theorem tagOut_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (hT : Covers [⟨c.T, 16⟩] s.wr) :
    WP isa (.block tagOut) s fun s' => PK s s' ∧ bytesAt s'.mem c.T 16 = bytesAt s.mem c.W 16 ∧
      Frame [⟨c.T, 16⟩] s.mem s'.mem :=
  WP.mono (copy_wp (S := c.W) (D := c.T) (soff := tagO) (doff := 0) (n := 16) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [E.s0]; exact BitVec.add_zero _) (by rw [E.s8, BitVec.add_zero])
    (covers_prefix (Covers.right E.perm.w) (by decide)) hT
    (L.t_w.sub_right (Region.sub_prefix (by decide))).symm)
    fun s' ⟨K, hb, hf⟩ => ⟨⟨K.rd, K.wr, K.sp, fun r hr => K.gpr r (by revert r hr; decide)⟩, hb, hf⟩

/-! ## The comparison -/

/-- `1 − ((d ||| −d) >>> 63)`: 1 if `d` is 0, else 0. -/
theorem zero_test (d : BitVec 64) :
    BitVec.ofNat 64 1 - ((d ||| (BitVec.ofNat 64 0 - d)) >>> 63) = BitVec.ofNat 64 (if d = 0 then 1 else 0) := by
  have h := Proof.AesCcm.neg_or_msb d
  rw [show BitVec.ofNat 64 0 = (0 : BitVec 64) from rfl, h]
  by_cases hd : d = 0 <;> simp only [hd, ite_true, ite_false] <;> decide

/-- `cmp`: `s11` is 1 iff the 16 bytes at `W` and at `W + 240` are equal. -/
theorem cmp_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block cmp) s fun s' => PK s s' ∧ s'.mem = s.mem ∧
      s'.gpr .s11 = BitVec.ofNat 64 (if bytesAt s.mem c.W 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 240) 16
        then 1 else 0) := by
  unfold cmp
  refine wp_ld (a := c.W + BitVec.ofNat 64 0) (by decide) (by rw [E.s0] <;> rfl)
    (L.wal8 (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [u₁.other _ (by decide), E.s0] <;> rfl)
    (L.wal8 (by decide) (by decide)) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (by decide) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s0, Offset.add_add] <;> rfl)
    (by rw [Offset.add_add]; exact L.wal8 (by decide) (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, Offset.add_add]; exact E.perm.wR (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (by decide) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      E.s0, Offset.add_add] <;> rfl)
    (by rw [Offset.add_add]; exact L.wal8 (by decide) (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, Offset.add_add]; exact E.perm.wR (by decide))
    fun s₅ u₅ => ?_
  refine wp_xor fun s₆ u₆ => wp_or fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ =>
    wp_or fun s₁₀ u₁₀ => wp_srl (by decide) fun s₁₁ u₁₁ => wp_li (by decide) fun s₁₂ u₁₂ =>
    wp_sub fun s₁₃ u₁₃ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans
    (PK.ofUpd u₁₃)))))))))))),
    by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem], ?_⟩
  have hd : s₇.gpr .a0 =
      (s.mem.readW (c.W + BitVec.ofNat 64 0) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 240) 64) |||
      (s.mem.readW (c.W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) 64 ^^^
        s.mem.readW (c.W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) 64) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .a0 (by decide), u₅.gpr, u₅.other .a1 (by decide), u₄.gpr,
      u₅.other .a0 (by decide), u₄.other .a0 (by decide), u₃.gpr, u₂.gpr, u₂.other .a0 (by decide), u₁.gpr,
      u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  rw [u₁₃.gpr, u₁₂.gpr, u₁₂.other .a0 (by decide), u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other .a0 (by decide),
    u₈.gpr, u₈.other .a0 (by decide), hd, zero_test]
  have hw := Proof.AesCcm.words_eq s.mem (c.W + BitVec.ofNat 64 0) (c.W + BitVec.ofNat 64 240)
  rw [BitVec.add_zero] at hw ⊢
  congr 2
  exact propext hw

/-! ## The mask -/

/-- One byte ANDed with `0 − s11`: the byte if `P`, else 0. -/
theorem mask_byte (b : Byte) (P : Prop) [Decidable P] :
    ((b.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0))).setWidth 8 : Byte) =
      if P then b else 0 := by
  rw [BitVec.setWidth_and, Proof.AesCcm.RISCV64.byte_rt]
  by_cases hP : P <;> simp only [hP, ite_true, ite_false]
  · rw [show ((BitVec.ofNat 64 0 - BitVec.ofNat 64 1).setWidth 8 : Byte) = BitVec.allOnes 8 by decide,
      BitVec.and_allOnes]
  · rw [show ((BitVec.ofNat 64 0 - BitVec.ofNat 64 0).setWidth 8 : Byte) = 0 by decide]
    simp

/-- The byte just past what `writeBytes` writes is unchanged. -/
theorem writeBytes_end (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 xs.length) = m (q + BitVec.ofNat 64 xs.length) := by
  simp only [writeBytes]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp

/-- `mask`: every byte of the data kept if `P`, zeroed if not, for `s11` the
indicator of `P`. -/
theorem mask_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Prop} [Decidable P]
    (h25 : s.gpr .s11 = BitVec.ofNat 64 (if P then 1 else 0)) :
    WP isa mask s fun s' => PK s s' ∧ s'.gpr .s11 = s.gpr .s11 ∧
      s'.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D c.n).map fun b => if P then b else 0) := by
  have hn := L.n_lt
  unfold mask
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    WP.block_nil ?_)
  have pk₄ : PK s s₄ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have s11₄ : s₄.gpr .s11 = s.gpr .s11 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have a2₄ : s₄.gpr .a2 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h25]
  have a0₄ : s₄.gpr .a0 = c.D := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s6]
  have a1₄ : s₄.gpr .a1 = BitVec.ofNat 64 c.n := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s7]
  let f : Byte → Byte := fun b => if P then b else 0
  refine WP.ite (decide (c.n = 0)) (eval_z a1₄ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₄, s11₄, ?_⟩
    rw [m₄, h0]
    simp [bytesAt, writeBytes_nil]
  · have h0 : c.n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (fun (w : Nat) (t : State) => ∃ i, w = c.n - i ∧ i < c.n ∧ t.gpr .a0 = c.D + BitVec.ofNat 64 i ∧
        t.gpr .a1 = BitVec.ofNat 64 (c.n - i) ∧ t.gpr .a2 = s₄.gpr .a2 ∧ t.gpr .s11 = s.gpr .s11 ∧
        t.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D i).map f) ∧ PK s t) ?_ (c.n - 0) _
      ⟨0, rfl, by omega_arith, by rw [a0₄]; exact (BitVec.add_zero _).symm, by rw [a1₄, Nat.sub_zero], rfl, s11₄,
        by rw [m₄]; simp [bytesAt, writeBytes_nil], pk₄⟩
    rintro w t ⟨i, rfl, hi, a0, a1, a2, s11, mem, pk⟩
    have Et := E.of_pk pk
    have hin : i + 1 ≤ c.n := by omega_arith
    have hD : Covers [⟨c.D, c.n⟩] t.wr := Et.perm.d
    unfold maskBody
    refine wp_lbu (a := c.D + BitVec.ofNat 64 i) (by decide) (by rw [a0]; exact BitVec.add_zero _)
      (in_off (Covers.right hD) hin hn) fun t₁ u₁ => ?_
    refine wp_and fun t₂ u₂ => ?_
    refine wp_sb (a := c.D + BitVec.ofNat 64 i) (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), a0]; exact BitVec.add_zero _)
      (by rw [u₂.wr, u₁.wr]; exact in_off hD hin hn) fun t₃ u₃ => ?_
    refine wp_addi (by decide) fun t₄ u₄ => wp_subi (imm := 1) (by decide) fun t₅ u₅ =>
      WP.block_nil ?_
    have pk₅ : PK s t₅ := pk.trans ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans
      ((PK.ofUpd u₄).trans (PK.ofUpd u₅)))))
    have hlen : ((bytesAt s.mem c.D i).map f).length = i := by rw [List.length_map, length_bytesAt]
    have hb : t.mem (c.D + BitVec.ofNat 64 i) = s.mem (c.D + BitVec.ofNat 64 i) := by
      rw [mem]
      have := writeBytes_end s.mem c.D ((bytesAt s.mem c.D i).map f) (by rw [hlen]; omega_arith)
      rwa [hlen] at this
    have hmem : t₅.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D (i + 1)).map f) := by
      rw [u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₁.other .a2 (by decide), a2, a2₄, u₂.mem,
        u₁.mem, mask_byte, hb, mem, Proof.Cmac.Stream.bytesAt_append, Proof.AesCcm.RISCV64.bytesAt_one,
        List.map_append, List.map_singleton]
      rw [writeBytes_snoc _ _ _ _ (by rw [hlen]; omega_arith), hlen]
    have hstep : c.D + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have a0' : t₅.gpr .a0 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), a0, hstep]
    have a1' : t₅.gpr .a1 = BitVec.ofNat 64 (c.n - (i + 1)) := by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), a1,
        Proof.AesCcm.RISCV64.ofNat_sub_one (by omega_arith), Nat.sub_sub]
    have a2' : t₅.gpr .a2 = s₄.gpr .a2 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), a2]
    have s11' : t₅.gpr .s11 = s.gpr .s11 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
        s11]
    have ev := eval_nz (r := .a1) (a := c.n - (i + 1)) a1' (by omega_arith)
    by_cases he : i + 1 = c.n
    · left
      exact ⟨by rw [ev]; simp [he], pk₅, s11', by rw [hmem, he]⟩
    · right
      exact ⟨by rw [ev]; simp; omega_arith, c.n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, a0', a1', a2', s11', hmem, pk₅⟩

end VG.Proof.AesGcmSiv.RISCV64
