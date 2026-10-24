module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Env
public import VerifiedGarbage.Impl.AesSiv.PPC64LE
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.AesCcm.Compare
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes

/-!
# AES-SIV on PPC64LE: the synthetic IVs in and out, the comparison and the mask

Untrusted: everything here is checked by Lean. `sivOut` copies the synthetic
IV at `W` to `siv` and `sivIn` the received one from `siv` to `W`
(`sivOut_wp`, `sivIn_wp`); `compare` leaves 1 in `r25` iff the IVs at `W`
and `W + 112` are equal, without a branch (`compare_wp`); `mask` ANDs every
byte of the data with `0 − r25` (`mask_wp`). As for AES-GCM-SIV.
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE VG.WriteBytes
open VG.Impl.AesCcm.PPC64LE (maskBody)
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_subi wp_li wp_sub wp_ld wp_std wp_xor wp_or wp_lsr wp_and
  wp_lbz wp_stb)
open VG.Proof.AesCcm.PPC64LE (wp_mv)
open VG.Proof.Gather.PPC64LE (eval_zero eval_nonzero)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)

/-! ## The synthetic IVs in and out -/

/-- The 16 bytes at `S` copied to `D`, a doubleword at a time. -/
def copy2Mem (m : Mem) (S D : Addr) : Mem :=
  (m.writeW D (m.readW S 64)).writeW (D + BitVec.ofNat 64 8) (m.readW (S + BitVec.ofNat 64 8) 64)

theorem copy2Mem_bytes (m : Mem) (S D : Addr) : bytesAt (copy2Mem m S D) D 16 = bytesAt m S 16 := by
  rw [copy2Mem, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, Proof.Cmac.bytesAt_split]

theorem copy2Mem_frame (m : Mem) (S D : Addr) : Frame [⟨D, 16⟩] m (copy2Mem m S D) :=
  Proof.Cmac.frame_store2 _ _ _

/-- `sivIn`: the received synthetic IV copied to `W`. -/
theorem sivIn_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block sivIn) s fun s' => PK s s' ∧ s'.mem = copy2Mem s.mem c.V c.W := by
  unfold sivIn
  refine wp_ld (a := c.V + BitVec.ofNat 64 0) (by decide) (by decide) (by rw [E.r24]) (E.perm.vR (by decide))
    fun s₁ u₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 0) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14]) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_ld (a := c.V + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r24]) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.vR (by decide))
    fun s₃ u₃ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add])
    (by rw [u₃.wr, u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans (PK.ofMupd u₄))), ?_⟩
  have sep : Mem.Sep (c.V + BitVec.ofNat 64 8) (64 / 8) (c.W + BitVec.ofNat 64 0) (64 / 8) :=
    ((L.v_w' (d := 0) (k := 8) (by decide)).sub_left (Offset.sub_base c.V (d := 8) (n := 8) (k := 16)
      (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, Mem.readW_writeW_sep sep (by decide),
    BitVec.add_zero, BitVec.add_zero]
  rfl

/-- `sivOut`: the synthetic IV at `W` copied to `siv`. -/
theorem sivOut_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (hV : Covers [⟨c.V, 16⟩] s.wr) :
    WP isa (.block sivOut) s fun s' => PK s s' ∧ s'.mem = copy2Mem s.mem c.W c.V := by
  unfold sivOut
  refine wp_ld (a := c.W + BitVec.ofNat 64 0) (by decide) (by decide) (by rw [E.r14]) (E.perm.wR (by decide))
    fun s₁ u₁ => ?_
  have hV₁ : Covers [⟨c.V, 16⟩] s₁.wr := by rw [u₁.wr]; exact hV
  refine wp_std (a := c.V + BitVec.ofNat 64 0) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r24]) (VG.Proof.Gather.PPC64LE.in_off hV₁ (by decide) (by decide))
    fun s₂ u₂ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r14]) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₃ u₃ => ?_
  refine wp_std (a := c.V + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r24, Offset.add_add])
    (by rw [u₃.wr, u₂.wr, Offset.add_add]; exact VG.Proof.Gather.PPC64LE.in_off hV₁ (by decide) (by decide))
    fun s₄ u₄ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans (PK.ofMupd u₄))), ?_⟩
  have sep : Mem.Sep (c.W + BitVec.ofNat 64 8) (64 / 8) (c.V + BitVec.ofNat 64 0) (64 / 8) := by
    rw [BitVec.add_zero]
    exact ((L.v_w' (d := 8) (k := 8) (by decide)).sub_left (Region.sub_prefix (by decide))).symm.sep
      (Region.contains_self _ _) (Region.contains_self _ _)
  rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, Mem.readW_writeW_sep sep (by decide),
    BitVec.add_zero, BitVec.add_zero]
  rfl

/-! ## The comparison -/

/-- `1 − ((d ||| −d) >>> 63)`: 1 if `d` is 0, else 0. -/
theorem zero_test (d : BitVec 64) :
    BitVec.ofNat 64 1 - ((d ||| (BitVec.ofNat 64 0 - d)) >>> 63) = BitVec.ofNat 64 (if d = 0 then 1 else 0) := by
  have h := Proof.AesCcm.neg_or_msb d
  rw [show BitVec.ofNat 64 0 = (0 : BitVec 64) from rfl, h]
  by_cases hd : d = 0 <;> simp only [hd, ite_true, ite_false] <;> decide

/-- `compare`: `r25` is 1 iff the 16 bytes at `W` and at `W + 112` are equal. -/
theorem compare_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block Impl.AesSiv.PPC64LE.compare) s fun s' => PK s s' ∧ s'.mem = s.mem ∧
      s'.gpr .r25 = BitVec.ofNat 64 (if bytesAt s.mem c.W 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 tO) 16
        then 1 else 0) := by
  unfold Impl.AesSiv.PPC64LE.compare
  refine wp_ld (a := c.W + BitVec.ofNat 64 0) (by decide) (by decide) (by rw [E.r14] <;> rfl)
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 tO) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14] <;> rfl) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.r14, Offset.add_add] <;> rfl)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, Offset.add_add]; exact E.perm.wR (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 tO + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      E.r14, Offset.add_add] <;> rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, Offset.add_add]; exact E.perm.wR (by decide))
    fun s₅ u₅ => ?_
  refine wp_xor fun s₆ u₆ => wp_or fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ =>
    wp_or fun s₁₀ u₁₀ => wp_lsr (by decide) fun s₁₁ u₁₁ => wp_li (by decide) fun s₁₂ u₁₂ =>
    wp_sub fun s₁₃ u₁₃ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans
    (PK.ofUpd u₁₃)))))))))))),
    by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem], ?_⟩
  have hd : s₇.gpr .r3 =
      (s.mem.readW (c.W + BitVec.ofNat 64 0) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 tO) 64) |||
      (s.mem.readW (c.W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) 64 ^^^
        s.mem.readW (c.W + BitVec.ofNat 64 tO + BitVec.ofNat 64 8) 64) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .r3 (by decide), u₅.gpr, u₅.other .r4 (by decide), u₄.gpr,
      u₅.other .r3 (by decide), u₄.other .r3 (by decide), u₃.gpr, u₂.gpr, u₂.other .r3 (by decide), u₁.gpr,
      u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  rw [u₁₃.gpr, u₁₂.gpr, u₁₂.other .r3 (by decide), u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other .r3 (by decide),
    u₈.gpr, u₈.other .r3 (by decide), hd, zero_test]
  have hw := Proof.AesCcm.words_eq s.mem (c.W + BitVec.ofNat 64 0) (c.W + BitVec.ofNat 64 tO)
  rw [BitVec.add_zero] at hw ⊢
  congr 2
  exact propext hw

/-! ## The mask -/

/-- One byte ANDed with `0 − r25`: the byte if `P`, else 0. -/
theorem mask_byte (b : Byte) (P : Prop) [Decidable P] :
    ((b.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0))).setWidth 8 : Byte) =
      if P then b else 0 := by
  rw [BitVec.setWidth_and, VG.Proof.Gather.PPC64LE.byte_rt]
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

/-- `mask`: every byte of the data kept if `P`, zeroed if not, for `r25` the
indicator of `P`. -/
theorem mask_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Prop} [Decidable P]
    (h25 : s.gpr .r25 = BitVec.ofNat 64 (if P then 1 else 0)) :
    WP isa mask s fun s' => PK s s' ∧ s'.gpr .r25 = s.gpr .r25 ∧
      s'.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D c.n).map fun b => if P then b else 0) := by
  have hn := L.n_lt
  unfold mask
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    WP.block_nil ?_)
  have pk₄ : PK s s₄ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r25₄ : s₄.gpr .r25 = s.gpr .r25 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have r9₄ : s₄.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h25]
  have r3₄ : s₄.gpr .r3 = c.D := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.r22]
  have r4₄ : s₄.gpr .r4 = BitVec.ofNat 64 c.n := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.r23]
  let f : Byte → Byte := fun b => if P then b else 0
  refine WP.ite (decide (c.n = 0)) (eval_zero r4₄ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₄, r25₄, ?_⟩
    rw [m₄, h0]
    simp [bytesAt, writeBytes_nil]
  · have h0 : c.n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (fun (w : Nat) (t : State) => ∃ i, w = c.n - i ∧ i < c.n ∧ t.gpr .r3 = c.D + BitVec.ofNat 64 i ∧
        t.gpr .r4 = BitVec.ofNat 64 (c.n - i) ∧ t.gpr .r9 = s₄.gpr .r9 ∧ t.gpr .r25 = s.gpr .r25 ∧
        t.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D i).map f) ∧ PK s t) ?_ (c.n - 0) _
      ⟨0, rfl, by omega, by rw [r3₄]; exact (BitVec.add_zero _).symm, by rw [r4₄, Nat.sub_zero], rfl, r25₄,
        by rw [m₄]; simp [bytesAt, writeBytes_nil], pk₄⟩
    rintro w t ⟨i, rfl, hi, r3, r4, r9, r25, mem, pk⟩
    have Et := E.of_pk pk
    have hin : i + 1 ≤ c.n := by omega
    have hD : Covers [⟨c.D, c.n⟩] t.wr := Et.perm.d
    unfold maskBody
    refine wp_lbz (a := c.D + BitVec.ofNat 64 i) (by decide) (by decide)
      (by rw [r3]; exact BitVec.add_zero _)
      (VG.Proof.Gather.PPC64LE.in_off (Covers.right hD) hin hn) fun t₁ u₁ => ?_
    refine wp_and fun t₂ u₂ => ?_
    refine wp_stb (a := c.D + BitVec.ofNat 64 i) (by decide) (by decide)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), r3]; exact BitVec.add_zero _)
      (by rw [u₂.wr, u₁.wr]; exact VG.Proof.Gather.PPC64LE.in_off hD hin hn) fun t₃ u₃ => ?_
    refine wp_addi (by decide) (by decide) fun t₄ u₄ => wp_subi (by decide) (by decide) fun t₅ u₅ =>
      WP.block_nil ?_
    have pk₅ : PK s t₅ := pk.trans ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans
      ((PK.ofUpd u₄).trans (PK.ofUpd u₅)))))
    have hlen : ((bytesAt s.mem c.D i).map f).length = i := by rw [List.length_map, length_bytesAt]
    have hb : t.mem (c.D + BitVec.ofNat 64 i) = s.mem (c.D + BitVec.ofNat 64 i) := by
      rw [mem]
      have := writeBytes_end s.mem c.D ((bytesAt s.mem c.D i).map f) (by rw [hlen]; omega)
      rwa [hlen] at this
    have hmem : t₅.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D (i + 1)).map f) := by
      rw [u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₁.other .r9 (by decide), r9, r9₄, u₂.mem,
        u₁.mem, mask_byte, hb, mem, Proof.Cmac.Stream.bytesAt_append, VG.Proof.Gather.PPC64LE.bytesAt_one,
        List.map_append, List.map_singleton]
      rw [writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen]
    have hstep : c.D + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have r3' : t₅.gpr .r3 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r3, hstep]
    have r4' : t₅.gpr .r4 = BitVec.ofNat 64 (c.n - (i + 1)) := by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r4,
        VG.Proof.Gather.PPC64LE.ofNat_sub_one (by omega), Nat.sub_sub]
    have r9' : t₅.gpr .r9 = s₄.gpr .r9 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r9]
    have r25' : t₅.gpr .r25 = s.gpr .r25 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
        r25]
    have ev := eval_nonzero (r := .r4) (a := c.n - (i + 1)) r4' (by omega)
    by_cases he : i + 1 = c.n
    · left
      exact ⟨by rw [ev]; simp [he], pk₅, r25', by rw [hmem, he]⟩
    · right
      exact ⟨by rw [ev]; simp; omega, c.n - (i + 1), by omega, i + 1, rfl, by omega, r3', r4', r9', r25', hmem, pk₅⟩

end VG.Proof.AesSiv.PPC64LE
