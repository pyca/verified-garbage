module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
public import VerifiedGarbage.Impl.AesSiv.RISCV64
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
import VerifiedGarbage.Proof.AesCcm.Compare
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-SIV on RISC-V: the synthetic IVs in and out, the comparison and the mask

Untrusted: everything here is checked by Lean. `sivOut` copies the synthetic
IV at `W` to `siv` and `sivIn` the received one from `siv` to `W`, a byte at
a time (`Bytes.copyBytes_ok`; `sivOut_wp`, `sivIn_wp`); `compare` leaves 1
in `s0` iff the IVs at `W` and `W + 112` are equal, without a branch
(`sltu`, `compare_wp`); `mask` ANDs every byte of the data with `0 − s0`
(`mask_wp`). As on PPC64LE (`Proof/AesSiv/PPC64LE/Fn.lean`), but for the
copies, whose `siv` has no stated alignment.
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesSiv.RISCV64 VG.WriteBytes
open VG.Impl.AesCcm.RISCV64 (maskBody)
open VG.Proof.AesCcm.RISCV64 (eval_z eval_nz bytesAt_one byte_rt ofNat_sub_one in_off)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)

/-! ## The synthetic IVs in and out -/

/-- Bytes copied one at a time, as `bytesAt`. -/
theorem copied_bytes {m m' : Mem} {S D : Addr} {n : Nat}
    (h : ∀ j < n, m' (D + BitVec.ofNat 64 (0 + j)) = m (S + BitVec.ofNat 64 (0 + j))) :
    bytesAt m' D n = bytesAt m S n := by
  unfold bytesAt
  refine List.map_congr_left fun i hi => ?_
  have := h i (List.mem_range.mp hi)
  rwa [Nat.zero_add] at this

/-- The 16 bytes of `siv` and of `W` are apart. -/
theorem v_w0 {c : Cx} (L : Lay c) {i : Nat} (hi : i < 16) :
    ¬ (⟨c.W + BitVec.ofNat 64 0, 16⟩ : Region).Contains (c.V + BitVec.ofNat 64 (0 + i)) 1 :=
  L.v_w' (d := 0) (k := 16) (by decide) _ (Offset.contains_base _ (by omega) (by omega))

theorem w0_v {c : Cx} (L : Lay c) {i : Nat} (hi : i < 16) :
    ¬ (⟨c.V + BitVec.ofNat 64 0, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 (0 + i)) 1 := by
  intro h
  rw [BitVec.add_zero] at h
  exact L.v_w' (d := 0) (k := 16) (by decide) _ h (by
    rw [BitVec.add_zero]; exact Offset.contains_base _ (by omega) (by omega))

/-- `sivIn`: the received synthetic IV copied to `W`. -/
theorem sivIn_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block sivIn) s fun s' => PK s s' ∧ Frame [⟨c.W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem c.W 16 = bytesAt s.mem c.V 16 := by
  unfold sivIn
  refine WP.mono (Bytes.copyBytes_ok (tmp := .t0) (src := .s11) (dst := .s1) (soff := 0) (doff := 0) (n := 16)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by rw [E.s11]; exact E.perm.vR (by omega))
    (fun i hi => by rw [E.s1]; exact E.perm.wW (by omega))
    (fun i hi => by rw [E.s1, E.s11]; exact v_w0 L hi)) fun s' h => ?_
  refine ⟨⟨h.rd, h.wr, h.sp, fun r hr => h.gpr r (by intro e; subst e; simp [keepRegs] at hr)⟩, ?_, ?_⟩
  · have := h.frame; rwa [E.s1, BitVec.add_zero] at this
  · have := copied_bytes (n := 16) (m := s.mem) (m' := s'.mem) (S := c.V) (D := c.W)
      (fun j hj => by
        have := h.copied j hj
        rwa [E.s1, E.s11] at this)
    exact this

/-- `sivOut`: the synthetic IV at `W` copied to `siv`. -/
theorem sivOut_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (hV : Covers [⟨c.V, 16⟩] s.wr) :
    WP isa (.block sivOut) s fun s' => PK s s' ∧ Frame [⟨c.V, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem c.V 16 = bytesAt s.mem c.W 16 := by
  unfold sivOut
  refine WP.mono (Bytes.copyBytes_ok (tmp := .t0) (src := .s1) (dst := .s11) (soff := 0) (doff := 0) (n := 16)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by rw [E.s1]; exact E.perm.wR (by omega))
    (fun i hi => by rw [E.s11]; exact in_off hV (by omega) (by decide))
    (fun i hi => by rw [E.s1, E.s11]; exact w0_v L hi)) fun s' h => ?_
  refine ⟨⟨h.rd, h.wr, h.sp, fun r hr => h.gpr r (by intro e; subst e; simp [keepRegs] at hr)⟩, ?_, ?_⟩
  · have := h.frame; rwa [E.s11, BitVec.add_zero] at this
  · have := copied_bytes (n := 16) (m := s.mem) (m' := s'.mem) (S := c.W) (D := c.V)
      (fun j hj => by
        have := h.copied j hj
        rwa [E.s1, E.s11] at this)
    exact this

/-! ## The comparison -/

theorem wp_and {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- `1 − (0 <ᵤ d)`: 1 if `d` is 0, else 0. -/
theorem zero_test (d : BitVec 64) :
    BitVec.ofNat 64 1 - (if BitVec.ofNat 64 0 < d then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if d = 0 then 1 else 0) := by
  by_cases hd : d = 0
  · subst hd; decide
  · have h : BitVec.ofNat 64 0 < d := by
      rw [BitVec.lt_def]
      have : d.toNat ≠ 0 := fun h => hd (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [BitVec.toNat_ofNat]; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false hd)]; decide

/-- `compare`: `s0` is 1 iff the 16 bytes at `W` and at `W + 112` are equal. -/
theorem compare_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block Impl.AesSiv.RISCV64.compare) s fun s' => PK s s' ∧ s'.mem = s.mem ∧
      s'.gpr .s0 = BitVec.ofNat 64 (if bytesAt s.mem c.W 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 tO) 16
        then 1 else 0) := by
  unfold Impl.AesSiv.RISCV64.compare
  refine wp_ld (a := c.W + BitVec.ofNat 64 0) (by decide) (by rw [E.s1])
    (L.alW (by decide) (by decide)) (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 tO) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]) (L.alW (by decide) (by decide))
    (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 8) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s1])
    (L.alW (by decide) (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 (tO + 8)) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      E.s1])
    (L.alW (by decide) (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₅ u₅ => ?_
  refine wp_xor fun s₆ u₆ => wp_or fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_sltu fun s₉ u₉ =>
    wp_li (by decide) fun s₁₀ u₁₀ => wp_sub fun s₁₁ u₁₁ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans (PK.ofUpd u₁₁)))))))))),
    by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem], ?_⟩
  have hd : s₇.gpr .t0 =
      (s.mem.readW (c.W + BitVec.ofNat 64 0) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 tO) 64) |||
      (s.mem.readW (c.W + BitVec.ofNat 64 8) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 (tO + 8)) 64) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .t0 (by decide), u₅.gpr, u₅.other .t1 (by decide), u₄.gpr,
      u₅.other .t0 (by decide), u₄.other .t0 (by decide), u₃.gpr, u₂.gpr, u₂.other .t0 (by decide), u₁.gpr,
      u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  rw [u₁₁.gpr, u₁₀.gpr, u₁₀.other .t0 (by decide), u₉.gpr, u₈.gpr, u₈.other .t0 (by decide), hd, zero_test]
  have hw := Proof.AesCcm.words_eq s.mem (c.W + BitVec.ofNat 64 0) (c.W + BitVec.ofNat 64 tO)
  rw [Offset.add_add, Offset.add_add, BitVec.add_zero] at hw
  rw [BitVec.add_zero]
  congr 2
  exact propext hw

/-! ## The mask -/

/-- One byte ANDed with `0 − s0`: the byte if `P`, else 0. -/
theorem mask_byte (b : Byte) (P : Prop) [Decidable P] :
    ((b.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0))).setWidth 8 : Byte) =
      if P then b else 0 := by
  rw [BitVec.setWidth_and, byte_rt]
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

/-- `mask`: every byte of the data kept if `P`, zeroed if not, for `s0` the
indicator of `P`. -/
theorem mask_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Prop} [Decidable P]
    (hs0 : s.gpr .s0 = BitVec.ofNat 64 (if P then 1 else 0)) :
    WP isa mask s fun s' => PK s s' ∧ s'.gpr .s0 = s.gpr .s0 ∧
      s'.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D c.n).map fun b => if P then b else 0) := by
  have hn := L.n_lt
  unfold mask
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    WP.block_nil ?_)
  have pk₄ : PK s s₄ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have s0₄ : s₄.gpr .s0 = s.gpr .s0 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have r9₄ : s₄.gpr .t1 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hs0]
  have r3₄ : s₄.gpr .a0 = c.D := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s9]
  have r4₄ : s₄.gpr .a2 = BitVec.ofNat 64 c.n := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s10]
  let f : Byte → Byte := fun b => if P then b else 0
  refine WP.ite (decide (c.n = 0)) (eval_z r4₄ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₄, s0₄, ?_⟩
    rw [m₄, h0]
    simp [bytesAt, writeBytes_nil]
  · have h0 : c.n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (fun (w : Nat) (t : State) => ∃ i, w = c.n - i ∧ i < c.n ∧ t.gpr .a0 = c.D + BitVec.ofNat 64 i ∧
        t.gpr .a2 = BitVec.ofNat 64 (c.n - i) ∧ t.gpr .t1 = s₄.gpr .t1 ∧ t.gpr .s0 = s.gpr .s0 ∧
        t.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D i).map f) ∧ PK s t) ?_ (c.n - 0) _
      ⟨0, rfl, by omega, by rw [r3₄]; exact (BitVec.add_zero _).symm, by rw [r4₄, Nat.sub_zero], rfl, s0₄,
        by rw [m₄]; simp [bytesAt, writeBytes_nil], pk₄⟩
    rintro w t ⟨i, rfl, hi, r3, r4, r9, s0, mem, pk⟩
    have Et := E.of_pk pk
    have hin : i + 1 ≤ c.n := by omega
    have hD : Covers [⟨c.D, c.n⟩] t.wr := Et.perm.d
    unfold maskBody
    refine wp_lbu (a := c.D + BitVec.ofNat 64 i) (by decide)
      (by rw [r3]; exact BitVec.add_zero _)
      (in_off (Covers.right hD) hin hn) fun t₁ u₁ => ?_
    refine wp_and fun t₂ u₂ => ?_
    refine wp_sb (a := c.D + BitVec.ofNat 64 i) (by decide)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), r3]; exact BitVec.add_zero _)
      (by rw [u₂.wr, u₁.wr]; exact in_off hD hin hn) fun t₃ u₃ => ?_
    refine wp_addi (by decide) fun t₄ u₄ => wp_subi (by decide) fun t₅ u₅ =>
      WP.block_nil ?_
    have pk₅ : PK s t₅ := pk.trans ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans
      ((PK.ofUpd u₄).trans (PK.ofUpd u₅)))))
    have hlen : ((bytesAt s.mem c.D i).map f).length = i := by rw [List.length_map, length_bytesAt]
    have hb : t.mem (c.D + BitVec.ofNat 64 i) = s.mem (c.D + BitVec.ofNat 64 i) := by
      rw [mem]
      have := writeBytes_end s.mem c.D ((bytesAt s.mem c.D i).map f) (by rw [hlen]; omega)
      rwa [hlen] at this
    have hmem : t₅.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D (i + 1)).map f) := by
      rw [u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₁.other .t1 (by decide), r9, r9₄, u₂.mem,
        u₁.mem, mask_byte, hb, mem, Proof.Cmac.Stream.bytesAt_append, bytesAt_one,
        List.map_append, List.map_singleton]
      rw [writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen]
    have hstep : c.D + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have r3' : t₅.gpr .a0 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r3, hstep]
    have r4' : t₅.gpr .a2 = BitVec.ofNat 64 (c.n - (i + 1)) := by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r4,
        ofNat_sub_one (by omega), Nat.sub_sub]
    have r9' : t₅.gpr .t1 = s₄.gpr .t1 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r9]
    have s0' : t₅.gpr .s0 = s.gpr .s0 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
        s0]
    have ev := eval_nz (r := .a2) (a := c.n - (i + 1)) r4' (by omega)
    by_cases he : i + 1 = c.n
    · left
      exact ⟨by rw [ev]; simp [he], pk₅, s0', by rw [hmem, he]⟩
    · right
      exact ⟨by rw [ev]; simp; omega, c.n - (i + 1), by omega, i + 1, rfl, by omega, r3', r4', r9', s0', hmem, pk₅⟩

end VG.Proof.AesSiv.RISCV64
