module

public import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchLists
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Siv.Spec
public import VerifiedGarbage.Impl.AesSiv.RISCV64
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Long
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.AesSiv.RISCV64.Rel
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.Rel
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesSiv.RISCV64.CtrLoop
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.Long
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.CtrLoop
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.AesSiv.Long
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesSiv.Long
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
meta import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
import VerifiedGarbage.Proof.AesSiv.RISCV64.Mac
import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.Mac
meta import VerifiedGarbage.Proof.AesSiv.Ctr32
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Spec.Siv.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
import VerifiedGarbage.Proof.AesCcm.Compare
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.Siv.Contract
meta import VerifiedGarbage.Proof.AesSiv.Scratch
meta import VerifiedGarbage.Impl.AesSiv.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Spec.Aes
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
meta import VerifiedGarbage.Proof.AesCcm.Compare
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Stream

/-! ### `AesSiv.RISCV64.TopCT`, which only this module used -/

section

/-! ### `AesSiv.RISCV64.Dec`, which this module and modules that import it used -/

section

/-! ### `AesSiv.RISCV64.Enc`, which this module and modules that import it used -/

section

/-! ### `AesSiv.RISCV64.Fn`, which this module and modules that import it used -/

section

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
  L.v_w' (d := 0) (k := 16) (by decide) _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))

theorem w0_v {c : Cx} (L : Lay c) {i : Nat} (hi : i < 16) :
    ¬ (⟨c.V + BitVec.ofNat 64 0, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 (0 + i)) 1 := by
  intro h
  rw [BitVec.add_zero] at h
  exact L.v_w' (d := 0) (k := 16) (by decide) _ h (by
    rw [BitVec.add_zero]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))

/-- `sivIn`: the received synthetic IV copied to `W`. -/
theorem sivIn_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block sivIn) s fun s' => PK s s' ∧ Frame [⟨c.W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem c.W 16 = bytesAt s.mem c.V 16 := by
  unfold sivIn
  refine WP.mono (Bytes.copyBytes_ok (tmp := .t0) (src := .s11) (dst := .s1) (soff := 0) (doff := 0) (n := 16)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by rw [E.s11]; exact E.perm.vR (by omega_using [hi]))
    (fun i hi => by rw [E.s1]; exact E.perm.wW (by omega_using [hi]))
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
    (fun i hi => by rw [E.s1]; exact E.perm.wR (by omega_using [hi]))
    (fun i hi => by rw [E.s11]; exact in_off hV (by omega_using [hi]) (by decide))
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
      simp only [BitVec.toNat_ofNat]; omega_using [this]
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
  obtain hd : s₇.gpr .t0 =
      (s.mem.readW (c.W + BitVec.ofNat 64 0) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 tO) 64) |||
      (s.mem.readW (c.W + BitVec.ofNat 64 8) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 (tO + 8)) 64) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .t0 (by decide), u₅.gpr, u₅.other .t1 (by decide), u₄.gpr,
      u₅.other .t0 (by decide), u₄.other .t0 (by decide), u₃.gpr, u₂.gpr, u₂.other .t0 (by decide), u₁.gpr,
      u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  rw [u₁₁.gpr, u₁₀.gpr, u₁₀.other .t0 (by decide), u₉.gpr, u₈.gpr, u₈.other .t0 (by decide), hd, zero_test]
  obtain hw := Proof.AesCcm.words_eq s.mem (c.W + BitVec.ofNat 64 0) (c.W + BitVec.ofNat 64 tO)
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
  obtain pk₄ : PK s s₄ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)))
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain s0₄ : s₄.gpr .s0 = s.gpr .s0 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain r9₄ : s₄.gpr .t1 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hs0]
  obtain r3₄ : s₄.gpr .a0 = c.D := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s9]
  obtain r4₄ : s₄.gpr .a2 = BitVec.ofNat 64 c.n := by
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
      ⟨0, rfl, by omega_using [h0], by rw [r3₄]; exact (BitVec.add_zero _).symm, by rw [r4₄, Nat.sub_zero], rfl, s0₄,
        by rw [m₄]; simp [bytesAt, writeBytes_nil], pk₄⟩
    rintro w t ⟨i, rfl, hi, r3, r4, r9, s0, mem, pk⟩
    obtain Et := E.of_pk pk
    obtain hin : i + 1 ≤ c.n := by omega_using [hi]
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
    obtain pk₅ : PK s t₅ := pk.trans ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans
      ((PK.ofUpd u₄).trans (PK.ofUpd u₅)))))
    obtain hlen : ((bytesAt s.mem c.D i).map f).length = i := by rw [List.length_map, length_bytesAt]
    obtain hb : t.mem (c.D + BitVec.ofNat 64 i) = s.mem (c.D + BitVec.ofNat 64 i) := by
      rw [mem]
      have := writeBytes_end s.mem c.D ((bytesAt s.mem c.D i).map f) (by rw [hlen]; omega_using [hn, hi])
      rwa [hlen] at this
    obtain hmem : t₅.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D (i + 1)).map f) := by
      rw [u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₁.other .t1 (by decide), r9, r9₄, u₂.mem,
        u₁.mem, mask_byte, hb, mem, Proof.Cmac.Stream.bytesAt_append, bytesAt_one,
        List.map_append, List.map_singleton]
      rw [writeBytes_snoc _ _ _ _ (by rw [hlen]; omega_using [hn, hi]), hlen]
    obtain hstep : c.D + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    obtain r3' : t₅.gpr .a0 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r3, hstep]
    obtain r4' : t₅.gpr .a2 = BitVec.ofNat 64 (c.n - (i + 1)) := by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r4,
        ofNat_sub_one (by omega_using [hi]), Nat.sub_sub]
    obtain r9' : t₅.gpr .t1 = s₄.gpr .t1 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r9]
    obtain s0' : t₅.gpr .s0 = s.gpr .s0 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
        s0]
    obtain ev := eval_nz (r := .a2) (a := c.n - (i + 1)) r4' (by omega_using [hn])
    by_cases he : i + 1 = c.n
    · left
      exact ⟨by rw [ev]; simp [he], pk₅, s0', by rw [hmem, he]⟩
    · right
      exact ⟨by rw [ev]; simp; omega_using [hi, he], c.n - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], r3', r4', r9', s0', hmem, pk₅⟩

end VG.Proof.AesSiv.RISCV64

end

end

/-! ### `AesSiv.RISCV64.Entry`, which this module and modules that import it used -/

section

/-!
# AES-SIV on RISC-V: the arguments, the entry and the exit

Untrusted: everything here is checked by Lean. `encrypt` and `decrypt` are
given their public values in `a0`–`a7` (`Args`). `entry` saves our caller's
registers and the return address at `W + 128` and keeps the arguments in
`s1`–`s5` and `s9`–`s11` (`entry_wp`); `restore` reloads them, `s1`, the
base, last (`exit_wp`). The pieces write only the parts of `W` in `mutR`
and the data, so the slots stay as the entry left them. As on PPC64LE
(`Proof/AesSiv/PPC64LE/Entry.lean`); the entry saves every callee-saved
register, so none is left for the pieces to keep untouched.
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64
open VG.RISCV64 VG.RISCV64.Steps
open VG.RISCV64.Spill (saveCode saveMem Saved saveMem_saved save_ok restoreCode restore_wp)

/-- What `encrypt` and `decrypt` are given: the public values `c`. -/
structure Args (c : Cx) (s : State) : Prop where
  lay : Lay c
  a0 : s.gpr .a0 = c.C
  a1 : s.gpr .a1 = BitVec.ofNat 64 c.R
  a2 : s.gpr .a2 = c.A
  a3 : s.gpr .a3 = BitVec.ofNat 64 c.N
  a4 : s.gpr .a4 = c.D
  a5 : s.gpr .a5 = BitVec.ofNat 64 c.n
  a6 : s.gpr .a6 = c.V
  a7 : s.gpr .a7 = c.W
  perm : Perm c s

/-! ## What the pieces write -/

/-- What the pieces write: the parts of `W` below the slots and above them,
and the data. -/
abbrev mutR (c : Cx) : List Region := [⟨c.W, 128⟩, ⟨c.W + BitVec.ofNat 64 240, 2336⟩, ⟨c.D, c.n⟩]

theorem sub_lo {c : Cx} {d k : Nat} (h : d + k ≤ 128) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨c.W, 128⟩, by simp, Offset.sub_base _ h⟩

theorem sub_hi {c : Cx} {d k : Nat} (h₁ : 240 ≤ d) (h₂ : d + k ≤ 2576) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ h₁ (by omega_using [h₂])⟩

theorem sub_data {c : Cx} : ∃ r' ∈ mutR c, Region.Sub ⟨c.D, c.n⟩ r' := ⟨_, by simp, fun _ h => h⟩

/-! ## The entry -/

/-- What the entry writes: the saved registers and the return address. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 104⟩

/-- The slots of our caller's registers and of the return address, in the
order the entry saves them. -/
abbrev savedL : List (Reg × Nat) := saved ++ [(.ra, raO)]

theorem savedL_bound : ∀ p ∈ savedL, 128 ≤ p.2 ∧ p.2 + 8 ≤ 128 + 104 := by decide

theorem savedL_fits : Spill.Fits savedL := by decide

theorem savedL_off : ∀ p ∈ savedL, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

/-- The slots are kept by what the pieces write. -/
theorem slots_mut {c : Cx} (L : Lay c) : ∀ r ∈ mutR c, (entryR c.W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (Lay.w0_w (c := c) (n := 128) (d := 128) (k := 104) (Nat.le_refl _) (by decide)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm

/-- Our caller's registers, kept in their slots by writes to `mutR`. -/
theorem saved_mut {c : Cx} (L : Lay c) {g : Reg → BitVec 64} {m m' : Mem} (hf : Frame (mutR c) m m')
    (h : Saved c.W g savedL m) : Saved c.W g savedL m' :=
  h.frame_in savedL_bound hf (slots_mut L)

/-- What the entry leaves. -/
structure Entered (c : Cx) (s s₁ : State) : Prop where
  env : Env c s₁
  s4 : s₁.gpr .s4 = c.A
  s5 : s₁.gpr .s5 = BitVec.ofNat 64 c.N
  saved : Saved c.W s.gpr savedL s₁.mem
  frame : Frame [entryR c.W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

theorem entry_code : entry = saveCode .a7 savedL ++
    ([Impl.AesCbc.RISCV64.mov .s1 .a7, Impl.AesCbc.RISCV64.mov .s2 .a0, Impl.AesCbc.RISCV64.mov .s3 .a1,
      Impl.AesCbc.RISCV64.mov .s4 .a2, Impl.AesCbc.RISCV64.mov .s5 .a3, Impl.AesCbc.RISCV64.mov .s9 .a4,
      Impl.AesCbc.RISCV64.mov .s10 .a5, Impl.AesCbc.RISCV64.mov .s11 .a6] : List Instr) := rfl

theorem entry_wp {c : Cx} {s : State} (Ar : Args c s) : WP isa (.block entry) s (Entered c s) := by
  have L := Ar.lay
  have hww := L.ww
  rw [entry_code]
  refine save_ok (b := .a7) (by rw [Ar.a7]; exact L.wal) savedL_off (fun p hp => by
    rw [Ar.a7]; exact Ar.perm.wW (by have := savedL_bound p hp; omega_using [this])) ?_
  rw [Ar.a7]
  generalize hs₀ : ({ s with mem := saveMem s.mem c.W s.gpr savedL } : State) = s₀
  have g₀ : s₀.gpr = s.gpr := by rw [← hs₀]
  have rd₀ : s₀.rd = s.rd := by rw [← hs₀]
  have wr₀ : s₀.wr = s.wr := by rw [← hs₀]
  have sp₀ : s₀.sp = s.sp := by rw [← hs₀]
  have m₀ : s₀.mem = saveMem s.mem c.W s.gpr savedL := by rw [← hs₀]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  have m₈ : s₈.mem = s₀.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₈ : s₈.rd = s.rd := by
    rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rd₀]
  have wr₈ : s₈.wr = s.wr := by
    rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wr₀]
  -- Each move reads an argument register, which no earlier move writes.
  have g : ∀ r, r ∉ [Reg.s1, .s2, .s3, .s4, .s5, .s9, .s10, .s11] → s₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h9, h10, h11⟩ := hr
    rw [u₈.other _ h11, u₇.other _ h10, u₆.other _ h9, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3,
      u₂.other _ h2, u₁.other _ h1, g₀]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Ar.perm.of_eq rd₈ wr₈⟩, ?_, ?_, ?_, ?_, rd₈, wr₈, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, g₀, Ar.a7]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), g₀, Ar.a0]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), g₀, Ar.a1]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a4]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a5]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a6]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀, Ar.a2]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a3]
  · rw [m₈, m₀]; exact saveMem_saved savedL_fits _ _ _
  · rw [m₈, m₀]; exact Spill.saveMem_frame savedL_bound (by omega_using []) _ _ _
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, sp₀]

/-! ## The exit -/

/-- The slots `restore` reloads, in its order. -/
abbrev restoreL : List (Reg × Nat) := (.ra, raO) :: saved

theorem restore_code : restore = restoreCode .s1 restoreL := rfl

theorem restoreL_sub : ∀ p ∈ restoreL, p ∈ savedL := by decide

theorem preserved_restored : ∀ r ∈ preserved, r ∈ restoreL.map Prod.fst := by decide

/-- `restore`: our caller's registers and return address back, for `s₀` the
state at the entry. -/
theorem exit_wp {c : Cx} (L : Lay c) {s₀ s : State} (E : Env c s) (sv : Saved c.W s₀.gpr savedL s.mem)
    (hsp : s.sp = s₀.sp) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .a0 = s.gpr .a0 := by
  rw [restore_code]
  refine WP.mono (restore_wp (b := .s1) (B := c.W) L.wal E.s1 (by decide) (by decide) (fun p hp => by
      have := savedL_bound p (restoreL_sub p hp)
      exact E.perm.wR (by omega_using [this])) (sv.sub restoreL_sub)) fun s' R => ?_
  refine ⟨⟨fun r hr => ?_, by rw [R.sp, hsp], R.gpr (.ra, raO) List.mem_cons_self⟩, R.mem,
    R.other _ (by decide)⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (preserved_restored r hr)
  exact R.gpr p hp

end VG.Proof.AesSiv.RISCV64

end

end

/-!
# AES-SIV on RISC-V: `encrypt`

Untrusted: everything here is checked by Lean. `encS2v` saves our caller's
registers, computes S2V's first state and S2V of the associated data
(`encS2v_wp`); `encrypt` then finishes S2V with the plaintext into `W`, which
is the synthetic IV `V`, encrypts the plaintext in place by CTR from `V`'s
counter, copies `V` to `siv` and restores our caller's registers
(`encrypt_wp`). Everything but the data and `siv` that the code writes is in
`W`, which the key context, the descriptors and the components miss
(`WF`). As on PPC64LE (`Proof/AesSiv/PPC64LE/Enc.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesSiv.RISCV64
open VG.Spec.Aes (bytesAt)

/-! ## Writes within `W` -/

/-- A frame within `W`. -/
abbrev WF (c : Cx) (m m' : Mem) : Prop := Frame [⟨c.W, 2576⟩] m m'

theorem WF.of {c : Cx} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨c.W, 2576⟩) : WF c m m' :=
  h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem WF.trans {c : Cx} {m₁ m₂ m₃ : Mem} (h₁ : WF c m₁ m₂) (h₂ : WF c m₂ m₃) : WF c m₁ m₃ :=
  Frame.trans h₁ h₂

theorem wR_sub {c : Cx} : ∀ r ∈ wR c, Region.Sub r ⟨c.W, 2576⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem oR_sub {c : Cx} {out : Nat} (h : out + 16 ≤ 2576) : ∀ r ∈ oR c out, Region.Sub r ⟨c.W, 2576⟩ := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Lay.wSub h
  · exact wR_sub r hr

theorem WF.ctxMac {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') :
    Spec.Siv.ctxMac m' c.C c.R = Spec.Siv.ctxMac m c.C c.R :=
  ctxMac_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.c_w) L.rb

theorem WF.ctxCiph {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') :
    Spec.Siv.ctxCiph m' c.C c.R = Spec.Siv.ctxCiph m c.C c.R :=
  ctxCiph_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.c_w) L.rb

theorem WF.data {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') : bytesAt m' c.D c.n = bytesAt m c.D c.n :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.d_w) (by have := L.n_lt; omega_using [this])

theorem WF.descW {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') {i j : Nat} (hi : i < c.N) (hj : j < 2) :
    descW m' c.A i j = descW m c.A i j := by
  have aw := L.aw
  exact h.readW (r := ⟨c.A + BitVec.ofNat 64 (16 * i + 8 * j), 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.a_w.sub_left (Offset.sub_base _ (by omega_using [hi, hj]))) (by decide)

theorem WF.ads {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') {s : State} (hA : Ads c m s) : Ads c m' s :=
  fun i hi => by rw [h.descW L hi (by decide), h.descW L hi (by decide)]; exact hA i hi

/-- The `i`-th region the descriptors list. -/
theorem listed_eq (m : Mem) (A : Addr) (i : Nat) :
    (⟨(m.readW (A + BitVec.ofNat 64 (i * (2 * (64 / 8)))) 64).setWidth 64,
      (m.readW (A + BitVec.ofNat 64 (i * (2 * (64 / 8))) + BitVec.ofNat 64 (64 / 8)) 64).toNat * Elem.size .u8⟩ :
        Region) = ⟨descW m A i 0, (descW m A i 1).toNat⟩ := by
  simp only [descW, BitVec.setWidth_eq, Elem.size, Nat.mul_one]
  rw [show i * (2 * (64 / 8)) = 16 * i + 8 * 0 by omega_using [], show (64 / 8 : Nat) = 8 from rfl, Offset.add_add,
    show 16 * i + 8 * 0 + 8 = 16 * i + 8 * 1 by omega_using []]

theorem WF.components {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') {s : State} (hA : Ads c m s) :
    Spec.Siv.components 64 m' c.A c.N = Spec.Siv.components 64 m c.A c.N := by
  refine Proof.AesSiv.components_congr fun r hr a ha => (h a fun r' hr' hc => ?_).symm
  simp only [List.mem_singleton] at hr'; subst hr'
  rcases List.mem_cons.mp hr with rfl | hr
  · refine L.a_w a ?_ hc
    simp only [Sig.descRegion, Region.Contains] at ha ⊢
    omega_using [ha]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hb := (hA i (List.mem_range.mp hi)).w
    rw [listed_eq] at ha
    exact hb a ha hc

/-! ## S2V of the associated data -/

/-- What S2V of the associated data leaves, from the state `σ` at the entry
and the state `s₁` after it. -/
structure S2vDone (c : Cx) (σ s₁ s : State) : Prop where
  en : Entered c σ s₁
  inv : AInv c s₁ c.N s

theorem encS2v_wp {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ s₁ s', S2vDone c s s₁ s' → s'.gpr .s6 = c.D → s'.gpr .s7 = BitVec.ofNat 64 c.n → WP isa rest s' Q) :
    WP isa (.seq encS2v rest) s Q := by
  have L := Ar.lay
  unfold encS2v
  refine WP.seq (WP.seq (WP.block_append_iff.mpr (WP.mono (entry_wp Ar) fun s₁ En => ?_)))
  have E₁ := En.env
  refine WP.mono (WP.seq_iff.mp (start_wp L E₁)) fun s₂' h => WP.seq (WP.mono h fun s₂ ⟨K₂, f₂, d₂⟩ => ?_)
  have wf₁ : WF c s.mem s₁.mem := WF.of En.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  have I₀ : AInv c s₁ 0 s₂ :=
    { env := E₁.of_pk K₂.pk
      pk := K₂.pk
      ads := (wf₁.ads L hA).of_eq (by rw [K₂.pk.rd, En.rd]) (by rw [K₂.pk.wr, En.wr])
      s4 := by rw [K₂.s4, En.s4, Nat.mul_zero, BitVec.add_zero]
      s5 := by rw [K₂.s5, En.s5, Nat.sub_zero]
      frame := f₂
      acc := by rw [d₂, List.take_zero, Spec.Siv.s2vAcc, List.foldl_nil] }
  refine WP.seq (WP.mono (s2vAds_wp L I₀) fun s₃ I₃ => ?_)
  refine wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil ?_
  have pk₅ : PK s₃ s₅ := (PK.ofUpd u₄).trans (PK.ofUpd u₅)
  refine k s₁ s₅ ⟨En, ⟨I₃.env.of_pk pk₅, I₃.pk.trans pk₅, I₃.ads.of_eq pk₅.rd pk₅.wr,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), I₃.s4],
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), I₃.s5],
      by rw [u₅.mem, u₄.mem]; exact I₃.frame, by rw [u₅.mem, u₄.mem]; exact I₃.acc⟩⟩
    (by rw [u₅.other _ (by decide), u₄.gpr, I₃.env.s9])
    (by rw [u₅.gpr, u₄.other _ (by decide), I₃.env.s10])

/-- The facts of `S2vDone` about the entry's memory. -/
theorem S2vDone.facts {c : Cx} (L : Lay c) {σ s₁ s : State} (h : S2vDone c σ s₁ s) (hA : Ads c σ.mem σ) :
    WF c σ.mem s.mem ∧ bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16 =
      Spec.Siv.s2vAcc (Spec.Siv.ctxMac σ.mem c.C c.R) (Spec.Siv.components 64 σ.mem c.A c.N) := by
  have wf₁ : WF c σ.mem s₁.mem := WF.of h.en.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  refine ⟨wf₁.trans (WF.of h.inv.frame wR_sub), ?_⟩
  rw [h.inv.acc, List.take_of_length_le (by rw [length_components]), wf₁.ctxMac L, wf₁.components L hA]

/-! ## `encrypt` -/

theorem mutR_wR {c : Cx} : ∀ r ∈ wR c, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)

theorem mutR_oR {c : Cx} {out : Nat} (h : out + 16 ≤ 128) : ∀ r ∈ oR c out, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact sub_lo h
  · exact mutR_wR r hr

theorem mutR_ctrR {c : Cx} : ∀ r ∈ ctrR c, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_data
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)

theorem ctrR_W0 {c : Cx} (L : Lay c) :
    ∀ r ∈ ctrR c, (⟨c.W + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.d_w' (by decide)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- `vg_aes_siv_encrypt`: `encryptWith`'s synthetic IV at `siv` and ciphertext
at `data`. -/
theorem encrypt_wp {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) (hV : Covers [⟨c.V, 16⟩] s.wr) :
    WP isa encrypt s fun s' => abiPreserved s s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem c.C c.R) (Spec.Siv.ctxCiph s.mem c.C c.R)
          (Spec.Siv.components 64 s.mem c.A c.N) (bytesAt s.mem c.D c.n) =
        (bytesAt s'.mem c.V 16, bytesAt s'.mem c.D c.n) := by
  have L := Ar.lay
  unfold encrypt
  refine encS2v_wp Ar hA fun s₁ s₄ S h6 h7 => ?_
  obtain ⟨wf₄, acc₄⟩ := S.facts L hA
  have E₄ := S.inv.env
  refine WP.seq (WP.mono (finish_wp L E₄ (L.bufD E₄.perm) h6 h7 (out := 0) (.inl rfl))
    fun s₅ ⟨pk₅, f₅, v₅⟩ => ?_)
  have E₅ := E₄.of_pk pk₅
  have wf₅ : WF c s.mem s₅.mem := wf₄.trans (WF.of f₅ (oR_sub (by decide)))
  refine WP.seq (WP.mono (ctr_wp L E₅ (src := 0) (by decide) (by decide)) fun s₆ ⟨pk₆, f₆, d₆⟩ => ?_)
  have E₆ := E₅.of_pk pk₆
  have pk₁₆ : PK s₁ s₆ := S.inv.pk.trans (pk₅.trans pk₆)
  refine WP.block_append_iff.mpr (WP.mono (sivOut_wp L E₆ (by rw [pk₁₆.wr, S.en.wr]; exact hV))
    fun s₇ ⟨pk₇, f₇, v₇⟩ => ?_)
  have E₇ := E₆.of_pk pk₇
  have pk₁₇ : PK s₁ s₇ := pk₁₆.trans pk₇
  -- Our caller's registers, in their slots.
  have fm : Frame (mutR c) s₁.mem s₆.mem :=
    ((S.inv.frame.sub mutR_wR).trans (f₅.sub (mutR_oR (by decide)))).trans (f₆.sub mutR_ctrR)
  have sv₇ : Spill.Saved c.W s.gpr savedL s₇.mem :=
    (saved_mut L fm S.en.saved).frame_in savedL_bound f₇ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.v_w' (by decide)).symm
  refine WP.mono (exit_wp L E₇ sv₇ (by rw [pk₁₇.sp, S.en.sp])) fun s₈ ⟨ab, m₈, _⟩ => ⟨ab, ?_⟩
  -- The synthetic IV and the ciphertext.
  have v₆ : bytesAt s₆.mem c.W 16 = bytesAt s₅.mem c.W 16 := by
    have := Proof.Cmac.bytesAt_frame f₆ (ctrR_W0 L) (by decide)
    rwa [BitVec.add_zero] at this
  rw [BitVec.add_zero] at v₅ d₆
  rw [Spec.Siv.encryptWith_eq, Spec.Siv.sealWith]
  have hv : bytesAt s₈.mem c.V 16 = Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem c.C c.R) (Spec.Siv.components 64 s.mem c.A c.N))
      (bytesAt s.mem c.D c.n) := by
    rw [m₈, v₇, v₆, v₅, wf₄.ctxMac L, wf₄.data L, acc₄]
  have hd : bytesAt s₈.mem c.D c.n = bytesAt s₆.mem c.D c.n := by
    rw [m₈]
    exact Proof.Cmac.bytesAt_frame f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.v_d.symm) (by have := L.n_lt; omega_using [this])
  rw [hv, hd, d₆, wf₅.ctxCiph L, wf₅.data L, v₅, wf₄.ctxMac L, wf₄.data L, acc₄]

end VG.Proof.AesSiv.RISCV64

end

end

/-!
# AES-SIV on RISC-V: `decrypt`

Untrusted: everything here is checked by Lean. After S2V of the associated
data (`encS2v_wp`), `decrypt` copies the received synthetic IV `V` to `W`,
decrypts the data in place by CTR from `V`'s counter, finishes S2V with the
plaintext into `W + 112`, compares the two IVs without a branch, ANDs every
byte of the data with the mask of the comparison and returns its result
(`decrypt_wp`). As on PPC64LE (`Proof/AesSiv/PPC64LE/Dec.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesSiv.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_siv_decrypt`: with `P` the plaintext of the data under the
received synthetic IV `V` and `T` S2V's IV of it, the result is whether
`V = T`, and the data is `P`, or zeros if not. -/
theorem decrypt_wp {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) :
    WP isa decrypt s fun s' => abiPreserved s s' ∧
      let mac := Spec.Siv.ctxMac s.mem c.C c.R
      let V := bytesAt s.mem c.V 16
      let P := Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem c.C c.R) (Spec.Siv.counter V) (bytesAt s.mem c.D c.n)
      let T := Spec.Siv.s2vFinish mac (Spec.Siv.s2vAcc mac (Spec.Siv.components 64 s.mem c.A c.N)) P
      s'.gpr .a0 = BitVec.ofNat 64 (if V = T then 1 else 0) ∧
        bytesAt s'.mem c.D c.n = P.map fun b => if V = T then b else 0 := by
  have L := Ar.lay
  have hn := L.n_lt
  unfold decrypt
  refine encS2v_wp Ar hA fun s₁ s₄ S _ _ => ?_
  obtain ⟨wf₄, acc₄⟩ := S.facts L hA
  have E₄ := S.inv.env
  -- The received IV in.
  refine WP.seq (WP.mono (sivIn_wp L E₄) fun s₅ ⟨pk₅, f₅, b₅⟩ => ?_)
  obtain E₅ := E₄.of_pk pk₅
  obtain wf₅ : WF c s.mem s₅.mem := wf₄.trans (WF.of f₅ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide))
  obtain v₅ : bytesAt s₅.mem (c.W + BitVec.ofNat 64 0) 16 = bytesAt s.mem c.V 16 := by
    rw [BitVec.add_zero, b₅]
    exact Proof.Cmac.bytesAt_frame wf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.v_w) (by decide)
  obtain a₅ : bytesAt s₅.mem (c.W + BitVec.ofNat 64 dO) 16 = bytesAt s₄.mem (c.W + BitVec.ofNat 64 dO) 16 :=
    Proof.Cmac.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Lay.w0_w (c := c) (n := 16) (d := dO) (k := 16) (by decide) (by decide)).symm) (by decide)
  -- CTR.
  refine WP.seq (WP.mono (ctr_wp L E₅ (src := 0) (by decide) (by decide)) fun s₆ ⟨pk₆, f₆, d₆⟩ => ?_)
  obtain E₆ := E₅.of_pk pk₆
  obtain v₆ : bytesAt s₆.mem (c.W + BitVec.ofNat 64 0) 16 = bytesAt s₅.mem (c.W + BitVec.ofNat 64 0) 16 :=
    Proof.Cmac.bytesAt_frame f₆ (ctrR_W0 L) (by decide)
  obtain a₆ : bytesAt s₆.mem (c.W + BitVec.ofNat 64 dO) 16 = bytesAt s₅.mem (c.W + BitVec.ofNat 64 dO) 16 :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (L.d_w' (by decide)).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  obtain mac₆ : Spec.Siv.ctxMac s₆.mem c.C c.R = Spec.Siv.ctxMac s.mem c.C c.R := by
    rw [ctxMac_frame f₆ (ctrR_c L) L.rb, wf₅.ctxMac L]
  -- The plaintext as S2V's string, and S2V's end.
  refine WP.seq (wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_)
  obtain pk₈ : PK s₆ s₈ := (PK.ofUpd u₇).trans (PK.ofUpd u₈)
  obtain E₈ := E₆.of_pk pk₈
  obtain m₈ : s₈.mem = s₆.mem := by rw [u₈.mem, u₇.mem]
  refine WP.seq (WP.mono (finish_wp L E₈ (L.bufD E₈.perm) (by rw [u₈.other _ (by decide), u₇.gpr, E₆.s9])
    (by rw [u₈.gpr, u₇.other _ (by decide), E₆.s10]) (out := tO) (.inr rfl)) fun s₉ ⟨pk₉, f₉, t₉⟩ => ?_)
  obtain E₉ := E₈.of_pk pk₉
  obtain v₉ : bytesAt s₉.mem c.W 16 = bytesAt s₈.mem c.W 16 := by
    have := Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (p := c.W + BitVec.ofNat 64 0) (n := 16)
      (by decide)
    rwa [BitVec.add_zero] at this
  obtain wf₉ : WF c s₈.mem s₉.mem := WF.of f₉ (oR_sub (by decide))
  -- The comparison and the mask.
  refine WP.seq (WP.mono (compare_wp L E₉) fun s₁₀ ⟨pk₁₀, m₁₀, s0₁₀⟩ => ?_)
  obtain E₁₀ := E₉.of_pk pk₁₀
  refine WP.seq (WP.mono (mask_wp L E₁₀ s0₁₀) fun s₁₁ ⟨pk₁₁, s0₁₁, m₁₁⟩ => ?_)
  obtain E₁₁ := E₁₀.of_pk pk₁₁
  refine WP.block_append_iff.mpr (wp_mv fun s₁₂ u₁₂ => WP.block_nil ?_)
  obtain E₁₂ := E₁₁.of_pk (PK.ofUpd u₁₂)
  obtain pk₁₂ : PK s₁ s₁₂ := S.inv.pk.trans (pk₅.trans (pk₆.trans (pk₈.trans (pk₉.trans (pk₁₀.trans (pk₁₁.trans
    (PK.ofUpd u₁₂)))))))
  -- Our caller's registers, in their slots.
  obtain fd : Frame [⟨c.D, c.n⟩] s₁₀.mem s₁₁.mem := by
    rw [m₁₁]
    exact writeBytes_frame _ _ _ (by
      rw [List.length_map, Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)
  obtain f₄₅ : Frame (mutR c) s₄.mem s₅.mem :=
    f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W, 128⟩, by simp, Region.sub_prefix (by decide)⟩
  obtain f₆₉ : Frame (mutR c) s₆.mem s₉.mem := by rw [← m₈]; exact f₉.sub (mutR_oR (by decide))
  obtain f₉₁₁ : Frame (mutR c) s₉.mem s₁₁.mem := by
    rw [← m₁₀]
    refine fd.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact sub_data
  obtain fm : Frame (mutR c) s₁.mem s₁₂.mem := by
    rw [u₁₂.mem]
    exact ((((S.inv.frame.sub mutR_wR).trans f₄₅).trans (f₆.sub mutR_ctrR)).trans f₆₉).trans f₉₁₁
  refine WP.mono (exit_wp L E₁₂ (saved_mut L fm S.en.saved) (by rw [pk₁₂.sp, S.en.sp]))
    fun s₁₃ ⟨ab, m₁₃, a0₁₃⟩ => ⟨ab, ?_⟩
  -- The IVs, the plaintext and the result.
  obtain hV : bytesAt s₉.mem c.W 16 = bytesAt s.mem c.V 16 := by
    have := v₆.trans v₅
    rw [BitVec.add_zero] at this
    rw [v₉, m₈, this]
  obtain hP : bytesAt s₉.mem c.D c.n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem c.C c.R)
      (Spec.Siv.counter (bytesAt s.mem c.V 16)) (bytesAt s.mem c.D c.n) := by
    rw [wf₉.data L, m₈, d₆, v₅, wf₅.ctxCiph L, wf₅.data L]
  obtain hT : bytesAt s₉.mem (c.W + BitVec.ofNat 64 tO) 16 = Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem c.C c.R) (Spec.Siv.components 64 s.mem c.A c.N))
      (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem c.C c.R) (Spec.Siv.counter (bytesAt s.mem c.V 16))
        (bytesAt s.mem c.D c.n)) := by
    rw [t₉, m₈, mac₆, a₆, a₅, acc₄, ← hP, wf₉.data L, m₈]
  refine ⟨?_, ?_⟩
  · rw [a0₁₃, u₁₂.gpr, s0₁₁, s0₁₀, hV, hT]
  · rw [m₁₃, u₁₂.mem, m₁₁, m₁₀, hV, hT, hP]
    obtain key : ∀ xs : List Byte, xs.length = c.n → bytesAt (writeBytes s₉.mem c.D xs) c.D c.n = xs := by
      intro xs hx
      have := Proof.AesCcm.bytesAt_writeBytes_base s₉.mem c.D xs (n := c.n) (by omega_using [hx]) hn
      rwa [hx, List.drop_eq_nil_of_le (by rw [Proof.Cmac.bytesAt_length]), List.append_nil] at this
    exact key _ (by rw [List.length_map, ← hP, Proof.Cmac.bytesAt_length])

end VG.Proof.AesSiv.RISCV64

end

end

/-! ### `AesSiv.RISCV64.CtrCT`, which only this module used -/

section

/-!
# AES-SIV on RISC-V: CTR in two runs

Untrusted: everything here is checked by Lean. `ctrWhole`, a block of the
rest (`ctrBody`) and the whole of `ctr src`, run from two states in the same
environment, leak the same: the code between calls by the taint analysis
(`rel_env`), from the environment's registers and the data pointer and
length left, `s6` and `s7`, which are public in both runs, and each call of
`vg_aes_ctr32` by its proof (`rel_ctr`). The counter `Q` is the IV's and
differs between the runs, but only its bytes in memory, never an address or
a branch. The loop of blocks relates two runs after the same number of
blocks, which the correctness proofs describe (`CInv`). As on PPC64LE
(`Proof/AesSiv/PPC64LE/CtrCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp rel_seqR rel_of_eq2 rel_post)
open VG.Proof.AesCtr.RISCV64 (CtrCall ctr_call)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_ite)
open VG.Spec.Aes (bytesAt)

/-- `ctrPre`: the arguments of `vg_aes_ctr32` for the keystream block. -/
theorem ctrPre_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block ctrPre) s fun s' => PK s s' ∧ s'.gpr .s6 = s.gpr .s6 ∧ s'.gpr .s7 = s.gpr .s7 ∧
      CtrCall s' (c.C + BitVec.ofNat 64 272) (c.W + BitVec.ofNat 64 cbO) (c.W + BitVec.ofNat 64 ksO)
        (c.W + BitVec.ofNat 64 384) c.R 1 := by
  unfold ctrPre
  simp only [List.append_assoc]
  refine zero16_wp L E (d := ksO) (by decide) (by decide) fun s₁ pk₁ g₁ _ => ?_
  have E₁ := E.of_pk pk₁
  refine copy16_wp L E₁ (by decide) (by decide) (by decide) (by decide) (by decide) fun s₂ pk₂ g₂ _ => ?_
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (imm := 272) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ => wp_li (imm := 1) (by decide) fun s₈ u₈ =>
    WP.block_nil ?_
  have pk₈ : PK s₂ s₈ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))
  have E₈ := E.of_pk (pk₁.trans (pk₂.trans pk₈))
  refine ⟨pk₁.trans (pk₂.trans pk₈),
    by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁],
    by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁], ?_⟩
  exact cargsW L E₈ (o := cbO) (by decide) (d := ksO) (by decide) (.inr (by decide))
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, g₁, E.s2])
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, g₁, E.s3])
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, g₁, E.s1])
    (by simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁, E.s1])
    (by simp (disch := decide) only [u₈.gpr])
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, g₁, E.s1]; rfl)

/-- What a call of `vg_aes_ctr32` keeps. -/
theorem ctrCall_keep {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    Runs Impl.AesCtr.RISCV64.ctrCall s fun t => PK s t ∧ t.gpr .s6 = s.gpr .s6 ∧ t.gpr .s7 = s.gpr .s7 :=
  Runs.of_wp (WP.mono (ctr_call h) fun _ h' =>
    ⟨PK.ofSaved h'.rd h'.wr h'.sp h'.saved, h'.saved _ (by decide), h'.saved _ (by decide)⟩)

/-- What a block of CTR leaves, from block `i`. -/
theorem ctrBody_runs {c : Cx} (L : Lay c) {s₀ s : State} {q : List Byte} {i : Nat} (E₀ : Env c s₀)
    (hlow64 : Spec.Siv.beNat q % 2 ^ 64 < 2 ^ 63) (I : CInv c s₀ q i s) (hi : 16 * i < c.n) :
    Runs ctrBody s (Stepped c s₀ q i s) :=
  Runs.of_wp (by unfold ctrBody; exact ctrHead_wp L I hi E₀ fun _ H => ctrTail_wp L I hi E₀ hlow64 H)

/-! ## Two runs -/

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
include L E₁ E₂ hsp

/-- `ctrWhole`: the whole blocks by one call. -/
theorem ctrWhole_rel : RelCT isa (Eq2 σ₁ σ₂) ctrWhole TT := by
  unfold ctrWhole
  refine rel_seqR (rel_env [] E₁ E₂ hsp agree_nil ⟨_, by taint_decide⟩) (Runs.of_wp (wholePre_wp L E₁))
    (Runs.of_wp (wholePre_wp L E₂)) fun τ₁ τ₂ ⟨pk₁, s6₁, s7₁, _, C₁⟩ ⟨pk₂, s6₂, s7₂, _, C₂⟩ => ?_
  have hspτ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (rel_ctr C₁ C₂ hspτ) (ctrCall_keep C₁) (ctrCall_keep C₂)
    fun ρ₁ ρ₂ ⟨k₁, a6₁, a7₁⟩ ⟨k₂, a6₂, a7₂⟩ => ?_
  exact rel_env [.s6, .s7] (E₁.of_pk (pk₁.trans k₁)) (E₂.of_pk (pk₂.trans k₂)) (by rw [k₁.sp, k₂.sp, hspτ])
    (agree_cons (by rw [a6₁, a6₂, s6₁, s6₂]) (agree_cons (by rw [a7₁, a7₂, s7₁, s7₂]) agree_nil))
    ⟨_, by taint_decide⟩

/-- A block of CTR, from two states that agree on the data pointer and the
length left. -/
theorem ctrBody_rel (h6 : σ₁.gpr .s6 = σ₂.gpr .s6) (h7 : σ₁.gpr .s7 = σ₂.gpr .s7) :
    RelCT isa (Eq2 σ₁ σ₂) ctrBody TT := by
  unfold ctrBody
  refine rel_seqR (rel_env [] E₁ E₂ hsp agree_nil ⟨_, by taint_decide⟩) (Runs.of_wp (ctrPre_wp L E₁))
    (Runs.of_wp (ctrPre_wp L E₂)) fun τ₁ τ₂ ⟨pk₁, s6₁, s7₁, C₁⟩ ⟨pk₂, s6₂, s7₂, C₂⟩ => ?_
  have hspτ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (rel_ctr C₁ C₂ hspτ) (ctrCall_keep C₁) (ctrCall_keep C₂)
    fun ρ₁ ρ₂ ⟨k₁, a6₁, a7₁⟩ ⟨k₂, a6₂, a7₂⟩ => ?_
  exact rel_env [.s6, .s7] (E₁.of_pk (pk₁.trans k₁)) (E₂.of_pk (pk₂.trans k₂)) (by rw [k₁.sp, k₂.sp, hspτ])
    (agree_cons (by rw [a6₁, a6₂, s6₁, s6₂, h6]) (agree_cons (by rw [a7₁, a7₂, s7₁, s7₂, h7]) agree_nil))
    ⟨_, by taint_decide⟩

/-- `ctr src`: CTR from the counter of the IV at `W + src`. -/
theorem ctr_rel {src : Nat} (hsrc : src + 16 ≤ cntO) (hsrc8 : src % 8 = 0) : RelCT isa (Eq2 σ₁ σ₂) (ctr src) TT := by
  have hn := L.n_lt
  have hk := wholeOf_le c.n
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [])) (.block (counter src)) h).isSome = true := by
    have : src = 0 ∨ src = 8 ∨ src = 16 ∨ src = 24 ∨ src = 32 ∨ src = 40 ∨ src = 48 := by
      simp only [cntO] at hsrc; omega_arith
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  -- The counter `Q`, in each run.
  have start : ∀ {σ : State}, Env c σ → Runs (.block (counter src)) σ fun τ => PK σ τ ∧ ∃ q : List Byte,
      q.length = 16 ∧ Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31 ∧ Spec.Siv.beNat q % 2 ^ 64 < 2 ^ 63 ∧
        CntAt τ.mem c.W q 0 := fun E =>
    Runs.of_wp (by
      rw [← List.append_nil (counter src)]
      exact counter_wp L E hsrc hsrc8 fun _ pk _ hq =>
        WP.block_nil ⟨pk, _, length_counter _, counter_low _, counter_low64 _, cnt_init hq⟩)
  unfold ctr
  refine rel_seqR (rel_env [] E₁ E₂ hsp agree_nil t) (start E₁) (start E₂)
    fun τ₁ τ₂ ⟨pk₁, Q₁, hl₁, lo₁, hi₁, q₁⟩ ⟨pk₂, Q₂, hl₂, lo₂, hi₂, q₂⟩ => ?_
  have F₁ := E₁.of_pk pk₁
  have F₂ := E₂.of_pk pk₂
  have hspτ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (ctrWhole_rel L F₁ F₂ hspτ) (Runs.of_wp (ctrWhole_wp L F₁ hl₁ lo₁ hi₁ q₁))
    (Runs.of_wp (ctrWhole_wp L F₂ hl₂ lo₂ hi₂ q₂)) fun ρ₁ ρ₂ I₁ I₂ => ?_
  refine rel_ite (evalZ I₁.s7 (by omega_arith)) (evalZ I₂.s7 (by omega_arith)) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] (F₁.of_pk I₁.pk) (F₂.of_pk I₂.pk) (by rw [I₁.pk.sp, I₂.pk.sp, hspτ]) agree_nil
      ⟨_, by taint_decide⟩
  have h0 : 16 * wholeOf c.n < c.n := by
    have : c.n - 16 * wholeOf c.n ≠ 0 := by simpa using hf
    omega_arith
  refine (RelCT.loop (Q := TT) (fun m (a b : State) => ∃ i, m = c.n - 16 * i ∧ 16 * i < c.n ∧
      CInv c τ₁ Q₁ i a ∧ CInv c τ₂ Q₂ i b) (fun m => ?_) (c.n - 16 * wholeOf c.n)).mono
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨wholeOf c.n, rfl, h0, I₁, I₂⟩) fun _ _ h => h
  refine rel_of_eq2 fun a b ⟨i, hm, hi, J₁, J₂⟩ => ?_
  refine (rel_post (ctrBody_rel L (F₁.of_pk J₁.pk) (F₂.of_pk J₂.pk) (by rw [J₁.pk.sp, J₂.pk.sp, hspτ])
      (by rw [J₁.s6, J₂.s6]) (by rw [J₁.s7, J₂.s7]))
    (ctrBody_runs L F₁ hi₁ J₁ hi) (ctrBody_runs L F₂ hi₂ J₂ hi)).mono (fun _ _ h => h) fun a' b' ⟨S₁, S₂⟩ => ?_
  have ev₁ := evalNZ S₁.s7 (by omega_arith)
  have ev₂ := evalNZ S₂.s7 (by omega_arith)
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
  rw [ev₁] at ht
  have hgt : 16 < c.n - 16 * i := by simp at ht; omega_arith
  have mk : ∀ {τ u u' : State} {q : List Byte}, CInv c τ q i u → Stepped c τ q i u u' →
      CInv c τ q (i + 1) u' := fun J S =>
    ⟨J.pk.trans S.pk, S.s6, by rw [S.s7]; congr 1; omega_arith, by omega_arith, S.cnt,
      by rw [S.data]; congr 1; omega_arith, S.frame⟩
  exact ⟨c.n - 16 * (i + 1), by omega_arith, i + 1, rfl, by omega_arith, mk J₁ S₁, mk J₂ S₂⟩

end

end VG.Proof.AesSiv.RISCV64

end

end

/-! ### `AesSiv.RISCV64.MacCT`, which this module and modules that import it used -/

section

/-!
# AES-SIV on RISC-V: S2V in two runs

Untrusted: everything here is checked by Lean. Each piece of S2V, run from
two states satisfying its correctness proof's hypotheses in the same
environment, leaks the same: the code between calls by the taint analysis
(`rel_env`), from the environment's registers and those on which the two
runs agree (the descriptor pointer and count `s4` and `s5`, the string's
address and length `s6` and `s7`, and what the code derives from the
length, `s8` and `s0`), and each call of `vg_cmac_aes_update` and
`vg_cmac_aes_finalize` by its proof (`rel_upd`, `rel_fin`), from the
arguments the correctness proofs give it. The loop over the components of
associated data relates two runs after the same number of components
(`AInv`), whose descriptors are public. As on PPC64LE
(`Proof/AesSiv/PPC64LE/MacCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Proof.CmacAes.Stream.RISCV64 (UArgs upd_call FArgs)
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp rel_seqR rel_of_eq2 rel_post)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_ite)
open VG.Spec.Aes (bytesAt)

/-! ## What the pieces set before the calls -/

/-- `cmacArgs₁`: the arguments of the update over the whole blocks. -/
theorem cmacArgs₁_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {st : Nat} (hst : st + 16 ≤ 384)
    {P : Addr} {n : Nat} (hP : Buf c s P n) (h19 : s.gpr .s6 = P)
    (h21 : s.gpr .s8 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) :
    WP isa (.block (cmacArgs₁ st)) s fun s₂ => MacKeep s s₂ ∧ s₂.gpr .s8 = s.gpr .s8 ∧
      UArgs s₂ c.C (c.W + BitVec.ofNat 64 st) P (c.W + BitVec.ofNat 64 384) c.R (Spec.Cmac.chainedLen 16 n / 16) := by
  have hn := hP.lt
  obtain hcl := chainedLen_le n
  obtain hcd := chainedLen_div n
  unfold cmacArgs₁ macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_mv fun t₅ v₅ => wp_srl (by decide) fun t₆ v₆ =>
    WP.block_nil ?_
  obtain K : MacKeep s t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
  obtain E₆ := E.of_pk K.pk
  obtain hq := (hP.take hcl).of_eq K.pk.rd K.pk.wr
  rw [← hcd] at hq
  refine ⟨K, by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)], ?_⟩
  exact uargs L E₆ hst hq.src (hq.wd (d := st) (k := 16) (by omega_arith)) (by omega_arith)
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E.s1])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h19])
    (by rw [v₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h21, ofNat_lsr4' (by omega_arith)])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E.s1]; rfl)

/-- `cmacArgs₂`: the arguments of the finalization of the last bytes. -/
theorem cmacArgs₂_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {st : Nat} (hst : st + 16 ≤ 384)
    {P : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hq : Buf c s (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n))
    (h19 : s.gpr .s6 = P) (h20 : s.gpr .s7 = BitVec.ofNat 64 n)
    (h21 : s.gpr .s8 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) :
    WP isa (.block (cmacArgs₂ st)) s fun s₄ => MacKeep s s₄ ∧
      FArgs s₄ c.C (c.W + BitVec.ofNat 64 st) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n))
        (c.W + BitVec.ofNat 64 384) (n - Spec.Cmac.chainedLen 16 n) c.R := by
  obtain hcl := chainedLen_le n
  obtain hrest := chainedLen_rest n
  unfold cmacArgs₂ macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_add fun t₅ v₅ => wp_sub fun t₆ v₆ =>
    WP.block_nil ?_
  obtain K : MacKeep s t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
  obtain E₆ := E.of_pk K.pk
  obtain hq' := hq.of_eq K.pk.rd K.pk.wr
  refine ⟨K, ?_⟩
  exact fargs L E₆ hst hrest hq'.src (hq'.wd (by omega_arith))
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E.s1])
    (by simp (disch := decide) only [v₆.other, v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, h19, h21])
    (by
      simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, h20, h21]
      exact ofNat_sub' hcl hn)
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E.s1]; rfl)

/-- `shortArgs out`: the state at `W + out` zeroed, and the arguments of the
finalization of the tail. -/
theorem shortArgs_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (.block (shortArgs out)) s fun s' => PK s s' ∧
      FArgs s' c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 384) 16 c.R := by
  obtain ho : out + 16 ≤ tailO ∨ tailO + 16 ≤ out := by rcases hout with rfl | rfl <;> decide
  obtain ho' : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  obtain ho8 : out % 8 = 0 := by rcases hout with rfl | rfl <;> decide
  unfold shortArgs
  rw [List.append_assoc]
  refine zero16_wp L E (d := out) (by omega_arith) ho8 fun s₁ pk₁ _ _ => ?_
  obtain E₁ := E.of_pk pk₁
  unfold macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
    wp_li (by decide) fun t₆ v₆ => WP.block_nil ?_
  obtain pk₆ : PK s₁ t₆ := (PK.ofUpd v₁).trans ((PK.ofUpd v₂).trans ((PK.ofUpd v₃).trans ((PK.ofUpd v₄).trans
    ((PK.ofUpd v₅).trans (PK.ofUpd v₆)))))
  obtain E₆ := E₁.of_pk pk₆
  exact ⟨pk₁.trans pk₆, fargs L E₆ (y := out) ho' (Nat.le_refl 16) (L.srcW E₆.perm (t := tailO) (k := 16) (by decide))
    (L.w_w (by omega_arith) (by decide) (by omega_arith))
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E₁.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E₁.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1])
    (by rw [v₆.gpr])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1]; rfl)⟩

/-- `longArgs₁ out`: the state at `W + out` zeroed, and the arguments of the
update over the `k` blocks of `P`. -/
theorem longArgs₁_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n k : Nat} (hP : Buf c s P n)
    (hk : 16 * k ≤ n) (h19 : s.gpr .s6 = P) (h21 : s.gpr .s8 = BitVec.ofNat 64 (16 * k)) {out : Nat}
    (hout : out = 0 ∨ out = tO) :
    WP isa (.block (longArgs₁ out)) s fun s₁ => MacKeep s s₁ ∧ s₁.gpr .s8 = s.gpr .s8 ∧
      UArgs s₁ c.C (c.W + BitVec.ofNat 64 out) P (c.W + BitVec.ofNat 64 384) c.R k := by
  have hn := hP.lt
  obtain ho : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  obtain ho8 : out % 8 = 0 := by rcases hout with rfl | rfl <;> decide
  unfold longArgs₁
  refine zero16_wp L E (d := out) (by omega_arith) ho8 fun s₀ pk₀ g₀ _ => ?_
  simp only [List.append_eq, List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_mv fun t₅ v₅ => wp_srl (by decide) fun t₆ v₆ =>
    WP.block_nil ?_
  obtain K₀ : MacKeep s s₀ := ⟨pk₀, g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide)⟩
  obtain K : MacKeep s₀ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
  obtain E₀ := E.of_pk pk₀
  obtain E₆ := E₀.of_pk K.pk
  obtain hq := (hP.take hk).of_eq (by rw [K.pk.rd, pk₀.rd]) (by rw [K.pk.wr, pk₀.wr])
  obtain r21₆ : t₆.gpr .s8 = s.gpr .s8 := by
    simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, g₀]
  refine ⟨K₀.trans K, r21₆, ?_⟩
  exact uargs L E₆ ho hq.src (hq.wd (d := out) (k := 16) (by omega_arith)) (by omega_arith)
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E₀.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E₀.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E₀.s1])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), g₀ _ (by decide), h19])
    (by
      simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, g₀, h21]
      rw [ofNat_lsr4' (by omega_arith), show 16 * k / 16 = k by omega_arith])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₀.s1]; rfl)

/-- `longArgs₂ out`: the arguments of the update over the first `j` blocks of
the tail. -/
theorem longArgs₂_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {n : Nat}
    (h25 : s.gpr .s0 = BitVec.ofNat 64 (jOf n)) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (.block (longArgs₂ out)) s fun s₄ => MacKeep s s₄ ∧ s₄.gpr .s8 = s.gpr .s8 ∧
      s₄.gpr .s0 = s.gpr .s0 ∧
      UArgs s₄ c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 384) c.R
        (jOf n) := by
  obtain hj1 := jOf_le n
  obtain ho : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  unfold longArgs₂ macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
    wp_mv fun t₆ v₆ => WP.block_nil ?_
  obtain K : MacKeep s t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
  obtain E₆ := E.of_pk K.pk
  refine ⟨K, by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other],
    by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other], ?_⟩
  exact uargs L E₆ ho (L.srcW E₆.perm (t := tailO) (k := 16 * jOf n) (by simp only [tailO]; omega_arith))
    (out_tail L hout (by decide) (by simp only [tailO]; omega_arith)) (by omega_arith)
    (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.gpr, E.s2])
    (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.gpr, v₁.other, E.s3])
    (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.gpr, v₂.other, v₁.other, E.s1])
    (by simp (disch := decide) only [v₆.other, v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, E.s1])
    (by simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, h25])
    (by simp (disch := decide) only [v₆.other, v₅.other, v₄.gpr, v₃.other, v₂.other, v₁.other, E.s1]; rfl)

/-- `longArgs₃ out`: the arguments of the finalization of the rest of the
tail. -/
theorem longArgs₃_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {n : Nat} (hn : n < 2 ^ 64) (h16 : 16 ≤ n)
    (h20 : s.gpr .s7 = BitVec.ofNat 64 n) (h21 : s.gpr .s8 = BitVec.ofNat 64 (16 * kOf n))
    (h25 : s.gpr .s0 = BitVec.ofNat 64 (jOf n)) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (.block (longArgs₃ out)) s fun s₆ => MacKeep s s₆ ∧
      FArgs s₆ c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 (tailO + 16 * jOf n))
        (c.W + BitVec.ofNat 64 384) (n - 16 * kOf n - 16 * jOf n) c.R := by
  obtain hT := kOf_tail h16
  obtain hJ := jOf_rest h16
  obtain hj1 := jOf_le n
  obtain hk : 16 * kOf n ≤ n := by omega_arith
  obtain ho : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  unfold longArgs₃ macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
    wp_sll (by decide) fun t₆ v₆ => wp_add fun t₇ v₇ => wp_sub fun t₈ v₈ => wp_sub fun t₉ v₉ =>
    WP.block_nil ?_
  obtain K : MacKeep s t₉ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans ((MacKeep.ofUpd v₆).trans ((MacKeep.ofUpd v₇).trans
      ((MacKeep.ofUpd v₈).trans (MacKeep.ofUpd v₉))))))))
  obtain E₉ := E.of_pk K.pk
  obtain sh : t₆.gpr .t0 = BitVec.ofNat 64 (16 * jOf n) := by
    simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, h25]
    exact ofNat_shl4 (by omega_arith)
  refine ⟨K, ?_⟩
  exact fargs L E₉ ho hJ.2.2 (L.srcW E₉.perm (t := tailO + 16 * jOf n) (k := n - 16 * kOf n - 16 * jOf n)
      (by simp only [tailO]; omega_arith))
    (out_tail L hout (by simp only [tailO]; omega_arith) (by simp only [tailO]; omega_arith))
    (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other,
      v₂.other, v₁.gpr, E.s2])
    (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other,
      v₂.gpr, v₁.other, E.s3])
    (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.gpr,
      v₂.other, v₁.other, E.s1])
    (by
      simp (disch := decide) only [v₉.other, v₈.other, v₇.gpr, v₆.other, sh]
      simp (disch := decide) only [v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, E.s1]
      exact Offset.add_add _ _ _)
    (by
      simp (disch := decide) only [v₉.gpr, v₈.gpr, v₈.other, v₇.other, sh]
      simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, h20, h21]
      rw [ofNat_sub' hk hn, ofNat_sub' (by omega_arith) (by omega_arith)])
    (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.gpr, v₃.other,
      v₂.other, v₁.other, E.s1]; rfl)

/-- `(L − 1) / 16` tested: `L / 16` in `r9`. -/
theorem finLsr_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa (.block [.shift .srl .d .t0 .s7 4]) s fun s₁ => MacKeep s s₁ ∧ s₁.gpr .t0 = BitVec.ofNat 64 (n / 16) :=
  wp_srl (by decide) fun _ u₁ => WP.block_nil ⟨MacKeep.ofUpd u₁, by rw [u₁.gpr, h20, ofNat_lsr4' hn]⟩

/-- What a call of `vg_cmac_aes_update` keeps. -/
theorem upd_keep {s : State} {K C D S : Addr} {R n : Nat} (U : UArgs s K C D S R n) :
    Runs Impl.CmacAes.Stream.RISCV64.updCall s fun t => MacKeep s t ∧ t.gpr .s8 = s.gpr .s8 ∧
      t.gpr .s0 = s.gpr .s0 :=
  Runs.of_wp (WP.mono (upd_call U) fun _ h =>
    ⟨MacKeep.ofSaved h.rd h.wr h.sp h.saved, h.saved _ (by decide), h.saved _ (by decide)⟩)

/-! ## S2V's first state -/

/-! ## The CMAC of a string -/

/-- `cmacOf stO`, for the same string (`n` bytes at `P`) in both runs. -/
theorem cmacOf_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
    {P : Addr} {n : Nat} (hP₁ : Buf c σ₁ P n) (hP₂ : Buf c σ₂ P n) (h19₁ : σ₁.gpr .s6 = P)
    (h19₂ : σ₂.gpr .s6 = P) (h20₁ : σ₁.gpr .s7 = BitVec.ofNat 64 n) (h20₂ : σ₂.gpr .s7 = BitVec.ofNat 64 n) :
    RelCT isa (Eq2 σ₁ σ₂) (cmacOf stO) TT := by
  have hn := hP₁.lt
  obtain hcl := chainedLen_le n
  obtain head : ∀ {σ : State}, Env c σ → Buf c σ P n → σ.gpr .s6 = P → σ.gpr .s7 = BitVec.ofNat 64 n →
      Runs (.seq (cmacLen stO) (.block (cmacArgs₁ stO))) σ fun t => MacKeep σ t ∧
        t.gpr .s8 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n) ∧
        UArgs t c.C (c.W + BitVec.ofNat 64 stO) P (c.W + BitVec.ofNat 64 384) c.R
          (Spec.Cmac.chainedLen 16 n / 16) := fun E hP h19 h20 =>
    Runs.of_wp (WP.seq (WP.mono (cmacLen_wp L E (st := stO) (by decide) (by decide) hn h20) fun s₁ ⟨K₁, h21₁, _⟩ =>
      WP.mono (cmacArgs₁_wp L (E.of_pk K₁.pk) (st := stO) (by decide) (hP.of_eq K₁.pk.rd K₁.pk.wr)
        (by rw [K₁.s6, h19]) h21₁) fun _ ⟨K₂, r21₂, U⟩ => ⟨K₁.trans K₂, by rw [r21₂, h21₁], U⟩))
  obtain tail : ∀ {σ ρ : State}, Env c σ → Buf c σ P n → σ.gpr .s6 = P → σ.gpr .s7 = BitVec.ofNat 64 n →
      MacKeep σ ρ → ρ.gpr .s8 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n) →
      Runs (.block (cmacArgs₂ stO)) ρ fun t => MacKeep ρ t ∧
        FArgs t c.C (c.W + BitVec.ofNat 64 stO) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n))
          (c.W + BitVec.ofNat 64 384) (n - Spec.Cmac.chainedLen 16 n) c.R := fun E hP h19 h20 G h21 =>
    Runs.of_wp (cmacArgs₂_wp L (E.of_pk G.pk) (by decide) hn ((hP.drop hcl).of_eq G.pk.rd G.pk.wr)
      (by rw [G.s6, h19]) (by rw [G.s7, h20]) h21)
  unfold cmacOf
  refine RelCT.assoc (rel_seqR (rel_env [.s6, .s7] E₁ E₂ hsp
      (agree_cons (h19₁.trans h19₂.symm) (agree_cons (h20₁.trans h20₂.symm) agree_nil)) ⟨_, by taint_decide⟩)
    (head E₁ hP₁ h19₁ h20₁) (head E₂ hP₂ h19₂ h20₂) fun τ₁ τ₂ ⟨K₁, r21₁, U₁⟩ ⟨K₂, r21₂, U₂⟩ => ?_)
  obtain hspτ : τ₁.sp = τ₂.sp := by rw [K₁.pk.sp, K₂.pk.sp, hsp]
  refine rel_seqR (rel_upd U₁ U₂ hspτ) (upd_keep U₁) (upd_keep U₂) fun ρ₁ ρ₂ ⟨G₁, q21₁, _⟩ ⟨G₂, q21₂, _⟩ => ?_
  obtain M₁ := K₁.trans G₁
  obtain M₂ := K₂.trans G₂
  obtain hspρ : ρ₁.sp = ρ₂.sp := by rw [M₁.pk.sp, M₂.pk.sp, hsp]
  refine rel_seqR (rel_env [.s6, .s7, .s8] (E₁.of_pk M₁.pk) (E₂.of_pk M₂.pk) hspρ
      (agree_cons (by rw [M₁.s6, M₂.s6, h19₁, h19₂]) (agree_cons (by rw [M₁.s7, M₂.s7, h20₁, h20₂])
        (agree_cons (by rw [q21₁, q21₂, r21₁, r21₂]) agree_nil))) ⟨_, by taint_decide⟩)
    (tail E₁ hP₁ h19₁ h20₁ M₁ (by rw [q21₁, r21₁])) (tail E₂ hP₂ h19₂ h20₂ M₂ (by rw [q21₂, r21₂]))
    fun ω₁ ω₂ ⟨N₁, F₁⟩ ⟨N₂, F₂⟩ => ?_
  exact rel_fin F₁ F₂ (by rw [N₁.pk.sp, N₂.pk.sp, hspρ])

/-! ## The associated data -/

/-- The descriptors, public: the same in both runs. -/
abbrev DescAgree (c : Cx) (m₁ m₂ : Mem) : Prop :=
  ∀ i < c.N, descW m₁ c.A i 0 = descW m₂ c.A i 0 ∧ descW m₁ c.A i 1 = descW m₂ c.A i 1

/-- One component, from two runs after the same number `i` of them. -/
theorem aStep_rel {c : Cx} (L : Lay c) {σ₁ σ₂ s₁ s₂ : State} {i : Nat} (hi : i < c.N) (I₁ : AInv c σ₁ i s₁)
    (I₂ : AInv c σ₂ i s₂) (hsp : s₁.sp = s₂.sp) (hd : DescAgree c σ₁.mem σ₂.mem) :
    RelCT isa (Eq2 s₁ s₂) (.seq (.block adNext) (.seq (cmacOf stO) (.block adStep))) TT := by
  obtain ⟨d0, d1⟩ := hd i hi
  refine rel_seqR (rel_env [.s4] I₁.env I₂.env hsp (agree_cons (I₁.s4.trans I₂.s4.symm) agree_nil)
      ⟨_, by taint_decide⟩)
    (Runs.of_wp (adNext_wp L I₁ hi)) (Runs.of_wp (adNext_wp L I₂ hi)) fun τ₁ τ₂ ⟨a19₁, a20₁, k₁⟩ ⟨a19₂, a20₂, k₂⟩ => ?_
  obtain E₁ := I₁.env.of_pk k₁.pk
  obtain E₂ := I₂.env.of_pk k₂.pk
  obtain hP₁ : Buf c τ₁ (descW σ₁.mem c.A i 0) (descW σ₁.mem c.A i 1).toNat := (I₁.ads i hi).of_eq k₁.pk.rd k₁.pk.wr
  obtain hP₂ : Buf c τ₂ (descW σ₁.mem c.A i 0) (descW σ₁.mem c.A i 1).toNat := by
    rw [d0, d1]; exact (I₂.ads i hi).of_eq k₂.pk.rd k₂.pk.wr
  obtain b19₂ : τ₂.gpr .s6 = descW σ₁.mem c.A i 0 := by rw [a19₂, d0]
  obtain b20₁ : τ₁.gpr .s7 = BitVec.ofNat 64 (descW σ₁.mem c.A i 1).toNat := by rw [a20₁]; simp
  obtain b20₂ : τ₂.gpr .s7 = BitVec.ofNat 64 (descW σ₁.mem c.A i 1).toNat := by rw [a20₂, d1]; simp
  obtain hsp₁ : τ₁.sp = τ₂.sp := by rw [k₁.pk.sp, k₂.pk.sp, hsp]
  refine rel_seqR (cmacOf_rel L E₁ E₂ hsp₁ hP₁ hP₂ a19₁ b19₂ b20₁ b20₂)
    (Runs.of_wp (cmacOf_wp L E₁ (st := stO) (by decide) (by decide) hP₁ a19₁ b20₁))
    (Runs.of_wp (cmacOf_wp L E₂ (st := stO) (by decide) (by decide) hP₂ b19₂ b20₂))
    fun ρ₁ ρ₂ ⟨K₁, _, _⟩ ⟨K₂, _, _⟩ => ?_
  exact rel_env [.s4, .s5] (E₁.of_pk K₁.pk) (E₂.of_pk K₂.pk) (by rw [K₁.pk.sp, K₂.pk.sp, hsp₁])
    (agree_cons (by rw [K₁.s4, K₂.s4, k₁.s4, k₂.s4, I₁.s4, I₂.s4])
      (agree_cons (by rw [K₁.s5, K₂.s5, k₁.s5, k₂.s5, I₁.s5, I₂.s5]) agree_nil)) ⟨_, by taint_decide⟩

/-- S2V over all the components, from two runs at S2V's first state whose
descriptors agree. -/
theorem s2vAds_rel {c : Cx} (L : Lay c) {σ₁ σ₂ s₁ s₂ : State} (I₁ : AInv c σ₁ 0 s₁) (I₂ : AInv c σ₂ 0 s₂)
    (hsp : s₁.sp = s₂.sp) (hd : DescAgree c σ₁.mem σ₂.mem) : RelCT isa (Eq2 s₁ s₂) s2vAds TT := by
  have aw := L.aw
  obtain hN : c.N < 2 ^ 64 := by omega_arith
  obtain hσ : σ₁.sp = σ₂.sp := I₁.pk.sp.symm.trans (hsp.trans I₂.pk.sp)
  obtain h18₁ : s₁.gpr .s5 = BitVec.ofNat 64 c.N := by rw [I₁.s5, Nat.sub_zero]
  obtain h18₂ : s₂.gpr .s5 = BitVec.ofNat 64 c.N := by rw [I₂.s5, Nat.sub_zero]
  unfold s2vAds
  refine rel_ite (evalZ h18₁ hN) (evalZ h18₂ hN) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] I₁.env I₂.env hsp agree_nil ⟨_, by taint_decide⟩
  obtain h0 : c.N ≠ 0 := by simpa using hf
  refine (RelCT.loop (Q := TT) (fun k (a b : State) => ∃ j, k = c.N - j ∧ j < c.N ∧
      AInv c σ₁ j a ∧ AInv c σ₂ j b) (fun k => ?_) (c.N - 0)).mono
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨0, rfl, by omega_arith, I₁, I₂⟩) fun _ _ h => h
  refine rel_of_eq2 fun a b ⟨j, hk, hj, J₁, J₂⟩ => ?_
  refine (rel_post (aStep_rel L hj J₁ J₂ (by rw [J₁.pk.sp, J₂.pk.sp, hσ]) hd) (Runs.of_wp (aStep_wp L J₁ hj))
    (Runs.of_wp (aStep_wp L J₂ hj))).mono (fun _ _ h => h) fun a' b' ⟨J₁', J₂'⟩ => ?_
  obtain ev₁ := evalNZ J₁'.s5 (by omega_arith)
  obtain ev₂ := evalNZ J₂'.s5 (by omega_arith)
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.N - (j + 1), ?_, j + 1, rfl, ?_, J₁', J₂'⟩⟩
  · rw [ev₁] at ht; simp at ht; omega_arith
  · rw [ev₁] at ht; simp at ht; omega_arith

/-! ## Finishing S2V -/

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
  {P : Addr} {n : Nat} (hP₁ : Buf c σ₁ P n) (hP₂ : Buf c σ₂ P n) (h19₁ : σ₁.gpr .s6 = P)
  (h19₂ : σ₂.gpr .s6 = P) (h20₁ : σ₁.gpr .s7 = BitVec.ofNat 64 n) (h20₂ : σ₂.gpr .s7 = BitVec.ofNat 64 n)
  {out : Nat} (hout : out = 0 ∨ out = tO)
include L E₁ E₂ hsp hP₁ hP₂ h19₁ h19₂ h20₁ h20₂ hout

/-- The short case, `L < 16`. -/
theorem short_rel (hn : n < 16) : RelCT isa (Eq2 σ₁ σ₂) (.seq shortTail (shortMac out)) TT := by
  obtain t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s6, .s7]))
      (.seq shortTail (.block (shortArgs out))) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain head : ∀ {σ : State}, Env c σ → Buf c σ P n → σ.gpr .s6 = P → σ.gpr .s7 = BitVec.ofNat 64 n →
      Runs (.seq shortTail (.block (shortArgs out))) σ fun t => PK σ t ∧
        FArgs t c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 384) 16 c.R :=
    fun E hP h19 h20 => Runs.of_wp (WP.seq (WP.mono (shortTail_wp L E hP hn h19 h20) fun _ ⟨pk₁, _, _⟩ =>
      WP.mono (shortArgs_wp L (E.of_pk pk₁) hout) fun _ ⟨pk, F⟩ => ⟨pk₁.trans pk, F⟩))
  unfold shortMac
  exact RelCT.assoc (rel_seqR (rel_env [.s6, .s7] E₁ E₂ hsp
      (agree_cons (h19₁.trans h19₂.symm) (agree_cons (h20₁.trans h20₂.symm) agree_nil)) t)
    (head E₁ hP₁ h19₁ h20₁) (head E₂ hP₂ h19₂ h20₂) fun _ _ ⟨pk₁, F₁⟩ ⟨pk₂, F₂⟩ =>
      rel_fin F₁ F₂ (by rw [pk₁.sp, pk₂.sp, hsp]))

/-- The long case, `L ≥ 16`. -/
theorem long_rel (h16 : 16 ≤ n) : RelCT isa (Eq2 σ₁ σ₂) (.seq longTail (longMac out)) TT := by
  have hn := hP₁.lt
  obtain hT := kOf_tail h16
  obtain hk : 16 * kOf n ≤ n := by omega_arith
  obtain t₁ : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s6, .s7]))
      (.seq longTail (.block (longArgs₁ out))) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain t₂ : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s7]))
      (.seq jBlock (.block (longArgs₂ out))) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain t₃ : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s7, .s8, .s0]))
      (.block (longArgs₃ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  -- The tail, and the arguments of the update over the `k` blocks.
  obtain head : ∀ {σ : State}, Env c σ → Buf c σ P n → σ.gpr .s6 = P → σ.gpr .s7 = BitVec.ofNat 64 n →
      Runs (.seq longTail (.block (longArgs₁ out))) σ fun t => MacKeep σ t ∧
        t.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) ∧
        UArgs t c.C (c.W + BitVec.ofNat 64 out) P (c.W + BitVec.ofNat 64 384) c.R (kOf n) := by
    intro σ E hP h19 h20
    unfold longTail
    refine Runs.of_wp (WP.seq (WP.seq (WP.mono (kBlock_wp hn h16 h20) fun s₁ ⟨K₁, _, r21₁⟩ => ?_)))
    refine WP.mono (tailCopy_wp L (E.of_pk K₁.pk) (hP.of_eq K₁.pk.rd K₁.pk.wr) hk hT.1 hT.2
      (by rw [K₁.s6, h19]) (by rw [K₁.s7, h20]) r21₁) fun s₂ ⟨K₂, r21₂, _, _⟩ => ?_
    obtain K₁₂ := K₁.trans K₂
    exact WP.mono (longArgs₁_wp L (E.of_pk K₁₂.pk) (hP.of_eq K₁₂.pk.rd K₁₂.pk.wr) hk (by rw [K₁₂.s6, h19])
      (by rw [r21₂, r21₁]) hout) fun _ ⟨K₃, r21₃, U⟩ => ⟨K₁₂.trans K₃, by rw [r21₃, r21₂, r21₁], U⟩
  -- `j`, and the arguments of the update over the first `j` blocks of the tail.
  obtain head₂ : ∀ {ρ : State}, Env c ρ → ρ.gpr .s7 = BitVec.ofNat 64 n →
      ρ.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) →
      Runs (.seq jBlock (.block (longArgs₂ out))) ρ fun t => MacKeep ρ t ∧
        t.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) ∧ t.gpr .s0 = BitVec.ofNat 64 (jOf n) ∧
        UArgs t c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 384) c.R
          (jOf n) := fun E h20 h21 =>
    Runs.of_wp (WP.seq (WP.mono (jBlock_wp hn h16 h20) fun _ ⟨K₃, _, r21₃, r25₃⟩ =>
      WP.mono (longArgs₂_wp L (E.of_pk K₃.pk) r25₃ hout) fun _ ⟨K₄, r21₄, r25₄, U⟩ =>
        ⟨K₃.trans K₄, by rw [r21₄, r21₃, h21], by rw [r25₄, r25₃], U⟩))
  unfold longMac
  refine RelCT.assoc (rel_seqR (rel_env [.s6, .s7] E₁ E₂ hsp
      (agree_cons (h19₁.trans h19₂.symm) (agree_cons (h20₁.trans h20₂.symm) agree_nil)) t₁)
    (head E₁ hP₁ h19₁ h20₁) (head E₂ hP₂ h19₂ h20₂) fun τ₁ τ₂ ⟨K₁, r21₁, U₁⟩ ⟨K₂, r21₂, U₂⟩ => ?_)
  obtain hspτ : τ₁.sp = τ₂.sp := by rw [K₁.pk.sp, K₂.pk.sp, hsp]
  refine rel_seqR (rel_upd U₁ U₂ hspτ) (upd_keep U₁) (upd_keep U₂) fun ρ₁ ρ₂ ⟨G₁, q21₁, _⟩ ⟨G₂, q21₂, _⟩ => ?_
  obtain M₁ := K₁.trans G₁
  obtain M₂ := K₂.trans G₂
  obtain hspρ : ρ₁.sp = ρ₂.sp := by rw [M₁.pk.sp, M₂.pk.sp, hsp]
  obtain q20₁ : ρ₁.gpr .s7 = BitVec.ofNat 64 n := by rw [M₁.s7, h20₁]
  obtain q20₂ : ρ₂.gpr .s7 = BitVec.ofNat 64 n := by rw [M₂.s7, h20₂]
  obtain p21₁ : ρ₁.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) := by rw [q21₁, r21₁]
  obtain p21₂ : ρ₂.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) := by rw [q21₂, r21₂]
  refine RelCT.assoc (rel_seqR (rel_env [.s7] (E₁.of_pk M₁.pk) (E₂.of_pk M₂.pk) hspρ
      (agree_cons (q20₁.trans q20₂.symm) agree_nil) t₂)
    (head₂ (E₁.of_pk M₁.pk) q20₁ p21₁) (head₂ (E₂.of_pk M₂.pk) q20₂ p21₂)
    fun ω₁ ω₂ ⟨N₁, w21₁, w25₁, V₁⟩ ⟨N₂, w21₂, w25₂, V₂⟩ => ?_)
  obtain hspω : ω₁.sp = ω₂.sp := by rw [N₁.pk.sp, N₂.pk.sp, hspρ]
  refine rel_seqR (rel_upd V₁ V₂ hspω) (upd_keep V₁) (upd_keep V₂) fun υ₁ υ₂ ⟨G₁', x21₁, x25₁⟩ ⟨G₂', x21₂, x25₂⟩ => ?_
  obtain Q₁ := (M₁.trans N₁).trans G₁'
  obtain Q₂ := (M₂.trans N₂).trans G₂'
  obtain hspυ : υ₁.sp = υ₂.sp := by rw [Q₁.pk.sp, Q₂.pk.sp, hsp]
  obtain y20₁ : υ₁.gpr .s7 = BitVec.ofNat 64 n := by rw [Q₁.s7, h20₁]
  obtain y20₂ : υ₂.gpr .s7 = BitVec.ofNat 64 n := by rw [Q₂.s7, h20₂]
  obtain y21₁ : υ₁.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) := by rw [x21₁, w21₁]
  obtain y21₂ : υ₂.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) := by rw [x21₂, w21₂]
  obtain y25₁ : υ₁.gpr .s0 = BitVec.ofNat 64 (jOf n) := by rw [x25₁, w25₁]
  obtain y25₂ : υ₂.gpr .s0 = BitVec.ofNat 64 (jOf n) := by rw [x25₂, w25₂]
  obtain H₁ := E₁.of_pk Q₁.pk
  obtain H₂ := E₂.of_pk Q₂.pk
  refine rel_seqR (rel_env [.s7, .s8, .s0] H₁ H₂ hspυ
      (agree_cons (y20₁.trans y20₂.symm) (agree_cons (y21₁.trans y21₂.symm)
        (agree_cons (y25₁.trans y25₂.symm) agree_nil))) t₃)
    (Runs.of_wp (longArgs₃_wp L H₁ hn h16 y20₁ y21₁ y25₁ hout))
    (Runs.of_wp (longArgs₃_wp L H₂ hn h16 y20₂ y21₂ y25₂ hout)) fun φ₁ φ₂ ⟨R₁, A₁⟩ ⟨R₂, A₂⟩ => ?_
  exact rel_fin A₁ A₂ (by rw [R₁.pk.sp, R₂.pk.sp, hspυ])

/-- `finish out`: S2V finished with the same string (`n` bytes at `P`) in both
runs. -/
theorem finish_rel : RelCT isa (Eq2 σ₁ σ₂) (finish out) TT := by
  have hn := hP₁.lt
  unfold finish
  refine rel_seqR (rel_env [.s7] E₁ E₂ hsp (agree_cons (h20₁.trans h20₂.symm) agree_nil) ⟨_, by taint_decide⟩)
    (Runs.of_wp (finLsr_wp hn h20₁)) (Runs.of_wp (finLsr_wp hn h20₂)) fun τ₁ τ₂ ⟨K₁, r9₁⟩ ⟨K₂, r9₂⟩ => ?_
  obtain hspτ : τ₁.sp = τ₂.sp := by rw [K₁.pk.sp, K₂.pk.sp, hsp]
  obtain F₁ := E₁.of_pk K₁.pk
  obtain F₂ := E₂.of_pk K₂.pk
  obtain q19₁ : τ₁.gpr .s6 = P := by rw [K₁.s6, h19₁]
  obtain q19₂ : τ₂.gpr .s6 = P := by rw [K₂.s6, h19₂]
  obtain q20₁ : τ₁.gpr .s7 = BitVec.ofNat 64 n := by rw [K₁.s7, h20₁]
  obtain q20₂ : τ₂.gpr .s7 = BitVec.ofNat 64 n := by rw [K₂.s7, h20₂]
  obtain B₁ := hP₁.of_eq K₁.pk.rd K₁.pk.wr
  obtain B₂ := hP₂.of_eq K₂.pk.rd K₂.pk.wr
  refine rel_ite (evalZ r9₁ (by omega_arith)) (evalZ r9₂ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n / 16 = 0 := by simpa using ht
    exact short_rel L F₁ F₂ hspτ B₁ B₂ q19₁ q19₂ q20₁ q20₂ hout (by omega_arith)
  · have h0 : n / 16 ≠ 0 := by simpa using hf
    exact long_rel L F₁ F₂ hspτ B₁ B₂ q19₁ q19₂ q20₁ q20₂ hout (by omega_arith)

end

end VG.Proof.AesSiv.RISCV64

end

end

/-!
# AES-SIV on RISC-V: constant time of `encrypt` and `decrypt`

Untrusted: everything here is checked by Lean. Two runs from the same public
arguments (`Args c`) with the same descriptors (`DescAgree`) leak the same:
the entry and the code between the pieces by the taint analysis, the pieces
by `MacCT.lean` and `CtrCT.lean`, each from what the correctness proofs
establish of both runs (`rel_seqR`, `Runs.of_wp`). `decrypt` compares the
IVs and masks the data without a branch, so its result is not leaked. As on
PPC64LE (`Proof/AesSiv/PPC64LE/TopCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesSiv.RISCV64
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint)
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp rel_seqR)
open VG.Proof.CmacAes.Stream.RISCV64 (FArgs)
open VG.Spec.Aes (bytesAt)

/-- The entry, S2V's first state and its call. -/
theorem entryStart_wp {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) :
    WP isa (.seq (.block (entry ++ startPre)) Impl.CmacAes.Stream.RISCV64.finCall) s fun s₂ =>
      ∃ s₁, Entered c s s₁ ∧ AInv c s₁ 0 s₂ := by
  have L := Ar.lay
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (entry_wp Ar) fun s₁ En => ?_))
  have E₁ := En.env
  refine WP.mono (WP.seq_iff.mp (start_wp L E₁)) fun s₂' h => WP.mono h fun s₂ ⟨K₂, f₂, d₂⟩ => ⟨s₁, En, ?_⟩
  have wf₁ : WF c s.mem s₁.mem := WF.of En.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  exact { env := E₁.of_pk K₂.pk
          pk := K₂.pk
          ads := (wf₁.ads L hA).of_eq (by rw [K₂.pk.rd, En.rd]) (by rw [K₂.pk.wr, En.wr])
          s4 := by rw [K₂.s4, En.s4, Nat.mul_zero, BitVec.add_zero]
          s5 := by rw [K₂.s5, En.s5, Nat.sub_zero]
          frame := f₂
          acc := by rw [d₂, List.take_zero, Spec.Siv.s2vAcc, List.foldl_nil] }

/-- The entry and S2V's first state in two runs. -/
theorem entryStart_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂)
    (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block (entry ++ startPre)) Impl.CmacAes.Stream.RISCV64.finCall) TT := by
  have W {σ : State} (A : Args c σ) : WP isa (.block (entry ++ startPre)) σ fun s =>
      ∃ s₁, Entered c σ s₁ ∧ s.sp = σ.sp ∧
        FArgs s c.C (c.W + BitVec.ofNat 64 dO) (c.W + BitVec.ofNat 64 zO) (c.W + BitVec.ofNat 64 384) 16 c.R :=
    WP.block_append_iff.mpr (WP.mono (entry_wp A) fun s₁ En => WP.mono (startPre_wp L En.env)
      fun s ⟨K, _, F⟩ => ⟨s₁, En, by rw [K.pk.sp, En.sp], F⟩)
  have hb : RelCT isa (Eq2 σ₁ σ₂) (.block (entry ++ startPre)) TT := by
    refine RelCT.block_append (rel_seqR (rel_taint [.a7] hsp (agree_cons (by rw [A₁.a7, A₂.a7]) agree_nil)
      (by taint_decide)) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂)) fun τ₁ τ₂ En En' => ?_)
    exact rel_env [] En.env En'.env (by rw [En.sp, En'.sp, hsp]) agree_nil ⟨_, by taint_decide⟩
  exact rel_seqR hb (Runs.of_wp (W A₁)) (Runs.of_wp (W A₂)) fun τ₁ τ₂ ⟨_, _, h₁, F₁⟩ ⟨_, _, h₂, F₂⟩ =>
    rel_fin F₁ F₂ (by rw [h₁, h₂, hsp])

/-- `encS2v` in two runs. -/
theorem encS2v_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂)
    (hA₁ : Ads c σ₁.mem σ₁) (hA₂ : Ads c σ₂.mem σ₂) (hd : DescAgree c σ₁.mem σ₂.mem) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) encS2v TT := by
  unfold encS2v
  refine RelCT.assoc (rel_seqR (entryStart_rel L A₁ A₂ hsp) (Runs.of_wp (entryStart_wp A₁ hA₁))
    (Runs.of_wp (entryStart_wp A₂ hA₂)) fun τ₁ τ₂ ⟨s₁, En, I⟩ ⟨s₁', En', I'⟩ => ?_)
  have wf : WF c σ₁.mem s₁.mem := WF.of En.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  have wf' : WF c σ₂.mem s₁'.mem := WF.of En'.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  have hd₁ : DescAgree c s₁.mem s₁'.mem := fun i hi => by
    rw [wf.descW L hi (by decide), wf.descW L hi (by decide), wf'.descW L hi (by decide),
      wf'.descW L hi (by decide)]
    exact hd i hi
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [I.pk.sp, I'.pk.sp, En.sp, En'.sp, hsp]
  refine rel_seqR (s2vAds_rel L I I' hsp₁ hd₁) (Runs.of_wp (s2vAds_wp L I)) (Runs.of_wp (s2vAds_wp L I'))
    fun τ₃ τ₄ I₃ I₄ => ?_
  exact rel_env [] I₃.env I₄.env (by rw [I₃.pk.sp, I₄.pk.sp, En.sp, En'.sp, hsp]) agree_nil ⟨_, by taint_decide⟩

/-- What `encS2v` leaves. -/
theorem encS2v_runs {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) :
    Runs encS2v s fun s' => ∃ s₁, S2vDone c s s₁ s' ∧ s'.gpr .s6 = c.D ∧ s'.gpr .s7 = BitVec.ofNat 64 c.n := by
  have h := encS2v_wp (rest := .block []) (Q := fun s' => ∃ s₁, S2vDone c s s₁ s' ∧ s'.gpr .s6 = c.D ∧
    s'.gpr .s7 = BitVec.ofNat 64 c.n) Ar hA fun s₁ s' S h19 h20 => WP.block_nil ⟨s₁, S, h19, h20⟩
  exact Runs.of_wp (WP.mono (WP.seq_iff.mp h) fun _ h => WP.block_nil_iff.mp h)

/-- `vg_aes_siv_encrypt` in two runs. -/
theorem encrypt_rel {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂)
    (hA₁ : Ads c σ₁.mem σ₁) (hA₂ : Ads c σ₂.mem σ₂) (hd : DescAgree c σ₁.mem σ₂.mem) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) encrypt TT := by
  have L := A₁.lay
  unfold encrypt
  refine rel_seqR (encS2v_rel L A₁ A₂ hA₁ hA₂ hd hsp) (encS2v_runs A₁ hA₁) (encS2v_runs A₂ hA₂)
    fun s₄ t₄ ⟨_, S, r19, r20⟩ ⟨_, S', r19', r20'⟩ => ?_
  have E₄ := S.inv.env
  have E₄' := S'.inv.env
  have h₄ : s₄.sp = t₄.sp := by rw [S.inv.pk.sp, S'.inv.pk.sp, S.en.sp, S'.en.sp, hsp]
  refine rel_seqR (finish_rel L E₄ E₄' h₄ (L.bufD E₄.perm) (L.bufD E₄'.perm) r19 r19' r20 r20' (.inl rfl))
    (Runs.of_wp (finish_wp L E₄ (L.bufD E₄.perm) r19 r20 (out := 0) (.inl rfl)))
    (Runs.of_wp (finish_wp L E₄' (L.bufD E₄'.perm) r19' r20' (out := 0) (.inl rfl))) fun s₅ t₅ F F' => ?_
  have E₅ := E₄.of_pk F.1
  have E₅' := E₄'.of_pk F'.1
  have h₅ : s₅.sp = t₅.sp := by rw [F.1.sp, F'.1.sp, h₄]
  refine rel_seqR (ctr_rel L E₅ E₅' h₅ (src := 0) (by decide) (by decide))
    (Runs.of_wp (ctr_wp L E₅ (src := 0) (by decide) (by decide)))
    (Runs.of_wp (ctr_wp L E₅' (src := 0) (by decide) (by decide))) fun s₆ t₆ C C' => ?_
  exact rel_env [] (E₅.of_pk C.1) (E₅'.of_pk C'.1) (by rw [C.1.sp, C'.1.sp, h₅]) agree_nil ⟨_, by taint_decide⟩

/-- `vg_aes_siv_decrypt` in two runs. -/
theorem decrypt_rel {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂)
    (hA₁ : Ads c σ₁.mem σ₁) (hA₂ : Ads c σ₂.mem σ₂) (hd : DescAgree c σ₁.mem σ₂.mem) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) decrypt TT := by
  have L := A₁.lay
  unfold decrypt
  refine rel_seqR (encS2v_rel L A₁ A₂ hA₁ hA₂ hd hsp) (encS2v_runs A₁ hA₁) (encS2v_runs A₂ hA₂)
    fun s₄ t₄ ⟨_, S, _, _⟩ ⟨_, S', _, _⟩ => ?_
  have E₄ := S.inv.env
  have E₄' := S'.inv.env
  have h₄ : s₄.sp = t₄.sp := by rw [S.inv.pk.sp, S'.inv.pk.sp, S.en.sp, S'.en.sp, hsp]
  refine rel_seqR (rel_env [] E₄ E₄' h₄ agree_nil ⟨_, by taint_decide⟩) (Runs.of_wp (sivIn_wp L E₄))
    (Runs.of_wp (sivIn_wp L E₄')) fun s₅ t₅ ⟨pk₅, _⟩ ⟨pk₅', _⟩ => ?_
  have E₅ := E₄.of_pk pk₅
  have E₅' := E₄'.of_pk pk₅'
  have h₅ : s₅.sp = t₅.sp := by rw [pk₅.sp, pk₅'.sp, h₄]
  refine rel_seqR (ctr_rel L E₅ E₅' h₅ (src := 0) (by decide) (by decide))
    (Runs.of_wp (ctr_wp L E₅ (src := 0) (by decide) (by decide)))
    (Runs.of_wp (ctr_wp L E₅' (src := 0) (by decide) (by decide))) fun s₆ t₆ C C' => ?_
  have E₆ := E₅.of_pk C.1
  have E₆' := E₅'.of_pk C'.1
  have h₆ : s₆.sp = t₆.sp := by rw [C.1.sp, C'.1.sp, h₅]
  have D (σ : State) (E : Env c σ) : WP isa (.block dataStr) σ fun s => Env c s ∧ s.sp = σ.sp ∧
      s.gpr .s6 = c.D ∧ s.gpr .s7 = BitVec.ofNat 64 c.n :=
    wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => WP.block_nil
      ⟨E.of_pk ((PK.ofUpd u₁).trans (PK.ofUpd u₂)), by rw [u₂.sp, u₁.sp],
        by rw [u₂.other _ (by decide), u₁.gpr, E.s9], by rw [u₂.gpr, u₁.other _ (by decide), E.s10]⟩
  refine rel_seqR (rel_env [] E₆ E₆' h₆ agree_nil ⟨_, by taint_decide⟩) (Runs.of_wp (D _ E₆))
    (Runs.of_wp (D _ E₆')) fun s₇ t₇ ⟨E₇, sp₇, r19, r20⟩ ⟨E₇', sp₇', r19', r20'⟩ => ?_
  have h₇ : s₇.sp = t₇.sp := by rw [sp₇, sp₇', h₆]
  refine rel_seqR (finish_rel L E₇ E₇' h₇ (L.bufD E₇.perm) (L.bufD E₇'.perm) r19 r19' r20 r20' (.inr rfl))
    (Runs.of_wp (finish_wp L E₇ (L.bufD E₇.perm) r19 r20 (out := tO) (.inr rfl)))
    (Runs.of_wp (finish_wp L E₇' (L.bufD E₇'.perm) r19' r20' (out := tO) (.inr rfl))) fun s₈ t₈ F F' => ?_
  exact rel_env [] (E₇.of_pk F.1) (E₇'.of_pk F'.1) (by rw [F.1.sp, F'.1.sp, h₇]) agree_nil ⟨_, by taint_decide⟩

end VG.Proof.AesSiv.RISCV64

end

end

/-!
# AES-SIV on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness (`Enc.lean`,
`Dec.lean`) and constant time (`TopCT.lean`) of `encrypt` and `decrypt`,
states satisfying their preconditions, and the shared contracts of
`Spec/Siv/Contract.lean` with the working space as a last argument
(`Proof/AesSiv/Scratch.lean`), then in a frame on the stack
(`Verified.stackScratchLists`). `init`'s are in `Init.lean`. As on PPC64LE
(`Proof/AesSiv/PPC64LE/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)

theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)

theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem cov_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-- Component `i`'s region, as the descriptors list it. -/
theorem listed_mem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (⟨descW m A i 0, (descW m A i 1).toNat⟩ : Region) ∈ Sig.listed 64 m .u8 A N :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, listed_eq m A i⟩

/-- The public values of `encrypt` and `decrypt`, in their registers. -/
def cxOf (s : State) : Cx :=
  ⟨s.gpr .a0, s.gpr .a7, s.gpr .a2, s.gpr .a4, s.gpr .a6, (s.gpr .a1).toNat, (s.gpr .a3).toNat,
    (s.gpr .a5).toNat⟩

/-- The precondition of `encrypt`'s shared contract gives the proofs': the
arguments, the components, and `siv` writable. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract RISCV64.abi 0).pre s) :
    Args (cxOf s) s ∧ Ads (cxOf s) s.mem s ∧ Covers [⟨(cxOf s).V, 16⟩] s.wr := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, RISCV64.abi,
    RISCV64.argRegs, List.getD] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.append_nil, List.append_eq] at *
  rename_i hsp cd cv fc fd fv fw hR cal hrd hwr pw fl
  obtain ⟨cW, dV, dW, dA, -, vW, -, -, wA, wL, -⟩ := pw
  obtain ⟨fA, fL⟩ := fl
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have mC : (⟨s.gpr .a0, 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mA : (⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mD : (⟨s.gpr .a4, (s.gpr .a5).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mV : (⟨s.gpr .a6, 16⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mW : (⟨s.gpr .a7, 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have L : Lay (cxOf s) :=
    ⟨fc, fw, cal, h, by rw [Nat.mul_comm]; exact fA, fd, fv, cW, cd, by rw [Nat.mul_comm]; exact wA.symm,
      by rw [Nat.mul_comm]; exact dA.symm, dW, vW, dV.symm, hR, BitVec.isLt _⟩
  refine ⟨⟨L, rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, rfl,
    ⟨cov_mem (inRd mC), cov_mem mW, cov_mem (inRd mA), cov_mem mD, cov_mem (inWr mV)⟩⟩, fun i hi => ?_, cov_mem mV⟩
  have hm := listed_mem s.mem (s.gpr .a2) hi
  have mP : (⟨descW s.mem (s.gpr .a2) i 0, (descW s.mem (s.gpr .a2) i 1).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
  exact ⟨cov_mem (inRd mP), BitVec.isLt _, fL _ hm, (wL _ hm).symm⟩

/-- The precondition of `decrypt`'s shared contract gives the proofs': the
arguments and the components. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract RISCV64.abi 0).pre s) :
    Args (cxOf s) s ∧ Ads (cxOf s) s.mem s := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, RISCV64.abi,
    RISCV64.argRegs, List.getD] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.append_nil, List.append_eq] at *
  rename_i hsp cd fc fd fv fw hR cal hrd hwr pw fl
  obtain ⟨cW, dV, dW, dA, -, vW, wA, wL, -⟩ := pw
  obtain ⟨fA, fL⟩ := fl
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have mC : (⟨s.gpr .a0, 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mV : (⟨s.gpr .a6, 16⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mA : (⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mD : (⟨s.gpr .a4, (s.gpr .a5).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mW : (⟨s.gpr .a7, 2576⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have L : Lay (cxOf s) :=
    ⟨fc, fw, cal, h, by rw [Nat.mul_comm]; exact fA, fd, fv, cW, cd, by rw [Nat.mul_comm]; exact wA.symm,
      by rw [Nat.mul_comm]; exact dA.symm, dW, vW, dV.symm, hR, BitVec.isLt _⟩
  refine ⟨⟨L, rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, rfl,
    ⟨cov_mem (inRd mC), cov_mem mW, cov_mem (inRd mA), cov_mem mD, cov_mem (inRd mV)⟩⟩, fun i hi => ?_⟩
  have hm := listed_mem s.mem (s.gpr .a2) hi
  have mP : (⟨descW s.mem (s.gpr .a2) i 0, (descW s.mem (s.gpr .a2) i 1).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
  exact ⟨cov_mem (inRd mP), BitVec.isLt _, fL _ hm, (wL _ hm).symm⟩

/-! ## Correctness -/

theorem encrypt_correct (s : State) (hs : (Proof.AesSiv.encryptScratchContract RISCV64.abi 0).pre s) :
    ∃ t s', Exec isa Impl.AesSiv.RISCV64.encrypt s t s' ∧ abiPreserved s s' ∧
      (Proof.AesSiv.encryptScratchContract RISCV64.abi 0).post s s' := by
  obtain ⟨Ar, hA, hV⟩ := encPre_of hs
  obtain ⟨t, s', he, hab, hq⟩ := encrypt_wp Ar hA hV
  refine ⟨t, s', he, hab, ?_⟩
  sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Proof.AesSiv.encryptRoundsPost,
    RISCV64.abi, RISCV64.argRegs, List.getD]
  exact fun _ => hq

theorem decrypt_correct (s : State) (hs : (Proof.AesSiv.decryptScratchContract RISCV64.abi 0).pre s) :
    ∃ t s', Exec isa Impl.AesSiv.RISCV64.decrypt s t s' ∧ abiPreserved s s' ∧
      (Proof.AesSiv.decryptScratchContract RISCV64.abi 0).post s s' := by
  obtain ⟨Ar, hA⟩ := decPre_of hs
  obtain ⟨t, s', he, hab, hr, hd⟩ := decrypt_wp Ar hA
  refine ⟨t, s', he, hab, ?_⟩
  sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Proof.AesSiv.decryptRoundsPost,
    RISCV64.abi, RISCV64.argRegs, List.getD]
  intro _
  simp only [cxOf] at hr hd
  rw [Spec.Siv.decryptWith_eq, Spec.Siv.openWith]
  have hl : ∀ x : List Byte, x.length = (s.gpr .a5).toNat → x.map (fun _ => (0 : Byte)) =
      Spec.Siv.zeros (s.gpr .a5).toNat := fun x hx => by
    rw [List.map_const', hx]; rfl
  split
  · rename_i pt heq
    split at heq
    · rename_i hT
      obtain rfl := Option.some.inj heq
      simp only [eq_true hT.symm, ite_true, List.map_id'] at hr hd
      exact ⟨by rw [hr]; rfl, hd⟩
    · cases heq
  · rename_i heq
    split at heq
    · cases heq
    · rename_i hT
      simp only [eq_false (Ne.symm hT), ite_false] at hr hd
      refine ⟨by rw [hr]; rfl, ?_⟩
      rw [hd]
      exact hl _ (by rw [Proof.Siv.length_ctr (Spec.Siv.ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (fun y => Proof.Cmac.aesWith_length _ _ y),
        Proof.Cmac.bytesAt_length])

/-! ## Satisfiable preconditions -/

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, with no associated data and no data: the context at
`0x1000`, `siv` at `0x5000` and the working space at `0x4000`. -/
def encSat (rd wr : List Region) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x5000 | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := rd
  wr := wr

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract RISCV64.abi 0).pre s := by
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    RISCV64.abi, RISCV64.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩]

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract RISCV64.abi 0).pre s := by
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, RISCV64.abi, RISCV64.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩]

theorem encFrameSat_pre : ∃ s, (Proof.AesSiv.encryptRoundsContract RISCV64.abi 2576).pre s := by
  implies_sat [Proof.AesSiv.encryptRoundsContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, Proof.AesSiv.encryptRoundsPost,
    RISCV64.abi, RISCV64.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x5000, 16⟩]

theorem decFrameSat_pre : ∃ s, (Proof.AesSiv.decryptRoundsContract RISCV64.abi 2576).pre s := by
  implies_sat [Proof.AesSiv.decryptRoundsContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Proof.AesSiv.decryptRoundsPost,
    Spec.Siv.decryptLeak, RISCV64.abi, RISCV64.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩]

/-! ## Constant time -/

/-- Descriptors whose bytes are the same in two memories have the same words. -/
theorem descW_eq {m m' : Mem} {A : Addr} {N : Nat}
    (h : ∀ k < N * 16, m (A + BitVec.ofNat 64 k) = m' (A + BitVec.ofNat 64 k))
    {i j : Nat} (hi : i < N) (hj : j < 2) : descW m A i j = descW m' A i j := by
  have e := Mem.read_congr (m := m) (m' := m') (a := A + BitVec.ofNat 64 (16 * i + 8 * j))
    (n := 64 / 8) fun k hk => by rw [Offset.add_add]; exact h _ (by omega_using [hi, hj, hk])
  simp only [descW, Mem.readW, e]

/-- Two runs from the same public arguments: both from the public values of
the first, with the same descriptors. -/
theorem enc_two {s₁ s₂ : State} (A₂ : Args (cxOf s₂) s₂) (hA₂ : Ads (cxOf s₂) s₂.mem s₂)
    (hp : s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
      s₁.gpr .a7 = s₂.gpr .a7 ∧ ∀ i, i < (s₁.gpr .a3).toNat * 16 →
        s₁.mem (s₁.gpr .a2 + BitVec.ofNat 64 i) = s₂.mem (s₁.gpr .a2 + BitVec.ofNat 64 i)) :
    Args (cxOf s₁) s₂ ∧ Ads (cxOf s₁) s₂.mem s₂ ∧ DescAgree (cxOf s₁) s₁.mem s₂.mem := by
  obtain ⟨-, q3, q4, q5, q6, q7, q8, q9, q10, hd⟩ := hp
  have hcx : cxOf s₂ = cxOf s₁ := by simp only [cxOf, q3, q4, q5, q6, q7, q8, q9, q10]
  rw [hcx] at A₂ hA₂
  exact ⟨A₂, hA₂, fun i hi => ⟨descW_eq hd hi (by decide), descW_eq hd hi (by decide)⟩⟩

theorem encrypt_verified : Verified RISCV64.target Impl.AesSiv.RISCV64.encrypt
    (Proof.AesSiv.encryptScratchContract RISCV64.abi 0) := by
  refine ⟨encrypt_correct, VG.Proof.Gather.RISCV64.ct_of fun s₁ s₂ h₁ h₂ hp => ?_, encSat_pre⟩
  sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, RISCV64.abi, RISCV64.argRegs,
    List.getD] at hp
  obtain ⟨A₁, hA₁, -⟩ := encPre_of h₁
  obtain ⟨A₂, hA₂, -⟩ := encPre_of h₂
  obtain ⟨A₂', hA₂', hd⟩ := enc_two A₂ hA₂ hp
  exact encrypt_rel A₁ A₂' hA₁ hA₂' hd hp.1

theorem decrypt_verified : Verified RISCV64.target Impl.AesSiv.RISCV64.decrypt
    (Proof.AesSiv.decryptScratchContract RISCV64.abi 0) := by
  refine ⟨decrypt_correct, VG.Proof.Gather.RISCV64.ct_of fun s₁ s₂ h₁ h₂ hp => ?_, decSat_pre⟩
  sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptLeak,
    RISCV64.abi, RISCV64.argRegs, List.getD] at hp
  obtain ⟨hsp, -, hr⟩ := hp
  obtain ⟨A₁, hA₁⟩ := decPre_of h₁
  obtain ⟨A₂, hA₂⟩ := decPre_of h₂
  obtain ⟨A₂', hA₂', hd⟩ := enc_two A₂ hA₂ ⟨hsp, hr⟩
  exact decrypt_rel A₁ A₂' hA₁ hA₂' hd hsp

/-! ## The working space on the stack -/

/-- `encrypt` with its working space in a frame of 2576 bytes. -/
theorem encrypt_framed : Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2576 .a7
    Impl.AesSiv.RISCV64.encrypt) (Proof.AesSiv.encryptRoundsContract RISCV64.abi 2576) :=
  RISCV64.Verified.stackScratchLists (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.encryptPre RISCV64.abi.ptrBits) (post := Proof.AesSiv.encryptRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2576) encrypt_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.encryptPostOut_local _ vs m m₁ m₂ r hl)
    encFrameSat_pre

/-- `decrypt` with its working space in a frame of 2576 bytes. -/
theorem decrypt_framed : Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2576 .a7
    Impl.AesSiv.RISCV64.decrypt) (Proof.AesSiv.decryptRoundsContract RISCV64.abi 2576) :=
  RISCV64.Verified.stackScratchLists (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.decryptPre RISCV64.abi.ptrBits) (post := Proof.AesSiv.decryptRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2576) (leak := some (Spec.Siv.decryptLeak RISCV64.abi.ptrBits))
    decrypt_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.decryptPostOut_local _ vs m m₁ m₂ r hl)
    decFrameSat_pre

end VG.Proof.AesSiv.RISCV64
