module

public import VerifiedGarbage.Impl.Modes.RISCV64.Counter
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ctr
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Big-endian counter increments on RISC-V

`incBE_wp`: `incBE w` adds 1 to the `w`-byte big-endian number at `Q`
modulo `256 ^ w` (`incBEMem`), a byte at a time from the last, the carry in
`t1`; it writes only `t0` and `t1`. After `k` bytes, the counter's bytes are
its first `w - k` and the increment of its last `k` (`stepBytes`), and the
carry is the increment's carry out of them (`incSteps_run`).
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64.Counter

open VG VG.RISCV64 VG.Impl.Modes.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (toNat ofNat)

/-- Memory with the `w` bytes at `Q` incremented. -/
def incBEMem (w : Nat) (m : Mem) (Q : Addr) : Mem := fun x =>
  if (x - Q).toNat < w then (ofNat (toNat (bytesAt m Q w) + 1) w).getD (x - Q).toNat 0 else m x

/-! ## The bytes -/

theorem toNat_singleton (b : Byte) : toNat [b] = b.toNat := by simp [toNat]

theorem foldl_lt : ∀ (l : List Byte) {acc j : Nat}, acc < 256 ^ j →
    l.foldl (fun a b => 256 * a + b.toNat) acc < 256 ^ (j + l.length)
  | [], _, _, h => by simpa using h
  | b :: l, acc, j, h => by
    rw [List.foldl_cons, List.length_cons, show j + (l.length + 1) = (j + 1) + l.length by omega]
    refine foldl_lt l ?_
    have := b.isLt
    have : 256 * acc + 256 ≤ 256 * 256 ^ j := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    rw [Nat.pow_succ]; omega

theorem toNat_lt (l : List Byte) : toNat l < 256 ^ l.length := by
  have := foldl_lt l (acc := 0) (j := 0) (by decide)
  rwa [Nat.zero_add] at this

theorem ofNat_one (x : Nat) : ofNat x 1 = [BitVec.ofNat 8 x] := by simp [ofNat]

/-- The counter's bytes after `k` of them: the first `w - k` as they were, and
the increment of the last `k`. -/
def stepBytes (B : List Byte) (w k : Nat) : List Byte :=
  B.take (w - k) ++ ofNat (toNat (B.drop (w - k)) + 1) k

/-- The carry out of the last `k` bytes. -/
def carry (B : List Byte) (w k : Nat) : Nat := (toNat (B.drop (w - k)) + 1) / 256 ^ k

theorem carry_le (B : List Byte) {w k : Nat} (hB : B.length = w) (hk : k ≤ w) : carry B w k ≤ 1 := by
  have h := toNat_lt (B.drop (w - k))
  rw [List.length_drop, hB, show w - (w - k) = k by omega] at h
  unfold carry
  have hp : 0 < 256 ^ k := Nat.pow_pos (by decide)
  have : toNat (B.drop (w - k)) + 1 < 2 * 256 ^ k := by omega
  have := (Nat.div_lt_iff_lt_mul hp).mpr this
  omega

theorem stepBytes_zero (B : List Byte) {w : Nat} (hB : B.length = w) : stepBytes B w 0 = B := by
  simp [stepBytes, ofNat, ← hB]

theorem stepBytes_full (B : List Byte) (w : Nat) :
    stepBytes B w w = ofNat (toNat B + 1) w := by
  simp [stepBytes]

theorem stepBytes_length (B : List Byte) {w k : Nat} (hB : B.length = w) (hk : k ≤ w) :
    (stepBytes B w k).length = w := by
  simp [stepBytes, VG.Proof.AesCtr.length_ofNat, hB]; omega

/-- The next byte: byte `w - 1 - k` plus the carry. -/
theorem stepBytes_succ (B : List Byte) {w k : Nat} (hB : B.length = w) (hk : k < w) :
    stepBytes B w (k + 1) = (stepBytes B w k).set (w - 1 - k)
      (BitVec.ofNat 8 ((B[w - 1 - k]'(by omega)).toNat + carry B w k)) := by
  have e1 : B.take (w - k) = B.take (w - 1 - k) ++ [B[w - 1 - k]'(by omega)] := by
    rw [show w - k = w - 1 - k + 1 by omega, List.take_add_one, List.getElem?_eq_getElem (by omega)]
    rfl
  have e2 : B.drop (w - (k + 1)) = B[w - 1 - k]'(by omega) :: B.drop (w - k) := by
    rw [show w - (k + 1) = w - 1 - k by omega, List.drop_eq_getElem_cons (by omega),
      show w - 1 - k + 1 = w - k by omega]
  have hlen : (B.drop (w - k)).length = k := by rw [List.length_drop, hB]; omega
  have ht : toNat (B.drop (w - (k + 1))) =
      (B[w - 1 - k]'(by omega)).toNat * 256 ^ k + toNat (B.drop (w - k)) := by
    rw [e2, show (B[w - 1 - k]'(by omega)) :: B.drop (w - k) = [B[w - 1 - k]'(by omega)] ++ B.drop (w - k)
      from rfl, VG.Proof.AesCtr.toNat_append, toNat_singleton, hlen]
  have hp : 0 < 256 ^ k := Nat.pow_pos (by decide)
  unfold stepBytes
  rw [e1, ht, show w - (k + 1) = w - 1 - k by omega, Nat.add_comm k 1, VG.Proof.AesCtr.ofNat_add, ofNat_one]
  have hd : ((B[w - 1 - k]'(by omega)).toNat * 256 ^ k + toNat (B.drop (w - k)) + 1) / 256 ^ k =
      (B[w - 1 - k]'(by omega)).toNat + carry B w k := by
    unfold carry
    rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.add_comm]
  have hm : ofNat ((B[w - 1 - k]'(by omega)).toNat * 256 ^ k + toNat (B.drop (w - k)) + 1) k =
      ofNat (toNat (B.drop (w - k)) + 1) k := by
    apply VG.Proof.AesCtr.ofNat_congr
    rw [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_mod]
  rw [hd, hm]
  have hl : (B.take (w - 1 - k)).length = w - 1 - k := by rw [List.length_take, hB]; omega
  rw [List.append_assoc, List.set_append_right _ _ (by omega), hl, Nat.sub_self]
  rfl

theorem carry_succ (B : List Byte) {w k : Nat} (hB : B.length = w) (hk : k < w) :
    carry B w (k + 1) = ((B[w - 1 - k]'(by omega)).toNat + carry B w k) / 256 := by
  have e2 : B.drop (w - (k + 1)) = B[w - 1 - k]'(by omega) :: B.drop (w - k) := by
    rw [show w - (k + 1) = w - 1 - k by omega, List.drop_eq_getElem_cons (by omega),
      show w - 1 - k + 1 = w - k by omega]
  have hlen : (B.drop (w - k)).length = k := by rw [List.length_drop, hB]; omega
  have hp : 0 < 256 ^ k := Nat.pow_pos (by decide)
  unfold carry
  rw [e2, show (B[w - 1 - k]'(by omega)) :: B.drop (w - k) = [B[w - 1 - k]'(by omega)] ++ B.drop (w - k)
    from rfl, VG.Proof.AesCtr.toNat_append, toNat_singleton, hlen, Nat.pow_succ, ← Nat.div_div_eq_div_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.add_comm]

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ## One byte -/

theorem write1_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    m.write a 1 v x = if x = a then v else m x := by
  by_cases h : x = a
  · subst h
    rw [ite_eq_left rfl]
    simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_lt_one, ite_true, Nat.mul_zero]
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
  · rw [ite_eq_right h]
    exact Mem.write_apply fun h' => h (by
      have : (x - a).toNat = 0 := by omega
      have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [this]; rfl)
      calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
        _ = a := by rw [h0]; simp)

theorem incByte_run {base : Reg} (h0 : base ≠ .t0) (_h1 : base ≠ .t1) {off : Nat} (ho : off < 2048)
    (u : State) {a : Addr} (ha : u.gpr base + BitVec.ofNat 64 off = a)
    (hr : InRegions (u.rd ++ u.wr) a 1) (hw : InRegions u.wr a 1) (hc : (u.gpr .t1).toNat ≤ 1) :
    WP isa (.block (incByte base off)) u fun t =>
      t.mem = u.mem.write a 1 (BitVec.ofNat 8 ((u.mem a).toNat + (u.gpr .t1).toNat)) ∧
      t.gpr .t1 = BitVec.ofNat 64 (((u.mem a).toNat + (u.gpr .t1).toNat) / 256) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → t.gpr r = u.gpr r) ∧ t.rd = u.rd ∧ t.wr = u.wr := by
  subst ha
  unfold incByte
  mrun [hr, hw, ho, Ne.symm h0, h0]
  have hb := (u.mem (u.gpr base + BitVec.ofNat 64 off)).isLt
  have hs : ((u.mem (u.gpr base + BitVec.ofNat 64 off)).setWidth 64 + u.gpr .t1).toNat =
      (u.mem (u.gpr base + BitVec.ofNat 64 off)).toNat + (u.gpr .t1).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, fun r hr0 hr1 => by simp [hr0, hr1]⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, hs, BitVec.toNat_ofNat]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, hs, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega)]

/-! ## The increment -/

theorem flatMap_range_succ {α : Type} (f : Nat → List α) (k : Nat) :
    (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- After `k` bytes from `s`. -/
structure StepInv (w : Nat) (s : State) (Q : Addr) (k : Nat) (u : State) : Prop where
  mem : ∀ x, u.mem x = if (x - Q).toNat < w then
    (stepBytes (bytesAt s.mem Q w) w k).getD (x - Q).toNat 0 else s.mem x
  t1 : u.gpr .t1 = BitVec.ofNat 64 (carry (bytesAt s.mem Q w) w k)
  gpr : ∀ r, r ≠ .t0 → r ≠ .t1 → u.gpr r = s.gpr r
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem incSteps_run {base : Reg} (h0 : base ≠ .t0) (h1 : base ≠ .t1) {off w : Nat} (hw : w ≤ 16)
    (ho : off + w ≤ 2048) {s : State} {Q : Addr} (ha : s.gpr base + BitVec.ofNat 64 off = Q)
    (hr : ∀ i < w, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1)
    (hW : ∀ i < w, InRegions s.wr (Q + BitVec.ofNat 64 i) 1) {u : State}
    (I : StepInv w s Q 0 u) :
    ∀ k ≤ w, WP isa (.block ((List.range k).flatMap fun i => incByte base (off + (w - 1 - i)))) u
      (StepInv w s Q k)
  | 0, _ => WP.block_nil I
  | k + 1, hk => by
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (incSteps_run h0 h1 hw ho ha hr hW I k (by omega)) fun v J => ?_
    have hB : (bytesAt s.mem Q w).length = w := by simp [bytesAt]
    have hp : w - 1 - k < w := by omega
    have hav : v.gpr base + BitVec.ofNat 64 (off + (w - 1 - k)) = Q + BitVec.ofNat 64 (w - 1 - k) := by
      rw [J.gpr _ h0 h1, ← ha, Offset.add_add]
    have hsub : (Q + BitVec.ofNat 64 (w - 1 - k) - Q).toNat = w - 1 - k := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    -- The byte read is the original one.
    have hbyte : v.mem (Q + BitVec.ofNat 64 (w - 1 - k)) = (bytesAt s.mem Q w)[w - 1 - k]'(by omega) := by
      rw [J.mem, hsub, ite_eq_left hp, getD_of_lt (by rw [stepBytes_length _ hB (by omega)]; exact hp)]
      simp only [stepBytes, List.getElem_append_left (by rw [List.length_take, hB]; omega : w - 1 - k <
        (List.take (w - k) (bytesAt s.mem Q w)).length), List.getElem_take]
    have hc := carry_le (bytesAt s.mem Q w) hB (k := k) (by omega)
    refine WP.mono (incByte_run h0 h1 (by omega) v hav (by rw [J.rd, J.wr]; exact hr _ hp)
      (by rw [J.wr]; exact hW _ hp) (by rw [J.t1, BitVec.toNat_ofNat]; omega))
      fun t ⟨tm, t1, tg, trd, twr⟩ => ⟨fun x => ?_, ?_, fun r r0 r1 => by rw [tg r r0 r1, J.gpr r r0 r1],
        by rw [trd, J.rd], by rw [twr, J.wr]⟩
    · rw [tm, write1_apply, hbyte, J.t1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        stepBytes_succ _ hB (by omega)]
      by_cases hx : x = Q + BitVec.ofNat 64 (w - 1 - k)
      · subst hx
        rw [ite_eq_left rfl, hsub, ite_eq_left hp, getD_of_lt (by
          rw [List.length_set, stepBytes_length _ hB (by omega)]; exact hp), List.getElem_set_self]
      · rw [ite_eq_right hx, J.mem]
        split
        · rename_i hxl
          have hne : (x - Q).toNat ≠ w - 1 - k := fun e => hx (by
            rw [← e]; apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (x - Q).isLt]
            simp [BitVec.toNat_sub]; omega)
          simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne)]
        · rfl
    · rw [t1, hbyte, J.t1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), carry_succ _ hB (by omega)]

theorem incBE_wp {base : Reg} (h0 : base ≠ .t0) (h1 : base ≠ .t1) {off w : Nat} (hw : w ≤ 16)
    (ho : off + w ≤ 2048) {s : State} {Q : Addr} (ha : s.gpr base + BitVec.ofNat 64 off = Q)
    (hr : ∀ i < w, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1)
    (hW : ∀ i < w, InRegions s.wr (Q + BitVec.ofNat 64 i) 1) {is : List Instr} {P : State → Prop}
    (k : ∀ s', s'.mem = incBEMem w s.mem Q → (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' P) :
    WP isa (.block (incBE w base off ++ is)) s P := by
  have hB : (bytesAt s.mem Q w).length = w := by simp [bytesAt]
  unfold incBE
  rw [List.cons_append, ← List.singleton_append, ← List.append_assoc, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (Q := fun u => u = s.write .t1 (BitVec.ofNat 64 1)) (by mrun) fun u hu => ?_
  subst hu
  have I : StepInv w s Q 0 (s.write .t1 (BitVec.ofNat 64 1)) := by
    refine ⟨fun x => ?_, ?_, fun r _ r1 => by simp [State.write, r1], rfl, rfl⟩
    · show s.mem x = _
      split
      · rename_i hx
        rw [stepBytes_zero _ hB, getD_of_lt (by rw [hB]; exact hx)]
        simp only [bytesAt, List.getElem_map, List.getElem_range]
        congr 1
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (x - Q).isLt]
        simp [BitVec.toNat_sub]; omega
      · rfl
    · show BitVec.ofNat 64 1 = BitVec.ofNat 64 (carry _ w 0)
      rw [carry, List.drop_eq_nil_of_le (by omega), Nat.pow_zero, Nat.div_one]
      rfl
  refine WP.mono (incSteps_run h0 h1 hw ho ha hr hW I w (Nat.le_refl _))
    fun v J => k v (funext fun x => ?_) (fun r r0 r1 => J.gpr r r0 r1)
      J.rd J.wr
  rw [J.mem, stepBytes_full _ w]
  rfl

end VG.Proof.Modes.RISCV64.Counter
