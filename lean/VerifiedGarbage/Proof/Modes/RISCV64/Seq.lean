module

public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Ops
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Modes.RISCV64.Counter
public import VerifiedGarbage.Spec.Ctr
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Impl.Modes.RISCV64.Wide
public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
public import VerifiedGarbage.Proof.Framework.RISCV64.BigFrame

/-! ### `Modes.RISCV64.Step`, which only this module used -/

section

/-! ### `Modes.RISCV64.Ops`, which only this module used -/

section

/-! ### `Modes.RISCV64.Counter`, which only this module used -/

section

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
    rw [List.foldl_cons, List.length_cons, show j + (l.length + 1) = (j + 1) + l.length by omega_using []]
    refine foldl_lt l ?_
    have := b.isLt
    have : 256 * acc + 256 ≤ 256 * 256 ^ j := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    rw [Nat.pow_succ]; omega_using [h]

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
  obtain h := toNat_lt (B.drop (w - k))
  rw [List.length_drop, hB, show w - (w - k) = k by omega_using [hk]] at h
  unfold carry
  obtain hp : 0 < 256 ^ k := Nat.pow_pos (by decide)
  have : toNat (B.drop (w - k)) + 1 < 2 * 256 ^ k := by omega_using [h]
  have := (Nat.div_lt_iff_lt_mul hp).mpr this
  omega_using [this]

theorem stepBytes_zero (B : List Byte) {w : Nat} (hB : B.length = w) : stepBytes B w 0 = B := by
  simp [stepBytes, ofNat, ← hB]

theorem stepBytes_full (B : List Byte) (w : Nat) :
    stepBytes B w w = ofNat (toNat B + 1) w := by
  simp [stepBytes]

theorem stepBytes_length (B : List Byte) {w k : Nat} (hB : B.length = w) (hk : k ≤ w) :
    (stepBytes B w k).length = w := by
  simp [stepBytes, VG.Proof.AesCtr.length_ofNat, hB]; omega_using [hk]

/-- The next byte: byte `w - 1 - k` plus the carry. -/
theorem stepBytes_succ (B : List Byte) {w k : Nat} (hB : B.length = w) (hk : k < w) :
    stepBytes B w (k + 1) = (stepBytes B w k).set (w - 1 - k)
      (BitVec.ofNat 8 ((B[w - 1 - k]'(by omega_using [hB, hk])).toNat + carry B w k)) := by
  obtain e1 : B.take (w - k) = B.take (w - 1 - k) ++ [B[w - 1 - k]'(by omega_using [hB, hk])] := by
    rw [show w - k = w - 1 - k + 1 by omega_using [hk], List.take_add_one, List.getElem?_eq_getElem (by omega_using [hB, hk])]
    rfl
  obtain e2 : B.drop (w - (k + 1)) = B[w - 1 - k]'(by omega_using [hB, hk]) :: B.drop (w - k) := by
    rw [show w - (k + 1) = w - 1 - k by omega_using [], List.drop_eq_getElem_cons (by omega_using [hB, hk]),
      show w - 1 - k + 1 = w - k by omega_using [hk]]
  obtain hlen : (B.drop (w - k)).length = k := by rw [List.length_drop, hB]; omega_using [hk]
  obtain ht : toNat (B.drop (w - (k + 1))) =
      (B[w - 1 - k]'(by omega_using [hB, hk])).toNat * 256 ^ k + toNat (B.drop (w - k)) := by
    rw [e2, show (B[w - 1 - k]'(by omega_using [hB, hk])) :: B.drop (w - k) = [B[w - 1 - k]'(by omega_using [hB, hk])] ++ B.drop (w - k)
      from rfl, VG.Proof.AesCtr.toNat_append, toNat_singleton, hlen]
  obtain hp : 0 < 256 ^ k := Nat.pow_pos (by decide)
  unfold stepBytes
  rw [e1, ht, show w - (k + 1) = w - 1 - k by omega_using [], Nat.add_comm k 1, VG.Proof.AesCtr.ofNat_add, ofNat_one]
  obtain hd : ((B[w - 1 - k]'(by omega_using [hB, hk])).toNat * 256 ^ k + toNat (B.drop (w - k)) + 1) / 256 ^ k =
      (B[w - 1 - k]'(by omega_using [hB, hk])).toNat + carry B w k := by
    unfold carry
    rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.add_comm]
  obtain hm : ofNat ((B[w - 1 - k]'(by omega_using [hB, hk])).toNat * 256 ^ k + toNat (B.drop (w - k)) + 1) k =
      ofNat (toNat (B.drop (w - k)) + 1) k := by
    apply VG.Proof.AesCtr.ofNat_congr
    rw [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_mod]
  rw [hd, hm]
  obtain hl : (B.take (w - 1 - k)).length = w - 1 - k := by rw [List.length_take, hB]; omega_using []
  rw [List.append_assoc, List.set_append_right _ _ (by omega_using [hl]), hl, Nat.sub_self]
  rfl

theorem carry_succ (B : List Byte) {w k : Nat} (hB : B.length = w) (hk : k < w) :
    carry B w (k + 1) = ((B[w - 1 - k]'(by omega_using [hB, hk])).toNat + carry B w k) / 256 := by
  obtain e2 : B.drop (w - (k + 1)) = B[w - 1 - k]'(by omega_using [hB, hk]) :: B.drop (w - k) := by
    rw [show w - (k + 1) = w - 1 - k by omega_using [], List.drop_eq_getElem_cons (by omega_using [hB, hk]),
      show w - 1 - k + 1 = w - k by omega_using [hk]]
  obtain hlen : (B.drop (w - k)).length = k := by rw [List.length_drop, hB]; omega_using [hk]
  obtain hp : 0 < 256 ^ k := Nat.pow_pos (by decide)
  unfold carry
  rw [e2, show (B[w - 1 - k]'(by omega_using [hB, hk])) :: B.drop (w - k) = [B[w - 1 - k]'(by omega_using [hB, hk])] ++ B.drop (w - k)
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
      have : (x - a).toNat = 0 := by omega_using [h']
      obtain h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [this]; rfl)
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
  obtain hb := (u.mem (u.gpr base + BitVec.ofNat 64 off)).isLt
  obtain hs : ((u.mem (u.gpr base + BitVec.ofNat 64 off)).setWidth 64 + u.gpr .t1).toNat =
      (u.mem (u.gpr base + BitVec.ofNat 64 off)).toNat + (u.gpr .t1).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_using [hc]), Nat.mod_eq_of_lt (by omega_using [])]
  refine ⟨?_, ?_, fun r hr0 hr1 => by simp [hr0, hr1]⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, hs, BitVec.toNat_ofNat]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, hs, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega_using [])]

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
    refine WP.mono (incSteps_run h0 h1 hw ho ha hr hW I k (by omega_using [hk])) fun v J => ?_
    obtain hB : (bytesAt s.mem Q w).length = w := by simp [bytesAt]
    obtain hp : w - 1 - k < w := by omega_using [hk]
    obtain hav : v.gpr base + BitVec.ofNat 64 (off + (w - 1 - k)) = Q + BitVec.ofNat 64 (w - 1 - k) := by
      rw [J.gpr _ h0 h1, ← ha, Offset.add_add]
    obtain hsub : (Q + BitVec.ofNat 64 (w - 1 - k) - Q).toNat = w - 1 - k := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hw])]
    -- The byte read is the original one.
    obtain hbyte : v.mem (Q + BitVec.ofNat 64 (w - 1 - k)) = (bytesAt s.mem Q w)[w - 1 - k]'(by omega_using [hk, hB]) := by
      rw [J.mem, hsub, ite_eq_left hp, getD_of_lt (by rw [stepBytes_length _ hB (by omega_using [hk])]; exact hp)]
      simp only [stepBytes, List.getElem_append_left (by rw [List.length_take, hB]; omega_using [hk] : w - 1 - k <
        (List.take (w - k) (bytesAt s.mem Q w)).length), List.getElem_take]
    obtain hc := carry_le (bytesAt s.mem Q w) hB (k := k) (by omega_using [hk])
    refine WP.mono (incByte_run h0 h1 (by omega_using [ho, hk]) v hav (by rw [J.rd, J.wr]; exact hr _ hp)
      (by rw [J.wr]; exact hW _ hp) (by rw [J.t1, BitVec.toNat_ofNat]; omega_using [hc]))
      fun t ⟨tm, t1, tg, trd, twr⟩ => ⟨fun x => ?_, ?_, fun r r0 r1 => by rw [tg r r0 r1, J.gpr r r0 r1],
        by rw [trd, J.rd], by rw [twr, J.wr]⟩
    · rw [tm, write1_apply, hbyte, J.t1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc]),
        stepBytes_succ _ hB (by omega_using [hk])]
      by_cases hx : x = Q + BitVec.ofNat 64 (w - 1 - k)
      · subst hx
        rw [ite_eq_left rfl, hsub, ite_eq_left hp, getD_of_lt (by
          rw [List.length_set, stepBytes_length _ hB (by omega_using [hk])]; exact hp), List.getElem_set_self]
      · rw [ite_eq_right hx, J.mem]
        split
        · rename_i hxl
          obtain hne : (x - Q).toNat ≠ w - 1 - k := fun e => hx (by
            rw [← e]; apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (x - Q).isLt]
            simp [BitVec.toNat_sub]; omega_using [])
          simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne)]
        · rfl
    · rw [t1, hbyte, J.t1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc]), carry_succ _ hB (by omega_using [hk])]

theorem incBE_wp {base : Reg} (h0 : base ≠ .t0) (h1 : base ≠ .t1) {off w : Nat} (hw : w ≤ 16)
    (ho : off + w ≤ 2048) {s : State} {Q : Addr} (ha : s.gpr base + BitVec.ofNat 64 off = Q)
    (hr : ∀ i < w, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1)
    (hW : ∀ i < w, InRegions s.wr (Q + BitVec.ofNat 64 i) 1) {is : List Instr} {P : State → Prop}
    (k : ∀ s', s'.mem = incBEMem w s.mem Q → (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' P) :
    WP isa (.block (incBE w base off ++ is)) s P := by
  obtain hB : (bytesAt s.mem Q w).length = w := by simp [bytesAt]
  unfold incBE
  rw [List.cons_append, ← List.singleton_append, ← List.append_assoc, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (Q := fun u => u = s.write .t1 (BitVec.ofNat 64 1)) (by mrun) fun u hu => ?_
  subst hu
  obtain I : StepInv w s Q 0 (s.write .t1 (BitVec.ofNat 64 1)) := by
    refine ⟨fun x => ?_, ?_, fun r _ r1 => by simp [State.write, r1], rfl, rfl⟩
    · show s.mem x = _
      split
      · rename_i hx
        rw [stepBytes_zero _ hB, getD_of_lt (by rw [hB]; exact hx)]
        simp only [bytesAt, List.getElem_map, List.getElem_range]
        congr 1
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (x - Q).isLt]
        simp [BitVec.toNat_sub]; omega_using []
      · rfl
    · show BitVec.ofNat 64 1 = BitVec.ofNat 64 (carry _ w 0)
      rw [carry, List.drop_eq_nil_of_le (by omega_using [hB]), Nat.pow_zero, Nat.div_one]
      rfl
  refine WP.mono (incSteps_run h0 h1 hw ho ha hr hW I w (Nat.le_refl _))
    fun v J => k v (funext fun x => ?_) (fun r r0 r1 => J.gpr r r0 r1)
      J.rd J.wr
  rw [J.mem, stepBytes_full _ w]
  rfl

end VG.Proof.Modes.RISCV64.Counter

end

end


/-!
# The modes' operations on RISC-V

`opsCode_wp`: the code of a list of operations (`Core.opsCode`) does to
the bytes of the three areas in memory what `applyOps` says (with the
areas' contents read from memory, `cont`), and changes nothing else in
memory, and no register but `t0`, `t1` and `t2`. It needs each area's
address (`AreasOk.ea`: the base register and displacement of the area give
the address `A l` plus the offset, with an encodable displacement),
readable and writable bytes, and areas apart from each other. The
operations are copies and XORs (`opCode_wp_plain`), of bytes or of words
(`Core.loadW`, `Core.storeW`: a word at a time in an area that
`Core.wordAt w` names, whose address is then a multiple of 4, as the
offsets of a word are, `WordAl`; else a byte at a time), and the counters'
increments (`Proof/Modes/RISCV64/Counter.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Modes VG.Impl.Modes.RISCV64
open VG.Impl.Words.RISCV64 (loadLE32 storeLE32)
open VG.Spec.Aes (bytesAt)

/-- The areas' contents, from memory: byte `i` of area `l` at `A l + i`. -/
def cont (A : Loc → Addr) (m : Mem) : Areas := fun l i => m (A l + BitVec.ofNat 64 i)

/-- The areas of the step, of lengths `len`, at `A` in `s`: each operand's
address, readable (or writable) and apart. -/
structure AreasOk (c : Core) (s : State) (len : Loc → Nat) (A : Loc → Addr) (ws : List Loc) : Prop where
  ea : ∀ l off, off < len l →
    s.gpr (c.loc l).1 + BitVec.ofNat 64 ((c.loc l).2 + off) = A l + BitVec.ofNat 64 off
  disp : ∀ l off, off < len l → (c.loc l).2 + off < 2048
  rd : ∀ l off w, 0 < w → off + w ≤ len l → InRegions (s.rd ++ s.wr) (A l + BitVec.ofNat 64 off) w
  wr : ∀ l ∈ ws, ∀ off w, 0 < w → off + w ≤ len l → InRegions s.wr (A l + BitVec.ofNat 64 off) w
  apart : ∀ l l', l ≠ l' → Region.Disjoint ⟨A l, len l⟩ ⟨A l', len l'⟩
  fit : ∀ l, len l < 2 ^ 32

/-- What an operation's code may write: `t0`, `t1` and `t2`. -/
def Tmp (s s' : State) : Prop := ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r

theorem AreasOk.congr {c : Core} {s s' : State} {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc}
    (h : AreasOk c s len A ws) (hg : ∀ l, s'.gpr (c.loc l).1 = s.gpr (c.loc l).1) (hr : s'.rd = s.rd)
    (hw : s'.wr = s.wr) : AreasOk c s' len A ws :=
  ⟨fun l off ho => by rw [hg l]; exact h.ea l off ho, h.disp,
    fun l off w hw0 ho => by rw [hr, hw]; exact h.rd l off w hw0 ho,
    fun l hl off w hw0 ho => by rw [hw]; exact h.wr l hl off w hw0 ho, h.apart, h.fit⟩

/-- Every area. -/
def allLocs : List Loc := [.dat, .chn, .buf]

theorem mem_allLocs (l : Loc) : l ∈ allLocs := by cases l <;> simp [allLocs]

/-- An operation that is a copy or an XOR, not an increment. -/
def Plain (o : Op) : Prop := o.inc = false ∧ o.inc32 = false

/-- Memory after `o`: its destination's bytes are `Op.val` of the areas. -/
def opMem (A : Loc → Addr) (o : Op) (m : Mem) : Mem := fun x =>
  if (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat < o.width then
    o.val (cont A m) (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat
  else m x

theorem write4_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    m.writeW a v x = if (x - a).toNat < 4 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  simp only [Mem.writeW, Mem.write]
  rfl

theorem write1_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    m.writeW a v x = if (x - a).toNat < 1 then v else m x := by
  simp only [Mem.writeW, Mem.write]
  split
  · rename_i h
    rw [show (x - a).toNat = 0 by omega_using [h]]
    simp
  · rfl

theorem byte_xor (u v : BitVec 32) (t : Nat) :
    (u ^^^ v).extractLsb' (8 * t) 8 = u.extractLsb' (8 * t) 8 ^^^ v.extractLsb' (8 * t) 8 := by
  ext j hj
  simp

theorem setWidth_xor8 (u v : Byte) : (u.setWidth 64 ^^^ v.setWidth 64).setWidth 8 = u ^^^ v := by
  ext j hj
  simp

theorem setWidth_xor32 (u v : BitVec 32) : (u.setWidth 64 ^^^ v.setWidth 64).setWidth 32 = u ^^^ v := by
  ext j hj
  simp

theorem setWidth32_64 (u : BitVec 32) : (u.setWidth 64).setWidth 32 = u := by
  ext j hj
  simp

theorem setWidth8_64 (u : Byte) : (u.setWidth 64).setWidth 8 = u := by
  ext j hj
  simp

theorem byte_xor_zero' (u : Byte) : u ^^^ 0 = u := by simp

theorem width_pos (o : Op) : 0 < o.width := by
  unfold Op.width; split <;> (try split) <;> (try split) <;> decide

theorem loc_ne (c : Core) (l : Loc) : (c.loc l).1 ≠ .t0 ∧ (c.loc l).1 ≠ .t1 ∧ (c.loc l).1 ≠ .t2 := by
  cases l <;> simp [Core.loc, sb]

/-! ## Words a byte at a time -/

theorem wp_loadLE32 {s : State} {d tmp n : Reg} {off : Nat} {a : Addr} {is : List Instr} {Q : State → Prop}
    (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp) (ho : off + 3 < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', s'.gpr d = (s.mem.readW a 32).setWidth 64 → (∀ r, r ≠ d → r ≠ tmp → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (loadLE32 d tmp n off ++ is)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.loadLE32_ok hdn htn hdt ho (by rw [ha]; exact hin)) fun s' e => ?_
  subst e
  refine k _ (by rw [RegUpd.gpr_write_self, ha]) (fun r h1 h2 => by
    rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]) rfl rfl rfl

theorem wp_storeLE32 {s : State} {v tmp n : Reg} {off : Nat} {a : Addr} {is : List Instr} {Q : State → Prop}
    (htv : tmp ≠ v) (htn : tmp ≠ n) (ho : off + 3 < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', s'.mem = s.mem.writeW a ((s.gpr v).setWidth 32) → (∀ r, r ≠ tmp → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (storeLE32 v tmp n off ++ is)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.storeLE32_ok htv htn ho (by rw [ha]; exact hout)) fun s' e => ?_
  subst e
  refine k _ (by rw [ha]; rfl) (fun r h1 => by rw [RegUpd.gpr_write_of_ne _ _ h1]) rfl rfl

/-- A word's offsets are multiples of 4. -/
def WordAl (o : Op) : Prop :=
  o.wide = true → o.dOff % 4 = 0 ∧ o.sOff % 4 = 0 ∧ ∀ l off, o.xr = some (l, off) → off % 4 = 0

theorem al4 {p : Addr} (hp : p.toNat % 4 = 0) {d : Nat} (hd : d % 4 = 0) :
    (p + BitVec.ofNat 64 d).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hp, hd]

/-- A word of area `l`, as `Core.loadW` loads it. -/
theorem wp_loadW (c : Core) {w : Bool} {l : Loc} {s : State} {d tmp : Reg} {off : Nat} {a : Addr}
    {is : List Instr} {Q : State → Prop}
    (hdn : d ≠ (c.loc l).1) (htn : tmp ≠ (c.loc l).1) (hdt : d ≠ tmp) (ho : (c.loc l).2 + off + 3 < 2048)
    (ha : s.gpr (c.loc l).1 + BitVec.ofNat 64 ((c.loc l).2 + off) = a)
    (hal : Core.wordAt w l = true → a.toNat % 4 = 0) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', s'.gpr d = (s.mem.readW a 32).setWidth 64 → (∀ r, r ≠ d → r ≠ tmp → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (c.loadW w l d tmp off ++ is)) s Q := by
  unfold Core.loadW
  split
  · rename_i hw
    exact wp_lwu (by omega_using [ho]) ha (hal hw) hin fun s' u => k s' u.gpr (fun r h _ => u.other r h) u.mem u.rd u.wr
  · exact wp_loadLE32 hdn htn hdt ho ha hin k

/-- A word of area `l`, as `Core.storeW` stores it. -/
theorem wp_storeW (c : Core) {w : Bool} {l : Loc} {s : State} {v tmp : Reg} {off : Nat} {a : Addr}
    {is : List Instr} {Q : State → Prop}
    (htv : tmp ≠ v) (htn : tmp ≠ (c.loc l).1) (ho : (c.loc l).2 + off + 3 < 2048)
    (ha : s.gpr (c.loc l).1 + BitVec.ofNat 64 ((c.loc l).2 + off) = a)
    (hal : Core.wordAt w l = true → a.toNat % 4 = 0) (hout : InRegions s.wr a 4)
    (k : ∀ s', s'.mem = s.mem.writeW a ((s.gpr v).setWidth 32) → (∀ r, r ≠ tmp → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (c.storeW w l v tmp off ++ is)) s Q := by
  unfold Core.storeW
  split
  · rename_i hw
    exact wp_sw (by omega_using [ho]) ha (hal hw) hout fun s' u => k s' u.mem (fun r _ => by rw [u.gpr]) u.rd u.wr
  · exact wp_storeLE32 htv htn ho ha hout k

theorem copyBlk_wordAl (bw : Nat) (dst src : Loc) : ∀ o ∈ copyBlk bw dst src, WordAl o := by
  intro o ho
  simp only [copyBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨i, -, rfl⟩ := ho
  exact fun _ => ⟨Nat.mul_mod_right 4 i, Nat.mul_mod_right 4 i, fun _ _ h => by cases h⟩

theorem xorBlk_wordAl (bw : Nat) (dst a b : Loc) : ∀ o ∈ xorBlk bw dst a b, WordAl o := by
  intro o ho
  simp only [xorBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨i, -, rfl⟩ := ho
  exact fun _ => ⟨Nat.mul_mod_right 4 i, Nat.mul_mod_right 4 i, fun _ _ h => by
    cases h; exact Nat.mul_mod_right 4 i⟩

/-! ## One operation -/

theorem opCode_wp_plain (c : Core) (w : Bool) {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} {o : Op}
    (hpl : Plain o) (ho : o.InBounds len) (hwa : WordAl o)
    (hal : ∀ l, Core.wordAt w l = true → (A l).toNat % 4 = 0)
    (hdst : o.dst ∈ ws) {s : State} (h : AreasOk c s len A ws) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.mem = opMem A o s.mem → Tmp s s' → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (c.opCode w o ++ is)) s Q := by
  obtain ⟨hd, hs, hx⟩ := ho
  obtain ⟨hinc, hi32⟩ := hpl
  obtain hw0 := width_pos o
  obtain keep : ∀ {t : State}, Tmp s t → ∀ l, t.gpr (c.loc l).1 = s.gpr (c.loc l).1 :=
    fun ht l => ht _ (loc_ne c l).1 (loc_ne c l).2.1 (loc_ne c l).2.2
  obtain eaD := h.ea o.dst o.dOff (by omega_arith)
  obtain eaS := h.ea o.src o.sOff (by omega_arith)
  obtain nD := loc_ne c o.dst
  obtain nS := loc_ne c o.src
  simp only [Core.opCode, hinc, hi32, Bool.false_eq_true, ite_false]
  cases hwd : o.wide
  · -- A byte.
    obtain hW : o.width = 1 := by simp [Op.width, hinc, hi32, hwd]
    rw [hW] at hd hs hx
    obtain dD := h.disp o.dst o.dOff (by omega_arith)
    obtain dS := h.disp o.src o.sOff (by omega_arith)
    simp only [Bool.false_eq_true, ite_false]
    cases hxr : o.xr with
    | none =>
      simp only [List.nil_append, List.cons_append, List.append_nil]
      refine wp_lbu dS eaS (h.rd _ _ _ (by decide) hs) fun s₁ u₁ => ?_
      refine wp_sb (a := A o.dst + BitVec.ofNat 64 o.dOff) dD
        (by rw [u₁.other _ nD.1]; exact eaD) (by rw [u₁.wr]; exact h.wr _ hdst _ _ (by decide) hd) fun s₂ u₂ => ?_
      refine k s₂ ?_ (fun r h1 _ _ => by rw [u₂.gpr, u₁.other r h1]) (by rw [u₂.rd, u₁.rd])
        (by rw [u₂.wr, u₁.wr])
      funext x
      rw [u₂.mem, u₁.mem, u₁.gpr, setWidth8_64, write1_apply]
      simp only [opMem, hW, Op.val, hinc, hi32, Bool.false_eq_true, ite_false, hxr, cont, byte_xor_zero']
      split
      · rename_i hlt; rw [show (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat = 0 by omega_arith, Nat.add_zero]
      · rfl
    | some p =>
      obtain ⟨l, off⟩ := p
      obtain hx' := hx l off hxr
      obtain eaX := h.ea l off (by omega_arith)
      obtain dX := h.disp l off (by omega_arith)
      simp only [List.cons_append, List.append_assoc]
      refine wp_lbu dS eaS (h.rd _ _ _ (by decide) hs) fun s₁ u₁ => ?_
      refine wp_lbu (a := A l + BitVec.ofNat 64 off) dX (by rw [u₁.other _ (loc_ne c l).1]; exact eaX)
        (by rw [u₁.rd, u₁.wr]; exact h.rd _ _ _ (by decide) hx') fun s₂ u₂ => ?_
      refine wp_xor fun s₃ u₃ => ?_
      refine wp_sb (a := A o.dst + BitVec.ofNat 64 o.dOff) dD (by
          rw [u₃.other _ nD.1, u₂.other _ nD.2.1, u₁.other _ nD.1]
          exact eaD)
        (by rw [u₃.wr, u₂.wr, u₁.wr]; exact h.wr _ hdst _ _ (by decide) hd) fun s₄ u₄ => ?_
      refine k s₄ ?_ (fun r h1 h2 _ => by rw [u₄.gpr, u₃.other r h1, u₂.other r h2, u₁.other r h1])
        (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      funext x
      rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem,
        setWidth_xor8, write1_apply]
      simp only [opMem, hW, Op.val, hinc, hi32, Bool.false_eq_true, ite_false, hxr, cont]
      split
      · rename_i hlt; rw [show (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat = 0 by omega_arith,
          Nat.add_zero, Nat.add_zero]
      · rfl
  · -- A word.
    obtain hW : o.width = 4 := by simp [Op.width, hinc, hi32, hwd]
    obtain ⟨aD, aS, aX⟩ := hwa hwd
    obtain alA : ∀ l off, off % 4 = 0 → Core.wordAt w l = true → (A l + BitVec.ofNat 64 off).toNat % 4 = 0 :=
      fun l off ho hw => al4 (hal l hw) ho
    rw [hW] at hd hs hx
    obtain dD := h.disp o.dst (o.dOff + 3) (by omega_arith)
    obtain dS := h.disp o.src (o.sOff + 3) (by omega_arith)
    simp only [ite_true]
    cases hxr : o.xr with
    | none =>
      simp only [List.nil_append, List.append_assoc]
      refine wp_loadW c nS.1.symm nS.2.2.symm (by decide) (by omega_arith) eaS (alA _ _ aS)
        (h.rd _ _ _ (by decide) hs) fun s₁ g₁ o₁ m₁ rd₁ wr₁ => ?_
      refine wp_storeW c (a := A o.dst + BitVec.ofNat 64 o.dOff) (by decide) nD.2.2.symm (by omega_arith)
        (by rw [o₁ _ nD.1 nD.2.2]; exact eaD) (alA _ _ aD) (by rw [wr₁]; exact h.wr _ hdst _ _ (by decide) hd)
        fun s₂ m₂ g₂ rd₂ wr₂ => ?_
      refine k s₂ ?_ (fun r h1 _ h3 => by rw [g₂ r h3, o₁ r h1 h3]) (by rw [rd₂, rd₁])
        (by rw [wr₂, wr₁])
      funext x
      rw [m₂, m₁, g₁, setWidth32_64, write4_apply]
      simp only [opMem, hW, Op.val, hinc, hi32, Bool.false_eq_true, ite_false, hxr, cont, byte_xor_zero']
      split
      · rename_i hlt; rw [← Mem.readW_byte s.mem _ hlt, VG.Offset.add_add]
      · rfl
    | some p =>
      obtain ⟨l, off⟩ := p
      obtain hx' := hx l off hxr
      obtain eaX := h.ea l off (by omega_arith)
      obtain dX := h.disp l (off + 3) (by omega_arith)
      obtain nX := loc_ne c l
      simp only [List.append_assoc, List.singleton_append]
      refine wp_loadW c nS.1.symm nS.2.2.symm (by decide) (by omega_arith) eaS (alA _ _ aS)
        (h.rd _ _ _ (by decide) hs) fun s₁ g₁ o₁ m₁ rd₁ wr₁ => ?_
      refine wp_loadW c (a := A l + BitVec.ofNat 64 off) nX.2.1.symm nX.2.2.symm (by decide) (by omega_arith)
        (by rw [o₁ _ nX.1 nX.2.2]; exact eaX) (alA _ _ (aX l off hxr))
        (by rw [rd₁, wr₁]; exact h.rd _ _ _ (by decide) hx') fun s₂ g₂ o₂ m₂ rd₂ wr₂ => ?_
      refine wp_xor fun s₃ u₃ => ?_
      refine wp_storeW c (a := A o.dst + BitVec.ofNat 64 o.dOff) (by decide) nD.2.2.symm (by omega_arith)
        (by rw [u₃.other _ nD.1, o₂ _ nD.2.1 nD.2.2, o₁ _ nD.1 nD.2.2]; exact eaD) (alA _ _ aD)
        (by rw [u₃.wr, wr₂, wr₁]; exact h.wr _ hdst _ _ (by decide) hd) fun s₄ m₄ g₄ rd₄ wr₄ => ?_
      refine k s₄ ?_ (fun r h1 h2 h3 => by rw [g₄ r h3, u₃.other r h1, o₂ r h2 h3, o₁ r h1 h3])
        (by rw [rd₄, u₃.rd, rd₂, rd₁]) (by rw [wr₄, u₃.wr, wr₂, wr₁])
      funext x
      rw [m₄, u₃.mem, m₂, m₁, u₃.gpr, o₂ _ (by decide) (by decide), g₁, g₂, m₁, setWidth_xor32, write4_apply]
      simp only [opMem, hW, Op.val, hinc, hi32, Bool.false_eq_true, ite_false, hxr, cont]
      split
      · rename_i hlt; rw [byte_xor, ← Mem.readW_byte s.mem _ hlt, ← Mem.readW_byte s.mem _ hlt,
          VG.Offset.add_add, VG.Offset.add_add]
      · rfl

/-- Any operation: a copy or an XOR (`opCode_wp_plain`), or an increment
(`Counter.incBE_wp`). -/
theorem opCode_wp (c : Core) (w : Bool) {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} {o : Op}
    (ho : o.InBounds len) (hwa : WordAl o) (hal : ∀ l, Core.wordAt w l = true → (A l).toNat % 4 = 0)
    (hdst : o.dst ∈ ws) {s : State} (h : AreasOk c s len A ws) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.mem = opMem A o s.mem → Tmp s s' → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (c.opCode w o ++ is)) s Q := by
  have hd := ho.1
  obtain nD := loc_ne c o.dst
  have eb (n : Nat) : bytesAt s.mem (A o.dst + BitVec.ofNat 64 o.dOff) n =
      (List.range n).map fun i => cont A s.mem o.dst (o.dOff + i) := by
    simp only [bytesAt, cont, VG.Offset.add_add]
  have inc (w : Nat) (hw1 : 0 < w) (hw : w ≤ 16) (hW : o.width = w)
      (hval : ∀ t, o.val (cont A s.mem) t =
        (Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt s.mem (A o.dst + BitVec.ofNat 64 o.dOff) w) + 1) w).getD t 0) :
      WP isa (.block (Impl.Modes.RISCV64.incBE w (c.loc o.dst).1 ((c.loc o.dst).2 + o.dOff) ++ is)) s Q := by
    rw [hW] at hd
    refine Counter.incBE_wp nD.1 nD.2.1 hw (by have := h.disp o.dst (o.dOff + w - 1) (by omega_arith); omega_arith)
      (h.ea o.dst o.dOff (by omega_arith))
      (fun i hi => by rw [VG.Offset.add_add]; exact h.rd _ _ _ (by decide) (by omega_arith))
      (fun i hi => by rw [VG.Offset.add_add]; exact h.wr _ hdst _ _ (by decide) (by omega_arith))
      fun s' m' g' rd' wr' => k s' ?_ (fun r h1 h2 _ => g' r h1 h2) rd' wr'
    rw [m']
    funext x
    simp only [Counter.incBEMem, opMem, hW, hval]
  cases hinc : o.inc
  · cases hi32 : o.inc32
    · exact opCode_wp_plain c w ⟨hinc, hi32⟩ ho hwa hal hdst h k
    · -- GCM's `inc₃₂`.
      simp only [Core.opCode, hinc, hi32, Bool.false_eq_true, ite_false, ite_true, inc32At]
      exact inc 4 (by decide) (by decide) (by simp [Op.width, hinc, hi32]) fun t => by
        simp only [Op.val, hinc, hi32, Bool.false_eq_true, ite_false, ite_true, eb]
  · -- The 128-bit increment.
    simp only [Core.opCode, hinc, ite_true, incAt]
    exact inc 16 (by decide) (by decide) (by simp [Op.width, hinc]) fun t => by
      simp only [Op.val, hinc, ite_true, eb, Spec.Ctr.inc]

/-! ## Areas -/

/-- The regions of the areas `ws`. -/
def areaRegions (len : Loc → Nat) (A : Loc → Addr) (ws : List Loc) : List Region :=
  ws.map fun l => ⟨A l, len l⟩

theorem sub_self_add (p : Addr) {i : Nat} (hi : i < 2 ^ 64) : (p + BitVec.ofNat 64 i - p).toNat = i := by
  rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem contains_area {p : Addr} {n i : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) :
    (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 := by
  simp only [Region.Contains]; rw [sub_self_add p (by omega_arith)]; omega_arith

/-- A byte the destination of `o` writes is in its area. -/
theorem in_dst {len : Loc → Nat} {A : Loc → Addr} {o : Op} (ho : o.InBounds len) (hfit : len o.dst < 2 ^ 32)
    {x : Addr} (hx : (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat < o.width) :
    (⟨A o.dst, len o.dst⟩ : Region).Contains x 1 := by
  have := (VG.Offset.lt_iff x (A o.dst) (d := o.dOff) (n := o.width) (by have := ho.1; omega_arith)).mp hx
  simp only [Region.Contains]; have := ho.1; omega_arith

theorem opMem_frame {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} {o : Op} (ho : o.InBounds len)
    (hdst : o.dst ∈ ws) (hfit : ∀ l, len l < 2 ^ 32) (m : Mem) :
    Frame (areaRegions len A ws) m (opMem A o m) := by
  intro x hx
  simp only [opMem]
  rw [ite_eq_right fun h => hx _ (List.mem_map.mpr ⟨_, hdst, rfl⟩) (in_dst ho (hfit _) h)]

theorem opMem_cont {c : Core} {s : State} {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc}
    (h : AreasOk c s len A ws) {o : Op}
    (ho : o.InBounds len) (m : Mem) : Agree len (cont A (opMem A o m)) (o.apply (cont A m)) := by
  intro l i hi
  obtain hl := h.fit l
  simp only [cont, opMem, Op.apply]
  by_cases hd : l = o.dst
  · subst hd
    obtain e := VG.Offset.lt_iff (A o.dst + BitVec.ofNat 64 i) (A o.dst) (d := o.dOff) (n := o.width)
      (by have := ho.1; omega_arith)
    rw [sub_self_add _ (by omega_arith)] at e
    by_cases hc : o.dOff ≤ i ∧ i < o.dOff + o.width
    · rw [ite_eq_left (e.mpr hc), ite_eq_left ⟨rfl, hc⟩]
      congr 1
      rw [← VG.Offset.add_add_eq (A o.dst) (Nat.add_sub_cancel' hc.1), sub_self_add _ (by omega_arith)]
    · rw [ite_eq_right (fun h' => hc (e.mp h')), ite_eq_right (fun h' => hc h'.2)]
  · rw [ite_eq_right (fun h' => h.apart l o.dst hd _ (contains_area hi (by omega_arith)) (in_dst ho (h.fit _) h')),
      ite_eq_right (fun h' => hd h'.1)]

/-! ## Lists of operations -/

theorem opsCode_wp (c : Core) (w : Bool) {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc}
    (hal : ∀ l, Core.wordAt w l = true → (A l).toNat % 4 = 0) :
    ∀ {os : List Op}, (∀ o ∈ os, o.InBounds len ∧ o.dst ∈ ws) → (∀ o ∈ os, WordAl o) → ∀ {s : State},
    AreasOk c s len A ws → ∀ {is : List Instr} {Q : State → Prop},
    (∀ s', Agree len (cont A s'.mem) (applyOps os (cont A s.mem)) →
      Frame (areaRegions len A ws) s.mem s'.mem → Tmp s s' → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) →
    WP isa (.block (c.opsCode w os ++ is)) s Q
  | [], _, _, s, _, is, Q, k => by
    simpa [Core.opsCode] using k s (fun _ _ _ => rfl) (Frame.refl _ _) (fun _ _ _ _ => rfl) rfl rfl
  | o :: os, hb, ha, s, h, is, Q, k => by
    obtain ho := (hb o List.mem_cons_self)
    rw [show c.opsCode w (o :: os) ++ is = c.opCode w o ++ (c.opsCode w os ++ is) by
      simp [Core.opsCode, List.append_assoc]]
    refine opCode_wp c w ho.1 (ha o List.mem_cons_self) hal ho.2 h fun s₁ m₁ g₁ rd₁ wr₁ => ?_
    obtain h₁ : AreasOk c s₁ len A ws :=
      h.congr (fun l => g₁ _ (loc_ne c l).1 (loc_ne c l).2.1 (loc_ne c l).2.2) rd₁ wr₁
    refine opsCode_wp c w hal (fun o' ho' => hb o' (List.mem_cons_of_mem _ ho'))
      (fun o' ho' => ha o' (List.mem_cons_of_mem _ ho')) h₁
      fun s' a' f' g' rd' wr' => ?_
    refine k s' (fun l i hi => ?_) ?_ (fun r h1 h2 h3 => by rw [g' r h1 h2 h3, g₁ r h1 h2 h3])
      (by rw [rd', rd₁]) (by rw [wr', wr₁])
    · rw [a' l i hi, applyOps_cons]
      refine applyOps_agree (fun o' ho' => (hb o' (List.mem_cons_of_mem _ ho')).1)
        (fun l' i' hi' => ?_) l i hi
      rw [m₁]; exact opMem_cont h ho.1 _ l' i' hi'
    · rw [m₁] at f'; exact (opMem_frame ho.1 ho.2 h.fit _).trans f'

end VG.Proof.Modes.RISCV64

end

end


/-!
# One step of a mode on RISCV64

`body_wp`: one run of the loop's body (`Core.body`) takes the invariant
(`Inv`) from `j` steps done to `j + 1`. After `j` steps, the data are the
outputs of the mode's step function `F` on the first `j` input steps
followed by the other inputs, the chaining value is `F`'s after them, the
data pointer and the steps left are in `s2` and `s3`, and the key is
ready. The step's three areas (`areas`) are the data's step `j`, the
chaining value's slots and the first `bl` bytes of the core's buffer;
`pre` and `post` are `opsCode_wp`, the block cipher `crypt_wp`, which
enciphers the buffer's bytes as `ciphB` (`BufCipher`), and
`ComputesB M L bl ciphB F` relates them to `F`.

A step takes `d` from `s3`, which holds `n₀ - d j` after `j` steps: one
block a step (`body_wp`, `loop_wp`: `bl = 4 bw`, `d = 1`, `n₀ = n`), or a
group of `2 ^ lg` blocks (`bodyWide_wp`, `loopWide_wp`: `bl = 4 bw 2 ^ lg`,
`d = 2 ^ lg`, `n = n₀ / d`), the loop going on while `t0 = s3 >> lg` is
not zero. The key is ready for the regions `W`, which hold the data and
the frame.
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Modes VG.Impl.Modes.RISCV64
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The areas' lengths: a step's data, a block of `4 bw` bytes, and the
buffer's first `bl` bytes. -/
def lens (c : Core) (st bl : Nat) : Loc → Nat
  | .dat => st
  | .chn => 4 * c.bw
  | .buf => bl

/-- The areas' addresses, for step `j` of the data at `D`. -/
def areas (c : Core) (B D : Addr) (st j : Nat) : Loc → Addr
  | .dat => D + BitVec.ofNat 64 (st * j)
  | .chn => slotA B Core.chnSlot
  | .buf => slotA B c.buf

/-- The data. -/
abbrev dataRegion (D : Addr) (st n : Nat) : Region := ⟨D, st * n⟩

/-- The data of step `j`. -/
abbrev datRegion (D : Addr) (st j : Nat) : Region := ⟨D + BitVec.ofNat 64 (st * j), st⟩

/-- The chaining value's slots. -/
abbrev chnRegion (c : Core) (B : Addr) : Region := ⟨slotA B Core.chnSlot, 4 * c.bw⟩

/-- The whole frame. -/
abbrev scrRegion (c : Core) (B : Addr) : Region := ⟨B, 8 * c.total⟩

/-- What a run keeps fixed: the frame at `B`, the data at `D` of `n`
steps of `st` bytes, the buffer's `bl` bytes a step uses, the regions `W`
the key is ready for, the count `n₀ - d j` in `s3`, and the layout. -/
structure Fixed (c : Core) (s₀ : State) (B D : Addr) (n st bl : Nat) (W : List Region) (n₀ d : Nat) :
    Prop where
  scr : ScrIn s₀ B c.total
  dataW : ∀ o w, 0 < w → o + w ≤ st * n → InRegions s₀.wr (D + BitVec.ofNat 64 o) w
  dataFit : D.toNat + st * n ≤ 2 ^ 64
  dataScr : Region.Disjoint (dataRegion D st n) (scrRegion c B)
  nFit : n₀ < 2 ^ 64
  cnt : d * n ≤ n₀
  dec : d ≤ 2048
  step : 0 < st ∧ st ≤ 2032
  buf : 0 < bl ∧ bl ≤ 4 * c.bw * c.G
  dataIn : ∃ r ∈ W, Region.Sub (dataRegion D st n) r
  scrIn : scrRegion c B ∈ W
  layout : Layout c

/-- Every access within a writable region of the data is permitted. -/
theorem dataW_of_mem {wr : List Region} {D : Addr} {len : Nat} (hm : (⟨D, len⟩ : Region) ∈ wr)
    (hD : D.toNat + len ≤ 2 ^ 64) {o w : Nat} (hw : 0 < w) (ho : o + w ≤ len) :
    InRegions wr (D + BitVec.ofNat 64 o) w :=
  ⟨_, hm, VG.Offset.contains_base _ (by omega_using [ho]) (by omega_using [hD, ho, hw])⟩

/-- The regions a mode writes: the data and the frame. -/
abbrev wrs (c : Core) (B D : Addr) (n st : Nat) : List Region := [dataRegion D st n, scrRegion c B]

/-- The regions a run changes. -/
abbrev big (c : Core) (B D : Addr) (n st : Nat) : List Region :=
  [coreRegion c B, chnRegion c B, dataRegion D st n]

/-- The invariant after `j` of the `n` steps from the inputs `xs` and the
chaining value `c0`. -/
structure Inv (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n st : Nat) (W : List Region) (n₀ d : Nat)
    (k : cs.Key) (F : StepFn) (c0 : List Byte) (xs : List (List Byte)) (j : Nat) (s : State) : Prop where
  b : s.gpr sb = B
  keep : ∀ r ∈ kept, r ≠ .s3 → r ≠ .s2 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.gpr .s2 = D + BitVec.ofNat 64 (st * j)
  np : s.gpr .s3 = BitVec.ofNat 64 (n₀ - d * j)
  ready : cs.Ready s B W k
  data : chunksAt st s.mem D n = (run F c0 (xs.take j)).1 ++ xs.drop j
  chn : bytesAt s.mem (slotA B Core.chnSlot) (4 * c.bw) = (run F c0 (xs.take j)).2
  frame : Frame (big c B D n st) s₀.mem s.mem

/-- After all `n` steps from the state `s₂`, by whatever loops: the data are
`F`'s outputs on the inputs `xs` from `c0`, the chaining value `F`'s last,
the frame's base and the registers the caller expects kept, and memory
changed only in `big`. -/
structure Done (s₂ : State) (B D : Addr) (n st : Nat) (F : StepFn) (c0 : List Byte) (xs : List (List Byte))
    (s : State) : Prop where
  b : s.gpr sb = B
  keep : ∀ r ∈ kept, r ≠ .s3 → r ≠ .s2 → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  data : chunksAt st s.mem D n = (run F c0 xs).1
  chn : bytesAt s.mem (slotA B Core.chnSlot) (4 * c.bw) = (run F c0 xs).2
  frame : Frame (big c B D n st) s₂.mem s.mem

theorem Inv.done {cs : CoreSpec c} {s₀ : State} {B D : Addr} {n st : Nat} {W : List Region} {n₀ d : Nat}
    {k : cs.Key} {F : StepFn} {c0 : List Byte} {xs : List (List Byte)} {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs n s) (hxs : xs.length = n) : Done (c := c) s₀ B D n st F c0 xs s := by
  refine ⟨hI.b, hI.keep, hI.rd, hI.wr, ?_, ?_, hI.frame⟩
  · rw [hI.data, List.take_of_length_le (by omega_using [hxs]), List.drop_of_length_le (by omega_using [hxs]), List.append_nil]
  · rw [hI.chn, List.take_of_length_le (by omega_using [hxs])]

/-! ## Areas -/

theorem rd_agree {len : Loc → Nat} {a a' : Areas} (h : Agree len a a') {l : Loc} {n : Nat} (hn : n ≤ len l) :
    rd a l n = rd a' l n :=
  List.map_congr_left fun i hi => h l i (by have := List.mem_range.mp hi; omega_using [hn, this])

theorem cryptBuf_agree {len : Loc → Nat} {n : Nat} (hn : n ≤ len .buf) (ciph : Spec.Cbc.Cipher) {a a' : Areas}
    (h : Agree len a a') : Agree len (cryptBuf n ciph a) (cryptBuf n ciph a') := by
  intro l i hi
  simp only [cryptBuf]
  split
  · rename_i hl; subst hl; rw [rd_agree h hn]
  · exact h l i hi

theorem Agree.trans {len : Loc → Nat} {a b c : Areas} (h₁ : Agree len a b) (h₂ : Agree len b c) :
    Agree len a c := fun l i hi => (h₁ l i hi).trans (h₂ l i hi)

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.savedSlot, coreSlot]); omega_arith))

theorem slot_sub {B : Addr} {total d n : Nat} (h : d + n ≤ 8 * total) :
    Region.Sub ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B, 8 * total⟩ :=
  VG.Offset.sub_base _ h

/-- The buffer's bytes a step uses, within the frame's lowest region. -/
theorem Fixed.buf_le {s₀ : State} {B D : Addr} {n st bl : Nat} {W : List Region} {n₀ d : Nat}
    (hF : Fixed c s₀ B D n st bl W n₀ d) : 8 * c.buf + bl ≤ min (8 * c.total) 2032 :=
  Nat.le_min.mpr ⟨Nat.le_trans (Nat.add_le_add_left hF.buf.2 _) hF.layout.buf_le,
    Nat.le_trans (Nat.add_le_add_left hF.buf.2 _) hF.layout.disp⟩

/-- Every byte of the areas at step `j`, as the code addresses them. -/
theorem areasOk {s₀ s : State} {B D : Addr} {n st bl : Nat} {W : List Region} {n₀ d j : Nat}
    (hF : Fixed c s₀ B D n st bl W n₀ d) (hj : j < n)
    (hb : s.gpr sb = B) (hdp : s.gpr .s2 = D + BitVec.ofNat 64 (st * j)) (hwr : s.wr = s₀.wr) :
    AreasOk c s (lens c st bl) (areas c B D st j) allLocs := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hge := hL.buf_ge
  have hbuf := hL.buf_le
  have hdisp := hL.disp
  have hst := hF.step
  have hD := hF.dataFit
  obtain hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hb4 : 8 * c.buf + bl ≤ min (8 * c.total) 2032 := hF.buf_le
  obtain hW : ∀ l off w, 0 < w → off + w ≤ lens c st bl l → InRegions s.wr (areas c B D st j l + BitVec.ofNat 64 off) w := by
    intro l off w hw0 ho
    rw [hwr]
    cases l
    · simp only [lens, areas] at ho ⊢
      rw [VG.Offset.add_add]; exact hF.dataW _ _ hw0 (by omega_using [hjn, ho])
    · simp only [lens, areas] at ho ⊢
      rw [VG.Offset.add_add]; exact hF.scr.low _ _ (by have := hge; simp only [coreSlot] at this; slot_omega)
    · simp only [lens, areas] at ho ⊢
      rw [VG.Offset.add_add]; exact hF.scr.low _ _ (by omega_using [hb4, ho])
  refine ⟨fun l off ho => ?_, fun l off ho => ?_, fun l off w hw0 ho => ?_, fun l _ off w hw0 ho => hW l off w hw0 ho,
    fun l l' hne => ?_, fun l => ?_⟩
  · cases l
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hdp, Nat.zero_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
  · cases l
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hst]
    · simp only [Core.loc, lens] at ho ⊢; slot_omega
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hb4, hdisp]
  · obtain ⟨r, hr, hc⟩ := hW l off w hw0 ho
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have dD : ∀ d m, d + m ≤ 8 * c.total →
        Region.Disjoint ⟨D + BitVec.ofNat 64 (st * j), st⟩ ⟨B + BitVec.ofNat 64 d, m⟩ :=
      fun d m h => (hF.dataScr.sub_left (VG.Offset.sub_base _ hjn)).sub_right (slot_sub h)
    have h6 : coreSlot = 6 := rfl
    obtain hb8 : 8 * c.buf + bl ≤ 8 * c.total := Nat.le_trans hb4 (Nat.min_le_left _ _)
    obtain hc : 8 * Core.chnSlot + 4 * c.bw ≤ 8 * c.buf := by
      simp only [Core.chnSlot]; omega_using [hge, h6, hbw]
    obtain dCB : Region.Disjoint ⟨slotA B Core.chnSlot, 4 * c.bw⟩ ⟨slotA B c.buf, bl⟩ :=
      VG.Offset.disjoint _ (.inl hc) (by omega_using [hc, hfit, hb8]) (by omega_using [hfit, hb8])
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [lens, areas]
    · exact dD _ _ (by omega_using [hc, hb8])
    · exact dD _ _ hb8
    · exact (dD _ _ (by omega_using [hc, hb8])).symm
    · exact dCB
    · exact (dD _ _ hb8).symm
    · exact dCB.symm
  · cases l <;> simp only [lens] <;> omega_using [hst, hbw, hb4]

/-! ## The regions of a step -/

/-- The regions a step's operations and core change: the data of the step,
the core's slots and the chaining value. -/
abbrev fine (c : Core) (B D : Addr) (st j : Nat) : List Region :=
  [datRegion D st j, coreRegion c B, chnRegion c B]

/-- What a step needs of the regions. -/
structure Regs (c : Core) (B D : Addr) (n st bl : Nat) (W : List Region) (j : Nat) : Prop where
  areasFine : ∀ r ∈ areaRegions (lens c st bl) (areas c B D st j) allLocs, ∃ r' ∈ fine c B D st j, Region.Sub r r'
  areasW : ∀ r ∈ areaRegions (lens c st bl) (areas c B D st j) allLocs, ∃ r' ∈ W, Region.Sub r r'
  areasCore : ∀ r ∈ areaRegions (lens c st bl) (areas c B D st j) allLocs,
    Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)
  chnCore : Region.Disjoint (chnRegion c B) (coreRegion c B)
  datCore : Region.Disjoint (datRegion D st j) (coreRegion c B)
  datData : Region.Sub (datRegion D st j) (dataRegion D st n)
  dataCore : Region.Disjoint (dataRegion D st n) (coreRegion c B)
  dataChn : Region.Disjoint (dataRegion D st n) (chnRegion c B)
  toBig : ∀ r ∈ fine c B D st j, ∃ r' ∈ big c B D n st, Region.Sub r r'

theorem regs {s₀ : State} {B D : Addr} {n st bl : Nat} {W : List Region} {n₀ d j : Nat}
    (hF : Fixed c s₀ B D n st bl W n₀ d) (hj : j < n) :
    Regs c B D n st bl W j := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hge := hL.buf_ge
  have hbuf := hL.buf_le
  have hG := hL.G_pos
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  obtain hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain subDat : Region.Sub (datRegion D st j) (dataRegion D st n) := VG.Offset.sub_base _ hjn
  obtain hb4 : 8 * c.buf + 4 * c.bw ≤ 8 * c.total :=
    Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hG) _) hbuf
  obtain hbl : 8 * c.buf + bl ≤ 8 * c.total := Nat.le_trans hF.buf_le (Nat.min_le_left _ _)
  have h6 : coreSlot = 6 := rfl
  obtain subBuf : Region.Sub ⟨slotA B c.buf, bl⟩ (coreRegion c B) :=
    VG.Offset.sub _ (by omega_using [hge, h6]) (by omega_using [hge, hbl, h6])
  obtain subBlk : Region.Sub ⟨slotA B c.buf, bl⟩ (blkRegion c B) := Region.sub_prefix hF.buf.2
  obtain chnScr : Region.Sub (chnRegion c B) (scrRegion c B) :=
    VG.Offset.sub_base _ (by simp only [Core.chnSlot]; omega_using [hge, hb4, h6, hbw])
  obtain coreScr : Region.Sub (coreRegion c B) (scrRegion c B) :=
    VG.Offset.sub_base _ (by omega_using [hge, hb4, h6])
  obtain chnCore : Region.Disjoint (chnRegion c B) (coreRegion c B) :=
    VG.Offset.disjoint _ (.inl (by simp only [Core.chnSlot]; omega_using [hbw, h6]))
      (by simp only [Core.chnSlot]; omega_using [hfit, hge, hb4, h6, hbw]) (by omega_using [hfit, hge, hb4, h6])
  obtain datCore : Region.Disjoint (datRegion D st j) (coreRegion c B) :=
    (hF.dataScr.sub_left subDat).sub_right coreScr
  obtain m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  obtain m2 : ∀ {a b c' : Region} {l : List Region}, c' ∈ a :: b :: c' :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, chnCore, datCore, subDat,
    hF.dataScr.sub_right coreScr, hF.dataScr.sub_right chnScr, fun r hr => ?_⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, m2, fun _ h => h⟩
    · exact ⟨_, m1, subBuf⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨rD, hrD, sD⟩ := hF.dataIn
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, hrD, fun x hx => sD x (subDat x hx)⟩
    · exact ⟨_, hF.scrIn, chnScr⟩
    · exact ⟨_, hF.scrIn, fun x hx => coreScr x (subBuf x hx)⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl datCore.symm
    · exact .inl chnCore.symm
    · exact .inr subBlk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, m2, subDat⟩
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, m1, fun _ h => h⟩

/-! ## The stages of a step -/

/-- In the middle of a step from `s`: the areas agree with `a`, the key is
ready, the mode's registers are kept, and memory has changed only in `fine`
since `s`. -/
structure Mid (cs : CoreSpec c) (s₀ : State) (B D : Addr) (st bl : Nat) (W : List Region) (j : Nat)
    (k : cs.Key) (s : State) (a : Areas) (s' : State) : Prop where
  b : s'.gpr sb = B
  kept : ∀ r ∈ kept, s'.gpr r = s.gpr r
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  ready : cs.Ready s' B W k
  agree : Agree (lens c st bl) (cont (areas c B D st j) s'.mem) a
  frame : Frame (fine c B D st j) s.mem s'.mem

theorem mem_kept {r : Reg} (h : r = .a0 ∨ r = .s1 ∨ r = .s3 ∨ r = .s2) : r ∈ kept := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- The operations' registers are not kept. -/
theorem kept_ne : ∀ r ∈ kept, r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 := by decide

/-- What the operations' words need, when the areas `Core.wordAt w` names
are accessed a word at a time: the mode's words at multiples of 4
(`WordAl`), the frame's base a multiple of 4, and when `w`, the data's
address and its step too. -/
structure WordOk (c : Core) (w : Bool) (M : Mode) (B D : Addr) (st : Nat) : Prop where
  pre : ∀ o ∈ M.pre, WordAl o
  post : ∀ o ∈ M.post, WordAl o
  base : B.toNat % 4 = 0
  dat : w = true → D.toNat % 4 = 0 ∧ st % 4 = 0

theorem areas_al {w : Bool} {M : Mode} {B D : Addr} {st : Nat} (h : WordOk c w M B D st) (j : Nat) :
    ∀ l, Core.wordAt w l = true → (areas c B D st j l).toNat % 4 = 0
  | .dat, hw => by
    obtain ⟨hD, hs⟩ := h.dat (by simpa [Core.wordAt] using hw)
    exact al4 hD (by rw [Nat.mul_mod, hs, Nat.zero_mul, Nat.zero_mod])
  | .chn, _ => al4 h.base (by simp [Core.chnSlot])
  | .buf, _ => al4 h.base (by omega_using [])

/-- The operations' hypotheses, for `opsCode_wp`. -/
theorem ops_ok {len : Loc → Nat} {os : List Op} (h : ∀ o ∈ os, o.InBounds len) :
    ∀ o ∈ os, o.InBounds len ∧ o.dst ∈ allLocs :=
  fun o ho => ⟨h o ho, mem_allLocs _⟩

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ d : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} {w : Bool}

theorem pre_wp (hF : Fixed c s₀ B D n st bl W n₀ d) (hw : WordOk c w M B D st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st bl)) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s) :
    WP isa (.block (c.opsCode w M.pre)) s
      (Mid cs s₀ B D st bl W j k s (applyOps M.pre (cont (areas c B D st j) s.mem))) := by
  obtain hR := regs hF hj
  obtain hA : AreasOk c s (lens c st bl) (areas c B D st j) allLocs := areasOk hF hj hI.b hI.dp hI.wr
  rw [← List.append_nil (c.opsCode w M.pre)]
  refine WP.of_syms (opsCode_wp c w (areas_al hw j) (ops_ok hpre) hw.pre hA fun s₂ a₂ f₂ g₂ rd₂ wr₂ => WP.block_nil fun sy₂ => ?_)
  exact ⟨by rw [g₂ _ (by decide) (by decide) (by decide)]; exact hI.b,
    fun r hr => g₂ r (kept_ne r hr).1 (kept_ne r hr).2.1 (kept_ne r hr).2.2,
    by rw [rd₂, hI.rd], by rw [wr₂, hI.wr],
    cs.ready_frame hI.ready (fun r hr _ _ _ _ => g₂ r (kept_ne r hr).1 (kept_ne r hr).2.1 (kept_ne r hr).2.2) rd₂ wr₂ sy₂ f₂
      hR.areasW hR.areasCore, a₂,
    f₂.sub hR.areasFine⟩

end

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem blkAddr_zero (c : Core) (B : Addr) : blkAddr c B 0 = slotA B c.buf := by
  simp only [blkAddr, Nat.mul_zero, BitVec.add_zero]

/-- The core's block cipher, as the cipher `ciphB` on the buffer's first `bl`
bytes: what `crypt_wp` gives of the buffer's blocks determines them. -/
def BufCipher (c : Core) (ciph ciphB : Spec.Cbc.Cipher) (bl : Nat) : Prop :=
  ∀ (B : Addr) (m m' : Mem), (∀ j < c.G, bytesAt m' (blkAddr c B j) (4 * c.bw) =
    ciph (bytesAt m (blkAddr c B j) (4 * c.bw))) →
    bytesAt m' (slotA B c.buf) bl = ciphB (bytesAt m (slotA B c.buf) bl)

/-- One block: the cipher on the buffer's first block. -/
theorem bufCipher_one (hG : 0 < c.G) (ciph : Spec.Cbc.Cipher) : BufCipher c ciph ciph (4 * c.bw) :=
  fun B m m' h => by have e := h 0 hG; rwa [blkAddr_zero] at e

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ d : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} {w : Bool}

theorem crypt_step (hF : Fixed c s₀ B D n st bl W n₀ d) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB bl) {j : Nat} (hj : j < n) {s s₂ : State} {a : Areas}
    (hm : Mid cs s₀ B D st bl W j k s a s₂) :
    WP isa c.crypt s₂ (Mid cs s₀ B D st bl W j k s (cryptBuf bl ciphB a)) := by
  obtain hR := regs hF hj
  have hst := hF.step
  obtain hbw : c.bw ≤ 4 := by rcases hF.layout.bw with h | h <;> omega_using [h]
  refine WP.mono (cs.crypt_wp hm.b (hF.scr.congr hm.wr) hm.ready)
    fun s₃ ⟨b₃, kept₃, ready₃, f₃, enc₃, rd₃, wr₃⟩ => ?_
  refine ⟨b₃, fun r hr => by rw [kept₃ r hr, hm.kept r hr], by rw [rd₃, hm.rd], by rw [wr₃, hm.wr], ready₃, ?_,
    hm.frame.trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)⟩
  refine Agree.trans (b := cryptBuf bl ciphB (cont (areas c B D st j) s₂.mem)) ?_
    (cryptBuf_agree (by simp [lens]) _ hm.agree)
  intro l i hi
  cases l
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := datRegion D st j) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.datCore) (by show st ≤ 2 ^ 64; omega_using [hst]) hi
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := chnRegion c B) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.chnCore) (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw]) hi
  · simp only [lens] at hi
    obtain e := hB B s₂.mem s₃.mem enc₃
    simp only [cryptBuf, cont, areas, ite_true]
    rw [← bytesAt_getD s₃.mem (slotA B c.buf) hi, e]
    rfl

end

theorem chunksAt_getElem {L : Nat} {m : Mem} {p : Addr} {n j : Nat} (hj : j < n) :
    (chunksAt L m p n)[j]'(by rw [chunksAt_length]; exact hj) = bytesAt m (p + BitVec.ofNat 64 (L * j)) L := by
  simp [chunksAt]

/-- Input step `j`, from the invariant. -/
theorem Inv.input {cs : CoreSpec c} {s₀ : State} {B D : Addr} {n st : Nat} {W : List Region} {n₀ d : Nat}
    {k : cs.Key} {F : StepFn} {c0 : List Byte} {xs : List (List Byte)} {j : Nat} {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s) (hxs : xs.length = n) (hj : j < n) :
    bytesAt s.mem (D + BitVec.ofNat 64 (st * j)) st = xs[j]'(by omega_using [hxs, hj]) := by
  obtain hl : (run F c0 (xs.take j)).1.length = j := by rw [run_length, List.length_take]; omega_using [hxs, hj]
  obtain e := congrArg (·[j]?) hI.data
  simp only [List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self, List.getElem?_drop, Nat.add_zero] at e
  rw [List.getElem?_eq_getElem (by rw [chunksAt_length]; exact hj), List.getElem?_eq_getElem (by omega_using [hxs, hj]),
    chunksAt_getElem hj] at e
  exact Option.some.inj e

theorem ofNat_sub64 {a b : Nat} (h : b ≤ a) : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := Nat.mod_le a (2 ^ 64)
  by_cases hb : b < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hb]
    by_cases ha : a < 2 ^ 64
    · rw [Nat.mod_eq_of_lt ha]; omega_using [h, hb]
    · omega_using [h, hb]
  · omega_using [h]

/-- What the instructions `ex` after a step's count do: change only `t0`,
establishing `X`. -/
def ExOk (ex : List Instr) (X : State → Prop) : Prop :=
  ∀ t, WP isa (.block ex) t fun t' => (∀ r, r ≠ .t0 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧
    t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.syms = t.syms ∧ X t'

theorem exOk_nil : ExOk [] fun _ => True := fun _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, trivial⟩

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ d : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} {w : Bool}

theorem post_wp (hF : Fixed c s₀ B D n st bl W n₀ d) (hw : WordOk c w M B D st) (hM : M.step = st)
    {ciphB : Spec.Cbc.Cipher}
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c st bl)) (hcomp : ComputesB M (4 * c.bw) bl ciphB F)
    {ex : List Instr} {X : State → Prop} (hex : ExOk ex X)
    (hxs : xs.length = n) {j : Nat} (hj : j < n) {s s₃ : State} (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s)
    (hm : Mid cs s₀ B D st bl W j k s (cryptBuf bl ciphB
      (applyOps M.pre (cont (areas c B D st j) s.mem))) s₃) :
    WP isa (.block (c.opsCode w M.post ++ (.addi .s2 .s2 (M.step : Int) :: .addi .s3 .s3 (-(d : Int)) :: ex))) s₃
      fun s' => Inv cs s₀ B D n st W n₀ d k F c0 xs (j + 1) s' ∧ X s' := by
  obtain hR := regs hF hj
  have hL := hF.layout
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hst := hF.step
  have hDf := hF.dataFit
  obtain hcnt : d * j + d ≤ n₀ := by rw [← Nat.mul_succ]; exact Nat.le_trans (Nat.mul_le_mul_left _ hj) hF.cnt
  obtain hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain k₃ : ∀ r, r = .a0 ∨ r = .s1 ∨ r = .s3 ∨ r = .s2 → s₃.gpr r = s.gpr r :=
    fun r hr => hm.kept r (mem_kept hr)
  obtain dp₃ : s₃.gpr .s2 = D + BitVec.ofNat 64 (st * j) := by rw [k₃ _ (by simp), hI.dp]
  obtain np₃ : s₃.gpr .s3 = BitVec.ofNat 64 (n₀ - d * j) := by rw [k₃ _ (by simp), hI.np]
  obtain hA : AreasOk c s₃ (lens c st bl) (areas c B D st j) allLocs := areasOk hF hj hm.b dp₃ hm.wr
  refine WP.of_syms (opsCode_wp c w (areas_al hw j) (ops_ok hpost) hw.post hA fun s₅ a₅ f₅ g₅ rd₅ wr₅ => ?_)
  refine wp_addi (by omega_using [hM, hst]) fun s₆ u₆ =>
    wp_subi hF.dec fun s₇ u₇ => WP.mono (hex s₇) fun s₈ ⟨g₈, m₈, rd₈, wr₈, sy₈', x₈⟩ sy₈ => ⟨?_, x₈⟩
  obtain g₇ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .s3 → r ≠ .s2 → s₈.gpr r = s₃.gpr r :=
    fun r h1 h2 h0 h3 h4 => by rw [g₈ r h1, u₇.other r h3, u₆.other r h4, g₅ r h1 h2 h0]
  obtain m₇ : s₈.mem = s₅.mem := by rw [m₈, u₇.mem, u₆.mem]
  obtain s2₅ : s₅.gpr .s2 = D + BitVec.ofNat 64 (st * j) := by rw [g₅ _ (by decide) (by decide) (by decide), dp₃]
  obtain s3₅ : s₅.gpr .s3 = BitVec.ofNat 64 (n₀ - d * j) := by rw [g₅ _ (by decide) (by decide) (by decide), np₃]
  have sy₇ : s₈.syms = s₃.syms := sy₈
  -- The step's outputs.
  let A := areas c B D st j
  obtain hstep : Agree (lens c st bl) (cont A s₅.mem) (stepA M bl ciphB (cont A s.mem)) :=
    Agree.trans a₅ (applyOps_agree hpost hm.agree)
  obtain ⟨hc1, hc2⟩ := hcomp (cont A s.mem)
  rw [hM] at hc1 hc2
  obtain xj : rd (cont A s.mem) .dat st = xs[j]'(by omega_using [hxs, hj]) := hI.input hxs hj
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 (xs.take j)).2 := hI.chn
  rw [xj, cj] at hc1 hc2
  obtain out₅ : bytesAt s₅.mem (D + BitVec.ofNat 64 (st * j)) st =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1 := by
    rw [← hc1]; exact rd_agree hstep (l := .dat) (Nat.le_refl _)
  obtain chn₅ : bytesAt s₅.mem (slotA B Core.chnSlot) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2 := by
    rw [← hc2]; exact rd_agree hstep (l := .chn) (Nat.le_refl _)
  obtain all : Frame (fine c B D st j) s.mem s₅.mem := hm.frame.trans (f₅.sub hR.areasFine)
  obtain hrun : run F c0 (xs.take (j + 1)) = ((run F c0 (xs.take j)).1 ++
      [(F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1],
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega_using [hxs, hj]), Option.toList_some, run_snoc]
  refine ⟨by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm.b,
    fun r hr h30 h31 => by
      rw [g₇ r (kept_ne r hr).1 (kept_ne r hr).2.1 (kept_ne r hr).2.2 h30 h31, hm.kept r hr, hI.keep r hr h30 h31],
    by rw [rd₈, u₇.rd, u₆.rd, rd₅, hm.rd], by rw [wr₈, u₇.wr, u₆.wr, wr₅, hm.wr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₈ _ (by decide), u₇.other _ (by decide), u₆.gpr, s2₅, VG.Offset.add_add, hM, Nat.mul_succ]
  · rw [g₈ _ (by decide), u₇.gpr, u₆.other _ (by decide), s3₅, ofNat_sub64 (by omega_using [hcnt]), Nat.mul_succ]
    congr 1; omega_using [hcnt]
  · exact cs.ready_frame hm.ready (fun r hr _ h31 h30 _ => g₇ r (kept_ne r hr).1 (kept_ne r hr).2.1 (kept_ne r hr).2.2 h30 h31)
      (by rw [rd₈, u₇.rd, u₆.rd, rd₅]) (by rw [wr₈, u₇.wr, u₆.wr, wr₅]) sy₇ (by rw [m₇]; exact f₅)
      hR.areasW hR.areasCore
  · rw [m₇, chunksAt_set (j := j) (fun i hi hout => ?_), hI.data, out₅, run_set F c0 (by omega_using [hxs, hj])]
    refine all _ fun r hr hcon => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [Region.Contains] at hcon
      obtain e := (VG.Offset.lt_iff (D + BitVec.ofNat 64 i) D (d := st * j) (n := st)
        (by omega_using [hDf, hjn])).mp (by omega_using [hcon])
      rw [sub_self_add _ (by omega_using [hDf, hi])] at e
      omega_using [hout, e]
    · exact hR.dataCore _ (contains_area hi (by omega_using [hDf])) hcon
    · exact hR.dataChn _ (contains_area hi (by omega_using [hDf])) hcon
  · rw [m₇, chn₅, hrun]
  · rw [m₇]; exact hI.frame.trans (all.sub hR.toBig)

/-! ## The step and the loop -/

/-- A step: `pre`, the core, `post`, the count, and `ex`. -/
theorem step_wp (hF : Fixed c s₀ B D n st bl W n₀ d) (hw : WordOk c w M B D st) (hM : M.step = st)
    {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB bl)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st bl)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st bl))
    (hcomp : ComputesB M (4 * c.bw) bl ciphB F) {ex : List Instr} {X : State → Prop} (hex : ExOk ex X)
    (hxs : xs.length = n) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s) :
    WP isa (.seq (.block (c.opsCode w M.pre)) (.seq c.crypt
      (.block (c.opsCode w M.post ++ (.addi .s2 .s2 (M.step : Int) :: .addi .s3 .s3 (-(d : Int)) :: ex))))) s
      fun s' => Inv cs s₀ B D n st W n₀ d k F c0 xs (j + 1) s' ∧ X s' :=
  WP.seq (WP.mono (pre_wp cs hF hw hpre hj hI) fun _ h₂ =>
    WP.seq (WP.mono (crypt_step cs hF hB hj h₂) fun _ h₃ => post_wp cs hF hw hM hpost hcomp hex hxs hj hI h₃))

theorem body_wp (hF : Fixed c s₀ B D n st (4 * c.bw) W n₀ 1) (hw : WordOk c w M B D st) (hM : M.step = st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st (4 * c.bw)))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c st (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = n) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ 1 k F c0 xs j s) :
    WP isa (c.body w M) s (Inv cs s₀ B D n st W n₀ 1 k F c0 xs (j + 1)) :=
  WP.mono (step_wp cs hF hw hM (bufCipher_one hF.layout.G_pos _) hpre hpost hcomp exOk_nil hxs hj hI) fun _ h => h.1

theorem loop_wp (hF : Fixed c s₀ B D n st (4 * c.bw) W n 1) (hw : WordOk c w M B D st) (hM : M.step = st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st (4 * c.bw)))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c st (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = n) {s : State}
    (hI : Inv cs s₀ B D n st W n 1 k F c0 xs 0 s) :
    WP isa (.ite (.zero .s3) (.block []) (.loop (c.body w M) (.nonzero .s3))) s
      (Inv cs s₀ B D n st W n 1 k F c0 xs n) := by
  have hn64 := hF.nFit
  obtain ev : ∀ {j t}, j ≤ n → t.gpr .s3 = BitVec.ofNat 64 (n - 1 * j) →
      isa.eval (.nonzero .s3) t = some (decide (n - 1 * j ≠ 0)) := fun hj h =>
    eval_nonzero_ofNat _ _ (by omega_using [hn64, hj]) h
  by_cases hn : n = 0
  · subst hn
    exact WP.ite true (by rw [eval_zero_ofNat s .s3 (by decide) hI.np]; rfl) (fun _ => WP.block_nil hI)
      (fun h => by cases h)
  refine WP.ite false (by rw [eval_zero_ofNat s .s3 (by omega_using [hn64]) hI.np]; simp [hn])
    (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := c.body w M) (c := .nonzero .s3) (Q := Inv cs s₀ B D n st W n 1 k F c0 xs n)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ Inv cs s₀ B D n st W n 1 k F c0 xs j t)
    ?_ n s ⟨0, by omega_using [], by omega_using [hn], hI⟩
  rintro _ t ⟨j, rfl, hj, h⟩
  refine WP.mono (body_wp cs hF hw hM hpre hpost hcomp hxs hj h) fun t' h' => ?_
  obtain e := ev (j := j + 1) (by omega_using [hj]) h'.np
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [e]; simp [he], he ▸ h'⟩
  · right; exact ⟨by rw [e]; simp; omega_using [hj, he], n - (j + 1), by omega_using [hj, he], j + 1, rfl,
      by omega_using [hj, he], h'⟩

end

/-! ## A group of blocks a step -/

/-- `t0` is `s3 >> lg`: whether a group of `2 ^ lg` blocks is left. -/
def GroupsLeft (lg : Nat) (t : State) : Prop := t.gpr .t0 = t.gpr .s3 >>> lg

theorem exOk_groupsLeft {lg : Nat} (h : lg < 64) : ExOk [Core.groupsLeft lg] (GroupsLeft lg) :=
  fun t => WP.of_syms (wp_srl h fun t' u => WP.block_nil fun sy =>
    ⟨fun r hr => u.other r hr, u.mem, u.rd, u.wr, sy, by
      simp only [GroupsLeft, u.gpr, u.other _ (show Reg.s3 ≠ .t0 by decide)]⟩)

theorem ushiftRight_ofNat {x lg : Nat} (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x >>> lg = BitVec.ofNat 64 (x / 2 ^ lg) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} {w : Bool}

/-- The steps of `2 ^ lg` blocks, `n = n₀ / 2 ^ lg` of them. -/
theorem loopWide_wp {lg : Nat} (hlg : lg < 64) (hF : Fixed c s₀ B D n st bl W n₀ (2 ^ lg))
    (hw : WordOk c w M B D st)
    (hn : n = n₀ / 2 ^ lg) (hM : M.step = st) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB bl)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st bl)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st bl))
    (hcomp : ComputesB M (4 * c.bw) bl ciphB F) (hxs : xs.length = n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs 0 s) :
    WP isa (c.loopWide w M lg) s (Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs n) := by
  have hn64 := hF.nFit
  obtain hp : 0 < 2 ^ lg := Nat.two_pow_pos lg
  -- After `j` steps, `t0` says whether `j < n`.
  obtain ev : ∀ {j : Nat} {t : State}, j ≤ n → t.gpr .s3 = BitVec.ofNat 64 (n₀ - 2 ^ lg * j) →
      GroupsLeft lg t → isa.eval (.nonzero .t0) t = some (decide (j < n)) ∧
        isa.eval (.zero .t0) t = some (decide (n ≤ j)) := fun {j t} hj h3 hg => by
    obtain hq : (n₀ - 2 ^ lg * j) / 2 ^ lg = n - j := by rw [Nat.sub_mul_div, hn]
    obtain h0 : t.gpr .t0 = BitVec.ofNat 64 (n - j) := by
      rw [hg, h3, ushiftRight_ofNat (by omega_using [hn64]), hq]
    obtain hlt : n - j < 2 ^ 64 := by
      have : n ≤ n₀ := by rw [hn]; exact Nat.div_le_self _ _
      omega_using [hn64, this]
    rw [eval_nonzero_ofNat _ _ hlt h0, eval_zero_ofNat _ _ hlt h0]
    exact ⟨congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h], fun h => by omega_using [h]⟩),
      congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h, hj], fun h => by omega_using [h]⟩)⟩
  unfold Core.loopWide
  refine WP.seq (WP.of_syms (wp_srl hlg fun s₁ u₁ => WP.block_nil fun sy₁ => ?_))
  obtain hI₁ : Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs 0 s₁ :=
    ⟨by rw [u₁.other _ (by decide)]; exact hI.b,
      fun r hr h3 h2 => by rw [u₁.other r (kept_ne r hr).1]; exact hI.keep r hr h3 h2,
      by rw [u₁.rd, hI.rd], by rw [u₁.wr, hI.wr], by rw [u₁.other _ (by decide)]; exact hI.dp,
      by rw [u₁.other _ (by decide)]; exact hI.np,
      cs.ready_frame (rs := []) hI.ready (fun r hr _ _ _ _ => u₁.other r (kept_ne r hr).1) u₁.rd u₁.wr sy₁
        (by rw [u₁.mem]; exact Frame.refl _ _) (fun _ h => nomatch h) (fun _ h => nomatch h),
      by rw [u₁.mem]; exact hI.data, by rw [u₁.mem]; exact hI.chn, by rw [u₁.mem]; exact hI.frame⟩
  obtain g₁ : GroupsLeft lg s₁ := by simp only [GroupsLeft, u₁.gpr, u₁.other _ (show Reg.s3 ≠ .t0 by decide)]
  obtain ⟨-, ez⟩ := ev (Nat.zero_le _) hI₁.np g₁
  by_cases hn0 : n = 0
  · subst hn0
    exact WP.ite true (by rw [ez]; rfl) (fun _ => WP.block_nil hI₁) (fun h => by cases h)
  refine WP.ite false (by rw [ez]; simp; omega_using [hn0]) (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := c.bodyWide w M lg) (c := .nonzero .t0)
    (Q := Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs n)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs j t)
    ?_ n s₁ ⟨0, by omega_using [], by omega_using [hn0], hI₁⟩
  rintro _ t ⟨j, rfl, hj, h⟩
  refine WP.mono (step_wp cs hF hw hM hB hpre hpost hcomp (exOk_groupsLeft hlg) hxs hj h) fun t' ⟨h', g'⟩ => ?_
  obtain ⟨e, -⟩ := ev (j := j + 1) (by omega_using [hj]) h'.np g'
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [e]; simp [he], he ▸ h'⟩
  · right; exact ⟨by rw [e]; simp; omega_using [hj, he], n - (j + 1), by omega_using [hj, he], j + 1, rfl,
      by omega_using [hj, he], h'⟩

end

end VG.Proof.Modes.RISCV64

end

end


/-!
# A mode on RISC-V, for any core: the whole function

`seq_wp`: `c.seq M`, for a core `c` with `CoreSpec c` and a mode `M` whose
operations compute the step function `F` (`Computes`), with its arguments in
registers (`f(key = a0, iv = a1, data = a2, n = a3)`), replaces the `n`
steps of data at `data` with the outputs of `F` from the IV, and (if
`M.ivOut`) the IV with the last chaining value; it keeps the registers the
caller expects preserved, the stack pointer and the return address. Each
mode's and cipher's contract follows from it. `seq_changes_wp`: besides,
memory changes only in the frame (below the stack pointer), the data and the
IV, and the frame is zeroed (`Changes`).

Both are `seqWith_changes_wp` for the loops of `Core.seq`, `Core.steps M`
(`steps_ok`): the function around any loops that take all the steps
(`LoopsOk`), as `Core.seq2`'s do too (`Wide.lean`). `seqWith_changesO_wp`
is the function around loops that leave any data and chaining value
(`LoopsOkO`), as those of the final CFB functions do (`SeqFinal.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Modes VG.Impl.Modes.RISCV64
open VG.Spec.Aes (bytesAt)

variable {c : Core} {M : Mode}

section
variable (s₀ : State)

abbrev P : Addr := s₀.gpr .a1
abbrev Dp : Addr := s₀.gpr .a2
abbrev N : Nat := (s₀.gpr .a3).toNat

abbrev ivR (c : Core) : Region := ⟨P s₀, 4 * c.bw⟩

/-- The frame's base. -/
abbrev Fb (c : Core) : Addr := s₀.sp - BitVec.ofNat 64 (8 * c.total)

end

/-- What the function needs on entry: the IV readable (and writable, apart
from the data, if the mode writes it back), the data writable, neither
wrapping around, the frame's bytes below the stack pointer, apart from the
IV and the data. -/
structure SeqPre (c : Core) (M : Mode) (s₀ : State) : Prop where
  spAl : s₀.sp.toNat % 16 = 0
  spFit : 8 * c.total ≤ s₀.sp.toNat
  ivRd : ivR s₀ c ∈ s₀.rd ++ s₀.wr
  ivWr : M.ivOut = true → ivR s₀ c ∈ s₀.wr
  ivFit : (P s₀).toNat + 4 * c.bw ≤ 2 ^ 64
  dataW : dataRegion (Dp s₀) M.step (N s₀) ∈ s₀.wr
  dataFit : (Dp s₀).toNat + M.step * N s₀ ≤ 2 ^ 64
  dataScr : Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) (scrRegion c (Fb s₀ c))
  ivScr : Region.Disjoint (ivR s₀ c) (scrRegion c (Fb s₀ c))
  ivData : M.ivOut = true → Region.Disjoint (ivR s₀ c) (dataRegion (Dp s₀) M.step (N s₀))
  step : 0 < M.step ∧ M.step ≤ 4 * c.bw
  layout : Layout c

/-! ## The slots -/

/-- The mode's slots. -/
abbrev modeR (B : Addr) : Region := ⟨B, 48⟩

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.savedSlot, coreSlot]); omega_arith))

theorem range4_map {α : Type} (f : Nat → α) : (List.range 4).map f = [f 0, f 1, f 2, f 3] := rfl

theorem bw_le (hL : Layout c) : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]

theorem buf_le4 (hL : Layout c) : 8 * c.buf + 4 * c.bw ≤ min (8 * c.total) 2032 :=
  Nat.le_min.mpr ⟨Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hL.G_pos) _) hL.buf_le,
    Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hL.G_pos) _) hL.disp⟩

/-- The mode's slots are below the core's. -/
theorem total_ge (hL : Layout c) : coreSlot + 1 ≤ c.total := by
  have := hL.buf_ge; have := buf_le4 hL; have := hL.bw
  simp only [coreSlot] at *; omega_arith

theorem fb_toNat' {s₀ : State} (hfit : 8 * c.total ≤ s₀.sp.toNat) :
    (Fb s₀ c).toNat = s₀.sp.toNat - 8 * c.total := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_arith)]

theorem fb_toNat {s₀ : State} (hp : SeqPre c M s₀) : (Fb s₀ c).toNat = s₀.sp.toNat - 8 * c.total :=
  fb_toNat' hp.spFit

theorem fb_al {s₀ : State} (hp : SeqPre c M s₀) : (Fb s₀ c).toNat % 4 = 0 := by
  rw [fb_toNat hp]; have := hp.spAl; omega_using [this]

/-- The frame, from inside `bigFrame`, for any function in the modes' frame. -/
theorem scrIn_of' {s₀ t : State} (hs : s₀.sp.toNat % 16 = 0) (hsp : 8 * c.total ≤ s₀.sp.toNat)
    (hL : Layout c) (ht : FrameAt (8 * c.total) s₀ t)
    (hw : 0 < 8 * c.total → 8 * c.total ≤ 4064 → (⟨t.sp, 8 * c.total⟩ : Region) ∈ t.wr) :
    ScrIn t (Fb s₀ c) c.total := by
  obtain hf := fb_toNat' hsp
  have he := hL.even
  have := s₀.sp.isLt
  obtain hg := total_ge hL
  have e : Fb s₀ c = t.sp := ht.sp.symm
  refine ⟨by rw [hf]; omega_arith, by rw [hf]; omega_arith, fun o w ho => ?_,
    fun h4 => by rw [e]; exact hw (by simp only [coreSlot] at hg; omega_arith) h4, ?_⟩
  · obtain ⟨L, h1, h2, h3⟩ := ht.low (by simp only [coreSlot] at hg; omega_arith)
    rw [e]
    exact ⟨_, h3, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · intro o w h0 ho hc
    have e : Fb s₀ c = t.sp := ht.sp.symm
    rw [e]; exact ht.inFrame o w h0 ho hc

/-- The frame, from inside `bigFrame`. -/
theorem scrIn_of {s₀ t : State} (hp : SeqPre c M s₀) (ht : FrameAt (8 * c.total) s₀ t)
    (hw : 0 < 8 * c.total → 8 * c.total ≤ 4064 → (⟨t.sp, 8 * c.total⟩ : Region) ∈ t.wr) :
    ScrIn t (Fb s₀ c) c.total :=
  scrIn_of' hp.spAl hp.spFit hp.layout ht hw

/-- A slot of the mode, in its lowest region. -/
theorem slot_low {s : State} {B : Addr} {k : Nat} (hS : ScrIn s B c.total) (hL : Layout c) (hk : k < coreSlot) :
    InRegions s.wr (slotA B k) 8 := by
  have := total_ge hL
  have h6 : coreSlot = 6 := rfl
  exact hS.low _ _ (by omega_arith)

theorem slot_al {s : State} {B : Addr} {k : Nat} (hS : ScrIn s B c.total) (hk : k < c.total) :
    (slotA B k).toNat % 8 = 0 := by
  have := hS.al; have := hS.fit
  obtain e : (B + BitVec.ofNat 64 (8 * k)).toNat = B.toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * k) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  rw [e]
  omega_arith

theorem readW_sep64 {m : Mem} {a b : Addr} {v : BitVec 64} (h : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (fun x h1 h2 => h x (by simp only [Region.Contains]; omega_using [h1])
    (by simp only [Region.Contains]; omega_using [h2])) (by decide)

/-- Two different slots of the mode are apart. -/
theorem slot_sep {B : Addr} {i j : Nat} (hi : i < coreSlot) (hj : j < coreSlot) (hne : i ≠ j) :
    Region.Disjoint ⟨slotA B i, 8⟩ ⟨slotA B j, 8⟩ :=
  VG.Offset.disjoint _ (by omega_using [hne]) (by simp only [coreSlot] at *; omega_arith)
    (by simp only [coreSlot] at *; omega_arith)

/-- A slot of the mode, in its slots. -/
theorem slot_mode {B : Addr} {i : Nat} (hi : i < coreSlot) : (modeR B).Contains (slotA B i) (64 / 8) :=
  VG.Offset.contains_base _ (by simp only [coreSlot] at *; omega_arith) (by simp only [coreSlot] at *; omega_arith)

/-! ## The IV's copies -/

/-- The areas of the IV's copies: the IV as the data. -/
def ivAreas (c : Core) (P B : Addr) : Loc → Addr
  | .dat => P
  | .chn => slotA B Core.chnSlot
  | .buf => slotA B c.buf

/-- The IV's copies access only the frame a word at a time. -/
theorem ivAreas_al {s₀ : State} (hp : SeqPre c M s₀) (P : Addr) :
    ∀ l, Core.wordAt false l = true → (ivAreas c P (Fb s₀ c) l).toNat % 4 = 0
  | .dat, h => by cases h
  | .chn, _ => al4 (fb_al hp) (by simp [Core.chnSlot])
  | .buf, _ => al4 (fb_al hp) (by omega_using [])

theorem ivAreasOk {s₀ s : State} (hp : SeqPre c M s₀) (hS : ScrIn s (Fb s₀ c) c.total)
    (hb : s.gpr sb = Fb s₀ c) (h2 : s.gpr .s2 = P s₀) {ws : List Loc} (hws : ∀ l ∈ ws, l = .dat → ivR s₀ c ∈ s.wr)
    (hiv : ivR s₀ c ∈ s.rd ++ s.wr) :
    AreasOk c s (fun _ => 4 * c.bw) (ivAreas c (P s₀) (Fb s₀ c)) ws := by
  have hL := hp.layout
  have hdisp := hL.disp
  have hge := hL.buf_ge
  obtain hbw := bw_le hL
  obtain hb4 := buf_le4 hL
  have hP := hp.ivFit
  have hfit := hS.fit
  have h6 : coreSlot = 6 := rfl
  obtain inScr : ∀ d w, d + w ≤ min (8 * c.total) 2032 → InRegions s.wr (Fb s₀ c + BitVec.ofNat 64 d) w :=
    fun d w h => hS.low d w h
  refine ⟨fun l off ho => ?_, fun l off ho => ?_, fun l off w hw0 ho => ?_, fun l hl off w hw0 ho => ?_,
    fun l l' hne => ?_, fun _ => by omega_arith⟩
  · cases l
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [h2, Nat.zero_add]
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb, VG.Offset.add_add]
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb, VG.Offset.add_add]
  · cases l <;> simp only [Core.loc] at ho ⊢ <;> slot_omega
  · cases l
    · exact ⟨_, hiv, VG.Offset.contains_base _ ho (by omega_arith)⟩
    · obtain ⟨r, hr, hc⟩ := inScr (8 * Core.chnSlot + off) w (by slot_omega)
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
    · obtain ⟨r, hr, hc⟩ := inScr (8 * c.buf + off) w (by omega_arith)
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
  · cases l
    · exact ⟨_, hws _ hl rfl, VG.Offset.contains_base _ ho (by omega_arith)⟩
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by slot_omega)
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by omega_arith)
  · have hb8 : 8 * c.buf + 4 * c.bw ≤ 8 * c.total := Nat.le_trans hb4 (Nat.min_le_left _ _)
    obtain dIv : ∀ d, d + 4 * c.bw ≤ 8 * c.total →
        Region.Disjoint (ivR s₀ c) ⟨Fb s₀ c + BitVec.ofNat 64 d, 4 * c.bw⟩ :=
      fun d h => hp.ivScr.sub_right (slot_sub h)
    obtain hc : 8 * Core.chnSlot + 4 * c.bw ≤ 8 * c.buf := by slot_omega
    obtain dCB : Region.Disjoint ⟨slotA (Fb s₀ c) Core.chnSlot, 4 * c.bw⟩ ⟨slotA (Fb s₀ c) c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inl hc) (by omega_arith) (by omega_arith)
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [ivAreas]
    · exact dIv _ (by omega_arith)
    · exact dIv _ hb8
    · exact (dIv _ (by omega_arith)).symm
    · exact dCB
    · exact (dIv _ hb8).symm
    · exact dCB.symm

theorem copyBlk_ok {bw : Nat} {dst src : Loc} {ws : List Loc} (hd : dst ∈ ws) {len : Loc → Nat}
    (hl : ∀ l, len l = 4 * bw) : ∀ o ∈ copyBlk bw dst src, o.InBounds len ∧ o.dst ∈ ws := by
  intro o ho
  simp only [copyBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨w, hw, rfl⟩ := ho
  refine ⟨⟨?_, ?_, fun _ _ h => by cases h⟩, hd⟩ <;>
    simp only [Op.width, Bool.false_eq_true, ite_false, ite_true, hl] <;> omega_using [hw]

/-! ## The entry -/

/-- After the entry, from `t` in the frame: the frame's base in `sb`, the
mode's state in `s1`–`s3`, the caller's `s1`–`s4` in their slots, the IV in
the chaining value's. -/
structure Entered (c : Core) (s₀ t s : State) : Prop where
  b : s.gpr sb = Fb s₀ c
  s1 : s.gpr .s1 = P s₀
  s3 : s.gpr .s3 = s₀.gpr .a3
  s2 : s.gpr .s2 = Dp s₀
  keep : ∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = t.wr
  saved : ∀ i < 4, s.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .s1)
  chn : bytesAt s.mem (slotA (Fb s₀ c) Core.chnSlot) (4 * c.bw) = bytesAt s₀.mem (P s₀) (4 * c.bw)
  frame : Frame [modeR (Fb s₀ c)] s₀.mem s.mem

/-- The registers the entry writes are not kept, but for `s1`–`s4`. -/
theorem kept_ne_entry : ∀ r ∈ kept, r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 := by decide

/-- After `Core.entry`, from `t` in the frame: the frame's base in `sb`,
the second and fourth arguments in `s1`, `s2` and `s3`, the caller's
`s1`–`s4` in their slots, and the rest as on entry but for `t0`. -/
structure Saves (c : Core) (s₀ t s : State) : Prop where
  b : s.gpr sb = Fb s₀ c
  s1 : s.gpr .s1 = s₀.gpr .a1
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = s₀.gpr .a3
  other : ∀ r, r ≠ .t0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = t.wr
  saved : ∀ i < 4, s.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .s1)
  frame : Frame [modeR (Fb s₀ c)] s₀.mem s.mem

/-- The caller's `s1`–`s4` saved, for any function in the modes' frame. -/
theorem saves_wp {s₀ t : State} (hL : Layout c) (hS : ScrIn t (Fb s₀ c) c.total)
    (ht : FrameAt (8 * c.total) s₀ t) :
    WP isa (.block Core.entry) t (Saves c s₀ t) := by
  obtain hg := total_ge hL
  have h6 : coreSlot = 6 := rfl
  obtain hsv : ∀ i < 4, Core.savedSlot i < coreSlot := fun i hi => by slot_omega
  obtain ha : ∀ i < 4, (slotA (Fb s₀ c) (Core.savedSlot i)).toNat % 8 = 0 := fun i hi =>
    slot_al hS (by have := hsv i hi; omega_arith)
  obtain hw : ∀ i < 4, InRegions t.wr (slotA (Fb s₀ c) (Core.savedSlot i)) 8 := fun i hi =>
    slot_low hS hL (hsv i hi)
  obtain g₀ : ∀ r, t.gpr r = s₀.gpr r := fun r => by rw [ht.gpr]
  simp only [Core.entry, range4_map, Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append, mov]
  refine wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_
  obtain b₁ : s₁.gpr .t0 = Fb s₀ c := by rw [u₁.gpr, BitVec.add_zero, ht.sp]
  refine wp_sd (a := slotA (Fb s₀ c) (Core.savedSlot 0)) (by decide) (by rw [b₁]) (ha 0 (by decide))
    (by rw [u₁.wr]; exact hw 0 (by decide)) fun s₂ u₂ => ?_
  refine wp_sd (a := slotA (Fb s₀ c) (Core.savedSlot 1)) (by decide) (by rw [u₂.gpr, b₁])
    (ha 1 (by decide)) (by rw [u₂.wr, u₁.wr]; exact hw 1 (by decide)) fun s₃ u₃ => ?_
  refine wp_sd (a := slotA (Fb s₀ c) (Core.savedSlot 2)) (by decide) (by rw [u₃.gpr, u₂.gpr, b₁])
    (ha 2 (by decide)) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw 2 (by decide)) fun s₄ u₄ => ?_
  refine wp_sd (a := slotA (Fb s₀ c) (Core.savedSlot 3)) (by decide) (by rw [u₄.gpr, u₃.gpr, u₂.gpr, b₁])
    (ha 3 (by decide)) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hw 3 (by decide)) fun s₅ u₅ => ?_
  obtain g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  obtain v₁ : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => by rw [u₁.other r h, g₀]
  obtain m₅ : s₅.mem = (((s₀.mem.writeW (slotA (Fb s₀ c) (Core.savedSlot 0)) (s₀.gpr .s1)).writeW
      (slotA (Fb s₀ c) (Core.savedSlot 1)) (s₀.gpr .s2)).writeW (slotA (Fb s₀ c) (Core.savedSlot 2))
      (s₀.gpr .s3)).writeW (slotA (Fb s₀ c) (Core.savedSlot 3)) (s₀.gpr .s4) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, ht.mem,
      v₁ .s1 (by decide), v₁ .s2 (by decide), v₁ .s3 (by decide), v₁ .s4 (by decide)]
  refine wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_
  obtain m₉ : s₉.mem = s₅.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  -- The saved values.
  obtain sv₅ : ∀ i < 4, s₅.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 =
      s₀.gpr (Core.savedRegs.getD i .s1) := by
    intro i hi
    rw [m₅]
    obtain sep := fun i j hi hj hne => slot_sep (B := Fb s₀ c) (i := Core.savedSlot i) (j := Core.savedSlot j)
      (hsv i hi) (hsv j hj) (by simp only [Core.savedSlot]; exact hne)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · rw [readW_sep64 (sep 0 3 (by decide) (by decide) (by decide)),
        readW_sep64 (sep 0 2 (by decide) (by decide) (by decide)),
        readW_sep64 (sep 0 1 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]; rfl
    · rw [readW_sep64 (sep 1 3 (by decide) (by decide) (by decide)),
        readW_sep64 (sep 1 2 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]; rfl
    · rw [readW_sep64 (sep 2 3 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]; rfl
    · rw [Mem.readW_writeW_self64]; rfl
  obtain f₅ : Frame [modeR (Fb s₀ c)] s₀.mem s₅.mem := by
    rw [m₅]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (slot_mode (hsv 0 (by decide)))).writeW
      List.mem_cons_self _ (slot_mode (hsv 1 (by decide)))).writeW List.mem_cons_self _
      (slot_mode (hsv 2 (by decide)))).writeW List.mem_cons_self _ (slot_mode (hsv 3 (by decide)))
  refine ⟨?_, ?_, ?_, ?_, fun r h0 h1 h2 h3 h4 => ?_, ?_, ?_, fun i hi => by rw [m₉]; exact sv₅ i hi,
    by rw [m₉]; exact f₅⟩
  · rw [show sb = .s4 from rfl] at u₆ ⊢
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅, b₁]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅, v₁ _ (by decide)]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅, v₁ _ (by decide)]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅, v₁ _ (by decide)]
  · rw [u₉.other r h3, u₈.other r h2, u₇.other r h1, u₆.other r h4, g₅, v₁ r h0]
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, ht.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem entry_wp {s₀ t : State} (hp : SeqPre c M s₀) (ht : FrameAt (8 * c.total) s₀ t)
    (hw : 0 < 8 * c.total → 8 * c.total ≤ 4064 → (⟨t.sp, 8 * c.total⟩ : Region) ∈ t.wr) :
    WP isa (.block (Core.entry ++ c.ivIn)) t (Entered c s₀ t) := by
  have hL := hp.layout
  obtain hbw := bw_le hL
  obtain hS := scrIn_of hp ht hw
  obtain hg := total_ge hL
  have h6 : coreSlot = 6 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (saves_wp hL hS ht) fun s₉ h₉ => ?_
  obtain hsv : ∀ i < 4, Core.savedSlot i < coreSlot := fun i hi => by slot_omega
  obtain keep₉ : ∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s₉.gpr r = s₀.gpr r :=
    fun r hr h1 h2 h3 h4 => h₉.other r (kept_ne_entry r hr).1 h1 h2 h3 h4
  simp only [Core.ivIn, mov]
  -- The IV to the chaining value.
  obtain hS₉ : ScrIn s₉ (Fb s₀ c) c.total := hS.congr h₉.wr
  refine opsCode_wp c false (ws := [.chn]) (ivAreas_al hp _) (copyBlk_ok (List.mem_singleton_self _) fun _ => rfl)
    (copyBlk_wordAl _ _ _) (ivAreasOk hp hS₉ h₉.b h₉.s2 (fun l hl e => by simp at hl; subst hl; cases e)
      (by rw [h₉.rd, h₉.wr]; obtain ⟨ws, hws⟩ := ht.wr; rw [hws]
          rcases List.mem_append.mp hp.ivRd with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_append_right _ h)))
    fun s₁₁ a₁₁ f₁₁ g₁₁ rd₁₁ wr₁₁ => wp_mv fun s₁₂ u₁₂ => WP.block_nil ?_
  obtain chnOnly : ∀ {R : Region}, R.Disjoint (chnRegion c (Fb s₀ c)) →
      ∀ r ∈ areaRegions (fun _ => 4 * c.bw) (ivAreas c (P s₀) (Fb s₀ c)) [.chn], R.Disjoint r := fun h r hr => by
    simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h
  obtain g : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .s2 → s₁₂.gpr r = s₉.gpr r := fun r h0 h1 h2 hs => by
    rw [u₁₂.other r hs, g₁₁ r h0 h1 h2]
  refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h₉.b,
    by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h₉.s1,
    by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h₉.s3,
    by rw [u₁₂.gpr, g₁₁ _ (by decide) (by decide) (by decide),
      h₉.other _ (by decide) (by decide) (by decide) (by decide) (by decide)],
    fun r hr h1 h2 h3 h4 => by
      rw [g r (kept_ne_entry r hr).1 (kept_ne_entry r hr).2.1 (kept_ne_entry r hr).2.2 h2,
        keep₉ r hr h1 h2 h3 h4],
    by rw [u₁₂.rd, rd₁₁, h₉.rd], by rw [u₁₂.wr, wr₁₁, h₉.wr], fun i hi => ?_, ?_, ?_⟩
  · rw [u₁₂.mem, ← h₉.saved i hi]
    exact f₁₁.readW (Region.contains_self _ _) (chnOnly
      (VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))) (by decide)
  · refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    obtain e := a₁₁ .chn i hi
    simp only [cont, ivAreas] at e
    rw [u₁₂.mem, e, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
    exact h₉.frame.bytes (R := ivR s₀ c) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ivScr.sub_right (Region.sub_prefix (by omega_arith))) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith) hi
  · rw [u₁₂.mem]
    refine h₉.frame.trans (f₁₁.sub fun r hr => ?_)
    simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, List.mem_singleton_self _, VG.Offset.sub_base _ (by slot_omega)⟩

/-! ## The exit -/

theorem restore_wp {s₀ u : State} (hL : Layout c) (hS : ScrIn u (Fb s₀ c) c.total)
    (hb : u.gpr sb = Fb s₀ c)
    (hsv : ∀ i < 4, u.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .s1))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u', u'.gpr .s1 = s₀.gpr .s1 → u'.gpr .s2 = s₀.gpr .s2 → u'.gpr .s3 = s₀.gpr .s3 →
      u'.gpr .s4 = s₀.gpr .s4 → u'.gpr .t3 = Fb s₀ c →
      (∀ r, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → r ≠ .t3 → u'.gpr r = u.gpr r) →
      u'.mem = u.mem → u'.rd = u.rd → u'.wr = u.wr → WP isa (.block is) u' Q) :
    WP isa (.block (Core.restore ++ is)) u Q := by
  obtain hg := total_ge hL
  have h6 : coreSlot = 6 := rfl
  obtain hsv' : ∀ i < 4, Core.savedSlot i < coreSlot := fun i hi => by slot_omega
  obtain ha : ∀ i < 4, (slotA (Fb s₀ c) (Core.savedSlot i)).toNat % 8 = 0 := fun i hi =>
    slot_al hS (by have := hsv' i hi; omega_arith)
  obtain hin : ∀ i < 4, InRegions (u.rd ++ u.wr) (slotA (Fb s₀ c) (Core.savedSlot i)) 8 := fun i hi => by
    obtain ⟨r, hr, hc⟩ := slot_low hS hL (hsv' i hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [Core.restore, range4_map, Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append, mov]
  refine wp_mv fun u₀ v₀ => ?_
  obtain b₀ : u₀.gpr .t3 = Fb s₀ c := by rw [v₀.gpr]; exact hb
  refine wp_ld (a := slotA (Fb s₀ c) (Core.savedSlot 0)) (by decide) (by rw [b₀]) (ha 0 (by decide))
    (by rw [v₀.rd, v₀.wr]; exact hin 0 (by decide)) fun u₁ v₁ => ?_
  refine wp_ld (a := slotA (Fb s₀ c) (Core.savedSlot 1)) (by decide) (by rw [v₁.other _ (by decide), b₀])
    (ha 1 (by decide)) (by rw [v₁.rd, v₁.wr, v₀.rd, v₀.wr]; exact hin 1 (by decide)) fun u₂ v₂ => ?_
  refine wp_ld (a := slotA (Fb s₀ c) (Core.savedSlot 2)) (by decide)
    (by rw [v₂.other _ (by decide), v₁.other _ (by decide), b₀]) (ha 2 (by decide))
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, v₀.rd, v₀.wr]; exact hin 2 (by decide)) fun u₃ v₃ => ?_
  refine wp_ld (a := slotA (Fb s₀ c) (Core.savedSlot 3)) (by decide)
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), b₀]) (ha 3 (by decide))
    (by rw [v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, v₀.rd, v₀.wr]; exact hin 3 (by decide)) fun u₄ v₄ => ?_
  obtain m₃ : u₃.mem = u.mem := by rw [v₃.mem, v₂.mem, v₁.mem, v₀.mem]
  refine k u₄ ?_ ?_ ?_ ?_ ?_ (fun r h1 h2 h3 h4 ht => ?_) (by rw [v₄.mem, m₃])
    (by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, v₀.rd]) (by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, v₀.wr])
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, v₀.mem,
      hsv 0 (by decide)]; rfl
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, v₀.mem, hsv 1 (by decide)]; rfl
  · rw [v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, v₀.mem, hsv 2 (by decide)]; rfl
  · rw [v₄.gpr, m₃, hsv 3 (by decide)]; rfl
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), b₀]
  · rw [v₄.other r h4, v₃.other r h3, v₂.other r h2, v₁.other r h1, v₀.other r ht]

theorem wipe_wp {u : State} {B : Addr} (hL : Layout c) (hS : ScrIn u B c.total) (h3 : u.gpr .t3 = B) :
    WP isa c.wipe u fun u' => (∀ j < c.total, u'.mem.readW (slotA B j) 64 = 0#64) ∧
      Frame [⟨B, 8 * c.total⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  obtain hg := total_ge hL
  have ht := hL.total
  have h6 : coreSlot = 6 := rfl
  have hal := hS.al
  have hfit := hS.fit
  unfold Core.wipe
  apply WP.seq
  refine WP.mono (Q := fun (v : State) => v.gpr .t0 = 0#64 ∧ v.gpr .t1 = B ∧ v.gpr .t2 = BitVec.ofNat 64 c.total ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → v.gpr r = u.gpr r) ∧ v.mem = u.mem ∧ v.rd = u.rd ∧ v.wr = u.wr)
    (wp_li (imm := 0) (by decide) fun v₁ w₁ => wp_mv fun v₂ w₂ => wp_li (by omega_arith) fun v₃ w₃ =>
      WP.block_nil ⟨by rw [w₃.other _ (by decide), w₂.other _ (by decide), w₁.gpr],
        by rw [w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide), h3], w₃.gpr,
        fun r h0 h1 h2 => by rw [w₃.other r h2, w₂.other r h1, w₁.other r h0],
        by rw [w₃.mem, w₂.mem, w₁.mem], by rw [w₃.rd, w₂.rd, w₁.rd], by rw [w₃.wr, w₂.wr, w₁.wr]⟩)
    fun v ⟨z0, p1, c2, gv, mv, rv, wv⟩ => ?_
  refine WP.mono (fillLoop_ok (v := .t0) (ptr := .t1) (cnt := .t2) (by decide) (by decide) (by decide) v
    (N := c.total) (by simp only [coreSlot] at hg; omega_arith) (by omega_arith) c2
    (by rw [p1]; omega_arith) (fun i hi => by
      rw [wv, p1]; exact hS.wr _ _ (by decide) (by omega_arith) (by omega_arith)))
    fun u' ⟨tz, tf, tk⟩ => ⟨fun j hj => by rw [← z0, ← p1]; exact tz j hj, by rw [← mv, ← p1]; exact tf,
      fun r h0 h1 h2 => by rw [tk.gpr (by simp [h1, h2]), gv r h0 h1 h2], by rw [tk.2.1, rv],
      by rw [tk.2.2, wv]⟩

/-! ## The function -/

theorem chunksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {st n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (dataRegion D st n) r) (hn : st * n ≤ 2 ^ 64) :
    chunksAt st m' D n = chunksAt st m D n := by
  refine List.map_congr_left fun j hj => List.map_congr_left fun u hu => ?_
  obtain hj := List.mem_range.mp hj
  obtain hu := List.mem_range.mp hu
  have : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  rw [VG.Offset.add_add]
  exact hf.bytes (R := dataRegion D st n) hd hn (by show st * j + u < st * n; omega_arith)

/-- The inputs: the data's steps and the IV, on entry. -/
abbrev xs0 (M : Mode) (s₀ : State) : List (List Byte) := chunksAt M.step s₀.mem (Dp s₀) (N s₀)
abbrev iv0 (c : Core) (s₀ : State) : List Byte := bytesAt s₀.mem (P s₀) (4 * c.bw)

/-- The regions the mode writes, on entry: the data and the frame. -/
abbrev wrs0 (c : Core) (M : Mode) (s₀ : State) : List Region := wrs c (Fb s₀ c) (Dp s₀) (N s₀) M.step

/-- What the function changes besides the registers: memory only in the
frame, the data and the IV; and it leaves the frame zeroed. -/
structure Changes (c : Core) (M : Mode) (s₀ s' : State) : Prop where
  frame : Frame [scrRegion c (Fb s₀ c), dataRegion (Dp s₀) M.step (N s₀), ivR s₀ c] s₀.mem s'.mem
  zeroed : ∀ j < c.total, s'.mem.readW (slotA (Fb s₀ c) j) 64 = 0#64

/-- What the code `loops` must do, from the state after the key, with the
mode's first step to take: all of them (`Done`). -/
def LoopsOk (cs : CoreSpec c) (M : Mode) (F : StepFn) (s₀ : State) (k : cs.Key) (loops : Prog isa) : Prop :=
  ∀ s₂, Fixed c s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step (4 * c.bw) (wrs0 c M s₀) (N s₀) 1 →
    Inv cs s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step (wrs0 c M s₀) (N s₀) 1 k F (iv0 c s₀) (xs0 M s₀) 0 s₂ →
    WP isa loops s₂ (Done (c := c) s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step F (iv0 c s₀) (xs0 M s₀))

/-- `Done`, with the data's steps `outD` and the chaining value `outC` at
the end, whatever gives them. -/
structure DoneO (s₂ : State) (B D : Addr) (n st : Nat) (outD : List (List Byte)) (outC : List Byte) (s : State) :
    Prop where
  b : s.gpr sb = B
  keep : ∀ r ∈ kept, r ≠ .s3 → r ≠ .s2 → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  data : chunksAt st s.mem D n = outD
  chn : bytesAt s.mem (slotA B Core.chnSlot) (4 * c.bw) = outC
  frame : Frame (big c B D n st) s₂.mem s.mem

/-- `LoopsOk`, with the data's steps `outD` and the chaining value `outC`
at the end (`DoneO`): loops that need not take `F`'s steps, from `F`'s
invariant for none. -/
def LoopsOkO (cs : CoreSpec c) (M : Mode) (F : StepFn) (s₀ : State) (k : cs.Key) (outD : List (List Byte))
    (outC : List Byte) (loops : Prog isa) : Prop :=
  ∀ s₂, Fixed c s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step (4 * c.bw) (wrs0 c M s₀) (N s₀) 1 →
    Inv cs s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step (wrs0 c M s₀) (N s₀) 1 k F (iv0 c s₀) (xs0 M s₀) 0 s₂ →
    WP isa loops s₂ (DoneO (c := c) s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step outD outC)

theorem LoopsOk.toO {cs : CoreSpec c} {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} {loops : Prog isa}
    (h : LoopsOk cs M F s₀ k loops) :
    LoopsOkO cs M F s₀ k (run F (iv0 c s₀) (xs0 M s₀)).1 (run F (iv0 c s₀) (xs0 M s₀)).2 loops :=
  fun s₂ hF hI => WP.mono (h s₂ hF hI) fun _ d => ⟨d.b, d.keep, d.rd, d.wr, d.data, d.chn, d.frame⟩

theorem LoopsOkO.toLoopsOk {cs : CoreSpec c} {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key}
    {loops : Prog isa}
    (h : LoopsOkO cs M F s₀ k (run F (iv0 c s₀) (xs0 M s₀)).1 (run F (iv0 c s₀) (xs0 M s₀)).2 loops) :
    LoopsOk cs M F s₀ k loops :=
  fun s₂ hF hI => WP.mono (h s₂ hF hI) fun _ d => ⟨d.b, d.keep, d.rd, d.wr, d.data, d.chn, d.frame⟩

/-- The function around the loops `loops`, which leave the data's steps
`outD` and the chaining value `outC`, and what it changes (`Changes`). -/
theorem seqWith_changesO_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key}
    {outD : List (List Byte)} {outC : List Byte} {loops : Prog isa}
    (hp : SeqPre c M s₀) (hloops : LoopsOkO cs M F s₀ k outD outC loops) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seqWith loops M.ivOut) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = outD ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = outC) ∧
      Changes c M s₀ s' := by
  have hL := hp.layout
  obtain hg := total_ge hL
  have h6 : coreSlot = 6 := rfl
  obtain hbw := bw_le hL
  obtain hb4 := buf_le4 hL
  obtain hf := fb_toNat hp
  have hspf := hp.spFit
  have hsp := s₀.sp.isLt
  obtain hfit : (Fb s₀ c).toNat + 8 * c.total ≤ 2 ^ 64 := by omega_arith
  obtain modeScr : Region.Sub (modeR (Fb s₀ c)) (scrRegion c (Fb s₀ c)) := Region.sub_prefix (by omega_arith)
  obtain coreScr : Region.Sub (coreRegion c (Fb s₀ c)) (scrRegion c (Fb s₀ c)) :=
    VG.Offset.sub_base _ (by omega_arith)
  obtain chnScr : Region.Sub (chnRegion c (Fb s₀ c)) (scrRegion c (Fb s₀ c)) := VG.Offset.sub_base _ (by slot_omega)
  obtain m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  unfold Core.seqWith
  refine bigFrame_wp (by simp only [Core.frameBytes]; have := hL.even; omega_arith)
    (by simp only [Core.frameBytes]; omega_arith) fun t ht hw => ?_
  obtain hS := scrIn_of hp ht hw
  obtain ⟨ws, hws⟩ := ht.wr
  -- The entry and the key.
  refine WP.seq (WP.of_syms (WP.mono (entry_wp hp ht hw) fun s₁ h₁ sy₁ => ?_))
  obtain wr₁ : s₁.wr = ws ++ s₀.wr := by rw [h₁.wr, hws]
  refine WP.seq (WP.mono (cs.prepare_wp h₁.b (hS.congr h₁.wr) m1
    (cs.keyArgs_congr hk h₁.keep h₁.rd ⟨ws, wr₁⟩ (sy₁.trans ht.syms)
      (h₁.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, m1, modeScr⟩)))
    fun s₂ ⟨ready₂, b₂, kept₂, f₂, rd₂, wr₂⟩ => ?_)
  have kp : ∀ r, r ∈ kept → s₂.gpr r = s₁.gpr r := kept₂
  obtain f₀₂ : Frame [modeR (Fb s₀ c), coreRegion c (Fb s₀ c)] s₀.mem s₂.mem :=
    (h₁.frame.mono (by simp)).trans (f₂.mono (by simp))
  obtain dataOut : ∀ r ∈ [modeR (Fb s₀ c), coreRegion c (Fb s₀ c)],
      Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dataScr.sub_right modeScr
    · exact hp.dataScr.sub_right coreScr
  obtain modeOut : ∀ {R : Region}, Region.Sub R (modeR (Fb s₀ c)) → ∀ r ∈ [coreRegion c (Fb s₀ c)], R.Disjoint r :=
    fun hsub r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Offset.disjoint_base _ (by slot_omega) (by omega_arith)).symm.sub_left hsub
  obtain wr₂' : s₂.wr = ws ++ s₀.wr := by rw [wr₂, wr₁]
  obtain hFx : Fixed c s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step (4 * c.bw) (wrs0 c M s₀) (N s₀) 1 :=
    ⟨hS.congr (by rw [wr₂, h₁.wr]), fun o w hw ho => by rw [wr₂']; exact dataW_of_mem (List.mem_append_right _ hp.dataW) hp.dataFit hw ho,
      hp.dataFit,
      hp.dataScr, (s₀.gpr .a3).isLt, by omega_arith, by decide, ⟨hp.step.1, by have := hp.step.2; omega_arith⟩,
      ⟨by rcases hL.bw with h | h <;> omega_using [h], Nat.le_mul_of_pos_right _ hL.G_pos⟩,
      ⟨_, List.mem_cons_self, fun _ h => h⟩, List.mem_cons_of_mem _ List.mem_cons_self, hL⟩
  obtain hI : Inv cs s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step (wrs0 c M s₀) (N s₀) 1 k F (iv0 c s₀) (xs0 M s₀) 0 s₂ := by
    refine ⟨b₂, fun _ _ _ _ => rfl, rfl, rfl, ?_, ?_, ready₂, ?_, ?_, Frame.refl _ _⟩
    · rw [kp _ (by decide), h₁.s2, Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · rw [kp _ (by decide), h₁.s3, Nat.mul_zero, Nat.sub_zero]; simp only [N, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [chunksAt_frame f₀₂ dataOut (by have := hp.dataFit; omega_arith)]
      simp only [List.take_zero, run, List.nil_append, List.drop_zero]
    · simp only [List.take_zero, run]
      rw [iv0, ← h₁.chn]
      refine List.map_congr_left fun i hi => f₂.bytes (R := chnRegion c (Fb s₀ c))
        (modeOut (VG.Offset.sub_base _ (by slot_omega))) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith)
        (List.mem_range.mp hi)
  obtain sv₂ : ∀ i < 4, s₂.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 =
      s₀.gpr (Core.savedRegs.getD i .s1) := fun i hi => by
    rw [← h₁.saved i hi]
    exact f₂.readW (Region.contains_self _ _) (modeOut (VG.Offset.sub_base _ (by slot_omega))) (by decide)
  -- The steps.
  refine WP.seq (WP.mono (hloops s₂ hFx hI) fun s₄ h₄ => ?_)
  obtain slotOut : ∀ i < 4, ∀ r ∈ big c (Fb s₀ c) (Dp s₀) (N s₀) M.step,
      Region.Disjoint ⟨slotA (Fb s₀ c) (Core.savedSlot i), 64 / 8⟩ r := fun i hi r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by omega_arith)
    · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
    · exact (hp.dataScr.sub_right (VG.Offset.sub_base _ (by slot_omega))).symm
  obtain sv₄ : ∀ i < 4, s₄.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 =
      s₀.gpr (Core.savedRegs.getD i .s1) := fun i hi => by
    rw [← sv₂ i hi]
    exact h₄.frame.readW (Region.contains_self _ _) (slotOut i hi) (by decide)
  have data₄ : chunksAt M.step s₄.mem (Dp s₀) (N s₀) = outD := h₄.data
  obtain keep₄ : ∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s₄.gpr r = s₀.gpr r :=
    fun r hr h1 h2 h3 h4 => by rw [h₄.keep r hr h3 h2, kp r hr, h₁.keep r hr h1 h2 h3 h4]
  obtain s1₄ : s₄.gpr .s1 = P s₀ := by rw [h₄.keep _ (by decide) (by decide) (by decide), kp _ (by decide), h₁.s1]
  obtain wr₄ : s₄.wr = t.wr := by rw [h₄.wr, wr₂, h₁.wr]
  obtain rd₄ : s₄.rd = s₀.rd := by rw [h₄.rd, rd₂, h₁.rd]
  obtain hS₄ : ScrIn s₄ (Fb s₀ c) c.total := hS.congr wr₄
  obtain fr₄ : Frame [scrRegion c (Fb s₀ c), dataRegion (Dp s₀) M.step (N s₀), ivR s₀ c] s₀.mem s₄.mem := by
    refine (f₀₂.sub fun r hr => ?_).trans (h₄.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, modeScr⟩
      · exact ⟨_, List.mem_cons_self, coreScr⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, coreScr⟩
      · exact ⟨_, List.mem_cons_self, chnScr⟩
      · exact ⟨_, m1, fun _ h => h⟩
  -- The end: the registers back, the frame zeroed.
  obtain abi : ∀ v : State, v.gpr .s1 = s₀.gpr .s1 → v.gpr .s2 = s₀.gpr .s2 → v.gpr .s3 = s₀.gpr .s3 →
      v.gpr .s4 = s₀.gpr .s4 → (∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → v.gpr r = s₀.gpr r) →
      abiPreserved s₀ { v with sp := s₀.sp, wr := s₀.wr } := fun v g1 g2 g3 g4 hk => ⟨fun r hr => by
        show v.gpr r = _
        by_cases e1 : r = .s1
        · subst e1; exact g1
        by_cases e2 : r = .s2
        · subst e2; exact g2
        by_cases e3 : r = .s3
        · subst e3; exact g3
        by_cases e4 : r = .s4
        · subst e4; exact g4
        exact hk r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)) e1 e2 e3 e4, rfl,
        hk .ra (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  obtain ne3 : ∀ r ∈ kept, r ≠ .t3 ∧ r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 := by decide
  have scrData : Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) ⟨Fb s₀ c, 8 * c.total⟩ := hp.dataScr
  apply WP.seq
  cases hiv : M.ivOut
  · rw [show (if false = true then c.ivBack else []) = [] by simp, List.nil_append, ← List.append_nil Core.restore]
    refine restore_wp hL hS₄ h₄.b sv₄ fun u g1 g2 g3 g4 g3' g m rdu wru => WP.block_nil ?_
    refine WP.mono (wipe_wp hL (hS₄.congr wru) g3') fun s' ⟨z, f, g', rd', wr'⟩ =>
      ⟨abi s' (by rw [g' _ (by decide) (by decide) (by decide), g1])
        (by rw [g' _ (by decide) (by decide) (by decide), g2]) (by rw [g' _ (by decide) (by decide) (by decide), g3])
        (by rw [g' _ (by decide) (by decide) (by decide), g4]) fun r hr h1 h2 h3 h4 => by
          rw [g' r (ne3 r hr).2.1 (ne3 r hr).2.2.1 (ne3 r hr).2.2.2, g r h1 h2 h3 h4 (ne3 r hr).1,
            keep₄ r hr h1 h2 h3 h4], ?_, (fun h => by cases h), ⟨?_, z⟩⟩
    · show chunksAt M.step s'.mem (Dp s₀) (N s₀) = _
      rw [chunksAt_frame f (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact scrData) (by have := hp.dataFit; omega_arith), m,
        data₄]
    · show Frame _ s₀.mem s'.mem
      rw [m] at f
      exact fr₄.trans (f.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  · rw [show (if true = true then c.ivBack else []) ++ Core.restore =
      mov .s2 .s1 :: (c.opsCode false (copyBlk c.bw .dat .chn) ++ Core.restore) by simp [Core.ivBack]]
    refine wp_mv fun s₅ u₅ => ?_
    obtain b₅ : s₅.gpr sb = Fb s₀ c := by rw [u₅.other _ (by decide)]; exact h₄.b
    obtain ivW : ivR s₀ c ∈ s₅.wr := by rw [u₅.wr, wr₄, hws]; exact List.mem_append_right _ (hp.ivWr hiv)
    refine opsCode_wp c false (ws := [.dat]) (ivAreas_al hp _) (copyBlk_ok (List.mem_singleton_self _) fun _ => rfl)
      (copyBlk_wordAl _ _ _) (ivAreasOk hp (hS₄.congr u₅.wr) b₅ (by rw [u₅.gpr, s1₄]) (fun _ _ _ => ivW)
        (List.mem_append_right _ ivW)) fun s₆ a₆ f₆ g₆ rd₆ wr₆ => ?_
    rw [u₅.mem] at a₆ f₆
    obtain ivOnly : ∀ {R : Region}, R.Disjoint (ivR s₀ c) → ∀ r ∈ areaRegions (fun _ => 4 * c.bw)
        (ivAreas c (P s₀) (Fb s₀ c)) [.dat], R.Disjoint r := fun h r hr => by
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h
    obtain sv₆ : ∀ i < 4, s₆.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 =
        s₀.gpr (Core.savedRegs.getD i .s1) := fun i hi => by
      rw [← sv₄ i hi]
      exact f₆.readW (Region.contains_self _ _)
        (ivOnly (hp.ivScr.sub_right (VG.Offset.sub_base _ (by slot_omega))).symm) (by decide)
    obtain g₆' : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .s2 → s₆.gpr r = s₄.gpr r := fun r h0 h1 h2 h3 => by
      rw [g₆ r h0 h1 h2, u₅.other r h3]
    obtain b₆ : s₆.gpr sb = Fb s₀ c := by
      rw [g₆' _ (by decide) (by decide) (by decide) (by decide)]; exact h₄.b
    refine restore_wp hL (hS₄.congr (by rw [wr₆, u₅.wr])) b₆ sv₆ fun u g1 g2 g3 g4 g3' g m rdu wru => WP.block_nil ?_
    refine WP.mono (wipe_wp hL (hS₄.congr (by rw [wru, wr₆, u₅.wr])) g3') fun s' ⟨z, f, g', rd', wr'⟩ =>
      ⟨abi s' (by rw [g' _ (by decide) (by decide) (by decide), g1])
        (by rw [g' _ (by decide) (by decide) (by decide), g2]) (by rw [g' _ (by decide) (by decide) (by decide), g3])
        (by rw [g' _ (by decide) (by decide) (by decide), g4]) fun r hr h1 h2 h3 h4 => by
          rw [g' r (ne3 r hr).2.1 (ne3 r hr).2.2.1 (ne3 r hr).2.2.2, g r h1 h2 h3 h4 (ne3 r hr).1,
            g₆' r (ne3 r hr).2.1 (ne3 r hr).2.2.1 (ne3 r hr).2.2.2 h2, keep₄ r hr h1 h2 h3 h4], ?_, (fun _ => ?_),
        ⟨?_, z⟩⟩
    · show chunksAt M.step s'.mem (Dp s₀) (N s₀) = _
      rw [chunksAt_frame f (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact scrData) (by have := hp.dataFit; omega_arith), m,
        chunksAt_frame f₆ (ivOnly (hp.ivData hiv).symm) (by have := hp.dataFit; omega_arith), data₄]
    · show bytesAt s'.mem (P s₀) (4 * c.bw) = _
      have hc := h₄.chn
      rw [← hc]
      refine List.map_congr_left fun i hi => ?_
      obtain hi := List.mem_range.mp hi
      rw [f.bytes (R := ivR s₀ c) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.ivScr) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith) hi,
        m]
      obtain e₆ := a₆ .dat i hi
      simp only [cont, ivAreas] at e₆
      rw [e₆, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
      rfl
    · show Frame _ s₀.mem s'.mem
      rw [m] at f
      refine (fr₄.trans (f₆.sub fun r hr => ?_)).trans (f.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-- The function around the loops `loops` meets the mode's postcondition, and
changes only `Changes`. -/
theorem seqWith_changes_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} {loops : Prog isa}
    (hp : SeqPre c M s₀) (hloops : LoopsOk cs M F s₀ k loops) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seqWith loops M.ivOut) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) ∧
      Changes c M s₀ s' :=
  seqWith_changesO_wp cs hp hloops.toO hk

/-- One step at a time. -/
theorem steps_ok (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} {w : Bool}
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step (4 * c.bw)))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step (4 * c.bw)))
    (hpreA : ∀ o ∈ M.pre, WordAl o) (hpostA : ∀ o ∈ M.post, WordAl o)
    (hD : w = true → (Dp s₀).toNat % 4 = 0 ∧ M.step % 4 = 0)
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) : LoopsOk cs M F s₀ k (c.steps w M) := fun _ hFx hI =>
  WP.mono (loop_wp cs hFx ⟨hpreA, hpostA, by have := hFx.scr.al; omega_using [this], hD⟩ rfl hpre hpost hcomp
    (chunksAt_length _ _ _ _) hI) fun _ h => h.done (chunksAt_length _ _ _ _)

theorem and3 (x : BitVec 64) : x &&& BitVec.ofInt 64 3 = BitVec.ofNat 64 (x.toNat % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 3).toNat = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega_using []

/-- The loops `L w`, `w` whether the data's address is a multiple of 4, as
`Core.aligned` chooses them for steps of `st` bytes, for any outputs. -/
theorem aligned_okO (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key}
    {outD : List (List Byte)} {outC : List Byte} {st : Nat} {L : Bool → Prog isa}
    (h : ∀ w, (w = true → (Dp s₀).toNat % 4 = 0 ∧ st % 4 = 0) → LoopsOkO cs M F s₀ k outD outC (L w)) :
    LoopsOkO cs M F s₀ k outD outC (Core.aligned st L) := by
  unfold Core.aligned
  split
  · rename_i hst
    intro s₂ hFx hI
    refine WP.seq (WP.of_syms (wp_andi (imm := 3) (by decide) fun s₃ u₃ => WP.block_nil fun sy₃ => ?_))
    have o₃ : ∀ r, r ≠ .t0 → s₃.gpr r = s₂.gpr r := u₃.other
    obtain hF₃ : Fixed c s₃ (Fb s₀ c) (Dp s₀) (N s₀) M.step (4 * c.bw) (wrs0 c M s₀) (N s₀) 1 :=
      ⟨hFx.scr.congr u₃.wr, by rw [u₃.wr]; exact hFx.dataW, hFx.dataFit, hFx.dataScr, hFx.nFit, hFx.cnt,
        hFx.dec, hFx.step, hFx.buf, hFx.dataIn, hFx.scrIn, hFx.layout⟩
    obtain hI₃ : Inv cs s₃ (Fb s₀ c) (Dp s₀) (N s₀) M.step (wrs0 c M s₀) (N s₀) 1 k F (iv0 c s₀) (xs0 M s₀) 0 s₃ :=
      ⟨by rw [o₃ _ (by decide)]; exact hI.b, fun _ _ _ _ => rfl, rfl, rfl,
        by rw [o₃ _ (by decide)]; exact hI.dp, by rw [o₃ _ (by decide)]; exact hI.np,
        cs.ready_frame (rs := []) hI.ready (fun r hr _ _ _ _ => o₃ r (kept_ne r hr).1) u₃.rd u₃.wr sy₃
          (by rw [u₃.mem]; exact Frame.refl _ _) (fun _ h => nomatch h) (fun _ h => nomatch h),
        by rw [u₃.mem]; exact hI.data, by rw [u₃.mem]; exact hI.chn, Frame.refl _ _⟩
    obtain back : ∀ {t}, DoneO (c := c) s₃ (Fb s₀ c) (Dp s₀) (N s₀) M.step outD outC t →
        DoneO (c := c) s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step outD outC t := fun d =>
      ⟨d.b, fun r hr h3 h2 => by rw [d.keep r hr h3 h2, o₃ r (kept_ne r hr).1], by rw [d.rd, u₃.rd],
        by rw [d.wr, u₃.wr], d.data, d.chn, by rw [← u₃.mem]; exact d.frame⟩
    obtain ev : isa.eval (.zero .t0) s₃ = some (decide ((Dp s₀).toNat % 4 = 0)) := by
      obtain e : s₂.gpr .s2 = Dp s₀ := by rw [hI.dp, Nat.mul_zero]; simp
      rw [eval_zero, u₃.gpr, e, and3, ofNat_beq_zero (by omega_using [])]
    exact WP.ite _ ev (fun hd => WP.mono (h true (fun _ => ⟨by simpa using hd, hst⟩) s₃ hF₃ hI₃) fun _ d => back d)
      (fun _ => WP.mono (h false (fun e => by cases e) s₃ hF₃ hI₃) fun _ d => back d)
  · exact h false fun e => by cases e

/-- The loops `L w`, `w` whether the data's address is a multiple of 4, as
`Core.aligned` chooses them. -/
theorem aligned_ok (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} {L : Bool → Prog isa}
    (h : ∀ w, (w = true → (Dp s₀).toNat % 4 = 0 ∧ M.step % 4 = 0) → LoopsOk cs M F s₀ k (L w)) :
    LoopsOk cs M F s₀ k (Core.aligned M.step L) :=
  (aligned_okO cs fun w hw => (h w hw).toO).toLoopsOk

/-- `seq_wp`, and what the function changes (`Changes`). -/
theorem seq_changes_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step (4 * c.bw)))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step (4 * c.bw)))
    (hpreA : ∀ o ∈ M.pre, WordAl o) (hpostA : ∀ o ∈ M.post, WordAl o)
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) ∧
      Changes c M s₀ s' :=
  seqWith_changes_wp cs hp (aligned_ok cs fun _ hD => steps_ok cs hpre hpost hpreA hpostA hD hcomp) hk

theorem seq_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step (4 * c.bw)))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step (4 * c.bw)))
    (hpreA : ∀ o ∈ M.pre, WordAl o) (hpostA : ∀ o ∈ M.post, WordAl o)
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) :=
  WP.mono (seq_changes_wp cs hp hpre hpost hpreA hpostA hcomp hk) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

end VG.Proof.Modes.RISCV64
