module

import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Variant
public import VerifiedGarbage.Proof.ChaCha20.AArch64.XorContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Xor

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Xor
open VG.Proof.ChaCha20 (ctr ctr_zero ctr_succ keystream_getD length_keystream bytesAt_xor_to
  serialize_stateAt)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt contains_off readW_writeW_out block_correct)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.write (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    Upd s (s.write sz d v) d (v.setWidth 64) :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl⟩

theorem Upd.write64 (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write .x d v) d v := by
  simpa using Upd.write s .x d v

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_mov {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (mov d n :: is)) s Q :=
  wp_addImm (by decide) fun s' u => k s' (by simpa using u)

/-- `wp_mov`, with the stack pointer and the vector registers kept. -/
theorem wp_movS {d n : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n) → s'.sp = s.sp → s'.v = s.v → WP isa (.block is) s' Q) :
    WP isa (.block (mov d n :: is)) s Q := by
  refine WP.cons (s' := s.write .x d (s.gpr n + BitVec.ofNat 64 0)) (by simp [mov, exec, State.read]) ?_
  have u := Upd.write64 s d (s.gpr n + BitVec.ofNat 64 0)
  have hsp : (s.write .x d (s.gpr n + BitVec.ofNat 64 0)).sp = s.sp := rfl
  have hv : (s.write .x d (s.gpr n + BitVec.ofNat 64 0)).v = s.v := rfl
  generalize s.write .x d (s.gpr n + BitVec.ofNat 64 0) = s' at u hsp hv ⊢
  exact k s' (by simpa using u) hsp hv

theorem wp_addImm32 {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth 32 + BitVec.ofNat 32 imm).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .w d n imm :: is)) s Q :=
  WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 + BitVec.ofNat 32 imm))
    (by simp [exec, h, State.read]) (k _ (Upd.write _ _ _ _))

theorem wp_subImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  WP.cons (s' := s.write .x d (imm.setWidth 64)) (by simp [exec]) (k _ (Upd.write64 _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - s.gpr m)) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_eor32 {d n m : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth 32 ^^^ (s.gpr m).setWidth 32).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .w d n m :: is)) s Q :=
  WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 ^^^ (s.gpr m).setWidth 32)) rfl
    (k _ (Upd.write _ _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n >>> sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (((s.mem a).setWidth 32))) ?_ (k _ ?_)
  · simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
      Option.bind_some, State.load, hin, Option.map_some, read_one]
  · have := Upd.write s .w t ((s.mem a).setWidth 32)
    have e : ((s.mem a).setWidth 32).setWidth 64 = (s.mem a).setWidth 64 := by
      ext i hi; simp
    rwa [e] at this

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp [Size.bits]; try omega

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_str32 {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .x t (s.mem.readW a 64)) ?_ (k _ (Upd.write64 _ _ _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

theorem wp_ldr32 {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (s.mem.readW a 32)) ?_ (k _ (Upd.write s .w t _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

end

/-! ## Arithmetic -/

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  conv => lhs; rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- `x >>> 6`, of a number below 2⁶⁴. -/
theorem ofNat_shr6 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 6 = BitVec.ofNat 64 (a / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by lit_omega)]

theorem eval_zero (s : State) (r : Reg) : eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem eval_nonzero (s : State) (r : Reg) : eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

theorem eval_nonzero_ofNat (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 k) : isa.eval (.nonzero .x r) s = some (decide (k ≠ 0)) := by
  have e : isa.eval (.nonzero .x r) s = some (s.gpr r != 0) := eval_nonzero s r
  rw [e, h, bne, ofNat_beq_zero hk]
  simp

/-- The byte stored by `eor w6, w6, w8; strb w6, …` after two `ldrb`s. -/
theorem xor_setWidth (a b : Byte) :
    (((a.setWidth 64).setWidth 32 ^^^ (b.setWidth 64).setWidth 32).setWidth 64).setWidth 8 =
      a ^^^ b := by
  ext i hi; simp

/-- The word stored by `add w3, w3, #1; str w3, …` after an `ldr w3`. -/
theorem inc_setWidth (v : BitVec 32) :
    ((((v.setWidth 64).setWidth 32 + BitVec.ofNat 32 1).setWidth 64).setWidth 32) = v + 1 := by
  simp

/-! ## The entry state

`vg_chacha20_xor`'s source (`x1`) and destination (`x4`) are either the same
buffer or apart (`TPre.alias`): the loop's invariant says what the
destination holds before the bytes done (`OInv.data`, `Dst`) and that the
source after them is intact (`OInv.src`, `Src`), which holds in both cases
(`src_step`). `XPre` is the precondition of the in-place code that
ChaCha20-Poly1305's stitched kernel shares, with the data at `x1` (`dp`).
-/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .x0
abbrev dp : Addr := s₀.gpr .x1
abbrev L : Nat := (s₀.gpr .x2).toNat
abbrev bp : Addr := s₀.gpr .x3
/-- The destination of `vg_chacha20_xor` (that of the in-place code is `dp`). -/
abbrev tp : Addr := s₀.gpr .x4
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev tR : Region := ⟨tp s₀, L s₀⟩
abbrev bR : Region := ⟨bp s₀, 320⟩
/-- The state, the data (the source) and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (L s₀)
/-- The destination on entry. -/
abbrev T0 (k : Nat) : Byte := s₀.mem (tp s₀ + BitVec.ofNat 64 k)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (L s₀)
/-- How many bytes of block `j` are used. -/
abbrev C (j : Nat) : Nat := min 64 (L s₀ - P s₀ j)
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .x2).isLt

/-- The in-place code's precondition: the data at `x1`. -/
structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀, bR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  st_b : (stR s₀).Disjoint (bR s₀)
  d_b : (dR s₀).Disjoint (bR s₀)
  nowrap : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

/-- `vg_chacha20_xor`'s precondition (`xorAArch64.pre`): the source at `x1`,
the destination at `x4`. -/
structure TPre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, tR s₀, bR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  st_t : (stR s₀).Disjoint (tR s₀)
  st_b : (stR s₀).Disjoint (bR s₀)
  d_b : (dR s₀).Disjoint (bR s₀)
  t_b : (tR s₀).Disjoint (bR s₀)
  /-- In place, or apart. -/
  alias : tp s₀ = dp s₀ ∨ (dR s₀).Disjoint (tR s₀)
  nowrap : (dp s₀).toNat + L s₀ ≤ 2 ^ 64
  tnowrap : (tp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem TPre.of (s₀ : State) (h : Proof.ChaCha20.xorAArch64.pre s₀) : TPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- Our caller's `x19`, `x20`, `x30` and `x27`, saved in `buf[256, 288)`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved (bp s₀) s₀.gpr saved m

/-- What the destination holds once the first `n` bytes are done. -/
def Dst (s₀ : State) (n : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (tp s₀ + BitVec.ofNat 64 k) =
    if k < n then D0 s₀ k ^^^ (KS s₀).getD k 0 else T0 s₀ k

/-- The source after the first `n` bytes is intact. -/
def Src (s₀ : State) (n : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, n ≤ k → m (dp s₀ + BitVec.ofNat 64 k) = D0 s₀ k

/-- Before block `j` (the loop's invariant). -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = bp s₀
  x19 : s.gpr .x19 = dp s₀ + BitVec.ofNat 64 (P s₀ j)
  x20 : s.gpr .x20 = BitVec.ofNat 64 (L s₀ - P s₀ j)
  x27 : s.gpr .x27 = tp s₀ + BitVec.ofNat 64 (P s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : Dst s₀ (P s₀ j) s.mem
  src : Src s₀ (P s₀ j) s.mem
  saved : Saved s₀ s.mem

/-! ## Memory -/

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_out m p v (j := i) (k := 12) hi (by lit_omega) (by lit_omega)

/-- The counter (word 12) of a state in memory. -/
theorem stateAt_getElem_counter (m : Mem) (p : Addr) :
    (stateAt m p)[12] = m.readW (p + BitVec.ofNat 64 48) 32 := by
  simp only [stateAt, Vector.getElem_ofFn]

/-- The state after its counter is advanced by `j` in memory. -/
theorem stateAt_writeW_ctr (m : Mem) (p : Addr) (j : Nat) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48)
      (m.readW (p + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 j)) p = ctr (stateAt m p) j := by
  rw [stateAt_writeW_counter, ctr, stateAt_getElem_counter]

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (contains_off (by lit_omega) (by lit_omega)) hd (by decide)

/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨bp s₀, 256⟩

/-- Where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨bp s₀ + BitVec.ofNat 64 256, 32⟩

theorem b256_sub (s₀ : State) : Region.Sub (b256 s₀) (bR s₀) := Region.sub_prefix (by lit_omega)

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bR s₀) := Offset.sub_base _ (by lit_omega)

theorem savR_b256 (s₀ : State) : (savR s₀).Disjoint (b256 s₀) := Offset.disjoint_base _ (by lit_omega) (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' :=
  Spill.Saved.frame_in h (by decide) hf hd

/-- The destination survives a frame apart from it. -/
theorem Dst.frame {s₀ : State} {n : Nat} {rs : List Region} {m m' : Mem} (h : Dst s₀ n m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (tR s₀).Disjoint r) : Dst s₀ n m' := fun k hk => by
  rw [hf.bytes (R := tR s₀) hd (Nat.le_of_lt (L_lt s₀)) hk]; exact h k hk

/-- The source survives a frame apart from it. -/
theorem Src.frame {s₀ : State} {n : Nat} {rs : List Region} {m m' : Mem} (h : Src s₀ n m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) : Src s₀ n m' := fun k hk hn => by
  rw [hf.bytes (R := dR s₀) hd (Nat.le_of_lt (L_lt s₀)) hk]; exact h k hk hn

/-- A write to the destination that leaves it as `Dst s₀ n'` says leaves the
source after `n'` intact: in place, the destination's bytes after `n'` are
those on entry, which are the source's; apart, the source is outside the
write. -/
theorem src_step {s₀ : State} (hp : TPre s₀) {n n' : Nat} (hn : n ≤ n') {m m' : Mem}
    (hs : Src s₀ n m) (hf : Frame [tR s₀] m m') (hd : Dst s₀ n' m') : Src s₀ n' m' := by
  intro k hk hk'
  rcases hp.alias with he | hdis
  · have := hd k hk
    simp only [show ¬ k < n' by omega, ite_false] at this
    simp only [D0, T0, dp, tp] at this he ⊢
    rw [← he]; exact this
  · rw [hf.bytes (R := dR s₀) (by simpa using hdis) (Nat.le_of_lt (L_lt s₀)) hk]
    exact hs k hk (by omega)

/-- `src_step`, through writes to the destination and to regions apart from
the source. -/
theorem src_step' {s₀ : State} (hp : TPre s₀) {n n' : Nat} (hn : n ≤ n') {m m' : Mem}
    {rs : List Region} (hs : Src s₀ n m) (hf : Frame rs m m')
    (hrs : ∀ r ∈ rs, (dR s₀).Disjoint r ∨ Region.Sub r (tR s₀)) (hd : Dst s₀ n' m') :
    Src s₀ n' m' := by
  intro k hk hk'
  rcases hp.alias with he | hdis
  · have := hd k hk
    simp only [show ¬ k < n' by omega, ite_false] at this
    simp only [D0, T0, dp, tp] at this he ⊢
    rw [← he]; exact this
  · have hc : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
      contains_off (by have := L_lt s₀; omega) (by have := L_lt s₀; omega)
    rw [hf _ fun r hr => by
      rcases hrs r hr with hr' | hr'
      · exact hr' _ hc
      · exact fun h => hdis _ hc (hr' _ h)]
    exact hs k hk (by omega)

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 =
      m.readW (p + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep p h (by lit_omega) (by lit_omega)) (by decide)

/-- Distinct offsets below 2⁶⁴ from the same base are distinct addresses. -/
theorem off_ne (p : Addr) {k k' : Nat} (hk : k < 2 ^ 64) (hk' : k' < 2 ^ 64) (h : k' ≠ k) :
    p + BitVec.ofNat 64 k' ≠ p + BitVec.ofNat 64 k := by
  intro he
  have e : BitVec.ofNat 64 k' = BitVec.ofNat 64 k := by
    have e := congrArg (· - p) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt hk', toNat_ofNat_lt hk] at this
  exact h this

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ↓reduceIte]

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : TPre s₀) :
    WP isa (.block (save ++ [mov .x19 .x1, mov .x20 .x2, mov .x27 .x4, mov .x1 .x3])) s₀ (OInv s₀ 0) := by
  refine Spill.save_ok (by decide) (fun p hp' => have hb : p.2 + 8 ≤ 320 := by revert p; decide
    ⟨bR s₀, by simp [hp.wr], contains_off hb (by omega)⟩) ?_
  refine wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_mov fun s₅' u₅' => wp_mov fun s₆ u₆ =>
    WP.block_nil ?_
  have hm : s₆.mem = Spill.saveMem s₀.mem (bp s₀) s₀.gpr saved := by
    rw [u₆.mem, u₅'.mem, u₅.mem, u₄.mem]
  have hf : Frame [bR s₀] s₀.mem s₆.mem := by
    rw [hm]; exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk _ => ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅'.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide)]
  · rw [u₆.gpr, u₅'.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅'.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; simp [P]
  · rw [u₆.other _ (by decide), u₅'.other _ (by decide), u₅.gpr, u₄.other _ (by decide)]; simp [P]
  · rw [u₆.other _ (by decide), u₅'.gpr, u₅.other _ (by decide), u₄.other _ (by decide)]; simp [P]
  · rw [u₆.rd, u₅'.rd, u₅.rd, u₄.rd]
  · rw [u₆.wr, u₅'.wr, u₅.wr, u₄.wr]
  · rw [stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := tR s₀) (by simpa using hp.t_b) (Nat.le_of_lt (L_lt s₀)) hk
  · exact hf.bytes (R := dR s₀) (by simpa using hp.d_b) (Nat.le_of_lt (L_lt s₀)) hk
  · rw [hm]; exact Spill.saveMem_saved (by decide) _ _ _

/-! ## Calling the block function -/

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends OInv s₀ j s where
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

theorem call_ok (v : BlockImpl) {s₀ : State} (hp : TPre s₀) {j : Nat} {s : State} (h : OInv s₀ j s) :
    WP isa (.call v.callee.name v.callee.code) s (AInv s₀ j) := by
  have c0 : s.callEntry.gpr .x0 = st s₀ := (State.callEntry_gpr _ (by decide)).trans h.x0
  have c1 : s.callEntry.gpr .x1 = bp s₀ := (State.callEntry_gpr _ (by decide)).trans h.x1
  have hwr : s.wr = [stR s₀, tR s₀, bR s₀] := by rw [h.wr, hp.wr]
  have hrd : s.rd = [dR s₀] := by rw [h.rd, hp.rd]
  refine WP.call (k := Proof.ChaCha20.blockAArch64) v.ok
    (rd := [stR s₀]) (wr := [b256 s₀]) ?_ ?_ ?_ ?_ v.noFrames
  · simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, (hp.st_b.sub_right (b256_sub s₀)).symm⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · intro s₂ hrd₂ hwr₂ _ hf hcs hkeep hpost
    have hst : stateAt s₂.mem (st s₀) = stateAt s.mem (st s₀) :=
      stateAt_frame hf (by simpa using hp.st_b.sub_right (b256_sub s₀))
    simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, h.cnt] at hpost
    refine ⟨⟨by rw [hkeep .x0 (by decide) (v.keeps _ (by simp)), h.x0],
      by rw [hkeep .x1 (by decide) (v.keeps _ (by simp)), h.x1],
      by rw [hcs .x19 (by simp [preserved]) (by decide), h.x19],
      by rw [hcs .x20 (by simp [preserved]) (by decide), h.x20],
      by rw [hcs .x27 (by simp [preserved]) (by decide), h.x27],
      by rw [hrd₂, h.rd], by rw [hwr₂, h.wr], by rw [hst, h.cnt],
      h.data.frame hf (by simpa using hp.t_b.sub_right (b256_sub s₀)),
      h.src.frame hf (by simpa using hp.d_b.sub_right (b256_sub s₀)),
      h.saved.frame hf (by simpa using savR_b256 s₀)⟩, fun t ht => ?_⟩
    rw [← serialize_stateAt s₂.mem (bp s₀) ht, hpost]

/-! ## The bytes of block `j` -/

/-- Before byte `i` of block `j`. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = bp s₀
  x19 : s.gpr .x19 = dp s₀ + BitVec.ofNat 64 (P s₀ j + i)
  x27 : s.gpr .x27 = tp s₀ + BitVec.ofNat 64 (P s₀ j + i)
  x7 : s.gpr .x7 = bp s₀ + BitVec.ofNat 64 i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (C s₀ j - i)
  x20 : s.gpr .x20 = BitVec.ofNat 64 (L s₀ - P s₀ j - C s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : Dst s₀ (P s₀ j + i) s.mem
  src : Src s₀ (P s₀ j + i) s.mem
  saved : Saved s₀ s.mem
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

theorem sel_ok {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) {s : State} (h : AInv s₀ j s) :
    WP isa (.seq (.block [.lsr .x .x9 .x20 6, mov .x2 .x20])
      (.seq (.ite (.zero .x .x9) (.block []) (.block [.movz .x .x2 64 0]))
        (.block [.sub .x .x20 .x20 .x2, mov .x7 .x1]))) s (IInv s₀ j 0) := by
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have hx9 : s₂.gpr .x9 = BitVec.ofNat 64 ((L s₀ - P s₀ j) / 64) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.x20, ofNat_shr6 (by lit_omega)]
  have hx2 : s₂.gpr .x2 = BitVec.ofNat 64 (L s₀ - P s₀ j) := by
    rw [u₂.gpr, u₁.other _ (by decide), h.x20]
  refine WP.seq (WP.mono (Q := fun s₃ : State => s₃.gpr .x2 = BitVec.ofNat 64 (C s₀ j) ∧
      (∀ r, r ≠ .x2 → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr) ?_
    fun s₃ ⟨f₁, f₂, f₃, f₄, f₅⟩ => ?_)
  · refine WP.ite (decide ((L s₀ - P s₀ j) / 64 = 0))
      (by have e : isa.eval (.zero .x .x9) s₂ = some (s₂.gpr .x9 == 0) := eval_zero s₂ .x9
          rw [e, hx9, ofNat_beq_zero (by lit_omega)])
      (fun ht => WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩)
      (fun hf => wp_movz fun s₃ u₃ => WP.block_nil ⟨?_, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩)
    · simp only [decide_eq_true_eq] at ht
      rw [hx2, show C s₀ j = L s₀ - P s₀ j by omega]
    · simp only [decide_eq_false_iff_not] at hf
      rw [u₃.gpr, show C s₀ j = 64 by omega]; rfl
  · refine wp_sub fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
    have g : ∀ r, r ≠ .x2 → r ≠ .x20 → r ≠ .x7 → r ≠ .x9 → s₅.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ => by rw [u₅.other r h₃, u₄.other r h₂, f₂ r h₁, u₂.other r h₁, u₁.other r h₄]
    have gm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, f₃, u₂.mem, u₁.mem]
    refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide), h.x0],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.x1],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.x19, Nat.add_zero],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.x27, Nat.add_zero],
      by rw [u₅.gpr, u₄.other _ (by decide), f₂ _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.x1]; simp,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), f₁, Nat.sub_zero],
      by rw [u₅.other _ (by decide), u₄.gpr, f₂ _ (by decide), f₁, u₂.other _ (by decide),
        u₁.other _ (by decide), h.x20, sub_ofNat (by lit_omega)],
      by rw [u₅.rd, u₄.rd, f₄, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, f₅, u₂.wr, u₁.wr, h.wr],
      by rw [gm, h.cnt], fun k hk => by rw [gm, h.data k hk, Nat.add_zero],
      fun k hk hk' => by rw [gm]; exact h.src k hk (by omega),
      by rw [gm]; exact h.saved, fun t ht => by rw [gm]; exact h.ks t ht⟩

/-! ## One byte -/

def xorBody : List Instr :=
  [.ldrb .x6 .x19 0, .ldrb .x8 .x7 0, .logic .eor .w .x6 .x6 .x8, .strb .x6 .x27 0,
    .addImm .x .x19 .x19 1, .addImm .x .x27 .x27 1, .addImm .x .x7 .x7 1, .subImm .x .x2 .x2 1]

theorem xorLoop_eq : xorLoop = .loop (.block xorBody) (.nonzero .x .x2) := rfl

/-- `P j = 64 j` while blocks remain. -/
theorem P_eq {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ j = 64 * j := by
  simp only [P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j) :
    (KS s₀).getD (P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD i 0 := by
  have hP := P_eq hj
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  rw [KS, keystream_getD _ (by lit_omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

theorem xor_step {s₀ : State} (hp : TPre s₀) {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j)
    {s : State} (h : IInv s₀ j i s) : WP isa (.block xorBody) s (IInv s₀ j (i + 1)) := by
  have hL := L_lt s₀
  have hk : P s₀ j + i < L s₀ := by have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl; omega
  have hC64 : C s₀ j ≤ 64 := Nat.min_le_left _ _
  have cd : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    contains_off (by lit_omega) (by lit_omega)
  have ct : (tR s₀).Contains (tp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    contains_off (by lit_omega) (by lit_omega)
  have cb : (bR s₀).Contains (bp s₀ + BitVec.ofNat 64 i) 1 := contains_off (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cd⟩
  have i₂ : InRegions (s.rd ++ s.wr) (bp s₀ + BitVec.ofNat 64 i) 1 :=
    ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  have o₁ : InRegions s.wr (tp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨tR s₀, by simp [h.wr, hp.wr], ct⟩
  unfold xorBody
  refine wp_ldrb (a := dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) (by decide)
    (by rw [h.x19]; exact BitVec.add_zero _) i₁ fun s₁ u₁ => ?_
  refine wp_ldrb (a := bp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), h.x7]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr]; exact i₂) fun s₂ u₂ => ?_
  refine wp_eor32 fun s₃ u₃ => ?_
  refine wp_strb (a := tp s₀ + BitVec.ofNat 64 (P s₀ j + i)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x27]
        exact BitVec.add_zero _)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o₁) fun s₄ g₄ => ?_
  refine wp_addImm (by decide) fun s₅ u₅ => wp_addImm (by decide) fun s₅' u₅' =>
    wp_addImm (by decide) fun s₆ u₆ => wp_subImm (by decide) fun s₇ u₇ => WP.block_nil ?_
  have hv : (s₃.gpr .x6).setWidth 8 =
      D0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, xor_setWidth,
      h.src _ hk (Nat.le_refl _), h.ks i (by lit_omega), ks_eq hj hi]
  have hm : s₇.mem = s.mem.writeW (tp s₀ + BitVec.ofNat 64 (P s₀ j + i))
      (D0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0) := by
    rw [u₇.mem, u₆.mem, u₅'.mem, u₅.mem, g₄.mem, hv, u₃.mem, u₂.mem, u₁.mem]
  have hfd : Frame [tR s₀] s.mem s₇.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ct
  have g : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x19 → r ≠ .x27 → r ≠ .x7 → r ≠ .x2 →
      s₇.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₃' h₄ h₅ => by
      rw [u₇.other r h₅, u₆.other r h₄, u₅'.other r h₃', u₅.other r h₃, g₄.gpr, u₃.other r h₁,
        u₂.other r h₂, u₁.other r h₁]
  have hd : Dst s₀ (P s₀ j + (i + 1)) s₇.mem := fun k hk' => by
    rw [hm, writeW8_apply]
    by_cases he : k = P s₀ j + i
    · subst he; simp
    · simp only [off_ne (tp s₀) (by lit_omega) (by lit_omega) he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < P s₀ j + i
      · simp [h₁, show k < P s₀ j + (i + 1) by omega]
      · simp [h₁, show ¬ k < P s₀ j + (i + 1) by omega]
  refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x1],
    ?_, ?_, ?_, ?_,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅'.other _ (by decide),
      u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.x20],
    by rw [u₇.rd, u₆.rd, u₅'.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅'.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [stateAt_frame hfd (by simpa using hp.st_t), h.cnt], hd,
    src_step hp (by omega) h.src hfd hd,
    h.saved.frame hfd (by simpa using (hp.t_b.sub_right (savR_sub s₀)).symm), fun t ht => ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅'.other _ (by decide), u₅.gpr, g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x19, add_ofNat,
      Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅'.gpr, u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x27, add_ofNat,
      Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅'.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x7, add_ofNat]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅'.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x2,
      sub_ofNat (by lit_omega), Nat.sub_sub]
  · rw [hfd.bytes (R := bR s₀) (by simpa using hp.t_b.symm) (show 320 ≤ 2 ^ 64 by omega)
      (show t < 320 by omega)]
    exact h.ks t ht

/-! ## A whole block -/

theorem xorLoop_ok {s₀ : State} (hp : TPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) : WP isa xorLoop s (IInv s₀ j (C s₀ j)) := by
  have hpos : 0 < C s₀ j := by simp only [C]; omega
  have hC : C s₀ j ≤ 64 := by simp only [C]; omega
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = C s₀ j - i ∧ i < C s₀ j ∧ IInv s₀ j i s
  have hstep : ∀ n s, Inv n s → WP isa (.block xorBody) s (fun s' =>
      (isa.eval (.nonzero .x .x2) s' = some false ∧ IInv s₀ j (C s₀ j) s') ∨
      (isa.eval (.nonzero .x .x2) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (xor_step hp hj hi hI) fun s' h' => ?_
    have hz := eval_nonzero_ofNat s' .x2 (by lit_omega) h'.x2
    by_cases hl : i + 1 = C s₀ j
    · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
    · exact .inr ⟨by rw [hz]; simp; omega, C s₀ j - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (C s₀ j) s ⟨0, by simp, hpos, h⟩

/-! ## The end of a block -/

def nextInstrs : List Instr := [.ldr .w .x3 .x0 48, .addImm .w .x3 .x3 1, .str .w .x3 .x0 48]

theorem P_succ {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ (j + 1) = P s₀ j + C s₀ j := by
  simp only [P, C] at *; omega

theorem next_ok {s₀ : State} (hp : TPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j (C s₀ j) s) : WP isa (.block nextInstrs) s (OInv s₀ (j + 1)) := by
  have hP := P_succ hj
  have c₁ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 48) 4 := contains_off (by lit_omega) (by lit_omega)
  unfold nextInstrs
  refine wp_ldr32 (by decide) (by rw [h.x0]) ⟨stR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩
    fun s₁ u₁ => wp_addImm32 (by decide) fun s₂ u₂ => ?_
  refine wp_str32 (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.x0])
    ⟨stR s₀, by simp [u₂.wr, u₁.wr, h.wr, hp.wr], c₁⟩ fun s₃ g₃ => WP.block_nil ?_
  have hv : s.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) j)[12]'(by decide) := by
    rw [← h.cnt]; simp [stateAt]
  have hm : s₃.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 48) ((ctr (S0 s₀) j)[12]'(by decide) + 1) := by
    rw [g₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, inc_setWidth, hv]
  have hfs : Frame [stR s₀] s.mem s₃.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have g : ∀ r, r ≠ .x3 → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃.gpr, u₂.other r hr, u₁.other r hr]
  refine ⟨by rw [g _ (by decide), h.x0], by rw [g _ (by decide), h.x1],
    by rw [g _ (by decide), h.x19, hP], by rw [g _ (by decide), h.x20, hP, Nat.sub_sub],
    by rw [g _ (by decide), h.x27, hP],
    by rw [g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [g₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [hm, stateAt_writeW_counter, h.cnt, ctr_succ], ?_, ?_,
    h.saved.frame hfs (by simpa using (hp.st_b.sub_right (savR_sub s₀)).symm)⟩
  · rw [hP]; exact h.data.frame hfs (by simpa using hp.st_t.symm)
  · rw [hP]; exact h.src.frame hfs (by simpa using hp.st_d.symm)

theorem body_eq (v : BlockImpl) : bodyWith v.callee =
    .seq (.call v.callee.name v.callee.code)
    (.seq (.block [.lsr .x .x9 .x20 6, mov .x2 .x20])
    (.seq (.ite (.zero .x .x9) (.block []) (.block [.movz .x .x2 64 0]))
    (.seq (.block [.sub .x .x20 .x20 .x2, mov .x7 .x1])
    (.seq xorLoop (.block nextInstrs))))) := rfl

theorem body_ok (v : BlockImpl) {s₀ : State} (hp : TPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : OInv s₀ j s) : WP isa (bodyWith v.callee) s (OInv s₀ (j + 1)) := by
  rw [body_eq v]
  refine WP.seq (WP.mono (call_ok v hp h) fun s₁ h₁ => ?_)
  have hs := sel_ok hj h₁
  rw [WP.seq_iff] at hs
  rw [WP.seq_iff]
  refine WP.mono hs fun s₂ h₂ => ?_
  rw [WP.seq_iff] at h₂
  rw [WP.seq_iff]
  refine WP.mono h₂ fun s₃ h₃ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₃ fun s₄ h₄ => ?_
  exact WP.seq (WP.mono (xorLoop_ok hp hj h₄) fun s₅ h₅ => next_ok hp hj h₅)

/-! ## The epilogue -/

/-- What the code guarantees on return, beyond the registers it never writes. -/
def Post (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.gpr .x0 = st s₀ ∧ s'.gpr .x1 = bp s₀ ∧
    Proof.ChaCha20.xorAArch64.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : TPre s₀) {j : Nat} (hj : P s₀ j = L s₀) {s : State}
    (h : OInv s₀ j s) : WP isa (.block restore) s (Post s₀) := by
  refine WP.mono (Spill.restore_wp h.x1 (by decide) (by decide) (fun p hp' =>
      have hb : p.2 + 8 ≤ 320 := by revert p; decide
      ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], contains_off hb (by omega)⟩)
    h.saved) fun s₃ h₃ => ⟨h₃.gpr, by rw [h₃.other _ (by decide), h.x0],
      by rw [h₃.other _ (by decide), h.x1], ?_⟩
  · refine bytesAt_xor_to (length_keystream _ _) fun k hk => ?_
    have hk' : k < L s₀ := hk
    rw [h₃.mem, h.data k hk']
    simp only [show k < P s₀ j by omega, ite_true]

/-! ## The whole function -/

theorem xor_eq (v : BlockImpl) : (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) =
    .seq (.block (save ++ [mov .x19 .x1, mov .x20 .x2, mov .x27 .x4, mov .x1 .x3]))
    (.seq (.ite (.zero .x .x20) (.block []) (.loop (bodyWith v.callee) (.nonzero .x .x20))) (.block restore)) := rfl

theorem main_ok (v : BlockImpl) {s₀ : State} (hp : TPre s₀) : WP isa (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) s₀ (Post s₀) := by
  have hL := L_lt s₀
  rw [xor_eq v]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => epilogue_ok hp hj h₂)
  have hz : isa.eval (.zero .x .x20) s₁ = some (decide (L s₀ = 0)) := by
    have e : isa.eval (.zero .x .x20) s₁ = some (s₁.gpr .x20 == 0) := eval_zero s₁ .x20
    rw [e, h₁.x20, ofNat_beq_zero (by lit_omega)]
    simp [P]
  refine WP.ite (decide (L s₀ = 0)) hz (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil ⟨0, by simp [P, h], h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s => ∃ j, n = L s₀ - P s₀ j ∧ P s₀ j < L s₀ ∧ OInv s₀ j s
    have hstep : ∀ n s, Inv n s → WP isa (bodyWith v.callee) s (fun s' =>
        (isa.eval (.nonzero .x .x20) s' = some false ∧ ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s') ∨
        (isa.eval (.nonzero .x .x20) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, hI⟩
      refine WP.mono (body_ok v hp hj hI) fun s' h' => ?_
      have hz' := eval_nonzero_ofNat s' .x20 (by lit_omega) h'.x20
      have hP := P_succ hj
      have hC : 0 < C s₀ j := by simp only [C]; omega
      have hle : P s₀ (j + 1) ≤ L s₀ := by simp only [P]; omega
      by_cases hl : L s₀ - P s₀ (j + 1) = 0
      · exact .inl ⟨by rw [hz']; simp [hl], j + 1, by omega, h'⟩
      · exact .inr ⟨by rw [hz']; simp [hl], L s₀ - P s₀ (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (L s₀ - P s₀ 0) s₁ ⟨0, rfl, by simp [P]; omega, h₁⟩

/-- The callee-saved registers the code never writes (`x19`, `x20`, `x27` and
`x30` are saved and restored). -/
def untouched : List Reg := [.x21, .x22, .x23, .x24, .x25, .x26, .x28]

theorem untouched_ok (v : BlockImpl) : ∀ r ∈ untouched,
    ∀ i ∈ instrs (Impl.ChaCha20.AArch64.Xor.xorWith v.callee), clobbers i r = false := v.xorKeeps

theorem correct (v : BlockImpl) {s₀ : State} (hp : TPre s₀) :
    ∃ t s', Exec isa (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) s₀ t s' ∧ abiPreserved s₀ s' ∧
      (Proof.ChaCha20.xorAArch64.post s₀ s' ∧ s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3) := by
  obtain ⟨t, s', he, ⟨hsv, h0, h1, hpost⟩⟩ := main_ok v hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he v.xorKeepsV⟩, hpost, h0, h1⟩
  have hu : ∀ r ∈ untouched, s'.gpr r = s₀.gpr r := fun r hr =>
    Exec.gpr (untouched_ok v r hr) he (.inr (by
      simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.x19, 256) (by simp [saved])
  · exact hsv (.x20, 264) (by simp [saved])
  · exact hu _ (by simp [untouched])
  · exact hu _ (by simp [untouched])
  · exact hu _ (by simp [untouched])
  · exact hu _ (by simp [untouched])
  · exact hu _ (by simp [untouched])
  · exact hu _ (by simp [untouched])
  · exact hsv (.x27, 280) (by simp [saved])
  · exact hu _ (by simp [untouched])
  · exact hsv (.x30, 272) (by simp [saved])

/-- `vg_chacha20_xor` returns with `x0` holding `state` and `x1` holding `buf`
(which was in `x3` on entry), for a caller that recomputes pointers from
them. -/
theorem xor_x1 (v : BlockImpl) (s : State) (hs : Proof.ChaCha20.xorAArch64.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorAArch64.post s s' ∧ s'.gpr .x0 = s.gpr .x0 ∧ s'.gpr .x1 = s.gpr .x3) :=
  correct v (TPre.of s hs)

/-- `xor_x1` with the general-purpose registers' part of the ABI. -/
theorem xor_gpr (v : BlockImpl) (s : State) (hs : Proof.ChaCha20.xorAArch64.pre s) :
    WP isa (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) s fun u => GprAbi s u ∧
      Proof.ChaCha20.xorAArch64.post s u ∧ u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 :=
  (xor_x1 v s hs).imp fun _ ⟨u, he, ha, hu⟩ => ⟨u, he, ⟨ha.1, ha.2.1⟩, hu⟩

/-! ## The rest of the data

The vector kernels leave the data after their whole chunks to code proven
against the contract on its own entry (this code, or `Small.short`), run on
the rest of the source and of the destination. -/

/-- The source and the destination after their first `n` bytes. -/
abbrev srcRest (s₀ : State) (n : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 n, L s₀ - n⟩
abbrev dstRest (s₀ : State) (n : Nat) : Region := ⟨tp s₀ + BitVec.ofNat 64 n, L s₀ - n⟩

theorem ctr_ctr (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.getElem_set_self, Vector.set_set, BitVec.ofNat_add, BitVec.add_assoc]

/-- A byte of the destination, from the source XORed with a keystream. -/
theorem bytes_of_to {m m' : Mem} {p q : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' q n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (q + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega),
    Option.getD_some]
  simpa using e

theorem not_rest {s₀ : State} {n k : Nat} (hk : k < n) (hn : n ≤ L s₀) :
    ¬ (dstRest s₀ n).Contains (tp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := L_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

/-- An implementation `c` of the contract (with `x0` and `x1` on return as
`Xor.xor`'s), run on the rest after the first `n` bytes (a multiple of 64),
from a state with the source and the destination done up to there: the
contract's postcondition for the whole. -/
theorem rest_ok {c : Prog isa} (hnf : c.noFrames = true) {s₀ s : State} {n : Nat}
    (hc : ∀ s, Proof.ChaCha20.xorAArch64.pre s → L s = L s₀ - n → WP isa c s fun u => GprAbi s u ∧
      Proof.ChaCha20.xorAArch64.post s u ∧ u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3)
    (hp : TPre s₀) (hn : n ≤ L s₀) (h64 : n % 64 = 0)
    (h0 : s.gpr .x0 = st s₀) (h1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 n)
    (h2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - n)) (h3 : s.gpr .x3 = bp s₀)
    (h4 : s.gpr .x4 = tp s₀ + BitVec.ofNat 64 n) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hcnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (n / 64))
    (hd : Dst s₀ n s.mem) (hs : Src s₀ n s.mem) :
    WP isa c s fun u => GprAbi s u ∧ Proof.ChaCha20.xorAArch64.post s₀ u ∧
      u.gpr .x0 = s₀.gpr .x0 ∧ u.gpr .x1 = s₀.gpr .x3 := by
  have hL := L_lt s₀
  have hN : (BitVec.ofNat 64 (L s₀ - n)).toNat = L s₀ - n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ts : Region.Sub (srcRest s₀ n) (dR s₀) := Offset.sub_base _ (by omega)
  have tt : Region.Sub (dstRest s₀ n) (tR s₀) := Offset.sub_base _ (by omega)
  have hpre : Proof.ChaCha20.xorAArch64.pre
      (s.withRegions [srcRest s₀ n] [stR s₀, dstRest s₀ n, bR s₀]) := by
    simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, h0, h1, h2, h3, h4, hN]
    refine ⟨trivial, trivial, hp.st_d.sub_right ts, hp.st_t.sub_right tt, hp.st_b, hp.d_b.sub_left ts,
      hp.t_b.sub_left tt, ?_, ?_, ?_⟩
    · rcases hp.alias with he | hdis
      · exact .inl (by rw [he])
      · exact .inr ((hdis.sub_left ts).sub_right tt)
    · have := hp.nowrap; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · have := hp.tnowrap; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hcw : Covers [stR s₀, dstRest s₀ n, bR s₀] s.wr := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨tR s₀, by simp, n, rfl, by dsimp; omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, by simp⟩
  have hcr : Covers [srcRest s₀ n] s.rd := by
    rw [hrd, hp.rd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨dR s₀, by simp, n, rfl, by dsimp; omega⟩
  refine WP.narrow (hc _ hpre (by simp only [L, State.withRegions_gpr, h2, hN]))
    (Covers.append hcr hcw) hcw ?_ hnf
  intro u _ _ _ hf ⟨ha, hpost, hu0, hu1⟩
  simp only [GprAbi, State.withRegions_gpr, State.withRegions_sp] at ha
  simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_mem,
    h0, h1, h2, h4, hN, hcnt] at hpost
  simp only [State.withRegions_gpr] at hu0 hu1
  refine ⟨ha, ?_, hu0.trans h0, hu1.trans h3⟩
  refine bytesAt_xor_to (length_keystream _ _) fun k hk => ?_
  have hk' : k < L s₀ := hk
  by_cases hkn : k < n
  · have ct : (tR s₀).Contains (tp s₀ + BitVec.ofNat 64 k) 1 :=
      contains_off (by lit_omega) (by lit_omega)
    rw [hf _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact fun h => hp.st_t _ h ct
      · exact not_rest hkn hn
      · exact fun h => hp.t_b _ ct h), hd k hk', ite_eq_left hkn]
  · have x := bytes_of_to (length_keystream _ _) hpost (k := k - n)
      (show k - n < L s₀ - n by omega)
    rw [Offset.add_add, Offset.add_add, show n + (k - n) = k by omega, hs k hk' (by omega),
      keystream_getD _ (by omega), ctr_ctr,
      show n / 64 + (k - n) / 64 = k / 64 by omega, show (k - n) % 64 = k % 64 by omega] at x
    rw [x, keystream_getD _ hk']

/-! ## Constant time -/

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.ChaCha20.xorAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem xor_correct (v : BlockImpl) (s : State) (hs : Proof.ChaCha20.xorAArch64.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorAArch64.post s s' :=
  (correct v (TPre.of s hs)).imp fun _ ⟨s', he, ha, hpost, _⟩ => ⟨s', he, ha, hpost⟩

theorem xor_ct (v : BlockImpl) : ConstantTime isa Proof.ChaCha20.xorAArch64.pre Proof.ChaCha20.xorAArch64.pub
    (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) := by
  obtain ⟨h, hh⟩ := v.xorTaint
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => agree₀ hp) hh

end VG.Proof.ChaCha20.AArch64.Xor
