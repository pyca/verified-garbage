module

public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Save
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Init
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Poly1305.BlocksScratch
meta import VerifiedGarbage.Proof.Poly1305.PPC64LE.Save
meta import VerifiedGarbage.Proof.Poly1305.PPC64LE.Init
meta import VerifiedGarbage.Proof.Poly1305.PPC64LE.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Poly1305.BlocksScratch

/-!
# Poly1305 on PPC64LE: `blocks`

As on AArch64 (`Proof/Poly1305/AArch64/Blocks.lean`), between `save` and
`restore` (`Proof/Poly1305/PPC64LE/Save.lean`): the code after `save` is
proved from the state `save` leaves, which agrees with the state on entry
on the state's first 56 bytes and the blocks.
-/

@[expose] public section

namespace VG.Proof.Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.Poly1305.PPC64LE
open VG.Proof.Poly1305.Radix26
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

/-! ## Common to `blocks` and `finalize` -/

section
variable (s₀ : State)
/-- The state, on entry. -/
abbrev st : Addr := s₀.gpr .r3
/-- The clamped `r`. -/
abbrev Rn : Nat := Rk s₀.mem (st s₀)
/-- The accumulator on entry. -/
abbrev A0 : Nat := leNum (bytesAt s₀.mem (st s₀) 24)
end

/-- The memory `setup` leaves. -/
structure Mem₁ (s₀ : State) (m₁ : Mem) : Prop where
  frame : Frame [cR (st s₀)] s₀.mem m₁
  coefs : Coefs m₁ (st s₀) (Rn s₀)

theorem cR_sub_wR (st : Addr) : Region.Sub (cR st) (wR st) :=
  Offset.sub st (by decide) (by decide)

theorem cR_sub_sR (st : Addr) : Region.Sub (cR st) (sR st) := sub_sR st (by decide)

/-- The accumulator on entry is less than `p` if the state represents a message. -/
theorem A0_lt {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) : A0 s₀ < P := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2] at this
  exact this

/-- The key of a state that represents a message, and its clamped `r`. -/
theorem repr_key {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    bytesAt s₀.mem (off (st s₀) 24) 32 = key := h.2.1

theorem repr_acc {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    accumulate (Rn s₀) msg = A0 s₀ := by
  rw [A0, h.2.2, ← repr_key h, clamp_key]

/-- The words of `h` stored. -/
def storeHm (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) : Mem :=
  ((m.writeW (off st 0) w0).writeW (off st 8) w1).writeW (off st 16) w2

set_option simprocs false in
theorem storeH_ok (s : State) (hw : sR (s.gpr .r3) ∈ s.wr) :
    WP isa (.block storeH) s fun s' =>
      s'.mem = storeHm s.mem (s.gpr .r3) (s.gpr .r18) (s.gpr .r19) (s.gpr .r0) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .r3) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  simp only [off] at o0 o8 o16
  apply WP.of_runBlock
  simp (config := {decide := true}) only [storeH, runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d, o0, o8, o16, Option.some.injEq, exists_eq_left']
  trivial

theorem storeHm_frame {st : Addr} {r : Region} {m m' : Mem} (hf : Frame [hR st, r] m m')
    (w0 w1 w2 : BitVec 64) : Frame [hR st, r] m (storeHm m' st w0 w1 w2) := by
  have c : ∀ d, d + 8 ≤ 24 → (hR st).Contains (off st d) (64 / 8) := fun d hd => hR_contains st hd
  exact ((hf.writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
    (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))

set_option simprocs false in
theorem storeHm_acc (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) :
    leNum (bytesAt (storeHm m st w0 w1 w2) st 24) = w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat := by
  rw [leNum_acc]
  simp (config := {decide := true}) only [w64, storeHm, readW_writeW_off,
    Mem.readW_writeW_self64]

/-! ## `blocks` -/

section
variable (s₀ : State)
abbrev bp : Addr := s₀.gpr .r4
abbrev nb : Nat := (s₀.gpr .r5).toNat
abbrev blR : Region := ⟨bp s₀, 16 * nb s₀⟩
/-- The working space. -/
abbrev scr : Addr := s₀.gpr .r6
/-- The first `i` blocks. -/
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem (bp s₀) (16 * i)
/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (16 * i)
end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀), savR (scr s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  st_scr : (sR (st s₀)).Disjoint (savR (scr s₀))
  bl_scr : (blR s₀).Disjoint (savR (scr s₀))
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64

theorem BPre.of (s₀ : State) (h : Proof.Poly1305.blocksPPC64LE.pre s₀) : BPre s₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem BPre.congr {s₀ s : State} (hp : BPre s₀) (h3 : s.gpr .r3 = s₀.gpr .r3)
    (h4 : s.gpr .r4 = s₀.gpr .r4) (h5 : s.gpr .r5 = s₀.gpr .r5) (h6 : s.gpr .r6 = s₀.gpr .r6)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : BPre s := by
  obtain ⟨a, b, c, d, e, f⟩ := hp
  simp only [blR, sR, savR, st, bp, nb, scr] at a b c d e f
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [blR, sR, savR, st, bp, nb, scr, h3, h4, h5, h6, hrd, hwr]
  exacts [a, b, c, d, e, f]

/-- What holds between blocks, after `i` of them, with the memory `m₁` left
by `setup`. -/
structure Common (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r21 : s.gpr .r21 = s₀.gpr .r21
  mask : s.gpr .r20 = M26
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  acc : A0 s₀ < P → hv s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ i) % P ∧ Bounds s

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop extends Common s₀ m₁ i s where
  r4 : s.gpr .r4 = blkAddr s₀ i
  r5 : s.gpr .r5 = BitVec.ofNat 64 (nb s₀ - i)

namespace BPre
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  have := (bp s₀).isLt
  by_contra h
  refine hp.st_bl (st s₀) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.zero_add, Nat.reduceLeDiff]) ?_
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [h, this]

theorem blk_contains {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 d) 8 := by
  have := hp.nb_lt
  rw [blkAddr, Offset.add_add]
  exact contains_off (by omega_using [hi, hd]) (by omega_using [hi, hd, this])

/-- Block words, in memory the code has written only in the coefficients. -/
theorem blk_word {m : Mem} (hf : Frame [cR (st s₀)] s₀.mem m) {i d : Nat} (hi : i < nb s₀)
    (hd : d + 8 ≤ 16) :
    m.readW (blkAddr s₀ i + BitVec.ofNat 64 d) 64 = s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 d) 64 :=
  hf.readW (hp.blk_contains hi hd) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.st_bl.symm.sub_right (cR_sub_sR _)) (by decide)

theorem coefIn {s : State} (hx0 : s.gpr .r3 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CoefIn s := fun off h₁ h₂ => by
  rw [hrd, hwr, hx0, hp.wr]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, contains_off (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂])⟩

end BPre

set_option simprocs false in
theorem advance_ok (s : State) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .r4 = s.gpr .r4 + BitVec.ofNat 64 16 ∧ s'.gpr .r5 = s.gpr .r5 - BitVec.ofNat 64 1 ∧
      Keeps [.r4, .r5] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, runBlock_cons, runStep_some, runBlock_nil,
    exec_addi (show Reg.r4 ≠ .r0 by decide) (show 16 < 2 ^ 15 by decide),
    exec_subi (show Reg.r5 ≠ .r0 by decide) (show 1 ≤ 2 ^ 15 by decide), write_gpr, ite_true,
    ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [write_gpr, hr.2, hr.1, ite_false]

/-- The value of block `i`, with the `0x01` byte appended: its two words and `2¹²⁸`. -/
theorem block_value {s₀ : State} (hp : BPre s₀) {m : Mem} (hf : Frame [cR (st s₀)] s₀.mem m)
    {i : Nat} (hi : i < nb s₀) :
    w64 m (blkAddr s₀ i) 0 + 2 ^ 64 * w64 m (blkAddr s₀ i) 8 + 2 ^ 128 * true.toNat =
      leNum (bytesAt s₀.mem (blkAddr s₀ i) 16 ++ [0x01]) := by
  simp only [w64]
  rw [hp.blk_word hf hi (by decide), hp.blk_word hf hi (by decide), Poly1305.leNum_append,
    Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

theorem blks_succ (s₀ : State) (i : Nat) :
    blks s₀ (i + 1) = blks s₀ i ++ bytesAt s₀.mem (blkAddr s₀ i) 16 := by
  simp only [blks, blkAddr]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega_using [], Poly1305.bytesAt_add]

theorem bounds_eq {s s' : State} (h : ∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11], s'.gpr r = s.gpr r) :
    hv s' = hv s ∧ (Bounds s → Bounds s') := by
  have e : ∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11], v s' r = v s r := fun r hr => by simp only [v, h r hr]
  refine ⟨by simp only [hv, e .r7 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false]), e .r8 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), e .r9 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), e .r10 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]),
    e .r11 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true])], fun hb => ?_⟩
  simp only [Bounds, e .r7 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false]), e .r8 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), e .r9 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), e .r10 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]),
    e .r11 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true])]
  exact hb

theorem body_ok {s₀ : State} (hp : BPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {i : Nat}
    (hi : i < nb s₀) {s : State} (hL : LInv s₀ m₁ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .d .r5) s' = some false ∧ Common s₀ m₁ (nb s₀) s') ∨
      (eval (.nonzero .d .r5) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ m₁ (i + 1) s') := by
  have hin : ∀ d : Nat, d + 8 ≤ 16 →
      InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [hL.rd, hL.wr, hL.r4, hp.rd]
    exact ⟨blR s₀, List.mem_append_left _ (List.mem_singleton_self _), hp.blk_contains hi hd⟩
  have hab := absorb_ok s true (Rk_lt _ _) hL.mask (by rw [hL.mem, hL.r3]; exact hm.coefs)
    (hp.coefIn hL.r3 hL.rd hL.wr) (hin 0 (by decide)) (hin (0 + 8) (by decide))
  rw [body]
  refine WP.block_append (WP.mono hab fun s₁ ⟨ha, k₁⟩ => ?_)
  refine WP.mono (advance_ok s₁) fun s₂ ⟨a₁, a₂, k₂⟩ => ?_
  have k := k₁.trans k₂
  have hc : Common s₀ m₁ (i + 1) s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun hA => ?_⟩
    · rw [k.gpr' (r := .r3), hL.r3]
    · rw [k.gpr' (r := .r21), hL.r21]
    · rw [k.gpr' (r := .r20), hL.mask]
    · rw [k.2.2.1, hL.rd]
    · rw [k.2.2.2, hL.wr]
    · rw [k.2.1, hL.mem]
    · obtain ⟨hv₀, hb⟩ := hL.acc hA
      obtain ⟨hv', hb'⟩ := ha hb
      obtain ⟨e₂, b₂⟩ := bounds_eq (s := s₁) (s' := s₂) fun r hr => k₂.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      refine ⟨?_, b₂ hb'⟩
      have h16 : (blks s₀ i).length % 16 = 0 := by
        simp only [blks, Poly1305.length_bytesAt]; omega_using []
      have hb1 : 0 < (bytesAt s₀.mem (blkAddr s₀ i) 16).length := by
        rw [Poly1305.length_bytesAt]; omega_using []
      have hb2 : (bytesAt s₀.mem (blkAddr s₀ i) 16).length ≤ 16 := by rw [Poly1305.length_bytesAt]
      rw [e₂, hv', hL.r4, hL.mem, block_value hp hm.frame hi, mod_step hv₀, blks_succ,
        Poly1305.absorbAll_append h16, Poly1305.absorbAll_block hb1 hb2]
  have hx2 : s₂.gpr .r5 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [a₂, k₁.gpr' (r := .r5), hL.r5, Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  have hev : eval (.nonzero .d .r5) s₂ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp only [Nat.sub_self, BitVec.ofNat_eq_ofNat, bne_self_eq_false], hlast ▸ hc⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, this, h'])] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega_using [hi, hne], { hc with r4 := ?_, r5 := hx2 }⟩
    rw [a₁, k₁.gpr' (r := .r4), hL.r4, blkAddr, blkAddr, Offset.add_add, Nat.mul_succ]

/-! ## Epilogue -/

theorem words_val (V : Nat) :
    V % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ 64 % 2 ^ 64) + 2 ^ 128 * (V / 2 ^ 128) = V := by omega_using []

theorem Mem₁.frame_wR {s₀ : State} {m₁ : Mem} (hm : Mem₁ s₀ m₁) :
    Frame [hR (st s₀), wR (st s₀)] s₀.mem m₁ :=
  hm.frame.sub fun r hr => ⟨wR (st s₀), by simp only [List.mem_cons, Region.mk.injEq, BitVec.add_right_eq_self, BitVec.reduceEq, Nat.reduceEqDiff, and_self, List.not_mem_nil, or_false, or_true], by
    simp only [List.mem_singleton] at hr; subst hr; exact cR_sub_wR _⟩

theorem epilogue_ok {s₀ : State} (hp : BPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s : State}
    (hc : Common s₀ m₁ (nb s₀) s) :
    WP isa (.block (reduce ++ pack ++ storeH)) s fun s' => Proof.Poly1305.blocksPPC64LE.post s₀ s' ∧
      s'.gpr .r3 = st s₀ ∧ s'.gpr .r21 = s₀.gpr .r21 ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [hR (st s₀), cR (st s₀)] s₀.mem s'.mem := by
  refine WP.block_append (WP.block_append (WP.mono (reduce_ok s hc.mask) fun s₁ ⟨hr, k₁⟩ =>
    WP.mono (pack_ok s₁) fun s₂ ⟨hp₂, k₂⟩ => ?_))
  have x0₂ : s₂.gpr .r3 = st s₀ := by rw [k₂.gpr', k₁.gpr', hc.r3]
  refine WP.mono (storeH_ok s₂ (by
    rw [k₂.2.2.2, k₁.2.2.2, hc.wr, hp.wr, x0₂]; exact List.mem_cons_self))
    fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ => ?_
  have mem₂ : s₂.mem = m₁ := by rw [k₂.2.1, k₁.2.1, hc.mem]
  rw [x0₂, mem₂] at m₃
  refine ⟨?_, by rw [g₃, x0₂], by rw [g₃, k₂.gpr', k₁.gpr', hc.r21], by rw [rd₃, k₂.2.2.1, k₁.2.2.1, hc.rd], by rw [wr₃, k₂.2.2.2, k₁.2.2.2, hc.wr],
    by rw [m₃]; exact storeHm_frame (hm.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; simp only [hr, List.mem_cons, List.not_mem_nil, or_false, or_true]) _ _ _⟩
  intro key msg hrep
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := hc.acc hA
  obtain ⟨hN, n0, n1, n2, n3, -⟩ := hr hb
  obtain ⟨w0, w1, w2⟩ := hp₂ n0 n1 n2 n3
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₃.mem := by
    rw [m₃]; exact storeHm_frame hm.frame_wR _ _ _
  have hlen := hrep.1
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hlen]
  · rw [← off_24, key_frame hf]; exact repr_key hrep
  · rw [m₃, storeHm_acc, ← repr_key hrep, clamp_key, Poly1305.accumulate_append hlen, repr_acc hrep]
    have hV : val5 (v s₁ .r7) (v s₁ .r8) (v s₁ .r9) (v s₁ .r10) (v s₁ .r11) =
        Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ (nb s₀)) := by
      rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
    change v s₂ .r18 + 2 ^ 64 * v s₂ .r19 + 2 ^ 128 * v s₂ .r0 = _
    rw [w0, w1, w2, words_val, hV]

/-! ## The whole function -/

/-- The nonvolatile registers the code does not use: never written. -/
def keepRegs : List Reg := [.r2, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- A preserved register is saved, or kept. -/
theorem preserved_cases : ∀ r ∈ preserved, (∃ i < 8, r = saved i) ∨ r ∈ keepRegs := by decide

theorem sR_56 (st : Addr) : Region.Sub ⟨st, 56⟩ (sR st) := Region.sub_prefix (by decide)

theorem hR_sub_sR (st : Addr) : Region.Sub (hR st) (sR st) := Region.sub_prefix (by decide)

/-- The state's first 56 bytes, which `save` does not write. -/
theorem save_repr {s₀ s₁ : State} (hs : Frame [savR (s₀.gpr .r6)] s₀.mem s₁.mem)
    (hd : (sR (s₀.gpr .r3)).Disjoint (savR (s₀.gpr .r6))) {key msg : List Byte}
    (h : Repr s₀.mem (s₀.gpr .r3) key msg) : Repr s₁.mem (s₀.gpr .r3) key msg := by
  refine Proof.Poly1305.repr_congr (fun i hi => ?_) h
  refine hs.bytes (R := ⟨s₀.gpr .r3, 56⟩) (fun r hr => ?_) (show (56 : Nat) ≤ 2 ^ 64 by decide) hi
  simp only [List.mem_singleton] at hr
  subst hr
  exact hd.sub_left (sR_56 _)

theorem blocks_correct {s₀ : State} (hp₀ : BPre s₀) :
    WP isa blocks s₀ fun s' => (∀ i < 8, s'.gpr (saved i) = s₀.gpr (saved i)) ∧
      Proof.Poly1305.blocksPPC64LE.post s₀ s' := by
  have hsv := save_ok s₀ (w := .r6) (by decide)
    (by rw [hp₀.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  refine WP.seq (WP.block_append (WP.mono hsv fun s₁ hs₁ => ?_))
  have hg : ∀ r ∈ [Reg.r3, .r4, .r5, .r6], s₁.gpr r = s₀.gpr r := fun r hr =>
    hs₁.gpr r (by revert r; decide)
  have hp : BPre s₁ := hp₀.congr (hg _ (by decide)) (hg _ (by decide)) (hg _ (by decide))
    (hg _ (by decide)) hs₁.rd hs₁.wr
  refine WP.mono (setup_ok s₁ (by rw [hp.wr]; exact List.mem_cons_self)) fun s₂ h₁ => ?_
  have hm : Mem₁ s₁ s₂.mem := ⟨h₁.frame, h₁.coefs⟩
  have hc₀ : Common s₁ s₂.mem 0 s₂ := ⟨h₁.gpr .r3 (by decide), h₁.gpr .r21 (by decide), h₁.mask,
    h₁.rd, h₁.wr, rfl, fun hA => by
      obtain ⟨e, b⟩ := h₁.acc hA
      refine ⟨?_, b⟩
      rw [e, show blks s₁ 0 = [] by simp only [blks, bytesAt, Nat.mul_zero, List.range_zero, List.map_nil], Poly1305.absorbAll_nil]⟩
  have x2₁ : s₂.gpr .r5 = s₁.gpr .r5 := h₁.gpr .r5 (by decide)
  refine WP.seq (WP.mono (Q := Common s₁ s₂.mem (nb s₁)) ?_ fun s₃ hc₃ => ?_)
  · refine WP.ite (s₂.gpr .r5 == 0) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq])
      (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₁ = 0 := by
        simp only [x2₁, beq_iff_eq] at h
        simp only [nb, h, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
      exact WP.block_nil (M := isa) (h0 ▸ hc₀)
    · have hpos : 0 < nb s₁ := by
        simp only [x2₁, beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₁ - i ∧ i < nb s₁ ∧ LInv s₁ s₂.mem i s
      have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
          (eval (.nonzero .d .r5) s' = some false ∧ Common s₁ s₂.mem (nb s₁) s') ∨
          (eval (.nonzero .d .r5) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
        rintro m s ⟨i, rfl, hi, hL⟩
        refine WP.mono (body_ok hp hm hi hL) fun s' h => ?_
        rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
        · exact .inl ⟨he, hc⟩
        · exact .inr ⟨he, nb s₁ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩
      have hL₀ : LInv s₁ s₂.mem 0 s₂ :=
        { hc₀ with
          r4 := by rw [h₁.gpr .r4 (by decide)]; simp only [blkAddr, Nat.mul_zero, BitVec.add_zero]
          r5 := by rw [x2₁]; simp only [nb, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] }
      exact WP.loop (M := isa) Inv hstep (nb s₁) s₂ ⟨0, rfl, hpos, hL₀⟩
  · refine WP.block_append (WP.mono (epilogue_ok hp hm hc₃)
      fun s₄ ⟨hpost, r3₄, r21₄, rd₄, wr₄, hf₄⟩ => ?_)
    have hst : st s₁ = s₀.gpr .r3 := hg _ (by decide)
    have hdj : ∀ r ∈ [hR (st s₁), cR (st s₁)], (savR (s₀.gpr .r6)).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp₀.st_scr.symm.sub_right (by rw [hst]; exact hR_sub_sR _)
      · exact hp₀.st_scr.symm.sub_right (by rw [hst]; exact cR_sub_sR _)
    have hsav : ∀ i < 8, s₄.mem.readW (off (s₀.gpr .r6) (8 * i)) 64 = s₀.gpr (saved i) := by
      intro i hi
      rw [hf₄.readW (r := savR (s₀.gpr .r6)) (w := 64) (sav_contains _ hi) hdj (by decide)]
      exact hs₁.saved i hi
    refine WP.mono (restore_ok s₄ (w := s₀.gpr .r6) (v := fun i => s₀.gpr (saved i))
      (by rw [r21₄, hs₁.r21])
      (by rw [wr₄, hp.wr]; exact List.mem_cons_of_mem _ (by rw [scr, hg _ (by decide)]; exact List.mem_cons_self))
      hsav)
      fun s' ⟨hr, _, hm', _, _⟩ => ⟨hr, fun key msg hrep => ?_⟩
    have h := hpost key msg (by rw [hg .r3 (by decide)]; exact save_repr hs₁.frame hp₀.st_scr hrep)
    rw [hg .r3 (by decide)] at h
    rw [hm']
    have hbl : bytesAt s₁.mem (s₁.gpr .r4) (16 * (s₁.gpr .r5).toNat) =
        bytesAt s₀.mem (s₀.gpr .r4) (16 * (s₀.gpr .r5).toNat) := by
      rw [hg .r4 (by decide), hg .r5 (by decide)]
      refine Proof.Poly1305.bytesAt_congr' fun i hi => hs₁.frame.bytes (R := blR s₀) (fun r hr => ?_)
        (Nat.le_of_lt hp₀.nb_lt) hi
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp₀.bl_scr
    rw [hbl] at h
    exact h

/-- A state satisfying the precondition (with no blocks). -/
def blocksSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 128⟩]

theorem blocks_untouched : Untouched blocks keepRegs :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem blocks_verified : Verified PPC64LE.target blocks Proof.Poly1305.blocksPPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ⟨blocksSat, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide⟩⟩
  · obtain ⟨t, s', he, hr, h⟩ := blocks_correct (BPre.of s hs)
    refine ⟨t, s', he, ⟨fun r hr' => ?_, Exec.sp he,
      Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩
    rcases preserved_cases r hr' with ⟨i, hi, rfl⟩ | hk'
    · exact hr i hi
    · exact Exec.gpr (blocks_untouched r hk') he
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Poly1305.PPC64LE
