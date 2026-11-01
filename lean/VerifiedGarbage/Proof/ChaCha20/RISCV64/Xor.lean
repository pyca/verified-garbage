module

import VerifiedGarbage.Proof.ChaCha20.RISCV64.Block
meta import VerifiedGarbage.Proof.ChaCha20.RISCV64.Block
public import VerifiedGarbage.Proof.ChaCha20.Keystream
meta import VerifiedGarbage.Proof.ChaCha20.Keystream
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Xor
meta import VerifiedGarbage.Impl.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.Proof.ChaCha20.Contract
meta import VerifiedGarbage.Proof.ChaCha20.Contract
meta import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.WriteBytes
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.ChaCha20.RISCV64
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Contract
public import VerifiedGarbage.Proof.ChaCha20.Spec
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# ChaCha20 keystream XOR on RISC-V

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/ChaCha20/PPC64LE/Xor.lean`), with the block counter read and
written a byte at a time and our caller's registers saved at `buf + 256`
rounded up to a multiple of 8.
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.RISCV64

/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it.
RISC-V contract for
`vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`:
XORs the first `len` bytes of the keystream of the state at `state` into the
`len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other; `data` does not wrap around the end of the
address space. The return address is in `ra`, and the code uses no stack.
The pointers and the length are public; the state and the data are
secret. -/
def xorRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 64⟩
    let data : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let buf : Region := ⟨s.gpr .a3, 320⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
        (keystream (stateAt s.mem (s.gpr .a0)) (s.gpr .a2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.RISCV64.Xor

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.RISCV64.ByteLoad
  VG.Impl.ChaCha20.RISCV64.Xor VG.Impl.Words.RISCV64
open VG.Proof.ChaCha20 (ctr ctr_zero ctr_succ keystream_getD length_keystream bytesAt_xor
  serialize_stateAt)
open VG.Proof.ChaCha20.RISCV64 (readW_writeW_out block_verified)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-! ## Arithmetic -/

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- `x >>> 6`, of a number below 2⁶⁴. -/
theorem ofNat_shr6 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 6 = BitVec.ofNat 64 (a / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The byte stored by `xor t3, t3, t4; sb t3, …` after two `lbu`s. -/
theorem xor_setWidth (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8) = a ^^^ b := by
  ext i hi; simp

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .a0
abbrev dp : Addr := s₀.gpr .a1
abbrev L : Nat := (s₀.gpr .a2).toNat
abbrev bp : Addr := s₀.gpr .a3
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev bR : Region := ⟨bp s₀, 320⟩
/-- How far `buf + 256` is below a multiple of 8. -/
abbrev q : Nat := pad (bp s₀ + BitVec.ofNat 64 256)
/-- Where our caller's registers are saved: `buf + 256`, rounded up. -/
abbrev sv : Addr := bp s₀ + BitVec.ofNat 64 256 + BitVec.ofNat 64 (q s₀)
abbrev savR : Region := ⟨bp s₀ + BitVec.ofNat 64 (256 + q s₀), 24⟩
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (L s₀)
/-- How many bytes of block `j` are used. -/
abbrev C (j : Nat) : Nat := min 64 (L s₀ - P s₀ j)
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .a2).isLt

theorem q_lt (s₀ : State) : q s₀ < 8 := pad_lt _

theorem sv_add (s₀ : State) (d : Nat) :
    sv s₀ + BitVec.ofNat 64 d = bp s₀ + BitVec.ofNat 64 (256 + q s₀ + d) := align_add _ _ _

theorem sv_al (s₀ : State) {d : Nat} (hd : d % 8 = 0) : (sv s₀ + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  align_al_add _ hd

theorem sav_contains (s₀ : State) {d : Nat} (hd : d + 8 ≤ 24) :
    (savR s₀).Contains (sv s₀ + BitVec.ofNat 64 d) 8 := by
  have := q_lt s₀
  rw [sv_add]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem sav_in (s₀ : State) {d : Nat} (hd : d + 8 ≤ 24) :
    (bR s₀).Contains (sv s₀ + BitVec.ofNat 64 d) 8 := by
  have := q_lt s₀
  rw [sv_add]
  exact Offset.contains_base _ (by omega) (by omega)

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀, bR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  st_b : (stR s₀).Disjoint (bR s₀)
  d_b : (dR s₀).Disjoint (bR s₀)
  nowrap : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorRISCV64.pre s₀) : XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Our caller's `s5` and `s6`, and our return address, saved at `sv`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (sv s₀ + BitVec.ofNat 64 0) 64 = s₀.gpr .s5 ∧
  m.readW (sv s₀ + BitVec.ofNat 64 8) 64 = s₀.gpr .s6 ∧
  m.readW (sv s₀ + BitVec.ofNat 64 16) 64 = s₀.gpr .ra

/-- The callee-saved registers the block function writes (and restores). -/
def nvRegs : List Reg := [.s0, .s1, .s2, .s3, .s4]

/-- They hold our caller's values. -/
def NV (s₀ s : State) : Prop := ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r

/-- Before block `j` (the loop's invariant). -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  a1 : s.gpr .a1 = bp s₀
  s5 : s.gpr .s5 = dp s₀ + BitVec.ofNat 64 (P s₀ j)
  s6 : s.gpr .s6 = BitVec.ofNat 64 (L s₀ - P s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
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
    exact readW_writeW_out m p v (j := i) (k := 12) hi (by omega) (by omega)

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨bp s₀, 256⟩

theorem b256_sub (s₀ : State) : Region.Sub (b256 s₀) (bR s₀) := Region.sub_prefix (by omega)

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bR s₀) :=
  Offset.sub_base _ (by have := q_lt s₀; omega)

theorem savR_b256 (s₀ : State) : (savR s₀).Disjoint (b256 s₀) :=
  Offset.disjoint_base _ (by omega) (by have := q_lt s₀; omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [hf.readW (sav_contains s₀ (by omega)) hd (by decide), h1],
    by rw [hf.readW (sav_contains s₀ (by omega)) hd (by decide), h2],
    by rw [hf.readW (sav_contains s₀ (by omega)) hd (by decide), h3]⟩

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 =
      m.readW (p + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep p h (by omega) (by omega)) (by decide)

/-- Distinct bytes of the data are at distinct addresses. -/
theorem data_ne {s₀ : State} {k k' : Nat} (hk : k < L s₀) (hk' : k' < L s₀) (h : k' ≠ k) :
    dp s₀ + BitVec.ofNat 64 k' ≠ dp s₀ + BitVec.ofNat 64 k :=
  Offset.add_ofNat_ne _ (by have := L_lt s₀; omega) (by have := L_lt s₀; omega) h

/-! ## The prologue -/

theorem savePtr_ok {s : State} (n : Reg) :
    WP isa (.block (savePtr n)) s (· = s.write .t0
      (s.gpr n + BitVec.ofNat 64 256 + BitVec.ofNat 64 (pad (s.gpr n + BitVec.ofNat 64 256)))) := by
  apply WP.of_runBlock
  simp only [savePtr, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 263 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write,
    Option.some.injEq, exists_eq_left']
  rw [align_off_eq _ (off := 256) (by decide) (by decide)]

theorem prologue_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block (save ++ [mov .s5 .a1, mov .s6 .a2, mov .a1 .a3])) s₀ (OInv s₀ 0) := by
  have o : ∀ d, d + 8 ≤ 24 → InRegions s₀.wr (sv s₀ + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨bR s₀, by simp [hp.wr], sav_in s₀ hd⟩
  rw [save, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a3) fun s₁ e => ?_
  subst e
  have t₀ : (s₀.write .t0 (sv s₀)).gpr .t0 = sv s₀ := RegUpd.gpr_write_self _ _ _
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 0) (by decide) (by rw [t₀]) (sv_al _ (by decide))
    (o 0 (by omega)) fun s₂ g₂ => ?_
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 8) (by decide) (by rw [g₂.gpr, t₀])
    (sv_al _ (by decide)) (by rw [g₂.wr]; exact o 8 (by omega)) fun s₃ g₃ => ?_
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 16) (by decide) (by rw [g₃.gpr, g₂.gpr, t₀])
    (sv_al _ (by decide)) (by rw [g₃.wr, g₂.wr]; exact o 16 (by omega)) fun s₄ g₄ => ?_
  refine wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .t0 → s₄.gpr r = s₀.gpr r := fun r h => by
    rw [g₄.gpr, g₃.gpr, g₂.gpr, RegUpd.gpr_write_of_ne _ _ h]
  have hm : s₇.mem = ((s₀.mem.writeW (sv s₀ + BitVec.ofNat 64 0) (s₀.gpr .s5)).writeW
      (sv s₀ + BitVec.ofNat 64 8) (s₀.gpr .s6)).writeW (sv s₀ + BitVec.ofNat 64 16) (s₀.gpr .ra) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, g₃.gpr, g₃.mem, g₂.gpr, g₂.mem, RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide)]
    rfl
  have hf : Frame [bR s₀] s₀.mem s₇.mem := by
    rw [hm]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sav_in s₀ (by omega))).writeW
      (List.mem_singleton_self _) _ (sav_in s₀ (by omega))).writeW
      (List.mem_singleton_self _) _ (sav_in s₀ (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g _ (by decide)]; simp [P]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g _ (by decide)]; simp [P]
  · rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, g₃.rd, g₂.rd]; rfl
  · rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, g₃.wr, g₂.wr]; rfl
  · rw [stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := dR s₀) (by simpa using hp.d_b) (Nat.le_of_lt (L_lt s₀)) hk
  · rw [hm]
    refine ⟨?_, ?_, ?_⟩
    · rw [readW64_off _ _ _ (by omega) (by omega) (by omega),
        readW64_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
    · rw [readW64_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-! ## Calling the block function -/

/-- The registers the block function never writes. -/
def kept : List Reg := [.a0, .a1]

theorem block_keeps : ((instrs Impl.ChaCha20.RISCV64.block).all fun i =>
    kept.all fun r => dstOf i != some r) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem block_keeps_reg {r : Reg} (hr : r ∈ kept) :
    ∀ i ∈ instrs Impl.ChaCha20.RISCV64.block, dstOf i ≠ some r := by
  intro i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp block_keeps i hi) r hr
  simpa using this

theorem block_noFrames : Impl.ChaCha20.RISCV64.block.noFrames = true := by decide +kernel

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends OInv s₀ j s where
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

theorem call_ok {s₀ : State} (hp : XPre s₀) {j : Nat} {s : State} (h : OInv s₀ j s) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.RISCV64.block) s
      fun s' => AInv s₀ j s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s.gpr r := by
  have c0 : s.callEntry.gpr .a0 = st s₀ := (State.callEntry_gpr _ (by decide)).trans h.a0
  have c1 : s.callEntry.gpr .a1 = bp s₀ := (State.callEntry_gpr _ (by decide)).trans h.a1
  have hwr : s.wr = [stR s₀, dR s₀, bR s₀] := by rw [h.wr, hp.wr]
  have hrd : s.rd = [] := by rw [h.rd, hp.rd]
  refine WP.call (k := Proof.ChaCha20.blockRISCV64) block_verified.1
    (rd := [stR s₀]) (wr := [b256 s₀]) ?_ ?_ ?_ ?_ block_noFrames
  · simp only [Proof.ChaCha20.blockRISCV64, State.withRegions_gpr, State.withRegions_rd,
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
    simp only [Proof.ChaCha20.blockRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, h.cnt] at hpost
    refine ⟨⟨⟨by rw [hkeep .a0 (by decide) (block_keeps_reg (by simp [kept])), h.a0],
      by rw [hkeep .a1 (by decide) (block_keeps_reg (by simp [kept])), h.a1],
      by rw [hcs .s5 (by decide), h.s5],
      by rw [hcs .s6 (by decide), h.s6],
      by rw [hrd₂, h.rd], by rw [hwr₂, h.wr], by rw [hst, h.cnt], fun k hk => ?_,
      h.saved.frame hf (by simpa using savR_b256 s₀)⟩, fun t ht => ?_⟩,
      fun r hr => hcs r (by revert r; decide)⟩
    · rw [hf.bytes (R := dR s₀) (by simpa using hp.d_b.sub_right (b256_sub s₀))
        (Nat.le_of_lt (L_lt s₀)) hk]
      exact h.data k hk
    · rw [← serialize_stateAt s₂.mem (bp s₀) ht, hpost]

/-! ## The bytes of block `j` -/

/-- Before byte `i` of block `j`. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  a1 : s.gpr .a1 = bp s₀
  s5 : s.gpr .s5 = dp s₀ + BitVec.ofNat 64 (P s₀ j + i)
  t2 : s.gpr .t2 = bp s₀ + BitVec.ofNat 64 i
  a2 : s.gpr .a2 = BitVec.ofNat 64 (C s₀ j - i)
  s6 : s.gpr .s6 = BitVec.ofNat 64 (L s₀ - P s₀ j - C s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j + i then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : Saved s₀ s.mem
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

def selProg : Prog isa :=
  .seq (.block [.shift .srl .d .t1 .s6 6, mov .a2 .s6])
    (.seq (.ite (.zero .t1) (.block []) (.block [.li .a2 64]))
      (.block [.sub .s6 .s6 .a2, mov .t2 .a1]))

theorem sel_ok {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) {s : State} (h : AInv s₀ j s) :
    WP isa selProg s (IInv s₀ j 0) := by
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  refine WP.seq (wp_srl (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => WP.block_nil ?_)
  have hr9 : s₂.gpr .t1 = BitVec.ofNat 64 ((L s₀ - P s₀ j) / 64) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.s6, ofNat_shr6 (by omega)]
  have hr5 : s₂.gpr .a2 = BitVec.ofNat 64 (L s₀ - P s₀ j) := by
    rw [u₂.gpr, u₁.other _ (by decide), h.s6]
  refine WP.seq (WP.mono (Q := fun s₃ : State => s₃.gpr .a2 = BitVec.ofNat 64 (C s₀ j) ∧
      (∀ r, r ≠ .a2 → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr) ?_
    fun s₃ ⟨f₁, f₂, f₃, f₄, f₅⟩ => ?_)
  · refine WP.ite (decide ((L s₀ - P s₀ j) / 64 = 0))
      (eval_zero_ofNat _ _ (by omega) hr9)
      (fun ht => WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩)
      (fun hf => wp_li (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩)
    · simp only [decide_eq_true_eq] at ht
      rw [hr5, show C s₀ j = L s₀ - P s₀ j by omega]
    · simp only [decide_eq_false_iff_not] at hf
      rw [u₃.gpr, show C s₀ j = 64 by omega]
  · refine wp_sub fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil ?_
    have g : ∀ r, r ≠ .a2 → r ≠ .s6 → r ≠ .t2 → r ≠ .t1 → s₅.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ => by rw [u₅.other r h₃, u₄.other r h₂, f₂ r h₁, u₂.other r h₁, u₁.other r h₄]
    have gm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, f₃, u₂.mem, u₁.mem]
    refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide), h.a0],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.a1],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.s5, Nat.add_zero],
      by rw [u₅.gpr, u₄.other _ (by decide), f₂ _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.a1]; simp,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), f₁, Nat.sub_zero],
      by rw [u₅.other _ (by decide), u₄.gpr, f₂ _ (by decide), f₁, u₂.other _ (by decide),
        u₁.other _ (by decide), h.s6, sub_ofNat (by omega)],
      by rw [u₅.rd, u₄.rd, f₄, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, f₅, u₂.wr, u₁.wr, h.wr],
      by rw [gm, h.cnt], fun k hk => by rw [gm, h.data k hk, Nat.add_zero],
      by rw [gm]; exact h.saved, fun t ht => by rw [gm]; exact h.ks t ht⟩

/-! ## One byte -/

def xorBody : List Instr :=
  [.load .b .t3 .s5 0, .load .b .t4 .t2 0, .logic .xor .t3 .t3 .t4, .store .b .t3 .s5 0,
    .addi .s5 .s5 1, .addi .t2 .t2 1, .addi .a2 .a2 (-1)]

theorem xorLoop_eq : xorLoop = .loop (.block xorBody) (.nonzero .a2) := rfl

/-- `P j = 64 j` while blocks remain. -/
theorem P_eq {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ j = 64 * j := by
  simp only [P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j) :
    (KS s₀).getD (P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD i 0 := by
  have hP := P_eq hj
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  rw [KS, keystream_getD _ (by omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

theorem xor_step {s₀ : State} (hp : XPre s₀) {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j)
    {s : State} (h : IInv s₀ j i s) : WP isa (.block xorBody) s (IInv s₀ j (i + 1)) := by
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  have hk : P s₀ j + i < L s₀ := by omega
  have cd : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have cb : (bR s₀).Contains (bp s₀ + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega) (by omega)
  have i₁ : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cd⟩
  have i₂ : InRegions (s.rd ++ s.wr) (bp s₀ + BitVec.ofNat 64 i) 1 :=
    ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  have o₁ : InRegions s.wr (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dR s₀, by simp [h.wr, hp.wr], cd⟩
  unfold xorBody
  refine wp_lbu (a := dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) (by decide)
    (by rw [h.s5]; exact BitVec.add_zero _) i₁ fun s₁ u₁ => ?_
  refine wp_lbu (a := bp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), h.t2]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr]; exact i₂) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sb (a := dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.s5]
        exact BitVec.add_zero _)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o₁) fun s₄ g₄ => ?_
  refine wp_addi (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ =>
    wp_subi (imm := 1) (by decide) fun s₇ u₇ => WP.block_nil ?_
  have hv : (s₃.gpr .t3).setWidth 8 =
      D0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, xor_setWidth, h.data _ hk,
      h.ks i (by omega), ks_eq hj hi]
    simp
  have hm : s₇.mem = s.mem.writeW (dp s₀ + BitVec.ofNat 64 (P s₀ j + i))
      (D0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, hv, u₃.mem, u₂.mem, u₁.mem]
  have hfd : Frame [dR s₀] s.mem s₇.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have g : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .s5 → r ≠ .t2 → r ≠ .a2 → s₇.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by
      rw [u₇.other r h₅, u₆.other r h₄, u₅.other r h₃, g₄.gpr, u₃.other r h₁, u₂.other r h₂,
        u₁.other r h₁]
  refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a1], ?_, ?_, ?_,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.s6],
    by rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [stateAt_frame hfd (by simpa using hp.st_d), h.cnt], fun k hk' => ?_,
    h.saved.frame hfd (by simpa using (hp.d_b.sub_right (savR_sub s₀)).symm), fun t ht => ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.s5, add_ofNat, Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.t2, add_ofNat]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.a2, sub_ofNat (by omega), Nat.sub_sub]
  · rw [hm, WriteBytes.writeW8_apply]
    by_cases he : k = P s₀ j + i
    · subst he; simp
    · simp only [data_ne hk hk' he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < P s₀ j + i
      · simp [h₁, show k < P s₀ j + (i + 1) by omega]
      · simp [h₁, show ¬ k < P s₀ j + (i + 1) by omega]
  · rw [hfd.bytes (R := bR s₀) (by simpa using hp.d_b.symm) (show 320 ≤ 2 ^ 64 by omega)
      (show t < 320 by omega)]
    exact h.ks t ht

/-! ## A whole block -/

theorem xorLoop_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) : WP isa xorLoop s (IInv s₀ j (C s₀ j)) := by
  have hpos : 0 < C s₀ j := by simp only [C]; omega
  have hC : C s₀ j ≤ 64 := by simp only [C]; omega
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = C s₀ j - i ∧ i < C s₀ j ∧ IInv s₀ j i s
  have hstep : ∀ n s, Inv n s → WP isa (.block xorBody) s (fun s' =>
      (isa.eval (.nonzero .a2) s' = some false ∧ IInv s₀ j (C s₀ j) s') ∨
      (isa.eval (.nonzero .a2) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (xor_step hp hj hi hI) fun s' h' => ?_
    have hz := eval_nonzero_ofNat s' .a2 (by omega) h'.a2
    by_cases hl : i + 1 = C s₀ j
    · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
    · exact .inr ⟨by rw [hz]; simp; omega, C s₀ j - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (C s₀ j) s ⟨0, by simp, hpos, h⟩

/-! ## The end of a block -/

theorem P_succ {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ (j + 1) = P s₀ j + C s₀ j := by
  simp only [P, C] at *; omega

/-- The counter stored by `addi t1, t1, 1` and `storeLE32` after a `loadLE32 t1`. -/
theorem inc_setWidth (v : BitVec 32) :
    ((v.setWidth 64 + BitVec.ofNat 64 1).setWidth 32) = v + 1 := by
  rw [lo32_add, lo32_ext]; rfl

theorem next_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j (C s₀ j) s) : WP isa (.block next) s (OInv s₀ (j + 1)) := by
  have hP := P_succ hj
  have c₁ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 48) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  unfold next
  rw [List.append_assoc, List.singleton_append, WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega)
    (by rw [h.a0]; exact ⟨stR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩)) fun s₁ e₁ => ?_
  have g₁ : ∀ r, r ≠ .t1 → r ≠ .t3 → s₁.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [e₁, RegUpd.gpr_write_of_ne _ _ h₁, RegUpd.gpr_write_of_ne _ _ h₂]
  have hv : s.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) j)[12] := by
    rw [← h.cnt]; simp [stateAt]
  have t₁ : s₁.gpr .t1 = (s.mem.readW (st s₀ + BitVec.ofNat 64 48) 32).setWidth 64 := by
    rw [e₁, RegUpd.gpr_write_self, h.a0]
  have m₁ : s₁.mem = s.mem := by rw [e₁]; rfl
  have rd₁ : s₁.rd = s.rd := by rw [e₁]; rfl
  have wr₁ : s₁.wr = s.wr := by rw [e₁]; rfl
  refine wp_addi (by decide) fun s₂ u₂ => ?_
  have a0₂ : s₂.gpr .a0 = st s₀ := by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h.a0]
  refine WP.mono (storeLE32_ok (by decide) (by decide) (by omega)
    (by rw [a0₂, u₂.wr, wr₁]; exact ⟨stR s₀, by simp [h.wr, hp.wr], c₁⟩)) fun s₃ e₃ => ?_
  have hm : s₃.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 48) ((ctr (S0 s₀) j)[12] + 1) := by
    rw [e₃]; simp only [RegUpd.mem_write, a0₂, u₂.gpr, t₁, inc_setWidth, hv, u₂.mem, m₁]
  have g : ∀ r, r ≠ .t1 → r ≠ .t3 → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [e₃, RegUpd.gpr_write_of_ne _ _ h₂]; exact (u₂.other r h₁).trans (g₁ r h₁ h₂)
  have rd₃ : s₃.rd = s.rd := by rw [e₃, RegUpd.rd_write]; exact u₂.rd.trans rd₁
  have wr₃ : s₃.wr = s.wr := by rw [e₃, RegUpd.wr_write]; exact u₂.wr.trans wr₁
  have hfs : Frame [stR s₀] s.mem s₃.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  refine ⟨by rw [g _ (by decide) (by decide), h.a0], by rw [g _ (by decide) (by decide), h.a1],
    by rw [g _ (by decide) (by decide), h.s5, hP],
    by rw [g _ (by decide) (by decide), h.s6, hP, Nat.sub_sub],
    by rw [rd₃, h.rd], by rw [wr₃, h.wr],
    by rw [hm, stateAt_writeW_counter, h.cnt, ctr_succ], fun k hk => ?_,
    h.saved.frame hfs (by simpa using (hp.st_b.sub_right (savR_sub s₀)).symm)⟩
  rw [hfs.bytes (R := dR s₀) (by simpa using hp.st_d.symm) (Nat.le_of_lt (L_lt s₀)) hk, h.data k hk, hP]

/-- The body after the call. -/
def rest : Prog isa :=
  .seq (.block [.shift .srl .d .t1 .s6 6, mov .a2 .s6])
  (.seq (.ite (.zero .t1) (.block []) (.block [.li .a2 64]))
  (.seq (.block [.sub .s6 .s6 .a2, mov .t2 .a1])
  (.seq xorLoop (.block next))))

theorem body_eq : body = .seq (.call "vg_chacha20_block" Impl.ChaCha20.RISCV64.block) rest := rfl

theorem rest_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : AInv s₀ j s) : WP isa rest s (OInv s₀ (j + 1)) := by
  have hs := sel_ok hj h
  unfold selProg at hs
  rw [WP.seq_iff] at hs
  rw [rest, WP.seq_iff]
  refine WP.mono hs fun s₂ h₂ => ?_
  rw [WP.seq_iff] at h₂
  rw [WP.seq_iff]
  refine WP.mono h₂ fun s₃ h₃ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₃ fun s₄ h₄ => ?_
  exact WP.seq (WP.mono (xorLoop_ok hp hj h₄) fun s₅ h₅ => next_ok hp hj h₅)

/-- Registers that code never writes keep their values. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

theorem body_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : OInv s₀ j s) (hnv : NV s₀ s) : WP isa body s fun s' => OInv s₀ (j + 1) s' ∧ NV s₀ s' := by
  rw [body_eq]
  refine WP.seq (WP.mono (call_ok hp h) fun s₁ ⟨h₁, nv₁⟩ => ?_)
  exact WP.mono (WP.gprs (rs := nvRegs) (rest_ok hp hj h₁) (by decide)) fun s₂ ⟨h₂, nv₂⟩ =>
    ⟨h₂, fun r hr => (nv₂ r hr).trans ((nv₁ r hr).trans (hnv r hr))⟩

/-! ## The epilogue -/

/-- What the code guarantees on return, beyond the registers it never writes. -/
def Post (s₀ s' : State) : Prop :=
  s'.gpr .s5 = s₀.gpr .s5 ∧ s'.gpr .s6 = s₀.gpr .s6 ∧ s'.gpr .ra = s₀.gpr .ra ∧
    Proof.ChaCha20.xorRISCV64.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j = L s₀) {s : State}
    (h : OInv s₀ j s) : WP isa (.block restore) s (Post s₀) := by
  have i : ∀ d, d + 8 ≤ 24 → InRegions (s.rd ++ s.wr) (sv s₀ + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], sav_in s₀ hd⟩
  obtain ⟨sv1, sv2, sv3⟩ := h.saved
  rw [restore, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a1) fun s₁ e => ?_
  subst e
  have t₀ : (s.write .t0 (s.gpr .a1 + BitVec.ofNat 64 256 +
      BitVec.ofNat 64 (pad (s.gpr .a1 + BitVec.ofNat 64 256)))).gpr .t0 = sv s₀ := by
    rw [RegUpd.gpr_write_self, h.a1]
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 16) (by decide) (by rw [t₀]) (sv_al _ (by decide))
    (i 16 (by omega)) fun s₂ u₂ => ?_
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 0) (by decide) (by rw [u₂.other _ (by decide), t₀])
    (sv_al _ (by decide)) (by rw [u₂.rd, u₂.wr]; exact i 0 (by omega)) fun s₃ u₃ => ?_
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 8) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), t₀])
    (sv_al _ (by decide)) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact i 8 (by omega)) fun s₄ u₄ =>
    WP.block_nil ?_
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem]; rfl
  refine ⟨by rw [u₄.other _ (by decide), u₃.gpr, u₂.mem]; exact sv1,
    by rw [u₄.gpr, u₃.mem, u₂.mem]; exact sv2,
    by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; exact sv3, ?_⟩
  refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
  have hk' : k < L s₀ := hk
  rw [hm, h.data k hk']
  simp only [show k < P s₀ j by omega, ite_true]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.RISCV64.Xor.xor =
    .seq (.block (save ++ [mov .s5 .a1, mov .s6 .a2, mov .a1 .a3]))
    (.seq (.ite (.zero .s6) (.block []) (.loop body (.nonzero .s6))) (.block restore)) := rfl

theorem main_ok {s₀ : State} (hp : XPre s₀) :
    WP isa Impl.ChaCha20.RISCV64.Xor.xor s₀ fun s' => Post s₀ s' ∧ NV s₀ s' := by
  have hL := L_lt s₀
  rw [xor_eq]
  refine WP.seq (WP.mono (WP.gprs (rs := nvRegs) (prologue_ok hp) (by decide)) fun s₁ ⟨h₁, nv₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s ∧ NV s₀ s) ?_
    fun s₂ ⟨j, hj, h₂, nv₂⟩ => WP.mono (WP.gprs (rs := nvRegs) (epilogue_ok hp hj h₂) (by decide))
      fun s₃ ⟨h₃, nv₃⟩ => ⟨h₃, fun r hr => (nv₃ r hr).trans (nv₂ r hr)⟩)
  have hz : isa.eval (.zero .s6) s₁ = some (decide (L s₀ = 0)) := by
    rw [eval_zero_ofNat _ _ (by omega) h₁.s6]
    simp [P]
  refine WP.ite (decide (L s₀ = 0)) hz (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil ⟨0, by simp [P, h], h₁, nv₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s =>
      ∃ j, n = L s₀ - P s₀ j ∧ P s₀ j < L s₀ ∧ OInv s₀ j s ∧ NV s₀ s
    have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
        (isa.eval (.nonzero .s6) s' = some false ∧ ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s' ∧ NV s₀ s') ∨
        (isa.eval (.nonzero .s6) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, hI, hnv⟩
      refine WP.mono (body_ok hp hj hI hnv) fun s' ⟨h', nv'⟩ => ?_
      have hz' := eval_nonzero_ofNat s' .s6 (by omega) h'.s6
      have hP := P_succ hj
      have hC : 0 < C s₀ j := by simp only [C]; omega
      have hle : P s₀ (j + 1) ≤ L s₀ := by simp only [P]; omega
      by_cases hl : L s₀ - P s₀ (j + 1) = 0
      · exact .inl ⟨by rw [hz']; simp [hl], j + 1, by omega, h', nv'⟩
      · exact .inr ⟨by rw [hz']; simp [hl], L s₀ - P s₀ (j + 1), by omega, j + 1, rfl, by omega,
          h', nv'⟩
    exact WP.loop (M := isa) Inv hstep (L s₀ - P s₀ 0) s₁ ⟨0, rfl, by simp [P]; omega, h₁, nv₁⟩

/-- The callee-saved registers that no instruction writes, including those of
the block function. -/
def untouched : List Reg := [.s7, .s8, .s9, .s10, .s11]

theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs Impl.ChaCha20.RISCV64.Xor.xor,
    dstOf i ≠ some r := by
  have : ((instrs Impl.ChaCha20.RISCV64.Xor.xor).all fun i =>
      untouched.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

theorem correct {s₀ : State} (hp : XPre s₀) :
    ∃ t s', Exec isa Impl.ChaCha20.RISCV64.Xor.xor s₀ t s' ∧ abiPreserved s₀ s' ∧
      Proof.ChaCha20.xorRISCV64.post s₀ s' := by
  obtain ⟨t, s', he, ⟨h5, h6, hra, hpost⟩, hnv⟩ := main_ok hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hra⟩, hpost⟩
  have hl : ∀ r ∈ untouched, r ∉ linkRegs := by decide
  have key : ∀ r ∈ preserved, r = .s5 ∨ r = .s6 ∨ r ∈ nvRegs ∨ r ∈ untouched := by decide
  rcases key r hr with rfl | rfl | h | h
  · exact h5
  · exact h6
  · exact hnv r h
  · exact Exec.gpr (untouched_ok r h) he (.inr (hl r h))

/-! ## Constant time -/

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.ChaCha20.xorRISCV64.pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4]

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩]

theorem xor_correct (s : State) (hs : Proof.ChaCha20.xorRISCV64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.RISCV64.Xor.xor s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorRISCV64.post s s' :=
  correct (XPre.of s hs)

theorem xor_ct : ConstantTime isa Proof.ChaCha20.xorRISCV64.pre Proof.ChaCha20.xorRISCV64.pub
    Impl.ChaCha20.RISCV64.Xor.xor :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

theorem xor_verified :
    Verified RISCV64.target Impl.ChaCha20.RISCV64.Xor.xor (Proof.ChaCha20.xorContract RISCV64.abi) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Proof.ChaCha20.xorContract, Proof.ChaCha20.xorSig, RISCV64.abi, RISCV64.argRegs,
      Proof.ChaCha20.xorRISCV64]
      [sat] using sat)

end VG.Proof.ChaCha20.RISCV64.Xor
