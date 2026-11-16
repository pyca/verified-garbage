module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Save
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Common
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream

/-! ### `Hmac.Stream.PPC64LE.PadKey`, which only this module used -/

section

/-!
# HMAC over any streaming hash function on PPC64LE: the padded key

`padKey dst c` writes `K₀ ⊕ c`, the key's `kl` bytes (at `r23`, `r24` of
them) XORed with the byte `c` and then `c` up to a block, at `N(dst)`
(`padKey_ok`): two loops of byte stores, which write only that block.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.PadKey

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.MdStream.PPC64LE (mov)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_li wp_mov wp_add wp_sub wp_addi wp_subi wp_lbz wp_stb
  eval_zero eval_nonzero ofNat_beq_zero sub_ofNat contains_offset)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open Spec.Sha256 (bytesAt)

/-- The key `K` padded with zeros to `B` bytes. -/
def K0 (K : List Byte) (B : Nat) : List Byte := K ++ List.replicate (B - K.length) 0

theorem K0_length {K : List Byte} {B : Nat} (h : K.length ≤ B) : (K0 K B).length = B := by
  simp [K0]; omega_arith

theorem wp_xor {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  VG.Proof.MdStream.PPC64LE.WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem xor_byte (b : Byte) (v : Nat) :
    ((b.setWidth 64 ^^^ BitVec.ofNat 64 v).setWidth 8 : Byte) = b ^^^ BitVec.ofNat 8 v := by
  ext i hi
  simp

theorem byte_ofNat (v : Nat) : ((BitVec.ofNat 64 v).setWidth 8 : Byte) = (0 : Byte) ^^^ BitVec.ofNat 8 v := by
  ext i hi
  simp

/-- The bytes `j` of the block written so far. -/
abbrev blk (K : List Byte) (B c j : Nat) : List Byte :=
  ((K0 K B).take j).map (· ^^^ BitVec.ofNat 8 c)

section
variable {H : Hash} (s₀ : State) (dst : Reg) (c kl : Nat) (K : List Byte)

/-- The base of the block. -/
abbrev bp : Addr := s₀.gpr dst + BitVec.ofNat 64 H.N

/-- `j` bytes of the block are written. -/
structure Inv (j : Nat) (s : State) : Prop where
  keep : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ .r25 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r12 : s.gpr .r12 = BitVec.ofNat 64 c
  r25 : s.gpr .r25 = BitVec.ofNat 64 j
  mem : s.mem = writeBytes s₀.mem (bp (H := H) s₀ dst) (blk K H.B c j)

/-- In the key loop: `r9` points at key byte `j`, and `r10` counts those left. -/
structure KInv (j : Nat) (s : State) : Prop extends Inv (H := H) s₀ dst c K j s where
  r9 : s.gpr .r9 = s₀.gpr .r23 + BitVec.ofNat 64 j
  r10 : s.gpr .r10 = BitVec.ofNat 64 (kl - j)

/-- In the pad loop: `r10` counts the bytes left. -/
structure PInv (j : Nat) (s : State) : Prop extends Inv (H := H) s₀ dst c K j s where
  r10 : s.gpr .r10 = BitVec.ofNat 64 (H.B - j)

end

/-- The hypotheses of `padKey`: the key (`kl` bytes `K` at `r23`, `r24` =
`kl`), at most a block, readable and disjoint from the block at `N(dst)`,
which is writable. -/
structure Hyp (H : Hash) (s₀ : State) (dst : Reg) (kl : Nat) (K : List Byte) : Prop where
  B : H.B < 2 ^ 15
  N : H.N < 2 ^ 15
  kl_le : kl ≤ H.B
  r24 : s₀.gpr .r24 = BitVec.ofNat 64 kl
  key : bytesAt s₀.mem (s₀.gpr .r23) kl = K
  kin : ∀ j < kl, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r23 + BitVec.ofNat 64 j) 1
  out : ∀ j < H.B, InRegions s₀.wr (bp (H := H) s₀ dst + BitVec.ofNat 64 j) 1
  disj : Region.Disjoint ⟨s₀.gpr .r23, kl⟩ ⟨bp (H := H) s₀ dst, H.B⟩
  dst : dst ≠ .r0 ∧ dst ≠ .r8 ∧ dst ≠ .r9 ∧ dst ≠ .r10 ∧ dst ≠ .r11 ∧ dst ≠ .r12 ∧ dst ≠ .r25

variable {H : Hash} {s₀ : State} {dst : Reg} {c kl : Nat} {K : List Byte}

theorem Hyp.K_length (hy : Hyp H s₀ dst kl K) : K.length = kl := by
  rw [← hy.key]; simp [bytesAt]

theorem blk_succ (c : Nat) {j : Nat} (hj : j < (K0 K H.B).length) :
    blk K H.B c (j + 1) = blk K H.B c j ++ [(K0 K H.B).getD j 0 ^^^ BitVec.ofNat 8 c] := by
  simp only [blk]
  rw [List.take_add_one, List.map_append, List.getElem?_eq_getElem hj]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem blk_length (hy : Hyp H s₀ dst kl K) {j : Nat} (hj : j ≤ H.B) : (blk K H.B c j).length = j := by
  rw [List.length_map, List.length_take, K0_length (by rw [hy.K_length]; exact hy.kl_le)]
  omega_arith

theorem K0_getD_lt {j : Nat} (hj : j < K.length) : (K0 K H.B).getD j 0 = K.getD j 0 := by
  simp [K0, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem K0_getD_ge {j : Nat} (hj : K.length ≤ j) : (K0 K H.B).getD j 0 = 0 := by
  simp only [K0, List.getD_eq_getElem?_getD, List.getElem?_append_right hj, List.getElem?_replicate]
  split <;> rfl

/-- A byte written after the `j` written so far. -/
theorem Inv.write (hy : Hyp H s₀ dst kl K) {j : Nat} (hj : j < H.B) {m : Mem}
    (hm : m = writeBytes s₀.mem (bp (H := H) s₀ dst) (blk K H.B c j)) :
    m.writeW (bp (H := H) s₀ dst + BitVec.ofNat 64 j) ((K0 K H.B).getD j 0 ^^^ BitVec.ofNat 8 c) =
      writeBytes s₀.mem (bp (H := H) s₀ dst) (blk K H.B c (j + 1)) := by
  obtain e := writeBytes_snoc s₀.mem (bp (H := H) s₀ dst) (blk K H.B c j)
    ((K0 K H.B).getD j 0 ^^^ BitVec.ofNat 8 c) (by rw [blk_length hy (Nat.le_of_lt hj)]; have := hy.B; omega_arith)
  rw [blk_length hy (Nat.le_of_lt hj)] at e
  rw [hm, blk_succ c (by rw [K0_length (by rw [hy.K_length]; exact hy.kl_le)]; exact hj), e]

theorem writeBytes_out {m : Mem} {q a : Addr} {xs : List Byte} {n : Nat}
    (h : ¬ (⟨q, n⟩ : Region).Contains a 1) (hl : xs.length ≤ n) : writeBytes m q xs a = m a := by
  simp only [writeBytes, Region.Contains] at h ⊢
  split
  · omega_arith
  · rfl

/-- Key byte `j`, while the block is written. -/
theorem key_byte (hy : Hyp H s₀ dst kl K) {j j' : Nat} (hj : j < kl) (hj' : j' ≤ H.B) {m : Mem}
    (hm : m = writeBytes s₀.mem (bp (H := H) s₀ dst) (blk K H.B c j')) :
    m (s₀.gpr .r23 + BitVec.ofNat 64 j) = (K0 K H.B).getD j 0 := by
  have hl := hy.K_length
  have := hy.B
  have := hy.kl_le
  rw [hm, writeBytes_out (n := H.B) (hy.disj _ (contains_offset (by omega_arith) (by omega_arith)))
      (by rw [blk_length hy hj']; exact hj'), K0_getD_lt (by omega_arith), ← hy.key]
  simp [bytesAt, List.getD_eq_getElem?_getD, hj]

/-! ## The loops -/

/-- The key loop's body. -/
def keyBody (H : Hash) (dst : Reg) : List Instr :=
  [.lbz .r8 .r9 0, .logic .xor .r8 .r8 .r12, .add .r11 dst .r25, .stb .r8 .r11 H.N,
    .addi .r9 .r9 1, .addi .r25 .r25 1, .subi .r10 .r10 1]

theorem keyLoop_eq (H : Hash) (dst : Reg) : H.keyLoop dst = .loop (.block (keyBody H dst)) (.nonzero .d .r10) := rfl

/-- The pad loop's body. -/
def padBody (H : Hash) (dst : Reg) : List Instr :=
  [.add .r11 dst .r25, .stb .r12 .r11 H.N, .addi .r25 .r25 1, .subi .r10 .r10 1]

theorem padLoop_eq (H : Hash) (dst : Reg) : H.padLoop dst = .loop (.block (padBody H dst)) (.nonzero .d .r10) := rfl

theorem stb_addr (d : Addr) (n j : Nat) :
    d + BitVec.ofNat 64 j + BitVec.ofNat 64 n = d + BitVec.ofNat 64 n + BitVec.ofNat 64 j := by
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j), ← BitVec.add_assoc]

theorem key_step (hy : Hyp H s₀ dst kl K) {j : Nat} (hj : j < kl) {s : State}
    (h : KInv (H := H) s₀ dst c kl K j s) : WP isa (.block (keyBody H dst)) s (KInv (H := H) s₀ dst c kl K (j + 1)) := by
  obtain hjB : j < H.B := Nat.lt_of_lt_of_le hj hy.kl_le
  obtain ⟨d0, d8, d9, d10, d11, d12, d31⟩ := hy.dst
  obtain hd : s.gpr dst = s₀.gpr dst := h.keep dst d8 d9 d10 d11 d12 d31
  unfold keyBody
  refine wp_lbz (a := s₀.gpr .r23 + BitVec.ofNat 64 j) (by decide) (by rw [h.r9, BitVec.add_zero])
    (by rw [h.rd, h.wr]; exact hy.kin j hj) fun s₁ u₁ => ?_
  refine wp_xor fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  refine wp_stb (a := bp (H := H) s₀ dst + BitVec.ofNat 64 j) hy.N ?_
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hy.out j hjB) fun s₄ u₄ => ?_
  · rw [u₃.gpr, u₂.other _ d8, u₁.other _ d8, hd, u₂.other _ (by decide), u₁.other _ (by decide), h.r25,
      stb_addr]
  refine wp_addi (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ =>
    wp_subi (by decide) fun s₇ u₇ => WP.block_nil ?_
  obtain k : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r25 → s₇.gpr r = s.gpr r :=
    fun r a b c d e => by
      rw [u₇.other r c, u₆.other r e, u₅.other r b, u₄.gpr, u₃.other r d, u₂.other r a, u₁.other r a]
  obtain v : (s₃.gpr .r8).setWidth 8 = (K0 K H.B).getD j 0 ^^^ BitVec.ofNat 8 c := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.r12, xor_byte,
      key_byte hy hj (by omega_arith) h.mem]
  refine ⟨⟨fun r a b c d e f => (k r a b c d f).trans (h.keep r a b c d e f),
    by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r12], ?_, ?_⟩, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r25, BitVec.ofNat_add]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, v, u₃.mem, u₂.mem, u₁.mem]
    exact Inv.write hy hjB h.mem
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r9, BitVec.ofNat_add, BitVec.add_assoc]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r10, show kl - (j + 1) = kl - j - 1 by omega_arith,
      ← sub_ofNat (a := kl - j) (b := 1) (by omega_arith)]

theorem pad_step (hy : Hyp H s₀ dst kl K) {j : Nat} (hj : kl ≤ j) (hj' : j < H.B) {s : State}
    (h : PInv (H := H) s₀ dst c K j s) :
    WP isa (.block (padBody H dst)) s (PInv (H := H) s₀ dst c K (j + 1)) := by
  obtain ⟨d0, d8, d9, d10, d11, d12, d31⟩ := hy.dst
  obtain hd : s.gpr dst = s₀.gpr dst := h.keep dst d8 d9 d10 d11 d12 d31
  unfold padBody
  refine wp_add fun s₁ u₁ => ?_
  refine wp_stb (a := bp (H := H) s₀ dst + BitVec.ofNat 64 j) hy.N ?_
    (by rw [u₁.wr, h.wr]; exact hy.out j hj') fun s₂ u₂ => ?_
  · rw [u₁.gpr, hd, h.r25, stb_addr]
  refine wp_addi (by decide) fun s₃ u₃ => wp_subi (by decide) fun s₄ u₄ => WP.block_nil ?_
  obtain k : ∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r25 → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [u₄.other r a, u₃.other r c, u₂.gpr, u₁.other r b]
  obtain v : (s₁.gpr .r12).setWidth 8 = (K0 K H.B).getD j 0 ^^^ BitVec.ofNat 8 c := by
    rw [u₁.other _ (by decide), h.r12, K0_getD_ge (by rw [hy.K_length]; exact hj), byte_ofNat]
  refine ⟨⟨fun r a b c d e f => (k r c d f).trans (h.keep r a b c d e f),
    by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [k _ (by decide) (by decide) (by decide), h.r12], ?_, ?_⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r25, BitVec.ofNat_add]
  · rw [u₄.mem, u₃.mem, u₂.mem, v, u₁.mem]
    exact Inv.write hy hj' h.mem
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r10,
      show H.B - (j + 1) = H.B - j - 1 by omega_arith, ← sub_ofNat (a := H.B - j) (b := 1) (by omega_arith)]

theorem key_loop_ok (hy : Hyp H s₀ dst kl K) {s : State} (h : KInv (H := H) s₀ dst c kl K 0 s)
    (hk : 0 < kl) : WP isa (H.keyLoop dst) s (Inv (H := H) s₀ dst c K kl) := by
  have := hy.kl_le
  have := hy.B
  rw [keyLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = kl - j ∧ j < kl ∧ KInv (H := H) s₀ dst c kl K j s) ?_ kl s
    ⟨0, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hb⟩
  refine WP.mono (key_step hy hj hb) fun s' hb' => ?_
  obtain hz : isa.eval (.nonzero .d .r10) s' = some (decide (kl - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r10) s' = _
    rw [eval_nonzero, hb'.r10, bne, ofNat_beq_zero (by omega_arith)]
    simp
  by_cases hl : kl - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rw [show kl = j + 1 by omega_arith]; exact hb'.toInv
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega_arith, j + 1, rfl, by omega_arith, hb'⟩

theorem pad_loop_ok (hy : Hyp H s₀ dst kl K) {s : State} (h : PInv (H := H) s₀ dst c K kl s)
    (hk : kl < H.B) : WP isa (H.padLoop dst) s (Inv (H := H) s₀ dst c K H.B) := by
  have := hy.B
  rw [padLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = H.B - j ∧ kl ≤ j ∧ j < H.B ∧ PInv (H := H) s₀ dst c K j s) ?_
    (H.B - kl) s ⟨kl, rfl, Nat.le_refl _, hk, h⟩
  rintro n s ⟨j, rfl, hj, hj', hb⟩
  refine WP.mono (pad_step hy hj hj' hb) fun s' hb' => ?_
  obtain hz : isa.eval (.nonzero .d .r10) s' = some (decide (H.B - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r10) s' = _
    rw [eval_nonzero, hb'.r10, bne, ofNat_beq_zero (by omega_arith)]
    simp
  by_cases hl : H.B - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rw [show H.B = j + 1 by omega_arith]; exact hb'.toInv
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega_arith, j + 1, rfl, by omega_arith, by omega_arith, hb'⟩

/-- The whole block is `K₀ ⊕ c`. -/
theorem blk_full (hy : Hyp H s₀ dst kl K) :
    blk K H.B c H.B = Spec.Hmac.xorPad (K0 K H.B) (BitVec.ofNat 8 c) := by
  rw [blk, List.take_of_length_le (by rw [K0_length (by rw [hy.K_length]; exact hy.kl_le)])]
  rfl

/-- `padKey dst c`: `K₀ ⊕ c` at `N(dst)`, writing only `r8`–`r12` and `r25`. -/
theorem padKey_ok (hy : Hyp H s₀ dst kl K) (hc : c < 2 ^ 15) {Q : State → Prop}
    (hQ : ∀ s', Inv (H := H) s₀ dst c K H.B s' → Q s') : WP isa (H.padKey dst c) s₀ Q := by
  have := hy.B
  have := hy.kl_le
  obtain ⟨d0, d8, d9, d10, d11, d12, d31⟩ := hy.dst
  unfold Hash.padKey
  refine WP.seq (wp_li hc fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => wp_mov fun s₃ u₃ =>
    wp_mov fun s₄ u₄ => WP.block_nil ?_)
  obtain hI : Inv (H := H) s₀ dst c K 0 s₄ :=
    ⟨fun r a b c d e f => by rw [u₄.other r c, u₃.other r b, u₂.other r f, u₁.other r e],
      by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr],
      by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr],
      by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; simp [blk, writeBytes_nil]⟩
  obtain h10 : s₄.gpr .r10 = BitVec.ofNat 64 kl := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hy.r24]
  obtain h9 : s₄.gpr .r9 = s₀.gpr .r23 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  -- The key loop.
  refine WP.seq (WP.mono (Q := Inv (H := H) s₀ dst c K kl) ?_ fun s₅ h₅ => ?_)
  · have hz : eval (.zero .d .r10) s₄ = some (decide (kl = 0)) := by
      rw [eval_zero, h10, ofNat_beq_zero (by omega_arith)]
    refine WP.ite (decide (kl = 0)) hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      exact WP.block_nil hI
    · simp only [decide_eq_false_iff_not] at hb
      exact key_loop_ok hy ⟨hI, by rw [h9, BitVec.add_zero], by rw [h10, Nat.sub_zero]⟩ (by omega_arith)
  -- The pad loop.
  refine WP.seq (wp_li hy.B fun s₆ u₆ => wp_sub fun s₇ u₇ => WP.block_nil ?_)
  obtain hI₇ : Inv (H := H) s₀ dst c K kl s₇ :=
    ⟨fun r a b c d e f => by rw [u₇.other r c, u₆.other r c]; exact h₅.keep r a b c d e f,
      by rw [u₇.rd, u₆.rd, h₅.rd], by rw [u₇.wr, u₆.wr, h₅.wr], by rw [u₇.sp, u₆.sp, h₅.sp],
      by rw [u₇.other _ (by decide), u₆.other _ (by decide), h₅.r12],
      by rw [u₇.other _ (by decide), u₆.other _ (by decide), h₅.r25],
      by rw [u₇.mem, u₆.mem, h₅.mem]⟩
  obtain h10' : s₇.gpr .r10 = BitVec.ofNat 64 (H.B - kl) := by
    rw [u₇.gpr, u₆.gpr, u₆.other _ (by decide), h₅.r25, sub_ofNat (by omega_arith)]
  obtain hz : eval (.zero .d .r10) s₇ = some (decide (H.B - kl = 0)) := by
    rw [eval_zero, h10', ofNat_beq_zero (by omega_arith)]
  refine WP.ite (decide (H.B - kl = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hQ _ (by rw [show H.B = kl by omega_arith]; exact hI₇))
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.mono (pad_loop_ok hy ⟨hI₇, h10'⟩ (by omega_arith)) hQ

end VG.Proof.Hmac.Stream.PPC64LE.PadKey

end

end


/-!
# HMAC over any streaming hash function on PPC64LE: `init`

`initMain` saves our caller's `r20`–`r25`, sets both states' hash values
with the streaming `init`, writes `K₀ ⊕ ipad` into the outer state's buffer
(`padKey`) and absorbs it into the inner state with `update`, then writes
`K₀ ⊕ opad` into the inner state's buffer and absorbs it into the outer
state, and restores the registers (`correctMain`). A state representing the
empty message or a whole block does not use its buffer
(`HashOK.repr_keep`). Every write is in the two states, the scratch space
or the 48 bytes below the stack pointer, where the callees' frames go.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Init

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.MdStream.PPC64LE (mov)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_li wp_mov wp_addi contains_offset)
open VG.WriteBytes (writeBytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev inn : Addr := s₀.gpr .r3
abbrev out : Addr := s₀.gpr .r4
abbrev kp : Addr := s₀.gpr .r5
abbrev kl : Nat := (s₀.gpr .r6).toNat
abbrev scr : Addr := s₀.gpr .r7
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev kR : Region := ⟨kp s₀, kl s₀⟩
abbrev scR : Region := ⟨scr s₀, H.W + 48⟩
/-- The key. -/
abbrev K : List Byte := bytesAt s₀.mem (kp s₀) (kl s₀)
/-- Everything the code writes. -/
abbrev all : List Region := [inR H s₀, outR H s₀, scR H s₀, below s₀.sp 48]

end

/-- `init`'s precondition, with the stack pointer below its frame: its
callees' frames are in the 48 bytes below it. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [kR s₀]
  wr : s₀.wr = [inR H s₀, outR H s₀, scR H s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  i_s : (inR H s₀).Disjoint (scR H s₀)
  o_s : (outR H s₀).Disjoint (scR H s₀)
  k_i : (kR s₀).Disjoint (inR H s₀)
  k_o : (kR s₀).Disjoint (outR H s₀)
  k_s : (kR s₀).Disjoint (scR H s₀)
  sp48 : 48 ≤ s₀.sp.toNat
  si : (below s₀.sp 48).Disjoint (inR H s₀)
  so : (below s₀.sp 48).Disjoint (outR H s₀)
  sk : (below s₀.sp 48).Disjoint (kR s₀)
  ss : (below s₀.sp 48).Disjoint (scR H s₀)

variable {H : Hash} (hH : HashOK H) {s₀ : State}

theorem cover_self {rs : List Region} {R : Region} (h : R ∈ rs) :
    ∃ r' ∈ rs, ∃ off, R.base = r'.base + BitVec.ofNat 64 off ∧ off + R.len ≤ r'.len :=
  ⟨R, h, 0, by simp, by simp⟩

theorem cover_pre {rs : List Region} {R : Region} (h : R ∈ rs) {n : Nat} (hn : n ≤ R.len) :
    ∃ r' ∈ rs, ∃ off, (⟨R.base, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨R, h, 0, by simp, by simp; exact hn⟩

theorem cover_off {rs : List Region} {R : Region} (h : R ∈ rs) {o n : Nat} (hn : o + n ≤ R.len) :
    ∃ r' ∈ rs, ∃ off, (⟨R.base + BitVec.ofNat 64 o, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + n ≤ r'.len :=
  ⟨R, h, o, rfl, hn⟩

theorem covers_one {rs : List Region} {R : Region} (h : R ∈ rs) : Covers [R] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact cover_self h

/-- The hash value at the start of a state. -/
theorem hv_sub (p : Addr) : Region.Sub ⟨p, H.N⟩ ⟨p, H.S⟩ := Region.sub_prefix (by simp)

/-- The buffer of a state. -/
theorem buf_sub (p : Addr) : Region.Sub ⟨p + BitVec.ofNat 64 H.N, H.B⟩ ⟨p, H.S⟩ :=
  Offset.sub_base p (by simp)

/-- A state's hash value and its buffer are disjoint. -/
theorem hv_buf (hN : H.N ≤ 64) (hB : H.B ≤ 128) (p : Addr) :
    Region.Disjoint ⟨p, H.N⟩ ⟨p + BitVec.ofNat 64 H.N, H.B⟩ :=
  Offset.base_disjoint p (Nat.le_refl _) (by omega_arith)

/-- The working space of the functions we call. -/
theorem w_sub (p : Addr) : Region.Sub ⟨p, H.W⟩ ⟨p, H.W + 48⟩ := Region.sub_prefix (by omega_arith)

/-- The save area. -/
theorem sv_sub (p : Addr) : Region.Sub ⟨p + BitVec.ofNat 64 H.W, 48⟩ ⟨p, H.W + 48⟩ :=
  Offset.sub_base p (by omega_arith)

theorem w_sv (hW : H.W ≤ 1024) (p : Addr) : Region.Disjoint ⟨p, H.W⟩ ⟨p + BitVec.ofNat 64 H.W, 48⟩ :=
  Offset.base_disjoint p (Nat.le_refl _) (by omega_arith)

/-- `k0` is the key padded with zeros, for a key of at most a block. -/
theorem blockKey_eq (hp : Pre H s₀) :
    blockKey hH.SH.H (K s₀) = PadKey.K0 (K s₀) H.B := by
  obtain hl : (K s₀).length = kl s₀ := by simp [bytesAt]
  simp only [blockKey, PadKey.K0, hH.hB, hl, show ¬ (H.B < kl s₀) by have := hp.kl_le; omega_arith, ite_false]

/-! ## Correctness -/

/-- What we know of a state of `initMain` about the regions: those of `s₀`. -/
structure Regs (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- A state's buffer is writable, and disjoint from the key. -/
theorem buf_out (hp : Pre H s₀) {q : Addr} (hq : q = inn s₀ ∨ q = out s₀) :
    (⟨q, H.S⟩ : Region) ∈ s₀.wr ∧ (kR s₀).Disjoint ⟨q, H.S⟩ := by
  rcases hq with rfl | rfl
  · exact ⟨by simp [hp.wr], hp.k_i⟩
  · exact ⟨by simp [hp.wr], hp.k_o⟩

include hH in
/-- `padKey dst c`: `K₀ ⊕ c` into the buffer of the state at `q`, the inner
or the outer one. -/
theorem padKey_ok (hp : Pre H s₀) {dst : Reg} (hdst : dst ≠ .r0 ∧ dst ≠ .r8 ∧ dst ≠ .r9 ∧ dst ≠ .r10 ∧
      dst ≠ .r11 ∧ dst ≠ .r12 ∧ dst ≠ .r25) {c : Nat} (hc : c < 2 ^ 15) {q : Addr}
    (hq : q = inn s₀ ∨ q = out s₀) {s : State} (hr : Regs s₀ s) (hd : s.gpr dst = q)
    (h29 : s.gpr .r23 = kp s₀) (h30 : s.gpr .r24 = s₀.gpr .r6) (hk : bytesAt s.mem (kp s₀) (kl s₀) = K s₀)
    {Q : State → Prop}
    (hQ : ∀ s', Regs s₀ s' → (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ .r25 →
        s'.gpr r = s.gpr r) →
      s'.mem = writeBytes s.mem (q + BitVec.ofNat 64 H.N)
        (xorPad (PadKey.K0 (K s₀) H.B) (BitVec.ofNat 8 c)) → Q s') :
    WP isa (H.padKey dst c) s Q := by
  have hN : 0 < H.N ∧ H.N ≤ 64 := hH.dims.N
  have hB : H.B = 64 ∨ H.B = 128 := hH.dims.B
  have hS : H.S = H.N + H.B := rfl
  have hkl := hp.kl_le
  obtain ⟨hw, hdk⟩ := buf_out hp hq
  obtain hy : PadKey.Hyp H s dst (kl s₀) (K s₀) := ⟨by omega_arith, by omega_arith, hkl,
    by rw [h30, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [h29, hk],
    fun j hj => ⟨kR s₀, by simp [hr.rd, hr.wr, hp.rd], by rw [h29]; exact contains_offset (by omega_arith) (by omega_arith)⟩,
    fun j hj => ⟨⟨q, H.S⟩, by rw [hr.wr]; exact hw, by
      simp only [PadKey.bp]
      rw [hd, Proof.MdStream.PPC64LE.add_ofNat]; exact contains_offset (by omega_arith) (by omega_arith)⟩,
    by simp only [PadKey.bp]; rw [h29, hd]; exact hdk.sub_right (buf_sub _), hdst⟩
  refine PadKey.padKey_ok hy hc fun s' hi => ?_
  refine hQ s' ⟨hi.rd.trans hr.rd, hi.wr.trans hr.wr, hi.sp.trans hr.sp⟩ hi.keep ?_
  rw [hi.mem, PadKey.blk_full hy]
  simp only [PadKey.bp]
  rw [hd]

/-- `updBlock st src`: the block in the buffer of the state at `q` into the
state at `p`. -/
theorem updBlock_ok (hp : Pre H s₀) {st src : Reg} (hst : st ≠ .r0) (hsrc : src ≠ .r0 ∧ src ≠ .r3 ∧ src ≠ .r4)
    {p q : Addr} (hpq : (p = inn s₀ ∧ q = out s₀) ∨ (p = out s₀ ∧ q = inn s₀)) {s : State} (hr : Regs s₀ s)
    (h_st : s.gpr st = p) (h_src : s.gpr src = q) (h27 : s.gpr .r21 = scr s₀) {Q : State → Prop}
    (hQ : ∀ s', Regs s₀ s' →
      Frame ([⟨p, H.S⟩, ⟨scr s₀, H.W⟩] ++ [below s₀.sp 48]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (hH.SH.Repr s.mem p [] → hH.SH.Repr s'.mem p (bytesAt s.mem (q + BitVec.ofNat 64 H.N) H.B)) → Q s') :
    WP isa (H.updBlock st src) s Q := by
  have hN : 0 < H.N ∧ H.N ≤ 64 := hH.dims.N
  have hB : H.B = 64 ∨ H.B = 128 := hH.dims.B
  have hS : H.S = H.N + H.B := rfl
  obtain ⟨s0, s3, s4⟩ := hsrc
  obtain hp' : (⟨p, H.S⟩ : Region) ∈ s₀.wr ∧ (⟨q, H.S⟩ : Region) ∈ s₀.wr ∧
      Region.Disjoint ⟨p, H.S⟩ ⟨q, H.S⟩ ∧ Region.Disjoint ⟨p, H.S⟩ (scR H s₀) ∧
      Region.Disjoint ⟨q, H.S⟩ (scR H s₀) ∧ (below s₀.sp 48).Disjoint ⟨p, H.S⟩ ∧
      (below s₀.sp 48).Disjoint ⟨q, H.S⟩ := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simp [hp.wr], by simp [hp.wr], hp.i_o, hp.i_s, hp.o_s, hp.si, hp.so⟩
    · exact ⟨by simp [hp.wr], by simp [hp.wr], hp.i_o.symm, hp.o_s, hp.i_s, hp.so, hp.si⟩
  obtain ⟨wp, wq, dpq, dps, dqs, sp_, sq⟩ := hp'
  unfold Hash.updBlock
  refine WP.seq (wp_mov (fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => wp_addi (by omega_arith) (fun s₃ u₃ =>
    wp_li (by omega_arith) fun s₄ u₄ => wp_mov (fun s₅ u₅ => WP.block_nil ?_) (by decide)) s0) hst)
  obtain k : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s.gpr r :=
    fun r a b c d e => by rw [u₅.other r e, u₄.other r d, u₃.other r c, u₂.other r b, u₁.other r a]
  obtain r₅ : Regs s₀ s₅ :=
    ⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hr.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hr.wr],
      by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hr.sp]⟩
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain r4 : s₅.gpr .r4 = BitVec.ofNat 64 ([] : List Byte).length := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    rfl
  refine hH.callUpd_ok (st := p) (dat := q + BitVec.ofNat 64 H.N) (scr := scr s₀) (len := H.B)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, h_st])
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ s4, u₁.other _ s3, h_src])
    (by rw [u₅.other _ (by decide), u₄.gpr]; exact Proof.MdStream.PPC64LE.toNat_ofNat_lt (by omega_arith))
    (by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h27])
    (dps.sub_right (w_sub _)) (dpq.symm.sub_left (buf_sub _)) ((dqs.sub_left (buf_sub _)).sub_right (w_sub _))
    (by rw [r₅.sp]; exact hp.sp48) (by rw [r₅.sp]; exact sp_)
    (by rw [r₅.sp]; exact sq.sub_right (buf_sub _)) (by rw [r₅.sp]; exact hp.ss.sub_right (w_sub _))
    (by
      rw [r₅.rd, r₅.wr]
      refine Covers.of_sub fun r hr' => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl
      · exact cover_off (List.mem_append_right _ wq) (by simp)
      · exact cover_self (List.mem_append_right _ wp)
      · exact cover_pre (R := scR H s₀) (List.mem_append_right _ (by simp [hp.wr])) (by simp))
    (by
      rw [r₅.wr]
      refine Covers.of_sub fun r hr' => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact cover_self wp
      · exact cover_pre (R := scR H s₀) (by simp [hp.wr]) (by simp))
    fun s' rd' wr' sp' f' cs' hpost => hQ s' ⟨rd'.trans r₅.rd, wr'.trans r₅.wr, sp'.trans r₅.sp⟩
      (by rw [← m₅, ← r₅.sp]; exact f')
      (fun r hr => by
        rw [cs' r hr]
        exact k r (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide) (by revert r; decide))
      fun h => by
        have := hpost [] (by rw [m₅]; exact h) r4
        rwa [List.nil_append, m₅] at this

/-- Our variables in `r20`–`r24`, and the callee-saved registers we never
write. -/
structure Vars (s₀ s : State) : Prop where
  r20 : s.gpr .r20 = inn s₀
  r21 : s.gpr .r21 = scr s₀
  r22 : s.gpr .r22 = out s₀
  r23 : s.gpr .r23 = kp s₀
  r24 : s.gpr .r24 = s₀.gpr .r6
  un : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

/-- `Vars` after a call, which preserves the callee-saved registers. -/
theorem Vars.of_pres {s s' : State} (h : Vars s₀ s) (hc : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Vars s₀ s' :=
  ⟨(hc _ (by decide)).trans h.r20, (hc _ (by decide)).trans h.r21, (hc _ (by decide)).trans h.r22,
    (hc _ (by decide)).trans h.r23, (hc _ (by decide)).trans h.r24,
    fun r hr => (hc r (untouched_pres r hr)).trans (h.un r hr)⟩

/-- `Vars` after code writing only `r3`–`r12` and `r25`. -/
theorem Vars.of_keep {s s' : State} (h : Vars s₀ s)
    (hc : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 →
      r ≠ .r11 → r ≠ .r12 → r ≠ .r25 → s'.gpr r = s.gpr r) : Vars s₀ s' := by
  obtain k : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r26, .r27, .r28, .r29, .r30, .r31, .r20,
      .r21, .r22, .r23, .r24], s'.gpr r = s.gpr r := by
    intro r hr
    exact hc r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide)
  exact ⟨(k _ (by simp)).trans h.r20, (k _ (by simp)).trans h.r21, (k _ (by simp)).trans h.r22,
    (k _ (by simp)).trans h.r23, (k _ (by simp)).trans h.r24,
    fun r hr => (k r (by revert r; decide)).trans (h.un r hr)⟩

/-- `padKey`'s writes: the buffer of the state at `q`. -/
theorem pad_frame {K : List Byte} (hK : K.length ≤ H.B) (m : Mem)
    (q : Addr) (c : Byte) :
    Frame [⟨q + BitVec.ofNat 64 H.N, H.B⟩] m
      (writeBytes m (q + BitVec.ofNat 64 H.N) (xorPad (PadKey.K0 K H.B) c)) :=
  VG.WriteBytes.writeBytes_frame _ _ _ (by
    rw [show (xorPad (PadKey.K0 K H.B) c).length = H.B by simp [xorPad, PadKey.K0_length hK]]
    exact Region.contains_self _ _)

theorem pad_bytes (hB : H.B ≤ 128) {K : List Byte} (hK : K.length ≤ H.B) (m : Mem)
    (q : Addr) (c : Byte) :
    bytesAt (writeBytes m (q + BitVec.ofNat 64 H.N) (xorPad (PadKey.K0 K H.B) c))
      (q + BitVec.ofNat 64 H.N) H.B = xorPad (PadKey.K0 K H.B) c := by
  obtain e : (xorPad (PadKey.K0 K H.B) c).length = H.B := by simp [xorPad, PadKey.K0_length hK]
  have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self m (q + BitVec.ofNat 64 H.N)
    (xorPad (PadKey.K0 K H.B) c) (by rw [e]; omega_arith)
  rwa [e] at this

theorem pad36 : (BitVec.ofNat 8 0x36 : Byte) = ipad := rfl
theorem pad5c : (BitVec.ofNat 8 0x5c : Byte) = opad := rfl

/-- `init` without its frame: the callee-saved registers are kept. -/
theorem correctMain (hp : Pre H s₀) :
    WP isa H.initMain s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      hH.SH.Repr s'.mem (inn s₀) (xorPad (blockKey hH.SH.H (K s₀)) ipad) ∧
      hH.SH.Repr s'.mem (out s₀) (xorPad (blockKey hH.SH.H (K s₀)) opad) := by
  have hN : 0 < H.N ∧ H.N ≤ 64 := hH.dims.N
  have hW : H.W % 8 = 0 ∧ H.W ≤ 1024 := hH.dims.so
  have hB : H.B = 64 ∨ H.B = 128 := hH.dims.B
  obtain hB' : H.B ≤ 128 := by omega_arith
  have hkl := hp.kl_le
  obtain hkB : kl s₀ < 2 ^ 64 := (s₀.gpr .r6).isLt
  obtain hbelow : ∀ r ∈ all H s₀, Region.Disjoint (below s₀.sp 48) r ∨ r = below s₀.sp 48 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [.inl hp.si, .inl hp.so, .inl hp.ss, .inr rfl]
  -- Everything that the code writes is in `all`; the key is outside.
  obtain key_keep : ∀ m, Frame (all H s₀) s₀.mem m → bytesAt m (kp s₀) (kl s₀) = K s₀ := by
    intro m hf
    refine Proof.Sha256.Stream.bytesAt_congr fun i hi => hf.bytes (R := kR s₀) ?_ (by simp; omega_arith) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    exacts [hp.k_i, hp.k_o, hp.k_s, hp.sk.symm]
  unfold Hash.initMain
  -- Save our caller's registers, and set up ours.
  refine WP.seq (save_ok hH.dims.so (b := .r7) (by decide)
    (fun d hd₁ hd₂ => ⟨scR H s₀, by simp [hp.wr], contains_offset (show d + 8 ≤ H.W + 48 from hd₂) (by have : d + 8 ≤ H.W + 48 := hd₂; omega_arith)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_)
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => WP.block_nil ?_
  obtain k₆ : ∀ r, r ≠ .r20 → r ≠ .r21 → r ≠ .r22 → r ≠ .r23 → r ≠ .r24 → s₆.gpr r = s₀.gpr r :=
    fun r a b c d e => by
      rw [u₆.other r e, u₅.other r d, u₄.other r c, u₃.other r b, u₂.other r a, g₁]
  obtain r20 : s₆.gpr .r20 = inn s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁]
  obtain r21 : s₆.gpr .r21 = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁]
  obtain r22 : s₆.gpr .r22 = out s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  obtain r23 : s₆.gpr .r23 = kp s₀ := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  obtain r24 : s₆.gpr .r24 = s₀.gpr .r6 := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  obtain sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  obtain m₆ : s₆.mem = saveMem H.W s₀.mem (scr s₀) s₀.gpr := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  obtain f₆ : Frame (all H s₀) s₀.mem s₆.mem := by
    rw [m₆]
    exact (saveMem_frame hH.dims.so _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      show (⟨scr s₀, H.W + 48⟩ : Region) ∈ all H s₀; simp
  obtain sv₆ : Saved H.W (scr s₀) s₀.gpr s₆.mem := by rw [m₆]; exact saveMem_saved hH.dims.so _ _ _
  -- The inner state's hash value.
  refine WP.seq (hH.callInit_ok (st := inn s₀) (by rw [k₆ _ (by decide) (by decide) (by decide)
      (by decide) (by decide)]) ⟨by rw [sp₆]; exact hp.sp48, by rw [sp₆]; exact hp.si⟩
    (by rw [rd₆, wr₆, hp.rd, hp.wr]; exact covers_one (by simp))
    (by rw [wr₆, hp.wr]; exact covers_one (by simp))
    fun s₇ rd₇ wr₇ sp₇ f₇ cs₇ hrI₇ => ?_)
  rw [sp₆] at f₇
  obtain f₇' : Frame (all H s₀) s₀.mem s₇.mem := f₆.trans (f₇.mono (by simp))
  -- The outer state's.
  refine WP.seq (wp_mov fun s₈ u₈ => WP.block_nil ?_)
  refine WP.seq (hH.callInit_ok (st := out s₀) (by rw [u₈.gpr, cs₇ _ (by decide), r22])
      ⟨by rw [u₈.sp, sp₇, sp₆]; exact hp.sp48, by rw [u₈.sp, sp₇, sp₆]; exact hp.so⟩
    (by rw [u₈.rd, u₈.wr, rd₇, wr₇, rd₆, wr₆, hp.rd, hp.wr]; exact covers_one (by simp))
    (by rw [u₈.wr, wr₇, wr₆, hp.wr]; exact covers_one (by simp))
    fun s₉ rd₉ wr₉ sp₉ f₉ cs₉ hrO₉ => ?_)
  rw [u₈.sp, sp₇, sp₆, u₈.mem] at f₉
  obtain f₉' : Frame (all H s₀) s₀.mem s₉.mem := f₇'.trans (f₉.mono (by simp))
  obtain hrI₉ : hH.SH.Repr s₉.mem (inn s₀) [] :=
    hH.repr_keep f₉ (by simp) (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_left (hv_sub _)
      · exact hp.si.symm.sub_left (hv_sub _)) hrI₇
  obtain g₉ : ∀ r, r ≠ .r3 → r ∈ preserved → s₉.gpr r = s₆.gpr r := fun r h3 hr => by
    rw [cs₉ r hr, u₈.other r h3, cs₇ r hr]
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, u₈.rd, rd₇, rd₆]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, u₈.wr, wr₇, wr₆]
  obtain sp₉' : s₉.sp = s₀.sp := by rw [sp₉, u₈.sp, sp₇, sp₆]
  obtain hr₉ : Regs s₀ s₉ := ⟨rd₉', wr₉', sp₉'⟩
  have hS : H.S = H.N + H.B := rfl
  obtain hKl : (K s₀).length ≤ H.B := by simp [bytesAt]; exact hkl
  obtain sv₉ : Saved H.W (scr s₀) s₀.gpr s₉.mem := by
    refine saved_keep (saved_keep sv₆ f₇ ?_) f₉ ?_ <;>
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · first
        | exact (hp.i_s.symm.sub_left (sv_sub _))
        | exact (hp.o_s.symm.sub_left (sv_sub _))
      · exact hp.ss.symm.sub_left (sv_sub _)
  obtain u₉ : ∀ r ∈ untouched, s₉.gpr r = s₀.gpr r := fun r hr => by
    rw [g₉ r (by revert r; decide) (by revert r; decide), k₆ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide)]
  -- `K₀ ⊕ ipad` into the outer state's buffer.
  refine WP.seq (padKey_ok hH hp (dst := .r22) (by decide) (c := 0x36) (by decide) (q := out s₀) (.inr rfl) hr₉
    (by rw [g₉ _ (by decide) (by decide), r22]) (by rw [g₉ _ (by decide) (by decide), r23])
    (by rw [g₉ _ (by decide) (by decide), r24]) (key_keep _ f₉') fun s₁₀ hr₁₀ k₁₀ m₁₀ => ?_)
  obtain fB₁₀ := pad_frame hKl s₉.mem (out s₀) (BitVec.ofNat 8 0x36)
  rw [← m₁₀] at fB₁₀
  obtain fs₁₀ : ∀ R : Region, R.Disjoint (outR H s₀) → R.Disjoint ⟨out s₀ + BitVec.ofNat 64 H.N, H.B⟩ :=
    fun R h => h.sub_right (buf_sub _)
  obtain f₁₀' : Frame (all H s₀) s₀.mem s₁₀.mem :=
    f₉'.trans (fB₁₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨outR H s₀, by simp, buf_sub _⟩)
  obtain hrI₁₀ : hH.SH.Repr s₁₀.mem (inn s₀) [] :=
    hH.repr_keep fB₁₀ (by simp) (by
      simp only [List.mem_singleton]; rintro r rfl; exact fs₁₀ _ (hp.i_o.sub_left (hv_sub _))) hrI₉
  obtain hrO₁₀ : hH.SH.Repr s₁₀.mem (out s₀) [] :=
    hH.repr_keep fB₁₀ (by simp) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hv_buf hN.2 hB' _) hrO₉
  obtain sv₁₀ : Saved H.W (scr s₀) s₀.gpr s₁₀.mem :=
    saved_keep sv₉ fB₁₀ (by
      simp only [List.mem_singleton]; rintro r rfl; exact fs₁₀ _ (hp.o_s.symm.sub_left (sv_sub _)))
  obtain v₆ : Vars s₀ s₆ := ⟨r20, r21, r22, r23, r24, fun r hr => k₆ r (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)⟩
  obtain v₉ : Vars s₀ s₉ := ((v₆.of_pres cs₇).of_keep fun r h3 _ _ _ _ _ _ _ _ _ _ => u₈.other r h3).of_pres cs₉
  obtain v₁₀ : Vars s₀ s₁₀ := v₉.of_keep fun r _ _ _ _ _ a b c d e f => k₁₀ r a b c d e f
  -- Absorb it into the inner state.
  refine WP.seq (updBlock_ok hH hp (st := .r20) (src := .r22) (by decide) (by decide) (.inl ⟨rfl, rfl⟩)
    hr₁₀ v₁₀.r20 v₁₀.r22 v₁₀.r21 fun s₁₁ hr₁₁ f₁₁ cs₁₁ hup => ?_)
  obtain v₁₁ : Vars s₀ s₁₁ := v₁₀.of_pres cs₁₁
  obtain hrI₁₁ : hH.SH.Repr s₁₁.mem (inn s₀) (xorPad (PadKey.K0 (K s₀) H.B) ipad) := by
    have := hup hrI₁₀
    rwa [m₁₀, pad_bytes hB' hKl] at this
  obtain dI : ∀ R : Region, R ∈ [inR H s₀, ⟨scr s₀, H.W⟩, below s₀.sp 48] → R.Disjoint ⟨out s₀, H.N⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl | rfl)
    · exact hp.i_o.sub_right (hv_sub _)
    · exact (hp.o_s.symm.sub_left (w_sub _)).sub_right (hv_sub _)
    · exact hp.so.sub_right (hv_sub _)
  obtain hrO₁₁ : hH.SH.Repr s₁₁.mem (out s₀) [] :=
    hH.repr_keep f₁₁ (by simp) (fun r hr => (dI r (by simpa using hr)).symm) hrO₁₀
  obtain f₁₁' : Frame (all H s₀) s₀.mem s₁₁.mem :=
    f₁₀'.trans (f₁₁.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨inR H s₀, by simp, fun _ h => h⟩
      · exact ⟨scR H s₀, by simp, w_sub _⟩
      · exact ⟨below s₀.sp 48, by simp, fun _ h => h⟩)
  obtain sv₁₁ : Saved H.W (scr s₀) s₀.gpr s₁₁.mem := by
    refine saved_keep sv₁₀ f₁₁ fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.i_s.symm.sub_left (sv_sub _)
    · exact (w_sv hW.2 _).symm
    · exact hp.ss.symm.sub_left (sv_sub _)
  -- `K₀ ⊕ opad` into the inner state's buffer.
  refine WP.seq (padKey_ok hH hp (dst := .r20) (by decide) (c := 0x5c) (by decide) (q := inn s₀) (.inl rfl)
    hr₁₁ v₁₁.r20 v₁₁.r23 v₁₁.r24 (key_keep _ f₁₁') fun s₁₂ hr₁₂ k₁₂ m₁₂ => ?_)
  obtain fB₁₂ := pad_frame hKl s₁₁.mem (inn s₀) (BitVec.ofNat 8 0x5c)
  rw [← m₁₂] at fB₁₂
  obtain v₁₂ : Vars s₀ s₁₂ := v₁₁.of_keep fun r _ _ _ _ _ a b c d e f => k₁₂ r a b c d e f
  obtain hrI₁₂ : hH.SH.Repr s₁₂.mem (inn s₀) (xorPad (PadKey.K0 (K s₀) H.B) ipad) :=
    hH.repr_keep fB₁₂ (by simp [xorPad, PadKey.K0_length hKl]) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hv_buf hN.2 hB' _) hrI₁₁
  obtain hrO₁₂ : hH.SH.Repr s₁₂.mem (out s₀) [] :=
    hH.repr_keep fB₁₂ (by simp) (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_o.symm.sub_left (hv_sub _)).sub_right (buf_sub _)) hrO₁₁
  obtain f₁₂' : Frame (all H s₀) s₀.mem s₁₂.mem :=
    f₁₁'.trans (fB₁₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨inR H s₀, by simp, buf_sub _⟩)
  obtain sv₁₂ : Saved H.W (scr s₀) s₀.gpr s₁₂.mem :=
    saved_keep sv₁₁ fB₁₂ (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.symm.sub_left (sv_sub _)).sub_right (buf_sub _))
  -- Absorb it into the outer state.
  refine WP.seq (updBlock_ok hH hp (st := .r22) (src := .r20) (by decide) (by decide) (.inr ⟨rfl, rfl⟩)
    hr₁₂ v₁₂.r22 v₁₂.r20 v₁₂.r21 fun s₁₃ hr₁₃ f₁₃ cs₁₃ hup' => ?_)
  obtain v₁₃ : Vars s₀ s₁₃ := v₁₂.of_pres cs₁₃
  obtain hrO₁₃ : hH.SH.Repr s₁₃.mem (out s₀) (xorPad (PadKey.K0 (K s₀) H.B) opad) := by
    have := hup' hrO₁₂
    rwa [m₁₂, pad_bytes hB' hKl] at this
  obtain hrI₁₃ : hH.SH.Repr s₁₃.mem (inn s₀) (xorPad (PadKey.K0 (K s₀) H.B) ipad) := by
    refine hH.repr_keep f₁₃ (by simp [xorPad, PadKey.K0_length hKl]) (fun r hr => ?_) hrI₁₂
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.i_o.sub_left (hv_sub _)
    · exact (hp.i_s.sub_left (hv_sub _)).sub_right (w_sub _)
    · exact hp.si.symm.sub_left (hv_sub _)
  obtain sv₁₃ : Saved H.W (scr s₀) s₀.gpr s₁₃.mem := by
    refine saved_keep sv₁₂ f₁₃ fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.o_s.symm.sub_left (sv_sub _)
    · exact (w_sv hW.2 _).symm
    · exact hp.ss.symm.sub_left (sv_sub _)
  -- Restore our caller's registers.
  refine restore_ok hH.dims.so (scr := scr s₀) v₁₃.r21
    (fun d hd₁ hd₂ => ⟨scR H s₀, by simp [hr₁₃.rd, hr₁₃.wr, hp.wr],
      contains_offset (show d + 8 ≤ H.W + 48 from hd₂) (by have : d + 8 ≤ H.W + 48 := hd₂; omega_arith)⟩)
    s₀.gpr sv₁₃ fun s' hsv ho hmem _ _ hsp => ⟨preserved_of hsv fun r hr => ?_, by rw [hsp, hr₁₃.sp], ?_⟩
  · rw [ho r (by simp only [Hash.savedAt, List.map_cons, List.map_nil]; revert r; decide)]
    exact v₁₃.un r hr
  · rw [hmem, blockKey_eq hH hp, pad36, pad5c] at *
    exact ⟨hrI₁₃, hrO₁₃⟩

/-! ## The frame -/

include hH in
theorem initMain_fdepth : H.initMain.fdepth ≤ 1 := by
  have := hH.initFd
  have := hH.updFd
  simp only [Hash.initMain, Hash.callInit, Hash.callUpd, Hash.padKey, Hash.updBlock, Hash.keyLoop,
    Hash.padLoop, Code.fdepth, Nat.max_le]
  omega_arith

include hH in
theorem initMain_pf : pushFrames H.initMain = true := by
  simp [Hash.initMain, Hash.callInit, Hash.callUpd, Hash.padKey, Hash.updBlock, Hash.keyLoop,
    Hash.padLoop, pushFrames, hH.initPf, hH.updPf]

/-- The state `initMain` starts in: the link register moved to `r0`, then
pushed in a frame. -/
abbrev inner (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

/-- The frame's push leaves a region disjoint from it as it was. -/
theorem inner_bytes {s₀ : State} {R : Region} (hd : (below s₀.sp 48).Disjoint R) (hR : R.len < 2 ^ 64) {i : Nat}
    (hi : i < R.len) : (inner s₀).mem (R.base + BitVec.ofNat 64 i) = s₀.mem (R.base + BitVec.ofNat 64 i) :=
  Proof.MdStream.PPC64LE.write_frame_bytes hd hR hi

theorem pre_inner {s₀ : State} (hp : (initG hH.SH (H.W + 48) 96).pre s₀) (hS : hH.SH.stateBytes = H.S) :
    Pre H (inner s₀) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hp
  rw [hS] at h2 h3 h4 h5 h6 h7 h10 h11
  obtain sub : Region.Sub (below (s₀.sp - 48) 48) (below s₀.sp 96) := below_body s₀.sp 48
  exact ⟨by rw [hH.hB] at h0; exact h0, h1, h2, h3, h4, h5, h6, h7, h8,
    by show 48 ≤ (s₀.sp - 48).toNat; bv_omega, h10.sub_left sub, h11.sub_left sub, h12.sub_left sub,
    h13.sub_left sub⟩

/-- `init`, with its frame. -/
theorem correct {s₀ : State} (hp : (initG hH.SH (H.W + 48) 96).pre s₀) :
    WP isa H.init s₀ fun s' => abiPreserved s₀ s' ∧ (initG hH.SH (H.W + 48) 96).post s₀ s' := by
  obtain hpi := pre_inner hH hp hH.hS
  obtain ⟨_, _, h2, _, _, _, _, _, _, h9, h10, h11, h12, h13⟩ := hp
  obtain hsub : Region.Sub (below s₀.sp 48) (below s₀.sp 96) := below_sub (by omega_arith) (by omega_arith)
  refine WP.seq (Proof.MdStream.PPC64LE.WP.cons exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by show 48 ≤ s₀.sp.toNat; omega_arith) (fun R hR => ?_) (WP.mono (correctMain hH hpi)
    fun s' ⟨hk, hsp, hI, hO⟩ => ?_) (by have := initMain_fdepth hH; omega_arith) (initMain_pf hH)
  · rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, h2] at hR
    obtain hf : Region.Sub ⟨s₀.sp - 48 + 32, 16⟩ (below s₀.sp 96) :=
      fun a h => hsub a (Proof.MdStream.PPC64LE.frame_sub s₀.sp a h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact h10.sub_left hf
    · exact h11.sub_left hf
    · exact h13.sub_left hf
  · refine Proof.MdStream.PPC64LE.WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed, State.write, h0, ite_false]
    · simp [State.write]
    · have hK : K (inner s₀) = bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat :=
        Proof.Sha256.Stream.bytesAt_congr fun i hi =>
          inner_bytes (R := ⟨s₀.gpr .r5, (s₀.gpr .r6).toNat⟩) (h12.symm.sub_right hsub).symm
            (s₀.gpr .r6).isLt hi
      rw [hK] at hI hO
      exact ⟨hI, hO⟩

end VG.Proof.Hmac.Stream.PPC64LE.Init
