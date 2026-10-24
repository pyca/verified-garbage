module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic

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
  simp [K0]; omega

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
  omega

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
  have e := writeBytes_snoc s₀.mem (bp (H := H) s₀ dst) (blk K H.B c j)
    ((K0 K H.B).getD j 0 ^^^ BitVec.ofNat 8 c) (by rw [blk_length hy (Nat.le_of_lt hj)]; have := hy.B; omega)
  rw [blk_length hy (Nat.le_of_lt hj)] at e
  rw [hm, blk_succ c (by rw [K0_length (by rw [hy.K_length]; exact hy.kl_le)]; exact hj), e]

theorem writeBytes_out {m : Mem} {q a : Addr} {xs : List Byte} {n : Nat}
    (h : ¬ (⟨q, n⟩ : Region).Contains a 1) (hl : xs.length ≤ n) : writeBytes m q xs a = m a := by
  simp only [writeBytes, Region.Contains] at h ⊢
  split
  · omega
  · rfl

/-- Key byte `j`, while the block is written. -/
theorem key_byte (hy : Hyp H s₀ dst kl K) {j j' : Nat} (hj : j < kl) (hj' : j' ≤ H.B) {m : Mem}
    (hm : m = writeBytes s₀.mem (bp (H := H) s₀ dst) (blk K H.B c j')) :
    m (s₀.gpr .r23 + BitVec.ofNat 64 j) = (K0 K H.B).getD j 0 := by
  have hl := hy.K_length
  have := hy.B
  have := hy.kl_le
  rw [hm, writeBytes_out (n := H.B) (hy.disj _ (contains_offset (by omega) (by omega)))
      (by rw [blk_length hy hj']; exact hj'), K0_getD_lt (by omega), ← hy.key]
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
  have hjB : j < H.B := Nat.lt_of_lt_of_le hj hy.kl_le
  obtain ⟨d0, d8, d9, d10, d11, d12, d31⟩ := hy.dst
  have hd : s.gpr dst = s₀.gpr dst := h.keep dst d8 d9 d10 d11 d12 d31
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
  have k : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r25 → s₇.gpr r = s.gpr r :=
    fun r a b c d e => by
      rw [u₇.other r c, u₆.other r e, u₅.other r b, u₄.gpr, u₃.other r d, u₂.other r a, u₁.other r a]
  have v : (s₃.gpr .r8).setWidth 8 = (K0 K H.B).getD j 0 ^^^ BitVec.ofNat 8 c := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.r12, xor_byte,
      key_byte hy hj (by omega) h.mem]
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
      u₂.other _ (by decide), u₁.other _ (by decide), h.r10, show kl - (j + 1) = kl - j - 1 by omega,
      ← sub_ofNat (a := kl - j) (b := 1) (by omega)]

theorem pad_step (hy : Hyp H s₀ dst kl K) {j : Nat} (hj : kl ≤ j) (hj' : j < H.B) {s : State}
    (h : PInv (H := H) s₀ dst c K j s) :
    WP isa (.block (padBody H dst)) s (PInv (H := H) s₀ dst c K (j + 1)) := by
  obtain ⟨d0, d8, d9, d10, d11, d12, d31⟩ := hy.dst
  have hd : s.gpr dst = s₀.gpr dst := h.keep dst d8 d9 d10 d11 d12 d31
  unfold padBody
  refine wp_add fun s₁ u₁ => ?_
  refine wp_stb (a := bp (H := H) s₀ dst + BitVec.ofNat 64 j) hy.N ?_
    (by rw [u₁.wr, h.wr]; exact hy.out j hj') fun s₂ u₂ => ?_
  · rw [u₁.gpr, hd, h.r25, stb_addr]
  refine wp_addi (by decide) fun s₃ u₃ => wp_subi (by decide) fun s₄ u₄ => WP.block_nil ?_
  have k : ∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r25 → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [u₄.other r a, u₃.other r c, u₂.gpr, u₁.other r b]
  have v : (s₁.gpr .r12).setWidth 8 = (K0 K H.B).getD j 0 ^^^ BitVec.ofNat 8 c := by
    rw [u₁.other _ (by decide), h.r12, K0_getD_ge (by rw [hy.K_length]; exact hj), byte_ofNat]
  refine ⟨⟨fun r a b c d e f => (k r c d f).trans (h.keep r a b c d e f),
    by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [k _ (by decide) (by decide) (by decide), h.r12], ?_, ?_⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r25, BitVec.ofNat_add]
  · rw [u₄.mem, u₃.mem, u₂.mem, v, u₁.mem]
    exact Inv.write hy hj' h.mem
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r10,
      show H.B - (j + 1) = H.B - j - 1 by omega, ← sub_ofNat (a := H.B - j) (b := 1) (by omega)]

theorem key_loop_ok (hy : Hyp H s₀ dst kl K) {s : State} (h : KInv (H := H) s₀ dst c kl K 0 s)
    (hk : 0 < kl) : WP isa (H.keyLoop dst) s (Inv (H := H) s₀ dst c K kl) := by
  have := hy.kl_le
  have := hy.B
  rw [keyLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = kl - j ∧ j < kl ∧ KInv (H := H) s₀ dst c kl K j s) ?_ kl s
    ⟨0, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hb⟩
  refine WP.mono (key_step hy hj hb) fun s' hb' => ?_
  have hz : isa.eval (.nonzero .d .r10) s' = some (decide (kl - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r10) s' = _
    rw [eval_nonzero, hb'.r10, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : kl - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rw [show kl = j + 1 by omega]; exact hb'.toInv
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hb'⟩

theorem pad_loop_ok (hy : Hyp H s₀ dst kl K) {s : State} (h : PInv (H := H) s₀ dst c K kl s)
    (hk : kl < H.B) : WP isa (H.padLoop dst) s (Inv (H := H) s₀ dst c K H.B) := by
  have := hy.B
  rw [padLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = H.B - j ∧ kl ≤ j ∧ j < H.B ∧ PInv (H := H) s₀ dst c K j s) ?_
    (H.B - kl) s ⟨kl, rfl, Nat.le_refl _, hk, h⟩
  rintro n s ⟨j, rfl, hj, hj', hb⟩
  refine WP.mono (pad_step hy hj hj' hb) fun s' hb' => ?_
  have hz : isa.eval (.nonzero .d .r10) s' = some (decide (H.B - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r10) s' = _
    rw [eval_nonzero, hb'.r10, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : H.B - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rw [show H.B = j + 1 by omega]; exact hb'.toInv
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, by omega, hb'⟩

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
  have hI : Inv (H := H) s₀ dst c K 0 s₄ :=
    ⟨fun r a b c d e f => by rw [u₄.other r c, u₃.other r b, u₂.other r f, u₁.other r e],
      by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr],
      by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr],
      by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; simp [blk, writeBytes_nil]⟩
  have h10 : s₄.gpr .r10 = BitVec.ofNat 64 kl := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hy.r24]
  have h9 : s₄.gpr .r9 = s₀.gpr .r23 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  -- The key loop.
  refine WP.seq (WP.mono (Q := Inv (H := H) s₀ dst c K kl) ?_ fun s₅ h₅ => ?_)
  · have hz : eval (.zero .d .r10) s₄ = some (decide (kl = 0)) := by
      rw [eval_zero, h10, ofNat_beq_zero (by omega)]
    refine WP.ite (decide (kl = 0)) hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      exact WP.block_nil hI
    · simp only [decide_eq_false_iff_not] at hb
      exact key_loop_ok hy ⟨hI, by rw [h9, BitVec.add_zero], by rw [h10, Nat.sub_zero]⟩ (by omega)
  -- The pad loop.
  refine WP.seq (wp_li hy.B fun s₆ u₆ => wp_sub fun s₇ u₇ => WP.block_nil ?_)
  have hI₇ : Inv (H := H) s₀ dst c K kl s₇ :=
    ⟨fun r a b c d e f => by rw [u₇.other r c, u₆.other r c]; exact h₅.keep r a b c d e f,
      by rw [u₇.rd, u₆.rd, h₅.rd], by rw [u₇.wr, u₆.wr, h₅.wr], by rw [u₇.sp, u₆.sp, h₅.sp],
      by rw [u₇.other _ (by decide), u₆.other _ (by decide), h₅.r12],
      by rw [u₇.other _ (by decide), u₆.other _ (by decide), h₅.r25],
      by rw [u₇.mem, u₆.mem, h₅.mem]⟩
  have h10' : s₇.gpr .r10 = BitVec.ofNat 64 (H.B - kl) := by
    rw [u₇.gpr, u₆.gpr, u₆.other _ (by decide), h₅.r25, sub_ofNat (by omega)]
  have hz : eval (.zero .d .r10) s₇ = some (decide (H.B - kl = 0)) := by
    rw [eval_zero, h10', ofNat_beq_zero (by omega)]
  refine WP.ite (decide (H.B - kl = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hQ _ (by rw [show H.B = kl by omega]; exact hI₇))
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.mono (pad_loop_ok hy ⟨hI₇, h10'⟩ (by omega)) hQ

end VG.Proof.Hmac.Stream.PPC64LE.PadKey
