import VerifiedGarbage.Proof.AesOcb.X86_64.Args
import VerifiedGarbage.Proof.Ocb.LowBit
import VerifiedGarbage.Proof.Gcm.X86_64.Rev

/-!
# AES-OCB on x86-64: the table of `L_j` (`table`, `lAddr`)

Untrusted: everything here is checked by Lean. `L_j` is kept in the 16-byte
slot `slot j` of the table at `W + tblO` (`Tbl`), the top 6 bits of
`debruijn · 2^j`, which differ for every `j < 64` (`slot_inj`). `lAddr`
finds the slot of `L_{ntz(i)}` from `i` without a branch: `2^{ntz(i)}` is
`i ∧ (0 − i)` (`Proof.Ocb.lowbit`, `lAddr_ok`). `table` writes `L_j` for
every `j` with `2^j ≤ M = (len | aad_len) / 16`, doubling each from the one
before (`table_ok`).

A block in an SSE register is the 16 bytes in memory order, the first in
the least significant byte: `rv` byte-reverses it to OCB's block
(`blockAtMem_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesCcm.X86_64 (runBlock_append eval_e eval_ne toNat_ofNat_of_lt)

/-! ## Blocks in SSE registers -/

/-- OCB's block of the 16 bytes in an SSE register. -/
abbrev rv (x : BitVec 128) : Block := XBinOp.eval .pshufb x Proof.Gcm.X86_64.revMask

theorem blockAtMem_eq (m : Mem) (p : Addr) : blockAtMem m p = rv (m.readW p 128) :=
  Proof.Gcm.X86_64.blockAt_eq m p

theorem rv_xor (a b : BitVec 128) : rv (a ^^^ b) = rv a ^^^ rv b := Proof.Gcm.X86_64.pshufb_rev_xor a b

theorem blockAtMem_writeW (m : Mem) (p : Addr) (v : BitVec 128) : blockAtMem (m.writeW p v) p = rv v := by
  rw [blockAtMem_eq, Mem.readW_writeW_self m p 16 _ (by decide)]

/-! ## Slots -/

/-- The slot of `L_t` in the table: the top 6 bits of `2^t · debruijn`. -/
def slot (t : Nat) : Nat := 2 ^ t * debruijn.toNat % 2 ^ 64 / 2 ^ 58

theorem slot_lt (t : Nat) : slot t < 64 := by
  unfold slot
  have := Nat.mod_lt (2 ^ t * debruijn.toNat) (show 0 < 2 ^ 64 by decide)
  omega

/-- The inverse of `slot`, for `t < 64`. -/
def slotInv : List Nat :=
  [0, 1, 2, 53, 3, 7, 54, 27, 4, 38, 41, 8, 34, 55, 48, 28, 62, 5, 39, 46, 44, 42, 22, 9, 24, 35, 59, 56,
   49, 18, 29, 11, 63, 52, 6, 26, 37, 40, 33, 47, 61, 45, 43, 21, 23, 58, 17, 10, 51, 25, 36, 32, 60, 20,
   57, 16, 50, 31, 19, 15, 30, 14, 13, 12]

theorem slotInv_slot : ∀ t < 64, slotInv.getD (slot t) 0 = t := by decide

theorem slot_inj {a b : Nat} (ha : a < 64) (hb : b < 64) (h : slot a = slot b) : a = b := by
  rw [← slotInv_slot a ha, ← slotInv_slot b hb, h]

theorem slot_zero : slot 0 = 0 := by decide
theorem slot_one : slot 1 = 1 := by decide

/-- `slotOf`'s value: `16 ·` the top 6 bits. -/
theorem slotOf_val (x : BitVec 64) : (x >>> 58).rotateRight 60 = BitVec.ofNat 64 (16 * (x.toNat / 2 ^ 58)) := by
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateRight, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have h1 : x.toNat / 2 ^ 58 < 64 := by omega
  have h2 : x.toNat / 2 ^ 58 / 2 ^ 60 = 0 := by omega
  rw [h2, Nat.zero_or, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `2^t · debruijn` (`mul`), then `slotOf`: `16 · slot t`. -/
theorem slot_val (t : Nat) (ht : t < 64) :
    ((BitVec.ofNat 64 ((BitVec.ofNat 64 (2 ^ t)).toNat * debruijn.toNat)) >>> 58).rotateRight 60 =
      BitVec.ofNat 64 (16 * slot t) := by
  rw [slotOf_val, BitVec.toNat_ofNat, toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) ht)]
  rfl

/-- `lAddr`: `rcx ← W + 16 · slot(ntz(i))`. -/
theorem lAddr_ok {W : Addr} {s : State} (h15 : s.gpr .r15 = W) {i : Nat} (hi : 0 < i) (hi' : i < 2 ^ 64)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) :
    ∃ s', runBlock isa lAddr s = some s' ∧ s'.gpr .rcx = W + BitVec.ofNat 64 (16 * slot (ntz i)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.xmm = s.xmm ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ht : ntz i < 64 := by
    have := Proof.Ocb.two_pow_ntz_le hi
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp (Nat.lt_of_le_of_lt this hi')
  refine ⟨_, by orun [lAddr, slotOf, execMul, h15, hbp], ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15, hbp,
      sext0, Proof.Ocb.lowbit hi hi', slot_val _ ht]
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, ite_false]
  all_goals rfl

/-! ## The table -/

/-- The table at `W + tblO` holds `L_j` (`lAt l j`) in slot `slot j`, for
every `j` with `2^j ≤ M`, where `M < 2^60`. -/
structure Tbl (W : Addr) (l : Block) (M : Nat) (m : Mem) : Prop where
  lt : M < 2 ^ 60
  val : ∀ j, 2 ^ j ≤ M → blockAtMem m (W + BitVec.ofNat 64 (tblO + 16 * slot j)) = lAt l j

theorem lt_of_two_pow {j M : Nat} (h : 2 ^ j ≤ M) {k : Nat} (hM : M < 2 ^ k) : j < k :=
  (Nat.pow_lt_pow_iff_right (by decide)).mp (Nat.lt_of_le_of_lt h hM)

/-- A slot of the table is in `wT W`. -/
theorem slot_sub (W : Addr) (j : Nat) : Region.Sub ⟨W + BitVec.ofNat 64 (tblO + 16 * slot j), 16⟩ (wT W) :=
  Offset.sub W (by simp only [tblO]; omega) (by have := slot_lt j; simp only [tblO]; omega)

theorem Tbl.frame {W : Addr} {l : Block} {M : Nat} {m m' : Mem} {rs : List Region} (T : Tbl W l M m)
    (h : Frame rs m m') (hd : ∀ r ∈ rs, (wT W).Disjoint r) : Tbl W l M m' :=
  ⟨T.lt, fun j hj => by rw [blockAtMem_frame h fun r hr => (hd r hr).sub_left (slot_sub W j), T.val j hj]⟩

/-- The table holds `L_{ntz(i)}` for every block index `i ≤ len / 16` of a
string of `len` bytes. -/
def TblL (W : Addr) (l : Block) (len : Nat) (m : Mem) : Prop := ∃ M, Tbl W l M m ∧ len / 16 ≤ M

theorem TblL.frame {W : Addr} {l : Block} {len : Nat} {m m' : Mem} {rs : List Region} (T : TblL W l len m)
    (h : Frame rs m m') (hd : ∀ r ∈ rs, (wT W).Disjoint r) : TblL W l len m' :=
  let ⟨M, T, hM⟩ := T
  ⟨M, T.frame h hd, hM⟩

theorem Tbl.mono {W : Addr} {l : Block} {M M' : Nat} {m : Mem} (T : Tbl W l M m) (h : M' ≤ M) : Tbl W l M' m :=
  ⟨by have := T.lt; omega, fun j hj => T.val j (by omega)⟩

/-- The table misses the rest of `W`. -/
theorem Lay.wT_w {K W SP : Addr} (L : Lay K W SP) {a k : Nat} (h : a + k ≤ 2560) :
    (wT W).Disjoint ⟨W + BitVec.ofNat 64 a, k⟩ :=
  L.w_w (.inr h) (by decide) (by omega)

/-- `L_{ntz(i)}`, for `0 < i ≤ M`, is in the table. -/
theorem Tbl.ntz {W : Addr} {l : Block} {M : Nat} {m : Mem} (T : Tbl W l M m) {i : Nat} (hi : 0 < i) (hM : i ≤ M) :
    blockAtMem m (W + BitVec.ofNat 64 (tblO + 16 * slot (ntz i))) = lAt l (ntz i) :=
  T.val _ (Nat.le_trans (Proof.Ocb.two_pow_ntz_le hi) hM)

/-- `W + 16 · slot t + tblO`. -/
theorem slot_addr (W : Addr) (t : Nat) :
    W + BitVec.ofNat 64 (16 * slot t) + BitVec.ofNat 64 tblO = W + BitVec.ofNat 64 (tblO + 16 * slot t) := by
  rw [Offset.add_add, Nat.add_comm]

/-- What `table` leaves. -/
structure TablePost (K W SP : Addr) (l : Block) (M : Nat) (s s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame [wT W] s.mem s'.mem
  tbl : Tbl W l M s'.mem
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The loop of `table`. -/
abbrev tableBody : List Instr :=
  [.alu .add .r11 (.reg .r11), mvr .rax .r11, .mul .rsi] ++ slotOf ++
    [.alu .add .rax (.reg .r15), mvr .rdi .rax] ++ dbl .r10 0 .rdi tblO ++
    [mvr .r10 .rdi, addi .r10 tblO, .shift .shr .r9 1, .alu .test .r9 (.reg .r9)]

theorem shr1' {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> 1 = BitVec.ofNat 64 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hv, toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem ofNat_self_beq {a : Nat} (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a &&& BitVec.ofNat 64 a == 0) = decide (a = 0) :=
  Proof.AesCcm.X86_64.and_self_beq ha

/-- One step of `table`: `L_{j+1} = double(L_j)` to its slot. -/
theorem tableStep_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {j x : Nat} (hj : j + 1 < 64)
    (hx : x < 2 ^ 64) (h9 : t.gpr .r9 = BitVec.ofNat 64 x)
    (h10 : t.gpr .r10 = W + BitVec.ofNat 64 (tblO + 16 * slot j)) (h11 : t.gpr .r11 = BitVec.ofNat 64 (2 ^ j))
    (hsi : t.gpr .rsi = debruijn) :
    ∃ t', runBlock isa tableBody t = some t' ∧ t'.gpr .r9 = BitVec.ofNat 64 (x / 2) ∧
      t'.zf = some (decide (x / 2 = 0)) ∧ t'.gpr .r10 = W + BitVec.ofNat 64 (tblO + 16 * slot (j + 1)) ∧
      t'.gpr .r11 = BitVec.ofNat 64 (2 ^ (j + 1)) ∧ t'.gpr .rsi = debruijn ∧
      BlkStep W (tblO + 16 * slot (j + 1)) (double (blockAtMem t.mem (W + BitVec.ofNat 64 (tblO + 16 * slot j))))
        [.rax, .rdx, .rcx, .r8, .r9, .r10, .r11, .rdi] t t' := by
  have h15 := E.r15
  have hp : 2 ^ (j + 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hj
  have e11 : BitVec.ofNat 64 (2 ^ j) + BitVec.ofNat 64 (2 ^ j) = BitVec.ofNat 64 (2 ^ (j + 1)) := by
    rw [BitVec.ofNat_add_ofNat, Nat.pow_succ, Nat.mul_two]
  obtain ⟨t₁, run₁, h11₁, hdi₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      ([.alu .add .r11 (.reg .r11), mvr .rax .r11, .mul .rsi] ++ slotOf ++ [.alu .add .rax (.reg .r15), mvr .rdi .rax])
        t = some t₁ ∧ t₁.gpr .r11 = BitVec.ofNat 64 (2 ^ (j + 1)) ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 (16 * slot (j + 1)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r11 → r ≠ .rdi → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by orun [slotOf, execMul, h11, hsi, h15], ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h11, e11]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h11, hsi, h15, e11,
        slot_val _ hj, BitVec.add_comm (BitVec.ofNat 64 (16 * slot (j + 1)))]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, ite_false]
    all_goals rfl
  have hslot := slot_lt (j + 1)
  have hslotj := slot_lt j
  have w₀ : InRegions t₁.wr (W + BitVec.ofNat 64 (16 * slot (j + 1)) + BitVec.ofNat 64 tblO) 8 := by
    rw [slot_addr, wr₁]; exact E.perm.wW (by simp only [tblO]; omega)
  have w₁ : InRegions t₁.wr (W + BitVec.ofNat 64 (16 * slot (j + 1)) + BitVec.ofNat 64 (tblO + 8)) 8 := by
    rw [Offset.add_add, wr₁, show 16 * slot (j + 1) + (tblO + 8) = tblO + 16 * slot (j + 1) + 8 by omega]
    exact E.perm.wW (by simp only [tblO]; omega)
  have r₀ : InRegions (t₁.rd ++ t₁.wr) (W + BitVec.ofNat 64 (tblO + 16 * slot j) + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero, rd₁, wr₁]; exact E.perm.wR (by simp only [tblO]; omega)
  have r₁ : InRegions (t₁.rd ++ t₁.wr) (W + BitVec.ofNat 64 (tblO + 16 * slot j) + BitVec.ofNat 64 (0 + 8)) 8 := by
    rw [Offset.add_add, rd₁, wr₁]; exact E.perm.wR (by simp only [tblO]; omega)
  obtain ⟨t₂, run₂, B₂⟩ := dbl_ok (s := t₁) (b := .r10) (o := .rdi) (a := 0) (d := tblO) hdi₁
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h10]) (by decide) (by decide) (by decide)
    (by decide) (by decide) r₀ r₁ w₀ w₁
  have hdi₂ : t₂.gpr .rdi = W + BitVec.ofNat 64 (16 * slot (j + 1)) := by rw [B₂.gpr _ (by decide), hdi₁]
  have h9₂ : t₂.gpr .r9 = BitVec.ofNat 64 x := by
    rw [B₂.gpr _ (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide), h9]
  obtain ⟨t₃, run₃, h9₃, zf₃, h10₃, g₃, m₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa
      [mvr .r10 .rdi, addi .r10 tblO, .shift .shr .r9 1, .alu .test .r9 (.reg .r9)] t₂ = some t₃ ∧
      t₃.gpr .r9 = BitVec.ofNat 64 (x / 2) ∧ t₃.zf = some (decide (x / 2 = 0)) ∧
      t₃.gpr .r10 = W + BitVec.ofNat 64 (tblO + 16 * slot (j + 1)) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by orun [hdi₂, h9₂], ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h9₂, shr1' hx]
    · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h9₂,
        shr1' hx, ofNat_self_beq (show x / 2 < 2 ^ 64 by omega)]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hdi₂]
      exact slot_addr W (j + 1)
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, ite_false]
    all_goals rfl
  refine ⟨t₃, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃],
    h9₃, zf₃, h10₃, ?_, ?_, ?_⟩
  · rw [g₃ _ (by decide) (by decide), B₂.gpr _ (by decide), h11₁]
  · rw [g₃ _ (by decide) (by decide), B₂.gpr _ (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide),
      hsi]
  · have fr := B₂.frame
    have v := B₂.val
    rw [slot_addr] at fr v
    refine ⟨by rw [m₃, ← m₁]; exact fr, ?_,
      fun r hr => ?_, by rw [rd₃, B₂.rd, rd₁], by rw [wr₃, B₂.wr, wr₁]⟩
    · rw [m₃, v, m₁, BitVec.add_zero]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
      rw [g₃ r h5 h6, B₂.gpr r (by simp [h1, h2, h3, h4]), g₁ r h1 h2 h7 h8]

theorem shrK {v : Nat} (hv : v < 2 ^ 64) (k : Nat) : BitVec.ofNat 64 v >>> k = BitVec.ofNat 64 (v / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hv, toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv),
    Nat.shiftRight_eq_div_pow]

theorem ofNat_or {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (a ||| b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb, toNat_ofNat_of_lt (Nat.or_lt_two_pow ha hb)]

/-- The table, for `M = (len | aad_len) / 16`. -/
theorem table_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {l : Block} {n al : Nat} (hn : n < 2 ^ 64)
    (hal : al < 2 ^ 64) (hlen : s.mem.readW (W + BitVec.ofNat 64 lenO) 64 = BitVec.ofNat 64 n)
    (halen : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa table s (TablePost K W SP l ((n ||| al) / 16) s) := by
  have h15 := E.r15
  have hor : n ||| al < 2 ^ 64 := Nat.or_lt_two_pow hn hal
  generalize hM : (n ||| al) / 16 = M
  have hM60 : M < 2 ^ 60 := by omega
  obtain ⟨s₁, run₁, B₁⟩ := copy16_ok (s := s) (a := l0O) (d := tblO) h15 (E.perm.wR (by decide))
    (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have r₁ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 216) 8 := by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide)
  have r₂ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 248) 8 := by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide)
  have h15₁ : s₁.gpr .r15 = W := by rw [B₁.gpr _ (by decide), h15]
  have hlen₁ : s₁.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n := by
    rw [B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact E.perm.w |> fun _ => Offset.disjoint W (.inl (by decide))
        (by decide) (by decide)) (by decide)]; exact hlen
  have halen₁ : s₁.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 al := by
    rw [B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 248, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inl (by decide))
        (by decide) (by decide)) (by decide)]; exact halen
  obtain ⟨s₂, run₂, h9₂, zf₂, h10₂, h11₂, hsi₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [ld .r9 .r15 lenO, ld .rax .r15 alenO, .alu .or .r9 (.reg .rax), .shift .shr .r9 5, mvr .r10 .r15,
        addi .r10 tblO, .mov .r11 (.imm 1), .movImm64 .rsi debruijn, .alu .test .r9 (.reg .r9)] s₁ = some s₂ ∧
      s₂.gpr .r9 = BitVec.ofNat 64 (M / 2 ^ (0 + 1)) ∧ s₂.zf = some (decide (M / 2 ^ (0 + 1) = 0)) ∧
      s₂.gpr .r10 = W + BitVec.ofNat 64 (tblO + 16 * slot 0) ∧ s₂.gpr .r11 = BitVec.ofNat 64 (2 ^ 0) ∧
      s₂.gpr .rsi = debruijn ∧
      (∀ r ∈ calleeSaved, s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have e : (n ||| al) / 2 ^ 5 = M / 2 ^ (0 + 1) := by rw [← hM]; omega
    refine ⟨_, by orun [h15₁, r₁, r₂, hlen₁, halen₁], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hlen₁, halen₁,
        ofNat_or hn hal, shrK hor, e]
    · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hlen₁,
        halen₁, ofNat_or hn hal, shrK hor, e, ofNat_self_beq (show M / 2 ^ (0 + 1) < 2 ^ 64 by omega)]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₁, slot_zero]; rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, sext1]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₂ : Env K W SP s₂ := E.of_saved (fun r hr => by
      rw [g₂ r hr, B₁.gpr r (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)])
    (by rw [rd₂, B₁.rd]) (by rw [wr₂, B₁.wr])
  have sv₂ : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [g₂ r hr, B₁.gpr r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  have fr₂ : Frame [wT W] s.mem s₂.mem := by
    rw [m₂]; exact B₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨wT W, List.mem_singleton_self _, by
        have := slot_sub W 0; rwa [slot_zero, Nat.mul_zero, Nat.add_zero] at this⟩
  have v₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 (tblO + 16 * slot 0)) = lAt l 0 := by
    rw [m₂, slot_zero, Nat.mul_zero, Nat.add_zero, B₁.val, hl0]
  unfold table
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.ite _ (eval_e zf₂) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : M / 2 = 0 := by simpa using hb
    refine ⟨E₂, fr₂, ⟨hM60, fun j hj => ?_⟩, sv₂, by rw [rd₂, B₁.rd], by rw [wr₂, B₁.wr]⟩
    have : j = 0 := by
      have := lt_of_two_pow hj (k := 1) (by omega)
      omega
    subst this; exact v₂
  have hpos : 0 < M / 2 ^ (0 + 1) := by have := of_decide_eq_false hb; omega
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = M / 2 ^ (j + 1) ∧ 0 < M / 2 ^ (j + 1) ∧
      t.gpr .r9 = BitVec.ofNat 64 (M / 2 ^ (j + 1)) ∧ t.gpr .r10 = W + BitVec.ofNat 64 (tblO + 16 * slot j) ∧
      t.gpr .r11 = BitVec.ofNat 64 (2 ^ j) ∧ t.gpr .rsi = debruijn ∧
      (∀ k ≤ j, blockAtMem t.mem (W + BitVec.ofNat 64 (tblO + 16 * slot k)) = lAt l k) ∧
      Frame [wT W] s.mem t.mem ∧ Env K W SP t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr) ?_ (M / 2 ^ (0 + 1)) _
    ⟨0, rfl, hpos, h9₂, h10₂, h11₂, hsi₂, fun k hk => (Nat.le_zero.mp hk) ▸ v₂,
      fr₂, E₂, sv₂, by rw [rd₂, B₁.rd], by rw [wr₂, B₁.wr]⟩
  rintro k t ⟨j, rfl, hpos, h9, h10, h11, hsi, hv, fr, Et, sv, rd, wr⟩
  have hj : j + 1 < 60 := lt_of_two_pow (j := j + 1) (M := M) (by
    have := Nat.div_mul_le_self M (2 ^ (j + 1))
    have : 1 ≤ M / 2 ^ (j + 1) := hpos
    calc 2 ^ (j + 1) = 1 * 2 ^ (j + 1) := (Nat.one_mul _).symm
      _ ≤ M / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_le_mul_right _ hpos
      _ ≤ M := Nat.div_mul_le_self M _) hM60
  obtain ⟨t', run', h9', zf', h10', h11', hsi', B'⟩ := tableStep_ok Et (j := j) (x := M / 2 ^ (j + 1))
    (by omega) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) h9 h10 h11 hsi
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have e2 : M / 2 ^ (j + 1) / 2 = M / 2 ^ (j + 1 + 1) := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  have hslot := slot_lt (j + 1)
  have fr' : Frame [wT W] s.mem t'.mem := fr.trans (B'.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wT W, List.mem_singleton_self _, slot_sub W (j + 1)⟩)
  have hv' : ∀ k ≤ j + 1, blockAtMem t'.mem (W + BitVec.ofNat 64 (tblO + 16 * slot k)) = lAt l k := by
    intro k hk
    rcases Nat.lt_or_ge k (j + 1) with hk' | hk'
    · have hks := slot_lt k
      have hne : slot k ≠ slot (j + 1) := fun h => by have := slot_inj (by omega) (by omega) h; omega
      rw [blockAtMem_frame B'.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (by simp only [tblO]; omega) (by simp only [tblO]; omega)
          (by simp only [tblO]; omega)), hv k (by omega)]
    · obtain rfl : k = j + 1 := by omega
      rw [B'.val, hv j (Nat.le_refl _)]; rfl
  have Et' : Env K W SP t' := Et.of_saved (fun r hr => B'.gpr r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) B'.rd B'.wr
  have sv' : ∀ r ∈ calleeSaved, t'.gpr r = s.gpr r := fun r hr => by
    rw [B'.gpr r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), sv r hr]
  by_cases h0 : M / 2 ^ (j + 1) / 2 = 0
  · left
    refine ⟨(eval_ne zf').trans (by simp [h0]), Et', fr', ⟨hM60, fun k hk => ?_⟩, sv',
      by rw [B'.rd, rd], by rw [B'.wr, wr]⟩
    have : k ≤ j + 1 := by
      rw [e2] at h0
      have := lt_of_two_pow hk (k := j + 1 + 1) (by
        rcases Nat.lt_or_ge M (2 ^ (j + 1 + 1)) with h | h
        · exact h
        · have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega : 1 * 2 ^ (j + 1 + 1) ≤ M); omega)
      omega
    exact hv' k this
  · right
    refine ⟨(eval_ne zf').trans (by simp [h0]), M / 2 ^ (j + 1 + 1), by omega, j + 1, rfl, by omega,
      by rw [h9', e2], h10', h11', hsi', hv', fr', Et', sv', by rw [B'.rd, rd], by rw [B'.wr, wr]⟩

end VG.Proof.AesOcb.X86_64
