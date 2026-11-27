module

-- separate module: the selection from a table of 16 arrays, at any place in the layout, for every windowed exponentiation
public import VerifiedGarbage.Impl.Bignum.RISCV64.WinSelect
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Selecting an entry of a 16-entry table on RISC-V

`winSelect_ok`: `WinSelect.winSelect o t` makes array `o` equal to array
`t + d`, for the digit `d < 16` in `t6`, and writes only array `o`: `masks`
(`masks_ok`), the eight entries of a half under the masks of `d mod 8`
(`half_ok`, by induction on the entries), and the choice of the half by `d`'s
top bit (`merge_ok`).
-/

@[expose] public section

namespace VG.Proof.WinSelect.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.WinSelect
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot slot_sep Arrays)
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-- All ones if `b`, else 0. -/
abbrev mask (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-! ## The masks -/

theorem bit_mask : ∀ d j : Fin 8,
    ((1#64 <<< d.val) <<< (63 - j.val)).sshiftRight 63 = mask (decide (j.val = d.val)) := by decide

theorem top_mask : ∀ d : Fin 16, (BitVec.ofNat 64 d.val <<< 60).sshiftRight 63 = mask (decide (8 ≤ d.val)) := by
  decide

theorem low_digit : ∀ d : Fin 16, (BitVec.ofNat 64 d.val &&& 7#64).toNat % 64 = d.val % 8 := by decide

/-- The registers of the masks. -/
def maskRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .t2]

theorem maskReg_mem : ∀ j < 8, maskReg j ∈ maskRegs := by decide

theorem maskReg_inj : ∀ n < 8, ∀ j < n, maskReg j ≠ maskReg n := by decide

/-- The masks of `e < 8` below `n`. -/
def Masks (s : State) (n e : Nat) : Prop := ∀ j < n, s.gpr (maskReg j) = mask (decide (j = e))

theorem bitMask_ok {s : State} {e n : Nat} (h4 : s.gpr .t4 = 1#64 <<< e) (he : e < 8) (hn : n < 8) :
    WP isa (.block (bitMask (maskReg n) n)) s fun t =>
      t.gpr (maskReg n) = mask (decide (n = e)) ∧ t.mem = s.mem ∧ Keep [maskReg n] s t := by
  unfold bitMask
  rw [show ([.shift .sll .d (maskReg n) .t4 (63 - n), .shift .sra .d (maskReg n) (maskReg n) 63] : List Instr) =
    [.shift .sll .d (maskReg n) .t4 (63 - n)] ++ [.shift .sra .d (maskReg n) (maskReg n) 63] from rfl]
  apply WP.of_runBlock
  refine ⟨(s.write (maskReg n) (s.gpr .t4 <<< (63 - n))).write (maskReg n)
    ((s.gpr .t4 <<< (63 - n)).sshiftRight 63), ?_, ?_, rfl, ?_⟩
  · simp only [List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec_shift_d (show 63 - n < 64 by omega_arith), exec_shift_d (show 63 < 64 by decide), gpr_write_self]
  · rw [gpr_write_self, h4]
    exact bit_mask ⟨e, he⟩ ⟨n, hn⟩
  · exact Keep.trans' (Keep.write _ _ _) (Keep.write _ _ _)

theorem bitMasks_succ (n : Nat) : (List.range (n + 1)).flatMap (fun j => bitMask (maskReg j) j) =
    (List.range n).flatMap (fun j => bitMask (maskReg j) j) ++ bitMask (maskReg n) n := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem bitMasks_ok {s : State} {e : Nat} (h4 : s.gpr .t4 = 1#64 <<< e) (he : e < 8) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun j => bitMask (maskReg j) j)) s fun t =>
      Masks t n e ∧ t.mem = s.mem ∧ Keep maskRegs s t
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keep.refl _ _⟩
  | n + 1, hn => by
    rw [bitMasks_succ, WP.block_append_iff]
    refine WP.mono (bitMasks_ok h4 he n (by omega_arith)) fun t ⟨hM, hm, hk⟩ => ?_
    refine WP.mono (bitMask_ok (n := n) ((hk.gpr (by decide)).trans h4) he (by omega_arith))
      fun u ⟨hu, um, uk⟩ => ⟨fun j hj => ?_, um.trans hm, (hk.trans uk).mono fun r hr => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [uk.gpr (by rw [List.mem_singleton]; exact maskReg_inj n (by omega_arith) j hj)]
        exact hM j hj
      · exact hu
    · rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · rw [List.mem_singleton.mp hr]; exact maskReg_mem n (by omega_arith)

/-- `masks`: the masks of `d mod 8`, and of `d ≥ 8` in `s4`. -/
theorem masks_ok {s : State} {d : Nat} (h6 : s.gpr .t6 = BitVec.ofNat 64 d) (hd : d < 16) :
    WP isa (.block masks) s fun t => (Masks t 8 (d % 8) ∧ t.gpr .s4 = mask (decide (8 ≤ d)) ∧ t.mem = s.mem) ∧
      Keep (([.s4, .t4, .t5] : List Reg) ++ maskRegs) s t := by
  unfold masks
  rw [WP.block_append_iff]
  have hpre : WP isa (.block (([.shift .sll .d .s4 .t6 60, .shift .sra .d .s4 .s4 63] : List Instr) ++ hot)) s fun t =>
      (t.gpr .s4 = mask (decide (8 ≤ d)) ∧ t.gpr .t4 = 1#64 <<< (d % 8) ∧ t.mem = s.mem) ∧
        Keep [.s4, .t4, .t5] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold hot
    brun [h6, exec_li, Pub.pub_li1, exec_sllReg, top_mask ⟨d, hd⟩, low_digit ⟨d, hd⟩]
  refine WP.mono hpre fun t ⟨⟨t4, hot, tm⟩, tk⟩ => ?_
  refine WP.mono (bitMasks_ok hot (Nat.mod_lt _ (by decide)) 8 (Nat.le_refl _)) fun u ⟨hM, um, uk⟩ =>
    ⟨⟨hM, (uk.gpr (by decide)).trans t4, um.trans tm⟩, tk.trans uk⟩

/-! ## Half the entries -/

/-- The two pairs of words the halves are selected into. -/
def Pair (x y : Reg) : Prop := x = .s0 ∧ y = .s1 ∨ x = .s2 ∧ y = .s3

theorem maskReg_ne : ∀ j < 8, maskReg j ≠ .t6 ∧ maskReg j ≠ .t3 ∧ maskReg j ≠ .s0 ∧ maskReg j ≠ .s1 ∧
    maskReg j ≠ .s2 ∧ maskReg j ≠ .s3 ∧ maskReg j ≠ .s5 := by decide

theorem and_mask (x : BitVec 64) (b : Bool) : x &&& mask b = if b then x else 0#64 := by
  cases b
  · exact BitVec.and_zero
  · exact BitVec.and_allOnes

/-- The word or'ed in under its mask. -/
theorem acc_step {e n : Nat} {f : Nat → BitVec 64} {z : BitVec 64} (hz : z = if e < n then f e else 0#64) :
    z ||| (f n &&& mask (decide (n = e))) = if e < n + 1 then f e else 0#64 := by
  subst hz
  rw [and_mask]
  by_cases he : n = e
  · subst he; simp
  · have hiff : (e < n + 1) = (e < n) := propext (by omega_arith)
    simp [he, hiff]

/-- The first entry of a half. -/
theorem first_ok {s : State} {B : Addr} {Z p w e : Nat} {x y : Reg} (hxy : Pair x y) (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B p) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (hm : s.gpr (maskReg 0) = mask (decide (0 = e))) (h8 : p % 8 = 0) (hp : p + 16 ≤ Z) :
    WP isa (.block (first x y (maskReg 0))) s fun t =>
      (t.gpr x = (Mont.word s.mem B p &&& mask (decide (0 = e))) ∧
        t.gpr y = (Mont.word s.mem B (p + 8) &&& mask (decide (0 = e))) ∧
        t.gpr .t3 = off B (p + 8 * (w + 2)) ∧ t.mem = s.mem) ∧ Keep [x, y, .t6, .t3] s t := by
  have l0 : InRegions (s.rd ++ s.wr) (off B p) 8 := hs.ld (by omega_arith)
  have l8 : InRegions (s.rd ++ s.wr) (off B (p + 8)) 8 := hs.ld (by omega_arith)
  have g0 : (off B p).toNat % 8 = 0 := hs.al8 (by omega_arith) h8
  have g8 : (off B (p + 8)).toNat % 8 = 0 := hs.al8 (by omega_arith) (by omega_arith)
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold first
    brun [show maskReg 0 = .a0 from rfl, h3, h5, show s.gpr .a0 = mask (decide (0 = e)) from hm, l0, l8, g0, g8, Mont.word]

/-- Another entry of a half. -/
theorem cell_ok {s : State} {B : Addr} {Z p w e n : Nat} {x y : Reg} (hxy : Pair x y) (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B p) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (hn : n < 8)
    (hm : s.gpr (maskReg n) = mask (decide (n = e))) (h8 : p % 8 = 0) (hp : p + 16 ≤ Z) :
    WP isa (.block (cell x y (maskReg n))) s fun t =>
      (t.gpr x = s.gpr x ||| (Mont.word s.mem B p &&& mask (decide (n = e))) ∧
        t.gpr y = s.gpr y ||| (Mont.word s.mem B (p + 8) &&& mask (decide (n = e))) ∧
        t.gpr .t3 = off B (p + 8 * (w + 2)) ∧ t.mem = s.mem) ∧ Keep [x, y, .t6, .t3] s t := by
  have l0 : InRegions (s.rd ++ s.wr) (off B p) 8 := hs.ld (by omega_arith)
  have l8 : InRegions (s.rd ++ s.wr) (off B (p + 8)) 8 := hs.ld (by omega_arith)
  have g0 : (off B p).toNat % 8 = 0 := hs.al8 (by omega_arith) h8
  have g8 : (off B (p + 8)).toNat % 8 = 0 := hs.al8 (by omega_arith) (by omega_arith)
  obtain ⟨m6, m3, m0, m1, m2, ms3, m5⟩ := maskReg_ne n hn
  generalize maskReg n = m at hm m6 m3 m0 m1 m2 ms3 m5 ⊢
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold cell
    brun [m6, m3, m0, m1, m2, ms3, m5, h3, h5, hm, l0, l8, g0, g8, Mont.word]

theorem cells_succ (x y : Reg) (n : Nat) : cells x y (n + 1) = cells x y n ++ cell x y (maskReg (n + 1)) := by
  simp only [cells, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem slot_add (w t j : Nat) : slot w t + j * (8 * (w + 2)) = slot w (t + j) := by
  unfold slot; rw [Nat.add_mul]; omega_arith

theorem slot_succ (w j : Nat) : slot w j + 8 * (w + 2) = slot w (j + 1) := by
  have := slot_add w j 1; rwa [Nat.one_mul] at this

theorem slot_le (w : Nat) {i j : Nat} (h : i ≤ j) : slot w i ≤ slot w j := by
  unfold slot; have := Nat.mul_le_mul_right (8 * (w + 2)) h; omega_arith

theorem slot_al8 (w j : Nat) : slot w j % 8 = 0 := by
  unfold slot Impl.Bignum.hdrBytes
  rw [show j * (8 * (w + 2)) = 8 * (j * (w + 2)) by ac_rfl]
  omega_arith

/-- Entries up to `n + 1` of the eight arrays from `t`, the columns at byte
offset `c`: the words of array `t + e` once it is among them. -/
theorem cells_ok {s : State} {B : Addr} {Z w t c e : Nat} {x y : Reg} (hxy : Pair x y) (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B (slot w t + c)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (hm : Masks s 8 e) (h8 : c % 8 = 0) (hc : c + 16 ≤ 8 * (w + 2)) (hZ : slot w (t + 8) ≤ Z) :
    ∀ n < 8, WP isa (.block (first x y (maskReg 0) ++ cells x y n)) s fun u =>
      (u.gpr x = (if e < n + 1 then Mont.word s.mem B (slot w (t + e) + c) else 0#64) ∧
        u.gpr y = (if e < n + 1 then Mont.word s.mem B (slot w (t + e) + c + 8) else 0#64) ∧
        u.gpr .t3 = off B (slot w (t + (n + 1)) + c) ∧ u.mem = s.mem) ∧ Keep [x, y, .t6, .t3] s u
  | 0, _ => by
    have hf := slot_succ w t
    have hl := slot_le w (show t + 1 ≤ t + 8 by omega_arith)
    simp only [cells, List.range_zero, List.flatMap_nil, List.append_nil]
    refine WP.mono (first_ok hxy hs h3 h5 (hm 0 (by decide)) (by have := slot_al8 w t; omega_arith)
      (by omega_arith)) fun u ⟨⟨ux, uy, u3, um⟩, uk⟩ => ⟨⟨?_, ?_, ?_, um⟩, uk⟩
    · rw [ux, and_mask]
      by_cases he : e = 0
      · subst he; simp
      · simp [he, Ne.symm he]
    · rw [uy, and_mask]
      by_cases he : e = 0
      · subst he; simp
      · simp [he, Ne.symm he]
    · rw [u3, ← hf]; exact congrArg (off B) (by omega_arith)
  | n + 1, hn => by
    have hf := slot_succ w (t + (n + 1))
    have hl := slot_le w (show t + (n + 1) + 1 ≤ t + 8 by omega_arith)
    rw [cells_succ, ← List.append_assoc, WP.block_append_iff]
    refine WP.mono (cells_ok hxy hs h3 h5 hm h8 hc hZ n (by omega_arith)) fun u ⟨⟨ux, uy, u3, um⟩, uk⟩ => ?_
    have k5 : Reg.s5 ∉ [x, y, .t6, .t3] := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    have km : maskReg (n + 1) ∉ [x, y, .t6, .t3] := by
      obtain ⟨m6, m3, m0, m1, m2, ms3, -⟩ := maskReg_ne (n + 1) hn
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [List.mem_cons, List.not_mem_nil, m6, m3, m0, m1, m2, ms3, or_self, not_false_eq_true]
    refine WP.mono (cell_ok hxy (hs.congr uk.2.2) u3 ((uk.gpr k5).trans h5) hn
      ((uk.gpr km).trans (hm (n + 1) hn)) (by have := slot_al8 w (t + (n + 1)); omega_arith) (by omega_arith))
      fun v ⟨⟨vx, vy, v3, vm⟩, vk⟩ => ⟨⟨?_, ?_, ?_, vm.trans um⟩, Keep.trans' uk vk⟩
    · rw [vx, um]
      exact acc_step (f := fun j => Mont.word s.mem B (slot w (t + j) + c)) ux
    · rw [vy, um]
      exact acc_step (f := fun j => Mont.word s.mem B (slot w (t + j) + c + 8)) uy
    · rw [v3, ← Nat.add_assoc t (n + 1) 1, ← hf]; exact congrArg (off B) (by omega_arith)

/-- A half: the two words of array `t + e`. -/
theorem half_ok {s : State} {B : Addr} {Z w t c e : Nat} {x y : Reg} (hxy : Pair x y) (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B (slot w t + c)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (hm : Masks s 8 e) (he : e < 8) (h8 : c % 8 = 0) (hc : c + 16 ≤ 8 * (w + 2)) (hZ : slot w (t + 8) ≤ Z) :
    WP isa (.block (half x y)) s fun u =>
      (u.gpr x = Mont.word s.mem B (slot w (t + e) + c) ∧ u.gpr y = Mont.word s.mem B (slot w (t + e) + c + 8) ∧
        u.gpr .t3 = off B (slot w (t + 8) + c) ∧ u.mem = s.mem) ∧ Keep [x, y, .t6, .t3] s u := by
  refine WP.mono (cells_ok hxy hs h3 h5 hm h8 hc hZ 7 (by decide)) fun u ⟨⟨ux, uy, u3, um⟩, uk⟩ =>
    ⟨⟨?_, ?_, u3, um⟩, uk⟩
  · rw [ux, ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]
  · rw [uy, ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]

/-! ## The two halves -/

theorem merge_arith (a b : BitVec 64) (q : Bool) : a ^^^ ((b ^^^ a) &&& mask q) = if q then b else a := by
  rw [and_mask]
  cases q
  · exact BitVec.xor_zero
  · show a ^^^ (b ^^^ a) = b
    rw [BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem shl4 (a : Nat) : BitVec.ofNat 64 a <<< 4 = BitVec.ofNat 64 (16 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- `merge` and `next`: the half `q` chosen and stored, the pointers two
columns on, and the count. -/
theorem merge_ok {s : State} {B : Addr} {Z w t o c : Nat} {q : Bool} (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B (slot w (t + 16) + c)) (h4 : s.gpr .t4 = off B (slot w o + c))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (hq : s.gpr .s4 = mask q)
    (h8 : c % 8 = 0) (hc : c + 16 ≤ 8 * (w + 2)) (hZ : slot w (o + 1) ≤ Z) :
    WP isa (.block (merge ++ (next ++ ([.addi .t5 .t5 (-1)] : List Instr)))) s fun u =>
      (u.mem = (s.mem.writeW (off B (slot w o + c)) (if q then s.gpr .s2 else s.gpr .s0)).writeW
          (off B (slot w o + c + 8)) (if q then s.gpr .s3 else s.gpr .s1) ∧
        u.gpr .t3 = off B (slot w t + c + 16) ∧ u.gpr .t4 = off B (slot w o + c + 16) ∧
        u.gpr .t5 = s.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep [.s0, .s1, .s2, .s3, .t3, .t4, .t5, .t6] s u := by
  have hf := slot_succ w o
  have ha := slot_al8 w o
  have ht := slot_add w t 16
  have hsub : off B (slot w (t + 16) + c) - BitVec.ofNat 64 (16 * (8 * (w + 2))) = off B (slot w t + c) := by
    rw [off_sub B (by omega_arith)]; exact congrArg (off B) (by omega_arith)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold merge next
  brun [h3, h4, h5, hq, shl4, hsub, hs.st (show slot w o + c + 8 ≤ Z by omega_arith),
    hs.st (show slot w o + c + 8 + 8 ≤ Z by omega_arith), hs.al8 (show slot w o + c + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show slot w o + c + 8 + 8 ≤ Z by omega_arith) (by omega_arith), merge_arith]

/-! ## The selection -/

/-- The registers the selection writes. -/
def selectRegs : List Reg := [.s4, .t4, .t5] ++ maskRegs ++ [.t3, .s0, .s1, .s2, .s3, .t6]

theorem wordsVal_congr {m m' : Mem} {B : Addr} {a b : Nat} :
    ∀ n, (∀ k < n, Mont.word m B (a + 8 * k) = Mont.word m' B (b + 8 * k)) → wordsVal m B a n = wordsVal m' B b n
  | 0, _ => rfl
  | n + 1, h => by
    rw [wordsVal_succ_top, wordsVal_succ_top, wordsVal_congr n fun k hk => h k (by omega_arith),
      h n (by omega_arith)]

/-- The pointers and the count. -/
theorem bases_ok {s : State} {B : Addr} {w o t : Nat} (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : w < 2 ^ 31) :
    WP isa (.block (bases o t)) s fun u =>
      (u.gpr .t3 = off B (slot w t) ∧ u.gpr .t4 = off B (slot w o) ∧
        u.gpr .t5 = BitVec.ofNat 64 ((w + 1) / 2) ∧ u.mem = s.mem) ∧ Keep [.t3, .t4, .t5] s u := by
  unfold bases
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 t) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h7)
    ((k1.gpr (by decide)).trans h5) o) fun t₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have hcnt : BitVec.ofNat 64 (w + 1) >>> 1 = BitVec.ofNat 64 ((w + 1) / 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  have hc : WP isa (.block [.addi .t5 .t0 1, .shift .srl .d .t5 .t5 1]) t₂ fun u =>
      (u.gpr .t5 = BitVec.ofNat 64 ((w + 1) / 2) ∧ u.mem = t₂.mem) ∧ Keep [.t5] t₂ u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(k2.gpr (r := .t0) (by decide)).trans ((k1.gpr (by decide)).trans h0), ← BitVec.ofNat_add, hcnt]
  refine WP.mono hc fun u ⟨⟨u5, um⟩, uk⟩ => ⟨⟨?_, ?_, u5, by rw [um, m2, m1]⟩, ((k1.trans k2).trans uk).mono (by decide)⟩
  · rw [uk.gpr (by decide), k2.gpr (by decide), a3]
  · rw [uk.gpr (by decide), a4]

/-- `winSelect o t`: array `o` := array `t + d`, for `d < 16` in `t6`. -/
theorem winSelect_ok {s : State} {B : Addr} {Z w o t d : Nat} (hs : Scr s B Z)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw1 : 1 ≤ w) (hw : w < 2 ^ 31) (h6 : s.gpr .t6 = BitVec.ofNat 64 d)
    (hd : d < 16) (hot : o < t) (hZ : slot w (t + 16) ≤ Z) :
    WP isa (winSelect o t) s fun u =>
      (wordsVal u.mem B (slot w o) w = wordsVal s.mem B (slot w (t + d)) w ∧ Arrays B w [o] s.mem u.mem) ∧
        Keep selectRegs s u := by
  have hnw := hs.nowrap
  have hZo := slot_le w (show o + 1 ≤ t + 16 by omega_arith)
  have hZt := slot_le w (show t + 8 ≤ t + 16 by omega_arith)
  have hod := slot_le w (show o + 1 ≤ t + d by omega_arith)
  have hfo := slot_succ w o
  have hfd := slot_succ w (t + d)
  have hZd := slot_le w (show t + d + 1 ≤ t + 16 by omega_arith)
  unfold winSelect countLoop
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (masks_ok h6 hd) fun s₁ ⟨⟨M1, q1, m1⟩, k1⟩ => ?_
  refine WP.mono (bases_ok (o := o) (t := t) ((k1.gpr (by decide)).trans h7) ((k1.gpr (by decide)).trans h5)
    ((k1.gpr (by decide)).trans h0) hw) fun s₂ ⟨⟨a3, a4, a5, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  let I : Nat → State → Prop := fun k u => Masks u 8 (d % 8) ∧ u.gpr .s4 = mask (decide (8 ≤ d)) ∧
    u.gpr .t3 = off B (slot w t + 16 * k) ∧ u.gpr .t4 = off B (slot w o + 16 * k) ∧
    (∀ i < 2 * k, Mont.word u.mem B (slot w o + 8 * i) = Mont.word s.mem B (slot w (t + d) + 8 * i)) ∧
    Outside B (slot w o) (16 * k) s.mem u.mem ∧ Keep selectRegs s u
  have init : I 0 s₂ := ⟨fun j hj => by
      rw [k2.gpr (by have := maskReg_ne j hj; revert j; decide)]; exact M1 j hj,
    by rw [k2.gpr (by decide), q1], by rw [a3]; rfl, by rw [a4]; rfl, fun i hi => absurd hi (by omega_arith),
    by rw [m2, m1]; exact Outside.refl _ _ _ _, k12.mono (by decide)⟩
  refine WP.mono (wp_countdown (cnt := .t5) (N := (w + 1) / 2) (by omega_arith) (by omega_arith) I
    (fun k hk u ⟨uM, uq, u3, u4, uw, uo, uk⟩ _ => ?_) init a5) fun u ⟨_, _, _, _, uw, uo, uk⟩ =>
      ⟨⟨wordsVal_congr w fun i hi => uw i (by omega_arith),
        Arrays.of_outside (by simp) uo (Nat.le_refl _) (by omega_arith)⟩, uk⟩
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have hs' := hs.congr uk.2.2
  have e5 := (uk.gpr (r := .s5) (by decide)).trans h5
  have hm8 : d % 8 < 8 := Nat.mod_lt _ (by decide)
  refine WP.mono (half_ok (.inl ⟨rfl, rfl⟩) hs' u3 e5 uM hm8 (by omega_arith) (by omega_arith) (by omega_arith))
    fun v ⟨⟨v0, v1, v3, vm⟩, vk⟩ => ?_
  rw [WP.block_append_iff]
  have vM : Masks v 8 (d % 8) := fun j hj => by
    rw [vk.gpr (by revert j; decide)]; exact uM j hj
  refine WP.mono (half_ok (.inr ⟨rfl, rfl⟩) (hs'.congr vk.2.2) (t := t + 8) v3 ((vk.gpr (by decide)).trans e5) vM hm8
    (by omega_arith) (by omega_arith) (by rw [Nat.add_assoc]; exact hZ))
    fun x ⟨⟨x2, x3, xt, xm⟩, xk⟩ => ?_
  rw [vm] at x2 x3 xm
  have kx := vk.trans xk
  refine WP.mono (merge_ok (o := o) (t := t) (q := decide (8 ≤ d)) (hs'.congr kx.2.2)
    (by rw [xt, Nat.add_assoc t 8 8]) ((kx.gpr (by decide)).trans u4) ((kx.gpr (by decide)).trans e5)
    ((kx.gpr (by decide)).trans uq) (by omega_arith) (by omega_arith) (by omega_arith))
    fun y ⟨⟨ym, y3, y4, y5⟩, yk⟩ => ?_
  have kk := kx.trans yk
  -- the words chosen are the digit's entry's
  have pick : ∀ a b : BitVec 64, ∀ c, a = Mont.word u.mem B (slot w (t + d % 8) + c) →
      b = Mont.word u.mem B (slot w (t + 8 + d % 8) + c) →
      (if decide (8 ≤ d) then b else a) = Mont.word u.mem B (slot w (t + d) + c) := by
    rintro a b c rfl rfl
    by_cases h : 8 ≤ d
    · simp only [h, decide_true, ↓reduceIte, show t + 8 + d % 8 = t + d by omega_arith]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, show t + d % 8 = t + d by omega_arith]
  have p0 := pick (x.gpr .s0) (x.gpr .s2) (16 * k) ((xk.gpr (by decide)).trans v0) x2
  have p1 := pick (x.gpr .s1) (x.gpr .s3) (16 * k + 8) ((xk.gpr (by decide)).trans v1) x3
  rw [p0, p1, xm] at ym
  have src : ∀ c, c + 8 ≤ 8 * (w + 2) → Mont.word u.mem B (slot w (t + d) + c) = Mont.word s.mem B (slot w (t + d) + c) :=
    fun c hc => uo.word (.inr (by omega_arith)) (by omega_arith)
  rw [src _ (by omega_arith), src _ (by omega_arith)] at ym
  have o1 := writeW_outside u.mem B (d := slot w o + 16 * k)
    (Mont.word s.mem B (slot w (t + d) + 16 * k)) (by omega_arith)
  have o2 := writeW_outside (u.mem.writeW (off B (slot w o + 16 * k)) (Mont.word s.mem B (slot w (t + d) + 16 * k))) B
    (d := slot w o + 16 * k + 8) (Mont.word s.mem B (slot w (t + d) + (16 * k + 8))) (by omega_arith)
  refine ⟨⟨fun j hj => ?_, ?_, y3, y4, fun i hi => ?_, ?_, (uk.trans kk).mono (by decide)⟩, ?_⟩
  · rw [kk.gpr (by revert j; decide)]; exact uM j hj
  · rw [kk.gpr (by decide), uq]
  · rw [ym]
    rcases (show i < 2 * k ∨ i = 2 * k ∨ i = 2 * k + 1 by omega_arith) with hi | rfl | rfl
    · rw [o2.word (.inl (by omega_arith)) (by omega_arith), o1.word (.inl (by omega_arith)) (by omega_arith)]
      exact uw i hi
    · rw [o2.word (.inl (by omega_arith)) (by omega_arith), show 8 * (2 * k) = 16 * k by omega_arith,
        word_writeW_self]
    · rw [show slot w o + 8 * (2 * k + 1) = slot w o + 16 * k + 8 by omega_arith, word_writeW_self,
        show 8 * (2 * k + 1) = 16 * k + 8 by omega_arith]
  · rw [ym]
    exact ((uo.mono (Nat.le_refl _) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))).trans
      (o2.mono (by omega_arith) (by omega_arith))
  · rw [y5, kx.gpr (by decide)]

end VG.Proof.WinSelect.RISCV64
