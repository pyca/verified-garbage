module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Nat.Bitwise.Basic

/-!
# HMAC over any streaming hash function on RISC-V: shared lemmas

* `Lay`: the layout of the frames of `init` and `finalize`, from the sizes of
  the hash function.
* `entry_ok`: `entryCmp` leaves in `t1` a value that is zero exactly when the
  key is at most a block.
* `wipe_ok`: the doubleword stores zeroing the start of `init`'s frame.
* The save and restore of `ra` and `s7`–`s11` are `Spill`'s
  (`saveAt_eq`, `restoreAt_eq`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)

/-! ## The layout -/

/-- The sizes the proofs use. -/
structure Lay (H : Hash) : Prop where
  N : 0 < H.N ∧ H.N ≤ 64
  B : H.B = 64 ∨ H.B = 128
  D : 0 < H.D ∧ H.D ≤ 64
  F : H.F ≤ 1024
  iso : H.S + H.D ≤ H.iso ∧ H.iso % 8 = 0
  ibytes : H.iso + 48 ≤ H.ibytes ∧ H.ibytes < 2048 ∧ H.ibytes % 16 = 0
  fso : H.D ≤ H.fso ∧ H.fso % 8 = 0
  fbytes : H.fso + 48 ≤ H.fbytes ∧ H.fbytes < 2048 ∧ H.fbytes % 16 = 0

namespace HashOK

variable {H : Hash} (hH : HashOK H)

include hH in
theorem lay : Lay H := by
  have hB := hH.hB64
  have hN := hH.hN
  have hD0 := hH.hD0
  have hD := hH.hD64
  have hF := hH.hF
  have hS : H.S = H.N + H.B := rfl
  refine ⟨hN, hB, ⟨hD0, hD⟩, hF, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Hash.iso, Hash.ibytes, Hash.fso, Hash.fbytes, hS] <;> omega

end HashOK

theorem toNat_sub {sp : Addr} {n : Nat} (h : n ≤ sp.toNat) (hn : n < 2 ^ 64) :
    (sp - BitVec.ofNat 64 n).toNat = sp.toNat - n := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact h),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-! ## The entry comparison -/

/-- `(x >>> (b + 1)) + ((x &&& (2 B - 1)) + B - 1) >>> (b + 1)`, with
`B = 2 ^ b`, is zero exactly when `x` is at most `B`. -/
theorem cmp_eq {b : Nat} (hb : b = 6 ∨ b = 7) (x : BitVec 64) :
    ((x >>> (b + 1)) + ((x &&& BitVec.ofNat 64 (2 ^ (b + 1) - 1)) + BitVec.ofNat 64 (2 ^ b - 1)) >>> (b + 1)
      == 0) = decide (x.toNat ≤ 2 ^ b) := by
  have hx := x.isLt
  have ha : (x &&& BitVec.ofNat 64 (2 ^ (b + 1) - 1)).toNat = x.toNat % 2 ^ (b + 1) := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases hb with rfl | rfl <;> decide),
      Nat.and_two_pow_sub_one_eq_mod]
  have hb' : ((x &&& BitVec.ofNat 64 (2 ^ (b + 1) - 1)) + BitVec.ofNat 64 (2 ^ b - 1)).toNat =
      x.toNat % 2 ^ (b + 1) + (2 ^ b - 1) := by
    rw [BitVec.toNat_add, ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 ^ b - 1)
      (by rcases hb with rfl | rfl <;> decide)]
    rcases hb with rfl | rfl <;> omega
  have hv : ((x >>> (b + 1)) + ((x &&& BitVec.ofNat 64 (2 ^ (b + 1) - 1)) + BitVec.ofNat 64 (2 ^ b - 1)) >>>
      (b + 1)).toNat = x.toNat / 2 ^ (b + 1) + (x.toNat % 2 ^ (b + 1) + (2 ^ b - 1)) / 2 ^ (b + 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, hb', Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]
    rcases hb with rfl | rfl <;> omega
  by_cases h : x.toNat ≤ 2 ^ b
  · rw [decide_eq_true h]
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [hv]
    simp
    rcases hb with rfl | rfl <;> omega
  · rw [decide_eq_false h]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [hv] at this
    simp at this
    rcases hb with rfl | rfl <;> omega

theorem ofInt_pow_sub {b : Nat} (hb : b = 6 ∨ b = 7) :
    BitVec.ofInt 64 ((2 : Int) ^ (b + 1) - 1) = BitVec.ofNat 64 (2 ^ (b + 1) - 1) ∧
      BitVec.ofInt 64 ((2 : Int) ^ b - 1) = BitVec.ofNat 64 (2 ^ b - 1) ∧
      imm12 ((2 : Int) ^ (b + 1) - 1) ∧ imm12 ((2 : Int) ^ b - 1) ∧ b + 1 < 64 := by
  rcases hb with rfl | rfl <;> decide

/-- `entryCmp`: `t1` is zero exactly when `key_len` (`a3`) is at most a
block; it writes only `t1` and `t2`. -/
theorem entry_ok {H : Hash} (hb : H.b = 6 ∨ H.b = 7) {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ u, (∀ r, r ≠ .t1 → r ≠ .t2 → u.gpr r = s.gpr r) → u.mem = s.mem → u.rd = s.rd →
      u.wr = s.wr → u.sp = s.sp → (u.gpr .t1 == 0) = decide ((s.gpr .a3).toNat ≤ H.B) →
      WP isa (.block rest) u Q) :
    WP isa (.block (H.entryCmp ++ rest)) s Q := by
  obtain ⟨e₁, e₂, i₁, i₂, h64⟩ := ofInt_pow_sub hb
  unfold Hash.entryCmp
  simp only [List.cons_append, List.nil_append]
  refine Steps.wp_srl h64 fun s₁ u₁ => Steps.wp_andi i₁ fun s₂ u₂ => ?_
  refine Steps.WP.cons (exec_addi i₂) ?_
  refine Steps.wp_srl h64 fun s₄ u₄ => Steps.wp_add fun s₅ u₅ => ?_
  have u₃ := Steps.Upd.write s₂ .t2 (s₂.gpr .t2 + BitVec.ofInt 64 ((2 : Int) ^ H.b - 1))
  refine k s₅ (fun r h1 h2 => ?_) ?_ ?_ ?_ ?_ ?_
  · rw [u₅.other r h1, u₄.other r h2, u₃.other r h2, u₂.other r h2, u₁.other r h1]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₅.gpr, u₄.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₂.gpr, u₁.gpr, u₁.other _ (by decide), e₁, e₂]
    exact cmp_eq hb _

/-! ## Zeroing the start of a frame -/

/-- The stores of `t1` at `8 k(s8)`, `k < n`. -/
def stores (n : Nat) : List Instr := (List.range n).map fun k => .store .d .t1 .s8 (8 * k)

/-- `stores n`: memory changes only in the `8 n` bytes at `s8`. -/
theorem stores_ok (n : Nat) {fr : Addr} (hal : fr.toNat % 8 = 0) (hn : 8 * n ≤ 2048)
    {rest : List Instr} {s : State} {Q : State → Prop} (h8 : s.gpr .s8 = fr)
    (hin : ∀ k < n, InRegions s.wr (fr + BitVec.ofNat 64 (8 * k)) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨fr, 8 * n⟩] s.mem s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (stores n ++ rest)) s Q := by
  induction n generalizing rest with
  | zero => exact k s rfl rfl rfl rfl (Frame.refl _ _)
  | succ n ih =>
    rw [stores, List.range_succ, List.map_append, List.append_assoc]
    refine ih (by omega) (fun j hj => hin j (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ f₁ => ?_
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    refine Steps.wp_sd (a := fr + BitVec.ofNat 64 (8 * n)) (by omega) (by rw [g₁, h8])
      (Spill.al8 hal (by omega)) (by rw [wr₁]; exact hin n (by omega)) fun s₂ m₂ => ?_
    refine k s₂ (by rw [m₂.gpr, g₁]) (by rw [m₂.rd, rd₁]) (by rw [m₂.wr, wr₁]) (by rw [m₂.sp, sp₁]) ?_
    rw [m₂.mem]
    refine Frame.writeW ((f₁.sub fun r hr => ?_)) (List.mem_singleton_self _) _
      (Offset.contains_base fr (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩

theorem wipe_eq (H : Hash) : H.wipe = .li .t1 0 :: stores (H.iso / 8) := rfl

/-! ## Saving and restoring -/

/-- Where `restoreAt` loads each register from, in its order. -/
def restList (so : Nat) : List (Reg × Nat) :=
  [(.ra, so), (.s7, so + 8), (.s9, so + 24), (.s10, so + 32), (.s11, so + 40), (.s8, so + 16)]

theorem restList_fst (so : Nat) : (restList so).map Prod.fst = [.ra, .s7, .s9, .s10, .s11, .s8] := rfl

theorem saveAt_eq (so : Nat) : Hash.saveAt so = .addSp .t0 0 :: Spill.saveCode .t0 (Hash.savedAt so) := rfl

theorem restoreAt_eq (so : Nat) : Hash.restoreAt so = Spill.restoreCode .s8 (restList so) := rfl

theorem restorable (so : Nat) : Spill.Restorable .s8 (restList so) := by
  refine ⟨?_, ?_⟩ <;> simp [restList]

theorem restList_mem {so : Nat} {p : Reg × Nat} : p ∈ restList so ↔ p ∈ Hash.savedAt so := by
  simp only [restList, Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false]
  constructor <;> rintro (h | h | h | h | h | h) <;> simp [h]

theorem savedAt_off {so : Nat} (hso : so % 8 = 0 ∧ so + 48 ≤ 2048) :
    ∀ p ∈ Hash.savedAt so, p.2 % 8 = 0 ∧ p.2 < 2048 := by
  intro p hp
  simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem savedAt_fits {so : Nat} (hso : so % 8 = 0 ∧ so + 48 ≤ 2048) : Spill.Fits (Hash.savedAt so) := by
  refine ⟨savedAt_off hso, ?_⟩
  simp only [Hash.savedAt, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
  omega

theorem savedAt_in {so : Nat} : ∀ p ∈ Hash.savedAt so, so ≤ p.2 ∧ p.2 + 8 ≤ so + 48 := by
  intro p hp
  simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- The callee-saved registers that only the functions we call write (they
restore them). -/
def nvRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6]

/-- The callee-saved registers are the caller's again once `ra` and
`s7`–`s11` are restored and `nvRegs` kept. -/
theorem preserved_of {so : Nat} {g : Reg → BitVec 64} {s' : State}
    (hsv : ∀ p ∈ Hash.savedAt so, s'.gpr p.1 = g p.1) (hu : ∀ r ∈ nvRegs, s'.gpr r = g r) :
    ∀ r ∈ preserved, s'.gpr r = g r := by
  intro r hr
  have key : ∀ r ∈ preserved, r ∈ nvRegs ∨ r ∈ [Reg.s7, .s8, .s9, .s10, .s11] := by decide
  rcases key r hr with h | h
  · exact hu r h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact hsv (.s7, so + 8) (by simp [Hash.savedAt])
    · exact hsv (.s8, so + 16) (by simp [Hash.savedAt])
    · exact hsv (.s9, so + 24) (by simp [Hash.savedAt])
    · exact hsv (.s10, so + 32) (by simp [Hash.savedAt])
    · exact hsv (.s11, so + 40) (by simp [Hash.savedAt])

end VG.Proof.Hmac.Stream.RISCV64
