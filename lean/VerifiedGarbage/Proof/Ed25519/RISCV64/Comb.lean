module

-- separate module: its proofs (about 6 s) build in parallel with `Encode`'s and `VerifyFn`'s, which `ScalarBase` also imports

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Comb
public import VerifiedGarbage.Proof.Ed25519.RISCV64.BaseContract
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldProg
public import VerifiedGarbage.Proof.Ed25519.CombDigits64
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.Ed25519.WindowNibble
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointAccumulate
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointMul
public import VerifiedGarbage.Proof.X25519.RISCV64.R64.Mul
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic

/-!
# Ed25519's base-point multiplication on RISC-V: the comb

What `combMultiply` computes, as ARMv7's comb does (`Proof/Ed25519/Arm/CombLoop.lean`).

*The digits.* Digit `i` of the scalar at `p` is the nibble `n` of byte `i / 2` (its high
nibble for odd `i`), `nibAt`; `combDigit` leaves the mask of its sign (all ones for `n < 8`)
at byte `SGN` of the working space, in `a4` the magnitude `magOf n` of `n - 8`, in
`maskReg 1 … 8` the masks of the magnitudes, all ones exactly for `magOf n`, and in `t0` 1
exactly for the magnitude 0 (`combDigit_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519 VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519 (sel)

/-- Digit `i`'s nibble of the scalar at `p`. -/
def nibAt (m : Mem) (p : Addr) (i : Nat) : Nat :=
  (m (p + BitVec.ofNat 64 (i / 2))).toNat / 16 ^ (i % 2) % 16

theorem nibAt_lt (m : Mem) (p : Addr) (i : Nat) : nibAt m p i < 16 := Nat.mod_lt _ (by decide)

/-- The magnitude of the digit `n - 8`. -/
def magOf (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

theorem magOf_le {n : Nat} (hn : n < 16) : magOf n ≤ 8 := by
  unfold magOf; split <;> omega

/-- All ones for `true`, zero for `false`. -/
def maskB (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xori {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .xor d n imm :: is)) s Q :=
  WP.cons (exec_logicImm h) (k _ (Upd.write _ _ _))

theorem wp_andi' {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n &&& BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .and d n imm :: is)) s Q :=
  WP.cons (exec_logicImm h) (k _ (Upd.write _ _ _))

theorem wp_addi' {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi h) (k _ (Upd.write _ _ _))

theorem wp_srlr {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n >>> ((s.gpr m).toNat % 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.shiftReg .srl .d d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.write _ _ _))

theorem wp_li0 {d : Reg} (k : ∀ s', Upd s s' d 0 → WP isa (.block is) s' Q) :
    WP isa (.block (.li d 0 :: is)) s Q :=
  WP.cons (exec_li (by decide)) (k _ (Upd.write _ _ _))

end

private theorem mask_fact : ∀ a ≤ 8, ∀ k < 8,
    (0 : BitVec 64) - (((BitVec.ofNat 64 a ^^^ BitVec.ofInt 64 ((k + 1 : Nat) : Int)) +
      BitVec.ofInt 64 (-1)) >>> 63) = maskB (decide (a = k + 1)) := by decide

private theorem sign_fact : ∀ n < 16,
    (0 : BitVec 64) - ((BitVec.ofNat 64 n + BitVec.ofInt 64 (-8)) >>> 63) = maskB (decide (n < 8)) ∧
      ((BitVec.ofNat 64 n + BitVec.ofInt 64 (-8)) ^^^ maskB (decide (n < 8))) - maskB (decide (n < 8)) =
        BitVec.ofNat 64 (magOf n) := by decide

private theorem identity_fact : ∀ a ≤ 8,
    (if (0 : BitVec 64) < BitVec.ofNat 64 a then (1 : BitVec 64) else 0) ^^^ BitVec.ofInt 64 1 =
      BitVec.ofNat 64 (if a = 0 then 1 else 0) := by decide

private theorem counter_fact : ∀ i < 64,
    BitVec.ofNat 64 i >>> 1 = BitVec.ofNat 64 (i / 2) ∧
      ((BitVec.ofNat 64 i &&& BitVec.ofInt 64 1) <<< 2).toNat % 64 = 4 * (i % 2) := by decide

theorem nibble_eq (v : Nat) (hv : v < 256) (o : Nat) :
    (BitVec.ofNat 64 v >>> (4 * o) &&& BitVec.ofInt 64 15) = BitVec.ofNat 64 (v / 16 ^ o % 16) := by
  apply BitVec.eq_of_toNat_eq
  have h16 : (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 := rfl
  have hl : v / 16 ^ o % 16 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h16,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl,
    Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega), Nat.pow_mul]

private theorem maskReg_fact : ∀ k < 8,
    maskReg (k + 1) ≠ .a0 ∧ maskReg (k + 1) ≠ .a4 ∧ maskReg (k + 1) ≠ .a3 ∧
      maskReg (k + 1) ∈ [Reg.t1, .t2, .t3, .t4, .t5, .t6, .a6, .a7] := by decide

private theorem maskReg_ne : ∀ k < 8, ∀ k' < 8, k' ≠ k → maskReg (k' + 1) ≠ maskReg (k + 1) := by
  decide

/-- The mask registers. -/
abbrev maskRegs : List Reg := [.t1, .t2, .t3, .t4, .t5, .t6, .a6, .a7]

/-- The masks of the magnitudes, from the magnitude `a` in `a4` and zero in `a0`. -/
structure MaskInv (s₀ : State) (a : Nat) (k : Nat) (s : State) : Prop where
  rest : Rest maskRegs s₀ s
  mem : s.mem = s₀.mem
  masks : ∀ k' < k, s.gpr (maskReg (k' + 1)) = maskB (decide (a = k' + 1))

theorem combMasks_ok {s₀ : State} {a : Nat} (ha : a ≤ 8) (h0 : s₀.gpr .a0 = 0)
    (h4 : s₀.gpr .a4 = BitVec.ofNat 64 a) :
    WP isa (.block ((List.range 8).flatMap fun k => combMask (k + 1))) s₀ (MaskInv s₀ a 8) := by
  refine wp_range_flatMap (M := isa) (MaskInv s₀ a) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨Rest.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have m := maskReg_fact k hk
  have g0 : s.gpr .a0 = 0 := (h.rest.gpr _ (by decide)).trans h0
  have g4 : s.gpr .a4 = BitVec.ofNat 64 a := (h.rest.gpr _ (by decide)).trans h4
  unfold combMask
  refine wp_xori (by unfold imm12; omega) fun s₁ u₁ => wp_addi' (by decide) fun s₂ u₂ =>
    wp_srl (by decide) fun s₃ u₃ => wp_sub fun s₄ u₄ => WP.block_nil ?_
  have hr : ∀ {t t' : State} {v : BitVec 64}, Upd t t' (maskReg (k + 1)) v → Rest maskRegs t t' :=
    fun u => u.rest m.2.2.2
  refine ⟨h.rest.trans ((hr u₁).trans ((hr u₂).trans ((hr u₃).trans (hr u₄)))), ?_, fun k' hk' => ?_⟩
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · have ne := maskReg_ne k hk k' (by omega) (by omega)
      rw [u₄.other _ ne, u₃.other _ ne, u₂.other _ ne, u₁.other _ ne]
      exact h.masks k' hk'
    · rw [u₄.gpr, u₃.other _ m.1.symm, u₂.other _ m.1.symm, u₁.other _ m.1.symm, g0, u₃.gpr,
        u₂.gpr, u₁.gpr, g4]
      exact mask_fact a ha k' hk

/-- The scalar's copy in the working space at `b`. -/
abbrev scalAt (b : Addr) : Addr := b + BitVec.ofNat 64 SCAL

/-- The registers `combDigit` writes. -/
abbrev digitR : List Reg := [.a0, .a1, .a2, .a4, .a5, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .a6, .a7]

theorem combDigit_ok {b : Addr} {s : State} (hc : Ctx b s) {i : Nat} (hi : i < 64)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 i) :
    WP isa (.block combDigit) s fun t =>
      Rest digitR s t ∧
      t.mem = s.mem.writeW (b + BitVec.ofNat 64 SGN) (maskB (decide (nibAt s.mem (scalAt b) i < 8))) ∧
      t.gpr .a0 = 0 ∧ t.gpr .a4 = BitVec.ofNat 64 (magOf (nibAt s.mem (scalAt b) i)) ∧
      (∀ k < 8, t.gpr (maskReg (k + 1)) = maskB (decide (magOf (nibAt s.mem (scalAt b) i) = k + 1))) ∧
      t.gpr .t0 = BitVec.ofNat 64 (if magOf (nibAt s.mem (scalAt b) i) = 0 then 1 else 0) := by
  have cf := counter_fact i hi
  have hS : SCAL = 1152 := rfl
  unfold combDigit
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_srl (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => ?_
  let a := scalAt b + BitVec.ofNat 64 (i / 2)
  have ea : s₂.gpr .a1 + BitVec.ofNat 64 SCAL = a := by
    rw [u₂.gpr, u₁.other _ (by decide), hc.a3, u₁.gpr, h1, cf.1, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (i / 2)),
      ← BitVec.add_assoc]
  have hin : InRegions (s₂.rd ++ s₂.wr) a 1 := by
    rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
    show InRegions _ (b + BitVec.ofNat 64 SCAL + BitVec.ofNat 64 (i / 2)) 1
    rw [Offset.add_add]
    exact hc.inR (by omega)
  refine wp_lbu (a := a) (by decide) ea hin fun s₃ u₃ => ?_
  have v_lt := (s.mem a).isLt
  have m2 : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have e3 : s₃.gpr .a2 = BitVec.ofNat 64 (s.mem a).toNat := by
    rw [u₃.gpr, m2]
    exact BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;> omega)
  refine wp_andi' (by decide) fun s₄ u₄ => wp_sll (by decide) fun s₅ u₅ => wp_srlr fun s₆ u₆ =>
    wp_andi' (by decide) fun s₇ u₇ => ?_
  have e7 : s₇.gpr .a4 = BitVec.ofNat 64 (nibAt s.mem (scalAt b) i) := by
    rw [u₇.gpr, u₆.gpr, u₅.other .a2 (by decide), u₄.other .a2 (by decide), e3, u₅.gpr, u₄.gpr,
      u₃.other .s1 (by decide), u₂.other .s1 (by decide), u₁.other .s1 (by decide), h1, cf.2]
    exact nibble_eq _ v_lt _
  have r7 : Rest [.a1, .a2, .a4, .t0] s s₇ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans
      (u₇.rest (by decide)))))))
  have m7 : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m2]
  have sf := sign_fact _ (nibAt_lt s.mem (scalAt b) i)
  refine wp_li0 fun s₈ u₈ => wp_addi' (by decide) fun s₉ u₉ => wp_srl (by decide) fun s₁₀ u₁₀ =>
    wp_sub fun s₁₁ u₁₁ => ?_
  have g11 : s₁₁.gpr .a5 = maskB (decide (nibAt s.mem (scalAt b) i < 8)) := by
    rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), e7]
    exact sf.1
  have r11 : Rest [.a0, .a1, .a2, .a4, .a5, .t0] s s₁₁ :=
    (r7.mono (by decide)).trans ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans
      ((u₁₀.rest (by decide)).trans (u₁₁.rest (by decide)))))
  have hc11 : Ctx b s₁₁ := hc.of_rest r11 (by decide)
  refine wp_sd (a := b + BitVec.ofNat 64 SGN) (by decide) (by rw [hc11.a3]) (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show SGN = 56 from rfl]; have := hc.al; omega) (hc11.wr _ _ (by decide))
    fun s₁₂ u₁₂ => wp_xor fun s₁₃ u₁₃ => wp_sub fun s₁₄ u₁₄ => ?_
  have g14 : s₁₄.gpr .a4 = BitVec.ofNat 64 (magOf (nibAt s.mem (scalAt b) i)) := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₃.other _ (by decide), u₁₂.gpr, g11, u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.gpr, u₈.other _ (by decide), e7]
    exact sf.2
  have g0 : s₁₄.gpr .a0 = 0 := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
  have m14 : s₁₄.mem = s.mem.writeW (b + BitVec.ofNat 64 SGN) (maskB (decide (nibAt s.mem (scalAt b) i < 8))) := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, g11, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m7]
  have r14 : Rest [.a0, .a1, .a2, .a4, .a5, .t0] s s₁₄ :=
    r11.trans ((u₁₂.rest _).trans ((u₁₃.rest (by decide)).trans (u₁₄.rest (by decide))))
  refine WP.block_nil (WP.mono (combMasks_ok (magOf_le (nibAt_lt _ _ _)) g0 g14) fun t h => ?_)
  refine wp_sltu fun t₁ v₁ => wp_xori (by decide) fun t₂ v₂ => WP.block_nil ?_
  have ga0 : t.gpr .a0 = 0 := (h.rest.gpr _ (by decide)).trans g0
  have ga4 : t.gpr .a4 = BitVec.ofNat 64 (magOf (nibAt s.mem (scalAt b) i)) := (h.rest.gpr _ (by decide)).trans g14
  refine ⟨(r14.mono (by decide)).trans ((h.rest.mono (by decide)).trans ((v₁.rest (by decide)).trans
      (v₂.rest (by decide)))), by rw [v₂.mem, v₁.mem, h.mem, m14],
    by rw [v₂.other _ (by decide), v₁.other _ (by decide), ga0],
    by rw [v₂.other _ (by decide), v₁.other _ (by decide), ga4],
    fun k hk => ?_, ?_⟩
  · have m := maskReg_fact k hk
    rw [v₂.other _ (by revert k; decide), v₁.other _ (by revert k; decide)]
    exact h.masks k hk
  · rw [v₂.gpr, v₁.gpr, ga0, ga4]
    exact identity_fact _ (magOf_le (nibAt_lt _ _ _))

/-! ## The selection -/

/-- The comb's tables at `T` in `s`: aligned, not wrapping around, readable, and their
doublewords. -/
structure TblAt (s : State) (T : Addr) : Prop where
  al : T.toNat % 8 = 0
  fit : T.toNat + 49152 ≤ 2 ^ 64
  rd : InRegions (s.rd ++ s.wr) T 49152
  words : ∀ q < 64 * 96, s.mem.readW (T + BitVec.ofNat 64 (8 * q)) 64 = combWord q

theorem TblAt.of_frame {s t : State} {T : Addr} {L : List Region} (h : TblAt s T)
    (hr : t.rd ++ t.wr = s.rd ++ s.wr) (hf : Frame L s.mem t.mem) (hd : ∀ r ∈ L, (TBL T).Disjoint r) :
    TblAt t T :=
  ⟨h.al, h.fit, hr ▸ h.rd, fun q hq => by
    rw [← h.words q hq]
    exact hf.readW (r := TBL T) (Offset.contains_base T (by omega) (by omega)) hd (by decide)⟩

/-- Doubleword `j` of coordinate `c` of entry `a` of table `i`: the identity's `[1, 1, 0]` for
`a = 0`. -/
def selDw (i a c j : Nat) : Nat := (combCoord (combCached64 i a) c).val / 2 ^ (64 * j) % 2 ^ 64

theorem selDw_lt (i a c j : Nat) : selDw i a c j < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem selDw_succ (i m c j : Nat) : selDw i (m + 1) c j = combDw i m c j := rfl

private theorem selDw_zero_fact : ∀ c < 3, ∀ j < 4,
    (combCoord ⟨1, 1, 0, 2⟩ c).val / 2 ^ (64 * j) % 2 ^ 64 = if c < 2 ∧ j = 0 then 1 else 0 := by
  decide

theorem selDw_zero (i c j : Nat) (hc : c < 3) (hj : j < 4) :
    selDw i 0 c j = if c < 2 ∧ j = 0 then 1 else 0 := by
  have e : combCached64 i 0 = ⟨1, 1, 0, 2⟩ := by
    unfold combCached64 combCached combCached16; split <;> rfl
  rw [selDw, e]
  exact selDw_zero_fact c hc j hj

private theorem cand_fact (a m : Nat) (x w : BitVec 64) :
    x ||| (w &&& maskB (decide (a = m + 1))) = if a = m + 1 then x ||| w else x := by
  by_cases h : a = m + 1
  · rw [ite_eq_left h, maskB, ite_eq_left (decide_eq_true h), BitVec.and_allOnes]
  · rw [ite_eq_right h, maskB, ite_eq_right (by simp [h])]
    show x ||| (w &&& 0#64) = x
    rw [BitVec.and_zero, BitVec.or_zero]

private theorem maskReg_out : ∀ m < 8, maskReg (m + 1) ∉ [Reg.a4, .a5] := by decide

private theorem maskReg_a5 : ∀ m < 8, maskReg (m + 1) ≠ .a5 := by decide

/-- The registers and table the selection reads. -/
structure SelCtx (b T : Addr) (i a : Nat) (s : State) : Prop where
  ctx : Ctx8 b s
  s2 : s.gpr .s2 = T + BitVec.ofNat 64 (768 * i)
  masks : ∀ k < 8, s.gpr (maskReg (k + 1)) = maskB (decide (a = k + 1))
  t0 : s.gpr .t0 = BitVec.ofNat 64 (if a = 0 then 1 else 0)
  tbl : TblAt s T
  apart : (TBL T).Disjoint ⟨b, 8192⟩

theorem SelCtx.of_rest {b T : Addr} {i a : Nat} {s t : State} (h : SelCtx b T i a s)
    (hr : Rest [.a4, .a5] s t) (hf : Frame [⟨b, 8192⟩] s.mem t.mem) : SelCtx b T i a t :=
  ⟨h.ctx.of_rest hr (by decide), (hr.gpr _ (by decide)).trans h.s2,
    fun k hk => (hr.gpr _ (maskReg_out k hk)).trans (h.masks k hk), (hr.gpr _ (by decide)).trans h.t0,
    h.tbl.of_frame (by rw [hr.rd, hr.wr]) hf (by simpa only [List.mem_singleton, forall_eq] using h.apart),
    h.apart⟩

theorem selectCand_ok {b T : Addr} {i a c j m : Nat} {s : State} (h : SelCtx b T i a s)
    (hi : i < 64) (hc : c < 3) (hj : j < 4) (hm : m < 8) :
    WP isa (.block (selectCand (96 * m + 32 * c + 8 * j) m)) s fun t =>
      t.gpr .a4 = s.gpr .a4 ||| (BitVec.ofNat 64 (combDw i m c j) &&& maskB (decide (a = m + 1))) ∧
      Rest [.a4, .a5] s t ∧ t.mem = s.mem := by
  have fit := h.tbl.fit
  have q_lt : 96 * i + 12 * m + 4 * c + j < 64 * 96 := by omega
  have e : 768 * i + (96 * m + 32 * c + 8 * j) = 8 * (96 * i + 12 * m + 4 * c + j) := by omega
  have ha : s.gpr .s2 + BitVec.ofNat 64 (96 * m + 32 * c + 8 * j) =
      T + BitVec.ofNat 64 (8 * (96 * i + 12 * m + 4 * c + j)) := by
    rw [h.s2, BitVec.add_assoc, ← BitVec.ofNat_add, e]
  have hv := h.tbl.words _ q_lt
  have lv : combWord (96 * i + 12 * m + 4 * c + j) = BitVec.ofNat 64 (combDw i m c j) := by
    unfold combWord; congr 2 <;> omega
  unfold selectCand
  refine wp_ld (by omega) ha (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := h.tbl.al; omega)
    (CallLay.inRegions_sub h.tbl.rd (by omega) (by decide)) fun s₁ u₁ =>
    wp_and fun s₂ u₂ => wp_or fun s₃ u₃ => WP.block_nil ?_
  have mm := h.masks m hm
  have hne : maskReg (m + 1) ≠ .a5 := maskReg_a5 m hm
  refine ⟨?_, (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide))),
    by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.gpr, u₁.gpr, hv, lv,
    u₁.other _ hne, mm]

theorem selectDw_ok {b T : Addr} {i a c j : Nat} {s : State} (h : SelCtx b T i a s)
    (hi : i < 64) (ha : a ≤ 8) (hc : c < 3) (hj : j < 4) :
    WP isa (.block (selectDw c j)) s fun t =>
      Rest [.a4, .a5] s t ∧
      t.mem = s.mem.writeW (b + BitVec.ofNat 64 (64 + 32 * (4 + c) + 8 * j))
        (BitVec.ofNat 64 (selDw i a c j)) := by
  unfold selectDw
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The start: the identity's doubleword.
  have start : WP isa (.block (if c < 2 ∧ j = 0 then [.addi .a4 .t0 0] else [.li .a4 0])) s fun t =>
      t.gpr .a4 = BitVec.ofNat 64 (if a = 0 ∧ c < 2 ∧ j = 0 then 1 else 0) ∧ Rest [.a4, .a5] s t ∧
        t.mem = s.mem := by
    split
    · rename_i hcj
      refine wp_mv fun s₁ u₁ => WP.block_nil ⟨?_, u₁.rest (by decide), u₁.mem⟩
      rw [u₁.gpr, h.t0]
      by_cases a0 : a = 0 <;> simp [a0, hcj]
    · rename_i hcj
      refine wp_li0 fun s₁ u₁ => WP.block_nil ⟨?_, u₁.rest (by decide), u₁.mem⟩
      rw [u₁.gpr]
      simp only [hcj, and_false, ↓reduceIte]
      rfl
  refine WP.mono start fun s₀ ⟨g₀, r₀, m₀⟩ => ?_
  -- The candidates.
  have h₀ := h.of_rest r₀ (by rw [m₀]; exact Frame.refl _ _)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n t => SelCtx b T i a t ∧ Rest [.a4, .a5] s₀ t ∧ t.mem = s₀.mem ∧
      t.gpr .a4 = BitVec.ofNat 64 (if 1 ≤ a ∧ a ≤ n then selDw i a c j else
        if a = 0 ∧ c < 2 ∧ j = 0 then 1 else 0))
    (fun n t hn ⟨ht, rt, mt, gt⟩ => ?_) 8 (Nat.le_refl _) s₀
    ⟨h₀, Rest.refl _ _, rfl, by rw [g₀, ite_eq_right (show ¬(1 ≤ a ∧ a ≤ 0) by omega)]⟩) fun s₁ ⟨h₁, r₁, m₁, g₁⟩ => ?_
  · refine WP.mono (selectCand_ok ht hi hc hj hn) fun u ⟨gu, ru, mu⟩ =>
      ⟨ht.of_rest ru (by rw [mu]; exact Frame.refl _ _), rt.trans ru, mu.trans mt, ?_⟩
    rw [gu, gt, cand_fact a n]
    by_cases e : a = n + 1
    · subst e
      rw [ite_eq_left rfl, ite_eq_right (show ¬(1 ≤ n + 1 ∧ n + 1 ≤ n) by omega),
        ite_eq_right (show ¬(n + 1 = 0 ∧ c < 2 ∧ j = 0) by omega),
        ite_eq_left (show 1 ≤ n + 1 ∧ n + 1 ≤ n + 1 from ⟨by omega, Nat.le_refl _⟩), selDw_succ]
      exact BitVec.zero_or
    · rw [ite_eq_right e]
      congr 1
      by_cases h1 : 1 ≤ a ∧ a ≤ n
      · rw [ite_eq_left h1, ite_eq_left (show 1 ≤ a ∧ a ≤ n + 1 from ⟨h1.1, by omega⟩)]
      · rw [ite_eq_right h1, ite_eq_right (show ¬(1 ≤ a ∧ a ≤ n + 1) by omega)]
  -- The store.
  have hc₁ := h₁.ctx
  refine wp_sd (a := b + BitVec.ofNat 64 (64 + 32 * (4 + c) + 8 * j)) (by omega) (by rw [hc₁.a3])
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hc₁.al; omega)
    (hc₁.ctx.wr _ _ (by omega)) fun t ut => WP.block_nil ⟨r₀.trans (r₁.trans (ut.rest _)), ?_⟩
  have sel : (if 1 ≤ a ∧ a ≤ 8 then selDw i a c j else if a = 0 ∧ c < 2 ∧ j = 0 then 1 else 0) =
      selDw i a c j := by
    rcases Nat.eq_zero_or_pos a with a0 | apos
    · subst a0
      rw [ite_eq_right (show ¬(1 ≤ 0 ∧ 0 ≤ 8) by omega), selDw_zero i c j hc hj]
      by_cases hcj : c < 2 ∧ j = 0
      · rw [ite_eq_left ⟨rfl, hcj⟩, ite_eq_left hcj]
      · rw [ite_eq_right (fun h => hcj h.2), ite_eq_right hcj]
    · rw [ite_eq_left ⟨apos, ha⟩]
  rw [ut.mem, m₁, m₀, g₁, sel]

/-- The slots 4–6 the selection writes. -/
abbrev selR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 192, 96⟩

/-- The selection's invariant after `q` doublewords. -/
structure SelInv (b T : Addr) (i a : Nat) (s₀ : State) (q : Nat) (s : State) : Prop where
  sel : SelCtx b T i a s
  rest : Rest [.a4, .a5] s₀ s
  frame : Frame [selR b] s₀.mem s.mem
  dws : ∀ q' < q, X448.RISCV64.R64.dw s.mem b (192 + 8 * q') = selDw i a (q' / 4) (q' % 4)

theorem combSelect_ok {b T : Addr} {i a : Nat} {s : State} (h : SelCtx b T i a s) (hi : i < 64)
    (ha : a ≤ 8) :
    WP isa (.block combSelect) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [selR b] s.mem t.mem ∧
      ∀ q < 12, X448.RISCV64.R64.dw t.mem b (192 + 8 * q) = selDw i a (q / 4) (q % 4) := by
  unfold combSelect
  refine WP.mono (wp_range_flatMap (M := isa) (SelInv b T i a s) (fun q t hq h => ?_) 12
    (Nat.le_refl _) s ⟨h, Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun t h => ⟨h.rest, h.frame, h.dws⟩
  have e : 64 + 32 * (4 + q / 4) + 8 * (q % 4) = 192 + 8 * q := by omega
  refine WP.mono (selectDw_ok h.sel hi ha (by omega) (Nat.mod_lt _ (by decide))) fun u ⟨ru, mu⟩ => ?_
  rw [e] at mu
  have fw : Frame [selR b] t.mem u.mem := by
    rw [mu]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))
  refine ⟨h.sel.of_rest ru (fw.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base b (by decide)⟩),
    h.rest.trans ru, h.frame.trans fw, fun q' hq' => ?_⟩
  rw [mu]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
  · rw [X448.RISCV64.R64.dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    exact h.dws q' hq'
  · rw [X448.RISCV64.R64.dw_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (selDw_lt i a _ _)]

/-! ## The slots -/

theorem val4_digits (v : Nat) :
    R64.val4 (fun j => v / 2 ^ (64 * j) % 2 ^ 64) = v % 2 ^ 256 := by
  simp only [R64.val4, Nat.mul_zero, Nat.mul_one, show 64 * 2 = 128 from rfl, show 64 * 3 = 192 from rfl,
    Nat.pow_zero, Nat.div_one]
  omega

/-- The selected entry's coordinate `c` in slot `4 + c`. -/
theorem sel_env {m : Mem} {b : Addr} {i a : Nat}
    (h : ∀ q < 12, X448.RISCV64.R64.dw m b (192 + 8 * q) = selDw i a (q / 4) (q % 4))
    (sl : Slot) (c : Nat) (hc : c < 3) (hs : sl.val = 4 + c) :
    env m b sl = combCoord (combCached64 i a) c := by
  have hv : V m b (offset sl) = (combCoord (combCached64 i a) c).val := by
    rw [R64.V_eq4]
    have hl : ∀ j < 4, X448.RISCV64.R64.ew m b (offset sl) j =
        (combCoord (combCached64 i a) c).val / 2 ^ (64 * j) % 2 ^ 64 := fun j hj => by
      have e := h (4 * c + j) (by omega)
      rw [show (4 * c + j) / 4 = c by omega, show (4 * c + j) % 4 = j by omega,
        show 192 + 8 * (4 * c + j) = offset sl + 8 * j by simp only [offset, hs]; omega] at e
      exact e
    rw [R64.val4_congr hl, val4_digits,
      Nat.mod_eq_of_lt (Nat.lt_trans (combCoord (combCached64 i a) c).isLt (by decide))]
  simp only [env, FS, hv, VG.Proof.X25519.toFe_self]

/-! ## The addition -/

/-- What `addAffineOps` computes, from the point's coordinates and the cached entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> grind

theorem addAffineOps_formula (e : Env) :
    point (evalOps addAffineOps e) 0 1 2 3 = mixedResult (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) :=
  rfl

/-! ## The step -/

theorem maskB_eq (b : Bool) : maskB b = 0 - BitVec.ofNat 64 b.toNat := by cases b <;> decide

theorem magOf_eq (n : Nat) : magOf n = Proof.Ed25519.mag n := rfl

/-- Nibble `i` of the scalar's bytes is the decoded scalar's. -/
theorem nibAt_eq (m : Mem) (p : Addr) {i : Nat} (hi : i < 64) :
    nibAt m p i = Proof.Ed25519.nib (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32)) i := by
  rw [Proof.Ed25519.nib, Proof.Ed25519.decodeLE_nibble, Proof.Ed25519.nibbleOf, nibAt]
  have hg : (Spec.Ed25519.bytesAt m p 32).getD (i / 2) 0 = m (p + BitVec.ofNat 64 (i / 2)) := by
    simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, show i / 2 < 32 by omega]
  rw [hg]
  have := (m (p + BitVec.ofNat 64 (i / 2))).isLt
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, ite_eq_right (by decide), pow_zero, Nat.div_one]
  · rw [h, ite_eq_left rfl, pow_one]; omega

/-- The sign's mask in the working space. -/
abbrev SGNR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SGN, 8⟩

/-- What a step writes: the sign's mask and the field area. -/
abbrev stepW (b : Addr) : List Region := [SGNR b, FA b]

/-- The registers a step writes. -/
abbrev stepR : List Reg := .s1 :: .s2 :: fclob

/-- What the loop never changes: the tables, apart from the working space. -/
structure CombEnv (s₀ : State) (b T : Addr) : Prop where
  tbl : TblAt s₀ T
  apart : (TBL T).Disjoint ⟨b, 8192⟩

/-- The loop's invariant, after `j` steps. -/
structure CombInv (s₀ : State) (b T : Addr) (S : Nat) (j : Nat) (s : State) : Prop where
  bound : j ≤ 64
  ctx : Ctx8 b s
  ws : WS b s
  s1 : s.gpr .s1 = BitVec.ofNat 64 j
  s2 : s.gpr .s2 = T + BitVec.ofNat 64 (768 * j)
  zero : env s.mem b 21 = 0
  acc : Rep (point (env s.mem b) 0 1 2 3) ((((17 * combGVal : Nat) : ℤ) + digitSum64 S j) • baseAff)
  rest : Rest stepR s₀ s
  frame : Frame (stepW b) s₀.mem s.mem
  scalar : S = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (scalAt b) 32)

theorem stepW_ws {b : Addr} {m m' : Mem} (hf : Frame (stepW b) m m') : Frame [⟨b, 8192⟩] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩

/-- The scalar's copy is apart from what a step writes. -/
theorem scal_apart {b : Addr} {m m' : Mem} (hf : Frame (stepW b) m m') :
    Spec.Ed25519.bytesAt m' (scalAt b) 32 = Spec.Ed25519.bytesAt m (scalAt b) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun n hn => hf _ fun r hr => ?_
  have hn := List.mem_range.mp hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [Offset.add_add]
  rcases hr with rfl | rfl
  · exact fun hc => Offset.disjoint b (d := SCAL + n) (n := 1) (e := SGN) (k := 8) (.inr (by
      simp only [SCAL, SGN]; omega)) (by simp only [SCAL]; omega) (by decide) _ (Region.contains_self _ _) hc
  · exact fun hc => Offset.disjoint b (d := SCAL + n) (n := 1) (e := 64) (k := 960) (.inr (by
      simp only [SCAL]; omega)) (by simp only [SCAL]; omega) (by decide) _ (Region.contains_self _ _) hc

private theorem next_fact : ∀ j < 64,
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 64) != 0) = decide (j + 1 ≠ 64) := by decide

/-- A slot apart from the region a frame writes keeps its element. -/
theorem env_frameR {m m' : Mem} {b : Addr} {R : Region} (hf : Frame [R] m m') (sl : Slot)
    (hd : ∀ k < 8, (⟨b + BitVec.ofNat 64 (offset sl + 4 * k), 4⟩ : Region).Disjoint R) :
    env m' b sl = env m b sl := by
  simp only [env, FS, V]
  exact congrArg _ (VG.Proof.X25519.val32_congr (limb_frame hf fun r hr k hk => by rw [List.mem_singleton.mp hr]; exact hd k hk))

/-- The region `[d, d + n)` of the working space is apart from slot `sl` unless they meet. -/
theorem slot_apart {b : Addr} (sl : Slot) {d n : Nat} (h : d + n ≤ offset sl ∨ offset sl + 32 ≤ d)
    (hn : d + n ≤ 8192) :
    ∀ k < 8, (⟨b + BitVec.ofNat 64 (offset sl + 4 * k), 4⟩ : Region).Disjoint
      ⟨b + BitVec.ofNat 64 d, n⟩ := fun k hk =>
  Offset.disjoint _ (by omega) (by simp only [offset] at h ⊢; have := sl.isLt; omega) (by omega)

private theorem slot_cases : ∀ sl : Slot, sl.val = 4 ∨ sl.val = 5 ∨ sl.val = 6 ∨
    sl.val < 4 ∨ 7 ≤ sl.val := by decide

theorem combStep_ok {s₀ s : State} {b T : Addr} {S j : Nat} (E : CombEnv s₀ b T)
    (h : CombInv s₀ b T S j s) (hj : j < 64) :
    WP isa combStep s fun t => isa.eval (.nonzero .a4) t = some (decide (j + 1 ≠ 64)) ∧
      CombInv s₀ b T S (j + 1) t := by
  have nf := next_fact j hj
  have n_lt := nibAt_lt s.mem (scalAt b) j
  have hrr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rest.rd, h.rest.wr]
  have apartL : ∀ L : List Region, (∀ r ∈ L, Region.Sub r ⟨b, 8192⟩) → ∀ r ∈ L, (TBL T).Disjoint r :=
    fun L hL r hr => E.apart.sub_right (hL r hr)
  have hT : TblAt s T := E.tbl.of_frame hrr (stepW_ws h.frame) (by simpa only [List.mem_singleton, forall_eq] using E.apart)
  have hnib : nibAt s.mem (scalAt b) j = Proof.Ed25519.nib S j := by rw [nibAt_eq _ _ hj, ← h.scalar]
  -- The digit and the selection.
  rw [combStep]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (combDigit_ok h.ctx.ctx hj h.s1) fun u ⟨ru, mu, _, _, gm, g0⟩ => ?_
  have fu : Frame [SGNR b] s.mem u.mem := by
    rw [mu]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have cu := h.ctx.of_rest ru (by decide)
  have hTu : TblAt u T := hT.of_frame (by rw [ru.rd, ru.wr])
    (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (show SGN + 8 ≤ 8192 by decide)⟩)
    (by simpa only [List.mem_singleton, forall_eq] using E.apart)
  have hsel : SelCtx b T j (magOf (nibAt s.mem (scalAt b) j)) u :=
    ⟨cu, (ru.gpr _ (by decide)).trans h.s2, gm, g0, hTu, E.apart⟩
  refine WP.mono (combSelect_ok hsel hj (magOf_le n_lt)) fun v ⟨rv, fv, lv⟩ => ?_
  -- The slots after the selection.
  have envv : ∀ sl : Slot, (sl.val < 4 ∨ 7 ≤ sl.val) → env v.mem b sl = env s.mem b sl := fun sl hs => by
    rw [env_frameR fv sl (slot_apart sl (by simp only [offset]; have := sl.isLt; omega) (by decide)),
      env_frameR fu sl (slot_apart sl (by simp only [offset, SGN]; omega) (by decide))]
  have ent : ∀ c < 3, ∀ sl : Slot, sl.val = 4 + c →
      env v.mem b sl = combCoord (combCached64 j (magOf (nibAt s.mem (scalAt b) j))) c :=
    fun c hc sl hs => sel_env lv sl c hc hs
  have cv := cu.of_rest rv (by decide)
  have wsv : WS b v := (h.ws.of_rest ru).of_rest rv
  have sgn : v.mem.readW (b + BitVec.ofNat 64 SGN) 64 = maskB (decide (nibAt s.mem (scalAt b) j < 8)) := by
    rw [fv.readW (r := SGNR b) (Region.contains_self _ _)
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (by decide), mu, Mem.readW_writeW_self64]
  -- The negation.
  refine WP.seq ?_
  rw [combNeg, WP.seq_iff]
  refine WP.mono (fieldCode_ok [.sub 7 21 6] cv.ctx wsv) fun w ⟨kw, ew⟩ => ?_
  have cw := cv.of_keep kw
  have wsw : WS b w := wsv.of_rest kw.rest
  rw [List.singleton_append]
  refine X448.RISCV64.R64.ld_ok cw.ctx (d := SGN) (by decide) (by decide) fun x₀ ux => ?_
  have sgnw : w.mem.readW (b + BitVec.ofNat 64 SGN) 64 = maskB (decide (nibAt s.mem (scalAt b) j < 8)) := by
    rw [kw.frame.readW (r := SGNR b) (Region.contains_self _ _)
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (by decide), sgn]
  let sw := (decide (nibAt s.mem (scalAt b) j < 8)).toNat
  have hsw : sw ≤ 1 := Bool.toNat_le _
  have cx₀ := cw.of_rest (ux.rest (ws := [.t0]) (by decide)) (by decide)
  have t0x : x₀.gpr .t0 = 0 - BitVec.ofNat 64 sw := by rw [ux.gpr, sgnw, maskB_eq]
  refine WP.append (cswapSlot_ok cx₀ hsw t0x 4 5 (by decide)) fun x₁ ⟨r₁, f₁, a₁, c₁, k₁⟩ => ?_
  refine WP.mono (cswapSlot_ok (cx₀.of_rest r₁ (by decide)) hsw (by rw [r₁.gpr _ (by decide), t0x]) 6 7 (by decide))
    fun x ⟨r₂, f₂, a₂, c₂, k₂⟩ => ?_
  have cx := (cx₀.of_rest r₁ (by decide)).of_rest r₂ (by decide)
  have wsx : WS b x := ((wsw.of_rest (ux.rest (ws := [.t0]) (by decide))).of_rest r₁).of_rest r₂
  -- The addition.
  refine WP.seq (WP.mono (fieldCode_ok addAffineOps cx.ctx wsx) fun y ⟨ky, ey⟩ => ?_)
  have cy := cx.of_keep ky
  -- The counter.
  refine wp_addi (imm := 1) (by decide) fun z₁ uz₁ => wp_addi (imm := 768) (by decide) fun z₂ uz₂ =>
    wp_subi (imm := 64) (by decide) fun z uz => WP.block_nil ?_
  have s1y : y.gpr .s1 = BitVec.ofNat 64 j := by
    rw [ky.rest.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), ux.other _ (by decide),
      kw.rest.gpr _ (by decide), rv.gpr _ (by decide), ru.gpr _ (by decide), h.s1]
  have s2y : y.gpr .s2 = T + BitVec.ofNat 64 (768 * j) := by
    rw [ky.rest.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), ux.other _ (by decide),
      kw.rest.gpr _ (by decide), rv.gpr _ (by decide), ru.gpr _ (by decide), h.s2]
  have s1z : z.gpr .s1 = BitVec.ofNat 64 (j + 1) := by
    rw [uz.other _ (by decide), uz₂.other _ (by decide), uz₁.gpr, s1y, nf.1]
  have restz : Rest stepR s z :=
    (ru.mono (by decide)).trans ((rv.mono (by decide)).trans ((kw.rest.mono (by decide)).trans
      ((ux.rest (ws := stepR) (by decide)).trans ((r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans
      ((ky.rest.mono (by decide)).trans ((uz₁.rest (ws := stepR) (by decide)).trans
      ((uz₂.rest (ws := stepR) (by decide)).trans (uz.rest (ws := stepR) (by decide))))))))))
  have memz : z.mem = y.mem := by rw [uz.mem, uz₂.mem, uz₁.mem]
  have fz : Frame (stepW b) s.mem z.mem := by
    rw [memz]
    refine (fu.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans ?_
    refine ((fv.sub fun r hr => ⟨FA b, by simp, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩).trans ?_)
    refine (kw.frame.mono (by simp)).trans ?_
    have f₁' := f₁
    rw [ux.mem] at f₁'
    exact (f₁'.mono (by simp)).trans ((f₂.mono (by simp)).trans (ky.frame.mono (by simp)))
  -- The entry's coordinates.
  obtain ⟨q, hq, hqz, hrq⟩ := Proof.Ed25519.combEntry64_ok j (Proof.Ed25519.nib S j) hj (Proof.Ed25519.nib_lt S j)
  rw [hnib] at ent sgn
  have e4 := ent 0 (by decide) 4 rfl
  have e5 := ent 1 (by decide) 5 rfl
  have e6 := ent 2 (by decide) 6 rfl
  have e21 : env v.mem b 21 = 0 := (envv 21 (.inr (by decide))).trans h.zero
  have w4 : env w.mem b 4 = env v.mem b 4 := by rw [ew]; rfl
  have w5 : env w.mem b 5 = env v.mem b 5 := by rw [ew]; rfl
  have w6 : env w.mem b 6 = env v.mem b 6 := by rw [ew]; rfl
  have w7 : env w.mem b 7 = env v.mem b 21 - env v.mem b 6 := by rw [ew]; rfl
  have wlow : ∀ i : Slot, i ≠ 7 → env w.mem b i = env v.mem b i := fun i hi => by
    rw [ew]; exact Function.update_of_ne hi _ _
  have ex₀ : env x₀.mem b = env w.mem b := by rw [ux.mem]
  have x4 : env x.mem b 4 = sel sw (env w.mem b 4) (env w.mem b 5) := by
    rw [k₂ 4 (by decide) (by decide), a₁, ex₀]
  have x5 : env x.mem b 5 = sel sw (env w.mem b 5) (env w.mem b 4) := by
    rw [k₂ 5 (by decide) (by decide), c₁, ex₀]
  have x6 : env x.mem b 6 = sel sw (env w.mem b 6) (env w.mem b 7) := by
    rw [a₂, k₁ 6 (by decide) (by decide), k₁ 7 (by decide) (by decide), ex₀]
  have xlow : ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env x.mem b i = env s.mem b i := fun i hi => by
    rw [k₂ i (fun e => by subst e; simp at hi) (fun e => by subst e; simp at hi),
      k₁ i (fun e => by subst e; simp at hi) (fun e => by subst e; simp at hi), ex₀,
      wlow i (fun e => by subst e; simp at hi)]
    exact envv i (by omega)
  have cq : env x.mem b 4 = q.Y - q.X ∧ env x.mem b 5 = q.Y + q.X ∧
      env x.mem b 6 = q.T * 2 * Spec.Ed25519.d := by
    have c0 : ∀ p, combCoord p 0 = p.X := fun _ => rfl
    have c1 : ∀ p, combCoord p 1 = p.Y := fun _ => rfl
    have c2 : ∀ p, combCoord p 2 = p.Z := fun _ => rfl
    rw [c0, magOf_eq] at e4
    rw [c1, magOf_eq] at e5
    rw [c2, magOf_eq] at e6
    rw [x4, x5, x6, w4, w5, w6, w7, e4, e5, e6, e21]
    have hc := congrArg (fun p => (p.X, p.Y, p.Z)) hq
    simp only [Proof.Ed25519.cache, Prod.mk.injEq] at hc
    by_cases hlt : Proof.Ed25519.nib S j < 8
    · have : sw = 1 := by simp only [sw, hnib, hlt, decide_true, Bool.toNat_true]
      simp only [hlt, ↓reduceIte, Proof.Ed25519.negCached] at hc
      simp only [sel, this, ↓reduceIte]
      exact hc
    · have : sw = 0 := by simp only [sw, hnib, hlt, decide_false, Bool.toNat_false]
      simp only [hlt, ↓reduceIte] at hc
      simp only [sel, this, show (0 : Nat) ≠ 1 from by decide, ↓reduceIte]
      exact hc
  refine ⟨?_, ⟨by omega, cy.of_rest ((uz₁.rest (ws := [.s1, .s2, .a4]) (by decide)).trans
      ((uz₂.rest (by decide)).trans (uz.rest (by decide)))) (by decide),
    ((wsx.of_rest ky.rest).of_rest ((uz₁.rest (ws := [.s1, .s2, .a4]) (by decide)).trans
      ((uz₂.rest (by decide)).trans (uz.rest (by decide))))), s1z, ?_, ?_, ?_, h.rest.trans restz,
    h.frame.trans fz, ?_⟩⟩
  · rw [eval_nonzero, uz.gpr, uz₂.other _ (by decide), uz₁.gpr, s1y, nf.1, nf.2]
  · rw [uz.other _ (by decide), uz₂.gpr, uz₁.other _ (by decide), s2y, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 768 * j + 768 = 768 * (j + 1) by omega]
  · -- Slot 21 is still zero.
    rw [memz, ey]
    show env x.mem b 21 = 0
    rw [xlow 21 (.inr (by decide))]
    exact h.zero
  · -- The accumulator.
    rw [memz, ey, addAffineOps_formula, cq.1, cq.2.1, cq.2.2, xlow 0 (.inl (by decide)),
      xlow 1 (.inl (by decide)), xlow 2 (.inl (by decide)), xlow 3 (.inl (by decide))]
    have e := mixedResult_eq (point (env s.mem b) 0 1 2 3) q hqz
    simp only [point] at e
    rw [e, Proof.Ed25519.digitSum64, ← add_assoc, add_smul]
    exact pointAdd_rep h.acc (by simpa only [Proof.Ed25519.sdig] using hrq)
  · rw [h.scalar, scal_apart fz]

/-- The loop, from step `j₀ < 64` to the end. -/
theorem combSteps_ok {s₀ s : State} {b T : Addr} {S j₀ : Nat} (E : CombEnv s₀ b T)
    (h : CombInv s₀ b T S j₀ s) (hj₀ : j₀ < 64) :
    WP isa (.loop combStep (.nonzero .a4)) s fun t => CombInv s₀ b T S 64 t := by
  apply WP.loop (fun n t => CombInv s₀ b T S (64 - n) t ∧ 0 < n ∧ n ≤ 64) (n := 64 - j₀)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (combStep_ok E ht (by omega)) fun u ⟨ue, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by rw [ue]; rfl, hu⟩
    · refine Or.inr ⟨by rw [ue]; simp only [show 64 - (k + 1) + 1 ≠ 64 by omega, ne_eq,
        not_false_eq_true, decide_true], k, by omega, ?_, by omega, by omega⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨by rw [show 64 - (64 - j₀) = j₀ by omega]; exact h, by omega, by omega⟩

/-! ## The scalar's copy -/

/-- The scalar's copy in the working space. -/
abbrev scalR (b : Addr) : Region := ⟨scalAt b, 32⟩

private theorem byte_rt (x : BitVec 8) : (x.setWidth 64).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem combCopy_ok {s : State} {b P : Addr} (hc : Ctx8 b s) (hp : s.gpr .s0 = P)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 k) 1)
    (hsep : (⟨P, 32⟩ : Region).Disjoint (scalR b)) :
    WP isa (.block combCopy) s fun t => Rest [.a4] s t ∧ Frame [scalR b] s.mem t.mem ∧
      ∀ k < 32, t.mem (b + BitVec.ofNat 64 (SCAL + k)) = s.mem (P + BitVec.ofNat 64 k) := by
  have src : ∀ k < 32, ∀ m : Mem, Frame [scalR b] s.mem m →
      m (P + BitVec.ofNat 64 k) = s.mem (P + BitVec.ofNat 64 k) := fun k hk m hf =>
    hf _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc' => hsep _ (Offset.contains_base P (by omega) (by omega)) hc'
  refine wp_range_flatMap (M := isa) (fun (k : Nat) (t : State) => Rest [.a4] s t ∧ Frame [scalR b] s.mem t.mem ∧
      ∀ i < k, t.mem (b + BitVec.ofNat 64 (SCAL + i)) = s.mem (P + BitVec.ofNat 64 i))
    (fun (k : Nat) (t : State) hk ⟨rt, ft, ct⟩ => ?_) 32 le_rfl s
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine wp_lbu (a := P + BitVec.ofNat 64 k) (by omega)
    (by rw [rt.gpr _ (by decide), hp])
    (by rw [rt.rd, rt.wr]; exact hr k hk) fun t₁ u₁ => ?_
  refine wp_sb (a := b + BitVec.ofNat 64 (SCAL + k)) (by simp only [SCAL]; omega)
    (by rw [u₁.other _ (by decide), rt.gpr _ (by decide), hc.a3])
    (by rw [u₁.wr, rt.wr]; exact hc.ctx.wr _ _ (by simp only [SCAL]; omega))
    fun t₂ u₂ => WP.block_nil ?_
  have m2 : t₂.mem = t.mem.writeW (b + BitVec.ofNat 64 (SCAL + k)) (t.mem (P + BitVec.ofNat 64 k)) := by
    rw [u₂.mem, u₁.gpr, u₁.mem, byte_rt]
  refine ⟨rt.trans ((u₁.rest (by decide)).trans (u₂.rest _)), ?_, fun i hi => ?_⟩
  · rw [m2]
    exact ft.writeW (List.mem_singleton_self _) _
      (Offset.contains b (d := SCAL + k) (n := 1) (e := SCAL) (k := 32) (by omega) (by omega)
        (by simp only [SCAL]; omega))
  · rw [m2, VG.WriteBytes.writeW8_apply]
    by_cases hik : i = k
    · subst hik
      rw [ite_eq_left rfl]
      exact src i hk _ ft
    · have hne : b + BitVec.ofNat 64 (SCAL + i) ≠ b + BitVec.ofNat 64 (SCAL + k) :=
        fun he => Offset.disjoint b (d := SCAL + i) (n := 1) (e := SCAL + k) (k := 1)
          (by omega) (by simp only [SCAL]; omega) (by simp only [SCAL]; omega) _
          (Region.contains_self _ _) (he ▸ Region.contains_self _ _)
      rw [ite_eq_right hne]
      exact ct i (by omega)

/-! ## The start -/

private def combStartCheck (p : Spec.Ed25519.Point) : Bool :=
  combStart.X * p.Z == p.X && combStart.Y * p.Z == p.Y && p.Z != 0

private theorem combStart_check :
    combStartCheck (Spec.Ed25519.pointMul (17 * Proof.Ed25519.combGVal) Spec.Ed25519.basePoint) = true := by
  decide +kernel

theorem combStart_ok : Rep combStart ((17 * Proof.Ed25519.combGVal) • baseAff) := by
  have hp := pointMul_rep (17 * Proof.Ed25519.combGVal) basePoint_rep
  have hc := combStart_check
  simp only [combStartCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact Proof.Ed25519.combPt_rep (q := combStartAff) hp hx hy

/-! ## The multiplication -/

theorem wp_lla {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {name : String}
    (k : ∀ s', Upd s s' d (s.syms name) → WP isa (.block is) s' Q) :
    WP isa (.block (.lla d name :: is)) s Q :=
  WP.cons exec_lla (k _ (Upd.write _ _ _))

/-- What `combMultiply` writes: the scalar's copy, the sign's mask and the field area. -/
abbrev combW (b : Addr) : List Region := scalR b :: stepW b

/-- The comb after the scalar's copy: the accumulator's start, the counter, the tables' address
and the 64 steps, for the scalar's copy at `scalAt b`. -/
theorem combRun_ok {u : State} {b T : Addr} (cuu : Ctx8 b u) (wsu : WS b u) (hT : TblAt u T)
    (hsym : u.syms combSym = T) (apart : (TBL T).Disjoint ⟨b, 8192⟩) :
    WP isa (.seq combInit (.loop combStep (.nonzero .a4))) u fun t => Rest stepR u t ∧
      Frame (stepW b) u.mem t.mem ∧
      Rep (point (env t.mem b) 0 1 2 3)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (scalAt b) 32) • baseAff) := by
  rw [combInit, WP.seq_iff, WP.seq_iff]
  refine WP.mono_syms (fieldCode_ok _ cuu.ctx wsu) fun v ⟨kv, ev⟩ syv => ?_
  let w₁ := v.write .s1 (BitVec.ofInt 64 0)
  let w := w₁.write .s2 (w₁.syms combSym)
  refine WP.cons (s' := w₁) (exec_li (by decide)) (WP.cons (s' := w) exec_lla (WP.block_nil ?_))
  have u₁ : Upd v w₁ .s1 (BitVec.ofInt 64 0) := Upd.write _ _ _
  have u₂ : Upd w₁ w .s2 (w₁.syms combSym) := Upd.write _ _ _
  have rw₂ : Rest [.s1, .s2] v w := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  have mw : w.mem = v.mem := by rw [u₂.mem, u₁.mem]
  have cw : Ctx8 b w := (cuu.of_keep kv).of_rest rw₂ (by decide)
  have wsw : WS b w := (wsu.of_rest kv.rest).of_rest rw₂
  have fsw : Frame (stepW b) u.mem w.mem := by
    rw [mw]
    exact kv.frame.mono (by simp)
  have hTw : TblAt w T := hT.of_frame (by rw [rw₂.rd, rw₂.wr, kv.rest.rd, kv.rest.wr]) fsw
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact apart.sub_right (Offset.sub_base _ (by decide))
      · exact apart.sub_right (Offset.sub_base _ (by decide))
  have E : CombEnv w b T := ⟨hTw, apart⟩
  have scal : Spec.Ed25519.bytesAt w.mem (scalAt b) 32 = Spec.Ed25519.bytesAt u.mem (scalAt b) 32 :=
    scal_apart fsw
  have syw : w₁.syms = u.syms := syv
  have I : CombInv w b T (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (scalAt b) 32)) 0 w := by
    refine ⟨by decide, cw, wsw, by rw [u₂.other _ (by decide), u₁.gpr]; rfl,
      by rw [u₂.gpr, syw, hsym, Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero],
      ?_, ?_, Rest.refl _ _, Frame.refl _ _, by rw [scal]⟩
    · rw [mw, ev]
      simp [constPointOps, evalOps, evalOp]
    · rw [mw, ev, evalOps, List.foldl_append, ← evalOps, ← evalOps, (env_constPoint _ _).1]
      simpa only [Proof.Ed25519.digitSum64, add_zero, natCast_zsmul] using combStart_ok
  have hS := Proof.Ed25519.decodeLE_lt32 u.mem (scalAt b)
  refine WP.mono (combSteps_ok E I (by decide)) fun t ht => ⟨?_, ?_, ?_⟩
  · exact (kv.rest.mono (by decide)).trans ((rw₂.mono (by decide)).trans ht.rest)
  · exact (fsw.trans (ht.frame.mono (by simp)))
  · have := ht.acc
    rw [Proof.Ed25519.comb64_total (by simpa using hS), natCast_zsmul] at this
    exact this

theorem combMultiply_ok {s : State} {b P T : Addr} (hc : Ctx8 b s) (hws : WS b s) (hp : s.gpr .s0 = P)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 k) 1)
    (hsep : (⟨P, 32⟩ : Region).Disjoint ⟨b, 8192⟩)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨b, 8192⟩) :
    WP isa combMultiply s fun t => Rest stepR s t ∧ Frame (combW b) s.mem t.mem ∧
      Rep (point (env t.mem b) 0 1 2 3)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem P 32) • baseAff) := by
  have sub : (scalR b).Sub ⟨b, 8192⟩ := Offset.sub_base _ (by decide)
  rw [combMultiply, combPrepare]
  refine WP.seq (WP.seq (WP.mono_syms (combCopy_ok hc hp hr (hsep.sub_right sub)) fun u ⟨ru, fu, cu⟩ syu => ?_))
  have hTu : TblAt u T := hT.of_frame (by rw [ru.rd, ru.wr]) fu fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right sub
  have scal : Spec.Ed25519.bytesAt u.mem (scalAt b) 32 = Spec.Ed25519.bytesAt s.mem P 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun n hn => ?_
    rw [scalAt, Offset.add_add]
    exact cu n (List.mem_range.mp hn)
  refine WP.seq_iff.mp (WP.mono (combRun_ok (hc.of_rest ru (by decide)) (hws.of_rest ru) hTu
    (by rw [syu, hsym]) apart) fun t ⟨rt, ft, pt⟩ => ⟨?_, ?_, ?_⟩)
  · exact (ru.mono (by decide)).trans rt
  · exact (fu.mono (by simp)).trans (ft.mono (by simp))
  · rw [← scal]; exact pt

end VG.Proof.Ed25519.RISCV64
