module

public import VerifiedGarbage.Proof.Camellia.Arm.Core
public import VerifiedGarbage.Proof.Camellia.Layout32
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Aes.Arm.Sbox
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Reduce
public import VerifiedGarbage.Impl.Camellia.Arm.Layers
public import VerifiedGarbage.Proof.Framework.Arm.Straight
public import VerifiedGarbage.Impl.Camellia.Arm.Ecb

/-! ### `Camellia.Arm.Prologue`, which the modules that import this one used -/

section

/-! ### `Camellia.Arm.Copy`, which this module and modules that import it used -/

section

/-!
# Copying blocks on ARMv7, and small steps

As SM4's (`Proof/Sm4/Arm/Copy.lean`, whose code is the same): the loop
`copyBlocks` copies `c ≥ 1` blocks of 16 bytes from `r0` to `r12` (areas
that do not overlap), a word at a time through `t0`, counting down `r3`,
and changes nothing else in memory (`copyBlocks_wp`); `groupCount_wp` is
`r3 := min(r2, 8)`. And the single instructions the data loop runs.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Impl.Camellia.Arm
open VG.Arm.Straight (add_ofNat_ofNat wordAddr)
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR lsrOp ldS stS)
open VG.Proof.Camellia (off_sub_toNat off_sub_not)

/-- Slot `k` of the scratch buffer at `b`, as a 64-bit offset. -/
theorem slot_addr {b : BitVec 32} {k : Nat} (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    wordAddr b k = State.addr b + BitVec.ofNat 64 (4 * k) := VG.Arm.addr_add (by omega_arith)

/-- Slot `k` is in the scratch buffer. -/
theorem slot_inR {rs : List Region} {b : BitVec 32} {n k : Nat} (hr : (⟨State.addr b, 4 * n⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) : InRegions rs (wordAddr b k) 4 :=
  ⟨_, hr, by
    rw [slot_addr (by omega_arith)]
    have := addr_toNat b
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩


/-- `add d, n, #v` (`v` encodable). -/
theorem addImm_ok (s : State) (d n : Reg) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.dp .add d n (.imm v)] s = some s' ∧ s'.gpr d = s.gpr n + v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.gpr n + v), by
    rw [runBlock_cons, show exec (.dp .add d n (.imm v)) s = some (s.setReg d (s.gpr n + v)) by
      simp [exec, Op2.eval, hv], runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩


theorem ofNat32_sub_beq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega


/-- `subs d, n, #1`. -/
theorem subs1_ok (s : State) (d : Reg) :
    ∃ s', runBlock isa [.subs d d (.imm 1)] s = some s' ∧ s'.gpr d = s.gpr d - 1 ∧ s'.z = (s.gpr d - 1 == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1), ?_, RegUpd.gpr_setReg_self _ _ _, by rw [RegUpd.z_setReg]; rfl,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d d (.imm 1)) s = some ((subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1)) by
    simp [exec, Op2.eval]; decide, runStep_some, runBlock_nil]


theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega


/-- `mov d, #v` (`v` encodable). -/
theorem movImm_ok (s : State) (d : Reg) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.mov d (.imm v)] s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d v, by
    rw [runBlock_cons, show exec (.mov d (.imm v)) s = some (s.setReg d v) by simp [exec, Op2.eval, hv],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩


theorem writeW_readW32_apply (m m' : Mem) (a c x : Addr) :
    m.writeW a (m'.readW c 32) x =
      if (x - a).toNat < 4 then m' (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, Mem.readW, BitVec.setWidth_eq]
  split
  · rename_i h
    exact Mem.extractLsb'_read m' c (n := 4) h
  · rfl


theorem lsr3_beq {v : Nat} (hv : v < 2 ^ 32) :
    (BitVec.ofNat 32 v >>> 3 - 0 == 0) = decide (v < 8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.gpr n), by
    rw [runBlock_cons, show exec (movR d n) s = some (s.setReg d (s.gpr n)) by simp [movR, exec, Op2.eval],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `r3 := min(r2, 8)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hn : s.gpr .r2 = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa groupCount s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .r3 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₂ := s.setReg t0 (s.gpr .r2 >>> 3)
  let s₃ := subFlags s₂ (s₂.gpr t0) 0
  have e₂₃ : runBlock isa [.mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)] s = some s₃ := by
    rw [runBlock_cons, show exec (.mov t0 (lsrOp .r2 3)) s = some s₂ by simp [exec, Op2.eval, lsrOp, s₂],
      runStep_some, runBlock_cons,
      show exec (.cmp t0 (.imm 0)) s₂ = some s₃ by simp [exec, Op2.eval, s₃]; decide,
      runStep_some, runBlock_nil]
  have z₃ : s₃.z = (BitVec.ofNat 32 v >>> 3 - 0 == 0) := by
    show (s₂.gpr t0 - 0 == 0) = _; rw [RegUpd.gpr_setReg_self, hn]
  have o₃ : ∀ r, r ≠ t0 → s₃.gpr r = s.gpr r := fun r hr => by
    show s₂.gpr r = _; rw [RegUpd.gpr_setReg_of_ne _ _ hr]
  have r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [o₃ _ (by decide), hn]
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₃, e₂₃, ?_⟩)
  refine WP.ite (decide (8 ≤ v)) ((eval_ne s₃).trans (by
      rw [z₃, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega_arith)) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movImm_ok s₃ .r3 8 (by decide)
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, Nat.min_eq_right (by simp at h; omega_arith)]; rfl
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r3 .r2
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, r2₃, Nat.min_eq_left (by simp at h; omega_arith)]

/-- `subs d, n, m`. -/
theorem subsR_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.subs d n (.reg m)] s = some s' ∧ s'.gpr d = s.gpr n - s.gpr m ∧
      s'.z = (s.gpr n - s.gpr m == 0) ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr n) (s.gpr m)).setReg d (s.gpr n - s.gpr m), ?_, RegUpd.gpr_setReg_self _ _ _,
    by rw [RegUpd.z_setReg]; rfl, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d n (.reg m)) s =
    some ((subFlags s (s.gpr n) (s.gpr m)).setReg d (s.gpr n - s.gpr m)) by simp [exec, Op2.eval],
    runStep_some, runBlock_nil]

theorem toNat_add32 (D : BitVec 32) {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).toNat = D.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : d < 2 ^ 32), Nat.mod_eq_of_lt h]


/-- What a copy keeps, after its first `k` bytes. -/
structure Copied (A B : Addr) (c : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  copied : ∀ t < k, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem

/-- `ldr t0, [r0, #d]; str t0, [r1, #d]`: the copy's next word. -/
theorem copyWord_ok {A B : BitVec 32} {c : Nat} {s₀ s : State} {j d : Nat} (hd : d < 16) (hd4 : d % 4 = 0)
    (hj : j < c) (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr B, 16 * c⟩)
    (hr : InRegions (s.rd ++ s.wr) (State.addr A + BitVec.ofNat 64 (16 * j + d)) 4)
    (hw : InRegions s.wr (State.addr B + BitVec.ofNat 64 (16 * j + d)) 4)
    (h0 : s.gpr .r0 = A + BitVec.ofNat 32 (16 * j)) (h1 : s.gpr .r12 = B + BitVec.ofNat 32 (16 * j))
    (hi : Copied (State.addr A) (State.addr B) c s₀ (16 * j + d) s) :
    ∃ s', runBlock isa [.ldr t0 .r0 d, .str t0 .r12 d] s = some s' ∧
      Copied (State.addr A) (State.addr B) c s₀ (16 * j + d + 4) s' ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have eA : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr A + BitVec.ofNat 64 (16 * j + d) := by
    rw [h0, add_ofNat_ofNat, VG.Arm.addr_add (by omega_arith)]
  have eB : State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = State.addr B + BitVec.ofNat 64 (16 * j + d) := by
    rw [h1, add_ofNat_ofNat, VG.Arm.addr_add (by omega_arith)]
  have h₁ : (s.setReg t0 (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32)).gpr .r12 = s.gpr .r12 :=
    RegUpd.gpr_setReg_of_ne _ _ (by decide)
  refine ⟨{ s.setReg t0 (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32) with
      mem := s.mem.writeW (State.addr B + BitVec.ofNat 64 (16 * j + d))
        (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32) }, ?_,
    ⟨fun t ht' => ?_, hi.frame.trans fun x hx => ?_⟩, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩
  · rw [runBlock_cons, exec_ldr (by omega_arith) (by rw [eA]; exact hr), eA, runStep_some, runBlock_cons,
      exec_str (by omega_arith) (by rw [h₁, eB]; exact hw), runStep_some, runBlock_nil, h₁, eB,
      RegUpd.gpr_setReg_self]
    rfl
  · have hn : 16 * c < 2 ^ 64 := by omega_arith
    have hAs : ∀ t < 16 * c, s.mem (State.addr A + BitVec.ofNat 64 t) = s₀.mem (State.addr A + BitVec.ofNat 64 t) :=
      fun t ht => hi.frame.bytes (R := ⟨State.addr A, 16 * c⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by simp only; omega_arith) ht
    show (s.mem.writeW _ _) _ = _
    rw [writeW_readW32_apply]
    by_cases h8 : 16 * j + d ≤ t
    · rw [ite_eq_left (by rw [off_sub_toNat _ h8 (by omega_arith)]; omega_arith), off_sub_toNat _ h8 (by omega_arith),
        VG.Offset.add_add, show 16 * j + d + (t - (16 * j + d)) = t by omega_arith, hAs t (by omega_arith)]
    · rw [ite_eq_right (off_sub_not _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
      exact hi.copied t (by omega_arith)
  · show (s.mem.writeW _ _) x = s.mem x
    rw [writeW_readW32_apply, ite_eq_right fun h =>
      hx _ (List.mem_singleton_self _) (VG.Offset.sub_base _ (show 16 * j + d + 4 ≤ 16 * c by omega_arith) _
        (by simp only [Region.Contains]; omega_arith))]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : BitVec 32) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .r0 = A + BitVec.ofNat 32 (16 * j)
  dst : s.gpr .r12 = B + BitVec.ofNat 32 (16 * j)
  cnt : s.gpr .r3 = BitVec.ofNat 32 (c - j)
  cp : Copied (State.addr A) (State.addr B) c s₀ (16 * j) s
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem copyBlocks_wp {A B : BitVec 32} {c : Nat} {s₀ : State} (hc : 0 < c) (hc8 : c ≤ 8)
    (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hA : ∀ t < 16 * c, t % 4 = 0 → InRegions (s₀.rd ++ s₀.wr) (State.addr A + BitVec.ofNat 64 t) 4)
    (hB : ∀ t < 16 * c, t % 4 = 0 → InRegions s₀.wr (State.addr B + BitVec.ofNat 64 t) 4)
    (hsep : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_arith, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have rA : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.rd = s₀.rd → s.wr = s₀.wr →
      InRegions (s.rd ++ s.wr) (State.addr A + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h1 h2 => by
    rw [h1, h2]; exact hA _ (by omega_arith) (by omega_arith)
  have rB : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (State.addr B + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h2 => by
    rw [h2]; exact hB _ (by omega_arith) (by omega_arith)
  obtain ⟨s₁, e₁, c₁, g₁, rd₁, wr₁, sp₁⟩ := copyWord_ok (d := 0) (by decide) (by decide) hj hfA hfB hsep
    (rA 0 (by decide) (by decide) s hi.rd hi.wr) (rB 0 (by decide) (by decide) s hi.wr) hi.src hi.dst
    (by simpa using hi.cp)
  obtain ⟨s₂, e₂, c₂, g₂, rd₂, wr₂, sp₂⟩ := copyWord_ok (d := 4) (by decide) (by decide) hj hfA hfB hsep
    (rA 4 (by decide) (by decide) s₁ (rd₁.trans hi.rd) (wr₁.trans hi.wr))
    (rB 4 (by decide) (by decide) s₁ (wr₁.trans hi.wr))
    (by rw [g₁ _ (by decide), hi.src]) (by rw [g₁ _ (by decide), hi.dst]) (by simpa using c₁)
  obtain ⟨s₃, e₃, c₃, g₃, rd₃, wr₃, sp₃⟩ := copyWord_ok (d := 8) (by decide) (by decide) hj hfA hfB hsep
    (rA 8 (by decide) (by decide) s₂ (rd₂.trans (rd₁.trans hi.rd)) (wr₂.trans (wr₁.trans hi.wr)))
    (rB 8 (by decide) (by decide) s₂ (wr₂.trans (wr₁.trans hi.wr)))
    (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.src]) (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.dst])
    c₂
  obtain ⟨s₄, e₄, c₄, g₄, rd₄, wr₄, sp₄⟩ := copyWord_ok (d := 12) (by decide) (by decide) hj hfA hfB hsep
    (rA 12 (by decide) (by decide) s₃ (rd₃.trans (rd₂.trans (rd₁.trans hi.rd)))
      (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (rB 12 (by decide) (by decide) s₃ (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.src])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.dst]) c₃
  have g₄' : ∀ r, r ≠ t0 → s₄.gpr r = s.gpr r := fun r hr => by rw [g₄ r hr, g₃ r hr, g₂ r hr, g₁ r hr]
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅, sp₅⟩ := addImm_ok s₄ .r0 .r0 16 (by decide)
  obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := addImm_ok s₅ .r12 .r12 16 (by decide)
  obtain ⟨s₇, e₇, c₇, z₇, o₇, m₇, rd₇, wr₇, sp₇⟩ := subs1_ok s₆ .r3
  refine WP.of_runBlock ⟨s₇, by
    rw [show ([Instr.ldr t0 .r0 0, .str t0 .r12 0, .ldr t0 .r0 4, .str t0 .r12 4,
      .ldr t0 .r0 8, .str t0 .r12 8, .ldr t0 .r0 12, .str t0 .r12 12,
      .dp .add .r0 .r0 (.imm 16), .dp .add .r12 .r12 (.imm 16), .subs .r3 .r3 (.imm 1)] : List Instr) =
      [.ldr t0 .r0 0, .str t0 .r12 0] ++ ([.ldr t0 .r0 4, .str t0 .r12 4] ++ ([.ldr t0 .r0 8, .str t0 .r12 8] ++
      ([.ldr t0 .r0 12, .str t0 .r12 12] ++ ([.dp .add .r0 .r0 (.imm 16)] ++
      ([.dp .add .r12 .r12 (.imm 16)] ++ [.subs .r3 .r3 (.imm 1)]))))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some,
      runBlock_app, e₆, Option.bind_some, e₇], ?_⟩
  have hc₇ : s₇.gpr .r3 = BitVec.ofNat 32 (c - (j + 1)) := by
    rw [c₇, o₆ _ (by decide), o₅ _ (by decide), g₄' _ (by decide), hi.cnt,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      show c - j - 1 = c - (j + 1) by omega_arith]
  have hm : s₇.mem = s₄.mem := by rw [m₇, m₆, m₅]
  have hinv : CopyInv A B c s₀ (j + 1) s₇ := by
    refine ⟨?_, ?_, hc₇, ⟨fun t ht => ?_, by rw [hm]; exact c₄.frame⟩, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr],
      by rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁, hi.sp]⟩
    · rw [o₇ _ (by decide), o₆ _ (by decide), a₅, g₄' _ (by decide), hi.src,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_ofNat,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₇ _ (by decide), a₆, o₅ _ (by decide), g₄' _ (by decide), hi.dst,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_ofNat,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [hm]; exact c₄.copied t (by omega_arith)
    · rw [o₇ r h3, o₆ r h2, o₅ r h1, g₄' r h4, hi.regs r h1 h2 h3 h4]
  have hz : s₇.z = decide (c - (j + 1) = 0) := by
    rw [z₇, ← c₇, hc₇, ofNat32_beq_zero (by omega_arith)]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega_arith),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hinv⟩


end VG.Proof.Camellia.Arm

end

end

/-!
# Slots, and saving and restoring registers, on ARMv7

Loads and stores of the scratch buffer's slots through a base register
(`ldW_ok`, `stW_ok`, and lists of them), and the prologue and epilogue's
saving and restoring of the callee-saved registers (`save_ok`,
`restore_ok`) in the slots from `savedSlot`, as SM4's
(`Proof/Sm4/Arm/Prologue.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (sb t0 t1 kp)

theorem savedSlot_eq : savedSlot = 618 := rfl
theorem dSlot_eq : dSlot = 627 := rfl
theorem nSlot_eq : nSlot = 628 := rfl

/-- The scratch buffer at `b`, in the writable regions. -/
structure ScrIn (rs : List Region) (b : BitVec 32) : Prop where
  mem : (⟨State.addr b, 4 * slots⟩ : Region) ∈ rs
  fit : b.toNat + 4 * slots ≤ 2 ^ 32

theorem ScrIn.slot {rs : List Region} {b : BitVec 32} (h : ScrIn rs b) {k : Nat} (hk : k < slots) :
    InRegions rs (wordAddr b k) 4 := slot_inR h.mem h.fit hk

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A slot is inside the scratch buffer. -/
theorem slot_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k : Nat} (hk : k < slots) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨State.addr b, 4 * slots⟩ := by
  rw [slot_addr (by omega_using [hfit, hk])]
  exact VG.Offset.sub_base _ (by omega_using [hk])

/-- A slot after a store to a slot. -/
theorem readW_slot_write {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hfit, hj]) (by omega_using [hfit, hk]) h) (by decide)

/-- `ldr d, [n, #4 k]`, `n` holding `b`. -/
theorem ldW_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : 4 * k < 4096)
    (hin : InRegions (s.rd ++ s.wr) (wordAddr b k) 4) :
    ∃ s', runBlock isa [.ldr d n (4 * k)] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), by
    rw [runBlock_cons, exec_ldr hk (by rw [hn]; exact hin), hn, runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `str t, [n, #4 k]`, `n` holding `b`. -/
theorem stW_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : 4 * k < 4096)
    (hin : InRegions s.wr (wordAddr b k) 4) :
    runBlock isa [.str t n (4 * k)] s = some { s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) } := by
  rw [runBlock_cons, exec_str hk (by rw [hn]; exact hin), hn, runStep_some, runBlock_nil]

/-- A store to a slot of the scratch buffer. -/
theorem stSlot_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.str t n (4 * k)] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.z = s.z ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem :=
  ⟨_, stW_ok s t n hn (by rw [slots_eq] at hk; omega_using [hk]) (hw.slot hk), rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩

/-- A load of a slot of the scratch buffer. -/
theorem ldSlot_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.ldr d n (4 * k)] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ldW_ok s d n hn (by rw [slots_eq] at hk; omega_using [hk]) (inRd (hw.slot hk))

/-- Stores of registers to distinct slots, through `n`, which none of them is. -/
theorem stW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Nat × Reg)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.map fun x => .str x.2 n (4 * x.1)) s = some s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < slots → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      ∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = s.gpr x.2
  | [], s, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hnd, hin => by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, sp₁, -, f₁⟩ := stSlot_ok s x.2 n hn (hin x List.mem_cons_self) hw
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', sp', f', o', v'⟩ :=
      stW_list_ok n L s₁ (by rw [g₁, hn]) (by rw [wr₁]; exact hw) hnd.2
        fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁, sp'.trans sp₁,
      (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hw.fit (hin x List.mem_cons_self)⟩).trans f',
      fun k hk hks => ?_,
      fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hks, m₁, readW_slot_write hw.fit _ hks (hin x List.mem_cons_self)]
      simp only [hk.1, ite_false]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (hin _ List.mem_cons_self), m₁, Mem.readW_writeW_self32]
      · rw [v' y hy, g₁]

/-- Loads of distinct slots into distinct registers, through `n`, which none of them is. -/
theorem ldW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Reg × Nat)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (∀ x ∈ L, x.1 ≠ n) → (L.map (·.1)).Nodup → (∀ x ∈ L, x.2 < slots) →
    ∃ s', runBlock isa (L.map fun x => .ldr x.1 n (4 * x.2)) s = some s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧
      ∀ x ∈ L, s'.gpr x.1 = s.mem.readW (wordAddr b x.2) 32
  | [], s, _, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hne, hnd, hin => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s x.1 n hn (hin x List.mem_cons_self) hw
    have hn₁ : s₁.gpr n = b := by rw [o₁ _ (hne x List.mem_cons_self).symm, hn]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', sp', o', v'⟩ := ldW_list_ok n L s₁ hn₁ (by rw [wr₁]; exact hw)
      (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, sp'.trans sp₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1, v₁]
      · rw [v' y hy, m₁]

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .r4

theorem savedRegs_eq : savedRegs = (List.range 9).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 9, m.readW (wordAddr b (savedSlot + i)) 32 = s₀.gpr (sreg i)

theorem save_ok {s : State} {base : Reg} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr base = b) :
    ∃ s', runBlock isa (saveRegs base) s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem ∧
      ∀ k, k < savedSlot → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 := by
  let L : List (Nat × Reg) := (List.range 9).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs base = L.map fun x => .str x.2 base (4 * x.1) := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 9).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  obtain ⟨s', e', g', rd', wr', sp', f', o', v'⟩ := stW_list_ok base L s hb hw (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega)
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, g', rd', wr', sp', f', fun k hk => o' k ?_ (by
    rw [savedSlot_eq] at hk; rw [slots_eq]; omega_using [hk])⟩
  · exact v' (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
  · rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega_using [hk, h]

theorem sreg_ne_r12 : ∀ i < 9, sreg i ≠ .r12 := by decide

theorem restore_ok {s₀ s : State} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr .r12 = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa (restoreRegs .r12) s = some s' ∧ (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 9, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let L : List (Reg × Nat) := (List.range 9).map fun i => (sreg i, savedSlot + i)
  have hL : restoreRegs .r12 = L.map fun x => .ldr x.1 .r12 (4 * x.2) := by
    rw [restoreRegs, savedRegs_eq]
  have hregs : L.map (·.1) = (List.range 9).map sreg := by simp only [L, List.map_map]; rfl
  obtain ⟨s', e', m', rd', wr', sp', o', v'⟩ := ldW_list_ok .r12 L s hb hw
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx; exact sreg_ne_r12 i hi)
    (by rw [hregs]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega)
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, fun r hr => o' r ?_, m', rd', wr', sp'⟩
  · rw [v' (sreg i, savedSlot + i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)]
    exact hs i hi
  · rw [hregs]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    exact fun i hi h => hr i hi h.symm

end VG.Proof.Camellia.Arm

end

end

/-! ### `Camellia.Arm.StoreFrame`, which this module and modules that import it used -/

section

/-!
# A block that stores only at given offsets of `sb` (ARMv7)

`runBlock_storesIn`: a block whose every instruction stores nothing but a
word at `sb + d`, for `lo ≤ d` and `d + 4 ≤ hi`, and never writes `sb`
(`storesIn lo hi`, checked of every instruction by evaluation), keeps `sb`
and the memory outside `[sb + lo, sb + hi)`. The tail of Camellia's eight
blocks stores the blocks through `sb`, whose slots the analysis of constant
time tracks, and this gives its frame, which the linear checker's (every
slot below `hi`) does not.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm
open VG.Impl.Aes.Arm (sb)

/-- `i` stores nothing but the word at `sb + d`, for `lo ≤ d` and `d + 4 ≤ hi`,
and does not write `sb`. -/
def storesIn (lo hi : Nat) : Instr → Bool
  | .str _ n d => n == sb && decide (lo ≤ d) && decide (d + 4 ≤ hi)
  | .strb .. | .push _ | .pop .. | .alloc _ | .free _ => false
  | i => !clobbers i sb

/-- The bytes `[sb + lo, sb + hi)`. -/
abbrev storeRegion (b : BitVec 32) (lo hi : Nat) : Region := ⟨State.addr b + BitVec.ofNat 64 lo, hi - lo⟩

theorem exec_mem_of_noStore {i : Instr} {s s' : State} (h : exec i s = some s')
    (hi : ∀ t n off, i ≠ .str t n off) (hb : ∀ t n off, i ≠ .strb t n off) : s'.mem = s.mem := by
  cases i with
  | str t n off => exact absurd rfl (hi t n off)
  | strb t n off => exact absurd rfl (hb t n off)
  | _ =>
    simp only [reduceExec, State.load32, State.load8, Option.map_eq_some_iff] at h
    (repeat' split at h) <;>
    (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    first
    | (subst h; rfl)
    | (obtain ⟨_, _, rfl⟩ := h; rfl)
    | (cases h)

theorem exec_storesIn {lo hi : Nat} {i : Instr} {s s' : State} (hs : storesIn lo hi i = true)
    (hfit : (s.gpr sb).toNat + hi ≤ 2 ^ 32) (h : exec i s = some s') :
    s'.gpr sb = s.gpr sb ∧ Frame [storeRegion (s.gpr sb) lo hi] s.mem s'.mem := by
  cases i with
  | str t n d =>
    simp only [storesIn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    obtain ⟨⟨rfl, h1⟩, h2⟩ := hs
    simp only [reduceExec, State.store32] at h
    split at h <;> [skip; cases h]
    split at h <;> [skip; cases h]
    simp only [Option.some.injEq] at h; subst h
    refine ⟨rfl, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_⟩
    rw [VG.Arm.addr_add (by omega_using [hfit, h2])]
    exact VG.Offset.contains _ h1 (by omega_using [h2]) (by have := (s.gpr sb).isLt; omega_using [hfit, h2, h1])
  | _ =>
    first
    | (simp [storesIn] at hs; done)
    | (refine ⟨exec_gpr (by simp_all [storesIn]) h, ?_⟩
       rw [exec_mem_of_noStore h (fun _ _ _ e => nomatch e) (fun _ _ _ e => nomatch e)]
       exact Frame.refl _ _)

theorem runBlock_storesIn {lo hi : Nat} : ∀ (is : List Instr) {s s' : State},
    is.all (storesIn lo hi) = true → (s.gpr sb).toNat + hi ≤ 2 ^ 32 → runBlock isa is s = some s' →
      s'.gpr sb = s.gpr sb ∧ Frame [storeRegion (s.gpr sb) lo hi] s.mem s'.mem
  | [], s, s', _, _, h => by
    rw [runBlock_nil, Option.some.injEq] at h; subst h; exact ⟨rfl, Frame.refl _ _⟩
  | i :: is, s, s', ha, hfit, h => by
    simp only [List.all_cons, Bool.and_eq_true] at ha
    rw [runBlock_cons] at h
    cases he : exec i s with
    | none => rw [he] at h; cases h
    | some s₁ =>
      rw [he, runStep_some] at h
      obtain ⟨b₁, f₁⟩ := exec_storesIn ha.1 hfit he
      obtain ⟨b₂, f₂⟩ := runBlock_storesIn is ha.2 (by rw [b₁]; exact hfit) h
      rw [b₁] at b₂ f₂
      exact ⟨b₂, f₁.trans f₂⟩

end VG.Proof.Camellia.Arm

end

end

/-!
# The head and tail of eight blocks of bitsliced Camellia on ARMv7

`head` bitslices both halves of the eight blocks in the tail buffer (at
`r12`) and whitens them, and `tail` whitens, transposes and stores them
back; between them the groups of rounds (`group_wp`) run in a loop.
`crypt8_ok` composes them: each block becomes `cryptWords g E` of it.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Bitslice (lanes)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp ldS stS)
open VG.Proof.Camellia (pair group groups cryptWords groupsN groupsN_succ)
open VG.Proof.Sm4.Arm (linPostG linG_ok)

/-! ## The tail buffer -/

/-- Word `t` of the tail buffer. -/
abbrev dataW (s : State) (t : Nat) : BitVec 32 := slotW s (tailSlot + t)

/-- Block `b` in the tail buffer. -/
abbrev blk (s : State) (b : Nat) : Spec.Camellia.Block :=
  Spec.Camellia.blockAt s.mem (State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * b))

theorem dataW_byte (s : State) (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) {b c j : Nat} (hb : b < 8)
    (hc : c < 16) (hj : j < 8) :
    (dataW s (4 * b + c / 4)).getLsbD (8 * (c % 4) + j) =
      (s.mem (State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * b) + BitVec.ofNat 64 c)).getLsbD j := by
  rw [slots_eq] at hfit
  rw [dataW, slotW, wordAddr, VG.Arm.addr_add (by rw [tailSlot_eq]; omega_arith), W32.readW32_bit _ _ (by omega_arith) hj,
    VG.Offset.add_add, VG.Offset.add_add,
    show 4 * (tailSlot + (4 * b + c / 4)) + c % 4 = 4 * tailSlot + 16 * b + c by omega_arith]

theorem data_words (s : State) (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) :
    W32.BlockWords (dataW s) (blk s) := fun b hb c hc j hj => by
  rw [dataW_byte s hfit hb hc hj]
  simp [Spec.Camellia.blockAt]

theorem blk_of_words {s : State} (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) {B : Nat → Spec.Camellia.Block}
    (h : W32.BlockWords (dataW s) B) {b : Nat} (hb : b < 8) : blk s b = B b := by
  apply Vector.ext
  intro c hc
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [← h b hb c hc j hj, dataW_byte s hfit hb hc hj]
  simp [Spec.Camellia.blockAt]

/-! ## The transposes -/

/-- `r12` points to the tail buffer. -/
def AtTail (s : State) : Prop := s.gpr u7 = s.gpr sb + BitVec.ofNat 32 (4 * tailSlot)

theorem wordAddr_tail {s : State} (h : AtTail s) (j : Nat) :
    wordAddr (s.gpr u7) j = wordAddr (s.gpr sb) (tailSlot + j) := by
  rw [wordAddr, wordAddr, h, add_ofNat_ofNat, show 4 * tailSlot + 4 * j = 4 * (tailSlot + j) by omega_arith]

theorem ok_toBs {s : State} (hs : Scr s (s.gpr sb)) (ht : AtTail s) : Ok toBsCfg s where
  slotIn k hk := hs.slot_in (by simp only [toBsCfg, keySlot_eq] at hk; rw [slots_eq]; omega_arith)
  extIn j hj := by
    simp only [toBsCfg] at hj ⊢
    rw [wordAddr_tail ht]
    obtain ⟨r, hr, hc⟩ := hs.slot_in (k := tailSlot + j) (by rw [slots_eq, tailSlot_eq]; omega_arith)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  slots := by have := hs.fit; simp only [toBsCfg]; rw [slots_eq] at this; rw [keySlot_eq]; omega_arith
  sep k hk j hj := by
    have := hs.fit
    simp only [toBsCfg, keySlot_eq] at hk hj ⊢
    rw [wordAddr_tail ht]
    rw [slots_eq] at this
    exact slot_sep _ (by omega_arith) (by rw [tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)

theorem toBs_all : (layerKeep.all fun r => ((List.range 4).flatMap toBsWord).all fun i => !clobbers i r) =
    true ∧ (((List.range 4).flatMap toBsWord).all fun i => !clobbers i u7) = true := by
  constructor <;> decide +kernel

/-- `toBs`: the planes of the halves, from the words of the blocks. -/
theorem toBs_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    (ht : AtTail s) :
    ∃ s', runBlock isa ((List.range 4).flatMap toBsWord) s = some s' ∧ Ctx s₀ s' ∧
      s'.gpr kp = s.gpr kp ∧ s'.gpr u7 = s.gpr u7 ∧
      (∀ w < 4, ∀ j < 8, ∀ p < 32, (slotW s' (d1Slot + (8 * w + j))).getLsbD p =
        (dataW s (4 * (p % 8) + w)).getLsbD (8 * (p / 8) + j)) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hs := hc.scr hp
  obtain ⟨s', h', -, so', -, rd', wr', -, o', f', -, -⟩ := linG_ok toBs_check (ok_toBs hs ht) (dataW s)
    (fun r i hri => by simp at hri) (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv)
    (fun j hj => ⟨by simp only [toBsCfg] at hj; omega_arith, by rw [Nat.zero_add]; simp only [toBsCfg, wordAddr_tail ht]⟩)
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp toBs_all.1 r (not_layerWrites r hr))
  have hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32 := hs.fit
  refine ⟨s', h', hc.stepL rd' wr' (fun r h1 _ => hkeep r h1) f', hkeep _ (by decide), o' _ toBs_all.2,
    fun w hw j hj p hp => ?_, fun k h1 h2 => slot_above_frame hfit (hkeep _ (by decide)) f' h1 h2⟩
  have := so' (d1Slot + (8 * w + j)) (toBsG w j)
    (by
      simp only [toBsOuts, List.mem_map, List.mem_range, Prod.mk.injEq]
      exact ⟨8 * w + j, by omega_arith, rfl, by rw [show (8 * w + j) / 8 = w by omega_arith, show (8 * w + j) % 8 = j by omega_arith]⟩)
    (by simp only [toBsCfg, d1Slot_eq, keySlot_eq]; omega_arith) p hp
  simp only [toBsCfg] at this
  rw [slotW, hkeep _ (by decide), this, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc,
    bitOf_word _ _ _ (by omega_arith)]

theorem ok_fromBs {s : State} (hs : Scr s (s.gpr sb)) : Ok fromBsCfg s where
  slotIn k hk := by
    simp only [fromBsCfg] at hk ⊢
    exact hs.slot_in (by rw [slots_eq]; rw [tailSlot_eq] at hk; omega_arith)
  extIn j hj := by simp [fromBsCfg] at hj
  slots := by
    have := hs.fit
    simp only [fromBsCfg, tailSlot_eq]
    rw [slots_eq] at this; omega_arith
  sep k _ j hj := by simp [fromBsCfg] at hj

theorem fromBs_all : (layerKeep.all fun r => ((List.range 4).flatMap fromBsWord).all fun i => !clobbers i r) =
    true ∧ (((List.range 4).flatMap fromBsWord).all (storesIn (4 * tailSlot) (4 * tailSlot + 128))) = true := by
  constructor <;> decide +kernel

/-- `fromBs`: the words of the blocks, from the planes of the halves. -/
theorem fromBs_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa ((List.range 4).flatMap fromBsWord) s = some s' ∧ Ctx s₀ s' ∧
      (∀ b < 8, ∀ w < 4, ∀ i < 4, ∀ j < 8, (dataW s' (4 * b + w)).getLsbD (8 * i + j) =
        (slotW s (d1Slot + (8 * ((w + 2) % 4) + j))).getLsbD (8 * i + b)) := by
  have hs := hc.scr hp
  obtain ⟨s', h', -, so', -, rd', wr', -, o', -, -, -⟩ := linG_ok fromBs_check (ok_fromBs hs) (slotW s)
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [fromBsIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [fromBsCfg, d1Slot_eq, tailSlot_eq]; omega_arith, by rw [d1Slot_eq]; omega_arith, rfl⟩)
    (fun kv hkv => by simp at hkv) (fun j hj => by simp [fromBsCfg] at hj)
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp fromBs_all.1 r (not_layerWrites r hr))
  have hfit := hs.fit
  rw [slots_eq] at hfit
  obtain ⟨-, f'⟩ := runBlock_storesIn _ fromBs_all.2 (by rw [tailSlot_eq]; omega_arith) h'
  refine ⟨s', h', hc.step rd' wr' (fun r h1 _ => hkeep r h1) ?_, fun b hb w hw i hi j hj => ?_⟩
  · refine f'.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hb := hc.base
    refine ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inr (.inl rfl)), ?_⟩
    simp only [storeRegion, hb]
    rw [VG.Arm.addr_add (by rw [← hb, tailSlot_eq]; omega_arith), show 4 * tailSlot + 128 - 4 * tailSlot = 128 by omega_arith]
    exact fun _ h => h
  · have := so' (tailSlot + (4 * b + w)) (fromBsG (4 * b + w))
      (by simp only [fromBsOuts, List.mem_map, List.mem_range]; exact ⟨4 * b + w, by omega_arith, rfl⟩)
      (by simp only [fromBsCfg]; omega_arith) (8 * i + j) (by omega_arith)
    simp only [fromBsCfg] at this
    rw [dataW, slotW, hkeep _ (by decide), this, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
      show (4 * b + w) % 4 = w by omega_arith, show (8 * i + j) % 8 = j by omega_arith, show (8 * i + j) / 8 = i by omega_arith,
      show (4 * b + w) / 4 = b by omega_arith, Nat.add_assoc, bitOf_word _ _ _ (by omega_arith),
      show d1Slot + 8 * ((w + 2) % 4) + j = d1Slot + (8 * ((w + 2) % 4) + j) by omega_arith]

/-! ## The whitening -/

theorem whiten_all (swap : Bool) :
    (layerKeep.all fun r => (whiten swap).all fun i => !clobbers i r) = true ∧
      ((whiten swap).all fun i => !clobbers i u7) = true := by
  cases swap <;> (constructor <;> decide +kernel)

/-- The whitening, with the two entries at `kp`. -/
theorem whiten_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) (swap : Bool)
    (hchk : check (lanes 32 11) layerCfg (linExt 32) (whiten swap) whitenEnv
      (linPostG 11 [] (whitenOuts swap) [] whitenEnv) = true) :
    ∃ s', runBlock isa (whiten swap) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ s'.gpr u7 = s.gpr u7 ∧
      (∀ i < 32, ∀ p < 32, (slotW s' (d1Slot + i)).getLsbD p =
        ((slotW s (d1Slot + i)).getLsbD p ^^ (keyW s (if swap then (i + 16) % 32 else i)).getLsbD p)) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hok := hc.ok hp hk hm34
  let W : Nat → BitVec 32 := fun i => if i < 32 then slotW s (d1Slot + i) else keyW s (i - 32)
  obtain ⟨s', h', -, so', -, rd', wr', -, o', f', -, -⟩ := linG_ok hchk hok W
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk', rfl, rfl⟩ := halvesIns_mem hji
      exact ⟨by simp only [layerCfg, keySlot_eq, d1Slot_eq]; omega_arith, by omega_arith, by simp [W, hk']; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W, show ¬ 32 + j < 32 by omega_arith]; rfl⟩)
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp (whiten_all swap).1 r (not_layerWrites r hr))
  have hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32 := by rw [hc.base]; exact hp.scr.fit
  refine ⟨s', h', hc.stepL rd' wr' (fun r h1 _ => hkeep r h1) f', hkeep _ (by decide), o' _ (whiten_all swap).2,
    fun i hi p hp => ?_, fun k h1 h2 => slot_above_frame hfit (hkeep _ (by decide)) f' h1 h2⟩
  have := so' (d1Slot + i) (whitenG swap i)
    (by simp only [whitenOuts, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
    (by simp only [layerCfg, d1Slot_eq, keySlot_eq]; omega_arith) p hp
  simp only [layerCfg] at this
  have hki : (if swap then (i + 16) % 32 else i) < 32 := by split <;> omega_arith
  rw [slotW, hkeep _ (by decide), this, whitenG, Straight.xorBits_cons, Straight.xorBits_cons,
    Straight.xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
  simp only [W, hi, ↓reduceIte, show ¬ 32 + (if swap then (i + 16) % 32 else i) < 32 by omega_arith,
    show 32 + (if swap then (i + 16) % 32 else i) - 32 = (if swap then (i + 16) % 32 else i) by omega_arith]

/-! ## The head -/

theorem exec_addImm {s : State} {d n : Reg} {v : BitVec 32} (he : encodable v = true) :
    exec (.dp .add d n (.imm v)) s = some (s.setReg d (s.gpr n + v)) := by
  simp only [exec, Op2.eval, he, ↓reduceIte, Option.map_some]

/-- The halves of the eight blocks after the prewhitening. -/
def headHalves (s : State) (E : Nat → BitVec 64) (b : Nat) : BitVec 64 × BitVec 64 :=
  (W32.hiOf (blk s b) ^^^ E 0, W32.loOf (blk s b) ^^^ E 1)

theorem head_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) :
    ∃ s', runBlock isa head s₀ = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) 2 ∧
      Halves s' (headHalves s₀ E) := by
  have hg : 8 * g + 2 ≤ 34 := hp.nk34
  have hfit := hp.scr.fit
  let b := s₀.gpr sb
  -- `r12 := ` the tail buffer.
  have e₁ : exec (slotAddr u7 tailSlot) s₀ =
      some (s₀.setReg u7 (s₀.gpr sb + BitVec.ofNat 32 (4 * tailSlot))) := exec_addImm (by decide)
  have c₁ := (Ctx.refl s₀).step (s' := s₀.setReg u7 (s₀.gpr sb + BitVec.ofNat 32 (4 * tailSlot))) rfl rfl
    (fun r h1 _ => RegUpd.gpr_setReg_of_ne _ _ (fun h => h1 (by rw [h]; decide))) (Frame.refl _ _)
  have t₁ : AtTail (s₀.setReg u7 (s₀.gpr sb + BitVec.ofNat 32 (4 * tailSlot))) := by
    rw [AtTail, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide)]
  -- The transposes.
  obtain ⟨s₂, e₂, c₂, -, -, x₂, a₂⟩ := toBs_step hp.toKeyCtx c₁ t₁
  have hd₁ : ∀ t, dataW (s₀.setReg u7 (s₀.gpr sb + BitVec.ofNat 32 (4 * tailSlot))) t = dataW s₀ t :=
    fun t => slotW_setReg _ _ (by decide) _
  obtain ⟨hD1, hD2⟩ := W32.halves_of_words (Q := fun k => slotW s₂ (d1Slot + k))
    (fun w hw j hj p hp => by rw [x₂ w hw j hj p hp, hd₁]) (data_words s₀ hfit)
  -- `kp := ` the table, and the whitening.
  have e₃ : exec (slotAddr kp keySlot) s₂ = some (s₂.setReg kp (s₂.gpr sb + BitVec.ofNat 32 (4 * keySlot))) :=
    exec_addImm (by decide)
  have c₃ := c₂.step (s' := s₂.setReg kp (s₂.gpr sb + BitVec.ofNat 32 (4 * keySlot))) rfl rfl
    (fun r _ h2 => RegUpd.gpr_setReg_of_ne _ _ h2) (Frame.refl _ _)
  have k₃ : AtEntry (s₂.setReg kp (s₂.gpr sb + BitVec.ofNat 32 (4 * keySlot))) b 0 := by
    rw [AtEntry, RegUpd.gpr_setReg_self, c₂.base, Nat.mul_zero, Nat.add_zero]
  obtain ⟨s₄, e₄, c₄, kp₄, -, w₄, -⟩ := whiten_step hp.toKeyCtx c₃ k₃ (by omega_arith) false whiten0_check
  have hK0 := c₃.keyRel hp.toKeyCtx k₃ (e := 0) (by omega_arith)
  have hK1 := c₃.keyRel hp.toKeyCtx k₃ (e := 1) (by omega_arith)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hK0 hK1
  have hs₃ : ∀ k, slotW (s₂.setReg kp (s₂.gpr sb + BitVec.ofNat 32 (4 * keySlot))) k = slotW s₂ k :=
    fun k => slotW_setReg _ _ (by decide) _
  -- `kp += 128`.
  refine ⟨s₄.setReg kp (s₄.gpr kp + BitVec.ofNat 32 128), ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · rw [show head = [slotAddr u7 tailSlot] ++ (List.range 4).flatMap toBsWord ++ [slotAddr kp keySlot] ++
        whiten false ++ [.dp .add kp kp (.imm (BitVec.ofNat 32 128))] from rfl,
      runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_cons, e₁, runStep_some, runBlock_nil,
      Option.bind_some, e₂, Option.bind_some, runBlock_cons, e₃, runStep_some, runBlock_nil, Option.bind_some,
      e₄, Option.bind_some, addKp_ok _ _ encodable_128]
  · exact c₄.step rfl rfl (fun r _ h2 => RegUpd.gpr_setReg_of_ne _ _ h2) (Frame.refl _ _)
  · exact k₃.add (n := 2) (by rw [RegUpd.gpr_setReg_self, kp₄])
  · refine (W32.HalfRel.xor hD1 hK0 fun i hi p hp => ?_).congr_right fun _ _ => rfl
    show (slotW (s₄.setReg kp _) (d1Slot + i)).getLsbD p = _
    rw [slotW_setReg _ _ (by decide), w₄ i (by omega_arith) p hp, hs₃]
    simp
  · refine (W32.HalfRel.xor hD2 hK1 fun i hi p hp => ?_).congr_right fun _ _ => rfl
    show (slotW (s₄.setReg kp _) (d2Slot + i)).getLsbD p = _
    rw [slotW_setReg _ _ (by decide), show d2Slot + i = d1Slot + (16 + i) by rw [d1Slot_eq, d2Slot_eq]; omega_arith,
      w₄ (16 + i) (by omega_arith) p hp, hs₃]
    simp

/-! ## The tail -/

theorem tail_ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    (hk : AtEntry s (s₀.gpr sb) (8 * g)) {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa tail s = some s' ∧ Ctx s₀ s' ∧
      W32.BlockWords (dataW s')
        (fun b => Spec.Camellia.encodeBlock (((S b).2 ^^^ E (8 * g)) ++ ((S b).1 ^^^ E (8 * g + 1)))) := by
  have hg : 8 * g + 2 ≤ 34 := hp.nk34
  obtain ⟨h1, h2⟩ := hS
  have hK0 := hc.keyRel hp.toKeyCtx hk (e := 0) (by omega_arith)
  have hK1 := hc.keyRel hp.toKeyCtx hk (e := 1) (by omega_arith)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.add_zero] at hK0 hK1
  obtain ⟨s₁, e₁, c₁, -, -, w₁, -⟩ := whiten_step hp.toKeyCtx hc hk (by omega_arith) true whiten1_check
  obtain ⟨s₃, e₃, c₃, x₃⟩ := fromBs_step hp.toKeyCtx c₁
  refine ⟨s₃, ?_, c₃, W32.block_of_planes (Q := fun k => slotW s₁ (d1Slot + (k + 16) % 32))
    (fun b hb w hw i hi j hj => ?_) ?_ ?_⟩
  · rw [tail, runBlock_app, e₁, Option.bind_some, e₃]
  · rw [x₃ b hb w hw i hi j hj]
    congr 3; omega_arith
  · refine (W32.HalfRel.xor h2 hK0 fun i hi p hp => ?_).congr_right fun _ _ => rfl
    show (slotW s₁ _).getLsbD p = _
    rw [show d1Slot + (i + 16) % 32 = d1Slot + (16 + i) by omega_arith, w₁ (16 + i) (by omega_arith) p hp,
      show d1Slot + (16 + i) = d2Slot + i by rw [d1Slot_eq, d2Slot_eq]; omega_arith]
    simp only [↓reduceIte, show (16 + i + 16) % 32 = i by omega_arith, half]
  · refine (W32.HalfRel.xor h1 hK1 fun i hi p hp => ?_).congr_right fun _ _ => rfl
    show (slotW s₁ _).getLsbD p = _
    rw [show (16 + i + 16) % 32 = i by omega_arith, w₁ i (by omega_arith) p hp]
    simp only [↓reduceIte, show (i + 16) % 32 = 16 + i by omega_arith, half]

/-! ## The groups -/

theorem groups_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    (hk : AtEntry s (s₀.gpr sb) 2) {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    WP isa (.loop groupBody .ne) s fun s' => Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (8 * g) ∧
      Halves s' (fun b => groups g E (S b)) := by
  have hg0 : 0 < g := by rcases hp.hg with h | h <;> omega_arith
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = g - i ∧ i < g ∧ Ctx s₀ s' ∧
    AtEntry s' (s₀.gpr sb) (2 + 8 * i) ∧ Halves s' (fun b => groupsN g E i (S b))
  refine WP.loop (M := isa) Inv (fun n s' hs' => ?_) g s ⟨0, by omega_arith, hg0, hc, hk, by simpa [groupsN] using hS⟩
  obtain ⟨i, rfl, hi, hc', hk', hS'⟩ := hs'
  refine WP.mono (group_wp hp hc' hi hk' hS') fun s'' ⟨c'', S'', k'', z''⟩ => ?_
  simp only [← groupsN_succ] at S''
  by_cases he : i + 1 = g
  · refine .inl ⟨(eval_ne s'').trans (by rw [z'']; simp [he]), c'', ?_, ?_⟩
    · simpa only [show ¬ i + 1 < g by omega_arith, ↓reduceIte] using k''
    · have hG : ∀ d, groupsN g E (i + 1) d = groups g E d := fun d => by rw [he]; rfl
      simpa only [hG] using S''
  · refine .inr ⟨(eval_ne s'').trans (by rw [z'']; simp [he]), g - (i + 1), by omega_arith, i + 1, rfl,
      by omega_arith, c'', ?_, S''⟩
    simpa only [show i + 1 < g by omega_arith, ↓reduceIte] using k''

/-! ## Eight blocks -/

/-- `crypt8`: each of the eight blocks in the tail buffer becomes `cryptWords g E` of it. -/
theorem crypt8_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) :
    WP isa crypt8 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 8, blk s' b = Spec.Camellia.encodeBlock (cryptWords g E (Spec.Camellia.decodeBlock (blk s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, k₁, S₁⟩ := head_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (groups_wp hp c₁ k₁ S₁) fun s₂ ⟨c₂, k₂, S₂⟩ => ?_)
  obtain ⟨s₃, e₃, c₃, w₃⟩ := tail_ok hp c₂ k₂ S₂
  refine WP.of_runBlock ⟨s₃, e₃, c₃, fun b hb => ?_⟩
  rw [blk_of_words (by rw [c₃.base]; exact hp.scr.fit) w₃ hb, cryptWords]
  rfl

end VG.Proof.Camellia.Arm
