module

public import VerifiedGarbage.Impl.Mont.AArch64.P521.Op
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Straight-line carry arithmetic on AArch64: what it computes

A sequence of `Op`s runs on the machine (`run_ok`) as on registers holding
numbers below `2⁶⁴` and a carry of 0 or 1 (`St`, `run`), for operands that
can be loaded (`InOk`): the memory, the regions and the registers it does
not write are unchanged.
-/

-- separate module: the machine's part of the checker, without its data
@[expose] public section

namespace VG.Proof.Mont.AArch64.P521

open VG VG.AArch64 VG.Impl.Mont.AArch64.P521
open VG.Proof.Mont (off word)
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- Registers as numbers, and the carry. -/
structure St where
  g : Reg → Nat
  c : Nat

/-- The state with register `d` holding `v`. -/
def St.set (s : St) (d : Reg) (v : Nat) : St := ⟨fun r => if r = d then v else s.g r, s.c⟩

/-- The state with register `d` holding `v mod 2⁶⁴`, and the carry `v / 2⁶⁴`. -/
def St.setc (s : St) (d : Reg) (v : Nat) : St :=
  ⟨fun r => if r = d then v % 2 ^ 64 else s.g r, v / 2 ^ 64⟩

/-- An operation on numbers, with the operands' words `inp`. -/
def step (inp : Nat → Nat → Nat) : Op → St → St
  | .ld k i d, s => s.set d (inp k i)
  | .mul d n m, s => s.set d (s.g n * s.g m % 2 ^ 64)
  | .umulh d n m, s => s.set d (s.g n * s.g m / 2 ^ 64)
  | .add d n m, s => s.set d ((s.g n + s.g m) % 2 ^ 64)
  | .adds d n m, s => s.setc d (s.g n + s.g m)
  | .adcs d n m, s => s.setc d (s.g n + s.g m + s.c)
  | .adc d n m, s => s.set d ((s.g n + s.g m + s.c) % 2 ^ 64)
  | .subs d n m, s => s.setc d (s.g n + (2 ^ 64 - 1 - s.g m) + 1)
  | .sbcs d n m, s => s.setc d (s.g n + (2 ^ 64 - 1 - s.g m) + s.c)
  | .lsl d n k, s => s.set d (s.g n * 2 ^ k % 2 ^ 64)
  | .lsr d n k, s => s.set d (s.g n / 2 ^ k)
  | .extr d n m k, s => s.set d ((s.g n * 2 ^ 64 + s.g m) / 2 ^ k % 2 ^ 64)
  | .movz d v, s => s.set d (v % 2 ^ 16)
  | .low d n m _, s => s.set d (s.g n &&& s.g m)

/-- A sequence of operations. -/
def run (inp : Nat → Nat → Nat) : List Op → St → St
  | [], s => s
  | o :: os, s => run inp os (step inp o s)

/-- The registers and the carry of a machine state. -/
def ofState (s : State) : St := ⟨fun r => (s.gpr r).toNat, s.c.toNat⟩

/-- Every register holds a word, and the carry is 0 or 1. -/
structure Ok (s : St) : Prop where
  g : ∀ r, s.g r < 2 ^ 64
  c : s.c ≤ 1

theorem ofState_ok (s : State) : Ok (ofState s) := ⟨fun r => (s.gpr r).isLt, Bool.toNat_le s.c⟩

/-- The operands' words can be loaded: word `i` of operand `k` is `inp k i`,
for the operands and words that `use` allows. -/
structure InOk (ptr : Nat → Reg × Nat) (use : Nat → Nat → Prop) (inp : Nat → Nat → Nat) (s : State) : Prop where
  ld : ∀ k i, use k i → InRegions (s.rd ++ s.wr) (s.gpr (ptr k).1 + BitVec.ofNat 64 ((ptr k).2 + 8 * i)) 8
  enc : ∀ k i, use k i → ((ptr k).2 + 8 * i) % 8 = 0 ∧ (ptr k).2 + 8 * i < 32768
  val : ∀ k i, use k i → (word s.mem (s.gpr (ptr k).1) ((ptr k).2 + 8 * i)).toNat = inp k i

/-- The operation's shifts and constants can be encoded, its loads are of
words `use` allows, and it does not write a pointer. -/
def Enc (ptr : Nat → Reg × Nat) (use : Nat → Nat → Prop) : Op → Prop
  | .ld k i d => use k i ∧ ∀ q, (ptr q).1 ≠ d
  | .lsl d _ k | .lsr d _ k | .extr d _ _ k => k < 64 ∧ ∀ q, (ptr q).1 ≠ d
  | o => ∀ q, (ptr q).1 ≠ o.dst

theorem Enc.dst {ptr : Nat → Reg × Nat} {use : Nat → Nat → Prop} {o : Op} (h : Enc ptr use o) :
    ∀ q, (ptr q).1 ≠ o.dst := by
  cases o <;> first | exact h | exact h.2

theorem InOk.of_same {ptr : Nat → Reg × Nat} {use : Nat → Nat → Prop} {inp : Nat → Nat → Nat} {s t : State}
    (h : InOk ptr use inp s) (hg : ∀ q, t.gpr (ptr q).1 = s.gpr (ptr q).1) (hm : t.mem = s.mem)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : InOk ptr use inp t :=
  ⟨fun k i hk => by rw [hg, hr, hw]; exact h.ld k i hk, h.enc, fun k i hk => by rw [hg, hm]; exact h.val k i hk⟩

private theorem not_toNat (x : BitVec 64) : (~~~x).toNat = 2 ^ 64 - 1 - x.toNat := by
  rw [BitVec.toNat_not]

private theorem write_rel (s : State) (d : Reg) (v : BitVec 64) (w : Nat) (h : v.toNat = w) :
    ofState (s.write .x d v) = (ofState s).set d w ∧ Keeps [d] s (s.write .x d v) ∧ (s.write .x d v).v = s.v := by
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [ofState, St.set, RegUpd.c_write, St.mk.injEq, and_true]
    funext r
    rw [RegUpd.gpr_write]
    split
    · simp only [Size.bits, BitVec.setWidth_eq, h]
    · rfl
  · simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr

private theorem awc_rel (s : State) (d : Reg) (a b : BitVec 64) (c : Bool) (w : Nat)
    (h : a.toNat + b.toNat + c.toNat = w) :
    ofState (s.addWithCarry .x d a b c) = (ofState s).setc d w ∧ Keeps [d] s (s.addWithCarry .x d a b c) ∧
      (s.addWithCarry .x d a b c).v = s.v := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := Bool.toNat_le c
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [ofState, St.setc, St.mk.injEq]
    constructor
    · funext r
      rw [RegUpd.gpr_addWithCarry]
      split
      · simp only [Size.bits, BitVec.setWidth_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [← h]
        omega_using [hc]
      · rfl
    · rw [RegUpd.c_addWithCarry, ← h]
      by_cases hh : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat
      · simp only [Size.bits, hh, decide_true, Bool.toNat_true]
        omega_using [hh, ha, hb, hc]
      · simp only [Size.bits, hh, decide_false, Bool.toNat_false]
        omega_using [hh]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_addWithCarry, hr, ite_false]

/-- One operation on the machine. -/
theorem step_ok {ptr : Nat → Reg × Nat} {use : Nat → Nat → Prop} {inp : Nat → Nat → Nat} {s : State}
    (hi : InOk ptr use inp s) {o : Op} (he : Enc ptr use o) :
    ∃ t, exec (o.instr ptr) s = some t ∧ ofState t = step inp o (ofState s) ∧ Keeps [o.dst] s t ∧ t.v = s.v := by
  have hc := Bool.toNat_le s.c
  cases o with
  | ld k i d =>
    refine ⟨_, exec_ldr_x (hi.enc k i he.1) (hi.ld k i he.1), ?_⟩
    exact write_rel s d _ _ (hi.val k i he.1)
  | mul d n m => exact ⟨_, rfl, write_rel s d _ _ (by simp only [read_x, BitVec.toNat_mul]; rfl)⟩
  | umulh d n m =>
    refine ⟨_, rfl, write_rel s d _ _ ?_⟩
    rw [BitVec.toNat_ofNat]
    refine Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul ?_)
    exact Nat.mul_lt_mul'' (s.gpr n).isLt (s.gpr m).isLt
  | add d n m => exact ⟨_, rfl, write_rel s d _ _ (by simp only [read_x, BitVec.toNat_add]; rfl)⟩
  | adds d n m => exact ⟨_, rfl, awc_rel s d _ _ _ _ (by simp only [read_x]; rfl)⟩
  | adcs d n m => exact ⟨_, rfl, awc_rel s d _ _ _ _ (by simp only [read_x]; rfl)⟩
  | adc d n m =>
    refine ⟨_, rfl, write_rel s d _ _ ?_⟩
    simp only [read_x, BitVec.toNat_add, Size.bits, BitVec.toNat_ofNat, ofState]
    omega_using [hc]
  | subs d n m =>
    refine ⟨_, rfl, awc_rel s d _ _ _ _ ?_⟩
    simp only [read_x, not_toNat, Bool.toNat_true, ofState]
  | sbcs d n m =>
    refine ⟨_, rfl, awc_rel s d _ _ _ _ ?_⟩
    simp only [read_x, not_toNat, ofState]
  | lsl d n k =>
    refine ⟨_, by simp only [Op.instr, exec, show k < Size.x.bits from he.1, ite_true]; rfl, write_rel s d _ _ ?_⟩
    simp only [read_x, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ofState]
  | lsr d n k =>
    refine ⟨_, by simp only [Op.instr, exec, show k < Size.x.bits from he.1, ite_true]; rfl, write_rel s d _ _ ?_⟩
    simp only [read_x, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ofState]
  | extr d n m k =>
    refine ⟨_, by simp only [Op.instr, exec, show k < Size.x.bits from he.1, ite_true]; rfl, write_rel s d _ _ ?_⟩
    simp only [read_x, Size.bits, BitVec.extractLsb'_toNat, BitVec.toNat_append, Nat.shiftRight_eq_div_pow, ofState]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (s.gpr m).isLt, Nat.shiftLeft_eq]
  | movz d v =>
    refine ⟨_, by simp only [Op.instr, exec, show 16 * 0 < Size.x.bits by decide, ite_true]; rfl, write_rel s d _ _ ?_⟩
    simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Size.bits]
    omega_using []
  | low d n m k =>
    exact ⟨_, rfl, write_rel s d _ _ (by simp only [read_x, BitVec.toNat_and]; rfl)⟩

/-- The registers a sequence writes. -/
def dsts (os : List Op) : List Reg := os.map Op.dst

/-- A sequence on the machine. -/
theorem run_ok {ptr : Nat → Reg × Nat} {use : Nat → Nat → Prop} {inp : Nat → Nat → Nat} :
    ∀ (os : List Op) {s : State}, InOk ptr use inp s → (∀ o ∈ os, Enc ptr use o) →
      WP isa (.block (os.map (Op.instr ptr))) s fun t =>
        ofState t = run inp os (ofState s) ∧ Keeps (dsts os) s t ∧ t.v = s.v
  | [], s, _, _ => WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  | o :: os, s, hi, he => by
    obtain ⟨u, hu, hr, hk, hv⟩ := step_ok hi (he o (List.mem_cons_self ..))
    have ho := (he o (List.mem_cons_self ..)).dst
    refine WP.block_cons_iff.mpr ⟨u, hu, ?_⟩
    have hi' : InOk ptr use inp u := hi.of_same (fun q => hk.gpr _ (by simpa using ho q)) hk.mem hk.rd hk.wr
    refine WP.mono (run_ok os hi' fun o' h => he o' (List.mem_cons_of_mem _ h)) fun t ⟨rt, kt, vt⟩ => ⟨?_, ?_, vt.trans hv⟩
    · rw [rt, hr]; rfl
    · refine (hk.mono ?_).trans (kt.mono ?_)
      · intro r h; rw [List.mem_singleton.mp h]; exact List.mem_cons_self ..
      · intro r h; exact List.mem_cons_of_mem _ h

end VG.Proof.Mont.AArch64.P521
