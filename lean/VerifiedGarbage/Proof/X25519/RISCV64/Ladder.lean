module

public import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
import VerifiedGarbage.Proof.X25519.RISCV64.Cswap
import VerifiedGarbage.Proof.X25519.RISCV64.AddSub

/-! ### `X25519.RISCV64.Slots`, which this module and modules that import it used -/

section

/-!
# X25519 on RISCV64: the field elements the working space holds

`SlotsOk m B qs v`: each slot `q` of `qs` holds the element `v q`. A write of
one slot keeps the others' elements (`slots_after`, with `upd`), for slots
whose separation from the output is decided on their offsets (`Sep1`), and
writing only the field area `[0, ACC + 64)` of the working space (`FA`).
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64
open VG.Spec.X25519 (P Fe)
open VG.Proof.X25519 (toFe toFe_mul toFe_add toFe_sub)

/-- Each slot `q` of `qs` holds `v q`. -/
def SlotsOk (m : Mem) (B : Addr) (qs : List Nat) (v : Nat → Fe) : Prop :=
  ∀ q ∈ qs, FS m B q = v q

theorem SlotsOk.mono {m : Mem} {B : Addr} {qs qs' : List Nat} {v : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs', q ∈ qs) : SlotsOk m B qs' v := fun q hq => h q (hs q hq)

theorem SlotsOk.congr {m : Mem} {B : Addr} {qs : List Nat} {v w : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs, v q = w q) : SlotsOk m B qs w := fun q hq => (h q hq).trans (hs q hq)

/-- `v` with the element `x` at `o`. -/
def upd (v : Nat → Fe) (o : Nat) (x : Fe) (q : Nat) : Fe := if q = o then x else v q

theorem upd_self (v : Nat → Fe) (o : Nat) (x : Fe) : upd v o x o = x := by simp [upd]

theorem upd_of_ne (v : Nat → Fe) {o q : Nat} (x : Fe) (h : q ≠ o) : upd v o x q = v q := by simp [upd, h]

/-- `o` is a multiple of 4, and every slot of `qs` is `o` or separate from
it, below `ACC`, and a multiple of 4 (for the alignment of words). -/
def Sep1 (o : Nat) (qs : List Nat) : Bool :=
  o % 4 == 0 && qs.all fun q => (q == o || q + 32 ≤ o || o + 32 ≤ q) && q + 32 ≤ ACC && q % 4 == 0

theorem sep1_get {o : Nat} {qs : List Nat} (h : Sep1 o qs = true) {q : Nat} (hq : q ∈ qs) :
    (q = o ∨ q + 32 ≤ o ∨ o + 32 ≤ q) ∧ q + 32 ≤ ACC ∧ q % 4 = 0 := by
  simp only [Sep1, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 q hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1.elim (fun h => h.elim .inl (fun h => .inr (.inl h))) (fun h => .inr (.inr h)),
    this.1.2, this.2⟩

/-- The field area `[0, ACC + 64)` of the working space: the elements and
the product at `ACC`. -/
abbrev FA (b : Addr) : Region := ⟨b, ACC + 64⟩

section
variable {b : Addr}

/-- The slots of `qs` other than `o` after a write of `o` (and `ACC`). -/
theorem slots_after {o : Nat} {qs : List Nat} (hq : Sep1 o qs = true)
    (ho : o + 32 ≤ ACC) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩] m m')
    {v : Nat → Fe} (hS : SlotsOk m b qs v) {q : Nat} (hq' : q ∈ qs) (hqo : q ≠ o) :
    FS m' b q = v q := by
  obtain ⟨h1, h3, -⟩ := sep1_get hq hq'
  have hA := ACC_eq
  have e : ∀ k < 8, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [hqo, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, ho])
      · exact Offset.disjoint _ (.inl (by omega_using [h3, hk])) (by omega_using [hA, h3, hk]) (by omega_using [hA])
  rw [FS, V, val32_congr e]; exact hS q hq'

theorem frame_FA {o : Nat} (ho : o + 32 ≤ ACC) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩] m m') :
    Frame [FA b] m m' := by
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_using [ho])

theorem frame_o {o : Nat} {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] m m') :
    Frame [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩] m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

/-- The elements after swapping `x` and `y` if `sw = 1`. -/
def swapV (x y sw : Nat) (v : Nat → Fe) (q : Nat) : Fe :=
  if q = x then sel sw (v x) (v y) else if q = y then sel sw (v y) (v x) else v q

end

end VG.Proof.X25519.RISCV64

end

end

/-!
# X25519 on RISCV64: the ladder's operations

One iteration of the ladder as field operations on the slots (`ladOps`,
`runOps`), whose values are `ladderStep`'s (`ladOps_vals`), from the elements
`x1, x2, z2, x3, z3, a24` (`LQ`, `ladV`), and the scalar's bits in the
working space (`Bits`).
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64
open VG.Spec.X25519 (P Fe Ladder ladderStep cswap a24)
open VG.Proof.X25519 (toFe ladderAfter ladderAfter_step ladderStep_eq bit bit_le ladderAfter_swap_le)

/-! ## Sequences of field operations -/

/-- A field operation: `o = x · y`, `x + y` or `x - y`. -/
inductive FOp
  | mul (o x y : Nat)
  | add (o x y : Nat)
  | sub (o x y : Nat)

def FOp.out : FOp → Nat
  | .mul o _ _ | .add o _ _ | .sub o _ _ => o

def FOp.x : FOp → Nat
  | .mul _ x _ | .add _ x _ | .sub _ x _ => x

def FOp.y : FOp → Nat
  | .mul _ _ y | .add _ _ y | .sub _ _ y => y

def FOp.val : FOp → (Nat → Fe) → Fe
  | .mul _ x y, v => v x * v y
  | .add _ x y, v => v x + v y
  | .sub _ x y, v => v x - v y

/-- The elements after the operations. -/
def runOps : List FOp → (Nat → Fe) → Nat → Fe
  | [], v => v
  | op :: ops, v => runOps ops (upd v op.out (op.val v))

/-- The slots known after the operations. -/
def outsQ : List FOp → List Nat → List Nat
  | [], qs => qs
  | op :: ops, qs => outsQ ops (op.out :: qs)

/-! ## One iteration -/

/-- The field operations of an iteration, after the swaps. -/
def ladOps : List FOp :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB, .add C X3 Z3, .sub D X3 Z3,
    .mul DA D A, .mul CB C B, .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3,
    .mul Z3 X1 Z3, .mul X2 AA BB, .mul Z2 A24 E, .add Z2 AA Z2, .mul Z2 E Z2]

/-- The slots the ladder's state lives in. -/
def LQ : List Nat := [X1, X2, Z2, X3, Z3, A24]

/-- The elements of the ladder's state `st`, and `x1` and `a24`. -/
def ladV (x1 : Fe) (st : Ladder) (q : Nat) : Fe :=
  if q = X1 then x1 else if q = X2 then st.x2 else if q = Z2 then st.z2 else if q = X3 then st.x3
  else if q = Z3 then st.z3 else a24

theorem cswap_fst (sw : Nat) (x y : Fe) : (Spec.X25519.cswap sw x y).1 = sel sw x y := by
  unfold Spec.X25519.cswap sel; split <;> rfl

theorem cswap_snd (sw : Nat) (x y : Fe) : (Spec.X25519.cswap sw x y).2 = sel sw y x := by
  unfold Spec.X25519.cswap sel; split <;> rfl

/-- The elements after an iteration. -/
theorem ladOps_vals (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) :
    ∀ q ∈ LQ, runOps ladOps (swapV Z2 Z3 (st.swap ^^^ bit k t) (swapV X2 X3 (st.swap ^^^ bit k t)
      (ladV x1 st))) q = ladV x1 (ladderStep k x1 st t) q := by
  intro q hq
  rw [ladderStep_eq]
  simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ladOps, runOps, FOp.out, FOp.val, upd, swapV, ladV, cswap_fst, cswap_snd, X1, X2, Z2, X3,
      Z3, A, B, C, D, AA, BB, E, DA, CB, A24, Nat.reduceEqDiff, ↓reduceIte]

theorem ofNat_xor {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 y = BitVec.ofNat 64 (x ^^^ y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_imm hx, toNat_imm hy, toNat_imm (Nat.xor_lt_two_pow hx hy)]

theorem xor_le_one {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

/-- The bits of the scalar in `BITS`. -/
def Bits (b : Addr) (k : Nat) (m : Mem) : Prop :=
  ∀ t < 255, m (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (bit k t)

end VG.Proof.X25519.RISCV64
