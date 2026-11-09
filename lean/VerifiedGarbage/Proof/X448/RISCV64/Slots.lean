module
public import VerifiedGarbage.Proof.X448.RISCV64.Field
import VerifiedGarbage.Proof.X25519.RISCV64.Cswap

import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.X448.RISCV64.Cswap
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
import VerifiedGarbage.Proof.X25519.RISCV64.Pass

/-!
# X448 on RISCV64: the field elements the working space holds

`SlotsOk m B qs v`: each slot `q` of `qs` holds the element `v q`. Updates
of `v` (`upd`, `swapV`), for slots whose separation from the output is
decided on their offsets (`Sep1`), and writes only to the field area
`[0, ACC + 112)` of the working space (`FA`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Spec.X448 (P Fe)
open VG.Proof.X448 (toFe toFe_mul toFe_add toFe_sub)

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
  o % 4 == 0 && qs.all fun q => (q == o || q + 56 ≤ o || o + 56 ≤ q) && q + 56 ≤ ACC && q % 4 == 0

theorem sep1_o {o : Nat} {qs : List Nat} (h : Sep1 o qs = true) : o % 4 = 0 := by
  simp only [Sep1, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem sep1_get {o : Nat} {qs : List Nat} (h : Sep1 o qs = true) {q : Nat} (hq : q ∈ qs) :
    (q = o ∨ q + 56 ≤ o ∨ o + 56 ≤ q) ∧ q + 56 ≤ ACC ∧ q % 4 = 0 := by
  simp only [Sep1, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 q hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1.elim (fun h => h.elim .inl (fun h => .inr (.inl h))) (fun h => .inr (.inr h)),
    this.1.2, this.2⟩

/-- The field area `[0, ACC + 112)` of the working space: the elements and
the product at `ACC`. -/
abbrev FA (b : Addr) : Region := ⟨b, ACC + 112⟩

section
variable {b : Addr}

/-- The slots of `qs` other than `o` after a write of `o` (and `ACC`). -/
theorem slots_after {o : Nat} {qs : List Nat} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] m m')
    {v : Nat → Fe} (hS : SlotsOk m b qs v) {q : Nat} (hq' : q ∈ qs) (hqo : q ≠ o) :
    FS m' b q = v q := by
  obtain ⟨h1, h3, -⟩ := sep1_get hq hq'
  have hA := ACC_eq
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [hqo, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, ho])
      · exact Offset.disjoint _ (.inl (by omega_using [h3, hk])) (by omega_using [hA, h3, hk]) (by omega_using [hA])
  rw [FS, V, val32_congr e]; exact hS q hq'

theorem frame_FA {o : Nat} (ho : o + 56 ≤ ACC) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] m m') :
    Frame [FA b] m m' := by
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_using [ho])

theorem frame_o {o : Nat} {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] m m') :
    Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

/-- The elements after swapping `x` and `y` if `sw = 1`. -/
def swapV (x y sw : Nat) (v : Nat → Fe) (q : Nat) : Fe :=
  if q = x then sel sw (v x) (v y) else if q = y then sel sw (v y) (v x) else v q

end

end VG.Proof.X448.RISCV64
