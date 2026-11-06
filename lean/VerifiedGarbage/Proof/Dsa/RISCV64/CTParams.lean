module

public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBase
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTKey
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTBase
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTKey
meta import VerifiedGarbage.Proof.Dsa.Accepted
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# DSA verification on RISC-V: constant time, the cuts of the domain's and y's checks

The levels `R0`–`R3`, `RK` and `elemOrder` (`CTBase.lean`): the registers at
their cuts (`pins*`), and what correctness says at their branches (`mid*`),
from which the next level's states satisfy its phase (`sem*`): p and q odd,
`p mod q = 1`, g's and y's ranges and orders. After y's check, `body` starts
from `SB`: the key passed the checks, with p, `-p⁻¹ mod 2⁶⁴` and `R² mod p`
in the P space and q in the Q space (`CK`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Bignum (slot)

/-! ## The oddness of p and q -/

theorem P1.step {v : VD} {s t : State} {rs : List Reg} (h : P1 v s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : P1 v t :=
  ⟨h.1.keepM k hm hr, by rw [Lens, hm]; exact h.2.1, h.2.2⟩

/-- A pointer to the key's octets from `o`, `k` of them, then `odd`. -/
theorem odd_P1 {v : VD} {s : State} {ptr : List Instr} {o k : Nat} (hk : 1 ≤ k ∧ k ≤ 1024)
    (hok : o + k ≤ v.kn)
    (hptr : WP isa (.block ptr) s fun t => P1 v t ∧ t.gpr .s7 = off v.key o ∧ t.gpr .s8 = BitVec.ofNat 64 k) :
    WP isa (.block (ptr ++ odd)) s fun t => P1 v t ∧ (t.gpr .a0 = 0 ↔ Spec.Dsa.decodeBE (v.sl o k) % 2 = 1) :=
  WP.block_append (WP.mono hptr fun _ ⟨h', a7, a8⟩ =>
    WP.mono (odd_ok a7 a8 hk.1 hk.2 (h'.1.hk.sub hok).rd) fun _ ⟨⟨a0, m⟩, kt⟩ =>
      ⟨h'.step kt m, by rw [a0, h'.1.bytes hok]⟩)

theorem ptrP_P1 {v : VD} {s : State} (h : P1 v s) :
    WP isa (.block ptrP) s fun t => P1 v t ∧ t.gpr .s7 = off v.key 0 ∧ t.gpr .s8 = BitVec.ofNat 64 v.L.pl :=
  WP.mono (ptrP_ok h.1.scr h.1.ok h.1.regs) fun _ ⟨⟨a7, a8, m⟩, k⟩ => ⟨h.step k m, by rw [off_zero]; exact a7, a8⟩

theorem ptrQ_P1 {v : VD} {s : State} (h : P1 v s) :
    WP isa (.block ptrQ) s fun t => P1 v t ∧ t.gpr .s7 = off v.key v.L.pl ∧ t.gpr .s8 = BitVec.ofNat 64 v.L.ql :=
  WP.mono (ptrQ_ok h.1.scr h.1.ok h.1.regs) fun _ ⟨⟨a7, a8, m⟩, k⟩ => ⟨h.step k m, a7, a8⟩

/-- A block of a pointer to the key's octets, then `odd`: the pointer's
registers from the state the predicate fixes. -/
theorem rel_ptr {Φ : VD → State → Prop} {ptr : List Instr} (o k : VD → Nat)
    (hΦ : ∀ v s, Φ v s → WP isa (.block ptr) s fun t =>
      Fix (fixB v ++ [(.s7, off v.key (o v)), (.s8, BitVec.ofNat 64 (k v))]) t)
    (hpin : Pins Φ [.s6, .s11, .ra])
    {hc₁ : VG.Taint.Hint taint.T} (h₁ : (taint.check (Taint.ofRegs [.s6, .s11, .ra]) (.block ptr) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint taint.T}
    (h₂ : (taint.check (Taint.ofRegs [.s6, .s11, .ra, .s7, .s8]) (.block odd) hc₂).isSome = true) :
    RelCT isa (Two Φ) (Code.seqL [.block (ptr ++ odd)]) fun _ _ => True :=
  VG.Proof.Bignum.RISCV64.RelCT.seqL_single (RelCT.block_append (RelCT.seq
    (two_post (Ψ := fun v t => Fix (fixB v ++ [(.s7, off v.key (o v)), (.s8, BitVec.ofNat 64 (k v))]) t)
      (two_taint [.s6, .s11, .ra] hpin h₁) hΦ)
    (two_taint [.s6, .s11, .ra, .s7, .s8]
      (pins_fix (fun v => fixB v ++ [(.s7, off v.key (o v)), (.s8, BitVec.ofNat 64 (k v))]) (fun _ => rfl)
        fun _ _ h => h) h₂)))

theorem pins_P1 {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → P1 v s) : Pins Φ [.s6, .s11, .ra] :=
  pins_fix fixB (fun _ => rfl) fun v s hs => (h v s hs).1.fixB

section R0

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → P1 v u)
include hΦ

theorem relR0 : RelCT isa (Two (At Φ FR0 0)) (seg FR0 0 1) fun _ _ => True :=
  rel_ptr (fun _ => 0) (fun v => v.L.pl)
    (fun _ _ h => (ptrP_P1 (hΦ _ _ (at_zero_inv h))).mono fun _ ⟨h', a7, a8⟩ => h'.1.fixB.app ⟨a7, a8, trivial⟩)
    (pins_P1 fun _ _ h => hΦ _ _ (at_zero_inv h)) (by taint_decide) (by taint_decide)

end R0

/-- At the branch on p's oddness. -/
abbrev MR0 (v : VD) (u : State) : Prop := P1 v u ∧ (u.gpr .a0 = 0 ↔ v.p % 2 = 1)

section R0

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → P1 v u)
include hΦ

theorem midR0 {v : VD} {s : State} (h : Φ v s) : WP isa (Code.seqL (FR0.take 1)) s (MR0 v) :=
  WP.of_flat (c := .block (ptrP ++ odd)) rfl
    (odd_P1 (by have := (hΦ _ _ h).1.pl; omega) (by have := (hΦ _ _ h).1.kn; omega) (ptrP_P1 (hΦ _ _ h)))

theorem zeroR0 : ∀ v s₁ s₂, At Φ FR0 1 v s₁ → At Φ FR0 1 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => v.p % 2 = 1) fun _ _ h => (midR0 hΦ h).mono fun _ h => h.2

theorem semR1 {v : VD} {u : State} (h : At Φ FR0 1 v u ∧ u.gpr .a0 = 0) : P1 v u ∧ v.p % 2 = 1 :=
  let m := at_sem (fun _ _ h => midR0 hΦ h) h.1
  ⟨m.1, m.2.mp h.2⟩

end R0

section R1

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → P1 v u ∧ v.p % 2 = 1)
include hΦ

theorem relR1 : RelCT isa (Two (At Φ FR1 0)) (seg FR1 0 1) fun _ _ => True :=
  rel_ptr (fun v => v.L.pl) (fun v => v.L.ql)
    (fun _ _ h => (ptrQ_P1 (hΦ _ _ (at_zero_inv h)).1).mono fun _ ⟨h', a7, a8⟩ => h'.1.fixB.app ⟨a7, a8, trivial⟩)
    (pins_P1 fun _ _ h => (hΦ _ _ (at_zero_inv h)).1) (by taint_decide) (by taint_decide)

end R1

/-- At the branch on q's oddness. -/
abbrev MR1 (v : VD) (u : State) : Prop := P1 v u ∧ v.p % 2 = 1 ∧ (u.gpr .a0 = 0 ↔ v.q % 2 = 1)

section R1

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → P1 v u ∧ v.p % 2 = 1)
include hΦ

theorem midR1 {v : VD} {s : State} (h : Φ v s) : WP isa (Code.seqL (FR1.take 1)) s (MR1 v) :=
  WP.of_flat (c := .block (ptrQ ++ odd)) rfl
    ((odd_P1 (by have := (hΦ _ _ h).1.1.ql; omega) (by have := (hΦ _ _ h).1.1.kn; omega) (ptrQ_P1 (hΦ _ _ h).1)).mono
      fun _ ⟨h', a0⟩ => ⟨h', (hΦ _ _ h).2, a0⟩)

theorem zeroR1 : ∀ v s₁ s₂, At Φ FR1 1 v s₁ → At Φ FR1 1 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => v.q % 2 = 1) fun _ _ h => (midR1 hΦ h).mono fun _ h => h.2.2

end R1

/-- `R2`'s phase: p and q odd. -/
abbrev SR2 (v : VD) (u : State) : Prop := P1 v u ∧ v.p % 2 = 1 ∧ v.q % 2 = 1

section R1

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → P1 v u ∧ v.p % 2 = 1)
include hΦ

theorem semR2 {v : VD} {u : State} (h : At Φ FR1 1 v u ∧ u.gpr .a0 = 0) : SR2 v u :=
  let m := at_sem (fun _ _ h => midR1 hΦ h) h.1
  ⟨m.1, m.2.1, m.2.2.mp h.2⟩

end R1

/-! ## `p mod q = 1` -/

section R2

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SR2 v u)
include hΦ

theorem pinsR2_0 : Pins (At Φ FR2 0) [.s6, .s11, .ra] :=
  pins_at_fix fixB (fun _ => rfl) fun _ _ h => ⟨[], _, .block rfl, (hΦ _ _ h).1.1.fixB⟩

theorem pinsR2_2 : Pins (At Φ FR2 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.key v.L.pl), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h => by
    have B := (hΦ _ _ h).1.1
    refine WP.of_flat (c := .seq (.block enterQ) (.block ptrQ)) rfl
      (WP.seq (WP.mono (enterQ_ok B.ok B.scr B.regs) fun _ ⟨⟨iq, m⟩, k⟩ => ?_))
    have B1 := B.keepM k m
    exact WP.mono (ptrQ_ok B1.scr B1.ok B1.regs) fun _ ⟨⟨a7, a8, m'⟩, k'⟩ =>
      ((B1.keepM k' m').fixB.app (fix_envQ (iq.keep k'))).app ⟨a7, a8, trivial⟩

theorem pinsR2_10 : Pins (At Φ FR2 10) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s9, v.key), (.s10, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun v _ h => by
    have B := (hΦ _ _ h).1.1
    refine WP.of_flat (c := .seq setupQ (.block ([.addi .s9 .s11 0] ++ getP .s10))) rfl
      (WP.seq (WP.mono (setupQ_ok B.ok B.scr B.regs (B.hk.take (by have := B.kn; omega))) fun t ⟨⟨iq, _, _, qb⟩, k⟩ => ?_))
    have B1 := B.body k (qb.body B.ok)
    refine WP.block_append (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = v.key ∧ u.mem = t.mem)
      (by brun [B1.regs.s11, BitVec.add_zero]) (by decide) (by rfl)) fun _ ⟨⟨a9, m⟩, k'⟩ => ?_)
    have B2 := B1.keepM k' m
    exact WP.mono (getP_ok B2.scr B2.ok B2.regs .s10) fun _ ⟨⟨a10, m'⟩, k''⟩ =>
      ((B2.keepM k'' m').fixB.app (fix_envQ ((iq.keep k').keep k''))).app
        ⟨(k''.gpr (r := .s9) (by decide)).trans a9, a10, trivial⟩

end R2

/-- q in the Q space's array 0, its word `w` zero. -/
abbrev QF (v : VD) (u : State) : Prop :=
  arrQ u.mem v.L 0 = v.q ∧ word u.mem v.L.Q (slot v.L.wq 0 + 8 * v.L.wq) = 0

/-- At the branch on `p mod q`. -/
abbrev MR2 (v : VD) (u : State) : Prop := SR2 v u ∧ QF v u ∧ (u.gpr .a0 = 0 ↔ v.p % v.q = 1)

section R2

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SR2 v u)
include hΦ

theorem midR2 {v : VD} {s : State} (h : Φ v s) : WP isa (Code.seqL (FR2.take 23)) s (MR2 v) := by
  obtain ⟨⟨B, l, hsz⟩, hp, hq⟩ := hΦ _ _ h
  have bd := VG.Proof.Dsa.supported_bounds hsz
  refine WP.of_flat (c := pModQ) rfl (WP.mono (pModQ_ok B.ok B.scr B.regs (B.hk.take (by have := B.kn; omega))
    (by rw [B.q]; omega)) fun t ⟨⟨_, q0, qtop, a0, qb⟩, k⟩ => ?_)
  have hb := qb.body B.ok
  exact ⟨⟨⟨B.body k hb, by rw [Lens, hb.word (by decide)]; exact l, hsz⟩, hp, hq⟩, ⟨by rw [q0, B.q], qtop⟩,
    by rw [a0, B.p, B.q]⟩

theorem zeroR2 : ∀ v s₁ s₂, At Φ FR2 23 v s₁ → At Φ FR2 23 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => v.p % v.q = 1) fun _ _ h => (midR2 hΦ h).mono fun _ h => h.2.2

end R2

/-- `R3`'s phase: also `p mod q = 1`, with q in the Q space. -/
abbrev SR3 (v : VD) (u : State) : Prop := SR2 v u ∧ v.p % v.q = 1 ∧ QF v u

section R2

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SR2 v u)
include hΦ

theorem semR3 {v : VD} {u : State} (h : At Φ FR2 23 v u ∧ u.gpr .a0 = 0) : SR3 v u :=
  let m := at_sem (fun _ _ h => midR2 hΦ h) h.1
  ⟨m.1, m.2.2.mp h.2, m.2.1⟩

end R2

/-! ## The P space and g -/

/-- In the P space, with p, `-p⁻¹ mod 2⁶⁴` and `R² mod p` in it and q in the
Q space: `Checked`, for the public data. -/
structure CK (v : VD) (u : State) : Prop where
  base : Base v u
  inp : InP u v.L
  p0 : arrP u.mem v.L 0 = v.p
  ptop : word u.mem v.L.S (slot v.L.wp 0 + 8 * v.L.wp) = 0
  inv : ((word u.mem v.L.S (slot v.L.wp 0)).toNat * (u.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  p24 : arrP u.mem v.L 24 = 2 ^ (128 * v.L.wp) % v.p
  q0 : arrQ u.mem v.L 0 = v.q
  qtop : word u.mem v.L.Q (slot v.L.wq 0 + 8 * v.L.wq) = 0
  lens : Lens v v.qb u

theorem CK.checked {v : VD} {u : State} (h : CK v u) : Checked u u v.L v.key v.sig v.d :=
  ⟨h.inp, h.base.scr, h.base.regs, by rw [h.base.p]; exact h.p0, h.ptop, h.inv, by rw [h.base.p]; exact h.p24,
    by rw [h.base.q]; exact h.q0, h.qtop, by rw [h.base.q]; exact h.lens⟩

/-- `CK` through `checkElem`. -/
theorem CK.elem {v : VD} {t u : State} (h : CK v t) {rs : List Reg} (k : Keep rs t u)
    (hrs : ∀ r ∈ regsRegs, r ∉ rs) (ht1 : u.gpr .t1 = t.gpr .t1) (hin : InP u v.L)
    (o : Outside v.L.S (slot v.L.wp 1) (23 * (8 * (v.L.wp + 2))) t.mem u.mem) : CK v u := by
  have c := Checked.elem h.base.ok h.checked k hrs ht1 hin o
  have B := h.base.body k (p_arrays_body h.base.ok o) hrs
  exact ⟨B, hin, by rw [c.p0, h.base.p], c.ptop, c.inv, by rw [c.p24, h.base.p], by rw [c.q0, h.base.q], c.qtop,
    by rw [Lens, c.lens, h.base.q]; rfl⟩

theorem setupP_SR3 {v : VD} {s : State} (h : SR3 v s) :
    WP isa setupP s fun t => CK v t ∧ Keep setupPRegs s t := by
  obtain ⟨⟨⟨B, l, hsz⟩, hp, _⟩, _, q0, qtop⟩ := h
  have bd := VG.Proof.Dsa.supported_bounds hsz
  refine WP.mono (setupP_ok B.ok B.scr B.regs (B.hk.take (by have := B.kn; omega)) (by rw [B.p]; omega) (by rw [B.p]; exact hp))
    fun t ⟨⟨ip, p0, ptop, inv, _, p24, pb⟩, k⟩ => ⟨?_, k⟩
  have hb := pb.body B.ok
  exact ⟨B.body k hb, ip, by rw [p0, B.p], ptop, inv, by rw [p24, B.p], by rw [pb.arrQ B.ok]; exact q0,
    by rw [pb.qtop B.ok]; exact qtop, by rw [Lens, hb.word (by decide)]; exact l⟩

section R3

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SR3 v u)
include hΦ

theorem pinsR3_0 : Pins (At Φ FR3 0) [.s6, .s11, .ra] :=
  pins_at_fix fixB (fun _ => rfl) fun _ _ h => ⟨[], _, .block rfl, (hΦ _ _ h).1.1.1.fixB⟩

theorem pinsR3_2 : Pins (At Φ FR3 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, v.key), (.s8, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun _ _ h => by
    have B := (hΦ _ _ h).1.1.1
    refine WP.of_flat (c := .seq (.block enterP) (.block ptrP)) rfl
      (WP.seq (WP.mono (enterP_ok B.ok B.scr B.regs) fun _ ⟨⟨ip, m⟩, k⟩ => ?_))
    have B1 := B.keepM k m
    exact WP.mono (ptrP_ok B1.scr B1.ok B1.regs) fun _ ⟨⟨a7, a8, m'⟩, k'⟩ =>
      ((B1.keepM k' m').fixB.app (fix_envP (ip.keep k'))).app ⟨a7, a8, trivial⟩

end R3

/-- An element's pointer, in the P space. -/
theorem ptr_CK {v : VD} {s : State} {ptr : List Instr} {o : Nat} (h : CK v s)
    (hptr : WP isa (.block ptr) s fun u =>
        (u.gpr .s7 = off v.key o ∧ u.gpr .s8 = BitVec.ofNat 64 v.L.pl ∧ u.mem = s.mem) ∧ Keep ptrRegs s u) :
    WP isa (.block ptr) s fun t => (CK v t ∧ t.gpr .s7 = off v.key o ∧ t.gpr .s8 = BitVec.ofNat 64 v.L.pl) ∧
      Keep ptrRegs s t :=
  WP.mono hptr fun _ ⟨⟨a7, a8, m⟩, k⟩ =>
    ⟨⟨h.elem k (by decide) (k.gpr (by decide)) (h.inp.keep k) (by rw [m]; exact Outside.refl _ _ _ _), a7, a8⟩, k⟩

theorem fix_CK {v : VD} {s : State} (h : CK v s) : Fix (fixB v ++ envP v) s := h.base.fixB.app (fix_envP h.inp)

section R3

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SR3 v u)
include hΦ

theorem pinsR3_18 : Pins (At Φ FR3 18) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq setupP (.block ptrG)) rfl (WP.seq (WP.mono (setupP_SR3 (hΦ _ _ h)) fun _ ⟨c, _⟩ =>
      (ptr_CK c (ptrG_ok c.base.scr c.base.ok c.base.regs)).mono fun _ ⟨⟨c', a7, a8⟩, _⟩ => (fix_CK c').app ⟨a7, a8, trivial⟩))

end R3

/-- An element of the key, octets from `o`: in range. -/
abbrev ERange (v : VD) (o : Nat) : Prop :=
  1 < Spec.Dsa.decodeBE (v.sl o v.L.pl) ∧ Spec.Dsa.decodeBE (v.sl o v.L.pl) < v.p

/-- And of order q. -/
abbrev EOk (v : VD) (o : Nat) : Prop := ERange v o ∧ Spec.Dsa.decodeBE (v.sl o v.L.pl) ^ v.q % v.p = 1

/-- At the branch on an element's range: `elemOrder`'s phase. -/
abbrev ME (v : VD) (o : Nat) (u : State) : Prop := Base v u ∧ InP u v.L ∧ (u.gpr .a0 = 0 ↔ ERange v o)

/-- An element's pointer, its load and its range. -/
theorem range_CK {v : VD} {s : State} {o : Nat} (h : CK v s) (ho : o + v.L.pl ≤ v.kn)
    (h7 : s.gpr .s7 = off v.key o) (h8 : s.gpr .s8 = BitVec.ofNat 64 v.L.pl) :
    WP isa (.seq (loadArr 4) elemRange) s (ME v o) := by
  have hL := h.base.ok
  have hbuf := hL.buf_end
  have hqZ : v.L.qOff ≤ v.L.Z := by simp only [Lay.bOff] at hbuf; omega
  have e0 := Lay.slot_eq v.L.wp 0; have e1 := Lay.slot_eq v.L.wp 1; have e4 := Lay.slot_eq v.L.wp 4
  have hw := hL.wp_ge
  have hnw := hL.nowrap
  have en := h.inp.env
  have he := h.base.hk.sub ho
  refine WP.seq (WP.mono (loadArr_ok en (j := 4) (N := off v.key o) (by decide)
    (by rw [h7]; exact (BitVec.add_zero _).symm) h8 (by have := h.base.pl; omega) (by have := hL.wp_eq; omega)
    he.rd (fun i hi x hx => he.sep i hi x (Nat.lt_of_lt_of_le hx hqZ))) fun s₁ ⟨⟨v4, top4, o1, a7⟩, k1⟩ => ?_)
  have e1' : Env s₁ v.L.S v.L.qOff v.L.wp :=
    ⟨en.hs.congr k1.2.2, a7, (k1.gpr (by decide)).trans en.s5, (k1.gpr (by decide)).trans en.t0, en.w2, en.w48,
      en.hZ⟩
  have A0 : wordsVal s₁.mem v.L.S (slot v.L.wp 0) v.L.wp = v.p := by
    rw [o1.wordsVal (by omega) (by omega_arith)]; exact h.p0
  refine WP.mono (elemRange_ok e1' top4) fun t ⟨⟨r0, _, o2, e2⟩, k2⟩ => ?_
  rw [v4, A0, h.base.bytes ho] at r0
  have k12 := k1.trans k2
  exact ⟨h.base.body k12 (p_arrays_body hL (p_elem2 o1 o2)), ⟨e2, (k12.gpr (by decide)).trans h.inp.s6⟩, r0⟩

/-- An element's pointer and `checkElem`. -/
theorem elem_CK {v : VD} {s : State} {o : Nat} (h : CK v s) (hsz : SzOk v) (hpo : v.p % 2 = 1)
    (ho : o + v.L.pl ≤ v.kn)
    (h7 : s.gpr .s7 = off v.key o) (h8 : s.gpr .s8 = BitVec.ofNat 64 v.L.pl) :
    WP isa checkElem s fun t => CK v t ∧ (t.gpr .a0 = 0 ↔ EOk v o) := by
  have bd := VG.Proof.Dsa.supported_bounds hsz
  refine WP.mono (checkElem_ok h.base.ok h.base.scr h.base.regs h.inp (h.base.hk.take (by have := h.base.kn; omega))
    (h.base.hk.sub ho) h7 h8 h.p0 (by omega) hpo h.inv h.p24) fun t ⟨⟨ip, a0, o', t1⟩, k⟩ =>
      ⟨h.elem k (by decide) t1 ip o', ?_⟩
  rw [a0, h.base.bytes ho, h.base.q, EOk, ERange, and_assoc]

section R3

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SR3 v u)
include hΦ

/-- At the branch on g's range. -/
theorem midEg {v : VD} {s : State} (h : Φ v s) :
    WP isa (Code.seqL (FR3.take 45)) s (ME v (v.L.pl + v.L.ql)) :=
  WP.of_flat (c := .seq setupP (.seq (.block ptrG) (.seq (loadArr 4) elemRange))) rfl
    (WP.seq (WP.mono (setupP_SR3 (hΦ _ _ h)) fun _ ⟨c, _⟩ => WP.seq ((ptr_CK c (ptrG_ok c.base.scr c.base.ok c.base.regs)).mono
      fun _ ⟨⟨c', a7, a8⟩, _⟩ => range_CK c' (by have := c'.base.kn; omega) a7 a8)))

theorem zeroEg : ∀ v s₁ s₂, At Φ FR3 45 v s₁ → At Φ FR3 45 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => ERange v (v.L.pl + v.L.ql)) fun _ _ h => (midEg hΦ h).mono fun _ h => h.2.2

theorem semEg {v : VD} {u : State} (h : At Φ FR3 45 v u ∧ u.gpr .a0 = 0) : Base v u ∧ InP u v.L :=
  let m := at_sem (fun _ _ h => midEg hΦ h) h.1
  ⟨m.1, m.2.1⟩

end R3

/-- The domain passed the checks. -/
abbrev KM (v : VD) : Prop := SzOk v ∧ v.p % 2 = 1 ∧ v.q % 2 = 1 ∧ v.p % v.q = 1

/-- At the branch on g's check. -/
abbrev MR3 (v : VD) (u : State) : Prop := CK v u ∧ KM v ∧ (u.gpr .a0 = 0 ↔ EOk v (v.L.pl + v.L.ql))

section R3

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SR3 v u)
include hΦ

theorem midR3 {v : VD} {s : State} (h : Φ v s) : WP isa (Code.seqL (FR3.take 46)) s (MR3 v) := by
  obtain ⟨⟨⟨B, l, hsz⟩, hp, hq⟩, pm, qf⟩ := hΦ _ _ h
  exact WP.of_flat (c := .seq setupP (.seq (.block ptrG) checkElem)) rfl
    (WP.seq (WP.mono (setupP_SR3 (hΦ _ _ h)) fun _ ⟨c, _⟩ => WP.seq ((ptr_CK c (ptrG_ok c.base.scr c.base.ok c.base.regs)).mono
      fun _ ⟨⟨c', a7, a8⟩, _⟩ => (elem_CK c' hsz hp (by have := c'.base.kn; omega) a7 a8).mono fun _ ⟨c'', a0⟩ =>
        ⟨c'', ⟨hsz, hp, hq, pm⟩, a0⟩)))

theorem zeroR3 : ∀ v s₁ s₂, At Φ FR3 46 v s₁ → At Φ FR3 46 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => EOk v (v.L.pl + v.L.ql)) fun _ _ h => (midR3 hΦ h).mono fun _ h => h.2.2

end R3

/-- `RK`'s phase: the domain passed the checks. -/
abbrev SK (v : VD) (u : State) : Prop := CK v u ∧ KM v ∧ EOk v (v.L.pl + v.L.ql) ∧ KY v

section R3

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SR3 v u)
include hΦ

theorem semK (hY : ∀ v u, Φ v u → KY v) {v : VD} {u : State} (h : At Φ FR3 46 v u ∧ u.gpr .a0 = 0) :
    SK v u :=
  let m := at_sem (fun _ _ h => midR3 hΦ h) h.1
  ⟨m.1, m.2.1, m.2.2.mp h.2, at_pure hY h.1⟩

end R3

/-! ## y -/

section K

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SK v u)
include hΦ

theorem pinsK_0 : Pins (At Φ FK 0) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envP v) (fun _ => rfl) fun _ _ h => ⟨[], _, .block rfl, fix_CK (hΦ _ _ h).1⟩

theorem pinsK_1 : Pins (At Φ FK 1) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (2 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun _ _ h => WP.of_flat (c := .block ptrY) rfl
      ((ptr_CK (hΦ _ _ h).1 (ptrY_ok (hΦ _ _ h).1.base.scr (hΦ _ _ h).1.base.ok (hΦ _ _ h).1.base.regs)).mono fun _ ⟨⟨c', a7, a8⟩, _⟩ => (fix_CK c').app ⟨a7, a8, trivial⟩)

/-- At the branch on y's range. -/
theorem midEy {v : VD} {s : State} (h : Φ v s) :
    WP isa (Code.seqL (FK.take 28)) s (ME v (2 * v.L.pl + v.L.ql)) :=
  WP.of_flat (c := .seq (.block ptrY) (.seq (loadArr 4) elemRange)) rfl
    (WP.seq ((ptr_CK (hΦ _ _ h).1 (ptrY_ok (hΦ _ _ h).1.base.scr (hΦ _ _ h).1.base.ok (hΦ _ _ h).1.base.regs)).mono fun _ ⟨⟨c', a7, a8⟩, _⟩ =>
      range_CK c' (by have := (hΦ _ _ h).2.2.2; omega) a7 a8))

theorem zeroEy : ∀ v s₁ s₂, At Φ FK 28 v s₁ → At Φ FK 28 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => ERange v (2 * v.L.pl + v.L.ql)) fun _ _ h => (midEy hΦ h).mono fun _ h => h.2.2

theorem semEy {v : VD} {u : State} (h : At Φ FK 28 v u ∧ u.gpr .a0 = 0) : Base v u ∧ InP u v.L :=
  let m := at_sem (fun _ _ h => midEy hΦ h) h.1
  ⟨m.1, m.2.1⟩

end K

/-- At the branch on y's check. -/
abbrev MK (v : VD) (u : State) : Prop := SK v u ∧ (u.gpr .a0 = 0 ↔ EOk v (2 * v.L.pl + v.L.ql))

section K

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SK v u)
include hΦ

theorem midK {v : VD} {s : State} (h : Φ v s) : WP isa (Code.seqL (FK.take 29)) s (MK v) := by
  obtain ⟨c, km, eg, ky⟩ := hΦ _ _ h
  exact WP.of_flat (c := .seq (.block ptrY) checkElem) rfl
    (WP.seq ((ptr_CK c (ptrY_ok c.base.scr c.base.ok c.base.regs)).mono fun _ ⟨⟨c', a7, a8⟩, _⟩ =>
      (elem_CK c' km.1 km.2.1 (by omega) a7 a8).mono fun _ ⟨c'', a0⟩ => ⟨⟨c'', km, eg, ky⟩, a0⟩))

theorem zeroK : ∀ v s₁ s₂, At Φ FK 29 v s₁ → At Φ FK 29 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => EOk v (2 * v.L.pl + v.L.ql)) fun _ _ h => (midK hΦ h).mono fun _ h => h.2

end K

/-- The public data name a signature and a digest, as verification's do. -/
abbrev VB (v : VD) : Prop := v.full = true ∧ v.sgl = 2 * v.L.ql

/-- `body`'s phase: the key passed the checks. -/
abbrev SB (v : VD) (u : State) : Prop := SK v u ∧ EOk v (2 * v.L.pl + v.L.ql) ∧ VB v

section K

variable {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → SK v u)
include hΦ

end K

/-! ## `elemOrder` -/

/-- `elemOrder`'s cuts, from a level whose states are in the P space. -/
theorem pinsE_0 {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → Base v u ∧ InP u v.L) :
    Pins (At Φ FE 0) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envP v) (fun _ => rfl) fun _ _ h =>
    ⟨[], _, .block rfl, (hΦ _ _ h).1.fixB.app (fix_envP (hΦ _ _ h).2)⟩

theorem pinsE_3 {Φ : VD → State → Prop} (hΦ : ∀ v u, Φ v u → Base v u ∧ InP u v.L) :
    Pins (At Φ FE 3) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s9, off (off v.key v.L.pl) 0), (.s10, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun v _ h => by
    obtain ⟨B, ip⟩ := hΦ _ _ h
    have hL := B.ok
    have hw := hL.wp_ge
    have e0 := Lay.slot_eq v.L.wp 0; have e1 := Lay.slot_eq v.L.wp 1; have e24 := Lay.slot_eq v.L.wp 24
    have e28 := Lay.slot_eq v.L.wp 28
    refine WP.of_flat (c := .seq (copy 1 24) (.block (ptrQ ++ [.addi .s9 .s7 0, .addi .s10 .s8 0]))) rfl
      (WP.seq (WP.mono (copy_ok ip.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
        fun _ ⟨⟨_, o1⟩, k1⟩ => ?_))
    have B1 := B.body k1 (Body.ofP hL o1 (by omega) (by simp only [Lay.qOff]; omega))
    refine WP.block_append (WP.mono (ptrQ_ok B1.scr hL B1.regs) fun t ⟨⟨a7, a8, m2⟩, k2⟩ =>
      WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off (off v.key v.L.pl) 0 ∧
        u.gpr .s10 = BitVec.ofNat 64 v.L.ql ∧ u.mem = t.mem) (by brun [a7, a8, BitVec.add_zero]) (by decide) (by rfl))
      fun _ ⟨⟨b9, b10, m3⟩, k3⟩ => ?_)
    have B3 := (B1.keepM k2 m2).keepM k3 m3
    exact (B3.fixB.app (fix_envP ((ip.keep k1).keep k2 |>.keep k3))).app ⟨b9, b10, trivial⟩

/-- `elemOrder`, from a level whose states are in the P space. -/
theorem eo_rel {Φ : VD → State → Prop} (hrun : ∀ v s, Φ v s → WP isa (Code.seqL FE) s fun _ => True)
    (hΦ : ∀ v u, Φ v u → Base v u ∧ InP u v.L) : RelCT isa (Two Φ) elemOrder fun _ _ => True :=
  chain_start (chain_cons hrun (m := 3) (by decide) (two_taint _ (pinsE_0 hΦ) (by taint_decide))
    (two_taint _ (pinsE_3 hΦ) (by taint_decide)))

end VG.Proof.Dsa.RISCV64.CT
