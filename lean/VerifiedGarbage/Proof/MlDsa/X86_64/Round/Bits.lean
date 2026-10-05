import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Round
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlDsa.Round.Ones
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Round.Arith`. -/
section

/-!
# ML-DSA on x86-64: what the rounding code computes

The values the code of `Impl/MlDsa/X86_64/Round/Round.lean` leaves in its
registers, as the symbolic execution of a block writes them (`condAddV`,
`hbRawV`, `hbV`), and what they are as natural numbers (`condAddV_toNat`,
`hbRawV_toNat`, `hbV_toNat`), from the target-independent lemmas of
`Proof/MlDsa/Round/Decompose.lean`.
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Spec.MlDsa (q gamma2s)
open VG.Proof.MlDsa.Round (hbF q_eq mem_gamma2s hbF_le hbF_eq)

/-- A 32-bit immediate below `2³¹`, sign-extended. -/
theorem sx_toNat {k : BitVec 32} (h : k.toNat < 2 ^ 31) : (BitVec.signExtend 64 k).toNat = k.toNat := by
  have : k.msb = false := by rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
  rw [BitVec.toNat_signExtend, this, BitVec.toNat_setWidth]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  omega

theorem sx_ofNat_toNat {k : Nat} (h : k < 2 ^ 31) : (BitVec.signExtend 64 (BitVec.ofNat 32 k)).toNat = k := by
  rw [VG.Proof.MlDsa.X86_64.Round.sx_toNat (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega

theorem setWidth64_toNat (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]; have := x.isLt; omega

/-! ## Conditional addition -/

/-- What `condAdd r x m k` leaves in `r`: `r - x`, plus `k` if it borrows. -/
def condAddV (r x : BitVec 64) (k : BitVec 32) : BitVec 64 :=
  r - x + (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (r.toNat < x.toNat))) &&& BitVec.signExtend 64 k)

theorem condAddV_toNat {r x : BitVec 64} {k : BitVec 32} (hk : k.toNat < 2 ^ 31) (hx : x.toNat ≤ r.toNat + k.toNat) :
    (VG.Proof.MlDsa.X86_64.Round.condAddV r x k).toNat = if r.toNat < x.toNat then r.toNat + k.toNat - x.toNat else r.toNat - x.toNat := by
  have hs := VG.Proof.MlDsa.X86_64.Round.sx_toNat hk
  have hr := r.isLt
  have hx' := x.isLt
  unfold VG.Proof.MlDsa.X86_64.Round.condAddV
  by_cases h : r.toNat < x.toNat
  · rw [decide_eq_true h, ite_eq_left_of_eq_true _ _ (eq_true h)]
    have e : (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 64 := by decide
    rw [e, BitVec.allOnes_and, BitVec.toNat_add, BitVec.toNat_sub, hs]
    omega
  · rw [decide_eq_false h, ite_eq_right_of_eq_false _ _ (eq_false h)]
    have e : (0#64 - BitVec.setWidth 64 (BitVec.ofBool false)) = 0#64 := by decide
    rw [e, BitVec.zero_and, BitVec.add_zero, BitVec.toNat_sub]
    omega

/-- `condAdd` of an immediate `k` and mask `k`: the conditional subtraction of `k`. -/
theorem condAddV_imm_toNat {r : BitVec 64} {k : Nat} (hk : k < 2 ^ 31) (hr : r.toNat < 2 * k) :
    (VG.Proof.MlDsa.X86_64.Round.condAddV r (BitVec.signExtend 64 (BitVec.ofNat 32 k)) (BitVec.ofNat 32 k)).toNat = r.toNat % k := by
  have e := VG.Proof.MlDsa.X86_64.Round.sx_ofNat_toNat hk
  have e' : (BitVec.ofNat 32 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  rw [VG.Proof.MlDsa.X86_64.Round.condAddV_toNat (by omega) (by omega), e, e']
  split
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## `Decompose` -/

/-- What `hbRaw g` leaves in `rax` from `a`. -/
def hbRawV (g : Nat) (a : BitVec 64) : BitVec 64 :=
  (BitVec.ofNat 64 (((a + BitVec.signExtend 64 (127 : BitVec 32)) >>> 7).toNat *
      (BitVec.setWidth 64 (BitVec.ofNat 32 (dMul g))).toNat) +
    BitVec.signExtend 64 (BitVec.ofNat 32 (dAdd g))) >>> dShift g

theorem dMul_eq (g : Nat) : dMul g = Proof.MlDsa.Round.hbMul g := rfl
theorem dAdd_eq (g : Nat) : dAdd g = Proof.MlDsa.Round.hbAdd g := rfl
theorem dShift_eq (g : Nat) : dShift g = Proof.MlDsa.Round.hbShift g := rfl

theorem dMod_eq {g : Nat} (h : g ∈ gamma2s) : dMod g = Proof.MlDsa.Round.hbM g := by
  rcases mem_gamma2s h with rfl | rfl <;> rfl

theorem hbRawV_toNat {g : Nat} (h : g ∈ gamma2s) {a : BitVec 64} (ha : a.toNat < VG.Spec.MlDsa.q) :
    (VG.Proof.MlDsa.X86_64.Round.hbRawV g a).toNat = hbF g a.toNat := by
  rw [VG.Proof.MlDsa.Round.q_eq] at ha
  have hM : dMul g ≤ 11275 := by unfold dMul; split <;> decide
  have hA : dAdd g ≤ 2 ^ 23 := by unfold dAdd; split <;> decide
  have e1 : (a + BitVec.signExtend 64 (127 : BitVec 32)).toNat = a.toNat + 127 := by
    rw [BitVec.toNat_add, show (BitVec.signExtend 64 (127 : BitVec 32)).toNat = 127 by decide]; omega
  have e2 : ((a + BitVec.signExtend 64 (127 : BitVec 32)) >>> 7).toNat = (a.toNat + 127) / 128 := by
    rw [BitVec.toNat_ushiftRight, e1, Nat.shiftRight_eq_div_pow]
  have e3 : (BitVec.setWidth 64 (BitVec.ofNat 32 (dMul g))).toNat = dMul g := by
    rw [VG.Proof.MlDsa.X86_64.Round.setWidth64_toNat, BitVec.toNat_ofNat]; omega
  have hp : (a.toNat + 127) / 128 * dMul g ≤ 65473 * 11275 :=
    Nat.mul_le_mul (by omega) hM
  have e4 : (BitVec.ofNat 64 (((a + BitVec.signExtend 64 (127 : BitVec 32)) >>> 7).toNat *
      (BitVec.setWidth 64 (BitVec.ofNat 32 (dMul g))).toNat) +
      BitVec.signExtend 64 (BitVec.ofNat 32 (dAdd g))).toNat = (a.toNat + 127) / 128 * dMul g + dAdd g := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, e2, e3, VG.Proof.MlDsa.X86_64.Round.sx_ofNat_toNat (by omega)]
    omega
  unfold VG.Proof.MlDsa.X86_64.Round.hbRawV
  rw [BitVec.toNat_ushiftRight (BitVec.ofNat 64 _ + _), e4, Nat.shiftRight_eq_div_pow, hbF_eq h (by rw [VG.Proof.MlDsa.Round.q_eq]; exact ha)]
  rfl

/-- What `hb g` leaves in `rax` from `a`. -/
def hbV (g : Nat) (a : BitVec 64) : BitVec 64 :=
  VG.Proof.MlDsa.X86_64.Round.condAddV (VG.Proof.MlDsa.X86_64.Round.hbRawV g a) (BitVec.signExtend 64 (BitVec.ofNat 32 (dMod g))) (BitVec.ofNat 32 (dMod g))

theorem hbV_toNat {g : Nat} (h : g ∈ gamma2s) {a : BitVec 64} (ha : a.toNat < VG.Spec.MlDsa.q) :
    (VG.Proof.MlDsa.X86_64.Round.hbV g a).toNat = hbF g a.toNat % Proof.MlDsa.Round.hbM g := by
  have hM : dMod g ≤ 44 ∧ 16 ≤ dMod g := by unfold dMod; split <;> decide
  have hf := hbF_le h ha
  rw [← VG.Proof.MlDsa.X86_64.Round.dMod_eq h] at hf ⊢
  rw [VG.Proof.MlDsa.X86_64.Round.hbV, VG.Proof.MlDsa.X86_64.Round.condAddV_imm_toNat (by omega) (by rw [VG.Proof.MlDsa.X86_64.Round.hbRawV_toNat h ha]; omega), VG.Proof.MlDsa.X86_64.Round.hbRawV_toNat h ha]

end VG.Proof.MlDsa.X86_64.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Round.Loop`. -/
section

/-!
# ML-DSA on x86-64: the loop over the coefficients

`mapLoop body` runs `body` for `rcx` = 256 down to 1, and iteration `i` (from 0)
handles coefficient `255 - i` at `[p + 4·rcx - 4]` (`cfAddr`) of each
polynomial `p`. `loop_ok` proves it once for every function: from a body that
writes, to coefficient `255 - i` of each output polynomial (in a register of
`outs`), the value `V o (255 - i)` and keeps an invariant `J` of its other
registers, the loop writes every coefficient of each output. The inputs
(registers `ins`) are never written, so the body reads the coefficients of the
initial memory (`Inv.read`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (coeffAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep wp_countdown setReg_gpr setReg_mem ofNat64_pred)

/-! ## Addresses -/

/-- `p + 4c - 4`, the address of `cf p` when `rcx = c`. -/
def cfAddr (p c : Addr) : Addr := p + c * BitVec.ofNat 64 4 + BitVec.ofInt 64 (-4)

theorem ea_cf (s : State) (p : Reg) : s.ea (cf p) = VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr p) (s.gpr .rcx) := rfl

theorem cfAddr_eq (p : Addr) (j : Nat) :
    VG.Proof.MlDsa.X86_64.Round.cfAddr p (BitVec.ofNat 64 (j + 1)) = VG.Proof.MlDsa.Round.coeffAddr p j := by
  unfold VG.Proof.MlDsa.X86_64.Round.cfAddr VG.Proof.MlDsa.Round.coeffAddr
  rw [BitVec.add_assoc]
  refine congrArg (p + ·) ?_
  have e : BitVec.ofInt 64 (-4) = -BitVec.ofNat 64 4 := by decide
  rw [e, ← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## The writes of an iteration -/

/-- Stores of `v` at `a` for each `(a, v)`, in order. -/
def writes (m : Mem) (ps : List (Addr × BitVec 32)) : Mem := ps.foldl (fun m p => m.writeW p.1 p.2) m

theorem writes_cons (m : Mem) (p : Addr × BitVec 32) (ps : List (Addr × BitVec 32)) :
    VG.Proof.MlDsa.X86_64.Round.writes m (p :: ps) = VG.Proof.MlDsa.X86_64.Round.writes (m.writeW p.1 p.2) ps := rfl

section
variable (P : Reg → Addr)

/-- Writes to coefficient `j` of polynomials disjoint from that at `p` leave it unchanged. -/
theorem coeffAt_writes_disjoint (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    {p : Addr} (hd : ∀ o ∈ outs, (pR p).Disjoint (pR (P o))) {k : Nat} (hk : k < 256) :
    VG.Spec.MlDsa.coeffAt (VG.Proof.MlDsa.X86_64.Round.writes m (outs.map fun o => (VG.Proof.MlDsa.Round.coeffAddr (P o) j, V o))) p k = VG.Spec.MlDsa.coeffAt m p k := by
  induction outs generalizing m with
  | nil => rfl
  | cons o os ih =>
    rw [List.map_cons, VG.Proof.MlDsa.X86_64.Round.writes_cons]
    rw [ih _ fun o' h => hd o' (List.mem_cons_of_mem _ h),
      coeffAt_writeW_disjoint m (hd o List.mem_cons_self) (VG.Proof.MlDsa.Round.coeff_contains _ hj) hk]

theorem coeffAt_writes (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    (hpw : outs.Pairwise fun a b => (pR (P a)).Disjoint (pR (P b))) {o : Reg} (ho : o ∈ outs) {k : Nat}
    (hk : k < 256) :
    VG.Spec.MlDsa.coeffAt (VG.Proof.MlDsa.X86_64.Round.writes m (outs.map fun o => (VG.Proof.MlDsa.Round.coeffAddr (P o) j, V o))) (P o) k =
      if j = k then V o else VG.Spec.MlDsa.coeffAt m (P o) k := by
  induction outs generalizing m with
  | nil => cases ho
  | cons o' os ih =>
    rw [List.map_cons, VG.Proof.MlDsa.X86_64.Round.writes_cons]
    rw [List.pairwise_cons] at hpw
    by_cases hr : o ∈ os
    · rw [ih _ hpw.2 hr]
      have hd : (pR (P o)).Disjoint (pR (P o')) := (hpw.1 o hr).symm
      rw [coeffAt_writeW_disjoint m hd (VG.Proof.MlDsa.Round.coeff_contains _ hj) hk]
    · obtain rfl : o = o' := by simpa [hr] using ho
      rw [VG.Proof.MlDsa.X86_64.Round.coeffAt_writes_disjoint P _ os j hj V (fun o' h => hpw.1 o' h) hk, VG.Proof.MlDsa.Round.coeffAt_writeW m _ hk hj]

theorem frame_writes {rs : List Region} {m₀ m : Mem} (hf : Frame rs m₀ m) (outs : List Reg) (j : Nat)
    (hj : j < 256) (V : Reg → BitVec 32) (hin : ∀ o ∈ outs, pR (P o) ∈ rs) :
    Frame rs m₀ (VG.Proof.MlDsa.X86_64.Round.writes m (outs.map fun o => (VG.Proof.MlDsa.Round.coeffAddr (P o) j, V o))) := by
  induction outs generalizing m with
  | nil => exact hf
  | cons o os ih =>
    rw [List.map_cons, VG.Proof.MlDsa.X86_64.Round.writes_cons]
    exact ih (hf.writeW (hin o List.mem_cons_self) _ (VG.Proof.MlDsa.Round.coeff_contains _ hj)) fun o' h =>
      hin o' (List.mem_cons_of_mem _ h)

end

/-! ## The loop -/

/-- Where the loop's polynomials are: inputs readable, outputs writable,
the outputs pairwise disjoint and disjoint from the inputs. -/
structure Layout (s₀ : State) (ins outs : List Reg) : Prop where
  rd : ∀ p ∈ ins, pR (s₀.gpr p) ∈ s₀.rd ++ s₀.wr
  wr : ∀ o ∈ outs, pR (s₀.gpr o) ∈ s₀.wr
  dis : ∀ p ∈ ins, ∀ o ∈ outs, (pR (s₀.gpr p)).Disjoint (pR (s₀.gpr o))
  pw : outs.Pairwise fun a b => (pR (s₀.gpr a)).Disjoint (pR (s₀.gpr b))

/-- After `i` iterations: the registers `fixed` are unchanged, the outputs
hold their values from coefficient `256 - i` on, and `J i`. -/
structure Inv (s₀ : State) (fixed outs : List Reg) (V : Reg → Nat → BitVec 32) (J : Nat → State → Prop)
    (i : Nat) (s : State) : Prop where
  fixed : ∀ r ∈ fixed, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (outs.map fun o => pR (s₀.gpr o)) s₀.mem s.mem
  done : ∀ o ∈ outs, ∀ k, 256 - i ≤ k → k < 256 → VG.Spec.MlDsa.coeffAt s.mem (s₀.gpr o) k = V o k
  j : J i s

section
variable {s₀ : State} {ins outs fixed : List Reg} {V : Reg → Nat → BitVec 32} {J : Nat → State → Prop}
  {i : Nat} {s : State}

/-- The address of the coefficient that iteration `i` handles. -/
theorem Inv.addr (hI : VG.Proof.MlDsa.X86_64.Round.Inv s₀ fixed outs V J i s) (hc : s.gpr .rcx = BitVec.ofNat 64 (256 - i)) (hi : i < 256)
    {p : Reg} (hp : p ∈ fixed) : VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr p) (s.gpr .rcx) = VG.Proof.MlDsa.Round.coeffAddr (s₀.gpr p) (255 - i) := by
  rw [hI.fixed p hp, hc, show 256 - i = 255 - i + 1 by omega]
  exact VG.Proof.MlDsa.X86_64.Round.cfAddr_eq _ _

theorem Inv.inR (hL : VG.Proof.MlDsa.X86_64.Round.Layout s₀ ins outs) (hI : VG.Proof.MlDsa.X86_64.Round.Inv s₀ fixed outs V J i s) {p : Reg} (hp : p ∈ ins) {k : Nat}
    (hk : k < 256) : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.Round.coeffAddr (s₀.gpr p) k) 4 := by
  rw [hI.rd, hI.wr]
  exact ⟨_, hL.rd p hp, VG.Proof.MlDsa.Round.coeff_contains _ hk⟩

theorem Inv.inW (hL : VG.Proof.MlDsa.X86_64.Round.Layout s₀ ins outs) (hI : VG.Proof.MlDsa.X86_64.Round.Inv s₀ fixed outs V J i s) {o : Reg} (ho : o ∈ outs) {k : Nat}
    (hk : k < 256) : InRegions s.wr (VG.Proof.MlDsa.Round.coeffAddr (s₀.gpr o) k) 4 := by
  rw [hI.wr]
  exact ⟨_, hL.wr o ho, VG.Proof.MlDsa.Round.coeff_contains _ hk⟩

/-- The inputs are those of the initial memory. -/
theorem Inv.read (hL : VG.Proof.MlDsa.X86_64.Round.Layout s₀ ins outs) (hI : VG.Proof.MlDsa.X86_64.Round.Inv s₀ fixed outs V J i s) {p : Reg} (hp : p ∈ ins) {k : Nat}
    (hk : k < 256) : s.mem.readW (VG.Proof.MlDsa.Round.coeffAddr (s₀.gpr p) k) 32 = VG.Spec.MlDsa.coeffAt s₀.mem (s₀.gpr p) k :=
  coeffAt_frame hI.frame (fun _ hr => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
    exact hL.dis p hp o ho) hk

end

/-- The loop, from a body that writes `V o (255 - i)` to coefficient `255 - i` of each output. -/
theorem loop_ok {s₀ : State} {ins outs fixed clob : List Reg} {body : List Instr} {V : Reg → Nat → BitVec 32}
    {J : Nat → State → Prop} (hL : VG.Proof.MlDsa.X86_64.Round.Layout s₀ ins outs) (hfix : ∀ r ∈ fixed, r ∉ clob) (hcx : .rcx ∈ clob)
    (hJ : ∀ s, s.gpr .rcx = BitVec.ofNat 64 256 → s.mem = s₀.mem → Keep [.rcx] s₀ s → J 0 s)
    (hbody : ∀ i < 256, ∀ s, VG.Proof.MlDsa.X86_64.Round.Inv s₀ fixed outs V J i s → s.gpr .rcx = BitVec.ofNat 64 (256 - i) →
      WP isa (.block (body ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
        (s'.mem = VG.Proof.MlDsa.X86_64.Round.writes s.mem (outs.map fun o => (VG.Proof.MlDsa.Round.coeffAddr (s₀.gpr o) (255 - i), V o (255 - i))) ∧
          s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ J (i + 1) s') ∧
        Keep clob s s') :
    WP isa (mapLoop body) s₀ (VG.Proof.MlDsa.X86_64.Round.Inv s₀ fixed outs V J 256) := by
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s => s.mem = s₀.mem ∧ s.gpr .rcx = BitVec.ofNat 64 256)
    (by apply WP.of_runBlock; simp [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      setReg_gpr, setReg_mem]) (by decide)) fun s₁ ⟨⟨hm, hc⟩, hk⟩ => ?_)
  have h0 : VG.Proof.MlDsa.X86_64.Round.Inv s₀ fixed outs V J 0 s₁ := by
    refine ⟨fun r hr => hk.gpr fun h => ?_, hk.2.1, hk.2.2, ?_, fun _ _ k h₁ h₂ => absurd h₂ (by omega),
      hJ s₁ hc hm hk⟩
    · simp only [List.mem_singleton] at h
      subst h
      exact hfix _ hr hcx
    · rw [hm]; exact Frame.refl _ _
  refine wp_countdown (cnt := .rcx) (N := 256) (by decide) (by decide) (VG.Proof.MlDsa.X86_64.Round.Inv s₀ fixed outs V J)
    (fun i hi s hI hc => ?_) (fun _ h => h) h0 hc
  · refine WP.mono (hbody i hi s hI hc) fun s' ⟨⟨hm', hc', hz', hJ'⟩, hk'⟩ => ⟨?_, hc', hz'⟩
    refine ⟨fun r hr => (hk'.gpr (hfix r hr)).trans (hI.fixed r hr), hk'.2.1.trans hI.rd, hk'.2.2.trans hI.wr,
      ?_, fun o ho k h₁ h₂ => ?_, hJ'⟩
    · rw [hm']
      exact VG.Proof.MlDsa.X86_64.Round.frame_writes _ hI.frame outs _ (by omega) _ fun o ho => List.mem_map_of_mem ho
    · rw [hm', VG.Proof.MlDsa.X86_64.Round.coeffAt_writes _ _ outs _ (by omega) _ hL.pw ho h₂]
      split
      · subst k; rfl
      · exact hI.done o ho k (by omega) h₂

end VG.Proof.MlDsa.X86_64.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Round.Contracts`. -/
section

/-!
# ML-DSA on x86-64: the contracts the rounding proofs are written against

For each function, a contract with the facts of its shared contract
(`Spec/MlDsa/Poly.lean`) spelled out for x86-64: the arguments in their
registers, the permitted regions, their disjointness, and the postcondition.
`Verified.of_correct` moves a proof to the shared contract, which implies it
(`round_implies`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Proof.MlDsa.Round
open VG.Spec.MlDsa

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- A `u32` argument in `r`. -/
abbrev arg32 (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_mldsa_power2round(t = rdi, t1 = rsi, t0 = rdx)`. -/
def power2RoundK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [pR (s.gpr .rsi), pR (s.gpr .rdx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdx)) ∧ (VG.Proof.MlDsa.X86_64.Round.retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (VG.Proof.MlDsa.X86_64.Round.retR s).Disjoint (pR (s.gpr .rsi)) ∧ (VG.Proof.MlDsa.X86_64.Round.retR s).Disjoint (pR (s.gpr .rdx)) ∧ VG.Spec.MlDsa.Reduced s.mem (s.gpr .rdi)
  post s s' :=
    NatPolyIs s'.mem (s.gpr .rsi) ((VG.Spec.MlDsa.polyAt s.mem (s.gpr .rdi)).map fun c => (VG.Spec.MlDsa.power2Round c).1.toNat) ∧
      VG.Spec.MlDsa.PolyIs s'.mem (s.gpr .rdx) ((VG.Spec.MlDsa.polyAt s.mem (s.gpr .rdi)).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-- `r = rdi, gamma2 = esi, out = rdx`, with the postcondition `post`. -/
def bitsK (post : State → State → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [pR (s.gpr .rdx)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (VG.Proof.MlDsa.X86_64.Round.retR s).Disjoint (pR (s.gpr .rdi)) ∧ (VG.Proof.MlDsa.X86_64.Round.retR s).Disjoint (pR (s.gpr .rdx)) ∧ VG.Proof.MlDsa.X86_64.Round.arg32 s .rsi ∈ gamma2s ∧
    VG.Spec.MlDsa.Reduced s.mem (s.gpr .rdi)
  post := post
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `vg_mldsa_high_bits(r = rdi, gamma2 = esi, out = rdx)`. -/
def highBitsK : Contract isa := VG.Proof.MlDsa.X86_64.Round.bitsK fun s s' =>
  NatPolyIs s'.mem (s.gpr .rdx) ((VG.Spec.MlDsa.polyAt s.mem (s.gpr .rdi)).map fun c => (VG.Spec.MlDsa.highBits (VG.Proof.MlDsa.X86_64.Round.arg32 s .rsi) c).toNat)

/-- `vg_mldsa_low_bits(r = rdi, gamma2 = esi, out = rdx)`. -/
def lowBitsK : Contract isa := VG.Proof.MlDsa.X86_64.Round.bitsK fun s s' =>
  VG.Spec.MlDsa.PolyIs s'.mem (s.gpr .rdx) ((VG.Spec.MlDsa.polyAt s.mem (s.gpr .rdi)).map fun c => ofInt (VG.Spec.MlDsa.lowBits (VG.Proof.MlDsa.X86_64.Round.arg32 s .rsi) c))

/-- `vg_mldsa_norm_lt(f = rdi, bound = esi)`. -/
def normLtK : Contract isa where
  pre s := s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [] ∧ (VG.Proof.MlDsa.X86_64.Round.retR s).Disjoint (pR (s.gpr .rdi)) ∧ VG.Spec.MlDsa.Reduced s.mem (s.gpr .rdi)
  post s s' := (s'.gpr .rax).setWidth 32 = if normRq [VG.Spec.MlDsa.polyAt s.mem (s.gpr .rdi)] < VG.Proof.MlDsa.X86_64.Round.arg32 s .rsi then 1 else 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `a = rdi, b = rsi, gamma2 = edx, out = rcx`, with the precondition
`pre'` on the memory and the postcondition `post`. -/
def hintK (pre' : State → Prop) (post : State → State → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi), pR (s.gpr .rsi)] ∧ s.wr = [pR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rcx)) ∧
    (VG.Proof.MlDsa.X86_64.Round.retR s).Disjoint (pR (s.gpr .rdi)) ∧ (VG.Proof.MlDsa.X86_64.Round.retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (VG.Proof.MlDsa.X86_64.Round.retR s).Disjoint (pR (s.gpr .rcx)) ∧ VG.Proof.MlDsa.X86_64.Round.arg32 s .rdx ∈ gamma2s ∧ pre' s
  post := post
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32

/-- `vg_mldsa_make_hint(z = rdi, r = rsi, gamma2 = edx, h = rcx)`. -/
def makeHintK : Contract isa :=
  VG.Proof.MlDsa.X86_64.Round.hintK (fun s => VG.Spec.MlDsa.Reduced s.mem (s.gpr .rdi) ∧ VG.Spec.MlDsa.Reduced s.mem (s.gpr .rsi)) fun s s' =>
    let hint := Vector.zipWith (VG.Spec.MlDsa.makeHint (VG.Proof.MlDsa.X86_64.Round.arg32 s .rdx)) (VG.Spec.MlDsa.polyAt s.mem (s.gpr .rdi)) (VG.Spec.MlDsa.polyAt s.mem (s.gpr .rsi))
    HintIs s'.mem (s.gpr .rcx) 1 [hint] ∧ ((s'.gpr .rax).setWidth 32).toNat = hintOnes [hint]

/-- `vg_mldsa_use_hint(h = rdi, r = rsi, gamma2 = edx, out = rcx)`. -/
def useHintK : Contract isa :=
  VG.Proof.MlDsa.X86_64.Round.hintK (fun s => VG.Spec.MlDsa.Reduced s.mem (s.gpr .rsi)) fun s s' =>
    NatPolyIs s'.mem (s.gpr .rcx) (Vector.zipWith (fun hj rj => (VG.Spec.MlDsa.useHint (VG.Proof.MlDsa.X86_64.Round.arg32 s .rdx) hj rj).toNat)
      ((hintAt s.mem (s.gpr .rdi) 1).headD (Vector.replicate VG.Spec.MlDsa.n false)) (VG.Spec.MlDsa.polyAt s.mem (s.gpr .rsi)))

/-- The taint in which the registers `rs` are public, and the low halves of
`los` (public 32-bit arguments). -/
def regsLo (rs los : List Reg) : X86_64.Taint.T :=
  { regs := RegSet.ofList rs, flags := false, lo := RegSet.ofList los }

theorem agree_regsLo {rs los : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hl : ∀ r ∈ los, (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32) :
    X86_64.Taint.Agree (VG.Proof.MlDsa.X86_64.Round.regsLo rs los) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  ok _ h := by cases h
  slots _ h := by cases h
  lo r hr := hl r (RegSet.mem_ofList.mp hr)

/-- `sig_implies`, whose satisfiability witness may need `Reduced` of the
memory of zeros. -/
syntax "round_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| round_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by sig_implies_pre [$ls,*]
        post := by sig_implies_post [$ls,*]
        pub := by sig_implies_pub [$ls,*]
        sat := by
          refine ⟨$w, ?_⟩
          sig_pre [$ls,*]
          and_intros
          all_goals first
            | rfl
            | decide
            | exact Region.disjoint_of_sep (by decide)
            | exact reduced_zero _
            | (intro a h₁ h₂
               set_option linter.unusedSimpArgs false in
               simp only [Region.Contains, $ws,*] at h₁ h₂
               bv_omega) })

end VG.Proof.MlDsa.X86_64.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Round.OneOut`. -/
section

/-!
# ML-DSA on x86-64: the functions with `γ₂` and one output

`vg_mldsa_high_bits`, `vg_mldsa_low_bits` and `vg_mldsa_use_hint` compare `γ₂`
(in `gr`) with `(q - 1)/32`, move their output pointer (in `oa`) to `r10`, and
run the loop of the body for the `γ₂` they found. `oneOut_ok` proves this
once, from a body that stores `F γ₂ x` for the coefficients `x p` of the
inputs `p`.
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (coeffAt gamma2s)
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)

/-- `x - k` is zero exactly when `x = k`. -/
theorem sub_beq_zero32 (x k : BitVec 32) : (x - k == 0) = decide (x = k) := by
  by_cases h : x = k
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; apply h; bv_omega

theorem gamma_cases {s₀ : State} {gr : Reg} (hg : VG.Proof.MlDsa.X86_64.Round.arg32 s₀ gr ∈ gamma2s) :
    (BitVec.setWidth 32 (s₀.gpr gr) = BitVec.ofNat 32 g32 → VG.Proof.MlDsa.X86_64.Round.arg32 s₀ gr = g32) ∧
      (BitVec.setWidth 32 (s₀.gpr gr) ≠ BitVec.ofNat 32 g32 → VG.Proof.MlDsa.X86_64.Round.arg32 s₀ gr = g88) := by
  refine ⟨fun h => by rw [VG.Proof.MlDsa.X86_64.Round.arg32, h]; rfl, fun h => ?_⟩
  rcases mem_gamma2s hg with e | e
  · exact e
  · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h

/-- What the prologue does: `γ₂` compared, and the output pointer in `r10`. -/
def Prologue (gr oa : Reg) (s s' : State) : Prop :=
  (s'.gpr .r10 = s.gpr oa ∧ s'.zf = some (BitVec.setWidth 32 (s.gpr gr) - BitVec.ofNat 32 g32 == 0) ∧
    s'.mem = s.mem) ∧ Keep [gr, .r10] s s'

theorem prologue_rsi_rdx (s : State) :
    WP isa (.block (gammaCmp .rsi ++ ([.mov .r10 (.reg .rdx)] : List Instr))) s (VG.Proof.MlDsa.X86_64.Round.Prologue .rsi .rdx s) := by
  refine WP.keep _ ?_ (by decide)
  unfold gammaCmp
  xrun [List.cons_append, List.nil_append]

theorem prologue_rdx_rcx (s : State) :
    WP isa (.block (gammaCmp .rdx ++ ([.mov .r10 (.reg .rcx)] : List Instr))) s (VG.Proof.MlDsa.X86_64.Round.Prologue .rdx .rcx s) := by
  refine WP.keep _ ?_ (by decide)
  unfold gammaCmp
  xrun [List.cons_append, List.nil_append]

theorem oneOut_ok {s₀ : State} {ins : List Reg} {gr oa : Reg} {clob : List Reg} {body : Nat → List Instr}
    {F : Nat → List (BitVec 32) → BitVec 32}
    (hrd : ∀ p ∈ ins, pR (s₀.gpr p) ∈ s₀.rd) (hwr : s₀.wr = [pR (s₀.gpr oa)])
    (hdis : ∀ p ∈ ins, (pR (s₀.gpr p)).Disjoint (pR (s₀.gpr oa))) (hg : VG.Proof.MlDsa.X86_64.Round.arg32 s₀ gr ∈ gamma2s)
    (hpro : WP isa (.block (gammaCmp gr ++ ([.mov .r10 (.reg oa)] : List Instr))) s₀ (VG.Proof.MlDsa.X86_64.Round.Prologue gr oa s₀)) (hins : ∀ p ∈ ins, p ≠ gr ∧ p ≠ .r10) (hfix : ∀ r ∈ Reg.r10 :: ins, r ∉ clob)
    (hcx : .rcx ∈ clob)
    (hbody : ∀ g, (g = g32 ∨ g = g88) → ∀ s, (∀ p ∈ ins, InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr p) (s.gpr .rcx)) 4) →
      InRegions s.wr (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .r10) (s.gpr .rcx)) 4 →
      WP isa (.block (body g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
        (s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .r10) (s.gpr .rcx))
            (F g (ins.map fun p => s.mem.readW (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr p) (s.gpr .rcx)) 32)) ∧
          s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep clob s s') :
    WP isa (.seq (.block (gammaCmp gr ++ ([.mov .r10 (.reg oa)] : List Instr))) (.ite .e (mapLoop (body g32)) (mapLoop (body g88))))
      s₀ fun s' =>
        (∀ k < 256, VG.Spec.MlDsa.coeffAt s'.mem (s₀.gpr oa) k = F (VG.Proof.MlDsa.X86_64.Round.arg32 s₀ gr) (ins.map fun p => VG.Spec.MlDsa.coeffAt s₀.mem (s₀.gpr p) k)) ∧
          Frame [pR (s₀.gpr oa)] s₀.mem s'.mem := by
  refine WP.seq (WP.mono hpro fun s₁ ⟨⟨h10, hz, hm⟩, hk⟩ => ?_)
  have hp : ∀ p ∈ ins, s₁.gpr p = s₀.gpr p := fun p hp' =>
    hk.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hins p hp')
  have hL : VG.Proof.MlDsa.X86_64.Round.Layout s₁ ins [.r10] :=
    { rd := fun p hp' => by rw [hp p hp', hk.2.1, hk.2.2]; exact List.mem_append_left _ (hrd p hp')
      wr := fun o ho => by
        simp only [List.mem_singleton] at ho; subst ho; rw [h10, hk.2.2, hwr]; exact List.mem_singleton_self _
      dis := fun p hp' o ho => by
        simp only [List.mem_singleton] at ho; subst ho; rw [h10, hp p hp']; exact hdis p hp'
      pw := List.pairwise_singleton _ _ }
  have go : ∀ g, VG.Proof.MlDsa.X86_64.Round.arg32 s₀ gr = g → WP isa (mapLoop (body g)) s₁ fun s' =>
      (∀ k < 256, VG.Spec.MlDsa.coeffAt s'.mem (s₀.gpr oa) k = F (VG.Proof.MlDsa.X86_64.Round.arg32 s₀ gr) (ins.map fun p => VG.Spec.MlDsa.coeffAt s₀.mem (s₀.gpr p) k)) ∧
        Frame [pR (s₀.gpr oa)] s₀.mem s'.mem := by
    intro g hge
    refine WP.mono (VG.Proof.MlDsa.X86_64.Round.loop_ok (fixed := .r10 :: ins) (V := fun _ k => F g (ins.map fun p => VG.Spec.MlDsa.coeffAt s₀.mem (s₀.gpr p) k))
      (J := fun _ _ => True) hL hfix hcx (fun _ _ _ _ => trivial) fun i hi s hI hc => ?_) fun s' hI => ?_
    · have ha : ∀ p ∈ Reg.r10 :: ins, VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr p) (s.gpr .rcx) = VG.Proof.MlDsa.Round.coeffAddr (s₁.gpr p) (255 - i) :=
        fun p hp' => hI.addr hc hi hp'
      have hg' : g = g32 ∨ g = g88 := by
        rcases mem_gamma2s hg with e | e <;> rw [e] at hge <;> subst hge <;> decide
      refine WP.mono (hbody g hg' s (fun p hp' => by
          rw [ha p (List.mem_cons_of_mem _ hp')]; exact hI.inR hL hp' (by omega))
        (by rw [ha _ List.mem_cons_self]; exact hI.inW hL List.mem_cons_self (by omega)))
        fun s' ⟨⟨hm', hc', hz'⟩, hk'⟩ => ⟨⟨?_, hc', hz', trivial⟩, hk'⟩
      rw [hm', ha _ List.mem_cons_self]
      refine congrArg (Mem.writeW _ _ <| F g ·) (List.map_congr_left fun p hp' => ?_)
      rw [ha p (List.mem_cons_of_mem _ hp'), hI.read hL hp' (by omega), hm, hp p hp']
    · refine ⟨fun k hk => ?_, ?_⟩
      · rw [← h10, hI.done .r10 List.mem_cons_self k (by omega) hk, hge]
      · have := hI.frame
        rw [hm, List.map_singleton, h10] at this
        exact this
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from hz) (fun h => ?_) (fun h => ?_)
  · rw [VG.Proof.MlDsa.X86_64.Round.sub_beq_zero32, decide_eq_true_eq] at h
    exact go _ ((VG.Proof.MlDsa.X86_64.Round.gamma_cases hg).1 h)
  · rw [VG.Proof.MlDsa.X86_64.Round.sub_beq_zero32, decide_eq_false_iff_not] at h
    exact go _ ((VG.Proof.MlDsa.X86_64.Round.gamma_cases hg).2 h)

end VG.Proof.MlDsa.X86_64.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_high_bits` and `vg_mldsa_low_bits`
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of)

theorem dShift_ge (g : Nat) : 1 ≤ dShift g := by unfold dShift; split <;> decide
theorem dShift_le (g : Nat) : dShift g ≤ 63 := by unfold dShift; split <;> decide

/-! ## The bodies -/

/-- The `r₁` the body of `highBits` stores. -/
def hbS (g : Nat) (x : BitVec 32) : BitVec 32 := BitVec.setWidth 32 (VG.Proof.MlDsa.X86_64.Round.hbV g (BitVec.setWidth 64 x))

/-- The `r₀` the body of `lowBits` stores. -/
def lbS (g : Nat) (x : BitVec 32) : BitVec 32 :=
  BitVec.setWidth 32 (VG.Proof.MlDsa.X86_64.Round.condAddV (BitVec.setWidth 64 x)
    (BitVec.ofNat 64 ((VG.Proof.MlDsa.X86_64.Round.hbV g (BitVec.setWidth 64 x)).toNat * (BitVec.setWidth 64 (BitVec.ofNat 32 (2 * g))).toNat))
    qImm)

theorem hbBody_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (h1 : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4)
    (h2 : InRegions s.wr (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .r10) (s.gpr .rcx)) 4) :
    WP isa (.block (hbBody g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .r10) (s.gpr .rcx))
          (VG.Proof.MlDsa.X86_64.Round.hbS g (s.mem.readW (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by rcases hg with rfl | rfl <;> decide)
  unfold hbBody hb hbRaw condAdd
  xrun [h1, h2, VG.Proof.MlDsa.X86_64.Round.ea_cf, List.cons_append, List.nil_append, VG.Proof.MlDsa.X86_64.Round.hbS, VG.Proof.MlDsa.X86_64.Round.hbV, VG.Proof.MlDsa.X86_64.Round.hbRawV, VG.Proof.MlDsa.X86_64.Round.condAddV, VG.Proof.MlDsa.X86_64.Round.dShift_ge, VG.Proof.MlDsa.X86_64.Round.dShift_le]
  rfl

theorem lbBody_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (h1 : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4)
    (h2 : InRegions s.wr (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .r10) (s.gpr .rcx)) 4) :
    WP isa (.block (lbBody g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .r10) (s.gpr .rcx))
          (VG.Proof.MlDsa.X86_64.Round.lbS g (s.mem.readW (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .r8, .r11, .rcx] s s' := by
  refine WP.keep _ ?_ (by rcases hg with rfl | rfl <;> decide)
  unfold lbBody hb hbRaw condAdd
  xrun [h1, h2, VG.Proof.MlDsa.X86_64.Round.ea_cf, List.cons_append, List.nil_append, VG.Proof.MlDsa.X86_64.Round.lbS, VG.Proof.MlDsa.X86_64.Round.hbV, VG.Proof.MlDsa.X86_64.Round.hbRawV, VG.Proof.MlDsa.X86_64.Round.condAddV, VG.Proof.MlDsa.X86_64.Round.dShift_ge, VG.Proof.MlDsa.X86_64.Round.dShift_le]
  rfl

/-! ## The values -/

theorem hbS_toNat {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (VG.Proof.MlDsa.X86_64.Round.hbS g x).toNat = hbF g x.toNat % Proof.MlDsa.Round.hbM g := by
  have hx' : (BitVec.setWidth 64 x).toNat < q := by rw [VG.Proof.MlDsa.X86_64.Round.setWidth64_toNat]; exact hx
  have hM : Proof.MlDsa.Round.hbM g ≤ 44 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have := Nat.mod_lt (hbF g x.toNat) (show Proof.MlDsa.Round.hbM g > 0 by rcases mem_gamma2s h with rfl | rfl <;> decide)
  rw [VG.Proof.MlDsa.X86_64.Round.hbS, BitVec.toNat_setWidth, VG.Proof.MlDsa.X86_64.Round.hbV_toNat h hx', VG.Proof.MlDsa.X86_64.Round.setWidth64_toNat]
  omega

theorem lbS_toNat {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (VG.Proof.MlDsa.X86_64.Round.lbS g x).toNat = (ofInt (lowBits g (Fin.ofNat q x.toNat))).val := by
  have hx' : (BitVec.setWidth 64 x).toNat < q := by rw [VG.Proof.MlDsa.X86_64.Round.setWidth64_toNat]; exact hx
  have hv : (Fin.ofNat q x.toNat).val = x.toNat := Nat.mod_eq_of_lt hx
  rw [lowBits_val h, hv]
  have hM := hbM_mul h
  have hlt : hbF g x.toNat % Proof.MlDsa.Round.hbM g < Proof.MlDsa.Round.hbM g :=
    Nat.mod_lt _ (by rcases mem_gamma2s h with rfl | rfl <;> decide)
  have hle : hbF g x.toNat % Proof.MlDsa.Round.hbM g * (2 * g) ≤ q - 1 := by
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hlt))
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_of_lt hlt)
    rw [← hM]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
  have hg : 2 * g < 2 ^ 31 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have e1 : (BitVec.ofNat 64 ((VG.Proof.MlDsa.X86_64.Round.hbV g (BitVec.setWidth 64 x)).toNat *
      (BitVec.setWidth 64 (BitVec.ofNat 32 (2 * g))).toNat)).toNat =
      hbF g x.toNat % Proof.MlDsa.Round.hbM g * (2 * g) := by
    rw [BitVec.toNat_ofNat, VG.Proof.MlDsa.X86_64.Round.hbV_toNat h hx', VG.Proof.MlDsa.X86_64.Round.setWidth64_toNat, VG.Proof.MlDsa.X86_64.Round.setWidth64_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 * g < 2 ^ 32 by omega)]
    rw [q_eq] at hle
    omega
  have hq : qImm.toNat = q := rfl
  rw [VG.Proof.MlDsa.X86_64.Round.lbS, BitVec.toNat_setWidth, VG.Proof.MlDsa.X86_64.Round.condAddV_toNat (by decide) (by rw [e1, hq, VG.Proof.MlDsa.X86_64.Round.setWidth64_toNat]; omega), e1, hq,
    VG.Proof.MlDsa.X86_64.Round.setWidth64_toNat]
  rw [q_eq] at hx hle ⊢
  split <;> omega

/-! ## The functions -/

section
variable {post : State → State → Prop} {s₀ : State} (hp : (VG.Proof.MlDsa.X86_64.Round.bitsK post).pre s₀)
include hp

theorem bits_ok {body : Nat → List Instr} {F : Nat → List (BitVec 32) → BitVec 32} {clob : List Reg}
    (hfix : ∀ r ∈ [Reg.r10, .rdi], r ∉ clob) (hcx : .rcx ∈ clob)
    (hbody : ∀ g, (g = g32 ∨ g = g88) → ∀ s, (∀ p ∈ [Reg.rdi], InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr p) (s.gpr .rcx)) 4) →
      InRegions s.wr (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .r10) (s.gpr .rcx)) 4 →
      WP isa (.block (body g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
        (s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr .r10) (s.gpr .rcx))
            (F g ([Reg.rdi].map fun p => s.mem.readW (VG.Proof.MlDsa.X86_64.Round.cfAddr (s.gpr p) (s.gpr .rcx)) 32)) ∧
          s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep clob s s') :
    WP isa (.seq (.block (gammaCmp .rsi ++ ([.mov .r10 (.reg .rdx)] : List Instr))) (.ite .e (mapLoop (body g32)) (mapLoop (body g88))))
      s₀ fun s' =>
        (∀ k < 256, VG.Spec.MlDsa.coeffAt s'.mem (s₀.gpr .rdx) k = F (VG.Proof.MlDsa.X86_64.Round.arg32 s₀ .rsi) [VG.Spec.MlDsa.coeffAt s₀.mem (s₀.gpr .rdi) k]) ∧
          Frame [pR (s₀.gpr .rdx)] s₀.mem s'.mem :=
  VG.Proof.MlDsa.X86_64.Round.oneOut_ok (ins := [.rdi]) (fun p h => by simp only [List.mem_singleton] at h; subst h; rw [hp.1]; simp) hp.2.1
    (fun p h => by simp only [List.mem_singleton] at h; subst h; exact hp.2.2.1) hp.2.2.2.2.2.1
    (VG.Proof.MlDsa.X86_64.Round.prologue_rsi_rdx s₀) (fun p h => by simp only [List.mem_singleton] at h; subst h; decide) hfix hcx hbody

end

theorem highBits_correct (s₀ : State) (hp : highBitsK.pre s₀) :
    ∃ t s', Exec isa highBits s₀ t s' ∧ abiPreserved s₀ s' ∧ highBitsK.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .r8, .r10]
    (VG.Proof.MlDsa.X86_64.Round.bits_ok hp (F := fun g xs => VG.Proof.MlDsa.X86_64.Round.hbS g (xs.headD 0)) (by decide) (by decide)
      fun g hg s h1 h2 => VG.Proof.MlDsa.X86_64.Round.hbBody_ok hg s (h1 _ (List.mem_singleton_self _)) h2) (by decide)
  have hr : VG.Spec.MlDsa.Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf ?_), ?_⟩
  · simpa using hp.2.2.2.2.1
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hv k hk, map_get _ _ hk, List.headD_cons, VG.Proof.MlDsa.X86_64.Round.hbS_toNat hp.2.2.2.2.2.1 (hr k hk), highBits_eq hp.2.2.2.2.2.1,
      VG.Proof.MlDsa.Round.polyAt_val hr hk]
    exact (Int.toNat_natCast _).symm

theorem lowBits_correct (s₀ : State) (hp : lowBitsK.pre s₀) :
    ∃ t s', Exec isa lowBits s₀ t s' ∧ abiPreserved s₀ s' ∧ lowBitsK.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .r8, .r10, .r11]
    (VG.Proof.MlDsa.X86_64.Round.bits_ok hp (F := fun g xs => VG.Proof.MlDsa.X86_64.Round.lbS g (xs.headD 0)) (by decide) (by decide)
      fun g hg s h1 h2 => VG.Proof.MlDsa.X86_64.Round.lbBody_ok hg s (h1 _ (List.mem_singleton_self _)) h2) (by decide)
  have hr : VG.Spec.MlDsa.Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf ?_), ?_⟩
  · simpa using hp.2.2.2.2.1
  · refine VG.Proof.MlDsa.Round.polyIs_of_toNat fun k hk => ?_
    rw [hv k hk, map_get _ _ hk, List.headD_cons, VG.Proof.MlDsa.X86_64.Round.lbS_toNat hp.2.2.2.2.2.1 (hr k hk), VG.Proof.MlDsa.Round.polyAt_get _ _ hk]

/-- The pointers and `rsp` are public, and `γ₂`. -/
def bitsτ : X86_64.Taint.T := VG.Proof.MlDsa.X86_64.Round.regsLo [.rdi, .rdx, .rsp] [.rsi]

theorem bits_agree {post : State → State → Prop} (s₁ s₂ : State) (_ : (VG.Proof.MlDsa.X86_64.Round.bitsK post).pre s₁)
    (_ : (VG.Proof.MlDsa.X86_64.Round.bitsK post).pre s₂) (hp : (VG.Proof.MlDsa.X86_64.Round.bitsK post).pub s₁ s₂) : X86_64.Taint.Agree VG.Proof.MlDsa.X86_64.Round.bitsτ s₁ s₂ :=
  VG.Proof.MlDsa.X86_64.Round.agree_regsLo (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2.2

theorem highBits_ct : ConstantTime isa highBitsK.pre highBitsK.pub highBits :=
  VG.Taint.constantTime (A := X86_64.taint) VG.Proof.MlDsa.X86_64.Round.bitsτ VG.Proof.MlDsa.X86_64.Round.bits_agree (by taint_decide)

theorem lowBits_ct : ConstantTime isa lowBitsK.pre lowBitsK.pub lowBits :=
  VG.Taint.constantTime (A := X86_64.taint) VG.Proof.MlDsa.X86_64.Round.bitsτ VG.Proof.MlDsa.X86_64.Round.bits_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def bitsSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 95232 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem highBits_verified : Verified X86_64.target highBits (highBitsContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Round.highBits_correct VG.Proof.MlDsa.X86_64.Round.highBits_ct (by
    round_implies [highBitsContract, bitsSig, VG.Proof.MlDsa.X86_64.Round.highBitsK, VG.Proof.MlDsa.X86_64.Round.bitsK, X86_64.abi, X86_64.argRegs] [bitsSat]
      using VG.Proof.MlDsa.X86_64.Round.bitsSat)

theorem lowBits_verified : Verified X86_64.target lowBits (lowBitsContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Round.lowBits_correct VG.Proof.MlDsa.X86_64.Round.lowBits_ct (by
    round_implies [lowBitsContract, bitsSig, VG.Proof.MlDsa.X86_64.Round.lowBitsK, VG.Proof.MlDsa.X86_64.Round.bitsK, X86_64.abi, X86_64.argRegs] [bitsSat]
      using VG.Proof.MlDsa.X86_64.Round.bitsSat)

end VG.Proof.MlDsa.X86_64.Round

end
