import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Round.HintCore`. -/
section

/-!
# ML-DSA on x86 (32-bit): what `makeHint` and `useHint` compute per coefficient

The cores of the two loops (`Core2`), from the coefficients `a = [esi]` and `b =
[edi]`:

* `mhCore g`: `MakeHint(a, b)` as 0 or 1 (`mhV`): whether the `r₁` of `b`
  and of `b + a mod q` differ, from their xor `x < 64` as `(x + 63) >> 6`;
  it also adds it to `ecx`;
* `uhCore g`: `UseHint(a ≠ 0, b)` (`uhV`): `(f + m + δ) mod m`, with `δ` the
  masked `±1`.
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_)
open VG.Spec.MlDsa (q gamma2s)
open VG.Proof.MlDsa.Round (hbF hbM hbF_le hbM_mul mem_gamma2s q_eq)
open VG.Proof.MlKem.X86 (Only wp_movm toNat_ofNat32 eq_ofNat_of_toNat)

/-- `core` leaves `V a b` in `eax` from `a = [esi]` (less than `q` if `reqA`) and `b = [edi] < q`,
changing only `eax`, `edx`, `ebx`, `ecx` and the flags, and adds it to `ecx` if `cnt`. -/
def Core2 (core : List Instr) (V : Nat → Nat → Nat) (reqA cnt : Bool) : Prop :=
  ∀ (is : List Instr) (s : State) (P : State → Prop) (a b : Nat), (reqA = true → a < q) → b < q →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4 → (s.mem.readW (s.ea (at_ .esi 0)) 32).toNat = a →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4 → (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = b →
    (∀ s', Only [.eax, .edx, .ebx, .ecx] s s' → (s'.gpr .eax).toNat = V a b →
      (cnt = true → s'.gpr .ecx = s.gpr .ecx + s'.gpr .eax) → WP isa (.block is) s' P) →
    WP isa (.block (core ++ is)) s P

/-- `MakeHint`, as 0 or 1. -/
def mhV (g a b : Nat) : Nat := if hbV g b = hbV g ((b + a) % q) then 0 else 1

theorem xor_shift {x y : Nat} (hx : x < 64) (hy : y < 64) : ((x ^^^ y) + 63) / 64 = if x = y then 0 else 1 := by
  have hl : x ^^^ y < 2 ^ 6 := Nat.xor_lt_two_pow (by omega) (by omega)
  by_cases e : x = y
  · subst e; rw [Nat.xor_self, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
    have : x ^^^ y ≠ 0 := fun h => e (Nat.eq_of_testBit_eq fun i => by
      have := congrArg (Nat.testBit · i) h
      simp only [Nat.testBit_xor, Nat.zero_testBit] at this
      revert this; cases x.testBit i <;> cases y.testBit i <;> simp)
    omega

theorem hbV_lt64 {g : Nat} (hg : g ∈ gamma2s) (a : Nat) : hbV g a < 64 := by
  have := Nat.mod_lt (hbF g a) (show hbM g > 0 by rcases mem_gamma2s hg with rfl | rfl <;> decide)
  have : hbM g ≤ 44 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  unfold hbV; omega

theorem mhCore_eq (g : Nat) (is : List Instr) : mhCore g ++ is =
    .mov .eax (.mem (at_ .edi 0)) :: (hb g ++ (.mov .ebx (.reg .eax) :: .mov .eax (.mem (at_ .edi 0)) ::
      .alu .add .eax (.mem (at_ .esi 0)) :: (condAdd .eax (.imm qImm) .edx qImm ++ (hb g ++
      (.alu .xor .eax (.reg .ebx) :: .alu .add .eax (.imm 63) :: .shift .shr .eax 6 ::
        .alu .add .ecx (.reg .eax) :: is))))) := by
  simp only [mhCore, List.cons_append, List.nil_append, List.append_assoc]

theorem mhCore_spec {g : Nat} (hg : g ∈ gamma2s) : VG.Proof.MlDsa.X86.Round.Core2 (mhCore g) (VG.Proof.MlDsa.X86.Round.mhV g) true true := by
  intro is s P a b ha hb hia hva hib hvb c
  have ha := ha rfl
  have hq : q = 8380417 := rfl
  have hB : ∀ {s' : State} {B : BitVec 32}, s'.gpr .esi = B → s'.ea (at_ .esi 0) = addr B 0 :=
    fun h => by rw [State.ea, at_, h]; rfl
  rw [VG.Proof.MlDsa.X86.Round.mhCore_eq]
  refine wp_movm hib (hb_spec hg (a := b) (by simp [State.setReg, hvb]) hb fun s₁ o₁ v₁ => ?_)
  have esi₁ : s₁.gpr .esi = s.gpr .esi := by rw [o₁.gpr _ (by decide)]; simp [State.setReg]
  have edi₁ : s₁.gpr .edi = s.gpr .edi := by rw [o₁.gpr _ (by decide)]; simp [State.setReg]
  have m₁ : s₁.mem = s.mem := o₁.mem
  have rw₁ : s₁.rd ++ s₁.wr = s.rd ++ s.wr := by rw [o₁.rd, o₁.wr]; rfl
  refine wp_mov fun s₂ u₂ => wp_ldm (B := s.gpr .edi) (o := 0) (by rw [u₂.other _ (by decide), edi₁])
    (by rw [u₂.rd, u₂.wr, rw₁]; exact hib) fun s₃ u₃ =>
    wp_addm (B := s.gpr .esi) (o := 0) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), esi₁])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, rw₁]; exact hia) fun s₄ u₄ => ?_
  have v₃ : (s₃.gpr .eax).toNat = b := by rw [u₃.gpr, u₂.mem, m₁]; exact hvb
  have v₄ : (s₄.gpr .eax).toNat = b + a := by
    rw [u₄.gpr, BitVec.toNat_add, v₃, u₃.mem, u₂.mem, m₁]
    rw [show (s.mem.readW (addr (s.gpr .esi) 0) 32) = s.mem.readW (s.ea (at_ .esi 0)) 32 from rfl, hva]
    omega
  refine condAdd_spec (by decide) (X := qImm) rfl (by rw [v₄, show qImm.toNat = q from rfl]; omega)
    fun s₅ o₅ v₅ => hb_spec hg (a := (b + a) % q) (by rw [v₅, v₄, show qImm.toNat = 8380417 from rfl, hq]; unfold condAddN; split <;> omega)
      (Nat.mod_lt _ (by decide)) fun s₆ o₆ v₆ => wp_xor fun s₇ u₇ => wp_addi fun s₈ u₈ =>
      wp_shr (by decide) fun s₉ u₉ _ => wp_add fun s₁₀ u₁₀ _ => c s₁₀ ?_ ?_ fun _ => ?_
  · have o := (VG.Proof.MlKem.X86.Only.setReg s .eax (s.mem.readW (s.ea (at_ .edi 0)) 32)).trans o₁
    have o := (o.trans (updOnly u₂)).trans (updOnly u₃)
    have o := ((o.trans (updOnly u₄)).trans o₅).trans o₆
    have o := (((o.trans (updOnly u₇)).trans (updOnly u₈)).trans (updOnly u₉)).trans (updOnly u₁₀)
    exact o.mono (by decide)
  · have eb₆ : (s₆.gpr .ebx).toNat = hbV g b := by
      rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, v₁]
      rfl
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.gpr, BitVec.toNat_ushiftRight, BitVec.toNat_add,
      BitVec.toNat_xor, v₆, eb₆, Nat.shiftRight_eq_div_pow]
    have h1 := VG.Proof.MlDsa.X86.Round.hbV_lt64 hg ((b + a) % q)
    have h2 := VG.Proof.MlDsa.X86.Round.hbV_lt64 hg b
    have hx : hbF g ((b + a) % q) % hbM g ^^^ hbV g b < 2 ^ 6 := Nat.xor_lt_two_pow (by unfold hbV at h1; omega) (by omega)
    rw [show (63 : BitVec 32).toNat = 63 from rfl, Nat.mod_eq_of_lt (by omega),
      show hbF g ((b + a) % q) % hbM g = hbV g ((b + a) % q) from rfl, VG.Proof.MlDsa.X86.Round.xor_shift h1 h2, VG.Proof.MlDsa.X86.Round.mhV]
    by_cases e : hbV g b = hbV g ((b + a) % q)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true e.symm), ite_eq_left_of_eq_true _ _ (eq_true e)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => e h.symm), ite_eq_right_of_eq_false _ _ (eq_false e)]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), o₆.gpr _ (by decide),
      o₅.gpr _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      o₁.gpr _ (by decide), u₁₀.other _ (by decide)]
    simp [State.setReg]

/-- `UseHint`, from the hint word `a` and `b`. -/
def uhV (g a b : Nat) : Nat :=
  (if a ≠ 0 then (if hbF g b * (2 * g) < b then hbF g b + hbM g + 1 else hbF g b + hbM g - 1)
    else hbF g b + hbM g) % hbM g

/-- The masked `±1`: `1` or `-1` if `c₂`, as `c₁`, and else `0`. -/
def uhD (c₁ c₂ : Bool) : BitVec 32 :=
  (((if c₁ then BitVec.allOnes 32 else 0) &&& 2) - 1) &&& (if c₂ then BitVec.allOnes 32 else 0)

/-- The masked `±1` and the additions of `f` and `m`. -/
theorem uh_val (c₁ c₂ : Bool) (F M : BitVec 32) (hF : F.toNat + M.toNat + 1 < 2 ^ 32) (hM : 1 ≤ M.toNat) :
    (VG.Proof.MlDsa.X86.Round.uhD c₁ c₂ + F + M).toNat =
      if c₂ then (if c₁ then F.toNat + M.toNat + 1 else F.toNat + M.toNat - 1) else F.toNat + M.toNat := by
  cases c₁ <;> cases c₂
  · rw [show VG.Proof.MlDsa.X86.Round.uhD false false = 0 by decide, BitVec.toNat_add, BitVec.toNat_add]
    simp; omega
  · rw [show VG.Proof.MlDsa.X86.Round.uhD false true = BitVec.allOnes 32 by decide, BitVec.toNat_add, BitVec.toNat_add,
      BitVec.toNat_allOnes]
    simp; omega
  · rw [show VG.Proof.MlDsa.X86.Round.uhD true false = 0 by decide, BitVec.toNat_add, BitVec.toNat_add]
    simp; omega
  · rw [show VG.Proof.MlDsa.X86.Round.uhD true true = 1 by decide, BitVec.toNat_add, BitVec.toNat_add]
    simp; omega

/-- Two conditional subtractions of `m` reduce a value less than `3m`. -/
theorem condAdd_twice {x m : Nat} (hx : x < 3 * m) : condAddN (condAddN x m m) m m = x % m := by
  unfold condAddN
  by_cases h₁ : x < m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h₁), show x + m - m = x by omega,
      ite_eq_left_of_eq_true _ _ (eq_true h₁), show x + m - m = x by omega, Nat.mod_eq_of_lt h₁]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁)]
    by_cases h₂ : x - m < m
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h₂), show x - m + m - m = x - m by omega,
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt h₂]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h₂), Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem uhCore_eq (g : Nat) (is : List Instr) : uhCore g ++ is =
    .mov .eax (.mem (at_ .edi 0)) :: .mov .ebx (.reg .eax) :: (hbRaw g ++
      (.mov .ecx (.reg .eax) :: .mov .edx (.imm (BitVec.ofNat 32 (2 * g))) :: .mul .edx ::
        .alu .sub .eax (.reg .ebx) :: .alu .sbb .eax (.reg .eax) :: .alu .and .eax (.imm 2) ::
        .alu .sub .eax (.imm 1) :: .mov .ebx (.imm 0) :: .alu .sub .ebx (.mem (at_ .esi 0)) ::
        .alu .sbb .ebx (.reg .ebx) :: .alu .and .eax (.reg .ebx) :: .alu .add .eax (.reg .ecx) ::
        .alu .add .eax (.imm (BitVec.ofNat 32 (dMod g))) ::
        (condAdd .eax (.imm (BitVec.ofNat 32 (dMod g))) .edx (BitVec.ofNat 32 (dMod g)) ++
        (condAdd .eax (.imm (BitVec.ofNat 32 (dMod g))) .edx (BitVec.ofNat 32 (dMod g)) ++ is)))) := by
  simp only [uhCore, List.cons_append, List.nil_append, List.append_assoc]

theorem uhCore_spec {g : Nat} (hg : g ∈ gamma2s) : VG.Proof.MlDsa.X86.Round.Core2 (uhCore g) (VG.Proof.MlDsa.X86.Round.uhV g) false false := by
  intro is s P a b _ hb hia hva hib hvb c
  have hq : q = 8380417 := rfl
  have hf := hbF_le hg hb
  have hm : 16 ≤ hbM g ∧ hbM g ≤ 44 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hgl : 2 * g ≤ 523776 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hk : (BitVec.ofNat 32 (dMod g)).toNat = hbM g := by rw [dMod_eq hg]; exact ofNat_small (by omega)
  rw [VG.Proof.MlDsa.X86.Round.uhCore_eq]
  refine wp_movm hib (wp_mov fun s₂ u₂ => hbRaw_spec hg (a := b) ?_ hb fun s₃ o₃ v₃ => ?_)
  · rw [u₂.other _ (by decide)]; simp [State.setReg, hvb]
  have b₃ : (s₃.gpr .ebx).toNat = b := by
    rw [o₃.gpr _ (by decide), u₂.gpr]; simp [State.setReg, hvb]
  have esi₃ : s₃.gpr .esi = s.gpr .esi := by
    rw [o₃.gpr _ (by decide), u₂.other _ (by decide)]; simp [State.setReg]
  have m₃ : s₃.mem = s.mem := by rw [o₃.mem, u₂.mem]; rfl
  have rw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [o₃.rd, o₃.wr, u₂.rd, u₂.wr]; rfl
  refine wp_mov fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
  have e₅ : (s₅.gpr .eax).toNat = hbF g b := by rw [u₅.other _ (by decide), u₄.other _ (by decide), v₃]
  have d₅ : (s₅.gpr .edx).toNat = 2 * g := by rw [u₅.gpr]; exact ofNat_small (by omega)
  have hmul : hbF g b * (2 * g) < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_trans hf hm.2) hgl) (by decide)
  refine wp_mulSmall (r := .edx) (by rw [e₅, d₅]; exact hmul) fun s₆ o₆ v₆ => ?_
  refine wp_subr fun s₇ u₇ c₇ => wp_sbb_self c₇ fun s₈ u₈ => wp_andi fun s₉ u₉ => wp_subi fun s₁₀ u₁₀ _ _ =>
    wp_movi fun s₁₁ u₁₁ => wp_subm (B := s.gpr .esi) (o := 0) ?_ ?_ fun s₁₂ u₁₂ c₁₂ =>
    wp_sbb_self c₁₂ fun s₁₃ u₁₃ => wp_and fun s₁₄ u₁₄ => wp_add fun s₁₅ u₁₅ _ => wp_addi fun s₁₆ u₁₆ => ?_
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), o₆.gpr _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), esi₃]
  · rw [u₁₁.rd, u₁₁.wr, u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, o₆.rd, o₆.wr, u₅.rd, u₅.wr,
      u₄.rd, u₄.wr, rw₃]
    exact hia
  have e₆ : (s₆.gpr .eax).toNat = hbF g b * (2 * g) := by rw [v₆, e₅, d₅]
  have eb₆ : (s₆.gpr .ebx).toNat = b := by
    rw [o₆.gpr _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), b₃]
  have eF : (s₁₂.gpr .ecx).toNat = hbF g b := by
    rw [u₁₂.other .ecx (by decide), u₁₁.other .ecx (by decide), u₁₀.other .ecx (by decide),
      u₉.other .ecx (by decide), u₈.other .ecx (by decide), u₇.other .ecx (by decide), o₆.gpr .ecx (by decide),
      u₅.other .ecx (by decide), u₄.gpr, v₃]
  have ea : (s₁₁.mem.readW (addr (s.gpr .esi) 0) 32).toNat = a := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, o₆.mem, u₅.mem, u₄.mem, m₃]; exact hva
  have e0 : (s₁₁.gpr .ebx).toNat = 0 := by rw [u₁₁.gpr]; rfl
  have x₁₆ : (s₁₆.gpr .eax).toNat =
      if 0 < a then (if hbF g b * (2 * g) < b then hbF g b + hbM g + 1 else hbF g b + hbM g - 1)
      else hbF g b + hbM g := by
    rw [u₁₆.gpr, u₁₅.gpr, u₁₄.gpr, u₁₃.gpr, u₁₄.other .ecx (by decide), u₁₃.other .eax (by decide),
      u₁₃.other .ecx (by decide), u₁₂.other .eax (by decide), u₁₁.other .eax (by decide), u₁₀.gpr, u₉.gpr,
      u₈.gpr, e₆, eb₆, e0, ea]
    refine (VG.Proof.MlDsa.X86.Round.uh_val _ _ _ _ (by rw [eF, hk]; omega) (by rw [hk]; omega)).trans ?_
    rw [eF, hk]
    by_cases h₁ : 0 < a <;> by_cases h₂ : hbF g b * (2 * g) < b <;> simp [h₁, h₂]
  have hx : (s₁₆.gpr .eax).toNat < 3 * hbM g := by
    rw [x₁₆]; split
    · split <;> omega
    · omega
  refine condAdd_spec (by decide) (X := BitVec.ofNat 32 (dMod g)) rfl (by rw [hk]; omega)
    fun s₁₇ o₁₇ v₁₇ => condAdd_spec (by decide) (X := BitVec.ofNat 32 (dMod g)) rfl
      (by rw [hk, v₁₇, hk]; unfold condAddN; split <;> omega) fun s₁₈ o₁₈ v₁₈ =>
      c s₁₈ ?_ ?_ (fun h => absurd h (by decide))
  · have o := (VG.Proof.MlKem.X86.Only.setReg s .eax (s.mem.readW (s.ea (at_ .edi 0)) 32)).trans (updOnly u₂)
    have o := ((o.trans o₃).trans (updOnly u₄)).trans (updOnly u₅)
    have o := (((o.trans o₆).trans (updOnly u₇)).trans (updOnly u₈)).trans (updOnly u₉)
    have o := (((o.trans (updOnly u₁₀)).trans (updOnly u₁₁)).trans (updOnly u₁₂)).trans (updOnly u₁₃)
    have o := ((((o.trans (updOnly u₁₄)).trans (updOnly u₁₅)).trans (updOnly u₁₆)).trans o₁₇).trans o₁₈
    exact o.mono (by decide)
  · rw [v₁₈, v₁₇, hk, VG.Proof.MlDsa.X86.Round.condAdd_twice hx, x₁₆, VG.Proof.MlDsa.X86.Round.uhV]
    by_cases h₁ : 0 < a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h₁), ite_eq_left_of_eq_true _ _ (eq_true (by omega : a ≠ 0))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁), ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬a ≠ 0))]

end VG.Proof.MlDsa.X86.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Round.Hint`. -/
section

/-!
# ML-DSA on x86 (32-bit): the loops of `vg_mldsa_make_hint` and `vg_mldsa_use_hint`

Both store the end of their output, `out + 1024`, in the argument slot of
`γ₂`, compare `γ₂` with `(q - 1)/32` (`hintInit`), and run, for the value they
found, a loop of a core (`Core2`, `HintCore.lean`) and `endTail`, which stores
`eax` to the output at `ebp` and compares the advanced `ebp` with the end
(`hint_step`). The loop is proven once for both (`hint_piece`); `makeHint`
also counts the values in `ecx` (`cnt`).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q gamma2s coeffAt Reduced)
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_frame coeffAt_writeW coeffAt_writeW_disjoint
  n_eq q_eq)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_esp P0_wr frameR retR LeafPost LeafEnd Piece toNat_ofNat32
  eq_ofNat_of_toNat ptr_next sub_beq_zero)

/-- The precondition of both, with `reqA` if the first polynomial is reduced (`makeHint`'s `z`). -/
structure HPre (reqA : Bool) (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s₀.rd = [pR (pA s₀ 0), pR (pA s₀ 1)]
  wr : s₀.wr = [pR (pA s₀ 3), VG.Proof.MlDsa.X86.Round.aR s₀ 4]
  a_o : (pR (pA s₀ 0)).Disjoint (pR (pA s₀ 3))
  a_a : (pR (pA s₀ 0)).Disjoint (VG.Proof.MlDsa.X86.Round.aR s₀ 4)
  b_o : (pR (pA s₀ 1)).Disjoint (pR (pA s₀ 3))
  b_a : (pR (pA s₀ 1)).Disjoint (VG.Proof.MlDsa.X86.Round.aR s₀ 4)
  o_a : (pR (pA s₀ 3)).Disjoint (VG.Proof.MlDsa.X86.Round.aR s₀ 4)
  ret_a' : (retR s₀).Disjoint (pR (pA s₀ 0))
  ret_b : (retR s₀).Disjoint (pR (pA s₀ 1))
  ret_o : (retR s₀).Disjoint (pR (pA s₀ 3))
  ret_a : (retR s₀).Disjoint (VG.Proof.MlDsa.X86.Round.aR s₀ 4)
  stk_a' : (VG.Proof.MlDsa.X86.Round.stkR s₀).Disjoint (pR (pA s₀ 0))
  stk_b : (VG.Proof.MlDsa.X86.Round.stkR s₀).Disjoint (pR (pA s₀ 1))
  stk_o : (VG.Proof.MlDsa.X86.Round.stkR s₀).Disjoint (pR (pA s₀ 3))
  stk_a : (VG.Proof.MlDsa.X86.Round.stkR s₀).Disjoint (VG.Proof.MlDsa.X86.Round.aR s₀ 4)
  a_fit : (arg s₀ 0).toNat + 1024 ≤ 2 ^ 32
  b_fit : (arg s₀ 1).toNat + 1024 ≤ 2 ^ 32
  o_fit : (arg s₀ 3).toNat + 1024 ≤ 2 ^ 32
  g2 : (arg s₀ 2).toNat ∈ gamma2s
  a_red : reqA = true → Reduced s₀.mem (pA s₀ 0)
  b_red : Reduced s₀.mem (pA s₀ 1)

/-- The public data: the stack pointer, the pointers and `γ₂`. -/
def HPub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

/-! ## The prologue -/

/-- After `hintInit`. -/
structure HS1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame [VG.Proof.MlDsa.X86.Round.aR s₀ 4] (P0 s₀).mem s.mem
  slot : s.mem.readW (argAddr s₀ 2) 32 = arg s₀ 3 + 1024
  esi : s.gpr .esi = arg s₀ 0
  edi : s.gpr .edi = arg s₀ 1
  ebp : s.gpr .ebp = arg s₀ 3
  ecx : s.gpr .ecx = 0
  zf : s.zf = some (arg s₀ 2 == BitVec.ofNat 32 g32)

theorem hintInit_piece (reqA : Bool) : Piece (VG.Proof.MlDsa.X86.Round.HPre reqA) VG.Proof.MlDsa.X86.Round.HPub (fun s₀ s => s = P0 s₀) VG.Proof.MlDsa.X86.Round.HS1 (.block hintInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by taint_decide)
  · subst e
    have hin : VG.Proof.MlDsa.X86.Round.aR s₀ 4 ∈ s₀.rd ++ s₀.wr := by simp [hp.wr]
    obtain ⟨a₀, i₀, v₀⟩ := VG.Proof.MlDsa.X86.Round.arg_P0 (i := 0) (by omega) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₁, i₁, v₁⟩ := VG.Proof.MlDsa.X86.Round.arg_P0 (i := 1) (by omega) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₂, i₂, v₂⟩ := VG.Proof.MlDsa.X86.Round.arg_P0 (i := 2) (by omega) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₃, i₃, v₃⟩ := VG.Proof.MlDsa.X86.Round.arg_P0 (i := 3) (by omega) hp.sp hp.sp' hin hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at a₀ a₁ a₂ a₃
    have w₂ : InRegions (P0 s₀).wr (argAddr s₀ 2) 4 :=
      ⟨VG.Proof.MlDsa.X86.Round.aR s₀ 4, by rw [P0_wr, hp.wr]; simp, arg_contains (by omega) hp.sp'⟩
    have s02 : Mem.Sep (argAddr s₀ 2) 4 (argAddr s₀ 0) 4 := by
      have := hp.sp'; intro x h₁ h₂; simp only [argAddr, E0] at this h₁ h₂; bv_omega
    have s12 : Mem.Sep (argAddr s₀ 2) 4 (argAddr s₀ 1) 4 := by
      have := hp.sp'; intro x h₁ h₂; simp only [argAddr, E0] at this h₁ h₂; bv_omega
    have s32 : Mem.Sep (argAddr s₀ 2) 4 (argAddr s₀ 3) 4 := by
      have := hp.sp'; intro x h₁ h₂; simp only [argAddr, E0] at this h₁ h₂; bv_omega
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, hintInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, a₁, a₂, a₃, i₀, i₁, i₂, i₃, v₀, v₁, v₂, v₃, w₂,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (arg_contains (by omega)
      hp.sp'), Mem.readW_writeW_self32 _ _ _, by simp, by simp, by simp, by simp, by rw [sub_beq_zero']⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

/-! ## The loop -/

/-- The first polynomial's coefficient `i`. -/
abbrev cA (s₀ : State) (i : Nat) : Nat := (coeffAt s₀.mem (pA s₀ 0) i).toNat

/-- The second polynomial's coefficient `i`. -/
abbrev cB (s₀ : State) (i : Nat) : Nat := (coeffAt s₀.mem (pA s₀ 1) i).toNat

/-- The sum of the first `k` values. -/
def sumV (V : Nat → Nat → Nat) (s₀ : State) : Nat → Nat
  | 0 => 0
  | k + 1 => VG.Proof.MlDsa.X86.Round.sumV V s₀ k + V (VG.Proof.MlDsa.X86.Round.cA s₀ k) (VG.Proof.MlDsa.X86.Round.cB s₀ k)

/-- After `k` coefficients. -/
structure HInv (V : Nat → Nat → Nat) (cnt : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = arg s₀ 0 + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = arg s₀ 1 + BitVec.ofNat 32 (4 * k)
  ebp : s.gpr .ebp = arg s₀ 3 + BitVec.ofNat 32 (4 * k)
  frame : Frame [pR (pA s₀ 3), VG.Proof.MlDsa.X86.Round.aR s₀ 4] (P0 s₀).mem s.mem
  slot : s.mem.readW (argAddr s₀ 2) 32 = arg s₀ 3 + 1024
  out : ∀ i < k, coeffAt s.mem (pA s₀ 3) i = BitVec.ofNat 32 (V (VG.Proof.MlDsa.X86.Round.cA s₀ i) (VG.Proof.MlDsa.X86.Round.cB s₀ i))
  ecx : cnt = true → s.gpr .ecx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Round.sumV V s₀ k)

/-- The output pointer compared with the end of the output. -/
theorem end_cmp' (x : BitVec 32) {X : Nat} (hX : X ≤ 1024) :
    (x + BitVec.ofNat 32 X - (x + 1024) == 0) = decide (X = 1024) := by
  rw [sub_beq_zero, BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat32 (by omega),
    show (1024 : BitVec 32).toNat = 1024 from rfl]
  simp only [Nat.reducePow]
  exact decide_eq_decide.mpr (by constructor <;> intro h <;> omega)

theorem hint_step {core : List Instr} {V : Nat → Nat → Nat} {reqA cnt : Bool} (hc : VG.Proof.MlDsa.X86.Round.Core2 core V reqA cnt)
    {s₀ : State} (hp : VG.Proof.MlDsa.X86.Round.HPre reqA s₀) {k : Nat} (hk : k < 256) {s : State}
    (h : VG.Proof.MlDsa.X86.Round.HInv V cnt s₀ k s) :
    WP isa (.block (core ++ endTail)) s fun s' =>
      VG.Proof.MlDsa.X86.Round.HInv V cnt s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < VG.Spec.MlDsa.n := by rw [n_eq]; exact hk
  have ina : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4 := by
    rw [State.ea, at_, h.esi, ea_cf hp.a_fit hk, h.rd, h.wr, pushed_rd, P0_wr, hp.rd]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  have inb : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4 := by
    rw [State.ea, at_, h.edi, ea_cf hp.b_fit hk, h.rd, h.wr, pushed_rd, P0_wr, hp.rd]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  have va : (s.mem.readW (s.ea (at_ .esi 0)) 32).toNat = VG.Proof.MlDsa.X86.Round.cA s₀ k := by
    rw [State.ea, at_, h.esi, ea_cf hp.a_fit hk, ← VG.Proof.MlDsa.Round.coeffAt_eq,
      in_keep hp.sp h.frame hp.stk_a' (by simp [hp.a_o, hp.a_a]) hk]
  have vb : (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = VG.Proof.MlDsa.X86.Round.cB s₀ k := by
    rw [State.ea, at_, h.edi, ea_cf hp.b_fit hk, ← VG.Proof.MlDsa.Round.coeffAt_eq,
      in_keep hp.sp h.frame hp.stk_b (by simp [hp.b_o, hp.b_a]) hk]
  refine hc _ s _ _ _ (fun e => (hp.a_red e) k hk') (hp.b_red k hk') ina va inb vb fun s₁ o₁ v₁ c₁ => ?_
  have ebp₁ : s₁.gpr .ebp = arg s₀ 3 + BitVec.ofNat 32 (4 * k) := by rw [o₁.gpr _ (by decide), h.ebp]
  have out : InRegions s₁.wr (addr (arg s₀ 3 + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.o_fit hk, o₁.wr, h.wr, P0_wr, hp.wr]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  refine wp_stm ebp₁ out fun s₂ m₂ => wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_addi fun s₅ u₅ =>
    wp_cmpm (B := s₅.gpr .esp) (o := 28) rfl ?_ fun s₆ f₆ z₆ =>
    WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun e => ?_⟩, ?_⟩
  · have hsp : s₅.gpr .esp = (P0 s₀).gpr .esp := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, o₁.gpr _ (by decide),
        h.esp]
    rw [show addr (s₅.gpr .esp) 28 = argAddr s₀ 2 by rw [hsp]; exact VG.Proof.MlKem.X86.P0_argAddr s₀ 2,
      u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, m₂.rd, m₂.wr, o₁.rd, o₁.wr, h.rd, h.wr, pushed_rd, P0_wr, hp.wr]
    exact ⟨VG.Proof.MlDsa.X86.Round.aR s₀ 4, by simp, arg_contains (by omega) hp.sp'⟩
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr,
      o₁.gpr _ (by decide), h.esp]
  · rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, m₂.rd, o₁.rd, h.rd]
  · rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, m₂.wr, o₁.wr, h.wr]
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, o₁.gpr _ (by decide), h.esi]
    exact ptr_next _ _ 4
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, o₁.gpr _ (by decide), h.edi]
    exact ptr_next _ _ 4
  · rw [f₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, ebp₁]
    exact ptr_next _ _ 4
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂.mem, addr_cf hp.o_fit hk, o₁.mem]
    exact h.frame.writeW (by simp) _ (coeff_contains _ hk')
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂.mem, addr_cf hp.o_fit hk, o₁.mem,
      Mem.readW_writeW_sep (Region.Disjoint.sep hp.o_a.symm (arg_contains (by omega) hp.sp')
        (coeff_contains _ hk')) (by decide), h.slot]
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂.mem, addr_cf hp.o_fit hk, o₁.mem,
      coeffAt_writeW _ _ (by rw [n_eq]; omega) hk']
    by_cases e : k = i
    · subst e; rw [ite_eq_left rfl]; exact eq_ofNat_of_toNat v₁
    · rw [ite_eq_right e]; exact h.out i (by omega)
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, c₁ e,
      h.ecx e, eq_ofNat_of_toNat v₁, ← BitVec.ofNat_add]
    rfl
  · simp only [eval, z₆, Option.map_some]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, addr_cf hp.o_fit hk, o₁.mem,
      show addr (s₅.gpr .esp) 28 = argAddr s₀ 2 by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, o₁.gpr _ (by decide),
          h.esp]; exact VG.Proof.MlKem.X86.P0_argAddr s₀ 2,
      Mem.readW_writeW_sep (Region.Disjoint.sep hp.o_a.symm (arg_contains (by omega) hp.sp')
        (coeff_contains _ hk')) (by decide), h.slot, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      m₂.gpr, ebp₁, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.MlKem.X86.add_ofNat_add,
      VG.Proof.MlDsa.X86.Round.end_cmp' _ (by omega)]
    by_cases e : k + 1 < 256
    · rw [decide_eq_false (by omega), decide_eq_true e]; rfl
    · rw [decide_eq_true (by omega), decide_eq_false e]; rfl

theorem hint_loop {core : List Instr} {V : Nat → Nat → Nat} {reqA cnt : Bool} (hc : VG.Proof.MlDsa.X86.Round.Core2 core V reqA cnt)
    (E : State → Prop) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp]) (.block (core ++ endTail)) hh).isSome = true) :
    Piece (VG.Proof.MlDsa.X86.Round.HPre reqA) VG.Proof.MlDsa.X86.Round.HPub (fun s₀ s => VG.Proof.MlDsa.X86.Round.HS1 s₀ s ∧ E s₀) (fun s₀ s => VG.Proof.MlDsa.X86.Round.HInv V cnt s₀ 256 s ∧ E s₀)
      (.loop (.block (core ++ endTail)) .ne) := by
  refine (Piece.loop (fun k s₀ s => VG.Proof.MlDsa.X86.Round.HInv V cnt s₀ k s ∧ E s₀) (by decide) fun k hk =>
    Piece.taint [.esp, .esi, .edi, .ebp]
      (fun s₀ s hp ⟨h, he⟩ => (VG.Proof.MlDsa.X86.Round.hint_step hc hp hk h).mono fun _ ⟨h', c'⟩ => ⟨⟨h', he⟩, c'⟩)
      (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, hq.2.1]
        · rw [h.edi, h'.edi, hq.2.2.1]
        · rw [h.ebp, h'.ebp, hq.2.2.2.2]) ht).mono (fun s₀ s _ ⟨h, he⟩ => ⟨?_, he⟩) fun _ _ _ h => h
  exact ⟨h.esp, h.rd, h.wr, by rw [h.esi]; simp, by rw [h.edi]; simp, by rw [h.ebp]; simp,
    h.frame.mono (by simp), h.slot, fun i hi => absurd hi (by omega), fun _ => by rw [h.ecx]; rfl⟩

/-- `γ₂` is `(q - 1)/32`: the branch the code takes. -/
def hG32 (s₀ : State) : Bool := arg s₀ 2 == BitVec.ofNat 32 g32

/-- Both branches, for the core `core g` computing `Vf g`. -/
theorem hint_ite {core : Nat → List Instr} {Vf : Nat → Nat → Nat → Nat} {reqA cnt : Bool}
    (hc : ∀ g ∈ gamma2s, VG.Proof.MlDsa.X86.Round.Core2 (core g) (Vf g) reqA cnt)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp]) (.block (core g32 ++ endTail)) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp]) (.block (core g88 ++ endTail)) h₂).isSome = true) :
    Piece (VG.Proof.MlDsa.X86.Round.HPre reqA) VG.Proof.MlDsa.X86.Round.HPub VG.Proof.MlDsa.X86.Round.HS1 (fun s₀ s => VG.Proof.MlDsa.X86.Round.HInv (Vf (arg s₀ 2).toNat) cnt s₀ 256 s)
      (.ite .e (.loop (.block (core g32 ++ endTail)) .ne) (.loop (.block (core g88 ++ endTail)) .ne)) := by
  refine Piece.ite VG.Proof.MlDsa.X86.Round.hG32 (fun s₀ s _ h => h.zf) (fun s₀ s₀' _ _ hq => by simp only [VG.Proof.MlDsa.X86.Round.hG32, hq.2.2.2.1]) ?_ ?_
  · refine (VG.Proof.MlDsa.X86.Round.hint_loop (hc g32 g32_mem) (fun s₀ => VG.Proof.MlDsa.X86.Round.hG32 s₀ = true) t₁).mono (fun _ _ _ h => h)
      fun s₀ s hp ⟨h, he⟩ => ?_
    rcases gamma_cases hp.g2 with ⟨_, e⟩ | ⟨e', _⟩
    · rw [e]; exact h
    · rw [VG.Proof.MlDsa.X86.Round.hG32, e'] at he; exact absurd he (by decide)
  · refine (VG.Proof.MlDsa.X86.Round.hint_loop (hc g88 g88_mem) (fun s₀ => VG.Proof.MlDsa.X86.Round.hG32 s₀ = false) t₂).mono (fun _ _ _ h => h)
      fun s₀ s hp ⟨h, he⟩ => ?_
    rcases gamma_cases hp.g2 with ⟨e', _⟩ | ⟨_, e⟩
    · rw [VG.Proof.MlDsa.X86.Round.hG32, e'] at he; exact absurd he (by decide)
    · rw [e]; exact h

theorem hW {reqA : Bool} {s₀ : State} (hp : VG.Proof.MlDsa.X86.Round.HPre reqA s₀) :
    ∀ r ∈ [pR (pA s₀ 3), VG.Proof.MlDsa.X86.Round.aR s₀ 4], (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨by rw [← VG.Proof.MlDsa.X86.Round.stk_eq hp.sp]; exact hp.stk_o, hp.ret_o⟩
  · exact ⟨by rw [← VG.Proof.MlDsa.X86.Round.stk_eq hp.sp]; exact hp.stk_a, hp.ret_a⟩

end VG.Proof.MlDsa.X86.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Round.HintF`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_make_hint` and `vg_mldsa_use_hint`

Both functions are the prologue and the loops of `Hint.lean`; `makeHint` then
returns the count in `ecx`, which is the number of 1s (`sumV_ones`).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q gamma2s coeffAt Reduced polyAt HintIs NatPolyIs hintOnes hintAt makeHintContract
  makeHintSig useHintContract useHintSig)
open VG.Proof.MlDsa.Round (coeffAddr pR n_eq q_eq polyAt_val hintIs_of_toNat natPolyIs_of_toNat zipWith_get
  hintAt_get onesFrom onesFrom_step onesFrom_n hintOnes_single makeHint_eq useHint_eq)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_esp P0_wr frameR retR LeafPost LeafEnd Piece satState toNat_ofNat32
  setWidth_append32)

theorem HPre.of_mh {s₀ : State} (h : (makeHintContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Round.HPre true s₀ := by
  sig_pre [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    fun _ => h22, h23⟩

theorem HPre.of_uh {s₀ : State} (h : (useHintContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Round.HPre false s₀ := by
  sig_pre [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    fun h => absurd h (by decide), h22⟩

/-! ## `useHint` -/

theorem uh_piece : Piece (VG.Proof.MlDsa.X86.Round.HPre false) VG.Proof.MlDsa.X86.Round.HPub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => VG.Proof.MlDsa.X86.Round.HInv (VG.Proof.MlDsa.X86.Round.uhV (arg s₀ 2).toNat) false s₀ 256 s) s₀ s') useHint :=
  Piece.leaf (fun s₀ => [pR (pA s₀ 3), VG.Proof.MlDsa.X86.Round.aR s₀ 4]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩) (fun _ hp => VG.Proof.MlDsa.X86.Round.hW hp) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (VG.Proof.MlDsa.X86.Round.hintInit_piece false) (VG.Proof.MlDsa.X86.Round.hint_ite (fun g hg => VG.Proof.MlDsa.X86.Round.uhCore_spec hg) (by taint_decide)
      (by taint_decide))).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem uhV_lt {g : Nat} (hg : g ∈ gamma2s) (a b : Nat) : VG.Proof.MlDsa.X86.Round.uhV g a b < 2 ^ 32 := by
  have hm : 0 < VG.Proof.MlDsa.Round.hbM g := by
    rcases VG.Proof.MlDsa.Round.mem_gamma2s hg with e | e <;> rw [e] <;> decide
  have : VG.Proof.MlDsa.Round.hbM g ≤ 44 := by
    rcases VG.Proof.MlDsa.Round.mem_gamma2s hg with e | e <;> rw [e] <;> decide
  unfold VG.Proof.MlDsa.X86.Round.uhV
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hm) (by omega)

theorem uh_post {s₀ s : State} (hp : VG.Proof.MlDsa.X86.Round.HPre false s₀) (h : VG.Proof.MlDsa.X86.Round.HInv (VG.Proof.MlDsa.X86.Round.uhV (arg s₀ 2).toNat) false s₀ 256 s) :
    NatPolyIs s.mem (pA s₀ 3) (Vector.zipWith (fun hj rj => (VG.Spec.MlDsa.useHint (arg s₀ 2).toNat hj rj).toNat)
      ((hintAt s₀.mem (pA s₀ 0) 1).headD (Vector.replicate VG.Spec.MlDsa.n false)) (polyAt s₀.mem (pA s₀ 1))) := by
  refine natPolyIs_of_toNat fun i hi => ?_
  rw [h.out i hi, zipWith_get _ _ _ hi, hintAt_get _ _ hi, useHint_eq hp.g2, polyAt_val hp.b_red hi,
    toNat_ofNat32 (VG.Proof.MlDsa.X86.Round.uhV_lt hp.g2 _ _), Int.toNat_natCast]
  unfold VG.Proof.MlDsa.X86.Round.uhV
  congr 1
  by_cases e : coeffAt s₀.mem (pA s₀ 0) i = 0
  · have e' : VG.Proof.MlDsa.X86.Round.cA s₀ i = 0 := by simp [VG.Proof.MlDsa.X86.Round.cA, e]
    have d : decide (coeffAt s₀.mem (pA s₀ 0) i ≠ 0) = false := decide_eq_false fun h => h e
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h' e')]
    simp only [d, Bool.false_eq_true, ↓reduceIte]
  · have e' : VG.Proof.MlDsa.X86.Round.cA s₀ i ≠ 0 := fun h' => e (BitVec.eq_of_toNat_eq h')
    have d : decide (coeffAt s₀.mem (pA s₀ 0) i ≠ 0) = true := decide_eq_true e
    rw [ite_eq_left_of_eq_true _ _ (eq_true e')]
    simp only [d, ↓reduceIte]

/-- Memory with the arguments `0x400`, `0x800`, `(q - 1)/32` and `0` at `0x5004`. -/
def hintSatMem : Mem := fun a =>
  if a = 0x5005 then 4 else if a = 0x5009 then 8 else if a = 0x500d then 0xff else if a = 0x500e then 3 else 0

theorem hintSat_zero (a : Addr) (ha : a.toNat < 0x5000) : VG.Proof.MlDsa.X86.Round.hintSatMem a = 0 := by
  simp only [VG.Proof.MlDsa.X86.Round.hintSatMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)]

theorem useHint_verified : Verified X86.target useHint (useHintContract X86.abi 16) := by
  refine Piece.verified ((uh_piece.pre_mono (fun _ h => HPre.of_uh h) fun s s' _ _ h => by
      sig_pub [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact VG.Proof.MlDsa.X86.Round.uh_post (HPre.of_uh h₀) hinv
  · let st := satState VG.Proof.MlDsa.X86.Round.hintSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 0x800 := by decide
    have a2 : arg st 2 = 261888 := by decide
    have a3 : arg st 3 = 0 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, reduced_zero VG.Proof.MlDsa.X86.Round.hintSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

/-! ## `makeHint` -/

/-- After the loops, the count to `eax`. -/
def MhEnd (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86.Round.HInv (VG.Proof.MlDsa.X86.Round.mhV (arg s₀ 2).toNat) true s₀ 256 s ∧ s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Round.sumV (VG.Proof.MlDsa.X86.Round.mhV (arg s₀ 2).toNat) s₀ 256)

theorem mh_piece : Piece (VG.Proof.MlDsa.X86.Round.HPre true) VG.Proof.MlDsa.X86.Round.HPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlDsa.X86.Round.MhEnd s₀) s₀ s')
    makeHint :=
  Piece.leaf (fun s₀ => [pR (pA s₀ 3), VG.Proof.MlDsa.X86.Round.aR s₀ 4]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩) (fun _ hp => VG.Proof.MlDsa.X86.Round.hW hp) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (VG.Proof.MlDsa.X86.Round.hintInit_piece true) (Piece.seq (VG.Proof.MlDsa.X86.Round.hint_ite (fun g hg => VG.Proof.MlDsa.X86.Round.mhCore_spec hg) (by taint_decide)
      (by taint_decide)) (Piece.taint [] (fun s₀ s hp h => wp_mov fun s₁ u₁ => WP.block_nil_iff.mpr
        ⟨⟨by rw [u₁.other _ (by decide), h.esp], by rw [u₁.rd, h.rd], by rw [u₁.wr, h.wr],
          by rw [u₁.other _ (by decide), h.esi], by rw [u₁.other _ (by decide), h.edi],
          by rw [u₁.other _ (by decide), h.ebp], by rw [u₁.mem]; exact h.frame, by rw [u₁.mem]; exact h.slot,
          fun i hi => by rw [u₁.mem]; exact h.out i hi, fun e => by rw [u₁.other _ (by decide)]; exact h.ecx e⟩,
          by rw [u₁.gpr]; exact h.ecx rfl⟩)
        (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)))).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h⟩)

theorem mhV_le {g a b : Nat} : VG.Proof.MlDsa.X86.Round.mhV g a b ≤ 1 := by unfold VG.Proof.MlDsa.X86.Round.mhV; split <;> omega

theorem sumV_le {g : Nat} {s₀ : State} : ∀ k, VG.Proof.MlDsa.X86.Round.sumV (VG.Proof.MlDsa.X86.Round.mhV g) s₀ k ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by have := VG.Proof.MlDsa.X86.Round.sumV_le (g := g) (s₀ := s₀) k; have := @VG.Proof.MlDsa.X86.Round.mhV_le g (VG.Proof.MlDsa.X86.Round.cA s₀ k) (VG.Proof.MlDsa.X86.Round.cB s₀ k); simp only [VG.Proof.MlDsa.X86.Round.sumV]; omega

/-- The hint of `makeHint`, coefficient by coefficient. -/
theorem mh_get {s₀ : State} (hp : VG.Proof.MlDsa.X86.Round.HPre true s₀) {i : Nat} (hi : i < 256) :
    ((Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
      (polyAt s₀.mem (pA s₀ 1)))[i]!).toNat = VG.Proof.MlDsa.X86.Round.mhV (arg s₀ 2).toNat (VG.Proof.MlDsa.X86.Round.cA s₀ i) (VG.Proof.MlDsa.X86.Round.cB s₀ i) := by
  have hi' : i < VG.Spec.MlDsa.n := by rw [n_eq]; exact hi
  rw [zipWith_get _ _ _ hi', makeHint_eq hp.g2, polyAt_val (hp.a_red rfl) hi', polyAt_val hp.b_red hi', VG.Proof.MlDsa.X86.Round.mhV]
  by_cases e : hbV (arg s₀ 2).toNat (VG.Proof.MlDsa.X86.Round.cB s₀ i) = hbV (arg s₀ 2).toNat ((VG.Proof.MlDsa.X86.Round.cB s₀ i + VG.Proof.MlDsa.X86.Round.cA s₀ i) % q)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true e)]
    simp only [hbV] at e
    simp [e]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
    simp only [hbV] at e
    simp [e]

theorem sumV_ones {s₀ : State} (hp : VG.Proof.MlDsa.X86.Round.HPre true s₀) :
    ∀ k ≤ 256, VG.Proof.MlDsa.X86.Round.sumV (VG.Proof.MlDsa.X86.Round.mhV (arg s₀ 2).toNat) s₀ k + onesFrom (Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat)
      (polyAt s₀.mem (pA s₀ 0)) (polyAt s₀.mem (pA s₀ 1))) k =
      onesFrom (Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
        (polyAt s₀.mem (pA s₀ 1))) 0
  | 0, _ => Nat.zero_add _
  | k + 1, hk => by
    rw [← VG.Proof.MlDsa.X86.Round.sumV_ones hp k (by omega), onesFrom_step _ (show k < VG.Spec.MlDsa.n by rw [n_eq]; omega), VG.Proof.MlDsa.X86.Round.mh_get hp (by omega)]
    simp only [VG.Proof.MlDsa.X86.Round.sumV]
    omega

theorem mh_post {s₀ s : State} (hp : VG.Proof.MlDsa.X86.Round.HPre true s₀) (h : VG.Proof.MlDsa.X86.Round.MhEnd s₀ s) :
    HintIs s.mem (pA s₀ 3) 1 [Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
      (polyAt s₀.mem (pA s₀ 1))] ∧
    (s.gpr .eax).toNat = hintOnes [Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
      (polyAt s₀.mem (pA s₀ 1))] := by
  refine ⟨hintIs_of_toNat fun j hj => ?_, ?_⟩
  · rw [h.1.out j hj]
    exact congrArg (BitVec.ofNat 32) (VG.Proof.MlDsa.X86.Round.mh_get hp hj).symm
  · rw [h.2, toNat_ofNat32 (by have := VG.Proof.MlDsa.X86.Round.sumV_le (g := (arg s₀ 2).toNat) (s₀ := s₀) 256; omega), hintOnes_single,
      ← VG.Proof.MlDsa.X86.Round.sumV_ones hp 256 (Nat.le_refl _), show (256 : Nat) = VG.Spec.MlDsa.n from rfl, onesFrom_n, Nat.add_zero]

theorem makeHint_verified : Verified X86.target makeHint (makeHintContract X86.abi 16) := by
  refine Piece.verified ((mh_piece.pre_mono (fun _ h => HPre.of_mh h) fun s s' _ _ h => by
      sig_pub [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    have hp := HPre.of_mh h₀
    have ⟨p1, p2⟩ := VG.Proof.MlDsa.X86.Round.mh_post hp hinv
    sig_post [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm, setWidth_append32, hax]
    exact ⟨p1, p2⟩
  · let st := satState VG.Proof.MlDsa.X86.Round.hintSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 0x800 := by decide
    have a2 : arg st 2 = 261888 := by decide
    have a3 : arg st 3 = 0 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, reduced_zero VG.Proof.MlDsa.X86.Round.hintSat_zero 0x400 (by decide),
      reduced_zero VG.Proof.MlDsa.X86.Round.hintSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.X86.Round

end
