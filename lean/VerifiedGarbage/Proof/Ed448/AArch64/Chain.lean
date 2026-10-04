import VerifiedGarbage.Proof.Ed25519.AArch64.Step

/-!
# Ed448 on AArch64: carry chains along registers

The value of a list of registers, lowest word first (`rv`), and a chain of
`adcs` (`adcs_ok`) or of an `adds` and `adcs` (`adds_ok`) along registers,
proven once by induction on the chain: the destinations' value plus the
carry out is the sum of the sources' values. A chain may write a register
it reads only when no later instruction of the chain reads or writes it
(`ChainOk`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- The value of the registers `rs`, lowest first. -/
def rv (s : State) : List Reg → Nat
  | [] => 0
  | r :: rs => (s.gpr r).toNat + 2 ^ 64 * rv s rs

theorem pow64_succ (n : Nat) : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem rv_lt (s : State) : ∀ rs : List Reg, rv s rs < 2 ^ (64 * rs.length)
  | [] => by simp [rv]
  | r :: rs => by
    have h1 := (s.gpr r).isLt
    have h2 := rv_lt s rs
    rw [rv, List.length_cons, pow64_succ]
    generalize 2 ^ (64 * rs.length) = Q at h2 ⊢
    have : 2 ^ 64 * rv s rs + 2 ^ 64 ≤ 2 ^ 64 * Q := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
    omega

theorem rv_congr {s t : State} : ∀ {rs : List Reg}, (∀ r ∈ rs, t.gpr r = s.gpr r) → rv t rs = rv s rs
  | [], _ => rfl
  | r :: rs, h => by
    rw [rv, rv, h r List.mem_cons_self, rv_congr fun r' hr' => h r' (List.mem_cons_of_mem _ hr')]

theorem Keeps.rv_eq {rs : List Reg} {s t : State} (h : Keeps rs s t) {X : List Reg}
    (hX : ∀ r ∈ X, r ∉ rs) : rv t X = rv s X :=
  rv_congr fun r hr => h.gpr r (hX r hr)

/-! ## Chains -/

/-- `adcs d, n, m` for each `(d, n, m)`. -/
def adcsOf (ts : List (Reg × Reg × Reg)) : List Instr := ts.map fun t => .adcs .x t.1 t.2.1 t.2.2

/-- No instruction of a chain reads or writes a register an earlier one wrote. -/
def ChainOk : List (Reg × Reg × Reg) → Bool
  | [] => true
  | t :: ts => ts.all (fun u => u.1 != t.1 && u.2.1 != t.1 && u.2.2 != t.1) && ChainOk ts

def dsts (ts : List (Reg × Reg × Reg)) : List Reg := ts.map (·.1)
def lhs (ts : List (Reg × Reg × Reg)) : List Reg := ts.map (·.2.1)
def rhs (ts : List (Reg × Reg × Reg)) : List Reg := ts.map (·.2.2)

theorem addWithCarry_val (a b : BitVec 64) (c : Bool) :
    (a + b + BitVec.ofNat 64 c.toNat).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  simpa only [Ed25519.Word64.addCarry, Ed25519.Word64.carryOut] using
    Ed25519.Word64.addCarry_value a b c

theorem not_mem_map {ts : List (Reg × Reg × Reg)} {f : Reg × Reg × Reg → Reg} {d : Reg}
    (h : ∀ u ∈ ts, f u ≠ d) : ∀ r ∈ ts.map f, r ≠ d := by
  intro r hr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  exact h u hu

/-- A chain of `adcs`, from the carry `s.c`. -/
theorem adcs_ok : ∀ (ts : List (Reg × Reg × Reg)) (s : State), ChainOk ts = true →
    WP isa (.block (adcsOf ts)) s fun t =>
      rv t (dsts ts) + 2 ^ (64 * ts.length) * t.c.toNat = rv s (lhs ts) + rv s (rhs ts) + s.c.toNat ∧
      Keeps (dsts ts) s t
  | [], s, _ => WP.block_nil ⟨by simp [rv, dsts, lhs, rhs], Keeps.refl _ _⟩
  | (d, n, m) :: ts, s, h => by
    simp only [ChainOk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hd, hok⟩ := h
    rw [adcsOf, List.map_cons, WP.block_cons_iff]
    let s1 := s.addWithCarry .x d (s.gpr n) (s.gpr m) s.c
    refine ⟨s1, by simp only [exec, read_x]; rfl, ?_⟩
    refine WP.mono (adcs_ok ts s1 hok) fun t ⟨e, k⟩ => ?_
    have hdd : d ∉ dsts ts := fun hm => not_mem_map (fun u hu => (hd u hu).1.1) d hm rfl
    have g1 : t.gpr d = s1.gpr d := k.gpr d hdd
    have k1 : ∀ r, r ≠ d → s1.gpr r = s.gpr r := fun r hr => by
      simp only [s1, RegUpd.gpr_addWithCarry, hr, ite_false]
    have l1 : rv s1 (lhs ts) = rv s (lhs ts) :=
      rv_congr fun r hr => k1 r (not_mem_map (fun u hu => (hd u hu).1.2) r hr)
    have r1 : rv s1 (rhs ts) = rv s (rhs ts) :=
      rv_congr fun r hr => k1 r (not_mem_map (fun u hu => (hd u hu).2) r hr)
    have v1 := addWithCarry_val (s.gpr n) (s.gpr m) s.c
    have d1 : s1.gpr d = s.gpr n + s.gpr m + BitVec.ofNat 64 s.c.toNat := by
      simp only [s1, RegUpd.gpr_addWithCarry, ite_true, BitVec.setWidth_eq]
    have c1 : s1.c = decide (2 ^ 64 ≤ (s.gpr n).toNat + (s.gpr m).toNat + s.c.toNat) := rfl
    rw [l1, r1, c1] at e
    refine ⟨?_, ⟨fun r hr => ?_, k.mem, k.rd, k.wr, k.sp⟩⟩
    · simp only [dsts, lhs, rhs, List.map_cons, rv, List.length_cons]
      rw [g1, d1, pow64_succ, Nat.mul_assoc]
      simp only [dsts, lhs, rhs] at e
      generalize 2 ^ (64 * ts.length) * t.c.toNat = Y at e ⊢
      generalize (s.gpr n + s.gpr m + BitVec.ofNat 64 s.c.toNat).toNat = D at v1 ⊢
      omega
    · simp only [dsts, List.map_cons, List.mem_cons, not_or] at hr
      rw [k.gpr r hr.2, k1 r hr.1]

/-- A chain of an `adds` and `adcs`. -/
theorem adds_ok (d n m : Reg) (ts : List (Reg × Reg × Reg)) (s : State)
    (h : ChainOk ((d, n, m) :: ts) = true) :
    WP isa (.block (.adds .x d n m :: adcsOf ts)) s fun t =>
      rv t (d :: dsts ts) + 2 ^ (64 * (ts.length + 1)) * t.c.toNat =
        rv s (n :: lhs ts) + rv s (m :: rhs ts) ∧
      Keeps (d :: dsts ts) s t := by
  have he : isa.exec (.adds .x d n m) s = isa.exec (.adcs .x d n m) { s with c := false } := rfl
  have e := adcs_ok ((d, n, m) :: ts) { s with c := false } h
  rw [adcsOf, List.map_cons, WP.block_cons_iff] at e
  rw [WP.block_cons_iff, he]
  obtain ⟨s1, h1, w⟩ := e
  refine ⟨s1, h1, WP.mono w fun t ⟨v, k⟩ => ⟨?_, ⟨fun r hr => k.gpr r hr, k.mem, k.rd, k.wr, k.sp⟩⟩⟩
  simpa only [dsts, lhs, rhs, List.map_cons, List.length_cons, Bool.toNat_false, Nat.add_zero,
    rv_congr (s := s) (t := { s with c := false }) (fun _ _ => rfl)] using v

end VG.Proof.Ed448.AArch64
