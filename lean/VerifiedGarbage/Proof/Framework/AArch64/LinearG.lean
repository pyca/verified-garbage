import VerifiedGarbage.Proof.Framework.AArch64.Linear

/-!
# AArch64: linear layers with inputs, constants and outputs in slots

`linear_ok` (`Linear.lean`) with input words in registers and in slots of
the scratch buffer, constants in slots, outputs in registers and in slots,
and slots the code keeps (`linEnvG`, `linPostG`, `linG_ok`). Camellia's and
SM4's bitsliced linear layers are checked with these.
-/

namespace VG.AArch64.Straight

open VG.Bitslice

/-- The registers `ins` and the slots `sins` hold input words, and the slots
`cs` constants. -/
def linEnvG (ins : List (Reg × Nat)) (sins : List (Nat × Nat)) (cs : List (Nat × BitVec 64)) :
    Env (Nat × Nat) :=
  { reg := fun r => (ins.find? (·.1 == r)).map (inWord ·.2)
    slot := fun k => match sins.find? (·.1 == k) with
      | some ki => some (inWord ki.2)
      | none => (cs.find? (·.1 == k)).map fun kv => (kv.2.toNat, 0) }

/-- `linPost`, each output slot `k` holds `outWord g`, and the slots `keep`
hold what `e₀` gives them. -/
def linPostG (k : Nat) (outs : List (Reg × (Nat → List Nat))) (souts : List (Nat × (Nat → List Nat)))
    (keep : List Nat) (e₀ : Env (Nat × Nat)) (e : Env (Nat × Nat)) : Bool :=
  linPost k outs e &&
    (souts.all fun o => e.slot o.1 == some (outWord o.2) &&
      (List.range 64).all fun p => (o.2 p).all (· < 2 ^ k)) &&
    keep.all fun j => (e₀.slot j).isSome && e.slot j == e₀.slot j

/-- `linear_ok`, with input words and constants in slots, and output slots. -/
theorem linG_ok {k xb : Nat} {c : Cfg} {is : List Instr} {ins : List (Reg × Nat)}
    {sins : List (Nat × Nat)} {cs : List (Nat × BitVec 64)} {outs : List (Reg × (Nat → List Nat))}
    {souts : List (Nat × (Nat → List Nat))}
    {keep : List Nat}
    (hchk : check (lanes 64 k) c (linExt xb) is (linEnvG ins sins cs)
      (linPostG k outs souts keep (linEnvG ins sins cs)) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 64)
    (hin : ∀ r i, (r, i) ∈ ins → 64 * i + 64 ≤ 2 ^ k ∧ W i = s.gpr r)
    (hsin : ∀ j i, (j, i) ∈ sins →
      j < c.slots ∧ 64 * i + 64 ≤ 2 ^ k ∧ W i = s.mem.readW (wordAddr (s.gpr c.base) j) 64)
    (hcs : ∀ kv ∈ cs, kv.1 < c.slots ∧ s.mem.readW (wordAddr (s.gpr c.base) kv.1) 64 = kv.2)
    (hext : ∀ j < c.exts,
      64 * (xb + j) + 64 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 64) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ r g, (r, g) ∈ outs → ∀ p < 64, (s'.gpr r).getLsbD p = xorBits W (g p)) ∧
      (∀ j g, (j, g) ∈ souts → j < c.slots →
        ∀ p < 64, (s'.mem.readW (wordAddr (s.gpr c.base) j) 64).getLsbD p = xorBits W (g p)) ∧
      (∀ j ∈ keep, j < c.slots →
        s'.mem.readW (wordAddr (s.gpr c.base) j) 64 = s.mem.readW (wordAddr (s.gpr c.base) j) 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, (is.all fun i => dstOf i != some r) = true → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem ∧ s'.gpr c.base = s.gpr c.base ∧
      s'.gpr c.ext = s.gpr c.ext := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (LaneRel k (assign W (2 ^ k))) c (linExt xb) (linEnvG ins sins cs) s := by
    refine ⟨fun r a h => ?_, fun j a hj h => ?_, fun j a hj h => ?_, fun _ _ h => by cases h⟩
    · simp only [linEnvG, Option.map_eq_some_iff] at h
      obtain ⟨⟨r', i⟩, hf, rfl⟩ := h
      have hr : r' = r := by simpa using List.find?_some hf
      subst hr
      obtain ⟨h1, h2⟩ := hin r' i (List.mem_of_find?_eq_some hf)
      rw [← h2]; exact inWord_rel W h1
    · simp only [linEnvG] at h
      split at h
      · rename_i ki hf
        simp only [Option.some.injEq] at h; subst h
        have hk : ki.1 = j := by simpa using List.find?_some hf
        obtain ⟨-, h1, h2⟩ := hsin ki.1 ki.2 (List.mem_of_find?_eq_some hf)
        rw [← hk, ← h2]; exact inWord_rel W h1
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨k', v⟩, hf, rfl⟩ := h
        have hk : k' = j := by simpa using List.find?_some hf
        subst hk
        rw [(hcs _ (List.mem_of_find?_eq_some hf)).2]
        exact lanes_sound.const rfl
    · simp only [linExt, Option.some.injEq] at h; subst h
      obtain ⟨h1, h2⟩ := hext j hj
      rw [← h2]; exact inWord_rel W h1
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  simp only [linPostG, Bool.and_eq_true] at hpost
  obtain ⟨⟨hpost, hspost⟩, hkeep⟩ := hpost
  refine ⟨s', hs', fun r g hrg q hq => ?_, fun j g hjg hj q hq => ?_, fun j hj hjs => ?_, p.rd, p.wr,
    p.sp, fun r hr => p.other r (by simp [hr]), p.frame, p.base, p.ext⟩
  · have h := List.all_eq_true.mp hpost (r, g) hrg
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact outWord_rel (fun p hp a ha => h.2 p hp a ha) (p.rel.reg r _ h.1) q hq
  · have h := List.all_eq_true.mp hspost (j, g) hjg
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    rw [← p.base]
    exact outWord_rel (fun p hp a ha => h.2 p hp a ha) (p.rel.slot j _ hj h.1) q hq
  · have h := List.all_eq_true.mp hkeep j hj
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
    obtain ⟨⟨a, ha⟩, he⟩ := h
    have r₁ := p.rel.slot j a hjs (he.trans ha)
    have r₀ := hrel.slot j a hjs ha
    rw [p.base] at r₁
    exact BitVec.eq_of_getLsbD_eq fun q hq => by rw [r₁.2 q hq, r₀.2 q hq]

/-! ## The checks -/

end VG.AArch64.Straight
