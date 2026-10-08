import VerifiedGarbage.Impl.Camellia.X86_64.Layers
import VerifiedGarbage.Proof.Camellia.Bitsliced
import VerifiedGarbage.Proof.Framework.X86_64.Linear

/-!
# The linear layers of bitsliced Camellia on x86-64, by evaluation

Each layer is checked by evaluation over the lane domain
(`Framework/X86_64/Linear.lean`): the kernel runs it on the input words as
atoms (the state registers are words 0–7, the subkey's planes at `kp`
words 8–23) and compares every output bit with the XOR of input bits given
here. The masks of the layers are constants in their slots
(`layerMasks`), which `linK_ok` takes as known.

Position `p = 8c + b` of a plane is byte `c` of block `b`, and byte `c`
holds the half's byte `pos c`.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1)
open VG.Proof.Camellia (toBsG fromBsG keyInG outPG)

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
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, (is.all fun i => i.dst != some r) = true → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (LaneRel k (assign W (2 ^ k))) c (linExt xb) (linEnvG ins sins cs) s := by
    refine ⟨fun r a h => ?_, fun j a hj h => ?_, fun j a hj h => ?_⟩
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
    fun r hr => p.other r (by simp [hr]), p.frame⟩
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

/-- The slots below the table, the masks among them; the subkey's 16 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := keySlot, ext := kp, exts := 16 }

/-- The state registers hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

theorem toBs_check :
    check (lanes 64 9) layerCfg (linExt 8) toBs (linEnvG qIns [] []) (linPostG 9 (qOuts toBsG) [] [] (linEnvG qIns [] [])) = true := by
  decide +kernel

theorem fromBs_check :
    check (lanes 64 9) layerCfg (linExt 8) fromBs (linEnvG qIns [] []) (linPostG 9 (qOuts fromBsG) [] [] (linEnvG qIns [] [])) = true := by
  decide +kernel

/-- The masks' slots. -/
def maskSlots : List Nat := layerMasks.map (·.1)

/-- The slots of both halves, input words 24–39 (after the subkey's). -/
def halvesIns : List (Nat × Nat) := (List.range 16).map fun j => (d1Slot + j, 24 + j)

def keyInEnv : Env (Nat × Nat) := linEnvG qIns halvesIns layerMasks

theorem keyIn0_check :
    check (lanes 64 12) layerCfg (linExt 8) (keyXor 0 ++ inSel) keyInEnv
      (linPostG 12 (qOuts (keyInG 0)) [] (maskSlots ++ halvesIns.map (·.1)) keyInEnv) = true := by
  decide +kernel

theorem keyIn8_check :
    check (lanes 64 12) layerCfg (linExt 8) (keyXor 8 ++ inSel) keyInEnv
      (linPostG 12 (qOuts (keyInG 8)) [] (maskSlots ++ halvesIns.map (·.1)) keyInEnv) = true := by
  decide +kernel

/-- Both halves' planes, in slots 64–79, are input words 8–23. -/
def bothIns : List (Nat × Nat) := (List.range 16).map fun j => (d1Slot + j, 8 + j)

/-- The Feistel XOR into the half at slot `d`: plane `j` of both the state
and that half is the XOR of the two. -/
def feistelG (d j p : Nat) : List Nat := [64 * j + p, 64 * (8 + (d - d1Slot) + j) + p]

def bothEnv : Env (Nat × Nat) := linEnvG qIns bothIns layerMasks

/-- The slots the Feistel XOR into the half at `d` keeps: the masks and the
other half. -/
def feistelKeep (d : Nat) : List Nat :=
  maskSlots ++ (List.range 8).map fun j => (if d = d1Slot then d2Slot else d1Slot) + j

theorem feistel1_check :
    check (lanes 64 12) layerCfg (linExt 24) (feistel d1Slot) bothEnv
      (linPostG 12 (qOuts (feistelG d1Slot)) ((List.range 8).map fun j => (d1Slot + j, feistelG d1Slot j))
        (feistelKeep d1Slot) bothEnv) = true := by
  decide +kernel

theorem feistel2_check :
    check (lanes 64 12) layerCfg (linExt 24) (feistel d2Slot) bothEnv
      (linPostG 12 (qOuts (feistelG d2Slot)) ((List.range 8).map fun j => (d2Slot + j, feistelG d2Slot j))
        (feistelKeep d2Slot) bothEnv) = true := by
  decide +kernel

theorem outP_check :
    check (lanes 64 12) layerCfg (linExt 24) (outSel ++ pLayer) bothEnv
      (linPostG 12 (qOuts outPG) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.X86_64
