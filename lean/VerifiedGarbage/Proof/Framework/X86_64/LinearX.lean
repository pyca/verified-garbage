module

public import VerifiedGarbage.Proof.Framework.X86_64.StraightX
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms

/-!
# x86-64: linear layers of bitsliced SSE2 code, quadword by quadword

`Linear.lean` for the quadword-lane evaluator (`StraightX`): straight-line
SSE2 code that only moves and XORs bits within each quadword, and masks them
with constants, is checked by evaluating it over the lane domain
(`Bitslice.lanes`), on input words given as atoms (bit `t` of input word `i`
is atom `64 i + t`). The inputs are registers (`ins`), whose quadword `l` is
input word `i` of lane `l` (`W l i`). `linear_ok` turns a successful check
into a statement about the machine: bit `p` of quadword `l` of each output
register is the XOR of the input bits `g p` of lane `l`.
-/

@[expose] public section

namespace VG.X86_64.StraightX

open VG.Bitslice

/-- The registers `ins` hold input words, and the registers `cs` constants. -/
def linEnv (ins : List (XReg × Nat)) (cs : List (XReg × BitVec 64) := []) : Env (Nat × Nat) :=
  { reg := fun r => match ins.find? (·.1 == r) with
      | some p => some (inWord p.2)
      | none => (cs.find? (·.1 == r)).map fun p => (p.2.toNat, 0),
    slot := fun _ => none }

/-- Each output register `r` holds `outWord g`, below `2 ^ (64 2 ^ k)` (`outOk`). -/
def linPost (k : Nat) (outs : List (XReg × (Nat → List Nat))) (e : Env (Nat × Nat)) : Bool :=
  outs.all fun o => outOk k (e.reg o.1) o.2

/-- A linear block that the evaluator accepts, on the machine. -/
theorem linear_ok {k : Nat} {c : Cfg} {is : List Instr} {ins : List (XReg × Nat)}
    {outs : List (XReg × (Nat → List Nat))} {cs : List (XReg × BitVec 64)}
    (hchk : check (lanes 64 k) c is (linEnv ins cs) (linPost k outs) = true)
    {s : State} (hok : Ok c s) (W : Nat → Nat → BitVec 64)
    (hin : ∀ r i, (r, i) ∈ ins → 64 * i + 64 ≤ 2 ^ k ∧ ∀ l < 2, W l i = qword (s.xmm r) l)
    (hcs : ∀ r v, (r, v) ∈ cs → ∀ l < 2, qword (s.xmm r) l = v) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ r g, (r, g) ∈ outs → ∀ l < 2, ∀ p < 64, (qword (s'.xmm r) l).getLsbD p = xorBits (W l) (g p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧
      (∀ r, (is.all fun i => i.dst != some r) = true → s'.gpr r = s.gpr r) ∧
      (∀ x, (is.all fun i => xdst i != some x) = true → s'.xmm x = s.xmm x) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  have hrel : Rel (fun l => LaneRel k (assign (W l) (2 ^ k))) c (linEnv ins cs) s := by
    refine ⟨fun r a h l hl => ?_, (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩
    simp only [linEnv] at h
    split at h
    · rename_i p hf
      cases h
      have hr : p.1 = r := by simpa using List.find?_some hf
      obtain ⟨h1, h2⟩ := hin p.1 p.2 (List.mem_of_find?_eq_some hf)
      rw [← hr, ← h2 l hl]; exact inWord_rel (W l) h1
    · obtain ⟨⟨r', v⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
      have hr : r' = r := by simpa using List.find?_some hf
      subst hr
      rw [hcs r' v (List.mem_of_find?_eq_some hf) l hl]
      exact lanes_sound.const (v := v) rfl
  obtain ⟨s', hs', p⟩ := run (fun _ _ => lanes_sound) hok hrel he
  refine ⟨s', hs', fun r g hrg l hl q hq => ?_, p.rd, p.wr, p.cf, p.zf,
    fun r hr => p.gpr r (by simp [hr]), fun x hx => p.other x (by simp [hx]), p.frame⟩
  obtain ⟨h1, h2⟩ := outOkW_spec (List.all_eq_true.mp hpost (r, g) hrg)
  exact outWord_rel_of_lt h2 (p.rel.reg r _ h1 l hl) q hq

end VG.X86_64.StraightX
