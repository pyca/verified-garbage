module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
public import VerifiedGarbage.Proof.Framework.RISCV64.Linear
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# The transposition of the state, by evaluation

The transposition (`transposeBody`) only moves and XORs bits of the 64
state words (slots 0–63 at `s0`), and masks them with the six constants of
the mask words (`maskOff`, external words at `a0`): the lane domain
evaluates it on words of atoms (bit `t` of word `i` is atom `64 i + t`),
and the check that bit `p` of word `j` is then atom `64 p + j` proves that
it transposes any 64 words. `transpose_ok` adds the `addi` that points `a0`
at the masks.
-/

-- separate module: builds in parallel with `Pass`, which does not import it

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.TripleDes.RISCV64.Bitslice
open VG.Proof.TripleDes.Bitslice (transposeW)

/-- The state words, and the mask words at `a0`. -/
def transCfg : Cfg := { base := .s0, slots := 64, ext := .a0, exts := 6 }

/-- The mask words' constants. -/
def maskKs : List (Nat × BitVec 64) := (List.range 6).map fun k => (k, swapMask (maskShifts.getD k 1))

def transEnv : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if k < 64 then some (inWord k) else none }

def transPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 64).all fun j => e.slot j == some (outWord (fun p => [64 * p + j]))

theorem transpose_check :
    check (lanes 64 12) transCfg (kExt maskKs) (instrs transposeProg.lit) transEnv transPost = true := by
  lit_decide

theorem transpose_keeps_a1 : ((instrs transposeProg.lit).all fun i => dst i != some .a1) = true := by
  lit_decide

theorem transpose_keeps_a2 : ((instrs transposeProg.lit).all fun i => dst i != some .a2) = true := by
  lit_decide

theorem transpose_code : instrs transposeProg.lit = transposeBody := by
  rw [← transposeProg.lit_eq]; rfl

/-- The mask words hold the masks. -/
def MasksAt (s : State) : Prop :=
  ∀ k < 6, s.mem.readW (wordAddr (s.gpr .s0) (112 + k)) 64 = swapMask (maskShifts.getD k 1)

theorem masksAt_frame {s s' : State} (hb : s'.gpr .s0 = s.gpr .s0) (h : Room s)
    (f : Frame [stR s] s.mem s'.mem) (hm : MasksAt s) : MasksAt s' := by
  intro k hk
  rw [hb, ← hm k hk]
  refine f.readW (Region.contains_self _ 8) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  have := h.fit
  exact Offset.disjoint_base _ (by omega) (by unfold frameBytes at this; omega)

theorem wordAddr_masks (b : Addr) (j : Nat) :
    wordAddr (b + BitVec.ofInt 64 (maskOff : Int)) j = wordAddr b (112 + j) := by
  simp only [wordAddr]
  rw [show BitVec.ofInt 64 (maskOff : Int) = BitVec.ofNat 64 896 from rfl, Offset.add_add]
  congr 2
  omega

theorem transpose_ok {s : State} (h : Room s) (hm : MasksAt s) :
    ∃ s', runBlock isa transpose s = some s' ∧ (∀ j < 64, words s' j = transposeW (words s) j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .s0 = s.gpr .s0 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a2 = s.gpr .a2 ∧ Frame [stR s] s.mem s'.mem := by
  have e₁ := exec_addi (s := s) (d := .a0) (n := .s0) (imm := (maskOff : Int)) (by decide)
  let s₁ := s.write .a0 (s.gpr .s0 + BitVec.ofInt 64 (maskOff : Int))
  have b₁ : s₁.gpr .s0 = s.gpr .s0 := by simp [s₁, RegUpd.gpr_write]
  have a₁ : s₁.gpr .a0 = s.gpr .s0 + BitVec.ofInt 64 (maskOff : Int) := by simp [s₁, RegUpd.gpr_write]
  have hok : Ok transCfg s₁ :=
    { slotIn := fun k hk => by
        show InRegions s.wr (wordAddr (s₁.gpr .s0) k) 8
        rw [b₁]; exact slot_in h (by simp only [transCfg] at hk; omega)
      extIn := fun k hk => by
        have hk' : k < 6 := hk
        show InRegions (s.rd ++ s.wr) (wordAddr (s₁.gpr .a0) k) 8
        rw [a₁, wordAddr_masks _ k]
        obtain ⟨r, hr, hc⟩ := slot_in h (k := 112 + k) (by omega)
        exact ⟨r, List.mem_append_right _ hr, hc⟩
      baseAl := fun _ => by show (s₁.gpr .s0).toNat % 8 = 0; rw [b₁]; exact h.al
      extAl := fun _ => by
        show (s₁.gpr .a0).toNat % 8 = 0
        rw [a₁, show BitVec.ofInt 64 (maskOff : Int) = BitVec.ofNat 64 (8 * 112) from rfl]
        exact wordAddr_al h.al 112 (by decide)
      slots := by decide
      sep := fun k hk j hj => by
        have hk' : k < 64 := hk
        have hj' : j < 6 := hj
        show Mem.Sep (wordAddr (s₁.gpr .s0) k) 8 (wordAddr (s₁.gpr .a0) j) 8
        rw [b₁, a₁, wordAddr_masks _ j]
        exact Offset.sep _ (by omega) (by omega) (by omega) }
  have hrel : Rel (LaneRel 12 (assign (words s) (2 ^ 12))) transCfg (kExt maskKs) transEnv s₁ := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl => ?_), kExt_rel fun j v hjv => ?_⟩
    · have hj' : j < 64 := hj
      simp only [transEnv, hj', ite_true, Option.some.injEq] at hsl
      subst hsl
      show LaneRel 12 _ _ (s.mem.readW (wordAddr (s₁.gpr .s0) j) 64)
      rw [b₁]
      exact inWord_rel (words s) (by omega)
    · obtain ⟨k, hk, he⟩ := List.mem_map.mp hjv
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hk' := List.mem_range.mp hk
      show s.mem.readW (wordAddr (s₁.gpr .a0) k) 64 = _
      rw [a₁, wordAddr_masks _ k, hm k hk']
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ transpose_check
  rw [transpose_code] at he
  obtain ⟨s', hs', p⟩ := run lanes_sound laneRel_fun hok hrel he
  have k₁ := transpose_keeps_a1
  have k₂ := transpose_keeps_a2
  rw [transpose_code] at k₁ k₂
  refine ⟨s', by rw [transpose, runBlock_cons, show base = .s0 from rfl, e₁, runStep_some]; exact hs',
    fun j hj => ?_, p.rd, p.wr, p.sp, p.base.trans b₁,
    (p.other .a1 (by rw [k₁]; decide)).trans (by simp [s₁, RegUpd.gpr_write]),
    (p.other .a2 (by rw [k₂]; decide)).trans (by simp [s₁, RegUpd.gpr_write]), ?_⟩
  · have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    have hs := p.rel.slot j _ (show j < 64 from hj) (beq_iff_eq.mp hpj)
    have bits := outWord_rel (fun q hq a ha => by simp at ha; omega) hs
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have hsj : words s' j = s'.mem.readW (wordAddr (s'.gpr transCfg.base) j) 64 := rfl
    rw [hsj, bits b hb]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, transposeW, getLsbD_ofBits, hb,
      decide_true, Bool.true_and]
    exact bitOf_word (words s) b j hj
  · have hr : slotRegion transCfg s₁ = stR s := by simp only [slotRegion, transCfg, b₁, stR]
    have f := p.frame
    rw [hr] at f
    exact f

end VG.Proof.TripleDes.RISCV64.Bitsliced
