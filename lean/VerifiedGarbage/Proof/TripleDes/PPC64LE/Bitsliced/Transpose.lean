module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Machine
meta import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes

/-!
# The transposition of the state, by evaluation

The transposition (`transposeBody`) only moves, shifts, rotates and XORs
bits of the 64 state words (slots 0–63 at `r10`), and masks them with the
six constants of the mask words (`maskOff`, external words at `r25`): the
lane domain evaluates it on words of atoms (bit `t` of word `i` is atom
`64 i + t`), and the check that bit `p` of word `j` is then atom `64 p + j`
proves that it transposes any 64 words. `transpose_ok` adds the `addi` that
points `r25` at the masks. As on RISC-V
(`Proof/TripleDes/RISCV64/Bitsliced/Transpose.lean`).
-/

-- separate module: builds in parallel with `Pass`, which does not import it

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Bitsliced

open VG VG.PPC64LE VG.PPC64LE.Straight VG.PPC64LE.RegUpd VG.Bitslice VG.Impl.TripleDes.PPC64LE.Bitslice
open VG.Proof.TripleDes.Bitslice (transposeW)

/-- External word `j` is the constant `v` for each `(j, v)` of `ks`. -/
def kExt (ks : List (Nat × BitVec 64)) (j : Nat) : Option (Nat × Nat) :=
  (ks.find? (·.1 == j)).map fun p => (p.2.toNat, 0)

/-- External words that are constants. -/
theorem kExt_rel {k : Nat} {c : Cfg} {s : State} {W : Nat → BitVec 64} {ks : List (Nat × BitVec 64)}
    (hks : ∀ j v, (j, v) ∈ ks → s.mem.readW (wordAddr (s.gpr c.ext) j) 64 = v) :
    ∀ j a, j < c.exts → kExt ks j = some a →
      LaneRel k (assign W (2 ^ k)) a (s.mem.readW (wordAddr (s.gpr c.ext) j) 64) := by
  intro j a _ h
  simp only [kExt, Option.map_eq_some_iff] at h
  obtain ⟨⟨j', v⟩, hf, rfl⟩ := h
  have hj' : j' = j := by simpa using List.find?_some hf
  subst hj'
  rw [hks j' v (List.mem_of_find?_eq_some hf)]
  refine ⟨v.isLt, fun q _ => ?_⟩
  simp [par_zero, BitVec.testBit_toNat]

/-- The state words, and the mask words at `r25`. -/
def transCfg : Cfg := { base := .r10, slots := 64, ext := .r25, exts := 6 }

/-- The mask words' constants. -/
def maskKs : List (Nat × BitVec 64) := (List.range 6).map fun k => (k, swapMask (maskShifts.getD k 1))

def transEnv : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if k < 64 then some (inWord k) else none }

def transPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 64).all fun j => e.slot j == some (outWord (fun p => [64 * p + j]))

theorem transpose_check :
    check (lanes 64 12) transCfg (kExt maskKs) (instrs transposeProg.lit) transEnv transPost = true := by
  lit_decide

/-- The registers the transposition leaves alone. -/
def transKept : List Reg := [.r3, .r4, .r5, .r7, .r8, .r9, .r11]

theorem transpose_keeps :
    transKept.all (fun r => (instrs transposeProg.lit).all fun i => dst i != some r) = true := by
  lit_decide

theorem transpose_code : instrs transposeProg.lit = transposeBody := by
  rw [← transposeProg.lit_eq]; rfl

/-- The mask words hold the masks. -/
def MasksAt (s : State) : Prop :=
  ∀ k < 6, s.mem.readW (wordAddr (s.gpr .r10) (64 + k)) 64 = swapMask (maskShifts.getD k 1)

/-- The mask words. -/
def maskR (s : State) : Region := ⟨wordAddr (s.gpr .r10) 64, 48⟩

theorem masksAt_frame {s s' : State} (hb : s'.gpr .r10 = s.gpr .r10)
    (f : Frame [stR s] s.mem s'.mem) (hm : MasksAt s) : MasksAt s' := by
  intro k hk
  rw [hb, ← hm k hk]
  refine f.readW (Region.contains_self _ 8) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base _ (by omega) (by omega)

theorem wordAddr_masks (b : Addr) (j : Nat) :
    wordAddr (b + BitVec.ofNat 64 maskOff) j = wordAddr b (64 + j) := by
  simp only [wordAddr]
  rw [show maskOff = 512 from rfl, Offset.add_add]
  congr 2
  omega

theorem transpose_ok {s : State} (h : Room s) (hm : MasksAt s) :
    ∃ s', runBlock isa transpose s = some s' ∧ (∀ j < 64, words s' j = transposeW (words s) j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ s'.gpr .r10 = s.gpr .r10 ∧
      (∀ r ∈ transKept, s'.gpr r = s.gpr r) ∧ Frame [stR s] s.mem s'.mem := by
  have e₁ := exec_addi (s := s) (d := .r25) (n := .r10) (imm := maskOff) (by decide) (by decide)
  let s₁ := s.write .r25 (s.gpr .r10 + BitVec.ofNat 64 maskOff)
  have b₁ : s₁.gpr .r10 = s.gpr .r10 := by simp [s₁, gpr_write]
  have a₁ : s₁.gpr .r25 = s.gpr .r10 + BitVec.ofNat 64 maskOff := by simp [s₁, gpr_write]
  have hok : Ok transCfg s₁ :=
    { slotIn := fun k hk => by
        show InRegions s.wr (wordAddr (s₁.gpr .r10) k) 8
        rw [b₁]; exact slot_in h (by simp only [transCfg] at hk; omega)
      extIn := fun k hk => by
        have hk' : k < 6 := hk
        show InRegions (s.rd ++ s.wr) (wordAddr (s₁.gpr .r25) k) 8
        rw [a₁, wordAddr_masks _ k]
        obtain ⟨r, hr, hc⟩ := slot_in h (k := 64 + k) (by omega)
        exact ⟨r, List.mem_append_right _ hr, hc⟩
      slots := by decide
      sep := fun k hk j hj => by
        have hk' : k < 64 := hk
        have hj' : j < 6 := hj
        show Mem.Sep (wordAddr (s₁.gpr .r10) k) 8 (wordAddr (s₁.gpr .r25) j) 8
        rw [b₁, a₁, wordAddr_masks _ j]
        exact Offset.sep _ (by omega) (by omega) (by omega) }
  have hrel : Rel (LaneRel 12 (assign (words s) (2 ^ 12))) transCfg (kExt maskKs) transEnv s₁ := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl => ?_), kExt_rel fun j v hjv => ?_⟩
    · have hj' : j < 64 := hj
      simp only [transEnv, hj', ite_true, Option.some.injEq] at hsl
      subst hsl
      show LaneRel 12 _ _ (s.mem.readW (wordAddr (s₁.gpr .r10) j) 64)
      rw [b₁]
      exact inWord_rel (words s) (by omega)
    · obtain ⟨k, hk, he⟩ := List.mem_map.mp hjv
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hk' := List.mem_range.mp hk
      show s.mem.readW (wordAddr (s₁.gpr .r25) k) 64 = _
      rw [a₁, wordAddr_masks _ k, hm k hk']
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ transpose_check
  rw [transpose_code] at he
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  have kp := transpose_keeps
  rw [transpose_code] at kp
  refine ⟨s', by rw [transpose, runBlock_cons, show base = .r10 from rfl, e₁, runStep_some]; exact hs',
    fun j hj => ?_, p.rd, p.wr, p.sp, p.lr, p.base.trans b₁, fun r hr => ?_, ?_⟩
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
  · have h1 := List.all_eq_true.mp kp r hr
    have hne : r ≠ .r25 := by
      simp only [transKept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [p.other r (by rw [h1]; decide)]
    simp [s₁, gpr_write, hne]
  · have hr : slotRegion transCfg s₁ = stR s := by simp only [slotRegion, transCfg, b₁, stR]
    have f := p.frame
    rw [hr] at f
    exact f

end VG.Proof.TripleDes.PPC64LE.Bitsliced
