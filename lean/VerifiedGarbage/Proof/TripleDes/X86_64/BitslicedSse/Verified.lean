import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedSse
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.VerifiedBlock
import VerifiedGarbage.Proof.Framework.X86_64.StraightX
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.Framework.Bitslice.Vars
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Verified
import VerifiedGarbage.Proof.TripleDes.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit`. -/
section

/-! # The SSE2 S-box circuits' and transposition's code, as literals -/

namespace VG.Impl.TripleDes.X86_64.BitsliceSse

open VG.X86_64

-- The circuits' code, once, which the literals below and the functions'
-- literals (`Lit`) read rather than run the register allocator again.
materialize_table VG.Impl.TripleDes.X86_64.BitsliceSse.sboxCode 8

-- The transposition, once.
materialize_value transpose

-- A pair of rounds and the exchange of the halves, once for both directions.
materialize_value roundPair
materialize_value VG.Impl.TripleDes.X86_64.BitsliceSse.swapHalves

def sbox0 : Prog isa := .block (VG.Impl.TripleDes.X86_64.BitsliceSse.sboxCode 0)
def sbox1 : Prog isa := .block (VG.Impl.TripleDes.X86_64.BitsliceSse.sboxCode 1)
def sbox2 : Prog isa := .block (VG.Impl.TripleDes.X86_64.BitsliceSse.sboxCode 2)
def sbox3 : Prog isa := .block (VG.Impl.TripleDes.X86_64.BitsliceSse.sboxCode 3)
def sbox4 : Prog isa := .block (VG.Impl.TripleDes.X86_64.BitsliceSse.sboxCode 4)
def sbox5 : Prog isa := .block (VG.Impl.TripleDes.X86_64.BitsliceSse.sboxCode 5)
def sbox6 : Prog isa := .block (VG.Impl.TripleDes.X86_64.BitsliceSse.sboxCode 6)
def sbox7 : Prog isa := .block (VG.Impl.TripleDes.X86_64.BitsliceSse.sboxCode 7)

materialize_code VG.Impl.TripleDes.X86_64.BitsliceSse.sbox0
materialize_code VG.Impl.TripleDes.X86_64.BitsliceSse.sbox1
materialize_code VG.Impl.TripleDes.X86_64.BitsliceSse.sbox2
materialize_code VG.Impl.TripleDes.X86_64.BitsliceSse.sbox3
materialize_code VG.Impl.TripleDes.X86_64.BitsliceSse.sbox4
materialize_code VG.Impl.TripleDes.X86_64.BitsliceSse.sbox5
materialize_code VG.Impl.TripleDes.X86_64.BitsliceSse.sbox6
materialize_code VG.Impl.TripleDes.X86_64.BitsliceSse.sbox7

def transposeProg : Prog isa := .block transpose

materialize_code VG.Impl.TripleDes.X86_64.BitsliceSse.transposeProg

end VG.Impl.TripleDes.X86_64.BitsliceSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Sbox`. -/
section

/-!
# The SSE2 S-box circuits' machine code

Untrusted. The kernel checks each allocated circuit on all 64 inputs once,
and the quadword-lane evaluator (`StraightX`) with the truth-table domain
lifts that check to every bit position of every quadword of arbitrary
128-bit words. The circuits spill to the scratch buffer (`[rcx + 16k]`,
`k < spills`), read all ones from `ones`, and write no general-purpose
register.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.StraightX VG.Bitslice VG.Impl.TripleDes.X86_64.BitsliceSse
open VG.Proof.TripleDes (inputTable outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (j : Nat) : Prog isa := sboxLiterals.getD j (.block [])

def sboxCfg : Cfg := { base := .rcx, slots := spills }

def sboxEnv : Env Nat :=
  { reg := fun r => if r = VG.Impl.TripleDes.X86_64.BitsliceSse.ones then some (2 ^ 64 - 1)
      else ((List.range 6).find? (fun k => inReg k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (j : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun i => e.reg (outReg i) == some (outputTable j i)

theorem sbox_check : ∀ j < 8,
    VG.X86_64.StraightX.check (table 64 64) VG.Proof.TripleDes.X86_64.BitslicedSse.sboxCfg (instrs (VG.Proof.TripleDes.X86_64.BitslicedSse.sboxLiteral j)) VG.Proof.TripleDes.X86_64.BitslicedSse.sboxEnv (VG.Proof.TripleDes.X86_64.BitslicedSse.sboxPost j) = true := by
  decide +kernel

theorem sboxLiteral_eq : ∀ j < 8, VG.Proof.TripleDes.X86_64.BitslicedSse.sboxLiteral j = .block (sboxCode j)
  | 0, _ => sbox0.lit_eq.symm
  | 1, _ => sbox1.lit_eq.symm
  | 2, _ => sbox2.lit_eq.symm
  | 3, _ => sbox3.lit_eq.symm
  | 4, _ => sbox4.lit_eq.symm
  | 5, _ => sbox5.lit_eq.symm
  | 6, _ => sbox6.lit_eq.symm
  | 7, _ => sbox7.lit_eq.symm
  | n + 8, h => by omega

theorem sbox_preserves : ∀ j < 8,
    (instrs (VG.Proof.TripleDes.X86_64.BitslicedSse.sboxLiteral j)).all (fun op => xdst op != some VG.Impl.TripleDes.X86_64.BitsliceSse.ones && op.dst == none) = true := by
  decide +kernel

/-- Bit `P` of each input register, as the S-box's input. -/
def inputAt (s : VG.X86_64.State) (P : Nat) : BitVec 6 :=
  ofBits 6 fun i => (s.xmm (inReg i)).getLsbD P

theorem inputAt_bit (s : VG.X86_64.State) (P k : Nat) (hk : k < 6) :
    (VG.Proof.TripleDes.X86_64.BitslicedSse.inputAt s P).toNat.testBit k = (s.xmm (inReg k)).getLsbD P := by
  simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem inReg_ne_ones : ∀ k < 6, inReg k ≠ VG.Impl.TripleDes.X86_64.BitsliceSse.ones := by decide

/-- Every S-box output bit, for arbitrary input words and spill slots, with
all ones in `ones`. Only the spill slots change in memory, and no
general-purpose register or flag changes. -/
theorem sbox_ok (j : Nat) (hj : j < 8) {s : VG.X86_64.State} (hok : Ok VG.Proof.TripleDes.X86_64.BitslicedSse.sboxCfg s)
    (hones : s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128) :
    ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ P < 128, (s'.xmm (outReg i)).getLsbD P =
        (Spec.TripleDes.sBox j (VG.Proof.TripleDes.X86_64.BitslicedSse.inputAt s P)).getLsbD i) ∧
      s'.gpr = s.gpr ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones ∧ VG.Frame [slotRegion VG.Proof.TripleDes.X86_64.BitslicedSse.sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (VG.Proof.TripleDes.X86_64.BitslicedSse.sboxLiteral j) = sboxCode j := by rw [VG.Proof.TripleDes.X86_64.BitslicedSse.sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ (VG.Proof.TripleDes.X86_64.BitslicedSse.sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg i) = some (outputTable j i) := by
    intro i hi
    have h := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp h
  have key : ∀ p < 64, ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      Post (fun q => TableRel p (VG.Proof.TripleDes.X86_64.BitslicedSse.inputAt s (64 * q + p)).toNat) VG.Proof.TripleDes.X86_64.BitslicedSse.sboxCfg e' s s'
        (fun r => ((sboxCode j).all fun op => xdst op != some r) = false)
        (fun r => ((sboxCode j).all fun op => op.dst != some r) = false) := by
    intro p hp
    refine run (fun q _ => table_sound hp (VG.Proof.TripleDes.X86_64.BitslicedSse.inputAt s (64 * q + p)).isLt) hok
      ⟨fun r a h q hq => ?_, (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
        (fun _ _ h => by cases h)⟩ he
    have hc := (VG.Proof.TripleDes.X86_64.BitslicedSse.inputAt s (64 * q + p)).isLt
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.sboxEnv] at h
    split at h
    · rename_i hr
      cases h; subst hr
      simp only [TableRel, getLsbD_qword _ hp, hones, BitVec.getLsbD_allOnes,
        Nat.testBit_two_pow_sub_one, hc, decide_true, show 64 * q + p < 128 by omega]
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      have hqr := List.find?_some hk
      have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
      simp only [beq_iff_eq] at hqr
      subst hqr
      simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
        VG.Proof.TripleDes.X86_64.BitslicedSse.inputAt_bit s _ k hk6, getLsbD_qword _ hp]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  have pres := VG.Proof.TripleDes.X86_64.BitslicedSse.sbox_preserves j hj
  rw [codeEq] at pres
  have pres' := List.all_eq_true.mp pres
  refine ⟨s', hs', fun i hi P hP => ?_, funext fun r => p₀.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h
      have := pres' op hop
      simp [h] at this),
    p₀.cf, p₀.zf, p₀.rd, p₀.wr, p₀.other VG.Impl.TripleDes.X86_64.BitsliceSse.ones (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h
      have := pres' op hop
      simp [h] at this), p₀.frame⟩
  obtain ⟨s'', hs'', p₁⟩ := key (P % 64) (Nat.mod_lt _ (by decide))
  obtain rfl := Straight.run_unique hs'' hs'
  have h := p₁.rel.reg (outReg i) _ (hout i hi) (P / 64) (by omega)
  have eP : 64 * (P / 64) + P % 64 = P := Nat.div_add_mod P 64
  simp only [TableRel, outputTable, testBit_tableOf, (VG.Proof.TripleDes.X86_64.BitslicedSse.inputAt s _).isLt,
    decide_true, Bool.true_and, eP, getLsbD_qword _ (Nat.mod_lt _ (by decide) : P % 64 < 64)] at h
  rw [BitVec.ofNat_toNat] at h
  exact h.symm

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Transpose`. -/
section

/-!
# The transposition of the SSE2 state, by evaluation

The 64 state words are the 16-byte slots at `rsi`. The transposition only
moves and XORs bits within the quadword lanes of the words, and masks them
with constants: the lane domain evaluates it on words of atoms (bit `t` of
word `i` is atom `64 i + t`) once, and the check that bit `p` of word `j` is
then atom `64 p + j` proves, through the quadword-lane evaluator, that it
transposes the 64 quadwords of every lane (`transpose_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.StraightX VG.Bitslice VG.Impl.TripleDes.X86_64.BitsliceSse
open VG.Proof.TripleDes.Bitslice (transposeW)

/-- The state words. -/
def stateCfg : VG.X86_64.StraightX.Cfg := { base := .rsi, slots := 64 }

/-- State word `j`. -/
def words (s : VG.X86_64.State) (j : Nat) : BitVec 128 := s.mem.readW (xAddr (s.gpr .rsi) j) 128

/-- Quadword lane `q` of the state words. -/
def laneW (s : VG.X86_64.State) (q : Nat) : Nat → BitVec 64 := fun j => qword (VG.Proof.TripleDes.X86_64.BitslicedSse.words s j) q

def transEnv : VG.X86_64.StraightX.Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if k < 64 then some (inWord k) else none }

def transPost (e : VG.X86_64.StraightX.Env (Nat × Nat)) : Bool :=
  (List.range 64).all fun j => e.slot j == some (outWord (fun p => [64 * p + j]))

theorem transpose_check :
    VG.X86_64.StraightX.check (lanes 64 12) VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg (instrs transposeProg.lit) VG.Proof.TripleDes.X86_64.BitslicedSse.transEnv VG.Proof.TripleDes.X86_64.BitslicedSse.transPost = true := by
  decide +kernel

theorem transpose_code : instrs transposeProg.lit = transpose := by
  rw [← transposeProg.lit_eq]; rfl

/-- The state words' area. -/
def stateR (s : VG.X86_64.State) : Region := ⟨s.gpr .rsi, 1024⟩

theorem transpose_nogpr :
    (instrs transposeProg.lit).all (fun op => op.dst == none || op.dst == some .rbx) = true := by
  decide +kernel

/-- Each quadword lane of the state words, transposed. Only `rbx` (the masks'
constants) and vector registers change, and in memory only the state words. -/
theorem transpose_ok {s : VG.X86_64.State} (hok : VG.X86_64.StraightX.Ok VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg s) :
    ∃ s', runBlock isa transpose s = some s' ∧
      (∀ q < 2, ∀ j < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s' q j = transposeW (VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s q) j) ∧
      (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := VG.X86_64.StraightX.of_check _ _ VG.Proof.TripleDes.X86_64.BitslicedSse.transpose_check
  rw [VG.Proof.TripleDes.X86_64.BitslicedSse.transpose_code] at he
  have hrel : VG.X86_64.StraightX.Rel (fun q => LaneRel 12 (assign (VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s q) (2 ^ 12))) VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg VG.Proof.TripleDes.X86_64.BitslicedSse.transEnv s := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl q hq => ?_), (fun _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.transEnv] at hsl
    split at hsl
    · rename_i hk
      simp only [Option.some.injEq] at hsl
      subst hsl
      exact inWord_rel (VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s q) (by omega)
    · cases hsl
  obtain ⟨s', hs', p⟩ := VG.X86_64.StraightX.run (fun _ _ => lanes_sound) hok hrel he
  have nog := List.all_eq_true.mp VG.Proof.TripleDes.X86_64.BitslicedSse.transpose_nogpr
  rw [VG.Proof.TripleDes.X86_64.BitslicedSse.transpose_code] at nog
  refine ⟨s', hs', fun q hq j hj => ?_, fun r hr => p.gpr r ?_, p.cf, p.zf, p.rd, p.wr, p.frame⟩
  · have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    have hs := p.rel.slot j _ (by show j < 64; omega) (beq_iff_eq.mp hpj) q hq
    have bits := outWord_rel (fun q hq a ha => by simp at ha; omega) hs
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have hsj : VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s' q j = qword (s'.mem.readW (xAddr (s'.gpr stateCfg.base) j) 128) q := rfl
    rw [hsj, bits b hb]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, transposeW, getLsbD_ofBits, hb,
      decide_true, Bool.true_and]
    exact VG.Bitslice.bitOf_word (VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s q) b j hj
  · simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
    intro op hop h
    have := nog op hop
    simp [h, hr] at this

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Machine`. -/
section

/-!
# The SSE2 machine state of a batch

The 64 state words are the 16-byte slots at `rsi` (`words`), in a writable
region apart from the scratch buffer at `rcx`, which holds the circuits'
spills (`Room`). Code that only moves and XORs whole words (the S-box
outputs, the exchange of the halves) is checked on the variable domain,
quadword lane by quadword lane (`varsRun`).
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.StraightX VG.X86_64.RegUpd VG.Bitslice
open VG.Impl.TripleDes.X86_64.BitsliceSse

/-- The scratch buffer. -/
def scratchR (s : VG.X86_64.State) : Region := ⟨s.gpr .rcx, 1024⟩

/-- The circuits' spill slots, at the start of the scratch buffer. -/
def spillR (s : VG.X86_64.State) : Region := ⟨s.gpr .rcx, 256⟩

theorem spill_sub (s : VG.X86_64.State) : Region.Sub (VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s) (VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s) := Region.sub_prefix (by decide)

/-- What a batch's code needs of the machine: the scratch buffer writable,
the state words writable and apart from it. -/
structure Room (s : VG.X86_64.State) : Prop where
  scratch : VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s ∈ s.wr
  state : Ok VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg s
  sep : (VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s).Disjoint (VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s)

theorem Room.congr {s s' : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hsi : s'.gpr .rsi = s.gpr .rsi) (hw : s'.wr = s.wr) : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s' where
  scratch := by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR, hc, hw]; exact h.scratch
  state := h.state.congr hsi hw
  sep := by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR, hc, hsi]; exact h.sep

theorem runBlock_cat (a b : List Instr) (s : VG.X86_64.State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : VG.X86_64.State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat, h₁, Option.bind_some, h₂]

/-! ## Quadwords -/

open VG.X86_64.StraightY (qword_xor qword_app)

theorem eq_of_qword {x y : BitVec 128} (h : ∀ q < 2, qword x q = qword y q) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun z => z.getLsbD (i % 64)) (h (i / 64) (by omega))
  simp only [getLsbD_qword _ (Nat.mod_lt i (by decide) : i % 64 < 64), Nat.div_add_mod] at e
  exact e

theorem qword_zero (q : Nat) : qword 0 q = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [qword]

/-! ## Words as XORs of variables -/

/-- Slot `k` is variable `k`; register `regs[i]` is variable `64 + i`. -/
def varEnv (regs : List XReg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (64 + i),
    slot := fun k => if k < 64 then some (2 ^ k) else none }

/-- The values of the variables, in quadword lane `q`. -/
def varVals (s : VG.X86_64.State) (regs : List XReg) (q v : Nat) : BitVec 64 :=
  if v < 64 then VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s q v else qword (s.xmm (regs.getD (v - 64) .xmm0)) q

def varN (regs : List XReg) : Nat := 64 + regs.length

theorem varEnv_rel {s : VG.X86_64.State} (regs : List XReg) :
    Rel (fun q => VarRel (VG.Proof.TripleDes.X86_64.BitslicedSse.varVals s regs q) (VG.Proof.TripleDes.X86_64.BitslicedSse.varN regs)) VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg (VG.Proof.TripleDes.X86_64.BitslicedSse.varEnv regs) s where
  reg r a h q hq := by
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.varEnv, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [VarRel, VG.Proof.TripleDes.X86_64.BitslicedSse.varN]
    rw [xorSet_two_pow _ (by omega)]
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.varVals, show ¬ 64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, heq]
  slot k a hk h q hq := by
    have hk' : k < 64 := hk
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.varEnv, hk', ite_true, Option.some.injEq] at h
    subst h
    simp only [VarRel, VG.Proof.TripleDes.X86_64.BitslicedSse.varN]
    rw [xorSet_two_pow _ (by omega)]
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.varVals, hk', ite_true, VG.Proof.TripleDes.X86_64.BitslicedSse.laneW, VG.Proof.TripleDes.X86_64.BitslicedSse.words, VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg]
  gc _ _ h := by cases h
  xc _ _ h := by cases h

/-- Run a block that the variable domain accepts on the state words. -/
theorem varsRun {is : List Instr} (regs : List XReg) {post : Env Nat → Bool}
    (hchk : VG.X86_64.StraightX.check (vars 64) VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg is (VG.Proof.TripleDes.X86_64.BitslicedSse.varEnv regs) post = true) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (fun q => VarRel (VG.Proof.TripleDes.X86_64.BitslicedSse.varVals s regs q) (VG.Proof.TripleDes.X86_64.BitslicedSse.varN regs)) VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg e' s s'
        (fun r => (is.all fun i => xdst i != some r) = false)
        (fun r => (is.all fun i => i.dst != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  obtain ⟨s', hs', p⟩ := run (fun q _ => vars_sound _ _) h.state (VG.Proof.TripleDes.X86_64.BitslicedSse.varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

theorem xorSet_two_pow_xor {V : Nat → BitVec 64} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

/-! ## Instructions on whole registers -/

theorem xmm_pxor (s : VG.X86_64.State) (d a : XReg) :
    ((XOp.bin .pxor d a).exec s).xmm d = s.xmm d ^^^ s.xmm a := by
  simp [XOp.exec, State.setXmm, XBinOp.eval]

/-- The all-zero or all-one quadword. -/
def maskVal (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-- The all-zero or all-one word. -/
def maskX (b : Bool) : BitVec 128 := if b then BitVec.allOnes 128 else 0

theorem getLsbD_maskX (b : Bool) {P : Nat} (hP : P < 128) : (VG.Proof.TripleDes.X86_64.BitslicedSse.maskX b).getLsbD P = b := by
  cases b
  · simp [VG.Proof.TripleDes.X86_64.BitslicedSse.maskX]
  · simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.maskX, ite_true, BitVec.getLsbD_allOnes, hP, decide_true]

/-- `movq x, r` then `punpcklqdq x, x` of a mask. -/
theorem bcast_mask (s : VG.X86_64.State) (x : XReg) (r : Reg) (b : Bool) (hr : s.gpr r = VG.Proof.TripleDes.X86_64.BitslicedSse.maskVal b) :
    ((XOp.bin .punpcklqdq x x).exec ((XOp.movq x r).exec s)).xmm x = VG.Proof.TripleDes.X86_64.BitslicedSse.maskX b := by
  apply VG.Proof.TripleDes.X86_64.BitslicedSse.eq_of_qword; intro q hq
  simp only [XOp.exec, State.setXmm, ite_true, XBinOp.eval, hr]
  rw [qword_app _ _ hq, qword_app _ _ (by decide)]
  simp only [ite_true]
  have e : qword (VG.Proof.TripleDes.X86_64.BitslicedSse.maskX b) q = VG.Proof.TripleDes.X86_64.BitslicedSse.maskVal b := by
    cases b
    · simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.maskVal, VG.Proof.TripleDes.X86_64.BitslicedSse.maskX, Bool.false_eq_true, ite_false, VG.Proof.TripleDes.X86_64.BitslicedSse.qword_zero]
    · simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.maskVal, VG.Proof.TripleDes.X86_64.BitslicedSse.maskX, ite_true]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [getLsbD_qword _ hi]
      simp only [BitVec.getLsbD_allOnes, hi, show 64 * q + i < 128 by omega, decide_true]
  rw [e]
  split <;> rfl

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Step`. -/
section

/-!
# One S-box of an SSE2 round, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, the next six key bits of
`rax` as masks, broadcast and XORed with the words of `E`; its circuit;
XORing its outputs into their words) does to the state words what `step`
does, given the key bits at the top of `rax`, and shifts them out.
`swapHalves_ok`: the exchange of the halves does what `swapW` does.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.StraightX VG.X86_64.RegUpd VG.Bitslice
open VG.Impl.TripleDes.X86_64.BitsliceSse VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)
open VG.X86_64.StraightY (qword_xor)

theorem add_self_eq (x : BitVec 64) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
  congr 1
  omega

theorem add_self_carry (a : BitVec 64) : decide (2 ^ 64 ≤ a.toNat + a.toNat) = a.msb := by
  rw [BitVec.msb_eq_decide]
  have := a.isLt
  simp only [Nat.add_one_sub_one]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

theorem sbb_self (a : BitVec 64) (c : Bool) : a - a - (BitVec.ofBool c).setWidth 64 = VG.Proof.TripleDes.X86_64.BitslicedSse.maskVal c := by
  cases c <;> simp [VG.Proof.TripleDes.X86_64.BitslicedSse.maskVal]

theorem msb_shiftLeft (R : BitVec 64) {n : Nat} (hn : n < 64) : (R <<< n).msb = R.getLsbD (63 - n) := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
  have : ¬ 63 < n := by omega
  simp [this, show (63 : Nat) < 64 by decide]

theorem word_in {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) {w : Nat} (hw : w < 64) :
    InRegions (s.rd ++ s.wr) (s.ea (word w)) 16 := by
  obtain ⟨r, hr, hc⟩ := h.state.slotIn w hw
  have e : s.ea (word w) = xAddr (s.gpr stateCfg.base) w := ea_of rfl rfl rfl
  rw [e]
  exact ⟨r, List.mem_append_right _ hr, hc⟩


/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ maskReg ∧ inReg i ≠ VG.Impl.TripleDes.X86_64.BitsliceSse.ones := by decide

theorem inReg_inj' : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

/-- One input: the next key bit as a mask, XORed with state word `w`. -/
theorem inputStep_run {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) {x : XReg} (hx : x ≠ maskReg) {w : Nat} (hw : w < 64) :
    ∃ s', runBlock isa [.alu .add .rax (.reg .rax), .alu .sbb .rbx (.reg .rbx),
        .xop (.movq maskReg .rbx), xbin .punpcklqdq maskReg maskReg, xload x (word w),
        xbin .pxor x maskReg] s = some s' ∧
      s'.gpr .rax = s.gpr .rax <<< 1 ∧ s'.xmm x = VG.Proof.TripleDes.X86_64.BitslicedSse.words s w ^^^ VG.Proof.TripleDes.X86_64.BitslicedSse.maskX (s.gpr .rax).msb ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      (∀ y, y ≠ x → y ≠ maskReg → s'.xmm y = s.xmm y) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let a := s.gpr .rax
  let s₁ := (arithFlags s (a + a) (decide (2 ^ 64 ≤ a.toNat + a.toNat)) (addOverflow a a (a + a))).setReg
    .rax (a + a)
  have e₁ : exec (.alu .add .rax (.reg .rax)) s = some s₁ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]; rfl
  have cf₁ : s₁.cf = some a.msb := by
    simp only [s₁, cf_setReg, cf_arithFlags, VG.Proof.TripleDes.X86_64.BitslicedSse.add_self_carry]
  let b := s₁.gpr .rbx
  let r := b - b - (BitVec.ofBool a.msb).setWidth 64
  let s₂ := (arithFlags s₁ r (decide (b.toNat < b.toNat + a.msb.toNat)) (subOverflow b b r)).setReg .rbx r
  have e₂ : exec (.alu .sbb .rbx (.reg .rbx)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some, cf₁, Option.map_some]; rfl
  have rbx₂ : s₂.gpr .rbx = VG.Proof.TripleDes.X86_64.BitslicedSse.maskVal a.msb := by
    simp only [s₂, gpr_setReg_self, r]; exact VG.Proof.TripleDes.X86_64.BitslicedSse.sbb_self _ _
  let s₃ := (XOp.movq maskReg .rbx).exec s₂
  let s₄ := (XOp.bin .punpcklqdq maskReg maskReg).exec s₃
  have m₄ : s₄.xmm maskReg = VG.Proof.TripleDes.X86_64.BitslicedSse.maskX a.msb := VG.Proof.TripleDes.X86_64.BitslicedSse.bcast_mask s₂ maskReg .rbx a.msb rbx₂
  have g₄ : s₄.gpr = s₂.gpr := by simp [s₄, s₃, XOp.exec, State.setXmm]
  have mem₄ : s₄.mem = s.mem := by simp [s₄, s₃, XOp.exec, State.setXmm, s₂, s₁, mem_setReg, mem_arithFlags]
  have rd₄ : s₄.rd = s.rd := by simp [s₄, s₃, XOp.exec, State.setXmm, s₂, s₁, rd_setReg, rd_arithFlags]
  have wr₄ : s₄.wr = s.wr := by simp [s₄, s₃, XOp.exec, State.setXmm, s₂, s₁, wr_setReg, wr_arithFlags]
  have si₄ : s₄.gpr .rsi = s.gpr .rsi := by simp [g₄, s₂, s₁, gpr_setReg]
  have c₄ : s₄.gpr .rcx = s.gpr .rcx := by simp [g₄, s₂, s₁, gpr_setReg]
  have h₄ : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s₄ := h.congr c₄ si₄ wr₄
  let v := s₄.mem.readW (s₄.ea (word w)) 128
  have hv : v = VG.Proof.TripleDes.X86_64.BitslicedSse.words s w := by
    simp only [v, mem₄, VG.Proof.TripleDes.X86_64.BitslicedSse.words]
    rw [show s₄.ea (word w) = xAddr (s₄.gpr .rsi) w from ea_of rfl rfl rfl, si₄]
  let s₅ := s₄.setXmm x v
  have e₅ : exec (xload x (word w)) s₄ = some s₅ := by
    simp only [xload, exec, State.load128, VG.Proof.TripleDes.X86_64.BitslicedSse.word_in h₄ hw, ite_true, Option.map_some]; rfl
  let s₆ := (XOp.bin .pxor x maskReg).exec s₅
  have y₄ : ∀ y, y ≠ maskReg → s₄.xmm y = s.xmm y := by
    intro y hy
    simp only [s₄, s₃, XOp.exec, xmm_setXmm, hy, ite_false]; rfl
  refine ⟨s₆, ?_, ?_, ?_, fun r' h1 h2 => ?_, fun y h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons]
    rw [show exec (.xop (.movq maskReg .rbx)) s₂ = some s₃ from rfl, runStep_some,
      runBlock_cons, show exec (xbin .punpcklqdq maskReg maskReg) s₃ = some s₄ from rfl,
      runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      show exec (xbin .pxor x maskReg) s₅ = some s₆ from rfl, runStep_some, runBlock_nil]
  · simp [s₆, s₅, XOp.exec, State.setXmm, g₄, s₂, s₁, gpr_setReg, VG.Proof.TripleDes.X86_64.BitslicedSse.add_self_eq, a]
  · simp only [s₆, VG.Proof.TripleDes.X86_64.BitslicedSse.xmm_pxor, s₅, xmm_setXmm, ite_true, Ne.symm hx, ite_false, m₄, hv, a]
  · simp [s₆, s₅, XOp.exec, State.setXmm, g₄, s₂, s₁, gpr_setReg, h1, h2]
  · simp only [s₆, XOp.exec, xmm_setXmm, h1, ite_false, s₅]
    exact y₄ y h2
  · simp [s₆, s₅, XOp.exec, State.setXmm, mem₄]
  · simp [s₆, s₅, XOp.exec, State.setXmm, rd₄]
  · simp [s₆, s₅, XOp.exec, State.setXmm, wr₄]

def inputsN (ρ : Role) (j n : Nat) : List Instr :=
  (List.range n).flatMap fun m => inputStep ρ j (5 - m)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = VG.Proof.TripleDes.X86_64.BitslicedSse.inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    VG.Proof.TripleDes.X86_64.BitslicedSse.inputsN ρ j (n + 1) = VG.Proof.TripleDes.X86_64.BitslicedSse.inputsN ρ j n ++ inputStep ρ j (5 - n) := by
  simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readWord_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, readWord ρ (eBit (inBit j i)) < 64 := by
  intro ρ; cases ρ <;> lit_decide

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.X86_64.BitslicedSse.inputsN ρ j n) s = some s' ∧ s'.gpr .rax = s.gpr .rax <<< n ∧
      (∀ m < n, s'.xmm (inReg (5 - m)) = VG.Proof.TripleDes.X86_64.BitslicedSse.words s (readWord ρ (eBit (inBit j (5 - m)))) ^^^
        VG.Proof.TripleDes.X86_64.BitslicedSse.maskX ((s.gpr .rax).getLsbD (63 - m))) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, by simp, fun m hm => by omega, fun _ _ _ => rfl, rfl, rfl, rfl,
      rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, k₁, in₁, g₁, o₁, m₁, rd₁, wr₁⟩ := ih (by omega)
    have h₁ : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s₁ := h.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide)) wr₁
    obtain ⟨hq, ho⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.inReg_ne (5 - n) (by omega)
    obtain ⟨s₂, run₂, k₂, q₂, g₂, y₂, m₂, rd₂, wr₂⟩ :=
      VG.Proof.TripleDes.X86_64.BitslicedSse.inputStep_run h₁ hq (w := readWord ρ (eBit (inBit j (5 - n)))) (VG.Proof.TripleDes.X86_64.BitslicedSse.readWord_lt ρ j hj _ (by omega))
    refine ⟨s₂, ?_, ?_, fun m hm => ?_, fun r h1 h2 => (g₂ r h1 h2).trans (g₁ r h1 h2),
      (y₂ _ (Ne.symm ho) (by decide)).trans o₁, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁⟩
    · rw [VG.Proof.TripleDes.X86_64.BitslicedSse.inputsN_succ]; exact VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some run₁ run₂
    · rw [k₂, k₁, ← BitVec.shiftLeft_add]
    · by_cases he : m = n
      · subst he
        rw [q₂, k₁, VG.Proof.TripleDes.X86_64.BitslicedSse.msb_shiftLeft _ (by omega)]
        simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.words, m₁, g₁ .rsi (by decide) (by decide)]
      · have hne : inReg (5 - m) ≠ inReg (5 - n) := by
          intro e; have := VG.Proof.TripleDes.X86_64.BitslicedSse.inReg_inj' _ (by omega) _ (by omega) e; omega
        rw [y₂ _ hne (VG.Proof.TripleDes.X86_64.BitslicedSse.inReg_ne (5 - m) (by omega)).1, in₁ m (by omega)]

/-! ## Outputs -/

def outPost (ρ : Role) (j : Nat) (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k ==
    some (match outIdx ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (64 + i)
      | none => 2 ^ k)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    VG.X86_64.StraightX.check (vars 64) VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg (outputCode ρ j) (VG.Proof.TripleDes.X86_64.BitslicedSse.varEnv outRegs) (VG.Proof.TripleDes.X86_64.BitslicedSse.outPost ρ j) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

theorem outputCode_regs : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => i.dst == none && xdst i != some VG.Impl.TripleDes.X86_64.BitsliceSse.ones) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s' k = match outIdx ρ j k with
        | some i => VG.Proof.TripleDes.X86_64.BitslicedSse.words s k ^^^ s.xmm (outReg i)
        | none => VG.Proof.TripleDes.X86_64.BitslicedSse.words s k) ∧
      s'.gpr = s.gpr ∧ s'.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.varsRun outRegs (VG.Proof.TripleDes.X86_64.BitslicedSse.output_check ρ j hj) h
  simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have regs := List.all_eq_true.mp (VG.Proof.TripleDes.X86_64.BitslicedSse.outputCode_regs ρ j hj)
  refine ⟨s', hrun, fun k hk => ?_, funext fun r => p.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this),
    p.other VG.Impl.TripleDes.X86_64.BitsliceSse.ones (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this), p.rd, p.wr, p.frame⟩
  apply VG.Proof.TripleDes.X86_64.BitslicedSse.eq_of_qword; intro q hq
  have hs := p.rel.slot k _ hk (hpost k hk) q hq
  simp only [VarRel] at hs
  have e : qword (VG.Proof.TripleDes.X86_64.BitslicedSse.words s' k) q = qword (s'.mem.readW (xAddr (s'.gpr stateCfg.base) k) 128) q := by
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.words, VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg]
  rw [e, hs]
  split
  · rename_i i hi
    have hi4 := VG.Proof.TripleDes.X86_64.BitslicedSse.outIdx_lt ρ j k i hi
    rw [VG.Proof.TripleDes.X86_64.BitslicedSse.xorSet_two_pow_xor (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.varN, outRegs]; omega) (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.varN, outRegs]; omega)]
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.varVals, hk, ite_true, show ¬ 64 + i < 64 by omega, ite_false,
      Nat.add_sub_cancel_left, qword_xor, VG.Proof.TripleDes.X86_64.BitslicedSse.laneW, outReg]
  · rw [xorSet_two_pow _ (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.varN]; omega)]
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.varVals, hk, ite_true, VG.Proof.TripleDes.X86_64.BitslicedSse.laneW]

/-! ## One S-box -/

theorem spill_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) : Ok VG.Proof.TripleDes.X86_64.BitslicedSse.sboxCfg s :=
  Ok.of_off (off := 0) h.scratch (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR, VG.Proof.TripleDes.X86_64.BitslicedSse.sboxCfg]) (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR, VG.Proof.TripleDes.X86_64.BitslicedSse.sboxCfg, spills])
    (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR])

/-- The state words are apart from the spill slots. -/
theorem words_spill {s s' : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) (hsi : s'.gpr .rsi = s.gpr .rsi)
    (hf : VG.Frame [slotRegion VG.Proof.TripleDes.X86_64.BitslicedSse.sboxCfg s] s.mem s'.mem) (x : Nat) (hx : x < 64) :
    VG.Proof.TripleDes.X86_64.BitslicedSse.words s' x = VG.Proof.TripleDes.X86_64.BitslicedSse.words s x := by
  simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.words, hsi]
  refine hf.readW (r := ⟨xAddr (s.gpr .rsi) x, 16⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  refine (h.sep.sub_left ?_).sub_right (Region.sub_prefix (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.sboxCfg, spills]))
  exact Offset.sub_base _ (by omega)

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s)
    (hones : s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128) (k : BitVec 48)
    (hkey : ∀ i < 6, (s.gpr .rax).getLsbD (58 + i) = k.getLsbD (inBit j i)) :
    ∃ s', runBlock isa (sboxStep ρ j) s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s' x = VG.Proof.TripleDes.Bitslice.step ρ k j (VG.Proof.TripleDes.X86_64.BitslicedSse.words s) x) ∧ s'.gpr .rax = s.gpr .rax <<< 6 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, in₁, g₁, o₁, m₁, rd₁, wr₁⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.inputsN_ok ρ hj (Nat.le_refl 6) h
  have c₁ := g₁ .rcx (by decide) (by decide)
  have si₁ := g₁ .rsi (by decide) (by decide)
  have h₁ := h.congr c₁ si₁ wr₁
  obtain ⟨s₂, run₂, out₂, g₂, cf₂, zf₂, rd₂, wr₂, o₂, f₂⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.sbox_ok j hj (VG.Proof.TripleDes.X86_64.BitslicedSse.spill_ok h₁) (by rw [o₁, hones])
  have h₂ := h₁.congr (by rw [g₂]) (by rw [g₂]) wr₂
  obtain ⟨s₃, run₃, w₃, g₃, o₃, rd₃, wr₃, f₃⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.outputs_ok ρ hj h₂
  have w₂ : ∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s₂ x = VG.Proof.TripleDes.X86_64.BitslicedSse.words s x := by
    intro x hx
    rw [VG.Proof.TripleDes.X86_64.BitslicedSse.words_spill h₁ (by rw [g₂]) f₂ x hx]
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.words, m₁, si₁]
  have hin : ∀ i < 6, s₁.xmm (inReg i) =
      VG.Proof.TripleDes.X86_64.BitslicedSse.words s (readWord ρ (eBit (inBit j i))) ^^^ VG.Proof.TripleDes.X86_64.BitslicedSse.maskX (k.getLsbD (inBit j i)) := by
    intro i hi
    have e := in₁ (5 - i) (by omega)
    rw [show 5 - (5 - i) = i by omega] at e
    rw [e, show 63 - (5 - i) = 58 + i by omega, hkey i hi]
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, fun r h1 h2 => ?_, ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩
  · rw [sboxStep, VG.Proof.TripleDes.X86_64.BitslicedSse.inputCode_eq]; exact VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some (VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some run₁ run₂) run₃
  · rw [w₃ x hx]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact w₂ x hx
    · have hi4 := VG.Proof.TripleDes.X86_64.BitslicedSse.outIdx_lt ρ j x i hidx
      dsimp only
      rw [w₂ x hx]
      refine congrArg (VG.Proof.TripleDes.X86_64.BitslicedSse.words s x ^^^ ·) ?_
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [out₂ i hi4 p hp]
      simp only [sboxOut, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      refine congrArg (fun z => (Spec.TripleDes.sBox j z).getLsbD i) ?_
      apply BitVec.eq_of_getLsbD_eq
      intro i' hi'
      simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.inputAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, VG.Proof.TripleDes.X86_64.BitslicedSse.getLsbD_maskX _ hp]
  · rw [g₃, g₂, k₁]
  · rw [g₃, g₂, g₁ r h1 h2]
  · rw [o₃, o₂, o₁]
  · have a : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s₁.mem := by rw [m₁]; exact Frame.refl _ _
    have b : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s₁.mem s₂.mem := by
      refine f₂.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, List.mem_cons_self, ?_⟩
      simp only [slotRegion, VG.Proof.TripleDes.X86_64.BitslicedSse.sboxCfg, VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, c₁]
      exact Region.sub_prefix (by simp [spills])
    have c : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s₂.mem s₃.mem := by
      refine f₃.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, g₂, si₁]
      exact fun _ h => h
    exact (a.trans b).trans c

/-! ## The exchange of the halves -/

/-- The word that goes into word `k`. -/
def swapSlot (k : Nat) : Nat := match partner k with | some y => y | none => k

def swapPost (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k == some (2 ^ VG.Proof.TripleDes.X86_64.BitslicedSse.swapSlot k)

theorem swap_check : VG.X86_64.StraightX.check (vars 64) VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg VG.Impl.TripleDes.X86_64.BitsliceSse.swapHalves (VG.Proof.TripleDes.X86_64.BitslicedSse.varEnv [.xmm0, .xmm1]) VG.Proof.TripleDes.X86_64.BitslicedSse.swapPost = true := by
  lit_decide

theorem swapSlot_lt : ∀ k < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.swapSlot k < 64 := by lit_decide

theorem swap_regs : (swapHalves.all fun i => i.dst == none && xdst i != some VG.Impl.TripleDes.X86_64.BitsliceSse.ones) = true := by
  lit_decide

theorem swapHalves_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) :
    ∃ s', runBlock isa VG.Impl.TripleDes.X86_64.BitsliceSse.swapHalves s = some s' ∧ (∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s' x = swapW (VG.Proof.TripleDes.X86_64.BitslicedSse.words s) x) ∧
      s'.gpr = s.gpr ∧ s'.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.varsRun [.xmm0, .xmm1] VG.Proof.TripleDes.X86_64.BitslicedSse.swap_check h
  simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have regs := List.all_eq_true.mp VG.Proof.TripleDes.X86_64.BitslicedSse.swap_regs
  refine ⟨s', hrun, fun x hx => ?_, funext fun r => p.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this),
    p.other VG.Impl.TripleDes.X86_64.BitsliceSse.ones (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this), p.rd, p.wr, p.frame⟩
  apply VG.Proof.TripleDes.X86_64.BitslicedSse.eq_of_qword; intro q hq
  have hs := p.rel.slot x _ hx (hpost x hx) q hq
  simp only [VarRel] at hs
  have e : qword (VG.Proof.TripleDes.X86_64.BitslicedSse.words s' x) q = qword (s'.mem.readW (xAddr (s'.gpr stateCfg.base) x) 128) q := by
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.words, VG.Proof.TripleDes.X86_64.BitslicedSse.stateCfg]
  rw [e, hs, xorSet_two_pow _ (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.varN]; have := VG.Proof.TripleDes.X86_64.BitslicedSse.swapSlot_lt x hx; omega)]
  simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.varVals, VG.Proof.TripleDes.X86_64.BitslicedSse.swapSlot_lt x hx, ite_true, VG.Proof.TripleDes.X86_64.BitslicedSse.laneW]
  unfold swapW VG.Proof.TripleDes.X86_64.BitslicedSse.swapSlot
  cases partner x <;> rfl

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Round`. -/
section

/-!
# An SSE2 round on the machine

`round_ok`: the code of a round reads the round key at the key pointer
`r8` into `rax`, advances the pointer by the step `r9`, and does to the 64
state words what `roundW` does, with the key's low 48 bits.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.StraightX VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceSse
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW steps_succ steps_congr)

/-! ## The round key -/

theorem keyLoad_ok {s : VG.X86_64.State} (hkey : InRegions (s.rd ++ s.wr) (s.gpr .r8) 8) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      s'.gpr .rax = (s.mem.readW (s.gpr .r8) 64).rotateRight 48 ∧
      s'.gpr .r8 = s.gpr .r8 + s.gpr .r9 ∧ (∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ y, s'.xmm y = s.xmm y) := by
  let kp := s.gpr .r8
  let K := s.mem.readW kp 64
  let δ := s.gpr .r9
  let s₁ := s.setReg .rax K
  have e₁ : exec (.mov .rax (.mem { base := .r8, disp := 0 })) s = some s₁ := by
    have hea : s.ea { base := .r8, disp := 0 } = kp := by simp [State.ea, kp]
    have hl : s.load64 kp = some K := by simp only [State.load64, hkey, ite_true, kp, K]
    simp only [exec, readSrc, hea, hl, Option.map_some]
    rfl
  let v := kp + δ
  let s₂ := (arithFlags s₁ v (decide (2 ^ 64 ≤ kp.toNat + δ.toNat)) (addOverflow kp δ v)).setReg .r8 v
  have e₂ : exec (.alu .add .r8 (.reg .r9)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]
    have ha : s₁.gpr .r8 = kp := by simp [s₁, gpr_setReg, kp]
    have hd : s₁.gpr .r9 = δ := by simp [s₁, gpr_setReg, δ]
    rw [ha, hd]
  let s₃ := (s₂.setFlags (some ((s₂.gpr .rax).rotateRight 48).msb) none s₂.zf s₂.sf).setReg .rax
    ((s₂.gpr .rax).rotateRight 48)
  have e₃ : exec (.shift .ror .rax 48) s₂ = some s₃ := by
    simp only [exec, execShift]; rfl
  refine ⟨s₃, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, fun y => rfl⟩
  · rw [keyLoad, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · simp [s₃, s₂, s₁, gpr_setReg, K, kp]
  · simp [s₃, s₂, gpr_setReg, gpr_setFlags, v, kp, δ]
  · simp [s₃, s₂, s₁, gpr_setReg, gpr_setFlags, h1, h2]
  · simp [s₃, s₂, s₁, mem_setReg, mem_setFlags, mem_arithFlags]
  · simp [s₃, s₂, s₁, rd_setReg, rd_setFlags, rd_arithFlags]
  · simp [s₃, s₂, s₁, wr_setReg, wr_setFlags, wr_arithFlags]

/-! ## The S-boxes -/

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    VG.Proof.TripleDes.X86_64.BitslicedSse.stepsCode ρ (n + 1) = VG.Proof.TripleDes.X86_64.BitslicedSse.stepsCode ρ n ++ sboxStep ρ n := by
  simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- S-box `j`'s key bits are at the top of the rotated key, shifted by the
bits of the S-boxes before it. -/
theorem keyBits (K : BitVec 64) {j i : Nat} (hj : j < 8) (hi : i < 6) :
    (K.rotateRight 48 <<< (6 * j)).getLsbD (58 + i) = (K.setWidth 48).getLsbD (inBit j i) := by
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_setWidth]
  have h1 : ¬ 58 + i < 6 * j := by omega
  have h2 : ¬ 58 + i - 6 * j < 64 - 48 % 64 := by omega
  have h3 : 58 + i - 6 * j - (64 - 48 % 64) = inBit j i := by unfold inBit; omega
  have h4 : inBit j i < 48 := by unfold inBit; omega
  simp only [h1, decide_false, Bool.not_false, Bool.true_and, h2, ite_false, h3, h4, decide_true,
    Bool.true_and, show 58 + i < 64 by omega, show 58 + i - 6 * j < 64 by omega]

theorem stepsCode_ok (ρ : Role) (K : BitVec 64) {n : Nat} (hn : n ≤ 8) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s)
    (hones : s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128) (hr : s.gpr .rax = K.rotateRight 48) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.X86_64.BitslicedSse.stepsCode ρ n) s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s' x = steps ρ (K.setWidth 48) n (VG.Proof.TripleDes.X86_64.BitslicedSse.words s) x) ∧
      s'.gpr .rax = K.rotateRight 48 <<< (6 * n) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, by simp [hr], fun _ _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, r₁, g₁, o₁, rd₁, wr₁, f₁⟩ := ih (by omega)
    have c₁ := g₁ .rcx (by decide) (by decide)
    have si₁ := g₁ .rsi (by decide) (by decide)
    have h₁ := h.congr c₁ si₁ wr₁
    obtain ⟨s₂, run₂, w₂, r₂, g₂, o₂, rd₂, wr₂, f₂⟩ :=
      VG.Proof.TripleDes.X86_64.BitslicedSse.sboxStep_ok ρ (by omega : n < 8) h₁ (by rw [o₁, hones]) (K.setWidth 48)
        (fun i hi => by rw [r₁]; exact VG.Proof.TripleDes.X86_64.BitslicedSse.keyBits K (by omega) hi)
    refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun r h1 h2 => (g₂ r h1 h2).trans (g₁ r h1 h2),
      o₂.trans o₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩
    · rw [VG.Proof.TripleDes.X86_64.BitslicedSse.stepsCode_succ]; exact VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ _ (by omega) w₁ (w₁ x hx)
    · rw [r₂, r₁, ← BitVec.shiftLeft_add, show 6 * n + 6 = 6 * (n + 1) by omega]
    · rw [show VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₁ = VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, c₁],
        show VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₁ = VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, si₁]] at f₂
      exact f₁.trans f₂

/-! ## A round -/

theorem round_eq (ρ : Role) : VG.Impl.TripleDes.X86_64.BitsliceSse.round ρ = keyLoad ++ VG.Proof.TripleDes.X86_64.BitslicedSse.stepsCode ρ 8 := rfl

theorem round_ok (ρ : Role) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) (hones : s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128)
    (hkey : InRegions (s.rd ++ s.wr) (s.gpr .r8) 8) :
    ∃ s', runBlock isa (VG.Impl.TripleDes.X86_64.BitsliceSse.round ρ) s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s' x = roundW ρ ((s.mem.readW (s.gpr .r8) 64).setWidth 48) (VG.Proof.TripleDes.X86_64.BitslicedSse.words s) x) ∧
      s'.gpr .r8 = s.gpr .r8 + s.gpr .r9 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, r₁, k₁, g₁, m₁, rd₁, wr₁, y₁⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.keyLoad_ok hkey
  have c₁ := g₁ .rcx (by decide) (by decide)
  have si₁ := g₁ .rsi (by decide) (by decide)
  have h₁ := h.congr c₁ si₁ wr₁
  obtain ⟨s₂, run₂, w₂, -, g₂, o₂, rd₂, wr₂, f₂⟩ :=
    VG.Proof.TripleDes.X86_64.BitslicedSse.stepsCode_ok ρ _ (Nat.le_refl 8) h₁ (by rw [y₁, hones]) r₁
  refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun r h1 h2 h3 => ?_, by rw [o₂, y₁], rd₂.trans rd₁,
    wr₂.trans wr₁, ?_⟩
  · rw [VG.Proof.TripleDes.X86_64.BitslicedSse.round_eq]; exact VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    have e : ∀ y, VG.Proof.TripleDes.X86_64.BitslicedSse.words s₁ y = VG.Proof.TripleDes.X86_64.BitslicedSse.words s y := fun y => by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.words, m₁, si₁]
    exact steps_congr ρ _ (Nat.le_refl 8) (fun y _ => e y) x hx
  · rw [g₂ _ (by decide) (by decide), k₁]
  · rw [g₂ r h1 h2, g₁ r h1 h3]
  · rw [show VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₁ = VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, c₁],
      show VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₁ = VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, si₁]] at f₂
    rw [m₁] at f₂
    exact f₂

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Pass`. -/
section

/-!
# An SSE2 DES pass on the machine

A pass chooses its first key's address (`r8`) and the step between keys
(`r9`) by the pass count (`r11`, `passStart`), runs eight pairs of rounds
(counted in `r10`), exchanges the halves and counts the pass. `pass_ok`: it
does to the state words what `swapW (pairs …)` does, with the keys read at
the addresses `a₀ + r δ`, which are apart from the scratch buffer and the
state words.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.StraightX VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceSse
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (roundW pairs swapW partner)
open VG.Proof.TripleDes.X86_64.Bitsliced (keyAt kptr_succ cnt_sub passA passD roundW_congr pairs_congr
  pairs_keys_congr swapW_congr)
open VG.Impl.TripleDes.X86_64.Bitslice (passKey)

/-- Eight readable bytes, apart from the scratch buffer and the state words. -/
structure Apart (s : VG.X86_64.State) (a : Addr) : Prop where
  read : InRegions (s.rd ++ s.wr) a 8
  scratch : (⟨a, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s)
  state : (⟨a, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s)

theorem Apart.congr {s s' : VG.X86_64.State} {a : Addr} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s a) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hsi : s'.gpr .rsi = s.gpr .rsi) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s' a where
  read := by rw [hrd, hwr]; exact h.read
  scratch := by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR, hc]; exact h.scratch
  state := by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, hsi]; exact h.state

theorem Apart.readW {s : VG.X86_64.State} {a : Addr} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s a) {m : Mem}
    (hf : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem m) : m.readW a 64 = s.mem.readW a 64 :=
  hf.readW (Region.contains_self a 8) (by simpa using ⟨h.scratch.sub_right (VG.Proof.TripleDes.X86_64.BitslicedSse.spill_sub s), h.state⟩)
    (by decide)

/-! ## Counting down a register -/

theorem sub1_run (s : VG.X86_64.State) (r : Reg) :
    ∃ s', runBlock isa [.alu .sub r (.imm 1)] s = some s' ∧ s'.gpr r = s.gpr r - 1 ∧
      s'.zf = some (s.gpr r - 1 == 0) ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ y, s'.xmm y = s.xmm y) := by
  let v := s.gpr r
  let t := v - (1 : BitVec 32).signExtend 64
  refine ⟨(arithFlags s t (decide (v.toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow v ((1 : BitVec 32).signExtend 64) t)).setReg r t, ?_, ?_, ?_, fun r' h => ?_,
    ?_, ?_, ?_, fun y => rfl⟩
  · rw [runBlock_cons]; rfl
  · simp only [gpr_setReg_self]; rfl
  · simp only [zf_setReg, zf_arithFlags]; rfl
  · simp [gpr_setReg, h]
  · simp [mem_setReg, mem_arithFlags]
  · simp [rd_setReg, rd_arithFlags]
  · simp [wr_setReg, wr_arithFlags]

/-! ## A pair of rounds -/

theorem roundPair_eq : roundPair = VG.Impl.TripleDes.X86_64.BitsliceSse.round .ba ++ VG.Impl.TripleDes.X86_64.BitsliceSse.round .ab ++ ([.alu .sub .r10 (.imm 1)] : List Instr) :=
  rfl

theorem roundPair_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) (hones : s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128)
    (h₁ : VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s (s.gpr .r8)) (h₂ : VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s (s.gpr .r8 + s.gpr .r9)) :
    ∃ s', runBlock isa roundPair s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s' x = roundW .ab ((s.mem.readW (s.gpr .r8 + s.gpr .r9) 64).setWidth 48)
        (roundW .ba ((s.mem.readW (s.gpr .r8) 64).setWidth 48) (VG.Proof.TripleDes.X86_64.BitslicedSse.words s)) x) ∧
      s'.gpr .r8 = s.gpr .r8 + s.gpr .r9 + s.gpr .r9 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some (s.gpr .r10 - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, key₁, g₁, o₁, rd₁, wr₁, f₁⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.round_ok .ba h hones h₁.read
  have c₁ := g₁ .rcx (by decide) (by decide) (by decide)
  have si₁ := g₁ .rsi (by decide) (by decide) (by decide)
  have r9₁ := g₁ .r9 (by decide) (by decide) (by decide)
  have h₁' := h.congr c₁ si₁ wr₁
  have a₂ : VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s₁ (s₁.gpr .r8) := by rw [key₁]; exact h₂.congr c₁ si₁ rd₁ wr₁
  obtain ⟨s₂, run₂, w₂, key₂, g₂, o₂, rd₂, wr₂, f₂⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.round_ok .ab h₁' (by rw [o₁, hones]) a₂.read
  obtain ⟨s₃, run₃, cnt₃, zf₃, g₃, m₃, rd₃, wr₃, y₃⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.sub1_run s₂ .r10
  have kread : s₁.mem.readW (s.gpr .r8 + s.gpr .r9) 64 = s.mem.readW (s.gpr .r8 + s.gpr .r9) 64 :=
    h₂.readW f₁
  have r10₂ : s₂.gpr .r10 = s.gpr .r10 := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)]
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, ?_, ?_, fun r a b c d => ?_, ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩
  · rw [VG.Proof.TripleDes.X86_64.BitslicedSse.roundPair_eq]; exact VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some (VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some run₁ run₂) run₃
  · have e : VG.Proof.TripleDes.X86_64.BitslicedSse.words s₃ x = VG.Proof.TripleDes.X86_64.BitslicedSse.words s₂ x := by
      simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.words, m₃, g₃ .rsi (by decide)]
    rw [e, w₂ x hx, key₁, kread]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.roundW_congr .ab _ w₁ x hx
  · rw [g₃ _ (by decide), key₂, key₁, r9₁]
  · rw [cnt₃, r10₂]
  · rw [zf₃, r10₂]
  · rw [g₃ r d, g₂ r a b c, g₁ r a b c]
  · rw [y₃, o₂, o₁]
  · have e₂ : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s₁.mem s₂.mem := by
      rwa [show VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₁ = VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, c₁],
        show VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₁ = VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, si₁]] at f₂
    rw [m₃]
    exact f₁.trans e₂

/-! ## The loop of pairs of rounds -/

/-- The registers a pass changes. -/
def PassRegs (r : Reg) : Prop := r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11

structure LoopInv (s₀ : VG.X86_64.State) (m : Nat) (s : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s
  ones : s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ m
  le : m ≤ 8
  words : ∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s x = pairs (keyAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9)) (8 - m) (VG.Proof.TripleDes.X86_64.BitslicedSse.words s₀) x
  key : s.gpr .r8 = s₀.gpr .r8 + BitVec.ofNat 64 (2 * (8 - m)) * s₀.gpr .r9
  cnt : s.gpr .r10 = BitVec.ofNat 64 m
  gpr : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₀] s₀.mem s.mem

structure LoopPost (s₀ s : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s
  ones : s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s x = pairs (keyAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9)) 8 (VG.Proof.TripleDes.X86_64.BitslicedSse.words s₀) x
  gpr : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₀] s₀.mem s.mem

theorem pairLoop_ok {s₀ : VG.X86_64.State} (hk : ∀ r < 16,
      VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s₀ (s₀.gpr .r8 + BitVec.ofNat 64 r * s₀.gpr .r9))
    (m₀ : Nat) (s₁ : VG.X86_64.State) (hs₁ : VG.Proof.TripleDes.X86_64.BitslicedSse.LoopInv s₀ m₀ s₁) :
    WP isa (.loop (.block roundPair) .ne) s₁ (VG.Proof.TripleDes.X86_64.BitslicedSse.LoopPost s₀) := by
  refine WP.loop (M := isa) (VG.Proof.TripleDes.X86_64.BitslicedSse.LoopInv s₀) ?_ m₀ s₁ hs₁
  intro m s hs
  let a₀ := s₀.gpr .r8
  let δ := s₀.gpr .r9
  have hδ : s.gpr .r9 = δ := hs.gpr _ (by decide) (by decide) (by decide) (by decide)
  have hc : s.gpr .rcx = s₀.gpr .rcx := hs.gpr _ (by decide) (by decide) (by decide) (by decide)
  have hsi : s.gpr .rsi = s₀.gpr .rsi := hs.gpr _ (by decide) (by decide) (by decide) (by decide)
  have n16 : 2 * (8 - m) + 1 < 16 := by have := hs.pos; omega
  have a₁ : VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s (s.gpr .r8) := by
    rw [hs.key]; exact (hk _ (by omega)).congr hc hsi hs.rd hs.wr
  have a₂ : VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s (s.gpr .r8 + s.gpr .r9) := by
    rw [hs.key, hδ, kptr_succ]; exact (hk _ n16).congr hc hsi hs.rd hs.wr
  obtain ⟨s', run', w', key', cnt', zf', g', o', rd', wr', f'⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.roundPair_ok hs.room hs.ones a₁ a₂
  refine WP.of_runBlock ⟨s', run', ?_⟩
  have frame' : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₀] s₀.mem s'.mem := by
    have := hs.frame
    rw [show VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s = VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀ by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, hc],
      show VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s = VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₀ by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, hsi]] at f'
    exact this.trans f'
  have k1 : (s.mem.readW (s.gpr .r8) 64).setWidth 48 = keyAt s₀.mem a₀ δ (2 * (8 - m)) := by
    rw [hs.key]; simp only [keyAt]
    rw [((hk _ (by omega)).readW hs.frame)]
  have k2 : (s.mem.readW (s.gpr .r8 + s.gpr .r9) 64).setWidth 48 =
      keyAt s₀.mem a₀ δ (2 * (8 - m) + 1) := by
    rw [hs.key, hδ, kptr_succ]; simp only [keyAt]
    rw [((hk _ n16).readW hs.frame)]
  have words' : ∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s' x = pairs (keyAt s₀.mem a₀ δ) (8 - m + 1) (VG.Proof.TripleDes.X86_64.BitslicedSse.words s₀) x := by
    intro x hx
    rw [w' x hx, k1, k2]
    simp only [pairs]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.roundW_congr .ab _ (VG.Proof.TripleDes.X86_64.Bitsliced.roundW_congr .ba _ hs.words) x hx
  have gpr' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s₀.gpr r :=
    fun r a b c d => (g' r a b c d).trans (hs.gpr r a b c d)
  have room' := hs.room.congr (g' _ (by decide) (by decide) (by decide) (by decide))
    (g' _ (by decide) (by decide) (by decide) (by decide)) wr'
  have ones' : s'.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128 := by rw [o', hs.ones]
  have cntv : s.gpr .r10 - 1 = BitVec.ofNat 64 (m - 1) := by
    rw [hs.cnt]
    exact cnt_sub m hs.pos
  by_cases h1 : m = 1
  · subst h1
    left
    refine ⟨?_, ⟨room', ones', rd'.trans hs.rd, wr'.trans hs.wr, words', gpr', frame'⟩⟩
    show s'.zf.map (!·) = some false
    rw [zf', cntv]; rfl
  · right
    refine ⟨?_, m - 1, by omega, ⟨room', ones', rd'.trans hs.rd, wr'.trans hs.wr, by omega,
      by have := hs.le; omega, ?_, ?_, ?_, gpr', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [zf', cntv]
      have : (BitVec.ofNat 64 (m - 1) == 0) = false := by
        have hm : m ≤ 8 := hs.le
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by omega)] at this
        have := hs.pos
        omega
      rw [this]; rfl
    · have e : 8 - (m - 1) = 8 - m + 1 := by have := hs.le; omega
      rw [e]; exact words'
    · rw [key', hs.key, hδ, kptr_succ, kptr_succ]
      congr 3
      have := hs.le; omega
    · rw [cnt', cntv]

/-! ## The start of a pass -/

/-- What the start of a pass leaves. -/
structure StartPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : VG.X86_64.State) : Prop where
  key : s'.gpr .r8 = s.gpr .rdi + BitVec.ofNat 64 (passKey d p).1
  step : s'.gpr .r9 = BitVec.ofInt 64 (passKey d p).2
  round : s'.gpr .r10 = 8
  gpr : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ y, s'.xmm y = s.xmm y

theorem passKey_imm : ∀ d : Spec.TripleDes.Direction, ∀ p, 1 ≤ p → p ≤ 3 →
    (BitVec.ofNat 32 (passKey d p).1).signExtend 64 = BitVec.ofNat 64 (passKey d p).1 ∧
    (BitVec.ofInt 32 (passKey d p).2).signExtend 64 = BitVec.ofInt 64 (passKey d p).2 := by
  intro d p h1 h3
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | decide

/-- A comparison of a register with an immediate. -/
def cmpState (s : VG.X86_64.State) (r : Reg) (v : BitVec 32) : VG.X86_64.State :=
  arithFlags s (s.gpr r - v.signExtend 64) (decide ((s.gpr r).toNat < (v.signExtend 64).toNat))
    (subOverflow (s.gpr r) (v.signExtend 64) (s.gpr r - v.signExtend 64))

theorem cmp_run (s : VG.X86_64.State) (r : Reg) (v : BitVec 32) :
    runBlock isa [.alu .cmp r (.imm v)] s = some (VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState s r v) := by
  rw [runBlock_cons]
  rfl

theorem passStart_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : VG.X86_64.State}
    (hc : s.gpr .r11 = BitVec.ofNat 64 p) :
    WP isa (VG.Impl.TripleDes.X86_64.BitsliceSse.passStart d) s (VG.Proof.TripleDes.X86_64.BitslicedSse.StartPost d p s) := by
  -- the code of a branch, and what follows it
  have branch : ∀ (s₁ : VG.X86_64.State), s₁.gpr = s.gpr → s₁.mem = s.mem → s₁.rd = s.rd → s₁.wr = s.wr →
      (∀ y, s₁.xmm y = s.xmm y) →
      WP isa (.block (passKeyCode d p)) s₁ (fun s₂ =>
        WP isa (.block [.mov .r10 (.imm 8)]) s₂ (VG.Proof.TripleDes.X86_64.BitslicedSse.StartPost d p s)) := by
    intro s₁ g₁ m₁ rd₁ wr₁ y₁
    let t₁ := s₁.setReg .r8 (s₁.gpr .rdi)
    let a := BitVec.ofNat 32 (passKey d p).1
    let t₂ := (arithFlags t₁ (t₁.gpr .r8 + a.signExtend 64)
      (decide (2 ^ 64 ≤ (t₁.gpr .r8).toNat + (a.signExtend 64).toNat))
      (addOverflow (t₁.gpr .r8) (a.signExtend 64) (t₁.gpr .r8 + a.signExtend 64))).setReg .r8
      (t₁.gpr .r8 + a.signExtend 64)
    let t₃ := t₂.setReg .r9 ((BitVec.ofInt 32 (passKey d p).2).signExtend 64)
    refine WP.of_runBlock ⟨t₃, ?_, ?_⟩
    · rw [passKeyCode, runBlock_cons, show exec (.mov .r8 (.reg .rdi)) s₁ = some t₁ from rfl,
        runStep_some, runBlock_cons, show exec (.alu .add .r8 (.imm a)) t₁ = some t₂ from rfl,
        runStep_some, runBlock_cons, show exec (.mov .r9 (.imm (BitVec.ofInt 32 (passKey d p).2))) t₂ =
          some t₃ from rfl, runStep_some, runBlock_nil]
    let t₄ := t₃.setReg .r10 ((8 : BitVec 32).signExtend 64)
    refine WP.of_runBlock ⟨t₄, by rw [runBlock_cons]; rfl, ?_⟩
    obtain ⟨i1, i2⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.passKey_imm d p hp.1 hp.2
    refine ⟨?_, ?_, ?_, fun r a b c => ?_, ?_, ?_, ?_, fun y => ?_⟩
    · simp [t₄, t₃, t₂, t₁, gpr_setReg, g₁, a, i1]
    · simp [t₄, t₃, gpr_setReg, i2]
    · simp [t₄, gpr_setReg]
    · simp [t₄, t₃, t₂, t₁, gpr_setReg, a, b, c, g₁]
    · simp [t₄, t₃, t₂, t₁, mem_setReg, mem_arithFlags, m₁]
    · simp [t₄, t₃, t₂, t₁, rd_setReg, rd_arithFlags, rd₁]
    · simp [t₄, t₃, t₂, t₁, wr_setReg, wr_arithFlags, wr₁]
    · rw [← y₁ y]; rfl
  apply WP.seq
  let t₁ := VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState s .r11 3
  refine WP.of_runBlock ⟨t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmp_run s .r11 3, ?_⟩
  apply WP.seq
  have zf₁ : isa.eval .e t₁ = some (p == 3) := by
    show t₁.zf = _
    simp only [t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, zf_arithFlags, hc]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide
  apply WP.ite (p == 3) zf₁
  · intro h3
    have : p = 3 := by simpa using h3
    subst this
    exact branch t₁ (by simp [t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState]) (by simp [t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, mem_arithFlags])
      (by simp [t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, rd_arithFlags]) (by simp [t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, wr_arithFlags]) (fun _ => rfl)
  · intro h3
    have hp3 : p ≠ 3 := by simpa using h3
    apply WP.seq
    let t₂ := VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState t₁ .r11 2
    refine WP.of_runBlock ⟨t₂, VG.Proof.TripleDes.X86_64.BitslicedSse.cmp_run t₁ .r11 2, ?_⟩
    have zf₂ : isa.eval .e t₂ = some (p == 2) := by
      show t₂.zf = _
      simp only [t₂, t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, zf_arithFlags, gpr_arithFlags, hc]
      rcases hp with ⟨h1, h3⟩
      rcases p with _ | _ | _ | _ | p <;> first | omega | decide
    have g₂ : t₂.gpr = s.gpr := by simp [t₂, t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState]
    have m₂ : t₂.mem = s.mem := by simp [t₂, t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, mem_arithFlags]
    have rd₂ : t₂.rd = s.rd := by simp [t₂, t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, rd_arithFlags]
    have wr₂ : t₂.wr = s.wr := by simp [t₂, t₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, wr_arithFlags]
    apply WP.ite (p == 2) zf₂
    · intro h2
      have : p = 2 := by simpa using h2
      subst this
      exact branch t₂ g₂ m₂ rd₂ wr₂ (fun _ => rfl)
    · intro h2
      have : p = 1 := by have : p ≠ 2 := by simpa using h2
                         omega
      subst this
      exact branch t₂ g₂ m₂ rd₂ wr₂ (fun _ => rfl)

/-! ## A pass -/

structure PassPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s'
  ones : s'.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  words : ∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s' x =
    swapW (pairs (keyAt s.mem (passA d p (s.gpr .rdi)) (passD d p)) 8 (VG.Proof.TripleDes.X86_64.BitslicedSse.words s)) x
  count : s'.gpr .r11 = s.gpr .r11 - 1
  zf : s'.zf = some (s.gpr .r11 - 1 == 0)
  gpr : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs r → s'.gpr r = s.gpr r
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s'.mem

theorem pass_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : VG.X86_64.State}
    (h : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s) (hones : s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128) (hc : s.gpr .r11 = BitVec.ofNat 64 p)
    (hk : ∀ r < 16, VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s (passA d p (s.gpr .rdi) + BitVec.ofNat 64 r * passD d p)) :
    WP isa (VG.Impl.TripleDes.X86_64.BitsliceSse.pass d) s (VG.Proof.TripleDes.X86_64.BitslicedSse.PassPost d p s) := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.BitslicedSse.passStart_ok d hp hc)
  intro s₁ p₁
  have c₁ := p₁.gpr .rcx (by decide) (by decide) (by decide)
  have si₁ := p₁.gpr .rsi (by decide) (by decide) (by decide)
  have h₁ := h.congr c₁ si₁ p₁.wr
  apply WP.seq
  have hk₁ : ∀ r < 16, VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s₁ (s₁.gpr .r8 + BitVec.ofNat 64 r * s₁.gpr .r9) := by
    intro r hr
    rw [p₁.key, p₁.step]; exact (hk r hr).congr c₁ si₁ p₁.rd p₁.wr
  have inv : VG.Proof.TripleDes.X86_64.BitslicedSse.LoopInv s₁ 8 s₁ := by
    refine ⟨h₁, by rw [p₁.xmm, hones], rfl, rfl, by decide, by decide, fun _ _ => rfl, ?_, ?_,
      fun _ _ _ _ _ => rfl, Frame.refl _ _⟩
    · simp
    · rw [p₁.round]; rfl
  apply WP.mono (VG.Proof.TripleDes.X86_64.BitslicedSse.pairLoop_ok hk₁ 8 s₁ inv)
  intro s₂ p₂
  have h₂ := p₂.room
  obtain ⟨s₃, run₃, sw₃, g₃, o₃, rd₃, wr₃, f₃⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.swapHalves_ok h₂
  obtain ⟨s₄, run₄, cnt₄, zf₄, g₄, m₄, rd₄, wr₄, y₄⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.sub1_run s₃ .r11
  refine WP.of_runBlock ⟨s₄, VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some run₃ run₄, ?_⟩
  have keys : ∀ r < 16, keyAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9) r =
      keyAt s.mem (passA d p (s.gpr .rdi)) (passD d p) r := by
    intro r hr
    simp only [keyAt, p₁.key, p₁.step, p₁.mem]
    rfl
  have state₁ : ∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s₁ x = VG.Proof.TripleDes.X86_64.BitslicedSse.words s x := fun x _ => by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.words, p₁.mem, si₁]
  have gs₂ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s₂.gpr r = s.gpr r :=
    fun r a b c e f => (p₂.gpr r a b c f).trans (p₁.gpr r c e f)
  have r11₃ : s₃.gpr .r11 = s.gpr .r11 := by
    rw [g₃, gs₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have c₂ := gs₂ .rcx (by decide) (by decide) (by decide) (by decide) (by decide)
  have si₂ := gs₂ .rsi (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨h.congr (by rw [g₄ _ (by decide), g₃, c₂]) (by rw [g₄ _ (by decide), g₃, si₂])
      (wr₄.trans (wr₃.trans (p₂.wr.trans p₁.wr))),
    by rw [y₄, o₃, p₂.ones], rd₄.trans (rd₃.trans (p₂.rd.trans p₁.rd)),
    wr₄.trans (wr₃.trans (p₂.wr.trans p₁.wr)), fun x hx => ?_, ?_, ?_,
    fun r hr => ?_, ?_⟩
  · have e : VG.Proof.TripleDes.X86_64.BitslicedSse.words s₄ x = VG.Proof.TripleDes.X86_64.BitslicedSse.words s₃ x := by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.words, m₄, g₄ .rsi (by decide)]
    rw [e, sw₃ x hx]
    apply VG.Proof.TripleDes.X86_64.Bitsliced.swapW_congr _ x hx
    intro y hy
    rw [p₂.words y hy, VG.Proof.TripleDes.X86_64.Bitsliced.pairs_keys_congr 8 (fun r hr => keys r (by omega))]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.pairs_congr _ 8 state₁ y hy
  · rw [cnt₄, r11₃]
  · rw [zf₄, r11₃]
  · obtain ⟨a, b, c, e, f, g⟩ := hr
    rw [g₄ r g, g₃, gs₂ r a b c e f]
  · have g₃' : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s₂.mem s₃.mem := by
      refine f₃.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, si₂]; exact fun _ h => h⟩
    have g₂ := p₂.frame
    rw [show VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₁ = VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, c₁],
      show VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₁ = VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, si₁], p₁.mem] at g₂
    rw [m₄]
    exact g₂.trans g₃'

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Passes`. -/
section

/-!
# The three SSE2 passes

The loop of passes, counted down from 3 in `r11`, does to the state words
what three DES passes do (`chain`), with the components and directions of
TDEA, in every lane.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceSse VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (passW pairs swapW)
open VG.Proof.TripleDes.X86_64.Bitsliced (chain keyAt passA passD passComp passIdx_lt passAddr_eq
  keyAt_pass cnt_sub pairs_keys_congr pairs_congr swapW_congr)

/-- The key words of the passes are apart from the scratch buffer and the state. -/
theorem passKeys_apart {s : VG.X86_64.State} {S : Addr} (hS : ∀ i < 48, VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s (S + BitVec.ofNat 64 (8 * i)))
    (d : VG.Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {r : Nat} (hr : r < 16) :
    VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s (passA d p S + BitVec.ofNat 64 r * passD d p) := by
  simp only [passA, passD]
  rw [BitVec.add_assoc, passAddr_eq d p hp.1 hp.2 r hr]
  exact hS _ (passIdx_lt d p hp.1 hp.2 r hr)

structure PassesInv (d : VG.Spec.TripleDes.Direction) (s₀ : VG.X86_64.State) (p : Nat) (s : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s
  ones : s.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ p
  le : p ≤ 3
  words : ∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s x = chain d (VG.Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) (3 - p) (VG.Proof.TripleDes.X86_64.BitslicedSse.words s₀) x
  count : s.gpr .r11 = BitVec.ofNat 64 p
  gpr : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs r → s.gpr r = s₀.gpr r
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₀] s₀.mem s.mem

structure PassesPost (d : VG.Spec.TripleDes.Direction) (s₀ s : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s x = chain d (VG.Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) 3 (VG.Proof.TripleDes.X86_64.BitslicedSse.words s₀) x
  gpr : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs r → s.gpr r = s₀.gpr r
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₀] s₀.mem s.mem

theorem passes_ok (d : VG.Spec.TripleDes.Direction) {s₀ : VG.X86_64.State}
    (hS : ∀ i < 48, VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s₀ (s₀.gpr .rdi + BitVec.ofNat 64 (8 * i)))
    (p₀ : Nat) (s₁ : VG.X86_64.State) (hs₁ : VG.Proof.TripleDes.X86_64.BitslicedSse.PassesInv d s₀ p₀ s₁) :
    WP isa (.loop (VG.Impl.TripleDes.X86_64.BitsliceSse.pass d) .ne) s₁ (VG.Proof.TripleDes.X86_64.BitslicedSse.PassesPost d s₀) := by
  refine WP.loop (M := isa) (VG.Proof.TripleDes.X86_64.BitslicedSse.PassesInv d s₀) ?_ p₀ s₁ hs₁
  intro p s hs
  let S := s₀.gpr .rdi
  have g : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs r → s.gpr r = s₀.gpr r := hs.gpr
  have hS' : s.gpr .rdi = S := g _ (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have hc := g .rcx (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have hsi := g .rsi (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have hp : 1 ≤ p ∧ p ≤ 3 := ⟨hs.pos, hs.le⟩
  have hk : ∀ r < 16, VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s (passA d p (s.gpr .rdi) + BitVec.ofNat 64 r * passD d p) := by
    intro r hr
    rw [hS']
    exact (VG.Proof.TripleDes.X86_64.BitslicedSse.passKeys_apart hS d hp hr).congr hc hsi hs.rd hs.wr
  apply WP.mono (VG.Proof.TripleDes.X86_64.BitslicedSse.pass_ok d hp hs.room hs.ones hs.count hk)
  intro s' q
  have keys : ∀ r < 16, keyAt s.mem (passA d p (s.gpr .rdi)) (passD d p) r =
      VG.Proof.TripleDes.roundKey (componentSchedule (VG.Spec.TripleDes.scheduleAt s₀.mem S) (passComp d p).1)
        (passComp d p).2 r := by
    intro r hr
    have e := (VG.Proof.TripleDes.X86_64.BitslicedSse.passKeys_apart hS d hp hr).readW hs.frame
    simp only [keyAt, hS']
    rw [e, ← keyAt_pass s₀.mem S d hp hr]; rfl
  have words' : ∀ x < 64, VG.Proof.TripleDes.X86_64.BitslicedSse.words s' x = chain d (VG.Spec.TripleDes.scheduleAt s₀.mem S) (3 - p + 1) (VG.Proof.TripleDes.X86_64.BitslicedSse.words s₀) x := by
    intro x hx
    rw [q.words x hx, VG.Proof.TripleDes.X86_64.Bitsliced.pairs_keys_congr 8 (fun r hr => keys r (by omega))]
    simp only [chain, show 3 - (3 - p) = p by omega]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.swapW_congr (VG.Proof.TripleDes.X86_64.Bitsliced.pairs_congr _ 8 hs.words) x hx
  have gpr' : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs r → s'.gpr r = s₀.gpr r := fun r hr => (q.gpr r hr).trans (g r hr)
  have frame' : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₀] s₀.mem s'.mem := by
    have := q.frame
    rw [show VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s = VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀ by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, hc],
      show VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s = VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₀ by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, hsi]] at this
    exact hs.frame.trans this
  have cntv : s.gpr .r11 - 1 = BitVec.ofNat 64 (p - 1) := by rw [hs.count]; exact cnt_sub p hs.pos
  by_cases h1 : p = 1
  · subst h1
    left
    refine ⟨?_, q.room, q.rd.trans hs.rd, q.wr.trans hs.wr, words', gpr', frame'⟩
    show s'.zf.map (!·) = some false
    rw [q.zf, cntv]; rfl
  · right
    refine ⟨?_, p - 1, by omega, ⟨q.room, q.ones, q.rd.trans hs.rd, q.wr.trans hs.wr, by omega,
      by omega, ?_, ?_, gpr', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [q.zf, cntv]
      have : (BitVec.ofNat 64 (p - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by omega)] at this
        omega
      rw [this]; rfl
    · rw [show 3 - (p - 1) = 3 - p + 1 by omega]; exact words'
    · rw [q.count, cntv]

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Batch`. -/
section

/-!
# An SSE2 batch

A batch of 128 blocks, in place: each quadword lane `q` of the 64 state
words (the 1024 bytes at `rsi`) is transposed, so that lane `64 q + i` of
the words is IP of block `2 i + q`; the three passes run; the lanes are
transposed back, and each block becomes its TDEA encryption or decryption
(`batch_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.StraightX VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceSse
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW ipLane_bit)
open VG.Proof.TripleDes.X86_64.Bitsliced (chain chain_lane blockOut blockOut_cores ipLane_congr wAt
  readW_bit blockAt_of_readW)

/-! ## Quadword lanes as blocks -/

theorem qw_readW (m : Mem) (a : Addr) {q : Nat} (hq : q < 2) :
    qword (m.readW a 128) q = m.readW (a + BitVec.ofNat 64 q * 8) 64 := by
  have e := readW_extract m a (w := 128) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * (8 * q) = 64 * q by omega, show 8 * 8 = 64 by rfl] at e
  rw [qword, e]
  congr 2
  rw [BitVec.mul_comm, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_mul_ofNat]

/-- Quadword `q` of state word `i` is block `2 i + q`. -/
theorem laneW_eq (s : VG.X86_64.State) {q i : Nat} (hq : q < 2) :
    VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s q i = s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) (2 * i + q)) 64 := by
  simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.laneW, VG.Proof.TripleDes.X86_64.BitslicedSse.words, xAddr]
  rw [VG.Proof.TripleDes.X86_64.BitslicedSse.qw_readW _ _ hq, BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  have e : ∀ a b : Nat, a = b → s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 a) 64 =
      s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 b) 64 := fun a b h => by rw [h]
  exact e _ _ (by omega)

/-- Lane `64 q + i` of 128-bit words is lane `i` of their quadwords `q`. -/
theorem ipLane_qw {W : Nat → BitVec 128} {q i : Nat} (hi : i < 64) :
    ipLane W (64 * q + i) = ipLane (fun j => qword (W j) q) i := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [ipLane_bit _ _ ht, ipLane_bit _ _ ht, getLsbD_qword _ hi]

/-! ## The batch -/

/-- What a batch needs: the scratch buffer and the 128 blocks' state words,
and the schedule's words, readable and apart from both. -/
structure BatchPre (s : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s
  sched : ∀ i < 48, VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s (s.gpr .rdi + BitVec.ofNat 64 (8 * i))
  schedSep : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s)

structure BatchPost (d : VG.Spec.TripleDes.Direction) (s s' : VG.X86_64.State) : Prop where
  out : ∀ b < 128, VG.Spec.TripleDes.blockAt s'.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) b) =
    VG.Proof.TripleDes.X86_64.Bitsliced.blockOut (VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d (VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) b))
  rsi : s'.gpr .rsi = s.gpr .rsi + 1024
  rdx : s'.gpr .rdx = s.gpr .rdx - 128
  cf : s'.cf = some (decide ((s.gpr .rdx - 128).toNat < 128))
  gpr : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs r → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s'.mem

theorem frame_into {rs : List Region} {m m' : Mem} {r : Region} (h : VG.Frame [r] m m') (hr : r ∈ rs) :
    VG.Frame rs m m' :=
  h.mono fun r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr

theorem batch_ok (d : VG.Spec.TripleDes.Direction) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.BatchPre s) : WP isa (batch d) s (VG.Proof.TripleDes.X86_64.BitslicedSse.BatchPost d s) := by
  let S := s.gpr .rdi
  let D := s.gpr .rsi
  rw [batch]
  apply WP.seq
  -- the transposition, all ones, and the count of passes
  obtain ⟨s₁, run₁, w₁, g₁, -, -, rd₁, wr₁, f₁⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.transpose_ok h.room.state
  let t₁ := s₁.setReg .rbx (BitVec.allOnes 64)
  let t₂ := (XOp.movq VG.Impl.TripleDes.X86_64.BitsliceSse.ones .rbx).exec t₁
  let t₃ := (XOp.bin .punpcklqdq VG.Impl.TripleDes.X86_64.BitsliceSse.ones VG.Impl.TripleDes.X86_64.BitsliceSse.ones).exec t₂
  let s₂ := t₃.setReg .r11 ((3 : BitVec 32).signExtend 64)
  refine WP.of_runBlock ⟨s₂, VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some (VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some run₁ (by
    rw [bcast, runBlock_cons, show exec (.movImm64 .rbx (BitVec.allOnes 64)) s₁ = some t₁ from rfl,
      runStep_some, runBlock_cons, show exec (.xop (.movq VG.Impl.TripleDes.X86_64.BitsliceSse.ones .rbx)) t₁ = some t₂ from rfl,
      runStep_some, runBlock_cons,
      show exec (xbin .punpcklqdq VG.Impl.TripleDes.X86_64.BitsliceSse.ones VG.Impl.TripleDes.X86_64.BitsliceSse.ones) t₂ = some t₃ from rfl, runStep_some,
      runBlock_nil])) (by rw [runBlock_cons]; rfl), ?_⟩
  have ones₂ : s₂.xmm VG.Impl.TripleDes.X86_64.BitsliceSse.ones = BitVec.allOnes 128 :=
    VG.Proof.TripleDes.X86_64.BitslicedSse.bcast_mask t₁ VG.Impl.TripleDes.X86_64.BitsliceSse.ones .rbx true (by simp [t₁, gpr_setReg, VG.Proof.TripleDes.X86_64.BitslicedSse.maskVal])
  have g₂ : ∀ r, r ≠ .rbx → r ≠ .r11 → s₂.gpr r = s.gpr r := by
    intro r a b
    simp [s₂, t₃, t₂, t₁, XOp.exec, State.setXmm, gpr_setReg, a, b, g₁ r a]
  have m₂ : s₂.mem = s₁.mem := by simp [s₂, t₃, t₂, t₁, XOp.exec, State.setXmm, mem_setReg]
  have rd₂ : s₂.rd = s.rd := by simp [s₂, t₃, t₂, t₁, XOp.exec, State.setXmm, rd_setReg, rd₁]
  have wr₂ : s₂.wr = s.wr := by simp [s₂, t₃, t₂, t₁, XOp.exec, State.setXmm, wr_setReg, wr₁]
  have c₂ := g₂ .rcx (by decide) (by decide)
  have si₂ := g₂ .rsi (by decide) (by decide)
  have di₂ := g₂ .rdi (by decide) (by decide)
  have h₂ : VG.Proof.TripleDes.X86_64.BitslicedSse.Room s₂ := h.room.congr c₂ si₂ wr₂
  have words₂ : ∀ j, VG.Proof.TripleDes.X86_64.BitslicedSse.words s₂ j = VG.Proof.TripleDes.X86_64.BitslicedSse.words s₁ j := fun j => by
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.words, m₂, si₂, g₁ .rsi (by decide)]
  have scr₂ : VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₂ = VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s := by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, c₂]
  have st₂ : VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₂ = VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s := by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, si₂]
  have f₂ : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s.mem s₂.mem := by
    rw [m₂]; exact VG.Proof.TripleDes.X86_64.BitslicedSse.frame_into f₁ (List.mem_cons_of_mem _ List.mem_cons_self)
  -- the passes
  apply WP.seq
  have hS₂ : ∀ i < 48, VG.Proof.TripleDes.X86_64.BitslicedSse.Apart s₂ (s₂.gpr .rdi + BitVec.ofNat 64 (8 * i)) := by
    intro i hi; rw [di₂]; exact (h.sched i hi).congr c₂ si₂ rd₂ wr₂
  have inv : VG.Proof.TripleDes.X86_64.BitslicedSse.PassesInv d s₂ 3 s₂ :=
    ⟨h₂, ones₂, rfl, rfl, by decide, by decide, fun _ _ => rfl, by simp [s₂, gpr_setReg],
      fun _ _ => rfl, Frame.refl _ _⟩
  apply WP.mono (VG.Proof.TripleDes.X86_64.BitslicedSse.passes_ok d hS₂ 3 s₂ inv)
  intro s₃ q₃
  have g₃ : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs r → s₃.gpr r = s.gpr r := by
    intro r hr; rw [q₃.gpr r hr, g₂ r hr.2.1 hr.2.2.2.2.2]
  have si₃ := g₃ .rsi (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have c₃ := g₃ .rcx (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have rdx₃ := g₃ .rdx (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  -- the transposition back, and the next batch
  obtain ⟨s₄, run₄, w₄, g₄, -, -, rd₄, wr₄, f₄⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.transpose_ok q₃.room.state
  have si₄ : s₄.gpr .rsi = D := (g₄ .rsi (by decide)).trans si₃
  have rdx₄ : s₄.gpr .rdx = s.gpr .rdx := (g₄ .rdx (by decide)).trans rdx₃
  let u₁ := (arithFlags s₄ (s₄.gpr .rsi + (1024 : BitVec 32).signExtend 64)
    (decide (2 ^ 64 ≤ (s₄.gpr .rsi).toNat + ((1024 : BitVec 32).signExtend 64).toNat))
    (addOverflow (s₄.gpr .rsi) ((1024 : BitVec 32).signExtend 64)
      (s₄.gpr .rsi + (1024 : BitVec 32).signExtend 64))).setReg .rsi
    (s₄.gpr .rsi + (1024 : BitVec 32).signExtend 64)
  let v := u₁.gpr .rdx - (128 : BitVec 32).signExtend 64
  let u₂ := (arithFlags u₁ v (decide ((u₁.gpr .rdx).toNat < ((128 : BitVec 32).signExtend 64).toNat))
    (subOverflow (u₁.gpr .rdx) ((128 : BitVec 32).signExtend 64) v)).setReg .rdx v
  let s₅ := VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState u₂ .rdx 128
  refine WP.of_runBlock ⟨s₅, VG.Proof.TripleDes.X86_64.BitslicedSse.runBlock_cat_some run₄ (by
    rw [runBlock_cons, show exec (.alu .add .rsi (.imm 1024)) s₄ = some u₁ from rfl, runStep_some,
      runBlock_cons, show exec (.alu .sub .rdx (.imm 128)) u₁ = some u₂ from rfl, runStep_some,
      VG.Proof.TripleDes.X86_64.BitslicedSse.cmp_run]), ?_⟩
  have m₅ : s₅.mem = s₄.mem := by simp [s₅, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, u₂, u₁, mem_setReg, mem_arithFlags]
  have g₅ : ∀ r, r ≠ .rsi → r ≠ .rdx → s₅.gpr r = s₄.gpr r := by
    intro r a b; simp [s₅, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, u₂, u₁, gpr_setReg, a, b]
  have rdx₅ : s₅.gpr .rdx = s.gpr .rdx - 128 := by
    simp [s₅, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, u₂, u₁, gpr_setReg, v, rdx₄]
  -- every block of the batch
  have K₂ : VG.Spec.TripleDes.scheduleAt s₂.mem (s₂.gpr .rdi) = VG.Spec.TripleDes.scheduleAt s.mem S := by
    rw [di₂, m₂]
    exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.schedSep
  refine ⟨fun b hb => ?_, ?_, rdx₅, ?_, fun r hr a c => ?_, ?_, ?_, ?_⟩
  · have hq : b % 2 < 2 := Nat.mod_lt _ (by decide)
    have hi : b / 2 < 64 := by omega
    have eb : 2 * (b / 2) + b % 2 = b := Nat.div_add_mod b 2
    -- lane 64 q + i before the passes: IP of the block
    have lane₂ : ipLane (VG.Proof.TripleDes.X86_64.BitslicedSse.words s₂) (64 * (b % 2) + b / 2) =
        permute ip (VG.Spec.TripleDes.decodeBlock (VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b))) := by
      rw [VG.Proof.TripleDes.X86_64.BitslicedSse.ipLane_qw hi]
      have e : ∀ j < 64, qword (VG.Proof.TripleDes.X86_64.BitslicedSse.words s₂ j) (b % 2) = transposeW (VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s (b % 2)) j := by
        intro j hj; rw [words₂]; exact w₁ _ hq j hj
      rw [VG.Proof.TripleDes.X86_64.Bitsliced.ipLane_congr e]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hi fun j hj => ?_
      rw [VG.Proof.TripleDes.X86_64.BitslicedSse.laneW_eq s hq, eb]
      exact readW_bit s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) hj
    -- the block's word at the end
    have word₅ : s₅.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) 64 = transposeW (VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s₃ (b % 2)) (b / 2) := by
      rw [m₅, ← w₄ _ hq _ hi, VG.Proof.TripleDes.X86_64.BitslicedSse.laneW_eq s₄ hq, si₄, eb]
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.blockOut_cores, ← K₂]
    apply blockAt_of_readW
    intro j hj
    rw [word₅, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj]
    have e₃ : ipLane (VG.Proof.TripleDes.X86_64.BitslicedSse.laneW s₃ (b % 2)) (b / 2) = ipLane (VG.Proof.TripleDes.X86_64.BitslicedSse.words s₃) (64 * (b % 2) + b / 2) :=
      (VG.Proof.TripleDes.X86_64.BitslicedSse.ipLane_qw hi).symm
    rw [e₃, VG.Proof.TripleDes.X86_64.Bitsliced.ipLane_congr q₃.words, chain_lane d _ _ (by omega), lane₂]
  · simp [s₅, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, u₂, u₁, gpr_setReg, si₄]; rfl
  · have u₂d : u₂.gpr .rdx = s.gpr .rdx - 128 := by
      simp [u₂, u₁, gpr_setReg, v, rdx₄]
    simp only [s₅, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, cf_arithFlags, u₂d,
      show ((128 : BitVec 32).signExtend 64).toNat = 128 by decide]
  · rw [g₅ r a c, g₄ r hr.2.1, g₃ r hr]
  · simp [s₅, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, u₂, u₁, rd_setReg, rd_arithFlags, rd₄, q₃.rd, rd₂]
  · simp [s₅, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, u₂, u₁, wr_setReg, wr_arithFlags, wr₄, q₃.wr, wr₂]
  · have a := q₃.frame
    rw [scr₂, st₂] at a
    have b : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s, VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s] s₃.mem s₄.mem := by
      rw [show VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s₃ = VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, si₃]] at f₄
      exact VG.Proof.TripleDes.X86_64.BitslicedSse.frame_into f₄ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [m₅]
    exact (f₂.trans a).trans b

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit`. -/
section

namespace VG

materialize_code Impl.TripleDes.X86_64.BitsliceSse.encrypt
materialize_code Impl.TripleDes.X86_64.BitsliceSse.decrypt

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.ConstantTime`. -/
section

/-!
# Constant time

As for the 64-block code: the pointers, the count of blocks and the stack
pointer are public, and so is everything the function computes from them
(the batches, the counts of passes and rounds, the addresses of the round
keys), which the batches of 128 blocks keep in registers.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64
open VG.Proof.TripleDes.X86_64.Bitsliced (ecbTaint)

/-! The analyses, with the summaries of the 64-block code they end with. -/

taint_summary encSum : taintS ecbTaint Impl.TripleDes.X86_64.BitsliceSse.encrypt
  using Bitsliced.encSum
taint_summary decSum : taintS ecbTaint Impl.TripleDes.X86_64.BitsliceSse.decrypt
  using Bitsliced.decSum

theorem encrypt_constantTime (pre : VG.X86_64.State → Prop) (pub : VG.X86_64.State → VG.X86_64.State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree ecbTaint s t) :
    ConstantTime isa pre pub Impl.TripleDes.X86_64.BitsliceSse.encrypt :=
  let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk encSum (by decide +kernel)
  VG.Taint.constantTime (A := taintS) ecbTaint hagree h

theorem decrypt_constantTime (pre : VG.X86_64.State → Prop) (pub : VG.X86_64.State → VG.X86_64.State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree ecbTaint s t) :
    ConstantTime isa pre pub Impl.TripleDes.X86_64.BitsliceSse.decrypt :=
  let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk decSum (by decide +kernel)
  VG.Taint.constantTime (A := taintS) ecbTaint hagree h

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Wide`. -/
section

/-!
# Batches of 128 blocks

While at least 128 blocks are left, the SSE2 code runs a batch on the next
128 (`wide_ok`): of the `n` blocks, the first `n - n % 128` become their
encryption or decryption, and `rsi` and `rdx` then point at and count the
`n % 128` left. `rbx`, the one callee-saved register the batches use, is
saved in the scratch buffer and restored.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.StraightX VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceSse
open VG.Spec.TripleDes
open VG.Proof.TripleDes.X86_64.Bitsliced (blockOut wAt wAt_wAt blockAt_frame toNat_ofNat_of_le)

/-- A region disjoint from a nonempty one does not cover the whole address space. -/
theorem len_lt_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h2 : 0 < r₂.len) : r₁.len < 2 ^ 64 := by
  by_contra hc
  refine h r₂.base ?_ ?_
  · simp only [Region.Contains]; have := (r₂.base - r₁.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self]; simp; omega

/-- What the batches may assume of the state they start in: the scratch
buffer and the `n` blocks of data writable (at offset `o` of a writable
region), the schedule readable, apart from each other. -/
structure WideEnv (s : VG.X86_64.State) : Prop where
  scratch : VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s ∈ s.wr
  data : ∃ r ∈ s.wr, ∃ o : Nat, s.gpr .rsi = r.base + BitVec.ofNat 64 o ∧
    o + 8 * (s.gpr .rdx).toNat ≤ r.len ∧ r.len < 2 ^ 64
  keyIn : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * i)) 8
  dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s)
  keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s)
  keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64

theorem WideEnv.len {s : VG.X86_64.State} (E : VG.Proof.TripleDes.X86_64.BitslicedSse.WideEnv s) : 8 * (s.gpr .rdx).toNat < 2 ^ 64 :=
  VG.Proof.TripleDes.X86_64.BitslicedSse.len_lt_of_disjoint E.dataBuf (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR])

/-- The registers the batches change, but for `rsi` and `rdx`. -/
def WideRegs (r : Reg) : Prop := VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs r ∧ r ≠ .rsi ∧ r ≠ .rdx

/-- `m` blocks left, a multiple of 128 fewer than `n`, and at least 128. -/
structure WideInv (d : VG.Spec.TripleDes.Direction) (s₀ : VG.X86_64.State) (n m : Nat) (s : VG.X86_64.State) : Prop where
  ge : 128 ≤ m
  le : m ≤ n
  mod : m % 128 = n % 128
  rdx : s.gpr .rdx = BitVec.ofNat 64 m
  rsi : s.gpr .rsi = VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s₀.gpr .rsi) (n - m)
  gpr : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - m, VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s₀.gpr .rsi) b) =
    VG.Proof.TripleDes.X86_64.Bitsliced.blockOut (VG.Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) d (VG.Spec.TripleDes.blockAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s₀.gpr .rsi) b))
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, ⟨s₀.gpr .rsi, 8 * (n - m)⟩] s₀.mem s.mem

structure WideLoopPost (d : VG.Spec.TripleDes.Direction) (s₀ : VG.X86_64.State) (n : Nat) (s : VG.X86_64.State) : Prop where
  rdx : s.gpr .rdx = BitVec.ofNat 64 (n % 128)
  rsi : s.gpr .rsi = VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s₀.gpr .rsi) (n - n % 128)
  gpr : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - n % 128, VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s₀.gpr .rsi) b) =
    VG.Proof.TripleDes.X86_64.Bitsliced.blockOut (VG.Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) d (VG.Spec.TripleDes.blockAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s₀.gpr .rsi) b))
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, ⟨s₀.gpr .rsi, 8 * (n - n % 128)⟩] s₀.mem s.mem

theorem WideInv.batchPre {d : VG.Spec.TripleDes.Direction} {s₀ : VG.X86_64.State} {n m : Nat} (E : VG.Proof.TripleDes.X86_64.BitslicedSse.WideEnv s₀)
    (hn : (s₀.gpr .rdx).toNat = n) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.BitslicedSse.WideInv d s₀ n m s) : VG.Proof.TripleDes.X86_64.BitslicedSse.BatchPre s := by
  have hl := E.len
  have hfit := E.fit
  have g : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs r → s.gpr r = s₀.gpr r := h.gpr
  have hc := g .rcx (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have hdi := g .rdi (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have scr : VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s = VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s₀ := by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR, hc]
  have hge := h.ge
  have hle := h.le
  have st : Region.Sub (VG.Proof.TripleDes.X86_64.BitslicedSse.stateR s) ⟨s₀.gpr .rsi, 8 * n⟩ := by
    simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, h.rsi, VG.Proof.TripleDes.X86_64.Bitsliced.wAt]
    exact Offset.sub_base _ (by omega)
  have dataB : (⟨s₀.gpr .rsi, 8 * n⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s₀) := hn ▸ E.dataBuf
  refine ⟨⟨by rw [scr, h.wr]; exact E.scratch, ?_, ?_⟩, fun i hi => ⟨?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨r, hr, o, hb, hor, hrl⟩ := E.data
    rw [hn] at hor
    refine Ok.of_off (off := o + 8 * (n - m)) (by rw [h.wr]; exact hr) ?_ ?_ hrl
    · show s.gpr .rsi = _
      rw [h.rsi, VG.Proof.TripleDes.X86_64.Bitsliced.wAt, hb, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · show o + 8 * (n - m) + 16 * 64 ≤ r.len; omega
  · rw [scr]; exact dataB.sub_left st
  · rw [hdi, h.rd, h.wr]; exact E.keyIn i hi
  · rw [hdi, scr]; exact E.keyBuf.sub_left (Offset.sub_base _ (by omega))
  · rw [hdi]
    exact (E.keyData.sub_left (Offset.sub_base _ (by omega))).sub_right (hn ▸ st)
  · rw [hdi]; exact E.keyData.sub_right (hn ▸ st)

theorem loop_ok (d : VG.Spec.TripleDes.Direction) {s₀ : VG.X86_64.State} (E : VG.Proof.TripleDes.X86_64.BitslicedSse.WideEnv s₀) {n : Nat}
    (hn : (s₀.gpr .rdx).toNat = n) (m : Nat) (s : VG.X86_64.State) (hs : VG.Proof.TripleDes.X86_64.BitslicedSse.WideInv d s₀ n m s) :
    WP isa (.loop (batch d) .ae) s (VG.Proof.TripleDes.X86_64.BitslicedSse.WideLoopPost d s₀ n) := by
  refine WP.loop (M := isa) (VG.Proof.TripleDes.X86_64.BitslicedSse.WideInv d s₀ n) ?_ m s hs
  intro m s h
  have hl := E.len
  have hge := h.ge
  have hle := h.le
  apply WP.mono (VG.Proof.TripleDes.X86_64.BitslicedSse.batch_ok d (h.batchPre E hn))
  intro s' q
  let D := s₀.gpr .rsi
  let S := s₀.gpr .rdi
  have g : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs r → s.gpr r = s₀.gpr r := h.gpr
  have hc := g .rcx (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have hdi := g .rdi (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have spl : VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s = VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀ := by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, hc]
  have hm : (s.gpr .rdx).toNat = m := by rw [h.rdx]; exact VG.Proof.TripleDes.X86_64.Bitsliced.toNat_ofNat_of_le hle (by omega)
  -- the memory written so far
  have frame' : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, ⟨D, 8 * (n - (m - 128))⟩] s₀.mem s'.mem := by
    have f₁ : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, ⟨D, 8 * (n - (m - 128))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 8 * (n - (m - 128))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Region.sub_prefix (by omega)⟩
    have f₂ : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, ⟨D, 8 * (n - (m - 128))⟩] s.mem s'.mem := q.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s₀, List.mem_cons_self, by rw [spl]; exact fun _ h => h⟩
      · refine ⟨⟨D, 8 * (n - (m - 128))⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
        simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, h.rsi, VG.Proof.TripleDes.X86_64.Bitsliced.wAt]
        exact Offset.sub_base _ (by omega)
    exact f₁.trans f₂
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s₀) := hn ▸ E.dataBuf
  have done' : ∀ b < n - (m - 128), VG.Spec.TripleDes.blockAt s'.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) =
      VG.Proof.TripleDes.X86_64.Bitsliced.blockOut (VG.Spec.TripleDes.scheduleAt s₀.mem S) d (VG.Spec.TripleDes.blockAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b)) := by
    intro b hb
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine VG.Proof.TripleDes.X86_64.Bitsliced.blockAt_frame q.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [spl]
        exact (dataB.sub_left (Offset.sub_base _ (by omega))).sub_right (VG.Proof.TripleDes.X86_64.BitslicedSse.spill_sub s₀)
      · simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.stateR, h.rsi, VG.Proof.TripleDes.X86_64.Bitsliced.wAt]
        exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega⟩
      have e := q.out j (by omega)
      rw [h.rsi, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_wAt, hdi] at e
      rw [e]
      have hK : VG.Spec.TripleDes.scheduleAt s.mem S = VG.Spec.TripleDes.scheduleAt s₀.mem S :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame S h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact E.keyBuf.sub_right (VG.Proof.TripleDes.X86_64.BitslicedSse.spill_sub s₀)
          · exact (hn ▸ E.keyData).sub_right (Region.sub_prefix (by omega))
      have hB : VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D (n - m + j)) = VG.Spec.TripleDes.blockAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D (n - m + j)) :=
        VG.Proof.TripleDes.X86_64.Bitsliced.blockAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (dataB.sub_left (Offset.sub_base _ (by omega))).sub_right (VG.Proof.TripleDes.X86_64.BitslicedSse.spill_sub s₀)
          · exact Offset.disjoint_base D (by omega) (by omega)
      rw [hK, hB]
  have rdx' : s'.gpr .rdx = BitVec.ofNat 64 (m - 128) := by
    rw [q.rdx, h.rdx, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge]
  have rsi' : s'.gpr .rsi = VG.Proof.TripleDes.X86_64.Bitsliced.wAt D (n - (m - 128)) := by
    rw [q.rsi, h.rsi, show (1024 : BitVec 64) = BitVec.ofNat 64 (8 * 128) from rfl, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    have e : ∀ a b : Nat, a = b → D + BitVec.ofNat 64 a = D + BitVec.ofNat 64 b := fun a b h => by rw [h]
    exact e _ _ (by omega)
  have gpr' : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs r → s'.gpr r = s₀.gpr r := fun r hr =>
    (q.gpr r hr.1 hr.2.1 hr.2.2).trans (g r hr)
  have cf' : s'.cf = some (decide (m - 128 < 128)) := by
    rw [q.cf, h.rdx, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge, VG.Proof.TripleDes.X86_64.Bitsliced.toNat_ofNat_of_le (n := n) (by omega) (by omega)]
  by_cases hend : m - 128 < 128
  · left
    have e : m - 128 = n % 128 := by have := h.mod; omega
    refine ⟨by show s'.cf.map (!·) = some false; rw [cf']; simp [hend],
      by rw [rdx', e], by rw [rsi', e], gpr', q.rd.trans h.rd, q.wr.trans h.wr,
      by rw [← e]; exact done', by rw [← e]; exact frame'⟩
  · right
    refine ⟨by show s'.cf.map (!·) = some true; rw [cf']; simp [hend], m - 128, by omega,
      ⟨by omega, by omega, by have := h.mod; omega, rdx', rsi', gpr', q.rd.trans h.rd,
        q.wr.trans h.wr, done', frame'⟩⟩

/-! ## The whole phase -/

structure WidePost (d : VG.Spec.TripleDes.Direction) (s s' : VG.X86_64.State) : Prop where
  rdx : s'.gpr .rdx = BitVec.ofNat 64 ((s.gpr .rdx).toNat % 128)
  rsi : s'.gpr .rsi = VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) ((s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 128)
  gpr : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs r → s'.gpr r = s.gpr r
  rbx : s'.gpr .rbx = s.gpr .rbx
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  done : ∀ b < (s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 128, VG.Spec.TripleDes.blockAt s'.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) b) =
    VG.Proof.TripleDes.X86_64.Bitsliced.blockOut (VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d (VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) b))
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s, ⟨s.gpr .rsi, 8 * ((s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 128)⟩]
    s.mem s'.mem

theorem ea_rbxSave (s : VG.X86_64.State) : s.ea rbxSave = s.gpr .rcx + BitVec.ofNat 64 1016 := rfl

/-- Where `rbx` is saved. -/
def rbxR (s : VG.X86_64.State) : Region := ⟨s.gpr .rcx + BitVec.ofNat 64 1016, 8⟩

theorem rbx_sub (s : VG.X86_64.State) : Region.Sub (VG.Proof.TripleDes.X86_64.BitslicedSse.rbxR s) (VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s) := Offset.sub_base _ (by decide)

theorem rbx_spill (s : VG.X86_64.State) : (VG.Proof.TripleDes.X86_64.BitslicedSse.rbxR s).Disjoint (VG.Proof.TripleDes.X86_64.BitslicedSse.spillR s) :=
  Offset.disjoint_base _ (by decide) (by decide)

theorem rbxSave_in (s : VG.X86_64.State) : (VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s).Contains (s.ea rbxSave) 8 :=
  VG.Proof.TripleDes.X86_64.BitslicedSse.rbx_sub s |> fun h => Offset.contains_base _ (by decide) (by decide)

theorem wide_ok (d : VG.Spec.TripleDes.Direction) {s : VG.X86_64.State} (E : VG.Proof.TripleDes.X86_64.BitslicedSse.WideEnv s) : WP isa (wide d) s (VG.Proof.TripleDes.X86_64.BitslicedSse.WidePost d s) := by
  let n := (s.gpr .rdx).toNat
  have hl := E.len
  rw [wide]
  apply WP.seq
  let s₁ := VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState s .rdx 128
  refine WP.of_runBlock ⟨s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmp_run s .rdx 128, ?_⟩
  have cf₁ : isa.eval .b s₁ = some (decide (n < 128)) := by
    show s₁.cf = _
    simp only [s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, cf_arithFlags, show ((128 : BitVec 32).signExtend 64).toNat = 128 by decide]
    rfl
  apply WP.ite (decide (n < 128)) cf₁
  · intro hlt
    have hlt' : n < 128 := by simpa using hlt
    apply WP.block_nil
    have e : n % 128 = n := Nat.mod_eq_of_lt hlt'
    refine ⟨?_, ?_, fun r _ => by simp [s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState], by simp [s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState],
      by simp [s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, rd_arithFlags], by simp [s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, wr_arithFlags],
      fun b hb => by simp only [n] at e; omega, ?_⟩
    · simp only [s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, gpr_arithFlags]
      rw [show (s.gpr .rdx).toNat % 128 = (s.gpr .rdx).toNat from e]; simp
    · simp only [s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, gpr_arithFlags]
      rw [show (s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 128 = 0 by simp only [n] at e; omega]
      simp [VG.Proof.TripleDes.X86_64.Bitsliced.wAt]
    · simp only [s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, mem_arithFlags]; exact Frame.refl _ _
  · intro hge
    have hge' : 128 ≤ n := by simp at hge; omega
    -- save rbx
    apply WP.seq
    have hst : InRegions s₁.wr (s₁.ea rbxSave) 8 := by
      have := VG.Proof.TripleDes.X86_64.BitslicedSse.rbxSave_in s
      simp only [s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, wr_arithFlags]
      exact ⟨_, E.scratch, by simpa [s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, State.ea] using this⟩
    let s₂ : VG.X86_64.State := { s₁ with
                                mem := s₁.mem.writeW (s₁.ea rbxSave) (s₁.gpr .rbx) }
    refine WP.of_runBlock ⟨s₂, by
      rw [runBlock_cons]
      simp only [exec, State.store64, hst, ite_true, runStep_some, runBlock_nil]; rfl, ?_⟩
    have g₂ : s₂.gpr = s.gpr := by simp [s₂, s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState]
    have rd₂ : s₂.rd = s.rd := by simp [s₂, s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, rd_arithFlags]
    have wr₂ : s₂.wr = s.wr := by simp [s₂, s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, wr_arithFlags]
    have ea₂ : s₂.ea rbxSave = s.ea rbxSave := by simp [s₂, s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, State.ea]
    have f₂ : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.rbxR s] s.mem s₂.mem := by
      simp only [s₂, s₁, VG.Proof.TripleDes.X86_64.BitslicedSse.cmpState, mem_arithFlags]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (by simp only [State.ea, gpr_arithFlags]; exact Region.contains_self _ _)
    have E₂ : VG.Proof.TripleDes.X86_64.BitslicedSse.WideEnv s₂ := by
      have sc : VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s₂ = VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s := by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR, g₂]
      refine ⟨by rw [sc, wr₂]; exact E.scratch, by rw [g₂, wr₂]; exact E.data,
        by rw [g₂, rd₂, wr₂]; exact E.keyIn, by rw [g₂, sc]; exact E.dataBuf,
        by rw [g₂, sc]; exact E.keyBuf, by rw [g₂]; exact E.keyData, by rw [g₂]; exact E.fit⟩
    apply WP.seq
    have hn₂ : (s₂.gpr .rdx).toNat = n := by rw [g₂]
    have I : VG.Proof.TripleDes.X86_64.BitslicedSse.WideInv d s₂ n n s₂ := ⟨hge', Nat.le_refl _, rfl, by rw [g₂]; simp [n], by simp [VG.Proof.TripleDes.X86_64.Bitsliced.wAt],
      fun _ _ => rfl, rfl, rfl, fun b hb => by omega, by rw [Nat.sub_self]; exact Frame.refl _ _⟩
    apply WP.mono (VG.Proof.TripleDes.X86_64.BitslicedSse.loop_ok d E₂ hn₂ n s₂ I)
    intro s₃ p₃
    -- restore rbx
    have c₃ : s₃.gpr .rcx = s.gpr .rcx := (p₃.gpr .rcx (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])).trans (by rw [g₂])
    have ea₃ : s₃.ea rbxSave = s.ea rbxSave := by simp [State.ea, rbxSave, c₃]
    have hld : InRegions (s₃.rd ++ s₃.wr) (s₃.ea rbxSave) 8 := by
      rw [ea₃, p₃.wr, wr₂]
      exact ⟨_, List.mem_append_right _ E.scratch, VG.Proof.TripleDes.X86_64.BitslicedSse.rbxSave_in s⟩
    have saved : s₃.mem.readW (s.ea rbxSave) 64 = s.gpr .rbx := by
      have e₁ : s₃.mem.readW (s.ea rbxSave) 64 = s₂.mem.readW (s.ea rbxSave) 64 := by
        refine p₃.frame.readW (r := VG.Proof.TripleDes.X86_64.BitslicedSse.rbxR s) (Region.contains_self _ _) ?_ (by decide)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, g₂]; exact VG.Proof.TripleDes.X86_64.BitslicedSse.rbx_spill s
        · rw [g₂]
          exact (E.dataBuf.sub_left (Region.sub_prefix (by omega))).symm.sub_left (VG.Proof.TripleDes.X86_64.BitslicedSse.rbx_sub s)
      rw [e₁]
      simp only [s₂, ea₂.symm]
      exact Mem.readW_writeW_self _ _ 8 _ (by decide)
    let s₄ := s₃.setReg .rbx (s₃.mem.readW (s₃.ea rbxSave) 64)
    let s₅ := s₄
    refine WP.of_runBlock ⟨s₅, by
      rw [runBlock_cons]
      simp only [exec, readSrc, State.load64, hld, ite_true, Option.map_some, runStep_some,
        runBlock_nil]
      rfl, ?_⟩
    have g₅ : ∀ r, r ≠ .rbx → s₅.gpr r = s₃.gpr r := by
      intro r hr; simp [s₅, s₄, gpr_setReg, hr]
    refine ⟨by rw [g₅ _ (by decide), p₃.rdx], by rw [g₅ _ (by decide), p₃.rsi, g₂],
      fun r hr => by rw [g₅ r (by simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs] at hr; exact hr.1.2.1), p₃.gpr r hr, g₂],
      by simp [s₅, s₄, gpr_setReg, ea₃, saved],
      by simp [s₅, s₄, rd_setReg, p₃.rd, rd₂], by simp [s₅, s₄, wr_setReg, p₃.wr, wr₂],
      fun b hb => ?_, ?_⟩
    · have e := p₃.done b hb
      have hm : s₅.mem = s₃.mem := by simp [s₅, s₄, mem_setReg]
      rw [hm]
      simp only [g₂] at e
      rw [e]
      have hK : VG.Spec.TripleDes.scheduleAt s₂.mem (s.gpr .rdi) = VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi) :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame _ f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact E.keyBuf.sub_right (VG.Proof.TripleDes.X86_64.BitslicedSse.rbx_sub s)
      have hB : VG.Spec.TripleDes.blockAt s₂.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) b) = VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) b) :=
        VG.Proof.TripleDes.X86_64.Bitsliced.blockAt_frame f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (E.dataBuf.sub_left (Offset.sub_base _ (by omega))).sub_right (VG.Proof.TripleDes.X86_64.BitslicedSse.rbx_sub s)
      rw [hK, hB]
    · have hm : s₅.mem = s₃.mem := by simp [s₅, s₄, mem_setReg]
      rw [hm]
      have a : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s, ⟨s.gpr .rsi, 8 * (n - n % 128)⟩] s.mem s₂.mem :=
        f₂.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s, List.mem_cons_self, VG.Proof.TripleDes.X86_64.BitslicedSse.rbx_sub s⟩
      have b : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s, ⟨s.gpr .rsi, 8 * (n - n % 128)⟩] s₂.mem s₃.mem :=
        p₃.frame.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s, List.mem_cons_self, by
              simp only [VG.Proof.TripleDes.X86_64.BitslicedSse.spillR, g₂]; exact VG.Proof.TripleDes.X86_64.BitslicedSse.spill_sub s⟩
          · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [g₂]; exact fun _ h => h⟩
      exact a.trans b

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Ecb`. -/
section

/-!
# The SSE2 function

The batches of 128 blocks (`wide_ok`), then the 64-block code on the blocks
left (`Bitsliced.ecb_ok`): every block becomes its encryption or decryption
(`ecb_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceSse VG.Spec.TripleDes
open VG.Proof.TripleDes.X86_64.Bitsliced (blockOut wAt wAt_wAt blockAt_frame EcbPre EcbPost ecb_blocks)

/-- The function on blocks in a writable region apart from the scratch
buffer and the schedule: every block becomes its encryption or decryption
(`EcbPost`), as the 64-block code's `ecb_ok` says of it. -/
theorem ecb_post (d : VG.Spec.TripleDes.Direction) {s : VG.X86_64.State} (E : VG.Proof.TripleDes.X86_64.BitslicedSse.WideEnv s)
    (retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩) :
    WP isa (ecb d) s (EcbPost d s) := by
  let n := (s.gpr .rdx).toNat
  let D := s.gpr .rsi
  let S := s.gpr .rdi
  let k := n - n % 128
  have hl := E.len
  have fit := E.fit
  have dataBuf := E.dataBuf
  have keyBuf := E.keyBuf
  have keyData := E.keyData
  obtain ⟨⟨rb, rl⟩, hr, o, hb, hor, hrl⟩ := E.data
  rw [Impl.TripleDes.X86_64.BitsliceSse.ecb]
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.BitslicedSse.wide_ok d E)
  intro s₁ w
  have g : ∀ r, VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs r → s₁.gpr r = s.gpr r := w.gpr
  have hc := g .rcx (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have hdi := g .rdi (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have hsp := g .rsp (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  have hm : (s₁.gpr .rdx).toNat = n % 128 := by
    rw [w.rdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hD₁ : s₁.gpr .rsi = VG.Proof.TripleDes.X86_64.Bitsliced.wAt D k := w.rsi
  have sub₁ : Region.Sub ⟨s₁.gpr .rsi, 8 * (s₁.gpr .rdx).toNat⟩ ⟨D, 8 * n⟩ := by
    rw [hD₁, hm]; exact Offset.sub_base _ (by omega)
  have pre₁ : EcbPre s₁ := by
    refine ⟨by rw [hc, w.wr]; exact E.scratch, fun i hi => ?_,
      fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [w.wr, hD₁, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_wAt]
      rw [hm] at hi
      refine ⟨_, hr, ?_⟩
      have e : VG.Proof.TripleDes.X86_64.Bitsliced.wAt D (k + i) = rb + BitVec.ofNat 64 (o + 8 * (k + i)) := by
        simp only [VG.Proof.TripleDes.X86_64.Bitsliced.wAt, D, hb, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rw [e]
      exact Offset.contains_base _ (by simp only at hor; omega) (by simp only at hrl hor; omega)
    · rw [hdi, w.rd, w.wr]; exact E.keyIn i hi
    · rw [hdi]; exact keyData.sub_right sub₁
    · rw [hdi, hc]; exact keyBuf
    · rw [hc]; exact dataBuf.sub_left sub₁
    · rw [hsp]; exact retData.sub_right sub₁
    · rw [hsp, hc]; exact retBuf
    · rw [hD₁, hm]
      have hfit : D.toNat + 8 * n ≤ 2 ^ 64 := fit
      have hk : k + n % 128 = n := by omega
      simp only [VG.Proof.TripleDes.X86_64.Bitsliced.wAt, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega)]
      by_cases hw : D.toNat + 8 * k < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hw]; omega
      · rw [show D.toNat + 8 * k = 2 ^ 64 by omega, Nat.mod_self]; omega
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.ecb_ok d pre₁)
  intro s' t
  have scr₁ : VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₁ = VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s := by
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR, hc]
  have tf := t.frame
  rw [scr₁] at tf
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s) := dataBuf
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun b hb => ?_, ?_⟩
  · rw [t.gpr.1 r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w.rbx
    all_goals exact g _ (by simp [VG.Proof.TripleDes.X86_64.BitslicedSse.WideRegs, VG.Proof.TripleDes.X86_64.BitslicedSse.PassRegs])
  · rw [← hsp, t.gpr.2, hsp]
    refine w.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact retBuf
    · exact retData.sub_right (Region.sub_prefix (by omega))
  · by_cases hbk : b < k
    · rw [← w.done b hbk]
      refine VG.Proof.TripleDes.X86_64.Bitsliced.blockAt_frame tf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dataB.sub_left (Offset.sub_base _ (by omega))
      · rw [hD₁, hm]
        exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, b = k + j := ⟨b - k, by omega⟩
      have e := t.done j (by rw [hm]; omega)
      rw [hD₁, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_wAt, hdi] at e
      rw [e]
      have hK : VG.Spec.TripleDes.scheduleAt s₁.mem S = VG.Spec.TripleDes.scheduleAt s.mem S :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame S w.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact keyBuf
          · exact keyData.sub_right (Region.sub_prefix (by omega))
      have hB : VG.Spec.TripleDes.blockAt s₁.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D (k + j)) = VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D (k + j)) :=
        VG.Proof.TripleDes.X86_64.Bitsliced.blockAt_frame w.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dataB.sub_left (Offset.sub_base _ (by omega))
          · exact Offset.disjoint_base D (by omega) (by omega)
      rw [hK, hB]
  · have a : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s, ⟨D, 8 * n⟩] s.mem s₁.mem := w.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 8 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
    have b : VG.Frame [VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s, ⟨D, 8 * n⟩] s₁.mem s'.mem := tf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.TripleDes.X86_64.BitslicedSse.scratchR s, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 8 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, sub₁⟩
    exact a.trans b

/-- `WideEnv` from the regions of the contract. -/
theorem WideEnv.of_regions {s : VG.X86_64.State} (hrd : s.rd = [⟨s.gpr .rdi, 384⟩])
    (hwr : s.wr = [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 1024⟩])
    (keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64) : VG.Proof.TripleDes.X86_64.BitslicedSse.WideEnv s := by
  have hl := VG.Proof.TripleDes.X86_64.BitslicedSse.len_lt_of_disjoint dataBuf (by simp)
  refine ⟨by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
    ⟨_, by rw [hwr]; exact List.mem_cons_self, 0, by simp, by simp, hl⟩, fun i hi => ?_,
    dataBuf, keyBuf, keyData, fit⟩
  rw [hrd]
  exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩

theorem ecb_ok (d : VG.Spec.TripleDes.Direction) {s : VG.X86_64.State} (hrd : s.rd = [⟨s.gpr .rdi, 384⟩])
    (hwr : s.wr = [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 1024⟩])
    (keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64) :
    WP isa (ecb d) s (fun s' => gprPreserved s s' ∧
      VG.Spec.TripleDes.blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
        Spec.TripleDes.ecb (VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d
          (VG.Spec.TripleDes.blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)) :=
  WP.mono (VG.Proof.TripleDes.X86_64.BitslicedSse.ecb_post d (WideEnv.of_regions hrd hwr keyData keyBuf dataBuf fit) retData retBuf)
    fun _ p => ⟨p.gpr, VG.Proof.TripleDes.X86_64.Bitsliced.ecb_blocks _ _ _ _ _ _ p.done⟩

end VG.Proof.TripleDes.X86_64.BitslicedSse

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Verified`. -/
section

/-! # The SSE2 bitsliced ECB functions meet their contracts -/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64
open VG.Proof.TripleDes.X86_64.Bitsliced (contract ecbTaint_agree satState publicRegs_five)

theorem encrypt_correct (s : VG.X86_64.State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.BitsliceSse.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.ecb_ok .encrypt rd wr kd kb db rdt rb fit
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.TripleDes.X86_64.BitsliceSse.encrypt) (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : VG.X86_64.State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.BitsliceSse.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.TripleDes.X86_64.BitslicedSse.ecb_ok .decrypt rd wr kd kb db rdt rb fit
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.TripleDes.X86_64.BitsliceSse.decrypt) (by lit_decide) he ha, hp⟩

theorem encrypt_verified : Verified target Impl.TripleDes.X86_64.BitsliceSse.encrypt
    (Proof.TripleDes.ecbEncryptScratchContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.X86_64.BitslicedSse.encrypt_correct
    (VG.Proof.TripleDes.X86_64.BitslicedSse.encrypt_constantTime _ _ (ecbTaint_agree .encrypt)) ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract, publicRegs_five] [satState] using VG.Proof.TripleDes.X86_64.Bitsliced.satState

theorem decrypt_verified : Verified target Impl.TripleDes.X86_64.BitsliceSse.decrypt
    (Proof.TripleDes.ecbDecryptScratchContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.X86_64.BitslicedSse.decrypt_correct
    (VG.Proof.TripleDes.X86_64.BitslicedSse.decrypt_constantTime _ _ (ecbTaint_agree .decrypt)) ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract, publicRegs_five] [satState] using VG.Proof.TripleDes.X86_64.Bitsliced.satState

end VG.Proof.TripleDes.X86_64.BitslicedSse

end
