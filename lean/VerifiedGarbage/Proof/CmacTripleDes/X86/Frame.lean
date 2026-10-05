import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.CmacTripleDes.X86.Round
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.X86.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Rows
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Impl.CmacTripleDes.X86
import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit`. -/
section

/-!
# The DES block's x86 code as literals, for kernel-evaluated checks

The S-boxes' leaves, the round's parts, `IP`, `IP⁻¹` and the block are each
evaluated once, here:
the checks of each part (`Round.lean`, `Block.lean`) and the literals of the
functions that run the block (`Lit.lean`) read these literals rather than
evaluate the S-box leaves and bit permutations again.
-/

namespace VG

materialize_table Impl.CmacTripleDes.X86.leaf 2 64
materialize_value Impl.CmacTripleDes.X86.inputs
materialize_table Impl.CmacTripleDes.X86.tree 2
materialize_value Impl.CmacTripleDes.X86.output
materialize_value Impl.CmacTripleDes.X86.ipCode
materialize_value Impl.CmacTripleDes.X86.fpCode
materialize_code Impl.CmacTripleDes.X86.block

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Round`. -/
section

/-!
# A DES round on x86 (32-bit)

Untrusted: everything here is checked by Lean.

As on 32-bit ARM (`Proof/CmacTripleDes/Arm/Round.lean`): the round's parts
are checked by evaluation (`Straight.check`), the broadcast inputs
(`inputs`) and the output (`output`) over the lane domain (`linear_ok`, all
their words in slots), and each half's S-boxes (`tree`) over the row domain
(`Bitslice.rows`), on all 64 values of a box's input at once. `round_ok`
composes them: slot `L` becomes `R`, and slot `R` becomes `L ⊕ f(R, K)`,
with `K` the round key's low word and the low 16 bits of its high word.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86

/-- The round's memory: slots 0–17 at `ebp`, and the round key's two words
at `esi`. -/
def rCfg : Cfg := { base := .ebp, slots := 18, ext := .esi, exts := 2 }

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : VG.X86.State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .ebp) k) 32

/-- The round key's words. -/
abbrev keyLo (s : VG.X86.State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esi) 0) 32
abbrev keyHi (s : VG.X86.State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esi) 1) 32

/-- The round key: the low 16 bits of its high word, and its low word. -/
abbrev key48 (s : VG.X86.State) : BitVec 48 := (VG.Proof.CmacTripleDes.X86.keyHi s).setWidth 16 ++ VG.Proof.CmacTripleDes.X86.keyLo s

/-! ## The inputs -/

/-- Bit `b` of the round key, as an atom: of its low word (input word 1) or
its high word (input word 2). -/
def keyAtom (b : Nat) : Nat := if b < 32 then 32 + b else 64 + (b - 32)

/-- Bit `p` of input slot `t` (half `t / 6`, input bit `t % 6`): in lane `p / 6`,
below its fifth bit, `R`'s bit (atom `0 … 31`) XOR the key's. -/
def inG (t p : Nat) : List Nat :=
  if p < 24 ∧ p % 6 < 4 then
    [expSrc (24 * (t / 6) + 6 * (p / 6) + t % 6), VG.Proof.CmacTripleDes.X86.keyAtom (24 * (t / 6) + 6 * (p / 6) + t % 6)]
  else []

/-- The slot of input `t`. -/
def inSlot (t : Nat) : Nat := 7 * (t / 6) + t % 6

/-- The inputs' slots, and `L` and `R` (input words 3 and 0) kept. -/
def inOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 12).map (fun t => (VG.Proof.CmacTripleDes.X86.inSlot t, VG.Proof.CmacTripleDes.X86.inG t)) ++ [(slotL, fun p => [96 + p]), (slotR, fun p => [p])]

theorem inputs_check :
    VG.X86.Straight.check (lanes 32 7) VG.Proof.CmacTripleDes.X86.rCfg (linExt 1) inputs (linEnv [(slotR, 0), (slotL, 3)]) (linPost rCfg.slots 7 VG.Proof.CmacTripleDes.X86.inOuts) =
      true := by
  lit_decide

/-! ## The S-boxes -/

/-- Slot `t` on row `c`, at every position: bit `t % 7` of `c`. -/
def rowIn (t : Nat) : Nat := tableOf (fun a => (a / 32).testBit (t % 7)) 2048

/-- Half `h`'s input slots. -/
def sbEnv (h : Nat) : Env Nat :=
  { reg := fun _ => none, slot := fun t => if 7 * h ≤ t ∧ t < 7 * h + 6 then some (VG.Proof.CmacTripleDes.X86.rowIn t) else none }

/-- At bit `6 j + off i b` (`i` the box in lane `j` of half `h`), output bit
`b` of box `i`, on every row. -/
def sbPost (h : Nat) (e : Env Nat) : Bool :=
  match e.reg .ebx with
  | some F => (List.range 4).all fun j => (List.range 4).all fun b => (List.range 64).all fun c =>
      F.testBit (32 * c + (6 * j + off (boxOf h j) b)) ==
        (Proof.TripleDes.outputTable (boxOf h j) b).testBit c
  | none => false

/-- The slots half `h` uses: the broadcast inputs up to its own, and its
spare slot. -/
def sCfg (h : Nat) : Cfg := { base := .ebp, slots := 7 * h + 7, ext := .esi, exts := 0 }

theorem sbox0_check : VG.X86.Straight.check (rows 32 6) (VG.Proof.CmacTripleDes.X86.sCfg 0) (fun _ => none) (tree 0) (VG.Proof.CmacTripleDes.X86.sbEnv 0) (VG.Proof.CmacTripleDes.X86.sbPost 0) = true := by
  lit_decide

theorem sbox1_check : VG.X86.Straight.check (rows 32 6) (VG.Proof.CmacTripleDes.X86.sCfg 1) (fun _ => none) (tree 1) (VG.Proof.CmacTripleDes.X86.sbEnv 1) (VG.Proof.CmacTripleDes.X86.sbPost 1) = true := by
  lit_decide

/-! ## The output -/

/-- The atom of output bit `u` of the S-boxes: bit `outPos u` of half 0's
outputs (slot 14, input word 0) or of half 1's (slot 15, input word 1). -/
def sAtom (u : Nat) : Nat := if outHalf u = 0 then outPos u else 32 + outPos u

/-- Slot `R`: bit `j` of `L` (input word 2) XOR the S-boxes' bit `pSrc j`. -/
def oGR (p : Nat) : List Nat := if p < 32 then [VG.Proof.CmacTripleDes.X86.sAtom (pSrc p), 64 + p] else [64 + p]

/-- Slot `L` gets `R` (input word 3), slot `R` `L ⊕ P(S)`. -/
def oOuts : List (Nat × (Nat → List Nat)) := [(slotL, fun p => [96 + p]), (slotR, VG.Proof.CmacTripleDes.X86.oGR)]

/-- The output's slots. -/
def oCfg : Cfg := { base := .ebp, slots := 18, ext := .esi, exts := 0 }

theorem output_check :
    VG.X86.Straight.check (lanes 32 7) VG.Proof.CmacTripleDes.X86.oCfg (linExt 0) output (linEnv [(14, 0), (15, 1), (slotL, 2), (slotR, 3)])
      (linPost oCfg.slots 7 VG.Proof.CmacTripleDes.X86.oOuts) = true := by
  lit_decide

/-! ## Machine facts -/

theorem runBlock_append (a b : List Instr) (s : VG.X86.State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

theorem wordAddr_eq (b : BitVec 32) {k : Nat} (h : b.toNat + 4 * k < 2 ^ 32) :
    wordAddr b k = b.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq h

/-- Word `k` of the slots is outside a frame on the first `n` words. -/
theorem slot_frame {m m' : Mem} {b : BitVec 32} {n k : Nat} (hf : Frame [⟨b.setWidth 64, 4 * n⟩] m m')
    (hk : n ≤ k) (hb : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [VG.Proof.CmacTripleDes.X86.wordAddr_eq b (by omega)]
  refine hf.readW (r := ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base _ (by omega) (by omega)

/-- Words `j` and `k` of the slots are apart. -/
theorem slot_word_sep (b : BitVec 32) {j k : Nat} (h : j ≠ k) (hj : b.toNat + 4 * j + 4 ≤ 2 ^ 32)
    (hk : b.toNat + 4 * k + 4 ≤ 2 ^ 32) : Mem.Sep (wordAddr b j) (32 / 8) (wordAddr b k) (32 / 8) := by
  rw [VG.Proof.CmacTripleDes.X86.wordAddr_eq b (by omega), VG.Proof.CmacTripleDes.X86.wordAddr_eq b (by omega)]
  exact Offset.sep _ (by omega) (by omega) (by omega)

/-- `mov [b + o], r`, run. -/
theorem runBlock_store {s : VG.X86.State} {b r : Reg} {o : Nat} (hout : InRegions s.wr (addr (s.gpr b) o) 4) :
    runBlock isa [.store ⟨b, o⟩ r] s = some { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.gpr r) } := by
  rw [runBlock_cons, show exec (.store ⟨b, o⟩ r) s = some { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.gpr r) }
    by simp [exec, State.store32, ea_mk, hout], runStep_some, runBlock_nil]

/-! ## The inputs, on the machine -/

/-- The inputs of `inputs`: `R`, the round key's words and `L`. -/
def inW (s : VG.X86.State) (i : Nat) : BitVec 32 :=
  if i = 0 then VG.Proof.CmacTripleDes.X86.slotW s slotR else if i = 1 then VG.Proof.CmacTripleDes.X86.keyLo s else if i = 2 then VG.Proof.CmacTripleDes.X86.keyHi s else VG.Proof.CmacTripleDes.X86.slotW s slotL

/-- The registers the round keeps. -/
def kept : List Reg := [.esp, .esi, .ebp]

theorem inputs_kept : kept.all (fun r => inputs.all fun i => i.dst != some r) = true := by lit_decide

theorem slot_bits {x y : BitVec 32} (h : ∀ p < 32, x.getLsbD p = y.getLsbD p) : x = y :=
  BitVec.eq_of_getLsbD_eq fun p hp => h p hp

theorem inputs_ok {s : VG.X86.State} (hok : Ok VG.Proof.CmacTripleDes.X86.rCfg s) :
    ∃ s', runBlock isa inputs s = some s' ∧
      (∀ t < 12, ∀ p < 32, (VG.Proof.CmacTripleDes.X86.slotW s' (VG.Proof.CmacTripleDes.X86.inSlot t)).getLsbD p = xorBits (VG.Proof.CmacTripleDes.X86.inW s) (VG.Proof.CmacTripleDes.X86.inG t p)) ∧
      VG.Proof.CmacTripleDes.X86.slotW s' slotL = VG.Proof.CmacTripleDes.X86.slotW s slotL ∧ VG.Proof.CmacTripleDes.X86.slotW s' slotR = VG.Proof.CmacTripleDes.X86.slotW s slotR ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.X86.rCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rd, wr, keep, fr⟩ := linear_ok VG.Proof.CmacTripleDes.X86.inputs_check hok (VG.Proof.CmacTripleDes.X86.inW s)
    (fun j i h hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨by decide, rfl⟩
      · exact ⟨by decide, rfl⟩)
    (fun j hj => by
      simp only [VG.Proof.CmacTripleDes.X86.rCfg] at hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact ⟨by decide, rfl⟩
      · exact ⟨by decide, rfl⟩)
  have kp : ∀ r ∈ VG.Proof.CmacTripleDes.X86.kept, s'.gpr r = s.gpr r := fun r hr => keep _ (List.all_eq_true.mp VG.Proof.CmacTripleDes.X86.inputs_kept r hr)
  have e10 : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [VG.Proof.CmacTripleDes.X86.kept])
  have bit : ∀ j g, (j, g) ∈ VG.Proof.CmacTripleDes.X86.inOuts → ∀ p < 32, (VG.Proof.CmacTripleDes.X86.slotW s' j).getLsbD p = xorBits (VG.Proof.CmacTripleDes.X86.inW s) (g p) := fun j g h p hp => by
    rw [VG.Proof.CmacTripleDes.X86.slotW, e10]; exact hout j g h p hp
  refine ⟨s', hs', fun t ht p hp => bit _ _ (List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
    p hp, VG.Proof.CmacTripleDes.X86.slot_bits fun p hp => ?_, VG.Proof.CmacTripleDes.X86.slot_bits fun p hp => ?_, rd, wr, kp, fr⟩
  · rw [bit slotL _ (List.mem_append_right _ (List.mem_cons_self ..)) p hp]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, VG.Proof.CmacTripleDes.X86.inW, show (96 + p) / 32 = 3 by omega,
      show (96 + p) % 32 = p by omega]
    rfl
  · rw [bit slotR _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) p hp]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, VG.Proof.CmacTripleDes.X86.inW, Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
    rfl

/-! ## The S-boxes, on the machine -/

theorem tree_kept (h : Nat) (hh : h < 2) : kept.all (fun r => (tree h).all fun i => i.dst != some r) = true := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> lit_decide

/-- The input of the box whose lane of half `h` holds bit `p`, from bit `p`
of the slots. -/
def boxIn (h : Nat) (s : VG.X86.State) (p : Nat) : BitVec 6 := ofBits 6 fun t => (VG.Proof.CmacTripleDes.X86.slotW s (7 * h + t)).getLsbD p

theorem off_lt4 : ∀ h < 2, ∀ j < 4, ∀ b < 4, off (boxOf h j) b < 4 := by decide

theorem sbox_ok {h : Nat} (hh : h < 2) {s : VG.X86.State} (hok : Ok (VG.Proof.CmacTripleDes.X86.sCfg h) s) :
    ∃ s', runBlock isa (tree h) s = some s' ∧
      (∀ j < 4, ∀ b < 4, (s'.gpr .ebx).getLsbD (6 * j + off (boxOf h j) b) =
        (Spec.TripleDes.sBox (boxOf h j) (VG.Proof.CmacTripleDes.X86.boxIn h s (6 * j + off (boxOf h j) b))).getLsbD b) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion (VG.Proof.CmacTripleDes.X86.sCfg h) s] s.mem s'.mem := by
  have hchk : VG.X86.Straight.check (rows 32 6) (VG.Proof.CmacTripleDes.X86.sCfg h) (fun _ => none) (tree h) (VG.Proof.CmacTripleDes.X86.sbEnv h) (VG.Proof.CmacTripleDes.X86.sbPost h) = true := by
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
    · exact VG.Proof.CmacTripleDes.X86.sbox0_check
    · exact VG.Proof.CmacTripleDes.X86.sbox1_check
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain ⟨F, hF, hout⟩ : ∃ F, e'.reg .ebx = some F ∧ ∀ j < 4, ∀ b < 4, ∀ c < 64,
      F.testBit (32 * c + (6 * j + off (boxOf h j) b)) =
        (Spec.TripleDes.sBox (boxOf h j) (BitVec.ofNat 6 c)).getLsbD b := by
    simp only [VG.Proof.CmacTripleDes.X86.sbPost] at hpost
    split at hpost
    · rename_i F hF
      refine ⟨F, hF, fun j hj b hb c hc => ?_⟩
      have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hpost j
        (List.mem_range.mpr hj)) b (List.mem_range.mpr hb)) c (List.mem_range.mpr hc)
      rw [← Proof.TripleDes.testBit_outputTable hc]
      simpa using this
    · cases hpost
  have key : ∀ p < 32, ∃ s', runBlock isa (tree h) s = some s' ∧
      Post (RowRel p (VG.Proof.CmacTripleDes.X86.boxIn h s p).toNat) (VG.Proof.CmacTripleDes.X86.sCfg h) (fun _ => none) e' s s'
        (fun r => ((tree h).all fun i => i.dst != some r) = false) := by
    intro p hp
    refine run (rows_sound hp (VG.Proof.CmacTripleDes.X86.boxIn h s p).isLt) hok
      ⟨fun r a h => by simp [VG.Proof.CmacTripleDes.X86.sbEnv] at h, fun t a ht h' => ?_, fun _ _ _ h => by cases h⟩ he
    simp only [VG.Proof.CmacTripleDes.X86.sbEnv] at h'
    split at h'
    · rename_i ht6
      cases h'
      show (VG.Proof.CmacTripleDes.X86.rowIn t).testBit (32 * (VG.Proof.CmacTripleDes.X86.boxIn h s p).toNat + p) = (VG.Proof.CmacTripleDes.X86.slotW s t).getLsbD p
      have hc := (VG.Proof.CmacTripleDes.X86.boxIn h s p).isLt
      obtain ⟨u, rfl, hu⟩ : ∃ u, t = 7 * h + u ∧ u < 6 := ⟨t - 7 * h, by omega, by omega⟩
      rw [VG.Proof.CmacTripleDes.X86.rowIn, testBit_tableOf, decide_eq_true (by omega : 32 * (boxIn h s p).toNat + p < 2048),
        Bool.true_and, show (32 * (VG.Proof.CmacTripleDes.X86.boxIn h s p).toNat + p) / 32 = (VG.Proof.CmacTripleDes.X86.boxIn h s p).toNat by omega,
        BitVec.testBit_toNat, VG.Proof.CmacTripleDes.X86.boxIn, getLsbD_ofBits, show (7 * h + u) % 7 = u by omega,
        decide_eq_true hu, Bool.true_and]
    · cases h'
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj b hb => ?_, p₀.rd, p₀.wr,
    fun r hr => p₀.other r (by simp [List.all_eq_true.mp (VG.Proof.CmacTripleDes.X86.tree_kept h hh) r hr]), p₀.frame⟩
  have hp : 6 * j + off (boxOf h j) b < 32 := by have := VG.Proof.CmacTripleDes.X86.off_lt4 h hh j hj b hb; omega
  obtain ⟨s'', hs'', p₁⟩ := key _ hp
  obtain rfl := run_unique hs'' hs'
  have h' := p₁.rel.reg .ebx F hF
  simp only [RowRel] at h'
  rw [← h', hout j hj b hb _ (VG.Proof.CmacTripleDes.X86.boxIn h s _).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## The output, on the machine -/

/-- The inputs of `output`: the halves' outputs, `L` and `R`. -/
def oW (s : VG.X86.State) (i : Nat) : BitVec 32 :=
  if i = 0 then VG.Proof.CmacTripleDes.X86.slotW s 14 else if i = 1 then VG.Proof.CmacTripleDes.X86.slotW s 15 else if i = 2 then VG.Proof.CmacTripleDes.X86.slotW s slotL else VG.Proof.CmacTripleDes.X86.slotW s slotR

theorem output_kept : kept.all (fun r => output.all fun i => i.dst != some r) = true := by lit_decide

theorem output_ok {s : VG.X86.State} (hok : Ok VG.Proof.CmacTripleDes.X86.oCfg s) :
    ∃ s', runBlock isa output s = some s' ∧
      VG.Proof.CmacTripleDes.X86.slotW s' slotL = VG.Proof.CmacTripleDes.X86.slotW s slotR ∧
      (∀ p < 32, (VG.Proof.CmacTripleDes.X86.slotW s' slotR).getLsbD p = xorBits (VG.Proof.CmacTripleDes.X86.oW s) (VG.Proof.CmacTripleDes.X86.oGR p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.X86.oCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rd, wr, keep, fr⟩ := linear_ok VG.Proof.CmacTripleDes.X86.output_check hok (VG.Proof.CmacTripleDes.X86.oW s)
    (fun j i h hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.X86.oCfg]))
  have kp : ∀ r ∈ VG.Proof.CmacTripleDes.X86.kept, s'.gpr r = s.gpr r := fun r hr => keep _ (List.all_eq_true.mp VG.Proof.CmacTripleDes.X86.output_kept r hr)
  have e10 : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [VG.Proof.CmacTripleDes.X86.kept])
  have bit : ∀ j g, (j, g) ∈ VG.Proof.CmacTripleDes.X86.oOuts → ∀ p < 32, (VG.Proof.CmacTripleDes.X86.slotW s' j).getLsbD p = xorBits (VG.Proof.CmacTripleDes.X86.oW s) (g p) := fun j g h p hp => by
    rw [VG.Proof.CmacTripleDes.X86.slotW, e10]; exact hout j g h p hp
  refine ⟨s', hs', VG.Proof.CmacTripleDes.X86.slot_bits fun p hp => ?_, fun p hp => bit _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) p hp,
    rd, wr, kp, fr⟩
  rw [bit slotL _ (List.mem_cons_self ..) p hp]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, VG.Proof.CmacTripleDes.X86.oW, show (96 + p) / 32 = 3 by omega,
    show (96 + p) % 32 = p by omega]
  rfl

/-! ## The round -/

theorem expSrc_lt : ∀ q < 48, expSrc q < 32 := by lit_decide

theorem pSrc_lt : ∀ j < 32, pSrc j < 32 := by lit_decide

/-- The box inputs that `inputs` broadcasts. -/
theorem boxIn_eq {s s₁ : VG.X86.State}
    (hx : ∀ t < 12, ∀ p < 32, (VG.Proof.CmacTripleDes.X86.slotW s₁ (VG.Proof.CmacTripleDes.X86.inSlot t)).getLsbD p = xorBits (VG.Proof.CmacTripleDes.X86.inW s) (VG.Proof.CmacTripleDes.X86.inG t p))
    {h j o : Nat} (hh : h < 2) (hj : j < 4) (ho : o < 4) :
    VG.Proof.CmacTripleDes.X86.boxIn h s₁ (6 * j + o) = chunk (VG.Proof.CmacTripleDes.X86.slotW s slotR) (VG.Proof.CmacTripleDes.X86.key48 s) (boxOf h j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hb : 6 * (7 - boxOf h j) = 24 * h + 6 * j := by simp only [boxOf]; omega
  have hE := VG.Proof.CmacTripleDes.X86.expSrc_lt (24 * h + 6 * j + t) (by omega)
  have hs : 7 * h + t = VG.Proof.CmacTripleDes.X86.inSlot (6 * h + t) := by simp only [VG.Proof.CmacTripleDes.X86.inSlot]; omega
  rw [VG.Proof.CmacTripleDes.X86.boxIn, getLsbD_ofBits, decide_eq_true ht, Bool.true_and, hs, hx (6 * h + t) (by omega) _ (by omega),
    getLsbD_chunk _ _ (by simp only [boxOf]; omega) ht, VG.Proof.CmacTripleDes.X86.inG, ite_eq_left (by omega), hb,
    show (6 * h + t) / 6 = h by omega, show (6 * h + t) % 6 = t by omega, show (6 * j + o) / 6 = j by omega]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, VG.Proof.CmacTripleDes.X86.inW, VG.Proof.CmacTripleDes.X86.keyAtom]
  rw [Nat.div_eq_of_lt (show expSrc (24 * h + 6 * j + t) < 32 by omega),
    Nat.mod_eq_of_lt (show expSrc (24 * h + 6 * j + t) < 32 by omega), ite_eq_left rfl]
  congr 1
  rw [BitVec.getLsbD_append]
  by_cases h32 : 24 * h + 6 * j + t < 32
  · rw [ite_eq_left h32, ite_eq_left h32, show (32 + (24 * h + 6 * j + t)) / 32 = 1 by omega,
      show (32 + (24 * h + 6 * j + t)) % 32 = 24 * h + 6 * j + t by omega]
    rfl
  · rw [ite_eq_right h32, ite_eq_right h32, show (64 + (24 * h + 6 * j + t - 32)) / 32 = 2 by omega,
      show (64 + (24 * h + 6 * j + t - 32)) % 32 = 24 * h + 6 * j + t - 32 by omega,
      BitVec.getLsbD_setWidth, decide_eq_true (by omega : 24 * h + 6 * j + t - 32 < 16), Bool.true_and]
    rfl

/-- The slots of a configuration on fewer slots, with no external words. -/
theorem ok_fewer {c c' : Cfg} {s : VG.X86.State} (h : Ok c s) (hb : c'.base = c.base) (hn : c'.slots ≤ c.slots)
    (he : c'.exts = 0) : Ok c' s :=
  ⟨fun k hk => by rw [hb]; exact h.slotIn k (by omega), fun k hk => absurd hk (by omega),
    by rw [hb]; have := h.fit; omega, fun k _ j hj => absurd hj (by omega)⟩

/-- One round: `(L, R) := (R, L ⊕ f(R, K))` on slots `L` and `R`, with the
round key at `esi`. -/
theorem round_ok {s : VG.X86.State} (hok : Ok VG.Proof.CmacTripleDes.X86.rCfg s) :
    ∃ s', runBlock isa VG.Impl.CmacTripleDes.X86.round s = some s' ∧
      VG.Proof.CmacTripleDes.X86.slotW s' slotL = VG.Proof.CmacTripleDes.X86.slotW s slotR ∧
      VG.Proof.CmacTripleDes.X86.slotW s' slotR = VG.Proof.CmacTripleDes.X86.slotW s slotL ^^^ Spec.TripleDes.roundFunction (VG.Proof.CmacTripleDes.X86.slotW s slotR) (VG.Proof.CmacTripleDes.X86.key48 s) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.X86.rCfg s] s.mem s'.mem := by
  have hfit := hok.fit
  simp only [VG.Proof.CmacTripleDes.X86.rCfg] at hfit
  have hb : ∀ k ≤ 17, (s.gpr .ebp).toNat + 4 * k + 4 ≤ 2 ^ 32 := fun k hk => by omega
  obtain ⟨s₁, h₁, hx, L₁, R₁, rd₁, wr₁, k₁, f₁⟩ := VG.Proof.CmacTripleDes.X86.inputs_ok hok
  have e₁ : s₁.gpr .ebp = s.gpr .ebp := k₁ _ (by simp [VG.Proof.CmacTripleDes.X86.kept])
  have i₁ : s₁.gpr .esi = s.gpr .esi := k₁ .esi (by simp [VG.Proof.CmacTripleDes.X86.kept])
  have hok₁ : Ok VG.Proof.CmacTripleDes.X86.rCfg s₁ := hok.congr e₁ i₁ rd₁ wr₁
  obtain ⟨s₂, h₂, y₂, rd₂, wr₂, k₂, f₂⟩ := VG.Proof.CmacTripleDes.X86.sbox_ok (h := 0) (by decide) (VG.Proof.CmacTripleDes.X86.ok_fewer hok₁ rfl (by decide) rfl)
  have e₂ : s₂.gpr .ebp = s.gpr .ebp := (k₂ _ (by simp [VG.Proof.CmacTripleDes.X86.kept])).trans e₁
  -- Half 0's outputs to slot 14.
  have w14 : InRegions s₂.wr (addr (s₂.gpr .ebp) (4 * 14)) 4 := by
    rw [wr₂, e₂, ← e₁]; exact hok₁.slotIn 14 (by decide)
  let s₃ : VG.X86.State := { s₂ with
                              mem := s₂.mem.writeW (addr (s₂.gpr .ebp) (4 * 14)) (s₂.gpr .ebx) }
  have h₃ : runBlock isa [.store (VG.Impl.CmacTripleDes.X86.at_ .ebp (4 * 14)) .ebx] s₂ = some s₃ := VG.Proof.CmacTripleDes.X86.runBlock_store w14
  have e₃ : s₃.gpr .ebp = s.gpr .ebp := e₂
  obtain ⟨s₄, h₄, y₄, rd₄, wr₄, k₄, f₄⟩ := VG.Proof.CmacTripleDes.X86.sbox_ok (h := 1) (by decide)
    (VG.Proof.CmacTripleDes.X86.ok_fewer (hok₁.congr (e₃.trans e₁.symm) (show s₃.gpr .esi = s₁.gpr .esi from k₂ .esi (by simp [VG.Proof.CmacTripleDes.X86.kept]))
      (rd₂ : s₃.rd = s₁.rd) (wr₂ : s₃.wr = s₁.wr)) rfl (by decide) rfl)
  have e₄ : s₄.gpr .ebp = s.gpr .ebp := (k₄ _ (by simp [VG.Proof.CmacTripleDes.X86.kept])).trans e₃
  have w15 : InRegions s₄.wr (addr (s₄.gpr .ebp) (4 * 15)) 4 := by
    rw [wr₄, show s₃.wr = s₁.wr from wr₂, e₄, ← e₁]; exact hok₁.slotIn 15 (by decide)
  let s₅ : VG.X86.State := { s₄ with
                              mem := s₄.mem.writeW (addr (s₄.gpr .ebp) (4 * 15)) (s₄.gpr .ebx) }
  have h₅ : runBlock isa [.store (VG.Impl.CmacTripleDes.X86.at_ .ebp (4 * 15)) .ebx] s₄ = some s₅ := VG.Proof.CmacTripleDes.X86.runBlock_store w15
  have e₅ : s₅.gpr .ebp = s.gpr .ebp := e₄
  have rd₅ : s₅.rd = s₁.rd := rd₄.trans rd₂
  have wr₅ : s₅.wr = s₁.wr := wr₄.trans wr₂
  obtain ⟨s₆, h₆, L₆, R₆, rd₆, wr₆, k₆, f₆⟩ := VG.Proof.CmacTripleDes.X86.output_ok
    (VG.Proof.CmacTripleDes.X86.ok_fewer (hok₁.congr (e₅.trans e₁.symm) (show s₅.gpr .esi = s₁.gpr .esi from
      (k₄ .esi (by simp [VG.Proof.CmacTripleDes.X86.kept])).trans (k₂ .esi (by simp [VG.Proof.CmacTripleDes.X86.kept]))) rd₅ wr₅) rfl (by decide) rfl)
  -- The slots along the way.
  have sep : ∀ j k, j ≠ k → j ≤ 17 → k ≤ 17 →
      Mem.Sep (wordAddr (s.gpr .ebp) j) (32 / 8) (wordAddr (s.gpr .ebp) k) (32 / 8) :=
    fun j k h hj hk => VG.Proof.CmacTripleDes.X86.slot_word_sep _ h (hb j hj) (hb k hk)
  have st₃ : ∀ k, k ≠ 14 → k ≤ 17 → VG.Proof.CmacTripleDes.X86.slotW s₃ k = VG.Proof.CmacTripleDes.X86.slotW s₂ k := fun k hk hk' => by
    show (s₂.mem.writeW (wordAddr (s₂.gpr .ebp) 14) (s₂.gpr .ebx)).readW (wordAddr (s₂.gpr .ebp) k) 32 =
      s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32
    rw [e₂, Mem.readW_writeW_sep (sep k 14 hk hk' (by decide)) (by decide)]
  have st₅ : ∀ k, k ≠ 15 → k ≤ 17 → VG.Proof.CmacTripleDes.X86.slotW s₅ k = VG.Proof.CmacTripleDes.X86.slotW s₄ k := fun k hk hk' => by
    show (s₄.mem.writeW (wordAddr (s₄.gpr .ebp) 15) (s₄.gpr .ebx)).readW (wordAddr (s₄.gpr .ebp) k) 32 =
      s₄.mem.readW (wordAddr (s₄.gpr .ebp) k) 32
    rw [e₄, Mem.readW_writeW_sep (sep k 15 hk hk' (by decide)) (by decide)]
  have fr₂ : ∀ k, 7 ≤ k → k ≤ 17 → VG.Proof.CmacTripleDes.X86.slotW s₂ k = VG.Proof.CmacTripleDes.X86.slotW s₁ k := fun k h₁' h₂' => by
    show s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32 = s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32
    rw [e₂, ← e₁]
    exact VG.Proof.CmacTripleDes.X86.slot_frame (n := 7) f₂ h₁' (by rw [e₁]; exact hb k h₂')
  have fr₄ : ∀ k, 14 ≤ k → k ≤ 17 → VG.Proof.CmacTripleDes.X86.slotW s₄ k = VG.Proof.CmacTripleDes.X86.slotW s₃ k := fun k h₁' h₂' => by
    show s₄.mem.readW (wordAddr (s₄.gpr .ebp) k) 32 = s₃.mem.readW (wordAddr (s₃.gpr .ebp) k) 32
    rw [e₄, ← e₃]
    exact VG.Proof.CmacTripleDes.X86.slot_frame (n := 14) f₄ h₁' (by rw [e₃]; exact hb k h₂')
  have slotLR : ∀ k, 16 ≤ k → k ≤ 17 → VG.Proof.CmacTripleDes.X86.slotW s₅ k = VG.Proof.CmacTripleDes.X86.slotW s k := fun k h₁' h₂' => by
    rw [st₅ k (by omega) h₂', fr₄ k (by omega) h₂', st₃ k (by omega) h₂', fr₂ k (by omega) h₂']
    rcases (by omega : k = 16 ∨ k = 17) with rfl | rfl
    · exact L₁
    · exact R₁
  have slot14 : VG.Proof.CmacTripleDes.X86.slotW s₅ 14 = s₂.gpr .ebx := by
    rw [st₅ 14 (by decide) (by decide), fr₄ 14 (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  have slot15 : VG.Proof.CmacTripleDes.X86.slotW s₅ 15 = s₄.gpr .ebx := Mem.readW_writeW_self32 _ _ _
  have box₄ : ∀ p, VG.Proof.CmacTripleDes.X86.boxIn 1 s₃ p = VG.Proof.CmacTripleDes.X86.boxIn 1 s₁ p := fun p => by
    apply BitVec.eq_of_getLsbD_eq
    intro t ht
    rw [VG.Proof.CmacTripleDes.X86.boxIn, VG.Proof.CmacTripleDes.X86.boxIn, getLsbD_ofBits, getLsbD_ofBits]
    by_cases ht6 : t < 6
    · rw [st₃ (7 * 1 + t) (by omega) (by omega), fr₂ (7 * 1 + t) (by omega) (by omega)]
    · simp [ht6]
  refine ⟨s₆, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [VG.Impl.CmacTripleDes.X86.round, VG.Proof.CmacTripleDes.X86.runBlock_append, VG.Proof.CmacTripleDes.X86.runBlock_append, h₁, Option.bind_some, sboxes, VG.Proof.CmacTripleDes.X86.runBlock_append, VG.Proof.CmacTripleDes.X86.runBlock_append,
      VG.Proof.CmacTripleDes.X86.runBlock_append, h₂, Option.bind_some, h₃, Option.bind_some, h₄, Option.bind_some, h₅, Option.bind_some, h₆]
  · rw [L₆, slotLR slotR (by decide) (by decide)]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hu := VG.Proof.CmacTripleDes.X86.pSrc_lt j hj
    rw [R₆ j hj, VG.Proof.CmacTripleDes.X86.oGR, ite_eq_left hj, BitVec.getLsbD_xor, getLsbD_roundFunction _ _ hj, xorBits_cons,
      xorBits_cons, xorBits_nil, Bool.xor_false]
    have hL : bitOf (VG.Proof.CmacTripleDes.X86.oW s₅) (64 + j) = (VG.Proof.CmacTripleDes.X86.slotW s slotL).getLsbD j := by
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, bitOf, VG.Proof.CmacTripleDes.X86.oW, show (64 + j) / 32 = 2 by omega,
        show (64 + j) % 32 = j by omega]
      rw [slotLR slotL (by decide) (by decide)]
    rw [hL, Bool.xor_comm]
    congr 1
    obtain ⟨b, hb', hbe⟩ : ∃ b, b < 4 ∧ pSrc j % 4 = b := ⟨_, Nat.mod_lt _ (by decide), rfl⟩
    by_cases hh : pSrc j / 4 < 4
    · -- Half 0, in slot 14.
      have hi : boxOf 0 (pSrc j / 4) = 7 - pSrc j / 4 := by simp [boxOf]
      have ho := VG.Proof.CmacTripleDes.X86.off_lt4 0 (by decide) _ hh b hb'
      have hpos : VG.Proof.CmacTripleDes.X86.sAtom (pSrc j) = 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b := by
        rw [VG.Proof.CmacTripleDes.X86.sAtom, outHalf, ite_eq_left hh, ite_eq_left rfl, outPos, hi, Nat.mod_eq_of_lt hh, hbe]
      have hbit : bitOf (VG.Proof.CmacTripleDes.X86.oW s₅) (VG.Proof.CmacTripleDes.X86.sAtom (pSrc j)) =
          (VG.Proof.CmacTripleDes.X86.slotW s₅ 14).getLsbD (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b) := by
        rw [hpos]
        simp only [↓reduceIte, bitOf, VG.Proof.CmacTripleDes.X86.oW,
          Nat.div_eq_of_lt (show 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b < 32 by omega),
          Nat.mod_eq_of_lt (show 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b < 32 by omega)]
      rw [hbit, slot14, y₂ _ hh b hb', VG.Proof.CmacTripleDes.X86.boxIn_eq hx (by decide) hh ho, hi]
      simp only [hbe]
    · -- Half 1, in slot 15.
      have hm : pSrc j / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
      have hi : boxOf 1 (pSrc j / 4 % 4) = 7 - pSrc j / 4 := by simp only [boxOf]; omega
      have ho := VG.Proof.CmacTripleDes.X86.off_lt4 1 (by decide) _ hm b hb'
      have hpos : VG.Proof.CmacTripleDes.X86.sAtom (pSrc j) = 32 + (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b) := by
        rw [VG.Proof.CmacTripleDes.X86.sAtom, outHalf, ite_eq_right hh, ite_eq_right (by decide), outPos, hi, hbe]
      have hbit : bitOf (VG.Proof.CmacTripleDes.X86.oW s₅) (VG.Proof.CmacTripleDes.X86.sAtom (pSrc j)) =
          (VG.Proof.CmacTripleDes.X86.slotW s₅ 15).getLsbD (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b) := by
        rw [hpos]
        simp only [reduceCtorEq, ↓reduceIte, bitOf, VG.Proof.CmacTripleDes.X86.oW,
          show (32 + (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b)) / 32 = 1 by omega,
          show (32 + (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b)) % 32 =
            6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b by omega]
      rw [hbit, slot15, y₄ _ hm b hb', box₄, VG.Proof.CmacTripleDes.X86.boxIn_eq hx (by decide) hm ho, hi]
      simp only [hbe]
  · rw [rd₆, rd₅]; exact rd₁
  · rw [wr₆, wr₅]; exact wr₁
  · rw [k₆ r hr, show s₅.gpr r = s₄.gpr r from rfl, k₄ r hr, show s₃.gpr r = s₂.gpr r from rfl, k₂ r hr, k₁ r hr]
  · have R : ∀ (c : Cfg) (t : VG.X86.State), c.base = .ebp → c.slots ≤ 18 → t.gpr .ebp = s.gpr .ebp →
        ∀ r ∈ [slotRegion c t], ∃ r' ∈ [slotRegion VG.Proof.CmacTripleDes.X86.rCfg s], Region.Sub r r' := fun c t hc hn ht r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [slotRegion, hc, ht]
      exact Region.sub_prefix (by simp only [VG.Proof.CmacTripleDes.X86.rCfg]; omega)
    have cw : ∀ k ≤ 17, (slotRegion VG.Proof.CmacTripleDes.X86.rCfg s).Contains (wordAddr (s.gpr .ebp) k) (32 / 8) := fun k hk => by
      rw [VG.Proof.CmacTripleDes.X86.wordAddr_eq _ (by omega)]
      exact Offset.contains_base _ (by simp only [VG.Proof.CmacTripleDes.X86.rCfg]; omega) (by omega)
    have f₃ : Frame [slotRegion VG.Proof.CmacTripleDes.X86.rCfg s] s₂.mem s₃.mem := by
      show Frame _ s₂.mem (s₂.mem.writeW (wordAddr (s₂.gpr .ebp) 14) _)
      rw [e₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 14 (by decide))
    have f₅ : Frame [slotRegion VG.Proof.CmacTripleDes.X86.rCfg s] s₄.mem s₅.mem := by
      show Frame _ s₄.mem (s₄.mem.writeW (wordAddr (s₄.gpr .ebp) 15) _)
      rw [e₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 15 (by decide))
    exact ((((f₁.trans (f₂.sub (R _ _ rfl (by decide) e₁))).trans f₃).trans
      (f₄.sub (R _ _ rfl (by decide) e₃))).trans f₅).trans (f₆.sub (R _ _ rfl (by decide) e₅))

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Block`. -/
section

/-!
# TDEA on x86 (32-bit): the passes and the block

Untrusted: everything here is checked by Lean.

As on 32-bit ARM (`Proof/CmacTripleDes/Arm/Block.lean`): `block` encrypts the
64-bit block in `eax:edx` with the key schedule at `esi` (`block_ok`): `IP`
into slots `L` and `R`, three passes of sixteen rounds (`pass_ok`, the round
keys a step apart, the halves exchanged after each pass), and `IP⁻¹`. During
the block, `esi` points to slot `kpos p j` of the key schedule before round
`j` of pass `p`, and slots 18–20 of the scratch buffer at `ebp` hold the
counters and the step. The block changes only its words of the scratch
buffer (bytes `[0, 84)`) and the registers but `esp` and `ebp`.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.X86.Straight VG.X86.Wp VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86
  VG.Proof.CmacTripleDes

/-- What the block needs: the key schedule at `esi` readable, and the words
0–20 of the scratch buffer at `ebp` writable, apart from it. -/
structure BlockPre (s : State) : Prop where
  sched : ∃ len, (⟨(s.gpr .esi).setWidth 64, len⟩ : Region) ∈ s.rd ++ s.wr ∧ 384 ≤ len ∧
    (s.gpr .esi).toNat + len ≤ 2 ^ 32
  scr : ∃ len, (⟨(s.gpr .ebp).setWidth 64, len⟩ : Region) ∈ s.wr ∧ 84 ≤ len ∧
    (s.gpr .ebp).toNat + len ≤ 2 ^ 32
  disj : Region.Disjoint ⟨(s.gpr .ebp).setWidth 64, 84⟩ ⟨(s.gpr .esi).setWidth 64, 384⟩

/-- The block's words of the scratch buffer. -/
abbrev xR (s₀ : State) : Region := ⟨(s₀.gpr .ebp).setWidth 64, 84⟩

/-- What the block keeps. -/
structure Same (s₀ s : State) : Prop where
  ebp : s.gpr .ebp = s₀.gpr .ebp
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacTripleDes.X86.xR s₀] s₀.mem s.mem

/-- The key schedule. -/
abbrev sch (s₀ : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem ((s₀.gpr .esi).setWidth 64)

/-- Word `k` at offset `off` of a region that does not wrap around. -/
theorem in_word {rs : List Region} {b : BitVec 32} {len off k : Nat}
    (hr : (⟨b.setWidth 64, len⟩ : Region) ∈ rs) (hfit : b.toNat + len ≤ 2 ^ 32) (h : off + 4 * k + 4 ≤ len) :
    InRegions rs (wordAddr (b + BitVec.ofNat 32 off) k) 4 :=
  ⟨_, hr, contains_word rfl hfit h (Nat.le_refl _)⟩

theorem add_zero32 (b : BitVec 32) : b + BitVec.ofNat 32 0 = b := BitVec.add_zero b

/-- Word `k` of a region at `b` that does not wrap around. -/
theorem contains_w {b : BitVec 32} {len k : Nat} (hfit : b.toNat + len ≤ 2 ^ 32) (h : 4 * k + 4 ≤ len) :
    (⟨b.setWidth 64, len⟩ : Region).Contains (wordAddr b k) 4 := by
  have := contains_word (r := ⟨b.setWidth 64, len⟩) (b := b) (off := 0) (k := k) (n := len) rfl hfit (by omega)
    (Nat.le_refl _)
  rwa [VG.Proof.CmacTripleDes.X86.add_zero32] at this

theorem contains_w_off {b : BitVec 32} {len off k : Nat} (hfit : b.toNat + len ≤ 2 ^ 32)
    (h : off + 4 * k + 4 ≤ len) :
    (⟨b.setWidth 64, len⟩ : Region).Contains (wordAddr (b + BitVec.ofNat 32 off) k) 4 :=
  contains_word rfl hfit h (Nat.le_refl _)

theorem wordAddr_off (b : BitVec 32) {off k : Nat} (h : b.toNat + off + 4 * k < 2 ^ 32) :
    wordAddr (b + BitVec.ofNat 32 off) k = b.setWidth 64 + BitVec.ofNat 64 (off + 4 * k) := by
  rw [wordAddr, VG.X86.Straight.addr_add_ofNat, addr_eq (by omega)]

theorem ok_at {s₀ s : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) (h : VG.Proof.CmacTripleDes.X86.Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * n)) : Ok VG.Proof.CmacTripleDes.X86.rCfg s := by
  obtain ⟨lR, hR, hRl, hRw⟩ := hp.sched
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, ?_, fun k hk' j hj => ?_⟩
  · simp only [VG.Proof.CmacTripleDes.X86.rCfg] at hk'
    rw [h.wr, show rCfg.base = .ebp from rfl, h.ebp, ← VG.Proof.CmacTripleDes.X86.add_zero32 (s₀.gpr .ebp)]
    exact VG.Proof.CmacTripleDes.X86.in_word hX hXw (by omega)
  · simp only [VG.Proof.CmacTripleDes.X86.rCfg] at hk'
    rw [h.rd, h.wr, show rCfg.ext = .esi from rfl, hk]
    exact VG.Proof.CmacTripleDes.X86.in_word hR hRw (by omega)
  · show (s.gpr .ebp).toNat + 4 * 18 ≤ 2 ^ 32
    rw [h.ebp]; omega
  · simp only [VG.Proof.CmacTripleDes.X86.rCfg] at hk' hj
    rw [show rCfg.base = .ebp from rfl, show rCfg.ext = .esi from rfl, h.ebp, hk]
    exact hp.disj.sep (VG.Proof.CmacTripleDes.X86.contains_w (by omega) (by omega)) (VG.Proof.CmacTripleDes.X86.contains_w_off (len := 384) (by omega) (by omega))

theorem key_at {s₀ s : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) (h : VG.Proof.CmacTripleDes.X86.Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * n)) : VG.Proof.CmacTripleDes.X86.key48 s = ((VG.Proof.CmacTripleDes.X86.sch s₀).getD n 0).setWidth 48 := by
  obtain ⟨lR, hR, hRl, hRw⟩ := hp.sched
  rw [scheduleAt_getD _ _ hn, setWidth48_readW]
  have rd : ∀ d, d + 4 ≤ 384 → s.mem.readW ((s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 32 =
      s₀.mem.readW ((s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 32 := fun d hd =>
    h.frame.readW (r := ⟨(s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.disj.symm.sub_left (Offset.sub_base _ hd)) (by decide)
  rw [VG.Proof.CmacTripleDes.X86.key48, VG.Proof.CmacTripleDes.X86.keyLo, VG.Proof.CmacTripleDes.X86.keyHi, hk, VG.Proof.CmacTripleDes.X86.wordAddr_off _ (by omega), VG.Proof.CmacTripleDes.X86.wordAddr_off _ (by omega), rd _ (by omega),
    rd _ (by omega), Offset.add_add, show 8 * n + 4 * 0 = 8 * n by omega]

/-! ## The rounds of a pass -/

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

/-- The distance from one round key to the next in pass `p`. -/
def stride (p : Nat) : BitVec 32 := if p % 2 = 1 then BitVec.ofNat 32 (2 ^ 32 - 8) else BitVec.ofNat 32 8

theorem kpos_succ_addr (a : BitVec 32) {p j : Nat} (hp : p < 3) (hj : j < 16) :
    a + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.X86.kpos p j) + VG.Proof.CmacTripleDes.X86.stride p = a + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.X86.kpos p (j + 1)) := by
  rw [BitVec.add_assoc, VG.Proof.CmacTripleDes.X86.stride, VG.Proof.CmacTripleDes.X86.kpos, VG.Proof.CmacTripleDes.X86.kpos]
  congr 1
  split
  · rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [← BitVec.ofNat_add]
    congr 1

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- After `j` rounds of pass `p`, from the halves `lr`. -/
structure PInv (s₀ : State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : State) : Prop where
  same : VG.Proof.CmacTripleDes.X86.Same s₀ s
  esi : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.X86.kpos p j)
  step : VG.Proof.CmacTripleDes.X86.slotW s slotStep = VG.Proof.CmacTripleDes.X86.stride p
  pcnt : VG.Proof.CmacTripleDes.X86.slotW s slotPasses = BitVec.ofNat 32 (3 - p)
  rcnt : VG.Proof.CmacTripleDes.X86.slotW s slotRounds = BitVec.ofNat 32 (16 - j)
  halves : (VG.Proof.CmacTripleDes.X86.slotW s slotL, VG.Proof.CmacTripleDes.X86.slotW s slotR) = VG.Proof.CmacTripleDes.rounds (passKeys (VG.Proof.CmacTripleDes.X86.sch s₀) p) j lr

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : VG.Proof.CmacTripleDes.X86.kpos p j < 48 := by
  simp only [VG.Proof.CmacTripleDes.X86.kpos]; split <;> omega

theorem passKeys_at (s₀ : State) {p j : Nat} (hj : j < 16) :
    passKeys (VG.Proof.CmacTripleDes.X86.sch s₀) p j = ((VG.Proof.CmacTripleDes.X86.sch s₀).getD (VG.Proof.CmacTripleDes.X86.kpos p j) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, VG.Proof.CmacTripleDes.X86.kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega]
  · rw [ite_eq_right h, ite_eq_right h]

/-- The scratch buffer's word `k` (of 21) is inside it. -/
theorem BlockPre.slotIn {s₀ s : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) (h : VG.Proof.CmacTripleDes.X86.Same s₀ s) {k : Nat} (hk : k < 21) :
    InRegions s.wr (addr (s.gpr .ebp) (4 * k)) 4 := by
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr
  rw [h.wr, h.ebp, ← VG.Proof.CmacTripleDes.X86.add_zero32 (s₀.gpr .ebp)]
  exact VG.Proof.CmacTripleDes.X86.in_word hX hXw (by omega)

theorem BlockPre.slotIn' {s₀ s : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) (h : VG.Proof.CmacTripleDes.X86.Same s₀ s) {k : Nat} (hk : k < 21) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (4 * k)) 4 := by
  obtain ⟨r, hr, hc⟩ := hp.slotIn h hk
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem BlockPre.fit {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) : (s₀.gpr .ebp).toNat + 84 ≤ 2 ^ 32 := by
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr; omega

/-- Slots `j` and `k` are apart. -/
theorem slot_ne {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) {j k : Nat} (h : j ≠ k) (hj : j < 21) (hk : k < 21) :
    Mem.Sep (wordAddr (s₀.gpr .ebp) j) (32 / 8) (wordAddr (s₀.gpr .ebp) k) (32 / 8) :=
  VG.Proof.CmacTripleDes.X86.slot_word_sep _ h (by have := hp.fit; omega) (by have := hp.fit; omega)

/-- The frame of the block's words, after a write of one of them. -/
theorem Same.write {s₀ s : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) (h : VG.Proof.CmacTripleDes.X86.Same s₀ s) {k : Nat} (hk : k < 21) (v : BitVec 32) :
    Frame [VG.Proof.CmacTripleDes.X86.xR s₀] s₀.mem (s.mem.writeW (wordAddr (s₀.gpr .ebp) k) v) :=
  h.frame.writeW (List.mem_singleton_self _) _ (contains_word rfl (by have := hp.fit; omega)
    (show 0 + 4 * k + 4 ≤ 84 by omega) (Nat.le_refl _) |> fun c => by rwa [VG.Proof.CmacTripleDes.X86.add_zero32] at c)

/-- One round of pass `p`. -/
theorem roundStep_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {j : Nat} (hj : j < 16) {s : State} (h : VG.Proof.CmacTripleDes.X86.PInv s₀ p lr j s) :
    WP isa (.block (VG.Impl.CmacTripleDes.X86.round ++ roundTail)) s fun s' => s'.zf = some (decide (j + 1 = 16)) ∧ VG.Proof.CmacTripleDes.X86.PInv s₀ p lr (j + 1) s' := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, h₁, eL, eR, rd₁, wr₁, k₁, f₁⟩ := VG.Proof.CmacTripleDes.X86.round_ok (VG.Proof.CmacTripleDes.X86.ok_at hp h.same (VG.Proof.CmacTripleDes.X86.kpos_lt hp3 hj) h.esi)
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  have e₁ : s₁.gpr .ebp = s₀.gpr .ebp := (k₁ .ebp (by simp [VG.Proof.CmacTripleDes.X86.kept])).trans h.same.ebp
  have hsub : ∀ r ∈ [slotRegion VG.Proof.CmacTripleDes.X86.rCfg s], ∃ r' ∈ [VG.Proof.CmacTripleDes.X86.xR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [slotRegion, VG.Proof.CmacTripleDes.X86.xR]; rw [show rCfg.base = .ebp from rfl, h.same.ebp]
    exact Region.sub_prefix (by decide)
  have same₁ : VG.Proof.CmacTripleDes.X86.Same s₀ s₁ :=
    ⟨e₁, (k₁ .esp (by simp [VG.Proof.CmacTripleDes.X86.kept])).trans h.same.esp, rd₁.trans h.same.rd, wr₁.trans h.same.wr,
      h.same.frame.trans (f₁.sub hsub)⟩
  -- The counters past the round's slots.
  have keep : ∀ k, 18 ≤ k → k < 21 → VG.Proof.CmacTripleDes.X86.slotW s₁ k = VG.Proof.CmacTripleDes.X86.slotW s k := fun k h₁' h₂' => by
    show s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32 = s.mem.readW (wordAddr (s.gpr .ebp) k) 32
    rw [e₁, ← h.same.ebp]
    exact VG.Proof.CmacTripleDes.X86.slot_frame (n := 18) f₁ h₁' (by rw [h.same.ebp]; have := hp.fit; omega)
  have i₁ : s₁.gpr .esi = s.gpr .esi := k₁ .esi (by simp [VG.Proof.CmacTripleDes.X86.kept])
  -- `roundTail`.
  have in20 := hp.slotIn' same₁ (k := slotStep) (by decide)
  have in18 := hp.slotIn' same₁ (k := slotRounds) (by decide)
  have w18 := hp.slotIn same₁ (k := slotRounds) (by decide)
  rw [e₁] at in20 in18 w18
  refine wp_ldm e₁ in20 fun s₂' u₂' => VG.X86.Wp.wp_add fun s₂ u₂ _ => wp_ldm (B := s₀.gpr .ebp)
    (by rw [u₂.other _ (by decide), u₂'.other _ (by decide), e₁])
    (by rw [u₂.rd, u₂.wr, u₂'.rd, u₂'.wr]; exact in18) fun s₃ u₃ => VG.X86.Wp.wp_subi fun s₄ u₄ _ z₄ => ?_
  have e₄ : s₄.gpr .ebp = s₀.gpr .ebp := by rw [u₄.other _ (by decide), u₃.other _ (by decide),
    u₂.other _ (by decide), u₂'.other _ (by decide), e₁]
  refine wp_stm e₄ (by rw [u₄.wr, u₃.wr, u₂.wr, u₂'.wr]; exact w18) fun s₅ w₅ => WP.block_nil ?_
  have m₅ : s₅.mem = s₁.mem.writeW (wordAddr (s₀.gpr .ebp) slotRounds) (s₄.gpr .eax) := by
    rw [w₅.mem, u₄.mem, u₃.mem, u₂.mem, u₂'.mem]
  have g₅ : ∀ r, r ≠ .esi → r ≠ .eax → s₅.gpr r = s₁.gpr r := fun r h₁' h₂' => by
    rw [w₅.gpr, u₄.other _ h₂', u₃.other _ h₂', u₂.other _ h₁', u₂'.other _ h₂']
  have e₅ : s₅.gpr .ebp = s₀.gpr .ebp := by rw [g₅ _ (by decide) (by decide), e₁]
  have r18 : VG.Proof.CmacTripleDes.X86.slotW s₁ slotRounds = BitVec.ofNat 32 (16 - j) := by rw [keep _ (by decide) (by decide), h.rcnt]
  have ax₄ : s₄.gpr .eax = BitVec.ofNat 32 (16 - (j + 1)) := by
    rw [u₄.gpr, u₃.gpr, u₂.mem, u₂'.mem, ← e₁, ← VG.Proof.CmacTripleDes.X86.slotW, r18, VG.Proof.CmacTripleDes.X86.ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  have other : ∀ k, k ≠ slotRounds → k < 21 → VG.Proof.CmacTripleDes.X86.slotW s₅ k = VG.Proof.CmacTripleDes.X86.slotW s₁ k := fun k hk hk' => by
    show s₅.mem.readW (wordAddr (s₅.gpr .ebp) k) 32 = s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32
    rw [m₅, e₅, e₁, Mem.readW_writeW_sep (VG.Proof.CmacTripleDes.X86.slot_ne hp hk hk' (by decide)) (by decide)]
  refine ⟨?_, ⟨e₅.trans same₁.ebp.symm |>.trans same₁.ebp, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w₅.zf, z₄, u₃.gpr, u₂.mem, u₂'.mem, ← e₁, ← VG.Proof.CmacTripleDes.X86.slotW, r18, VG.Proof.CmacTripleDes.X86.ofNat_sub_one (by omega) (by omega),
      Wp.ofNat_beq_zero (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [g₅ _ (by decide) (by decide)]; exact same₁.esp
  · rw [w₅.rd, u₄.rd, u₃.rd, u₂.rd, u₂'.rd]; exact same₁.rd
  · rw [w₅.wr, u₄.wr, u₃.wr, u₂.wr, u₂'.wr]; exact same₁.wr
  · rw [m₅]; exact Same.write hp same₁ (by decide) _
  · rw [w₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₂'.gpr, u₂'.other _ (by decide), i₁, h.esi, ← e₁, ← VG.Proof.CmacTripleDes.X86.slotW,
      keep _ (by decide) (by decide), h.step, VG.Proof.CmacTripleDes.X86.kpos_succ_addr _ hp3 hj]
  · rw [other _ (by decide) (by decide), keep _ (by decide) (by decide), h.step]
  · rw [other _ (by decide) (by decide), keep _ (by decide) (by decide), h.pcnt]
  · show s₅.mem.readW (wordAddr (s₅.gpr .ebp) slotRounds) 32 = _
    rw [m₅, e₅, Mem.readW_writeW_self32, ax₄]
  · rw [other _ (by decide) (by decide), other _ (by decide) (by decide), rounds_succ, ← h.halves, eL, eR,
      VG.Proof.CmacTripleDes.X86.key_at hp h.same (VG.Proof.CmacTripleDes.X86.kpos_lt hp3 hj) h.esi, VG.Proof.CmacTripleDes.X86.passKeys_at s₀ hj]

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl

/-- Reading slot `k` after writing slot `j`. -/
theorem rd_wr_ne {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) (m : Mem) {j k : Nat} (v : BitVec 32) (h : k ≠ j) (hk : k < 21)
    (hj : j < 21) :
    (m.writeW (wordAddr (s₀.gpr .ebp) j) v).readW (wordAddr (s₀.gpr .ebp) k) 32 =
      m.readW (wordAddr (s₀.gpr .ebp) k) 32 :=
  Mem.readW_writeW_sep (VG.Proof.CmacTripleDes.X86.slot_ne hp h hk hj) (by decide)

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : State} (h : VG.Proof.CmacTripleDes.X86.Same s₀ s) (hesi : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.X86.kpos p 0))
    (hstep : VG.Proof.CmacTripleDes.X86.slotW s slotStep = VG.Proof.CmacTripleDes.X86.stride p) (hpc : VG.Proof.CmacTripleDes.X86.slotW s slotPasses = BitVec.ofNat 32 (3 - p))
    (hh : (VG.Proof.CmacTripleDes.X86.slotW s slotL, VG.Proof.CmacTripleDes.X86.slotW s slotR) = lr) :
    WP isa pass s (VG.Proof.CmacTripleDes.X86.PInv s₀ p lr 16) := by
  have w18 := hp.slotIn h (k := slotRounds) (by decide)
  rw [h.ebp] at w18
  refine WP.seq (VG.X86.Wp.wp_movi fun s₁ u₁ => wp_stm (B := s₀.gpr .ebp) (by rw [u₁.other _ (by decide), h.ebp])
    (by rw [u₁.wr]; exact w18) fun s₂ w₂ => WP.block_nil ?_)
  have g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by rw [w₂.gpr, u₁.other _ hr]
  have e₂ : s₂.gpr .ebp = s₀.gpr .ebp := by rw [g₂ _ (by decide), h.ebp]
  have m₂ : s₂.mem = s.mem.writeW (wordAddr (s₀.gpr .ebp) slotRounds) (16 : BitVec 32) := by rw [w₂.mem, u₁.mem, u₁.gpr]
  have other : ∀ k, k ≠ slotRounds → k < 21 → VG.Proof.CmacTripleDes.X86.slotW s₂ k = VG.Proof.CmacTripleDes.X86.slotW s k := fun k hk hk' => by
    show s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32 = s.mem.readW (wordAddr (s.gpr .ebp) k) 32
    rw [m₂, e₂, h.ebp, VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ hk hk' (by decide)]
  have hI : VG.Proof.CmacTripleDes.X86.PInv s₀ p lr 0 s₂ :=
    ⟨⟨e₂, by rw [g₂ _ (by decide)]; exact h.esp, by rw [w₂.rd, u₁.rd]; exact h.rd,
      by rw [w₂.wr, u₁.wr]; exact h.wr, by rw [m₂]; exact Same.write hp h (by decide) _⟩,
      by rw [g₂ _ (by decide), hesi], by rw [other _ (by decide) (by decide), hstep],
      by rw [other _ (by decide) (by decide), hpc],
      by show s₂.mem.readW (wordAddr (s₂.gpr .ebp) slotRounds) 32 = _; rw [m₂, e₂, Mem.readW_writeW_self32]; rfl,
      by rw [other _ (by decide) (by decide), other _ (by decide) (by decide), hh]; rfl⟩
  refine WP.loop (M := isa) (body := .block (VG.Impl.CmacTripleDes.X86.round ++ roundTail)) (c := .ne) (Q := VG.Proof.CmacTripleDes.X86.PInv s₀ p lr 16)
    (fun (n : Nat) (t : State) => ∃ j, n = 16 - j ∧ j < 16 ∧ VG.Proof.CmacTripleDes.X86.PInv s₀ p lr j t) ?_ 16 _ ⟨0, rfl, by decide, hI⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.X86.roundStep_ok hp hp3 hj ht) fun t' ⟨z', h'⟩ => ?_
  by_cases hz : j + 1 = 16
  · left
    refine ⟨by rw [VG.Proof.CmacTripleDes.X86.eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [VG.Proof.CmacTripleDes.X86.eval_ne, z']; simp [hz], 16 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

/-! ## The passes -/

/-- After `p` passes, from the block `x`. -/
structure OInv (s₀ : State) (x : BitVec 64) (p : Nat) (s : State) : Prop where
  same : VG.Proof.CmacTripleDes.X86.Same s₀ s
  esi : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.X86.kpos p 0)
  step : VG.Proof.CmacTripleDes.X86.slotW s slotStep = VG.Proof.CmacTripleDes.X86.stride p
  pcnt : VG.Proof.CmacTripleDes.X86.slotW s slotPasses = BitVec.ofNat 32 (3 - p)
  halves : (VG.Proof.CmacTripleDes.X86.slotW s slotL, VG.Proof.CmacTripleDes.X86.slotW s slotR) = passes (VG.Proof.CmacTripleDes.X86.sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))

theorem kpos_tail_addr (a : BitVec 32) {p : Nat} (hp : p < 3) :
    a + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.X86.kpos p 16) + (128 - VG.Proof.CmacTripleDes.X86.stride p) = a + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.X86.kpos (p + 1) 0) := by
  rw [BitVec.add_assoc]
  congr 1
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem stride_succ {p : Nat} (hp : p < 3) : 0 - VG.Proof.CmacTripleDes.X86.stride p = VG.Proof.CmacTripleDes.X86.stride (p + 1) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

/-- One pass and the exchange after it. -/
theorem passBody_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) {x : BitVec 64} {p : Nat} (hp3 : p < 3) {s : State}
    (h : VG.Proof.CmacTripleDes.X86.OInv s₀ x p s) :
    WP isa (.seq pass (.block passTail)) s fun s' => s'.zf = some (decide (p + 1 = 3)) ∧ VG.Proof.CmacTripleDes.X86.OInv s₀ x (p + 1) s' := by
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.pass_ok hp hp3 h.same h.esi h.step h.pcnt h.halves) fun s₁ h₁ => ?_)
  have e₁ := h₁.same.ebp
  have rin : ∀ k, k < 21 → InRegions (s₁.rd ++ s₁.wr) (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn' h₁.same hk; rwa [e₁] at this
  have win : ∀ k, k < 21 → InRegions s₁.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn h₁.same hk; rwa [e₁] at this
  refine wp_ldm (o := 4 * slotStep) e₁ (rin _ (by decide)) fun t₁ u₁ => VG.X86.Wp.wp_movi fun t₂ u₂ =>
    VG.X86.Wp.wp_sub fun t₃ u₃ _ => VG.X86.Wp.wp_add fun t₄ u₄ _ => VG.X86.Wp.wp_movi fun t₅ u₅ => VG.X86.Wp.wp_sub fun t₆ u₆ _ => ?_
  have g₆ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₆.gpr r = s₁.gpr r := fun r ha hc hs => by
    rw [u₆.other _ ha, u₅.other _ ha, u₄.other _ hs, u₃.other _ ha, u₂.other _ ha, u₁.other _ hc]
  have e₆ : t₆.gpr .ebp = s₀.gpr .ebp := by rw [g₆ _ (by decide) (by decide) (by decide), e₁]
  have wr₆ : t₆.wr = s₁.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have rd₆ : t₆.rd = s₁.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have m₆ : t₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have stp : t₁.gpr .ecx = VG.Proof.CmacTripleDes.X86.stride p := by rw [u₁.gpr, ← e₁, ← VG.Proof.CmacTripleDes.X86.slotW, h₁.step]
  refine wp_stm e₆ (by rw [wr₆]; exact win _ (by decide)) fun t₇ w₇ => ?_
  refine wp_ldm (o := 4 * slotL) (by rw [w₇.gpr, e₆]) (by rw [w₇.rd, w₇.wr, rd₆, wr₆]; exact rin _ (by decide))
    fun t₈ u₈ => ?_
  refine wp_ldm (o := 4 * slotR) (by rw [u₈.other _ (by decide), w₇.gpr, e₆])
    (by rw [u₈.rd, u₈.wr, w₇.rd, w₇.wr, rd₆, wr₆]; exact rin _ (by decide)) fun t₉ u₉ => ?_
  have e₉ : t₉.gpr .ebp = s₀.gpr .ebp := by rw [u₉.other _ (by decide), u₈.other _ (by decide), w₇.gpr, e₆]
  have wr₉ : t₉.wr = s₁.wr := by rw [u₉.wr, u₈.wr, w₇.wr, wr₆]
  refine wp_stm (o := 4 * slotL) e₉ (by rw [wr₉]; exact win _ (by decide)) fun t₁₀ w₁₀ => ?_
  refine wp_stm (o := 4 * slotR) (by rw [w₁₀.gpr, e₉]) (by rw [w₁₀.wr, wr₉]; exact win _ (by decide))
    fun t₁₁ w₁₁ => ?_
  refine wp_ldm (o := 4 * slotPasses) (by rw [w₁₁.gpr, w₁₀.gpr, e₉])
    (by rw [w₁₁.rd, w₁₁.wr, w₁₀.rd, w₁₀.wr, u₉.rd, u₈.rd, w₇.rd, rd₆, wr₉]; exact rin _ (by decide))
    fun t₁₂ u₁₂ => VG.X86.Wp.wp_subi fun t₁₃ u₁₃ _ z₁₃ => ?_
  have e₁₃ : t₁₃.gpr .ebp = s₀.gpr .ebp := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), w₁₁.gpr, w₁₀.gpr, e₉]
  refine wp_stm (o := 4 * slotPasses) e₁₃
    (by rw [u₁₃.wr, u₁₂.wr, w₁₁.wr, w₁₀.wr, wr₉]; exact win _ (by decide)) fun t₁₄ w₁₄ => WP.block_nil ?_
  -- The memory.
  have m₁₁ : t₁₁.mem = ((s₁.mem.writeW (wordAddr (s₀.gpr .ebp) slotStep) (t₆.gpr .eax)).writeW
      (wordAddr (s₀.gpr .ebp) slotL) (t₉.gpr .ecx)).writeW (wordAddr (s₀.gpr .ebp) slotR) (t₉.gpr .eax) := by
    rw [w₁₁.mem, w₁₀.mem, w₁₀.gpr, u₉.mem, u₈.mem, w₇.mem, m₆]
  have m₁₄ : t₁₄.mem = t₁₁.mem.writeW (wordAddr (s₀.gpr .ebp) slotPasses) (t₁₃.gpr .eax) := by
    rw [w₁₄.mem, u₁₃.mem, u₁₂.mem]
  have rd₁ : ∀ k, VG.Proof.CmacTripleDes.X86.slotW s₁ k = s₁.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [VG.Proof.CmacTripleDes.X86.slotW, e₁]
  have ax₉L : t₉.gpr .eax = VG.Proof.CmacTripleDes.X86.slotW s₁ slotL := by
    rw [u₉.other _ (by decide), u₈.gpr, w₇.mem, m₆, VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  have ax₉R : t₉.gpr .ecx = VG.Proof.CmacTripleDes.X86.slotW s₁ slotR := by
    rw [u₉.gpr, u₈.mem, w₇.mem, m₆, VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  have pc₁₂ : t₁₂.gpr .eax = VG.Proof.CmacTripleDes.X86.slotW s₁ slotPasses := by
    rw [u₁₂.gpr, m₁₁, VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  have e₁₄ : t₁₄.gpr .ebp = s₀.gpr .ebp := by rw [w₁₄.gpr, e₁₃]
  have sl : ∀ k, VG.Proof.CmacTripleDes.X86.slotW t₁₄ k = t₁₄.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [VG.Proof.CmacTripleDes.X86.slotW, e₁₄]
  have g₁₄ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₁₄.gpr r = s₁.gpr r := fun r ha hc hs => by
    rw [w₁₄.gpr, u₁₃.other _ ha, u₁₂.other _ ha, w₁₁.gpr, w₁₀.gpr, u₉.other _ hc, u₈.other _ ha, w₇.gpr,
      g₆ _ ha hc hs]
  refine ⟨?_, ⟨⟨e₁₄, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [w₁₄.zf, z₁₃, pc₁₂, h₁.pcnt, VG.Proof.CmacTripleDes.X86.ofNat_sub_one (by omega) (by omega), Wp.ofNat_beq_zero (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [g₁₄ _ (by decide) (by decide) (by decide)]; exact h₁.same.esp
  · rw [w₁₄.rd, u₁₃.rd, u₁₂.rd, w₁₁.rd, w₁₀.rd, u₉.rd, u₈.rd, w₇.rd, rd₆]; exact h₁.same.rd
  · rw [w₁₄.wr, u₁₃.wr, u₁₂.wr, w₁₁.wr, w₁₀.wr, wr₉]; exact h₁.same.wr
  · have xC : ∀ k, k < 21 → (VG.Proof.CmacTripleDes.X86.xR s₀).Contains (wordAddr (s₀.gpr .ebp) k) (32 / 8) := fun k hk =>
      VG.Proof.CmacTripleDes.X86.contains_w (by have := hp.fit; omega) (by omega)
    rw [m₁₄, m₁₁]
    exact (((h₁.same.frame.writeW (List.mem_singleton_self _) _ (xC slotStep (by decide))).writeW
      (List.mem_singleton_self _) _ (xC slotL (by decide))).writeW (List.mem_singleton_self _) _
      (xC slotR (by decide))).writeW (List.mem_singleton_self _) _ (xC slotPasses (by decide))
  · rw [w₁₄.gpr, u₁₃.other .esi (by decide), u₁₂.other .esi (by decide), w₁₁.gpr, w₁₀.gpr,
      u₉.other .esi (by decide), u₈.other .esi (by decide), w₇.gpr, u₆.other .esi (by decide),
      u₅.other .esi (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₃.other .esi (by decide), u₂.other .esi (by decide),
      u₂.other .ecx (by decide), u₁.other .esi (by decide), h₁.esi, stp, VG.Proof.CmacTripleDes.X86.kpos_tail_addr _ hp3]
  · rw [sl, m₁₄, VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), m₁₁,
      VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, u₆.gpr, u₅.gpr, u₅.other .ecx (by decide), u₄.other .ecx (by decide),
      u₃.other .ecx (by decide), u₂.other .ecx (by decide), stp, VG.Proof.CmacTripleDes.X86.stride_succ hp3]
  · rw [sl, m₁₄, Mem.readW_writeW_self32, u₁₃.gpr, pc₁₂, h₁.pcnt, VG.Proof.CmacTripleDes.X86.ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  · rw [sl, sl, m₁₄, VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), m₁₁, VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Mem.readW_writeW_self32, ax₉L, ax₉R, passes, ← h₁.halves]
    rfl

/-- The three passes. -/
theorem passes_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) {x : BitVec 64} {s : State} (h : VG.Proof.CmacTripleDes.X86.OInv s₀ x 0 s) :
    WP isa (.loop (.seq pass (.block passTail)) .ne) s (VG.Proof.CmacTripleDes.X86.OInv s₀ x 3) := by
  refine WP.loop (M := isa) (body := .seq pass (.block passTail)) (c := .ne) (Q := VG.Proof.CmacTripleDes.X86.OInv s₀ x 3)
    (fun (n : Nat) (t : State) => ∃ p, n = 3 - p ∧ p < 3 ∧ VG.Proof.CmacTripleDes.X86.OInv s₀ x p t) ?_ 3 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨p, rfl, hp3, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.X86.passBody_ok hp hp3 ht) fun t' ⟨z', h'⟩ => ?_
  by_cases hz : p + 1 = 3
  · left
    refine ⟨by rw [VG.Proof.CmacTripleDes.X86.eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [VG.Proof.CmacTripleDes.X86.eval_ne, z']; simp [hz], 3 - (p + 1), by omega, p + 1, rfl, by omega, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- Bit `b` of a block `hi ‖ lo`, as an atom: of `hi` (input word 0) or `lo`
(input word 1). -/
def xAtom (b : Nat) : Nat := if 32 ≤ b then b - 32 else 32 + b

/-- `IP`'s high half into slot `L`, its low half into slot `R`. -/
def ipGL (t : Nat) : List Nat := if t < 32 then [VG.Proof.CmacTripleDes.X86.xAtom (ipSrc (32 + t))] else []
def ipGR (t : Nat) : List Nat := if t < 32 then [VG.Proof.CmacTripleDes.X86.xAtom (ipSrc t)] else []

theorem ip_check :
    VG.X86.Straight.check (lanes 32 6) VG.Proof.CmacTripleDes.X86.oCfg (linExt 0) ipCode (linEnv [(0, 0), (1, 1)])
      (linPost oCfg.slots 6 [(slotL, VG.Proof.CmacTripleDes.X86.ipGL), (slotR, VG.Proof.CmacTripleDes.X86.ipGR)]) = true := by
  lit_decide

/-- `IP⁻¹(R ‖ L)` into slots 0 (high word) and 1 (low word), from `R` in slot
`L` (input word 0) and `L` in slot `R` (input word 1). -/
def fpG0 (t : Nat) : List Nat := if t < 32 then [VG.Proof.CmacTripleDes.X86.xAtom (fpSrc (32 + t))] else []
def fpG1 (t : Nat) : List Nat := if t < 32 then [VG.Proof.CmacTripleDes.X86.xAtom (fpSrc t)] else []

theorem fp_check :
    VG.X86.Straight.check (lanes 32 6) VG.Proof.CmacTripleDes.X86.oCfg (linExt 0) fpCode (linEnv [(slotL, 0), (slotR, 1)])
      (linPost oCfg.slots 6 [(0, VG.Proof.CmacTripleDes.X86.fpG0), (1, VG.Proof.CmacTripleDes.X86.fpG1)]) = true := by
  lit_decide

theorem ip_kept : kept.all (fun r => ipCode.all fun i => i.dst != some r) = true := by lit_decide

theorem fp_kept : kept.all (fun r => fpCode.all fun i => i.dst != some r) = true := by lit_decide

theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by lit_decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by lit_decide

/-- A bit of `hi ‖ lo`. -/
theorem bit_xAtom (W : Nat → BitVec 32) {b : Nat} (hb : b < 64) :
    bitOf W (VG.Proof.CmacTripleDes.X86.xAtom b) = (W 0 ++ W 1).getLsbD b := by
  rw [BitVec.getLsbD_append, VG.Proof.CmacTripleDes.X86.xAtom]
  by_cases h : 32 ≤ b
  · rw [ite_eq_left h, ite_eq_right (by omega), bitOf, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h, ite_eq_left (by omega), bitOf, show (32 + b) / 32 = 1 by omega,
      show (32 + b) % 32 = b by omega]

theorem ip_ok {s : State} (hok : Ok VG.Proof.CmacTripleDes.X86.oCfg s) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      (VG.Proof.CmacTripleDes.X86.slotW s' slotL, VG.Proof.CmacTripleDes.X86.slotW s' slotR) = split (Spec.TripleDes.permute Spec.TripleDes.ip (VG.Proof.CmacTripleDes.X86.slotW s 0 ++ VG.Proof.CmacTripleDes.X86.slotW s 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.X86.oCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then VG.Proof.CmacTripleDes.X86.slotW s 0 else VG.Proof.CmacTripleDes.X86.slotW s 1
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok VG.Proof.CmacTripleDes.X86.ip_check hok W
    (fun j i hji _ => by
      simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hji
      rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.X86.oCfg]))
  have kp : ∀ r ∈ VG.Proof.CmacTripleDes.X86.kept, s'.gpr r = s.gpr r := fun r hr => hoth _ (List.all_eq_true.mp VG.Proof.CmacTripleDes.X86.ip_kept r hr)
  have e : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [VG.Proof.CmacTripleDes.X86.kept])
  have bit : ∀ j g, (j, g) ∈ [(slotL, VG.Proof.CmacTripleDes.X86.ipGL), (slotR, VG.Proof.CmacTripleDes.X86.ipGR)] → ∀ p < 32,
      (VG.Proof.CmacTripleDes.X86.slotW s' j).getLsbD p = xorBits W (g p) := fun j g h p hp => by
    rw [VG.Proof.CmacTripleDes.X86.slotW, e]; exact hout j g h p hp
  refine ⟨s', hs', ?_, hrd, hwr, kp, hfr⟩
  have hx : W 0 ++ W 1 = VG.Proof.CmacTripleDes.X86.slotW s 0 ++ VG.Proof.CmacTripleDes.X86.slotW s 1 := rfl
  simp only [split, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
  · rw [bit slotL VG.Proof.CmacTripleDes.X86.ipGL (List.mem_cons_self ..) t ht, VG.Proof.CmacTripleDes.X86.ipGL, ite_eq_left ht, xorBits_cons, xorBits_nil,
      Bool.xor_false, VG.Proof.CmacTripleDes.X86.bit_xAtom W (VG.Proof.CmacTripleDes.X86.ipSrc_lt _ (by omega)), hx, BitVec.getLsbD_setWidth, decide_eq_true ht,
      Bool.true_and, BitVec.getLsbD_ushiftRight, getLsbD_permute _ _ (by decide) (show 32 + t < 64 by omega)]
    rfl
  · rw [bit slotR VG.Proof.CmacTripleDes.X86.ipGR (List.mem_cons_of_mem _ (List.mem_cons_self ..)) t ht, VG.Proof.CmacTripleDes.X86.ipGR, ite_eq_left ht, xorBits_cons,
      xorBits_nil, Bool.xor_false, VG.Proof.CmacTripleDes.X86.bit_xAtom W (VG.Proof.CmacTripleDes.X86.ipSrc_lt _ (by omega)), hx, BitVec.getLsbD_setWidth,
      decide_eq_true ht, Bool.true_and, getLsbD_permute _ _ (by decide) (show t < 64 by omega)]
    rfl

theorem fp_ok {s : State} (hok : Ok VG.Proof.CmacTripleDes.X86.oCfg s) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      VG.Proof.CmacTripleDes.X86.slotW s' 0 ++ VG.Proof.CmacTripleDes.X86.slotW s' 1 = Spec.TripleDes.permute Spec.TripleDes.fp (VG.Proof.CmacTripleDes.X86.slotW s slotL ++ VG.Proof.CmacTripleDes.X86.slotW s slotR) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.X86.oCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then VG.Proof.CmacTripleDes.X86.slotW s slotL else VG.Proof.CmacTripleDes.X86.slotW s slotR
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok VG.Proof.CmacTripleDes.X86.fp_check hok W
    (fun j i hji _ => by
      simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hji
      rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.X86.oCfg]))
  have kp : ∀ r ∈ VG.Proof.CmacTripleDes.X86.kept, s'.gpr r = s.gpr r := fun r hr => hoth _ (List.all_eq_true.mp VG.Proof.CmacTripleDes.X86.fp_kept r hr)
  have e : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [VG.Proof.CmacTripleDes.X86.kept])
  have bit : ∀ j g, (j, g) ∈ [(0, VG.Proof.CmacTripleDes.X86.fpG0), (1, VG.Proof.CmacTripleDes.X86.fpG1)] → ∀ p < 32,
      (VG.Proof.CmacTripleDes.X86.slotW s' j).getLsbD p = xorBits W (g p) := fun j g h p hp => by
    rw [VG.Proof.CmacTripleDes.X86.slotW, e]; exact hout j g h p hp
  refine ⟨s', hs', ?_, hrd, hwr, kp, hfr⟩
  have hx : W 0 ++ W 1 = VG.Proof.CmacTripleDes.X86.slotW s slotL ++ VG.Proof.CmacTripleDes.X86.slotW s slotR := rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_append, getLsbD_permute _ _ (by decide) hj,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl]
  by_cases h32 : j < 32
  · rw [ite_eq_left h32, bit 1 VG.Proof.CmacTripleDes.X86.fpG1 (List.mem_cons_of_mem _ (List.mem_cons_self ..)) j h32, VG.Proof.CmacTripleDes.X86.fpG1, ite_eq_left h32,
      xorBits_cons, xorBits_nil, Bool.xor_false, VG.Proof.CmacTripleDes.X86.bit_xAtom W (VG.Proof.CmacTripleDes.X86.fpSrc_lt _ hj), hx]
  · rw [ite_eq_right h32, bit 0 VG.Proof.CmacTripleDes.X86.fpG0 (List.mem_cons_self ..) (j - 32) (by omega), VG.Proof.CmacTripleDes.X86.fpG0, ite_eq_left (by omega),
      xorBits_cons, xorBits_nil, Bool.xor_false, show 32 + (j - 32) = j by omega, VG.Proof.CmacTripleDes.X86.bit_xAtom W (VG.Proof.CmacTripleDes.X86.fpSrc_lt _ hj), hx]

/-! ## The block -/

theorem oCfg_ok {s₀ s : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) (h : VG.Proof.CmacTripleDes.X86.Same s₀ s) : Ok VG.Proof.CmacTripleDes.X86.oCfg s :=
  ⟨fun k hk => hp.slotIn h (by simp only [VG.Proof.CmacTripleDes.X86.oCfg] at hk; omega), fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.X86.oCfg]),
    by show (s.gpr .ebp).toNat + 4 * 18 ≤ 2 ^ 32; rw [h.ebp]; have := hp.fit; omega,
    fun k _ j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.X86.oCfg])⟩

theorem oCfg_sub {s₀ s : State} (h : VG.Proof.CmacTripleDes.X86.Same s₀ s) : ∀ r ∈ [slotRegion VG.Proof.CmacTripleDes.X86.oCfg s], ∃ r' ∈ [VG.Proof.CmacTripleDes.X86.xR s₀], Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [slotRegion, VG.Proof.CmacTripleDes.X86.xR]; rw [show oCfg.base = .ebp from rfl, h.ebp]
    exact Region.sub_prefix (by decide)

/-- TDEA encryption of the block in `eax:edx` (its high and low words) with
the key schedule at `esi`, into `eax:edx`. -/
theorem block_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.BlockPre s₀) :
    WP isa VG.Impl.CmacTripleDes.X86.block s₀ fun s =>
      VG.Proof.CmacTripleDes.X86.Same s₀ s ∧ s.gpr .esi = s₀.gpr .esi ∧
        s.gpr .eax ++ s.gpr .edx = tdes (VG.Proof.CmacTripleDes.X86.sch s₀) (s₀.gpr .eax ++ s₀.gpr .edx) := by
  have xC : ∀ k, k < 21 → (VG.Proof.CmacTripleDes.X86.xR s₀).Contains (wordAddr (s₀.gpr .ebp) k) (32 / 8) := fun k hk =>
    VG.Proof.CmacTripleDes.X86.contains_w (by have := hp.fit; omega) (by omega)
  have same₀ : VG.Proof.CmacTripleDes.X86.Same s₀ s₀ := ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  have win : ∀ k, k < 21 → InRegions s₀.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => hp.slotIn same₀ hk
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_stm (o := 4 * 0) rfl (win 0 (by decide)) fun s₁ w₁ =>
    wp_stm (o := 4 * 1) (by rw [w₁.gpr]) (by rw [w₁.wr]; exact win 1 (by decide)) fun s₂ w₂ => WP.block_nil ?_
  have m₂ : s₂.mem = (s₀.mem.writeW (wordAddr (s₀.gpr .ebp) 0) (s₀.gpr .eax)).writeW (wordAddr (s₀.gpr .ebp) 1)
      (s₀.gpr .edx) := by rw [w₂.mem, w₁.mem, w₁.gpr]
  have same₂ : VG.Proof.CmacTripleDes.X86.Same s₀ s₂ := ⟨by rw [w₂.gpr, w₁.gpr], by rw [w₂.gpr, w₁.gpr], by rw [w₂.rd, w₁.rd],
    by rw [w₂.wr, w₁.wr], by
      rw [m₂]; exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (xC 0 (by decide))).writeW
        (List.mem_singleton_self _) _ (xC 1 (by decide))⟩
  have sl₂ : ∀ k, VG.Proof.CmacTripleDes.X86.slotW s₂ k = s₂.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [VG.Proof.CmacTripleDes.X86.slotW, same₂.ebp]
  have x₂ : VG.Proof.CmacTripleDes.X86.slotW s₂ 0 ++ VG.Proof.CmacTripleDes.X86.slotW s₂ 1 = s₀.gpr .eax ++ s₀.gpr .edx := by
    rw [sl₂, sl₂, m₂, VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
      Mem.readW_writeW_self32]
  obtain ⟨s₃, h₃, ip₃, rd₃, wr₃, k₃, f₃⟩ := VG.Proof.CmacTripleDes.X86.ip_ok (VG.Proof.CmacTripleDes.X86.oCfg_ok hp same₂)
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  have e₃ : s₃.gpr .ebp = s₀.gpr .ebp := (k₃ .ebp (by simp [VG.Proof.CmacTripleDes.X86.kept])).trans same₂.ebp
  have same₃ : VG.Proof.CmacTripleDes.X86.Same s₀ s₃ := ⟨e₃, (k₃ .esp (by simp [VG.Proof.CmacTripleDes.X86.kept])).trans same₂.esp, rd₃.trans same₂.rd,
    wr₃.trans same₂.wr, same₂.frame.trans (f₃.sub (VG.Proof.CmacTripleDes.X86.oCfg_sub same₂))⟩
  have win₃ : ∀ k, k < 21 → InRegions s₃.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn same₃ hk; rwa [e₃] at this
  refine VG.X86.Wp.wp_movi fun s₄ u₄ => wp_stm (o := 4 * slotPasses) (B := s₀.gpr .ebp) (by rw [u₄.other _ (by decide), e₃])
    (by rw [u₄.wr]; exact win₃ _ (by decide)) fun s₅ w₅ => VG.X86.Wp.wp_movi fun s₆ u₆ =>
    wp_stm (o := 4 * slotStep) (B := s₀.gpr .ebp) (by rw [u₆.other _ (by decide), w₅.gpr, u₄.other _ (by decide), e₃])
    (by rw [u₆.wr, w₅.wr, u₄.wr]; exact win₃ _ (by decide)) fun s₇ w₇ => WP.block_nil ?_
  have m₇ : s₇.mem = (s₃.mem.writeW (wordAddr (s₀.gpr .ebp) slotPasses) (3 : BitVec 32)).writeW
      (wordAddr (s₀.gpr .ebp) slotStep) (8 : BitVec 32) := by
    rw [w₇.mem, u₆.mem, u₆.gpr, w₅.mem, u₄.mem, u₄.gpr]
  have g₇ : ∀ r, r ≠ .eax → s₇.gpr r = s₃.gpr r := fun r hr => by
    rw [w₇.gpr, u₆.other _ hr, w₅.gpr, u₄.other _ hr]
  have e₇ : s₇.gpr .ebp = s₀.gpr .ebp := by rw [g₇ _ (by decide), e₃]
  have sl₇ : ∀ k, VG.Proof.CmacTripleDes.X86.slotW s₇ k = s₇.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [VG.Proof.CmacTripleDes.X86.slotW, e₇]
  have sl₃ : ∀ k, VG.Proof.CmacTripleDes.X86.slotW s₃ k = s₃.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [VG.Proof.CmacTripleDes.X86.slotW, e₃]
  have esi₇ : s₇.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.X86.kpos 0 0) := by
    rw [g₇ _ (by decide), k₃ .esi (by simp [VG.Proof.CmacTripleDes.X86.kept]), show s₂.gpr .esi = s₀.gpr .esi by rw [w₂.gpr, w₁.gpr]]
    simp [VG.Proof.CmacTripleDes.X86.kpos]
  have hO : VG.Proof.CmacTripleDes.X86.OInv s₀ (s₀.gpr .eax ++ s₀.gpr .edx) 0 s₇ :=
    ⟨⟨e₇, by rw [g₇ _ (by decide)]; exact same₃.esp, by rw [w₇.rd, u₆.rd, w₅.rd, u₄.rd]; exact same₃.rd,
      by rw [w₇.wr, u₆.wr, w₅.wr, u₄.wr]; exact same₃.wr, by
        rw [m₇]; exact (same₃.frame.writeW (List.mem_singleton_self _) _ (xC slotPasses (by decide))).writeW
          (List.mem_singleton_self _) _ (xC slotStep (by decide))⟩,
      esi₇,
      by rw [sl₇, m₇, Mem.readW_writeW_self32]; rfl,
      by rw [sl₇, m₇, VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl,
      by rw [sl₇, sl₇, m₇, VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
        VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
        VG.Proof.CmacTripleDes.X86.rd_wr_ne hp _ _ (by decide) (by decide) (by decide), ← sl₃, ← sl₃, ip₃, x₂]; rfl⟩
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.passes_ok hp hO) fun s₈ h₈ => ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine VG.X86.Wp.wp_subi fun s₉ u₉ _ _ => WP.block_nil ?_
  have same₉ : VG.Proof.CmacTripleDes.X86.Same s₀ s₉ := ⟨by rw [u₉.other _ (by decide)]; exact h₈.same.ebp,
    by rw [u₉.other _ (by decide)]; exact h₈.same.esp, by rw [u₉.rd]; exact h₈.same.rd,
    by rw [u₉.wr]; exact h₈.same.wr, by rw [u₉.mem]; exact h₈.same.frame⟩
  obtain ⟨s₁₀, h₁₀, fp₁₀, rd₁₀, wr₁₀, k₁₀, f₁₀⟩ := VG.Proof.CmacTripleDes.X86.fp_ok (VG.Proof.CmacTripleDes.X86.oCfg_ok hp same₉)
  refine WP.of_runBlock ⟨s₁₀, h₁₀, ?_⟩
  have e₁₀ : s₁₀.gpr .ebp = s₀.gpr .ebp := (k₁₀ .ebp (by simp [VG.Proof.CmacTripleDes.X86.kept])).trans same₉.ebp
  have same₁₀ : VG.Proof.CmacTripleDes.X86.Same s₀ s₁₀ := ⟨e₁₀, (k₁₀ .esp (by simp [VG.Proof.CmacTripleDes.X86.kept])).trans same₉.esp, rd₁₀.trans same₉.rd,
    wr₁₀.trans same₉.wr, same₉.frame.trans (f₁₀.sub (VG.Proof.CmacTripleDes.X86.oCfg_sub same₉))⟩
  have rin : ∀ k, k < 21 → InRegions (s₁₀.rd ++ s₁₀.wr) (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn' same₁₀ hk; rwa [e₁₀] at this
  refine wp_ldm (o := 4 * 0) e₁₀ (rin 0 (by decide)) fun s₁₁ u₁₁ =>
    wp_ldm (o := 4 * 1) (B := s₀.gpr .ebp) (by rw [u₁₁.other _ (by decide), e₁₀])
    (by rw [u₁₁.rd, u₁₁.wr]; exact rin 1 (by decide)) fun s₁₂ u₁₂ => WP.block_nil ?_
  refine ⟨⟨by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide)]; exact same₁₀.ebp,
    by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide)]; exact same₁₀.esp,
    by rw [u₁₂.rd, u₁₁.rd]; exact same₁₀.rd, by rw [u₁₂.wr, u₁₁.wr]; exact same₁₀.wr,
    by rw [u₁₂.mem, u₁₁.mem]; exact same₁₀.frame⟩, ?_, ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), k₁₀ .esi (by simp [VG.Proof.CmacTripleDes.X86.kept]), u₉.gpr, h₈.esi,
      show 8 * VG.Proof.CmacTripleDes.X86.kpos 3 0 = 504 from rfl, show (504 : BitVec 32) = BitVec.ofNat 32 504 from rfl, BitVec.add_sub_cancel]
  · have sl₁₀ : ∀ k, VG.Proof.CmacTripleDes.X86.slotW s₁₀ k = s₁₀.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [VG.Proof.CmacTripleDes.X86.slotW, e₁₀]
    have sl₉ : ∀ k, VG.Proof.CmacTripleDes.X86.slotW s₉ k = VG.Proof.CmacTripleDes.X86.slotW s₈ k := fun k => by rw [VG.Proof.CmacTripleDes.X86.slotW, VG.Proof.CmacTripleDes.X86.slotW, u₉.mem, u₉.other _ (by decide)]
    rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₂.gpr, u₁₁.mem, ← sl₁₀, ← sl₁₀, fp₁₀, sl₉, sl₉, tdes_eq, ← h₈.halves]

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.KeysLit`. -/
section

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

namespace VG

materialize_value Impl.CmacTripleDes.X86.roundKeys

theorem Proof.CmacTripleDes.X86.roundKeys_eq :
    Impl.CmacTripleDes.X86.roundKeys = Impl.CmacTripleDes.X86.roundKeys.lit :=
  Impl.CmacTripleDes.X86.roundKeys.lit_eq

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Lit`. -/
section

/-! # TDEA-CMAC's x86 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.CmacTripleDes.X86.init
materialize_code Impl.CmacTripleDes.X86.update
materialize_code Impl.CmacTripleDes.X86.finalize

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Contract`. -/
section

/-!
# TDEA-CMAC on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/TripleDesContract.lean`, which imply these
(`Implies.lean`). The arguments are on the stack, from `[esp + 4]` (cdecl);
the functions call nothing and use no stack.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86

/-- `CIPH_K` for TDEA with the key schedule at `w`, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) : Spec.Cmac.Cipher := Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m w)

/-- `vg_cmac_triple_des_init(key, key_len, out, scratch)`. -/
def initX86 : Contract isa where
  pre s :=
    let key : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
    let out : Region := ⟨(VG.X86.arg s 2).setWidth 64, 400⟩
    let scr : Region := ⟨(VG.X86.arg s 3).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [out, scr] ∧ key.Disjoint out ∧ key.Disjoint scr ∧ out.Disjoint scr ∧
      args.Disjoint out ∧ args.Disjoint scr ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 400 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 3).toNat + 640 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      Spec.TripleDes.validKey (VG.X86.arg s 1).toNat
  post s s' :=
    let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem ((VG.X86.arg s 2).setWidth 64) = k ∧
      Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 2).setWidth 64 + 384) 16 = ks.1 ++ ks.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `vg_cmac_triple_des_update(schedule, state, data, n, scratch)`. -/
def updateX86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(VG.X86.arg s 0).setWidth 64, 384⟩
    let state : Region := ⟨(VG.X86.arg s 1).setWidth 64, 8⟩
    let data : Region := ⟨(VG.X86.arg s 2).setWidth 64, 8 * (VG.X86.arg s 3).toNat⟩
    let scr : Region := ⟨(VG.X86.arg s 4).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      (VG.X86.arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 2).toNat + 8 * (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 4).toNat + 640 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 1).setWidth 64) 8 =
      Spec.Cmac.chain (VG.Proof.CmacTripleDes.X86.ciphAt s.mem ((VG.X86.arg s 0).setWidth 64)) (Spec.Aes.bytesAt s.mem ((VG.X86.arg s 1).setWidth 64) 8)
        (Spec.Cmac.blocksAt s.mem ((VG.X86.arg s 2).setWidth 64) 8 (VG.X86.arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `vg_cmac_triple_des_finalize(key, state, last, last_len, scratch)`. -/
def finalizeX86 : Contract isa where
  pre s :=
    let key : Region := ⟨(VG.X86.arg s 0).setWidth 64, 400⟩
    let state : Region := ⟨(VG.X86.arg s 1).setWidth 64, 8⟩
    let last : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
    let scr : Region := ⟨(VG.X86.arg s 4).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      (VG.X86.arg s 0).toNat + 400 ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 4).toNat + 640 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat ≤ 8
  post s s' :=
    let ciph := VG.Proof.CmacTripleDes.X86.ciphAt s.mem ((VG.X86.arg s 0).setWidth 64)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64 + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < (VG.X86.arg s 3).toNat) →
      Spec.Aes.bytesAt s.mem ((VG.X86.arg s 1).setWidth 64) 8 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 1).setWidth 64) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, VG.X86.arg s₁ i = VG.X86.arg s₂ i

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Save`. -/
section

/-!
# TDEA-CMAC on x86: saving and restoring the registers, and the arguments

Untrusted: everything here is checked by Lean. Each function saves our
caller's `ebx`, `esi`, `edi` and `ebp` to bytes `[84, 100)` of the scratch
buffer through `eax` (`save`, a `Spill.saveCode`), and restores them from
there through `ebp`, `ebp` last (`restore`). It loads its arguments from the stack (`wp_arg`).
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86
open VG.Proof.MdStream.X86 (Upd wp_movm)

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `xor d, [b + o]`. -/
theorem wp_xorma {d b : Reg} {o : Nat} {a : Addr} (ha : addr (s.gpr b) o = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem (at_ b o)) :: is)) s Q := by
  subst ha
  exact Wp.wp_xorm rfl hin fun s' u => k s' ⟨u.gpr, u.other, u.mem, u.rd, u.wr⟩

/-- `mov d, [esp + 4 + 4 i]`, the stack argument `i` of the entry state `s₀`. -/
theorem wp_arg {d : Reg} {o : Nat} {s₀ : State} (i : Nat) (ho : o = 4 + 4 * i) (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i)
    (k : ∀ s', Upd s s' d (VG.X86.arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (at_ .esp o)) :: is)) s Q :=
  wp_movm (by rw [VG.Proof.CmacTripleDes.X86.ea_at', hesp, ho]; rfl) hin fun s' u => k s' (hv ▸ u)

end

/-! ## Saving -/

theorem saved_fits : Spill.Fits 100 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 84 ≤ p.2 ∧ p.2 + 4 ≤ 100 := by decide

theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide

/-- A scratch buffer of at least 100 bytes holds the slots. -/
theorem fits_of {S : BitVec 32} {n : Nat} (h : S.toNat + n ≤ 2 ^ 32) (hn : 100 ≤ n) : S.toNat + 100 ≤ 2 ^ 32 := by
  omega

/-- The memory after saving the registers to the scratch buffer at `S`. -/
def savedMem (s₀ : State) (S : BitVec 32) : Mem :=
  Spill.saveMem s₀.mem (S.setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

theorem savedMem_frame (s₀ : State) (S : BitVec 32) :
    Frame [⟨S.setWidth 64 + BitVec.ofNat 64 84, 16⟩] s₀.mem (VG.Proof.CmacTripleDes.X86.savedMem s₀ S) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp => by
    have h := VG.Proof.CmacTripleDes.X86.saved_bound p hp
    rw [show S.setWidth 64 + BitVec.ofNat 64 p.2 = S.setWidth 64 + BitVec.ofNat 64 84 + BitVec.ofNat 64 (p.2 - 84)
      from (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)

/-- Slots unchanged since the registers were saved hold the registers of `s₀`. -/
theorem saved_of {s₀ : State} {S : BitVec 32} {m : Mem}
    (hm : ∀ d, 84 ≤ d → d + 4 ≤ 100 →
      m.readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 = (VG.Proof.CmacTripleDes.X86.savedMem s₀ S).readW (S.setWidth 64 + BitVec.ofNat 64 d) 32) :
    Spill.Saved m (S.setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved := fun p hp =>
  have h := VG.Proof.CmacTripleDes.X86.saved_bound p hp
  (hm _ h.1 h.2).trans (Spill.saveMem_saved_ofNat _ _ _ VG.Proof.CmacTripleDes.X86.saved_fits (by decide) p hp)

/-! ## Restoring -/

/-- The registers but `ebp`, and where they are saved. -/
def saved3 : List (Reg × Nat) := [(.ebx, 84), (.esi, 88), (.edi, 92)]

theorem restore_eq : restore = Spill.restoreCode .ebp (VG.Proof.CmacTripleDes.X86.saved3 ++ [(.ebp, 96)]) ++ [] := rfl

/-- `restore` from the scratch buffer at `S`, whose slots hold `g`. -/
theorem restore_ok {s : State} {S : BitVec 32} {g : Reg → BitVec 32} (hb : s.gpr .ebp = S)
    (hS : S.toNat + 100 ≤ 2 ^ 32)
    (hr : ∀ d, 84 ≤ d → d + 4 ≤ 100 → InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 d) 4)
    (hs : Spill.Saved s.mem (S.setWidth 64 + BitVec.ofNat 64 ·) g saved) :
    WP isa (.block restore) s (Spill.Restored s · g saved) := by
  have ha := Spill.addr_eq_of_fits hS VG.Proof.CmacTripleDes.X86.saved_fits
  rw [VG.Proof.CmacTripleDes.X86.restore_eq]
  refine Spill.restoreBase_ok VG.Proof.CmacTripleDes.X86.saved3 (by decide) (fun p hp => ?_)
    (by rw [hb]; exact hs.congr (fun p hp => (ha p hp).symm) fun _ _ => rfl) fun s' u => WP.block_nil u
  have h := VG.Proof.CmacTripleDes.X86.saved_bound p hp
  rw [hb, ha p hp]; exact hr _ h.1 h.2

/-- The registers restored from slots holding those of `s₀`, with the stack
pointer and the return address kept. -/
theorem restored {s₀ s s' : State} (h : Spill.Restored s s' s₀.gpr saved) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hret : s'.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32) :
    abiPreserved s₀ s' :=
  ⟨h.abi (by decide) (by decide) hsp, hret⟩

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Update`. -/
section

/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_update`

Untrusted: everything here is checked by Lean. The invariant after `k`
blocks (`LInv`): words 32 and 33 of the scratch buffer hold the next block
and the blocks left, only the state, the block's words and those two have
changed since the registers were saved, and the state is the chaining value
after the first `k` blocks.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86 VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_cmpi wp_bswap)

theorem bswap_eq (x : BitVec 32) : bswap x = byteRev32 x := rfl

/-- The key schedule is unchanged outside a frame. -/
theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) :
    Spec.TripleDes.scheduleAt m' p = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro n hn
  rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, scheduleAt_getD _ _ hn]
  exact hf.readW (r := ⟨p + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

theorem addr_zero (x : BitVec 32) : addr x 0 = x.setWidth 64 := by
  simp only [addr]; rw [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]

theorem addr_off2 {x : BitVec 32} {a b : Nat} (h : x.toNat + a + b < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 a) b = x.setWidth 64 + BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
  rw [Straight.addr_add_ofNat, addr_eq (by omega), Offset.add_add]

theorem add0 (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

section
variable (s₀ : State)

abbrev W : BitVec 32 := VG.X86.arg s₀ 0
abbrev St : BitVec 32 := VG.X86.arg s₀ 1
abbrev Dp : BitVec 32 := VG.X86.arg s₀ 2
abbrev N : Nat := (VG.X86.arg s₀ 3).toNat
abbrev S : BitVec 32 := VG.X86.arg s₀ 4

abbrev schR : Region := ⟨(VG.Proof.CmacTripleDes.X86.W s₀).setWidth 64, 384⟩
abbrev stR : Region := ⟨(VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64, 8⟩
abbrev dataR : Region := ⟨(VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64, 8 * VG.Proof.CmacTripleDes.X86.N s₀⟩
abbrev scrR : Region := ⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64, 640⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := VG.Proof.CmacTripleDes.X86.ciphAt s₀.mem ((VG.Proof.CmacTripleDes.X86.W s₀).setWidth 64)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem ((VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64) 8 (VG.Proof.CmacTripleDes.X86.N s₀)

/-- What changes after the registers are saved. -/
abbrev chg : List Region :=
  [VG.Proof.CmacTripleDes.X86.stR s₀, ⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64, 84⟩, ⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩]

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacTripleDes.X86.schR s₀, VG.Proof.CmacTripleDes.X86.dataR s₀, VG.Proof.CmacTripleDes.X86.argsR s₀]
  wr : s₀.wr = [VG.Proof.CmacTripleDes.X86.stR s₀, VG.Proof.CmacTripleDes.X86.scrR s₀]
  sch_st : (VG.Proof.CmacTripleDes.X86.schR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.stR s₀)
  sch_scr : (VG.Proof.CmacTripleDes.X86.schR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.scrR s₀)
  data_st : (VG.Proof.CmacTripleDes.X86.dataR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.stR s₀)
  data_scr : (VG.Proof.CmacTripleDes.X86.dataR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.scrR s₀)
  st_scr : (VG.Proof.CmacTripleDes.X86.stR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.scrR s₀)
  args_st : (VG.Proof.CmacTripleDes.X86.argsR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.stR s₀)
  args_scr : (VG.Proof.CmacTripleDes.X86.argsR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.scrR s₀)
  ret_st : (VG.Proof.CmacTripleDes.X86.retR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.stR s₀)
  ret_scr : (VG.Proof.CmacTripleDes.X86.retR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.scrR s₀)
  sch_fit : (VG.Proof.CmacTripleDes.X86.W s₀).toNat + 384 ≤ 2 ^ 32
  st_fit : (VG.Proof.CmacTripleDes.X86.St s₀).toNat + 8 ≤ 2 ^ 32
  data_fit : (VG.Proof.CmacTripleDes.X86.Dp s₀).toNat + 8 * VG.Proof.CmacTripleDes.X86.N s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacTripleDes.X86.S s₀).toNat + 640 ≤ 2 ^ 32
  esp_fit : (s₀.gpr .esp).toNat + 24 ≤ 2 ^ 32

theorem UPre.of {s₀ : State} (h : updateX86.pre s₀) : VG.Proof.CmacTripleDes.X86.UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = VG.Proof.CmacTripleDes.X86.W s₀
  ebp : s.gpr .ebp = VG.Proof.CmacTripleDes.X86.S s₀
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.mem.readW ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128) 32 = VG.Proof.CmacTripleDes.X86.Dp s₀ + BitVec.ofNat 32 (8 * k)
  left : s.mem.readW ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 132) 32 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.X86.N s₀ - k)
  frame : Frame (VG.Proof.CmacTripleDes.X86.chg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) s.mem
  state : Spec.Aes.bytesAt s.mem ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) 8 =
    Spec.Cmac.chain (VG.Proof.CmacTripleDes.X86.ciph s₀) (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) 8) ((VG.Proof.CmacTripleDes.X86.blks s₀).take k)

/-! ## Regions -/

section
variable {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.UPre s₀)
include hp

theorem UPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.scrR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem UPre.scrEa {s : State} (h : s.gpr .ebp = VG.Proof.CmacTripleDes.X86.S s₀) {d : Nat} (hd : d < 640) :
    s.ea (at_ .ebp d) = (VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [VG.Proof.CmacTripleDes.X86.ea_at', h]; exact addr_eq (by have := hp.scr_fit; omega)

/-- Argument `i`'s address, in the arguments' region. -/
theorem UPre.argAddr_eq {i : Nat} (hi : i < 5) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.esp_fit
  show addr (s₀.gpr .esp) (4 + 4 * i) = addr (s₀.gpr .esp) (4 + 4 * 0) + _
  rw [addr_eq (by omega), addr_eq (by omega), Offset.add_add, show 4 + 4 * 0 + 4 * i = 4 + 4 * i by omega]

/-- The arguments are unchanged while only `chg` changes after the registers are saved. -/
theorem UPre.arg_eq {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.X86.chg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) m) {i : Nat} (hi : i < 5) :
    m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have hsub : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.CmacTripleDes.X86.argsR s₀) := by
    rw [hp.argAddr_eq hi]; exact Offset.sub_base _ (by omega)
  rw [hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
  · exact (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.S s₀)).readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.args_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.args_st.sub_left hsub
    · exact (hp.args_scr.sub_left hsub).sub_right (Region.sub_prefix (by decide))
    · exact (hp.args_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))

theorem UPre.argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.argAddr_eq hi]
  exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.argsR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))

theorem UPre.sched {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.X86.chg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) m) :
    Spec.TripleDes.scheduleAt m ((VG.Proof.CmacTripleDes.X86.W s₀).setWidth 64) = Spec.TripleDes.scheduleAt s₀.mem ((VG.Proof.CmacTripleDes.X86.W s₀).setWidth 64) := by
  rw [VG.Proof.CmacTripleDes.X86.scheduleAt_frame hf fun r hr => ?_]
  · exact VG.Proof.CmacTripleDes.X86.scheduleAt_frame (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sch_st
    · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))

theorem UPre.data {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.X86.chg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) m) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.X86.N s₀) :
    Spec.Aes.bytesAt m ((VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 8 =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 8 := by
  have hsub : Region.Sub ⟨(VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k), 8⟩ (VG.Proof.CmacTripleDes.X86.dataR s₀) :=
    Offset.sub_base _ (by omega)
  rw [bytesAt_frame hf (fun r hr => ?_) (by decide)]
  · exact bytesAt_frame (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.data_st.sub_left hsub
    · exact (hp.data_scr.sub_left hsub).sub_right (Region.sub_prefix (by decide))
    · exact (hp.data_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))

/-- The block's precondition, with the registers and regions of the function. -/
theorem UPre.block {s : State} (h9 : s.gpr .esi = VG.Proof.CmacTripleDes.X86.W s₀) (h10 : s.gpr .ebp = VG.Proof.CmacTripleDes.X86.S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : VG.Proof.CmacTripleDes.X86.BlockPre s where
  sched := ⟨384, by rw [hrd, hwr, hp.rd, h9]; simp, Nat.le_refl _, by rw [h9]; exact hp.sch_fit⟩
  scr := ⟨640, by rw [hwr, hp.wr, h10]; simp, by decide, by rw [h10]; exact hp.scr_fit⟩
  disj := by
    rw [h9, h10]
    exact hp.sch_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-! ## One block -/

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.X86.N s₀) :
    (VG.Proof.CmacTripleDes.X86.blks s₀).take (k + 1) =
      (VG.Proof.CmacTripleDes.X86.blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

/-- The two words at `a` XORed, as a big-endian integer. -/
theorem bswap_xor_append (a₀ a₁ b₀ b₁ : BitVec 32) :
    bswap (a₀ ^^^ b₀) ++ bswap (a₁ ^^^ b₁) = byteRev64 ((a₁ ++ a₀) ^^^ (b₁ ++ b₀)) := by
  rw [VG.Proof.CmacTripleDes.X86.bswap_eq, VG.Proof.CmacTripleDes.X86.bswap_eq, byteRev32_append, BitVec.xor_append]

theorem readW_writeW_far (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

theorem readW_lo_of_hi (m : Mem) (a : Addr) (v w : BitVec 32) :
    ((m.writeW a v).writeW (a + BitVec.ofNat 64 4) w).readW a 32 = v := by
  have := VG.Proof.CmacTripleDes.X86.readW_writeW_far (m.writeW a v) a w (d := 0) (e := 4) (by decide) (by decide) (by decide)
  rw [VG.Proof.CmacTripleDes.X86.add0] at this
  rw [this, Mem.readW_writeW_self32]

theorem body_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.X86.N s₀) {s : State} (h : VG.Proof.CmacTripleDes.X86.LInv s₀ k s) :
    WP isa updBody s fun s' => VG.Proof.CmacTripleDes.X86.LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (VG.Proof.CmacTripleDes.X86.N s₀ - (k + 1) = 0)) := by
  have hN : VG.Proof.CmacTripleDes.X86.N s₀ < 2 ^ 32 := (VG.X86.arg s₀ 3).isLt
  have hsf := hp.scr_fit
  have hdf := hp.data_fit
  have htf := hp.st_fit
  have rdwr : s.rd ++ s.wr = [VG.Proof.CmacTripleDes.X86.schR s₀, VG.Proof.CmacTripleDes.X86.dataR s₀, VG.Proof.CmacTripleDes.X86.argsR s₀, VG.Proof.CmacTripleDes.X86.stR s₀, VG.Proof.CmacTripleDes.X86.scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have scrIn : ∀ d, d + 4 ≤ 640 → InRegions (s.rd ++ s.wr) ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.scrR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  have stIn : ∀ d, d + 4 ≤ 8 → InRegions (s.rd ++ s.wr) ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.stR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  have dIn : ∀ d, d + 4 ≤ 8 →
      InRegions (s.rd ++ s.wr) ((VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr, Offset.add_add]
      exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.dataR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  -- `chainIn`.
  refine WP.seq (?_ : WP isa (.block chainIn) s _)
  simp only [chainIn, stk]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 1 rfl h.esp (hp.argIn h.rd h.wr (by decide)) (hp.arg_eq h.frame (by decide))
    fun s₁ u₁ => ?_
  refine wp_movm (hp.scrEa (by rw [u₁.other _ (by decide), h.ebp]) (by decide))
    (by rw [u₁.rd, u₁.wr]; exact scrIn 128 (by decide)) fun s₂ u₂ => ?_
  have r1₂ : s₂.gpr .ecx = VG.Proof.CmacTripleDes.X86.St s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have r7₂ : s₂.gpr .edi = VG.Proof.CmacTripleDes.X86.Dp s₀ + BitVec.ofNat 32 (8 * k) := by rw [u₂.gpr, u₁.mem, h.dp]
  refine wp_movm (a := (VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) (by rw [VG.Proof.CmacTripleDes.X86.ea_at', r1₂, VG.Proof.CmacTripleDes.X86.addr_zero])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; simpa [VG.Proof.CmacTripleDes.X86.add0] using stIn 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_movm (a := (VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [VG.Proof.CmacTripleDes.X86.ea_at', u₃.other _ (by decide), r1₂]; exact addr_eq (by omega))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.CmacTripleDes.X86.wp_xorma (a := (VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k))
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), r7₂, VG.Proof.CmacTripleDes.X86.addr_off2 (by omega), VG.Proof.CmacTripleDes.X86.add0])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; simpa [VG.Proof.CmacTripleDes.X86.add0] using dIn 0 (by decide))
    fun s₅ u₅ => ?_
  refine VG.Proof.CmacTripleDes.X86.wp_xorma (a := (VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 4)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r7₂, VG.Proof.CmacTripleDes.X86.addr_off2 (by omega)])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact dIn 4 (by decide))
    fun s₆ u₆ => wp_bswap fun s₇ u₇ => wp_bswap fun s₈ u₈ => WP.block_nil ?_
  -- What `chainIn` leaves.
  have g₈ : ∀ r, r ∉ [Reg.eax, .ecx, .edx, .edi] → s₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₈.other _ hr.2.2.1, u₇.other _ hr.1, u₆.other _ hr.2.2.1, u₅.other _ hr.1, u₄.other _ hr.2.2.1,
      u₃.other _ hr.1, u₂.other _ hr.2.2.2, u₁.other _ hr.2.1]
  have m₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have ax₈ : s₈.gpr .eax ++ s₈.gpr .edx = byteRev64 (s.mem.readW ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) 64 ^^^
      s.mem.readW ((VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 64) := by
    rw [u₈.gpr, u₈.other .eax (by decide), u₇.gpr, u₇.other .edx (by decide), u₆.gpr, u₆.other .eax (by decide),
      u₅.gpr, u₅.other .edx (by decide), u₄.gpr, u₄.other .eax (by decide), u₃.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem, readW64_split, readW64_split s.mem ((VG.Proof.CmacTripleDes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)), VG.Proof.CmacTripleDes.X86.bswap_xor_append]
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.block_ok (UPre.block hp (by rw [g₈ _ (by decide), h.esi])
    (by rw [g₈ _ (by decide), h.ebp]) (by rw [rd₈, h.rd]) (by rw [wr₈, h.wr]))) fun s₉ ⟨same, esi₉, ax₉⟩ => ?_)
  have ebp₉ : s₉.gpr .ebp = VG.Proof.CmacTripleDes.X86.S s₀ := by rw [same.ebp, g₈ _ (by decide), h.ebp]
  have esp₉ : s₉.gpr .esp = s₀.gpr .esp := by rw [same.esp, g₈ _ (by decide), h.esp]
  have xR₈ : VG.Proof.CmacTripleDes.X86.xR s₈ = ⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64, 84⟩ := by rw [VG.Proof.CmacTripleDes.X86.xR, g₈ _ (by decide), h.ebp]
  have f₉ : Frame [⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64, 84⟩] s.mem s₉.mem := by rw [← m₈, ← xR₈]; exact same.frame
  have slot : ∀ d, 84 ≤ d → d + 4 ≤ 640 →
      s₉.mem.readW ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s.mem.readW ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => f₉.readW (r := ⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have frame₉ : Frame (VG.Proof.CmacTripleDes.X86.chg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) s₉.mem := h.frame.trans (f₉.mono (by simp))
  have rd₉ : s₉.rd = s₀.rd := by rw [same.rd, rd₈, h.rd]
  have wr₉ : s₉.wr = s₀.wr := by rw [same.wr, wr₈, h.wr]
  have rdwr₉ : s₉.rd ++ s₉.wr = [VG.Proof.CmacTripleDes.X86.schR s₀, VG.Proof.CmacTripleDes.X86.dataR s₀, VG.Proof.CmacTripleDes.X86.argsR s₀, VG.Proof.CmacTripleDes.X86.stR s₀, VG.Proof.CmacTripleDes.X86.scrR s₀] := by
    rw [rd₉, wr₉, hp.rd, hp.wr]; rfl
  simp only [chainOut, stk]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 1 rfl esp₉ (hp.argIn rd₉ wr₉ (by decide)) (hp.arg_eq frame₉ (by decide)) fun t₁ v₁ => ?_
  refine wp_movm (hp.scrEa (by rw [v₁.other _ (by decide), ebp₉]) (by decide))
    (by rw [v₁.rd, v₁.wr, rdwr₉]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun t₂ v₂ => ?_
  refine wp_movm (hp.scrEa (by rw [v₂.other _ (by decide), v₁.other _ (by decide), ebp₉]) (by decide))
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, rdwr₉]
        exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun t₃ v₃ => ?_
  have r1₃ : t₃.gpr .ecx = VG.Proof.CmacTripleDes.X86.St s₀ := by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr]
  have r7₃ : t₃.gpr .edi = VG.Proof.CmacTripleDes.X86.Dp s₀ + BitVec.ofNat 32 (8 * k) := by
    rw [v₃.other _ (by decide), v₂.gpr, v₁.mem, slot 128 (by decide) (by decide), h.dp]
  have r3₃ : t₃.gpr .ebx = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.X86.N s₀ - k) := by
    rw [v₃.gpr, v₂.mem, v₁.mem, slot 132 (by decide) (by decide), h.left]
  refine wp_bswap fun t₄ v₄ => wp_bswap fun t₅ v₅ => ?_
  have stW : ∀ d, d + 4 ≤ 8 → InRegions t₅.wr ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₉, hp.wr]
    exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.stR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_store (a := (VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) (by rw [VG.Proof.CmacTripleDes.X86.ea_at', v₅.other _ (by decide), v₄.other _ (by decide), r1₃,
                               VG.Proof.CmacTripleDes.X86.addr_zero]) (by simpa [VG.Proof.CmacTripleDes.X86.add0] using stW 0 (by decide)) fun t₆ w₆ => ?_
  refine wp_store (a := (VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [VG.Proof.CmacTripleDes.X86.ea_at', w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r1₃]; exact addr_eq (by omega))
    (by rw [w₆.wr]; exact stW 4 (by decide)) fun t₇ w₇ => ?_
  refine wp_addi fun t₈ v₈ => wp_subi fun t₉ v₉ _ => ?_
  have g₉ : ∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx, .edi] → t₉.gpr r = s₉.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₉.other _ hr.2.1, v₈.other _ hr.2.2.2.2, w₇.gpr, w₆.gpr, v₅.other _ hr.2.2.2.1, v₄.other _ hr.1,
      v₃.other _ hr.2.1, v₂.other _ hr.2.2.2.2, v₁.other _ hr.2.2.1]
  have ebp₉' : t₉.gpr .ebp = VG.Proof.CmacTripleDes.X86.S s₀ := by rw [g₉ _ (by decide), ebp₉]
  have wr₉' : t₉.wr = [VG.Proof.CmacTripleDes.X86.stR s₀, VG.Proof.CmacTripleDes.X86.scrR s₀] := by
    rw [v₉.wr, v₈.wr, w₇.wr, w₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₉, hp.wr]
  have scrW : ∀ d, d + 4 ≤ 640 → InRegions t₉.wr ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [wr₉']; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.scrR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_store (hp.scrEa ebp₉' (by decide)) (scrW 128 (by decide)) fun t₁₀ w₁₀ => ?_
  refine wp_store (hp.scrEa (by rw [w₁₀.gpr, ebp₉']) (by decide)) (by rw [w₁₀.wr]; exact scrW 132 (by decide))
    fun t₁₁ w₁₁ => wp_cmpi fun t₁₂ f₁₂ _ z₁₂ => WP.block_nil ?_
  -- The registers stored.
  have r7₉ : t₉.gpr .edi = VG.Proof.CmacTripleDes.X86.Dp s₀ + BitVec.ofNat 32 (8 * (k + 1)) := by
    rw [v₉.other _ (by decide), v₈.gpr, w₇.gpr, w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r7₃,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_add, show 8 * k + 8 = 8 * (k + 1) by omega]
  have r3₉ : t₉.gpr .ebx = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.X86.N s₀ - (k + 1)) := by
    rw [v₉.gpr, v₈.other _ (by decide), w₇.gpr, w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r3₃,
      VG.Proof.CmacTripleDes.X86.ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  -- The memory.
  have m₉ : t₉.mem = (s₉.mem.writeW ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) (bswap (s₉.gpr .eax))).writeW
      ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64 + BitVec.ofNat 64 4) (bswap (s₉.gpr .edx)) := by
    rw [v₉.mem, v₈.mem, w₇.mem, w₆.mem, w₆.gpr, v₅.gpr, v₅.other .eax (by decide), v₄.gpr, v₅.mem, v₄.mem,
      v₄.other .edx (by decide), v₃.other .eax (by decide), v₃.other .edx (by decide), v₂.other .eax (by decide),
      v₂.other .edx (by decide), v₁.other .eax (by decide), v₁.other .edx (by decide), v₃.mem, v₂.mem, v₁.mem]
  have m₁₁ : t₁₁.mem = (t₉.mem.writeW ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128)
      (VG.Proof.CmacTripleDes.X86.Dp s₀ + BitVec.ofNat 32 (8 * (k + 1)))).writeW ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 132)
      (BitVec.ofNat 32 (VG.Proof.CmacTripleDes.X86.N s₀ - (k + 1))) := by
    rw [w₁₁.mem, w₁₀.mem, w₁₀.gpr, r7₉, r3₉]
  have g₁₂ : t₁₂.gpr = t₉.gpr := by rw [f₁₂.gpr, w₁₁.gpr, w₁₀.gpr]
  -- The state.
  have hS : VG.Proof.CmacTripleDes.X86.sch s₈ = Spec.TripleDes.scheduleAt s₀.mem ((VG.Proof.CmacTripleDes.X86.W s₀).setWidth 64) := by
    show Spec.TripleDes.scheduleAt s₈.mem ((s₈.gpr .esi).setWidth 64) = _
    rw [g₈ _ (by decide), h.esi, m₈]; exact UPre.sched hp h.frame
  have hD := UPre.data hp h.frame hk
  have stFrame : Spec.Aes.bytesAt t₁₁.mem ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) 8 =
      Spec.Aes.bytesAt t₉.mem ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) 8 := by
    rw [m₁₁]
    refine bytesAt_frame (rs := [⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩]) ?_ (fun r hr => ?_) (by decide)
    · have c : ∀ d, 128 ≤ d → d + 4 ≤ 136 →
          (⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩ : Region).Contains
            ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => by
        rw [show (VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d =
          (VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (d - 128) from (Offset.add_add_eq _ (by omega)).symm]
        exact Offset.contains_base _ (by omega) (by omega)
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c 132 (by decide) (by decide))
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g₁₂, g₉ _ (by decide), esi₉, g₈ _ (by decide), h.esi]
  · rw [g₁₂, ebp₉']
  · rw [g₁₂, g₉ _ (by decide), esp₉]
  · rw [f₁₂.rd, w₁₁.rd, w₁₀.rd, v₉.rd, v₈.rd, w₇.rd, w₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd₉]
  · rw [f₁₂.wr, w₁₁.wr, w₁₀.wr, wr₉', ← hp.wr]
  · rw [f₁₂.mem, m₁₁, VG.Proof.CmacTripleDes.X86.readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [f₁₂.mem, m₁₁, Mem.readW_writeW_self32]
  · rw [f₁₂.mem, m₁₁, m₉]
    have c4 : (VG.Proof.CmacTripleDes.X86.stR s₀).Contains ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64 + BitVec.ofNat 64 4) (32 / 8) :=
      Offset.contains_base _ (by decide) (by omega)
    have c0 : (VG.Proof.CmacTripleDes.X86.stR s₀).Contains ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) (32 / 8) := by
      simpa [VG.Proof.CmacTripleDes.X86.add0] using Offset.contains_base ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    have cs : ∀ d, 128 ≤ d → d + 4 ≤ 136 →
        (⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩ : Region).Contains ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d)
          (32 / 8) := fun d h₁ h₂ => by
      rw [show (VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d = (VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128 +
        BitVec.ofNat 64 (d - 128) from (Offset.add_add_eq _ (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    exact (((frame₉.writeW (r := VG.Proof.CmacTripleDes.X86.stR s₀) (by simp) _ c0).writeW (r := VG.Proof.CmacTripleDes.X86.stR s₀) (by simp) _ c4).writeW (by simp) _
      (cs 128 (by decide) (by decide))).writeW (by simp) _ (cs 132 (by decide) (by decide))
  · rw [f₁₂.mem, stFrame, m₉, ← le8_readW, readW64_split, Mem.readW_writeW_self32, VG.Proof.CmacTripleDes.X86.readW_lo_of_hi, VG.Proof.CmacTripleDes.X86.bswap_eq, VG.Proof.CmacTripleDes.X86.bswap_eq,
      byteRev32_append, ax₉, ax₈, hS, ← tdesWith_le8, le8_xor, le8_readW, le8_readW, h.state, hD,
      VG.Proof.CmacTripleDes.X86.take_succ_blks s₀ hk, chain_append, chain_single]
  · rw [z₁₂, show t₁₁.gpr .ebx = t₉.gpr .ebx by rw [w₁₁.gpr, w₁₀.gpr], r3₉,
      show ∀ x : BitVec 32, x - 0 = x from fun x => by simp, Wp.ofNat_beq_zero (by omega)]

theorem eval_ne' (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl
theorem eval_e' (s : State) : isa.eval .e s = s.zf := rfl

theorem loop_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.X86.N s₀) {s : State}
    (h : VG.Proof.CmacTripleDes.X86.LInv s₀ k s) : WP isa (.loop updBody .ne) s (VG.Proof.CmacTripleDes.X86.LInv s₀ (VG.Proof.CmacTripleDes.X86.N s₀)) := by
  refine WP.loop (M := isa) (body := updBody) (c := .ne) (Q := VG.Proof.CmacTripleDes.X86.LInv s₀ (VG.Proof.CmacTripleDes.X86.N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = VG.Proof.CmacTripleDes.X86.N s₀ - j ∧ j < VG.Proof.CmacTripleDes.X86.N s₀ ∧ VG.Proof.CmacTripleDes.X86.LInv s₀ j t) ?_ (VG.Proof.CmacTripleDes.X86.N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (VG.Proof.CmacTripleDes.X86.body_ok hp hk h) fun s' ⟨h', z'⟩ => ?_
  by_cases hz : VG.Proof.CmacTripleDes.X86.N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [VG.Proof.CmacTripleDes.X86.eval_ne', z']; simp [hz], ?_⟩
    rwa [show VG.Proof.CmacTripleDes.X86.N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [VG.Proof.CmacTripleDes.X86.eval_ne', z']; simp [hz], VG.Proof.CmacTripleDes.X86.N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## The whole function -/

/-- The arguments of the entry state, unchanged by saving the registers. -/
theorem UPre.arg_saved {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.UPre s₀) {i : Nat} (hi : i < 5) :
    (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀)).readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i :=
  hp.arg_eq (Frame.refl _ _) hi

theorem prologue_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.UPre s₀) :
    WP isa (.block updPre) s₀ fun s => VG.Proof.CmacTripleDes.X86.LInv s₀ 0 s ∧ s.zf = some (decide (VG.Proof.CmacTripleDes.X86.N s₀ = 0)) := by
  have hsc := hp.scr_fit
  have hN : VG.Proof.CmacTripleDes.X86.N s₀ < 2 ^ 32 := (VG.X86.arg s₀ 3).isLt
  rw [show updPre = .mov .eax (stk 20) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 12), .store (at_ .ebp 128) .eax,
      .mov .eax (stk 16), .store (at_ .ebp 132) .eax, .alu .cmp .eax (.imm 0)] : List Instr)) from rfl]
  simp only [stk]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 4 rfl rfl (hp.argIn rfl rfl (by decide)) rfl fun s₁ u₁ => ?_
  refine Spill.save_ofNat_ok saved VG.Proof.CmacTripleDes.X86.saved_fits (by rw [u₁.gpr]; exact VG.Proof.CmacTripleDes.X86.fits_of hp.scr_fit (by decide))
    (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := VG.Proof.CmacTripleDes.X86.saved_bound p hp'
    have hsc' : (VG.X86.arg s₀ 4).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
    rw [u₁.gpr, u₁.wr]
    exact hp.inScr (by omega) (by decide)
  have hm₂ : s₂.mem = VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀) := by
    rw [u₂.mem, u₁.mem, u₁.gpr, VG.Proof.CmacTripleDes.X86.savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (VG.Proof.CmacTripleDes.X86.saved_ne_eax p hp')
  have fr : ∀ m, m = VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀) → Frame (VG.Proof.CmacTripleDes.X86.chg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) m := fun m h => h ▸ Frame.refl _ _
  refine wp_mov fun s₃ u₃ => ?_
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 0 rfl esp₃ (hp.argIn rd₃ wr₃ (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_saved (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 2 rfl (by rw [u₄.other _ (by decide), esp₃])
    (hp.argIn (by rw [u₄.rd, rd₃]) (by rw [u₄.wr, wr₃]) (by decide))
    (by rw [u₄.mem, u₃.mem, hm₂]; exact hp.arg_saved (by decide)) fun s₅ u₅ => ?_
  have ebp₅ : s₅.gpr .ebp = VG.Proof.CmacTripleDes.X86.S s₀ := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]
  refine wp_store (hp.scrEa ebp₅ (by decide)) (by rw [u₅.wr, u₄.wr, wr₃]; exact hp.inScr (by decide) (by decide))
    fun s₆ w₆ => ?_
  have m₆ : s₆.mem = (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀)).writeW ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128) (VG.Proof.CmacTripleDes.X86.Dp s₀) := by
    rw [w₆.mem, u₅.gpr, u₅.mem, u₄.mem, u₃.mem, hm₂]
  have c : ∀ d, 128 ≤ d → d + 4 ≤ 136 →
      (⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩ : Region).Contains ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d)
        (32 / 8) := fun d h₁ h₂ => by
    rw [show (VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d = (VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128 +
      BitVec.ofNat 64 (d - 128) from (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)
  have f₆ : Frame (VG.Proof.CmacTripleDes.X86.chg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (by simp) _ (c 128 (by decide) (by decide))
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 3 rfl (by rw [w₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (hp.argIn (by rw [w₆.rd, u₅.rd, u₄.rd, rd₃]) (by rw [w₆.wr, u₅.wr, u₄.wr, wr₃]) (by decide))
    (hp.arg_eq f₆ (by decide)) fun s₇ u₇ => ?_
  refine wp_store (hp.scrEa (by rw [u₇.other _ (by decide), w₆.gpr, ebp₅]) (by decide))
    (by rw [u₇.wr, w₆.wr, u₅.wr, u₄.wr, wr₃]; exact hp.inScr (by decide) (by decide)) fun s₈ w₈ =>
    wp_cmpi fun s₉ f₉ _ z₉ => WP.block_nil ?_
  have m₉ : s₉.mem = s₆.mem.writeW ((VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 132) (VG.X86.arg s₀ 3) := by
    rw [f₉.mem, w₈.mem, u₇.gpr, u₇.mem]
  have g₉ : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s₉.gpr r = s₀.gpr r := fun r ha hs hb => by
    rw [f₉.gpr, w₈.gpr, u₇.other _ ha, w₆.gpr, u₅.other _ ha, u₄.other _ hs, u₃.other _ hb, u₂.gpr, u₁.other _ ha]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₉.gpr, w₈.gpr, u₇.other _ (by decide), w₆.gpr, u₅.other _ (by decide), u₄.gpr]
  · rw [f₉.gpr, w₈.gpr, u₇.other _ (by decide), w₆.gpr, ebp₅]
  · rw [g₉ _ (by decide) (by decide) (by decide)]
  · rw [f₉.rd, w₈.rd, u₇.rd, w₆.rd, u₅.rd, u₄.rd, rd₃]
  · rw [f₉.wr, w₈.wr, u₇.wr, w₆.wr, u₅.wr, u₄.wr, wr₃]
  · rw [m₉, VG.Proof.CmacTripleDes.X86.readW_writeW_far _ _ _ (by decide) (by decide) (by decide), m₆, Mem.readW_writeW_self32]
    show VG.Proof.CmacTripleDes.X86.Dp s₀ = VG.Proof.CmacTripleDes.X86.Dp s₀ + BitVec.ofNat 32 0; rw [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]
  · rw [m₉, Mem.readW_writeW_self32, Nat.sub_zero]; simp [VG.Proof.CmacTripleDes.X86.N]
  · rw [m₉]; exact f₆.writeW (by simp) _ (c 132 (by decide) (by decide))
  · rw [List.take_zero, show Spec.Cmac.chain (VG.Proof.CmacTripleDes.X86.ciph s₀) (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) 8) [] =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) 8 from rfl]
    rw [m₉, m₆, bytesAt_frame (rs := [⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩])
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c 132 (by decide) (by decide)))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)]
    exact bytesAt_frame (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · rw [z₉, show s₈.gpr .eax = VG.X86.arg s₀ 3 by rw [w₈.gpr, u₇.gpr],
      show ∀ x : BitVec 32, x - 0 = x from fun x => by simp,
      show VG.X86.arg s₀ 3 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.X86.N s₀) by simp [VG.Proof.CmacTripleDes.X86.N], Wp.ofNat_beq_zero hN]

theorem mid_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.UPre s₀) {s₁ : State} (h : VG.Proof.CmacTripleDes.X86.LInv s₀ 0 s₁) (hz : s₁.zf = some (decide (VG.Proof.CmacTripleDes.X86.N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop updBody .ne)) s₁ (VG.Proof.CmacTripleDes.X86.LInv s₀ (VG.Proof.CmacTripleDes.X86.N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (VG.Proof.CmacTripleDes.X86.N s₀ = 0)) := by rw [VG.Proof.CmacTripleDes.X86.eval_e', hz]
  by_cases hn : VG.Proof.CmacTripleDes.X86.N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact VG.Proof.CmacTripleDes.X86.loop_ok hp (by omega) h

/-- What changes is apart from the return address and the saved registers. -/
theorem UPre.ret_kept {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.UPre s₀) {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.X86.chg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.S s₀)) m) :
    m.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
  rw [hf.readW (r := VG.Proof.CmacTripleDes.X86.retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
  · exact (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.S s₀)).readW (r := VG.Proof.CmacTripleDes.X86.retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))

theorem epilogue_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.UPre s₀) {s₂ : State} (h₂ : VG.Proof.CmacTripleDes.X86.LInv s₀ (VG.Proof.CmacTripleDes.X86.N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hsc := hp.scr_fit
  refine WP.mono (VG.Proof.CmacTripleDes.X86.restore_ok h₂.ebp (by omega) (fun d h₁ h₂' => ?_) (VG.Proof.CmacTripleDes.X86.saved_of fun d h₁ h₂' => ?_))
    fun s' r' => ⟨VG.Proof.CmacTripleDes.X86.restored r' h₂.esp (by rw [r'.mem]; exact hp.ret_kept h₂.frame), ?_⟩
  · rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  · refine h₂.frame.readW (r := ⟨(VG.Proof.CmacTripleDes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.st_scr.sub_right (Offset.sub_base _ (by omega))).symm
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (d := d) (e := 128) (by omega) (by omega) (by omega)
  · show Spec.Aes.bytesAt s'.mem ((VG.Proof.CmacTripleDes.X86.St s₀).setWidth 64) 8 = Spec.Cmac.chain (VG.Proof.CmacTripleDes.X86.ciph s₀) _ (VG.Proof.CmacTripleDes.X86.blks s₀)
    rw [r'.mem, h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp {s₀ : State} (h0 : updateX86.pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.mid_wp hp h₁ z₁) fun _ h₂ => VG.Proof.CmacTripleDes.X86.epilogue_wp hp h₂))

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Keys`. -/
section

/-!
# DES's key schedule on x86 (32-bit)

Untrusted: everything here is checked by Lean.

`roundKeys` only moves bits of the key at `[esi]` (its high word, then its
low word) to the round keys' words it stores at `[edi]`: the kernel checks it
over the lane domain (`roundKeys_check`, `linear_ok`), and
`getLsbD_expandDesKey` says the bits are the specification's.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86
  VG.Proof.CmacTripleDes

/-- The round keys' words at `edi`, and the key's two words at `esi`. -/
def kCfg : Cfg := { base := .edi, slots := 32, ext := .esi, exts := 2 }

/-- Bit `q` of word `w` (0 low, 1 high) of round key `j`: bit `rkSrc j (32 w + q)`
of the key. -/
def rkG (k q : Nat) : List Nat :=
  if q < (if k % 2 = 0 then 32 else 16) then [VG.Proof.CmacTripleDes.X86.xAtom (rkSrc (k / 2) (32 * (k % 2) + q))] else []

theorem rkG_lo {j q : Nat} (hq : q < 32) : VG.Proof.CmacTripleDes.X86.rkG (2 * j) q = [VG.Proof.CmacTripleDes.X86.xAtom (rkSrc j q)] := by
  simp [VG.Proof.CmacTripleDes.X86.rkG, hq, show 2 * j / 2 = j by omega]

theorem rkG_hi {j q : Nat} (hq : q < 16) : VG.Proof.CmacTripleDes.X86.rkG (2 * j + 1) q = [VG.Proof.CmacTripleDes.X86.xAtom (rkSrc j (32 + q))] := by
  simp [VG.Proof.CmacTripleDes.X86.rkG, hq, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]

theorem rkG_hi0 {j q : Nat} (hq : 16 ≤ q) : VG.Proof.CmacTripleDes.X86.rkG (2 * j + 1) q = [] := by
  simp [VG.Proof.CmacTripleDes.X86.rkG, show (2 * j + 1) % 2 = 1 by omega, show ¬ q < 16 by omega]

/-- Every round key's words. -/
def kOuts : List (Nat × (Nat → List Nat)) := (List.range 32).map fun k => (k, VG.Proof.CmacTripleDes.X86.rkG k)

theorem roundKeys_check :
    VG.X86.Straight.check (lanes 32 6) VG.Proof.CmacTripleDes.X86.kCfg (linExt 0) roundKeys (linEnv []) (linPost kCfg.slots 6 VG.Proof.CmacTripleDes.X86.kOuts) = true := by
  rw [VG.Proof.CmacTripleDes.X86.roundKeys_eq]; lit_decide

theorem rkSrc_lt : ∀ j < 16, ∀ q < 48, rkSrc j q < 64 := by lit_decide

/-- The registers `roundKeys` keeps. -/
def kKept : List Reg := [.eax, .edx, .esi, .edi, .ebp, .esp]

theorem roundKeys_kept : kKept.all (fun r => roundKeys.all fun i => i.dst != some r) = true := by
  rw [VG.Proof.CmacTripleDes.X86.roundKeys_eq]; lit_decide

/-- The DES key at `esi`: its high word, then its low word. -/
abbrev desKey (s : State) : BitVec 64 :=
  s.mem.readW (wordAddr (s.gpr .esi) 0) 32 ++ s.mem.readW (wordAddr (s.gpr .esi) 1) 32

/-- The round keys of the DES key at `esi`, in `[edi + 8 j]` and `[edi + 8 j + 4]`. -/
theorem roundKeys_ok {s : State} (hok : Ok VG.Proof.CmacTripleDes.X86.kCfg s) :
    ∃ s', runBlock isa roundKeys s = some s' ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .edi) (2 * j + 1)) 32).setWidth 16 ++
          s'.mem.readW (wordAddr (s.gpr .edi) (2 * j)) 32 =
        (Spec.TripleDes.expandDesKey (VG.Proof.CmacTripleDes.X86.desKey s)).getD j 0) ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .edi) (2 * j + 1)) 32) >>> 16 = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86.kKept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.X86.kCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.mem.readW (wordAddr (s.gpr .esi) 0) 32
    else s.mem.readW (wordAddr (s.gpr .esi) 1) 32
  obtain ⟨s', hs', hout, rd, wr, keep, fr⟩ := linear_ok VG.Proof.CmacTripleDes.X86.roundKeys_check hok W (fun j i h => by simp at h)
    (fun j hj => by
      simp only [VG.Proof.CmacTripleDes.X86.kCfg] at hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact ⟨by decide, rfl⟩
      · exact ⟨by decide, rfl⟩)
  have hw : ∀ k < 32, ∀ q < 32, (s'.mem.readW (wordAddr (s.gpr .edi) k) 32).getLsbD q = xorBits W (VG.Proof.CmacTripleDes.X86.rkG k q) :=
    fun k hk q hq => hout k (VG.Proof.CmacTripleDes.X86.rkG k) (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩) q hq
  have hx : W 0 ++ W 1 = VG.Proof.CmacTripleDes.X86.desKey s := rfl
  refine ⟨s', hs', fun j hj => ?_, fun j hj => ?_, rd, wr,
    fun r hr => keep _ (List.all_eq_true.mp VG.Proof.CmacTripleDes.X86.roundKeys_kept r hr), fr⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [BitVec.getLsbD_append, getLsbD_expandDesKey _ hj hq]
    have hs := VG.Proof.CmacTripleDes.X86.rkSrc_lt j hj q hq
    by_cases h32 : q < 32
    · rw [ite_eq_left h32, hw (2 * j) (by omega) q h32, VG.Proof.CmacTripleDes.X86.rkG_lo h32, xorBits_cons, xorBits_nil,
        Bool.xor_false, VG.Proof.CmacTripleDes.X86.bit_xAtom W hs, hx]
    · rw [ite_eq_right h32, BitVec.getLsbD_setWidth, decide_eq_true (by omega : q - 32 < 16), Bool.true_and,
        hw (2 * j + 1) (by omega) (q - 32) (by omega), VG.Proof.CmacTripleDes.X86.rkG_hi (by omega), show 32 + (q - 32) = q by omega,
        xorBits_cons, xorBits_nil, Bool.xor_false, VG.Proof.CmacTripleDes.X86.bit_xAtom W hs, hx]
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [BitVec.getLsbD_ushiftRight]
    by_cases hq' : 16 + q < 32
    · rw [hw (2 * j + 1) (by omega) (16 + q) hq', VG.Proof.CmacTripleDes.X86.rkG_hi0 (by omega)]
      simp
    · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
      simp

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Init`. -/
section

/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_init`

Untrusted: everything here is checked by Lean. `initPre` saves the
registers and stores the three DES keys, as the high and low words of
big-endian integers, at bytes `[100, 124)` of the scratch buffer; each
iteration of the loop then writes one DES key's sixteen round keys
(`KInv`); the zero block is encrypted with them and doubled twice, a word
at a time, into the subkeys.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86 VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_add wp_subi wp_sub wp_andi
  wp_or wp_cmpi wp_shr wp_bswap)
open VG.X86.Straight (wordAddr)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `xor d, r`. -/
theorem wp_xorr {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  Wp.wp_xor fun s' u => k s' ⟨u.gpr, u.other, u.mem, u.rd, u.wr⟩

end

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev K : BitVec 32 := VG.X86.arg s₀ 0
abbrev Kl : Nat := (VG.X86.arg s₀ 1).toNat
abbrev O : BitVec 32 := VG.X86.arg s₀ 2
abbrev Sc : BitVec 32 := VG.X86.arg s₀ 3

abbrev ikeyR : Region := ⟨(VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64, VG.Proof.CmacTripleDes.X86.Kl s₀⟩
abbrev outR : Region := ⟨(VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64, 400⟩
abbrev iscrR : Region := ⟨(VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64, 640⟩
abbrev iargsR : Region := ⟨argAddr s₀ 0, 16⟩

/-- The key's bytes. -/
abbrev keyB : List Byte := Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.Kl s₀)

/-- DES key `j`, as a big-endian integer. -/
abbrev kw (j : Nat) : BitVec 64 :=
  byteRev64 (s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) j)) 64)

/-- What the function changes after saving the registers. -/
abbrev ichg : List Region :=
  [⟨(VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64, 84⟩, ⟨(VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩, VG.Proof.CmacTripleDes.X86.outR s₀]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacTripleDes.X86.ikeyR s₀, VG.Proof.CmacTripleDes.X86.iargsR s₀]
  wr : s₀.wr = [VG.Proof.CmacTripleDes.X86.outR s₀, VG.Proof.CmacTripleDes.X86.iscrR s₀]
  key_out : (VG.Proof.CmacTripleDes.X86.ikeyR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.outR s₀)
  key_scr : (VG.Proof.CmacTripleDes.X86.ikeyR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.iscrR s₀)
  out_scr : (VG.Proof.CmacTripleDes.X86.outR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.iscrR s₀)
  args_out : (VG.Proof.CmacTripleDes.X86.iargsR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.outR s₀)
  args_scr : (VG.Proof.CmacTripleDes.X86.iargsR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.iscrR s₀)
  ret_out : (VG.Proof.CmacTripleDes.X86.retR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.outR s₀)
  ret_scr : (VG.Proof.CmacTripleDes.X86.retR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.iscrR s₀)
  key_fit : (VG.Proof.CmacTripleDes.X86.K s₀).toNat + VG.Proof.CmacTripleDes.X86.Kl s₀ ≤ 2 ^ 32
  out_fit : (VG.Proof.CmacTripleDes.X86.O s₀).toNat + 400 ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacTripleDes.X86.Sc s₀).toNat + 640 ≤ 2 ^ 32
  esp_fit : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32
  valid : VG.Proof.CmacTripleDes.X86.Kl s₀ = 16 ∨ VG.Proof.CmacTripleDes.X86.Kl s₀ = 24

theorem IPre.of {s₀ : State} (h : initX86.pre s₀) : VG.Proof.CmacTripleDes.X86.IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩

/-- After the round keys of `i` DES keys. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  ebp : s.gpr .ebp = VG.Proof.CmacTripleDes.X86.Sc s₀
  esi : s.gpr .esi = VG.Proof.CmacTripleDes.X86.Sc s₀ + BitVec.ofNat 32 (100 + 8 * i)
  edi : s.gpr .edi = VG.Proof.CmacTripleDes.X86.O s₀ + BitVec.ofNat 32 (128 * i)
  edx : s.gpr .edx = BitVec.ofNat 32 (3 - i)
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : ∀ j < 3, s.mem.readW ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 (100 + 8 * j)) 32 ++
    s.mem.readW ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 (104 + 8 * j)) 32 = VG.Proof.CmacTripleDes.X86.kw s₀ j
  sched : ∀ n < 16 * i, s.mem.readW ((VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (8 * n)) 64 =
    (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86.keyB s₀)).getD n 0
  frame : Frame [⟨(VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩, ⟨(VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64, 384⟩]
    (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.Sc s₀)) s.mem

/-! ## Regions -/

theorem keyOff_le {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.IPre s₀) {j : Nat} (hj : j < 3) : keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) j + 8 ≤ VG.Proof.CmacTripleDes.X86.Kl s₀ := by
  simp only [keyOff]; rcases hp.valid with h | h <;> rw [h] <;> split <;> omega

section
variable {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.IPre s₀)
include hp

theorem IPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.iscrR s₀) (by simp) (Offset.contains_base _ h (by have := hp.scr_fit; omega))

theorem IPre.inOut {d n : Nat} (h : d + n ≤ 400) (hn : 0 < n) :
    InRegions s₀.wr ((VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.outR s₀) (by simp) (Offset.contains_base _ h (by have := hp.out_fit; omega))

theorem IPre.inKey {d n : Nat} (h : d + n ≤ VG.Proof.CmacTripleDes.X86.Kl s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.ikeyR s₀) (by simp) (Offset.contains_base _ h (by have := hp.key_fit; omega))

theorem IPre.scrEa {s : State} (h : s.gpr .ebp = VG.Proof.CmacTripleDes.X86.Sc s₀) {d : Nat} (hd : d < 640) :
    s.ea (at_ .ebp d) = (VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [VG.Proof.CmacTripleDes.X86.ea_at', h]; exact addr_eq (by have := hp.scr_fit; omega)

theorem IPre.keyEa {s : State} (h : s.gpr .ecx = VG.Proof.CmacTripleDes.X86.K s₀) {d : Nat} (hd : d < VG.Proof.CmacTripleDes.X86.Kl s₀) :
    s.ea (at_ .ecx d) = (VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [VG.Proof.CmacTripleDes.X86.ea_at', h]; exact addr_eq (by have := hp.key_fit; omega)

theorem IPre.argAddr_eq {i : Nat} (hi : i < 4) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.esp_fit
  show addr (s₀.gpr .esp) (4 + 4 * i) = addr (s₀.gpr .esp) (4 + 4 * 0) + _
  rw [addr_eq (by omega), addr_eq (by omega), Offset.add_add, show 4 + 4 * 0 + 4 * i = 4 + 4 * i by omega]

theorem IPre.argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.argAddr_eq hi]
  exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.iargsR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))

/-- The arguments, unchanged outside the output and the scratch buffer. -/
theorem IPre.arg_eq {m : Mem} (hf : Frame [VG.Proof.CmacTripleDes.X86.outR s₀, VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have hsub : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.CmacTripleDes.X86.iargsR s₀) := by
    rw [hp.argAddr_eq hi]; exact Offset.sub_base _ (by omega)
  refine hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.args_out.sub_left hsub
  · exact hp.args_scr.sub_left hsub

/-- The key is unchanged while only the scratch buffer changes. -/
theorem IPre.keyRead {m : Mem} (hf : Frame [VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ VG.Proof.CmacTripleDes.X86.Kl s₀) :
    m.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨(VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ hd)) (by decide)

omit hp in
/-- DES key `j` from its two words. -/
theorem kw_eq (j : Nat) :
    bswap (s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) j)) 32) ++
      bswap (s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) j + 4)) 32) = VG.Proof.CmacTripleDes.X86.kw s₀ j := by
  rw [VG.Proof.CmacTripleDes.X86.bswap_eq, VG.Proof.CmacTripleDes.X86.bswap_eq, byteRev32_append, VG.Proof.CmacTripleDes.X86.kw, readW64_split, Offset.add_add]

end

/-! ## The prologue -/

/-- A word of the key, byte-reversed, to the scratch buffer. -/
theorem keyWord_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.IPre s₀) {s : State} {d o : Nat} {rest : List Instr} {Q : State → Prop}
    (hd : d + 4 ≤ VG.Proof.CmacTripleDes.X86.Kl s₀) (ho : o + 4 ≤ 640)
    (hcx : s.gpr .ecx = VG.Proof.CmacTripleDes.X86.K s₀) (hbp : s.gpr .ebp = VG.Proof.CmacTripleDes.X86.Sc s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem s.mem)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 o)
        (bswap (s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 d) 32)) → WP isa (.block rest) s' Q) :
    WP isa (.block (keyWord d o ++ rest)) s Q := by
  show WP isa (.block (.mov .eax (.mem (at_ .ecx d)) :: .bswap .eax :: .store (at_ .ebp o) .eax :: rest)) s Q
  refine wp_movm (hp.keyEa hcx (by omega)) (by rw [hrd, hwr]; exact hp.inKey hd (by decide))
    fun s₁ u₁ => wp_bswap fun s₂ u₂ => ?_
  refine wp_store (hp.scrEa (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hbp]) (by omega))
    (by rw [u₂.wr, u₁.wr, hwr]; exact hp.inScr ho (by decide)) fun s₃ w₃ => k s₃ (fun r hr => ?_)
    (by rw [w₃.rd, u₂.rd, u₁.rd]) (by rw [w₃.wr, u₂.wr, u₁.wr]) ?_
  · rw [w₃.gpr, u₂.other _ hr, u₁.other _ hr]
  · rw [w₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, hp.keyRead hf hd]

/-- A byte offset of the scratch buffer in its bytes `[100, 124)`. -/
theorem keysC {S : Addr} {d : Nat} (h₁ : 100 ≤ d) (h₂ : d + 4 ≤ 124) :
    (⟨S + BitVec.ofNat 64 100, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (32 / 8) := by
  rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 100 + BitVec.ofNat 64 (d - 100) from
    (Offset.add_add_eq _ (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

theorem initPre_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.IPre s₀) : WP isa initPre s₀ (VG.Proof.CmacTripleDes.X86.KInv s₀ 0) := by
  have sf := hp.scr_fit
  have sf' : (VG.X86.arg s₀ 3).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
  have kl : 16 ≤ VG.Proof.CmacTripleDes.X86.Kl s₀ := by rcases hp.valid with h | h <;> omega
  rw [show initPre = .seq (.block (.mov .eax (stk 16) :: (Spill.saveCode .eax saved ++
      (.mov .ebp (.reg .eax) :: .mov .ecx (stk 4) :: (keyWord 0 100 ++ (keyWord 4 104 ++ (keyWord 8 108 ++
        (keyWord 12 112 ++ ([.mov .eax (stk 8), .alu .cmp .eax (.imm 16)] : List Instr)))))))))
      (.seq (.ite .e (.block [.mov .eax (.mem (at_ .ecx 0)), .mov .edx (.mem (at_ .ecx 4))])
          (.block [.mov .eax (.mem (at_ .ecx 16)), .mov .edx (.mem (at_ .ecx 20))]))
        (.block [.bswap .eax, .bswap .edx, .store (at_ .ebp 116) .eax, .store (at_ .ebp 120) .edx,
          .mov .esi (.reg .ebp), .alu .add .esi (.imm 100), .mov .edi (stk 12), .mov .edx (.imm 3)])) from rfl]
  refine WP.seq ?_
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 3 rfl rfl (hp.argIn rfl rfl (by decide)) rfl fun s₁ u₁ => ?_
  refine Spill.save_ofNat_ok saved VG.Proof.CmacTripleDes.X86.saved_fits (by rw [u₁.gpr]; exact VG.Proof.CmacTripleDes.X86.fits_of hp.scr_fit (by decide))
    (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := VG.Proof.CmacTripleDes.X86.saved_bound p hp'
    rw [u₁.gpr, u₁.wr]
    exact hp.inScr (by omega) (by decide)
  have hm₂ : s₂.mem = VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.Sc s₀) := by
    rw [u₂.mem, u₁.mem, u₁.gpr, VG.Proof.CmacTripleDes.X86.savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (VG.Proof.CmacTripleDes.X86.saved_ne_eax p hp')
  have sv : Frame [VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.Sc s₀)) := (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.Sc s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.CmacTripleDes.X86.iscrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  have toOS : ∀ {m}, Frame [VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem m → Frame [VG.Proof.CmacTripleDes.X86.outR s₀, VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem m := fun hf =>
    hf.mono (by simp)
  have scrC : ∀ d, d + 4 ≤ 640 → (VG.Proof.CmacTripleDes.X86.iscrR s₀).Contains ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega)
  refine wp_mov fun s₃ u₃ => ?_
  have e₃ : s₃.gpr .ebp = VG.Proof.CmacTripleDes.X86.Sc s₀ := by rw [u₃.gpr, u₂.gpr, u₁.gpr]
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 0 rfl esp₃ (hp.argIn rd₃ wr₃ (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_eq (toOS sv) (by decide)) fun s₄ u₄ => ?_
  have cx₄ : s₄.gpr .ecx = VG.Proof.CmacTripleDes.X86.K s₀ := u₄.gpr
  have bp₄ : s₄.gpr .ebp = VG.Proof.CmacTripleDes.X86.Sc s₀ := by rw [u₄.other _ (by decide), e₃]
  -- The four words of the first two DES keys.
  refine VG.Proof.CmacTripleDes.X86.keyWord_wp hp (by omega) (by decide) cx₄ bp₄ (by rw [u₄.rd, rd₃]) (by rw [u₄.wr, wr₃])
    (by rw [u₄.mem, u₃.mem, hm₂]; exact sv) fun s₅ g₅ rd₅ wr₅ m₅ => ?_
  have F₅ : Frame [VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem s₅.mem := by
    rw [m₅, u₄.mem, u₃.mem, hm₂]; exact sv.writeW (List.mem_singleton_self _) _ (scrC 100 (by decide))
  refine VG.Proof.CmacTripleDes.X86.keyWord_wp hp (by omega) (by decide) (by rw [g₅ _ (by decide), cx₄]) (by rw [g₅ _ (by decide), bp₄])
    (by rw [rd₅, u₄.rd, rd₃]) (by rw [wr₅, u₄.wr, wr₃]) F₅ fun s₆ g₆ rd₆ wr₆ m₆ => ?_
  have F₆ : Frame [VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem s₆.mem := by
    rw [m₆]; exact F₅.writeW (List.mem_singleton_self _) _ (scrC 104 (by decide))
  refine VG.Proof.CmacTripleDes.X86.keyWord_wp hp (by omega) (by decide) (by rw [g₆ _ (by decide), g₅ _ (by decide), cx₄])
    (by rw [g₆ _ (by decide), g₅ _ (by decide), bp₄]) (by rw [rd₆, rd₅, u₄.rd, rd₃])
    (by rw [wr₆, wr₅, u₄.wr, wr₃]) F₆ fun s₇ g₇ rd₇ wr₇ m₇ => ?_
  have F₇ : Frame [VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem s₇.mem := by
    rw [m₇]; exact F₆.writeW (List.mem_singleton_self _) _ (scrC 108 (by decide))
  refine VG.Proof.CmacTripleDes.X86.keyWord_wp hp (by omega) (by decide) (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), cx₄])
    (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), bp₄]) (by rw [rd₇, rd₆, rd₅, u₄.rd, rd₃])
    (by rw [wr₇, wr₆, wr₅, u₄.wr, wr₃]) F₇ fun s₈ g₈ rd₈ wr₈ m₈ => ?_
  have F₈ : Frame [VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem s₈.mem := by
    rw [m₈]; exact F₇.writeW (List.mem_singleton_self _) _ (scrC 112 (by decide))
  have g₈' : ∀ r, r ≠ .eax → s₈.gpr r = s₄.gpr r := fun r h => by rw [g₈ r h, g₇ r h, g₆ r h, g₅ r h]
  have rd₈' : s₈.rd = s₀.rd := by rw [rd₈, rd₇, rd₆, rd₅, u₄.rd, rd₃]
  have wr₈' : s₈.wr = s₀.wr := by rw [wr₈, wr₇, wr₆, wr₅, u₄.wr, wr₃]
  have esp₈ : s₈.gpr .esp = s₀.gpr .esp := by rw [g₈' _ (by decide), u₄.other _ (by decide), esp₃]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 1 rfl esp₈ (hp.argIn rd₈' wr₈' (by decide)) (hp.arg_eq (toOS F₈) (by decide))
    fun s₉ u₉ => wp_cmpi fun s₁₀ f₁₀ _ z₁₀ => WP.block_nil ?_
  have ev : isa.eval .e s₁₀ = some (decide (VG.Proof.CmacTripleDes.X86.Kl s₀ = 16)) := by
    rw [VG.Proof.CmacTripleDes.X86.eval_e', z₁₀, u₉.gpr, show VG.X86.arg s₀ 1 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.X86.Kl s₀) by simp [VG.Proof.CmacTripleDes.X86.Kl],
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, MdStream.X86.sub_beq (VG.X86.arg s₀ 1).isLt (by decide)]
  have g₁₀ : ∀ r, r ≠ .eax → s₁₀.gpr r = s₄.gpr r := fun r h => by rw [f₁₀.gpr, u₉.other _ h, g₈' r h]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [f₁₀.rd, u₉.rd, rd₈']
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [f₁₀.wr, u₉.wr, wr₈']
  have mem₁₀ : s₁₀.mem = s₈.mem := by rw [f₁₀.mem, u₉.mem]
  -- The third DES key.
  have third : ∀ d, d + 8 ≤ VG.Proof.CmacTripleDes.X86.Kl s₀ →
      WP isa (.block [.mov .eax (.mem (at_ .ecx d)), .mov .edx (.mem (at_ .ecx (d + 4)))]) s₁₀ fun s₁₁ =>
        s₁₁.gpr .eax = s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 d) 32 ∧
        s₁₁.gpr .edx = s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 (d + 4)) 32 ∧
        (∀ r, r ≠ .eax → r ≠ .edx → s₁₁.gpr r = s₁₀.gpr r) ∧ s₁₁.mem = s₈.mem ∧ s₁₁.rd = s₀.rd ∧
        s₁₁.wr = s₀.wr := by
    intro d hd
    have cx : s₁₀.gpr .ecx = VG.Proof.CmacTripleDes.X86.K s₀ := by rw [g₁₀ _ (by decide), cx₄]
    refine wp_movm (hp.keyEa cx (by omega)) (by rw [rd₁₀, wr₁₀]; exact hp.inKey (by omega) (by decide))
      fun s₁₁ u₁₁ => ?_
    refine wp_movm (hp.keyEa (by rw [u₁₁.other _ (by decide), cx]) (by omega))
      (by rw [u₁₁.rd, u₁₁.wr, rd₁₀, wr₁₀]; exact hp.inKey (by omega) (by decide))
      fun s₁₂ u₁₂ => WP.block_nil ⟨?_, ?_, fun r h4 h5 => ?_, ?_, ?_, ?_⟩
    · rw [u₁₂.other _ (by decide), u₁₁.gpr, mem₁₀, hp.keyRead F₈ (by omega)]
    · rw [u₁₂.gpr, u₁₁.mem, mem₁₀, hp.keyRead F₈ (by omega)]
    · rw [u₁₂.other _ h5, u₁₁.other _ h4]
    · rw [u₁₂.mem, u₁₁.mem, mem₁₀]
    · rw [u₁₂.rd, u₁₁.rd, rd₁₀]
    · rw [u₁₂.wr, u₁₁.wr, wr₁₀]
  refine WP.seq (WP.mono (Q := fun (s₁₁ : State) =>
      s₁₁.gpr .eax = s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) 2)) 32 ∧
      s₁₁.gpr .edx = s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) 2 + 4)) 32 ∧
      (∀ r, r ≠ .eax → r ≠ .edx → s₁₁.gpr r = s₁₀.gpr r) ∧ s₁₁.mem = s₈.mem ∧ s₁₁.rd = s₀.rd ∧
      s₁₁.wr = s₀.wr) ?_ fun s₁₁ h₁₁ => ?_)
  · by_cases h16 : VG.Proof.CmacTripleDes.X86.Kl s₀ = 16
    · refine WP.ite true (by rw [ev]; simp [h16]) (fun _ => ?_) (fun h => by cases h)
      have := third 0 (by omega)
      rwa [show keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) 2 = 0 by simp [keyOff, h16]]
    · refine WP.ite false (by rw [ev]; simp [h16]) (fun h => by cases h) (fun _ => ?_)
      have h24 : VG.Proof.CmacTripleDes.X86.Kl s₀ = 24 := by rcases hp.valid with h | h <;> omega
      have := third 16 (by omega)
      rwa [show keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) 2 = 16 by simp [keyOff, h24]]
  obtain ⟨ax₁₁, dx₁₁, g₁₁, m₁₁, rd₁₁, wr₁₁⟩ := h₁₁
  have bp₁₁ : s₁₁.gpr .ebp = VG.Proof.CmacTripleDes.X86.Sc s₀ := by rw [g₁₁ _ (by decide) (by decide), g₁₀ _ (by decide), bp₄]
  refine wp_bswap fun s₁₂ u₁₂ => wp_bswap fun s₁₃ u₁₃ => ?_
  have bp₁₃ : s₁₃.gpr .ebp = VG.Proof.CmacTripleDes.X86.Sc s₀ := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), bp₁₁]
  refine wp_store (hp.scrEa bp₁₃ (by decide)) (by rw [u₁₃.wr, u₁₂.wr, wr₁₁]; exact hp.inScr (by decide) (by decide))
    fun s₁₄ w₁₄ => ?_
  refine wp_store (hp.scrEa (by rw [w₁₄.gpr, bp₁₃]) (by decide))
    (by rw [w₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁]; exact hp.inScr (by decide) (by decide)) fun s₁₅ w₁₅ => ?_
  refine wp_mov fun s₁₆ u₁₆ => wp_addi fun s₁₇ u₁₇ => ?_
  have esp₁₇ : s₁₇.gpr .esp = s₀.gpr .esp := by
    rw [u₁₇.other _ (by decide), u₁₆.other _ (by decide), w₁₅.gpr, w₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), g₁₁ _ (by decide) (by decide), g₁₀ _ (by decide), u₄.other _ (by decide), esp₃]
  have rd₁₇ : s₁₇.rd = s₀.rd := by rw [u₁₇.rd, u₁₆.rd, w₁₅.rd, w₁₄.rd, u₁₃.rd, u₁₂.rd, rd₁₁]
  have wr₁₇ : s₁₇.wr = s₀.wr := by rw [u₁₇.wr, u₁₆.wr, w₁₅.wr, w₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁]
  have mem₁₅ : s₁₅.mem = ((((((VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.Sc s₀)).writeW ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 100)
      (bswap (s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 0) 32))).writeW
      ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 104) (bswap (s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 4) 32))).writeW
      ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 108) (bswap (s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 8) 32))).writeW
      ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 112)
        (bswap (s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 12) 32))).writeW
      ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 116)
        (bswap (s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) 2)) 32))).writeW
      ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 120)
        (bswap (s₀.mem.readW ((VG.Proof.CmacTripleDes.X86.K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) 2 + 4)) 32)) := by
    rw [w₁₅.mem, w₁₄.mem, w₁₄.gpr, u₁₃.gpr, u₁₃.other .eax (by decide), u₁₂.gpr, u₁₃.mem, u₁₂.mem,
      u₁₂.other .edx (by decide), ax₁₁, dx₁₁, m₁₁, m₈, m₇, m₆, m₅, u₄.mem, u₃.mem, hm₂]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 2 rfl esp₁₇ (hp.argIn rd₁₇ wr₁₇ (by decide))
    (by
      rw [u₁₇.mem, u₁₆.mem, mem₁₅]
      refine hp.arg_eq (toOS ?_) (by decide)
      exact (((((sv.writeW (List.mem_singleton_self _) _ (scrC 100 (by decide))).writeW (List.mem_singleton_self _) _
        (scrC 104 (by decide))).writeW (List.mem_singleton_self _) _ (scrC 108 (by decide))).writeW
        (List.mem_singleton_self _) _ (scrC 112 (by decide))).writeW (List.mem_singleton_self _) _
        (scrC 116 (by decide))).writeW (List.mem_singleton_self _) _ (scrC 120 (by decide)))
    fun s₁₈ u₁₈ => wp_movi fun s₁₉ u₁₉ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => absurd hn (by omega), ?_⟩
  · rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.other _ (by decide),
      w₁₅.gpr, w₁₄.gpr, bp₁₃]
  · rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr, w₁₅.gpr, w₁₄.gpr, bp₁₃]; rfl
  · rw [u₁₉.other _ (by decide), u₁₈.gpr, VG.Proof.CmacTripleDes.X86.add_zero32]
  · rw [u₁₉.gpr]; rfl
  · rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), esp₁₇]
  · rw [u₁₉.rd, u₁₈.rd, rd₁₇]
  · rw [u₁₉.wr, u₁₈.wr, wr₁₇]
  · rw [u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, mem₁₅, ← VG.Proof.CmacTripleDes.X86.kw_eq (s₀ := s₀) j]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [show keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) 0 = 0 by simp [keyOff]]
      simp (disch := decide) only [VG.Proof.CmacTripleDes.X86.readW_writeW_far, Mem.readW_writeW_self32]
    · rw [show keyOff (VG.Proof.CmacTripleDes.X86.Kl s₀) 1 = 8 by simp [keyOff]]
      simp (disch := decide) only [VG.Proof.CmacTripleDes.X86.readW_writeW_far, Mem.readW_writeW_self32]
    · simp (disch := decide) only [VG.Proof.CmacTripleDes.X86.readW_writeW_far, Mem.readW_writeW_self32]
  · rw [u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, mem₁₅]
    have c : ∀ d, 100 ≤ d → d + 4 ≤ 124 → (⟨(VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩ : Region).Contains
        ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => VG.Proof.CmacTripleDes.X86.keysC h₁ h₂
    exact ((((((Frame.refl _ _).writeW (by simp) _ (c 100 (by decide) (by decide))).writeW (by simp) _
      (c 104 (by decide) (by decide))).writeW (by simp) _ (c 108 (by decide) (by decide))).writeW (by simp) _
      (c 112 (by decide) (by decide))).writeW (by simp) _ (c 116 (by decide) (by decide))).writeW (by simp) _
      (c 120 (by decide) (by decide))

/-! ## The round keys -/

theorem keyStep_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.IPre s₀) {i : Nat} (hi : i < 3) {s : State} (h : VG.Proof.CmacTripleDes.X86.KInv s₀ i s) :
    WP isa (.block keysBody) s fun s' => VG.Proof.CmacTripleDes.X86.KInv s₀ (i + 1) s' ∧ s'.zf = some (decide (3 - (i + 1) = 0)) := by
  have sf := hp.scr_fit
  have of := hp.out_fit
  have oN : (VG.Proof.CmacTripleDes.X86.O s₀ + BitVec.ofNat 32 (128 * i)).toNat = (VG.Proof.CmacTripleDes.X86.O s₀).toNat + 128 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hok : Straight.Ok VG.Proof.CmacTripleDes.X86.kCfg s := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk j hj => ?_⟩
    · simp only [VG.Proof.CmacTripleDes.X86.kCfg] at hk
      rw [show kCfg.base = .edi from rfl, h.edi, h.wr, hp.wr]
      exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.outR s₀) (by simp) (VG.Proof.CmacTripleDes.X86.contains_w_off (by omega) (by omega))
    · simp only [VG.Proof.CmacTripleDes.X86.kCfg] at hk
      rw [show kCfg.ext = .esi from rfl, h.esi, h.rd, h.wr, hp.rd, hp.wr]
      exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.iscrR s₀) (by simp) (VG.Proof.CmacTripleDes.X86.contains_w_off (by omega) (by omega))
    · show (s.gpr .edi).toNat + 4 * 32 ≤ 2 ^ 32
      rw [h.edi, oN]; omega
    · simp only [VG.Proof.CmacTripleDes.X86.kCfg] at hk hj
      rw [show kCfg.base = .edi from rfl, show kCfg.ext = .esi from rfl, h.edi, h.esi]
      exact hp.out_scr.sep (VG.Proof.CmacTripleDes.X86.contains_w_off (by omega) (by omega)) (VG.Proof.CmacTripleDes.X86.contains_w_off (by omega) (by omega))
  obtain ⟨s₁, run₁, rk₁, hi₁, rd₁, wr₁, k₁, f₁⟩ := VG.Proof.CmacTripleDes.X86.roundKeys_ok hok
  rw [keysBody, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  refine wp_addi fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ z₄ => WP.block_nil ?_
  have kk : ∀ r ∈ VG.Proof.CmacTripleDes.X86.kKept, s₁.gpr r = s.gpr r := k₁
  have dk : VG.Proof.CmacTripleDes.X86.desKey s = VG.Proof.CmacTripleDes.X86.kw s₀ i := by
    rw [VG.Proof.CmacTripleDes.X86.desKey, h.esi, VG.Proof.CmacTripleDes.X86.wordAddr_off _ (by omega), VG.Proof.CmacTripleDes.X86.wordAddr_off _ (by omega), show 100 + 8 * i + 4 * 0 = 100 + 8 * i by omega,
      show 100 + 8 * i + 4 * 1 = 104 + 8 * i by omega, h.keys i hi]
  have slotR : Straight.slotRegion VG.Proof.CmacTripleDes.X86.kCfg s = ⟨(VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (128 * i), 128⟩ := by
    simp only [Straight.slotRegion]; rw [show kCfg.base = .edi from rfl, h.edi, ← VG.Proof.CmacTripleDes.X86.addr_zero, VG.Proof.CmacTripleDes.X86.addr_off2 (by omega), VG.Proof.CmacTripleDes.X86.add0]; rfl
  rw [slotR] at f₁
  have m₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  have dx₁ : s₁.gpr .edx = BitVec.ofNat 32 (3 - i) := by rw [kk _ (by simp [VG.Proof.CmacTripleDes.X86.kKept]), h.edx]
  have dec : BitVec.ofNat 32 (3 - i) - 1 = BitVec.ofNat 32 (3 - (i + 1)) := by
    rw [VG.Proof.CmacTripleDes.X86.ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  have wA : ∀ k < 32, wordAddr (s.gpr .edi) k = (VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (128 * i + 4 * k) :=
    fun k hk => by rw [h.edi, VG.Proof.CmacTripleDes.X86.wordAddr_off _ (by omega)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => ?_, ?_⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), kk _ (by simp [VG.Proof.CmacTripleDes.X86.kKept]), h.ebp]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), kk _ (by simp [VG.Proof.CmacTripleDes.X86.kKept]), h.esi,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_add, show 100 + 8 * i + 8 = 100 + 8 * (i + 1) by omega]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, kk _ (by simp [VG.Proof.CmacTripleDes.X86.kKept]), h.edi,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, Offset.add_add, show 128 * i + 128 = 128 * (i + 1) by omega]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), dx₁, dec]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), kk _ (by simp [VG.Proof.CmacTripleDes.X86.kKept]), h.esp]
  · rw [u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  · rw [m₄, ← h.keys j hj]
    have keep : ∀ d, 100 ≤ d → d + 4 ≤ 124 → s₁.mem.readW ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 =
        s.mem.readW ((VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 := fun d h₁ h₂ =>
      f₁.readW (r := ⟨(VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.out_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (Offset.sub_base _ (by omega)))
        (by decide)
    rw [keep _ (by omega) (by omega), keep _ (by omega) (by omega)]
  · rw [m₄]
    by_cases hn' : n < 16 * i
    · rw [← h.sched n hn', f₁.readW (r := ⟨(VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
    · obtain ⟨j, rfl⟩ : ∃ j, n = 16 * i + j := ⟨n - 16 * i, by omega⟩
      have hj : j < 16 := by omega
      have hk := VG.Proof.CmacTripleDes.X86.keyOff_le hp hi
      rw [readW64_split, Offset.add_add, show 8 * (16 * i + j) + 4 = 128 * i + 4 * (2 * j + 1) by omega,
        ← wA (2 * j + 1) (by omega), show 8 * (16 * i + j) = 128 * i + 4 * (2 * j) by omega, ← wA (2 * j) (by omega),
        append_of_hi _ _ (hi₁ j hj), rk₁ j hj, dk, VG.Proof.CmacTripleDes.X86.kw, expandKey_getD _ hi hj, Proof.Cmac.bytesAt_length,
        decode_bytesAt _ _ hk]
  · rw [m₄]
    exact h.frame.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨(VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64, 384⟩, by simp, Offset.sub_base _ (by omega)⟩)
  · rw [z₄, u₃.other _ (by decide), u₂.other _ (by decide), dx₁, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.X86.sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem keys_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.IPre s₀) {s : State} (h : VG.Proof.CmacTripleDes.X86.KInv s₀ 0 s) :
    WP isa (.loop (.block keysBody) .ne) s (VG.Proof.CmacTripleDes.X86.KInv s₀ 3) := by
  refine WP.loop (M := isa) (body := .block keysBody) (c := .ne) (Q := VG.Proof.CmacTripleDes.X86.KInv s₀ 3)
    (fun (n : Nat) (t : State) => ∃ i, n = 3 - i ∧ i < 3 ∧ VG.Proof.CmacTripleDes.X86.KInv s₀ i t) ?_ 3 s ⟨0, rfl, by decide, h⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.X86.keyStep_ok hp hi ht) fun t' ⟨h', z'⟩ => ?_
  by_cases hz : i + 1 = 3
  · left
    refine ⟨by rw [VG.Proof.CmacTripleDes.X86.eval_ne', z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [VG.Proof.CmacTripleDes.X86.eval_ne', z']; simp; omega, 3 - (i + 1), by omega, i + 1, rfl, by omega, h'⟩

/-! ## The subkeys -/

/-- `dbl d` doubles `eax:edx` and stores it, as bytes, at `[edi + d]`. -/
theorem dbl_wp {s : State} {d : Nat} {a : Addr} {rest : List Instr} {Q : State → Prop}
    (ha : addr (s.gpr .edi) d = a) (ha4 : addr (s.gpr .edi) (d + 4) = a + BitVec.ofNat 64 4)
    (w0 : InRegions s.wr a 4) (w4 : InRegions s.wr (a + BitVec.ofNat 64 4) 4)
    (k : ∀ s', s'.gpr .eax ++ s'.gpr .edx = dbl64 (s.gpr .eax ++ s.gpr .edx) →
      s'.mem = (s.mem.writeW a (bswap (s'.gpr .eax))).writeW (a + BitVec.ofNat 64 4) (bswap (s'.gpr .edx)) →
      (∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx] → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) :
    WP isa (.block (dbl d ++ rest)) s Q := by
  show WP isa (.block (.mov .ecx (.reg .eax) :: .shift .shr .ecx 31 :: .mov .ebx (.imm 0) ::
    .alu .sub .ebx (.reg .ecx) :: .alu .and .ebx (.imm 0x1b) :: .mov .ecx (.reg .edx) :: .shift .shr .ecx 31 ::
    .alu .add .eax (.reg .eax) :: .alu .or .eax (.reg .ecx) :: .alu .add .edx (.reg .edx) ::
    .alu .xor .edx (.reg .ebx) :: .mov .ecx (.reg .eax) :: .bswap .ecx :: .store (at_ .edi d) .ecx ::
    .mov .ecx (.reg .edx) :: .bswap .ecx :: .store (at_ .edi (d + 4)) .ecx :: rest)) s Q
  refine wp_mov fun s₁ u₁ => wp_shr (by decide) fun s₂ u₂ => wp_movi fun s₃ u₃ => wp_sub fun s₄ u₄ _ =>
    wp_andi fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_shr (by decide) fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_or fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => VG.Proof.CmacTripleDes.X86.wp_xorr fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ => wp_bswap fun s₁₃ u₁₃ => ?_
  have g₁₃ : ∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx] → s₁₃.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₃.other _ hr.2.2.1, u₁₂.other _ hr.2.2.1, u₁₁.other _ hr.2.2.2, u₁₀.other _ hr.2.2.2, u₉.other _ hr.1,
      u₈.other _ hr.1, u₇.other _ hr.2.2.1, u₆.other _ hr.2.2.1, u₅.other _ hr.2.1, u₄.other _ hr.2.1,
      u₃.other _ hr.2.1, u₂.other _ hr.2.2.1, u₁.other _ hr.2.2.1]
  have m₁₃ : s₁₃.mem = s.mem := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have wr₁₃ : s₁₃.wr = s.wr := by
    rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have di₁₃ : s₁₃.gpr .edi = s.gpr .edi := g₁₃ _ (by decide)
  refine wp_store (by rw [VG.Proof.CmacTripleDes.X86.ea_at', di₁₃, ha]) (by rw [wr₁₃]; exact w0) fun s₁₄ w₁₄ => ?_
  refine wp_mov fun s₁₅ u₁₅ => wp_bswap fun s₁₆ u₁₆ => ?_
  refine wp_store (by rw [VG.Proof.CmacTripleDes.X86.ea_at', u₁₆.other _ (by decide), u₁₅.other _ (by decide), w₁₄.gpr, di₁₃, ha4])
    (by rw [u₁₆.wr, u₁₅.wr, w₁₄.wr, wr₁₃]; exact w4) fun s₁₇ w₁₇ => ?_
  have r0f : s₁₇.gpr .eax = s₁₁.gpr .eax := by
    rw [w₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), w₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide)]
  have r1f : s₁₇.gpr .edx = s₁₁.gpr .edx := by
    rw [w₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), w₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide)]
  refine k s₁₇ ?_ ?_ (fun r hr => ?_) ?_ ?_
  · have a3 : s₁₀.gpr .ebx = ((0 : BitVec 32) - (s.gpr .eax >>> 31)) &&& (0x1b : BitVec 32) := by
      rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr]
    have a0 : s₁₁.gpr .eax = s.gpr .eax <<< 1 ||| s.gpr .edx >>> 31 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₈.other _ (by decide), u₇.gpr,
        u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide), add_self]
    have a1 : s₁₁.gpr .edx =
        s.gpr .edx <<< 1 ^^^ (((0 : BitVec 32) - (s.gpr .eax >>> 31)) &&& (0x1b : BitVec 32)) := by
      rw [u₁₁.gpr, a3, u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), add_self]
    rw [r0f, r1f, a0, a1, dbl_append]
  · rw [w₁₇.mem, u₁₆.mem, u₁₅.mem, w₁₄.mem, m₁₃, u₁₆.gpr, u₁₅.gpr, w₁₄.gpr, u₁₃.other .edx (by decide),
      u₁₃.gpr, u₁₂.gpr, r0f, r1f, u₁₂.other .edx (by decide)]
  · rw [w₁₇.gpr, u₁₆.other _ (by simp_all), u₁₅.other _ (by simp_all), w₁₄.gpr, g₁₃ r hr]
  · rw [w₁₇.rd, u₁₆.rd, u₁₅.rd, w₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd,
      u₃.rd, u₂.rd, u₁.rd]
  · rw [w₁₇.wr, u₁₆.wr, u₁₅.wr, w₁₄.wr, wr₁₃]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initX86.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initX86.post s₀ s' := by
  have hp := IPre.of h0
  have sf := hp.scr_fit
  have of := hp.out_fit
  have of' : (VG.X86.arg s₀ 2).toNat + 400 ≤ 2 ^ 32 := hp.out_fit
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.keys_ok hp h₁) fun s₂ h₂ => ?_)
  have F₂ : Frame [VG.Proof.CmacTripleDes.X86.outR s₀, VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem s₂.mem :=
    ((VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.Sc s₀)).sub fun r hr => ⟨VG.Proof.CmacTripleDes.X86.iscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
    (h₂.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.CmacTripleDes.X86.iscrR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacTripleDes.X86.outR s₀, by simp, Region.sub_prefix (by decide)⟩)
  -- The key schedule is in place.
  have hsch₂ : Spec.TripleDes.scheduleAt s₂.mem ((VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64) = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86.keyB s₀) := by
    apply Vector.ext
    intro n hn
    rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, h₂.sched n (by omega)]
  refine WP.seq ?_
  simp only [stk]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 2 rfl h₂.esp (hp.argIn h₂.rd h₂.wr (by decide)) (hp.arg_eq F₂ (by decide))
    fun s₃ u₃ => wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => WP.block_nil ?_
  have g₅ : ∀ r, r ∉ [Reg.eax, .edx, .esi] → s₅.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.1, u₄.other _ hr.1, u₃.other _ hr.2.2]
  have esi₅ : s₅.gpr .esi = VG.Proof.CmacTripleDes.X86.O s₀ := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have ebp₅ : s₅.gpr .ebp = VG.Proof.CmacTripleDes.X86.Sc s₀ := by rw [g₅ _ (by decide), h₂.ebp]
  have ax₅ : s₅.gpr .eax ++ s₅.gpr .edx = (0 : BitVec 64) := by rw [u₅.gpr, u₅.other _ (by decide), u₄.gpr]; rfl
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, h₂.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, h₂.wr]
  have hsch₅ : VG.Proof.CmacTripleDes.X86.sch s₅ = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86.keyB s₀) := by
    show Spec.TripleDes.scheduleAt s₅.mem ((s₅.gpr .esi).setWidth 64) = _
    rw [esi₅, m₅, hsch₂]
  have bp : VG.Proof.CmacTripleDes.X86.BlockPre s₅ :=
    { sched := ⟨400, by rw [esi₅, rd₅, wr₅, hp.rd, hp.wr]; simp, by decide, by rw [esi₅]; exact of⟩
      scr := ⟨640, by rw [ebp₅, wr₅, hp.wr]; simp, by decide, by rw [ebp₅]; exact sf⟩
      disj := by
        rw [esi₅, ebp₅]
        exact (hp.out_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.block_ok bp) fun s₆ ⟨same₆, esi₆, ax₆⟩ => ?_)
  rw [ax₅, hsch₅] at ax₆
  have xR₅ : VG.Proof.CmacTripleDes.X86.xR s₅ = ⟨(VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64, 84⟩ := by rw [VG.Proof.CmacTripleDes.X86.xR, ebp₅]
  have f₆ : Frame [⟨(VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64, 84⟩] s₂.mem s₆.mem := by rw [← m₅, ← xR₅]; exact same₆.frame
  have F₆ : Frame [VG.Proof.CmacTripleDes.X86.outR s₀, VG.Proof.CmacTripleDes.X86.iscrR s₀] s₀.mem s₆.mem :=
    F₂.trans (f₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacTripleDes.X86.iscrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  have esp₆ : s₆.gpr .esp = s₀.gpr .esp := by rw [same₆.esp, g₅ _ (by decide), h₂.esp]
  have ebp₆ : s₆.gpr .ebp = VG.Proof.CmacTripleDes.X86.Sc s₀ := by rw [same₆.ebp, ebp₅]
  have rd₆ : s₆.rd = s₀.rd := by rw [same₆.rd, rd₅]
  have wr₆ : s₆.wr = s₀.wr := by rw [same₆.wr, wr₅]
  show WP isa (.block (.mov .edi (stk 12) :: .alu .add .edi (.imm 384) :: (dbl 0 ++ (dbl 8 ++ restore)))) s₆ _
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 2 rfl esp₆ (hp.argIn rd₆ wr₆ (by decide)) (hp.arg_eq F₆ (by decide))
    fun s₇ u₇ => wp_addi fun s₈ u₈ => ?_
  have di₈ : s₈.gpr .edi = VG.Proof.CmacTripleDes.X86.O s₀ + 384 := by rw [u₈.gpr, u₇.gpr]
  have oA : ∀ d, d < 16 → addr (s₈.gpr .edi) d = (VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d) := fun d hd => by
    rw [di₈, show (384 : BitVec 32) = BitVec.ofNat 32 384 from rfl, VG.Proof.CmacTripleDes.X86.addr_off2 (by omega), Offset.add_add]
  have wO : ∀ d, d + 4 ≤ 16 → InRegions s₈.wr ((VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d)) 4 := fun d hd => by
    rw [u₈.wr, u₇.wr, wr₆]; exact hp.inOut (by omega) (by decide)
  have a4 : ∀ d, (VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d) + BitVec.ofNat 64 4 =
      (VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d + 4) := fun d => Offset.add_add _ _ _
  refine VG.Proof.CmacTripleDes.X86.dbl_wp (a := (VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (384 + 0)) (oA 0 (by decide))
    (by rw [oA 4 (by decide), a4]) (wO 0 (by decide)) (by rw [a4]; exact wO 4 (by decide))
    fun s₉ ax₉ m₉ g₉ rd₉ wr₉ => ?_
  refine VG.Proof.CmacTripleDes.X86.dbl_wp (a := (VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (384 + 8)) (by rw [g₉ _ (by decide), oA 8 (by decide)])
    (by rw [g₉ _ (by decide), oA 12 (by decide), a4]) (by rw [wr₉]; exact wO 8 (by decide))
    (by rw [wr₉, a4]; exact wO 12 (by decide)) fun s₁₀ ax₁₀ m₁₀ g₁₀ rd₁₀ wr₁₀ => ?_
  have ebp₁₀ : s₁₀.gpr .ebp = VG.Proof.CmacTripleDes.X86.Sc s₀ := by
    rw [g₁₀ _ (by decide), g₉ _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), ebp₆]
  have rdwr₁₀ : s₁₀.rd ++ s₁₀.wr = [VG.Proof.CmacTripleDes.X86.ikeyR s₀, VG.Proof.CmacTripleDes.X86.iargsR s₀, VG.Proof.CmacTripleDes.X86.outR s₀, VG.Proof.CmacTripleDes.X86.iscrR s₀] := by
    rw [rd₁₀, wr₁₀, rd₉, wr₉, u₈.rd, u₈.wr, u₇.rd, u₇.wr, rd₆, wr₆, hp.rd, hp.wr]; rfl
  -- What changed since the registers were saved.
  have oC : ∀ d, d + 4 ≤ 16 → (VG.Proof.CmacTripleDes.X86.outR s₀).Contains ((VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d)) (32 / 8) :=
    fun d hd => Offset.contains_base _ (by omega) (by omega)
  have F₁₀ : Frame (VG.Proof.CmacTripleDes.X86.ichg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.Sc s₀)) s₁₀.mem := by
    have F₂' : Frame (VG.Proof.CmacTripleDes.X86.ichg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.Sc s₀)) s₂.mem := h₂.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨(VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.CmacTripleDes.X86.outR s₀, by simp, Region.sub_prefix (by decide)⟩
    have F₆' : Frame (VG.Proof.CmacTripleDes.X86.ichg s₀) (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.Sc s₀)) s₆.mem := F₂'.trans (f₆.mono fun r hr => by simp at hr; simp [hr])
    rw [m₁₀, m₉, u₈.mem, u₇.mem, a4, a4]
    exact (((F₆'.writeW (by simp) _ (oC 0 (by decide))).writeW (by simp) _ (oC 4 (by decide))).writeW (by simp) _
      (oC 8 (by decide))).writeW (by simp) _ (oC 12 (by decide))
  refine WP.mono (VG.Proof.CmacTripleDes.X86.restore_ok ebp₁₀ (by omega) (fun d h₁' h₂' => by
      rw [rdwr₁₀]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.iscrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
      (VG.Proof.CmacTripleDes.X86.saved_of (S := VG.Proof.CmacTripleDes.X86.Sc s₀) fun d h₁' h₂' => ?_))
    fun s' r' => ⟨VG.Proof.CmacTripleDes.X86.restored r' ?_ ?_, ?_, ?_⟩
  · refine F₁₀.readW (r := ⟨(VG.Proof.CmacTripleDes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hp.out_scr.sub_right (Offset.sub_base _ (by omega))).symm
  · rw [g₁₀ _ (by decide), g₉ _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), esp₆]
  · rw [r'.mem, F₁₀.readW (r := VG.Proof.CmacTripleDes.X86.retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.Sc s₀)).readW (r := VG.Proof.CmacTripleDes.X86.retR s₀) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))
      · exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))
      · exact hp.ret_out
  -- The key schedule.
  · show Spec.TripleDes.scheduleAt s'.mem ((VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64) = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86.keyB s₀)
    rw [r'.mem, ← hsch₂]
    refine VG.Proof.CmacTripleDes.X86.scheduleAt_frame (rs := [VG.Proof.CmacTripleDes.X86.iscrR s₀, ⟨(VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 384, 16⟩]) ?_ fun r hr => ?_
    · have c : ∀ d, d + 4 ≤ 16 → (⟨(VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 384, 16⟩ : Region).Contains
          ((VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d)) (32 / 8) := fun d hd => by
        rw [← Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
      rw [m₁₀, m₉, u₈.mem, u₇.mem, a4, a4]
      exact ((((f₆.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.CmacTripleDes.X86.iscrR s₀, by simp, Region.sub_prefix (by decide)⟩).writeW (by simp) _ (c 0 (by decide))).writeW
        (by simp) _ (c 4 (by decide))).writeW (by simp) _ (c 8 (by decide))).writeW (by simp) _ (c 12 (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.out_scr.sub_left (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by omega)
  -- The subkeys.
  · show Spec.Aes.bytesAt s'.mem ((VG.Proof.CmacTripleDes.X86.O s₀).setWidth 64 + BitVec.ofNat 64 384) 16 =
      (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86.keyB s₀))) 8).1 ++
        (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86.keyB s₀))) 8).2
    rw [subkeys_tdes, r'.mem, bytesAt_split, ← le8_readW, ← le8_readW, readW64_split, readW64_split, m₁₀, m₉, u₈.mem,
      u₇.mem]
    simp (disch := decide) only [Offset.add_add, VG.Proof.CmacTripleDes.X86.readW_writeW_far, Mem.readW_writeW_self32]
    rw [VG.Proof.CmacTripleDes.X86.bswap_eq, VG.Proof.CmacTripleDes.X86.bswap_eq, VG.Proof.CmacTripleDes.X86.bswap_eq, VG.Proof.CmacTripleDes.X86.bswap_eq, byteRev32_append, byteRev32_append, ax₁₀, ax₉,
      u₈.other .eax (by decide), u₈.other .edx (by decide), u₇.other .eax (by decide), u₇.other .edx (by decide), ax₆]

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize`. -/
section

/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_finalize`, up to the last block

Untrusted: everything here is checked by Lean. After saving the registers,
the function forms the last block `Mₙ` (SP 800-38B §6.2 step 4) in
`eax:edx`, as little-endian words (`BPost`): `Mₙ* ⊕ K1` for a complete block
(`full_wp`), else `Mₙ*` copied a byte at a time onto zeros at bytes
`[136, 144)` of the scratch buffer, `0x80` after it, and XORed with `K2`
(`partial_wp`).
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86 VG.Proof.CmacTripleDes VG.Proof.Cmac VG.WriteBytes
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_cmpi wp_bswap
  wp_movzx8 wp_store8)

section
variable (s₀ : State)

abbrev FW : BitVec 32 := VG.X86.arg s₀ 0
abbrev FSt : BitVec 32 := VG.X86.arg s₀ 1
abbrev FP : BitVec 32 := VG.X86.arg s₀ 2
abbrev FL : Nat := (VG.X86.arg s₀ 3).toNat
abbrev FS : BitVec 32 := VG.X86.arg s₀ 4

abbrev keyR : Region := ⟨(VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64, 400⟩
abbrev fstR : Region := ⟨(VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64, 8⟩
abbrev lastR : Region := ⟨(VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64, VG.Proof.CmacTripleDes.X86.FL s₀⟩
abbrev fscrR : Region := ⟨(VG.Proof.CmacTripleDes.X86.FS s₀).setWidth 64, 640⟩

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacTripleDes.X86.keyR s₀, VG.Proof.CmacTripleDes.X86.lastR s₀, VG.Proof.CmacTripleDes.X86.argsR s₀]
  wr : s₀.wr = [VG.Proof.CmacTripleDes.X86.fstR s₀, VG.Proof.CmacTripleDes.X86.fscrR s₀]
  key_st : (VG.Proof.CmacTripleDes.X86.keyR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.fstR s₀)
  key_scr : (VG.Proof.CmacTripleDes.X86.keyR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.fscrR s₀)
  last_st : (VG.Proof.CmacTripleDes.X86.lastR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.fstR s₀)
  last_scr : (VG.Proof.CmacTripleDes.X86.lastR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.fscrR s₀)
  st_scr : (VG.Proof.CmacTripleDes.X86.fstR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.fscrR s₀)
  args_st : (VG.Proof.CmacTripleDes.X86.argsR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.fstR s₀)
  args_scr : (VG.Proof.CmacTripleDes.X86.argsR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.fscrR s₀)
  ret_st : (VG.Proof.CmacTripleDes.X86.retR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.fstR s₀)
  ret_scr : (VG.Proof.CmacTripleDes.X86.retR s₀).Disjoint (VG.Proof.CmacTripleDes.X86.fscrR s₀)
  key_fit : (VG.Proof.CmacTripleDes.X86.FW s₀).toNat + 400 ≤ 2 ^ 32
  st_fit : (VG.Proof.CmacTripleDes.X86.FSt s₀).toNat + 8 ≤ 2 ^ 32
  last_fit : (VG.Proof.CmacTripleDes.X86.FP s₀).toNat + VG.Proof.CmacTripleDes.X86.FL s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacTripleDes.X86.FS s₀).toNat + 640 ≤ 2 ^ 32
  esp_fit : (s₀.gpr .esp).toNat + 24 ≤ 2 ^ 32
  len : VG.Proof.CmacTripleDes.X86.FL s₀ ≤ 8

theorem FPre.of {s₀ : State} (h : finalizeX86.pre s₀) : VG.Proof.CmacTripleDes.X86.FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 384) 8)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m P L)

/-- The bytes where a partial last block is formed. -/
abbrev mnR (s₀ : State) : Region := ⟨(VG.Proof.CmacTripleDes.X86.FS s₀).setWidth 64 + BitVec.ofNat 64 136, 8⟩

/-- What the prologue leaves. -/
structure P1 (s₀ s : State) : Prop where
  ebp : s.gpr .ebp = VG.Proof.CmacTripleDes.X86.FS s₀
  esi : s.gpr .esi = VG.Proof.CmacTripleDes.X86.FW s₀
  esp : s.gpr .esp = s₀.gpr .esp
  mem : s.mem = VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the branch on the length leaves: `Mₙ` in `eax:edx`. -/
structure BPost (s₀ s : State) : Prop where
  ebp : s.gpr .ebp = VG.Proof.CmacTripleDes.X86.FS s₀
  esi : s.gpr .esi = VG.Proof.CmacTripleDes.X86.FW s₀
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacTripleDes.X86.mnR s₀] (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)) s.mem
  blk : le8 (s.gpr .edx ++ s.gpr .eax) = VG.Proof.CmacTripleDes.X86.mn s₀.mem ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64) ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.FL s₀)

section
variable {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.FPre s₀)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr ((VG.Proof.CmacTripleDes.X86.FS s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.fscrR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 400) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.keyR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ VG.Proof.CmacTripleDes.X86.FL s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.lastR s₀) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

theorem FPre.scrEa {s : State} (h : s.gpr .ebp = VG.Proof.CmacTripleDes.X86.FS s₀) {d : Nat} (hd : d < 640) :
    s.ea (at_ .ebp d) = (VG.Proof.CmacTripleDes.X86.FS s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [VG.Proof.CmacTripleDes.X86.ea_at', h]; exact addr_eq (by have := hp.scr_fit; omega)

theorem FPre.keyEa {s : State} (h : s.gpr .esi = VG.Proof.CmacTripleDes.X86.FW s₀) {d : Nat} (hd : d < 400) :
    addr (s.gpr .esi) d = (VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [h]; exact addr_eq (by have := hp.key_fit; omega)

theorem FPre.argAddr_eq {i : Nat} (hi : i < 5) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.esp_fit
  show addr (s₀.gpr .esp) (4 + 4 * i) = addr (s₀.gpr .esp) (4 + 4 * 0) + _
  rw [addr_eq (by omega), addr_eq (by omega), Offset.add_add, show 4 + 4 * 0 + 4 * i = 4 + 4 * i by omega]

theorem FPre.argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.argAddr_eq hi]
  exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.argsR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))

/-- The arguments, unchanged outside the state and the scratch buffer. -/
theorem FPre.arg_eq {rs : List Region} {m : Mem} (hf : Frame rs (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)) m)
    (hd : ∀ r ∈ rs, Region.Sub r (VG.Proof.CmacTripleDes.X86.fstR s₀) ∨ Region.Sub r (VG.Proof.CmacTripleDes.X86.fscrR s₀)) {i : Nat} (hi : i < 5) :
    m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have hsub : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.CmacTripleDes.X86.argsR s₀) := by
    rw [hp.argAddr_eq hi]; exact Offset.sub_base _ (by omega)
  rw [hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
  · exact (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)).readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.args_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))) (by decide)
  · rcases hd r hr with h | h
    · exact (hp.args_st.sub_left hsub).sub_right h
    · exact (hp.args_scr.sub_left hsub).sub_right h

/-- Saving the registers leaves the key unchanged. -/
theorem FPre.keyBytes {d : Nat} (h : d + 8 ≤ 400) :
    Spec.Aes.bytesAt (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)) ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 d) 8 =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 d) 8 :=
  bytesAt_frame (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (Offset.sub_base _ (by decide))) (by decide)

theorem FPre.lastBytes :
    Spec.Aes.bytesAt (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)) ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.FL s₀) =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.FL s₀) :=
  bytesAt_frame (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.last_scr.sub_right (Offset.sub_base _ (by decide))) (by have := hp.len; omega)

end

/-! ## The prologue -/

theorem fpre1_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.FPre s₀) :
    WP isa (.block (([.mov .eax (stk 20)] : List Instr) ++ save ++
      ([.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 16), .alu .cmp .eax (.imm 8)] : List Instr)))
      s₀ fun s => VG.Proof.CmacTripleDes.X86.P1 s₀ s ∧ s.zf = some (decide (VG.Proof.CmacTripleDes.X86.FL s₀ = 8)) := by
  have hsc := hp.scr_fit
  have hL := hp.len
  rw [show ([.mov .eax (stk 20)] : List Instr) ++ save ++
    ([.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 16), .alu .cmp .eax (.imm 8)] : List Instr) =
    .mov .eax (stk 20) :: (Spill.saveCode .eax saved ++
      ([.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 16), .alu .cmp .eax (.imm 8)] : List Instr)) from rfl]
  simp only [stk]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 4 rfl rfl (hp.argIn rfl rfl (by decide)) rfl fun s₁ u₁ => ?_
  refine Spill.save_ofNat_ok saved VG.Proof.CmacTripleDes.X86.saved_fits (by rw [u₁.gpr]; exact VG.Proof.CmacTripleDes.X86.fits_of hp.scr_fit (by decide))
    (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := VG.Proof.CmacTripleDes.X86.saved_bound p hp'
    have hsc' : (VG.X86.arg s₀ 4).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
    rw [u₁.gpr, u₁.wr]
    exact hp.inScr (by omega) (by decide)
  have hm₂ : s₂.mem = VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀) := by
    rw [u₂.mem, u₁.mem, u₁.gpr, VG.Proof.CmacTripleDes.X86.savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (VG.Proof.CmacTripleDes.X86.saved_ne_eax p hp')
  have nf : ∀ r ∈ ([] : List Region), Region.Sub r (VG.Proof.CmacTripleDes.X86.fstR s₀) ∨ Region.Sub r (VG.Proof.CmacTripleDes.X86.fscrR s₀) := fun _ h => by cases h
  refine wp_mov fun s₃ u₃ => ?_
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 0 rfl esp₃ (hp.argIn rd₃ wr₃ (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_eq (Frame.refl _ _) nf (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 3 rfl (by rw [u₄.other _ (by decide), esp₃])
    (hp.argIn (by rw [u₄.rd, rd₃]) (by rw [u₄.wr, wr₃]) (by decide))
    (by rw [u₄.mem, u₃.mem, hm₂]; exact hp.arg_eq (Frame.refl _ _) nf (by decide)) fun s₅ u₅ =>
    wp_cmpi fun s₆ f₆ _ z₆ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), esp₃]
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₆.rd, u₅.rd, u₄.rd, rd₃]
  · rw [f₆.wr, u₅.wr, u₄.wr, wr₃]
  · rw [z₆, u₅.gpr, show VG.X86.arg s₀ 3 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.X86.FL s₀) by simp [VG.Proof.CmacTripleDes.X86.FL],
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, MdStream.X86.sub_beq (by omega) (by decide)]

/-! ## A complete last block -/

theorem full_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.FPre s₀) (hL : VG.Proof.CmacTripleDes.X86.FL s₀ = 8) {s : State} (h : VG.Proof.CmacTripleDes.X86.P1 s₀ s) :
    WP isa (.block full) s (VG.Proof.CmacTripleDes.X86.BPost s₀) := by
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have nf : ∀ r ∈ ([] : List Region), Region.Sub r (VG.Proof.CmacTripleDes.X86.fstR s₀) ∨ Region.Sub r (VG.Proof.CmacTripleDes.X86.fscrR s₀) := fun _ h => by cases h
  have lf8 : (VG.X86.arg s₀ 2).toNat + 8 ≤ 2 ^ 32 := by have := hp.last_fit; rw [hL] at this; exact this
  simp only [full, stk]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 2 rfl h.esp (hp.argIn h.rd h.wr (by decide))
    (by rw [h.mem]; exact hp.arg_eq (Frame.refl _ _) nf (by decide)) fun s₁ u₁ => ?_
  refine wp_movm (a := (VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (by rw [VG.Proof.CmacTripleDes.X86.ea_at', u₁.gpr, VG.Proof.CmacTripleDes.X86.addr_zero])
    (by rw [u₁.rd, u₁.wr, hrw]; simpa [VG.Proof.CmacTripleDes.X86.add0] using hp.inLast (d := 0) (n := 4) (by omega) (by decide))
    fun s₂ u₂ => ?_
  refine wp_movm (a := (VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [VG.Proof.CmacTripleDes.X86.ea_at', u₂.other _ (by decide), u₁.gpr]; exact addr_eq (by omega))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.inLast (d := 4) (n := 4) (by omega) (by decide))
    fun s₃ u₃ => ?_
  have esi₃ : s₃.gpr .esi = VG.Proof.CmacTripleDes.X86.FW s₀ := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
  have k384 := hp.inKey (d := 384) (n := 4) (by decide) (by decide)
  have k388 := hp.inKey (d := 388) (n := 4) (by decide) (by decide)
  refine VG.Proof.CmacTripleDes.X86.wp_xorma (hp.keyEa (d := 384) esi₃ (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact k384) fun s₄ u₄ => ?_
  refine VG.Proof.CmacTripleDes.X86.wp_xorma (hp.keyEa (d := 388) (by rw [u₄.other _ (by decide), esi₃]) (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact k388)
    fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s₅.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.2, u₄.other _ hr.1, u₃.other _ hr.2.2, u₂.other _ hr.1, u₁.other _ hr.2.1]
  have mem : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [g _ (by decide), h.ebp], by rw [g _ (by decide), h.esi], by rw [g _ (by decide), h.esp],
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [mem, h.mem]; exact Frame.refl _ _, ?_⟩
  rw [u₅.gpr, u₅.other .eax (by decide), u₄.gpr, u₄.other .edx (by decide), u₃.gpr, u₃.other .eax (by decide),
    u₂.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, ← BitVec.xor_append, ← readW64_split,
    show (VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 388 =
      (VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 384 + BitVec.ofNat 64 4 from (Offset.add_add _ 384 4).symm,
    ← readW64_split, h.mem, le8_xor, le8_readW, le8_readW, hp.keyBytes (by decide)]
  have lb := hp.lastBytes
  rw [hL] at lb
  rw [lb]
  simp only [VG.Proof.CmacTripleDes.X86.mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, hL, ite_true]
  exact Proof.Cmac.xor_comm _ _

/-! ## Copying the last bytes -/

theorem byte_rt32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 8)
    (hcx : s.gpr .ecx = p) (hdi : s.gpr .edi = c) (hdx : s.gpr .edx = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 8 ≤ 2 ^ 32)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 8, InRegions s.wr (c.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hd : (⟨p.setWidth 64, L⟩ : Region).Disjoint ⟨c.setWidth 64, 8⟩) :
    WP isa copy s fun s' =>
      s'.mem = VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) L) ∧
      s'.gpr .edi = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → r ≠ .edx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.movzx8 .eax (at_ .ecx 0), .store8 (at_ .edi 0) .al,
      .alu .add .ecx (.imm 1), .alu .add .edi (.imm 1), .alu .sub .edx (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .ecx = p + BitVec.ofNat 32 i ∧
      t.gpr .edi = c + BitVec.ofNat 32 i ∧ t.gpr .edx = BitVec.ofNat 32 (L - i) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → r ≠ .edx → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [hcx]; exact (BitVec.add_zero p).symm, by rw [hdi]; exact (BitVec.add_zero c).symm,
      by rw [hdx, Nat.sub_zero], by simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, xc, xd, xn, mem, g, rd, wr⟩
  refine wp_movzx8 (a := p.setWidth 64 + BitVec.ofNat 64 i) (by rw [VG.Proof.CmacTripleDes.X86.ea_at', xc, VG.Proof.CmacTripleDes.X86.addr_off2 (by omega), VG.Proof.CmacTripleDes.X86.add0])
    (by rw [rd, wr]; exact hr i hi) fun t₁ u₁ => ?_
  refine wp_store8 (a := c.setWidth 64 + BitVec.ofNat 64 i)
    (by rw [VG.Proof.CmacTripleDes.X86.ea_at', u₁.other _ (by decide), xd, VG.Proof.CmacTripleDes.X86.addr_off2 (by omega), VG.Proof.CmacTripleDes.X86.add0]) (by rw [u₁.wr, wr]; exact hw i (by omega))
    fun t₂ v₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (p.setWidth 64) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i)
      (p.setWidth 64 + BitVec.ofNat 64 i) = s.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
    (VG.WriteBytes.writeBytes_frame s.mem (c.setWidth 64) _ (R := ⟨c.setWidth 64, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t₅.mem = VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, show Reg8.al.reg = .eax from rfl, u₁.gpr, u₁.mem, mem, VG.Proof.CmacTripleDes.X86.byte_rt32, hx,
      Proof.Cmac.bytesAt_succ, VG.WriteBytes.writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have xn' : t₅.gpr .edx = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xn,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.X86.sub_ofNat (by omega)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    rw [VG.Proof.CmacTripleDes.X86.eval_ne', z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xn,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.X86.sub_ofNat (by omega), Nat.sub_sub,
      Wp.ofNat_beq_zero (by omega)]
    rfl
  have gg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → r ≠ .edx → t₅.gpr r = s.gpr r := fun r ha hc hdi hdx => by
    rw [u₅.other _ hdx, u₄.other _ hdi, u₃.other _ hc, v₂.gpr, u₁.other _ ha, g r ha hc hdi hdx]
  have xd' : t₅.gpr .edi = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xd,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have xc' : t₅.gpr .ecx = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), xc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [xd', he], gg, rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, xc', xd', xn', hmem, gg, rd', wr'⟩

/-! ## A partial last block -/

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.FPre s₀) (hL : VG.Proof.CmacTripleDes.X86.FL s₀ < 8) {s : State} (h : VG.Proof.CmacTripleDes.X86.P1 s₀ s) :
    WP isa partialBlock s (VG.Proof.CmacTripleDes.X86.BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hN : VG.Proof.CmacTripleDes.X86.FL s₀ < 2 ^ 32 := (VG.X86.arg s₀ 3).isLt
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  let C : Addr := (VG.Proof.CmacTripleDes.X86.FS s₀).setWidth 64 + BitVec.ofNat 64 136
  have cIn : ∀ i < 8, InRegions s₀.wr (C + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [Offset.add_add]; exact hp.inScr (by omega) (by decide)
  have cR : ∀ d n, d + n ≤ 8 → (VG.Proof.CmacTripleDes.X86.mnR s₀).Contains (C + BitVec.ofNat 64 d) n := fun d n h =>
    Offset.contains_base _ h (by omega)
  have mnS : ∀ r ∈ [VG.Proof.CmacTripleDes.X86.mnR s₀], Region.Sub r (VG.Proof.CmacTripleDes.X86.fstR s₀) ∨ Region.Sub r (VG.Proof.CmacTripleDes.X86.fscrR s₀) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Or.inr (Offset.sub_base _ (by decide))
  -- Zero the bytes.
  refine WP.seq ?_
  simp only [zero, stk]
  refine wp_movi fun s₁ u₁ => ?_
  refine wp_store (hp.scrEa (by rw [u₁.other _ (by decide), h.ebp]) (by decide))
    (by rw [u₁.wr, h.wr]; exact hp.inScr (by decide) (by decide)) fun s₂ w₂ => ?_
  refine wp_store (hp.scrEa (by rw [w₂.gpr, u₁.other _ (by decide), h.ebp]) (by decide))
    (by rw [w₂.wr, u₁.wr, h.wr]; exact hp.inScr (by decide) (by decide)) fun s₃ w₃ => ?_
  let m₁ := ((VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)).writeW C (0 : BitVec 32)).writeW (C + BitVec.ofNat 64 4) (0 : BitVec 32)
  have mem₃ : s₃.mem = m₁ := by
    rw [w₃.mem, w₂.mem, w₂.gpr, u₁.gpr, u₁.mem, h.mem]
    show _ = ((VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)).writeW C (0 : BitVec 32)).writeW (C + BitVec.ofNat 64 4) (0 : BitVec 32)
    rw [Offset.add_add]
  have fm₁ : Frame [VG.Proof.CmacTripleDes.X86.mnR s₀] (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)) m₁ :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simpa [VG.Proof.CmacTripleDes.X86.add0] using cR 0 4 (by decide))).writeW
      (List.mem_singleton_self _) _ (cR 4 4 (by decide))
  refine wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => ?_
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, w₃.rd, w₂.rd, u₁.rd, h.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, w₃.wr, w₂.wr, u₁.wr, h.wr]
  have esp₅ : s₅.gpr .esp = s₀.gpr .esp := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), w₃.gpr, w₂.gpr, u₁.other _ (by decide), h.esp]
  have mem₅ : s₅.mem = m₁ := by rw [u₅.mem, u₄.mem, mem₃]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 2 rfl esp₅ (hp.argIn rd₅ wr₅ (by decide))
    (by rw [mem₅]; exact hp.arg_eq fm₁ mnS (by decide)) fun s₆ u₆ => ?_
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 3 rfl (by rw [u₆.other _ (by decide), esp₅])
    (hp.argIn (by rw [u₆.rd, rd₅]) (by rw [u₆.wr, wr₅]) (by decide))
    (by rw [u₆.mem, mem₅]; exact hp.arg_eq fm₁ mnS (by decide)) fun s₇ u₇ =>
    wp_cmpi fun s₈ f₈ _ z₈ => WP.block_nil ?_
  have mem₈ : s₈.mem = m₁ := by rw [f₈.mem, u₇.mem, u₆.mem, mem₅]
  have g₈ : ∀ r, r ∉ [Reg.eax, .ecx, .edx, .edi] → s₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₈.gpr, u₇.other _ hr.2.2.1, u₆.other _ hr.2.1, u₅.other _ hr.2.2.2, u₄.other _ hr.2.2.2, w₃.gpr, w₂.gpr,
      u₁.other _ hr.1]
  have di₈ : s₈.gpr .edi = VG.Proof.CmacTripleDes.X86.FS s₀ + BitVec.ofNat 32 136 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, w₃.gpr, w₂.gpr,
      u₁.other _ (by decide), h.ebp]; rfl
  have cx₈ : s₈.gpr .ecx = VG.Proof.CmacTripleDes.X86.FP s₀ := by rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr]
  have dx₈ : s₈.gpr .edx = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.X86.FL s₀) := by rw [f₈.gpr, u₇.gpr]; simp [VG.Proof.CmacTripleDes.X86.FL]
  have z8 : s₈.zf = some (decide (VG.Proof.CmacTripleDes.X86.FL s₀ = 0)) := by
    rw [z₈, u₇.gpr, show ∀ x : BitVec 32, x - 0 = x from fun x => by simp,
      show VG.X86.arg s₀ 3 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.X86.FL s₀) by simp [VG.Proof.CmacTripleDes.X86.FL], Wp.ofNat_beq_zero hN]
  have rd₈ : s₈.rd = s₀.rd := by rw [f₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₈ : s₈.wr = s₀.wr := by rw [f₈.wr, u₇.wr, u₆.wr, wr₅]
  have hcA : (VG.Proof.CmacTripleDes.X86.FS s₀ + BitVec.ofNat 32 136).setWidth 64 = C := by
    rw [← VG.Proof.CmacTripleDes.X86.addr_zero, VG.Proof.CmacTripleDes.X86.addr_off2 (by omega), VG.Proof.CmacTripleDes.X86.add0]
  have dPC : (VG.Proof.CmacTripleDes.X86.lastR s₀).Disjoint ⟨C, 8⟩ := hp.last_scr.sub_right (Offset.sub_base _ (by decide))
  have lastM₁ : Spec.Aes.bytesAt m₁ ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.FL s₀) =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.FL s₀) := by
    rw [← hp.lastBytes]
    exact bytesAt_frame fm₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (t : State) =>
      t.mem = VG.WriteBytes.writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.FL s₀)) ∧
      t.gpr .edi = VG.Proof.CmacTripleDes.X86.FS s₀ + BitVec.ofNat 32 136 + BitVec.ofNat 32 (VG.Proof.CmacTripleDes.X86.FL s₀) ∧
      (∀ r, r ∉ [Reg.eax, .ecx, .edx, .edi] → t.gpr r = s.gpr r) ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr) ?_ fun t ht => ?_)
  · by_cases hL0 : VG.Proof.CmacTripleDes.X86.FL s₀ = 0
    · refine WP.ite true (by rw [VG.Proof.CmacTripleDes.X86.eval_e', z8, hL0]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₈, hL0]; simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil],
        by rw [di₈, hL0]; exact (BitVec.add_zero _).symm, g₈, rd₈, wr₈⟩
    · refine WP.ite false (by rw [VG.Proof.CmacTripleDes.X86.eval_e', z8]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (VG.Proof.CmacTripleDes.X86.copy_wp (p := VG.Proof.CmacTripleDes.X86.FP s₀) (c := VG.Proof.CmacTripleDes.X86.FS s₀ + BitVec.ofNat 32 136) (by omega) (by omega) cx₈ di₈ dx₈
        (by omega) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        (fun i hi => by rw [rd₈, wr₈]; exact hp.inLast (by omega) (by decide))
        (fun i hi => by rw [wr₈, hcA]; exact cIn i hi) (by rw [hcA]; exact dPC)) ?_
      rintro t ⟨m₂, di₂, g₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, mem₈, hcA, lastM₁], di₂, fun r hr => by
        rw [g₂ r (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h]))
          (fun h => hr (by simp [h])), g₈ r hr], by rw [rd₂, rd₈], by rw [wr₂, wr₈]⟩
  obtain ⟨m₂, di₂, g₂, rd₂, wr₂⟩ := ht
  have hlen : (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.FL s₀)).length = VG.Proof.CmacTripleDes.X86.FL s₀ :=
    Proof.Cmac.bytesAt_length _ _ _
  have cL : t.ea (at_ .edi 0) = C + BitVec.ofNat 64 (VG.Proof.CmacTripleDes.X86.FL s₀) := by
    rw [VG.Proof.CmacTripleDes.X86.ea_at', di₂, Offset.add_add, VG.Proof.CmacTripleDes.X86.addr_off2 (by omega), VG.Proof.CmacTripleDes.X86.add0, Offset.add_add]
  have trw : t.rd ++ t.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂]
  have ebpt : t.gpr .ebp = VG.Proof.CmacTripleDes.X86.FS s₀ := by rw [g₂ _ (by decide), h.ebp]
  have esit : t.gpr .esi = VG.Proof.CmacTripleDes.X86.FW s₀ := by rw [g₂ _ (by decide), h.esi]
  simp only [padK2]
  refine wp_movi fun t₁ v₁ => ?_
  refine wp_store8 (by rw [show t₁.ea (at_ .edi 0) = t.ea (at_ .edi 0) by rw [VG.Proof.CmacTripleDes.X86.ea_at', VG.Proof.CmacTripleDes.X86.ea_at', v₁.other _ (by decide)],
      cL]) (by rw [v₁.wr, wr₂]; exact cIn _ hL) fun t₂ v₂ => ?_
  refine wp_movm (hp.scrEa (by rw [v₂.gpr, v₁.other _ (by decide), ebpt]) (by decide))
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact VG.Proof.CmacTripleDes.X86.wr_in (hp.inScr (by decide) (by decide))) fun t₃ v₃ => ?_
  refine wp_movm (hp.scrEa (by rw [v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), ebpt]) (by decide))
    (by rw [v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact VG.Proof.CmacTripleDes.X86.wr_in (hp.inScr (by decide) (by decide)))
    fun t₄ v₄ => ?_
  have k392 := hp.inKey (d := 392) (n := 4) (by decide) (by decide)
  have k396 := hp.inKey (d := 396) (n := 4) (by decide) (by decide)
  refine VG.Proof.CmacTripleDes.X86.wp_xorma (hp.keyEa (d := 392) (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr,
                                 v₁.other _ (by decide), esit]) (by decide))
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact k392) fun t₅ v₅ => ?_
  refine VG.Proof.CmacTripleDes.X86.wp_xorma (hp.keyEa (d := 396) (by rw [v₅.other _ (by decide), v₄.other _ (by decide),
                                 v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), esit]) (by decide))
    (by rw [v₅.rd, v₅.wr, v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact k396)
    fun t₆ v₆ => WP.block_nil ?_
  let m₃ := (VG.WriteBytes.writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.FL s₀))).writeW
    (C + BitVec.ofNat 64 (VG.Proof.CmacTripleDes.X86.FL s₀)) (0x80 : Byte)
  have mem₂ : t₂.mem = m₃ := by rw [v₂.mem, v₁.mem, m₂, show Reg8.al.reg = .eax from rfl, v₁.gpr, VG.Proof.CmacTripleDes.X86.b80]
  have g₆ : ∀ r, r ∉ [Reg.eax, .ecx, .edx, .edi] → t₆.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₆.other _ hr.2.2.1, v₅.other _ hr.1, v₄.other _ hr.2.2.1, v₃.other _ hr.1, v₂.gpr, v₁.other _ hr.1,
      g₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  -- The frame.
  have fr : Frame [VG.Proof.CmacTripleDes.X86.mnR s₀] (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)) m₃ := by
    refine (fm₁.trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)).writeW (List.mem_singleton_self _) _ (cR _ 1 (by omega))
    rw [hlen]; simpa [VG.Proof.CmacTripleDes.X86.add0] using cR 0 (VG.Proof.CmacTripleDes.X86.FL s₀) (by omega)
  -- The block.
  have kD : (⟨(VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 392, 8⟩ : Region).Disjoint (VG.Proof.CmacTripleDes.X86.mnR s₀) :=
    (hp.key_scr.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))
  have k2 : Spec.Aes.bytesAt m₃ ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 392) 8 =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 392) 8 := by
    rw [bytesAt_frame fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kD) (by decide),
      hp.keyBytes (by decide)]
  have pad : Spec.Aes.bytesAt m₃ C 8 =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.FL s₀) ++ [0x80] ++ Spec.Cmac.zeros (8 - VG.Proof.CmacTripleDes.X86.FL s₀ - 1) := by
    have hz : Spec.Aes.bytesAt m₁ C 8 = Spec.Cmac.zeros 8 := by
      rw [← le8_readW, readW64_split, Mem.readW_writeW_self32, VG.Proof.CmacTripleDes.X86.readW_lo_of_hi]; decide
    have := padded_bytes8 m₁ C (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FP s₀).setWidth 64) (VG.Proof.CmacTripleDes.X86.FL s₀)) (by rw [hlen]; exact hL) hz
    rw [hlen] at this
    exact this
  refine ⟨by rw [g₆ _ (by decide), h.ebp], by rw [g₆ _ (by decide), h.esi], by rw [g₆ _ (by decide), h.esp],
    by rw [v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd₂],
    by rw [v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₂],
    by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, mem₂]; exact fr, ?_⟩
  rw [v₆.gpr, v₆.other .eax (by decide), v₅.gpr, v₅.other .edx (by decide), v₄.gpr, v₄.other .eax (by decide),
    v₃.gpr, v₅.mem, v₄.mem, v₃.mem, mem₂, ← BitVec.xor_append,
    show (VG.Proof.CmacTripleDes.X86.FS s₀).setWidth 64 + BitVec.ofNat 64 140 = C + BitVec.ofNat 64 4 from (Offset.add_add _ 136 4).symm,
    ← readW64_split,
    show (VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 396 =
      (VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 392 + BitVec.ofNat 64 4 from (Offset.add_add _ 392 4).symm,
    ← readW64_split, le8_xor, le8_readW, le8_readW, pad, k2]
  simp only [VG.Proof.CmacTripleDes.X86.mn, Spec.Cmac.lastBlock, hlen, show VG.Proof.CmacTripleDes.X86.FL s₀ ≠ 8 by omega, ite_false]
  exact Proof.Cmac.xor_comm _ _

theorem finPre_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86.FPre s₀) : WP isa finPre s₀ (VG.Proof.CmacTripleDes.X86.BPost s₀) := by
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.fpre1_wp hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  by_cases hL : VG.Proof.CmacTripleDes.X86.FL s₀ = 8
  · exact WP.ite true (by rw [VG.Proof.CmacTripleDes.X86.eval_e', z₁]; simp [hL]) (fun _ => VG.Proof.CmacTripleDes.X86.full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [VG.Proof.CmacTripleDes.X86.eval_e', z₁]; simp [hL]) (fun h => by cases h)
      (fun _ => VG.Proof.CmacTripleDes.X86.partial_wp hp (by have := hp.len; omega) h₁)

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.CT`. -/
section

/-!
# TDEA-CMAC on x86: constant time

Untrusted: everything here is checked by Lean. The taint analysis
(`Framework/X86/Taint.lean`) checks that only the stack arguments, which are
public, decide branches and addresses. The functions keep their pointers
and counts in the scratch buffer, the second writable region: the analysis
knows the stack argument holding it is that region's base, so `ebp`, loaded
from it, addresses public words there, and the block's counters and step
are stored and loaded through it.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86

/-- `init`'s initial taint: the stack arguments are public; `out` and
`scratch` are the bases of the writable regions. -/
def initTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [400, 640], argLen := 20, argBases := [(12, 0), (16, 1)] }

/-- `update`'s and `finalize`'s: the stack arguments are public; `state` and
`scratch` are the bases of the writable regions. -/
def streamTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8, 640], argLen := 24, argBases := [(8, 0), (20, 1)] }

theorem argMem_eq {s₁ s₂ : State} {n : Nat} (f₁ : (s₁.gpr .esp).toNat + n ≤ 2 ^ 32)
    (f₂ : (s₂.gpr .esp).toNat + n ≤ 2 ^ 32) (ha : ∀ i, 4 + 4 * i < n → VG.X86.arg s₁ i = VG.X86.arg s₂ i) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < n) :
    s₁.mem (VG.X86.Taint.argByte s₁ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) =
      s₂.mem (VG.X86.Taint.argByte s₂ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) := by
  rw [show VG.X86.Taint.depth ([] : List (Option Nat)) = 0 from rfl, Nat.zero_add,
    VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
    Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
  exact congrArg _ (ha _ (by omega))

/-! ## `init` -/

theorem init_wf {s : State} (h : initX86.pre s) : VG.X86.Taint.Wf VG.Proof.CmacTripleDes.X86.initTaint s := by
  have hp := IPre.of h
  have := hp.out_fit; have := hp.scr_fit; have := hp.esp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.CmacTripleDes.X86.initTaint], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [VG.Proof.CmacTripleDes.X86.initTaint]; omega, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_scr
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.args_scr
  · intro p hp'
    simp only [VG.Proof.CmacTripleDes.X86.initTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [VG.Proof.CmacTripleDes.X86.initTaint], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, VG.X86.arg, argAddr]

theorem init_ct : ConstantTime isa initX86.pre initX86.pub init := by
  refine VG.Taint.constantTime (A := taint) VG.Proof.CmacTripleDes.X86.initTaint ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨hesp, ha⟩
  have hp₁ := IPre.of h₁; have hp₂ := IPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.CmacTripleDes.X86.init_wf h₁, VG.Proof.CmacTripleDes.X86.init_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => VG.Proof.CmacTripleDes.X86.argMem_eq (n := 20) hp₁.esp_fit hp₂.esp_fit (fun i hi => ha i (by omega)) h4 hk⟩
  · simp only [VG.Proof.CmacTripleDes.X86.initTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [VG.Proof.CmacTripleDes.X86.outR, VG.Proof.CmacTripleDes.X86.iscrR, VG.Proof.CmacTripleDes.X86.O, VG.Proof.CmacTripleDes.X86.Sc, ha 2 (by omega), ha 3 (by omega)]

/-! ## `update` and `finalize` -/

/-- The state and the scratch buffer, the writable regions of `update` and
`finalize`, from their stack arguments. -/
abbrev streamWr (s : State) : List Region := [⟨(VG.X86.arg s 1).setWidth 64, 8⟩, ⟨(VG.X86.arg s 4).setWidth 64, 640⟩]

theorem streamTaint_wf {s : State} (hwr : s.wr = VG.Proof.CmacTripleDes.X86.streamWr s)
    (st_scr : Region.Disjoint ⟨(VG.X86.arg s 1).setWidth 64, 8⟩ ⟨(VG.X86.arg s 4).setWidth 64, 640⟩)
    (ret_st : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(VG.X86.arg s 1).setWidth 64, 8⟩)
    (ret_scr : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(VG.X86.arg s 4).setWidth 64, 640⟩)
    (args_st : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(VG.X86.arg s 1).setWidth 64, 8⟩)
    (args_scr : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(VG.X86.arg s 4).setWidth 64, 640⟩)
    (st_fit : (VG.X86.arg s 1).toNat + 8 ≤ 2 ^ 32) (scr_fit : (VG.X86.arg s 4).toNat + 640 ≤ 2 ^ 32)
    (esp_fit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) : VG.X86.Taint.Wf VG.Proof.CmacTripleDes.X86.streamTaint s := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hwr, VG.Proof.CmacTripleDes.X86.streamTaint], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [VG.Proof.CmacTripleDes.X86.streamTaint]; omega, ?_⟩, ?_⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact st_scr
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) ret_st args_st
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) ret_scr args_scr
  · intro p hp'
    simp only [VG.Proof.CmacTripleDes.X86.streamTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [VG.Proof.CmacTripleDes.X86.streamTaint], ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, VG.X86.arg, argAddr]

/-- Two runs agree on `streamTaint` when they agree on the stack arguments. -/
theorem streamTaint_agree {s₁ s₂ : State} (w₁ : VG.X86.Taint.Wf VG.Proof.CmacTripleDes.X86.streamTaint s₁)
    (w₂ : VG.X86.Taint.Wf VG.Proof.CmacTripleDes.X86.streamTaint s₂) (hw₁ : s₁.wr = VG.Proof.CmacTripleDes.X86.streamWr s₁) (hw₂ : s₂.wr = VG.Proof.CmacTripleDes.X86.streamWr s₂)
    (f₁ : (s₁.gpr .esp).toNat + 24 ≤ 2 ^ 32) (f₂ : (s₂.gpr .esp).toNat + 24 ≤ 2 ^ 32)
    (hesp : s₁.gpr .esp = s₂.gpr .esp) (ha : ∀ i < 5, VG.X86.arg s₁ i = VG.X86.arg s₂ i) :
    VG.X86.Taint.Agree VG.Proof.CmacTripleDes.X86.streamTaint s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, w₁, w₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => VG.Proof.CmacTripleDes.X86.argMem_eq (n := 24) f₁ f₂ (fun i hi => ha i (by omega)) h4 hk⟩
  · simp only [VG.Proof.CmacTripleDes.X86.streamTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hw₁, hw₂]; simp only [VG.Proof.CmacTripleDes.X86.streamWr, ha 1 (by omega), ha 4 (by omega)]

theorem update_ct : ConstantTime isa updateX86.pre updateX86.pub update := by
  refine VG.Taint.constantTime (A := taint) VG.Proof.CmacTripleDes.X86.streamTaint ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨hesp, ha⟩
  have p₁ := UPre.of h₁; have p₂ := UPre.of h₂
  exact VG.Proof.CmacTripleDes.X86.streamTaint_agree
    (VG.Proof.CmacTripleDes.X86.streamTaint_wf p₁.wr p₁.st_scr p₁.ret_st p₁.ret_scr p₁.args_st p₁.args_scr p₁.st_fit p₁.scr_fit p₁.esp_fit)
    (VG.Proof.CmacTripleDes.X86.streamTaint_wf p₂.wr p₂.st_scr p₂.ret_st p₂.ret_scr p₂.args_st p₂.args_scr p₂.st_fit p₂.scr_fit p₂.esp_fit)
    p₁.wr p₂.wr p₁.esp_fit p₂.esp_fit hesp ha

theorem finalize_ct : ConstantTime isa finalizeX86.pre finalizeX86.pub finalize := by
  refine VG.Taint.constantTime (A := taint) VG.Proof.CmacTripleDes.X86.streamTaint ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨hesp, ha⟩
  have p₁ := FPre.of h₁; have p₂ := FPre.of h₂
  exact VG.Proof.CmacTripleDes.X86.streamTaint_agree
    (VG.Proof.CmacTripleDes.X86.streamTaint_wf p₁.wr p₁.st_scr p₁.ret_st p₁.ret_scr p₁.args_st p₁.args_scr p₁.st_fit p₁.scr_fit p₁.esp_fit)
    (VG.Proof.CmacTripleDes.X86.streamTaint_wf p₂.wr p₂.st_scr p₂.ret_st p₂.ret_scr p₂.args_st p₂.args_scr p₂.st_fit p₂.scr_fit p₂.esp_fit)
    p₁.wr p₂.wr p₁.esp_fit p₂.esp_fit hesp ha

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.FinalizeCorrect`. -/
section

/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_finalize` is correct

Untrusted: everything here is checked by Lean. After the branch on the
length, `eax:edx` holds `Mₙ` (`BPost`); the function XORs in the chaining
value `C`, encrypts it and stores `CIPH_K(C ⊕ Mₙ)` as the state, the MAC
(`macFull_split8`).
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86 VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.X86 (Upd Mupd wp_movm wp_store wp_bswap)

theorem finalize_wp {s₀ : State} (h0 : finalizeX86.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeX86.post s₀ s' := by
  have hp := FPre.of h0
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have tf := hp.st_fit
  have tf' : (VG.X86.arg s₀ 1).toNat + 8 ≤ 2 ^ 32 := hp.st_fit
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.finPre_wp hp) fun s₁ h₁ => ?_)
  have rdwr₁ : s₁.rd ++ s₁.wr = [VG.Proof.CmacTripleDes.X86.keyR s₀, VG.Proof.CmacTripleDes.X86.lastR s₀, VG.Proof.CmacTripleDes.X86.argsR s₀, VG.Proof.CmacTripleDes.X86.fstR s₀, VG.Proof.CmacTripleDes.X86.fscrR s₀] := by
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  have stIn : ∀ d, d + 4 ≤ 8 → InRegions (s₁.rd ++ s₁.wr) ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr₁]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.fstR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  have mnS : ∀ r ∈ [VG.Proof.CmacTripleDes.X86.mnR s₀], Region.Sub r (VG.Proof.CmacTripleDes.X86.fstR s₀) ∨ Region.Sub r (VG.Proof.CmacTripleDes.X86.fscrR s₀) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Or.inr (Offset.sub_base _ (by decide))
  -- `finMid`.
  refine WP.seq ?_
  simp only [finMid, stk]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 1 rfl h₁.esp (hp.argIn h₁.rd h₁.wr (by decide)) (hp.arg_eq h₁.frame mnS (by decide))
    fun s₂ u₂ => ?_
  refine VG.Proof.CmacTripleDes.X86.wp_xorma (a := (VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64) (by rw [u₂.gpr, VG.Proof.CmacTripleDes.X86.addr_zero])
    (by rw [u₂.rd, u₂.wr]; simpa [VG.Proof.CmacTripleDes.X86.add0] using stIn 0 (by decide)) fun s₃ u₃ => ?_
  refine VG.Proof.CmacTripleDes.X86.wp_xorma (a := (VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [u₃.other .ecx (by decide), u₂.gpr]; exact addr_eq (by omega))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_bswap fun s₅ u₅ => wp_bswap fun s₆ u₆ => WP.block_nil ?_
  have g₆ : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s₆.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2, u₅.other _ hr.1, u₄.other _ hr.2.2, u₃.other _ hr.1, u₂.other _ hr.2.1]
  have mem₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have ax₆ : s₆.gpr .eax ++ s₆.gpr .edx =
      byteRev64 ((s₁.gpr .edx ++ s₁.gpr .eax) ^^^ s₁.mem.readW ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64) 64) := by
    rw [u₆.gpr, u₆.other .eax (by decide), u₅.gpr, u₅.other .edx (by decide), u₄.gpr, u₄.other .eax (by decide),
      u₃.gpr, u₃.other .edx (by decide), u₂.other .eax (by decide), u₂.other .edx (by decide), u₃.mem,
      u₂.mem, VG.Proof.CmacTripleDes.X86.bswap_xor_append,
      readW64_split s₁.mem]
  have esi₆ : s₆.gpr .esi = VG.Proof.CmacTripleDes.X86.FW s₀ := by rw [g₆ _ (by decide), h₁.esi]
  have ebp₆ : s₆.gpr .ebp = VG.Proof.CmacTripleDes.X86.FS s₀ := by rw [g₆ _ (by decide), h₁.ebp]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr]
  have bp : VG.Proof.CmacTripleDes.X86.BlockPre s₆ :=
    { sched := ⟨400, by rw [esi₆, rd₆, wr₆, hp.rd]; simp, by decide, by rw [esi₆]; exact kf⟩
      scr := ⟨640, by rw [ebp₆, wr₆, hp.wr]; simp, by decide, by rw [ebp₆]; exact sf⟩
      disj := by
        rw [esi₆, ebp₆]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86.block_ok bp) fun s₇ ⟨same₇, esi₇, ax₇⟩ => ?_)
  let A := (VG.Proof.CmacTripleDes.X86.FS s₀).setWidth 64
  have xR₆ : VG.Proof.CmacTripleDes.X86.xR s₆ = ⟨A, 84⟩ := by rw [VG.Proof.CmacTripleDes.X86.xR, ebp₆]
  have f₇ : Frame [⟨A, 84⟩] s₁.mem s₇.mem := by rw [← mem₆, ← xR₆]; exact same₇.frame
  have F₇ : Frame [VG.Proof.CmacTripleDes.X86.mnR s₀, ⟨A, 84⟩] (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)) s₇.mem :=
    (h₁.frame.mono (by simp)).trans (f₇.mono (by simp))
  have F₇S : ∀ r ∈ [VG.Proof.CmacTripleDes.X86.mnR s₀, ⟨A, 84⟩], Region.Sub r (VG.Proof.CmacTripleDes.X86.fstR s₀) ∨ Region.Sub r (VG.Proof.CmacTripleDes.X86.fscrR s₀) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (Offset.sub_base _ (by decide))
    · exact Or.inr (Region.sub_prefix (by decide))
  have esp₇ : s₇.gpr .esp = s₀.gpr .esp := by rw [same₇.esp, g₆ _ (by decide), h₁.esp]
  have ebp₇ : s₇.gpr .ebp = VG.Proof.CmacTripleDes.X86.FS s₀ := by rw [same₇.ebp, ebp₆]
  have rd₇ : s₇.rd = s₀.rd := by rw [same₇.rd, rd₆]
  have wr₇ : s₇.wr = s₀.wr := by rw [same₇.wr, wr₆]
  rw [WP.block_append_iff]
  refine VG.Proof.CmacTripleDes.X86.wp_arg (s₀ := s₀) 1 rfl esp₇ (hp.argIn rd₇ wr₇ (by decide)) (hp.arg_eq F₇ F₇S (by decide))
    fun s₈ u₈ => wp_bswap fun s₉ u₉ => wp_bswap fun s₁₀ u₁₀ => ?_
  have stW : ∀ d, d + 4 ≤ 8 → InRegions s₁₀.wr ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [u₁₀.wr, u₉.wr, u₈.wr, wr₇, hp.wr]
    exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.fstR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_store (a := (VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64) (by rw [VG.Proof.CmacTripleDes.X86.ea_at', u₁₀.other _ (by decide), u₉.other _ (by decide),
                               u₈.gpr, VG.Proof.CmacTripleDes.X86.addr_zero]) (by simpa [VG.Proof.CmacTripleDes.X86.add0] using stW 0 (by decide)) fun s₁₁ w₁₁ => ?_
  refine wp_store (a := (VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [VG.Proof.CmacTripleDes.X86.ea_at', w₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]; exact addr_eq (by omega))
    (by rw [w₁₁.wr]; exact stW 4 (by decide)) fun s₁₂ w₁₂ => WP.block_nil ?_
  have ebp₁₂ : s₁₂.gpr .ebp = VG.Proof.CmacTripleDes.X86.FS s₀ := by
    rw [w₁₂.gpr, w₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), ebp₇]
  have mem₁₂ : s₁₂.mem = (s₇.mem.writeW ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64) (bswap (s₇.gpr .eax))).writeW
      ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64 + BitVec.ofNat 64 4) (bswap (s₇.gpr .edx)) := by
    rw [w₁₂.mem, w₁₁.mem, w₁₁.gpr, u₁₀.gpr, u₁₀.other .eax (by decide), u₉.gpr, u₁₀.mem, u₉.mem,
      u₉.other .edx (by decide), u₈.other .eax (by decide), u₈.other .edx (by decide), u₈.mem]
  have rdwr₁₂ : s₁₂.rd ++ s₁₂.wr = [VG.Proof.CmacTripleDes.X86.keyR s₀, VG.Proof.CmacTripleDes.X86.lastR s₀, VG.Proof.CmacTripleDes.X86.argsR s₀, VG.Proof.CmacTripleDes.X86.fstR s₀, VG.Proof.CmacTripleDes.X86.fscrR s₀] := by
    rw [w₁₂.rd, w₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, w₁₂.wr, w₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, rd₇, wr₇, hp.rd, hp.wr]; rfl
  have c0 : (VG.Proof.CmacTripleDes.X86.fstR s₀).Contains ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64) (32 / 8) := by
    simpa [VG.Proof.CmacTripleDes.X86.add0] using Offset.contains_base ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  have c4 : (VG.Proof.CmacTripleDes.X86.fstR s₀).Contains ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64 + BitVec.ofNat 64 4) (32 / 8) :=
    Offset.contains_base _ (by decide) (by omega)
  have F₁₂ : Frame [VG.Proof.CmacTripleDes.X86.mnR s₀, ⟨A, 84⟩, VG.Proof.CmacTripleDes.X86.fstR s₀] (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)) s₁₂.mem := by
    rw [mem₁₂]
    exact ((F₇.mono (by simp)).writeW (r := VG.Proof.CmacTripleDes.X86.fstR s₀) (by simp) _ c0).writeW (r := VG.Proof.CmacTripleDes.X86.fstR s₀) (by simp) _ c4
  -- The slots of the saved registers.
  have slots : ∀ d, 84 ≤ d → d + 4 ≤ 100 →
      s₁₂.mem.readW (A + BitVec.ofNat 64 d) 32 = (VG.Proof.CmacTripleDes.X86.savedMem s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)).readW (A + BitVec.ofNat 64 d) 32 := by
    intro d h₁' h₂'
    refine F₁₂.readW (r := ⟨A + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact (hp.st_scr.sub_right (Offset.sub_base _ (by omega))).symm
  have ret : s₁₂.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
    rw [F₁₂.readW (r := VG.Proof.CmacTripleDes.X86.retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact (VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)).readW (r := VG.Proof.CmacTripleDes.X86.retR s₀) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))
      · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))
      · exact hp.ret_st
  refine WP.mono (VG.Proof.CmacTripleDes.X86.restore_ok ebp₁₂ (by omega) (fun d h₁' h₂' => by
      rw [rdwr₁₂]; exact VG.Proof.CmacTripleDes.X86.in_rw (r := VG.Proof.CmacTripleDes.X86.fscrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
      (VG.Proof.CmacTripleDes.X86.saved_of slots))
    fun s' r' => ⟨VG.Proof.CmacTripleDes.X86.restored r' (by
      rw [w₁₂.gpr, w₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), esp₇]) (by rw [r'.mem, ret]), ?_⟩
  intro hk msg hml hne hst
  have F₈ : Frame [VG.Proof.CmacTripleDes.X86.fscrR s₀] s₀.mem s₇.mem := by
    refine ((VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)).sub fun r hr => ⟨VG.Proof.CmacTripleDes.X86.fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
      (F₇.sub fun r hr => ⟨VG.Proof.CmacTripleDes.X86.fscrR s₀, by simp, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub_base _ (by decide)
    · exact Region.sub_prefix (by decide)
  have F₁ : Frame [VG.Proof.CmacTripleDes.X86.fscrR s₀] s₀.mem s₁.mem :=
    ((VG.Proof.CmacTripleDes.X86.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86.FS s₀)).sub fun r hr => ⟨VG.Proof.CmacTripleDes.X86.fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
    (h₁.frame.sub fun r hr => ⟨VG.Proof.CmacTripleDes.X86.fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩)
  have hS' : VG.Proof.CmacTripleDes.X86.sch s₆ = Spec.TripleDes.scheduleAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64) := by
    show Spec.TripleDes.scheduleAt s₆.mem ((s₆.gpr .esi).setWidth 64) = _
    rw [esi₆, mem₆]
    exact VG.Proof.CmacTripleDes.X86.scheduleAt_frame F₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.key_scr.sub_left (Region.sub_prefix (by decide))
  have hst₁ : le8 (s₁.mem.readW ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64) 64) = Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64) 8 := by
    rw [le8_readW]
    exact bytesAt_frame F₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr) (by decide)
  have hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64))
  have hk' : Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 384) 8 ++
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 392) 8 =
      (Spec.Cmac.subkeys (VG.Proof.CmacTripleDes.X86.ciphAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64)) 8).1 ++
        (Spec.Cmac.subkeys (VG.Proof.CmacTripleDes.X86.ciphAt s₀.mem ((VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64)) 8).2 := by
    rw [show (VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 392 =
        (VG.Proof.CmacTripleDes.X86.FW s₀).setWidth 64 + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
      (Offset.add_add _ 384 8).symm, ← bytesAt_split]; exact hk
  obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, VG.Proof.CmacTripleDes.X86.ciphAt, hks, length_le8])
  show Spec.Aes.bytesAt s'.mem ((VG.Proof.CmacTripleDes.X86.FSt s₀).setWidth 64) 8 = _
  rw [r'.mem, mem₁₂, ← le8_readW, readW64_split, Mem.readW_writeW_self32, VG.Proof.CmacTripleDes.X86.readW_lo_of_hi, VG.Proof.CmacTripleDes.X86.bswap_eq, VG.Proof.CmacTripleDes.X86.bswap_eq,
    byteRev32_append, ax₇, ax₆, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
    macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, Proof.Cmac.xor_comm]

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Implies`. -/
section

/-!
# TDEA-CMAC on x86: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), which `Frame.lean` moves to the
shared contracts of `Spec/Cmac/TripleDesContract.lean`.

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition: a 16-byte
key at `0x1000`, the output at `0x2000` and the scratch buffer at `0x4000`,
as stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16
    else if a = 0x800d then 0x20 else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x2000, 400⟩, ⟨0x4000, 640⟩]

theorem init_implies : initX86.Implies (initScratchContract X86.abi 0) := by
  have a0 : VG.X86.arg VG.Proof.CmacTripleDes.X86.initSat 0 = 0x1000 := by decide
  have a1 : VG.X86.arg VG.Proof.CmacTripleDes.X86.initSat 1 = 16 := by decide
  have a2 : VG.X86.arg VG.Proof.CmacTripleDes.X86.initSat 2 = 0x2000 := by decide
  have a3 : VG.X86.arg VG.Proof.CmacTripleDes.X86.initSat 3 = 0x4000 := by decide
  have e : argAddr VG.Proof.CmacTripleDes.X86.initSat 0 = 0x8004 := by decide
  have esp : initSat.gpr .esp = 0x8000 := rfl
  sig_implies [initScratchContract, initScratchSig, Spec.Cmac.tdesInitPre, Spec.Cmac.tdesInitPost,
    X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, VG.Proof.CmacTripleDes.X86.initX86] [a0, a1, a2, a3, e, esp] using VG.Proof.CmacTripleDes.X86.initSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition: the key
at `0x1000`, the state at `0x2000`, no last bytes at `0x3000` and the
scratch buffer at `0x4000`, as stack arguments at `0x8004`. -/
def finSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20
    else if a = 0x800d then 0x30 else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finalize_implies : finalizeX86.Implies (VG.Proof.CmacTripleDes.finalizeScratchContract X86.abi 0) := by
  have a0 : VG.X86.arg VG.Proof.CmacTripleDes.X86.finSat 0 = 0x1000 := by decide
  have a1 : VG.X86.arg VG.Proof.CmacTripleDes.X86.finSat 1 = 0x2000 := by decide
  have a2 : VG.X86.arg VG.Proof.CmacTripleDes.X86.finSat 2 = 0x3000 := by decide
  have a3 : VG.X86.arg VG.Proof.CmacTripleDes.X86.finSat 3 = 0 := by decide
  have a4 : VG.X86.arg VG.Proof.CmacTripleDes.X86.finSat 4 = 0x4000 := by decide
  have e : argAddr VG.Proof.CmacTripleDes.X86.finSat 0 = 0x8004 := by decide
  have esp : finSat.gpr .esp = 0x8000 := rfl
  sig_implies [VG.Proof.CmacTripleDes.finalizeScratchContract, VG.Proof.CmacTripleDes.finalizeScratchSig, Spec.Cmac.tdesFinalizePre,
    Spec.Cmac.tdesFinalizePost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, VG.Proof.CmacTripleDes.X86.finalizeX86] [a0, a1, a2, a3, a4, e, esp] using VG.Proof.CmacTripleDes.X86.finSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition: as
`finSat`, with no blocks. -/
def updSat : State := { VG.Proof.CmacTripleDes.X86.finSat with
                                    rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] }

theorem update_implies : updateX86.Implies (VG.Proof.CmacTripleDes.updateScratchContract X86.abi 0) := by
  have a0 : VG.X86.arg VG.Proof.CmacTripleDes.X86.updSat 0 = 0x1000 := by decide
  have a1 : VG.X86.arg VG.Proof.CmacTripleDes.X86.updSat 1 = 0x2000 := by decide
  have a2 : VG.X86.arg VG.Proof.CmacTripleDes.X86.updSat 2 = 0x3000 := by decide
  have a3 : VG.X86.arg VG.Proof.CmacTripleDes.X86.updSat 3 = 0 := by decide
  have a4 : VG.X86.arg VG.Proof.CmacTripleDes.X86.updSat 4 = 0x4000 := by decide
  have e : argAddr VG.Proof.CmacTripleDes.X86.updSat 0 = 0x8004 := by decide
  have esp : updSat.gpr .esp = 0x8000 := rfl
  sig_implies [VG.Proof.CmacTripleDes.updateScratchContract, VG.Proof.CmacTripleDes.updateScratchSig, Spec.Cmac.tdesUpdatePost, X86.abi,
    X86.argSlots,
    X86.argVal, X86.argBytes, VG.Proof.CmacTripleDes.X86.updateX86] [a0, a1, a2, a3, a4, e, esp] using VG.Proof.CmacTripleDes.X86.updSat

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Verified`. -/
section

/-!
# TDEA-CMAC on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time under this target's contracts (`Contract.lean`), and the shared
contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), which imply them, with no
stack: the functions call nothing, and save our caller's registers in the
scratch buffer.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86

theorem init_verified : Verified X86.target init (initScratchContract X86.abi 0) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacTripleDes.X86.init_wp hs) VG.Proof.CmacTripleDes.X86.init_ct VG.Proof.CmacTripleDes.X86.init_implies

theorem update_verified : Verified X86.target update (VG.Proof.CmacTripleDes.updateScratchContract X86.abi 0) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacTripleDes.X86.update_wp hs) VG.Proof.CmacTripleDes.X86.update_ct VG.Proof.CmacTripleDes.X86.update_implies

theorem finalize_verified : Verified X86.target finalize (VG.Proof.CmacTripleDes.finalizeScratchContract X86.abi 0) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacTripleDes.X86.finalize_wp hs) VG.Proof.CmacTripleDes.X86.finalize_ct VG.Proof.CmacTripleDes.X86.finalize_implies

end VG.Proof.CmacTripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86.Frame`. -/
section

/-!
# TDEA-CMAC on x86, with its working space on the stack

The functions run their code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it and copies the arguments
passed on the stack (`Verified.stackScratch`): the return address, the
copied arguments (three for `init`, four for the others) and the 640 bytes
of working space. The copies are read only where the pre- and
postconditions read the buffers (`Proof/CmacTripleDes/Scratch.lean`).
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition, without the
working space: a 16-byte key at `0x1000` and the output at `0x2000`, as
stack arguments at `0x8004`. -/
def initFrameSat : State :=
  { VG.Proof.CmacTripleDes.X86.initSat with
                 rd := [⟨0x1000, 16⟩, ⟨0x8004, 12⟩], wr := [⟨0x2000, 400⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesInitContract X86.abi 660).pre s := by
  implies_sat [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, Spec.Cmac.tdesInitPre,
    Spec.Cmac.tdesInitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.CmacTripleDes.X86.initFrameSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition, without
the working space: the key at `0x1000`, the state at `0x2000` and no last
bytes at `0x3000`, as stack arguments at `0x8004`. -/
def finFrameSat : State :=
  { VG.Proof.CmacTripleDes.X86.finSat with
                rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩, ⟨0x8004, 16⟩], wr := [⟨0x2000, 8⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinalizeContract X86.abi 664).pre s := by
  implies_sat [Spec.Cmac.tdesFinalizeContract, Spec.Cmac.tdesFinalizeSig, Spec.Cmac.tdesFinalizePre,
    Spec.Cmac.tdesFinalizePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.CmacTripleDes.X86.finFrameSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition, without
the working space: as `finFrameSat`, with no blocks. -/
def updFrameSat : State :=
  { VG.Proof.CmacTripleDes.X86.finSat with
                rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩, ⟨0x8004, 16⟩], wr := [⟨0x2000, 8⟩] }

theorem updFrameSat_pre : ∃ s, (Spec.Cmac.tdesUpdateContract X86.abi 664).pre s := by
  implies_sat [Spec.Cmac.tdesUpdateContract, Spec.Cmac.tdesUpdateSig, Spec.Cmac.tdesUpdatePost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updFrameSat, finSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.CmacTripleDes.X86.updFrameSat

theorem init_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 660 3 init)
    (Spec.Cmac.tdesInitContract X86.abi 660) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesInitPre X86.abi.ptrBits) (post := Spec.Cmac.tdesInitPost X86.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 660) VG.Proof.CmacTripleDes.X86.init_verified (by decide) (by lit_decide) (by lit_decide)
    (initPre_local _) (initPost_local _) VG.Proof.CmacTripleDes.X86.initFrameSat_pre

theorem update_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 664 4 update)
    (Spec.Cmac.tdesUpdateContract X86.abi 664) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesUpdateSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesUpdatePost X86.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 664) VG.Proof.CmacTripleDes.X86.update_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (VG.Proof.CmacTripleDes.updatePost_local _) VG.Proof.CmacTripleDes.X86.updFrameSat_pre

theorem finalize_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 664 4 finalize)
    (Spec.Cmac.tdesFinalizeContract X86.abi 664) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesFinalizeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesFinalizePre X86.abi.ptrBits)
    (post := Spec.Cmac.tdesFinalizePost X86.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 664) VG.Proof.CmacTripleDes.X86.finalize_verified (by decide) (by lit_decide)
    (by lit_decide) (finalizePre_local _) (VG.Proof.CmacTripleDes.finalizePost_local _) VG.Proof.CmacTripleDes.X86.finFrameSat_pre

end VG.Proof.CmacTripleDes.X86

end
