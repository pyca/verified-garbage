module

public import VerifiedGarbage.Proof.MdStream.X86.Common
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Impl.CmacTripleDes.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.CmacTripleDes.X86.Contract
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacTripleDes.Des
public import VerifiedGarbage.Proof.CmacTripleDes.Rows
public import VerifiedGarbage.Proof.Framework.X86.Linear
public import VerifiedGarbage.Proof.Framework.Bitslice.Rows
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
public import VerifiedGarbage.Impl.CmacTripleDes.X86.Round
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.Framework.X86.Wp

/-! ### `CmacTripleDes.X86.Block`, which this module and modules that import it used -/

section

/-! ### `CmacTripleDes.X86.Round`, which only this module used -/

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

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86

/-- The round's memory: slots 0–17 at `ebp`, and the round key's two words
at `esi`. -/
def rCfg : Cfg := { base := .ebp, slots := 18, ext := .esi, exts := 2 }

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .ebp) k) 32

/-- The round key's words. -/
abbrev keyLo (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esi) 0) 32
abbrev keyHi (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esi) 1) 32

/-- The round key: the low 16 bits of its high word, and its low word. -/
abbrev key48 (s : State) : BitVec 48 := (keyHi s).setWidth 16 ++ keyLo s

/-! ## The inputs -/

/-- Bit `b` of the round key, as an atom: of its low word (input word 1) or
its high word (input word 2). -/
def keyAtom (b : Nat) : Nat := if b < 32 then 32 + b else 64 + (b - 32)

/-- Bit `p` of input slot `t` (half `t / 6`, input bit `t % 6`): in lane `p / 6`,
below its fifth bit, `R`'s bit (atom `0 … 31`) XOR the key's. -/
def inG (t p : Nat) : List Nat :=
  if p < 24 ∧ p % 6 < 4 then
    [expSrc (24 * (t / 6) + 6 * (p / 6) + t % 6), keyAtom (24 * (t / 6) + 6 * (p / 6) + t % 6)]
  else []

/-- The slot of input `t`. -/
def inSlot (t : Nat) : Nat := 7 * (t / 6) + t % 6

/-- The inputs' slots, and `L` and `R` (input words 3 and 0) kept. -/
def inOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 12).map (fun t => (inSlot t, inG t)) ++ [(slotL, fun p => [96 + p]), (slotR, fun p => [p])]

theorem inputs_check :
    check (lanes 32 7) rCfg (linExt 1) inputs (linEnv [(slotR, 0), (slotL, 3)]) (linPost rCfg.slots 7 inOuts) =
      true := by
  lit_decide

/-! ## The S-boxes -/

/-- Slot `t` on row `c`, at every position: bit `t % 7` of `c`. -/
def rowIn (t : Nat) : Nat := rowsOf 32 (fun c => c.testBit (t % 7)) 64

/-- Half `h`'s input slots. -/
def sbEnv (h : Nat) : Env Nat :=
  { reg := fun _ => none, slot := fun t => if 7 * h ≤ t ∧ t < 7 * h + 6 then some (rowIn t) else none }

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

theorem sbox0_check : check (rows 32 6) (sCfg 0) (fun _ => none) (tree 0) (sbEnv 0) (sbPost 0) = true := by
  lit_decide

theorem sbox1_check : check (rows 32 6) (sCfg 1) (fun _ => none) (tree 1) (sbEnv 1) (sbPost 1) = true := by
  lit_decide

/-! ## The output -/

/-- The atom of output bit `u` of the S-boxes: bit `outPos u` of half 0's
outputs (slot 14, input word 0) or of half 1's (slot 15, input word 1). -/
def sAtom (u : Nat) : Nat := if outHalf u = 0 then outPos u else 32 + outPos u

/-- Slot `R`: bit `j` of `L` (input word 2) XOR the S-boxes' bit `pSrc j`. -/
def oGR (p : Nat) : List Nat := if p < 32 then [sAtom (pSrc p), 64 + p] else [64 + p]

/-- Slot `L` gets `R` (input word 3), slot `R` `L ⊕ P(S)`. -/
def oOuts : List (Nat × (Nat → List Nat)) := [(slotL, fun p => [96 + p]), (slotR, oGR)]

/-- The output's slots. -/
def oCfg : Cfg := { base := .ebp, slots := 18, ext := .esi, exts := 0 }

theorem output_check :
    check (lanes 32 7) oCfg (linExt 0) output (linEnv [(14, 0), (15, 1), (slotL, 2), (slotR, 3)])
      (linPost oCfg.slots 7 oOuts) = true := by
  lit_decide

/-! ## Machine facts -/

theorem runBlock_append (a b : List Instr) (s : State) :
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
  rw [wordAddr_eq b (by omega_arith)]
  refine hf.readW (r := ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

/-- Words `j` and `k` of the slots are apart. -/
theorem slot_word_sep (b : BitVec 32) {j k : Nat} (h : j ≠ k) (hj : b.toNat + 4 * j + 4 ≤ 2 ^ 32)
    (hk : b.toNat + 4 * k + 4 ≤ 2 ^ 32) : Mem.Sep (wordAddr b j) (32 / 8) (wordAddr b k) (32 / 8) := by
  rw [wordAddr_eq b (by omega_arith), wordAddr_eq b (by omega_arith)]
  exact Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- `mov [b + o], r`, run. -/
theorem runBlock_store {s : State} {b r : Reg} {o : Nat} (hout : InRegions s.wr (addr (s.gpr b) o) 4) :
    runBlock isa [.store ⟨b, o⟩ r] s = some { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.gpr r) } := by
  rw [runBlock_cons, show exec (.store ⟨b, o⟩ r) s = some { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.gpr r) }
    by simp [exec, State.store32, ea_mk, hout], runStep_some, runBlock_nil]

/-! ## The inputs, on the machine -/

/-- The inputs of `inputs`: `R`, the round key's words and `L`. -/
def inW (s : State) (i : Nat) : BitVec 32 :=
  if i = 0 then slotW s slotR else if i = 1 then keyLo s else if i = 2 then keyHi s else slotW s slotL

/-- The registers the round keeps. -/
def kept : List Reg := [.esp, .esi, .ebp]

theorem inputs_kept : kept.all (fun r => inputs.all fun i => i.dst != some r) = true := by lit_decide

theorem slot_bits {x y : BitVec 32} (h : ∀ p < 32, x.getLsbD p = y.getLsbD p) : x = y :=
  BitVec.eq_of_getLsbD_eq fun p hp => h p hp

theorem inputs_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa inputs s = some s' ∧
      (∀ t < 12, ∀ p < 32, (slotW s' (inSlot t)).getLsbD p = xorBits (inW s) (inG t p)) ∧
      slotW s' slotL = slotW s slotL ∧ slotW s' slotR = slotW s slotR ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rd, wr, keep, fr⟩ := linear_ok inputs_check hok (inW s)
    (fun j i h hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨by decide, rfl⟩
      · exact ⟨by decide, rfl⟩)
    (fun j hj => by
      simp only [rCfg] at hj
      rcases (by omega_arith : j = 0 ∨ j = 1) with rfl | rfl
      · exact ⟨by decide, rfl⟩
      · exact ⟨by decide, rfl⟩)
  obtain kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => keep _ (List.all_eq_true.mp inputs_kept r hr)
  obtain e10 : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  obtain bit : ∀ j g, (j, g) ∈ inOuts → ∀ p < 32, (slotW s' j).getLsbD p = xorBits (inW s) (g p) := fun j g h p hp => by
    rw [slotW, e10]; exact hout j g h p hp
  refine ⟨s', hs', fun t ht p hp => bit _ _ (List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
    p hp, slot_bits fun p hp => ?_, slot_bits fun p hp => ?_, rd, wr, kp, fr⟩
  · rw [bit slotL _ (List.mem_append_right _ (List.mem_cons_self ..)) p hp]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, inW, show (96 + p) / 32 = 3 by omega_arith,
      show (96 + p) % 32 = p by omega_arith]
    rfl
  · rw [bit slotR _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) p hp]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, inW, Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
    rfl

/-! ## The S-boxes, on the machine -/

theorem tree_kept (h : Nat) (hh : h < 2) : kept.all (fun r => (tree h).all fun i => i.dst != some r) = true := by
  rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;> lit_decide

/-- The input of the box whose lane of half `h` holds bit `p`, from bit `p`
of the slots. -/
def boxIn (h : Nat) (s : State) (p : Nat) : BitVec 6 := ofBits 6 fun t => (slotW s (7 * h + t)).getLsbD p

theorem off_lt4 : ∀ h < 2, ∀ j < 4, ∀ b < 4, off (boxOf h j) b < 4 := by decide

theorem sbox_ok {h : Nat} (hh : h < 2) {s : State} (hok : Ok (sCfg h) s) :
    ∃ s', runBlock isa (tree h) s = some s' ∧
      (∀ j < 4, ∀ b < 4, (s'.gpr .ebx).getLsbD (6 * j + off (boxOf h j) b) =
        (Spec.TripleDes.sBox (boxOf h j) (boxIn h s (6 * j + off (boxOf h j) b))).getLsbD b) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion (sCfg h) s] s.mem s'.mem := by
  obtain hchk : check (rows 32 6) (sCfg h) (fun _ => none) (tree h) (sbEnv h) (sbPost h) = true := by
    rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl
    · exact sbox0_check
    · exact sbox1_check
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain ⟨F, hF, hout⟩ : ∃ F, e'.reg .ebx = some F ∧ ∀ j < 4, ∀ b < 4, ∀ c < 64,
      F.testBit (32 * c + (6 * j + off (boxOf h j) b)) =
        (Spec.TripleDes.sBox (boxOf h j) (BitVec.ofNat 6 c)).getLsbD b := by
    simp only [sbPost] at hpost
    split at hpost
    · rename_i F hF
      refine ⟨F, hF, fun j hj b hb c hc => ?_⟩
      have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hpost j
        (List.mem_range.mpr hj)) b (List.mem_range.mpr hb)) c (List.mem_range.mpr hc)
      rw [← Proof.TripleDes.testBit_outputTable hc]
      simpa using this
    · cases hpost
  obtain key : ∀ p < 32, ∃ s', runBlock isa (tree h) s = some s' ∧
      Post (RowRel p (boxIn h s p).toNat) (sCfg h) (fun _ => none) e' s s'
        (fun r => ((tree h).all fun i => i.dst != some r) = false) := by
    intro p hp
    refine run (rows_sound hp (boxIn h s p).isLt) hok
      ⟨fun r a h => by simp [sbEnv] at h, fun t a ht h' => ?_, fun _ _ _ h => by cases h⟩ he
    simp only [sbEnv] at h'
    split at h'
    · rename_i ht6
      cases h'
      show (rowIn t).testBit (32 * (boxIn h s p).toNat + p) = (slotW s t).getLsbD p
      obtain hc := (boxIn h s p).isLt
      obtain ⟨u, rfl, hu⟩ : ∃ u, t = 7 * h + u ∧ u < 6 := ⟨t - 7 * h, by omega_arith, by omega_arith⟩
      rw [rowIn, testBit_rowsOf, decide_eq_true (by omega_arith : 32 * (boxIn h s p).toNat + p < 32 * 64),
        Bool.true_and, show (32 * (boxIn h s p).toNat + p) / 32 = (boxIn h s p).toNat by omega_arith,
        BitVec.testBit_toNat, boxIn, getLsbD_ofBits, show (7 * h + u) % 7 = u by omega_arith,
        decide_eq_true hu, Bool.true_and]
    · cases h'
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_arith)
  refine ⟨s', hs', fun j hj b hb => ?_, p₀.rd, p₀.wr,
    fun r hr => p₀.other r (by simp [List.all_eq_true.mp (tree_kept h hh) r hr]), p₀.frame⟩
  obtain hp : 6 * j + off (boxOf h j) b < 32 := by have := off_lt4 h hh j hj b hb; omega_arith
  obtain ⟨s'', hs'', p₁⟩ := key _ hp
  obtain rfl := run_unique hs'' hs'
  obtain h' := p₁.rel.reg .ebx F hF
  simp only [RowRel] at h'
  rw [← h', hout j hj b hb _ (boxIn h s _).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## The output, on the machine -/

/-- The inputs of `output`: the halves' outputs, `L` and `R`. -/
def oW (s : State) (i : Nat) : BitVec 32 :=
  if i = 0 then slotW s 14 else if i = 1 then slotW s 15 else if i = 2 then slotW s slotL else slotW s slotR

theorem output_kept : kept.all (fun r => output.all fun i => i.dst != some r) = true := by lit_decide

theorem output_ok {s : State} (hok : Ok oCfg s) :
    ∃ s', runBlock isa output s = some s' ∧
      slotW s' slotL = slotW s slotR ∧
      (∀ p < 32, (slotW s' slotR).getLsbD p = xorBits (oW s) (oGR p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion oCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rd, wr, keep, fr⟩ := linear_ok output_check hok (oW s)
    (fun j i h hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  obtain kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => keep _ (List.all_eq_true.mp output_kept r hr)
  obtain e10 : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  obtain bit : ∀ j g, (j, g) ∈ oOuts → ∀ p < 32, (slotW s' j).getLsbD p = xorBits (oW s) (g p) := fun j g h p hp => by
    rw [slotW, e10]; exact hout j g h p hp
  refine ⟨s', hs', slot_bits fun p hp => ?_, fun p hp => bit _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) p hp,
    rd, wr, kp, fr⟩
  rw [bit slotL _ (List.mem_cons_self ..) p hp]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, oW, show (96 + p) / 32 = 3 by omega_arith,
    show (96 + p) % 32 = p by omega_arith]
  rfl

/-! ## The round -/

theorem expSrc_lt : ∀ q < 48, expSrc q < 32 := by lit_decide

theorem pSrc_lt : ∀ j < 32, pSrc j < 32 := by lit_decide

/-- The box inputs that `inputs` broadcasts. -/
theorem boxIn_eq {s s₁ : State}
    (hx : ∀ t < 12, ∀ p < 32, (slotW s₁ (inSlot t)).getLsbD p = xorBits (inW s) (inG t p))
    {h j o : Nat} (hh : h < 2) (hj : j < 4) (ho : o < 4) :
    boxIn h s₁ (6 * j + o) = chunk (slotW s slotR) (key48 s) (boxOf h j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  obtain hb : 6 * (7 - boxOf h j) = 24 * h + 6 * j := by simp only [boxOf]; omega_arith
  obtain hE := expSrc_lt (24 * h + 6 * j + t) (by omega_arith)
  obtain hs : 7 * h + t = inSlot (6 * h + t) := by simp only [inSlot]; omega_arith
  rw [boxIn, getLsbD_ofBits, decide_eq_true ht, Bool.true_and, hs, hx (6 * h + t) (by omega_arith) _ (by omega_arith),
    getLsbD_chunk _ _ (by simp only [boxOf]; omega_arith) ht, inG, ite_eq_left (by omega_arith), hb,
    show (6 * h + t) / 6 = h by omega_arith, show (6 * h + t) % 6 = t by omega_arith, show (6 * j + o) / 6 = j by omega_arith]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, inW, keyAtom]
  rw [Nat.div_eq_of_lt (show expSrc (24 * h + 6 * j + t) < 32 by omega_arith),
    Nat.mod_eq_of_lt (show expSrc (24 * h + 6 * j + t) < 32 by omega_arith), ite_eq_left rfl]
  congr 1
  rw [BitVec.getLsbD_append]
  by_cases h32 : 24 * h + 6 * j + t < 32
  · rw [ite_eq_left h32, ite_eq_left h32, show (32 + (24 * h + 6 * j + t)) / 32 = 1 by omega_arith,
      show (32 + (24 * h + 6 * j + t)) % 32 = 24 * h + 6 * j + t by omega_arith]
    rfl
  · rw [ite_eq_right h32, ite_eq_right h32, show (64 + (24 * h + 6 * j + t - 32)) / 32 = 2 by omega_arith,
      show (64 + (24 * h + 6 * j + t - 32)) % 32 = 24 * h + 6 * j + t - 32 by omega_arith,
      BitVec.getLsbD_setWidth, decide_eq_true (by omega_arith : 24 * h + 6 * j + t - 32 < 16), Bool.true_and]
    rfl

/-- The slots of a configuration on fewer slots, with no external words. -/
theorem ok_fewer {c c' : Cfg} {s : State} (h : Ok c s) (hb : c'.base = c.base) (hn : c'.slots ≤ c.slots)
    (he : c'.exts = 0) : Ok c' s :=
  ⟨fun k hk => by rw [hb]; exact h.slotIn k (by omega_arith), fun k hk => absurd hk (by omega_arith),
    by rw [hb]; have := h.fit; omega_arith, fun k _ j hj => absurd hj (by omega_arith)⟩

/-- One round: `(L, R) := (R, L ⊕ f(R, K))` on slots `L` and `R`, with the
round key at `esi`. -/
theorem round_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa round s = some s' ∧
      slotW s' slotL = slotW s slotR ∧
      slotW s' slotR = slotW s slotL ^^^ Spec.TripleDes.roundFunction (slotW s slotR) (key48 s) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  have hfit := hok.fit
  simp only [rCfg] at hfit
  obtain hb : ∀ k ≤ 17, (s.gpr .ebp).toNat + 4 * k + 4 ≤ 2 ^ 32 := fun k hk => by omega_arith
  obtain ⟨s₁, h₁, hx, L₁, R₁, rd₁, wr₁, k₁, f₁⟩ := inputs_ok hok
  obtain e₁ : s₁.gpr .ebp = s.gpr .ebp := k₁ _ (by simp [kept])
  obtain i₁ : s₁.gpr .esi = s.gpr .esi := k₁ .esi (by simp [kept])
  obtain hok₁ : Ok rCfg s₁ := hok.congr e₁ i₁ rd₁ wr₁
  obtain ⟨s₂, h₂, y₂, rd₂, wr₂, k₂, f₂⟩ := sbox_ok (h := 0) (by decide) (ok_fewer hok₁ rfl (by decide) rfl)
  obtain e₂ : s₂.gpr .ebp = s.gpr .ebp := (k₂ _ (by simp [kept])).trans e₁
  -- Half 0's outputs to slot 14.
  obtain w14 : InRegions s₂.wr (addr (s₂.gpr .ebp) (4 * 14)) 4 := by
    rw [wr₂, e₂, ← e₁]; exact hok₁.slotIn 14 (by decide)
  let s₃ : State := { s₂ with mem := s₂.mem.writeW (addr (s₂.gpr .ebp) (4 * 14)) (s₂.gpr .ebx) }
  obtain h₃ : runBlock isa [.store (at_ .ebp (4 * 14)) .ebx] s₂ = some s₃ := runBlock_store w14
  have e₃ : s₃.gpr .ebp = s.gpr .ebp := e₂
  obtain ⟨s₄, h₄, y₄, rd₄, wr₄, k₄, f₄⟩ := sbox_ok (h := 1) (by decide)
    (ok_fewer (hok₁.congr (e₃.trans e₁.symm) (show s₃.gpr .esi = s₁.gpr .esi from k₂ .esi (by simp [kept]))
      (rd₂ : s₃.rd = s₁.rd) (wr₂ : s₃.wr = s₁.wr)) rfl (by decide) rfl)
  obtain e₄ : s₄.gpr .ebp = s.gpr .ebp := (k₄ _ (by simp [kept])).trans e₃
  obtain w15 : InRegions s₄.wr (addr (s₄.gpr .ebp) (4 * 15)) 4 := by
    rw [wr₄, show s₃.wr = s₁.wr from wr₂, e₄, ← e₁]; exact hok₁.slotIn 15 (by decide)
  let s₅ : State := { s₄ with mem := s₄.mem.writeW (addr (s₄.gpr .ebp) (4 * 15)) (s₄.gpr .ebx) }
  obtain h₅ : runBlock isa [.store (at_ .ebp (4 * 15)) .ebx] s₄ = some s₅ := runBlock_store w15
  have e₅ : s₅.gpr .ebp = s.gpr .ebp := e₄
  obtain rd₅ : s₅.rd = s₁.rd := rd₄.trans rd₂
  obtain wr₅ : s₅.wr = s₁.wr := wr₄.trans wr₂
  obtain ⟨s₆, h₆, L₆, R₆, rd₆, wr₆, k₆, f₆⟩ := output_ok
    (ok_fewer (hok₁.congr (e₅.trans e₁.symm) (show s₅.gpr .esi = s₁.gpr .esi from
      (k₄ .esi (by simp [kept])).trans (k₂ .esi (by simp [kept]))) rd₅ wr₅) rfl (by decide) rfl)
  -- The slots along the way.
  obtain sep : ∀ j k, j ≠ k → j ≤ 17 → k ≤ 17 →
      Mem.Sep (wordAddr (s.gpr .ebp) j) (32 / 8) (wordAddr (s.gpr .ebp) k) (32 / 8) :=
    fun j k h hj hk => slot_word_sep _ h (hb j hj) (hb k hk)
  obtain st₃ : ∀ k, k ≠ 14 → k ≤ 17 → slotW s₃ k = slotW s₂ k := fun k hk hk' => by
    show (s₂.mem.writeW (wordAddr (s₂.gpr .ebp) 14) (s₂.gpr .ebx)).readW (wordAddr (s₂.gpr .ebp) k) 32 =
      s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32
    rw [e₂, Mem.readW_writeW_sep (sep k 14 hk hk' (by decide)) (by decide)]
  obtain st₅ : ∀ k, k ≠ 15 → k ≤ 17 → slotW s₅ k = slotW s₄ k := fun k hk hk' => by
    show (s₄.mem.writeW (wordAddr (s₄.gpr .ebp) 15) (s₄.gpr .ebx)).readW (wordAddr (s₄.gpr .ebp) k) 32 =
      s₄.mem.readW (wordAddr (s₄.gpr .ebp) k) 32
    rw [e₄, Mem.readW_writeW_sep (sep k 15 hk hk' (by decide)) (by decide)]
  obtain fr₂ : ∀ k, 7 ≤ k → k ≤ 17 → slotW s₂ k = slotW s₁ k := fun k h₁' h₂' => by
    show s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32 = s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32
    rw [e₂, ← e₁]
    exact slot_frame (n := 7) f₂ h₁' (by rw [e₁]; exact hb k h₂')
  obtain fr₄ : ∀ k, 14 ≤ k → k ≤ 17 → slotW s₄ k = slotW s₃ k := fun k h₁' h₂' => by
    show s₄.mem.readW (wordAddr (s₄.gpr .ebp) k) 32 = s₃.mem.readW (wordAddr (s₃.gpr .ebp) k) 32
    rw [e₄, ← e₃]
    exact slot_frame (n := 14) f₄ h₁' (by rw [e₃]; exact hb k h₂')
  obtain slotLR : ∀ k, 16 ≤ k → k ≤ 17 → slotW s₅ k = slotW s k := fun k h₁' h₂' => by
    rw [st₅ k (by omega_arith) h₂', fr₄ k (by omega_arith) h₂', st₃ k (by omega_arith) h₂', fr₂ k (by omega_arith) h₂']
    rcases (by omega_arith : k = 16 ∨ k = 17) with rfl | rfl
    · exact L₁
    · exact R₁
  obtain slot14 : slotW s₅ 14 = s₂.gpr .ebx := by
    rw [st₅ 14 (by decide) (by decide), fr₄ 14 (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  obtain slot15 : slotW s₅ 15 = s₄.gpr .ebx := Mem.readW_writeW_self32 _ _ _
  obtain box₄ : ∀ p, boxIn 1 s₃ p = boxIn 1 s₁ p := fun p => by
    apply BitVec.eq_of_getLsbD_eq
    intro t ht
    rw [boxIn, boxIn, getLsbD_ofBits, getLsbD_ofBits]
    by_cases ht6 : t < 6
    · rw [st₃ (7 * 1 + t) (by omega_arith) (by omega_arith), fr₂ (7 * 1 + t) (by omega_arith) (by omega_arith)]
    · simp [ht6]
  refine ⟨s₆, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [round, runBlock_append, runBlock_append, h₁, Option.bind_some, sboxes, runBlock_append, runBlock_append,
      runBlock_append, h₂, Option.bind_some, h₃, Option.bind_some, h₄, Option.bind_some, h₅, Option.bind_some, h₆]
  · rw [L₆, slotLR slotR (by decide) (by decide)]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    obtain hu := pSrc_lt j hj
    rw [R₆ j hj, oGR, ite_eq_left hj, BitVec.getLsbD_xor, getLsbD_roundFunction _ _ hj, xorBits_cons,
      xorBits_cons, xorBits_nil, Bool.xor_false]
    obtain hL : bitOf (oW s₅) (64 + j) = (slotW s slotL).getLsbD j := by
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, bitOf, oW, show (64 + j) / 32 = 2 by omega_arith,
        show (64 + j) % 32 = j by omega_arith]
      rw [slotLR slotL (by decide) (by decide)]
    rw [hL, Bool.xor_comm]
    congr 1
    obtain ⟨b, hb', hbe⟩ : ∃ b, b < 4 ∧ pSrc j % 4 = b := ⟨_, Nat.mod_lt _ (by decide), rfl⟩
    by_cases hh : pSrc j / 4 < 4
    · -- Half 0, in slot 14.
      obtain hi : boxOf 0 (pSrc j / 4) = 7 - pSrc j / 4 := by simp [boxOf]
      obtain ho := off_lt4 0 (by decide) _ hh b hb'
      obtain hpos : sAtom (pSrc j) = 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b := by
        rw [sAtom, outHalf, ite_eq_left hh, ite_eq_left rfl, outPos, hi, Nat.mod_eq_of_lt hh, hbe]
      obtain hbit : bitOf (oW s₅) (sAtom (pSrc j)) =
          (slotW s₅ 14).getLsbD (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b) := by
        rw [hpos]
        simp only [↓reduceIte, bitOf, oW,
          Nat.div_eq_of_lt (show 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b < 32 by omega_arith),
          Nat.mod_eq_of_lt (show 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b < 32 by omega_arith)]
      rw [hbit, slot14, y₂ _ hh b hb', boxIn_eq hx (by decide) hh ho, hi]
      simp only [hbe]
    · -- Half 1, in slot 15.
      obtain hm : pSrc j / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
      obtain hi : boxOf 1 (pSrc j / 4 % 4) = 7 - pSrc j / 4 := by simp only [boxOf]; omega_arith
      obtain ho := off_lt4 1 (by decide) _ hm b hb'
      obtain hpos : sAtom (pSrc j) = 32 + (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b) := by
        rw [sAtom, outHalf, ite_eq_right hh, ite_eq_right (by decide), outPos, hi, hbe]
      obtain hbit : bitOf (oW s₅) (sAtom (pSrc j)) =
          (slotW s₅ 15).getLsbD (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b) := by
        rw [hpos]
        simp only [reduceCtorEq, ↓reduceIte, bitOf, oW,
          show (32 + (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b)) / 32 = 1 by omega_arith,
          show (32 + (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b)) % 32 =
            6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b by omega_arith]
      rw [hbit, slot15, y₄ _ hm b hb', box₄, boxIn_eq hx (by decide) hm ho, hi]
      simp only [hbe]
  · rw [rd₆, rd₅]; exact rd₁
  · rw [wr₆, wr₅]; exact wr₁
  · rw [k₆ r hr, show s₅.gpr r = s₄.gpr r from rfl, k₄ r hr, show s₃.gpr r = s₂.gpr r from rfl, k₂ r hr, k₁ r hr]
  · have R : ∀ (c : Cfg) (t : State), c.base = .ebp → c.slots ≤ 18 → t.gpr .ebp = s.gpr .ebp →
        ∀ r ∈ [slotRegion c t], ∃ r' ∈ [slotRegion rCfg s], Region.Sub r r' := fun c t hc hn ht r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [slotRegion, hc, ht]
      exact Region.sub_prefix (by simp only [rCfg]; omega_arith)
    obtain cw : ∀ k ≤ 17, (slotRegion rCfg s).Contains (wordAddr (s.gpr .ebp) k) (32 / 8) := fun k hk => by
      rw [wordAddr_eq _ (by omega_arith)]
      exact Offset.contains_base _ (by simp only [rCfg]; omega_arith) (by omega_arith)
    obtain f₃ : Frame [slotRegion rCfg s] s₂.mem s₃.mem := by
      show Frame _ s₂.mem (s₂.mem.writeW (wordAddr (s₂.gpr .ebp) 14) _)
      rw [e₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 14 (by decide))
    obtain f₅ : Frame [slotRegion rCfg s] s₄.mem s₅.mem := by
      show Frame _ s₄.mem (s₄.mem.writeW (wordAddr (s₄.gpr .ebp) 15) _)
      rw [e₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 15 (by decide))
    exact ((((f₁.trans (f₂.sub (R _ _ rfl (by decide) e₁))).trans f₃).trans
      (f₄.sub (R _ _ rfl (by decide) e₃))).trans f₅).trans (f₆.sub (R _ _ rfl (by decide) e₅))

end VG.Proof.CmacTripleDes.X86

end

end


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

@[expose] public section

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
  frame : Frame [xR s₀] s₀.mem s.mem

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
  have := contains_word (r := ⟨b.setWidth 64, len⟩) (b := b) (off := 0) (k := k) (n := len) rfl hfit (by omega_arith)
    (Nat.le_refl _)
  rwa [add_zero32] at this

theorem contains_w_off {b : BitVec 32} {len off k : Nat} (hfit : b.toNat + len ≤ 2 ^ 32)
    (h : off + 4 * k + 4 ≤ len) :
    (⟨b.setWidth 64, len⟩ : Region).Contains (wordAddr (b + BitVec.ofNat 32 off) k) 4 :=
  contains_word rfl hfit h (Nat.le_refl _)

theorem wordAddr_off (b : BitVec 32) {off k : Nat} (h : b.toNat + off + 4 * k < 2 ^ 32) :
    wordAddr (b + BitVec.ofNat 32 off) k = b.setWidth 64 + BitVec.ofNat 64 (off + 4 * k) := by
  rw [wordAddr, addr_add_ofNat, addr_eq (by omega_arith)]

theorem ok_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * n)) : Ok rCfg s := by
  obtain ⟨lR, hR, hRl, hRw⟩ := hp.sched
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, ?_, fun k hk' j hj => ?_⟩
  · simp only [rCfg] at hk'
    rw [h.wr, show rCfg.base = .ebp from rfl, h.ebp, ← add_zero32 (s₀.gpr .ebp)]
    exact in_word hX hXw (by omega_arith)
  · simp only [rCfg] at hk'
    rw [h.rd, h.wr, show rCfg.ext = .esi from rfl, hk]
    exact in_word hR hRw (by omega_arith)
  · show (s.gpr .ebp).toNat + 4 * 18 ≤ 2 ^ 32
    rw [h.ebp]; omega_arith
  · simp only [rCfg] at hk' hj
    rw [show rCfg.base = .ebp from rfl, show rCfg.ext = .esi from rfl, h.ebp, hk]
    exact hp.disj.sep (contains_w (by omega_arith) (by omega_arith)) (contains_w_off (len := 384) (by omega_arith) (by omega_arith))

theorem key_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * n)) : key48 s = ((sch s₀).getD n 0).setWidth 48 := by
  obtain ⟨lR, hR, hRl, hRw⟩ := hp.sched
  rw [scheduleAt_getD _ _ hn, setWidth48_readW]
  obtain rd : ∀ d, d + 4 ≤ 384 → s.mem.readW ((s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 32 =
      s₀.mem.readW ((s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 32 := fun d hd =>
    h.frame.readW (r := ⟨(s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.disj.symm.sub_left (Offset.sub_base _ hd)) (by decide)
  rw [key48, keyLo, keyHi, hk, wordAddr_off _ (by omega_arith), wordAddr_off _ (by omega_arith), rd _ (by omega_arith),
    rd _ (by omega_arith), Offset.add_add, show 8 * n + 4 * 0 = 8 * n by omega_arith]

/-! ## The rounds of a pass -/

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

/-- The distance from one round key to the next in pass `p`. -/
def stride (p : Nat) : BitVec 32 := if p % 2 = 1 then BitVec.ofNat 32 (2 ^ 32 - 8) else BitVec.ofNat 32 8

theorem kpos_succ_addr (a : BitVec 32) {p j : Nat} (hp : p < 3) (hj : j < 16) :
    a + BitVec.ofNat 32 (8 * kpos p j) + stride p = a + BitVec.ofNat 32 (8 * kpos p (j + 1)) := by
  rw [BitVec.add_assoc, stride, kpos, kpos]
  congr 1
  split
  · rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  · rw [← BitVec.ofNat_add]
    congr 1

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

/-- After `j` rounds of pass `p`, from the halves `lr`. -/
structure PInv (s₀ : State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : State) : Prop where
  same : Same s₀ s
  esi : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * kpos p j)
  step : slotW s slotStep = stride p
  pcnt : slotW s slotPasses = BitVec.ofNat 32 (3 - p)
  rcnt : slotW s slotRounds = BitVec.ofNat 32 (16 - j)
  halves : (slotW s slotL, slotW s slotR) = rounds (passKeys (sch s₀) p) j lr

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : kpos p j < 48 := by
  simp only [kpos]; split <;> omega_arith

theorem passKeys_at (s₀ : State) {p j : Nat} (hj : j < 16) :
    passKeys (sch s₀) p j = ((sch s₀).getD (kpos p j) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega_arith]
  · rw [ite_eq_right h, ite_eq_right h]

/-- The scratch buffer's word `k` (of 21) is inside it. -/
theorem BlockPre.slotIn {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {k : Nat} (hk : k < 21) :
    InRegions s.wr (addr (s.gpr .ebp) (4 * k)) 4 := by
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr
  rw [h.wr, h.ebp, ← add_zero32 (s₀.gpr .ebp)]
  exact in_word hX hXw (by omega_arith)

theorem BlockPre.slotIn' {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {k : Nat} (hk : k < 21) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (4 * k)) 4 := by
  obtain ⟨r, hr, hc⟩ := hp.slotIn h hk
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem BlockPre.fit {s₀ : State} (hp : BlockPre s₀) : (s₀.gpr .ebp).toNat + 84 ≤ 2 ^ 32 := by
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr; omega_arith

/-- Slots `j` and `k` are apart. -/
theorem slot_ne {s₀ : State} (hp : BlockPre s₀) {j k : Nat} (h : j ≠ k) (hj : j < 21) (hk : k < 21) :
    Mem.Sep (wordAddr (s₀.gpr .ebp) j) (32 / 8) (wordAddr (s₀.gpr .ebp) k) (32 / 8) :=
  slot_word_sep _ h (by have := hp.fit; omega_arith) (by have := hp.fit; omega_arith)

/-- The frame of the block's words, after a write of one of them. -/
theorem Same.write {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {k : Nat} (hk : k < 21) (v : BitVec 32) :
    Frame [xR s₀] s₀.mem (s.mem.writeW (wordAddr (s₀.gpr .ebp) k) v) :=
  h.frame.writeW (List.mem_singleton_self _) _ (contains_word rfl (by have := hp.fit; omega_arith)
    (show 0 + 4 * k + 4 ≤ 84 by omega_arith) (Nat.le_refl _) |> fun c => by rwa [add_zero32] at c)

/-- One round of pass `p`. -/
theorem roundStep_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {j : Nat} (hj : j < 16) {s : State} (h : PInv s₀ p lr j s) :
    WP isa (.block (round ++ roundTail)) s fun s' => s'.zf = some (decide (j + 1 = 16)) ∧ PInv s₀ p lr (j + 1) s' := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, h₁, eL, eR, rd₁, wr₁, k₁, f₁⟩ := round_ok (ok_at hp h.same (kpos_lt hp3 hj) h.esi)
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  obtain e₁ : s₁.gpr .ebp = s₀.gpr .ebp := (k₁ .ebp (by simp [kept])).trans h.same.ebp
  obtain hsub : ∀ r ∈ [slotRegion rCfg s], ∃ r' ∈ [xR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [slotRegion, xR]; rw [show rCfg.base = .ebp from rfl, h.same.ebp]
    exact Region.sub_prefix (by decide)
  obtain same₁ : Same s₀ s₁ :=
    ⟨e₁, (k₁ .esp (by simp [kept])).trans h.same.esp, rd₁.trans h.same.rd, wr₁.trans h.same.wr,
      h.same.frame.trans (f₁.sub hsub)⟩
  -- The counters past the round's slots.
  obtain keep : ∀ k, 18 ≤ k → k < 21 → slotW s₁ k = slotW s k := fun k h₁' h₂' => by
    show s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32 = s.mem.readW (wordAddr (s.gpr .ebp) k) 32
    rw [e₁, ← h.same.ebp]
    exact slot_frame (n := 18) f₁ h₁' (by rw [h.same.ebp]; have := hp.fit; omega_arith)
  obtain i₁ : s₁.gpr .esi = s.gpr .esi := k₁ .esi (by simp [kept])
  -- `roundTail`.
  obtain in20 := hp.slotIn' same₁ (k := slotStep) (by decide)
  obtain in18 := hp.slotIn' same₁ (k := slotRounds) (by decide)
  obtain w18 := hp.slotIn same₁ (k := slotRounds) (by decide)
  rw [e₁] at in20 in18 w18
  refine wp_ldm e₁ in20 fun s₂' u₂' => wp_add fun s₂ u₂ _ => wp_ldm (B := s₀.gpr .ebp)
    (by rw [u₂.other _ (by decide), u₂'.other _ (by decide), e₁])
    (by rw [u₂.rd, u₂.wr, u₂'.rd, u₂'.wr]; exact in18) fun s₃ u₃ => wp_subi fun s₄ u₄ _ z₄ => ?_
  obtain e₄ : s₄.gpr .ebp = s₀.gpr .ebp := by rw [u₄.other _ (by decide), u₃.other _ (by decide),
    u₂.other _ (by decide), u₂'.other _ (by decide), e₁]
  refine wp_stm e₄ (by rw [u₄.wr, u₃.wr, u₂.wr, u₂'.wr]; exact w18) fun s₅ w₅ => WP.block_nil ?_
  obtain m₅ : s₅.mem = s₁.mem.writeW (wordAddr (s₀.gpr .ebp) slotRounds) (s₄.gpr .eax) := by
    rw [w₅.mem, u₄.mem, u₃.mem, u₂.mem, u₂'.mem]
  obtain g₅ : ∀ r, r ≠ .esi → r ≠ .eax → s₅.gpr r = s₁.gpr r := fun r h₁' h₂' => by
    rw [w₅.gpr, u₄.other _ h₂', u₃.other _ h₂', u₂.other _ h₁', u₂'.other _ h₂']
  obtain e₅ : s₅.gpr .ebp = s₀.gpr .ebp := by rw [g₅ _ (by decide) (by decide), e₁]
  obtain r18 : slotW s₁ slotRounds = BitVec.ofNat 32 (16 - j) := by rw [keep _ (by decide) (by decide), h.rcnt]
  obtain ax₄ : s₄.gpr .eax = BitVec.ofNat 32 (16 - (j + 1)) := by
    rw [u₄.gpr, u₃.gpr, u₂.mem, u₂'.mem, ← e₁, ← slotW, r18, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  obtain other : ∀ k, k ≠ slotRounds → k < 21 → slotW s₅ k = slotW s₁ k := fun k hk hk' => by
    show s₅.mem.readW (wordAddr (s₅.gpr .ebp) k) 32 = s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32
    rw [m₅, e₅, e₁, Mem.readW_writeW_sep (slot_ne hp hk hk' (by decide)) (by decide)]
  refine ⟨?_, ⟨e₅.trans same₁.ebp.symm |>.trans same₁.ebp, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w₅.zf, z₄, u₃.gpr, u₂.mem, u₂'.mem, ← e₁, ← slotW, r18, ofNat_sub_one (by omega_arith) (by omega_arith),
      Wp.ofNat_beq_zero (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · rw [g₅ _ (by decide) (by decide)]; exact same₁.esp
  · rw [w₅.rd, u₄.rd, u₃.rd, u₂.rd, u₂'.rd]; exact same₁.rd
  · rw [w₅.wr, u₄.wr, u₃.wr, u₂.wr, u₂'.wr]; exact same₁.wr
  · rw [m₅]; exact Same.write hp same₁ (by decide) _
  · rw [w₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₂'.gpr, u₂'.other _ (by decide), i₁, h.esi, ← e₁, ← slotW,
      keep _ (by decide) (by decide), h.step, kpos_succ_addr _ hp3 hj]
  · rw [other _ (by decide) (by decide), keep _ (by decide) (by decide), h.step]
  · rw [other _ (by decide) (by decide), keep _ (by decide) (by decide), h.pcnt]
  · show s₅.mem.readW (wordAddr (s₅.gpr .ebp) slotRounds) 32 = _
    rw [m₅, e₅, Mem.readW_writeW_self32, ax₄]
  · rw [other _ (by decide) (by decide), other _ (by decide) (by decide), rounds_succ, ← h.halves, eL, eR,
      key_at hp h.same (kpos_lt hp3 hj) h.esi, passKeys_at s₀ hj]

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl

/-- Reading slot `k` after writing slot `j`. -/
theorem rd_wr_ne {s₀ : State} (hp : BlockPre s₀) (m : Mem) {j k : Nat} (v : BitVec 32) (h : k ≠ j) (hk : k < 21)
    (hj : j < 21) :
    (m.writeW (wordAddr (s₀.gpr .ebp) j) v).readW (wordAddr (s₀.gpr .ebp) k) 32 =
      m.readW (wordAddr (s₀.gpr .ebp) k) 32 :=
  Mem.readW_writeW_sep (slot_ne hp h hk hj) (by decide)

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : State} (h : Same s₀ s) (hesi : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * kpos p 0))
    (hstep : slotW s slotStep = stride p) (hpc : slotW s slotPasses = BitVec.ofNat 32 (3 - p))
    (hh : (slotW s slotL, slotW s slotR) = lr) :
    WP isa pass s (PInv s₀ p lr 16) := by
  obtain w18 := hp.slotIn h (k := slotRounds) (by decide)
  rw [h.ebp] at w18
  refine WP.seq (wp_movi fun s₁ u₁ => wp_stm (B := s₀.gpr .ebp) (by rw [u₁.other _ (by decide), h.ebp])
    (by rw [u₁.wr]; exact w18) fun s₂ w₂ => WP.block_nil ?_)
  obtain g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by rw [w₂.gpr, u₁.other _ hr]
  obtain e₂ : s₂.gpr .ebp = s₀.gpr .ebp := by rw [g₂ _ (by decide), h.ebp]
  obtain m₂ : s₂.mem = s.mem.writeW (wordAddr (s₀.gpr .ebp) slotRounds) (16 : BitVec 32) := by rw [w₂.mem, u₁.mem, u₁.gpr]
  obtain other : ∀ k, k ≠ slotRounds → k < 21 → slotW s₂ k = slotW s k := fun k hk hk' => by
    show s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32 = s.mem.readW (wordAddr (s.gpr .ebp) k) 32
    rw [m₂, e₂, h.ebp, rd_wr_ne hp _ _ hk hk' (by decide)]
  obtain hI : PInv s₀ p lr 0 s₂ :=
    ⟨⟨e₂, by rw [g₂ _ (by decide)]; exact h.esp, by rw [w₂.rd, u₁.rd]; exact h.rd,
      by rw [w₂.wr, u₁.wr]; exact h.wr, by rw [m₂]; exact Same.write hp h (by decide) _⟩,
      by rw [g₂ _ (by decide), hesi], by rw [other _ (by decide) (by decide), hstep],
      by rw [other _ (by decide) (by decide), hpc],
      by show s₂.mem.readW (wordAddr (s₂.gpr .ebp) slotRounds) 32 = _; rw [m₂, e₂, Mem.readW_writeW_self32]; rfl,
      by rw [other _ (by decide) (by decide), other _ (by decide) (by decide), hh]; rfl⟩
  refine WP.loop (M := isa) (body := .block (round ++ roundTail)) (c := .ne) (Q := PInv s₀ p lr 16)
    (fun (n : Nat) (t : State) => ∃ j, n = 16 - j ∧ j < 16 ∧ PInv s₀ p lr j t) ?_ 16 _ ⟨0, rfl, by decide, hI⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (roundStep_ok hp hp3 hj ht) fun t' ⟨z', h'⟩ => ?_
  by_cases hz : j + 1 = 16
  · left
    refine ⟨by rw [eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [eval_ne, z']; simp [hz], 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, h'⟩

/-! ## The passes -/

/-- After `p` passes, from the block `x`. -/
structure OInv (s₀ : State) (x : BitVec 64) (p : Nat) (s : State) : Prop where
  same : Same s₀ s
  esi : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * kpos p 0)
  step : slotW s slotStep = stride p
  pcnt : slotW s slotPasses = BitVec.ofNat 32 (3 - p)
  halves : (slotW s slotL, slotW s slotR) = passes (sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))

theorem kpos_tail_addr (a : BitVec 32) {p : Nat} (hp : p < 3) :
    a + BitVec.ofNat 32 (8 * kpos p 16) + (128 - stride p) = a + BitVec.ofNat 32 (8 * kpos (p + 1) 0) := by
  rw [BitVec.add_assoc]
  congr 1
  rcases (by omega_arith : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem stride_succ {p : Nat} (hp : p < 3) : 0 - stride p = stride (p + 1) := by
  rcases (by omega_arith : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

/-- One pass and the exchange after it. -/
theorem passBody_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {p : Nat} (hp3 : p < 3) {s : State}
    (h : OInv s₀ x p s) :
    WP isa (.seq pass (.block passTail)) s fun s' => s'.zf = some (decide (p + 1 = 3)) ∧ OInv s₀ x (p + 1) s' := by
  refine WP.seq (WP.mono (pass_ok hp hp3 h.same h.esi h.step h.pcnt h.halves) fun s₁ h₁ => ?_)
  have e₁ := h₁.same.ebp
  obtain rin : ∀ k, k < 21 → InRegions (s₁.rd ++ s₁.wr) (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn' h₁.same hk; rwa [e₁] at this
  obtain win : ∀ k, k < 21 → InRegions s₁.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn h₁.same hk; rwa [e₁] at this
  refine wp_ldm (o := 4 * slotStep) e₁ (rin _ (by decide)) fun t₁ u₁ => wp_movi fun t₂ u₂ =>
    wp_sub fun t₃ u₃ _ => wp_add fun t₄ u₄ _ => wp_movi fun t₅ u₅ => wp_sub fun t₆ u₆ _ => ?_
  obtain g₆ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₆.gpr r = s₁.gpr r := fun r ha hc hs => by
    rw [u₆.other _ ha, u₅.other _ ha, u₄.other _ hs, u₃.other _ ha, u₂.other _ ha, u₁.other _ hc]
  obtain e₆ : t₆.gpr .ebp = s₀.gpr .ebp := by rw [g₆ _ (by decide) (by decide) (by decide), e₁]
  obtain wr₆ : t₆.wr = s₁.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain rd₆ : t₆.rd = s₁.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain m₆ : t₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain stp : t₁.gpr .ecx = stride p := by rw [u₁.gpr, ← e₁, ← slotW, h₁.step]
  refine wp_stm e₆ (by rw [wr₆]; exact win _ (by decide)) fun t₇ w₇ => ?_
  refine wp_ldm (o := 4 * slotL) (by rw [w₇.gpr, e₆]) (by rw [w₇.rd, w₇.wr, rd₆, wr₆]; exact rin _ (by decide))
    fun t₈ u₈ => ?_
  refine wp_ldm (o := 4 * slotR) (by rw [u₈.other _ (by decide), w₇.gpr, e₆])
    (by rw [u₈.rd, u₈.wr, w₇.rd, w₇.wr, rd₆, wr₆]; exact rin _ (by decide)) fun t₉ u₉ => ?_
  obtain e₉ : t₉.gpr .ebp = s₀.gpr .ebp := by rw [u₉.other _ (by decide), u₈.other _ (by decide), w₇.gpr, e₆]
  obtain wr₉ : t₉.wr = s₁.wr := by rw [u₉.wr, u₈.wr, w₇.wr, wr₆]
  refine wp_stm (o := 4 * slotL) e₉ (by rw [wr₉]; exact win _ (by decide)) fun t₁₀ w₁₀ => ?_
  refine wp_stm (o := 4 * slotR) (by rw [w₁₀.gpr, e₉]) (by rw [w₁₀.wr, wr₉]; exact win _ (by decide))
    fun t₁₁ w₁₁ => ?_
  refine wp_ldm (o := 4 * slotPasses) (by rw [w₁₁.gpr, w₁₀.gpr, e₉])
    (by rw [w₁₁.rd, w₁₁.wr, w₁₀.rd, w₁₀.wr, u₉.rd, u₈.rd, w₇.rd, rd₆, wr₉]; exact rin _ (by decide))
    fun t₁₂ u₁₂ => wp_subi fun t₁₃ u₁₃ _ z₁₃ => ?_
  obtain e₁₃ : t₁₃.gpr .ebp = s₀.gpr .ebp := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), w₁₁.gpr, w₁₀.gpr, e₉]
  refine wp_stm (o := 4 * slotPasses) e₁₃
    (by rw [u₁₃.wr, u₁₂.wr, w₁₁.wr, w₁₀.wr, wr₉]; exact win _ (by decide)) fun t₁₄ w₁₄ => WP.block_nil ?_
  -- The memory.
  obtain m₁₁ : t₁₁.mem = ((s₁.mem.writeW (wordAddr (s₀.gpr .ebp) slotStep) (t₆.gpr .eax)).writeW
      (wordAddr (s₀.gpr .ebp) slotL) (t₉.gpr .ecx)).writeW (wordAddr (s₀.gpr .ebp) slotR) (t₉.gpr .eax) := by
    rw [w₁₁.mem, w₁₀.mem, w₁₀.gpr, u₉.mem, u₈.mem, w₇.mem, m₆]
  obtain m₁₄ : t₁₄.mem = t₁₁.mem.writeW (wordAddr (s₀.gpr .ebp) slotPasses) (t₁₃.gpr .eax) := by
    rw [w₁₄.mem, u₁₃.mem, u₁₂.mem]
  obtain rd₁ : ∀ k, slotW s₁ k = s₁.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₁]
  obtain ax₉L : t₉.gpr .eax = slotW s₁ slotL := by
    rw [u₉.other _ (by decide), u₈.gpr, w₇.mem, m₆, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  obtain ax₉R : t₉.gpr .ecx = slotW s₁ slotR := by
    rw [u₉.gpr, u₈.mem, w₇.mem, m₆, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  obtain pc₁₂ : t₁₂.gpr .eax = slotW s₁ slotPasses := by
    rw [u₁₂.gpr, m₁₁, rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  obtain e₁₄ : t₁₄.gpr .ebp = s₀.gpr .ebp := by rw [w₁₄.gpr, e₁₃]
  obtain sl : ∀ k, slotW t₁₄ k = t₁₄.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₁₄]
  obtain g₁₄ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₁₄.gpr r = s₁.gpr r := fun r ha hc hs => by
    rw [w₁₄.gpr, u₁₃.other _ ha, u₁₂.other _ ha, w₁₁.gpr, w₁₀.gpr, u₉.other _ hc, u₈.other _ ha, w₇.gpr,
      g₆ _ ha hc hs]
  refine ⟨?_, ⟨⟨e₁₄, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [w₁₄.zf, z₁₃, pc₁₂, h₁.pcnt, ofNat_sub_one (by omega_arith) (by omega_arith), Wp.ofNat_beq_zero (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · rw [g₁₄ _ (by decide) (by decide) (by decide)]; exact h₁.same.esp
  · rw [w₁₄.rd, u₁₃.rd, u₁₂.rd, w₁₁.rd, w₁₀.rd, u₉.rd, u₈.rd, w₇.rd, rd₆]; exact h₁.same.rd
  · rw [w₁₄.wr, u₁₃.wr, u₁₂.wr, w₁₁.wr, w₁₀.wr, wr₉]; exact h₁.same.wr
  · have xC : ∀ k, k < 21 → (xR s₀).Contains (wordAddr (s₀.gpr .ebp) k) (32 / 8) := fun k hk =>
      contains_w (by have := hp.fit; omega_arith) (by omega_arith)
    rw [m₁₄, m₁₁]
    exact (((h₁.same.frame.writeW (List.mem_singleton_self _) _ (xC slotStep (by decide))).writeW
      (List.mem_singleton_self _) _ (xC slotL (by decide))).writeW (List.mem_singleton_self _) _
      (xC slotR (by decide))).writeW (List.mem_singleton_self _) _ (xC slotPasses (by decide))
  · rw [w₁₄.gpr, u₁₃.other .esi (by decide), u₁₂.other .esi (by decide), w₁₁.gpr, w₁₀.gpr,
      u₉.other .esi (by decide), u₈.other .esi (by decide), w₇.gpr, u₆.other .esi (by decide),
      u₅.other .esi (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₃.other .esi (by decide), u₂.other .esi (by decide),
      u₂.other .ecx (by decide), u₁.other .esi (by decide), h₁.esi, stp, kpos_tail_addr _ hp3]
  · rw [sl, m₁₄, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), m₁₁,
      rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, u₆.gpr, u₅.gpr, u₅.other .ecx (by decide), u₄.other .ecx (by decide),
      u₃.other .ecx (by decide), u₂.other .ecx (by decide), stp, stride_succ hp3]
  · rw [sl, m₁₄, Mem.readW_writeW_self32, u₁₃.gpr, pc₁₂, h₁.pcnt, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  · rw [sl, sl, m₁₄, rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      rd_wr_ne hp _ _ (by decide) (by decide) (by decide), m₁₁, rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Mem.readW_writeW_self32, ax₉L, ax₉R, passes, ← h₁.halves]
    rfl

/-- The three passes. -/
theorem passes_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {s : State} (h : OInv s₀ x 0 s) :
    WP isa (.loop (.seq pass (.block passTail)) .ne) s (OInv s₀ x 3) := by
  refine WP.loop (M := isa) (body := .seq pass (.block passTail)) (c := .ne) (Q := OInv s₀ x 3)
    (fun (n : Nat) (t : State) => ∃ p, n = 3 - p ∧ p < 3 ∧ OInv s₀ x p t) ?_ 3 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨p, rfl, hp3, ht⟩
  refine WP.mono (passBody_ok hp hp3 ht) fun t' ⟨z', h'⟩ => ?_
  by_cases hz : p + 1 = 3
  · left
    refine ⟨by rw [eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [eval_ne, z']; simp [hz], 3 - (p + 1), by omega_arith, p + 1, rfl, by omega_arith, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- Bit `b` of a block `hi ‖ lo`, as an atom: of `hi` (input word 0) or `lo`
(input word 1). -/
def xAtom (b : Nat) : Nat := if 32 ≤ b then b - 32 else 32 + b

/-- `IP`'s high half into slot `L`, its low half into slot `R`. -/
def ipGL (t : Nat) : List Nat := if t < 32 then [xAtom (ipSrc (32 + t))] else []
def ipGR (t : Nat) : List Nat := if t < 32 then [xAtom (ipSrc t)] else []

theorem ip_check :
    check (lanes 32 6) oCfg (linExt 0) ipCode (linEnv [(0, 0), (1, 1)])
      (linPost oCfg.slots 6 [(slotL, ipGL), (slotR, ipGR)]) = true := by
  lit_decide

/-- `IP⁻¹(R ‖ L)` into slots 0 (high word) and 1 (low word), from `R` in slot
`L` (input word 0) and `L` in slot `R` (input word 1). -/
def fpG0 (t : Nat) : List Nat := if t < 32 then [xAtom (fpSrc (32 + t))] else []
def fpG1 (t : Nat) : List Nat := if t < 32 then [xAtom (fpSrc t)] else []

theorem fp_check :
    check (lanes 32 6) oCfg (linExt 0) fpCode (linEnv [(slotL, 0), (slotR, 1)])
      (linPost oCfg.slots 6 [(0, fpG0), (1, fpG1)]) = true := by
  lit_decide

theorem ip_kept : kept.all (fun r => ipCode.all fun i => i.dst != some r) = true := by lit_decide

theorem fp_kept : kept.all (fun r => fpCode.all fun i => i.dst != some r) = true := by lit_decide

theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by lit_decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by lit_decide

/-- A bit of `hi ‖ lo`. -/
theorem bit_xAtom (W : Nat → BitVec 32) {b : Nat} (hb : b < 64) :
    bitOf W (xAtom b) = (W 0 ++ W 1).getLsbD b := by
  rw [BitVec.getLsbD_append, xAtom]
  by_cases h : 32 ≤ b
  · rw [ite_eq_left h, ite_eq_right (by omega_arith), bitOf, Nat.div_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  · rw [ite_eq_right h, ite_eq_left (by omega_arith), bitOf, show (32 + b) / 32 = 1 by omega_arith,
      show (32 + b) % 32 = b by omega_arith]

theorem ip_ok {s : State} (hok : Ok oCfg s) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      (slotW s' slotL, slotW s' slotR) = split (Spec.TripleDes.permute Spec.TripleDes.ip (slotW s 0 ++ slotW s 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion oCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then slotW s 0 else slotW s 1
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok ip_check hok W
    (fun j i hji _ => by
      simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hji
      rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  obtain kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => hoth _ (List.all_eq_true.mp ip_kept r hr)
  obtain e : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  obtain bit : ∀ j g, (j, g) ∈ [(slotL, ipGL), (slotR, ipGR)] → ∀ p < 32,
      (slotW s' j).getLsbD p = xorBits W (g p) := fun j g h p hp => by
    rw [slotW, e]; exact hout j g h p hp
  refine ⟨s', hs', ?_, hrd, hwr, kp, hfr⟩
  have hx : W 0 ++ W 1 = slotW s 0 ++ slotW s 1 := rfl
  simp only [split, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
  · rw [bit slotL ipGL (List.mem_cons_self ..) t ht, ipGL, ite_eq_left ht, xorBits_cons, xorBits_nil,
      Bool.xor_false, bit_xAtom W (ipSrc_lt _ (by omega_arith)), hx, BitVec.getLsbD_setWidth, decide_eq_true ht,
      Bool.true_and, BitVec.getLsbD_ushiftRight, getLsbD_permute _ _ (by decide) (show 32 + t < 64 by omega_arith)]
    rfl
  · rw [bit slotR ipGR (List.mem_cons_of_mem _ (List.mem_cons_self ..)) t ht, ipGR, ite_eq_left ht, xorBits_cons,
      xorBits_nil, Bool.xor_false, bit_xAtom W (ipSrc_lt _ (by omega_arith)), hx, BitVec.getLsbD_setWidth,
      decide_eq_true ht, Bool.true_and, getLsbD_permute _ _ (by decide) (show t < 64 by omega_arith)]
    rfl

theorem fp_ok {s : State} (hok : Ok oCfg s) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      slotW s' 0 ++ slotW s' 1 = Spec.TripleDes.permute Spec.TripleDes.fp (slotW s slotL ++ slotW s slotR) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion oCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then slotW s slotL else slotW s slotR
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok fp_check hok W
    (fun j i hji _ => by
      simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hji
      rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  obtain kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => hoth _ (List.all_eq_true.mp fp_kept r hr)
  obtain e : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  obtain bit : ∀ j g, (j, g) ∈ [(0, fpG0), (1, fpG1)] → ∀ p < 32,
      (slotW s' j).getLsbD p = xorBits W (g p) := fun j g h p hp => by
    rw [slotW, e]; exact hout j g h p hp
  refine ⟨s', hs', ?_, hrd, hwr, kp, hfr⟩
  have hx : W 0 ++ W 1 = slotW s slotL ++ slotW s slotR := rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_append, getLsbD_permute _ _ (by decide) hj,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl]
  by_cases h32 : j < 32
  · rw [ite_eq_left h32, bit 1 fpG1 (List.mem_cons_of_mem _ (List.mem_cons_self ..)) j h32, fpG1, ite_eq_left h32,
      xorBits_cons, xorBits_nil, Bool.xor_false, bit_xAtom W (fpSrc_lt _ hj), hx]
  · rw [ite_eq_right h32, bit 0 fpG0 (List.mem_cons_self ..) (j - 32) (by omega_arith), fpG0, ite_eq_left (by omega_arith),
      xorBits_cons, xorBits_nil, Bool.xor_false, show 32 + (j - 32) = j by omega_arith, bit_xAtom W (fpSrc_lt _ hj), hx]

/-! ## The block -/

theorem oCfg_ok {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) : Ok oCfg s :=
  ⟨fun k hk => hp.slotIn h (by simp only [oCfg] at hk; omega_arith), fun k hk => absurd hk (by simp [oCfg]),
    by show (s.gpr .ebp).toNat + 4 * 18 ≤ 2 ^ 32; rw [h.ebp]; have := hp.fit; omega_arith,
    fun k _ j hj => absurd hj (by simp [oCfg])⟩

theorem oCfg_sub {s₀ s : State} (h : Same s₀ s) : ∀ r ∈ [slotRegion oCfg s], ∃ r' ∈ [xR s₀], Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [slotRegion, xR]; rw [show oCfg.base = .ebp from rfl, h.ebp]
    exact Region.sub_prefix (by decide)

/-- TDEA encryption of the block in `eax:edx` (its high and low words) with
the key schedule at `esi`, into `eax:edx`. -/
theorem block_ok {s₀ : State} (hp : BlockPre s₀) :
    WP isa block s₀ fun s =>
      Same s₀ s ∧ s.gpr .esi = s₀.gpr .esi ∧
        s.gpr .eax ++ s.gpr .edx = tdes (sch s₀) (s₀.gpr .eax ++ s₀.gpr .edx) := by
  obtain xC : ∀ k, k < 21 → (xR s₀).Contains (wordAddr (s₀.gpr .ebp) k) (32 / 8) := fun k hk =>
    contains_w (by have := hp.fit; omega_arith) (by omega_arith)
  obtain same₀ : Same s₀ s₀ := ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  obtain win : ∀ k, k < 21 → InRegions s₀.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => hp.slotIn same₀ hk
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_stm (o := 4 * 0) rfl (win 0 (by decide)) fun s₁ w₁ =>
    wp_stm (o := 4 * 1) (by rw [w₁.gpr]) (by rw [w₁.wr]; exact win 1 (by decide)) fun s₂ w₂ => WP.block_nil ?_
  obtain m₂ : s₂.mem = (s₀.mem.writeW (wordAddr (s₀.gpr .ebp) 0) (s₀.gpr .eax)).writeW (wordAddr (s₀.gpr .ebp) 1)
      (s₀.gpr .edx) := by rw [w₂.mem, w₁.mem, w₁.gpr]
  obtain same₂ : Same s₀ s₂ := ⟨by rw [w₂.gpr, w₁.gpr], by rw [w₂.gpr, w₁.gpr], by rw [w₂.rd, w₁.rd],
    by rw [w₂.wr, w₁.wr], by
      rw [m₂]; exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (xC 0 (by decide))).writeW
        (List.mem_singleton_self _) _ (xC 1 (by decide))⟩
  obtain sl₂ : ∀ k, slotW s₂ k = s₂.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, same₂.ebp]
  obtain x₂ : slotW s₂ 0 ++ slotW s₂ 1 = s₀.gpr .eax ++ s₀.gpr .edx := by
    rw [sl₂, sl₂, m₂, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
      Mem.readW_writeW_self32]
  obtain ⟨s₃, h₃, ip₃, rd₃, wr₃, k₃, f₃⟩ := ip_ok (oCfg_ok hp same₂)
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  obtain e₃ : s₃.gpr .ebp = s₀.gpr .ebp := (k₃ .ebp (by simp [kept])).trans same₂.ebp
  obtain same₃ : Same s₀ s₃ := ⟨e₃, (k₃ .esp (by simp [kept])).trans same₂.esp, rd₃.trans same₂.rd,
    wr₃.trans same₂.wr, same₂.frame.trans (f₃.sub (oCfg_sub same₂))⟩
  obtain win₃ : ∀ k, k < 21 → InRegions s₃.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn same₃ hk; rwa [e₃] at this
  refine wp_movi fun s₄ u₄ => wp_stm (o := 4 * slotPasses) (B := s₀.gpr .ebp) (by rw [u₄.other _ (by decide), e₃])
    (by rw [u₄.wr]; exact win₃ _ (by decide)) fun s₅ w₅ => wp_movi fun s₆ u₆ =>
    wp_stm (o := 4 * slotStep) (B := s₀.gpr .ebp) (by rw [u₆.other _ (by decide), w₅.gpr, u₄.other _ (by decide), e₃])
    (by rw [u₆.wr, w₅.wr, u₄.wr]; exact win₃ _ (by decide)) fun s₇ w₇ => WP.block_nil ?_
  obtain m₇ : s₇.mem = (s₃.mem.writeW (wordAddr (s₀.gpr .ebp) slotPasses) (3 : BitVec 32)).writeW
      (wordAddr (s₀.gpr .ebp) slotStep) (8 : BitVec 32) := by
    rw [w₇.mem, u₆.mem, u₆.gpr, w₅.mem, u₄.mem, u₄.gpr]
  obtain g₇ : ∀ r, r ≠ .eax → s₇.gpr r = s₃.gpr r := fun r hr => by
    rw [w₇.gpr, u₆.other _ hr, w₅.gpr, u₄.other _ hr]
  obtain e₇ : s₇.gpr .ebp = s₀.gpr .ebp := by rw [g₇ _ (by decide), e₃]
  obtain sl₇ : ∀ k, slotW s₇ k = s₇.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₇]
  obtain sl₃ : ∀ k, slotW s₃ k = s₃.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₃]
  obtain esi₇ : s₇.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * kpos 0 0) := by
    rw [g₇ _ (by decide), k₃ .esi (by simp [kept]), show s₂.gpr .esi = s₀.gpr .esi by rw [w₂.gpr, w₁.gpr]]
    simp [kpos]
  obtain hO : OInv s₀ (s₀.gpr .eax ++ s₀.gpr .edx) 0 s₇ :=
    ⟨⟨e₇, by rw [g₇ _ (by decide)]; exact same₃.esp, by rw [w₇.rd, u₆.rd, w₅.rd, u₄.rd]; exact same₃.rd,
      by rw [w₇.wr, u₆.wr, w₅.wr, u₄.wr]; exact same₃.wr, by
        rw [m₇]; exact (same₃.frame.writeW (List.mem_singleton_self _) _ (xC slotPasses (by decide))).writeW
          (List.mem_singleton_self _) _ (xC slotStep (by decide))⟩,
      esi₇,
      by rw [sl₇, m₇, Mem.readW_writeW_self32]; rfl,
      by rw [sl₇, m₇, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl,
      by rw [sl₇, sl₇, m₇, rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
        rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
        rd_wr_ne hp _ _ (by decide) (by decide) (by decide), ← sl₃, ← sl₃, ip₃, x₂]; rfl⟩
  refine WP.seq (WP.mono (passes_ok hp hO) fun s₈ h₈ => ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_subi fun s₉ u₉ _ _ => WP.block_nil ?_
  obtain same₉ : Same s₀ s₉ := ⟨by rw [u₉.other _ (by decide)]; exact h₈.same.ebp,
    by rw [u₉.other _ (by decide)]; exact h₈.same.esp, by rw [u₉.rd]; exact h₈.same.rd,
    by rw [u₉.wr]; exact h₈.same.wr, by rw [u₉.mem]; exact h₈.same.frame⟩
  obtain ⟨s₁₀, h₁₀, fp₁₀, rd₁₀, wr₁₀, k₁₀, f₁₀⟩ := fp_ok (oCfg_ok hp same₉)
  refine WP.of_runBlock ⟨s₁₀, h₁₀, ?_⟩
  obtain e₁₀ : s₁₀.gpr .ebp = s₀.gpr .ebp := (k₁₀ .ebp (by simp [kept])).trans same₉.ebp
  obtain same₁₀ : Same s₀ s₁₀ := ⟨e₁₀, (k₁₀ .esp (by simp [kept])).trans same₉.esp, rd₁₀.trans same₉.rd,
    wr₁₀.trans same₉.wr, same₉.frame.trans (f₁₀.sub (oCfg_sub same₉))⟩
  obtain rin : ∀ k, k < 21 → InRegions (s₁₀.rd ++ s₁₀.wr) (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn' same₁₀ hk; rwa [e₁₀] at this
  refine wp_ldm (o := 4 * 0) e₁₀ (rin 0 (by decide)) fun s₁₁ u₁₁ =>
    wp_ldm (o := 4 * 1) (B := s₀.gpr .ebp) (by rw [u₁₁.other _ (by decide), e₁₀])
    (by rw [u₁₁.rd, u₁₁.wr]; exact rin 1 (by decide)) fun s₁₂ u₁₂ => WP.block_nil ?_
  refine ⟨⟨by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide)]; exact same₁₀.ebp,
    by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide)]; exact same₁₀.esp,
    by rw [u₁₂.rd, u₁₁.rd]; exact same₁₀.rd, by rw [u₁₂.wr, u₁₁.wr]; exact same₁₀.wr,
    by rw [u₁₂.mem, u₁₁.mem]; exact same₁₀.frame⟩, ?_, ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), k₁₀ .esi (by simp [kept]), u₉.gpr, h₈.esi,
      show 8 * kpos 3 0 = 504 from rfl, show (504 : BitVec 32) = BitVec.ofNat 32 504 from rfl, BitVec.add_sub_cancel]
  · have sl₁₀ : ∀ k, slotW s₁₀ k = s₁₀.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₁₀]
    obtain sl₉ : ∀ k, slotW s₉ k = slotW s₈ k := fun k => by rw [slotW, slotW, u₉.mem, u₉.other _ (by decide)]
    rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₂.gpr, u₁₁.mem, ← sl₁₀, ← sl₁₀, fp₁₀, sl₉, sl₉, tdes_eq, ← h₈.halves]

end VG.Proof.CmacTripleDes.X86

end

end

/-! ### `CmacTripleDes.X86.Save`, which only this module used -/

section

/-!
# TDEA-CMAC on x86: saving and restoring the registers, and the arguments

Untrusted: everything here is checked by Lean. Each function saves our
caller's `ebx`, `esi`, `edi` and `ebp` to bytes `[84, 100)` of the scratch
buffer through `eax` (`save`, a `Spill.saveCode`), and restores them from
there through `ebp`, `ebp` last (`restore`). It loads its arguments from the stack (`wp_arg`).
-/

@[expose] public section

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
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (at_ .esp o)) :: is)) s Q :=
  wp_movm (by rw [ea_at', hesp, ho]; rfl) hin fun s' u => k s' (hv ▸ u)

end

/-! ## Saving -/

theorem saved_fits : Spill.Fits 100 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 84 ≤ p.2 ∧ p.2 + 4 ≤ 100 := by decide

theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide

/-- A scratch buffer of at least 100 bytes holds the slots. -/
theorem fits_of {S : BitVec 32} {n : Nat} (h : S.toNat + n ≤ 2 ^ 32) (hn : 100 ≤ n) : S.toNat + 100 ≤ 2 ^ 32 := by
  omega_using [h, hn]

/-- The memory after saving the registers to the scratch buffer at `S`. -/
def savedMem (s₀ : State) (S : BitVec 32) : Mem :=
  Spill.saveMem s₀.mem (S.setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

theorem savedMem_frame (s₀ : State) (S : BitVec 32) :
    Frame [⟨S.setWidth 64 + BitVec.ofNat 64 84, 16⟩] s₀.mem (savedMem s₀ S) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp => by
    obtain h := saved_bound p hp
    rw [show S.setWidth 64 + BitVec.ofNat 64 p.2 = S.setWidth 64 + BitVec.ofNat 64 84 + BitVec.ofNat 64 (p.2 - 84)
      from (Offset.add_add_eq _ (by omega_using [h])).symm]
    exact Offset.contains_base _ (by omega_using [h]) (by omega_using [h])

/-- Slots unchanged since the registers were saved hold the registers of `s₀`. -/
theorem saved_of {s₀ : State} {S : BitVec 32} {m : Mem}
    (hm : ∀ d, 84 ≤ d → d + 4 ≤ 100 →
      m.readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 = (savedMem s₀ S).readW (S.setWidth 64 + BitVec.ofNat 64 d) 32) :
    Spill.Saved m (S.setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved := fun p hp =>
  have h := saved_bound p hp
  (hm _ h.1 h.2).trans (Spill.saveMem_saved_ofNat _ _ _ saved_fits (by decide) p hp)

/-! ## Restoring -/

/-- The registers but `ebp`, and where they are saved. -/
def saved3 : List (Reg × Nat) := [(.ebx, 84), (.esi, 88), (.edi, 92)]

theorem restore_eq : restore = Spill.restoreCode .ebp (saved3 ++ [(.ebp, 96)]) ++ [] := rfl

/-- `restore` from the scratch buffer at `S`, whose slots hold `g`. -/
theorem restore_ok {s : State} {S : BitVec 32} {g : Reg → BitVec 32} (hb : s.gpr .ebp = S)
    (hS : S.toNat + 100 ≤ 2 ^ 32)
    (hr : ∀ d, 84 ≤ d → d + 4 ≤ 100 → InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 d) 4)
    (hs : Spill.Saved s.mem (S.setWidth 64 + BitVec.ofNat 64 ·) g saved) :
    WP isa (.block restore) s (Spill.Restored s · g saved) := by
  obtain ha := Spill.addr_eq_of_fits hS saved_fits
  rw [restore_eq]
  refine Spill.restoreBase_ok saved3 (by decide) (fun p hp => ?_)
    (by rw [hb]; exact hs.congr (fun p hp => (ha p hp).symm) fun _ _ => rfl) fun s' u => WP.block_nil u
  obtain h := saved_bound p hp
  rw [hb, ha p hp]; exact hr _ h.1 h.2

/-- The registers restored from slots holding those of `s₀`, with the stack
pointer and the return address kept. -/
theorem restored {s₀ s s' : State} (h : Spill.Restored s s' s₀.gpr saved) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hret : s'.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32) :
    abiPreserved s₀ s' :=
  ⟨h.abi (by decide) (by decide) hsp, hret⟩

end VG.Proof.CmacTripleDes.X86

end

end


/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_update`

Untrusted: everything here is checked by Lean. The invariant after `k`
blocks (`LInv`): words 32 and 33 of the scratch buffer hold the next block
and the blocks left, only the state, the block's words and those two have
changed since the registers were saved, and the state is the chaining value
after the first `k` blocks.
-/

@[expose] public section

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
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega_arith))) (by decide)

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

theorem addr_zero (x : BitVec 32) : addr x 0 = x.setWidth 64 := by
  simp only [addr]; rw [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]

theorem addr_off2 {x : BitVec 32} {a b : Nat} (h : x.toNat + a + b < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 a) b = x.setWidth 64 + BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
  rw [Straight.addr_add_ofNat, addr_eq (by omega_arith), Offset.add_add]

theorem add0 (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

section
variable (s₀ : State)

abbrev W : BitVec 32 := arg s₀ 0
abbrev St : BitVec 32 := arg s₀ 1
abbrev Dp : BitVec 32 := arg s₀ 2
abbrev N : Nat := (arg s₀ 3).toNat
abbrev S : BitVec 32 := arg s₀ 4

abbrev schR : Region := ⟨(W s₀).setWidth 64, 384⟩
abbrev stR : Region := ⟨(St s₀).setWidth 64, 8⟩
abbrev dataR : Region := ⟨(Dp s₀).setWidth 64, 8 * N s₀⟩
abbrev scrR : Region := ⟨(S s₀).setWidth 64, 640⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem ((W s₀).setWidth 64)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem ((Dp s₀).setWidth 64) 8 (N s₀)

/-- What changes after the registers are saved. -/
abbrev chg : List Region :=
  [stR s₀, ⟨(S s₀).setWidth 64, 84⟩, ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩]

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀, argsR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  sch_st : (schR s₀).Disjoint (stR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_st : (dataR s₀).Disjoint (stR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  st_scr : (stR s₀).Disjoint (scrR s₀)
  args_st : (argsR s₀).Disjoint (stR s₀)
  args_scr : (argsR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 384 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 8 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + 8 * N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 640 ≤ 2 ^ 32
  esp_fit : (s₀.gpr .esp).toNat + 24 ≤ 2 ^ 32

theorem UPre.of {s₀ : State} (h : updateX86.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = W s₀
  ebp : s.gpr .ebp = S s₀
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 128) 32 = Dp s₀ + BitVec.ofNat 32 (8 * k)
  left : s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 132) 32 = BitVec.ofNat 32 (N s₀ - k)
  frame : Frame (chg s₀) (savedMem s₀ (S s₀)) s.mem
  state : Spec.Aes.bytesAt s.mem ((St s₀).setWidth 64) 8 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 8) ((blks s₀).take k)

/-! ## Regions -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.inScr {d n : Nat} (h : d + n ≤ 640) (_hn : 0 < n) :
    InRegions s₀.wr ((S s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ h (by omega_arith))

theorem UPre.scrEa {s : State} (h : s.gpr .ebp = S s₀) {d : Nat} (hd : d < 640) :
    s.ea (at_ .ebp d) = (S s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [ea_at', h]; exact addr_eq (by have := hp.scr_fit; omega_arith)

/-- Argument `i`'s address, in the arguments' region. -/
theorem UPre.argAddr_eq {i : Nat} (hi : i < 5) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.esp_fit
  show addr (s₀.gpr .esp) (4 + 4 * i) = addr (s₀.gpr .esp) (4 + 4 * 0) + _
  rw [addr_eq (by omega_arith), addr_eq (by omega_arith), Offset.add_add, show 4 + 4 * 0 + 4 * i = 4 + 4 * i by omega_arith]

/-- The arguments are unchanged while only `chg` changes after the registers are saved. -/
theorem UPre.arg_eq {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) {i : Nat} (hi : i < 5) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i := by
  obtain hsub : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
    rw [hp.argAddr_eq hi]; exact Offset.sub_base _ (by omega_arith)
  rw [hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
  · exact (savedMem_frame s₀ (S s₀)).readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => by
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
  exact in_rw (r := argsR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by omega_arith))

theorem UPre.sched {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) :
    Spec.TripleDes.scheduleAt m ((W s₀).setWidth 64) = Spec.TripleDes.scheduleAt s₀.mem ((W s₀).setWidth 64) := by
  rw [scheduleAt_frame hf fun r hr => ?_]
  · exact scheduleAt_frame (savedMem_frame s₀ (S s₀)) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sch_st
    · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))

theorem UPre.data {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) {k : Nat} (hk : k < N s₀) :
    Spec.Aes.bytesAt m ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 8 =
      Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 8 := by
  obtain hsub : Region.Sub ⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k), 8⟩ (dataR s₀) :=
    Offset.sub_base _ (by omega_arith)
  rw [bytesAt_frame hf (fun r hr => ?_) (by decide)]
  · exact bytesAt_frame (savedMem_frame s₀ (S s₀)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.data_st.sub_left hsub
    · exact (hp.data_scr.sub_left hsub).sub_right (Region.sub_prefix (by decide))
    · exact (hp.data_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))

/-- The block's precondition, with the registers and regions of the function. -/
theorem UPre.block {s : State} (h9 : s.gpr .esi = W s₀) (h10 : s.gpr .ebp = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : BlockPre s where
  sched := ⟨384, by rw [hrd, hwr, hp.rd, h9]; simp, Nat.le_refl _, by rw [h9]; exact hp.sch_fit⟩
  scr := ⟨640, by rw [hwr, hp.wr, h10]; simp, by decide, by rw [h10]; exact hp.scr_fit⟩
  disj := by
    rw [h9, h10]
    exact hp.sch_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-! ## One block -/

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega_arith)]
  simp [Spec.Cmac.blocksAt]

/-- The two words at `a` XORed, as a big-endian integer. -/
theorem bswap_xor_append (a₀ a₁ b₀ b₁ : BitVec 32) :
    bswap (a₀ ^^^ b₀) ++ bswap (a₁ ^^^ b₁) = byteRev64 ((a₁ ++ a₀) ^^^ (b₁ ++ b₀)) := by
  rw [bswap_eq, bswap_eq, byteRev32_append, BitVec.xor_append]

theorem readW_writeW_far (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega_arith) (by omega_arith)) (by decide)

theorem readW_lo_of_hi (m : Mem) (a : Addr) (v w : BitVec 32) :
    ((m.writeW a v).writeW (a + BitVec.ofNat 64 4) w).readW a 32 = v := by
  have := readW_writeW_far (m.writeW a v) a w (d := 0) (e := 4) (by decide) (by decide) (by decide)
  rw [add0] at this
  rw [this, Mem.readW_writeW_self32]

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa updBody s fun s' => LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) := by
  obtain hN : N s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have hsf := hp.scr_fit
  have hdf := hp.data_fit
  have htf := hp.st_fit
  obtain rdwr : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain scrIn : ∀ d, d + 4 ≤ 640 → InRegions (s.rd ++ s.wr) ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ hd (by omega_arith))
  obtain stIn : ∀ d, d + 4 ≤ 8 → InRegions (s.rd ++ s.wr) ((St s₀).setWidth 64 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact in_rw (r := stR s₀) (by simp) (Offset.contains_base _ hd (by omega_arith))
  obtain dIn : ∀ d, d + 4 ≤ 8 →
      InRegions (s.rd ++ s.wr) ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr, Offset.add_add]
      exact in_rw (r := dataR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by omega_arith))
  -- `chainIn`.
  refine WP.seq (?_ : WP isa (.block chainIn) s _)
  simp only [chainIn, stk]
  refine wp_arg (s₀ := s₀) 1 rfl h.esp (hp.argIn h.rd h.wr (by decide)) (hp.arg_eq h.frame (by decide))
    fun s₁ u₁ => ?_
  refine wp_movm (hp.scrEa (by rw [u₁.other _ (by decide), h.ebp]) (by decide))
    (by rw [u₁.rd, u₁.wr]; exact scrIn 128 (by decide)) fun s₂ u₂ => ?_
  obtain r1₂ : s₂.gpr .ecx = St s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  obtain r7₂ : s₂.gpr .edi = Dp s₀ + BitVec.ofNat 32 (8 * k) := by rw [u₂.gpr, u₁.mem, h.dp]
  refine wp_movm (a := (St s₀).setWidth 64) (by rw [ea_at', r1₂, addr_zero])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; simpa [add0] using stIn 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_movm (a := (St s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [ea_at', u₃.other _ (by decide), r1₂]; exact addr_eq (by omega_arith))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_xorma (a := (Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k))
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), r7₂, addr_off2 (by omega_arith), add0])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; simpa [add0] using dIn 0 (by decide))
    fun s₅ u₅ => ?_
  refine wp_xorma (a := (Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 4)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r7₂, addr_off2 (by omega_arith)])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact dIn 4 (by decide))
    fun s₆ u₆ => wp_bswap fun s₇ u₇ => wp_bswap fun s₈ u₈ => WP.block_nil ?_
  -- What `chainIn` leaves.
  obtain g₈ : ∀ r, r ∉ [Reg.eax, .ecx, .edx, .edi] → s₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₈.other _ hr.2.2.1, u₇.other _ hr.1, u₆.other _ hr.2.2.1, u₅.other _ hr.1, u₄.other _ hr.2.2.1,
      u₃.other _ hr.1, u₂.other _ hr.2.2.2, u₁.other _ hr.2.1]
  obtain m₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain ax₈ : s₈.gpr .eax ++ s₈.gpr .edx = byteRev64 (s.mem.readW ((St s₀).setWidth 64) 64 ^^^
      s.mem.readW ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 64) := by
    rw [u₈.gpr, u₈.other .eax (by decide), u₇.gpr, u₇.other .edx (by decide), u₆.gpr, u₆.other .eax (by decide),
      u₅.gpr, u₅.other .edx (by decide), u₄.gpr, u₄.other .eax (by decide), u₃.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem, readW64_split, readW64_split s.mem ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)), bswap_xor_append]
  refine WP.seq (WP.mono (block_ok (UPre.block hp (by rw [g₈ _ (by decide), h.esi])
    (by rw [g₈ _ (by decide), h.ebp]) (by rw [rd₈, h.rd]) (by rw [wr₈, h.wr]))) fun s₉ ⟨same, esi₉, ax₉⟩ => ?_)
  obtain ebp₉ : s₉.gpr .ebp = S s₀ := by rw [same.ebp, g₈ _ (by decide), h.ebp]
  obtain esp₉ : s₉.gpr .esp = s₀.gpr .esp := by rw [same.esp, g₈ _ (by decide), h.esp]
  obtain xR₈ : xR s₈ = ⟨(S s₀).setWidth 64, 84⟩ := by rw [xR, g₈ _ (by decide), h.ebp]
  obtain f₉ : Frame [⟨(S s₀).setWidth 64, 84⟩] s.mem s₉.mem := by rw [← m₈, ← xR₈]; exact same.frame
  obtain slot : ∀ d, 84 ≤ d → d + 4 ≤ 640 →
      s₉.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => f₉.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)
  obtain frame₉ : Frame (chg s₀) (savedMem s₀ (S s₀)) s₉.mem := h.frame.trans (f₉.mono (by simp))
  obtain rd₉ : s₉.rd = s₀.rd := by rw [same.rd, rd₈, h.rd]
  obtain wr₉ : s₉.wr = s₀.wr := by rw [same.wr, wr₈, h.wr]
  obtain rdwr₉ : s₉.rd ++ s₉.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [rd₉, wr₉, hp.rd, hp.wr]; rfl
  simp only [chainOut, stk]
  refine wp_arg (s₀ := s₀) 1 rfl esp₉ (hp.argIn rd₉ wr₉ (by decide)) (hp.arg_eq frame₉ (by decide)) fun t₁ v₁ => ?_
  refine wp_movm (hp.scrEa (by rw [v₁.other _ (by decide), ebp₉]) (by decide))
    (by rw [v₁.rd, v₁.wr, rdwr₉]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega_arith)))
    fun t₂ v₂ => ?_
  refine wp_movm (hp.scrEa (by rw [v₂.other _ (by decide), v₁.other _ (by decide), ebp₉]) (by decide))
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, rdwr₉]
        exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega_arith)))
    fun t₃ v₃ => ?_
  obtain r1₃ : t₃.gpr .ecx = St s₀ := by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr]
  obtain r7₃ : t₃.gpr .edi = Dp s₀ + BitVec.ofNat 32 (8 * k) := by
    rw [v₃.other _ (by decide), v₂.gpr, v₁.mem, slot 128 (by decide) (by decide), h.dp]
  obtain r3₃ : t₃.gpr .ebx = BitVec.ofNat 32 (N s₀ - k) := by
    rw [v₃.gpr, v₂.mem, v₁.mem, slot 132 (by decide) (by decide), h.left]
  refine wp_bswap fun t₄ v₄ => wp_bswap fun t₅ v₅ => ?_
  obtain stW : ∀ d, d + 4 ≤ 8 → InRegions t₅.wr ((St s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₉, hp.wr]
    exact in_rw (r := stR s₀) (by simp) (Offset.contains_base _ hd (by omega_arith))
  refine wp_store (a := (St s₀).setWidth 64) (by rw [ea_at', v₅.other _ (by decide), v₄.other _ (by decide), r1₃,
    addr_zero]) (by simpa [add0] using stW 0 (by decide)) fun t₆ w₆ => ?_
  refine wp_store (a := (St s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [ea_at', w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r1₃]; exact addr_eq (by omega_arith))
    (by rw [w₆.wr]; exact stW 4 (by decide)) fun t₇ w₇ => ?_
  refine wp_addi fun t₈ v₈ => wp_subi fun t₉ v₉ _ => ?_
  obtain g₉ : ∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx, .edi] → t₉.gpr r = s₉.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₉.other _ hr.2.1, v₈.other _ hr.2.2.2.2, w₇.gpr, w₆.gpr, v₅.other _ hr.2.2.2.1, v₄.other _ hr.1,
      v₃.other _ hr.2.1, v₂.other _ hr.2.2.2.2, v₁.other _ hr.2.2.1]
  obtain ebp₉' : t₉.gpr .ebp = S s₀ := by rw [g₉ _ (by decide), ebp₉]
  obtain wr₉' : t₉.wr = [stR s₀, scrR s₀] := by
    rw [v₉.wr, v₈.wr, w₇.wr, w₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₉, hp.wr]
  obtain scrW : ∀ d, d + 4 ≤ 640 → InRegions t₉.wr ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [wr₉']; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ hd (by omega_arith))
  refine wp_store (hp.scrEa ebp₉' (by decide)) (scrW 128 (by decide)) fun t₁₀ w₁₀ => ?_
  refine wp_store (hp.scrEa (by rw [w₁₀.gpr, ebp₉']) (by decide)) (by rw [w₁₀.wr]; exact scrW 132 (by decide))
    fun t₁₁ w₁₁ => wp_cmpi fun t₁₂ f₁₂ _ z₁₂ => WP.block_nil ?_
  -- The registers stored.
  obtain r7₉ : t₉.gpr .edi = Dp s₀ + BitVec.ofNat 32 (8 * (k + 1)) := by
    rw [v₉.other _ (by decide), v₈.gpr, w₇.gpr, w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r7₃,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_add, show 8 * k + 8 = 8 * (k + 1) by omega_arith]
  obtain r3₉ : t₉.gpr .ebx = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [v₉.gpr, v₈.other _ (by decide), w₇.gpr, w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r3₃,
      ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  -- The memory.
  obtain m₉ : t₉.mem = (s₉.mem.writeW ((St s₀).setWidth 64) (bswap (s₉.gpr .eax))).writeW
      ((St s₀).setWidth 64 + BitVec.ofNat 64 4) (bswap (s₉.gpr .edx)) := by
    rw [v₉.mem, v₈.mem, w₇.mem, w₆.mem, w₆.gpr, v₅.gpr, v₅.other .eax (by decide), v₄.gpr, v₅.mem, v₄.mem,
      v₄.other .edx (by decide), v₃.other .eax (by decide), v₃.other .edx (by decide), v₂.other .eax (by decide),
      v₂.other .edx (by decide), v₁.other .eax (by decide), v₁.other .edx (by decide), v₃.mem, v₂.mem, v₁.mem]
  obtain m₁₁ : t₁₁.mem = (t₉.mem.writeW ((S s₀).setWidth 64 + BitVec.ofNat 64 128)
      (Dp s₀ + BitVec.ofNat 32 (8 * (k + 1)))).writeW ((S s₀).setWidth 64 + BitVec.ofNat 64 132)
      (BitVec.ofNat 32 (N s₀ - (k + 1))) := by
    rw [w₁₁.mem, w₁₀.mem, w₁₀.gpr, r7₉, r3₉]
  obtain g₁₂ : t₁₂.gpr = t₉.gpr := by rw [f₁₂.gpr, w₁₁.gpr, w₁₀.gpr]
  -- The state.
  obtain hS : sch s₈ = Spec.TripleDes.scheduleAt s₀.mem ((W s₀).setWidth 64) := by
    show Spec.TripleDes.scheduleAt s₈.mem ((s₈.gpr .esi).setWidth 64) = _
    rw [g₈ _ (by decide), h.esi, m₈]; exact UPre.sched hp h.frame
  obtain hD := UPre.data hp h.frame hk
  obtain stFrame : Spec.Aes.bytesAt t₁₁.mem ((St s₀).setWidth 64) 8 =
      Spec.Aes.bytesAt t₉.mem ((St s₀).setWidth 64) 8 := by
    rw [m₁₁]
    refine bytesAt_frame (rs := [⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩]) ?_ (fun r hr => ?_) (by decide)
    · have c : ∀ d, 128 ≤ d → d + 4 ≤ 136 →
          (⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩ : Region).Contains
            ((S s₀).setWidth 64 + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => by
        rw [show (S s₀).setWidth 64 + BitVec.ofNat 64 d =
          (S s₀).setWidth 64 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (d - 128) from (Offset.add_add_eq _ (by omega_arith)).symm]
        exact Offset.contains_base _ (by omega_arith) (by omega_arith)
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
  · rw [f₁₂.mem, m₁₁, readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [f₁₂.mem, m₁₁, Mem.readW_writeW_self32]
  · rw [f₁₂.mem, m₁₁, m₉]
    obtain c4 : (stR s₀).Contains ((St s₀).setWidth 64 + BitVec.ofNat 64 4) (32 / 8) :=
      Offset.contains_base _ (by decide) (by omega_arith)
    obtain c0 : (stR s₀).Contains ((St s₀).setWidth 64) (32 / 8) := by
      simpa [add0] using Offset.contains_base ((St s₀).setWidth 64) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    obtain cs : ∀ d, 128 ≤ d → d + 4 ≤ 136 →
        (⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩ : Region).Contains ((S s₀).setWidth 64 + BitVec.ofNat 64 d)
          (32 / 8) := fun d h₁ h₂ => by
      rw [show (S s₀).setWidth 64 + BitVec.ofNat 64 d = (S s₀).setWidth 64 + BitVec.ofNat 64 128 +
        BitVec.ofNat 64 (d - 128) from (Offset.add_add_eq _ (by omega_arith)).symm]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    exact (((frame₉.writeW (r := stR s₀) (by simp) _ c0).writeW (r := stR s₀) (by simp) _ c4).writeW (by simp) _
      (cs 128 (by decide) (by decide))).writeW (by simp) _ (cs 132 (by decide) (by decide))
  · rw [f₁₂.mem, stFrame, m₉, ← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi, bswap_eq, bswap_eq,
      byteRev32_append, ax₉, ax₈, hS, ← tdesWith_le8, le8_xor, le8_readW, le8_readW, h.state, hD,
      take_succ_blks s₀ hk, chain_append, chain_single]
  · rw [z₁₂, show t₁₁.gpr .ebx = t₉.gpr .ebx by rw [w₁₁.gpr, w₁₀.gpr], r3₉,
      show ∀ x : BitVec 32, x - 0 = x from fun x => by simp, Wp.ofNat_beq_zero (by omega_arith)]

theorem eval_ne' (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl
theorem eval_e' (s : State) : isa.eval .e s = s.zf := rfl

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ k s) : WP isa (.loop updBody .ne) s (LInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := updBody) (c := .ne) (Q := LInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' ⟨h', z'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [eval_ne', z']; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_arith]
  · right
    refine ⟨by rw [eval_ne', z']; simp [hz], N s₀ - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, h'⟩

/-! ## The whole function -/

/-- The arguments of the entry state, unchanged by saving the registers. -/
theorem UPre.arg_saved {s₀ : State} (hp : UPre s₀) {i : Nat} (hi : i < 5) :
    (savedMem s₀ (S s₀)).readW (argAddr s₀ i) 32 = arg s₀ i :=
  hp.arg_eq (Frame.refl _ _) hi

theorem prologue_wp {s₀ : State} (hp : UPre s₀) :
    WP isa (.block updPre) s₀ fun s => LInv s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)) := by
  have hsc := hp.scr_fit
  obtain hN : N s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  rw [show updPre = .mov .eax (stk 20) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 12), .store (at_ .ebp 128) .eax,
      .mov .eax (stk 16), .store (at_ .ebp 132) .eax, .alu .cmp .eax (.imm 0)] : List Instr)) from rfl]
  simp only [stk]
  refine wp_arg (s₀ := s₀) 4 rfl rfl (hp.argIn rfl rfl (by decide)) rfl fun s₁ u₁ => ?_
  refine Spill.save_ofNat_ok saved saved_fits (by rw [u₁.gpr]; exact fits_of hp.scr_fit (by decide))
    (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    have hsc' : (arg s₀ 4).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
    rw [u₁.gpr, u₁.wr]
    exact hp.inScr (by omega_arith) (by decide)
  obtain hm₂ : s₂.mem = savedMem s₀ (S s₀) := by
    rw [u₂.mem, u₁.mem, u₁.gpr, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  obtain fr : ∀ m, m = savedMem s₀ (S s₀) → Frame (chg s₀) (savedMem s₀ (S s₀)) m := fun m h => h ▸ Frame.refl _ _
  refine wp_mov fun s₃ u₃ => ?_
  obtain rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  refine wp_arg (s₀ := s₀) 0 rfl esp₃ (hp.argIn rd₃ wr₃ (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_saved (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) 2 rfl (by rw [u₄.other _ (by decide), esp₃])
    (hp.argIn (by rw [u₄.rd, rd₃]) (by rw [u₄.wr, wr₃]) (by decide))
    (by rw [u₄.mem, u₃.mem, hm₂]; exact hp.arg_saved (by decide)) fun s₅ u₅ => ?_
  obtain ebp₅ : s₅.gpr .ebp = S s₀ := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]
  refine wp_store (hp.scrEa ebp₅ (by decide)) (by rw [u₅.wr, u₄.wr, wr₃]; exact hp.inScr (by decide) (by decide))
    fun s₆ w₆ => ?_
  obtain m₆ : s₆.mem = (savedMem s₀ (S s₀)).writeW ((S s₀).setWidth 64 + BitVec.ofNat 64 128) (Dp s₀) := by
    rw [w₆.mem, u₅.gpr, u₅.mem, u₄.mem, u₃.mem, hm₂]
  obtain c : ∀ d, 128 ≤ d → d + 4 ≤ 136 →
      (⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩ : Region).Contains ((S s₀).setWidth 64 + BitVec.ofNat 64 d)
        (32 / 8) := fun d h₁ h₂ => by
    rw [show (S s₀).setWidth 64 + BitVec.ofNat 64 d = (S s₀).setWidth 64 + BitVec.ofNat 64 128 +
      BitVec.ofNat 64 (d - 128) from (Offset.add_add_eq _ (by omega_arith)).symm]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain f₆ : Frame (chg s₀) (savedMem s₀ (S s₀)) s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (by simp) _ (c 128 (by decide) (by decide))
  refine wp_arg (s₀ := s₀) 3 rfl (by rw [w₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (hp.argIn (by rw [w₆.rd, u₅.rd, u₄.rd, rd₃]) (by rw [w₆.wr, u₅.wr, u₄.wr, wr₃]) (by decide))
    (hp.arg_eq f₆ (by decide)) fun s₇ u₇ => ?_
  refine wp_store (hp.scrEa (by rw [u₇.other _ (by decide), w₆.gpr, ebp₅]) (by decide))
    (by rw [u₇.wr, w₆.wr, u₅.wr, u₄.wr, wr₃]; exact hp.inScr (by decide) (by decide)) fun s₈ w₈ =>
    wp_cmpi fun s₉ f₉ _ z₉ => WP.block_nil ?_
  obtain m₉ : s₉.mem = s₆.mem.writeW ((S s₀).setWidth 64 + BitVec.ofNat 64 132) (arg s₀ 3) := by
    rw [f₉.mem, w₈.mem, u₇.gpr, u₇.mem]
  obtain g₉ : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s₉.gpr r = s₀.gpr r := fun r ha hs hb => by
    rw [f₉.gpr, w₈.gpr, u₇.other _ ha, w₆.gpr, u₅.other _ ha, u₄.other _ hs, u₃.other _ hb, u₂.gpr, u₁.other _ ha]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₉.gpr, w₈.gpr, u₇.other _ (by decide), w₆.gpr, u₅.other _ (by decide), u₄.gpr]
  · rw [f₉.gpr, w₈.gpr, u₇.other _ (by decide), w₆.gpr, ebp₅]
  · rw [g₉ _ (by decide) (by decide) (by decide)]
  · rw [f₉.rd, w₈.rd, u₇.rd, w₆.rd, u₅.rd, u₄.rd, rd₃]
  · rw [f₉.wr, w₈.wr, u₇.wr, w₆.wr, u₅.wr, u₄.wr, wr₃]
  · rw [m₉, readW_writeW_far _ _ _ (by decide) (by decide) (by decide), m₆, Mem.readW_writeW_self32]
    show Dp s₀ = Dp s₀ + BitVec.ofNat 32 0; rw [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]
  · rw [m₉, Mem.readW_writeW_self32, Nat.sub_zero]; simp [N]
  · rw [m₉]; exact f₆.writeW (by simp) _ (c 132 (by decide) (by decide))
  · rw [List.take_zero, show Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 8) [] =
      Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 8 from rfl]
    rw [m₉, m₆, bytesAt_frame (rs := [⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩])
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c 132 (by decide) (by decide)))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)]
    exact bytesAt_frame (savedMem_frame s₀ (S s₀)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · rw [z₉, show s₈.gpr .eax = arg s₀ 3 by rw [w₈.gpr, u₇.gpr],
      show ∀ x : BitVec 32, x - 0 = x from fun x => by simp,
      show arg s₀ 3 = BitVec.ofNat 32 (N s₀) by simp [N], Wp.ofNat_beq_zero hN]

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁) (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop updBody .ne)) s₁ (LInv s₀ (N s₀)) := by
  obtain ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by rw [eval_e', hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega_arith) h

/-- What changes is apart from the return address and the saved registers. -/
theorem UPre.ret_kept {s₀ : State} (hp : UPre s₀) {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) :
    m.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
  rw [hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
  · exact (savedMem_frame s₀ (S s₀)).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hsc := hp.scr_fit
  refine WP.mono (restore_ok h₂.ebp (by omega_arith) (fun d h₁ h₂' => ?_) (saved_of fun d h₁ h₂' => ?_))
    fun s' r' => ⟨restored r' h₂.esp (by rw [r'.mem]; exact hp.ret_kept h₂.frame), ?_⟩
  · rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · refine h₂.frame.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.st_scr.sub_right (Offset.sub_base _ (by omega_arith))).symm
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (d := d) (e := 128) (by omega_arith) (by omega_arith) (by omega_arith)
  · show Spec.Aes.bytesAt s'.mem ((St s₀).setWidth 64) 8 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [r'.mem, h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp {s₀ : State} (h0 : updateX86.pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  obtain hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp hp h₁ z₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacTripleDes.X86
