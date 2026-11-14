module

public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.CmacTripleDes.Des
public import VerifiedGarbage.Proof.CmacTripleDes.Rows
public import VerifiedGarbage.Proof.Framework.X86.Linear
public import VerifiedGarbage.Proof.Framework.Bitslice.Rows
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
public import VerifiedGarbage.Impl.CmacTripleDes.X86.Round
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.AddrArith

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
  have kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => keep _ (List.all_eq_true.mp inputs_kept r hr)
  have e10 : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  have bit : ∀ j g, (j, g) ∈ inOuts → ∀ p < 32, (slotW s' j).getLsbD p = xorBits (inW s) (g p) := fun j g h p hp => by
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
  have hchk : check (rows 32 6) (sCfg h) (fun _ => none) (tree h) (sbEnv h) (sbPost h) = true := by
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
  have key : ∀ p < 32, ∃ s', runBlock isa (tree h) s = some s' ∧
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
      have hc := (boxIn h s p).isLt
      obtain ⟨u, rfl, hu⟩ : ∃ u, t = 7 * h + u ∧ u < 6 := ⟨t - 7 * h, by omega_arith, by omega_arith⟩
      rw [rowIn, testBit_rowsOf, decide_eq_true (by omega_arith : 32 * (boxIn h s p).toNat + p < 32 * 64),
        Bool.true_and, show (32 * (boxIn h s p).toNat + p) / 32 = (boxIn h s p).toNat by omega_arith,
        BitVec.testBit_toNat, boxIn, getLsbD_ofBits, show (7 * h + u) % 7 = u by omega_arith,
        decide_eq_true hu, Bool.true_and]
    · cases h'
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_arith)
  refine ⟨s', hs', fun j hj b hb => ?_, p₀.rd, p₀.wr,
    fun r hr => p₀.other r (by simp [List.all_eq_true.mp (tree_kept h hh) r hr]), p₀.frame⟩
  have hp : 6 * j + off (boxOf h j) b < 32 := by have := off_lt4 h hh j hj b hb; omega_arith
  obtain ⟨s'', hs'', p₁⟩ := key _ hp
  obtain rfl := run_unique hs'' hs'
  have h' := p₁.rel.reg .ebx F hF
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
  have kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => keep _ (List.all_eq_true.mp output_kept r hr)
  have e10 : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  have bit : ∀ j g, (j, g) ∈ oOuts → ∀ p < 32, (slotW s' j).getLsbD p = xorBits (oW s) (g p) := fun j g h p hp => by
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
  have hb : 6 * (7 - boxOf h j) = 24 * h + 6 * j := by simp only [boxOf]; omega_arith
  have hE := expSrc_lt (24 * h + 6 * j + t) (by omega_arith)
  have hs : 7 * h + t = inSlot (6 * h + t) := by simp only [inSlot]; omega_arith
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
  have hb : ∀ k ≤ 17, (s.gpr .ebp).toNat + 4 * k + 4 ≤ 2 ^ 32 := fun k hk => by omega_arith
  obtain ⟨s₁, h₁, hx, L₁, R₁, rd₁, wr₁, k₁, f₁⟩ := inputs_ok hok
  have e₁ : s₁.gpr .ebp = s.gpr .ebp := k₁ _ (by simp [kept])
  have i₁ : s₁.gpr .esi = s.gpr .esi := k₁ .esi (by simp [kept])
  have hok₁ : Ok rCfg s₁ := hok.congr e₁ i₁ rd₁ wr₁
  obtain ⟨s₂, h₂, y₂, rd₂, wr₂, k₂, f₂⟩ := sbox_ok (h := 0) (by decide) (ok_fewer hok₁ rfl (by decide) rfl)
  have e₂ : s₂.gpr .ebp = s.gpr .ebp := (k₂ _ (by simp [kept])).trans e₁
  -- Half 0's outputs to slot 14.
  have w14 : InRegions s₂.wr (addr (s₂.gpr .ebp) (4 * 14)) 4 := by
    rw [wr₂, e₂, ← e₁]; exact hok₁.slotIn 14 (by decide)
  let s₃ : State := { s₂ with mem := s₂.mem.writeW (addr (s₂.gpr .ebp) (4 * 14)) (s₂.gpr .ebx) }
  have h₃ : runBlock isa [.store (at_ .ebp (4 * 14)) .ebx] s₂ = some s₃ := runBlock_store w14
  have e₃ : s₃.gpr .ebp = s.gpr .ebp := e₂
  obtain ⟨s₄, h₄, y₄, rd₄, wr₄, k₄, f₄⟩ := sbox_ok (h := 1) (by decide)
    (ok_fewer (hok₁.congr (e₃.trans e₁.symm) (show s₃.gpr .esi = s₁.gpr .esi from k₂ .esi (by simp [kept]))
      (rd₂ : s₃.rd = s₁.rd) (wr₂ : s₃.wr = s₁.wr)) rfl (by decide) rfl)
  have e₄ : s₄.gpr .ebp = s.gpr .ebp := (k₄ _ (by simp [kept])).trans e₃
  have w15 : InRegions s₄.wr (addr (s₄.gpr .ebp) (4 * 15)) 4 := by
    rw [wr₄, show s₃.wr = s₁.wr from wr₂, e₄, ← e₁]; exact hok₁.slotIn 15 (by decide)
  let s₅ : State := { s₄ with mem := s₄.mem.writeW (addr (s₄.gpr .ebp) (4 * 15)) (s₄.gpr .ebx) }
  have h₅ : runBlock isa [.store (at_ .ebp (4 * 15)) .ebx] s₄ = some s₅ := runBlock_store w15
  have e₅ : s₅.gpr .ebp = s.gpr .ebp := e₄
  have rd₅ : s₅.rd = s₁.rd := rd₄.trans rd₂
  have wr₅ : s₅.wr = s₁.wr := wr₄.trans wr₂
  obtain ⟨s₆, h₆, L₆, R₆, rd₆, wr₆, k₆, f₆⟩ := output_ok
    (ok_fewer (hok₁.congr (e₅.trans e₁.symm) (show s₅.gpr .esi = s₁.gpr .esi from
      (k₄ .esi (by simp [kept])).trans (k₂ .esi (by simp [kept]))) rd₅ wr₅) rfl (by decide) rfl)
  -- The slots along the way.
  have sep : ∀ j k, j ≠ k → j ≤ 17 → k ≤ 17 →
      Mem.Sep (wordAddr (s.gpr .ebp) j) (32 / 8) (wordAddr (s.gpr .ebp) k) (32 / 8) :=
    fun j k h hj hk => slot_word_sep _ h (hb j hj) (hb k hk)
  have st₃ : ∀ k, k ≠ 14 → k ≤ 17 → slotW s₃ k = slotW s₂ k := fun k hk hk' => by
    show (s₂.mem.writeW (wordAddr (s₂.gpr .ebp) 14) (s₂.gpr .ebx)).readW (wordAddr (s₂.gpr .ebp) k) 32 =
      s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32
    rw [e₂, Mem.readW_writeW_sep (sep k 14 hk hk' (by decide)) (by decide)]
  have st₅ : ∀ k, k ≠ 15 → k ≤ 17 → slotW s₅ k = slotW s₄ k := fun k hk hk' => by
    show (s₄.mem.writeW (wordAddr (s₄.gpr .ebp) 15) (s₄.gpr .ebx)).readW (wordAddr (s₄.gpr .ebp) k) 32 =
      s₄.mem.readW (wordAddr (s₄.gpr .ebp) k) 32
    rw [e₄, Mem.readW_writeW_sep (sep k 15 hk hk' (by decide)) (by decide)]
  have fr₂ : ∀ k, 7 ≤ k → k ≤ 17 → slotW s₂ k = slotW s₁ k := fun k h₁' h₂' => by
    show s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32 = s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32
    rw [e₂, ← e₁]
    exact slot_frame (n := 7) f₂ h₁' (by rw [e₁]; exact hb k h₂')
  have fr₄ : ∀ k, 14 ≤ k → k ≤ 17 → slotW s₄ k = slotW s₃ k := fun k h₁' h₂' => by
    show s₄.mem.readW (wordAddr (s₄.gpr .ebp) k) 32 = s₃.mem.readW (wordAddr (s₃.gpr .ebp) k) 32
    rw [e₄, ← e₃]
    exact slot_frame (n := 14) f₄ h₁' (by rw [e₃]; exact hb k h₂')
  have slotLR : ∀ k, 16 ≤ k → k ≤ 17 → slotW s₅ k = slotW s k := fun k h₁' h₂' => by
    rw [st₅ k (by omega_arith) h₂', fr₄ k (by omega_arith) h₂', st₃ k (by omega_arith) h₂', fr₂ k (by omega_arith) h₂']
    rcases (by omega_arith : k = 16 ∨ k = 17) with rfl | rfl
    · exact L₁
    · exact R₁
  have slot14 : slotW s₅ 14 = s₂.gpr .ebx := by
    rw [st₅ 14 (by decide) (by decide), fr₄ 14 (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  have slot15 : slotW s₅ 15 = s₄.gpr .ebx := Mem.readW_writeW_self32 _ _ _
  have box₄ : ∀ p, boxIn 1 s₃ p = boxIn 1 s₁ p := fun p => by
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
    have hu := pSrc_lt j hj
    rw [R₆ j hj, oGR, ite_eq_left hj, BitVec.getLsbD_xor, getLsbD_roundFunction _ _ hj, xorBits_cons,
      xorBits_cons, xorBits_nil, Bool.xor_false]
    have hL : bitOf (oW s₅) (64 + j) = (slotW s slotL).getLsbD j := by
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, bitOf, oW, show (64 + j) / 32 = 2 by omega_arith,
        show (64 + j) % 32 = j by omega_arith]
      rw [slotLR slotL (by decide) (by decide)]
    rw [hL, Bool.xor_comm]
    congr 1
    obtain ⟨b, hb', hbe⟩ : ∃ b, b < 4 ∧ pSrc j % 4 = b := ⟨_, Nat.mod_lt _ (by decide), rfl⟩
    by_cases hh : pSrc j / 4 < 4
    · -- Half 0, in slot 14.
      have hi : boxOf 0 (pSrc j / 4) = 7 - pSrc j / 4 := by simp [boxOf]
      have ho := off_lt4 0 (by decide) _ hh b hb'
      have hpos : sAtom (pSrc j) = 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b := by
        rw [sAtom, outHalf, ite_eq_left hh, ite_eq_left rfl, outPos, hi, Nat.mod_eq_of_lt hh, hbe]
      have hbit : bitOf (oW s₅) (sAtom (pSrc j)) =
          (slotW s₅ 14).getLsbD (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b) := by
        rw [hpos]
        simp only [↓reduceIte, bitOf, oW,
          Nat.div_eq_of_lt (show 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b < 32 by omega_arith),
          Nat.mod_eq_of_lt (show 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b < 32 by omega_arith)]
      rw [hbit, slot14, y₂ _ hh b hb', boxIn_eq hx (by decide) hh ho, hi]
      simp only [hbe]
    · -- Half 1, in slot 15.
      have hm : pSrc j / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
      have hi : boxOf 1 (pSrc j / 4 % 4) = 7 - pSrc j / 4 := by simp only [boxOf]; omega_arith
      have ho := off_lt4 1 (by decide) _ hm b hb'
      have hpos : sAtom (pSrc j) = 32 + (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b) := by
        rw [sAtom, outHalf, ite_eq_right hh, ite_eq_right (by decide), outPos, hi, hbe]
      have hbit : bitOf (oW s₅) (sAtom (pSrc j)) =
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
    have cw : ∀ k ≤ 17, (slotRegion rCfg s).Contains (wordAddr (s.gpr .ebp) k) (32 / 8) := fun k hk => by
      rw [wordAddr_eq _ (by omega_arith)]
      exact Offset.contains_base _ (by simp only [rCfg]; omega_arith) (by omega_arith)
    have f₃ : Frame [slotRegion rCfg s] s₂.mem s₃.mem := by
      show Frame _ s₂.mem (s₂.mem.writeW (wordAddr (s₂.gpr .ebp) 14) _)
      rw [e₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 14 (by decide))
    have f₅ : Frame [slotRegion rCfg s] s₄.mem s₅.mem := by
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
  have rd : ∀ d, d + 4 ≤ 384 → s.mem.readW ((s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 32 =
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
  have e₁ : s₁.gpr .ebp = s₀.gpr .ebp := (k₁ .ebp (by simp [kept])).trans h.same.ebp
  have hsub : ∀ r ∈ [slotRegion rCfg s], ∃ r' ∈ [xR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [slotRegion, xR]; rw [show rCfg.base = .ebp from rfl, h.same.ebp]
    exact Region.sub_prefix (by decide)
  have same₁ : Same s₀ s₁ :=
    ⟨e₁, (k₁ .esp (by simp [kept])).trans h.same.esp, rd₁.trans h.same.rd, wr₁.trans h.same.wr,
      h.same.frame.trans (f₁.sub hsub)⟩
  -- The counters past the round's slots.
  have keep : ∀ k, 18 ≤ k → k < 21 → slotW s₁ k = slotW s k := fun k h₁' h₂' => by
    show s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32 = s.mem.readW (wordAddr (s.gpr .ebp) k) 32
    rw [e₁, ← h.same.ebp]
    exact slot_frame (n := 18) f₁ h₁' (by rw [h.same.ebp]; have := hp.fit; omega_arith)
  have i₁ : s₁.gpr .esi = s.gpr .esi := k₁ .esi (by simp [kept])
  -- `roundTail`.
  have in20 := hp.slotIn' same₁ (k := slotStep) (by decide)
  have in18 := hp.slotIn' same₁ (k := slotRounds) (by decide)
  have w18 := hp.slotIn same₁ (k := slotRounds) (by decide)
  rw [e₁] at in20 in18 w18
  refine wp_ldm e₁ in20 fun s₂' u₂' => wp_add fun s₂ u₂ _ => wp_ldm (B := s₀.gpr .ebp)
    (by rw [u₂.other _ (by decide), u₂'.other _ (by decide), e₁])
    (by rw [u₂.rd, u₂.wr, u₂'.rd, u₂'.wr]; exact in18) fun s₃ u₃ => wp_subi fun s₄ u₄ _ z₄ => ?_
  have e₄ : s₄.gpr .ebp = s₀.gpr .ebp := by rw [u₄.other _ (by decide), u₃.other _ (by decide),
    u₂.other _ (by decide), u₂'.other _ (by decide), e₁]
  refine wp_stm e₄ (by rw [u₄.wr, u₃.wr, u₂.wr, u₂'.wr]; exact w18) fun s₅ w₅ => WP.block_nil ?_
  have m₅ : s₅.mem = s₁.mem.writeW (wordAddr (s₀.gpr .ebp) slotRounds) (s₄.gpr .eax) := by
    rw [w₅.mem, u₄.mem, u₃.mem, u₂.mem, u₂'.mem]
  have g₅ : ∀ r, r ≠ .esi → r ≠ .eax → s₅.gpr r = s₁.gpr r := fun r h₁' h₂' => by
    rw [w₅.gpr, u₄.other _ h₂', u₃.other _ h₂', u₂.other _ h₁', u₂'.other _ h₂']
  have e₅ : s₅.gpr .ebp = s₀.gpr .ebp := by rw [g₅ _ (by decide) (by decide), e₁]
  have r18 : slotW s₁ slotRounds = BitVec.ofNat 32 (16 - j) := by rw [keep _ (by decide) (by decide), h.rcnt]
  have ax₄ : s₄.gpr .eax = BitVec.ofNat 32 (16 - (j + 1)) := by
    rw [u₄.gpr, u₃.gpr, u₂.mem, u₂'.mem, ← e₁, ← slotW, r18, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  have other : ∀ k, k ≠ slotRounds → k < 21 → slotW s₅ k = slotW s₁ k := fun k hk hk' => by
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
  have w18 := hp.slotIn h (k := slotRounds) (by decide)
  rw [h.ebp] at w18
  refine WP.seq (wp_movi fun s₁ u₁ => wp_stm (B := s₀.gpr .ebp) (by rw [u₁.other _ (by decide), h.ebp])
    (by rw [u₁.wr]; exact w18) fun s₂ w₂ => WP.block_nil ?_)
  have g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by rw [w₂.gpr, u₁.other _ hr]
  have e₂ : s₂.gpr .ebp = s₀.gpr .ebp := by rw [g₂ _ (by decide), h.ebp]
  have m₂ : s₂.mem = s.mem.writeW (wordAddr (s₀.gpr .ebp) slotRounds) (16 : BitVec 32) := by rw [w₂.mem, u₁.mem, u₁.gpr]
  have other : ∀ k, k ≠ slotRounds → k < 21 → slotW s₂ k = slotW s k := fun k hk hk' => by
    show s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32 = s.mem.readW (wordAddr (s.gpr .ebp) k) 32
    rw [m₂, e₂, h.ebp, rd_wr_ne hp _ _ hk hk' (by decide)]
  have hI : PInv s₀ p lr 0 s₂ :=
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
  have rin : ∀ k, k < 21 → InRegions (s₁.rd ++ s₁.wr) (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn' h₁.same hk; rwa [e₁] at this
  have win : ∀ k, k < 21 → InRegions s₁.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn h₁.same hk; rwa [e₁] at this
  refine wp_ldm (o := 4 * slotStep) e₁ (rin _ (by decide)) fun t₁ u₁ => wp_movi fun t₂ u₂ =>
    wp_sub fun t₃ u₃ _ => wp_add fun t₄ u₄ _ => wp_movi fun t₅ u₅ => wp_sub fun t₆ u₆ _ => ?_
  have g₆ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₆.gpr r = s₁.gpr r := fun r ha hc hs => by
    rw [u₆.other _ ha, u₅.other _ ha, u₄.other _ hs, u₃.other _ ha, u₂.other _ ha, u₁.other _ hc]
  have e₆ : t₆.gpr .ebp = s₀.gpr .ebp := by rw [g₆ _ (by decide) (by decide) (by decide), e₁]
  have wr₆ : t₆.wr = s₁.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have rd₆ : t₆.rd = s₁.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have m₆ : t₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have stp : t₁.gpr .ecx = stride p := by rw [u₁.gpr, ← e₁, ← slotW, h₁.step]
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
    fun t₁₂ u₁₂ => wp_subi fun t₁₃ u₁₃ _ z₁₃ => ?_
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
  have rd₁ : ∀ k, slotW s₁ k = s₁.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₁]
  have ax₉L : t₉.gpr .eax = slotW s₁ slotL := by
    rw [u₉.other _ (by decide), u₈.gpr, w₇.mem, m₆, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  have ax₉R : t₉.gpr .ecx = slotW s₁ slotR := by
    rw [u₉.gpr, u₈.mem, w₇.mem, m₆, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  have pc₁₂ : t₁₂.gpr .eax = slotW s₁ slotPasses := by
    rw [u₁₂.gpr, m₁₁, rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  have e₁₄ : t₁₄.gpr .ebp = s₀.gpr .ebp := by rw [w₁₄.gpr, e₁₃]
  have sl : ∀ k, slotW t₁₄ k = t₁₄.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₁₄]
  have g₁₄ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₁₄.gpr r = s₁.gpr r := fun r ha hc hs => by
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
  have kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => hoth _ (List.all_eq_true.mp ip_kept r hr)
  have e : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  have bit : ∀ j g, (j, g) ∈ [(slotL, ipGL), (slotR, ipGR)] → ∀ p < 32,
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
  have kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => hoth _ (List.all_eq_true.mp fp_kept r hr)
  have e : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  have bit : ∀ j g, (j, g) ∈ [(0, fpG0), (1, fpG1)] → ∀ p < 32,
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
  have xC : ∀ k, k < 21 → (xR s₀).Contains (wordAddr (s₀.gpr .ebp) k) (32 / 8) := fun k hk =>
    contains_w (by have := hp.fit; omega_arith) (by omega_arith)
  have same₀ : Same s₀ s₀ := ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  have win : ∀ k, k < 21 → InRegions s₀.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => hp.slotIn same₀ hk
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_stm (o := 4 * 0) rfl (win 0 (by decide)) fun s₁ w₁ =>
    wp_stm (o := 4 * 1) (by rw [w₁.gpr]) (by rw [w₁.wr]; exact win 1 (by decide)) fun s₂ w₂ => WP.block_nil ?_
  have m₂ : s₂.mem = (s₀.mem.writeW (wordAddr (s₀.gpr .ebp) 0) (s₀.gpr .eax)).writeW (wordAddr (s₀.gpr .ebp) 1)
      (s₀.gpr .edx) := by rw [w₂.mem, w₁.mem, w₁.gpr]
  have same₂ : Same s₀ s₂ := ⟨by rw [w₂.gpr, w₁.gpr], by rw [w₂.gpr, w₁.gpr], by rw [w₂.rd, w₁.rd],
    by rw [w₂.wr, w₁.wr], by
      rw [m₂]; exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (xC 0 (by decide))).writeW
        (List.mem_singleton_self _) _ (xC 1 (by decide))⟩
  have sl₂ : ∀ k, slotW s₂ k = s₂.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, same₂.ebp]
  have x₂ : slotW s₂ 0 ++ slotW s₂ 1 = s₀.gpr .eax ++ s₀.gpr .edx := by
    rw [sl₂, sl₂, m₂, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
      Mem.readW_writeW_self32]
  obtain ⟨s₃, h₃, ip₃, rd₃, wr₃, k₃, f₃⟩ := ip_ok (oCfg_ok hp same₂)
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  have e₃ : s₃.gpr .ebp = s₀.gpr .ebp := (k₃ .ebp (by simp [kept])).trans same₂.ebp
  have same₃ : Same s₀ s₃ := ⟨e₃, (k₃ .esp (by simp [kept])).trans same₂.esp, rd₃.trans same₂.rd,
    wr₃.trans same₂.wr, same₂.frame.trans (f₃.sub (oCfg_sub same₂))⟩
  have win₃ : ∀ k, k < 21 → InRegions s₃.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn same₃ hk; rwa [e₃] at this
  refine wp_movi fun s₄ u₄ => wp_stm (o := 4 * slotPasses) (B := s₀.gpr .ebp) (by rw [u₄.other _ (by decide), e₃])
    (by rw [u₄.wr]; exact win₃ _ (by decide)) fun s₅ w₅ => wp_movi fun s₆ u₆ =>
    wp_stm (o := 4 * slotStep) (B := s₀.gpr .ebp) (by rw [u₆.other _ (by decide), w₅.gpr, u₄.other _ (by decide), e₃])
    (by rw [u₆.wr, w₅.wr, u₄.wr]; exact win₃ _ (by decide)) fun s₇ w₇ => WP.block_nil ?_
  have m₇ : s₇.mem = (s₃.mem.writeW (wordAddr (s₀.gpr .ebp) slotPasses) (3 : BitVec 32)).writeW
      (wordAddr (s₀.gpr .ebp) slotStep) (8 : BitVec 32) := by
    rw [w₇.mem, u₆.mem, u₆.gpr, w₅.mem, u₄.mem, u₄.gpr]
  have g₇ : ∀ r, r ≠ .eax → s₇.gpr r = s₃.gpr r := fun r hr => by
    rw [w₇.gpr, u₆.other _ hr, w₅.gpr, u₄.other _ hr]
  have e₇ : s₇.gpr .ebp = s₀.gpr .ebp := by rw [g₇ _ (by decide), e₃]
  have sl₇ : ∀ k, slotW s₇ k = s₇.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₇]
  have sl₃ : ∀ k, slotW s₃ k = s₃.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₃]
  have esi₇ : s₇.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * kpos 0 0) := by
    rw [g₇ _ (by decide), k₃ .esi (by simp [kept]), show s₂.gpr .esi = s₀.gpr .esi by rw [w₂.gpr, w₁.gpr]]
    simp [kpos]
  have hO : OInv s₀ (s₀.gpr .eax ++ s₀.gpr .edx) 0 s₇ :=
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
  have same₉ : Same s₀ s₉ := ⟨by rw [u₉.other _ (by decide)]; exact h₈.same.ebp,
    by rw [u₉.other _ (by decide)]; exact h₈.same.esp, by rw [u₉.rd]; exact h₈.same.rd,
    by rw [u₉.wr]; exact h₈.same.wr, by rw [u₉.mem]; exact h₈.same.frame⟩
  obtain ⟨s₁₀, h₁₀, fp₁₀, rd₁₀, wr₁₀, k₁₀, f₁₀⟩ := fp_ok (oCfg_ok hp same₉)
  refine WP.of_runBlock ⟨s₁₀, h₁₀, ?_⟩
  have e₁₀ : s₁₀.gpr .ebp = s₀.gpr .ebp := (k₁₀ .ebp (by simp [kept])).trans same₉.ebp
  have same₁₀ : Same s₀ s₁₀ := ⟨e₁₀, (k₁₀ .esp (by simp [kept])).trans same₉.esp, rd₁₀.trans same₉.rd,
    wr₁₀.trans same₉.wr, same₉.frame.trans (f₁₀.sub (oCfg_sub same₉))⟩
  have rin : ∀ k, k < 21 → InRegions (s₁₀.rd ++ s₁₀.wr) (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
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
    have sl₉ : ∀ k, slotW s₉ k = slotW s₈ k := fun k => by rw [slotW, slotW, u₉.mem, u₉.other _ (by decide)]
    rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₂.gpr, u₁₁.mem, ← sl₁₀, ← sl₁₀, fp₁₀, sl₉, sl₉, tdes_eq, ← h₈.halves]

end VG.Proof.CmacTripleDes.X86
