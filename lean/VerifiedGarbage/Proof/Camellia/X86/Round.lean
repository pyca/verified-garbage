module

public import VerifiedGarbage.Impl.Camellia.X86.Sbox
public import VerifiedGarbage.Proof.Camellia.SboxTable
public import VerifiedGarbage.Proof.Framework.X86.Straight
public import VerifiedGarbage.Proof.Camellia.Bitsliced32
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Camellia.Bitsliced
public import VerifiedGarbage.Impl.Camellia.X86.Ecb
public import VerifiedGarbage.Proof.Framework.X86.Linear

/-! ### `Camellia.X86.Linear`, which this module and modules that import it used -/

section

/-!
# The linear layers of bitsliced Camellia on x86 (32-bit), by evaluation

As on ARMv7 (`Proof/Camellia/Arm/Round.lean`), with every word in slots
(`Framework/X86/Linear.lean`): the kernel runs each linear block on its
input words as atoms and compares every output slot with the XOR of input
bits given here, bit `t` of input word `i` being `32 i + t`. The slots a
block must keep are outputs too, each the input word it held.

* A round's left word (`preL`): the halves' planes (slots 40–71) are input
  words `0 … 31`, the subkeys' planes at `kp` words `32 …`.
* The middle (`midLR`): the left word's S-box output (slots 0–7) is words
  `0 … 7`, the halves' planes `8 … 39`, the subkeys' planes at `kp` words
  `40 …`.
* The end (`postP`): the right word's S-box output (slots 0–7) is words
  `0 … 7`, the left word's selected output (slots 32–39) words `8 … 15`,
  the halves' planes words `16 … 47`.
* The whitening: the halves' planes are words `0 … 31`, the two entries
  at `kp` words `32 … 63`.
* The transposes (`toBsWord`, `fromBsWord`): the tail buffer's eight
  blocks (slots 72–103), or the halves' planes, are words `0 … 31`.
* A subkey's planes (`keyPlane`): its word, in slot 0 of the scratch
  buffer (an external word of the entry at `kp`), is input word `0`.

Position `p = 8 i + b` of a plane of word `w` is byte `4 w + i` of the half
of block `b`.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.Bitslice VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb)
open VG.Proof.Camellia (pRow)

/-! ## A round -/

/-- The slots below the tail buffer; the two entries' 32 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := tailSlot, ext := kp, exts := 32 }

/-- The slots below the tail buffer, without the subkeys. -/
def linCfg : Cfg := { base := sb, slots := tailSlot, ext := kp, exts := 0 }

/-- Both halves (slots 40–71), from input word `x`. -/
def halvesIns (x : Nat) : List (Nat × Nat) := (List.range 32).map fun k => (d1Slot + k, x + k)

/-- Slot `j` keeps its input word `x`. -/
def keepOut (j x : Nat) : Nat × (Nat → List Nat) := (j, fun p => [32 * x + p])

/-- The halves kept, from input word `x`. -/
def halvesKeep (x : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => keepOut (d1Slot + k) (x + k)

/-- The left word's S-box input: plane `j` at `p` is the selected plane of
the source half (at slot `src`) XOR the subkey's, at word `off` of `kp`. -/
def preG (off src j p : Nat) : List Nat :=
  [32 * (src - d1Slot + W32.inSrc (p / 8) j) + p, 32 * (32 + off + W32.inSrc (p / 8) j) + p]

def preOuts (off src : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map (fun j => (j, preG off src j)) ++ halvesKeep 0

theorem preL0_check :
    check (lanes 32 11) layerCfg (linExt 32) (preL 0 d1Slot) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (preOuts 0 d1Slot)) = true := by
  decide +kernel

theorem preL16_check :
    check (lanes 32 11) layerCfg (linExt 32) (preL 16 d2Slot) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (preOuts 16 d2Slot)) = true := by
  decide +kernel

/-- The S-box's output (slots `0 … 7`), then the halves. -/
def midIns : List (Nat × Nat) := (List.range 8).map (fun k => (k, k)) ++ halvesIns 8

/-- The left word's selected output, to slot `32 + j`. -/
def ylG (j p : Nat) : List Nat := [32 * W32.outSrc (p / 8) j + p]

/-- The right word's S-box input. -/
def midG (off src j p : Nat) : List Nat :=
  [32 * (16 + (src - d1Slot) + W32.inSrc (4 + p / 8) j) + p,
   32 * (48 + off + W32.inSrc (4 + p / 8) j) + p]

def midOuts (off src : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map (fun j => (j, midG off src j)) ++
    (List.range 8).map (fun j => (ylSlot + j, ylG j)) ++ halvesKeep 8

theorem mid0_check :
    check (lanes 32 12) layerCfg (linExt 40) (midLR 0 d1Slot) (linEnv midIns)
      (linPost tailSlot 12 (midOuts 0 d1Slot)) = true := by
  decide +kernel

theorem mid16_check :
    check (lanes 32 12) layerCfg (linExt 40) (midLR 16 d2Slot) (linEnv midIns)
      (linPost tailSlot 12 (midOuts 16 d2Slot)) = true := by
  decide +kernel

/-- The S-box's output (slots `0 … 7`), the left word's output (slots
32–39) and both halves (slots 40–71). -/
def postIns : List (Nat × Nat) :=
  (List.range 8).map (fun k => (k, k)) ++ (List.range 40).map fun k => (ylSlot + k, 8 + k)

/-- The selected S-box output of byte `c` of plane `j` at position `b`. -/
def selG (j b c : Nat) : Nat :=
  if c < 4 then 32 * (8 + j) + 8 * c + b else 32 * W32.outSrc c j + 8 * (c - 4) + b

/-- Plane `8 w + j` of the half at slot `dst`, XOR the P-function of the
selected outputs. -/
def postG (dst w j p : Nat) : List Nat :=
  (32 * (16 + (dst - d1Slot) + 8 * w + j) + p) :: (pRow (4 * w + p / 8)).map (selG j (p % 8))

/-- The other half's slot. -/
def other (dst : Nat) : Nat := if dst = d1Slot then d2Slot else d1Slot

def postOuts (dst : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 16).map (fun k => (dst + k, postG dst (k / 8) (k % 8))) ++
    (List.range 16).map fun k => keepOut (other dst + k) (16 + (other dst - d1Slot) + k)

theorem post2_check :
    check (lanes 32 11) linCfg (linExt 48) (postP d2Slot) (linEnv postIns)
      (linPost tailSlot 11 (postOuts d2Slot)) = true := by
  decide +kernel

theorem post1_check :
    check (lanes 32 11) linCfg (linExt 48) (postP d1Slot) (linEnv postIns)
      (linPost tailSlot 11 (postOuts d1Slot)) = true := by
  decide +kernel

/-! ## The whitening -/

/-- Plane `i` of the halves (`D1`'s, then `D2`'s), XOR word `i` (or, with
`swap`, word `(i + 16) % 32`) of the entries at `kp`. -/
def whitenG (swap : Bool) (i p : Nat) : List Nat :=
  [32 * i + p, 32 * (32 + (if swap then (i + 16) % 32 else i)) + p]

def whitenOuts (swap : Bool) : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun i => (d1Slot + i, whitenG swap i)

theorem whiten0_check :
    check (lanes 32 11) layerCfg (linExt 32) (whiten false) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (whitenOuts false)) = true := by
  decide +kernel

theorem whiten1_check :
    check (lanes 32 11) layerCfg (linExt 32) (whiten true) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (whitenOuts true)) = true := by
  decide +kernel

/-! ## The transposes -/

/-- The slots below the table, without external words. -/
def bsCfg : Cfg := { base := sb, slots := keySlot, ext := sb, exts := 0 }

/-- The tail buffer's 32 words are input words `0 … 31`. -/
def tailIns : List (Nat × Nat) := (List.range 32).map fun k => (tailSlot + k, k)

/-- Plane `j` of the state's word `w`, at `p = 8 i + b`: bit `j` of byte `i`
of word `w` of block `b` (the tail buffer's word `4 b + w`). -/
def toBsG (w j p : Nat) : List Nat := [32 * (4 * (p % 8) + w) + 8 * (p / 8) + j]

def toBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => (d1Slot + k, toBsG (k / 8) (k % 8))

theorem toBs_check :
    check (lanes 32 10) bsCfg (linExt 0) ((List.range 4).flatMap toBsWord) (linEnv tailIns)
      (linPost keySlot 10 toBsOuts) = true := by
  decide +kernel

/-- Bit `8 i + j` of the tail buffer's word `t = 4 b + w`, byte `i` (from the
most significant) of word `w` of block `b`: plane `j` of the state's word
`(w + 2) % 4` at `8 i + b`. -/
def fromBsG (t k : Nat) : List Nat := [32 * (8 * ((t % 4 + 2) % 4) + k % 8) + 8 * (k / 8) + t / 4]

def fromBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun t => (tailSlot + t, fromBsG t)

theorem fromBs_check :
    check (lanes 32 10) bsCfg (linExt 0) ((List.range 4).flatMap fromBsWord) (linEnv (halvesIns 0))
      (linPost keySlot 10 fromBsOuts) = true := by
  decide +kernel

/-! ## The subkeys' planes -/

/-- The entry at `kp`; the subkey's word in slot 0 of the scratch buffer. -/
def entryCfg : Cfg := { base := kp, slots := 16, ext := sb, exts := 1 }

/-- The other word's planes, input words `1 … 8`. -/
def keyIns (w : Nat) : List (Nat × Nat) := (List.range 8).map fun j => (8 * (1 - w) + j, 1 + j)

/-- Plane `j` of a subkey's word: bit `8 i + b` is bit `8 i + j` of the word
in slot 0. -/
def keyBsG (j p : Nat) : List Nat := [8 * (p / 8) + j]

def keyOuts (w : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map (fun j => (8 * w + j, keyBsG j)) ++
    (List.range 8).map fun j => keepOut (8 * (1 - w) + j) (1 + j)

theorem keyPlanes0_check :
    check (lanes 32 9) entryCfg (linExt 0) ((List.range 8).flatMap (keyPlane 0)) (linEnv (keyIns 0))
      (linPost 16 9 (keyOuts 0)) = true := by
  decide +kernel

theorem keyPlanes1_check :
    check (lanes 32 9) entryCfg (linExt 0) ((List.range 8).flatMap (keyPlane 1)) (linEnv (keyIns 1))
      (linPost 16 9 (keyOuts 1)) = true := by
  decide +kernel

end VG.Proof.Camellia.X86

end

end

/-! ### `Camellia.X86.Sbox`, which only this module used -/

section

/-!
# The bitsliced Camellia S-box on x86 (32-bit)

As on ARMv7 (`Proof/Camellia/Arm/Sbox.lean`), with the planes in slots: the
kernel evaluates `sboxCode` once on truth tables of the 256 inputs
(`Bitslice.table`) and compares the result with the specification's
`SBOX1`. `sbox_ok` then gives, at every bit position `p`, `SBOX1` of the
byte formed by bit `p` of the planes in slots `0 … 7`.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb tmpRegs)
open VG.Proof.Camellia
open VG.Proof.Camellia.W32 (bsByte getLsbD_bsByte)

/-- The S-box's memory: its planes and spill slots, at `edi`. -/
def sboxCfg : Cfg := { base := sb, slots := 32, ext := sb, exts := 0 }

/-- Slot `j` of the scratch buffer. -/
abbrev slotW (s : State) (j : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr sb) j) 32

def sboxEnv : Env Nat :=
  { reg := fun _ => none, slot := fun k => if k < 8 then some (inT k) else none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.slot j == some (sbox1T j)

theorem sbox_check :
    check (table 32 256) sboxCfg (fun _ => none) sboxCode sboxEnv sboxPost = true := by
  lit_decide

/-- The registers the layers may write. -/
theorem not_tmp (r : Reg) (hr : r ∉ tmpRegs) : r ∈ [Reg.esp, .esi, .edi] := by
  revert hr; cases r <;> decide

/-- `SBOX1`, at every bit position of the planes in slots `0 … 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32,
        (slotW s' j).getLsbD p = (Spec.Camellia.sbox1 (bsByte (slotW s) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  obtain hout : ∀ j < 8, e'.slot j = some (sbox1T j) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  obtain key : ∀ p < 32, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (slotW s) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    obtain hc := (bsByte (slotW s) p).isLt
    refine run (table_sound hp hc) hok ⟨(fun r a h => by cases h), fun k a _ h => ?_,
      (fun _ _ _ h => by cases h)⟩ he
    simp only [sboxEnv] at h
    split at h
    · rename_i hk8
      cases h
      simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
        BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8, slotW, sboxCfg]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_using [])
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    obtain hc := (bsByte (slotW s) p).isLt
    have := p₁.rel.slot j _ (by simp [sboxCfg]; omega_using [hj]) (hout j hj)
    have hb : s''.gpr sb = s.gpr sb := p₁.base
    simp only [TableRel, sboxCfg, hb] at this
    rw [slotW, hb, ← this, testBit_sbox1T hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have h : ([Reg.esp, .esi, .edi].all fun r => sboxCode.all fun i => i.dst != some r) = true := by
      decide +kernel
    simp [List.all_eq_true.mp h r (not_tmp r hr)]

end VG.Proof.Camellia.X86

end

end


/-!
# A round of bitsliced Camellia on x86 (32-bit)

As on ARMv7 (`Proof/Camellia/Arm/Round.lean`), with the S-box's planes in
slots 0–7: `round_ok`, with the half `D1` (or `D2`) in its slots, the other
half in its slots and the subkey's planes at `kp`, `round off src dst`
leaves `d2 ^ F(d1, k)` in the other half's slots, keeping the first half's
and writing only the slots below the tail buffer. The layers are composed
from their checks (`Linear.lean`, `Sbox.lean`) and `W32.round_rel`.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Bitslice (lanes bitOf xorBits bitOf_word xorBits_cons xorBits_nil)
open VG.Impl.Aes.X86 (sb tmpRegs)
open VG.Proof.Camellia (pRow pRow_lt)

/-- Word `k` of the table entries at `kp`. -/
abbrev keyW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr kp) k) 32

/-- The sixteen planes of the half at slot `d`. -/
def half (s : State) (d : Nat) : Nat → BitVec 32 := fun i => slotW s (d + i)

/-- A slot kept by a linear block: its output is its own input word. -/
theorem keep_word {W : Nat → BitVec 32} {i : Nat} {v v' : BitVec 32} (hW : W i = v)
    (h : ∀ p < 32, v'.getLsbD p = xorBits W [32 * i + p]) : v' = v :=
  BitVec.eq_of_getLsbD_eq fun p hp => by
    rw [h p hp, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, hW]

theorem ok_sbox {s : State} (h : Ok layerCfg s) : Ok sboxCfg s where
  slotIn k hk := h.slotIn k (by simp [sboxCfg, layerCfg, tailSlot] at hk ⊢; omega_using [hk])
  extIn k hk := by simp [sboxCfg] at hk
  fit := by have := h.fit; simp [sboxCfg, layerCfg, tailSlot] at this ⊢; omega_using [this]
  sep k _ j hj := by simp [sboxCfg] at hj

theorem ok_lin {s : State} (h : Ok layerCfg s) : Ok linCfg s where
  slotIn k hk := h.slotIn k (by simpa [linCfg, layerCfg] using hk)
  extIn k hk := by simp [linCfg] at hk
  fit := by have := h.fit; simpa [linCfg, layerCfg] using this
  sep k _ j hj := by simp [linCfg] at hj

theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

/-- A frame of the first `n` slots keeps slot `k ≥ n`. -/
theorem slot_above {m m' : Mem} {b : BitVec 32} {n k : Nat} (hf : Frame [⟨b.setWidth 64, 4 * n⟩] m m')
    (hk : n ≤ k) (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  obtain e : wordAddr b k = b.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega_using [hfit])
  rw [e]
  exact hf.readW (r := ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have : (b.setWidth 64).toNat = b.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]
      exact VG.Offset.disjoint_base _ (by omega_using [hk]) (by omega_using [hfit])) (by decide)

/-- A frame of the slots keeps the external words. -/
theorem frame_ext {c : Cfg} {s : State} {m' : Mem} (hok : Ok c s) (hf : Frame [slotRegion c s] s.mem m')
    {j : Nat} (hj : j < c.exts) :
    m'.readW (wordAddr (s.gpr c.ext) j) 32 = s.mem.readW (wordAddr (s.gpr c.ext) j) 32 := by
  simp only [Mem.readW]
  rw [Mem.read_congr fun i hi => (hf _ fun r hr hc => ?_).symm]
  simp only [List.mem_singleton] at hr; subst hr
  have hfit := hok.fit
  simp only [slotRegion, Region.Contains] at hc
  obtain hb : ((s.gpr c.base).setWidth 64).toNat = (s.gpr c.base).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (s.gpr c.base).isLt; omega_using [])]
  obtain hi' : i < 4 := by simpa using hi
  generalize hx : wordAddr (s.gpr c.ext) j + BitVec.ofNat 64 i = x at hc
  obtain hk : (x - (s.gpr c.base).setWidth 64).toNat / 4 < c.slots := by omega_using [hc]
  obtain hsep := hok.sep _ hk j hj x
  rw [wordAddr, addr_eq (by omega_using [hfit, hc])] at hsep
  refine hsep ?_ (by rw [← hx, Mem.sub_ofNat_toNat _ (by omega_using [hi])]; exact hi')
  generalize (s.gpr c.base).setWidth 64 = B at *
  bv_omega_arith

/-- The P-function's terms, as the selected outputs of the S-boxes. -/
theorem xorBits_sel (W YL SR : Nat → BitVec 32) (hS : ∀ i < 8, W i = SR i) (hY : ∀ j < 8, W (8 + j) = YL j)
    {j b : Nat} (hj : j < 8) (hb : b < 8) :
    ∀ l : List Nat, (∀ c ∈ l, c < 8) → xorBits W (l.map (selG j b)) = W32.rowSel YL SR j b l
  | [], _ => rfl
  | c :: l, hl => by
    obtain hc := hl c List.mem_cons_self
    obtain ih := xorBits_sel W YL SR hS hY hj hb l fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, xorBits_cons, W32.rowSel, List.foldr_cons] at ih ⊢
    rw [ih]
    congr 1
    simp only [selG, W32.ySel]
    split
    · rw [Nat.add_assoc, bitOf_word _ _ _ (by omega_arith), hY j hj]
    · rw [Nat.add_assoc, bitOf_word _ _ _ (by omega_using [hb, hc]), hS _ (W32.outSrc_lt hj)]

/-- The two rounds of a pair: `D2 ^= F(D1, k)` with the first entry at
`kp`, `D1 ^= F(D2, k)` with the second. -/
def RoundCase (off src dst : Nat) : Prop :=
  (off = 0 ∧ src = d1Slot ∧ dst = d2Slot) ∨ (off = 16 ∧ src = d2Slot ∧ dst = d1Slot)

theorem halvesIns_mem {x j i : Nat} (h : (j, i) ∈ halvesIns x) : ∃ k < 32, j = d1Slot + k ∧ i = x + k := by
  simp only [halvesIns, List.mem_map, List.mem_range, Prod.mk.injEq] at h
  obtain ⟨k, hk, rfl, rfl⟩ := h
  exact ⟨k, hk, rfl, rfl⟩

theorem halvesKeep_mem {x k : Nat} (hk : k < 32) : keepOut (d1Slot + k) (x + k) ∈ halvesKeep x := by
  simp only [halvesKeep, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩

/-- A round, with the subkey at word `off` of `kp`. -/
theorem round_ok {off src dst : Nat}
    (hA : check (lanes 32 11) layerCfg (linExt 32) (preL off src) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (preOuts off src)) = true)
    (hC : check (lanes 32 12) layerCfg (linExt 40) (midLR off src) (linEnv midIns)
      (linPost tailSlot 12 (midOuts off src)) = true)
    (hE : check (lanes 32 11) linCfg (linExt 48) (postP dst) (linEnv postIns)
      (linPost tailSlot 11 (postOuts dst)) = true)
    (hall : ([Reg.esp, .esi, .edi].all fun r =>
      (preL off src ++ midLR off src ++ postP dst).all fun i => i.dst != some r) = true)
    (hcase : RoundCase off src dst)
    {s : State} (hok : Ok layerCfg s) {d1 d2 : Nat → BitVec 64} {k : BitVec 64}
    (hQ : W32.HalfRel (half s src) d1) (hK : W32.HalfRel (fun i => keyW s (off + i)) fun _ => k)
    (hR : W32.HalfRel (half s dst) d2) :
    ∃ s', runBlock isa (round off src dst) s = some s' ∧
      W32.HalfRel (half s' dst) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) ∧
      (∀ i < 16, slotW s' (src + i) = slotW s (src + i)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  have hall' : ∀ r, r ∉ tmpRegs → ((preL off src).all fun i => i.dst != some r) = true ∧
      ((midLR off src).all fun i => i.dst != some r) = true ∧
      ((postP dst).all fun i => i.dst != some r) = true := fun r hr => by
    have := List.all_eq_true.mp hall r (not_tmp r hr)
    simp only [List.all_append, Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hsb : sb ∉ tmpRegs := by decide
  have hkp : kp ∉ tmpRegs := by decide
  have hfit := hok.fit
  simp only [layerCfg, tailSlot] at hfit
  have hsd : (src = d1Slot ∧ dst = d2Slot) ∨ (src = d2Slot ∧ dst = d1Slot) := by
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  have hsrc : d1Slot ≤ src ∧ src + 16 ≤ d1Slot + 32 := by
    rcases hsd with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [d1Slot, d2Slot]
  have hdst : d1Slot ≤ dst ∧ dst + 16 ≤ d1Slot + 32 := by
    rcases hsd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [d1Slot, d2Slot]
  have hother : other dst = src := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hoff : off + 16 ≤ 32 := by rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  -- The left word's S-box input.
  let W₁ : Nat → BitVec 32 := fun i => if i < 32 then slotW s (d1Slot + i) else keyW s (i - 32)
  obtain ⟨s₁, h₁, x₁, rd₁, wr₁, o₁, f₁⟩ := linear_ok hA hok W₁
    (fun j i hji hj => by
      obtain ⟨k, hk, rfl, rfl⟩ := halvesIns_mem hji
      exact ⟨by omega_arith, by simp [W₁, hk]; rfl⟩)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₁, show ¬ 32 + j < 32 by omega_arith]; rfl⟩)
  simp only [layerCfg] at x₁
  have b₁ : s₁.gpr sb = s.gpr sb := o₁ _ (hall' sb hsb).1
  have kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (hall' kp hkp).1
  have hXL : ∀ j < 8, ∀ p < 32, (slotW s₁ j).getLsbD p =
      ((half s src (W32.inSrc (p / 8) j)).getLsbD p ^^ (keyW s (off + W32.inSrc (p / 8) j)).getLsbD p) := by
    intro j hj p hp
    have hi := W32.inSrc_lt (c := p / 8) hj
    rw [slotW, b₁, x₁ j (preG off src j) (List.mem_append_left _
        (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)) p hp,
      preG, xorBits_cons, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, Bool.xor_false]
    simp only [W₁, half, show src - d1Slot + W32.inSrc (p / 8) j < 32 by omega_arith, ↓reduceIte,
      show ¬ 32 + off + W32.inSrc (p / 8) j < 32 by omega_arith,
      show 32 + off + W32.inSrc (p / 8) j - 32 = off + W32.inSrc (p / 8) j by omega_arith,
      show d1Slot + (src - d1Slot + W32.inSrc (p / 8) j) = src + W32.inSrc (p / 8) j by omega_arith]
  have hok₁ : Ok layerCfg s₁ := hok.congr b₁ kp₁ rd₁ wr₁
  have keep₁ : ∀ i < 32, slotW s₁ (d1Slot + i) = slotW s (d1Slot + i) := fun i hi => by
    rw [slotW, b₁]
    exact keep_word (W := W₁) (i := 0 + i) (by simp [W₁, hi])
      (x₁ _ _ (List.mem_append_right _ (halvesKeep_mem (x := 0) hi)))
  have kw₁ : ∀ j < 32, keyW s₁ j = keyW s j := fun j hj => by
    simp only [keyW, kp₁]; exact frame_ext hok f₁ (by simpa [layerCfg] using hj)
  -- The left word's S-box.
  obtain ⟨s₂, h₂, sx₂, rd₂, wr₂, o₂, f₂⟩ := sbox_ok (ok_sbox hok₁)
  have b₂ : s₂.gpr sb = s.gpr sb := (o₂ sb hsb).trans b₁
  have kp₂ : s₂.gpr kp = s.gpr kp := (o₂ kp hkp).trans kp₁
  have hok₂ : Ok layerCfg s₂ := hok₁.congr (o₂ sb hsb) (o₂ kp hkp) rd₂ wr₂
  have above₂ : ∀ k, 32 ≤ k → k < tailSlot → slotW s₂ k = slotW s₁ k := fun k h1 h2 => by
    simp only [slotW, o₂ sb hsb]
    refine slot_above (n := 32) (by simpa [slotRegion, sboxCfg] using f₂) h1 ?_
    rw [b₁]; simp [tailSlot] at h2; omega_arith
  have sub₂ : ∀ {t : State}, Frame [slotRegion sboxCfg t] t.mem s₂.mem →
      Frame [slotRegion layerCfg t] t.mem s₂.mem := fun f => f.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by
      simp only [slotRegion, sboxCfg, layerCfg]; exact Region.sub_prefix (by simp [tailSlot])⟩
  have kw₂ : ∀ j < 32, keyW s₂ j = keyW s j := fun j hj => by
    rw [← kw₁ j hj]; simp only [keyW, o₂ kp hkp]
    exact frame_ext hok₁ (sub₂ f₂) (by simpa [layerCfg] using hj)
  have keep₂ : ∀ i < 32, slotW s₂ (d1Slot + i) = slotW s (d1Slot + i) := fun i hi => by
    rw [above₂ _ (by simp only [d1Slot]; omega_arith) (by simp [d1Slot, tailSlot]; omega_arith), keep₁ i hi]
  -- The left word's output selection, and the right word's S-box input.
  let W₃ : Nat → BitVec 32 := fun i =>
    if i < 8 then slotW s₂ i else if i < 40 then slotW s₂ (d1Slot + (i - 8)) else keyW s₂ (i - 40)
  obtain ⟨s₃, h₃, x₃, rd₃, wr₃, o₃, f₃⟩ := linear_ok hC hok₂ W₃
    (fun j i hji hj => by
      simp only [midIns, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      rcases hji with ⟨k, hk, rfl, rfl⟩ | hji
      · exact ⟨by omega_arith, by simp [W₃, hk]; rfl⟩
      · obtain ⟨k, hk, rfl, rfl⟩ := halvesIns_mem hji
        exact ⟨by omega_arith, by simp [W₃, show ¬ 8 + k < 8 by omega_arith, show 8 + k < 40 by omega_arith]; rfl⟩)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₃, show ¬ 40 + j < 8 by omega_arith, show ¬ 40 + j < 40 by omega_arith]; rfl⟩)
  simp only [layerCfg] at x₃
  have b₃' : s₃.gpr sb = s₂.gpr sb := o₃ _ (hall' sb hsb).2.1
  have b₃ : s₃.gpr sb = s.gpr sb := b₃'.trans b₂
  have kp₃ : s₃.gpr kp = s.gpr kp := (o₃ _ (hall' kp hkp).2.1).trans kp₂
  have hYL : ∀ j < 8, ∀ p < 32, (slotW s₃ (ylSlot + j)).getLsbD p = (slotW s₂ (W32.outSrc (p / 8) j)).getLsbD p := by
    intro j hj p hp
    have := x₃ (ylSlot + j) (ylG j) (List.mem_append_left _ (List.mem_append_right _
      (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))) p hp
    rw [slotW, b₃, ← b₂, this, ylG, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp, Bool.xor_false]
    simp only [W₃, W32.outSrc_lt hj, ↓reduceIte]
  have hXR : ∀ j < 8, ∀ p < 32, (slotW s₃ j).getLsbD p =
      ((half s src (8 + W32.inSrc (4 + p / 8) j)).getLsbD p ^^
        (keyW s (off + (8 + W32.inSrc (4 + p / 8) j))).getLsbD p) := by
    intro j hj p hp
    have hi := W32.inSrc_lt (c := 4 + p / 8) hj
    rw [slotW, b₃, ← b₂, x₃ j (midG off src j) (List.mem_append_left _ (List.mem_append_left _
        (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))) p hp,
      midG, xorBits_cons, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, Bool.xor_false]
    simp only [W₃, half, show ¬ 16 + (src - d1Slot) + W32.inSrc (4 + p / 8) j < 8 by omega_arith,
      show 16 + (src - d1Slot) + W32.inSrc (4 + p / 8) j < 40 by omega_arith, ↓reduceIte,
      show ¬ 48 + off + W32.inSrc (4 + p / 8) j < 8 by omega_arith,
      show ¬ 48 + off + W32.inSrc (4 + p / 8) j < 40 by omega_arith,
      show 48 + off + W32.inSrc (4 + p / 8) j - 40 = off + (8 + W32.inSrc (4 + p / 8) j) by omega_arith,
      kw₂ _ (show off + (8 + W32.inSrc (4 + p / 8) j) < 32 by omega_arith),
      show d1Slot + (16 + (src - d1Slot) + W32.inSrc (4 + p / 8) j - 8) =
        src + (8 + W32.inSrc (4 + p / 8) j) by omega_arith]
    rw [show src + (8 + W32.inSrc (4 + p / 8) j) = d1Slot + (src - d1Slot + 8 + W32.inSrc (4 + p / 8) j) by omega_arith,
      keep₂ _ (by omega_arith)]
  have hok₃ : Ok layerCfg s₃ := hok₂.congr b₃' (o₃ _ (hall' kp hkp).2.1) rd₃ wr₃
  have keep₃ : ∀ i < 32, slotW s₃ (d1Slot + i) = slotW s (d1Slot + i) := fun i hi => by
    rw [slotW, b₃']
    rw [keep_word (W := W₃) (i := 8 + i) (v := slotW s₂ (d1Slot + i))
      (by simp [W₃, show ¬ 8 + i < 8 by omega_arith, show 8 + i < 40 by omega_arith])
      (x₃ _ _ (List.mem_append_right _ (halvesKeep_mem (x := 8) hi)))]
    exact keep₂ i hi
  -- The right word's S-box.
  obtain ⟨s₄, h₄, sx₄, rd₄, wr₄, o₄, f₄⟩ := sbox_ok (ok_sbox hok₃)
  have b₄ : s₄.gpr sb = s.gpr sb := (o₄ sb hsb).trans b₃
  have hok₄ : Ok layerCfg s₄ := hok₃.congr (o₄ sb hsb) (o₄ kp hkp) rd₄ wr₄
  have above₄ : ∀ k, 32 ≤ k → k < tailSlot → slotW s₄ k = slotW s₃ k := fun k h1 h2 => by
    simp only [slotW, o₄ sb hsb]
    refine slot_above (n := 32) (by simpa [slotRegion, sboxCfg] using f₄) h1 ?_
    rw [b₃]; simp [tailSlot] at h2; omega_arith
  -- The right word's output selection, the P-function and the XOR.
  let W₅ : Nat → BitVec 32 := fun i => if i < 8 then slotW s₄ i else slotW s₄ (ylSlot + (i - 8))
  obtain ⟨s₅, h₅, y₅, rd₅, wr₅, o₅, f₅⟩ := linear_ok hE (ok_lin hok₄) W₅
    (fun j i hji hj => by
      simp only [postIns, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      rcases hji with ⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩
      · exact ⟨by omega_arith, by simp [W₅, hk]; rfl⟩
      · exact ⟨by omega_arith, by simp [W₅, show ¬ 8 + k < 8 by omega_arith]; rfl⟩)
    (fun j hj => by simp [linCfg] at hj)
  simp only [linCfg] at y₅
  have b₅' : s₅.gpr sb = s₄.gpr sb := o₅ _ (hall' sb hsb).2.2
  have hW₅ : ∀ i < 32, W₅ (16 + i) = slotW s (d1Slot + i) := fun i hi => by
    simp only [W₅, show ¬ 16 + i < 8 by omega_arith, ↓reduceIte, show ylSlot + (16 + i - 8) = d1Slot + i by
      simp [ylSlot, d1Slot]; omega_arith]
    rw [above₄ _ (by simp only [d1Slot]; omega_arith) (by simp [d1Slot, tailSlot]; omega_arith), keep₃ i hi]
  have hR' : ∀ w < 2, ∀ j < 8, ∀ p < 32, (half s₅ dst (8 * w + j)).getLsbD p =
      ((half s dst (8 * w + j)).getLsbD p ^^
        W32.rowSel (fun j => slotW s₃ (ylSlot + j)) (slotW s₄) j (p % 8) (pRow (4 * w + p / 8))) := by
    intro w hw j hj p hp
    have := y₅ (dst + (8 * w + j)) (postG dst w j)
      (List.mem_append_left _ (by
        simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
        exact ⟨8 * w + j, by omega_arith, rfl, by
          rw [show (8 * w + j) / 8 = w by omega_arith, show (8 * w + j) % 8 = j by omega_arith]⟩)) p hp
    rw [half, slotW, b₅', this, postG, xorBits_cons, bitOf_word _ _ _ hp,
      show 16 + (dst - d1Slot) + 8 * w + j = 16 + (dst - d1Slot + 8 * w + j) by omega_arith,
      hW₅ _ (by omega_arith), show d1Slot + (dst - d1Slot + 8 * w + j) = dst + (8 * w + j) by omega_arith,
      xorBits_sel W₅ (fun j => slotW s₃ (ylSlot + j)) (slotW s₄) (fun i hi => by simp [W₅, hi])
        (fun j hj => by
          simp only [W₅, show ¬ 8 + j < 8 by omega_arith, ↓reduceIte, show 8 + j - 8 = j by omega_arith]
          exact above₄ _ (by simp [ylSlot]) (by simp [ylSlot, tailSlot]; omega_arith))
        hj (by omega_arith) _ fun c hc => pRow_lt hc]
    rfl
  have hD := W32.round_rel hQ hK hR hXL sx₂ (fun j hj p hp => hYL j hj p hp) hXR sx₄ hR'
  refine ⟨s₅, ?_, hD, fun i hi => ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁],
    fun r hr => ?_, ?_⟩
  · rw [round, runBlock_app, runBlock_app, runBlock_app, runBlock_app, h₁, Option.bind_some, h₂,
      Option.bind_some, h₃, Option.bind_some, h₄, Option.bind_some, h₅]
  · have hk : keepOut (other dst + i) (16 + (other dst - d1Slot) + i) ∈ postOuts dst :=
      List.mem_append_right _ (by simp only [List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
    have hv := keep_word (W := W₅) (i := 16 + (other dst - d1Slot) + i) (v := slotW s (src + i)) ?_ (y₅ _ _ hk)
    · rw [hother] at hv; rw [slotW, b₅', hv]
    · rw [hother, show 16 + (src - d1Slot) + i = 16 + (src - d1Slot + i) by omega_arith, hW₅ _ (by omega_arith),
        show d1Slot + (src - d1Slot + i) = src + i by omega_arith]
  · rw [o₅ r (hall' r hr).2.2, o₄ r hr, o₃ r (hall' r hr).2.1, o₂ r hr, o₁ r (hall' r hr).1]
  · have sbs : ∀ {t : State}, t.gpr sb = s.gpr sb → ∀ r ∈ [slotRegion sboxCfg t],
        ∃ r' ∈ [slotRegion layerCfg s], Region.Sub r r' := fun ht r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by
        simp only [slotRegion, sboxCfg, layerCfg, ht]; exact Region.sub_prefix (by decide)⟩
    have e₂ : slotRegion layerCfg s₂ = slotRegion layerCfg s := by simp only [slotRegion, layerCfg, b₂]
    have e₄ : slotRegion linCfg s₄ = slotRegion layerCfg s := by simp only [slotRegion, linCfg, layerCfg, b₄]
    have g₂ : Frame [slotRegion layerCfg s] s₁.mem s₂.mem := f₂.sub (sbs b₁)
    have g₃ : Frame [slotRegion layerCfg s] s₂.mem s₃.mem := by rw [← e₂]; exact f₃
    have g₄ : Frame [slotRegion layerCfg s] s₃.mem s₄.mem := f₄.sub (sbs b₃)
    have g₅ : Frame [slotRegion layerCfg s] s₄.mem s₅.mem := by rw [← e₄]; exact f₅
    exact f₁.trans (g₂.trans (g₃.trans (g₄.trans g₅)))

end VG.Proof.Camellia.X86
