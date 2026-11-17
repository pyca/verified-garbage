module

public import VerifiedGarbage.Impl.Camellia.Arm.Sbox
public import VerifiedGarbage.Proof.Camellia.SboxTable
public import VerifiedGarbage.Proof.Framework.Arm.Straight
public import VerifiedGarbage.Proof.Camellia.Bitsliced32
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Camellia.Bitsliced
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Camellia.Arm.Ecb
public import VerifiedGarbage.Proof.Sm4.Arm.LinG
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Camellia.Arm.Linear`, which this module and modules that import it used -/

section

/-!
# The linear layers of bitsliced Camellia on ARMv7, by evaluation

Each linear block is checked by evaluation over the lane domain
(`Framework/Arm/Linear.lean`, with words in slots: `Sm4/Arm/LinG.lean`):
the kernel runs it on its input words as atoms and compares every output
bit with the XOR of input bits given here, bit `t` of input word `i`
being `32 i + t`.

* A round's left word (`preL`): the source half's planes (slots `src …`)
  are input words `0 … 15`, the subkeys' planes at `kp` words `16 …`.
* The middle (`midLR`): the left word's S-box output in the state
  registers is words `0 … 7`, the source half's planes `8 … 23`, the
  subkeys' planes at `kp` words `24 …`.
* The end (`postP`): the right word's S-box output in the state registers
  is words `0 … 7`, the left word's selected output (slots 32–39) words
  `8 … 15`, the halves' planes (slots 40–71) words `16 … 47`.
* The whitening: the halves' planes are words `0 … 31`, the two entries
  at `kp` words `32 … 63`.
* The transposes (`toBsWord`, `fromBsWord`): the tail buffer's eight
  blocks (slots 632–663) are words `0 … 31`; the halves' planes are.

Position `p = 8 i + b` of a plane of word `w` is byte `4 w + i` of the half
of block `b`.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Bitslice VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Arm.Straight (inWord outWord bitOf xorBits assign)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp)
open VG.Proof.Sm4.Arm (linEnvG linPostG linG_ok)
open VG.Proof.Camellia (pRow)


/-- The registers `q 0 … q 7` hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

/-! ## A round -/

/-- The slots below the table; the two entries' 32 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := keySlot, ext := kp, exts := 32 }

/-- The slots below the table, without the subkeys. -/
def linCfg : Cfg := { base := sb, slots := keySlot, ext := kp, exts := 0 }

/-- The half at slot `src`, from input word `x`. -/
def halfIns (src x : Nat) : List (Nat × Nat) := (List.range 16).map fun k => (src + k, x + k)

/-- The halves' slots. -/
def halvesSlots : List Nat := (List.range 32).map (d1Slot + ·)

/-- Both halves (slots 40–71), from input word `x`. -/
def halvesIns (x : Nat) : List (Nat × Nat) := halfIns d1Slot x ++ halfIns d2Slot (x + 16)

def preEnv : Env (Nat × Nat) := linEnvG [] (halvesIns 0) []

/-- The left word's S-box input: plane `j` at `p` is the selected plane of
the source half (at slot `src`) XOR the subkey's, at word `off` of `kp`. -/
def preG (off src j p : Nat) : List Nat :=
  [32 * (src - d1Slot + W32.inSrc (p / 8) j) + p, 32 * (32 + off + W32.inSrc (p / 8) j) + p]

theorem preL0_check :
    check (lanes 32 11) layerCfg (linExt 32) (preL 0 d1Slot) preEnv
      (linPostG 11 (qOuts (preG 0 d1Slot)) [] halvesSlots preEnv) = true := by
  decide +kernel

theorem preL16_check :
    check (lanes 32 11) layerCfg (linExt 32) (preL 16 d2Slot) preEnv
      (linPostG 11 (qOuts (preG 16 d2Slot)) [] halvesSlots preEnv) = true := by
  decide +kernel

def midEnv : Env (Nat × Nat) := linEnvG qIns (halvesIns 8) []

/-- The left word's selected output, to slot `32 + j`. -/
def ylG (j p : Nat) : List Nat := [32 * W32.outSrc (p / 8) j + p]

/-- The right word's S-box input. -/
def midG (off src j p : Nat) : List Nat :=
  [32 * (16 + (src - d1Slot) + W32.inSrc (4 + p / 8) j) + p,
   32 * (48 + off + W32.inSrc (4 + p / 8) j) + p]

def ylOuts : List (Nat × (Nat → List Nat)) := (List.range 8).map fun j => (ylSlot + j, ylG j)

theorem mid0_check :
    check (lanes 32 12) layerCfg (linExt 40) (midLR 0 d1Slot) midEnv
      (linPostG 12 (qOuts (midG 0 d1Slot)) ylOuts halvesSlots midEnv) = true := by
  decide +kernel

theorem mid16_check :
    check (lanes 32 12) layerCfg (linExt 40) (midLR 16 d2Slot) midEnv
      (linPostG 12 (qOuts (midG 16 d2Slot)) ylOuts halvesSlots midEnv) = true := by
  decide +kernel

/-- The left word's output (slots 32–39) and both halves (slots 40–71). -/
def postIns : List (Nat × Nat) := (List.range 40).map fun k => (ylSlot + k, 8 + k)

def postEnv : Env (Nat × Nat) := linEnvG qIns postIns []

/-- The selected S-box output of byte `c` of plane `j` at position `b`. -/
def selG (j b c : Nat) : Nat :=
  if c < 4 then 32 * (8 + j) + 8 * c + b else 32 * W32.outSrc c j + 8 * (c - 4) + b

/-- Plane `8 w + j` of the half at slot `dst`, XOR the P-function of the
selected outputs. -/
def postG (dst w j p : Nat) : List Nat :=
  (32 * (16 + (dst - d1Slot) + 8 * w + j) + p) :: (pRow (4 * w + p / 8)).map (selG j (p % 8))

def postOuts (dst : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 16).map fun k => (dst + k, postG dst (k / 8) (k % 8))

/-- The slots of the other half. -/
def otherSlots (dst : Nat) : List Nat :=
  (List.range 16).map ((if dst = d1Slot then d2Slot else d1Slot) + ·)

theorem post2_check :
    check (lanes 32 11) linCfg (linExt 48) (postP d2Slot) postEnv
      (linPostG 11 [] (postOuts d2Slot) (otherSlots d2Slot) postEnv) = true := by
  decide +kernel

theorem post1_check :
    check (lanes 32 11) linCfg (linExt 48) (postP d1Slot) postEnv
      (linPostG 11 [] (postOuts d1Slot) (otherSlots d1Slot) postEnv) = true := by
  decide +kernel

/-! ## The whitening -/

def whitenEnv : Env (Nat × Nat) := linEnvG [] (halvesIns 0) []

/-- Plane `i` of the halves (`D1`'s, then `D2`'s), XOR word `i` (or, with
`swap`, word `(i + 16) % 32`) of the entries at `kp`. -/
def whitenG (swap : Bool) (i p : Nat) : List Nat :=
  [32 * i + p, 32 * (32 + (if swap then (i + 16) % 32 else i)) + p]

def whitenOuts (swap : Bool) : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun i => (d1Slot + i, whitenG swap i)

theorem whiten0_check :
    check (lanes 32 11) layerCfg (linExt 32) (whiten false) whitenEnv
      (linPostG 11 [] (whitenOuts false) [] whitenEnv) = true := by
  decide +kernel

theorem whiten1_check :
    check (lanes 32 11) layerCfg (linExt 32) (whiten true) whitenEnv
      (linPostG 11 [] (whitenOuts true) [] whitenEnv) = true := by
  decide +kernel

/-! ## The transposes -/

/-- The working space at `sb`, and the tail buffer's 32 words at `r12`. -/
def toBsCfg : Cfg := { base := sb, slots := keySlot, ext := u7, exts := 32 }

def toBsEnv : Env (Nat × Nat) := linEnvG [] [] []

/-- Plane `j` of the state's word `w`, at `p = 8 i + b`: bit `j` of byte `i`
of word `w` of block `b` (the tail buffer's word `4 b + w`). -/
def toBsG (w j p : Nat) : List Nat := [32 * (4 * (p % 8) + w) + 8 * (p / 8) + j]

def toBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => (d1Slot + k, toBsG (k / 8) (k % 8))

theorem toBs_check :
    check (lanes 32 10) toBsCfg (linExt 0) ((List.range 4).flatMap toBsWord) toBsEnv
      (linPostG 10 [] toBsOuts [] toBsEnv) = true := by
  decide +kernel

/-- The working space at `sb`, up to the end of the tail buffer, whose
words the transpose stores. -/
def fromBsCfg : Cfg := { base := sb, slots := tailSlot + 32, ext := sb, exts := 0 }

/-- The halves' planes, input words `d1Slot … d1Slot + 31`. -/
def fromBsIns : List (Nat × Nat) := (List.range 32).map fun k => (d1Slot + k, d1Slot + k)

def fromBsEnv : Env (Nat × Nat) := linEnvG [] fromBsIns []

/-- Bit `8 i + j` of the tail buffer's word `t = 4 b + w`, byte `i` (from the
most significant) of word `w` of block `b`: plane `j` of the state's word
`(w + 2) % 4` at `8 i + b` (the working space's word `40 + 8 ((w + 2) % 4) + j`). -/
def fromBsG (t k : Nat) : List Nat := [32 * (d1Slot + 8 * ((t % 4 + 2) % 4) + k % 8) + 8 * (k / 8) + t / 4]

def fromBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun t => (tailSlot + t, fromBsG t)

theorem fromBs_check :
    check (lanes 32 12) fromBsCfg (linExt 0) ((List.range 4).flatMap fromBsWord) fromBsEnv
      (linPostG 12 [] fromBsOuts [] fromBsEnv) = true := by
  decide +kernel

/-! ## The subkeys' planes -/

/-- The entry at `kp`. -/
def entryCfg : Cfg := { base := kp, slots := 16, ext := kp, exts := 0 }

/-- The word in `q 4` is input word 0, the entry's words `1 … 16`. -/
def keyEnv : Env (Nat × Nat) := linEnvG [(q 4, 0)] ((List.range 16).map fun k => (k, 1 + k)) []

/-- Plane `j` of a subkey's word: bit `8 i + b` is bit `8 i + j` of the word
in `q 4`. -/
def keyBsG (j p : Nat) : List Nat := [8 * (p / 8) + j]

def keyOuts (w : Nat) : List (Nat × (Nat → List Nat)) := (List.range 8).map fun j => (8 * w + j, keyBsG j)

/-- The other word's planes. -/
def keyKeep (w : Nat) : List Nat := (List.range 8).map fun j => 8 * (1 - w) + j

theorem keyPlanes0_check :
    check (lanes 32 10) entryCfg (linExt 0) (keyPlanes 0) keyEnv
      (linPostG 10 [] (keyOuts 0) (keyKeep 0) keyEnv) = true := by
  decide +kernel

theorem keyPlanes1_check :
    check (lanes 32 10) entryCfg (linExt 0) (keyPlanes 1) keyEnv
      (linPostG 10 [] (keyOuts 1) (keyKeep 1) keyEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.Arm

end

end

/-! ### `Camellia.Arm.Sbox`, which only this module used -/

section

/-!
# The bitsliced Camellia S-box on ARMv7

As on the 64-bit targets: `sboxCode` only combines words bitwise (and
builds all ones with `mov` and `sub`), so the kernel evaluates it once on
truth tables of the 256 inputs (`Bitslice.table`) and compares the result
with the specification's `SBOX1`. `sbox_ok` then gives, at every bit
position `p`, `SBOX1` of the byte formed by bit `p` of the eight words.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm VG.Impl.Camellia.Arm
open VG.Proof.Camellia
open VG.Proof.Camellia.W32 (bsByte getLsbD_bsByte)

/-- The S-box's memory: its spill slots, at `r8`. -/
def sboxCfg : Cfg := { base := sb, slots := 32, ext := sb, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some (sbox1T j)

theorem sbox_check :
    check (table 32 256) sboxCfg (fun _ => none) Impl.Camellia.Arm.sboxCode sboxEnv sboxPost = true := by
  lit_decide

/-- The registers the layers may write: the state, the S-box's temporaries
and all ones, and the linear layers' temporaries. -/
def layerWrites : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r10, .r11, .r12, .lr]

/-- The registers outside `layerWrites`. -/
def layerKeep : List Reg := [.r8, .r9]

theorem not_layerWrites (r : Reg) (hr : r ∉ layerWrites) : r ∈ layerKeep := by
  revert hr; cases r <;> decide

/-- A block that writes none of `layerKeep` writes only `layerWrites`. -/
theorem writes_rest {is : List Instr}
    (h : layerKeep.all (fun r => is.all fun i => !clobbers i r) = true)
    (r : Reg) (hr : r ∉ layerWrites) : (is.all fun i => !clobbers i r) = true :=
  List.all_eq_true.mp h r (not_layerWrites r hr)

/-- `SBOX1`, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa Impl.Camellia.Arm.sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32,
        (s'.gpr (q j)).getLsbD p = (Spec.Camellia.sbox1 (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  obtain hout : ∀ j < 8, e'.reg (q j) = some (sbox1T j) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  obtain key : ∀ p < 32, ∃ s', runBlock isa Impl.Camellia.Arm.sboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (Impl.Camellia.Arm.sboxCode.all fun i => !clobbers i r) = false) := by
    intro p hp
    obtain hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    obtain hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_using [])
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    obtain hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, testBit_sbox1T hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp [writes_rest (is := Impl.Camellia.Arm.sboxCode) (by decide +kernel) r hr]

end VG.Proof.Camellia.Arm

end

end


/-!
# A round of bitsliced Camellia on ARMv7

`round_ok`: with the half `D1` (or `D2`) in its slots, the other half in
its slots and the subkey's planes at `kp`, `round off src dst` leaves
`d2 ^ F(d1, k)` in the other half's slots, keeping the first half's and
writing only the slots below the table. The layers are composed from their
checks (`Linear.lean`, `Sbox.lean`) and `W32.round_rel`.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Bitslice (lanes)
open VG.Impl.Aes.Arm (q sb t0 t1 kp)
open VG.Proof.Sm4.Arm (linG_ok linPostG)
open VG.Proof.Camellia (pRow pRow_lt)

/-- The planes in the state registers. -/
abbrev Qs (s : State) (i : Nat) : BitVec 32 := s.gpr (q i)

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr sb) k) 32

/-- Word `k` of the table entries at `kp`. -/
abbrev keyW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr kp) k) 32

/-- The sixteen planes of the half at slot `d`. -/
def half (s : State) (d : Nat) : Nat → BitVec 32 := fun i => slotW s (d + i)

theorem ok_sbox {s : State} (h : Ok layerCfg s) : Ok sboxCfg s where
  slotIn k hk := h.slotIn k (by simp [sboxCfg, layerCfg, keySlot] at hk ⊢; omega_using [hk])
  extIn k hk := by simp [sboxCfg] at hk
  slots := by have := h.slots; simp [sboxCfg, layerCfg, keySlot] at this ⊢; omega_using [this]
  sep k _ j hj := by simp [sboxCfg] at hj

theorem ok_lin {s : State} (h : Ok layerCfg s) : Ok linCfg s where
  slotIn k hk := h.slotIn k (by simpa [linCfg, layerCfg] using hk)
  extIn k hk := by simp [linCfg] at hk
  slots := by have := h.slots; simpa [linCfg, layerCfg] using this
  sep k _ j hj := by simp [linCfg] at hj

/-- A frame of the first `n` slots keeps slot `k ≥ n`. -/
theorem slot_above {m m' : Mem} {b : BitVec 32} {n k : Nat} (hf : Frame [⟨State.addr b, 4 * n⟩] m m') (hk : n ≤ k)
    (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) : m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  obtain e : wordAddr b k = State.addr b + BitVec.ofNat 64 (4 * k) := addr_add (by omega_using [hfit])
  have := b.isLt
  obtain hb : (State.addr b).toNat = b.toNat := by simp [State.addr]; omega_using []
  rw [e]
  exact hf.readW (r := ⟨State.addr b + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base _ (by omega_using [hk]) (by omega_using [hfit])) (by decide)

/-- A frame of the slots keeps the external words. -/
theorem frame_ext {c : Cfg} {s : State} {m' : Mem} (hok : Ok c s) (hf : Frame [slotRegion c s] s.mem m')
    {j : Nat} (hj : j < c.exts) :
    m'.readW (wordAddr (s.gpr c.ext) j) 32 = s.mem.readW (wordAddr (s.gpr c.ext) j) 32 := by
  simp only [Mem.readW]
  congr 1
  refine Mem.read_congr fun i hi => hf _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  have hfit := hok.slots
  simp only [slotRegion, Region.Contains] at hc
  obtain hb := toNat_addr (s.gpr c.base)
  obtain hk : (wordAddr (s.gpr c.ext) j + BitVec.ofNat 64 i - State.addr (s.gpr c.base)).toNat / 4 < c.slots := by
    omega_using [hc]
  obtain hsep := hok.sep _ hk j hj (wordAddr (s.gpr c.ext) j + BitVec.ofNat 64 i)
  obtain e1 := wordAddr_toNat (s.gpr c.base)
    (k := (wordAddr (s.gpr c.ext) j + BitVec.ofNat 64 i - State.addr (s.gpr c.base)).toNat / 4) (by omega_using [hc, hfit])
  obtain hi' : i < 4 := by simpa using hi
  generalize wordAddr (s.gpr c.base) _ = W at hsep e1
  generalize wordAddr (s.gpr c.ext) j = A at *
  generalize State.addr (s.gpr c.base) = B at *
  obtain hx : (A + BitVec.ofNat 64 i - A).toNat < 4 := by
    rw [Mem.sub_ofNat_toNat A (by omega_using [hi])]; exact hi'
  refine hsep ?_ hx
  obtain hBl : B.toNat < 2 ^ 32 := by omega_using [hb]
  bv_omega

theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

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
  simp only [halvesIns, halfIns, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq] at h
  rcases h with ⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩
  · exact ⟨k, by omega_using [hk], rfl, rfl⟩
  · exact ⟨16 + k, by omega_using [hk], by simp [d1Slot, d2Slot]; omega_using [], by omega_using []⟩

theorem mem_halvesSlots {k : Nat} (hk : k < 32) : d1Slot + k ∈ halvesSlots := by
  simp only [halvesSlots, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩

/-- A round, with the subkey at word `off` of `kp`. -/
theorem round_ok {off src dst : Nat}
    (hA : check (lanes 32 11) layerCfg (linExt 32) (preL off src) preEnv
      (linPostG 11 (qOuts (preG off src)) [] halvesSlots preEnv) = true)
    (hC : check (lanes 32 12) layerCfg (linExt 40) (midLR off src) midEnv
      (linPostG 12 (qOuts (midG off src)) ylOuts halvesSlots midEnv) = true)
    (hE : check (lanes 32 11) linCfg (linExt 48) (postP dst) postEnv
      (linPostG 11 [] (postOuts dst) (otherSlots dst) postEnv) = true)
    (hall : (layerKeep.all fun r =>
      (preL off src ++ midLR off src ++ postP dst).all fun i => !clobbers i r) = true)
    (hcase : RoundCase off src dst)
    {s : State} (hok : Ok layerCfg s) {d1 d2 : Nat → BitVec 64} {k : BitVec 64}
    (hQ : W32.HalfRel (half s src) d1) (hK : W32.HalfRel (fun i => keyW s (off + i)) fun _ => k)
    (hR : W32.HalfRel (half s dst) d2) :
    ∃ s', runBlock isa (round off src dst) s = some s' ∧
      W32.HalfRel (half s' dst) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) ∧
      (∀ i < 16, slotW s' (src + i) = slotW s (src + i)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  obtain hall' : ∀ r, r ∉ layerWrites → ((preL off src).all fun i => !clobbers i r) = true ∧
      ((midLR off src).all fun i => !clobbers i r) = true ∧
      ((postP dst).all fun i => !clobbers i r) = true := fun r hr => by
    have := List.all_eq_true.mp hall r (not_layerWrites r hr)
    simp only [List.all_append, Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  obtain hsb : sb ∉ layerWrites := by decide
  obtain hkp : kp ∉ layerWrites := by decide
  have hfit := hok.slots
  simp only [layerCfg, keySlot] at hfit
  have hd1 : d1Slot = 40 := rfl
  have hks : keySlot = 72 := rfl
  have hyl : ylSlot = 32 := rfl
  obtain hsd : (src = d1Slot ∧ dst = d2Slot) ∨ (src = d2Slot ∧ dst = d1Slot) := by
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  obtain hsrc : d1Slot ≤ src ∧ src + 16 ≤ d1Slot + 32 := by
    rcases hsd with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [d1Slot, d2Slot]
  obtain hdst : d1Slot ≤ dst ∧ dst + 16 ≤ d1Slot + 32 := by
    rcases hsd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [d1Slot, d2Slot]
  obtain hoff : off + 16 ≤ 32 := by rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  -- The left word's S-box input.
  let W₁ : Nat → BitVec 32 := fun i => if i < 32 then slotW s (d1Slot + i) else keyW s (i - 32)
  obtain ⟨s₁, h₁, x₁, -, k₁, rd₁, wr₁, sp₁, o₁, f₁, -, -⟩ := linG_ok hA hok W₁
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := halvesIns_mem hji
      exact ⟨by simp only [layerCfg, keySlot, d1Slot]; omega_arith, by omega_arith, by simp [W₁, hk]; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₁, show ¬ 32 + j < 32 by omega_arith]; rfl⟩)
  obtain b₁ : s₁.gpr sb = s.gpr sb := o₁ _ (hall' sb hsb).1
  obtain kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (hall' kp hkp).1
  obtain hXL : ∀ j < 8, ∀ p < 32, (Qs s₁ j).getLsbD p =
      ((half s src (W32.inSrc (p / 8) j)).getLsbD p ^^ (keyW s (off + W32.inSrc (p / 8) j)).getLsbD p) := by
    intro j hj p hp
    obtain hi := W32.inSrc_lt (c := p / 8) hj
    rw [x₁ (q j) (preG off src j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
      preG, xorBits_cons, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, Bool.xor_false]
    simp only [W₁, half, show src - d1Slot + W32.inSrc (p / 8) j < 32 by omega_arith, ↓reduceIte,
      show ¬ 32 + off + W32.inSrc (p / 8) j < 32 by omega_arith,
      show 32 + off + W32.inSrc (p / 8) j - 32 = off + W32.inSrc (p / 8) j by omega_arith,
      show d1Slot + (src - d1Slot + W32.inSrc (p / 8) j) = src + W32.inSrc (p / 8) j by omega_arith]
  obtain hok₁ : Ok layerCfg s₁ := hok.congr b₁ kp₁ rd₁ wr₁
  obtain keep₁ : ∀ i < 32, slotW s₁ (d1Slot + i) = slotW s (d1Slot + i) := fun i hi => by
    have := k₁ (d1Slot + i) (mem_halvesSlots hi) (by simp only [layerCfg, keySlot, d1Slot]; omega_arith)
    simp only [layerCfg] at this
    rw [slotW, b₁, this]
  obtain kw₁ : ∀ j < 32, keyW s₁ j = keyW s j := fun j hj => by
    simp only [keyW, kp₁]; exact frame_ext hok f₁ (by simpa [layerCfg] using hj)
  -- The left word's S-box.
  obtain ⟨s₂, h₂, sx₂, rd₂, wr₂, sp₂, o₂, f₂⟩ := sbox_ok (ok_sbox hok₁)
  obtain b₂ : s₂.gpr sb = s.gpr sb := (o₂ sb hsb).trans b₁
  obtain kp₂ : s₂.gpr kp = s.gpr kp := (o₂ kp hkp).trans kp₁
  obtain hok₂ : Ok layerCfg s₂ := hok₁.congr (o₂ sb hsb) (o₂ kp hkp) rd₂ wr₂
  obtain above₂ : ∀ k, 32 ≤ k → k < keySlot → slotW s₂ k = slotW s₁ k := fun k h1 h2 => by
    simp only [slotW, o₂ sb hsb]
    refine slot_above (n := 32) (by simpa [slotRegion, sboxCfg] using f₂) h1 ?_
    rw [b₁]; simp [keySlot] at h2; omega_arith
  obtain sub₂ : ∀ {t : State}, Ok layerCfg t → Frame [slotRegion sboxCfg t] t.mem s₂.mem →
      Frame [slotRegion layerCfg t] t.mem s₂.mem := fun _ f => f.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by
      simp only [slotRegion, sboxCfg, layerCfg]; exact Region.sub_prefix (by simp [keySlot])⟩
  obtain kw₂ : ∀ j < 32, keyW s₂ j = keyW s j := fun j hj => by
    rw [← kw₁ j hj]; simp only [keyW, o₂ kp hkp]
    exact frame_ext hok₁ (sub₂ hok₁ f₂) (by simpa [layerCfg] using hj)
  obtain keep₂ : ∀ i < 32, slotW s₂ (d1Slot + i) = slotW s (d1Slot + i) := fun i hi => by
    rw [above₂ _ (by omega_arith) (by omega_arith), keep₁ i hi]
  -- The left word's output selection, and the right word's S-box input.
  let W₃ : Nat → BitVec 32 := fun i =>
    if i < 8 then Qs s₂ i else if i < 40 then slotW s₂ (d1Slot + (i - 8)) else keyW s₂ (i - 40)
  obtain ⟨s₃, h₃, x₃, y₃, k₃, rd₃, wr₃, sp₃, o₃, f₃, -, -⟩ := linG_ok hC hok₂ W₃
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, by simp [W₃, hi]⟩)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := halvesIns_mem hji
      exact ⟨by simp only [layerCfg, keySlot, d1Slot]; omega_arith, by omega_arith, by
        simp [W₃, show ¬ 8 + k < 8 by omega_arith, show 8 + k < 40 by omega_arith]; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₃, show ¬ 40 + j < 8 by omega_arith, show ¬ 40 + j < 40 by omega_arith]; rfl⟩)
  obtain b₃' : s₃.gpr sb = s₂.gpr sb := o₃ _ (hall' sb hsb).2.1
  obtain b₃ : s₃.gpr sb = s.gpr sb := b₃'.trans b₂
  obtain kp₃ : s₃.gpr kp = s.gpr kp := (o₃ _ (hall' kp hkp).2.1).trans kp₂
  obtain hYL : ∀ j < 8, ∀ p < 32, (slotW s₃ (ylSlot + j)).getLsbD p = (Qs s₂ (W32.outSrc (p / 8) j)).getLsbD p := by
    intro j hj p hp
    have := y₃ (ylSlot + j) (ylG j) (by simp only [ylOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      (by simp [layerCfg, ylSlot, keySlot]; omega_arith) p hp
    simp only [layerCfg] at this
    rw [slotW, b₃, ← b₂, this, ylG, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp, Bool.xor_false]
    simp only [W₃, W32.outSrc_lt hj, ↓reduceIte]
  obtain hXR : ∀ j < 8, ∀ p < 32, (Qs s₃ j).getLsbD p =
      ((half s src (8 + W32.inSrc (4 + p / 8) j)).getLsbD p ^^
        (keyW s (off + (8 + W32.inSrc (4 + p / 8) j))).getLsbD p) := by
    intro j hj p hp
    obtain hi := W32.inSrc_lt (c := 4 + p / 8) hj
    rw [x₃ (q j) (midG off src j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
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
  obtain hok₃ : Ok layerCfg s₃ := hok₂.congr (o₃ _ (hall' sb hsb).2.1) (o₃ _ (hall' kp hkp).2.1) rd₃ wr₃
  obtain keep₃ : ∀ i < 32, slotW s₃ (d1Slot + i) = slotW s (d1Slot + i) := fun i hi => by
    have := k₃ (d1Slot + i) (mem_halvesSlots hi) (by simp only [layerCfg, keySlot, d1Slot]; omega_arith)
    simp only [layerCfg] at this
    rw [slotW, b₃', this]; exact keep₂ i hi
  -- The right word's S-box.
  obtain ⟨s₄, h₄, sx₄, rd₄, wr₄, sp₄, o₄, f₄⟩ := sbox_ok (ok_sbox hok₃)
  obtain b₄ : s₄.gpr sb = s.gpr sb := (o₄ sb hsb).trans b₃
  obtain hok₄ : Ok layerCfg s₄ := hok₃.congr (o₄ sb hsb) (o₄ kp hkp) rd₄ wr₄
  obtain above₄ : ∀ k, 32 ≤ k → k < keySlot → slotW s₄ k = slotW s₃ k := fun k h1 h2 => by
    simp only [slotW, o₄ sb hsb]
    refine slot_above (n := 32) (by simpa [slotRegion, sboxCfg] using f₄) h1 ?_
    rw [b₃]; simp [keySlot] at h2; omega_arith
  -- The right word's output selection, the P-function and the XOR.
  let W₅ : Nat → BitVec 32 := fun i => if i < 8 then Qs s₄ i else slotW s₄ (ylSlot + (i - 8))
  obtain ⟨s₅, h₅, -, y₅, k₅, rd₅, wr₅, sp₅, o₅, f₅, -, -⟩ := linG_ok hE (ok_lin hok₄) W₅
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, by simp [W₅, hi]⟩)
    (fun j i hji => by
      simp only [postIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [linCfg, keySlot, ylSlot]; omega_arith, by omega_arith, by
        simp [W₅, show ¬ 8 + k < 8 by omega_arith]; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [linCfg] at hj)
  obtain b₅' : s₅.gpr sb = s₄.gpr sb := o₅ _ (hall' sb hsb).2.2
  obtain b₅ : s₅.gpr sb = s.gpr sb := b₅'.trans b₄
  obtain hW₅ : ∀ i < 32, W₅ (16 + i) = slotW s (d1Slot + i) := fun i hi => by
    simp only [W₅, show ¬ 16 + i < 8 by omega_arith, ↓reduceIte, show ylSlot + (16 + i - 8) = d1Slot + i by
      simp [ylSlot, d1Slot]; omega_arith]
    rw [above₄ _ (by omega_arith) (by omega_arith), keep₃ i hi]
  obtain hR' : ∀ w < 2, ∀ j < 8, ∀ p < 32, (half s₅ dst (8 * w + j)).getLsbD p =
      ((half s dst (8 * w + j)).getLsbD p ^^
        W32.rowSel (fun j => slotW s₃ (ylSlot + j)) (Qs s₄) j (p % 8) (pRow (4 * w + p / 8))) := by
    intro w hw j hj p hp
    have := y₅ (dst + (8 * w + j)) (postG dst w j)
      (by
        simp only [postOuts, List.mem_map, List.mem_range, Prod.mk.injEq]
        exact ⟨8 * w + j, by omega_arith, rfl, by
          rw [show (8 * w + j) / 8 = w by omega_arith, show (8 * w + j) % 8 = j by omega_arith]⟩)
      (by simp [linCfg, keySlot]; omega_arith) p hp
    simp only [linCfg] at this
    rw [half, slotW, b₅', this, postG, xorBits_cons, bitOf_word _ _ _ hp,
      show 16 + (dst - d1Slot) + 8 * w + j = 16 + (dst - d1Slot + 8 * w + j) by omega_arith,
      hW₅ _ (by omega_arith), show d1Slot + (dst - d1Slot + 8 * w + j) = dst + (8 * w + j) by omega_arith,
      xorBits_sel W₅ (fun j => slotW s₃ (ylSlot + j)) (Qs s₄) (fun i hi => by simp [W₅, hi])
        (fun j hj => by
          simp only [W₅, show ¬ 8 + j < 8 by omega_arith, ↓reduceIte, show 8 + j - 8 = j by omega_arith]
          exact above₄ _ (by simp [ylSlot]) (by simp [ylSlot, keySlot]; omega_arith))
        hj (by omega_arith) _ fun c hc => pRow_lt hc]
    rfl
  obtain hD := W32.round_rel hQ hK hR hXL sx₂ (fun j hj p hp => hYL j hj p hp) hXR sx₄ hR'
  refine ⟨s₅, ?_, hD, fun i hi => ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁],
    by rw [sp₅, sp₄, sp₃, sp₂, sp₁], fun r hr => ?_, ?_⟩
  · rw [round, runBlock_app, runBlock_app, runBlock_app, runBlock_app, h₁, Option.bind_some, h₂,
      Option.bind_some, h₃, Option.bind_some, h₄, Option.bind_some, h₅]
  · have hk : src + i ∈ otherSlots dst := by
      simp only [otherSlots, List.mem_map, List.mem_range]
      refine ⟨i, hi, ?_⟩
      rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [d1Slot, d2Slot]
    have := k₅ (src + i) hk (by simp [linCfg, keySlot]; omega_arith)
    simp only [linCfg] at this
    rw [slotW, b₅', this, show src + i = d1Slot + (src - d1Slot + i) by omega_arith]
    exact (above₄ _ (by omega_arith) (by omega_arith)).trans (keep₃ _ (by omega_arith))
  · rw [o₅ r (hall' r hr).2.2, o₄ r hr, o₃ r (hall' r hr).2.1, o₂ r hr, o₁ r (hall' r hr).1]
  · have sbs : ∀ {t : State}, t.gpr sb = s.gpr sb → ∀ r ∈ [slotRegion sboxCfg t],
        ∃ r' ∈ [slotRegion layerCfg s], Region.Sub r r' := fun ht r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by
        simp only [slotRegion, sboxCfg, layerCfg, ht]; exact Region.sub_prefix (by decide)⟩
    obtain e₁ : slotRegion layerCfg s₁ = slotRegion layerCfg s := by simp only [slotRegion, layerCfg, b₁]
    obtain e₂ : slotRegion layerCfg s₂ = slotRegion layerCfg s := by simp only [slotRegion, layerCfg, b₂]
    obtain e₄ : slotRegion linCfg s₄ = slotRegion layerCfg s := by simp only [slotRegion, linCfg, layerCfg, b₄]
    obtain g₂ : Frame [slotRegion layerCfg s] s₁.mem s₂.mem := f₂.sub (sbs b₁)
    obtain g₃ : Frame [slotRegion layerCfg s] s₂.mem s₃.mem := by rw [← e₂]; exact f₃
    obtain g₄ : Frame [slotRegion layerCfg s] s₃.mem s₄.mem := f₄.sub (sbs b₃)
    obtain g₅ : Frame [slotRegion layerCfg s] s₄.mem s₅.mem := by rw [← e₄]; exact f₅
    exact f₁.trans (g₂.trans (g₃.trans (g₄.trans g₅)))

end VG.Proof.Camellia.Arm
