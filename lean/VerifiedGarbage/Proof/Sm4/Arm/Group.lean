module

public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Impl.Sm4.Arm.Ecb
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Arm.Straight
public import VerifiedGarbage.Impl.Sm4.Arm.Layers
public import VerifiedGarbage.Proof.Sm4.Bitsliced32
public import VerifiedGarbage.Proof.Sm4.Arm.LinG
public import VerifiedGarbage.Impl.Sm4.Arm.Sbox
public import VerifiedGarbage.Proof.Sm4.Rounds

/-! ### `Sm4.Arm.Prologue`, which this module and modules that import it used -/

section

/-! ### `Sm4.Arm.Core`, which this module and modules that import it used -/

section

/-! ### `Sm4.Arm.Round`, which only this module used -/

section

/-! ### `Sm4.Arm.Linear`, which only this module used -/

section

/-!
# The linear layers of bitsliced SM4 on ARMv7, by evaluation

As on x86-64 (`Proof/Sm4/X86_64/Linear.lean`), on 32-bit words: each
linear block is checked by evaluation over the lane domain, the kernel
running it on its input words as atoms and comparing every output bit
with the XOR of input bits given here.

* A round's input (`preX`): the state's planes (slots 32–63) are input
  words `0 … 31`, the round keys' planes at `kp` words `32 …`.
* A round's linear layer (`lin`): the S-box's output in the state
  registers is input words `0 … 7`, the state's planes words `8 … 39`.
* The transposes (`toBs`, `fromBs`): the tail buffer's eight blocks
  (slots 64–95) are input words `0 … 31`; the state's planes are.
* A round key's planes (`keyPlanes`): its word, byte-reversed, in `q 0` is
  input word `0`; the planes are the entry at `kp`.

Position `p = 8 i + b` of a plane is byte `i` (from the most significant)
of the word of block `b`.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Bitslice VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Arm.Straight (inWord outWord bitOf xorBits assign)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp)
open VG.Proof.Sm4 (W32.rotP)
open VG.Impl.Sm4 (Lin)

/-- The registers `q 0 … q 7` hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

/-! ## A round -/

/-- The slots below the table; the round keys' 32 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := tableSlot, ext := kp, exts := 32 }

/-- The state's planes, from input word `x`: plane `j` of word `w` is
input word `x + 8 w + j`. -/
def stateIns (x : Nat) : List (Nat × Nat) := (List.range 32).map fun k => (32 + k, x + k)

def stateSlots : List Nat := (List.range 32).map (32 + ·)

def preEnv : Env (Nat × Nat) := linEnvG [] (stateIns 0) []

/-- `preX e b c d`: plane `j` of `X_b ⊕ X_c ⊕ X_d ⊕ rk`, the round key at
entry `e` of `kp`. -/
def preG (e b c d j p : Nat) : List Nat :=
  [32 * (8 * b + j) + p, 32 * (8 * c + j) + p, 32 * (8 * d + j) + p, 32 * (32 + 8 * e + j) + p]

theorem pre0_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 0 1 2 3) preEnv
      (linPostG 11 (qOuts (preG 0 1 2 3)) [] stateSlots preEnv) = true := by
  decide +kernel

theorem pre1_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 1 2 3 0) preEnv
      (linPostG 11 (qOuts (preG 1 2 3 0)) [] stateSlots preEnv) = true := by
  decide +kernel

theorem pre2_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 2 3 0 1) preEnv
      (linPostG 11 (qOuts (preG 2 3 0 1)) [] stateSlots preEnv) = true := by
  decide +kernel

theorem pre3_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 3 0 1 2) preEnv
      (linPostG 11 (qOuts (preG 3 0 1 2)) [] stateSlots preEnv) = true := by
  decide +kernel

/-- The slots below the table, without the round keys. -/
def linCfg : Cfg := { base := sb, slots := tableSlot, ext := kp, exts := 0 }

def linEnv : Env (Nat × Nat) := linEnvG qIns (stateIns 8) []

/-- Plane `j` of the state's word `a`, XOR the linear layer of the S-box's output. -/
def linG (l : Lin) (a j p : Nat) : List Nat :=
  (32 * (8 + 8 * a + j) + p) :: (l.terms j).map fun sm => 32 * sm.1 + W32.rotP p sm.2

/-- The state's planes but word `a`'s. -/
def linKeep (a : Nat) : List Nat := ((List.range 32).filter (· / 8 != a)).map (32 + ·)

def linOuts (l : Lin) (a : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map fun j => (stateSlot a j, linG l a j)

/-- `linG` written out, without `List.map`, whose evaluation by the kernel
costs most of a check that evaluates `linG` at every bit of every output
(`linOuts_eq_flat`). -/
def linGFlat : Lin → Nat → Nat → Nat → List Nat
  | .enc, a, j, p =>
    if 2 ≤ j then
      [32 * (8 + 8 * a + j) + p, 32 * j + W32.rotP p 0, 32 * j + W32.rotP p 3, 32 * (j - 2) + W32.rotP p 0,
        32 * (j - 2) + W32.rotP p 1, 32 * (j - 2) + W32.rotP p 2]
    else
      [32 * (8 + 8 * a + j) + p, 32 * j + W32.rotP p 0, 32 * j + W32.rotP p 3, 32 * (j + 6) + W32.rotP p 1,
        32 * (j + 6) + W32.rotP p 2, 32 * (j + 6) + W32.rotP p 3]
  | .key, a, j, p =>
    [32 * (8 + 8 * a + j) + p, 32 * j + W32.rotP p 0,
      if 5 ≤ j then 32 * (j - 5) + W32.rotP p 1 else 32 * (j + 3) + W32.rotP p 2,
      if j = 7 then 32 * 0 + W32.rotP p 2 else 32 * (j + 1) + W32.rotP p 3]

theorem linG_eq_flat : linG = linGFlat := by
  funext l a j p
  cases l <;> simp only [linG, linGFlat, Lin.terms, Proof.Sm4.linTerms, Proof.Sm4.keyTerms]
  · split <;> simp
  · by_cases h5 : 5 ≤ j <;> by_cases h7 : j = 7 <;> simp [h5, h7]

def linOutsFlat (l : Lin) (a : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map fun j => (stateSlot a j, linGFlat l a j)

theorem linOuts_eq_flat : linOuts = linOutsFlat := by
  funext l a; simp only [linOuts, linOutsFlat, linG_eq_flat]

theorem linE0_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 0) linEnv
      (linPostG 11 [] (linOuts .enc 0) (linKeep 0) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linE1_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 1) linEnv
      (linPostG 11 [] (linOuts .enc 1) (linKeep 1) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linE2_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 2) linEnv
      (linPostG 11 [] (linOuts .enc 2) (linKeep 2) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linE3_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 3) linEnv
      (linPostG 11 [] (linOuts .enc 3) (linKeep 3) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK0_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 0) linEnv
      (linPostG 11 [] (linOuts .key 0) (linKeep 0) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK1_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 1) linEnv
      (linPostG 11 [] (linOuts .key 1) (linKeep 1) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK2_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 2) linEnv
      (linPostG 11 [] (linOuts .key 2) (linKeep 2) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK3_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 3) linEnv
      (linPostG 11 [] (linOuts .key 3) (linKeep 3) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

/-! ## The transposes -/

/-- The slots below the table, without external words. -/
def bsCfg : Cfg := { base := sb, slots := tableSlot, ext := sb, exts := 0 }

/-- The tail buffer's 32 words are input words `0 … 31`. -/
def tailIns : List (Nat × Nat) := (List.range 32).map fun k => (tailSlot + k, k)

def toBsEnv : Env (Nat × Nat) := linEnvG [] tailIns []

/-- Plane `j` of the state's word `w`, at `p = 8 i + b`: bit `j` of byte `i`
of word `w` of block `b` (the tail buffer's word `4 b + w`). -/
def toBsG (w j p : Nat) : List Nat := [32 * (4 * (p % 8) + w) + 8 * (p / 8) + j]

def toBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => (32 + k, toBsG (k / 8) (k % 8))

theorem toBs_check :
    check (lanes 32 10) bsCfg (linExt 0) toBs toBsEnv (linPostG 10 [] toBsOuts [] toBsEnv) = true := by
  lit_decide

def fromBsEnv : Env (Nat × Nat) := linEnvG [] (stateIns 0) []

/-- Bit `8 i + j` of the tail buffer's word `t = 4 b + w`, byte `i` (from the
most significant) of word `w` of block `b`: plane `j` of the state's word
`3 - w` at `8 i + b`. -/
def fromBsG (t k : Nat) : List Nat := [32 * (8 * (3 - t % 4) + k % 8) + 8 * (k / 8) + t / 4]

def fromBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun t => (tailSlot + t, fromBsG t)

theorem fromBs_check :
    check (lanes 32 10) bsCfg (linExt 0) fromBs fromBsEnv
      (linPostG 10 [] fromBsOuts stateSlots fromBsEnv) = true := by
  lit_decide

/-! ## The round keys' planes -/

/-- The entry at `kp`. -/
def entryCfg : Cfg := { base := kp, slots := 8, ext := kp, exts := 0 }

def keyEnv : Env (Nat × Nat) := linEnvG [(q 0, 0)] [] []

/-- Plane `j` of a round key's: bit `8 i + b` is bit `8 i + j` of its word,
byte-reversed, in `q 0`. -/
def keyBsG (j p : Nat) : List Nat := [8 * (p / 8) + j]

theorem keyPlanes_check :
    check (lanes 32 5) entryCfg (linExt 0) keyPlanes keyEnv
      (linPostG 5 [] ((List.range 8).map fun j => (j, keyBsG j)) [] keyEnv) = true := by
  decide +kernel

end VG.Proof.Sm4.Arm

end

end

/-! ### `Sm4.Arm.Sbox`, which only this module used -/

section

/-!
# The bitsliced SM4 S-box on ARMv7

`sboxCode` only combines words bitwise, so it computes the same Boolean
function at each of the 32 bit positions: the kernel evaluates it once on
truth tables of the 256 inputs (`Bitslice.table`) and compares the result
with the specification's S-box on the same inputs. `sbox_ok` then gives,
at every bit position `p`, the S-box of the byte formed by bit `p` of the
eight words.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4
open VG.Proof.Sm4.W32 (bsByte getLsbD_bsByte)

/-- The S-box's memory: its spill slots, at `r8`. -/
def sboxCfg : Cfg := { base := sb, slots := 32, ext := sb, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some (sboxT j)

theorem sbox_check :
    check (table 32 256) sboxCfg (fun _ => none) Impl.Sm4.Arm.sboxCode sboxEnv sboxPost = true := by
  lit_decide

/-- The registers the layers may write: the state, the S-box's temporaries
and all ones, and the linear layers' masks and temporaries. -/
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

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa Impl.Sm4.Arm.sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32,
        (s'.gpr (q j)).getLsbD p = (sboxB (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some (sboxT j) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 32, ∃ s', runBlock isa Impl.Sm4.Arm.sboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (Impl.Sm4.Arm.sboxCode.all fun i => !clobbers i r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_using [])
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, sboxT, testBit_tableOf]
    simp [hc, sboxN_eq hc, BitVec.testBit_toNat]
  · simp [writes_rest (is := Impl.Sm4.Arm.sboxCode) (by decide +kernel) r hr]

end VG.Proof.Sm4.Arm

end

end


/-!
# A round of bitsliced SM4 on ARMv7

As on x86-64 (`Proof/Sm4/X86_64/Core.lean`), on 32-bit planes:
`round_ok`, with the state's four words in their slots (`StRel`) and the
round key's planes at entry `a` of `kp`, `round l a a b c d` replaces word
`a` of every block's state with its new value (`sround`), keeping the other
words and writing only the slots below the table. The layers are composed
from their checks (`Linear.lean`, `Sbox.lean`) and `W32.round_rel`.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Bitslice (lanes)
open VG.Impl.Aes.Arm (q sb t0 t1 kp)
open VG.Proof.Sm4 (sround W32.WordRel W32.termsXor W32.round_rel)
open VG.Impl.Sm4 (Lin)

/-- The planes in the state registers. -/
abbrev Qs (s : State) (i : Nat) : BitVec 32 := s.gpr (q i)

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr sb) k) 32

/-- Word `k` of the table entries at `kp`. -/
abbrev keyW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr kp) k) 32

/-- The planes of the state's word `w`. -/
def planes (s : State) (w : Nat) : Nat → BitVec 32 := fun j => slotW s (stateSlot w j)

/-- The state's words hold the blocks' states: word `w` of block `b` is `X b w`. -/
def StRel (s : State) (X : Nat → Nat → Spec.Sm4.Word) : Prop :=
  ∀ w < 4, W32.WordRel (planes s w) (fun b => X b w)

theorem ok_sbox {s : State} (h : Ok layerCfg s) : Ok sboxCfg s where
  slotIn k hk := h.slotIn k (by simp [sboxCfg, layerCfg, tableSlot] at hk ⊢; omega_using [hk])
  extIn k hk := by simp [sboxCfg] at hk
  slots := by have := h.slots; simp [sboxCfg, layerCfg, tableSlot] at this ⊢; omega_using [this]
  sep k _ j hj := by simp [sboxCfg] at hj

/-- A frame of the first `n` slots keeps slot `k ≥ n`. -/
theorem slot_above {m m' : Mem} {b : BitVec 32} {n k : Nat} (hf : Frame [⟨State.addr b, 4 * n⟩] m m') (hk : n ≤ k)
    (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) : m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  have e : wordAddr b k = State.addr b + BitVec.ofNat 64 (4 * k) := addr_add (by omega_using [hfit])
  have := b.isLt
  have hb : (State.addr b).toNat = b.toNat := by simp [State.addr]; omega_using []
  rw [e]
  exact hf.readW (r := ⟨State.addr b + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base _ (by omega_using [hk]) (by omega_using [hfit])) (by decide)

theorem stateIns_mem {x j i : Nat} (h : (j, i) ∈ stateIns x) : ∃ k < 32, j = 32 + k ∧ i = x + k := by
  simp only [stateIns, List.mem_map, List.mem_range, Prod.mk.injEq] at h
  obtain ⟨k, hk, rfl, rfl⟩ := h
  exact ⟨k, hk, rfl, rfl⟩

theorem planes_eq (s : State) (w j : Nat) : planes s w j = slotW s (32 + (8 * w + j)) := by
  simp only [planes, stateSlot, Nat.add_assoc]

theorem xorBits_map32 (W : Nat → BitVec 32) (l : List (Nat × Nat)) (hl : ∀ wt ∈ l, wt.2 < 32) :
    xorBits W (l.map fun wt => 32 * wt.1 + wt.2) = W32.termsXor W l := by
  induction l with
  | nil => rfl
  | cons wt l ih =>
    simp only [List.map_cons, xorBits_cons, W32.termsXor, List.foldr_cons] at ih ⊢
    rw [bitOf_word _ _ _ (hl wt (by simp)), ih fun v hv => hl v (by simp [hv])]

theorem termsXor_congr {W S : Nat → BitVec 32} (hS : ∀ i < 8, W i = S i) :
    ∀ l : List (Nat × Nat), (∀ wt ∈ l, wt.1 < 8) → W32.termsXor W l = W32.termsXor S l
  | [], _ => rfl
  | wt :: l, h => by
    have ih := termsXor_congr hS l fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [W32.termsXor, List.foldr_cons] at ih ⊢
    rw [hS wt.1 (h wt List.mem_cons_self), ih]

/-- The linear layer's terms, as the bits of the S-box's output. -/
theorem xorBits_terms (W S : Nat → BitVec 32) (hS : ∀ i < 8, W i = S i) (l : List (Nat × Nat))
    (hl : ∀ sm ∈ l, sm.1 < 8) (p : Nat) :
    xorBits W (l.map fun sm => 32 * sm.1 + W32.rotP p sm.2) =
      W32.termsXor S (l.map fun sm => (sm.1, W32.rotP p sm.2)) := by
  rw [show (l.map fun sm => 32 * sm.1 + W32.rotP p sm.2) =
      ((l.map fun sm => (sm.1, W32.rotP p sm.2)).map fun wt => 32 * wt.1 + wt.2) by simp,
    xorBits_map32 W _ (fun wt hwt => by
      simp only [List.mem_map] at hwt; obtain ⟨sm, _, rfl⟩ := hwt; exact Nat.mod_lt _ (by decide))]
  exact termsXor_congr hS _ fun wt hwt => by
    simp only [List.mem_map] at hwt; obtain ⟨sm, hsm, rfl⟩ := hwt; exact hl sm hsm

theorem ok_lin {s : State} (h : Ok layerCfg s) : Ok linCfg s where
  slotIn k hk := h.slotIn k (by simpa [linCfg, layerCfg] using hk)
  extIn k hk := by simp [linCfg] at hk
  slots := by have := h.slots; simpa [linCfg, layerCfg] using this
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

/-- A round, with the round key at entry `a` of `kp`. -/
theorem round_ok (l : Lin) {a b c d : Nat} (ha : a < 4)
    (hb : b = (a + 1) % 4) (hc : c = (a + 2) % 4) (hd : d = (a + 3) % 4)
    (hpre : check (lanes 32 11) layerCfg (linExt 32) (preX a b c d) preEnv
      (linPostG 11 (qOuts (preG a b c d)) [] stateSlots preEnv) = true)
    (hlin : check (lanes 32 11) linCfg (linExt 40) (lin l a) linEnv
      (linPostG 11 [] (linOuts l a) (linKeep a) linEnv) = true)
    (hall : (layerKeep.all fun r =>
      (preX a b c d ++ lin l a).all fun i => !clobbers i r) = true)
    {s : State} (hok : Ok layerCfg s) {X : Nat → Nat → Spec.Sm4.Word} {k : Spec.Sm4.Word}
    (hX : StRel s X) (hK : W32.WordRel (fun j => keyW s (8 * a + j)) fun _ => k) :
    ∃ s', runBlock isa (round l a a b c d) s = some s' ∧
      StRel s' (fun b' => sround l k a (X b')) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  have hall' : ∀ r, r ∉ layerWrites → ((preX a b c d).all fun i => !clobbers i r) = true ∧
      ((lin l a).all fun i => !clobbers i r) = true := fun r hr => by
    have := List.all_eq_true.mp hall r (not_layerWrites r hr)
    rw [List.all_append, Bool.and_eq_true] at this
    exact this
  have hsb : sb ∉ layerWrites := by decide
  have hkp : kp ∉ layerWrites := by decide
  have hfit := hok.slots
  simp only [layerCfg, tableSlot] at hfit
  -- The S-box's input.
  let W₁ : Nat → BitVec 32 := fun i => if i < 32 then slotW s (32 + i) else keyW s (i - 32)
  obtain ⟨s₁, h₁, x₁, -, k₁, rd₁, wr₁, sp₁, o₁, f₁, -, -⟩ := linG_ok hpre hok W₁
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [layerCfg, tableSlot]; omega_arith, by omega_arith, by simp [W₁, hk]; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₁, show ¬ 32 + j < 32 by omega_arith]; rfl⟩)
  have b₁ : s₁.gpr sb = s.gpr sb := o₁ _ (hall' sb hsb).1
  have kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (hall' kp hkp).1
  have hW₁ : ∀ w < 4, ∀ j < 8, W₁ (8 * w + j) = planes s w j := fun w hw j hj => by
    simp only [W₁, show 8 * w + j < 32 by omega_arith, ↓reduceIte, planes_eq]
  have hXb : ∀ j < 8, ∀ p < 32, (Qs s₁ j).getLsbD p =
      ((((planes s b j).getLsbD p ^^ (planes s c j).getLsbD p) ^^ (planes s d j).getLsbD p) ^^
        (keyW s (8 * a + j)).getLsbD p) := by
    intro j hj p hp
    have hb4 : b < 4 := by omega_arith
    have hc4 : c < 4 := by omega_arith
    have hd4 : d < 4 := by omega_arith
    rw [x₁ (q j) (preG a b c d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
      preG, xorBits_cons, xorBits_cons, xorBits_cons, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp,
      bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, hW₁ b hb4 j hj, hW₁ c hc4 j hj,
      hW₁ d hd4 j hj]
    simp only [W₁, show ¬ 32 + 8 * a + j < 32 by omega_arith, ↓reduceIte, show 32 + 8 * a + j - 32 = 8 * a + j by omega_arith,
      Bool.xor_false, Bool.xor_assoc]
  have hok₁ : Ok layerCfg s₁ := hok.congr b₁ kp₁ rd₁ wr₁
  have keep₁ : ∀ k ∈ stateSlots, slotW s₁ k = slotW s k := fun k hk => by
    have hk' : k < layerCfg.slots := by
      simp only [stateSlots, List.mem_map, List.mem_range] at hk
      simp only [layerCfg, tableSlot]
      obtain ⟨x, hx, rfl⟩ := hk; omega_arith
    have := k₁ k hk hk'
    simp only [layerCfg] at this
    rw [slotW, b₁, this]
  -- The S-box.
  obtain ⟨s₂, h₂, sx₂, rd₂, wr₂, sp₂, o₂, f₂⟩ := sbox_ok (ok_sbox hok₁)
  have b₂ : s₂.gpr sb = s.gpr sb := (o₂ sb hsb).trans b₁
  have kp₂ : s₂.gpr kp = s.gpr kp := (o₂ kp hkp).trans kp₁
  have hok₂ : Ok layerCfg s₂ := hok₁.congr (o₂ sb hsb) (o₂ kp hkp) rd₂ wr₂
  have above₂ : ∀ k, 32 ≤ k → k < tableSlot → slotW s₂ k = slotW s₁ k := fun k h1 h2 => by
    simp only [slotW, o₂ sb hsb]
    refine slot_above (n := 32) (by simpa [slotRegion, sboxCfg] using f₂) h1 ?_
    rw [b₁]; simp [tableSlot] at h2; omega_arith
  have keep₂ : ∀ k ∈ stateSlots, slotW s₂ k = slotW s k := fun k hk => by
    have hk' : 32 ≤ k ∧ k < tableSlot := by
      simp only [stateSlots, List.mem_map, List.mem_range] at hk
      obtain ⟨x, hx, rfl⟩ := hk; simp only [tableSlot]; omega_arith
    rw [above₂ k hk'.1 hk'.2, keep₁ k hk]
  have hst₂ : ∀ w < 4, ∀ j < 8, slotW s₂ (32 + (8 * w + j)) = planes s w j := fun w hw j hj => by
    rw [keep₂ _ (by simp only [stateSlots, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega_arith, rfl⟩),
      planes_eq]
  -- The linear layer, into word `a`.
  let W₃ : Nat → BitVec 32 := fun i => if i < 8 then Qs s₂ i else slotW s₂ (32 + (i - 8))
  obtain ⟨s₃, h₃, -, y₃, k₃, rd₃, wr₃, sp₃, o₃, f₃, -, -⟩ := linG_ok hlin (ok_lin hok₂) W₃
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, by simp [W₃, hi]⟩)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [linCfg, tableSlot]; omega_arith, by omega_arith, by
        simp [W₃, show ¬ 8 + k < 8 by omega_arith]; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [linCfg] at hj)
  have b₃ : s₃.gpr sb = s.gpr sb := (o₃ _ ((hall' sb hsb).2)).trans b₂
  have hA' : ∀ j < 8, ∀ p < 32, (planes s₃ a j).getLsbD p =
      ((planes s a j).getLsbD p ^^ W32.termsXor (Qs s₂) ((l.terms j).map fun sm => (sm.1, W32.rotP p sm.2))) := by
    intro j hj p hp
    have := y₃ (stateSlot a j) (linG l a j) (by simp only [linOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      (by simp [stateSlot, linCfg, tableSlot]; omega_arith) p hp
    simp only [linCfg] at this
    rw [planes, slotW, b₃, ← b₂, this, linG, xorBits_cons, bitOf_word _ _ _ hp,
      xorBits_terms W₃ (Qs s₂) (fun i hi => by simp [W₃, hi]) _ (Proof.Sm4.terms_lt l j hj)]
    simp only [W₃, show ¬ 8 + 8 * a + j < 8 by omega_arith, ↓reduceIte, show 32 + (8 + 8 * a + j - 8) = 32 + (8 * a + j) by omega_arith,
      hst₂ a ha j hj]
  have keep₃ : ∀ k ∈ linKeep a, slotW s₃ k = slotW s₂ k := fun k hk => by
    have hk' : k < linCfg.slots := by
      simp only [linKeep, List.mem_map, List.mem_filter, List.mem_range] at hk
      simp only [linCfg, tableSlot]
      obtain ⟨x, ⟨hx, -⟩, rfl⟩ := hk; omega_arith
    have := k₃ k hk hk'
    simp only [linCfg] at this
    rw [slotW, b₃, ← b₂, this]
  refine ⟨s₃, ?_, fun w hw => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
    by rw [sp₃, sp₂, sp₁], fun r hr => ?_, ?_⟩
  · rw [round, runBlock_app, runBlock_app, h₁, Option.bind_some, h₂, Option.bind_some, h₃]
  · by_cases hwa : w = a
    · subst hwa
      have hr := W32.round_rel l (hX b (by omega_arith)) (hX c (by omega_arith)) (hX d (by omega_arith)) hK (hX w hw) hXb sx₂ hA'
      refine hr.congr_right fun b' _ => ?_
      simp only [sround, ↓reduceIte, hb, hc, hd]
    · refine (hX w hw).congr (fun j hj => ?_) |>.congr_right fun b' _ => by simp only [sround, hwa, ↓reduceIte]
      show planes s₃ w j = planes s w j
      rw [planes_eq, planes_eq, keep₃ _ (by
        simp only [linKeep, List.mem_map, List.mem_filter, List.mem_range]
        exact ⟨8 * w + j, ⟨by omega_arith, by simp; omega_arith⟩, rfl⟩), hst₂ w hw j hj, planes_eq]
  · rw [o₃ r (hall' r hr).2, o₂ r hr, o₁ r (hall' r hr).1]
  · have e₂ : slotRegion linCfg s₂ = slotRegion layerCfg s := by simp only [slotRegion, linCfg, layerCfg, b₂]
    refine f₁.trans ((f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans (e₂ ▸ f₃))
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, sboxCfg, layerCfg, b₁]
    exact Region.sub_prefix (by simp [tableSlot])

end VG.Proof.Sm4.Arm

end

end


/-!
# Eight blocks of bitsliced SM4 on ARMv7: the rounds

As on x86-64 (`Proof/Sm4/X86_64/Core.lean`): with the table of bitsliced
round keys `E 0 … E 31` in the scratch buffer (`KeyCtx`), the rounds are
`round_ok`, four at a time (`rounds4_ok`), in a loop whose invariant is
`quads`; they write only the slots below the table (`Ctx`). `rounds_wp`
is that loop for either linear transformation, which the key schedule
runs too.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Bitslice (lanes)
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR)
open VG.Proof.Sm4 (sround quad quads ofBlock outBlock W32.WordRel)
open VG.Impl.Sm4 (Lin)

/-- Word `j` of entry `e` of the table, in the scratch buffer at `b`. -/
def entryW (m : Mem) (b : BitVec 32) (e j : Nat) : BitVec 32 :=
  m.readW (wordAddr b (tableSlot + 8 * e + j)) 32

/-- What the rounds need: the scratch buffer, writable, and a table of 32
round keys. -/
structure KeyCtx (s₀ : State) (E : Nat → Spec.Sm4.Word) : Prop where
  scr : (⟨State.addr (s₀.gpr sb), 4 * slots⟩ : Region) ∈ s₀.wr
  fit : (s₀.gpr sb).toNat + 4 * slots ≤ 2 ^ 32
  keys : ∀ e < 32, W32.WordRel (entryW s₀.mem (s₀.gpr sb) e) fun _ => E e

/-- What stays the same: the regions, the stack pointer, the registers but
the layers' and `kp`, and the memory outside the slots below the table. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ layerWrites → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [⟨State.addr (s₀.gpr sb), 4 * tableSlot⟩] s₀.mem s.mem

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide)

theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hk : ∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r)
    (hf : Frame [⟨State.addr (s₀.gpr sb), 4 * tableSlot⟩] s.mem s'.mem) : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r h1 h2 => (hk r h1 h2).trans (hc.keep r h1 h2),
    hc.frame.trans hf⟩

theorem Ctx.trans {s₀ s₁ s₂ : State} (h₁ : Ctx s₀ s₁) (h₂ : Ctx s₁ s₂) : Ctx s₀ s₂ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, fun r a b => (h₂.keep r a b).trans (h₁.keep r a b),
    h₁.frame.trans (by rw [← h₁.base]; exact h₂.frame)⟩

/-! ## Addresses -/

theorem slots_eq : slots = 364 := rfl
theorem tableSlot_eq : tableSlot = 96 := rfl
theorem tableEnd_eq : tableEnd = 352 := rfl
theorem tailSlot_eq : tailSlot = 64 := rfl

/-- `kp` at entry `m` of the table. -/
def AtEntry (s : State) (b : BitVec 32) (m : Nat) : Prop :=
  s.gpr kp = b + BitVec.ofNat 32 (4 * tableSlot + 32 * m)

theorem keyW_entry {s : State} {b : BitVec 32} {m : Nat} (hk : AtEntry s b m) (e j : Nat) :
    keyW s (8 * e + j) = entryW s.mem b (m + e) j := by
  simp only [keyW, wordAddr, entryW]
  rw [hk, add_ofNat_ofNat,
    show 4 * tableSlot + 32 * m + 4 * (8 * e + j) = 4 * (tableSlot + 8 * (m + e) + j) by omega_arith]

/-- Slot `k` of the scratch buffer at `b`, as a 64-bit offset. -/
theorem slot_addr {b : BitVec 32} {k : Nat} (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    wordAddr b k = State.addr b + BitVec.ofNat 64 (4 * k) := addr_add (by omega_arith)

theorem addr_toNat (b : BitVec 32) : (State.addr b).toNat = b.toNat := by
  have := b.isLt; simp [State.addr]; omega_arith

/-- Slot `k` is in the scratch buffer. -/
theorem slot_in {rs : List Region} {b : BitVec 32} {n k : Nat} (hr : (⟨State.addr b, 4 * n⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) : InRegions rs (wordAddr b k) 4 :=
  ⟨_, hr, by
    rw [slot_addr (by omega_arith)]
    have := addr_toNat b
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem ok_layer {s : State} {b : BitVec 32} {m : Nat} (hscr : (⟨State.addr b, 4 * slots⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) (hb : s.gpr sb = b) (hk : AtEntry s b m) (hm : m + 4 ≤ 32) :
    Ok layerCfg s where
  slotIn k hk' := by
    simp only [layerCfg, tableSlot_eq] at hk' ⊢
    rw [hb]; exact slot_in hscr hfit (by rw [slots_eq]; omega_arith)
  extIn j hj := by
    simp only [layerCfg] at hj ⊢
    have e : wordAddr (s.gpr kp) j = wordAddr b (tableSlot + 8 * m + j) := by
      simp only [wordAddr]; rw [show s.gpr kp = _ from hk, add_ofNat_ofNat]
      rw [show 4 * tableSlot + 32 * m + 4 * j = 4 * (tableSlot + 8 * m + j) by omega_arith]
    rw [e]
    obtain ⟨r, hr, hc⟩ := slot_in hscr hfit (k := tableSlot + 8 * m + j) (by rw [slots_eq, tableSlot_eq]; omega_arith)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  slots := by simp only [layerCfg, tableSlot_eq]; rw [hb]; rw [slots_eq] at hfit; omega_arith
  sep k hk' j hj := by
    simp only [layerCfg, tableSlot_eq] at hk' hj ⊢
    have e : wordAddr (s.gpr kp) j = wordAddr b (tableSlot + 8 * m + j) := by
      simp only [wordAddr]; rw [show s.gpr kp = _ from hk, add_ofNat_ofNat]
      rw [show 4 * tableSlot + 32 * m + 4 * j = 4 * (tableSlot + 8 * m + j) by omega_arith]
    rw [e, hb]
    rw [slots_eq] at hfit
    exact slot_sep b (by omega_arith) (by rw [tableSlot_eq]; omega_arith) (by rw [tableSlot_eq]; omega_arith)

/-! ## Under `Ctx` -/

theorem Ctx.entry {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {e j : Nat} (he : e < 32) (hj : j < 8) :
    entryW s.mem (s₀.gpr sb) e j = entryW s₀.mem (s₀.gpr sb) e j := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  have hb := addr_toNat (s₀.gpr sb)
  simp only [entryW]
  rw [slot_addr (by rw [tableSlot_eq]; omega_arith)]
  refine hc.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq]; omega_arith) (by rw [tableSlot_eq]; omega_arith)

theorem Ctx.keyRel {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m e : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hme : m + e < 32) :
    W32.WordRel (fun j => keyW s (8 * e + j)) fun _ => E (m + e) :=
  (hp.keys _ hme).congr fun j hj => by rw [keyW_entry hk, hc.entry hp hme hj]

theorem Ctx.ok {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 4 ≤ 32) : Ok layerCfg s :=
  ok_layer (by rw [hc.wr]; exact hp.scr) hp.fit hc.base hk hm

/-- A round, under `Ctx`: `round l a …` with the round key at entry `m + a`. -/
theorem round_step (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {a b c d m : Nat} (ha : a < 4) (hb : b = (a + 1) % 4) (hc' : c = (a + 2) % 4) (hd : d = (a + 3) % 4)
    (hpre : check (lanes 32 11) layerCfg (linExt 32) (preX a b c d) preEnv
      (linPostG 11 (qOuts (preG a b c d)) [] stateSlots preEnv) = true)
    (hlin : check (lanes 32 11) linCfg (linExt 40) (lin l a) linEnv
      (linPostG 11 [] (linOuts l a) (linKeep a) linEnv) = true)
    (hall : (layerKeep.all fun r =>
      (preX a b c d ++ lin l a).all fun i => !clobbers i r) = true)
    (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 4 ≤ 32) {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa (round l a a b c d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      StRel s' (fun b' => sround l (E (m + a)) a (X b')) := by
  obtain ⟨s', h', hX', rd', wr', sp', o', f'⟩ :=
    round_ok l ha hb hc' hd hpre hlin hall (hc.ok hp hk hm) hX (hc.keyRel hp hk (e := a) (by omega_arith))
  refine ⟨s', h', hc.step rd' wr' sp' (fun r hr _ => o' r hr) (f'.mono fun r hr => ?_), o' _ (by decide), hX'⟩
  simp only [List.mem_singleton] at hr; subst hr
  simp only [slotRegion, layerCfg, hc.base]; simp

/-- Four rounds, the round keys at entries `4 m … 4 m + 3`. -/
theorem rounds4_ok (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) (4 * m)) (hm : m < 8) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s X) :
    ∃ s', runBlock isa (rounds4 l) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      StRel s' (fun b => quad l E m (X b)) := by
  have hm4 : 4 * m + 4 ≤ 32 := by omega_arith
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := round_step l hp hc (a := 0) (by decide) rfl rfl rfl pre0_check
    (by cases l <;> [exact linE0_check; exact linK0_check]) (by cases l <;> decide +kernel) hk hm4 hX
  obtain ⟨s₂, e₂, c₂, k₂, X₂⟩ := round_step l hp c₁ (a := 1) (by decide) rfl rfl rfl pre1_check
    (by cases l <;> [exact linE1_check; exact linK1_check]) (by cases l <;> decide +kernel)
    (by rw [AtEntry, k₁]; exact hk) hm4 X₁
  obtain ⟨s₃, e₃, c₃, k₃, X₃⟩ := round_step l hp c₂ (a := 2) (by decide) rfl rfl rfl pre2_check
    (by cases l <;> [exact linE2_check; exact linK2_check]) (by cases l <;> decide +kernel)
    (by rw [AtEntry, k₂, k₁]; exact hk) hm4 X₂
  obtain ⟨s₄, e₄, c₄, k₄, X₄⟩ := round_step l hp c₃ (a := 3) (by decide) rfl rfl rfl pre3_check
    (by cases l <;> [exact linE3_check; exact linK3_check]) (by cases l <;> decide +kernel)
    (by rw [AtEntry, k₃, k₂, k₁]; exact hk) hm4 X₃
  refine ⟨s₄, ?_, c₄, by rw [k₄, k₃, k₂, k₁], ?_⟩
  · rw [rounds4, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄]
  · simpa only [quad, Nat.add_zero] using X₄

/-! ## The loop of the rounds -/

/-- `add d, n, #v` (`v` encodable). -/
theorem addImm_ok (s : State) (d n : Reg) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.dp .add d n (.imm v)] s = some s' ∧ s'.gpr d = s.gpr n + v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.gpr n + v), by
    rw [runBlock_cons, show exec (.dp .add d n (.imm v)) s = some (s.setReg d (s.gpr n + v)) by
      simp [exec, Op2.eval, hv], runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `sub d, n, #v` (`v` encodable). -/
theorem subImm_ok (s : State) (d n : Reg) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.dp .sub d n (.imm v)] s = some s' ∧ s'.gpr d = s.gpr n - v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.gpr n - v), by
    rw [runBlock_cons, show exec (.dp .sub d n (.imm v)) s = some (s.setReg d (s.gpr n - v)) by
      simp [exec, Op2.eval, hv], runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `sub t0, kp, sb; cmp t0, #v`. -/
theorem endTest_ok (s : State) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.dp .sub t0 kp (.reg sb), .cmp t0 (.imm v)] s = some s' ∧
      s'.z = (s.gpr kp - s.gpr sb - v == 0) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₁ := s.setReg t0 (s.gpr kp - s.gpr sb)
  refine ⟨subFlags s₁ (s.gpr kp - s.gpr sb) v, ?_, by simp [subFlags], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [runBlock_cons, show exec (.dp .sub t0 kp (.reg sb)) s = some s₁ from rfl, runStep_some, runBlock_cons,
      show exec (.cmp t0 (.imm v)) s₁ = some (subFlags s₁ (s.gpr kp - s.gpr sb) v) by
        simp [exec, Op2.eval, hv, s₁, RegUpd.gpr_setReg_self],
      runStep_some, runBlock_nil]
  · simp [subFlags, s₁, RegUpd.gpr_setReg_of_ne _ _ hr]

theorem ofNat32_sub_beq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

/-- `cmp`'s `ne`: whether `Z` is clear. -/
theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

/-- A step that changes only `kp` keeps `Ctx`. -/
theorem Ctx.kp {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ kp → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : Ctx s₀ s' :=
  hc.step hrd hwr hsp (fun r _ h2 => hg r h2) (by rw [hm]; exact Frame.refl _ _)

/-- A step that changes only `t0` (and the flags) keeps `Ctx`. -/
theorem Ctx.t0 {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ t0 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : Ctx s₀ s' :=
  hc.step hrd hwr hsp (fun r h1 _ => hg r fun h => h1 (by subst h; decide)) (by rw [hm]; exact Frame.refl _ _)

theorem StRel.congr {s s' : State} {X : Nat → Nat → Spec.Sm4.Word} (h : StRel s X)
    (hs : ∀ k, slotW s' k = slotW s k) : StRel s' X :=
  fun w hw => (h w hw).congr fun _ _ => hs _

/-- Four rounds, `kp += 128` and the end test. -/
theorem roundsBody_ok (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) (4 * m)) (hm : m < 8) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s X) :
    ∃ s', runBlock isa (roundsBody l) s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (4 * (m + 1)) ∧
      StRel s' (fun b => quad l E m (X b)) ∧ s'.z = decide (m + 1 = 8) := by
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok l hp hc hk hm hX
  obtain ⟨s₂, e₂, kp₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₁ kp kp 128 (by decide)
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃, sp₃⟩ := endTest_ok s₂ (BitVec.ofNat 32 (4 * tableEnd)) (by decide)
  have hc₂ : Ctx s₀ s₂ := c₁.kp o₂ m₂ rd₂ wr₂ sp₂
  have hk₂ : AtEntry s₂ (s₀.gpr sb) (4 * (m + 1)) := by
    rw [AtEntry, kp₂, k₁, show s.gpr kp = _ from hk, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl,
      add_ofNat_ofNat, show 4 * tableSlot + 32 * (4 * m) + 128 = 4 * tableSlot + 32 * (4 * (m + 1)) by omega_arith]
  refine ⟨s₃, ?_, hc₂.t0 g₃ m₃ rd₃ wr₃ sp₃, by rw [AtEntry, g₃ _ (by decide)]; exact hk₂, ?_, ?_⟩
  · rw [roundsBody, runBlock_app, e₁, Option.bind_some,
      show ([.dp .add kp kp (.imm 128), .dp .sub t0 kp (.reg sb), .cmp t0 (.imm (BitVec.ofNat 32 (4 * tableEnd)))] :
        List Instr) = [.dp .add kp kp (.imm 128)] ++ [.dp .sub t0 kp (.reg sb),
          .cmp t0 (.imm (BitVec.ofNat 32 (4 * tableEnd)))] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃]
  · exact X₁.congr fun k => by simp only [slotW, m₃, g₃ sb (by decide), m₂, o₂ sb (by decide)]
  · rw [z₃, show s₂.gpr kp = _ from hk₂, hc₂.base, VG.Offset.add_sub_cancel_left, ofNat32_sub_beq
      (by rw [tableSlot_eq]; omega_arith) (by rw [tableEnd_eq]; omega_arith), tableSlot_eq, tableEnd_eq]
    simp only [decide_eq_decide]; omega_arith

/-- `add kp, sb, #4 k`. -/
theorem kpAt_ok (s : State) (k : Nat) (hv : encodable (BitVec.ofNat 32 (4 * k)) = true) :
    ∃ s', runBlock isa [kpAt k] s = some s' ∧ s'.gpr kp = s.gpr sb + BitVec.ofNat 32 (4 * k) ∧
      (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  addImm_ok s kp sb _ hv

/-- The 32 rounds, the round keys at entries `0 … 31`. -/
theorem rounds_wp (l : Lin) {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s₀ X) :
    WP isa (rounds l) s₀ fun s' => Ctx s₀ s' ∧ StRel s' (fun b => quads l E 8 (X b)) := by
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := kpAt_ok s₀ tableSlot (by decide)
  have hc₁ : Ctx s₀ s₁ := (Ctx.refl s₀).kp o₁ m₁ rd₁ wr₁ sp₁
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  let Inv : Nat → State → Prop := fun n s' => ∃ m, n = 8 - m ∧ m < 8 ∧ Ctx s₀ s' ∧
    AtEntry s' (s₀.gpr sb) (4 * m) ∧ StRel s' (fun b => quads l E m (X b))
  refine WP.loop (M := isa) Inv (fun n s' hs' => ?_) 8 s₁
    ⟨0, rfl, by omega_arith, hc₁, by rw [AtEntry, k₁]; simp, hX.congr fun k => by simp only [slotW, m₁, o₁ sb (by decide)]⟩
  obtain ⟨m, rfl, hm8, hc', hk', hX'⟩ := hs'
  obtain ⟨s'', e'', c'', k'', X'', z''⟩ := roundsBody_ok l hp hc' hk' hm8 hX'
  have X3 : StRel s'' fun b => quads l E (m + 1) (X b) := X''
  refine WP.of_runBlock ⟨s'', e'', ?_⟩
  by_cases h8 : m + 1 = 8
  · refine .inl ⟨by rw [eval_ne, z'', h8]; rfl, c'', ?_⟩
    rw [h8] at X3; exact X3
  · exact .inr ⟨by rw [eval_ne, z'']; simp [h8], 8 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, c'', k'', X3⟩

end VG.Proof.Sm4.Arm

end

end

/-!
# Slots, and saving and restoring registers, on ARMv7

Loads and stores of the scratch buffer's slots through a base register
(`ldW_ok`, `stW_ok`, and lists of them), and the prologue and epilogue's
saving and restoring of the callee-saved registers (`save_ok`,
`restore_ok`) in the slots from `savedSlot`.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (sb t0 t1 kp)

theorem savedSlot_eq : savedSlot = 352 := rfl
theorem dSlot_eq : dSlot = 361 := rfl
theorem nSlot_eq : nSlot = 362 := rfl

/-- The scratch buffer at `b`, in the writable regions. -/
structure ScrIn (rs : List Region) (b : BitVec 32) : Prop where
  mem : (⟨State.addr b, 4 * slots⟩ : Region) ∈ rs
  fit : b.toNat + 4 * slots ≤ 2 ^ 32

theorem ScrIn.slot {rs : List Region} {b : BitVec 32} (h : ScrIn rs b) {k : Nat} (hk : k < slots) :
    InRegions rs (wordAddr b k) 4 := slot_in h.mem h.fit hk

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A slot is inside the scratch buffer. -/
theorem slot_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k : Nat} (hk : k < slots) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨State.addr b, 4 * slots⟩ := by
  rw [slot_addr (by omega_using [hfit, hk])]
  exact VG.Offset.sub_base _ (by omega_using [hk])

/-- A slot after a store to a slot. -/
theorem readW_slot_write {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hfit, hj]) (by omega_using [hfit, hk]) h) (by decide)

/-- `ldr d, [n, #4 k]`, `n` holding `b`. -/
theorem ldW_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : 4 * k < 4096)
    (hin : InRegions (s.rd ++ s.wr) (wordAddr b k) 4) :
    ∃ s', runBlock isa [.ldr d n (4 * k)] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), by
    rw [runBlock_cons, exec_ldr hk (by rw [hn]; exact hin), hn, runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `str t, [n, #4 k]`, `n` holding `b`. -/
theorem stW_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : 4 * k < 4096)
    (hin : InRegions s.wr (wordAddr b k) 4) :
    runBlock isa [.str t n (4 * k)] s = some { s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) } := by
  rw [runBlock_cons, exec_str hk (by rw [hn]; exact hin), hn, runStep_some, runBlock_nil]

/-- A store to a slot of the scratch buffer. -/
theorem stSlot_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.str t n (4 * k)] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.z = s.z ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem :=
  ⟨_, stW_ok s t n hn (by rw [slots_eq] at hk; omega_using [hk]) (hw.slot hk), rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩

/-- A load of a slot of the scratch buffer. -/
theorem ldSlot_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.ldr d n (4 * k)] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ldW_ok s d n hn (by rw [slots_eq] at hk; omega_using [hk]) (inRd (hw.slot hk))

/-- Stores of registers to distinct slots, through `n`, which none of them is. -/
theorem stW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Nat × Reg)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.map fun x => .str x.2 n (4 * x.1)) s = some s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < slots → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      ∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = s.gpr x.2
  | [], s, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hnd, hin => by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, sp₁, -, f₁⟩ := stSlot_ok s x.2 n hn (hin x List.mem_cons_self) hw
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', sp', f', o', v'⟩ :=
      stW_list_ok n L s₁ (by rw [g₁, hn]) (by rw [wr₁]; exact hw) hnd.2
        fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁, sp'.trans sp₁,
      (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hw.fit (hin x List.mem_cons_self)⟩).trans f',
      fun k hk hks => ?_,
      fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hks, m₁, readW_slot_write hw.fit _ hks (hin x List.mem_cons_self)]
      simp only [hk.1, ite_false]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (hin _ List.mem_cons_self), m₁, Mem.readW_writeW_self32]
      · rw [v' y hy, g₁]

/-- Loads of distinct slots into distinct registers, through `n`, which none of them is. -/
theorem ldW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Reg × Nat)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (∀ x ∈ L, x.1 ≠ n) → (L.map (·.1)).Nodup → (∀ x ∈ L, x.2 < slots) →
    ∃ s', runBlock isa (L.map fun x => .ldr x.1 n (4 * x.2)) s = some s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧
      ∀ x ∈ L, s'.gpr x.1 = s.mem.readW (wordAddr b x.2) 32
  | [], s, _, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hne, hnd, hin => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s x.1 n hn (hin x List.mem_cons_self) hw
    have hn₁ : s₁.gpr n = b := by rw [o₁ _ (hne x List.mem_cons_self).symm, hn]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', sp', o', v'⟩ := ldW_list_ok n L s₁ hn₁ (by rw [wr₁]; exact hw)
      (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, sp'.trans sp₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1, v₁]
      · rw [v' y hy, m₁]

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .r4

theorem savedRegs_eq : savedRegs = (List.range 9).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 9, m.readW (wordAddr b (savedSlot + i)) 32 = s₀.gpr (sreg i)

theorem save_ok {s : State} {base : Reg} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr base = b) :
    ∃ s', runBlock isa (saveRegs base) s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem ∧
      ∀ k, k < savedSlot → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 := by
  let L : List (Nat × Reg) := (List.range 9).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs base = L.map fun x => .str x.2 base (4 * x.1) := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 9).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  obtain ⟨s', e', g', rd', wr', sp', f', o', v'⟩ := stW_list_ok base L s hb hw (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega)
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, g', rd', wr', sp', f', fun k hk => o' k ?_ (by
    rw [savedSlot_eq] at hk; rw [slots_eq]; omega_using [hk])⟩
  · exact v' (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
  · rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega_using [hk, h]

theorem sreg_ne_r12 : ∀ i < 9, sreg i ≠ .r12 := by decide

theorem restore_ok {s₀ s : State} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr .r12 = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa (restoreRegs .r12) s = some s' ∧ (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 9, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let L : List (Reg × Nat) := (List.range 9).map fun i => (sreg i, savedSlot + i)
  have hL : restoreRegs .r12 = L.map fun x => .ldr x.1 .r12 (4 * x.2) := by
    rw [restoreRegs, savedRegs_eq]
  have hregs : L.map (·.1) = (List.range 9).map sreg := by simp only [L, List.map_map]; rfl
  obtain ⟨s', e', m', rd', wr', sp', o', v'⟩ := ldW_list_ok .r12 L s hb hw
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx; exact sreg_ne_r12 i hi)
    (by rw [hregs]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega)
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, fun r hr => o' r ?_, m', rd', wr', sp'⟩
  · rw [v' (sreg i, savedSlot + i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)]
    exact hs i hi
  · rw [hregs]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    exact fun i hi h => hr i hi h.symm

end VG.Proof.Sm4.Arm

end

end

/-! ### `Sm4.Arm.Crypt8`, which this module and modules that import it used -/

section

/-!
# The transposes, and eight blocks of bitsliced SM4 on ARMv7

`toBs_step` turns the eight blocks of the tail buffer into the state's
planes, and `fromBs_step` turns the state's planes back into the output
blocks (the words in reverse order); `crypt8_wp` composes them with the
32 rounds (`rounds_wp`): each block of the tail buffer becomes the output
of SM4's rounds with the table's round keys.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR)
open VG.Proof.Sm4 (quads ofBlock outBlock getLsbD_wordAt getLsbD_outBlock' blockAt_getD)
open VG.Impl.Sm4 (Lin)

/-- Block `b` of the tail buffer. -/
abbrev tailBlock (s : State) (b : Nat) : Spec.Sm4.Block :=
  Spec.Sm4.blockAt s.mem (State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * b))

theorem KeyCtx.of_ctx {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    KeyCtx s E where
  scr := by rw [hc.wr, hc.base]; exact hp.scr
  fit := by rw [hc.base]; exact hp.fit
  keys e he := by rw [hc.base]; exact (hp.keys e he).congr fun j hj => hc.entry hp he hj

theorem ok_bs {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) : Ok bsCfg s where
  slotIn k hk := by
    simp only [bsCfg, tableSlot_eq] at hk ⊢
    rw [hc.wr, hc.base]; exact slot_in hp.scr hp.fit (by rw [slots_eq]; omega_arith)
  extIn k hk := by simp [bsCfg] at hk
  slots := by have := hp.fit; simp only [bsCfg, hc.base]; rw [slots_eq] at this; rw [tableSlot_eq]; omega_arith
  sep k _ j hj := by simp [bsCfg] at hj

/-- The registers `Ctx` keeps but `kp`: `sb` alone. -/
theorem keep_sb (r : Reg) (h1 : r ∉ layerWrites) (h2 : r ≠ kp) : r = sb := by
  revert h1 h2; cases r <;> decide

/-- A block of the slots below the table that keeps `sb` keeps `Ctx`. -/
theorem Ctx.bs {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hb : s'.gpr sb = s.gpr sb) (hf : Frame [slotRegion bsCfg s] s.mem s'.mem) : Ctx s₀ s' :=
  hc.step hrd hwr hsp (fun r h1 h2 => by rw [keep_sb r h1 h2]; exact hb) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, bsCfg, hc.base])

theorem byte_addr (b : BitVec 32) {k i n : Nat} (hn : 4 * k + i = n) (hfit : b.toNat + 4 * k < 2 ^ 32) :
    wordAddr b k + BitVec.ofNat 64 i = State.addr b + BitVec.ofNat 64 n := by
  rw [wordAddr, addr_add hfit, BitVec.add_assoc, ← BitVec.ofNat_add, hn]

/-- The tail buffer's blocks to the state's planes. -/
theorem toBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa toBs s = some s' ∧ Ctx s₀ s' ∧
      StRel s' (fun b w => ofBlock (tailBlock s b) w) := by
  have hchk := toBs_check
  unfold toBsEnv at hchk
  have hfit := hp.fit
  rw [slots_eq, ← hc.base] at hfit
  obtain ⟨s', h', -, hso, -, rd', wr', sp', -, f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (tailSlot + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [tailIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [bsCfg, tableSlot_eq, tailSlot_eq]; omega_arith, by omega_arith, rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso
  refine ⟨s', h', hc.bs rd' wr' sp' hb' f', fun w hw b hb i hi j hj => ?_⟩
  have hp8 : 8 * i + b < 32 := by omega_arith
  have hmem := hso (32 + (8 * w + j)) (toBsG ((8 * w + j) / 8) ((8 * w + j) % 8)) (by
      simp only [toBsOuts, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega_arith, rfl⟩)
      (by rw [tableSlot_eq]; omega_arith) _ hp8
  rw [show (8 * w + j) / 8 = w by omega_arith, show (8 * w + j) % 8 = j by omega_arith] at hmem
  have ht : 8 * i + j < 32 := by omega_arith
  show (slotW s' (stateSlot w j)).getLsbD (8 * i + b) = _
  rw [slotW, hb', show stateSlot w j = 32 + (8 * w + j) by simp only [stateSlot]; omega_arith, hmem, toBsG,
    show (8 * i + b) % 8 = b by omega_arith, show (8 * i + b) / 8 = i by omega_arith, xorBits_cons, xorBits_nil,
    Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ ht, slotW, readW_bit _ _ hi hj]
  simp only [ofBlock]
  rw [getLsbD_wordAt _ _ hi hj, blockAt_getD _ _ (by omega_arith), byte_addr _ rfl (by rw [tailSlot_eq]; omega_arith),
    BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * (tailSlot + (4 * b + w)) + i = 4 * tailSlot + 16 * b + (4 * w + i) by omega_arith]

/-- The state's planes back to the tail buffer's blocks. -/
theorem fromBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa fromBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ StRel s' X ∧
      ∀ b < 8, tailBlock s' b = outBlock (X b) := by
  have hchk := fromBs_check
  unfold fromBsEnv at hchk
  have hfit := hp.fit
  rw [slots_eq, ← hc.base] at hfit
  obtain ⟨s', h', -, hso, hkeep, rd', wr', sp', o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (32 + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [bsCfg, tableSlot_eq]; omega_arith, by omega_arith, by simp only [Nat.zero_add]; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkeep
  have hall : (fromBs.all fun i => !clobbers i kp) = true := by decide +kernel
  refine ⟨s', h', hc.bs rd' wr' sp' hb' f', o' kp hall, fun w hw => (hX w hw).congr fun j hj => ?_, fun b hb => ?_⟩
  · show slotW s' (stateSlot w j) = slotW s (stateSlot w j)
    have hm : stateSlot w j ∈ stateSlots := by
      simp only [stateSlots, List.mem_map, List.mem_range]
      exact ⟨8 * w + j, by omega_arith, by simp only [stateSlot]; omega_arith⟩
    rw [slotW, hb', hkeep _ hm (by simp only [stateSlot, tableSlot_eq]; omega_arith)]
  apply Vector.ext
  intro k hk
  refine BitVec.eq_of_getLsbD_eq fun j hj => ?_
  rw [getLsbD_outBlock' (X b) hk hj]
  have ht : 8 * (k % 4) + j < 32 := by omega_arith
  have hmem := hso (tailSlot + (4 * b + k / 4)) (fromBsG (4 * b + k / 4)) (by
      simp only [fromBsOuts, List.mem_map, List.mem_range]; exact ⟨4 * b + k / 4, by omega_arith, rfl⟩)
      (by rw [tableSlot_eq, tailSlot_eq]; omega_arith) _ ht
  rw [readW_bit _ _ (by omega_arith) hj, byte_addr _ rfl (by rw [tailSlot_eq]; omega_arith)] at hmem
  have e1 : 8 * (3 - (4 * b + k / 4) % 4) + (8 * (k % 4) + j) % 8 = 8 * (3 - k / 4) + j := by omega_arith
  have e2 : 8 * ((8 * (k % 4) + j) / 8) + (4 * b + k / 4) / 4 = 8 * (k % 4) + b := by omega_arith
  have hw : 3 - k / 4 < 4 := by omega_arith
  have hbit := hX (3 - k / 4) hw b hb (k % 4) (by omega_arith) j hj
  rw [fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, e1, Nat.add_assoc, e2, bitOf_word _ _ _ (by omega_arith)] at hmem
  simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
  rw [hb', BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * tailSlot + 16 * b + k = 4 * (tailSlot + (4 * b + k / 4)) + k % 4 by omega_arith,
    hmem, ← hbit, planes_eq]

/-- `crypt8`: each block of the tail buffer becomes the output of SM4's 32
rounds with the table's round keys. -/
theorem crypt8_wp {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) :
    WP isa crypt8 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 8, tailBlock s' b = outBlock (quads .enc E 8 (ofBlock (tailBlock s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, X₁⟩ := toBs_step hp (Ctx.refl s₀)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (rounds_wp .enc (hp.of_ctx c₁) X₁) fun s₂ ⟨c₂, X₂⟩ => ?_)
  have c₀₂ := c₁.trans c₂
  obtain ⟨s₃, e₃, c₃, -, -, hout⟩ := fromBs_step hp c₀₂ X₂
  exact WP.of_runBlock ⟨s₃, e₃, c₃, hout⟩

end VG.Proof.Sm4.Arm

end

end

/-! ### `Sm4.Arm.Keys`, which this module and modules that import it used -/

section

/-!
# The table of bitsliced round keys on ARMv7

`keyOne_step`: `keyOne` bitslices the round key at `r12` into the table's
entry at `kp`, every block's copy of it alike. `keys_wp` builds the table in
the order the rounds use the round keys: `rk₀ … rk₃₁` for encryption,
`rk₃₁ … rk₀` for decryption.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR lsrOp)
open VG.Proof.Sm4 (getLsbD_scheduleAt)

/-- `ldr r0, [r12]; rev r0, r0`. -/
theorem keyWord_ok (s : State) (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 0)) 4) :
    ∃ s', runBlock isa keyWord s = some s' ∧
      s'.gpr (q 0) = rev (s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 0)) 32) ∧
      (∀ r, r ≠ q 0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let x := s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 0)) 32
  refine ⟨(s.setReg (q 0) x).setReg (q 0) (rev x), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl, rfl⟩
  rw [keyWord, runBlock_cons, exec_ldr (by decide) h, runStep_some, runBlock_cons,
    show exec (.rev (q 0) (q 0)) (s.setReg (q 0) x) = some ((s.setReg (q 0) x).setReg (q 0) (rev x)) by
      simp only [exec, RegUpd.gpr_setReg_self],
    runStep_some, runBlock_nil]

/-- The schedule at `sched`, apart from the scratch buffer at `b`. -/
structure SchedPre (s : State) (b sched : BitVec 32) : Prop where
  base : s.gpr sb = b
  scr : (⟨State.addr b, 4 * slots⟩ : Region) ∈ s.wr
  fit : b.toNat + 4 * slots ≤ 2 ^ 32
  sch : (⟨State.addr sched, 128⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr sched, 128⟩ ⟨State.addr b, 4 * slots⟩

theorem SchedPre.congr {s s' : State} {b sched : BitVec 32} (h : SchedPre s b sched)
    (hb : s'.gpr sb = s.gpr sb) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SchedPre s' b sched :=
  ⟨hb.trans h.base, hwr ▸ h.scr, h.fit, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

/-- Round key `i` of the schedule at `sched`. -/
theorem SchedPre.keyIn {s : State} {b sched : BitVec 32} (h : SchedPre s b sched) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (State.addr (sched + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4 :=
  ⟨_, h.sch, by
    have := h.schFit
    rw [BitVec.add_zero, addr_add (by omega_arith)]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- The word at round key `i` is round key `i`. -/
theorem key_word (m : Mem) {sched : BitVec 32} (hfit : sched.toNat + 128 ≤ 2 ^ 32) {i : Nat} (hi : i < 32) :
    m.readW (State.addr (sched + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 =
      (Spec.Sm4.scheduleAt m (State.addr sched)).getD i 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [VG.Proof.Aes.getD_eq _ hi, show k = 8 * (k / 8) + k % 8 by omega_arith,
    getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith), readW_bit _ _ (by omega_arith) (by omega_arith),
    BitVec.add_zero, addr_add (by omega_arith), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The table's entry `e` at `b`. -/
theorem entry_addr {b : BitVec 32} {e j : Nat} :
    wordAddr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)) j = wordAddr b (tableSlot + 8 * e + j) := by
  simp only [wordAddr]
  rw [add_ofNat_ofNat, show 4 * tableSlot + 32 * e + 4 * j = 4 * (tableSlot + 8 * e + j) by omega_arith]

/-- The round key at `r12` to the entry at `kp`. -/
theorem keyOne_step {s : State} {b sched : BitVec 32} {e i : Nat} (hp : SchedPre s b sched)
    (hkp : s.gpr kp = b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)) (he : e < 32)
    (hr : s.gpr .r12 = sched + BitVec.ofNat 32 (4 * i)) (hi : i < 32) :
    ∃ s', runBlock isa keyOne s = some s' ∧
      (∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)), 32⟩] s.mem s'.mem ∧
      W32.WordRel (entryW s'.mem b e) (fun _ => (Spec.Sm4.scheduleAt s.mem (State.addr sched)).getD i 0) := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  -- The word.
  obtain ⟨s₁, e₁, x₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := keyWord_ok s (by rw [hr]; exact hp.keyIn hi)
  rw [hr, key_word _ hp.schFit hi] at x₁
  -- Its planes, to the entry.
  have kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (by decide)
  have hok : Ok entryCfg s₁ :=
    { slotIn := fun k hk => by
        simp only [entryCfg] at hk ⊢
        rw [wr₁, kp₁, hkp, entry_addr]
        exact slot_in hp.scr hp.fit (by rw [slots_eq, tableSlot_eq]; omega_arith)
      extIn := fun k hk => by simp [entryCfg] at hk
      slots := by
        simp only [entryCfg]; rw [kp₁, hkp, BitVec.toNat_add, BitVec.toNat_ofNat, tableSlot_eq]
        have := b.isLt
        rw [Nat.mod_eq_of_lt (show 384 + 32 * e < 2 ^ 32 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
      sep := fun k _ j hj => by simp [entryCfg] at hj }
  have hchk := keyPlanes_check
  unfold keyEnv at hchk
  obtain ⟨s₂, e₂, -, hso₂, -, rd₂, wr₂, sp₂, o₂, f₂, -, -⟩ := linG_ok hchk hok (fun _ => s₁.gpr (q 0))
    (fun r i hri => by
      simp only [List.mem_singleton, Prod.mk.injEq] at hri
      obtain ⟨rfl, rfl⟩ := hri
      exact ⟨by decide, rfl⟩)
    (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv) (fun j hj => by simp [entryCfg] at hj)
  simp only [entryCfg] at hso₂ f₂
  have he₂ : ∀ j < 8, ∀ p < 32, (entryW s₂.mem b e j).getLsbD p = (rev (Vector.getD
      (Spec.Sm4.scheduleAt s.mem (State.addr sched)) i 0)).getLsbD (8 * (p / 8) + j) := fun j hj p hp => by
    have h := hso₂ j (keyBsG j) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) hj p hp
    rw [keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
      show 8 * (p / 8) + j = 32 * 0 + (8 * (p / 8) + j) by omega_arith, bitOf_word _ _ _ (by omega_arith), x₁, kp₁, hkp,
      entry_addr] at h
    rw [entryW, h]
  have hall₂ : ([Reg.r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .lr].all fun r =>
      keyPlanes.all fun i => !clobbers i r) = true := by decide +kernel
  refine ⟨s₂, ?_, fun r h0 h3 h11 => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], ?_, ?_⟩
  · rw [keyOne, runBlock_app, e₁, Option.bind_some, e₂]
  · rw [o₂ r (List.all_eq_true.mp hall₂ r (by revert h0 h3 h11; cases r <;> decide)), o₁ r h0]
  · rw [← m₁]
    refine f₂.mono fun r hr => ?_
    simp only [slotRegion, List.mem_singleton] at hr; subst hr
    rw [kp₁, hkp]; exact List.mem_singleton_self _
  · intro b' hb' i' hi' j hj
    rw [he₂ j hj _ (by omega_arith), show (8 * i' + b') / 8 = i' by omega_arith, rev_bit _ hi' hj]

/-! ## The loop -/

/-- The entry of round key `i`: `i` for encryption, `31 - i` for decryption. -/
def entOf : Dir → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 31 - i

/-- `kp` before iteration `m`, as an offset in the scratch buffer. -/
def kpAtIter : Dir → Nat → Nat
  | .encrypt, m => 4 * tableSlot + 32 * m
  | .decrypt, m => 4 * tableSlot - 32 + 32 * (32 - m)

/-- The instruction stepping `kp`. -/
def kpStep : Dir → Instr
  | .encrypt => .dp .add kp kp (.imm 32)
  | .decrypt => .dp .sub kp kp (.imm 32)

/-- The loop's body. -/
def tableBody (dir : Dir) : List Instr :=
  keyOne ++ ([.dp .add .r12 .r12 (.imm 4), kpStep dir, .subs .lr .lr (.imm 1)] : List Instr)

theorem keys_eq (dir : Dir) :
    keys dir = .seq (.block [kpAt (match dir with | .encrypt => tableSlot | .decrypt => tableSlot + 8 * 31),
      .mov .lr (.imm 32)]) (.loop (.block (tableBody dir)) .ne) := by
  cases dir <;> rfl

theorem kpAtIter_ent (dir : Dir) {m : Nat} (hm : m < 32) :
    kpAtIter dir m = 4 * tableSlot + 32 * entOf dir m := by
  cases dir <;> simp only [kpAtIter, entOf, tableSlot_eq] <;> omega_arith

theorem entOf_lt (dir : Dir) {i : Nat} (hi : i < 32) : entOf dir i < 32 := by cases dir <;> simp [entOf] <;> omega_arith

theorem entOf_inj (dir : Dir) {i i' : Nat} (hi : i < 32) (hi' : i' < 32) (h : entOf dir i = entOf dir i') :
    i = i' := by cases dir <;> simp [entOf] at h <;> omega_arith

theorem entOf_entOf (dir : Dir) {e : Nat} (he : e < 32) : entOf dir (entOf dir e) = e := by
  cases dir <;> simp [entOf] <;> omega_arith

/-- `kp ± 32`. -/
theorem kpStep_ok (dir : Dir) (s : State) {b : BitVec 32} {m : Nat} (hm : m < 32)
    (hkp : s.gpr kp = b + BitVec.ofNat 32 (kpAtIter dir m)) :
    ∃ s', runBlock isa [kpStep dir] s = some s' ∧ s'.gpr kp = b + BitVec.ofNat 32 (kpAtIter dir (m + 1)) ∧
      (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  cases dir
  · obtain ⟨s', e', r', o', m', rd', wr', sp'⟩ := addImm_ok s kp kp 32 (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr', sp'⟩
    rw [r', hkp, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, add_ofNat_ofNat]
    simp only [kpAtIter]; rw [show 4 * tableSlot + 32 * m + 32 = 4 * tableSlot + 32 * (m + 1) by omega_arith]
  · obtain ⟨s', e', r', o', m', rd', wr', sp'⟩ := subImm_ok s kp kp 32 (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr', sp'⟩
    simp only [kpAtIter] at hkp ⊢
    rw [r', hkp, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
      show 4 * tableSlot - 32 + 32 * (32 - m) = (4 * tableSlot - 32 + 32 * (32 - (m + 1))) + 32 by
        rw [tableSlot_eq]; omega_arith, ← add_ofNat_ofNat, BitVec.add_sub_cancel]

/-- `subs d, n, #1`. -/
theorem subs1_ok (s : State) (d : Reg) :
    ∃ s', runBlock isa [.subs d d (.imm 1)] s = some s' ∧ s'.gpr d = s.gpr d - 1 ∧ s'.z = (s.gpr d - 1 == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1), ?_, RegUpd.gpr_setReg_self _ _ _, by rw [RegUpd.z_setReg]; rfl,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d d (.imm 1)) s = some ((subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1)) by
    simp [exec, Op2.eval]; decide, runStep_some, runBlock_nil]

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e i : Nat}
    (hf : Frame [⟨State.addr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)), 32⟩] m m')
    (hi : i < 32) (he : e < 32) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  rw [slots_eq] at hfit
  have hb := addr_toNat b
  rw [addr_add (by rw [tableSlot_eq]; omega_arith)] at hf
  simp only [entryW]
  rw [slot_addr (by rw [tableSlot_eq]; omega_arith)]
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [tableSlot_eq]
  exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The table's entry `e` is inside the table. -/
theorem entry_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e : Nat} (he : e < 32) :
    Region.Sub ⟨State.addr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)), 32⟩ ⟨State.addr b, 4 * tableEnd⟩ := by
  rw [slots_eq] at hfit
  rw [addr_add (by rw [tableSlot_eq]; omega_arith), tableSlot_eq, tableEnd_eq]
  exact VG.Offset.sub_base _ (by omega_arith)

theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

/-- What the loop keeps, after `m` of its 32 iterations. -/
structure KInv (s₀ : State) (b sched : BitVec 32) (dir : Dir) (m : Nat) (s : State) : Prop where
  pre : SchedPre s b sched
  kpv : s.gpr kp = b + BitVec.ofNat 32 (kpAtIter dir m)
  ptr : s.gpr .r12 = sched + BitVec.ofNat 32 (4 * m)
  cnt : s.gpr .lr = BitVec.ofNat 32 (32 - m)
  ent : ∀ i < m, W32.WordRel (entryW s.mem b (entOf dir i))
    (fun _ => (Spec.Sm4.scheduleAt s₀.mem (State.addr sched)).getD i 0)
  frame : Frame [⟨State.addr b, 4 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → r ≠ .r12 → r ≠ kp → r ≠ .lr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The schedule is outside the scratch buffer. -/
theorem SchedPre.sched_eq {s : State} {b sched : BitVec 32} (h : SchedPre s b sched) {m m' : Mem} {n : Nat}
    (hn : n ≤ slots) (hf : Frame [⟨State.addr b, 4 * n⟩] m m') :
    Spec.Sm4.scheduleAt m' (State.addr sched) = Spec.Sm4.scheduleAt m (State.addr sched) := by
  have hb : ∀ k < 128, m' (State.addr sched + BitVec.ofNat 64 k) = m (State.addr sched + BitVec.ofNat 64 k) :=
    fun k hk => hf.bytes (R := ⟨State.addr sched, 128⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.sep.sub_right (Region.sub_prefix (by omega_arith))) (by show 128 ≤ 2 ^ 64; omega_arith) hk
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega_arith), hb (4 * i + 1) (by omega_arith), hb (4 * i + 2) (by omega_arith), hb (4 * i + 3) (by omega_arith)]

/-- One iteration: round key `m`. -/
theorem keyIter_ok (dir : Dir) {s₀ s : State} {b sched : BitVec 32} {m : Nat} (hm : m < 32)
    (hi : KInv s₀ b sched dir m s) :
    ∃ s', runBlock isa (tableBody dir) s = some s' ∧ KInv s₀ b sched dir (m + 1) s' ∧
      s'.z = decide (m + 1 = 32) := by
  have hpre := hi.pre
  have hfit := hpre.fit
  have he := entOf_lt dir hm
  have hsched : Spec.Sm4.scheduleAt s.mem (State.addr sched) = Spec.Sm4.scheduleAt s₀.mem (State.addr sched) :=
    hpre.sched_eq (by rw [tableEnd_eq, slots_eq]; omega_arith) hi.frame
  obtain ⟨s₁, e₁, o₁, rd₁, wr₁, sp₁, f₁, E₁⟩ := keyOne_step (e := entOf dir m) hpre
    (by rw [hi.kpv, kpAtIter_ent dir hm]) he hi.ptr hm
  rw [hsched] at E₁
  have ko : ∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → s₁.gpr r = s.gpr r := o₁
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₁ .r12 .r12 4 (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := kpStep_ok dir s₂ (b := b) hm
    (by rw [o₂ _ (by decide), ko kp (by decide) (by decide) (by decide), hi.kpv])
  obtain ⟨s₄, e₄, c₄, z₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := subs1_ok s₃ .lr
  have hc₃ : s₃.gpr .lr = BitVec.ofNat 32 (32 - m) := by
    rw [o₃ _ (by decide), o₂ _ (by decide), ko .lr (by decide) (by decide) (by decide), hi.cnt]
  have hmem : s₄.mem = s₁.mem := by rw [m₄, m₃, m₂]
  have hb₄ : s₄.gpr sb = s.gpr sb := by
    rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), ko sb (by decide) (by decide) (by decide)]
  have hf₁ : Frame [⟨State.addr b, 4 * tableEnd⟩] s₀.mem s₁.mem :=
    hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact entry_sub hfit he⟩)
  refine ⟨s₄, ?_, ⟨hpre.congr hb₄ (by rw [rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄, wr₃, wr₂, wr₁]),
      by rw [o₄ _ (by decide), r₃], ?_, ?_, fun i hi' => ?_, by rw [hmem]; exact hf₁,
      fun r h0 h3 h11 h12 hk hl => by rw [o₄ r hl, o₃ r hk, o₂ r h12, ko r h0 h3 h11, hi.regs r h0 h3 h11 h12 hk hl],
      by rw [rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₄, wr₃, wr₂, wr₁, hi.wr], by rw [sp₄, sp₃, sp₂, sp₁, hi.sp]⟩, ?_⟩
  · rw [tableBody, runBlock_app, e₁, Option.bind_some,
      show ([.dp .add .r12 .r12 (.imm 4), kpStep dir, .subs .lr .lr (.imm 1)] : List Instr) =
        [.dp .add .r12 .r12 (.imm 4)] ++ ([kpStep dir] ++ [.subs .lr .lr (.imm 1)]) from rfl,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [o₄ _ (by decide), o₃ _ (by decide), r₂, ko .r12 (by decide) (by decide) (by decide), hi.ptr,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_ofNat, show 4 * m + 4 = 4 * (m + 1) by omega_arith]
  · rw [c₄, hc₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      show 32 - m - 1 = 32 - (m + 1) by omega_arith]
  · rw [hmem]
    rcases (show i < m ∨ i = m by omega_arith) with hlt | rfl
    · exact (hi.ent i hlt).congr fun j hj => entryW_frame hfit f₁ (entOf_lt dir (by omega_arith)) he
        (fun h => by have := entOf_inj dir (by omega_arith) hm h; omega_arith) hj
    · exact E₁
  · rw [z₄, hc₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      ofNat32_beq_zero (by omega_arith)]
    simp only [decide_eq_decide]; omega_arith

theorem keyLoop_wp (dir : Dir) {s₀ s : State} {b sched : BitVec 32} (hi : KInv s₀ b sched dir 0 s) :
    WP isa (.loop (.block (tableBody dir)) .ne) s (KInv s₀ b sched dir 32) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 32 - m ∧ m < 32 ∧ KInv s₀ b sched dir m s)
    (fun n s hs => ?_) 32 s ⟨0, rfl, by omega_arith, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := keyIter_ok dir hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h32 : m + 1 = 32
  · exact .inl ⟨by rw [eval_ne, z', h32]; rfl, by rw [h32] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_ne, z']; simp [h32], 32 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, hi'⟩

/-- The round keys in the order the rounds use them. -/
def dirKeys (dir : Dir) (sch : Spec.Sm4.Schedule) (e : Nat) : Spec.Sm4.Word := sch.getD (entOf dir e) 0

/-- What the table's construction leaves. -/
structure KeysPost (s₀ : State) (b sched : BitVec 32) (dir : Dir) (s : State) : Prop where
  pre : SchedPre s b sched
  key : KeyCtx s (dirKeys dir (Spec.Sm4.scheduleAt s₀.mem (State.addr sched)))
  frame : Frame [⟨State.addr b, 4 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → r ≠ .r12 → r ≠ kp → r ≠ .lr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- `mov d, #v` (`v` encodable). -/
theorem movImm_ok (s : State) (d : Reg) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.mov d (.imm v)] s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d v, by
    rw [runBlock_cons, show exec (.mov d (.imm v)) s = some (s.setReg d v) by simp [exec, Op2.eval, hv],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : BitVec 32} (hp : SchedPre s₀ b sched)
    (hr : s₀.gpr .r12 = sched) :
    WP isa (keys dir) s₀ (KeysPost s₀ b sched dir) := by
  rw [keys_eq]
  let k := match dir with | .encrypt => tableSlot | .decrypt => tableSlot + 8 * 31
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := kpAt_ok s₀ k (by cases dir <;> decide)
  obtain ⟨s₂, e₂, l₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movImm_ok s₁ .lr 32 (by decide)
  have hinv : KInv s₀ b sched dir 0 s₂ := by
    refine ⟨hp.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]),
      by rw [o₂ _ (by decide), k₁, hp.base]; cases dir <;> rfl,
      by rw [o₂ _ (by decide), o₁ _ (by decide), hr]; simp,
      by rw [l₂]; rfl, fun i hi => by omega_arith, by rw [m₂, m₁]; exact Frame.refl _ _,
      fun r _ _ _ _ hk hl => by rw [o₂ r hl, o₁ r hk], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁]⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, WP.mono (keyLoop_wp dir hinv) fun s h => ?_⟩)
  · rw [show ([kpAt k, .mov .lr (.imm 32)] : List Instr) = [kpAt k] ++ [.mov .lr (.imm 32)] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂]
  · refine ⟨h.pre, ⟨by rw [h.pre.base]; exact h.pre.scr, by rw [h.pre.base]; exact h.pre.fit, fun e he => ?_⟩,
      h.frame, h.regs, h.rd, h.wr, h.sp⟩
    rw [h.pre.base]
    have := h.ent (entOf dir e) (entOf_lt dir he)
    rw [entOf_entOf dir he] at this
    exact this

end VG.Proof.Sm4.Arm

end

end

/-! ### `Sm4.Arm.Copy`, which only this module used -/

section

/-!
# Copying blocks on ARMv7

As on AArch64: `copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks
of 16 bytes from `r0` to `r12` (areas that do not overlap), a word at a time
through `t0`, counting down `r3`, and changes nothing else in memory.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (t0)
open VG.Arm.Straight (add_ofNat_ofNat)
open VG.Proof.Sm4 (off_sub_toNat off_sub_not writeW_readW32_apply)

/-- What a copy keeps, after its first `k` bytes. -/
structure Copied (A B : Addr) (c : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  copied : ∀ t < k, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem

/-- `ldr t0, [r0, #d]; str t0, [r1, #d]`: the copy's next word. -/
theorem copyWord_ok {A B : BitVec 32} {c : Nat} {s₀ s : State} {j d : Nat} (hd : d < 16) (hd4 : d % 4 = 0)
    (hj : j < c) (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr B, 16 * c⟩)
    (hr : InRegions (s.rd ++ s.wr) (State.addr A + BitVec.ofNat 64 (16 * j + d)) 4)
    (hw : InRegions s.wr (State.addr B + BitVec.ofNat 64 (16 * j + d)) 4)
    (h0 : s.gpr .r0 = A + BitVec.ofNat 32 (16 * j)) (h1 : s.gpr .r12 = B + BitVec.ofNat 32 (16 * j))
    (hi : Copied (State.addr A) (State.addr B) c s₀ (16 * j + d) s) :
    ∃ s', runBlock isa [.ldr t0 .r0 d, .str t0 .r12 d] s = some s' ∧
      Copied (State.addr A) (State.addr B) c s₀ (16 * j + d + 4) s' ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain eA : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr A + BitVec.ofNat 64 (16 * j + d) := by
    rw [h0, add_ofNat_ofNat, addr_add (by omega_arith)]
  obtain eB : State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = State.addr B + BitVec.ofNat 64 (16 * j + d) := by
    rw [h1, add_ofNat_ofNat, addr_add (by omega_arith)]
  obtain h₁ : (s.setReg t0 (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32)).gpr .r12 = s.gpr .r12 :=
    RegUpd.gpr_setReg_of_ne _ _ (by decide)
  refine ⟨{ s.setReg t0 (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32) with
      mem := s.mem.writeW (State.addr B + BitVec.ofNat 64 (16 * j + d))
        (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32) }, ?_,
    ⟨fun t ht' => ?_, hi.frame.trans fun x hx => ?_⟩, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩
  · rw [runBlock_cons, exec_ldr (by omega_arith) (by rw [eA]; exact hr), eA, runStep_some, runBlock_cons,
      exec_str (by omega_arith) (by rw [h₁, eB]; exact hw), runStep_some, runBlock_nil, h₁, eB,
      RegUpd.gpr_setReg_self]
    rfl
  · have hn : 16 * c < 2 ^ 64 := by omega_arith
    obtain hAs : ∀ t < 16 * c, s.mem (State.addr A + BitVec.ofNat 64 t) = s₀.mem (State.addr A + BitVec.ofNat 64 t) :=
      fun t ht => hi.frame.bytes (R := ⟨State.addr A, 16 * c⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by simp only; omega_arith) ht
    show (s.mem.writeW _ _) _ = _
    rw [writeW_readW32_apply]
    by_cases h8 : 16 * j + d ≤ t
    · rw [ite_eq_left (by rw [off_sub_toNat _ h8 (by omega_arith)]; omega_arith), off_sub_toNat _ h8 (by omega_arith),
        VG.Offset.add_add, show 16 * j + d + (t - (16 * j + d)) = t by omega_arith, hAs t (by omega_arith)]
    · rw [ite_eq_right (off_sub_not _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
      exact hi.copied t (by omega_arith)
  · show (s.mem.writeW _ _) x = s.mem x
    rw [writeW_readW32_apply, ite_eq_right fun h =>
      hx _ (List.mem_singleton_self _) (VG.Offset.sub_base _ (show 16 * j + d + 4 ≤ 16 * c by omega_arith) _
        (by simp only [Region.Contains]; omega_arith))]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : BitVec 32) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .r0 = A + BitVec.ofNat 32 (16 * j)
  dst : s.gpr .r12 = B + BitVec.ofNat 32 (16 * j)
  cnt : s.gpr .r3 = BitVec.ofNat 32 (c - j)
  cp : Copied (State.addr A) (State.addr B) c s₀ (16 * j) s
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem copyBlocks_wp {A B : BitVec 32} {c : Nat} {s₀ : State} (hc : 0 < c) (hc8 : c ≤ 8)
    (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hA : ∀ t < 16 * c, t % 4 = 0 → InRegions (s₀.rd ++ s₀.wr) (State.addr A + BitVec.ofNat 64 t) 4)
    (hB : ∀ t < 16 * c, t % 4 = 0 → InRegions s₀.wr (State.addr B + BitVec.ofNat 64 t) 4)
    (hsep : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_arith, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  obtain rA : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.rd = s₀.rd → s.wr = s₀.wr →
      InRegions (s.rd ++ s.wr) (State.addr A + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h1 h2 => by
    rw [h1, h2]; exact hA _ (by omega_arith) (by omega_arith)
  obtain rB : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (State.addr B + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h2 => by
    rw [h2]; exact hB _ (by omega_arith) (by omega_arith)
  obtain ⟨s₁, e₁, c₁, g₁, rd₁, wr₁, sp₁⟩ := copyWord_ok (d := 0) (by decide) (by decide) hj hfA hfB hsep
    (rA 0 (by decide) (by decide) s hi.rd hi.wr) (rB 0 (by decide) (by decide) s hi.wr) hi.src hi.dst
    (by simpa using hi.cp)
  obtain ⟨s₂, e₂, c₂, g₂, rd₂, wr₂, sp₂⟩ := copyWord_ok (d := 4) (by decide) (by decide) hj hfA hfB hsep
    (rA 4 (by decide) (by decide) s₁ (rd₁.trans hi.rd) (wr₁.trans hi.wr))
    (rB 4 (by decide) (by decide) s₁ (wr₁.trans hi.wr))
    (by rw [g₁ _ (by decide), hi.src]) (by rw [g₁ _ (by decide), hi.dst]) (by simpa using c₁)
  obtain ⟨s₃, e₃, c₃, g₃, rd₃, wr₃, sp₃⟩ := copyWord_ok (d := 8) (by decide) (by decide) hj hfA hfB hsep
    (rA 8 (by decide) (by decide) s₂ (rd₂.trans (rd₁.trans hi.rd)) (wr₂.trans (wr₁.trans hi.wr)))
    (rB 8 (by decide) (by decide) s₂ (wr₂.trans (wr₁.trans hi.wr)))
    (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.src]) (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.dst])
    c₂
  obtain ⟨s₄, e₄, c₄, g₄, rd₄, wr₄, sp₄⟩ := copyWord_ok (d := 12) (by decide) (by decide) hj hfA hfB hsep
    (rA 12 (by decide) (by decide) s₃ (rd₃.trans (rd₂.trans (rd₁.trans hi.rd)))
      (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (rB 12 (by decide) (by decide) s₃ (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.src])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.dst]) c₃
  obtain g₄' : ∀ r, r ≠ t0 → s₄.gpr r = s.gpr r := fun r hr => by rw [g₄ r hr, g₃ r hr, g₂ r hr, g₁ r hr]
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅, sp₅⟩ := addImm_ok s₄ .r0 .r0 16 (by decide)
  obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := addImm_ok s₅ .r12 .r12 16 (by decide)
  obtain ⟨s₇, e₇, c₇, z₇, o₇, m₇, rd₇, wr₇, sp₇⟩ := subs1_ok s₆ .r3
  refine WP.of_runBlock ⟨s₇, by
    rw [show ([Instr.ldr t0 .r0 0, .str t0 .r12 0, .ldr t0 .r0 4, .str t0 .r12 4,
      .ldr t0 .r0 8, .str t0 .r12 8, .ldr t0 .r0 12, .str t0 .r12 12,
      .dp .add .r0 .r0 (.imm 16), .dp .add .r12 .r12 (.imm 16), .subs .r3 .r3 (.imm 1)] : List Instr) =
      [.ldr t0 .r0 0, .str t0 .r12 0] ++ ([.ldr t0 .r0 4, .str t0 .r12 4] ++ ([.ldr t0 .r0 8, .str t0 .r12 8] ++
      ([.ldr t0 .r0 12, .str t0 .r12 12] ++ ([.dp .add .r0 .r0 (.imm 16)] ++
      ([.dp .add .r12 .r12 (.imm 16)] ++ [.subs .r3 .r3 (.imm 1)]))))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some,
      runBlock_app, e₆, Option.bind_some, e₇], ?_⟩
  obtain hc₇ : s₇.gpr .r3 = BitVec.ofNat 32 (c - (j + 1)) := by
    rw [c₇, o₆ _ (by decide), o₅ _ (by decide), g₄' _ (by decide), hi.cnt,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      show c - j - 1 = c - (j + 1) by omega_arith]
  obtain hm : s₇.mem = s₄.mem := by rw [m₇, m₆, m₅]
  obtain hinv : CopyInv A B c s₀ (j + 1) s₇ := by
    refine ⟨?_, ?_, hc₇, ⟨fun t ht => ?_, by rw [hm]; exact c₄.frame⟩, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr],
      by rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁, hi.sp]⟩
    · rw [o₇ _ (by decide), o₆ _ (by decide), a₅, g₄' _ (by decide), hi.src,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_ofNat,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₇ _ (by decide), a₆, o₅ _ (by decide), g₄' _ (by decide), hi.dst,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_ofNat,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [hm]; exact c₄.copied t (by omega_arith)
    · rw [o₇ r h3, o₆ r h2, o₅ r h1, g₄' r h4, hi.regs r h1 h2 h3 h4]
  obtain hz : s₇.z = decide (c - (j + 1) = 0) := by
    rw [z₇, ← c₇, hc₇, ofNat32_beq_zero (by omega_arith)]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega_arith),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hinv⟩

end VG.Proof.Sm4.Arm

end

end


/-!
# A group of blocks of SM4 ECB on ARMv7

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(eight, or the last one to seven) to the tail buffer, transforms it
(`crypt8_wp`), copies the blocks back and steps to the next group. The data
pointer and the blocks left live in their slots (`dSlot`, `nSlot`) between
the steps, which use every other register.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Proof.Sm4 (DInv quads ofBlock outBlock not_contains_off blockAt_getD)
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR lsrOp ldS stS)

/-! ## Small blocks -/

theorem lsr3_beq {v : Nat} (hv : v < 2 ^ 32) :
    (BitVec.ofNat 32 v >>> 3 - 0 == 0) = decide (v < 8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.gpr n), by
    rw [runBlock_cons, show exec (movR d n) s = some (s.setReg d (s.gpr n)) by simp [movR, exec, Op2.eval],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `r3 := min(r2, 8)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hn : s.gpr .r2 = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa groupCount s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .r3 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₂ := s.setReg t0 (s.gpr .r2 >>> 3)
  let s₃ := subFlags s₂ (s₂.gpr t0) 0
  obtain e₂₃ : runBlock isa [.mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)] s = some s₃ := by
    rw [runBlock_cons, show exec (.mov t0 (lsrOp .r2 3)) s = some s₂ by simp [exec, Op2.eval, lsrOp, s₂],
      runStep_some, runBlock_cons,
      show exec (.cmp t0 (.imm 0)) s₂ = some s₃ by simp [exec, Op2.eval, s₃]; decide,
      runStep_some, runBlock_nil]
  obtain z₃ : s₃.z = (BitVec.ofNat 32 v >>> 3 - 0 == 0) := by
    show (s₂.gpr t0 - 0 == 0) = _; rw [RegUpd.gpr_setReg_self, hn]
  obtain o₃ : ∀ r, r ≠ t0 → s₃.gpr r = s.gpr r := fun r hr => by
    show s₂.gpr r = _; rw [RegUpd.gpr_setReg_of_ne _ _ hr]
  obtain r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [o₃ _ (by decide), hn]
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₃, e₂₃, ?_⟩)
  refine WP.ite (decide (8 ≤ v)) ((eval_ne s₃).trans (by
      rw [z₃, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega_using [h])) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movImm_ok s₃ .r3 8 (by decide)
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, Nat.min_eq_right (by simp at h; omega_using [h])]; rfl
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r3 .r2
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, r2₃, Nat.min_eq_left (by simp at h; omega_using [h])]

/-- `subs d, n, m`. -/
theorem subsR_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.subs d n (.reg m)] s = some s' ∧ s'.gpr d = s.gpr n - s.gpr m ∧
      s'.z = (s.gpr n - s.gpr m == 0) ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr n) (s.gpr m)).setReg d (s.gpr n - s.gpr m), ?_, RegUpd.gpr_setReg_self _ _ _,
    by rw [RegUpd.z_setReg]; rfl, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d n (.reg m)) s =
    some ((subFlags s (s.gpr n) (s.gpr m)).setReg d (s.gpr n - s.gpr m)) by simp [exec, Op2.eval],
    runStep_some, runBlock_nil]

theorem toNat_add32 (D : BitVec 32) {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).toNat = D.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h] : d < 2 ^ 32), Nat.mod_eq_of_lt h]

/-! ## The scratch buffer's contents -/

/-- The slots `lo … hi - 1` of the scratch buffer at `b`. -/
abbrev slotsRegion (b : BitVec 32) (lo hi : Nat) : Region :=
  ⟨State.addr b + BitVec.ofNat 64 (4 * lo), 4 * (hi - lo)⟩

/-- A slot outside a frame. -/
theorem slot_keep {rs : List Region} {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {lo hi : Nat} (hhi : hi ≤ slots) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b lo hi).Disjoint r)
    {k : Nat} (hk1 : lo ≤ k) (hk2 : k < hi) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [slots_eq] at hfit hhi
  rw [slot_addr (by omega_using [hfit, hhi, hk2])]
  exact hf.readW (VG.Offset.contains _ (by omega_using [hk1]) (by omega_using [hk2]) (by omega_using [hhi, hk1, hk2])) hd (by decide)

/-- What the data loop keeps in the scratch buffer: the table and the saved
registers, in the slots from `tableSlot` to `dSlot`. -/
structure ScrOk (s₀ : State) (b : BitVec 32) (E : Nat → Spec.Sm4.Word) (m : Mem) : Prop where
  keys : ∀ e < 32, W32.WordRel (entryW m b e) fun _ => E e
  saved : Saved s₀ b m

theorem ScrOk.frame {s₀ : State} {b : BitVec 32} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b tableSlot dSlot).Disjoint r) : ScrOk s₀ b E m' := by
  refine ⟨fun e he => (h.keys e he).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact slot_keep hfit (by decide) hf hd (by omega_using []) (by rw [dSlot_eq, tableSlot_eq]; omega_using [he, hj])
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf hd (by rw [savedSlot_eq, tableSlot_eq]; omega_using [])
      (by rw [savedSlot_eq, dSlot_eq]; omega_using [hi])

/-! ## The data loop -/

/-- Each block, transformed: the output of the 32 rounds with the round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (j : Nat) : Spec.Sm4.Block :=
  outBlock (quads .enc E 8 (ofBlock (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n : Nat) : Prop where
  scr : ScrIn s₀.wr b
  dat : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr b, 4 * slots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) :
    Prop where
  base : s.gpr sb = b
  dp : s.gpr .r1 = D + BitVec.ofNat 32 (128 * k)
  np : s.gpr .r2 = BitVec.ofNat 32 (n - 8 * k)
  lt : 8 * k < n
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n (8 * k) (outF s₀.mem (State.addr D) E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Sm4.Word) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n n (outF s₀.mem (State.addr D) E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa group s fun s' => (s'.z = true ∧ GDone s₀ b D n E s') ∨
      (s'.z = false ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hb := addr_toNat b
  rw [slots_eq] at hfit
  obtain hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_arith
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 32 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 32 (128 * k)
  let T := b + BitVec.ofNat 32 (4 * tailSlot)
  obtain hA : State.addr A = State.addr D + BitVec.ofNat 64 (128 * k) := addr_add (by omega_arith)
  obtain hT : State.addr T = State.addr b + BitVec.ofNat 64 (4 * tailSlot) := addr_add (by rw [tailSlot_eq]; omega_arith)
  obtain hAn : A.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_arith)]; omega_arith
  obtain hTn : T.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by rw [tailSlot_eq]; omega_arith), tailSlot_eq]; omega_arith
  obtain hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr T + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwS.mem, ?_⟩
    rw [hT, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr A + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain subA : Region.Sub ⟨State.addr A, 16 * c⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega_arith)
  obtain subT : Region.Sub ⟨State.addr T, 16 * c⟩ ⟨State.addr b, 4 * slots⟩ := by
    rw [hT]; exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith)
  obtain sepAT : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr T, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  -- The regions the steps write keep the slots from `tableSlot`.
  obtain dT : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr T, 16 * c⟩ := by
    rw [hT]; exact VG.Offset.disjoint _ (by rw [tableSlot_eq, tailSlot_eq]; omega_arith)
      (by rw [tableSlot_eq, slots_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain dA : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr A, 16 * c⟩ :=
    ((hp.sep.sub_left subA).sub_right (VG.Offset.sub_base _ (by rw [tableSlot_eq, slots_eq]))).symm
  obtain dTab : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr b, 4 * tableSlot⟩ :=
    VG.Offset.disjoint_base _ (by omega_arith) (by rw [tableSlot_eq, slots_eq]; omega_arith)
  obtain sub_ts : ∀ l u, tableSlot ≤ l → l ≤ u → u ≤ slots →
      (slotsRegion b l u).Sub (slotsRegion b tableSlot slots) :=
    fun l u h1 h2 h3 => VG.Offset.sub _ (by omega_arith) (by rw [slots_eq] at h3 ⊢; omega_arith)
  obtain subTab : (slotsRegion b tableSlot dSlot).Sub (slotsRegion b tableSlot slots) :=
    sub_ts _ _ (Nat.le_refl _) (by decide) (by decide)
  obtain dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨State.addr b, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨State.addr D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have r1₀ : s.gpr .r1 = A := hi.dp
  unfold group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.np hv) fun s₁ ⟨r3₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a, sp₂a⟩ := movR_ok s₁ .r0 .r1
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₂a .r12 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₂ r h12, o₂a r h0, o₁ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show ([movR .r0 .r1, tailAddr .r12] : List Instr) = [movR .r0 .r1] ++ [tailAddr .r12] from rfl,
      runBlock_app, e₂a, Option.bind_some]; exact e₂, ?_⟩)
  refine WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide) (by decide), r1₀]; simp [A],
      by rw [r₂, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base]; simp [T],
      by rw [o₂ _ (by decide), o₂a _ (by decide), r3₁, Nat.sub_zero], ⟨fun t ht => by omega_arith, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₃ h₃ => ?_
  obtain f₃ : Frame [⟨State.addr T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  obtain g₃ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₃.regs r h0 h12 h3 h4, g₂ r h0 h12 h3 h4]
  obtain base₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b E s₃.mem := hi.scr.frame hfit' f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_left subTab
  obtain wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  obtain rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  obtain sp₃ : s₃.sp = s.sp := by rw [h₃.sp, sp₂, sp₂a, sp₁]
  obtain hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The data pointer and the blocks left to their slots.
  unfold cryptSaved
  obtain ⟨s₄a, e₄a, m₄a, g₄a, rd₄a, wr₄a, sp₄a, -, f₄a⟩ := stSlot_ok s₃ .r1 sb (k := dSlot) base₃ (by decide) hwS₃
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₄a .r2 sb (k := nSlot) (by rw [g₄a, base₃])
    (by decide) (by rw [wr₄a]; exact hwS₃)
  obtain r1₃ : s₃.gpr .r1 = A := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), r1₀]
  obtain r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.np]
  obtain fs : Frame [⟨wordAddr b dSlot, 4⟩, ⟨wordAddr b nSlot, 4⟩] s₃.mem s₄.mem :=
    (f₄a.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₄.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  obtain hsub : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      Region.Sub r ⟨State.addr b, 4 * slots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slot_sub hfit' (by decide)
    · exact slot_sub hfit' (by decide)
  obtain dsTab : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      (slotsRegion b tableSlot dSlot).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)] <;>
      exact VG.Offset.disjoint _ (by (try simp only [tableSlot_eq, dSlot_eq, nSlot_eq]); omega_arith)
        (by (try simp only [tableSlot_eq, dSlot_eq]); omega_arith) (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)
  obtain sc₄ : ScrOk s₀ b E s₄.mem := sc₃.frame hfit' fs dsTab
  obtain base₄ : s₄.gpr sb = b := by rw [g₄, g₄a, base₃]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₄a, wr₃]
  obtain dp₄ : s₄.mem.readW (wordAddr b dSlot) 32 = A := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide), m₄a,
      readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, r1₃]
  obtain np₄ : s₄.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 v := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, g₄a, r2₃]
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([stS dSlot .r1, stS nSlot .r2] : List Instr) =
      [.str .r1 sb (4 * dSlot)] ++ [.str .r2 sb (4 * nSlot)] from rfl, runBlock_app, e₄a, Option.bind_some, e₄],
    ?_⟩))
  -- The eight blocks.
  obtain hkey : KeyCtx s₄ E :=
    { scr := by rw [base₄, wr₄']; exact hwS.mem
      fit := by rw [base₄]; exact hfit'
      keys := fun e he => by rw [base₄]; exact sc₄.keys e he }
  refine WP.seq (WP.mono (crypt8_wp hkey) fun s₅ ⟨c₅, b₅⟩ => ?_)
  obtain base₅ : s₅.gpr sb = b := by rw [c₅.base, base₄]
  obtain f₅ : Frame [⟨State.addr b, 4 * tableSlot⟩] s₄.mem s₅.mem := by have := c₅.frame; rw [base₄] at this; exact this
  obtain keep₅ : ∀ j, tableSlot ≤ j → j < slots → s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => slot_keep hfit' (Nat.le_refl _) f₅
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTab) h1 h2
  obtain sc₅ : ScrOk s₀ b E s₅.mem := sc₄.frame hfit' f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dTab.sub_left subTab
  obtain wr₅ : s₅.wr = s.wr := by rw [c₅.wr, wr₄']
  obtain rd₅ : s₅.rd = s.rd := by rw [c₅.rd, rd₄, rd₄a, rd₃]
  obtain sp₅ : s₅.sp = s.sp := by rw [c₅.sp, sp₄, sp₄a, sp₃]
  obtain hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  -- The data pointer and the blocks left back.
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a, sp₆a⟩ := ldSlot_ok s₅ .r1 sb (k := dSlot) base₅ (by decide) hwS₅
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := ldSlot_ok s₆a .r2 sb (k := nSlot)
    (by rw [o₆a _ (by decide), base₅]) (by decide) (by rw [wr₆a]; exact hwS₅)
  refine WP.of_runBlock ⟨s₆, by
    rw [show ([ldS .r1 dSlot, ldS .r2 nSlot] : List Instr) =
      [.ldr .r1 sb (4 * dSlot)] ++ [.ldr .r2 sb (4 * nSlot)] from rfl, runBlock_app, e₆a, Option.bind_some, e₆],
    ?_⟩
  obtain r1₆ : s₆.gpr .r1 = A := by rw [o₆ _ (by decide), r₆a, keep₅ _ (by decide) (by decide), dp₄]
  obtain r2₆ : s₆.gpr .r2 = BitVec.ofNat 32 v := by rw [r₆, m₆a, keep₅ _ (by decide) (by decide), np₄]
  obtain base₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₆a _ (by decide), base₅]
  obtain mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆a]
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆a, wr₅]
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆a, rd₅]
  obtain sp₆' : s₆.sp = s.sp := by rw [sp₆, sp₆a, sp₅]
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r2₆ hv) fun s₇ ⟨r3₇, o₇, m₇, rd₇, wr₇, sp₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a, sp₈a⟩ := addImm_ok s₇ .r0 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈, sp₈⟩ := movR_ok s₈a .r12 .r1
  obtain mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈a, m₇, mem₆]
  obtain g₈ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₈.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₈ r h12, o₈a r h0, o₇ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [show ([tailAddr .r0, movR .r12 .r1] : List Instr) =
      [.dp .add .r0 sb (.imm (BitVec.ofNat 32 (4 * tailSlot)))] ++ [movR .r12 .r1] from rfl,
      runBlock_app, e₈a, Option.bind_some]; exact e₈, ?_⟩)
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈a, rd₇, rd₆']
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈a, wr₇, wr₆']
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₈', wr₈']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₈']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₈ _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₆]; simp [T],
      by rw [r₈, o₈a _ (by decide), o₇ _ (by decide) (by decide), r1₆]; simp [A],
      by rw [o₈ _ (by decide), o₈a _ (by decide), r3₇, Nat.sub_zero], ⟨fun t ht => by omega_arith, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₉ h₉ => ?_
  obtain f₉ : Frame [⟨State.addr A, 16 * c⟩] s₅.mem s₉.mem := by rw [← mem₈]; exact h₉.cp.frame
  obtain g₉ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₉.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₉.regs r h0 h12 h3 h4, g₈ r h0 h12 h3 h4]
  obtain sc₉ : ScrOk s₀ b E s₉.mem := sc₅.frame hfit' f₉ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dA.sub_left subTab
  obtain wr₉ : s₉.wr = s.wr := by rw [h₉.wr, wr₈']
  obtain rd₉ : s₉.rd = s.rd := by rw [h₉.rd, rd₈']
  obtain sp₉ : s₉.sp = s.sp := by rw [h₉.sp, sp₈, sp₈a, sp₇, sp₆']
  -- The blocks the eight-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, tailBlock s₄ j =
      Spec.Sm4.blockAt s₀.mem (State.addr D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega_arith)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    obtain hout : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
        ¬ r.Contains (State.addr b + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, dSlot_eq, nSlot_eq]); omega_arith)
          (by rw [tailSlot_eq]; omega_arith) (by omega_arith) (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)
    rw [base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega_arith,
      fs _ hout, this, mem₂, hi.data _ (by omega_arith), ite_eq_right (by omega_arith), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₉.mem (State.addr D) n (8 * k + c) (outF s₀.mem (State.addr D) E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : State.addr D + BitVec.ofNat 64 i = State.addr A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, h₉.cp.copied _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : State.addr T + BitVec.ofNat 64 (i - 128 * k) =
          State.addr (s₅.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [base₅, hT, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨State.addr A, 16 * c⟩ : Region)], ¬ r.Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hA]
          exact not_contains_off _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [f₉ _ hout,
        f₅.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        fs.bytes (R := ⟨State.addr D, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hin,
        f₃.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  obtain fr₉ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s.mem s₉.mem := by
    refine ((f₃.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((fs.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩).trans
      ((f₅.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₉.sub fun r hr => ⟨⟨State.addr D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  -- On to the next group.
  obtain r2₉ : s₉.gpr .r2 = BitVec.ofNat 32 v := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), r2₆]
  unfold advance
  refine WP.seq (WP.mono (groupCount_wp r2₉ hv) fun s₁₀ ⟨r3₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀, sp₁₀⟩ => ?_)
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁, sp₁₁⟩ := addImm_ok s₁₀ .r1 .r1 128 (by decide)
  obtain ⟨s₁₂, e₁₂, r₁₂, z₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂, sp₁₂⟩ := subsR_ok s₁₁ .r2 .r2 .r3
  refine WP.of_runBlock ⟨s₁₂, by
    rw [show ([.dp .add .r1 .r1 (.imm 128), .subs .r2 .r2 (.reg .r3)] : List Instr) =
      [.dp .add .r1 .r1 (.imm 128)] ++ [.subs .r2 .r2 (.reg .r3)] from rfl,
      runBlock_app, e₁₁, Option.bind_some, e₁₂], ?_⟩
  obtain zz : s₁₂.z = decide (v = c) := by
    rw [z₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
      ofNat32_sub_beq (by omega_arith) (by omega_arith)]
  obtain hmem : s₁₂.mem = s₉.mem := by rw [m₁₂, m₁₁, m₁₀]
  obtain base₁₂ : s₁₂.gpr sb = b := by
    rw [o₁₂ _ (by decide), o₁₁ _ (by decide), o₁₀ _ (by decide) (by decide),
      g₉ _ (by decide) (by decide) (by decide) (by decide), base₆]
  obtain rd₁₂' : s₁₂.rd = s₀.rd := by rw [rd₁₂, rd₁₁, rd₁₀, rd₉, hi.rd]
  obtain wr₁₂' : s₁₂.wr = s₀.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₉, hi.wr]
  obtain sp₁₂' : s₁₂.sp = s₀.sp := by rw [sp₁₂, sp₁₁, sp₁₀, sp₉, hi.sp]
  obtain fr : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₁₂.mem := by
    rw [hmem]; exact hi.frame.trans fr₉
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [zz]; simp; omega_arith, base₁₂, hmem ▸ sc₉, by have := hmem ▸ hdata; rwa [hn] at this, fr,
      rd₁₂', wr₁₂', sp₁₂'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨by rw [zz]; simp; omega_arith, base₁₂, ?_, ?_, by omega_arith, hmem ▸ sc₉,
      by rw [hmem, show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata, fr, rd₁₂', wr₁₂', sp₁₂'⟩
    · rw [o₁₂ _ (by decide), r₁₁, o₁₀ _ (by decide) (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide),
        r1₆]
      simp only [A]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [r₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
        VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - c = n - 8 * (k + 1) by omega_arith]

end VG.Proof.Sm4.Arm
