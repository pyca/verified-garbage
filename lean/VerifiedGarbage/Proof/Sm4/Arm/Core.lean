module

public import VerifiedGarbage.Proof.Sm4.Bitsliced32
public import VerifiedGarbage.Proof.Sm4.Arm.LinG
import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
public import VerifiedGarbage.Impl.Sm4.Arm.Layers
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Sm4.Arm.Sbox
public import VerifiedGarbage.Proof.Framework.Arm.Straight
public import VerifiedGarbage.Proof.Sm4.Rounds
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Sm4.Arm.Ecb
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith

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
