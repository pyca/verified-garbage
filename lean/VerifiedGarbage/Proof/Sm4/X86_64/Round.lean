module

public import VerifiedGarbage.Proof.Sm4.Bitsliced
public import VerifiedGarbage.Proof.Camellia.X86_64.Linear
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
public import VerifiedGarbage.Impl.Sm4.X86_64.Layers
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Sm4.X86_64.Sbox
public import VerifiedGarbage.Proof.Sm4.SboxTable
public import VerifiedGarbage.Proof.Framework.X86_64.Straight
public import VerifiedGarbage.Proof.Aes.Bitsliced
public import VerifiedGarbage.Proof.Sm4.Rounds
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Sm4.X86_64.Linear`, which only this module used -/

section

/-!
# The linear layers of bitsliced SM4 on x86-64, by evaluation

Each linear block is checked by evaluation over the lane domain
(`Framework/X86_64/Linear.lean`, through Camellia's `linG_ok`): the kernel
runs it on its input words as atoms and compares every output bit with the
XOR of input bits given here.

* A round's input (`preX`): the state's planes (slots 64–95) are input
  words `0 … 31`, the round keys' planes at `kp` words `32 …`.
* A round's linear layer (`lin`): the S-box's output in the state
  registers is input words `0 … 7`, the state's planes words `8 … 39`.
* The transposes (`toBs`, `fromBs`): the tail buffer's sixteen blocks
  (slots 96–127) are input words `0 … 31`; the state's planes are.
* A round key's planes (`keyLoad`): the schedule's word at `rdi` is input
  word `0`.

Position `p = 16 i + b` of a plane is byte `i` (from the most significant)
of the word of block `b`.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 at_ slotAt)
open VG.Proof.Camellia.X86_64 (linEnvG linPostG)
open VG.Proof.Sm4 (rotP)
open VG.Impl.Sm4 (Lin)

/-- The registers `q 0 … q 7` hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

def keyMaskSlots : List Nat := keyMasks.map (·.1)

/-! ## A round -/

/-- The slots below the table; the round keys' 32 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := tableSlot, ext := kp, exts := 32 }

/-- The state's planes, from input word `x`: plane `j` of word `w` is
input word `x + 8 w + j`. -/
def stateIns (x : Nat) : List (Nat × Nat) := (List.range 32).map fun k => (64 + k, x + k)

def stateSlots : List Nat := (List.range 32).map (64 + ·)

def preEnv : Env (Nat × Nat) := linEnvG [] (stateIns 0) keyMasks

/-- `preX e b c d`: plane `j` of `X_b ⊕ X_c ⊕ X_d ⊕ rk`, the round key at
entry `e` of `kp`. -/
def preG (e b c d j p : Nat) : List Nat :=
  [64 * (8 * b + j) + p, 64 * (8 * c + j) + p, 64 * (8 * d + j) + p, 64 * (32 + 8 * e + j) + p]

theorem pre0_check :
    check (lanes 64 12) layerCfg (linExt 32) (preX 0 1 2 3) preEnv
      (linPostG 12 (qOuts (preG 0 1 2 3)) [] (keyMaskSlots ++ stateSlots) preEnv) = true := by
  decide +kernel

theorem pre1_check :
    check (lanes 64 12) layerCfg (linExt 32) (preX 1 2 3 0) preEnv
      (linPostG 12 (qOuts (preG 1 2 3 0)) [] (keyMaskSlots ++ stateSlots) preEnv) = true := by
  decide +kernel

theorem pre2_check :
    check (lanes 64 12) layerCfg (linExt 32) (preX 2 3 0 1) preEnv
      (linPostG 12 (qOuts (preG 2 3 0 1)) [] (keyMaskSlots ++ stateSlots) preEnv) = true := by
  decide +kernel

theorem pre3_check :
    check (lanes 64 12) layerCfg (linExt 32) (preX 3 0 1 2) preEnv
      (linPostG 12 (qOuts (preG 3 0 1 2)) [] (keyMaskSlots ++ stateSlots) preEnv) = true := by
  decide +kernel

/-- The slots below the table, without the round keys. -/
def linCfg : Cfg := { base := sb, slots := tableSlot, ext := kp, exts := 0 }

def linEnv : Env (Nat × Nat) := linEnvG qIns (stateIns 8) keyMasks

/-- Plane `j` of the state's word `a`, XOR the linear layer of the S-box's output. -/
def linG (l : Lin) (a j p : Nat) : List Nat :=
  (64 * (8 + 8 * a + j) + p) :: (l.terms j).map fun sm => 64 * sm.1 + rotP p sm.2

/-- The state's planes but word `a`'s, and the masks. -/
def linKeep (a : Nat) : List Nat :=
  keyMaskSlots ++ ((List.range 32).filter (· / 8 != a)).map (64 + ·)

def linOuts (l : Lin) (a : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map fun j => (stateSlot a j, linG l a j)

/-- `linG` written out, without `List.map`, whose evaluation by the kernel
costs most of a check that evaluates `linG` at every bit of every output
(`linOuts_eq_flat`). -/
def linGFlat : Lin → Nat → Nat → Nat → List Nat
  | .enc, a, j, p =>
    if 2 ≤ j then
      [64 * (8 + 8 * a + j) + p, 64 * j + rotP p 0, 64 * j + rotP p 3, 64 * (j - 2) + rotP p 0,
        64 * (j - 2) + rotP p 1, 64 * (j - 2) + rotP p 2]
    else
      [64 * (8 + 8 * a + j) + p, 64 * j + rotP p 0, 64 * j + rotP p 3, 64 * (j + 6) + rotP p 1,
        64 * (j + 6) + rotP p 2, 64 * (j + 6) + rotP p 3]
  | .key, a, j, p =>
    [64 * (8 + 8 * a + j) + p, 64 * j + rotP p 0,
      if 5 ≤ j then 64 * (j - 5) + rotP p 1 else 64 * (j + 3) + rotP p 2,
      if j = 7 then 64 * 0 + rotP p 2 else 64 * (j + 1) + rotP p 3]

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
    check (lanes 64 12) linCfg (linExt 40) (lin .enc 0) linEnv
      (linPostG 12 [] (linOuts .enc 0) (linKeep 0) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linE1_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .enc 1) linEnv
      (linPostG 12 [] (linOuts .enc 1) (linKeep 1) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linE2_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .enc 2) linEnv
      (linPostG 12 [] (linOuts .enc 2) (linKeep 2) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linE3_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .enc 3) linEnv
      (linPostG 12 [] (linOuts .enc 3) (linKeep 3) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK0_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .key 0) linEnv
      (linPostG 12 [] (linOuts .key 0) (linKeep 0) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK1_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .key 1) linEnv
      (linPostG 12 [] (linOuts .key 1) (linKeep 1) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK2_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .key 2) linEnv
      (linPostG 12 [] (linOuts .key 2) (linKeep 2) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK3_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .key 3) linEnv
      (linPostG 12 [] (linOuts .key 3) (linKeep 3) linEnv) = true := by
  rw [linOuts_eq_flat]; decide +kernel

/-! ## The transposes -/

/-- The slots below the table, without external words. -/
def bsCfg : Cfg := { base := sb, slots := tableSlot, ext := sb, exts := 0 }

/-- The tail buffer's 32 words are input words `0 … 31`. -/
def tailIns : List (Nat × Nat) := (List.range 32).map fun k => (tailSlot + k, k)

def toBsEnv : Env (Nat × Nat) := linEnvG [] tailIns keyMasks

/-- Plane `j` of the state's word `w`, at `p = 16 i + b`: bit `j` of byte
`4 (w mod 2) + i` of the tail buffer's word `2 b + ⌊w / 2⌋`. -/
def toBsG (w j p : Nat) : List Nat := [64 * (2 * (p % 16) + w / 2) + 8 * (4 * (w % 2) + p / 16) + j]

def toBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => (64 + k, toBsG (k / 8) (k % 8))

theorem toBs_check :
    check (lanes 64 11) bsCfg (linExt 0) toBs toBsEnv
      (linPostG 11 [] toBsOuts keyMaskSlots toBsEnv) = true := by
  lit_decide

def fromBsEnv : Env (Nat × Nat) := linEnvG [] (stateIns 0) keyMasks

/-- Bit `8 β + j` of the tail buffer's word `t = 2 b + h`, byte `8 h + β`
of block `b`, word `w' = 2 h + ⌊β / 4⌋`: plane `j` of the state's word
`3 - w'` at byte `β mod 4`. -/
def fromBsG (t k : Nat) : List Nat :=
  [64 * (8 * (3 - (2 * (t % 2) + k / 32)) + k % 8) + 16 * (k / 8 % 4) + t / 2]

def fromBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun t => (tailSlot + t, fromBsG t)

theorem fromBs_check :
    check (lanes 64 11) bsCfg (linExt 0) fromBs fromBsEnv
      (linPostG 11 [] fromBsOuts (keyMaskSlots ++ stateSlots) fromBsEnv) = true := by
  lit_decide

/-! ## The round keys' planes -/

/-- The masks' slots; the schedule's word at `rdi`. -/
def keyCfg : Cfg := { base := sb, slots := 64, ext := .rdi, exts := 1 }

def keyEnv : Env (Nat × Nat) := linEnvG [] [] keyMasks

/-- Plane `j` of round key `2 m + h`: bit `16 i + b` is bit `j` of its byte
`i` from the most significant, bits `32 h + 8 (3 - i) + j` of the word. -/
def keyBsG (h j p : Nat) : List Nat := [32 * h + 8 * (3 - p / 16) + j]

theorem keyLoad0_check :
    check (lanes 64 7) keyCfg (linExt 0) (keyLoad 0) keyEnv
      (linPostG 7 (qOuts (keyBsG 0)) [] keyMaskSlots keyEnv) = true := by
  decide +kernel

theorem keyLoad1_check :
    check (lanes 64 7) keyCfg (linExt 0) (keyLoad 1) keyEnv
      (linPostG 7 (qOuts (keyBsG 1)) [] keyMaskSlots keyEnv) = true := by
  decide +kernel

/-- The entry at `rsi`. -/
def entryCfg : Cfg := { base := .rsi, slots := 8, ext := .rsi, exts := 0 }

def entryEnv : Env (Nat × Nat) := linEnvG qIns [] []

theorem keyStore_check :
    check (lanes 64 9) entryCfg (linExt 0) keyStore entryEnv
      (linPostG 9 [] ((List.range 8).map fun j => (j, fun p => [64 * j + p])) [] entryEnv) = true := by
  decide +kernel

end VG.Proof.Sm4.X86_64

end

end

/-! ### `Sm4.X86_64.Sbox`, which only this module used -/

section

/-!
# The bitsliced SM4 S-box on x86-64

`sboxCode` only combines words bitwise, so it computes the same Boolean
function at each of the 64 bit positions: the kernel evaluates it once on
truth tables of the 256 inputs (`Bitslice.table`) and compares the result
with the specification's S-box on the same inputs. `sbox_ok` then gives,
at every bit position `p`, the S-box of the byte formed by bit `p` of the
eight words.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4
open VG.Proof.Aes (bsByte getLsbD_bsByte)

/-- The S-box's memory: its spill slots, at `r9`. -/
def sboxCfg : Cfg := { base := sb, slots := 48, ext := sb, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some (sboxT j)

theorem sbox_check :
    check (table 64 256) sboxCfg (fun _ => none) Impl.Sm4.X86_64.sboxCode sboxEnv sboxPost = true := by
  lit_decide

/-- The registers the S-box writes. -/
def sboxWrites : List Reg := [q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, t0, t1]

theorem sbox_writes_rest :
    [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all
      (fun r => Impl.Sm4.X86_64.sboxCode.all fun i => i.dst != some r) = true := by
  decide +kernel

theorem not_sboxWrites (r : Reg) (hr : r ∉ sboxWrites) :
    r ∈ [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9] := by
  revert hr; cases r <;> decide

theorem sbox_writes (r : Reg) (hr : r ∉ sboxWrites) :
    (Impl.Sm4.X86_64.sboxCode.all fun i => i.dst != some r) = true :=
  List.all_eq_true.mp sbox_writes_rest r (not_sboxWrites r hr)

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa Impl.Sm4.X86_64.sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (sboxB (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some (sboxT j) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 64, ∃ s', runBlock isa Impl.Sm4.X86_64.sboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (Impl.Sm4.X86_64.sboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_using [])
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, sboxT, testBit_tableOf]
    simp [hc, sboxN_eq hc, BitVec.testBit_toNat]
  · simp [sbox_writes r hr]

end VG.Proof.Sm4.X86_64

end

end


/-!
# A round of bitsliced SM4 on x86-64

`round_ok`: with the state's four words in their slots (`StRel`) and the
round key's planes at entry `a` of `kp`, `round l a a b c d` (the other words
`b`, `c`, `d` the next ones, cyclically) replaces word `a` of every block's
state with its new value (`sround`), keeping the other words and the masks,
and writing only the slots below the table. The layers are composed from
their checks (`Linear.lean`, `Sbox.lean`) and `round_rel`.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1)
open VG.Proof.Camellia.X86_64 (linEnvG linPostG linG_ok)
open VG.Proof.Sm4 (WordRel rotP round_rel sround)
open VG.Impl.Sm4 (Lin)
open VG.Proof.Aes (bsByte termsXor xorBits_map)

/-- The planes in the state registers. -/
abbrev Qs (s : State) (i : Nat) : BitVec 64 := s.gpr (q i)

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr sb) k) 64

/-- Word `k` of the table entries at `kp`. -/
abbrev keyW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr kp) k) 64

/-- The masks are in their slots. -/
def MasksOk (s : State) : Prop := ∀ kv ∈ keyMasks, slotW s kv.1 = kv.2

/-- The planes of the state's word `w`. -/
def planes (s : State) (w : Nat) : Nat → BitVec 64 := fun j => slotW s (stateSlot w j)

/-- The state's words hold the blocks' states: word `w` of block `b` is `X b w`. -/
def StRel (s : State) (X : Nat → Nat → Spec.Sm4.Word) : Prop :=
  ∀ w < 4, WordRel (planes s w) (fun b => X b w)

theorem mask_lt {kv : Nat × BitVec 64} (hkv : kv ∈ keyMasks) : kv.1 < 64 := by
  simp [keyMasks] at hkv; rcases hkv with h | h | h <;> subst h <;> simp [evenSlot, oddSlot, grpSlot]

theorem ok_sbox {s : State} (h : Ok layerCfg s) : Ok sboxCfg s where
  slotIn k hk := h.slotIn k (by simp [sboxCfg, layerCfg, tableSlot] at hk ⊢; omega_using [hk])
  extIn k hk := by simp [sboxCfg] at hk
  slots := by simp [sboxCfg]
  sep k _ j hj := by simp [sboxCfg] at hj

/-- The frame of the S-box (its spills) keeps the slots from 48 on. -/
theorem slot_above {m m' : Mem} {b : Addr} {n k : Nat} (hf : Frame [⟨b, 8 * n⟩] m m') (hk : n ≤ k)
    (hk' : k < 2 ^ 58) : m'.readW (wordAddr b k) 64 = m.readW (wordAddr b k) 64 :=
  hf.readW (r := ⟨wordAddr b k, 8⟩) (by simp only [Region.Contains]; simp) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base b (by omega_using [hk]) (by omega_using [hk'])) (by decide)

theorem stateIns_mem {x j i : Nat} (h : (j, i) ∈ stateIns x) : ∃ k < 32, j = 64 + k ∧ i = x + k := by
  simp only [stateIns, List.mem_map, List.mem_range, Prod.mk.injEq] at h
  obtain ⟨k, hk, rfl, rfl⟩ := h
  exact ⟨k, hk, rfl, rfl⟩

theorem masks_in {s : State} (hm : MasksOk s) : ∀ kv ∈ keyMasks, kv.1 < layerCfg.slots ∧
    s.mem.readW (wordAddr (s.gpr layerCfg.base) kv.1) 64 = kv.2 := fun kv hkv =>
  ⟨by have := mask_lt hkv; simp only [layerCfg, tableSlot]; omega_using [this], hm kv hkv⟩

theorem planes_eq (s : State) (w j : Nat) : planes s w j = slotW s (64 + (8 * w + j)) := by
  simp only [planes, stateSlot, Nat.add_assoc]

theorem termsXor_congr {W S : Nat → BitVec 64} (hS : ∀ i < 8, W i = S i) :
    ∀ l : List (Nat × Nat), (∀ wt ∈ l, wt.1 < 8) → termsXor W l = termsXor S l
  | [], _ => rfl
  | wt :: l, h => by
    have ih := termsXor_congr hS l fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [termsXor, List.foldr_cons] at ih ⊢
    rw [hS wt.1 (h wt List.mem_cons_self), ih]

/-- The linear layer's terms, as the bits of the S-box's output. -/
theorem xorBits_terms (W S : Nat → BitVec 64) (hS : ∀ i < 8, W i = S i) (l : List (Nat × Nat))
    (hl : ∀ sm ∈ l, sm.1 < 8) (p : Nat) :
    xorBits W (l.map fun sm => 64 * sm.1 + rotP p sm.2) =
      termsXor S (l.map fun sm => (sm.1, rotP p sm.2)) := by
  rw [show (l.map fun sm => 64 * sm.1 + rotP p sm.2) =
      ((l.map fun sm => (sm.1, rotP p sm.2)).map fun wt => 64 * wt.1 + wt.2) by simp,
    xorBits_map W _ (fun wt hwt => by
      simp only [List.mem_map] at hwt; obtain ⟨sm, _, rfl⟩ := hwt; exact Nat.mod_lt _ (by decide))]
  exact termsXor_congr hS _ fun wt hwt => by
    simp only [List.mem_map] at hwt; obtain ⟨sm, hsm, rfl⟩ := hwt; exact hl sm hsm

theorem ok_lin {s : State} (h : Ok layerCfg s) : Ok linCfg s where
  slotIn k hk := h.slotIn k (by simpa [linCfg, layerCfg] using hk)
  extIn k hk := by simp [linCfg] at hk
  slots := by simp [linCfg, tableSlot]
  sep k _ j hj := by simp [linCfg] at hj

theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- A round, with the round key at entry `a` of `kp`. -/
theorem round_ok (l : Lin) {a b c d : Nat} (ha : a < 4)
    (hb : b = (a + 1) % 4) (hc : c = (a + 2) % 4) (hd : d = (a + 3) % 4)
    (hpre : check (lanes 64 12) layerCfg (linExt 32) (preX a b c d) preEnv
      (linPostG 12 (qOuts (preG a b c d)) [] (keyMaskSlots ++ stateSlots) preEnv) = true)
    (hlin : check (lanes 64 12) linCfg (linExt 40) (lin l a) linEnv
      (linPostG 12 [] (linOuts l a) (linKeep a) linEnv) = true)
    (hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r =>
      (preX a b c d ++ lin l a).all fun i => i.dst != some r) = true)
    {s : State} (hok : Ok layerCfg s) (hm : MasksOk s) {X : Nat → Nat → Spec.Sm4.Word} {k : Spec.Sm4.Word}
    (hX : StRel s X) (hK : WordRel (fun j => keyW s (8 * a + j)) fun _ => k) :
    ∃ s', runBlock isa (round l a a b c d) s = some s' ∧
      StRel s' (fun b' => sround l k a (X b')) ∧ MasksOk s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  have hall' : ∀ r, r ∉ sboxWrites → ((preX a b c d).all fun i => i.dst != some r) = true ∧
      ((lin l a).all fun i => i.dst != some r) = true := fun r hr => by
    have := List.all_eq_true.mp hall r (not_sboxWrites r hr)
    rw [List.all_append, Bool.and_eq_true] at this
    exact this
  have hsb : sb ∉ sboxWrites := by decide
  have hkp : kp ∉ sboxWrites := by decide
  -- The S-box's input.
  let W₁ : Nat → BitVec 64 := fun i => if i < 32 then slotW s (64 + i) else keyW s (i - 32)
  obtain ⟨s₁, h₁, x₁, -, k₁, rd₁, wr₁, o₁, f₁, -, -⟩ := linG_ok hpre hok W₁
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [layerCfg, tableSlot]; omega_arith, by omega_arith, by simp [W₁, hk]; rfl⟩)
    (masks_in hm)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₁, show ¬ 32 + j < 32 by omega_arith]; rfl⟩)
  have b₁ : s₁.gpr sb = s.gpr sb := o₁ _ (hall' sb hsb).1
  have kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (hall' kp hkp).1
  have hW₁ : ∀ w < 4, ∀ j < 8, W₁ (8 * w + j) = planes s w j := fun w hw j hj => by
    simp only [W₁, show 8 * w + j < 32 by omega_arith, ↓reduceIte, planes_eq]
  have hXb : ∀ j < 8, ∀ p < 64, (Qs s₁ j).getLsbD p =
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
  have keep₁ : ∀ k ∈ keyMaskSlots ++ stateSlots, slotW s₁ k = slotW s k := fun k hk => by
    have hk' : k < layerCfg.slots := by
      simp only [keyMaskSlots, stateSlots, keyMasks, List.mem_append, List.mem_map, List.mem_range,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
      simp only [layerCfg, tableSlot]
      rcases hk with ((h | h | h) | ⟨x, hx, rfl⟩) <;> (try subst h) <;> (try simp only [evenSlot, oddSlot, grpSlot]) <;> omega_arith
    have := k₁ k hk hk'
    simp only [layerCfg] at this
    rw [slotW, b₁, this]
  -- The S-box.
  obtain ⟨s₂, h₂, sx₂, rd₂, wr₂, o₂, f₂⟩ := sbox_ok (ok_sbox hok₁)
  have b₂ : s₂.gpr sb = s.gpr sb := (o₂ sb hsb).trans b₁
  have kp₂ : s₂.gpr kp = s.gpr kp := (o₂ kp hkp).trans kp₁
  have hok₂ : Ok layerCfg s₂ := hok₁.congr (o₂ sb hsb) (o₂ kp hkp) rd₂ wr₂
  have above₂ : ∀ k, 48 ≤ k → k < tableSlot → slotW s₂ k = slotW s₁ k := fun k h1 h2 => by
    simp only [slotW, o₂ sb hsb]
    exact slot_above (n := 48) f₂ h1 (by simp [tableSlot] at h2; omega_arith)
  have keep₂ : ∀ k ∈ keyMaskSlots ++ stateSlots, slotW s₂ k = slotW s k := fun k hk => by
    have hk' : 48 ≤ k ∧ k < tableSlot := by
      simp only [keyMaskSlots, stateSlots, keyMasks, List.mem_append, List.mem_map, List.mem_range,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with ((h | h | h) | ⟨x, hx, rfl⟩) <;> (try subst h) <;> (try simp only [evenSlot, oddSlot, grpSlot, tableSlot]) <;> omega_arith
    rw [above₂ k hk'.1 hk'.2, keep₁ k hk]
  have hm₂ : MasksOk s₂ := fun kv hkv => by
    rw [keep₂ kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv))]; exact hm kv hkv
  have hst₂ : ∀ w < 4, ∀ j < 8, slotW s₂ (64 + (8 * w + j)) = planes s w j := fun w hw j hj => by
    rw [keep₂ _ (List.mem_append_right _ (by
      simp only [stateSlots, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega_arith, rfl⟩)), planes_eq]
  -- The linear layer, into word `a`.
  let W₃ : Nat → BitVec 64 := fun i => if i < 8 then Qs s₂ i else slotW s₂ (64 + (i - 8))
  obtain ⟨s₃, h₃, -, y₃, k₃, rd₃, wr₃, o₃, f₃, -, -⟩ := linG_ok hlin (ok_lin hok₂) W₃
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, by simp [W₃, hi]⟩)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [linCfg, tableSlot]; omega_arith, by omega_arith, by
        simp [W₃, show ¬ 8 + k < 8 by omega_arith]; rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [linCfg, tableSlot]; omega_arith, hm₂ kv hkv⟩)
    (fun j hj => by simp [linCfg] at hj)
  have b₃ : s₃.gpr sb = s.gpr sb := (o₃ _ ((hall' sb hsb).2)).trans b₂
  have hA' : ∀ j < 8, ∀ p < 64, (planes s₃ a j).getLsbD p =
      ((planes s a j).getLsbD p ^^ termsXor (Qs s₂) ((l.terms j).map fun sm => (sm.1, rotP p sm.2))) := by
    intro j hj p hp
    have := y₃ (stateSlot a j) (linG l a j) (by simp only [linOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      (by simp [stateSlot, linCfg, tableSlot]; omega_arith) p hp
    simp only [linCfg] at this
    rw [planes, slotW, b₃, ← b₂, this, linG, xorBits_cons, bitOf_word _ _ _ hp,
      xorBits_terms W₃ (Qs s₂) (fun i hi => by simp [W₃, hi]) _ (Proof.Sm4.terms_lt l j hj)]
    simp only [W₃, show ¬ 8 + 8 * a + j < 8 by omega_arith, ↓reduceIte, show 64 + (8 + 8 * a + j - 8) = 64 + (8 * a + j) by omega_arith,
      hst₂ a ha j hj]
  have keep₃ : ∀ k ∈ linKeep a, slotW s₃ k = slotW s₂ k := fun k hk => by
    have hk' : k < linCfg.slots := by
      simp only [linKeep, keyMaskSlots, keyMasks, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
      simp only [linCfg, tableSlot]
      rcases hk with ((h | h | h) | ⟨x, ⟨hx, -⟩, rfl⟩) <;> (try subst h) <;> (try simp only [evenSlot, oddSlot, grpSlot]) <;> omega_arith
    have := k₃ k hk hk'
    simp only [linCfg] at this
    rw [slotW, b₃, ← b₂, this]
  refine ⟨s₃, ?_, fun w hw => ?_, fun kv hkv => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fun r hr => ?_, ?_⟩
  · rw [round, runBlock_app, runBlock_app, h₁, Option.bind_some, h₂, Option.bind_some, h₃]
  · by_cases hwa : w = a
    · subst hwa
      have hr := round_rel l (hX b (by omega_arith)) (hX c (by omega_arith)) (hX d (by omega_arith)) hK (hX w hw) hXb sx₂ hA'
      refine hr.congr_right fun b' _ => ?_
      simp only [sround, ↓reduceIte, hb, hc, hd]
    · refine (hX w hw).congr (fun j hj => ?_) |>.congr_right fun b' _ => by simp only [sround, hwa, ↓reduceIte]
      show planes s₃ w j = planes s w j
      rw [planes_eq, planes_eq, keep₃ _ (List.mem_append_right _ (by
        simp only [List.mem_map, List.mem_filter, List.mem_range]
        exact ⟨8 * w + j, ⟨by omega_arith, by simp; omega_arith⟩, rfl⟩)), hst₂ w hw j hj, planes_eq]
  · rw [keep₃ kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv))]; exact hm₂ kv hkv
  · rw [o₃ r (hall' r hr).2, o₂ r hr, o₁ r (hall' r hr).1]
  · have e₁ : slotRegion layerCfg s₁ = slotRegion layerCfg s := by simp only [slotRegion, layerCfg, b₁]
    have e₂ : slotRegion linCfg s₂ = slotRegion layerCfg s := by simp only [slotRegion, linCfg, layerCfg, b₂]
    refine f₁.trans ((f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans (e₂ ▸ f₃))
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, sboxCfg, layerCfg, b₁]
    exact Region.sub_prefix (by simp [tableSlot])

end VG.Proof.Sm4.X86_64
