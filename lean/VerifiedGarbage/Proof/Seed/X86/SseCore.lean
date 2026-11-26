module

public import VerifiedGarbage.Proof.Framework.X86.StraightSse
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Impl.Seed.X86.Sse
public import VerifiedGarbage.Proof.Seed.G
public import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Seed.Memory
public import VerifiedGarbage.Proof.Seed.X86.AesNiWideCore
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.SymFrame

/-!
# SEED's core on x86 (32-bit) in XMM registers

`coreSpec`: the core of `Impl/Seed/X86/Sse.lean`, which enciphers sixteen
blocks at a time, is SEED, as the modes' proofs need it
(`Modes.X86.CoreSpec`), in either direction.

The kernel evaluates the straight-line pieces of the code (`StraightSse`):
the linear ones (`G`'s words to planes, its mixing with the transposes back,
and the blocks to words and back) bit by bit in the lanes domain, the
S-boxes in truth tables, on every byte and either S-box at once (`tableM`:
the mask of the S-boxes' places is the ninth variable), and a round's steps
around `G` as expressions. From these checks:

* `QW`: four slots hold a word of each of sixteen blocks;
* `g_ok`, `gCall_wp'`: `G` of sixteen words, and the call of it, which the
  key expansion uses too; `gCall_wp` in the block function's state (`At`);
* `round_wp`, `turn_wp`, `loop_wp`, `blocksIn_ok`, `blocksOut_ok`: the
  specification's rounds, on every block's words (`Q4`);
* `cryptFn_wp`, `crypt_wp`: the block function, and the core's call of it;
* `prepare_wp`: the round keys as the block function reads them (`Keys`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86.Sse

open VG VG.X86 VG.X86.StraightSse VG.Bitslice VG.Impl.Seed.X86.Sse
open VG.Spec.Seed (Word Direction)
open VG.Proof.Seed (byteOf maskOf sOf xor4 sNat)

/-! ## The kernel's checks -/

def cfg : Cfg := ⟨Impl.Modes.X86.sb, 80, kr, 4, tbr, tableName, table⟩
/-- What `G` uses. -/
def cfgG : Cfg := ⟨Impl.Modes.X86.sb, 36, kr, 0, tbr, tableName, table⟩

/-- The bit of the four words' registers that bit `p` of plane `j` is. -/
def inG (j p : Nat) : List Nat :=
  if j < 4 then [128 * (p % 4) + 4 * (p / 4) + j]
  else if p % 32 < 28 then [128 * (p % 4) + 4 * (p / 4 + 1) + (j - 4)] else []

theorem gIn_chk : check (ofDom (lanes 128 9)) cfgG (fun _ => none) gIn
    (linEnv ((List.range 4).map fun r => (gS + r, r, 0)))
    (linPost 36 9 ((List.range 8).map fun j => (j, inG j))) = true := by kernel_rfl

/-- The truth tables of 512 rows, whose constants are 1 in the rows from 256 on where bit `p` of a word
of them is. -/
def tableM (m : BitVec 128) : Dom Nat 128 :=
  { table 128 512 with const := fun v => if v = m then some (tableOf (fun c => c.testBit 8) 512) else none }

/-- The mask of the S-box. -/
def mS : BitVec 128 := tblAt Impl.Seed.X86.Sse.table oM

def sboxEnv : Env Nat :=
  { reg := fun _ => none, slot := fun k => if k < 8 then some (tableOf (fun c => c.testBit k) 512) else none }

/-- The S-boxes XORed with their constants, in the rows of `mS` and in the others. -/
def sRow (c : Nat) : Nat :=
  if c.testBit 8 then sNat false (c % 256) ^^^ 0xa9 else sNat true (c % 256) ^^^ 0x38

theorem sbox_chk : check (ofDom (tableM mS)) cfgG (fun _ => none) sboxCode sboxEnv (fun e =>
    (List.range 8).all fun j => e.slot j == some (tableOf (fun c => (sRow c).testBit j) 512)) = true := by kernel_rfl

/-- The constants of plane `j` of the S-boxes' outputs. -/
def cS8 (j : Nat) : BitVec 128 := ofBits 128 fun p => if p / 8 % 2 = 0 then (0xa9).testBit j else (0x38).testBit j

def outG (r p : Nat) : List Nat :=
  (List.range 4).filterMap fun a =>
    if (maskOf ((a + p / 8 % 4) % 4)).getLsbD (p % 8) then some (128 * (p % 8) + (8 * (4 * (p / 32) + a) + r)) else none

theorem gOut_chk : check (ofDom (lanes 128 10)) cfgG (fun _ => none) gOut
    (linEnv ((List.range 8).map fun j => (j, j, cS8 j)))
    (linPost 36 10 ((List.range 4).map fun r => (gS + r, outG r))) = true := by kernel_rfl

/-- A block of these instructions, as expressions of the slots and the external words. -/
def atomsE : Env XE := { reg := fun _ => none, slot := fun k => some (.atom k) }

def exprOk (is : List Instr) (outs : List (Nat × XE)) : Bool :=
  check exprs cfg (fun n => some (.atom (80 + n))) is atomsE fun e =>
    outs.all fun o => decide (o.1 < 80) && e.slot o.1 == some o.2

def bn (op : XBinOp) (a b : Nat) : XE := .bin op (.atom a) (.atom b)

def step1E (r ko : Nat) : List (Nat × XE) := (List.range 4).flatMap fun k =>
  [(aS + k, bn .pxor (r + k) (80 + ko)),
   (gS + k, .bin .pxor (.bin .pxor (bn .pxor (r + k) (80 + ko)) (.atom (r + 4 + k))) (.atom (81 + ko)))]
def step2E : List (Nat × XE) := (List.range 4).flatMap fun k =>
  [(cS + k, .atom (gS + k)), (gS + k, bn .paddd (gS + k) (aS + k))]
def step3E : List (Nat × XE) := (List.range 4).flatMap fun k =>
  [(dS + k, .atom (gS + k)), (gS + k, bn .paddd (gS + k) (cS + k))]
def step4E (l : Nat) : List (Nat × XE) := (List.range 4).flatMap fun k =>
  [(l + 4 + k, bn .pxor (l + 4 + k) (gS + k)), (l + k, .bin .pxor (bn .paddd (gS + k) (dS + k)) (.atom (l + k)))]

theorem steps_chk : (exprOk (step1 (arr 2) 0) (step1E (arr 2) 0) && exprOk (step1 (arr 0) 32) (step1E (arr 0) 2) &&
    exprOk step2 step2E && exprOk step3 step3E && exprOk (step4 (arr 0)) (step4E (arr 0)) &&
    exprOk (step4 (arr 2)) (step4E (arr 2))) = true := by kernel_rfl

/-- The bit of the blocks that bit `p` of slot `q` of word `k` is. -/
def inB (k q p : Nat) : List Nat :=
  [128 * (4 * q + p / 32) + (8 * (4 * k + (3 - p % 32 / 8)) + p % 8)]
theorem blocksIn_chk : check (ofDom (lanes 128 11)) cfg (fun _ => none) blocksIn
    (linEnv ((List.range 16).map fun b => (bufS + b, b, 0)))
    (linPost 80 11 ((List.range 16).map fun i => (48 + i, inB (i / 4) (i % 4)))) = true := by kernel_rfl

/-- The bit of the words that bit `p` of block `b` is. -/
def outB (b p : Nat) : List Nat :=
  [128 * (4 * ((p / 32 + 2) % 4) + b / 4) + (32 * (b % 4) + (8 * (3 - p % 32 / 8) + p % 8))]
/-- No external words. -/
def cfgO : Cfg := { cfg with exts := 0 }
theorem blocksOut_chk : check (ofDom (lanes 128 11)) cfgO (fun _ => none) blocksOut
    (linEnv ((List.range 16).map fun i => (48 + i, i, 0)))
    (linPost 80 11 ((List.range 16).map fun b => (bufS + b, outB b))) = true := by kernel_rfl

/-! ## The slots each part stores -/

def storesOk (is : List Instr) (p : Nat → Bool) : Bool := (stored cfg is).all p
theorem stores_chk : (storesOk (step1 (arr 2) 0) (fun k => 32 ≤ k && k < 40) && storesOk (step1 (arr 0) 32) (fun k => 32 ≤ k && k < 40) &&
    storesOk step2 (fun k => 32 ≤ k && k < 36 || 40 ≤ k && k < 44) &&
    storesOk step3 (fun k => 32 ≤ k && k < 36 || 44 ≤ k && k < 48) &&
    storesOk (step4 (arr 0)) (fun k => 48 ≤ k && k < 56) && storesOk (step4 (arr 2)) (fun k => 56 ≤ k && k < 64) &&
    storesOk blocksIn (fun k => 48 ≤ k && k < 64) && storesOk blocksOut (fun k => 64 ≤ k)) = true := by kernel_rfl
theorem stored_out : stored cfgO blocksOut = stored cfg blocksOut := by kernel_rfl
theorem stored_g : ((stored cfgG gIn).all (· < 8) && (stored cfgG sboxCode).all (· < 29) && (stored cfgG g).all (· != tblSlot)) = true := by kernel_rfl

/-! ## The layout -/

/-- The four slots from `d` on hold the words `x` of the sixteen blocks. -/
def QW (m : Mem) (B : BitVec 32) (d : Nat) (x : Nat → Word) : Prop :=
  ∀ r < 4, ∀ l < 4, dword (W m B (d + r)) l = x (4 * r + l)

theorem QW.congr {m m' : Mem} {B : BitVec 32} {d : Nat} {x : Nat → Word} (h : QW m B d x)
    (e : ∀ r < 4, W m' B (d + r) = W m B (d + r)) : QW m' B d x := fun r hr l hl => by
  rw [e r hr]; exact h r hr l hl

theorem QW.bit {m : Mem} {B : BitVec 32} {d : Nat} {x : Nat → Word} (h : QW m B d x) {r l t : Nat} (hr : r < 4) (hl : l < 4)
    (ht : t < 32) : (W m B (d + r)).getLsbD (32 * l + t) = (x (4 * r + l)).getLsbD t := by
  rw [bit_dword, show (32 * l + t) / 32 = l by omega_arith, show (32 * l + t) % 32 = t by omega_arith, h r hr l hl]

theorem QW.of_bits {m : Mem} {B : BitVec 32} {d : Nat} {x : Nat → Word}
    (h : ∀ r < 4, ∀ l < 4, ∀ t < 32, (W m B (d + r)).getLsbD (32 * l + t) = (x (4 * r + l)).getLsbD t) : QW m B d x :=
  fun r hr l hl => BitVec.eq_of_getLsbD_eq fun t ht => by
    rw [getLsbD_dword, decide_eq_true ht, Bool.true_and]; exact h r hr l hl t ht

/-- What every part of the block's code needs of the state, with the round
keys from the `q`th on at `kr`. -/
structure At (s₀ : State) (B : BitVec 32) (q : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  kp : s.gpr kr = B + BitVec.ofNat 32 (16 * (80 + q))
  tb : s.gpr tbr = s₀.syms tableName
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  frame : Frame [slotsR B 0 80, below (s₀.gpr .esp) 4] s₀.mem s.mem
  tab : W s.mem B tblSlot = W s₀.mem B tblSlot

section
variable {s₀ s : State} {B : BitVec 32} {q m : Nat}

theorem At.ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 80 + q + 4 ≤ m) : Ok cfg s := by
  have hf := hs.fit
  have hkr : (B + BitVec.ofNat 32 (16 * (80 + q))).toNat = B.toNat + 16 * (80 + q) :=
    Straight.toNat_add_off (by omega_arith)
  have e1 : ∀ k < 80, xAddr (s.gpr cfg.base) k = B.setWidth 64 + BitVec.ofNat 64 (16 * k) := fun k hk => by
    show addr (s.gpr Impl.Modes.X86.sb) _ = _
    rw [h.base, addr16 (by omega_arith)]
  have e2 : ∀ k < 4, xAddr (s.gpr cfg.ext) k = B.setWidth 64 + BitVec.ofNat 64 (16 * (80 + q + k)) := fun k hk => by
    show addr (s.gpr kr) _ = _
    rw [h.kp, Straight.addr_add_ofNat, ← Nat.mul_add, addr16 (by omega_arith)]
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk j hj => ?_, ?_⟩
  · have hk : k < 80 := hk
    rw [e1 k hk, h.wr, ← addr16 (by omega_arith)]
    exact hs.acc _ (by omega_arith)
  · have hk : k < 4 := hk
    rw [e2 k hk, h.rd, h.wr, ← addr16 (by omega_arith)]
    obtain ⟨r, hr, hc⟩ := hs.acc (80 + q + k) (by omega_arith)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · show (s.gpr Impl.Modes.X86.sb).toNat + 16 * 80 ≤ _
    rw [h.base]; omega_arith
  · rw [e1 k hk, e2 j hj]
    have hk : k < 80 := hk
    have hj : j < 4 := hj
    intro x h₁ h₂
    exact Offset.disjoint (B.setWidth 64) (d := 16 * k) (n := 16) (e := 16 * (80 + q + j)) (k := 16)
      (by omega_arith) (by omega_arith) (by omega_arith) x h₁ h₂
  · show s.gpr tbr = s.syms tableName
    rw [h.tb, h.syms]

theorem At.okO (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hm : 80 ≤ m) : Ok cfgO s := by
  have hf := hs.fit
  refine ⟨fun k hk => ?_, fun k hk => absurd hk (Nat.not_lt_zero _), ?_, fun k hk j hj => absurd hj (Nat.not_lt_zero _), ?_⟩
  · have hk : k < 80 := hk
    show InRegions s.wr (addr (s.gpr Impl.Modes.X86.sb) (16 * k)) 16
    rw [h.base, h.wr]
    exact hs.acc _ (by omega_arith)
  · show (s.gpr Impl.Modes.X86.sb).toNat + 16 * 80 ≤ _
    rw [h.base]; omega_arith
  · show s.gpr tbr = s.syms tableName
    rw [h.tb, h.syms]

theorem At.ext (h : At s₀ B q s) (k : Nat) :
    s.mem.readW (xAddr (s.gpr cfg.ext) k) 128 = W s.mem B (80 + q + k) := by
  show s.mem.readW (addr (s.gpr kr) _) 128 = _
  rw [h.kp, Straight.addr_add_ofNat, ← Nat.mul_add]; rfl

theorem At.slot (h : At s₀ B q s) (m : Mem) (k : Nat) :
    m.readW (xAddr (s.gpr cfg.base) k) 128 = W m B k := by
  show m.readW (addr (s.gpr Impl.Modes.X86.sb) _) 128 = _
  rw [h.base]; rfl

theorem At.kept {is : List Instr} {s' : State} (h : At s₀ B q s) (p : Runs cfg is s s') {f : Nat → Bool}
    (hst : storesOk is f = true) {k : Nat} (hk : k < 80) (hf : f k = false) : W s'.mem B k = W s.mem B k := by
  rw [← h.slot, ← h.slot]
  refine p.kept k hk fun hm => ?_
  have := List.all_eq_true.mp hst k hm
  rw [hf] at this; cases this

theorem At.runs {is : List Instr} {s' : State} (h : At s₀ B q s) (p : Runs cfg is s s') {f : Nat → Bool}
    (hst : storesOk is f = true) (hf : f tblSlot = false) : At s₀ B q s' := by
  refine ⟨by rw [p.gpr]; exact h.base, by rw [p.gpr]; exact h.esp, by rw [p.gpr]; exact h.kp, by rw [p.gpr]; exact h.tb,
    p.rd.trans h.rd, p.wr.trans h.wr, p.syms.trans h.syms, h.frame.trans ?_,
    (h.kept p hst (by decide) hf).trans h.tab⟩
  have := p.frame
  simp only [slotRegion, show s.gpr cfg.base = B from h.base] at this
  refine this.mono fun r hr => ?_
  rw [List.mem_singleton] at hr; subst hr
  simp [slotsR, cfg]

/-! ## G -/

theorem xor4_filterMap (V : Nat → BitVec 128) (c : Nat → Bool) (u : Nat → Nat) (t : Nat) (hu : ∀ a < 4, u a < 128) :
    xorBits V ((List.range 4).filterMap fun a => if c a then some (128 * t + u a) else none) =
      xor4 fun a => (V t).getLsbD (u a) && c a := by
  have e : ∀ a < 4, bitOf V (128 * t + u a) = (V t).getLsbD (u a) := fun a ha => bitOf_word V _ _ (hu a ha)
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.filterMap_cons, List.filterMap_nil, xor4]
  cases c 0 <;> cases c 1 <;> cases c 2 <;> cases c 3 <;>
    simp [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]

theorem tableM_sound {p c : Nat} (hp : p < 128) (hc : c < 512) {M : BitVec 128} (hM : M.getLsbD p = c.testBit 8) :
    (tableM M).Sound (TableRel (w := 128) p c) where
  xor := (table_sound hp hc).xor
  and := (table_sound hp hc).and
  or := (table_sound hp hc).or
  ror _ h := by cases h
  shr _ h := by cases h
  const {v a} h := by
    simp only [tableM] at h
    split at h
    · rename_i hv; cases h; subst hv
      rw [TableRel, testBit_tableOf, decide_eq_true hc, Bool.true_and, hM]
    · cases h

/-- What `G` needs of the state: the slots of the scratch buffer it uses, and the table. -/
structure GOk (s : State) (B : BitVec 32) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  tb : s.gpr tbr = s.syms tableName
  slots : SlotsIn 36 s B

theorem GOk.ok (h : GOk s B) : Ok cfgG s := by
  have hf := h.slots.fit
  refine ⟨fun k hk => ?_, fun k hk => absurd hk (Nat.not_lt_zero _), ?_, fun k hk j hj => absurd hj (Nat.not_lt_zero _), h.tb⟩
  · show InRegions s.wr (addr (s.gpr Impl.Modes.X86.sb) (16 * k)) 16
    rw [h.base]
    exact h.slots.acc _ hk
  · show (s.gpr Impl.Modes.X86.sb).toNat + 16 * 36 ≤ _
    rw [h.base]; omega_arith

theorem GOk.slot (h : GOk s B) (m : Mem) (k : Nat) : m.readW (xAddr (s.gpr cfgG.base) k) 128 = W m B k := by
  show m.readW (addr (s.gpr Impl.Modes.X86.sb) _) 128 = _
  rw [h.base]; rfl

theorem GOk.runs {is : List Instr} {s' : State} (h : GOk s B) (p : Runs cfgG is s s') : GOk s' B :=
  ⟨by rw [p.gpr]; exact h.base, by rw [p.gpr, p.syms]; exact h.tb, ⟨by rw [p.wr]; exact h.slots.acc, h.slots.fit⟩⟩

theorem GOk.kept {is : List Instr} {s' : State} (h : GOk s B) (p : Runs cfgG is s s') {f : Nat → Bool}
    (hst : (stored cfgG is).all f = true) {k : Nat} (hk : k < 36) (hf : f k = false) : W s'.mem B k = W s.mem B k := by
  rw [← h.slot, ← h.slot]
  refine p.kept k hk fun hm => ?_
  have := List.all_eq_true.mp hst k hm
  rw [hf] at this; cases this

theorem gIn_ok (h : GOk s B) :
    ∃ s', runBlock isa gIn s = some s' ∧ Runs cfgG gIn s s' ∧ ∀ j < 8, ∀ r < 4, ∀ i < 16,
      (W s'.mem B j).getLsbD (8 * i + r) = (W s.mem B (gS + r)).getLsbD (8 * i + j) := by
  obtain ⟨s', hr', p', ho⟩ := linear_ok0 gIn_chk h.ok (fun r => W s.mem B (gS + r)) fun j i w hm _ => by
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hm
    obtain ⟨t, ht, rfl, rfl, rfl⟩ := hm
    refine ⟨by omega_arith, ?_⟩
    rw [h.slot]; exact xor0 _
  refine ⟨s', hr', p', fun j hj r hr i hi => ?_⟩
  have := ho j (inG j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) (8 * i + r) (by omega_arith)
  rw [h.slot, inG] at this
  rw [this]
  split
  · rw [Nat.add_assoc, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (by omega_arith)]
    rw [show (8 * i + r) % 4 = r by omega_arith, show 4 * ((8 * i + r) / 4) + j = 8 * i + j by omega_arith]
  · rw [ite_eq_left (by omega_arith), Nat.add_assoc, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (by omega_arith)]
    rw [show (8 * i + r) % 4 = r by omega_arith, show 4 * ((8 * i + r) / 4 + 1) + (j - 4) = 8 * i + j by omega_arith]

theorem sbox_ok (h : GOk s B) :
    ∃ s', runBlock isa sboxCode s = some s' ∧ Runs cfgG sboxCode s s' ∧ ∀ j < 8, ∀ p < 128,
      (W s'.mem B j).getLsbD p = (sRow ((ofBits 8 fun k => (W s.mem B k).getLsbD p).toNat +
        if mS.getLsbD p then 256 else 0)).testBit j := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_chk
  have hpt : ∀ p < 128, ∃ s', runBlock isa sboxCode s = some s' ∧ Runs cfgG sboxCode s s' ∧ ∀ j < 8,
      (W s'.mem B j).getLsbD p = (sRow ((ofBits 8 fun k => (W s.mem B k).getLsbD p).toNat +
        if mS.getLsbD p then 256 else 0)).testBit j := by
    intro p hp
    obtain ⟨b, hb⟩ : ∃ b : BitVec 8, b = ofBits 8 (fun k => (W s.mem B k).getLsbD p) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : Nat, c = b.toNat + if mS.getLsbD p then 256 else 0 := ⟨_, rfl⟩
    have hb8 := b.isLt
    have hc' : c < 512 := by rw [hc]; split <;> omega_arith
    have h8 : mS.getLsbD p = c.testBit 8 := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hc]
      split
      · rename_i e; rw [e]; exact (decide_eq_true (by omega_arith)).symm
      · rename_i e; rw [Bool.not_eq_true] at e; rw [e]; exact (decide_eq_false (by omega_arith)).symm
    have hlow : ∀ k < 8, c.testBit k = b.getLsbD k := fun k hk => by
      have : c % 2 ^ 8 = b.toNat := by rw [hc]; split <;> omega_arith
      rw [BitVec.getLsbD, ← this, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and]
    have hrel : Rel (TableRel (w := 128) p c) cfgG (fun _ => none) sboxEnv s := by
      refine ⟨(fun r a h => by cases h), fun k a hk ha => ?_, fun k a hk ha => by cases ha⟩
      simp only [sboxEnv] at ha
      split at ha
      · rename_i hk8
        cases ha
        rw [h.slot, TableRel, testBit_tableOf, decide_eq_true hc', Bool.true_and, hlow k hk8, hb,
          getLsbD_ofBits, decide_eq_true hk8, Bool.true_and]
      · cases ha
    obtain ⟨s', hs', p'⟩ := run (ofDom_sound _ (tableM_sound hp hc' h8)) h.ok hrel he
    refine ⟨s', hs', p'.runs, fun j hj => ?_⟩
    have hj' := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    have := p'.rel.slot j _ (show j < 36 by omega_arith) (eq_of_beq hj')
    rw [p'.gpr, h.slot, TableRel, testBit_tableOf, decide_eq_true hc', Bool.true_and] at this
    rw [← this, hc, hb]
  obtain ⟨s', hs', p', _⟩ := hpt 0 (by decide)
  refine ⟨s', hs', p', fun j hj p hp => ?_⟩
  obtain ⟨s'', hs'', _, hv⟩ := hpt p hp
  rw [hs'] at hs''
  cases hs''
  exact hv j hj

theorem gOut_ok (h : GOk s B) :
    ∃ s', runBlock isa gOut s = some s' ∧ Runs cfgG gOut s s' ∧ ∀ r < 4, ∀ l < 4, ∀ z < 4, ∀ t < 8,
      (W s'.mem B (gS + r)).getLsbD (32 * l + (8 * z + t)) = xor4 fun a =>
        (W s.mem B t ^^^ cS8 t).getLsbD (8 * (4 * l + a) + r) && (maskOf ((a + z) % 4)).getLsbD t := by
  obtain ⟨s', hr', p', ho⟩ := linear_ok0 gOut_chk h.ok (fun j => W s.mem B j ^^^ cS8 j) fun j i w hm _ => by
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hm
    obtain ⟨t, ht, rfl, rfl, rfl⟩ := hm
    refine ⟨by omega_arith, ?_⟩
    rw [h.slot, BitVec.xor_assoc, BitVec.xor_self]; exact xor0 _
  refine ⟨s', hr', p', fun r hr l hl z hz t ht => ?_⟩
  have := ho (gS + r) (outG r) (List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩) (32 * l + (8 * z + t)) (by omega_arith)
  rw [h.slot, outG, show (32 * l + (8 * z + t)) / 8 % 4 = z by omega_arith, show (32 * l + (8 * z + t)) % 8 = t by omega_arith,
    show (32 * l + (8 * z + t)) / 32 = l by omega_arith,
    xor4_filterMap _ (fun a => (maskOf ((a + z) % 4)).getLsbD t) (fun a => 8 * (4 * l + a) + r) t
      (fun a ha => by omega_arith)] at this
  exact this

/-- The mask's bits. -/
theorem mS_bit : ∀ i < 16, ∀ r < 4, mS.getLsbD (8 * i + r) = decide (i % 2 = 0) := by decide

theorem cS8_bit {t i r : Nat} (hi : i < 16) (hr : r < 4) :
    (cS8 t).getLsbD (8 * i + r) = if i % 2 = 0 then (0xa9).testBit t else (0x38).testBit t := by
  rw [cS8, getLsbD_ofBits, decide_eq_true (by omega_arith), Bool.true_and, show (8 * i + r) / 8 = i by omega_arith]

theorem sRow_even {b : Nat} (hb : b < 256) (t : Nat) :
    ((sRow (b + 256)).testBit t ^^ (0xa9).testBit t) = (sNat false b).testBit t := by
  rw [sRow, ite_eq_left (by rw [Nat.testBit_eq_decide_div_mod_eq]; exact decide_eq_true (by omega_arith)),
    show (b + 256) % 256 = b by omega_arith, Nat.testBit_xor, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

theorem sRow_odd {b : Nat} (hb : b < 256) (t : Nat) :
    ((sRow (b + 0)).testBit t ^^ (0x38).testBit t) = (sNat true b).testBit t := by
  rw [sRow, ite_eq_right (by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false (by omega_arith)]; exact Bool.false_ne_true),
    show (b + 0) % 256 = b by omega_arith, Nat.testBit_xor, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- `G` of the sixteen words. -/
theorem g_ok (h : GOk s B) {x : Nat → Word} (hx : QW s.mem B gS x) :
    ∃ s', runBlock isa g s = some s' ∧ Runs cfgG g s s' ∧ QW s'.mem B gS fun i => Spec.Seed.g (x i) := by
  obtain ⟨s₁, r₁, p₁, v₁⟩ := gIn_ok h
  have a₁ := h.runs p₁
  obtain ⟨s₂, r₂, p₂, v₂⟩ := sbox_ok a₁
  have a₂ := a₁.runs p₂
  obtain ⟨s₃, r₃, p₃, v₃⟩ := gOut_ok a₂
  refine ⟨s₃, ?_, p₁.trans (p₂.trans p₃), QW.of_bits fun r hr l hl t ht => ?_⟩
  · rw [g, run_append r₁ (run_append r₂ r₃)]
  · obtain ⟨z, u, hz, hu, rfl⟩ : ∃ z u, z < 4 ∧ u < 8 ∧ t = 8 * z + u :=
      ⟨t / 8, t % 8, by omega_arith, by omega_arith, by omega_arith⟩
    rw [v₃ r hr l hl z hz u hu, Proof.Seed.getLsbD_g _ hz hu]
    have ha : ∀ a < 4, (W s₂.mem B u ^^^ cS8 u).getLsbD (8 * (4 * l + a) + r) =
        (sOf a (byteOf (x (4 * r + l)) a)).getLsbD u := fun a ha => by
      have hi : 4 * l + a < 16 := by omega_arith
      have hb : (ofBits 8 fun k => (W s₁.mem B k).getLsbD (8 * (4 * l + a) + r)) = byteOf (x (4 * r + l)) a :=
        BitVec.eq_of_getLsbD_eq fun k hk => by
          rw [getLsbD_ofBits, decide_eq_true hk, Bool.true_and, v₁ k hk r hr _ hi, Proof.Seed.getLsbD_byteOf _ hk,
            show 8 * (4 * l + a) + k = 32 * l + (8 * a + k) by omega_arith]
          exact hx.bit hr hl (by omega_arith)
      have hlt := (byteOf (x (4 * r + l)) a).isLt
      rw [BitVec.getLsbD_xor, v₂ u hu _ (by omega_arith), hb, mS_bit _ hi r hr, cS8_bit hi hr, sOf,
        Proof.Seed.sTable_getD, BitVec.getLsbD_ofNat, decide_eq_true hu, Bool.true_and]
      rcases Nat.mod_two_eq_zero_or_one a with e | e
      · rw [show (4 * l + a) % 2 = 0 by omega_arith]
        simp only [decide_true, ite_true]
        rw [sRow_even hlt, e]; rfl
      · rw [show (4 * l + a) % 2 = 1 by omega_arith]
        simp only [Nat.one_ne_zero, decide_false, Bool.false_eq_true, ite_false]
        rw [sRow_odd hlt, e]; rfl
    unfold xor4
    dsimp only
    rw [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide)]

/-- The call of `G`. -/
theorem gCall_wp' (h : GOk s B) (hst : Region.Disjoint (below (s.gpr .esp) 4) (slotsR B 0 36)) {x : Nat → Word}
    (hx : QW s.mem B gS x) {Q : State → Prop}
    (K : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      Frame [slotsR B 0 36, below (s.gpr .esp) 4] s.mem s'.mem → W s'.mem B tblSlot = W s.mem B tblSlot →
      QW s'.mem B gS (fun i => Spec.Seed.g (x i)) → Q s') : WP isa gCall s Q := by
  have hf := h.slots.fit
  have hce : Frame [below (s.gpr .esp) 4] s.mem s.callEntry.mem := by
    rw [State.callEntry_mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have keep : ∀ k < 36, W s.callEntry.mem B k = W s.mem B k := fun k hk => W_frame hce (by omega_arith) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (hst.sub_right (Offset.sub _ (by omega_arith) (by omega_arith))).symm
  have hg : ∀ r ≠ .esp, s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr _ hr
  have h' : GOk s.callEntry B := ⟨(hg _ (by decide)).trans h.base, (hg _ (by decide)).trans h.tb,
    ⟨fun k hk => by rw [State.callEntry_wr]; exact h.slots.acc k hk, hf⟩⟩
  obtain ⟨u, ru, pu, xu⟩ := g_ok h' (hx.congr fun r hr => keep _ (by unfold gS; omega_arith))
  have st := stored_g
  simp only [Bool.and_eq_true] at st
  have fu : Frame [slotsR B 0 36] s.callEntry.mem u.mem := by
    have := pu.frame
    simp only [slotRegion, show s.callEntry.gpr cfgG.base = B from h'.base] at this
    simpa [slotsR, cfgG] using this
  refine WP.callBody (WP.of_runBlock ⟨u, ru, ?_, ?_, K _ ?_ pu.rd pu.wr pu.syms ?_ ?_ xu⟩)
  · rw [pu.gpr, State.callEntry_esp]
  · rw [fu.readW (r := below (s.gpr .esp) 4) (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hst) (by decide), State.callEntry_mem, Mem.readW_writeW_self32]
  · funext r
    by_cases hr : r = .esp
    · subst hr; simp [State.setReg]
    · simp only [State.setReg, hr, ite_false, pu.gpr]; exact hg r hr
  · refine (hce.mono fun r hr => ?_).trans (fu.mono fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  · exact (h'.kept pu st.2 (by decide) rfl).trans (keep _ (by decide))

/-- What the calls of `G` need: the scratch buffer's slots, and the four
bytes below `esp` apart from them. -/
structure Env0 (m : Nat) (s₀ : State) (B : BitVec 32) : Prop where
  slots : SlotsIn m s₀ B
  stk : Region.Disjoint (below (s₀.gpr .esp) 4) ⟨B.setWidth 64, 16 * m⟩

theorem Env0.out (hs : Env0 m s₀ B) {k : Nat} (hk : k < m) : Region.Disjoint (slotsR B k 1) (below (s₀.gpr .esp) 4) :=
  (hs.stk.sub_right (Offset.sub_base _ (by omega_arith))).symm

theorem gCall_wp (h : At s₀ B q s) (hs : Env0 m s₀ B) (hq : 80 + q + 4 ≤ m) {x : Nat → Word} (hx : QW s.mem B gS x)
    {Q : State → Prop}
    (K : ∀ s', At s₀ B q s' → s'.gpr = s.gpr → QW s'.mem B gS (fun i => Spec.Seed.g (x i)) →
      (∀ k, 36 ≤ k → k < 80 → W s'.mem B k = W s.mem B k) → Q s') : WP isa gCall s Q := by
  have hf := hs.slots.fit
  have hG : GOk s B := ⟨h.base, h.tb.trans (congrFun h.syms _).symm,
    ⟨fun k hk => by rw [h.wr]; exact hs.slots.acc k (by omega_arith), by omega_arith⟩⟩
  refine gCall_wp' hG (by rw [h.esp]; exact hs.stk.sub_right (Offset.sub_base _ (by omega_arith))) hx
    fun s' g' rd' wr' sy' f' t' x' => K s' ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ g' x' fun k h1 h2 => ?_
  · rw [g']; exact h.base
  · rw [g']; exact h.esp
  · rw [g']; exact h.kp
  · rw [g']; exact h.tb
  · rw [rd']; exact h.rd
  · rw [wr']; exact h.wr
  · rw [sy']; exact h.syms
  · refine h.frame.trans (f'.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [h.esp]; exact fun _ h => h⟩
  · exact t'.trans h.tab
  · refine W_frame f' (by omega_arith) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint (B.setWidth 64) (.inr (by omega_arith)) (by omega_arith) (by decide)
    · rw [h.esp]; exact hs.out (by omega_arith)

end

section
variable {s₀ s : State} {B : BitVec 32} {q m : Nat}

/-! ## A round -/

/-- The words of a block of expressions: the slots, and the external words. -/
def inV (m : Mem) (B : BitVec 32) (q : Nat) (n : Nat) : BitVec 128 := if n < 80 then W m B n else W m B (q + n)

theorem exprs_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 80 + q + 4 ≤ m) {is : List Instr} {outs : List (Nat × XE)}
    (hchk : exprOk is outs = true) :
    ∃ s', runBlock isa is s = some s' ∧ Runs cfg is s s' ∧ ∀ k e, (k, e) ∈ outs → W s'.mem B k = e.eval (inV s.mem B q) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (fun (e : XE) x => x = e.eval (inV s.mem B q)) cfg (fun n => some (.atom (80 + n))) atomsE s := by
    refine ⟨(fun r a h => by cases h), fun k a hk ha => ?_, fun k a hk ha => ?_⟩
    · cases ha
      have hk : k < 80 := hk
      rw [h.slot, XE.eval, inV, ite_eq_left hk]
    · cases ha
      rw [h.ext, XE.eval, inV, ite_eq_right (by omega_arith)]
      exact congrArg _ (by omega_arith)
  obtain ⟨s', hs', p'⟩ := run (exprs_sound _) (h.ok hs hq) hrel he
  refine ⟨s', hs', p'.runs, fun k e hke => ?_⟩
  have := List.all_eq_true.mp hpost (k, e) hke
  rw [Bool.and_eq_true, decide_eq_true_eq] at this
  have := p'.rel.slot k _ this.1 (eq_of_beq this.2)
  rw [p'.gpr, h.slot] at this
  exact this

/-- The slot `i` of round keys has the round key `v` in every doubleword. -/
def KW (m : Mem) (B : BitVec 32) (i : Nat) (v : Word) : Prop := ∀ l < 4, dword (W m B (80 + i)) l = v

/-- The round keys. -/
def Keys (m : Mem) (B : BitVec 32) (rk : Nat → Word) : Prop := ∀ i < 32, KW m B i (rk i)

theorem At.keys (h : At s₀ B q s) (hs : Env0 112 s₀ B) {rk : Nat → Word} (hk : Keys s₀.mem B rk) : Keys s.mem B rk := by
  have hf := hs.slots.fit
  intro i hi l hl
  rw [W_frame h.frame (by omega_arith) fun r hr => ?_]
  · exact hk i hi l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint (B.setWidth 64) (.inr (by omega_arith)) (by omega_arith) (by decide)
    · exact hs.out (by omega_arith)

theorem mem_lanes {α : Type} {f : Nat → List α} {k : Nat} {a : α} (hk : k < 4) (h : a ∈ f k) : a ∈ (List.range 4).flatMap f :=
  List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, h⟩

/-- The slots that a round reads and writes are as they were: those of the
state's words and the values of F. -/
def Kept (m m' : Mem) (B : BitVec 32) (a n : Nat) : Prop := ∀ k, a ≤ k → k < a + n → W m' B k = W m B k

theorem step1_ok (h : At s₀ B q s) (hs : Env0 112 s₀ B) (hq : 80 + q + 4 ≤ 112) {r ko : Nat} (hr : r + 8 ≤ 64) (hko : ko + 1 < 4)
    (hchk : exprOk (step1 r (16 * ko)) (step1E r ko) = true)
    (hst : storesOk (step1 r (16 * ko)) (fun k => 32 ≤ k && k < 40) = true)
    {R0 R1 : Nat → Word} {K0 K1 : Word} (h0 : QW s.mem B r R0) (h1 : QW s.mem B (r + 4) R1)
    (k0 : KW s.mem B (q + ko) K0) (k1 : KW s.mem B (q + ko + 1) K1) :
    ∃ s', runBlock isa (step1 r (16 * ko)) s = some s' ∧ At s₀ B q s' ∧ s'.gpr = s.gpr ∧
      QW s'.mem B aS (fun b => R0 b ^^^ K0) ∧ QW s'.mem B gS (fun b => (R0 b ^^^ K0) ^^^ (R1 b ^^^ K1)) ∧
      Kept s.mem s'.mem B 48 16 := by
  obtain ⟨s', r', p', v⟩ := exprs_ok h hs.slots hq hchk
  have e0 : ∀ k < 4, inV s.mem B q (r + k) = W s.mem B (r + k) := fun k hk => by rw [inV, ite_eq_left (by omega_arith)]
  have e1 : ∀ k < 4, inV s.mem B q (r + 4 + k) = W s.mem B (r + 4 + k) := fun k hk => by rw [inV, ite_eq_left (by omega_arith)]
  have e2 : inV s.mem B q (80 + ko) = W s.mem B (80 + (q + ko)) := by
    rw [inV, ite_eq_right (by omega_arith)]; exact congrArg _ (by omega_arith)
  have e3 : inV s.mem B q (81 + ko) = W s.mem B (80 + (q + ko + 1)) := by
    rw [inV, ite_eq_right (by omega_arith)]; exact congrArg _ (by omega_arith)
  refine ⟨s', r', h.runs p' hst rfl, p'.gpr, fun k hk l hl => ?_, fun k hk l hl => ?_, fun k h1 h2 =>
    h.kept p' hst (by omega_arith) (by simp; omega_arith)⟩
  · rw [v (aS + k) _ (mem_lanes hk (List.mem_cons_self)), bn, XE.eval, XE.eval, XE.eval, dword_pxor, e0 k hk, e2, h0 k hk l hl, k0 l hl]
  · rw [v (gS + k) _ (mem_lanes hk (List.mem_cons_of_mem _ List.mem_cons_self)), bn]
    simp only [XE.eval]
    rw [dword_pxor, dword_pxor, dword_pxor, e0 k hk, e1 k hk, e2, e3, h0 k hk l hl, h1 k hk l hl, k0 l hl, k1 l hl, BitVec.xor_assoc]

theorem inV_lo (m : Mem) (B : BitVec 32) (q : Nat) {n : Nat} (hn : n < 80) : inV m B q n = W m B n := by rw [inV, ite_eq_left hn]

theorem step23_ok (h : At s₀ B q s) (hs : Env0 112 s₀ B) (hq : 80 + q + 4 ≤ 112) {is : List Instr} {d a : Nat} (ha : a + 4 ≤ 80)
    (hchk : exprOk is ((List.range 4).flatMap fun k => [(d + k, .atom (gS + k)), (gS + k, bn .paddd (gS + k) (a + k))]) = true)
    {f : Nat → Bool} (hst : storesOk is f = true) (hft : f tblSlot = false)
    {X Y : Nat → Word} (hx : QW s.mem B gS X) (hy : QW s.mem B a Y) :
    ∃ s', runBlock isa is s = some s' ∧ At s₀ B q s' ∧ s'.gpr = s.gpr ∧
      QW s'.mem B d X ∧ QW s'.mem B gS (fun b => X b + Y b) ∧ ∀ k < 80, f k = false → W s'.mem B k = W s.mem B k := by
  obtain ⟨s', r', p', v⟩ := exprs_ok h hs.slots hq hchk
  have hg : gS = 32 := rfl
  refine ⟨s', r', h.runs p' hst hft, p'.gpr, fun k hk l hl => ?_, fun k hk l hl => ?_, fun k hk hf => h.kept p' hst hk hf⟩
  · rw [v (d + k) _ (mem_lanes hk (List.mem_cons_self)), XE.eval, inV_lo _ _ _ (by omega_arith), hx k hk l hl]
  · rw [v (gS + k) _ (mem_lanes hk (List.mem_cons_of_mem _ List.mem_cons_self)), bn]
    simp only [XE.eval]
    rw [dword_paddd _ _ hl, inV_lo _ _ _ (by omega_arith), inV_lo _ _ _ (by omega_arith), hx k hk l hl, hy k hk l hl]

theorem step4_ok (h : At s₀ B q s) (hs : Env0 112 s₀ B) (hq : 80 + q + 4 ≤ 112) {l : Nat} (hl : l + 8 ≤ 64)
    (hchk : exprOk (step4 l) (step4E l) = true) {f : Nat → Bool} (hst : storesOk (step4 l) f = true) (hft : f tblSlot = false)
    {E D L0 L1 : Nat → Word} (hE : QW s.mem B gS E) (hD : QW s.mem B dS D) (h0 : QW s.mem B l L0) (h1 : QW s.mem B (l + 4) L1) :
    ∃ s', runBlock isa (step4 l) s = some s' ∧ At s₀ B q s' ∧ s'.gpr = s.gpr ∧
      QW s'.mem B l (fun b => L0 b ^^^ (E b + D b)) ∧ QW s'.mem B (l + 4) (fun b => L1 b ^^^ E b) ∧
      ∀ k < 80, f k = false → W s'.mem B k = W s.mem B k := by
  obtain ⟨s', r', p', v⟩ := exprs_ok h hs.slots hq hchk
  have hg : gS = 32 := rfl
  have hd : dS = 44 := rfl
  refine ⟨s', r', h.runs p' hst hft, p'.gpr, fun k hk i hi => ?_, fun k hk i hi => ?_, fun k hk hf => h.kept p' hst hk hf⟩
  · rw [v (l + k) _ (mem_lanes hk (List.mem_cons_of_mem _ List.mem_cons_self)), bn]
    simp only [XE.eval]
    rw [dword_pxor, dword_paddd _ _ hi, inV_lo _ _ _ (by omega_arith), inV_lo _ _ _ (by omega_arith),
      inV_lo _ _ _ (by omega_arith), hE k hk i hi, hD k hk i hi, h0 k hk i hi, BitVec.xor_comm]
  · rw [v (l + 4 + k) _ (mem_lanes hk (List.mem_cons_self)), bn]
    simp only [XE.eval]
    rw [dword_pxor, inV_lo _ _ _ (by omega_arith), inV_lo _ _ _ (by omega_arith), hE k hk i hi, h1 k hk i hi]

/-- A round: the left half in the slots `l` and up is XORed with F of the right, in `r` and up. -/
theorem round_wp (h : At s₀ B q s) (hs : Env0 112 s₀ B) (hq : 80 + q + 4 ≤ 112) {l r ko : Nat} (hl : l + 8 ≤ 64) (hl' : 48 ≤ l)
    (hr : r + 8 ≤ 64) (hr' : 48 ≤ r) (hlr : l + 8 ≤ r ∨ r + 8 ≤ l) (hko : ko + 1 < 4)
    (c1 : exprOk (step1 r (16 * ko)) (step1E r ko) = true)
    (st1 : storesOk (step1 r (16 * ko)) (fun k => 32 ≤ k && k < 40) = true)
    (c4 : exprOk (step4 l) (step4E l) = true) (st4 : storesOk (step4 l) (fun k => l ≤ k && k < l + 8) = true)
    {L0 L1 R0 R1 : Nat → Word} {K0 K1 : Word} (hL0 : QW s.mem B l L0) (hL1 : QW s.mem B (l + 4) L1)
    (hR0 : QW s.mem B r R0) (hR1 : QW s.mem B (r + 4) R1)
    (k0 : KW s.mem B (q + ko) K0) (k1 : KW s.mem B (q + ko + 1) K1) :
    WP isa (round l r (16 * ko)) s fun s' => At s₀ B q s' ∧ s'.gpr = s.gpr ∧
      QW s'.mem B l (fun b => L0 b ^^^ (Spec.Seed.f K0 K1 (R0 b) (R1 b)).1) ∧
      QW s'.mem B (l + 4) (fun b => L1 b ^^^ (Spec.Seed.f K0 K1 (R0 b) (R1 b)).2) ∧
      QW s'.mem B r R0 ∧ QW s'.mem B (r + 4) R1 := by
  have c := steps_chk
  have st := stores_chk
  simp only [Bool.and_eq_true] at c st
  obtain ⟨s₁, r₁, a₁, g₁, A₁, G₁, K₁⟩ := step1_ok h hs hq hr hko c1 st1 hR0 hR1 k0 k1
  refine WP.seq (WP.of_runBlock ⟨s₁, r₁, WP.seq (gCall_wp a₁ hs hq G₁ fun s₂ a₂ g₂ G₂ K₂ => ?_)⟩)
  have A₂ : QW s₂.mem B aS (fun b => R0 b ^^^ K0) := A₁.congr fun k hk => K₂ _ (by unfold aS; omega_arith) (by unfold aS; omega_arith)
  obtain ⟨s₃, r₃, a₃, g₃, C₃, G₃, K₃⟩ := step23_ok a₂ hs hq (by decide) c.1.1.1.2 st.1.1.1.1.1.2 rfl G₂ A₂
  refine WP.seq (WP.of_runBlock ⟨s₃, r₃, WP.seq (gCall_wp a₃ hs hq G₃ fun s₄ a₄ g₄ G₄ K₄ => ?_)⟩)
  have C₄ := C₃.congr fun k hk => K₄ (cS + k) (by unfold cS; omega_arith) (by unfold cS; omega_arith)
  obtain ⟨s₅, r₅, a₅, g₅, D₅, G₅, K₅⟩ := step23_ok a₄ hs hq (by decide) c.1.1.2 st.1.1.1.1.2 rfl G₄ C₄
  refine WP.seq (WP.of_runBlock ⟨s₅, r₅, WP.seq (gCall_wp a₅ hs hq G₅ fun s₆ a₆ g₆ G₆ K₆ => ?_)⟩)
  have D₆ := D₅.congr fun k hk => K₆ (dS + k) (by unfold dS; omega_arith) (by unfold dS; omega_arith)
  have keep : ∀ k, 48 ≤ k → k < 64 → W s₆.mem B k = W s.mem B k := fun k h1 h2 => by
    rw [K₆ k (by omega_arith) (by omega_arith), K₅ k (by omega_arith) (by simp; omega_arith), K₄ k (by omega_arith) (by omega_arith),
      K₃ k (by omega_arith) (by simp; omega_arith), K₂ k (by omega_arith) (by omega_arith), K₁ k h1 (by omega_arith)]
  have q6 : ∀ {d : Nat} {x : Nat → Word}, 48 ≤ d → d + 4 ≤ 64 → QW s.mem B d x → QW s₆.mem B d x := fun h1 h2 hx =>
    hx.congr fun k hk => keep _ (by omega_arith) (by omega_arith)
  obtain ⟨s₇, r₇, a₇, g₇, X₇, Y₇, K₇⟩ := step4_ok a₆ hs hq hl c4 st4 (by simp; unfold tblSlot; omega_arith) G₆ D₆
    (q6 hl' (by omega_arith) hL0) (q6 (by omega_arith) (by omega_arith) hL1)
  refine WP.of_runBlock ⟨s₇, r₇, a₇, by rw [g₇, g₆, g₅, g₄, g₃, g₂, g₁], X₇, Y₇, ?_, ?_⟩
  · exact (q6 hr' (by omega_arith) hR0).congr fun k hk => K₇ _ (by omega_arith) (by simp; omega_arith)
  · exact (q6 (by omega_arith) (by omega_arith) hR1).congr fun k hk => K₇ _ (by omega_arith) (by simp; omega_arith)

/-! ## The rounds -/

open VG.Proof.Seed (Quad roundsN decodeQ encodeSwapped)

variable {rk : Nat → Word}

/-- The round keys of round `j + 1`. -/
abbrev keyOf (rk : Nat → Word) : Nat → Word × Word := fun j => (rk (2 * j), rk (2 * j + 1))

/-- The words of the sixteen blocks. -/
def Q4 (m : Mem) (B : BitVec 32) (x : Nat → Quad) : Prop :=
  QW m B (arr 0) (fun b => (x b).1) ∧ QW m B (arr 0 + 4) (fun b => (x b).2.1) ∧ QW m B (arr 2) (fun b => (x b).2.2.1) ∧
    QW m B (arr 2 + 4) (fun b => (x b).2.2.2)

theorem arrs : arr 0 = 48 ∧ arr 2 = 56 := ⟨rfl, rfl⟩

/-- Two rounds. -/
theorem turn_wp (hs : Env0 112 s₀ B) (hk : Keys s₀.mem B rk) {i : Nat} (hi : i < 8) (h : At s₀ B (4 * i) s) {x : Nat → Quad}
    (hx : Q4 s.mem B x) {c : Nat} (hc : s.gpr .ecx = BitVec.ofNat 32 c) (hc1 : 1 ≤ c) (hc8 : c ≤ 8) :
    WP isa turn s fun s' => At s₀ B (4 * (i + 1)) s' ∧
      Q4 s'.mem B (fun b => Spec.Seed.round (keyOf rk (2 * i + 1)) (Spec.Seed.round (keyOf rk (2 * i)) (x b))) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (c - 1) ∧ s'.zf = some (decide (c = 1)) := by
  have ck := steps_chk
  have st := stores_chk
  simp only [Bool.and_eq_true] at ck st
  have k := h.keys hs hk
  refine WP.seq (WP.mono (round_wp h hs (by omega_arith) (l := arr 0) (r := arr 2) (ko := 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ck.1.1.1.1.1 st.1.1.1.1.1.1.1 ck.1.2 st.1.1.1.2 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
    (K0 := rk (2 * (2 * i))) (K1 := rk (2 * (2 * i) + 1)) (by rw [show 4 * i + 0 = 2 * (2 * i) by omega_arith]; exact k _ (by omega_arith))
    (by rw [show 4 * i + 0 + 1 = 2 * (2 * i) + 1 by omega_arith]; exact k _ (by omega_arith)))
    fun s₁ ⟨a₁, g₁, X₁, Y₁, U₁, V₁⟩ => ?_)
  have k' := a₁.keys hs hk
  refine WP.seq (WP.mono (round_wp a₁ hs (by omega_arith) (l := arr 2) (r := arr 0) (ko := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ck.1.1.1.1.2 st.1.1.1.1.1.1.2 ck.2 st.1.1.2 U₁ V₁ X₁ Y₁
    (K0 := rk (2 * (2 * i + 1))) (K1 := rk (2 * (2 * i + 1) + 1))
    (by rw [show 4 * i + 2 = 2 * (2 * i + 1) by omega_arith]; exact k' _ (by omega_arith))
    (by rw [show 4 * i + 2 + 1 = 2 * (2 * i + 1) + 1 by omega_arith]; exact k' _ (by omega_arith)))
    fun s₂ ⟨a₂, g₂, X₂, Y₂, U₂, V₂⟩ => ?_)
  refine Wp.wp_addi fun s₃ u₃ => Wp.wp_subi fun s₄ u₄ _ z₄ => WP.block_nil ?_
  have e₃ : s₃.gpr .ecx = BitVec.ofNat 32 c := by rw [u₃.other _ (by decide), g₂, g₁, hc]
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact a₂.base
  · rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact a₂.esp
  · rw [u₄.other _ (by decide), u₃.gpr, a₂.kp, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, Offset.add_ofNat_add_ofNat,
      show 16 * (80 + 4 * i) + 64 = 16 * (80 + 4 * (i + 1)) by omega_arith]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact a₂.tb
  · rw [u₄.rd, u₃.rd]; exact a₂.rd
  · rw [u₄.wr, u₃.wr]; exact a₂.wr
  · rw [u₄.syms, u₃.syms]; exact a₂.syms
  · rw [m₄]; exact a₂.frame
  · rw [m₄]; exact a₂.tab
  · rw [m₄]; exact U₂
  · rw [m₄]; exact V₂
  · rw [m₄]; exact X₂
  · rw [m₄]; exact Y₂
  · rw [u₄.gpr, e₃]; exact Wp.ofNat_pred hc1
  · rw [z₄, e₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_arith) (by decide)]

/-- The sixteen rounds. -/
theorem loop_wp (hs : Env0 112 s₀ B) (hk : Keys s₀.mem B rk) (h : At s₀ B 0 s) {x : Nat → Quad}
    (hx : Q4 s.mem B x) (hc : s.gpr .ecx = BitVec.ofNat 32 8) :
    WP isa (.loop turn .ne) s fun s' => At s₀ B 32 s' ∧ Q4 s'.mem B (fun b => roundsN (keyOf rk) 16 (x b)) := by
  refine WP.loop (M := isa) (fun (c : Nat) (s' : State) => 1 ≤ c ∧ c ≤ 8 ∧ At s₀ B (4 * (8 - c)) s' ∧
    Q4 s'.mem B (fun b => roundsN (keyOf rk) (2 * (8 - c)) (x b)) ∧ s'.gpr .ecx = BitVec.ofNat 32 c) ?_ 8 s
    ⟨by decide, by decide, h, by rw [show (fun b => roundsN (keyOf rk) (2 * (8 - 8)) (x b)) = x from funext fun _ => rfl]; exact hx, hc⟩
  rintro c t ⟨h1, h8, a, px, hcx⟩
  refine WP.mono (turn_wp hs hk (i := 8 - c) (by omega_arith) a px hcx h1 h8) fun t' ⟨a', p', c', z'⟩ => ?_
  have e : (fun b => Spec.Seed.round (keyOf rk (2 * (8 - c) + 1)) (Spec.Seed.round (keyOf rk (2 * (8 - c)))
      (roundsN (keyOf rk) (2 * (8 - c)) (x b)))) = fun b => roundsN (keyOf rk) (2 * (8 - (c - 1))) (x b) := funext fun b => by
    rw [← Proof.Seed.roundsN_succ, ← Proof.Seed.roundsN_succ, show 2 * (8 - c) + 1 + 1 = 2 * (8 - (c - 1)) by omega_arith]
  rw [e] at p'
  rw [show 8 - c + 1 = 8 - (c - 1) by omega_arith] at a'
  by_cases hc1 : c = 1
  · subst hc1
    exact .inl ⟨by show t'.zf.map _ = _; rw [z']; rfl, a', p'⟩
  · exact .inr ⟨by show t'.zf.map _ = _; rw [z', decide_eq_false hc1]; rfl, c - 1, by omega_arith, by omega_arith,
      by omega_arith, a', p', c'⟩

/-! ## The blocks -/

/-- The address of block `b` of the buffer. -/
abbrev blk (B : BitVec 32) (b : Nat) : Addr := B.setWidth 64 + BitVec.ofNat 64 (16 * (bufS + b))

/-- Block `b` of the buffer. -/
abbrev blkAt (m : Mem) (B : BitVec 32) (b : Nat) : Spec.Seed.Block := Spec.Seed.blockAt m (blk B b)

theorem blocksIn_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 80 + q + 4 ≤ m) :
    ∃ s', runBlock isa blocksIn s = some s' ∧ At s₀ B q s' ∧ s'.gpr = s.gpr ∧
      Q4 s'.mem B (fun b => decodeQ (blkAt s.mem B b)) := by
  have hf := hs.fit
  have hbs : bufS = 64 := rfl
  obtain ⟨s', hr', p', ho⟩ := linear_ok0 blocksIn_chk (h.ok hs hq) (fun b => W s.mem B (bufS + b)) fun j i w hm _ => by
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hm
    obtain ⟨t, ht, rfl, rfl, rfl⟩ := hm
    refine ⟨by omega_arith, ?_⟩
    rw [h.slot]; exact xor0 _
  have st := stores_chk
  simp only [Bool.and_eq_true] at st
  have key : ∀ k < 4, QW s'.mem B (48 + 4 * k) (fun b => Spec.Seed.wordAt (blkAt s.mem B b) (4 * k)) := fun k hk => by
    refine QW.of_bits fun r hr l hl t ht => ?_
    obtain ⟨a, u, ha, hu, rfl⟩ : ∃ a u, a < 4 ∧ u < 8 ∧ t = 8 * a + u :=
      ⟨t / 8, t % 8, by omega_arith, by omega_arith, by omega_arith⟩
    have := ho (48 + (4 * k + r)) (inB ((4 * k + r) / 4) ((4 * k + r) % 4))
      (List.mem_map.mpr ⟨4 * k + r, List.mem_range.mpr (by omega_arith), rfl⟩) (32 * l + (8 * a + u)) (by omega_arith)
    rw [h.slot, inB, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (by omega_arith),
      show (4 * k + r) / 4 = k by omega_arith, show (4 * k + r) % 4 = r by omega_arith,
      show (32 * l + (8 * a + u)) / 32 = l by omega_arith, show (32 * l + (8 * a + u)) % 32 / 8 = a by omega_arith,
      show (32 * l + (8 * a + u)) % 8 = u by omega_arith, W_bit _ (by omega_arith) (by omega_arith) hu] at this
    rw [Nat.add_assoc 48, this, ← Proof.Seed.getLsbD_byteOf _ hu, AesNi.byteOf_wordAt _ _ ha, AesNi.blockAt_getD _ _ (by omega_arith),
      Offset.add_ofNat_add_ofNat]
  exact ⟨s', hr', h.runs p' st.1.2 rfl, p'.gpr, key 0 (by decide), key 1 (by decide), key 2 (by decide), key 3 (by decide)⟩

theorem blocksOut_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hm : 80 ≤ m) {x : Nat → Quad} (hx : Q4 s.mem B x) :
    ∃ s', runBlock isa blocksOut s = some s' ∧ At s₀ B q s' ∧ ∀ b < 16, Spec.Aes.bytesAt s'.mem (blk B b) 16 = (encodeSwapped (x b)).toList := by
  have hf := hs.fit
  have hbs : bufS = 64 := rfl
  obtain ⟨s', hr', p', ho⟩ := linear_ok0 blocksOut_chk (h.okO hs hm) (fun i => W s.mem B (48 + i)) fun j i w hm _ => by
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hm
    obtain ⟨t, ht, rfl, rfl, rfl⟩ := hm
    refine ⟨by omega_arith, ?_⟩
    show _ = s.mem.readW (xAddr (s.gpr cfg.base) _) 128
    rw [h.slot]; exact xor0 _
  have p' : Runs cfg blocksOut s s' := ⟨p'.only, p'.other, fun k hk hn => p'.kept k hk (by rw [stored_out]; exact hn), p'.frame⟩
  have st := stores_chk
  simp only [Bool.and_eq_true] at st
  refine ⟨s', hr', h.runs p' st.2 rfl, fun b hb => ?_⟩
  rw [show encodeSwapped (x b) = Vector.ofFn fun i : Fin 16 =>
    byteOf ((#v[(x b).2.2.1, (x b).2.2.2, (x b).1, (x b).2.1] : Vector Word 4).getD (i.val / 4) 0) (3 - i.val % 4) from rfl]
  refine List.ext_getElem (by simp [Spec.Aes.bytesAt]) fun i h₁ _ => ?_
  have hi : i < 16 := by simpa [Spec.Aes.bytesAt] using h₁
  rw [Vector.getElem_toList, Vector.getElem_ofFn]
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, Offset.add_ofNat_add_ofNat]
  refine BitVec.eq_of_getLsbD_eq fun u hu => ?_
  rw [← W_bit _ (by omega_arith) hi hu, Proof.Seed.getLsbD_byteOf _ hu]
  have := ho (bufS + b) (outB b) (List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩) (8 * i + u) (by omega_arith)
  have this : (s'.mem.readW (xAddr (s.gpr cfg.base) (bufS + b)) 128).getLsbD (8 * i + u) = _ := this
  rw [h.slot, outB, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (by omega_arith),
    show (8 * i + u) / 32 = i / 4 by omega_arith, show (8 * i + u) % 32 / 8 = i % 4 by omega_arith,
    show (8 * i + u) % 8 = u by omega_arith] at this
  rw [this]
  have rd : ∀ {d e : Nat} {X : Nat → Word}, QW s.mem B d X → e = d + b / 4 →
      (W s.mem B e).getLsbD (32 * (b % 4) + (8 * (3 - i % 4) + u)) = (X b).getLsbD (8 * (3 - i % 4) + u) := fun hX e => by
    rw [e, hX.bit (by omega_arith) (by omega_arith) (by omega_arith), show 4 * (b / 4) + b % 4 = b by omega_arith]
  have ar := arrs
  rcases cases4 (show i / 4 < 4 by omega_arith) with e | e | e | e
  · rw [e]; exact rd (X := fun b => (x b).2.2.1) hx.2.2.1 (by omega_arith)
  · rw [e]; exact rd (X := fun b => (x b).2.2.2) hx.2.2.2 (by omega_arith)
  · rw [e]; exact rd (X := fun b => (x b).1) hx.1 (by omega_arith)
  · rw [e]; exact rd (X := fun b => (x b).2.1) hx.2.1 (by omega_arith)

/-- The block function, on sixteen blocks. -/
theorem cryptFn_wp (hs : Env0 112 s B) (hk : Keys s.mem B rk)
    (hB : s.gpr Impl.Modes.X86.sb = B) (hkr : s.gpr kr = B + BitVec.ofNat 32 (16 * 80))
    (htb : s.gpr tbr = s.syms tableName) (hc : s.gpr .ecx = BitVec.ofNat 32 8) :
    WP isa cryptFn s fun s' => At s B 32 s' ∧
      ∀ b < 16, Spec.Aes.bytesAt s'.mem (blk B b) 16 = (Spec.Seed.crypt (keyOf rk) (blkAt s.mem B b)).toList := by
  have h : At s B 0 s := ⟨hB, rfl, hkr, htb, rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  obtain ⟨s₁, r₁, a₁, g₁, x₁⟩ := blocksIn_ok h hs.slots (by decide)
  refine WP.seq (WP.of_runBlock ⟨s₁, r₁, WP.seq (WP.mono (loop_wp hs hk a₁ x₁ (by rw [g₁, hc])) fun s₂ ⟨a₂, x₂⟩ => ?_)⟩)
  obtain ⟨s₃, r₃, a₃, v₃⟩ := blocksOut_ok a₂ hs.slots (by decide) x₂
  exact WP.of_runBlock ⟨s₃, r₃, a₃, fun b hb => by rw [v₃ b hb, Proof.Seed.crypt_eq]⟩

/-! ## The core's code -/

/-- The scratch buffer. -/
structure Scr (s : State) (B : BitVec 32) : Prop where
  wr : (⟨B.setWidth 64, 1832⟩ : Region) ∈ s.wr
  fit : B.toNat + 1832 ≤ 2 ^ 32

theorem Scr.slots (h : Scr s B) : SlotsIn 112 s B where
  acc k hk := ⟨_, h.wr, by
    have := h.fit
    rw [addr16 (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  fit := by have := h.fit; omega_arith

/-- The eight bytes below `esp` hold the two calls' return addresses. -/
theorem below8 {E : BitVec 32} (hE : 8 ≤ E.toNat) : Region.Sub (below (E - 4) 4) (below E 8) ∧ Region.Sub (below E 4) (below E 8) := by
  exact ⟨below_inner (sp := E) (a := 4) (k := 4) (by decide) hE, below_sub (by decide) hE⟩

/-- `crypt`: the block function, called. -/
theorem crypt_wp (hB : s.gpr Impl.Modes.X86.sb = B) (hs : Scr s B) (hk : Keys s.mem B rk)
    (htab : s.mem.readW (addr B 480) 32 = s.syms tableName) (hE : 8 ≤ (s.gpr .esp).toNat)
    (hst : Region.Disjoint (below (s.gpr .esp) 8) ⟨B.setWidth 64, 1832⟩) :
    WP isa crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.syms = s.syms ∧ Frame [slotsR B 0 80, below (s.gpr .esp) 8] s.mem s'.mem ∧
      W s'.mem B tblSlot = W s.mem B tblSlot ∧
      ∀ b < 16, Spec.Aes.bytesAt s'.mem (blk B b) 16 = (Spec.Seed.crypt (keyOf rk) (blkAt s.mem B b)).toList := by
  have hf := hs.fit
  obtain ⟨b8, b4⟩ := below8 hE
  refine WP.seq ?_
  show WP isa (.block (.mov tbr (.mem ⟨Impl.Modes.X86.sb, 480⟩) :: .mov .ecx (.imm 8) ::
    .mov kr (.reg Impl.Modes.X86.sb) :: [.alu .add kr (.imm 1280)])) s _
  refine Wp.wp_ldm hB ⟨_, List.mem_append_right _ hs.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by decide) (by decide)⟩ fun s₁ u₁ => ?_
  refine Wp.wp_movi fun s₂ u₂ => Wp.wp_mov fun s₃ u₃ => Wp.wp_addi fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sy₄ : s₄.syms = s.syms := by rw [u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  have sp₄ : s₄.gpr .esp = s.gpr .esp := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have B₄ : s₄.gpr Impl.Modes.X86.sb = B := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have t₄ : s₄.gpr tbr = s.syms tableName := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, htab]
  have c₄ : s₄.gpr .ecx = BitVec.ofNat 32 8 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl
  have k₄ : s₄.gpr kr = B + BitVec.ofNat 32 (16 * 80) := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hB]; rfl
  have hce : Frame [below (s.gpr .esp) 4] s.mem s₄.callEntry.mem := by
    rw [State.callEntry_mem, m₄, sp₄]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have keep : ∀ k < 112, W s₄.callEntry.mem B k = W s.mem B k := fun k hk => by
    refine W_frame hce (by omega_arith) fun r hr => ?_
    rw [List.mem_singleton] at hr; subst hr
    exact ((hst.sub_left b4).sub_right (Offset.sub_base _ (by omega_arith))).symm
  have hbs : bufS = 64 := rfl
  have kb : ∀ b < 16, blkAt s₄.callEntry.mem B b = blkAt s.mem B b := fun b hb => by
    simp only [blkAt, Spec.Seed.blockAt]
    congr 1
    funext i
    have hi := i.isLt
    refine hce.bytes (R := ⟨blk B b, 16⟩) (fun r hr => ?_) (by show (16 : Nat) ≤ 2 ^ 64; decide) hi
    rw [List.mem_singleton] at hr; subst hr
    exact ((hst.sub_left b4).sub_right (Offset.sub_base _ (by omega_arith))).symm
  have hs₄ : Scr s₄.callEntry B := ⟨by rw [State.callEntry_wr, wr₄]; exact hs.wr, hf⟩
  have e₄ : s₄.callEntry.gpr .esp = s.gpr .esp - 4 := by rw [State.callEntry_esp, sp₄]
  have he : Env0 112 s₄.callEntry B := ⟨hs₄.slots, by rw [e₄]; exact (hst.sub_left b8).sub_right (Region.sub_prefix (by decide))⟩
  refine WP.callBody (WP.mono (cryptFn_wp (rk := rk) he
    (fun i hi l hl => by rw [keep _ (by omega_arith)]; exact hk i hi l hl)
    (by rw [State.callEntry_gpr _ (by decide), B₄]) (by rw [State.callEntry_gpr _ (by decide), k₄])
    (by rw [State.callEntry_gpr _ (by decide), t₄]; exact (congrFun sy₄ _).symm) (by rw [State.callEntry_gpr _ (by decide), c₄]))
    fun u ⟨a, v⟩ => ⟨by rw [a.esp, State.callEntry_esp], ?_, ?_⟩)
  · have e := a.frame.readW (r := ⟨(s₄.gpr .esp - 4).setWidth 64, 4⟩) (a := (s₄.gpr .esp - 4).setWidth 64) (w := 32)
      (Region.contains_self _ 4) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [sp₄]
          exact (hst.sub_left b4).sub_right (Offset.sub_base _ (by decide))
        · rw [e₄, sp₄]
          have hn : (s.gpr .esp - 4).toNat = (s.gpr .esp).toNat - 4 := sub_toNat (k := 4) (by omega_arith)
          have hn' : (s.gpr .esp - 4 - BitVec.ofNat 32 4).toNat = (s.gpr .esp).toNat - 8 := by
            rw [sub_toNat (by omega_arith), hn]; omega_arith
          have eb : (s.gpr .esp - 4).setWidth 64 = (s.gpr .esp - 4 - BitVec.ofNat 32 4).setWidth 64 + BitVec.ofNat 64 4 := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth, hn, hn', BitVec.toNat_ofNat]
            have := (s.gpr .esp).isLt
            omega_arith
          show Region.Disjoint ⟨(s.gpr .esp - 4).setWidth 64, 4⟩ ⟨(s.gpr .esp - 4 - BitVec.ofNat 32 4).setWidth 64, 4⟩
          rw [eb]
          exact (Offset.base_disjoint _ (by decide) (by decide)).symm) (by decide)
    rw [e, State.callEntry_mem, Mem.readW_writeW_self32]
  · refine ⟨a.base, by simp [State.setReg, sp₄], a.rd.trans (by rw [State.callEntry_rd, rd₄]),
      a.wr.trans (by rw [State.callEntry_wr, wr₄]), a.syms.trans sy₄, ?_, ?_, fun b hb => ?_⟩
    · refine (hce.sub fun r hr => ?_).trans (a.frame.sub fun r hr => ?_)
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, b4⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [e₄]; exact b8⟩
    · exact a.tab.trans (keep _ (by decide))
    · rw [← kb b hb]; exact v b hb

/-! ## The round keys -/

/-- The two doublewords of eight bytes of memory. -/
theorem dword_readW64 (m : Mem) (a : Addr) {k : Nat} (hk : k < 2) :
    dword ((0 : BitVec 64) ++ m.readW a 64) k = m.readW (a + BitVec.ofNat 64 (4 * k)) 32 := by
  refine BitVec.eq_of_getLsbD_eq fun t ht => ?_
  have e1 := byte_readW m a (w := 64) (k := 4 * k + t / 8) (by omega_arith)
  have e2 := byte_readW m (a + BitVec.ofNat 64 (4 * k)) (w := 32) (k := t / 8) (by omega_arith)
  rw [Offset.add_ofNat_add_ofNat, ← e1] at e2
  have := congrArg (fun v : BitVec 8 => v.getLsbD (t % 8)) e2
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true (Nat.mod_lt t (show 0 < 8 by decide)), Bool.true_and] at this
  rw [getLsbD_dword, decide_eq_true ht, Bool.true_and, BitVec.getLsbD_append, ite_eq_left (by omega_arith),
    show 32 * k + t = 8 * (4 * k + t / 8) + t % 8 by omega_arith, ← this, show 8 * (t / 8) + t % 8 = t by omega_arith]

/-- The round of the schedule whose keys are the `j`th that `prepare` reads. -/
def ri : Direction → Nat → Nat
  | .encrypt, j => j
  | .decrypt, j => 15 - j

/-- What a step of `prepare`'s loop needs: the next keys read are the `j`th
of the schedule at `p` in the order of `d`, and those before are in their places. -/
structure Pr (s₁ : State) (B p : BitVec 32) (d : Direction) (F : Nat → Word) (j : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₁.gpr .esp
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  syms : s.syms = s₁.syms
  src : j < 16 → s.gpr .eax = p + BitVec.ofNat 32 (8 * ri d j)
  dst : s.gpr kr = B + BitVec.ofNat 32 (16 * (80 + 2 * j))
  frame : Frame [slotsR B 80 32] s₁.mem s.mem
  keys : ∀ i < 2 * j, KW s.mem B i (F i)

/-- The schedule, readable and apart from the scratch buffer. -/
structure SchIn (s₁ : State) (B p : BitVec 32) : Prop where
  rd : (⟨p.setWidth 64, 128⟩ : Region) ∈ s₁.rd ++ s₁.wr
  fit : p.toNat + 128 ≤ 2 ^ 32
  dis : Region.Disjoint ⟨p.setWidth 64, 128⟩ ⟨B.setWidth 64, 1832⟩

theorem store128_eq {t : State} {a : Addr} {v : BitVec 128} (h : InRegions t.wr a 16) :
    t.store128 a v = some { t with mem := t.mem.writeW a v } := by
  simp only [State.store128, h, ite_true]

/-- `prepOne`, on the machine. -/
theorem prepOne_run {p q q' : Addr} (hp : addr (s.gpr .eax) 0 = p) (hq : addr (s.gpr kr) 0 = q) (hq' : addr (s.gpr kr) 16 = q')
    (hin : InRegions (s.rd ++ s.wr) p 8) (hout : InRegions s.wr q 16) (hout' : InRegions s.wr q' 16)
    {V : BitVec 128} (hV : V = (0 : BitVec 64) ++ s.mem.readW p 64) {is : List Instr} {Q : State → Prop}
    (K : ∀ u : State, u.gpr = s.gpr → u.rd = s.rd → u.wr = s.wr → u.syms = s.syms →
      u.mem = (s.mem.writeW q (shufDwords V 0x00)).writeW q' (shufDwords V 0x55) → WP isa (.block is) u Q) :
    WP isa (.block (prepOne ++ is)) s Q := by
  have r0 : exec (.movqLoad .xmm0 (Impl.Modes.X86.at_ .eax 0)) s = some (s.setXmm .xmm0 V) := by
    show (s.load64 (addr (s.gpr .eax) 0)).map _ = _
    rw [hp, hV]
    simp only [State.load64, hin, ite_true, Option.map_some]
  obtain ⟨t, ht⟩ : ∃ t : State, t = (s.setXmm .xmm0 V).setXmm .xmm1 (shufDwords V 0x00) := ⟨_, rfl⟩
  have r1 : exec (.xop (.pshufd .xmm1 .xmm0 0x00)) (s.setXmm .xmm0 V) = some t := by rw [ht]; rfl
  obtain ⟨t', ht'⟩ : ∃ t' : State, t' = { t with mem := t.mem.writeW q (t.xmm .xmm1) } := ⟨_, rfl⟩
  have r2 : exec (stx kr 0 .xmm1) t = some t' := by
    show t.store128 (addr (t.gpr kr) 0) (t.xmm .xmm1) = _
    rw [show addr (t.gpr kr) 0 = q by rw [ht]; exact hq, store128_eq (by rw [ht]; exact hout), ht']
  obtain ⟨w', hw⟩ : ∃ w' : State, w' = t'.setXmm .xmm1 (shufDwords V 0x55) := ⟨_, rfl⟩
  have r3 : exec (.xop (.pshufd .xmm1 .xmm0 0x55)) t' = some w' := by rw [hw, ht', ht]; rfl
  have r4 : exec (stx kr 16 .xmm1) w' = some { w' with mem := w'.mem.writeW q' (w'.xmm .xmm1) } := by
    show w'.store128 (addr (w'.gpr kr) 16) (w'.xmm .xmm1) = _
    rw [show addr (w'.gpr kr) 16 = q' by rw [hw, ht', ht]; exact hq', store128_eq (by rw [hw, ht', ht]; exact hout')]
  have hpr : prepOne ++ is = .movqLoad .xmm0 (Impl.Modes.X86.at_ .eax 0) :: .xop (.pshufd .xmm1 .xmm0 0x00) :: stx kr 0 .xmm1 ::
    .xop (.pshufd .xmm1 .xmm0 0x55) :: stx kr 16 .xmm1 :: is := rfl
  rw [hpr]
  exact Wp.cons r0 (Wp.cons r1 (Wp.cons r2 (Wp.cons r3 (Wp.cons r4 (K _ (by rw [hw, ht', ht]; rfl) (by rw [hw, ht', ht]; rfl)
    (by rw [hw, ht', ht]; rfl) (by rw [hw, ht', ht]; rfl) (by rw [hw, ht', ht]; rfl))))))

theorem prepOne_wp {s₁ : State} {p : BitVec 32} {d : Direction} {F : Nat → Word} {j : Nat} (hs : Scr s₁ B) (hp : SchIn s₁ B p)
    (h : Pr s₁ B p d F j s) (hj : j < 16)
    (hF : ∀ c < 2, F (2 * j + c) = s₁.mem.readW (p.setWidth 64 + BitVec.ofNat 64 (4 * (2 * ri d j + c))) 32)
    {is : List Instr} {Q : State → Prop}
    (K : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → Frame [slotsR B 80 32] s₁.mem s'.mem →
      (∀ i < 2 * (j + 1), KW s'.mem B i (F i)) → WP isa (.block is) s' Q) :
    WP isa (.block (prepOne ++ is)) s Q := by
  have hf := hs.fit
  have hpf := hp.fit
  have hri : ri d j < 16 := by cases d <;> simp only [ri] <;> omega_arith
  have ea : addr (s.gpr .eax) 0 = p.setWidth 64 + BitVec.ofNat 64 (8 * ri d j) := by
    rw [h.src hj, Straight.addr_add_ofNat, Nat.add_zero, addr_eq (by omega_arith)]
  have ed : ∀ c < 2, addr (s.gpr kr) (16 * c) = B.setWidth 64 + BitVec.ofNat 64 (16 * (80 + 2 * j + c)) := fun c hc => by
    rw [h.dst, Straight.addr_add_ofNat, ← Nat.mul_add, addr_eq (by omega_arith)]
  have hin : ∀ c < 2, InRegions s.wr (B.setWidth 64 + BitVec.ofNat 64 (16 * (80 + 2 * j + c))) 16 := fun c hc =>
    ⟨_, by rw [h.wr]; exact hs.wr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain ⟨V, hV⟩ : ∃ V : BitVec 128, V = (0 : BitVec 64) ++ s.mem.readW (p.setWidth 64 + BitVec.ofNat 64 (8 * ri d j)) 64 := ⟨_, rfl⟩
  have hVd : ∀ c < 2, dword V c = F (2 * j + c) := fun c hc => by
    rw [hV, dword_readW64 _ _ hc, Offset.add_ofNat_add_ofNat, hF c hc, show 8 * ri d j + 4 * c = 4 * (2 * ri d j + c) by omega_arith]
    refine h.frame.readW (Region.contains_self _ 4) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton] at hr; subst hr
    exact (hp.dis.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by decide))
  refine prepOne_run ea (ed 0 (by decide)) (ed 1 (by decide))
    ⟨_, by rw [h.rd, h.wr]; exact hp.rd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ (hin 0 (by decide))
    (hin 1 (by decide)) hV fun u ug ur uw us um => K u ug ur uw us ?_ ?_
  · have fr : Frame [slotsR B 80 32] s.mem u.mem := by
      rw [um]
      refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
      · exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
    exact h.frame.trans fr
  · have f2 : Frame [slotsR B (80 + 2 * j + 1) 1] (s.mem.writeW (B.setWidth 64 + BitVec.ofNat 64 (16 * (80 + 2 * j + 0))) (shufDwords V 0x00)) u.mem := by
      rw [um]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
    have f1 : Frame [slotsR B (80 + 2 * j + 0) 1] s.mem (s.mem.writeW (B.setWidth 64 + BitVec.ofNat 64 (16 * (80 + 2 * j + 0))) (shufDwords V 0x00)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
    intro i hi l hl
    by_cases h2 : i < 2 * j
    · rw [W_frame f2 (by omega_arith) fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint (B.setWidth 64) (by omega_arith) (by omega_arith) (by omega_arith),
        W_frame f1 (by omega_arith) fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint (B.setWidth 64) (by omega_arith) (by omega_arith) (by omega_arith)]
      exact h.keys i h2 l hl
    · rcases (show i = 2 * j + 0 ∨ i = 2 * j + 1 by omega_arith) with rfl | rfl
      · rw [W_frame f2 (by omega_arith) fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint (B.setWidth 64) (by omega_arith) (by omega_arith) (by omega_arith)]
        rw [← Nat.add_assoc, W, addr16 (by omega_arith), Mem.readW_writeW_self _ _ 16 _ (by decide), ← hVd 0 (by decide)]
        exact dword_shufDwords_bcast V (k := 0) (by decide) hl
      · rw [um, ← Nat.add_assoc, W, addr16 (by omega_arith), Mem.readW_writeW_self _ _ 16 _ (by decide), ← hVd 1 (by decide)]
        exact dword_shufDwords_bcast V (k := 1) (by decide) hl

theorem add_back (p : BitVec 32) {a d : Nat} (h : d ≤ a) :
    p + BitVec.ofNat 32 (8 * a) - BitVec.ofNat 32 (8 * d) = p + BitVec.ofNat 32 (8 * (a - d)) := by
  rw [show 8 * a = 8 * (a - d) + 8 * d by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- On to the next round's keys. -/
theorem keyNext_wp {p : BitVec 32} {d : Direction} {j : Nat} (hj : j < 16) (ha : s.gpr .eax = p + BitVec.ofNat 32 (8 * ri d j))
    {is : List Instr} {Q : State → Prop}
    (K : ∀ s' v, Wp.Upd s s' .eax v → (j + 1 < 16 → v = p + BitVec.ofNat 32 (8 * ri d (j + 1))) → WP isa (.block is) s' Q) :
    WP isa (.block (keyNext d :: is)) s Q := by
  cases d
  · refine Wp.wp_addi fun s' u => K s' _ u fun _ => ?_
    rw [ha, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_ofNat_add_ofNat]
    rfl
  · refine Wp.wp_subi fun s' u _ _ => K s' _ u fun h => ?_
    rw [ha, show (8 : BitVec 32) = BitVec.ofNat 32 (8 * 1) from rfl, ri, add_back _ (by omega_arith), ri,
      show 15 - j - 1 = 15 - (j + 1) by omega_arith]

theorem prepLoop_wp {s₁ : State} {p : BitVec 32} {d : Direction} {F : Nat → Word} (hs : Scr s₁ B) (hp : SchIn s₁ B p)
    (hF : ∀ j < 16, ∀ c < 2, F (2 * j + c) = s₁.mem.readW (p.setWidth 64 + BitVec.ofNat 64 (4 * (2 * ri d j + c))) 32)
    (h : Pr s₁ B p d F 0 s) (hc : s.gpr .ecx = BitVec.ofNat 32 16) :
    WP isa (.loop (.block (prepOne ++ [keyNext d, .alu .add kr (.imm 32), .alu .sub .ecx (.imm 1)])) .ne) s
      fun s' => Pr s₁ B p d F 16 s' := by
  refine WP.loop (M := isa) (fun (c : Nat) (s' : State) => 1 ≤ c ∧ c ≤ 16 ∧ Pr s₁ B p d F (16 - c) s' ∧
    s'.gpr .ecx = BitVec.ofNat 32 c) ?_ 16 s ⟨by decide, by decide, by rw [Nat.sub_self]; exact h, hc⟩
  rintro c t ⟨h1, h2, a, hcx⟩
  refine prepOne_wp hs hp a (by omega_arith) (hF _ (by omega_arith)) fun s₂ g₂ rd₂ wr₂ sy₂ f₂ k₂ => ?_
  refine keyNext_wp (p := p) (d := d) (j := 16 - c) (by omega_arith) (by rw [g₂]; exact a.src (by omega_arith)) fun s₃ v u₃ hv => ?_
  refine Wp.wp_addi fun s₄ u₄ => Wp.wp_subi fun s₅ u₅ _ z₅ => WP.block_nil ?_
  have e₄ : s₄.gpr .ecx = BitVec.ofNat 32 c := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, hcx]
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have g₅ : ∀ r, r ≠ .ecx → r ≠ kr → r ≠ .eax → s₅.gpr r = t.gpr r := fun r h1 h2 h3 => by
    rw [u₅.other _ h1, u₄.other _ h2, u₃.other _ h3, g₂]
  have P : Pr s₁ B p d F (16 - (c - 1)) s₅ := by
    have e : 16 - (c - 1) = 16 - c + 1 := by omega_arith
    rw [e]
    refine ⟨(g₅ _ (by decide) (by decide) (by decide)).trans a.base, (g₅ _ (by decide) (by decide) (by decide)).trans a.esp,
      by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, a.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, a.wr],
      by rw [u₅.syms, u₄.syms, u₃.syms, sy₂, a.syms], fun hj => ?_, ?_, by rw [m₅]; exact f₂, by rw [m₅]; exact k₂⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; exact hv hj
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, a.dst, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
        Offset.add_ofNat_add_ofNat, show 16 * (80 + 2 * (16 - c)) + 32 = 16 * (80 + 2 * (16 - c + 1)) by omega_arith]
  have z : s₅.zf = some (decide (c = 1)) := by
    rw [z₅, e₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_arith) (by decide)]
  by_cases hc1 : c = 1
  · subst hc1
    exact .inl ⟨by show s₅.zf.map _ = _; rw [z]; rfl, P⟩
  · exact .inr ⟨by show s₅.zf.map _ = _; rw [z, decide_eq_false hc1]; rfl, c - 1, by omega_arith, by omega_arith, by omega_arith, P,
      by rw [u₅.gpr, e₄]; exact Wp.ofNat_pred h1⟩

/-- `ownTable` changes a register alone. -/
theorem ownTable_wp {s : State} (h : s.gpr .eax = s.syms tableName) {is : List Instr} {Q : State → Prop}
    (K : ∀ s' : State, s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      s'.zf = s.zf → s'.cf = s.cf → WP isa (.block is) s' Q) :
    WP isa (.block (ownTable :: is)) s Q := by
  have e : exec ownTable s = some (s.setXmm .xmm0 (tblAt Impl.Seed.X86.Sse.table 0)) := by
    simp only [ownTable, Impl.Modes.X86.at_, exec, h, show (0 : Nat) % 8 = 0 from rfl,
      show (0 : Nat) / 8 + 2 ≤ Impl.Seed.X86.Sse.table.length by decide, and_self, ite_true]
    rfl
  exact Wp.cons e (K _ rfl rfl rfl rfl rfl rfl rfl)

theorem prepHead_wp {d : Direction} {p : BitVec 32} (hB : s.gpr Impl.Modes.X86.sb = B) (hs : Scr s B)
    (hax : s.gpr .eax = s.syms tableName)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (Impl.Modes.X86.argOp 0)) 4) (hp : s.mem.readW (s.ea (Impl.Modes.X86.argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (Impl.Modes.X86.argOp 0), 4⟩ ⟨B.setWidth 64, 1832⟩) (F : Nat → Word) :
    WP isa (.block (prepHead d)) s fun s' => Pr s' B p d F 0 s' ∧ s'.gpr .ecx = BitVec.ofNat 32 16 ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧ Frame [slotsR B 30 1] s.mem s'.mem ∧
      s'.mem.readW (addr B 480) 32 = s.syms tableName := by
  have hf := hs.fit
  have ha : addr B 480 = B.setWidth 64 + BitVec.ofNat 64 480 := addr_eq (by omega_arith)
  have hw : InRegions s.wr (addr B 480) 4 := ⟨_, hs.wr, by
    rw [ha]; exact Offset.contains_base _ (by decide) (by decide)⟩
  show WP isa (.block (.store ⟨Impl.Modes.X86.sb, 480⟩ .eax :: ownTable :: .mov .eax (.mem ⟨.esp, 4 + 4 * 0⟩) ::
    .alu .add .eax (.imm (BitVec.ofNat 32 (keyAt d))) :: .mov kr (.reg Impl.Modes.X86.sb) :: .alu .add kr (.imm 1280) ::
    [.mov .ecx (.imm 16)])) s _
  refine Wp.wp_stm hB hw fun s₁ u₁ => ownTable_wp (by rw [u₁.gpr, u₁.syms]; exact hax) fun s₂ g₂ m₂ rd₂ wr₂ sy₂ z₂ c₂ => ?_
  have u₂ : Wp.Mupd s s₂ (s.mem.writeW (addr B 480) (s.gpr .eax)) :=
    ⟨g₂.trans u₁.gpr, m₂.trans u₁.mem, rd₂.trans u₁.rd, wr₂.trans u₁.wr, z₂.trans u₁.zf, c₂.trans u₁.cf, sy₂.trans u₁.syms⟩
  have f₂ : Frame [slotsR B 30 1] s.mem s₂.mem := by
    rw [u₂.mem, ha]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  have e0 : s₂.mem.readW (s.ea (Impl.Modes.X86.argOp 0)) 32 = p := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0B.sub_right (Offset.sub_base _ (by decide))) (by decide), hp]
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₂.gpr]) (by rw [u₂.rd, u₂.wr]; exact hin0) fun s₃ u₃ => ?_
  refine Wp.wp_addi fun s₄ u₄ => Wp.wp_mov fun s₅ u₅ => Wp.wp_addi fun s₆ u₆ => Wp.wp_movi fun s₇ u₇ => WP.block_nil ?_
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have g₇ : ∀ r, r ≠ .ecx → r ≠ kr → r ≠ .eax → s₇.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₇.other _ h1, u₆.other _ h2, u₅.other _ h2, u₄.other _ h3, u₃.other _ h3, u₂.gpr]
  refine ⟨⟨(g₇ _ (by decide) (by decide) (by decide)).trans hB, rfl, rfl, rfl, rfl, fun _ => ?_, ?_, Frame.refl _ _,
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩, u₇.gpr, g₇ _ (by decide) (by decide) (by decide),
    by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr],
    by rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms], by rw [m₇]; exact f₂, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr,
      show s₂.mem.readW (addr (s.gpr .esp) (4 + 4 * 0)) 32 = p from e0]
    cases d <;> rfl
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hB]; rfl
  · rw [m₇, u₂.mem, Mem.readW_writeW_self32, hax]

open VG.Proof.Seed.X86.AesNiWide (pos pos_lt pos_decrypt)

theorem pos_ri (d : Direction) {j c : Nat} (hj : j < 16) (hc : c < 2) : pos d (2 * j + c) = 2 * ri d j + c := by
  cases d
  · rfl
  · have := pos_decrypt hj
    rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl
    · exact this.1
    · exact this.2

/-- The round keys in `d`'s order. -/
abbrev rkOf (d : Direction) (k : Spec.Seed.Schedule) : Nat → Word := fun i => k.getD (pos d i) 0

theorem rkOf_at (d : Direction) (m : Mem) (p : Addr) {j c : Nat} (hj : j < 16) (hc : c < 2) :
    rkOf d (Spec.Seed.scheduleAt m p) (2 * j + c) = m.readW (p + BitVec.ofNat 64 (4 * (2 * ri d j + c))) 32 := by
  have hri : ri d j < 16 := by cases d <;> simp only [ri] <;> omega_arith
  rw [rkOf, pos_ri d hj hc, Proof.Seed.vector_getD _ _ (by omega_arith), Proof.Seed.scheduleAt_readW _ _ _ (by omega_arith)]

/-- `prepare d` leaves the schedule's round keys in `d`'s order, each in every
doubleword of its slot, and the table's address, in their slots. -/
theorem prepare_wp {d : Direction} {p : BitVec 32} (hB : s.gpr Impl.Modes.X86.sb = B) (hs : Scr s B)
    (hesp : 4 ≤ (s.gpr .esp).toNat)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (Impl.Modes.X86.argOp 0)) 4) (hp : s.mem.readW (s.ea (Impl.Modes.X86.argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (Impl.Modes.X86.argOp 0), 4⟩ ⟨B.setWidth 64, 1832⟩)
    (hsch : SchIn s B p)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨p.setWidth 64, 128⟩)
    (h0S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (Impl.Modes.X86.argOp 0), 4⟩) :
    WP isa (prepare d) s fun s' => Keys s'.mem B (rkOf d (Spec.Seed.scheduleAt s.mem (p.setWidth 64))) ∧
      s'.mem.readW (addr B 480) 32 = s.syms tableName ∧ s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64, 1792⟩, below (s.gpr .esp) 4] s.mem s'.mem := by
  have hf := hs.fit
  refine WP.seq (WP.mono (symFrame_ok tableName s hesp) fun s₁ a₁ => ?_)
  have esp₁ : s₁.gpr .esp = s.gpr .esp := a₁.gpr .esp (by decide)
  have ea₁ : s₁.ea (Impl.Modes.X86.argOp 0) = s.ea (Impl.Modes.X86.argOp 0) := by
    show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
    rw [esp₁]
  have hs₁ : Scr s₁ B := ⟨by rw [a₁.wr]; exact hs.wr, hf⟩
  refine WP.seq (WP.mono (prepHead_wp (d := d) (p := p) (F := rkOf d (Spec.Seed.scheduleAt s.mem (p.setWidth 64)))
    ((a₁.gpr _ (by decide)).trans hB) hs₁ (by rw [a₁.addr, a₁.syms])
    (by rw [ea₁, a₁.rd, a₁.wr]; exact hin0)
    (by rw [ea₁, a₁.frame.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0S.symm) (by decide), hp]) (by rw [ea₁]; exact h0B))
    fun s₂ ⟨P, c, esp₂, rd₂, wr₂, sy₂, F₂, t₂⟩ => ?_)
  have hs₂ : Scr s₂ B := ⟨by rw [wr₂]; exact hs₁.wr, hf⟩
  have hsch₂ : SchIn s₂ B p := ⟨by rw [rd₂, wr₂, a₁.rd, a₁.wr]; exact hsch.rd, hsch.fit, hsch.dis⟩
  have esch : Spec.Seed.scheduleAt s₂.mem (p.setWidth 64) = Spec.Seed.scheduleAt s.mem (p.setWidth 64) := by
    rw [Proof.Seed.scheduleAt_frame F₂ fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact hsch.dis.sub_right (Offset.sub_base _ (by decide)),
      Proof.Seed.scheduleAt_frame a₁.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact hkS.symm]
  refine WP.mono (prepLoop_wp hs₂ hsch₂ (fun j hj c hc => by rw [← esch, rkOf_at d _ _ hj hc]) P c) fun s' Q => ?_
  refine ⟨fun i hi => Q.keys i (by omega_arith), ?_, Q.base, Q.esp.trans (esp₂.trans esp₁), Q.rd.trans (rd₂.trans a₁.rd),
    Q.wr.trans (wr₂.trans a₁.wr), Q.syms.trans (sy₂.trans a₁.syms), ?_⟩
  · rw [Q.frame.readW (r := ⟨addr B 480, 4⟩) (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      rw [show addr B 480 = B.setWidth 64 + BitVec.ofNat 64 480 from addr_eq (by omega_arith)]
      exact Offset.disjoint (B.setWidth 64) (by decide) (by decide) (by decide)) (by decide), t₂, a₁.syms]
  · refine ((a₁.frame.mono fun r hr => ?_).trans (F₂.sub fun r hr => ?_)).trans (Q.frame.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩

end

/-! ## The core -/

section

open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)
open VG.Proof.Seed (dirCipher)
open VG.Proof.Seed.X86.AesNiWide (pos dirCipher_bytes)

/-- The key's arguments, as of the cores by the AES S-box, the eight bytes
below `esp`, where `crypt` calls the block function and that calls `G`, apart
from the mode's regions too. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  AesNi.KeyArgs s rs k ∧ 8 ≤ (s.gpr .esp).toNat ∧ ∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .esp) 8) r

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k :=
  ⟨AesNi.keyArgs_congr h.1 hesp hrd hwr hf, by rw [hesp]; exact h.2⟩

/-- The key `k` is ready, for the direction `d`, in the scratch buffer at `B`. -/
structure Ready (d : Direction) (s : State) (B : BitVec 32) (k : Spec.Seed.Schedule) : Prop where
  keys : Keys s.mem B (rkOf d k)
  tab : s.mem.readW (addr B 480) 32 = s.syms tableName
  fit : B.toNat + 1832 ≤ 2 ^ 32
  esp : 8 ≤ (s.gpr .esp).toNat
  stk : Region.Disjoint (stkRegion (s.gpr .esp) 8) ⟨B.setWidth 64, 1832⟩

theorem ready_frame {d : Direction} {s s' : State} {B : BitVec 32} {k : Spec.Seed.Schedule} {rs : List Region}
    (h : Ready d s B k) (hesp : s'.gpr .esp = s.gpr .esp) (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (core d) B) r ∨ Region.Sub r (blkRegion (core d) B)) :
    Ready d s' B k := by
  have hfit := h.fit
  have keep : ∀ {a n : Nat}, (a + n ≤ 1024 ∨ 1280 ≤ a) → a + n ≤ 1792 → ∀ r ∈ rs,
      Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩ r := fun {a n} h₁ h₂ r hr => by
    rcases hd r hr with h | h
    · exact h.sub_left (Offset.sub_base _ (by show a + n ≤ 4 * 448; omega_arith))
    · exact (Offset.disjoint (B.setWidth 64) (d := a) (n := n) (e := 4 * 256) (k := 4 * 4 * 16)
        (by omega_arith) (by omega_arith) (by decide)).sub_right h
  refine ⟨fun i hi l hl => ?_, ?_, hfit, by rw [hesp]; exact h.esp, by rw [hesp]; exact h.stk⟩
  · rw [W_frame hf (by omega_arith) (keep (by omega_arith) (by omega_arith))]
    exact h.keys i hi l hl
  · have ha : addr B 480 = B.setWidth 64 + BitVec.ofNat 64 480 := addr_eq (by omega_arith)
    rw [hsy, ← h.tab, ha]
    exact hf.readW (Region.contains_self _ 4) (keep (by decide) (by decide)) (by decide)

theorem prepare_ok {d : Direction} {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (core d).total)
    (hR : (⟨B.setWidth 64, 4 * (core d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (core d).prepare s fun s' => Ready d s' B k ∧ s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (core d) B, stkRegion (s.gpr .esp) (core d).stack] s.mem s'.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨⟨p, hin0, hp, hkk, hsch, hfit, hdis, hd0, hkS, h0S⟩, hE, hst⟩ := hk
  refine WP.mono (prepare_wp (d := d) hB ⟨hs.wr, hs.fit⟩ (Nat.le_trans (by decide) hE) hin0 hp (hd0 _ hR) ⟨hsch, hfit, hdis _ hR⟩ hkS h0S)
    fun s' ⟨K, t, b, e, rd, wr, sy, f⟩ => ?_
  refine ⟨⟨by rw [hkk]; exact K, by rw [t, sy], hs.fit, by rw [e]; exact hE, by rw [e]; exact hst _ hR⟩, b, e, f.sub fun r hr => ?_, rd, wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, (below8 hE).2⟩

theorem crypt_ok {d : Direction} {s : State} {B : BitVec 32} {k : Spec.Seed.Schedule} (hB : s.gpr Impl.Modes.X86.sb = B)
    (hs : VG.Proof.Modes.X86.ScrIn s B (core d).total) (hr : Ready d s B k) :
    WP isa (core d).crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready d s' B k ∧
      Frame [coreRegion (core d) B, stkRegion (s.gpr .esp) (core d).stack] s.mem s'.mem ∧
      (∀ j < (core d).G, Spec.Aes.bytesAt s'.mem (blkAddr (core d) B j) (4 * (core d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (core d) B j) (4 * (core d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit := hr.fit
  have hblk : ∀ j, blkAddr (core d) B j = blk B j := fun j => by
    show B.setWidth 64 + BitVec.ofNat 64 (4 * 256) + BitVec.ofNat 64 (4 * 4 * j) = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun z => B.setWidth 64 + BitVec.ofNat 64 z) (by show 4 * 256 + 4 * 4 * j = 16 * (64 + j); omega_arith)
  refine WP.mono (crypt_wp hB ⟨hs.wr, hs.fit⟩ hr.keys hr.tab hr.esp hr.stk) fun s' ⟨b, e, rd, wr, sy, f, tb, v⟩ => ?_
  refine ⟨b, e, ⟨fun i hi l hl => ?_, ?_, hfit, by rw [e]; exact hr.esp, by rw [e]; exact hr.stk⟩, f.sub fun r hr' => ?_, fun j hj => ?_, rd, wr⟩
  · rw [W_frame f (by omega_arith) fun r hr' => ?_]
    · exact hr.keys i hi l hl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact Offset.disjoint (B.setWidth 64) (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact (hr.stk.sub_right (Offset.sub_base _ (by omega_arith))).symm
  · have e1 : ∀ m : Mem, m.readW (addr B 480) 32 = (W m B tblSlot).extractLsb' 0 32 := fun m => by
      have := dword_readW m (addr B 480) (j := 0) (by decide)
      rw [Nat.mul_zero, BitVec.add_zero] at this
      exact this.symm
    rw [e1, tb, ← e1, sy]; exact hr.tab
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by show 16 * 0 + 16 * 80 ≤ 4 * 448; decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · show Spec.Aes.bytesAt s'.mem (blkAddr (core d) B j) 16 =
      dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (core d) B j) 16)
    rw [hblk, dirCipher_bytes]
    exact v j hj

/-- SEED's core of sixteen blocks meets what the modes need, in the
direction `d`. -/
def coreSpec (d : Direction) : CoreSpec (core d) where
  Key := Spec.Seed.Schedule
  cipher k := dirCipher d k
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, core]
  layout := ⟨by show 0 < 16; decide, .inr rfl, by show 256 + 4 * 16 ≤ 448; decide, by show 448 + 10 ≤ 458; decide⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h e _ _ sy f _ hd := ready_frame h e sy f hd
  prepare_wp hB hs hR hk _ := prepare_ok hB hs hR hk
  crypt_wp hB hs hr _ := crypt_ok hB hs hr

end

end VG.Proof.Seed.X86.Sse
