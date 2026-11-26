module

public import VerifiedGarbage.Proof.Framework.X86.StraightSse
public import VerifiedGarbage.Impl.Camellia.X86.Sse
public import VerifiedGarbage.Proof.Camellia.Bitsliced
public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideCore
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.SymFrame

/-!
# Camellia's core on x86 (32-bit) in XMM registers

`coreSpec`: the core of `Impl/Camellia/X86/Sse.lean`, which enciphers sixteen
blocks at a time, is Camellia, as the modes' proofs need it
(`Modes.X86.CoreSpec`), in either direction.

The kernel evaluates the straight-line pieces of the code (`StraightSse`):
the linear ones (a half's planes with a subkey, the rotations and `P` with
the other half, the blocks to planes and back) bit by bit in the lanes
domain, the S-box in truth tables, on every byte at once, and what prepares
a subkey as expressions. From these checks, with `byteOf` a byte of a half:

* `PAt`: eight slots hold the planes of sixteen halves, and `At` a state in
  the middle of the block function, at a subkey;
* `round_ok`, `whiten_ok`, `fl_ok`, `flinv_ok`, `blocksIn_ok`,
  `blocksOut_ok`: each piece on the planes is the specification's function
  on every block's halves;
* `cryptFn_wp`, `crypt_wp`: the block function, and the core's call of it;
* `prepare_wp`: the subkeys as the block function reads them (`Ready`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.Sse

open VG VG.X86 VG.X86.StraightSse VG.Bitslice VG.Impl.Camellia.X86.Sse
open VG.Spec.Camellia (sbox1)
open VG.Impl.Camellia.X86 (Dir)
open VG.Proof.Camellia (byteOf pRow)

/-! ## The kernel's checks -/

def cfg : Cfg := ⟨Impl.Modes.X86.sb, 60, kr, 4, tbr, tableName, table⟩

def inS (i j : Nat) : Nat := if i = 3 ∨ i = 6 then (j + 7) % 8 else j
def outS (i j : Nat) : Nat :=
  if i = 1 ∨ i = 4 then (j + 7) % 8 else if i = 2 ∨ i = 5 then (j + 1) % 8 else j

def planesIn (d : Nat) (w : Nat) : List (Nat × Nat × BitVec 128) := (List.range 8).map fun j => (d + j, w + j, 0)

def keyInG (q j p : Nat) : List Nat :=
  [128 * inS (p / 16) j + p, 128 * (8 + q) + 16 * (p / 16) + inS (p / 16) j]

noncomputable def roundInOk (q src : Nat) : Bool :=
  check (ofDom (lanes 128 11)) cfg (linExt 8 0) (roundIn src (16 * q)) (linEnv (planesIn src 0))
    (linPost 60 11 ((List.range 8).map fun j => (j, keyInG q j)))

theorem roundIn_chk1 : roundInOk 2 d1 = true := by kernel_rfl

def sboxEnv : Env Nat := { reg := fun _ => none, slot := fun k => if k < 8 then some (tableOf (fun c => c.testBit k) 256) else none }
noncomputable def sboxOk : Bool :=
  check (ofDom (table 128 256)) cfg (fun _ => none) sboxCode sboxEnv fun e =>
    (List.range 8).all fun j => e.slot j ==
      some (tableOf (fun c => (sbox1 (BitVec.ofNat 8 c ^^^ 0xc5#8) ^^^ 0x6e#8).getLsbD j) 256)
theorem sbox_chk : sboxOk = true := by kernel_rfl

def c6e (j : Nat) : BitVec 128 := if wBit j then BitVec.allOnes 128 else 0
def roundOutG (j p : Nat) : List Nat :=
  (128 * (8 + j) + p) :: (pRow (p / 16)).map fun i => 128 * outS i j + 16 * i + p % 16
noncomputable def roundOutOk (dst : Nat) : Bool :=
  check (ofDom (lanes 128 11)) cfg (fun _ => none) (roundOut dst)
    (linEnv ((List.range 8).map (fun j => (j, j, c6e j)) ++ planesIn dst 8))
    (linPost 60 11 ((List.range 8).map fun j => (dst + j, roundOutG j)))
theorem roundOut_chk1 : roundOutOk d1 = true := by kernel_rfl

theorem roundOut_chk2 : roundOutOk d2 = true := by kernel_rfl
theorem roundIn_chk2 : roundInOk 3 d2 = true := by kernel_rfl

/-- The blocks' planes. -/
def inG (h j p : Nat) : List Nat := [128 * (p % 16) + 8 * (8 * h + p / 16) + j]
noncomputable def blocksInOk : Bool :=
  check (ofDom (lanes 128 11)) cfg (fun _ => none) blocksIn
    (linEnv ((List.range 16).map fun b => (bufS + b, b, 0)))
    (linPost 60 11 (((List.range 8).map fun j => (d1 + j, inG 0 j)) ++ ((List.range 8).map fun j => (d2 + j, inG 1 j))))
theorem blocksIn_chk : blocksInOk = true := by kernel_rfl

def outG (b t : Nat) : List Nat :=
  [if t < 64 then 128 * (8 + t % 8) + 16 * (t / 8) + b else 128 * (t % 8) + 16 * (t / 8 - 8) + b]
noncomputable def blocksOutOk : Bool :=
  check (ofDom (lanes 128 11)) cfg (fun _ => none) blocksOut (linEnv (planesIn d1 0 ++ planesIn d2 8))
    (linPost 60 11 ((List.range 16).map fun b => (bufS + b, outG b)))
theorem blocksOut_chk : blocksOutOk = true := by kernel_rfl

/-- The whitening. -/
def uW : BitVec 128 := 0x00c500e200c500c500e200c500c500c5#128
def whitenG (q j p : Nat) : List Nat := [128 * j + p, 128 * (8 + q) + 16 * (p / 16) + j]
noncomputable def whitenOk (q d : Nat) : Bool :=
  check (ofDom (lanes 128 11)) cfg (linExt 8 uW) (whiten (16 * q) d) (linEnv (planesIn d 0))
    (linPost 60 11 ((List.range 8).map fun j => (d + j, whitenG q j)))
theorem whiten_chk : (whitenOk 0 d1 && whitenOk 1 d2 && whitenOk 2 d2 && whitenOk 3 d1) = true := by kernel_rfl

/-! ## FL -/
def kE (j : Nat) : XE := .un (.shift .psraw 15) (.un (.shift .pslld (BitVec.ofNat 8 (15 - j))) (.atom 8))
def rotE : Nat → XE
  | 0 => .bin .pxor (.atom 0) (.un (.shift .pslldq 8) (.un (.pshuflw 0x39) (.bin .pand (.atom 7) (kE 7))))
  | j + 1 => .bin .pxor (.atom (j + 1)) (.un (.shift .pslldq 8) (.bin .pand (rotE j) (kE j)))
def orE (j : Nat) : XE :=
  .bin .pxor (.atom j) (.un (.shift .psrldq 8) (.bin .por (kE j) (.atom j)))
def flEnv (d : Nat) : Env XE :=
  { reg := fun r => if r = .xmm6 then some (.atom 8) else none,
    slot := fun k => if d ≤ k ∧ k < d + 8 then some (.atom (k - d)) else none }
noncomputable def flOk (is : List Instr) (d : Nat) (E : Nat → XE) : Bool :=
  check exprs cfg (fun _ => none) is (flEnv d) fun e => (List.range 8).all fun j => e.slot (d + j) == some (E j)
def rots (d : Nat) : List Instr := (List.range 8).flatMap (flRot d)
def ors (d : Nat) : List Instr := (List.range 8).flatMap (flOr d)
theorem fl_chk : (flOk (rots d1) d1 rotE && flOk (ors d1) d1 orE && flOk (rots d2) d2 rotE && flOk (ors d2) d2 orE) = true := by
  kernel_rfl

noncomputable def ldKOk (r : Nat) : Bool :=
  check exprs cfg (fun n => some (.atom n)) (ldK (16 * r)) ⟨fun _ => none, fun _ => none⟩ fun e =>
    e.reg .xmm6 == some (.bin .pxor (.atom r) (.const uW))
theorem ldK_chk : (ldKOk 2 && ldKOk 3) = true := by kernel_rfl

/-! ## The slots each part stores -/
def storesOk (is : List Instr) (p : Nat → Bool) : Bool := (stored cfg is).all p
def parts : Bool :=
  storesOk (roundIn d1 32) (· < 8) && storesOk (roundIn d2 48) (· < 8) && storesOk sboxCode (· < 26) &&
  storesOk (roundOut d1) (fun k => 28 ≤ k && k < 36) && storesOk (roundOut d2) (fun k => 36 ≤ k && k < 44) &&
  storesOk (rots d1 ++ ors d1 ++ whiten 0 d1 ++ whiten 48 d1) (fun k => 28 ≤ k && k < 36) &&
  storesOk (rots d2 ++ ors d2 ++ whiten 16 d2 ++ whiten 32 d2) (fun k => 36 ≤ k && k < 44)
theorem parts_chk : parts = true := by kernel_rfl

theorem parts_chk2 : (storesOk blocksIn (fun k => 28 ≤ k && k < 44) && storesOk blocksOut (fun k => 28 ≤ k && k < 60)) = true := by
  kernel_rfl

theorem parts_fl : (storesOk (rots d1) (fun k => d1 ≤ k && k < d1 + 8) && storesOk (ors d1) (fun k => d1 ≤ k && k < d1 + 8) &&
    storesOk (rots d2) (fun k => d2 ≤ k && k < d2 + 8) && storesOk (ors d2) (fun k => d2 ≤ k && k < d2 + 8)) = true := by
  kernel_rfl
def no6 (is : List Instr) : Bool := is.all fun i => xdst i != some .xmm6
theorem fl_no6 : (no6 (rots d1) && no6 (ors d1) && no6 (rots d2) && no6 (ors d2)) = true := by kernel_rfl

theorem parts_rounds : (storesOk (roundIn d1 (16 * 2)) (· < 8) && storesOk (roundOut d2) (fun k => d2 ≤ k && k < d2 + 8) &&
    storesOk (roundIn d2 (16 * 3)) (· < 8) && storesOk (roundOut d1) (fun k => d1 ≤ k && k < d1 + 8)) = true := by kernel_rfl

theorem parts_whiten : (storesOk (whiten (16 * 0) d1) (fun k => d1 ≤ k && k < d1 + 8) && storesOk (whiten (16 * 1) d2) (fun k => d2 ≤ k && k < d2 + 8) &&
    storesOk (whiten (16 * 2) d2) (fun k => d2 ≤ k && k < d2 + 8) && storesOk (whiten (16 * 3) d1) (fun k => d1 ≤ k && k < d1 + 8)) = true := by kernel_rfl

/-! ## The subkeys -/

/-- No slots and no external words. -/
def cfg0 : Cfg := ⟨Impl.Modes.X86.sb, 0, kr, 0, tbr, tableName, table⟩
def prepMid : List Instr := [mv .xmm1 .xmm0, x .pand .xmm0 .xmm7, sh .psrld .xmm1 8, x .pand .xmm1 .xmm7,
   x .punpcklwd .xmm0 .xmm1, x .pxor .xmm0 .xmm6]
def prepEnv : Env XE :=
  { reg := fun | .xmm0 => some (.atom 0) | .xmm6 => some (.atom 6) | .xmm7 => some (.atom 7) | _ => none, slot := fun _ => none }
theorem prepMid_chk : check exprs cfg0 (fun _ => none) prepMid prepEnv (fun e => e.reg .xmm0 ==
    some (.bin .pxor (.bin .punpcklwd (.bin .pand (.atom 0) (.atom 7))
      (.bin .pand (.un (.shift .psrld 8) (.atom 0)) (.atom 7))) (.atom 6))) = true := by kernel_rfl

/-! ## The layout -/

/-- The eight planes from slot `d` on hold the halves `x b` of sixteen blocks. -/
def PAt (m : Mem) (B : BitVec 32) (d : Nat) (x : Nat → BitVec 64) : Prop :=
  ∀ b < 16, ∀ i < 8, ∀ j < 8, (W m B (d + j)).getLsbD (16 * i + b) = (byteOf (x b) i).getLsbD j

/-- The form a subkey is kept in, without `uW`: byte `i` in lane `i`. -/
def spread (k : BitVec 64) : BitVec 128 :=
  ofBits 128 fun p => decide (p % 16 < 8) && (byteOf k (p / 16)).getLsbD (p % 16)

theorem spread_bit (k : BitVec 64) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (spread k).getLsbD (16 * i + j) = (byteOf k i).getLsbD j := by
  rw [spread, getLsbD_ofBits, show (16 * i + j) % 16 = j by omega_arith, show (16 * i + j) / 16 = i by omega_arith,
    decide_eq_true (show 16 * i + j < 128 by omega_arith), decide_eq_true hj]
  rfl

theorem PAt.frame {m m' : Mem} {B : BitVec 32} {d : Nat} {x : Nat → BitVec 64} (h : PAt m B d x)
    (e : ∀ j < 8, W m' B (d + j) = W m B (d + j)) : PAt m' B d x := fun b hb i hi j hj => by
  rw [e j hj]; exact h b hb i hi j hj

/-! ## A round -/

/-- The scratch buffer. -/
structure Scr (s : State) (B : BitVec 32) : Prop where
  wr : (⟨B.setWidth 64, 1544⟩ : Region) ∈ s.wr
  fit : B.toNat + 1544 ≤ 2 ^ 32

theorem Scr.slots {s : State} {B : BitVec 32} (h : Scr s B) : SlotsIn 94 s B where
  acc k hk := ⟨_, h.wr, by
    have := h.fit
    rw [addr16 (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  fit := by have := h.fit; omega_arith

/-- What every part of the block's code needs of the state, with the subkeys
from the `q`th on at `kr`. -/
structure At (s₀ : State) (B : BitVec 32) (q : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  kp : s.gpr kr = B + BitVec.ofNat 32 (16 * (60 + q))
  tb : s.gpr tbr = s₀.syms tableName
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  frame : Frame [slotsR B 0 60] s₀.mem s.mem
  tab : W s.mem B tblSlot = W s₀.mem B tblSlot

section
variable {s₀ s : State} {B : BitVec 32} {q m : Nat}

theorem At.ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) : Ok cfg s := by
  have hf := hs.fit
  have hkr : (B + BitVec.ofNat 32 (16 * (60 + q))).toNat = B.toNat + 16 * (60 + q) :=
    Straight.toNat_add_off (by omega_arith)
  have e1 : ∀ k < 60, xAddr (s.gpr cfg.base) k = B.setWidth 64 + BitVec.ofNat 64 (16 * k) := fun k hk => by
    show addr (s.gpr Impl.Modes.X86.sb) _ = _
    rw [h.base, addr16 (by omega_arith)]
  have e2 : ∀ k < 4, xAddr (s.gpr cfg.ext) k = B.setWidth 64 + BitVec.ofNat 64 (16 * (60 + q + k)) := fun k hk => by
    show addr (s.gpr kr) _ = _
    rw [h.kp, Straight.addr_add_ofNat, ← Nat.mul_add, addr16 (by omega_arith)]
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk j hj => ?_, ?_⟩
  · have hk : k < 60 := hk
    rw [e1 k hk, h.wr, ← addr16 (by omega_arith)]
    exact hs.acc _ (by omega_arith)
  · have hk : k < 4 := hk
    rw [e2 k hk, h.rd, h.wr, ← addr16 (by omega_arith)]
    obtain ⟨r, hr, hc⟩ := hs.acc (60 + q + k) (by omega_arith)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · show (s.gpr Impl.Modes.X86.sb).toNat + 16 * 60 ≤ _
    rw [h.base]; omega_arith
  · rw [e1 k hk, e2 j hj]
    have hk : k < 60 := hk
    have hj : j < 4 := hj
    intro x h₁ h₂
    exact Offset.disjoint (B.setWidth 64) (d := 16 * k) (n := 16) (e := 16 * (60 + q + j)) (k := 16)
      (by omega_arith) (by omega_arith) (by omega_arith) x h₁ h₂
  · show s.gpr tbr = s.syms tableName
    rw [h.tb, h.syms]

theorem At.ext (h : At s₀ B q s) (k : Nat) :
    s.mem.readW (xAddr (s.gpr cfg.ext) k) 128 = W s.mem B (60 + q + k) := by
  show s.mem.readW (addr (s.gpr kr) _) 128 = _
  rw [h.kp, Straight.addr_add_ofNat, ← Nat.mul_add]; rfl

theorem At.slot (h : At s₀ B q s) (k : Nat) :
    s.mem.readW (xAddr (s.gpr cfg.base) k) 128 = W s.mem B k := by
  show s.mem.readW (addr (s.gpr Impl.Modes.X86.sb) _) 128 = _
  rw [h.base]; rfl

theorem At.slot' (h : At s₀ B q s) (m : Mem) (k : Nat) :
    m.readW (xAddr (s.gpr cfg.base) k) 128 = W m B k := by
  show m.readW (addr (s.gpr Impl.Modes.X86.sb) _) 128 = _
  rw [h.base]; rfl

/-- Subkey `k` is at slot `60 + k`, as the code keeps it. -/
theorem At.key (h : At s₀ B q s) (hs : SlotsIn m s₀ B) {k : Nat} (hk : 60 + k < m) : W s.mem B (60 + k) = W s₀.mem B (60 + k) := by
  have hf := hs.fit
  refine W_frame h.frame (by omega_arith) fun r hr => ?_
  rw [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint (B.setWidth 64) (.inr (by omega_arith)) (by omega_arith) (by omega_arith)

/-- The planes' slots are after the table's. -/
theorem rng_not {d : Nat} (h : 28 ≤ d) : (decide (d ≤ tblSlot) && decide (tblSlot < d + 8)) = false := by
  rw [decide_eq_false (by unfold tblSlot; omega_arith)]; rfl

theorem At.kept {is : List Instr} {s' : State} (h : At s₀ B q s) (p : Runs cfg is s s') {f : Nat → Bool}
    (hst : storesOk is f = true) {k : Nat} (hk : k < 60) (hf : f k = false) : W s'.mem B k = W s.mem B k := by
  rw [← h.slot', ← h.slot]
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
  simpa [slotsR, cfg] using this

/-- The words of a linear layer with the planes `src` and the external words. -/
def inW (m : Mem) (B : BitVec 32) (src : Nat) (q : Nat) (v : BitVec 128) (i : Nat) : BitVec 128 :=
  if i < 8 then W m B (src + i) else W m B (60 + q + (i - 8)) ^^^ v

theorem mem_planesIn {d w j i : Nat} {v : BitVec 128} (h : (j, i, v) ∈ planesIn d w) :
    ∃ t < 8, j = d + t ∧ i = w + t ∧ v = 0 := by
  simp only [planesIn, List.mem_map, List.mem_range, Prod.mk.injEq] at h
  obtain ⟨t, ht, rfl, rfl, rfl⟩ := h
  exact ⟨t, ht, rfl, rfl, rfl⟩

theorem inS_lt {i j : Nat} (hj : j < 8) : inS i j < 8 := by unfold inS; split <;> omega_arith
theorem outS_lt {i j : Nat} (hj : j < 8) : outS i j < 8 := by unfold outS; split <;> [skip; split] <;> omega_arith

/-- The subkey XOR and input selection. -/
theorem roundIn_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) {r src : Nat} (hr : r < 4)
    (hchk : roundInOk r src = true) :
    ∃ s', runBlock isa (roundIn src (16 * r)) s = some s' ∧ Runs cfg (roundIn src (16 * r)) s s' ∧
      ∀ j < 8, ∀ p < 128, (W s'.mem B j).getLsbD p =
        ((W s.mem B (src + inS (p / 16) j)).getLsbD p ^^
          (W s.mem B (60 + q + r)).getLsbD (16 * (p / 16) + inS (p / 16) j)) := by
  obtain ⟨s', hr', p', ho⟩ := linear_ok hchk (h.ok hs hq) (inW s.mem B src q 0)
    (fun j i w hm _ => by
      obtain ⟨t, ht, rfl, rfl, rfl⟩ := mem_planesIn hm
      refine ⟨by omega_arith, ?_⟩
      rw [h.slot, inW, ite_eq_left (by omega_arith), xor0, Nat.zero_add])
    (fun j hj => by
      have hj : j < 4 := hj
      refine ⟨by omega_arith, ?_⟩
      rw [h.ext, inW, ite_eq_right (by omega_arith), xor0, xor0, Nat.add_sub_cancel_left])
  refine ⟨s', hr', p', fun j hj p hp => ?_⟩
  have := ho j (keyInG r j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp
  have hi := inS_lt (i := p / 16) hj
  rw [h.slot', keyInG, Nat.add_assoc, xorBits2 _ hp (by omega_arith)] at this
  rw [this, inW, inW, ite_eq_left hi, ite_eq_right (by omega_arith), xor0, Nat.add_sub_cancel_left]

/-- The S-box of every byte, of planes XORed with `0xc5`, to planes XORed
with `0x6e`. -/
theorem sbox_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) :
    ∃ s', runBlock isa sboxCode s = some s' ∧ Runs cfg sboxCode s s' ∧
      ∀ j < 8, ∀ p < 128, (W s'.mem B j).getLsbD p =
        (sbox1 (ofBits 8 (fun k => (W s.mem B k).getLsbD p) ^^^ 0xc5#8) ^^^ 0x6e#8).getLsbD j := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_chk
  have hpt : ∀ p < 128, ∃ s', runBlock isa sboxCode s = some s' ∧ Runs cfg sboxCode s s' ∧
      ∀ j < 8, (W s'.mem B j).getLsbD p =
        (sbox1 (ofBits 8 (fun k => (W s.mem B k).getLsbD p) ^^^ 0xc5#8) ^^^ 0x6e#8).getLsbD j := by
    intro p hp
    obtain ⟨c, hc⟩ : ∃ c : BitVec 8, c = ofBits 8 (fun k => (W s.mem B k).getLsbD p) := ⟨_, rfl⟩
    have hrel : Rel (TableRel (w := 128) p c.toNat) cfg (fun _ => none) sboxEnv s := by
      refine ⟨(fun r a h => by cases h), fun k a hk ha => ?_, fun k a hk ha => by cases ha⟩
      simp only [sboxEnv] at ha
      split at ha
      · rename_i hk8
        cases ha
        rw [h.slot, TableRel, testBit_tableOf, decide_eq_true c.isLt, Bool.true_and, ← BitVec.getLsbD, hc,
          getLsbD_ofBits, decide_eq_true hk8, Bool.true_and]
      · cases ha
    obtain ⟨s', hs', p'⟩ := run (ofDom_sound _ (table_sound hp c.isLt)) (h.ok hs hq) hrel he
    refine ⟨s', hs', p'.runs, fun j hj => ?_⟩
    have hj' := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    have := p'.rel.slot j _ (show j < 60 by omega_arith) (eq_of_beq hj')
    rw [p'.gpr, h.slot', TableRel, testBit_tableOf, decide_eq_true c.isLt, Bool.true_and, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] at this
    rw [← this, hc]
  obtain ⟨s', hs', p', _⟩ := hpt 0 (by decide)
  refine ⟨s', hs', p', fun j hj p hp => ?_⟩
  obtain ⟨s'', hs'', _, hv⟩ := hpt p hp
  rw [hs'] at hs''
  cases hs''
  exact hv j hj

/-- The words of the output layer. -/
def outW (m : Mem) (B : BitVec 32) (dst : Nat) (i : Nat) : BitVec 128 :=
  if i < 8 then W m B i ^^^ c6e i else W m B (dst + (i - 8))

/-- The output selection and the P-function, into the other half. -/
theorem roundOut_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) {dst : Nat}
    (hchk : roundOutOk dst = true) :
    ∃ s', runBlock isa (roundOut dst) s = some s' ∧ Runs cfg (roundOut dst) s s' ∧
      ∀ j < 8, ∀ p < 128, (W s'.mem B (dst + j)).getLsbD p =
        ((W s.mem B (dst + j)).getLsbD p ^^ (pRow (p / 16)).foldr
          (fun i acc => (W s.mem B (outS i j) ^^^ c6e (outS i j)).getLsbD (16 * i + p % 16) ^^ acc) false) := by
  obtain ⟨s', hr', p', ho⟩ := linear_ok0 hchk (h.ok hs hq) (outW s.mem B dst) fun j i w hm _ => by
    rcases List.mem_append.mp hm with hm | hm
    · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hm
      obtain ⟨t, ht, rfl, rfl, rfl⟩ := hm
      refine ⟨by omega_arith, ?_⟩
      rw [h.slot, outW, ite_eq_left ht, BitVec.xor_assoc, BitVec.xor_self]
      exact xor0 _
    · obtain ⟨t, ht, rfl, rfl, rfl⟩ := mem_planesIn hm
      refine ⟨by omega_arith, ?_⟩
      rw [h.slot, outW, ite_eq_right (by omega_arith), xor0, Nat.add_sub_cancel_left]
  refine ⟨s', hr', p', fun j hj p hp => ?_⟩
  have := ho (dst + j) (roundOutG j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp
  have hl : ∀ i ∈ pRow (p / 16), 16 * i + p % 16 < 128 := fun i hi => by
    have := Proof.Camellia.pRow_lt hi; omega_arith
  rw [h.slot', roundOutG, xorBits_cons, bitOf_word _ _ _ hp] at this
  have e : ((pRow (p / 16)).map fun i => 128 * outS i j + 16 * i + p % 16) =
      (pRow (p / 16)).map fun i => 128 * outS i j + (16 * i + p % 16) :=
    List.map_congr_left fun i _ => Nat.add_assoc _ _ _
  rw [e, xorBits_map _ (fun i => outS i j) (fun i => 16 * i + p % 16) _ hl, outW, ite_eq_right (by omega_arith),
    Nat.add_sub_cancel_left] at this
  rw [this]
  refine congrArg _ (congrArg (fun f => List.foldr f false (pRow (p / 16))) (funext fun i => funext fun acc => ?_))
  rw [outW, ite_eq_left (outS_lt hj)]

theorem cases8 {i : Nat} (hi : i < 8) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega_arith

theorem inS_eq {i j : Nat} (hi : i < 8) : inS i j = Proof.Camellia.inSrc (Proof.Camellia.cpos i) j := by
  rcases cases8 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem outS_eq {i j : Nat} (hi : i < 8) : outS i j = Proof.Camellia.outSrc (Proof.Camellia.cpos i) j := by
  rcases cases8 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The byte of a lane that an S-box's input constant and rotation make `0xc5`. -/
theorem uW_bit : ∀ i < 8, ∀ j < 8, uW.getLsbD (16 * i + inS i j) = (0xc5#8).getLsbD j := by decide

theorem wBit_eq : ∀ j < 8, wBit j = (0x6e#8).getLsbD j := by decide

theorem c6e_bit (j : Nat) (hj : j < 8) (p : Nat) (hp : p < 128) : (c6e j).getLsbD p = (0x6e#8).getLsbD j := by
  rw [← wBit_eq j hj, c6e]
  cases wBit j
  · exact BitVec.getLsbD_zero
  · rw [ite_eq_left rfl, BitVec.getLsbD_allOnes, decide_eq_true hp]

/-- A round: the half in the planes `dst` is XORed with `f` of the other. -/
theorem round_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) {r src dst : Nat} (hr : r < 4)
    (hin : roundInOk r src = true) (hout : roundOutOk dst = true)
    (st1 : storesOk (roundIn src (16 * r)) (· < 8) = true) (st3 : storesOk (roundOut dst) (fun k => dst ≤ k && k < dst + 8) = true)
    (hsrc : 26 ≤ src) (hsrc' : src + 8 ≤ 44) (hdst : 28 ≤ dst) (hdst' : dst + 8 ≤ 44)
    (hsd : src + 8 ≤ dst ∨ dst + 8 ≤ src)
    {x y : Nat → BitVec 64} {k : BitVec 64} (hx : PAt s.mem B src x) (hy : PAt s.mem B dst y)
    (hk : W s.mem B (60 + q + r) = spread k ^^^ uW) :
    ∃ s', runBlock isa (round (16 * r) src dst) s = some s' ∧ At s₀ B q s' ∧ PAt s'.mem B src x ∧
      PAt s'.mem B dst (fun b => y b ^^^ Spec.Camellia.f (x b) k) ∧
      s'.gpr = s.gpr ∧ ∀ e, 44 ≤ e → e < 60 → W s'.mem B e = W s.mem B e := by
  obtain ⟨s₁, r₁, p₁, v₁⟩ := roundIn_ok h hs hq hr hin
  have st2 : storesOk sboxCode (· < 26) = true := by
    have := parts_chk; simp only [parts, Bool.and_eq_true] at this; exact this.1.1.1.1.2
  have a₁ := h.runs p₁ st1 rfl
  obtain ⟨s₂, r₂, p₂, v₂⟩ := sbox_ok a₁ hs hq
  have a₂ := a₁.runs p₂ st2 rfl
  obtain ⟨s₃, r₃, p₃, v₃⟩ := roundOut_ok a₂ hs hq hout
  have a₃ := a₂.runs p₃ st3 (rng_not (by omega_arith))
  have kep : ∀ j, 26 ≤ j → j < 60 → (¬ (dst ≤ j ∧ j < dst + 8)) → W s₃.mem B j = W s.mem B j := fun j h1 h2 h3 => by
    rw [a₂.kept p₃ st3 h2 (by simp; omega_arith), a₁.kept p₂ st2 h2 (by simp; omega_arith),
      h.kept p₁ st1 h2 (by simp; omega_arith)]
  have ked : ∀ j, 26 ≤ j → j < 60 → W s₂.mem B j = W s.mem B j := fun j h1 h2 => by
    rw [a₁.kept p₂ st2 h2 (by simp; omega_arith), h.kept p₁ st1 h2 (by simp; omega_arith)]
  refine ⟨s₃, ?_, a₃, hx.frame fun j hj => kep _ (by omega_arith) (by omega_arith) (by omega_arith), ?_,
    by rw [p₃.gpr, p₂.gpr, p₁.gpr], fun e h1 h2 => kep e (by omega_arith) h2 (by omega_arith)⟩
  · rw [round, List.append_assoc]
    exact run_append r₁ (run_append r₂ r₃)
  intro b hb i hi j hj
  have hp : 16 * i + b < 128 := by omega_arith
  rw [v₃ j hj _ hp, ked _ (by omega_arith) (by omega_arith), hy b hb i hi j hj, Proof.Camellia.byteOf_xor,
    BitVec.getLsbD_xor, Proof.Camellia.getLsbD_byteOf_f _ _ hi hj, show (16 * i + b) / 16 = i by omega_arith,
    show (16 * i + b) % 16 = b by omega_arith]
  refine congrArg _ ?_
  have hrow : ∀ l : List Nat, (∀ i' ∈ l, i' < 8) →
      l.foldr (fun i' acc => (W s₂.mem B (outS i' j) ^^^ c6e (outS i' j)).getLsbD (16 * i' + b) ^^ acc) false =
        Proof.Camellia.xorRow (fun i' => Proof.Camellia.sboxAt i' (byteOf (x b ^^^ k) i')) l j := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons i' l ih =>
      intro hl
      have hi' := hl i' List.mem_cons_self
      have ho := outS_lt (i := i') hj
      have hp' : 16 * i' + b < 128 := by omega_arith
      simp only [Proof.Camellia.xorRow, List.foldr_cons] at ih ⊢
      rw [ih fun i'' h'' => hl i'' (List.mem_cons_of_mem _ h'')]
      refine congrArg (· ^^ _) ?_
      have hb8 : ofBits 8 (fun k' => (W s₁.mem B k').getLsbD (16 * i' + b)) ^^^ 0xc5#8 =
          ofBits 8 fun j' => (byteOf (x b ^^^ k) i').getLsbD (Proof.Camellia.inSrc (Proof.Camellia.cpos i') j') := by
        refine Proof.Aes.byte_ext fun j' hj' => ?_
        have hin' := inS_lt (i := i') hj'
        rw [BitVec.getLsbD_xor, getLsbD_ofBits, getLsbD_ofBits, decide_eq_true hj', Bool.true_and, Bool.true_and,
          v₁ j' hj' _ hp', show (16 * i' + b) / 16 = i' by omega_arith, hx b hb i' hi' _ hin', hk, BitVec.getLsbD_xor,
          spread_bit _ hi' hin', uW_bit i' hi' j' hj', ← inS_eq hi', Proof.Camellia.byteOf_xor, BitVec.getLsbD_xor]
        cases (byteOf (x b) i').getLsbD (inS i' j') <;> cases (byteOf k i').getLsbD (inS i' j') <;>
          cases (0xc5#8).getLsbD j' <;> rfl
      rw [BitVec.getLsbD_xor, v₂ _ ho _ hp', c6e_bit _ ho _ hp', BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_self,
        Bool.xor_false, hb8, outS_eq hi', Proof.Camellia.sbox_sel (Proof.Camellia.cpos_lt hi') hj,
        Proof.Camellia.pos_cpos hi']
  exact hrow _ fun i' hi' => Proof.Camellia.pRow_lt hi'

/-! ## Whitening, FL and the transposes -/

/-- The bits of a kept subkey. -/
theorem spread_xor_bit (k : BitVec 64) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    ((spread k ^^^ uW) ^^^ uW).getLsbD (16 * i + j) = (byteOf k i).getLsbD j := by
  rw [BitVec.xor_assoc, BitVec.xor_self]
  exact (congrArg (fun v : BitVec 128 => v.getLsbD (16 * i + j)) (xor0 _)).trans (spread_bit k hi hj)

theorem whiten_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) {r d : Nat} (hr : r < 4)
    (hchk : whitenOk r d = true) (hst : storesOk (whiten (16 * r) d) (fun k => d ≤ k && k < d + 8) = true)
    (hd : 28 ≤ d) (hd' : d + 8 ≤ 44) {x : Nat → BitVec 64} {k : BitVec 64} (hx : PAt s.mem B d x)
    (hk : W s.mem B (60 + q + r) = spread k ^^^ uW) :
    ∃ s', runBlock isa (whiten (16 * r) d) s = some s' ∧ At s₀ B q s' ∧ PAt s'.mem B d (fun b => x b ^^^ k) ∧
      s'.gpr = s.gpr ∧ ∀ e, e + 8 ≤ 60 → (e + 8 ≤ d ∨ d + 8 ≤ e) → ∀ y, PAt s.mem B e y → PAt s'.mem B e y := by
  obtain ⟨s', hr', p', ho⟩ := linear_ok hchk (h.ok hs hq) (inW s.mem B d q uW)
    (fun j i w hm _ => by
      obtain ⟨t, ht, rfl, rfl, rfl⟩ := mem_planesIn hm
      refine ⟨by omega_arith, ?_⟩
      rw [h.slot, inW, ite_eq_left (by omega_arith), xor0, Nat.zero_add])
    (fun j hj => by
      have hj : j < 4 := hj
      refine ⟨by omega_arith, ?_⟩
      rw [h.ext, inW, ite_eq_right (by omega_arith), Nat.add_sub_cancel_left, BitVec.xor_assoc, BitVec.xor_self]
      exact xor0 _)
  refine ⟨s', hr', h.runs p' hst (rng_not (by omega_arith)), fun b hb i hi j hj => ?_, p'.gpr, fun e he hde y hy => hy.frame fun j hj =>
    h.kept p' hst (by omega_arith) (by simp; omega_arith)⟩
  have hp : 16 * i + b < 128 := by omega_arith
  have := ho (d + j) (whitenG r j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) _ hp
  rw [h.slot', whitenG, Nat.add_assoc, xorBits2 _ hp (by omega_arith), show (16 * i + b) / 16 = i by omega_arith, inW, inW,
    ite_eq_left hj, ite_eq_right (by omega_arith), Nat.add_sub_cancel_left, hk, spread_xor_bit _ _ _ hi hj,
    hx b hb i hi j hj] at this
  rw [this, Proof.Camellia.byteOf_xor, BitVec.getLsbD_xor]

/-- The planes of the blocks `8 h …` of a half, as `Proof/Camellia/Bitsliced.lean` has them. -/
def proj (h : Nat) (P : Nat → BitVec 128) (j : Nat) : BitVec 64 :=
  ofBits 64 fun p => (P j).getLsbD (16 * Proof.Camellia.pos (p / 8) + (8 * h + p % 8))

theorem proj_bit (h : Nat) (P : Nat → BitVec 128) (j : Nat) {p : Nat} (hp : p < 64) :
    (proj h P j).getLsbD p = (P j).getLsbD (16 * Proof.Camellia.pos (p / 8) + (8 * h + p % 8)) := by
  rw [proj, getLsbD_ofBits, decide_eq_true hp, Bool.true_and]

theorem PAt.half {m : Mem} {d : Nat} {x : Nat → BitVec 64} (hx : PAt m B d x) {h : Nat} (hh : h < 2) :
    Proof.Camellia.HalfRel (proj h fun j => W m B (d + j)) (fun b => x (8 * h + b)) := fun b hb c hc j hj => by
  rw [proj_bit _ _ _ (by omega_arith), show (8 * c + b) / 8 = c by omega_arith, show (8 * c + b) % 8 = b by omega_arith]
  exact hx (8 * h + b) (by omega_arith) _ (Proof.Camellia.pos_lt hc) j hj

theorem PAt.of_half {m : Mem} {d : Nat} {x : Nat → BitVec 64}
    (h : ∀ h < 2, Proof.Camellia.HalfRel (proj h fun j => W m B (d + j)) (fun b => x (8 * h + b))) : PAt m B d x := by
  intro b hb i hi j hj
  have := h (b / 8) (by omega_arith) (b % 8) (by omega_arith) (Proof.Camellia.cpos i) (Proof.Camellia.cpos_lt hi) j hj
  dsimp only at this
  have hc := Proof.Camellia.cpos_lt hi
  rw [proj_bit _ _ _ (by omega_arith), show (8 * Proof.Camellia.cpos i + b % 8) / 8 = Proof.Camellia.cpos i by omega_arith,
    show (8 * Proof.Camellia.cpos i + b % 8) % 8 = b % 8 by omega_arith, Proof.Camellia.pos_cpos hi,
    show 8 * (b / 8) + b % 8 = b by omega_arith] at this
  exact this

/-- The subkey's planes. -/
def kPl (k : BitVec 64) (j : Nat) : BitVec 64 :=
  ofBits 64 fun p => (byteOf k (Proof.Camellia.pos (p / 8))).getLsbD j

theorem kPl_bit (k : BitVec 64) (j : Nat) {p : Nat} (hp : p < 64) :
    (kPl k j).getLsbD p = (byteOf k (Proof.Camellia.pos (p / 8))).getLsbD j := by
  rw [kPl, getLsbD_ofBits, decide_eq_true hp, Bool.true_and]

theorem kPl_half (k : BitVec 64) : Proof.Camellia.HalfRel (kPl k) (fun _ => k) := fun b hb c hc j hj => by
  rw [kPl_bit _ _ (by omega_arith), show (8 * c + b) / 8 = c by omega_arith]

/-- Plane `j` of the subkey: bit `j` of byte `i` in all of lane `i`. -/
theorem kE_bit {V : Nat → BitVec 128} {k : BitVec 64} (hk : V 8 = spread k) {i j b : Nat} (hi : i < 8) (hj : j < 8)
    (hb : b < 16) : ((kE j).eval V).getLsbD (16 * i + b) = (byteOf k i).getLsbD j := by
  have hp : 16 * i + b < 128 := by omega_arith
  have h15 : (BitVec.ofNat 8 (15 - j)).toNat = 15 - j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  simp only [kE, XE.eval]
  rw [un_bit _ _ hp]
  simp only [Un.src, bitOpt]
  rw [show (15 : BitVec 8).toNat = 15 from rfl, show (16 * i + b) / 16 = i by omega_arith,
    show min 15 ((16 * i + b) % 16 + 15) = 15 by omega_arith, un_bit _ _ (by omega_arith)]
  simp only [Un.src, h15]
  rw [ite_eq_left (by omega_arith), bitOpt, hk, show 16 * i + 15 - (15 - j) = 16 * i + j by omega_arith, spread_bit _ hi hj]

theorem slq_bit (x : BitVec 128) {p : Nat} (hp : p < 128) :
    (Un.eval (.shift .pslldq 8) x).getLsbD p = if 64 ≤ p then x.getLsbD (p - 64) else false := by
  rw [un_bit _ _ hp]
  simp only [Un.src, show (8 : BitVec 8).toNat = 8 from rfl]
  by_cases h : 64 ≤ p
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h]; rfl

theorem srq_bit (x : BitVec 128) {p : Nat} (hp : p < 128) :
    (Un.eval (.shift .psrldq 8) x).getLsbD p = if p < 64 then x.getLsbD (p + 64) else false := by
  rw [un_bit _ _ hp]
  simp only [Un.src, show (8 : BitVec 8).toNat = 8 from rfl]
  by_cases h : p < 64
  · rw [ite_eq_left h, ite_eq_left (by omega_arith)]; rfl
  · rw [ite_eq_right h, ite_eq_right (by omega_arith)]; rfl

theorem shuf39_bit (x : BitVec 128) {m b : Nat} (hm : m < 4) (hb : b < 16) :
    (Un.eval (.pshuflw 0x39) x).getLsbD (16 * m + b) = x.getLsbD (16 * ((m + 1) % 4) + b) := by
  rw [un_bit _ _ (by omega_arith)]
  simp only [Un.src, show (16 * m + b) / 16 = m by omega_arith, show (16 * m + b) % 16 = b by omega_arith,
    show 16 * m + b < 64 by omega_arith, ite_true, bitOpt]
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega_arith
  rcases this with rfl | rfl | rfl | rfl <;> rfl

/-- Plane `j` after the rotation step, in its left half and its right half. -/
theorem rotE_lo (V : Nat → BitVec 128) (j : Nat) {p : Nat} (hp : p < 64) :
    ((rotE j).eval V).getLsbD p = (V j).getLsbD p := by
  cases j <;> simp only [rotE, XE.eval, XBinOp.eval] <;>
    rw [BitVec.getLsbD_xor, slq_bit _ (by omega_arith), ite_eq_right (by omega_arith), Bool.xor_false]

theorem rotE_hi {V : Nat → BitVec 128} {k : BitVec 64} (hk : V 8 = spread k) {j m b : Nat} (hj : j < 8) (hm : m < 4)
    (hb : b < 16) : ((rotE j).eval V).getLsbD (16 * (4 + m) + b) = ((V j).getLsbD (16 * (4 + m) + b) ^^
      ((V ((j + 7) % 8)).getLsbD (16 * (if j = 0 then (m + 1) % 4 else m) + b) &&
        (byteOf k (if j = 0 then (m + 1) % 4 else m)).getLsbD ((j + 7) % 8))) := by
  have hp : 16 * (4 + m) + b < 128 := by omega_arith
  cases j with
  | zero =>
    simp only [rotE, XE.eval, XBinOp.eval, ite_true]
    rw [BitVec.getLsbD_xor, slq_bit _ hp, ite_eq_left (by omega_arith), show 16 * (4 + m) + b - 64 = 16 * m + b by omega_arith,
      shuf39_bit _ hm hb, BitVec.getLsbD_and, kE_bit hk (by omega_arith) (by decide) hb]
  | succ j =>
    simp only [rotE, XE.eval, XBinOp.eval, show ¬ j + 1 = 0 by omega_arith, ite_false]
    rw [BitVec.getLsbD_xor, slq_bit _ hp, ite_eq_left (by omega_arith), show 16 * (4 + m) + b - 64 = 16 * m + b by omega_arith,
      BitVec.getLsbD_and, kE_bit hk (by omega_arith) (by omega_arith) hb, rotE_lo _ _ (by omega_arith),
      show (j + 1 + 7) % 8 = j by omega_arith]

theorem orE_lo {V : Nat → BitVec 128} {k : BitVec 64} (hk : V 8 = spread k) {j m b : Nat} (hj : j < 8) (hm : m < 4)
    (hb : b < 16) : ((orE j).eval V).getLsbD (16 * m + b) = ((V j).getLsbD (16 * m + b) ^^
      ((V j).getLsbD (16 * (4 + m) + b) || (byteOf k (4 + m)).getLsbD j)) := by
  simp only [orE, XE.eval, XBinOp.eval]
  rw [BitVec.getLsbD_xor, srq_bit _ (by omega_arith), ite_eq_left (by omega_arith), BitVec.getLsbD_or,
    show 16 * m + b + 64 = 16 * (4 + m) + b by omega_arith, kE_bit hk (by omega_arith) hj hb, Bool.or_comm]

theorem orE_hi (V : Nat → BitVec 128) (j : Nat) {p : Nat} (hp : 64 ≤ p) (hp' : p < 128) :
    ((orE j).eval V).getLsbD p = (V j).getLsbD p := by
  simp only [orE, XE.eval, XBinOp.eval]
  rw [BitVec.getLsbD_xor, srq_bit _ hp', ite_eq_right (by omega_arith), Bool.xor_false]

theorem pos_odd' {p : Nat} (hp : p < 64) (ho : (p / 8) % 2 = 1) : Proof.Camellia.pos (p / 8) = 4 + p / 16 := by
  simp only [Proof.Camellia.pos]; omega_arith
theorem pos_even' {p : Nat} (ho : (p / 8) % 2 = 0) : Proof.Camellia.pos (p / 8) = p / 16 := by
  simp only [Proof.Camellia.pos]; omega_arith

theorem rot_step {V : Nat → BitVec 128} {k : BitVec 64} (hk : V 8 = spread k) {h : Nat} (hh : h < 2) :
    Proof.Camellia.RotStep (proj h V) (kPl k) (proj h fun j => (rotE j).eval V) := by
  intro j hj p hp
  have hrp : Proof.Camellia.rotPos j p < 64 := Nat.mod_lt _ (by decide)
  rw [proj_bit _ _ _ hp, proj_bit _ _ _ hp, proj_bit _ _ _ hrp, kPl_bit _ _ hrp]
  by_cases ho : (p / 8) % 2 = 1
  · have e1 : Proof.Camellia.oddAt p = true := by simp only [Proof.Camellia.oddAt, ho]; rfl
    rw [e1, Bool.true_and, pos_odd' hp ho, rotE_hi hk hj (by omega_arith) (by omega_arith)]
    have e2 : Proof.Camellia.pos (Proof.Camellia.rotPos j p / 8) = if j = 0 then (p / 16 + 1) % 4 else p / 16 := by
      unfold Proof.Camellia.rotPos Proof.Camellia.pos
      split <;> omega_arith
    have e3 : Proof.Camellia.rotPos j p % 8 = p % 8 := by unfold Proof.Camellia.rotPos; split <;> omega_arith
    rw [e2, e3]
  · have e1 : Proof.Camellia.oddAt p = false := by
      simp only [Proof.Camellia.oddAt, show p / 8 % 2 = 0 by omega_arith]; rfl
    rw [e1, Bool.false_and, Bool.false_and, Bool.xor_false, pos_even' (by omega_arith), rotE_lo _ _ (by omega_arith)]

theorem or_step {V : Nat → BitVec 128} {k : BitVec 64} (hk : V 8 = spread k) {h : Nat} (hh : h < 2) :
    Proof.Camellia.OrStep (proj h V) (kPl k) (proj h fun j => (orE j).eval V) := by
  intro j hj p hp
  have hrp : (p + 8) % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [proj_bit _ _ _ hp, proj_bit _ _ _ hp, proj_bit _ _ _ hrp, kPl_bit _ _ hrp]
  by_cases ho : (p / 8) % 2 = 1
  · have e1 : Proof.Camellia.oddAt p = true := by simp only [Proof.Camellia.oddAt, ho]; rfl
    rw [e1, Bool.not_true, Bool.false_and, Bool.xor_false, pos_odd' hp ho, orE_hi _ _ (by omega_arith) (by omega_arith)]
  · have e1 : Proof.Camellia.oddAt p = false := by
      simp only [Proof.Camellia.oddAt, show p / 8 % 2 = 0 by omega_arith]; rfl
    rw [e1, Bool.not_false, Bool.true_and, pos_even' (by omega_arith), orE_lo hk hj (by omega_arith) (by omega_arith)]
    have e2 : Proof.Camellia.pos ((p + 8) % 64 / 8) = 4 + p / 16 := by unfold Proof.Camellia.pos; omega_arith
    have e3 : (p + 8) % 64 % 8 = p % 8 := by omega_arith
    rw [e2, e3]

/-- A step of `fl` or `flinv`, under the subkey in `xmm6`. -/
theorem flStep_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) {is : List Instr} {d : Nat} {E : Nat → XE}
    (hchk : flOk is d E = true) (hd : d + 8 ≤ 60) (h6 : (is.all fun i => xdst i != some .xmm6) = true) :
    ∃ s', runBlock isa is s = some s' ∧ Runs cfg is s s' ∧ s'.xmm .xmm6 = s.xmm .xmm6 ∧
      ∀ j < 8, W s'.mem B (d + j) = (E j).eval fun n => if n < 8 then W s.mem B (d + n) else s.xmm .xmm6 := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (fun e x => x = e.eval fun n => if n < 8 then W s.mem B (d + n) else s.xmm .xmm6) cfg
      (fun _ => none) (flEnv d) s := by
    refine ⟨fun r a ha => ?_, fun k a hk ha => ?_, fun k a hk ha => by cases ha⟩
    · simp only [flEnv] at ha
      split at ha
      · rename_i hr; cases ha; subst hr; rfl
      · cases ha
    · simp only [flEnv] at ha
      split at ha
      · rename_i hk'; cases ha
        rw [h.slot]
        simp only [XE.eval]
        rw [ite_eq_left (by omega_arith), show d + (k - d) = k by omega_arith]
      · cases ha
  obtain ⟨s', hs', p'⟩ := run (exprs_sound _) (h.ok hs hq) hrel he
  refine ⟨s', hs', p'.runs, p'.other _ h6, fun j hj => ?_⟩
  have hj' := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  have := p'.rel.slot (d + j) _ (show d + j < 60 by omega_arith) (eq_of_beq hj')
  rw [p'.gpr, h.slot'] at this
  exact this

theorem ldK_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) {r : Nat} (hchk : ldKOk r = true)
    {k : BitVec 64} (hk : W s.mem B (60 + q + r) = spread k ^^^ uW) :
    ∃ s', runBlock isa (ldK (16 * r)) s = some s' ∧ Runs cfg (ldK (16 * r)) s s' ∧ s'.mem = s.mem ∧
      s'.xmm .xmm6 = spread k := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (fun (e : XE) x => x = e.eval fun n => W s.mem B (60 + q + n)) cfg (fun n => some (XE.atom n))
      ⟨fun _ => none, fun _ => none⟩ s :=
    ⟨(fun r a ha => by cases ha), (fun k a hk ha => by cases ha), fun k a hk ha => by cases ha; exact h.ext k⟩
  obtain ⟨s', hs', p'⟩ := run (exprs_sound fun n => W s.mem B (60 + q + n)) (h.ok hs hq) hrel he
  refine ⟨s', hs', p'.runs, ?_, ?_⟩
  · exact run_mem rfl hs'
  · have := p'.rel.reg .xmm6 _ (eq_of_beq hpost)
    rw [this]
    simp only [XE.eval, XBinOp.eval]
    rw [hk, BitVec.xor_assoc, BitVec.xor_self]
    exact xor0 _

/-- Two steps of `fl` or `flinv` under a subkey. -/
theorem fl2_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) {r d : Nat} (hl : ldKOk r = true)
    {i₁ i₂ : List Instr} {E₁ E₂ : Nat → XE} (hd : 28 ≤ d) (hd' : d + 8 ≤ 44)
    (c₁ : flOk i₁ d E₁ = true) (c₂ : flOk i₂ d E₂ = true)
    (x₁ : (i₁.all fun i => xdst i != some .xmm6) = true) (x₂ : (i₂.all fun i => xdst i != some .xmm6) = true)
    (st₁ : storesOk i₁ (fun k => d ≤ k && k < d + 8) = true) (st₂ : storesOk i₂ (fun k => d ≤ k && k < d + 8) = true)
    {x z : Nat → BitVec 64} {k : BitVec 64} (hx : PAt s.mem B d x)
    (hk : W s.mem B (60 + q + r) = spread k ^^^ uW)
    (hz : ∀ V V' : Nat → BitVec 128, V 8 = spread k → V' 8 = spread k → (∀ j < 8, V' j = (E₁ j).eval V) →
      ∀ h < 2, ∀ e : Nat → BitVec 64, Proof.Camellia.HalfRel (proj h V) e → (∀ b, e b = x (8 * h + b)) →
        Proof.Camellia.HalfRel (proj h fun j => (E₂ j).eval V') fun b => z (8 * h + b)) :
    ∃ s', runBlock isa (ldK (16 * r) ++ i₁ ++ i₂) s = some s' ∧ At s₀ B q s' ∧ PAt s'.mem B d z ∧
      s'.gpr = s.gpr ∧ ∀ e, e + 8 ≤ 60 → (e + 8 ≤ d ∨ d + 8 ≤ e) → ∀ y, PAt s.mem B e y → PAt s'.mem B e y := by
  obtain ⟨s₁, r₁, p₁, m₁, k₁⟩ := ldK_ok h hs hq hl hk
  have a₁ := h.runs p₁ (f := fun _ => false) rfl rfl
  obtain ⟨s₂, r₂, p₂, k₂, v₂⟩ := flStep_ok a₁ hs hq c₁ (by omega_arith) x₁
  have a₂ := a₁.runs p₂ st₁ (rng_not (by omega_arith))
  obtain ⟨s₃, r₃, p₃, _, v₃⟩ := flStep_ok a₂ hs hq c₂ (by omega_arith) x₂
  refine ⟨s₃, ?_, a₂.runs p₃ st₂ (rng_not (by omega_arith)), ?_, by rw [p₃.gpr, p₂.gpr, p₁.gpr], fun e he hde y hy => hy.frame fun j hj => ?_⟩
  · rw [List.append_assoc]; exact run_append r₁ (run_append r₂ r₃)
  · refine PAt.of_half fun hh h2 => ?_
    have := hz _ (fun n => if n < 8 then W s₂.mem B (d + n) else s₂.xmm .xmm6)
      (show (if 8 < 8 then _ else s₁.xmm .xmm6) = spread k from k₁) (k₂.trans k₁)
      (fun j hj => by simp only [hj, ite_true]; exact v₂ j hj) hh h2 (fun b => x (8 * hh + b)) ?_ fun _ => rfl
    · refine this.congr fun j hj => ?_
      unfold proj
      dsimp only
      rw [v₃ j hj]
    · refine (hx.half h2).congr fun j hj => ?_
      unfold proj
      simp only [hj, ite_true, m₁]
  · rw [a₂.kept p₃ st₂ (by omega_arith) (by simp; omega_arith), a₁.kept p₂ st₁ (by omega_arith) (by simp; omega_arith), m₁]

theorem proj_eq {V V' : Nat → BitVec 128} {E : Nat → XE} (e : ∀ j < 8, V' j = (E j).eval V) (h : Nat) {j : Nat}
    (hj : j < 8) : proj h (fun j => (E j).eval V) j = proj h V' j := by
  unfold proj
  dsimp only
  rw [e j hj]

theorem fl_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) {x : Nat → BitVec 64} {k : BitVec 64}
    (hx : PAt s.mem B d1 x) (hk : W s.mem B (60 + q + 2) = spread k ^^^ uW) :
    ∃ s', runBlock isa (fl 32 d1) s = some s' ∧ At s₀ B q s' ∧ PAt s'.mem B d1 (fun b => Spec.Camellia.fl (x b) k) ∧
      s'.gpr = s.gpr ∧ ∀ e, e + 8 ≤ 60 → (e + 8 ≤ d1 ∨ d1 + 8 ≤ e) → ∀ y, PAt s.mem B e y → PAt s'.mem B e y := by
  have c := fl_chk
  have l := ldK_chk
  have st := parts_fl
  have n6 := fl_no6
  simp only [Bool.and_eq_true] at c l st n6
  refine fl2_ok h hs hq l.1 (by decide) (by decide) c.1.1.1 c.1.1.2 n6.1.1.1 n6.1.1.2
    st.1.1.1 st.1.1.2 hx hk fun V V' hV hV' e₁ hh h2 e he hx' => ?_
  have r : Proof.Camellia.RotStep (proj hh V) (kPl k) (proj hh V') := fun j hj p hp => by
    rw [← proj_eq e₁ hh hj]; exact rot_step hV h2 j hj p hp
  have := Proof.Camellia.fl_rel he (kPl_half k) r (or_step hV' h2)
  rw [show e = fun b => x (8 * hh + b) from funext hx'] at this
  exact this

theorem flinv_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) {x : Nat → BitVec 64} {k : BitVec 64}
    (hx : PAt s.mem B d2 x) (hk : W s.mem B (60 + q + 3) = spread k ^^^ uW) :
    ∃ s', runBlock isa (flinv 48 d2) s = some s' ∧ At s₀ B q s' ∧ PAt s'.mem B d2 (fun b => Spec.Camellia.flinv (x b) k) ∧
      s'.gpr = s.gpr ∧ ∀ e, e + 8 ≤ 60 → (e + 8 ≤ d2 ∨ d2 + 8 ≤ e) → ∀ y, PAt s.mem B e y → PAt s'.mem B e y := by
  have c := fl_chk
  have l := ldK_chk
  have st := parts_fl
  have n6 := fl_no6
  simp only [Bool.and_eq_true] at c l st n6
  refine fl2_ok h hs hq l.2 (by decide) (by decide) c.2 c.1.2 n6.2 n6.1.2
    st.2 st.1.2 hx hk fun V V' hV hV' e₁ hh h2 e he hx' => ?_
  have r : Proof.Camellia.OrStep (proj hh V) (kPl k) (proj hh V') := fun j hj p hp => by
    rw [← proj_eq e₁ hh hj]; exact or_step hV h2 j hj p hp
  have := Proof.Camellia.flinv_rel he (kPl_half k) r (rot_step hV' h2)
  rw [show e = fun b => x (8 * hh + b) from funext hx'] at this
  exact this

/-! ## The transposes -/

/-- The blocks of the buffer. -/
theorem blocksIn_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) :
    ∃ s', runBlock isa blocksIn s = some s' ∧ At s₀ B q s' ∧ s'.gpr = s.gpr ∧
      (∀ e, 44 ≤ e → e < 60 → W s'.mem B e = W s.mem B e) ∧
      ∀ b < 16, ∀ i < 8, ∀ j < 8,
        (W s'.mem B (d1 + j)).getLsbD (16 * i + b) = (W s.mem B (bufS + b)).getLsbD (8 * i + j) ∧
        (W s'.mem B (d2 + j)).getLsbD (16 * i + b) = (W s.mem B (bufS + b)).getLsbD (8 * (8 + i) + j) := by
  obtain ⟨s', hr', p', ho⟩ := linear_ok0 blocksIn_chk (h.ok hs hq) (fun b => W s.mem B (bufS + b)) fun j i w hm _ => by
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hm
    obtain ⟨t, ht, rfl, rfl, rfl⟩ := hm
    refine ⟨by omega_arith, ?_⟩
    rw [h.slot]; exact xor0 _
  have st := parts_chk2
  rw [Bool.and_eq_true] at st
  refine ⟨s', hr', h.runs p' st.1 rfl, p'.gpr, fun e h1 h2 => h.kept p' st.1 h2 (by simp; omega_arith), fun b hb i hi j hj => ?_⟩
  have hp : 16 * i + b < 128 := by omega_arith
  have g1 := ho (d1 + j) (inG 0 j) (List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)) _ hp
  have g2 := ho (d2 + j) (inG 1 j) (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)) _ hp
  rw [h.slot', inG, Nat.add_assoc, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (by omega_arith),
    show (16 * i + b) % 16 = b by omega_arith, show (16 * i + b) / 16 = i by omega_arith] at g1 g2
  rw [g1, g2, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  exact ⟨rfl, rfl⟩

theorem blocksOut_ok (h : At s₀ B q s) (hs : SlotsIn m s₀ B) (hq : 60 + q + 4 ≤ m) :
    ∃ s', runBlock isa blocksOut s = some s' ∧ At s₀ B q s' ∧ s'.gpr = s.gpr ∧
      ∀ b < 16, ∀ i < 8, ∀ j < 8,
        (W s'.mem B (bufS + b)).getLsbD (8 * i + j) = (W s.mem B (d2 + j)).getLsbD (16 * i + b) ∧
        (W s'.mem B (bufS + b)).getLsbD (8 * (8 + i) + j) = (W s.mem B (d1 + j)).getLsbD (16 * i + b) := by
  obtain ⟨s', hr', p', ho⟩ := linear_ok0 blocksOut_chk (h.ok hs hq)
    (fun i => if i < 8 then W s.mem B (d1 + i) else W s.mem B (d2 + (i - 8))) fun j i w hm _ => by
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨t, ht, rfl, rfl, rfl⟩ := mem_planesIn hm
      refine ⟨by omega_arith, ?_⟩
      rw [h.slot, ite_eq_left (by omega_arith), xor0, Nat.zero_add]
    · obtain ⟨t, ht, rfl, rfl, rfl⟩ := mem_planesIn hm
      refine ⟨by omega_arith, ?_⟩
      rw [h.slot, ite_eq_right (by omega_arith), xor0, Nat.add_sub_cancel_left]
  have st := parts_chk2
  rw [Bool.and_eq_true] at st
  refine ⟨s', hr', h.runs p' st.2 rfl, p'.gpr, fun b hb i hi j hj => ?_⟩
  have g1 := ho (bufS + b) (outG b) (List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩) (8 * i + j) (by omega_arith)
  have g2 := ho (bufS + b) (outG b) (List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩) (8 * (8 + i) + j) (by omega_arith)
  rw [h.slot', outG] at g1 g2
  rw [ite_eq_left (by omega_arith), Nat.add_assoc, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (by omega_arith),
    show (8 * i + j) % 8 = j by omega_arith, show (8 * i + j) / 8 = i by omega_arith] at g1
  rw [ite_eq_right (by omega_arith), Nat.add_assoc, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (by omega_arith),
    show (8 * (8 + i) + j) % 8 = j by omega_arith, show (8 * (8 + i) + j) / 8 - 8 = i by omega_arith] at g2
  rw [ite_eq_right (by omega_arith), Nat.add_sub_cancel_left] at g1
  rw [ite_eq_left hj] at g2
  exact ⟨g1, g2⟩

/-! ## The block function -/

variable {E : Nat → BitVec 64} {g : Nat}

/-- The subkeys `E`, as the code keeps them. -/
def Keys (m : Mem) (B : BitVec 32) (n : Nat) (E : Nat → BitVec 64) : Prop :=
  ∀ k < n, W m B (60 + k) = spread (E k) ^^^ uW

/-- The halves of the sixteen blocks. -/
def PP (m : Mem) (B : BitVec 32) (x : Nat → BitVec 64 × BitVec 64) : Prop :=
  PAt m B d1 (fun b => (x b).1) ∧ PAt m B d2 (fun b => (x b).2)

theorem At.keyE (h : At s₀ B q s) (hs : SlotsIn m s₀ B) {n : Nat} (hk : Keys s₀.mem B n E) (hn : 60 + n ≤ m) {r : Nat}
    (hr : q + r < n) : W s.mem B (60 + q + r) = spread (E (q + r)) ^^^ uW := by
  rw [Nat.add_assoc, h.key hs (by omega_arith)]
  exact hk _ hr

theorem At.upd {s' : State} {d : Reg} {v : BitVec 32} (h : At s₀ B q s) (u : Wp.Upd s s' d v)
    (hd : d ≠ Impl.Modes.X86.sb ∧ d ≠ .esp ∧ d ≠ kr ∧ d ≠ tbr) : At s₀ B q s' :=
  ⟨by rw [u.other _ hd.1.symm]; exact h.base, by rw [u.other _ hd.2.1.symm]; exact h.esp,
    by rw [u.other _ hd.2.2.1.symm]; exact h.kp, by rw [u.other _ hd.2.2.2.symm]; exact h.tb,
    u.rd.trans h.rd, u.wr.trans h.wr, u.syms.trans h.syms, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.tab⟩

theorem At.next {s' : State} (h : At s₀ B q s) (u : Wp.Upd s s' kr (s.gpr kr + 32)) : At s₀ B (q + 2) s' :=
  ⟨by rw [u.other _ (by decide)]; exact h.base, by rw [u.other _ (by decide)]; exact h.esp,
    by rw [u.gpr, h.kp, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Offset.add_ofNat_add_ofNat,
      show 16 * (60 + q) + 32 = 16 * (60 + (q + 2)) by omega_arith],
    by rw [u.other _ (by decide)]; exact h.tb,
    u.rd.trans h.rd, u.wr.trans h.wr, u.syms.trans h.syms, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.tab⟩

theorem PP.mem {m m' : Mem} {x : Nat → BitVec 64 × BitVec 64} (h : PP m B x) (e : m' = m) : PP m' B x := e ▸ h

/-- A pair of rounds. -/
theorem pair_wp (hs : SlotsIn m s₀ B) {n : Nat} (hk : Keys s₀.mem B n E) (hn : 60 + n ≤ m) (hq : q + 4 ≤ n) (h : At s₀ B q s)
    {x : Nat → BitVec 64 × BitVec 64} (hx : PP s.mem B x) {c : Nat} (hc : s.gpr .edx = BitVec.ofNat 32 c) (hc1 : 1 ≤ c)
    (hc3 : c ≤ 3) {N : BitVec 32} (hN : s.gpr .ecx = N) :
    WP isa (.block pairB) s fun s' => At s₀ B (q + 2) s' ∧
      PP s'.mem B (fun b => Proof.Camellia.pair (E (q + 2)) (E (q + 3)) (x b)) ∧
      s'.gpr .edx = BitVec.ofNat 32 (c - 1) ∧ s'.zf = some (decide (c = 1)) ∧ s'.gpr .ecx = N := by
  have st := parts_rounds
  simp only [Bool.and_eq_true] at st
  obtain ⟨s₁, r₁, a₁, x₁, y₁, g₁, _⟩ := round_ok h hs (by omega_arith) (r := 2) (src := d1) (dst := d2) (by decide) roundIn_chk1
    roundOut_chk2 st.1.1.1 st.1.1.2 (by decide) (by decide) (by decide) (by decide) (by decide) hx.1 hx.2
    (h.keyE hs hk hn (by omega_arith))
  obtain ⟨s₂, r₂, a₂, x₂, y₂, g₂, _⟩ := round_ok a₁ hs (by omega_arith) (r := 3) (src := d2) (dst := d1) (by decide) roundIn_chk2
    roundOut_chk1 st.1.2 st.2 (by decide) (by decide) (by decide) (by decide) (by decide) y₁ x₁
    (a₁.keyE hs hk hn (by omega_arith))
  have hg : s₂.gpr = s.gpr := g₂.trans g₁
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₂, run_append r₁ r₂, ?_⟩)
  refine Wp.wp_addi fun s₃ u₃ => Wp.wp_subi fun s₄ u₄ _ z₄ => WP.block_nil ?_
  have e₃ : s₃.gpr .edx = BitVec.ofNat 32 c := by rw [u₃.other _ (by decide), hg, hc]
  refine ⟨(a₂.next u₃).upd u₄ (by decide), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [u₄.mem, u₃.mem]; exact y₂
  · rw [u₄.mem, u₃.mem]; exact x₂
  · rw [u₄.gpr, e₃]; exact Wp.ofNat_pred hc1
  · rw [z₄, e₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_arith) (by decide)]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), hg, hN]

/-- `t` pairs of rounds from subkey `q + 2` on. -/
def pairsE (E : Nat → BitVec 64) (q t : Nat) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (List.range t).foldl (fun d t => Proof.Camellia.pair (E (q + 2 * t + 2)) (E (q + 2 * t + 3)) d) d

theorem pairsE_succ (q t : Nat) (d : BitVec 64 × BitVec 64) :
    pairsE E q (t + 1) d = Proof.Camellia.pair (E (q + 2 * t + 2)) (E (q + 2 * t + 3)) (pairsE E q t d) := by
  simp only [pairsE, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem pairsE_tri (i : Nat) (d : BitVec 64 × BitVec 64) : pairsE E (8 * i) 3 d = AesNi.tri E i d := by
  show Proof.Camellia.pair (E (8 * i + 2 * 2 + 2)) (E (8 * i + 2 * 2 + 3)) (Proof.Camellia.pair (E (8 * i + 2 * 1 + 2))
    (E (8 * i + 2 * 1 + 3)) (Proof.Camellia.pair (E (8 * i + 2 * 0 + 2)) (E (8 * i + 2 * 0 + 3)) d)) = _
  rw [AesNi.tri, show 8 * i + 2 * 2 + 2 = 2 + 8 * i + 4 by omega_arith, show 8 * i + 2 * 2 + 3 = 2 + 8 * i + 5 by omega_arith,
    show 8 * i + 2 * 1 + 2 = 2 + 8 * i + 2 by omega_arith, show 8 * i + 2 * 1 + 3 = 2 + 8 * i + 3 by omega_arith,
    show 8 * i + 2 * 0 + 2 = 2 + 8 * i by omega_arith, show 8 * i + 2 * 0 + 3 = 2 + 8 * i + 1 by omega_arith]

/-- The three pairs of a group. -/
theorem pairs_wp (hs : SlotsIn m s₀ B) {n : Nat} (hk : Keys s₀.mem B n E) (hn : 60 + n ≤ m) (hq : q + 8 ≤ n) (h : At s₀ B q s)
    {x : Nat → BitVec 64 × BitVec 64} (hx : PP s.mem B x) (hd : s.gpr .edx = BitVec.ofNat 32 3) {N : BitVec 32}
    (hc : s.gpr .ecx = N) :
    WP isa (.loop (.block pairB) .ne) s fun s' => At s₀ B (q + 6) s' ∧ PP s'.mem B (fun b => pairsE E q 3 (x b)) ∧
      s'.gpr .ecx = N := by
  refine WP.loop (M := isa) (fun (k : Nat) (s' : State) => 1 ≤ k ∧ k ≤ 3 ∧ At s₀ B (q + 2 * (3 - k)) s' ∧
    PP s'.mem B (fun b => pairsE E q (3 - k) (x b)) ∧ s'.gpr .edx = BitVec.ofNat 32 k ∧ s'.gpr .ecx = N) ?_ 3 s
    ⟨by decide, by decide, by rw [Nat.sub_self]; exact h,
      by rw [Nat.sub_self, show (fun b => pairsE E q 0 (x b)) = x from rfl]; exact hx, hd, hc⟩
  rintro k t ⟨h1, h3, a, px, hd, hcx⟩
  refine WP.mono (pair_wp hs hk hn (by omega_arith) a px hd h1 h3 hcx) fun t' ⟨a', p', d', z', c'⟩ => ?_
  have e : (fun b => Proof.Camellia.pair (E (q + 2 * (3 - k) + 2)) (E (q + 2 * (3 - k) + 3)) (pairsE E q (3 - k) (x b))) =
      fun b => pairsE E q (3 - (k - 1)) (x b) := funext fun b => by
    rw [← pairsE_succ, show 3 - k + 1 = 3 - (k - 1) by omega_arith]
  rw [e] at p'
  rw [show q + 2 * (3 - k) + 2 = q + 2 * (3 - (k - 1)) by omega_arith] at a'
  by_cases hk1 : k = 1
  · subst hk1
    exact .inl ⟨by show t'.zf.map _ = _; rw [z']; rfl, a', p', c'⟩
  · exact .inr ⟨by show t'.zf.map _ = _; rw [z', decide_eq_false hk1]; rfl, k - 1, by omega_arith, by omega_arith,
      by omega_arith, a', p', d', c'⟩

/-- The six rounds of a group. -/
theorem group_wp (hs : SlotsIn m s₀ B) {n : Nat} (hk : Keys s₀.mem B n E) (hn : 60 + n ≤ m) (hq : q + 8 ≤ n) (h : At s₀ B q s)
    {x : Nat → BitVec 64 × BitVec 64} (hx : PP s.mem B x) {c : Nat} (hc : s.gpr .ecx = BitVec.ofNat 32 c) (hc1 : 1 ≤ c)
    (hc3 : c ≤ 4) :
    WP isa Impl.Camellia.X86.Sse.group s fun s' => At s₀ B (q + 6) s' ∧ PP s'.mem B (fun b => pairsE E q 3 (x b)) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (c - 1) ∧ s'.zf = some (decide (c = 1)) := by
  refine WP.seq (Wp.wp_movi fun s₁ u₁ => WP.block_nil (WP.seq (WP.mono
    (pairs_wp hs hk hn hq (h.upd u₁ (by decide)) (hx.mem u₁.mem) u₁.gpr ((u₁.other _ (by decide)).trans hc))
    fun s₂ ⟨a₂, x₂, c₂⟩ => ?_)))
  refine Wp.wp_subi fun s₃ u₃ _ z₃ => WP.block_nil ⟨a₂.upd u₃ (by decide), x₂.mem u₃.mem, ?_, ?_⟩
  · rw [u₃.gpr, c₂]; exact Wp.ofNat_pred hc1
  · rw [z₃, c₂, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_arith) (by decide)]

/-- FL and FL⁻¹ between groups. -/
theorem layer_wp (hs : SlotsIn m s₀ B) {n : Nat} (hk : Keys s₀.mem B n E) (hn : 60 + n ≤ m) (hq : q + 4 ≤ n) (h : At s₀ B q s)
    {x : Nat → BitVec 64 × BitVec 64} (hx : PP s.mem B x) {c : Nat} (hc : s.gpr .ecx = BitVec.ofNat 32 c) (hc1 : 1 ≤ c)
    (hc3 : c ≤ 4) :
    WP isa (.block layer) s fun s' => At s₀ B (q + 2) s' ∧
      PP s'.mem B (fun b => (Spec.Camellia.fl (x b).1 (E (q + 2)), Spec.Camellia.flinv (x b).2 (E (q + 3)))) ∧
      s'.gpr .ecx = BitVec.ofNat 32 c ∧ s'.zf = some false := by
  obtain ⟨s₁, r₁, a₁, x₁, g₁, k₁⟩ := fl_ok h hs (by omega_arith) hx.1 (h.keyE hs hk hn (by omega_arith))
  obtain ⟨s₂, r₂, a₂, x₂, g₂, k₂⟩ := flinv_ok a₁ hs (by omega_arith) (k₁ d2 (by decide) (by decide) _ hx.2)
    (a₁.keyE hs hk hn (by omega_arith))
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₂, run_append r₁ r₂, ?_⟩)
  refine Wp.wp_addi fun s₃ u₃ => Wp.wp_test fun s₄ u₄ z₄ => WP.block_nil ?_
  have c₃ : s₃.gpr .ecx = BitVec.ofNat 32 c := by rw [u₃.other _ (by decide), g₂, g₁, hc]
  have a₃ := a₂.next u₃
  refine ⟨⟨by rw [u₄.gpr]; exact a₃.base, by rw [u₄.gpr]; exact a₃.esp, by rw [u₄.gpr]; exact a₃.kp,
    by rw [u₄.gpr]; exact a₃.tb, u₄.rd.trans a₃.rd, u₄.wr.trans a₃.wr, u₄.syms.trans a₃.syms,
    by rw [u₄.mem]; exact a₃.frame, by rw [u₄.mem]; exact a₃.tab⟩, ⟨?_, ?_⟩, by rw [u₄.gpr]; exact c₃, ?_⟩
  · rw [u₄.mem, u₃.mem]; exact k₂ d1 (by decide) (by decide) _ x₁
  · rw [u₄.mem, u₃.mem]; exact x₂
  · rw [z₄, c₃, BitVec.and_self, Wp.ofNat_beq_zero (by omega_arith), decide_eq_false (by omega_arith)]

/-- The groups of rounds, the layers between them. -/
theorem loop_wp (hs : Scr s₀ B) (hg : g = 3 ∨ g = 4) (hk : Keys s₀.mem B (8 * g + 2) E) (h : At s₀ B 0 s)
    {x : Nat → BitVec 64 × BitVec 64} (hx : PP s.mem B x) (hc : s.gpr .ecx = BitVec.ofNat 32 g) :
    WP isa (.loop (.seq Impl.Camellia.X86.Sse.group (.ite .e (.block []) (.block layer))) .ne) s fun s' =>
      At s₀ B (8 * g - 2) s' ∧ PP s'.mem B (fun b => Proof.Camellia.groups g E (x b)) := by
  refine WP.loop (M := isa) (fun (k : Nat) (s' : State) => 1 ≤ k ∧ k ≤ g ∧ At s₀ B (8 * (g - k)) s' ∧
    PP s'.mem B (fun b => (List.range (g - k)).foldl (Proof.Camellia.group g E) (x b)) ∧
    s'.gpr .ecx = BitVec.ofNat 32 k) ?_ g s
    ⟨by omega_arith, Nat.le_refl _, by rw [Nat.sub_self]; exact h, by rw [Nat.sub_self]; exact hx, hc⟩
  rintro k t ⟨h1, h3, a, px, hcx⟩
  refine WP.seq (WP.mono (group_wp hs.slots hk (by omega_arith) (by omega_arith) a px hcx h1 (by omega_arith))
    fun s₁ ⟨a₁, p₁, c₁, z₁⟩ => ?_)
  refine WP.ite (decide (k = 1)) z₁ (fun hb => WP.block_nil (.inl ⟨?_, ?_⟩)) fun hb => ?_
  · show s₁.zf.map _ = _
    rw [z₁, hb]; rfl
  · have h1 : k = 1 := of_decide_eq_true hb
    subst h1
    refine ⟨by rw [show 8 * g - 2 = 8 * (g - 1) + 6 by omega_arith]; exact a₁, ?_⟩
    have e : (fun b => Proof.Camellia.groups g E (x b)) =
        fun b => pairsE E (8 * (g - 1)) 3 ((List.range (g - 1)).foldl (Proof.Camellia.group g E) (x b)) := funext fun b => by
      have := AesNi.foldl_group g E (x b) (g - 1)
      rw [Nat.sub_add_cancel h3] at this
      rw [Proof.Camellia.groups, this, AesNi.group_eq, ite_eq_right (by omega_arith), pairsE_tri]
    rw [e]
    exact p₁
  · have h1 : k ≠ 1 := of_decide_eq_false hb
    refine WP.mono (layer_wp hs.slots hk (by omega_arith) (by omega_arith) a₁ p₁ c₁ (by omega_arith) (by omega_arith))
      fun s₂ ⟨a₂, p₂, c₂, z₂⟩ => .inr ⟨?_, k - 1, by omega_arith, by omega_arith, by omega_arith, ?_, ?_, c₂⟩
    · show s₂.zf.map _ = _
      rw [z₂]; rfl
    · rw [show 8 * (g - (k - 1)) = 8 * (g - k) + 6 + 2 by omega_arith]; exact a₂
    · have e : (fun b => (List.range (g - (k - 1))).foldl (Proof.Camellia.group g E) (x b)) = fun b =>
          (Spec.Camellia.fl (pairsE E (8 * (g - k)) 3 ((List.range (g - k)).foldl (Proof.Camellia.group g E) (x b))).1
              (E (8 * (g - k) + 6 + 2)),
            Spec.Camellia.flinv (pairsE E (8 * (g - k)) 3 ((List.range (g - k)).foldl (Proof.Camellia.group g E) (x b))).2
              (E (8 * (g - k) + 6 + 3))) := funext fun b => by
        rw [show g - (k - 1) = g - k + 1 by omega_arith, AesNi.foldl_group, AesNi.group_eq, ite_eq_left (by omega_arith),
          pairsE_tri, show 8 * (g - k) + 6 + 2 = 8 + 8 * (g - k) by omega_arith,
          show 8 * (g - k) + 6 + 3 = 9 + 8 * (g - k) by omega_arith]
      rw [e]
      exact p₂

/-- The address of block `b` of the buffer. -/
abbrev blk (B : BitVec 32) (b : Nat) : Addr := B.setWidth 64 + BitVec.ofNat 64 (16 * (bufS + b))

/-- The halves of a block in memory. -/
def halves (m : Mem) (p : Addr) : BitVec 64 × BitVec 64 :=
  ((Spec.Camellia.decodeBlock (Spec.Camellia.blockAt m p) >>> 64).setWidth 64,
    (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt m p)).setWidth 64)

theorem cryptHead_wp (h : At s₀ B 0 s) (hs : Scr s₀ B) (hk : Keys s₀.mem B (8 * g + 2) E) (hg : g = 3 ∨ g = 4) :
    ∃ s', runBlock isa cryptHead s = some s' ∧ At s₀ B 0 s' ∧ s'.gpr = s.gpr ∧
      PP s'.mem B (fun b => ((halves s.mem (blk B b)).1 ^^^ E 0, (halves s.mem (blk B b)).2 ^^^ E 1)) := by
  have hf := hs.fit
  have hbs : bufS = 44 := rfl
  have st := parts_whiten
  have c := whiten_chk
  simp only [Bool.and_eq_true] at st c
  obtain ⟨s₁, r₁, a₁, g₁, _, v₁⟩ := blocksIn_ok h hs.slots (by decide)
  have x₁ : PAt s₁.mem B d1 (fun b => (halves s.mem (blk B b)).1) := fun b hb i hi j hj => by
    rw [(v₁ b hb i hi j hj).1, W_bit _ (by omega_arith) (by omega_arith) hj]
    simp only [halves]
    rw [Proof.Camellia.byteOf_hi _ hi, AesNi.blockAt_get _ _ (by omega_arith), Offset.add_ofNat_add_ofNat]
  have y₁ : PAt s₁.mem B d2 (fun b => (halves s.mem (blk B b)).2) := fun b hb i hi j hj => by
    rw [(v₁ b hb i hi j hj).2, W_bit _ (by omega_arith) (by omega_arith) hj]
    simp only [halves]
    rw [Proof.Camellia.byteOf_lo _ hi, AesNi.blockAt_get _ _ (by omega_arith), Offset.add_ofNat_add_ofNat]
  obtain ⟨s₂, r₂, a₂, x₂, g₂, k₂⟩ := whiten_ok a₁ hs.slots (by decide) (r := 0) (d := d1) (by decide) c.1.1.1 st.1.1.1 (by decide) (by decide) x₁
    (a₁.keyE hs.slots hk (by omega_arith) (by omega_arith))
  obtain ⟨s₃, r₃, a₃, x₃, g₃, k₃⟩ := whiten_ok a₂ hs.slots (by decide) (r := 1) (d := d2) (by decide) c.1.1.2 st.1.1.2 (by decide) (by decide)
    (k₂ d2 (by decide) (by decide) _ y₁) (a₂.keyE hs.slots hk (by omega_arith) (by omega_arith))
  exact ⟨s₃, by rw [cryptHead, List.append_assoc]; exact run_append r₁ (run_append r₂ r₃), a₃,
    g₃.trans (g₂.trans g₁), k₃ d1 (by decide) (by decide) _ x₂, x₃⟩

theorem cryptTail_wp (h : At s₀ B (8 * g - 2) s) (hs : Scr s₀ B) (hk : Keys s₀.mem B (8 * g + 2) E) (hg : g = 3 ∨ g = 4)
    {x : Nat → BitVec 64 × BitVec 64} (hx : PP s.mem B x) :
    ∃ s', runBlock isa cryptTail s = some s' ∧ At s₀ B (8 * g - 2) s' ∧
      ∀ b < 16, Spec.Aes.bytesAt s'.mem (blk B b) 16 =
        (Spec.Camellia.encodeBlock (((x b).2 ^^^ E (8 * g)) ++ ((x b).1 ^^^ E (8 * g + 1)))).toList := by
  have hf := hs.fit
  have hbs : bufS = 44 := rfl
  have st := parts_whiten
  have c := whiten_chk
  simp only [Bool.and_eq_true] at st c
  obtain ⟨s₁, r₁, a₁, x₁, g₁, k₁⟩ := whiten_ok h hs.slots (by omega_arith) (r := 2) (d := d2) (by decide) c.1.2 st.1.2 (by decide) (by decide)
    hx.2 (h.keyE hs.slots hk (by omega_arith) (by omega_arith))
  obtain ⟨s₂, r₂, a₂, x₂, g₂, k₂⟩ := whiten_ok a₁ hs.slots (by omega_arith) (r := 3) (d := d1) (by decide) c.2 st.2 (by decide) (by decide)
    (k₁ d1 (by decide) (by decide) _ hx.1) (a₁.keyE hs.slots hk (by omega_arith) (by omega_arith))
  obtain ⟨s₃, r₃, a₃, g₃, v₃⟩ := blocksOut_ok a₂ hs.slots (by omega_arith)
  have y₂ := k₂ d2 (by decide) (by decide) _ x₁
  rw [show 8 * g - 2 + 2 = 8 * g by omega_arith] at y₂
  rw [show 8 * g - 2 + 3 = 8 * g + 1 by omega_arith] at x₂
  refine ⟨s₃, by rw [cryptTail, List.append_assoc]; exact run_append r₁ (run_append r₂ r₃), a₃, fun b hb => ?_⟩
  refine List.ext_getElem (by simp [Spec.Aes.bytesAt]) fun q h₁ _ => ?_
  have hq : q < 16 := by simpa [Spec.Aes.bytesAt] using h₁
  rw [Vector.getElem_toList, Proof.Camellia.encodeBlock_getElem _ _ hq]
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, Offset.add_ofNat_add_ofNat]
  refine Proof.Aes.byte_ext fun j hj => ?_
  rw [← W_bit _ (by omega_arith) hq hj]
  by_cases h8 : q < 8
  · rw [ite_eq_left h8, (v₃ b hb q h8 j hj).1, y₂ b hb q h8 j hj]
  · have := (v₃ b hb (q - 8) (by omega_arith) j hj).2
    rw [show 8 + (q - 8) = q by omega_arith] at this
    rw [ite_eq_right h8, this, x₂ b hb _ (by omega_arith) j hj]

/-- The block function, on sixteen blocks. -/
theorem cryptFn_wp (hs : Scr s B) (hg : g = 3 ∨ g = 4) (hk : Keys s.mem B (8 * g + 2) E)
    (hB : s.gpr Impl.Modes.X86.sb = B) (hkr : s.gpr kr = B + BitVec.ofNat 32 (16 * 60))
    (htb : s.gpr tbr = s.syms tableName) (hc : s.gpr .ecx = BitVec.ofNat 32 g) :
    WP isa cryptFn s fun s' => At s B (8 * g - 2) s' ∧
      ∀ b < 16, Spec.Aes.bytesAt s'.mem (blk B b) 16 =
        (Spec.Camellia.encodeBlock (Proof.Camellia.cryptWords g E (Spec.Camellia.decodeBlock
          (Spec.Camellia.blockAt s.mem (blk B b))))).toList := by
  have h : At s B 0 s := ⟨hB, rfl, hkr, htb, rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  obtain ⟨s₁, r₁, a₁, g₁, x₁⟩ := cryptHead_wp h hs hk hg
  refine WP.seq (WP.of_runBlock ⟨s₁, r₁, WP.seq (WP.mono (loop_wp hs hg hk a₁ x₁ (by rw [g₁, hc])) fun s₂ ⟨a₂, x₂⟩ => ?_)⟩)
  obtain ⟨s₃, r₃, a₃, v₃⟩ := cryptTail_wp a₂ hs hk hg x₂
  exact WP.of_runBlock ⟨s₃, r₃, a₃, v₃⟩

/-! ## The core's code -/

/-- `crypt`: the block function, called. -/
theorem crypt_wp {R : Nat} (hB : s.gpr Impl.Modes.X86.sb = B) (hs : Scr s B) (hR : R = 18 ∨ R = 24)
    (hk : Keys s.mem B (8 * (R / 6) + 2) E) (hin : InRegions (s.rd ++ s.wr) (s.ea (Impl.Modes.X86.argOp 1)) 4)
    (hv : s.mem.readW (s.ea (Impl.Modes.X86.argOp 1)) 32 = BitVec.ofNat 32 R)
    (htab : s.mem.readW (addr B 416) 32 = s.syms tableName)
    (hst : Region.Disjoint (below (s.gpr .esp) 4) ⟨B.setWidth 64, 1544⟩) :
    WP isa crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.syms = s.syms ∧ Frame [slotsR B 0 60, below (s.gpr .esp) 4] s.mem s'.mem ∧
      W s'.mem B tblSlot = W s.mem B tblSlot ∧
      ∀ b < 16, Spec.Aes.bytesAt s'.mem (blk B b) 16 =
        (Spec.Camellia.encodeBlock (Proof.Camellia.cryptWords (R / 6) E (Spec.Camellia.decodeBlock
          (Spec.Camellia.blockAt s.mem (blk B b))))).toList := by
  have hf := hs.fit
  refine WP.seq ?_
  show WP isa (.block (.mov tbr (.mem ⟨Impl.Modes.X86.sb, 416⟩) :: .mov .ecx (.mem ⟨.esp, 4 + 4 * 1⟩) ::
    .shift .shr .ecx 3 :: .alu .add .ecx (.imm 1) :: .mov kr (.reg Impl.Modes.X86.sb) :: [.alu .add kr (.imm 960)])) s _
  refine Wp.wp_ldm hB ⟨_, List.mem_append_right _ hs.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by decide) (by decide)⟩ fun s₁ u₁ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (u₁.other _ (by decide)) (by rw [u₁.rd, u₁.wr]; exact hin) fun s₂ u₂ => ?_
  refine Wp.wp_shr (by decide) fun s₃ u₃ _ => Wp.wp_addi fun s₄ u₄ => Wp.wp_mov fun s₅ u₅ => Wp.wp_addi fun s₆ u₆ =>
    WP.block_nil ?_
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sy₆ : s₆.syms = s.syms := by rw [u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  have sp₆ : s₆.gpr .esp = s.gpr .esp := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  have B₆ : s₆.gpr Impl.Modes.X86.sb = B := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have t₆ : s₆.gpr tbr = s.syms tableName := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, htab]
  have c₆ : s₆.gpr .ecx = BitVec.ofNat 32 (R / 6) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem]
    show (s.mem.readW (s.ea (Impl.Modes.X86.argOp 1)) 32 >>> 3) + 1 = _
    rw [hv]
    rcases hR with rfl | rfl <;> rfl
  have k₆ : s₆.gpr kr = B + BitVec.ofNat 32 (16 * 60) := by
    rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hB]; rfl
  have hce : Frame [below (s.gpr .esp) 4] s.mem s₆.callEntry.mem := by
    rw [State.callEntry_mem, m₆, sp₆]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have keep : ∀ k < 96, W s₆.callEntry.mem B k = W s.mem B k := fun k hk => by
    refine W_frame hce (by omega_arith) fun r hr => ?_
    rw [List.mem_singleton] at hr; subst hr
    exact (hst.sub_right (Offset.sub_base _ (by omega_arith))).symm
  have hbs : bufS = 44 := rfl
  have kb : ∀ b < 16, Spec.Camellia.blockAt s₆.callEntry.mem (blk B b) = Spec.Camellia.blockAt s.mem (blk B b) := fun b hb => by
    simp only [Spec.Camellia.blockAt]
    congr 1
    funext i
    have hi := i.isLt
    refine hce.bytes (R := ⟨blk B b, 16⟩) (fun r hr => ?_) (by show (16 : Nat) ≤ 2 ^ 64; decide) hi
    rw [List.mem_singleton] at hr; subst hr
    exact (hst.sub_right (Offset.sub_base _ (by omega_arith))).symm
  have hs₆ : Scr s₆.callEntry B := ⟨by rw [State.callEntry_wr, wr₆]; exact hs.wr, hf⟩
  refine WP.callBody (WP.mono (cryptFn_wp (E := E) (g := R / 6) hs₆ (by omega_arith)
    (fun k hk' => by rw [keep _ (by omega_arith)]; exact hk k hk')
    (by rw [State.callEntry_gpr _ (by decide), B₆]) (by rw [State.callEntry_gpr _ (by decide), k₆])
    (by rw [State.callEntry_gpr _ (by decide), t₆]; exact (congrFun sy₆ _).symm) (by rw [State.callEntry_gpr _ (by decide), c₆]))
    fun u ⟨a, v⟩ => ⟨by rw [a.esp, State.callEntry_esp], ?_, ?_⟩)
  · have e := a.frame.readW (r := ⟨(s₆.gpr .esp - 4).setWidth 64, 4⟩) (a := (s₆.gpr .esp - 4).setWidth 64) (w := 32)
      (Region.contains_self _ 4) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        rw [sp₆]
        exact hst.sub_right (Offset.sub_base _ (by decide))) (by decide)
    rw [e, State.callEntry_mem, Mem.readW_writeW_self32]
  · refine ⟨a.base, by simp [State.setReg, sp₆], a.rd.trans (by rw [State.callEntry_rd, rd₆]),
      a.wr.trans (by rw [State.callEntry_wr, wr₆]), a.syms.trans sy₆, ?_, ?_, fun b hb => ?_⟩
    · exact (hce.mono fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self).trans
        (a.frame.mono fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
    · exact a.tab.trans (keep _ (by decide))
    · rw [← kb b hb]; exact v b hb

/-! ## The subkeys -/

theorem wp_movi_x {d : Reg} {v : BitVec 32} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Wp.Upd s s' d v → s'.xmm = s.xmm → WP isa (.block is) s' Q) : WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.setReg _ _ _) rfl)


/-- The low byte of every 16-bit lane. -/
def lowM : BitVec 128 := 0x00ff00ff00ff00ff00ff00ff00ff00ff#128

theorem lowM_bit : ∀ p < 128, lowM.getLsbD p = decide (p % 16 < 8) := by decide

/-- A subkey's eight bytes, one in each 16-bit lane. -/
theorem spread_mem (m : Mem) (a : Addr) :
    XBinOp.eval .punpcklwd (((0 : BitVec 64) ++ m.readW a 64) &&& lowM)
      (XShiftOp.eval .psrld ((0 : BitVec 64) ++ m.readW a 64) 8 &&& lowM) = spread (Spec.Camellia.wordAt m a) := by
  have hv : ∀ i < 8, ∀ j < 8, ((0 : BitVec 64) ++ m.readW a 64).getLsbD (8 * i + j) =
      (byteOf (Spec.Camellia.wordAt m a) i).getLsbD j := fun i hi j hj => by
    rw [Proof.Camellia.byteOf_wordAt _ _ hi, ← byte_readW m a (w := 64) (by omega_arith), BitVec.getLsbD_append,
      ite_eq_left (by omega_arith), BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
  refine BitVec.eq_of_getLsbD_eq fun p hp => ?_
  obtain ⟨V, hV⟩ : ∃ V : BitVec 128, V = (0 : BitVec 64) ++ m.readW a 64 := ⟨_, rfl⟩
  rw [← hV] at hv ⊢
  rw [spread, getLsbD_ofBits, decide_eq_true hp, Bool.true_and]
  by_cases ho : p / 16 % 2 = 1
  · rw [bin_bit (op := .punpcklwd) (s := true) (q := 16 * (p / 32) + p % 16) _ _ hp (by simp [binSrc, ho]), ite_eq_left rfl,
      BitVec.getLsbD_and, lowM_bit _ (by omega_arith), show (16 * (p / 32) + p % 16) % 16 = p % 16 by omega_arith, Bool.and_comm]
    by_cases h8 : p % 16 < 8
    · refine congrArg _ ?_
      have := shift_bit .psrld 8 V (p := 16 * (p / 32) + p % 16) (by omega_arith)
      rw [this]
      simp only [Un.src, show (8 : BitVec 8).toNat = 8 from rfl]
      rw [ite_eq_left (by omega_arith), bitOpt, ← hv _ (by omega_arith) _ h8]
      exact congrArg _ (by omega_arith)
    · rw [decide_eq_false h8, Bool.false_and, Bool.false_and]
  · rw [bin_bit (op := .punpcklwd) (s := false) (q := 16 * (p / 32) + p % 16) _ _ hp (by simp [binSrc, ho]),
      ite_eq_right (by decide),
      BitVec.getLsbD_and, lowM_bit _ (by omega_arith), show (16 * (p / 32) + p % 16) % 16 = p % 16 by omega_arith, Bool.and_comm]
    by_cases h8 : p % 16 < 8
    · refine congrArg _ ?_
      rw [← hv _ (by omega_arith) _ h8]
      exact congrArg _ (by omega_arith)
    · rw [decide_eq_false h8, Bool.false_and, Bool.false_and]

/-- What a step of `prepare`'s loops needs: the next subkey read is the
`a`th of the schedule at `p`, and those up to `k` of `F` are in their places. -/
structure Pr (s₁ : State) (B p : BitVec 32) (F : Nat → BitVec 64) (a k : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₁.gpr .esp
  tb : s.gpr tbr = s₁.syms tableName
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  syms : s.syms = s₁.syms
  src : s.gpr .eax = p + BitVec.ofNat 32 (8 * a)
  dst : s.gpr kr = B + BitVec.ofNat 32 (16 * (60 + k))
  x7 : s.xmm .xmm7 = lowM
  x6 : s.xmm .xmm6 = uW
  frame : Frame [slotsR B 60 34] s₁.mem s.mem
  keys : Keys s.mem B k F

/-- The schedule, readable and apart from the scratch buffer. -/
structure SchIn (s₁ : State) (B p : BitVec 32) : Prop where
  rd : (⟨p.setWidth 64, 272⟩ : Region) ∈ s₁.rd ++ s₁.wr
  fit : p.toNat + 272 ≤ 2 ^ 32
  dis : Region.Disjoint ⟨p.setWidth 64, 272⟩ ⟨B.setWidth 64, 1544⟩

theorem Pr.src8 {s₁ : State} {p : BitVec 32} {F : Nat → BitVec 64} {a k : Nat} (h : Pr s₁ B p F a k s) (hp : SchIn s₁ B p)
    (ha : a < 34) : addr (s.gpr .eax) 0 = p.setWidth 64 + BitVec.ofNat 64 (8 * a) := by
  have := hp.fit
  rw [h.src, Straight.addr_add_ofNat, Nat.add_zero, addr_eq (by omega_arith)]

/-- The registers' part of `prepOne`. -/
theorem prepMid_ok {V : BitVec 128} {k : BitVec 64} (h6 : s.xmm .xmm6 = uW) (h7 : s.xmm .xmm7 = lowM) (h0 : s.xmm .xmm0 = V)
    (htb : s.gpr tbr = s.syms tableName)
    (hval : XBinOp.eval .punpcklwd (V &&& lowM) (XShiftOp.eval .psrld V 8 &&& lowM) = spread k) :
    ∃ t, runBlock isa prepMid s = some t ∧ t.xmm .xmm0 = spread k ^^^ uW ∧ t.xmm .xmm6 = uW ∧ t.xmm .xmm7 = lowM ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms := by
  have hok : Ok cfg0 s := ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun k hk => absurd hk (Nat.not_lt_zero _),
    Nat.le_of_lt (s.gpr cfg0.base).isLt, fun k hk => absurd hk (Nat.not_lt_zero _), htb⟩
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ prepMid_chk
  have hrel : Rel (fun (e : XE) v => v = e.eval fun n => if n = 0 then V else if n = 6 then uW else lowM) cfg0 (fun _ => none)
      prepEnv s := by
    refine ⟨fun r a ha => ?_, fun k a hk => absurd hk (Nat.not_lt_zero _), fun k a hk => absurd hk (Nat.not_lt_zero _)⟩
    cases r <;> simp only [prepEnv, reduceCtorEq, Option.some.injEq] at ha <;> subst ha
    · exact h0
    · exact h6
    · exact h7
  obtain ⟨t, ht, pt⟩ := run (exprs_sound _) hok hrel he
  refine ⟨t, ht, ?_, (pt.other .xmm6 rfl).trans h6, (pt.other .xmm7 rfl).trans h7, pt.gpr, run_mem rfl ht, pt.rd, pt.wr, pt.syms⟩
  rw [pt.rel.reg .xmm0 _ (eq_of_beq hpost)]
  simp only [XE.eval, ite_true, show ¬ 7 = 0 by decide, show ¬ 7 = 6 by decide, show ¬ 6 = 0 by decide, ite_false]
  exact congrArg (· ^^^ uW) hval

/-- `prepOne`, on the machine. -/
theorem prepOne_run {p : Addr} {q : Addr} (hp : addr (s.gpr .eax) 0 = p) (hq : addr (s.gpr kr) 0 = q)
    (hin : InRegions (s.rd ++ s.wr) p 8) (hout : InRegions s.wr q 16) (h6 : s.xmm .xmm6 = uW) (h7 : s.xmm .xmm7 = lowM)
    (htb : s.gpr tbr = s.syms tableName) {is : List Instr} {Q : State → Prop}
    (K : ∀ u, Wp.Upd { s with mem := s.mem.writeW q (spread (Spec.Camellia.wordAt s.mem p) ^^^ uW) } u kr (s.gpr kr + 16) →
      u.xmm .xmm6 = uW → u.xmm .xmm7 = lowM → WP isa (.block is) u Q) :
    WP isa (.block (prepOne ++ is)) s Q := by
  have r0 : exec (.movqLoad .xmm0 (Impl.Modes.X86.at_ .eax 0)) s = some (s.setXmm .xmm0 ((0 : BitVec 64) ++ s.mem.readW p 64)) := by
    show (s.load64 (addr (s.gpr .eax) 0)).map _ = _
    rw [hp]
    simp only [State.load64, hin, ite_true, Option.map_some]
  obtain ⟨t, ht, x0, x6, x7, tg, tm, trd, tw, ts⟩ := prepMid_ok (s := s.setXmm .xmm0 ((0 : BitVec 64) ++ s.mem.readW p 64))
    h6 h7 rfl htb (spread_mem s.mem p)
  have r1 : exec (stx kr 0 .xmm0) t = some { t with mem := t.mem.writeW q (t.xmm .xmm0) } := by
    show t.store128 (addr (t.gpr kr) 0) _ = _
    have hq' : addr (t.gpr kr) 0 = q := by rw [tg]; exact hq
    have ho : InRegions t.wr q 16 := by rw [tw]; exact hout
    rw [hq']
    simp only [State.store128, ho, ite_true]
  have hpr : prepOne ++ is = .movqLoad .xmm0 (Impl.Modes.X86.at_ .eax 0) :: (prepMid ++ (stx kr 0 .xmm0 ::
      .alu .add kr (.imm 16) :: is)) := rfl
  rw [hpr]
  refine Wp.cons r0 (WP.block_append_iff.mpr (WP.of_runBlock ⟨t, ht, Wp.cons r1 (AesNi.wp_addi_x fun u uu ux =>
    K u ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_)⟩))
  · rw [uu.gpr]; exact congrArg (· + 16) (congrFun tg kr)
  · rw [uu.other _ hr]; exact congrFun tg r
  · rw [uu.mem]
    show t.mem.writeW q (t.xmm .xmm0) = s.mem.writeW q _
    rw [x0, tm]; rfl
  · rw [uu.rd]; exact trd
  · rw [uu.wr]; exact tw
  · rw [uu.syms]; exact ts
  · rw [ux]; exact x6
  · rw [ux]; exact x7

theorem prepOne_wp {s₁ : State} {p : BitVec 32} {F : Nat → BitVec 64} {a k : Nat} (hs : Scr s₁ B) (hp : SchIn s₁ B p)
    (h : Pr s₁ B p F a k s) (ha : a < 34) (hk : k < 34) (hF : F k = AesNi.Ew s₁.mem p a) {is : List Instr} {Q : State → Prop}
    (K : ∀ s', Pr s₁ B p F a (k + 1) s' → s'.gpr .ecx = s.gpr .ecx → WP isa (.block is) s' Q) :
    WP isa (.block (prepOne ++ is)) s Q := by
  have hf := hs.fit
  have hpf := hp.fit
  have ea : addr (s.gpr .eax) 0 = p.setWidth 64 + BitVec.ofNat 64 (8 * a) := h.src8 hp ha
  have ed : addr (s.gpr kr) 0 = B.setWidth 64 + BitVec.ofNat 64 (16 * (60 + k)) := by
    rw [h.dst, Straight.addr_add_ofNat, Nat.add_zero, addr_eq (by omega_arith)]
  have hw : Spec.Camellia.wordAt s.mem (p.setWidth 64 + BitVec.ofNat 64 (8 * a)) = F k := by
    rw [hF, AesNi.Ew]
    refine Proof.Camellia.wordAt_frame h.frame fun r hr => ?_
    rw [List.mem_singleton] at hr; subst hr
    exact (hp.dis.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by decide))
  refine prepOne_run ea ed ⟨_, by rw [h.rd, h.wr]; exact hp.rd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    ⟨_, by rw [h.wr]; exact hs.wr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ h.x6 h.x7
    (by rw [h.tb, h.syms]) fun u uu u6 u7 => K u ?_ (uu.other _ (by decide))
  rw [hw] at uu
  have um := uu.mem
  dsimp only at um
  have fr : Frame [slotsR B (60 + k) 1] s.mem u.mem := by
    rw [um]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
  refine ⟨(uu.other _ (by decide)).trans h.base, (uu.other _ (by decide)).trans h.esp, (uu.other _ (by decide)).trans h.tb,
    uu.rd.trans h.rd, uu.wr.trans h.wr, uu.syms.trans h.syms, (uu.other _ (by decide)).trans h.src, ?_, u7, u6, ?_,
    fun j hj => ?_⟩
  · rw [uu.gpr, h.dst, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.add_ofNat_add_ofNat,
      show 16 * (60 + k) + 16 = 16 * (60 + (k + 1)) by omega_arith]
  · exact h.frame.trans (fr.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩)
  · by_cases hjk : j = k
    · subst hjk
      rw [um]
      unfold W
      rw [addr16 (by omega_arith)]
      exact Mem.readW_writeW_self _ _ 16 _ (by decide)
    · rw [W_frame fr (by omega_arith) fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint (B.setWidth 64) (by omega_arith) (by omega_arith) (by omega_arith)]
      exact h.keys j (by omega_arith)

theorem Pr.move {s₁ s' : State} {p : BitVec 32} {F : Nat → BitVec 64} {a a' k : Nat} (h : Pr s₁ B p F a k s)
    {v : BitVec 32} (u : Wp.Upd s s' .eax v) (hx : s'.xmm = s.xmm) (hv : v = p + BitVec.ofNat 32 (8 * a')) : Pr s₁ B p F a' k s' :=
  ⟨(u.other _ (by decide)).trans h.base, (u.other _ (by decide)).trans h.esp, (u.other _ (by decide)).trans h.tb,
    u.rd.trans h.rd, u.wr.trans h.wr, u.syms.trans h.syms, u.gpr.trans hv, (u.other _ (by decide)).trans h.dst,
    by rw [hx]; exact h.x7, by rw [hx]; exact h.x6, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.keys⟩

theorem Pr.count {s₁ s' : State} {p : BitVec 32} {F : Nat → BitVec 64} {a k : Nat} (h : Pr s₁ B p F a k s)
    {v : BitVec 32} (u : Wp.Upd s s' .ecx v) (hx : s'.xmm = s.xmm) : Pr s₁ B p F a k s' :=
  ⟨(u.other _ (by decide)).trans h.base, (u.other _ (by decide)).trans h.esp, (u.other _ (by decide)).trans h.tb,
    u.rd.trans h.rd, u.wr.trans h.wr, u.syms.trans h.syms, (u.other _ (by decide)).trans h.src, (u.other _ (by decide)).trans h.dst,
    by rw [hx]; exact h.x7, by rw [hx]; exact h.x6, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.keys⟩

theorem add_back (p : BitVec 32) {a d : Nat} (h : d ≤ a) :
    p + BitVec.ofNat 32 (8 * a) - BitVec.ofNat 32 (8 * d) = p + BitVec.ofNat 32 (8 * (a - d)) := by
  rw [show 8 * a = 8 * (a - d) + 8 * d by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- A loop over the schedule's subkeys, upwards. -/
theorem upLoop_wp {s₁ : State} {p : BitVec 32} {F : Nat → BitVec 64} {n : Nat} (hs : Scr s₁ B) (hp : SchIn s₁ B p) (hn : n ≤ 34)
    (hn1 : 1 ≤ n) (hF : ∀ k < n, F k = AesNi.Ew s₁.mem p k) (h : Pr s₁ B p F 0 0 s) (hc : s.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa (.loop (.block (prepOne ++ [addE, .alu .sub .ecx (.imm 1)])) .ne) s fun s' => Pr s₁ B p F n n s' := by
  refine WP.loop (M := isa) (fun (c : Nat) (s' : State) => 1 ≤ c ∧ c ≤ n ∧ Pr s₁ B p F (n - c) (n - c) s' ∧
    s'.gpr .ecx = BitVec.ofNat 32 c) ?_ n s ⟨hn1, Nat.le_refl _, by rw [Nat.sub_self]; exact h, hc⟩
  rintro c t ⟨h1, h2, a, hcx⟩
  refine prepOne_wp hs hp a (by omega_arith) (by omega_arith) (hF _ (by omega_arith)) fun s₂ a₂ c₂ => ?_
  refine AesNi.wp_addi_x fun s₃ u₃ x₃ => AesNi.wp_subi_x fun s₄ u₄ x₄ z₄ => WP.block_nil ?_
  have a₃ : Pr s₁ B p F (n - (c - 1)) (n - c + 1) s₃ := a₂.move u₃ x₃ (by
    rw [a₂.src, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_ofNat_add_ofNat,
      show 8 * (n - c) + 8 = 8 * (n - (c - 1)) by omega_arith])
  rw [show n - c + 1 = n - (c - 1) by omega_arith] at a₃
  have e₃ : s₃.gpr .ecx = BitVec.ofNat 32 c := by rw [u₃.other _ (by decide), c₂, hcx]
  have a₄ := a₃.count u₄ x₄
  have z : s₄.zf = some (decide (c = 1)) := by
    rw [z₄, e₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_arith) (by decide)]
  by_cases hc1 : c = 1
  · subst hc1
    exact .inl ⟨by show s₄.zf.map _ = _; rw [z]; rfl, by simpa using a₄⟩
  · exact .inr ⟨by show s₄.zf.map _ = _; rw [z, decide_eq_false hc1]; rfl, c - 1, by omega_arith, by omega_arith, by omega_arith, a₄,
      by rw [u₄.gpr, e₃]; exact Wp.ofNat_pred h1⟩

/-- And downwards, from the `a`th to the second. -/
theorem downLoop_wp {s₁ : State} {p : BitVec 32} {F : Nat → BitVec 64} {a k : Nat} (hs : Scr s₁ B) (hp : SchIn s₁ B p)
    (ha : a < 34) (ha1 : 2 ≤ a) (hk : k + a - 1 ≤ 34) (hF : ∀ j < a - 1, F (k + j) = AesNi.Ew s₁.mem p (a - j))
    (h : Pr s₁ B p F a k s) (hc : s.gpr .ecx = BitVec.ofNat 32 (a - 1)) :
    WP isa (.loop (.block (prepOne ++ [subE, .alu .sub .ecx (.imm 1)])) .ne) s fun s' => Pr s₁ B p F 1 (k + a - 1) s' := by
  refine WP.loop (M := isa) (fun (c : Nat) (s' : State) => 1 ≤ c ∧ c ≤ a - 1 ∧ Pr s₁ B p F (c + 1) (k + (a - 1 - c)) s' ∧
    s'.gpr .ecx = BitVec.ofNat 32 c) ?_ (a - 1) s ⟨by omega_arith, Nat.le_refl _, by
      rw [Nat.sub_self, show a - 1 + 1 = a by omega_arith]; exact h, hc⟩
  rintro c t ⟨h1, h2, b, hcx⟩
  refine prepOne_wp hs hp b (by omega_arith) (by omega_arith) (by
    rw [hF _ (by omega_arith), show a - (a - 1 - c) = c + 1 by omega_arith]) fun s₂ a₂ c₂ => ?_
  refine AesNi.wp_subi_x fun s₃ u₃ x₃ _ => AesNi.wp_subi_x fun s₄ u₄ x₄ z₄ => WP.block_nil ?_
  have a₃ : Pr s₁ B p F c (k + (a - 1 - c) + 1) s₃ := a₂.move u₃ x₃ (by
    rw [a₂.src, show (8 : BitVec 32) = BitVec.ofNat 32 (8 * 1) from rfl, add_back _ (by omega_arith), Nat.add_sub_cancel])
  have e₃ : s₃.gpr .ecx = BitVec.ofNat 32 c := by rw [u₃.other _ (by decide), c₂, hcx]
  have a₄ := a₃.count u₄ x₄
  have z : s₄.zf = some (decide (c = 1)) := by
    rw [z₄, e₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_arith) (by decide)]
  by_cases hc1 : c = 1
  · subst hc1
    exact .inl ⟨by show s₄.zf.map _ = _; rw [z]; rfl, by
      rw [show k + (a - 1 - 1) + 1 = k + a - 1 by omega_arith] at a₄; exact a₄⟩
  · exact .inr ⟨by show s₄.zf.map _ = _; rw [z, decide_eq_false hc1]; rfl, c - 1, by omega_arith, by omega_arith, by omega_arith, by
      rw [show c - 1 + 1 = c by omega_arith, show k + (a - 1 - (c - 1)) = k + (a - 1 - c) + 1 by omega_arith]; exact a₄,
      by rw [u₄.gpr, e₃]; exact Wp.ofNat_pred h1⟩

theorem prepEnc_wp {s₁ : State} {p : BitVec 32} {R : Nat} (hR : R = 18 ∨ R = 24) (hs : Scr s₁ B) (hp : SchIn s₁ B p)
    (h : Pr s₁ B p (AesNi.Ew s₁.mem p) 0 0 s) (hz : s.zf = some (decide (R = 18))) :
    WP isa prepEnc s fun s' => ∃ a, Pr s₁ B p (AesNi.Ew s₁.mem p) a (8 * (R / 6) + 2) s' := by
  refine WP.seq (WP.mono (Q := fun (s' : State) => Pr s₁ B p (AesNi.Ew s₁.mem p) 0 0 s' ∧
    s'.gpr .ecx = BitVec.ofNat 32 (8 * (R / 6) + 2)) ?_ fun t ⟨a, c⟩ => WP.mono (upLoop_wp hs hp (by omega_arith) (by omega_arith)
      (fun _ _ => rfl) a c) fun _ h => ⟨_, h⟩)
  refine WP.ite (decide (R = 18)) hz (fun hb => wp_movi_x fun t u hx => WP.block_nil ⟨h.count u hx, ?_⟩)
    fun hb => wp_movi_x fun t u hx => WP.block_nil ⟨h.count u hx, ?_⟩
  · have : R = 18 := of_decide_eq_true hb
    subst this; exact u.gpr
  · have : R = 24 := by have : R ≠ 18 := of_decide_eq_false hb; omega_arith
    subst this; exact u.gpr

theorem prepDec_wp {s₁ : State} {p : BitVec 32} {R : Nat} (hR : R = 18 ∨ R = 24) (hs : Scr s₁ B) (hp : SchIn s₁ B p)
    {F : Nat → BitVec 64} (hF : F = fun k => AesNi.Ew s₁.mem p (Proof.Camellia.decPerm (R / 6) k))
    (h : Pr s₁ B p F 0 0 s) (hz : s.zf = some (decide (R = 18))) :
    WP isa prepDec s fun s' => ∃ a, Pr s₁ B p F a (8 * (R / 6) + 2) s' := by
  obtain ⟨g, hg⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg34 : g = 3 ∨ g = 4 := by omega_arith
  rw [hg] at hF ⊢
  have f1 : ∀ k < 2, F k = AesNi.Ew s₁.mem p (8 * g + k) := fun k hk => by
    rw [hF]; simp only [Proof.Camellia.decPerm, hk, ite_true]
  have f2 : ∀ j < 8 * g - 1 - 1, F (2 + j) = AesNi.Ew s₁.mem p (8 * g - 1 - j) := fun j hj => by
    rw [hF]
    simp only [Proof.Camellia.decPerm, show ¬ 2 + j < 2 by omega_arith, show 2 + j < 8 * g by omega_arith, ite_false, ite_true]
    rw [show 8 * g + 1 - (2 + j) = 8 * g - 1 - j by omega_arith]
  have f3 : ∀ k < 2, F (8 * g + k) = AesNi.Ew s₁.mem p k := fun k hk => by
    rw [hF]
    simp only [Proof.Camellia.decPerm, show ¬ 8 * g + k < 2 by omega_arith, show ¬ 8 * g + k < 8 * g by omega_arith, ite_false]
    rw [Nat.add_sub_cancel_left]
  refine WP.seq (WP.mono (Q := fun (s' : State) => Pr s₁ B p F (8 * g) 0 s' ∧
    s'.gpr .ecx = BitVec.ofNat 32 (8 * g - 1 - 1)) ?_ fun t ⟨a, c⟩ => ?_)
  · refine WP.ite (decide (R = 18)) hz (fun hb => wp_movi_x fun t u hx => AesNi.wp_addi_x fun t' u' hx' => WP.block_nil ⟨?_, ?_⟩)
      fun hb => wp_movi_x fun t u hx => AesNi.wp_addi_x fun t' u' hx' => WP.block_nil ⟨?_, ?_⟩
    · have : R = 18 := of_decide_eq_true hb
      have hg3 : g = 3 := by omega_arith
      refine (h.count u hx).move u' hx' ?_
      rw [(h.count u hx).src, hg3, show (192 : BitVec 32) = BitVec.ofNat 32 192 from rfl, Offset.add_ofNat_add_ofNat]
    · have : R = 18 := of_decide_eq_true hb
      have hg3 : g = 3 := by omega_arith
      rw [u'.other _ (by decide), u.gpr, hg3]; rfl
    · have : R = 24 := by have : R ≠ 18 := of_decide_eq_false hb; omega_arith
      have hg3 : g = 4 := by omega_arith
      refine (h.count u hx).move u' hx' ?_
      rw [(h.count u hx).src, hg3, show (256 : BitVec 32) = BitVec.ofNat 32 256 from rfl, Offset.add_ofNat_add_ofNat]
    · have : R = 24 := by have : R ≠ 18 := of_decide_eq_false hb; omega_arith
      have hg3 : g = 4 := by omega_arith
      rw [u'.other _ (by decide), u.gpr, hg3]; rfl
  refine WP.seq ?_
  rw [List.append_assoc, List.append_assoc]
  refine prepOne_wp hs hp a (by omega_arith) (by decide) (f1 0 (by decide)) fun t₁ a₁ c₁ => ?_
  refine AesNi.wp_addi_x fun t₂ u₂ x₂ => ?_
  have a₂ : Pr s₁ B p F (8 * g + 1) 1 t₂ := a₁.move u₂ x₂ (by
    rw [a₁.src, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_ofNat_add_ofNat,
      show 8 * (8 * g) + 8 = 8 * (8 * g + 1) by omega_arith])
  refine prepOne_wp hs hp a₂ (by omega_arith) (by decide) (f1 1 (by decide)) fun t₃ a₃ c₃ => ?_
  refine AesNi.wp_subi_x fun t₄ u₄ x₄ _ => WP.block_nil ?_
  have a₄ : Pr s₁ B p F (8 * g - 1) 2 t₄ := a₃.move u₄ x₄ (by
    rw [a₃.src, show (16 : BitVec 32) = BitVec.ofNat 32 (8 * 2) from rfl, add_back _ (by omega_arith),
      show 8 * g + 1 - 2 = 8 * g - 1 by omega_arith])
  refine WP.seq (WP.mono (downLoop_wp hs hp (by omega_arith) (by omega_arith) (by omega_arith) f2 a₄
    (by rw [u₄.other _ (by decide), c₃, u₂.other _ (by decide), c₁, c])) fun t₅ a₅ => ?_)
  rw [show 2 + (8 * g - 1) - 1 = 8 * g by omega_arith] at a₅
  rw [List.append_assoc, List.append_assoc]
  refine AesNi.wp_subi_x fun t₆ u₆ x₆ _ => ?_
  have a₆ : Pr s₁ B p F 0 (8 * g) t₆ := a₅.move u₆ x₆ (by
    rw [a₅.src, show (8 : BitVec 32) = BitVec.ofNat 32 (8 * 1) from rfl, add_back _ (by decide)])
  refine prepOne_wp hs hp a₆ (by decide) (by omega_arith) (f3 0 (by decide)) fun t₇ a₇ _ => ?_
  refine AesNi.wp_addi_x fun t₈ u₈ x₈ => ?_
  have a₈ : Pr s₁ B p F 1 (8 * g + 1) t₈ := a₇.move u₈ x₈ (by
    rw [a₇.src, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_ofNat_add_ofNat])
  rw [← List.append_nil prepOne]
  exact prepOne_wp hs hp a₈ (by decide) (by omega_arith) (f3 1 (by decide)) fun t₉ a₉ _ => WP.block_nil ⟨1, a₉⟩

theorem tb_exec (h : s.gpr tbr = s.syms tableName) {d : XReg} {off : Nat} (h8 : off % 8 = 0)
    (hl : off / 8 + 2 ≤ table.length) : exec (tb d off) s = some (s.setXmm d (tblAt table off)) := by
  simp only [tb, Impl.Modes.X86.at_, exec, h, h8, hl, and_self, ite_true]; rfl

/-- The constants, and the table's address in its slot. -/
theorem prepHead_wp {R : Nat} {p : BitVec 32} (hB : s.gpr Impl.Modes.X86.sb = B) (hs : Scr s B) (hR : R = 18 ∨ R = 24)
    (hax : s.gpr .eax = s.syms tableName)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (Impl.Modes.X86.argOp 0)) 4) (hp : s.mem.readW (s.ea (Impl.Modes.X86.argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (Impl.Modes.X86.argOp 0), 4⟩ ⟨B.setWidth 64, 1544⟩)
    (hin1 : InRegions (s.rd ++ s.wr) (s.ea (Impl.Modes.X86.argOp 1)) 4)
    (hv : s.mem.readW (s.ea (Impl.Modes.X86.argOp 1)) 32 = BitVec.ofNat 32 R)
    (h1B : Region.Disjoint ⟨s.ea (Impl.Modes.X86.argOp 1), 4⟩ ⟨B.setWidth 64, 1544⟩) (F : Nat → BitVec 64) :
    WP isa (.block prepHead) s fun s' => Pr s' B p F 0 0 s' ∧ s'.zf = some (decide (R = 18)) ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧ Frame [slotsR B 26 1] s.mem s'.mem ∧
      s'.mem.readW (addr B 416) 32 = s.syms tableName := by
  have hf := hs.fit
  have ha : addr B 416 = B.setWidth 64 + BitVec.ofNat 64 416 := addr_eq (by omega_arith)
  have hw : InRegions s.wr (addr B 416) 4 := ⟨_, hs.wr, by
    rw [ha]; exact Offset.contains_base _ (by decide) (by decide)⟩
  show WP isa (.block (.store ⟨Impl.Modes.X86.sb, 416⟩ .eax :: .mov tbr (.reg .eax) :: .mov .eax (.mem ⟨.esp, 4 + 4 * 0⟩) ::
    .mov .ecx (.mem ⟨.esp, 4 + 4 * 1⟩) :: .mov kr (.reg Impl.Modes.X86.sb) :: .alu .add kr (.imm 960) ::
    tb .xmm7 0 :: tb .xmm6 128 :: [.alu .cmp .ecx (.imm 18)])) s _
  refine Wp.wp_stm hB hw fun s₂ u₂ => ?_
  have f₂ : Frame [slotsR B 26 1] s.mem s₂.mem := by
    rw [u₂.mem, ha]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  have sub : Region.Sub (slotsR B 26 1) ⟨B.setWidth 64, 1544⟩ := Offset.sub_base _ (by decide)
  have e0 : s₂.mem.readW (s.ea (Impl.Modes.X86.argOp 0)) 32 = p := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0B.sub_right sub) (by decide), hp]
  have e1 : s₂.mem.readW (s.ea (Impl.Modes.X86.argOp 1)) 32 = BitVec.ofNat 32 R := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h1B.sub_right sub) (by decide), hv]
  refine Wp.wp_mov fun s₃ u₃ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₃.other _ (by decide), u₂.gpr])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin0) fun s₄ u₄ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin1) fun s₅ u₅ => ?_
  refine Wp.wp_mov fun s₆ u₆ => Wp.wp_addi fun s₇ u₇ => ?_
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have b₇ : s₇.gpr Impl.Modes.X86.sb = B := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, hB]
  have sp₇ : s₇.gpr .esp = s.gpr .esp := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]
  have rd₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  have sy₇ : s₇.syms = s.syms := by rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms]
  have t₇ : s₇.gpr tbr = s₇.syms tableName := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, sy₇, hax]
  have a₇ : s₇.gpr .eax = p + BitVec.ofNat 32 (8 * 0) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem]
    rw [show BitVec.ofNat 32 (8 * 0) = (0 : BitVec 32) from rfl, show p + (0 : BitVec 32) = p from BitVec.add_zero _]
    exact e0
  have c₇ : s₇.gpr .ecx = BitVec.ofNat 32 R := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem]
    exact e1
  have k₇ : s₇.gpr kr = B + BitVec.ofNat 32 (16 * (60 + 0)) := by
    rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hB]; rfl
  have x7 : exec (tb .xmm7 0) s₇ = some (s₇.setXmm .xmm7 lowM) := tb_exec t₇ (by decide) (by decide)
  have x6 : exec (tb .xmm6 128) (s₇.setXmm .xmm7 lowM) = some ((s₇.setXmm .xmm7 lowM).setXmm .xmm6 uW) :=
    tb_exec (s := s₇.setXmm .xmm7 lowM) t₇ (by decide) (by decide)
  refine Wp.cons x7 (Wp.cons x6 (Wp.cons rfl (WP.block_nil ?_)))
  refine ⟨⟨b₇, rfl, t₇, rfl, rfl, rfl, a₇, k₇, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩, ?_, sp₇, rd₇, wr₇, sy₇,
    by show Frame _ s.mem s₇.mem; rw [m₇]; exact f₂, ?_⟩
  · show some (s₇.gpr .ecx - 18 == 0) = _
    rw [c₇, show (18 : BitVec 32) = BitVec.ofNat 32 18 from rfl, Wp.sub_beq (by omega_arith) (by decide)]
  · show s₇.mem.readW _ 32 = _
    rw [m₇, u₂.mem, Mem.readW_writeW_self32, hax]

/-- `prepare d` leaves the schedule's subkeys in `d`'s order, as the code
keeps them, and the table's address, in their slots. -/
theorem prepare_wp {d : Dir} {R : Nat} {p : BitVec 32} (hB : s.gpr Impl.Modes.X86.sb = B) (hs : Scr s B)
    (hR : R = 18 ∨ R = 24) (hesp : 4 ≤ (s.gpr .esp).toNat)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (Impl.Modes.X86.argOp 0)) 4) (hp : s.mem.readW (s.ea (Impl.Modes.X86.argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (Impl.Modes.X86.argOp 0), 4⟩ ⟨B.setWidth 64, 1544⟩)
    (hin1 : InRegions (s.rd ++ s.wr) (s.ea (Impl.Modes.X86.argOp 1)) 4)
    (hv : s.mem.readW (s.ea (Impl.Modes.X86.argOp 1)) 32 = BitVec.ofNat 32 R)
    (h1B : Region.Disjoint ⟨s.ea (Impl.Modes.X86.argOp 1), 4⟩ ⟨B.setWidth 64, 1544⟩)
    (hsch : SchIn s B p)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨p.setWidth 64, 272⟩)
    (h0S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (Impl.Modes.X86.argOp 0), 4⟩)
    (h1S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (Impl.Modes.X86.argOp 1), 4⟩) :
    WP isa (prepare d) s fun s' => Keys s'.mem B (8 * (R / 6) + 2) (AesNiWide.Ed d (R / 6) (AesNi.Ew s.mem p)) ∧
      s'.mem.readW (addr B 416) 32 = s.syms tableName ∧ s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64, 1504⟩, below (s.gpr .esp) 4] s.mem s'.mem := by
  have hf := hs.fit
  refine WP.seq (WP.mono (symFrame_ok tableName s hesp) fun s₁ a₁ => ?_)
  have esp₁ : s₁.gpr .esp = s.gpr .esp := a₁.gpr .esp (by decide)
  have ea₁ : ∀ k, s₁.ea (Impl.Modes.X86.argOp k) = s.ea (Impl.Modes.X86.argOp k) := fun k => by
    show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
    rw [esp₁]
  have hs₁ : Scr s₁ B := ⟨by rw [a₁.wr]; exact hs.wr, hf⟩
  have rdw : ∀ {a : Addr}, Region.Disjoint (below (s.gpr .esp) 4) ⟨a, 4⟩ → s₁.mem.readW a 32 = s.mem.readW a 32 := fun hd =>
    a₁.frame.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hd.symm) (by decide)
  refine WP.seq (WP.mono (prepHead_wp (R := R) (p := p) (F := AesNiWide.Ed d (R / 6) (AesNi.Ew s.mem p))
    ((a₁.gpr _ (by decide)).trans hB) hs₁ hR (by rw [a₁.addr, a₁.syms])
    (by rw [ea₁, a₁.rd, a₁.wr]; exact hin0) (by rw [ea₁, rdw h0S, hp]) (by rw [ea₁]; exact h0B)
    (by rw [ea₁, a₁.rd, a₁.wr]; exact hin1) (by rw [ea₁, rdw h1S, hv]) (by rw [ea₁]; exact h1B))
    fun s₂ ⟨P, z, esp₂, rd₂, wr₂, sy₂, F₂, t₂⟩ => ?_)
  have hs₂ : Scr s₂ B := ⟨by rw [wr₂]; exact hs₁.wr, hf⟩
  have hsch₂ : SchIn s₂ B p := ⟨by rw [rd₂, wr₂, a₁.rd, a₁.wr]; exact hsch.rd, hsch.fit, hsch.dis⟩
  have ew : ∀ j < 34, AesNi.Ew s₂.mem p j = AesNi.Ew s.mem p j := fun j hj => by
    unfold AesNi.Ew
    rw [Proof.Camellia.wordAt_frame F₂ fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (hsch.dis.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by decide)),
      Proof.Camellia.wordAt_frame a₁.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact hkS.symm.sub_left (Offset.sub_base _ (by omega_arith))]
  have fin : ∀ s' : State, (∃ a, Pr s₂ B p (AesNiWide.Ed d (R / 6) (AesNi.Ew s₂.mem p)) a (8 * (R / 6) + 2) s') →
      Keys s'.mem B (8 * (R / 6) + 2) (AesNiWide.Ed d (R / 6) (AesNi.Ew s.mem p)) ∧
      s'.mem.readW (addr B 416) 32 = s.syms tableName ∧ s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64, 1504⟩, below (s.gpr .esp) 4] s.mem s'.mem := fun s' ⟨a, Q⟩ => by
    refine ⟨fun k hk => ?_, ?_, Q.base, Q.esp.trans (esp₂.trans esp₁), Q.rd.trans (rd₂.trans a₁.rd),
      Q.wr.trans (wr₂.trans a₁.wr), Q.syms.trans (sy₂.trans a₁.syms), ?_⟩
    · rw [Q.keys k hk]
      refine congrArg (fun v => spread v ^^^ uW) ?_
      cases d
      · exact ew k (by omega_arith)
      · exact ew _ (AesNiWide.decPerm_lt (by omega_arith) hk)
    · rw [Q.frame.readW (r := ⟨addr B 416, 4⟩) (Region.contains_self _ 4) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        rw [show addr B 416 = B.setWidth 64 + BitVec.ofNat 64 416 from addr_eq (by omega_arith)]
        exact Offset.disjoint (B.setWidth 64) (by decide) (by decide) (by decide)) (by decide), t₂, a₁.syms]
    · refine ((a₁.frame.mono fun r hr => ?_).trans (F₂.sub fun r hr => ?_)).trans (Q.frame.sub fun r hr => ?_)
      · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
  have P' : Pr s₂ B p (AesNiWide.Ed d (R / 6) (AesNi.Ew s₂.mem p)) 0 0 s₂ :=
    { P with keys := fun j hj => absurd hj (Nat.not_lt_zero _) }
  cases d
  · exact WP.mono (prepEnc_wp hR hs₂ hsch₂ P' z) fin
  · exact WP.mono (prepDec_wp hR hs₂ hsch₂ rfl P' z) fin

end

/-! ## The core -/

section

open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)
open VG.Proof.Camellia (schedWords schedWords_getD decPerm)

/-- The key's arguments, as of the cores by the AES S-box, the four bytes
below `esp`, where `crypt` calls the block function, apart from the mode's
regions too. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  AesNi.KeyArgs s rs k ∧ ∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .esp) 4) r

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k :=
  ⟨AesNi.keyArgs_congr h.1 hesp hrd hwr hf, by rw [hesp]; exact h.2⟩

/-- The key `k` is ready, for the direction `d`, in the scratch buffer at `B`. -/
structure Ready (d : Dir) (s : State) (B : BitVec 32) (k : Nat × List (BitVec 64)) : Prop where
  keys : Keys s.mem B (8 * (k.1 / 6) + 2) (AesNiWide.Ed d (k.1 / 6) fun i => k.2.getD i 0)
  tab : s.mem.readW (addr B 416) 32 = s.syms tableName
  rounds : AesNi.RArg s k.1
  valid : k.1 = 18 ∨ k.1 = 24
  fit : B.toNat + 1544 ≤ 2 ^ 32
  stk : Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨B.setWidth 64, 1544⟩
  stkR : Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨s.ea (Impl.Modes.X86.argOp 1), 4⟩

theorem ready_frame {d : Dir} {s s' : State} {B : BitVec 32} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready d s B k) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (core d) B) r ∨ Region.Sub r (blkRegion (core d) B)) :
    Ready d s' B k := by
  have hfit := h.fit
  have hv := h.valid
  have keep : ∀ {a n : Nat}, (a + n ≤ 704 ∨ 960 ≤ a) → a + n ≤ 1504 → ∀ r ∈ rs,
      Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩ r := fun {a n} h₁ h₂ r hr => by
    rcases hd r hr with h | h
    · exact h.sub_left (Offset.sub_base _ (by show a + n ≤ 4 * 376; omega_arith))
    · exact (Offset.disjoint (B.setWidth 64) (d := a) (n := n) (e := 4 * 176) (k := 4 * 4 * 16)
        (by omega_arith) (by omega_arith) (by decide)).sub_right h
  refine ⟨fun j hj => ?_, ?_, h.rounds.frame hesp hrd hwr hf hs, hv, hfit, by rw [hesp]; exact h.stk,
    by rw [hesp, AesNi.ea_esp hesp]; exact h.stkR⟩
  · rw [W_frame hf (by omega_arith) (keep (by omega_arith) (by omega_arith))]
    exact h.keys j hj
  · have ha : addr B 416 = B.setWidth 64 + BitVec.ofNat 64 416 := addr_eq (by omega_arith)
    rw [hsy, ← h.tab, ha]
    exact hf.readW (Region.contains_self _ 4) (keep (by decide) (by decide)) (by decide)

theorem prepare_ok {d : Dir} {s : State} {B : BitVec 32} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (core d).total)
    (hR : (⟨B.setWidth 64, 4 * (core d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (hsp : (core d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (core d).prepare s fun s' => Ready d s' B k ∧ s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (core d) B, stkRegion (s.gpr .esp) (core d).stack] s.mem s'.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨⟨p, hin0, hp, hin1, hRa, hRv, hws, hsch, hfit, hdis, hd0, hd1, hdw, hkS, h0S, h1S⟩, hst⟩ := hk
  simp only at hRa hRv hws ⊢
  refine WP.mono (prepare_wp (d := d) hB ⟨hs.wr, hs.fit⟩ hRv hsp hin0 hp (hd0 _ hR) hin1 hRa (hd1 _ hR) ⟨hsch, hfit, hdis _ hR⟩
    hkS h0S h1S) fun s' ⟨K, t, b, e, rd, wr, sy, f⟩ => ?_
  refine ⟨⟨fun i hi => ?_, by rw [t, sy], ⟨by rw [rd, wr, AesNi.ea_esp e]; exact hin1, ?_,
    by rw [wr, AesNi.ea_esp e]; exact hdw⟩, hRv, hs.fit, by rw [e]; exact hst _ hR, by rw [e, AesNi.ea_esp e]; exact h1S⟩, b, e, f, rd, wr⟩
  · rw [K i hi]
    refine congrArg (fun v => spread v ^^^ uW) ?_
    cases d
    · show AesNi.Ew s.mem p i = ws.getD i 0
      rw [hws, schedWords_getD _ _ (by simp only [Spec.Camellia.scheduleLength]; exact hi)]
      rfl
    · show AesNi.Ew s.mem p (decPerm (R / 6) i) = ws.getD (decPerm (R / 6) i) 0
      rw [hws, schedWords_getD _ _ (by simp only [Spec.Camellia.scheduleLength]; exact AesNiWide.decPerm_lt' hi)]
      rfl
  · rw [AesNi.ea_esp e, f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hRa]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hd1 _ hR).sub_right (Region.sub_prefix (by show 1504 ≤ 4 * 386; decide))
    · exact h1S.symm

theorem crypt_ok {d : Dir} {s : State} {B : BitVec 32} {k : Nat × List (BitVec 64)} (hB : s.gpr Impl.Modes.X86.sb = B)
    (hs : VG.Proof.Modes.X86.ScrIn s B (core d).total) (hr : Ready d s B k) :
    WP isa (core d).crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready d s' B k ∧
      Frame [coreRegion (core d) B, stkRegion (s.gpr .esp) (core d).stack] s.mem s'.mem ∧
      (∀ j < (core d).G, Spec.Aes.bytesAt s'.mem (blkAddr (core d) B j) (4 * (core d).bw) =
        dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (blkAddr (core d) B j) (4 * (core d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  have hfit := hr.fit
  have hv := hr.valid
  have hblk : ∀ j, blkAddr (core d) B j = blk B j := fun j => by
    show B.setWidth 64 + BitVec.ofNat 64 (4 * 176) + BitVec.ofNat 64 (4 * 4 * j) = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun z => B.setWidth 64 + BitVec.ofNat 64 z) (by show 4 * 176 + 4 * 4 * j = 16 * (44 + j); omega_arith)
  refine WP.mono (crypt_wp hB ⟨hs.wr, hs.fit⟩ hv hr.keys hr.rounds.1 hr.rounds.2.1 hr.tab hr.stk)
    fun s' ⟨b, e, rd, wr, sy, f, tb, v⟩ => ?_
  refine ⟨b, e, ⟨fun j hj => ?_, ?_, ⟨by rw [rd, wr, AesNi.ea_esp e]; exact hr.rounds.1, ?_, by rw [wr, AesNi.ea_esp e]; exact hr.rounds.2.2⟩,
    hv, hfit, by rw [e]; exact hr.stk, by rw [e, AesNi.ea_esp e]; exact hr.stkR⟩, f.sub fun r hr => ?_, fun j hj => ?_, rd, wr⟩
  · have hj' : j < 34 := by simp only at hj; omega_arith
    rw [W_frame f (by omega_arith) fun r hr' => ?_]
    · exact hr.keys j hj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact Offset.disjoint (B.setWidth 64) (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact (hr.stk.sub_right (Offset.sub_base _ (by omega_arith))).symm
  · have e1 : ∀ m : Mem, m.readW (addr B 416) 32 = (W m B tblSlot).extractLsb' 0 32 := fun m => by
      have := dword_readW m (addr B 416) (j := 0) (by decide)
      rw [Nat.mul_zero, BitVec.add_zero] at this
      exact this.symm
    rw [e1, tb, ← e1, sy]; exact hr.tab
  · rw [AesNi.ea_esp e, f.readW (Region.contains_self _ _) (fun r hr' => ?_) (by decide)]
    · exact hr.rounds.2.1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hr.rounds.2.2 _ hs.wr).sub_right (Offset.sub_base _ (by show 16 * 0 + 16 * 60 ≤ 4 * 386; decide))
      · exact hr.stkR.symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by show 16 * 0 + 16 * 60 ≤ 4 * 376; decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · show Spec.Aes.bytesAt s'.mem (blkAddr (core d) B j) 16 =
      dirCipher d _ (Spec.Aes.bytesAt s.mem (blkAddr (core d) B j) 16)
    rw [hblk, AesNiWide.dir_bytes hv]
    exact v j hj

/-- Camellia's core of sixteen blocks meets what the modes need, in the
direction `d`. -/
def coreSpec (d : Dir) : CoreSpec (core d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher, core]
  layout := ⟨by show 0 < 16; decide, .inr rfl, by show 176 + 4 * 16 ≤ 376; decide, by show 376 + 10 ≤ 386; decide⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h e r w sy f hs hd := ready_frame h e r w sy f hs hd
  prepare_wp hB hs hR hk hsp := prepare_ok hB hs hR hk hsp
  crypt_wp hB hs hr _ := crypt_ok hB hs hr

end

end VG.Proof.Camellia.X86.Sse
