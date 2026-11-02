module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyCheck
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLayout
public import VerifiedGarbage.Proof.Rsa.KeyArrays
import VerifiedGarbage.Proof.Framework.Omega

/-! # The checks of an RSA key on RISC-V: the state between the steps

As on PPC64LE (`Proof/Rsa/PPC64LE/KcBase.lean`), in words of 64 bits.
`Arrs m B w A live`: the arrays `live` hold `A`. `Geo`: the working space
(`B`, `Z` bytes) and the modulus' length `K`, which two runs share; `Vals`:
the numbers read, which they may not. `Stg g s₀ A live c s`: from the state
`s₀` the checks start from, the steps so far wrote only the arrays and the
header words they may and the registers `bodyRegs`, the arrays `live` hold
`A`, the division's divisor has its extra word 0, and the mask is `c`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (sOdd sB sC)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (upd upd_ne upd_self)

/-! ## The arrays' values -/

/-- The arrays `live` hold `A`. -/
def Arrs (m : Mem) (B : Addr) (w : Nat) (A : Nat → Nat) (live : List Nat) : Prop :=
  ∀ j ∈ live, num m B w j = A j

theorem Arrs.get {m : Mem} {B : Addr} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {j : Nat} (hj : j ∈ live) : num m B w j = A j := h j hj

theorem Arrs.cons {m : Mem} {B : Addr} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {o : Nat} (e : num m B w o = A o) : Arrs m B w A (o :: live) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj'
  · exact e
  · exact h j hj'

theorem Arrs.sub {m : Mem} {B : Addr} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {live' : List Nat} (hs : ∀ j ∈ live', j ∈ live) : Arrs m B w A live' :=
  fun j hj => h j (hs j hj)

/-! ## The state between the steps -/

structure Geo where
  B : Addr
  Z : Nat
  K : Nat

/-- `w = ⌈K / 8⌉`. -/
abbrev Geo.w (g : Geo) : Nat := (g.K + 7) / 8

structure Vals where
  n : Nat
  e : Nat
  p : Nat
  q : Nat
  dP : Nat
  dQ : Nat
  qI : Nat
  d : Nat

/-- The arrays after the numbers are read. -/
def vals (v : Vals) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (upd (upd (fun _ => 0) aE v.e) aN v.n) aD v.d) aP v.p) aQ v.q) aDP v.dP)
    aDQ v.dQ) aQI v.qI

/-- The header words the checks write. -/
abbrev bodySlots : List Nat := [sOdd, sB, sC, sF, sMask]

/-- The registers the checks may change. -/
abbrev bodyRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a5, .s7]

theorem bodySlots_hdr : ∀ d ∈ bodySlots, d + 8 ≤ hdr := by decide

/-- Between the steps. -/
structure Stg (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat) (c : Bool) (s : State) : Prop where
  ws : Ws s g.B g.Z g.w nArr
  frame : Keys.Frame g.B g.w (List.range nArr) bodySlots s0.mem s.mem
  regs : Keep bodyRegs s0 s
  arrs : Arrs s.mem g.B g.w A live
  live_lt : ∀ j ∈ live, j < nArr
  vdTop : word s.mem g.B (arr g.w aVD + 8 * g.w) = 0
  mask : slot s.mem g.B sMask = if c then 1 else 0

/-- A step from `Stg`. -/
theorem Stg.next {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {rs : List Reg} (hw : Ws t g.B g.Z g.w nArr)
    (k : Keys.Frame g.B g.w js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, d ∈ bodySlots) (r : Keep rs s t) (hrs : ∀ x ∈ rs, x ∈ bodyRegs) {A' : Nat → Nat}
    {live' : List Nat} {c' : Bool} (ha : Arrs t.mem g.B g.w A' live') (hl : ∀ j ∈ live', j < nArr)
    (vd : word t.mem g.B (arr g.w aVD + 8 * g.w) = 0)
    (mk : slot t.mem g.B sMask = if c' then 1 else 0) : Stg g s0 A' live' c' t :=
  ⟨hw, h.frame.trans (k.mono (fun j hj => List.mem_range.2 (hjs j hj)) hds),
    (h.regs.trans r).mono fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hx
      · exact hrs x hx, ha, hl, vd, mk⟩

/-- The mask through a step that leaves its slot. -/
theorem Stg.mask_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keys.Frame g.B g.w js ds s.mem m')
    (hd : ∀ d ∈ ds, sMask + 8 ≤ d ∨ d + 8 ≤ sMask) : slot m' g.B sMask = if c then 1 else 0 := by
  rw [k.slot (by decide) hd, h.mask]

/-- The divisor's extra word through a step that leaves `aVD`. -/
theorem Stg.vd_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keys.Frame g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ js, j ≠ aVD) (hd : ∀ d ∈ ds, d + 8 ≤ hdr) :
    word m' g.B (arr g.w aVD + 8 * g.w) = 0 := by
  rw [k.word (by omega) hj hd (h.ws.fit64 (by decide)), h.vdTop]

/-- The arrays through a step that writes none of them. -/
theorem Stg.arrs_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keys.Frame g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ live, j ∉ js) (hd : ∀ d ∈ ds, d + 8 ≤ hdr) : Arrs m' g.B g.w A live := fun j hj' => by
  rw [k.num (fun i hi e => hj j hj' (by subst e; exact hi)) hd (h.ws.fit64 (h.live_lt j hj')),
    h.arrs j hj']

/-- The arrays through a step that writes `o := v`. -/
theorem Stg.arrs_write {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keys.Frame g.B g.w js ds s.mem m')
    {o v : Nat} (e : num m' g.B g.w o = v) (hj : ∀ j ∈ live, j = o ∨ j ∉ js)
    (hd : ∀ d ∈ ds, d + 8 ≤ hdr) : Arrs m' g.B g.w (upd A o v) live := by
  intro j hj'
  by_cases e' : j = o
  · subst e'; rw [upd_self]; exact e
  · rw [upd_ne _ _ e', k.num (fun i hi ei => ((hj j hj').resolve_left e') (by subst ei; exact hi)) hd
      (h.ws.fit64 (h.live_lt j hj')), h.arrs j hj']

theorem Stg.sub {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {live' : List Nat} (hs : ∀ j ∈ live', j ∈ live) : Stg g s0 A live' c s :=
  { h with arrs := h.arrs.sub hs, live_lt := fun j hj => h.live_lt j (hs j hj) }

theorem Stg.congr' {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {A' : Nat → Nat} (e : ∀ j ∈ live, A j = A' j) : Stg g s0 A' live c s :=
  { h with arrs := fun j hj => (h.arrs j hj).trans (e j hj) }

/-- The mask and'ed with a check. -/
theorem acc_bits {x y : Nat} {c d : Bool} (hx : x = if c then 1 else 0) (hy : y = if d then 1 else 0) :
    x * y = if (c && d) then 1 else 0 := by
  subst hx hy; cases c <;> cases d <;> rfl

theorem bit_le {c : Bool} {x : Nat} (h : x = if c then 1 else 0) : x ≤ 1 := by
  subst h; cases c <;> decide

end VG.Proof.Rsa.RISCV64.KeyCheck
