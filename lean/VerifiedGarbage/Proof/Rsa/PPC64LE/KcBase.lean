module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyCheck
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.KeyArrays
import VerifiedGarbage.Proof.Framework.Block

/-! # The checks of an RSA key on PPC64LE: the state between the steps

As on ARMv7 (`Proof/Rsa/Arm/KcBase.lean`). `Geo`: the working space (`B`,
`Z` bytes) and the modulus' length `K`, which two runs share; `Vals`: the
numbers read, which they may not. `Stg g s₀ A live c s`: from the state `s₀`
the checks start from, the steps so far wrote only the arrays and the header
words they may and the registers `bodyRegs`, the arrays `live` hold `A`,
and the mask is `c`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)

structure Geo where
  B : Addr
  Z : Nat
  K : Nat

/-- `w = ⌈K / 4⌉`. -/
abbrev Geo.w (g : Geo) : Nat := (g.K + 3) / 4

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
abbrev bodyRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The arrays through a step that writes none of them. -/
theorem arrsKeep {m m' : Mem} {B : Addr} {w : Nat} {A : Nat → Nat} {live : List Nat} {js ds : List Nat}
    (h : Arrs m B w A live) (k : KeyWorkspace.Keep B w js ds m m')
    (hj : ∀ j ∈ live, j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr)
    (fit : ∀ j ∈ live, arr w j + S w ≤ 2 ^ 64) : Arrs m' B w A live := fun j hj' => by
  rw [k.num (fun i hi e => hj j hj' (by subst e; exact hi)) hd (fit j hj'), h j hj']

/-- Between the steps. -/
structure Stg (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat) (c : Bool) (s : State) : Prop where
  ws : Ws s g.B g.Z g.w nArr
  keep : KeyWorkspace.Keep g.B g.w (List.range nArr) bodySlots s0.mem s.mem
  regs : Keep bodyRegs s0 s
  arrs : Arrs s.mem g.B g.w A live
  live_lt : ∀ j ∈ live, j < nArr
  vdTop : w32 s.mem g.B (arr g.w aVD + 4 * g.w) = 0
  mask : slot s.mem g.B sMask = if c then 1 else 0

/-- A step from `Stg`. -/
theorem Stg.next {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {rs : List Reg} (hw : Ws t g.B g.Z g.w nArr)
    (k : KeyWorkspace.Keep g.B g.w js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, d ∈ bodySlots) (r : Keep rs s t) (hrs : ∀ x ∈ rs, x ∈ bodyRegs) {A' : Nat → Nat}
    {live' : List Nat} {c' : Bool} (ha : Arrs t.mem g.B g.w A' live') (hl : ∀ j ∈ live', j < nArr)
    (vd : w32 t.mem g.B (arr g.w aVD + 4 * g.w) = 0)
    (mk : slot t.mem g.B sMask = if c' then 1 else 0) : Stg g s0 A' live' c' t :=
  ⟨hw, h.keep.trans (k.mono (fun j hj => List.mem_range.2 (hjs j hj)) hds),
    (h.regs.trans r).mono fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hx
      · exact hrs x hx, ha, hl, vd, mk⟩

/-- The mask through a step that leaves its slot. -/
theorem Stg.mask_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : KeyWorkspace.Keep g.B g.w js ds s.mem m')
    (hd : ∀ d ∈ ds, sMask + 4 ≤ d ∨ d + 4 ≤ sMask) : slot m' g.B sMask = if c then 1 else 0 := by
  rw [k.slot (by decide) hd, h.mask]

/-- The top digit of `aVD` through a step that leaves `aVD`. -/
theorem Stg.vd_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : KeyWorkspace.Keep g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ js, j ≠ aVD) (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) :
    w32 m' g.B (arr g.w aVD + 4 * g.w) = 0 := by
  rw [k.word (by simp only [S]; omega) hj hd (h.ws.fit64 (by decide)), h.vdTop]

/-- The arrays through a step that writes none of them. -/
theorem Stg.arrs_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : KeyWorkspace.Keep g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ live, j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) : Arrs m' g.B g.w A live :=
  arrsKeep h.arrs k hj hd fun j hj' => h.ws.fit64 (h.live_lt j hj')

/-- The arrays through a step that writes `o := v`. -/
theorem Stg.arrs_write {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : KeyWorkspace.Keep g.B g.w js ds s.mem m')
    {o v : Nat} (e : num m' g.B g.w o = v) (hj : ∀ j ∈ live, j = o ∨ j ∉ js)
    (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) : Arrs m' g.B g.w (upd A o v) live := by
  intro j hj'
  by_cases e' : j = o
  · subst e'; rw [upd_self]; exact e
  · rw [upd_ne _ _ e', k.num (fun i hi ei => ((hj j hj').resolve_left e') (by subst ei; exact hi)) hd
      (h.ws.fit64 (h.live_lt j hj')), h.arrs j hj']

/-- The mask and'ed with a check. -/
theorem acc_bits {x y : Nat} {c d : Bool} (hx : x = if c then 1 else 0) (hy : y = if d then 1 else 0) :
    (if x = 1 ∧ y = 1 then 1 else 0) = if (c && d) then 1 else 0 := by
  subst hx hy; cases c <;> cases d <;> rfl

theorem bit_le {c : Bool} {x : Nat} (h : x = if c then 1 else 0) : x ≤ 1 := by
  subst h; cases c <;> decide

end VG.Proof.Rsa.PPC64LE.KeyCheck
