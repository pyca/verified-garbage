module

public import VerifiedGarbage.Proof.Rsa.X86.KeyArrs
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheck
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.TCB.X86.State

/-! # The checks of an RSA key on i686: the state between the steps

`Geo`: the working space (`B`, `Z` bytes) and native word width `w`, which
two runs share; `Vals`: the numbers read, which they may not. `Stg g s₀ A
live c s`: from the state `s₀` the checks start from, the steps so far wrote
only the arrays and the header words they may, the arrays `live` hold `A`,
and the mask is `c`. The workspace base stays in EDI throughout.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

structure Geo where
  B : Addr
  Z : Nat
  w : Nat

structure Vals where
  n : Nat
  e : Nat
  p : Nat
  q : Nat
  dP : Nat
  dQ : Nat
  qI : Nat
  d : Nat

/-- The arrays after the numbers are read (in the order the entry reads them). -/
def vals (v : Vals) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (upd (upd (fun _ => 0) aE v.e) aD v.d) aP v.p) aQ v.q) aDP v.dP) aDQ v.dQ)
    aQI v.qI) aN v.n

/-- The header words the checks write. -/
abbrev bodySlots : List Nat := [sB, sC, sT, sF, sMask]

/-- The workspace base and stack pointer are preserved. -/
abbrev bodyRegs : List Reg := [.eax, .ecx, .edx, .ebp, .ebx, .esi]

/-- Between the steps. -/
structure Stg (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat) (c : Bool) (s : State) : Prop where
  ws : Ws s g.B g.Z g.w nArr
  keep : Keep g.B g.w (List.range nArr) bodySlots s0.mem s.mem
  rest : Keeps bodyRegs s0 s
  arrs : Arrs s.mem g.B g.w A live
  live_lt : ∀ j ∈ live, j < nArr
  vdTop : w32 s.mem g.B (arr g.w aVD + 4 * g.w) = 0
  mask : slot s.mem g.B sMask = if c then 1 else 0

/-- A step from `Stg`. -/
theorem Stg.next {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {rs : List Reg} (hw : Ws t g.B g.Z g.w nArr)
    (k : Keep g.B g.w js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr) (hds : ∀ d ∈ ds, d ∈ bodySlots)
    (r : Keeps rs s t) (hrs : ∀ x ∈ rs, x ∈ bodyRegs) {A' : Nat → Nat} {live' : List Nat} {c' : Bool}
    (ha : Arrs t.mem g.B g.w A' live') (hl : ∀ j ∈ live', j < nArr)
    (vd : w32 t.mem g.B (arr g.w aVD + 4 * g.w) = 0)
    (mk : slot t.mem g.B sMask = if c' then 1 else 0) : Stg g s0 A' live' c' t := by
  exact ⟨hw, h.keep.trans (k.mono (fun j hj => List.mem_range.2 (hjs j hj)) hds),
    h.rest.trans (r.mono hrs), ha, hl, vd, mk⟩

/-- The mask through a step that leaves its slot. -/
theorem Stg.mask_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keep g.B g.w js ds s.mem m')
    (hd : ∀ d ∈ ds, sMask + 4 ≤ d ∨ d + 4 ≤ sMask) : slot m' g.B sMask = if c then 1 else 0 := by
  rw [k.slot (by decide) hd, h.mask]

/-- The top word of `aVD` through a step that leaves `aVD`. -/
theorem Stg.vd_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keep g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ js, j ≠ aVD) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) :
    w32 m' g.B (arr g.w aVD + 4 * g.w) = 0 := by
  rw [k.word (by simp only [S]; omega) hj hd (h.ws.fit64 (by decide)), h.vdTop]

/-- The arrays through a step that writes none of them. -/
theorem Stg.arrs_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keep g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ live, j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) : Arrs m' g.B g.w A live :=
  h.arrs.keep k h.ws (fun j hj' => ⟨h.live_lt j hj', hj j hj'⟩) hd

/-- The arrays through a step that writes `o := v`. -/
theorem Stg.arrs_write {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keep g.B g.w js ds s.mem m') {o v : Nat}
    (e : num m' g.B g.w o = v) (hj : ∀ j ∈ live, j = o ∨ j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) :
    Arrs m' g.B g.w (upd A o v) live :=
  h.arrs.write k h.ws e (fun j hj' => (hj j hj').imp_right fun n => ⟨h.live_lt j hj', n⟩) hd

/-- The mask and'ed with a check. -/
theorem acc_bits {x y : Nat} {c d : Bool} (hx : x = if c then 1 else 0) (hy : y = if d then 1 else 0) :
    (if x = 1 ∧ y = 1 then 1 else 0) = if (c && d) then 1 else 0 := by
  subst hx hy; cases c <;> cases d <;> rfl

theorem bit_le {c : Bool} {x : Nat} (h : x = if c then 1 else 0) : x ≤ 1 := by
  subst h; cases c <;> decide

end VG.Proof.Rsa.X86.KeyCheck
