module

public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Guard
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Eq
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.MulMod
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Rsa.X86.KeyArrs
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheck
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.TCB.X86.State

/-! ### `Rsa.X86.KcWord`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86.KcOps`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86.KcBase`, which this module and modules that import it used -/

section

/-! # The checks of an RSA key on i686: the state between the steps

`Geo`: the working space (`B`, `Z` bytes), the modulus's length `len`, of
the width `w = kw len`, and which key is checked, which two runs share; `Vals`: the numbers read, which they may not. `Stg g s₀ A
live c s`: from the state `s₀` the checks start from, the steps so far wrote
only the arrays and the header words they may, the arrays `live` hold `A`,
and the mask is `c`, with the length and the working space's arguments
(`RtWs`) as they were.
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
  len : Nat
  full : Bool

/-- The width in words. -/
abbrev Geo.w (g : Geo) : Nat := VG.Proof.Rsa.X86.KeyRt.kw g.len

/-- Where the operations find the length and the working space. -/
abbrev Geo.L (g : Geo) : VG.Impl.Rsa.X86.KeyRt.Lay := VG.Impl.Rsa.X86.KeyCheckRt.lay g.full

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
abbrev bodySlots : List Nat := [sB, sC, sT, sF, sMask, VG.Impl.Rsa.X86.KeyRt.sCy, VG.Impl.Rsa.X86.KeyRt.sQb,
  VG.Impl.Rsa.X86.WordModRt.oD, VG.Impl.Rsa.X86.WordModRt.oV, VG.Impl.Bignum.X86.R2Words.oMask VG.Impl.Rsa.X86.WordModRt.h0,
  VG.Impl.Rsa.X86.WordModRt.oSteps, VG.Impl.Rsa.X86.WordModRt.oQ, VG.Impl.Rsa.X86.WordModRt.oU0,
  VG.Impl.Rsa.X86.WordModRt.oU2, VG.Impl.Rsa.X86.WordModRt.oD1, VG.Impl.Rsa.X86.WordModRt.oDig,
  VG.Impl.Rsa.X86.WordModRt.oJ, VG.Impl.Rsa.X86.KeyCheckRt.sG]

/-- The workspace base and stack pointer are preserved. -/
abbrev bodyRegs : List Reg := [.eax, .ecx, .edx, .ebp, .ebx, .esi]

/-- Between the steps. -/
structure Stg (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat) (c : Bool) (s : State) : Prop where
  ws : VG.Proof.Rsa.X86.KeyRt.RtWs g.L s g.B g.Z g.len nArr
  keep : Keep g.B g.w (List.range nArr) bodySlots s0.mem s.mem
  rest : Keeps bodyRegs s0 s
  arrs : Arrs s.mem g.B g.w A live
  live_lt : ∀ j ∈ live, j < nArr
  vdTop : w32 s.mem g.B (arr g.w aVD + 4 * g.w) = 0
  mask : slot s.mem g.B sMask = if c then 1 else 0

/-- A step from `Stg`. -/
theorem Stg.next {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {rs : List Reg}
    (hw : VG.Proof.Rsa.X86.KeyRt.RtWs g.L t g.B g.Z g.len nArr)
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
  rw [k.word (by simp only [S]; omega_using []) hj hd (h.ws.ws.fit64 (by decide)), h.vdTop]

/-- The arrays through a step that writes none of them. -/
theorem Stg.arrs_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keep g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ live, j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) : Arrs m' g.B g.w A live :=
  h.arrs.keep k h.ws.ws (fun j hj' => ⟨h.live_lt j hj', hj j hj'⟩) hd

/-- The arrays through a step that writes `o := v`. -/
theorem Stg.arrs_write {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keep g.B g.w js ds s.mem m') {o v : Nat}
    (e : num m' g.B g.w o = v) (hj : ∀ j ∈ live, j = o ∨ j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) :
    Arrs m' g.B g.w (upd A o v) live :=
  h.arrs.write k h.ws.ws e (fun j hj' => (hj j hj').imp_right fun n => ⟨h.live_lt j hj', n⟩) hd

/-- The mask and'ed with a check. -/
theorem acc_bits {x y : Nat} {c d : Bool} (hx : x = if c then 1 else 0) (hy : y = if d then 1 else 0) :
    (if x = 1 ∧ y = 1 then 1 else 0) = if (c && d) then 1 else 0 := by
  subst hx hy; cases c <;> cases d <;> rfl

theorem bit_le {c : Bool} {x : Nat} (h : x = if c then 1 else 0) : x ≤ 1 := by
  subst h; cases c <;> decide

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! # The checks of an RSA key on i686: the steps on `Stg`

`copy`, `clrLow`, the comparisons `ltA` and `eqA` (and'ed into the mask)
each from `Stg` to `Stg`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (borrow_iff)
open VG.Proof.Rsa.X86.KeyRt (RtWs MulIdx mulArrs)

theorem opRegs_body : ∀ x ∈ [.eax, .ecx, .edx, .ebp, .ebx], x ∈ bodyRegs := by decide
theorem subRegs_body : ∀ x ∈ [.eax, .ebx, .ecx, .edx, .ebp], x ∈ bodyRegs := by decide
theorem allRegs_body : ∀ x ∈ [.eax, .ecx, .edx, .ebp, .ebx, .esi], x ∈ bodyRegs := by decide

theorem Stg.sub {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {live' : List Nat} (hs : ∀ j ∈ live', j ∈ live) : Stg g s0 A live' c s :=
  { h with arrs := h.arrs.sub hs, live_lt := fun j hj => h.live_lt j (hs j hj) }

theorem Stg.congr {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {A' : Nat → Nat} (e : live.map A = live.map A') : Stg g s0 A' live c s :=
  { h with arrs := h.arrs.congr e }

theorem Stg.congr' {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {A' : Nat → Nat} (e : ∀ j ∈ live, A j = A' j) : Stg g s0 A' live c s :=
  { h with arrs := fun j hj => (h.arrs j hj).trans (e j hj) }

/-- A step from `Stg` that writes no memory and only the registers `rs`. -/
theorem Stg.regs {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {rs : List Reg} (K : Keeps rs s t) (mem : t.mem = s.mem)
    (hrs : ∀ x ∈ rs, x ∈ bodyRegs) : Stg g s0 A live c t := by
  have k : Keep g.B g.w [] [] s.mem t.mem := by rw [mem]; exact Keep.refl _ _ _ _ _
  exact h.next (h.ws.keep K (by intro e; have := hrs _ e; simp [bodyRegs] at this)
      (by intro e; have := hrs _ e; simp [bodyRegs] at this) (by rw [mem]; exact fun _ _ => rfl))
    k (by simp) (by simp) K hrs (h.arrs_keep k (by simp) (by simp)) h.live_lt
    (h.vd_keep k (by simp) (by simp)) (h.mask_keep k (by simp))

/-- `copy o a`, `o` then tracked. -/
theorem Stg.copy_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a : Nat} (ho : o < nArr) (ha : a ∈ live) (hoa : o ≠ a) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.copy g.L o a) s (Stg g s0 (upd A o (A a)) (o :: live) c) := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.copy_ok h.ws ho (h.live_lt a ha) hoa) fun t ⟨ht, k, e, r, top⟩ => ?_
  refine h.next ht k (by simpa using ho) (by simp) r (by decide) ?_ ?_ ?_ (h.mask_keep k (by simp))
  · have e' : num t.mem g.B g.w o = A a := e.trans (h.arrs.get ha)
    exact (h.arrs_write k e' (fun j _ => (Decidable.em (j = o)).imp_right fun n => by simpa using n)
      (by simp)).cons (by rw [upd_self]; exact e')
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact ho
    · exact h.live_lt j hj'
  · by_cases hv : o = aVD
    · subst hv; rw [top, h.vdTop]
    · exact h.vd_keep k (by simpa using hv) (by simp)

/-- `clrLow j`. -/
theorem Stg.clrLow_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {j : Nat} (hj : j ∈ live) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyRt.clrLow g.L j)) s (Stg g s0 (upd A j (2 * (A j / 2))) live c) := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.clrLow_ok h.ws (h.live_lt j hj)) fun t ⟨ht, k, e, r, top⟩ => ?_
  refine h.next ht k (by simpa using h.live_lt j hj) (by simp) r (by decide)
    (h.arrs_write k (by rw [e, h.arrs.get hj]) (fun i _ => (Decidable.em (i = j)).imp_right fun n => by
      simpa using n) (by simp)) h.live_lt ?_ (h.mask_keep k (by simp))
  by_cases hv : j = aVD
  · subst hv; rw [top, h.vdTop]
  · exact h.vd_keep k (by simpa using hv) (by simp)

/-- The check in `sF` and'ed into the mask. -/
theorem Stg.acc_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c d : Bool}
    (h : Stg g s0 A live c s) (hf : slot s.mem g.B sF = if d then 1 else 0) :
    WP isa (.block acc) s (Stg g s0 A live (c && d)) := by
  unfold acc
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.andS_ok h.ws (by decide) (by decide) (by decide) (bit_le h.mask) (bit_le hf))
    fun t ⟨ht, k, e, r⟩ => ?_
  refine h.next ht k (by simp) (by decide) r (by decide) (h.arrs_keep k (by simp) (by decide)) h.live_lt
    (h.vd_keep k (by simp) (by decide)) ?_
  rw [e, acc_bits h.mask hf]

/-- `ltA a b`: the mask and'ed with `[a] < [b]`. -/
theorem Stg.ltA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) (hW : aW ∉ live) :
    WP isa (seqs (ltA g.full a b)) s (Stg g s0 A live (c && decide (A a < A b))) := by
  have na := h.live_lt a ha
  have nb := h.live_lt b hb
  have hWa : aW ≠ a := fun e => hW (e ▸ ha)
  have hWb : aW ≠ b := fun e => hW (e ▸ hb)
  rw [ltA, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok h.ws (o := aW) (a := a) (b := b) (by decide) na nb)
    fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  have g1 : Stg g s0 A live c t1 :=
    h.next h1 k1 (by decide) (by simp) r1 subRegs_body
      (h.arrs_keep k1 (fun j hj e => hW (by simp at e; exact e ▸ hj)) (by simp)) h.live_lt
      (h.vd_keep k1 (by decide) (by simp)) (h.mask_keep k1 (by simp))
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok h1 (d := sF) (by decide) .ebx) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have g2 : Stg g s0 A live c t2 :=
    g1.next h2 k2 (by simp) (by decide) r2 (by simp) (g1.arrs_keep k2 (by simp) (by decide))
      g1.live_lt (g1.vd_keep k2 (by simp) (by decide)) (g1.mask_keep k2 (by decide))
  refine g2.acc_ok ?_
  rw [e2]
  have hb' := borrow_iff (P := 2 ^ (32 * g.w)) v1 (val32_lt _ _ _ _) b1
  rw [h.arrs.get ha, h.arrs.get hb] at hb'
  by_cases hlt : A a < A b
  · have : (t1.gpr .ebx).toNat = 1 := by have := hb'.not.mpr (by omega_using [hlt]); omega_using [b1, this]
    simp [hlt, this]
  · have : (t1.gpr .ebx).toNat = 0 := hb'.mpr (by omega_using [hlt])
    simp [hlt, this]

/-- `eqA a b`: the mask and'ed with `[a] = [b]`. -/
theorem Stg.eqA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) (hW : aW ∉ live) :
    WP isa (seqs (eqA g.full a b)) s (Stg g s0 A live (c && decide (A a = A b))) := by
  have na := h.live_lt a ha
  have nb := h.live_lt b hb
  have hWa : aW ≠ a := fun e => hW (e ▸ ha)
  have hWb : aW ≠ b := fun e => hW (e ▸ hb)
  rw [eqA, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.eqS_ok h.ws (d := sF) (a := a) (b := b) (t := aW) (by decide) na nb hWa hWb
    (by decide)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  have g1 : Stg g s0 A live c t1 :=
    h.next h1 k1 (by decide) (by decide) r1 opRegs_body
      (h.arrs_keep k1 (fun j hj e => hW (by simp at e; exact e ▸ hj)) (by decide)) h.live_lt
      (h.vd_keep k1 (by decide) (by decide)) (h.mask_keep k1 (by decide))
  refine g1.acc_ok ?_
  rw [e1, h.arrs.get ha, h.arrs.get hb]
  by_cases he : A a = A b <;> simp [he]

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! # The checks of an RSA key on i686: the word steps on `Stg`

The products (`mulWide`, `mulShort`), the product compared with `n`
(`eqWide`), the guard (`balanced`), the branch on it (`ifBalanced`), and
the remainder by word steps (`wordMod`), each from `Stg` to `Stg`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.WordRt (MLen wq mw Bal Top val32_low top_iff sub0_beq)

theorem wordRegs_body : ∀ x ∈ [.eax, .ebx, .ecx, .edx, .esi, .ebp], x ∈ bodyRegs := by decide

/-- An argument from where the checks started. -/
theorem Stg.arg {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {i : Nat} {x : BitVec 32}
    (a : VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z i x) : VG.Proof.Bignum.X86.CallArgument s g.B g.Z i x :=
  a.keep h.rest (by decide)
    (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws.ws h.keep (fun j hj => List.mem_range.mp hj) (by decide))

/-- `mulWide o a b`: `[a] [b]`, `2 w` words from array `o` on. -/
theorem Stg.mulWide_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a b : Nat} (ho : o + 1 < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (hol : ∀ j ∈ live, j ≠ o ∧ j ≠ o + 1) (hv : o ≠ aVD ∧ o + 1 ≠ aVD) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulWide g.L o a b) s fun t => Stg g s0 A live c t ∧
      val32 t.mem g.B (arr g.w o) (2 * g.w) = A a * A b := by
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.mulWide_ok h.ws ho (h.live_lt a ha) (h.live_lt b hb)
    (hol a ha).1 (hol a ha).2 (hol b hb).1 (hol b hb).2) fun t ⟨ht, k, e, r⟩ => ⟨?_, ?_⟩
  · refine h.next ht k (by simp; omega_using [ho]) (by decide) r wordRegs_body
      (h.arrs_keep k (fun j hj => by simp [(hol j hj).1, (hol j hj).2]) (by decide)) h.live_lt
      (h.vd_keep k (by simp [hv.1, hv.2]) (by decide)) (h.mask_keep k (by decide))
  · rw [e, h.arrs.get ha, h.arrs.get hb]

/-- `mulHalf o a b`: `[a] [b]` where both are below `2^(32 (w / 2))`, `2 w` words from array `o` on. -/
theorem Stg.mulHalf_if_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a b : Nat} (ho : o + 1 < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (hol : ∀ j ∈ live, j ≠ o ∧ j ≠ o + 1) (hv : o ≠ aVD ∧ o + 1 ≠ aVD) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulHalf g.L o a b) s fun t => Stg g s0 A live c t ∧
      (A a < 2 ^ (32 * (g.w / 2)) → A b < 2 ^ (32 * (g.w / 2)) →
        val32 t.mem g.B (arr g.w o) (2 * g.w) = A a * A b) := by
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.mulHalf_ok h.ws ho (h.live_lt a ha) (h.live_lt b hb)
    (hol a ha).1 (hol a ha).2 (hol b hb).1 (hol b hb).2) fun t ⟨ht, k, e, r⟩ => ⟨?_, fun hA hB => ?_⟩
  · refine h.next ht k (by simp; omega_using [ho]) (by decide) r wordRegs_body
      (h.arrs_keep k (fun j hj => by simp [(hol j hj).1, (hol j hj).2]) (by decide)) h.live_lt
      (h.vd_keep k (by simp [hv.1, hv.2]) (by decide)) (h.mask_keep k (by decide))
  · have ea : val32 s.mem g.B (arr g.w a) g.w = A a := h.arrs.get ha
    have eb : val32 s.mem g.B (arr g.w b) g.w = A b := h.arrs.get hb
    rw [e, VG.Proof.Rsa.X86.WordRt.val32_low_of_lt (n := g.w) (Nat.div_le_self _ _) (by rw [ea]; exact hA), ea,
      VG.Proof.Rsa.X86.WordRt.val32_low_of_lt (n := g.w) (Nat.div_le_self _ _) (by rw [eb]; exact hB), eb]

/-- `mulHalf o a b`: `[a] [b]`, both below `2^(32 (w / 2))`, `2 w` words from array `o` on. -/
theorem Stg.mulHalf_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a b : Nat} (ho : o + 1 < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (hol : ∀ j ∈ live, j ≠ o ∧ j ≠ o + 1) (hv : o ≠ aVD ∧ o + 1 ≠ aVD)
    (hA : A a < 2 ^ (32 * (g.w / 2))) (hB : A b < 2 ^ (32 * (g.w / 2))) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulHalf g.L o a b) s fun t => Stg g s0 A live c t ∧
      val32 t.mem g.B (arr g.w o) (2 * g.w) = A a * A b :=
  WP.mono (h.mulHalf_if_ok ho ha hb hol hv) fun _ ⟨ht, e⟩ => ⟨ht, e hA hB⟩

/-- Two words are the number, when it is below `2^64`. -/
theorem val32_two {m : Mem} {B : Addr} {w j : Nat} (hw : 2 ≤ w) (hl : num m B w j < 2 ^ 64) :
    val32 m B (arr w j) 2 = num m B w j :=
  val32_low hw hl

/-- `mulShort o a b`: `[a] [b]`, `[b] < 2^64`, `w + 2` words from array `o` on. -/
theorem Stg.mulShort_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a b : Nat} (ho : o + 1 < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (hol : ∀ j ∈ live, j ≠ o ∧ j ≠ o + 1) (hv : o ≠ aVD ∧ o + 1 ≠ aVD) (hw2 : 2 ≤ g.w) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulShort g.L o a b) s fun t => Stg g s0 A live c t ∧
      (A b < 2 ^ 64 → val32 t.mem g.B (arr g.w o) (g.w + 2) = A a * A b) := by
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.mulShort_ok h.ws hw2 ho (h.live_lt a ha) (h.live_lt b hb)
    (hol a ha).1 (hol a ha).2 (hol b hb).1 (hol b hb).2) fun t ⟨ht, k, e, r⟩ => ⟨?_, ?_⟩
  · refine h.next ht k (by simp; omega_using [ho]) (by decide) r wordRegs_body
      (h.arrs_keep k (fun j hj => by simp [(hol j hj).1, (hol j hj).2]) (by decide)) h.live_lt
      (h.vd_keep k (by simp [hv.1, hv.2]) (by decide)) (h.mask_keep k (by decide))
  · intro hB
    have gb := h.arrs.get hb
    rw [e, h.arrs.get ha, val32_two hw2 (by rw [gb]; exact hB), gb]

/-- `eqWide sF o n`: whether the `2 w` words from array `o` on are `[n]`, into `sF`. -/
theorem Stg.eqWide_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o n : Nat} (ho : o + 1 < nArr) (hn : n ∈ live) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.eqWide g.L sF o n) s fun t => Stg g s0 A live c t ∧
      slot t.mem g.B sF = if val32 s.mem g.B (arr g.w o) (2 * g.w) = A n then 1 else 0 := by
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.eqWide_ok h.ws ho (h.live_lt n hn) (by decide))
    fun t ⟨ht, k, e, r⟩ => ⟨?_, ?_⟩
  · refine h.next ht k (by simp) (by decide) r (by decide)
      (h.arrs_keep k (by simp) (by decide)) h.live_lt (h.vd_keep k (by simp) (by decide)) (h.mask_keep k (by decide))
  · rw [e, h.arrs.get hn]

/-- `balanced`: the guard into `sG`, of `n_len` (argument 1), `p_len`, `q_len` and `n`'s top word. -/
theorem Stg.balanced_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {ap aq : Nat}
    (cp : VG.Proof.Bignum.X86.CallArgument s g.B g.Z (pLenArg g.full) (BitVec.ofNat 32 ap))
    (cq : VG.Proof.Bignum.X86.CallArgument s g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 aq))
    (hap : ap ≤ 1024) (haq : aq ≤ 1024) (hn : aN ∈ live) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.balanced g.L 1 (pLenArg g.full) (qLenArg g.full) aN sG)) s
      fun t => Stg g s0 A live c t ∧ ∃ an, an ≤ 1024 ∧
        VG.Proof.Bignum.X86.CallArgument s g.B g.Z 1 (BitVec.ofNat 32 an) ∧
        VG.Proof.Rsa.X86.KeyRt.kw (g.L.toLen an) = g.w ∧
        (slot t.mem g.B sG = 0 ↔ Bal an ap aq (mw s.mem g.B g.w aN (g.w - 1))) := by
  obtain ⟨an, han, hkw, cn⟩ := h.ws.lenArg
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.balanced_ok h.ws cn cp cq han hap haq (h.live_lt aN hn) (by decide))
    fun t ⟨ht, k, e, r⟩ => ⟨?_, an, han, cn, hkw, e⟩
  refine h.next ht k (by simp) (by decide) r (by decide)
    (h.arrs_keep k (by simp) (by decide)) h.live_lt (h.vd_keep k (by simp) (by decide)) (h.mask_keep k (by decide))

/-- `ifBalanced sG word other`: `word` where `sG` is zero, else `other`. -/
theorem Stg.ifBalanced_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {P : Prop} (hg : slot s.mem g.B sG = 0 ↔ P) {W O : Prog isa} {Q : State → Prop}
    (hW : P → ∀ u, Stg g s0 A live c u → WP isa W u Q) (hO : ¬P → ∀ u, Stg g s0 A live c u → WP isa O u Q) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.ifBalanced sG W O) s Q := by
  unfold VG.Impl.Rsa.X86.WordModRt.ifBalanced
  refine WP.seq (wp_movS (readSrc_sc h.ws.ws.workspace (by have := h.ws.ws.hdr_le; unfold sG hdr at *; omega_using [this]))
    fun u U _ => wp_cmpi fun t T _ z => WP.block_nil ?_)
  have ht : Stg g s0 A live c t :=
    (h.regs U.keeps U.mem (by decide)).regs (T.keeps []) T.mem (by decide)
  have ev : u.gpr .eax = s.mem.readW (off g.B sG) 32 := U.gpr
  have sl : slot s.mem g.B sG = (s.mem.readW (off g.B sG) 32).toNat := rfl
  refine WP.ite _ (by change t.zf = _; exact z) (fun hb => hW (hg.mp ?_) t ht) (fun hb => hO (fun p => ?_) t ht)
  · rw [ev, sub0_beq, decide_eq_true_iff] at hb
    rw [sl, hb]
  · rw [ev, sub0_beq, decide_eq_false_iff_not] at hb
    exact hb (by rw [← sl]; exact hg.mpr p)

/-- `wordMod x r m top`: `[r] = X mod [m]`, `X` the dividend's words from array `x` on (`w`, or
`W' + k` for `top = some k`), by word steps, `m` of `p`'s length `W'` words, when the top bit of its
`W'` words is set (and `m` is then left as it was). -/
theorem Stg.wordMod_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {x r m ap : Nat} {top : Option Nat}
    (hm : MLen s0 g.B g.Z (pLenArg g.full) ap) (h4 : 4 ≤ wq ap) (hw : wq ap ≤ g.w)
    (htop : ∀ k, top = some k → wq ap + k ≤ g.w)
    (hx : x < nArr) (hr : r < nArr) (hmL : m ∈ live)
    (hl : ∀ j ∈ live, j ≠ r ∧ j ≠ aT) (hrm : r ≠ m) (hrT : r ≠ aT) (hmT : m ≠ aT)
    (hxr : r ≠ x) (hxt : aT ≠ x) (hxm : m ≠ x)
    (hv : m ≠ aVD ∧ r ≠ aVD) :
    WP isa (wordMod g.full x r m top) s fun t => ∃ M R,
      (Top (wq ap) (A m) →
        M = A m ∧ R = val32 s.mem g.B (arr g.w x) (VG.Proof.Rsa.X86.WordRt.xw g.len ap top) % A m) ∧
      Stg g s0 (upd (upd A m M) r R) (r :: live) c t := by
  have hmN := h.live_lt m hmL
  have fm := h.ws.ws.fit64 hmN
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.wordMod_ok h.ws ⟨h.arg hm.arg, hm.le⟩ hx hr hmN (by decide) hrT hmT hrm hxr hxt hxm
    h4 hw htop) fun t ⟨ht, k, wk, wtop, wr, K⟩ => ⟨num t.mem g.B g.w m, num t.mem g.B g.w r, ?_, ?_⟩
  · intro ⟨lo, hi⟩
    have gm := h.arrs.get hmL
    have hpos : 0 < wq ap := by omega_using [h4]
    -- `m`'s words from `W'` on are zero, its word `W' - 1` has its top bit set.
    have low : val32 s.mem g.B (arr g.w m) (wq ap) = A m := by
      rw [val32_low hw (by change num s.mem g.B g.w m < _; rw [gm]; exact hi)]; exact gm
    have topw : 2 ^ 31 ≤ mw s.mem g.B g.w m (wq ap - 1) := (top_iff hpos).mpr (by rw [low]; exact lo)
    have tlt : mw s.mem g.B g.w m (wq ap - 1) < 2 ^ 32 := (s.mem.readW _ 32).isLt
    have same : ∀ i, i < g.w + 2 → mw t.mem g.B g.w m i = mw s.mem g.B g.w m i := fun i hi' => by
      by_cases e : i = wq ap - 1
      · subst e
        have key : ∀ T : Nat, 2 ^ 31 ≤ T → T < 2 ^ 32 → T % 2 ^ 31 + 2 ^ 31 = T := fun T a b => by omega_using [a, b]
        rw [wtop]; exact key _ topw tlt
      · exact wk i hi' e
    have numEq : ∀ n, n ≤ g.w → val32 t.mem g.B (arr g.w m) n = val32 s.mem g.B (arr g.w m) n :=
      fun n hn => val32_congr (k := n) fun i (hi' : i < n) => same i (by omega_using [hn, hi'])
    refine ⟨(numEq g.w (Nat.le_refl _)).trans gm, ?_⟩
    rw [wr, numEq _ hw, low]
  · refine h.next ht k (by
        intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hmN
        · exact hr
        · decide) (by decide) K wordRegs_body ?_ ?_
      (h.vd_keep k (by simp [hv.1, hv.2]; decide) (by decide)) (h.mask_keep k (by decide))
    · exact (h.arrs_write k rfl (fun j hj => by
        by_cases e : j = m
        · exact .inl e
        · exact .inr (by simp [e, (hl j hj).1, (hl j hj).2]))
        (by decide)).add rfl
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj'
      · exact hr
      · exact h.live_lt j hj'

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! # Initial state for i686 RSA key validation -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys

structure BodyIn (g : Geo) (v : Vals) (s : State) : Prop where
  ws : VG.Proof.Rsa.X86.KeyRt.RtWs g.L s g.B g.Z g.len nArr
  arrs : Arrs s.mem g.B g.w (vals v) (List.range nArr)
  vdTop : w32 s.mem g.B (arr g.w aVD + 4 * g.w) = 0
  /-- `q`'s length argument, whose bytes bound `q`. -/
  qLen : ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ v.q < 2 ^ (8 * a) ∧
    VG.Proof.Bignum.X86.CallArgument s g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 a)
  /-- `p`'s. -/
  pLen : ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ v.p < 2 ^ (8 * a) ∧
    VG.Proof.Bignum.X86.CallArgument s g.B g.Z (pLenArg g.full) (BitVec.ofNat 32 a)

abbrev live0 : List Nat := [aZ, aOne, aN, aE, aP, aQ, aDP, aDQ, aQI, aD]

theorem first_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa (.seq (.block (VG.Impl.Rsa.X86.KeyRt.setOne g.L aOne)) (.block (VG.Impl.Rsa.X86.KeyRt.bitOf g.L sMask aP))) s
      (Stg g s (upd (vals v) aOne 1) live0 (decide (v.p % 2 = 1))) := by
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.setOne_ok h.ws (j := aOne) (by decide)) fun s4 ⟨h4, k4, e4, r4⟩ => ?_
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.bitOf_ok h4 (j := aP) (by decide) (by decide)) fun t ⟨ht, k5, e5, r5⟩ => ?_
  have a3 : Arrs s.mem g.B g.w (vals v) live0 := h.arrs.sub (by decide)
  have a4 : Arrs s4.mem g.B g.w (upd (vals v) aOne 1) live0 := by
    refine a3.write k4 h.ws.ws ?_ (by decide) (by simp)
    rw [e4, a3.get (by decide), show vals v aOne = 0 by rfl]
  have p4 : num s4.mem g.B g.w aP = v.p := by rw [a4.get (by decide)]; rfl
  refine ⟨ht, (k4.mono (by decide) (by simp)).trans (k5.mono (by simp) (by decide)),
    (r4.mono (by decide)).trans (r5.mono (by decide)), a4.keep k5 ht.ws (by decide) (by decide),
    by decide, ?_, ?_⟩
  · rw [k5.word (by unfold S Geo.w; omega_using []) (by simp) (by decide) (h.ws.ws.fit64 (by decide)),
      k4.word (by unfold S Geo.w; omega_using []) (by decide) (by simp) (h.ws.ws.fit64 (by decide)), h.vdTop]
  · rw [e5, p4]
    rcases Nat.mod_two_eq_zero_or_one v.p with e | e <;> simp [e]

/-- The arrays after `start`. -/
abbrev aStart (v : Vals) : Nat → Nat := upd (vals v) aOne 1

/-- `start`: `1`, and the mask of `p` odd and `p q = n`. -/
theorem start_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa (start g.full) s (Stg g s (aStart v) live0 (decide (v.p % 2 = 1) && decide (v.p * v.q = v.n))) := by
  unfold start
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have f := first_ok h
  rw [WP.seq_iff] at f
  refine WP.mono f fun u hu => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono hu fun t ht => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  -- The guard, then the product: over the primes' `w / 2` words where it holds.
  obtain ⟨ap, -, hap, plt, parg⟩ := h.pLen
  obtain ⟨aq, -, haq, qlt, qarg⟩ := h.qLen
  refine WP.mono (ht.balanced_ok (ht.arg parg) (ht.arg qarg) hap haq (by decide))
    fun t7 ⟨h7, an, _, _, hkw, hg⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h7.ifBalanced_ok hg (Q := fun t1 => Stg g s (aStart v) live0 (decide (v.p % 2 = 1)) t1 ∧
      val32 t1.mem g.B (arr g.w aVQ) (2 * g.w) = aStart v aP * aStart v aQ)
    (fun bal u hu => ?_) fun _ u hu => hu.mulWide_ok (o := aVQ) (a := aP) (b := aQ) (by decide) (by decide)
      (by decide) (by decide) (by decide)) fun t1 ⟨h1, e1⟩ => ?_
  · obtain ⟨h8, hpa, hqa, -, -⟩ := bal
    have hkw' : VG.Proof.Rsa.X86.KeyRt.kw an = g.w := hkw
    have hw : g.w = an / 4 := by
      rw [← hkw']
      simp only [VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords]; omega_using [h8]
    have e8 : 32 * (g.w / 2) = 8 * ap := by omega_using [h8, hpa, hw]
    exact hu.mulHalf_ok (o := aVQ) (a := aP) (b := aQ) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by show v.p < _; rw [e8]; exact plt) (by show v.q < _; rw [e8, show 8 * ap = 8 * aq by omega_using [hpa, hqa]]; exact qlt)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.eqWide_ok (o := aVQ) (n := aN) (by decide) (by decide)) fun t2 ⟨h2, e2⟩ => ?_
  refine h2.acc_ok ?_
  rw [e2, e1]
  change (if v.p * v.q = v.n then 1 else 0) = _
  by_cases hh : v.p * v.q = v.n <;> simp [hh]
end VG.Proof.Rsa.X86.KeyCheck
