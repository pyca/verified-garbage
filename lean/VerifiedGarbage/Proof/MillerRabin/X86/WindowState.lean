module

public import VerifiedGarbage.Proof.MillerRabin.X86.SquareState
public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.DataSlots
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.MillerRabin.X86.FlagMath
import VerifiedGarbage.Proof.MillerRabin.X86.MaskMath
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! ### `MillerRabin.X86.DataWindowControl`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.Counter`, which this module and modules that import it used -/

section

/-! # A positive public counter is decremented and determines the loop branch -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (count1_zf)

theorem counterDown_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (d q : Nat) (scratch : scratchWord d) (positive : 0 < q) (bound : q < 2 ^ 32)
    (count : s.mem.readW (off g.W d) 32 = BitVec.ofNat 32 q) :
    WP isa (.block [.mov .eax (.mem (slot d)), .alu .sub .eax (.imm 1), .store (slot d) .eax]) s fun t =>
      w32 t.mem g.W d = q - 1 ∧ t.zf = some (decide (q = 1)) ∧
      Outside g.W d 4 s.mem t.mem ∧ Keeps [.eax] s t ∧ Context g t := by
  have fit : d + 4 ≤ g.L := by have := v.headerFit; unfold scratchWord at scratch; omega_using [scratch, this]
  refine wp_movS (C.readScalar d fit) fun a A _ => wp_subZ rfl fun b B Z => ?_
  have Ka : Keeps [.eax] s b := A.keeps.trans B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  have Cb := C.keepMem Ka (by decide) Mb
  refine wp_storeS (ea_ptr Cb.ws Cb.base (d := d) (by omega_using [fit]))
    (ws_write Cb.ws (y := 0 + d) (n := 4) (by omega_using [fit])) fun t T => WP.block_nil ?_
  have ax : (a.gpr .eax).toNat = q - 0 := by
    rw [A.gpr, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.sub_zero]
  obtain ⟨V, last⟩ := count1_zf (N := q) (j := 0) ax positive
  have O : Outside g.W d 4 s.mem t.mem := by
    rw [T.mem, Nat.zero_add, Mb]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; omega_using [fit, this])
  have Kt : Keeps [.eax] s t := Ka.widen (T.keeps [])
  refine ⟨?_, ?_, O, Kt, C.keepScalar Kt (by decide) O scratch⟩
  · rw [T.mem, Nat.zero_add, w32_write_self, B.gpr]
    exact V
  · rw [T.zf, Z, last]
    congr 1
    exact decide_eq_decide.mpr (by omega_using [])

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.AdvanceWindow`, which only this module used -/

section

/-! # Advance the exponent word and count down its eight public windows -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/ShiftWindow.lean`, which only this module imported.
section

/-! # Four native-word doublings advance one fixed-width secret window -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem doubleFour_ok (s : State) :
    WP isa (.block [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax)]) s fun t =>
      t.gpr .eax = s.gpr .eax <<< 4 ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  refine wp_addS rfl fun a A _ => wp_addS rfl fun b B _ =>
    wp_addS rfl fun c C _ => wp_addS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (C.mem.trans (B.mem.trans A.mem)),
    ((A.keeps.trans B.keeps).trans C.keeps).trans T.keeps⟩
  rw [T.gpr, C.gpr, B.gpr, A.gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def advanceWindow : List Instr :=
  [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .store (slot sValue) .eax, .mov .eax (.mem (slot sWindows)),
    .alu .sub .eax (.imm 1), .store (slot sWindows) .eax]

theorem advanceWindow_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (q : Nat) (positive : 0 < q) (bound : q < 2 ^ 32)
    (count : s.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 q) :
    WP isa (.block advanceWindow) s fun t =>
      t.mem.readW (off g.W sValue) 32 = s.gpr .eax <<< 4 ∧
      w32 t.mem g.W sWindows = q - 1 ∧ t.zf = some (decide (q = 1)) ∧
      Outs g.W [(sValue, 4), (sWindows, 4)] s.mem t.mem ∧ Keeps [.eax] s t ∧ Context g t := by
  have header := v.headerFit
  have fitV : sValue + 4 ≤ g.L := by unfold sValue; omega_using [header]
  change WP isa (.block ([.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax)] ++
    [.store (slot sValue) .eax, .mov .eax (.mem (slot sWindows)),
      .alu .sub .eax (.imm 1), .store (slot sWindows) .eax])) s _
  refine WP.block_append (WP.mono (doubleFour_ok s) fun a ⟨AX, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine wp_storeS (ea_ptr Ca.ws Ca.base (d := sValue) (by omega_using [fitV]))
    (ws_write Ca.ws (y := 0 + sValue) (n := 4) (by omega_using [fitV])) fun b B => ?_
  have Ov : Outside g.W sValue 4 a.mem b.mem := by
    rw [B.mem, Nat.zero_add]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; omega_using [fitV, this])
  have Cb := Ca.keepScalar (B.keeps []) (by decide) Ov (by unfold scratchWord sValue; simp)
  have oldCount : b.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 q := by
    have unchanged := BitVec.eq_of_toNat_eq (Ov.w32 (d := sWindows)
      (by unfold sValue sWindows; omega_using []) (by unfold sWindows; decide))
    rw [unchanged, Ma, count]
  refine WP.mono (counterDown_ok v Cb sWindows q (by unfold scratchWord sWindows; simp)
    positive bound oldCount) fun t ⟨Count, Z, Ow, Kw, Ct⟩ => ?_
  have O₁ : Outs g.W [(sValue, 4), (sWindows, 4)] s.mem b.mem := by
    rw [Ma] at Ov
    exact Outs.of_outside Ov (by simp)
  refine ⟨?_, Count, Z, O₁.trans (Outs.of_outside Ow (by simp)),
    (Ka.widen (B.keeps [])).trans Kw, Ct⟩
  have unchanged := BitVec.eq_of_toNat_eq (Ow.w32 (d := sValue)
    (by unfold sValue sWindows; omega_using []) (by unfold sValue; decide))
  rw [unchanged, B.mem, Nat.zero_add, Mem.readW_writeW_self32, AX]

end VG.Proof.MillerRabin.X86

end

end

/-! # One exponent-window update retains exact known values -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/WindowBits.lean`, which only this module imported.
section

/-! # A window replaces the pass flag exactly when its digit is nonzero -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem windowBits_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (E1 E2 F : Bool)
    (eq1 : s.mem.readW (off g.W sEq1) 32 = BitVec.ofNat 32 E1.toNat)
    (eq2 : s.mem.readW (off g.W sEq2) 32 = BitVec.ofNat 32 E2.toNat)
    (flag : s.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32 F.toNat) :
    WP isa (.block (windowEnd.take 12)) s fun t =>
      t.gpr .eax = s.mem.readW (off g.W sValue) 32 ∧
      (t.gpr .ecx).toNat = (if (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = 0 then F else E1 || E2).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have header := v.headerFit
  change WP isa (.block [.mov .eax (.mem (slot sValue)), .mov .edx (.reg .eax), .shift .shr .edx 28,
    .alu .sub .edx (.imm 1), .shift .shr .edx 31, .mov .ebx (.reg .edx), .alu .xor .ebx (.imm 1),
    .mov .ecx (.mem (slot sEq1)), .alu .or .ecx (.mem (slot sEq2)), .alu .and .ecx (.reg .ebx),
    .alu .and .edx (.mem (slot sFlag)), .alu .or .ecx (.reg .edx)]) s _
  refine wp_movS (C.readScalar sValue (by unfold sValue; omega)) fun a A _ => ?_
  refine wp_movS rfl fun b B _ => wp_shr (by decide) fun c D _ => wp_subS rfl fun d H _ => ?_
  refine wp_shr (by decide) fun e I _ => wp_movS rfl fun f J _ => wp_logicS (.inr rfl) rfl fun h K => ?_
  have Kh : Keeps [.eax, .ebx, .edx] s h :=
    ((((((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps).widen H.keeps).widen I.keeps).widen J.keeps).widen K.keeps
  have Mh : h.mem = s.mem := by rw [K.mem, J.mem, I.mem, H.mem, D.mem, B.mem, A.mem]
  refine wp_movS (C.readScalarAfter Kh (by decide) Mh sEq1 (by unfold sEq1; omega)) fun i L _ => ?_
  have Ki : Keeps [.eax, .ebx, .ecx, .edx] s i := (Kh.mono (by decide)).widen L.keeps
  have Mi : i.mem = s.mem := L.mem.trans Mh
  refine wp_orS (C.readScalarAfter Ki (by decide) Mi sEq2 (by unfold sEq2; omega)) fun j N => ?_
  refine wp_logicS (.inl rfl) rfl fun k P => ?_
  have Kk : Keeps [.eax, .ebx, .ecx, .edx] s k := (Ki.widen N.keeps).widen P.keeps
  have Mk : k.mem = s.mem := P.mem.trans (N.mem.trans Mi)
  refine wp_logicS (.inl rfl) (C.readScalarAfter Kk (by decide) Mk sFlag (by unfold sFlag; omega)) fun l Q => ?_
  refine wp_orS rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, T.mem.trans (Q.mem.trans Mk), (Kk.widen Q.keeps).widen T.keeps⟩
  · rw [T.other .eax (by decide), Q.other .eax (by decide), P.other .eax (by decide),
      N.other .eax (by decide), L.other .eax (by decide), K.other .eax (by decide),
      J.other .eax (by decide), I.other .eax (by decide), H.other .eax (by decide),
      D.other .eax (by decide), B.other .eax (by decide), A.gpr]
  · rw [T.gpr, Q.other .ecx (by decide), P.gpr, N.gpr, L.gpr, eq1, eq2,
      N.other .ebx (by decide), L.other .ebx (by decide), K.gpr, J.gpr,
      Q.gpr, P.other .edx (by decide), N.other .edx (by decide), L.other .edx (by decide),
      K.other .edx (by decide), J.other .edx (by decide), I.gpr, H.gpr, D.gpr, B.gpr, A.gpr, flag]
    change let z := ((s.mem.readW (off g.W sValue) 32 >>> 28) - 1) >>> 31
      (((BitVec.ofNat 32 E1.toNat ||| BitVec.ofNat 32 E2.toNat) &&& (z ^^^ 1)) |||
        (z &&& BitVec.ofNat 32 F.toNat)).toNat = _
    have digit := digit_lt (s.mem.readW (off g.W sValue) 32)
    have result := windowFlag_value digit E1 E2 F
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using result

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/WindowControl.lean`, which only this module imported.
section

/-! # A complete window end updates secret data and a public countdown -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def windowWrites : List (Nat × Nat) := [(sFlag, 4), (sValue, 4), (sWindows, 4)]

theorem windowEnd_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (q : Nat) (positive : 0 < q) (bound : q < 2 ^ 32) (E1 E2 F : Bool)
    (eq1 : s.mem.readW (off g.W sEq1) 32 = BitVec.ofNat 32 E1.toNat)
    (eq2 : s.mem.readW (off g.W sEq2) 32 = BitVec.ofNat 32 E2.toNat)
    (flag : s.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32 F.toNat)
    (count : s.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 q) :
    WP isa (.block windowEnd) s fun t =>
      w32 t.mem g.W sFlag =
        (if (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = 0 then F else E1 || E2).toNat ∧
      t.mem.readW (off g.W sValue) 32 = s.mem.readW (off g.W sValue) 32 <<< 4 ∧
      w32 t.mem g.W sWindows = q - 1 ∧ t.zf = some (decide (q = 1)) ∧
      Outs g.W windowWrites s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t ∧ Context g t := by
  have header := v.headerFit
  have fitF : sFlag + 4 ≤ g.L := by unfold sFlag; omega_using [header]
  change WP isa (.block (windowEnd.take 12 ++ .store (slot sFlag) .ecx :: advanceWindow)) s _
  refine WP.block_append (WP.mono (windowBits_ok v C E1 E2 F eq1 eq2 flag)
    fun a ⟨AX, Flag, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine wp_storeS (ea_ptr Ca.ws Ca.base (d := sFlag) (by omega_using [fitF]))
    (ws_write Ca.ws (y := 0 + sFlag) (n := 4) (by omega_using [fitF])) fun b B => ?_
  have Of : Outside g.W sFlag 4 a.mem b.mem := by
    rw [B.mem, Nat.zero_add]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; omega_using [fitF, this])
  have Cb := Ca.keepScalar (B.keeps []) (by decide) Of (by unfold scratchWord sFlag; simp)
  have oldCount : b.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 q := by
    have unchanged := BitVec.eq_of_toNat_eq (Of.w32 (d := sWindows)
      (by unfold sFlag sWindows; omega_using []) (by unfold sWindows; decide))
    rw [unchanged, Ma, count]
  refine WP.mono (advanceWindow_ok v Cb q positive bound oldCount)
    fun t ⟨Value, Count, Z, Ot, Kt, Ct⟩ => ?_
  have O₁ : Outs g.W windowWrites s.mem b.mem := by
    rw [Ma] at Of
    exact Outs.of_outside Of (by simp [windowWrites])
  have O₂ : Outs g.W windowWrites b.mem t.mem := Ot.mono (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> simp [windowWrites])
  refine ⟨?_, ?_, Count, Z, O₁.trans O₂, (Ka.widen (B.keeps [])).widen Kt, Ct⟩
  · have preserved := (WorkspaceFrame.of_outs Cb.ws.nowrap Ot).read32 fitF (by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> left <;> decide)
    change (t.mem.readW (off g.W sFlag) 32).toNat = _
    rw [preserved, B.mem, Nat.zero_add, Mem.readW_writeW_self32]
    exact Flag
  · rw [Value, B.gpr, AX]

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def windowSlots (V : Nat → BitVec 32) (q : Nat) (E1 E2 F : Bool) : Nat → BitVec 32 :=
  setAt (setAt (setAt V sFlag (BitVec.ofNat 32
      (if (V sValue >>> 28).toNat = 0 then F else E1 || E2).toNat))
    sValue (V sValue <<< 4)) sWindows (BitVec.ofNat 32 (q - 1))

theorem Data.windowEnd {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    (q : Nat) (positive : 0 < q) (bound : q < 2 ^ 32) (E1 E2 F : Bool)
    (known : ∀ d ∈ [sEq1, sEq2, sFlag, sValue, sWindows], d ∈ Ds)
    (eq1 : V sEq1 = BitVec.ofNat 32 E1.toNat) (eq2 : V sEq2 = BitVec.ofNat 32 E2.toNat)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWindows = BitVec.ofNat 32 q) :
    WP isa (.block windowEnd) s fun t =>
      Data g A Js (windowSlots V q E1 E2 F) ([sFlag, sValue, sWindows] ++ Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ Outs g.W windowWrites s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have read (d : Nat) (mem : d ∈ [sEq1, sEq2, sFlag, sValue, sWindows]) := (D.slotValues d (known d mem)).2
  refine WP.mono (windowEnd_ok v D.context q positive bound E1 E2 F
    ((read _ (by simp)).trans eq1) ((read _ (by simp)).trans eq2)
    ((read _ (by simp)).trans flag) ((read _ (by simp)).trans count))
    fun t ⟨Flag, Value, Count, Z, O, K, C⟩ => ?_
  rw [read sValue (by simp)] at Flag Value
  have flagWord : t.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32
      (if (V sValue >>> 28).toNat = 0 then F else E1 || E2).toNat := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W sFlag = _
    rw [Flag]
    cases (if (V sValue >>> 28).toNat = 0 then F else E1 || E2) <;> rfl
  have countWord : t.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 (q - 1) := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W sWindows = _
    rw [Count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]
  refine ⟨D.afterSlots v C [sFlag, sValue, sWindows] ?_ ?_ O, Z, O, K⟩
  · intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · refine ⟨by unfold scratchWord sFlag; simp, ?_⟩
      change t.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32
        (if (V sValue >>> 28).toNat = 0 then F else E1 || E2).toNat
      exact flagWord
    · refine ⟨by unfold scratchWord sValue; simp, ?_⟩
      change t.mem.readW (off g.W sValue) 32 = V sValue <<< 4
      exact Value
    · refine ⟨by unfold scratchWord sWindows; simp, ?_⟩
      change t.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 (q - 1)
      exact countWord
  · intro d _ none
    have nf : d ≠ sFlag := fun eq => none (by simp [eq])
    have nv : d ≠ sValue := fun eq => none (by simp [eq])
    have nw : d ≠ sWindows := fun eq => none (by simp [eq])
    exact ((setAt_other _ _ nw).trans (setAt_other _ _ nv)).trans (setAt_other _ _ nf)

end VG.Proof.MillerRabin.X86

end

end

/-! # Values through four squares, a complete table scan and one window product -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

def windowFields : List Nat := [sFlag, sValue, sWords, sWindows]

def windowDigit (V : Nat → BitVec 32) : Nat := (V sValue >>> 28).toNat

def windowSquaresV (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Nat → BitVec 32 :=
  squareCounters (setAt (setAt V sThreshold 0#32) sSquares 4#32) A c w 0 4 F 4

def windowScanA (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Nat → Nat :=
  let sq := squareValues A c w 0 4 F 4
  setAt sq aX (sq (aTable + windowDigit V))

def windowProductA (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Nat → Nat :=
  let scan := windowScanA V A c w F
  setAt scan aY (Word32.mm c w (scan aY) (scan aX))

def windowOne (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Bool :=
  decide (windowProductA V A c w F aY = windowProductA V A c w F aOne)

def windowMinus (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Bool :=
  decide (windowProductA V A c w F aY = windowProductA V A c w F aMinusOne)

def windowEqV (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Nat → BitVec 32 :=
  setAt (setAt (windowSquaresV V A c w F) sEq1 (BitVec.ofNat 32 (windowOne V A c w F).toNat))
    sEq2 (BitVec.ofNat 32 (windowMinus V A c w F).toNat)

def windowResult (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Nat × Bool :=
  Word32.mwin c w (A aMinusOne) (fun d => A (aTable + d)) (windowDigit V) (A aY, F)

def windowCounters (V : Nat → BitVec 32) (A : Nat → Nat) (c w q : Nat) (F : Bool) : Nat → BitVec 32 :=
  setAt (setAt (setAt V sFlag (BitVec.ofNat 32 (windowResult V A c w F).2.toNat))
    sValue (V sValue <<< 4)) sWindows (BitVec.ofNat 32 (q - 1))

theorem windowScan_product (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) :
    Word32.mm c w (windowScanA V A c w F aY) (windowScanA V A c w F aX) =
      (windowResult V A c w F).1 := by
  unfold windowScanA windowResult squareValues Word32.mwin
  rw [setAt_other _ _ (by decide : aY ≠ aX), setAt_self, setAt_self,
    setAt_other _ _ (by unfold aTable aY; omega_using [] : aTable + windowDigit V ≠ aY)]
  rfl

theorem windowProduct_value (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool)
    {j : Nat} (notX : j ≠ aX) :
    windowProductA V A c w F j = setAt A aY (windowResult V A c w F).1 j := by
  unfold windowProductA
  rw [windowScan_product]
  by_cases y : j = aY
  · subst j; rw [setAt_self, setAt_self]
  · rw [setAt_other _ _ y, windowScanA, setAt_other _ _ notX,
      squareValues, setAt_other _ _ y, setAt_other _ _ y]

theorem windowResult_flag (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool)
    (one : A aTable = A aOne) :
    (if windowDigit V = 0 then (squareState A c w 0 4 F 4).2
      else windowOne V A c w F || windowMinus V A c w F) = (windowResult V A c w F).2 := by
  unfold windowOne windowMinus
  rw [windowProduct_value V A c w F (by decide : aY ≠ aX), setAt_self,
    windowProduct_value V A c w F (by decide : aOne ≠ aX),
    setAt_other _ _ (by decide : aOne ≠ aY),
    windowProduct_value V A c w F (by decide : aMinusOne ≠ aX),
    setAt_other _ _ (by decide : aMinusOne ≠ aY)]
  change (if windowDigit V = 0 then (squareState A c w 0 4 F 4).2 else
    decide ((windowResult V A c w F).1 = A aOne) ||
      decide ((windowResult V A c w F).1 = A aMinusOne)) = _
  rw [← one]
  rfl

theorem windowCounters_eq (V : Nat → BitVec 32) (A : Nat → Nat) (c w q : Nat) (F : Bool)
    (one : A aTable = A aOne) {d : Nat} (known : d ∈ windowFields) :
    windowSlots (windowEqV V A c w F) q (windowOne V A c w F) (windowMinus V A c w F)
      (squareState A c w 0 4 F 4).2 d = windowCounters V A c w q F d := by
  change d ∈ [184, 208, 232, 240] at known
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl
  · change BitVec.ofNat 32 (if windowDigit V = 0 then (squareState A c w 0 4 F 4).2 else
      windowOne V A c w F || windowMinus V A c w F).toNat = _
    rw [windowResult_flag V A c w F one]
    rfl
  · rfl
  · rfl
  · rfl

end VG.Proof.MillerRabin.X86
