module

public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Impl.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! ### `Rsa.X86.DivBit`, which only this module used -/

section

/-! # Insert one division bit into an even native-word array -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Div

theorem insertBit_raw {s : State} {base : Addr} {size dst : Nat} (hs : Scr s base size)
    (fit : dst + 4 ≤ size) :
    WP isa (.block (insertBit dst)) s fun t =>
      t.mem = s.mem.writeW (off base dst) (s.mem.readW (off base dst) 32 + s.gpr .ebx) ∧
      Keeps [.eax] s t := by
  unfold insertBit
  refine wp_movS (readSrc_sc hs fit) fun u U _ => ?_
  refine wp_addS rfl fun v V _ => ?_
  have hv := (hs.of_keeps U.keeps (by decide)).of_keeps V.keeps (by decide)
  refine wp_storeS (hv.ea (by omega_using [fit])) (hv.write fit) fun t T => WP.block_nil ?_
  refine ⟨?_, (U.keeps.trans V.keeps).trans (T.keeps _)⟩
  rw [T.mem, V.mem, U.mem, V.gpr, U.gpr, U.other .ebx (by decide)]

theorem insertBit_ok {s : State} {base : Addr} {size n dst : Nat} (hs : Scr s base size)
    (hn : 0 < n) (fit : dst + 4 * n ≤ size) (bit : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (.block (insertBit dst)) s fun t =>
      Outside base dst (4 * n) s.mem t.mem ∧ Keeps [.eax] s t ∧
      (val32 s.mem base dst n % 2 = 0 →
        val32 t.mem base dst n = val32 s.mem base dst n + (s.gpr .ebx).toNat) := by
  refine WP.mono (insertBit_raw hs (by omega_using [hn, fit])) ?_
  rintro t ⟨mem, rest⟩
  have outside := writeW32_outside s.mem base (d := dst)
    (s.mem.readW (off base dst) 32 + s.gpr .ebx) (by have := hs.nowrap; omega_using [fit, this])
  rw [← mem] at outside
  refine ⟨outside.mono (Nat.le_refl _) (by omega_using [hn]), rest, ?_⟩
  intro even
  have low (m : Mem) : val32 m base dst n =
      w32 m base dst + 2 ^ 32 * val32 m base (dst + 4) (n - 1) := by
    rw [show n = (n - 1) + 1 by omega_using [hn]]
    rfl
  rw [low s.mem] at even
  have lowEven : (s.mem.readW (off base dst) 32).toNat % 2 = 0 := by
    change w32 s.mem base dst % 2 = 0
    omega_using [even]
  have wordBound := (s.mem.readW (off base dst) 32).isLt
  have nowrap := hs.nowrap
  have high := outside.val32 (d := dst + 4) (k := n - 1) (by omega_using []) (by omega_using [fit, nowrap])
  rw [low t.mem, low s.mem, high]
  have head : w32 t.mem base dst = w32 s.mem base dst + (s.gpr .ebx).toNat := by
    rw [mem, w32_write_self, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega_using [bit, lowEven])]
  rw [head]
  omega_using []
end VG.Proof.Rsa.X86.Div

end

end

/-! ### `Rsa.X86.DivStep`, which only this module used -/

section

/-! ### `Rsa.X86.DivShiftArrays`, which only this module used -/

section

/-! # The quotient's high bit is shifted into the extended remainder -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/DivShift.lean`, which only this module imported.
section

/-! # The division shift returns the high bit without branching on it -/

section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Rsa.X86.Div

theorem saveCarry_ok (s : State) (save : Bool) (c : Bool) (hc : s.gpr .ecx = cmask c) :
    WP isa (.block (if save then [.mov .ebx (.reg .ecx), .alu .and .ebx (.imm 1)] else [])) s fun t =>
      t.gpr .ebx = (if save then (BitVec.ofBool c).setWidth 32 else s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.ebx] s t := by
  cases save with
  | false => exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | true =>
    refine wp_movS rfl fun u U _ => ?_
    refine wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
    refine ⟨?_, T.mem.trans U.mem, U.keeps.trans T.keeps⟩
    rw [T.gpr, U.gpr, hc, ite_eq_left rfl]
    cases c <;> rfl

theorem shift_ok {s : State} {base : Addr} {size n dst tmp : Nat} (hs : Scr s base size)
    (hn : 0 < n) (hdst : dst + 4 * n ≤ size) (htmp : tmp + 4 * n ≤ size)
    (sep : tmp + 4 * n ≤ dst ∨ dst + 4 * n ≤ tmp) (save : Bool) :
    WP isa (shift n dst tmp save) s fun t =>
      Outs base [(dst, 4 * n), (tmp, 4 * n)] s.mem t.mem ∧
      (∃ c : Bool, val32 t.mem base dst n + 2 ^ (32 * n) * c.toNat =
          2 * val32 s.mem base dst n ∧
        t.gpr .ebx = (if save then (BitVec.ofBool c).setWidth 32 else s.gpr .ebx)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold shift
  refine WP.seq (WP.mono (chainAddW_ok hs hn htmp hdst hdst sep sep) ?_)
  rintro u ⟨frameU, ⟨c, carry, value⟩, restU⟩
  refine WP.seq (WP.mono (saveCarry_ok u save c carry) ?_)
  rintro w ⟨bit, memW, restW⟩
  have hw := (hs.of_keeps restU (by decide)).of_keeps restW (by decide)
  refine WP.mono (copyWords_ok hw hn htmp hdst (by omega)) ?_
  rintro t ⟨frameT, valueT, restT⟩
  refine ⟨(Outs.of_outside frameU (by simp)).trans ?_, ⟨c, ?_, ?_⟩,
    (restU.mono (by decide)).trans ((restW.mono (by decide)).trans (restT.mono (by decide)))⟩
  · rw [memW] at frameT
    exact Outs.of_outside frameT (by simp)
  · rw [valueT, memW]
    omega
  · rw [restT.1 .ebx (by decide), bit, restU.1 .ebx (by decide)]
end VG.Proof.Rsa.X86.Div
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Rsa.X86.Div

theorem shiftArrays_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (shiftArrays g.n (g.offsets 0) (g.offsets 1) (g.offsets 3)) s fun t =>
      g.value t.mem 0 = 2 * g.value s.mem 0 % 2 ^ (32 * g.n) ∧
      (g.value s.mem 1 < 2 ^ (32 * g.n) →
        g.value t.mem 1 = 2 * g.value s.mem 1 + g.value s.mem 0 / 2 ^ (32 * g.n - 1)) ∧
      Context g t ∧ Outs g.base g.ranges s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have f0 : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := h.fits 1
  have f3 : g.offsets 3 + 4 * (g.n + 1) ≤ g.size := h.fits 3
  have sep01 : g.offsets 0 + 4 * g.n ≤ g.offsets 1 ∨
      g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 1 (by decide)
  have sep03 : g.offsets 0 + 4 * g.n ≤ g.offsets 3 ∨
      g.offsets 3 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 3 (by decide)
  have sep13 : g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 3 ∨
      g.offsets 3 + 4 * (g.n + 1) ≤ g.offsets 1 := h.separate 1 3 (by decide)
  have nowrap := h.workspace.nowrap
  unfold shiftArrays
  refine WP.seq (WP.mono (shift_ok h.workspace h.positive f0 (by omega_using [f3]) (by omega_using [sep03]) true) ?_)
  rintro u ⟨frameU, ⟨c, qVal, bitU⟩, restU⟩
  change g.value u.mem 0 + 2 ^ (32 * g.n) * c.toNat = 2 * g.value s.mem 0 at qVal
  have hu := h.after restU
  have remU : g.value u.mem 1 = g.value s.mem 1 := by
    change val32 _ _ _ (g.n + 1) = val32 _ _ _ (g.n + 1)
    apply frameU.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega_arith
    · omega_using [f1, nowrap]
  refine WP.seq (WP.mono (shift_ok hu.workspace (by omega_using []) f1 f3 (by omega_using [sep13]) false) ?_)
  rintro w ⟨frameW, ⟨cr, rVal, bitW⟩, restW⟩
  have hw := hu.after restW
  have bit : (w.gpr .ebx).toNat = c.toNat := by
    rw [bitW, bitU]
    cases c <;> rfl
  have boundedBit : (w.gpr .ebx).toNat ≤ 1 := by rw [bit]; cases c <;> decide
  refine WP.mono (insertBit_ok hw.workspace (by omega_using []) f1 boundedBit) ?_
  rintro t ⟨frameT, restT, remT⟩
  change g.value w.mem 1 % 2 = 0 → g.value t.mem 1 = g.value w.mem 1 + (w.gpr .ebx).toNat at remT
  have quoW : g.value w.mem 0 = g.value u.mem 0 := by
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    apply frameW.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega_arith
    · omega_using [f0, nowrap]
  have quoT : g.value t.mem 0 = g.value w.mem 0 := by
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    exact frameT.val32 (by omega_using [sep01]) (by omega_using [f0, nowrap])
  have quoBound : g.value u.mem 0 < 2 ^ (32 * g.n) := val32_lt _ _ _ _
  have quoOriginal : g.value s.mem 0 < 2 ^ (32 * g.n) := val32_lt _ _ _ _
  have radix : 2 ^ (32 * g.n) = 2 * 2 ^ (32 * g.n - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := h.positive; omega_using [this]
  have quotient : g.value u.mem 0 = 2 * g.value s.mem 0 % 2 ^ (32 * g.n) := by
    have eq := congrArg (fun x => x % 2 ^ (32 * g.n)) qVal
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt quoBound] at eq
    exact eq
  have high : c.toNat = g.value s.mem 0 / 2 ^ (32 * g.n - 1) := by
    change g.value u.mem 0 + 2 ^ (32 * g.n) * c.toNat = 2 * g.value s.mem 0 at qVal
    rw [radix] at qVal quoOriginal quoBound
    cases c with
    | false =>
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at qVal ⊢
      exact (Nat.div_eq_of_lt (by omega_using [quoBound, qVal])).symm
    | true =>
      simp only [Bool.toNat_true, Nat.mul_one] at qVal ⊢
      exact (Nat.div_eq_of_lt_le (by omega_using [qVal]) (by omega_using [quoOriginal])).symm
  refine ⟨quoT.trans (quoW.trans quotient), ?_, hw.after restT,
    (quotientShift_frame frameU).trans ((frameW.mono (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Geometry.ranges])).trans
        (Outs.of_outside frameT (by simp [Geometry.ranges]))),
    restU.trans (restW.trans (restT.mono (by decide)))⟩
  intro remBound
  change g.value w.mem 1 + 2 ^ (32 * (g.n + 1)) * cr.toNat = 2 * g.value u.mem 1 at rVal
  have remWidth : g.value w.mem 1 < 2 ^ (32 * (g.n + 1)) := val32_lt _ _ _ _
  rw [remU, pow32_succ] at rVal
  have remDouble : g.value w.mem 1 = 2 * g.value s.mem 1 := by
    cases cr <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at rVal <;> omega_arith
  have even : g.value w.mem 1 % 2 = 0 := by rw [remDouble]; omega_using []
  rw [remT even, bit, remDouble, high]
end VG.Proof.Rsa.X86.Div

end

end

/-! ### `Rsa.X86.DivReduce`, which only this module used -/

section

/-! # Conditional subtraction selects the next remainder and quotient bit -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Rsa.X86.Div

theorem selectMask_ok (s : State) (c : Bool) (hc : s.gpr .ecx = cmask c) :
    WP isa (.block selectMask) s fun t =>
      t.gpr .ecx = cmask (!c) ∧ t.gpr .ebx = (BitVec.ofBool (!c)).setWidth 32 ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ecx] s t := by
  unfold selectMask
  refine wp_movS rfl fun u U _ => ?_
  refine wp_logicS (.inr rfl) rfl fun v V => ?_
  refine wp_logicS (.inl rfl) rfl fun w W => ?_
  refine wp_logicS (.inr rfl) rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, T.mem.trans (W.mem.trans (V.mem.trans U.mem)),
    (U.keeps.mono (by decide)).trans ((V.keeps.mono (by decide)).trans
      ((W.keeps.mono (by decide)).trans (T.keeps.mono (by decide))))⟩
  · rw [T.gpr, W.other .ecx (by decide), V.other .ecx (by decide), U.other .ecx (by decide), hc,
      ite_eq_right (by decide)]
    cases c <;> rfl
  · rw [T.other .ebx (by decide), W.gpr, V.gpr, U.gpr, hc,
      ite_eq_left rfl, ite_eq_right (by decide)]
    cases c <;> rfl

theorem reduce_ok {s : State} {base : Addr} {size n rem divisor tmp : Nat} (hs : Scr s base size)
    (hrem : rem + 4 * (n + 1) ≤ size) (hdiv : divisor + 4 * (n + 1) ≤ size)
    (htmp : tmp + 4 * (n + 1) ≤ size)
    (sr : tmp + 4 * (n + 1) ≤ rem ∨ rem + 4 * (n + 1) ≤ tmp)
    (sd : tmp + 4 * (n + 1) ≤ divisor ∨ divisor + 4 * (n + 1) ≤ tmp) :
    WP isa (reduce n rem divisor tmp) s fun t =>
      Outs base [(rem, 4 * (n + 1)), (tmp, 4 * (n + 1))] s.mem t.mem ∧
      val32 t.mem base rem (n + 1) =
        (if val32 s.mem base rem (n + 1) < val32 s.mem base divisor (n + 1)
          then val32 s.mem base rem (n + 1)
          else val32 s.mem base rem (n + 1) - val32 s.mem base divisor (n + 1)) ∧
      t.gpr .ebx = (if val32 s.mem base rem (n + 1) < val32 s.mem base divisor (n + 1) then 0 else 1) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold reduce
  refine WP.seq (WP.mono (chainSubW_ok hs (by omega_using []) htmp hrem hdiv sr sd) ?_)
  rintro u ⟨frameU, ⟨c, carry, value⟩, restU⟩
  refine WP.seq (WP.mono (selectMask_ok u c carry) ?_)
  rintro w ⟨mask, bit, memW, restW⟩
  have hw := (hs.of_keeps restU (by decide)).of_keeps restW (by decide)
  refine WP.mono (selectsW_ok hw (!c) mask (by omega_using []) hrem htmp hrem (.inl rfl) (by omega_using [sr])) ?_
  rintro t ⟨frameT, valueT, restT⟩
  have nowrap := hs.nowrap
  have same : val32 w.mem base rem (n + 1) = val32 s.mem base rem (n + 1) := by
    rw [memW]
    exact frameU.val32 (by omega_using [sr]) (by omega_using [hrem, nowrap])
  have ub := val32_lt u.mem base tmp (n + 1)
  have rb := val32_lt s.mem base rem (n + 1)
  have db := val32_lt s.mem base divisor (n + 1)
  refine ⟨(Outs.of_outside frameU (by simp)).trans ?_, ?_, ?_,
    (restU.mono (by decide)).trans ((restW.mono (by decide)).trans (restT.mono (by decide)))⟩
  · rw [memW] at frameT
    exact Outs.of_outside frameT (by simp)
  · rw [valueT]
    cases c with
    | false =>
      simp only [Bool.not_false, ite_true, memW, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at *
      rw [ite_eq_right (by omega_using [value])]
      omega_using [value]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.toNat_true, Nat.mul_one] at *
      rw [same, ite_eq_left (by omega_using [ub, value])]
  · rw [restT.1 .ebx (by decide), bit]
    cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at value
    · rw [ite_eq_right (by omega_using [value])]; rfl
    · rw [ite_eq_left (by omega_using [ub, value])]; rfl
end VG.Proof.Rsa.X86.Div

end

end

/-! # Native i686 division implements the shared bit-serial step -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Rsa.X86.Div

theorem step_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (step g.n (g.offsets 0) (g.offsets 1) (g.offsets 2) (g.offsets 3)) s fun t =>
      t.gpr .esi = s.gpr .esi - 1 ∧ t.zf = some (s.gpr .esi - 1 == 0) ∧ Context g t ∧
      Outs g.base g.ranges s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      (g.value s.mem 1 < g.value s.mem 2 → g.value s.mem 2 < 2 ^ (32 * g.n) →
        (g.value t.mem 1, g.value t.mem 0) =
          Rsa.divStep (g.value s.mem 2) (32 * g.n) (g.value s.mem 1, g.value s.mem 0)) := by
  have f0 : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := h.fits 1
  have f2 : g.offsets 2 + 4 * (g.n + 1) ≤ g.size := h.fits 2
  have f3 : g.offsets 3 + 4 * (g.n + 1) ≤ g.size := h.fits 3
  have sep01 : g.offsets 0 + 4 * g.n ≤ g.offsets 1 ∨
      g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 1 (by decide)
  have sep03 : g.offsets 0 + 4 * g.n ≤ g.offsets 3 ∨
      g.offsets 3 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 3 (by decide)
  have nowrap := h.workspace.nowrap
  unfold step
  refine WP.seq (WP.mono (shiftArrays_ok h) ?_)
  rintro u ⟨qU, rU, hu, frameU, restU⟩
  have dU := h.divisor_frame frameU
  refine WP.seq (WP.mono (reduce_ok hu.workspace f1 f2 f3
    (h.separate 3 1 (by decide)) (h.separate 3 2 (by decide))) ?_)
  rintro v ⟨frameV, rV, bitV, restV⟩
  change g.value v.mem 1 =
    (if g.value u.mem 1 < g.value u.mem 2 then g.value u.mem 1 else g.value u.mem 1 - g.value u.mem 2) at rV
  change v.gpr .ebx = (if g.value u.mem 1 < g.value u.mem 2 then 0 else 1) at bitV
  have hv := hu.after restV
  have qV : g.value v.mem 0 = g.value u.mem 0 := by
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    apply frameV.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega_arith
    · omega_using [f0, nowrap]
  have bit : (v.gpr .ebx).toNat ≤ 1 := by rw [bitV]; split <;> decide
  refine WP.block_append (WP.mono (insertBit_ok hv.workspace h.positive f0 bit) ?_)
  rintro w ⟨frameW, restW, qW⟩
  change g.value v.mem 0 % 2 = 0 → g.value w.mem 0 = g.value v.mem 0 + (v.gpr .ebx).toNat at qW
  refine WP.mono (count_ok w) ?_
  rintro t ⟨count, zero, memT, restT⟩
  have countV : w.gpr .esi = s.gpr .esi :=
    (restW.1 .esi (by decide)).trans ((restV.1 .esi (by decide)).trans (restU.1 .esi (by decide)))
  have frameWV : Outs g.base g.ranges v.mem w.mem := Outs.of_outside frameW (by simp [Geometry.ranges])
  have frameVU : Outs g.base g.ranges u.mem v.mem := frameV.mono (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [Geometry.ranges])
  refine ⟨by rw [count, countV], by rw [zero, countV], (hv.after restW).after restT,
    ?_, (restU.mono (by decide)).trans ((restV.mono (by decide)).trans
      ((restW.mono (by decide)).trans (restT.mono (by decide)))), ?_⟩
  · rw [memT]
    exact frameU.trans (frameVU.trans frameWV)
  intro remBound divBound
  have rValue := rU (Nat.lt_trans remBound divBound)
  have radix : 2 ^ (32 * g.n) = 2 * 2 ^ (32 * g.n - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := h.positive; omega_using [this]
  have even : g.value v.mem 0 % 2 = 0 := by
    rw [qV, qU, Nat.mod_mod_of_dvd _ ⟨2 ^ (32 * g.n - 1), radix⟩]
    omega_using []
  have remW : g.value w.mem 1 = g.value v.mem 1 := by
    change val32 _ _ _ (g.n + 1) = val32 _ _ _ (g.n + 1)
    exact frameW.val32 (by omega_using [sep01]) (by omega_using [f1, nowrap])
  rw [memT, remW, rV, qW even, bitV, qV, qU, rValue, dU]
  dsimp only [Rsa.divStep]
  split <;> simp
end VG.Proof.Rsa.X86.Div

end

end

/-! # Termination and quotient/remainder correctness of fixed-count division -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/DivInit.lean`, which only this module imported.
section

/-! # Initialize division with a zero remainder and public iteration count -/

section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic

theorem init_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (.seq (zerosW (g.offsets 1) (g.n + 1))
      (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 * g.n)))])) s fun t =>
      g.value t.mem 1 = 0 ∧ g.value t.mem 0 = g.value s.mem 0 ∧
      t.gpr .esi = BitVec.ofNat 32 (32 * g.n) ∧ Context g t ∧
      Outs g.base g.ranges s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := h.fits 1
  have f0 : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
  have sep : g.offsets 0 + 4 * g.n ≤ g.offsets 1 ∨
      g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 1 (by decide)
  have nowrap := h.workspace.nowrap
  refine WP.seq (WP.mono (zerosW_ok h.workspace (by omega) f1) ?_)
  rintro u ⟨frameU, zero, restU⟩
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, ?_, T.gpr, (h.after restU).after T.keeps, ?_,
    (restU.mono (by decide)).trans (T.keeps.mono (by decide))⟩
  · rw [T.mem]; exact zero
  · rw [T.mem]
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    exact frameU.val32 sep (by omega)
  · rw [T.mem]
    exact Outs.of_outside frameU (by simp [Geometry.ranges])
end VG.Proof.Rsa.X86.Div
end

end

@[expose] public section

namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.Impl.Rsa.X86.Div VG.Proof.Mont VG.Proof.Mont.X86
open VG.X86.Wp (ofNat_beq_zero)

structure Invariant (g : Geometry) (s0 : State) (D N i : Nat) (s : State) : Prop where
  ctx : Context g s
  index : i ≤ 32 * g.n
  count : s.gpr .esi = BitVec.ofNat 32 (32 * g.n - i)
  frame : Outs g.base g.ranges s0.mem s.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s0 s
  divisor : g.value s.mem 2 = D
  value : 0 < D → D < 2 ^ (32 * g.n) →
    (g.value s.mem 1, g.value s.mem 0) = divIter D (32 * g.n) i (0, N)

theorem loop_ok {g : Geometry} {s0 s : State} {D N : Nat}
    (h : Invariant g s0 D N 0 s) (boundN : N < 2 ^ (32 * g.n)) :
    WP isa (.loop (step g.n (g.offsets 0) (g.offsets 1) (g.offsets 2) (g.offsets 3)) .ne) s (Invariant g s0 D N (32 * g.n)) := by
  have positive := h.ctx.positive
  have bound := h.ctx.bound
  let I := fun k t => ∃ i, i + k = 32 * g.n ∧ 0 < k ∧ Invariant g s0 D N i t
  refine WP.loop (M := isa) I ?_ (32 * g.n) s ⟨0, by omega_arith, by omega_arith, h⟩
  intro k t pre
  obtain ⟨i, sum, hk, inv⟩ := pre
  refine WP.mono (step_ok inv.ctx) ?_
  rintro u ⟨count, zero, ctxU, frameU, restU, valueU⟩
  have countU : u.gpr .esi = BitVec.ofNat 32 (32 * g.n - (i + 1)) := by
    rw [count, inv.count]
    change BitVec.ofNat 32 (32 * g.n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
    congr 1
  have zeroU : u.zf = some (decide (i + 1 = 32 * g.n)) := by
    rw [zero, inv.count]
    change some (BitVec.ofNat 32 (32 * g.n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [show 32 * g.n - i - 1 = 0 ↔ i + 1 = 32 * g.n by omega_arith]
  have next : Invariant g s0 D N (i + 1) u := by
    refine ⟨ctxU, by omega_arith, countU, inv.frame.trans frameU, inv.rest.trans restU,
      (inv.ctx.divisor_frame frameU).trans inv.divisor, ?_⟩
    intro dPos dBound
    have previous := inv.value dPos dBound
    obtain ⟨q, less, _, _, _⟩ := divIter_inv dPos boundN i (by omega_arith)
    rw [← previous] at less
    rw [inv.divisor] at valueU
    exact (valueU less dBound).trans (by rw [previous]; rfl)
  by_cases done : i + 1 = 32 * g.n
  · left
    refine ⟨?_, done ▸ next⟩
    change u.zf.map not = some false
    simp only [zeroU, done, decide_true, Option.map_some, Bool.not_true]
  · right
    refine ⟨?_, k - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, next⟩
    change u.zf.map not = some true
    simp only [zeroU, done, decide_false, Option.map_some, Bool.not_false]

theorem code_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (code g.n (g.offsets 0) (g.offsets 1) (g.offsets 2) (g.offsets 3)) s fun t =>
      Context g t ∧ Outs g.base g.ranges s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      (0 < g.value s.mem 2 → g.value s.mem 2 < 2 ^ (32 * g.n) →
        g.value t.mem 1 = g.value s.mem 0 % g.value s.mem 2 ∧
        g.value t.mem 0 = g.value s.mem 0 / g.value s.mem 2) := by
  unfold code
  refine WP.seq (WP.mono (init_ok h) ?_)
  rintro u ⟨rU, qU, count, ctxU, frameU, restU⟩
  have boundN : g.value s.mem 0 < 2 ^ (32 * g.n) := val32_lt _ _ _ _
  have inv : Invariant g s (g.value s.mem 2) (g.value s.mem 0) 0 u :=
    ⟨ctxU, by omega_using [], by simpa only [Nat.sub_zero] using count, frameU, restU,
      h.divisor_frame frameU, fun _ _ => by rw [rU, qU]; rfl⟩
  refine WP.mono (loop_ok inv boundN) ?_
  intro t done
  refine ⟨done.ctx, done.frame, done.rest, fun dPos dBound => ?_⟩
  have value := done.value dPos dBound
  rw [divIter_done dPos boundN] at value
  exact Prod.mk.inj value

end VG.Proof.Rsa.X86.Div
