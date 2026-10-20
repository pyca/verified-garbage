module

import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Shift
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power

/-! # The table of a run-time-width windowed exponentiation

Entry `j` of the table lies at `te len c j`, in the wide slots from 20
(`entryPtr_ok`). A selection by pointers set up in registers ends by
reloading `edi` (`selectTail_ok`). The table holds `b^j R mod M` for
`j < 16` (`buildTable_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (adds_ok selectLoop_ok)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- Entry `j` of the table. -/
abbrev te (len : Nat) (c : Ctx) (j : Nat) : Nat := lo len (.slot .wide 20) + j * bc len c

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The table, and slots 0 to 8 of the context, within the working space and apart. -/
theorem In.table_fit (h : In base bytes len args s) (c : Ctx) :
    lo len (.slot c 8) + st len c ≤ lo len (.slot .wide 20) ∧ te len c 16 < bytes := by
  have f27 := h.slot_fit .wide (j := 27) (by decide)
  have hb := bc_half_le' len
  have g := bc_ge h.lower' .wide
  have hst : st len c ≤ st len .wide := by cases c <;> simp only [st] <;> omega
  have hbc : bc len c ≤ bc len .wide := by cases c <;> simp only [st] at hst <;> omega
  have m1 : 9 * st len c ≤ 9 * st len .wide := Nat.mul_le_mul_left 9 hst
  have m2 : 16 * bc len c ≤ 16 * bc len .wide := Nat.mul_le_mul_left 16 hbc
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have e27 : lo len (.slot .wide 27) = numBase + 27 * st len .wide := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have et : te len c 16 = lo len (.slot .wide 20) + 16 * bc len c := rfl
  rw [e27] at f27
  rw [e8, e20, et, e20]
  omega

theorem entryPtr_ok {is : List Instr} {Q : State → Prop} {c : Ctx} {j : Nat} {r t : Reg} (hrt : r ≠ t)
    (hte : t ≠ .edi) (hre : r ≠ .esp) (hts : t ≠ .esp) (hedi : (s.gpr .edi).toNat = base.toNat)
    (hr : readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len)) (hl : len ≤ 1024) (hj : j ≤ 16)
    (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u base r (te len c j) → WP isa (.block is) u Q) :
    WP isa (.block (entryPtr c r j t ++ is)) s Q := by
  have hb := bc_le hl c
  have hw := bc_le hl .wide
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have nb : numBase = 3336 := rfl
  have hlo : lo len (.slot .wide 20) < 2 ^ 32 := by rw [e20, est, nb]; omega
  simp only [entryPtr, List.append_assoc]
  refine ptrTo_ok (x := .slot .wide 20) hrt hte hedi hr hl hlo
    fun u K m p => ?_
  have hr' : readSrc u (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len) := by
    rw [← hr]; simp only [readSrc, State.load32, State.ea, argAt, at_, K.1 .esp (by simp [hre.symm, hts.symm]), m,
      K.2.1, K.2.2]; rfl
  refine widthC_ok (k := 0) (c := c) (r := t) hr' hl fun v Kv mv ev => adds_ok hrt j fun w Kw mw ew => ?_
  refine kk w ((K.trans (Kv.mono (by simp))).trans (Kw.mono (by simp))) (by rw [mw, mv, m]) ?_
  rw [PtrAt, ew, Kv.1 _ (by simp [hrt]), BitVec.toNat_add, p, ev, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := bc len c) (by omega)]
  have : j * bc len c ≤ 16 * 1024 := Nat.mul_le_mul hj hb
  rw [Nat.mod_eq_of_lt (a := j * bc len c) (by omega), Nat.mod_add_mod, Nat.add_assoc]

/-- A selection under the mask `ecx` through `ebp` (source) and `ebx` (destination), `edi` counting
the bytes, then `edi` reloaded: from `s₀`, whose inputs hold, by register changes. -/
theorem selectTail_ok {s₀ : State} (h : In base bytes len args s₀)
    (K₀ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s₀ s) (m₀ : s.mem = s₀.mem)
    {x d N : Nat} {k : Bool} (hN : 0 < N) (hx : x + 4 * N ≤ bytes) (hd : d + 4 * N ≤ bytes)
    (hxd : d + 4 * N ≤ x ∨ x + 4 * N ≤ d) (pe : PtrAt s base .ebp x) (pb : PtrAt s base .ebx d)
    (ce : (s.gpr .edi).toNat = 4 * N) (hk : s.gpr .ecx = cmask k) :
    WP isa (.seq selectLoop (.block restoreEdi)) s fun u =>
      Outside base d (4 * N) s.mem u.mem ∧
      val32 u.mem base d N = (if k then val32 s.mem base x N else val32 s.mem base d N) ∧
      PtrAt u base .ebx (d + 4 * N) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s₀ u := by
  have ws : Ws s base bytes := h.ws.of_keeps K₀
  have hn := h.crt.scratch.nowrap
  refine WP.seq (WP.mono (selectLoop_ok ws (x := x) (d := d) (N := N) k hN hx hd hxd pe pb ce hk)
    fun t ⟨O, V, pbt, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s₀ t := K₀.trans (Kt.mono (by decide))
  have Oall : Outside base 0 bytes s₀.mem t.mem := by rw [← m₀]; exact O.mono (Nat.zero_le _) (by omega)
  refine wp_movS ((h.crt.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  have ed : t₁.gpr .edi = s₀.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  refine ⟨by rw [u₁.mem]; exact O, by rw [u₁.mem]; exact V, by rw [PtrAt, u₁.other _ (by decide)]; exact pbt,
    PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) ?_ ed⟩
  exact (Kall.trans (u₁.keeps.mono (by decide))).mono (by decide)

end

end VG.Proof.Bignum.X86.CrtRt
