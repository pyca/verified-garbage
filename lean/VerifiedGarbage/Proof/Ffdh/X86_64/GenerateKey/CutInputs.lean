module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Bignum.Layout
import Mathlib.Algebra.GroupWithZero.Nat
import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound

/-! ### `Ffdh.X86_64.GenerateKey.Scan`, which this module and modules that import it used -/

section

/-! # FFDH on x86-64: the bound scan preserves the key-generation inputs -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Domain and random input with initialized y, before scalar sampling. -/
structure Inputs (p : GkP) (rb : List Byte) (s : State) : Prop where
  base : Base p rb s
  rdi : s.gpr .rdi = p.B
  y : Src s p.B p.Z p.yp (List.replicate p.k 0)
  g : word s.mem p.B (8 * sG) = off p.dp p.k
  q : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)

/-- Header changes made while scanning or masking the bound. -/
def scanRanges : List (Nat × Nat) := [(8 * sEp, 8), (8 * sEl, 8), (8 * sMsk, 8)]

theorem scanRanges_end : ∀ r ∈ scanRanges, r.1 + r.2 ≤ 256 := by
  simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> decide

theorem Inputs.keep {p : GkP} {rb : List Byte} {s t : State} {rs : List Reg} (h : Inputs p rb s)
    (hf : Frm p.B scanRanges s.mem t.mem) (k : Keep rs s t) (hdi : .rdi ∉ rs) : Inputs p rb t := by
  have hZ := h.base.hZ
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [sEp, sEl, sMsk, sFn] <;> omega_using [hZ])
  have hh : ∀ i < 32, i ≠ sEp → i ≠ sEl → i ≠ sMsk →
      word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi he hl hm =>
    hf.word_eq (by
      simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> simp only <;> omega_arith) (by omega_using [hi])
  refine ⟨h.base.keep hi k ?_, (k.gpr hdi).trans h.rdi, h.y.congrK hi k,
    (hh _ (by decide) (by decide) (by decide) (by decide)).trans h.g,
    (hh _ (by decide) (by decide) (by decide) (by decide)).trans h.q⟩
  intro e he
  simp only [GkP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! ### `Ffdh.X86_64.GenerateKey.Finish`, which the modules that import this one used -/

section

/-! # FFDH on x86-64: sampled inputs enter the proven private-scalar core -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/CutFinish.lean`, which only this module imported.
section

/-! # FFDH on x86-64: retain the scalar's significant slice -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem cutFinish_ok {s : State} {B xp : Addr} {Z ld n : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z)
    (hX : word s.mem B (8 * sX) = xp) (hN : word s.mem B (8 * sEl) = BitVec.ofNat 64 n)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 ld) :
    WP isa (.block cutFinish) s fun t =>
      word t.mem B (8 * sX) = off xp ld ∧ word t.mem B (8 * sXl) = BitVec.ofNat 64 n ∧
      Frm B [(8 * sX, 8), (8 * sXl, 8)] s.mem t.mem ∧ Keep [.rax] s t := by
  let m₁ := s.mem.writeW (off B (8 * sX)) (off xp ld)
  let m := m₁.writeW (off B (8 * sXl)) (BitVec.ofNat 64 n)
  have ox := writeW_outside (d := 8 * sX) s.mem B (off xp ld) (by decide)
  have on := writeW_outside (d := 8 * sXl) m₁ B (BitVec.ofNat 64 n) (by decide)
  have hN' : word m₁ B (8 * sEl) = BitVec.ofNat 64 n := by
    rw [ox.word (by decide) (by decide)]
    exact hN
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = m) (by
    unfold cutFinish
    xrun [State.ea, hdr, hdi, hdrOff, h8, hX, hN',
      hs.ld (d := 8 * sX) (by change 168 ≤ Z; omega),
      hs.st (d := 8 * sX) (by change 168 ≤ Z; omega),
      hs.ld (d := 8 * sEl) (by change 200 ≤ Z; omega),
      hs.st (d := 8 * sXl) (by change 176 ≤ Z; omega), m, m₁, off]) rfl)
    fun t ⟨hm, k⟩ => ?_
  refine ⟨?_, ?_, ?_, k⟩
  · rw [hm, on.word (by decide) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro a ha
    rw [hm]
    exact (on a (ha (8 * sXl, 8) (by simp))).trans (ox a (ha (8 * sX, 8) (by simp)))

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The private-key core sees the significant slice of x and the initialized y. -/
theorem finish_base {p : GkP} {rb : List Byte} {s : State} (h : Inputs p rb s)
    (hx : Src s p.B p.Z p.xp (p.cut rb)) (hm : p.mv = true)
    (hn : word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n) (h8 : s.gpr .r8 = BitVec.ofNat 64 p.ld) :
    WP isa (.block cutFinish) s fun t =>
      CheckPrivate.Base p.kp (p.xb rb) t ∧ t.gpr .rdi = p.B ∧
      word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧
      InScr p.B p.Z s.mem t.mem ∧ Keep [.rax] s t := by
  have hk := h.base.k1
  have hl := h.base.ld_lt
  have hZ := h.base.hZ
  refine WP.mono (cutFinish_ok h.base.scr h.rdi (by omega_using [hZ])
    (h.base.hdr (sX, p.xp) (by simp [GkP.headers])) hn h8)
    fun t ⟨hX, hXl, hf, k⟩ => ?_
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [sX, sXl, sFn] <;> omega_using [hZ])
  have hh : ∀ i < 32, i ≠ sX → i ≠ sXl → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hx hxl => hf.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> omega_arith) (by omega_using [hi])
  refine ⟨⟨h.base.k1, h.base.k2, h.base.dl, h.base.doml, List.length_replicate,
    h.base.xb_length, by change 1 ≤ p.k - p.ld; omega_using [hl], by change p.k - p.ld ≤ p.k; omega_using [],
    h.base.hZ, h.base.scr.congr k.2.2, h.base.dom.congrK hi k,
    (hx.drop p.ld).congrK hi k, h.y.congrK hi k, ?_, ?_⟩,
    (k.gpr (by decide)).trans h.rdi,
    (hh _ (by decide) (by decide) (by decide)).trans h.g,
    (hh _ (by decide) (by decide) (by decide)).trans h.q,
    fun i hi => hh i (by omega_using [hi]) (by unfold sX sFn; omega_using [hi]) (by unfold sXl sFn; omega_using [hi]), hi, k⟩
  · intro e he
    simp only [CheckPrivate.KpP.headers, GkP.kp, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hh sDom (by decide) (by decide) (by decide)).trans
        (h.base.hdr (sDom, p.dp) (by simp [GkP.headers]))
    · exact (hh sDomLen (by decide) (by decide) (by decide)).trans
        (h.base.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [GkP.headers]))
    · exact (hh sK (by decide) (by decide) (by decide)).trans
        (h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers]))
    · exact (hh sY (by decide) (by decide) (by decide)).trans
        (h.base.hdr (sY, p.yp) (by simp [GkP.headers]))
    · exact hX
    · exact hXl
  · change Spec.Ffdh.privateValid p.params (Spec.Rsa.os2ip (p.xb rb)) = p.sv
    rw [h.base.sample_value hm]
    exact h.base.valid

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! ### `Ffdh.X86_64.GenerateKey.CutSetup`, which only this module used -/

section

/-! # FFDH on x86-64: initialize the scalar-cut loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The public registers at the start of the cut loop. -/
def CutRegs (p : GkP) (s : State) : Prop :=
  s.gpr .r10 = p.rp ∧ s.gpr .r11 = p.xp ∧ s.gpr .r9 = p.msk ∧
    s.gpr .r8 = BitVec.ofNat 64 p.ld ∧ s.gpr .rcx = 0 ∧ s.gpr .r14 = BitVec.ofNat 64 p.k

theorem cutSetup_ok {p : GkP} {rb : List Byte} {s : State} (h : Inputs p rb s)
    (hn : word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n)
    (hm : word s.mem p.B (8 * sMsk) = p.msk) :
    WP isa (.block cutSetup) s fun t => (CutRegs p t ∧ t.mem = s.mem) ∧
      Keep [.r10, .r11, .r9, .r8, .rcx, .r14] s t := by
  have hk := h.base.k2
  have hl := h.base.ld_lt
  have hZ := h.base.hZ
  have hsub : BitVec.ofNat 64 p.k - BitVec.ofNat 64 p.n = BitVec.ofNat 64 p.ld := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    change _ = p.ld % 2 ^ 64
    have hn : p.n = p.k - p.ld := rfl
    omega_using [hl, hn]
  refine WP.keep _ ?_ rfl
  unfold cutSetup
  xrun [CutRegs, State.ea, hdr, h.rdi, hdrOff,
    h.base.scr.ld (d := 8 * sRand) (by change 208 ≤ p.Z; omega_using [hZ]),
    h.base.scr.ld (d := 8 * sX) (by change 168 ≤ p.Z; omega_using [hZ]),
    h.base.scr.ld (d := 8 * sMsk) (by change 256 ≤ p.Z; omega_using [hZ]),
    h.base.scr.ld (d := 8 * sK) (by change 152 ≤ p.Z; omega_using [hZ]),
    h.base.scr.ld (d := 8 * sEl) (by change 200 ≤ p.Z; omega_using [hZ]),
    h.base.hdr (sRand, p.rp) (by simp [GkP.headers]),
    h.base.hdr (sX, p.xp) (by simp [GkP.headers]),
    h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers]), hn, hm, hsub]

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! ### `Ffdh.X86_64.GenerateKey.Cut`, which only this module used -/

section

/-! # FFDH on x86-64: cutting random octets to the public scalar bound -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem cmov_reg (s : State) (cc : Cond) (d r : Reg) :
    execCmov cc d (.reg r) s = (eval cc s).map
      (fun c => s.setReg d (if c then s.gpr r else s.gpr d)) := by
  simp only [execCmov, readSrc, Option.bind_some]
  congr 1
  funext c
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    symm
    simp only [State.setReg]
    congr 1
    funext r'
    split <;> simp_all
  · rfl

/-- One scalar byte is written without branching on its value. -/
theorem cutBody_ok {s : State} {rp xp : Addr} {j ld k : Nat} {b : Byte} {msk : BitVec 64}
    (hj : j < k) (hk : k < 2 ^ 31) (hld : ld < k)
    (hrp : s.gpr .r10 = off rp j) (hxp : s.gpr .r11 = off xp j)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 j) (h8 : s.gpr .r8 = BitVec.ofNat 64 ld)
    (h9 : s.gpr .r9 = msk) (h14 : s.gpr .r14 = BitVec.ofNat 64 (k - j))
    (hrd : InRegions (s.rd ++ s.wr) (off rp j) 1) (hwr : InRegions s.wr (off xp j) 1)
    (hb : s.mem (off rp j) = b) :
    WP isa (.block cutBody) s fun t =>
      (t.mem = s.mem.writeW (off xp j)
        (if j < ld then (0 : Byte) else if j = ld then b &&& msk.setWidth 8 else b) ∧
      t.gpr .r10 = off rp (j + 1) ∧ t.gpr .r11 = off xp (j + 1) ∧
      t.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧ t.gpr .r14 = BitVec.ofNat 64 (k - (j + 1)) ∧
      t.zf = some (decide (j + 1 = k))) ∧ Keep [.rax, .rdx, .rbx, .r10, .r11, .rcx, .r14] s t := by
  have hj64 : j < 2 ^ 64 := by omega_using [hj, hk]
  have hld64 : ld < 2 ^ 64 := by omega_using [hk, hld]
  have hcmp : decide ((BitVec.ofNat 64 j).toNat < (BitVec.ofNat 64 ld).toNat) = decide (j < ld) := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt hld64]
  have heq : (BitVec.ofNat 64 j == BitVec.ofNat 64 ld) = decide (j = ld) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt hld64] at this
      exact this
    · exact congrArg (BitVec.ofNat 64)
  refine WP.keep _ ?_ rfl
  unfold cutBody
  xrun [State.ea, at0, hrp, hxp, hcx, h8, h9, h14,
    show off rp j + BitVec.ofInt 64 0 = off rp j by simp,
    show off xp j + BitVec.ofInt 64 0 = off xp j by simp, hrd, hwr, hb, hcmp, sub_beq_zero, heq, cmov_reg, eval]
  refine ⟨?_, ?_, ?_, ofNat_add_one j, ?_, ?_⟩
  · apply congrArg (s.mem.writeW (off xp j))
    simp only [decide_eq_true_eq]
    by_cases he : j = ld
    · simp only [ite_eq_left he, ite_eq_right (show ¬ j < ld by omega_using [he])]
      simp [BitVec.setWidth_and]
    · simp only [ite_eq_right he]
      by_cases hl : j < ld <;> simp [hl, BitVec.setWidth_and]
      exact BitVec.and_allOnes
  · simp only [off, BitVec.add_assoc, ofNat_add_one]
  · simp only [off, BitVec.add_assoc, ofNat_add_one]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega_using [hj]
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl] at this
      omega_using [hk, this]
    · intro h
      rw [show k - j = 1 by omega_using [h]]
      rfl

/-- The loop invariant records the written prefix and preserves every other byte. -/
structure CutInv (s₀ : State) (rp xp : Addr) (rb : List Byte) (ld : Nat)
    (msk : BitVec 64) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .rdx, .rbx, .r10, .r11, .rcx, .r14] s₀ t
  ptrR : t.gpr .r10 = off rp j
  ptrX : t.gpr .r11 = off xp j
  cx : t.gpr .rcx = BitVec.ofNat 64 j
  count : t.gpr .r14 = BitVec.ofNat 64 (rb.length - j)
  bytes : ∀ i < j, t.mem (off xp i) =
    if i < ld then 0 else if i = ld then rb.getD i 0 &&& msk.setWidth 8 else rb.getD i 0
  frame : ∀ a, (∀ i < j, a ≠ off xp i) → t.mem a = s₀.mem a

/-- Extend the written prefix by one byte, leaving unread randomness intact. -/
theorem cutStep_ok {s₀ t : State} {rp xp : Addr} {rb : List Byte} {ld j : Nat} {msk : BitVec 64}
    (hk : rb.length < 2 ^ 31) (hj : j < rb.length) (hld : ld < rb.length)
    (h8 : s₀.gpr .r8 = BitVec.ofNat 64 ld) (h9 : s₀.gpr .r9 = msk)
    (hrd : ∀ i < rb.length, InRegions (s₀.rd ++ s₀.wr) (off rp i) 1)
    (hwr : ∀ i < rb.length, InRegions s₀.wr (off xp i) 1)
    (hb : ∀ i < rb.length, s₀.mem (off rp i) = rb.getD i 0)
    (hsep : ∀ i < rb.length, ∀ l < rb.length, off rp i ≠ off xp l)
    (h : CutInv s₀ rp xp rb ld msk j t) :
    WP isa (.block cutBody) t fun u =>
      u.zf = some (decide (j + 1 = rb.length)) ∧ CutInv s₀ rp xp rb ld msk (j + 1) u := by
  have hrd' : InRegions (t.rd ++ t.wr) (off rp j) 1 := by
    rw [h.keep.2.1, h.keep.2.2]; exact hrd j hj
  have hwr' : InRegions t.wr (off xp j) 1 := by rw [h.keep.2.2]; exact hwr j hj
  have hb' : t.mem (off rp j) = rb.getD j 0 := by
    rw [h.frame _ (fun i hi => hsep j hj i (by omega_using [hj, hi]))]; exact hb j hj
  refine WP.mono (cutBody_ok hj hk hld h.ptrR h.ptrX h.cx
    ((h.keep.gpr (by decide)).trans h8) ((h.keep.gpr (by decide)).trans h9)
    h.count hrd' hwr' hb') fun u ⟨⟨hm, hrp, hxp, hcx, hcount, hz⟩, k⟩ => ?_
  refine ⟨hz, ⟨keep_trans h.keep k, hrp, hxp, hcx, hcount, ?_, ?_⟩⟩
  · intro i hi
    rw [hm, WriteBytes.writeW8_apply]
    by_cases he : i = j
    · subst he
      rw [ite_eq_left rfl]
    · rw [ite_eq_right (out_ne (by omega_using [hk, hj, hi]) (by omega_using [hk, hj]) he)]
      exact h.bytes i (by omega_using [hi, he])
  · intro a ha
    rw [hm, WriteBytes.writeW8_apply, ite_eq_right (ha j (by omega_using []))]
    exact h.frame a (fun i hi => ha i (by omega_using [hi]))

/-- Cut all random octets with a fixed trip count determined by the public width. -/
theorem cut_ok {s : State} {rp xp : Addr} {rb : List Byte} {ld : Nat} {msk : BitVec 64}
    (hk1 : 1 ≤ rb.length) (hk : rb.length < 2 ^ 31) (hld : ld < rb.length)
    (hrp : s.gpr .r10 = rp) (hxp : s.gpr .r11 = xp) (hcx : s.gpr .rcx = 0)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 ld) (h9 : s.gpr .r9 = msk)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 rb.length)
    (hrd : ∀ i < rb.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < rb.length, InRegions s.wr (off xp i) 1)
    (hb : ∀ i < rb.length, s.mem (off rp i) = rb.getD i 0)
    (hsep : ∀ i < rb.length, ∀ l < rb.length, off rp i ≠ off xp l) :
    WP isa (.loop (.block cutBody) .ne) s (CutInv s rp xp rb ld msk rb.length) :=
  wp_upto (a := 0) (by omega_using [hk1]) (CutInv s rp xp rb ld msk)
    (fun j _ hj t ht => cutStep_ok hk hj hld h8 h9 hrd hwr hb hsep ht)
    (fun _ h => h) ⟨Keep.refl _ _, by rw [hrp]; simp, by rw [hxp]; simp,
      hcx, by simpa only [Nat.sub_zero] using h14, fun i hi => by omega, fun _ _ => rfl⟩

/-- Writing the scalar preserves every byte of the scratch workspace. -/
theorem CutInv.outside {s t : State} {B rp xp : Addr} {Z : Nat} {rb : List Byte}
    {ld : Nat} {msk : BitVec 64} (h : CutInv s rp xp rb ld msk rb.length t)
    (ho : VG.Proof.Rsa.X86_64.OutOk s B Z xp rb.length) :
    Outside B Z (2 ^ 64 - Z) s.mem t.mem := by
  intro a ha
  have ha64 : ofs B a < 2 ^ 64 := (a - B).isLt
  apply h.frame
  intro i hi he
  have hh : Z ≤ ofs B (off xp i) := ho.sep i hi
  rw [← he] at hh
  omega_using [ha, ha64, hh]

/-- The cut loop preserves a disjoint input, including a previously zeroed y. -/
theorem CutInv.src_keep {s t : State} {B rp xp ip : Addr} {Z : Nat} {rb bs : List Byte}
    {ld : Nat} {msk : BitVec 64} (h : CutInv s rp xp rb ld msk rb.length t)
    (hi : Src s B Z ip bs) (ha : VG.Proof.Rsa.X86_64.Apart xp rb.length ip bs.length) :
    Src t B Z ip bs :=
  ⟨fun i hl => by rw [h.keep.2.1, h.keep.2.2]; exact hi.rd i hl,
    fun i hl => by rw [h.frame _ (fun j hj => Ne.symm (ha j hj i hl))]; exact hi.val i hl, hi.out⟩

/-- The full scalar output is exactly `KeyScalar.cut`, and can be reused as an input. -/
theorem CutInv.src {s t : State} {B rp xp : Addr} {Z : Nat} {rb : List Byte}
    {ld : Nat} {msk : BitVec 64} (h : CutInv s rp xp rb ld msk rb.length t)
    (hld : ld < rb.length) (ho : VG.Proof.Rsa.X86_64.OutOk s B Z xp rb.length) :
    Src t B Z xp (KeyScalar.cut rb ld (msk.setWidth 8)) := by
  have hl := KeyScalar.cut_length (msk.setWidth 8) hld
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨r, hr, hc⟩ := ho.wr i (by rwa [hl] at hi)
    exact ⟨r, List.mem_append_right _ (by rw [h.keep.2.2]; exact hr), hc⟩
  · intro i hi
    have hi' : i < rb.length := by rwa [hl] at hi
    rw [h.bytes i hi', KeyScalar.cut_get _ hld hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  · intro i hi
    exact ho.sep i (by rwa [hl] at hi)

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end


/-! # FFDH on x86-64: preserve domain and initialized y while sampling x -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Cutting x preserves all other inputs and every scratch word. -/
theorem Inputs.cut_keep {p : GkP} {rb : List Byte} {s t : State} (h : Inputs p rb s)
    (hc : CutInv s p.rp p.xp rb p.ld p.msk rb.length t) :
    Inputs p rb t ∧ Src t p.B p.Z p.xp (p.cut rb) ∧
      (∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d) := by
  have ho : VG.Proof.Rsa.X86_64.OutOk s p.B p.Z p.xp rb.length := by rw [h.base.rl]; exact h.base.x
  have hout := hc.outside ho
  have hh : ∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d :=
    fun d hd => hout.word (Or.inl hd) (by have := h.base.scr.nowrap; omega_using [hd, this])
  have hg : Src t p.B p.Z p.dp p.dom := hc.src_keep h.base.dom (by
    rw [h.base.rl, h.base.doml]; exact h.base.xd)
  have hr : Src t p.B p.Z p.rp rb := hc.src_keep h.base.rand (by
    rw [h.base.rl]; exact h.base.xr)
  have hy : Src t p.B p.Z p.yp (List.replicate p.k 0) := hc.src_keep h.y (by
    rw [h.base.rl, List.length_replicate]; exact h.base.xy)
  have hZ := h.base.hZ
  have hbase : Base p rb t := by
    refine ⟨h.base.k1, h.base.k2, h.base.dl, h.base.doml, h.base.rl, h.base.hZ,
      h.base.scr.congr hc.keep.2.2, hg, hr,
      ⟨fun i hi => by rw [hc.keep.2.2]; exact h.base.x.wr i hi, h.base.x.sep⟩,
      ⟨fun i hi => by rw [hc.keep.2.2]; exact h.base.y.wr i hi, h.base.y.sep⟩,
      h.base.xy, h.base.xd, h.base.xr, h.base.yd, h.base.yr, ?_, h.base.valid, h.base.ldk, h.base.cutv⟩
    intro e he
    rw [hh _ (by
      simp only [GkP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sDom, sDomLen, sK, sY, sX, sRand, sFn] <;> omega_using [hZ])]
    exact h.base.hdr e he
  refine ⟨⟨hbase, (hc.keep.gpr (by decide)).trans h.rdi, hy, ?_, ?_⟩,
    hc.src (by rw [h.base.rl]; exact h.base.ld_lt) ho, hh⟩
  · rw [hh _ (by change 224 ≤ p.Z; omega_using [hZ])]; exact h.g
  · rw [hh _ (by change 232 ≤ p.Z; omega_using [hZ])]; exact h.q

/-- The full cut loop, ready to select the public exponent slice. -/
theorem cut_inputs {p : GkP} {rb : List Byte} {s : State} (h : Inputs p rb s) (hr : CutRegs p s) :
    WP isa (.loop (.block cutBody) .ne) s fun t =>
      Inputs p rb t ∧ Src t p.B p.Z p.xp (p.cut rb) ∧
      (∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d) ∧
      t.gpr .r8 = BitVec.ofNat 64 p.ld ∧ RunFrame p s.mem t.mem ∧ Keep [.rax, .rdx, .rbx, .r10, .r11, .rcx, .r14] s t := by
  obtain ⟨hrp, hxp, hm, hld, hcx, h14⟩ := hr
  have hk := h.base.k1
  have hk' := h.base.k2
  refine WP.mono (cut_ok (rb := rb) (by rw [h.base.rl]; omega_using [hk]) (by rw [h.base.rl]; omega_using [hk'])
    (by rw [h.base.rl]; exact h.base.ld_lt) hrp hxp hcx hld hm (by rw [h.base.rl]; exact h14)
    h.base.rand.rd (fun i hi => h.base.x.wr i (by rwa [h.base.rl] at hi))
    (fun i hi => by simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] using h.base.rand.val i hi)
    (fun i hi j hj => Ne.symm (h.base.xr j (by rwa [h.base.rl] at hj) i (by rwa [h.base.rl] at hi))))
    fun t hc => ?_
  obtain ⟨ht, hx, hh⟩ := h.cut_keep hc
  refine ⟨ht, hx, hh, (hc.keep.gpr (by decide)).trans hld, ?_, hc.keep⟩
  exact RunFrame.of_x (fun a hx => hc.frame a (fun i hi => hx i (by rwa [h.base.rl] at hi)))

end VG.Proof.Ffdh.X86_64.GenerateKey
