module

public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.OutputCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.OutputCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Arithmetic
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Words
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Arithmetic
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Tactic.Push
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
meta import Mathlib.Algebra.GroupWithZero.Nat
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.Words
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.Layout

/-! ### `Ffdh.X86_64.GenerateKey.PublicOutputCT`, which the modules that import this one used -/

section

/-! ### `Ffdh.X86_64.GenerateKey.Outputs`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.GenerateKey.MaskOutput`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.GenerateKey.MaskSetup`, which this module and modules that import it used -/

section

/-! # FFDH on x86-64: recover the scalar output's full-width pointer -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem maskSetup_ok {s : State} {B xp : Addr} {Z k ld : Nat} {c : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z) (hk : k < 2 ^ 31) (hld : ld < k)
    (hX : word s.mem B (8 * sX) = off xp ld)
    (hL : word s.mem B (8 * sXl) = BitVec.ofNat 64 (k - ld))
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hax : s.gpr .rax = BitVec.ofNat 64 c.toNat) :
    WP isa (.block maskSetup) s fun t =>
      (t.gpr .r11 = xp ∧ t.gpr .r15 = mask c ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧
      word t.mem B (8 * sF) = BitVec.ofNat 64 c.toNat ∧ Frm B [(8 * sF, 8)] s.mem t.mem) ∧
      Keep [.r15, .r11, .rdx, .rcx] s t := by
  let m := s.mem.writeW (off B (8 * sF)) (BitVec.ofNat 64 c.toNat)
  have hf := writeW_outside (d := 8 * sF) s.mem B (BitVec.ofNat 64 c.toNat) (by decide)
  have hh : ∀ i < sF, word m B (8 * i) = word s.mem B (8 * i) :=
    fun i hi => hf.word (Or.inl (by omega)) (by unfold sF sFn at hi; omega)
  have hX' : word m B (8 * sX) = off xp ld := (hh _ (by decide)).trans hX
  have hL' : word m B (8 * sXl) = BitVec.ofNat 64 (k - ld) := (hh _ (by decide)).trans hL
  have hK' : word m B (8 * sK) = BitVec.ofNat 64 k := (hh _ (by decide)).trans hK
  have hsub : BitVec.ofNat 64 k - BitVec.ofNat 64 (k - ld) = BitVec.ofNat 64 ld := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hmask : 0#64 - BitVec.ofNat 64 c.toNat = mask c := by cases c <;> rfl
  refine WP.mono (WP.keep [.r15, .r11, .rdx, .rcx] (Q := fun t =>
      t.gpr .r11 = xp ∧ t.gpr .r15 = mask c ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧ t.mem = m) (by
    unfold maskSetup
    xrun [State.ea, hdr, hdi, hdrOff, hax, hX', hL', hK', hsub, hmask,
      show (BitVec.setWidth 64 (0 : BitVec 32)) = 0#64 from rfl,
      hs.st (d := 8 * sF) (by change 248 ≤ Z; omega),
      hs.ld (d := 8 * sX) (by change 168 ≤ Z; omega),
      hs.ld (d := 8 * sXl) (by change 176 ≤ Z; omega),
      hs.ld (d := 8 * sK) (by change 152 ≤ Z; omega), m, off, BitVec.add_sub_cancel]) rfl)
    fun t ⟨⟨hp, hm, hcx, hmem⟩, kt⟩ => ?_
  exact ⟨⟨hp, hm, hcx, by rw [hmem]; exact word_writeW_self _ _ _ _,
    by rw [hmem]; exact Frm.of_outside hf (by simp)⟩, kt⟩

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! # FFDH on x86-64: the complete masked scalar store -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Mask.lean`, which only this module imported.
section

/-! # FFDH on x86-64: mask a rejected scalar's output -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The masked prefix and unchanged remainder of a scalar buffer. -/
structure MaskInv (s₀ : State) (op : Addr) (len : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r11, .rcx] s₀ t
  ptr : t.gpr .r11 = off op j
  count : t.gpr .rcx = BitVec.ofNat 64 (len - j)
  bytes : ∀ i < j, t.mem (off op i) = if c then s₀.mem (off op i) else 0
  frame : ∀ a, (∀ i < j, a ≠ off op i) → t.mem a = s₀.mem a

theorem maskBody_ok {s : State} {op : Addr} {j len : Nat} {c : Bool}
    (hj : j < len) (hl : len < 2 ^ 31) (hp : s.gpr .r11 = off op j)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (len - j)) (hm : s.gpr .r15 = mask c)
    (hwr : InRegions s.wr (off op j) 1) :
    WP isa (.block maskBody) s fun t =>
      (t.mem = s.mem.writeW (off op j) (if c then s.mem (off op j) else (0 : Byte)) ∧
      t.gpr .r11 = off op (j + 1) ∧ t.gpr .rcx = BitVec.ofNat 64 (len - (j + 1)) ∧
      t.zf = some (decide (j + 1 = len))) ∧ Keep [.rax, .r11, .rcx] s t := by
  have hrd : InRegions (s.rd ++ s.wr) (off op j) 1 :=
    let ⟨r, hr, hc⟩ := hwr; ⟨r, List.mem_append_right _ hr, hc⟩
  have hmByte : ((s.mem (off op j)).setWidth 64 &&& mask c).setWidth 8 =
      if c then s.mem (off op j) else 0 := by
    cases c <;> simp [mask, BitVec.setWidth_and]
    exact BitVec.and_allOnes
  refine WP.keep _ ?_ rfl
  unfold maskBody
  xrun [State.ea, at0, hp, hcx, hm,
    show off op j + BitVec.ofInt 64 0 = off op j by simp, hrd, hwr, hmByte,
    ofNat64_pred (show 1 ≤ len - j by omega) (by omega),
    ofNat64_beq_zero (show len - j - 1 < 2 ^ 64 by omega)]
  refine ⟨?_, ?_, ?_⟩
  · simp only [off, BitVec.add_assoc, ofNat_add_one]
  · rw [show len - j - 1 = len - (j + 1) by omega]
  · exact decide_eq_decide.mpr (by omega)

theorem maskStep_ok {s₀ t : State} {op : Addr} {j len : Nat} {c : Bool}
    (hj : j < len) (hl : len < 2 ^ 31) (hm : s₀.gpr .r15 = mask c)
    (hwr : ∀ i < len, InRegions s₀.wr (off op i) 1) (h : MaskInv s₀ op len c j t) :
    WP isa (.block maskBody) t fun u =>
      u.zf = some (decide (j + 1 = len)) ∧ MaskInv s₀ op len c (j + 1) u := by
  refine WP.mono (maskBody_ok hj hl h.ptr h.count ((h.keep.gpr (by decide)).trans hm)
    (by rw [h.keep.2.2]; exact hwr j hj)) fun u ⟨⟨hmem, hp, hcount, hz⟩, k⟩ => ?_
  refine ⟨hz, ⟨keep_trans h.keep k, hp, hcount, ?_, ?_⟩⟩
  · intro i hi
    rw [hmem, WriteBytes.writeW8_apply]
    by_cases he : i = j
    · subst he
      rw [ite_eq_left rfl, h.frame _ (fun i hi => out_ne (by omega) (by omega) (by omega))]
    · rw [ite_eq_right (out_ne (by omega) (by omega) he)]
      exact h.bytes i (by omega)
  · intro a ha
    rw [hmem, WriteBytes.writeW8_apply, ite_eq_right (ha j (by omega))]
    exact h.frame a (fun i hi => ha i (by omega))

/-- The mask loop writes every byte on both success and failure. -/
theorem mask_ok {s : State} {op : Addr} {len : Nat} {c : Bool}
    (hl1 : 1 ≤ len) (hl : len < 2 ^ 31) (hp : s.gpr .r11 = op)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 len) (hm : s.gpr .r15 = mask c)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1) :
    WP isa (.loop (.block maskBody) .ne) s (MaskInv s op len c len) :=
  wp_upto (a := 0) (by omega) (MaskInv s op len c)
    (fun j _ hj t ht => maskStep_ok hj hl hm hwr ht) (fun _ h => h)
    ⟨Keep.refl _ _, by rw [hp]; simp, by rw [hcx, Nat.sub_zero], fun i hi => by omega, fun _ _ => rfl⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem maskX_ok {s : State} {B xp : Addr} {Z k ld : Nat} {c : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z) (hk : k < 2 ^ 31) (hld : ld < k)
    (hX : word s.mem B (8 * sX) = off xp ld)
    (hL : word s.mem B (8 * sXl) = BitVec.ofNat 64 (k - ld))
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hax : s.gpr .rax = BitVec.ofNat 64 c.toNat)
    (ho : VG.Proof.Rsa.X86_64.OutOk s B Z xp k) :
    WP isa maskX s fun t =>
      (∀ i < k, t.mem (off xp i) = if c then s.mem (off xp i) else 0) ∧
      word t.mem B (8 * sF) = BitVec.ofNat 64 c.toNat ∧ t.gpr .rdi = B ∧
      (∀ a, Z ≤ ofs B a → (∀ i < k, a ≠ off xp i) → t.mem a = s.mem a) ∧
      (∀ i < 6, word t.mem B (8 * i) = word s.mem B (8 * i)) ∧ Keep mmRegs s t := by
  unfold maskX
  refine WP.seq (WP.mono (maskSetup_ok hs hdi hZ hk hld hX hL hK hax)
    fun u ⟨⟨hp, hm, hcx, hF, hf⟩, k₁⟩ => ?_)
  have hi : InScr B Z s.mem u.mem := InScr.of_frm hf (by
    simp only [List.mem_singleton]; rintro r rfl; change 248 ≤ Z; omega_using [hZ])
  refine WP.mono (mask_ok (by omega_using [hld]) hk hp hcx hm (fun i hi => by rw [k₁.2.2]; exact ho.wr i hi))
    fun t hc => ?_
  have hout : Outside B Z (2 ^ 64 - Z) u.mem t.mem := by
    intro a ha
    have ha64 : ofs B a < 2 ^ 64 := (a - B).isLt
    apply hc.frame
    intro i hi he
    have hh : Z ≤ ofs B (off xp i) := ho.sep i hi
    rw [← he] at hh
    omega_using [hdi, hZ, hk, hld, hX, hL, hK, hax, hp, hm, hcx, hF, ha, ha64, hi, hh]
  have hh : ∀ d, d + 8 ≤ Z → word t.mem B d = word u.mem B d :=
    fun d hd => hout.word (Or.inl hd) (by have := hs.nowrap; omega_using [hd, this])
  refine ⟨?_, by rw [hh _ (by change 248 ≤ Z; omega_using [hZ])]; exact hF,
    ((k₁.trans hc.keep).gpr (by decide)).trans hdi, ?_, ?_, (k₁.trans hc.keep).mono (by decide)⟩
  · intro i hi'
    rw [hc.bytes i hi', hi _ (ho.sep i hi')]
  · intro a ha hne
    rw [hc.frame a hne, hi a ha]
  · intro i hi'
    rw [hh _ (by omega_using [hZ, hi']), hf.word_eq (by
      simp only [List.mem_singleton]; rintro r rfl
      exact Or.inl (by unfold sF sFn; omega_using [hi'])) (by omega_using [hi'])]

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! ### `Ffdh.X86_64.GenerateKey.ArithmeticBridge`, which this module and modules that import it used -/

section

/-! # FFDH key generation on x86-64: a generator power uses exchange's output proof -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Bridge.lean`, which only this module imported.
section

/-! # FFDH key generation on x86-64: reuse the exchange output workspace -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Only the outer header's public-value and output pointers change. -/
theorem bridge_ok {s : State} {B yp gp : Addr} {Z o w : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w w mi)
    (hY : word s.mem B (8 * sY) = yp) (hG : word s.mem B (8 * sG) = gp) :
    WP isa (.block bridge) s fun t =>
      word t.mem B (8 * VG.Impl.Ffdh.X86_64.Domain.sOut) = yp ∧
      word t.mem B (8 * sY) = gp ∧
      Frm B [(8 * VG.Impl.Ffdh.X86_64.Domain.sOut, 8), (8 * sY, 8)] s.mem t.mem ∧
      Keep [.rax, .rdx] s t := by
  have hZ : 256 ≤ Z := by have := hc.lo; have := hc.hi; unfold slot hdrBytes at *; omega
  have hs := hc.scr
  have hldY := hs.ld (d := 8 * sY) (by change 160 ≤ Z; omega)
  have hstO := hs.st (d := 8 * VG.Impl.Ffdh.X86_64.Domain.sOut) (by change 184 ≤ Z; omega)
  have hstY := hs.st (d := 8 * sY) (by change 160 ≤ Z; omega)
  have hldG := hs.ld (d := 8 * sG) (by change 224 ≤ Z; omega)
  let m₁ := s.mem.writeW (off B (8 * VG.Impl.Ffdh.X86_64.Domain.sOut)) yp
  let m := m₁.writeW (off B (8 * sY)) gp
  have ho := writeW_outside (d := 8 * VG.Impl.Ffdh.X86_64.Domain.sOut) s.mem B yp (by decide)
  have hy := writeW_outside (d := 8 * sY) m₁ B gp (by decide)
  have hG' : word m₁ B (8 * sG) = gp := by
    rw [ho.word (by decide) (by decide)]
    exact hG
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = m) (by
    unfold bridge
    xrun [State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hc.rdi, hdrOff, hc.good.scr.ld (hdr_lt_slot w 8 (show VG.Impl.Rsa.X86_64.Crt.sLink < 32 by decide)),
      hc.link, hldY, hY, hstO, hldG, hG', hstY, m, m₁]) rfl) fun t ⟨hm, k⟩ => ?_
  refine ⟨?_, ?_, ?_, k⟩
  · rw [hm, hy.word (by decide) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro a ha
    rw [hm]
    exact (hy a (ha (8 * sY, 8) (by simp))).trans
      (ho a (ha (8 * VG.Impl.Ffdh.X86_64.Domain.sOut, 8) (by simp)))

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The private core's output buffer becomes exchange's output, and its
public generator becomes exchange's peer input. -/
def outputP (p : CheckPrivate.KpP) : Exchange.ExP :=
  ⟨p.B, p.Z, p.k, p.dl, p.dp, p.dom, p.yp, p.xp, p.xl, off p.dp p.k, p.gb, p.sp⟩

/-- Move only public pointers; preserve all arithmetic and the computed power. -/
theorem value_bridge {p : CheckPrivate.KpP} {xb : List Byte} {s : State}
    (h : CheckPrivate.Value p xb s) (ho : VG.Proof.Rsa.X86_64.OutOk s p.B p.Z p.yp p.k) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.bridge) s fun t =>
      Exchange.Value (outputP p) xb t ∧ InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep [.rax, .rdx] s t := by
  obtain ⟨⟨mi, hb, hc, hg⟩, hy⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  have hZ := hb.hZ
  refine WP.mono (bridge_ok hc.sub
    (hb.hdr (sY, p.yp) (by simp [CheckPrivate.KpP.headers])) hg)
    fun t ⟨hOut, hY, hf, k⟩ => ?_
  have hr : ∀ r ∈ [(8 * VG.Impl.Ffdh.X86_64.Domain.sOut, 8), (8 * sY, 8)],
      128 ≤ r.1 ∧ r.1 + r.2 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> decide
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (fun r he => by have := hr r he; omega_using [hZ, this])
  have hh : ∀ i < 32, i ≠ sY → i ≠ VG.Impl.Ffdh.X86_64.Domain.sOut →
      word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi hy ho =>
    hf.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> omega_arith) (by omega_using [hi])
  have hv : ∀ j < 8, wv t.mem (off p.B (inner p.w)) (slot p.w j) p.w =
      wv s.mem (off p.B (inner p.w)) (slot p.w j) p.w := by
    intro j hj
    have hs := slot_le (w := p.w) hj
    have hlo := hc.sub.lo
    have hhi := hc.sub.hi
    have hn := hb.scr.nowrap
    have h256 : 256 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega_using []
    refine wv_congr fun i hi => ?_
    rw [word_off, word_off]
    exact hf.word_eq (fun r he => Or.inr (by have := hr r he; omega_using [h256, this])) (by omega_using [hs, hhi, hn, hi])
  have hc' : ModCtx t p.B p.Z (inner p.w) p.w mi p.P :=
    ⟨hc.sub.of_parent hf hr k.2.2 (k.gpr (by decide)),
      hc.xv.of_parent hc.sub.toMem hf (fun r he => (hr r he).2),
      by rw [hv _ (by decide)]; exact hc.r2l,
      by rw [hv _ (by decide)]; exact hc.r2,
      hc.odd, hc.x1, hc.wide, hc.w2, hc.w28⟩
  have hgl : p.gb.length = p.k := by
    simp only [CheckPrivate.KpP.gb, List.length_take, List.length_drop, hb.doml]
    rcases hb.dl with hd | hd <;> rw [hd] <;> omega_using []
  have hySrc := ((hb.dom.drop p.k).take p.k).congrK hi k
  have hb' : Exchange.Base (outputP p) xb t := by
    refine ⟨hb.k1, hb.k2, hb.dl, hb.doml, hgl, hb.xlen, hb.xl1, hb.xl2,
      hb.hZ, hb.scr.congr k.2.2, hb.dom.congrK hi k, hb.x.congrK hi k, hySrc, ?_,
      fun i hi => by rw [k.2.2]; exact ho.wr i hi, ho.sep⟩
    intro e he
    simp only [Exchange.ExP.headers, outputP, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hh sDom (by decide) (by decide) (by decide)).trans
        (hb.hdr (sDom, p.dp) (by simp [CheckPrivate.KpP.headers]))
    · exact (hh sDomLen (by decide) (by decide) (by decide)).trans
        (hb.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [CheckPrivate.KpP.headers]))
    · exact (hh sK (by decide) (by decide) (by decide)).trans
        (hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CheckPrivate.KpP.headers]))
    · exact hY
    · exact (hh sX (by decide) (by decide) (by decide)).trans
        (hb.hdr (sX, p.xp) (by simp [CheckPrivate.KpP.headers]))
    · exact (hh sXl (by decide) (by decide) (by decide)).trans
        (hb.hdr (sXl, BitVec.ofNat 64 p.xl) (by simp [CheckPrivate.KpP.headers]))
    · exact hOut
  exact ⟨⟨⟨mi, hb', hc'⟩, (hv aY (by decide)).trans hy⟩, hi,
    fun i hi => hh i (by omega_using [hi]) (by unfold sY sFn; omega_using [hi])
      (by unfold VG.Impl.Ffdh.X86_64.Domain.sOut sFn; omega_using [hi]), k⟩

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! ### `Ffdh.X86_64.GenerateKey.OutputBytes`, which this module and modules that import it used -/

section

/-! # FFDH key generation on x86-64: byte outputs after masking -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- Read back a source buffer exactly. -/
theorem bytes_src {s : State} {B op : Addr} {Z : Nat} {bs : List Byte} (h : Src s B Z op bs) :
    Spec.Rsa.bytesAt s.mem op bs.length = bs := by
  apply List.ext_getElem (by rw [bytesAt_length])
  intro i _ hi
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  exact h.val i hi

/-- A masked buffer is the original octets or an equally sized zero string. -/
theorem bytes_masked {s t : State} {B op : Addr} {Z k : Nat} {bs : List Byte} {c : Bool}
    (h : Src s B Z op bs) (hl : bs.length = k)
    (hm : ∀ i < k, t.mem (off op i) = if c then s.mem (off op i) else 0) :
    Spec.Rsa.bytesAt t.mem op k = if c then bs else List.replicate k 0 := by
  cases c
  · apply List.ext_getElem (by simp only [Bool.false_eq_true, ↓reduceIte, bytesAt_length, List.length_replicate])
    intro i hi _
    simp only [Bool.false_eq_true, ↓reduceIte, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range,
      List.getElem_replicate]
    exact hm i (by rwa [bytesAt_length] at hi)
  · simp only [↓reduceIte]
    apply List.ext_getElem (by rw [bytesAt_length, hl])
    intro i _ hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact (hm i (by rwa [← hl])).trans (h.val i hi)

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! ### `Ffdh.X86_64.GenerateKey.PublicOutput`, which this module and modules that import it used -/

section

/-! # FFDH on x86-64: range-check and encode a generated public key -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

abbrev GkP.z (p : GkP) (rb : List Byte) : Nat := p.kp.z (p.xb rb)
abbrev GkP.fl (p : GkP) (rb : List Byte) : Prop := p.kp.fl (p.xb rb)

def PublicPost (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if p.fl rb then p.z rb else 0) p.k ∧
    t.gpr .rax = bit (p.fl rb) ∧ t.gpr .rdi = p.B ∧ Src t p.B p.Z p.xp (p.cut rb) ∧ Scr t p.B p.Z ∧
    word t.mem p.B (8 * sX) = off p.xp p.ld ∧ word t.mem p.B (8 * sXl) = BitVec.ofNat 64 p.n ∧
    word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem publicOutput_ok {p : GkP} {rb : List Byte} {s : State}
    (h : CheckPrivate.Value p.kp (p.xb rb) s) (hx : Src s p.B p.Z p.xp (p.cut rb))
    (ho : OutOk s p.B p.Z p.yp p.k) (ha : Apart p.xp p.k p.yp p.k)
    (hxl : (p.cut rb).length = p.k) :
    WP isa (seqs publicOutput) s (PublicPost p rb s) := by
  unfold publicOutput
  refine wp_seqs_cons (by simp [range])
    (WP.mono (value_bridge h ho) fun u ⟨hu, hi₁, hs₁, k₁⟩ => ?_)
  have hxu := hx.congrK hi₁ k₁
  refine wp_seqs_append (a := range aY) (by simp [range]) (by simp)
    (WP.mono (Exchange.value_checked hu) fun v ⟨hv, hi₂, hs₂, k₂⟩ => ?_)
  have hxv := hxu.congrK hi₂ k₂
  have hv' := hv
  obtain ⟨⟨mi, hb, hc⟩, _, _, _⟩ := hv
  refine WP.mono (Exchange.output_ok hv') fun t ⟨hy, hflag, hd, hf, hs₃, k₃⟩ => ?_
  have hhf : Outside p.B p.Z (2 ^ 64 - p.Z) v.mem t.mem := by
    intro a hh
    have ha64 : ofs p.B a < 2 ^ 64 := (a - p.B).isLt
    apply hf
    intro i hi he
    change a = p.yp + BitVec.ofNat 64 i at he
    have hsep : p.Z ≤ ofs p.B (p.yp + BitVec.ofNat 64 i) := hb.sep i hi
    rw [← he] at hsep
    omega_using [hh, ha64, hsep]
  have hh : ∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word v.mem p.B d :=
    fun d hd => hhf.word (Or.inl hd) (by have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hb.scr.nowrap; omega_using [hd, hn])
  have hxt : Src t p.B p.Z p.xp (p.cut rb) := by
    refine ⟨fun i hi => by rw [k₃.2.1, k₃.2.2]; exact hxv.rd i hi, ?_, hxv.out⟩
    intro i hi
    rw [hf _ (fun j hj => ha i (by rwa [hxl] at hi) j hj)]
    exact hxv.val i hi
  have hZ : 128 * p.k + 256 ≤ p.Z := hb.hZ
  have hs₁' : ∀ i < 6, word u.mem p.B (8 * i) = word s.mem p.B (8 * i) := hs₁
  have hs₂' : ∀ i < 6, word v.mem p.B (8 * i) = word u.mem p.B (8 * i) := hs₂
  have hs₃' : ∀ i < 6, word t.mem p.B (8 * i) = word v.mem p.B (8 * i) := hs₃
  refine ⟨hy, hflag, hd, hxt, hb.scr.congr k₃.2.2, ?_, ?_, ?_, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [hh _ (by change 168 ≤ p.Z; omega_using [hZ])]
    exact hb.hdr (sX, off p.xp p.ld) (by simp [Exchange.ExP.headers, outputP, GkP.kp])
  · rw [hh _ (by change 176 ≤ p.Z; omega_using [hZ])]
    exact hb.hdr (sXl, BitVec.ofNat 64 p.n) (by simp [Exchange.ExP.headers, outputP, GkP.kp])
  · rw [hh _ (by change 152 ≤ p.Z; omega_using [hZ])]
    exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [Exchange.ExP.headers, outputP, GkP.kp])
  · intro i hi
    rw [hs₃' i hi, hs₂' i hi, hs₁' i hi]
  · exact (RunFrame.of_scr hi₁).trans ((RunFrame.of_scr hi₂).trans (RunFrame.of_y hf))

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! # FFDH on x86-64: generated-key outputs and status -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Status.lean`, which only this module imported.
section

/-! # FFDH on x86-64: encode success or a degenerate-public-value rejection -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem status_ok {s : State} {B : Addr} {Z : Nat} {c : Bool}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hZ : 256 ≤ Z)
    (hF : word s.mem B (8 * sF) = BitVec.ofNat 64 c.toNat) :
    WP isa (.block status) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 (if c then 1 else 3) ∧ t.mem = s.mem) ∧ Keep [.rax, .rdx] s t := by
  refine WP.keep _ ?_ rfl
  unfold status
  xrun [State.ea, hdr, hd, hdrOff, hs.ld (d := 8 * sF) (by change 248 ≤ Z; omega), hF]
  cases c <;> rfl

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem bit_eq_bool (P : Prop) [Decidable P] :
    bit P = BitVec.ofNat 64 (decide P).toNat := by
  by_cases h : P <;> simp only [bit, h, ↓reduceIte, decide_true, decide_false] <;> rfl

/-- Both outputs are masked when the generated public value is degenerate. -/
def PowerPost (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (if p.fl rb then 1 else 3) ∧ t.gpr .rdi = p.B ∧
    Spec.Rsa.bytesAt t.mem p.xp p.k = (if p.fl rb then p.cut rb else List.replicate p.k 0) ∧
    Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if p.fl rb then p.z rb else 0) p.k ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem outputs_ok {p : GkP} {rb : List Byte} {s₀ s : State}
    (h : PublicPost p rb s₀ s) (ho : OutOk s p.B p.Z p.xp p.k)
    (hy : OutOk s p.B p.Z p.yp p.k) (ha : Apart p.xp p.k p.yp p.k)
    (hZ : 256 ≤ p.Z) (hk : p.k < 2 ^ 31) (hld : p.ld < p.k) (hlen : (p.cut rb).length = p.k) :
    WP isa (seqs [maskX, .block status]) s (PowerPost p rb s) := by
  obtain ⟨hY, hax, hd, hx, hs, hX, hXl, hK, _, _⟩ := h
  change WP isa (.seq maskX (.block status)) s _
  refine WP.seq (WP.mono (maskX_ok hs hd hZ hk hld hX hXl hK
    (c := decide (p.fl rb)) (hax.trans (bit_eq_bool (p.fl rb))) ho)
    fun u ⟨hm, hF, hd', hf, hs', k₁⟩ => ?_)
  have hxu := bytes_masked hx hlen hm
  have hYu : Spec.Rsa.bytesAt u.mem p.yp p.k = Spec.Rsa.bytesAt s.mem p.yp p.k := by
    change (List.range p.k).map _ = (List.range p.k).map _
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    exact hf _ (hy.sep i hi') (fun j hj => Ne.symm (ha j hj i hi'))
  refine WP.mono (status_ok (hs.congr k₁.2.2) hd' hZ hF) fun t ⟨⟨ha', hm'⟩, k₂⟩ => ?_
  refine ⟨?_, (k₂.gpr (by decide)).trans hd', ?_, ?_, ?_, ?_, (k₁.trans k₂).mono (by decide)⟩
  · simpa only [decide_eq_true_eq] using ha'
  · rw [hm', hxu]
    simp only [decide_eq_true_eq]
  · rw [hm', hYu, hY]
  · intro i hi
    rw [hm']; exact hs' i hi
  · intro a ha hx _
    rw [hm']
    exact hf a ha hx

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! ### `Ffdh.X86_64.GenerateKey.MaskCT`, which this module and modules that import it used -/

section

/-! # FFDH on x86-64: output masks never control branches or addresses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

/-- The flag may differ between runs; only output pointers and byte counts are public. -/
structure MaskPre (p : GkP) (s : State) : Prop where
  scr : Scr s p.B p.Z
  rdi : s.gpr .rdi = p.B
  room : 256 ≤ p.Z
  k : p.k < 2 ^ 31
  ld : p.ld < p.k
  x : word s.mem p.B (8 * sX) = off p.xp p.ld
  n : word s.mem p.B (8 * sXl) = BitVec.ofNat 64 (p.k - p.ld)
  width : word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k
  out : OutOk s p.B p.Z p.xp p.k
  flag : ∃ c : Bool, s.gpr .rax = BitVec.ofNat 64 c.toNat

private def maskVal (p : GkP) : Reg → BitVec 64
  | .rdi => p.B | .r11 => p.xp | .rcx => BitVec.ofNat 64 p.k | _ => 0

private theorem mask_regs (p : GkP) (s : State) (h : MaskPre p s) :
    WP isa (.block maskSetup) s fun t => ∀ r ∈ [.rdi, .r11, .rcx], t.gpr r = maskVal p r := by
  obtain ⟨c, hc⟩ := h.flag
  refine WP.mono (maskSetup_ok h.scr h.rdi h.room h.k h.ld h.x h.n h.width hc)
    fun t ⟨⟨hp, _, hcx, _⟩, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (k.gpr (by decide)).trans h.rdi
  · exact hp
  · exact hcx

private theorem mask_end (p : GkP) (s : State) (h : MaskPre p s) :
    WP isa maskX s fun t => t.gpr .rdi = p.B := by
  obtain ⟨c, hc⟩ := h.flag
  exact WP.mono (maskX_ok h.scr h.rdi h.room h.k h.ld h.x h.n h.width hc h.out)
    fun _ ⟨_, _, hd, _⟩ => hd

theorem mask_ct : RelCT isa (Two MaskPre) maskX (Two fun (p : GkP) s => s.gpr .rdi = p.B) :=
  pin_ct [.rdi] [.rdi, .r11, .rcx] maskVal (pins_rdiB GkP.B fun _ _ h => h.rdi)
    (by taint_decide) mask_regs (by taint_decide) mask_end

theorem mask_status_ct : RelCT isa (Two MaskPre) (seqs [maskX, .block status]) fun _ _ => True :=
  RelCT.seq mask_ct (two_taint [.rdi] (pins_rdiB GkP.B fun _ _ h => h) (by taint_decide))

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! # FFDH on x86-64: public-key encoding reuses exchange's timing proof -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (sLink ws)

/-- A generator power and a writable output, as private-key validation
computes it: what the public output's timing depends on. -/
def KBV (p : CheckPrivate.KpP) (s : State) : Prop := ∃ xb,
  CheckPrivate.Value p xb s ∧ OutOk s p.B p.Z p.yp p.k

private def EV (p : CheckPrivate.KpP) (s : State) : Prop := ∃ xb, Exchange.Value (outputP p) xb s
private def EC (p : CheckPrivate.KpP) (s : State) : Prop := ∃ xb, Exchange.Checked (outputP p) xb s

private def bridgeRest : List Instr :=
  [.mov .rdx (.mem (ws .rax sY)), .store (ws .rax VG.Impl.Ffdh.X86_64.Domain.sOut) .rdx,
    .mov .rdx (.mem (ws .rax sG)), .store (ws .rax sY) .rdx]

private theorem bridge_ptr (p : CheckPrivate.KpP) (s : State) (h : KBV p s) :
    WP isa (.block [.mov .rax (.mem (hdr sLink))]) s fun t => t.gpr .rax = p.B := by
  obtain ⟨_, ⟨⟨mi, _, hc, _⟩, _⟩, _⟩ := h
  have hld := hc.sub.good.scr.ld (hdr_lt_slot p.w 8 (show sLink < 32 by decide))
  xrun [State.ea, hdr, hc.sub.rdi, hdrOff, hld, hc.sub.link]

private theorem bridge_ct : RelCT isa (Two KBV) (.block bridge) (Two EV) := by
  change RelCT isa (Two KBV) (.block ([.mov .rax (.mem (hdr sLink))] ++ bridgeRest)) (Two EV)
  refine RelCT.block_append (pin_ct [.rdi] [.rax] (fun p _ => p.B)
    (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, ⟨⟨_, _, hc, _⟩, _⟩, _⟩ := h; exact hc.sub.rdi)
    (by taint_decide) ?_ (by taint_decide) ?_)
  · intro p s h
    exact WP.mono (bridge_ptr p s h) fun _ hh r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hh
  · intro p s h
    obtain ⟨xb, hv, ho⟩ := h
    have hw : WP isa (.block bridge) s (EV p) :=
      WP.mono (value_bridge hv ho) fun _ ⟨he, _⟩ => ⟨xb, he⟩
    change WP isa (.block ([.mov .rax (.mem (hdr sLink))] ++ bridgeRest)) s (EV p) at hw
    exact WP.seq_iff.mpr (WP.block_append_iff.mp hw)

private theorem ev_good (p : CheckPrivate.KpP) (s : State) (h : EV p s) : GoodW1 (outputP p).ws s := by
  obtain ⟨_, ⟨mi, _, hc⟩, _⟩ := h
  exact ⟨⟨mi, hc.sub.good, Nat.le_refl _⟩, Nat.le_trans (by decide) hc.w2,
    Nat.lt_trans hc.w28 (by decide)⟩

private theorem ev_checked (p : CheckPrivate.KpP) (s : State) (h : EV p s) :
    WP isa (seqs (range aY)) s (EC p) := by
  obtain ⟨xb, hv⟩ := h
  exact WP.mono (Exchange.value_checked hv) fun _ ⟨hc, _⟩ => ⟨xb, hc⟩

/-- The public output's timing depends only on the public parameters. -/
theorem public_ct : RelCT isa (Two KBV) (seqs publicOutput) fun _ _ => True := by
  unfold publicOutput
  refine seqs_cons_ct (by simp [range]) (RelCT.seq bridge_ct ?_)
  refine RelCT.seqs_append (a := range aY) (by simp [range]) (by simp)
    (RelCT.seq (R := Two EC)
      (two_post (two_map (fun p => (outputP p).ws) ev_good
        (range_ct (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) ev_checked) ?_)
  exact two_map outputP (fun _ _ h => by obtain ⟨xb, hc⟩ := h; exact ⟨_, hc⟩) Exchange.output_ct

/-- A computed generator power with its full scalar and output buffers. -/
def ValueIn (p : GkP) (s : State) : Prop := ∃ rb,
  CheckPrivate.Value p.kp (p.xb rb) s ∧ Buffers p rb s

private theorem value_mask (p : GkP) (s : State) (h : ValueIn p s) :
    WP isa (seqs publicOutput) s (MaskPre p) := by
  obtain ⟨rb, hv, hb⟩ := h
  have hZ : 128 * p.k + 256 ≤ p.Z := hv.1.choose_spec.1.hZ
  have hk : p.k ≤ 1024 := hv.1.choose_spec.1.k2
  refine WP.mono (publicOutput_ok hv hb.x hb.oy hb.xy hb.len) fun t ht => ?_
  obtain ⟨_, hax, hd, _, hs, hx, hn, hK, _, _, k⟩ := ht
  refine ⟨hs, hd, by omega_using [hZ], by omega_using [hk], hb.ld, hx, hn, hK,
    ⟨fun i hi => by rw [k.2.2]; exact hb.ox.wr i hi, hb.ox.sep⟩, decide (p.fl rb), ?_⟩
  exact hax.trans (bit_eq_bool (p.fl rb))

theorem public_mask_ct : RelCT isa (Two ValueIn) (seqs publicOutput) (Two MaskPre) :=
  two_post (two_map GkP.kp (fun _ _ h => by obtain ⟨rb, hv, hb⟩ := h; exact ⟨_, hv, hb.oy⟩) public_ct) value_mask

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! # FFDH key-generation status and generator powers -/

@[expose] public section

namespace VG.Proof.Ffdh

open VG.Spec.Ffdh

/-- The scalar rejection status is independent of all public-key checks. -/
theorem keyStatus_scalar (a : Parameters) (x : Nat) :
    keyStatus a x = 2 ↔ privateValid a x = false := by
  unfold keyStatus
  cases hv : privateValid a x <;>
    simp only [Bool.not_false, Bool.not_true, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  split <;> decide

/-- A checked generator's powers need only a range check to produce a key. -/
theorem keyStatus_power {a : Parameters} (h : parametersValid a = true) (x : Nat)
    (hx : privateValid a x = true) :
    keyStatus a x = if 1 < a.g ^ x % a.p ∧ a.g ^ x % a.p < a.p - 1 then 1 else 3 := by
  rw [KeyScalar.keyStatus_eq h, hx]
  simp only [Bool.true_eq_false, ↓reduceIte]
  congr 1
  exact propext (publicValid_power h x)

end VG.Proof.Ffdh
