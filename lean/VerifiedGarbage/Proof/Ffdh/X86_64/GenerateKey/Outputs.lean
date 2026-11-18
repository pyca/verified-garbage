module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskOutput
public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
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
