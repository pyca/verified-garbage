module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskOutput
import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ArithmeticBridge
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

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
