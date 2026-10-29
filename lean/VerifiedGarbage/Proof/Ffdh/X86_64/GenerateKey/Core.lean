module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.PublicOutput

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Work
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.OutputBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskOutput
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
import VerifiedGarbage.Proof.Ffdh.Domain
/-! # FFDH on x86-64: scalar rejection and generated public values -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Tail.lean`, which only this module imported.
section

/-! # FFDH on x86-64: exponentiate a sampled scalar and finish both outputs -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem tail_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    {p : GkP} {rb : List Byte} {mi : BitVec 64} {s : State}
    (h : CheckPrivate.Work p.kp (p.xb rb) mi s) (hd : s.gpr .rdi = off p.B (inner p.w))
    (hm : p.mv = true) (hx : Src s p.B p.Z p.xp (p.cut rb))
    (hoX : OutOk s p.B p.Z p.xp p.k) (hoY : OutOk s p.B p.Z p.yp p.k)
    (ha : Apart p.xp p.k p.yp p.k) (hlen : (p.cut rb).length = p.k) (hld : p.ld < p.k) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.tail M.mm E.code (.seq (.block r2Head) R.code))) s (PowerPost p rb s) := by
  have hZ : 128 * p.k + 256 ≤ p.Z := h.base.hZ
  have hk : p.k ≤ 1024 := h.base.k2
  unfold VG.Impl.Ffdh.X86_64.Domain.GenerateKey.tail
  simp only [List.append_assoc]
  refine wp_seqs_append (a := [.seq (.block r2Head) R.code]) (by simp) (by simp)
    (WP.mono (CheckPrivate.work_ready M R h hd hm) fun u ⟨hu, hi₁, hs₁, k₁⟩ => ?_)
  refine wp_seqs_append (a := pow M.mm E.code sG sK sX sXl)
    (b := publicOutput ++ [maskX, .block status]) (by simp [pow]) (by simp)
    (WP.mono (CheckPrivate.ready_value M E hu) fun v ⟨hv, hi₂, hs₂, k₂⟩ => ?_)
  have hxy := (hx.congrK hi₁ k₁).congrK hi₂ k₂
  have hyv : OutOk v p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact hoY.wr i hi, hoY.sep⟩
  refine wp_seqs_append (a := publicOutput) (b := [maskX, .block status]) (by simp [publicOutput]) (by simp)
    (WP.mono (publicOutput_ok hv hxy hyv ha hlen) fun z hz => ?_)
  have hz' := hz
  obtain ⟨_, _, _, _, _, _, _, _, hs₃, hf₃, k₃⟩ := hz
  have hox : OutOk z p.B p.Z p.xp p.k :=
    ⟨fun i hi => by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hoX.wr i hi, hoX.sep⟩
  have hoy : OutOk z p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hoY.wr i hi, hoY.sep⟩
  refine WP.mono (outputs_ok hz' hox hoy ha (by omega) (by omega) hld hlen)
    fun t ⟨hret, hdi, hX, hY, hs₄, hf₄, k₄⟩ => ?_
  refine ⟨hret, hdi, hX, hY, ?_, ?_, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · intro i hi
    have a₁ : word u.mem p.B (8 * i) = word s.mem p.B (8 * i) := hs₁ i hi
    have a₂ : word v.mem p.B (8 * i) = word u.mem p.B (8 * i) := hs₂ i hi
    exact (hs₄ i hi).trans ((hs₃ i hi).trans (a₂.trans a₁))
  · exact (RunFrame.of_scr hi₁).trans ((RunFrame.of_scr hi₂).trans (hf₃.trans hf₄))

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Reject.lean`, which only this module imported.
section

/-! # FFDH on x86-64: rejected scalars zero both key outputs -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

def RejectPost (p : GkP) (s t : State) : Prop :=
  t.gpr .rax = 2 ∧ t.gpr .rdi = p.B ∧
    Spec.Rsa.bytesAt t.mem p.xp p.k = List.replicate p.k 0 ∧
    Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem reject_ok {p : GkP} {rb : List Byte} {mi : BitVec 64} {s : State}
    (h : CheckPrivate.Work p.kp (p.xb rb) mi s) (hd : s.gpr .rdi = off p.B (inner p.w))
    (hax : s.gpr .rax = 0) (hx : Src s p.B p.Z p.xp (p.cut rb))
    (ho : OutOk s p.B p.Z p.xp p.k) (ha : Apart p.xp p.k p.yp p.k)
    (hlen : (p.cut rb).length = p.k) (hld : p.ld < p.k) :
    WP isa (seqs [.block [leave], maskX, ret 2]) s (RejectPost p s) := by
  have hZ : 128 * p.k + 256 ≤ p.Z := h.base.hZ
  have hk : p.k ≤ 1024 := h.base.k2
  change WP isa (.seq (.block [leave]) (.seq maskX (ret 2))) s _
  refine WP.seq (WP.mono (leave_ok (h.mem.ctx hd)) fun u ⟨hdu, hmu, k₁⟩ => ?_)
  have hb := h.base
  have hXu : word u.mem p.B (8 * sX) = off p.xp p.ld := by
    rw [hmu]; exact hb.hdr (sX, off p.xp p.ld) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  have hLu : word u.mem p.B (8 * sXl) = BitVec.ofNat 64 (p.k - p.ld) := by
    rw [hmu]; exact hb.hdr (sXl, BitVec.ofNat 64 p.n) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  have hKu : word u.mem p.B (8 * sK) = BitVec.ofNat 64 p.k := by
    rw [hmu]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  have hiu : InScr p.B p.Z s.mem u.mem := by intro a _; rw [hmu]
  have hxu := hx.congrK hiu k₁
  have hyu : Src u p.B p.Z p.yp (List.replicate p.k 0) := hb.y.congrK hiu k₁
  have hou : OutOk u p.B p.Z p.xp p.k := ⟨fun i hi => by rw [k₁.2.2]; exact ho.wr i hi, ho.sep⟩
  refine WP.seq (WP.mono (maskX_ok (B := p.B) (Z := p.Z) (hb.scr.congr k₁.2.2) hdu (by omega) (by omega) hld
    hXu hLu hKu (c := false) (by rw [k₁.gpr (by decide), hax]; rfl) hou)
    fun v ⟨hmask, _, hdv, hf, hs, k₂⟩ => ?_)
  have hXv : Spec.Rsa.bytesAt v.mem p.xp p.k = List.replicate p.k 0 := bytes_masked hxu hlen hmask
  have hYv : Src v p.B p.Z p.yp (List.replicate p.k 0) := by
    refine ⟨fun i hi => by rw [k₂.2.1, k₂.2.2]; exact hyu.rd i hi, ?_, hyu.out⟩
    intro i hi
    rw [hf _ (hyu.out i hi) (fun j hj => Ne.symm (ha j hj i (by simpa only [List.length_replicate] using hi)))]
    exact hyu.val i hi
  have hYbytes : Spec.Rsa.bytesAt v.mem p.yp p.k = List.replicate p.k 0 := by
    have hh := bytes_src hYv
    simpa only [List.length_replicate] using hh
  refine WP.mono (ret_ok (r := 2) v (by decide)) fun t ⟨hr, hmem, k₃⟩ => ?_
  exact ⟨hr, (k₃.gpr (by decide)).trans hdv, by rw [hmem]; exact hXv,
    by rw [hmem]; exact hYbytes, fun i hi => by rw [hmem, hs i hi, hmu],
    (fun a ha hx _ => by rw [hmem, hf a ha hx, hmu]),
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/ResultMath.lean`, which only this module imported.
section

/-! # FFDH on x86-64: generation's machine status matches the shared specification -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.Spec.Ffdh

/-- The scalar test rejects with 2; a power's range flag selects 1 or 3. -/
def resultStatus (p : GkP) (rb : List Byte) : Nat :=
  if p.sv = false then 2 else if p.fl rb then 1 else 3

theorem Base.power_value {p : GkP} {rb : List Byte} {s : X86_64.State} (h : Base p rb s)
    (hm : p.mv = true) : p.z rb = p.params.g ^ p.scalar rb % p.params.p := by
  change p.params.g ^ Spec.Rsa.os2ip (p.xb rb) % p.params.p = _
  rw [h.sample_value hm]

theorem Base.resultStatus_eq {p : GkP} {rb : List Byte} {s : X86_64.State} (h : Base p rb s)
    (hm : p.mv = true) (ha : parametersValid p.params = true) :
    resultStatus p rb = keyStatus p.params (p.scalar rb) := by
  cases hsv : p.sv with
  | false =>
    have hx : privateValid p.params (p.scalar rb) = false := h.valid.trans hsv
    have hr := (VG.Proof.Ffdh.keyStatus_scalar p.params (p.scalar rb)).mpr hx
    simpa only [resultStatus, hsv, ↓reduceIte] using hr.symm
  | true =>
    have hx : privateValid p.params (p.scalar rb) = true := h.valid.trans hsv
    rw [VG.Proof.Ffdh.keyStatus_power ha _ hx]
    simp only [resultStatus, hsv, Bool.true_eq_false, ↓reduceIte]
    congr 1
    apply propext
    change (1 < p.z rb ∧ 2 * (p.z rb / 2) + 1 < p.P) ↔ _
    rw [lt_pm1 (VG.Proof.Bignum.valid_facts hm h.k1).1, h.power_value hm]
    rfl

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

/-- The complete attempt result before restoring the caller's saved registers. -/
def AttemptPost (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (resultStatus p rb) ∧ t.gpr .rdi = p.B ∧
    Spec.Rsa.bytesAt t.mem p.xp p.k = (if resultStatus p rb = 1 then p.cut rb else List.replicate p.k 0) ∧
    Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if resultStatus p rb = 1 then p.z rb else 0) p.k ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem core_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    {p : GkP} {rb : List Byte} {s : State}
    (h : CheckPrivate.Base p.kp (p.xb rb) s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) (hx : Src s p.B p.Z p.xp (p.cut rb))
    (hoX : OutOk s p.B p.Z p.xp p.k) (hoY : OutOk s p.B p.Z p.yp p.k)
    (ha : Apart p.xp p.k p.yp p.k) (hlen : (p.cut rb).length = p.k) (hld : p.ld < p.k) :
    WP isa (seqs (core M.mm E.code (.seq (.block r2Head) R.code))) s (AttemptPost p rb s) := by
  have hk : 64 ≤ p.k := h.k1
  have hodd := (valid_facts hm hk).1
  unfold core
  simp only [List.append_assoc]
  refine wp_seqs_append
    (a := ([.block VG.Impl.Rsa.X86_64.head] ++ pSetup ++ VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl))
    (b := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++ [.block [.alu .test .rax (.reg .rax)],
      .ite .e (seqs [.block [VG.Impl.Rsa.X86_64.Crt.leave], maskX, ret 2])
        (seqs (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.tail M.mm E.code (.seq (.block r2Head) R.code)))])
    (by simp [pSetup]) (by simp)
    (WP.mono (CheckPrivate.setup_work h hd hG hQ hm) fun u₁ S₁ => ?_)
  obtain ⟨mi, hw₁, hd₁⟩ := S₁.1
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr]) (by simp)
    (WP.mono (CheckPrivate.scalar_ok hw₁ hd₁ hodd) fun u₂ S₂ => ?_)
  have hw₂ := S₂.1.1
  have hd₂ := S₂.1.2.1
  simp only [seqs]
  have hflag₂ : u₂.gpr .rax = bit (p.sv = true) := S₂.1.2.2
  refine WP.seq (WP.mono (test_bit_ok hflag₂) fun u₃ ⟨hz, hmem, k⟩ => ?_)
  have hw₃ := hw₂.keep hmem k
  have hd₃ := (k.gpr (by decide)).trans hd₂
  have S₃ : CheckPrivate.StepPost p.kp u₂ (fun _ => True) u₃ :=
    ⟨trivial, by rw [hmem]; exact InScr.refl _ _ _, fun _ _ => by rw [hmem], k.mono (by decide)⟩
  have H := (S₁.trans S₂).trans S₃
  have hx₃ := hx.congrK H.2.1 H.2.2.2
  have hox₃ : OutOk u₃ p.B p.Z p.xp p.k :=
    ⟨fun i hi => by rw [H.2.2.2.2.2]; exact hoX.wr i hi, hoX.sep⟩
  have hoy₃ : OutOk u₃ p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [H.2.2.2.2.2]; exact hoY.wr i hi, hoY.sep⟩
  refine WP.ite (!decide (p.sv = true)) (by simp [eval, hz]) (fun he => ?_) (fun he => ?_)
  · have hsv : p.sv = false := by cases h : p.sv <;> simp_all
    have hax₃ : u₃.gpr .rax = 0 := by
      rw [k.gpr (by decide)]
      simpa only [bit, hsv, Bool.false_eq_true, ↓reduceIte] using hflag₂
    refine WP.mono (reject_ok hw₃ hd₃ hax₃ hx₃ hox₃ ha hlen hld)
      fun t ⟨hr, hd, hX, hY, hs, hf, kt⟩ => ?_
    refine ⟨?_, hd, ?_, ?_, ?_, (RunFrame.of_scr H.2.1).trans hf, keep_trans H.2.2.2 kt⟩
    · simpa [resultStatus, hsv] using hr
    · simpa [resultStatus, hsv] using hX
    · simpa [resultStatus, hsv, i2osp_zero'] using hY
    · intro i hi
      have hH : word u₃.mem p.B (8 * i) = word s.mem p.B (8 * i) := H.2.2.1 i hi
      exact (hs i hi).trans hH
  · have hsv : p.sv = true := by cases h : p.sv <;> simp_all
    refine WP.mono (tail_ok M E R hw₃ hd₃ hm hx₃ hox₃ hoy₃ ha hlen hld)
      fun t ⟨hr, hd, hX, hY, hs, hf, kt⟩ => ?_
    have hres : resultStatus p rb = if p.fl rb then 1 else 3 := by
      simp only [resultStatus, hsv, Bool.true_eq_false, ↓reduceIte]
    refine ⟨by rwa [hres], hd, ?_, ?_, ?_, (RunFrame.of_scr H.2.1).trans hf, keep_trans H.2.2.2 kt⟩
    · rw [hres]
      by_cases hf : p.fl rb
      · rw [ite_eq_left hf, ite_eq_left (by decide)]
        simpa only [ite_eq_left hf] using hX
      · rw [ite_eq_right hf, ite_eq_right (by decide)]
        simpa only [ite_eq_right hf] using hX
    · rw [hres]
      by_cases hf : p.fl rb
      · rw [ite_eq_left hf, ite_eq_left (by decide)]
        simpa only [ite_eq_left hf] using hY
      · rw [ite_eq_right hf, ite_eq_right (by decide)]
        simpa only [ite_eq_right hf] using hY
    · intro i hi
      have hH : word u₃.mem p.B (8 * i) = word s.mem p.B (8 * i) := H.2.2.1 i hi
      exact (hs i hi).trans hH

end VG.Proof.Ffdh.X86_64.GenerateKey
