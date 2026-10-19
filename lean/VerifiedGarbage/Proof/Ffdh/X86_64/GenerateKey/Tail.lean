module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock

/-! # FFDH on x86-64: exponentiate a sampled scalar and finish both outputs -/

@[expose] public section

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
