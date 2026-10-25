module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Core
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Zero
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample

/-! # FFDH on x86-64: a complete key-generation attempt -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem main_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    {p : GkP} {rb : List Byte} {s : State} (h : Base p rb s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.main M.mm E.code (.seq (.block r2Head) R.code)) s
      (AttemptPost p rb s) := by
  have hk := h.k1
  have hZ := h.hZ
  unfold VG.Impl.Ffdh.X86_64.Domain.GenerateKey.main
  change WP isa (.seq (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK)
    (seqs (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.scalar ++
      VG.Impl.Ffdh.X86_64.Domain.GenerateKey.core M.mm E.code (.seq (.block r2Head) R.code)))) s _
  refine WP.seq (WP.mono (zero_ok h hd) fun u ⟨hu, hy, hf₁, hh, k₁⟩ => ?_)
  have hdi : u.gpr .rdi = p.B := (k₁.gpr (by decide)).trans hd
  have hg : word u.mem p.B (8 * sG) = off p.dp p.k := by
    rw [hh _ (by change 224 ≤ p.Z; omega)]; exact hG
  have hq : word u.mem p.B (8 * sQ) = off p.dp (2 * p.k) := by
    rw [hh _ (by change 232 ≤ p.Z; omega)]; exact hQ
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.scalar)
    (b := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.core M.mm E.code (.seq (.block r2Head) R.code))
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.scalar])
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.core, pSetup])
    (WP.mono (scalar_ok ⟨hu, hdi, hy, hg, hq⟩ hm) fun v ⟨hb, hx, hdv, hgv, hqv, hs₂, hf₂, k₂⟩ => ?_)
  have hox : OutOk v p.B p.Z p.xp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact h.x.wr i hi, h.x.sep⟩
  have hoy : OutOk v p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact h.y.wr i hi, h.y.sep⟩
  refine WP.mono (core_ok M E R hb hdv hgv hqv hm hx hox hoy h.xy (h.cut_length) h.ld_lt)
    fun t ⟨hr, hdt, hX, hY, hs₃, hf₃, k₃⟩ => ?_
  refine ⟨hr, hdt, hX, hY, ?_, (RunFrame.of_y hf₁).trans (hf₂.trans hf₃), ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro i hi
  rw [hs₃ i hi, hs₂ i hi, hh _ (by omega)]

end VG.Proof.Ffdh.X86_64.GenerateKey
