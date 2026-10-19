module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Work
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data

import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.OutputBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskOutput

/-! # FFDH on x86-64: rejected scalars zero both key outputs -/

@[expose] public section

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
