module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scan
import VerifiedGarbage.Proof.Framework.Omega

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
    omega
  refine WP.keep _ ?_ rfl
  unfold cutSetup
  xrun [CutRegs, State.ea, hdr, h.rdi, hdrOff,
    h.base.scr.ld (d := 8 * sRand) (by change 208 ≤ p.Z; omega),
    h.base.scr.ld (d := 8 * sX) (by change 168 ≤ p.Z; omega),
    h.base.scr.ld (d := 8 * sMsk) (by change 256 ≤ p.Z; omega),
    h.base.scr.ld (d := 8 * sK) (by change 152 ≤ p.Z; omega),
    h.base.scr.ld (d := 8 * sEl) (by change 200 ≤ p.Z; omega),
    h.base.hdr (sRand, p.rp) (by simp [GkP.headers]),
    h.base.hdr (sX, p.xp) (by simp [GkP.headers]),
    h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers]), hn, hm, hsub]

end VG.Proof.Ffdh.X86_64.GenerateKey
