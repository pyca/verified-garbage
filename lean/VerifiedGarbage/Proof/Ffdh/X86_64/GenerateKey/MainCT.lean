module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CoreCT
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Zero
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CoreCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Zero
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: a key-generation attempt in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

/-- A checked public modulus with uninitialized output buffers. -/
def ZeroPre (p : GkP) (s : State) : Prop := ∃ rb, Base p rb s ∧ s.gpr .rdi = p.B ∧
  word s.mem p.B (8 * sG) = off p.dp p.k ∧ word s.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧ p.mv = true

private def zeroLoads : List Instr :=
  [.mov .rsi (.mem (hdr sY)), .mov .rcx (.mem (hdr sK)), .mov32 .rax (.imm 0)]

private def zeroVal (p : GkP) : Reg → BitVec 64
  | .rsi => p.yp | .rcx => BitVec.ofNat 64 p.k | _ => 0

private theorem zero_regs (p : GkP) (s : State) (h : ZeroPre p s) :
    WP isa (.block zeroLoads) s fun t => ∀ r ∈ [.rsi, .rcx], t.gpr r = zeroVal p r := by
  obtain ⟨rb, hb, hd, _⟩ := h
  have hZ := hb.hZ
  refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = p.yp ∧
      t.gpr .rcx = BitVec.ofNat 64 p.k) (by
    unfold zeroLoads
    xrun [State.ea, hdr, hd, hdrOff,
      hb.scr.ld (d := 8 * sY) (by change 160 ≤ p.Z; omega),
      hb.scr.ld (d := 8 * sK) (by change 152 ≤ p.Z; omega),
      hb.hdr (sY, p.yp) (by simp [GkP.headers]),
      hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers])]) rfl)
    fun t ⟨⟨hy, hk⟩, _⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hy
  · exact hk

private theorem zero_inputs (p : GkP) (s : State) (h : ZeroPre p s) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) s (IV p) := by
  obtain ⟨rb, hb, hd, hG, hQ, hm⟩ := h
  have hZ := hb.hZ
  refine WP.mono (zero_ok hb hd) fun t ⟨hb', hy, _, hh, k⟩ => ?_
  exact ⟨⟨rb, hb', (k.gpr (by decide)).trans hd, hy,
    (hh _ (by change 224 ≤ p.Z; omega)).trans hG,
    (hh _ (by change 232 ≤ p.Z; omega)).trans hQ⟩, hm⟩

private theorem zero_ct : RelCT isa (Two ZeroPre) (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) (Two IV) :=
  pin_ct [.rdi] [.rsi, .rcx] zeroVal (pins_rdiB GkP.B fun _ _ h => by obtain ⟨_, _, hd, _⟩ := h; exact hd)
    (by taint_decide) zero_regs (by taint_decide) zero_inputs

theorem main_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two ZeroPre)
      (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.main M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  change RelCT isa (Two ZeroPre) (.seq (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK)
    (seqs (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.scalar ++
      VG.Impl.Ffdh.X86_64.Domain.GenerateKey.core M.mm E.code (.seq (.block r2Head) R.code)))) _
  exact RelCT.seq zero_ct (RelCT.seqs_append
    (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.scalar)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.scalar])
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.core, pSetup])
    (RelCT.seq sample_ct (core_ct M E R hE)))

end VG.Proof.Ffdh.X86_64.GenerateKey
