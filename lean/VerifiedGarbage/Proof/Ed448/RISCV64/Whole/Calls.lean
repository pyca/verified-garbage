module

import VerifiedGarbage.Proof.Ed448.RISCV64.BaseVerified
public import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarVerified
public import VerifiedGarbage.Proof.Ed448.RISCV64.VVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseMain

/-!
# Ed448's whole functions on RISCV64: the calls of the Ed448 functions

`base_call`, `reduce_call`, `mulAdd_call` and `veq_call`: a call of
`vg_ed448_scalar_base`, `vg_ed448_scalar_reduce`, `vg_ed448_scalar_mul_add`
or `vg_ed448_verify_equation` with its arguments in `a0`–`a4`, by its
contract by register (`baseRISCV64`, …): what it writes, that it keeps the
callee-saved registers, and its result. None of them has a frame
(`*_noFrames`, checked once here).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64
open VG.Spec.Ed448 (bytesAt)

theorem base_noFrames : Impl.Ed448.RISCV64.scalarBase.noFrames = true := by decide +kernel
theorem reduce_noFrames : Impl.Ed448.RISCV64.scalarReduce.noFrames = true := by decide +kernel
theorem mulAdd_noFrames : Impl.Ed448.RISCV64.scalarMulAdd.noFrames = true := by decide +kernel
theorem veq_noFrames : Impl.Ed448.RISCV64.verifyEquation.noFrames = true := by decide +kernel

theorem ce_gpr (s : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {s : State} {Q : State → Prop}

theorem base_call (hl : Proof.Ed448.BaseLadder2Ok) {out sc ws : Addr} (h0 : s.gpr .a0 = out)
    (h1 : s.gpr .a1 = sc) (h2 : s.gpr .a2 = ws) (d₀ : Region.Disjoint ⟨out, 57⟩ ⟨sc, 57⟩)
    (d₁ : Region.Disjoint ⟨out, 57⟩ ⟨ws, 8192⟩)
    (d₂ : Region.Disjoint ⟨sc, 57⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨sc, 57⟩] ++ [⟨out, 57⟩, ⟨ws, 8192⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨out, 57⟩, ⟨ws, 8192⟩] s.wr)
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨out, 57⟩, ⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      bytesAt s'.mem out 57 = Spec.Ed448.scalarBase (bytesAt s.mem sc 57) → Q s') :
    WP isa (.call "vg_ed448_scalar_base" Impl.Ed448.RISCV64.scalarBase) s Q := by
  refine WP.call (k := baseRISCV64) (scalarBase_ok hl) (rd := [⟨sc, 57⟩]) (wr := [⟨out, 57⟩, ⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), h1],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h2],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h1]; exact d₀,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h2]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h1, h2]; exact d₂⟩ hc hw
    (fun s' a b c f g _ hp => k s' a b c f g ?_) base_noFrames
  simp only [baseRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    h0, h1] at hp
  exact hp

theorem reduce_call {out wide ws : Addr} (h0 : s.gpr .a0 = out) (h1 : s.gpr .a1 = wide) (h2 : s.gpr .a2 = ws)
    (d₁ : Region.Disjoint ⟨out, 57⟩ ⟨wide, 114⟩) (d₂ : Region.Disjoint ⟨out, 57⟩ ⟨ws, 8192⟩)
    (d₃ : Region.Disjoint ⟨wide, 114⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨wide, 114⟩] ++ [⟨out, 57⟩, ⟨ws, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨out, 57⟩, ⟨ws, 8192⟩] s.wr)
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨out, 57⟩, ⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      bytesAt s'.mem out 57 = Spec.Ed448.scalarReduce (bytesAt s.mem wide 114) → Q s') :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.RISCV64.scalarReduce) s Q := by
  refine WP.call (k := reduceRISCV64) reduce_ok' (rd := [⟨wide, 114⟩]) (wr := [⟨out, 57⟩, ⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), h1],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h2],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h1]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h2]; exact d₂,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h1, h2]; exact d₃⟩ hc hw
    (fun s' a b c f g _ hp => k s' a b c f g ?_) reduce_noFrames
  simp only [reduceRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    h0, h1] at hp
  exact hp

theorem mulAdd_call {out r k a ws : Addr} (h0 : s.gpr .a0 = out) (h1 : s.gpr .a1 = r) (h2 : s.gpr .a2 = k)
    (h3 : s.gpr .a3 = a) (h4 : s.gpr .a4 = ws) (d₁ : Region.Disjoint ⟨out, 57⟩ ⟨ws, 8192⟩)
    (d₂ : Region.Disjoint ⟨r, 57⟩ ⟨ws, 8192⟩) (d₃ : Region.Disjoint ⟨k, 57⟩ ⟨ws, 8192⟩)
    (d₄ : Region.Disjoint ⟨a, 57⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨r, 57⟩, ⟨k, 57⟩, ⟨a, 57⟩] ++ [⟨out, 57⟩, ⟨ws, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨out, 57⟩, ⟨ws, 8192⟩] s.wr)
    (K : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨out, 57⟩, ⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      bytesAt s'.mem out 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem r 57) (bytesAt s.mem k 57)
        (bytesAt s.mem a 57) → Q s') :
    WP isa (.call "vg_ed448_scalar_mul_add" Impl.Ed448.RISCV64.scalarMulAdd) s Q := by
  refine WP.call (k := mulAddRISCV64) mulAdd_ok' (rd := [⟨r, 57⟩, ⟨k, 57⟩, ⟨a, 57⟩]) (wr := [⟨out, 57⟩, ⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide),
        h1, h2, h3],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h4],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h4]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h1, h4]; exact d₂,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h2, h4]; exact d₃,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h4]; exact d₄⟩ hc hw
    (fun s' a b c f g _ hp => K s' a b c f g ?_) mulAdd_noFrames
  simp only [mulAddRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide),
    h0, h1, h2, h3] at hp
  exact hp

theorem veq_call (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) {pk sig ch ws : Addr}
    (h0 : s.gpr .a0 = pk) (h1 : s.gpr .a1 = sig) (h2 : s.gpr .a2 = ch) (h3 : s.gpr .a3 = ws)
    (d₁ : Region.Disjoint ⟨pk, 57⟩ ⟨ws, 8192⟩) (d₂ : Region.Disjoint ⟨sig, 114⟩ ⟨ws, 8192⟩)
    (d₃ : Region.Disjoint ⟨ch, 57⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩] ++ [⟨ws, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨ws, 8192⟩] s.wr)
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (s'.gpr .a0).setWidth 32 = (if Spec.Ed448.verifyEquation (bytesAt s.mem pk 57) (bytesAt s.mem sig 114)
        (bytesAt s.mem ch 57) then 1 else 0) → Q s') :
    WP isa (.call "vg_ed448_verify_equation" Impl.Ed448.RISCV64.verifyEquation) s Q := by
  refine WP.call (k := verifyRISCV64) (verifyEquation_ok hR hV) (rd := [⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩])
    (wr := [⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide),
        h0, h1, h2],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), h3],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h3]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h1, h3]; exact d₂,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h2, h3]; exact d₃⟩ hc hw
    (fun s' a b c f g _ hp => k s' a b c f g ?_) veq_noFrames
  simp only [verifyRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), h0, h1, h2] at hp
  exact hp

end

end VG.Proof.Ed448.RISCV64.Whole
