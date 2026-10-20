module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PublicCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryLayoutCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock

/-! # Equal public ABI inputs determine the same complete generation plan -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem GenerationTape.heq_of_data {p q : GenerationGeometry} {a : GenerationTape p} {b : GenerationTape q}
    (hg : p = q) (hp : a.ptr = b.ptr) (hb : a.bytes = b.bytes) : HEq a b := by
  cases hg
  cases a
  cases b
  cases hp
  cases hb
  rfl

theorem GenerationContext.eq_of_data {a b : GenerationContext}
    (hg : a.geo = b.geo) (hs : HEq a.seeds b.seeds) (hh : HEq a.hs b.hs)
    (hr : HEq a.rand b.rand) (hw : a.saved = b.saved) : a = b := by
  cases a
  cases b
  cases hg
  cases hs
  cases hh
  cases hr
  cases hw
  rfl

theorem GenerationPublicAgree.context {s t : State} {hs : GenerationABI s} {ht : GenerationABI t}
    (h : GenerationPublicAgree s t) : contextOf hs = contextOf ht := by
  have di := h.regs .rdi (by decide)
  have si := h.regs .rsi (by decide)
  have dx := h.regs .rdx (by decide)
  have cx := h.regs .rcx (by decide)
  have r8 := h.regs .r8 (by decide)
  have r9 := h.regs .r9 (by decide)
  have a0 := h.args 0 (by decide)
  have a1 := h.args 1 (by decide)
  have a2 := h.args 2 (by decide)
  have a3 := h.args 3 (by decide)
  have a4 := h.args 4 (by decide)
  have geo : geometryOf hs = geometryOf ht := by
    unfold geometryOf
    congr 1
    · exact congrArg (fun x => x - BitVec.ofNat 64 344) h.sp
    · exact congrArg BitVec.toNat dx
    · exact congrArg BitVec.toNat cx
  have words : abiWords s = abiWords t := by
    funext k
    unfold abiWords
    split <;> simp only [di, si, dx, cx, r8, r9, a0, a1, a2, a3, a4]
  exact GenerationContext.eq_of_data geo
    (GenerationTape.heq_of_data geo r8 h.seeds)
    (GenerationTape.heq_of_data geo a0 h.hs)
    (GenerationTape.heq_of_data geo a2 h.rand) words

theorem GenerationPublicAgree.parameter {s t : State} {hs : GenerationABI s} {ht : GenerationABI t}
    (h : GenerationPublicAgree s t) : parameterOf hs = parameterOf ht := by
  have hc := h.context (hs := hs) (ht := ht)
  have tail : generationTail s = generationTail t := by
    simp only [generationTail, savedBase, h.sp, h.regs .rdi (by decide), h.regs .rsi (by decide),
      h.args 4 (by decide), h.args 5 (by decide)]
  have regions : generationRegions s = generationRegions t := by
    simp only [generationRegions, generationBase, h.sp, tail]
  simp only [parameterOf, hc, tail, regions]

end VG.Proof.Dsa.X86_64.Generation
