module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryBodyCT

/-! # Equal public ABI inputs determine the same complete generation plan -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

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
  have x0 := h.regs .x0 (by decide)
  have x1 := h.regs .x1 (by decide)
  have x2 := h.regs .x2 (by decide)
  have x3 := h.regs .x3 (by decide)
  have x4 := h.regs .x4 (by decide)
  have x5 := h.regs .x5 (by decide)
  have x6 := h.regs .x6 (by decide)
  have x7 := h.regs .x7 (by decide)
  have a0 := h.args 0 (by decide)
  have a1 := h.args 1 (by decide)
  have a2 := h.args 2 (by decide)
  have a3 := h.args 3 (by decide)
  have geo : geometryOf hs = geometryOf ht := by
    unfold geometryOf
    congr 1
    · exact congrArg (fun x => x - BitVec.ofNat 64 448) h.sp
    · exact congrArg BitVec.toNat x2
    · exact congrArg BitVec.toNat x3
  have words : abiWords s = abiWords t := by
    funext k
    unfold abiWords
    split <;> simp only [x0, x1, x2, x3, x4, x5, x6, x7, a0, a1, a2]
  exact GenerationContext.eq_of_data geo
    (GenerationTape.heq_of_data geo x4 h.seeds)
    (GenerationTape.heq_of_data geo x6 h.hs)
    (GenerationTape.heq_of_data geo a0 h.rand) words

def parameterOf {s : State} (h : GenerationABI s) : ParameterPublic :=
  ⟨contextOf h, 0, Nat.zero_le _, 0, Nat.zero_le _⟩

theorem GenerationPublicAgree.parameter {s t : State} {hs : GenerationABI s} {ht : GenerationABI t}
    (h : GenerationPublicAgree s t) : parameterOf hs = parameterOf ht := by
  simp only [parameterOf, h.context (hs := hs) (ht := ht)]

end VG.Proof.Dsa.AArch64.Generation
