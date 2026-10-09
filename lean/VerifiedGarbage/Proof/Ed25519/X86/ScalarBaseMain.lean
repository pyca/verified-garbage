import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
import VerifiedGarbage.Proof.Ed25519.X86.CommonFinish
import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign
import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86.InputBits
import VerifiedGarbage.Proof.Ed25519.X86.PointMul
import VerifiedGarbage.Proof.Ed25519.X86.CombTbl
import VerifiedGarbage.Proof.Framework.X86.Call

/-! Merged from `Proof.Ed25519.X86.ScalarBaseContract`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86
open VG.Impl.Ed25519.X86 (combSym)

/-- The regions and arguments of `vg_ed25519_scalar_base` (and `vg_x25519_base`): the tables
are readable, after the arguments, and the 20 bytes below `esp` a call of the field functions
uses lie apart from the input and the scratch. -/
def BaseRegions (s : State) : Prop :=
  let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
  let input : Region := ⟨(arg s 1).setWidth 64, 32⟩
  let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
  let args : Region := ⟨argAddr s 0, 12⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  s.rd = [input, args, TBL ((s.syms combSym).setWidth 64)] ∧ s.wr = [out, scratch] ∧
    out.Disjoint scratch ∧ input.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
    (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (callStk s).Disjoint input ∧
    (callStk s).Disjoint scratch

/-- The contract the proof is written against: the regions, the 20 bytes below `esp` (the
static's address's frame and the calls') apart from the buffers, and the tables. -/
def scalarBaseLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let stk : Region := callStk s
    BaseRegions s ∧ stk.Disjoint out ∧ CombHeld s [out, scratch, stk]
  post s t := Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2 ∧
    s.syms combSym = t.syms combSym

theorem BaseRegions.spfit {s : State} (h : BaseRegions s) : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

theorem BaseRegions.sp4 {s : State} (h : BaseRegions s) : 4 ≤ (s.gpr .esp).toNat := by
  have := h.2.2.2.2.2.2.2.2.2.2.2.2.1; omega

theorem scalarBase_pre {s : State} (h : BaseRegions s) :
    ScratchPre s 2 3 ∧ InputPre s 2 1 8 ∧ OutputPre s 2 := by
  obtain ⟨rd, wr, os, ins, _, ars, ro, rs, ofit, ifit, sfit, spfit, h20, ki, ks⟩ := h
  refine ⟨⟨by decide, ?_, sfit, ?_, by omega_using [spfit], ars, rs, h20, ks.symm⟩,
    ⟨?_, ifit, ?_, by rw [sub, addr_zero]; exact ki.symm⟩, ⟨?_, ofit, os, ro⟩⟩
  · rw [wr]; simp
  · rw [rd]; simp
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ins
  · rw [wr]; simp
end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointEncode`. -/
section
/-! Canonical Ed25519 point encoding in scratch slot1. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem pointEncode_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointEncode s fun t => IKeep x s t ∧
      fe t.mem x 96 =
        (env s.mem x 1 * Spec.X25519.pow (env s.mem x 2) (Spec.X25519.P - 2)).val +
        ((env s.mem x 0 * Spec.X25519.pow (env s.mem x 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  refine WP.seq (WP.mono (pointAffine_ok hc) fun a ⟨ka, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (freezeField_ok (ka.ctx hc) 0) fun b ⟨kb, eb, vb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointSign_ok (kb.ctx (ka.ctx hc))) fun c ⟨kc, mc, sc⟩ => ?_
  rw [WP.block_append_iff]
  have cc := kc.ctx (kb.ctx (ka.ctx hc))
  refine WP.mono (freezeField_ok cc 1) fun d ⟨kd, _, vd⟩ => ?_
  have ds : d.gpr .esi = BitVec.ofNat 32 (((env a.mem x 0).val % 2) * 2 ^ 31) := by
    change fe b.mem x 64 = _ at vb
    rw [kd.keep.esi, sc, vb]
  have dy : fe d.mem x 96 = (env a.mem x 1).val := by
    rw [mc, eb] at vd
    exact vd
  refine WP.mono (encodeSign_ok (kd.ctx cc) ((env a.mem x 0).val % 2) ((env a.mem x 1).val)
    (by omega) (Nat.lt_trans (env a.mem x 1).isLt (by decide : Spec.X25519.P < 2 ^ 255)) dy ds)
    fun t ⟨kt, vt⟩ => ?_
  refine ⟨(((ka.trans (IKeep.of_field kb)).trans kc).trans (IKeep.of_field kd)).trans (IKeep.of_field kt), ?_⟩
  rw [vt, ax, ay]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem baseSetup_d (e : Env) : evalOps baseSetupOps e 16 = Spec.Ed25519.d := rfl

theorem Saved.ikeep {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (k : IKeep x s t) : Saved s₀ x t :=
  h.of_offsetS hx ⟨k.edi, k.esp, k.rd, k.wr⟩ k.frame (by decide) (by decide) (by decide)

theorem Saved.mulkeep {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (k : MulKeep x s t) : Saved s₀ x t :=
  h.of_offsetS hx ⟨k.edi, k.esp, k.rd, k.wr⟩ k.frame (by decide) (by decide) (by decide)

theorem pointEncode_value {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointEncode s fun t => IKeep x s t ∧ Spec.Ed25519.encodeLE 32 (fe t.mem x 96) =
      Spec.Ed25519.encodePoint (point (env s.mem x) 0 1 2 3) := by
  refine WP.mono (pointEncode_ok hc) fun t ⟨kt, vt⟩ => ⟨kt, ?_⟩
  rw [vt]; rfl

end VG.Proof.Ed25519.X86
