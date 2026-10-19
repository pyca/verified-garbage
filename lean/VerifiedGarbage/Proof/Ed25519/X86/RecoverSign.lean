module

public import VerifiedGarbage.Proof.Ed25519.X86.RecoverParity
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ed25519.X86.FreezeField

/-! Merged from `Proof.Ed25519.X86.RecoverAdjust`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩
def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem recoverSuccess_ok {s : State} {x : BitVec 32} (hc : Ctx x s) :
    WP isa (.block recoverSuccess) s fun t => FieldKeep x s t ∧ t.gpr .eax = 1 ∧
      point (env t.mem x) 0 1 2 3 = recoveredPoint (env s.mem x 0) (env s.mem x 1) := by
  rw [recoverSuccess, WP.block_append_iff]
  refine WP.mono (fieldCode_ok recoverSuccessOps hc) fun a ⟨ka, ea⟩ => ?_
  refine WP.mono (returnFlag_ok a x true) fun t ⟨kt, mt, rt⟩ => ?_
  exact ⟨ka.trans kt, rt, by rw [mt, ea]; rfl⟩

private theorem adjustBranch_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (b : Bool)
    (hz : s.zf = some (((env s.mem x 0).val % 2 == 1) == b)) :
    WP isa (.ite .e (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0]))) s fun t =>
      FieldKeep x s t ∧ env t.mem x 0 = signedX (env s.mem x 0) b ∧ env t.mem x 1 = env s.mem x 1 := by
  apply WP.ite (((env s.mem x 0).val % 2 == 1) == b) hz
  · intro h
    exact WP.block_nil ⟨FieldKeep.refl _ _, by simp only [signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] hc) fun t ⟨kt, et⟩ => ?_
    refine ⟨kt, ?_, ?_⟩
    · rw [et]
      change 0 - env s.mem x 0 = signedX (env s.mem x 0) b
      simp only [signedX, h, Bool.false_eq_true, ite_false]
    · rw [et]; rfl

theorem recoverAdjustSign_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa recoverAdjustSign s fun t => FieldKeep x s t ∧ t.gpr .eax = 1 ∧
      point (env t.mem x) 0 1 2 3 = recoveredPoint (signedX (env s.mem x 0) b) (env s.mem x 1) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hc 0) fun a ⟨ka, ea, va⟩ => ?_
  refine WP.mono (recoverParity_ok (ka.ctx hc) b (ka.keep.esi.trans hb)) fun c ⟨kc, mc, zc⟩ => ?_
  have ec : env c.mem x = env s.mem x := by rw [mc, ea]
  have zc' : c.zf = some (((env c.mem x 0).val % 2 == 1) == b) := by
    change fe a.mem x 64 = _ at va
    rw [zc, va, ec]
  refine WP.seq (WP.mono (adjustBranch_ok ((ka.trans kc).ctx hc) b zc') fun d ⟨kd, dx, dy⟩ => ?_)
  refine WP.mono (recoverSuccess_ok (((ka.trans kc).trans kd).ctx hc)) fun t ⟨kt, rt, pt⟩ => ?_
  exact ⟨((ka.trans kc).trans kd).trans kt, rt, by rw [pt, dx, dy, ec]⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def DecodeResult (x : BitVec 32) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .eax = 0
  | some p => s.gpr .eax = 1 ∧ point (env s.mem x) 0 1 2 3 = p

def signResult (x y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if x = 0 && b then none else some (recoveredPoint (signedX x b) y)

theorem recoverInvalid_ok (s : State) (x : BitVec 32) :
    WP isa recoverInvalid s fun t => FieldKeep x s t ∧ DecodeResult x none t :=
  WP.mono (returnFlag_ok s x false) fun _ ⟨kt, _, rt⟩ => ⟨kt, rt⟩

/-- `test eax, eax` of a flag `c`. -/
theorem flagTest_ok {s : State} (x : BitVec 32) (c : Bool) (hc : s.gpr .eax = signWord c) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t => FieldKeep x s t ∧ t.mem = s.mem ∧
      isa.eval .ne t = some c := by
  refine Wp.wp_test fun t ht zt => WP.block_nil ?_
  refine ⟨FieldKeep.of_mem ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩ ht.mem, ht.mem, ?_⟩
  show t.zf.map (!·) = _
  rw [zt, BitVec.and_self, hc]
  cases c <;> rfl

theorem recoverZero_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa recoverZero s fun t => FieldKeep x s t ∧ env t.mem x = env s.mem x ∧
      t.gpr .eax = signWord (decide (env s.mem x 0 = 0) && b) := by
  refine WP.seq (WP.mono (fieldZero_ok hc 0) fun a ⟨ka, ea, za⟩ => ?_)
  apply WP.ite (decide (env s.mem x 0 = 0)) za
  · intro hz
    refine Wp.wp_mov fun t ht => WP.block_nil ⟨ka.trans (FieldKeep.of_mem (updKeep ht) ht.mem),
      by rw [ht.mem, ea], ?_⟩
    rw [ht.gpr, ka.keep.esi, hb, hz, Bool.true_and]
  · intro hn
    refine WP.mono (returnFlag_ok a x false) fun t ⟨kt, mt, rt⟩ => ⟨ka.trans kt, by rw [mt, ea], ?_⟩
    rw [rt, hn, Bool.false_and]

theorem recoverSign_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa recoverSign s fun t => FieldKeep x s t ∧
      DecodeResult x (signResult (env s.mem x 0) (env s.mem x 1) b) t := by
  refine WP.seq (WP.mono (recoverZero_ok hc b hb) fun a ⟨ka, ea, ra⟩ => ?_)
  refine WP.seq (WP.mono (flagTest_ok x _ ra) fun c ⟨kc, mc, zc⟩ => ?_)
  have kac := ka.trans kc
  have ec : env c.mem x = env s.mem x := by rw [mc, ea]
  apply WP.ite _ zc
  · intro ht
    refine WP.mono (recoverInvalid_ok c x) fun t ⟨kt, tr⟩ => ⟨kac.trans kt, ?_⟩
    simpa only [signResult, ht, ite_true] using tr
  · intro hf
    refine WP.mono (recoverAdjustSign_ok (kac.ctx hc) b (kac.keep.esi.trans hb)) fun t ⟨kt, rt, pt⟩ => ?_
    refine ⟨kac.trans kt, ?_⟩
    simp only [signResult, hf, Bool.false_eq_true, ite_false, DecodeResult]
    exact ⟨rt, by rw [ec] at pt; exact pt⟩

end VG.Proof.Ed25519.X86
