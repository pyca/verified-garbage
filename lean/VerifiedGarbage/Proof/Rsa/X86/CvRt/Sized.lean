module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.CvRt.Store
import VerifiedGarbage.Proof.Bignum.MemoryFrame
public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Load
import VerifiedGarbage.Proof.Rsa.X86.InvParts

/-! # CRT parameter calculation at a run-time width, once the modulus is accepted

`sized_ok`: the inputs loaded, the arithmetic, and the outputs released
under the checks' mask, as `ArithmeticPost` states them.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys (hdr seqs aZero)
open VG.Impl.Rsa.X86.CrtValues (sMask nArr)
open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Proof.Rsa.X86.Keys (Keep num slot wp_seqs_cons)
open VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.CrtValues (CallGeometry Inputs inputBytes bodyWrites)

def encode (g : CallGeometry) (accept : Bool) (i : Fin 3) (x : Nat) : List Byte :=
  Spec.Rsa.i2osp ((if accept then x else 0) % 2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len

def ArithmeticPost (g : CallGeometry) (m : Mem) (t : State) : Prop :=
  let a := arithmeticGeometry g m
  ∃ X₁ X₂ V R₂ R₃ X : Nat,
    (0 < a.P → X₁ = a.N / a.P ∧ X₂ = a.N % a.P) ∧
    (1 < a.M → V = Nat.gcd a.Q a.M ∧ (a.M : Int) ∣ (X : Int) * a.Q - V ∧ X < a.M) ∧
    (0 < 2 * (a.P / 2) → R₂ = a.D % (2 * (a.P / 2))) ∧
    (0 < 2 * (a.Q / 2) → R₃ = a.D % (2 * (a.Q / 2))) ∧
    Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = encode g (maskOf a.P a.Q X₁ X₂ V) 0 R₂ ∧
    Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = encode g (maskOf a.P a.Q X₁ X₂ V) 1 R₃ ∧
    Spec.Rsa.bytesAt t.mem (g.buffer 4).base (g.buffer 4).len = encode g (maskOf a.P a.Q X₁ X₂ V) 2 X ∧
    t.gpr .eax = BitVec.ofNat 32 (maskOf a.P a.Q X₁ X₂ V).toNat

theorem sized_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa sized s fun t => Inputs g t ∧ ArithmeticPost g s.mem t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw := h.ws.workspace.nowrap
  unfold sized
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h len) fun u ⟨hu, start, ou, ru⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (core_ok start) fun v ⟨kv, rv, zero, X₁, X₂, division, computed⟩ => ?_
  have ru' := inputsRt hu len
  have ov := keep_outside ru'.ws kv (by decide) (by decide)
  have kwEq : kw (g.args 7).toNat = 2 * g.n := by rw [len.width]
  have kv' : Keep g.base (2 * g.n) coreArrays coreSlots u.mem v.mem := by rw [← kwEq]; exact kv
  have bv := hu.keepBody kv' (by decide) (by decide)
  have hv := hu.after rv (by decide) (by decide) (scratchFrame hu ov)
  obtain ⟨V, mask, inverse⟩ := computed.mask
  refine WP.mono (stores_ok hv len zero _ mask) fun t ⟨ht, dp, dq, qi, status, frame, rest⟩ => ?_
  refine ⟨ht, ?_, ?_, ru.trans ((rv.mono (by decide)).trans rest)⟩
  · exact ⟨X₁, X₂, V, _, _, _, division, inverse, computed.remP, computed.remQ, dp, dq, qi, status⟩
  · have prior := outside_frame (ou.trans bv) (by omega)
    exact (prior.mono (by simp [bodyWrites])).trans frame

end VG.Proof.Rsa.X86.CrtValuesRt
