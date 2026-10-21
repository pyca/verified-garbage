module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! # The retained header and buffer permissions survive scratch arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

structure Input (E : Environment) (s : State) : Prop where
  valid : E.Valid
  ws : Ws s E.base E.size E.n 32
  arguments : ∀ i < 18, s.mem.readW (off E.base (4 * i)) 32 = E.argument i
  outWrite : ∀ i < 7, InRegions s.wr (E.outputRegion i).base (E.outputRegion i).len
  exponentRead : InRegions (s.rd ++ s.wr) E.exponentRegion.base E.exponentRegion.len

theorem Input.outputs {E : Environment} {s : State} (h : Input E s) : OutputInput E.outputs s := by
  refine ⟨h.ws, h.valid.outputs, fun i hi => h.arguments i (by omega), ?_⟩
  intro i hi
  rw [h.valid.outputRegion hi]
  exact h.outWrite i hi

theorem Input.keep {E : Environment} {s t : State} {rs : List Reg} (h : Input E s)
    (ws : Ws t E.base E.size E.n 32) (K : Keeps rs s t)
    (header : ∀ d, d + 4 ≤ 72 → t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32) : Input E t := by
  refine ⟨h.valid, ws, ?_, ?_, ?_⟩
  · intro i hi
    rw [header (4 * i) (by omega)]
    exact h.arguments i hi
  · intro i hi
    rw [K.2.2]
    exact h.outWrite i hi
  · rw [K.2.1, K.2.2]
    exact h.exponentRead

theorem Input.afterOuts {E : Environment} {s t : State} {regs : List Reg} {rs : List (Nat × Nat)}
    (h : Input E s) (ws : Ws t E.base E.size E.n 32) (K : Keeps regs s t)
    (lower : ∀ r ∈ rs, 72 ≤ r.1) (O : Outs E.base rs s.mem t.mem) : Input E t := by
  apply h.keep ws K
  intro d hd
  apply BitVec.eq_of_toNat_eq
  have H : val32 t.mem E.base d 1 = val32 s.mem E.base d 1 :=
    O.val32 (d := d) (k := 1) (fun r hr => Or.inl (Nat.le_trans hd (lower r hr))) (by omega)
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem Input.afterStage {E : Environment} {s t : State} {regs : List Reg} {js : List Nat}
    (h : Input E s) (ws : Ws t E.base E.size E.n 32) (K : Keeps regs s t)
    (O : Outs E.base (stageRanges E.n js) s.mem t.mem) : Input E t := by
  apply h.keep ws K
  intro d hd
  apply BitVec.eq_of_toNat_eq
  have H := stage_preserves_header (n := E.n) (d := d) (count := 1)
    (by change d + 4 ≤ VG.Impl.RsaKeyGen.X86.Key.kOk; unfold VG.Impl.RsaKeyGen.X86.Key.kOk; omega) O
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

end VG.Proof.RsaKeyGen.X86.Key
