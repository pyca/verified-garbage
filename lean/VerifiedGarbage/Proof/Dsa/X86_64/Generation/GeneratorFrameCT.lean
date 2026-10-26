module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorArguments
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoadsCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorArguments
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToDual

/-! # Bind public generator inputs through the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Dsa.Generation.Layout

structure GeneratorFramePublic where
  B : Addr
  F : Addr
  arena : Addr
  hp : Addr
  Z : Nat
  w : Nat
  pb : List Byte
  xb : List Byte
  pLength : pb.length = 8 * w
  xLength : xb.length = pb.length
  separate : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8

def GeneratorFramePublic.loads (c : GeneratorFramePublic) (result : Bool) : GeneratorLoadPublic :=
  ⟨⟨c.B, c.Z, c.w, off c.arena p, c.pb⟩, if result then off c.arena g else c.hp, c.xb⟩

def GeneratorFramePublic.pointers (c : GeneratorFramePublic) : ArgumentPointers := ⟨c.B, c.F⟩

structure GeneratorFrameInputs (result : Bool) (c : GeneratorFramePublic) (s : State) : Prop where
  stack : s.gpr .rsp = c.F
  read : ∀ k < 37, InRegions (s.rd ++ s.wr) (off c.F (8 * k)) 8
  arena : word s.mem c.F 40 = c.arena
  candidate : word s.mem c.F 168 = c.hp
  modulus : Src s c.B c.Z (off c.arena p) c.pb
  source : Src s c.B c.Z (if result then off c.arena g else c.hp) c.xb
  odd : result = false → Spec.Rsa.os2ip c.pb % 2 = 1

def GeneratorFrameBefore (len : Nat) (result : Bool) (c : GeneratorFramePublic) (s : State) : Prop :=
  GeneratorFrameInputs result c s ∧ Ws s c.B c.Z c.w ∧ c.pb.length = len

def GeneratorFrameLoaded (result : Bool) (c : GeneratorFramePublic) (s : State) : Prop :=
  GeneratorLoadBefore (c.loads result) s ∧ (result = false → Spec.Rsa.os2ip c.pb % 2 = 1)

theorem generatorFrame_ready {len : Nat} {result : Bool} {c : GeneratorFramePublic} {s : State}
    (h : GeneratorFrameBefore len result c s) :
    WP isa (.block (headerArguments (generatorRangeArguments len result))) s (GeneratorFrameLoaded result c) := by
  have hl : len < 2 ^ 31 := by omega_using [h.2.1.w2, c.pLength, h.2.2]
  refine WP.mono (generatorArguments_ok h.2.1 hl result h.1.stack h.1.read
    (W := fun k => word s.mem c.F (8 * k)) (fun _ _ => rfl) c.separate)
    fun t ⟨ht, hp, hpl, hx, hxl, hf, hk⟩ => ?_
  have frame : Frm c.B [(128, 128)] s.mem t.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(128, 128)], r.1 + r.2 ≤ c.Z := by
    simp only [List.mem_singleton, forall_eq]; exact h.2.1.h256
  have sp := h.1.modulus.congrK (InScr.of_frm frame bound) hk
  have sx := h.1.source.congrK (InScr.of_frm frame bound) hk
  have pp : word t.mem c.B 128 = off c.arena p := by simpa only [h.1.arena] using hp
  have xp : word t.mem c.B 144 = if result then off c.arena g else c.hp := by
    simpa only [h.1.arena, h.1.candidate] using hx
  have pl : word t.mem c.B 136 = BitVec.ofNat 64 c.pb.length := by rw [h.2.2]; exact hpl
  have xl : word t.mem c.B 152 = BitVec.ofNat 64 c.xb.length := by
    rw [c.xLength, h.2.2]; exact hxl
  have positive : 1 ≤ c.pb.length := by omega_using [c.pLength, h.2.1.w1]
  exact ⟨⟨⟨ht, pp, pl, sp, positive, Nat.le_of_eq c.pLength⟩,
    ⟨ht, xp, xl, sx, c.xLength ▸ positive, Nat.le_of_eq (c.xLength.trans c.pLength)⟩⟩, h.1.odd⟩

theorem generatorFrame_ct (len : Nat) (result : Bool)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .rsp])
      (.block (headerArguments (generatorRangeArguments len result))) hc).isSome = true) :
    RelCT isa (Two (GeneratorFrameBefore len result))
      (.seq (.block (headerArguments (generatorRangeArguments len result)))
        (if result then generatorResult else generatorRange)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map GeneratorFramePublic.pointers
    (fun _ _ h => ⟨h.2.1.rdi, h.1.stack⟩)
    (two_taint [.rdi, .rsp] argumentRegisters_pins ht))
    (fun _ _ h => generatorFrame_ready h)) ?_
  cases result
  · exact two_map (fun c : GeneratorFramePublic => c.loads false)
      (fun _ _ h => ⟨h.1, h.2 rfl⟩) generatorRange_ct
  · exact two_map (fun c : GeneratorFramePublic => c.loads true)
      (fun _ _ h => h.1) generatorResult_ct

end VG.Proof.Dsa.X86_64.Generation
