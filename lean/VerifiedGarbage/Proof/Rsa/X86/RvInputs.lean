module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame

/-! # Input and output geometry of the prime-recovery call -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

structure CallGeometry extends Geo where
  args : Nat → BitVec 32

def CallGeometry.buffer (g : CallGeometry) (i : Nat) : Region :=
  ⟨byteAddr (g.args i), (g.args (i + 1)).toNat⟩

def CallGeometry.writes (g : CallGeometry) : List Region :=
  [⟨g.B, g.Z⟩, g.buffer 0, g.buffer 2]

structure Inputs (g : CallGeometry) (s : State) : Prop where
  ws : Ws s g.B g.Z g.toGeo.w nArr
  lower : 8 ≤ g.n
  upper : g.n ≤ 128
  arguments : ∀ i, i < 12 → CallArgument s g.B g.Z i (g.args i)
  stackApart : ∀ i, i < 12 → ∀ r ∈ g.writes, Region.Disjoint ⟨stackAddress s i, 4⟩ r
  inputPositive : ∀ j : Fin 3, 0 < (g.buffer (4 + 2 * j.val)).len
  inputBound : ∀ j : Fin 3, (g.buffer (4 + 2 * j.val)).len ≤ 8 * g.n
  inputFit : ∀ j : Fin 3, (g.args (4 + 2 * j.val)).toNat + (g.buffer (4 + 2 * j.val)).len ≤ 2 ^ 32
  inputRead : ∀ j : Fin 3, InRegions (s.rd ++ s.wr) (g.buffer (4 + 2 * j.val)).base (g.buffer (4 + 2 * j.val)).len
  inputApart : ∀ j : Fin 3, ∀ r ∈ g.writes, (g.buffer (4 + 2 * j.val)).Disjoint r
  outputPositive : ∀ j : Fin 2, 0 < (g.buffer (2 * j.val)).len
  outputBound : ∀ j : Fin 2, (g.buffer (2 * j.val)).len ≤ 8 * g.n
  outputFit : ∀ j : Fin 2, (g.args (2 * j.val)).toNat + (g.buffer (2 * j.val)).len ≤ 2 ^ 32
  outputWrite : ∀ j : Fin 2, InRegions s.wr (g.buffer (2 * j.val)).base (g.buffer (2 * j.val)).len
  outputScratch : ∀ j : Fin 2, (g.buffer (2 * j.val)).Disjoint ⟨g.B, g.Z⟩
  outputSeparate : ∀ i j : Fin 2, i ≠ j → (g.buffer (2 * i.val)).Disjoint (g.buffer (2 * j.val))

theorem Inputs.after {g : CallGeometry} {s t : State} {regs : List Reg} (h : Inputs g s)
    (rest : Keeps regs s t) (di : .edi ∉ regs) (sp : .esp ∉ regs) (frame : Frame g.writes s.mem t.mem) :
    Inputs g t := by
  refine ⟨h.ws.rest rest di sp, h.lower, h.upper, ?_, ?_, h.inputPositive, h.inputBound,
    h.inputFit, ?_, h.inputApart, h.outputPositive, h.outputBound, h.outputFit, ?_, h.outputScratch,
    h.outputSeparate⟩
  · exact fun i hi => (h.arguments i hi).frame rest sp frame (h.stackApart i hi)
  · intro i hi r hr
    rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, rest.1 _ sp]]
    exact h.stackApart i hi r hr
  · intro j; rw [rest.2.1, rest.2.2]; exact h.inputRead j
  · intro j; rw [rest.2.2]; exact h.outputWrite j

theorem Inputs.keepBody {g : CallGeometry} {s : State} {m : Mem} {js ds : List Nat}
    (h : Inputs g s) (keep : Keep g.B g.toGeo.w js ds s.mem m)
    (hj : ∀ j ∈ js, j < nArr) (hd : ∀ d ∈ ds, SlotOk d) :
    Outside g.B 16 (g.Z - 16) s.mem m := by
  have ks : KS g.toGeo s (fun _ => 0) [] (fun _ => 0) [] (fun _ => 0) [] s :=
    ⟨h.ws, h.lower, h.upper, Outside.refl _ _ _ _, Keeps.refl _ _, by simp [Arrs], by simp [Arrs],
      by simp, by simp, by simp, by simp⟩
  exact ks.keepBody (t := {s with mem := m}) keep (fun j hm => h.ws.arr_fit (hj j hm)) hd

theorem Inputs.scratchFrame {g : CallGeometry} {s : State} (h : Inputs g s) {m m' : Mem}
    (frame : Outside g.B 16 (g.Z - 16) m m') : Frame g.writes m m' := by
  have out : Outside g.B 0 g.Z m m' :=
    frame.mono (by decide) (by have := h.ws.hdr_le; unfold hdr at this; omega)
  have f := outside_frame out (by have := h.ws.workspace.nowrap; omega)
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    f.mono (rs' := g.writes) (by simp [CallGeometry.writes, off])

theorem Inputs.of_KS {g : CallGeometry} {s t : State} {A AW V : Nat → Nat}
    {live liveW ls : List Nat} (h : Inputs g s)
    (ks : KS g.toGeo s A live AW liveW V ls t) : Inputs g t :=
  h.after ks.rest (by decide) (by decide) (h.scratchFrame ks.frame)

end VG.Proof.Rsa.X86.Recover
