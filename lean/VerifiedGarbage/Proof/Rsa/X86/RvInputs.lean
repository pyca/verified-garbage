module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame
import VerifiedGarbage.Proof.Weierstrass.Env

/-! # Input and output geometry of the prime-recovery call -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

structure CallGeometry extends Geo

def CallGeometry.buffer (g : CallGeometry) (i : Nat) : Region :=
  ⟨byteAddr (g.args i), (g.args (i + 1)).toNat⟩

/-- What the call may write: the working space, the outputs, and the 40 bytes below `sp`, where the
calls of `vg_rsa_mont_mul_at` put their frames. -/
def CallGeometry.writes (g : CallGeometry) : List Region :=
  [⟨g.B, g.Z⟩, g.buffer 0, g.buffer 2, VG.X86.below g.sp 40]

/-- The modulus's length (argument 5), of the width the arrays have, and the working space argument
at the working space. -/
structure Lengths (g : CallGeometry) : Prop where
  lower : 64 ≤ (g.args 5).toNat
  upper : (g.args 5).toNat ≤ 1024
  width : g.n = Spec.Rsa.modulusWords (g.args 5).toNat
  scratch : g.args 10 = BitVec.ofNat 32 g.B.toNat
  bytes : g.Z = (g.args 11).toNat * 8
  pLen : g.args 1 = g.args 5
  qLen : g.args 3 = g.args 5

structure Inputs (g : CallGeometry) (s : State) : Prop where
  ws : Ws s g.B g.Z g.toGeo.w nArr
  lower : 8 ≤ g.n
  upper : g.n ≤ 128
  esp : s.gpr .esp = g.sp
  room : VG.Proof.Mont.X86.CallRoom g.sp g.B g.Z
  top : g.sp.toNat + 52 ≤ 2 ^ 32
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
  wrEq : s.wr = g.wr

theorem Inputs.after {g : CallGeometry} {s t : State} {regs : List Reg} (h : Inputs g s)
    (rest : Keeps regs s t) (di : .edi ∉ regs) (sp : .esp ∉ regs) (frame : Frame g.writes s.mem t.mem) :
    Inputs g t := by
  refine ⟨h.ws.rest rest di sp, h.lower, h.upper, by rw [rest.1 _ sp]; exact h.esp, h.room, h.top, ?_, ?_, h.inputPositive, h.inputBound,
    h.inputFit, ?_, h.inputApart, h.outputPositive, h.outputBound, h.outputFit, ?_, h.outputScratch,
    h.outputSeparate, by rw [rest.2.2]; exact h.wrEq⟩
  · exact fun i hi => (h.arguments i hi).frame rest sp frame (h.stackApart i hi)
  · intro i hi r hr
    rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, rest.1 _ sp]]
    exact h.stackApart i hi r hr
  · intro j; rw [rest.2.1, rest.2.2]; exact h.inputRead j
  · intro j; rw [rest.2.2]; exact h.outputWrite j

theorem Inputs.keepBody {g : CallGeometry} {s : State} {m : Mem} {js ds : List Nat}
    (h : Inputs g s) (keep : Keep g.B g.toGeo.w js ds s.mem m)
    (hj : ∀ j ∈ js, j < nArr) (hd : ∀ d ∈ ds, SlotOk d) :
    Outside g.B 16 (g.Z - 16) s.mem m :=
  keepBody_of h.ws.hdr_le keep (fun j hm => h.ws.arr_fit (hj j hm)) hd

/-- The narrow arrays at the run-time width. -/
theorem Inputs.rt {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    VG.Proof.Rsa.X86.KeyRt.RtWs VG.Impl.Rsa.X86.RecoverRt.nar s g.B g.Z (8 * g.n + 8) nArr := by
  have ws : Ws s g.B g.Z (VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8)) nArr := by rw [kw_nar]; exact h.ws
  have up := h.upper
  refine ⟨ws, ⟨_, len.upper, ?_, ?_⟩, ?_, by omega, by decide⟩
  · simp only [VG.Impl.Rsa.X86.KeyRt.Lay.toLen, VG.Impl.Rsa.X86.RecoverRt.lay, VG.Proof.Rsa.X86.KeyRt.kw,
      Spec.Rsa.modulusWords, len.width]
    omega
  · have a := h.arguments 5 (by decide)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← len.scratch]; exact h.arguments 10 (by decide)

theorem Inputs.scratchFrame {g : CallGeometry} {s : State} (h : Inputs g s) {m m' : Mem}
    (frame : Outside g.B 16 (g.Z - 16) m m') : Frame g.writes m m' := by
  have out : Outside g.B 0 g.Z m m' :=
    frame.mono (by decide) (by have := h.ws.hdr_le; unfold hdr at this; omega)
  have f := outside_frame out (by have := h.ws.workspace.nowrap; omega)
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    f.mono (rs' := g.writes) (by simp [CallGeometry.writes, off])

/-- What a stage changes, within what the call may write. -/
theorem stage_writes (g : CallGeometry) (hz : 16 ≤ g.Z) :
    ∀ r ∈ stageR g.toGeo, ∃ r' ∈ g.writes, Region.Sub r r' := by
  intro r hr
  simp only [stageR, VG.Proof.Bignum.X86.CrtRt.frameR, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp [CallGeometry.writes], fun _ h => h⟩
  · exact ⟨⟨g.B, g.Z⟩, by simp [CallGeometry.writes], VG.Offset.sub_base _ (by omega)⟩

/-- The working space's length argument, at its length in `u64`s. -/
theorem Inputs.wsLen {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    CallArgument s g.B g.Z 11 (BitVec.ofNat 32 (g.Z / 8)) := by
  have a := h.arguments 11 (by decide)
  have e : g.Z / 8 = (g.args 11).toNat := by rw [len.bytes]; omega
  rwa [e, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- An argument's word lies apart from what a stage changes. -/
theorem Inputs.stageApart {g : CallGeometry} {s : State} (h : Inputs g s) {i : Nat} (hi : i < 12) :
    ∀ r ∈ stageR g.toGeo, Region.Disjoint ⟨stackAddress s i, 4⟩ r := fun r hr => by
  obtain ⟨r', hr', sub⟩ := stage_writes g (by have := h.ws.hdr_le; unfold hdr at this; omega) r hr
  exact (h.stackApart i hi r' hr').sub_right sub

theorem Inputs.of_KS {g : CallGeometry} {s t : State} {A AW V : Nat → Nat}
    {live liveW ls : List Nat} (h : Inputs g s)
    (ks : KS g.toGeo s A live AW liveW V ls t) : Inputs g t :=
  h.after ks.rest (by decide) (by decide) (ks.frame.sub (stage_writes g (by have := h.ws.hdr_le; unfold hdr at this; omega)))

end VG.Proof.Rsa.X86.Recover
