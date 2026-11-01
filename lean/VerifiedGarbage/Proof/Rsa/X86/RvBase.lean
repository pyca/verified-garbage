module

import VerifiedGarbage.Proof.Rsa.X86.RvViews
public import VerifiedGarbage.Impl.Rsa.X86.Recover
public import VerifiedGarbage.Proof.Rsa.X86.KeyArrs
public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # Workspace geometry and tracked stages for i686 prime recovery

The arrays are `RecoverRt`'s, of the run-time width's `nar` and `wid`
shapes: `w = 2 n + 2` and `W = 2 w + 2` words for the modulus's `n` 64-bit
words. A stage changes only the working space past its first 16 bytes and
the 40 bytes below the stack pointer `sp`, where the calls of
`vg_rsa_mont_mul_at` put their frames.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

structure Geo where
  B : Addr
  Z : Nat
  n : Nat
  sp : BitVec 32
  args : Nat → BitVec 32
  wr : List Region

abbrev Geo.w (g : Geo) : Nat := width g.n
abbrev Geo.W (g : Geo) : Nat := wide g.n
abbrev opRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]
abbrev SlotOk (d : Nat) : Prop := 16 ≤ d ∧ d + 4 ≤ hdr ∧ d % 4 = 0

theorem arrW_end (g : Geo) : arr g.W 22 = arr g.w nArr := by
  rw [Geo.W, wide, arr_W]
  rfl

theorem kw_nar (n : Nat) : VG.Proof.Rsa.X86.KeyRt.kw (8 * n + 8) = width n := by
  simp only [VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords, width]; omega

theorem kw_wid (n : Nat) : VG.Proof.Rsa.X86.KeyRt.kw (16 * n + 24) = wide n := by
  simp only [VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords, wide, width]; omega

/-- What a stage may change: the working space past its first 16 bytes, and the 40 bytes below `sp`. -/
abbrev stageR (g : Geo) : List Region := VG.Proof.Bignum.X86.CrtRt.frameR g.B g.sp [(16, g.Z - 16)]

theorem ws_wide {g : Geo} {s : State} (h : Ws s g.B g.Z g.w nArr) (hi : g.n ≤ 128) :
    Ws s g.B g.Z g.W 22 := by
  refine ⟨h.workspace, ?_, ?_, ?_⟩
  · rw [arrW_end]; exact h.fits
  · change 0 < 2 * (2 * g.n + 2) + 2; omega
  · change 2 * (2 * g.n + 2) + 2 ≤ 1024; omega

/-- What a stage's run starts from: its writable regions, and the call's arguments, apart from what the stage
writes. -/
def Start (g : Geo) (s0 : State) : Prop :=
  s0.wr = g.wr ∧ ∀ i < 12, VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z i (g.args i) ∧
    ∀ r ∈ stageR g, Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress s0 i, 4⟩ r

/-- A stage tracks both array widths and the scalar header words. -/
structure KS (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat)
    (AW : Nat → Nat) (liveW : List Nat) (V : Nat → Nat) (ls : List Nat) (s : State) : Prop where
  rt : VG.Proof.Rsa.X86.KeyRt.RtWs VG.Impl.Rsa.X86.RecoverRt.nar s g.B g.Z (8 * g.n + 8) nArr
  lower : 8 ≤ g.n
  upper : g.n ≤ 128
  frame : Frame (stageR g) s0.mem s.mem
  sp : s.gpr .esp = g.sp
  room : VG.Proof.Mont.X86.CallRoom g.sp g.B g.Z
  top : g.sp.toNat + 52 ≤ 2 ^ 32
  wsLen : VG.Proof.Bignum.X86.CallArgument s g.B g.Z 11 (BitVec.ofNat 32 (g.Z / 8))
  z8 : g.Z % 8 = 0
  rest : Keeps opRegs s0 s
  arrs : Arrs s.mem g.B g.w A live
  arrsW : Arrs s.mem g.B g.W AW liveW
  sl : ∀ d ∈ ls, slot s.mem g.B d = V d
  live_lt : ∀ j ∈ live, j < nArr
  liveW_lt : ∀ j ∈ liveW, j < 22
  ls_ok : ∀ d ∈ ls, SlotOk d
  start : Start g s0

section
variable {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.ws (h : KS g s0 A live AW liveW V ls s) : Ws s g.B g.Z g.w nArr := by
  have w := h.rt.ws
  rwa [kw_nar] at w

/-- The wide arrays at the run-time width. -/
theorem KS.rtW (h : KS g s0 A live AW liveW V ls s) :
    VG.Proof.Rsa.X86.KeyRt.RtWs VG.Impl.Rsa.X86.RecoverRt.wid s g.B g.Z (16 * g.n + 24) 22 := by
  have up := h.upper
  obtain ⟨a, la, ea, ca⟩ := h.rt.lenArg
  refine ⟨?_, ⟨a, la, ?_, ca⟩, h.rt.wsArg, by omega, h.rt.layLen⟩
  · rw [kw_wid]; exact ws_wide h.ws up
  · simp only [VG.Impl.Rsa.X86.KeyRt.Lay.toLen, VG.Impl.Rsa.X86.RecoverRt.lay, VG.Proof.Rsa.X86.KeyRt.kw,
      VG.Proof.Bignum.X86.PublicRt.wb, Spec.Rsa.modulusWords] at ea ⊢
    omega

/-- The workspace changes inside the stage's regions. -/
theorem outside_stage {g : Geo} {m m' : Mem} (O : Outside g.B 16 (g.Z - 16) m m') (fit : g.B.toNat + g.Z ≤ 2 ^ 64)
    (hz : 16 ≤ g.Z) : Frame (stageR g) m m' :=
  (VG.Proof.Bignum.outside_frame O (by omega)).mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    simp [VG.Proof.Bignum.X86.CrtRt.frameR]

theorem KS.wsW (h : KS g s0 A live AW liveW V ls s) : Ws s g.B g.Z g.W 22 :=
  ws_wide h.ws h.upper

theorem KS.of_rest (h : KS g s0 A live AW liveW V ls s) {rs : List Reg}
    (r : Keeps rs s t) (hr : ∀ x ∈ rs, x ∈ opRegs) (mem : t.mem = s.mem) :
    KS g s0 A live AW liveW V ls t :=
  have edi : Reg.edi ∉ rs := fun e => by have := hr _ e; simp [opRegs] at this
  have esp : Reg.esp ∉ rs := fun e => by have := hr _ e; simp [opRegs] at this
  ⟨h.rt.keep r edi esp (by rw [mem]; exact fun _ _ => rfl),
    h.lower, h.upper, mem ▸ h.frame, by rw [r.1 _ esp]; exact h.sp, h.room, h.top,
    h.wsLen.keep r esp (by rw [mem]; exact fun _ _ => rfl), h.z8, h.rest.trans (r.mono hr),
    mem ▸ h.arrs, mem ▸ h.arrsW, mem ▸ h.sl, h.live_lt, h.liveW_lt, h.ls_ok, h.start⟩

theorem KS.mono (h : KS g s0 A live AW liveW V ls s)
    {A' : Nat → Nat} {live' : List Nat} {AW' : Nat → Nat} {liveW' : List Nat}
    {V' : Nat → Nat} {ls' : List Nat}
    (hl : ∀ j ∈ live', j ∈ live ∧ A j = A' j)
    (hlW : ∀ j ∈ liveW', j ∈ liveW ∧ AW j = AW' j)
    (hls : ∀ d ∈ ls', d ∈ ls ∧ V d = V' d) : KS g s0 A' live' AW' liveW' V' ls' s :=
  ⟨h.rt, h.lower, h.upper, h.frame, h.sp, h.room, h.top, h.wsLen, h.z8, h.rest,
    fun j hj => (h.arrs j (hl j hj).1).trans (hl j hj).2,
    fun j hj => (h.arrsW j (hlW j hj).1).trans (hlW j hj).2,
    fun d hd => (h.sl d (hls d hd).1).trans (hls d hd).2,
    fun j hj => h.live_lt j (hl j hj).1,
    fun j hj => h.liveW_lt j (hlW j hj).1,
    fun d hd => h.ls_ok d (hls d hd).1, h.start⟩

/-- A step that keeps the header's first 16 bytes keeps everything outside the stage's range. -/
theorem keepBody_of {g : Geo} {m m' : Mem} (header : hdr ≤ g.Z) {v : Nat} {js ds : List Nat}
    (k : Keep g.B v js ds m m') (hj : ∀ j ∈ js, arr v j + S v ≤ g.Z)
    (hd : ∀ d ∈ ds, SlotOk d) : Outside g.B 16 (g.Z - 16) m m' := by
  intro a ha
  apply k a
  intro r hr
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, jm, rfl⟩ | ⟨d, dm, rfl⟩
  · have bound := hj j jm
    have lower : hdr ≤ arr v j := Nat.le_add_right _ _
    dsimp only
    unfold hdr at header lower
    omega
  · have bound := hd d dm
    dsimp only
    unfold SlotOk hdr at bound
    unfold hdr at header
    omega

theorem KS.keepBody (h : KS g s0 A live AW liveW V ls s) {v : Nat} {js ds : List Nat}
    (k : Keep g.B v js ds s.mem t.mem) (hj : ∀ j ∈ js, arr v j + S v ≤ g.Z)
    (hd : ∀ d ∈ ds, SlotOk d) : Outside g.B 16 (g.Z - 16) s.mem t.mem :=
  keepBody_of h.ws.hdr_le k hj hd

theorem KS.core (h : KS g s0 A live AW liveW V ls s) {v : Nat} {js ds : List Nat}
    (k : Keep g.B v js ds s.mem t.mem) (hj : ∀ j ∈ js, arr v j + S v ≤ g.Z)
    (hd : ∀ d ∈ ds, SlotOk d) (r : Keeps opRegs s t)
    {A' : Nat → Nat} {live' : List Nat} {AW' : Nat → Nat} {liveW' : List Nat}
    {V' : Nat → Nat} {ls' : List Nat}
    (ha : Arrs t.mem g.B g.w A' live') (hl : ∀ j ∈ live', j < nArr)
    (haW : Arrs t.mem g.B g.W AW' liveW') (hlW : ∀ j ∈ liveW', j < 22)
    (hsl : ∀ d ∈ ls', slot t.mem g.B d = V' d) (hls : ∀ d ∈ ls', SlotOk d) :
    KS g s0 A' live' AW' liveW' V' ls' t :=
  have header := h.ws.hdr_le
  have O := h.keepBody k hj hd
  have nw := h.ws.workspace.nowrap
  ⟨h.rt.keep r (by decide) (by decide) (O.mono (Nat.zero_le _) (by unfold hdr at header; omega)),
    h.lower, h.upper, h.frame.trans (outside_stage O (by omega) (by unfold hdr at header; omega)),
    by rw [r.1 _ (by decide)]; exact h.sp, h.room, h.top,
    h.wsLen.keep r (by decide) (O.mono (Nat.zero_le _) (by unfold hdr at header; omega)), h.z8,
    h.rest.trans r, ha, haW, hsl, hl, hlW, hls, h.start⟩

end
end VG.Proof.Rsa.X86.Recover
