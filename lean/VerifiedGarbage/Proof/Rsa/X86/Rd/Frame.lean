module

public import VerifiedGarbage.Proof.Rsa.X86.KeyArrs
import VerifiedGarbage.Proof.Rsa.KeyViews
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Compare
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Rsa.Sub32
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays

/-!
# `vg_rsa_recover_primes_det` on i686: the stages' framework

The numbers of the key working space read with `w` and with `W = 2 w + 2`
words; the state every stage keeps, and its frame; writes to arrays and
slots; the array operations on a stage, the flags, the arguments, and the
division's and the batched GCD's set-up.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Impl.Rsa.X86.Keys VG.Proof.Rsa.X86.Keys

theorem arr_W (w j : Nat) : arr (2 * w + 2) j = arr w (2 * j) :=
  VG.Proof.Rsa.KeyWorkspace.arr_W w j

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.X86.Recover VG.Impl.Rsa.X86.Keys

/-- A step that keeps the arrays read with `w` but `js` keeps the arrays
read with `W` but those that contain them. -/
theorem Keep.toW {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem} (k : Keep B w js ds m m') :
    Keep B (2 * w + 2) (js.map (· / 2)) ds m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.toW k

/-- A step that keeps the arrays read with `W` but `js` keeps the arrays
read with `w` but the two in each. -/
theorem Keep.ofW {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (k : Keep B (2 * w + 2) js ds m m') :
    Keep B w (js.flatMap fun j => [2 * j, 2 * j + 1]) ds m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.ofW k

/-- The arrays a step does not change keep their values, given that they
fit in the address space. -/
theorem Arrs.keepOf {m m' : Mem} {B : Addr} {v : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B v A live) {js ds : List Nat} (k : Keep B v js ds m m')
    (hl : ∀ j ∈ live, ∀ i ∈ js, i ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : ∀ j ∈ live, arr v j + S v ≤ 2 ^ 64) : Arrs m' B v A live :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.keepOf h k hl hd fit

/-- The arrays after a step that writes `[o] := x` alone. -/
theorem Arrs.upd1 {m m' : Mem} {B : Addr} {v : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B v A live) {o x : Nat} {ds : List Nat} (k : Keep B v [o] ds m m')
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (fit : ∀ j ∈ live, arr v j + S v ≤ 2 ^ 64)
    (e : num m' B v o = x) : Arrs m' B v (upd A o x) (o :: live) :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.upd1 h k hd fit e

end VG.Proof.Rsa.X86.Keys

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Impl.Rsa.X86.Keys VG.Proof.Rsa.X86.Keys

/-- A number of `W` words: the `w + 2` words of array `2 j` and the `w`
words of array `2 j + 1`. -/
theorem numW (m : Mem) (B : Addr) (w j : Nat) :
    num m B (2 * w + 2) j = val32 m B (arr w (2 * j)) (w + 2) +
      2 ^ (32 * (w + 2)) * num m B w (2 * j + 1) :=
  VG.Proof.Rsa.KeyWorkspace.numW m B w j

theorem numW_of {m : Mem} {B : Addr} {w j x : Nat}
    (h0 : val32 m B (arr w (2 * j)) (w + 2) = x) (h1 : num m B w (2 * j + 1) = 0) :
    num m B (2 * w + 2) j = x :=
  VG.Proof.Rsa.KeyWorkspace.numW_of h0 h1

end VG.Proof.Rsa.X86.Recover

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

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- The arrays read with `w` that a step with `w` words does not write. -/
theorem KS.arrs_w {js ds : List Nat} (h : KS g s0 A live AW liveW V ls s) (k : Keep g.B g.w js ds s.mem t.mem)
    (hl : ∀ j ∈ live, ∀ i ∈ js, i ≠ j) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem g.B g.w A live :=
  h.arrs.keepOf k hl (fun d hd => (hds d hd).2.1) fun j hj => h.ws.fit64 (h.live_lt j hj)

/-- The arrays read with `W` that a step with `w` words does not write. -/
theorem KS.arrsW_w {js ds : List Nat} (h : KS g s0 A live AW liveW V ls s) (k : Keep g.B g.w js ds s.mem t.mem)
    (hl : ∀ j ∈ liveW, ∀ i ∈ js, i / 2 ≠ j) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem g.B g.W AW liveW :=
  h.arrsW.keepOf k.toW (fun j hj i hi => by
      simp only [List.mem_map] at hi
      obtain ⟨i', hi', rfl⟩ := hi
      exact hl j hj i' hi') (fun d hd => (hds d hd).2.1) fun j hj => h.wsW.fit64 (h.liveW_lt j hj)

/-- The arrays read with `w` that a step with `W` words does not write. -/
theorem KS.arrs_W {js ds : List Nat} (h : KS g s0 A live AW liveW V ls s) (k : Keep g.B g.W js ds s.mem t.mem)
    (hl : ∀ j ∈ live, ∀ i ∈ js, j / 2 ≠ i) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem g.B g.w A live :=
  h.arrs.keepOf k.ofW (fun j hj i hi => by
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
      obtain ⟨i', hi', e⟩ := hi
      have := hl j hj i' hi'
      rcases e with rfl | rfl <;> omega) (fun d hd => (hds d hd).2.1) fun j hj => h.ws.fit64 (h.live_lt j hj)

/-- The arrays read with `W` that a step with `W` words does not write. -/
theorem KS.arrsW_W {js ds : List Nat} (h : KS g s0 A live AW liveW V ls s) (k : Keep g.B g.W js ds s.mem t.mem)
    (hl : ∀ j ∈ liveW, ∀ i ∈ js, i ≠ j) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem g.B g.W AW liveW :=
  h.arrsW.keepOf k hl (fun d hd => (hds d hd).2.1) fun j hj => h.wsW.fit64 (h.liveW_lt j hj)

/-- The header words a step does not write. -/
theorem KS.sl_keep {js ds : List Nat} {v : Nat} (h : KS g s0 A live AW liveW V ls s)
    (k : Keep g.B v js ds s.mem t.mem) (hl : ∀ d ∈ ls, ∀ e ∈ ds, d + 4 ≤ e ∨ e + 4 ≤ d) :
    ∀ d ∈ ls, slot t.mem g.B d = V d := fun d hd => by
  rw [k.slot (h.ls_ok d hd).2.1 (fun e he => hl d hd e he), h.sl d hd]

end
end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.write_w {o x : Nat} {ds : List Nat} (h : KS g s0 A live AW liveW V ls s)
    (k : Keep g.B g.w [o] ds s.mem t.mem) (ho : o < nArr) (hd : ∀ d ∈ ds, SlotOk d)
    (r : Keeps opRegs s t) (e : num t.mem g.B g.w o = x)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j)
    (hls : ∀ d ∈ ls, ∀ e ∈ ds, d + 4 ≤ e ∨ e + 4 ≤ d) :
    KS g s0 (upd A o x) (o :: live) AW liveW V ls t :=
  h.core k (by simpa using h.ws.arr_fit ho) hd r
    (h.arrs.upd1 k (fun d hm => (hd d hm).2.1) (fun j hj => h.ws.fit64 (h.live_lt j hj)) e)
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.live_lt j))
    (h.arrsW_w k (fun j hj i hi => by simp at hi; subst hi; exact hlW j hj) hd) h.liveW_lt
    (h.sl_keep k hls) h.ls_ok

theorem KS.write_W {o x : Nat} {ds : List Nat} (h : KS g s0 A live AW liveW V ls s)
    (k : Keep g.B g.W [o] ds s.mem t.mem) (ho : o < 22) (hd : ∀ d ∈ ds, SlotOk d)
    (r : Keeps opRegs s t) (e : num t.mem g.B g.W o = x)
    (hl : ∀ j ∈ live, j / 2 ≠ o)
    (hls : ∀ d ∈ ls, ∀ e ∈ ds, d + 4 ≤ e ∨ e + 4 ≤ d) :
    KS g s0 A live (upd AW o x) (o :: liveW) V ls t :=
  h.core k (by simpa using h.wsW.arr_fit ho) hd r
    (h.arrs_W k (fun j hj i hi => by simp at hi; subst hi; exact hl j hj) hd) h.live_lt
    (h.arrsW.upd1 k (fun d hm => (hd d hm).2.1) (fun j hj => h.wsW.fit64 (h.liveW_lt j hj)) e)
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.liveW_lt j))
    (h.sl_keep k hls) h.ls_ok

theorem KS.slot1 {d x v : Nat} (h : KS g s0 A live AW liveW V ls s)
    (k : Keep g.B v [] [d] s.mem t.mem) (hd : SlotOk d) (r : Keeps opRegs s t)
    (e : slot t.mem g.B d = x) : KS g s0 A live AW liveW (upd V d x) (d :: ls) t := by
  have kw : Keep g.B g.w [] [d] s.mem t.mem := k
  refine h.core kw (by simp) (by simpa using hd) r
    (h.arrs_w kw (by simp) (by simpa using hd)) h.live_lt
    (h.arrsW_w kw (by simp) (by simpa using hd)) h.liveW_lt ?_ ?_
  · intro d' hd'
    by_cases eq : d' = d
    · subst eq; rw [upd_self]; exact e
    · have old := (List.mem_cons.mp hd').resolve_left eq
      have info := h.ls_ok d' old
      rw [upd_ne _ _ eq, kw.slot info.2.1 (fun z hz => by
        simp only [List.mem_singleton] at hz
        subst hz
        have := info.2.2; have := hd.2.2; omega), h.sl d' old]
  · intro d' hd'
    rcases List.mem_cons.mp hd' with rfl | old
    · exact hd
    · exact h.ls_ok d' old

end
end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.readSlot (h : KS g s0 A live AW liveW V ls s) {d : Nat} (hd : d ∈ ls) :
    readSrc s (.mem (VG.Impl.Mont.X86.sc d)) = some (BitVec.ofNat 32 (V d)) := by
  have limit := (h.ls_ok d hd).2.1
  have header := h.ws.hdr_le
  rw [readSrc_sc h.ws.workspace (by omega), ← h.sl d hd]
  simp only [slot, w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem KS.storeSlot (h : KS g s0 A live AW liveW V ls s) {d : Nat} (hd : SlotOk d) (r : Reg) :
    WP isa (.block [.store (VG.Impl.Mont.X86.sc d) r]) s fun t =>
      KS g s0 A live AW liveW (upd V d (s.gpr r).toNat) (d :: ls) t ∧
      t.zf = s.zf ∧ Keeps [] s t := by
  have header := h.ws.hdr_le
  have limit := hd.2.1
  refine wp_storeS (h.ws.workspace.ea (by omega)) (h.ws.workspace.write (by omega))
    fun t T => WP.block_nil ?_
  have frame : Keep g.B g.w [] [d] s.mem t.mem := by
    rw [T.mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by unfold hdr at limit; omega)) (by simp)
  exact ⟨h.slot1 frame hd ((T.keeps []).mono (by decide)) (by
    unfold slot; rw [T.mem, w32_write_self]), T.zf, T.keeps []⟩

end
end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.KeyRt (copy sel sub3 half)
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.copy_w {o a : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hoa : o ≠ a) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (copy nar o a) s fun t =>
      KS g s0 (upd A o (A a)) (o :: live) AW liveW V ls t ∧ Keeps opRegs s t ∧
      w32 t.mem g.B (arr g.w o + 4 * g.w) = w32 s.mem g.B (arr g.w o + 4 * g.w) := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.copy_ok h.rt ho (h.live_lt a ha) hoa) fun t ⟨_, k, e, r, top⟩ => ?_
  rw [kw_nar] at k e top
  exact ⟨h.write_w k ho (by simp) (r.mono (by decide)) (e.trans (h.arrs a ha)) hlW (by simp),
    r.mono (by decide), top⟩

theorem KS.copy_W {o a : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hoa : o ≠ a) (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (copy wid o a) s fun t =>
      KS g s0 A live (upd AW o (AW a)) (o :: liveW) V ls t ∧ Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.copy_ok h.rtW ho (h.liveW_lt a ha) hoa) fun t ⟨_, k, e, r, _⟩ => ?_
  rw [kw_wid] at k e
  exact ⟨h.write_W k ho (by simp) (r.mono (by decide)) (e.trans (h.arrsW a ha)) hl (by simp),
    r.mono (by decide)⟩

theorem KS.sel_w {o a b sl : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hsl : sl ∈ ls)
    (bit : V sl ≤ 1) (hab : o ≠ a ∨ o ≠ b) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sel nar o a b sl) s fun t =>
      KS g s0 (upd A o (if V sl = 0 then A a else A b)) (o :: live) AW liveW V ls t ∧
      Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sel_ok h.rt ho (h.live_lt a ha) (h.live_lt b hb)
    (h.ls_ok sl hsl).2.1 (by rw [h.sl sl hsl]; exact bit) hab) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_nar] at k e
  refine ⟨h.write_w k ho (by simp) (r.mono (by decide)) ?_ hlW (by simp), r.mono (by decide)⟩
  rw [e, h.sl sl hsl, h.arrs a ha, h.arrs b hb]

theorem KS.sel_W {o a b sl : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hsl : sl ∈ ls)
    (bit : V sl ≤ 1) (hab : o ≠ a ∨ o ≠ b) (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (sel wid o a b sl) s fun t =>
      KS g s0 A live (upd AW o (if V sl = 0 then AW a else AW b)) (o :: liveW) V ls t ∧
      Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sel_ok h.rtW ho (h.liveW_lt a ha) (h.liveW_lt b hb)
    (h.ls_ok sl hsl).2.1 (by rw [h.sl sl hsl]; exact bit) hab) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_wid] at k e
  refine ⟨h.write_W k ho (by simp) (r.mono (by decide)) ?_ hl (by simp), r.mono (by decide)⟩
  rw [e, h.sl sl hsl, h.arrsW a ha, h.arrsW b hb]

theorem KS.sub3_w {o a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (_hoa : o ≠ a) (_hob : o ≠ b)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 nar o a b) s fun t => ∃ X,
      KS g s0 (upd A o X) (o :: live) AW liveW V ls t ∧ Keeps opRegs s t ∧
      X + A b = A a + 2 ^ (32 * g.w) * (t.gpr .ebx).toNat ∧ (t.gpr .ebx).toNat ≤ 1 := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok h.rt ho (h.live_lt a ha) (h.live_lt b hb))
    fun t ⟨_, k, e, b1, r⟩ => ?_
  rw [kw_nar] at k e
  exact ⟨num t.mem g.B g.w o,
    h.write_w k ho (by simp) (r.mono (by decide)) rfl hlW (by simp), r.mono (by decide),
    by rw [← h.arrs a ha, ← h.arrs b hb]; exact e, b1⟩

theorem KS.sub3_W {o a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (_hoa : o ≠ a) (_hob : o ≠ b)
    (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (sub3 wid o a b) s fun t => ∃ X,
      KS g s0 A live (upd AW o X) (o :: liveW) V ls t ∧ Keeps opRegs s t ∧
      X + AW b = AW a + 2 ^ (32 * g.W) * (t.gpr .ebx).toNat ∧ (t.gpr .ebx).toNat ≤ 1 := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok h.rtW ho (h.liveW_lt a ha) (h.liveW_lt b hb))
    fun t ⟨_, k, e, b1, r⟩ => ?_
  rw [kw_wid] at k e
  exact ⟨num t.mem g.B g.W o,
    h.write_W k ho (by simp) (r.mono (by decide)) rfl hl (by simp), r.mono (by decide),
    by rw [← h.arrsW a ha, ← h.arrsW b hb]; exact e, b1⟩

end
end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.KeyRt (bitOf clrLow setOne eqSFast)

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.bitOf_w {j sl : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ live) (hsl : SlotOk sl) :
    WP isa (.block (bitOf nar sl j)) s fun t =>
      KS g s0 A live AW liveW (upd V sl (A j % 2)) (sl :: ls) t ∧ Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.bitOf_ok h.rt (h.live_lt j hj) hsl.2.1) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_nar] at k e
  exact ⟨h.slot1 k hsl (r.mono (by decide)) (by rw [e, h.arrs j hj]), r.mono (by decide)⟩

theorem KS.setOne_w {j : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ live) (hlW : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (.block (setOne nar j)) s fun t =>
      KS g s0 (upd A j (1 + 2 ^ 32 * (A j / 2 ^ 32))) (j :: live) AW liveW V ls t ∧
      Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.setOne_ok h.rt (h.live_lt j hj)) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_nar] at k e
  exact ⟨h.write_w k (h.live_lt j hj) (by simp) (r.mono (by decide))
    (by rw [e, h.arrs j hj]) hlW (by simp), r.mono (by decide)⟩

theorem KS.eqS_w {d a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ha : a ∈ live) (hb : b ∈ live) (hd : SlotOk d) (hW : aW ∉ live)
    (hlW : ∀ j ∈ liveW, aW / 2 ≠ j)
    (hls : ∀ e ∈ ls, e + 4 ≤ sT ∨ sT + 4 ≤ e) :
    WP isa (eqSFast nar d a b) s fun t =>
      KS g s0 A live AW liveW (upd V d (if A a = A b then 1 else 0)) (d :: ls) t ∧
      Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.eqSFast_ok h.rt
    (h.live_lt a ha) (h.live_lt b hb) hd.2.1) fun t ⟨_, k0, e, r⟩ => ?_
  have k := k0.mono (js' := [aW]) (ds' := [sT, d]) (by simp) (by simp)
  rw [kw_nar] at k e
  have hdT : ∀ d' ∈ [sT, d], SlotOk d' := by
    intro d' hm
    rcases List.mem_cons.mp hm with rfl | hm
    · decide
    · simpa using (show d' = d from List.mem_singleton.mp hm) ▸ hd
  refine ⟨h.core k (by simpa using h.ws.arr_fit (show aW < nArr by decide)) hdT
    (r.mono (by decide))
    (h.arrs_w k (fun j hj i hi => by simp at hi; subst hi; exact fun e => hW (e ▸ hj)) hdT)
    h.live_lt (h.arrsW_w k (fun j hj i hi => by simp at hi; subst hi; exact hlW j hj) hdT)
    h.liveW_lt ?_ ?_, r.mono (by decide)⟩
  · intro x hx
    by_cases eq : x = d
    · subst eq; rw [upd_self, e, h.arrs a ha, h.arrs b hb]
    · have old := (List.mem_cons.mp hx).resolve_left eq
      have info := h.ls_ok x old
      rw [upd_ne _ _ eq, k.slot info.2.1 (fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hls x old
        · have := info.2.2; have := hd.2.2; omega), h.sl x old]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | old
    · exact hd
    · exact h.ls_ok x old

end
end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32 b2n)
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.KeyRt (sub3)

theorem KS.subWrap {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {o a b : Nat}
    (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 nar o a b) s fun t =>
      KS g s0 (upd A o (sub32 g.w (A a) (A b))) (o :: live) AW liveW V ls t ∧
      (t.gpr .ebx).toNat = b2n (decide (A a < A b)) := by
  refine WP.mono (h.sub3_w ho ha hb hoa hob hlW) fun t ⟨X, ht, _, value, borrow⟩ => ?_
  have xb : X < 2 ^ (32 * g.w) := by
    have v := ht.arrs o (by simp)
    rw [upd_self] at v
    rw [← v]
    exact val32_lt _ _ _ _
  have bb : A b < 2 ^ (32 * g.w) := by
    rw [← h.arrs b hb]
    exact val32_lt _ _ _ _
  obtain ⟨result, flag⟩ := VG.Proof.Rsa.sub32_of xb bb value borrow
  exact ⟨result ▸ ht, flag⟩

theorem KS.subWrap_W {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {o a b : Nat}
    (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hoa : o ≠ a) (hob : o ≠ b)
    (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (sub3 wid o a b) s fun t =>
      KS g s0 A live (upd AW o (sub32 g.W (AW a) (AW b))) (o :: liveW) V ls t ∧
      (t.gpr .ebx).toNat = b2n (decide (AW a < AW b)) := by
  refine WP.mono (h.sub3_W ho ha hb hoa hob hl) fun t ⟨X, ht, _, value, borrow⟩ => ?_
  have xb : X < 2 ^ (32 * g.W) := by
    have v := ht.arrsW o (by simp)
    rw [upd_self] at v
    rw [← v]
    exact val32_lt _ _ _ _
  have bb : AW b < 2 ^ (32 * g.W) := by
    rw [← h.arrsW b hb]
    exact val32_lt _ _ _ _
  obtain ⟨result, flag⟩ := VG.Proof.Rsa.sub32_of xb bb value borrow
  exact ⟨result ▸ ht, flag⟩

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

section
variable {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live liveW ls : List Nat}

 theorem KS.flagNot_ok {d a : Nat} {x : Bool}
    (h : KS g s0 A live AW liveW V ls s) (hd : SlotOk d) (ha : a ∈ ls) (va : V a = b2n x) :
    WP isa (VG.Impl.Rsa.X86.RecoverRt.flagNot d a) s fun t =>
      KS g s0 A live AW liveW (upd V d (b2n (!x))) (d :: ls) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.flagNot
  refine wp_movS (h.readSlot ha) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_logicS (.inr rfl) rfl fun v D => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : (v.gpr .eax).toNat = b2n (!x) := by
    rw [D.gpr, ite_eq_right (by decide), U.gpr, va]
    cases x <;> decide
  refine WP.block_append (WP.mono (hv.storeSlot hd .eax) fun t ⟨ht, _, _⟩ => ?_)
  rw [value] at ht
  exact WP.block_nil ht

theorem KS.flagAnd_ok {d a b : Nat} {x y : Bool}
    (h : KS g s0 A live AW liveW V ls s) (hd : SlotOk d) (ha : a ∈ ls) (hb : b ∈ ls)
    (va : V a = b2n x) (vb : V b = b2n y) :
    WP isa (VG.Impl.Rsa.X86.RecoverRt.flagBin .and d a b) s fun t =>
      KS g s0 A live AW liveW (upd V d (b2n (x && y))) (d :: ls) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.flagBin
  refine wp_movS (h.readSlot ha) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_logicS (.inl rfl) (hu.readSlot hb) fun v D => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : (v.gpr .eax).toNat = b2n (x && y) := by
    rw [D.gpr, ite_eq_left rfl, U.gpr, va, vb]
    cases x <;> cases y <;> decide
  refine WP.block_append (WP.mono (hv.storeSlot hd .eax) fun t ⟨ht, _, _⟩ => ?_)
  rw [value] at ht
  exact WP.block_nil ht

theorem KS.flagOr_ok {d a b : Nat} {x y : Bool}
    (h : KS g s0 A live AW liveW V ls s) (hd : SlotOk d) (ha : a ∈ ls) (hb : b ∈ ls)
    (va : V a = b2n x) (vb : V b = b2n y) :
    WP isa (VG.Impl.Rsa.X86.RecoverRt.flagBin .or d a b) s fun t =>
      KS g s0 A live AW liveW (upd V d (b2n (x || y))) (d :: ls) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.flagBin
  refine wp_movS (h.readSlot ha) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_orS (hu.readSlot hb) fun v D => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : (v.gpr .eax).toNat = b2n (x || y) := by
    rw [D.gpr, U.gpr, va, vb]
    cases x <;> cases y <;> decide
  refine WP.block_append (WP.mono (hv.storeSlot hd .eax) fun t ⟨ht, _, _⟩ => ?_)
  rw [value] at ht
  exact WP.block_nil ht

end
end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (stackAddress)
open VG.Impl.Rsa.X86.Keys

theorem KS.argument {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) {i : Nat} {v : BitVec 32}
    (arg : CallArgument s0 g.B g.Z i v) (apart : ∀ r ∈ stageR g, Region.Disjoint ⟨stackAddress s0 i, 4⟩ r) :
    CallArgument s g.B g.Z i v :=
  arg.frame h.rest (by decide) h.frame apart

/-- An argument of the stage's call, through the stage's writes. -/
theorem KS.arg {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) {i : Nat} {v : BitVec 32}
    (arg : CallArgument s0 g.B g.Z i v) (hi : i ≤ 11) : CallArgument s g.B g.Z i v := by
  have esp0 : s0.gpr .esp = g.sp := (h.rest.1 _ (by decide)).symm.trans h.sp
  have low := h.room.low
  have top := h.top
  refine h.argument arg fun r hr => ?_
  simp only [stageR, VG.Proof.Bignum.X86.CrtRt.frameR, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | ⟨p, rfl, rfl⟩
  · have ea : (stackAddress s0 i).toNat = g.sp.toNat + (4 + 4 * i) := by
      simp only [stackAddress, VG.X86.addr, VG.Proof.Bignum.X86.PublicRt.setWidth_toNat, BitVec.toNat_add,
        BitVec.toNat_ofNat, esp0]
      omega
    have eb : ((g.sp - BitVec.ofNat 32 96).setWidth 64).toNat = g.sp.toNat - 96 := by
      rw [VG.Proof.Bignum.X86.PublicRt.setWidth_toNat, VG.X86.sub_toNat (by omega)]
    exact (Region.disjoint_of_le (r₁ := below g.sp 96) (.inl (by dsimp only; rw [eb, ea]; omega))
      (by dsimp only; rw [eb]; omega) (by dsimp only; rw [ea]; omega)).symm
  · refine arg.stack.apart.sub_right ?_
    have := Offset.sub g.B (d := 16) (n := g.Z - 16) (e := 0) (k := g.Z) (Nat.zero_le _)
      (by have := h.ws.hdr_le; unfold hdr at this; omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (nar)
open VG.Impl.Rsa.X86.KeyRt (arrPtr)
open VG.Impl.Mont.X86 (at_)
open VG.Proof.Mont.X86.Rt (PtrAt ea_ptr ws_write)
open VG.Proof.Rsa.X86.KeyRt (kw)
open VG.Proof.Rsa.X86.Keys

/-- The word above narrow array `j`'s number zeroed, through a pointer to the array. -/
theorem zeroAbove_ok {s : State} {B : Addr} {Z len N : Nat}
    (h : VG.Proof.Rsa.X86.KeyRt.RtWs nar s B Z len N) {j : Nat} (hj : j < N) :
    WP isa (.block (arrPtr nar .eax j .edx ++ ([.alu .add .eax (.reg .edx), .alu .sub .eax (.imm 8),
        .mov .ecx (.imm 0), .store (at_ .eax 0) .ecx] : List Instr))) s fun t =>
      VG.Proof.Rsa.X86.KeyRt.RtWs nar t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      num t.mem B (kw len) j = num s.mem B (kw len) j ∧
      w32 t.mem B (arr (kw len) j + 4 * kw len) = 0 ∧ Keeps [.eax, .ecx, .edx] s t := by
  have fit := h.ws.arr_fit hj
  have nowrap := h.ws.workspace.nowrap
  simp only [S] at fit
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc h) h.lenLe h.edi (by decide)
    (by decide) (by omega) fun u K m p e => ?_
  refine wp_addS rfl fun u₁ U₁ _ => wp_subS rfl fun u₂ U₂ _ => wp_movS rfl fun u₃ U₃ _ => ?_
  have K₃ : Keeps [.eax, .ecx, .edx] s u₃ :=
    ((K.mono (by decide)).trans ((U₁.keeps.trans U₂.keeps).mono (by decide))).trans (U₃.keeps.mono (by decide))
  have hu := h.rt.of_keeps K₃
  have ptr : PtrAt u₃ B .eax (arr (kw len) j + 4 * kw len) := by
    rw [PtrAt, U₃.other _ (by decide), U₂.gpr, U₁.gpr, BitVec.toNat_sub, BitVec.toNat_add, p, e,
      show (8 : BitVec 32).toNat = 8 from rfl]
    omega
  refine wp_storeS (ea_ptr hu ptr (d := 0) (by omega))
    (ws_write hu (y := arr (kw len) j + 4 * kw len + 0) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off B (arr (kw len) j + 4 * kw len)) (0 : BitVec 32) := by
    rw [T.mem, U₃.gpr, U₃.mem, U₂.mem, U₁.mem, m, Nat.add_zero]
  have O := writeW32_outside s.mem B (d := arr (kw len) j + 4 * kw len) (0 : BitVec 32) (by omega)
  rw [← mem] at O
  have Kt : Keeps [.eax, .ecx, .edx] s t := K₃.trans ((T.keeps []).mono (by decide))
  refine ⟨h.keep Kt (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega)),
    Keep.of_arr O (by simp only [S]; omega) (by simp), ?_, by rw [mem, w32_write_self]; rfl, Kt⟩
  exact O.val32 (.inl (by omega)) (by omega)

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32)
open VG.Proof.Rsa.X86.InvBatchRt (rv nw)
open VG.Proof.Rsa.X86.KeyRt (kw)

/-- The header words the GCD writes, from the window to the batch count. -/
abbrev gcdSlots : List Nat :=
  [16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100]

/-- The GCD's writes are within the wide arrays 0 to 5, 11 and 12 and the header words. -/
theorem gcd_keep {g : Geo} {m m' : Mem}
    (U : VG.Proof.Weierstrass.Unch g.B (GcdBatchRt.gcdWrites (16 * g.n + 24)) m m') :
    Keep g.B g.W [0, 1, 2, 3, 4, 5, 11, 12] gcdSlots m m' := by
  have ek : kw (16 * g.n + 24) = 4 * g.n + 6 := by
    simp only [kw, Spec.Rsa.modulusWords]; omega
  have en : nw (16 * g.n + 24) = 2 * g.n + 3 := by simp only [nw, ek]; omega
  have eW : g.W = 4 * g.n + 6 := by simp only [Geo.W, wide, width]; omega
  intro x hx
  have each : ∀ j ∈ [0, 1, 2, 3, 4, 5, 11, 12], ofs g.B x < arr g.W j ∨ arr g.W j + S g.W ≤ ofs g.B x :=
    fun j hj => hx (arr g.W j, S g.W) (by
      simp only [ranges, List.mem_append, List.mem_map]
      exact .inl ⟨j, hj, rfl⟩)
  have slots : ofs g.B x < 16 ∨ 104 ≤ ofs g.B x := by
    by_contra c
    have mem : ∀ q < 22, 16 + 4 * q ∈ gcdSlots := by decide
    have := hx (16 + 4 * ((ofs g.B x - 16) / 4), 4) (by
      simp only [ranges, List.mem_append, List.mem_map]
      exact .inr ⟨_, mem _ (by omega), rfl⟩)
    simp only at this
    omega
  have h0 := each 0 (by decide); have h1 := each 1 (by decide); have h2 := each 2 (by decide)
  have h3 := each 3 (by decide); have h4 := each 4 (by decide); have h5 := each 5 (by decide)
  have h11 := each 11 (by decide); have h12 := each 12 (by decide)
  apply U x
  intro w hw
  simp only [GcdBatchRt.gcdWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
  have ar : ∀ j, arr g.W j = 160 + j * (16 * g.n + 32) := fun j => by simp only [arr, S, hdr, eW]; congr 2; omega
  have sr : S g.W = 16 * g.n + 32 := by simp only [S, eW]; omega
  have rj : ∀ j, rv (kw (16 * g.n + 24)) (VG.Impl.Rsa.X86.InvBatchRt.a j) = 160 + j * (16 * g.n + 32) := fun j => by
    rw [InvBatchRt.rv_a, en]; congr 2; omega
  rw [ar, sr] at h0 h1 h2 h3 h4 h5 h11 h12
  rcases hw with rfl | rfl | rfl
  · show ofs g.B x < 16 ∨ 16 + 88 ≤ ofs g.B x
    omega
  all_goals
    show ofs g.B x < _ ∨ _ ≤ ofs g.B x
    rw [rj, en]
    generalize hT : 16 * g.n + 32 = T at *
    rw [show 8 * (2 * g.n + 3) + 8 = T by omega]
    omega

end VG.Proof.Rsa.X86.Recover
