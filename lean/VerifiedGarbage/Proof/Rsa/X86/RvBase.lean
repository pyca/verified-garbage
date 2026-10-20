module

import VerifiedGarbage.Proof.Rsa.X86.RvViews
public import VerifiedGarbage.Impl.Rsa.X86.Recover
public import VerifiedGarbage.Proof.Rsa.X86.KeyArrs
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Workspace geometry and tracked stages for i686 prime recovery -/

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

abbrev Geo.w (g : Geo) : Nat := width g.n
abbrev Geo.W (g : Geo) : Nat := wide g.n
abbrev opRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]
abbrev SlotOk (d : Nat) : Prop := 16 ≤ d ∧ d + 4 ≤ hdr ∧ d % 4 = 0

theorem arrW_end (g : Geo) : arr g.W 22 = arr g.w nArr := by
  rw [Geo.W, wide, arr_W]
  rfl

theorem ws_wide {g : Geo} {s : State} (h : Ws s g.B g.Z g.w nArr) (hi : g.n ≤ 128) :
    Ws s g.B g.Z g.W 22 := by
  refine ⟨h.workspace, ?_, ?_, ?_⟩
  · rw [arrW_end]; exact h.fits
  · change 0 < 2 * (2 * g.n + 2) + 2; omega
  · change 2 * (2 * g.n + 2) + 2 ≤ 1024; omega

/-- A stage tracks both array widths and the scalar header words. -/
structure KS (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat)
    (AW : Nat → Nat) (liveW : List Nat) (V : Nat → Nat) (ls : List Nat) (s : State) : Prop where
  ws : Ws s g.B g.Z g.w nArr
  lower : 8 ≤ g.n
  upper : g.n ≤ 128
  frame : Outside g.B 16 (g.Z - 16) s0.mem s.mem
  rest : Keeps opRegs s0 s
  arrs : Arrs s.mem g.B g.w A live
  arrsW : Arrs s.mem g.B g.W AW liveW
  sl : ∀ d ∈ ls, slot s.mem g.B d = V d
  live_lt : ∀ j ∈ live, j < nArr
  liveW_lt : ∀ j ∈ liveW, j < 22
  ls_ok : ∀ d ∈ ls, SlotOk d

section
variable {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.wsW (h : KS g s0 A live AW liveW V ls s) : Ws s g.B g.Z g.W 22 :=
  ws_wide h.ws h.upper

theorem KS.of_rest (h : KS g s0 A live AW liveW V ls s) {rs : List Reg}
    (r : Keeps rs s t) (hr : ∀ x ∈ rs, x ∈ opRegs) (mem : t.mem = s.mem) :
    KS g s0 A live AW liveW V ls t :=
  ⟨h.ws.rest (r.mono hr), h.lower, h.upper, mem ▸ h.frame, h.rest.trans (r.mono hr),
    mem ▸ h.arrs, mem ▸ h.arrsW, mem ▸ h.sl, h.live_lt, h.liveW_lt, h.ls_ok⟩

theorem KS.mono (h : KS g s0 A live AW liveW V ls s)
    {A' : Nat → Nat} {live' : List Nat} {AW' : Nat → Nat} {liveW' : List Nat}
    {V' : Nat → Nat} {ls' : List Nat}
    (hl : ∀ j ∈ live', j ∈ live ∧ A j = A' j)
    (hlW : ∀ j ∈ liveW', j ∈ liveW ∧ AW j = AW' j)
    (hls : ∀ d ∈ ls', d ∈ ls ∧ V d = V' d) : KS g s0 A' live' AW' liveW' V' ls' s :=
  ⟨h.ws, h.lower, h.upper, h.frame, h.rest,
    fun j hj => (h.arrs j (hl j hj).1).trans (hl j hj).2,
    fun j hj => (h.arrsW j (hlW j hj).1).trans (hlW j hj).2,
    fun d hd => (h.sl d (hls d hd).1).trans (hls d hd).2,
    fun j hj => h.live_lt j (hl j hj).1,
    fun j hj => h.liveW_lt j (hlW j hj).1,
    fun d hd => h.ls_ok d (hls d hd).1⟩

theorem KS.keepBody (h : KS g s0 A live AW liveW V ls s) {v : Nat} {js ds : List Nat}
    (k : Keep g.B v js ds s.mem t.mem) (hj : ∀ j ∈ js, arr v j + S v ≤ g.Z)
    (hd : ∀ d ∈ ds, SlotOk d) : Outside g.B 16 (g.Z - 16) s.mem t.mem := by
  have header := h.ws.hdr_le
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

theorem KS.core (h : KS g s0 A live AW liveW V ls s) {v : Nat} {js ds : List Nat}
    (k : Keep g.B v js ds s.mem t.mem) (hj : ∀ j ∈ js, arr v j + S v ≤ g.Z)
    (hd : ∀ d ∈ ds, SlotOk d) (r : Keeps opRegs s t)
    {A' : Nat → Nat} {live' : List Nat} {AW' : Nat → Nat} {liveW' : List Nat}
    {V' : Nat → Nat} {ls' : List Nat}
    (ha : Arrs t.mem g.B g.w A' live') (hl : ∀ j ∈ live', j < nArr)
    (haW : Arrs t.mem g.B g.W AW' liveW') (hlW : ∀ j ∈ liveW', j < 22)
    (hsl : ∀ d ∈ ls', slot t.mem g.B d = V' d) (hls : ∀ d ∈ ls', SlotOk d) :
    KS g s0 A' live' AW' liveW' V' ls' t :=
  ⟨h.ws.rest r, h.lower, h.upper, h.frame.trans (h.keepBody k hj hd),
    h.rest.trans r, ha, haW, hsl, hl, hlW, hls⟩

end
end VG.Proof.Rsa.X86.Recover
