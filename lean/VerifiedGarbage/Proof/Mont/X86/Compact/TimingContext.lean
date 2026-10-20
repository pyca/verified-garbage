module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingBase
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata
public import VerifiedGarbage.Proof.Mont.X86.Compact.Bounds
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub

/-! # Read-only prepared metadata across the multiplication's timing proof -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

structure Geometry where
  W : Addr
  L : Nat
  A : Nat → BitVec 32
  N : Nat
  S : Nat
  mo : Nat
  a : Nat
  b : Nat
  o : Nat

structure Geometry.Valid (g : Geometry) : Prop where
  base : (g.A 0).toNat = g.W.toNat
  lay : Lay g.L g.N g.S g.mo g.a g.b
  positive : 0 < g.N
  n32 : 4 * g.N < 2 ^ 32
  outIndex : (g.A 2).toNat < 8
  outHeader : 128 ≤ g.o
  outFit : g.o + 4 * g.N ≤ g.L
  outScratch : g.o + 4 * g.N ≤ g.S ∨ g.S + 8 * g.N + 28 ≤ g.o
  outMod : g.o = g.mo ∨ g.o + 4 * g.N ≤ g.mo ∨ g.mo + 4 * g.N ≤ g.o

def Geometry.writes (g : Geometry) : List (Nat × Nat) := [(g.S, 8 * g.N + 28), (g.o, 4 * g.N)]

structure Context (g : Geometry) (s : State) : Prop where
  ws : Ws s g.W g.L
  args : Args s g.W g.L g.A
  metadata : Metadata s.mem g.W g.A g.N g.S g.mo g.a g.b
  outPtr : w32 s.mem g.W (64 + 8 * (g.A 2).toNat) = (g.W.toNat + g.o) % 2 ^ 32
  wf : VG.X86.Taint.Wf (timingTaint []) s

theorem Geometry.Valid.toL {g : Geometry} (v : g.Valid) {m m' : Mem}
    (O : Outs g.W g.writes m m') : Outs g.W [(0, g.L)] m m' :=
  Outs.widen O fun x hx r hr => by
    have out := hx _ (List.mem_singleton_self _)
    simp only [Geometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only at *
    · have := v.lay.scr; omega
    · have := v.outFit; omega

theorem Geometry.Valid.header {g : Geometry} (v : g.Valid) {m m' : Mem}
    (O : Outs g.W g.writes m m') {d : Nat} (fit : d + 4 ≤ 128) :
    w32 m' g.W d = w32 m g.W d := by
  have value := O.val32 (d := d) (k := 1) (by
    intro r hr
    simp only [Geometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · have := v.lay.header; omega
    · have := v.outHeader; omega) (by omega)
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using value

theorem Context.keep {g : Geometry} (v : g.Valid) {s t : State} (h : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (esp : .esp ∉ rs)
    (O : Outs g.W g.writes s.mem t.mem) (wf : VG.X86.Taint.Wf (timingTaint []) t) : Context g t := by
  refine ⟨h.ws.of_keeps K, h.args.of_keeps K esp (v.toL O), ?_, ?_, wf⟩
  · have M := h.metadata
    refine ⟨?_, M.aIndex, M.bIndex, ?_, ?_, ?_, ?_⟩
    · rw [v.header O (by decide)]; exact M.width
    · rw [v.header O (by decide)]; exact M.scratch
    · rw [v.header O (by decide)]; exact M.modulus
    · rw [v.header O (by have := M.aIndex; omega)]; exact M.left
    · rw [v.header O (by have := M.bIndex; omega)]; exact M.right
  · rw [v.header O (by have := v.outIndex; omega)]; exact h.outPtr

theorem timing_wf_keeps {s t : State} {rs : List Reg}
    (h : VG.X86.Taint.Wf (timingTaint []) s) (K : Keeps rs s t) (esp : .esp ∉ rs) :
    VG.X86.Taint.Wf (timingTaint []) t := by
  have sp := K.1 .esp esp
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, ?_, fun _ h => (List.not_mem_nil h).elim,
    ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
  · intro positive
    have H := h.args positive
    simpa only [VG.X86.Taint.argByte, sp, K.2.2] using H
  · simpa only [sp] using h.stk
  · intro p member
    have H := h.frames p member
    simpa only [sp, K.2.2] using H

theorem Context.keepK {g : Geometry} (v : g.Valid) {s t : State} (h : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (esp : .esp ∉ rs)
    (O : Outs g.W g.writes s.mem t.mem) : Context g t :=
  h.keep v K esp O (timing_wf_keeps h.wf K esp)

end VG.Proof.Mont.X86.Compact
