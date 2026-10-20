module

public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Public layout and persistent header for native RSA division -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure Geometry where
  base : BitVec 32
  size : Nat
  offsets : Fin 4 → Nat
  n : Nat

def Geometry.words (g : Geometry) (i : Fin 4) : Nat := if i = 0 then g.n else g.n + 1

def Geometry.ranges (g : Geometry) : List (Nat × Nat) :=
  [(g.offsets 0, 4 * g.n), (g.offsets 1, 4 * (g.n + 1)), (g.offsets 3, 4 * (g.n + 1))]

structure Context (g : Geometry) (s : State) : Prop where
  workspace : Workspace s g.base g.size
  positive : 0 < g.n
  bound : g.n < 2 ^ 24
  headerFits : 20 ≤ g.size
  fits : ∀ i, g.offsets i + 4 * g.words i ≤ g.size
  afterHeader : ∀ i, 20 ≤ g.offsets i
  separate : ∀ i j, i ≠ j →
    g.offsets i + 4 * g.words i ≤ g.offsets j ∨ g.offsets j + 4 * g.words j ≤ g.offsets i
  ptr : s.gpr .r8 = g.base
  pointers : ∀ i, s.mem.readW (off (State.addr g.base) (4 * i.val)) 32 =
    g.base + BitVec.ofNat 32 (g.offsets i)
  count : s.mem.readW (off (State.addr g.base) 16) 32 = BitVec.ofNat 32 g.n

theorem Context.after {g : Geometry} {s t : State} (h : Context g s)
    (frame : Outs (State.addr g.base) g.ranges s.mem t.mem)
    (wr : t.wr = s.wr) (ptr : t.gpr .r8 = s.gpr .r8) : Context g t := by
  have fit := h.workspace.nowrap
  have h0 := h.afterHeader 0
  have h1 := h.afterHeader 1
  have h3 := h.afterHeader 3
  have read (d : Nat) (hd : d + 4 ≤ 20) :
      t.mem.readW (off (State.addr g.base) d) 32 = s.mem.readW (off (State.addr g.base) d) 32 := by
    apply BitVec.eq_of_toNat_eq
    exact outs_word32 frame (by
      intro r hr
      simp only [Geometry.ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Or.inl (by omega)) (by omega)
  exact { h with
    workspace := h.workspace.congr wr
    ptr := ptr.trans h.ptr
    pointers := fun i => (read _ (by have := i.isLt; omega)).trans (h.pointers i)
    count := (read 16 (by decide)).trans h.count }

theorem Context.readPtr {g : Geometry} {s : State} (h : Context g s) (i : Fin 4) :
    InRegions (s.rd ++ s.wr) (off (State.addr g.base) (4 * i.val)) 4 :=
  h.workspace.read (by have := h.headerFits; have := i.isLt; omega)

theorem Context.addr {g : Geometry} {s : State} (h : Context g s) {d : Nat} (hd : d < 20) :
    State.addr (s.gpr .r8 + BitVec.ofNat 32 d) = off (State.addr g.base) d := by
  rw [h.ptr]
  exact VG.Arm.addr_add (by have := h.workspace.nowrap; have := h.headerFits; omega)

theorem Context.of_update {g : Geometry} {s t : State} {r : Reg} {v : BitVec 32}
    (h : Context g s) (u : VG.Proof.X25519.Arm.Upd s t r v) (hr : r ≠ .r8) : Context g t :=
  h.after (by rw [u.mem]; exact Outs.refl _ _ _) u.wr
    (u.other .r8 (Ne.symm hr))

theorem Context.loadPtr {g : Geometry} {s : State} (h : Context g s) (i : Fin 4)
    {r : Reg} (hr : r ≠ .r8) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X25519.Arm.Upd s t r (g.base + BitVec.ofNat 32 (g.offsets i)) →
      Context g t → WP isa (.block is) t Q) :
    WP isa (.block (.ldr r .r8 (4 * i.val) :: is)) s Q := by
  refine VG.Proof.X25519.Arm.wp_ldr (by have := i.isLt; omega)
    (h.addr (by have := i.isLt; omega)) (h.readPtr i) fun t u => ?_
  rw [h.pointers i] at u
  exact k t u (h.of_update u hr)

theorem Context.loadCount {g : Geometry} {s : State} (h : Context g s)
    {r : Reg} (hr : r ≠ .r8) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X25519.Arm.Upd s t r (BitVec.ofNat 32 g.n) →
      Context g t → WP isa (.block is) t Q) :
    WP isa (.block (.ldr r .r8 16 :: is)) s Q := by
  refine VG.Proof.X25519.Arm.wp_ldr (by decide) (h.addr (by decide))
    (h.workspace.read (by have := h.headerFits; omega)) fun t u => ?_
  rw [h.count] at u
  exact k t u (h.of_update u hr)

end VG.Proof.Rsa.Arm.Div
