module
-- separate module: the five-limb field's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.X25519.PPC64LE.Fe51.Ops
public import VerifiedGarbage.Proof.X25519.Ladder
public import VerifiedGarbage.Proof.X25519.PPC64LE.Bits
public import VerifiedGarbage.Proof.X25519.Chain250
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.X25519.PPC64LE.Cswap
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on PPC64LE, five 51-bit limbs: the ladder and the inversion

The elements are sixteen slots of 40 bytes (`isSlot`), each reduced, with the
element `v q` at `q` for the slots `qs` known (`SlotsOk`); a field operation
adds its result to them (`Cur.op`). An iteration (`step_ok`) is RFC 7748's
(`Spec.X25519.ladderStep`), whose swap of the two points the code takes as a
selection in `AA` and `BB` (`ladder_vals`): the other products are the same
for the two orders. The inversion is ref10's chain (`invert_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE.Fe51

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE.Fe51
open VG.Spec.X25519 (P Fe a24 Ladder ladderStep)
open VG.Proof.X25519 (toFe ladderAfter ladderAfter_step ladderAfter_swap_le ladderStep_eq bit bit_le)

/-! ## Slots -/

/-- The area of the elements: sixteen of 40 bytes. -/
abbrev FB (b : Addr) : Region := ⟨b + BitVec.ofNat 64 1088, 640⟩

/-- The offset of an element. -/
def isSlot (o : Nat) : Bool := decide (1088 ≤ o ∧ o < 1728 ∧ (o - 1088) % 40 = 0)

theorem isSlot_le {o : Nat} (h : isSlot o = true) : 1088 ≤ o ∧ o + 40 ≤ 1728 ∧ o % 4 = 0 := by
  simp only [isSlot, decide_eq_true_eq] at h
  omega_using [h]

theorem isSlot_sep {o q : Nat} (ho : isSlot o = true) (hq : isSlot q = true) (hqo : q ≠ o) :
    q + 40 ≤ o ∨ o + 40 ≤ q := by
  simp only [isSlot, decide_eq_true_eq] at ho hq
  omega_using [ho, hq, hqo]

/-- The slots `qs` hold the reduced elements `v`. -/
def SlotsOk (m : Mem) (B : Addr) (qs : List Nat) (v : Nat → Fe) : Prop :=
  ∀ q ∈ qs, isSlot q = true ∧ Tight m B q ∧ FS m B q = v q

theorem SlotsOk.mono {m : Mem} {B : Addr} {qs qs' : List Nat} {v : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs', q ∈ qs) : SlotsOk m B qs' v := fun q hq => h q (hs q hq)

theorem SlotsOk.congr {m : Mem} {B : Addr} {qs : List Nat} {v w : Nat → Fe} (h : SlotsOk m B qs v)
    (hv : ∀ q ∈ qs, v q = w q) : SlotsOk m B qs w := fun q hq => by rw [← hv q hq]; exact h q hq

/-- `v` with `x` at `o`. -/
def upd (v : Nat → Fe) (o : Nat) (x : Fe) (q : Nat) : Fe := if q = o then x else v q

theorem upd_self (v : Nat → Fe) (o : Nat) (x : Fe) : upd v o x o = x := by simp [upd]

theorem upd_of_ne (v : Nat → Fe) {o q : Nat} (x : Fe) (h : q ≠ o) : upd v o x q = v q := by simp [upd, h]

section
variable {b : Addr}

/-- The limbs of a slot other than the one a frame writes. -/
theorem slot_keep {o q : Nat} (ho : isSlot o = true) (hq : isSlot q = true) (hqo : q ≠ o) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 40⟩] m m') : ∀ k < 5, lw m' b q k = lw m b q k := fun k hk => by
  have h1 := isSlot_le ho; have h2 := isSlot_le hq; have h3 := isSlot_sep ho hq hqo
  exact dw_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (by omega_using [h3, hk]) (by omega_using [h2, hk]) (by omega_using [h1])

/-- The slots after a write of `o`. -/
theorem SlotsOk.write {o : Nat} {qs : List Nat} {v : Nat → Fe} {m m' : Mem} {x : Fe}
    (ho : isSlot o = true) (hS : SlotsOk m b qs v) (hf : Frame [⟨b + BitVec.ofNat 64 o, 40⟩] m m')
    (ht : Tight m' b o) (hx : FS m' b o = x) : SlotsOk m' b (o :: qs) (upd v o x) := fun q hq => by
  by_cases hqo : q = o
  · subst hqo; exact ⟨ho, ht, by rw [upd_self]; exact hx⟩
  · obtain ⟨h1, h2, h3⟩ := hS q ((List.mem_cons.mp hq).resolve_left hqo)
    have e := slot_keep ho h1 hqo hf
    refine ⟨h1, fun k hk => by rw [e k hk]; exact h2 k hk, ?_⟩
    rw [upd_of_ne _ _ hqo, ← h3, FS, FS, V5, V5, val5_congr e]

theorem frame_FB {o : Nat} (ho : isSlot o = true) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 40⟩] m m') : Frame [FB b] m m' := by
  have h := isSlot_le ho
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  rw [List.mem_singleton.mp hr]
  exact Offset.sub _ (by omega_using [h]) (by omega_using [h])

/-! ## Between field operations -/

/-- The registers the code changes: all but the pointers to `out` (`r3`) and
the working space (`r6`). -/
abbrev work : List Reg :=
  [.r0, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22,
    .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- `s'` is `s` but for the registers `work` and the elements. -/
structure Stp (b : Addr) (s s' : State) : Prop where
  rest : Rest work s s'
  frame : Frame [FB b] s.mem s'.mem

theorem Stp.refl (b : Addr) (s : State) : Stp b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Stp.trans {b : Addr} {s₁ s₂ s₃ : State} (h₁ : Stp b s₁ s₂) (h₂ : Stp b s₂ s₃) : Stp b s₁ s₃ :=
  ⟨h₁.rest.trans h₂.rest, h₁.frame.trans h₂.frame⟩

theorem Stp.of_rest {b : Addr} {s s' : State} {ws : List Reg} (hr : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∈ work) (hm : s'.mem = s.mem) : Stp b s s' :=
  ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

/-- Between field operations, from `s0`: `r0` and `r12` hold `a` and `c`,
and the slots `qs` the elements `v`. -/
structure Cur (b : Addr) (s0 : State) (a c : BitVec 64) (qs : List Nat) (v : Nat → Fe) (s : State) :
    Prop where
  ctx : Ctx b s
  stp : Stp b s0 s
  r0 : s.gpr .r0 = a
  r12 : s.gpr .r12 = c
  slots : SlotsOk s.mem b qs v

variable {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe}

theorem Cur.congr {qs' : List Nat} {w : Nat → Fe} {s : State} (h : Cur b s0 a c qs v s)
    (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) : Cur b s0 a c qs' w s :=
  ⟨h.ctx, h.stp, h.r0, h.r12, (h.slots.mono hq).congr hv⟩

/-- A field operation storing `x` at `o`. -/
theorem Cur.op {code : List Instr} {o : Nat} {x : Fe} {s : State} (h : Cur b s0 a c qs v s)
    (ho : isSlot o = true) (hw : WP isa (.block code) s (OpPost b o x s)) :
    WP isa (.block code) s fun s' => Cur b s0 a c (o :: qs) (upd v o x) s' ∧ LoOk b o s' :=
  WP.mono hw fun _ ⟨hr, hf, ht, hx, hl⟩ =>
    ⟨⟨h.ctx.of_rest hr (by decide), h.stp.trans ⟨hr.mono (by decide), frame_FB ho hf⟩,
      by rw [hr.gpr _ (by decide), h.r0], by rw [hr.gpr _ (by decide), h.r12],
      h.slots.write ho hf ht hx⟩, hl⟩

end

/-! ## The operations on slots -/

section
variable {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe}

theorem Cur.mul {o x y : Nat} {s : State} (h : Cur b s0 a c qs v s) (ho : isSlot o = true) (hx : x ∈ qs)
    (hy : y ∈ qs) :
    WP isa (.block (mul o x y)) s fun s' => Cur b s0 a c (o :: qs) (upd v o (v x * v y)) s' ∧ LoOk b o s' := by
  obtain ⟨sx, tx, fx⟩ := h.slots x hx
  obtain ⟨sy, ty, fy⟩ := h.slots y hy
  have lo := isSlot_le ho; have lx := isSlot_le sx; have ly := isSlot_le sy
  have := mul_ok (b := b) (o := o) (x := x) (y := y) (by omega_using [lo]) lo.2.2 (by omega_using [lx]) lx.2.2
    (by omega_using [ly]) ly.2.2 h.ctx tx ty
  rw [fx, fy] at this
  exact h.op ho this

theorem Cur.sqr {o x : Nat} {s : State} (h : Cur b s0 a c qs v s) (ho : isSlot o = true) (hx : x ∈ qs) :
    WP isa (.block (sqr o x)) s fun s' => Cur b s0 a c (o :: qs) (upd v o (v x * v x)) s' ∧ LoOk b o s' := by
  obtain ⟨sx, tx, fx⟩ := h.slots x hx
  have lo := isSlot_le ho; have lx := isSlot_le sx
  have := sqr_ok (b := b) (o := o) (x := x) (by omega_using [lo]) lo.2.2 (by omega_using [lx]) lx.2.2 h.ctx tx
  rw [fx] at this
  exact h.op ho this

theorem Cur.sqrL {o x : Nat} {s : State} (h : Cur b s0 a c qs v s) (ho : isSlot o = true) (hx : x ∈ qs)
    (hl : LoOk b x s) :
    WP isa (.block (sqrL o)) s fun s' => Cur b s0 a c (o :: qs) (upd v o (v x * v x)) s' ∧ LoOk b o s' := by
  obtain ⟨sx, tx, fx⟩ := h.slots x hx
  have lo := isSlot_le ho
  have := sqrL_ok (b := b) (o := o) (x := x) (by omega_using [lo]) lo.2.2 h.ctx tx hl
  rw [fx] at this
  exact h.op ho this

theorem Cur.mulDS {o x y z w : Nat} {s : State} (h : Cur b s0 a c qs v s) (ho : isSlot o = true)
    (hx : x ∈ qs) (hy : y ∈ qs) (hz : z ∈ qs) (hw : w ∈ qs) :
    WP isa (.block (mulDS o x y z w)) s fun s' =>
      Cur b s0 a c (o :: qs) (upd v o ((v x - v y) * (v z + v w))) s' ∧ LoOk b o s' := by
  obtain ⟨sx, tx, fx⟩ := h.slots x hx
  obtain ⟨sy, ty, fy⟩ := h.slots y hy
  obtain ⟨sz, tz, fz⟩ := h.slots z hz
  obtain ⟨sw, tw, fw⟩ := h.slots w hw
  have lo := isSlot_le ho; have lx := isSlot_le sx; have ly := isSlot_le sy
  have lz := isSlot_le sz; have lw' := isSlot_le sw
  have := mulDS_ok (b := b) (o := o) (a := x) (c := y) (e := z) (d := w) (by omega_using [lo]) lo.2.2
    (by omega_using [lx]) lx.2.2 (by omega_using [ly]) ly.2.2 (by omega_using [lz]) lz.2.2
    (by omega_using [lw']) lw'.2.2 h.ctx tx ty tz tw
  rw [fx, fy, fz, fw] at this
  exact h.op ho this

theorem Cur.mulSub {o x y z : Nat} {s : State} (h : Cur b s0 a c qs v s) (ho : isSlot o = true)
    (hx : x ∈ qs) (hy : y ∈ qs) (hz : z ∈ qs) :
    WP isa (.block (mulSub o x y z)) s fun s' =>
      Cur b s0 a c (o :: qs) (upd v o ((v x - v y) * v z)) s' ∧ LoOk b o s' := by
  obtain ⟨sx, tx, fx⟩ := h.slots x hx
  obtain ⟨sy, ty, fy⟩ := h.slots y hy
  obtain ⟨sz, tz, fz⟩ := h.slots z hz
  have lo := isSlot_le ho; have lx := isSlot_le sx; have ly := isSlot_le sy; have lz := isSlot_le sz
  have := mulSub_ok (b := b) (o := o) (a := x) (c := y) (e := z) (by omega_using [lo]) lo.2.2
    (by omega_using [lx]) lx.2.2 (by omega_using [ly]) ly.2.2 (by omega_using [lz]) lz.2.2 h.ctx tx ty tz
  rw [fx, fy, fz] at this
  exact h.op ho this

theorem Cur.sqrAdd {o x y : Nat} {s : State} (h : Cur b s0 a c qs v s) (ho : isSlot o = true)
    (hx : x ∈ qs) (hy : y ∈ qs) :
    WP isa (.block (sqrAdd o x y)) s fun s' =>
      Cur b s0 a c (o :: qs) (upd v o ((v x + v y) * (v x + v y))) s' ∧ LoOk b o s' := by
  obtain ⟨sx, tx, fx⟩ := h.slots x hx
  obtain ⟨sy, ty, fy⟩ := h.slots y hy
  have lo := isSlot_le ho; have lx := isSlot_le sx; have ly := isSlot_le sy
  have := sqrAdd_ok (b := b) (o := o) (a := x) (c := y) (by omega_using [lo]) lo.2.2
    (by omega_using [lx]) lx.2.2 (by omega_using [ly]) ly.2.2 h.ctx tx ty
  rw [fx, fy] at this
  exact h.op ho this

theorem Cur.sqrSub {o x y : Nat} {s : State} (h : Cur b s0 a c qs v s) (ho : isSlot o = true)
    (hx : x ∈ qs) (hy : y ∈ qs) :
    WP isa (.block (sqrSub o x y)) s fun s' =>
      Cur b s0 a c (o :: qs) (upd v o ((v x - v y) * (v x - v y))) s' ∧ LoOk b o s' := by
  obtain ⟨sx, tx, fx⟩ := h.slots x hx
  obtain ⟨sy, ty, fy⟩ := h.slots y hy
  have lo := isSlot_le ho; have lx := isSlot_le sx; have ly := isSlot_le sy
  have := sqrSub_ok (b := b) (o := o) (a := x) (c := y) (by omega_using [lo]) lo.2.2
    (by omega_using [lx]) lx.2.2 (by omega_using [ly]) ly.2.2 h.ctx tx ty
  rw [fx, fy] at this
  exact h.op ho this

theorem Cur.addA24 {o x y : Nat} {s : State} (h : Cur b s0 a c qs v s) (ho : isSlot o = true)
    (hx : x ∈ qs) (hy : y ∈ qs) :
    WP isa (.block (addA24 o x y)) s fun s' =>
      Cur b s0 a c (o :: qs) (upd v o (v x + a24 * (v x - v y))) s' ∧ LoOk b o s' := by
  obtain ⟨sx, tx, fx⟩ := h.slots x hx
  obtain ⟨sy, ty, fy⟩ := h.slots y hy
  have lo := isSlot_le ho; have lx := isSlot_le sx; have ly := isSlot_le sy
  have := addA24_ok (b := b) (o := o) (a := x) (c := y) (by omega_using [lo]) lo.2.2
    (by omega_using [lx]) lx.2.2 (by omega_using [ly]) ly.2.2 h.ctx tx ty
  rw [fx, fy] at this
  exact h.op ho this

theorem Cur.sqrSel (sub : Bool) {o x y z w sw : Nat} {s : State}
    (h : Cur b s0 (BitVec.ofNat 64 sw) c qs v s) (hsw : sw ≤ 1) (ho : isSlot o = true)
    (hx : x ∈ qs) (hy : y ∈ qs) (hz : z ∈ qs) (hw : w ∈ qs) :
    WP isa (.block (sqrSel o sub x y z w)) s fun s' =>
      Cur b s0 (BitVec.ofNat 64 sw) c (o :: qs) (upd v o
        (let t := VG.Proof.X25519.sel sw (if sub then v x - v y else v x + v y)
          (if sub then v z - v w else v z + v w)
        t * t)) s' ∧ LoOk b o s' := by
  obtain ⟨sx, tx, fx⟩ := h.slots x hx
  obtain ⟨sy, ty, fy⟩ := h.slots y hy
  obtain ⟨sz, tz, fz⟩ := h.slots z hz
  obtain ⟨sw', tw, fw⟩ := h.slots w hw
  have lo := isSlot_le ho; have lx := isSlot_le sx; have ly := isSlot_le sy
  have lz := isSlot_le sz; have lw' := isSlot_le sw'
  have := sqrSel_ok (b := b) sub (o := o) (a := x) (c := y) (e := z) (d := w) (by omega_using [lo]) lo.2.2
    (by omega_using [lx]) lx.2.2 (by omega_using [ly]) ly.2.2 (by omega_using [lz]) lz.2.2
    (by omega_using [lw']) lw'.2.2 h.ctx hsw h.r0 tx ty tz tw
  rw [fx, fy, fz, fw] at this
  exact h.op ho this

end

/-! ## One iteration -/

/-- The slots the ladder's state lives in. -/
def LQ : List Nat := [X1, X2, Z2, X3, Z3]

/-- The elements of the ladder's state `st`, and `x1`. -/
def ladV (x1 : Fe) (st : Ladder) (q : Nat) : Fe :=
  if q = X1 then x1 else if q = X2 then st.x2 else if q = Z2 then st.z2 else if q = X3 then st.x3
  else st.z3

theorem fe_add_comm (x y : Fe) : x + y = y + x := Fin.ext (by rw [Fin.val_add, Fin.val_add, Nat.add_comm])

/-- A difference's square is the opposite difference's. -/
theorem fe_sub_sq (x y : Fe) : (x - y) * (x - y) = (y - x) * (y - x) := by
  apply Fin.ext
  rw [Fin.val_mul, Fin.val_mul, Fin.val_sub, Fin.val_sub]
  have hx := x.isLt; have hy := y.isLt
  have hP : P = 2 ^ 255 - 19 := rfl
  generalize x.val = xv at *
  generalize y.val = yv at *
  generalize hu : (P - yv + xv) % P = u
  generalize hw : (P - xv + yv) % P = w
  have h : (u = 0 ∧ w = 0) ∨ u + w = P := by rw [hP] at *; omega_using [hu, hw, hx, hy]
  rcases h with ⟨rfl, rfl⟩ | h
  · rfl
  · have e : w * w + P * (2 * u) = u * u + P * P := by rw [← h]; grind
    have := congrArg (· % P) e
    simp only [Nat.add_mul_mod_self_left] at this
    exact this.symm

/-- An iteration, with its swap as a selection of what `AA` and `BB` square. -/
theorem ladder_vals (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) :
    ladderStep k x1 st t =
      let sw := st.swap ^^^ bit k t
      let A := VG.Proof.X25519.sel sw (st.x2 + st.z2) (st.x3 + st.z3)
      let B := VG.Proof.X25519.sel sw (st.x2 - st.z2) (st.x3 - st.z3)
      let AA := A * A
      let BB := B * B
      let DA := (st.x3 - st.z3) * (st.x2 + st.z2)
      let CB := (st.x2 - st.z2) * (st.x3 + st.z3)
      { x2 := AA * BB, z2 := (AA - BB) * (AA + a24 * (AA - BB)), x3 := (DA + CB) * (DA + CB),
        z3 := x1 * ((DA - CB) * (DA - CB)), swap := bit k t } := by
  rw [ladderStep_eq]
  simp only [Spec.X25519.cswap, VG.Proof.X25519.sel]
  by_cases h : st.swap ^^^ bit k t = 1
  · simp only [h, ↓reduceIte]
    rw [Fin.mul_comm (st.x2 + st.z2) (st.x3 - st.z3),
      fe_add_comm ((st.x2 - st.z2) * (st.x3 + st.z3)) ((st.x3 - st.z3) * (st.x2 + st.z2)),
      fe_sub_sq ((st.x2 - st.z2) * (st.x3 + st.z3)) ((st.x3 - st.z3) * (st.x2 + st.z2))]
  · simp only [h, ↓reduceIte]
    rw [Fin.mul_comm (st.x3 + st.z3) (st.x2 - st.z2)]

/-- The loop invariant of the ladder from `sL`, before the iteration for the
bit `n - 1`. -/
structure LadInv (b : Addr) (k : Nat) (x1 : Fe) (sL : State) (n : Nat) (s : State) : Prop where
  cur : Cur b sL (BitVec.ofNat 64 (ladderAfter k x1 n).swap) (BitVec.ofNat 64 n) LQ
    (ladV x1 (ladderAfter k x1 n)) s

section
variable {b : Addr}

/-- A bit of the scalar, which the elements' frame keeps. -/
theorem bit_at {k : Nat} {sL s : State} (hbits : Bits b k sL.mem) (hf : Frame [FB b] sL.mem s.mem)
    {t : Nat} (ht : t < 255) :
    s.mem (b + BitVec.ofNat 64 (t + Impl.X25519.PPC64LE.BITS)) = BitVec.ofNat 8 (bit k t) := by
  have hB : Impl.X25519.PPC64LE.BITS = 608 := rfl
  rw [hf _ fun r hr => ?_, Nat.add_comm, hbits _ ht]
  rw [List.mem_singleton.mp hr]
  exact fun h => Offset.disjoint b (d := t + Impl.X25519.PPC64LE.BITS) (n := 1) (e := 1088) (k := 640)
    (.inl (by omega_using [ht, hB])) (by omega_using [ht, hB]) (by omega_using []) _
    (Region.contains_self _ _) h

/-- `stepHead`: `swap ^= k_t` for the bit `t = n - 1`. -/
theorem head_ok {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa (.block stepHead) s (Cur b sL (BitVec.ofNat 64 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)))
      (BitVec.ofNat 64 (n - 1)) LQ (ladV x1 (ladderAfter k x1 n))) := by
  obtain ⟨hcur⟩ := h
  have hc := hcur.ctx
  have hB : Impl.X25519.PPC64LE.BITS = 608 := rfl
  have hsw := ladderAfter_swap_le k x1 hn'
  have hbt := bit_le k (n - 1)
  simp only [stepHead]
  refine wp_subi (by decide) (by decide) fun s1 u1 => ?_
  have e12 : s1.gpr .r12 = BitVec.ofNat 64 (n - 1) := by
    rw [u1.gpr, hcur.r12, ofNat_sub_one hn (by omega_arith)]
  refine wp_add fun s2 u2 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 (n - 1 + Impl.X25519.PPC64LE.BITS)) (by decide) (by decide)
    (by rw [u2.gpr, e12, u1.other _ (by decide), hc.r6, Offset.add_add])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hc.inR (by omega_arith)) fun s3 u3 => ?_
  have e4 : s3.gpr .r4 = BitVec.ofNat 64 (bit k (n - 1)) := by
    rw [u3.gpr, u2.mem, u1.mem, bit_at hbits hcur.stp.frame (by omega_arith), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith)]
  refine wp_xor fun s4 u4 => WP.block_nil ?_
  have hr4 : Rest [.r0, .r4, .r12] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  exact ⟨hc.of_rest hr4 (by decide), hcur.stp.trans (Stp.of_rest hr4 (by decide) hm4),
    by rw [u4.gpr, e4, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hcur.r0,
      ofNat_xor (by omega_arith) (by omega_arith)],
    by rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e12],
    by rw [hm4]; exact hcur.slots⟩

/-- `stepBit`: `swap = k_t`. -/
theorem stepBit_ok {k : Nat} {sL : State} (hbits : Bits b k sL.mem) {a : BitVec 64} {n : Nat} (hn : 1 ≤ n)
    (hn' : n ≤ 255) {qs : List Nat} {v : Nat → Fe} {s : State}
    (h : Cur b sL a (BitVec.ofNat 64 (n - 1)) qs v s) :
    WP isa (.block stepBit) s (Cur b sL (BitVec.ofNat 64 (bit k (n - 1))) (BitVec.ofNat 64 (n - 1)) qs v) := by
  have hc := h.ctx
  have hB : Impl.X25519.PPC64LE.BITS = 608 := rfl
  have hbt := bit_le k (n - 1)
  simp only [stepBit]
  refine wp_add fun s1 u1 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 (n - 1 + Impl.X25519.PPC64LE.BITS)) (by decide) (by decide)
    (by rw [u1.gpr, h.r12, hc.r6, Offset.add_add])
    (by rw [u1.rd, u1.wr]; exact hc.inR (by omega_arith)) fun s2 u2 => WP.block_nil ?_
  have hr2 : Rest [.r0, .r4] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  exact ⟨hc.of_rest hr2 (by decide), h.stp.trans (Stp.of_rest hr2 (by decide) hm2),
    by rw [u2.gpr, u1.mem, bit_at hbits h.stp.frame (by omega_arith), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith)],
    by rw [u2.other _ (by decide), u1.other _ (by decide), h.r12], by rw [hm2]; exact h.slots⟩

/-- The elements of an iteration's slots. -/
def SV (x1 x2 z2 x3 z3 aa bb da cb g t : Fe) (q : Nat) : Fe :=
  if q = X1 then x1 else if q = X2 then x2 else if q = Z2 then z2 else if q = X3 then x3
  else if q = Z3 then z3 else if q = AA then aa else if q = BB then bb else if q = DA then da
  else if q = CB then cb else if q = G then g else t

theorem step_ok {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa step s fun s' => LadInv b k x1 sL (n - 1) s' ∧ (s'.gpr .r12 != 0) = decide (n - 1 ≠ 0) := by
  have hsw : (ladderAfter k x1 n).swap ^^^ bit k (n - 1) ≤ 1 :=
    xor_le_one (ladderAfter_swap_le k x1 hn') (bit_le k (n - 1))
  unfold step
  refine WP.seq (WP.mono (head_ok hbits hn hn' h) fun s1 h1 => ?_)
  generalize hst' : ladderAfter k x1 n = st at h1 hsw
  generalize hsw' : st.swap ^^^ bit k (n - 1) = sw at h1 hsw
  let A := VG.Proof.X25519.sel sw (st.x2 + st.z2) (st.x3 + st.z3)
  let B := VG.Proof.X25519.sel sw (st.x2 - st.z2) (st.x3 - st.z3)
  let aa := A * A
  let bb := B * B
  let da := (st.x3 - st.z3) * (st.x2 + st.z2)
  let cb := (st.x2 - st.z2) * (st.x3 + st.z3)
  let g := aa + a24 * (aa - bb)
  let t := (da - cb) * (da - cb)
  have h1 := h1.congr (qs' := LQ) (w := SV x1 (st.x2) (st.z2) (st.x3) (st.z3) 0 0 0 0 0 0) (fun _ h => h) (by
      intro q hq; simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.seq (WP.mono (h1.sqrSel false (o := AA) (x := X2) (y := Z2) (z := X3) (w := Z3) hsw (by decide) (by decide) (by decide) (by decide) (by decide)) fun s2 ⟨h2, _⟩ => ?_)
  have h2 := h2.congr (qs' := [AA, X1, X2, Z2, X3, Z3]) (w := SV x1 (st.x2) (st.z2) (st.x3) (st.z3) aa 0 0 0 0 0) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.seq (WP.mono (h2.sqrSel true (o := BB) (x := X2) (y := Z2) (z := X3) (w := Z3) hsw (by decide) (by decide) (by decide) (by decide) (by decide)) fun s3 ⟨h3, _⟩ => ?_)
  have h3 := h3.congr (qs' := [BB, AA, X1, X2, Z2, X3, Z3]) (w := SV x1 (st.x2) (st.z2) (st.x3) (st.z3) aa bb 0 0 0 0) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.seq (WP.mono (stepBit_ok hbits hn hn' h3) fun s4 h4 => ?_)
  refine WP.seq (WP.mono (h4.mulDS (o := DA) (x := X3) (y := Z3) (z := X2) (w := Z2) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s5 ⟨h5, _⟩ => ?_)
  have h5 := h5.congr (qs' := [DA, BB, AA, X1, X2, Z2, X3, Z3]) (w := SV x1 (st.x2) (st.z2) (st.x3) (st.z3) aa bb da 0 0 0) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.seq (WP.mono (h5.mulDS (o := CB) (x := X2) (y := Z2) (z := X3) (w := Z3) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s6 ⟨h6, _⟩ => ?_)
  have h6 := h6.congr (qs' := [CB, DA, BB, AA, X1, X2, Z2, X3, Z3]) (w := SV x1 (st.x2) (st.z2) (st.x3) (st.z3) aa bb da cb 0 0) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.seq (WP.mono (h6.addA24 (o := G) (x := AA) (y := BB) (by decide) (by decide) (by decide)) fun s7 ⟨h7, _⟩ => ?_)
  have h7 := h7.congr (qs' := [G, CB, DA, BB, AA, X1, X2, Z2, X3, Z3]) (w := SV x1 (st.x2) (st.z2) (st.x3) (st.z3) aa bb da cb g 0) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.seq (WP.mono (h7.sqrSub (o := T) (x := DA) (y := CB) (by decide) (by decide) (by decide)) fun s8 ⟨h8, _⟩ => ?_)
  have h8 := h8.congr (qs' := [T, G, CB, DA, BB, AA, X1, X2, Z2, X3, Z3]) (w := SV x1 (st.x2) (st.z2) (st.x3) (st.z3) aa bb da cb g t) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.seq (WP.mono (h8.sqrAdd (o := X3) (x := DA) (y := CB) (by decide) (by decide) (by decide)) fun s9 ⟨h9, _⟩ => ?_)
  have h9 := h9.congr (qs' := [T, G, CB, DA, BB, AA, X1, X2, Z2, X3, Z3]) (w := SV x1 (st.x2) (st.z2) ((da + cb) * (da + cb)) (st.z3) aa bb da cb g t) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.seq (WP.mono (h9.mulSub (o := Z2) (x := AA) (y := BB) (z := G) (by decide) (by decide) (by decide) (by decide)) fun s10 ⟨h10, _⟩ => ?_)
  have h10 := h10.congr (qs' := [T, G, CB, DA, BB, AA, X1, X2, Z2, X3, Z3]) (w := SV x1 (st.x2) ((aa - bb) * g) ((da + cb) * (da + cb)) (st.z3) aa bb da cb g t) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.seq (WP.mono (h10.mul (o := Z3) (x := X1) (y := T) (by decide) (by decide) (by decide)) fun s11 ⟨h11, _⟩ => ?_)
  have h11 := h11.congr (qs' := [T, G, CB, DA, BB, AA, X1, X2, Z2, X3, Z3]) (w := SV x1 (st.x2) ((aa - bb) * g) ((da + cb) * (da + cb)) (x1 * t) aa bb da cb g t) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.mono (h11.mul (o := X2) (x := AA) (y := BB) (by decide) (by decide) (by decide)) fun s12 ⟨h12, _⟩ => ?_
  have h12 := h12.congr (qs' := [T, G, CB, DA, BB, AA, X1, X2, Z2, X3, Z3]) (w := SV x1 (aa * bb) ((aa - bb) * g) ((da + cb) * (da + cb)) (x1 * t) aa bb da cb g t) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have hst : ladderAfter k x1 (n - 1) = ladderStep k x1 st (n - 1) := by
    rw [ladderAfter_step k x1 (show n - 1 < 255 by omega_arith), Nat.sub_add_cancel hn, hst']
  refine ⟨⟨?_⟩, by rw [h12.r12, ofNat_ne_zero (by omega_arith)]⟩
  rw [hst]
  have hs : (ladderStep k x1 st (n - 1)).swap = bit k (n - 1) := by rw [ladderStep_eq]
  rw [hs]
  refine h12.congr (by decide) fun q hq => ?_
  rw [ladder_vals, hsw']
  simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The ladder, from the state with the bits of the scalar in `BITS` and the
initial elements in `LQ`. -/
theorem ladder_ok {k : Nat} {x1 : Fe} {s : State} (hc : Ctx b s) (hbits : Bits b k s.mem)
    (hS : SlotsOk s.mem b LQ (ladV x1 (VG.Proof.X25519.init x1))) :
    WP isa ladder s fun s' => Stp b s s' ∧ Ctx b s' ∧
      s'.gpr .r0 = BitVec.ofNat 64 (ladderAfter k x1 0).swap ∧
      SlotsOk s'.mem b LQ (ladV x1 (ladderAfter k x1 0)) := by
  unfold ladder
  refine WP.seq (wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ?_)
  have hr2 : Rest [.r0, .r12] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hbits2 : Bits b k s2.mem := by rw [hm2]; exact hbits
  have h255 : LadInv b k x1 s2 255 s2 :=
    ⟨⟨hc.of_rest hr2 (by decide), Stp.refl _ _, by rw [u2.gpr]; rfl,
      by rw [u2.other _ (by decide), u1.gpr], by rw [hm2]; exact hS⟩⟩
  have hst : Stp b s s2 := Stp.of_rest hr2 (by decide) hm2
  refine WP.mono (Q := LadInv b k x1 s2 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ LadInv b k x1 s2 m s') ?_ 255 s2 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨hst.trans h'.stp, h'.ctx, h'.r0, h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (step_ok hbits2 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, hl'⟩

end

/-! ## The swap after the loop -/

section
variable {b : Addr}

/-- While swapping `x` and `y` from `s0`, after `n` limbs. -/
structure SwapInv (b : Addr) (x y sw : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  rest : Rest [.r5, .r7, .r8] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 x, 8 * n⟩, ⟨b + BitVec.ofNat 64 y, 8 * n⟩] s0.mem s.mem
  lx : ∀ j < n, lw s.mem b x j = VG.Proof.X25519.sel sw (lw s0.mem b x j) (lw s0.mem b y j)
  ly : ∀ j < n, lw s.mem b y j = VG.Proof.X25519.sel sw (lw s0.mem b y j) (lw s0.mem b x j)

theorem cswap_ok {x y : Nat} (hx : x + 40 ≤ 4096) (hy : y + 40 ≤ 4096) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0)
    (hxy : x + 40 ≤ y ∨ y + 40 ≤ x) {s0 : State} (hc : Ctx b s0) {sw : Nat} (hsw : sw ≤ 1)
    (h11 : s0.gpr .r11 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block (cswap x y)) s0 (SwapInv b x y sw s0 5) := by
  refine wp_range_flatMap (M := isa) (SwapInv b x y sw s0) (fun k s hk h => ?_) 5 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  have wx : dw s.mem b (x + 8 * k) = lw s0.mem b x k :=
    dw_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hx, hk]) (by omega_using [hx, hk])
      · exact Offset.disjoint _ (by omega_using [hxy, hk]) (by omega_using [hx, hk]) (by omega_using [hy, hk])
  have wy : dw s.mem b (y + 8 * k) = lw s0.mem b y k :=
    dw_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [hxy, hk]) (by omega_using [hy, hk]) (by omega_using [hx, hk])
      · exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hy, hk]) (by omega_using [hy, hk])
  unfold cswapStep
  refine ld0_ok hcs (d := x + 8 * k) (by omega_using [hx, hk]) (by omega_using [hx4]) fun t1 v1 => ?_
  refine ld0_ok (hcs.of_rest (v1.rest (ws := [.r5]) (by decide)) (by decide)) (d := y + 8 * k)
    (by omega_using [hy, hk]) (by omega_using [hy4]) fun t2 v2 => ?_
  refine wp_xor fun t3 v3 => wp_and fun t4 v4 => ?_
  refine wp_xor fun t5 v5 => wp_xor fun t6 v6 => ?_
  have hr6 : Rest [.r5, .r7, .r8] s t6 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))))
  have hc6 : Ctx b t6 := hcs.of_rest hr6 (by decide)
  refine sd0_ok hc6 (d := x + 8 * k) (by omega_using [hx, hk]) (by omega_using [hx4]) fun t7 v7 => ?_
  refine sd0_ok (hc6.of_rest (v7.rest []) (by decide)) (d := y + 8 * k) (by omega_using [hy, hk])
    (by omega_using [hy4]) fun t8 v8 => ?_
  refine WP.block_nil ?_
  have eX : t2.gpr .r5 = s.mem.readW (b + BitVec.ofNat 64 (x + 8 * k)) 64 := by
    rw [v2.other _ (by decide), v1.gpr]
  have eY : t2.gpr .r7 = s.mem.readW (b + BitVec.ofNat 64 (y + 8 * k)) 64 := by
    rw [v2.gpr, v1.mem]
  have em : t3.gpr .r11 = 0 - BitVec.ofNat 64 sw := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h11]
  have e6x : t6.gpr .r5 = t2.gpr .r5 ^^^ ((t2.gpr .r5 ^^^ t2.gpr .r7) &&& (0 - BitVec.ofNat 64 sw)) := by
    rw [v6.other _ (by decide), v5.gpr, v4.other _ (by decide), v3.other _ (by decide), v4.gpr, v3.gpr, em]
  have e6y : t6.gpr .r7 = t2.gpr .r7 ^^^ ((t2.gpr .r5 ^^^ t2.gpr .r7) &&& (0 - BitVec.ofNat 64 sw)) := by
    rw [v6.gpr, v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v5.other _ (by decide),
      v4.gpr, v3.gpr, em]
  have hm8 : t8.mem = (s.mem.writeW (b + BitVec.ofNat 64 (x + 8 * k)) (t6.gpr .r5)).writeW
      (b + BitVec.ofNat 64 (y + 8 * k)) (t6.gpr .r7) := by
    rw [v8.mem, v7.gpr, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have vx : (t6.gpr .r5).toNat = VG.Proof.X25519.sel sw (lw s0.mem b x k) (lw s0.mem b y k) := by
    rw [e6x, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0]; rfl
    · rw [sel1]; rfl
  have vy : (t6.gpr .r7).toNat = VG.Proof.X25519.sel sw (lw s0.mem b y k) (lw s0.mem b x k) := by
    rw [e6y, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0']; rfl
    · rw [sel1']; rfl
  refine ⟨h.rest.trans (hr6.trans ((v7.rest _).trans (v8.rest _))), ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hm8]
    refine ((h.frame.sub fun r hr => ?_).writeW (List.mem_cons_self ..) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hx, hk]))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hy, hk]))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega_using [])⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_using [])⟩
  · rw [lw, hm8, dw_write_other _ _ _ (by omega_using [hxy, hk, hj]) (by omega_using [hx, hk, hj]) (by omega_using [hy, hk])]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [dw_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [hx, hk])]; exact h.lx j hj
    · rw [dw_write_self, vx]
  · rw [lw, hm8]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [dw_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [hy, hk]),
        dw_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_using [hx, hk])]; exact h.ly j hj
    · rw [dw_write_self, vy]

/-- The elements after swapping `x` and `y` if `sw = 1`. -/
def swapV (x y sw : Nat) (v : Nat → Fe) (q : Nat) : Fe :=
  if q = x then VG.Proof.X25519.sel sw (v x) (v y) else if q = y then VG.Proof.X25519.sel sw (v y) (v x)
  else v q

theorem cswapS {x y : Nat} {qs : List Nat} {v : Nat → Fe} (hx : x ∈ qs) (hy : y ∈ qs) (hxy : x ≠ y)
    {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1) (h11 : s.gpr .r11 = 0 - BitVec.ofNat 64 sw)
    (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (cswap x y)) s fun s' => Rest [.r5, .r7, .r8] s s' ∧ Frame [FB b] s.mem s'.mem ∧
      SlotsOk s'.mem b qs (swapV x y sw v) := by
  obtain ⟨sx, tx, fx⟩ := hS x hx
  obtain ⟨sy, ty, fy⟩ := hS y hy
  have lx := isSlot_le sx; have ly := isSlot_le sy
  have hsep := isSlot_sep sy sx hxy
  refine WP.mono (cswap_ok (b := b) (by omega_using [lx]) (by omega_using [ly]) lx.2.2 ly.2.2 hsep hc hsw h11)
    fun s' h => ⟨h.rest, ?_, ?_⟩
  · refine h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega_using [lx, ly]) (by omega_using [lx, ly])
  · intro q hq
    obtain ⟨sq, tq, fq⟩ := hS q hq
    have hlx : ∀ k < 5, lw s'.mem b x k = VG.Proof.X25519.sel sw (lw s.mem b x k) (lw s.mem b y k) := h.lx
    have hly : ∀ k < 5, lw s'.mem b y k = VG.Proof.X25519.sel sw (lw s.mem b y k) (lw s.mem b x k) := h.ly
    refine ⟨sq, ?_⟩
    by_cases hqx : q = x
    · subst hqx
      simp only [swapV, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 5, lw s'.mem b q k = lw s.mem b q k := fun k hk => by rw [hlx k hk]; rfl
        exact ⟨fun k hk => by rw [e k hk]; exact tx k hk, by rw [FS, V5, val5_congr e]; exact fx⟩
      · have e : ∀ k < 5, lw s'.mem b q k = lw s.mem b y k := fun k hk => by rw [hlx k hk]; rfl
        exact ⟨fun k hk => by rw [e k hk]; exact ty k hk, by rw [FS, V5, val5_congr e]; exact fy⟩
    by_cases hqy : q = y
    · subst hqy
      simp only [swapV, hqx, ite_false, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 5, lw s'.mem b q k = lw s.mem b q k := fun k hk => by rw [hly k hk]; rfl
        exact ⟨fun k hk => by rw [e k hk]; exact ty k hk, by rw [FS, V5, val5_congr e]; exact fy⟩
      · have e : ∀ k < 5, lw s'.mem b q k = lw s.mem b x k := fun k hk => by rw [hly k hk]; rfl
        exact ⟨fun k hk => by rw [e k hk]; exact tx k hk, by rw [FS, V5, val5_congr e]; exact fx⟩
    · simp only [swapV, hqx, hqy, ite_false]
      have lq := isSlot_le sq
      have s1 := isSlot_sep sx sq hqx
      have s2 := isSlot_sep sy sq hqy
      have e : ∀ k < 5, lw s'.mem b q k = lw s.mem b q k := fun k hk =>
        dw_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (by omega_using [s1, hk]) (by omega_using [lq, hk]) (by omega_using [lx])
          · exact Offset.disjoint _ (by omega_using [s2, hk]) (by omega_using [lq, hk]) (by omega_using [ly])
      exact ⟨fun k hk => by rw [e k hk]; exact tq k hk, by rw [FS, V5, val5_congr e]; exact fq⟩

theorem lastSwap_ok {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (h0 : s.gpr .r0 = BitVec.ofNat 64 sw) {v : Nat → Fe} (hS : SlotsOk s.mem b LQ v) :
    WP isa (.block lastSwap) s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b LQ (swapV Z2 Z3 sw (swapV X2 X3 sw v)) := by
  simp only [lastSwap, Impl.X25519.PPC64LE.mask, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_sub fun s2 u2 => ?_
  have hr2 : Rest [.r11] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have e11 : s2.gpr .r11 = 0 - BitVec.ofNat 64 sw := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), h0]; rfl
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (cswapS (v := v) (qs := LQ) (x := X2) (y := X3) (by decide) (by decide) (by decide) hc2
    hsw e11 (by rw [hm2]; exact hS)) fun s3 ⟨hr3, hf3, hS3⟩ => ?_
  have hc3 : Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine WP.mono (cswapS (x := Z2) (y := Z3) (by decide) (by decide) (by decide) hc3 hsw
    (by rw [hr3.gpr _ (by decide), e11]) hS3) fun s4 ⟨hr4, hf4, hS4⟩ =>
    ⟨⟨(hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans (hr4.mono (by decide))),
      by rw [← hm2]; exact hf3.trans hf4⟩, hc3.of_rest hr4 (by decide), hS4⟩

/-! ## The inversion -/

variable {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe}

/-- A product of the chain, the slots then `qs'` with the elements `w`. -/
theorem chainMul {o x y : Nat} {qs' : List Nat} {w : Nat → Fe} (ho : isSlot o = true) (hx : x ∈ qs)
    (hy : y ∈ qs) (hqs : ∀ q ∈ qs', q ∈ o :: qs) (hw : ∀ q ∈ qs', upd v o (v x * v y) q = w q) {s : State}
    (h : Cur b s0 a c qs v s) : WP isa (.block (mul o x y)) s (Cur b s0 a c qs' w) :=
  WP.mono (h.mul ho hx hy) fun _ h' => h'.1.congr hqs hw

/-- A square of the chain. -/
theorem chainSqr {o x : Nat} {qs' : List Nat} {w : Nat → Fe} (ho : isSlot o = true) (hx : x ∈ qs)
    (hqs : ∀ q ∈ qs', q ∈ o :: qs) (hw : ∀ q ∈ qs', upd v o (v x * v x) q = w q) {s : State}
    (h : Cur b s0 a c qs v s) : WP isa (.block (sqr o x)) s (Cur b s0 a c qs' w) :=
  WP.mono (h.sqr ho hx) fun _ h' => h'.1.congr hqs hw

theorem lo_ne12 : ∀ k < 5, lo k ≠ .r12 := by decide

/-- `[x]` squared `n` times into `[o]`, the slots then `qs'` with the elements `w`; `r12` counts. -/
theorem chainSqn {o x n : Nat} {qs' : List Nat} {w : Nat → Fe} (ho : isSlot o = true) (hx : x ∈ qs)
    (hn : 2 ≤ n) (hn' : n ≤ 255) (hqs : ∀ q ∈ qs', q ∈ o :: qs)
    (hw : ∀ q ∈ qs', upd v o (VG.Proof.X25519.sqn (v x) n) q = w q) {s : State}
    (h : Cur b s0 a c qs v s) :
    WP isa (Impl.X25519.PPC64LE.Fe51.sqn o x n) s fun s' => ∃ c', Cur b s0 a c' qs' w s' := by
  unfold Impl.X25519.PPC64LE.Fe51.sqn
  refine WP.seq (WP.mono (h.sqr ho hx) fun s1 ⟨h1, l1⟩ => ?_)
  refine WP.seq (wp_li (imm := n - 1) (by omega_using [hn']) fun s2 u2 => WP.block_nil ?_)
  have h2 : Cur b s0 a (BitVec.ofNat 64 (n - 1)) (o :: qs) (upd v o (VG.Proof.X25519.sqn (v x) (n - (n - 1)))) s2 := by
    rw [show n - (n - 1) = 1 by omega_using [hn]]
    exact ⟨h1.ctx.of_rest (u2.rest (ws := [.r12]) (by decide)) (by decide),
      h1.stp.trans (Stp.of_rest (u2.rest (ws := [.r12]) (by decide)) (by decide) u2.mem),
      by rw [u2.other _ (by decide), h1.r0], u2.gpr, by rw [u2.mem]; exact h1.slots⟩
  have l2 : LoOk b o s2 := fun k hk => by rw [u2.other _ (lo_ne12 k hk), u2.mem]; exact l1 k hk
  refine WP.mono (Q := fun t => Cur b s0 a (BitVec.ofNat 64 0) (o :: qs)
      (upd v o (VG.Proof.X25519.sqn (v x) n)) t) (WP.loop (M := isa)
    (fun m t => 1 ≤ m ∧ m ≤ n - 1 ∧
      Cur b s0 a (BitVec.ofNat 64 m) (o :: qs) (upd v o (VG.Proof.X25519.sqn (v x) (n - m))) t ∧ LoOk b o t) ?_
    (n - 1) s2 ⟨by omega_using [hn], Nat.le_refl _, h2, l2⟩) fun t ht => ⟨_, ht.congr hqs hw⟩
  rintro m t ⟨hm1, hm, ht, lt⟩
  refine WP.append (ht.sqrL (o := o) (x := o) ho List.mem_cons_self lt) fun t1 ⟨h1, l1⟩ => ?_
  have h1' : Cur b s0 a (BitVec.ofNat 64 m) (o :: qs)
      (upd v o (VG.Proof.X25519.sqn (v x) (n - (m - 1)))) t1 := by
    refine h1.congr (fun q hq => List.mem_cons_of_mem _ hq) fun q _ => ?_
    by_cases hqo : q = o
    · subst hqo
      simp only [upd_self]
      rw [show n - (m - 1) = (n - m) + 1 by omega_using [hm1, hm]]
      rfl
    · rw [upd_of_ne _ _ hqo, upd_of_ne _ _ hqo, upd_of_ne _ _ hqo]
  refine wp_subi (by decide) (by decide) fun t2 u2 => WP.block_nil ?_
  have e1 : t2.gpr .r12 = BitVec.ofNat 64 (m - 1) := by
    rw [u2.gpr, h1'.r12, ofNat_sub_one hm1 (by omega_using [hn', hm])]
  have h2' : Cur b s0 a (BitVec.ofNat 64 (m - 1)) (o :: qs)
      (upd v o (VG.Proof.X25519.sqn (v x) (n - (m - 1)))) t2 :=
    ⟨h1'.ctx.of_rest (u2.rest (ws := [.r12]) (by decide)) (by decide),
      h1'.stp.trans (Stp.of_rest (u2.rest (ws := [.r12]) (by decide)) (by decide) u2.mem),
      by rw [u2.other _ (by decide), h1'.r0], e1, by rw [u2.mem]; exact h1'.slots⟩
  have l2' : LoOk b o t2 := fun k hk => by rw [u2.other _ (lo_ne12 k hk), u2.mem]; exact l1 k hk
  rw [eval_nonzero, e1, ofNat_ne_zero (by omega_using [hn', hm])]
  by_cases hm0 : m - 1 = 0
  · refine .inl ⟨by simp [hm0], ?_⟩
    rw [show n - (m - 1) = n by omega_using [hm0], hm0] at h2'
    exact h2'
  · exact .inr ⟨by simp [hm0], m - 1, by omega_using [hm1], by omega_using [hm0], by omega_using [hm], h2', l2'⟩

/-- The chain's slots: `z` at `Z2`, `x2` at `X2` and `t0`–`t3` at `A`–`D`. -/
def cv (z x2 t0 t1 t2 t3 : Fe) (q : Nat) : Fe :=
  if q = Z2 then z else if q = X2 then x2 else if q = A then t0 else if q = B then t1 else if q = C then t2
  else t3

/-- The slots of the inversion. -/
def IQ : List Nat := [Z2, R, X2]

/-- **The inversion**: `[R] = [Z2]^(p-2)` by ref10's chain (`VG.Proof.X25519.invert`). -/
theorem invert_ok {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b [Z2, X2] v) (h0 : s.gpr .r0 = a) :
    WP isa Impl.X25519.PPC64LE.Fe51.invert s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b IQ (upd v R (VG.Proof.X25519.pw (v Z2) (P - 2))) := by
  let z := v Z2
  let x2 := v X2
  have h : Cur b s a (s.gpr .r12) [Z2, X2] (cv z x2 0 0 0 0) s :=
    ⟨hc, Stp.refl _ _, h0, rfl, hS.congr fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl⟩
  unfold Impl.X25519.PPC64LE.Fe51.invert
  let t0 := z * z
  refine WP.seq (WP.mono (chainSqr (o := A) (x := Z2) (qs' := [A, Z2, X2]) (w := cv z x2 t0 0 0 0)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> rfl) h) fun s1 h1 => ?_)
  let t1a := t0 * t0
  refine WP.seq (WP.mono (chainSqr (o := B) (x := A) (qs' := [B, A, Z2, X2]) (w := cv z x2 t0 t1a 0 0)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> rfl) h1) fun s2 h2 => ?_)
  let t1b := t1a * t1a
  refine WP.seq (WP.mono (chainSqr (o := B) (x := B) (qs' := [B, A, Z2, X2]) (w := cv z x2 t0 t1b 0 0)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> rfl) h2) fun s3 h3 => ?_)
  let t1c := z * t1b
  refine WP.seq (WP.mono (chainMul (o := B) (x := Z2) (y := B) (qs' := [B, A, Z2, X2]) (w := cv z x2 t0 t1c 0 0)
    (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> rfl) h3) fun s4 h4 => ?_)
  let t0' := t0 * t1c
  refine WP.seq (WP.mono (chainMul (o := A) (x := A) (y := B) (qs' := [B, A, Z2, X2]) (w := cv z x2 t0' t1c 0 0)
    (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> rfl) h4) fun s5 h5 => ?_)
  let t2a := t0' * t0'
  refine WP.seq (WP.mono (chainSqr (o := C) (x := A) (qs' := [C, B, A, Z2, X2]) (w := cv z x2 t0' t1c t2a 0)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl) h5) fun s6 h6 => ?_)
  let t1d := t1c * t2a
  refine WP.seq (WP.mono (chainMul (o := B) (x := B) (y := C) (qs' := [C, B, A, Z2, X2]) (w := cv z x2 t0' t1d t2a 0)
    (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl) h6) fun s7 h7 => ?_)
  let t2b := VG.Proof.X25519.sqn t1d 5
  refine WP.seq (WP.mono (chainSqn (o := C) (x := B) (n := 5) (qs' := [C, B, A, Z2, X2]) (w := cv z x2 t0' t1d t2b 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl) h7) fun s8 ⟨_, h8⟩ => ?_)
  let t1e := t2b * t1d
  refine WP.seq (WP.mono (chainMul (o := B) (x := C) (y := B) (qs' := [C, B, A, Z2, X2]) (w := cv z x2 t0' t1e t2b 0)
    (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl) h8) fun s9 h9 => ?_)
  let t2c := VG.Proof.X25519.sqn t1e 10
  refine WP.seq (WP.mono (chainSqn (o := C) (x := B) (n := 10) (qs' := [C, B, A, Z2, X2]) (w := cv z x2 t0' t1e t2c 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl) h9) fun s10 ⟨_, h10⟩ => ?_)
  let t2d := t2c * t1e
  refine WP.seq (WP.mono (chainMul (o := C) (x := C) (y := B) (qs' := [C, B, A, Z2, X2]) (w := cv z x2 t0' t1e t2d 0)
    (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl) h10) fun s11 h11 => ?_)
  let t3a := VG.Proof.X25519.sqn t2d 20
  refine WP.seq (WP.mono (chainSqn (o := D) (x := C) (n := 20) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1e t2d t3a)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h11) fun s12 ⟨_, h12⟩ => ?_)
  let t2e := t3a * t2d
  refine WP.seq (WP.mono (chainMul (o := C) (x := D) (y := C) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1e t2e t3a)
    (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h12) fun s13 h13 => ?_)
  let t2f := VG.Proof.X25519.sqn t2e 10
  refine WP.seq (WP.mono (chainSqn (o := C) (x := C) (n := 10) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1e t2f t3a)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h13) fun s14 ⟨_, h14⟩ => ?_)
  let t1f := t2f * t1e
  refine WP.seq (WP.mono (chainMul (o := B) (x := C) (y := B) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1f t2f t3a)
    (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h14) fun s15 h15 => ?_)
  let t2g := VG.Proof.X25519.sqn t1f 50
  refine WP.seq (WP.mono (chainSqn (o := C) (x := B) (n := 50) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1f t2g t3a)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h15) fun s16 ⟨_, h16⟩ => ?_)
  let t2h := t2g * t1f
  refine WP.seq (WP.mono (chainMul (o := C) (x := C) (y := B) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1f t2h t3a)
    (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h16) fun s17 h17 => ?_)
  let t3b := VG.Proof.X25519.sqn t2h 100
  refine WP.seq (WP.mono (chainSqn (o := D) (x := C) (n := 100) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1f t2h t3b)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h17) fun s18 ⟨_, h18⟩ => ?_)
  let t2i := t3b * t2h
  refine WP.seq (WP.mono (chainMul (o := C) (x := D) (y := C) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1f t2i t3b)
    (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h18) fun s19 h19 => ?_)
  let t2j := VG.Proof.X25519.sqn t2i 50
  refine WP.seq (WP.mono (chainSqn (o := C) (x := C) (n := 50) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1f t2j t3b)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h19) fun s20 ⟨_, h20⟩ => ?_)
  let t1g := t2j * t1f
  refine WP.seq (WP.mono (chainMul (o := B) (x := C) (y := B) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1g t2j t3b)
    (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h20) fun s21 h21 => ?_)
  let t1h := VG.Proof.X25519.sqn t1g 5
  refine WP.seq (WP.mono (chainSqn (o := B) (x := B) (n := 5) (qs' := [D, C, B, A, Z2, X2]) (w := cv z x2 t0' t1h t2j t3b)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h21) fun s22 ⟨_, h22⟩ => ?_)
  have hinv : t1h * t0' = VG.Proof.X25519.pw (v Z2) (P - 2) := by
    rw [← VG.Proof.X25519.pow_pw, ← VG.Proof.X25519.invert_eq]
    rfl
  refine WP.mono (chainMul (o := R) (x := B) (y := A) (qs' := IQ) (w := upd v R (VG.Proof.X25519.pw (v Z2) (P - 2)))
    (by decide) (by decide) (by decide) (by decide) ?_ h22) fun s' h' =>
    ⟨h'.stp, h'.ctx, h'.slots⟩
  intro q hq
  simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · rw [upd_of_ne _ _ (by decide), upd_of_ne _ _ (by decide)]; rfl
  · rw [upd_self, upd_self]; exact hinv
  · rw [upd_of_ne _ _ (by decide), upd_of_ne _ _ (by decide)]; rfl

end

end VG.Proof.X25519.PPC64LE.Fe51
