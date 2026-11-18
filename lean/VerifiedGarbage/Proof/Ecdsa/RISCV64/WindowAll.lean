module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV

/-!
# `vg_<curve>_mul` by four-bit windows on RISC-V: the body, for every curve

`WindowA.Cfg.body c dbl` leaves in `R` a representative of `[k]Q`
(`Kit.body_ok`), for `k` at `K`'s slot and `Q` affine in `R`'s first two,
once for every curve whose numbers are whole words in Montgomery's form: what
the proof needs of a curve is its `Kit`: the code's configuration, its
Jacobian doubling and the three steps of `R = 16 R` on the field's programs
(`dblStep_ok`, `toJStep_ok`, `fromJStep_ok`), its complete addition
(`addPt_ok`), and the numbers of its layout.

The layout is arithmetic in the configuration's number of words `c.n`: slot
`i` is at `64 + 8 n i` (`sl_eq`), the table of `24 n` bytes an entry is from
`c.jt`, and the field functions' own working space from `own c.n`. What the
proof needs of these is a few bounds, which are the kit's (`Kit.bounds`); its
side conditions about slots and ranges are arithmetic from them (`wa_dec`).

* `quad_ok`: `R = 16 R`: `R`'s representative of `P` into Jacobian
  coordinates, four doublings, and back in projective coordinates, with
  `Y = 1` where `Z` is zero;
* `build_ok`: the table of `[e]Q` from byte `c.jt`, stored through `a6` as
  verification's is;
* `select_ok`: the nibble's entry to `E`, by verification's selection;
* `step_ok`, `body_ok`: the windows, from `R = O`.

Each `<Curve>/Window.lean` is the curve's kit, and the statements about it
that other modules use.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.WindowAll

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.WindowA
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.WindowA
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Window (windows)

/-! ## What the statements are about -/

theorem mul_zero' {C : Spec.Weierstrass.Curve} (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; rfl

theorem mul_one' {C : Spec.Weierstrass.Curve} (P : Point C) : mul 1 P = P := by
  rw [Spec.Weierstrass.mul, ite_eq_right (by decide), show (1 : Nat) / 2 = 0 from rfl, mul_zero',
    ite_eq_right (by decide)]
  rfl

/-- The registers the selection writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4]

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (c : Cfg) (base : Addr) (s : State) (p : Pt) (P : Point c.C) : Prop where
  rep : Rep c.C (tmv c.C c.n base s p.x) (tmv c.C c.n base s p.y) (tmv c.C c.n base s p.z) P
  x : wordsVal s.mem base p.x c.n < c.C.p
  y : wordsVal s.mem base p.y c.n < c.C.p
  z : wordsVal s.mem base p.z c.n < c.C.p

theorem PtOk.of_eq {c : Cfg} {base : Addr} {s s' : State} {p : Pt} {P : Point c.C} (h : PtOk c base s p P)
    (hx : wordsVal s'.mem base p.x c.n = wordsVal s.mem base p.x c.n)
    (hy : wordsVal s'.mem base p.y c.n = wordsVal s.mem base p.y c.n)
    (hz : wordsVal s'.mem base p.z c.n = wordsVal s.mem base p.z c.n) : PtOk c base s' p P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y,
    by rw [hz]; exact h.z⟩

/-- A point copied to other slots. -/
theorem PtOk.move {c : Cfg} {base : Addr} {s s' : State} {p q : Pt} {P : Point c.C} (h : PtOk c base s p P)
    (hx : wordsVal s'.mem base q.x c.n = wordsVal s.mem base p.x c.n)
    (hy : wordsVal s'.mem base q.y c.n = wordsVal s.mem base p.y c.n)
    (hz : wordsVal s'.mem base q.z c.n = wordsVal s.mem base p.z c.n) : PtOk c base s' q P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y,
    by rw [hz]; exact h.z⟩

section
variable (c : Cfg)

/-- What the additions write. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW (Cfg.rcbSlots c) o).map (fun w => (w, 8 * c.n)) ++ [(own c.n, 64 * c.n)]

/-- The slots of the entry `E` of a window: 58, 59 and 60. -/
abbrev ePt : Pt := c.pt 58 59 60

/-- The slots of `R = 16 R`'s arithmetic. -/
abbrev wSl : List Nat :=
  [c.sl AP, c.sl B3P, c.sl ZERO, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5,
    c.sl RX, c.sl RY, c.sl RZ, c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

/-- What the field operations of `R = 16 R` write: `R`, `D`, `T`, the
temporaries and the functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(64 + 8 * c.n * 14, 120 * c.n), (own c.n, 64 * c.n)]

/-- The slots they write. -/
abbrev quadWl : List Nat :=
  [c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5, c.sl RX, c.sl RY, c.sl RZ,
    c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

/-- The constants the windows read. -/
structure KC (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (c.sl AP) c.n = c.C.a * 2 ^ (64 * c.n) % c.C.p
  bp : wordsVal s.mem base (c.sl B3P) c.n = 3 * c.C.b * 2 ^ (64 * c.n) % c.C.p
  zero : wordsVal s.mem base (c.sl ZERO) c.n = 0
  onep : wordsVal s.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p

theorem KC.of_eq {c : Cfg} {base : Addr} {s s' : State} (h : KC c base s)
    (e : ∀ d ∈ [c.sl AP, c.sl B3P, c.sl ZERO, c.sl ONEP], wordsVal s'.mem base d c.n = wordsVal s.mem base d c.n) :
    KC c base s' :=
  ⟨(e _ (by simp)).trans h.ap, (e _ (by simp)).trans h.bp, (e _ (by simp)).trans h.zero, (e _ (by simp)).trans h.onep⟩

/-- Entry `e`'s slots. -/
abbrev ent (e : Nat) : Pt := ⟨c.jt + 24 * c.n * e, c.jt + 24 * c.n * e + 8 * c.n, c.jt + 24 * c.n * e + 16 * c.n⟩

/-- The table up to entry `m`: `[e]Q` in entry `e`. -/
abbrev TabTo (base : Addr) (s : State) (Q : Point c.C) (m : Nat) : Prop := ∀ e ≤ m, PtOk c base s (ent c e) (mul e Q)

/-- While the table is built: the constants, the table up to entry `m + 1`,
`[m + 1]Q` in `D` and `Q` in `R`'s first two slots and one's. -/
structure AI (base : Addr) (s : State) (Q : Point c.C) (m : Nat) : Prop where
  ws : WsReg s base
  kc : KC c base s
  tab : TabTo c base s Q (m + 1)
  d : PtOk c base s (c.pt DX DY DZ) (mul (m + 1) Q)
  q : PtOk c base s (c.pt RX RY ONEP) Q

/-- What the table's additions write. -/
abbrev addsW : List (Nat × Nat) := [(64 + 8 * c.n * 17, 96 * c.n), (c.jt, 384 * c.n), (own c.n, 64 * c.n)]

/-- `Q`, the affine point of `R`'s first two slots. -/
abbrev qOf (base : Addr) (s : State) : Point c.C := .affine (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))

/-- What the table's construction writes. -/
abbrev buildW : List (Nat × Nat) := [(64 + 8 * c.n * 17, 96 * c.n), (c.jt, 384 * c.n), (own c.n, 64 * c.n)]

/-- What `vg_<curve>_mul`'s body reads at the start. -/
structure WPre (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  kc : KC c base s
  x : wordsVal s.mem base (c.sl RX) c.n < c.C.p
  y : wordsVal s.mem base (c.sl RY) c.n < c.C.p
  on : onCurve c.C (qOf c base s) = true

/-- What the windows read and keep, from `s₀`. -/
structure WFix (base : Addr) (s₀ : State) (Q : Point c.C) (k : Nat) : Prop where
  kc : KC c base s₀
  tab : TabTo c base s₀ Q 15
  kk : wordsVal s₀.mem base (c.sl K) c.n = k
  q : onCurve c.C Q = true

/-- What the windows write. -/
abbrev stepW : List (Nat × Nat) := [(64 + 8 * c.n * 14, 120 * c.n), (64 + 8 * c.n * 58, 24 * c.n), (own c.n, 64 * c.n)]

/-- The loop's invariant at `s1 = j`: `R` represents `[k >>> 4 j]Q`. -/
structure WInv (base : Addr) (s₀ s : State) (Q : Point c.C) (k j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base (stepW c) s₀.mem s.mem
  rep : PtOk c base s (c.pt RX RY RZ) (wpt Q k j)

/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(64 + 8 * c.n * 14, 120 * c.n), (64 + 8 * c.n * 58, 24 * c.n), (c.jt, 384 * c.n), (own c.n, 64 * c.n)]
end

theorem TabTo.of_eq {c : Cfg} {base : Addr} {s s' : State} {Q : Point c.C} {m : Nat} (h : TabTo c base s Q m)
    (he : ∀ d, c.jt ≤ d → d + 8 * c.n ≤ (c.jt + 384 * c.n) → wordsVal s'.mem base d c.n = wordsVal s.mem base d c.n)
    (hm : m ≤ 15) : TabTo c base s' Q m := fun e hlt => by
  have h15 := Nat.mul_le_mul_left (24 * c.n) (Nat.le_trans hlt hm)
  exact (h e hlt).of_eq (he (c.jt + 24 * c.n * e) (by omega_using []) (by omega_using [h15]))
    (he (c.jt + 24 * c.n * e + 8 * c.n) (by omega_using []) (by omega_using [h15]))
    (he (c.jt + 24 * c.n * e + 16 * c.n) (by omega_using []) (by omega_using [h15]))

/-! ## The layout, as arithmetic -/

/-- Slot `i`, as arithmetic has it. -/
theorem sl_eq (c : Cfg) (i : Nat) : c.sl i = 64 + 8 * c.n * i := rfl

/-- The field functions' own working space is above the slots. -/
theorem own_lo {n : Nat} (h : n ≤ 8) : 64 + 8 * n * 61 ≤ own n := by
  show _ ≤ rvOwn n
  rcases rvOwn_cases n with ⟨h6, e, -⟩ | ⟨h6, e, -⟩ <;> rw [e] <;> omega_using [h, h6]

/-- It is within the working space. -/
theorem own_hi {n : Nat} (h : n ≤ 8) : own n + 64 * n ≤ 8192 := by
  show rvOwn n + _ ≤ _
  rcases rvOwn_cases n with ⟨h6, e, -⟩ | ⟨h6, e, -⟩ <;> rw [e] <;> omega_using [h, h6]

/-- The table's entries, in order: the product of an entry's number is an atom to `omega`. -/
theorem ent_mono (n : Nat) {e e' : Nat} (h : e < e') : 24 * n * e + 24 * n ≤ 24 * n * e' := by
  have := Nat.mul_le_mul_left (24 * n) (Nat.succ_le_of_lt h)
  rwa [Nat.mul_succ] at this

theorem ent_le (n : Nat) {e e' : Nat} (h : e ≤ e') : 24 * n * e ≤ 24 * n * e' := Nat.mul_le_mul_left _ h

theorem sl_inj {c : Cfg} (n1 : 1 ≤ c.n) {i j : Nat} (e : c.sl i = c.sl j) : i = j := by
  have e' : 64 + 8 * c.n * i = 64 + 8 * c.n * j := e
  exact Nat.eq_of_mul_eq_mul_left (show 0 < 8 * c.n by omega_using [n1]) (Nat.add_left_cancel e')

/-- The slots a formula writes are distinct, and apart from those it reads, for points of numbered slots: by
their numbers. -/
theorem apart_rcb {c : Cfg} (n1 : 1 ≤ c.n) {i1 i2 i3 j1 j2 j3 k1 k2 k3 : Nat}
    (hk : [T0, T1, T2, T3, T4, T5, k1, k2, k3].Nodup)
    (ha : ∀ i ∈ [AP, B3P, i1, i2, i3, j1, j2, j3], i ∉ [T0, T1, T2, T3, T4, T5, k1, k2, k3]) :
    RcbApart c.rcbSlots (c.pt i1 i2 i3) (c.pt j1 j2 j3) (c.pt k1 k2 k3) := by
  have eW : rcbW c.rcbSlots (c.pt k1 k2 k3) = List.map c.sl [T0, T1, T2, T3, T4, T5, k1, k2, k3] := rfl
  have eR : rcbR c.rcbSlots (c.pt i1 i2 i3) (c.pt j1 j2 j3) = List.map c.sl [AP, B3P, i1, i2, i3, j1, j2, j3] := rfl
  refine ⟨?_, fun x hx hx' => ?_⟩
  · rw [eW]
    exact List.Pairwise.map _ (fun a b hab e => hab (sl_inj n1 e)) hk
  · rw [eR] at hx
    rw [eW] at hx'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, e⟩ := List.mem_map.mp hx'
    obtain rfl := sl_inj n1 e
    exact ha _ hi hj

/-- A slot is among slots: the lists as their elements. -/
local macro "wa_mem" : tactic => `(tactic|
  simp only [Cfg.pt, Cfg.zeroPt, Cfg.rcbSlots, rcbW, rcbR, wSl, quadWl, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, eq_self, true_or, or_true, and_self])

/-- The bounds of a layout, for the arithmetic on offsets: the words, the table and the field functions' own
working space (`Kit.bounds`). -/
abbrev Bnd (c : Cfg) : Prop := 1 ≤ c.n ∧ c.n ≤ 8 ∧ 64 + 8 * c.n * 61 ≤ c.jt ∧ c.jt ≤ 4096 ∧
  c.jt + 384 * c.n ≤ 8192 ∧ 64 + 8 * c.n * 61 ≤ own c.n ∧ own c.n + 64 * c.n ≤ 8192

/-! The slots, in order: the facts about one slot that the proof uses most, by the slots' numbers. -/

theorem sl_lt (c : Cfg) {i j : Nat} (h : i < j) : c.sl i + 8 * c.n ≤ 64 + 8 * c.n * j := by
  have := Nat.mul_le_mul_left (8 * c.n) (Nat.succ_le_of_lt h)
  rw [Nat.mul_succ] at this
  show 64 + 8 * c.n * i + 8 * c.n ≤ _
  omega_using [this]

theorem sl_out (c : Cfg) {i a b : Nat} (h : i < a ∨ b ≤ i) :
    c.sl i + 8 * c.n ≤ 64 + 8 * c.n * a ∨ 64 + 8 * c.n * b ≤ c.sl i :=
  h.imp (sl_lt c) fun h => Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _

theorem sl8 (c : Cfg) (i : Nat) : c.sl i % 8 = 0 := by
  show (64 + 8 * c.n * i) % 8 = 0
  rw [Nat.mul_assoc]; omega_using []

theorem sl_top {c : Cfg} (L : Bnd c) {i : Nat} (h : i ≤ 62) : c.sl i + 8 * c.n ≤ 4096 := by
  have := sl_lt c (Nat.lt_succ_of_le h)
  omega_using [this, L.2.1, Nat.mul_le_mul_left (8 * c.n) (Nat.succ_le_succ h)]

theorem sl_ws {c : Cfg} (L : Bnd c) {i : Nat} (h : i ≤ 62) : c.sl i + 8 * c.n ≤ 8192 :=
  Nat.le_trans (sl_top L h) (by decide)

theorem sl_fit {c : Cfg} (L : Bnd c) {i : Nat} (h : i ≤ 62) : c.sl i + 8 * c.n ≤ 2 ^ 64 :=
  Nat.le_trans (sl_top L h) (by decide)

/-- A slot a formula does not write, by its number. -/
theorem sl_notin {c : Cfg} (n1 : 1 ≤ c.n) {i k1 k2 k3 : Nat} (h : i ∉ [T0, T1, T2, T3, T4, T5, k1, k2, k3]) :
    c.sl i ∉ rcbW c.rcbSlots (c.pt k1 k2 k3) := fun hx => by
  have eW : rcbW c.rcbSlots (c.pt k1 k2 k3) = List.map c.sl [T0, T1, T2, T3, T4, T5, k1, k2, k3] := rfl
  rw [eW] at hx
  obtain ⟨j, hj, e⟩ := List.mem_map.mp hx
  exact h (sl_inj n1 e ▸ hj)

/-- Slots among slots, by their numbers. -/
theorem sub_sl {c : Cfg} {I J : List Nat} (h : ∀ i ∈ I, i ∈ J) : ∀ x ∈ I.map c.sl, x ∈ J.map c.sl := fun x hx => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map_of_mem (h i hi)

/-- The slots a formula writes are among those `R = 16 R` writes. -/
theorem rcbW_quad {c : Cfg} {k1 k2 k3 : Nat}
    (h : ∀ i ∈ [T0, T1, T2, T3, T4, T5, k1, k2, k3],
      i ∈ [T0, T1, T2, T3, T4, T5, RX, RY, RZ, DX, DY, DZ, TX, TY, TZ]) :
    ∀ w ∈ rcbW c.rcbSlots (c.pt k1 k2 k3), w ∈ quadWl c :=
  sub_sl h

/-- The slots of a formula are among `wSl`. -/
theorem rcb_wSl {c : Cfg} {i1 i2 i3 j1 j2 j3 k1 k2 k3 : Nat}
    (h : ∀ i ∈ [T0, T1, T2, T3, T4, T5, k1, k2, k3, AP, B3P, i1, i2, i3, j1, j2, j3],
      i ∈ [AP, B3P, ZERO, T0, T1, T2, T3, T4, T5, RX, RY, RZ, DX, DY, DZ, TX, TY, TZ]) :
    ∀ x ∈ rcbW c.rcbSlots (c.pt k1 k2 k3) ++ rcbR c.rcbSlots (c.pt i1 i2 i3) (c.pt j1 j2 j3), x ∈ wSl c :=
  sub_sl h

/-- A slot is below the field functions' own working space. -/
theorem sl_own {c : Cfg} (L : Bnd c) {i : Nat} (h : i < 61) :
    c.sl i + 8 * c.n ≤ own c.n ∨ own c.n + 64 * c.n ≤ c.sl i ∧ c.sl i + 8 * c.n ≤ 8192 :=
  .inl (Nat.le_trans (sl_lt c h) L.2.2.2.2.2.1)

/-- A fact about closed lists of slots and ranges, where none of the facts about one slot above is it: the lists
as their elements and the slots as `64 + 8 n i`, then arithmetic on each conjunct, with the layout's bounds
(`Kit.bounds`) from the context. -/
local macro "wa_dec" : tactic => `(tactic| (
  (try simp only [sl_eq, Cfg.pt, Cfg.zeroPt, Cfg.rcbSlots, rcbW, rcbR, wSl, quadWl, quadW, addsW, buildW, stepW, bodyW,
    addW, ent, ePt, ZERO, ONEP, AP, B3P, RX, RY, RZ, DX, DY, DZ, TX, TY, TZ, T0, T1, T2, T3, T4, T5, K,
    List.cons_append, List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    List.nodup_cons, List.nodup_nil, or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    not_false_eq_true, eq_self, true_or, or_true, and_self, and_true, true_and]) <;>
  (repeat' apply And.intro) <;> omega_arith))

/-! ## The kit -/

/-- What the proof needs of a curve. -/
structure Kit where
  c : Cfg
  /-- The slots of the complete additions. -/
  jSl : List Nat
  /-- The bytes below which a slot is read through `ld`'s offsets and is below the table. -/
  l1 : Nat
  /-- The numbers have at least one word. -/
  n1 : 1 ≤ c.n
  /-- The numbers have at most eight words. -/
  n8 : c.n ≤ 8
  /-- The table is aligned. -/
  jt8 : c.jt % 8 = 0
  /-- The table is above the slots: the last is `E`'s third, slot 60. -/
  jt_lo : 64 + 8 * c.n * 61 ≤ c.jt
  /-- The table starts no later than byte 4096. -/
  jt_top : c.jt ≤ 4096
  /-- The table's sixteen entries of `24 n` bytes are within the working space. -/
  jt_hi : c.jt + 384 * c.n ≤ 8192
  /-- The table is apart from the field functions' own working space. -/
  tab_own : c.jt + 384 * c.n ≤ own c.n ∨ own c.n + 64 * c.n ≤ c.jt
  /-- `l1` is above the numbered slots. -/
  l1_lo : 64 + 8 * c.n * 29 ≤ l1
  /-- `l1` is within `ld`'s offsets. -/
  l1_hi : l1 ≤ 4095
  /-- `l1` is below the table. -/
  l1_jt : l1 ≤ c.jt
  /-- The entry `E` of a window is at slot 58. -/
  ve : c.ve = 58
  /-- The slots of the table's additions, `T = D + Q`, are among `jSl`. -/
  jSl_adds : ∀ (x : Nat), x ∈ rcbW c.rcbSlots (c.pt TX TY TZ) ++ rcbR c.rcbSlots (c.pt DX DY DZ) (c.pt RX RY ONEP) → x ∈ jSl
  /-- The slots of a window's addition, `T = R + E`, are among `jSl`. -/
  jSl_step : ∀ (x : Nat), x ∈ rcbW c.rcbSlots (c.pt TX TY TZ) ++ rcbR c.rcbSlots (c.pt RX RY RZ) (ePt c) → x ∈ jSl
  /-- The curve's prime is not zero. -/
  p0 : 0 < c.C.p
  unit : UnitMod c.C.p (2 ^ (64 * c.n))
  /-- The Jacobian doubling, and the steps of `R = 16 R` on the field's programs. -/
  dbl : RcbSlots → Pt → Pt → List FOp
  dblStep_ok : Law c.C → ∀ {base : Addr} {s : State} {p o : Pt}, RcbApart c.rcbSlots p p o →
    (∀ x ∈ rcbW c.rcbSlots o ++ rcbR c.rcbSlots p p, x ∈ wSl c) → ∀ {V : List Nat} {E : Nat → Fe c.C},
    Inv c.n base c.C.p (· ∈ wSl c) V E s → (∀ x ∈ rcbR c.rcbSlots p p, x ∈ V) →
    E (c.sl AP) = Fin.ofNat c.C.p c.C.a → ∀ {P : Point c.C},
    onCurve c.C P = true → InvJ c.C (E p.x) (E p.y) (E p.z) P →
    WP isa (fprog c.FP (dbl c.rcbSlots p o)) s fun s' => KeepR c.n base (rcbW c.rcbSlots o) s s' ∧
      ∃ E', Inv c.n base c.C.p (· ∈ wSl c) ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ c.C (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW c.rcbSlots o → E' x = E x
  toJStep_ok : Law c.C → ∀ {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe c.C},
    Inv c.n base c.C.p (· ∈ wSl c) V E s →
    (∀ x ∈ rcbR c.rcbSlots (c.pt RX RY RZ) (Cfg.zeroPt c), x ∈ V) → ∀ {P : Point c.C},
    Rep c.C (E (c.sl RX)) (E (c.sl RY)) (E (c.sl RZ)) P → E (c.sl ZERO) = 0 →
    WP isa (fprog c.FP (toJ c.rcbSlots (c.pt RX RY RZ) (Cfg.zeroPt c) (c.pt DX DY DZ))) s fun s' =>
      KeepR c.n base (rcbW c.rcbSlots (c.pt DX DY DZ)) s s' ∧
      ∃ E', Inv c.n base c.C.p (· ∈ wSl c) ([c.sl DX, c.sl DY, c.sl DZ] ++ V) E' s' ∧
        InvJ c.C (E' (c.sl DX)) (E' (c.sl DY)) (E' (c.sl DZ)) P ∧
        ∀ x, x ∉ rcbW c.rcbSlots (c.pt DX DY DZ) → E' x = E x
  fromJStep_ok : ∀ {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe c.C},
    Inv c.n base c.C.p (· ∈ wSl c) V E s →
    (∀ x ∈ rcbR c.rcbSlots (c.pt DX DY DZ) (Cfg.zeroPt c), x ∈ V) →
    WP isa (fprog c.FP (fromJ c.rcbSlots (c.pt DX DY DZ) (Cfg.zeroPt c) (c.pt RX RY RZ))) s fun s' =>
      KeepR c.n base (rcbW c.rcbSlots (c.pt RX RY RZ)) s s' ∧
      ∃ E', Inv c.n base c.C.p (· ∈ wSl c) ([c.sl RX, c.sl RY, c.sl RZ] ++ V) E' s' ∧
        (E' (c.sl RX), E' (c.sl RY), E' (c.sl RZ)) =
          (E (c.sl DX) * E (c.sl DZ), E (c.sl DY) + E (c.sl ZERO),
            E (c.sl DZ) * E (c.sl DZ) * E (c.sl DZ)) ∧
        ∀ x, x ∉ rcbW c.rcbSlots (c.pt RX RY RZ) → E' x = E x
  /-- The complete addition, for points in slots of `jSl`. -/
  addPt_ok : Law c.C → ∀ {base : Addr} {s : State}, WsReg s base →
    wordsVal s.mem base (c.sl AP) c.n = c.C.a * 2 ^ (64 * c.n) % c.C.p →
    wordsVal s.mem base (c.sl B3P) c.n = 3 * c.C.b * 2 ^ (64 * c.n) % c.C.p →
    ∀ {p q o : Pt}, RcbApart c.rcbSlots p q o →
    (∀ x ∈ rcbW c.rcbSlots o ++ rcbR c.rcbSlots p q, x ∈ jSl) →
    ∀ {P P' : Point c.C}, onCurve c.C P = true → onCurve c.C P' = true →
    PtOk c base s p P → PtOk c base s q P' →
    WP isa (Verify.Cfg.addPt c p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW c o) s.mem s'.mem ∧ PtOk c base s' o (Spec.Weierstrass.add P P')

namespace Kit

/-- The bounds of the layout, for the arithmetic on offsets: the words, the table and the field functions' own
working space. -/
theorem bounds (Kt : Kit) : 1 ≤ Kt.c.n ∧ Kt.c.n ≤ 8 ∧ 64 + 8 * Kt.c.n * 61 ≤ Kt.c.jt ∧ Kt.c.jt ≤ 4096 ∧
    Kt.c.jt + 384 * Kt.c.n ≤ 8192 ∧ 64 + 8 * Kt.c.n * 61 ≤ own Kt.c.n ∧ own Kt.c.n + 64 * Kt.c.n ≤ 8192 :=
  ⟨Kt.n1, Kt.n8, Kt.jt_lo, Kt.jt_top, Kt.jt_hi, own_lo Kt.n8, own_hi Kt.n8⟩

/-- The bounds of `l1`. -/
theorem l1b (Kt : Kit) : 64 + 8 * Kt.c.n * 29 ≤ Kt.l1 ∧ Kt.l1 ≤ 4095 ∧ Kt.l1 ≤ Kt.c.jt :=
  ⟨Kt.l1_lo, Kt.l1_hi, Kt.l1_jt⟩

/-- The slots of the entry `E`. -/
theorem ePt_eq (Kt : Kit) : Kt.c.pt Kt.c.EX Kt.c.EY Kt.c.EZ = ePt Kt.c := by
  simp only [ePt, Cfg.EX, Cfg.EY, Cfg.EZ, Kt.ve, Nat.reduceAdd]

theorem slE (Kt : Kit) : Kt.c.sl Kt.c.EX = 64 + 8 * Kt.c.n * 58 := by
  simp only [Cfg.sl, slot, Cfg.EX, Kt.ve]

theorem dbl_apart_DT (Kt : Kit) : RcbApart Kt.c.rcbSlots (Kt.c.pt DX DY DZ) (Kt.c.pt DX DY DZ) (Kt.c.pt TX TY TZ) :=
  apart_rcb Kt.n1 (by decide) (by decide)

theorem dbl_apart_TD (Kt : Kit) : RcbApart Kt.c.rcbSlots (Kt.c.pt TX TY TZ) (Kt.c.pt TX TY TZ) (Kt.c.pt DX DY DZ) :=
  apart_rcb Kt.n1 (by decide) (by decide)

/-- Slots apart from what code writes are kept. -/
theorem keepU (Kt : Kit) {base : Addr} {Wl : List (Nat × Nat)} {m m' : Mem} (U : Unch base Wl m m') {D : List Nat}
    (hD : ∀ d ∈ D, (∀ w ∈ Wl, d + 8 * Kt.c.n ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 8 * Kt.c.n ≤ Kt.l1) :
    ∀ d ∈ D, wordsVal m' base d Kt.c.n = wordsVal m base d Kt.c.n := fun d hd =>
  U.wordsVal (hD d hd).1 (by have := (hD d hd).2; omega_using [this, Kt.l1_hi])

/-! ## `R = 16 R` -/

/-- `R = 16 R`, for `R` representing `P`. -/
theorem quad_ok (Kt : Kit) (hL : Law Kt.c.C) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC Kt.c base s) {P : Point Kt.c.C}
    (hP : onCurve Kt.c.C P = true) (hR : PtOk Kt.c base s (Kt.c.pt RX RY RZ) P) :
    WP isa (Cfg.quad Kt.c Kt.dbl) s fun s' => Kp s s' ∧ Unch base (quadW Kt.c) s.mem s'.mem ∧
      PtOk Kt.c base s' (Kt.c.pt RX RY RZ) (d16 P) := by
  have L := Kt.bounds
  obtain hp0 : 0 < Kt.c.C.p := Kt.p0
  have hn := hw.nowrap
  rw [Cfg.quad]
  simp only [progs]
  -- The start: `a`, `b`, zero and `R`.
  obtain hI : Inv Kt.c.n base Kt.c.C.p (· ∈ (wSl Kt.c)) [Kt.c.sl AP, Kt.c.sl B3P, Kt.c.sl ZERO, Kt.c.sl RX, Kt.c.sl RY, Kt.c.sl RZ]
      (fun x => toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (wordsVal s.mem base x Kt.c.n)) s := by
    refine ⟨hw, by wa_mem, fun x hx => ?_, fun x _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hK.ap]; exact Nat.mod_lt _ hp0
    · rw [hK.bp]; exact Nat.mod_lt _ hp0
    · rw [hK.zero]; exact hp0
    exacts [hR.x, hR.y, hR.z]
  obtain e0 : toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (wordsVal s.mem base (Kt.c.sl ZERO) Kt.c.n) = 0 := by
    rw [hK.zero]; exact toM_zero _ _
  obtain ea : toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (wordsVal s.mem base (Kt.c.sl AP) Kt.c.n) = Fin.ofNat Kt.c.C.p Kt.c.C.a := by
    rw [hK.ap, toM_mont Kt.unit]
  -- To Jacobian coordinates.
  refine WP.seq (WP.mono (Kt.toJStep_ok hL hI (by wa_mem) hR.rep e0) fun s₁ ⟨k₁, E₁, I₁, J₁, p₁⟩ => ?_)
  obtain a₁ : E₁ (Kt.c.sl AP) = Fin.ofNat Kt.c.C.p Kt.c.C.a := (p₁ _ (sl_notin Kt.n1 (by decide))).trans ea
  -- Four doublings.
  refine WP.seq (WP.mono (Kt.dblStep_ok hL Kt.dbl_apart_DT (rcb_wSl (by decide)) I₁ (by wa_mem) a₁ hP J₁)
    fun s₂ ⟨k₂, E₂, I₂, J₂, p₂⟩ => ?_)
  obtain a₂ : E₂ (Kt.c.sl AP) = Fin.ofNat Kt.c.C.p Kt.c.C.a := (p₂ _ (sl_notin Kt.n1 (by decide))).trans a₁
  refine WP.seq (WP.mono (Kt.dblStep_ok hL Kt.dbl_apart_TD (rcb_wSl (by decide)) I₂ (by wa_mem) a₂ (hL.onCurve_add hP hP) J₂)
    fun s₃ ⟨k₃, E₃, I₃, J₃, p₃⟩ => ?_)
  obtain a₃ : E₃ (Kt.c.sl AP) = Fin.ofNat Kt.c.C.p Kt.c.C.a := (p₃ _ (sl_notin Kt.n1 (by decide))).trans a₂
  obtain h4 := hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)
  refine WP.seq (WP.mono (Kt.dblStep_ok hL Kt.dbl_apart_DT (rcb_wSl (by decide)) I₃ (by wa_mem) a₃ h4 J₃)
    fun s₄ ⟨k₄, E₄, I₄, J₄, p₄⟩ => ?_)
  obtain a₄ : E₄ (Kt.c.sl AP) = Fin.ofNat Kt.c.C.p Kt.c.C.a := (p₄ _ (sl_notin Kt.n1 (by decide))).trans a₃
  refine WP.seq (WP.mono (Kt.dblStep_ok hL Kt.dbl_apart_TD (rcb_wSl (by decide)) I₄ (by wa_mem) a₄ (hL.onCurve_add h4 h4) J₄)
    fun s₅ ⟨k₅, E₅, I₅, J₅, p₅⟩ => ?_)
  -- Back to projective coordinates.
  refine WP.seq (WP.mono (Kt.fromJStep_ok I₅ (by wa_mem)) fun s₆ ⟨k₆, E₆, I₆, v₆, p₆⟩ => ?_)
  obtain z₅ : E₅ (Kt.c.sl ZERO) = 0 := by
    rw [p₅ _ (sl_notin Kt.n1 (by decide)), p₄ _ (sl_notin Kt.n1 (by decide)), p₃ _ (sl_notin Kt.n1 (by decide)), p₂ _
        (sl_notin Kt.n1 (by decide)), p₁ _ (sl_notin Kt.n1 (by decide))]; exact e0
  simp only [Prod.mk.injEq] at v₆
  obtain ⟨vx, vy, vz⟩ := v₆
  rw [z₅, Lean.Grind.AddCommMonoid.add_zero] at vy
  have hw₆ := I₆.ws
  have hn₆ := hw₆.nowrap
  obtain ltx := I₆.lt (Kt.c.sl RX) (List.mem_append_left _ (List.mem_cons_self))
  obtain lty := I₆.lt (Kt.c.sl RY) (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ltz := I₆.lt (Kt.c.sl RZ) (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  obtain vx' : tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RX) = E₆ (Kt.c.sl RX) := I₆.val (Kt.c.sl RX) (List.mem_append_left _
      (List.mem_cons_self))
  obtain vy' : tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RY) = E₆ (Kt.c.sl RY) := I₆.val (Kt.c.sl RY) (List.mem_append_left _
      (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain vz' : tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RZ) = E₆ (Kt.c.sl RZ) := I₆.val (Kt.c.sl RZ) (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  -- `Y = 1` where `Z = 0`.
  obtain KK : KeepR Kt.c.n base (quadWl Kt.c) s s₆ :=
    ((((k₁.mono (rcbW_quad (by decide))).trans (k₂.mono (rcbW_quad (by decide)))).trans ((k₃.mono (rcbW_quad (by decide))).trans
      (k₄.mono (rcbW_quad (by decide))))).trans ((k₅.mono (rcbW_quad (by decide))).trans (k₆.mono (rcbW_quad (by decide)))))
  have UK : Unch base ((quadWl Kt.c).map (fun w => (w, 8 * Kt.c.n)) ++ [(own Kt.c.n, 64 * Kt.c.n)]) s.mem s₆.mem := KK.mem
  obtain onep₆ : wordsVal s₆.mem base (Kt.c.sl ONEP) Kt.c.n = 2 ^ (64 * Kt.c.n) % Kt.c.C.p := by
    rw [UK.wordsVal (by wa_dec) (sl_fit L (by decide))]; exact hK.onep
  refine WP.block_append (WP.mono (zeroMask_ok hw₆ (n := Kt.c.n) (a := Kt.c.sl RZ) (sl8 _ _) (sl_top L (by decide)))
    fun s₇ ⟨r₇, m₇, a7₇⟩ => ?_)
  obtain hw₇ := hw₆.of_rest r₇
  refine WP.mono (sel_ok (decide (wordsVal s₆.mem base (Kt.c.sl RZ) Kt.c.n = 0)) Kt.c.n hw₇ a7₇
    (o := Kt.c.sl RY) (a := Kt.c.sl RY) (b := Kt.c.sl ONEP) (sl8 _ _) (sl8 _ _) (sl8 _ _) (sl_top L (by decide))
    (sl_top L (by decide)) (sl_top L (by decide)) (Or.inl (Nat.le_refl _)) (by wa_dec)) fun s₈ ⟨e₈, r₈, O₈⟩ => ?_
  rw [m₇] at e₈ O₈
  obtain ex : wordsVal s₈.mem base (Kt.c.sl RX) Kt.c.n = wordsVal s₆.mem base (Kt.c.sl RX) Kt.c.n :=
    O₈.wordsVal (by wa_dec) (sl_fit L (by decide))
  obtain ez : wordsVal s₈.mem base (Kt.c.sl RZ) Kt.c.n = wordsVal s₆.mem base (Kt.c.sl RZ) Kt.c.n :=
    O₈.wordsVal (by wa_dec) (sl_fit L (by decide))
  obtain hZ : (wordsVal s₆.mem base (Kt.c.sl RZ) Kt.c.n = 0) ↔ E₅ (Kt.c.sl DZ) = 0 := by
    rw [← toM_eq_zero_iff Kt.unit ltz]
    show tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RZ) = 0 ↔ _
    rw [vz', vz]
    exact ⟨fun h => by_contra fun hz => cube_ne_zero hL hz h, fun h => by rw [h]; grind⟩
  obtain hrep := InvJ.out hL J₅
  refine ⟨KK.kp.trans ((Kp.of_rest r₇).trans (Kp.of_rest r₈)), (UK.trans O₈.unch).cover (by wa_dec), ⟨?_, ?_, ?_, ?_⟩⟩
  · show Rep Kt.c.C (tmv Kt.c.C Kt.c.n base s₈ (Kt.c.sl RX)) (tmv Kt.c.C Kt.c.n base s₈ (Kt.c.sl RY)) (tmv Kt.c.C Kt.c.n base s₈
      (Kt.c.sl RZ)) _
    simp only [tmv]
    rw [ex, ez]
    show Rep Kt.c.C (tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RX)) _ (tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RZ)) _
    rw [vx', vz', vx, vz, e₈]
    by_cases h0 : E₅ (Kt.c.sl DZ) = 0
    · have hc : decide (wordsVal s₆.mem base (Kt.c.sl RZ) Kt.c.n = 0) = true := decide_eq_true (hZ.mpr h0)
      have h0' : E₅ (Kt.c.pt DX DY DZ).z = 0 := h0
      rw [show (if E₅ (Kt.c.pt DX DY DZ).z = 0 then (1 : Fe Kt.c.C) else E₅ (Kt.c.pt DX DY DZ).y) = 1 from
        by simp [h0']] at hrep
      simp only [hc, ↓reduceIte]
      rw [onep₆, toM_one Kt.unit]
      exact hrep
    · have hc : decide (wordsVal s₆.mem base (Kt.c.sl RZ) Kt.c.n = 0) = false :=
        decide_eq_false fun h => h0 (hZ.mp h)
      have h0' : ¬E₅ (Kt.c.pt DX DY DZ).z = 0 := h0
      rw [show (if E₅ (Kt.c.pt DX DY DZ).z = 0 then (1 : Fe Kt.c.C) else E₅ (Kt.c.pt DX DY DZ).y) =
        E₅ (Kt.c.pt DX DY DZ).y from by simp [h0']] at hrep
      simp only [hc, ↓reduceIte, Bool.false_eq_true]
      show Rep Kt.c.C _ (tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RY)) _ _
      rw [vy', vy]
      exact hrep
  · show wordsVal s₈.mem base (Kt.c.sl RX) Kt.c.n < Kt.c.C.p
    rw [ex]; exact ltx
  · show wordsVal s₈.mem base (Kt.c.sl RY) Kt.c.n < Kt.c.C.p
    rw [e₈]; split
    · rw [onep₆]; exact Nat.mod_lt _ (Kt.p0)
    · exact lty
  · show wordsVal s₈.mem base (Kt.c.sl RZ) Kt.c.n < Kt.c.C.p
    rw [ez]; exact ltz

/-! ## The table -/

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok (Kt : Kit) {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 8 = 0 ∧ x + 8 * Kt.c.n ≤ Kt.c.jt)
    (hxy : o.x + 8 * Kt.c.n ≤ o.y) (hyz : o.y + 8 * Kt.c.n ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 8 * Kt.c.n ≤ o.x ∨ o.z + 8 * Kt.c.n ≤ a) :
    WP isa (.block (Cfg.copyPt Kt.c o p)) s fun s' =>
      wordsVal s'.mem base o.x Kt.c.n = wordsVal s.mem base p.x Kt.c.n
          ∧ wordsVal s'.mem base o.y Kt.c.n = wordsVal s.mem base p.y Kt.c.n ∧
      wordsVal s'.mem base o.z Kt.c.n = wordsVal s.mem base p.z Kt.c.n ∧ Rest [.t0] s s' ∧
      Unch base [(o.x, 8 * Kt.c.n), (o.y, 8 * Kt.c.n), (o.z, 8 * Kt.c.n)] s.mem s'.mem := by
  have L := Kt.bounds
  have hn := hw.nowrap
  obtain g := fun x hx => h8 x hx
  obtain gp := fun x hx => hp x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g gp
  obtain ⟨⟨ox8, ox⟩, ⟨oy8, oy⟩, ⟨oz8, oz⟩, ⟨px8, px⟩, ⟨py8, py⟩, ⟨pz8, pz⟩⟩ := g
  obtain ⟨hpx, hpy, hpz⟩ := gp
  rw [Cfg.copyPt, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok Kt.c.n hw (o := o.x) (a := p.x) ox8 px8 (by omega_using [ox, L]) (by omega_using [px, L])
      (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]))
    fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (copy_ok Kt.c.n hw₁ (o := o.y) (a := p.y) oy8 py8 (by omega_using [oy, L]) (by omega_using [py, L])
      (by omega_using [hxy, hyz, hpy]))
    fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.mono (copy_ok Kt.c.n hw₂ (o := o.z) (a := p.z) oz8 pz8 (by omega_using [oz, L]) (by omega_using [pz, L])
      (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]))
    fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_, (r₁.trans r₂).trans r₃ |>.mono (by simp), ?_⟩
  · rw [O₃.wordsVal (by omega_using [hxy, hyz]) (by omega_using [ox, L]), O₂.wordsVal (by omega_using [hxy]) (by omega_using [ox, L]),
      e₁]
  · rw [O₃.wordsVal (by omega_using [hyz]) (by omega_using [oy, L]), e₂, O₁.wordsVal
      (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]) (by omega_using [py, L])]
  · rw [e₃, O₂.wordsVal (by omega_using [hxy, hyz, hpz]) (by omega_using [pz, L]), O₁.wordsVal
      (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]) (by omega_using [pz, L])]
  · exact ((O₁.unch.trans O₂.unch).trans O₃.unch).mono (by simp)

/-- `D`'s slots, as `copyPt` writes them. -/
theorem dSl (Kt : Kit) : ∀ w ∈ ([((Kt.c.pt DX DY DZ).x, 8 * Kt.c.n), ((Kt.c.pt DX DY DZ).y, 8 * Kt.c.n), ((Kt.c.pt DX DY DZ).z,
    8 * Kt.c.n)] : List (Nat × Nat)),
    64 + 8 * Kt.c.n * 17 ≤ w.1 ∧ w.1 + w.2 ≤ 64 + 8 * Kt.c.n * 20 := by
  have L := Kt.bounds
  wa_dec

/-- A point in slots below `l1` to entry `e`. -/
theorem store_ok (Kt : Kit) {s : State} {base : Addr} (hw : WsReg s base) {e : Nat} (he : e < 16) {p : Pt}
    (hs : ∀ x ∈ [p.x, p.y, p.z], x % 8 = 0 ∧ x + 8 * Kt.c.n ≤ Kt.l1) {P : Point Kt.c.C} (hp : PtOk Kt.c base s p P) :
    WP isa (.block (Verify.Cfg.storePt Kt.c e p)) s fun s' => PtOk Kt.c base s' (ent Kt.c e) P ∧ Rest [.t0, .a6] s s' ∧
      Outside base (Kt.c.jt + 24 * Kt.c.n * e) (24 * Kt.c.n) s.mem s'.mem := by
  have L := Kt.bounds
  have L1 := Kt.l1b
  have hn := hw.nowrap
  obtain g := fun x hx => hs x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨⟨hx8, hx⟩, ⟨hy8, hy⟩, ⟨hz8, hz⟩⟩ := g
  have he15 := ent_le Kt.c.n (Nat.le_of_lt_succ he)
  refine WP.mono (VG.Proof.Ecdsa.RISCV64.Joint.storePt_ok Kt.c hw (e := e) ⟨Kt.jt8, by wa_dec⟩
      (by show Kt.c.jt + 24 * Kt.c.n * e + 24 * Kt.c.n ≤ 8192; omega_using [he15, L, L1])
    (by show 24 * Kt.c.n * e + 24 * Kt.c.n ≤ 4095; omega_using [he15, L, L1])
        ⟨hx8, by show _ + 8 * Kt.c.n ≤ 4095; omega_using [hx, L, L1], by show _ + 8 * Kt.c.n ≤ Kt.c.jt; omega_using [hx, L, L1]⟩
    ⟨hy8, by show _ + 8 * Kt.c.n ≤ 4095; omega_using [hy, L, L1], by show _ + 8 * Kt.c.n ≤ Kt.c.jt; omega_using [hy, L, L1]⟩
    ⟨hz8, by show _ + 8 * Kt.c.n ≤ 4095; omega_using [hz, L, L1], by show _ + 8 * Kt.c.n ≤ Kt.c.jt; omega_using [hz, L, L1]⟩)
        fun s' ⟨ex, ey, ez, r, O⟩ => ?_
  simp only [show Verify.Cfg.jb Kt.c = 24 * Kt.c.n from rfl] at ex ey ez O
  exact ⟨hp.move ex ey ez, r, O⟩

/-- An addition's writes into `T`, within `addsW`, and apart from the table. -/
theorem addW_T (Kt : Kit) : ∀ w ∈ addW Kt.c (Kt.c.pt TX TY TZ), (∃ w' ∈ (addsW Kt.c), w'.1 ≤ w.1
    ∧ w.1 + w.2 ≤ w'.1 + w'.2) ∧
    (w.1 + w.2 ≤ Kt.c.jt ∨ Kt.c.jt + 384 * Kt.c.n ≤ w.1) := by
  have L := Kt.bounds
  have T := Kt.tab_own
  wa_dec

/-- `copyPt`'s writes into `D`, within `addsW`. -/
theorem dW (Kt : Kit) : ∀ w ∈ ([((Kt.c.pt DX DY DZ).x, 8 * Kt.c.n), ((Kt.c.pt DX DY DZ).y, 8 * Kt.c.n), ((Kt.c.pt DX DY DZ).z,
    8 * Kt.c.n)] : List (Nat × Nat)),
    ∃ w' ∈ (addsW Kt.c), w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  have L := Kt.bounds
  wa_dec

/-- Entry `e`'s bytes, within `addsW`. -/
theorem entW (Kt : Kit) {e : Nat} (he : e < 16) : ∃ w' ∈ (addsW Kt.c), w'.1 ≤ Kt.c.jt + 24 * Kt.c.n * e
    ∧ Kt.c.jt + 24 * Kt.c.n * e + 24 * Kt.c.n ≤ w'.1 + w'.2 := by
  have he15 := ent_le Kt.c.n (Nat.le_of_lt_succ he)
  exact ⟨(Kt.c.jt, 384 * Kt.c.n), List.mem_cons_of_mem _ List.mem_cons_self, by simp only; omega_using [], by simp only; omega_using [he15]⟩

/-- Entry `e`, kept by memory unchanged there. -/
theorem ent_of (Kt : Kit) {base : Addr} {s s' : State} {e : Nat} {P : Point Kt.c.C} (h : PtOk Kt.c base s (ent Kt.c e) P)
    (k : ∀ d, Kt.c.jt + 24 * Kt.c.n * e ≤ d → d + 8 * Kt.c.n ≤ Kt.c.jt + 24 * Kt.c.n * e + 24 * Kt.c.n
        → wordsVal s'.mem base d Kt.c.n = wordsVal s.mem base d Kt.c.n) :
    PtOk Kt.c base s' (ent Kt.c e) P := by
  exact h.of_eq (k (Kt.c.jt + 24 * Kt.c.n * e) (Nat.le_refl _) (by omega_using [])) (k (Kt.c.jt + 24 * Kt.c.n * e + 8 * Kt.c.n)
      (by omega_using []) (by omega_using []))
    (k (Kt.c.jt + 24 * Kt.c.n * e + 16 * Kt.c.n) (by omega_using []) (by omega_using []))

/-- The additions of `[e]Q` for `e = 2 … m + 1`. -/
theorem adds_ok (Kt : Kit) (hL : Law Kt.c.C) {base : Addr} {Q : Point Kt.c.C} (hQ : onCurve Kt.c.C Q = true) :
    ∀ m ≤ 14, ∀ {s : State}, AI Kt.c base s Q 0 →
      WP isa (Cfg.adds Kt.c m) s fun s' => Kp s s' ∧ Unch base (addsW Kt.c) s.mem s'.mem ∧ AI Kt.c base s' Q m
  | 0, _, s, h => WP.block_nil ⟨Kp.refl _, Unch.refl _ _ _, h⟩
  | m + 1, hm, s, h => by
    have L := Kt.bounds
    have L1 := Kt.l1b
    rw [Cfg.adds]
    refine WP.seq (WP.mono (Kt.adds_ok hL hQ m (by omega_using [hm]) h) fun s₁ ⟨k₁, U₁, A₁⟩ => ?_)
    have hw₁ := A₁.ws
    have hn := hw₁.nowrap
    -- `T = D + Q`.
    refine WP.seq (WP.mono (Kt.addPt_ok hL hw₁ A₁.kc.ap A₁.kc.bp (p := Kt.c.pt DX DY DZ) (q := Kt.c.pt RX RY ONEP)
      (o := Kt.c.pt TX TY TZ) (apart_rcb Kt.n1 (by decide) (by decide)) Kt.jSl_adds (hL.onCurve_mul hQ _) hQ A₁.d A₁.q)
      fun s₂ ⟨k₂, U₂, p₂⟩ => ?_)
    rw [mul_succ' hL hQ, show m + 1 + 1 = m + 2 by omega_using []] at p₂
    obtain hw₂ := hw₁.of_kp k₂
    obtain e₂ : ∀ d ∈ [Kt.c.sl AP, Kt.c.sl B3P, Kt.c.sl ZERO, Kt.c.sl ONEP] ++ [Kt.c.sl RX, Kt.c.sl RY],
        wordsVal s₂.mem base d Kt.c.n =
        wordsVal s₁.mem base d Kt.c.n := Kt.keepU U₂ (by wa_dec)
    obtain far₂ : ∀ d, Kt.c.jt ≤ d → d + 8 * Kt.c.n ≤ Kt.c.jt + 384 * Kt.c.n
        → wordsVal s₂.mem base d Kt.c.n = wordsVal s₁.mem base d Kt.c.n :=
      fun d h1 h2 => U₂.wordsVal (fun w hw => by have := (Kt.addW_T w hw).2; omega_using [h1, h2, this]) (by omega_using [h2, L, L1])
    -- Stored to entry `m + 2`.
    refine WP.block_append (WP.mono (Kt.store_ok hw₂ (e := m + 2) (by omega_using [hm]) (by wa_dec) p₂)
      fun s₃ ⟨p₃, r₃, O₃⟩ => ?_)
    obtain hw₃ := hw₂.of_rest r₃
    obtain e₃ : ∀ d, d + 8 * Kt.c.n ≤ Kt.l1 → wordsVal s₃.mem base d Kt.c.n = wordsVal s₂.mem base d Kt.c.n := fun d hd =>
      O₃.wordsVal (by omega_using [hd, L, L1]) (by omega_using [hd, L, L1])
    obtain pT₃ : PtOk Kt.c base s₃ (Kt.c.pt TX TY TZ) (mul (m + 2) Q) :=
      p₂.of_eq (e₃ _ (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo)) (e₃ _ (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo)) (e₃ _
          (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo))
    -- `D = T`.
    refine WP.mono (Kt.copyPt_ok hw₃ (o := Kt.c.pt DX DY DZ) (p := Kt.c.pt TX TY TZ) (by wa_dec) (sl_lt _ (by decide)) (sl_lt _
        (by decide))
      (by wa_dec)) fun s₄ ⟨x₄, y₄, z₄, r₄, U₄⟩ => ?_
    obtain e₄ : ∀ d, (d + 8 * Kt.c.n ≤ 64 + 8 * Kt.c.n * 17 ∨ 64 + 8 * Kt.c.n * 20 ≤ d) → d + 8 * Kt.c.n ≤ 8192
        → wordsVal s₄.mem base d Kt.c.n = wordsVal s₃.mem base d Kt.c.n :=
      fun d h1 h2 => U₄.wordsVal (fun w hw => by have := Kt.dSl w hw; omega_using [h1, this]) (by omega_using [h2])
    obtain kd : ∀ d ∈ [Kt.c.sl AP, Kt.c.sl B3P, Kt.c.sl ZERO, Kt.c.sl ONEP] ++ [Kt.c.sl RX, Kt.c.sl RY],
        wordsVal s₄.mem base d Kt.c.n = wordsVal s₁.mem base d Kt.c.n := fun d hd => by
      obtain hd' : d + 8 * Kt.c.n ≤ 64 + 8 * Kt.c.n * 17 :=
        (by wa_dec : ∀ d ∈ [Kt.c.sl AP, Kt.c.sl B3P, Kt.c.sl ZERO, Kt.c.sl ONEP] ++ [Kt.c.sl RX, Kt.c.sl RY],
          d + 8 * Kt.c.n ≤ 64 + 8 * Kt.c.n * 17) d hd
      rw [e₄ d (.inl hd') (by omega_using [hd', L, L1]), e₃ d (by omega_using [hd', L, L1]), e₂ d hd]
    refine ⟨k₁.trans (k₂.trans ((Kp.of_rest r₃).trans (Kp.of_rest r₄))), ?_, ⟨hw₃.of_rest r₄, ?_, ?_, ?_, ?_⟩⟩
    · refine (((U₁.trans U₂).trans O₃.unch).trans U₄).cover fun w hw => ?_
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · rcases List.mem_append.mp hw with hw | hw
          · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
          · exact (Kt.addW_T w hw).1
        · rw [List.mem_singleton] at hw
          subst hw
          exact Kt.entW (by omega_using [hm])
      · exact Kt.dW w hw
    · exact A₁.kc.of_eq fun d hd => kd d (List.mem_append_left _ hd)
    · intro e he
      obtain he15 : 24 * Kt.c.n * e ≤ 24 * Kt.c.n * 15 := ent_le _ (by omega_using [hm, he])
      rcases Nat.lt_or_ge e (m + 2) with h | h
      · have pe := A₁.tab e (by omega_using [h])
        obtain hlt := ent_mono Kt.c.n h
        exact Kt.ent_of pe fun d h1 h2 => by
          rw [e₄ d (.inr (by omega_using [h1, L, L1])) (by omega_using [h2, he15, L, L1]), O₃.wordsVal (by omega_using [h2, hlt])
              (by omega_using [h2, he15, L, L1]),
            far₂ d (by omega_using [h1]) (by omega_using [h2, he15])]
      · obtain rfl : e = m + 2 := by omega_using [he, h]
        exact Kt.ent_of p₃ fun d h1 h2 => e₄ d (.inr (by omega_using [h1, L, L1])) (by omega_using [h2, he15, L, L1])
    · exact pT₃.move x₄ y₄ z₄
    · exact A₁.q.of_eq (kd _ (by wa_mem)) (kd _ (by wa_mem)) (kd _ (by wa_mem))

/-- The table of `[e]Q`. -/
theorem build_ok (Kt : Kit) (hL : Law Kt.c.C) {base : Addr} {s : State} (hp : WPre Kt.c base s) :
    WP isa (Cfg.build Kt.c) s fun s' => Kp s s' ∧ Unch base (buildW Kt.c) s.mem s'.mem ∧ KC Kt.c base s' ∧
      TabTo Kt.c base s' (qOf Kt.c base s) 15 ∧
      ∀ d, d + 8 * Kt.c.n ≤ 64 + 8 * Kt.c.n * 17 → wordsVal s'.mem base d Kt.c.n = wordsVal s.mem base d Kt.c.n := by
  have L := Kt.bounds
  have L1 := Kt.l1b
  have hw := hp.ws
  have hn := hw.nowrap
  obtain hp0 : 0 < Kt.c.C.p := Kt.p0
  have hK := hp.kc
  obtain h1 : tmv Kt.c.C Kt.c.n base s (Kt.c.sl ONEP) = 1 := by
    simp only [tmv]; rw [hK.onep]; exact toM_one Kt.unit
  obtain h0 : tmv Kt.c.C Kt.c.n base s (Kt.c.sl ZERO) = 0 := by
    simp only [tmv]; rw [hK.zero]; exact toM_zero _ _
  obtain pO : PtOk Kt.c base s (Kt.c.pt ZERO ONEP ZERO) (mul 0 (qOf Kt.c base s)) := by
    refine ⟨?_, show wordsVal _ _ (Kt.c.sl ZERO) Kt.c.n < _ by rw [hK.zero]; exact hp0,
      show wordsVal _ _ (Kt.c.sl ONEP) Kt.c.n < _ by rw [hK.onep]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (Kt.c.sl ZERO) Kt.c.n < _ by rw [hK.zero]; exact hp0⟩
    show Rep Kt.c.C (tmv Kt.c.C Kt.c.n base s (Kt.c.sl ZERO)) (tmv Kt.c.C Kt.c.n base s (Kt.c.sl ONEP)) (tmv Kt.c.C Kt.c.n base s
        (Kt.c.sl ZERO)) _
    rw [h0, h1, mul_zero']
    exact rep_infinity' hL
  obtain pQ : PtOk Kt.c base s (Kt.c.pt RX RY ONEP) (qOf Kt.c base s) := by
    refine ⟨?_, hp.x, hp.y, show wordsVal _ _ (Kt.c.sl ONEP) Kt.c.n < _ by rw [hK.onep]; exact Nat.mod_lt _ hp0⟩
    show Rep Kt.c.C (tmv Kt.c.C Kt.c.n base s (Kt.c.sl RX)) (tmv Kt.c.C Kt.c.n base s (Kt.c.sl RY)) (tmv Kt.c.C Kt.c.n base s
        (Kt.c.sl ONEP)) _
    rw [h1]
    exact rep_affine' hL _ _
  rw [Cfg.build, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (Kt.store_ok hw (e := 0) (by decide) (by wa_dec) pO)
    fun s₁ ⟨p₁, r₁, O₁⟩ => ?_))
  obtain hw₁ := hw.of_rest r₁
  obtain e₁ : ∀ d, d + 8 * Kt.c.n ≤ Kt.l1 → wordsVal s₁.mem base d Kt.c.n = wordsVal s.mem base d Kt.c.n := fun d hd =>
    O₁.wordsVal (by omega_using [hd, L, L1]) (by omega_using [hd, L, L1])
  refine WP.block_append (WP.mono (Kt.store_ok hw₁ (e := 1) (by decide) (by wa_dec)
    (pQ.of_eq (e₁ _ (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo)) (e₁ _ (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo)) (e₁ _
        (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo)))) fun s₂ ⟨p₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  obtain e₂ : ∀ d, d + 8 * Kt.c.n ≤ Kt.l1 → wordsVal s₂.mem base d Kt.c.n = wordsVal s.mem base d Kt.c.n := fun d hd => by
    rw [O₂.wordsVal (by omega_using [hd, L, L1]) (by omega_using [hd, L, L1]), e₁ d hd]
  refine WP.mono (Kt.copyPt_ok hw₂ (o := Kt.c.pt DX DY DZ) (p := Kt.c.pt RX RY ONEP) (by wa_dec) (sl_lt _ (by decide)) (sl_lt _
      (by decide))
    (by wa_dec)) fun s₃ ⟨x₃, y₃, z₃, r₃, U₃⟩ => ?_
  obtain hw₃ := hw₂.of_rest r₃
  obtain e₃ : ∀ d, (d + 8 * Kt.c.n ≤ 64 + 8 * Kt.c.n * 17 ∨ 64 + 8 * Kt.c.n * 20 ≤ d) → d + 8 * Kt.c.n ≤ 8192
      → wordsVal s₃.mem base d Kt.c.n = wordsVal s₂.mem base d Kt.c.n :=
    fun d h1 h2 => U₃.wordsVal (fun w hw => by have := Kt.dSl w hw; omega_using [h1, this]) (by omega_using [h2])
  obtain pQ₃ : PtOk Kt.c base s₃ (Kt.c.pt RX RY ONEP) (qOf Kt.c base s) :=
    pQ.of_eq ((e₃ _ (.inl (sl_lt _ (by decide))) (sl_ws L (by decide))).trans (e₂ _ (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo)))
      ((e₃ _ (.inl (sl_lt _ (by decide))) (sl_ws L (by decide))).trans (e₂ _ (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo)))
      ((e₃ _ (.inl (sl_lt _ (by decide))) (sl_ws L (by decide))).trans (e₂ _ (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo)))
  obtain hA : AI Kt.c base s₃ (qOf Kt.c base s) 0 := by
    refine ⟨hw₃, hK.of_eq fun d hd => ?_, fun e he => ?_, ?_, pQ₃⟩
    · have hd' : d + 8 * Kt.c.n ≤ 64 + 8 * Kt.c.n * 17 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> exact sl_lt _ (by decide)
      rw [e₃ d (.inl hd') (by omega_using [hd', L, L1]), e₂ d (by omega_using [hd', L, L1])]
    · rcases Nat.lt_or_ge e 1 with h | h
      · obtain rfl : e = 0 := by omega_using [h]
        exact p₁.of_eq ((e₃ _ (.inr (by wa_dec)) (by wa_dec)).trans (O₂.wordsVal (by wa_dec) (by wa_dec)))
          ((e₃ _ (.inr (by wa_dec)) (by wa_dec)).trans (O₂.wordsVal (by wa_dec) (by wa_dec)))
          ((e₃ _ (.inr (by wa_dec)) (by wa_dec)).trans (O₂.wordsVal (by wa_dec) (by wa_dec)))
      · obtain rfl : e = 1 := by omega_using [he, h]
        rw [mul_one']
        exact p₂.of_eq (e₃ _ (.inr (by wa_dec)) (by wa_dec)) (e₃ _ (.inr (by wa_dec)) (by wa_dec))
          (e₃ _ (.inr (by wa_dec)) (by wa_dec))
    · rw [mul_one']
      exact (pQ.of_eq (e₂ _ (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo)) (e₂ _ (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo)) (e₂ _
          (Nat.le_trans (sl_lt _ (by decide)) Kt.l1_lo))).move x₃ y₃ z₃
  refine WP.mono (Kt.adds_ok hL hp.on 14 (Nat.le_refl _) hA) fun s₄ ⟨k₄, U₄, A₄⟩ => ?_
  refine ⟨((Kp.of_rest r₁).trans (Kp.of_rest r₂)).trans ((Kp.of_rest r₃).trans k₄), ?_, A₄.kc, A₄.tab, ?_⟩
  · refine (((O₁.unch.trans O₂.unch).trans U₃).trans U₄).cover fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (((hw | hw) | hw) | hw)
    · subst hw; exact ⟨(Kt.c.jt, 384 * Kt.c.n), by simp, by wa_dec, by wa_dec⟩
    · subst hw; exact ⟨(Kt.c.jt, 384 * Kt.c.n), by simp, by wa_dec, by wa_dec⟩
    · rcases hw with rfl | rfl | rfl <;> exact ⟨(64 + 8 * Kt.c.n * 17, 96 * Kt.c.n), by simp, by wa_dec, by wa_dec⟩
    · exact ⟨w, by simpa using hw, Nat.le_refl _, Nat.le_refl _⟩
  · intro d hd
    rw [U₄.wordsVal (by simp; omega_using [hd, L, L1]) (by omega_using [hd, L, L1]), e₃ d (.inl hd) (by omega_using [hd, L, L1]),
        e₂ d (by omega_using [hd, L, L1])]

/-! ## The nibble's entry -/

open VG.Proof.Ecdsa.RISCV64.Joint (scansJ_ok masks4_ok wordsVal_of_words wp_addAt) in
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs) in
/-- The window's entry `[k_j]Q` to `E`. -/
theorem select_ok (Kt : Kit) {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 16 * Kt.c.n)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) {Q : Point Kt.c.C} (hT : TabTo Kt.c base s Q 15) :
    WP isa (.block (Cfg.select Kt.c)) s fun s' =>
      PtOk Kt.c base s' (ePt Kt.c) (mul ((wordsVal s.mem base (Kt.c.sl K) Kt.c.n >>> (4 * j)) % 16) Q) ∧
      Outside base (64 + 8 * Kt.c.n * 58) (24 * Kt.c.n) s.mem s'.mem ∧ Rest selRegs s s' := by
  have L := Kt.bounds
  have hn := hw.nowrap
  rw [Cfg.select]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (nibble_ok Kt.c hw hj (sl_top L (by decide)) h1) fun s₁ ⟨v₁, r₁, m₁⟩ => ?_)
  generalize ha : (wordsVal s.mem base (Kt.c.sl K) Kt.c.n >>> (4 * j)) % 16 = a at v₁
  obtain ha16 : a < 16 := ha ▸ Nat.mod_lt _ (by decide)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono masks4_ok fun s₂ ⟨v₂, r₂, m₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine wp_addAt (by wa_dec) fun s₄ u₄ => ?_
  obtain r₄ : Rest [.a0] s₂ s₄ := u₄.rest (by decide)
  obtain hw₄ := hw₂.of_rest r₄
  obtain h0 : s₄.gpr .a0 = base + BitVec.ofNat 64 Kt.c.jt := by
    rw [u₄.gpr, r₂.gpr _ (by decide), r₁.gpr _ (by decide), hw.s0]
  obtain hm : ∀ b < 4, s₄.gpr (maskReg b) = maskOf (a.testBit b) := fun b hb => by
    rw [r₄.gpr _ (by
      have : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega_using [hb]
      rcases this with rfl | rfl | rfl | rfl <;> decide), v₂ b hb, v₁, BitVec.getLsbD_ofNat]
    simp [show b < 64 by omega_using [hb]]
  refine WP.mono (WP.rdwr (scansJ_ok Kt.c Kt.jt8 (by wa_dec) (by wa_dec) (by rw [Kt.slE]; wa_dec)
    (by rw [Kt.slE]; wa_dec) (3 * Kt.c.n)
    (Nat.le_refl _) hw₄ h0 hm)) fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_
  simp only [Kt.slE] at v₅ O₅
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, m₂, m₁]
  rw [m₄] at v₅ O₅
  rw [Nat.mod_eq_of_lt ha16] at v₅
  obtain he : PtOk Kt.c base s (ent Kt.c a) (mul a Q) := hT a (by omega_using [ha])
  obtain wv : ∀ b < 3, wordsVal s₅.mem base (64 + 8 * Kt.c.n * 58 + 8 * Kt.c.n * b) Kt.c.n = wordsVal s.mem base
      (Kt.c.jt + 24 * Kt.c.n * a + 8 * Kt.c.n * b) Kt.c.n :=
    fun b hb => wordsVal_of_words Kt.c.n fun q hq => by
      rw [show 64 + 8 * Kt.c.n * 58 + 8 * Kt.c.n * b + 8 * q = 64 + 8 * Kt.c.n * 58 + 8 * (Kt.c.n * b + q) by
          omega_using [Nat.mul_assoc 8 Kt.c.n b],
        v₅ _ (by omega_using [hb, hq, Nat.mul_le_mul_left Kt.c.n (Nat.le_of_lt_succ hb)])]
      congr 1; omega_using [Nat.mul_assoc 8 Kt.c.n b]
  refine ⟨he.move (by have := wv 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at this; exact this)
    (by
      have := wv 1 (by decide)
      rw [Nat.mul_one, show 64 + 8 * Kt.c.n * 58 + 8 * Kt.c.n = 64 + 8 * Kt.c.n * 59 by omega_using []] at this
      exact this)
    (by
      have := wv 2 (by decide)
      rw [show 64 + 8 * Kt.c.n * 58 + 8 * Kt.c.n * 2 = 64 + 8 * Kt.c.n * 60 by omega_using [],
        show 8 * Kt.c.n * 2 = 16 * Kt.c.n by omega_using []] at this
      exact this),
    O₅.mono (Nat.le_refl _) (by omega_using []), ?_⟩
  exact ((r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₄.mono (by decide)).trans
    ⟨fun r hr => k₅.1 r (fun h => hr ((by decide : ∀ r ∈ treeRegs, r ∈ selRegs) r h)),
      rd₅, wr₅, sp₅⟩)))

/-! ## The windows -/

/-- Slots apart from what a window writes. -/
theorem stepW_far (Kt : Kit) {base : Addr} {m m' : Mem} (U : Unch base (stepW Kt.c) m m') {d : Nat}
    (h1 : d + 8 * Kt.c.n ≤ (64 + 8 * Kt.c.n * 14) ∨ (64 + 8 * Kt.c.n * 29) ≤ d) (h2 : d + 8 * Kt.c.n ≤ (64 + 8 * Kt.c.n * 58) ∨
        (64 + 8 * Kt.c.n * 61) ≤ d) (h3 : d + 8 * Kt.c.n ≤ own Kt.c.n ∨ (own Kt.c.n + 64 * Kt.c.n) ≤ d
            ∧ d + 8 * Kt.c.n ≤ 8192) :
    wordsVal m' base d Kt.c.n = wordsVal m base d Kt.c.n := by
  have L := Kt.bounds
  exact U.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [h1, h2, h3])
      (by omega_using [h3, L])

/-- A window. -/
theorem step_ok (Kt : Kit) (hL : Law Kt.c.C) {base : Addr} {s₀ : State} {Q : Point Kt.c.C} {k : Nat} (hP : WFix Kt.c base s₀ Q k)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 16 * Kt.c.n) {s : State} (hI : WInv Kt.c base s₀ s Q k j) :
    WP isa (Cfg.step Kt.c Kt.dbl) s fun s' => WInv Kt.c base s₀ s' Q k (j - 1) := by
  have L := Kt.bounds
  have T := Kt.tab_own
  have hn := hI.ws.nowrap
  obtain hT : TabTo Kt.c base s Q 15 := hP.tab.of_eq (fun d h1 h2 => Kt.stepW_far hI.unch (.inr (by omega_using [h1, L, T]))
    (.inr (by omega_using [h1, L, T])) (by omega_using [h1, h2, L, T])) (by decide)
  rw [Cfg.step, Kt.ePt_eq]
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  obtain hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (Kt.select_ok hw₁ (j := j - 1) (by omega_using [hj, L, T]) u₁.gpr
    (hT.of_eq (fun d _ _ => by rw [u₁.mem]) (by decide))) fun s₂ ⟨pE, O₂, r₂⟩ => ?_
  rw [u₁.mem, Kt.stepW_far hI.unch (d := Kt.c.sl K) (.inr (by wa_dec)) (.inl (sl_lt _ (by decide))) (sl_own L (by decide)), hP.kk] at pE
  rw [u₁.mem] at O₂
  obtain hw₂ := hw₁.of_rest r₂
  obtain e₂ : ∀ d, (d + 8 * Kt.c.n ≤ (64 + 8 * Kt.c.n * 14) ∨ (64 + 8 * Kt.c.n * 29) ≤ d) → (d + 8 * Kt.c.n ≤
      (64 + 8 * Kt.c.n * 58) ∨ (64 + 8 * Kt.c.n * 61) ≤ d) → (d + 8 * Kt.c.n ≤ own Kt.c.n ∨ (own Kt.c.n + 64 * Kt.c.n) ≤ d
          ∧ d + 8 * Kt.c.n ≤ 8192) →
      wordsVal s₂.mem base d Kt.c.n = wordsVal s₀.mem base d Kt.c.n := fun d h1 h2 h3 => by
    rw [O₂.wordsVal (by omega_using [h2]) (by omega_using [h3, L, T]), Kt.stepW_far hI.unch h1 h2 h3]
  obtain pR₂ : PtOk Kt.c base s₂ (Kt.c.pt RX RY RZ) (wpt Q k j) :=
    hI.rep.of_eq (O₂.wordsVal (by wa_dec) (sl_fit L (by decide))) (O₂.wordsVal (by wa_dec) (sl_fit L (by decide)))
      (O₂.wordsVal (by wa_dec) (sl_fit L (by decide)))
  obtain hK₂ : KC Kt.c base s₂ := hP.kc.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact e₂ _ (sl_out _ (by decide)) (sl_out _ (by decide)) (sl_own L (by decide))
  obtain hX := hL.onCurve_mul hP.q (k >>> (4 * j))
  obtain h2 := hL.onCurve_add hX hX
  obtain h4 := hL.onCurve_add h2 h2
  obtain h8 := hL.onCurve_add h4 h4
  obtain h16 := hL.onCurve_add h8 h8
  obtain hE := hL.onCurve_mul hP.q ((k >>> (4 * (j - 1))) % 16)
  -- `R = 16 R`.
  refine WP.seq (WP.mono (Kt.quad_ok hL hw₂ hK₂ hX pR₂) fun s₃ ⟨K₃, U₃, pR₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp K₃
  obtain k₃ : ∀ d, (d + 8 * Kt.c.n ≤ (64 + 8 * Kt.c.n * 14) ∨ (64 + 8 * Kt.c.n * 29) ≤ d) → (d + 8 * Kt.c.n ≤ own Kt.c.n ∨
      (own Kt.c.n + 64 * Kt.c.n) ≤ d ∧ d + 8 * Kt.c.n ≤ 8192) → wordsVal s₃.mem base d Kt.c.n = wordsVal s₂.mem base d Kt.c.n :=
    fun d h1 h2 => U₃.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [h1, h2])
      (by omega_using [h2, L, T])
  obtain pE₃ := pE.of_eq (k₃ _ (sl_out _ (by decide)) (sl_own L (by decide))) (k₃ _ (sl_out _ (by decide)) (sl_own L (by decide)))
      (k₃ _ (sl_out _ (by decide)) (sl_own L (by decide)))
  obtain hK₃ : KC Kt.c base s₃ := hK₂.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (sl_out _ (by decide)) (sl_own L (by decide))
  -- `T = R + E`.
  refine WP.seq (WP.mono (Kt.addPt_ok hL hw₃ hK₃.ap hK₃.bp (p := Kt.c.pt RX RY RZ) (q := ePt Kt.c)
    (o := Kt.c.pt TX TY TZ) (apart_rcb Kt.n1 (by decide) (by decide)) Kt.jSl_step h16 hE pR₃ pE₃) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  obtain hw₄ := hw₃.of_kp K₄
  -- `R = T`.
  refine WP.mono (Kt.copyPt_ok hw₄ (o := Kt.c.pt RX RY RZ) (p := Kt.c.pt TX TY TZ) (by wa_dec) (sl_lt _ (by decide))
    (sl_lt _ (by decide)) (by wa_dec)) fun s₅ ⟨x₅, y₅, z₅, r₅, U₅⟩ => ?_
  refine ⟨hw₄.of_rest r₅, ?_, ?_, ?_, ?_⟩
  · rw [r₅.gpr _ (by decide), K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans (Kc.of_rest r₂)).trans
      (K₃.kc.trans (K₄.kc.trans (Kc.of_rest r₅)))
  · exact ((((hI.unch.trans (show Unch base [(64 + 8 * Kt.c.n * 58,
      24 * Kt.c.n)] s.mem s₂.mem from O₂.unch)).trans U₃).trans U₄).trans
      U₅).cover (by wa_dec)
  · have e := wstep hL hP.q k (j - 1)
    rw [show j - 1 + 1 = j by omega_using [hj1]] at e
    rw [← e]
    exact pT.move x₅ y₅ z₅

/-! ## The body -/

/-- `R = [k]Q`, for `k` at `K`'s slot and `Q` affine in `R`'s first two. -/
theorem body_ok (Kt : Kit) (hL : Law Kt.c.C) {base : Addr} {s : State} (hp : WPre Kt.c base s) :
    WP isa (Cfg.body Kt.c Kt.dbl) s fun s' => Kc s s' ∧ Unch base (bodyW Kt.c) s.mem s'.mem ∧
      PtOk Kt.c base s' (Kt.c.pt RX RY RZ) (mul (wordsVal s.mem base (Kt.c.sl K) Kt.c.n) (qOf Kt.c base s)) := by
  have L := Kt.bounds
  have hn := hp.ws.nowrap
  obtain hp0 : 0 < Kt.c.C.p := Kt.p0
  rw [Cfg.body]
  refine WP.seq (WP.mono (Kt.build_ok hL hp) fun s₁ ⟨K₁, U₁, hK₁, T₁, e₁⟩ => ?_)
  obtain hw₁ := hp.ws.of_kp K₁
  refine WP.seq (WP.block_append (WP.mono (Kt.copyPt_ok hw₁ (o := Kt.c.pt RX RY RZ) (p := Kt.c.pt ZERO ONEP ZERO)
    (by wa_dec) (sl_lt _ (by decide)) (sl_lt _ (by decide)) (by wa_dec)) fun s₂ ⟨x₂, y₂, z₂, r₂, U₂⟩ => ?_))
  obtain hw₂ := hw₁.of_rest r₂
  refine wp_li (imm := 16 * Kt.c.n) (by wa_dec) fun s₃ u₃ => WP.block_nil ?_
  obtain hw₃ : WsReg s₃ base := hw₂.of_kc (Kc.of_rest (u₃.rest (ws := [.s1]) (by decide)))
  obtain U₃ : Unch base [(64 + 8 * Kt.c.n * 14, 24 * Kt.c.n)] s₁.mem s₃.mem := by rw [u₃.mem]; exact U₂.cover (by wa_dec)
  obtain k₃ : ∀ d, d + 8 * Kt.c.n ≤ 64 + 8 * Kt.c.n * 14 ∨ 64 + 8 * Kt.c.n * 17 ≤ d → d + 8 * Kt.c.n ≤ 8192
      → wordsVal s₃.mem base d Kt.c.n = wordsVal s₁.mem base d Kt.c.n :=
    fun d h h' => U₃.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_using [h])
      (by omega_using [h'])
  obtain hP : WFix Kt.c base s₃ (qOf Kt.c base s) (wordsVal s.mem base (Kt.c.sl K) Kt.c.n) :=
    ⟨hK₁.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (sl_out _ (by decide)) (sl_ws L (by decide)),
     T₁.of_eq (fun d h1 h2 => k₃ d (by omega_using [h1, L]) (by omega_using [h2, L])) (by decide),
     by rw [k₃ _ (sl_out _ (by decide)) (sl_ws L (by decide)), U₁.wordsVal (by wa_dec) (sl_fit L (by decide))], hp.on⟩
  have zv : wordsVal s₁.mem base (Kt.c.sl ZERO) Kt.c.n = 0 := hK₁.zero
  have ov : wordsVal s₁.mem base (Kt.c.sl ONEP) Kt.c.n = 2 ^ (64 * Kt.c.n) % Kt.c.C.p := hK₁.onep
  obtain rx : wordsVal s₃.mem base (Kt.c.sl RX) Kt.c.n = 0 := by rw [u₃.mem]; exact x₂.trans zv
  obtain ry : wordsVal s₃.mem base (Kt.c.sl RY) Kt.c.n = 1 * 2 ^ (64 * Kt.c.n) % Kt.c.C.p := by
    rw [u₃.mem, Nat.one_mul]; exact y₂.trans ov
  obtain rz : wordsVal s₃.mem base (Kt.c.sl RZ) Kt.c.n = 0 := by rw [u₃.mem]; exact z₂.trans zv
  obtain hk : wordsVal s.mem base (Kt.c.sl K) Kt.c.n < 2 ^ (64 * Kt.c.n) := wordsVal_lt _ _ _ _
  obtain hI : WInv Kt.c base s₃ s₃ (qOf Kt.c base s) (wordsVal s.mem base (Kt.c.sl K) Kt.c.n) (16 * Kt.c.n) := by
    refine ⟨hw₃, u₃.gpr, ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [wpt_top _ hk]
      show Rep Kt.c.C (tmv Kt.c.C Kt.c.n base s₃ (Kt.c.sl RX)) (tmv Kt.c.C Kt.c.n base s₃ (Kt.c.sl RY)) (tmv Kt.c.C Kt.c.n base s₃
          (Kt.c.sl RZ)) _
      simp only [tmv]
      rw [rx, ry, rz, toM_zero, Nat.one_mul, toM_one Kt.unit]
      exact rep_infinity' hL
    · show wordsVal _ _ (Kt.c.sl RX) Kt.c.n < _; rw [rx]; exact hp0
    · show wordsVal _ _ (Kt.c.sl RY) Kt.c.n < _; rw [ry]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (Kt.c.sl RZ) Kt.c.n < _; rw [rz]; exact hp0
  refine countLoop_ok (Inv := fun j s' => WInv Kt.c base s₃ s' (qOf Kt.c base s) (wordsVal s.mem base (Kt.c.sl K) Kt.c.n) j)
    (n := 16 * Kt.c.n) (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => Kt.step_ok hL hP h1 h2 hi) (fun s' hi => ?_)
    (by wa_dec) (by wa_dec) hI
  refine ⟨(K₁.kc.trans (Kc.of_rest ((r₂.mono (by decide)).trans (u₃.rest (ws := [.t0, .s1]) (by decide))))).trans
    hi.keep, ((U₁.trans U₃).trans hi.unch).cover (by wa_dec), ?_⟩
  rw [← wpt_zero]
  exact hi.rep
end Kit

end VG.Proof.Ecdsa.RISCV64.WindowAll
