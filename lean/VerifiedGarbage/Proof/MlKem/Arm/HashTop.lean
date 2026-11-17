module

public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Impl.MlKem.Arm.Top
import VerifiedGarbage.Proof.MlKem.Arm.Prims
import VerifiedGarbage.Proof.MlKem.Arm.Sample
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.Arm.Keccak
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.MlKem.Arm.Reduce

/-! ### `MlKem.Arm.Lay`, which this module and modules that import it used -/

section

/-!
# ML-KEM on 32-bit ARM: the buffers of the top-level functions

The top-level functions work on a few buffers (`Lay`): `scratch` (buffer 0),
the 8 bytes below the stack pointer (buffer 1), and their arguments; the
contracts make them pairwise disjoint (`Lay.Ok`). A region is `l` bytes at
offset `o` of buffer `i` (`Lay.R`), and two regions are disjoint when a
computation on the offsets says so (`sepB`, decided by the kernel), so what a
call writes and what the proofs keep track of are lists of triples `(i, o,
l)`.

A state `s` in which the functions run their parts is `Ctx`: `r7` points to
`scratch`, and the stack pointer is the one of buffer 1. `Kept rs s s'`
(`Keccak.lean`) says what a part changes.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem

/-- Buffers: their pointers and sizes. -/
structure Lay where
  ptr : Nat → BitVec 32
  sizes : List Nat

/-- Whether the regions `a` and `b` (buffer, offset, length) are within
their buffers and apart. -/
def sepB (sz : List Nat) (a b : Nat × Nat × Nat) : Bool :=
  a.1 < sz.length && b.1 < sz.length && a.2.1 + a.2.2 ≤ sz.getD a.1 0 && b.2.1 + b.2.2 ≤ sz.getD b.1 0 &&
    (a.1 != b.1 || a.2.1 + a.2.2 ≤ b.2.1 || b.2.1 + b.2.2 ≤ a.2.1)

/-- `a` is apart from every region of `W`. -/
def sepAll (sz : List Nat) (a : Nat × Nat × Nat) (W : List (Nat × Nat × Nat)) : Bool := W.all (sepB sz a)

namespace Lay

variable (L : Lay)

abbrev size (i : Nat) : Nat := L.sizes.getD i 0

/-- `l` bytes at offset `o` of buffer `i`. -/
abbrev R (i o l : Nat) : Region := ⟨State.addr (L.ptr i) + BitVec.ofNat 64 o, l⟩

/-- The regions of the triples `W`. -/
abbrev RL (W : List (Nat × Nat × Nat)) : List Region := W.map fun w => L.R w.1 w.2.1 w.2.2

/-- The buffers fit in the address space and are pairwise disjoint. -/
structure Ok : Prop where
  fit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32
  disj : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i ≠ j →
    (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩

variable {L}

theorem R_sub {i o l : Nat} (h : o + l ≤ L.size i) :
    Region.Sub (L.R i o l) ⟨State.addr (L.ptr i), L.size i⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  bv_omega

theorem disj (hL : L.Ok) {i o l j o' l' : Nat} (h : sepB L.sizes (i, o, l) (j, o', l') = true) :
    (L.R i o l).Disjoint (L.R j o' l') := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hla⟩, hlb⟩, hs⟩ := h
  by_cases e : i = j
  · subst e
    have hf : (L.ptr i).toNat + L.sizes.getD i 0 ≤ 2 ^ 32 := hL.fit i ha
    have hs' : o + l ≤ o' ∨ o' + l' ≤ o := by
      rcases hs with (hs | hs) | hs
      · exact absurd rfl hs
      · exact .inl hs
      · exact .inr hs
    exact region_disj_off hs' hla hlb (addr_fit _ (by omega_using [hf]))
  · exact ((hL.disj _ ha _ hb e).sub_left (R_sub hla)).sub_right (R_sub hlb)

theorem disjAll (hL : L.Ok) {i o l : Nat} {W : List (Nat × Nat × Nat)} (h : sepAll L.sizes (i, o, l) W = true) :
    ∀ r ∈ L.RL W, (L.R i o l).Disjoint r := by
  intro r hr
  obtain ⟨⟨j, o', l'⟩, hw, rfl⟩ := List.mem_map.mp hr
  exact disj hL (List.all_eq_true.mp h _ hw)

/-- The address of a pointer into a buffer. -/
theorem addr_off (hL : L.Ok) {i o : Nat} (hi : i < L.sizes.length) (ho : o < L.size i) :
    State.addr (L.ptr i + BitVec.ofNat 32 o) = State.addr (L.ptr i) + BitVec.ofNat 64 o :=
  addr_add (by have := hL.fit i hi; omega_using [ho, this])

theorem regA_off (hL : L.Ok) {i o l : Nat} (hi : i < L.sizes.length) (ho : o < L.size i) :
    regA (L.ptr i + BitVec.ofNat 32 o) l = L.R i o l := by
  simp only [regA, addr_off hL hi ho]

theorem regA_zero (i l : Nat) : regA (L.ptr i) l = L.R i 0 l := by
  simp only [regA, Lay.R, add_ofNat_zero]

theorem fit_off (hL : L.Ok) {i o l : Nat} (hi : i < L.sizes.length) (h : o + l ≤ L.size i) (hl : 0 < l) :
    (L.ptr i + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 := by
  have := hL.fit i hi
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [h, hl, this]),
    Nat.mod_eq_of_lt (by omega_using [h, hl, this])]
  omega_using [h, this]

/-- A part of a buffer the state may access. -/
theorem covers {i o l : Nat} {ws : List Region} (hin : ⟨State.addr (L.ptr i), L.size i⟩ ∈ ws)
    (h : o + l ≤ L.size i) : Covers [L.R i o l] ws := by
  intro x n ⟨q, hq, hc⟩
  rw [List.mem_singleton] at hq; subst hq
  refine ⟨_, hin, ?_⟩
  simp only [Region.Contains] at hc ⊢
  bv_omega

theorem polyIs_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o : Nat} (h : sepAll L.sizes (i, o, 1024) W = true) {f : Poly}
    (hp : PolyIs m (State.addr (L.ptr i) + BitVec.ofNat 64 o) f) :
    PolyIs m' (State.addr (L.ptr i) + BitVec.ofNat 64 o) f :=
  polyIs_frame hf (disjAll hL h) hp

theorem bytes_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hl : l ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' (State.addr (L.ptr i) + BitVec.ofNat 64 o) l =
      Spec.Sha3.bytesAt m (State.addr (L.ptr i) + BitVec.ofNat 64 o) l :=
  bytesAt_frame hf (disjAll hL h) hl

/-- `Ok` from the disjointness of the buffers `i < j`. -/
theorem ok_of (hfit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32)
    (hd : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i < j →
      (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩) : L.Ok := by
  refine ⟨hfit, fun i hi j hj hij => ?_⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hd i hi j hj h
  · exact (hd j hj i hi h).symm

end Lay

/-! ## What changes -/

theorem Kept.refl (rs : List Region) (s : State) : Kept rs s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.mono {rs rs' : List Region} {s s' : State} (h : Kept rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.mono hs⟩

/-- The same, for regions given by triples. -/
theorem Kept.monoL {L : Lay} {W W' : List (Nat × Nat × Nat)} {s s' : State} (h : Kept (L.RL W) s s')
    (hs : ∀ w ∈ W, w ∈ W') : Kept (L.RL W') s s' :=
  h.mono fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨w, hs w hw, rfl⟩

/-- A state that differs only in registers other than the callee-saved ones. -/
structure Only (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.kept {s s' : State} (h : Only s s') (rs : List Region) : Kept rs s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩

theorem Only.of_gpr {s : State} (g : Reg → BitVec 32) (h : ∀ r ∈ preserved, r ≠ .lr → g r = s.gpr r) :
    Only s { s with gpr := g } :=
  ⟨h, rfl, rfl, rfl, rfl⟩

/-! ## The setting of the parts -/

/-- `s` runs a part of a top-level function: `scratch` (buffer 0, writable,
of which the parts use the first 32768 bytes) in `r7`, and the 8 bytes
below the stack pointer (buffer 1). -/
structure Ctx (L : Lay) (s : State) : Prop where
  ok : L.Ok
  sz0 : 32768 ≤ L.size 0
  sz1 : L.size 1 = 8
  len : 2 ≤ L.sizes.length
  r7 : s.gpr .r7 = L.ptr 0
  sp8 : 8 ≤ s.sp.toNat
  sp : L.ptr 1 = s.sp - BitVec.ofNat 32 8
  cw : (⟨State.addr (L.ptr 0), L.size 0⟩ : Region) ∈ s.wr

theorem Ctx.bel {L : Lay} {s : State} (h : Ctx L s) : below s 8 = L.R 1 0 8 := by
  simp only [Lay.R, h.sp, addr_sub h.sp8, add_ofNat_zero]

theorem Ctx.kept {L : Lay} {s s' : State} (h : Ctx L s) {rs : List Region} (hk : Kept rs s s') : Ctx L s' :=
  ⟨h.ok, h.sz0, h.sz1, h.len, by rw [hk.cs .r7 (by decide) (by decide), h.r7], by rw [hk.sp]; exact h.sp8,
    by rw [hk.sp]; exact h.sp, by rw [hk.wr]; exact h.cw⟩

theorem Ctx.only {L : Lay} {s s' : State} (h : Ctx L s) (hk : Only s s') : Ctx L s' := h.kept (hk.kept [])

/-- A part of `scratch` the state may write. -/
theorem Ctx.cs {L : Lay} {s : State} (h : Ctx L s) {o l : Nat} (hl : o + l ≤ 32768) :
    Covers [L.R 0 o l] s.wr := Lay.covers h.cw (Nat.le_trans hl h.sz0)

theorem Ctx.addr {L : Lay} {s : State} (h : Ctx L s) {o : Nat} (ho : o < 32768) :
    State.addr (L.ptr 0 + BitVec.ofNat 32 o) = State.addr (L.ptr 0) + BitVec.ofNat 64 o :=
  Lay.addr_off h.ok (by have := h.len; omega_using [this]) (Nat.lt_of_lt_of_le ho h.sz0)

theorem Ctx.regAo {L : Lay} {s : State} (h : Ctx L s) {o : Nat} (ho : o < 32768) (l : Nat) :
    regA (L.ptr 0 + BitVec.ofNat 32 o) l = L.R 0 o l :=
  Lay.regA_off h.ok (by have := h.len; omega_using [this]) (Nat.lt_of_lt_of_le ho h.sz0)

theorem Ctx.fit {L : Lay} {s : State} (h : Ctx L s) : (L.ptr 0).toNat + 32768 ≤ 2 ^ 32 := by
  have := h.ok.fit 0 (by have := h.len; omega_using [this]); have := h.sz0; omega_arith

theorem Ctx.fitO {L : Lay} {s : State} (h : Ctx L s) {o l : Nat} (hl : o + l ≤ 32768) (hl0 : 0 < l) :
    (L.ptr 0 + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 :=
  Lay.fit_off h.ok (by have := h.len; omega_using [this]) (Nat.le_trans hl h.sz0) hl0

end VG.Proof.MlKem.Arm

end

end

/-!
# ML-KEM-768 on 32-bit ARM: the hash routine

`hash` (`Impl/MlKem/Arm/Top.lean`) computes the sponge of the concatenation of
its input pieces, and writes consecutive output to its output pieces
(`hash_ok`): from the all-zero state (`repr_nil`), each `absorb` continues the
message from the position the previous one returned, the padding, and each
`squeeze` continues the output. It changes only the Keccak state and working
space, the outputs, the 8 bytes below the stack pointer, and registers that
are not callee-saved (or `lr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.Sha3 (Repr stateAt bytesAt absorb pad squeezeFrom rates)

theorem pres_ne {r : Reg} (h : r ∈ preserved) (hl : r ≠ .lr) :
    r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  revert r; decide

theorem enc200 : encodable (BitVec.ofNat 32 200) = true := by decide
theorem enc0 : encodable (BitVec.ofNat 32 0) = true := by decide

/-- The arguments of an `absorb` or a `squeeze`. -/
theorem kargs_ok {s : State} {rate : Nat} (first : Bool) {p : Piece} (hb : p.base ∈ preserved ∧ p.base ≠ .lr)
    (hre : encodable (BitVec.ofNat 32 rate) = true) (hoe : encodable (BitVec.ofNat 32 p.off) = true)
    (hle : encodable (BitVec.ofNat 32 p.len) = true) :
    WP isa (.block (keccakArgs rate first ++ pieceArgs p)) s fun s' => Only s s' ∧
      s'.gpr .r0 = s.gpr .r7 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧
      s'.gpr .r2 = (if first then BitVec.ofNat 32 0 else s.gpr .r0) ∧
      s'.gpr .r3 = s.gpr p.base + BitVec.ofNat 32 p.off ∧ s'.gpr .r12 = BitVec.ofNat 32 p.len ∧
      s'.gpr .lr = s.gpr .r7 + BitVec.ofNat 32 200 := by
  obtain ⟨n0, n1, n2, n3, n12⟩ := pres_ne hb.1 hb.2
  have nl := hb.2
  cases first <;>
  · run_block [keccakArgs, pieceArgs, ptrTo, hre, hoe, hle, enc200, enc0, n0, n1, n2, n3, n12, nl]
    refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
    obtain ⟨m0, m1, m2, m3, m12⟩ := pres_ne hr hl
    simp only [m0, m1, m2, m3, m12, hl, ite_false]

/-- The arguments of a `pad`. -/
theorem pargs_ok {s : State} {rate sfx : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hse : encodable (BitVec.ofNat 32 sfx) = true) :
    WP isa (.block (keccakArgs rate false ++ ([.mov .r3 (.imm (BitVec.ofNat 32 sfx))] : List Instr))) s
      fun s' => Only s s' ∧ s'.gpr .r0 = s.gpr .r7 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧
        s'.gpr .r2 = s.gpr .r0 ∧ s'.gpr .r3 = BitVec.ofNat 32 sfx ∧ s'.gpr .lr = s.gpr .r7 + BitVec.ofNat 32 200 := by
  run_block [keccakArgs, ptrTo, hre, hse, enc200]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, m12⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, hl, ite_false]

/-! ## Regions in `scratch` and below the stack pointer -/

theorem Ctx.sep00 {L : Lay} {s : State} (hc : Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 32768) (h : o + l ≤ o' ∨ o' + l' ≤ o) : sepB L.sizes (0, o, l) (0, o', l') = true := by
  have := hc.len; have := hc.sz0
  simp only [sepB, Lay.size] at this ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_true_eq_false,
    false_or]
  omega_arith

theorem Ctx.sep01 {L : Lay} {s : State} (hc : Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 8) : sepB L.sizes (0, o, l) (1, o', l') = true := by
  have h0 := hc.len; have h1 := hc.sz0; have h2 := hc.sz1
  simp only [Lay.size] at h1 h2
  simp only [sepB, h2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  omega_using [h₁, h₂, h0, h1]

theorem sepB_symm {sz : List Nat} {a b : Nat × Nat × Nat} (h : sepB sz a b = true) : sepB sz b a = true := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h ⊢
  omega_using [h]

/-- The regions of the sponge functions: the state, the working space and the stack arguments. -/
abbrev kRegs : List (Nat × Nat × Nat) := [(0, 0, 200), (0, 200, 640), (1, 0, 8)]

theorem Ctx.kregs {L : Lay} {s : State} (hc : Ctx L s) :
    regA (L.ptr 0) 200 = L.R 0 0 200 ∧ regA (L.ptr 0 + BitVec.ofNat 32 200) 640 = L.R 0 200 640 ∧
      below s 8 = L.R 1 0 8 :=
  ⟨Lay.regA_zero _ _, hc.regAo (by decide) _, hc.bel⟩

/-! ## Pieces -/

/-- Piece `p` is the region `L.R (idx p.base) p.off p.len`, which the state
may read (or write, if `w`), apart from the sponge's regions. -/
structure PieceOk (L : Lay) (idx : Reg → Nat) (s : State) (w : Bool) (p : Piece) : Prop where
  base : p.base ∈ preserved ∧ p.base ≠ .lr
  ptr : s.gpr p.base = L.ptr (idx p.base)
  oenc : encodable (BitVec.ofNat 32 p.off) = true
  lenc : encodable (BitVec.ofNat 32 p.len) = true
  pos : 0 < p.len
  lt : p.off + p.len < 2 ^ 32
  sep : sepAll L.sizes (idx p.base, p.off, p.len) kRegs = true
  cov : (⟨State.addr (L.ptr (idx p.base)), L.size (idx p.base)⟩ : Region) ∈ (if w then s.wr else s.rd ++ s.wr)

/-- The region of a piece. -/
abbrev Lay.P (L : Lay) (idx : Reg → Nat) (p : Piece) : Region := L.R (idx p.base) p.off p.len

/-- The bytes of a piece. -/
abbrev Lay.pb (L : Lay) (idx : Reg → Nat) (m : Mem) (p : Piece) : List Byte :=
  bytesAt m (State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off) p.len

theorem sepAll_head {sz : List Nat} {a w : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : sepAll sz a (w :: W) = true) : sepB sz a w = true := by
  simp only [sepAll, List.all_cons, Bool.and_eq_true] at h; exact h.1

theorem sepB_bounds {sz : List Nat} {i o l : Nat} {w : Nat × Nat × Nat} (h : sepB sz (i, o, l) w = true) :
    i < sz.length ∧ o + l ≤ sz.getD i 0 := by
  simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.2⟩

theorem PieceOk.bounds {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p) :
    idx p.base < L.sizes.length ∧ p.off + p.len ≤ L.size (idx p.base) :=
  sepB_bounds (sepAll_head h.sep)

theorem PieceOk.sepK {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p) :
    sepB L.sizes (idx p.base, p.off, p.len) (0, 0, 200) = true ∧
      sepB L.sizes (idx p.base, p.off, p.len) (0, 200, 640) = true ∧
      sepB L.sizes (idx p.base, p.off, p.len) (1, 0, 8) = true := by
  have := h.sep
  simp only [sepAll, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

theorem PieceOk.regA {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : PieceOk L idx s w p) : regA (L.ptr (idx p.base) + BitVec.ofNat 32 p.off) p.len = L.P idx p :=
  Lay.regA_off hL h.bounds.1 (by have := h.bounds.2; have := h.pos; omega_arith)

theorem RL_kRegs (L : Lay) : L.RL kRegs = [L.R 0 0 200, L.R 0 200 640, L.R 1 0 8] := rfl

/-- The position the next call starts from: 0 first, or the one the last
call returned. -/
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .r0).toNat

theorem pos_r2 (first : Bool) (s : State) :
    (if first then BitVec.ofNat 32 0 else s.gpr .r0) = BitVec.ofNat 32 (Pos first s) := by
  cases first
  · simp only [Pos, Bool.false_eq_true, ite_false, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rfl

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega_using [h]

/-- The registers and permissions of `s₀`. -/
structure Rg (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s.gpr r = s₀.gpr r

theorem Kept.rg {rs : List Region} {s₀ s : State} (h : Kept rs s₀ s) : Rg s₀ s := ⟨h.rd, h.wr, h.sp, h.cs⟩

theorem Rg.kept {rs : List Region} {s₀ s s' : State} (h : Rg s₀ s) (hk : Kept rs s s') : Rg s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun r hr hl => by rw [hk.cs r hr hl, h.cs r hr hl]⟩

theorem Rg.ctx {L : Lay} {s₀ s : State} (hc : Ctx L s₀) (h : Rg s₀ s) : Ctx L s :=
  ⟨hc.ok, hc.sz0, hc.sz1, hc.len, by rw [h.cs .r7 (by decide) (by decide), hc.r7], by rw [h.sp]; exact hc.sp8,
    by rw [h.sp]; exact hc.sp, by rw [h.wr]; exact hc.cw⟩

theorem PieceOk.covR {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (h : PieceOk L idx s₀ false p)
    (hg : Rg s₀ s) : Covers [L.P idx p] (s.rd ++ s.wr) := by
  have := h.cov
  simp only [Bool.false_eq_true, ite_false] at this
  rw [hg.rd, hg.wr]
  exact Lay.covers this h.bounds.2

theorem PieceOk.covW {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (h : PieceOk L idx s₀ true p)
    (hg : Rg s₀ s) : Covers [L.P idx p] s.wr := by
  have := h.cov
  simp only [ite_true] at this
  rw [hg.wr]
  exact Lay.covers this h.bounds.2

theorem PieceOk.fit {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : PieceOk L idx s w p) : (L.ptr (idx p.base) + BitVec.ofNat 32 p.off).toNat + p.len ≤ 2 ^ 32 :=
  Lay.fit_off hL h.bounds.1 h.bounds.2 h.pos

theorem PieceOk.len32 {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p)
    (_hL : L.Ok) : p.len < 2 ^ 32 := by
  have := h.lt; omega_using [this]

theorem PieceOk.addr {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : PieceOk L idx s w p) :
    State.addr (L.ptr (idx p.base) + BitVec.ofNat 32 p.off) = State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off :=
  Lay.addr_off hL h.bounds.1 (by have := h.bounds.2; have := h.pos; omega_arith)

theorem covers_kregs {L : Lay} {s : State} (hc : Ctx L s) :
    Covers [regA (L.ptr 0) 200, regA (L.ptr 0 + BitVec.ofNat 32 200) 640] s.wr := by
  rw [hc.kregs.1, hc.kregs.2.1]
  exact covers_cons' (hc.cs (by decide)) (covers_cons' (hc.cs (by decide)) covers_nil')

/-! ## The absorbs -/

theorem absorbs_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) {s₀ : State} (hc : Ctx L s₀) :
    ∀ (ps : List Piece) (first : Bool) (s : State) (msg : List Byte),
      (∀ p ∈ ps, PieceOk L idx s₀ false p) →
      Kept (L.RL kRegs) s₀ s → Repr s.mem (State.addr (L.ptr 0)) rate msg →
      Pos first s = msg.length % rate →
      WP isa (absorbs rate first ps) s fun s' =>
        Kept (L.RL kRegs) s₀ s' ∧
        Repr s'.mem (State.addr (L.ptr 0)) rate (msg ++ (ps.map (L.pb idx s₀.mem)).flatten) ∧
        Pos (first && ps.isEmpty) s' = (msg ++ (ps.map (L.pb idx s₀.mem)).flatten).length % rate := by
  intro ps
  induction ps with
  | nil => exact fun first s msg _ hk hr hpos => WP.block_nil ⟨hk, by simpa using hr, by simpa using hpos⟩
  | cons p ps ih =>
    intro first s msg hps hk hr hpos
    have hp := hps p (List.mem_cons_self ..)
    have hL := hc.ok
    have rpos := rate_pos hrate
    have hcs := hk.rg.ctx hc
    refine WP.seq (WP.mono (kargs_ok first hp.base hre hp.oenc hp.lenc) fun s₁ ⟨o₁, g0, g1, g2, g3, g12, glr⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hk.cs _ hp.base.1 hp.base.2, hp.ptr]
    rw [hcs.r7] at g0 glr
    rw [gb] at g3
    rw [pos_r2] at g2
    have hpos' : Pos first s < rate := by rw [hpos]; exact Nat.mod_lt _ rpos
    obtain ⟨e0, e1, e2⟩ := hc₁.kregs
    have er := hp.regA hL
    have hg₁ : Rg s₀ s₁ := hk.rg.kept (o₁.kept [])
    have hA : AbsorbArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
        rate (Pos first s) p.len := by
      refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos', hp.len32 hL, hc₁.sp8, fit_le (by decide) hc.fit,
        hp.fit hL, hc.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, covers_kregs hc₁, ?_⟩
      · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
      · rw [er, e0]; exact Lay.disj hL hp.sepK.1
      · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
      · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
      · rw [er]; exact hp.covR hg₁
    refine WP.seq (absorb_ok hA fun s₂ k₂ r₂ ret₂ => ?_)
    rw [e0, e1, e2, ← RL_kRegs] at k₂
    have hk₂ : Kept (L.RL kRegs) s₀ s₂ := hk.trans ((o₁.kept _).trans k₂)
    have eb : bytesAt s₁.mem (State.addr (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)) p.len = L.pb idx s₀.mem p := by
      rw [o₁.mem, hp.addr hL]
      exact Lay.bytes_keep hL hk.frame hp.sep (by have := hp.len32 hL; omega_using [this])
    have rep := r₂ msg (by rw [o₁.mem]; exact hr) hpos
    rw [eb] at rep
    refine WP.mono (ih false s₂ (msg ++ L.pb idx s₀.mem p) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hk₂ rep
      ?_) fun s' ⟨k', r', p'⟩ => ?_
    · show (s₂.gpr .r0).toNat = _
      rw [ret₂, hpos, List.length_append, bytesAt_length, Nat.mod_add_mod]
    · simp only [List.map_cons, List.flatten_cons, List.isEmpty_cons, Bool.and_false, ← List.append_assoc]
        at r' p' ⊢
      exact ⟨k', r', p'⟩

/-! ## The squeezes -/

/-- The triple of a piece. -/
abbrev trip (idx : Reg → Nat) (p : Piece) : Nat × Nat × Nat := (idx p.base, p.off, p.len)

/-- The output pieces hold consecutive output from the state `P`, from
position `c` on. -/
def Outs (L : Lay) (idx : Reg → Nat) (m : Mem) (rate : Nat) (P : Spec.Sha3.State) : Nat → List Piece → Prop
  | _, [] => True
  | c, p :: ps => L.pb idx m p = squeezeFrom rate P c p.len ∧ Outs L idx m rate P (c + p.len) ps

theorem sepAll_append {sz : List Nat} {a : Nat × Nat × Nat} {W W' : List (Nat × Nat × Nat)}
    (h : sepAll sz a W = true) (h' : sepAll sz a W' = true) : sepAll sz a (W ++ W') = true := by
  simp only [sepAll, List.all_append, Bool.and_eq_true] at h h' ⊢; exact ⟨h, h'⟩

theorem sepAll_map {α : Type} {sz : List Nat} {a : Nat × Nat × Nat} {ps : List α} {f : α → Nat × Nat × Nat}
    (h : ∀ q ∈ ps, sepB sz a (f q) = true) : sepAll sz a (ps.map f) = true := by
  simp only [sepAll, List.all_map, List.all_eq_true, Function.comp]; exact h

theorem squeezes_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) {s₀ : State} (hc : Ctx L s₀) {P : Spec.Sha3.State} :
    ∀ (ps : List Piece) (first : Bool) (s : State) (c : Nat),
      (∀ p ∈ ps, PieceOk L idx s₀ true p) → ps.Pairwise (fun p q => sepB L.sizes (trip idx p) (trip idx q) = true) →
      Rg s₀ s → Pos first s ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s.mem (State.addr (L.ptr 0))) (Pos first s) d = squeezeFrom rate P c d) →
      WP isa (squeezes rate first ps) s fun s' =>
        Kept (L.RL (kRegs ++ ps.map (trip idx))) s s' ∧ Outs L idx s'.mem rate P c ps := by
  intro ps
  induction ps with
  | nil => exact fun _ s _ _ _ _ _ _ => WP.block_nil ⟨Kept.refl _ _, trivial⟩
  | cons p ps ih =>
    intro first s c hps hpw hg hple hcont
    have hp := hps p (List.mem_cons_self ..)
    have hL := hc.ok
    have rpos := rate_pos hrate
    have rle := rates_lt hrate
    have hcs := hg.ctx hc
    refine WP.seq (WP.mono (kargs_ok first hp.base hre hp.oenc hp.lenc) fun s₁ ⟨o₁, g0, g1, g2, g3, g12, glr⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hg.cs _ hp.base.1 hp.base.2, hp.ptr]
    rw [hcs.r7] at g0 glr
    rw [gb] at g3
    rw [pos_r2] at g2
    obtain ⟨e0, e1, e2⟩ := hc₁.kregs
    have er := hp.regA hL
    have hg₁ : Rg s₀ s₁ := hg.kept (o₁.kept [])
    have hS : SqueezeArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
        rate (Pos first s) p.len := by
      refine ⟨g0, g1, g2, g3, g12, glr, hrate, hple, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc.fit,
        hp.fit hL, hc.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e0, er]; exact Lay.disj hL (sepB_symm hp.sepK.1)
      · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
      · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
      · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
      · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e0, er, e1]
        exact covers_cons' (hc₁.cs (by decide)) (covers_cons' (hp.covW hg₁)
          (covers_cons' (hc₁.cs (by decide)) covers_nil'))
    refine WP.seq (squeeze_ok hS fun s₂ k₂ b₂ r₂ n₂ => ?_)
    rw [e0, er, e1, e2] at k₂
    have out₂ : L.pb idx s₂.mem p = squeezeFrom rate P c p.len := by
      show bytesAt s₂.mem (State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off) p.len = _
      rw [← hp.addr hL, b₂, o₁.mem, hcont]
    have cont₂ : ∀ d, squeezeFrom rate (stateAt s₂.mem (State.addr (L.ptr 0))) (Pos false s₂) d =
        squeezeFrom rate P (c + p.len) d := fun d => by
      rw [show Pos false s₂ = (s₂.gpr .r0).toNat from rfl, n₂, o₁.mem]
      exact squeezeFrom_shift rpos (by omega_using [rle]) hcont p.len d
    have pw := List.pairwise_cons.mp hpw
    have hg₂ : Rg s₀ s₂ := hg₁.kept k₂
    refine WP.mono (ih false s₂ (c + p.len) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) pw.2 hg₂ r₂ cont₂)
      fun s' ⟨k', o'⟩ => ⟨?_, ?_, o'⟩
    · refine (o₁.kept _).trans ((k₂.mono fun r hr => ?_).trans (k'.monoL fun w hw => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [Lay.RL, List.map_append, List.map_cons, List.mem_append, List.mem_cons, List.mem_map]
        rcases hr with rfl | rfl | rfl | rfl <;> simp
      · simp only [List.mem_append, List.mem_map, List.map_cons, List.mem_cons] at hw ⊢
        rcases hw with hw | ⟨q, hq, rfl⟩
        · exact .inl hw
        · exact .inr (.inr ⟨q, hq, rfl⟩)
    · rw [← out₂]
      exact Lay.bytes_keep hL k'.frame (sepAll_append hp.sep (sepAll_map pw.1)) (by have := hp.len32 hL; omega_using [this])

/-! ## The whole hash -/

theorem zeroState_ok {L : Lay} {s : State} (hc : Ctx L s) :
    WP isa (.block (zeroState .r7)) s fun s' =>
      Kept (L.RL [(0, 0, 200)]) s s' ∧ stateAt s'.mem (State.addr (L.ptr 0)) = Spec.Sha3.zero := by
  rw [zeroState, ← List.singleton_append, WP.block_append_iff]
  have hmov : WP isa (.block [.mov .r12 (.imm 0)]) s fun s₁ => s₁.gpr = (s.setReg .r12 0).gpr ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    run_block []
  refine WP.mono hmov fun s₁ ⟨g, m, rd, wr, sp⟩ => ?_
  have e7 : s₁.gpr .r7 = L.ptr 0 := by rw [g]; simp [State.setReg, hc.r7]
  refine WP.mono (Sample.zeroWords_ok .r7 (s₁ := s₁) (by rw [g]; simp [State.setReg])
    (by rw [e7]; exact fit_le (by decide) hc.fit) fun k hk => by
      rw [e7, wr]
      exact hc.cs (o := 4 * k) (l := 4) (by omega_using [hk]) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    fun s₂ h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e7] at hf hz
  refine ⟨⟨fun r hr hl => ?_, by rw [h₂.sp, sp], by rw [h₂.rd, rd], by rw [h₂.wr, wr], ?_⟩,
    Sample.stateAt_zero hz⟩
  · rw [h₂.gpr, g]
    obtain ⟨-, -, -, -, n12⟩ := pres_ne hr hl
    simp [State.setReg, n12]
  · rw [← m]
    refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    rw [List.mem_singleton] at hr; subst hr
    show Region.Sub _ (L.R 0 0 200)
    rw [← Lay.regA_zero]; exact fun _ h => h

theorem sfx8 {sfx : Nat} (h : sfx < 256) : (BitVec.ofNat 32 sfx).setWidth 8 = BitVec.ofNat 8 sfx := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h] : sfx < 2 ^ 32)]

/-- `hash`: the sponge of the pieces `ins`, output into the pieces `outs`. -/
theorem hash_ok {L : Lay} {idx : Reg → Nat} {rate sfx : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) (hse : encodable (BitVec.ofNat 32 sfx) = true)
    (hsfx : sfx < 256) {s₀ : State} (hc : Ctx L s₀) {ins outs : List Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, PieceOk L idx s₀ false p) (hout : ∀ p ∈ outs, PieceOk L idx s₀ true p)
    (hpw : outs.Pairwise (fun p q => sepB L.sizes (trip idx p) (trip idx q) = true)) :
    WP isa (hash rate sfx ins outs) s₀ fun s' =>
      Kept (L.RL (kRegs ++ outs.map (trip idx))) s₀ s' ∧
      Outs L idx s'.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (L.pb idx s₀.mem)).flatten)) 0
        outs := by
  have hL := hc.ok
  have rpos := rate_pos hrate
  refine WP.seq (WP.mono (zeroState_ok hc) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (absorbs_ok hrate hre hc ins true s₁ [] hin (k₁.monoL (by simp)) (repr_nil z₁)
    (by simp [Pos])) fun s₂ ⟨k₂, r₂, p₂⟩ => ?_)
  have hie : ins.isEmpty = false := by cases ins; exact absurd rfl hne; rfl
  rw [hie, Bool.and_false] at p₂
  rw [List.nil_append] at r₂ p₂
  have hc₂ := k₂.rg.ctx hc
  refine WP.seq (WP.mono (pargs_ok hre hse) fun s₃ ⟨o₃, g0, g1, g2, g3, glr⟩ => ?_)
  have hc₃ := hc₂.only o₃
  rw [hc₂.r7] at g0 glr
  obtain ⟨e0, e1, e2⟩ := hc₃.kregs
  have hP : PadArgs s₃ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) rate (s₂.gpr .r0).toNat (BitVec.ofNat 32 sfx) := by
    refine ⟨g0, g1, by rw [g2, BitVec.ofNat_toNat, BitVec.setWidth_eq], g3, glr, hrate,
      by rw [show (s₂.gpr .r0).toNat = Pos false s₂ from rfl, p₂]; exact Nat.mod_lt _ rpos, hc₃.sp8,
      fit_le (by decide) hc.fit, hc.fitO (by decide) (by decide), ?_, ?_, ?_, covers_kregs hc₃⟩
    · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
    · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
    · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
  refine WP.seq (pad_ok hP fun s₄ k₄ st₄ => ?_)
  rw [e0, e1, e2, ← RL_kRegs] at k₄
  have st := st₄ _ (by rw [o₃.mem]; exact r₂) p₂
  rw [sfx8 hsfx] at st
  have hg₄ : Rg s₀ s₄ := (k₂.trans ((o₃.kept _).trans k₄)).rg
  refine WP.mono (squeezes_ok hrate hre hc outs true s₄ 0 hout hpw hg₄ (Nat.zero_le _)
    (fun d => by rw [st]; rfl)) fun s' ⟨k', o'⟩ => ⟨?_, o'⟩
  refine ((k₂.trans ((o₃.kept _).trans k₄)).monoL fun w hw => List.mem_append_left _ hw).trans k'

/-! ## The arguments of the sponge functions, for the constant-time proofs -/

theorem absorbArgs_of {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : Ctx L s₁) (hg : Rg s₀ s₁) (hp : PieceOk L idx s₀ false p) {pos : Nat} (hpos : pos < rate)
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = L.ptr (idx p.base) + BitVec.ofNat 32 p.off) (g12 : s₁.gpr .r12 = BitVec.ofNat 32 p.len)
    (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    AbsorbArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
      rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  have er := hp.regA hL
  refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hp.fit hL, hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, covers_kregs hc₁, ?_⟩
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [er, e0]; exact Lay.disj hL hp.sepK.1
  · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
  · rw [er]; exact hp.covR hg

theorem squeezeArgs_of {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : Ctx L s₁) (hg : Rg s₀ s₁) (hp : PieceOk L idx s₀ true p) {pos : Nat} (hpos : pos ≤ rate)
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = L.ptr (idx p.base) + BitVec.ofNat 32 p.off) (g12 : s₁.gpr .r12 = BitVec.ofNat 32 p.len)
    (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    SqueezeArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
      rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  have er := hp.regA hL
  refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hp.fit hL, hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, er]; exact Lay.disj hL (sepB_symm hp.sepK.1)
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
  · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e0, er, e1]
    exact covers_cons' (hc₁.cs (by decide)) (covers_cons' (hp.covW hg)
      (covers_cons' (hc₁.cs (by decide)) covers_nil'))

theorem padArgs_of {L : Lay} {rate : Nat} (hrate : rate ∈ rates) {s₁ : State} (hc₁ : Ctx L s₁) {pos : Nat}
    (hpos : pos < rate) {sfx : BitVec 32}
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = sfx) (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    PadArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) rate pos sfx := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  refine ⟨g0, g1, g2, g3, glr, hrate, hpos, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, covers_kregs hc₁⟩
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))

/-- The 64 bytes of `G(c)` squeezed at once: both of its outputs. -/
theorem G_split (c : List Byte) :
    Spec.Sha3.squeezeFrom 72 (VG.Proof.MlKem.padded 72 Spec.Sha3.sha3Suffix c) 0 64 =
      (Spec.MlKem.G c).1 ++ (Spec.MlKem.G c).2 := by
  simp only [Spec.MlKem.G, VG.Proof.MlKem.sha3_512_eq, List.take_append_drop]

end VG.Proof.MlKem.Arm
