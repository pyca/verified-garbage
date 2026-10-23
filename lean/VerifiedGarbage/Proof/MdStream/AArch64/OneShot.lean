module

public import VerifiedGarbage.Proof.MdStream.AArch64.Common
public import VerifiedGarbage.Impl.MdStream.AArch64.OneShot
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MdStream.AArch64.Tail16

/-!
# One-shot Merkle–Damgård digests on AArch64

The functional correctness of `OneShot.digest` (`Impl/MdStream/AArch64/OneShot.lean`),
for any hash function (`Md`), any correct compression function (`CalleeOk`),
any code `init` storing an initial hash value `iv` (writing only `x9` and
`x10`), and the hash function's
length field and digest code (`ShapeD`): it runs `init`, compresses the whole
blocks of the message, builds the last block or two in its frame (as
`Md.hash_one` and `Md.hash_two` describe them) and compresses them, and
writes the digest. Constant time is proven for each hash function's code by
the taint analysis, calls included.
-/

@[expose] public section

namespace VG.Proof.MdStream.AArch64.OneShot

open VG VG.AArch64 VG.Impl.MdStream.AArch64 VG.Impl.MdStream.AArch64.OneShot
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (bytesAt_congr writeBytes writeBytes_frame bytesAt_writeBytes getD_append_left
  getD_append_right)

/-! ## The precondition -/

section
variable (P : Params) (s : State)

abbrev dp : Addr := s.gpr .x0
abbrev len : Nat := (s.gpr .x1).toNat
abbrev out : Addr := s.gpr .x2
/-- The base of the frame. -/
abbrev fb : Addr := s.sp - BitVec.ofNat 64 (frameBytes P)
abbrev dR : Region := ⟨dp s, len s⟩
abbrev oR (D : Nat) : Region := ⟨out s, D⟩
abbrev fR : Region := ⟨fb P s, frameBytes P⟩
/-- The hash value and the block, laid out as a streaming state. -/
abbrev stR : Region := ⟨fb P s, P.N + P.B⟩
/-- The hash value. -/
abbrev hR : Region := ⟨fb P s, P.N⟩
/-- The block. -/
abbrev bR : Region := ⟨fb P s + BitVec.ofNat 64 P.N, P.B⟩
/-- The compression function's scratch space. -/
abbrev scR : Region := ⟨fb P s + BitVec.ofNat 64 (scO P), P.so⟩
/-- The saved registers. -/
abbrev slR : Region := ⟨fb P s + BitVec.ofNat 64 (slO P), 64⟩

end

/-- The message is readable, `out` writable, they do not overlap each other
or the frame, which fits below the stack pointer. -/
structure Pre (P : Params) (D : Nat) (s : State) : Prop where
  rd : s.rd = [dR s]
  wr : s.wr = [oR s D]
  d_o : (dR s).Disjoint (oR s D)
  sp : frameBytes P ≤ s.sp.toNat
  f_d : (fR P s).Disjoint (dR s)
  f_o : (fR P s).Disjoint (oR s D)

/-- The contract: the first `D` bytes of the digest, from `iv`, of the message. -/
def oneK {P : Params} (H : Md P.B P.N P.L) (iv : H.HV) (D : Nat) : Contract isa where
  pre := Pre P D
  post s s' := H.lenOk (len s) →
    bytesAt s'.mem (out s) D = (H.hash iv (bytesAt s.mem (dp s) (len s))).take D
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

/-- What the code storing the initial hash value does: on a state whose only
region is the streaming state at `x0`, it makes the state represent the empty
message. -/
def initK {P : Params} (H : Md P.B P.N P.L) (iv : H.HV) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, P.N + P.B⟩]
  post s s' := H.Repr iv s'.mem (s.gpr .x0) []
  pub _ _ := True

/-- The frame fits an immediate. -/
structure Fits (P : Params) : Prop where
  lt : frameBytes P < 4096

/-! ## The frame -/

section
variable {P : Params}

theorem st_le (P : Params) : P.N + P.B ≤ scO P := by simp only [scO]; omega

theorem sc_le (P : Params) : scO P + P.so ≤ slO P := by simp [slO]

theorem sl_le (P : Params) : slO P + 64 ≤ frameBytes P := by simp only [frameBytes]; omega

theorem Fits.so (hF : Fits P) : P.N + P.B + P.so + 64 < 4096 := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; omega

variable (hF : Fits P) (s : State)
include hF

theorem h_b : (hR P s).Disjoint (bR P s) :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hF.so; omega)

theorem h_sc : (hR P s).Disjoint (scR P s) :=
  Offset.base_disjoint _ (by have := st_le P; omega) (by have := hF.so; have := sc_le P; have := sl_le P; have := hF.lt; omega)

theorem b_sc : (bR P s).Disjoint (scR P s) :=
  Offset.disjoint _ (.inl (st_le P)) (by have := hF.so; omega)
    (by have := hF.lt; have := sl_le P; have := sc_le P; omega)

theorem st_sl : (stR P s).Disjoint (slR P s) :=
  Offset.base_disjoint _ (by have := sc_le P; have := st_le P; omega)
    (by have := hF.lt; have := sl_le P; omega)

theorem sc_sl : (scR P s).Disjoint (slR P s) :=
  Offset.disjoint _ (.inl (sc_le P)) (by have := hF.lt; have := sl_le P; have := sc_le P; omega)
    (by have := hF.lt; have := sl_le P; omega)

end

section
variable {P : Params} (s : State)

theorem st_sub : Region.Sub (stR P s) (fR P s) :=
  Region.sub_prefix (by have := sc_le P; have := st_le P; have := sl_le P; omega)

theorem h_sub : Region.Sub (hR P s) (fR P s) :=
  Region.sub_prefix (by have := sc_le P; have := st_le P; have := sl_le P; omega)

theorem b_sub : Region.Sub (bR P s) (fR P s) :=
  Offset.sub_base _ (by have := sc_le P; have := st_le P; have := sl_le P; omega)

theorem sc_sub : Region.Sub (scR P s) (fR P s) :=
  Offset.sub_base _ (by have := sc_le P; have := sl_le P; omega)

theorem sl_sub : Region.Sub (slR P s) (fR P s) :=
  Offset.sub_base _ (sl_le P)

end

/-! ## One instruction at a time -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addSp {d : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.sp + BitVec.ofNat 64 imm)) (by simp [exec, h]) (k _ (Upd.write64 _ _ _))

theorem wp_stp {t1 t2 n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off ≤ 504)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (h₁ : InRegions s.wr a 8) (h₂ : InRegions s.wr (a + 8) 8)
    (k : ∀ s', Mupd s s' ((s.mem.writeW a (s.gpr t1)).writeW (a + 8) (s.gpr t2)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.stp t1 t2 n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := (s.mem.writeW a (s.gpr t1)).writeW (a + 8) (s.gpr t2) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, ho, and_self, ite_true, ha, State.store, h₁, h₂, Option.bind_some, Mem.writeW,
    State.read]
  try rfl

/-- `s'` is `s` with registers `d₁` and `d₂` (distinct) set to `v₁` and `v₂`. -/
structure Upd2 (s s' : State) (d₁ d₂ : Reg) (v₁ v₂ : BitVec 64) : Prop where
  gpr₁ : s'.gpr d₁ = v₁
  gpr₂ : s'.gpr d₂ = v₂
  other : ∀ r, r ≠ d₁ → r ≠ d₂ → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem wp_ldp {t1 t2 n : Reg} {off : Nat} {a : Addr} (ht : t1 ≠ t2) (ho : off % 8 = 0 ∧ off ≤ 504)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (h₁ : InRegions (s.rd ++ s.wr) a 8)
    (h₂ : InRegions (s.rd ++ s.wr) (a + 8) 8)
    (k : ∀ s', Upd2 s s' t1 t2 (s.mem.readW a 64) (s.mem.readW (a + 8) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldp t1 t2 n off :: is)) s Q := by
  refine WP.cons (s' := (s.write .x t1 (s.mem.readW a 64)).write .x t2 (s.mem.readW (a + 8) 64)) ?_
    (k _ ⟨?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩)
  · simp only [exec, ht, ne_eq, not_false_eq_true, ho, and_self, ite_true, ha, State.load, h₁, h₂,
      Option.bind_some, Option.map_some, Mem.readW]
    try rfl
  · simp only [State.write]; simp [ht]
  · simp [State.write]
  · simp [State.write, h1, h2]

end

/-! ## Offsets from a base -/

theorem ofNat_add8 (b : Addr) (off : Nat) :
    b + BitVec.ofNat 64 off + 8 = b + BitVec.ofNat 64 (off + 8) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl

theorem readW_off_self (m : Mem) (b : Addr) (i : Nat) (v : BitVec 64) :
    (m.writeW (b + BitVec.ofNat 64 i) v).readW (b + BitVec.ofNat 64 i) 64 = v :=
  Mem.readW_writeW_self64 _ _ _

theorem readW_off_sep (m : Mem) (b : Addr) {i j : Nat} (v : BitVec 64) (h : i + 8 ≤ j ∨ j + 8 ≤ i)
    (hi : i + 8 ≤ 2 ^ 64) (hj : j + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 j) v).readW (b + BitVec.ofNat 64 i) 64 = m.readW (b + BitVec.ofNat 64 i) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hi hj) (by decide)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `stp` at `b + off`, with `b` in the base register. -/
theorem wp_stpB {t1 t2 n : Reg} {off : Nat} {b : Addr} (ho : off % 8 = 0 ∧ off ≤ 504)
    (hb : s.gpr n = b) (h₁ : InRegions s.wr (b + BitVec.ofNat 64 off) 8)
    (h₂ : InRegions s.wr (b + BitVec.ofNat 64 (off + 8)) 8)
    (k : ∀ s', Mupd s s' ((s.mem.writeW (b + BitVec.ofNat 64 off) (s.gpr t1)).writeW
      (b + BitVec.ofNat 64 (off + 8)) (s.gpr t2)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stp t1 t2 n off :: is)) s Q :=
  wp_stp ho (a := b + BitVec.ofNat 64 off) (by rw [hb]) h₁ (by rwa [ofNat_add8])
    fun s' h => k s' (by rwa [ofNat_add8] at h)

/-- `ldp` at `b + off`, with `b` in the base register. -/
theorem wp_ldpB {t1 t2 n : Reg} {off : Nat} {b : Addr} (ht : t1 ≠ t2) (ho : off % 8 = 0 ∧ off ≤ 504)
    (hb : s.gpr n = b) (h₁ : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 off) 8)
    (h₂ : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (off + 8)) 8)
    (k : ∀ s', Upd2 s s' t1 t2 (s.mem.readW (b + BitVec.ofNat 64 off) 64)
      (s.mem.readW (b + BitVec.ofNat 64 (off + 8)) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldp t1 t2 n off :: is)) s Q :=
  wp_ldp ht ho (a := b + BitVec.ofNat 64 off) (by rw [hb]) h₁ (by rwa [ofNat_add8])
    fun s' h => k s' (by rwa [ofNat_add8] at h)

end

/-! ## `setup`: saving our caller's registers -/

/-- The registers we save, and where. -/
def saves : List (Reg × Nat) :=
  [(.x19, 0), (.x21, 8), (.x22, 16), (.x25, 24), (.x26, 32), (.x27, 40), (.x28, 48), (.x30, 56)]

/-- The registers of `s` we save, at `slO`. -/
def Slots (P : Params) (s : State) (m : Mem) : Prop :=
  ∀ p ∈ saves, m.readW (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 p.2) 64 = s.gpr p.1

/-- The callee-saved registers we never write. -/
def kept : List Reg := [.x20, .x23, .x24]

/-- The state after `setup`, from `s` (on entry). -/
structure S1 (P : Params) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = fR P s :: s.wr
  sp : t.sp = fb P s
  x0 : t.gpr .x0 = fb P s
  x25 : t.gpr .x25 = s.gpr .x1
  x26 : t.gpr .x26 = s.gpr .x2
  x27 : t.gpr .x27 = dp s
  keep : ∀ r ∈ kept, t.gpr r = s.gpr r
  frame : Frame [fR P s] s.mem t.mem
  slots : Slots P s t.mem

theorem slot_in {P : Params} (hF : Fits P) (s : State) {wr : List Region} (hwr : fR P s ∈ wr) {j : Nat}
    (hj : j ≤ 56) : InRegions wr (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 j) 8 :=
  ⟨fR P s, hwr, by
    have := sl_le P; have := hF.lt
    rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem setup_ok {P : Params} (hF : Fits P) {s a : State} (ha : a = allocated (frameBytes P) s) :
    WP isa (.block (setup P)) a (S1 P s) := by
  have hsl := sl_le P; have hlt := hF.lt
  subst ha
  have hwr : (allocated (frameBytes P) s).wr = fR P s :: s.wr := rfl
  have hin : ∀ {t : State}, t.wr = fR P s :: s.wr → ∀ j ≤ 56,
      InRegions t.wr (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 j) 8 :=
    fun h j hj => slot_in hF s (by rw [h]; exact List.mem_cons_self ..) hj
  simp only [setup]
  refine wp_addSp (by omega) fun s₁ u₁ => ?_
  have h10 : s₁.gpr .x10 = fb P s + BitVec.ofNat 64 (slO P) := by rw [u₁.gpr]; rfl
  have w₁ : s₁.wr = fR P s :: s.wr := u₁.wr.trans hwr
  refine wp_stpB (by decide) h10 (hin w₁ 0 (by omega)) (hin w₁ 8 (by omega)) fun s₂ m₂ => ?_
  have w₂ : s₂.wr = fR P s :: s.wr := m₂.wr.trans w₁
  refine wp_stpB (by decide) (by rw [m₂.gpr]; exact h10) (hin w₂ 16 (by omega)) (hin w₂ 24 (by omega))
    fun s₃ m₃ => ?_
  have w₃ : s₃.wr = fR P s :: s.wr := m₃.wr.trans w₂
  refine wp_stpB (by decide) (by rw [m₃.gpr, m₂.gpr]; exact h10) (hin w₃ 32 (by omega))
    (hin w₃ 40 (by omega)) fun s₄ m₄ => ?_
  have w₄ : s₄.wr = fR P s :: s.wr := m₄.wr.trans w₃
  refine wp_stpB (by decide) (by rw [m₄.gpr, m₃.gpr, m₂.gpr]; exact h10) (hin w₄ 48 (by omega))
    (hin w₄ 56 (by omega)) fun s₅ m₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_mov fun s₈ u₈ =>
    wp_addSp (by omega) fun s₉ u₉ => WP.block_nil ?_
  -- Registers of `s₅` are those of `s` but `x10`.
  have g₅ : ∀ r, r ≠ .x10 → s₅.gpr r = s.gpr r := fun r hr => by
    rw [m₅.gpr, m₄.gpr, m₃.gpr, m₂.gpr, u₁.other r hr]; rfl
  have sp₉ : s₉.sp = fb P s := by
    rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, m₅.sp, m₄.sp, m₃.sp, m₂.sp, u₁.sp]; rfl
  have mem₉ : s₉.mem = s₅.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have mem₅ : s₅.mem = ((((((((s.mem.writeW (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 0) (s.gpr .x19)).writeW
      (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 (0 + 8)) (s.gpr .x21)).writeW (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 16) (s.gpr .x22)).writeW
      (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 (16 + 8)) (s.gpr .x25)).writeW (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 32) (s.gpr .x26)).writeW
      (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 (32 + 8)) (s.gpr .x27)).writeW (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 48) (s.gpr .x28)).writeW
      (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 (48 + 8)) (s.gpr .x30)) := by
    simp only [m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₄.gpr, m₃.gpr, m₂.gpr, u₁.mem,
      u₁.other _ (show Reg.x19 ≠ .x10 by decide), u₁.other _ (show Reg.x21 ≠ .x10 by decide),
      u₁.other _ (show Reg.x22 ≠ .x10 by decide), u₁.other _ (show Reg.x25 ≠ .x10 by decide),
      u₁.other _ (show Reg.x26 ≠ .x10 by decide), u₁.other _ (show Reg.x27 ≠ .x10 by decide),
      u₁.other _ (show Reg.x28 ≠ .x10 by decide), u₁.other _ (show Reg.x30 ≠ .x10 by decide)]
    rfl
  have hc : ∀ j ≤ 56, (fR P s).Contains (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 j) 8 := fun j hj => by
    rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)
  have h64 : slO P + 64 ≤ 2 ^ 64 := by omega
  refine
    { rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, m₅.rd, m₄.rd, m₃.rd, m₂.rd, u₁.rd]; rfl
      wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, m₅.wr, w₄]
      sp := sp₉
      x0 := by rw [u₉.gpr, u₈.sp, u₇.sp, u₆.sp, m₅.sp, m₄.sp, m₃.sp, m₂.sp, u₁.sp]; simp [allocated]
      x25 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
        g₅ _ (by decide)]
      x26 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
        g₅ _ (by decide)]
      x27 := by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
        g₅ _ (by decide)]
      keep := fun r hr => by
        have : r ≠ .x0 ∧ r ≠ .x25 ∧ r ≠ .x26 ∧ r ≠ .x27 ∧ r ≠ .x10 := by
          simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide
        rw [u₉.other _ this.1, u₈.other _ this.2.2.2.1, u₇.other _ this.2.2.1, u₆.other _ this.2.1,
          g₅ _ this.2.2.2.2]
      frame := by
        rw [mem₉, mem₅]
        have hm := List.mem_singleton_self (fR P s)
        exact ((((((((Frame.refl _ _).writeW hm _ (hc 0 (by omega))).writeW hm _ (hc 8 (by omega))).writeW hm _
          (hc 16 (by omega))).writeW hm _ (hc 24 (by omega))).writeW hm _ (hc 32 (by omega))).writeW hm _
          (hc 40 (by omega))).writeW hm _ (hc 48 (by omega))).writeW hm _ (hc 56 (by omega))
      slots := fun p hp => by
        rw [mem₉, mem₅]
        simp only [saves, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (disch := omega) only [readW_off_self, readW_off_sep, Nat.reduceAdd] }

/-! ## Between the phases -/

/-- What every state inside the frame keeps of `s`, the state on entry. -/
structure Mid (P : Params) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = fR P s :: s.wr
  sp : t.sp = fb P s
  x25 : t.gpr .x25 = s.gpr .x1
  x26 : t.gpr .x26 = s.gpr .x2
  keep : ∀ r ∈ kept, t.gpr r = s.gpr r
  frame : Frame (fR P s :: s.wr) s.mem t.mem
  slots : Slots P s t.mem

theorem S1.mid {P : Params} {s t : State} (h : S1 P s t) : Mid P s t :=
  ⟨h.rd, h.wr, h.sp, h.x25, h.x26, h.keep,
    h.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..,
    h.slots⟩

theorem saves_le : ∀ p ∈ saves, p.2 ≤ 56 := by decide

/-- The registers `Mid` keeps. -/
abbrev midRegs : List Reg := .x25 :: .x26 :: kept

/-- The registers our code writes, besides the compression function's. -/
def scratchRegs : List Reg :=
  [.x0, .x1, .x2, .x3, .x6, .x7, .x9, .x10, .x11, .x12, .x13, .x16, .x17, .x19, .x21, .x22, .x27, .x28]

theorem mid_ne : ∀ r ∈ midRegs, ∀ q ∈ scratchRegs, r ≠ q := by decide

theorem mid_pres : ∀ r ∈ midRegs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem slot_contains {P : Params} (s : State) {j : Nat} (hj : j ≤ 56) :
    (slR P s).Contains (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 j) 8 :=
  Offset.contains_base _ (by omega) (by omega)

/-- A change of memory within regions of the frame other than the saved
registers', and of no register `Mid` keeps, keeps `Mid`. -/
theorem Mid.of_frame {P : Params} {s t t' : State} (h : Mid P s t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ midRegs, t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hsub : ∀ r ∈ rs, ∃ r' ∈ fR P s :: s.wr, Region.Sub r r')
    (hsl : ∀ r ∈ rs, (slR P s).Disjoint r) : Mid P s t' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  x25 := (hg _ (by simp)).trans h.x25
  x26 := (hg _ (by simp)).trans h.x26
  keep r hr := (hg r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))).trans (h.keep r hr)
  frame := h.frame.trans (hf.sub hsub)
  slots p hp := by
    rw [← h.slots p hp]
    exact hf.readW (slot_contains s (saves_le p hp)) hsl (by decide)

/-- Regions at offsets within the frame are covered by the regions of a
state inside it. -/
theorem covers_frame {P : Params} (s : State) {t : State} (hwr : t.wr = fR P s :: s.wr) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = fb P s + BitVec.ofNat 64 off ∧ off + r.len ≤ frameBytes P) :
    Covers rs t.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨fR P s, by rw [hwr]; exact List.mem_cons_self .., off, hb, hl⟩

theorem fb_zero (P : Params) (s : State) : fb P s = fb P s + BitVec.ofNat 64 0 := by simp

/-- The message's bytes are those on entry: the frame is disjoint from it. -/
theorem data_eq {P : Params} {D : Nat} {s t : State} (hp : Pre P D s) (h : Mid P s t) {i : Nat}
    (hi : i < len s) : t.mem (dp s + BitVec.ofNat 64 i) = s.mem (dp s + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s)
    (fun r hr => by
      rw [hp.wr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.f_d.symm
      · exact hp.d_o)
    (Nat.le_of_lt (s.gpr .x1).isLt) hi

/-- The message. -/
abbrev msg (s : State) : List Byte := bytesAt s.mem (dp s) (len s)

theorem msg_length (s : State) : (msg s).length = len s := by simp [bytesAt]

theorem msg_getD (s : State) {i : Nat} (hi : i < len s) : (msg s).getD i 0 = s.mem (dp s + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem len_lt (s : State) : len s < 2 ^ 64 := (s.gpr .x1).isLt

theorem x1_eq (s : State) : s.gpr .x1 = BitVec.ofNat 64 (len s) := by simp [len]

/-! ## `init` -/

theorem init_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} {iv : H.HV} {init : Prog isa}
    (hi : ∀ s, (initK H iv).pre s → ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧
      (initK H iv).post s s')
    (hiw : ∀ r, r ≠ .x9 → r ≠ .x10 → ∀ i ∈ instrs init, clobbers i r = false) (hin : init.noCalls = true)
    {s t : State} (h : S1 P s t) :
    WP isa init t fun t' => Mid P s t' ∧ t'.gpr .x27 = dp s ∧ H.stateAt t'.mem (fb P s) = iv := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P
  have hcov : Covers [stR P s] t.wr :=
    covers_frame s h.wr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨0, fb_zero P s, show 0 + (P.N + P.B) ≤ frameBytes P by omega⟩
  refine WP.inline hi (rd := []) (wr := [stR P s]) ⟨rfl, by simp [State.withRegions, h.x0]⟩
    (Covers.right hcov) hcov (fun t' hrd hwr habi hf hg hpost => ?_) hin
  have hk : ∀ r, r ≠ .x9 → r ≠ .x10 → t'.gpr r = t.gpr r := fun r h9 h10 => hg r (hiw r h9 h10)
  refine ⟨Mid.of_frame h.mid hrd hwr habi.2.1
      (fun r hr => hk r (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., st_sub s⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (st_sl hF s).symm),
    (hk _ (by decide) (by decide)).trans h.x27, ?_⟩
  have := (show H.Repr iv t'.mem (fb P s) [] by simpa [initK, State.withRegions, h.x0] using hpost).1
  simpa [Md.compressList_zero] using this

/-! ## Calling the compression function -/

/-- A call of the compression function on the `k` blocks at `src`, the hash
value at `st` and the scratch space at `scr`: the callee-saved registers
other than `x30` are kept. -/
theorem call_ok {P : Params} {H : Md P.B P.N P.L} {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {t : State} {st scr src : Addr} {k : Nat}
    (h0 : t.gpr .x0 = st) (h1 : t.gpr .x1 = src) (h2 : (t.gpr .x2).toNat = k) (h3 : t.gpr .x3 = scr)
    (d₁ : Region.Disjoint ⟨st, P.N⟩ ⟨scr, P.so⟩) (d₂ : Region.Disjoint ⟨src, P.B * k⟩ ⟨st, P.N⟩)
    (d₃ : Region.Disjoint ⟨src, P.B * k⟩ ⟨scr, P.so⟩)
    (hc : Covers [⟨src, P.B * k⟩, ⟨st, P.N⟩, ⟨scr, P.so⟩] (t.rd ++ t.wr))
    (hw : Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] t.wr) {Q : State → Prop}
    (hQ : ∀ t', t'.rd = t.rd → t'.wr = t.wr → (∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) →
      t'.sp = t.sp → Frame [⟨st, P.N⟩, ⟨scr, P.so⟩] t.mem t'.mem →
      H.stateAt t'.mem st = H.compressBlocks (H.stateAt t.mem st) t.mem src k → Q t') :
    WP isa (.call name code) t Q := by
  have c0 : t.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : t.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans h1
  have c2 : (t.callEntry.gpr .x2).toNat = k := by rw [State.callEntry_gpr _ (by decide)]; exact h2
  have c3 : t.callEntry.gpr .x3 = scr := (State.callEntry_gpr _ (by decide)).trans h3
  refine WP.call (k := compressK H) hf.verified
    (rd := [⟨src, P.B * k⟩]) (wr := [⟨st, P.N⟩, ⟨scr, P.so⟩]) ?_ ?_ hw ?_ hf.noFrames
  · simp only [compressK, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · simpa using hc
  · intro t' hrd hwr hsp hf' hcs _ hpost
    simp only [compressK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2] at hpost
    exact hQ t' hrd hwr hcs hsp hf' hpost

/-- What a call of the compression function from inside the frame keeps. -/
theorem call_mid {P : Params} (hF : Fits P) {s t t' : State} (h : Mid P s t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hcs : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hsp : t'.sp = t.sp) (hf : Frame [hR P s, scR P s] t.mem t'.mem) : Mid P s t' :=
  Mid.of_frame h hrd hwr hsp
    (fun r hr => hcs r (mid_pres r hr).1 (mid_pres r hr).2) hf
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., h_sub s⟩
      · exact ⟨_, List.mem_cons_self .., sc_sub s⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (st_sl hF s).symm.sub_right (Region.sub_prefix (by omega))
      · exact (sc_sl hF s).symm)

/-! ## The whole blocks -/

theorem whole_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} {iv : H.HV}
    {name : String} {code : Prog isa} (hf : CalleeOk H code) {s t : State} (hp : Pre P D s)
    (h : Mid P s t) (h27 : t.gpr .x27 = dp s) (hiv : H.stateAt t.mem (fb P s) = iv) :
    WP isa (whole P name code) t fun t' => Mid P s t' ∧
      t'.gpr .x27 = dp s + BitVec.ofNat 64 (P.B * (len s / P.B)) ∧
      H.stateAt t'.mem (fb P s) = H.compressList iv (msg s) (len s / P.B) := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have hB := hd.pos
  have hlen := len_lt s
  have hle : P.B * (len s / P.B) ≤ len s := Nat.mul_div_le _ _
  have hdl : len s / P.B ≤ len s := Nat.div_le_self _ _
  unfold whole
  refine WP.seq (wp_lsr (by have := hd.log; omega) fun t₁ u₁ => WP.block_nil ?_)
  have h28 : t₁.gpr .x28 = BitVec.ofNat 64 (len s / P.B) := by
    rw [u₁.gpr, h.x25, x1_eq, hd.shr hlen]
  have m₁ : Mid P s t₁ := Mid.of_frame h u₁.rd u₁.wr u₁.sp
    (fun r hr => u₁.other r (mid_ne r hr _ (by decide)))
    (rs := []) (fun x _ => by rw [u₁.mem]) (fun _ hr => absurd hr List.not_mem_nil)
    (fun _ hr => absurd hr List.not_mem_nil)
  have e27 : t₁.gpr .x27 = dp s := (u₁.other _ (by decide)).trans h27
  have hz : eval (.zero .x .x28) t₁ = some (decide (len s / P.B = 0)) := by
    rw [eval_zero, h28, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (len s / P.B = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ⟨m₁, by rw [e27, hb]; simp, ?_⟩
    rw [hb, Md.compressList_zero, u₁.mem, hiv]
  · simp only [decide_eq_false_iff_not] at hb
    unfold Impl.MdStream.AArch64.OneShot.compressWith
    refine WP.seq (WP.seq (wp_addSp (by omega) fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_mov fun t₄ u₄ =>
      wp_addSp (by omega) fun t₅ u₅ => WP.block_nil ?_))
    · -- The registers and memory at the call.
      have sp₅ : t₅.sp = fb P s := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, m₁.sp]
      have mem₅ : t₅.mem = t₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
      have m₅ : Mid P s t₅ := Mid.of_frame m₁ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd])
        (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]) (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp])
        (fun r hr => by
          rw [u₅.other _ (mid_ne r hr _ (by decide)), u₄.other _ (mid_ne r hr _ (by decide)),
            u₃.other _ (mid_ne r hr _ (by decide)), u₂.other _ (mid_ne r hr _ (by decide))])
        (rs := []) (fun x _ => by rw [mem₅]) (fun _ hr => absurd hr List.not_mem_nil)
        (fun _ hr => absurd hr List.not_mem_nil)
      have g0 : t₅.gpr .x0 = fb P s := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁.sp]; simp
      have g1 : t₅.gpr .x1 = dp s := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), e27]
      have g2 : (t₅.gpr .x2).toNat = len s / P.B := by
        rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h28,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have g3 : t₅.gpr .x3 = fb P s + BitVec.ofNat 64 (scO P) := by rw [u₅.gpr, u₄.sp, u₃.sp, u₂.sp, m₁.sp]
      have g27 : t₅.gpr .x27 = dp s := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), e27]
      have g28 : t₅.gpr .x28 = BitVec.ofNat 64 (len s / P.B) := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h28]
      have hbl : Region.Sub ⟨dp s, P.B * (len s / P.B)⟩ (dR s) := Region.sub_prefix hle
      refine call_ok hf g0 g1 g2 g3 (h_sc hF s) ((hp.f_d.symm.sub_left hbl).sub_right (h_sub s))
        ((hp.f_d.symm.sub_left hbl).sub_right (sc_sub s)) ?_ ?_ fun t₆ hrd hwr hcs hsp hf' hst => ?_
      · rw [m₅.rd, m₅.wr, hp.rd]
        apply Covers.of_sub
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨dR s, by simp, 0, by simp, by simp only [Nat.zero_add]; exact hle⟩
        · exact ⟨fR P s, by simp, 0, fb_zero P s, show 0 + P.N ≤ frameBytes P by omega⟩
        · exact ⟨fR P s, by simp, scO P, rfl, show scO P + P.so ≤ frameBytes P by omega⟩
      · exact covers_frame s m₅.wr fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨0, fb_zero P s, show 0 + P.N ≤ frameBytes P by omega⟩
          · exact ⟨scO P, rfl, show scO P + P.so ≤ frameBytes P by omega⟩
      have m₆ := call_mid hF m₅ hrd hwr hcs hsp hf'
      refine wp_lsl (by have := hd.log; omega) fun t₇ u₇ => wp_add fun t₈ u₈ => WP.block_nil ?_
      refine ⟨Mid.of_frame m₆ (by rw [u₈.rd, u₇.rd]) (by rw [u₈.wr, u₇.wr]) (by rw [u₈.sp, u₇.sp])
          (fun r hr => by
            rw [u₈.other _ (mid_ne r hr _ (by decide)), u₇.other _ (mid_ne r hr _ (by decide))])
          (rs := []) (fun x _ => by rw [u₈.mem, u₇.mem]) (fun _ hr => absurd hr List.not_mem_nil)
          (fun _ hr => absurd hr List.not_mem_nil), ?_, ?_⟩
      · rw [u₈.gpr, u₇.other _ (by decide), u₇.gpr, hcs _ (by decide) (by decide), hcs _ (by decide) (by decide),
          g27, g28, hd.shl (by omega)]
      · rw [u₈.mem, u₇.mem, hst, mem₅, u₁.mem, hiv]
        refine Md.compressBlocks_eq H fun j hj => ?_
        rw [msg_getD s (by omega)]
        exact data_eq hp h (by omega)

/-! ## Bytes at offsets from a base -/

theorem write_off (m : Mem) (b : Addr) {o j n : Nat} (v : BitVec (8 * n)) (ho : o + n < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    m.write (b + BitVec.ofNat 64 o) n v (b + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + n then v.extractLsb' (8 * (j - o)) 8 else m (b + BitVec.ofNat 64 j) := by
  simp only [Mem.write]
  rw [Offset.sub_toNat' b (by omega) hj]
  by_cases h : o ≤ j
  · simp only [h, ite_true, true_and]
    by_cases h' : j < o + n
    · simp only [show j - o < n by omega, ite_true, h']
    · simp only [show ¬ j - o < n by omega, ite_false, h']
  · simp only [h, ite_false, false_and, show ¬ 2 ^ 64 + j - o < n by omega]

theorem writeW64_off (m : Mem) (b : Addr) {o j : Nat} (v : BitVec 64) (ho : o + 8 < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    m.writeW (b + BitVec.ofNat 64 o) v (b + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + 8 then v.extractLsb' (8 * (j - o)) 8 else m (b + BitVec.ofNat 64 j) := by
  simp only [Mem.writeW]
  exact write_off m b _ ho hj

theorem writeW8_off (m : Mem) (b : Addr) {o j : Nat} (v : BitVec 8) (ho : o + 1 < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    m.writeW (b + BitVec.ofNat 64 o) v (b + BitVec.ofNat 64 j) =
      if j = o then v else m (b + BitVec.ofNat 64 j) := by
  simp only [Mem.writeW]
  rw [write_off m b _ ho hj]
  by_cases h : j = o
  · subst h; simp
  · simp only [show ¬ (o ≤ j ∧ j < o + 1) by omega, ite_false, h]

theorem writeBytes_off (m : Mem) (b : Addr) {o j : Nat} (xs : List Byte) (ho : o + xs.length < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    writeBytes m (b + BitVec.ofNat 64 o) xs (b + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + xs.length then xs.getD (j - o) 0 else m (b + BitVec.ofNat 64 j) := by
  simp only [writeBytes]
  rw [Offset.sub_toNat' b (by omega) hj]
  by_cases h : o ≤ j
  · simp only [h, ite_true, true_and]
    by_cases h' : j < o + xs.length
    · simp only [show j - o < xs.length by omega, ite_true, h']
    · simp only [show ¬ j - o < xs.length by omega, ite_false, h']
  · simp only [h, ite_false, false_and, show ¬ 2 ^ 64 + j - o < xs.length by omega]

/-- Byte `i` of a little-endian doubleword read. -/
theorem readW64_byte (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    (m.readW a 64).extractLsb' (8 * i) 8 = m (a + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi]
  rfl

/-! ## The block -/

section
variable (P : Params) (s : State)

/-- The block's address. -/
abbrev buf : Addr := fb P s + BitVec.ofNat 64 P.N
/-- The bytes of the message after its whole blocks. -/
abbrev rem : Nat := len s % P.B
/-- Where they start. -/
abbrev whl : Nat := P.B * (len s / P.B)

end

theorem buf_add (P : Params) (s : State) (j : Nat) :
    buf P s + BitVec.ofNat 64 j = fb P s + BitVec.ofNat 64 (P.N + j) := add_ofNat _ _ _

/-- The block holds the first `c` bytes after the whole blocks of the
message, then zeros. -/
def Blk (P : Params) (s : State) (c : Nat) (m : Mem) : Prop :=
  ∀ j < P.B, m (fb P s + BitVec.ofNat 64 (P.N + j)) = if j < c then (msg s).getD (whl P s + j) 0 else 0

theorem getD_congr {xs : List Byte} {a b : Nat} (h : a = b) : xs.getD a 0 = xs.getD b 0 := h ▸ rfl

/-- A byte of a doubleword loaded from the message. -/
theorem ld_byte {P : Params} {D : Nat} {s t : State} (hp : Pre P D s) (h : Mid P s t) {a i e : Nat}
    (hi : a + i < len s) (hi8 : i < 8) (he : e = i) :
    (t.mem.readW (dp s + BitVec.ofNat 64 a) 64).extractLsb' (8 * e) 8 = (msg s).getD (a + i) 0 := by
  subst he
  rw [readW64_byte _ _ hi8, add_ofNat, data_eq hp h hi, msg_getD s hi]

/-- `zeroBuf`'s stores: the first `n` pairs of doublewords of the block. -/
theorem zeros_ok {P : Params} (hF : Fits P) (hd : Dims P) (s : State) (n : Nat) (hn : n ≤ P.B / 16)
    {t : State} (h12 : t.gpr .x12 = buf P s) (h9 : t.gpr .x9 = 0) (hwr : fR P s ∈ t.wr) :
    WP isa (.block ((List.range n).map fun k => .stp .x9 .x9 .x12 (16 * k))) t fun t' =>
      t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧ Frame [bR P s] t.mem t'.mem ∧
      ∀ j < 16 * n, t'.mem (fb P s + BitVec.ofNat 64 (P.N + j)) = 0 := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, z₁⟩ => ?_
    have hin : ∀ o ≤ P.B - 8, InRegions t₁.wr (buf P s + BitVec.ofNat 64 o) 8 := fun o ho =>
      ⟨fR P s, by rw [wr₁]; exact hwr, by
        rw [buf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
    have hb : 16 * n + 16 ≤ P.B := by omega
    refine wp_stpB (by omega) (by rw [g₁, h12]) (hin _ (by omega)) (hin _ (by omega)) fun t₂ m₂ =>
      WP.block_nil ?_
    have hbc : ∀ o ≤ P.B - 8, (bR P s).Contains (buf P s + BitVec.ofNat 64 o) (64 / 8) := fun o ho =>
      Offset.contains_base _ (by omega) (by omega)
    refine ⟨by rw [m₂.gpr, g₁], by rw [m₂.rd, rd₁], by rw [m₂.wr, wr₁], by rw [m₂.sp, sp₁], ?_, fun j hj => ?_⟩
    · rw [m₂.mem]
      exact (f₁.writeW (List.mem_singleton_self _) _ (hbc _ (by omega))).writeW (List.mem_singleton_self _) _
        (hbc _ (by omega))
    · simp only [m₂.mem, g₁, h9, add_ofNat]
      rw [writeW64_off _ _ _ (by omega) (by omega), writeW64_off _ _ _ (by omega) (by omega)]
      split
      · simp
      split
      · simp
      · exact z₁ j (by omega)

/-- `zeroBuf`: the block is zero, and `x12` points at it. -/
theorem zeroBuf_ok {P : Params} (hF : Fits P) (hd : Dims P) {s t : State} (h : Mid P s t) :
    WP isa (.block (zeroBuf P)) t fun t' => Mid P s t' ∧ (∀ r, r ≠ .x9 → r ≠ .x12 → t'.gpr r = t.gpr r) ∧
      t'.gpr .x9 = 0 ∧ t'.gpr .x12 = buf P s ∧ Frame [bR P s] t.mem t'.mem ∧ Blk P s 0 t'.mem := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N
  simp only [zeroBuf, List.cons_append]
  refine wp_movz fun t₁ u₁ => wp_addSp (by omega) fun t₂ u₂ => ?_
  have h12 : t₂.gpr .x12 = buf P s := by rw [u₂.gpr, u₁.sp, h.sp]
  have h9 : t₂.gpr .x9 = 0 := by rw [u₂.other _ (by decide), u₁.gpr]; rfl
  refine WP.mono (zeros_ok hF hd s (P.B / 16) (Nat.le_refl _) h12 h9 (by rw [u₂.wr, u₁.wr, h.wr]; simp))
    fun t₃ ⟨g₃, rd₃, wr₃, sp₃, f₃, z₃⟩ => ?_
  have hk : ∀ r, r ≠ .x9 → r ≠ .x12 → t₃.gpr r = t.gpr r := fun r h9 h12 => by
    rw [g₃, u₂.other _ h12, u₁.other _ h9]
  have f : Frame [bR P s] t.mem t₃.mem := by rwa [u₂.mem, u₁.mem] at f₃
  refine ⟨Mid.of_frame h (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr]) (by rw [sp₃, u₂.sp, u₁.sp])
      (fun r hr => hk r (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide))) f
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., b_sub s⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr
                      exact (st_sl hF s).symm.sub_right (Offset.sub_base _ (by omega)) |>.symm |>.symm),
    hk, by rw [g₃, h9], by rw [g₃, h12], f, fun j hj => ?_⟩
  rw [z₃ j (by rcases hd.B with h | h <;> omega)]
  simp

/-! ## Counting loops -/

/-- `do body while r ≠ 0`, with `r = K ≥ 1` on entry and each iteration
`i < K` decrementing it. -/
theorem count_loop1 {body : Prog isa} {r : Reg} {I : Nat → State → Prop} {K : Nat} (hK : K < 2 ^ 64)
    (hK1 : K ≠ 0)
    (hstep : ∀ i < K, ∀ t, I i t → t.gpr r = BitVec.ofNat 64 (K - i) →
      WP isa body t fun t' => I (i + 1) t' ∧ t'.gpr r = BitVec.ofNat 64 (K - (i + 1)))
    {t : State} (h₀ : I 0 t) (hr : t.gpr r = BitVec.ofNat 64 K) :
    WP isa (.loop body (.nonzero .x r)) t (I K) := by
  refine WP.loop (M := isa) (fun n t => ∃ i, n = K - i ∧ i < K ∧ I i t ∧ t.gpr r = BitVec.ofNat 64 (K - i))
    ?_ K t ⟨0, rfl, by omega, h₀, by simpa using hr⟩
  rintro n t ⟨i, rfl, hi, hI, hri⟩
  refine WP.mono (hstep i hi t hI hri) fun t' ⟨hI', hr'⟩ => ?_
  have hz' : isa.eval (.nonzero .x r) t' = some (decide (K - (i + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x r) t' = _
    rw [eval_nonzero, hr', bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : K - (i + 1) = 0
  · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
    rwa [show i + 1 = K by omega] at hI'
  · exact .inr ⟨by rw [hz']; simp [hl], _, by omega, i + 1, rfl, by omega, hI', hr'⟩

/-- `if r = 0 skip else do body while r ≠ 0`, with `r = K` on entry and each
iteration `i < K` decrementing it. -/
theorem count_loop {body : Prog isa} {r : Reg} {I : Nat → State → Prop} {K : Nat} (hK : K < 2 ^ 64)
    (hstep : ∀ i < K, ∀ t, I i t → t.gpr r = BitVec.ofNat 64 (K - i) →
      WP isa body t fun t' => I (i + 1) t' ∧ t'.gpr r = BitVec.ofNat 64 (K - (i + 1)))
    {t : State} (h₀ : I 0 t) (hr : t.gpr r = BitVec.ofNat 64 K) :
    WP isa (.ite (.zero .x r) (.block []) (.loop body (.nonzero .x r))) t (I K) := by
  have hz : eval (.zero .x r) t = some (decide (K = 0)) := by
    rw [eval_zero, hr, ofNat_beq_zero hK]
  refine WP.ite (decide (K = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb; exact WP.block_nil h₀
  · simp only [decide_eq_false_iff_not] at hb
    exact count_loop1 hK hb hstep h₀ hr

/-! ## Copying the bytes left -/

/-- Copying, from the state `t₀`: `c` bytes copied. -/
structure CInv (P : Params) (s t₀ : State) (c : Nat) (t : State) : Prop where
  mid : Mid P s t
  c_le : c ≤ rem P s
  x27 : t.gpr .x27 = dp s + BitVec.ofNat 64 (whl P s + c)
  x12 : t.gpr .x12 = buf P s + BitVec.ofNat 64 c
  x28 : t.gpr .x28 = BitVec.ofNat 64 (rem P s)
  frame : Frame [bR P s] t₀.mem t.mem
  blk : Blk P s c t.mem

theorem whl_rem (P : Params) (s : State) : whl P s + rem P s = len s := Nat.div_add_mod _ _

/-- A byte of the message, read through the frame. -/
theorem msg_byte {P : Params} {D : Nat} {s t : State} (hp : Pre P D s) (h : Mid P s t) {i : Nat}
    (hi : i < len s) : t.mem (dp s + BitVec.ofNat 64 i) = (msg s).getD i 0 := by
  rw [data_eq hp h hi, msg_getD s hi]

theorem copy16_step {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t₀ t : State} (hp : Pre P D s)
    {c k : Nat} (hc : c + 16 ≤ rem P s) (h : CInv P s t₀ c t) (h13 : t.gpr .x13 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) :
    WP isa (.block copy16) t fun t' => CInv P s t₀ (c + 16) t' ∧ t'.gpr .x13 = BitVec.ofNat 64 (k - 1) := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N
  have hwr := whl_rem P s; have hlen := len_lt s
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  have hm := h.mid
  have hin : ∀ o, whl P s + c + o + 8 ≤ len s →
      InRegions (t.rd ++ t.wr) (dp s + BitVec.ofNat 64 (whl P s + c) + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨dR s, by rw [hm.rd, hp.rd]; simp, by
      rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩
  unfold copy16
  refine wp_ldpB (by decide) (by decide) h.x27 (hin 0 (by omega)) (hin 8 (by omega)) fun t₁ u₁ => ?_
  have hout : ∀ o, c + o + 8 ≤ P.B →
      InRegions t₁.wr (buf P s + BitVec.ofNat 64 c + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨fR P s, by rw [u₁.wr, hm.wr]; simp, by
      rw [add_ofNat, buf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_stpB (by decide) (by rw [u₁.other _ (by decide) (by decide), h.x12]) (hout 0 (by omega))
    (hout 8 (by omega)) fun t₂ m₂ => ?_
  refine wp_addImm (by decide) fun t₃ u₃ => wp_addImm (by decide) fun t₄ u₄ =>
    wp_subImm (by decide) fun t₅ u₅ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .x9 → r ≠ .x10 → t₂.gpr r = t.gpr r := fun r h9 h10 => by
    rw [m₂.gpr, u₁.other _ h9 h10]
  have mem₅ : t₅.mem = t₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have hbc : ∀ o, c + o + 8 ≤ P.B → (bR P s).Contains (buf P s + BitVec.ofNat 64 c + BitVec.ofNat 64 o) (64 / 8) :=
    fun o ho => by rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)
  have fr₂ : Frame [bR P s] t.mem t₂.mem := by
    rw [m₂.mem, u₁.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hbc 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (hbc 8 (by omega))
  refine ⟨⟨Mid.of_frame hm (by rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr])
      (by rw [u₅.sp, u₄.sp, u₃.sp, m₂.sp, u₁.sp])
      (fun r hr => by
        rw [u₅.other _ (mid_ne r hr _ (by decide)), u₄.other _ (mid_ne r hr _ (by decide)),
          u₃.other _ (mid_ne r hr _ (by decide)), g₂ _ (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide))])
      (by rw [mem₅]; exact fr₂)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., b_sub s⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr
                      exact (st_sl hF s).symm.sub_right (Offset.sub_base _ (by omega)) |>.symm |>.symm),
    by omega, ?_, ?_, ?_, by rw [mem₅]; exact h.frame.trans fr₂, fun j hj => ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide) (by decide), h.x27, add_ofNat, Nat.add_assoc]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide) (by decide), h.x12, add_ofNat]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide) (by decide), h.x28]
  · simp only [mem₅, m₂.mem, u₁.gpr₁, u₁.gpr₂, u₁.mem, add_ofNat]
    rw [writeW64_off _ _ _ (by omega) (by omega), writeW64_off _ _ _ (by omega) (by omega)]
    split
    · rw [ld_byte hp hm (i := j - (c + 8)) ?_ ?_ ?_, itp (show j < c + 16 by omega)]
      · exact getD_congr (by omega)
      all_goals omega
    split
    · rw [ld_byte hp hm (i := j - c) ?_ ?_ ?_, itp (show j < c + 16 by omega)]
      · exact getD_congr (by omega)
      all_goals omega
    rw [h.blk j hj]
    by_cases hjc : j < c
    · rw [itp hjc, itp (show j < c + 16 by omega)]
    · rw [itn hjc, itn (show ¬ j < c + 16 by omega)]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide) (by decide), h13,
      Offset.ofNat_sub_ofNat hk]

theorem copy1_step {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t₀ t : State} (hp : Pre P D s)
    {c k : Nat} (hc : c + 1 ≤ rem P s) (h : CInv P s t₀ c t) (h11 : t.gpr .x11 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) :
    WP isa (.block copy1) t fun t' => CInv P s t₀ (c + 1) t' ∧ t'.gpr .x11 = BitVec.ofNat 64 (k - 1) := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N
  have hwr := whl_rem P s; have hlen := len_lt s
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  have hm := h.mid
  unfold copy1
  refine wp_ldrb (a := dp s + BitVec.ofNat 64 (whl P s + c)) (by decide) (by rw [h.x27]; simp)
    ⟨dR s, by rw [hm.rd, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩ fun t₁ u₁ => ?_
  refine wp_strb (a := buf P s + BitVec.ofNat 64 c) (by decide)
    (by rw [u₁.other _ (by decide), h.x12]; simp)
    ⟨fR P s, by rw [u₁.wr, hm.wr]; simp, by rw [buf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
    fun t₂ m₂ => ?_
  refine wp_addImm (by decide) fun t₃ u₃ => wp_addImm (by decide) fun t₄ u₄ =>
    wp_subImm (by decide) fun t₅ u₅ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .x9 → t₂.gpr r = t.gpr r := fun r h9 => by rw [m₂.gpr, u₁.other _ h9]
  have mem₅ : t₅.mem = t₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have fr₂ : Frame [bR P s] t.mem t₂.mem := by
    rw [m₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by rw [buf_add]; exact Offset.contains _ (by omega) (by omega) (by omega))
  refine ⟨⟨Mid.of_frame hm (by rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr])
      (by rw [u₅.sp, u₄.sp, u₃.sp, m₂.sp, u₁.sp])
      (fun r hr => by
        rw [u₅.other _ (mid_ne r hr _ (by decide)), u₄.other _ (mid_ne r hr _ (by decide)),
          u₃.other _ (mid_ne r hr _ (by decide)), g₂ _ (mid_ne r hr _ (by decide))])
      (by rw [mem₅]; exact fr₂)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., b_sub s⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr
                      exact (st_sl hF s).symm.sub_right (Offset.sub_base _ (by omega)) |>.symm |>.symm),
    by omega, ?_, ?_, ?_, by rw [mem₅]; exact h.frame.trans fr₂, fun j hj => ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide), h.x27, add_ofNat, Nat.add_assoc]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide), h.x12, add_ofNat]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), h.x28]
  · simp only [mem₅, m₂.mem, u₁.gpr, u₁.mem, buf_add]
    rw [writeW8_off _ _ _ (by omega) (by omega)]
    split
    · rw [itp (show j < c + 1 by omega), data_eq hp hm (by omega), msg_getD s (by omega)]
      rw [show c = j by omega]
      ext i hi; simp
    rw [h.blk j hj]
    by_cases hjc : j < c
    · rw [itp hjc, itp (show j < c + 1 by omega)]
    · rw [itn hjc, itn (show ¬ j < c + 1 by omega)]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), h11, Offset.ofNat_sub_ofNat hk]

/-- The block holds the bytes left, `0x80`, then zeros. -/
def Blk80 (P : Params) (s : State) (m : Mem) : Prop :=
  ∀ j < P.B, m (fb P s + BitVec.ofNat 64 (P.N + j)) =
    if j < rem P s then (msg s).getD (whl P s + j) 0 else if j = rem P s then 0x80 else 0

theorem and15 (x : BitVec 64) :
    x &&& BitVec.setWidth 64 (15 : BitVec 16) = BitVec.ofNat 64 (x.toNat % 16) := by
  simpa using and_mask (n := 4) (by omega) x

/-- What the end of `copyTail` leaves, from the state `t₀`. -/
abbrev TailPost (P : Params) (s t₀ t : State) : Prop :=
  Mid P s t ∧ t.gpr .x28 = BitVec.ofNat 64 (rem P s) ∧ Frame [bR P s] t₀.mem t.mem ∧ Blk80 P s t.mem

/-- A write of a register other than those `CInv` describes keeps it. -/
theorem CInv.upd {P : Params} {s t₀ t t' : State} {c : Nat} {d : Reg} {v : BitVec 64} (h : CInv P s t₀ c t)
    (u : Upd t t' d v) (hm : ∀ r ∈ midRegs, r ≠ d) (h27 : d ≠ .x27) (h12 : d ≠ .x12) (h28 : d ≠ .x28) :
    CInv P s t₀ c t' :=
  ⟨Mid.of_frame h.mid u.rd u.wr u.sp (fun r hr => u.other r (hm r hr)) (rs := [])
      (fun x _ => by rw [u.mem]) (fun _ hr => absurd hr List.not_mem_nil) (fun _ hr => absurd hr List.not_mem_nil),
    h.c_le, by rw [u.other _ (Ne.symm h27), h.x27], by rw [u.other _ (Ne.symm h12), h.x12],
    by rw [u.other _ (Ne.symm h28), h.x28], by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.blk⟩

/-- Every byte left copied: then the `0x80` byte. -/
theorem mark1_ok {P : Params} (hF : Fits P) (hd : Dims P) {s t₀ t : State} (h : CInv P s t₀ (rem P s) t) :
    WP isa (.block [.movz .x .x9 0x80 0, .strb .x9 .x12 0]) t (TailPost P s t₀) := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  have hm₇ := h.mid
  refine wp_movz fun t₈ u₈ => wp_strb (a := buf P s + BitVec.ofNat 64 (rem P s)) (by decide)
    (by rw [u₈.other _ (by decide), h.x12]; simp)
    ⟨fR P s, by rw [u₈.wr, hm₇.wr]; simp, by rw [buf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
    fun t₉ m₉ => WP.block_nil ?_
  have fr₉ : Frame [bR P s] t.mem t₉.mem := by
    rw [m₉.mem, u₈.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by rw [buf_add]; exact Offset.contains _ (by omega) (by omega) (by omega))
  refine ⟨Mid.of_frame hm₇ (by rw [m₉.rd, u₈.rd]) (by rw [m₉.wr, u₈.wr]) (by rw [m₉.sp, u₈.sp])
      (fun r hr => by rw [m₉.gpr, u₈.other _ (mid_ne r hr _ (by decide))]) fr₉
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., b_sub s⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr
                      exact (st_sl hF s).symm.sub_right (Offset.sub_base _ (by omega)) |>.symm |>.symm),
    by rw [m₉.gpr, u₈.other _ (by decide), h.x28], h.frame.trans fr₉, fun j hj => ?_⟩
  simp only [m₉.mem, u₈.mem, u₈.gpr, buf_add]
  rw [writeW8_off _ _ _ (by omega) (by omega)]
  split
  · rw [itn (show ¬ j < rem P s by omega), itp (show j = rem P s by omega)]; rfl
  rw [h.blk j hj]
  by_cases hjc : j < rem P s
  · rw [itp hjc, itp hjc]
  · rw [itn hjc, itn hjc, itn (show ¬ j = rem P s by omega)]

theorem mark_lo : ∀ k < 8, (BitVec.setWidth 64 (0x80 : BitVec 16)).extractLsb' (8 * k) 8 =
    if k = 0 then 0x80 else 0 := by decide

theorem zero_lo (k : Nat) : (BitVec.setWidth 64 (0 : BitVec 16)).extractLsb' (8 * k) 8 = 0 := by simp

/-- The bytes left end at a multiple of 16: `0x80` and 15 zeros, one store. -/
theorem mark16_ok {P : Params} (hF : Fits P) (hd : Dims P) {s t₀ t : State} (h : CInv P s t₀ (rem P s) t) (h16 : rem P s % 16 = 0) :
    WP isa (.block mark16) t (TailPost P s t₀) := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  have hrB : rem P s + 16 ≤ P.B := by rcases hd.B with h | h <;> omega
  have hm := h.mid
  have hout : ∀ o, o + 8 ≤ 16 →
      InRegions t.wr (buf P s + BitVec.ofNat 64 (rem P s) + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨fR P s, by rw [hm.wr]; simp, by
      rw [add_ofNat, buf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  unfold mark16
  refine wp_movz fun t₁ u₁ => wp_movz fun t₂ u₂ => ?_
  refine wp_stpB (b := buf P s + BitVec.ofNat 64 (rem P s)) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.x12])
    (by rw [u₂.wr, u₁.wr]; exact hout 0 (by omega)) (by rw [u₂.wr, u₁.wr]; exact hout 8 (by omega))
    fun t₃ m₃ => WP.block_nil ?_
  have hbc : ∀ o, o + 8 ≤ 16 → (bR P s).Contains (buf P s + BitVec.ofNat 64 (rem P s) + BitVec.ofNat 64 o) (64 / 8) :=
    fun o ho => by rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)
  have fr₃ : Frame [bR P s] t.mem t₃.mem := by
    rw [m₃.mem, u₂.mem, u₁.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hbc 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (hbc 8 (by omega))
  have g₃ : ∀ r, r ≠ .x9 → r ≠ .x10 → t₃.gpr r = t.gpr r := fun r h9 h10 => by
    rw [m₃.gpr, u₂.other _ h10, u₁.other _ h9]
  refine ⟨Mid.of_frame hm (by rw [m₃.rd, u₂.rd, u₁.rd]) (by rw [m₃.wr, u₂.wr, u₁.wr])
      (by rw [m₃.sp, u₂.sp, u₁.sp])
      (fun r hr => g₃ r (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide))) fr₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., b_sub s⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr
                      exact (st_sl hF s).symm.sub_right (Offset.sub_base _ (by omega)) |>.symm |>.symm),
    by rw [g₃ _ (by decide) (by decide), h.x28], h.frame.trans fr₃, fun j hj => ?_⟩
  simp only [m₃.mem, u₂.gpr, u₂.other _ (show Reg.x9 ≠ Reg.x10 by decide), u₁.gpr, u₂.mem, u₁.mem, add_ofNat]
  rw [writeW64_off _ _ _ (by omega) (by omega), writeW64_off _ _ _ (by omega) (by omega)]
  split
  · rw [zero_lo, itn (show ¬ j < rem P s by omega), itn (show ¬ j = rem P s by omega)]
  split
  · rw [mark_lo _ (by omega)]
    rw [itn (show ¬ j < rem P s by omega)]
    by_cases hj0 : j = rem P s
    · rw [itp hj0]; subst hj0; simp
    · rw [itn hj0]
      split
      · exfalso; omega
      · rfl
  rw [h.blk j hj]
  by_cases hjc : j < rem P s
  · rw [itp hjc, itp hjc]
  · rw [itn hjc, itn hjc, itn (show ¬ j = rem P s by omega)]

/-- Fewer than 16 bytes in all: copied a byte at a time, then `0x80`. -/
theorem bytesTail_ok {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t₀ t : State} (hp : Pre P D s)
    (h : CInv P s t₀ (16 * (rem P s / 16)) t) (h11 : t.gpr .x11 = BitVec.ofNat 64 (rem P s % 16))
    (hr0 : rem P s % 16 ≠ 0) :
    WP isa (bytesTail) t (TailPost P s t₀) := by
  have hlen := len_lt s
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  unfold bytesTail
  refine WP.seq (WP.mono (count_loop1 (I := fun i t' => CInv P s t₀ (16 * (rem P s / 16) + i) t') (r := .x11)
      (by omega) hr0
      (fun i hi t' hI h11' => WP.mono (copy1_step hF hd hp (k := rem P s % 16 - i) (by omega) hI h11' (by omega))
        fun t'' ⟨hI'', h11''⟩ => ⟨by rwa [Nat.add_assoc] at hI'', by rw [h11'', Nat.sub_sub]⟩)
      (by rwa [Nat.add_zero]) h11) fun t₇ hI₇ => ?_)
  rw [Nat.div_add_mod] at hI₇
  exact mark1_ok hF hd hI₇

/-- The message's 16 bytes before `len - 16 + 16`, from `data`. -/
theorem src16 (d : Addr) {a r n : Nat} (h : a + r = n) (h16 : 16 ≤ n) (hn : n < 2 ^ 64) :
    d + BitVec.ofNat 64 a + BitVec.ofNat 64 r - BitVec.ofNat 64 16 = d + BitVec.ofNat 64 (n - 16) := by
  apply BitVec.eq_of_toNat_eq
  have := d.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- At least 16 bytes in all, and `r` left beyond a multiple of 16: the last
16 bytes, one store. -/
theorem tail16_ok {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t₀ t : State} (hp : Pre P D s)
    (h : CInv P s t₀ (16 * (rem P s / 16)) t) (h11 : t.gpr .x11 = BitVec.ofNat 64 (rem P s % 16))
    (hr0 : rem P s % 16 ≠ 0) (h16 : 16 ≤ len s) :
    WP isa (.block tail16) t (TailPost P s t₀) := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  have hlen := len_lt s
  have hwr := whl_rem P s
  have hc : 16 * (rem P s / 16) + rem P s % 16 = rem P s := Nat.div_add_mod _ _
  have hcB : 16 * (rem P s / 16) + 16 ≤ P.B := by rcases hd.B with h | h <;> omega
  have hm := h.mid
  refine WP.mono (tail16_run (r := rem P s % 16) (by omega) (Nat.mod_lt _ (by omega)) h11 ?_ ?_)
    fun t' ⟨g', rd', wr', sp', V, m', hV⟩ => ?_
  · rw [h.x27, src16 (dp s) (show whl P s + 16 * (rem P s / 16) + rem P s % 16 = len s by omega) h16 hlen]
    exact ⟨dR s, by rw [hm.rd, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.x12]
    exact ⟨fR P s, by rw [hm.wr]; simp, by rw [buf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have fr : Frame [bR P s] t.mem t'.mem := by
    rw [m', h.x12]
    exact (Frame.refl _ _).write (n := 16) (List.mem_singleton_self _) V
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨Mid.of_frame hm rd' wr' sp'
      (fun r hr => g' r (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide))
        (mid_ne r hr _ (by decide))) fr
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., b_sub s⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr
                      exact (st_sl hF s).symm.sub_right (Offset.sub_base _ (by omega)) |>.symm |>.symm),
    by rw [g' _ (by decide) (by decide) (by decide) (by decide), h.x28], h.frame.trans fr, fun j hj => ?_⟩
  rw [m', h.x12, buf_add, write_off (n := 16) _ _ V (by omega) (by omega)]
  split
  · rename_i hjc
    rw [show V.extractLsb' (8 * (P.N + j - (P.N + 16 * (rem P s / 16)))) 8 =
        vbyte V (j - 16 * (rem P s / 16)) by rw [vbyte, show P.N + j - (P.N + 16 * (rem P s / 16)) =
          j - 16 * (rem P s / 16) by omega], hV _ (by omega)]
    by_cases hjr : j < rem P s
    · rw [itp (show j - 16 * (rem P s / 16) < rem P s % 16 by omega), itp hjr, h.x27, add_ofNat,
        msg_byte hp hm (by omega)]
      exact getD_congr (by omega)
    · rw [itn (show ¬ j - 16 * (rem P s / 16) < rem P s % 16 by omega), itn hjr]
      by_cases hj0 : j = rem P s
      · rw [itp (show j - 16 * (rem P s / 16) = rem P s % 16 by omega), itp hj0]
      · rw [itn (show ¬ j - 16 * (rem P s / 16) = rem P s % 16 by omega), itn hj0]
  · rw [h.blk j hj]
    by_cases hjc : j < 16 * (rem P s / 16)
    · rw [itp hjc, itp (show j < rem P s by omega)]
    · rw [itn hjc, itn (show ¬ j < rem P s by omega), itn (show ¬ j = rem P s by omega)]

theorem copyTail_ok {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t : State} (hp : Pre P D s)
    (h : Mid P s t) (h27 : t.gpr .x27 = dp s + BitVec.ofNat 64 (whl P s)) (h12 : t.gpr .x12 = buf P s)
    (hb : Blk P s 0 t.mem) :
    WP isa (copyTail P) t fun t' => Mid P s t' ∧ t'.gpr .x28 = BitVec.ofNat 64 (rem P s) ∧
      Frame [bR P s] t.mem t'.mem ∧ Blk80 P s t'.mem := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  have hlen := len_lt s
  unfold copyTail
  refine WP.seq (wp_movz fun t₁ u₁ => wp_and fun t₂ u₂ => wp_lsr (by decide) fun t₃ u₃ => WP.block_nil ?_)
  have g₃ : ∀ r, r ≠ .x9 → r ≠ .x28 → r ≠ .x13 → t₃.gpr r = t.gpr r := fun r h9 h28 h13 => by
    rw [u₃.other _ h13, u₂.other _ h28, u₁.other _ h9]
  have h28 : t₃.gpr .x28 = BitVec.ofNat 64 (rem P s) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), u₁.gpr, h.x25, hd.and]
  have mem₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have m₃ : Mid P s t₃ := Mid.of_frame h (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp])
    (fun r hr => g₃ r (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide)))
    (rs := []) (fun x _ => by rw [mem₃]) (fun _ hr => absurd hr List.not_mem_nil)
    (fun _ hr => absurd hr List.not_mem_nil)
  have hI₀ : CInv P s t 0 t₃ :=
    ⟨m₃, Nat.zero_le _, by rw [g₃ _ (by decide) (by decide) (by decide), h27]; simp,
      by rw [g₃ _ (by decide) (by decide) (by decide), h12]; simp, h28, by rw [mem₃]; exact Frame.refl _ _,
      by rw [mem₃]; exact hb⟩
  have h13 : t₃.gpr .x13 = BitVec.ofNat 64 (rem P s / 16) := by
    have h28₂ : t₂.gpr .x28 = BitVec.ofNat 64 (rem P s) := by
      rw [u₂.gpr, u₁.other _ (by decide), u₁.gpr, h.x25, hd.and]
    rw [u₃.gpr, h28₂, ofNat_shr (by omega)]
  refine WP.seq (WP.mono (count_loop (I := fun i t' => CInv P s t (16 * i) t') (r := .x13) (by omega)
      (fun i hi t' hI h13' => WP.mono (copy16_step hF hd hp (k := rem P s / 16 - i) (by omega) hI h13' (by omega))
        fun t'' ⟨hI'', h13''⟩ => ⟨by rwa [show 16 * (i + 1) = 16 * i + 16 by omega], by rw [h13'', Nat.sub_sub]⟩)
      hI₀ h13) fun t₄ hI₄ => ?_)
  refine WP.seq (wp_movz fun t₅ u₅ => wp_and fun t₆ u₆ => WP.block_nil ?_)
  have g₆ : ∀ r, r ≠ .x9 → r ≠ .x11 → t₆.gpr r = t₄.gpr r := fun r h9 h11 => by
    rw [u₆.other _ h11, u₅.other _ h9]
  have mem₆ : t₆.mem = t₄.mem := by rw [u₆.mem, u₅.mem]
  have hI₆ : CInv P s t (16 * (rem P s / 16) + 0) t₆ :=
    ⟨Mid.of_frame hI₄.mid (by rw [u₆.rd, u₅.rd]) (by rw [u₆.wr, u₅.wr]) (by rw [u₆.sp, u₅.sp])
      (fun r hr => g₆ r (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide)))
      (rs := []) (fun x _ => by rw [mem₆]) (fun _ hr => absurd hr List.not_mem_nil)
      (fun _ hr => absurd hr List.not_mem_nil),
     by have := hI₄.c_le; omega, by rw [g₆ _ (by decide) (by decide), hI₄.x27, Nat.add_zero],
     by rw [g₆ _ (by decide) (by decide), hI₄.x12, Nat.add_zero], by rw [g₆ _ (by decide) (by decide), hI₄.x28],
     by rw [mem₆]; exact hI₄.frame, by rw [mem₆, Nat.add_zero]; exact hI₄.blk⟩
  have h11 : t₆.gpr .x11 = BitVec.ofNat 64 (rem P s % 16) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, hI₄.x28, and15, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show rem P s < 2 ^ 64 by omega)]
  have hz11 : eval (.zero .x .x11) t₆ = some (decide (rem P s % 16 = 0)) := by
    rw [eval_zero, h11, ofNat_beq_zero (by omega)]
  rw [Nat.add_zero] at hI₆
  refine WP.ite _ hz11 (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rw [show 16 * (rem P s / 16) = rem P s by omega] at hI₆
    exact mark16_ok hF hd hI₆ hb
  simp only [decide_eq_false_iff_not] at hb
  refine WP.seq (wp_lsr (by decide) fun t₇ u₇ => WP.block_nil ?_)
  have hI₇ := hI₆.upd u₇ (fun r hr => mid_ne r hr _ (by decide)) (by decide) (by decide) (by decide)
  have h11₇ : t₇.gpr .x11 = BitVec.ofNat 64 (rem P s % 16) := by rw [u₇.other _ (by decide), h11]
  have hz9 : eval (.zero .x .x9) t₇ = some (decide (len s / 2 ^ 4 = 0)) := by
    rw [eval_zero, u₇.gpr, hI₆.mid.x25, x1_eq, ofNat_shr hlen, ofNat_beq_zero (by omega)]
  refine WP.ite _ hz9 (fun hb' => bytesTail_ok hF hd hp hI₇ h11₇ hb) (fun hb' => ?_)
  simp only [decide_eq_false_iff_not] at hb'
  exact tail16_ok hF hd hp hI₇ h11₇ hb (by omega)

/-! ## Lists of bytes -/

theorem getD_app (xs ys : List Byte) (k : Nat) :
    (xs ++ ys).getD k 0 = if k < xs.length then xs.getD k 0 else ys.getD (k - xs.length) 0 := by
  by_cases h : k < xs.length
  · rw [itp h, getD_append_left h]
  · rw [itn h]
    have := getD_append_right (p := xs) (q := ys) (j := k - xs.length)
    rwa [show xs.length + (k - xs.length) = k by omega] at this

theorem getD_rep (n k : Nat) : (List.replicate n (0 : Byte)).getD k 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem getD_single (b : Byte) (k : Nat) : [b].getD k 0 = if k = 0 then b else 0 := by
  cases k <;> simp

theorem rest_getD (P : Params) (s : State) {k : Nat} :
    (Md.rest P.B (msg s)).getD k 0 = (msg s).getD (whl P s + k) 0 := by
  simp only [Md.rest, msg_length, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem rest_len (P : Params) (s : State) : (Md.rest P.B (msg s)).length = rem P s := by
  rw [Md.rest_length, msg_length]

/-- Byte `k < B` of the last block, if one: the bytes left, `0x80`, zeros and
the length field `lb`. -/
theorem pad1_getD (P : Params) (s : State) (hr : rem P s + P.L < P.B) {k : Nat} (lb : List Byte)
    (hlb : lb.length = P.L) :
    (Md.rest P.B (msg s) ++ [0x80] ++ List.replicate (P.B - P.L - 1 - rem P s) 0 ++ lb).getD k 0 =
      if k < P.B - P.L then
        (if k < rem P s then (msg s).getD (whl P s + k) 0 else if k = rem P s then 0x80 else 0)
      else lb.getD (k - (P.B - P.L)) 0 := by
  simp only [getD_app, List.length_append, rest_len, List.length_singleton, List.length_replicate,
    getD_single, getD_rep, rest_getD]
  by_cases h1 : k < rem P s
  · rw [itp (show k < rem P s + 1 + (P.B - P.L - 1 - rem P s) by omega), itp (show k < rem P s + 1 by omega),
      itp h1, itp (show k < P.B - P.L by omega), itp h1]
  by_cases h2 : k = rem P s
  · subst h2
    rw [itp (show rem P s < rem P s + 1 + (P.B - P.L - 1 - rem P s) by omega), itp (show rem P s < rem P s + 1 by omega),
      itn h1, itp (show rem P s - rem P s = 0 by omega), itp (show rem P s < P.B - P.L by omega), itn h1, itp rfl]
  by_cases h3 : k < P.B - P.L
  · rw [itp (show k < rem P s + 1 + (P.B - P.L - 1 - rem P s) by omega), itn (show ¬ k < rem P s + 1 by omega),
      itp h3, itn h1, itn h2]
  · rw [itn (show ¬ k < rem P s + 1 + (P.B - P.L - 1 - rem P s) by omega), itn h3,
      show k - (rem P s + 1 + (P.B - P.L - 1 - rem P s)) = k - (P.B - P.L) by omega]

/-- Byte `k < B` of the first of two last blocks. -/
theorem pad2a_getD (P : Params) (s : State) {k : Nat} :
    (Md.rest P.B (msg s) ++ [0x80] ++ List.replicate (P.B - 1 - rem P s) 0).getD k 0 =
      if k < rem P s then (msg s).getD (whl P s + k) 0 else if k = rem P s then 0x80 else 0 := by
  simp only [getD_app, List.length_append, rest_len, List.length_singleton, getD_single, getD_rep, rest_getD]
  by_cases h1 : k < rem P s
  · rw [itp (show k < rem P s + 1 by omega), itp h1, itp h1]
  by_cases h2 : k = rem P s
  · subst h2; rw [itp (show rem P s < rem P s + 1 by omega), itn h1, itp (show rem P s - rem P s = 0 by omega), itn h1, itp rfl]
  · rw [itn (show ¬ k < rem P s + 1 by omega), itn h1, itn h2]

/-- Byte `k` of the second of two last blocks. -/
theorem pad2b_getD (P : Params) {k : Nat} (lb : List Byte) :
    (List.replicate (P.B - P.L) 0 ++ lb).getD k 0 = if k < P.B - P.L then 0 else lb.getD (k - (P.B - P.L)) 0 := by
  simp only [getD_app, List.length_replicate, getD_rep]

/-! ## Compressing the block -/

theorem stateAt_bframe {P : Params} {H : Md P.B P.N P.L} (hF : Fits P) {s : State} {m m' : Mem}
    (hf : Frame [bR P s] m m') : H.stateAt m' (fb P s) = H.stateAt m (fb P s) :=
  H.stateAt_congr fun i hi => hf.bytes (R := hR P s)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h_b hF s)
    (by have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; show P.N ≤ 2 ^ 64; omega) hi

theorem compressBuf_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {name : String}
    {code : Prog isa} (hf : CalleeOk H code) {s t : State} (h : Mid P s t) {Q : State → Prop}
    (hQ : ∀ t', Mid P s t' → t'.gpr .x28 = t.gpr .x28 →
      H.stateAt t'.mem (fb P s) = H.compress (H.stateAt t.mem (fb P s)) (H.blockAt t.mem (buf P s)) → Q t') :
    WP isa (compressBuf P name code) t Q := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N
  unfold compressBuf Impl.MdStream.AArch64.OneShot.compressWith
  refine WP.seq (wp_addSp (by omega) fun t₁ u₁ => wp_addSp (by omega) fun t₂ u₂ => wp_movz fun t₃ u₃ =>
    wp_addSp (by omega) fun t₄ u₄ => WP.block_nil ?_)
  have mem₄ : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have sp₄ : t₄.sp = t.sp := by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have hk : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → t₄.gpr r = t.gpr r := fun r h0 h1 h2 h3 => by
    rw [u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  have m₄ : Mid P s t₄ := Mid.of_frame h (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    sp₄ (fun r hr => hk r (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide))
      (mid_ne r hr _ (by decide)))
    (rs := []) (fun x _ => by rw [mem₄]) (fun _ hr => absurd hr List.not_mem_nil)
    (fun _ hr => absurd hr List.not_mem_nil)
  have g0 : t₄.gpr .x0 = fb P s := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.sp]; simp
  have g1 : t₄.gpr .x1 = buf P s := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.sp, h.sp]
  have g2 : (t₄.gpr .x2).toNat = 1 := by rw [u₄.other _ (by decide), u₃.gpr]; rfl
  have g3 : t₄.gpr .x3 = fb P s + BitVec.ofNat 64 (scO P) := by rw [u₄.gpr, u₃.sp, u₂.sp, u₁.sp, h.sp]
  refine call_ok hf g0 g1 g2 g3 (h_sc hF s) (by rw [Nat.mul_one]; exact (h_b hF s).symm)
    (by rw [Nat.mul_one]; exact b_sc hF s) ?_ ?_ fun t₅ hrd hwr hcs hsp hf' hst => ?_
  · rw [m₄.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fR P s, by simp, P.N, rfl, show P.N + P.B * 1 ≤ frameBytes P by omega⟩
    · exact ⟨fR P s, by simp, 0, fb_zero P s, show 0 + P.N ≤ frameBytes P by omega⟩
    · exact ⟨fR P s, by simp, scO P, rfl, show scO P + P.so ≤ frameBytes P by omega⟩
  · exact covers_frame s m₄.wr fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, fb_zero P s, show 0 + P.N ≤ frameBytes P by omega⟩
      · exact ⟨scO P, rfl, show scO P + P.so ≤ frameBytes P by omega⟩
  refine hQ t₅ (call_mid hF m₄ hrd hwr hcs hsp hf') ?_ ?_
  · rw [hcs _ (by decide) (by decide), hk _ (by decide) (by decide) (by decide) (by decide)]
  · rw [hst, Md.compressBlocks_one, mem₄]

/-! ## The length field and the last compression -/

/-- Before the length field: the digest follows from the hash value and the
block's first `B - L` bytes. -/
structure Last {P : Params} (H : Md P.B P.N P.L) (iv : H.HV) (s t : State) : Prop where
  mid : Mid P s t
  hash : H.lenOk (len s) → H.hash iv (msg s) = H.digest (H.compress (H.stateAt t.mem (fb P s))
    (H.parse fun j => if j < P.B - P.L then t.mem (fb P s + BitVec.ofNat 64 (P.N + j))
      else (H.lenBytes (len s)).getD (j - (P.B - P.L)) 0))

/-- Writing back what was read leaves memory as it was. -/
theorem write_read_self (m : Mem) (a : Addr) (n : Nat) : m.write a n (m.read a n) = m := by
  funext x
  simp only [Mem.write]
  split
  · rename_i h
    rw [Mem.extractLsb'_read _ _ h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm,
      BitVec.sub_add_cancel]
  · rfl

theorem writeW_readW_self (m : Mem) (a : Addr) : m.writeW a (m.readW a 64) = m := by
  simp only [Mem.writeW, Mem.readW, BitVec.setWidth_eq]
  exact write_read_self m a 8

/-- `lenStore`: the block's last 16 bytes, stored again as they are. -/
theorem lenStore_ok {P : Params} (hF : Fits P) (hd : Dims P) {s t : State} (h : Mid P s t) :
    WP isa (.block (lenStore P)) t fun t' => Mid P s t' ∧ t'.mem = t.mem := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N
  have hB16 : 16 ≤ P.B := by rcases hd.B with h | h <;> omega
  unfold lenStore
  refine wp_addSp (by omega) fun t₁ u₁ => ?_
  generalize hb : fb P s + BitVec.ofNat 64 (P.N + P.B - 16) = b
  have h12 : t₁.gpr .x12 = b := by rw [u₁.gpr, h.sp, ← hb]
  have hc : ∀ o, o + 8 ≤ 16 → (fR P s).Contains (b + BitVec.ofNat 64 o) 8 := fun o ho => by
    rw [← hb, add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)
  have hin : ∀ o, o + 8 ≤ 16 → InRegions (t₁.rd ++ t₁.wr) (b + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨fR P s, by rw [u₁.wr, h.wr]; simp, hc o ho⟩
  refine wp_ldr (a := b + BitVec.ofNat 64 0) (by decide) (by rw [h12]) (hin 0 (by omega)) fun t₂ u₂ => ?_
  refine wp_ldr (a := b + BitVec.ofNat 64 8) (by decide) (by rw [u₂.other _ (by decide), h12])
    (by rw [u₂.rd, u₂.wr]; exact hin 8 (by omega)) fun t₃ u₃ => ?_
  refine wp_stpB (b := b) (by decide) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), h12])
    ⟨fR P s, by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; simp, hc 0 (by omega)⟩
    ⟨fR P s, by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; simp, hc 8 (by omega)⟩ fun t₄ m₄ => WP.block_nil ?_
  have mem₄ : t₄.mem = t.mem := by
    rw [m₄.mem, u₃.other _ (by decide), u₂.gpr, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, writeW_readW_self,
      show (0 + 8 : Nat) = 8 from rfl, writeW_readW_self]
  refine ⟨Mid.of_frame h (by rw [m₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [m₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [m₄.sp, u₃.sp, u₂.sp, u₁.sp])
    (fun r hr => by rw [m₄.gpr, u₃.other _ (mid_ne r hr _ (by decide)), u₂.other _ (mid_ne r hr _ (by decide)),
      u₁.other _ (mid_ne r hr _ (by decide))])
    (rs := []) (fun x _ => by rw [mem₄]) (fun _ hr => absurd hr List.not_mem_nil)
    (fun _ hr => absurd hr List.not_mem_nil), mem₄⟩

theorem lenFin_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    {iv : H.HV} {name : String} {code : Prog isa} (hf : CalleeOk H code) {s t : State} (hl : Last H iv s t) :
    WP isa (.seq (.block (([.addSp .x19 0, mov .x22 .x25] : List Instr) ++ P.len ++ lenStore P))
      (compressBuf P name code))
      t fun t' => Mid P s t' ∧ (H.lenOk (len s) → H.hash iv (msg s) = H.digest (H.stateAt t'.mem (fb P s))) := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N; have := hd.L
  have h := hl.mid
  refine WP.seq (wp_addSp (by omega) fun t₁ u₁ => wp_mov fun t₂ u₂ => ?_)
  have h19 : t₂.gpr .x19 = fb P s := by rw [u₂.other _ (by decide), u₁.gpr, h.sp]; simp
  have h22 : t₂.gpr .x22 = BitVec.ofNat 64 (len s) := by
    rw [u₂.gpr, u₁.other _ (by decide), h.x25, x1_eq]
  have hlc : (fR P s).Contains (fb P s + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L :=
    Offset.contains_base _ (by omega) (by omega)
  have hin : InRegions t₂.wr (t₂.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L :=
    ⟨fR P s, by rw [u₂.wr, u₁.wr, h.wr]; simp, by rw [h19]; exact hlc⟩
  simp only [List.append_eq, List.nil_append]
  rw [WP.block_append_iff]
  refine WP.mono (hs.len t₂ hin) fun t₃ ⟨g₃, rd₃, wr₃, sp₃, m₃⟩ => ?_
  rw [h19, h22] at m₃
  have hlb := H.lenOf_length (BitVec.ofNat 64 (len s))
  have fr₃ : Frame [bR P s] t.mem t₃.mem := by
    rw [m₃, u₂.mem, u₁.mem]
    exact writeBytes_frame _ _ _ (by rw [hlb, show P.N + P.B - P.L = P.N + (P.B - P.L) by omega, ← add_ofNat]
                                     exact Offset.contains_base _ (by omega) (by omega))
  have m₃' : Mid P s t₃ := Mid.of_frame h (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
    (by rw [sp₃, u₂.sp, u₁.sp])
    (fun r hr => by
      rw [g₃ _ (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide)), u₂.other _ (mid_ne r hr _ (by decide)),
        u₁.other _ (mid_ne r hr _ (by decide))]) fr₃
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., b_sub s⟩)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr
                    exact (st_sl hF s).symm.sub_right (Offset.sub_base _ (by omega)) |>.symm |>.symm)
  refine WP.mono (lenStore_ok hF hd m₃') fun t₇ ⟨m₇, e₇⟩ => ?_
  refine compressBuf_ok hF hd hf m₇ fun t₄ m₄ _ hst => ⟨m₄, fun hok => ?_⟩
  rw [hst, e₇, stateAt_bframe hF fr₃, hl.hash hok]
  refine congrArg (fun b => H.digest (H.compress _ b)) (H.parse_congr fun k hk => ?_)
  simp only [m₃, u₂.mem, u₁.mem, buf_add, H.lenOf_eq _ hok]
  rw [writeBytes_off _ _ _ (by rw [H.lenBytes_length]; omega) (by omega), H.lenBytes_length]
  by_cases hkl : k < P.B - P.L
  · rw [itp hkl, itn (show ¬ (P.N + P.B - P.L ≤ P.N + k ∧ P.N + k < P.N + P.B - P.L + P.L) by omega)]
  · rw [itn hkl, itp (show P.N + P.B - P.L ≤ P.N + k ∧ P.N + k < P.N + P.B - P.L + P.L by omega),
      show P.N + k - (P.N + P.B - P.L) = k - (P.B - P.L) by omega]

/-! ## The last block or two -/

theorem blockAt_eq {P : Params} {H : Md P.B P.N P.L} (s : State) (m : Mem) {f : Nat → Byte}
    (h : ∀ k < P.B, m (fb P s + BitVec.ofNat 64 (P.N + k)) = f k) : H.blockAt m (buf P s) = H.parse f :=
  H.parse_congr fun k hk => by rw [buf_add]; exact h k hk

theorem tail_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    {iv : H.HV} {name : String} {code : Prog isa} (hf : CalleeOk H code) {s t : State} (hp : Pre P D s)
    (h : Mid P s t) (h27 : t.gpr .x27 = dp s + BitVec.ofNat 64 (whl P s))
    (hw : H.stateAt t.mem (fb P s) = H.compressList iv (msg s) (len s / P.B)) :
    WP isa (tail P name code) t fun t' =>
      Mid P s t' ∧ (H.lenOk (len s) → H.hash iv (msg s) = H.digest (H.stateAt t'.mem (fb P s))) := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N; have := hd.L
  have hB := hd.pos
  have hr : rem P s < P.B := Nat.mod_lt _ hB
  unfold tail
  refine WP.seq (WP.mono (zeroBuf_ok hF hd h) fun t₁ ⟨m₁, g₁, _, h12₁, f₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (copyTail_ok hF hd hp m₁ (by rw [g₁ _ (by decide) (by decide), h27]) h12₁ b₁)
    fun t₂ ⟨m₂, h28₂, f₂, b₂⟩ => ?_)
  have hw₂ : H.stateAt t₂.mem (fb P s) = H.compressList iv (msg s) (len s / P.B) := by
    rw [stateAt_bframe hF f₂, stateAt_bframe hF f₁, hw]
  refine WP.seq (wp_addImm (by omega) fun t₃ u₃ => wp_lsr (by have := hd.log; omega) fun t₄ u₄ => WP.block_nil ?_)
  have h9 : t₄.gpr .x9 = BitVec.ofNat 64 ((rem P s + P.L) / P.B) := by
    rw [u₄.gpr, u₃.gpr, h28₂, ← BitVec.ofNat_add, hd.shr (by omega)]
  have mem₄ : t₄.mem = t₂.mem := by rw [u₄.mem, u₃.mem]
  have m₄ : Mid P s t₄ := Mid.of_frame m₂ (by rw [u₄.rd, u₃.rd]) (by rw [u₄.wr, u₃.wr]) (by rw [u₄.sp, u₃.sp])
    (fun r hr => by rw [u₄.other _ (mid_ne r hr _ (by decide)), u₃.other _ (mid_ne r hr _ (by decide))])
    (rs := []) (fun x _ => by rw [mem₄]) (fun _ hr => absurd hr List.not_mem_nil)
    (fun _ hr => absurd hr List.not_mem_nil)
  have hz : eval (.zero .x .x9) t₄ = some (decide ((rem P s + P.L) / P.B = 0)) := by
    have := Nat.div_le_self (rem P s + P.L) P.B
    rw [eval_zero, h9, ofNat_beq_zero (by omega)]
  have hlen : (msg s).length % P.B = rem P s := by rw [msg_length]
  refine WP.seq (WP.mono (Q := Last H iv s) (WP.ite _ hz (fun hb => ?_) (fun hb => ?_))
    fun t₅ hl => lenFin_ok hF hd hs hf hl)
  · -- One block.
    simp only [decide_eq_true_eq] at hb
    have hr1 : rem P s + P.L < P.B := by
      rcases Nat.lt_or_ge (rem P s + P.L) P.B with h | h
      · exact h
      · exact absurd hb (Nat.pos_iff_ne_zero.mp (Nat.div_pos h hB))
    refine WP.block_nil ⟨m₄, fun hok => ?_⟩
    rw [H.hash_one hB (by rw [hlen]; exact hr1), hlen, msg_length, mem₄, hw₂]
    refine congrArg H.digest (congrArg (H.compress _) (H.parse_congr fun k hk => ?_))
    rw [pad1_getD P s hr1 _ (H.lenBytes_length _)]
    by_cases hkl : k < P.B - P.L
    · rw [itp hkl, itp hkl, b₂ k hk]
    · rw [itn hkl, itn hkl]
  · -- Two blocks.
    simp only [decide_eq_false_iff_not] at hb
    have hr2 : P.B ≤ rem P s + P.L := by
      rcases Nat.lt_or_ge (rem P s + P.L) P.B with h | h
      · exact absurd (Nat.div_eq_of_lt h) hb
      · exact h
    refine WP.seq (compressBuf_ok hF hd hf m₄ fun t₅ m₅ _ hst₅ => ?_)
    refine WP.mono (zeroBuf_ok hF hd m₅) fun t₆ ⟨m₆, _, _, _, f₆, b₆⟩ => ⟨m₆, fun hok => ?_⟩
    rw [H.hash_two hB (by omega) (by rw [hlen]; exact hr2), hlen, msg_length, stateAt_bframe hF f₆, hst₅, mem₄,
      hw₂, blockAt_eq (H := H) s t₂.mem (f := fun t => (Md.rest P.B (msg s) ++ [0x80] ++
        List.replicate (P.B - 1 - rem P s) 0).getD t 0) fun k hk => by rw [b₂ k hk, pad2a_getD]]
    refine congrArg H.digest (congrArg (H.compress _) (H.parse_congr fun k hk => ?_))
    rw [pad2b_getD]
    by_cases hkl : k < P.B - P.L
    · rw [itp hkl, itp hkl, b₆ k hk]; rfl
    · rw [itn hkl, itn hkl]

/-! ## The digest, zeroing the frame and restoring the registers -/

/-- `n` pairs of zero doublewords at `p`, through the base register `b` and
the zero register `z`: memory changes only there. -/
theorem stps_ok {b z : Reg} {p : Addr} (n : Nat) {t : State} (hb : t.gpr b = p)
    (hin : ∀ o, o + 8 ≤ 16 * n → InRegions t.wr (p + BitVec.ofNat 64 o) 8) (hn : 16 * n ≤ 512) :
    WP isa (.block ((List.range n).map fun k => .stp z z b (16 * k))) t fun t' =>
      t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧ Frame [⟨p, 16 * n⟩] t.mem t'.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (fun o ho => hin o (by omega)) (by omega)) fun t₁ ⟨g₁, rd₁, wr₁, sp₁, f₁⟩ => ?_
    refine wp_stpB (by omega) (by rw [g₁, hb]) (by rw [wr₁]; exact hin _ (by omega))
      (by rw [wr₁]; exact hin _ (by omega)) fun t₂ m₂ => WP.block_nil ?_
    have hc : ∀ o, o + 8 ≤ 16 * (n + 1) → (⟨p, 16 * (n + 1)⟩ : Region).Contains (p + BitVec.ofNat 64 o) (64 / 8) :=
      fun o ho => Offset.contains_base _ ho (by omega)
    refine ⟨by rw [m₂.gpr, g₁], by rw [m₂.rd, rd₁], by rw [m₂.wr, wr₁], by rw [m₂.sp, sp₁], ?_⟩
    rw [m₂.mem]
    have f₁' : Frame [⟨p, 16 * (n + 1)⟩] t.mem t₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    exact (f₁'.writeW (List.mem_singleton_self _) _ (hc _ (by omega))).writeW
      (List.mem_singleton_self _) _ (hc _ (by omega))

theorem slot_rd {P : Params} (s : State) {t : State} (hwr : t.wr = fR P s :: s.wr) {j : Nat} (hj : j ≤ 56)
    (hlt : frameBytes P < 4096) :
    InRegions (t.rd ++ t.wr) (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 j) 8 :=
  ⟨fR P s, by rw [hwr]; simp, by
    have := sl_le P
    rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem finish_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    {iv : H.HV} {s t : State} (hp : Pre P D s) (h : Mid P s t)
    (hh : H.lenOk (len s) → H.hash iv (msg s) = H.digest (H.stateAt t.mem (fb P s))) :
    WP isa (.block (finish P)) t fun t' =>
      t'.rd = s.rd ∧ t'.wr = fR P s :: s.wr ∧ t'.sp = fb P s ∧ (∀ r ∈ preserved, t'.gpr r = s.gpr r) ∧
      (H.lenOk (len s) → bytesAt t'.mem (out s) D = (H.hash iv (msg s)).take D) := by
  have := hF.lt; have := sl_le P; have := sc_le P; have := st_le P; have := hd.B; have := hd.N
  have hDN := hs.le
  simp only [finish]
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine wp_addSp (by omega_arith) fun t₁ u₁ => wp_mov fun t₂ u₂ => WP.block_nil ?_
  have h19 : t₂.gpr .x19 = fb P s := by rw [u₂.other _ (by decide), u₁.gpr, h.sp]; simp
  have h21 : t₂.gpr .x21 = out s := by rw [u₂.gpr, u₁.other _ (by decide), h.x26]
  have wr₂ : t₂.wr = fR P s :: s.wr := by rw [u₂.wr, u₁.wr, h.wr]
  have rd₂ : t₂.rd = s.rd := by rw [u₂.rd, u₁.rd, h.rd]
  refine WP.mono (hs.out t₂ ⟨fR P s, by rw [rd₂, wr₂]; simp, by
      rw [h19]; simpa using Offset.contains_base (fb P s) (d := 0) (n := P.N) (k := frameBytes P)
        (by omega_arith) (by omega_arith)⟩
    ⟨oR s D, by rw [wr₂, hp.wr]; simp, by rw [h21]; exact Region.contains_self _ _⟩
    (by rw [h19, h21]; exact hp.f_o.sub_left (h_sub s))) fun t₃ ⟨g₃, rd₃, wr₃, sp₃, m₃⟩ => ?_
  rw [h19, h21] at m₃
  simp only [wipe, List.cons_append, List.nil_append]
  refine wp_addSp (by omega_arith) fun t₄ u₄ => wp_movz fun t₅ u₅ => ?_
  have h16 : t₅.gpr .x16 = fb P s := by rw [u₅.other _ (by decide), u₄.gpr, sp₃, u₂.sp, u₁.sp, h.sp]; simp
  have wr₅ : t₅.wr = fR P s :: s.wr := by rw [u₅.wr, u₄.wr, wr₃, wr₂]
  have hw16 : 16 * ((P.N + P.B + 15) / 16) = scO P := by simp only [scO]; omega_arith
  refine WP.mono (stps_ok (b := .x16) (z := .x17) (p := fb P s) ((P.N + P.B + 15) / 16) h16
      (fun o ho => ⟨fR P s, by rw [wr₅]; simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) (by omega_arith))
    fun t₆ ⟨g₆, rd₆, wr₆, sp₆, f₆⟩ => ?_
  -- What the digest and the wipe leave of `t`'s memory.
  have hdl : ((H.digest (H.stateAt t₂.mem (fb P s))).take D).length = D := by
    rw [List.length_take, H.digest_length]; exact Nat.min_eq_left hDN
  have fo : Frame [oR s D] t.mem t₃.mem := by
    rw [m₃, u₂.mem, u₁.mem]
    exact writeBytes_frame _ _ _ (by
      rw [List.length_take, H.digest_length, Nat.min_eq_left hDN]; exact Region.contains_self _ _)
  have fw : Frame [⟨fb P s, 16 * ((P.N + P.B + 15) / 16)⟩] t₃.mem t₆.mem := by rwa [u₅.mem, u₄.mem] at f₆
  have hwsl : (slR P s).Disjoint ⟨fb P s, 16 * ((P.N + P.B + 15) / 16)⟩ := by
    rw [hw16]; exact (Offset.base_disjoint (fb P s) (k := scO P) (e := slO P) (n := 64) (by have := sc_le P; omega_arith) (by omega_arith)).symm
  have hsl : Slots P s t₆.mem := fun q hq => by
    rw [← h.slots q hq]
    have hc := slot_contains (P := P) s (saves_le q hq)
    rw [fw.readW hc (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hwsl) (by decide)]
    exact fo.readW hc (fun r hr => by simp only [List.mem_singleton] at hr; subst hr
                                      exact hp.f_o.sub_left (sl_sub s)) (by decide)
  simp only [OneShot.restore]
  refine wp_addSp (by omega_arith) fun t₇ u₇ => ?_
  have h16₇ : t₇.gpr .x16 = fb P s + BitVec.ofNat 64 (slO P) := by
    rw [u₇.gpr, sp₆, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp, h.sp]
  have wr₇ : t₇.wr = fR P s :: s.wr := by rw [u₇.wr, wr₆, wr₅]
  refine wp_ldpB (by decide) (by decide) h16₇ (slot_rd s wr₇ (by omega_arith) hF.lt) (slot_rd s wr₇ (by omega_arith) hF.lt)
    fun t₈ u₈ => ?_
  refine wp_ldpB (by decide) (by decide) (by rw [u₈.other _ (by decide) (by decide), h16₇])
    (by rw [u₈.rd, u₈.wr]; exact slot_rd s wr₇ (by omega_arith) hF.lt)
    (by rw [u₈.rd, u₈.wr]; exact slot_rd s wr₇ (by omega_arith) hF.lt) fun t₉ u₉ => ?_
  refine wp_ldpB (by decide) (by decide)
    (by rw [u₉.other _ (by decide) (by decide), u₈.other _ (by decide) (by decide), h16₇])
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr]; exact slot_rd s wr₇ (by omega_arith) hF.lt)
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr]; exact slot_rd s wr₇ (by omega_arith) hF.lt) fun t₁₀ u₁₀ => ?_
  refine wp_ldpB (by decide) (by decide)
    (by rw [u₁₀.other _ (by decide) (by decide), u₉.other _ (by decide) (by decide),
      u₈.other _ (by decide) (by decide), h16₇])
    (by rw [u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr]; exact slot_rd s wr₇ (by omega_arith) hF.lt)
    (by rw [u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr]; exact slot_rd s wr₇ (by omega_arith) hF.lt)
    fun t₁₁ u₁₁ => WP.block_nil ?_
  have mem₁₁ : t₁₁.mem = t₆.mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  have sl : ∀ q ∈ saves, t₆.mem.readW (fb P s + BitVec.ofNat 64 (slO P) + BitVec.ofNat 64 q.2) 64 = s.gpr q.1 :=
    hsl
  refine ⟨by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, u₅.rd, u₄.rd, rd₃, rd₂],
    by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇],
    by rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, sp₆, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp, h.sp], fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₁₁.other _ (by decide) (by decide), u₁₀.other _ (by decide) (by decide),
        u₉.other _ (by decide) (by decide), u₈.gpr₁, u₇.mem, sl (.x19, 0) (by decide)]
    · rw [u₁₁.other _ (by decide) (by decide), u₁₀.other _ (by decide) (by decide),
        u₉.other _ (by decide) (by decide), u₈.other _ (by decide) (by decide), u₇.other _ (by decide), g₆,
        u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.keep _ (by decide)]
    · rw [u₁₁.other _ (by decide) (by decide), u₁₀.other _ (by decide) (by decide),
        u₉.other _ (by decide) (by decide), u₈.gpr₂, u₇.mem, sl (.x21, 8) (by decide)]
    · rw [u₁₁.other _ (by decide) (by decide), u₁₀.other _ (by decide) (by decide),
        u₉.gpr₁, u₈.mem, u₇.mem, sl (.x22, 16) (by decide)]
    · rw [u₁₁.other _ (by decide) (by decide), u₁₀.other _ (by decide) (by decide),
        u₉.other _ (by decide) (by decide), u₈.other _ (by decide) (by decide), u₇.other _ (by decide), g₆,
        u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.keep _ (by decide)]
    · rw [u₁₁.other _ (by decide) (by decide), u₁₀.other _ (by decide) (by decide),
        u₉.other _ (by decide) (by decide), u₈.other _ (by decide) (by decide), u₇.other _ (by decide), g₆,
        u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.keep _ (by decide)]
    · rw [u₁₁.other _ (by decide) (by decide), u₁₀.other _ (by decide) (by decide),
        u₉.gpr₂, u₈.mem, u₇.mem, sl (.x25, 24) (by decide)]
    · rw [u₁₁.other _ (by decide) (by decide), u₁₀.gpr₁, u₉.mem, u₈.mem, u₇.mem, sl (.x26, 32) (by decide)]
    · rw [u₁₁.other _ (by decide) (by decide), u₁₀.gpr₂, u₉.mem, u₈.mem, u₇.mem, sl (.x27, 40) (by decide)]
    · rw [u₁₁.gpr₁, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, sl (.x28, 48) (by decide)]
    · rw [u₁₁.gpr₂, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, sl (.x30, 56) (by decide)]
  · intro hok
    have hD : D < 2 ^ 64 := by omega_arith
    have e := bytesAt_writeBytes t₂.mem (out s) 0 ((H.digest (H.stateAt t₂.mem (fb P s))).take D) (by omega_arith)
    rw [hdl, show out s + BitVec.ofNat 64 0 = out s by simp, Nat.zero_add,
      show bytesAt t₂.mem (out s) 0 = [] from rfl, List.nil_append] at e
    have hout : bytesAt t₁₁.mem (out s) D = bytesAt t₃.mem (out s) D := by
      rw [mem₁₁]
      refine bytesAt_congr fun i hi => fw.bytes (R := oR s D) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.f_o.sub_left (Region.sub_prefix (by omega_arith))).symm) (show D ≤ 2 ^ 64 by omega_arith) hi
    rw [hout, m₃, e, hh hok, u₂.mem, u₁.mem]

/-! ## The digest -/

theorem frameBytes_ok {P : Params} (hF : Fits P) :
    0 < frameBytes P ∧ frameBytes P < 4096 ∧ frameBytes P % 16 = 0 :=
  ⟨by have := sl_le P; omega, hF.lt, by simp [frameBytes, Nat.mul_mod_left]⟩

/-- The one-shot digest is correct, given that `init` stores `iv`, writing
only `x9` and `x10`. -/
theorem correct {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    {iv : H.HV} {init : Prog isa} {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hi : ∀ s, (initK H iv).pre s → ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ (initK H iv).post s s')
    (hiw : ∀ r, r ≠ .x9 → r ≠ .x10 → ∀ i ∈ instrs init, clobbers i r = false) (hin : init.noCalls = true)
    (hv : (digest P init name code).allInstrs keepsV = true) {s : State} (hp : Pre P D s) :
    WP isa (digest P init name code) s fun s' => abiPreserved s s' ∧ (oneK H iv D).post s s' := by
  apply WP.withPreservedV (hc := hv)
  refine WP.alloc (frameBytes_ok hF) hp.sp ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok hF rfl) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (init_ok hF hi hiw hin h₁) fun t₂ ⟨m₂, g27, hiv⟩ => ?_)
  refine WP.seq (WP.mono (whole_ok hF hd hf hp m₂ g27 hiv) fun t₃ ⟨m₃, h27, hw⟩ => ?_)
  refine WP.seq (WP.mono (tail_ok hF hd hs hf hp m₃ h27 hw) fun t₄ ⟨m₄, hh⟩ => ?_)
  refine WP.mono (finish_ok hF hd hs hp m₄ hh) fun t₅ ⟨_, _, hsp, hg, hb⟩ => ?_
  exact ⟨⟨fun r hr => hg r hr, by simp only [freed, hsp, fb, BitVec.sub_add_cancel]⟩, hb⟩

/-- The one-shot digest writes no vector register if `init` and the
compression function do not. -/
theorem digest_keepsV {P : Params} {H : Md P.B P.N P.L} {D : Nat} (hs : ShapeD H D) {init : Prog isa}
    {name : String} {code : Prog isa}
    (hi : init.allInstrs VG.AArch64.keepsV = true) (h : code.allInstrs VG.AArch64.keepsV = true) :
    (digest P init name code).allInstrs VG.AArch64.keepsV = true := by
  have hl := List.all_eq_true.mp hs.lenKeepsV
  have ho := List.all_eq_true.mp hs.outKeepsV
  rw [Code.allInstrs_eq] at h hi ⊢
  have hc := List.all_eq_true.mp h
  have hii := List.all_eq_true.mp hi
  simp [digest, body, setup, whole, tail, copyTail, copy16, copy1, zeroBuf, compressBuf, mark16, tail16,
    bytesTail, lenStore, Impl.Tbl.AArch64.const128, Impl.Tbl.AArch64.const64,
    Impl.MdStream.AArch64.OneShot.compressWith, finish, wipe, OneShot.restore, instrs, lg, mov,
    VG.AArch64.keepsV, vdstOf, VOp.dst]
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    first
    | simpa [VG.AArch64.keepsV, vdstOf, VOp.dst] using hii x hx
    | simpa [VG.AArch64.keepsV, vdstOf, VOp.dst] using hc x hx
    | simpa [VG.AArch64.keepsV, vdstOf, VOp.dst] using hl x hx
    | simpa [VG.AArch64.keepsV, vdstOf, VOp.dst] using ho x hx

/-- The one-shot digest is verified, given that it is constant time (which
the taint analysis proves of each hash function's code). -/
theorem verified {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    {iv : H.HV} {init : Prog isa} {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hi : ∀ s, (initK H iv).pre s → ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ (initK H iv).post s s')
    (hiw : ∀ r, r ≠ .x9 → r ≠ .x10 → ∀ i ∈ instrs init, clobbers i r = false) (hin : init.noCalls = true)
    (hiv : init.allInstrs VG.AArch64.keepsV = true)
    (hct : ConstantTime isa (oneK H iv D).pre (oneK H iv D).pub (digest P init name code))
    (hsat : ∃ s, Pre P D s) :
    Verified AArch64.target (digest P init name code) (oneK H iv D) := by
  refine ⟨fun s hp => ?_, hct, hsat⟩
  obtain ⟨t, s', he, h⟩ := correct hF hd hs hf hi hiw hin (digest_keepsV hs hiv hf.keepsV) hp
  exact ⟨t, s', he, h⟩

/-- The initial taint agrees on the public arguments. -/
theorem agree₀ {P : Params} {H : Md P.B P.N P.L} {iv : H.HV} {D : Nat} {s₁ s₂ : State}
    (hpub : (oneK H iv D).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2]) s₁ s₂ := by
  obtain ⟨p0, p1, p2, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.MdStream.AArch64.OneShot
