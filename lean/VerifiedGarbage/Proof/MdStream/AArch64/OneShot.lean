module

public import VerifiedGarbage.Proof.MdStream.AArch64.Update
public import VerifiedGarbage.Proof.MdStream.AArch64.Finalize
public import VerifiedGarbage.Impl.MdStream.AArch64.OneShot
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# One-shot Merkle–Damgård digests on AArch64

The functional correctness of `OneShot.digest` (`Impl/MdStream/AArch64/OneShot.lean`),
for any hash function (`Md`), any correct compression function (`CalleeOk`)
and any code `init` storing an initial hash value `iv`: it runs `init`, then
the bodies of the streaming `update` and `finalize`, whose proofs
(`Update.correctMain`, `Finalize.correctMain`) it composes, each on the
regions of its own precondition (`WP.narrow`), in a frame of its own. Constant
time is proven for each hash function's code by the taint analysis, calls
included, as for `update` and `finalize`.
-/

@[expose] public section

namespace VG.Proof.MdStream.AArch64.OneShot

open VG VG.AArch64 VG.Impl.MdStream.AArch64 VG.Impl.MdStream.AArch64.OneShot
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (bytesAt_congr)

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
/-- The streaming state, the scratch space and the saved registers, in the frame. -/
abbrev stR : Region := ⟨fb P s, P.N + P.B⟩
abbrev scR : Region := ⟨fb P s + BitVec.ofNat 64 (scO P), P.so + 48⟩
abbrev slR : Region := ⟨fb P s + BitVec.ofNat 64 (slO P), 24⟩

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

/-- The sizes the frame needs: it fits an immediate, and the state is whole
doublewords. -/
structure Fits (P : Params) : Prop where
  lt : frameBytes P < 4096
  st : (P.N + P.B) % 8 = 0
  sl : slO P % 8 = 0

/-! ## The frame -/

section
variable {P : Params}

theorem Fits.sl_le (hF : Fits P) : slO P + 24 ≤ frameBytes P := by
  have := hF.lt; simp only [frameBytes] at *; omega

theorem sc_le (P : Params) : scO P + P.so + 48 ≤ slO P := by simp [slO]

theorem st_le (P : Params) : P.N + P.B ≤ scO P := by simp [scO]

theorem Fits.so (hF : Fits P) : P.so + 48 + (P.N + P.B) + 24 < 4096 := by
  have := hF.lt; have := hF.sl_le; simp only [slO, scO] at *; omega

variable (hF : Fits P) (s : State)
include hF

theorem st_sc : (stR P s).Disjoint (scR P s) :=
  Offset.base_disjoint _ (st_le P) (by have := hF.so; simp only [scO]; omega)

theorem st_sl : (stR P s).Disjoint (slR P s) :=
  Offset.base_disjoint _ (by have := sc_le P; have := st_le P; omega) (by have := hF.so; simp only [slO, scO]; omega)

theorem sc_sl : (scR P s).Disjoint (slR P s) :=
  Offset.disjoint _ (.inl (sc_le P)) (by have := hF.so; simp only [scO]; omega)
    (by have := hF.so; simp only [slO, scO]; omega)

theorem st_sub : Region.Sub (stR P s) (fR P s) :=
  Region.sub_prefix (by have := sc_le P; have := st_le P; have := hF.sl_le; omega)

theorem sc_sub : Region.Sub (scR P s) (fR P s) :=
  Offset.sub_base _ (by have := sc_le P; have := hF.sl_le; omega)

theorem sl_sub : Region.Sub (slR P s) (fR P s) :=
  Offset.sub_base _ hF.sl_le

end

/-! ## One instruction at a time: `add d, sp, #imm` -/

theorem wp_addSp {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.sp + BitVec.ofNat 64 imm)) (by simp [exec, h]) (k _ (Upd.write64 _ _ _))


/-! ## `setup`: saving `x25`, `x26` and `x30` -/

/-- The saved registers: `x25`, `x26` and `x30` of `s` at `slO`. -/
def Slots (P : Params) (s : State) (m : Mem) : Prop :=
  m.readW (fb P s + BitVec.ofNat 64 (slO P)) 64 = s.gpr .x25 ∧
  m.readW (fb P s + BitVec.ofNat 64 (slO P + 8)) 64 = s.gpr .x26 ∧
  m.readW (fb P s + BitVec.ofNat 64 (slO P + 16)) 64 = s.gpr .x30

/-- The state after `setup`, from `s` (on entry). -/
structure S1 (P : Params) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = fR P s :: s.wr
  sp : t.sp = fb P s
  x0 : t.gpr .x0 = fb P s
  x1 : t.gpr .x1 = s.gpr .x1
  x2 : t.gpr .x2 = dp s
  x3 : t.gpr .x3 = s.gpr .x1
  x25 : t.gpr .x25 = s.gpr .x1
  x26 : t.gpr .x26 = s.gpr .x2
  keep : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → t.gpr r = s.gpr r
  frame : Frame [fR P s] s.mem t.mem
  slots : Slots P s t.mem

theorem slot_in {P : Params} (hF : Fits P) (s : State) {t : State} (hwr : t.wr = fR P s :: s.wr) {j : Nat} (hj : j ≤ 2) :
    InRegions t.wr (fb P s + BitVec.ofNat 64 (slO P + 8 * j)) 8 :=
  ⟨fR P s, by rw [hwr]; exact List.mem_cons_self .., Offset.contains_base _ (by have := hF.sl_le; omega)
    (by have := hF.lt; have := hF.sl_le; omega)⟩

theorem setup_ok {P : Params} (hF : Fits P) {s a : State} (ha : a = allocated (frameBytes P) s) :
    WP isa (.block (setup P)) a (S1 P s) := by
  have hsl := hF.sl_le; have hlt := hF.lt; have h8 := hF.sl
  subst ha
  have hfb : (allocated (frameBytes P) s).sp + BitVec.ofNat 64 0 = fb P s := by
    simp [allocated]
  have hwr : (allocated (frameBytes P) s).wr = fR P s :: s.wr := rfl
  simp only [setup]
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  have h10 : s₁.gpr .x10 = fb P s := u₁.gpr.trans hfb
  refine wp_str (a := fb P s + BitVec.ofNat 64 (slO P)) (by omega) (by rw [h10])
    (by have := slot_in hF s (t := s₁) (u₁.wr.trans hwr) (j := 0) (by omega); simpa using this) fun s₂ m₂ => ?_
  refine wp_str (a := fb P s + BitVec.ofNat 64 (slO P + 8)) (by omega) (by rw [m₂.gpr, h10])
    (by rw [m₂.wr]; exact slot_in hF s (t := s₁) (u₁.wr.trans hwr) (j := 1) (by omega)) fun s₃ m₃ => ?_
  refine wp_str (a := fb P s + BitVec.ofNat 64 (slO P + 16)) (by omega) (by rw [m₃.gpr, m₂.gpr, h10])
    (by rw [m₃.wr, m₂.wr]; exact slot_in hF s (t := s₁) (u₁.wr.trans hwr) (j := 2) (by omega)) fun s₄ m₄ => ?_
  refine wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_mov fun s₈ u₈ =>
    wp_addSp (by decide) fun s₉ u₉ => WP.block_nil ?_
  -- Registers of `s₄` are those of `s` but `x10`.
  have g₄ : ∀ r, r ≠ .x10 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [m₄.gpr, m₃.gpr, m₂.gpr, u₁.other r hr]; rfl
  have sp₉ : s₉.sp = fb P s := by
    rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, m₄.sp, m₃.sp, m₂.sp, u₁.sp]; rfl
  have mem₉ : s₉.mem = s₄.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  have mem₄ : s₄.mem = ((s.mem.writeW (fb P s + BitVec.ofNat 64 (slO P)) (s.gpr .x25)).writeW
      (fb P s + BitVec.ofNat 64 (slO P + 8)) (s.gpr .x26)).writeW
      (fb P s + BitVec.ofNat 64 (slO P + 16)) (s.gpr .x30) := by
    simp only [m₄.mem, m₃.mem, m₂.mem, u₁.mem, m₃.gpr, m₂.gpr, u₁.other .x25 (by decide),
      u₁.other .x26 (by decide), u₁.other .x30 (by decide)]; rfl
  have hR : (fR P s).Contains (fb P s + BitVec.ofNat 64 (slO P)) 24 :=
    Offset.contains_base _ (by omega) (by omega)
  refine
    { rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, m₄.rd, m₃.rd, m₂.rd, u₁.rd]; rfl
      wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, m₄.wr, m₃.wr, m₂.wr, u₁.wr]; rfl
      sp := sp₉
      x0 := by rw [u₉.gpr, u₈.sp, u₇.sp, u₆.sp, u₅.sp, m₄.sp, m₃.sp, m₂.sp, u₁.sp]; simp [allocated]
      x1 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), g₄ _ (by decide)]
      x2 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
        u₅.other _ (by decide), g₄ _ (by decide)]
      x3 := by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g₄ _ (by decide)]
      x25 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide)]
      x26 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.gpr, u₅.other _ (by decide), g₄ _ (by decide)]
      keep := fun r hr h25 h26 => by
        have : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x10 := by
          simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
        rw [u₉.other _ this.1, u₈.other _ this.2.2.1, u₇.other _ this.2.1, u₆.other _ h26,
          u₅.other _ h25, g₄ _ this.2.2.2]
      frame := by
        rw [mem₉, mem₄]
        exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains_base _ (by omega) (by omega))).writeW (List.mem_singleton_self _) _
          (Offset.contains_base _ (by omega) (by omega))).writeW (List.mem_singleton_self _) _
          (Offset.contains_base _ (by omega) (by omega))
      slots := by
        rw [mem₉, mem₄]
        refine ⟨?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
        · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
            Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
            Mem.readW_writeW_self64]
        · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
            Mem.readW_writeW_self64] }


/-! ## Between the phases -/

/-- What every state inside the frame keeps of `s`, the state on entry. -/
structure Mid (P : Params) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = fR P s :: s.wr
  sp : t.sp = fb P s
  x25 : t.gpr .x25 = s.gpr .x1
  x26 : t.gpr .x26 = s.gpr .x2
  keep : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → t.gpr r = s.gpr r
  frame : Frame [fR P s] s.mem t.mem
  slots : Slots P s t.mem

theorem S1.mid {P : Params} {s t : State} (h : S1 P s t) : Mid P s t :=
  ⟨h.rd, h.wr, h.sp, h.x25, h.x26, fun r hr h25 h26 _ => h.keep r hr h25 h26, h.frame, h.slots⟩

/-- Regions at offsets within the frame are covered by the regions of a
state inside it. -/
theorem covers_frame {P : Params} (s : State) {t : State} (hwr : t.wr = fR P s :: s.wr) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = fb P s + BitVec.ofNat 64 off ∧ off + r.len ≤ frameBytes P) :
    Covers rs t.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨fR P s, by rw [hwr]; exact List.mem_cons_self .., off, hb, hl⟩

theorem fb_zero (P : Params) (s : State) : fb P s = fb P s + BitVec.ofNat 64 0 := by simp

/-- A change of memory within regions of the frame other than the saved
registers', and of no register `Mid` keeps, keeps `Mid`. -/
theorem Mid.of_frame {P : Params} (hF : Fits P) {s t t' : State} (h : Mid P s t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hsub : ∀ r ∈ rs, Region.Sub r (fR P s))
    (hsl : ∀ r ∈ rs, (slR P s).Disjoint r) : Mid P s t' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  x25 := (hg _ (by decide) (by decide)).trans h.x25
  x26 := (hg _ (by decide) (by decide)).trans h.x26
  keep r hr h25 h26 h30 := (hg r hr h30).trans (h.keep r hr h25 h26 h30)
  frame := h.frame.trans (hf.sub fun r hr => ⟨fR P s, List.mem_singleton_self _, hsub r hr⟩)
  slots := by
    have hn : (24 : Nat) ≤ 2 ^ 64 := by decide
    have hc : ∀ j ≤ 2, (slR P s).Contains (fb P s + BitVec.ofNat 64 (slO P + 8 * j)) 8 := fun j hj => by
      have := hF.lt; have := hF.sl_le
      exact Offset.contains _ (by omega) (by omega) (by omega)
    obtain ⟨a, b, c⟩ := h.slots
    refine ⟨?_, ?_, ?_⟩
    · rw [← a]; exact hf.readW (by simpa using hc 0 (by omega)) hsl (by decide)
    · rw [← b]; exact hf.readW (hc 1 (by omega)) hsl (by decide)
    · rw [← c]; exact hf.readW (hc 2 (by omega)) hsl (by decide)

end VG.Proof.MdStream.AArch64.OneShot
