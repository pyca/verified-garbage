module

public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Spill

/-! # The key search's state words (x86)

The controller keeps its words in the 128-byte state, at `addr S d`:
reading one through a store to another (`readW_write`), and through writes
apart from the state (`readW_frame`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86

/-- The state's region. -/
abbrev stR (S : BitVec 32) : Region := ⟨S.setWidth 64, 128⟩

/-- A store to the state's word at `d`, read at `e`. -/
theorem readW_write {m : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {d e : Nat} (v : BitVec 32)
    (hd : d + 4 ≤ 128) (he : e + 4 ≤ 128) (hde : d = e ∨ d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr S d) v).readW (addr S e) 32 = if d = e then v else m.readW (addr S e) 32 := by
  rw [Spill.addr_eq_of hS hd, Spill.addr_eq_of hS he]
  split
  · subst e; exact Mem.readW_writeW_self32 _ _ _
  · refine Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- The state's word at `d` lies in the state. -/
theorem contains_addr {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {d : Nat} (hd : d + 4 ≤ 128) :
    (stR S).Contains (addr S d) 4 := by
  rw [Spill.addr_eq_of hS hd]
  exact Offset.contains_base _ (by omega) (by omega)

/-- A word of the state, through writes apart from it. -/
theorem readW_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {S : BitVec 32}
    (hS : S.toNat + 128 ≤ 2 ^ 32) (hd : ∀ r ∈ rs, (stR S).Disjoint r) {d : Nat} (hd4 : d + 4 ≤ 128) :
    m'.readW (addr S d) 32 = m.readW (addr S d) 32 :=
  h.readW (contains_addr hS hd4) hd (by decide)

/-- Bytes apart from the regions a frame names. -/
theorem bytes_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  exact List.map_congr_left fun i hi => h.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-! ## Words by their offsets -/

/-- The state's words at the offsets `ds` hold `f` of their offsets. -/
def Ctl (m : Mem) (S : BitVec 32) (ds : List Nat) (f : Nat → BitVec 32) : Prop :=
  ∀ d ∈ ds, m.readW (addr S d) 32 = f d

/-- Offsets of whole words in the state. -/
def Aligned (ds : List Nat) : Prop := ∀ d ∈ ds, d + 4 ≤ 128 ∧ d % 4 = 0

instance (ds : List Nat) : Decidable (Aligned ds) := inferInstanceAs (Decidable (∀ d ∈ ds, _))

/-- `f` with `v` at `d`. -/
def upd (f : Nat → BitVec 32) (d : Nat) (v : BitVec 32) : Nat → BitVec 32 := fun e => if e = d then v else f e

theorem Ctl.get {m : Mem} {S : BitVec 32} {ds : List Nat} {f : Nat → BitVec 32} (h : Ctl m S ds f) {d : Nat}
    (hd : d ∈ ds) : m.readW (addr S d) 32 = f d := h d hd

theorem Ctl.congr {m : Mem} {S : BitVec 32} {ds : List Nat} {f g : Nat → BitVec 32} (h : Ctl m S ds f)
    (e : ∀ d ∈ ds, f d = g d) : Ctl m S ds g := fun d hd => (h d hd).trans (e d hd)

/-- A store to a word of the state. -/
theorem Ctl.write {m : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {ds : List Nat}
    {f : Nat → BitVec 32} (h : Ctl m S ds f) (hA : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0)
    (v : BitVec 32) : Ctl (m.writeW (addr S d) v) S ds (upd f d v) := by
  intro e he
  obtain ⟨he1, he4⟩ := hA e he
  rw [readW_write hS v hd he1 (by omega)]
  unfold upd
  by_cases hde : d = e
  · subst hde; simp
  · rw [ite_eq_right hde, ite_eq_right (Ne.symm hde)]; exact h e he

/-- Writes apart from the state. -/
theorem Ctl.frame {m m' : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {ds : List Nat}
    {f : Nat → BitVec 32} (h : Ctl m S ds f) (hA : Aligned ds) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (stR S).Disjoint r) : Ctl m' S ds f := fun e he => by
  rw [readW_frame hf hS hd (hA e he).1]; exact h e he

end VG.Proof.Ffdh.X86.KeySearch
