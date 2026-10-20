module
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-! # A controller's sixteen words, written in turn

The native controllers keep their state in sixteen 64-bit words at `B`:
`writeController m B values` writes each `(j, v)` of `values` to word `j`
in turn, and `controllerValue` is the value word `j` then holds. As the
x86-64 controllers' (`Proof/Ffdh/X86_64/Generation/ControlMemory.lean`),
for any target.
-/

@[expose] public section

namespace VG.Proof.Ffdh.Control

open VG VG.Proof.Bignum

def writeController (m : Mem) (B : Addr) (values : List (Nat × BitVec 64)) : Mem :=
  values.foldl (fun m e => m.writeW (off B (8 * e.1)) e.2) m

def controllerValue (values : List (Nat × BitVec 64)) (j : Nat) (initial : BitVec 64) : BitVec 64 :=
  values.foldl (fun value e => if j = e.1 then e.2 else value) initial

theorem controllerValue_unchanged (values : List (Nat × BitVec 64)) (j : Nat) (initial : BitVec 64)
    (hnot : ∀ e ∈ values, j ≠ e.1) : controllerValue values j initial = initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons e values ih =>
    change controllerValue values j (if j = e.1 then e.2 else initial) = initial
    rw [ite_eq_right (hnot e (List.mem_cons_self ..))]
    exact ih initial (fun x hx => hnot x (List.mem_cons_of_mem _ hx))

theorem writeController_append (m : Mem) (B : Addr) (xs ys : List (Nat × BitVec 64)) :
    writeController m B (xs ++ ys) = writeController (writeController m B xs) B ys := by
  exact List.foldl_append

theorem writeController_frame_size (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    {size : Nat} (hsize : size ≤ 2 ^ 64) (hvalues : ∀ e ∈ values, 8 * e.1 + 8 ≤ size) :
    Frame [⟨B, size⟩] m (writeController m B values) := by
  induction values generalizing m with
  | nil => exact Frame.refl _ _
  | cons e values ih =>
    have he := hvalues e (List.mem_cons_self ..)
    have hstore : Frame [⟨B, size⟩] m (m.writeW (off B (8 * e.1)) e.2) :=
      Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains_base _ he (by omega_using [he, hsize]))
    exact hstore.trans (ih _ (fun x hx => hvalues x (List.mem_cons_of_mem _ hx)))

theorem writeController_frame (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    (hvalues : ∀ e ∈ values, e.1 < 16) :
    Frame [⟨B, 128⟩] m (writeController m B values) :=
  writeController_frame_size m B values (by decide) fun e he => by
    have := hvalues e he; omega_using [this]

theorem controller_store_word (m : Mem) (B : Addr) (v : BitVec 64) {i j : Nat}
    (hi : i < 16) (hj : j < 16) :
    word (m.writeW (off B (8 * i)) v) B (8 * j) =
      if j = i then v else word m B (8 * j) := by
  by_cases he : j = i
  · subst he
    rw [ite_eq_left rfl]
    exact word_writeW_self _ _ _ _
  · rw [ite_eq_right he]
    exact hdrStore_hdr _ _ _ (by omega_using [hi]) (by omega_using [hj]) (Ne.symm he)

theorem writeController_word (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    (hvalues : ∀ e ∈ values, e.1 < 16) (j : Nat) (hj : j < 16) :
    word (writeController m B values) B (8 * j) = controllerValue values j (word m B (8 * j)) := by
  induction values generalizing m with
  | nil => rfl
  | cons e values ih =>
    have he := hvalues e (List.mem_cons_self ..)
    change word (writeController (m.writeW (off B (8 * e.1)) e.2) B values) B (8 * j) = _
    rw [ih _ (fun x hx => hvalues x (List.mem_cons_of_mem _ hx)), controller_store_word _ _ _ he hj]
    rfl

end VG.Proof.Ffdh.Control
