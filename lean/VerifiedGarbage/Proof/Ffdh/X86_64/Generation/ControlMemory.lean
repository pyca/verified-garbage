module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Sig

/-! # The generation controller's private sixteen-word workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

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
    Frame [⟨B, 128⟩] m (writeController m B values) := by
  induction values generalizing m with
  | nil => exact Frame.refl _ _
  | cons e values ih =>
    have he := hvalues e (List.mem_cons_self ..)
    have hstore : Frame [⟨B, 128⟩] m (m.writeW (off B (8 * e.1)) e.2) :=
      Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega_using [he]) (by omega_using [he]))
    exact hstore.trans (ih _ (fun x hx => hvalues x (List.mem_cons_of_mem _ hx)))

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

theorem controller_read_other (m : Mem) (B : Addr) (v : BitVec 64) {i j : Nat}
    (hi : i < 16) (hj : j < 16) (hne : i ≠ j) :
    (m.writeW (B + BitVec.ofNat 64 (8 * i)) v).readW (B + BitVec.ofNat 64 (8 * j)) 64 =
      m.readW (B + BitVec.ofNat 64 (8 * j)) 64 := by
  exact hdrStore_hdr _ _ _ (by omega_using [hi]) (by omega_using [hj]) hne

theorem writeController_policy (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 16) :
    Spec.Rsa.wordsAt (writeController m B values) B 4 =
      [controllerValue values 0 (word m B 0), controllerValue values 1 (word m B 8),
        controllerValue values 2 (word m B 16), controllerValue values 3 (word m B 24)] := by
  change [word (writeController m B values) B (8 * 0), word (writeController m B values) B (8 * 1),
    word (writeController m B values) B (8 * 2), word (writeController m B values) B (8 * 3)] = _
  rw [writeController_word _ _ _ hb 0 (by decide), writeController_word _ _ _ hb 1 (by decide),
    writeController_word _ _ _ hb 2 (by decide), writeController_word _ _ _ hb 3 (by decide)]

end VG.Proof.Ffdh.X86_64.Generation
