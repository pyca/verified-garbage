module

public import VerifiedGarbage.Proof.Argon2.AArch64.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.Mem

/-! # The scratch block as a vector of words -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2

/-- The permuted half of scratch. -/
def working (m : Mem) (p : Addr) : Block := Vector.ofFn fun i => word m p i.val

theorem working_get (m : Mem) (p : Addr) (i : Fin 128) :
    (working m p)[i] = word m p i.val := by
  simp only [working, Fin.getElem_fin, Vector.getElem_ofFn]

/-- A write changes exactly the selected word of the block. -/
theorem working_write (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    working (m.writeW (off p (1024 + 8 * i.val)) v) p = (working m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true, word, Mem.readW_writeW_self64]
  · simp only [h, ite_false, word]
    exact Mem.readW_writeW_sep
      (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- Store one register into its word of the permuted block. -/
theorem storeWord_ok (index : Fin 16 → Fin 128) (j : Fin 16) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block [Impl.Argon2.AArch64.storeWord index j]) s fun t =>
      t = { s with mem := s.mem.writeW (off p (1024 + 8 * (index j).val)) (s.gpr (Impl.Argon2.AArch64.lane j)) } := by
  have st := hs.write (d := 1024 + 8 * (index j).val) (n := 8) (by omega)
  rw [← hs.reg] at st
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.storeWord, runBlock_cons, runStep_some, runBlock_nil,
    exec_str_x (word_offset _ (index j).isLt) st, hs.reg, off,
    Option.some.injEq, exists_eq_left']

/-- Store the registers of the words `js` of a row or column, in order. -/
theorem stores_ok (index : Fin 16 → Fin 128) (js : List (Fin 16)) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block (js.map (Impl.Argon2.AArch64.storeWord index))) s fun t =>
      working t.mem p =
        js.foldl (fun b j => b.set (index j) (s.gpr (Impl.Argon2.AArch64.lane j))) (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    rw [List.map_cons, ← List.singleton_append]
    apply WP.block_append
    refine (storeWord_ok index j s hs).mono ?_
    intro s1 h1
    have hs1 : Scratch s1 p := by subst h1; exact ⟨hs.reg, hs.wr⟩
    refine (ih s1 hs1).mono ?_
    rintro t ⟨hw, hf, hg, hr, hwr, hv⟩
    subst h1
    refine ⟨?_, ?_, hg, hr, hwr, hv⟩
    · rw [hw, List.foldl_cons, working_write]
    · exact ((Frame.refl [⟨off p 1024, 1024⟩] s.mem).writeW (by simp) _
        (Offset.contains p (d := 1024 + 8 * (index j).val) (n := 8) (e := 1024) (k := 1024)
          (by omega) (by omega) (by omega))).trans hf

end VG.Proof.Argon2.AArch64
