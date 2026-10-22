module

import VerifiedGarbage.Proof.Argon2.AArch64.Mix
public import VerifiedGarbage.Impl.Argon2.AArch64.Compress
public import VerifiedGarbage.Proof.Argon2.Spec
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Argon2 compression working memory -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Impl.Argon2.AArch64

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (p : Addr) (i : Nat) : BitVec 64 := m.readW (off p (1024 + 8 * i)) 64

/-- Scratch permissions and its stable base register. -/
structure Scratch (s : State) (p : Addr) : Prop where
  reg : s.gpr .x3 = p
  wr : (⟨p, 4096⟩ : Region) ∈ s.wr

theorem Scratch.write {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions s.wr (off p d) n :=
  ⟨_, h.wr, Offset.contains_base p hd (by omega)⟩

theorem Scratch.read {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (off p d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base p hd (by omega)⟩

theorem word_offset (i : Nat) (hi : i < 128) :
    (1024 + 8 * i) % 8 = 0 ∧ 1024 + 8 * i < 32768 := by omega

theorem lane_injective : Function.Injective lane := by
  intro i j h
  revert i j
  decide

theorem lane_ne_x3 (j : Fin 16) : lane j ≠ .x3 := by revert j; decide

theorem lane_ne_x17 (j : Fin 16) : lane j ≠ .x17 := by revert j; decide

/-- Load one word of the permuted block into its register. -/
theorem loadWord_ok (index : Fin 16 → Fin 128) (j : Fin 16) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block [loadWord index j]) s fun t =>
      t = s.write .x (lane j) (word s.mem p (index j).val) := by
  have ld := hs.read (d := 1024 + 8 * (index j).val) (n := 8) (by omega)
  rw [← hs.reg] at ld
  apply WP.of_runBlock
  simp only [loadWord, runBlock_cons, runStep_some, runBlock_nil,
    exec_ldr_x (word_offset _ (index j).isLt) ld, hs.reg, word, off,
    Option.some.injEq, exists_eq_left']

/-- Load the words `js` of a row or column, each into its own register. -/
theorem loads_ok (index : Fin 16 → Fin 128) (js : List (Fin 16)) (hn : js.Nodup)
    (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (.block (js.map (loadWord index))) s fun t =>
      (∀ j ∈ js, t.gpr (lane j) = word s.mem p (index j).val) ∧
      (∀ r, (∀ j ∈ js, lane j ≠ r) → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v := by
  induction js generalizing s with
  | nil =>
    exact WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    obtain ⟨hj, hn'⟩ := List.nodup_cons.mp hn
    rw [List.map_cons, ← List.singleton_append]
    apply WP.block_append
    refine (loadWord_ok index j s hs).mono ?_
    rintro s1 rfl
    have hs1 : Scratch (s.write .x (lane j) (word s.mem p (index j).val)) p :=
      ⟨by rw [RegUpd.gpr_write_of_ne _ _ _ (lane_ne_x3 j).symm, hs.reg], hs.wr⟩
    refine (ih hn' _ hs1).mono ?_
    rintro t ⟨hl, hk, hm, hr, hw, hv⟩
    refine ⟨?_, ?_, hm, hr, hw, hv⟩
    · intro k hk'
      rcases List.mem_cons.mp hk' with rfl | hk'
      · rw [hk _ (fun i hi he => hj (by rw [← lane_injective he]; exact hi)), RegUpd.gpr_write_self,
          BitVec.setWidth_eq]
      · exact hl k hk'
    · intro r hr
      rw [hk r (fun i hi => hr i (List.mem_cons_of_mem _ hi)),
        RegUpd.gpr_write_of_ne _ _ _ (fun he => hr j (List.mem_cons_self ..) he.symm)]

end VG.Proof.Argon2.AArch64
