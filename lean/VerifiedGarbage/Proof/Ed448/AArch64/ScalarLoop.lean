import VerifiedGarbage.Proof.Ed448.AArch64.ScalarWord
import VerifiedGarbage.Proof.Ed448.ScalarWords

/-!
# Ed448 scalar arithmetic on AArch64: the loop over the words

`scalarLoop` consumes the words of an input of `8n + t` bytes at `x1` from
the top, below the `t` bytes the remainder starts from: the invariant is the
value modulo `L` of the consumed top bytes. The body writes no memory.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Spec.Ed448 (L bytesAt decodeLE)

theorem wordRead_ok (s : State) (k : Nat) (hb : s.gpr .x3 = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block wordRead) s fun t =>
      t.gpr .x3 = BitVec.ofNat 64 (8 * k) ∧
      t.gpr .x4 = s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 64 ∧
      Keeps [.x3, .x4] s t := by
  have hn : s.gpr .x3 - BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * k) := by
    rw [hb, show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [wordRead, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    Size.bytes, show (8 : Nat) < 4096 from by decide, show (0 : Nat) % 8 = 0 from rfl,
    show (0 : Nat) < 4096 * 8 from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hn, BitVec.add_zero, BitVec.setWidth_eq, hr,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, ⟨fun r h => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2, ite_false]

theorem scalarWord_eq : scalarWord = wordRead ++ (wordFold ++ csub) := by
  simp only [scalarWord, List.append_assoc]

/-- One word: read, folded in, reduced. -/
theorem scalarWord_ok (s : State) (hc : Consts s) (k : Nat)
    (hb : s.gpr .x3 = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8)
    (hv : rem s < L) :
    WP isa (.block scalarWord) s fun t =>
      t.gpr .x3 = BitVec.ofNat 64 (8 * k) ∧
      rem t = ((s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 64).toNat + 2 ^ 64 * rem s) % L ∧
      Keeps clob s t := by
  rw [scalarWord_eq, WP.block_append_iff]
  refine WP.mono (wordRead_ok s k hb hr) fun a ⟨ab, ax, ka⟩ => ?_
  have av : rem a = rem s := Keeps.rv_eq ka (by decide)
  have hca : Consts a := hc.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordFold_ok a hca (by rw [av]; exact hv)) fun b ⟨b2, bm, kb⟩ => ?_
  have hcb : Consts b := hca.of_keeps kb (by decide)
  refine WP.mono (csub_ok b hcb b2) fun t ⟨tv, kt⟩ => ?_
  refine ⟨?_, ?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩
  · rw [kt.gpr _ (by decide), kb.gpr _ (by decide)]; exact ab
  · rw [tv, bm, ax, av]

theorem counter_test : ∀ n < 17, (BitVec.ofNat 64 (8 * n) != 0) = decide (n ≠ 0) := by decide

/-- The loop's invariant, after `n` words are left: the remainder is that of
the bytes from word `n` up, of the `len` bytes at `x1`. -/
structure LoopInv (len : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  pos : 0 < n
  bound : 8 * n ≤ len
  counter : s.gpr .x3 = BitVec.ofNat 64 (8 * n)
  value : rem s = decodeLE (bytesAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * n)) (len - 8 * n)) % L
  keeps : Keeps clob s₀ s

/-- The loop, from `n₀ ≥ 1` words left, with the remainder of the bytes above
them: the remainder of all `len` bytes. -/
theorem scalarLoop_ok (s₀ : State) (hc : Consts s₀) {len n₀ : Nat} (hn : n₀ < 17)
    (hi : LoopInv len s₀ n₀ s₀)
    (hr : ∀ k < n₀, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa scalarLoop s₀ fun t =>
      rem t = decodeLE (bytesAt s₀.mem (s₀.gpr .x1) len) % L ∧ Keeps clob s₀ t := by
  apply WP.loop (fun n s => n ≤ n₀ ∧ LoopInv len s₀ n s) (n := n₀)
  · intro n s ⟨hnn, hi⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.pos; omega : n ≠ 0)
    have hp : s.gpr .x1 = s₀.gpr .x1 := hi.keeps.gpr .x1 (by decide)
    have hcs : Consts s := hc.of_keeps hi.keeps constRegs_clob
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := by
      rw [hi.keeps.rd, hi.keeps.wr, hp]; exact hr k (by omega)
    have hb := hi.bound
    have hv : rem s < L := by rw [hi.value]; exact Nat.mod_lt _ L_pos
    refine WP.mono (scalarWord_ok s hcs k hi.counter hread hv) fun t ⟨tb, tv, tk⟩ => ?_
    have kt := hi.keeps.trans tk
    have vt : rem t =
        decodeLE (bytesAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * k)) (len - 8 * k)) % L := by
      rw [tv, hp, hi.keeps.mem, hi.value, words_step _ _ len k hb, Nat.mul_comm (2 ^ 64),
        Nat.add_comm, mod_step]
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, read_x, tb, counter_test 0 (by decide),
        show decide ((0 : Nat) ≠ 0) = false from rfl], ?_, kt⟩
      simpa only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] using vt
    · exact Or.inr ⟨by simp only [eval, read_x, tb, counter_test k (by omega), decide_eq_true hk0],
        k, by omega, by omega, ⟨by omega, by omega, tb, vt, kt⟩⟩
  · exact ⟨Nat.le_refl _, hi⟩

end VG.Proof.Ed448.AArch64
