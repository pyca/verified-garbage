module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# ChaCha20-Poly1305 with the AVX2 code (x86-64): padding

`Stitch.padIns r n` writes only `r` (`pad_ok`): each of its instructions is
`mov r32, 0`, `mov r64, r64` or `mov r32, r32` (`IsPad`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.ChaCha20Poly1305.X86_64.Stitch

/-- An instruction of a padding of `r`. -/
def IsPad (r : Reg) (i : Instr) : Prop :=
  i = .mov32 r (.imm 0) ∨ i = .mov r (.reg r) ∨ i = .mov32 r (.reg r)

/-- What a padding of `r` leaves from `s`: all but `r` as it was. -/
structure PadPost (r : Reg) (s t : State) : Prop where
  gpr : ∀ q, q ≠ r → t.gpr q = s.gpr q
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mx : t.mxcsr = s.mxcsr

theorem PadPost.trans {r : Reg} {s t u : State} (h : PadPost r s t) (h' : PadPost r t u) : PadPost r s u :=
  ⟨fun q hq => (h'.gpr q hq).trans (h.gpr q hq), h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    h'.mx.trans h.mx⟩

theorem pad1_ok {r : Reg} {i : Instr} (hi : IsPad r i) (s : State) :
    WP isa (.block [i]) s (PadPost r s) := by
  apply WP.of_runBlock
  rcases hi with rfl | rfl | rfl
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨fun q hq => by simp [gpr_setReg, hq], rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨fun q hq => by simp [gpr_setReg, hq], rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨fun q hq => by simp [gpr_setReg, hq], rfl, rfl, rfl, rfl⟩

/-- A block of padding instructions writes only `r`. -/
theorem pad_ok (r : Reg) : ∀ (l : List Instr), (∀ i ∈ l, IsPad r i) → ∀ s,
    WP isa (.block l) s (PadPost r s)
  | [], _, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | i :: l, h, s => by
    rw [show i :: l = [i] ++ l from rfl]
    exact WP.block_append (WP.mono (pad1_ok (h i (List.mem_cons_self ..)) s) fun t ht =>
      WP.mono (pad_ok r l (fun j hj => h j (List.mem_cons_of_mem _ hj)) t) fun u hu => ht.trans hu)

theorem padIns_ok (r : Reg) {n : Nat} (hn : n ∈ [3, 5, 8, 9, 18, 19, 20, 29, 35]) (s : State) :
    WP isa (.block (padIns r n)) s (PadPost r s) :=
  pad_ok r _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [padIns, IsPad]) s

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
