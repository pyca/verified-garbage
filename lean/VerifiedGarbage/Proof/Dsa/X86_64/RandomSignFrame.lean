module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignABI
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! Allocate the wrapper frame and locate the incoming stack arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomBase (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 Random.frameBytes

def randomFreed (s : State) : State :=
  { s.setReg .rsp (s.gpr .rsp + BitVec.ofNat 64 Random.frameBytes) with wr := s.wr.tail }

theorem randomBase_toNat {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    (randomBase s).toNat = (s.gpr .rsp).toNat - Random.frameBytes := by
  have hl := h.stackLower
  simp only [randomBase, BitVec.toNat_sub, BitVec.toNat_ofNat, Random.frameBytes]
  have hb := (s.gpr .rsp).isLt
  omega

theorem random_frame_sub {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Region.Sub ⟨randomBase s, Random.frameBytes⟩ (below (s.gpr .rsp) (extra + 256)) := by
  apply below_sub (by unfold Random.frameBytes; omega)
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  omega

theorem random_alloc_scr {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Scr (allocState Random.frameBytes s) (randomBase s) Random.frameBytes := by
  apply Scr.of_mem (List.mem_cons_self ..)
  rw [randomBase_toNat h]
  have hb := (s.gpr .rsp).isLt
  unfold Random.frameBytes
  omega

theorem random_incoming_address (s : State) (j : Nat) :
    off (randomBase s) (256 + 8 * j) = stackArgAddr s j := by
  change s.gpr .rsp - BitVec.ofNat 64 248 + BitVec.ofNat 64 (256 + 8 * j) = _
  rw [show 256 + 8 * j = 248 + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem random_incoming_read {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (p : Nat × Nat) (hp : p ∈ RandomSign.incomingSlots) :
    InRegions ((allocState Random.frameBytes s).rd ++ (allocState Random.frameBytes s).wr)
      (off (randomBase s) p.1) 8 := by
  have hj (j : Nat) (hj : j < 7) :
      InRegions ((allocState Random.frameBytes s).rd ++ (allocState Random.frameBytes s).wr)
        (off (randomBase s) (256 + 8 * j)) 8 := by
    rw [random_incoming_address]
    refine ⟨⟨stackArgAddr s 0, 56⟩, List.mem_append_left _ ?_, ?_⟩
    · change _ ∈ s.rd
      rw [h.rd]
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]
    · simp only [stackArgAddr]
      exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8) (k := 56)
        (by omega) (by omega) (by decide)
  simp only [RandomSign.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hj 0 (by decide)
  · exact hj 1 (by decide)
  · exact hj 2 (by decide)
  · exact hj 3 (by decide)
  · exact hj 4 (by decide)
  · exact hj 5 (by decide)
  · exact hj 6 (by decide)

theorem random_frame_ok {extra : Nat} {s : State} (h : RandomSignABI extra s)
    {body : Prog isa} {Q : State → Prop}
    (hb : WP isa body (allocState Random.frameBytes s) fun t =>
      t.gpr .rsp = randomBase s ∧ t.wr = (allocState Random.frameBytes s).wr ∧ Q (randomFreed t)) :
    WP isa (.frame (.alloc Random.frameBytes) body (.free Random.frameBytes)) s Q := by
  obtain ⟨trace, t, he, htsp, htwr, hq⟩ := hb
  have hl := h.stackLower
  have ha : isa.push (.alloc Random.frameBytes) s = some (allocState Random.frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega⟩
  have hf : isa.pop (.free Random.frameBytes) (allocState Random.frameBytes s) t = some (randomFreed t) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, htsp, htwr, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

end VG.Proof.Dsa.X86_64
