module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignABI
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! Allocate the wrapper frame and locate the incoming stack arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomBase (s : State) : Addr := s.sp - BitVec.ofNat 64 Random.frameBytes

def randomFreed (s : State) : State :=
  { s with sp := s.sp + BitVec.ofNat 64 Random.frameBytes, wr := s.wr.tail }

theorem randomBase_toNat {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    (randomBase s).toNat = (s.sp).toNat - Random.frameBytes := by
  have hl := h.stackLower
  simp only [randomBase, BitVec.toNat_sub, BitVec.toNat_ofNat, Random.frameBytes]
  have hb := (s.sp).isLt
  omega

theorem random_frame_sub {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Region.Sub ⟨randomBase s, Random.frameBytes⟩ (below (s.sp) (extra + 256)) := by
  apply below_sub (by unfold Random.frameBytes; omega)
  have hl := h.stackLower
  have hb := (s.sp).isLt
  omega

theorem random_alloc_scr {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Scr (allocated Random.frameBytes s) (randomBase s) Random.frameBytes := by
  apply Scr.of_mem (List.mem_cons_self ..)
  rw [randomBase_toNat h]
  have hb := (s.sp).isLt
  unfold Random.frameBytes
  omega

theorem random_incoming_address (s : State) (j : Nat) :
    off (randomBase s) (256 + 8 * j) = stackArgAddr s j := by
  change s.sp - BitVec.ofNat 64 256 + BitVec.ofNat 64 (256 + 8 * j) = _
  rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem random_incoming_read {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (p : Nat × Nat) (hp : p ∈ RandomSign.incomingSlots) :
    InRegions ((allocated Random.frameBytes s).rd ++ (allocated Random.frameBytes s).wr)
      (off (randomBase s) p.1) 8 := by
  have hj (j : Nat) (hj : j < 5) :
      InRegions ((allocated Random.frameBytes s).rd ++ (allocated Random.frameBytes s).wr)
        (off (randomBase s) (256 + 8 * j)) 8 := by
    rw [random_incoming_address]
    refine ⟨⟨stackArgAddr s 0, 40⟩, List.mem_append_left _ ?_, ?_⟩
    · change _ ∈ s.rd
      rw [h.rd]
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]
    · simp only [stackArgAddr]
      exact Offset.contains _ (d := 8 * j) (n := 8) (e := 0) (k := 40)
        (by omega) (by omega) (by decide)
  simp only [RandomSign.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact hj 0 (by decide)
  · exact hj 1 (by decide)
  · exact hj 2 (by decide)
  · exact hj 3 (by decide)
  · exact hj 4 (by decide)

theorem random_frame_ok {extra : Nat} {s : State} (h : RandomSignABI extra s)
    {body : Prog isa} {Q : State → Prop}
    (hb : WP isa body (allocated Random.frameBytes s) fun t =>
      t.sp = randomBase s ∧ t.wr = (allocated Random.frameBytes s).wr ∧ Q (randomFreed t)) :
    WP isa (.frame (.alloc Random.frameBytes) body (.free Random.frameBytes)) s Q := by
  obtain ⟨trace, t, he, htsp, htwr, hq⟩ := hb
  have hl := h.stackLower
  have ha : isa.push (.alloc Random.frameBytes) s = some (allocated Random.frameBytes s) := by
    simp only [isa, push, allocated]
    exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega⟩
  have hf : isa.pop (.free Random.frameBytes) (allocated Random.frameBytes s) t = some (randomFreed t) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, htsp, htwr, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

end VG.Proof.Dsa.AArch64
