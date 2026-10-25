module

public import VerifiedGarbage.Proof.Poly1305.RISCV64.State
public import VerifiedGarbage.Proof.Poly1305.RISCV64.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.State
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Poly1305.Spec
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Poly1305 on RISC-V: `init`

The key is copied into the state a byte at a time, and the accumulator's 24
bytes are zeroed (`Proof/Framework/RISCV64/Bytes.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem byte_off (p : Addr) (d i : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (d + i) := Offset.add_add p d i

theorem init_correct (s : State) (hs : Proof.Poly1305.initRISCV64.pre s) :
    WP isa init s (Proof.Poly1305.initRISCV64.post s) := by
  obtain ⟨hrd, hwr, hdj⟩ := hs
  rw [init]
  refine WP.block_append (WP.mono (Bytes.copyBytes_ok (s := s) (tmp := .t0) (src := .a1) (dst := .a0)
    (soff := 0) (doff := 24) (n := 32) (by decide) (by decide) (by decide) (by decide)
    (fun i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      by rw [Nat.zero_add]; exact contains_off (by omega) (by omega)⟩)
    (fun i hi => in_st (by rw [hwr]; exact List.mem_singleton_self _) (by omega))
    (fun i hi hc => hdj (s.gpr .a1 + BitVec.ofNat 64 (0 + i))
      ((Offset.sub_base (s.gpr .a0) (d := 24) (n := 32) (k := 128) (by decide)) _ hc)
      (by rw [Nat.zero_add]; exact contains_off (by omega) (by omega)))) fun s₁ h₁ => ?_)
  have a0₁ : s₁.gpr .a0 = s.gpr .a0 := h₁.gpr _ (by decide)
  refine WP.mono (Bytes.storeBytes_ok (s := s₁) (tmp := .t0) (dst := .a0) (doff := 0)
    (bs := List.replicate 24 0) (by decide) (by decide) (by decide)
    (fun i hi => by
      rw [h₁.wr, a0₁]
      exact in_st (by rw [hwr]; exact List.mem_singleton_self _)
        (by simp only [List.length_replicate] at hi; omega))) fun s₂ h₂ => ?_
  refine ⟨rfl, ?_, ?_⟩
  · simp only [bytesAt]
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    rw [show (24 : BitVec 64) = BitVec.ofNat 64 24 from rfl, byte_off, ← a0₁,
      h₂.frame _ fun r hr hc => ?_, a0₁, h₁.copied i hi, Nat.zero_add]
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [List.length_replicate, Region.Contains] at hc
    rw [add_ofNat_zero, Offset.add_sub_cancel_left, toNat_ofNat_lt (by omega)] at hc
    omega_using [hc, hi]
  · rw [show bytesAt s₂.mem (s.gpr .a0) 24 = List.replicate 24 0 from ?_, Poly1305.leNum_replicate_zero]
    · rfl
    simp only [bytesAt]
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    have := h₂.stored i (by simp only [List.length_replicate]; omega)
    rw [Nat.zero_add, a0₁] at this
    rw [this]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi, ↓reduceIte, Option.getD_some]
    rfl

theorem init_ok (s : State) (hs : Proof.Poly1305.initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.initRISCV64.post s s' := by
  obtain ⟨tr, t, he, hpost, hkeep⟩ :=
    WP.keep [.t0] (init_correct s hs) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), hpost⟩

theorem init_ct : ConstantTime isa Proof.Poly1305.initRISCV64.pre
    Proof.Poly1305.initRISCV64.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2.1

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 128⟩]

theorem init_verified : Verified RISCV64.target init Proof.Poly1305.initRISCV64 :=
  ⟨init_ok, init_ct, ⟨initSat, rfl, rfl, Region.disjoint_of_sep (by decide)⟩⟩

end VG.Proof.Poly1305.RISCV64
