module

import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.Sm3.PPC64LE.Compress
public import VerifiedGarbage.Impl.Sm3.PPC64LE.Stream
import VerifiedGarbage.Proof.Sm3.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
meta import VerifiedGarbage.Proof.Sm3.PPC64LE.Compress
meta import VerifiedGarbage.Impl.Sm3.PPC64LE.Stream
meta import VerifiedGarbage.Proof.Sm3.Stream
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming SM3 on PPC64LE: `init`
-/

@[expose] public section

namespace VG.Proof.Sm3.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Sm3.PPC64LE.Stream
open VG.Proof.Sm3.PPC64LE (writeState stateAt_writeState contains_offset)
open VG.Proof.MdStream.PPC64LE (WP.cons)
open VG.Spec.Sm3 (stateAt iv)

/-- The three instructions storing the 32-bit word `x` at `off(r3)`. -/
def word (x : BitVec 32) (off : Nat) : List Instr :=
  [.lis .r8 (x.extractLsb' 16 16), .ori .r8 .r8 (x.extractLsb' 0 16), .store .w .r8 .r3 off]

theorem init_eq : init = .block (word iv[0] 0 ++ word iv[1] 4 ++ word iv[2] 8 ++ word iv[3] 12 ++
    word iv[4] 16 ++ word iv[5] 20 ++ word iv[6] 24 ++ word iv[7] 28) := rfl

theorem word_ok {x : BitVec 32} {off : Nat} (ho : off < 2 ^ 15) {rest : List Instr}
    {s : State} {Q : State → Prop} (hout : InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (s.gpr .r3 + BitVec.ofNat 64 off) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word x off ++ rest)) s Q := by
  simp only [word, List.cons_append, List.nil_append]
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_store_w (by decide) ho ?_)
    (k _ ?_ rfl rfl rfl ?_)))
  · simpa [State.write] using hout
  · intro r hr; simp [State.write, hr]
  · simp only [State.write, ite_true, show Reg.r3 ≠ .r8 by decide, ite_false]
    congr 1
    exact lis_ori x

theorem init_correct {s₀ : State} (hp : Proof.Sm3.initPPC64LE.pre s₀) :
    WP isa init s₀ fun s' => ((∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp) ∧
      Proof.Sm3.initPPC64LE.post s₀ s' := by
  obtain ⟨-, hwr⟩ := hp
  have o : ∀ k, k < 8 → InRegions s₀.wr (s₀.gpr .r3 + BitVec.ofNat 64 (4 * k)) 4 :=
    fun k hk => ⟨⟨s₀.gpr .r3, 96⟩, by simp [hwr], contains_offset (by omega) (by omega)⟩
  rw [init_eq, ← List.append_nil (_ ++ word iv[7] 28)]
  simp only [List.append_assoc]
  refine word_ok (by omega) (o 0 (by omega)) fun s1 g1 _ wr1 sp1 m1 => ?_
  refine word_ok (by omega) (by rw [wr1, g1 _ (by decide)]; exact o 1 (by omega))
    fun s2 g2 _ wr2 sp2 m2 => ?_
  refine word_ok (by omega) (by rw [wr2, wr1, g2 _ (by decide), g1 _ (by decide)]; exact o 2 (by omega))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  refine word_ok (by omega)
    (by rw [wr3, wr2, wr1, g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]; exact o 3 (by omega))
    fun s4 g4 _ wr4 sp4 m4 => ?_
  refine word_ok (by omega)
    (by rw [wr4, wr3, wr2, wr1, g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
        exact o 4 (by omega))
    fun s5 g5 _ wr5 sp5 m5 => ?_
  refine word_ok (by omega)
    (by rw [wr5, wr4, wr3, wr2, wr1, g5 _ (by decide), g4 _ (by decide), g3 _ (by decide),
          g2 _ (by decide), g1 _ (by decide)]
        exact o 5 (by omega))
    fun s6 g6 _ wr6 sp6 m6 => ?_
  have w6 : s6.wr = s₀.wr := by rw [wr6, wr5, wr4, wr3, wr2, wr1]
  have k6 : s6.gpr .r3 = s₀.gpr .r3 := by
    rw [g6 _ (by decide), g5 _ (by decide), g4 _ (by decide), g3 _ (by decide), g2 _ (by decide),
      g1 _ (by decide)]
  refine word_ok (by omega) (by rw [w6, k6]; exact o 6 (by omega)) fun s7 g7 _ wr7 sp7 m7 => ?_
  have w7 : s7.wr = s₀.wr := by rw [wr7, w6]
  have k7 : s7.gpr .r3 = s₀.gpr .r3 := by rw [g7 _ (by decide), k6]
  refine word_ok (by omega) (by rw [w7, k7]; exact o 7 (by omega)) fun s8 g8 _ _ sp8 m8 =>
    WP.block_nil ?_
  have k8 : ∀ r, r ≠ .r8 → s8.gpr r = s₀.gpr r := fun r h => by
    rw [g8 r h, g7 r h, g6 r h, g5 r h, g4 r h, g3 r h, g2 r h, g1 r h]
  have hm : s8.mem = writeState s₀.mem (s₀.gpr .r3) iv := by
    rw [m8, m7, m6, m5, m4, m3, m2, m1]
    simp only [g7 _ (show Reg.r3 ≠ .r8 by decide), g6 _ (show Reg.r3 ≠ .r8 by decide),
      g5 _ (show Reg.r3 ≠ .r8 by decide), g4 _ (show Reg.r3 ≠ .r8 by decide),
      g3 _ (show Reg.r3 ≠ .r8 by decide), g2 _ (show Reg.r3 ≠ .r8 by decide),
      g1 _ (show Reg.r3 ≠ .r8 by decide)]
    rfl
  refine ⟨⟨fun r hr => k8 r ?_, by rw [sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1]⟩, ?_⟩
  · revert r; decide
  · show Spec.Sm3.Repr s8.mem (s₀.gpr .r3) []
    rw [hm]
    exact Proof.Sm3.Stream.repr_nil (stateAt_writeState _ _ _)

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 96⟩]

theorem init_verified : Verified PPC64LE.target init Proof.Sm3.initPPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl⟩⟩
  · obtain ⟨t, s', he, ⟨hk, hsp⟩, h⟩ := init_correct hs
    exact ⟨t, s', he, ⟨hk, hsp, Exec.lr he (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ h
    refine ⟨h.2, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1

end VG.Proof.Sm3.PPC64LE.Stream
