module

import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.Md5.PPC64LE.Compress
public import VerifiedGarbage.Impl.Md5.PPC64LE.Stream
import VerifiedGarbage.Proof.Md5.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
meta import VerifiedGarbage.Proof.Md5.PPC64LE.Compress
meta import VerifiedGarbage.Impl.Md5.PPC64LE.Stream
meta import VerifiedGarbage.Proof.Md5.Stream
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.PPC64LE.Residue
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Residue
import VerifiedGarbage.Proof.Framework.PPC64LE.TaintMono
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintMono
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Finalize
import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
public import VerifiedGarbage.Proof.Md5.Md
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Finalize
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
meta import VerifiedGarbage.Proof.Md5.Md

/-! ### `Md5.PPC64LE.Stream.Md`, which the modules that import this one used -/

section

/-!
# Streaming MD5 on PPC64LE: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/PPC64LE.lean`), so they are verified by the generic proofs
(`Proof/MdStream/PPC64LE/`) for MD5's instance (`Proof/Md5/Md.lean`), given
what MD5's own pieces do: its length field and digest (`shape`), that its
compression function is verified (`callee`), and that the taint analysis
accepts its code.
-/

@[expose] public section

namespace VG.Proof.Md5.PPC64LE.Stream

open VG VG.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE

abbrev params := Impl.Md5.PPC64LE.Stream.params

theorem dims : Dims params := ⟨by decide, by decide, by decide, by decide⟩

theorem shape : ShapeD (P := params) md 16 where
  le := by decide
  len _ hout := len64_ok (d := params.N + params.B - params.L) (be := false) (by decide) hout
  out _ hin hout hd := by
    refine (out32_ok (n := 4) false (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq, List.take_of_length_le (by simp only [List.length_flatMap, bytes32_length]; decide)]

theorem callee : CalleeOk (P := params) md Impl.Md5.PPC64LE.compress :=
  ⟨compress_verified.1, by decide +kernel⟩

namespace Update

theorem update_verified : Verified PPC64LE.target Impl.Md5.PPC64LE.Stream.update Proof.Md5.updatePPC64LE :=
  have h := MdStream.PPC64LE.Update.verified (name := "vg_md5_compress") dims callee
    (VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
      (fun _ _ _ _ hp => MdStream.PPC64LE.Update.agree₀ hp) (by taint_decide_sum [VG.Proof.Md5.PPC64LE.compressSum]))
    (by decide +kernel) (by decide +kernel)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.PPC64LE.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified PPC64LE.target Impl.Md5.PPC64LE.Stream.finalize Proof.Md5.finalizePPC64LE :=
  have h := MdStream.PPC64LE.Finalize.verifiedD (name := "vg_md5_compress") dims shape callee
    (VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
      (fun _ _ _ _ hp => MdStream.PPC64LE.Finalize.agree₀D hp) (by taint_decide_sum [VG.Proof.Md5.PPC64LE.compressSum]))
    (by decide +kernel) (by decide +kernel)
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => by
      have := h Spec.Md5.H0 m hr trivial hc
      exact this.trans (List.take_of_length_le (Nat.le_of_eq (md.digest_length _))),
      fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.PPC64LE.Finalize.satD params 16

end Finalize

end VG.Proof.Md5.PPC64LE.Stream

end

end

/-!
# Streaming MD5 on PPC64LE: `init`
-/

@[expose] public section

namespace VG.Proof.Md5.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Md5.PPC64LE.Stream
open VG.Proof.Md5.PPC64LE (writeState stateAt_writeState contains_offset)
open VG.Proof.MdStream.PPC64LE (WP.cons)
open VG.Spec.Md5 (stateAt H0)

/-- The three instructions storing the 32-bit word `x` at `off(r3)`. -/
def word (x : BitVec 32) (off : Nat) : List Instr :=
  [.lis .r8 (x.extractLsb' 16 16), .ori .r8 .r8 (x.extractLsb' 0 16), .store .w .r8 .r3 off]

theorem init_eq : init = .block (word H0[0] 0 ++ word H0[1] 4 ++ word H0[2] 8 ++ word H0[3] 12) := rfl

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

theorem init_correct {s₀ : State} (hp : Proof.Md5.initPPC64LE.pre s₀) :
    WP isa init s₀ fun s' => ((∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp) ∧
      Proof.Md5.initPPC64LE.post s₀ s' := by
  obtain ⟨-, hwr⟩ := hp
  have o : ∀ k, k < 4 → InRegions s₀.wr (s₀.gpr .r3 + BitVec.ofNat 64 (4 * k)) 4 :=
    fun k hk => ⟨⟨s₀.gpr .r3, 80⟩, by simp [hwr], contains_offset (by omega_using [hk]) (by omega_using [hk])⟩
  rw [init_eq, ← List.append_nil (_ ++ word H0[3] 12)]
  simp only [List.append_assoc]
  refine word_ok (by omega_using []) (o 0 (by omega_using [])) fun s1 g1 _ wr1 sp1 m1 => ?_
  refine word_ok (by omega_using []) (by rw [wr1, g1 _ (by decide)]; exact o 1 (by omega_using []))
    fun s2 g2 _ wr2 sp2 m2 => ?_
  refine word_ok (by omega_using []) (by rw [wr2, wr1, g2 _ (by decide), g1 _ (by decide)]; exact o 2 (by omega_using []))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  have w3 : s3.wr = s₀.wr := by rw [wr3, wr2, wr1]
  have k3 : s3.gpr .r3 = s₀.gpr .r3 := by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  refine word_ok (by omega_using []) (by rw [w3, k3]; exact o 3 (by omega_using [])) fun s4 g4 _ _ sp4 m4 =>
    WP.block_nil ?_
  have k4 : ∀ r, r ≠ .r8 → s4.gpr r = s₀.gpr r := fun r h => by rw [g4 r h, g3 r h, g2 r h, g1 r h]
  have hm : s4.mem = writeState s₀.mem (s₀.gpr .r3) H0 := by
    rw [m4, m3, m2, m1]
    simp only [g3 _ (show Reg.r3 ≠ .r8 by decide), g2 _ (show Reg.r3 ≠ .r8 by decide),
      g1 _ (show Reg.r3 ≠ .r8 by decide)]
    rfl
  refine ⟨⟨fun r hr => k4 r ?_, by rw [sp4, sp3, sp2, sp1]⟩, ?_⟩
  · revert r; decide
  · show Spec.Md5.Repr s4.mem (s₀.gpr .r3) []
    rw [hm]
    exact Proof.Md5.Stream.repr_nil (stateAt_writeState _ _ _)

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 80⟩]

theorem init_verified : Verified PPC64LE.target init Proof.Md5.initPPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl⟩⟩
  · obtain ⟨t, s', he, ⟨hk, hsp⟩, h⟩ := init_correct hs
    exact ⟨t, s', he, ⟨hk, hsp, Exec.lr he (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ h
    refine ⟨h.2, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1

/-- `vg_md5_init` returns without secret residue: it reads no memory, so what it leaves is a function of its arguments (`Residue.noResidue_of_blind`). -/
theorem init_noResidue (k : Contract isa) (r : Nat) : NoResidue init k r :=
  Residue.noResidue_of_blind (by decide) k r

end VG.Proof.Md5.PPC64LE.Stream
