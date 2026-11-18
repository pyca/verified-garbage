module

public import VerifiedGarbage.Proof.MdStream.Arm.Update
public import VerifiedGarbage.Proof.MdStream.Arm.Finalize
import VerifiedGarbage.Proof.MdStream.Arm.Words
public import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Proof.Md5.Arm.Compress
public import VerifiedGarbage.Impl.Md5.Arm.Stream
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.Arm.Update
meta import VerifiedGarbage.Proof.MdStream.Arm.Finalize
meta import VerifiedGarbage.Proof.MdStream.Arm.Words
meta import VerifiedGarbage.Proof.Md5.Md
meta import VerifiedGarbage.Proof.Md5.Arm.Compress
meta import VerifiedGarbage.Impl.Md5.Arm.Stream
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Md5.Stream
import VerifiedGarbage.Proof.Md5.StateMem
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Md5.Stream
meta import VerifiedGarbage.Proof.Md5.StateMem
meta import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Md5.Arm.Stream.Init`, which the modules that import this one used -/

section

/-!
# Streaming MD5 on ARMv7: `init`
-/

@[expose] public section

namespace VG.Proof.Md5.Arm.Stream

open VG VG.Arm VG.Impl.Md5.Arm.Stream
open VG.Proof.Md5.Arm (contains_offset)
open VG.Proof.MdStream.Arm (WP.cons wp_str)
open VG.Spec.Md5 (stateAt H0)

/-- The three instructions storing the 32-bit word `x` at `[r0 + off]`. -/
def word (x : BitVec 32) (off : Nat) : List Instr :=
  [.movw .r12 (x.extractLsb' 0 16), .movt .r12 (x.extractLsb' 16 16), .str .r12 .r0 off]

theorem init_eq : init = .block (word H0[0] 0 ++ word H0[1] 4 ++ word H0[2] 8 ++ word H0[3] 12) := rfl

theorem word_ok {x : BitVec 32} {off : Nat} (ho : off < 4096) {rest : List Instr}
    {s : State} {Q : State → Prop} (hfit : (s.gpr .r0).toNat + off < 2 ^ 32)
    (hout : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (State.addr (s.gpr .r0) + BitVec.ofNat 64 off) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word x off ++ rest)) s Q := by
  simp only [word, List.cons_append, List.nil_append]
  refine WP.cons rfl (WP.cons rfl ?_)
  refine wp_str ho (by simp only [State.setReg]; exact addr_add hfit) hout fun s' u => ?_
  refine k s' (fun r hr => by rw [u.gpr]; simp [State.setReg, hr]) u.rd u.wr u.sp ?_
  rw [u.mem]
  simp only [State.setReg, ite_true, movw_movt]

theorem init_correct {s₀ : State} (hp : Proof.Md5.initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Md5.initArm.post s₀ s' := by
  obtain ⟨-, hwr, hfit⟩ := hp
  have o : ∀ k, k < 4 → InRegions s₀.wr (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * k)) 4 :=
    fun k hk => ⟨⟨State.addr (s₀.gpr .r0), 80⟩, by simp [hwr], contains_offset (by omega_using [hk]) (by omega_using [hk])⟩
  rw [init_eq, ← List.append_nil (_ ++ word H0[3] 12)]
  simp only [List.append_assoc]
  refine word_ok (by decide) (by omega_using []) (o 0 (by omega_using [])) fun s1 g1 _ wr1 sp1 m1 => ?_
  have k1 : s1.gpr .r0 = s₀.gpr .r0 := g1 _ (by decide)
  refine word_ok (by decide) (by rw [k1]; omega_using [hfit]) (by rw [wr1, k1]; exact o 1 (by omega_using []))
    fun s2 g2 _ wr2 sp2 m2 => ?_
  have k2 : s2.gpr .r0 = s₀.gpr .r0 := by rw [g2 _ (by decide), k1]
  refine word_ok (by decide) (by rw [k2]; omega_using [hfit]) (by rw [wr2, wr1, k2]; exact o 2 (by omega_using []))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  have k3 : s3.gpr .r0 = s₀.gpr .r0 := by rw [g3 _ (by decide), k2]
  have w3 : s3.wr = s₀.wr := by rw [wr3, wr2, wr1]
  refine word_ok (by decide) (by rw [k3]; omega_using [hfit]) (by rw [w3, k3]; exact o 3 (by omega_using []))
    fun s4 g4 _ _ sp4 m4 => WP.block_nil ?_
  have k4 : ∀ r, r ≠ .r12 → s4.gpr r = s₀.gpr r := fun r h => by
    rw [g4 r h, g3 r h, g2 r h, g1 r h]
  have hm : s4.mem = Proof.Md5.StateMem.writeState s₀.mem (State.addr (s₀.gpr .r0)) H0 := by
    rw [m4, m3, m2, m1, k3, k2, k1]
    rfl
  refine ⟨⟨fun r hr => k4 r ?_, by rw [sp4, sp3, sp2, sp1]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · show Spec.Md5.Repr s4.mem (State.addr (s₀.gpr .r0)) []
    rw [hm]
    exact Proof.Md5.Stream.repr_nil (Proof.Md5.StateMem.stateAt_writeState _ _ _)

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 80⟩]

theorem init_verified : Verified Arm.target init Proof.Md5.initArm := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, by decide⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0]) (fun _ _ _ _ hp => ?_) (by taint_decide)
    exact Taint.agree_ofRegs fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp

end VG.Proof.Md5.Arm.Stream

end

end

/-!
# Streaming MD5 on ARMv7: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/Arm.lean`), so they are verified by the generic proofs
(`Proof/MdStream/Arm/`) for MD5's instance (`Proof/Md5/Md.lean`), given what
MD5's own pieces do: its length field and digest (`shape`), that its
compression function is verified (`callee`), and that the taint analysis
accepts its code.
-/

@[expose] public section

namespace VG.Proof.Md5.Arm.Stream

open VG VG.Arm VG.Proof.MdStream VG.Proof.MdStream.Arm

abbrev params := Impl.Md5.Arm.Stream.params

theorem dims : Dims params := ⟨.inl rfl, by decide, by decide, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len _ hfit hout := len64_ok (d := params.N + (params.B - params.L)) (be := false) (by decide)
    (by have : params.B = 64 := rfl; have : params.L = 8 := rfl; omega_arith) hout
  out _ f₀ f₆ hin hout hd := by
    refine (out32_ok (n := 4) false (by decide) f₀ f₆ hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨fun r h _ => g r h, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Md5.Arm.compress :=
  ⟨compress_verified.1, by decide +kernel, by rw [← Code.allInstrs_eq]; decide +kernel⟩

namespace Update

theorem update_verified : Verified Arm.target Impl.Md5.Arm.Stream.update Proof.Md5.updateArm :=
  have h := MdStream.Arm.Update.verified (name := "vg_md5_compress") dims callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Update.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Update.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.Arm.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified Arm.target Impl.Md5.Arm.Stream.finalize Proof.Md5.finalizeArm :=
  have h := MdStream.Arm.Finalize.verified (name := "vg_md5_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.Arm.Finalize.sat params

end Finalize

end VG.Proof.Md5.Arm.Stream
