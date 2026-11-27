module

public import VerifiedGarbage.Proof.Sm3.Arm.Compress
public import VerifiedGarbage.Proof.Sm3.Scratch
public import VerifiedGarbage.Proof.MdStream.Arm.Finalize
public import VerifiedGarbage.Proof.MdStream.Arm.Update
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm3.Arm.Stream
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm3.Arm.Lit
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Sm3.Stream
import VerifiedGarbage.Proof.Sm3.StateMem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sm3.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Sm3.Arm.Compress
meta import VerifiedGarbage.Proof.Sm3.Stream
meta import VerifiedGarbage.Proof.Sm3.StateMem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Sm3.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.Sm3.Arm.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm3.Arm.Lit
import VerifiedGarbage.Proof.MdStream.Arm.Words
public import VerifiedGarbage.Proof.Sm3.Md
meta import VerifiedGarbage.Proof.MdStream.Arm.Update
meta import VerifiedGarbage.Proof.MdStream.Arm.Finalize
meta import VerifiedGarbage.Proof.MdStream.Arm.Words
meta import VerifiedGarbage.Proof.Sm3.Md
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Sm3.Arm.Stream.Md`, which only this module used -/

section

/-!
# Streaming SM3 on ARMv7: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/Arm.lean`), so they are verified by the generic proofs
(`Proof/MdStream/Arm/`) for SM3's instance (`Proof/Sm3/Md.lean`), given what
SM3's own pieces do: its length field and digest (`shape`), that its
compression function is verified (`callee`), and that the taint analysis
accepts its code.
-/

@[expose] public section

namespace VG.Proof.Sm3.Arm.Stream

open VG VG.Arm VG.Proof.MdStream VG.Proof.MdStream.Arm

abbrev params := Impl.Sm3.Arm.Stream.params

theorem dims : Dims params := ⟨.inl rfl, by decide, by decide, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len _ hfit hout := len64_ok (d := params.N + (params.B - params.L)) (be := true) (by decide)
    (by have : params.B = 64 := rfl; have : params.L = 8 := rfl; omega_arith) hout
  out _ f₀ f₆ hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) f₀ f₆ hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨fun r h _ => g r h, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Sm3.Arm.compress :=
  ⟨compress_verified.1, by lit_decide, by rw [← Code.allInstrs_eq]; lit_decide⟩

namespace Update

theorem update_verified : Verified Arm.target Impl.Sm3.Arm.Stream.update Proof.Sm3.updateArm :=
  have h := MdStream.Arm.Update.verified (name := "vg_sm3_compress") dims callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Update.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Update.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.Arm.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified Arm.target Impl.Sm3.Arm.Stream.finalize Proof.Sm3.finalizeArm :=
  have h := MdStream.Arm.Finalize.verified (name := "vg_sm3_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.Arm.Finalize.sat params

end Finalize

end VG.Proof.Sm3.Arm.Stream

end

end

/-! ### `Sm3.Arm.Stream.Init`, which only this module used -/

section

/-!
# Streaming SM3 on ARMv7: `init`
-/

@[expose] public section

namespace VG.Proof.Sm3.Arm.Stream

open VG VG.Arm VG.Impl.Sm3.Arm.Stream
open VG.Proof.Sm3.Arm (contains_offset)
open VG.Proof.MdStream.Arm (WP.cons wp_str)
open VG.Spec.Sm3 (stateAt iv)

/-- The three instructions storing the 32-bit word `x` at `[r0 + off]`. -/
def word (x : BitVec 32) (off : Nat) : List Instr :=
  [.movw .r12 (x.extractLsb' 0 16), .movt .r12 (x.extractLsb' 16 16), .str .r12 .r0 off]

theorem init_eq : init = .block (word iv[0] 0 ++ word iv[1] 4 ++ word iv[2] 8 ++ word iv[3] 12 ++
    word iv[4] 16 ++ word iv[5] 20 ++ word iv[6] 24 ++ word iv[7] 28) := rfl

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

theorem init_correct {s₀ : State} (hp : Proof.Sm3.initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sm3.initArm.post s₀ s' := by
  obtain ⟨-, hwr, hfit⟩ := hp
  have o : ∀ k, k < 8 → InRegions s₀.wr (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * k)) 4 :=
    fun k hk => ⟨⟨State.addr (s₀.gpr .r0), 96⟩, by simp [hwr], contains_offset (by omega_using [hk]) (by omega_using [hk])⟩
  rw [init_eq, ← List.append_nil (_ ++ word iv[7] 28)]
  simp only [List.append_assoc]
  refine word_ok (by decide) (by omega_using []) (o 0 (by omega_using [])) fun s1 g1 _ wr1 sp1 m1 => ?_
  have k1 : s1.gpr .r0 = s₀.gpr .r0 := g1 _ (by decide)
  refine word_ok (by decide) (by rw [k1]; omega_using [hfit]) (by rw [wr1, k1]; exact o 1 (by omega_using []))
    fun s2 g2 _ wr2 sp2 m2 => ?_
  have k2 : s2.gpr .r0 = s₀.gpr .r0 := by rw [g2 _ (by decide), k1]
  refine word_ok (by decide) (by rw [k2]; omega_using [hfit]) (by rw [wr2, wr1, k2]; exact o 2 (by omega_using []))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  have k3 : s3.gpr .r0 = s₀.gpr .r0 := by rw [g3 _ (by decide), k2]
  refine word_ok (by decide) (by rw [k3]; omega_using [hfit]) (by rw [wr3, wr2, wr1, k3]; exact o 3 (by omega_using []))
    fun s4 g4 _ wr4 sp4 m4 => ?_
  have k4 : s4.gpr .r0 = s₀.gpr .r0 := by rw [g4 _ (by decide), k3]
  refine word_ok (by decide) (by rw [k4]; omega_using [hfit]) (by rw [wr4, wr3, wr2, wr1, k4]; exact o 4 (by omega_using []))
    fun s5 g5 _ wr5 sp5 m5 => ?_
  have k5 : s5.gpr .r0 = s₀.gpr .r0 := by rw [g5 _ (by decide), k4]
  refine word_ok (by decide) (by rw [k5]; omega_using [hfit])
    (by rw [wr5, wr4, wr3, wr2, wr1, k5]; exact o 5 (by omega_using [])) fun s6 g6 _ wr6 sp6 m6 => ?_
  have k6 : s6.gpr .r0 = s₀.gpr .r0 := by rw [g6 _ (by decide), k5]
  have w6 : s6.wr = s₀.wr := by rw [wr6, wr5, wr4, wr3, wr2, wr1]
  refine word_ok (by decide) (by rw [k6]; omega_using [hfit]) (by rw [w6, k6]; exact o 6 (by omega_using []))
    fun s7 g7 _ wr7 sp7 m7 => ?_
  have k7 : s7.gpr .r0 = s₀.gpr .r0 := by rw [g7 _ (by decide), k6]
  have w7 : s7.wr = s₀.wr := by rw [wr7, w6]
  refine word_ok (by decide) (by rw [k7]; omega_using [hfit]) (by rw [w7, k7]; exact o 7 (by omega_using []))
    fun s8 g8 _ _ sp8 m8 => WP.block_nil ?_
  have k8 : ∀ r, r ≠ .r12 → s8.gpr r = s₀.gpr r := fun r h => by
    rw [g8 r h, g7 r h, g6 r h, g5 r h, g4 r h, g3 r h, g2 r h, g1 r h]
  have hm : s8.mem = Proof.Sm3.StateMem.writeState s₀.mem (State.addr (s₀.gpr .r0)) iv := by
    rw [m8, m7, m6, m5, m4, m3, m2, m1, k7, k6, k5, k4, k3, k2, k1]
    rfl
  refine ⟨⟨fun r hr => k8 r ?_, by rw [sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · show Spec.Sm3.Repr s8.mem (State.addr (s₀.gpr .r0)) []
    rw [hm]
    exact Proof.Sm3.Stream.repr_nil (Proof.Sm3.StateMem.stateAt_writeState _ _ _)

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
  wr := [⟨0x1000, 96⟩]

theorem init_verified : Verified Arm.target init Proof.Sm3.initArm := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, by decide⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0]) (fun _ _ _ _ hp => ?_) (by taint_decide)
    exact Taint.agree_ofRegs fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp

end VG.Proof.Sm3.Arm.Stream

end

end

/-!
# SM3 on ARMv7: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/Arm/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space (19 words: the compression
function's 104 bytes, then the registers the streaming code saves) in a frame
of their own: they are `updateScratch` and `finalizeScratch` (the shared
contracts with the working space as an argument, `Proof/Sm3/Scratch.lean`)
run in a frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sm3.Arm.Shared

open _root_.VG.Arm

theorem init : Verified Arm.target Impl.Sm3.Arm.Stream.init (Spec.Sm3.initContract Arm.abi) :=
  Proof.Sm3.Arm.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sm3.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sm3.Arm.Stream.initSat)

theorem updateScratch :
    Verified Arm.target Impl.Sm3.Arm.Stream.update (Proof.Sm3.updateScratchContract Arm.abi 19) :=
  Proof.Sm3.Arm.Stream.Update.update_verified.of_implies (by
    sig_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig,
      Proof.Sm3.updateArm, Proof.Sm3.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Sm3.Arm.Stream.Update.sat, MdStream.Arm.Update.sat, Impl.Sm3.Arm.Stream.params,
        Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sm3.Arm.Stream.Update.sat)

theorem finalizeScratch :
    Verified Arm.target Impl.Sm3.Arm.Stream.finalize (Proof.Sm3.finalizeScratchContract Arm.abi 19) :=
  Proof.Sm3.Arm.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig,
      Spec.Sm3.finalizeSig, Proof.Sm3.finalizeArm, Proof.Sm3.countArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sm3.Arm.Stream.Finalize.sat, MdStream.Arm.Finalize.sat, MdStream.Arm.Finalize.satBase,
        Impl.Sm3.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sm3.Arm.Stream.Finalize.sat)

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : Arm.State :=
  { MdStream.Arm.Update.sat Impl.Sm3.Arm.Stream.params with
    rd := [⟨0, 0⟩, ⟨0x4000, 8⟩], wr := [⟨0x1000, 96⟩] }

theorem update : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 168 2 Impl.Sm3.Arm.Stream.update)
    (Spec.Sm3.updateContract Arm.abi 168) :=
  Arm.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 19)
    (stack := 0) (bytes := 168) (m := 2)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by decide)
    (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.updatePost_local _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sm3.updatePostOut_local _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sm3.updateContract, Spec.Sm3.updateSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updateFrameSat, MdStream.Arm.Update.sat, Impl.Sm3.Arm.Stream.params, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : Arm.State :=
  { MdStream.Arm.Finalize.satBase with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩] }

theorem finalize : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 168 1 Impl.Sm3.Arm.Stream.finalize)
    (Spec.Sm3.finalizeContract Arm.abi 168) :=
  Arm.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 19)
    (stack := 0) (bytes := 168) (m := 1)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by decide)
    (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.finalizePost_local _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sm3.finalizePostOut_local _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sm3.finalizeContract, Spec.Sm3.finalizeSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeFrameSat)

end VG.Proof.Sm3.Arm.Shared
