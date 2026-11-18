module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sm3.X86.Compress
public import VerifiedGarbage.Proof.Sm3.X86.Lit
public import VerifiedGarbage.Proof.Sm3.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Sm3.Stream
import VerifiedGarbage.Proof.Sm3.StateMem
public import VerifiedGarbage.Proof.Sm3.X86.Contract
public import VerifiedGarbage.Impl.Sm3.X86.Stream
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.MdStream.X86.Common
meta import VerifiedGarbage.Proof.Sm3.Stream
meta import VerifiedGarbage.Proof.Sm3.StateMem
meta import VerifiedGarbage.Proof.Sm3.X86.Contract
meta import VerifiedGarbage.Impl.Sm3.X86.Stream
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm3.X86.Lit
public import VerifiedGarbage.Proof.MdStream.X86.Finalize
public import VerifiedGarbage.Proof.MdStream.X86.Update
import VerifiedGarbage.Proof.MdStream.X86.Words
public import VerifiedGarbage.Proof.Sm3.Md
meta import VerifiedGarbage.Proof.MdStream.X86.Finalize
meta import VerifiedGarbage.Proof.MdStream.X86.Update
meta import VerifiedGarbage.Proof.MdStream.X86.Words
meta import VerifiedGarbage.Proof.Sm3.Md
meta import VerifiedGarbage.Proof.Sm3.X86.Compress
meta import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! ### `Sm3.X86.Stream.Md`, which only this module used -/

section

/-!
# Streaming SM3 on x86 (32-bit): `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86/`) for SM3's instance (`Proof/Sm3/Md.lean`) with 160
bytes of scratch space, given what SM3's own pieces do: its length field and
digest (`shape`), that its compression function is verified (`callee`), and
that the taint analysis accepts its code (which it checks together with the
compression function's).
-/

@[expose] public section

namespace VG.Proof.Sm3.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86

abbrev params := Impl.Sm3.X86.Stream.params

theorem dims : Dims params 160 := ⟨.inl rfl, by decide, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len _ hfit hlo hhi ho := len64_ok (so := params.so) (d := params.N + params.B - params.L) (be := true)
    (by have : params.N + params.B - params.L + 8 = params.N + params.B := rfl; omega_using [hfit, this]) hlo hhi
    (ho _ (Nat.le_refl _) (by decide)) (ho _ (by decide) (by decide))
  out _ hbx hax hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) hbx hax hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ =>
      ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Sm3.X86.compress :=
  ⟨compress_verified.1, NoSp.of_all (by lit_decide), by lit_decide⟩

namespace Update

theorem update_verified : Verified X86.target Impl.Sm3.X86.Stream.update Proof.Sm3.updateX86 :=
  have h := MdStream.X86.Update.verified (name := "vg_sm3_compress") dims callee
    (VG.Taint.constantTime (A := taint) (MdStream.X86.Update.τ₀ params 160)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Update.agree₀ dims h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86.Update.sat params 160

end Update

namespace Finalize

theorem finalize_verified : Verified X86.target Impl.Sm3.X86.Stream.finalize Proof.Sm3.finalizeX86 :=
  have h := MdStream.X86.Finalize.verified (name := "vg_sm3_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (MdStream.X86.Finalize.τ₀ params 160)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀ dims h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86.Finalize.sat params 160

end Finalize

end VG.Proof.Sm3.X86.Stream

end

end

/-! ### `Sm3.X86.Stream.Init`, which only this module used -/

section

/-!
# Streaming SM3 on x86 (32-bit): `init`
-/

@[expose] public section

namespace VG.Proof.Sm3.X86.Stream

open VG VG.X86 VG.Impl.Sm3.X86.Stream
open VG.Impl.Sm3.X86 (at_)
open VG.Proof.MdStream.X86 (wp_movi wp_movm wp_store contains_addr)
open VG.Spec.Sm3 (stateAt iv)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- The two instructions storing the word `x` at `[eax + 4 * k]`. -/
def word (x : BitVec 32) (k : Nat) : List Instr := [.mov .ecx (.imm x), .store (at_ .eax (4 * k)) .ecx]

theorem init_eq : init = .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.block (word iv[0] 0 ++ word iv[1] 1 ++ word iv[2] 2 ++ word iv[3] 3 ++ word iv[4] 4 ++
      word iv[5] 5 ++ word iv[6] 6 ++ word iv[7] 7)) := rfl

theorem word_ok {x : BitVec 32} {k : Nat} {rest : List Instr} {s : State} {Q : State → Prop}
    {st : BitVec 32} (heax : s.gpr .eax = st) (hout : InRegions s.wr (addr st (4 * k)) 4)
    (kk : ∀ s', s'.gpr .eax = st → (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → s'.mem = s.mem.writeW (addr st (4 * k)) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word x k ++ rest)) s Q := by
  simp only [word, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => wp_store (a := addr st (4 * k))
    (by rw [ea_at, u₁.other _ (by decide), heax]) (by rw [u₁.wr]; exact hout) fun s₂ u₂ => ?_
  refine kk s₂ (by rw [u₂.gpr, u₁.other _ (by decide), heax]) (fun r hr => by rw [u₂.gpr, u₁.other r hr])
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) ?_
  rw [u₂.mem, u₁.gpr, u₁.mem]

theorem init_correct {s₀ : State} (hp : Proof.Sm3.initX86.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sm3.initX86.post s₀ s' := by
  obtain ⟨hrd, hwr, hargs, hret, hfit, hsp⟩ := hp
  let st := arg s₀ 0
  try rewrite [show arg s₀ 0 = st from rfl] at *
  have hst : st = arg s₀ 0 := rfl
  have o : ∀ k, k < 8 → InRegions s₀.wr (addr st (4 * k)) 4 :=
    fun k hk => ⟨⟨st.setWidth 64, 96⟩, by simp [hwr], contains_addr (by omega_using [hk]) (by omega_using []) hfit⟩
  rw [init_eq]
  refine WP.seq (wp_movm (a := addr (s₀.gpr .esp) 4) (ea_at _ _ _)
    ⟨⟨argAddr s₀ 0, 4⟩, by simp [hrd], Region.contains_self _ _⟩ fun s₁ u₁ => WP.block_nil ?_)
  have e1 : s₁.gpr .eax = st := u₁.gpr
  have w1 : s₁.wr = s₀.wr := u₁.wr
  rw [← List.append_nil (_ ++ word iv[7] 7)]
  simp only [List.append_assoc]
  refine word_ok e1 (by rw [w1]; exact o 0 (by omega_using [])) fun s2 a2 g2 _ wr2 m2 => ?_
  refine word_ok a2 (by rw [wr2, w1]; exact o 1 (by omega_using [])) fun s3 a3 g3 _ wr3 m3 => ?_
  refine word_ok a3 (by rw [wr3, wr2, w1]; exact o 2 (by omega_using [])) fun s4 a4 g4 _ wr4 m4 => ?_
  refine word_ok a4 (by rw [wr4, wr3, wr2, w1]; exact o 3 (by omega_using [])) fun s5 a5 g5 _ wr5 m5 => ?_
  refine word_ok a5 (by rw [wr5, wr4, wr3, wr2, w1]; exact o 4 (by omega_using [])) fun s6 a6 g6 _ wr6 m6 => ?_
  refine word_ok a6 (by rw [wr6, wr5, wr4, wr3, wr2, w1]; exact o 5 (by omega_using []))
    fun s7 a7 g7 _ wr7 m7 => ?_
  refine word_ok a7 (by rw [wr7, wr6, wr5, wr4, wr3, wr2, w1]; exact o 6 (by omega_using []))
    fun s8 a8 g8 _ wr8 m8 => ?_
  refine word_ok a8 (by rw [wr8, wr7, wr6, wr5, wr4, wr3, wr2, w1]; exact o 7 (by omega_using []))
    fun s9 _ g9 _ _ m9 => WP.block_nil ?_
  have k9 : ∀ r, r ≠ .ecx → r ≠ .eax → s9.gpr r = s₀.gpr r := fun r h h' => by
    rw [g9 r h, g8 r h, g7 r h, g6 r h, g5 r h, g4 r h, g3 r h, g2 r h, u₁.other r h']
  have ha : ∀ k, k < 8 → addr st (4 * k) = st.setWidth 64 + BitVec.ofNat 64 (4 * k) :=
    fun k hk => addr_eq (by omega_using [hfit, hk])
  have hm : s9.mem = Proof.Sm3.StateMem.writeState s₀.mem (st.setWidth 64) iv := by
    rw [m9, m8, m7, m6, m5, m4, m3, m2, u₁.mem, ha 0 (by omega_using []), ha 1 (by omega_using []), ha 2 (by omega_using []),
      ha 3 (by omega_using []), ha 4 (by omega_using []), ha 5 (by omega_using []), ha 6 (by omega_using []), ha 7 (by omega_using [])]
    rfl
  have hf : Frame [⟨st.setWidth 64, 96⟩] s₀.mem s9.mem := by
    rw [m9, m8, m7, m6, m5, m4, m3, m2, u₁.mem]
    have c : ∀ k, k < 8 → (⟨st.setWidth 64, 96⟩ : Region).Contains (addr st (4 * k)) (32 / 8) :=
      fun k hk => contains_addr (by omega_using [hk]) (by omega_using []) hfit
    have mm := List.mem_singleton_self (⟨st.setWidth 64, 96⟩ : Region)
    exact ((((((((Frame.refl _ _).writeW mm _ (c 0 (by omega_using []))).writeW mm _ (c 1 (by omega_using []))).writeW
      mm _ (c 2 (by omega_using []))).writeW mm _ (c 3 (by omega_using []))).writeW mm _ (c 4 (by omega_using []))).writeW
      mm _ (c 5 (by omega_using []))).writeW mm _ (c 6 (by omega_using []))).writeW mm _ (c 7 (by omega_using []))
  refine ⟨⟨fun r hr => k9 r ?_ ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)
  · show Spec.Sm3.Repr s9.mem (st.setWidth 64) []
    rw [hm]
    exact Proof.Sm3.Stream.repr_nil (Proof.Sm3.StateMem.stateAt_writeState _ _ _)

/-- Memory holding the argument `0x1000` at `0x4004`. -/
def initSatMem : Mem := fun a => if a = 0x4005 then 0x10 else 0

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := initSatMem
  rd := [⟨0x4004, 4⟩]
  wr := [⟨0x1000, 96⟩]

theorem initSat_pre : Proof.Sm3.initX86.pre initSat := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have e : argAddr initSat 0 = 0x4004 := by decide
  simp only [Proof.Sm3.initX86, a0, e]
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-- The initial taint: the argument is public. -/
def initτ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 8 }

theorem init_agree₀ {s₁ s₂ : State} (h₁ : Proof.Sm3.initX86.pre s₁) (h₂ : Proof.Sm3.initX86.pre s₂)
    (hpub : Proof.Sm3.initX86.pub s₁ s₂) : VG.X86.Taint.Agree initτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0⟩ := hpub
  have wf : ∀ s, Proof.Sm3.initX86.pre s → VG.X86.Taint.Wf initτ₀ s := by
    intro s hs
    obtain ⟨-, hw, hd, hr, -, hsp⟩ := hs
    refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hsp, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
    simp only [hw, List.mem_singleton]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 4) (by omega_using [hsp]) hr hd
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf _ h₁, wf _ h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [initτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · simp only [initτ₀] at hk
    rw [show VG.X86.Taint.depth initτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq h₁.2.2.2.2.2 h4 hk, VG.X86.Taint.argByte_eq h₂.2.2.2.2.2 h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using [])),
      show (k - 4) / 4 = 0 by omega_using [hk]]
    exact congrArg _ a0

theorem init_verified : Verified X86.target init Proof.Sm3.initX86 := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, initSat_pre⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) initτ₀ (fun _ _ h₁ h₂ hp => init_agree₀ h₁ h₂ hp)
      (by taint_decide)

end VG.Proof.Sm3.X86.Stream

end

end

/-!
# SM3 on x86: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/X86/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

The shared contract of `update` lets it write its arguments: the per-target
contract is first widened to writable arguments (`Verified.narrowTo`, the
same code running with the same trace and result), then moved to the shared
one. `update` and `finalize` call the
compression function, using the 20 bytes of stack below the return address.

`update` and `finalize` keep their working space (20 words: the compression
function's 112 bytes, then what the streaming code saves) in a frame of their
own: they are `updateScratch` and `finalizeScratch` (the shared contracts
with the working space as an argument, `Proof/Sm3/Scratch.lean`) run in a
frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sm3.X86.Shared

open _root_.VG.X86

/-- `updateX86` with its arguments writable. -/
def updateWide : Contract X86.isa :=
  { Proof.Sm3.updateX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 96⟩
      let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 160⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [data] ∧ s.wr = [state, scratch, args] ∧
      state.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧
      data.Disjoint state ∧ data.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
      stack.Disjoint data ∧
      (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 160 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 }

/-- Rewrites the per-target contracts at a narrowed state (`arg` does not
unfold cheaply). -/
tactic_template "narrow" : tactic =>
  `(tactic| simp only [Proof.Sm3.updateX86, updateWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
                     State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr])
tactic_template "narrow" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| simp only [Proof.Sm3.updateX86, updateWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
                     State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $loc)

/-- `update` only reads its arguments. -/
theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified X86.target Impl.Sm3.X86.Stream.update updateWide :=
  Verified.narrowTo Proof.Sm3.X86.Stream.Update.update_verified
    (fun s => [⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨argAddr s 0, 24⟩])
    (fun s => [⟨(arg s 0).setWidth 64, 96⟩, ⟨(arg s 5).setWidth 64, 160⟩])
    (fun _ h => by
      obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩ := h
      narrow
      exact ⟨trivial, trivial, h₃, h₆, h₇, h₄, h₅, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sm3.X86.Stream.Update.sat with
    rd := [⟨0x2000, 0⟩], wr := [⟨0x1000, 96⟩, ⟨0x3000, 160⟩, ⟨0x5004, 24⟩] }

theorem init :
    Verified X86.target Impl.Sm3.X86.Stream.init (Spec.Sm3.initContract X86.abi) :=
  Proof.Sm3.X86.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sm3.X86.Stream.initSat, Proof.Sm3.X86.Stream.initSatMem, X86.arg, X86.argAddr, Mem.readW,
        Mem.read] using Proof.Sm3.X86.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Proof.Sm3.updateScratchContract X86.abi 20 20) := by
  contract_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig, updateWide,
    Proof.Sm3.updateX86, Proof.Sm3.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateSat, Proof.Sm3.X86.Stream.Update.sat, MdStream.X86.Update.sat, MdStream.X86.Update.sat₀,
      MdStream.X86.Update.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using updateSat

theorem updateScratch :
    Verified X86.target Impl.Sm3.X86.Stream.update (Proof.Sm3.updateScratchContract X86.abi 20 20) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeScratch :
    Verified X86.target Impl.Sm3.X86.Stream.finalize (Proof.Sm3.finalizeScratchContract X86.abi 20 20) :=
  Proof.Sm3.X86.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig, Spec.Sm3.finalizeSig,
      Proof.Sm3.finalizeX86, Proof.Sm3.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sm3.X86.Stream.Finalize.sat, MdStream.X86.Finalize.sat, MdStream.X86.Finalize.sat₀,
        MdStream.X86.Finalize.satMem, Impl.Sm3.X86.Stream.params, X86.arg, X86.argAddr, Mem.readW,
        Mem.read] using Proof.Sm3.X86.Stream.Finalize.sat)

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : State :=
  { MdStream.X86.Update.sat₀ with rd := [⟨0x2000, 0⟩], wr := [⟨0x1000, 96⟩, ⟨0x5004, 20⟩] }

theorem update : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 188 5 Impl.Sm3.X86.Stream.update)
    (Spec.Sm3.updateContract X86.abi (20 + 188)) :=
  X86.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 20) (bytes := 188)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.updatePost_local _) (fun vs m m₁ m₂ r hl _ hb => Proof.Sm3.updatePostOut_local _ vs m m₁ m₂ r hl hb)
    (by implies_sat [Spec.Sm3.updateContract, Spec.Sm3.updateSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      [updateFrameSat, MdStream.X86.Update.sat₀, MdStream.X86.Update.satMem, X86.arg, X86.argAddr,
        Mem.readW, Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : State :=
  { MdStream.X86.Finalize.sat₀ with wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x5004, 16⟩] }

theorem finalize : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 184 4 Impl.Sm3.X86.Stream.finalize)
    (Spec.Sm3.finalizeContract X86.abi (20 + 184)) :=
  X86.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 20) (bytes := 184)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.finalizePost_local _) (fun vs m m₁ m₂ r hl _ hb => Proof.Sm3.finalizePostOut_local _ vs m m₁ m₂ r hl hb)
    (by implies_sat [Spec.Sm3.finalizeContract, Spec.Sm3.finalizeSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalizeFrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalizeFrameSat)

end VG.Proof.Sm3.X86.Shared
