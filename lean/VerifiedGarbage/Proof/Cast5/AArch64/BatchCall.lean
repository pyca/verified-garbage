module

public import VerifiedGarbage.Proof.Cast5.AArch64.TblBatch
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Cast5.AArch64.TblBatch
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
meta import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Calling the shared CAST5 batch

The arithmetic and its memory frame are unchanged. The caller additionally
uses `x10` for its link, and passes the round count in `x14` around the
ABI's call-clobbered `x16` and `x17`.
-/

@[expose] public section
namespace VG.Proof.Cast5.AArch64.Tbl
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Aes.AArch64 (movR)
open VG.Proof.Modes.AArch64 (KeepsReg)
open VG.Spec.Cast5 (Schedule blockAt)

/-- The call adapter's additional temporary. -/
def callG : List Reg := .x9 :: .x10 :: batchG

/-- The helper initializes its own static-table pointer. -/
structure CallPre (s : State) (k : Schedule) : Prop where
  consts : VG.Proof.Blowfish.AArch64.Consts s
  sched : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128
  key : ∀ j < 32, s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0

structure BatchCallPost (k : Schedule) (n : Nat) (up : Bool) (s t : State) : Prop where
  out : ∀ j < 16, blockAt t.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * j)) =
    blockOut k n up (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * j)))
  frame : Frame [⟨s.gpr .x4, 128⟩] s.mem t.mem
  x4 : t.gpr .x4 = s.gpr .x4
  gpr : ∀ r, r ∉ callG → t.gpr r = s.gpr r
  v : ∀ r, r ∉ roundV → t.v r = s.v r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  syms : t.syms = s.syms

theorem move_run (s : State) (d n : Reg) :
    runBlock isa [movR d n] s = some (s.write .x d (s.gpr n)) := by
  simp only [movR, runBlock_cons, exec_addImm_x (by decide : 0 < 4096),
    Modes.AArch64.read_x, BitVec.add_zero, runStep_some, runBlock_nil]

theorem batchFn_eq (up : Bool) : batchFn up = .seq (.block [movR .x16 .x14, .adrSym .x9 planesSym]) (batch up) := by
  cases up <;> rfl

theorem batchCall_ok (up : Bool) {s : State} {k : Schedule} {n : Nat}
    (P : CallPre s k) (hn : n = 12 ∨ n = 16) (h16 : s.gpr .x16 = BitVec.ofNat 64 n)
    (hW : ∀ j < 8, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (batchCall up) s (BatchCallPost k n up s) := by
  let s₁ := s.write .x .x10 (s.gpr .x30)
  let s₂ := s₁.write .x .x14 (s₁.gpr .x16)
  let b := s₂.callEntry
  let a₀ := b.write .x .x16 (b.gpr .x14)
  let a := a₀.write .x .x9 (a₀.syms planesSym)
  have a_other (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) (h14 : r ≠ .x14)
      (h16 : r ≠ .x16) (h17 : r ≠ .x17) (h30 : r ≠ .x30) : a.gpr r = s.gpr r := by
    rw [gpr_write_of_ne _ _ _ h9, gpr_write_of_ne _ _ _ h16, State.callEntry_gpr _ (by simp [linkRegs, h16, h17, h30]),
      gpr_write_of_ne _ _ _ h14, gpr_write_of_ne _ _ _ h10]
  have a16 : a.gpr .x16 = s.gpr .x16 := by
    rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_self, BitVec.setWidth_eq, State.callEntry_gpr _ (by decide),
      gpr_write_self, BitVec.setWidth_eq, gpr_write_of_ne _ _ _ (by decide)]
  have a4 : a.gpr .x4 = s.gpr .x4 := a_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have a0 : a.gpr .x0 = s.gpr .x0 := a_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have a9 : a.gpr .x9 = s.syms planesSym := by
    rw [gpr_write_self, BitVec.setWidth_eq, show a₀.syms = s.syms from rfl]
  have am : a.mem = s.mem := rfl
  have ard : a.rd = s.rd := rfl
  have awr : a.wr = s.wr := rfl
  have av : a.v = s.v := rfl
  have asp : a.sp = s.sp := rfl
  have asym : a.syms = s.syms := rfl
  have PA : CPre a k := ⟨by rw [a9, asym],
    by simpa only [Proof.Blowfish.AArch64.Consts, av] using P.consts,
    by rw [ard, awr, a0]; exact P.sched, by intro j hj; rw [am, a0]; exact P.key j hj⟩
  obtain ⟨tr, u, eu, pu⟩ := batch_ok up PA hn (a16.trans h16)
    (fun j hj => by rw [awr, a4]; exact hW j hj)
  have u30 : u.gpr .x30 = b.gpr .x30 := by
    rw [pu.gpr _ (by decide), gpr_write_of_ne _ _ _ (by decide), gpr_write_of_ne _ _ _ (by decide)]
  have u10 : u.gpr .x10 = s.gpr .x30 := by
    rw [pu.gpr _ (by decide), gpr_write_of_ne _ _ _ (by decide), gpr_write_of_ne _ _ _ (by decide),
      State.callEntry_gpr _ (by decide), gpr_write_of_ne _ _ _ (by decide),
      gpr_write_self, BitVec.setWidth_eq]
  have body : WP isa (batchFn up) b (fun t => t = u) := by
    rw [batchFn_eq]
    refine WP.seq (WP.of_runBlock ⟨a, ?_, ⟨tr, u, eu, rfl⟩⟩)
    change runBlock isa ([movR .x16 .x14] ++ [.adrSym .x9 planesSym]) b = some a
    rw [Modes.AArch64.runBlock_app, move_run, Option.bind_some]
    rw [runBlock_cons, exec_adrSym, runStep_some, runBlock_nil]
  obtain ⟨tr', u', eu', hu⟩ := body
  subst u'
  have ret : isa.ret b u = some u := by simp only [isa, VG.AArch64.ret, u30, ↓reduceIte]
  have call : WP isa (.call (if up then "vg_cast5_batch_encrypt" else "vg_cast5_batch_decrypt") (batchFn up))
      s₂ (fun t => t = u) := ⟨_, u, Exec.call (call_callEntry s₂) eu' ret, rfl⟩
  unfold batchCall
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, ?_⟩)
  · change runBlock isa ([movR .x10 .x30] ++ [movR .x14 .x16]) s = some s₂
    rw [Modes.AArch64.runBlock_app, move_run, Option.bind_some]
    exact move_run s₁ .x14 .x16
  refine WP.seq (WP.mono call fun t ht => ?_)
  subst t
  let v := u.write .x .x30 (u.gpr .x10)
  refine WP.of_runBlock ⟨v, move_run u _ _, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simpa only [v, mem_write, am, a4] using pu.out j hj
  · simpa only [v, mem_write, am, a4] using pu.frame
  · rw [gpr_write_of_ne _ _ _ (by decide), pu.x4, a4]
  · intro r hr
    by_cases h30 : r = .x30
    · subst r; rw [gpr_write_self, BitVec.setWidth_eq, u10]
    · have hb : r ∉ batchG := fun h => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
      have h9 : r ≠ .x9 := fun h => hr (by rw [h]; exact List.mem_cons_self)
      have h10 : r ≠ .x10 := fun h => hr (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      rw [gpr_write_of_ne _ _ _ h30, pu.gpr r hb]
      by_cases h16' : r = .x16
      · subst r; exact a16
      · exact a_other r h9 h10 (fun h => hb (by rw [h]; decide)) h16'
          (fun h => hb (by rw [h]; decide)) h30
  · intro r hr; rw [show v.v = u.v from rfl, pu.v r hr, av]
  · rw [show v.rd = u.rd from rfl, pu.rd, ard]
  · rw [show v.wr = u.wr from rfl, pu.wr, awr]
  · rw [show v.sp = u.sp from rfl, pu.sp, asp]
  · rw [show v.syms = u.syms from rfl, pu.syms, asym]

theorem move_value {s t : State} {tr : List Leak} {d n : Reg}
    (h : Exec isa (.block [movR d n]) s tr t) : t.gpr d = s.gpr n := by
  have hw : WP isa (.block [movR d n]) s (fun t => t.gpr d = s.gpr n) :=
    WP.of_runBlock ⟨s.write .x d (s.gpr n), move_run s d n,
      by rw [gpr_write_self, BitVec.setWidth_eq]⟩
  obtain ⟨tr', u, eu, hu⟩ := hw
  rw [(Exec.det h eu).2]
  exact hu

theorem callHead_value {s t : State} {tr : List Leak}
    (h : Exec isa (.block [movR .x10 .x30, movR .x14 .x16]) s tr t) :
    t.gpr .x10 = s.gpr .x30 := by
  let a := s.write .x .x10 (s.gpr .x30)
  let b := a.write .x .x14 (a.gpr .x16)
  have hw : WP isa (.block [movR .x10 .x30, movR .x14 .x16]) s
      (fun t => t.gpr .x10 = s.gpr .x30) := by
    refine WP.of_runBlock ⟨b, ?_, ?_⟩
    · change runBlock isa ([movR .x10 .x30] ++ [movR .x14 .x16]) s = some b
      rw [Modes.AArch64.runBlock_app, move_run, Option.bind_some]
      exact move_run a .x14 .x16
    · rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_self, BitVec.setWidth_eq]
  obtain ⟨tr', u, eu, hu⟩ := hw
  rw [(Exec.det h eu).2]
  exact hu

theorem batchCall_keeps_link (up : Bool) : KeepsReg .x30 (batchCall up) := by
  intro s tr t h
  unfold batchCall at h
  cases h with
  | seq hA hR =>
    cases hR with
    | seq hC hB =>
      have hc : (batchFn up).allInstrs (fun i => !clobbers i .x10) = true := by
        cases up <;> lit_decide
      rw [Code.allInstrs_eq] at hc
      have g := Exec.gpr (fun i hi => by simpa using List.all_eq_true.mp hc i hi) hC
        (.inr (by decide : Reg.x10 ∉ linkRegs))
      exact (move_value hB).trans (g.trans (callHead_value hA))

/-- Add the preserved link to a weakest precondition, including calls. -/
theorem keep_link {c : Prog isa} {s : State} {Q : State → Prop}
    (hk : KeepsReg .x30 c) (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ ∀ r ∈ [Reg.x30], t.gpr r = s.gpr r := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, hq, fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact hk _ _ _ he⟩

end VG.Proof.Cast5.AArch64.Tbl
