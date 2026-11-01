module

public import VerifiedGarbage.Proof.Bignum.Arm.MontCallArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The shared callable Montgomery product and square are constant time -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt Operand)
open VG.Proof.X25519.Arm (wp_cmp op2_reg)

theorem callCompare_ready (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : CallBodyReady base len w o a b s) :
    WP isa (.block [.cmp .r3 (.reg .r12)]) s fun t =>
      CallBodyReady base len w o a b t ∧
      t.z = (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) ∧ t.sp = s.sp := by
  refine wp_cmp (op2_reg s .r12) fun t flags eq => WP.block_nil ?_
  exact ⟨h.of_mem flags.mem (flags.rest []),
    by simpa only [h.input.aIndex, h.input.bIndex] using eq, (flags.rest []).sp⟩

theorem montCallArithmetic_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => CallBodyReady base len w o a b s ∧
      CallBodyReady base len w o a b t ∧ s.sp = t.sp)
      MontCall.arithmetic (fun _ _ => True) := by
  let P := fun s t : State => CallBodyReady base len w o a b s ∧
    CallBodyReady base len w o a b t ∧ s.sp = t.sp
  have cmp : RelCT isa P (.block [.cmp .r3 (.reg .r12)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have ready := cmp.wpDep (fun s t h => ⟨callCompare_ready s h.1, callCompare_ready t h.2.1⟩)
  unfold MontCall.arithmetic
  refine ready.seq (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    obtain ⟨_, s0, t0, _, hs, ht⟩ := h
    simp only [eval, hs.2.1, ht.2.1]
  · intro s t tr1 tr2 u v h e1 e2
    obtain ⟨⟨_, s0, t0, hp, hs, ht⟩, branch⟩ := h
    have bits : BitVec.ofNat 32 a = BitVec.ofNat 32 b := by
      have sub : BitVec.ofNat 32 a - BitVec.ofNat 32 b = 0 := by
        simpa only [eval, hs.2.1, Option.some.injEq, beq_iff_eq] using branch
      calc
        BitVec.ofNat 32 a = (BitVec.ofNat 32 a - BitVec.ofNat 32 b) + BitVec.ofNat 32 b := (BitVec.sub_add_cancel _ _).symm
        _ = BitVec.ofNat 32 b := by rw [sub]; exact BitVec.zero_add _
    have aw : a < 2 ^ 32 := by have := ha.1; omega
    have bw : b < 2 ^ 32 := by have := hb.1; omega
    have indices : a = b := by
      have natEq := congrArg BitVec.toNat bits
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt aw, Nat.mod_eq_of_lt bw] using natEq
    subst b
    exact squareBody_ct ho ha _ _ _ _ _ _
      ⟨hs.2.2.trans (hp.2.2.trans ht.2.2.symm),
        ⟨hs.1.input, hs.1.stackRead, hs.1.stackSep, hs.1.saved⟩,
        ⟨ht.1.input, ht.1.stackRead, ht.1.stackSep, ht.1.saved⟩⟩ e1 e2
  · intro s t tr1 tr2 u v h e1 e2
    obtain ⟨⟨_, s0, t0, _, hs, ht⟩, _⟩ := h
    exact montFnBody_ct ho ha hb fit _ _ _ _ _ _ ⟨hs.1.input, ht.1.input⟩ e1 e2

theorem montCallRestore_ct : RelCT isa (fun s t => s.sp = t.sp) (.block MontCall.restore)
    (fun s t => s.sp = t.sp) :=
  stackLoads_ct [(.r4, 4), (.r5, 8), (.r6, 12), (.r7, 16), (.r8, 20), (.r9, 24), (.r10, 28), (.r11, 32), (.lr, 36)]

theorem callBodyReady_of_entry (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : CallInput base len w o a b s) (u : State)
    (ready : FnBodyReady base len w o a b u) (mem : u.mem = (callPushed s).mem)
    (rest : VG.Proof.X25519.Arm.Rest [.r12] (callPushed s) u) :
    CallBodyReady base len w o a b u := by
  have saved := call_push_saved s h.stackFit
  refine ⟨ready, ?_, ?_, ?_⟩
  · rw [rest.rd, rest.wr, rest.sp]
    refine ⟨⟨State.addr (callPushed s).sp, 40⟩, List.mem_append_right _ List.mem_cons_self, ?_⟩
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  · rw [rest.sp]
    exact h.stackWorkspace.sub_left (Region.sub_prefix (by decide))
  · rw [mem, rest.sp]
    change (callPushed s).mem.readW (State.addr (s.sp - 40)) 32 = base
    simpa only [BitVec.add_zero] using (saved (.r0, 0) (by decide)).trans h.ptr

theorem montCallFn_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t => CallInput base len w o a b s ∧ CallInput base len w o a b t ∧ s.sp = t.sp)
      MontCall.code (fun _ _ => True) := by
  unfold MontCall.code
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed (rs := MontCall.savedRegs) (by decide) hs.stackFit
  have pt' := push_pushed (rs := MontCall.savedRegs) (by decide) ht.stackFit
  have es : callPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : callPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := loadStack_ct .r12 40 _ _ _ _ _ _ (by simp only [callPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, mem1, rest1⟩ := call_entry_ok s0 hs hb.1
      obtain ⟨_, t1, run2, ready2, mem2, rest2⟩ := call_entry_ok t0 ht hb.1
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have hw : 2 ≤ w := hs.width ▸ hs.layout.1
      have fit : arrAt w 8 ≤ 8 * len := hs.width ▸ hs.layout.2.2.1
      have tmpFits : arrAt w 3 + 32 ≤ 8 * len := by
        have := array_end_le (w := w) (j := 3) (k := 8) (by decide)
        omega
      have body := relCT_keep_sp (montCallArithmetic_ct (base := base) ho ha hb tmpFits) (fun _ _ h => h.2.2)
      obtain ⟨tailTrace, _⟩ := body.seq montCallRestore_ct _ _ _ _ _ _
        ⟨callBodyReady_of_entry s0 hs _ ready1 mem1 rest1,
          callBodyReady_of_entry t0 ht _ ready2 mem2 rest2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
