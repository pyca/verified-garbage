module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Wrap
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Rsa.Arm.PrivAllocCT
import VerifiedGarbage.Proof.Framework.Block

/-!
# The frames of the ARMv7 PKCS #1 v1.5 functions: correctness and constant time

`wrap_ok`: the body runs from `entered F s`, the state after the push and
the allocation; if it changes memory only within regions apart from the
push, the function returns with the calling convention's registers and
stack pointer, and its result and memory as the body left them.
`wrap_ct`: two runs with the same stack pointer leak the same trace if the
body's runs from the entered states do.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm VG.Proof.Bignum.Arm

/-- What the frame's size must be. -/
abbrev FrameOk (F : Nat) : Prop :=
  0 < F ∧ F < 4096 ∧ F % 8 = 0 ∧ encodable (BitVec.ofNat 32 F) = true

/-- The state the body starts in: after the push and the allocation. -/
def entered (F : Nat) (s : State) : State := allocated F (pcPushed s)

/-- The push's 56 bytes below the stack pointer on entry. -/
abbrev pushRegion (s : State) : Region := FrameStack.belowA s.sp 56

theorem entered_sp (F : Nat) (s : State) :
    (entered F s).sp = s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 F := rfl

theorem entered_wr (F : Nat) (s : State) :
    (entered F s).wr = ⟨State.addr (s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 F), F⟩ ::
      ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ :: s.wr := rfl

theorem entered_rd (F : Nat) (s : State) : (entered F s).rd = s.rd := rfl

theorem entered_gpr (F : Nat) (s : State) : (entered F s).gpr = s.gpr := rfl

theorem entered_mem (F : Nat) (s : State) : (entered F s).mem = (pcPushed s).mem := rfl

/-- Code never changes its permissions or the stack pointer, as a postcondition. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, hq, Exec.rdwr he⟩

theorem wrap_ok {F : Nat} (hF : FrameOk F) {body : Prog isa} {s : State} (hsp : F + 56 ≤ s.sp.toNat)
    {W : List Region} (hW : ∀ r ∈ W, (pushRegion s).Disjoint r) {Q : BitVec 32 → Mem → Prop}
    (hb : WP isa body (entered F s) fun u => Frame W (entered F s).mem u.mem ∧ Q (u.gpr .r0) u.mem) :
    WP isa (wrap F body) s fun t => abiPreserved s t ∧ Q (t.gpr .r0) t.mem := by
  have fit56 : 56 ≤ s.sp.toNat := by omega
  have allocation : F ≤ (pcPushed s).sp.toNat := by
    change F ≤ (s.sp - BitVec.ofNat 32 56).toNat
    rw [FrameStack.sub_toNat' fit56]
    omega
  unfold wrap
  refine WP.frame (by decide) fit56 (by decide) ?_
  rw [WP.seq_iff]
  refine WP.alloc hF allocation ?_
  refine WP.mono (WP.rdwr hb) ?_
  rintro u ⟨⟨frame, result⟩, -, wrU, spU⟩
  have spF : (freed F u).sp = (pcPushed s).sp := by
    change u.sp + BitVec.ofNat 32 F = _
    rw [spU]
    exact BitVec.sub_add_cancel _ _
  have wrF : (freed F u).wr = (pcPushed s).wr := by
    change u.wr.tail = _
    rw [wrU]; rfl
  have fit : (freed F u).sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spF]
    change (s.sp - BitVec.ofNat 32 56).toNat + 56 ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' fit56]
    have := s.sp.isLt
    omega
  have saved : Spill.Saved (freed F u).mem (State.addr (freed F u).sp) s.gpr pcCalleeSaved := by
    rw [spF]
    have initial := pc_push_callee_saved s fit56
    refine initial.frame (lo := 0) (hi := 56) (by decide) frame fun r hr => ?_
    change (⟨State.addr (s.sp - 56) + BitVec.ofNat 64 0, 56 - 0⟩ : Region).Disjoint r
    simp only [BitVec.add_zero, Nat.sub_zero]
    exact hW r hr
  have read : InRegions ((freed F u).rd ++ (freed F u).wr) (State.addr (freed F u).sp) 56 := by
    refine ⟨⟨State.addr (freed F u).sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrF, spF]
    exact List.mem_cons_self
  refine WP.mono (pc_restore_ok (freed F u) s.gpr fit read saved) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = u.gpr .r0 := restT.gpr .r0 (by simp [pcCalleeSaved])
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst he; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by simp [pcCalleeSaved])
    · exact restored (.r5, 20) (by simp [pcCalleeSaved])
    · exact restored (.r6, 24) (by simp [pcCalleeSaved])
    · exact restored (.r7, 28) (by simp [pcCalleeSaved])
    · exact restored (.r8, 32) (by simp [pcCalleeSaved])
    · exact restored (.r9, 36) (by simp [pcCalleeSaved])
    · exact restored (.r10, 40) (by simp [pcCalleeSaved])
    · exact restored (.r11, 44) (by simp [pcCalleeSaved])
    · exact restored (.lr, 52) (by simp [pcCalleeSaved])
  · rw [popped_sp, restT.sp, spF]
    exact BitVec.sub_add_cancel _ _
  · simp only [popped_gpr (by decide : Reg.r0 ≠ .r12), popped_mem, memT, ret]
    exact result

/-- Two runs of the frames leak the same trace if they have the same stack
pointer, room for the frames, and the body's runs from the entered states
leak the same trace. -/
theorem wrap_ct {F : Nat} (hF : FrameOk F) {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ s t, P s t → s.sp = t.sp) (hfit : ∀ s t, P s t → F + 56 ≤ s.sp.toNat)
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = entered F s ∧ b = entered F t) body fun _ _ => True) :
    RelCT isa P (wrap F body) fun _ _ => True := by
  unfold wrap
  apply RelCT.frame hsp
  intro s t tr1 tr2 u w hp e1 e2
  obtain ⟨s0, t0, h0, ps, pt⟩ := hp
  have fs := hfit _ _ h0
  have ft : F + 56 ≤ t0.sp.toNat := by rw [← hsp _ _ h0]; exact fs
  have ps' := push_pushed (s := s0) (rs := pushRegs) (by decide) (by change 56 ≤ s0.sp.toNat; omega)
  have pt' := push_pushed (s := t0) (rs := pushRegs) (by decide) (by change 56 ≤ t0.sp.toNat; omega)
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  have alloc : RelCT isa (fun a b => a = pcPushed s0 ∧ b = pcPushed t0) (.frame (.alloc F) body (.free F))
      fun a b => a.sp = b.sp := by
    refine relCT_keep_sp (Proof.Rsa.Arm.allocation_ct ?_) fun a b h => by rw [h.1, h.2]; simp [hsp _ _ h0]
    intro a b tr1 tr2 u v' h e1 e2
    obtain ⟨_, _, ⟨rfl, rfl⟩, pa, pb⟩ := h
    have alloc_s : isa.push (.alloc F) (pcPushed s0) = some (entered F s0) := by
      have hn : F ≤ (pcPushed s0).sp.toNat := by
        change F ≤ (s0.sp - BitVec.ofNat 32 56).toNat
        rw [FrameStack.sub_toNat' (by omega)]; omega
      simp only [isa, push, hF.1, hF.2.1, hF.2.2.1, hF.2.2.2, hn, and_self, ite_true]
      rfl
    have alloc_t : isa.push (.alloc F) (pcPushed t0) = some (entered F t0) := by
      have hn : F ≤ (pcPushed t0).sp.toNat := by
        change F ≤ (t0.sp - BitVec.ofNat 32 56).toNat
        rw [FrameStack.sub_toNat' (by omega)]; omega
      simp only [isa, push, hF.1, hF.2.1, hF.2.2.1, hF.2.2.2, hn, and_self, ite_true]
      rfl
    have ea : entered F s0 = a := Option.some.inj (alloc_s.symm.trans pa)
    have eb : entered F t0 = b := Option.some.inj (alloc_t.symm.trans pb)
    subst a; subst b
    exact hb _ _ _ _ _ _ ⟨s0, t0, h0, rfl, rfl⟩ e1 e2
  have restore : RelCT isa (fun s t => s.sp = t.sp) (.block Impl.Bignum.Arm.PcFn.restore)
      (fun s t => s.sp = t.sp) := stackLoads_ct pcCalleeSaved
  exact ⟨((alloc.seq restore) _ _ _ _ _ _ ⟨rfl, rfl⟩ e1 e2).1, trivial⟩

end VG.Proof.RsaPkcs1Sig.Arm
