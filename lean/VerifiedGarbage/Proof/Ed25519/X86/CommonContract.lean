import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.Taint

/-! Untrusted cdecl facts shared by the Ed25519 primitives. No particular
argument list or output is assumed by scratch setup and register saving. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

structure ScratchPre (s₀ : State) (scidx argc : Nat) : Prop where
  index : scidx < argc
  wr : scR 8192 (arg s₀ scidx) ∈ s₀.wr
  fit : (arg s₀ scidx).toNat + 8192 ≤ 2 ^ 32
  args : (⟨argAddr s₀ 0, 4 * argc⟩ : Region) ∈ s₀.rd ++ s₀.wr
  sp_fit : (s₀.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32
  args_sc : (⟨argAddr s₀ 0, 4 * argc⟩ : Region).Disjoint (scR 8192 (arg s₀ scidx))
  ret_sc : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (scR 8192 (arg s₀ scidx))
  /-- The 8 bytes of stack a call of a function of the working space uses, apart from the
  scratch. -/
  stk : 8 ≤ (s₀.gpr .esp).toNat ∧ (scR 8192 (arg s₀ scidx)).Disjoint (callStk s₀)

theorem ScratchPre.callStk_eq {s : State} {scidx argc : Nat} (hp : ScratchPre s scidx argc) :
    callStk s = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8, 8⟩ := by
  simp only [callStk, VG.X86.Taint.sub_setWidth hp.stk.1]

/-- The return address lies apart from the stack a call uses. -/
theorem ScratchPre.ret_stk {s : State} {scidx argc : Nat} (hp : ScratchPre s scidx argc) :
    (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (callStk s) := by
  rw [hp.callStk_eq]; exact Offset.base_disjoint_below _ (by decide)

/-- The arguments lie apart from the stack a call uses. -/
theorem ScratchPre.args_stk {s : State} {scidx argc : Nat} (hp : ScratchPre s scidx argc) :
    (⟨argAddr s 0, 4 * argc⟩ : Region).Disjoint (callStk s) := by
  have hf := hp.sp_fit
  have hi := hp.index
  have e : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    addr_eq (x := s.gpr .esp) (k := 4) (by omega)
  rw [hp.callStk_eq, e]
  exact Offset.disjoint_below _ (by omega)

theorem ScratchPre.arg_contains {s : State} {scidx argc i : Nat} (hp : ScratchPre s scidx argc)
    (hi : i < argc) : (⟨argAddr s 0, 4 * argc⟩ : Region).Contains
      (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  sub_contains (x := s.gpr .esp) (a := 4) (k := 4 * argc) hp.sp_fit
    (by omega_using []) (by omega_using [hi]) (by decide)

theorem ScratchPre.argIn {s : State} {scidx argc i : Nat} (hp : ScratchPre s scidx argc)
    (hi : i < argc) : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨_, hp.args, hp.arg_contains hi⟩

theorem ScratchPre.arg_same {s : State} {scidx argc i : Nat} (hp : ScratchPre s scidx argc)
    {m : Mem} (hf : Frame [scR 8192 (arg s scidx), callStk s] s.mem m) (hi : i < argc) :
    m.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i :=
  hf.readW (hp.arg_contains hi) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.args_sc
    · exact hp.args_stk) (by decide)

/-- The callee-saved registers and their slots in the scratch space. -/
def savedSlots : Spill.Slots := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

theorem savedSlots_bound : ∀ p ∈ savedSlots, p.2 + 4 ≤ 16 := by decide

structure Saved (s₀ : State) (x : BitVec 32) (s : State) : Prop where
  edi : s.gpr .edi = x
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scR 8192 x, callStk s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr x) s₀.gpr savedSlots
  /-- The stack a call uses lies apart from the workspace. -/
  stk : 8 ≤ (s₀.gpr .esp).toNat ∧ (scR 8192 x).Disjoint (callStk s₀)

theorem Saved.ctx {s₀ s : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hfit : x.toNat + 8192 ≤ 2 ^ 32) (hw : scR 8192 x ∈ s₀.wr)
    (hstk : 8 ≤ (s₀.gpr .esp).toNat ∧ (scR 8192 x).Disjoint (callStk s₀)) : Ctx x s :=
  ⟨h.edi, hfit, h.wr ▸ hw, by decide, fun _ _ => by rw [callStk, h.esp]; exact hstk⟩

/-- A component writing above the saved words, and to the stack a call uses, preserves the
common ABI invariant. -/
theorem Saved.of_frame {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hk : ScalarKeep s t) {rs : List Region}
    (hf : Frame rs s.mem t.mem)
    (hsub : ∀ r ∈ rs, r.Sub (scR 8192 x) ∨ r = callStk s)
    (hsep : ∀ p ∈ savedSlots, ∀ r ∈ rs, (sub x p.2 4).Disjoint r) : Saved s₀ x t :=
  ⟨hk.edi.trans h.edi, hk.esp.trans h.esp, hk.rd.trans h.rd, hk.wr.trans h.wr,
    h.frame.trans (hf.sub fun r hr => by
      rcases hsub r hr with hs | rfl
      · exact ⟨_, List.mem_cons_self .., hs⟩
      · exact ⟨_, by simp [callStk, h.esp], fun _ h => h⟩),
    h.saved.of_readW fun p hp => wd_frame hf (hsep p hp), h.stk⟩

theorem Saved.of_offset {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hk : ScalarKeep s t) {o n : Nat}
    (hf : Frame [sub x o n] s.mem t.mem) (ho : 16 ≤ o) (hn : o + n ≤ 8192)
    (ho' : o < 8192) : Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr; rw [List.mem_singleton.mp hr, scR_eq]
    exact .inl (sub_sub hx (Nat.zero_le _) hn ho')
  · intro p hp r hr; rw [List.mem_singleton.mp hr]
    have := savedSlots_bound p hp
    exact sub_disj (by omega_using [hx, this]) (by omega_using [hx, hn]) (Or.inl (by omega_using [this, ho]))

/-- `Saved.of_offset` for a frame with the stack a call uses. -/
theorem Saved.of_offsetS {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hk : ScalarKeep s t) {o n : Nat}
    (hf : Frame [sub x o n, callStk s] s.mem t.mem) (ho : 16 ≤ o) (hn : o + n ≤ 8192)
    (ho' : o < 8192) : Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [scR_eq]; exact .inl (sub_sub hx (Nat.zero_le _) hn ho')
    · exact .inr rfl
  · intro p hp r hr
    have := savedSlots_bound p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega_using [hx, this]) (by omega_using [hx, hn]) (Or.inl (by omega_using [this, ho]))
    · rw [callStk, h.esp]
      exact h.stk.2.sub_left (by
        rw [scR_eq]; exact sub_sub hx (Nat.zero_le _) (by omega_using [this]) (by omega_using [this]))

end VG.Proof.Ed25519.X86
