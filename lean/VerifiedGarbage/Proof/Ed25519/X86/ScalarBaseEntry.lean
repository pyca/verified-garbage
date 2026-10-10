import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.X86.CombSelect
import VerifiedGarbage.Proof.Framework.X86.SymFrame

/-!
# The comb's tables' address at the entry of `vg_ed25519_scalar_base` and `vg_x25519_base`

`combAddr 2` forms the static's address in a balanced four-byte CALL frame below `esp`
(`symFrame_ok`) and stores it at byte `combTbl` of the workspace: the rest of the function
starts (`BodyPre`) from the same regions and arguments, with the address there and the tables
readable (`TblAt`), and what it preserves of its own start the function preserves of its entry
(`Prologue`).
-/

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

/-- What the function's body needs. -/
def BodyPre (s : State) : Prop :=
  BaseRegions s ∧ wd s.mem (arg s 2) combTbl = s.syms combSym ∧
    TblAt (arg s 2) (s.syms combSym) s ∧ (TBL ((s.syms combSym).setWidth 64)).Disjoint (callStk s)

/-- The state `t` after the prologue, from the entry `s`. -/
structure Prologue (s t : State) : Prop where
  pre : BodyPre t
  gpr : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  ret : t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32
  args : ∀ j < 3, arg t j = arg s j
  input : Spec.Ed25519.bytesAt t.mem ((arg s 1).setWidth 64) 32 =
    Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32
  syms : t.syms = s.syms

/-- The static's address's frame, within the stack a call uses. -/
theorem below4_sub {sp : BitVec 32} (h : 8 ≤ sp.toNat) :
    Region.Sub (below sp 4) ⟨(sp - BitVec.ofNat 32 8).setWidth 64, 8⟩ := by
  simp only [below, Taint.sub_setWidth (show 4 ≤ sp.toNat by omega), Taint.sub_setWidth h]
  exact Offset.sub_below _ (by decide) (by decide)

theorem combAddr_ok {s : State} (h : scalarBaseLocal.pre s) : WP isa (combAddr 2) s (Prologue s) := by
  obtain ⟨hr, _, held⟩ := h
  obtain ⟨hp, hi, _⟩ := scalarBase_pre hr
  have h20 := hp.stk.1
  have hsp : 4 ≤ (s.gpr .esp).toNat := by omega
  have s4 := below4_sub h20
  have ki : (below (s.gpr .esp) 4).Disjoint ⟨(arg s 1).setWidth 64, 32⟩ := hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.sub_left s4
  have hspfit := hp.sp_fit
  have hl := combWords_length
  refine WP.seq (WP.mono (symFrame_ok combSym s hsp) fun s₁ P => ?_)
  have e1 : s₁.gpr .esp = s.gpr .esp := P.gpr .esp (by decide)
  have a1 : ∀ j < 3, arg s₁ j = arg s j := fun j hj => P.arg hsp (by omega)
  refine Wp.wp_ldm e1 (by rw [P.rd, P.wr]; exact hp.argIn hp.index) fun s₂ h₂ => ?_
  have e2 : s₂.gpr .edx = arg s 2 := by
    rw [h₂.gpr, ← a1 2 (by decide)]
    simp only [arg, argAddr, e1]
    rfl
  have hw : InRegions s₂.wr (addr (arg s 2) combTbl) 4 := by
    rw [h₂.wr, P.wr]
    exact ⟨_, hp.wr, scR_contains hp.fit (by decide) (by decide)⟩
  refine Wp.wp_stm e2 hw fun s₃ h₃ => WP.block_nil ?_
  have hsub : ∀ r : Reg, r ∈ [Reg.eax, .ecx] → r ∈ [Reg.eax, .ecx, .edx] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  have g3 : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s₃.gpr r = s.gpr r := fun r hr => by
    rw [h₃.gpr, h₂.other r (fun e => hr (by subst e; decide)), P.gpr r (fun e => hr (hsub r e))]
  have e3 : s₃.gpr .esp = s.gpr .esp := g3 .esp (by decide)
  have r3 : s₃.rd = s.rd := by rw [h₃.rd, h₂.rd, P.rd]
  have w3 : s₃.wr = s.wr := by rw [h₃.wr, h₂.wr, P.wr]
  have y3 : s₃.syms = s.syms := by rw [h₃.syms, h₂.syms, P.syms]
  -- The store, to the workspace.
  have G : Frame [scR 8192 (arg s 2)] s₁.mem s₃.mem := by
    rw [h₃.mem, h₂.mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (scR_contains hp.fit (by decide) (by decide))
  -- Everything: the frame below `esp` and the store.
  have F : Frame [below (s.gpr .esp) 4, scR 8192 (arg s 2)] s.mem s₃.mem :=
    (P.frame.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self).trans
      (G.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have a3 : ∀ j < 3, arg s₃ j = arg s j := by
    intro j hj
    rw [← a1 j hj]
    simp only [arg, argAddr, e3, e1]
    refine G.readW (r := ⟨argAddr s 0, 12⟩) ?_ ?_ (by decide)
    · exact hp.arg_contains (i := j) hj
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hp.args_sc
  have T3 : TblWords ((s.syms combSym).setWidth 64) s₃.mem := fun i hi => by
    rw [← held.1 i hi]
    refine F.readW (r := TBL ((s.syms combSym).setWidth 64)) (Offset.contains_base _ (by omega)
      (by omega)) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (held.2.2 _ (by simp)).sub_right s4
    · exact held.2.2 _ (by simp)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun r hr => g3 r ?_, ?_, a3, ?_, y3⟩
  · simpa only [BaseRegions, argAddr, callStk, e3, r3, w3, y3, a3 0 (by decide), a3 1 (by decide),
      a3 2 (by decide)] using hr
  · rw [a3 2 (by decide), y3, h₃.mem, wd_write_self, h₂.other .eax (by decide), P.addr]
  · rw [a3 2 (by decide), y3]
    exact ⟨held.2.1, by rw [r3, hr.1]; simp, T3, held.2.2 _ (by simp)⟩
  · rw [y3, callStk, e3]; exact held.2.2 _ (by simp)
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [← P.ret hsp (by omega)]
    refine G.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr; rw [List.mem_singleton.mp hr]; exact hp.ret_sc
  · unfold Spec.Ed25519.bytesAt
    have hs := hi.sep
    rw [sub, addr_zero] at hs
    refine List.map_congr_left fun k hk =>
      F.bytes (R := ⟨(arg s 1).setWidth 64, 32⟩) ?_ (by change 32 ≤ 2 ^ 64; decide)
        (List.mem_range.mp hk)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ki.symm
    · exact hs

/-- The regions and arguments survive the static's address's frame. -/
theorem BaseRegions.symAddr {name : String} {s t : State} (h : BaseRegions s)
    (P : SymAddrPost name s t) (hsp : 4 ≤ (s.gpr .esp).toNat) : BaseRegions t := by
  have hf : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 := h.2.2.2.2.2.2.2.2.2.2.2.1
  have e : t.gpr .esp = s.gpr .esp := P.gpr .esp (by decide)
  have a : ∀ j < 3, arg t j = arg s j := fun j hj => P.arg hsp (by omega)
  simpa only [BaseRegions, argAddr, callStk, e, P.rd, P.wr, P.syms, a 0 (by decide), a 1 (by decide),
    a 2 (by decide)] using h

/-- The public part of the states after the prologue. -/
theorem Prologue.pub {s t u v : State} (Pu : Prologue s u) (Pv : Prologue t v)
    (h : scalarBaseLocal.pub s t) : scalarBaseLocal.pub u v := by
  obtain ⟨sp, a0, a1, a2, sy⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Pu.gpr .esp (by decide), Pv.gpr .esp (by decide), sp]
  · rw [Pu.args 0 (by decide), Pv.args 0 (by decide), a0]
  · rw [Pu.args 1 (by decide), Pv.args 1 (by decide), a1]
  · rw [Pu.args 2 (by decide), Pv.args 2 (by decide), a2]
  · rw [Pu.syms, Pv.syms, sy]

/-- The function preserves of its entry what its body preserves of its start. -/
theorem Prologue.abi {s s' t : State} (h : Prologue s s') (ha : abiPreserved s' t) :
    abiPreserved s t := by
  refine ⟨fun r hr => (ha.1 r hr).trans (h.gpr r hr), ?_⟩
  have he := h.gpr .esp (by decide)
  have := ha.2
  rw [he] at this
  exact this.trans h.ret

end VG.Proof.Ed25519.X86
