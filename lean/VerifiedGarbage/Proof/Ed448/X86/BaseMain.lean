import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
import VerifiedGarbage.Proof.Ed448.X86.BaseSetup
import VerifiedGarbage.Proof.Ed448.X86.BaseStep
import VerifiedGarbage.Proof.Ed448.X86.BaseEncode
import VerifiedGarbage.Proof.Ed448.X86.ScalarMain
import VerifiedGarbage.Proof.X448.X86.Runs

/-!
# Ed448 base-point multiplication on x86 (32-bit): the whole function

`vg_ed448_scalar_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`
against a local contract (`scalarBaseLocal`, `BaseLocal.lean`: the arguments
only read): it
computes the encoding of the ladder over the scalar's bits
(`scalarBase_ladder`): the entry, the scalar's bits, the loop (`R` ends as
`ladder k 456`), the inversion of `Z` and the encoding. Every write is in the
working space but the result's, so the arguments and the scalar are read
unchanged; the callee-saved registers are restored from the working space,
and the return address is kept.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (ladder pt)
open VG.Impl.Ed448.X86 (scalarBase initSlots baseBits initVal)
open VG.Impl.X448.X86 (slot BITS ACC at_)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The precondition, by name. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 1).setWidth 64, 57⟩, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s 2)]
  out_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  scalar_sc : (⟨(arg s 1).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  args_out : (⟨argAddr s 0, 12⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  args_sc : (⟨argAddr s 0, 12⟩ : Region).Disjoint (scR (arg s 2))
  ret_out : (retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  ret_sc : (retR s).Disjoint (scR (arg s 2))
  out_fit : (arg s 0).toNat + 57 ≤ 2 ^ 32
  scalar_fit : (arg s 1).toNat + 57 ≤ 2 ^ 32
  sc_fit : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  sp_room : 20 ≤ (s.gpr .esp).toNat
  stk_out : (stkR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  stk_sc : (stkR s).Disjoint (scR (arg s 2))

theorem BasePre.of {s : State} (h : scalarBaseLocal.pre s) : BasePre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- The stack the calls use, as `below`. -/
theorem stkR_below {s : State} (h : 20 ≤ (s.gpr .esp).toNat) : stkR s = below (s.gpr .esp) 20 := by
  simp only [below]; rw [VG.X86.Taint.sub_setWidth h]

theorem BasePre.stk_args {s : State} (h : BasePre s) : (stkR s).Disjoint ⟨argAddr s 0, 12⟩ := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> simp only [argAddr] <;> bv_omega

theorem BasePre.stk_ret {s : State} (h : BasePre s) : (stkR s).Disjoint (retR s) := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> bv_omega

theorem BasePre.args {s : State} (h : BasePre s) : Args s 3 2 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega, by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

theorem initE (e : Env) (he : ∀ i : Index, e i = Proof.X448.toFe (initVal i.val)) :
    pt e 0 1 2 = Spec.Ed448.identity ∧ pt e 8 9 10 = Spec.Ed448.basePoint ∧ e 11 = Spec.Ed448.d := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [pt, he]
    rw [show ((0 : Index) : Nat) = 0 from rfl, show ((1 : Index) : Nat) = 1 from rfl,
      show ((2 : Index) : Nat) = 2 from rfl, show initVal 0 = Spec.Ed448.identity.X.val from rfl,
      show initVal 1 = Spec.Ed448.identity.Y.val from rfl,
      show initVal 2 = Spec.Ed448.identity.Z.val from rfl, Proof.X448.toFe_self,
      Proof.X448.toFe_self, Proof.X448.toFe_self]
  · simp only [pt, he]
    rw [show ((8 : Index) : Nat) = 8 from rfl, show ((9 : Index) : Nat) = 9 from rfl,
      show ((10 : Index) : Nat) = 10 from rfl, show initVal 8 = Spec.Ed448.basePoint.X.val from rfl,
      show initVal 9 = Spec.Ed448.basePoint.Y.val from rfl,
      show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self,
      Proof.X448.toFe_self, Proof.X448.toFe_self]
  · rw [he]; exact Proof.X448.toFe_self _

section
variable (σ : State)
/-- The working space and the scalar, from the entry state `σ`. -/
abbrev bsB : Addr := (arg σ 2).setWidth 64
abbrev kB : Nat := decodeLE (bytesAt σ.mem ((arg σ 1).setWidth 64) 57)
end

/-- After the entry block, from the entry state `σ`. -/
structure BMid (σ s : State) : Prop where
  pre : BasePre σ
  fe : FE bsB σ s
  rd : s.rd = σ.rd
  saved : Saved (bsB σ) σ.gpr s.mem
  bits : ∀ t < 456, s.mem (off (bsB σ) (BITS + t)) = BitVec.ofNat 8 ((kB σ >>> t) &&& 1)
  start : ∀ s', s'.gpr .esi = BitVec.ofNat 32 456 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
    s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → BaseInv (bsB σ) (kB σ) s s' 456

theorem entry_stage {s₀ : State} (h : BasePre s₀) :
    WP isa (.block (Impl.Ed448.X86.save 12 ++ initSlots ++ baseBits)) s₀ (BMid s₀) := by
  have hA := h.args
  have hin : Input s₀ (bsB s₀) (arg s₀ 1) 57 :=
    Input.of_region h.scalar_fit (by rw [h.rd]; simp) h.scalar_sc
  refine WP.block_append (WP.block_append (WP.mono (save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_))
  refine WP.mono (initSlots_ok hs₁) fun s₂ ⟨l₂, o₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have k02 : Keeps [.eax, .ebx, .ebp, .edi] s₀ s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have o02 : Outside (bsB s₀) 0 8192 s₀.mem s₂.mem :=
    (o₁.mono (by omega) (by omega)).trans (o₂.mono (by omega) (by omega))
  rw [baseBits]
  refine hA.load (i := 1) (k02.1 _ (by decide)) k02.2.1 k02.2.2 o02 (by decide) fun s₃ u₃ => ?_
  have hs₃ := hs₂.of_upd u₃ (by decide)
  refine WP.mono (baseBytes_ok (k := (arg s₀ 1).setWidth 64) hs₃ (by rw [u₃.gpr]) (by rw [u₃.gpr]; exact hin.fit)
    (by rw [u₃.rd, u₃.wr, k02.2.1, k02.2.2]; exact hin.read) hin.far) fun s₄ ⟨k₄, o₄, bits₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have mem34 : bytesAt s₃.mem ((arg s₀ 1).setWidth 64) 57 = bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57 := by
    rw [u₃.mem]; exact hin.bytes o02
  rw [mem34] at bits₄
  have e₄ : ∀ i : Index, E s₄.mem (bsB s₀) i = Proof.X448.toFe (initVal i.val) := by
    intro i
    rw [← initSlots_E l₂ i]
    simp only [E, F]
    rw [o₄.fe (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega), u₃.mem]
  have b₄ : BoundedEnv s₄.mem (bsB s₀) := by
    intro i j hj
    rw [o₄.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj, u₃.mem]
    exact initSlots_bounded l₂ i j hj
  obtain ⟨er, eq, ed⟩ := initE _ e₄
  have k04 : Keeps [.eax, .ebx, .ebp, .edi, .esi, .edx] s₀ s₄ :=
    (k02.mono (by decide)).trans ((u₃.rest (by decide)).trans (k₄.mono (by decide)))
  have sp₄ : s₄.gpr .esp = s₀.gpr .esp := k04.1 _ (by decide)
  have hc₄ : CallCtx s₄ (bsB s₀) := ⟨by rw [sp₄]; exact h.sp_room, by
    simp only [callStk, sp₄]; rw [← stkR_below h.sp_room]; exact h.stk_sc.symm⟩
  have o4w : Outside (bsB s₀) 0 8192 s₃.mem s₄.mem := o₄.mono (by omega) (by simp only [BITS]; omega)
  rw [u₃.mem] at o4w
  have ws : (⟨bsB s₀, 8192⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) 20] := by
    rw [h.wr]; simp
  refine ⟨h, ⟨⟨hs₄, hc₄, b₄⟩, sp₄, k04.2.2, (Outside.frame (o02.trans o4w)).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ws⟩, k04.2.1,
    (sv₁.outside o₂ (by decide)).outside (u₃.mem ▸ o₄) (by decide), bits₄, fun s' h1 h2 h3 h4 h5 => ?_⟩
  have k' : Keeps (.esi :: workRegs) s₄ s' :=
    ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
  exact ⟨hs₄.of_keeps k' (by decide), hc₄.keep (h2 _ (by decide)), h3 ▸ b₄, k', h1,
    h3 ▸ WsOut2.refl _ _ _ _ _ _, by rw [h3, er]; rfl, by rw [h3]; exact eq, by rw [h3]; exact ed⟩

/-- In the loop, `n` iterations from its end, which started in `s₄`. -/
def BL (σ s₄ s : State) (n : Nat) : Prop :=
  BMid σ s₄ ∧ BaseInv (bsB σ) (kB σ) s₄ s n ∧ FE bsB σ s

/-- `FE` from the loop's invariant, for code keeping it. -/
theorem BL.fin {σ s₄ s t : State} {n m : Nat} (h : BL σ s₄ s n) (ht : BaseInv (bsB σ) (kB σ) s₄ t m) :
    FInv (bsB σ) t ∧ t.gpr .esp = s.gpr .esp ∧ t.wr = s.wr :=
  ⟨⟨ht.scr, ht.ctx, ht.bounded⟩, (ht.regs.1 _ (by decide)).trans (h.2.1.regs.1 _ (by decide)).symm,
    ht.regs.2.2.trans h.2.1.regs.2.2.symm⟩

theorem loop_stage {σ s : State} (h : BMid σ s) :
    WP isa Impl.Ed448.X86.baseLoop s fun t => BL σ s t 0 :=
  WP.mono (h.fe.wp (NoSp.of_all (by decide +kernel)) (by decide +kernel)
    (Q := fun t => BaseInv (bsB σ) (kB σ) s t 0) (WP.mono (baseLoop_ok h.bits h.start) fun t ht =>
      ⟨⟨ht.scr, ht.ctx, ht.bounded⟩, ht.regs.1 _ (by decide), ht.regs.2.2, ht⟩))
    fun t ⟨fe, ht⟩ => ⟨h, ht, fe⟩

theorem step_stage {σ s₄ s : State} {n : Nat} (hn : n < 456) (h : BL σ s₄ s (n + 1)) :
    WP isa Impl.Ed448.X86.baseStep s fun t => BL σ s₄ t n ∧ t.zf = some (decide (n = 0)) :=
  WP.mono (h.2.2.wp (NoSp.of_all (by decide +kernel)) (by decide +kernel)
    (Q := fun t => BaseInv (bsB σ) (kB σ) s₄ t n ∧ t.zf = some (decide (n = 0)))
    (WP.mono (baseStep_ok hn h.1.bits h.2.1) fun t ⟨ht, z⟩ => ⟨(BL.fin h ht).1, (BL.fin h ht).2.1, (BL.fin h ht).2.2, ht, z⟩))
    fun t ⟨fe, ht, z⟩ => ⟨⟨h.1, ht, fe⟩, z⟩

theorem encode_stage {σ s₄ s : State} (h : BL σ s₄ s 0) :
    WP isa Impl.Ed448.X86.baseEncode s fun t => abiPreserved σ t ∧
      bytesAt t.mem ((arg σ 0).setWidth 64) 57 = Spec.Ed448.encodePoint (ladder (kB σ) 456) := by
  obtain ⟨m, hy, fe⟩ := h
  have hp := m.pre
  have hawr : ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20], (⟨argAddr σ 0, 4 * 3⟩ : Region).Disjoint r := by
    rw [hp.wr, ← stkR_below hp.sp_room]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.args_out
    · exact hp.args_sc
    · exact hp.stk_args.symm
  refine WP.mono (baseEncode_ok hp.args (by decide) fe.sp (hy.regs.2.1.trans m.rd) fe.wr fe.frame hawr
    fe.fin.scr fe.fin.ctx fe.fin.bounded (by rw [hp.wr]; simp) hp.out_fit hp.out_sc
    (m.saved.wsout2 hy.mem (by decide) (by decide))) fun t ⟨bt, rt, kt, ft⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rt (.ebx, 0) (by decide)
    · exact rt (.esi, 4) (by decide)
    · exact rt (.edi, 8) (by decide)
    · exact rt (.ebp, 12) (by decide)
    · rw [kt.1 _ (by decide), fe.sp]
  · have ret : (retR σ).Contains ((σ.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((σ.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    refine (fe.frame.trans ft).readW ret ?_ (by decide)
    rw [hp.wr, ← stkR_below hp.sp_room]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.ret_out
    · exact hp.ret_sc
    · exact hp.stk_ret.symm
  · rw [bt]
    exact congrArg Spec.Ed448.encodePoint hy.r

theorem scalarBase_ladder {s₀ : State} (h : BasePre s₀) :
    WP isa scalarBase s₀ fun t => abiPreserved s₀ t ∧
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 =
        Spec.Ed448.encodePoint (ladder (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57)) 456) := by
  unfold scalarBase
  exact WP.seq (WP.mono (entry_stage h) fun _ m => WP.seq (WP.mono (loop_stage m) fun _ l => encode_stage l))

end VG.Proof.Ed448.X86
