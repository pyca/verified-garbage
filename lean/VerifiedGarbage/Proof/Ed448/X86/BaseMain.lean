import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
import VerifiedGarbage.Proof.Ed448.X86.BaseSetup
import VerifiedGarbage.Proof.Ed448.X86.BaseStep
import VerifiedGarbage.Proof.Ed448.X86.BaseEncode
import VerifiedGarbage.Proof.Ed448.X86.ScalarMain

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

theorem BasePre.of {s : State} (h : scalarBaseLocal.pre s) : BasePre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

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

theorem scalarBase_ladder {s₀ : State} (h : BasePre s₀) :
    WP isa scalarBase s₀ fun t => abiPreserved s₀ t ∧
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 =
        Spec.Ed448.encodePoint (ladder (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57)) 456) := by
  have hA := h.args
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 2).setWidth 64 = b := ⟨_, rfl⟩
  have hin : Input s₀ base (arg s₀ 1) 57 :=
    Input.of_region h.scalar_fit (by rw [h.rd]; simp) (hbase ▸ h.scalar_sc)
  unfold scalarBase
  -- The entry: the registers saved, the slots, the scalar's bits.
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_)))
  rw [hbase] at hs₁ sv₁ o₁
  refine WP.mono (initSlots_ok hs₁) fun s₂ ⟨l₂, o₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have k02 : Keeps [.eax, .ebx, .ebp, .edi] s₀ s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have o02 : Outside base 0 8192 s₀.mem s₂.mem :=
    (o₁.mono (by omega) (by omega)).trans (o₂.mono (by omega) (by omega))
  rw [baseBits]
  refine hA.load (i := 1) (k02.1 _ (by decide)) k02.2.1 k02.2.2 (hbase ▸ o02) (by decide)
    fun s₃ u₃ => ?_
  have hs₃ := hs₂.of_upd u₃ (by decide)
  refine WP.mono (baseBytes_ok (k := (arg s₀ 1).setWidth 64) hs₃ (by rw [u₃.gpr]) (by rw [u₃.gpr]; exact hin.fit)
    (by rw [u₃.rd, u₃.wr, k02.2.1, k02.2.2]; exact hin.read) hin.far) fun s₄ ⟨k₄, o₄, bits₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have mem34 : bytesAt s₃.mem ((arg s₀ 1).setWidth 64) 57 = bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57 := by
    rw [u₃.mem]; exact hin.bytes o02
  rw [mem34] at bits₄
  have e₄ : ∀ i : Index, E s₄.mem base i = Proof.X448.toFe (initVal i.val) := by
    intro i
    rw [← initSlots_E l₂ i]
    simp only [E, F]
    rw [o₄.fe (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega), u₃.mem]
  have b₄ : BoundedEnv s₄.mem base := by
    intro i j hj
    rw [o₄.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj, u₃.mem]
    exact initSlots_bounded l₂ i j hj
  obtain ⟨er, eq, ed⟩ := initE _ e₄
  -- The loop.
  refine WP.seq (WP.mono (baseLoop_ok (s₀ := s₄) (s := s₄) bits₄ (fun s' h1 h2 h3 h4 h5 => ?_))
    fun y hy => ?_)
  · have k' : Keeps (.esi :: workRegs) s₄ s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    exact ⟨hs₄.of_keeps k' (by decide), h3 ▸ b₄, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _,
      by rw [h3, er]; rfl, by rw [h3]; exact eq, by rw [h3]; exact ed⟩
  -- The encoding.
  have k0y : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ y :=
    (k02.mono (by decide)).trans ((u₃.rest (by decide)).trans ((k₄.mono (by decide)).trans
      (hy.regs.mono (by decide))))
  have o4w : Outside base 0 8192 s₃.mem s₄.mem := o₄.mono (by omega) (by simp only [BITS]; omega)
  rw [u₃.mem] at o4w
  have m0y : Outside base 0 8192 s₀.mem y.mem :=
    (o02.trans o4w).trans (hy.mem.whole (by decide) (by decide))
  have svy : Saved base s₀.gpr y.mem :=
    ((sv₁.outside o₂ (by decide)).outside (u₃.mem ▸ o₄) (by decide)).outside2 hy.mem (by decide)
      (by decide)
  refine WP.mono (baseEncode_ok hA (by decide) (k0y.1 _ (by decide)) k0y.2.1 k0y.2.2 hbase m0y hy.scr
    hy.bounded (by rw [h.wr]; simp) h.out_fit (hbase ▸ h.out_sc) svy) fun t ⟨bt, rt, kt, ft⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rt (.ebx, 0) (by decide)
    · exact rt (.esi, 4) (by decide)
    · exact rt (.edi, 8) (by decide)
    · exact rt (.ebp, 12) (by decide)
    · rw [kt.1 _ (by decide), k0y.1 _ (by decide)]
  · have frame : Frame [⟨base, 8192⟩, ⟨(arg s₀ 0).setWidth 64, 57⟩] s₀.mem t.mem :=
      ((Outside.frame m0y).mono (by simp)).trans ft
    have ret : (retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    exact frame.readW ret
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hbase ▸ h.ret_sc
          · exact h.ret_out) (by decide)
  · rw [bt]
    exact congrArg Spec.Ed448.encodePoint hy.r

end VG.Proof.Ed448.X86
