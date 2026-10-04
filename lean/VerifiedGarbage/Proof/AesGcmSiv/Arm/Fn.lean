import VerifiedGarbage.Proof.AesGcmSiv.Arm.Cmp
import VerifiedGarbage.Proof.AesGcm.Arm.Args

/-!
# AES-GCM-SIV on ARMv7: the arguments and the entry

Untrusted: everything here is checked by Lean. The precondition `onePre`
gives the public arguments (`prmOf`), how they lie (`lay_of`), what the
state may access (`perm_of`) and the stack arguments (`args_of`). `entry`
loads `W` from the stack, saves our caller's registers at `W + 128`, as
AES-GCM does, and keeps the arguments in `r7`–`r11` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (arg args bel covers_of_mem covers_left covers_prefix SavedAt savedR argAddr_zero stackArg_eq)

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := s.gpr .r0
  W := arg s 3
  N := s.gpr .r2
  A := s.gpr .r3
  D := arg s 1
  SP := s.sp
  R := (s.gpr .r1).toNat
  al := (arg s 0).toNat
  n := (arg s 2).toNat

theorem args_eq (s : State) : args s 4 = argR s.sp := by
  simp only [args, argAddr_zero]

theorem lay_of {s : State} (h : onePre s) : Lay (prmOf s) := by
  obtain ⟨_, _, sd, sw, nd, nw, ad, aw, dw, da, wa, bs, bn, ba, bd, bw, fK, fN, fA, fD, fW, sp8, spf, hR⟩ := h
  rw [args_eq] at da wa
  exact ⟨fK, fW, fN, fA, fD, BitVec.isLt _, BitVec.isLt _, sp8, spf, sw, sd, nw, nd, aw, ad, dw, da, wa, bs, bn, ba,
    bd, bw, hR⟩

theorem perm_of {s : State} (h : onePre s) : Perm (prmOf s) s := by
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, da, wa, -⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), 12⟩,
      ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩, args s 4], Covers [r] (s.rd ++ s.wr) :=
    fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region), ⟨State.addr (arg s 3), 4096⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  refine ⟨mrd _ List.mem_cons_self, mrd _ (List.mem_cons_of_mem _ List.mem_cons_self),
    mrd _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), mwr _ List.mem_cons_self,
    mwr _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_, fun r hr => ?_⟩
  · have := mrd (args s 4) (by simp)
    rwa [args_eq] at this
  · rw [args_eq] at da wa
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact da.symm
    · exact wa.symm

theorem args_of (s : State) : Args (prmOf s) s.mem :=
  ⟨by simp [prmOf, arg, stackArg_eq], by simp [prmOf, arg, stackArg_eq], by simp [prmOf, arg, stackArg_eq]⟩

/-- What the entry leaves. -/
structure Entered (s s₁ : State) : Prop where
  env : Env (prmOf s) s₁
  saved : SavedAt s₁.mem (prmOf s).W s
  frame : Frame [savedR (prmOf s).W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- `entry`. -/
theorem entry_ok {s : State} (h : onePre s) : WP isa (.block entry) s (Entered s) := by
  have P := perm_of h
  have L := lay_of h
  have hw := L.ww
  have ha : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 12)) 4 := P.argR' L (k := 12) (by decide)
  have e12 : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 12)) 32 = (prmOf s).W := by simp [prmOf, arg, stackArg_eq]
  refine Proof.AesGcm.Arm.entry_ok (off := 12) (by decide) ha (by rw [e12]; omega)
    (by rw [e12]; exact P.w2560) fun s₁ g12 g rd wr sp sv fr => ?_
  rw [e12] at g12 sv fr
  refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun s₂ hs₂ => ?_
  subst hs₂
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by simp only [sp_setReg]; rw [sp]; rfl,
    P.of_eq (by simp only [rd_setReg]; exact rd) (by simp only [wr_setReg]; exact wr)⟩, by simpa [mem_setReg] using sv,
    by simpa [mem_setReg] using fr, by simp only [rd_setReg]; exact rd, by simp only [wr_setReg]; exact wr⟩
  all_goals simp [gpr_setReg, g, g12, prmOf]

/-! ## Regions -/

/-- Proves that a region is disjoint from each of a list of regions: parts
of `W`, the data, the stack below `SP`, or the key schedule. -/
macro "disj_tac" L:term : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true]
  repeat' apply And.intro
  all_goals first
    | (with_reducible refine Lay.w_w $L (.inl ?_) ?_ ?_) <;> decide
    | (with_reducible refine Lay.w_w $L (.inr ?_) ?_ ?_) <;> decide
    | (with_reducible refine Lay.d_w' $L ?_) <;> decide
    | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide
    | (with_reducible refine Lay.k_w' $L ?_) <;> decide
    | (with_reducible refine Lay.n_w' $L ?_) <;> decide
    | (with_reducible refine Lay.a_w' $L ?_) <;> decide
    | (with_reducible refine (Lay.bw' $L ?_).symm) <;> decide
    | (with_reducible refine Lay.args_w' $L ?_) <;> decide
    | with_reducible exact Lay.k_d $L
    | with_reducible exact Lay.n_d $L
    | with_reducible exact Lay.a_d $L
    | with_reducible exact (Lay.d_w $L).symm
    | with_reducible exact (Lay.bk $L).symm
    | with_reducible exact (Lay.bn $L).symm
    | with_reducible exact (Lay.ba $L).symm
    | with_reducible exact (Lay.bd $L).symm
    | with_reducible exact Lay.args_below $L
    | with_reducible exact (Lay.d_args $L).symm))

end VG.Proof.AesGcmSiv.Arm
