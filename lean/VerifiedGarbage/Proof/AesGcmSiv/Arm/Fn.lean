import VerifiedGarbage.Proof.AesGcmSiv.Arm.Cmp
import VerifiedGarbage.Proof.AesGcm.Arm.Args

/-!
# AES-GCM-SIV on ARMv7: the arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the public arguments (`prmOf`), how they lie (`lay_of`),
what the state may access (`args_of_seal`, `args_of_open`) and the stack
arguments (`args_of`). `recv` and `tagOut` copy the tag, whose address they
read from the stack (`recv_ok`, `tagOut_ok`). `entry`
loads `W` from the stack, saves our caller's registers at `W + 128`, as
AES-GCM does, and keeps the arguments in `r7`–`r11` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (arg args bel covers_of_mem covers_left covers_prefix SavedAt savedR argAddr_zero stackArg_eq
  in_off add_ofNat_zero mem_store)

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := s.gpr .r0
  W := arg s 4
  N := s.gpr .r2
  A := s.gpr .r3
  D := arg s 1
  T := arg s 3
  SP := s.sp
  R := (s.gpr .r1).toNat
  al := (arg s 0).toNat
  n := (arg s 2).toNat

theorem args_eq (s : State) : args s 5 = argR s.sp := by
  simp only [args, argAddr_zero]

theorem lay_of {s : State} (h : oneLay s) : Lay (prmOf s) := by
  obtain ⟨sd, sw, nd, nw, ad, aw, td, tw, dw, da, wa, bs, bn, ba, bd, bt, bw, fK, fN, fA, fD, fT, fW, sp8, spf,
    hR⟩ := h
  rw [args_eq] at da wa
  exact ⟨fK, fW, fN, fA, fD, BitVec.isLt _, BitVec.isLt _, sp8, spf, fT, sw, sd, nw, nd, aw, ad, dw, tw, td, da, wa,
    bs, bn, ba, bd, bw, hR⟩

/-- The permissions, from the buffers' coverage. -/
theorem perm_of_cov {s : State} (hk : Covers [⟨State.addr (s.gpr .r0), 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨State.addr (s.gpr .r2), 12⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨State.addr (arg s 1), (arg s 2).toNat⟩] s.wr) (hW : Covers [⟨State.addr (arg s 4), 3760⟩] s.wr)
    (ha : Covers [args s 5] (s.rd ++ s.wr)) (hT : Covers [⟨State.addr (arg s 3), 16⟩] (s.rd ++ s.wr))
    (hw : ∀ r ∈ s.wr, (args s 5).Disjoint r) : Perm (prmOf s) s := by
  rw [args_eq] at ha hw
  exact ⟨hk, hN, hA, hD, hW, ha, hw, hT⟩

/-- `seal`'s layout and permissions, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    Lay (prmOf s) ∧ Perm (prmOf s) s ∧ Covers [⟨State.addr (arg s 3), 16⟩] s.wr := by
  obtain ⟨hrd, hwr, ta, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), 12⟩,
      ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩, args s 5], Covers [r] (s.rd ++ s.wr) :=
    fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region), ⟨State.addr (arg s 3), 16⟩,
      ⟨State.addr (arg s 4), 3760⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  obtain ⟨-, -, -, -, -, -, -, -, -, da, wa, -⟩ := id hl
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)) (covers_left (mwr _ (by simp))) (fun r hr => by
      rw [hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact da.symm
      · exact ta.symm
      · exact wa.symm), mwr _ (by simp)⟩

/-- `open`'s layout and permissions, with its received tag, to read. -/
theorem args_of_open {s : State} (h : openPre s) : Lay (prmOf s) ∧ Perm (prmOf s) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), 12⟩,
      ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩, ⟨State.addr (arg s 3), 16⟩, args s 5], Covers [r] (s.rd ++ s.wr) :=
    fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region), ⟨State.addr (arg s 4), 3760⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  obtain ⟨-, -, -, -, -, -, -, -, -, da, wa, -⟩ := id hl
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (fun r hr => by
      rw [hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact da.symm
      · exact wa.symm)⟩

theorem args_of (s : State) : Args (prmOf s) s.mem :=
  ⟨by simp [prmOf, arg, stackArg_eq], by simp [prmOf, arg, stackArg_eq], by simp [prmOf, arg, stackArg_eq],
    by simp [prmOf, arg, stackArg_eq]⟩

/-- What the entry leaves. -/
structure Entered (s s₁ : State) : Prop where
  env : Env (prmOf s) s₁
  saved : SavedAt s₁.mem (prmOf s).W s
  frame : Frame [savedR (prmOf s).W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- `entry`. -/
theorem entry_ok {s : State} (L : Lay (prmOf s)) (P : Perm (prmOf s) s) : WP isa (.block entry) s (Entered s) := by
  have hw := L.ww
  have ha : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4 := P.argR' L (k := 16) (by decide)
  have e16 : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = (prmOf s).W := by simp [prmOf, arg, stackArg_eq]
  refine Proof.AesGcm.Arm.entry_ok (off := 16) (by decide) ha (by rw [e16]; omega)
    (by rw [e16]; exact P.w2560) fun s₁ g16 g rd wr sp sv fr => ?_
  rw [e16] at g16 sv fr
  refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun s₂ hs₂ => ?_
  subst hs₂
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by simp only [sp_setReg]; rw [sp]; rfl,
    P.of_eq (by simp only [rd_setReg]; exact rd) (by simp only [wr_setReg]; exact wr)⟩, by simpa [mem_setReg] using sv,
    by simpa [mem_setReg] using fr, by simp only [rd_setReg]; exact rd, by simp only [wr_setReg]; exact wr⟩
  all_goals simp [gpr_setReg, g, g16, prmOf]

/-! ## The tag's copies -/

/-- `tag`'s address, read from the stack. -/
theorem tagArg {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) :
    s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 12)) 32 = p.T ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 12)) 4 := by
  rw [E.sp]; exact ⟨A.a12, E.perm.argR' L (k := 12) (by decide)⟩

/-- A 16-byte block copied by words, all loaded first. -/
theorem bytesAt_copy4 (m : Mem) (S T : Addr) :
    bytesAt (Proof.Cmac.store4 m T (m.readW S 32) (m.readW (S + BitVec.ofNat 64 4) 32)
      (m.readW (S + BitVec.ofNat 64 8) 32) (m.readW (S + BitVec.ofNat 64 12) 32)) T 16 = bytesAt m S 16 := by
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4]

/-- `recv`: the received tag, at `T`, copied to `W`. -/
theorem recv_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨State.addr p.W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr p.W) 16 = bytesAt s.mem (State.addr p.T) 16 ∧
      Others [.r0, .r1, .r2, .r3, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hT, hTa⟩ := tagArg L E A
  have tw := L.tw
  have eT : ∀ k, k < 16 → State.addr (p.T + BitVec.ofNat 32 k) = State.addr p.T + BitVec.ofNat 64 k :=
    fun k hk => addr_add (by omega)
  have t₀ : InRegions (s.rd ++ s.wr) (State.addr p.T) 4 := by
    simpa using in_off (d := 0) (n := 4) E.perm.t (by decide) (by decide)
  have t₁ := in_off (d := 4) (n := 4) E.perm.t (by decide) (by decide)
  have t₂ := in_off (d := 8) (n := 4) E.perm.t (by decide) (by decide)
  have t₃ := in_off (d := 12) (n := 4) E.perm.t (by decide) (by decide)
  have w₀ : InRegions s.wr (State.addr p.W) 4 := by simpa using E.perm.wW (show 0 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 4 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 8 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 12 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [recv]; srun [E.r11, add_ofNat_zero, L.wA, hT, hTa, eT, t₀, t₁, t₂, t₃, w₀, w₁, w₂, w₃],
    ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store]
    exact Proof.Cmac.frame_store4 _ _ _ _ _
  · simp only [mem_setReg, mem_store]
    exact bytesAt_copy4 _ _ _

/-- `tagOut`: the tag at `W` copied to `T`, which the state may write. -/
theorem tagOut_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem)
    (hTw : Covers [⟨State.addr p.T, 16⟩] s.wr) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨State.addr p.T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr p.T) 16 = bytesAt s.mem (State.addr p.W) 16 ∧
      Others [.r0, .r1, .r2, .r3, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hT, hTa⟩ := tagArg L E A
  have tw := L.tw
  have eT : ∀ k, k < 16 → State.addr (p.T + BitVec.ofNat 32 k) = State.addr p.T + BitVec.ofNat 64 k :=
    fun k hk => addr_add (by omega)
  have t₀ : InRegions s.wr (State.addr p.T) 4 := by simpa using in_off (d := 0) (n := 4) hTw (by decide) (by decide)
  have t₁ := in_off (d := 4) (n := 4) hTw (by decide) (by decide)
  have t₂ := in_off (d := 8) (n := 4) hTw (by decide) (by decide)
  have t₃ := in_off (d := 12) (n := 4) hTw (by decide) (by decide)
  have w₀ : InRegions (s.rd ++ s.wr) (State.addr p.W) 4 := by simpa using E.perm.wR (show 0 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wR (show 4 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wR (show 8 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wR (show 12 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [tagOut]; srun [E.r11, add_ofNat_zero, L.wA, hT, hTa, eT, t₀, t₁, t₂, t₃, w₀, w₁, w₂, w₃],
    ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store]
    exact Proof.Cmac.frame_store4 _ _ _ _ _
  · simp only [mem_setReg, mem_store]
    exact bytesAt_copy4 _ _ _

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
    | (with_reducible refine Lay.t_w' $L ?_) <;> decide
    | with_reducible exact Lay.t_d $L
    | with_reducible exact (Lay.t_d $L).symm
    | with_reducible exact (Lay.d_w $L).symm
    | with_reducible exact (Lay.bk $L).symm
    | with_reducible exact (Lay.bn $L).symm
    | with_reducible exact (Lay.ba $L).symm
    | with_reducible exact (Lay.bd $L).symm
    | with_reducible exact Lay.args_below $L
    | with_reducible exact (Lay.d_args $L).symm))

end VG.Proof.AesGcmSiv.Arm
