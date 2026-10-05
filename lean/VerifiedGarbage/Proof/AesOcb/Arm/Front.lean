import VerifiedGarbage.Proof.AesOcb.Arm.Body
import VerifiedGarbage.Proof.AesOcb.Arm.Nonce
import VerifiedGarbage.Proof.AesGcm.Arm.Entry

/-!
# AES-OCB on ARMv7: before the data

Untrusted: everything here is checked by Lean. What the contracts'
preconditions give about the arguments (`prmOf`, `lay_of`, `perm_of`,
`args_of`); the entry, which saves our caller's registers in `W`, keeps `W`,
the key context and the rounds in registers, and computes `L_$` and `L_0`
(`entry_wp`); and the entry, `Offset_0` (`nonce`) and `HASH` (`hash`)
together (`pre_wp`), as on AArch64 (`Proof.AesOcb.AArch64.pre_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (blockAtMem_frame)
open VG.Proof.AesGcm.Arm (below SavedAt savedR entry_ok covers_of_mem covers_left)

/-! ## The arguments -/

/-- The public arguments of a call. -/
def prmOf (s : State) : Prm where
  K := s.gpr .r0
  W := arg s 6
  N := s.gpr .r2
  A := arg s 0
  D := arg s 2
  T := arg s 4
  SP := s.sp
  R := (s.gpr .r1).toNat
  nl := (s.gpr .r3).toNat
  al := (arg s 1).toNat
  n := (arg s 3).toNat
  tl := (arg s 5).toNat

theorem ofNat_toNat32' (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem argR_eq (s : State) : args s 7 = argR s.sp := by
  simp only [args, argR, stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem lay_of {s : State} (h : oneLay s) : Lay (prmOf s) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5, f1, f2, f3, f4, f5, sp8, spf, hR,
    hv, t1, t2, t3, t4⟩ := h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  rw [argR_eq] at d8 d9
  exact ⟨f1, f5, f2, f3, f4, t4, BitVec.isLt _, BitVec.isLt _, sp8, spf, d2, d1, d4, d3, d6, d5, t2, t1, d7, d8, d9,
    b1, b2, b3, b4, t3, b5, hR, hn1, hn15, ht1, ht16⟩

/-- The permissions, from the regions each function may read and write. -/
theorem perm_of {s : State} (_h : oneLay s)
    (mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 256⟩ : Region), ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩,
      ⟨State.addr (arg s 0), (arg s 1).toNat⟩, ⟨State.addr (arg s 4), (arg s 5).toNat⟩, args s 7],
      Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [(⟨State.addr (arg s 2), (arg s 3).toNat⟩ : Region), ⟨State.addr (arg s 6), 2560⟩], Covers [r] s.wr)
    (hwr : ∀ r ∈ s.wr, (args s 7).Disjoint r) : Perm (prmOf s) s := by
  rw [argR_eq] at mrd hwr
  exact ⟨mrd _ (by simp [prmOf]), mrd _ (by simp [prmOf]), mrd _ (by simp [prmOf]), mrd _ (by simp [prmOf]),
    mwr _ (by simp [prmOf]), mwr _ (by simp [prmOf]), mrd _ (by simp [prmOf]), hwr⟩

theorem args_of (s : State) : Args (prmOf s) s.mem :=
  ⟨rfl, by rw [prmOf, ofNat_toNat32']; rfl, rfl, by rw [prmOf, ofNat_toNat32']; rfl, rfl,
    by rw [prmOf, ofNat_toNat32']; rfl⟩

theorem sealPerm {s : State} (h : sealPre s) : Perm (prmOf s) s := by
  obtain ⟨hrd, hwr, hl, ht⟩ := h
  have d8 := hl.2.2.2.2.2.2.2.1
  have d9 := hl.2.2.2.2.2.2.2.2.1
  refine perm_of hl (fun r hr => ?_) (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_left (covers_of_mem (by rw [hwr]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact d8.symm
    · exact ht.symm
    · exact d9.symm

theorem openPerm {s : State} (h : openPre s) : Perm (prmOf s) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have d8 := hl.2.2.2.2.2.2.2.1
  have d9 := hl.2.2.2.2.2.2.2.2.1
  refine perm_of hl (fun r hr => ?_) (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact d8.symm
  · exact d9.symm

/-! ## Frames within `W` -/

section
variable {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame [⟨State.addr p.W, 2560⟩] m m')
include L h

theorem sched_W : sched p m' = sched p m :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact L.k_w.sub_left (Region.sub_prefix (by have := L.rounds_le; omega))) (by have := L.rounds_le; omega)

theorem lstar_W : lstarOf p m' = lstarOf p m := by
  unfold lstarOf Spec.Ocb.ctxLstar
  exact blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_left (Offset.sub_base _ (by decide))

theorem nonce_W : bytesAt m' (State.addr p.N) p.nl = bytesAt m (State.addr p.N) p.nl :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.n_w)
    (by have := L.nl15; omega)

theorem aad_W : bytesAt m' (State.addr p.A) p.al = bytesAt m (State.addr p.A) p.al :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.a_w)
    (by have := L.al_lt; omega)

theorem data_W : bytesAt m' (State.addr p.D) p.n = bytesAt m (State.addr p.D) p.n :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.d_w)
    (by have := L.n_lt; omega)

theorem tag_W : bytesAt m' (State.addr p.T) p.tl = bytesAt m (State.addr p.T) p.tl :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.t_w)
    (by have := L.tl16; omega)

theorem args_W (A : Args p m) : Args p m' :=
  A.frame L h fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.w_args.symm

end

/-- Proves that a block of `W` misses a frame of parts of `W` and the stack
below `sp`. -/
macro "wdisj" L:term : tactic => `(tactic| (
  simp only [nonceR, hashR, bodyR, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  and_intros
  all_goals first
    | (with_reducible refine Lay.w_w $L ?_ ?_ ?_) <;> decide
    | (with_reducible refine (Lay.bw' $L ?_).symm) <;> decide
    | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide))

/-- Proves that the data misses a frame of parts of `W` and the stack below
`sp`. -/
macro "ddisj" L:term : tactic => `(tactic| (
  simp only [nonceR, hashR, bodyR, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  and_intros
  all_goals first
    | (with_reducible refine Lay.d_w' $L ?_) <;> decide
    | with_reducible exact (Lay.bd $L).symm))

/-! ## The entry -/

/-- What the entry leaves. -/
structure EntryPost (p : Prm) (s₀ s : State) : Prop where
  env : Env p s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r4 : s.gpr .r4 = p.N
  r5 : s.gpr .r5 = BitVec.ofNat 32 p.nl
  frame : Frame [⟨State.addr p.W, 2560⟩] s₀.mem s.mem
  saved : SavedAt s.mem p.W s₀
  ld : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem)
  l0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p s₀.mem) 0
  ck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0

theorem entry_wp {p : Prm} (L : Lay p) {s₀ : State} (P : Perm p s₀) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa (.block entry) s₀ (EntryPost p s₀) := by
  have fw := L.ww
  have fk := L.kw
  have i24 : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 24)) 4 := by
    rw [hsp]; exact P.argR' L (k := 24) (by decide)
  simp only [entry, lsetup, List.append_assoc]
  refine entry_ok (off := 24) (by decide) i24 (by rw [hW]; exact L.ww) (by rw [hW]; exact P.w)
    fun s₁ g12 g rd₁ wr₁ sp₁ sv₁ fr₁ => ?_
  rw [hW] at g12 sv₁ fr₁
  obtain ⟨s₂, run₂, E₂, r4₂, r5₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.mov .r11 (.reg .r12), .mov .r10 (.reg .r0),
      .mov .r9 (.reg .r1), .mov .r4 (.reg .r2), .mov .r5 (.reg .r3)] s₁ = some s₂ ∧ Env p s₂ ∧
      s₂.gpr .r4 = p.N ∧ s₂.gpr .r5 = BitVec.ofNat 32 p.nl ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr := by
    refine ⟨_, by orun [], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, by rfl, by simp [rd_setReg, rd₁], by simp [wr_setReg, wr₁]⟩
    · simp [gpr_setReg, g .r1 (by decide), h1]
    · simp [gpr_setReg, g .r0 (by decide), h0]
    · simp [gpr_setReg, g12]
    · simp [sp_setReg, sp₁, hsp]
    · exact P.of_eq (by simp [rd_setReg, rd₁]) (by simp [wr_setReg, wr₁])
    · simp [gpr_setReg, g .r2 (by decide), h2]
    · simp [gpr_setReg, g .r3 (by decide), h3]
  refine WP.block_append (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  -- `L_$`
  refine WP.block_append (WP.mono (dbl_wp (b := .r10) (t := s₂) (P := State.addr p.K) (W := State.addr p.W)
    (sO := 240) (dO := ldO) ⟨by decide, by decide, by decide⟩ (by rw [E₂.r10]) (by rw [E₂.r11]) (by decide)
    (by decide) (by rw [E₂.r10]; omega) (by rw [E₂.r11]; simp only [ldO]; omega) (E₂.perm.kC (by decide))
    (E₂.perm.wC (by decide))) fun s₃ R₃ => ?_)
  have E₃ := E₂.of_others R₃.gpr R₃.sp R₃.rd R₃.wr
  -- `L_0`
  refine WP.block_append (WP.mono (dbl_wp (b := .r11) (t := s₃) (P := State.addr p.W) (W := State.addr p.W)
    (sO := ldO) (dO := l0O) ⟨by decide, by decide, by decide⟩ (by rw [E₃.r11]) (by rw [E₃.r11]) (by decide)
    (by decide) (by rw [E₃.r11]; simp only [ldO]; omega) (by rw [E₃.r11]; simp only [l0O]; omega)
    (E₃.perm.wCR (by decide)) (E₃.perm.wC (by decide))) fun s₄ R₄ => ?_)
  have E₄ := E₃.of_others R₄.gpr R₄.sp R₄.rd R₄.wr
  -- the checksum
  refine WP.mono (zero16_wp (s := s₄) (o := ckO) (by decide) (by rw [E₄.r11]; simp only [ckO]; omega)
    (by rw [E₄.r11]; exact E₄.perm.wC (by decide))) fun s₅ R₅ => ?_
  rw [E₄.r11] at R₅
  have f₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ldO, 16⟩] s₂.mem s₃.mem := by
    rw [R₃.mem]; exact dblMem_frame _ _ _
  have f₄ : Frame [⟨State.addr p.W + BitVec.ofNat 64 l0O, 16⟩] s₃.mem s₄.mem := by
    rw [R₄.mem]; exact dblMem_frame _ _ _
  have f₅ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] s₄.mem s₅.mem := by
    rw [R₅.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have inW : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region)],
      ∃ r' ∈ [(⟨State.addr p.W, 2560⟩ : Region)], Region.Sub r r' := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, Lay.wSub h⟩
  have F₂ : Frame [⟨State.addr p.W, 2560⟩] s₀.mem s₂.mem := by rw [m₂]; exact fr₁.sub (inW (by decide))
  have F₅ : Frame [⟨State.addr p.W, 2560⟩] s₂.mem s₅.mem :=
    ((f₃.sub (inW (by decide))).trans (f₄.sub (inW (by decide)))).trans (f₅.sub (inW (by decide)))
  have hl : blockAtMem s₂.mem (State.addr p.K + BitVec.ofNat 64 240) = lstarOf p s₀.mem :=
    (lstar_W L F₂).symm ▸ rfl
  have ld₃ : blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem) := by
    rw [R₃.mem, blockAtMem_dbl, hl]; rfl
  have ld₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem) := by
    rw [blockAtMem_frame f₄ (by wdisj L), ld₃]
  have l0₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p s₀.mem) 0 := by
    rw [R₄.mem, blockAtMem_dbl, ld₃]; rfl
  refine ⟨E₄.of_others R₅.gpr R₅.sp R₅.rd R₅.wr, by rw [R₅.rd, R₄.rd, R₃.rd, rd₂],
    by rw [R₅.wr, R₄.wr, R₃.wr, wr₂], by rw [R₅.gpr _ (by decide), R₄.gpr _ (by decide), R₃.gpr _ (by decide), r4₂],
    by rw [R₅.gpr _ (by decide), R₄.gpr _ (by decide), R₃.gpr _ (by decide), r5₂], F₂.trans F₅, ?_,
    by rw [blockAtMem_frame f₅ (by wdisj L), ld₄], by rw [blockAtMem_frame f₅ (by wdisj L), l0₄],
    by rw [R₅.mem, blockAtMem_zero4]⟩
  rw [← m₂] at sv₁
  exact ((sv₁.frame f₃ (by wdisj L)).frame f₄ (by wdisj L)).frame f₅ (by wdisj L)

/-! ## Before the data -/

theorem nonceR_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (nonceR p) m m') : Frame (mutR p) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact below_mut L

/-- What the pieces before the data leave: the offset, the checksum, `L_$`,
`L_0` and `HASH`, and the inputs as they were. -/
structure Pre (p : Prm) (s₀ s : State) : Prop where
  env : Env p s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  args : Args p s.mem
  saved : SavedAt s.mem p.W s₀
  sched : sched p s.mem = sched p s₀.mem
  lstar : lstarOf p s.mem = lstarOf p s₀.mem
  data : bytesAt s.mem (State.addr p.D) p.n = bytesAt s₀.mem (State.addr p.D) p.n
  tag : bytesAt s.mem (State.addr p.T) p.tl = bytesAt s₀.mem (State.addr p.T) p.tl
  ofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ciphOf p s₀.mem) p.tl (bytesAt s₀.mem (State.addr p.N) p.nl)
  o0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ciphOf p s₀.mem) p.tl (bytesAt s₀.mem (State.addr p.N) p.nl)
  ck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem)
  l0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p s₀.mem) 0
  sum : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ciphOf p s₀.mem) (lstarOf p s₀.mem) (aadOf p s₀.mem)

/-- `entry`, `nonce` and `hash`. -/
theorem pre_wp' {p : Prm} (L : Lay p) {s₀ : State} (P : Perm p s₀) (A : Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa (.seq (.block entry) (.seq nonce Impl.AesOcb.Arm.hash)) s₀ (Pre p s₀) := by
  refine WP.seq (WP.mono (entry_wp L P hsp h0 h1 h2 h3 hW) fun s₁ P₁ => ?_)
  have A₁ := args_W L P₁.frame A
  refine WP.seq (WP.mono (nonce_ok L P₁.env A₁ P₁.r4 P₁.r5) fun s₂ N₂ => ?_)
  have F₂ := nonceR_mut L N₂.frame
  have l₂ : lstarOf p s₂.mem = lstarOf p s₀.mem := (lstar_mut L F₂).trans (lstar_W L P₁.frame)
  have l0₂ : blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) =
      blockAtMem s₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) := blockAtMem_frame N₂.frame (by wdisj L)
  refine WP.mono (hash_ok L N₂.env (A₁.mut L F₂) (by rw [l0₂, P₁.l0, l₂])) fun s₃ H₃ => ?_
  have F₃ := hashR_mut L H₃.frame
  have sc₂ : sched p s₂.mem = sched p s₀.mem := (sched_mut L F₂).trans (sched_W L P₁.frame)
  have c₂ : ciphOf p s₂.mem = ciphOf p s₀.mem := by simp only [ciphOf, sc₂]
  have c₁ : ciphOf p s₁.mem = ciphOf p s₀.mem := by simp only [ciphOf, sched_W L P₁.frame]
  have k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 192) ∨
      (216 ≤ d ∧ d + 16 ≤ 256)) →
      blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun {d} hd => blockAtMem_frame H₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact (L.bw' (by omega)).symm
  have k₂ : ∀ {d : Nat}, d ∈ [ckO, ldO, l0O] →
      blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun {d} hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> exact blockAtMem_frame N₂.frame (by wdisj L)
  refine ⟨H₃.env, by rw [H₃.rd, N₂.rd, P₁.rd], by rw [H₃.wr, N₂.wr, P₁.wr], (A₁.mut L F₂).mut L F₃,
    ((P₁.saved.frame N₂.frame (by wdisj L)).frame H₃.frame (by wdisj L)),
    (sched_mut L F₃).trans sc₂, (lstar_mut L F₃).trans l₂,
    by rw [Proof.Cmac.bytesAt_frame H₃.frame (by ddisj L) (by have := L.n_lt; omega),
      Proof.Cmac.bytesAt_frame N₂.frame (by ddisj L) (by have := L.n_lt; omega), data_W L P₁.frame],
    by rw [tag_mut L F₃, tag_mut L F₂, tag_W L P₁.frame], ?_, ?_,
    by rw [k₃ (by decide), k₂ (by simp), P₁.ck], by rw [k₃ (by decide), k₂ (by simp), P₁.ld],
    by rw [k₃ (by decide), k₂ (by simp), P₁.l0], ?_⟩
  · rw [k₃ (by decide), N₂.ofs]
    show Spec.Ocb.offset0 (ciphOf p s₁.mem) _ _ = _
    rw [c₁, nonce_W L P₁.frame]
  · rw [k₃ (by decide), N₂.o0]
    show Spec.Ocb.offset0 (ciphOf p s₁.mem) _ _ = _
    rw [c₁, nonce_W L P₁.frame]
  · rw [H₃.sum, c₂, l₂, aadOf, aad_mut L F₂, aad_W L P₁.frame]

end VG.Proof.AesOcb.Arm
