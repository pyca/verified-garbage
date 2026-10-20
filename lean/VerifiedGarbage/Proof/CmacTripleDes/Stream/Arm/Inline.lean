module

import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
import VerifiedGarbage.Proof.CmacTripleDes.Arm.FinalizeCorrect
import VerifiedGarbage.Proof.CmacTripleDes.Arm.CT
import VerifiedGarbage.Proof.CmacTripleDes.InlineCT
import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.Arm
public import VerifiedGarbage.Proof.CmacTripleDes.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming TDEA-CMAC on ARMv7: the code of `init`, `update` and `finalize`, inline

Each run of the code of `vg_cmac_triple_des_init`, `_update` and `_finalize`
inside the streaming functions, from its contract (`WP.inline`): what it
needs (`…Args`), what it leaves (`…Post`, in terms of the memory before it),
and that two runs with the same arguments leak the same (`…_rel`). `update`
and `finalize` take the working space on the stack: they run in a frame that
pushes its address (`WP.frameInline`, `RelCT.frameInline`), in the 4 bytes
below the stack pointer (`blw4`), which the pop loads back.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm
open VG.Arm.FrameStack (addr_sub' sub_toNat')
open VG.Proof.CmacTripleDes.Arm (updateArm finalizeArm initArm ciphAt scheduleAt_frame)

/-! ## Inlining in a frame -/

/-- The 4 bytes below the stack pointer. -/
abbrev blw4 (s : State) : Region := ⟨State.addr s.sp - 4, 4⟩

/-- The state code run in a frame pushing `ra` runs from, with the
permissions it is given. -/
abbrev view (ra : Reg) (s : State) (rd wr : List Region) : State := (pushed [ra] s).withRegions rd wr

theorem e4 (ra : Reg) : BitVec.ofNat 32 (4 * [ra].length) = 4 := rfl

theorem view_gpr {ra : Reg} {s : State} {rd wr : List Region} (r : Reg) : (view ra s rd wr).gpr r = s.gpr r := rfl

theorem view_sp {ra : Reg} {s : State} {rd wr : List Region} : (view ra s rd wr).sp = s.sp - 4 := rfl

section
variable {s : State} (hsp : 4 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 4) = State.addr s.sp - 4 := addr_sub' (k := 4) hsp

theorem spA : (s.sp - 4).toNat = s.sp.toNat - 4 := sub_toNat' (k := 4) hsp

theorem amem (ra : Reg) : (pushed [ra] s).mem = s.mem.writeW (State.addr s.sp - 4) (s.gpr ra) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [ra].length)) [s.gpr ra] = _
  rw [e4]
  show s.mem.writeW (State.addr (s.sp - 4)) (s.gpr ra) = _
  rw [hA hsp]

theorem push_frame (ra : Reg) : Frame [blw4 s] s.mem (pushed [ra] s).mem := by
  rw [amem hsp]
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem push_slot (ra : Reg) : (pushed [ra] s).mem.readW (State.addr s.sp - 4) 32 = s.gpr ra := by
  rw [amem hsp, Mem.readW_writeW_self32]

theorem view_argAddr {ra : Reg} {rd wr : List Region} : stackArgAddr (view ra s rd wr) 0 = State.addr s.sp - 4 := by
  unfold stackArgAddr; rw [view_sp, show s.sp - 4 + BitVec.ofNat 32 (4 * 0) = s.sp - 4 from
    BitVec.add_zero _, hA hsp]

/-- The stack argument, as the code reads it. -/
theorem view_arg0 {ra : Reg} {rd wr : List Region} : stackArg (view ra s rd wr) 0 = s.gpr ra := by
  rw [stackArg, view_argAddr hsp]; exact push_slot hsp ra

theorem view_spf {ra : Reg} {rd wr : List Region} : (view ra s rd wr).sp.toNat + 4 ≤ 2 ^ 32 := by
  rw [view_sp, spA hsp]; have := s.sp.isLt; omega

/-- The covering of the code's regions, from those of the frame's owner. -/
theorem cov_push {ra : Reg} {rd₀ wr : List Region} (hr : Covers rd₀ (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers ((rd₀ ++ [blw4 s]) ++ wr) ((pushed [ra] s).rd ++ (pushed [ra] s).wr) := by
  intro x n ⟨r, hr', hc⟩
  rcases List.mem_append.mp hr' with hr' | hr'
  · rcases List.mem_append.mp hr' with hr' | hr'
    · obtain ⟨r', hr'', hc'⟩ := hr x n ⟨r, hr', hc⟩
      refine ⟨r', ?_, hc'⟩
      rcases List.mem_append.mp hr'' with h' | h'
      · exact List.mem_append_left _ h'
      · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')
    · rw [List.mem_singleton] at hr'; subst hr'
      refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
      rwa [e4, hA hsp]
  · obtain ⟨r', hr'', hc'⟩ := hw x n ⟨r, hr', hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr''), hc'⟩

end

theorem covW_push {ra : Reg} {s : State} {wr : List Region} (hw : Covers wr s.wr) :
    Covers wr (pushed [ra] s).wr := by
  intro x n hi
  obtain ⟨r', hr', hc'⟩ := hw x n hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

/-- Verified code without calls, in the frame that pushes its stack argument
`ra`, from its contract `k`: it runs from `view`, and changes memory only
within the regions it may write and the 4 bytes below the stack pointer; the
pop loads `ra` back, so it changes no callee-saved register. -/
theorem WP.frameInline {ra : Reg} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noCalls = true) {s : State} (hsp : 4 ≤ s.sp.toNat)
    {rd wr : List Region} (hpre : k.pre (view ra s rd wr))
    (hc : Covers (rd ++ wr) ((pushed [ra] s).rd ++ (pushed [ra] s).wr))
    (hw : Covers wr (pushed [ra] s).wr) (hb : ∀ r ∈ wr, (blw4 s).Disjoint r) {Q : State → Prop}
    (hQ : ∀ s' s₂ : State, s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [blw4 s]) s.mem s'.mem → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      s'.mem = s₂.mem → k.post (view ra s rd wr) (s₂.withRegions rd wr) → Q s') :
    WP isa (.frame (.push [ra]) c (.pop ra 4)) s Q := by
  refine WP.frame (rs := [ra]) (r := ra) rfl (by simpa using hsp) (by simp) ?_
  refine WP.inline (k := k) hv hpre hc hw (fun s₂ hrd₂ hwr₂ ha hf _ hpost => ?_) hn
  have hsp₂ : s₂.sp = s.sp - 4 := ha.2
  -- The slot the pop loads.
  have slot : s₂.mem.readW (State.addr s₂.sp) 32 = s.gpr ra := by
    rw [hsp₂, hA hsp, hf.readW (r := blw4 s) (Region.contains_self _ _) (fun r hr => (hb r hr)) (by decide),
      push_slot hsp]
  refine hQ _ s₂ ?_ ?_ ?_ ?_ (fun r hr => ?_) (popped_mem _ _ _) hpost
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem]
    refine ((push_frame hsp ra).mono fun r hr => ?_).trans (hf.mono fun r hr => ?_)
    · exact List.mem_append_right _ hr
    · exact List.mem_append_left _ hr
  · by_cases hra : r = ra
    · subst hra
      show (s₂.setReg r (s₂.mem.readW (State.addr s₂.sp) 32)).gpr r = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, slot]
    · rw [popped_gpr hra, ha.1 r hr, pushed_gpr]

/-- Two runs of such code leak the same if its contract holds in both, its
public data agree, and the stack pointers are the same. -/
theorem RelCT.frameInline {ra : Reg} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {rd wr : List Region} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ 4 ≤ s₁.sp.toNat ∧ 4 ≤ s₂.sp.toNat ∧
      k.pre (view ra s₁ rd wr) ∧ k.pre (view ra s₂ rd wr) ∧ k.pub (view ra s₁ rd wr) (view ra s₂ rd wr) ∧
      Covers (rd ++ wr) ((pushed [ra] s₁).rd ++ (pushed [ra] s₁).wr) ∧ Covers wr (pushed [ra] s₁).wr ∧
      Covers (rd ++ wr) ((pushed [ra] s₂).rd ++ (pushed [ra] s₂).wr) ∧ Covers wr (pushed [ra] s₂).wr) :
    RelCT isa P (.frame (.push [ra]) c (.pop ra 4)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => (h _ _ hp).1) ?_
  refine relCT_inline regionModel (Post := fun s s' => abiPreserved s s' ∧ k.post s s') hv hct
    fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨-, h₁, h₂, p₁, p₂, q, c₁, w₁, c₂, w₂⟩ := h _ _ hp
  rw [push_pushed rfl (by simpa using h₁), Option.some.injEq] at pa
  rw [push_pushed rfl (by simpa using h₂), Option.some.injEq] at pb
  subst pa pb
  exact ⟨rd, wr, rd, wr, p₁, p₂, q, c₁, w₁, c₂, w₂⟩

/-! ## `update` -/

/-- The regions the code of `update` runs with. -/
abbrev uRd (s : State) (W D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr W, 384⟩, ⟨State.addr D, 8 * n⟩] ++ [blw4 s]
abbrev uWr (C S : BitVec 32) : List Region := [⟨State.addr C, 8⟩, ⟨State.addr S, 640⟩]

/-- What a run of `update` needs: the key schedule `W`, the chaining value
`C`, `n` blocks at `D` and the working space `S`, in `r10`. -/
structure UArgs (s : State) (W C D S : BitVec 32) (n : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = C
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  r10 : s.gpr .r10 = S
  hn : 8 * n < 2 ^ 32
  hsp : 4 ≤ s.sp.toNat
  wc : (⟨State.addr W, 384⟩ : Region).Disjoint ⟨State.addr C, 8⟩
  ws : (⟨State.addr W, 384⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  dc : (⟨State.addr D, 8 * n⟩ : Region).Disjoint ⟨State.addr C, 8⟩
  ds : (⟨State.addr D, 8 * n⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  cs : (⟨State.addr C, 8⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  bw : (blw4 s).Disjoint ⟨State.addr W, 384⟩
  bd : (blw4 s).Disjoint ⟨State.addr D, 8 * n⟩
  bc : (blw4 s).Disjoint ⟨State.addr C, 8⟩
  bs : (blw4 s).Disjoint ⟨State.addr S, 640⟩
  fW : W.toNat + 384 ≤ 2 ^ 32
  fC : C.toNat + 8 ≤ 2 ^ 32
  fD : D.toNat + 8 * n ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 384⟩, ⟨State.addr D, 8 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 8⟩, ⟨State.addr S, 640⟩] s.wr

/-- What a run of `update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 8⟩, ⟨State.addr S, 640⟩, blw4 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr C) 8 =
    Spec.Cmac.chain (ciphAt s.mem (State.addr W)) (Spec.Aes.bytesAt s.mem (State.addr C) 8)
      (Spec.Cmac.blocksAt s.mem (State.addr D) 8 n)

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem UArgs.pre {s : State} {W C D S : BitVec 32} {n : Nat} (h : UArgs s W C D S n) :
    updateArm.pre (view .r10 s (uRd s W D n) (uWr C S)) := by
  have hN := toNat_ofNat32 (n := n) (by have := h.hn; omega)
  simp only [updateArm, view_arg0 h.hsp, view_argAddr h.hsp, view_gpr, h.r0, h.r1, h.r2, h.r3, h.r10, hN,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨rfl, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.bc.symm, h.bs.symm, h.fW, h.fC, h.fD, h.fS,
    view_spf h.hsp⟩

theorem keep_push {s : State} (hsp : 4 ≤ s.sp.toNat) (ra : Reg) {p : Addr} {k : Nat}
    (hd : (blw4 s).Disjoint ⟨p, k⟩) (hk : k ≤ 2 ^ 64) :
    Spec.Aes.bytesAt (pushed [ra] s).mem p k = Spec.Aes.bytesAt s.mem p k :=
  Proof.Cmac.bytesAt_frame (push_frame hsp ra) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hd.symm) hk

theorem upd_wp {s : State} {W C D S : BitVec 32} {n : Nat} (h : UArgs s W C D S n) :
    WP isa Impl.CmacTripleDes.Stream.Arm.updFrame s (UPost s W C D S n) := by
  have hN := toNat_ofNat32 (n := n) (by have := h.hn; omega)
  refine WP.frameInline (k := updateArm) (fun _ hs => Proof.CmacTripleDes.Arm.update_wp hs) (by lit_decide)
    h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bc
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [updateArm, view_gpr, h.r0, h.r1, h.r2, h.r3, hN, State.withRegions_mem] at hpost
  have hsch : ciphAt (pushed [.r10] s).mem (State.addr W) = ciphAt s.mem (State.addr W) := by
    simp only [ciphAt]
    rw [scheduleAt_frame (push_frame h.hsp .r10) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h.bw.symm]
  rw [hm, hpost, hsch, keep_push h.hsp .r10 h.bc (by decide)]
  congr 1
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => keep_push h.hsp .r10 (h.bd.sub_right (Offset.sub_base _ ?_)) (by decide)
  rw [List.mem_range] at hi; omega

theorem upd_rel {W C D S sp₀ : BitVec 32} {n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S n ∧ UArgs s₂ W C D S n ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P Impl.CmacTripleDes.Stream.Arm.updFrame fun _ _ => True := by
  refine RelCT.frameInline (k := updateArm) (rd := [⟨State.addr W, 384⟩, ⟨State.addr D, 8 * n⟩] ++
    [⟨State.addr sp₀ - 4, 4⟩]) (wr := uWr C S)
    (fun _ hs => Proof.CmacTripleDes.Arm.update_wp hs) Proof.CmacTripleDes.Arm.update_ct fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : uRd s₁ W D n = [⟨State.addr W, 384⟩, ⟨State.addr D, 8 * n⟩] ++ [⟨State.addr sp₀ - 4, 4⟩] := by
    rw [uRd, blw4, e₁]
  have r₂ : uRd s₂ W D n = [⟨State.addr W, 384⟩, ⟨State.addr D, 8 * n⟩] ++ [⟨State.addr sp₀ - 4, 4⟩] := by
    rw [uRd, blw4, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  have c₁ := cov_push (ra := .r10) h₁.hsp h₁.reads h₁.writes
  have c₂ := cov_push (ra := .r10) h₂.hsp h₂.reads h₂.writes
  rw [blw4, e₁] at c₁
  rw [blw4, e₂] at c₂
  refine ⟨e₁.trans e₂.symm, h₁.hsp, h₂.hsp, p₁, p₂, ?_, c₁, covW_push h₁.writes, c₂, covW_push h₂.writes⟩
  simp only [updateArm, view_sp, view_arg0 h₁.hsp, view_arg0 h₂.hsp, view_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3,
    h₁.r10, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r10, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `finalize` -/

/-- The regions the code of `finalize` runs with. -/
abbrev fRd (s : State) (K P : BitVec 32) (L : Nat) : List Region :=
  [⟨State.addr K, 400⟩, ⟨State.addr P, L⟩] ++ [blw4 s]
abbrev fWr (St S : BitVec 32) : List Region := [⟨State.addr St, 8⟩, ⟨State.addr S, 640⟩]

/-- What a run of `finalize` needs: the key schedule and subkeys `K`, the
state `St`, the `L` last bytes at `P` and the working space `S`, in `r12`. -/
structure FArgs (s : State) (K St P S : BitVec 32) (L : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = St
  r2 : s.gpr .r2 = P
  r3 : s.gpr .r3 = BitVec.ofNat 32 L
  r12 : s.gpr .r12 = S
  len : L ≤ 8
  hsp : 4 ≤ s.sp.toNat
  kst : (⟨State.addr K, 400⟩ : Region).Disjoint ⟨State.addr St, 8⟩
  ks : (⟨State.addr K, 400⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  pst : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr St, 8⟩
  ps : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  sts : (⟨State.addr St, 8⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  bk : (blw4 s).Disjoint ⟨State.addr K, 400⟩
  bp : (blw4 s).Disjoint ⟨State.addr P, L⟩
  bst : (blw4 s).Disjoint ⟨State.addr St, 8⟩
  bs : (blw4 s).Disjoint ⟨State.addr S, 640⟩
  fK : K.toNat + 400 ≤ 2 ^ 32
  fSt : St.toNat + 8 ≤ 2 ^ 32
  fP : P.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, 400⟩, ⟨State.addr P, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr St, 8⟩, ⟨State.addr S, 640⟩] s.wr

/-- What a run of `finalize` leaves. -/
structure FPost (s : State) (K St P S : BitVec 32) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr St, 8⟩, ⟨State.addr S, 640⟩, blw4 s] s.mem s'.mem
  out : let ciph := ciphAt s.mem (State.addr K)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (State.addr K + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem (State.addr St) 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (State.addr St) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (State.addr P) L)

theorem FArgs.pre {s : State} {K St P S : BitVec 32} {L : Nat} (h : FArgs s K St P S L) :
    finalizeArm.pre (view .r12 s (fRd s K P L) (fWr St S)) := by
  have hL := toNat_ofNat32 (n := L) (by have := h.len; omega)
  simp only [finalizeArm, view_arg0 h.hsp, view_argAddr h.hsp, view_gpr, h.r0, h.r1, h.r2, h.r3, h.r12, hL,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨rfl, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.bst.symm, h.bs.symm, h.fK, h.fSt, h.fP, h.fS,
    view_spf h.hsp, h.len⟩

theorem fin_wp {s : State} {K St P S : BitVec 32} {L : Nat} (h : FArgs s K St P S L) :
    WP isa Impl.CmacTripleDes.Stream.Arm.finFrame s (FPost s K St P S L) := by
  have hL := toNat_ofNat32 (n := L) (by have := h.len; omega)
  refine WP.frameInline (k := finalizeArm) (fun _ hs => Proof.CmacTripleDes.Arm.finalize_wp hs) (by lit_decide)
    h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bst
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [finalizeArm, view_gpr, h.r0, h.r1, h.r2, h.r3, hL, State.withRegions_mem] at hpost
  have hsch : ciphAt (pushed [.r12] s).mem (State.addr K) = ciphAt s.mem (State.addr K) := by
    simp only [ciphAt]
    rw [scheduleAt_frame (push_frame h.hsp .r12) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (h.bk.sub_right (Region.sub_prefix (by decide))).symm]
  have eK2 := keep_push h.hsp .r12 (p := State.addr K + 384) (k := 16)
    (h.bk.sub_right (Offset.sub_base (State.addr K) (d := 384) (n := 16) (by decide))) (by decide)
  have eSt := keep_push h.hsp .r12 h.bst (by decide)
  have eP := keep_push h.hsp .r12 h.bp (by have := h.len; omega)
  intro _ _ hk msg hmod hne hst
  rw [hsch, eK2, eSt, eP] at hpost
  rw [hm]
  exact hpost hk msg hmod hne hst

theorem fin_rel {K St P S sp₀ : BitVec 32} {L : Nat} {Pr : State → State → Prop}
    (h : ∀ s₁ s₂, Pr s₁ s₂ → FArgs s₁ K St P S L ∧ FArgs s₂ K St P S L ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa Pr Impl.CmacTripleDes.Stream.Arm.finFrame fun _ _ => True := by
  refine RelCT.frameInline (k := finalizeArm) (rd := [⟨State.addr K, 400⟩, ⟨State.addr P, L⟩] ++
    [⟨State.addr sp₀ - 4, 4⟩]) (wr := fWr St S)
    (fun _ hs => Proof.CmacTripleDes.Arm.finalize_wp hs) Proof.CmacTripleDes.Arm.finalize_ct fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : fRd s₁ K P L = [⟨State.addr K, 400⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 4, 4⟩] := by
    rw [fRd, blw4, e₁]
  have r₂ : fRd s₂ K P L = [⟨State.addr K, 400⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 4, 4⟩] := by
    rw [fRd, blw4, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  have c₁ := cov_push (ra := .r12) h₁.hsp h₁.reads h₁.writes
  have c₂ := cov_push (ra := .r12) h₂.hsp h₂.reads h₂.writes
  rw [blw4, e₁] at c₁
  rw [blw4, e₂] at c₂
  refine ⟨e₁.trans e₂.symm, h₁.hsp, h₂.hsp, p₁, p₂, ?_, c₁, covW_push h₁.writes, c₂, covW_push h₂.writes⟩
  simp only [finalizeArm, view_sp, view_arg0 h₁.hsp, view_arg0 h₂.hsp, view_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3,
    h₁.r12, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r12, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `init` -/

/-- What a run of `init` needs: the key `Kp` of `KL` bytes, the output `O`
and the working space `S`. -/
structure IArgs (s : State) (Kp O S : BitVec 32) (KL : Nat) : Prop where
  r0 : s.gpr .r0 = Kp
  r1 : s.gpr .r1 = BitVec.ofNat 32 KL
  r2 : s.gpr .r2 = O
  r3 : s.gpr .r3 = S
  klen : Spec.TripleDes.validKey KL
  ko : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr O, 400⟩
  ks : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  os : (⟨State.addr O, 400⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fO : O.toNat + 400 ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers ([⟨State.addr Kp, KL⟩] ++ [⟨State.addr O, 400⟩, ⟨State.addr S, 640⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨State.addr O, 400⟩, ⟨State.addr S, 640⟩] s.wr

/-- What a run of `init` leaves. -/
structure IPost (s : State) (Kp O S : BitVec 32) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr O, 400⟩, ⟨State.addr S, 640⟩] s.mem s'.mem
  out : let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (State.addr Kp) KL)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (State.addr O) = k ∧
      Spec.Aes.bytesAt s'.mem (State.addr O + 384) 16 = ks.1 ++ ks.2

theorem IArgs.pre {s : State} {Kp O S : BitVec 32} {KL : Nat} (h : IArgs s Kp O S KL) :
    initArm.pre (s.withRegions [⟨State.addr Kp, KL⟩] [⟨State.addr O, 400⟩, ⟨State.addr S, 640⟩]) := by
  have hK := toNat_ofNat32 (n := KL) (by rcases h.klen with h | h <;> omega)
  simp only [initArm, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.r0, h.r1, h.r2,
    h.r3, hK]
  exact ⟨trivial, trivial, h.ko, h.ks, h.os, h.fK, h.fO, h.fS, h.klen⟩

theorem init_inline_wp {s : State} {Kp O S : BitVec 32} {KL : Nat} (h : IArgs s Kp O S KL) :
    WP isa Impl.CmacTripleDes.Arm.init s (IPost s Kp O S KL) := by
  have hK := toNat_ofNat32 (n := KL) (by rcases h.klen with h | h <;> omega)
  refine WP.inline (k := initArm) (fun _ hs => Proof.CmacTripleDes.Arm.init_wp hs) h.pre h.reads h.writes
    (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.2, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [initArm, State.withRegions_gpr, State.withRegions_mem, h.r0, h.r1, h.r2, hK] at hpost
  exact hpost

end VG.Proof.CmacTripleDes.Stream.Arm
