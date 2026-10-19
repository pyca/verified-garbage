module

public import VerifiedGarbage.Proof.Argon2.Arm.Push
public import VerifiedGarbage.Proof.AesCbc.Arm.Loop
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Impl.AesXts.ArmUnit
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesXts.Arm.Body
import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.AesXts.Arm.Unit.Contract

/-!
# XTS-AES of data units on ARMv7: a call of a whole-block function

`xts_call`: a call of `vg_aes_xts_encrypt` or `vg_aes_xts_decrypt` (`enc`
true or false), in the frame of its stack arguments (`xcall`), on `N` blocks
at `D`, from the tweak at `T`, with working space `S`, from its contract
(`frameCall_ok`): the blocks are then XTS of them, the tweak the one after
them, and only the tweak, the blocks, `S` and the 16 bytes below the stack
pointer change. `xts_rel`: such calls, with the same arguments and stack
pointer in both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.AesCbc.Arm (modeArm)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesXts.Unit (blocks_bytesAt)
open VG.Spec.Aes (bytesAt)

/-- The whole-block functions. -/
def xcode : Bool → Prog isa
  | true => Impl.AesXts.Arm.encrypt
  | false => Impl.AesXts.Arm.decrypt

abbrev xname : Bool → String
  | true => "vg_aes_xts_encrypt"
  | false => "vg_aes_xts_decrypt"

theorem xcall_eq (enc : Bool) :
    (match enc with | true => Impl.AesXts.ArmUnit.encCall | false => Impl.AesXts.ArmUnit.decCall) =
      .frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length)) := by
  cases enc <;> rfl

theorem xts_ok : ∀ enc s, (modeArm (AesXts.xtsMode enc)).pre s →
    ∃ t s', Exec isa (xcode enc) s t s' ∧ abiPreserved s s' ∧ (modeArm (AesXts.xtsMode enc)).post s s'
  | true, _, hs => AesCbc.Arm.whole_wp Proof.AesXts.Arm.encBody_ok hs
  | false, _, hs => AesCbc.Arm.whole_wp Proof.AesXts.Arm.decBody_ok hs

theorem xts_ct : ∀ enc, ConstantTime isa (modeArm (AesXts.xtsMode enc)).pre (modeArm (AesXts.xtsMode enc)).pub
    (xcode enc)
  | true => AesCbc.Arm.whole_ct Proof.AesXts.Arm.encBody_ok Proof.AesXts.Arm.encBody_ct
  | false => AesCbc.Arm.whole_ct Proof.AesXts.Arm.decBody_ok Proof.AesXts.Arm.decBody_ct

theorem xts_stack : ∀ enc, armStack (xcode enc) ≤ 8
  | true => by decide +kernel
  | false => by decide +kernel

/-- The 16 bytes below a stack pointer. -/
abbrev stk16 (sp : BitVec 32) : Region := ⟨State.addr sp - BitVec.ofNat 64 16, 16⟩

/-- What a call of a whole-block function on `N` blocks needs. -/
structure XPre (s : State) (W T D S : BitVec 32) (N R : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = T
  r3 : s.gpr .r3 = D
  r12 : s.gpr .r12 = BitVec.ofNat 32 N
  lr : s.gpr .lr = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n : N < 2 ^ 28
  sp16 : 16 ≤ s.sp.toNat
  wt : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr T, 16⟩
  wd : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr D, 16 * N⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  td : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * N⟩
  ts : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  ds : (⟨State.addr D, 16 * N⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  stkW : (stk16 s.sp).Disjoint ⟨State.addr W, 240⟩
  stkT : (stk16 s.sp).Disjoint ⟨State.addr T, 16⟩
  stkD : (stk16 s.sp).Disjoint ⟨State.addr D, 16 * N⟩
  stkS : (stk16 s.sp).Disjoint ⟨State.addr S, 2176⟩
  fitW : W.toNat + 240 ≤ 2 ^ 32
  fitT : T.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * N ≤ 2 ^ 32
  fitS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr T, 16⟩, ⟨State.addr D, 16 * N⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of a whole-block function on `N` blocks leaves. -/
structure XPost (enc : Bool) (s : State) (W T D S : BitVec 32) (N R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr T, 16⟩, ⟨State.addr D, 16 * N⟩, ⟨State.addr S, 2176⟩, stk16 s.sp] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem (State.addr D) N =
    Spec.Xts.crypt (ciphOf enc R (bytesAt s.mem (State.addr W) (16 * (R + 1)))) (bytesAt s.mem (State.addr T) 16)
      (Spec.Cbc.blocksAt s.mem (State.addr D) N)
  tw : bytesAt s'.mem (State.addr T) 16 = Spec.Xts.next (bytesAt s.mem (State.addr T) 16) N

theorem toNat_n {N : Nat} (h : N < 2 ^ 28) : (BitVec.ofNat 32 N).toNat = N := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem toNat_r {R : Nat} (h : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-- The regions the callee is given. -/
abbrev xRd (sp W : BitVec 32) : List Region := [⟨State.addr W, 240⟩, ⟨State.addr sp - BitVec.ofNat 64 8, 8⟩]
abbrev xWr (T D S : BitVec 32) (N : Nat) : List Region :=
  [⟨State.addr T, 16⟩, ⟨State.addr D, 16 * N⟩, ⟨State.addr S, 2176⟩]

/-- The state the callee runs from. -/
abbrev xView (s : State) (W T D S : BitVec 32) (N : Nat) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions (xRd s.sp W) (xWr T D S N)

namespace XPre
variable {s : State} {W T D S : BitVec 32} {N R : Nat} (h : XPre s W T D S N R)
include h

theorem h8 : 4 * [Reg.r12, .lr].length ≤ s.sp.toNat := by have := h.sp16; simp; omega

theorem below_sub : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ (stk16 s.sp) :=
  Argon2.Arm.stkR_sub (by decide) (by have := h.sp16; omega)

omit h in
theorem view_sp : (xView s W T D S N).sp = s.sp - BitVec.ofNat 32 8 := rfl

theorem view_below : (⟨State.addr (xView s W T D S N).sp - BitVec.ofNat 64 8, 8⟩ : Region) =
    ⟨State.addr s.sp - BitVec.ofNat 64 16, 8⟩ := by
  rw [view_sp, addr_sub' (by have := h.sp16; omega), BitVec.sub_sub, ← BitVec.ofNat_add]

omit h in
theorem below2_sub : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 16, 8⟩ (stk16 s.sp) :=
  Region.sub_prefix (by decide)

omit h in
theorem view_gpr (r : Reg) (hr : r ∉ linkRegs) : (xView s W T D S N).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem arg0 : stackArg (xView s W T D S N) 0 = BitVec.ofNat 32 N := by
  rw [Argon2.Arm.pushed_arg h.h8 (by decide)]; exact h.r12

theorem arg1 : stackArg (xView s W T D S N) 1 = S := by
  rw [Argon2.Arm.pushed_arg h.h8 (by decide)]; exact h.lr

theorem argAddr : stackArgAddr (xView s W T D S N) 0 = State.addr s.sp - BitVec.ofNat 64 8 :=
  Argon2.Arm.pushed_argAddr h.h8

theorem pre (enc : Bool) : (modeArm (AesXts.xtsMode enc)).pre (xView s W T D S N) := by
  have hR := toNat_r h.rounds
  have hN := toNat_n h.n
  have hsp : (xView s W T D S N).sp.toNat = s.sp.toNat - 8 := by
    rw [view_sp]; exact sub_toNat' (by have := h.sp16; omega)
  simp only [modeArm, h.arg0, h.arg1, h.argAddr, view_gpr .r0 (by decide), view_gpr .r1 (by decide),
    view_gpr .r2 (by decide), view_gpr .r3 (by decide), h.r0, h.r1, h.r2, h.r3, hR, hN, State.withRegions_rd,
    State.withRegions_wr, h.view_below, hsp]
  refine ⟨trivial, trivial, h.wt, h.wd, h.ws, h.td, h.ts, h.ds, (h.stkT.sub_left h.below_sub).symm,
    (h.stkD.sub_left h.below_sub).symm, (h.stkS.sub_left h.below_sub).symm, h.stkW.sub_left below2_sub,
    h.stkT.sub_left below2_sub, h.stkD.sub_left below2_sub, h.stkS.sub_left below2_sub,
    h.fitW, h.fitT, h.fitD, h.fitS, by have := h.sp16; omega, by have := s.sp.isLt; omega, h.rounds⟩

theorem cov : Covers (xRd s.sp W ++ xWr T D S N) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' ⟨r, hr, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r', hr', hc'⟩ := h.reads x n' ⟨_, List.mem_singleton_self _, hc⟩
    refine ⟨r', ?_, hc'⟩
    rcases List.mem_append.mp hr' with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')
  · refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rwa [show 4 * [Reg.r12, .lr].length = 8 from rfl, addr_sub' (by have := h.sp16; omega)]
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.writes x n' ⟨_, by simp, hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (xWr T D S N) (pushed [.r12, .lr] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

theorem fp : Frame [Argon2.Arm.stkR s.sp (4 * [Reg.r12, .lr].length)] s.mem (pushed [.r12, .lr] s).mem :=
  Argon2.Arm.pushed_stk h.h8

theorem push_keeps {X : Region} (hX : (stk16 s.sp).Disjoint X) (hn : X.len ≤ 2 ^ 64) :
    bytesAt (pushed [.r12, .lr] s).mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame h.fp (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hX.sub_left (Argon2.Arm.stkR_sub (a := 4 * [Reg.r12, .lr].length) (b := 16) (by decide) (by have := h.sp16; omega))).symm) hn

end XPre

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  rw [← blocks_bytesAt, ← blocks_bytesAt, Proof.Cmac.bytesAt_frame hf hd hn]

theorem xts_call (enc : Bool) {s : State} {W T D S : BitVec 32} {N R : Nat} (h : XPre s W T D S N R) :
    WP isa (.frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length))) s
      (XPost enc s W T D S N R) := by
  have hR := toNat_r h.rounds
  have hN := toNat_n h.n
  refine Argon2.Arm.frameCall_ok (rs := [.r12, .lr]) (t := .r12) (by decide) (by decide) (by decide)
    (n := xname enc) (c := xcode enc) (xts_ok enc) (K := 16) (by have := xts_stack enc; simp; omega) h.sp16 (h.pre enc) h.cov h.covW ?_
  intro s₂ a hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  have eW : bytesAt (pushed [.r12, .lr] s).mem (State.addr W) (16 * (R + 1)) =
      bytesAt s.mem (State.addr W) (16 * (R + 1)) :=
    h.push_keeps (X := ⟨State.addr W, 16 * (R + 1)⟩) (h.stkW.sub_right (Region.sub_prefix hRb)) (by dsimp only; omega)
  have eT : bytesAt (pushed [.r12, .lr] s).mem (State.addr T) 16 = bytesAt s.mem (State.addr T) 16 :=
    h.push_keeps (X := ⟨State.addr T, 16⟩) h.stkT (by simp)
  have eD : Spec.Cbc.blocksAt (pushed [.r12, .lr] s).mem (State.addr D) N = Spec.Cbc.blocksAt s.mem (State.addr D) N :=
    blocksAt_frame h.fp (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkD.sub_left (Argon2.Arm.stkR_sub (a := 4 * [Reg.r12, .lr].length) (b := 16) (by decide) (by have := h.sp16; omega))).symm)
      (by have := h.fitD; omega)
  simp only [modeArm, AesXts.xtsMode, State.withRegions_mem, State.callEntry_mem, h.arg0,
    XPre.view_gpr .r0 (by decide), XPre.view_gpr .r1 (by decide), XPre.view_gpr .r2 (by decide),
    XPre.view_gpr .r3 (by decide), h.r0, h.r1, h.r2, h.r3, hR, hN, Proof.AesXts.Unit.length_blocksAt,
    eW, eT, eD] at hpost
  refine ⟨a.rd, a.wr, a.sp, a.cs, ?_, ?_, ?_⟩
  · refine a.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · simpa using hpost.1
  · simpa using hpost.2

/-- Calls of a whole-block function, with the same arguments and stack
pointer in both runs, are constant time. -/
theorem xts_rel (enc : Bool) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : BitVec 32, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length)))
      fun _ _ => True := by
  refine (RelCT.exists_ (P := fun (q : (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) × (Nat × Nat) × BitVec 32)
      (a b : State) => XPre a q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2 ∧
        XPre b q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2 ∧ a.sp = q.2.2 ∧ b.sp = q.2.2) fun q => ?_).mono
    (fun a b hp => by
      obtain ⟨W, T, D, S, N, R, h₁, h₂, e⟩ := h a b hp
      exact ⟨((W, T, D, S), (N, R), a.sp), h₁, h₂, rfl, e.symm⟩) fun _ _ h => h
  obtain ⟨⟨W, T, D, S⟩, ⟨N, R⟩, sp⟩ := q
  refine Argon2.Arm.frameCall_rel (rs := [.r12, .lr]) (t := .r12) (by decide) (xts_ok enc) (xts_ct enc)
    (xRd sp W) (xWr T D S N) fun s₁ s₂ ⟨h₁, h₂, e₁, e₂⟩ => ?_
  dsimp only at h₁ h₂ e₁ e₂
  have p₁ := h₁.pre enc
  have p₂ := h₂.pre enc
  unfold xView at p₁ p₂
  rw [e₁] at p₁
  rw [e₂] at p₂
  have c₁ := h₁.cov
  have c₂ := h₂.cov
  rw [e₁] at c₁
  rw [e₂] at c₂
  refine ⟨by rw [e₁, e₂], p₁, p₂, ?_, c₁, h₁.covW, c₂, h₂.covW⟩
  have a₁ := (Argon2.Arm.pushed_arg (rd := xRd sp W) (wr := xWr T D S N) h₁.h8 (i := 0) (by decide)).trans h₁.r12
  have b₁ := (Argon2.Arm.pushed_arg (rd := xRd sp W) (wr := xWr T D S N) h₁.h8 (i := 1) (by decide)).trans h₁.lr
  have a₂ := (Argon2.Arm.pushed_arg (rd := xRd sp W) (wr := xWr T D S N) h₂.h8 (i := 0) (by decide)).trans h₂.r12
  have b₂ := (Argon2.Arm.pushed_arg (rd := xRd sp W) (wr := xWr T D S N) h₂.h8 (i := 1) (by decide)).trans h₂.lr
  simp only [modeArm, a₁, b₁, a₂, b₂, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    pushed_sp, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1,
    h₂.r2, h₂.r3, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesXts.Arm.Unit
