import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Rc2.Arm.Stream
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.Arm.Key
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Stream.Common`. -/
section

section

/-!
# Streaming RC2-CBC on ARMv7: the calls

The callees take their scratch buffer `S` on the stack: a frame pushes it
(`push {r12, lr}`, with `S` in `r12` at `[sp]`) around the call. `key_call`
and `cbc_call` run the frame around the call of `vg_rc2_expand_key` and of
the CBC function: memory changes only in the callee's writable buffers and
the 8 bytes below the stack pointer. `key_rel` and `cbc_rel`: the frames, with
the same arguments and stack pointer in two runs, are constant time.
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm

/-- Addresses below a pointer do not wrap. -/
theorem addr_sub {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat) (by omega)]
  omega

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

/-- The 8 bytes below the stack pointer, where the frame pushes `S` and `lr`. -/
abbrev below (s : State) : Region := ⟨State.addr s.sp - 8, 8⟩

/-- The callee's stack argument. -/
abbrev argR (s : State) : Region := ⟨State.addr s.sp - 8, 4⟩

/-- The state the callee runs from, with the permissions it is given. -/
abbrev view (s : State) (rd wr : List Region) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions rd wr

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = 8 := rfl

section
variable {s : State} (hsp : 8 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := VG.Proof.Rc2.Arm.Stream.addr_sub hsp

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  have e : (s.sp - 8).toNat = s.sp.toNat - 8 := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)
  rw [addr_add (by rw [e]; omega), VG.Proof.Rc2.Arm.Stream.hA hsp]; rfl

theorem amem : (pushed [.r12, .lr] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (s.gpr .r12)).writeW (State.addr s.sp - 8 + 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)) [s.gpr .r12, s.gpr .lr] = _
  rw [VG.Proof.Rc2.Arm.Stream.e8, VG.Proof.Rc2.Arm.Stream.storeWords_two, VG.Proof.Rc2.Arm.Stream.hA hsp, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl,
    VG.Proof.Rc2.Arm.Stream.hA4 hsp]

theorem fA : Frame [VG.Proof.Rc2.Arm.Stream.below s] s.mem (pushed [.r12, .lr] s).mem := by
  rw [VG.Proof.Rc2.Arm.Stream.amem hsp]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

theorem sa0 (rd wr : List Region) : stackArgAddr (VG.Proof.Rc2.Arm.Stream.view s rd wr) 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, VG.Proof.Rc2.Arm.Stream.e8]
  rw [show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from BitVec.add_zero _, VG.Proof.Rc2.Arm.Stream.hA hsp]

theorem arg0 (rd wr : List Region) : stackArg (VG.Proof.Rc2.Arm.Stream.view s rd wr) 0 = s.gpr .r12 := by
  rw [stackArg, VG.Proof.Rc2.Arm.Stream.sa0 hsp, State.withRegions_mem, State.callEntry_mem, VG.Proof.Rc2.Arm.Stream.amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem view_sp (rd wr : List Region) : (VG.Proof.Rc2.Arm.Stream.view s rd wr).sp.toNat = s.sp.toNat - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, VG.Proof.Rc2.Arm.Stream.e8]
  exact BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)

/-- The callee's regions, which the frame covers with `s`'s. -/
theorem cov {rd wr : List Region} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ VG.Proof.Rc2.Arm.Stream.argR s :: wr) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' ⟨r, hr', hc⟩
  rcases List.mem_append.mp hr' with h' | h'
  · obtain ⟨r', hr'', hc'⟩ := hr x n' ⟨r, h', hc⟩
    refine ⟨r', ?_, hc'⟩
    rcases List.mem_append.mp hr'' with h'' | h''
    · exact List.mem_append_left _ h''
    · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h'')
  · rcases List.mem_cons.mp h' with rfl | h'
    · have eb : (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
          4 * [Reg.r12, Reg.lr].length⟩ : Region) = VG.Proof.Rc2.Arm.Stream.below s := by rw [VG.Proof.Rc2.Arm.Stream.e8, VG.Proof.Rc2.Arm.Stream.hA hsp]; rfl
      refine ⟨VG.Proof.Rc2.Arm.Stream.below s, List.mem_append_right _ (by rw [pushed_wr, eb]; exact List.mem_cons_self ..), ?_⟩
      simp only [Region.Contains] at hc ⊢; omega
    · obtain ⟨r', hr'', hc'⟩ := hw x n' ⟨r, h', hc⟩
      exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr''), hc'⟩

end

theorem covW {s : State} {wr : List Region} (hw : Covers wr s.wr) : Covers wr (pushed [.r12, .lr] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := hw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

theorem view_gpr (s : State) (rd wr : List Region) (r : Reg) (hr : r ∉ linkRegs) :
    (VG.Proof.Rc2.Arm.Stream.view s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

/-! ## `vg_rc2_expand_key` -/

/-- What the call of `vg_rc2_expand_key` needs. -/
structure KeyPre (s : State) (K KL E O S : BitVec 32) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = KL
  r2 : s.gpr .r2 = E
  r3 : s.gpr .r3 = O
  r12 : s.gpr .r12 = S
  hsp : 8 ≤ s.sp.toNat
  valid : Spec.Rc2.validKey KL.toNat E.toNat
  ko : (⟨State.addr K, KL.toNat⟩ : Region).Disjoint ⟨State.addr O, 128⟩
  ks : (⟨State.addr K, KL.toNat⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  os : (⟨State.addr O, 128⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  bk : (VG.Proof.Rc2.Arm.Stream.below s).Disjoint ⟨State.addr K, KL.toNat⟩
  bo : (VG.Proof.Rc2.Arm.Stream.below s).Disjoint ⟨State.addr O, 128⟩
  bs : (VG.Proof.Rc2.Arm.Stream.below s).Disjoint ⟨State.addr S, 512⟩
  hK : K.toNat + KL.toNat ≤ 2 ^ 32
  hO : O.toNat + 128 ≤ 2 ^ 32
  hS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, KL.toNat⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr O, 128⟩, ⟨State.addr S, 512⟩] s.wr

/-- What the call of `vg_rc2_expand_key` leaves. -/
structure KeyPost (s : State) (K KL E O S : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr O, 128⟩, ⟨State.addr S, 512⟩, VG.Proof.Rc2.Arm.Stream.below s] s.mem s'.mem
  sched : Spec.Rc2.scheduleAt s'.mem (State.addr O) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (State.addr K) KL.toNat) E.toNat

abbrev keyRd (s : State) (K KL : BitVec 32) : List Region := [⟨State.addr K, KL.toNat⟩, VG.Proof.Rc2.Arm.Stream.argR s]
abbrev keyWr (O S : BitVec 32) : List Region := [⟨State.addr O, 128⟩, ⟨State.addr S, 512⟩]

theorem KeyPre.pre {s : State} {K KL E O S : BitVec 32} (h : VG.Proof.Rc2.Arm.Stream.KeyPre s K KL E O S) :
    keyContract.pre (VG.Proof.Rc2.Arm.Stream.view s (VG.Proof.Rc2.Arm.Stream.keyRd s K KL) (VG.Proof.Rc2.Arm.Stream.keyWr O S)) := by
  have hv := VG.Proof.Rc2.Arm.Stream.view_sp h.hsp (VG.Proof.Rc2.Arm.Stream.keyRd s K KL) (VG.Proof.Rc2.Arm.Stream.keyWr O S)
  simp only [keyContract, VG.Proof.Rc2.Arm.Stream.arg0 h.hsp, VG.Proof.Rc2.Arm.Stream.sa0 h.hsp, VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r0 (by decide), VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r1 (by decide),
    VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r2 (by decide), VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r3 (by decide), h.r0, h.r1, h.r2, h.r3, h.r12,
    State.withRegions_rd, State.withRegions_wr, hv]
  refine ⟨trivial, trivial, h.ko, h.ks, h.os, ?_, ?_, h.hK, h.hO, h.hS, by have := s.sp.isLt; omega, h.valid⟩
  · exact (h.bo.sub_left (Region.sub_prefix (by decide)))
  · exact (h.bs.sub_left (Region.sub_prefix (by decide)))

theorem key_noCalls : expandKey.noCalls = true := by decide +kernel

theorem key_call {s : State} {K KL E O S : BitVec 32} (h : VG.Proof.Rc2.Arm.Stream.KeyPre s K KL E O S) :
    WP isa Stream.keyCall s (VG.Proof.Rc2.Arm.Stream.KeyPost s K KL E O S) := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := keyContract) key_correct (rd := VG.Proof.Rc2.Arm.Stream.keyRd s K KL) (wr := VG.Proof.Rc2.Arm.Stream.keyWr O S) h.pre
    (VG.Proof.Rc2.Arm.Stream.cov h.hsp h.reads h.writes) (VG.Proof.Rc2.Arm.Stream.covW h.writes) ?_ VG.Proof.Rc2.Arm.Stream.key_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have bytesK : Spec.Rc2.bytesAt (pushed [.r12, .lr] s).mem (State.addr K) KL.toNat =
      Spec.Rc2.bytesAt s.mem (State.addr K) KL.toNat :=
    VG.Proof.Rc2.bytesAt_frame (VG.Proof.Rc2.Arm.Stream.fA h.hsp) _ _ (by omega) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bk.symm)
  change Spec.Rc2.scheduleAt s₂.mem _ = _ at hpost
  simp only [State.withRegions_mem, State.callEntry_mem, VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r0 (by decide),
    VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r1 (by decide), VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r2 (by decide), VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, bytesK] at hpost
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp, VG.Proof.Rc2.Arm.Stream.e8]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ .r12 := by intro e; subst e; simp [preserved] at hr
    rw [popped_gpr this, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine ((VG.Proof.Rc2.Arm.Stream.fA h.hsp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact hpost

theorem key_rel {K KL E O S sp₀ : BitVec 32} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Rc2.Arm.Stream.KeyPre s₁ K KL E O S ∧ VG.Proof.Rc2.Arm.Stream.KeyPre s₂ K KL E O S ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P Stream.keyCall fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, h₁, h₂⟩ := h _ _ hp; rw [h₁, h₂]) ?_
  refine RelCT.call key_correct expandKey_constantTime
    [⟨State.addr K, KL.toNat⟩, ⟨State.addr sp₀ - 8, 4⟩] (VG.Proof.Rc2.Arm.Stream.keyWr O S) fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨h₁, h₂, sp₁, sp₂⟩ := h _ _ hp
  rw [push_pushed rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  have e₁ : VG.Proof.Rc2.Arm.Stream.keyRd s₁ K KL = [⟨State.addr K, KL.toNat⟩, ⟨State.addr sp₀ - 8, 4⟩] := by rw [← sp₁]
  have e₂ : VG.Proof.Rc2.Arm.Stream.keyRd s₂ K KL = [⟨State.addr K, KL.toNat⟩, ⟨State.addr sp₀ - 8, 4⟩] := by rw [← sp₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  have c₁ := VG.Proof.Rc2.Arm.Stream.cov h₁.hsp h₁.reads h₁.writes
  have c₂ := VG.Proof.Rc2.Arm.Stream.cov h₂.hsp h₂.reads h₂.writes
  rw [show VG.Proof.Rc2.Arm.Stream.argR s₁ = ⟨State.addr sp₀ - 8, 4⟩ by rw [← sp₁]] at c₁
  rw [show VG.Proof.Rc2.Arm.Stream.argR s₂ = ⟨State.addr sp₀ - 8, 4⟩ by rw [← sp₂]] at c₂
  have a₁ := VG.Proof.Rc2.Arm.Stream.arg0 h₁.hsp (VG.Proof.Rc2.Arm.Stream.keyRd s₁ K KL) (VG.Proof.Rc2.Arm.Stream.keyWr O S)
  have a₂ := VG.Proof.Rc2.Arm.Stream.arg0 h₂.hsp (VG.Proof.Rc2.Arm.Stream.keyRd s₂ K KL) (VG.Proof.Rc2.Arm.Stream.keyWr O S)
  rw [VG.Proof.Rc2.Arm.Stream.view, e₁] at p₁ a₁
  rw [VG.Proof.Rc2.Arm.Stream.view, e₂] at p₂ a₂
  refine ⟨p₁, p₂, ?_, c₁, VG.Proof.Rc2.Arm.Stream.covW h₁.writes, c₂, VG.Proof.Rc2.Arm.Stream.covW h₂.writes⟩
  simp only [keyContract, a₁, a₂, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, pushed_sp, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1,
    h₂.r2, h₂.r3, h₁.r12, h₂.r12, sp₁, sp₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The CBC functions -/

theorem cbc_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (Cbc.contract d).pre s) :
    ∃ t s', Exec isa (Impl.Rc2.Arm.Cbc.cbc d) s t s' ∧ abiPreserved s s' ∧ (Cbc.contract d).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := Cbc.cbc_body_correct d s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem cbc_noFrames (d : Spec.Rc2.Direction) : (Impl.Rc2.Arm.Cbc.cbc d).noFrames = true := by
  cases d <;> decide +kernel

/-- The name of the CBC function. -/
def cbcName : Spec.Rc2.Direction → String
  | .encrypt => "vg_rc2_cbc_encrypt"
  | .decrypt => "vg_rc2_cbc_decrypt"

theorem cbcCall_eq (d : Spec.Rc2.Direction) : Stream.cbcCall d =
    .frame (.push [.r12, .lr]) (.call (VG.Proof.Rc2.Arm.Stream.cbcName d) (Impl.Rc2.Arm.Cbc.cbc d)) (.pop .r12 8) := by
  cases d <;> rfl

/-- What the call of the CBC function needs. -/
structure CbcPre (s : State) (K I D N S : BitVec 32) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = I
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = N
  r12 : s.gpr .r12 = S
  hsp : 8 ≤ s.sp.toNat
  ki : (⟨State.addr K, 128⟩ : Region).Disjoint ⟨State.addr I, 8⟩
  kd : (⟨State.addr K, 128⟩ : Region).Disjoint ⟨State.addr D, 8 * N.toNat⟩
  ks : (⟨State.addr K, 128⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  id : (⟨State.addr I, 8⟩ : Region).Disjoint ⟨State.addr D, 8 * N.toNat⟩
  is : (⟨State.addr I, 8⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  ds : (⟨State.addr D, 8 * N.toNat⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  bk : (VG.Proof.Rc2.Arm.Stream.below s).Disjoint ⟨State.addr K, 128⟩
  bi : (VG.Proof.Rc2.Arm.Stream.below s).Disjoint ⟨State.addr I, 8⟩
  bd : (VG.Proof.Rc2.Arm.Stream.below s).Disjoint ⟨State.addr D, 8 * N.toNat⟩
  bs : (VG.Proof.Rc2.Arm.Stream.below s).Disjoint ⟨State.addr S, 512⟩
  hK : K.toNat + 128 ≤ 2 ^ 32
  hI : I.toNat + 8 ≤ 2 ^ 32
  hD : D.toNat + 8 * N.toNat ≤ 2 ^ 32
  hS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, 128⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr I, 8⟩, ⟨State.addr D, 8 * N.toNat⟩, ⟨State.addr S, 512⟩] s.wr

/-- What the call of the CBC function leaves. -/
structure CbcPost (d : Spec.Rc2.Direction) (s : State) (K I D N S : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr I, 8⟩, ⟨State.addr D, 8 * N.toNat⟩, ⟨State.addr S, 512⟩, VG.Proof.Rc2.Arm.Stream.below s] s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (State.addr D) N.toNat =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr K)) d (Spec.Rc2.blockAt s.mem (State.addr I))
      (Spec.Rc2.blocksAt s.mem (State.addr D) N.toNat)).1
  iv : Spec.Rc2.blockAt s'.mem (State.addr I) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr K)) d (Spec.Rc2.blockAt s.mem (State.addr I))
      (Spec.Rc2.blocksAt s.mem (State.addr D) N.toNat)).2

abbrev cbcRd (s : State) (K : BitVec 32) : List Region := [⟨State.addr K, 128⟩, VG.Proof.Rc2.Arm.Stream.argR s]
abbrev cbcWr (I D N S : BitVec 32) : List Region :=
  [⟨State.addr I, 8⟩, ⟨State.addr D, 8 * N.toNat⟩, ⟨State.addr S, 512⟩]

theorem CbcPre.pre {d : Spec.Rc2.Direction} {s : State} {K I D N S : BitVec 32} (h : VG.Proof.Rc2.Arm.Stream.CbcPre s K I D N S) :
    (Cbc.contract d).pre (VG.Proof.Rc2.Arm.Stream.view s (VG.Proof.Rc2.Arm.Stream.cbcRd s K) (VG.Proof.Rc2.Arm.Stream.cbcWr I D N S)) := by
  have hv := VG.Proof.Rc2.Arm.Stream.view_sp h.hsp (VG.Proof.Rc2.Arm.Stream.cbcRd s K) (VG.Proof.Rc2.Arm.Stream.cbcWr I D N S)
  simp only [Cbc.contract, VG.Proof.Rc2.Arm.Stream.arg0 h.hsp, VG.Proof.Rc2.Arm.Stream.sa0 h.hsp, VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r0 (by decide), VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r1 (by decide),
    VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r2 (by decide), VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r3 (by decide), h.r0, h.r1, h.r2, h.r3, h.r12,
    State.withRegions_rd, State.withRegions_wr, hv]
  refine ⟨trivial, trivial, h.ki, h.kd, h.ks, h.id, h.is, h.ds, ?_, ?_, ?_, h.hK, h.hI, h.hS,
    by have := s.sp.isLt; omega, h.hD⟩
  · exact (h.bi.sub_left (Region.sub_prefix (by decide))).symm
  · exact (h.bd.sub_left (Region.sub_prefix (by decide))).symm
  · exact (h.bs.sub_left (Region.sub_prefix (by decide))).symm

theorem cbc_call {d : Spec.Rc2.Direction} {s : State} {K I D N S : BitVec 32} (h : VG.Proof.Rc2.Arm.Stream.CbcPre s K I D N S) :
    WP isa (Stream.cbcCall d) s (VG.Proof.Rc2.Arm.Stream.CbcPost d s K I D N S) := by
  rw [VG.Proof.Rc2.Arm.Stream.cbcCall_eq]
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.callCalls (k := Cbc.contract d) (VG.Proof.Rc2.Arm.Stream.cbc_correct' d) (rd := VG.Proof.Rc2.Arm.Stream.cbcRd s K) (wr := VG.Proof.Rc2.Arm.Stream.cbcWr I D N S) h.pre
    (VG.Proof.Rc2.Arm.Stream.cov h.hsp h.reads h.writes) (VG.Proof.Rc2.Arm.Stream.covW h.writes) ?_ (VG.Proof.Rc2.Arm.Stream.cbc_noFrames d)
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have fK := Proof.Rc2.scheduleAt_frame (VG.Proof.Rc2.Arm.Stream.fA h.hsp) (State.addr K) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bk.symm)
  have fI := Proof.Rc2.blockAt_frame (VG.Proof.Rc2.Arm.Stream.fA h.hsp) (State.addr I) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bi.symm)
  have fD := Proof.Rc2.blocksAt_frame (VG.Proof.Rc2.Arm.Stream.fA h.hsp) (State.addr D) N.toNat (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm)
  obtain ⟨p₁, p₂⟩ := hpost
  simp only [State.withRegions_mem, State.callEntry_mem, VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r0 (by decide),
    VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r1 (by decide), VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r2 (by decide), VG.Proof.Rc2.Arm.Stream.view_gpr _ _ _ .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, fK, fI, fD] at p₁ p₂
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp, VG.Proof.Rc2.Arm.Stream.e8]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ .r12 := by intro e; subst e; simp [preserved] at hr
    rw [popped_gpr this, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine ((VG.Proof.Rc2.Arm.Stream.fA h.hsp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact p₁
  · rw [popped_mem]; exact p₂

theorem cbc_rel {d : Spec.Rc2.Direction} {K I D N S sp₀ : BitVec 32} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Rc2.Arm.Stream.CbcPre s₁ K I D N S ∧ VG.Proof.Rc2.Arm.Stream.CbcPre s₂ K I D N S ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P (Stream.cbcCall d) fun _ _ => True := by
  rw [VG.Proof.Rc2.Arm.Stream.cbcCall_eq]
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, h₁, h₂⟩ := h _ _ hp; rw [h₁, h₂]) ?_
  refine RelCT.call (VG.Proof.Rc2.Arm.Stream.cbc_correct' d) (Cbc.cbc_constantTime d)
    [⟨State.addr K, 128⟩, ⟨State.addr sp₀ - 8, 4⟩] (VG.Proof.Rc2.Arm.Stream.cbcWr I D N S) fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨h₁, h₂, sp₁, sp₂⟩ := h _ _ hp
  rw [push_pushed rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  have e₁ : VG.Proof.Rc2.Arm.Stream.cbcRd s₁ K = [⟨State.addr K, 128⟩, ⟨State.addr sp₀ - 8, 4⟩] := by rw [← sp₁]
  have e₂ : VG.Proof.Rc2.Arm.Stream.cbcRd s₂ K = [⟨State.addr K, 128⟩, ⟨State.addr sp₀ - 8, 4⟩] := by rw [← sp₂]
  have p₁ := h₁.pre (d := d)
  have p₂ := h₂.pre (d := d)
  have c₁ := VG.Proof.Rc2.Arm.Stream.cov h₁.hsp h₁.reads h₁.writes
  have c₂ := VG.Proof.Rc2.Arm.Stream.cov h₂.hsp h₂.reads h₂.writes
  rw [show VG.Proof.Rc2.Arm.Stream.argR s₁ = ⟨State.addr sp₀ - 8, 4⟩ by rw [← sp₁]] at c₁
  rw [show VG.Proof.Rc2.Arm.Stream.argR s₂ = ⟨State.addr sp₀ - 8, 4⟩ by rw [← sp₂]] at c₂
  have a₁ := VG.Proof.Rc2.Arm.Stream.arg0 h₁.hsp (VG.Proof.Rc2.Arm.Stream.cbcRd s₁ K) (VG.Proof.Rc2.Arm.Stream.cbcWr I D N S)
  have a₂ := VG.Proof.Rc2.Arm.Stream.arg0 h₂.hsp (VG.Proof.Rc2.Arm.Stream.cbcRd s₂ K) (VG.Proof.Rc2.Arm.Stream.cbcWr I D N S)
  rw [VG.Proof.Rc2.Arm.Stream.view, e₁] at p₁ a₁
  rw [VG.Proof.Rc2.Arm.Stream.view, e₂] at p₂ a₂
  refine ⟨p₁, p₂, ?_, c₁, VG.Proof.Rc2.Arm.Stream.covW h₁.writes, c₂, VG.Proof.Rc2.Arm.Stream.covW h₂.writes⟩
  simp only [Cbc.contract, a₁, a₂, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, pushed_sp, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1,
    h₂.r2, h₂.r3, h₁.r12, h₂.r12, sp₁, sp₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.Rc2.Arm.Stream

end

section

/-!
# Streaming RC2-CBC on ARMv7: the byte copy

`copy_wp`: the copy of `L` bytes from `src + so` to `dst + dd`
(`Impl.Rc2.Arm.Stream.copy`), for any registers, offsets and count, writes the
source bytes at the destination (`writeBytes`), advances both pointers by `L`,
and changes no other register but `r12` and the count.
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldr
  wp_str wp_ldrb wp_strb wp_ldrSp eval_eq eval_ne ofNat_beq_zero sub_ofNat cmp0)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)

theorem byte_rt32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

/-- The address of byte `i` of a buffer at `p + o` that does not wrap around. -/
theorem addr_off {p : BitVec 32} {i o : Nat} (h : p.toNat + o + i < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 i + BitVec.ofNat 32 o) =
      State.addr p + BitVec.ofNat 64 o + BitVec.ofNat 64 i := by
  rw [Offset.add_add, Offset.add_add, Nat.add_comm i o, addr_add (by omega)]

/-- What a copy leaves. -/
structure CopyPost (s : State) (src dst cnt : Reg) (A B : Addr) (L : Nat) (s' : State) : Prop where
  mem : s'.mem = VG.WriteBytes.writeBytes s.mem B (Spec.Rc2.bytesAt s.mem A L)
  srcv : s'.gpr src = s.gpr src + BitVec.ofNat 32 L
  dstv : s'.gpr dst = s.gpr dst + BitVec.ofNat 32 L
  keep : ∀ r, r ≠ src → r ≠ dst → r ≠ cnt → r ≠ .r12 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_wp {s : State} {src dst cnt : Reg} {so dd L : Nat}
    (h1 : src ≠ dst) (h2 : src ≠ cnt) (h3 : dst ≠ cnt) (h4 : src ≠ .r12) (h5 : dst ≠ .r12)
    (h6 : cnt ≠ .r12) (hso : so < 4096) (hdd : dd < 4096)
    (hc : s.gpr cnt = BitVec.ofNat 32 L) (hL : L < 2 ^ 32)
    (fp : (s.gpr src).toNat + so + L ≤ 2 ^ 32) (fd : (s.gpr dst).toNat + dd + L ≤ 2 ^ 32)
    (hr : 0 < L → Covers [⟨State.addr (s.gpr src) + BitVec.ofNat 64 so, L⟩] (s.rd ++ s.wr))
    (hw : 0 < L → Covers [⟨State.addr (s.gpr dst) + BitVec.ofNat 64 dd, L⟩] s.wr)
    (hd : 0 < L → (⟨State.addr (s.gpr src) + BitVec.ofNat 64 so, L⟩ : Region).Disjoint
      ⟨State.addr (s.gpr dst) + BitVec.ofNat 64 dd, L⟩) :
    WP isa (copy src so dst dd cnt) s (VG.Proof.Rc2.Arm.Stream.CopyPost s src dst cnt
      (State.addr (s.gpr src) + BitVec.ofNat 64 so) (State.addr (s.gpr dst) + BitVec.ofNat 64 dd) L) := by
  generalize hP : s.gpr src = P at *
  generalize hD : s.gpr dst = D at *
  generalize hA : State.addr P + BitVec.ofNat 64 so = A at *
  generalize hB : State.addr D + BitVec.ofNat 64 dd = B at *
  rw [copy]
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun t₀ f₀ z₀ => WP.block_nil ?_)
  have hz : t₀.z = decide (L = 0) := by rw [z₀, hc, cmp0 (by omega)]
  refine WP.ite (decide (L = 0)) (by rw [← hz]; rfl) (fun hL0 => WP.block_nil ?_) fun hL0 => ?_
  · have hL0 : L = 0 := of_decide_eq_true hL0
    subst hL0
    refine ⟨?_, ?_, ?_, fun r _ _ _ _ => ?_, f₀.sp, f₀.rd, f₀.wr⟩
    · rw [f₀.mem]; simp [Spec.Rc2.bytesAt, VG.WriteBytes.writeBytes_nil]
    · rw [f₀.gpr, hP]; exact (BitVec.add_zero P).symm
    · rw [f₀.gpr, hD]; exact (BitVec.add_zero D).symm
    · rw [f₀.gpr]
  have hL₀ : 0 < L := by have := of_decide_eq_false hL0; omega
  have hr := hr hL₀
  have hw := hw hL₀
  have hd := hd hL₀
  refine WP.loop (M := isa) (body := .block (VG.Impl.Rc2.Arm.Stream.copyBody src so dst dd cnt)) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr src = P + BitVec.ofNat 32 i ∧
      t.gpr dst = D + BitVec.ofNat 32 i ∧ t.gpr cnt = BitVec.ofNat 32 (L - i) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem B (Spec.Rc2.bytesAt s.mem A i) ∧
      (∀ r, r ≠ src → r ≠ dst → r ≠ cnt → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [f₀.gpr, hP]; exact (BitVec.add_zero P).symm,
      by rw [f₀.gpr, hD]; exact (BitVec.add_zero D).symm, by rw [f₀.gpr, hc, Nat.sub_zero],
      by rw [f₀.mem]; simp [Spec.Rc2.bytesAt, VG.WriteBytes.writeBytes_nil], fun r _ _ _ _ => by rw [f₀.gpr],
      f₀.sp, f₀.rd, f₀.wr⟩
  rintro n t ⟨i, rfl, hi, xs, xd, xc, mem, g, sp, rd, wr⟩
  refine wp_ldrb (a := A + BitVec.ofNat 64 i) hso (by rw [xs, ← hA]; exact VG.Proof.Rc2.Arm.Stream.addr_off (by omega))
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ u₁ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 i) hdd
    (by rw [u₁.other _ h5, xd, ← hB]; exact VG.Proof.Rc2.Arm.Stream.addr_off (by omega))
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Rc2.bytesAt s.mem A i).length = i := Proof.Rc2.bytesAt_length _ _ _
  have hx : VG.WriteBytes.writeBytes s.mem B (Spec.Rc2.bytesAt s.mem A i) (A + BitVec.ofNat 64 i) =
      s.mem (A + BitVec.ofNat 64 i) :=
    (VG.WriteBytes.writeBytes_frame s.mem B _ (R := ⟨B, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t₅.mem = VG.WriteBytes.writeBytes s.mem B (Spec.Rc2.bytesAt s.mem A (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, VG.Proof.Rc2.Arm.Stream.byte_rt32, hx, Proof.Rc2.bytesAt_succ,
      VG.WriteBytes.writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have e1 : (1 : BitVec 32) = BitVec.ofNat 32 1 := rfl
  have cs : t₄.gpr cnt = BitVec.ofNat 32 (L - i) := by
    rw [u₄.other _ (Ne.symm h3), u₃.other _ (Ne.symm h2), v₂.gpr, u₁.other _ h6, xc]
  have xc' : t₅.gpr cnt = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, cs, e1, sub_ofNat (by omega)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.Arm.eval .ne t₅ = _
    rw [eval_ne, z₅, cs, e1, sub_ofNat (by omega), Nat.sub_sub, ofNat_beq_zero (by omega)]
  have gg : ∀ r, r ≠ src → r ≠ dst → r ≠ cnt → r ≠ .r12 → t₅.gpr r = s.gpr r := fun r a b c d => by
    rw [u₅.other _ c, u₄.other _ b, u₃.other _ a, v₂.gpr, u₁.other _ d, g r a b c d]
  have xd' : t₅.gpr dst = D + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ h3, u₄.gpr, u₃.other _ (Ne.symm h1), v₂.gpr, u₁.other _ h5, xd, e1, Offset.add_add]
  have xs' : t₅.gpr src = P + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ h2, u₄.other _ h1, u₃.gpr, v₂.gpr, u₁.other _ h4, xs, e1, Offset.add_add]
  have sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    refine ⟨by rw [ev]; simp [he], ⟨by rw [hmem, he], by rw [xs', he, hP], by rw [xd', he, hD], gg,
      sp', rd', wr'⟩⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, xs', xd', xc', hmem, gg,
      sp', rd', wr'⟩

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : Spec.Rc2.bytesAt (VG.WriteBytes.writeBytes m q xs) q n = xs := by
  subst hn
  apply List.ext_getElem (by simp [Spec.Rc2.bytesAt])
  intro i h1 _
  simp only [Spec.Rc2.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Rc2.bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h1, ↓reduceIte,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

end VG.Proof.Rc2.Arm.Stream

end

section

/-!
# Streaming RC2-CBC on ARMv7: the contracts, spelled out

The contracts of `vg_rc2_cbc_init` and the update functions with their facts
written out for ARMv7 and a stack of 8 bytes (`initContract`,
`updateContract`), which imply the shared ones (`init_implies`,
`update_implies`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm

def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let iv : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    let ctx : Region := ⟨State.addr (stackArg s 1), 144⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 576⟩
    let below : Region := ⟨State.addr s.sp - 8, 8⟩
    8 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32 ∧ s.rd = [key, iv, args] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ iv.Disjoint ctx ∧ iv.Disjoint scr ∧ ctx.Disjoint scr ∧
      ctx.Disjoint args ∧ scr.Disjoint args ∧ below.Disjoint key ∧ below.Disjoint iv ∧
      below.Disjoint ctx ∧ below.Disjoint scr ∧ below.Disjoint args ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 144 ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + 576 ≤ 2 ^ 32
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits
        (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
        (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat) direction
        (s.gpr .r2).toNat with
      | .ok c => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        Spec.Rc2.contextAt s'.mem (State.addr (stackArg s 1)) direction 0 = c
      | .error e => (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = e.code
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

def updateContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨State.addr (s.gpr .r0), 144⟩
    let data : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let out : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 576⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    let below : Region := ⟨State.addr s.sp - 8, 8⟩
    8 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32 ∧ s.rd = [data, args] ∧ s.wr = [ctx, out, scr] ∧
      ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧
      data.Disjoint out ∧ data.Disjoint scr ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      scr.Disjoint args ∧ below.Disjoint ctx ∧ below.Disjoint data ∧ below.Disjoint out ∧
      below.Disjoint scr ∧ below.Disjoint args ∧
      (s.gpr .r0).toNat + 144 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + 576 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat < 8 ∧ (stackArg s 1).toNat = ((s.gpr .r1).toNat + (s.gpr .r3).toNat) / 8 * 8
  post s s' :=
    let result := Spec.Rc2.update (Spec.Rc2.contextAt s.mem (State.addr (s.gpr .r0)) d (s.gpr .r1).toNat)
      (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    Spec.Rc2.contextAt s'.mem (State.addr (s.gpr .r0)) d (((s.gpr .r1).toNat + (s.gpr .r3).toNat) % 8) =
        result.1 ∧
      Spec.Rc2.bytesAt s'.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat = result.2
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

def initSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r3 => 0x2000 | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6005 then 0x30 else if a = 0x6009 then 0x40 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6000, 12⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

def updateSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000 | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x30 else if a = 0x6009 then 0x40 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x6000, 12⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩]

theorem init_implies : initContract.Implies (Proof.Rc2.cbcInitScratchContract abi 8) := by
  sig_implies [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, VG.Proof.Rc2.Arm.Stream.initContract]
    [initSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.Arm.Stream.initSatState

theorem update_implies (d : Spec.Rc2.Direction) :
    (VG.Proof.Rc2.Arm.Stream.updateContract d).Implies (Proof.Rc2.cbcUpdateScratchContract abi d 8) := by
  sig_implies [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, VG.Proof.Rc2.Arm.Stream.updateContract]
    [updateSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.Arm.Stream.updateSatState

end VG.Proof.Rc2.Arm.Stream

end

/-!
# Streaming RC2-CBC on ARMv7: facts shared by the proofs

Sub-ranges of buffers, stack arguments, and the preconditions of `update` and
`init` by name (`UPre`, `IPre`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm

theorem ofNat_toNat32 (x : BitVec 32) : x = BitVec.ofNat 32 x.toNat := by simp

theorem add0 (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

theorem e128 : (128 : Addr) = BitVec.ofNat 64 128 := rfl
theorem e136 : (136 : Addr) = BitVec.ofNat 64 136 := rfl
theorem e512 : (512 : Addr) = BitVec.ofNat 64 512 := rfl

/-- A range at an offset within a region of `rs`. -/
theorem cov1 {rs : List Region} {b : Addr} {len : Nat} (hR : (⟨b, len⟩ : Region) ∈ rs) {off n : Nat}
    (h : off + n ≤ len) : Covers [⟨b + BitVec.ofNat 64 off, n⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, hR, off, rfl, h⟩

/-- The `i`-th stack argument, of the 12 bytes of them. -/
theorem stackArgAddr_eq (s : State) {i : Nat} (hi : i < 3) (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  unfold stackArgAddr
  rw [show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp from BitVec.add_zero _, addr_add (by omega)]

theorem argIn {s : State} {rs : List Region} (hR : (⟨stackArgAddr s 0, 12⟩ : Region) ∈ rs) {i : Nat}
    (hi : i < 3) (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) : InRegions rs (stackArgAddr s i) 4 := by
  rw [VG.Proof.Rc2.Arm.Stream.stackArgAddr_eq s hi hsp]
  exact ⟨_, hR, Offset.contains_base _ (by omega) (by omega)⟩

theorem ldrSp_addr (s : State) (i : Nat) :
    State.addr (s.sp + BitVec.ofNat 32 (4 * i)) = stackArgAddr s i := rfl

/-- Memory reads of 1 byte within a word written elsewhere. -/
theorem bytesAt_writeW {m : Mem} {p a : Addr} {n : Nat} (v : BitVec 32) (hn : n ≤ 2 ^ 64)
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨a, 4⟩) :
    Spec.Rc2.bytesAt (m.writeW a v) p n = Spec.Rc2.bytesAt m p n :=
  VG.Proof.Rc2.bytesAt_frame ((Frame.refl _ _).writeW (r := ⟨a, 4⟩) (List.mem_singleton_self _) _
    (Region.contains_self _ _)) p n hn (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)

/-- A stack argument, read from memory that changed only outside the arguments. -/
theorem stackArg_frame {s : State} {m : Mem} {rs : List Region} (hf : Frame rs s.mem m)
    (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) (hd : ∀ r ∈ rs, (⟨stackArgAddr s 0, 12⟩ : Region).Disjoint r)
    {i : Nat} (hi : i < 3) : m.readW (stackArgAddr s i) 32 = stackArg s i := by
  rw [stackArg]
  refine hf.readW ?_ hd (by decide)
  rw [VG.Proof.Rc2.Arm.Stream.stackArgAddr_eq s hi hsp]
  exact Offset.contains_base _ (by omega) (by omega)

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) (hl : r ≠ .lr) :
    r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hl | decide

/-- `t` is `s` but for `r12` and the flags. -/
structure Keep (s t : State) : Prop where
  reg : ∀ r, r ≠ .r12 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

/-- `copy_wp`, with the buffers' addresses named. -/
theorem copy_ok {s : State} {src dst cnt : Reg} {so dd L : Nat} {A B : Addr}
    (h1 : src ≠ dst) (h2 : src ≠ cnt) (h3 : dst ≠ cnt) (h4 : src ≠ .r12) (h5 : dst ≠ .r12)
    (h6 : cnt ≠ .r12) (hso : so < 4096) (hdd : dd < 4096)
    (hc : s.gpr cnt = BitVec.ofNat 32 L) (hL : L < 2 ^ 32)
    (fp : (s.gpr src).toNat + so + L ≤ 2 ^ 32) (fd : (s.gpr dst).toNat + dd + L ≤ 2 ^ 32)
    (hA : State.addr (s.gpr src) + BitVec.ofNat 64 so = A)
    (hB : State.addr (s.gpr dst) + BitVec.ofNat 64 dd = B)
    (hr : 0 < L → Covers [⟨A, L⟩] (s.rd ++ s.wr)) (hw : 0 < L → Covers [⟨B, L⟩] s.wr)
    (hd : 0 < L → (⟨A, L⟩ : Region).Disjoint ⟨B, L⟩) :
    WP isa (Impl.Rc2.Arm.Stream.copy src so dst dd cnt) s (VG.Proof.Rc2.Arm.Stream.CopyPost s src dst cnt A B L) := by
  subst hA hB
  exact VG.Proof.Rc2.Arm.Stream.copy_wp h1 h2 h3 h4 h5 h6 hso hdd hc hL fp fd hr hw hd

theorem writeBytes_frame' (m : Mem) (q : Addr) (xs : List Byte) {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (VG.WriteBytes.writeBytes m q xs) :=
  VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hn]; exact Region.contains_self _ _)

end VG.Proof.Rc2.Arm.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Stream.Long`. -/
section

/-! # Streaming RC2-CBC on ARMv7: the copies before CBC

With `out_len ≠ 0`: `lr` saved at `scratch + 512`, the pending bytes and the
first `out_len - pending_len` bytes of data to `out`, the rest of the data to
`ctx + 136`, and the arguments of the CBC function (`Mid`). -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.WriteBytes VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_str wp_ldrSp
  sub_ofNat ofNat_shr)

theorem toNat_add32 {a : BitVec 32} {k : Nat} (h : a.toNat + k < 2 ^ 32) :
    (a + BitVec.ofNat 32 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

/-- The state before the call of the CBC function, from the entry state `s`. -/
structure Mid (s t : State) : Prop where
  r0 : t.gpr .r0 = s.gpr .r0
  r1 : t.gpr .r1 = s.gpr .r0 + 128
  r2 : t.gpr .r2 = stackArg s 0
  r3 : t.gpr .r3 = BitVec.ofNat 32 ((stackArg s 1).toNat / 8)
  r12 : t.gpr .r12 = stackArg s 2
  callee : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  /-- Memory changed only in `out`, the pending block and the saved `lr`. -/
  frame : Frame [⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩,
    ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 136, 8⟩,
    ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩] s.mem t.mem
  lr : t.mem.readW (State.addr (stackArg s 2) + BitVec.ofNat 64 512) 32 = s.gpr .lr
  out : Spec.Rc2.bytesAt t.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat =
    Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 136) (s.gpr .r1).toNat ++
      Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r2)) ((stackArg s 1).toNat - (s.gpr .r1).toNat)
  pend : Spec.Rc2.bytesAt t.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 136)
      (((s.gpr .r1).toNat + (s.gpr .r3).toNat) % 8) =
    Spec.Rc2.bytesAt s.mem
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 ((stackArg s 1).toNat - (s.gpr .r1).toNat))
      (((s.gpr .r1).toNat + (s.gpr .r3).toNat) % 8)

/-- The code before the call, followed by `tail`. -/
def longWith (tail : Prog isa) : Prog isa :=
  .seq (.block toOut) (.seq (copy .r0 136 .lr 0 .r1) (.seq (.block middle) (.seq (copy .r2 0 .lr 0 .r1)
    (.seq (.block toPending) (.seq (copy .r2 0 .lr 136 .r3) (.seq (.block cbcArgs) tail))))))

theorem long_eq (d : Spec.Rc2.Direction) : long d = VG.Proof.Rc2.Arm.Stream.longWith (.seq (cbcCall d) (.block restoreLr)) := rfl

theorem long_ok' (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : VG.Proof.Rc2.Arm.Stream.Keep s t) {tail : Prog isa} {Q : State → Prop}
    (hQ : ∀ t', VG.Proof.Rc2.Arm.Stream.Mid s t' → WP isa tail t' Q) :
    WP isa (VG.Proof.Rc2.Arm.Stream.longWith tail) t Q := by
  obtain ⟨_, spfit, hrd, hwr, ctxData, ctxOut, ctxScr, ctxArgs, dataOut, dataScr, outScr, outArgs,
    scrArgs, _, _, _, _, _, fitC, fitD, fitO, fitS, hp, hN⟩ := hs
  have r1v : s.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := VG.Proof.Rc2.Arm.Stream.ofNat_toNat32 _
  have r3v : s.gpr .r3 = BitVec.ofNat 32 (s.gpr .r3).toNat := VG.Proof.Rc2.Arm.Stream.ofNat_toNat32 _
  have olv : stackArg s 1 = BitVec.ofNat 32 (stackArg s 1).toNat := VG.Proof.Rc2.Arm.Stream.ofNat_toNat32 _
  have hNlt := (s.gpr .r3).isLt
  have hOLlt := (stackArg s 1).isLt
  have argR (i : Nat) (hi : i < 3) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 :=
    VG.Proof.Rc2.Arm.Stream.argIn (by rw [hrd]; simp) hi spfit
  generalize hC : s.gpr .r0 = C at *
  generalize hDt : s.gpr .r2 = Dt at *
  generalize hO : stackArg s 0 = O at *
  generalize hS : stackArg s 2 = S at *
  generalize hLR : s.gpr .lr = LR at *
  generalize hP : (s.gpr .r1).toNat = P at *
  generalize hNN : (s.gpr .r3).toNat = N at *
  generalize hOL : (stackArg s 1).toNat = OL at *
  have h8 : 8 ≤ OL := by omega
  have hPO : P ≤ OL := by omega
  have hON : OL - P ≤ N := by omega
  have hR : N - (OL - P) = (P + N) % 8 := by omega
  have hRlt : (P + N) % 8 < 8 := Nat.mod_lt _ (by decide)
  have rdwr {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have scrW (i n : Nat) (h : i + n ≤ 576) : InRegions s.wr (State.addr S + BitVec.ofNat 64 i) n := by
    rw [hwr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega)⟩
  have ctxIn : (⟨State.addr C, 144⟩ : Region) ∈ s.rd ++ s.wr := by rw [hwr]; simp
  have outIn : (⟨State.addr O, OL⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have dataIn : (⟨State.addr Dt, N⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ctxInW : (⟨State.addr C, 144⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  -- The regions the code writes before the call.
  have argsSep : ∀ r ∈ [(⟨State.addr O, OL⟩ : Region), ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩], (Region.mk (stackArgAddr s 0) 12).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact outArgs.symm
    · exact ctxArgs.symm.sub_right (Offset.sub_base _ (by decide))
    · exact scrArgs.symm.sub_right (Offset.sub_base _ (by decide))
  -- Saving `lr`, and `out`.
  rw [VG.Proof.Rc2.Arm.Stream.longWith, show toOut = [.ldrSp .r12 8, .str .lr .r12 512, .ldrSp .lr 0] from rfl]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [ht.sp]; rfl)
    (by rw [ht.rd, ht.wr]; exact argR 2 (by decide)) fun u₁ v₁ => ?_)
  have r12₁ : u₁.gpr .r12 = S := by rw [v₁.gpr, ht.mem]; exact hS
  refine wp_str (a := State.addr S + BitVec.ofNat 64 512) (by decide) (by rw [r12₁]; exact addr_add (by omega))
    (by rw [v₁.wr, ht.wr]; exact scrW 512 4 (by decide)) fun u₂ v₂ => ?_
  have m₂ : u₂.mem = s.mem.writeW (State.addr S + BitVec.ofNat 64 512) LR := by
    rw [v₂.mem, v₁.mem, ht.mem, v₁.other _ (by decide), ht.reg _ (by decide), hLR]
  have f₂ : Frame [⟨State.addr O, OL⟩, ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩] s.mem u₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  refine wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [v₂.sp, v₁.sp, ht.sp]; rfl)
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, ht.rd, ht.wr]; exact argR 0 (by decide)) fun u₃ v₃ => WP.block_nil ?_
  have lr₃ : u₃.gpr .lr = O := by rw [v₃.gpr, VG.Proof.Rc2.Arm.Stream.stackArg_frame f₂ spfit argsSep (by decide)]; exact hO
  have g₃ (r : Reg) (h₁ : r ≠ .r12) (h₂ : r ≠ .lr) : u₃.gpr r = s.gpr r := by
    rw [v₃.other _ h₂, v₂.gpr, v₁.other _ h₁, ht.reg _ h₁]
  have rd₃ : u₃.rd = s.rd := by rw [v₃.rd, v₂.rd, v₁.rd, ht.rd]
  have wr₃ : u₃.wr = s.wr := by rw [v₃.wr, v₂.wr, v₁.wr, ht.wr]
  have sp₃ : u₃.sp = s.sp := by rw [v₃.sp, v₂.sp, v₁.sp, ht.sp]
  rw [← v₃.mem] at m₂ f₂
  -- The pending bytes to `out`.
  refine WP.seq (WP.mono (VG.Proof.Rc2.Arm.Stream.copy_ok (s := u₃) (src := .r0) (dst := .lr) (cnt := .r1) (so := 136) (dd := 0)
    (L := P) (A := State.addr C + BitVec.ofNat 64 136) (B := State.addr O)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₃ _ (by decide) (by decide), r1v]) (by omega)
    (by rw [g₃ _ (by decide) (by decide), hC]; omega) (by rw [lr₃]; omega)
    (by rw [g₃ _ (by decide) (by decide), hC]) (by rw [lr₃]; exact VG.Proof.Rc2.Arm.Stream.add0 _)
    (fun _ => by rw [rd₃, wr₃]; exact VG.Proof.Rc2.Arm.Stream.cov1 ctxIn (by omega))
    (fun _ => by rw [wr₃, ← VG.Proof.Rc2.Arm.Stream.add0 (State.addr O)]; exact VG.Proof.Rc2.Arm.Stream.cov1 outIn (by omega))
    (fun _ => (ctxOut.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix hPO))) ?_)
  intro u₄ c₄
  have f₄ : Frame [⟨State.addr O, P⟩] u₃.mem u₄.mem := by
    rw [c₄.mem]; exact VG.Proof.Rc2.Arm.Stream.writeBytes_frame' _ _ _ (Proof.Rc2.bytesAt_length _ _ _)
  have o₄ : Spec.Rc2.bytesAt u₄.mem (State.addr O) P =
      Spec.Rc2.bytesAt s.mem (State.addr C + BitVec.ofNat 64 136) P := by
    rw [c₄.mem, VG.Proof.Rc2.Arm.Stream.bytesAt_writeBytes_self _ _ (Proof.Rc2.bytesAt_length _ _ _) (by omega), m₂,
      VG.Proof.Rc2.Arm.Stream.bytesAt_writeW _ (by omega) ((ctxScr.sub_left (Offset.sub_base _ (by omega))).sub_right
        (Offset.sub_base _ (by decide)))]
  have F₄ : Frame [⟨State.addr O, OL⟩, ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩] s.mem u₄.mem :=
    f₂.trans (f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hPO⟩)
  -- `r12 = p`, `r0 = ctx`, `r1 = out_len - p`, `r3 = len - r1`.
  rw [show middle = [.ldrSp .r12 0, .dp .sub .r12 .lr (.reg .r12), .dp .sub .r0 .r0 (.reg .r12), .ldrSp .r1 4,
    .dp .sub .r1 .r1 (.reg .r12), .dp .sub .r3 .r3 (.reg .r1)] from rfl]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [c₄.sp, sp₃]; rfl)
    (by rw [c₄.rd, c₄.wr, rd₃, wr₃]; exact argR 0 (by decide)) fun w₁ y₁ => ?_)
  refine wp_sub (op2_reg _ _) fun w₂ y₂ => wp_sub (op2_reg _ _) fun w₃ y₃ => ?_
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) (by rw [y₃.sp, y₂.sp, y₁.sp, c₄.sp, sp₃]; rfl)
    (by rw [y₃.rd, y₃.wr, y₂.rd, y₂.wr, y₁.rd, y₁.wr, c₄.rd, c₄.wr, rd₃, wr₃]; exact argR 1 (by decide))
    fun w₄ y₄ => wp_sub (op2_reg _ _) fun w₅ y₅ => wp_sub (op2_reg _ _) fun w₆ y₆ => WP.block_nil ?_
  have r12₁ : w₁.gpr .r12 = O := by rw [y₁.gpr, VG.Proof.Rc2.Arm.Stream.stackArg_frame F₄ spfit argsSep (by decide)]; exact hO
  have lr₄ : u₄.gpr .lr = O + BitVec.ofNat 32 P := by rw [c₄.dstv, lr₃]
  have r0₄ : u₄.gpr .r0 = C + BitVec.ofNat 32 P := by rw [c₄.srcv, g₃ _ (by decide) (by decide), hC]
  have r12₂ : w₂.gpr .r12 = BitVec.ofNat 32 P := by
    rw [y₂.gpr, y₁.other _ (by decide), r12₁, lr₄, Offset.add_sub_cancel_left]
  have r0₃ : w₃.gpr .r0 = C := by
    rw [y₃.gpr, y₂.other _ (by decide), y₁.other _ (by decide), r0₄, r12₂, BitVec.add_sub_cancel]
  have mem₃ : w₃.mem = u₄.mem := by rw [y₃.mem, y₂.mem, y₁.mem]
  have r1₄ : w₄.gpr .r1 = BitVec.ofNat 32 OL := by
    rw [y₄.gpr, mem₃, VG.Proof.Rc2.Arm.Stream.stackArg_frame F₄ spfit argsSep (by decide), olv]
  have r1₅ : w₅.gpr .r1 = BitVec.ofNat 32 (OL - P) := by
    rw [y₅.gpr, r1₄, y₄.other _ (by decide), y₃.other _ (by decide), r12₂, sub_ofNat hPO]
  have r3₆ : w₆.gpr .r3 = BitVec.ofNat 32 ((P + N) % 8) := by
    rw [y₆.gpr, y₅.other _ (by decide), y₄.other _ (by decide), y₃.other _ (by decide), y₂.other _ (by decide),
      y₁.other _ (by decide), c₄.keep _ (by decide) (by decide) (by decide) (by decide),
      g₃ _ (by decide) (by decide), r3v, r1₅, sub_ofNat hON, hR]
  have g₆ (r : Reg) (h₁ : r ≠ .r12) (h₂ : r ≠ .lr) (h₃ : r ≠ .r0) (h₄ : r ≠ .r1) (h₅ : r ≠ .r3) :
      w₆.gpr r = s.gpr r := by
    rw [y₆.other _ h₅, y₅.other _ h₄, y₄.other _ h₄, y₃.other _ h₃, y₂.other _ h₁, y₁.other _ h₁,
      c₄.keep _ h₃ h₂ h₄ h₁, g₃ _ h₁ h₂]
  have lr₆ : w₆.gpr .lr = O + BitVec.ofNat 32 P := by
    rw [y₆.other _ (by decide), y₅.other _ (by decide), y₄.other _ (by decide), y₃.other _ (by decide),
      y₂.other _ (by decide), y₁.other _ (by decide), lr₄]
  have mem₆ : w₆.mem = u₄.mem := by rw [y₆.mem, y₅.mem, y₄.mem, mem₃]
  have rd₆ : w₆.rd = s.rd := by rw [y₆.rd, y₅.rd, y₄.rd, y₃.rd, y₂.rd, y₁.rd, c₄.rd, rd₃]
  have wr₆ : w₆.wr = s.wr := by rw [y₆.wr, y₅.wr, y₄.wr, y₃.wr, y₂.wr, y₁.wr, c₄.wr, wr₃]
  have sp₆ : w₆.sp = s.sp := by rw [y₆.sp, y₅.sp, y₄.sp, y₃.sp, y₂.sp, y₁.sp, c₄.sp, sp₃]
  have r0₆ : w₆.gpr .r0 = C := by
    rw [y₆.other _ (by decide), y₅.other _ (by decide), y₄.other _ (by decide), r0₃]
  have r1₆ : w₆.gpr .r1 = BitVec.ofNat 32 (OL - P) := by rw [y₆.other _ (by decide), r1₅]
  have eOP : State.addr (O + BitVec.ofNat 32 P) = State.addr O + BitVec.ofNat 64 P := addr_add (by omega)
  -- The first `out_len - p` bytes of data to `out + p`.
  refine WP.seq (WP.mono (VG.Proof.Rc2.Arm.Stream.copy_ok (s := w₆) (src := .r2) (dst := .lr) (cnt := .r1) (so := 0) (dd := 0)
    (L := OL - P) (A := State.addr Dt) (B := State.addr O + BitVec.ofNat 64 P)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r1₆ (by omega)
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), hDt]; omega)
    (by rw [lr₆, VG.Proof.Rc2.Arm.Stream.toNat_add32 (by omega)]; omega)
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), hDt]; exact VG.Proof.Rc2.Arm.Stream.add0 _)
    (by rw [lr₆, eOP]; exact VG.Proof.Rc2.Arm.Stream.add0 _)
    (fun _ => by rw [rd₆, wr₆, ← VG.Proof.Rc2.Arm.Stream.add0 (State.addr Dt)]; exact VG.Proof.Rc2.Arm.Stream.cov1 dataIn (by omega))
    (fun _ => by rw [wr₆]; exact VG.Proof.Rc2.Arm.Stream.cov1 outIn (by omega))
    (fun _ => (dataOut.sub_left (Region.sub_prefix hON)).sub_right (Offset.sub_base _ (by omega)))) ?_)
  intro u₅ c₅
  have c5m : u₅.mem = VG.WriteBytes.writeBytes u₄.mem (State.addr O + BitVec.ofNat 64 P)
      (Spec.Rc2.bytesAt u₄.mem (State.addr Dt) (OL - P)) := by rw [← mem₆]; exact c₅.mem
  have f₅ : Frame [⟨State.addr O + BitVec.ofNat 64 P, OL - P⟩] u₄.mem u₅.mem := by
    rw [c5m]; exact VG.Proof.Rc2.Arm.Stream.writeBytes_frame' _ _ _ (Proof.Rc2.bytesAt_length _ _ _)
  have o₅ : Spec.Rc2.bytesAt u₅.mem (State.addr O + BitVec.ofNat 64 P) (OL - P) =
      Spec.Rc2.bytesAt s.mem (State.addr Dt) (OL - P) := by
    rw [c5m, VG.Proof.Rc2.Arm.Stream.bytesAt_writeBytes_self _ _ (Proof.Rc2.bytesAt_length _ _ _) (by omega),
      Proof.Rc2.bytesAt_frame F₄ _ _ (by omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dataOut.sub_left (Region.sub_prefix hON)
        · exact ctxData.symm.sub_left (Region.sub_prefix hON) |>.sub_right (Offset.sub_base _ (by decide))
        · exact dataScr.sub_left (Region.sub_prefix hON) |>.sub_right (Offset.sub_base _ (by decide)))]
  have F₅ : Frame [⟨State.addr O, OL⟩, ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩] s.mem u₅.mem :=
    F₄.trans (f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega)⟩)
  -- The rest to `ctx + 136`.
  rw [show toPending = [.mov .lr (.reg .r0)] from rfl]
  refine WP.seq (wp_mov (op2_reg _ _) fun u₆ v₆ => WP.block_nil ?_)
  have r2₆ : u₆.gpr .r2 = Dt + BitVec.ofNat 32 (OL - P) := by
    rw [v₆.other _ (by decide), c₅.srcv, g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), hDt]
  have r0₅ : u₅.gpr .r0 = C := by rw [c₅.keep _ (by decide) (by decide) (by decide) (by decide), r0₆]
  have lr₆' : u₆.gpr .lr = C := by rw [v₆.gpr, r0₅]
  have r3₆' : u₆.gpr .r3 = BitVec.ofNat 32 ((P + N) % 8) := by
    rw [v₆.other _ (by decide), c₅.keep _ (by decide) (by decide) (by decide) (by decide), r3₆]
  -- The data after the first `out_len - p` bytes, at an address that wraps only if nothing is left.
  have eA (hR0 : 0 < (P + N) % 8) :
      State.addr (Dt + BitVec.ofNat 32 (OL - P)) = State.addr Dt + BitVec.ofNat 64 (OL - P) :=
    addr_add (by omega)
  have bA (m : Mem) : Spec.Rc2.bytesAt m (State.addr (Dt + BitVec.ofNat 32 (OL - P))) ((P + N) % 8) =
      Spec.Rc2.bytesAt m (State.addr Dt + BitVec.ofNat 64 (OL - P)) ((P + N) % 8) := by
    rcases Nat.eq_zero_or_pos ((P + N) % 8) with h0 | h0
    · rw [h0]; rfl
    · rw [eA h0]
  have dSub : Region.Sub ⟨State.addr Dt + BitVec.ofNat 64 (OL - P), (P + N) % 8⟩ ⟨State.addr Dt, N⟩ :=
    Offset.sub_base _ (by omega)
  have pSub : Region.Sub ⟨State.addr C + BitVec.ofNat 64 136, (P + N) % 8⟩ ⟨State.addr C, 144⟩ :=
    Offset.sub_base _ (by omega)
  refine WP.seq (WP.mono (VG.Proof.Rc2.Arm.Stream.copy_ok (s := u₆) (src := .r2) (dst := .lr) (cnt := .r3) (so := 0) (dd := 136)
    (L := (P + N) % 8) (A := State.addr (Dt + BitVec.ofNat 32 (OL - P))) (B := State.addr C + BitVec.ofNat 64 136)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r3₆' (by omega)
    (by
      rw [r2₆]
      rcases Nat.eq_zero_or_pos ((P + N) % 8) with h0 | h0
      · rw [h0]; have := (Dt + BitVec.ofNat 32 (OL - P)).isLt; omega
      · rw [VG.Proof.Rc2.Arm.Stream.toNat_add32 (by omega)]; omega)
    (by rw [lr₆']; omega) (by rw [r2₆]; exact VG.Proof.Rc2.Arm.Stream.add0 _) (by rw [lr₆'])
    (fun h0 => by
      rw [v₆.rd, v₆.wr, c₅.rd, c₅.wr, rd₆, wr₆, eA h0]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, dataIn, OL - P, rfl, by simp only; omega⟩)
    (fun _ => by rw [v₆.wr, c₅.wr, wr₆]; exact VG.Proof.Rc2.Arm.Stream.cov1 ctxInW (by omega))
    (fun h0 => by rw [eA h0]; exact (ctxData.symm.sub_left dSub).sub_right pSub)) ?_)
  intro u₇ c₇
  have c7m : u₇.mem = VG.WriteBytes.writeBytes u₅.mem (State.addr C + BitVec.ofNat 64 136)
      (Spec.Rc2.bytesAt u₅.mem (State.addr (Dt + BitVec.ofNat 32 (OL - P))) ((P + N) % 8)) := by
    rw [← v₆.mem]; exact c₇.mem
  have f₇ : Frame [⟨State.addr C + BitVec.ofNat 64 136, (P + N) % 8⟩] u₅.mem u₇.mem := by
    rw [c7m]; exact VG.Proof.Rc2.Arm.Stream.writeBytes_frame' _ _ _ (Proof.Rc2.bytesAt_length _ _ _)
  have F₇ : Frame [⟨State.addr O, OL⟩, ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩] s.mem u₇.mem :=
    F₅.trans (f₇.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega)⟩)
  have p₇ : Spec.Rc2.bytesAt u₇.mem (State.addr C + BitVec.ofNat 64 136) ((P + N) % 8) =
      Spec.Rc2.bytesAt s.mem (State.addr Dt + BitVec.ofNat 64 (OL - P)) ((P + N) % 8) := by
    rw [c7m, VG.Proof.Rc2.Arm.Stream.bytesAt_writeBytes_self _ _ (Proof.Rc2.bytesAt_length _ _ _) (by omega), bA,
      Proof.Rc2.bytesAt_frame F₅ _ _ (by omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dataOut.sub_left dSub
        · exact (ctxData.symm.sub_left dSub).sub_right (Offset.sub_base _ (by decide))
        · exact (dataScr.sub_left dSub).sub_right (Offset.sub_base _ (by decide)))]
  have r0₇ : u₇.gpr .r0 = C := by
    rw [c₇.keep _ (by decide) (by decide) (by decide) (by decide), v₆.other _ (by decide), r0₅]
  have rd₇ : u₇.rd = s.rd := by rw [c₇.rd, v₆.rd, c₅.rd, rd₆]
  have wr₇ : u₇.wr = s.wr := by rw [c₇.wr, v₆.wr, c₅.wr, wr₆]
  have sp₇ : u₇.sp = s.sp := by rw [c₇.sp, v₆.sp, c₅.sp, sp₆]
  have g₇ (r : Reg) (hr : r ∈ preserved) (hl : r ≠ .lr) : u₇.gpr r = s.gpr r := by
    obtain ⟨h0, h1, h2, h3, h12⟩ := VG.Proof.Rc2.Arm.Stream.preserved_ne hr hl
    rw [c₇.keep _ h2 hl h3 h12, v₆.other _ hl, c₅.keep _ h2 hl h1 h12, g₆ _ h12 hl h0 h1 h3]
  -- The arguments of the CBC function.
  rw [show cbcArgs = [.dp .add .r1 .r0 (.imm 128), .ldrSp .r2 0, .ldrSp .r3 4,
    .mov .r3 (.shifted .r3 .lsr 3), .ldrSp .r12 8] from rfl]
  refine WP.seq (wp_add (op2_imm (by decide)) fun x₁ z₁ => ?_)
  refine wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [z₁.sp, sp₇]; rfl)
    (by rw [z₁.rd, z₁.wr, rd₇, wr₇]; exact argR 0 (by decide)) fun x₂ z₂ => ?_
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) (by rw [z₂.sp, z₁.sp, sp₇]; rfl)
    (by rw [z₂.rd, z₂.wr, z₁.rd, z₁.wr, rd₇, wr₇]; exact argR 1 (by decide)) fun x₃ z₃ => ?_
  refine wp_mov (op2_lsr (by decide)) fun x₄ z₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [z₄.sp, z₃.sp, z₂.sp, z₁.sp, sp₇]; rfl)
    (by rw [z₄.rd, z₄.wr, z₃.rd, z₃.wr, z₂.rd, z₂.wr, z₁.rd, z₁.wr, rd₇, wr₇]; exact argR 2 (by decide))
    fun x₅ z₅ => WP.block_nil ?_
  have memx : x₅.mem = u₇.mem := by rw [z₅.mem, z₄.mem, z₃.mem, z₂.mem, z₁.mem]
  have mem₄ : x₄.mem = u₇.mem := by rw [z₄.mem, z₃.mem, z₂.mem, z₁.mem]
  have mem₂ : x₂.mem = u₇.mem := by rw [z₂.mem, z₁.mem]
  have mem₁ : x₁.mem = u₇.mem := z₁.mem
  apply hQ x₅
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [z₅.other _ (by decide), z₄.other _ (by decide), z₃.other _ (by decide), z₂.other _ (by decide),
      z₁.other _ (by decide), r0₇, hC]
  · rw [z₅.other _ (by decide), z₄.other _ (by decide), z₃.other _ (by decide), z₂.other _ (by decide),
      z₁.gpr, r0₇, hC]
  · rw [z₅.other _ (by decide), z₄.other _ (by decide), z₃.other _ (by decide), z₂.gpr, mem₁,
      VG.Proof.Rc2.Arm.Stream.stackArg_frame F₇ spfit argsSep (by decide), hO]
  · rw [z₅.other _ (by decide), z₄.gpr, z₃.gpr, mem₂, VG.Proof.Rc2.Arm.Stream.stackArg_frame F₇ spfit argsSep (by decide), olv,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hOLlt, ofNat_shr hOLlt]
  · rw [z₅.gpr, mem₄, VG.Proof.Rc2.Arm.Stream.stackArg_frame F₇ spfit argsSep (by decide), hS]
  · intro r hr hl
    obtain ⟨_, h1, h2, h3, h12⟩ := VG.Proof.Rc2.Arm.Stream.preserved_ne hr hl
    rw [z₅.other _ h12, z₄.other _ h3, z₃.other _ h3, z₂.other _ h2, z₁.other _ h1, g₇ r hr hl]
  · rw [z₅.sp, z₄.sp, z₃.sp, z₂.sp, z₁.sp, sp₇]
  · rw [z₅.rd, z₄.rd, z₃.rd, z₂.rd, z₁.rd, rd₇]
  · rw [z₅.wr, z₄.wr, z₃.wr, z₂.wr, z₁.wr, wr₇]
  · rw [memx, hO, hOL, hC, hS]; exact F₇
  · -- The saved `lr`.
    have a4 : Region.Sub ⟨State.addr S + BitVec.ofNat 64 512, 4⟩ ⟨State.addr S, 576⟩ := Offset.sub_base _ (by decide)
    rw [memx, hS, hLR,
      f₇.readW (r := ⟨State.addr S + BitVec.ofNat 64 512, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (ctxScr.symm.sub_left a4).sub_right pSub) (by decide),
      f₅.readW (r := ⟨State.addr S + BitVec.ofNat 64 512, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (outScr.symm.sub_left a4).sub_right (Offset.sub_base _ (by omega))) (by decide),
      f₄.readW (r := ⟨State.addr S + BitVec.ofNat 64 512, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (outScr.symm.sub_left a4).sub_right (Region.sub_prefix hPO)) (by decide),
      m₂, Mem.readW_writeW_self32]
  · -- `out`: the pending bytes, then the data.
    rw [memx, hO, hOL, hC, hP, hDt, show OL = P + (OL - P) by omega, Proof.Rc2.bytesAt_add,
      Nat.add_sub_cancel_left]
    have outSub : ∀ r ∈ [(⟨State.addr C + BitVec.ofNat 64 136, (P + N) % 8⟩ : Region)],
        (Region.mk (State.addr O) OL).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ctxOut.symm.sub_right pSub
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rw [Proof.Rc2.bytesAt_frame f₇ _ _ (by omega) (fun r hr => (outSub r hr).sub_left (Region.sub_prefix hPO)),
        Proof.Rc2.bytesAt_frame f₅ _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)), o₄]
    · rw [Proof.Rc2.bytesAt_frame f₇ _ _ (by omega)
          (fun r hr => (outSub r hr).sub_left (Offset.sub_base _ (by omega))), o₅]
  · rw [memx, hC, hP, hNN, hDt, hOL]; exact p₇

theorem long_ok (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : VG.Proof.Rc2.Arm.Stream.Keep s t) {Q : State → Prop}
    (hQ : ∀ t', VG.Proof.Rc2.Arm.Stream.Mid s t' → WP isa (.seq (cbcCall d) (.block restoreLr)) t' Q) :
    WP isa (long d) t Q := by
  rw [VG.Proof.Rc2.Arm.Stream.long_eq]; exact VG.Proof.Rc2.Arm.Stream.long_ok' d s hs hnz t ht hQ

end VG.Proof.Rc2.Arm.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Stream.Verified`. -/
section

section

/-! # Streaming RC2-CBC on ARMv7: the update functions

Without a complete block, the data is appended to the pending bytes
(`short_ok`); otherwise, after the copies (`long_ok`), the CBC function runs
on `out` and `lr` is restored (`call_ok`). -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.WriteBytes VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_add wp_ldr wp_ldrSp wp_cmp eval_eq cmp0)

/-- The postcondition of `update`: the callee-saved registers and the contract's. -/
abbrev UpdPost (d : Spec.Rc2.Direction) (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (VG.Proof.Rc2.Arm.Stream.updateContract d).post s s'

/-- With `out_len = 0` (so `pending_len + len < 8`). -/
theorem short_ok (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s)
    (hz : (stackArg s 1).toNat = 0) (t : State) (ht : VG.Proof.Rc2.Arm.Stream.Keep s t) :
    WP isa short t (VG.Proof.Rc2.Arm.Stream.UpdPost d s) := by
  obtain ⟨_, _, hrd, hwr, ctxData, _, _, _, _, _, _, _, _, _, _, _, _, _, fitC, fitD, _, _, hp, hN⟩ := hs
  have hshort : (s.gpr .r1).toNat + (s.gpr .r3).toNat < 8 := by omega
  have hNlt := (s.gpr .r3).isLt
  rw [short]
  refine WP.seq (wp_add (op2_reg _ _) fun t₁ u₁ => WP.block_nil ?_)
  have g₁ (r : Reg) (h₁ : r ≠ .r12) (h₂ : r ≠ .r1) : t₁.gpr r = s.gpr r := by
    rw [u₁.other _ h₂, ht.reg _ h₁]
  have r1₁ : t₁.gpr .r1 = s.gpr .r0 + BitVec.ofNat 32 (s.gpr .r1).toNat := by
    rw [u₁.gpr, ht.reg _ (by decide), ht.reg _ (by decide), ← VG.Proof.Rc2.Arm.Stream.ofNat_toNat32]
  have hD : State.addr (t₁.gpr .r1) + BitVec.ofNat 64 136 =
      State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat) := by
    rw [r1₁, addr_add (by omega), Offset.add_add, Nat.add_comm]
  have dstSub : Region.Sub ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat), (s.gpr .r3).toNat⟩
      ⟨State.addr (s.gpr .r0), 144⟩ := Offset.sub_base _ (by omega)
  apply WP.mono (VG.Proof.Rc2.Arm.Stream.copy_ok (s := t₁) (src := .r2) (dst := .r1) (cnt := .r3) (so := 0) (dd := 136)
    (L := (s.gpr .r3).toNat) (A := State.addr (s.gpr .r2))
    (B := State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₁ _ (by decide) (by decide)]; exact VG.Proof.Rc2.Arm.Stream.ofNat_toNat32 _) hNlt
    (by rw [g₁ _ (by decide) (by decide)]; omega)
    (by rw [r1₁, VG.Proof.Rc2.Arm.Stream.toNat_add32 (by omega)]; omega)
    (by rw [g₁ _ (by decide) (by decide)]; exact VG.Proof.Rc2.Arm.Stream.add0 _) hD
    (fun _ => by
      rw [u₁.rd, u₁.wr, ht.rd, ht.wr, ← VG.Proof.Rc2.Arm.Stream.add0 (State.addr (s.gpr .r2))]
      exact VG.Proof.Rc2.Arm.Stream.cov1 (len := (s.gpr .r3).toNat) (by rw [hrd]; simp) (by omega))
    (fun _ => by rw [u₁.wr, ht.wr]; exact VG.Proof.Rc2.Arm.Stream.cov1 (len := 144) (by rw [hwr]; simp) (by omega))
    (fun _ => ctxData.symm.sub_right dstSub))
  intro s' c'
  have m' : s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat))
      (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) := by
    rw [← ht.mem, ← u₁.mem]; exact c'.mem
  have frame : Frame [⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat), (s.gpr .r3).toNat⟩]
      s.mem s'.mem := by
    rw [m']; exact VG.Proof.Rc2.Arm.Stream.writeBytes_frame' _ _ _ (Proof.Rc2.bytesAt_length _ _ _)
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hl : r = .lr
    · subst hl; rw [c'.keep _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
    · obtain ⟨_, h1, h2, h3, h12⟩ := VG.Proof.Rc2.Arm.Stream.preserved_ne hr hl
      rw [c'.keep _ h2 h1 h3 h12, g₁ _ h12 h1]
  · show Spec.Rc2.contextAt s'.mem _ d _ = _ ∧ _
    rw [hN]
    refine update_post_short hshort ?_ ?_ ?_
    · exact Proof.Rc2.scheduleAt_frame frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega))
    · rw [VG.Proof.Rc2.Arm.Stream.e128]
      exact Proof.Rc2.blockAt_frame frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega))
    · rw [VG.Proof.Rc2.Arm.Stream.e136, Proof.Rc2.bytesAt_add, Offset.add_add,
        Proof.Rc2.bytesAt_frame frame _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)),
        m', VG.Proof.Rc2.Arm.Stream.bytesAt_writeBytes_self _ _ (Proof.Rc2.bytesAt_length _ _ _) (by omega)]

/-- Regions the call leaves alone. -/
theorem callSep {C O S : BitVec 32} {OL : Nat} {sp : Addr} (R : Region)
    (hiv : R.Disjoint ⟨State.addr C + BitVec.ofNat 64 128, 8⟩)
    (hout : R.Disjoint ⟨State.addr O, OL⟩) (hbuf : R.Disjoint ⟨State.addr S, 512⟩)
    (hst : R.Disjoint ⟨sp, 8⟩) :
    ∀ r ∈ [(⟨State.addr C + BitVec.ofNat 64 128, 8⟩ : Region), ⟨State.addr O, OL⟩, ⟨State.addr S, 512⟩,
      ⟨sp, 8⟩], R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hiv
  · exact hout
  · exact hbuf
  · exact hst

/-- Regions the copies leave alone. -/
theorem midSep {C O S : BitVec 32} {OL : Nat} (R : Region) (hout : R.Disjoint ⟨State.addr O, OL⟩)
    (hpend : R.Disjoint ⟨State.addr C + BitVec.ofNat 64 136, 8⟩)
    (hlr : R.Disjoint ⟨State.addr S + BitVec.ofNat 64 512, 4⟩) :
    ∀ r ∈ [(⟨State.addr O, OL⟩ : Region), ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩], R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hout
  · exact hpend
  · exact hlr

theorem ivSub (C : BitVec 32) : Region.Sub ⟨State.addr C + BitVec.ofNat 64 128, 8⟩ ⟨State.addr C, 144⟩ :=
  Offset.sub_base _ (by decide)
theorem keySub (C : BitVec 32) : Region.Sub ⟨State.addr C, 128⟩ ⟨State.addr C, 144⟩ :=
  Region.sub_prefix (by decide)
theorem pendSub (C : BitVec 32) : Region.Sub ⟨State.addr C + BitVec.ofNat 64 136, 8⟩ ⟨State.addr C, 144⟩ :=
  Offset.sub_base _ (by decide)
theorem bufSub (S : BitVec 32) : Region.Sub ⟨State.addr S, 512⟩ ⟨State.addr S, 576⟩ :=
  Region.sub_prefix (by decide)
theorem lrSub (S : BitVec 32) : Region.Sub ⟨State.addr S + BitVec.ofNat 64 512, 4⟩ ⟨State.addr S, 576⟩ :=
  Offset.sub_base _ (by decide)

theorem eN {OL : Nat} (h8 : OL % 8 = 0) (hOL : OL < 2 ^ 32) : 8 * (BitVec.ofNat 32 (OL / 8)).toNat = OL := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem eI {C : BitVec 32} (h : C.toNat + 144 ≤ 2 ^ 32) :
    State.addr (C + 128) = State.addr C + BitVec.ofNat 64 128 := addr_add (k := 128) (by omega)

/-- The arguments of the CBC function. -/
theorem mid_pre (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s)
    (t : State) (ht : VG.Proof.Rc2.Arm.Stream.Mid s t) :
    VG.Proof.Rc2.Arm.Stream.CbcPre t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0) (BitVec.ofNat 32 ((stackArg s 1).toNat / 8))
      (stackArg s 2) := by
  obtain ⟨sp8, _, _, hwr, _, ctxOut, ctxScr, _, _, _, outScr, _, _, bCtx, _, bOut, bScr, _, fitC, _, fitO,
    fitS, hp, hN⟩ := hs
  have eN' := VG.Proof.Rc2.Arm.Stream.eN (OL := (stackArg s 1).toNat) (by omega) (stackArg s 1).isLt
  have eI' := VG.Proof.Rc2.Arm.Stream.eI fitC
  have eb : (⟨State.addr t.sp - 8, 8⟩ : Region) = ⟨State.addr s.sp - 8, 8⟩ := by rw [ht.sp]
  refine ⟨ht.r0, ht.r1, ht.r2, ht.r3, ht.r12, by rw [ht.sp]; exact sp8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by omega, by show (s.gpr .r0 + BitVec.ofNat 32 128).toNat + 8 ≤ _; rw [VG.Proof.Rc2.Arm.Stream.toNat_add32 (by omega)]; omega,
    by rw [eN']; exact fitO, by omega, ?_, ?_⟩
  · rw [eI']; exact Offset.base_disjoint _ (by decide) (by decide)
  · rw [eN']; exact ctxOut.sub_left (VG.Proof.Rc2.Arm.Stream.keySub _)
  · exact (ctxScr.sub_left (VG.Proof.Rc2.Arm.Stream.keySub _)).sub_right (VG.Proof.Rc2.Arm.Stream.bufSub _)
  · rw [eI', eN']; exact ctxOut.sub_left (VG.Proof.Rc2.Arm.Stream.ivSub _)
  · rw [eI']; exact (ctxScr.sub_left (VG.Proof.Rc2.Arm.Stream.ivSub _)).sub_right (VG.Proof.Rc2.Arm.Stream.bufSub _)
  · rw [eN']; exact outScr.sub_right (VG.Proof.Rc2.Arm.Stream.bufSub _)
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb]; exact bCtx.sub_right (VG.Proof.Rc2.Arm.Stream.keySub _)
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb, eI']; exact bCtx.sub_right (VG.Proof.Rc2.Arm.Stream.ivSub _)
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb, eN']; exact bOut
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb]; exact bScr.sub_right (VG.Proof.Rc2.Arm.Stream.bufSub _)
  · rw [ht.rd, ht.wr, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (s.gpr .r0), 144⟩, by simp, 0, (VG.Proof.Rc2.Arm.Stream.add0 _).symm, by simp⟩
  · rw [ht.wr, hwr, eI', eN']
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨State.addr (s.gpr .r0), 144⟩, by simp, 128, rfl, by simp⟩
      · exact ⟨⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩, by simp, 0, (VG.Proof.Rc2.Arm.Stream.add0 _).symm, by simp⟩
      · exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, 0, (VG.Proof.Rc2.Arm.Stream.add0 _).symm, by simp⟩

/-- The update's postcondition, from the memory the call leaves. -/
theorem post_ok (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : VG.Proof.Rc2.Arm.Stream.Mid s t) (u : State)
    (hu : VG.Proof.Rc2.Arm.Stream.CbcPost d t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0)
      (BitVec.ofNat 32 ((stackArg s 1).toNat / 8)) (stackArg s 2) u) :
    (VG.Proof.Rc2.Arm.Stream.updateContract d).post s u := by
  obtain ⟨_, _, _, _, _, ctxOut, ctxScr, _, _, _, _, _, _, bCtx, _, _, _, _, fitC, _, _, _, hp, hN⟩ := hs
  have frame₁ := ht.frame
  have out₁ := ht.out
  have pend₁ := ht.pend
  obtain ⟨_, _, _, _, frame₂, data₂, iv₂⟩ := hu
  have hOLlt := (stackArg s 1).isLt
  have eb : VG.Proof.Rc2.Arm.Stream.below t = ⟨State.addr s.sp - 8, 8⟩ := by simp only [VG.Proof.Rc2.Arm.Stream.below, ht.sp]
  rw [VG.Proof.Rc2.Arm.Stream.eI fitC, VG.Proof.Rc2.Arm.Stream.eN (by omega) hOLlt, eb] at frame₂
  rw [VG.Proof.Rc2.Arm.Stream.eI fitC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (stackArg s 1).toNat / 8 < 2 ^ 32 by omega)] at data₂ iv₂
  show Spec.Rc2.contextAt u.mem _ d _ = _ ∧ _
  rw [hN] at out₁ pend₁ data₂ iv₂ frame₁ frame₂ ctxOut ⊢
  rw [Nat.mul_div_cancel _ (by decide : 0 < 8)] at data₂ iv₂
  have keyMid := Proof.Rc2.scheduleAt_frame frame₁ _ (VG.Proof.Rc2.Arm.Stream.midSep _ (ctxOut.sub_left (VG.Proof.Rc2.Arm.Stream.keySub _))
    (Offset.base_disjoint _ (by decide) (by decide)) ((ctxScr.sub_left (VG.Proof.Rc2.Arm.Stream.keySub _)).sub_right (VG.Proof.Rc2.Arm.Stream.lrSub _)))
  refine update_post_long hp (by omega) out₁ keyMid ?_ ?_ ?_ data₂ iv₂
  · rw [VG.Proof.Rc2.Arm.Stream.e128]
    exact Proof.Rc2.blockAt_frame frame₁ _ (VG.Proof.Rc2.Arm.Stream.midSep _ (ctxOut.sub_left (VG.Proof.Rc2.Arm.Stream.ivSub _))
      (Offset.disjoint _ (by decide) (by decide) (by decide)) ((ctxScr.sub_left (VG.Proof.Rc2.Arm.Stream.ivSub _)).sub_right (VG.Proof.Rc2.Arm.Stream.lrSub _)))
  · rw [VG.Proof.Rc2.Arm.Stream.e136, Proof.Rc2.bytesAt_frame frame₂ _ _ (by omega) (VG.Proof.Rc2.Arm.Stream.callSep _
        (Offset.disjoint _ (by omega) (by omega) (by decide)) (ctxOut.sub_left (Offset.sub_base _ (by omega)))
        ((ctxScr.sub_left (Offset.sub_base _ (by omega))).sub_right (VG.Proof.Rc2.Arm.Stream.bufSub _))
        (bCtx.symm.sub_left (Offset.sub_base _ (by omega)))), pend₁]
  · exact Proof.Rc2.scheduleAt_frame frame₂ _ (VG.Proof.Rc2.Arm.Stream.callSep _ (Offset.base_disjoint _ (by decide) (by decide))
      (ctxOut.sub_left (VG.Proof.Rc2.Arm.Stream.keySub _)) ((ctxScr.sub_left (VG.Proof.Rc2.Arm.Stream.keySub _)).sub_right (VG.Proof.Rc2.Arm.Stream.bufSub _))
      (bCtx.symm.sub_left (VG.Proof.Rc2.Arm.Stream.keySub _)))

/-- `lr` back from `scratch + 512`, after the call. -/
theorem restore_ok (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : VG.Proof.Rc2.Arm.Stream.Mid s t) (u : State)
    (hu : VG.Proof.Rc2.Arm.Stream.CbcPost d t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0)
      (BitVec.ofNat 32 ((stackArg s 1).toNat / 8)) (stackArg s 2) u) :
    WP isa (.block restoreLr) u (VG.Proof.Rc2.Arm.Stream.UpdPost d s) := by
  have hpost := VG.Proof.Rc2.Arm.Stream.post_ok d s hs hnz t ht u hu
  obtain ⟨_, spfit, hrd, hwr, _, ctxOut, ctxScr, ctxArgs, _, _, outScr, outArgs, scrArgs, bCtx, _, bOut,
    bScr, bArgs, fitC, _, _, fitS, hp, hN⟩ := hs
  have frame₁ := ht.frame
  have lr₁ := ht.lr
  obtain ⟨rd₂, wr₂, sp₂, saved₂, frame₂, _, _⟩ := hu
  have hOLlt := (stackArg s 1).isLt
  have eb : VG.Proof.Rc2.Arm.Stream.below t = ⟨State.addr s.sp - 8, 8⟩ := by simp only [VG.Proof.Rc2.Arm.Stream.below, ht.sp]
  rw [VG.Proof.Rc2.Arm.Stream.eI fitC, VG.Proof.Rc2.Arm.Stream.eN (by omega) hOLlt, eb] at frame₂
  have argR (i : Nat) (hi : i < 3) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 :=
    VG.Proof.Rc2.Arm.Stream.argIn (by rw [hrd]; simp) hi spfit
  rw [show restoreLr = [.ldrSp .r12 8, .ldr .lr .r12 512] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [sp₂, ht.sp]; rfl)
    (by rw [rd₂, wr₂, ht.rd, ht.wr]; exact argR 2 (by decide)) fun u₁ v₁ => ?_
  have hc2 : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s 2) (32 / 8) := by
    rw [VG.Proof.Rc2.Arm.Stream.stackArgAddr_eq s (i := 2) (by decide) spfit]; exact Offset.contains_base _ (by decide) (by decide)
  have argsS : u.mem.readW (stackArgAddr s 2) 32 = stackArg s 2 := by
    rw [frame₂.readW hc2 (VG.Proof.Rc2.Arm.Stream.callSep _ (ctxArgs.symm.sub_right (VG.Proof.Rc2.Arm.Stream.ivSub _)) outArgs.symm
        (scrArgs.symm.sub_right (VG.Proof.Rc2.Arm.Stream.bufSub _)) bArgs.symm) (by decide),
      VG.Proof.Rc2.Arm.Stream.stackArg_frame frame₁ spfit (VG.Proof.Rc2.Arm.Stream.midSep _ outArgs.symm (ctxArgs.symm.sub_right (VG.Proof.Rc2.Arm.Stream.pendSub _))
        (scrArgs.symm.sub_right (VG.Proof.Rc2.Arm.Stream.lrSub _))) (by decide)]
  refine wp_ldr (a := State.addr (stackArg s 2) + BitVec.ofNat 64 512) (by decide)
    (by rw [v₁.gpr, argsS]; exact addr_add (by omega))
    (by rw [v₁.rd, v₁.wr, rd₂, wr₂, ht.rd, ht.wr, hwr]
        exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₂ v₂ => WP.block_nil ?_
  have lr₂ : u₂.gpr .lr = s.gpr .lr := by
    rw [v₂.gpr, v₁.mem, frame₂.readW (r := ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩)
      (Region.contains_self _ _)
      (VG.Proof.Rc2.Arm.Stream.callSep _ ((ctxScr.sub_left (VG.Proof.Rc2.Arm.Stream.ivSub _)).sub_right (VG.Proof.Rc2.Arm.Stream.lrSub _)).symm (outScr.sub_right (VG.Proof.Rc2.Arm.Stream.lrSub _)).symm
        (Offset.disjoint_base _ (by decide) (by decide)) (bScr.sub_right (VG.Proof.Rc2.Arm.Stream.lrSub _)).symm) (by decide), lr₁]
  have mem₂ : u₂.mem = u.mem := by rw [v₂.mem, v₁.mem]
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hl : r = .lr
    · subst hl; rw [lr₂]
    · obtain ⟨_, _, _, _, h12⟩ := VG.Proof.Rc2.Arm.Stream.preserved_ne hr hl
      rw [v₂.other _ hl, v₁.other _ h12, saved₂ r hr hl, ht.callee r hr hl]
  · show Spec.Rc2.contextAt u₂.mem _ d _ = _ ∧ Spec.Rc2.bytesAt u₂.mem _ _ = _
    rw [mem₂]; exact hpost

/-- The call of the CBC function, `lr` restored, and the update's postcondition. -/
theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : VG.Proof.Rc2.Arm.Stream.Mid s t) :
    WP isa (.seq (cbcCall d) (.block restoreLr)) t (VG.Proof.Rc2.Arm.Stream.UpdPost d s) :=
  WP.seq (WP.mono (VG.Proof.Rc2.Arm.Stream.cbc_call (d := d) (VG.Proof.Rc2.Arm.Stream.mid_pre d s hs t ht)) fun u hu => VG.Proof.Rc2.Arm.Stream.restore_ok d s hs hnz t ht u hu)

/-- The stack arguments after the call are those on entry. -/
theorem args_after (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s)
    (t : State) (ht : VG.Proof.Rc2.Arm.Stream.Mid s t) (u : State)
    (hu : VG.Proof.Rc2.Arm.Stream.CbcPost d t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0)
      (BitVec.ofNat 32 ((stackArg s 1).toNat / 8)) (stackArg s 2) u) :
    ∀ i < 3, stackArg u i = stackArg s i := by
  obtain ⟨_, spfit, _, _, _, _, _, ctxArgs, _, _, _, outArgs, scrArgs, _, _, _, _, bArgs, fitC, _, _, _, hp,
    hN⟩ := hs
  have frame₂ := hu.frame
  have hOLlt := (stackArg s 1).isLt
  have eb : VG.Proof.Rc2.Arm.Stream.below t = ⟨State.addr s.sp - 8, 8⟩ := by simp only [VG.Proof.Rc2.Arm.Stream.below, ht.sp]
  rw [VG.Proof.Rc2.Arm.Stream.eI fitC, VG.Proof.Rc2.Arm.Stream.eN (by omega) hOLlt, eb] at frame₂
  intro i hi
  have hc : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s i) (32 / 8) := by
    rw [VG.Proof.Rc2.Arm.Stream.stackArgAddr_eq s hi spfit]; exact Offset.contains_base _ (by omega) (by omega)
  have ea : stackArgAddr u i = stackArgAddr s i := by unfold stackArgAddr; rw [hu.sp, ht.sp]
  rw [stackArg, ea, frame₂.readW hc (VG.Proof.Rc2.Arm.Stream.callSep _ (ctxArgs.symm.sub_right (VG.Proof.Rc2.Arm.Stream.ivSub _)) outArgs.symm
      (scrArgs.symm.sub_right (VG.Proof.Rc2.Arm.Stream.bufSub _)) bArgs.symm) (by decide),
    VG.Proof.Rc2.Arm.Stream.stackArg_frame ht.frame spfit (VG.Proof.Rc2.Arm.Stream.midSep _ outArgs.symm (ctxArgs.symm.sub_right (VG.Proof.Rc2.Arm.Stream.pendSub _))
      (scrArgs.symm.sub_right (VG.Proof.Rc2.Arm.Stream.lrSub _))) hi]

/-- The test of `out_len`. -/
theorem b0_wp (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s) :
    WP isa (.block [.ldrSp .r12 4, .cmp .r12 (.imm 0)]) s
      (fun t => VG.Proof.Rc2.Arm.Stream.Keep s t ∧ t.z = decide ((stackArg s 1).toNat = 0)) := by
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) rfl
    (VG.Proof.Rc2.Arm.Stream.argIn (by rw [hs.2.2.1]; simp) (by decide) hs.2.1) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ =>
      WP.block_nil ⟨⟨fun r hr => by rw [f₂.gpr, u₁.other _ hr], by rw [f₂.mem, u₁.mem],
        by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr], by rw [f₂.sp, u₁.sp]⟩, ?_⟩
  rw [z₂, u₁.gpr, VG.Proof.Rc2.Arm.Stream.ofNat_toNat32 (s.mem.readW (stackArgAddr s 1) 32), cmp0 (BitVec.isLt _)]; rfl

theorem update_wp (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s) :
    WP isa (update d) s (VG.Proof.Rc2.Arm.Stream.UpdPost d s) := by
  rw [update]
  refine WP.seq (WP.mono (VG.Proof.Rc2.Arm.Stream.b0_wp d s hs) fun t₂ ⟨ht, hz⟩ => ?_)
  refine WP.ite (decide ((stackArg s 1).toNat = 0)) (by rw [← hz]; rfl) (fun h => ?_) fun h => ?_
  · exact VG.Proof.Rc2.Arm.Stream.short_ok d s hs (of_decide_eq_true h) t₂ ht
  · exact VG.Proof.Rc2.Arm.Stream.long_ok d s hs (of_decide_eq_false h) t₂ ht fun t' ht' => VG.Proof.Rc2.Arm.Stream.call_ok d s hs (of_decide_eq_false h) t' ht'

theorem update_correct (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s) :
    ∃ t s', Exec isa (update d) s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Rc2.Arm.Stream.updateContract d).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.Arm.Stream.update_wp d s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

end VG.Proof.Rc2.Arm.Stream

end

section

section

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init`

The checks of the lengths (`checks_ok`), then, if they pass, the IV copied to
`ctx + 128` and `lr` saved (`args_ok`), the call of `vg_rc2_expand_key`
(`key_call`), and `lr` restored with 0 returned (`tail_ok`). -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_sub wp_cmp wp_ldr wp_str
  wp_ldrSp eval_ne sub_beq)

theorem range7 (x : BitVec 32) :
    ((x - 1) >>> 7 - 0 == 0) = decide (1 ≤ x.toNat ∧ x.toNat ≤ 128) := by
  rw [show ((x - 1) >>> 7 - 0 : BitVec 32) = (x - 1) >>> 7 from BitVec.sub_zero _]
  have e : ((x - 1) >>> 7).toNat = (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 128 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]; rfl
  have h := x.isLt
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, e, show (0 : BitVec 32).toNat = 0 from rfl]
  omega

theorem range10 (x : BitVec 32) :
    ((x - 1) >>> 10 - 0 == 0) = decide (1 ≤ x.toNat ∧ x.toNat ≤ 1024) := by
  rw [show ((x - 1) >>> 10 - 0 : BitVec 32) = (x - 1) >>> 10 from BitVec.sub_zero _]
  have e : ((x - 1) >>> 10).toNat = (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 1024 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]; rfl
  have h := x.isLt
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, e, show (0 : BitVec 32).toNat = 0 from rfl]
  omega

theorem eq8 (x : BitVec 32) : (x - 8 == 0) = decide (x.toNat = 8) := by
  rw [VG.Proof.Rc2.Arm.Stream.ofNat_toNat32 x, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, sub_beq x.isLt (by decide),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem setWidth_append (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt this]
  omega

theorem wp_mov_imm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (he : encodable v = true) (k : WP isa (.block is) (s.setReg d v) Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (by simp [exec, Op2.eval, he]) k

/-- The lengths are valid. -/
abbrev IValid (s : State) : Prop :=
  (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) ∧ (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) ∧
    (stackArg s 0).toNat = 8

/-- The error code for invalid lengths. -/
abbrev ICode (s : State) : Nat :=
  if ¬(1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) then 1
  else if ¬(1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) then 2 else 3

/-- What the checks leave. -/
structure CheckPost (s c : State) : Prop where
  keep : ∀ r, r ≠ .r0 → r ≠ .r12 → c.gpr r = s.gpr r
  mem : c.mem = s.mem
  rd : c.rd = s.rd
  wr : c.wr = s.wr
  sp : c.sp = s.sp
  z : c.z = decide (VG.Proof.Rc2.Arm.Stream.IValid s)
  ok : VG.Proof.Rc2.Arm.Stream.IValid s → c.gpr .r0 = s.gpr .r0
  err : ¬ VG.Proof.Rc2.Arm.Stream.IValid s → (c.gpr .r0).toNat = VG.Proof.Rc2.Arm.Stream.ICode s

theorem checks_ok (s : State) (hs : initContract.pre s) : WP isa checks s (VG.Proof.Rc2.Arm.Stream.CheckPost s) := by
  obtain ⟨_, spfit, hrd, _⟩ := hs
  rw [checks]
  refine WP.seq (wp_sub (op2_imm (by decide)) fun c₁ u₁ => wp_mov (op2_lsr (by decide)) fun c₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun c₃ f₃ z₃ => WP.block_nil ?_)
  have hk : c₃.z = decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) := by
    rw [z₃, u₂.gpr, u₁.gpr, VG.Proof.Rc2.Arm.Stream.range7]
  have g₃ (r : Reg) (h : r ≠ .r12) : c₃.gpr r = s.gpr r := by rw [f₃.gpr, u₂.other _ h, u₁.other _ h]
  have mem₃ : c₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  have rd₃ : c₃.rd = s.rd := by rw [f₃.rd, u₂.rd, u₁.rd]
  have wr₃ : c₃.wr = s.wr := by rw [f₃.wr, u₂.wr, u₁.wr]
  have sp₃ : c₃.sp = s.sp := by rw [f₃.sp, u₂.sp, u₁.sp]
  refine WP.ite (!decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128))
    (by show eval .ne c₃ = _; rw [eval_ne, hk]) (fun hb => VG.Proof.Rc2.Arm.Stream.wp_mov_imm (by decide) (WP.block_nil ?_)) fun hb => ?_
  · have hb : ¬(1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) := fun h => by simp [h] at hb
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₃ r h12], by rw [mem_setReg, mem₃],
      by rw [rd_setReg, rd₃], by rw [wr_setReg, wr₃], by rw [sp_setReg, sp₃], ?_, fun h => absurd h.1 hb,
      fun _ => ?_⟩
    · rw [z_setReg, hk]; simp only [VG.Proof.Rc2.Arm.Stream.IValid, hb, false_and, decide_false]
    · rw [gpr_setReg_self]; simp only [VG.Proof.Rc2.Arm.Stream.ICode, hb, not_false_eq_true, ite_true]; rfl
  have hb : 1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128 := by simpa using hb
  refine WP.seq (wp_sub (op2_imm (by decide)) fun c₄ u₄ => wp_mov (op2_lsr (by decide)) fun c₅ u₅ =>
    wp_cmp (op2_imm (by decide)) fun c₆ f₆ z₆ => WP.block_nil ?_)
  have he : c₆.z = decide (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) := by
    rw [z₆, u₅.gpr, u₄.gpr, g₃ _ (by decide), VG.Proof.Rc2.Arm.Stream.range10]
  have g₆ (r : Reg) (h : r ≠ .r12) : c₆.gpr r = s.gpr r := by rw [f₆.gpr, u₅.other _ h, u₄.other _ h, g₃ r h]
  have mem₆ : c₆.mem = s.mem := by rw [f₆.mem, u₅.mem, u₄.mem, mem₃]
  have rd₆ : c₆.rd = s.rd := by rw [f₆.rd, u₅.rd, u₄.rd, rd₃]
  have wr₆ : c₆.wr = s.wr := by rw [f₆.wr, u₅.wr, u₄.wr, wr₃]
  have sp₆ : c₆.sp = s.sp := by rw [f₆.sp, u₅.sp, u₄.sp, sp₃]
  refine WP.ite (!decide (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024))
    (by show eval .ne c₆ = _; rw [eval_ne, he]) (fun hb' => VG.Proof.Rc2.Arm.Stream.wp_mov_imm (by decide) (WP.block_nil ?_)) fun hb' => ?_
  · have hb' : ¬(1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) := fun h => by simp [h] at hb'
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₆ r h12], by rw [mem_setReg, mem₆],
      by rw [rd_setReg, rd₆], by rw [wr_setReg, wr₆], by rw [sp_setReg, sp₆], ?_, fun h => absurd h.2.1 hb',
      fun _ => ?_⟩
    · rw [z_setReg, he]; simp only [VG.Proof.Rc2.Arm.Stream.IValid, hb', false_and, and_false, decide_false]
    · rw [gpr_setReg_self]; simp only [VG.Proof.Rc2.Arm.Stream.ICode, hb, hb', not_false_eq_true, ite_true]
      rfl
  have hb' : 1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024 := by simpa using hb'
  rw [show checkIv = [.ldrSp .r12 0, .cmp .r12 (.imm 8)] from rfl]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [sp₆]; rfl)
    (by rw [rd₆, wr₆]; exact VG.Proof.Rc2.Arm.Stream.argIn (by rw [hrd]; simp) (by decide) spfit) fun c₇ u₇ =>
      wp_cmp (op2_imm (by decide)) fun c₈ f₈ z₈ => WP.block_nil ?_)
  have hi : c₈.z = decide ((stackArg s 0).toNat = 8) := by
    rw [z₈, u₇.gpr, mem₆, VG.Proof.Rc2.Arm.Stream.eq8]; rfl
  have g₈ (r : Reg) (h : r ≠ .r12) : c₈.gpr r = s.gpr r := by rw [f₈.gpr, u₇.other _ h, g₆ r h]
  have mem₈ : c₈.mem = s.mem := by rw [f₈.mem, u₇.mem, mem₆]
  have rd₈ : c₈.rd = s.rd := by rw [f₈.rd, u₇.rd, rd₆]
  have wr₈ : c₈.wr = s.wr := by rw [f₈.wr, u₇.wr, wr₆]
  have sp₈ : c₈.sp = s.sp := by rw [f₈.sp, u₇.sp, sp₆]
  refine WP.ite (!decide ((stackArg s 0).toNat = 8))
    (by show eval .ne c₈ = _; rw [eval_ne, hi]) (fun hb'' => VG.Proof.Rc2.Arm.Stream.wp_mov_imm (by decide) (WP.block_nil ?_))
    fun hb'' => WP.block_nil ?_
  · have hb'' : ¬(stackArg s 0).toNat = 8 := by simpa using hb''
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₈ r h12], by rw [mem_setReg, mem₈],
      by rw [rd_setReg, rd₈], by rw [wr_setReg, wr₈], by rw [sp_setReg, sp₈], ?_, fun h => absurd h.2.2 hb'',
      fun _ => ?_⟩
    · rw [z_setReg, hi]; simp only [VG.Proof.Rc2.Arm.Stream.IValid, hb'', and_false, decide_false]
    · rw [gpr_setReg_self]; simp only [VG.Proof.Rc2.Arm.Stream.ICode, hb, hb']; rfl
  · have hb'' : (stackArg s 0).toNat = 8 := by simpa using hb''
    refine ⟨fun r _ h12 => g₈ r h12, mem₈, rd₈, wr₈, sp₈, ?_, fun _ => g₈ _ (by decide),
      fun h => absurd ⟨hb, hb', hb''⟩ h⟩
    rw [hi]; simp only [VG.Proof.Rc2.Arm.Stream.IValid, hb, hb', hb'', and_self, decide_true]

end VG.Proof.Rc2.Arm.Stream

end

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` once the lengths are valid

-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_ldr wp_str wp_ldrSp eval_ne)

/-- The state before the call of `vg_rc2_expand_key`, from the entry state `s`. -/
structure ArgsPost (s u : State) : Prop where
  r0 : u.gpr .r0 = s.gpr .r0
  r1 : u.gpr .r1 = s.gpr .r1
  r2 : u.gpr .r2 = s.gpr .r2
  r3 : u.gpr .r3 = stackArg s 1
  r12 : u.gpr .r12 = stackArg s 2
  callee : ∀ r ∈ preserved, r ≠ .lr → u.gpr r = s.gpr r
  sp : u.sp = s.sp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  frame : Frame [⟨State.addr (stackArg s 1) + BitVec.ofNat 64 128, 8⟩,
    ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩] s.mem u.mem
  lr : u.mem.readW (State.addr (stackArg s 2) + BitVec.ofNat 64 512) 32 = s.gpr .lr
  iv : Spec.Rc2.blockAt u.mem (State.addr (stackArg s 1) + BitVec.ofNat 64 128) =
    Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r3))

theorem args_ok (s : State) (hs : initContract.pre s) (hv : VG.Proof.Rc2.Arm.Stream.IValid s) (c : State) (hc : VG.Proof.Rc2.Arm.Stream.CheckPost s c) :
    WP isa (.block initArgs) c (VG.Proof.Rc2.Arm.Stream.ArgsPost s) := by
  obtain ⟨_, spfit, hrd, hwr, _, _, ivCtx, ivScr, ctxScr, ctxArgs, scrArgs, _, _, _, _, _, _, fitIV,
    fitC, fitS⟩ := hs
  have hL : (stackArg s 0).toNat = 8 := hv.2.2
  rw [hL] at ivCtx ivScr fitIV hrd
  have g (r : Reg) (h : r ≠ .r12) : c.gpr r = s.gpr r := by
    by_cases h0 : r = .r0
    · subst h0; exact hc.ok hv
    · exact hc.keep r h0 h
  have argR (i : Nat) (hi : i < 3) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 :=
    VG.Proof.Rc2.Arm.Stream.argIn (by rw [hrd]; simp) hi spfit
  generalize hIV : s.gpr .r3 = IV at *
  generalize hCt : stackArg s 1 = Ct at *
  generalize hS : stackArg s 2 = S at *
  generalize hLR : s.gpr .lr = LR at *
  have lrSub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 512, 4⟩ ⟨State.addr S, 576⟩ := Offset.sub_base _ (by decide)
  have ivSub' : Region.Sub ⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩ ⟨State.addr Ct, 144⟩ :=
    Offset.sub_base _ (by decide)
  have argsSep : ∀ r ∈ [(⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩ : Region),
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩], (Region.mk (stackArgAddr s 0) 12).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ctxArgs.symm.sub_right ivSub'
    · exact scrArgs.symm.sub_right lrSub
  rw [show initArgs = [.ldrSp .r12 8, .str .lr .r12 512, .ldr .lr .r3 0, .ldr .r3 .r3 4, .ldrSp .r12 4,
    .str .lr .r12 128, .str .r3 .r12 132, .mov .r3 (.reg .r12), .ldrSp .r12 8] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [hc.sp]; rfl)
    (by rw [hc.rd, hc.wr]; exact argR 2 (by decide)) fun u₁ v₁ => ?_
  have r12₁ : u₁.gpr .r12 = S := by rw [v₁.gpr, hc.mem]; exact hS
  refine wp_str (a := State.addr S + BitVec.ofNat 64 512) (by decide) (by rw [r12₁]; exact addr_add (by omega))
    (by rw [v₁.wr, hc.wr, hwr]; exact ⟨⟨State.addr S, 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₂ v₂ => ?_
  have m₂ : u₂.mem = s.mem.writeW (State.addr S + BitVec.ofNat 64 512) LR := by
    rw [v₂.mem, v₁.mem, hc.mem, v₁.other _ (by decide), g _ (by decide), hLR]
  have f₂ : Frame [⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩, ⟨State.addr S + BitVec.ofNat 64 512, 4⟩]
      s.mem u₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have r3₂ : u₂.gpr .r3 = IV := by rw [v₂.gpr, v₁.other _ (by decide), g _ (by decide), hIV]
  have ivR : InRegions (u₂.rd ++ u₂.wr) (State.addr IV) 8 := by
    rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, hc.rd, hc.wr, hrd]; exact ⟨_, by simp, Region.contains_self _ _⟩
  have ivRead (k : Nat) (hk : k ≤ 4) : u₂.mem.readW (State.addr IV + BitVec.ofNat 64 k) 32 =
      s.mem.readW (State.addr IV + BitVec.ofNat 64 k) 32 := by
    rw [m₂]
    refine Mem.readW_writeW_sep (ivScr.sep (Offset.contains_base _ (by omega) (by omega)) ?_) (by decide)
    exact Offset.contains_base _ (by decide) (by decide)
  refine wp_ldr (a := State.addr IV + BitVec.ofNat 64 0) (by decide)
    (by rw [r3₂]; exact addr_add (by omega))
    (by obtain ⟨r, hr, hc'⟩ := ivR; exact ⟨r, hr, by rw [VG.Proof.Rc2.Arm.Stream.add0]; unfold Region.Contains at hc' ⊢; omega⟩)
    fun u₃ v₃ => ?_
  refine wp_ldr (a := State.addr IV + BitVec.ofNat 64 4) (by decide)
    (by rw [v₃.other _ (by decide), r3₂]; exact addr_add (by omega))
    (by rw [v₃.rd, v₃.wr]; exact (Cbc.halves ivR).2) fun u₄ v₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) (by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]; rfl)
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, hc.rd, hc.wr]; exact argR 1 (by decide))
    fun u₅ v₅ => ?_
  have r12₅ : u₅.gpr .r12 = Ct := by
    rw [v₅.gpr, v₄.mem, v₃.mem, VG.Proof.Rc2.Arm.Stream.stackArg_frame f₂ spfit argsSep (by decide)]; exact hCt
  have wr₅ : u₅.wr = s.wr := by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, hc.wr]
  refine wp_str (a := State.addr Ct + BitVec.ofNat 64 128) (by decide) (by rw [r12₅]; exact addr_add (by omega))
    (by rw [wr₅, hwr]; exact ⟨⟨State.addr Ct, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩) fun u₆ v₆ => ?_
  refine wp_str (a := State.addr Ct + BitVec.ofNat 64 128 + BitVec.ofNat 64 4) (by decide)
    (by rw [v₆.gpr, r12₅, Offset.add_add]; exact addr_add (by omega))
    (by rw [v₆.wr, wr₅, hwr, Offset.add_add]; exact ⟨⟨State.addr Ct, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₇ v₇ => wp_mov (op2_reg _ _) fun u₈ v₈ => ?_
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide)
    (by rw [v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]; rfl)
    (by rw [v₈.rd, v₈.wr, v₇.rd, v₇.wr, v₆.rd, v₆.wr, v₅.rd, wr₅, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hc.rd]
        exact argR 2 (by decide)) fun u₉ v₉ => WP.block_nil ?_
  -- The memory.
  have w0 : u₅.gpr .lr = s.mem.readW (State.addr IV + BitVec.ofNat 64 0) 32 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, ivRead 0 (by decide)]
  have w1 : u₆.gpr .r3 = s.mem.readW (State.addr IV + BitVec.ofNat 64 4) 32 := by
    rw [v₆.gpr, v₅.other _ (by decide), v₄.gpr, v₃.mem, ivRead 4 (by decide)]
  have m₇ : u₇.mem = u₂.mem.writeW (State.addr Ct + BitVec.ofNat 64 128)
      (s.mem.readW (State.addr IV + BitVec.ofNat 64 4) 32 ++ s.mem.readW (State.addr IV + BitVec.ofNat 64 0) 32) := by
    rw [v₇.mem, w1, v₆.mem, w0, v₅.mem, v₄.mem, v₃.mem, VG.Proof.Rc2.Word32.write64_pair]
  have mem₉ : u₉.mem = u₇.mem := by rw [v₉.mem, v₈.mem]
  have f₇ : Frame [⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩, ⟨State.addr S + BitVec.ofNat 64 512, 4⟩]
      s.mem u₇.mem := by
    rw [m₇]; exact f₂.writeW (by simp) _ (Region.contains_self _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr hl => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.gpr, v₇.gpr, v₆.gpr, r12₅, hCt]
  · rw [v₉.gpr, v₈.mem, VG.Proof.Rc2.Arm.Stream.stackArg_frame f₇ spfit argsSep (by decide)]
  · obtain ⟨h0, h1, h2, h3, h12⟩ := VG.Proof.Rc2.Arm.Stream.preserved_ne hr hl
    rw [v₉.other _ h12, v₈.other _ h3, v₇.gpr, v₆.gpr, v₅.other _ h12, v₄.other _ h3, v₃.other _ hl, v₂.gpr,
      v₁.other _ h12, g _ h12]
  · rw [v₉.sp, v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]
  · rw [v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hc.rd]
  · rw [v₉.wr, v₈.wr, v₇.wr, v₆.wr, wr₅]
  · rw [hCt, hS, mem₉]; exact f₇
  · rw [hS, hLR, mem₉, m₇, Mem.readW_writeW_sep (((ctxScr.sub_left ivSub').sub_right lrSub).symm.sep (Region.contains_self _ _)
      (Region.contains_self _ _)) (by decide), m₂, Mem.readW_writeW_self32]
  · rw [hCt, hIV, mem₉, m₇, Proof.Rc2.blockAt_store64, VG.Proof.Rc2.Arm.Stream.add0, ← VG.Proof.Rc2.Word32.read64_pair,
      ← Proof.Rc2.blockAt_read64]

end VG.Proof.Rc2.Arm.Stream

end

section

/-!
# Streaming RC2-CBC on ARMv7: the update functions are constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the test of
`out_len`, the copies before the call and the restore of `lr` after it are
checked by the taint analysis, from the public arguments (in registers and on
the stack), whose values in each run the correctness proofs pin; the branch on
`out_len` agrees in both runs; and the call of the CBC function, in its frame,
is constant time by its own proof (`cbc_rel`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (eval_eq)

theorem wp_nil_inv {s : State} {Q : State → Prop} (h : WP isa (.block []) s Q) : Q s := by
  obtain ⟨_, _, he, hq⟩ := h
  cases he with
  | block h => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]; exact hq

theorem sa0' (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  unfold stackArgAddr; rw [show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp from BitVec.add_zero _]

/-- Two states agree on the registers `rs` and the 12 bytes of stack arguments. -/
theorem agree12 {rs : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) (hsp : s₁.sp = s₂.sp)
    (fit : s₁.sp.toNat + 12 ≤ 2 ^ 32)
    (hw₁ : ∀ r ∈ s₁.wr, Region.Disjoint ⟨stackArgAddr s₁ 0, 12⟩ r)
    (hw₂ : ∀ r ∈ s₂.wr, Region.Disjoint ⟨stackArgAddr s₂ 0, 12⟩ r)
    (ha : ∀ i < 3, stackArg s₁ i = stackArg s₂ i) : VG.Arm.Taint.Agree (argTaint rs 12) s₁ s₂ :=
  agree_argTaint h hsp ⟨fit, by rw [← VG.Proof.Rc2.Arm.Stream.sa0']; exact hw₁⟩ ⟨hsp ▸ fit, by rw [← VG.Proof.Rc2.Arm.Stream.sa0']; exact hw₂⟩
    (argMem_of (j := 3) hsp fit ha)

/-- The code before the call, its pieces associated to the left. -/
def prefixL : Prog isa :=
  .seq (.seq (.seq (.seq (.seq (.seq (.block toOut) (copy .r0 136 .lr 0 .r1)) (.block middle))
    (copy .r2 0 .lr 0 .r1)) (.block toPending)) (copy .r2 0 .lr 136 .r3)) (.block cbcArgs)

theorem prefix_wp (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : VG.Proof.Rc2.Arm.Stream.Keep s t) : WP isa VG.Proof.Rc2.Arm.Stream.prefixL t (VG.Proof.Rc2.Arm.Stream.Mid s) := by
  have h := VG.Proof.Rc2.Arm.Stream.long_ok' d s hs hnz t ht (tail := .block []) (Q := VG.Proof.Rc2.Arm.Stream.Mid s) fun t' h => WP.block_nil h
  rw [VG.Proof.Rc2.Arm.Stream.longWith] at h
  have h := WP.assoc' (WP.assoc' (WP.assoc' (WP.assoc' (WP.assoc' (WP.assoc' h)))))
  exact WP.mono (WP.seq_iff.mp h) fun _ h => VG.Proof.Rc2.Arm.Stream.wp_nil_inv h

theorem b0_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12)
    (.block [.ldrSp .r12 4, .cmp .r12 (.imm 0)]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem short_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) short hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem prefix_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) VG.Proof.Rc2.Arm.Stream.prefixL hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem restore_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 12) (.block restoreLr) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem stackArg_keep {s t : State} (ht : VG.Proof.Rc2.Arm.Stream.Keep s t) (i : Nat) : stackArg t i = stackArg s i := by
  unfold stackArg stackArgAddr; rw [ht.mem, ht.sp]

theorem wrSep (d : Spec.Rc2.Direction) {s : State} (h : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨stackArgAddr s 0, 12⟩ r := by
  obtain ⟨_, _, _, hwr, _, _, _, ctxArgs, _, _, _, outArgs, scrArgs, _⟩ := h
  rw [hwr]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ctxArgs.symm
  · exact outArgs.symm
  · exact scrArgs.symm

theorem update_rel (d : Spec.Rc2.Direction) {s₀ s₀' : State} (h0 : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s₀)
    (h0' : (VG.Proof.Rc2.Arm.Stream.updateContract d).pre s₀') (hq : (VG.Proof.Rc2.Arm.Stream.updateContract d).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update d) fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have fit := h0.2.1
  have qa : ∀ i < 3, stackArg s₀ i = stackArg s₀' i := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact q₅
    · exact q₆
    · exact q₇
  have regs : ∀ r ∈ ([.r0, .r1, .r2, .r3] : List Reg), s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  have keepAgree : ∀ t t', VG.Proof.Rc2.Arm.Stream.Keep s₀ t → VG.Proof.Rc2.Arm.Stream.Keep s₀' t' →
      VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2, .r3] 12) t t' := fun t t' k k' =>
    VG.Proof.Rc2.Arm.Stream.agree12 (fun r hr => by
        have hr12 : r ≠ .r12 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> decide
        rw [k.reg r hr12, k'.reg r hr12]; exact regs r hr)
      (by rw [k.sp, k'.sp, q₀]) (by rw [k.sp]; exact fit)
      (by rw [k.wr, show stackArgAddr t 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [k.sp]]; exact VG.Proof.Rc2.Arm.Stream.wrSep d h0)
      (by rw [k'.wr, show stackArgAddr t' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [k'.sp]]
          exact VG.Proof.Rc2.Arm.Stream.wrSep d h0')
      (fun i hi => by rw [VG.Proof.Rc2.Arm.Stream.stackArg_keep k, VG.Proof.Rc2.Arm.Stream.stackArg_keep k']; exact qa i hi)
  rw [update]
  refine RelCT.seq (rel_agree (F := (· = s₀)) (F' := (· = s₀'))
    (G := fun t => VG.Proof.Rc2.Arm.Stream.Keep s₀ t ∧ t.z = decide ((stackArg s₀ 1).toNat = 0))
    (G' := fun t => VG.Proof.Rc2.Arm.Stream.Keep s₀' t ∧ t.z = decide ((stackArg s₀' 1).toNat = 0))
    (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      exact VG.Proof.Rc2.Arm.Stream.agree12 regs q₀ fit (VG.Proof.Rc2.Arm.Stream.wrSep d h0) (VG.Proof.Rc2.Arm.Stream.wrSep d h0') qa) VG.Proof.Rc2.Arm.Stream.b0_taint
    (fun s e => e ▸ VG.Proof.Rc2.Arm.Stream.b0_wp d s₀ h0) (fun s e => e ▸ VG.Proof.Rc2.Arm.Stream.b0_wp d s₀' h0')) ?_
  refine RelCT.ite (fun t t' ⟨⟨_, z⟩, ⟨_, z'⟩⟩ => by
    show eval .eq t = eval .eq t'; rw [eval_eq, eval_eq, z, z', q₆]) ?_ ?_
  · refine (rel_agree (F := fun t => VG.Proof.Rc2.Arm.Stream.Keep s₀ t ∧ (stackArg s₀ 1).toNat = 0)
      (F' := fun t => VG.Proof.Rc2.Arm.Stream.Keep s₀' t ∧ (stackArg s₀' 1).toNat = 0) (G := fun _ => True) (G' := fun _ => True)
      (argTaint [.r0, .r1, .r2, .r3] 12) (fun t t' k k' => keepAgree t t' k.1 k'.1) VG.Proof.Rc2.Arm.Stream.short_taint
      (fun t k => WP.mono (VG.Proof.Rc2.Arm.Stream.short_ok d s₀ h0 k.2 t k.1) fun _ _ => trivial)
      (fun t k => WP.mono (VG.Proof.Rc2.Arm.Stream.short_ok d s₀' h0' k.2 t k.1) fun _ _ => trivial)).mono ?_ fun _ _ _ => trivial
    rintro t t' ⟨⟨⟨k, z⟩, ⟨k', z'⟩⟩, he⟩
    have h1 : (stackArg s₀ 1).toNat = 0 := by
      change eval .eq t = _ at he
      rw [eval_eq, z] at he; exact of_decide_eq_true (Option.some.inj he)
    exact ⟨⟨k, h1⟩, ⟨k', by rw [← q₆]; exact h1⟩⟩
  by_cases hz0 : (stackArg s₀ 1).toNat = 0
  · refine RelCT.of_false fun t t' ⟨⟨⟨_, z⟩, _⟩, he⟩ => ?_
    change eval .eq t = _ at he
    rw [eval_eq, z, hz0] at he; simp at he
  have hz0' : (stackArg s₀' 1).toNat ≠ 0 := by rw [← q₆]; exact hz0
  rw [VG.Proof.Rc2.Arm.Stream.long_eq, VG.Proof.Rc2.Arm.Stream.longWith]
  apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc
  apply RelCT.assoc
  refine RelCT.mono (P := fun t t' => (VG.Proof.Rc2.Arm.Stream.Keep s₀ t ∧ (stackArg s₀ 1).toNat ≠ 0) ∧
    (VG.Proof.Rc2.Arm.Stream.Keep s₀' t' ∧ (stackArg s₀' 1).toNat ≠ 0)) ?_ ?_ fun _ _ h => h
  · refine RelCT.seq (rel_agree (F := fun t => VG.Proof.Rc2.Arm.Stream.Keep s₀ t ∧ (stackArg s₀ 1).toNat ≠ 0)
      (F' := fun t => VG.Proof.Rc2.Arm.Stream.Keep s₀' t ∧ (stackArg s₀' 1).toNat ≠ 0) (G := VG.Proof.Rc2.Arm.Stream.Mid s₀) (G' := VG.Proof.Rc2.Arm.Stream.Mid s₀')
      (argTaint [.r0, .r1, .r2, .r3] 12) (fun t t' k k' => keepAgree t t' k.1 k'.1) VG.Proof.Rc2.Arm.Stream.prefix_taint
      (fun t k => VG.Proof.Rc2.Arm.Stream.prefix_wp d s₀ h0 k.2 t k.1) (fun t k => VG.Proof.Rc2.Arm.Stream.prefix_wp d s₀' h0' k.2 t k.1)) ?_
    have hct : RelCT isa (fun t t' => VG.Proof.Rc2.Arm.Stream.Mid s₀ t ∧ VG.Proof.Rc2.Arm.Stream.Mid s₀' t') (cbcCall d) fun _ _ => True :=
      VG.Proof.Rc2.Arm.Stream.cbc_rel (sp₀ := s₀.sp) fun t t' ⟨m, m'⟩ => ⟨VG.Proof.Rc2.Arm.Stream.mid_pre d s₀ h0 t m, by
        have := VG.Proof.Rc2.Arm.Stream.mid_pre d s₀' h0' t' m'; rwa [← q₁, ← q₅, ← q₆, ← q₇] at this, m.sp, m'.sp.trans q₀.symm⟩
    refine RelCT.seq (rel_wp (G := fun u => ∃ t, VG.Proof.Rc2.Arm.Stream.Mid s₀ t ∧ VG.Proof.Rc2.Arm.Stream.CbcPost d t (s₀.gpr .r0) (s₀.gpr .r0 + 128)
        (stackArg s₀ 0) (BitVec.ofNat 32 ((stackArg s₀ 1).toNat / 8)) (stackArg s₀ 2) u)
      (G' := fun u => ∃ t, VG.Proof.Rc2.Arm.Stream.Mid s₀' t ∧ VG.Proof.Rc2.Arm.Stream.CbcPost d t (s₀'.gpr .r0) (s₀'.gpr .r0 + 128)
        (stackArg s₀' 0) (BitVec.ofNat 32 ((stackArg s₀' 1).toNat / 8)) (stackArg s₀' 2) u) hct
      (fun t m => WP.mono (VG.Proof.Rc2.Arm.Stream.cbc_call (VG.Proof.Rc2.Arm.Stream.mid_pre d s₀ h0 t m)) fun u hu => ⟨t, m, hu⟩)
      (fun t m => WP.mono (VG.Proof.Rc2.Arm.Stream.cbc_call (VG.Proof.Rc2.Arm.Stream.mid_pre d s₀' h0' t m)) fun u hu => ⟨t, m, hu⟩)) ?_
    refine rel_agree (argTaint [] 12) (fun u u' ⟨t, m, c⟩ ⟨t', m', c'⟩ => ?_) VG.Proof.Rc2.Arm.Stream.restore_taint
      (fun u ⟨t, m, c⟩ => WP.mono (VG.Proof.Rc2.Arm.Stream.restore_ok d s₀ h0 hz0 t m u c) fun _ _ => trivial)
      (fun u ⟨t, m, c⟩ => WP.mono (VG.Proof.Rc2.Arm.Stream.restore_ok d s₀' h0' hz0' t m u c) fun _ _ => trivial) |>.mono
      (fun _ _ h => h) fun _ _ _ => trivial
    exact VG.Proof.Rc2.Arm.Stream.agree12 (fun r hr => (List.not_mem_nil hr).elim) (by rw [c.sp, m.sp, c'.sp, m'.sp, q₀])
      (by rw [c.sp, m.sp]; exact fit)
      (by rw [c.wr, m.wr, show stackArgAddr u 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [c.sp, m.sp]]
          exact VG.Proof.Rc2.Arm.Stream.wrSep d h0)
      (by rw [c'.wr, m'.wr, show stackArgAddr u' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [c'.sp, m'.sp]]
          exact VG.Proof.Rc2.Arm.Stream.wrSep d h0')
      (fun i hi => by rw [VG.Proof.Rc2.Arm.Stream.args_after d s₀ h0 t m u c i hi, VG.Proof.Rc2.Arm.Stream.args_after d s₀' h0' t' m' u' c' i hi]; exact qa i hi)
  · intro t t' ⟨⟨⟨k, _⟩, ⟨k', _⟩⟩, _⟩
    exact ⟨⟨k, hz0⟩, ⟨k', hz0'⟩⟩

theorem update_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (VG.Proof.Rc2.Arm.Stream.updateContract d).pre (VG.Proof.Rc2.Arm.Stream.updateContract d).pub (update d) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.Rc2.Arm.Stream.update_rel d h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Rc2.Arm.Stream

end

section

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` is correct

-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_ldr wp_ldrSp eval_ne)

/-- The postcondition of `init`: the callee-saved registers and the contract's. -/
abbrev InitPost (s s' : State) : Prop := (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ initContract.post s s'

theorem key_pre (s : State) (hs : initContract.pre s) (hv : VG.Proof.Rc2.Arm.Stream.IValid s) (u : State) (hu : VG.Proof.Rc2.Arm.Stream.ArgsPost s u) :
    VG.Proof.Rc2.Arm.Stream.KeyPre u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) := by
  obtain ⟨sp8, _, hrd, hwr, keyCtx, keyScr, _, _, ctxScr, _, _, bKey, _, bCtx, bScr, _, fitK, _, fitC, fitS⟩ := hs
  have p128 : Region.Sub ⟨State.addr (stackArg s 1), 128⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Region.sub_prefix (by decide)
  have p512 : Region.Sub ⟨State.addr (stackArg s 2), 512⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Region.sub_prefix (by decide)
  have eb : (⟨State.addr u.sp - 8, 8⟩ : Region) = ⟨State.addr s.sp - 8, 8⟩ := by rw [hu.sp]
  refine ⟨hu.r0, hu.r1, hu.r2, hu.r3, hu.r12, by rw [hu.sp]; exact sp8,
    ⟨hv.1.1, hv.1.2, hv.2.1.1, hv.2.1.2⟩, keyCtx.sub_right p128, keyScr.sub_right p512,
    (ctxScr.sub_left p128).sub_right p512, ?_, ?_, ?_, fitK, by omega, by omega, ?_, ?_⟩
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bKey
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bCtx.sub_right p128
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bScr.sub_right p512
  · rw [hu.rd, hu.wr, hrd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp, 0, (VG.Proof.Rc2.Arm.Stream.add0 _).symm, by simp⟩
  · rw [hu.wr, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr (stackArg s 1), 144⟩, by simp, 0, (VG.Proof.Rc2.Arm.Stream.add0 _).symm, by simp⟩
      · exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, 0, (VG.Proof.Rc2.Arm.Stream.add0 _).symm, by simp⟩

theorem tail_ok (s : State) (hs : initContract.pre s) (hv : VG.Proof.Rc2.Arm.Stream.IValid s) (u : State) (hu : VG.Proof.Rc2.Arm.Stream.ArgsPost s u)
    (v : State) (hk : VG.Proof.Rc2.Arm.Stream.KeyPost u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) v) :
    WP isa (.block (restoreLr ++ ([.mov .r0 (.imm 0)] : List Instr))) v (VG.Proof.Rc2.Arm.Stream.InitPost s) := by
  obtain ⟨_, spfit, hrd, hwr, keyCtx, keyScr, _, _, ctxScr, ctxArgs, scrArgs, bKey, _, bCtx, bScr, bArgs,
    fitK, _, fitC, fitS⟩ := hs
  have eb : VG.Proof.Rc2.Arm.Stream.below u = ⟨State.addr s.sp - 8, 8⟩ := by simp only [VG.Proof.Rc2.Arm.Stream.below, hu.sp]
  have frame₂ := hk.frame
  rw [eb] at frame₂
  have p128 : Region.Sub ⟨State.addr (stackArg s 1), 128⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Region.sub_prefix (by decide)
  have i128 : Region.Sub ⟨State.addr (stackArg s 1) + BitVec.ofNat 64 128, 8⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Offset.sub_base _ (by decide)
  have p512 : Region.Sub ⟨State.addr (stackArg s 2), 512⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Region.sub_prefix (by decide)
  have l512 : Region.Sub ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Offset.sub_base _ (by decide)
  rw [show restoreLr ++ [.mov .r0 (.imm 0)] = [.ldrSp .r12 8, .ldr .lr .r12 512, .mov .r0 (.imm 0)] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [hk.sp, hu.sp]; rfl)
    (by rw [hk.rd, hk.wr, hu.rd, hu.wr]; exact VG.Proof.Rc2.Arm.Stream.argIn (by rw [hrd]; simp) (by decide) spfit) fun v₁ w₁ => ?_
  have hc2 : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s 2) (32 / 8) := by
    rw [VG.Proof.Rc2.Arm.Stream.stackArgAddr_eq s (i := 2) (by decide) spfit]; exact Offset.contains_base _ (by decide) (by decide)
  have argsS : v.mem.readW (stackArgAddr s 2) 32 = stackArg s 2 := by
    rw [frame₂.readW hc2 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ctxArgs.symm.sub_right p128
        · exact scrArgs.symm.sub_right p512
        · exact bArgs.symm) (by decide)]
    refine VG.Proof.Rc2.Arm.Stream.stackArg_frame hu.frame spfit (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ctxArgs.symm.sub_right i128
    · exact scrArgs.symm.sub_right l512
  refine wp_ldr (a := State.addr (stackArg s 2) + BitVec.ofNat 64 512) (by decide)
    (by rw [w₁.gpr, argsS]; exact addr_add (by omega))
    (by rw [w₁.rd, w₁.wr, hk.rd, hk.wr, hu.rd, hu.wr, hwr]
        exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun v₂ w₂ => VG.Proof.Rc2.Arm.Stream.wp_mov_imm (by decide) (WP.block_nil ?_)
  have lr₂ : v₂.gpr .lr = s.gpr .lr := by
    rw [w₂.gpr, w₁.mem, frame₂.readW (r := ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ((ctxScr.sub_left p128).sub_right l512).symm
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (bScr.sub_right l512).symm) (by decide), hu.lr]
  have mem₂ : v₂.mem = v.mem := by rw [w₂.mem, w₁.mem]
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hl : r = .lr
    · subst hl; rw [gpr_setReg_of_ne _ _ (by decide), lr₂]
    · obtain ⟨h0, _, _, _, h12⟩ := VG.Proof.Rc2.Arm.Stream.preserved_ne hr hl
      rw [gpr_setReg_of_ne _ _ h0, w₂.other _ hl, w₁.other _ h12, hk.saved r hr hl, hu.callee r hr hl]
  · have hsched : Spec.Rc2.scheduleAt (v₂.setReg .r0 0).mem (State.addr (stackArg s 1)) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat := by
      rw [mem_setReg, mem₂, hk.sched, Proof.Rc2.bytesAt_frame hu.frame _ _ (by omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact keyCtx.sub_right i128
        · exact keyScr.sub_right l512)]
    have hiv : Spec.Rc2.blockAt (v₂.setReg .r0 0).mem (State.addr (stackArg s 1) + 128) =
        Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r3)) := by
      rw [mem_setReg, mem₂, VG.Proof.Rc2.Arm.Stream.e128, Proof.Rc2.blockAt_frame frame₂ _ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (ctxScr.sub_left i128).sub_right p512
        · exact (bCtx.sub_right i128).symm), hu.iv]
    exact init_post hv.1 hv.2.1 hv.2.2 (by rw [VG.Proof.Rc2.Arm.Stream.setWidth_append, gpr_setReg_self]) hsched hiv

theorem init_wp (s : State) (hs : initContract.pre s) : WP isa init s (VG.Proof.Rc2.Arm.Stream.InitPost s) := by
  rw [init]
  refine WP.seq (WP.mono (VG.Proof.Rc2.Arm.Stream.checks_ok s hs) fun c hc => ?_)
  by_cases hv : VG.Proof.Rc2.Arm.Stream.IValid s
  · refine WP.ite false (by show eval .ne c = _; rw [eval_ne, hc.z]; simp [hv]) (fun h => absurd h (by simp))
      fun _ => ?_
    rw [initBody]
    exact WP.seq (WP.mono (VG.Proof.Rc2.Arm.Stream.args_ok s hs hv c hc) fun u hu =>
      WP.seq (WP.mono (VG.Proof.Rc2.Arm.Stream.key_call (VG.Proof.Rc2.Arm.Stream.key_pre s hs hv u hu)) fun v hk => VG.Proof.Rc2.Arm.Stream.tail_ok s hs hv u hu v hk))
  · refine WP.ite true (by show eval .ne c = _; rw [eval_ne, hc.z]; simp [hv]) (fun _ => WP.block_nil ?_)
      (fun h => absurd h (by simp))
    refine ⟨fun r hr => ?_, ?_⟩
    · have h : r ≠ .r0 ∧ r ≠ .r12 := by
        by_cases hl : r = .lr
        · subst hl; decide
        · obtain ⟨h0, _, _, _, h12⟩ := VG.Proof.Rc2.Arm.Stream.preserved_ne hr hl; exact ⟨h0, h12⟩
      exact hc.keep r h.1 h.2
    · exact init_post_error (by rw [VG.Proof.Rc2.Arm.Stream.setWidth_append]; exact hc.err hv) hv

theorem init_correct (s : State) (hs : initContract.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.Arm.Stream.init_wp s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

end VG.Proof.Rc2.Arm.Stream

end

section

/-!
# Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` is constant time

As for the updates (`Stream/UpdateCT.lean`): the checks, the copy of the IV
and the restore of `lr` are checked by the taint analysis, from the public
arguments; the branch on the checks agrees in both runs, as the lengths are
public; and the call of `vg_rc2_expand_key`, in its frame, is constant time by
its own proof (`key_rel`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (eval_ne)

/-- The stack arguments after the call are those on entry. -/
theorem args_after_key (s : State) (hs : initContract.pre s) (u : State) (hu : VG.Proof.Rc2.Arm.Stream.ArgsPost s u) (v : State)
    (hk : VG.Proof.Rc2.Arm.Stream.KeyPost u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) v) :
    ∀ i < 3, stackArg v i = stackArg s i := by
  obtain ⟨_, spfit, _, _, _, _, _, _, _, ctxArgs, scrArgs, _, _, _, _, bArgs, _⟩ := hs
  have eb : VG.Proof.Rc2.Arm.Stream.below u = ⟨State.addr s.sp - 8, 8⟩ := by simp only [VG.Proof.Rc2.Arm.Stream.below, hu.sp]
  have frame₂ := hk.frame
  rw [eb] at frame₂
  intro i hi
  have hc : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s i) (32 / 8) := by
    rw [VG.Proof.Rc2.Arm.Stream.stackArgAddr_eq s hi spfit]; exact Offset.contains_base _ (by omega) (by omega)
  have ea : stackArgAddr v i = stackArgAddr s i := by unfold stackArgAddr; rw [hk.sp, hu.sp]
  rw [stackArg, ea, frame₂.readW hc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ctxArgs.symm.sub_right (Region.sub_prefix (by decide))
      · exact scrArgs.symm.sub_right (Region.sub_prefix (by decide))
      · exact bArgs.symm) (by decide)]
  refine VG.Proof.Rc2.Arm.Stream.stackArg_frame hu.frame spfit (fun r hr => ?_) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ctxArgs.symm.sub_right (Offset.sub_base _ (by decide))
  · exact scrArgs.symm.sub_right (Offset.sub_base _ (by decide))

theorem iwrSep {s : State} (h : initContract.pre s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨stackArgAddr s 0, 12⟩ r := by
  obtain ⟨_, _, _, hwr, _, _, _, _, _, ctxArgs, scrArgs, _⟩ := h
  rw [hwr]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ctxArgs.symm
  · exact scrArgs.symm

theorem checks_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) checks hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem initArgs_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) (.block initArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem tail_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [] 12) (.block (restoreLr ++ ([.mov .r0 (.imm 0)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem init_rel {s₀ s₀' : State} (h0 : initContract.pre s₀) (h0' : initContract.pre s₀')
    (hq : initContract.pub s₀ s₀') : RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have fit := h0.2.1
  have qa : ∀ i < 3, stackArg s₀ i = stackArg s₀' i := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact q₅
    · exact q₆
    · exact q₇
  have regs : ∀ r ∈ ([.r0, .r1, .r2, .r3] : List Reg), s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  have hvq : VG.Proof.Rc2.Arm.Stream.IValid s₀ ↔ VG.Proof.Rc2.Arm.Stream.IValid s₀' := by simp only [VG.Proof.Rc2.Arm.Stream.IValid, q₂, q₃, q₅]
  rw [init]
  refine RelCT.seq (rel_agree (F := (· = s₀)) (F' := (· = s₀')) (G := VG.Proof.Rc2.Arm.Stream.CheckPost s₀) (G' := VG.Proof.Rc2.Arm.Stream.CheckPost s₀')
    (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      exact VG.Proof.Rc2.Arm.Stream.agree12 regs q₀ fit (VG.Proof.Rc2.Arm.Stream.iwrSep h0) (VG.Proof.Rc2.Arm.Stream.iwrSep h0') qa) VG.Proof.Rc2.Arm.Stream.checks_taint
    (fun s e => e ▸ VG.Proof.Rc2.Arm.Stream.checks_ok s₀ h0) (fun s e => e ▸ VG.Proof.Rc2.Arm.Stream.checks_ok s₀' h0')) ?_
  refine RelCT.ite (fun c c' ⟨hc, hc'⟩ => by
    show eval .ne c = eval .ne c'; rw [eval_ne, eval_ne, hc.z, hc'.z]; simp only [hvq]) ?_ ?_
  · exact RelCT.block_nil fun _ _ _ => trivial
  by_cases hv : VG.Proof.Rc2.Arm.Stream.IValid s₀
  swap
  · refine RelCT.of_false fun c c' ⟨⟨hc, _⟩, he⟩ => ?_
    change eval .ne c = _ at he
    rw [eval_ne, hc.z] at he; simp [hv] at he
  have hv' : VG.Proof.Rc2.Arm.Stream.IValid s₀' := hvq.mp hv
  rw [initBody]
  refine RelCT.mono (P := fun c c' => VG.Proof.Rc2.Arm.Stream.CheckPost s₀ c ∧ VG.Proof.Rc2.Arm.Stream.CheckPost s₀' c') ?_ (fun _ _ h => h.1)
    fun _ _ h => h
  refine RelCT.seq (rel_agree (G := VG.Proof.Rc2.Arm.Stream.ArgsPost s₀) (G' := VG.Proof.Rc2.Arm.Stream.ArgsPost s₀') (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun c c' hc hc' => ?_) VG.Proof.Rc2.Arm.Stream.initArgs_taint
    (fun c hc => VG.Proof.Rc2.Arm.Stream.args_ok s₀ h0 hv c hc) (fun c hc => VG.Proof.Rc2.Arm.Stream.args_ok s₀' h0' hv' c hc)) ?_
  · have g : ∀ {s c}, VG.Proof.Rc2.Arm.Stream.IValid s → VG.Proof.Rc2.Arm.Stream.CheckPost s c → ∀ r ∈ ([.r0, .r1, .r2, .r3] : List Reg), c.gpr r = s.gpr r :=
      fun hv hc r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hc.ok hv
        all_goals exact hc.keep _ (by decide) (by decide)
    have st : ∀ {s c}, VG.Proof.Rc2.Arm.Stream.CheckPost s c → ∀ i, stackArg c i = stackArg s i := fun hc i => by
      unfold stackArg stackArgAddr; rw [hc.mem, hc.sp]
    exact VG.Proof.Rc2.Arm.Stream.agree12 (fun r hr => by rw [g hv hc r hr, g hv' hc' r hr]; exact regs r hr)
      (by rw [hc.sp, hc'.sp, q₀]) (by rw [hc.sp]; exact fit)
      (by rw [hc.wr, show stackArgAddr c 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [hc.sp]]
          exact VG.Proof.Rc2.Arm.Stream.iwrSep h0)
      (by rw [hc'.wr, show stackArgAddr c' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [hc'.sp]]
          exact VG.Proof.Rc2.Arm.Stream.iwrSep h0')
      (fun i hi => by rw [st hc, st hc']; exact qa i hi)
  have hct : RelCT isa (fun u u' => VG.Proof.Rc2.Arm.Stream.ArgsPost s₀ u ∧ VG.Proof.Rc2.Arm.Stream.ArgsPost s₀' u') keyCall fun _ _ => True :=
    VG.Proof.Rc2.Arm.Stream.key_rel (sp₀ := s₀.sp) fun u u' ⟨a, a'⟩ => ⟨VG.Proof.Rc2.Arm.Stream.key_pre s₀ h0 hv u a, by
      have := VG.Proof.Rc2.Arm.Stream.key_pre s₀' h0' hv' u' a'; rwa [← q₁, ← q₂, ← q₃, ← q₆, ← q₇] at this, a.sp, a'.sp.trans q₀.symm⟩
  refine RelCT.seq (rel_wp (G := fun v => ∃ u, VG.Proof.Rc2.Arm.Stream.ArgsPost s₀ u ∧
      VG.Proof.Rc2.Arm.Stream.KeyPost u (s₀.gpr .r0) (s₀.gpr .r1) (s₀.gpr .r2) (stackArg s₀ 1) (stackArg s₀ 2) v)
    (G' := fun v => ∃ u, VG.Proof.Rc2.Arm.Stream.ArgsPost s₀' u ∧
      VG.Proof.Rc2.Arm.Stream.KeyPost u (s₀'.gpr .r0) (s₀'.gpr .r1) (s₀'.gpr .r2) (stackArg s₀' 1) (stackArg s₀' 2) v) hct
    (fun u a => WP.mono (VG.Proof.Rc2.Arm.Stream.key_call (VG.Proof.Rc2.Arm.Stream.key_pre s₀ h0 hv u a)) fun v hk => ⟨u, a, hk⟩)
    (fun u a => WP.mono (VG.Proof.Rc2.Arm.Stream.key_call (VG.Proof.Rc2.Arm.Stream.key_pre s₀' h0' hv' u a)) fun v hk => ⟨u, a, hk⟩)) ?_
  refine (rel_agree (argTaint [] 12) (fun v v' ⟨u, a, k⟩ ⟨u', a', k'⟩ => ?_) VG.Proof.Rc2.Arm.Stream.tail_taint
    (fun v ⟨u, a, k⟩ => WP.mono (VG.Proof.Rc2.Arm.Stream.tail_ok s₀ h0 hv u a v k) fun _ _ => trivial)
    (fun v ⟨u, a, k⟩ => WP.mono (VG.Proof.Rc2.Arm.Stream.tail_ok s₀' h0' hv' u a v k) fun _ _ => trivial)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  exact VG.Proof.Rc2.Arm.Stream.agree12 (fun r hr => (List.not_mem_nil hr).elim) (by rw [k.sp, a.sp, k'.sp, a'.sp, q₀])
    (by rw [k.sp, a.sp]; exact fit)
    (by rw [k.wr, a.wr, show stackArgAddr v 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [k.sp, a.sp]]
        exact VG.Proof.Rc2.Arm.Stream.iwrSep h0)
    (by rw [k'.wr, a'.wr, show stackArgAddr v' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [k'.sp, a'.sp]]
        exact VG.Proof.Rc2.Arm.Stream.iwrSep h0')
    (fun i hi => by
      rw [VG.Proof.Rc2.Arm.Stream.args_after_key s₀ h0 u a v k i hi, VG.Proof.Rc2.Arm.Stream.args_after_key s₀' h0' u' a' v' k' i hi]; exact qa i hi)

theorem init_constantTime : ConstantTime isa initContract.pre initContract.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.Rc2.Arm.Stream.init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Rc2.Arm.Stream

end

/-! # Verified streaming RC2-CBC on ARMv7 -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm

theorem init_verified : Verified target Impl.Rc2.Arm.Stream.init (Proof.Rc2.cbcInitScratchContract abi 8) :=
  Verified.of_correct VG.Proof.Rc2.Arm.Stream.init_correct VG.Proof.Rc2.Arm.Stream.init_constantTime VG.Proof.Rc2.Arm.Stream.init_implies

theorem encryptUpdate_verified :
    Verified target Impl.Rc2.Arm.Stream.encryptUpdate (Proof.Rc2.cbcEncryptUpdateScratchContract abi 8) :=
  Verified.of_correct (VG.Proof.Rc2.Arm.Stream.update_correct .encrypt) (VG.Proof.Rc2.Arm.Stream.update_constantTime .encrypt) (VG.Proof.Rc2.Arm.Stream.update_implies .encrypt)

theorem decryptUpdate_verified :
    Verified target Impl.Rc2.Arm.Stream.decryptUpdate (Proof.Rc2.cbcDecryptUpdateScratchContract abi 8) :=
  Verified.of_correct (VG.Proof.Rc2.Arm.Stream.update_correct .decrypt) (VG.Proof.Rc2.Arm.Stream.update_constantTime .decrypt) (VG.Proof.Rc2.Arm.Stream.update_implies .decrypt)

end VG.Proof.Rc2.Arm.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Stream.Frame`. -/
section

/-!
# RC2-CBC's streaming functions on ARMv7, with their working space on the stack

`init` and the updates run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 592 bytes that allocates it and
copies their two other stack arguments (`Verified.stackScratchWiped`), and
zero it before returning.
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State :=
  { VG.Proof.Rc2.Arm.Stream.initSatState with
                      rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6000, 8⟩], wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract Arm.abi 600).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, initSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.Rc2.Arm.Stream.initFrameSat

theorem init_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init)
      (Spec.Rc2.cbcInitContract Arm.abi 600) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 592) (m := 2) (words := 144) VG.Proof.Rc2.Arm.Stream.init_verified (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (cbcInitPost_local _) (cbcInitPostOut_local _) VG.Proof.Rc2.Arm.Stream.initFrameSat_pre

/-- A state satisfying the update functions' precondition, without the
working space. -/
def updateFrameSat : State :=
  { VG.Proof.Rc2.Arm.Stream.updateSatState with
                        rd := [⟨0x2000, 0⟩, ⟨0x6000, 8⟩], wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩] }

theorem updateFrameSat_pre (d : Spec.Rc2.Direction) :
    ∃ s, (Spec.Rc2.cbcUpdateContract Arm.abi d 600).pre s := by
  implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, Spec.Rc2.cbcUpdatePre,
    Spec.Rc2.cbcUpdatePost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [updateFrameSat, updateSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.Rc2.Arm.Stream.updateFrameSat

theorem encryptUpdate_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.encryptUpdate)
      (Spec.Rc2.cbcEncryptUpdateContract Arm.abi 600) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre Arm.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .encrypt Arm.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 592) (m := 2) (words := 144) VG.Proof.Rc2.Arm.Stream.encryptUpdate_verified (by decide) (by decide)
    (by decide) (by decide) (by decide) (cbcUpdatePre_local _) (cbcUpdatePost_local _ _)
    (cbcUpdatePostOut_local _ _) (VG.Proof.Rc2.Arm.Stream.updateFrameSat_pre .encrypt)

theorem decryptUpdate_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.decryptUpdate)
      (Spec.Rc2.cbcDecryptUpdateContract Arm.abi 600) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre Arm.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .decrypt Arm.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 592) (m := 2) (words := 144) VG.Proof.Rc2.Arm.Stream.decryptUpdate_verified (by decide) (by decide)
    (by decide) (by decide) (by decide) (cbcUpdatePre_local _) (cbcUpdatePost_local _ _)
    (cbcUpdatePostOut_local _ _) (VG.Proof.Rc2.Arm.Stream.updateFrameSat_pre .decrypt)

end VG.Proof.Rc2.Arm.Stream

end
