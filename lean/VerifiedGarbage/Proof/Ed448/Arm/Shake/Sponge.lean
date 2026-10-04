import VerifiedGarbage.Proof.Ed448.Arm.Shake.Layout
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash
import VerifiedGarbage.Impl.Ed448.Arm.Shake
import VerifiedGarbage.Proof.X25519.Arm.Instr

/-!
# Ed448 on ARMv7: the calls of the sponge functions

The Keccak state zeroed (`Kit.zero_ok`), and each call of a sponge function
through `Whole.call_ok` with its own contract (`Proof.Sha3.absorbArm`,
`padArm`, `squeezeArm`), from its set-up (`Kit.first_abs`, `Kit.next_abs`,
`Kit.pad_step`, `Kit.sqz_step`), for any layout (`Kit`) with `scratch` in
the saved word `sc` (`ScrAt`). An absorption reads its data from the frame,
an input or an output (`DataOk`); each after the first starts at the
position the previous one returned in `r0`. Each step states the regions it
may write: the outgoing stack arguments (`kArgs E 8`), the state and the
working space (`kWr scr`), and the squeezed output.
-/

namespace VG.Proof.Ed448.Arm.Shake

open VG VG.Arm VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Spec.Sha3 (stateAt)
open VG.Proof.X25519.Arm (Upd wp_mov op2_reg)
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR Whole.Ctx Whole.call_ok)

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t u : State}

/-- `scratch` is the saved word `sc`. -/
structure ScrAt (n : Nat) (val : Nat → BitVec 32) (sc : Nat) (scr : BitVec 32) : Prop where
  slot : Slot n sc
  val : val sc = scr

/-! ## The regions -/

/-- The state and the sponge functions' working space. -/
def kWr (scr : BitVec 32) : List Region :=
  [⟨State.addr scr, 200⟩, ⟨State.addr scr + BitVec.ofNat 64 KSCR, 640⟩]

/-- The outgoing stack arguments. -/
abbrev kArgs (E : BitVec 32) (k : Nat) : Region := ⟨State.addr E, k⟩

theorem kWr_sub (scr : BitVec 32) : ∀ r ∈ kWr scr, Whole.Within r (SCR scr) := by
  intro r hr
  simp only [kWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨0, (BitVec.add_zero _).symm, by change 0 + 200 ≤ 8192; decide⟩
  · exact ⟨KSCR, rfl, by change 208 + 640 ≤ 8192; decide⟩

theorem state_scratch (scr : BitVec 32) : (⟨State.addr scr, 200⟩ : Region).Disjoint
    ⟨State.addr scr + BitVec.ofNat 64 KSCR, 640⟩ := Offset.base_disjoint _ (by decide) (by decide)

/-- Data an absorption may read: in the frame, or in an input or an output. -/
def DataOk (E : BitVec 32) (ins outs : List Region) (D : Region) : Prop :=
  Whole.Within D (Whole.FR E) ∨ ∃ R ∈ ins ++ outs, Whole.Within D R

theorem covers_of {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ ins ++ outs, Whole.Within r R) :
    Covers rs (ins ++ Whole.FR E :: outs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases h r hr with hf | ⟨R, hR, hw⟩
  · exact ⟨Whole.FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
  · refine ⟨R, ?_, hw⟩
    rcases List.mem_append.mp hR with hi | ho
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)

theorem args_within (E : BitVec 32) {k : Nat} (hk : k ≤ 248) : Whole.Within (kArgs E k) (Whole.FR E) :=
  ⟨0, (BitVec.add_zero _).symm, by change 0 + k ≤ 248; omega⟩

theorem frame_within (E : BitVec 32) {d k : Nat} (hd : d + k ≤ 248) :
    Whole.Within ⟨State.addr E + BitVec.ofNat 64 d, k⟩ (Whole.FR E) := ⟨d, rfl, hd⟩

/-! ## The state, through a step outside it -/

theorem state_frame {ws : List Region} {m m' : Mem} (hm : Frame ws m m')
    (hd : ∀ r ∈ ws, (⟨State.addr scr, 200⟩ : Region).Disjoint r) :
    stateAt m' (State.addr scr) = stateAt m (State.addr scr) :=
  Proof.Sha3.stateAt_congr fun _ hj => hm.bytes (R := ⟨State.addr scr, 200⟩) hd
    (by change 200 ≤ 2 ^ 64; decide) hj

theorem repr_frame' {ws : List Region} {m m' : Mem} (hm : Frame ws m m')
    (hd : ∀ r ∈ ws, (⟨State.addr scr, 200⟩ : Region).Disjoint r) {msg : List Byte}
    (h : Spec.Sha3.Repr m (State.addr scr) 136 msg) : Spec.Sha3.Repr m' (State.addr scr) 136 msg := by
  unfold Spec.Sha3.Repr at h ⊢
  rw [state_frame hm hd]; exact h

/-- An absorption's set-up writes its two stack arguments. -/
theorem args_two (len : Value) (sc : Nat) : 4 * [len, Value.caller sc KSCR].length = 8 := rfl

theorem valid_const {k : Nat} (h : k < 65536) : valid n (.const k) := h
theorem valid_frame {d : Nat} (h : d < 256) : valid n (.frame d) := h

theorem ScrAt.valid {sc : Nat} (hsc : ScrAt n val sc scr) {d : Nat} (hd : d < 256) : valid n (.caller sc d) :=
  ⟨hsc.slot, hd⟩

/-- What an absorption reads, and what a squeeze writes. -/
def absRd (E : BitVec 32) (D : Region) : List Region := [D, kArgs E 8]

def sqzWr (E scr : BitVec 32) (d : Nat) : List Region :=
  [⟨State.addr scr, 200⟩, ⟨State.addr E + BitVec.ofNat 64 d, 114⟩,
    ⟨State.addr scr + BitVec.ofNat 64 KSCR, 640⟩]

namespace Kit

variable (hk : Kit E scr n ins outs)
include hk

theorem scr_addr : State.addr (scr + BitVec.ofNat 32 KSCR) = State.addr scr + BitVec.ofNat 64 KSCR :=
  addr_add (by have := hk.nc; simp only [KSCR]; omega)

theorem scr_fit : (scr + BitVec.ofNat 32 KSCR).toNat + 640 ≤ 2 ^ 32 := by
  have := hk.nc
  rw [BitVec.toNat_add_of_lt (by change scr.toNat + 208 < 2 ^ 32; omega)]
  change scr.toNat + 208 + 640 ≤ 2 ^ 32
  omega

theorem kWr_writes : ∀ r ∈ kWr scr, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R :=
  fun r hr => .inr ⟨SCR scr, hk.so, kWr_sub scr r hr⟩

theorem kWr_covered : ∀ r ∈ kWr scr, ∃ R ∈ ins ++ outs, Whole.Within r R :=
  fun r hr => ⟨SCR scr, List.mem_append_right _ hk.so, kWr_sub scr r hr⟩

theorem args_scr {k : Nat} (hk' : k ≤ 280) : ∀ r ∈ kWr scr, (kArgs E k).Disjoint r :=
  fun r hr => (hk.kc.sub_left (Region.sub_prefix hk')).sub_right (kWr_sub scr r hr).sub

/-- A region of the frame is outside the state and the working space. -/
theorem frame_kWr {d l : Nat} (hd : d + l ≤ 280) :
    ∀ r ∈ kWr scr, Region.Disjoint ⟨State.addr E + BitVec.ofNat 64 d, l⟩ r :=
  fun r hr => (hk.stack_scr hd).sub_right (kWr_sub scr r hr).sub

/-- Data in an input is outside the state, the working space and the
outgoing stack arguments. -/
theorem data_input {D R : Region} (hR : R ∈ ins) (hw : Whole.Within D R) :
    (∀ r ∈ kWr scr, D.Disjoint r) ∧ (kArgs E 8).Disjoint D := by
  have ho := hk.io R hR
  refine ⟨fun r hr => ((ho (SCR scr) (List.mem_append_left _ hk.so)).sub_left hw.sub).sub_right
    (kWr_sub scr r hr).sub, ?_⟩
  exact ((ho (Whole.FR E) (by simp)).sub_left hw.sub).symm.sub_left (Region.sub_prefix (by decide))

/-- The state is outside the frame's first `k` bytes. -/
theorem state_args {k : Nat} (hk' : k ≤ 280) : ∀ r ∈ [kArgs E k], (⟨State.addr scr, 200⟩ : Region).Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (hk.args_scr hk' _ (by simp [kWr])).symm

/-! ## The state, zeroed -/

theorem zeroStores_step (hu : Whole.Ctx E g m₀ ins outs t) (h0 : t.gpr .r0 = scr) (h1 : t.gpr .r1 = 0) :
    WP isa (.block Impl.Ed448.Arm.PublicKey.zeroStores) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      stateAt v.mem (State.addr scr) = Spec.Sha3.zero ∧ Frame [⟨State.addr scr, 200⟩] t.mem v.mem := by
  have hw : ∀ k < 50, InRegions t.wr (State.addr (t.gpr .r0) + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k hk'
    rw [hu.wr, h0]; exact ⟨SCR scr, List.mem_cons_of_mem _ hk.so, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (PublicKey.zeroStores_ok h1 (by rw [h0]; have := hk.nc; omega) hw) fun v hv => ⟨?_, ?_, ?_⟩
  · refine hu.of_frame hv.rd hv.wr hv.sp (fun r _ _ => by rw [hv.gpr]) hv.frame ?_
    intro r hr
    rw [List.mem_singleton.mp hr, h0]
    exact .inr ⟨SCR scr, hk.so, Region.sub_prefix (by decide)⟩
  · have := hv.zero
    rw [h0] at this
    exact PublicKey.stateAt_zero this
  · have f2 := hv.frame
    rw [h0] at f2
    exact f2

theorem zero_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hs : ScrAt n val sc scr) :
    WP isa (zeroState sc) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      stateAt u.mem (State.addr scr) = Spec.Sha3.zero ∧ Frame [⟨State.addr scr, 200⟩] t.mem u.mem := by
  unfold zeroState zeroArgs
  refine WP.seq (WP.mono (hk.setup_ok hc ha (args := [(.r0, .caller sc 0), (.r1, .const 0)]) (stk := [])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨hs.valid (by decide), valid_const (by decide), fun _ h => nomatch h⟩)
    (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hv, _⟩ => ?_)
  have h0 := hv (.r0, .caller sc 0) (by simp)
  have h1 := hv (.r1, .const 0) (by simp)
  simp only [argVal, hs.val, BitVec.add_zero] at h0 h1
  refine WP.mono (hk.zeroStores_step hu h0 h1) fun v ⟨hv, hz, f2⟩ => ⟨hv, hz, ?_⟩
  refine (Frame.sub hm fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans f2
  rw [List.mem_singleton.mp hr]
  intro x hx
  simp only [Region.Contains, List.length_nil, Nat.mul_zero] at hx
  omega

/-! ## `absorb` -/

theorem abs_pre {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hs : ∀ r ∈ kWr scr, Region.Disjoint ⟨State.addr P, N.toNat⟩ r) (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (he : t.sp = E) (h0 : t.gpr .r0 = scr) (h1 : t.gpr .r1 = 136) (h2 : t.gpr .r2 = BitVec.ofNat 32 pos)
    (h3 : t.gpr .r3 = P) (a0 : stackArg t 0 = N) (a1 : stackArg t 1 = scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.absorbArm.pre (t.callEntry.withRegions (absRd E ⟨State.addr P, N.toNat⟩) (kWr scr)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions (absRd E ⟨State.addr P, N.toNat⟩) (kWr scr)) j =
      stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions (absRd E ⟨State.addr P, N.toNat⟩) (kWr scr)) 0 =
      State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.absorbArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, h3, a0, a1, he, hk.scr_addr]
  have wa := hk.args_scr (k := 8) (by decide)
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨rfl, rfl, state_scratch scr, hs _ (by simp [kWr]), hs _ (by simp [kWr]),
    wa _ (by simp [kWr]), wa _ (by simp [kWr]), by have := hk.nc; omega, hfit, hk.scr_fit,
    by have := hk.top; omega, by decide, ?_⟩
  rw [hpn]; exact hp

theorem abs_covers {D : Region} (hcov : DataOk E ins outs D) :
    Covers (absRd E D ++ kWr scr) (ins ++ Whole.FR E :: outs) := by
  refine covers_of fun r hr => ?_
  simp only [absRd, List.cons_append, List.nil_append, List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · exact hcov
  · exact .inl (args_within E (by decide))
  · exact .inr (hk.kWr_covered r hr)

theorem absorb_call (hc : Whole.Ctx E g m₀ ins outs u) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hcov : DataOk E ins outs ⟨State.addr P, N.toNat⟩)
    (hs : ∀ r ∈ kWr scr, Region.Disjoint ⟨State.addr P, N.toNat⟩ r) (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (h0 : u.gpr .r0 = scr) (h1 : u.gpr .r1 = 136) (h2 : u.gpr .r2 = BitVec.ofNat 32 pos)
    (h3 : u.gpr .r3 = P) (a0 : stackArg u 0 = N) (a1 : stackArg u 1 = scr + BitVec.ofNat 32 KSCR) :
    WP isa (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.Arm.Stream.absorb) u fun v =>
      Whole.Ctx E g m₀ ins outs v ∧ Frame (kWr scr) u.mem v.mem ∧
      (∀ msg, Spec.Sha3.Repr u.mem (State.addr scr) 136 msg → pos = msg.length % 136 →
        Spec.Sha3.Repr v.mem (State.addr scr) 136 (msg ++ Spec.Ed448.bytesAt u.mem (State.addr P) N.toNat)) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((pos + N.toNat) % 136) := by
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine Whole.call_ok hc Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1 PublicKey.absorb_noFrames
    (hk.abs_pre hp hs hfit hc.sp h0 h1 h2 h3 a0 a1) (hk.abs_covers hcov) hk.kWr_writes
    fun v hv hf hpost => ⟨hv, hf, ?_, ?_⟩
  · have hp1 := hpost.1
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      stackArg_withRegions] at hp1
    rw [h0, h1, h2, h3, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0, hpn] at hp1
    exact hp1
  · have hp2 := hpost.2
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), stackArg_withRegions] at hp2
    rw [h1, h2, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0, hpn] at hp2
    apply BitVec.eq_of_toNat_eq
    rw [hp2, show BitVec.toNat (136 : BitVec 32) = 136 from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := (pos + N.toNat) % 136) (b := 2 ^ 32)
        (by have := Nat.mod_lt (pos + N.toNat) (by decide : 136 > 0); omega)]

/-- The first absorption, from position 0 of an empty state. -/
theorem first_abs (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {src len : Value} (vs : valid n src) (vl : valid n len)
    (hcov : DataOk E ins outs ⟨State.addr (argVal E val src), (argVal E val len).toNat⟩)
    (hs : ∀ r ∈ kWr scr, Region.Disjoint ⟨State.addr (argVal E val src), (argVal E val len).toNat⟩ r)
    (h8 : (kArgs E 8).Disjoint ⟨State.addr (argVal E val src), (argVal E val len).toNat⟩)
    (hfit : (argVal E val src).toNat + (argVal E val len).toNat ≤ 2 ^ 32)
    (hr : Spec.Sha3.Repr t.mem (State.addr scr) 136 []) :
    WP isa (absorb (firstArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (kArgs E 8 :: kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr scr) 136
        (Spec.Ed448.bytesAt t.mem (State.addr (argVal E val src)) (argVal E val len).toNat) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((argVal E val len).toNat % 136) := by
  unfold absorb firstArgs callWith
  refine WP.seq (WP.mono (hk.setup_ok hc ha
    (args := [(.r0, .caller sc 0), (.r1, .const 136), (.r2, .const 0), (.r3, src)])
    (stk := [len, .caller sc KSCR])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), valid_const (by decide), valid_const (by decide), vs, fun _ h => nomatch h⟩) (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨vl, hsc.valid (by decide), fun _ h => nomatch h⟩))
    fun u ⟨hu, hm, hv, st, _⟩ => ?_)
  rw [args_two] at hm
  have h0 := hv (.r0, .caller sc 0) (by simp)
  have h1 := hv (.r1, .const 136) (by simp)
  have h2 := hv (.r2, .const 0) (by simp)
  have h3 := hv (.r3, src) (by simp)
  have a0 := st 0 (by simp)
  have a1 := st 1 (by simp)
  simp only [argVal, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h1 h2 a1
  simp only [List.getElem_cons_zero] at a0
  have hbytes := bytes_setup hm h8 (by change (argVal E val len).toNat ≤ 2 ^ 64; have := (argVal E val len).isLt; omega)
  refine WP.mono (hk.absorb_call hu (pos := 0) (by decide) hcov hs hfit h0 h1 h2 h3 a0 a1)
    fun v ⟨hv, hf, hrv, h0v⟩ => ⟨hv, ?_, ?_, by rw [h0v, Nat.zero_add]⟩
  · exact (hm.mono fun r hr => by simp at hr ⊢; exact .inl hr).trans
      (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
  · have hrv := hrv [] (repr_frame' hm (hk.state_args (by decide)) hr) rfl
    simp only at hbytes
    rw [List.nil_append, hbytes] at hrv
    exact hrv

/-- An absorption at the position the previous one returned. -/
theorem next_abs (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {src len : Value} (vs : valid n src) (vl : valid n len)
    (hcov : DataOk E ins outs ⟨State.addr (argVal E val src), (argVal E val len).toNat⟩)
    (hs : ∀ r ∈ kWr scr, Region.Disjoint ⟨State.addr (argVal E val src), (argVal E val len).toNat⟩ r)
    (h8 : (kArgs E 8).Disjoint ⟨State.addr (argVal E val src), (argVal E val len).toNat⟩)
    (hfit : (argVal E val src).toNat + (argVal E val len).toNat ≤ 2 ^ 32)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (State.addr scr) 136 msg)
    (hpos : t.gpr .r0 = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (absorb (nextArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (kArgs E 8 :: kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr scr) 136
        (msg ++ Spec.Ed448.bytesAt t.mem (State.addr (argVal E val src)) (argVal E val len).toNat) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((msg.length + (argVal E val len).toNat) % 136) := by
  unfold absorb nextArgs callWith
  refine WP.seq ?_
  refine wp_mov (op2_reg _ _) fun s1 v1 => ?_
  have hc1 : Whole.Ctx E g m₀ ins outs s1 := hc.regs v1.rd v1.wr v1.sp
    (fun r hr _ => v1.other r (by rintro rfl; simp [preserved] at hr)) v1.mem
  refine WP.mono (hk.setup_ok hc1 ha
    (args := [(.r0, .caller sc 0), (.r1, .const 136), (.r3, src)]) (stk := [len, .caller sc KSCR])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), valid_const (by decide), vs, fun _ h => nomatch h⟩) (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨vl, hsc.valid (by decide), fun _ h => nomatch h⟩))
    fun u ⟨hu, hm, hv, st, hk'⟩ => ?_
  rw [args_two] at hm
  have h0 := hv (.r0, .caller sc 0) (by simp)
  have h1 := hv (.r1, .const 136) (by simp)
  have h3 := hv (.r3, src) (by simp)
  have a0 := st 0 (by simp)
  have a1 := st 1 (by simp)
  simp only [argVal, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h1 a1
  simp only [List.getElem_cons_zero] at a0
  have h2 : u.gpr .r2 = BitVec.ofNat 32 (msg.length % 136) := by
    rw [hk' .r2 (by simp) (by decide) (by decide), v1.gpr, hpos]
  have hrd : Spec.Sha3.Repr u.mem (State.addr scr) 136 msg := repr_frame' hm (hk.state_args (by decide)) (by
    unfold Spec.Sha3.Repr at hr ⊢; rw [v1.mem]; exact hr)
  have hbytes := bytes_setup hm h8 (by change (argVal E val len).toNat ≤ 2 ^ 64; have := (argVal E val len).isLt; omega)
  refine WP.mono (hk.absorb_call hu (Nat.mod_lt _ (by decide)) hcov hs hfit h0 h1 h2 h3 a0 a1)
    fun v ⟨hv, hf, hrv, h0v⟩ => ⟨hv, ?_, ?_, ?_⟩
  · rw [v1.mem] at hm
    exact (hm.mono fun r hr => by simp at hr ⊢; exact .inl hr).trans
      (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
  · have hrv := hrv msg hrd rfl
    simp only at hbytes
    rw [hbytes, v1.mem] at hrv
    exact hrv
  · rw [h0v, Nat.mod_add_mod]

/-- The first absorption, of `N` bytes at `P`. -/
theorem firstAt (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {src len : Value} (vs : valid n src) (vl : valid n len) {P : BitVec 32} {N : Nat}
    (hP : argVal E val src = P) (hN : (argVal E val len).toNat = N)
    (hcov : DataOk E ins outs ⟨State.addr P, N⟩) (hs : ∀ r ∈ kWr scr, Region.Disjoint ⟨State.addr P, N⟩ r)
    (h8 : (kArgs E 8).Disjoint ⟨State.addr P, N⟩) (hfit : P.toNat + N ≤ 2 ^ 32)
    (hr : Spec.Sha3.Repr t.mem (State.addr scr) 136 []) :
    WP isa (absorb (firstArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (kArgs E 8 :: kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr scr) 136 (Spec.Ed448.bytesAt t.mem (State.addr P) N) ∧
      v.gpr .r0 = BitVec.ofNat 32 (N % 136) := by
  have h := hk.first_abs hc ha hsc vs vl (by rw [hP, hN]; exact hcov) (by rw [hP, hN]; exact hs)
    (by rw [hP, hN]; exact h8) (by rw [hP, hN]; exact hfit) hr
  rw [hP, hN] at h
  exact h

/-- An absorption of `N` bytes at `P`, at the position the previous one returned. -/
theorem nextAt (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {src len : Value} (vs : valid n src) (vl : valid n len) {P : BitVec 32} {N : Nat}
    (hP : argVal E val src = P) (hN : (argVal E val len).toNat = N)
    (hcov : DataOk E ins outs ⟨State.addr P, N⟩) (hs : ∀ r ∈ kWr scr, Region.Disjoint ⟨State.addr P, N⟩ r)
    (h8 : (kArgs E 8).Disjoint ⟨State.addr P, N⟩) (hfit : P.toNat + N ≤ 2 ^ 32)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (State.addr scr) 136 msg)
    (hpos : t.gpr .r0 = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (absorb (nextArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (kArgs E 8 :: kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr scr) 136 (msg ++ Spec.Ed448.bytesAt t.mem (State.addr P) N) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((msg ++ Spec.Ed448.bytesAt t.mem (State.addr P) N).length % 136) := by
  have h := hk.next_abs hc ha hsc vs vl (by rw [hP, hN]; exact hcov) (by rw [hP, hN]; exact hs)
    (by rw [hP, hN]; exact h8) (by rw [hP, hN]; exact hfit) hr hpos
  rw [hP, hN] at h
  refine WP.mono h fun v ⟨hv, hf, hrv, h0⟩ => ⟨hv, hf, hrv, ?_⟩
  rw [h0]
  simp [Spec.Ed448.bytesAt]

/-! ## `pad` -/

theorem pad_pre {pos : Nat} (hp : pos < 136) (he : t.sp = E) (h0 : t.gpr .r0 = scr)
    (h1 : t.gpr .r1 = 136) (h2 : t.gpr .r2 = BitVec.ofNat 32 pos) (a0 : stackArg t 0 = scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.padArm.pre (t.callEntry.withRegions [kArgs E 4] (kWr scr)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions [kArgs E 4] (kWr scr)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions [kArgs E 4] (kWr scr)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.padArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, a0, he, hk.scr_addr]
  have wa := hk.args_scr (k := 4) (by decide)
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨rfl, rfl, state_scratch scr, wa _ (by simp [kWr]), wa _ (by simp [kWr]),
    by have := hk.nc; omega, hk.scr_fit, by have := hk.top; omega, by decide, ?_⟩
  rw [hpn]; exact hp

theorem pad_covers : Covers ([kArgs E 4] ++ kWr scr) (ins ++ Whole.FR E :: outs) := by
  refine covers_of fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]; exact .inl (args_within E (by decide))
  · exact .inr (hk.kWr_covered r hr)

theorem pad_step (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (State.addr scr) 136 msg)
    (hpos : t.gpr .r0 = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (pad sc) t fun v => Whole.Ctx E g m₀ ins outs v ∧ Frame (kArgs E 8 :: kWr scr) t.mem v.mem ∧
      stateAt v.mem (State.addr scr) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  unfold pad callWith padArgs
  refine WP.seq ?_
  refine wp_mov (op2_reg _ _) fun s1 v1 => ?_
  have hc1 : Whole.Ctx E g m₀ ins outs s1 := hc.regs v1.rd v1.wr v1.sp
    (fun r hr _ => v1.other r (by rintro rfl; simp [preserved] at hr)) v1.mem
  refine WP.mono (hk.setup_ok hc1 ha
    (args := [(.r0, .caller sc 0), (.r1, .const 136), (.r3, .const 0x1f)]) (stk := [.caller sc KSCR])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), valid_const (by decide), valid_const (by decide), fun _ h => nomatch h⟩) (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), fun _ h => nomatch h⟩))
    fun u ⟨hu, hm, hv, st, hk'⟩ => ?_
  have h0 := hv (.r0, .caller sc 0) (by simp)
  have h1 := hv (.r1, .const 136) (by simp)
  have h3 := hv (.r3, .const 0x1f) (by simp)
  have a0 := st 0 (by simp)
  simp only [argVal, hsc.val, List.getElem_cons_zero, BitVec.add_zero] at h0 h1 h3 a0
  have h2 : u.gpr .r2 = BitVec.ofNat 32 (msg.length % 136) := by
    rw [hk' .r2 (by simp) (by decide) (by decide), v1.gpr, hpos]
  have hrd : Spec.Sha3.Repr u.mem (State.addr scr) 136 msg := repr_frame' hm (hk.state_args (by simp)) (by
    unfold Spec.Sha3.Repr at hr ⊢; rw [v1.mem]; exact hr)
  have hpn : (BitVec.ofNat 32 (msg.length % 136)).toNat = msg.length % 136 := by
    rw [BitVec.toNat_ofNat]; have := Nat.mod_lt msg.length (by decide : 136 > 0); omega
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Pad.pad_verified.1 PublicKey.pad_noFrames
    (hk.pad_pre (Nat.mod_lt _ (by decide)) hu.sp h0 h1 h2 a0) hk.pad_covers hk.kWr_writes
    fun v hv hf hp => ⟨hv, ?_, ?_⟩
  · rw [v1.mem] at hm
    refine (Frame.sub hm fun r hr => ⟨kArgs E 8, List.mem_cons_self, ?_⟩).trans
      (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
    rw [List.mem_singleton.mp hr]
    exact Region.sub_prefix (by simp)
  · simp only [Proof.Sha3.padArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs)] at hp
    rw [h0, h1, h2, h3, hpn] at hp
    exact hp msg hrd rfl

/-! ## `squeeze` -/

theorem sqz_pre {d : Nat} (h8 : 8 ≤ d) (hd : d + 114 ≤ 248) (he : t.sp = E) (h0 : t.gpr .r0 = scr)
    (h1 : t.gpr .r1 = 136) (h2 : t.gpr .r2 = 0) (h3 : t.gpr .r3 = E + BitVec.ofNat 32 d)
    (a0 : stackArg t 0 = 114) (a1 : stackArg t 1 = scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.squeezeArm.pre (t.callEntry.withRegions [kArgs E 8] (sqzWr E scr d)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions [kArgs E 8] (sqzWr E scr d)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions [kArgs E 8] (sqzWr E scr d)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.squeezeArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, h3, a0, a1, he, hk.scr_addr, hk.frame_addr (by omega)]
  have wa := hk.args_scr (k := 8) (by decide)
  have so := hk.frame_kWr (d := d) (l := 114) (by omega)
  have ht := hk.top
  refine ⟨rfl, rfl, (so _ (by simp [kWr])).symm, state_scratch scr, so _ (by simp [kWr]),
    wa _ (by simp [kWr]), Offset.base_disjoint _ h8 (by omega), wa _ (by simp [kWr]),
    by have := hk.nc; omega, hk.frame_fit hd, hk.scr_fit, by omega, by decide, by decide⟩

theorem sqz_writes {d : Nat} (hd : d + 114 ≤ 248) :
    ∀ r ∈ sqzWr E scr d, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R := by
  intro r hr
  simp only [sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.kWr_writes _ (by simp [kWr])
  · exact .inl (frame_within E hd)
  · exact hk.kWr_writes _ (by simp [kWr])

theorem sqz_covers {d : Nat} (hd : d + 114 ≤ 248) :
    Covers ([kArgs E 8] ++ sqzWr E scr d) (ins ++ Whole.FR E :: outs) := by
  refine covers_of fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]; exact .inl (args_within E (by decide))
  · rcases hk.sqz_writes hd r hr with h | ⟨R, hR, h⟩
    · exact .inl h
    · exact .inr ⟨R, List.mem_append_right _ hR, h⟩

theorem sqz_step (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {d : Nat} (h8 : 8 ≤ d) (hd : d + 114 ≤ 248) :
    WP isa (squeeze sc d) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (kArgs E 8 :: sqzWr E scr d) t.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem (State.addr E + BitVec.ofNat 64 d) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem (State.addr scr)) 0 114 := by
  unfold squeeze callWith sqzArgs
  refine WP.seq (WP.mono (hk.setup_ok hc ha
    (args := [(.r0, .caller sc 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame d)])
    (stk := [.const 114, .caller sc KSCR])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), valid_const (by decide), valid_const (by decide), valid_frame (by omega), fun _ h => nomatch h⟩) (by simp [preserved])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨valid_const (by decide), hsc.valid (by decide), fun _ h => nomatch h⟩))
    fun u ⟨hu, hm, hv, st, _⟩ => ?_)
  rw [args_two] at hm
  have h0 := hv (.r0, .caller sc 0) (by simp)
  have h1 := hv (.r1, .const 136) (by simp)
  have h2 := hv (.r2, .const 0) (by simp)
  have h3 := hv (.r3, .frame d) (by simp)
  have a0 := st 0 (by simp)
  have a1 := st 1 (by simp)
  simp only [argVal, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 PublicKey.squeeze_noFrames
    (hk.sqz_pre h8 hd hu.sp h0 h1 h2 h3 a0 a1) (hk.sqz_covers hd) (hk.sqz_writes hd)
    fun v hv hf hp => ⟨hv, ?_, ?_⟩
  · exact (hm.mono fun r hr => by simp at hr ⊢; exact .inl hr).trans
      (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
  · have hp1 := hp.1
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      stackArg_withRegions] at hp1
    rw [h0, h1, h2, h3, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0, hk.frame_addr (by omega),
      state_frame hm (hk.state_args (by decide))] at hp1
    exact hp1

end Kit

end VG.Proof.Ed448.Arm.Shake
