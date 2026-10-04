import VerifiedGarbage.Proof.Ed448.Arm.Verify.Header
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash

/-!
# Ed448 verification on ARMv7: the calls of the sponge functions

Each call through `Whole.call_ok` with its own contract
(`Proof.Sha3.absorbArm`, `padArm`, `squeezeArm`), from its arguments in
registers and on the stack (`abs_call`, `pad_call`, `sqz_call`), and with
their set-up (`hdr_abs`, `next_abs`, `pad_step`, `sqz_step`). An absorption
reads its data from the frame or from an input (`DataOk`); each after the
first starts at the position the previous one returned in `r0`.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Spec.Sha3 (stateAt)
open VG.Proof.X25519.Arm (Upd wp_mov op2_reg)
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR Whole.call_ok)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t u : State}

/-! ## The regions -/

/-- The state and the sponge functions' working space. -/
def kWr (L : Lay) : List Region :=
  [⟨State.addr L.scr, 200⟩, ⟨State.addr L.scr + BitVec.ofNat 64 KSCR, 640⟩]

def kArgs (L : Lay) (n : Nat) : Region := ⟨State.addr L.E, n⟩

theorem scr_addr (hL : L.Ok) : State.addr (L.scr + BitVec.ofNat 32 KSCR) = State.addr L.scr + BitVec.ofNat 64 KSCR :=
  addr_add (by have := hL.nc; simp only [KSCR]; omega)

theorem scr_fit (hL : L.Ok) : (L.scr + BitVec.ofNat 32 KSCR).toNat + 640 ≤ 2 ^ 32 := by
  have := hL.nc
  rw [BitVec.toNat_add_of_lt (by change L.scr.toNat + 208 < 2 ^ 32; omega)]
  change L.scr.toNat + 208 + 640 ≤ 2 ^ 32
  omega

theorem frame_addr (hL : L.Ok) {d : Nat} (hd : d < 292) :
    State.addr (L.E + BitVec.ofNat 32 d) = State.addr L.E + BitVec.ofNat 64 d :=
  addr_add (by have := hL.top; omega)

theorem frame_fit (hL : L.Ok) {d n : Nat} (hd : d + n ≤ 248) :
    (L.E + BitVec.ofNat 32 d).toNat + n ≤ 2 ^ 32 := by
  have ht := hL.top
  rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem kWr_sub (L : Lay) : ∀ r ∈ kWr L, Whole.Within r L.SCR := by
  intro r hr
  simp only [kWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨0, (BitVec.add_zero _).symm, by change 0 + 200 ≤ 8192; decide⟩
  · exact ⟨KSCR, rfl, by change 208 + 640 ≤ 8192; decide⟩

theorem kWr_writes (L : Lay) : ∀ r ∈ kWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨L.SCR, by simp [Lay.outputs], kWr_sub L r hr⟩

theorem state_scratch (L : Lay) : (⟨State.addr L.scr, 200⟩ : Region).Disjoint
    ⟨State.addr L.scr + BitVec.ofNat 64 KSCR, 640⟩ := Offset.base_disjoint _ (by decide) (by decide)

theorem args_scr (hL : L.Ok) {n : Nat} (hn : n ≤ 280) : ∀ r ∈ kWr L, (kArgs L n).Disjoint r :=
  fun r hr => (hL.kc.sub_left (Region.sub_prefix hn)).sub_right (kWr_sub L r hr).sub

/-- Data an absorption may read: in the frame, or in an input. -/
def DataOk (L : Lay) (D : Region) : Prop := Whole.Within D L.FR ∨ ∃ R ∈ L.inputs, Whole.Within D R

theorem data_input (hL : L.Ok) {D R : Region} (hR : R ∈ L.inputs) (hw : Whole.Within D R) :
    (∀ r ∈ kWr L, D.Disjoint r) ∧ (kArgs L 8).Disjoint D := by
  have ho := hL.inputs_out hR
  refine ⟨fun r hr => ((ho L.SCR (by simp [Lay.outputs])).sub_left hw.sub).sub_right (kWr_sub L r hr).sub, ?_⟩
  exact ((ho L.FR (by simp)).sub_left hw.sub).symm.sub_left (Region.sub_prefix (by decide))

theorem data_frame (hL : L.Ok) {d n : Nat} (h8 : 8 ≤ d) (hd : d + n ≤ 248) :
    (∀ r ∈ kWr L, Region.Disjoint ⟨State.addr L.E + BitVec.ofNat 64 d, n⟩ r) ∧
      (kArgs L 8).Disjoint ⟨State.addr L.E + BitVec.ofNat 64 d, n⟩ :=
  ⟨fun r hr => (hL.kc.sub_left (Offset.sub_base _ (by omega))).sub_right (kWr_sub L r hr).sub,
    Offset.base_disjoint _ h8 (by omega)⟩

theorem covers_of {rs : List Region} (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R) :
    Covers rs (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases h r hr with hf | ⟨R, hR, hw⟩
  · exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, hf⟩
  · refine ⟨R, ?_, hw⟩
    rcases List.mem_append.mp hR with hi | ho
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)

theorem args_within (L : Lay) {n : Nat} (hn : n ≤ 248) : Whole.Within (kArgs L n) L.FR :=
  ⟨0, (BitVec.add_zero _).symm, by change 0 + n ≤ 248; omega⟩

theorem kWr_covered (L : Lay) : ∀ r ∈ kWr L, ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  fun r hr => ⟨L.SCR, by simp [Lay.outputs], kWr_sub L r hr⟩

/-! ## `absorb` -/

def absRd (L : Lay) (D : Region) : List Region := [D, kArgs L 8]

theorem abs_pre (hL : L.Ok) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hs : ∀ r ∈ kWr L, Region.Disjoint ⟨State.addr P, N.toNat⟩ r) (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (he : t.sp = L.E) (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 136) (h2 : t.gpr .r2 = BitVec.ofNat 32 pos)
    (h3 : t.gpr .r3 = P) (a0 : stackArg t 0 = N) (a1 : stackArg t 1 = L.scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.absorbArm.pre (t.callEntry.withRegions (absRd L ⟨State.addr P, N.toNat⟩) (kWr L)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions (absRd L ⟨State.addr P, N.toNat⟩) (kWr L)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions (absRd L ⟨State.addr P, N.toNat⟩) (kWr L)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.absorbArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, h3, a0, a1, he, scr_addr hL]
  have wa := args_scr hL (n := 8) (by decide)
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨rfl, rfl, state_scratch L, hs _ (by simp [kWr]), hs _ (by simp [kWr]),
    wa _ (by simp [kWr]), wa _ (by simp [kWr]), by have := hL.nc; omega, hfit, scr_fit hL,
    by have := hL.top; omega, by decide, ?_⟩
  rw [hpn]; exact hp

theorem abs_covers {P N : BitVec 32} (hcov : DataOk L ⟨State.addr P, N.toNat⟩) :
    Covers (absRd L ⟨State.addr P, N.toNat⟩ ++ kWr L) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine covers_of fun r hr => ?_
  simp only [absRd, List.cons_append, List.nil_append, List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · rcases hcov with h | ⟨R, hR, h⟩
    · exact .inl h
    · exact .inr ⟨R, List.mem_append_left _ hR, h⟩
  · exact .inl (args_within L (by decide))
  · exact .inr (kWr_covered L r hr)

theorem absorb_call (hc : Ctx L g m₀ u) (hL : L.Ok) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hcov : DataOk L ⟨State.addr P, N.toNat⟩) (hs : ∀ r ∈ kWr L, Region.Disjoint ⟨State.addr P, N.toNat⟩ r)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (h0 : u.gpr .r0 = L.scr) (h1 : u.gpr .r1 = 136) (h2 : u.gpr .r2 = BitVec.ofNat 32 pos)
    (h3 : u.gpr .r3 = P) (a0 : stackArg u 0 = N) (a1 : stackArg u 1 = L.scr + BitVec.ofNat 32 KSCR) :
    WP isa (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.Arm.Stream.absorb) u fun v => Ctx L g m₀ v ∧
      (∀ msg, Spec.Sha3.Repr u.mem (State.addr L.scr) 136 msg → pos = msg.length % 136 →
        Spec.Sha3.Repr v.mem (State.addr L.scr) 136 (msg ++ Spec.Ed448.bytesAt u.mem (State.addr P) N.toNat)) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((pos + N.toNat) % 136) := by
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine Whole.call_ok hc Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1 PublicKey.absorb_noFrames
    (abs_pre hL hp hs hfit hc.sp h0 h1 h2 h3 a0 a1) (abs_covers hcov) (kWr_writes L) fun v hv _ hpost => ⟨hv, ?_, ?_⟩
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

/-- The state, through a set-up (which writes only the frame's first 24 bytes). -/
theorem state_setup (hL : L.Ok) {m m' : Mem} (hm : Frame [⟨State.addr L.E, 24⟩] m m') :
    stateAt m' (State.addr L.scr) = stateAt m (State.addr L.scr) := by
  refine Proof.Sha3.stateAt_congr fun j hj => ?_
  refine hm.bytes (R := ⟨State.addr L.scr, 200⟩) ?_ (by change 200 ≤ 2 ^ 64; decide) hj
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact ((hL.kc.sub_left (Region.sub_prefix (by decide : 24 ≤ 280))).sub_right
    (Region.sub_prefix (by decide))).symm

theorem repr_setup (hL : L.Ok) {m m' : Mem} (hm : Frame [⟨State.addr L.E, 24⟩] m m') {msg : List Byte}
    (h : Spec.Sha3.Repr m (State.addr L.scr) 136 msg) : Spec.Sha3.Repr m' (State.addr L.scr) 136 msg := by
  unfold Spec.Sha3.Repr at h ⊢
  rw [state_setup hL hm]; exact h

theorem bytes_setup {m m' : Mem} (hm : Frame [⟨State.addr L.E, 24⟩] m m') {D : Region}
    (hd : (⟨State.addr L.E, 24⟩ : Region).Disjoint D) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' D.base D.len = Spec.Ed448.bytesAt m D.base D.len := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hm.bytes (R := D) ?_ hn (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact hd.symm

theorem Ctx.within_bytes (hc : Ctx L g m₀ t) (hL : L.Ok) {D R : Region} (hR : R ∈ L.inputs)
    (hw : Whole.Within D R) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt t.mem D.base D.len = Spec.Ed448.bytesAt m₀ D.base D.len := by
  unfold Spec.Ed448.bytesAt
  exact List.map_congr_left fun i hi =>
    hc.frame.bytes (R := D) (fun r hr => (hL.inputs_out hR r hr).sub_left hw.sub) hn (List.mem_range.mp hi)

/-- The header absorbed, from position 0 of an empty state. -/
theorem hdr_abs (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hr : Spec.Sha3.Repr t.mem (State.addr L.scr) 136 [])
    (hh : Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L) :
    WP isa (absorb hdrArgs) t fun v => Ctx L g m₀ v ∧
      Spec.Sha3.Repr v.mem (State.addr L.scr) 136 (hdrBytes L) ∧ v.gpr .r0 = BitVec.ofNat 32 10 := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.r0, scr 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame HDR)]) (stk := [.const 10, scr KSCR])
    (by decide) (by simp [valid, scr, Slot, HDR]) (by simp [preserved]) (by decide) (by simp [valid, scr, Slot, KSCR]))
    fun u ⟨hu, hm, hs, st, _⟩ => ?_)
  have h0 := hs (.r0, scr 0) (by simp)
  have h1 := hs (.r1, .const 136) (by simp)
  have h2 := hs (.r2, .const 0) (by simp)
  have h3 := hs (.r3, .frame HDR) (by simp)
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  simp only [argValue, scr, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  have hpd : State.addr (L.E + BitVec.ofNat 32 HDR) = State.addr L.E + BitVec.ofNat 64 HDR := frame_addr hL (by decide)
  have hN : (BitVec.ofNat 32 10).toNat = 10 := rfl
  obtain ⟨ds, _⟩ := data_frame hL (d := HDR) (n := 10) (by decide) (by decide)
  refine WP.mono (absorb_call hu hL (pos := 0) (by decide) (P := L.E + BitVec.ofNat 32 HDR)
      (N := BitVec.ofNat 32 10)
      (by rw [hpd, hN]; exact .inl ⟨HDR, rfl, by change 24 + 10 ≤ 248; decide⟩) (by rw [hpd, hN]; exact ds)
      (by rw [hN]; exact frame_fit hL (by decide)) h0 h1 h2 h3 a0 a1)
    fun v ⟨hv, hrv, h0v⟩ => ⟨hv, ?_, h0v⟩
  have hrv := hrv [] (repr_setup hL hm hr) rfl
  rw [hpd, hN, List.nil_append] at hrv
  rw [← hh]
  have := bytes_setup hm (D := ⟨State.addr L.E + BitVec.ofNat 64 HDR, 10⟩)
    (Offset.base_disjoint _ (by decide) (by decide)) (by change 10 ≤ 2 ^ 64; decide)
  rw [← this]; exact hrv

/-- An absorption at the position the previous one returned, of data in an input. -/
theorem next_abs (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) {src len : Value}
    (vs : valid src) (vl : valid len) {R : Region} (hR : R ∈ L.inputs)
    (hw : Whole.Within ⟨State.addr (argValue L src), (argValue L len).toNat⟩ R)
    (hfit : (argValue L src).toNat + (argValue L len).toNat ≤ 2 ^ 32)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (State.addr L.scr) 136 msg)
    (hpos : t.gpr .r0 = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (absorb (nextArgs src len)) t fun v => Ctx L g m₀ v ∧
      Spec.Sha3.Repr v.mem (State.addr L.scr) 136
        (msg ++ Spec.Ed448.bytesAt m₀ (State.addr (argValue L src)) (argValue L len).toNat) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((msg.length + (argValue L len).toNat) % 136) := by
  unfold absorb nextArgs
  refine WP.seq ?_
  refine wp_mov (op2_reg _ _) fun s1 v1 => ?_
  have hc1 : Ctx L g m₀ s1 := hc.regs v1.rd v1.wr v1.sp
    (fun r hr _ => v1.other r (by rintro rfl; simp [preserved] at hr)) v1.mem
  refine WP.mono (setup_ok hc1 hL ha
    (args := [(.r0, scr 0), (.r1, .const 136), (.r3, src)]) (stk := [len, scr KSCR])
    (by simp)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨.inr rfl, by decide⟩
      · show 136 < 65536; decide
      · exact vs)
    (by simp [preserved]) (by simp)
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact vl
      · exact ⟨.inr rfl, by decide⟩))
    fun u ⟨hu, hm, hs, st, hk⟩ => ?_
  have h0 := hs (.r0, scr 0) (by simp)
  have h1 := hs (.r1, .const 136) (by simp)
  have h3 := hs (.r3, src) (by simp)
  have a0 := st 0 (by simp)
  have a1 := st 1 (by simp)
  simp only [argValue, scr, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h1 a1
  simp only [List.getElem_cons_zero] at a0
  have h2 : u.gpr .r2 = BitVec.ofNat 32 (msg.length % 136) := by
    rw [hk .r2 (by simp) (by decide) (by decide), v1.gpr, hpos]
  obtain ⟨ds, _⟩ := data_input hL hR hw
  have hrd : Spec.Sha3.Repr u.mem (State.addr L.scr) 136 msg := repr_setup hL hm (by
    unfold Spec.Sha3.Repr at hr ⊢; rw [v1.mem]; exact hr)
  refine WP.mono (absorb_call hu hL (Nat.mod_lt _ (by decide)) (.inr ⟨R, hR, hw⟩) ds hfit
      h0 h1 h2 h3 a0 a1) fun v ⟨hv, hrv, h0v⟩ => ⟨hv, ?_, ?_⟩
  · have hrv := hrv msg hrd rfl
    rwa [hu.within_bytes hL hR hw (by change (argValue L len).toNat ≤ 2 ^ 64; have := (argValue L len).isLt; omega)] at hrv
  · rw [h0v, Nat.mod_add_mod]

/-! ## `pad` -/

theorem pad_pre (hL : L.Ok) {pos : Nat} (hp : pos < 136) (he : t.sp = L.E) (h0 : t.gpr .r0 = L.scr)
    (h1 : t.gpr .r1 = 136) (h2 : t.gpr .r2 = BitVec.ofNat 32 pos) (a0 : stackArg t 0 = L.scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.padArm.pre (t.callEntry.withRegions [kArgs L 4] (kWr L)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions [kArgs L 4] (kWr L)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions [kArgs L 4] (kWr L)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.padArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, a0, he, scr_addr hL]
  have wa := args_scr hL (n := 4) (by decide)
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨rfl, rfl, state_scratch L, wa _ (by simp [kWr]), wa _ (by simp [kWr]),
    by have := hL.nc; omega, scr_fit hL, by have := hL.top; omega, by decide, ?_⟩
  rw [hpn]; exact hp

theorem pad_covers (L : Lay) : Covers ([kArgs L 4] ++ kWr L) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine covers_of fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]; exact .inl (args_within L (by decide))
  · exact .inr (kWr_covered L r hr)

theorem pad_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) {msg : List Byte}
    (hr : Spec.Sha3.Repr t.mem (State.addr L.scr) 136 msg)
    (hpos : t.gpr .r0 = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (callWith padArgs Spec.Sha3.padScratchApi.name Impl.Sha3.Arm.Stream.pad) t fun v =>
      Ctx L g m₀ v ∧ stateAt v.mem (State.addr L.scr) =
        Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  unfold callWith padArgs
  refine WP.seq ?_
  refine wp_mov (op2_reg _ _) fun s1 v1 => ?_
  have hc1 : Ctx L g m₀ s1 := hc.regs v1.rd v1.wr v1.sp
    (fun r hr _ => v1.other r (by rintro rfl; simp [preserved] at hr)) v1.mem
  refine WP.mono (setup_ok hc1 hL ha
    (args := [(.r0, scr 0), (.r1, .const 136), (.r3, .const 0x1f)]) (stk := [scr KSCR])
    (by decide) (by simp [valid, scr, Slot]) (by simp [preserved]) (by decide) (by simp [valid, scr, Slot, KSCR]))
    fun u ⟨hu, hm, hs, st, hk⟩ => ?_
  have h0 := hs (.r0, scr 0) (by simp)
  have h1 := hs (.r1, .const 136) (by simp)
  have h3 := hs (.r3, .const 0x1f) (by simp)
  have a0 := st 0 (by decide)
  simp only [argValue, scr, Lay.value, List.getElem_cons_zero, BitVec.add_zero] at h0 h1 h3 a0
  have h2 : u.gpr .r2 = BitVec.ofNat 32 (msg.length % 136) := by
    rw [hk .r2 (by simp) (by decide) (by decide), v1.gpr, hpos]
  have hrd : Spec.Sha3.Repr u.mem (State.addr L.scr) 136 msg := repr_setup hL hm (by
    unfold Spec.Sha3.Repr at hr ⊢; rw [v1.mem]; exact hr)
  have hpn : (BitVec.ofNat 32 (msg.length % 136)).toNat = msg.length % 136 := by
    rw [BitVec.toNat_ofNat]; have := Nat.mod_lt msg.length (by decide : 136 > 0); omega
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Pad.pad_verified.1 PublicKey.pad_noFrames
    (pad_pre hL (Nat.mod_lt _ (by decide)) hu.sp h0 h1 h2 a0) (pad_covers L) (kWr_writes L)
    fun v hv _ hp => ⟨hv, ?_⟩
  simp only [Proof.Sha3.padArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs)] at hp
  rw [h0, h1, h2, h3, hpn] at hp
  exact hp msg hrd rfl

/-! ## `squeeze` -/

def sqzWr (L : Lay) : List Region :=
  [⟨State.addr L.scr, 200⟩, ⟨State.addr L.E + BitVec.ofNat 64 HASH, 114⟩,
    ⟨State.addr L.scr + BitVec.ofNat 64 KSCR, 640⟩]

theorem out_sub (L : Lay) : Whole.Within ⟨State.addr L.E + BitVec.ofNat 64 HASH, 114⟩ L.FR :=
  ⟨HASH, rfl, by change 40 + 114 ≤ 248; decide⟩

theorem sqz_pre (hL : L.Ok) (he : t.sp = L.E) (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 136)
    (h2 : t.gpr .r2 = 0) (h3 : t.gpr .r3 = L.E + BitVec.ofNat 32 HASH) (a0 : stackArg t 0 = 114)
    (a1 : stackArg t 1 = L.scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.squeezeArm.pre (t.callEntry.withRegions [kArgs L 8] (sqzWr L)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions [kArgs L 8] (sqzWr L)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions [kArgs L 8] (sqzWr L)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.squeezeArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, h3, a0, a1, he, scr_addr hL, frame_addr hL (by decide)]
  have wa := args_scr hL (n := 8) (by decide)
  obtain ⟨so, _⟩ := data_frame hL (d := HASH) (n := 114) (by decide) (by decide)
  have ht := hL.top
  refine ⟨rfl, rfl, (so _ (by simp [kWr])).symm, state_scratch L, so _ (by simp [kWr]),
    wa _ (by simp [kWr]), Offset.base_disjoint _ (by decide) (by decide), wa _ (by simp [kWr]),
    by have := hL.nc; omega, frame_fit hL (by decide), scr_fit hL, by omega, by decide, by decide⟩

theorem sqz_writes (L : Lay) : ∀ r ∈ sqzWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact kWr_writes L _ (by simp [kWr])
  · exact .inl (out_sub L)
  · exact kWr_writes L _ (by simp [kWr])

theorem sqz_covers (L : Lay) : Covers ([kArgs L 8] ++ sqzWr L) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine covers_of fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]; exact .inl (args_within L (by decide))
  · rcases sqz_writes L r hr with h | ⟨R, hR, h⟩
    · exact .inl h
    · exact .inr ⟨R, List.mem_append_right _ hR, h⟩

theorem sqz_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith squeezeArgs Spec.Sha3.squeezeScratchApi.name Impl.Sha3.Arm.Stream.squeeze) t fun v =>
      Ctx L g m₀ v ∧ Spec.Ed448.bytesAt v.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem (State.addr L.scr)) 0 114 := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.r0, scr 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame HASH)]) (stk := [.const 114, scr KSCR])
    (by decide) (by simp [valid, scr, Slot, HASH]) (by simp [preserved]) (by decide) (by simp [valid, scr, Slot, KSCR]))
    fun u ⟨hu, hm, hs, st, _⟩ => ?_)
  have h0 := hs (.r0, scr 0) (by simp)
  have h1 := hs (.r1, .const 136) (by simp)
  have h2 := hs (.r2, .const 0) (by simp)
  have h3 := hs (.r3, .frame HASH) (by simp)
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  simp only [argValue, scr, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 PublicKey.squeeze_noFrames
    (sqz_pre hL hu.sp h0 h1 h2 h3 a0 a1) (sqz_covers L) (sqz_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  have hp1 := hp.1
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    stackArg_withRegions] at hp1
  rw [h0, h1, h2, h3, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0, frame_addr hL (by decide)] at hp1
  rw [state_setup hL hm] at hp1
  exact hp1

end VG.Proof.Ed448.Arm.Verify
