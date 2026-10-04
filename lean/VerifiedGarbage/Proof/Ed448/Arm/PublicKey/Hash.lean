import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Layout
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha512.Arm.Word64

/-!
# Ed448 public-key derivation on ARMv7: `SHAKE256(seed, 114)`

The Keccak state at `scratch` zeroed (`zero_ok`), and the calls of
`vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch` (rate 136),
each through `Whole.call_ok` with its own contract (`Proof.Sha3.absorbArm`,
…): `hash_ok` leaves `SHAKE256(seed, 114)` in the frame at `HASH`.
-/

namespace VG.Proof.Ed448.Arm.PublicKey

open VG VG.Arm VG.Impl.Ed448.Arm.PublicKey VG.Impl.Ed25519.Arm.Whole
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR Whole.valid Whole.call_ok)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-! ## The state, zeroed -/

/-- After zeroing the first `k` words of the state at `r0`. -/
structure ZInv (s₁ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp
  frame : Frame [⟨State.addr (s₁.gpr .r0), 200⟩] s₁.mem s.mem
  zero : ∀ j < k, s.mem.readW (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32 = 0

theorem zeroStores_ok {s₁ : State} (h1 : s₁.gpr .r1 = 0) (hfit : (s₁.gpr .r0).toNat + 200 ≤ 2 ^ 32)
    (hwr : ∀ k < 50, InRegions s₁.wr (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block zeroStores) s₁ (ZInv s₁ 50) := by
  rw [zeroStores, List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa) (ZInv s₁) (fun k s hk h => ?_) 50 (Nat.le_refl _) s₁
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * k)) =
      State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (4 * k) := by
    rw [h.gpr, addr_add (by omega)]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_str (by omega) (by rw [ea, h.wr]; exact hwr k hk), runStep_some, runBlock_nil]
  refine ⟨_, rfl, h.gpr, h.rd, h.wr, h.sp, ?_, fun j hj => ?_⟩
  · rw [ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · show (s.mem.writeW _ _).readW _ _ = _
    rw [ea, h.gpr, h1]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.zero j (by omega)

theorem stateAt_zero {m : Mem} {p : Addr} (h : ∀ j < 50, m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Spec.Sha3.zero, Vector.getElem_replicate]
  rw [VG.Proof.Sha512.Arm.readW64, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, Offset.add_add,
    show 8 * i + 4 = 4 * (2 * i + 1) by omega, show 8 * i = 4 * (2 * i) by omega,
    h _ (by omega), h _ (by omega)]
  rfl

/-- The stores, from `scratch` in `r0` and `0` in `r1`. -/
theorem zeroStores_step (hu : Ctx L g m₀ t) (hL : L.Ok) (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 0) :
    WP isa (.block zeroStores) t fun u =>
      Ctx L g m₀ u ∧ stateAt u.mem (State.addr L.scr) = Spec.Sha3.zero := by
  have hw : ∀ k < 50, InRegions t.wr (State.addr (t.gpr .r0) + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k hk
    rw [hu.wr, h0]
    exact ⟨L.SCR, by simp [Lay.outputs], Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (zeroStores_ok h1 (by rw [h0]; have := hL.nc; omega) hw) fun v hv => ⟨?_, ?_⟩
  · refine hu.of_frame hv.rd hv.wr hv.sp (fun r _ _ => by rw [hv.gpr]) hv.frame ?_
    intro r hr
    rw [List.mem_singleton.mp hr, h0]
    exact .inr ⟨L.SCR, by simp [Lay.outputs], Region.sub_prefix (by decide)⟩
  · have := hv.zero
    rw [h0] at this
    exact stateAt_zero this

def zeroValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r1, .const 0)]

theorem zero_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa zeroState t fun u =>
      Ctx L g m₀ u ∧ stateAt u.mem (State.addr L.scr) = Spec.Sha3.zero := by
  unfold zeroState
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := zeroValues) (stk := [])
    (by decide) (by simp [zeroValues, Whole.valid]) (by simp [zeroValues]) (by simp [zeroValues, preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, _, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp [zeroValues])
  have h1 := hs (.r1, .const 0) (by simp [zeroValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1
  exact zeroStores_step hu hL h0 h1

/-! ## The regions of the calls -/

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

theorem hash_addr (hL : L.Ok) : State.addr (L.E + BitVec.ofNat 32 HASH) = State.addr L.E + BitVec.ofNat 64 HASH :=
  addr_add (by have := hL.top; simp only [HASH]; omega)

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

theorem seed_scr (hL : L.Ok) : ∀ r ∈ kWr L, L.SEED.Disjoint r :=
  fun r hr => hL.sc.sub_right (kWr_sub L r hr).sub

/-! ## `absorb` -/

def absRd (L : Lay) : List Region := [L.SEED, kArgs L 8]

theorem abs_pre (hL : L.Ok) (he : t.sp = L.E) (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 136)
    (h2 : t.gpr .r2 = 0) (h3 : t.gpr .r3 = L.seed) (a0 : stackArg t 0 = 57)
    (a1 : stackArg t 1 = L.scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.absorbArm.pre (t.callEntry.withRegions (absRd L) (kWr L)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions (absRd L) (kWr L)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions (absRd L) (kWr L)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.absorbArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, h3, a0, a1, he, scr_addr hL]
  have ws := seed_scr hL
  have wa := args_scr hL (n := 8) (by decide)
  refine ⟨rfl, rfl, state_scratch L, ws _ (by simp [kWr]), ws _ (by simp [kWr]),
    wa _ (by simp [kWr]), wa _ (by simp [kWr]), by have := hL.nc; omega, hL.ns, scr_fit hL,
    by have := hL.top; omega, by decide, by decide⟩

theorem abs_covers (L : Lay) : Covers (absRd L ++ kWr L) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [absRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.SEED, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by change 0 + 57 ≤ 57; decide⟩
    · exact ⟨L.FR, by simp, 0, (BitVec.add_zero _).symm, by change 0 + 8 ≤ 248; decide⟩
  · exact ⟨L.SCR, by simp [Lay.outputs], kWr_sub L r hr⟩

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem absorb_noFrames : Impl.Sha3.Arm.Stream.absorb.noFrames = true := by decide
theorem pad_noFrames : Impl.Sha3.Arm.Stream.pad.noFrames = true := by decide
theorem squeeze_noFrames : Impl.Sha3.Arm.Stream.squeeze.noFrames = true := by decide

def absValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r1, .const 136), (.r2, .const 0), (.r3, .caller 1 0)]
def absStack : List Value := [.const 57, .caller 2 KSCR]

theorem abs_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hz : stateAt t.mem (State.addr L.scr) = Spec.Sha3.zero) :
    WP isa (callWith absorbArgs Spec.Sha3.absorbScratchApi.name Impl.Sha3.Arm.Stream.absorb) t fun u =>
      Ctx L g m₀ u ∧ Spec.Sha3.Repr u.mem (State.addr L.scr) 136
        (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := absValues) (stk := absStack)
    (by decide) (by simp [absValues, Whole.valid]) (by simp [absValues]) (by simp [absValues, preserved])
    (by decide) (by simp [absStack, Whole.valid, KSCR]) (by simp [absStack])) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp [absValues])
  have h1 := hs (.r1, .const 136) (by simp [absValues])
  have h2 := hs (.r2, .const 0) (by simp [absValues])
  have h3 := hs (.r3, .caller 1 0) (by simp [absValues])
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  simp only [absStack, argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  have hz' : stateAt u.mem (State.addr L.scr) = Spec.Sha3.zero := by
    rw [← hz]
    refine Proof.Sha3.stateAt_congr fun j hj => ?_
    refine hm.bytes (R := ⟨State.addr L.scr, 200⟩) ?_ (by change 200 ≤ 2 ^ 64; decide) hj
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact ((hL.kc.sub_left (Region.sub_prefix (by decide : 24 ≤ 280))).sub_right
      (Region.sub_prefix (by decide))).symm
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1 absorb_noFrames
    (abs_pre hL hu.sp h0 h1 h2 h3 a0 a1) (abs_covers L) (kWr_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  have hp1 := hp.1
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    stackArg_withRegions] at hp1
  rw [h0, h1, h2, h3, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0] at hp1
  have h := hp1 [] (repr_nil hz') rfl
  change Spec.Sha3.Repr v.mem (State.addr L.scr) 136 ([] ++ Spec.Ed448.bytesAt u.mem (State.addr L.seed) 57) at h
  rw [List.nil_append, hu.seed_bytes hL] at h
  exact h

/-- The state, through a call's setup (which writes only the frame's first 24 bytes). -/
theorem state_setup (hL : L.Ok) {u : State} (hm : Frame [⟨State.addr L.E, 24⟩] t.mem u.mem) :
    stateAt u.mem (State.addr L.scr) = stateAt t.mem (State.addr L.scr) := by
  refine Proof.Sha3.stateAt_congr fun j hj => ?_
  refine hm.bytes (R := ⟨State.addr L.scr, 200⟩) ?_ (by change 200 ≤ 2 ^ 64; decide) hj
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact ((hL.kc.sub_left (Region.sub_prefix (by decide : 24 ≤ 280))).sub_right
    (Region.sub_prefix (by decide))).symm

theorem repr_setup (hL : L.Ok) {u : State} (hm : Frame [⟨State.addr L.E, 24⟩] t.mem u.mem) {msg : List Byte}
    (h : Spec.Sha3.Repr t.mem (State.addr L.scr) 136 msg) : Spec.Sha3.Repr u.mem (State.addr L.scr) 136 msg := by
  unfold Spec.Sha3.Repr at h ⊢
  rw [state_setup hL hm]; exact h

/-! ## `pad` -/

def padValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r1, .const 136), (.r2, .const 57), (.r3, .const 0x1f)]
def padStack : List Value := [.caller 2 KSCR]

theorem pad_pre (hL : L.Ok) (he : t.sp = L.E) (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 136)
    (h2 : t.gpr .r2 = 57) (a0 : stackArg t 0 = L.scr + BitVec.ofNat 32 KSCR) :
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
  refine ⟨rfl, rfl, state_scratch L, wa _ (by simp [kWr]), wa _ (by simp [kWr]),
    by have := hL.nc; omega, scr_fit hL, by have := hL.top; omega, by decide, by decide⟩

theorem pad_covers (L : Lay) : Covers ([kArgs L 4] ++ kWr L) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨L.FR, by simp, 0, (BitVec.add_zero _).symm, by change 0 + 4 ≤ 248; decide⟩
  · exact ⟨L.SCR, by simp [Lay.outputs], kWr_sub L r hr⟩

theorem pad_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) {msg : List Byte}
    (hr : Spec.Sha3.Repr t.mem (State.addr L.scr) 136 msg) (hl : msg.length = 57) :
    WP isa (callWith padArgs Spec.Sha3.padScratchApi.name Impl.Sha3.Arm.Stream.pad) t fun u =>
      Ctx L g m₀ u ∧ stateAt u.mem (State.addr L.scr) =
        Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := padValues) (stk := padStack)
    (by decide) (by simp [padValues, Whole.valid]) (by simp [padValues]) (by simp [padValues, preserved])
    (by decide) (by simp [padStack, Whole.valid, KSCR]) (by simp [padStack])) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp [padValues])
  have h1 := hs (.r1, .const 136) (by simp [padValues])
  have h2 := hs (.r2, .const 57) (by simp [padValues])
  have h3 := hs (.r3, .const 0x1f) (by simp [padValues])
  have a0 := st 0 (by decide)
  simp only [padStack, argValue, Lay.value, List.getElem_cons_zero, BitVec.add_zero] at h0 h1 h2 h3 a0
  have hr' := repr_setup hL hm hr
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Pad.pad_verified.1 pad_noFrames
    (pad_pre hL hu.sp h0 h1 h2 a0) (pad_covers L) (kWr_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  simp only [Proof.Sha3.padArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs)] at hp
  rw [h0, h1, h2, h3] at hp
  exact hp msg hr' (by rw [hl]; rfl)

/-! ## `squeeze` -/

def sqzWr (L : Lay) : List Region :=
  [⟨State.addr L.scr, 200⟩, ⟨State.addr L.E + BitVec.ofNat 64 HASH, 114⟩,
    ⟨State.addr L.scr + BitVec.ofNat 64 KSCR, 640⟩]

def sqzValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame HASH)]
def sqzStack : List Value := [.const 114, .caller 2 KSCR]

theorem out_sub (L : Lay) : Whole.Within ⟨State.addr L.E + BitVec.ofNat 64 HASH, 114⟩ L.FR :=
  ⟨HASH, rfl, by change 24 + 114 ≤ 248; decide⟩

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
  rw [h0, h1, h2, h3, a0, a1, he, scr_addr hL, hash_addr hL]
  have wa := args_scr hL (n := 8) (by decide)
  have so : ∀ r ∈ kWr L, (⟨State.addr L.E + BitVec.ofNat 64 HASH, 114⟩ : Region).Disjoint r :=
    fun r hr => (hL.kc.sub_left (Offset.sub_base _ (by decide : 24 + 114 ≤ 280))).sub_right
      (kWr_sub L r hr).sub
  have ht := hL.top
  refine ⟨rfl, rfl, (so _ (by simp [kWr])).symm, state_scratch L, so _ (by simp [kWr]),
    wa _ (by simp [kWr]), Offset.base_disjoint _ (by decide) (by decide), wa _ (by simp [kWr]),
    by have := hL.nc; omega, ?_, scr_fit hL, by omega, by decide, by decide⟩
  rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 24 < 2 ^ 32; omega)]
  change L.E.toNat + 24 + 114 ≤ 2 ^ 32
  omega

theorem sqz_writes (L : Lay) : ∀ r ∈ sqzWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact kWr_writes L _ (by simp [kWr])
  · exact .inl (out_sub L)
  · exact kWr_writes L _ (by simp [kWr])

theorem sqz_covers (L : Lay) : Covers ([kArgs L 8] ++ sqzWr L) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨L.FR, by simp, 0, (BitVec.add_zero _).symm, by change 0 + 8 ≤ 248; decide⟩
  · rcases sqz_writes L r hr with h | ⟨R, hR, h⟩
    · exact ⟨L.FR, by simp, h⟩
    · exact ⟨R, by simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hR), h⟩

theorem sqz_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith squeezeArgs Spec.Sha3.squeezeScratchApi.name Impl.Sha3.Arm.Stream.squeeze) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem (State.addr L.scr)) 0 114 := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := sqzValues) (stk := sqzStack)
    (by decide) (by simp [sqzValues, Whole.valid, HASH]) (by simp [sqzValues]) (by simp [sqzValues, preserved])
    (by decide) (by simp [sqzStack, Whole.valid, KSCR]) (by simp [sqzStack])) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp [sqzValues])
  have h1 := hs (.r1, .const 136) (by simp [sqzValues])
  have h2 := hs (.r2, .const 0) (by simp [sqzValues])
  have h3 := hs (.r3, .frame HASH) (by simp [sqzValues])
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  simp only [sqzStack, argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 squeeze_noFrames
    (sqz_pre hL hu.sp h0 h1 h2 h3 a0 a1) (sqz_covers L) (sqz_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  have hp1 := hp.1
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    stackArg_withRegions] at hp1
  rw [h0, h1, h2, h3, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0, hash_addr hL,
    state_setup hL hm] at hp1
  exact hp1

/-! ## The hash -/

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    Spec.Sha3.squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [Spec.Sha3.squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

theorem shake256_eq (m : List Byte) (d : Nat) :
    Spec.Sha3.shake256 m d =
      Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix m)) 0 d := by
  rw [squeezeFrom_zero]; rfl

/-- `SHAKE256(seed, 114)` in the frame at `HASH`. -/
theorem hash_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hash t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Sha3.shake256 (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) 114 := by
  refine WP.seq (WP.mono (zero_ok hc hL ha) fun t₁ ⟨hc₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (abs_step hc₁ hL ha hz₁) fun t₂ ⟨hc₂, hr₂⟩ => ?_)
  refine WP.seq (WP.mono (pad_step hc₂ hL ha hr₂ (by simp [Spec.Ed448.bytesAt])) fun t₃ ⟨hc₃, hs₃⟩ => ?_)
  refine WP.mono (sqz_step hc₃ hL ha) fun t₄ ⟨hc₄, hb₄⟩ => ⟨hc₄, ?_⟩
  rw [hb₄, hs₃, shake256_eq]

end VG.Proof.Ed448.Arm.PublicKey
