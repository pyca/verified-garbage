import VerifiedGarbage.Impl.Ed448.Arm.PublicKey
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Proof.Sha512.Arm.Compress
import VerifiedGarbage.Proof.Ed448.PruneBytes
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.X448.Arm.Verified
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ed448.Arm.BaseVerified
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.Arm.Inline

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Layout`. -/
section

/-!
# Ed448 public-key derivation on ARMv7: the layout

The frame is Ed25519's on this target (`Proof/Ed25519/Arm/Whole`): `Ctx`
holds between the frame's entry and its exit (the permissions, `sp`, the
callee-saved registers, and memory changed only in the frame and in the
outputs `out` and `scratch`). `Lay` names the pointers and the frame's base
`E`, and `setup_ok` sets a call's arguments from them.
-/

namespace VG.Proof.Ed448.Arm.PublicKey

open VG VG.Arm VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.ARGS Whole.value Whole.valid)

structure Lay where
  out : BitVec 32
  seed : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : VG.Proof.Ed448.Arm.PublicKey.Lay)
abbrev OUT : Region := ⟨State.addr L.out, 57⟩
abbrev SEED : Region := ⟨State.addr L.seed, 57⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := ⟨State.addr L.E, 280⟩
def inputs : List Region := [L.SEED, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : BitVec 32 := match j with | 0 => L.out | 1 => L.seed | _ => L.scr
structure Ok : Prop where
  top : L.E.toNat + 272 ≤ 2 ^ 32
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 57 ≤ 2 ^ 32
  ns : L.seed.toNat + 57 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

abbrev Ctx (L : VG.Proof.Ed448.Arm.PublicKey.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

def Arguments (L : VG.Proof.Ed448.Arm.PublicKey.Lay) (m : Mem) : Prop :=
  ∀ j < 3, m.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 = L.value j

def argValue (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

variable {L : VG.Proof.Ed448.Arm.PublicKey.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem frame_sub (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 248 ≤ 280)
theorem args_sub (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 248 + 24 ≤ 280)

theorem Ctx.seed_bytes (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) :
    Spec.Ed448.bytesAt t.mem (State.addr L.seed) 57 = Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57 := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi =>
    hc.frame.bytes (R := L.SEED) ?_ (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (VG.Proof.Ed448.Arm.PublicKey.frame_sub L)).symm

theorem Ctx.arg_word (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 3) :
    t.mem.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS)
    (Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.ko.sub_left (VG.Proof.Ed448.Arm.PublicKey.args_sub L)
  · exact hL.kc.sub_left (VG.Proof.Ed448.Arm.PublicKey.args_sub L)
  · exact Offset.disjoint_base _ (by decide : 248 ≤ 248) (by decide : 248 + 24 ≤ 2 ^ 64)

theorem value_eq (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₀)
    (v : Value) (hi : ∀ j d, v = .caller j d → j < 3) : Whole.value L.E t.mem v = VG.Proof.Ed448.Arm.PublicKey.argValue L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    simp only [Whole.value, VG.Proof.Ed448.Arm.PublicKey.argValue]
    rw [hc.arg_word hL (hi j d rfl), ha j (hi j d rfl)]

theorem setup_ok (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₀)
    {args : List (Reg × Value)} {stk : List Value} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3)
    (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, Whole.valid v)
    (his : ∀ v ∈ stk, ∀ j d, v = .caller j d → j < 3) :
    WP isa (.block (VG.Impl.Ed25519.Arm.Whole.setup args stk)) t fun u => VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧
      Frame [⟨State.addr L.E, 24⟩] t.mem u.mem ∧
      (∀ p ∈ args, u.gpr p.1 = VG.Proof.Ed448.Arm.PublicKey.argValue L p.2) ∧
      (∀ j (hj : j < stk.length), stackArg u j = VG.Proof.Ed448.Arm.PublicKey.argValue L (stk[j]'hj)) := by
  refine WP.mono (hc.setup hL.top hn hv hs hvs (by simp [Lay.inputs]) hr)
    fun u ⟨hu, hm, hregs, hstk⟩ => ⟨hu, hm, ?_, ?_⟩
  · intro p hp
    rw [hregs p hp, VG.Proof.Ed448.Arm.PublicKey.value_eq hc hL ha _ (hi p hp)]
  · intro j hj
    rw [hstk j hj, VG.Proof.Ed448.Arm.PublicKey.value_eq hc hL ha _ (his _ (List.getElem_mem hj))]

end VG.Proof.Ed448.Arm.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash`. -/
section

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

variable {L : VG.Proof.Ed448.Arm.PublicKey.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

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
    WP isa (.block zeroStores) s₁ (VG.Proof.Ed448.Arm.PublicKey.ZInv s₁ 50) := by
  rw [zeroStores, List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa) (VG.Proof.Ed448.Arm.PublicKey.ZInv s₁) (fun k s hk h => ?_) 50 (Nat.le_refl _) s₁
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
theorem zeroStores_step (hu : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 0) :
    WP isa (.block zeroStores) t fun u =>
      VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧ stateAt u.mem (State.addr L.scr) = Spec.Sha3.zero := by
  have hw : ∀ k < 50, InRegions t.wr (State.addr (t.gpr .r0) + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k hk
    rw [hu.wr, h0]
    exact ⟨L.SCR, by simp [Lay.outputs], Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (VG.Proof.Ed448.Arm.PublicKey.zeroStores_ok h1 (by rw [h0]; have := hL.nc; omega) hw) fun v hv => ⟨?_, ?_⟩
  · refine hu.of_frame hv.rd hv.wr hv.sp (fun r _ _ => by rw [hv.gpr]) hv.frame ?_
    intro r hr
    rw [List.mem_singleton.mp hr, h0]
    exact .inr ⟨L.SCR, by simp [Lay.outputs], Region.sub_prefix (by decide)⟩
  · have := hv.zero
    rw [h0] at this
    exact VG.Proof.Ed448.Arm.PublicKey.stateAt_zero this

def zeroValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r1, .const 0)]

theorem zero_ok (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₀) :
    WP isa zeroState t fun u =>
      VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧ stateAt u.mem (State.addr L.scr) = Spec.Sha3.zero := by
  unfold zeroState
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.setup_ok hc hL ha (args := VG.Proof.Ed448.Arm.PublicKey.zeroValues) (stk := [])
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.zeroValues, Whole.valid]) (by simp [VG.Proof.Ed448.Arm.PublicKey.zeroValues]) (by simp [VG.Proof.Ed448.Arm.PublicKey.zeroValues, preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, _, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.zeroValues])
  have h1 := hs (.r1, .const 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.zeroValues])
  simp only [VG.Proof.Ed448.Arm.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1
  exact VG.Proof.Ed448.Arm.PublicKey.zeroStores_step hu hL h0 h1

/-! ## The regions of the calls -/

/-- The state and the sponge functions' working space. -/
def kWr (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : List Region :=
  [⟨State.addr L.scr, 200⟩, ⟨State.addr L.scr + BitVec.ofNat 64 KSCR, 640⟩]

def kArgs (L : VG.Proof.Ed448.Arm.PublicKey.Lay) (n : Nat) : Region := ⟨State.addr L.E, n⟩

theorem scr_addr (hL : L.Ok) : State.addr (L.scr + BitVec.ofNat 32 KSCR) = State.addr L.scr + BitVec.ofNat 64 KSCR :=
  addr_add (by have := hL.nc; simp only [KSCR]; omega)

theorem scr_fit (hL : L.Ok) : (L.scr + BitVec.ofNat 32 KSCR).toNat + 640 ≤ 2 ^ 32 := by
  have := hL.nc
  rw [BitVec.toNat_add_of_lt (by change L.scr.toNat + 208 < 2 ^ 32; omega)]
  change L.scr.toNat + 208 + 640 ≤ 2 ^ 32
  omega

theorem hash_addr (hL : L.Ok) : State.addr (L.E + BitVec.ofNat 32 HASH) = State.addr L.E + BitVec.ofNat 64 HASH :=
  addr_add (by have := hL.top; simp only [HASH]; omega)

theorem kWr_sub (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : ∀ r ∈ VG.Proof.Ed448.Arm.PublicKey.kWr L, Whole.Within r L.SCR := by
  intro r hr
  simp only [VG.Proof.Ed448.Arm.PublicKey.kWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨0, (BitVec.add_zero _).symm, by change 0 + 200 ≤ 8192; decide⟩
  · exact ⟨KSCR, rfl, by change 208 + 640 ≤ 8192; decide⟩

theorem kWr_writes (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : ∀ r ∈ VG.Proof.Ed448.Arm.PublicKey.kWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed448.Arm.PublicKey.kWr_sub L r hr⟩

theorem state_scratch (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : (⟨State.addr L.scr, 200⟩ : Region).Disjoint
    ⟨State.addr L.scr + BitVec.ofNat 64 KSCR, 640⟩ := Offset.base_disjoint _ (by decide) (by decide)

theorem args_scr (hL : L.Ok) {n : Nat} (hn : n ≤ 280) : ∀ r ∈ VG.Proof.Ed448.Arm.PublicKey.kWr L, (VG.Proof.Ed448.Arm.PublicKey.kArgs L n).Disjoint r :=
  fun r hr => (hL.kc.sub_left (Region.sub_prefix hn)).sub_right (VG.Proof.Ed448.Arm.PublicKey.kWr_sub L r hr).sub

theorem seed_scr (hL : L.Ok) : ∀ r ∈ VG.Proof.Ed448.Arm.PublicKey.kWr L, L.SEED.Disjoint r :=
  fun r hr => hL.sc.sub_right (VG.Proof.Ed448.Arm.PublicKey.kWr_sub L r hr).sub

/-! ## `absorb` -/

def absRd (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : List Region := [L.SEED, VG.Proof.Ed448.Arm.PublicKey.kArgs L 8]

theorem abs_pre (hL : L.Ok) (he : t.sp = L.E) (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 136)
    (h2 : t.gpr .r2 = 0) (h3 : t.gpr .r3 = L.seed) (a0 : stackArg t 0 = 57)
    (a1 : stackArg t 1 = L.scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.absorbArm.pre (t.callEntry.withRegions (VG.Proof.Ed448.Arm.PublicKey.absRd L) (VG.Proof.Ed448.Arm.PublicKey.kWr L)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions (VG.Proof.Ed448.Arm.PublicKey.absRd L) (VG.Proof.Ed448.Arm.PublicKey.kWr L)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions (VG.Proof.Ed448.Arm.PublicKey.absRd L) (VG.Proof.Ed448.Arm.PublicKey.kWr L)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.absorbArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, h3, a0, a1, he, VG.Proof.Ed448.Arm.PublicKey.scr_addr hL]
  have ws := VG.Proof.Ed448.Arm.PublicKey.seed_scr hL
  have wa := VG.Proof.Ed448.Arm.PublicKey.args_scr hL (n := 8) (by decide)
  refine ⟨rfl, rfl, VG.Proof.Ed448.Arm.PublicKey.state_scratch L, ws _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr]), ws _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr]),
    wa _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr]), wa _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr]), by have := hL.nc; omega, hL.ns, VG.Proof.Ed448.Arm.PublicKey.scr_fit hL,
    by have := hL.top; omega, by decide, by decide⟩

theorem abs_covers (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : Covers (VG.Proof.Ed448.Arm.PublicKey.absRd L ++ VG.Proof.Ed448.Arm.PublicKey.kWr L) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [VG.Proof.Ed448.Arm.PublicKey.absRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.SEED, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by change 0 + 57 ≤ 57; decide⟩
    · exact ⟨L.FR, by simp, 0, (BitVec.add_zero _).symm, by change 0 + 8 ≤ 248; decide⟩
  · exact ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed448.Arm.PublicKey.kWr_sub L r hr⟩

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem absorb_noFrames : Impl.Sha3.Arm.Stream.absorb.noFrames = true := by decide
theorem pad_noFrames : Impl.Sha3.Arm.Stream.pad.noFrames = true := by decide
theorem squeeze_noFrames : Impl.Sha3.Arm.Stream.squeeze.noFrames = true := by decide

def absValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r1, .const 136), (.r2, .const 0), (.r3, .caller 1 0)]
def absStack : List Value := [.const 57, .caller 2 KSCR]

theorem abs_step (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₀)
    (hz : stateAt t.mem (State.addr L.scr) = Spec.Sha3.zero) :
    WP isa (callWith absorbArgs Spec.Sha3.absorbScratchApi.name Impl.Sha3.Arm.Stream.absorb) t fun u =>
      VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧ Spec.Sha3.Repr u.mem (State.addr L.scr) 136
        (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.setup_ok hc hL ha (args := VG.Proof.Ed448.Arm.PublicKey.absValues) (stk := VG.Proof.Ed448.Arm.PublicKey.absStack)
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues, Whole.valid]) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues]) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues, preserved])
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.absStack, Whole.valid, KSCR]) (by simp [VG.Proof.Ed448.Arm.PublicKey.absStack])) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues])
  have h1 := hs (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues])
  have h2 := hs (.r2, .const 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues])
  have h3 := hs (.r3, .caller 1 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues])
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  simp only [VG.Proof.Ed448.Arm.PublicKey.absStack, VG.Proof.Ed448.Arm.PublicKey.argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  have hz' : stateAt u.mem (State.addr L.scr) = Spec.Sha3.zero := by
    rw [← hz]
    refine Proof.Sha3.stateAt_congr fun j hj => ?_
    refine hm.bytes (R := ⟨State.addr L.scr, 200⟩) ?_ (by change 200 ≤ 2 ^ 64; decide) hj
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact ((hL.kc.sub_left (Region.sub_prefix (by decide : 24 ≤ 280))).sub_right
      (Region.sub_prefix (by decide))).symm
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1 VG.Proof.Ed448.Arm.PublicKey.absorb_noFrames
    (VG.Proof.Ed448.Arm.PublicKey.abs_pre hL hu.sp h0 h1 h2 h3 a0 a1) (VG.Proof.Ed448.Arm.PublicKey.abs_covers L) (VG.Proof.Ed448.Arm.PublicKey.kWr_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  have hp1 := hp.1
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    stackArg_withRegions] at hp1
  rw [h0, h1, h2, h3, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0] at hp1
  have h := hp1 [] (VG.Proof.Ed448.Arm.PublicKey.repr_nil hz') rfl
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
  rw [VG.Proof.Ed448.Arm.PublicKey.state_setup hL hm]; exact h

/-! ## `pad` -/

def padValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r1, .const 136), (.r2, .const 57), (.r3, .const 0x1f)]
def padStack : List Value := [.caller 2 KSCR]

theorem pad_pre (hL : L.Ok) (he : t.sp = L.E) (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 136)
    (h2 : t.gpr .r2 = 57) (a0 : stackArg t 0 = L.scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.padArm.pre (t.callEntry.withRegions [VG.Proof.Ed448.Arm.PublicKey.kArgs L 4] (VG.Proof.Ed448.Arm.PublicKey.kWr L)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions [VG.Proof.Ed448.Arm.PublicKey.kArgs L 4] (VG.Proof.Ed448.Arm.PublicKey.kWr L)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions [VG.Proof.Ed448.Arm.PublicKey.kArgs L 4] (VG.Proof.Ed448.Arm.PublicKey.kWr L)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.padArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, a0, he, VG.Proof.Ed448.Arm.PublicKey.scr_addr hL]
  have wa := VG.Proof.Ed448.Arm.PublicKey.args_scr hL (n := 4) (by decide)
  refine ⟨rfl, rfl, VG.Proof.Ed448.Arm.PublicKey.state_scratch L, wa _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr]), wa _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr]),
    by have := hL.nc; omega, VG.Proof.Ed448.Arm.PublicKey.scr_fit hL, by have := hL.top; omega, by decide, by decide⟩

theorem pad_covers (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : Covers ([VG.Proof.Ed448.Arm.PublicKey.kArgs L 4] ++ VG.Proof.Ed448.Arm.PublicKey.kWr L) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨L.FR, by simp, 0, (BitVec.add_zero _).symm, by change 0 + 4 ≤ 248; decide⟩
  · exact ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed448.Arm.PublicKey.kWr_sub L r hr⟩

theorem pad_step (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₀) {msg : List Byte}
    (hr : Spec.Sha3.Repr t.mem (State.addr L.scr) 136 msg) (hl : msg.length = 57) :
    WP isa (callWith padArgs Spec.Sha3.padScratchApi.name Impl.Sha3.Arm.Stream.pad) t fun u =>
      VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧ stateAt u.mem (State.addr L.scr) =
        Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.setup_ok hc hL ha (args := VG.Proof.Ed448.Arm.PublicKey.padValues) (stk := VG.Proof.Ed448.Arm.PublicKey.padStack)
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues, Whole.valid]) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues]) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues, preserved])
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.padStack, Whole.valid, KSCR]) (by simp [VG.Proof.Ed448.Arm.PublicKey.padStack])) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues])
  have h1 := hs (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues])
  have h2 := hs (.r2, .const 57) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues])
  have h3 := hs (.r3, .const 0x1f) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues])
  have a0 := st 0 (by decide)
  simp only [VG.Proof.Ed448.Arm.PublicKey.padStack, VG.Proof.Ed448.Arm.PublicKey.argValue, Lay.value, List.getElem_cons_zero, BitVec.add_zero] at h0 h1 h2 h3 a0
  have hr' := VG.Proof.Ed448.Arm.PublicKey.repr_setup hL hm hr
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Pad.pad_verified.1 VG.Proof.Ed448.Arm.PublicKey.pad_noFrames
    (VG.Proof.Ed448.Arm.PublicKey.pad_pre hL hu.sp h0 h1 h2 a0) (VG.Proof.Ed448.Arm.PublicKey.pad_covers L) (VG.Proof.Ed448.Arm.PublicKey.kWr_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  simp only [Proof.Sha3.padArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs)] at hp
  rw [h0, h1, h2, h3] at hp
  exact hp msg hr' (by rw [hl]; rfl)

/-! ## `squeeze` -/

def sqzWr (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : List Region :=
  [⟨State.addr L.scr, 200⟩, ⟨State.addr L.E + BitVec.ofNat 64 HASH, 114⟩,
    ⟨State.addr L.scr + BitVec.ofNat 64 KSCR, 640⟩]

def sqzValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame HASH)]
def sqzStack : List Value := [.const 114, .caller 2 KSCR]

theorem out_sub (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : Whole.Within ⟨State.addr L.E + BitVec.ofNat 64 HASH, 114⟩ L.FR :=
  ⟨HASH, rfl, by change 24 + 114 ≤ 248; decide⟩

theorem sqz_pre (hL : L.Ok) (he : t.sp = L.E) (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 136)
    (h2 : t.gpr .r2 = 0) (h3 : t.gpr .r3 = L.E + BitVec.ofNat 32 HASH) (a0 : stackArg t 0 = 114)
    (a1 : stackArg t 1 = L.scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.squeezeArm.pre (t.callEntry.withRegions [VG.Proof.Ed448.Arm.PublicKey.kArgs L 8] (VG.Proof.Ed448.Arm.PublicKey.sqzWr L)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions [VG.Proof.Ed448.Arm.PublicKey.kArgs L 8] (VG.Proof.Ed448.Arm.PublicKey.sqzWr L)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions [VG.Proof.Ed448.Arm.PublicKey.kArgs L 8] (VG.Proof.Ed448.Arm.PublicKey.sqzWr L)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.squeezeArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, h3, a0, a1, he, VG.Proof.Ed448.Arm.PublicKey.scr_addr hL, VG.Proof.Ed448.Arm.PublicKey.hash_addr hL]
  have wa := VG.Proof.Ed448.Arm.PublicKey.args_scr hL (n := 8) (by decide)
  have so : ∀ r ∈ VG.Proof.Ed448.Arm.PublicKey.kWr L, (⟨State.addr L.E + BitVec.ofNat 64 HASH, 114⟩ : Region).Disjoint r :=
    fun r hr => (hL.kc.sub_left (Offset.sub_base _ (by decide : 24 + 114 ≤ 280))).sub_right
      (VG.Proof.Ed448.Arm.PublicKey.kWr_sub L r hr).sub
  have ht := hL.top
  refine ⟨rfl, rfl, (so _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr])).symm, VG.Proof.Ed448.Arm.PublicKey.state_scratch L, so _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr]),
    wa _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr]), Offset.base_disjoint _ (by decide) (by decide), wa _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr]),
    by have := hL.nc; omega, ?_, VG.Proof.Ed448.Arm.PublicKey.scr_fit hL, by omega, by decide, by decide⟩
  rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 24 < 2 ^ 32; omega)]
  change L.E.toNat + 24 + 114 ≤ 2 ^ 32
  omega

theorem sqz_writes (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : ∀ r ∈ VG.Proof.Ed448.Arm.PublicKey.sqzWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [VG.Proof.Ed448.Arm.PublicKey.sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.Ed448.Arm.PublicKey.kWr_writes L _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr])
  · exact .inl (VG.Proof.Ed448.Arm.PublicKey.out_sub L)
  · exact VG.Proof.Ed448.Arm.PublicKey.kWr_writes L _ (by simp [VG.Proof.Ed448.Arm.PublicKey.kWr])

theorem sqz_covers (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : Covers ([VG.Proof.Ed448.Arm.PublicKey.kArgs L 8] ++ VG.Proof.Ed448.Arm.PublicKey.sqzWr L) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨L.FR, by simp, 0, (BitVec.add_zero _).symm, by change 0 + 8 ≤ 248; decide⟩
  · rcases VG.Proof.Ed448.Arm.PublicKey.sqz_writes L r hr with h | ⟨R, hR, h⟩
    · exact ⟨L.FR, by simp, h⟩
    · exact ⟨R, by simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hR), h⟩

theorem sqz_step (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₀) :
    WP isa (callWith squeezeArgs Spec.Sha3.squeezeScratchApi.name Impl.Sha3.Arm.Stream.squeeze) t fun u =>
      VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧ Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem (State.addr L.scr)) 0 114 := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.setup_ok hc hL ha (args := VG.Proof.Ed448.Arm.PublicKey.sqzValues) (stk := VG.Proof.Ed448.Arm.PublicKey.sqzStack)
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues, Whole.valid, HASH]) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues]) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues, preserved])
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzStack, Whole.valid, KSCR]) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzStack])) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues])
  have h1 := hs (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues])
  have h2 := hs (.r2, .const 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues])
  have h3 := hs (.r3, .frame HASH) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues])
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  simp only [VG.Proof.Ed448.Arm.PublicKey.sqzStack, VG.Proof.Ed448.Arm.PublicKey.argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 VG.Proof.Ed448.Arm.PublicKey.squeeze_noFrames
    (VG.Proof.Ed448.Arm.PublicKey.sqz_pre hL hu.sp h0 h1 h2 h3 a0 a1) (VG.Proof.Ed448.Arm.PublicKey.sqz_covers L) (VG.Proof.Ed448.Arm.PublicKey.sqz_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  have hp1 := hp.1
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    stackArg_withRegions] at hp1
  rw [h0, h1, h2, h3, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0, VG.Proof.Ed448.Arm.PublicKey.hash_addr hL,
    VG.Proof.Ed448.Arm.PublicKey.state_setup hL hm] at hp1
  exact hp1

/-! ## The hash -/

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    Spec.Sha3.squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [Spec.Sha3.squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

theorem shake256_eq (m : List Byte) (d : Nat) :
    Spec.Sha3.shake256 m d =
      Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix m)) 0 d := by
  rw [VG.Proof.Ed448.Arm.PublicKey.squeezeFrom_zero]; rfl

/-- `SHAKE256(seed, 114)` in the frame at `HASH`. -/
theorem hash_ok (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₀) :
    WP isa hash t fun u => VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Sha3.shake256 (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) 114 := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.zero_ok hc hL ha) fun t₁ ⟨hc₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.abs_step hc₁ hL ha hz₁) fun t₂ ⟨hc₂, hr₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.pad_step hc₂ hL ha hr₂ (by simp [Spec.Ed448.bytesAt])) fun t₃ ⟨hc₃, hs₃⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.Arm.PublicKey.sqz_step hc₃ hL ha) fun t₄ ⟨hc₄, hb₄⟩ => ⟨hc₄, ?_⟩
  rw [hb₄, hs₃, VG.Proof.Ed448.Arm.PublicKey.shake256_eq]

end VG.Proof.Ed448.Arm.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Prune`. -/
section

/-!
# Ed448 public-key derivation on ARMv7: pruning the hash in place

`pruneOps` clears bits 0–1 of byte 0 of the hash, sets bit 7 of byte 55 and
clears byte 56, from `r12`; the 57 bytes are then `Spec.Ed448.prune` of the
hash (`prune_step`, by `Proof.Ed448.prune_bytes`).
-/

namespace VG.Proof.Ed448.Arm.PublicKey

open VG VG.Arm VG.Impl.Ed448.Arm.PublicKey VG.Impl.Ed25519.Arm.Whole
open VG.Proof.X25519.Arm (wp_ldrb wp_strb wp_dp wp_movw op2_imm)
open VG.Proof.X448.Arm (writeW8_apply)
open VG.Proof.Ed25519.Arm (Whole.FR)

/-! ## The bytes -/

theorem bytesAt_split (m : Mem) (q : Addr) :
    Spec.Ed448.bytesAt m q 57 = m q :: (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 ++
      [m (q + BitVec.ofNat 64 55), m (q + BitVec.ofNat 64 56)]) := by
  have b1 : Spec.X25519.bytesAt m q 1 = [m q] := by
    simp [Spec.X25519.bytesAt]
  have b2 : ∀ p : Addr, Spec.X25519.bytesAt m p 2 = [m p, m (p + BitVec.ofNat 64 1)] := fun p => by
    simp [Spec.X25519.bytesAt, List.range_succ]
  rw [Proof.Ed448.bytesAt_eq, show 57 = 1 + (54 + 2) from rfl, VG.Proof.X25519.bytesAt_add,
    VG.Proof.X25519.bytesAt_add, b1, b2, Offset.add_add, Offset.add_add]
  rfl

theorem decodeLE_split (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) = (m q).toNat + 256 *
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54) + 2 ^ 432 *
        ((m (q + BitVec.ofNat 64 55)).toNat + 256 * (m (q + BitVec.ofNat 64 56)).toNat)) := by
  rw [VG.Proof.Ed448.Arm.PublicKey.bytesAt_split, Spec.Ed448.decodeLE, Proof.Ed448.decodeLE_append]
  have hl : (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54).length = 54 := by simp [Spec.Ed448.bytesAt]
  rw [hl, show (256 : Nat) ^ 54 = 2 ^ 432 by decide +kernel]
  simp only [Spec.Ed448.decodeLE, Nat.mul_zero, Nat.add_zero]

/-! ## The instructions -/

theorem and_fc : ∀ x : BitVec 8, (x.setWidth 32 &&& 0xfc#32).setWidth 8 = BitVec.ofNat 8 (x.toNat &&& 252) := by
  decide

theorem or_80 : ∀ x : BitVec 8, (x.setWidth 32 ||| 0x80#32).setWidth 8 = BitVec.ofNat 8 (x.toNat ||| 128) := by
  decide

theorem pruneOps_ok {s : State} {q : Addr} (hq : State.addr (s.gpr .r12) = q)
    (hfit : (s.gpr .r12).toNat + 57 ≤ 2 ^ 32) (hw : ∀ j < 57, InRegions s.wr (q + BitVec.ofNat 64 j) 1) :
    WP isa (.block pruneOps) s fun t =>
      t.mem = ((s.mem.writeW q (BitVec.ofNat 8 ((s.mem q).toNat &&& 252))).writeW
        (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((s.mem (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
          (q + BitVec.ofNat 64 56) (0 : BitVec 8) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ∀ r, r ≠ .r0 → t.gpr r = s.gpr r := by
  have hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1 := fun j hj => by
    obtain ⟨R, hR, hc⟩ := hw j hj
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have ea : ∀ j < 57, State.addr (s.gpr .r12 + BitVec.ofNat 32 j) = q + BitVec.ofNat 64 j := fun j hj => by
    rw [addr_add (by omega), hq]
  have e0 : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have ne55 : q + BitVec.ofNat 64 55 ≠ q := by
    intro h
    have := congrArg (fun x => (x - q).toNat) h
    simp only [BitVec.sub_self, Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  unfold pruneOps
  refine VG.Proof.X25519.Arm.wp_ldrb (a := q) (by decide) (by rw [ea 0 (by decide), e0]) (by rw [← e0]; exact hr 0 (by decide))
    fun s1 v1 => ?_
  refine wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun s2 v2 => ?_
  refine VG.Proof.X25519.Arm.wp_strb (a := q) (by decide)
    (by rw [v2.other _ (by decide), v1.other _ (by decide), ea 0 (by decide), e0])
    (by rw [v2.wr, v1.wr, ← e0]; exact hw 0 (by decide)) fun s3 v3 => ?_
  refine VG.Proof.X25519.Arm.wp_ldrb (a := q + BitVec.ofNat 64 55) (by decide)
    (by rw [v3.gpr, v2.other _ (by decide), v1.other _ (by decide), ea 55 (by decide)])
    (by rw [v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr]; exact hr 55 (by decide)) fun s4 v4 => ?_
  refine wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun s5 v5 => ?_
  refine VG.Proof.X25519.Arm.wp_strb (a := q + BitVec.ofNat 64 55) (by decide)
    (by rw [v5.other _ (by decide), v4.other _ (by decide), v3.gpr, v2.other _ (by decide),
      v1.other _ (by decide), ea 55 (by decide)])
    (by rw [v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hw 55 (by decide)) fun s6 v6 => ?_
  refine VG.Proof.X25519.Arm.wp_movw fun s7 v7 => ?_
  refine VG.Proof.X25519.Arm.wp_strb (a := q + BitVec.ofNat 64 56) (by decide)
    (by rw [v7.other _ (by decide), v6.gpr, v5.other _ (by decide), v4.other _ (by decide), v3.gpr,
      v2.other _ (by decide), v1.other _ (by decide), ea 56 (by decide)])
    (by rw [v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hw 56 (by decide)) fun t vt =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · have r2 : s2.gpr .r0 = (s.mem q).setWidth 32 &&& 0xfc#32 := by
      rw [v2.gpr]; change s1.gpr .r0 &&& _ = _; rw [v1.gpr]; rfl
    have m3 : s3.mem = s.mem.writeW q ((s2.gpr .r0).setWidth 8) := by rw [v3.mem, v2.mem, v1.mem]
    have r5 : s5.gpr .r0 = (s.mem (q + BitVec.ofNat 64 55)).setWidth 32 ||| 0x80#32 := by
      rw [v5.gpr]; change s4.gpr .r0 ||| _ = _
      rw [v4.gpr, m3, VG.Proof.X448.Arm.writeW8_apply, ite_eq_right ne55]; rfl
    rw [vt.mem, v7.mem, v6.mem, v5.mem, v4.mem, m3, v7.gpr, r5, r2, VG.Proof.Ed448.Arm.PublicKey.and_fc, VG.Proof.Ed448.Arm.PublicKey.or_80]
    rfl
  · rw [vt.sp, v7.sp, v6.sp, v5.sp, v4.sp, v3.sp, v2.sp, v1.sp]
  · rw [vt.rd, v7.rd, v6.rd, v5.rd, v4.rd, v3.rd, v2.rd, v1.rd]
  · rw [vt.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]
  · rw [vt.gpr, v7.other r hr, v6.gpr, v5.other r hr, v4.other r hr, v3.gpr, v2.other r hr, v1.other r hr]

end VG.Proof.Ed448.Arm.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Base`. -/
section

/-!
# Ed448 public-key derivation on ARMv7: the pruning, the scalar's call, and the whole

`prune_step`: the hash's first 57 bytes pruned in place (`Spec.Ed448.prune`);
`base_step`: `vg_ed448_scalar_base` called on them, given the reference
ladder's agreement with the specification (`BaseLadderOk`, a hypothesis);
`wipe_step`: the frame cleared. `publicKey_ok`: the whole function, in
Ed25519's frame on this target (`Whole.wrap_ok`).
-/

namespace VG.Proof.Ed448.Arm.PublicKey

open VG VG.Arm VG.Impl.Ed448.Arm.PublicKey VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR Whole.valid Whole.call_ok Whole.Ctx.zeroWords
  Whole.base Whole.base_addr Whole.base_top Whole.stack Whole.Saved Whole.entered Whole.saved_ctx
  Whole.saved_words Whole.bodyRd Whole.bodyWr Whole.wrap_ok)
open VG.Proof.X448.Arm (writeW8_apply off_eq_iff)
open VG.Proof.Ed448 (BaseLadderOk)

variable {L : VG.Proof.Ed448.Arm.PublicKey.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- Where the hash, and then the scalar, is. -/
abbrev hq (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : Addr := State.addr L.E + BitVec.ofNat 64 HASH

/-! ## Pruning -/

theorem bytesAt_take57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem pruned_value {m : Mem} {q : Addr} :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt (((m.writeW q (BitVec.ofNat 8 ((m q).toNat &&& 252))).writeW
        (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
          (q + BitVec.ofNat 64 56) (0 : BitVec 8)) q 57) =
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) &&& (2 ^ 448 - 4)) ||| 2 ^ 447 := by
  have ne : ∀ i j, i < 57 → j < 57 → i ≠ j → q + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j :=
    fun i j hi hj h e => h ((off_eq_iff q (by omega) (by omega)).mp e)
  have z : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have ne0 : ∀ j, 0 < j → j < 57 → q + BitVec.ofNat 64 j ≠ q := fun j h1 h2 e =>
    absurd ((off_eq_iff q (d := j) (e := 0) (by omega) (by omega)).mp (e.trans z.symm)) (by omega)
  generalize hm' : ((m.writeW q (BitVec.ofNat 8 ((m q).toNat &&& 252))).writeW
        (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
          (q + BitVec.ofNat 64 56) (0 : BitVec 8) = m'
  have mid : Spec.Ed448.bytesAt m' (q + BitVec.ofNat 64 1) 54 = Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [← hm', Offset.add_add, VG.Proof.X448.Arm.writeW8_apply, ite_eq_right (ne (1 + i) 56 (by omega) (by omega) (by omega)),
      VG.Proof.X448.Arm.writeW8_apply, ite_eq_right (ne (1 + i) 55 (by omega) (by omega) (by omega)), VG.Proof.X448.Arm.writeW8_apply,
      ite_eq_right (ne0 (1 + i) (by omega) (by omega))]
  have e0 : m' q = BitVec.ofNat 8 ((m q).toNat &&& 252) := by
    rw [← hm', VG.Proof.X448.Arm.writeW8_apply, ite_eq_right (ne0 56 (by omega) (by omega)).symm,
      VG.Proof.X448.Arm.writeW8_apply, ite_eq_right (ne0 55 (by omega) (by omega)).symm,
      VG.Proof.X448.Arm.writeW8_apply, ite_eq_left rfl]
  have e55 : m' (q + BitVec.ofNat 64 55) = BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128) := by
    rw [← hm', VG.Proof.X448.Arm.writeW8_apply, ite_eq_right (ne 55 56 (by omega) (by omega) (by omega)),
      VG.Proof.X448.Arm.writeW8_apply, ite_eq_left rfl]
  have e56 : m' (q + BitVec.ofNat 64 56) = BitVec.ofNat 8 0 := by
    rw [← hm', VG.Proof.X448.Arm.writeW8_apply, ite_eq_left rfl]; rfl
  rw [VG.Proof.Ed448.Arm.PublicKey.decodeLE_split, VG.Proof.Ed448.Arm.PublicKey.decodeLE_split, mid, e0, e55, e56]
  have h0 := (m q).isLt
  have h55 := (m (q + BitVec.ofNat 64 55)).isLt
  have hl : (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54).length = 54 := by simp [Spec.Ed448.bytesAt]
  have hM' := Proof.Ed448.decodeLE_lt' (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54)
  rw [hl] at hM'
  have hM : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54) < 2 ^ 432 :=
    Nat.lt_of_lt_of_le hM' (Nat.le_of_eq (by decide +kernel))
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left h0),
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 8) h55 (by decide))]
  have kk := Proof.Ed448.prune_bytes (b56 := (m (q + BitVec.ofNat 64 56)).toNat) h0 hM h55
  exact kk.symm

theorem prune_step (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) :
    WP isa prune t fun u => VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem (VG.Proof.Ed448.Arm.PublicKey.hq L) 57) =
        Spec.Ed448.prune (Spec.Ed448.bytesAt t.mem (VG.Proof.Ed448.Arm.PublicKey.hq L) 114) := by
  unfold prune
  refine WP.seq (VG.Proof.X25519.Arm.WP.cons (s' := t.setReg .r12 (t.sp + BitVec.ofNat 32 HASH))
    (by simp [exec, HASH]) (WP.block_nil ?_))
  have hsp := hc.sp
  have ht := hL.top
  have e12 : (t.setReg .r12 (t.sp + BitVec.ofNat 32 HASH)).gpr .r12 = L.E + BitVec.ofNat 32 HASH := by
    simp [State.setReg, hsp]
  refine WP.mono (VG.Proof.Ed448.Arm.PublicKey.pruneOps_ok (q := VG.Proof.Ed448.Arm.PublicKey.hq L) (by rw [e12]; exact VG.Proof.Ed448.Arm.PublicKey.hash_addr hL)
    (by rw [e12, BitVec.toNat_add_of_lt (by change L.E.toNat + 24 < 2 ^ 32; omega)]
        change L.E.toNat + 24 + 57 ≤ 2 ^ 32; omega)
    (fun j hj => by
      have h := hc.writable_frame (Offset.contains_base (State.addr L.E) (d := HASH + j) (n := 1)
        (k := 248) (by simp only [HASH]; omega) (by simp only [HASH]; omega))
      rw [← Offset.add_add] at h
      exact h))
    fun u ⟨um, usp, urd, uwr, ug⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame urd uwr usp ?_ (ws := [⟨VG.Proof.Ed448.Arm.PublicKey.hq L, 57⟩]) ?_ ?_
    · intro r hr _
      rw [ug r (by rintro rfl; simp [preserved] at hr)]
      exact RegUpd.gpr_setReg_of_ne _ _ (by rintro rfl; simp [preserved] at hr)
    · rw [um]
      refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
        ?_).writeW (List.mem_singleton_self _) _ ?_
      · have h := Offset.contains_base (VG.Proof.Ed448.Arm.PublicKey.hq L) (d := 0) (n := 1) (k := 57) (by omega) (by omega)
        rw [show VG.Proof.Ed448.Arm.PublicKey.hq L + BitVec.ofNat 64 0 = VG.Proof.Ed448.Arm.PublicKey.hq L from BitVec.add_zero _] at h
        exact h
      · exact Offset.contains_base _ (by omega) (by omega)
      · exact Offset.contains_base _ (by omega) (by omega)
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by simp only [HASH]; omega))
  · rw [um, VG.Proof.Ed448.Arm.PublicKey.pruned_value]
    unfold Spec.Ed448.prune
    rw [VG.Proof.Ed448.Arm.PublicKey.bytesAt_take57]
    rfl

/-! ## `vg_ed448_scalar_base` -/

theorem base_noFrames : Impl.Ed448.Arm.scalarBase.noFrames = true := by lit_decide

def BaseArgs (L : VG.Proof.Ed448.Arm.PublicKey.Lay) (t : State) : Prop :=
  t.gpr .r0 = L.out ∧ t.gpr .r1 = L.E + BitVec.ofNat 32 HASH ∧ t.gpr .r2 = L.scr

theorem base_pre (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.BaseArgs L t) :
    scalarBaseLocal.pre (t.callEntry.withRegions [⟨VG.Proof.Ed448.Arm.PublicKey.hq L, 57⟩] L.outputs) := by
  obtain ⟨h0, h1, h2⟩ := ha
  have e0 : (t.callEntry.withRegions [⟨VG.Proof.Ed448.Arm.PublicKey.hq L, 57⟩] L.outputs).gpr .r0 = L.out := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), h0]
  have e1 : (t.callEntry.withRegions [⟨VG.Proof.Ed448.Arm.PublicKey.hq L, 57⟩] L.outputs).gpr .r1 = L.E + BitVec.ofNat 32 HASH := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), h1]
  have e2 : (t.callEntry.withRegions [⟨VG.Proof.Ed448.Arm.PublicKey.hq L, 57⟩] L.outputs).gpr .r2 = L.scr := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h2]
  simp only [scalarBaseLocal]
  rw [e0, e1, e2, State.withRegions_rd, State.withRegions_wr, VG.Proof.Ed448.Arm.PublicKey.hash_addr hL]
  have h := hL.top
  refine ⟨rfl, rfl, hL.oc, hL.kc.sub_left (Offset.sub_base _ (by decide : 24 + 57 ≤ 280)), hL.no, ?_, hL.nc⟩
  rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 24 < 2 ^ 32; omega)]
  change L.E.toNat + 24 + 57 ≤ 2 ^ 32
  omega

theorem base_covers (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : Covers ([⟨VG.Proof.Ed448.Arm.PublicKey.hq L, 57⟩] ++ L.outputs) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨Whole.FR L.E, List.mem_append_right _ List.mem_cons_self, 24, rfl, by change 24 + 57 ≤ 248; decide⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

theorem base_writes (L : VG.Proof.Ed448.Arm.PublicKey.Lay) : ∀ r ∈ L.outputs,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

def baseValues : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .frame HASH), (.r2, .caller 2 0)]

theorem base_step (hl : BaseLadderOk) (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₀) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase) t fun u =>
      VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧ Spec.Ed448.bytesAt u.mem (State.addr L.out) 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem (VG.Proof.Ed448.Arm.PublicKey.hq L) 57) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.setup_ok hc hL ha (args := VG.Proof.Ed448.Arm.PublicKey.baseValues) (stk := [])
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues, Whole.valid, HASH]) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues]) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues, preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, hm, hav, _⟩ => ?_)
  have h0 := hav (.r0, .caller 0 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues])
  have h1 := hav (.r1, .frame HASH) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues])
  have h2 := hav (.r2, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues])
  simp only [VG.Proof.Ed448.Arm.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have he : Spec.Ed448.bytesAt u.mem (VG.Proof.Ed448.Arm.PublicKey.hq L) 57 = Spec.Ed448.bytesAt t.mem (VG.Proof.Ed448.Arm.PublicKey.hq L) 57 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => hm.bytes (R := ⟨VG.Proof.Ed448.Arm.PublicKey.hq L, 57⟩) ?_
      (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine Whole.call_ok hu (scalarBase_ok hl) VG.Proof.Ed448.Arm.PublicKey.base_noFrames (VG.Proof.Ed448.Arm.PublicKey.base_pre hL ⟨h0, h1, h2⟩) (VG.Proof.Ed448.Arm.PublicKey.base_covers L)
    (VG.Proof.Ed448.Arm.PublicKey.base_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  change Spec.Ed448.bytesAt v.mem (State.addr (u.callEntry.gpr .r0)) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r1)) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), h0, h1, VG.Proof.Ed448.Arm.PublicKey.hash_addr hL, he] at hp
  exact hp

/-! ## The frame, cleared -/

theorem wipe_step (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 57 = Spec.Ed448.bytesAt t.mem (State.addr L.out) 57 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 6) (count := 56) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 4 * 6 + 4 * 56 ≤ 280))).symm

/-! ## The body -/

theorem body_ok (hl : BaseLadderOk) (hc : VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₀) :
    WP isa body t fun u => VG.Proof.Ed448.Arm.PublicKey.Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 57 =
        Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.hash_ok hc hL ha) fun u ⟨hu, hh⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.prune_step hu hL) fun u' ⟨hu', hs⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.PublicKey.base_step hl hu' hL ha) fun u'' ⟨hu'', hp⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.Arm.PublicKey.wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, ?_⟩
  rw [hm, hp, Spec.Ed448.scalarBase, hs, hh]
  rfl

theorem body_noFrames : body.noFrames = true := by
  simp only [body, Impl.Ed448.Arm.PublicKey.hash, zeroState, prune, callWith, Code.noFrames, Bool.and_self]
  rw [VG.Proof.Ed448.Arm.PublicKey.absorb_noFrames, VG.Proof.Ed448.Arm.PublicKey.pad_noFrames, VG.Proof.Ed448.Arm.PublicKey.squeeze_noFrames, VG.Proof.Ed448.Arm.PublicKey.base_noFrames]
  rfl

/-! ## The whole function -/

/-- `vg_ed448_public_key(out = r0, seed = r1, scratch = r2)`, with 280 bytes of stack. -/
def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 57⟩
    let scr : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    s.rd = [seed] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat
  post s t := Spec.Ed448.bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2

def lay (s : State) : VG.Proof.Ed448.Arm.PublicKey.Lay := ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, Whole.base s⟩

theorem lay_ok {s : State} (h : pkLocal.pre s) : (VG.Proof.Ed448.Arm.PublicKey.lay s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hb⟩ := h
  have he := Whole.base_addr hb
  have top := Whole.base_top hb
  have hs := s.sp.isLt
  refine ⟨by change (Whole.base s).toNat + 272 ≤ 2 ^ 32; omega, os, oc, sc, ?_, ?_, ?_, no, ns, nc⟩
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact ko
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact ks
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact kc

theorem entry_below {s : State} (h : pkLocal.pre s) : 280 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2

theorem entry_writes {s : State} (h : pkLocal.pre s) :
    ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (VG.Proof.Ed448.Arm.PublicKey.lay_ok h).ko
  · exact (VG.Proof.Ed448.Arm.PublicKey.lay_ok h).kc

theorem entry_ctx {s p : State} (h : pkLocal.pre s) (hp : Whole.Saved (Whole.entered s) 3 p) :
    VG.Proof.Ed448.Arm.PublicKey.Ctx (VG.Proof.Ed448.Arm.PublicKey.lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, VG.Proof.Ed448.Arm.PublicKey.Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, VG.Proof.Ed448.Arm.PublicKey.lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hs : 280 ≤ s.sp.toNat) (hp : Whole.Saved (Whole.entered s) 3 p) :
    VG.Proof.Ed448.Arm.PublicKey.Arguments (VG.Proof.Ed448.Arm.PublicKey.lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hs (by decide : 3 ≤ 6)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt) hp hj
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases he with rfl | rfl | rfl <;> exact hw

theorem publicKey_ok (hl : BaseLadderOk) {s : State} (h : pkLocal.pre s) :
    WP isa VG.Impl.Ed448.Arm.PublicKey.code s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := Whole.wrap_ok VG.Proof.Ed448.Arm.PublicKey.body_noFrames (by decide : 3 ≤ 6) (VG.Proof.Ed448.Arm.PublicKey.entry_below h)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt)
    (by intro j hj h4; omega) (VG.Proof.Ed448.Arm.PublicKey.entry_writes h)
    (P := fun m m' _ => Spec.Ed448.bytesAt m' (State.addr (s.gpr .r0)) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m (State.addr (s.gpr .r1)) 57))
    (fun p hp => WP.mono (VG.Proof.Ed448.Arm.PublicKey.body_ok hl (VG.Proof.Ed448.Arm.PublicKey.entry_ctx h hp) (VG.Proof.Ed448.Arm.PublicKey.lay_ok h) (VG.Proof.Ed448.Arm.PublicKey.entry_args (VG.Proof.Ed448.Arm.PublicKey.entry_below h) hp))
      fun u ⟨hu, ho⟩ => ⟨by
        simpa only [Whole.bodyRd, h.1, VG.Proof.Ed448.Arm.PublicKey.Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
          Lay.SCR, Lay.ARGS, VG.Proof.Ed448.Arm.PublicKey.lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed448.bytesAt m (State.addr (s.gpr .r1)) 57 =
      Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨State.addr (s.gpr .r1), 57⟩) ?_
      (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (VG.Proof.Ed448.Arm.PublicKey.lay_ok h).ks.symm
  change Spec.Ed448.bytesAt u.mem (State.addr (s.gpr .r0)) 57 = _
  rw [hp, hs]

end VG.Proof.Ed448.Arm.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Verified`. -/
section

/-!
# Ed448 public-key derivation on ARMv7: constant time, and `Verified`

As Ed25519's on this target (`Proof/Ed25519/Arm/PublicKey/Verified.lean`):
two runs from the same pointers and `sp` set up the same arguments for every
call (`setup_ct`), each callee is constant time under its own contract
(`call_ct`), and the blocks between the calls address memory only through
`sp`, `scratch` and the frame (`zero_ct`, `prune_ct`, `wipe_ct`).
`publicKey_verified` takes the reference ladder's agreement with the
specification (`BaseLadderOk`) as a hypothesis.
-/

namespace VG.Proof.Ed448.Arm.PublicKey

open VG VG.Arm VG.Impl.Ed448.Arm.PublicKey VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.rel_wp Whole.setup_ct Whole.callEx Whole.CallReady
  Whole.block_cons_ct Whole.block_nil_ct Whole.zeroWords_ct Whole.wrap_ct Whole.base
  Whole.bodyRd Whole.bodyWr Whole.valid)
open VG.Proof.Ed448 (BaseLadderOk)

/-! ## Relational frame -/

abbrev Two (L : VG.Proof.Ed448.Arm.PublicKey.Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) := (VG.Proof.Ed448.Arm.PublicKey.Ctx L g₁ m₁ a ∧ P a) ∧ (VG.Proof.Ed448.Arm.PublicKey.Ctx L g₂ m₂ b ∧ P b)

def Slots (L : VG.Proof.Ed448.Arm.PublicKey.Lay) (args : List (Reg × Value)) (stk : List Value) (s : State) :=
  (∀ p ∈ args, s.gpr p.1 = VG.Proof.Ed448.Arm.PublicKey.argValue L p.2) ∧ ∀ j (hj : j < stk.length), stackArg s j = VG.Proof.Ed448.Arm.PublicKey.argValue L (stk[j]'hj)

variable {L : VG.Proof.Ed448.Arm.PublicKey.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₂)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, Whole.valid v)
    (his : ∀ v ∈ stk, ∀ j d, v = .caller j d → j < 3) :
    RelCT isa (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stk))
      (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.PublicKey.Slots L args stk)) := by
  refine Whole.rel_wp ((Whole.setup_ct args stk).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed448.Arm.PublicKey.setup_ok hc hL ha hn hv hi hr hs hvs his) fun _ ⟨hc, _, hg, ht⟩ => ⟨hc, hg, ht⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed448.Arm.PublicKey.setup_ok hc hL hb hn hv hi hr hs hvs his) fun _ ⟨hc, _, hg, ht⟩ => ⟨hc, hg, ht⟩

theorem call_ct {args : List (Reg × Value)} {stk : List Value} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hn : c.noFrames = true)
    (ready : ∀ t, t.sp = L.E → VG.Proof.Ed448.Arm.PublicKey.Slots L args stk t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      (∀ j < stk.length, stackArg a j = stackArg b j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.PublicKey.Slots L args stk)) (.call name c)
      (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ?_ ?_ ?_
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready a h.1.1.sp h.1.2
    let rb := ready b h.2.1.sp h.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (h.1.1.sp.trans h.2.1.sp.symm) ?_ ?_, ca, wa, cb, wb⟩
    · intro p hp
      rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2.1 p hp, h.2.2.1 p hp]
    · intro j hj
      exact (h.1.2.2 j hj).trans (h.2.2.2 j hj).symm
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wp hc correct hn) fun _ hu => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wp hc correct hn) fun _ hu => ⟨hu, trivial⟩

/-! ## The calls -/

section
variable {t : State}

def abs_ready (hL : L.Ok) (he : t.sp = L.E) (hs : VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.absValues VG.Proof.Ed448.Arm.PublicKey.absStack t) :
    Whole.CallReady Proof.Sha3.absorbArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues])
  have h1 := hs.1 (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues])
  have h2 := hs.1 (.r2, .const 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues])
  have h3 := hs.1 (.r3, .caller 1 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues])
  have a0 := hs.2 0 (by decide)
  have a1 := hs.2 1 (by decide)
  simp only [VG.Proof.Ed448.Arm.PublicKey.absStack, VG.Proof.Ed448.Arm.PublicKey.argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  exact ⟨VG.Proof.Ed448.Arm.PublicKey.absRd L, VG.Proof.Ed448.Arm.PublicKey.kWr L, VG.Proof.Ed448.Arm.PublicKey.abs_pre hL he h0 h1 h2 h3 a0 a1, VG.Proof.Ed448.Arm.PublicKey.abs_covers L, VG.Proof.Ed448.Arm.PublicKey.kWr_writes L⟩

def pad_ready (hL : L.Ok) (he : t.sp = L.E) (hs : VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.padValues VG.Proof.Ed448.Arm.PublicKey.padStack t) :
    Whole.CallReady Proof.Sha3.padArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues])
  have h1 := hs.1 (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues])
  have h2 := hs.1 (.r2, .const 57) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues])
  have a0 := hs.2 0 (by decide)
  simp only [VG.Proof.Ed448.Arm.PublicKey.padStack, VG.Proof.Ed448.Arm.PublicKey.argValue, Lay.value, List.getElem_cons_zero, BitVec.add_zero] at h0 h1 h2 a0
  exact ⟨[VG.Proof.Ed448.Arm.PublicKey.kArgs L 4], VG.Proof.Ed448.Arm.PublicKey.kWr L, VG.Proof.Ed448.Arm.PublicKey.pad_pre hL he h0 h1 h2 a0, VG.Proof.Ed448.Arm.PublicKey.pad_covers L, VG.Proof.Ed448.Arm.PublicKey.kWr_writes L⟩

def sqz_ready (hL : L.Ok) (he : t.sp = L.E) (hs : VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.sqzValues VG.Proof.Ed448.Arm.PublicKey.sqzStack t) :
    Whole.CallReady Proof.Sha3.squeezeArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues])
  have h1 := hs.1 (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues])
  have h2 := hs.1 (.r2, .const 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues])
  have h3 := hs.1 (.r3, .frame HASH) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues])
  have a0 := hs.2 0 (by decide)
  have a1 := hs.2 1 (by decide)
  simp only [VG.Proof.Ed448.Arm.PublicKey.sqzStack, VG.Proof.Ed448.Arm.PublicKey.argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  exact ⟨[VG.Proof.Ed448.Arm.PublicKey.kArgs L 8], VG.Proof.Ed448.Arm.PublicKey.sqzWr L, VG.Proof.Ed448.Arm.PublicKey.sqz_pre hL he h0 h1 h2 h3 a0 a1, VG.Proof.Ed448.Arm.PublicKey.sqz_covers L, VG.Proof.Ed448.Arm.PublicKey.sqz_writes L⟩

def base_ready (hL : L.Ok) (hs : VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.baseValues [] t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 0 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues])
  have h1 := hs.1 (.r1, .frame HASH) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues])
  have h2 := hs.1 (.r2, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues])
  simp only [VG.Proof.Ed448.Arm.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨VG.Proof.Ed448.Arm.PublicKey.hq L, 57⟩], L.outputs, VG.Proof.Ed448.Arm.PublicKey.base_pre hL ⟨h0, h1, h2⟩, VG.Proof.Ed448.Arm.PublicKey.base_covers L, VG.Proof.Ed448.Arm.PublicKey.base_writes L⟩

end

theorem abs_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.absValues VG.Proof.Ed448.Arm.PublicKey.absStack))
    (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.Arm.Stream.absorb) (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed448.Arm.PublicKey.call_ct Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1
    Proof.Sha3.Arm.Stream.Absorb.absorb_verified.2.1 VG.Proof.Ed448.Arm.PublicKey.absorb_noFrames (fun _ he h => VG.Proof.Ed448.Arm.PublicKey.abs_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues]), hg (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues]),
      hg (.r2, .const 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues]), hg (.r3, .caller 1 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues]),
      ht 0 (by decide), ht 1 (by decide)⟩
  · simp [VG.Proof.Ed448.Arm.PublicKey.absValues, linkRegs]

theorem pad_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.padValues VG.Proof.Ed448.Arm.PublicKey.padStack))
    (.call Spec.Sha3.padScratchApi.name Impl.Sha3.Arm.Stream.pad) (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed448.Arm.PublicKey.call_ct Proof.Sha3.Arm.Stream.Pad.pad_verified.1
    Proof.Sha3.Arm.Stream.Pad.pad_verified.2.1 VG.Proof.Ed448.Arm.PublicKey.pad_noFrames (fun _ he h => VG.Proof.Ed448.Arm.PublicKey.pad_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues]), hg (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues]),
      hg (.r2, .const 57) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues]), hg (.r3, .const 0x1f) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues]),
      ht 0 (by decide)⟩
  · simp [VG.Proof.Ed448.Arm.PublicKey.padValues, linkRegs]

theorem sqz_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.sqzValues VG.Proof.Ed448.Arm.PublicKey.sqzStack))
    (.call Spec.Sha3.squeezeScratchApi.name Impl.Sha3.Arm.Stream.squeeze) (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed448.Arm.PublicKey.call_ct Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1
    Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.2.1 VG.Proof.Ed448.Arm.PublicKey.squeeze_noFrames (fun _ he h => VG.Proof.Ed448.Arm.PublicKey.sqz_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues]), hg (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues]),
      hg (.r2, .const 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues]), hg (.r3, .frame HASH) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues]),
      ht 0 (by decide), ht 1 (by decide)⟩
  · simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues, linkRegs]

theorem base_ct (hl : BaseLadderOk) (hL : L.Ok) : RelCT isa (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.baseValues []))
    (.call "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase) (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed448.Arm.PublicKey.call_ct (scalarBase_ok hl) scalarBase_ct VG.Proof.Ed448.Arm.PublicKey.base_noFrames (fun _ _ h => VG.Proof.Ed448.Arm.PublicKey.base_ready hL h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hg (.r0, .caller 0 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues]), hg (.r1, .frame HASH) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues]),
      hg (.r2, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues]), hsp⟩
  · simp [VG.Proof.Ed448.Arm.PublicKey.baseValues, linkRegs]

/-! ## The blocks -/

/-- Stores through `r0`, which they leave alone. -/
theorem stores_ct (ks : List Nat) :
    RelCT isa (fun a b => a.gpr .r0 = b.gpr .r0) (.block (ks.map fun k => Instr.str .r1 .r0 (4 * k)))
      (fun a b => a.gpr .r0 = b.gpr .r0) := by
  induction ks with
  | nil => exact Whole.block_nil_ct
  | cons k ks ih =>
    refine Whole.block_cons_ct (fun a b a' b' hp ea eb => ⟨by simp only [addrs, hp], ?_⟩) ih
    rw [exec_gpr (by simp [dstOf]) ea, exec_gpr (by simp [dstOf]) eb, hp]

theorem zero_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.zeroValues []))
    (.block zeroStores) (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have r0 : ∀ {s : State}, VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.zeroValues [] s → s.gpr .r0 = L.scr := fun hs => by
    have h := hs.1 (.r0, .caller 2 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.zeroValues])
    simpa only [VG.Proof.Ed448.Arm.PublicKey.argValue, Lay.value, BitVec.add_zero] using h
  have r1 : ∀ {s : State}, VG.Proof.Ed448.Arm.PublicKey.Slots L VG.Proof.Ed448.Arm.PublicKey.zeroValues [] s → s.gpr .r1 = 0 := fun hs => by
    have h := hs.1 (.r1, .const 0) (by simp [VG.Proof.Ed448.Arm.PublicKey.zeroValues])
    exact h
  refine Whole.rel_wp ((VG.Proof.Ed448.Arm.PublicKey.stores_ct (List.range 50)).mono
    (fun _ _ h => (r0 h.1.2).trans (r0 h.2.2).symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, hs⟩
    exact WP.mono (VG.Proof.Ed448.Arm.PublicKey.zeroStores_step hc hL (r0 hs) (r1 hs)) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono (VG.Proof.Ed448.Arm.PublicKey.zeroStores_step hc hL (r0 hs) (r1 hs)) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-- Instructions that address memory only through `r12`, and leave it alone. -/
theorem r12_ct (is : List Instr) (hd : ∀ i ∈ is, dstOf i ≠ some .r12)
    (ha : ∀ i ∈ is, ∀ a b : State, a.gpr .r12 = b.gpr .r12 → addrs i a = addrs i b) :
    RelCT isa (fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12) (.block is)
      (fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12) := by
  induction is with
  | nil => exact Whole.block_nil_ct
  | cons i is ih =>
    refine Whole.block_cons_ct (fun a b a' b' hp ea eb => ⟨ha i List.mem_cons_self a b hp.2,
      (exec_sp ea).trans (hp.1.trans (exec_sp eb).symm), ?_⟩)
      (ih (fun j hj => hd j (List.mem_cons_of_mem _ hj)) (fun j hj => ha j (List.mem_cons_of_mem _ hj)))
    rw [exec_gpr (hd i List.mem_cons_self) ea, exec_gpr (hd i List.mem_cons_self) eb, hp.2]

theorem prune_sp_ct : RelCT isa (fun a b => a.sp = b.sp) prune (fun a b => a.sp = b.sp) := by
  unfold prune
  refine RelCT.seq (M := isa) (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12) ?_
    ((VG.Proof.Ed448.Arm.PublicKey.r12_ct pruneOps (by decide) ?_).mono (fun _ _ h => h) (fun _ _ h => h.1))
  · refine Whole.block_cons_ct (fun a b a' b' hp ea eb => ?_) Whole.block_nil_ct
    simp only [exec, HASH, show 24 < 256 from by decide, ite_true, Option.some.injEq] at ea eb
    subst a' b'
    exact ⟨rfl, hp, congrArg (· + BitVec.ofNat 32 24) hp⟩
  · intro i hi a b h
    simp only [pruneOps, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [addrs, h]

theorem prune_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) prune
    (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (prune_sp_ct.mono (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
    (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed448.Arm.PublicKey.prune_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed448.Arm.PublicKey.prune_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
    (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ((Whole.zeroWords_ct 6 56).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (VG.Proof.Ed448.Arm.PublicKey.wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (VG.Proof.Ed448.Arm.PublicKey.wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-! ## The whole function -/

theorem body_ct (hl : BaseLadderOk) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.PublicKey.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) body (VG.Proof.Ed448.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have z := VG.Proof.Ed448.Arm.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb VG.Proof.Ed448.Arm.PublicKey.zeroValues []
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.zeroValues, Whole.valid]) (by simp [VG.Proof.Ed448.Arm.PublicKey.zeroValues])
    (by simp [VG.Proof.Ed448.Arm.PublicKey.zeroValues, preserved]) (by decide) (by simp) (by simp)
  have a := VG.Proof.Ed448.Arm.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb VG.Proof.Ed448.Arm.PublicKey.absValues VG.Proof.Ed448.Arm.PublicKey.absStack
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues, Whole.valid]) (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues])
    (by simp [VG.Proof.Ed448.Arm.PublicKey.absValues, preserved]) (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.absStack, Whole.valid, KSCR])
    (by simp [VG.Proof.Ed448.Arm.PublicKey.absStack])
  have p := VG.Proof.Ed448.Arm.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb VG.Proof.Ed448.Arm.PublicKey.padValues VG.Proof.Ed448.Arm.PublicKey.padStack
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues, Whole.valid]) (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues])
    (by simp [VG.Proof.Ed448.Arm.PublicKey.padValues, preserved]) (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.padStack, Whole.valid, KSCR])
    (by simp [VG.Proof.Ed448.Arm.PublicKey.padStack])
  have q := VG.Proof.Ed448.Arm.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb VG.Proof.Ed448.Arm.PublicKey.sqzValues VG.Proof.Ed448.Arm.PublicKey.sqzStack
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues, Whole.valid, HASH]) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues])
    (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzValues, preserved]) (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzStack, Whole.valid, KSCR])
    (by simp [VG.Proof.Ed448.Arm.PublicKey.sqzStack])
  have b := VG.Proof.Ed448.Arm.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb VG.Proof.Ed448.Arm.PublicKey.baseValues []
    (by decide) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues, Whole.valid, HASH]) (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues])
    (by simp [VG.Proof.Ed448.Arm.PublicKey.baseValues, preserved]) (by decide) (by simp) (by simp)
  exact ((z.seq (VG.Proof.Ed448.Arm.PublicKey.zero_ct hL)).seq ((a.seq (VG.Proof.Ed448.Arm.PublicKey.abs_ct hL)).seq ((p.seq (VG.Proof.Ed448.Arm.PublicKey.pad_ct hL)).seq (q.seq (VG.Proof.Ed448.Arm.PublicKey.sqz_ct hL))))).seq
    ((VG.Proof.Ed448.Arm.PublicKey.prune_ct hL).seq ((b.seq (VG.Proof.Ed448.Arm.PublicKey.base_ct hl hL)).seq (VG.Proof.Ed448.Arm.PublicKey.wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : VG.Proof.Ed448.Arm.PublicKey.lay s = VG.Proof.Ed448.Arm.PublicKey.lay t := by
  obtain ⟨sp, h0, h1, h2⟩ := hp
  simp only [VG.Proof.Ed448.Arm.PublicKey.lay, Whole.base, sp, h0, h1, h2]

theorem publicKey_ct (hl : BaseLadderOk) : ConstantTime isa pkLocal.pre pkLocal.pub VG.Impl.Ed448.Arm.PublicKey.code := by
  refine Whole.wrap_ct (by decide : 3 ≤ 6) (fun _ _ hp => hp.1)
    (fun _ hs => VG.Proof.Ed448.Arm.PublicKey.entry_below hs) ?_ (by intro s hs j hj h4; omega) ?_ ?_
  · intro s _
    simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_of_lt s.sp.isLt
  · intro s hs p hp
    exact WP.mono (VG.Proof.Ed448.Arm.PublicKey.body_ok hl (VG.Proof.Ed448.Arm.PublicKey.entry_ctx hs hp) (VG.Proof.Ed448.Arm.PublicKey.lay_ok hs) (VG.Proof.Ed448.Arm.PublicKey.entry_args (VG.Proof.Ed448.Arm.PublicKey.entry_below hs) hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := VG.Proof.Ed448.Arm.PublicKey.lay_eq hp
    have hq : VG.Proof.Ed448.Arm.PublicKey.Ctx (VG.Proof.Ed448.Arm.PublicKey.lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ VG.Proof.Ed448.Arm.PublicKey.entry_ctx ht hqb
    have hqa : VG.Proof.Ed448.Arm.PublicKey.Arguments (VG.Proof.Ed448.Arm.PublicKey.lay s) q.mem := he ▸ VG.Proof.Ed448.Arm.PublicKey.entry_args (VG.Proof.Ed448.Arm.PublicKey.entry_below ht) hqb
    exact ⟨(VG.Proof.Ed448.Arm.PublicKey.body_ct hl (VG.Proof.Ed448.Arm.PublicKey.lay_ok hs) (VG.Proof.Ed448.Arm.PublicKey.entry_args (VG.Proof.Ed448.Arm.PublicKey.entry_below hs) hpa) hqa _ _ _ _ _ _
      ⟨⟨VG.Proof.Ed448.Arm.PublicKey.entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩]

theorem pk_implies : pkLocal.Implies (Spec.Ed448.publicKeyContract Arm.abi 280) := by
  sig_implies [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
    Spec.Ed448.scratchWords, VG.Proof.Ed448.Arm.PublicKey.pkLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [satState] using VG.Proof.Ed448.Arm.PublicKey.satState

/-- `vg_ed448_public_key` on ARMv7, given the reference ladder's agreement
with the specification. -/
theorem publicKey_verified (hl : BaseLadderOk) :
    Verified Arm.target VG.Impl.Ed448.Arm.PublicKey.code (Spec.Ed448.publicKeyContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => VG.Proof.Ed448.Arm.PublicKey.publicKey_ok hl h) (VG.Proof.Ed448.Arm.PublicKey.publicKey_ct hl) (.refl pk_implies.sat_left))
    VG.Proof.Ed448.Arm.PublicKey.pk_implies

end VG.Proof.Ed448.Arm.PublicKey

end
