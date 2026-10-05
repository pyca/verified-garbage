import VerifiedGarbage.Proof.Ed448.X86.Shake.Layout
import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT
import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Impl.Ed448.X86.Shake

/-!
# Ed448 on x86 (32-bit): the calls of the sponge functions

The Keccak state zeroed (`Kit.zero_ok`), and each call of a sponge function
through `Whole.call_ok` with its own contract (`Proof.Sha3.absorbX86`,
`padX86`, `squeezeX86`), from its set-up (`Kit.first_abs`, `Kit.next_abs`,
`Kit.pad_step`, `Kit.sqz_step`), for any layout (`Kit`) with `scratch` the
caller's argument `sc` (`ScrAt`). An absorption reads its data from the
frame, an input or an output (`DataOk`) outside what the calls write
(`Away`); each after the first starts at the position the previous one
returned in `eax`. Each step states the regions it may write: `Lo E` (the
outgoing arguments, and the return address and stack of its call), the
state and the working space (`kWr scr`), and the squeezed output.
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86 VG.X86.Wp VG.Impl.Ed448.X86.Shake
open VG.Impl.Ed25519.X86.Whole (Value setup at_)
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed25519.X86 (Whole.CallReady Whole.Ctx Whole.FR Whole.STK Whole.Within Whole.valid Whole.slots Whole.call_ok
  Whole.callEntry_frame Whole.arg_base)

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t u : State}

/-- `scratch` is the caller's argument `sc`. -/
structure ScrAt (n : Nat) (val : Nat → BitVec 32) (sc : Nat) (scr : BitVec 32) : Prop where
  lt : sc < n
  val : val sc = scr

theorem ScrAt.valid {sc : Nat} (h : ScrAt n val sc scr) (d : Nat) : Whole.valid n (.caller sc d) := h.lt

theorem absorb_stack : stackUse Impl.Sha3.X86.Stream.absorb = 12 := by decide +kernel
theorem pad_stack : stackUse Impl.Sha3.X86.Stream.pad = 12 := by decide +kernel
theorem squeeze_stack : stackUse Impl.Sha3.X86.Stream.squeeze = 12 := by decide +kernel

theorem nosp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem nosp_ite {c : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite c a b) :=
  nosp_seq (a := a) (b := b) ha hb

/-- The calls of the permutation do not write `esp`, from the permutation's
own `permute_nosp`, rather than by evaluating its code again. -/
theorem permuteCall_nosp (st scr : Reg) : NoSp (Impl.Sha3.X86.Stream.permuteCall st scr) := by
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · rfl
  rcases List.mem_append.mp hi with hi | hi
  · exact Proof.Sha3.X86.permute_nosp i hi
  · rw [List.mem_singleton.mp hi]; rfl

theorem next_nosp : NoSp Impl.Sha3.X86.Stream.next :=
  nosp_ite (nosp_seq (NoSp.of_all (by decide +kernel)) (permuteCall_nosp _ _)) (NoSp.of_all (by decide +kernel))

theorem absorb_nosp : NoSp Impl.Sha3.X86.Stream.absorb :=
  nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_seq (nosp_ite (NoSp.of_all (by decide +kernel))
    (nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_seq next_nosp (NoSp.of_all (by decide +kernel)))))
    (NoSp.of_all (by decide +kernel)))

theorem pad_nosp : NoSp Impl.Sha3.X86.Stream.pad :=
  nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_seq (permuteCall_nosp _ _) (NoSp.of_all (by decide +kernel)))

theorem squeeze_nosp : NoSp Impl.Sha3.X86.Stream.squeeze :=
  nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_seq (nosp_ite (NoSp.of_all (by decide +kernel))
    (nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_seq next_nosp (NoSp.of_all (by decide +kernel)))))
    (NoSp.of_all (by decide +kernel)))

theorem absorb_nosp' {args : List Instr} (h : NoSp (.block args)) : NoSp (absorb args) :=
  nosp_seq h absorb_nosp

theorem pad_nosp' {sc : Nat} (h : NoSp (.block (padArgs sc))) : NoSp (pad sc) :=
  nosp_seq h pad_nosp

theorem squeeze_nosp' {sc d : Nat} (h : NoSp (.block (sqzArgs sc d))) : NoSp (squeeze sc d) :=
  nosp_seq h squeeze_nosp

/-! ## The regions -/

/-- The state and the sponge functions' working space. -/
def kWr (scr : BitVec 32) : List Region :=
  [⟨scr.setWidth 64, 200⟩, ⟨(scr + BitVec.ofNat 32 KSCR).setWidth 64, 640⟩]

theorem kWr_state (scr : BitVec 32) : (⟨scr.setWidth 64, 200⟩ : Region) ∈ kWr scr := List.mem_cons_self
theorem kWr_scratch (scr : BitVec 32) : (⟨(scr + BitVec.ofNat 32 KSCR).setWidth 64, 640⟩ : Region) ∈ kWr scr :=
  List.mem_cons_of_mem _ List.mem_cons_self

/-- Data an absorption may read: in the frame, or in an input or an output. -/
def DataOk (E : BitVec 32) (ins outs : List Region) (D : Region) : Prop :=
  Whole.Within D (Whole.FR E) ∨ ∃ R ∈ ins ++ outs, Whole.Within D R

/-- Outside what a call of a sponge function writes but its squeezed output. -/
structure Away (E scr : BitVec 32) (D : Region) : Prop where
  lo : (Lo E).Disjoint D
  kwr : ∀ r ∈ kWr scr, D.Disjoint r

theorem lo_off (E : BitVec 32) {d : Nat} (hd : d ≤ 24) :
    E.setWidth 64 - BitVec.ofNat 64 d = E.setWidth 64 - 24 + BitVec.ofNat 64 (24 - d) :=
  Offset.sub_ofNat_eq _ hd

/-- A call's return address and the 12 bytes below it, from `E`. -/
theorem ret_lo {E : BitVec 32} (hE : 24 ≤ E.toNat) :
    Region.Sub ⟨(E - 4).setWidth 64, 4⟩ (Lo E) := by
  have e : (E - 4).setWidth 64 = E.setWidth 64 - 24 + BitVec.ofNat 64 20 := by
    rw [show (E - 4) = E - BitVec.ofNat 32 4 from rfl, Taint.sub_setWidth (by omega), lo_off E (by decide)]
  rw [e]
  exact Offset.sub_base _ (by decide)

theorem stk_lo {E : BitVec 32} (hE : 24 ≤ E.toNat) :
    Region.Sub ⟨(E - 4).setWidth 64 - 12, 12⟩ (Lo E) := by
  have e : (E - 4).setWidth 64 - 12 = E.setWidth 64 - 24 + BitVec.ofNat 64 8 := by
    rw [show (E - 4) = E - BitVec.ofNat 32 4 from rfl, Taint.sub_setWidth (by omega),
      show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, BitVec.sub_sub, ← BitVec.ofNat_add,
      lo_off E (by decide)]
  rw [e]
  exact Offset.sub_base _ (by decide)

theorem below4_lo {E : BitVec 32} (hE : 24 ≤ E.toNat) : Region.Sub (below E 4) (Lo E) :=
  fun p hp => below_lo hE p (below_sub (by decide) hE p hp)

theorem covers_of {E : BitVec 32} {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ ins ++ outs, Whole.Within r R) :
    Covers rs (ins ++ Whole.FR E :: outs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases h r hr with hf | ⟨R, hR, hw⟩
  · exact ⟨Whole.FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
  · refine ⟨R, ?_, hw⟩
    rcases List.mem_append.mp hR with hi | ho
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)

theorem args_within (E : BitVec 32) {k : Nat} (hk : k ≤ 256) : Whole.Within ⟨E.setWidth 64, k⟩ (Whole.FR E) :=
  ⟨0, (BitVec.add_zero _).symm, by change 0 + k ≤ 256; omega⟩

theorem frame_within (E : BitVec 32) {d l : Nat} (hd : d + l ≤ 256) : Whole.Within (fr E d l) (Whole.FR E) :=
  ⟨d, rfl, hd⟩

/-- The state, through a step outside it. -/
theorem state_frame {ws : List Region} {m m' : Mem} {p : Addr} (hm : Frame ws m m')
    (hd : ∀ r ∈ ws, (⟨p, 200⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p :=
  Proof.Sha3.stateAt_congr fun _ hj => hm.bytes (R := ⟨p, 200⟩) hd (by change 200 ≤ 2 ^ 64; decide) hj

theorem repr_frame {ws : List Region} {m m' : Mem} {p : Addr} (hm : Frame ws m m')
    (hd : ∀ r ∈ ws, (⟨p, 200⟩ : Region).Disjoint r) {msg : List Byte}
    (h : Spec.Sha3.Repr m p 136 msg) : Spec.Sha3.Repr m' p 136 msg := by
  unfold Spec.Sha3.Repr at h ⊢
  rw [state_frame hm hd]; exact h

/-- After zeroing the first `k` words of the state at `eax`. -/
structure ZInv (scr : BitVec 32) (s₁ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨scr.setWidth 64, 200⟩] s₁.mem s.mem
  zero : ∀ j < k, s.mem.readW (scr.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 = 0

theorem stateAt_zero {m : Mem} (h : ∀ j < 50, m.readW (scr.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 = 0) :
    stateAt m (scr.setWidth 64) = Spec.Sha3.zero := by
  refine Eq.trans (Proof.Sha3.stateAt_congr (m := fun _ => 0) fun j hj => ?_) ?_
  · have e := Mem.readW_byte m (scr.setWidth 64 + BitVec.ofNat 64 (4 * (j / 4))) (i := j % 4) (by omega)
    rw [Offset.add_add, show 4 * (j / 4) + j % 4 = j by omega, h (j / 4) (by omega)] at e
    rw [e]
    apply BitVec.eq_of_toNat_eq
    simp
  · apply Vector.ext
    intro i hi
    simp [stateAt, Spec.Sha3.zero, Mem.readW, Mem.read]

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    Spec.Sha3.squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [Spec.Sha3.squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

theorem shake256_eq (m : List Byte) (d : Nat) :
    Spec.Sha3.shake256 m d =
      Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix m)) 0 d := by
  rw [squeezeFrom_zero]; rfl

theorem length_sbytes (m : Mem) (p : Addr) (k : Nat) : (Spec.Sha3.bytesAt m p k).length = k := by
  simp [Spec.Sha3.bytesAt]

theorem argVal_const (k : Nat) : argVal E val (.const k) = BitVec.ofNat 32 k := rfl
theorem argVal_frame (d : Nat) : argVal E val (.frame d) = E + BitVec.ofNat 32 d := rfl
theorem argVal_caller (i d : Nat) : argVal E val (.caller i d) = val i + BitVec.ofNat 32 d := rfl

/-- Bytes outside the regions a step may write, through it. -/
theorem sframe_bytes {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {D : Region}
    (hd : ∀ r ∈ ws, D.Disjoint r) (hn : D.len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' D.base D.len = Spec.Sha3.bytesAt m D.base D.len := by
  unfold Spec.Sha3.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes hd hn (List.mem_range.mp hi)

/-- The outgoing arguments of an absorption. -/
structure AbsSlots (E scr : BitVec 32) (pos : Nat) (P N : BitVec 32) (s : State) : Prop where
  a0 : Whole.slots E s 0 = scr
  a1 : Whole.slots E s 1 = 136
  a2 : Whole.slots E s 2 = BitVec.ofNat 32 pos
  a3 : Whole.slots E s 3 = P
  a4 : Whole.slots E s 4 = N
  a5 : Whole.slots E s 5 = scr + BitVec.ofNat 32 KSCR

/-- The outgoing arguments of the padding. -/
structure PadSlots (E scr : BitVec 32) (pos : Nat) (s : State) : Prop where
  a0 : Whole.slots E s 0 = scr
  a1 : Whole.slots E s 1 = 136
  a2 : Whole.slots E s 2 = BitVec.ofNat 32 pos
  a3 : Whole.slots E s 3 = BitVec.ofNat 32 0x1f
  a4 : Whole.slots E s 4 = scr + BitVec.ofNat 32 KSCR

/-- The outgoing arguments of a squeeze into the frame at `d`. -/
structure SqzSlots (E scr : BitVec 32) (d : Nat) (s : State) : Prop where
  a0 : Whole.slots E s 0 = scr
  a1 : Whole.slots E s 1 = 136
  a2 : Whole.slots E s 2 = BitVec.ofNat 32 0
  a3 : Whole.slots E s 3 = E + BitVec.ofNat 32 d
  a4 : Whole.slots E s 4 = BitVec.ofNat 32 114
  a5 : Whole.slots E s 5 = scr + BitVec.ofNat 32 KSCR

namespace Kit

variable (hk : Kit E scr n ins outs)
include hk

theorem scr_addr : (scr + BitVec.ofNat 32 KSCR).setWidth 64 = scr.setWidth 64 + BitVec.ofNat 64 KSCR :=
  addr_eq (by have := hk.nc; simp only [KSCR]; omega)

theorem scr_fit : (scr + BitVec.ofNat 32 KSCR).toNat + 640 ≤ 2 ^ 32 := by
  have := hk.nc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := KSCR) (by simp only [KSCR]; omega),
    Nat.mod_eq_of_lt (by simp only [KSCR]; omega)]
  simp only [KSCR]; omega

theorem kWr_sub : ∀ r ∈ kWr scr, Whole.Within r (SCR scr) := by
  intro r hr
  simp only [kWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨0, (BitVec.add_zero _).symm, by change 0 + 200 ≤ 8192; decide⟩
  · exact ⟨KSCR, hk.scr_addr, by change 208 + 640 ≤ 8192; decide⟩

theorem state_scratch : (⟨scr.setWidth 64, 200⟩ : Region).Disjoint
    ⟨(scr + BitVec.ofNat 32 KSCR).setWidth 64, 640⟩ := by
  rw [hk.scr_addr]; exact Offset.base_disjoint _ (by decide) (by decide)

theorem kWr_writes : ∀ r ∈ kWr scr, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R :=
  fun r hr => .inr ⟨SCR scr, hk.so, hk.kWr_sub r hr⟩

theorem kWr_covered : ∀ r ∈ kWr scr, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ ins ++ outs, Whole.Within r R :=
  fun r hr => .inr ⟨SCR scr, List.mem_append_right _ hk.so, hk.kWr_sub r hr⟩

/-- `Lo E` is outside the state and the working space. -/
theorem lo_kWr : ∀ r ∈ kWr scr, (Lo E).Disjoint r :=
  fun r hr => hk.lo_scr.sub_right (hk.kWr_sub r hr).sub

theorem away_fr {d l : Nat} (h24 : 24 ≤ d) (hd : d + l ≤ 256) : Away E scr (fr E d l) :=
  ⟨lo_fr E h24 hd, fun r hr => (hk.fr_scr hd).sub_right (hk.kWr_sub r hr).sub⟩

theorem away_input {R D : Region} (hR : R ∈ ins) (hw : Whole.Within D R) : Away E scr D :=
  ⟨((hk.io R hR (Whole.STK E) (by simp)).sub_left hw.sub).symm.sub_left (lo_sub E),
    fun r hr => ((hk.io R hR (SCR scr) (List.mem_append_left _ hk.so)).sub_left hw.sub).sub_right
      (hk.kWr_sub r hr).sub⟩

theorem away_output {R D : Region} (hR : R ∈ outs) (hRs : R.Disjoint (SCR scr)) (hw : Whole.Within D R) :
    Away E scr D :=
  ⟨((hk.ko R hR).sub_right hw.sub).sub_left (lo_sub E),
    fun r hr => (hRs.sub_left hw.sub).sub_right (hk.kWr_sub r hr).sub⟩

/-! ## The state, zeroed -/

theorem zeroStores_ok {s₁ : State} (h0 : s₁.gpr .eax = scr) (h2 : s₁.gpr .edx = 0)
    (hwr : ∀ k < 50, InRegions s₁.wr (scr.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block zeroStores) s₁ (ZInv scr s₁ 50) := by
  rw [zeroStores, List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa) (ZInv scr s₁) (fun k s hk' h => ?_) 50 (Nat.le_refl _) s₁
    ⟨rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : addr scr (4 * k) = scr.setWidth 64 + BitVec.ofNat 64 (4 * k) :=
    addr_eq (by have := hk.nc; omega)
  have hb : s.gpr .eax = scr := by rw [h.gpr, h0]
  refine wp_stm hb (by rw [ea, h.wr]; exact hwr k hk') fun s' m => WP.block_nil
    ⟨by rw [m.gpr, h.gpr], by rw [m.rd, h.rd], by rw [m.wr, h.wr], ?_, fun j hj => ?_⟩
  · rw [m.mem, ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [m.mem, ea, h.gpr, h2]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.zero j (by omega)

/-- `scratch` into `eax`, `0` into `edx`. -/
theorem zeroArgs_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr) :
    WP isa (.block (zeroArgs sc)) t fun u => Whole.Ctx E g m₀ ins outs u ∧ u.gpr .eax = scr ∧
      u.gpr .edx = 0 ∧ u.mem = t.mem := by
  unfold zeroArgs
  refine wp_ldm (b := .esp) hc.esp (hk.readable hc sc hsc.lt) fun s1 v1 => wp_movi fun s2 v2 => WP.block_nil ?_
  refine ⟨hc.of_frame (by rw [v2.rd, v1.rd]) (by rw [v2.wr, v1.wr])
      (by rw [v2.other _ (by decide), v1.other _ (by decide)]) ?_ (ws := [])
      (by rw [v2.mem, v1.mem]; exact Frame.refl _ _) (fun _ h => nomatch h), ?_, v2.gpr, by rw [v2.mem, v1.mem]⟩
  · intro r hr _
    have h0 : r ≠ .eax := by rintro rfl; simp [calleeSaved] at hr
    have h2 : r ≠ .edx := by rintro rfl; simp [calleeSaved] at hr
    rw [v2.other r h2, v1.other r h0]
  · rw [v2.other _ (by decide), v1.gpr, hk.arg_word hc hsc.lt, ha sc hsc.lt, hsc.val]

/-- The stores, from `scratch` in `eax` and `0` in `edx`. -/
theorem zeroStores_step {s : State} (hc : Whole.Ctx E g m₀ ins outs s) (h0 : s.gpr .eax = scr)
    (h2 : s.gpr .edx = 0) :
    WP isa (.block zeroStores) s fun u => Whole.Ctx E g m₀ ins outs u ∧
      stateAt u.mem (scr.setWidth 64) = Spec.Sha3.zero ∧ Frame [⟨scr.setWidth 64, 200⟩] s.mem u.mem := by
  have hw : ∀ k < 50, InRegions s.wr (scr.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k hk'
    rw [hc.wr]
    exact ⟨SCR scr, List.mem_cons_of_mem _ hk.so, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (hk.zeroStores_ok h0 h2 hw) fun v hv => ⟨?_, stateAt_zero hv.zero, hv.frame⟩
  refine hc.of_frame hv.rd hv.wr (by rw [hv.gpr]) (fun r _ _ => by rw [hv.gpr]) hv.frame ?_
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨SCR scr, hk.so, Region.sub_prefix (by decide)⟩

theorem zero_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr) :
    WP isa (zeroState sc) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      stateAt u.mem (scr.setWidth 64) = Spec.Sha3.zero ∧ Frame [⟨scr.setWidth 64, 200⟩] t.mem u.mem := by
  unfold zeroState
  rw [WP.block_append_iff]
  refine WP.mono (hk.zeroArgs_ok hc ha hsc) fun u ⟨hu, h0, h2, hm⟩ => ?_
  refine WP.mono (hk.zeroStores_step hu h0 h2) fun v ⟨hv, hz, hf⟩ => ⟨hv, hz, ?_⟩
  rw [← hm]; exact hf

/-! ## The calls' common facts -/

theorem esp4 : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by have := hk.below; omega)

/-- The return address and the callee's stack are outside the regions `D`
that `Lo E` is outside. -/
theorem ret_disj {D : Region} (h : (Lo E).Disjoint D) : Region.Disjoint ⟨(E - 4).setWidth 64, 4⟩ D :=
  h.sub_left (ret_lo hk.below)

theorem stk_disj {D : Region} (h : (Lo E).Disjoint D) : Region.Disjoint ⟨(E - 4).setWidth 64 - 12, 12⟩ D :=
  h.sub_left (stk_lo hk.below)

omit hk in
theorem args_disj {D : Region} {k : Nat} (hk' : k ≤ 24) (h : (Lo E).Disjoint D) :
    Region.Disjoint ⟨E.setWidth 64, k⟩ D :=
  h.sub_left (args_lo E hk')

/-- Bytes outside `Lo E`, as the callee sees them. -/
theorem entry_bytes (hc : Whole.Ctx E g m₀ ins outs t) {D : Region} (h : (Lo E).Disjoint D) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt t.callEntry.mem D.base D.len = Spec.Ed448.bytesAt t.mem D.base D.len := by
  refine frame_bytes (Whole.callEntry_frame t) (fun r hr => ?_) hn
  rw [List.mem_singleton.mp hr, hc.esp]
  exact (h.sub_left (below4_lo hk.below)).symm

theorem entry_repr (hc : Whole.Ctx E g m₀ ins outs t) {msg : List Byte}
    (h : Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg) : Spec.Sha3.Repr t.callEntry.mem (scr.setWidth 64) 136 msg :=
  repr_frame (Whole.callEntry_frame t) (fun r hr => by
    rw [List.mem_singleton.mp hr, hc.esp]
    exact ((hk.lo_kWr _ (kWr_state scr)).sub_left (below4_lo hk.below)).symm) h

/-! ## `absorb` -/

def absRd (D : Region) : List Region := [D]
def absWr (E scr : BitVec 32) : List Region := kWr scr ++ [⟨E.setWidth 64, 24⟩]

theorem abs_pre (hc : Whole.Ctx E g m₀ ins outs t) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hd : Away E scr ⟨P.setWidth 64, N.toNat⟩) (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (h0 : arg t.callEntry 0 = scr) (h1 : arg t.callEntry 1 = 136) (h2 : arg t.callEntry 2 = BitVec.ofNat 32 pos)
    (h3 : arg t.callEntry 3 = P) (h4 : arg t.callEntry 4 = N) (h5 : arg t.callEntry 5 = scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.absorbX86.pre (t.callEntry.withRegions (absRd ⟨P.setWidth 64, N.toNat⟩) (absWr E scr)) := by
  have ab : ∀ rd wr, argAddr (t.callEntry.withRegions rd wr) 0 = E.setWidth 64 :=
    Whole.arg_base hc.esp
  simp only [Proof.Sha3.absorbX86, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, h0, h1, h2, h3, h4, h5, ab, absRd, absWr, kWr,
    List.cons_append, List.nil_append]
  have lk := hk.lo_kWr
  have e4 := hk.esp4
  have hb := hk.below
  have hf := hk.frame
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨trivial, trivial, hk.state_scratch, hd.kwr _ (kWr_state scr), hd.kwr _ (kWr_scratch scr),
    args_disj (by decide) (lk _ (kWr_state scr)), args_disj (by decide) hd.lo,
    args_disj (by decide) (lk _ (kWr_scratch scr)),
    hk.ret_disj (lk _ (kWr_state scr)), hk.ret_disj hd.lo, hk.ret_disj (lk _ (kWr_scratch scr)),
    hk.stk_disj (lk _ (kWr_state scr)), hk.stk_disj hd.lo, hk.stk_disj (lk _ (kWr_scratch scr)),
    by have := hk.nc; omega, hfit, hk.scr_fit, by omega, by omega, by decide, ?_⟩
  rw [hpn]; exact hp

theorem abs_covers {D : Region} (hcov : DataOk E ins outs D) :
    Covers (absRd D ++ absWr E scr) (ins ++ Whole.FR E :: outs) := by
  refine covers_of fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]; exact hcov
  rcases List.mem_append.mp hr with hr | hr
  · exact hk.kWr_covered r hr
  · rw [List.mem_singleton.mp hr]; exact .inl (args_within E (by decide))

theorem abs_writes : ∀ r ∈ absWr E scr, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hk.kWr_writes r hr
  · rw [List.mem_singleton.mp hr]; exact .inl (args_within E (by decide))

/-- What a call writes, in `Lo E` and the regions it may write. -/
theorem call_frame {ws : List Region} {m m' : Mem} (hf : Frame (ws ++ [VG.X86.below E 24]) m m')
    (hw : ∀ r ∈ ws, Region.Sub r (Lo E) ∨ r ∈ kWr scr) : Frame (Lo E :: kWr scr) m m' := by
  refine Frame.sub hf fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with h | h
    · exact ⟨Lo E, List.mem_cons_self, h⟩
    · exact ⟨r, List.mem_cons_of_mem _ h, fun _ h => h⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨Lo E, List.mem_cons_self, below_lo hk.below⟩

omit hk in
theorem absWr_lo : ∀ r ∈ absWr E scr, Region.Sub r (Lo E) ∨ r ∈ kWr scr := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact .inr hr
  · rw [List.mem_singleton.mp hr]; exact .inl (args_lo E (by decide))

theorem absorb_call (hc : Whole.Ctx E g m₀ ins outs t) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hcov : DataOk E ins outs ⟨P.setWidth 64, N.toNat⟩) (hd : Away E scr ⟨P.setWidth 64, N.toNat⟩)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (h0 : arg t.callEntry 0 = scr) (h1 : arg t.callEntry 1 = 136) (h2 : arg t.callEntry 2 = BitVec.ofNat 32 pos)
    (h3 : arg t.callEntry 3 = P) (h4 : arg t.callEntry 4 = N) (h5 : arg t.callEntry 5 = scr + BitVec.ofNat 32 KSCR) :
    WP isa (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.X86.Stream.absorb) t fun v =>
      Whole.Ctx E g m₀ ins outs v ∧ Frame (Lo E :: kWr scr) t.mem v.mem ∧
      (∀ msg, Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg → pos = msg.length % 136 →
        Spec.Sha3.Repr v.mem (scr.setWidth 64) 136 (msg ++ Spec.Sha3.bytesAt t.mem (P.setWidth 64) N.toNat)) ∧
      v.gpr .eax = BitVec.ofNat 32 ((pos + N.toNat) % 136) := by
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine Whole.call_ok hc hk.below Proof.Sha3.X86.Stream.Absorb.absorb_verified.1 absorb_nosp
    (by rw [absorb_stack]; decide) (hk.abs_pre hc hp hd hfit h0 h1 h2 h3 h4 h5) (hk.abs_covers hcov)
    hk.abs_writes fun v hv hf _ ⟨s₂, hm, hg, hpost⟩ => ⟨hv, hk.call_frame hf absWr_lo, ?_, ?_⟩
  · intro msg hr hpos
    have h := hpost.1 msg (by
      simp only [State.withRegions_mem, arg_withRegions, h0, h1]
      exact hk.entry_repr hc hr) (by simp only [arg_withRegions, h1, h2, hpn]; exact hpos)
    simp only [State.withRegions_mem, arg_withRegions, h0, h1, h3, h4] at h
    have e : Spec.Sha3.bytesAt t.callEntry.mem (P.setWidth 64) N.toNat =
        Spec.Sha3.bytesAt t.mem (P.setWidth 64) N.toNat :=
      hk.entry_bytes hc (D := ⟨P.setWidth 64, N.toNat⟩) hd.lo (by change N.toNat ≤ 2 ^ 64; have := N.isLt; omega)
    rw [hm, e] at h
    exact h
  · have h := hpost.2
    simp only [arg_withRegions, h1, h2, h4, hpn] at h
    rw [← hg .eax (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [h, show BitVec.toNat (136 : BitVec 32) = 136 from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := (pos + N.toNat) % 136) (b := 2 ^ 32)
        (by have := Nat.mod_lt (pos + N.toNat) (by decide : 136 > 0); omega)]

/-! ## Set-ups -/

/-- The state is outside the outgoing arguments. -/
theorem state_args : ∀ r ∈ [(⟨E.setWidth 64, 24⟩ : Region)], (⟨scr.setWidth 64, 200⟩ : Region).Disjoint r :=
  fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ((hk.lo_kWr _ (kWr_state scr)).sub_left (args_lo E (by decide))).symm

omit hk in
theorem args_frame {m m' : Mem} (h : Frame [⟨E.setWidth 64, 24⟩] m m') : Frame (Lo E :: kWr scr) m m' :=
  h.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨Lo E, List.mem_cons_self, args_lo E (by decide)⟩

omit hk in
theorem data_args {D : Region} (hd : Away E scr D) : ∀ r ∈ [(⟨E.setWidth 64, 24⟩ : Region)], D.Disjoint r :=
  fun r hr => by rw [List.mem_singleton.mp hr]; exact (hd.lo.sub_left (args_lo E (by decide))).symm

/-- `mov [esp + 8], edx`: the third outgoing argument. -/
theorem store2_ok (hc : Whole.Ctx E g m₀ ins outs t) :
    WP isa (.block [.store (at_ 8) .edx]) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧ Whole.slots E u 2 = t.gpr .edx ∧
      (∀ j < 6, j ≠ 2 → Whole.slots E u j = Whole.slots E t j) ∧ u.gpr = t.gpr := by
  have hf := hk.frame
  have ea : addr E 8 = E.setWidth 64 + BitVec.ofNat 64 8 := addr_eq (by omega)
  refine wp_stm (b := .esp) (o := 8) hc.esp ?_ fun u m => WP.block_nil ?_
  · rw [ea, hc.wr]; exact ⟨Whole.FR E, List.mem_cons_self, Offset.contains_base _ (by decide) (by decide)⟩
  have hfr : Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem := by
    rw [m.mem, ea]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine ⟨hc.of_frame m.rd m.wr (by rw [m.gpr]) (fun r _ _ => by rw [m.gpr]) hfr
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (Region.sub_prefix (by decide))), hfr, ?_,
    fun j hj h2 => ?_, m.gpr⟩
  · show u.mem.readW (E.setWidth 64 + BitVec.ofNat 64 8) 32 = _
    rw [m.mem, ea]; exact Mem.readW_writeW_self32 _ _ _
  · show u.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 = t.mem.readW _ 32
    rw [m.mem, ea, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]

omit hk in
/-- `mov edx, eax`. -/
theorem keep_ok (hc : Whole.Ctx E g m₀ ins outs t) {is : List Instr} {Q : State → Prop}
    (k : ∀ s, Whole.Ctx E g m₀ ins outs s → s.mem = t.mem → s.gpr .edx = t.gpr .eax →
      (∀ r, r ≠ .edx → s.gpr r = t.gpr r) → WP isa (.block is) s Q) :
    WP isa (.block (.mov .edx (.reg .eax) :: is)) t Q :=
  wp_mov fun s v => k s (hc.of_frame v.rd v.wr (v.other _ (by decide))
    (fun r hr _ => v.other r (by rintro rfl; simp [calleeSaved] at hr)) (ws := [])
    (by rw [v.mem]; exact Frame.refl _ _) (fun _ h => nomatch h)) v.mem v.gpr v.other

/-- A call's outgoing argument `j`, from its slot. -/
theorem slot_arg (hc : Whole.Ctx E g m₀ ins outs t) {j : Nat} (hj : j < 6) {v : BitVec 32}
    (h : Whole.slots E t j = v) : arg t.callEntry j = v :=
  (hk.call_arg hc hj).trans h

/-- `mov edx, eax`, a set-up, and `mov [esp + 8], edx`: a call's arguments,
the third the position the previous call returned. -/
theorem nsetup_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {vs : List Value}
    (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid n v) {pos : Nat} (hpos : t.gpr .eax = BitVec.ofNat 32 pos) :
    WP isa (.block (.mov .edx (.reg .eax) :: setup 0 vs ++ ([.store (at_ 8) .edx] : List Instr))) t fun w =>
      Whole.Ctx E g m₀ ins outs w ∧ Frame [⟨E.setWidth 64, 24⟩] t.mem w.mem ∧
      Whole.slots E w 2 = BitVec.ofNat 32 pos ∧
      ∀ j (hj : j < vs.length), j ≠ 2 → Whole.slots E w j = argVal E val (vs[j]'hj) := by
  rw [WP.block_append_iff]
  refine keep_ok hc fun s1 hc1 m1 e1 _ => ?_
  refine WP.mono (hk.setup_ok hc1 ha hn hv) fun u ⟨hu, hm, hs, hreg⟩ => ?_
  refine WP.mono (hk.store2_ok hu) fun w ⟨hw, hm2, h2, hs', _⟩ =>
    ⟨hw, by rw [m1] at hm; exact hm.trans hm2, by rw [h2, hreg .edx (by decide), e1, hpos],
      fun j hj h => (hs' j (by omega) h).trans (hs j hj)⟩

/-! ## Absorptions -/

/-- An absorption's arguments, from position 0. -/
theorem first_setup (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) :
    WP isa (.block (firstArgs sc src len)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧ AbsSlots E scr 0 (argVal E val src) (argVal E val len) u := by
  unfold firstArgs
  refine WP.mono (hk.setup_ok hc ha (by simp) ?_) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  · simp only [List.forall_mem_cons]
    exact ⟨hsc.valid 0, trivial, trivial, vs, vl, hsc.valid KSCR, fun _ h => nomatch h⟩
  have a0 := hs 0 (by simp)
  have a1 := hs 1 (by simp)
  have a2 := hs 2 (by simp)
  have a3 := hs 3 (by simp)
  have a4 := hs 4 (by simp)
  have a5 := hs 5 (by simp)
  simp only [argVal_const, argVal_caller, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at a0 a1 a2 a3 a4 a5
  exact ⟨a0, a1, a2, a3, a4, a5⟩

/-- An absorption's arguments, from the position the previous one returned. -/
theorem next_setup (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) {pos : Nat}
    (hpos : t.gpr .eax = BitVec.ofNat 32 pos) :
    WP isa (.block (nextArgs sc src len)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧ AbsSlots E scr pos (argVal E val src) (argVal E val len) u := by
  unfold nextArgs
  refine WP.mono (hk.nsetup_ok hc ha (by simp) ?_ hpos) fun u ⟨hu, hm, h2, hs⟩ => ⟨hu, hm, ?_⟩
  · simp only [List.forall_mem_cons]
    exact ⟨hsc.valid 0, trivial, trivial, vs, vl, hsc.valid KSCR, fun _ h => nomatch h⟩
  have a0 := hs 0 (by simp) (by decide)
  have a1 := hs 1 (by simp) (by decide)
  have a3 := hs 3 (by simp) (by decide)
  have a4 := hs 4 (by simp) (by decide)
  have a5 := hs 5 (by simp) (by decide)
  simp only [argVal_const, argVal_caller, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at a0 a1 a3 a4 a5
  exact ⟨a0, a1, h2, a3, a4, a5⟩

/-- An absorption's call, from its arguments. -/
theorem absorb_slots (hc : Whole.Ctx E g m₀ ins outs t) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hs : AbsSlots E scr pos P N t)
    (hcov : DataOk E ins outs ⟨P.setWidth 64, N.toNat⟩) (hd : Away E scr ⟨P.setWidth 64, N.toNat⟩)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 32) :
    WP isa (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.X86.Stream.absorb) t fun v =>
      Whole.Ctx E g m₀ ins outs v ∧ Frame (Lo E :: kWr scr) t.mem v.mem ∧
      (∀ msg, Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg → pos = msg.length % 136 →
        Spec.Sha3.Repr v.mem (scr.setWidth 64) 136 (msg ++ Spec.Sha3.bytesAt t.mem (P.setWidth 64) N.toNat)) ∧
      v.gpr .eax = BitVec.ofNat 32 ((pos + N.toNat) % 136) :=
  hk.absorb_call hc hp hcov hd hfit (hk.slot_arg hc (by decide) hs.a0) (hk.slot_arg hc (by decide) hs.a1)
    (hk.slot_arg hc (by decide) hs.a2) (hk.slot_arg hc (by decide) hs.a3) (hk.slot_arg hc (by decide) hs.a4)
    (hk.slot_arg hc (by decide) hs.a5)

/-- What an absorption's call needs, for its constant time. -/
def abs_ready (hc : Whole.Ctx E g m₀ ins outs t) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hs : AbsSlots E scr pos P N t)
    (hcov : DataOk E ins outs ⟨P.setWidth 64, N.toNat⟩) (hd : Away E scr ⟨P.setWidth 64, N.toNat⟩)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 32) : Whole.CallReady Proof.Sha3.absorbX86 E ins outs t :=
  ⟨absRd ⟨P.setWidth 64, N.toNat⟩, absWr E scr,
    hk.abs_pre hc hp hd hfit (hk.slot_arg hc (by decide) hs.a0) (hk.slot_arg hc (by decide) hs.a1)
      (hk.slot_arg hc (by decide) hs.a2) (hk.slot_arg hc (by decide) hs.a3) (hk.slot_arg hc (by decide) hs.a4)
      (hk.slot_arg hc (by decide) hs.a5), hk.abs_covers hcov, hk.abs_writes⟩

/-- The first absorption, of `N` bytes at `P`, from position 0 of an empty state. -/
theorem first_abs (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) {P : BitVec 32} {N : Nat}
    (hP : argVal E val src = P) (hN : (argVal E val len).toNat = N)
    (hcov : DataOk E ins outs ⟨P.setWidth 64, N⟩) (hd : Away E scr ⟨P.setWidth 64, N⟩)
    (hfit : P.toNat + N ≤ 2 ^ 32) (hr : Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 []) :
    WP isa (absorb (firstArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (Lo E :: kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (scr.setWidth 64) 136 (Spec.Sha3.bytesAt t.mem (P.setWidth 64) N) ∧
      v.gpr .eax = BitVec.ofNat 32 (N % 136) := by
  unfold absorb callWith
  refine WP.seq (WP.mono (hk.first_setup hc ha hsc vs vl) fun u ⟨hu, hm, hs⟩ => ?_)
  subst hP hN
  have hrd := repr_frame hm hk.state_args hr
  refine WP.mono (hk.absorb_slots hu (by decide) hs hcov hd hfit)
    fun v ⟨hv, hf, hrv, h0v⟩ => ⟨hv, (args_frame hm).trans hf, ?_, by rw [h0v, Nat.zero_add]⟩
  have e := sframe_bytes (D := ⟨(argVal E val src).setWidth 64, (argVal E val len).toNat⟩) hm (data_args hd)
    (by change (argVal E val len).toNat ≤ 2 ^ 64; omega)
  have h := hrv [] hrd rfl
  rw [List.nil_append, e] at h
  exact h

/-- An absorption of `N` bytes at `P`, at the position the previous one
returned. -/
theorem next_abs (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) {P : BitVec 32} {N : Nat}
    (hP : argVal E val src = P) (hN : (argVal E val len).toNat = N)
    (hcov : DataOk E ins outs ⟨P.setWidth 64, N⟩) (hd : Away E scr ⟨P.setWidth 64, N⟩)
    (hfit : P.toNat + N ≤ 2 ^ 32)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg)
    (hpos : t.gpr .eax = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (absorb (nextArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (Lo E :: kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (scr.setWidth 64) 136 (msg ++ Spec.Sha3.bytesAt t.mem (P.setWidth 64) N) ∧
      v.gpr .eax = BitVec.ofNat 32 ((msg ++ Spec.Sha3.bytesAt t.mem (P.setWidth 64) N).length % 136) := by
  unfold absorb callWith
  refine WP.seq (WP.mono (hk.next_setup hc ha hsc vs vl hpos) fun u ⟨hu, hm, hs⟩ => ?_)
  subst hP hN
  have hrd := repr_frame hm hk.state_args hr
  have e := sframe_bytes (D := ⟨(argVal E val src).setWidth 64, (argVal E val len).toNat⟩) hm (data_args hd)
    (by change (argVal E val len).toNat ≤ 2 ^ 64; omega)
  refine WP.mono (hk.absorb_slots hu (Nat.mod_lt _ (by decide)) hs hcov hd hfit)
    fun v ⟨hv, hf, hrv, h0v⟩ => ⟨hv, (args_frame hm).trans hf, ?_, ?_⟩
  · have h := hrv msg hrd rfl
    rw [e] at h
    exact h
  · rw [h0v, Nat.mod_add_mod, List.length_append]
    simp only [Spec.Sha3.bytesAt, List.length_map, List.length_range]

/-! ## `pad` -/

def padWr (E scr : BitVec 32) : List Region := kWr scr ++ [⟨E.setWidth 64, 20⟩]

theorem pad_pre (hc : Whole.Ctx E g m₀ ins outs t) {pos : Nat} (hp : pos < 136) (hs : PadSlots E scr pos t) :
    Proof.Sha3.padX86.pre (t.callEntry.withRegions [] (padWr E scr)) := by
  have ab : ∀ rd wr, argAddr (t.callEntry.withRegions rd wr) 0 = E.setWidth 64 :=
    Whole.arg_base hc.esp
  simp only [Proof.Sha3.padX86, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, hk.slot_arg hc (by decide) hs.a0,
    hk.slot_arg hc (by decide) hs.a1, hk.slot_arg hc (by decide) hs.a2, hk.slot_arg hc (by decide) hs.a4,
    ab, padWr, kWr, List.cons_append, List.nil_append]
  have lk := hk.lo_kWr
  have e4 := hk.esp4
  have hb := hk.below
  have hf := hk.frame
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨trivial, trivial, hk.state_scratch,
    args_disj (by decide) (lk _ (kWr_state scr)), args_disj (by decide) (lk _ (kWr_scratch scr)),
    hk.ret_disj (lk _ (kWr_state scr)), hk.ret_disj (lk _ (kWr_scratch scr)),
    hk.stk_disj (lk _ (kWr_state scr)), hk.stk_disj (lk _ (kWr_scratch scr)),
    by have := hk.nc; omega, hk.scr_fit, by omega, by omega, by decide, ?_⟩
  rw [hpn]; exact hp

theorem pad_covers : Covers ([] ++ padWr E scr) (ins ++ Whole.FR E :: outs) := by
  refine covers_of fun r hr => ?_
  rcases List.mem_append.mp (List.nil_append _ ▸ hr) with hr | hr
  · exact hk.kWr_covered r hr
  · rw [List.mem_singleton.mp hr]; exact .inl (args_within E (by decide))

theorem pad_writes : ∀ r ∈ padWr E scr, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hk.kWr_writes r hr
  · rw [List.mem_singleton.mp hr]; exact .inl (args_within E (by decide))

omit hk in
theorem padWr_lo : ∀ r ∈ padWr E scr, Region.Sub r (Lo E) ∨ r ∈ kWr scr := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact .inr hr
  · rw [List.mem_singleton.mp hr]; exact .inl (args_lo E (by decide))

/-- The padding's arguments, at the position the last absorption returned. -/
theorem pad_setup (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {pos : Nat} (hpos : t.gpr .eax = BitVec.ofNat 32 pos) :
    WP isa (.block (padArgs sc)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧ PadSlots E scr pos u := by
  unfold padArgs
  refine WP.mono (hk.nsetup_ok hc ha (by simp) ?_ hpos) fun u ⟨hu, hm, h2, hs⟩ => ⟨hu, hm, ?_⟩
  · simp only [List.forall_mem_cons]
    exact ⟨hsc.valid 0, trivial, trivial, trivial, hsc.valid KSCR, fun _ h => nomatch h⟩
  have a0 := hs 0 (by simp) (by decide)
  have a1 := hs 1 (by simp) (by decide)
  have a3 := hs 3 (by simp) (by decide)
  have a4 := hs 4 (by simp) (by decide)
  simp only [argVal_const, argVal_caller, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at a0 a1 a3 a4
  exact ⟨a0, a1, h2, a3, a4⟩

theorem pad_call (hc : Whole.Ctx E g m₀ ins outs t) {pos : Nat} (hp : pos < 136) (hs : PadSlots E scr pos t) :
    WP isa (.call Spec.Sha3.padScratchApi.name Impl.Sha3.X86.Stream.pad) t fun v =>
      Whole.Ctx E g m₀ ins outs v ∧ Frame (Lo E :: kWr scr) t.mem v.mem ∧
      ∀ msg, Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg → pos = msg.length % 136 →
        stateAt v.mem (scr.setWidth 64) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine Whole.call_ok hc hk.below Proof.Sha3.X86.Stream.Pad.pad_verified.1 pad_nosp
    (by rw [pad_stack]; decide) (hk.pad_pre hc hp hs) hk.pad_covers
    hk.pad_writes fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, hk.call_frame hf padWr_lo, fun msg hr hpos => ?_⟩
  simp only [Proof.Sha3.padX86, State.withRegions_mem, arg_withRegions, hm₂] at hpost
  rw [hk.slot_arg hc (by decide) hs.a0, hk.slot_arg hc (by decide) hs.a1, hk.slot_arg hc (by decide) hs.a2,
    hk.slot_arg hc (by decide) hs.a3, hpn] at hpost
  exact hpost msg (hk.entry_repr hc hr) hpos

def pad_ready (hc : Whole.Ctx E g m₀ ins outs t) {pos : Nat} (hp : pos < 136) (hs : PadSlots E scr pos t) :
    Whole.CallReady Proof.Sha3.padX86 E ins outs t :=
  ⟨[], padWr E scr, hk.pad_pre hc hp hs, hk.pad_covers, hk.pad_writes⟩

theorem pad_step (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg)
    (hpos : t.gpr .eax = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (pad sc) t fun v => Whole.Ctx E g m₀ ins outs v ∧ Frame (Lo E :: kWr scr) t.mem v.mem ∧
      stateAt v.mem (scr.setWidth 64) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  unfold pad callWith
  refine WP.seq (WP.mono (hk.pad_setup hc ha hsc hpos) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (hk.pad_call hu (Nat.mod_lt _ (by decide)) hs) fun v ⟨hv, hf, hp⟩ =>
    ⟨hv, (args_frame hm).trans hf, hp msg (repr_frame hm hk.state_args hr) rfl⟩

/-! ## `squeeze` -/

def sqzWr (E scr : BitVec 32) (d : Nat) : List Region :=
  [⟨scr.setWidth 64, 200⟩, fr E d 114, ⟨(scr + BitVec.ofNat 32 KSCR).setWidth 64, 640⟩, ⟨E.setWidth 64, 24⟩]

theorem sqz_pre (hc : Whole.Ctx E g m₀ ins outs t) {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256)
    (hs : SqzSlots E scr d t) :
    Proof.Sha3.squeezeX86.pre (t.callEntry.withRegions [] (sqzWr E scr d)) := by
  have ab : ∀ rd wr, argAddr (t.callEntry.withRegions rd wr) 0 = E.setWidth 64 :=
    Whole.arg_base hc.esp
  have fa := hk.fr_addr (d := d) (by omega)
  simp only [Proof.Sha3.squeezeX86, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, hk.slot_arg hc (by decide) hs.a0,
    hk.slot_arg hc (by decide) hs.a1, hk.slot_arg hc (by decide) hs.a2, hk.slot_arg hc (by decide) hs.a3,
    hk.slot_arg hc (by decide) hs.a4, hk.slot_arg hc (by decide) hs.a5, ab, sqzWr, fa]
  have lk := hk.lo_kWr
  have e4 := hk.esp4
  have hb := hk.below
  have hf := hk.frame
  have so : ∀ r ∈ kWr scr, (fr E d 114).Disjoint r := fun r hr => (hk.fr_scr hd).sub_right (hk.kWr_sub r hr).sub
  have lo := lo_fr E h24 hd
  refine ⟨trivial, rfl, (so _ (kWr_state scr)).symm, hk.state_scratch, so _ (kWr_scratch scr),
    args_disj (by decide) (lk _ (kWr_state scr)), Offset.base_disjoint _ h24 (by omega),
    args_disj (by decide) (lk _ (kWr_scratch scr)),
    hk.ret_disj (lk _ (kWr_state scr)), hk.ret_disj lo, hk.ret_disj (lk _ (kWr_scratch scr)),
    hk.stk_disj (lk _ (kWr_state scr)), hk.stk_disj lo, hk.stk_disj (lk _ (kWr_scratch scr)),
    by have := hk.nc; omega, hk.fr_fit hd, hk.scr_fit, by omega, by omega, by decide, by decide⟩

theorem sqz_writes {d : Nat} (hd : d + 114 ≤ 256) :
    ∀ r ∈ sqzWr E scr d, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R := by
  intro r hr
  simp only [sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hk.kWr_writes _ (kWr_state scr)
  · exact .inl (frame_within E hd)
  · exact hk.kWr_writes _ (kWr_scratch scr)
  · exact .inl (args_within E (by decide))

theorem sqz_covers {d : Nat} (hd : d + 114 ≤ 256) :
    Covers ([] ++ sqzWr E scr d) (ins ++ Whole.FR E :: outs) := by
  refine covers_of fun r hr => ?_
  rw [List.nil_append] at hr
  rcases hk.sqz_writes hd r hr with h | ⟨R, hR, h⟩
  · exact .inl h
  · exact .inr ⟨R, List.mem_append_right _ hR, h⟩

theorem sqz_setup (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    (d : Nat) :
    WP isa (.block (sqzArgs sc d)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧ SqzSlots E scr d u := by
  unfold sqzArgs
  refine WP.mono (hk.setup_ok hc ha (by simp) ?_) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  · simp only [List.forall_mem_cons]
    exact ⟨hsc.valid 0, trivial, trivial, trivial, trivial, hsc.valid KSCR, fun _ h => nomatch h⟩
  have a0 := hs 0 (by simp)
  have a1 := hs 1 (by simp)
  have a2 := hs 2 (by simp)
  have a3 := hs 3 (by simp)
  have a4 := hs 4 (by simp)
  have a5 := hs 5 (by simp)
  simp only [argVal_const, argVal_frame, argVal_caller, hsc.val, List.getElem_cons_zero,
    List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4 a5
  exact ⟨a0, a1, a2, a3, a4, a5⟩

theorem sqz_call (hc : Whole.Ctx E g m₀ ins outs t) {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256)
    (hs : SqzSlots E scr d t) :
    WP isa (.call Spec.Sha3.squeezeScratchApi.name Impl.Sha3.X86.Stream.squeeze) t fun v =>
      Whole.Ctx E g m₀ ins outs v ∧ Frame (Lo E :: fr E d 114 :: kWr scr) t.mem v.mem ∧
      Spec.Sha3.bytesAt v.mem (E.setWidth 64 + BitVec.ofNat 64 d) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem (scr.setWidth 64)) 0 114 := by
  have hst : stateAt t.callEntry.mem (scr.setWidth 64) = stateAt t.mem (scr.setWidth 64) :=
    state_frame (Whole.callEntry_frame t) (fun r hr => by
      rw [List.mem_singleton.mp hr, hc.esp]
      exact ((hk.lo_kWr _ (kWr_state scr)).sub_left (below4_lo hk.below)).symm)
  refine Whole.call_ok hc hk.below Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.1 squeeze_nosp
    (by rw [squeeze_stack]; decide) (hk.sqz_pre hc h24 hd hs) (hk.sqz_covers hd)
    (hk.sqz_writes hd) fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, ?_, ?_⟩
  · refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (kWr_state scr)), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (kWr_scratch scr)), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, args_lo E (by decide)⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨Lo E, List.mem_cons_self, below_lo hk.below⟩
  · have h := hpost.1
    simp only [State.withRegions_mem, arg_withRegions, hm₂, hk.slot_arg hc (by decide) hs.a0,
      hk.slot_arg hc (by decide) hs.a1, hk.slot_arg hc (by decide) hs.a2, hk.slot_arg hc (by decide) hs.a3,
      hk.slot_arg hc (by decide) hs.a4, hk.fr_addr (d := d) (by omega), hst] at h
    exact h

def sqz_ready (hc : Whole.Ctx E g m₀ ins outs t) {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256)
    (hs : SqzSlots E scr d t) : Whole.CallReady Proof.Sha3.squeezeX86 E ins outs t :=
  ⟨[], sqzWr E scr d, hk.sqz_pre hc h24 hd hs, hk.sqz_covers hd, hk.sqz_writes hd⟩

theorem sqz_step (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀) {sc : Nat} (hsc : ScrAt n val sc scr)
    {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256) :
    WP isa (squeeze sc d) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (Lo E :: fr E d 114 :: kWr scr) t.mem v.mem ∧
      Spec.Sha3.bytesAt v.mem (E.setWidth 64 + BitVec.ofNat 64 d) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem (scr.setWidth 64)) 0 114 := by
  unfold squeeze callWith
  refine WP.seq (WP.mono (hk.sqz_setup hc ha hsc d) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (hk.sqz_call hu h24 hd hs) fun v ⟨hv, hf, hb⟩ => ⟨hv, ?_, ?_⟩
  · have h1 : Frame (Lo E :: fr E d 114 :: kWr scr) t.mem u.mem := hm.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨Lo E, List.mem_cons_self, args_lo E (by decide)⟩
    exact h1.trans hf
  · rw [hb, state_frame hm hk.state_args]

end Kit

end VG.Proof.Ed448.X86.Shake
