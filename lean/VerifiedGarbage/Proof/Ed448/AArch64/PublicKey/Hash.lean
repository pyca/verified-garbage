import VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Layout
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Ed448 public-key derivation on AArch64: `SHAKE256(seed, 114)`

The Keccak state in `scratch` zeroed (`zero_ok`), the seed absorbed, the
padding absorbed, and 114 bytes squeezed into the frame (`hash_ok`), with
any implementation `v` of the permutation: each call is of the sponge
function's correctness for `v` (`Proof.Sha3.AArch64.Stream`).
-/

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (setup callWith Value)
open VG.Proof.Ed25519.AArch64.Whole (call_okF Within)
open VG.Spec.Sha3 (stateAt)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-! ## The state zeroed -/

theorem movz14_ok (s : State) :
    WP isa (.block [.movz .x .x14 0 0]) s fun t => t.gpr .x14 = 0 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v ∧ ∀ r, r ≠ .x14 → t.gpr r = s.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- After the first `n` stores of zero. -/
structure ZInv (scr : Addr) (s : State) (n : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : t.v = s.v
  gpr : t.gpr = s.gpr
  frame : Frame [⟨scr, 200⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (scr + BitVec.ofNat 64 (8 * j)) 64 = 0

theorem zstores_ok {s : State} {scr : Addr} (h15 : s.gpr .x15 = scr) (h14 : s.gpr .x14 = 0)
    (hw : (⟨scr, 8192⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 25, WP isa (.block ((List.range n).map fun k => Instr.str .x .x14 .x15 (8 * k))) s (ZInv scr s n)
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zstores_ok h15 h14 hw n (by omega)) fun u hu => ?_
    have dest : InRegions u.wr (u.gpr .x15 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [hu.gpr, hu.wr, h15]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    apply WP.of_runBlock
    have e15 : u.gpr .x15 = scr := by rw [hu.gpr, h15]
    have e14 : u.gpr .x14 = 0 := by rw [hu.gpr, h14]
    simp only [runBlock_cons]
    rw [exec_str_x ⟨by omega, by omega⟩ dest]
    simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
    rw [e15, e14]
    refine ⟨hu.rd, hu.wr, hu.sp, hu.v, hu.gpr, ?_, fun j hj => ?_⟩
    · exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
    · show (u.mem.writeW (scr + BitVec.ofNat 64 (8 * n)) (0 : BitVec 64)).readW
        (scr + BitVec.ofNat 64 (8 * j)) 64 = 0
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hu.words j (by omega)

theorem zero_state {m : Mem} {p : Addr} (h : ∀ j < 25, m.readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

theorem zeroArgs_ok (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (.block zeroArgs) t fun w => Ctx L g vec m₀ w ∧ w.gpr .x15 = L.scr := by
  refine WP.mono (setup_ok hc hL ha (args := [(.x15, .caller 2 0)]) (by decide)
    (by simp [VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp) (by simp [preserved]))
    fun u ⟨hu, _, hs⟩ => ⟨hu, ?_⟩
  have h15 := hs (.x15, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h15
  exact h15

theorem zeroStores_ok {u : State} (hu : Ctx L g vec m₀ u) (h15 : u.gpr .x15 = L.scr) :
    WP isa (.block zeroStores) u fun x => Ctx L g vec m₀ x ∧ stateAt x.mem L.scr = Spec.Sha3.zero := by
  rw [zeroStores, show ∀ (i : Instr) is, i :: is = [i] ++ is from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (movz14_ok u) fun w ⟨w14, wm, wrd, wwr, wsp, wv, wg⟩ => ?_
  have hw : Ctx L g vec m₀ w :=
    hu.regs wrd wwr wsp (fun r hr _ => wg r (by rintro rfl; simp [preserved] at hr)) wv wm
  have hws : (⟨L.scr, 8192⟩ : Region) ∈ w.wr := by
    rw [hw.wr]; simp [Lay.outputs]
  refine WP.mono (zstores_ok ((wg _ (by decide)).trans h15) w14 hws 25 (by omega)) fun x hx =>
    ⟨?_, zero_state hx.words⟩
  refine hw.of_frame hx.rd hx.wr hx.sp (fun r _ _ => by rw [hx.gpr]) (fun r _ => by rw [hx.v]) hx.frame ?_
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨L.SCR, by simp [Lay.outputs], Region.sub_prefix (by decide)⟩

/-! ## The calls -/

abbrev ST (L : Lay) : Region := ⟨L.scr, 200⟩
abbrev KS (L : Lay) : Region := ⟨L.scr + BitVec.ofNat 64 keccakScratch, 640⟩
abbrev HS (L : Lay) : Region := ⟨L.E + BitVec.ofNat 64 hashAt, 114⟩

theorem st_sub (L : Lay) : Region.Sub (ST L) L.SCR := Region.sub_prefix (by decide)
theorem ks_sub (L : Lay) : Region.Sub (KS L) L.SCR := Offset.sub_base _ (by decide)
theorem hs_sub (L : Lay) : Region.Sub (HS L) L.FR := Offset.sub_base _ (by decide)
theorem st_ks (L : Lay) : (ST L).Disjoint (KS L) := Offset.base_disjoint _ (by decide) (by decide)

theorem covers_writes {E : Addr} {rd wr ws : List Region}
    (hw : ∀ r ∈ ws, Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, Within r R) :
    Covers ws (rd ++ VG.Proof.Ed25519.AArch64.Whole.FR E :: wr) := by
  refine Covers.of_sub fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨_, List.mem_append_right _ List.mem_cons_self, hf⟩
  · exact ⟨R, List.mem_append_right _ (List.mem_cons_of_mem _ hR), hs⟩

theorem sponge_writes (L : Lay) : ∀ r ∈ [ST L, KS L],
    Within r L.FR ∨ ∃ R ∈ L.outputs, Within r R := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 200 ≤ 8192; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], keccakScratch, rfl, by change 256 + 640 ≤ 8192; decide⟩

theorem squeeze_writes (L : Lay) : ∀ r ∈ [ST L, HS L, KS L],
    Within r L.FR ∨ ∃ R ∈ L.outputs, Within r R := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 200 ≤ 8192; decide⟩
  · exact .inl ⟨hashAt, rfl, by change 128 + 114 ≤ 256; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], keccakScratch, rfl, by change 256 + 640 ≤ 8192; decide⟩

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

def absorbValues : List (Reg × Value) :=
  [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 0), (.x3, .caller 1 0), (.x4, .const 57),
    (.x5, .caller 2 keccakScratch)]

def padValues : List (Reg × Value) :=
  [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 57), (.x3, .const 0x1f),
    (.x4, .caller 2 keccakScratch)]

def squeezeValues : List (Reg × Value) :=
  [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 0), (.x3, .frame hashAt),
    (.x4, .const 114), (.x5, .caller 2 keccakScratch)]

theorem absorb_pre (hL : L.Ok) {u : State} (hsp : u.sp = L.E)
    (hs : ∀ p ∈ absorbValues, u.gpr p.1 = argValue L p.2) :
    Proof.Sha3.absorbAArch64.pre (u.callEntry.withRegions [L.SEED] [ST L, KS L]) := by
  have h0 := hs (.x0, .caller 2 0) (by simp [absorbValues])
  have h1 := hs (.x1, .const 136) (by simp [absorbValues])
  have h2 := hs (.x2, .const 0) (by simp [absorbValues])
  have h3 := hs (.x3, .caller 1 0) (by simp [absorbValues])
  have h4 := hs (.x4, .const 57) (by simp [absorbValues])
  have h5 := hs (.x5, .caller 2 keccakScratch) (by simp [absorbValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4 h5
  simp only [Proof.Sha3.absorbAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x5 ∉ linkRegs), h0, h1, h2, h3, h4, h5, hsp,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨trivial, trivial, st_ks L, hL.sc.sub_right (st_sub L), hL.sc.sub_right (ks_sub L), hL.e16,
    hL.cc.sub_right (st_sub L), hL.cs, hL.cc.sub_right (ks_sub L), by decide, by decide⟩

theorem absorb_covers (L : Lay) : Covers ([L.SEED] ++ [ST L, KS L]) (L.inputs ++ L.FR :: L.outputs) := by
  intro a n hin
  obtain ⟨r, hr, hh⟩ := hin
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr] at hh
    exact ⟨L.SEED, List.mem_append_left _ (by simp [Lay.inputs]), hh⟩
  · exact covers_writes (sponge_writes L) a n ⟨r, hr, hh⟩

theorem pad_pre (hL : L.Ok) {u : State} (hsp : u.sp = L.E)
    (hs : ∀ p ∈ padValues, u.gpr p.1 = argValue L p.2) :
    Proof.Sha3.padAArch64.pre (u.callEntry.withRegions [] [ST L, KS L]) := by
  have h0 := hs (.x0, .caller 2 0) (by simp [padValues])
  have h1 := hs (.x1, .const 136) (by simp [padValues])
  have h2 := hs (.x2, .const 57) (by simp [padValues])
  have h4 := hs (.x4, .caller 2 keccakScratch) (by simp [padValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h4
  simp only [Proof.Sha3.padAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h4, hsp,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨trivial, trivial, st_ks L, hL.e16, hL.cc.sub_right (st_sub L), hL.cc.sub_right (ks_sub L),
    by decide, by decide⟩

theorem hs_stk (L : Lay) : Region.Sub (HS L) L.STK := Offset.sub_base _ (by decide)

theorem squeeze_pre (hL : L.Ok) {u : State} (hsp : u.sp = L.E)
    (hs : ∀ p ∈ squeezeValues, u.gpr p.1 = argValue L p.2) :
    Proof.Sha3.squeezeAArch64.pre (u.callEntry.withRegions [] [ST L, HS L, KS L]) := by
  have h0 := hs (.x0, .caller 2 0) (by simp [squeezeValues])
  have h1 := hs (.x1, .const 136) (by simp [squeezeValues])
  have h2 := hs (.x2, .const 0) (by simp [squeezeValues])
  have h3 := hs (.x3, .frame hashAt) (by simp [squeezeValues])
  have h4 := hs (.x4, .const 114) (by simp [squeezeValues])
  have h5 := hs (.x5, .caller 2 keccakScratch) (by simp [squeezeValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4 h5
  have hos : (HS L).Disjoint (ST L) := (hL.kc.sub_left (hs_stk L)).sub_right (st_sub L)
  have hok : (HS L).Disjoint (KS L) := (hL.kc.sub_left (hs_stk L)).sub_right (ks_sub L)
  simp only [Proof.Sha3.squeezeAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x5 ∉ linkRegs), h0, h1, h2, h3, h4, h5, hsp,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨trivial, trivial, hos.symm, st_ks L, hok, hL.e16, hL.cc.sub_right (st_sub L),
    VG.Proof.Ed25519.AArch64.Whole.ck_frame (by decide), hL.cc.sub_right (ks_sub L), by decide, by decide⟩

theorem absorb_step (v : Proof.Sha3.AArch64.Permutation) (hc : Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : Arguments L m₀) (hz : stateAt t.mem L.scr = Spec.Sha3.zero) :
    WP isa (callWith absorbArgs ("vg_keccak_absorb" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.absorbWith v.callee)) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Sha3.Repr u.mem L.scr 136 (Spec.Sha3.bytesAt m₀ L.seed 57) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 0), (.x3, .caller 1 0), (.x4, .const 57),
      (.x5, .caller 2 keccakScratch)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp)
    (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  have h1 := hs (.x1, .const 136) (by simp)
  have h2 := hs (.x2, .const 0) (by simp)
  have h3 := hs (.x3, .caller 1 0) (by simp)
  have h4 := hs (.x4, .const 57) (by simp)
  have h5 := hs (.x5, .caller 2 keccakScratch) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4 h5
  have hpre := absorb_pre hL hu.sp (fun p hp => hs p hp)
  have hcov := absorb_covers L
  refine call_okF hu (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Nat.le_of_eq v.absorb_depth)
    hpre hcov (sponge_writes L) fun w hw _ hp => ⟨hw, ?_⟩
  have hh := hp.1 [] (by
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), h0, hm]
    exact repr_nil hz) (by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h2]
    rfl)
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h3, h4, List.nil_append,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hh
  have e : Spec.Sha3.bytesAt u.mem L.seed 57 = Spec.Sha3.bytesAt m₀ L.seed 57 :=
    hu.seed_bytes hL
  rw [e] at hh
  exact hh

theorem pad_step (v : Proof.Sha3.AArch64.Permutation) (hc : Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : Arguments L m₀) {msg : List Byte} (hr : Spec.Sha3.Repr t.mem L.scr 136 msg)
    (hl : msg.length = 57) :
    WP isa (callWith padArgs ("vg_keccak_pad" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.padWith v.callee)) t fun u =>
      Ctx L g vec m₀ u ∧ stateAt u.mem L.scr =
        Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 57), (.x3, .const 0x1f),
      (.x4, .caller 2 keccakScratch)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp)
    (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  have h1 := hs (.x1, .const 136) (by simp)
  have h2 := hs (.x2, .const 57) (by simp)
  have h3 := hs (.x3, .const 0x1f) (by simp)
  have h4 := hs (.x4, .caller 2 keccakScratch) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4
  have hpre := pad_pre hL hu.sp (fun p hp => hs p hp)
  have hcov : Covers ([] ++ [ST L, KS L]) (L.inputs ++ L.FR :: L.outputs) :=
    covers_writes (sponge_writes L)
  refine call_okF hu (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Nat.le_of_eq v.pad_depth)
    hpre hcov (sponge_writes L) fun w hw _ hp => ⟨hw, ?_⟩
  have hh := hp msg (by
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1, hm,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    exact hr) (by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h1, h2, hl,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod])
  simp only [State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h3,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hh
  exact hh

theorem squeeze_step (v : Proof.Sha3.AArch64.Permutation) (hc : Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : Arguments L m₀) :
    WP isa (callWith squeezeArgs ("vg_keccak_squeeze" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 hashAt) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem L.scr) 0 114 := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 0), (.x3, .frame hashAt),
      (.x4, .const 114), (.x5, .caller 2 keccakScratch)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch, hashAt]) (by simp)
    (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  have h1 := hs (.x1, .const 136) (by simp)
  have h2 := hs (.x2, .const 0) (by simp)
  have h3 := hs (.x3, .frame hashAt) (by simp)
  have h4 := hs (.x4, .const 114) (by simp)
  have h5 := hs (.x5, .caller 2 keccakScratch) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4 h5
  have hpre := squeeze_pre hL hu.sp (fun p hp => hs p hp)
  have hcov : Covers ([] ++ [ST L, HS L, KS L]) (L.inputs ++ L.FR :: L.outputs) :=
    covers_writes (squeeze_writes L)
  refine call_okF hu (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Nat.le_of_eq v.squeeze_depth)
    hpre hcov (squeeze_writes L) fun w hw _ hp => ⟨hw, ?_⟩
  have hh := hp.1
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3, h4, hm,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hh
  exact hh

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    Spec.Sha3.squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [Spec.Sha3.squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

theorem shake256_eq (m : List Byte) (d : Nat) :
    Spec.Sha3.shake256 m d =
      Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix m)) 0 d := by
  rw [squeezeFrom_zero]; rfl

theorem sha3_bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha3.bytesAt m p n).length = n := by
  simp [Spec.Sha3.bytesAt]

/-- `SHAKE256(seed, 114)` in the frame, at `hashAt`. -/
theorem hash_ok (v : Proof.Sha3.AArch64.Permutation) (hc : Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : Arguments L m₀) :
    WP isa (Impl.Ed448.AArch64.PublicKey.hash v.callee) t fun u => Ctx L g vec m₀ u ∧
      Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 hashAt) 114 =
        Spec.Sha3.shake256 (Spec.Sha3.bytesAt m₀ L.seed 57) 114 := by
  refine WP.seq (WP.mono (zeroArgs_ok hc hL ha) fun t₀ ⟨hc₀, h15⟩ => ?_)
  refine WP.seq (WP.mono (zeroStores_ok hc₀ h15) fun t₁ ⟨hc₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (absorb_step v hc₁ hL ha hz₁) fun t₂ ⟨hc₂, hr₂⟩ => ?_)
  refine WP.seq (WP.mono (pad_step v hc₂ hL ha hr₂ (sha3_bytesAt_length _ _ _)) fun t₃ ⟨hc₃, hs₃⟩ => ?_)
  refine WP.mono (squeeze_step v hc₃ hL ha) fun t₄ ⟨hc₄, hb₄⟩ => ⟨hc₄, ?_⟩
  rw [hb₄, hs₃, shake256_eq]

end VG.Proof.Ed448.AArch64.PublicKey
