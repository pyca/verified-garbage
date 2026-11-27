module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
public import VerifiedGarbage.Impl.Ed448.AArch64.PublicKey
public import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Zero
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Prune
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
meta import VerifiedGarbage.Impl.Ed448.AArch64.PublicKey
meta import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
meta import VerifiedGarbage.Proof.Sha3.AArch64.Variant
meta import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Zero
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
meta import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Prune
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx
import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Spec.Ed448.Contract
meta import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx
meta import VerifiedGarbage.Proof.Framework.OffsetBelow

/-! ### `Ed448.AArch64.PublicKey.Layout`, which only this module used -/

section

/-!
# Ed448 public-key derivation on AArch64: where everything is

The function's buffers (`out`, `seed`, `scratch`) and the frame of the
complete AArch64 operations (`Proof.Ed25519.AArch64.Whole`), from `E` up: the
256 bytes of locals (the scalar at 0, the hash at 128), the saved arguments
(48 bytes, at 256), and the frame of a callee below `E` (`CK`). `Ctx` is what
holds in the frame's body; `setup_ok` moves a call's arguments into its
registers.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.X448.AArch64.Base (combSym combWords)

/-- The buffers and the lowest address of the frame (`sp - 336` on entry). -/
structure Lay where
  out : Addr
  seed : Addr
  scr : Addr
  E : Addr
  /-- The comb's tables (the static `combSym`), which `vg_ed448_scalar_base` reads. -/
  T : Addr

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨L.out, 57⟩
abbrev SEED : Region := ⟨L.seed, 57⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev ARGS : Region := VG.Proof.Ed25519.AArch64.Whole.ARGS L.E
abbrev FR : Region := VG.Proof.Ed25519.AArch64.Whole.FR L.E
abbrev STK : Region := ⟨L.E, 336⟩
/-- The frame of a callee, below the locals. -/
abbrev CK : Region := VG.Proof.Ed25519.AArch64.Whole.CK L.E
abbrev TB : Region := VG.Proof.Ed448.AArch64.Whole.TBL L.T
def inputs : List Region := [L.SEED, L.TB, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : Addr := match j with | 0 => L.out | 1 => L.seed | _ => L.scr

/-- What the contract says of where the buffers and the stack are. -/
structure Ok : Prop where
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 57 ≤ 2 ^ 64
  ns : L.seed.toNat + 57 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  e16 : 16 ≤ L.E.toNat
  co : L.CK.Disjoint L.OUT
  cs : L.CK.Disjoint L.SEED
  cc : L.CK.Disjoint L.SCR
  tbo : L.TB.Disjoint L.OUT
  tbc : L.TB.Disjoint L.SCR
  tbk : L.TB.Disjoint L.STK
  tbck : L.TB.Disjoint L.CK
  tbfit : L.T.toNat + 8 * combWords.length ≤ 2 ^ 64
end Lay

abbrev Ctx (L : Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) :=
  VG.Proof.Ed25519.AArch64.Whole.Ctx L.E g vec m₀ L.inputs L.outputs t

/-- The saved arguments, and the comb's words. -/
def Arguments (L : Lay) (m : Mem) : Prop :=
  (∀ j < 3, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j) ∧
    VG.Proof.Ed448.AArch64.Whole.TblWords L.T m

/-- What `setup` moves into a register. -/
def argValue (L : Lay) : Value → Addr
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem frame_sub (L : Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 256 ≤ 336)
theorem args_sub (L : Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

/-- The comb's words, as on entry: no write reaches them. -/
theorem Ctx.tbl (hc : Ctx L g vec m₀ t) (hL : L.Ok) (hm : VG.Proof.Ed448.AArch64.Whole.TblWords L.T m₀) :
    VG.Proof.Ed448.AArch64.Whole.TblWords L.T t.mem := fun i hi => by
  have := hL.tbfit
  rw [← hm i hi]
  refine hc.frame.readW (r := L.TB) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, this])) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.tbo
  · exact hL.tbc
  · exact hL.tbk.sub_right (frame_sub L)
  · exact hL.tbck

/-- The seed, as on entry. -/
theorem Ctx.seed_bytes (hc : Ctx L g vec m₀ t) (hL : L.Ok) :
    Spec.Ed448.bytesAt t.mem L.seed 57 = Spec.Ed448.bytesAt m₀ L.seed 57 := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := L.SEED) ?_ (by change 57 ≤ 2 ^ 64; decide)
    (List.mem_range.mp hi)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (frame_sub L)).symm
  · exact hL.cs.symm

theorem Ctx.arg_word (hc : Ctx L g vec m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 3) :
    t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      m₀.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 := by
  refine hc.frame.readW (r := L.ARGS)
    (Offset.contains _ (e := 256) (k := 48) (by omega_using []) (by omega_using [hj]) (by decide)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.ko.sub_left (args_sub L)
  · exact hL.kc.sub_left (args_sub L)
  · exact Offset.disjoint_base _ (by decide : 256 ≤ 256) (by decide : 256 + 48 ≤ 2 ^ 64)
  · exact ((Offset.below_disjoint L.E (m := 16) (l := 304) (by decide)).sub_right
      (Offset.sub_base _ (by decide : 256 + 48 ≤ 304))).symm

/-- A call's arguments, from the saved ones. -/
theorem setup_ok (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) t fun u => Ctx L g vec m₀ u ∧ u.mem = t.mem ∧
      ∀ p ∈ args, u.gpr p.1 = argValue L p.2 := by
  refine WP.mono (hc.setup hn hv (by simp [Lay.inputs]) hr) fun u ⟨hu, hm, hs⟩ => ⟨hu, hm, ?_⟩
  intro p hp
  rw [hs p hp]
  rcases p with ⟨r, v⟩
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    have hj := hi (r, .caller j d) hp j d rfl
    simp only [VG.Proof.Ed25519.AArch64.Whole.value, argValue]
    change t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL hj, ha.1 j hj]

end VG.Proof.Ed448.AArch64.PublicKey

end

end

/-! ### `Ed448.AArch64.PublicKey.Main`, which only this module used -/

section

/-! ### `Ed448.AArch64.PublicKey.Base`, which this module and modules that import it used -/

section

/-!
# Ed448 public-key derivation on AArch64: pruning and the base point

The first 57 bytes of the hash, pruned, are stored as the scalar at the
bottom of the frame (`prune_ok`), `[s]B` is encoded into `out` by
`vg_ed448_scalar_base` (`base_step`, given that it meets its contract, `BaseOk`), and the scalar and
the hash in the frame are cleared (`wipe_step`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (setup callWith Value zeroWord)
open VG.Proof.Ed25519.AArch64.Whole (call_ok Within)
open VG.Proof.Ed448.AArch64.Whole (prune_run)

/-! ## In the frame's body -/

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem prune_step (hc : Ctx L g vec m₀ t) {h : List Byte}
    (hh : Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114 = h) :
    WP isa (.block prune) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem L.E 57) = Spec.Ed448.prune h := by
  have hwrite : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  have hh' : Spec.Sha3.bytesAt t.mem (t.sp + BitVec.ofNat 64 hashAt) 114 = h := by rw [hc.sp]; exact hh
  refine WP.mono (prune_run (d := 0) hwrite (by decide) (by decide) (by decide) (by decide) (by decide) hh')
    fun u ⟨hu, hf, hp⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame hu.rd hu.wr hu.sp ?_ ?_ hf ?_
    · intro r hr _
      apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
    · intro r _; rw [hu.v]
    · rintro r hr
      rw [List.mem_singleton.mp hr, hc.sp, BitVec.add_zero]
      exact .inl (Region.sub_prefix (by decide))
  · rw [hc.sp, BitVec.add_zero] at hp
    exact hp

theorem base_noFrames : Impl.Ed448.AArch64.scalarBase.noFrames = true :=
  Proof.Ed448.AArch64.scalarBase_noFrames

def baseValues : List (Reg × Value) := [(.x0, .caller 0 0), (.x1, .frame 0), (.x2, .caller 2 0)]

theorem base_pre (hL : L.Ok) {u : State} (hs : ∀ p ∈ baseValues, u.gpr p.1 = argValue L p.2)
    (hsy : u.syms Impl.X448.AArch64.Base.combSym = L.T)
    (hm : VG.Proof.Ed448.AArch64.Whole.TblWords L.T u.mem) :
    Proof.Ed448.AArch64.scalarBaseLocal.pre (u.callEntry.withRegions [⟨L.E, 57⟩, L.TB] L.outputs) := by
  have h0 := hs (.x0, .caller 0 0) (List.mem_of_getElem? (i := 0) rfl)
  have h1 := hs (.x1, .frame 0) (List.mem_of_getElem? (i := 1) rfl)
  have h2 := hs (.x2, .caller 2 0) (List.mem_of_getElem? (i := 2) rfl)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have hT : (u.callEntry.withRegions [⟨L.E, 57⟩, L.TB] L.outputs).syms Impl.X448.AArch64.Base.combSym = L.T :=
    hsy
  have hC : VG.Proof.X448.AArch64.Base.CombHeld (u.callEntry.withRegions [⟨L.E, 57⟩, L.TB] L.outputs)
      [⟨L.out, 57⟩, ⟨L.scr, 8192⟩] := by
    refine ⟨fun i hi => ?_, ?_, fun r hr => ?_⟩
    · rw [hT]; exact hm i hi
    · rw [hT]; exact hL.tbfit
    · rw [hT]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hL.tbo, hL.tbc]
  simp only [Proof.Ed448.AArch64.scalarBaseLocal, Proof.Ed448.AArch64.tblRegion, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2, hT]
  exact ⟨trivial, rfl, hL.oc, hL.kc.sub_left (Region.sub_prefix (by decide)), hL.nc, hC⟩

theorem base_covers (L : Lay) :
    Covers ([⟨L.E, 57⟩, L.TB] ++ L.outputs) (L.inputs ++ L.FR :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, 0, (BitVec.add_zero _).symm,
        by change 0 + 57 ≤ 256; decide⟩
    · exact ⟨L.TB, List.mem_append_left _ (by simp [Lay.inputs]), 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_writes (L : Lay) : ∀ r ∈ L.outputs, Within r L.FR ∨ ∃ R ∈ L.outputs, Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_step (hb : Proof.Ed448.AArch64.BaseOk) (hc : Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : Arguments L m₀) {n : Nat}
    (hs : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t.mem L.E 57) = n)
    (hsy : t.syms Impl.X448.AArch64.Base.combSym = L.T) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed448.bytesAt u.mem L.out 57 =
        Spec.Ed448.encodePoint (Spec.Ed448.pointMul n Spec.Ed448.basePoint) := by
  refine WP.seq (WP.mono_syms (setup_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 0), (.x2, .caller 2 0)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp) (by decide))
    fun u ⟨hu, hm, hav⟩ sy => ?_)
  have h0 := hav (.x0, .caller 0 0) (by simp)
  have h1 := hav (.x1, .frame 0) (by simp)
  have h2 := hav (.x2, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have hpre := base_pre hL (u := u) (fun p hp => hav p hp) (by rw [sy]; exact hsy) (hu.tbl hL ha.2)
  refine call_ok hu hb.ok base_noFrames hpre (base_covers L)
    (base_writes L) fun w hw _ hp => ⟨hw, ?_⟩
  change Spec.Ed448.bytesAt w.mem (u.callEntry.gpr .x0) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1, hm] at hp
  rw [hp, Spec.Ed448.scalarBase, hs]

theorem wipe_step (hc : Ctx L g vec m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed448.bytesAt u.mem L.out 57 = Spec.Ed448.bytesAt t.mem L.out 57 := by
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.Ctx.zeroWords hc (start := 0) (count := 32) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 0 + 8 * 32 ≤ 336))).symm

end VG.Proof.Ed448.AArch64.PublicKey

end

end

/-! ### `Ed448.AArch64.PublicKey.Hash`, which this module and modules that import it used -/

section

/-!
# Ed448 public-key derivation on AArch64: `SHAKE256(seed, 114)`

The Keccak state in `scratch` zeroed (`zero_ok`), the seed absorbed, the
padding absorbed, and 114 bytes squeezed into the frame (`hash_ok`), with
any implementation `v` of the permutation: each call is of the sponge
function's correctness for `v` (`Proof.Sha3.AArch64.Stream`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (setup callWith Value)
open VG.Proof.Ed25519.AArch64.Whole (call_okF Within)
open VG.Spec.Sha3 (stateAt)
open VG.Impl.Ed448.AArch64.Whole (zeroStores)
open VG.Proof.Ed448.AArch64.Whole (movz14_ok zstores_ok zero_state)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-! ## The state zeroed -/

theorem zeroArgs_ok (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (.block zeroArgs) t fun w => Ctx L g vec m₀ w ∧ w.gpr .x15 = L.scr := by
  refine WP.mono (setup_ok hc hL ha (args := [(.x15, .caller 2 0)]) (by decide)
    (by simp [VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp) (by decide))
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
  refine WP.mono (zstores_ok ((wg _ (by decide)).trans h15) w14 hws 25 (by omega_using [])) fun x hx =>
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
  have h0 := hs (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl)
  have h1 := hs (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl)
  have h2 := hs (.x2, .const 0) (List.mem_of_getElem? (i := 2) rfl)
  have h3 := hs (.x3, .caller 1 0) (List.mem_of_getElem? (i := 3) rfl)
  have h4 := hs (.x4, .const 57) (List.mem_of_getElem? (i := 4) rfl)
  have h5 := hs (.x5, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 5) rfl)
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
  have h0 := hs (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl)
  have h1 := hs (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl)
  have h2 := hs (.x2, .const 57) (List.mem_of_getElem? (i := 2) rfl)
  have h4 := hs (.x4, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 4) rfl)
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
  have h0 := hs (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl)
  have h1 := hs (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl)
  have h2 := hs (.x2, .const 0) (List.mem_of_getElem? (i := 2) rfl)
  have h3 := hs (.x3, .frame hashAt) (List.mem_of_getElem? (i := 3) rfl)
  have h4 := hs (.x4, .const 114) (List.mem_of_getElem? (i := 4) rfl)
  have h5 := hs (.x5, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 5) rfl)
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
    WP isa (callWith absorbArgs ("vg_keccak_absorb_scratch" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.absorbWith v.callee)) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Sha3.Repr u.mem L.scr 136 (Spec.Sha3.bytesAt m₀ L.seed 57) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 0), (.x3, .caller 1 0), (.x4, .const 57),
      (.x5, .caller 2 keccakScratch)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp)
    (by decide)) fun u ⟨hu, hm, hs⟩ => ?_)
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
    WP isa (callWith padArgs ("vg_keccak_pad_scratch" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.padWith v.callee)) t fun u =>
      Ctx L g vec m₀ u ∧ stateAt u.mem L.scr =
        Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 57), (.x3, .const 0x1f),
      (.x4, .caller 2 keccakScratch)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp)
    (by decide)) fun u ⟨hu, hm, hs⟩ => ?_)
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
    WP isa (callWith squeezeArgs ("vg_keccak_squeeze_scratch" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 hashAt) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem L.scr) 0 114 := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 0), (.x3, .frame hashAt),
      (.x4, .const 114), (.x5, .caller 2 keccakScratch)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch, hashAt]) (by simp)
    (by decide)) fun u ⟨hu, hm, hs⟩ => ?_)
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

end

end

/-!
# Ed448 public-key derivation on AArch64: the whole function

The contract the proof is written against (`pkLocal`: the facts of
`Spec.Ed448.publicKeyContract` for 352 bytes of stack, stated for AArch64),
and the correctness of `vg_ed448_public_key` against it, for any
implementation `v` of the Keccak permutation, given that
`vg_ed448_scalar_base` meets its contract (`BaseOk`, which the generic file passes in):
`SHAKE256(seed, 114)`, pruned, multiplies the base point into `out`; the
frame (`Proof.Ed25519.AArch64.Whole.wrap_ok`) restores `x30` and the stack
pointer, and the callee-saved registers are never written.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey
open VG.Impl.X448.AArch64.Base (combSym combWords)
open VG.Proof.X448.AArch64.Base (CombHeld)

/-- `vg_ed448_public_key(out = x0, seed = x1, scratch = x2)`, with 352 bytes of stack. -/
def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 57⟩
    let seed : Region := ⟨s.gpr .x1, 57⟩
    let scr : Region := ⟨s.gpr .x2, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [seed, VG.Proof.Ed448.AArch64.Whole.TBL (s.syms combSym)] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 57 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat ∧ CombHeld s [out, scr, stk]
  post s t := Spec.Ed448.bytesAt t.mem (s.gpr .x0) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.syms combSym = t.syms combSym

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, VG.Proof.Ed25519.AArch64.Whole.base s, s.syms combSym⟩

theorem lay_ok {s : State} (h : pkLocal.pre s) : (lay s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hsp, -, fit, dj⟩ := h
  have dk := dj (below s.sp 352) (by simp)
  exact ⟨os, oc, sc, ko.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s),
    ks.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s),
    kc.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s), no, ns, nc,
    VG.Proof.Ed25519.AArch64.Whole.base_16 hsp, ko.sub_left (VG.Proof.Ed25519.AArch64.Whole.ck_sub s),
    ks.sub_left (VG.Proof.Ed25519.AArch64.Whole.ck_sub s), kc.sub_left (VG.Proof.Ed25519.AArch64.Whole.ck_sub s),
    dj ⟨s.gpr .x0, 57⟩ (by simp), dj ⟨s.gpr .x2, 8192⟩ (by simp),
    dk.sub_right (VG.Proof.Ed25519.AArch64.Whole.stk_sub s),
    dk.sub_right (VG.Proof.Ed25519.AArch64.Whole.ck_sub s), fit⟩

theorem entry_below {s : State} (h : pkLocal.pre s) : 352 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.1

theorem entry_writes {s : State} (h : pkLocal.pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1

theorem entry_ctx {s p : State} (h : pkLocal.pre s)
    (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr s.v p.mem (p.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd s)
      (VG.Proof.Ed25519.AArch64.Whole.bodyWr s)) := by
  have hc := VG.Proof.Ed25519.AArch64.Whole.saved_ctx hp
  simpa only [VG.Proof.Ed25519.AArch64.Whole.bodyRd, h.1, VG.Proof.Ed25519.AArch64.Whole.bodyWr, h.2.1,
    Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, Lay.TB, lay, List.cons_append,
    List.nil_append] using hc

theorem entry_args {s p : State} (h : pkLocal.pre s)
    (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p) :
    Arguments (lay s) p.mem := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have hw := VG.Proof.Ed25519.AArch64.Whole.saved_words hp (j := j) (by omega_using [hj])
    have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
    rcases he with rfl | rfl | rfl <;> exact hw
  · obtain ⟨held, fit, dj⟩ := h.2.2.2.2.2.2.2.2.2.2.2.2
    have hf := VG.Proof.Ed25519.AArch64.Whole.saved_frame hp
    rw [← held i hi]
    refine hf.readW (r := VG.Proof.Ed448.AArch64.Whole.TBL (s.syms combSym))
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, fit])) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton.mp hr]
    exact (dj (below s.sp 352) (by simp)).sub_right (VG.Proof.Ed25519.AArch64.Whole.stk_sub s)

theorem entry_syms {s p : State}
    (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p) :
    (p.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd s)
      (VG.Proof.Ed25519.AArch64.Whole.bodyWr s)).syms combSym = (lay s).T :=
  congrFun hp.step.syms combSym

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem body_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk)
    (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) (hsy : t.syms combSym = L.T) :
    WP isa (body v.callee) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed448.bytesAt u.mem L.out 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57) := by
  refine WP.seq (WP.mono_syms (hash_ok v hc hL ha) fun u ⟨hu, hh⟩ su => ?_)
  refine WP.seq (WP.mono_syms (prune_step hu hh) fun u' ⟨hu', hs⟩ su' => ?_)
  refine WP.seq (WP.mono (base_step hb hu' hL ha hs (by rw [su', su]; exact hsy)) fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

theorem body_depth (v : Proof.Sha3.AArch64.Permutation) : (body v.callee).aarch64Depth ≤ 1 := by
  have ha := v.absorb_depth
  have hp := v.pad_depth
  have hs := v.squeeze_depth
  have hb := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames base_noFrames
  simp only [body, Impl.Ed448.AArch64.PublicKey.hash, Impl.Ed25519.AArch64.Whole.callWith, Code.aarch64Depth, Nat.max_le, hb, ha, hp, hs]
  omega_using []

theorem publicKey_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) {s : State}
    (h : pkLocal.pre s) :
    WP isa (publicKeyWith v.callee) s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := VG.Proof.Ed25519.AArch64.Whole.wrap_ok (body_depth v) (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed448.bytesAt m' (s.gpr .x0) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m (s.gpr .x1) 57))
    (hP := fun _ _ _ _ f hq => (List.map_congr_left fun i hi => VG.AArch64.lost_byte f
      ((entry_writes h ⟨s.gpr .x0, 57⟩ (by rw [h.2.1]; simp)).symm.sub_right
        (VG.AArch64.below_sub (by decide) (by decide))) (List.mem_range.mp hi)).trans hq)
    (fun p hp => WP.mono (body_ok v hb (entry_ctx h hp) (lay_ok h) (entry_args h hp) (entry_syms hp))
      fun u ⟨hu, ho⟩ => ⟨by
      simpa only [VG.Proof.Ed25519.AArch64.Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED,
        Lay.OUT, Lay.SCR, Lay.ARGS, Lay.TB, lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed448.bytesAt m (s.gpr .x1) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨s.gpr .x1, 57⟩) ?_
      (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed448.bytesAt u.mem (s.gpr .x0) 57 = _
  rw [hp, hs]

end VG.Proof.Ed448.AArch64.PublicKey

end

end

/-!
# Ed448 public-key derivation on AArch64: `Verified`

Correctness including the ABI (`publicKey_ok`), for any implementation `v`
of the Keccak permutation, given that `vg_ed448_scalar_base` meets
its contract in constant time (`BaseOk`, which the generic file passes in). Constant time: two runs whose pointers agree have the same
layout, so in the frame's body they are related by `Two`: both satisfy `Ctx`
with that layout (and what the next block or call needs of the registers,
`Slots`), whatever their secrets. The blocks address only the stack and
`scratch`, from registers that agree (the taint analysis); each call is of
constant-time code (the sponge functions for `v`, `vg_ed448_scalar_base`)
whose public data, its pointers and lengths, agree (`Whole.callEx`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (Value setup callWith)
open VG.Impl.Ed448.AArch64.Whole (zeroStores)
open VG.Impl.X448.AArch64.Base (combSym combWords combConsts)

abbrev Two (L : Lay) (g₁ g₂ : Reg → Addr) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) :=
  (Ctx L g₁ v₁ m₁ a ∧ a.syms combSym = L.T ∧ P a) ∧ (Ctx L g₂ v₂ m₂ b ∧ b.syms combSym = L.T ∧ P b)

/-- The registers hold what `setup args` moves into them. -/
def Slots (L : Lay) (args : List (Reg × Value)) (s : State) := ∀ p ∈ args, s.gpr p.1 = argValue L p.2

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L args)) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) ht) ?_ ?_
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (setup_ok hc hL ha hn hv hi hr) fun _ ⟨hc, _, hs⟩ sy => ⟨hc, sy ▸ hy, hs⟩
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (setup_ok hc hL hb hn hv hi hr) fun _ ⟨hc, _, hs⟩ sy => ⟨hc, sy ▸ hy, hs⟩

theorem call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → t.syms combSym = L.T →
      VG.Proof.Ed448.AArch64.Whole.TblWords L.T t.mem → Slots L args t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp → a.syms combSym = b.syms combSym →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L args)) (.call name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp ?_ ?_ ?_
  · refine VG.Proof.Ed25519.AArch64.Whole.callEx correct ct fun a b h => ?_
    let ra := ready a h.1.1.sp h.1.2.1 (h.1.1.tbl hL ha.2) h.1.2.2
    let rb := ready b h.2.1.sp h.2.2.1 (h.2.1.tbl hL hb.2) h.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (h.1.1.sp.trans h.2.1.sp.symm) (h.1.2.1.trans h.2.2.1.symm) ?_, ca, wa, cb, wb⟩
    intro p hp
    rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2.2 p hp, h.2.2.2 p hp]
  · intro t ⟨hc, hy, hs⟩
    exact WP.mono_syms ((ready t hc.sp hy (hc.tbl hL ha.2) hs).wpF hc correct hd)
      fun _ hu sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, hs⟩
    exact WP.mono_syms ((ready t hc.sp hy (hc.tbl hL hb.2) hs).wpF hc correct hd)
      fun _ hu sy => ⟨hu, sy ▸ hy, trivial⟩

/-- A call's arguments, then the call. -/
theorem callWith_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true)
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → t.syms combSym = L.T →
      VG.Proof.Ed448.AArch64.Whole.TblWords L.T t.mem → Slots L args t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp → a.syms combSym = b.syms combSym →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (callWith (setup args) name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb args hn hv hi hr ht).seq (call_ct hL ha hb correct ct hd ready kp hl)

/-! ## Each block and call -/

def zeroValues : List (Reg × Value) := [(.x15, .caller 2 0)]

theorem zeroStores_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L zeroValues)) (.block zeroStores)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have h15 : ∀ {t : State}, Slots L zeroValues t → t.gpr .x15 = L.scr := fun hs => by
    have h := hs (.x15, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl)
    simp only [argValue, Lay.value, BitVec.add_zero] at h
    exact h
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (RelCT.taint (A := taint) (Taint.ofRegs [.x15]) (fun a b h => ⟨h.1.1.sp.trans h.2.1.sp.symm,
      fun r hr => ?_⟩) (by taint_decide)) ?_ ?_
  · simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr
    rw [h15 h.1.2.2, h15 h.2.2.2]
  · intro t ⟨hc, hy, hs⟩
    exact WP.mono_syms (zeroStores_ok hc (h15 hs)) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, hs⟩
    exact WP.mono_syms (zeroStores_ok hc (h15 hs)) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

theorem prune_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block prune)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
      (by taint_decide)) ?_ ?_
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (prune_step hc (h := Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114) rfl)
      fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (prune_step hc (h := Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114) rfl)
      fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
      (by taint_decide)) ?_ ?_
  · intro t ⟨hc, hy, _⟩; exact WP.mono_syms (wipe_step hc hL) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, _⟩; exact WP.mono_syms (wipe_step hc hL) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

def absorb_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : Slots L absorbValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.absorbAArch64 L.E L.inputs L.outputs t :=
  ⟨[L.SEED], [ST L, KS L], absorb_pre hL hsp hs, absorb_covers L, sponge_writes L⟩

def pad_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : Slots L padValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.padAArch64 L.E L.inputs L.outputs t :=
  ⟨[], [ST L, KS L], pad_pre hL hsp hs, covers_writes (sponge_writes L), sponge_writes L⟩

def squeeze_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : Slots L squeezeValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.squeezeAArch64 L.E L.inputs L.outputs t :=
  ⟨[], [ST L, HS L, KS L], squeeze_pre hL hsp hs, covers_writes (squeeze_writes L), squeeze_writes L⟩

def base_ready (hL : L.Ok) {t : State} (hsy : t.syms combSym = L.T)
    (hm : VG.Proof.Ed448.AArch64.Whole.TblWords L.T t.mem) (hs : Slots L baseValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Ed448.AArch64.scalarBaseLocal L.E L.inputs L.outputs t :=
  ⟨[⟨L.E, 57⟩, L.TB], L.outputs, base_pre hL hs hsy hm, base_covers L, base_writes L⟩

theorem body_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) (hL : L.Ok)
    (ha : Arguments L m₁) (hb' : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body v.callee)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have z := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb' zeroValues
    (by decide) (by simp [zeroValues, VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp [zeroValues])
    (by decide) (by taint_decide)
  have a := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_keccak_absorb_scratch" ++ v.callee.suffix)
    hL ha hb' (args := absorbValues) (by decide)
    (by simp [absorbValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp [absorbValues])
    (by decide) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v)
    (Nat.le_of_eq v.absorb_depth) (fun _ hsp _ _ hs => absorb_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp _ hg => ⟨hg (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .const 0) (List.mem_of_getElem? (i := 2) rfl),
      hg (.x3, .caller 1 0) (List.mem_of_getElem? (i := 3) rfl), hg (.x4, .const 57) (List.mem_of_getElem? (i := 4) rfl),
      hg (.x5, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 5) rfl), hsp⟩)
    (by decide)
  have p := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_keccak_pad_scratch" ++ v.callee.suffix)
    hL ha hb' (args := padValues) (by decide)
    (by simp [padValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp [padValues])
    (by decide) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    (Nat.le_of_eq v.pad_depth) (fun _ hsp _ _ hs => pad_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp _ hg => ⟨hg (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .const 57) (List.mem_of_getElem? (i := 2) rfl),
      hg (.x4, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 4) rfl), hsp⟩)
    (by decide)
  have q := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂)
    (name := "vg_keccak_squeeze_scratch" ++ v.callee.suffix)
    hL ha hb' (args := squeezeValues) (by decide)
    (by simp [squeezeValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch, hashAt])
    (by simp [squeezeValues]) (by decide) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v)
    (Nat.le_of_eq v.squeeze_depth) (fun _ hsp _ _ hs => squeeze_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp _ hg => ⟨hg (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .const 0) (List.mem_of_getElem? (i := 2) rfl),
      hg (.x3, .frame hashAt) (List.mem_of_getElem? (i := 3) rfl), hg (.x4, .const 114) (List.mem_of_getElem? (i := 4) rfl),
      hg (.x5, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 5) rfl), hsp⟩)
    (by decide)
  have b := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_ed448_scalar_base")
    hL ha hb' (args := baseValues) (by decide)
    (by simp [baseValues, VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp [baseValues])
    (by decide) (by taint_decide)
    hb.ok hb.ct
    (VG.Proof.Ed25519.AArch64.Whole.depth_of_noFrames base_noFrames) (fun _ _ hy hm hs => base_ready hL hy hm hs)
    (fun _ _ _ _ _ _ hsp hy hg => ⟨hsp, hg (.x0, .caller 0 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .frame 0) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .caller 2 0) (List.mem_of_getElem? (i := 2) rfl),
      hy⟩)
    (by decide)
  exact (z.seq (zeroStores_ct.seq (a.seq (p.seq q)))).seq (prune_ct.seq (b.seq (wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, hsy⟩ := hp
  simp only [lay, VG.Proof.Ed25519.AArch64.Whole.base, sp, h0, h1, h2, hsy]

theorem publicKey_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) :
    ConstantTime isa pkLocal.pre pkLocal.pub (publicKeyWith v.callee) := by
  refine VG.Proof.Ed25519.AArch64.Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok v hb (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp) (entry_syms hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    have hqs : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).syms combSym = (lay s).T := he ▸ entry_syms hqb
    exact ⟨(body_ct v hb (lay_ok hs) (entry_args hs hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, entry_syms hpa, trivial⟩, ⟨hq, hqs, trivial⟩⟩ ea eb).1, trivial⟩

open VG.Proof.X448.AArch64.Base (combWords_length satMem satMem_held)

def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x9000
  mem := satMem
  rd := [⟨0x2000, 57⟩, ⟨0x100000, 58368⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State} (hsp : 352 ≤ s.sp.toNat)
    (hrd : s.rd = [⟨s.gpr .x1, 57⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩])
    (hheld : ∀ i < combWords.length,
      s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0)
    (hfit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ r)
    (hds : Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ ⟨s.sp - 352#64, 352⟩)
    (hal : (s.syms combSym).toNat % 64 = 0)
    (hrest : (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x1, 57⟩ ∧
      (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (⟨s.gpr .x1, 57⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x0, 57⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x1, 57⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 57 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64) :
    (Spec.Ed448.publicKeyContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  sig_pre [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
    Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
    VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hrest
  exact ⟨hsp, by rw [hrd]; rfl, hheld, hfit, hdw, hds, hal, by rw [hrd]; rfl, hw, r1, r2, r3, r4, r5, r6, r7,
    r8, r9⟩

theorem sat : ∃ s, (Spec.Ed448.publicKeyContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  have hl := combWords_length
  refine ⟨satState, spec_pre (by decide) (by rw [hl]; rfl) rfl satMem_held (by rw [hl]; decide) ?_
    (by rw [hl]; exact Region.disjoint_of_sep (by decide)) (by decide) ?_⟩
  · rw [hl]
    simp only [satState, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem pk_implies : pkLocal.Implies
    (Spec.Ed448.publicKeyContract (AArch64.abi.withConsts combConsts) 352) where
  pre s h := by
    sig_pre [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hsp, hd, held, fit, hdw, hds, -, ht, hw, os, oc, sc, ko, ks, kc, no, ns, nc⟩ := h
    refine ⟨?_, hw, os, oc, sc, ko, ks, kc, no, ns, nc, hsp, held, fit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hds
  post := by
    sig_implies_post [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
      Spec.Ed448.scratchWords, pkLocal, below, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts]
  pub := by
    sig_implies_pub [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
      Spec.Ed448.scratchWords, pkLocal, below, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts]
  sat := sat

theorem publicKey_verified (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) :
    Verified AArch64.target (publicKeyWith v.callee)
      (Spec.Ed448.publicKeyContract (AArch64.abi.withConsts combConsts) 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => publicKey_ok v hb h) (publicKey_ct v hb) (.refl pk_implies.sat_left))
    pk_implies

end VG.Proof.Ed448.AArch64.PublicKey
