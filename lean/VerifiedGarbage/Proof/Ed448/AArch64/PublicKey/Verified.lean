import VerifiedGarbage.Impl.Ed448.AArch64.PublicKey
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Prune
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Layout`. -/
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

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

/-- The buffers and the lowest address of the frame (`sp - 336` on entry). -/
structure Lay where
  out : Addr
  seed : Addr
  scr : Addr
  E : Addr

namespace Lay
variable (L : VG.Proof.Ed448.AArch64.PublicKey.Lay)
abbrev OUT : Region := ⟨L.out, 57⟩
abbrev SEED : Region := ⟨L.seed, 57⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev ARGS : Region := VG.Proof.Ed25519.AArch64.Whole.ARGS L.E
abbrev FR : Region := VG.Proof.Ed25519.AArch64.Whole.FR L.E
abbrev STK : Region := ⟨L.E, 336⟩
/-- The frame of a callee, below the locals. -/
abbrev CK : Region := VG.Proof.Ed25519.AArch64.Whole.CK L.E
def inputs : List Region := [L.SEED, L.ARGS]
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
end Lay

abbrev Ctx (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) :=
  VG.Proof.Ed25519.AArch64.Whole.Ctx L.E g vec m₀ L.inputs L.outputs t

/-- The saved arguments. -/
def Arguments (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) (m : Mem) : Prop :=
  ∀ j < 3, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j

/-- What `setup` moves into a register. -/
def argValue (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Value → Addr
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

variable {L : VG.Proof.Ed448.AArch64.PublicKey.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem frame_sub (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 256 ≤ 336)
theorem args_sub (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

/-- The seed, as on entry. -/
theorem Ctx.seed_bytes (hc : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) :
    Spec.Ed448.bytesAt t.mem L.seed 57 = Spec.Ed448.bytesAt m₀ L.seed 57 := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := L.SEED) ?_ (by change 57 ≤ 2 ^ 64; decide)
    (List.mem_range.mp hi)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (VG.Proof.Ed448.AArch64.PublicKey.frame_sub L)).symm
  · exact hL.cs.symm

theorem Ctx.arg_word (hc : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 3) :
    t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      m₀.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 := by
  refine hc.frame.readW (r := L.ARGS)
    (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.ko.sub_left (VG.Proof.Ed448.AArch64.PublicKey.args_sub L)
  · exact hL.kc.sub_left (VG.Proof.Ed448.AArch64.PublicKey.args_sub L)
  · exact Offset.disjoint_base _ (by decide : 256 ≤ 256) (by decide : 256 + 48 ≤ 2 ^ 64)
  · exact ((Offset.below_disjoint L.E (m := 16) (l := 304) (by decide)).sub_right
      (Offset.sub_base _ (by decide : 256 + 48 ≤ 304))).symm

/-- A call's arguments, from the saved ones. -/
theorem setup_ok (hc : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.AArch64.PublicKey.Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) t fun u => VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ u ∧ u.mem = t.mem ∧
      ∀ p ∈ args, u.gpr p.1 = VG.Proof.Ed448.AArch64.PublicKey.argValue L p.2 := by
  refine WP.mono (hc.setup hn hv (by simp [Lay.inputs]) hr) fun u ⟨hu, hm, hs⟩ => ⟨hu, hm, ?_⟩
  intro p hp
  rw [hs p hp]
  rcases p with ⟨r, v⟩
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    have hj := hi (r, .caller j d) hp j d rfl
    simp only [VG.Proof.Ed25519.AArch64.Whole.value, VG.Proof.Ed448.AArch64.PublicKey.argValue]
    change t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL hj, ha j hj]

end VG.Proof.Ed448.AArch64.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Hash`. -/
section

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
open VG.Impl.Ed448.AArch64.Whole (zeroStores)
open VG.Proof.Ed448.AArch64.Whole (movz14_ok zstores_ok zero_state)

variable {L : VG.Proof.Ed448.AArch64.PublicKey.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-! ## The state zeroed -/

theorem zeroArgs_ok (hc : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.AArch64.PublicKey.Arguments L m₀) :
    WP isa (.block zeroArgs) t fun w => VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ w ∧ w.gpr .x15 = L.scr := by
  refine WP.mono (VG.Proof.Ed448.AArch64.PublicKey.setup_ok hc hL ha (args := [(.x15, .caller 2 0)]) (by decide)
    (by simp [VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp) (by decide))
    fun u ⟨hu, _, hs⟩ => ⟨hu, ?_⟩
  have h15 := hs (.x15, .caller 2 0) (by simp)
  simp only [VG.Proof.Ed448.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h15
  exact h15

theorem zeroStores_ok {u : State} (hu : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ u) (h15 : u.gpr .x15 = L.scr) :
    WP isa (.block zeroStores) u fun x => VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ x ∧ VG.Spec.Sha3.stateAt x.mem L.scr = Spec.Sha3.zero := by
  rw [zeroStores, show ∀ (i : Instr) is, i :: is = [i] ++ is from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (movz14_ok u) fun w ⟨w14, wm, wrd, wwr, wsp, wv, wg⟩ => ?_
  have hw : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ w :=
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

abbrev ST (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Region := ⟨L.scr, 200⟩
abbrev KS (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Region := ⟨L.scr + BitVec.ofNat 64 keccakScratch, 640⟩
abbrev HS (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Region := ⟨L.E + BitVec.ofNat 64 hashAt, 114⟩

theorem st_sub (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Region.Sub (VG.Proof.Ed448.AArch64.PublicKey.ST L) L.SCR := Region.sub_prefix (by decide)
theorem ks_sub (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Region.Sub (VG.Proof.Ed448.AArch64.PublicKey.KS L) L.SCR := Offset.sub_base _ (by decide)
theorem hs_sub (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Region.Sub (VG.Proof.Ed448.AArch64.PublicKey.HS L) L.FR := Offset.sub_base _ (by decide)
theorem st_ks (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : (VG.Proof.Ed448.AArch64.PublicKey.ST L).Disjoint (VG.Proof.Ed448.AArch64.PublicKey.KS L) := Offset.base_disjoint _ (by decide) (by decide)

theorem covers_writes {E : Addr} {rd wr ws : List Region}
    (hw : ∀ r ∈ ws, VG.Proof.Ed25519.AArch64.Whole.Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.AArch64.Whole.Within r R) :
    Covers ws (rd ++ VG.Proof.Ed25519.AArch64.Whole.FR E :: wr) := by
  refine Covers.of_sub fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨_, List.mem_append_right _ List.mem_cons_self, hf⟩
  · exact ⟨R, List.mem_append_right _ (List.mem_cons_of_mem _ hR), hs⟩

theorem sponge_writes (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : ∀ r ∈ [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.KS L],
    VG.Proof.Ed25519.AArch64.Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, VG.Proof.Ed25519.AArch64.Whole.Within r R := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 200 ≤ 8192; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], keccakScratch, rfl, by change 256 + 640 ≤ 8192; decide⟩

theorem squeeze_writes (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : ∀ r ∈ [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.HS L, VG.Proof.Ed448.AArch64.PublicKey.KS L],
    VG.Proof.Ed25519.AArch64.Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, VG.Proof.Ed25519.AArch64.Whole.Within r R := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 200 ≤ 8192; decide⟩
  · exact .inl ⟨hashAt, rfl, by change 128 + 114 ≤ 256; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], keccakScratch, rfl, by change 256 + 640 ≤ 8192; decide⟩

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : VG.Spec.Sha3.stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show VG.Spec.Sha3.stateAt mem p = Proof.Sha3.Rep rate []
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
    (hs : ∀ p ∈ VG.Proof.Ed448.AArch64.PublicKey.absorbValues, u.gpr p.1 = VG.Proof.Ed448.AArch64.PublicKey.argValue L p.2) :
    Proof.Sha3.absorbAArch64.pre (u.callEntry.withRegions [L.SEED] [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.KS L]) := by
  have h0 := hs (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl)
  have h1 := hs (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl)
  have h2 := hs (.x2, .const 0) (List.mem_of_getElem? (i := 2) rfl)
  have h3 := hs (.x3, .caller 1 0) (List.mem_of_getElem? (i := 3) rfl)
  have h4 := hs (.x4, .const 57) (List.mem_of_getElem? (i := 4) rfl)
  have h5 := hs (.x5, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 5) rfl)
  simp only [VG.Proof.Ed448.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4 h5
  simp only [Proof.Sha3.absorbAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x5 ∉ linkRegs), h0, h1, h2, h3, h4, h5, hsp,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨trivial, trivial, VG.Proof.Ed448.AArch64.PublicKey.st_ks L, hL.sc.sub_right (VG.Proof.Ed448.AArch64.PublicKey.st_sub L), hL.sc.sub_right (VG.Proof.Ed448.AArch64.PublicKey.ks_sub L), hL.e16,
    hL.cc.sub_right (VG.Proof.Ed448.AArch64.PublicKey.st_sub L), hL.cs, hL.cc.sub_right (VG.Proof.Ed448.AArch64.PublicKey.ks_sub L), by decide, by decide⟩

theorem absorb_covers (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Covers ([L.SEED] ++ [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.KS L]) (L.inputs ++ L.FR :: L.outputs) := by
  intro a n hin
  obtain ⟨r, hr, hh⟩ := hin
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr] at hh
    exact ⟨L.SEED, List.mem_append_left _ (by simp [Lay.inputs]), hh⟩
  · exact VG.Proof.Ed448.AArch64.PublicKey.covers_writes (VG.Proof.Ed448.AArch64.PublicKey.sponge_writes L) a n ⟨r, hr, hh⟩

theorem pad_pre (hL : L.Ok) {u : State} (hsp : u.sp = L.E)
    (hs : ∀ p ∈ VG.Proof.Ed448.AArch64.PublicKey.padValues, u.gpr p.1 = VG.Proof.Ed448.AArch64.PublicKey.argValue L p.2) :
    Proof.Sha3.padAArch64.pre (u.callEntry.withRegions [] [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.KS L]) := by
  have h0 := hs (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl)
  have h1 := hs (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl)
  have h2 := hs (.x2, .const 57) (List.mem_of_getElem? (i := 2) rfl)
  have h4 := hs (.x4, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 4) rfl)
  simp only [VG.Proof.Ed448.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h4
  simp only [Proof.Sha3.padAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h4, hsp,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨trivial, trivial, VG.Proof.Ed448.AArch64.PublicKey.st_ks L, hL.e16, hL.cc.sub_right (VG.Proof.Ed448.AArch64.PublicKey.st_sub L), hL.cc.sub_right (VG.Proof.Ed448.AArch64.PublicKey.ks_sub L),
    by decide, by decide⟩

theorem hs_stk (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Region.Sub (VG.Proof.Ed448.AArch64.PublicKey.HS L) L.STK := Offset.sub_base _ (by decide)

theorem squeeze_pre (hL : L.Ok) {u : State} (hsp : u.sp = L.E)
    (hs : ∀ p ∈ VG.Proof.Ed448.AArch64.PublicKey.squeezeValues, u.gpr p.1 = VG.Proof.Ed448.AArch64.PublicKey.argValue L p.2) :
    Proof.Sha3.squeezeAArch64.pre (u.callEntry.withRegions [] [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.HS L, VG.Proof.Ed448.AArch64.PublicKey.KS L]) := by
  have h0 := hs (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl)
  have h1 := hs (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl)
  have h2 := hs (.x2, .const 0) (List.mem_of_getElem? (i := 2) rfl)
  have h3 := hs (.x3, .frame hashAt) (List.mem_of_getElem? (i := 3) rfl)
  have h4 := hs (.x4, .const 114) (List.mem_of_getElem? (i := 4) rfl)
  have h5 := hs (.x5, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 5) rfl)
  simp only [VG.Proof.Ed448.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4 h5
  have hos : (VG.Proof.Ed448.AArch64.PublicKey.HS L).Disjoint (VG.Proof.Ed448.AArch64.PublicKey.ST L) := (hL.kc.sub_left (VG.Proof.Ed448.AArch64.PublicKey.hs_stk L)).sub_right (VG.Proof.Ed448.AArch64.PublicKey.st_sub L)
  have hok : (VG.Proof.Ed448.AArch64.PublicKey.HS L).Disjoint (VG.Proof.Ed448.AArch64.PublicKey.KS L) := (hL.kc.sub_left (VG.Proof.Ed448.AArch64.PublicKey.hs_stk L)).sub_right (VG.Proof.Ed448.AArch64.PublicKey.ks_sub L)
  simp only [Proof.Sha3.squeezeAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x5 ∉ linkRegs), h0, h1, h2, h3, h4, h5, hsp,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨trivial, trivial, hos.symm, VG.Proof.Ed448.AArch64.PublicKey.st_ks L, hok, hL.e16, hL.cc.sub_right (VG.Proof.Ed448.AArch64.PublicKey.st_sub L),
    VG.Proof.Ed25519.AArch64.Whole.ck_frame (by decide), hL.cc.sub_right (VG.Proof.Ed448.AArch64.PublicKey.ks_sub L), by decide, by decide⟩

theorem absorb_step (v : Proof.Sha3.AArch64.Permutation) (hc : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : VG.Proof.Ed448.AArch64.PublicKey.Arguments L m₀) (hz : VG.Spec.Sha3.stateAt t.mem L.scr = Spec.Sha3.zero) :
    WP isa (callWith absorbArgs ("vg_keccak_absorb_scratch" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.absorbWith v.callee)) t fun u =>
      VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ u ∧ Spec.Sha3.Repr u.mem L.scr 136 (Spec.Sha3.bytesAt m₀ L.seed 57) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.setup_ok hc hL ha
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
  simp only [VG.Proof.Ed448.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4 h5
  have hpre := VG.Proof.Ed448.AArch64.PublicKey.absorb_pre hL hu.sp (fun p hp => hs p hp)
  have hcov := VG.Proof.Ed448.AArch64.PublicKey.absorb_covers L
  refine call_okF hu (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Nat.le_of_eq v.absorb_depth)
    hpre hcov (VG.Proof.Ed448.AArch64.PublicKey.sponge_writes L) fun w hw _ hp => ⟨hw, ?_⟩
  have hh := hp.1 [] (by
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), h0, hm]
    exact VG.Proof.Ed448.AArch64.PublicKey.repr_nil hz) (by
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

theorem pad_step (v : Proof.Sha3.AArch64.Permutation) (hc : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : VG.Proof.Ed448.AArch64.PublicKey.Arguments L m₀) {msg : List Byte} (hr : Spec.Sha3.Repr t.mem L.scr 136 msg)
    (hl : msg.length = 57) :
    WP isa (callWith VG.Impl.Ed448.AArch64.PublicKey.padArgs ("vg_keccak_pad_scratch" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.padWith v.callee)) t fun u =>
      VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ u ∧ VG.Spec.Sha3.stateAt u.mem L.scr =
        Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 57), (.x3, .const 0x1f),
      (.x4, .caller 2 keccakScratch)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp)
    (by decide)) fun u ⟨hu, hm, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  have h1 := hs (.x1, .const 136) (by simp)
  have h2 := hs (.x2, .const 57) (by simp)
  have h3 := hs (.x3, .const 0x1f) (by simp)
  have h4 := hs (.x4, .caller 2 keccakScratch) (by simp)
  simp only [VG.Proof.Ed448.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4
  have hpre := VG.Proof.Ed448.AArch64.PublicKey.pad_pre hL hu.sp (fun p hp => hs p hp)
  have hcov : Covers ([] ++ [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.KS L]) (L.inputs ++ L.FR :: L.outputs) :=
    VG.Proof.Ed448.AArch64.PublicKey.covers_writes (VG.Proof.Ed448.AArch64.PublicKey.sponge_writes L)
  refine call_okF hu (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Nat.le_of_eq v.pad_depth)
    hpre hcov (VG.Proof.Ed448.AArch64.PublicKey.sponge_writes L) fun w hw _ hp => ⟨hw, ?_⟩
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

theorem squeeze_step (v : Proof.Sha3.AArch64.Permutation) (hc : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : VG.Proof.Ed448.AArch64.PublicKey.Arguments L m₀) :
    WP isa (callWith squeezeArgs ("vg_keccak_squeeze_scratch" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) t fun u =>
      VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ u ∧ Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 hashAt) 114 =
        Spec.Sha3.squeezeFrom 136 (VG.Spec.Sha3.stateAt t.mem L.scr) 0 114 := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.setup_ok hc hL ha
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
  simp only [VG.Proof.Ed448.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4 h5
  have hpre := VG.Proof.Ed448.AArch64.PublicKey.squeeze_pre hL hu.sp (fun p hp => hs p hp)
  have hcov : Covers ([] ++ [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.HS L, VG.Proof.Ed448.AArch64.PublicKey.KS L]) (L.inputs ++ L.FR :: L.outputs) :=
    VG.Proof.Ed448.AArch64.PublicKey.covers_writes (VG.Proof.Ed448.AArch64.PublicKey.squeeze_writes L)
  refine call_okF hu (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Nat.le_of_eq v.squeeze_depth)
    hpre hcov (VG.Proof.Ed448.AArch64.PublicKey.squeeze_writes L) fun w hw _ hp => ⟨hw, ?_⟩
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
  rw [VG.Proof.Ed448.AArch64.PublicKey.squeezeFrom_zero]; rfl

theorem sha3_bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha3.bytesAt m p n).length = n := by
  simp [Spec.Sha3.bytesAt]

/-- `SHAKE256(seed, 114)` in the frame, at `hashAt`. -/
theorem hash_ok (v : Proof.Sha3.AArch64.Permutation) (hc : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : VG.Proof.Ed448.AArch64.PublicKey.Arguments L m₀) :
    WP isa (Impl.Ed448.AArch64.PublicKey.hash v.callee) t fun u => VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ u ∧
      Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 hashAt) 114 =
        Spec.Sha3.shake256 (Spec.Sha3.bytesAt m₀ L.seed 57) 114 := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.zeroArgs_ok hc hL ha) fun t₀ ⟨hc₀, h15⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.zeroStores_ok hc₀ h15) fun t₁ ⟨hc₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.absorb_step v hc₁ hL ha hz₁) fun t₂ ⟨hc₂, hr₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.pad_step v hc₂ hL ha hr₂ (VG.Proof.Ed448.AArch64.PublicKey.sha3_bytesAt_length _ _ _)) fun t₃ ⟨hc₃, hs₃⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.AArch64.PublicKey.squeeze_step v hc₃ hL ha) fun t₄ ⟨hc₄, hb₄⟩ => ⟨hc₄, ?_⟩
  rw [hb₄, hs₃, VG.Proof.Ed448.AArch64.PublicKey.shake256_eq]

end VG.Proof.Ed448.AArch64.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Base`. -/
section

/-!
# Ed448 public-key derivation on AArch64: pruning and the base point

The first 57 bytes of the hash, pruned, are stored as the scalar at the
bottom of the frame (`prune_ok`), `[s]B` is encoded into `out` by
`vg_ed448_scalar_base` (`base_step`, given that it meets its contract, `BaseOk`), and the scalar and
the hash in the frame are cleared (`wipe_step`).
-/

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (setup callWith Value zeroWord)
open VG.Proof.Ed25519.AArch64.Whole (call_ok Within)
open VG.Proof.Ed448.AArch64.Whole (prune_run)

/-! ## In the frame's body -/

variable {L : VG.Proof.Ed448.AArch64.PublicKey.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem prune_step (hc : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ t) {h : List Byte}
    (hh : Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114 = h) :
    WP isa (.block VG.Impl.Ed448.AArch64.PublicKey.prune) t fun u => VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ u ∧
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

theorem base_pre (hL : L.Ok) {u : State} (hs : ∀ p ∈ VG.Proof.Ed448.AArch64.PublicKey.baseValues, u.gpr p.1 = VG.Proof.Ed448.AArch64.PublicKey.argValue L p.2) :
    Proof.Ed448.AArch64.scalarBaseLocal.pre (u.callEntry.withRegions [⟨L.E, 57⟩] L.outputs) := by
  have h0 := hs (.x0, .caller 0 0) (List.mem_of_getElem? (i := 0) rfl)
  have h1 := hs (.x1, .frame 0) (List.mem_of_getElem? (i := 1) rfl)
  have h2 := hs (.x2, .caller 2 0) (List.mem_of_getElem? (i := 2) rfl)
  simp only [VG.Proof.Ed448.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  simp only [Proof.Ed448.AArch64.scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2]
  exact ⟨trivial, rfl, hL.oc, hL.kc.sub_left (Region.sub_prefix (by decide)), hL.nc⟩

theorem base_covers (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : Covers ([⟨L.E, 57⟩] ++ L.outputs) (L.inputs ++ L.FR :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, 0, (BitVec.add_zero _).symm,
      by change 0 + 57 ≤ 256; decide⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_writes (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) : ∀ r ∈ L.outputs, Within r L.FR ∨ ∃ R ∈ L.outputs, Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_step (hb : Proof.Ed448.AArch64.BaseOk) (hc : Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : Arguments L m₀) {n : Nat}
    (hs : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t.mem L.E 57) = n) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) t fun u =>
      VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ u ∧ Spec.Ed448.bytesAt u.mem L.out 57 =
        Spec.Ed448.encodePoint (Spec.Ed448.pointMul n Spec.Ed448.basePoint) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.setup_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 0), (.x2, .caller 2 0)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp) (by decide))
    fun u ⟨hu, hm, hav⟩ => ?_)
  have h0 := hav (.x0, .caller 0 0) (by simp)
  have h1 := hav (.x1, .frame 0) (by simp)
  have h2 := hav (.x2, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have hpre := base_pre hL (u := u) (fun p hp => hav p hp)
  refine call_ok hu hb.ok base_noFrames hpre (base_covers L)
    (base_writes L) fun w hw _ hp => ⟨hw, ?_⟩
  change Spec.Ed448.bytesAt w.mem (u.callEntry.gpr .x0) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1, hm] at hp
  rw [hp, Spec.Ed448.scalarBase, hs]

theorem wipe_step (hc : VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => VG.Proof.Ed448.AArch64.PublicKey.Ctx L g vec m₀ u ∧
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

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Main`. -/
section

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

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey

/-- `vg_ed448_public_key(out = x0, seed = x1, scratch = x2)`, with 352 bytes of stack. -/
def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 57⟩
    let seed : Region := ⟨s.gpr .x1, 57⟩
    let scr : Region := ⟨s.gpr .x2, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [seed] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 57 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat
  post s t := Spec.Ed448.bytesAt t.mem (s.gpr .x0) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

/-- The layout of a call from `s`. -/
def lay (s : State) : VG.Proof.Ed448.AArch64.PublicKey.Lay := ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, VG.Proof.Ed25519.AArch64.Whole.base s⟩

theorem lay_ok {s : State} (h : pkLocal.pre s) : (VG.Proof.Ed448.AArch64.PublicKey.lay s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hsp⟩ := h
  exact ⟨os, oc, sc, ko.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s),
    ks.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s),
    kc.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s), no, ns, nc,
    VG.Proof.Ed25519.AArch64.Whole.base_16 hsp, ko.sub_left (VG.Proof.Ed25519.AArch64.Whole.ck_sub s),
    ks.sub_left (VG.Proof.Ed25519.AArch64.Whole.ck_sub s), kc.sub_left (VG.Proof.Ed25519.AArch64.Whole.ck_sub s)⟩

theorem entry_below {s : State} (h : pkLocal.pre s) : 352 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2

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
    VG.Proof.Ed448.AArch64.PublicKey.Ctx (VG.Proof.Ed448.AArch64.PublicKey.lay s) s.gpr s.v p.mem (p.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd s)
      (VG.Proof.Ed25519.AArch64.Whole.bodyWr s)) := by
  have hc := VG.Proof.Ed25519.AArch64.Whole.saved_ctx hp
  simpa only [VG.Proof.Ed25519.AArch64.Whole.bodyRd, h.1, VG.Proof.Ed25519.AArch64.Whole.bodyWr, h.2.1,
    VG.Proof.Ed448.AArch64.PublicKey.Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, VG.Proof.Ed448.AArch64.PublicKey.lay, List.cons_append,
    List.nil_append] using hc

theorem entry_args {s p : State}
    (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p) :
    VG.Proof.Ed448.AArch64.PublicKey.Arguments (VG.Proof.Ed448.AArch64.PublicKey.lay s) p.mem := by
  intro j hj
  have hw := VG.Proof.Ed25519.AArch64.Whole.saved_words hp (j := j) (by omega)
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases he with rfl | rfl | rfl <;> exact hw

variable {L : VG.Proof.Ed448.AArch64.PublicKey.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem body_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk)
    (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (body v.callee) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed448.bytesAt u.mem L.out 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.hash_ok v hc hL ha) fun u ⟨hu, hh⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.prune_step hu hh) fun u' ⟨hu', hs⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.PublicKey.base_step hb hu' hL ha hs) fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (VG.Proof.Ed448.AArch64.PublicKey.wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

theorem body_depth (v : Proof.Sha3.AArch64.Permutation) : (VG.Impl.Ed448.AArch64.PublicKey.body v.callee).aarch64Depth ≤ 1 := by
  have ha := v.absorb_depth
  have hp := v.pad_depth
  have hs := v.squeeze_depth
  have hb := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.PublicKey.base_noFrames
  simp only [VG.Impl.Ed448.AArch64.PublicKey.body, Impl.Ed448.AArch64.PublicKey.hash, Impl.Ed25519.AArch64.Whole.callWith, Code.aarch64Depth, Nat.max_le, hb, ha, hp, hs]
  omega

theorem publicKey_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) {s : State}
    (h : pkLocal.pre s) :
    WP isa (publicKeyWith v.callee) s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := VG.Proof.Ed25519.AArch64.Whole.wrap_ok (VG.Proof.Ed448.AArch64.PublicKey.body_depth v) (VG.Proof.Ed448.AArch64.PublicKey.entry_below h) (VG.Proof.Ed448.AArch64.PublicKey.entry_writes h)
    (P := fun m m' _ => Spec.Ed448.bytesAt m' (s.gpr .x0) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m (s.gpr .x1) 57))
    (fun p hp => WP.mono (VG.Proof.Ed448.AArch64.PublicKey.body_ok v hb (VG.Proof.Ed448.AArch64.PublicKey.entry_ctx h hp) (VG.Proof.Ed448.AArch64.PublicKey.lay_ok h) (VG.Proof.Ed448.AArch64.PublicKey.entry_args hp)) fun u ⟨hu, ho⟩ => ⟨by
      simpa only [VG.Proof.Ed25519.AArch64.Whole.bodyRd, h.1, VG.Proof.Ed448.AArch64.PublicKey.Ctx, Lay.inputs, Lay.outputs, Lay.SEED,
        Lay.OUT, Lay.SCR, Lay.ARGS, VG.Proof.Ed448.AArch64.PublicKey.lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed448.bytesAt m (s.gpr .x1) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨s.gpr .x1, 57⟩) ?_
      (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (VG.Proof.Ed448.AArch64.PublicKey.lay_ok h).ks.symm
  change Spec.Ed448.bytesAt u.mem (s.gpr .x0) 57 = _
  rw [hp, hs]

end VG.Proof.Ed448.AArch64.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Verified`. -/
section

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

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (Value setup callWith)
open VG.Impl.Ed448.AArch64.Whole (zeroStores)

abbrev Two (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) (g₁ g₂ : Reg → Addr) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) := (VG.Proof.Ed448.AArch64.PublicKey.Ctx L g₁ v₁ m₁ a ∧ P a) ∧ (VG.Proof.Ed448.AArch64.PublicKey.Ctx L g₂ v₂ m₂ b ∧ P b)

/-- The registers hold what `setup args` moves into them. -/
def Slots (L : VG.Proof.Ed448.AArch64.PublicKey.Lay) (args : List (Reg × Value)) (s : State) := ∀ p ∈ args, s.gpr p.1 = VG.Proof.Ed448.AArch64.PublicKey.argValue L p.2

variable {L : VG.Proof.Ed448.AArch64.PublicKey.Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : VG.Proof.Ed448.AArch64.PublicKey.Arguments L m₁) (hb : VG.Proof.Ed448.AArch64.PublicKey.Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed448.AArch64.PublicKey.Slots L args)) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) ht) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed448.AArch64.PublicKey.setup_ok hc hL ha hn hv hi hr) fun _ ⟨hc, _, hs⟩ => ⟨hc, hs⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed448.AArch64.PublicKey.setup_ok hc hL hb hn hv hi hr) fun _ ⟨hc, _, hs⟩ => ⟨hc, hs⟩

theorem call_ct {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → VG.Proof.Ed448.AArch64.PublicKey.Slots L args t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed448.AArch64.PublicKey.Slots L args)) (.call name c)
      (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp ?_ ?_ ?_
  · refine VG.Proof.Ed25519.AArch64.Whole.callEx correct ct fun a b h => ?_
    let ra := ready a h.1.1.sp h.1.2
    let rb := ready b h.2.1.sp h.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (h.1.1.sp.trans h.2.1.sp.symm) ?_, ca, wa, cb, wb⟩
    intro p hp
    rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2 p hp, h.2.2 p hp]
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wpF hc correct hd) fun _ hu => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wpF hc correct hd) fun _ hu => ⟨hu, trivial⟩

/-- A call's arguments, then the call. -/
theorem callWith_ct (hL : L.Ok) (ha : VG.Proof.Ed448.AArch64.PublicKey.Arguments L m₁) (hb : VG.Proof.Ed448.AArch64.PublicKey.Arguments L m₂)
    {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true)
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → VG.Proof.Ed448.AArch64.PublicKey.Slots L args t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (callWith (setup args) name c)
      (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (VG.Proof.Ed448.AArch64.PublicKey.setup_ct hL ha hb args hn hv hi hr ht).seq (VG.Proof.Ed448.AArch64.PublicKey.call_ct correct ct hd ready kp hl)

/-! ## Each block and call -/

def zeroValues : List (Reg × Value) := [(.x15, .caller 2 0)]

theorem zeroStores_ct : RelCT isa (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed448.AArch64.PublicKey.Slots L VG.Proof.Ed448.AArch64.PublicKey.zeroValues)) (.block zeroStores)
    (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have h15 : ∀ {t : State}, VG.Proof.Ed448.AArch64.PublicKey.Slots L VG.Proof.Ed448.AArch64.PublicKey.zeroValues t → t.gpr .x15 = L.scr := fun hs => by
    have h := hs (.x15, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl)
    simp only [VG.Proof.Ed448.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h
    exact h
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (RelCT.taint (A := taint) (Taint.ofRegs [.x15]) (fun a b h => ⟨h.1.1.sp.trans h.2.1.sp.symm,
      fun r hr => ?_⟩) (by taint_decide)) ?_ ?_
  · simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr
    rw [h15 h.1.2, h15 h.2.2]
  · intro t ⟨hc, hs⟩
    exact WP.mono (VG.Proof.Ed448.AArch64.PublicKey.zeroStores_ok hc (h15 hs)) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono (VG.Proof.Ed448.AArch64.PublicKey.zeroStores_ok hc (h15 hs)) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem prune_ct : RelCT isa (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block VG.Impl.Ed448.AArch64.PublicKey.prune)
    (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
      (by taint_decide)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed448.AArch64.PublicKey.prune_step hc (h := Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed448.AArch64.PublicKey.prune_step hc (h := Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
    (VG.Proof.Ed448.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
      (by taint_decide)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (VG.Proof.Ed448.AArch64.PublicKey.wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (VG.Proof.Ed448.AArch64.PublicKey.wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

def absorb_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : VG.Proof.Ed448.AArch64.PublicKey.Slots L VG.Proof.Ed448.AArch64.PublicKey.absorbValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.absorbAArch64 L.E L.inputs L.outputs t :=
  ⟨[L.SEED], [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.KS L], VG.Proof.Ed448.AArch64.PublicKey.absorb_pre hL hsp hs, VG.Proof.Ed448.AArch64.PublicKey.absorb_covers L, VG.Proof.Ed448.AArch64.PublicKey.sponge_writes L⟩

def pad_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : VG.Proof.Ed448.AArch64.PublicKey.Slots L VG.Proof.Ed448.AArch64.PublicKey.padValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.padAArch64 L.E L.inputs L.outputs t :=
  ⟨[], [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.KS L], VG.Proof.Ed448.AArch64.PublicKey.pad_pre hL hsp hs, VG.Proof.Ed448.AArch64.PublicKey.covers_writes (VG.Proof.Ed448.AArch64.PublicKey.sponge_writes L), VG.Proof.Ed448.AArch64.PublicKey.sponge_writes L⟩

def squeeze_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : VG.Proof.Ed448.AArch64.PublicKey.Slots L VG.Proof.Ed448.AArch64.PublicKey.squeezeValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.squeezeAArch64 L.E L.inputs L.outputs t :=
  ⟨[], [VG.Proof.Ed448.AArch64.PublicKey.ST L, VG.Proof.Ed448.AArch64.PublicKey.HS L, VG.Proof.Ed448.AArch64.PublicKey.KS L], VG.Proof.Ed448.AArch64.PublicKey.squeeze_pre hL hsp hs, VG.Proof.Ed448.AArch64.PublicKey.covers_writes (VG.Proof.Ed448.AArch64.PublicKey.squeeze_writes L), VG.Proof.Ed448.AArch64.PublicKey.squeeze_writes L⟩

def base_ready (hL : L.Ok) {t : State} (hs : VG.Proof.Ed448.AArch64.PublicKey.Slots L VG.Proof.Ed448.AArch64.PublicKey.baseValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Ed448.AArch64.scalarBaseLocal L.E L.inputs L.outputs t :=
  ⟨[⟨L.E, 57⟩], L.outputs, VG.Proof.Ed448.AArch64.PublicKey.base_pre hL hs, VG.Proof.Ed448.AArch64.PublicKey.base_covers L, VG.Proof.Ed448.AArch64.PublicKey.base_writes L⟩

theorem body_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) (hL : L.Ok)
    (ha : Arguments L m₁) (hb' : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body v.callee)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have z := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb' zeroValues
    (by decide) (by simp [zeroValues, VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp [zeroValues])
    (by decide) (by taint_decide)
  have a := VG.Proof.Ed448.AArch64.PublicKey.callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_keccak_absorb_scratch" ++ v.callee.suffix)
    hL ha hb' (args := VG.Proof.Ed448.AArch64.PublicKey.absorbValues) (by decide)
    (by simp [VG.Proof.Ed448.AArch64.PublicKey.absorbValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp [VG.Proof.Ed448.AArch64.PublicKey.absorbValues])
    (by decide) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v)
    (Nat.le_of_eq v.absorb_depth) (fun _ hsp hs => VG.Proof.Ed448.AArch64.PublicKey.absorb_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp hg => ⟨hg (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .const 0) (List.mem_of_getElem? (i := 2) rfl),
      hg (.x3, .caller 1 0) (List.mem_of_getElem? (i := 3) rfl), hg (.x4, .const 57) (List.mem_of_getElem? (i := 4) rfl),
      hg (.x5, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 5) rfl), hsp⟩)
    (by decide)
  have p := VG.Proof.Ed448.AArch64.PublicKey.callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_keccak_pad_scratch" ++ v.callee.suffix)
    hL ha hb' (args := VG.Proof.Ed448.AArch64.PublicKey.padValues) (by decide)
    (by simp [VG.Proof.Ed448.AArch64.PublicKey.padValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp [VG.Proof.Ed448.AArch64.PublicKey.padValues])
    (by decide) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    (Nat.le_of_eq v.pad_depth) (fun _ hsp hs => VG.Proof.Ed448.AArch64.PublicKey.pad_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp hg => ⟨hg (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .const 57) (List.mem_of_getElem? (i := 2) rfl),
      hg (.x4, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 4) rfl), hsp⟩)
    (by decide)
  have q := VG.Proof.Ed448.AArch64.PublicKey.callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂)
    (name := "vg_keccak_squeeze_scratch" ++ v.callee.suffix)
    hL ha hb' (args := VG.Proof.Ed448.AArch64.PublicKey.squeezeValues) (by decide)
    (by simp [VG.Proof.Ed448.AArch64.PublicKey.squeezeValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch, hashAt])
    (by simp [VG.Proof.Ed448.AArch64.PublicKey.squeezeValues]) (by decide) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v)
    (Nat.le_of_eq v.squeeze_depth) (fun _ hsp hs => VG.Proof.Ed448.AArch64.PublicKey.squeeze_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp hg => ⟨hg (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .const 0) (List.mem_of_getElem? (i := 2) rfl),
      hg (.x3, .frame hashAt) (List.mem_of_getElem? (i := 3) rfl), hg (.x4, .const 114) (List.mem_of_getElem? (i := 4) rfl),
      hg (.x5, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 5) rfl), hsp⟩)
    (by decide)
  have b := VG.Proof.Ed448.AArch64.PublicKey.callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_ed448_scalar_base")
    hL ha hb' (args := VG.Proof.Ed448.AArch64.PublicKey.baseValues) (by decide)
    (by simp [VG.Proof.Ed448.AArch64.PublicKey.baseValues, VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp [VG.Proof.Ed448.AArch64.PublicKey.baseValues])
    (by decide) (by taint_decide)
    hb.ok hb.ct
    (VG.Proof.Ed25519.AArch64.Whole.depth_of_noFrames base_noFrames) (fun _ _ hs => base_ready hL hs)
    (fun _ _ _ _ _ _ hsp hg => ⟨hsp, hg (.x0, .caller 0 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .frame 0) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .caller 2 0) (List.mem_of_getElem? (i := 2) rfl)⟩)
    (by decide)
  exact (z.seq (zeroStores_ct.seq (a.seq (p.seq q)))).seq (prune_ct.seq (b.seq (VG.Proof.Ed448.AArch64.PublicKey.wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : VG.Proof.Ed448.AArch64.PublicKey.lay s = VG.Proof.Ed448.AArch64.PublicKey.lay t := by
  obtain ⟨sp, h0, h1, h2⟩ := hp
  simp only [VG.Proof.Ed448.AArch64.PublicKey.lay, VG.Proof.Ed25519.AArch64.Whole.base, sp, h0, h1, h2]

theorem publicKey_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) :
    ConstantTime isa pkLocal.pre pkLocal.pub (publicKeyWith v.callee) := by
  refine VG.Proof.Ed25519.AArch64.Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (VG.Proof.Ed448.AArch64.PublicKey.body_ok v hb (VG.Proof.Ed448.AArch64.PublicKey.entry_ctx hs hp) (VG.Proof.Ed448.AArch64.PublicKey.lay_ok hs) (VG.Proof.Ed448.AArch64.PublicKey.entry_args hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := VG.Proof.Ed448.AArch64.PublicKey.lay_eq hp
    have hq : VG.Proof.Ed448.AArch64.PublicKey.Ctx (VG.Proof.Ed448.AArch64.PublicKey.lay s) t.gpr t.v q.mem (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)) :=
      he ▸ VG.Proof.Ed448.AArch64.PublicKey.entry_ctx ht hqb
    have hqa : VG.Proof.Ed448.AArch64.PublicKey.Arguments (VG.Proof.Ed448.AArch64.PublicKey.lay s) q.mem := he ▸ VG.Proof.Ed448.AArch64.PublicKey.entry_args hqb
    exact ⟨(VG.Proof.Ed448.AArch64.PublicKey.body_ct v hb (VG.Proof.Ed448.AArch64.PublicKey.lay_ok hs) (VG.Proof.Ed448.AArch64.PublicKey.entry_args hpa) hqa _ _ _ _ _ _
      ⟨⟨VG.Proof.Ed448.AArch64.PublicKey.entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩]

theorem pk_implies : pkLocal.Implies (Spec.Ed448.publicKeyContract AArch64.abi 352) := by
  sig_implies [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
    Spec.Ed448.scratchWords, VG.Proof.Ed448.AArch64.PublicKey.pkLocal, below, AArch64.abi, AArch64.argRegs]
    [satState] using VG.Proof.Ed448.AArch64.PublicKey.satState

theorem publicKey_verified (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) :
    Verified AArch64.target (publicKeyWith v.callee) (Spec.Ed448.publicKeyContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => VG.Proof.Ed448.AArch64.PublicKey.publicKey_ok v hb h) (VG.Proof.Ed448.AArch64.PublicKey.publicKey_ct v hb) (.refl pk_implies.sat_left))
    VG.Proof.Ed448.AArch64.PublicKey.pk_implies

end VG.Proof.Ed448.AArch64.PublicKey

end
