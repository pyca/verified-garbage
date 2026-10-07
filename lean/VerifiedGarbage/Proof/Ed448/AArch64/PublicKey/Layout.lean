import VerifiedGarbage.Impl.Ed448.AArch64.PublicKey
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx

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
  refine hc.frame.readW (r := L.TB) (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)
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
    (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)) ?_ (by decide)
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
