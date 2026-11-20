module

public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Impl.Ed25519.AArch64.KeyPair
public import VerifiedGarbage.Proof.Sha512.AArch64.OneShot
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core
public import VerifiedGarbage.Proof.Ed25519.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.Sha512.PostOut
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
meta import VerifiedGarbage.Spec.Ed25519.KeyPair
meta import VerifiedGarbage.Impl.Ed25519.AArch64.KeyPair
meta import VerifiedGarbage.Proof.Sha512.AArch64.OneShot
meta import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
meta import VerifiedGarbage.Proof.Sha512.PostOut
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
public import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Prune
public import VerifiedGarbage.Proof.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Prune
meta import VerifiedGarbage.Proof.Ed25519.Contract
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.AArch64.Ladder
public import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
import VerifiedGarbage.Proof.Framework.OffsetBelow
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Attr.Core
meta import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import Mathlib.Tactic.NormNum.Prime
meta import Mathlib.Data.Nat.Totient
meta import Mathlib.Tactic.Positivity.Finset
meta import Mathlib.Algebra.Order.Field.Basic
meta import Mathlib.Tactic.NormNum.GCD
meta import Mathlib.Data.Sym.Sym2.Init
meta import Mathlib.Tactic.ContinuousFunctionalCalculus
meta import Mathlib.Tactic.Attr.Core

/-! ### `Ed25519.AArch64.PublicKey.Expanded`, which only this module used -/

section

/-! ### `Ed25519.AArch64.PublicKey.Verified`, which only this module used -/

section

/-! ### `Ed25519.AArch64.PublicKey.CTCommon`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Layout`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

structure Lay where
  out : Addr
  seed : Addr
  scr : Addr
  E : Addr
  /-- The comb's tables (the static `combSym`), which `vg_ed25519_scalar_base` reads. -/
  T : Addr
  /-- The bytes read at `seed`: the seed (32), or its cached SHA-512 digest (64). -/
  seedLen : Nat

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨L.out, 32⟩
abbrev SEED : Region := ⟨L.seed, L.seedLen⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := ⟨L.E, 336⟩
/-- The frame of a callee, below the locals. -/
abbrev CK : Region := Whole.CK L.E
abbrev TB : Region := TBL L.T
def inputs : List Region := [L.SEED, L.TB, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : Addr := match j with | 0 => L.out | 1 => L.seed | _ => L.scr
structure Ok : Prop where
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 32 ≤ 2 ^ 64
  ns : L.seed.toNat + L.seedLen ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  e16 : 16 ≤ L.E.toNat
  co : L.CK.Disjoint L.OUT
  cs : L.CK.Disjoint L.SEED
  cc : L.CK.Disjoint L.SCR
  tbo : L.TB.Disjoint L.OUT
  tbc : L.TB.Disjoint L.SCR
  tbk : L.TB.Disjoint L.STK
  tbck : L.TB.Disjoint L.CK
  tbfit : L.T.toNat + 8 * Impl.Ed25519.AArch64.combWords.length ≤ 2 ^ 64
end Lay

abbrev Ctx (L : Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g vec m₀ L.inputs L.outputs t

/-- The saved arguments, and the comb's words. -/
def Arguments (L : Lay) (m : Mem) : Prop :=
  (∀ j < 3, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j) ∧ TblWords L.T m

def argValue (L : Lay) : Value → Addr
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem frame_sub (L : Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 256 ≤ 336)
theorem args_sub (L : Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

/-- The comb's words, as on entry: no write reaches them. -/
theorem Ctx.tbl (hc : Ctx L g vec m₀ t) (hL : L.Ok) (hm : TblWords L.T m₀) : TblWords L.T t.mem :=
  fun i hi => by
    have := hL.tbfit
    rw [← hm i hi]
    refine hc.frame.readW (r := L.TB) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, this])) ?_ (by decide)
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hL.tbo
    · exact hL.tbc
    · exact hL.tbk.sub_right (frame_sub L)
    · exact hL.tbck

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

theorem setup_ok (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2)
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
    simp only [Whole.value, argValue]
    change t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL hj, ha.1 j hj]

end VG.Proof.Ed25519.AArch64.PublicKey
end

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Base`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (callWith)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem base_noFrames : Impl.Ed25519.AArch64.scalarBase.noFrames = true := by lit_decide

def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = L.out ∧ t.gpr .x1 = L.E + 32 ∧ t.gpr .x2 = L.scr

theorem base_pre (hL : L.Ok) (ha : BaseArgs L t) (hsy : t.syms Impl.Ed25519.AArch64.combSym = L.T)
    (hm : TblWords L.T t.mem) :
    scalarBaseLocal.pre (t.callEntry.withRegions [⟨L.E + 32, 32⟩, L.TB] L.outputs) := by
  obtain ⟨h0, h1, h2⟩ := ha
  have hT : (t.callEntry.withRegions [⟨L.E + 32, 32⟩, L.TB] L.outputs).syms
      Impl.Ed25519.AArch64.combSym = L.T := hsy
  have hC : CombHeld (t.callEntry.withRegions [⟨L.E + 32, 32⟩, L.TB] L.outputs) [⟨L.out, 32⟩, ⟨L.scr, 8192⟩] := by
    refine ⟨fun i hi => ?_, ?_, fun r hr => ?_⟩
    · rw [hT]; exact hm i hi
    · rw [hT]; exact hL.tbfit
    · rw [hT]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hL.tbo, hL.tbc]
  simp only [scalarBaseLocal, tblRegion, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2, hT]
  exact ⟨trivial, rfl, hL.kc.sub_left (Offset.sub_base _ (by decide : 32 + 32 ≤ 336)), hL.nc, hC⟩

theorem base_covers (L : Lay) : Covers ([⟨L.E + 32, 32⟩, L.TB] ++ L.outputs)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Whole.FR L.E, List.mem_append_right _ List.mem_cons_self, 32, rfl, by change 32 + 32 ≤ 256; decide⟩
    · exact ⟨L.TB, List.mem_append_left _ (by simp [Lay.inputs]), 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

theorem base_writes (L : Lay) : ∀ r ∈ L.outputs,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_call [VG.Proof.Ed25519.AArch64.Divstep.Sound] (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : BaseArgs L t)
    (hsy : t.syms Impl.Ed25519.AArch64.combSym = L.T) (hm : TblWords L.T t.mem) :
    WP isa (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem L.out 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (L.E + 32) 32) := by
  refine Whole.call_ok hc scalarBase_ok base_noFrames (base_pre hL ha hsy hm) (base_covers L)
    (base_writes L) fun u hu _ hp => ⟨hu, ?_⟩
  change Spec.Ed25519.bytesAt u.mem (t.callEntry.gpr .x0) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (t.callEntry.gpr .x1) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] at hp
  exact hp

theorem prune_step (hc : Ctx L g vec m₀ t) {digest : List Byte}
    (hh : Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = digest) :
    WP isa (.block prune) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (L.E + 32) 32) = Spec.Ed25519.prune digest := by
  have hwrite : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  have hash : Spec.Sha512.bytesAt t.mem (t.sp + 192) 64 = digest := by rw [hc.sp]; exact hh
  refine WP.mono (prune_ok hwrite hash) fun u ⟨hu, hf, hp⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame hu.rd hu.wr hu.sp ?_ ?_ hf ?_
    · intro r hr _
      apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
    · intro r _; rw [hu.v]
    · rintro r hr
      rw [List.mem_singleton.mp hr, hc.sp]
      exact .inl (Offset.sub_base _ (by decide : 32 + 32 ≤ 256))
  · rw [hc.sp] at hp
    exact hp

theorem base_step [VG.Proof.Ed25519.AArch64.Divstep.Sound] (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) {n : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (L.E + 32) 32) = n)
    (hsy : t.syms Impl.Ed25519.AArch64.combSym = L.T) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem L.out 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono_syms (setup_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 32), (.x2, .caller 2 0)])
    (by decide) (by decide) (by simp) (by decide)) fun u ⟨hu, hm, hav⟩ sy => ?_)
  have h0 := hav (.x0, .caller 0 0) (by simp)
  have h1 := hav (.x1, .frame 32) (by simp)
  have h2 := hav (.x2, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  refine WP.mono (base_call hu hL ⟨h0, h1, h2⟩ (by rw [sy]; exact hsy) (hu.tbl hL ha.2))
    fun u' ⟨hu', hp⟩ => ⟨hu', ?_⟩
  rw [hp, hm, Spec.Ed25519.scalarBase, hs]

theorem wipe_step (hc : Ctx L g vec m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem L.out 32 = Spec.Ed25519.bytesAt t.mem L.out 32 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 4) (count := 28) (by decide)) fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 4 + 8 * 28 ≤ 336))).symm

end VG.Proof.Ed25519.AArch64.PublicKey
end

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Correct`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Entry`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64

/-- The public key from `n` bytes read at the seed pointer (the seed, or its cached digest),
with the postcondition `post`. -/
def pkLocalWith (n : Nat) (post : State → State → Prop) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 32⟩
    let seed : Region := ⟨s.gpr .x1, n⟩
    let scr : Region := ⟨s.gpr .x2, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [seed, TBL (s.syms Impl.Ed25519.AArch64.combSym)] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + n ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat ∧ CombHeld s [out, scr, stk]
  post := post
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.syms Impl.Ed25519.AArch64.combSym = t.syms Impl.Ed25519.AArch64.combSym

def lay (n : Nat) (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, Whole.base s, s.syms Impl.Ed25519.AArch64.combSym, n⟩

variable {n : Nat} {post : State → State → Prop}

theorem lay_ok {s : State} (h : (pkLocalWith n post).pre s) : (lay n s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hsp, -, fit, dj⟩ := h
  have dk := dj (below s.sp 352) (by simp)
  exact ⟨os, oc, sc, ko.sub_left (Whole.stk_sub s), ks.sub_left (Whole.stk_sub s),
    kc.sub_left (Whole.stk_sub s), no, ns, nc, Whole.base_16 hsp, ko.sub_left (Whole.ck_sub s),
    ks.sub_left (Whole.ck_sub s), kc.sub_left (Whole.ck_sub s),
    dj ⟨s.gpr .x0, 32⟩ (by simp), dj ⟨s.gpr .x2, 8192⟩ (by simp),
    dk.sub_right (Whole.stk_sub s), dk.sub_right (Whole.ck_sub s), fit⟩

theorem entry_below {s : State} (h : (pkLocalWith n post).pre s) : 352 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.1

theorem entry_writes {s : State} (h : (pkLocalWith n post).pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1

theorem entry_ctx {s p : State} (h : (pkLocalWith n post).pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay n s) s.gpr s.v p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, Lay.TB, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (h : (pkLocalWith n post).pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Arguments (lay n s) p.mem := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have hw := Whole.saved_words hp (j := j) (by omega_using [hj])
    have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
    rcases he with rfl | rfl | rfl <;> exact hw
  · obtain ⟨held, fit, dj⟩ := h.2.2.2.2.2.2.2.2.2.2.2.2
    have hf := Whole.saved_frame hp
    rw [← held i hi]
    refine hf.readW (r := TBL (s.syms Impl.Ed25519.AArch64.combSym))
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, fit])) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton.mp hr]
    exact (dj (below s.sp 352) (by simp)).sub_right (Whole.stk_sub s)

theorem entry_syms {s p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)).syms Impl.Ed25519.AArch64.combSym = (lay n s).T :=
  congrFun hp.step.syms Impl.Ed25519.AArch64.combSym

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- The public key after a first step `first` that leaves a digest `D` at `frame 192`: the
public key of every seed whose digest `D` is. -/
theorem bodyFrom_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] {first : Prog isa} {D : List Byte}
    (hfirst : WP isa first t fun u => Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem (L.E + 192) 64 = D)
    (hL : L.Ok) (ha : Arguments L m₀) (hsy : t.syms Impl.Ed25519.AArch64.combSym = L.T) :
    WP isa (bodyFrom first) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem L.out 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul (Spec.Ed25519.prune D) Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono_syms hfirst fun u ⟨hu, hh⟩ su => ?_)
  refine WP.seq (WP.mono_syms (prune_step hu hh) fun u' ⟨hu', hs⟩ su' => ?_)
  refine WP.seq (WP.mono (base_step hu' hL ha hs (by rw [su', su]; exact hsy)) fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

abbrev Two (L : Lay) (g₁ g₂ : Reg → Addr) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) :=
  (Ctx L g₁ v₁ m₁ a ∧ a.syms Impl.Ed25519.AArch64.combSym = L.T ∧ P a) ∧
    (Ctx L g₂ v₂ m₂ b ∧ b.syms Impl.Ed25519.AArch64.combSym = L.T ∧ P b)

def Slots (L : Lay) (args : List (Reg × Value)) (s : State) := ∀ p ∈ args, s.gpr p.1 = argValue L p.2

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L args)) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) ht) ?_ ?_
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (setup_ok hc hL ha hn hv hi hr) fun _ ⟨hc, _, hs⟩ sy => ⟨hc, sy ▸ hy, hs⟩
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (setup_ok hc hL hb hn hv hi hr) fun _ ⟨hc, _, hs⟩ sy => ⟨hc, sy ▸ hy, hs⟩

theorem call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → t.syms Impl.Ed25519.AArch64.combSym = L.T → TblWords L.T t.mem →
      Slots L args t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      a.syms Impl.Ed25519.AArch64.combSym = b.syms Impl.Ed25519.AArch64.combSym →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L args)) (.call name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ?_ ?_ ?_
  · refine Whole.callEx correct ct fun a b h => ?_
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

end VG.Proof.Ed25519.AArch64.PublicKey

end

end

/-! # Constant time of the public key's derivation after its first step (AArch64) -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.AArch64.PublicKey.CTReady`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def baseValues : List (Reg × Value) := [(.x0, .caller 0 0), (.x1, .frame 32), (.x2, .caller 2 0)]

variable {L : Lay} {t : State}

def base_ready (hL : L.Ok) (hsy : t.syms Impl.Ed25519.AArch64.combSym = L.T) (hm : TblWords L.T t.mem)
    (hs : Slots L baseValues t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 0 0) (by decide)
  have h1 := hs (.x1, .frame 32) (by decide)
  have h2 := hs (.x2, .caller 2 0) (by decide)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨L.E + 32, 32⟩, L.TB], L.outputs, base_pre hL ⟨h0, h1, h2⟩ hsy hm, base_covers L, base_writes L⟩

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem base_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L baseValues))
    (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb scalarBase_ok scalarBase_ct (Whole.depth_of_noFrames base_noFrames)
    (fun _ _ hy hm h => base_ready hL hy hm h)
  · intro a b ar aw br bw hsp hy hg
    exact ⟨hsp, hg (.x0, .caller 0 0) (by decide), hg (.x1, .frame 32) (by decide),
      hg (.x2, .caller 2 0) (by decide), hy⟩
  · simp [baseValues, linkRegs]

theorem prune_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block prune)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide)) ?_ ?_
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (prune_step hc (digest := Spec.Ed25519.bytesAt t.mem (L.E + 192) 64) rfl)
      fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (prune_step hc (digest := Spec.Ed25519.bytesAt t.mem (L.E + 192) 64) rfl)
      fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide)) ?_ ?_
  · intro t ⟨hc, hy, _⟩; exact WP.mono_syms (wipe_step hc hL) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, _⟩; exact WP.mono_syms (wipe_step hc hL) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

/-- The public key after a first step related to itself, as the copy of a cached digest is. -/
theorem bodyFrom_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] {first : Prog isa}
    (hfirst : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) first
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True))
    (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (bodyFrom first)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have b := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb baseValues
    (by decide) (by simp [baseValues, Whole.valid]) (by simp [baseValues])
    (by decide) (by taint_decide)
  exact hfirst.seq (prune_ct.seq ((b.seq (base_ct hL ha hb)).seq (wipe_ct hL)))

theorem lay_eq {n : Nat} {post : State → State → Prop} {s t : State}
    (hp : (pkLocalWith n post).pub s t) : lay n s = lay n t := by
  obtain ⟨sp, h0, h1, h2, hsy⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, hsy]

end VG.Proof.Ed25519.AArch64.PublicKey
end

end

end

/-! # Ed25519 public-key derivation from the seed's cached SHA-512 digest (AArch64)

`codeExpanded` is `bodyFrom copyExpanded`: the digest at the second argument is copied to
`frame 192`, where `bodyFrom` reads it. The rest is proven by `bodyFrom_ok` and `bodyFrom_ct`. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey VG.Impl.Ed25519.AArch64.Whole
open VG.Proof.Ed25519 (publicKey_of_sha512_eq sha512_length)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- The digest at `seed`, read only and outside what the derivation writes. -/
theorem copy_src (hL : L.Ok) (h64 : L.seedLen = 64) : Whole.CopySrc L.E L.inputs L.outputs L.seed := by
  have hs : (⟨L.seed, 64⟩ : Region) = L.SEED := by rw [Lay.SEED, h64]
  refine ⟨hs ▸ by simp [Lay.inputs], fun r hr => ?_⟩
  rw [hs]
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (frame_sub L)).symm
  · exact hL.cs.symm

/-- The copy's arguments: the digest in `x1`, `frame 192` in `x15`. -/
theorem copy_args {u : State} (ho : ∀ p ∈ copyArgs, u.gpr p.1 = argValue L p.2) :
    u.gpr .x1 = L.seed ∧ u.gpr .x15 = L.E + BitVec.ofNat 64 192 := by
  have a1 := ho (.x1, .caller 1 0) (by simp [copyArgs])
  simp only [argValue, Lay.value, BitVec.add_zero] at a1
  exact ⟨a1, ho (.x15, .frame 192) (by simp [copyArgs])⟩

theorem copy_ok (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) (h64 : L.seedLen = 64) :
    WP isa copyExpanded t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem (L.E + 192) 64 = Spec.Ed25519.bytesAt m₀ L.seed 64 := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := copyArgs) (by decide) (by decide)
    (by simp [copyArgs]) (by simp [copyArgs, preserved])) fun u ⟨hu, _, ho⟩ => ?_)
  have ⟨a1, a15⟩ := copy_args ho
  exact Whole.copy_digest (copy_src hL h64) ⟨hu, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩

variable {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem copyWords_ct :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L copyArgs)) (.block copyWords) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x1, .x15]) (fun a b h => ⟨h.1.1.sp.trans h.2.1.sp.symm,
    fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.1.2.2 (.x1, .caller 1 0) (by simp [copyArgs])).trans
          (h.2.2.2 (.x1, .caller 1 0) (by simp [copyArgs])).symm
      · exact (h.1.2.2 (.x15, .frame 192) (by simp [copyArgs])).trans
          (h.2.2.2 (.x15, .frame 192) (by simp [copyArgs])).symm⟩) (by taint_decide)

theorem copy_ct (hL : L.Ok) (h64 : L.seedLen = 64) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) copyExpanded
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine (setup_ct hL ha hb copyArgs (by decide) (by decide) (by simp [copyArgs])
    (by simp [copyArgs, preserved]) (by taint_decide)).seq
    (Whole.rel_wp copyWords_ct ?_ ?_)
  · intro u ⟨hc, hy, ho⟩
    have ⟨a1, a15⟩ := copy_args ho
    exact WP.mono_syms (Whole.copy_digest (copy_src hL h64) ⟨hc, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun _ h sy => ⟨h.1, sy ▸ hy, trivial⟩
  · intro u ⟨hc, hy, ho⟩
    have ⟨a1, a15⟩ := copy_args ho
    exact WP.mono_syms (Whole.copy_digest (copy_src hL h64) ⟨hc, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun _ h sy => ⟨h.1, sy ▸ hy, trivial⟩

/-! ## The expanded-key entry point -/

/-- The public key from the seed's digest at `x1`. -/
def pkLocalE : Contract isa := pkLocalWith 64 fun s t => ∀ seed : List Byte, seed.length = 32 →
  Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed →
  Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 32 = Spec.Ed25519.publicKey seed

theorem bodyE_depth : (bodyFrom copyExpanded).aarch64Depth ≤ 1 := by
  have hb := Whole.depth_zero_of_noFrames base_noFrames
  simp only [bodyFrom, copyExpanded, Impl.Ed25519.AArch64.Whole.callWith, Code.aarch64Depth, Nat.max_le, hb]
  omega_using []

theorem pkE_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s : State} (h : pkLocalE.pre s) :
    WP isa codeExpanded s fun u => abiPreserved s u ∧ pkLocalE.post s u := by
  have hw := Whole.wrap_ok bodyE_depth (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (s.gpr .x0) 32 = Spec.Ed25519.encodePoint
      (Spec.Ed25519.pointMul (Spec.Ed25519.prune (Spec.Ed25519.bytesAt m (s.gpr .x1) 64))
        Spec.Ed25519.basePoint))
    (hP := fun _ _ _ _ f hq => (List.map_congr_left fun i hi => VG.AArch64.lost_byte f
      ((entry_writes h ⟨s.gpr .x0, 32⟩ (by rw [h.2.1]; simp)).symm.sub_right
        (VG.AArch64.below_sub (by decide) (by decide))) (List.mem_range.mp hi)).trans hq)
    (fun p hp => by
      have hc : Ctx (lay 64 s) s.gpr s.v p.mem _ := entry_ctx h hp
      have hL : (lay 64 s).Ok := lay_ok h
      have ha : Arguments (lay 64 s) p.mem := entry_args h hp
      exact WP.mono (bodyFrom_ok (copy_ok hc hL ha rfl) hL ha (entry_syms hp)) fun u huo => ⟨by
          simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
            Lay.SCR, Lay.ARGS, Lay.TB, lay, h.2.1, List.cons_append, List.nil_append] using huo.1,
          huo.2⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, fun seed _ hs => ?_⟩
  have hd : Spec.Ed25519.bytesAt m (s.gpr .x1) 64 = Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨s.gpr .x1, 64⟩) ?_
      (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed25519.bytesAt u.mem (s.gpr .x0) 32 = _
  rw [hp, hd, hs]
  rfl

theorem pkE_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] :
    ConstantTime isa pkLocalE.pre pkLocalE.pub codeExpanded := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    have hL : (lay 64 s).Ok := lay_ok hs
    have ha := entry_args hs hp
    exact WP.mono (bodyFrom_ok (copy_ok (entry_ctx hs hp) hL ha rfl) hL ha (entry_syms hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq (n := 64) hp
    have hq : Ctx (lay 64 s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay 64 s) q.mem := he ▸ entry_args ht hqb
    have hqs : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms Impl.Ed25519.AArch64.combSym =
        (lay 64 s).T := he ▸ entry_syms hqb
    have hL : (lay 64 s).Ok := lay_ok hs
    have hpa' := entry_args hs hpa
    exact ⟨(bodyFrom_ct (copy_ct hL rfl hpa' hqa) hL hpa' hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, entry_syms hpa, trivial⟩, ⟨hq, hqs, trivial⟩⟩ ea eb).1, trivial⟩

/-! ## The comb's tables in memory, for the witnesses of callers -/

open VG.Impl.Ed25519.AArch64 (combSym combWords combConsts)

/-- The comb's tables at `0x100000`, zeros below (irreducible: unfolding it in a definitional
check would evaluate the tables). -/
@[irreducible] def satMemTE : Mem := fun a =>
  if 0x100000 ≤ a.toNat then constMem 0x100000 combWords a else 0

theorem satMemTE_held : ∀ i < combWords.length,
    satMemTE.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  have hl := combWords_length
  rw [← constMem_held 0x100000 combWords (by omega_using [hl]) i hi]
  refine Mem.readW_congr fun b hb => ?_
  have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b).toNat = 0x100000 + 8 * i + b := by
    have h0 : (0x100000 : Addr).toNat = 0x100000 := rfl
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat, h0,
      Nat.mod_eq_of_lt (a := 8 * i + b) (by omega_using [hi, hl, hb])]
    omega_using [hi, hl, hb]
  unfold satMemTE
  simp only [e, show 0x100000 ≤ 0x100000 + 8 * i + b by omega_using [], ↓reduceIte]

end VG.Proof.Ed25519.AArch64.PublicKey

end

end

/-!
# Ed25519 key-pair derivation on AArch64

`keyPair` calls the one-shot SHA-512 digest of an implementation `v` of the
compression function, as it is emitted, scrubbed whole (`dgCode`), which writes the seed's digest to `expanded`, and then
`vg_ed25519_public_key_expanded`, which derives the public key from it. Its
proof uses only the two callees' contracts.

Addresses on the stack are offsets of `K s`, the lowest byte of the stack the
contract gives it (`sp - 944` on entry): `x30` is saved at `K s + 928`, the
allocation is at `K s + 896` (`out`, `expanded` and `scratch` in its first
three words), and both calls enter with `sp = K s + 896`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.KeyPair

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.KeyPair
open VG.Proof.Ed25519.AArch64 (TBL CombHeld)

/-- The contract. -/
abbrev spec : Contract isa :=
  Spec.Ed25519.keyPairContract (AArch64.abi.withConsts combConsts) 944

/-- The lowest byte of the stack used. -/
abbrev K (s : State) : Addr := s.sp - BitVec.ofNat 64 944

abbrev OUT (s : State) : Region := ⟨s.gpr .x0, 32⟩
abbrev EXP (s : State) : Region := ⟨s.gpr .x1, 64⟩
abbrev SEED (s : State) : Region := ⟨s.gpr .x2, 32⟩
abbrev SCR (s : State) : Region := ⟨s.gpr .x3, 8192⟩
abbrev STK (s : State) : Region := ⟨K s, 944⟩
abbrev TB (s : State) : Region := ⟨s.syms combSym, 8 * combWords.length⟩

/-- The precondition, spelled out. -/
structure Pre (s : State) : Prop where
  sp : 944 ≤ s.sp.toNat
  rd : s.rd = [SEED s, TB s]
  wr : s.wr = [OUT s, EXP s, SCR s]
  held : ∀ i < combWords.length,
    s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0
  fit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64
  tO : (TB s).Disjoint (OUT s)
  tE : (TB s).Disjoint (EXP s)
  tC : (TB s).Disjoint (SCR s)
  tK : (TB s).Disjoint (STK s)
  oe : (OUT s).Disjoint (EXP s)
  os : (OUT s).Disjoint (SEED s)
  oc : (OUT s).Disjoint (SCR s)
  es : (EXP s).Disjoint (SEED s)
  ec : (EXP s).Disjoint (SCR s)
  sc : (SEED s).Disjoint (SCR s)
  ko : (STK s).Disjoint (OUT s)
  ke : (STK s).Disjoint (EXP s)
  ks : (STK s).Disjoint (SEED s)
  kc : (STK s).Disjoint (SCR s)
  no : (s.gpr .x0).toNat + 32 ≤ 2 ^ 64
  ne : (s.gpr .x1).toNat + 64 ≤ 2 ^ 64
  ns : (s.gpr .x2).toNat + 32 ≤ 2 ^ 64
  nc : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64

theorem pre_of {s : State} (h : spec.pre s) : Pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig,
    Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨hsp, hd, hheld, hfit, hdw, hdk, -, ht, hw, oe, os, oc, es, ec, sc,
    ko, ke, ks, kc, no, ne, ns, nc⟩ := h
  refine ⟨hsp, ?_, hw, hheld, hfit, hdw _ (by rw [hw]; simp), hdw _ (by rw [hw]; simp),
    hdw _ (by rw [hw]; simp), hdk, oe, os, oc, es, ec, sc, ko, ke, ks, kc, no, ne, ns, nc⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl

/-- The precondition, from its facts and the tables' alignment. -/
theorem spec_of {s : State} (h : Pre s) (hal : (s.syms combSym).toNat % 64 = 0) : spec.pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig,
    Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  refine ⟨h.sp, by rw [h.rd]; rfl, h.held, h.fit, fun r hr => ?_, h.tK, hal, by rw [h.rd]; rfl, h.wr,
    h.oe, h.os, h.oc, h.es, h.ec, h.sc, h.ko, h.ke, h.ks, h.kc, h.no, h.ne, h.ns, h.nc⟩
  rw [h.wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.tO
  · exact h.tE
  · exact h.tC

/-! ## Addresses on the stack -/

theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    p + BitVec.ofNat 64 a - BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a - b) := by
  have : b < 2 ^ 64 := by omega_using [h, ha]
  have : a - b < 2 ^ 64 := by omega_using [ha]
  bv_omega

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sp_eq (s : State) : s.sp = K s + BitVec.ofNat 64 944 := by
  simp only [K, BitVec.sub_add_cancel]

theorem sp16 (s : State) : s.sp - 16 = K s + BitVec.ofNat 64 928 := by
  rw [sp_eq s]; exact off_sub _ (b := 16) (by decide) (by decide)

theorem sp48 (s : State) : s.sp - 16 - BitVec.ofNat 64 32 = K s + BitVec.ofNat 64 896 := by
  rw [sp16 s]; exact off_sub _ (by decide) (by decide)

theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 944) : Region.Sub ⟨K s + BitVec.ofNat 64 d, n⟩ (STK s) :=
  Offset.sub_base _ h

theorem K_toNat {s : State} (h : Pre s) {d : Nat} (hd : d ≤ 944) :
    (K s + BitVec.ofNat 64 d).toNat = (K s).toNat + d := by
  have hk : (K s).toNat + 944 = s.sp.toNat := by
    have := h.sp
    simp only [K, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [this]
  have := s.sp.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hd, hk]

namespace Pre

variable {s : State}

theorem kO (h : Pre s) {d n : Nat} (hd : d + n ≤ 944) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (OUT s) :=
  h.ko.sub_left (stk_sub s hd)
theorem kE (h : Pre s) {d n : Nat} (hd : d + n ≤ 944) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (EXP s) :=
  h.ke.sub_left (stk_sub s hd)
theorem kS (h : Pre s) {d n : Nat} (hd : d + n ≤ 944) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SEED s) :=
  h.ks.sub_left (stk_sub s hd)
theorem kC (h : Pre s) {d n : Nat} (hd : d + n ≤ 944) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SCR s) :=
  h.kc.sub_left (stk_sub s hd)
theorem kT (h : Pre s) {d n : Nat} (hd : d + n ≤ 944) : Region.Disjoint (TB s) ⟨K s + BitVec.ofNat 64 d, n⟩ :=
  h.tK.sub_right (stk_sub s hd)

end Pre

/-! ## Between the frame's allocation and its release -/

/-- The allocation. -/
abbrev AL (s : State) : Region := ⟨K s + BitVec.ofNat 64 896, 32⟩
/-- Where `x30` is saved. -/
abbrev LR (s : State) : Region := ⟨K s + BitVec.ofNat 64 928, 16⟩

/-- What holds after the arguments are saved, for the entry state `s`. -/
structure Ctx (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = AL s :: LR s :: s.wr
  sp : t.sp = K s + BitVec.ofNat 64 896
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  lr : t.mem.read (K s + BitVec.ofNat 64 928) 8 = s.gpr .x30
  fOut : t.mem.read (K s + BitVec.ofNat 64 896) 8 = s.gpr .x0
  fExp : t.mem.read (K s + BitVec.ofNat 64 904) 8 = s.gpr .x1
  fScr : t.mem.read (K s + BitVec.ofNat 64 912) 8 = s.gpr .x3
  sym : t.syms = s.syms
  frame : Frame [OUT s, EXP s, SCR s, STK s] s.mem t.mem

/-- The state the body starts in. -/
abbrev entered (s : State) : State := allocated 32 (pushed .x30 s)

theorem entered_sp (s : State) : (entered s).sp = K s + BitVec.ofNat 64 896 := sp48 s

theorem entered_wr (s : State) : (entered s).wr = AL s :: LR s :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 32, 32⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [sp48, sp16]

theorem entered_in {s : State} {d : Nat} (hd : d + 8 ≤ 32) :
    InRegions (entered s).wr ((entered s).sp + BitVec.ofNat 64 d) 8 := by
  rw [entered_wr, entered_sp, add_add]
  exact ⟨AL s, List.mem_cons_self .., Offset.contains _ (by omega_using []) (by omega_using [hd]) (by omega_using [])⟩

/-- The arguments saved, and the digest's arguments. -/
theorem digestArgs_ok (s : State) :
    WP isa (.block digestArgs) (entered s) fun t => Ctx s t ∧ t.gpr .x0 = s.gpr .x2 ∧
      t.gpr .x1 = BitVec.ofNat 64 32 ∧ t.gpr .x2 = s.gpr .x1 := by
  have h0 : InRegions (entered s).wr (entered s).sp 8 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using entered_in (s := s) (d := 0) (by decide)
  have h8 := entered_in (s := s) (d := 8) (by decide)
  have h16 := entered_in (s := s) (d := 16) (by decide)
  apply WP.of_runBlock
  have hz : (BitVec.ofNat 16 32).setWidth 64 <<< 0 = BitVec.ofNat 64 32 := by decide
  simp only [digestArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.store, State.read,
    h0, h8, h16, ite_true, Nat.reduceMod, Nat.reduceLT, and_self, Size.bits, BitVec.setWidth_eq,
    BitVec.add_zero, Nat.mul_zero, Option.some.injEq, exists_eq_left', RegUpd.gpr_write_self,
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x1 = Reg.x0 by decide)),
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x0 = Reg.x2 by decide)),
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x0 = Reg.x1 by decide)),
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x2 = Reg.x1 by decide))]
  have e0 : (entered s).gpr = s.gpr := rfl
  have em : (entered s).mem = s.mem.write (K s + BitVec.ofNat 64 928) 8 (s.gpr .x30) := by
    show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _; rw [sp16]
  rw [e0, em, entered_sp, add_add, add_add]
  have sep : ∀ {d e : Nat}, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ 944 → e + 8 ≤ 944 →
      Mem.Sep (K s + BitVec.ofNat 64 d) 8 (K s + BitVec.ofNat 64 e) 8 :=
    fun h₁ h₂ h₃ => Offset.sep _ h₁ (by omega_using [h₂]) (by omega_using [h₃])
  have kc : ∀ {d : Nat}, d + 8 ≤ 944 → (STK s).Contains (K s + BitVec.ofNat 64 d) 8 :=
    fun hd => Offset.contains_base _ hd (by omega_using [hd])
  have hk : STK s ∈ [OUT s, EXP s, SCR s, STK s] := by simp
  refine ⟨⟨rfl, entered_wr s, rfl, fun r hr hr' => ?_, fun _ _ => rfl, ?_, ?_, ?_, ?_, rfl,
    (((((Frame.refl _ _).write hk _ (kc (by decide))).write hk _ (kc (by decide))).write hk _
      (kc (by decide))).write hk _ (kc (by decide)))⟩, rfl, hz, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hr' | rfl
  · show Mem.read (Mem.write _ _ 8 _) _ 8 = _
    rw [Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide), read_write_self]
  · show Mem.read (Mem.write _ _ 8 _) _ 8 = _
    rw [Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide), read_write_self]
  · show Mem.read (Mem.write _ _ 8 _) _ 8 = _
    rw [Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide), read_write_self]
  · show Mem.read (Mem.write _ _ 8 _) _ 8 = _
    rw [read_write_self]

/-! ## Memory -/

/-- Bytes outside the regions a frame lists are kept. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' p n = Spec.Ed25519.bytesAt m p n :=
  List.map_congr_left fun _ hi => Frame.bytes hf (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem Ctx.bytes {s t : State} (hc : Ctx s t) {p : Addr} {n : Nat}
    (h₁ : Region.Disjoint ⟨p, n⟩ (OUT s)) (h₂ : Region.Disjoint ⟨p, n⟩ (EXP s))
    (h₃ : Region.Disjoint ⟨p, n⟩ (SCR s)) (h₄ : Region.Disjoint ⟨p, n⟩ (STK s)) (hn : n ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem p n = Spec.Ed25519.bytesAt s.mem p n := by
  refine bytesAt_frame hc.frame (fun r hr => ?_) hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

/-- What a call from the frame may change below `sp`, `16 d` bytes: within the stack used. -/
theorem below_sub {s t : State} (hc : Ctx s t) {d : Nat} (hd : 16 * d ≤ 896) :
    Region.Sub (below t.sp (16 * d)) (STK s) := by
  rw [hc.sp]
  show Region.Sub ⟨K s + BitVec.ofNat 64 896 - BitVec.ofNat 64 (16 * d), 16 * d⟩ _
  rw [off_sub _ hd (by decide)]
  exact stk_sub s (by omega_using [hd])

/-- After a call from the frame that writes `wr` (within `out`, `expanded` and
`scratch`) and the stack below `sp` the callee uses, `Ctx` holds again. -/
theorem Ctx.call {s t t' : State} (h : Pre s) (hc : Ctx s t) {wr : List Region} {d : Nat}
    (hd : 16 * d ≤ 896) (hsub : ∀ r ∈ wr, r = OUT s ∨ r = EXP s ∨ r = SCR s)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hf : Frame (wr ++ [below t.sp (16 * d)]) t.mem t'.mem)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hvs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hsy : t'.syms = t.syms) : Ctx s t' := by
  have keep : ∀ e, 896 ≤ e → e + 8 ≤ 944 →
      t'.mem.read (K s + BitVec.ofNat 64 e) 8 = t.mem.read (K s + BitVec.ofNat 64 e) 8 := by
    intro e h₁ h₂
    refine hf.read (r := ⟨K s + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · rcases hsub r hr with rfl | rfl | rfl
      · exact h.kO (by omega_using [h₂])
      · exact h.kE (by omega_using [h₂])
      · exact h.kC (by omega_using [h₂])
    · rw [List.mem_singleton.mp hr, hc.sp]
      have e' : K s + BitVec.ofNat 64 e = K s + BitVec.ofNat 64 896 + BitVec.ofNat 64 (e - 896) := by
        rw [add_add, Nat.add_sub_cancel' h₁]
      rw [e']
      exact Offset.disjoint_below _ (by omega_using [hd, h₂])
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'), fun r hr => (hvs r hr).trans (hc.vs r hr),
    (keep 928 (by decide) (by decide)).trans hc.lr, (keep 896 (by decide) (by decide)).trans hc.fOut,
    (keep 904 (by decide) (by decide)).trans hc.fExp, (keep 912 (by decide) (by decide)).trans hc.fScr,
    hsy.trans hc.sym, hc.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rcases hsub r hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp, below_sub hc hd⟩

/-! ## The digest -/

variable (v : Proof.Sha512.AArch64.Compress)

/-- The one-shot digest, as `vg_sha512_digest` runs it before it is scrubbed. -/
abbrev dgRaw : Prog isa :=
  Proof.Sha512.AArch64.oneShotWith (Impl.MdStream.AArch64.out64 8) Spec.Sha512.H0_512 v.suffix v.code

/-- `vg_sha512_digest` as it is emitted (`AArch64.ScrubAll.withScrubAll`): the
digest, then the registers it may write cleared and its frame zeroed. -/
abbrev dgCode : Prog isa :=
  VG.Impl.Residue.AArch64.scrubAll Proof.Sha512.AArch64.OneShot.stack 0
    (VG.Impl.Residue.AArch64.Clear.of (dgRaw v)) (dgRaw v)

abbrev dgK : Contract isa :=
  Spec.Sha512.digestContract AArch64.abi 64 Spec.Sha512.sha512 Proof.Sha512.AArch64.OneShot.stack

/-- The digest's postcondition reads the memory on return only within its output. -/
theorem dgOk : AArch64.ScrubAll.ScrubAllOk dgK Proof.Sha512.AArch64.OneShot.stack 0 :=
  AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Sha512.digestSig 64) (by decide) (by decide) (Nat.le_refl _)
    (Proof.Sha512.digestPost_out _ _ _ (by decide))

/-- The digest never writes PSTATE.DIT: its own code does not, and `v`'s
compression function does not (`Compress.noDit`). -/
theorem dgRaw_noDit : (dgRaw v).all (fun i => !i.writesDit) = true := by
  simp only [dgRaw, Proof.Sha512.AArch64.oneShotWith, Impl.MdStream.AArch64.OneShot.digest,
    Impl.MdStream.AArch64.OneShot.body, Impl.MdStream.AArch64.OneShot.tail, Impl.MdStream.AArch64.OneShot.whole,
    Impl.MdStream.AArch64.OneShot.compressBuf, Impl.MdStream.AArch64.OneShot.compressWith, Code.all, v.noDit,
    Bool.and_true]
  decide

/-- Nor does the scrubbing after it. -/
theorem dg_noDit : (dgCode v).all (fun i => !i.writesDit) = true := by
  have hn := dgRaw_noDit v
  show Code.all (fun i => !i.writesDit) (.seq (VG.Impl.Residue.AArch64.withRet 0
    (.seq (dgRaw v) (.block (VG.Impl.Residue.AArch64.clearsOf _))))
    (VG.Impl.Residue.AArch64.scrubTailG 896 (List.range 56))) = true
  simp only [VG.Impl.Residue.AArch64.withRet, VG.Impl.Residue.AArch64.scrubTailG, Code.all, hn,
    Bool.true_and, VG.Impl.Residue.AArch64.clearsOf, List.all_append, List.all_map, Function.comp_def]
  simp [Instr.writesDit]
  decide

theorem dgRaw_verified : Verified AArch64.target (dgRaw v) dgK :=
  (v.oneShot_verified (by decide) Proof.Sha512.AArch64.Stream.shape.toD v.oneShot512).of_implies
    (Proof.Sha512.AArch64.OneShot.implies (by decide) fun m =>
      List.take_of_length_le (Nat.le_of_eq (VG.Proof.Hmac.Generic.Common.finalHash_length _ m)))

theorem dg_verified : Verified AArch64.target (dgCode v) dgK :=
  AArch64.ScrubAll.Verified.scrubAll (VG.Impl.Residue.AArch64.Clear.of_wf _) (dgRaw_verified v)
    (by decide) (.inl rfl) dgOk

theorem dgRaw_depth : (dgRaw v).aarch64Depth ≤ 56 := by
  have h0 := Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames v.noFrames
  simp only [Proof.Sha512.AArch64.oneShotWith, Impl.MdStream.AArch64.OneShot.digest,
    Impl.MdStream.AArch64.OneShot.body, Impl.MdStream.AArch64.OneShot.whole,
    Impl.MdStream.AArch64.OneShot.tail, Impl.MdStream.AArch64.OneShot.compressWith,
    Impl.MdStream.AArch64.OneShot.compressBuf, Impl.MdStream.AArch64.OneShot.copyTail,
    Impl.MdStream.AArch64.OneShot.bytesTail, Impl.Sha512.AArch64.Stream.initPairs,
    Code.aarch64Depth, h0, Proof.Sha512.AArch64.OneShot.frameBytes_out, Nat.max_self,
    AArch64.Instr.frameUnits, Nat.zero_add]
  decide

/-- The scrubbing's frame is the digest's: 56 units. -/
theorem dg_depth : (dgCode v).aarch64Depth ≤ 56 := by
  have hl := dgRaw_depth v
  show Code.aarch64Depth (.seq (VG.Impl.Residue.AArch64.withRet 0
    (.seq (dgRaw v) (.block (VG.Impl.Residue.AArch64.clearsOf _))))
    (VG.Impl.Residue.AArch64.scrubTailG 896 (List.range 56))) ≤ 56
  simp only [VG.Impl.Residue.AArch64.withRet, VG.Impl.Residue.AArch64.scrubTailG, Code.aarch64Depth,
    AArch64.Instr.frameUnits, Nat.max_le, Nat.zero_le, Nat.reduceDiv, Nat.zero_add, Nat.le_refl, and_true]
  exact hl

theorem ce_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := State.callEntry_gpr t h

theorem dg_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hx0 : t.gpr .x0 = s.gpr .x2)
    (hx1 : t.gpr .x1 = BitVec.ofNat 64 32) (hx2 : t.gpr .x2 = s.gpr .x1) :
    dgK.pre (t.callEntry.withRegions [SEED s] [EXP s]) := by
  sig_pre [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, AArch64.abi,
    AArch64.argRegs, stackBelow]
  rw [hc.sp, hx0, hx1, hx2, BitVec.add_sub_cancel, show (BitVec.ofNat 64 32).toNat = 32 from rfl]
  have k0 : ∀ {n}, (⟨K s, n⟩ : Region) = ⟨K s + BitVec.ofNat 64 0, n⟩ := by simp
  refine ⟨by rw [K_toNat h (by decide)]; show 896 ≤ _; omega_using [], rfl, rfl, h.es.symm, ?_, ?_, h.ns, h.ne⟩
  · rw [k0]; exact h.kS (by decide)
  · rw [k0]; exact h.kE (by decide)

theorem dg_cov {s t : State} (h : Pre s) (hc : Ctx s t) :
    Covers ([SEED s] ++ [EXP s]) (t.rd ++ t.wr) ∧ Covers [EXP s] t.wr := by
  refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rw [hc.rd, hc.wr, h.rd, h.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · rw [hc.wr, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp

/-- The digest's call: the seed's digest at `expanded`. -/
theorem digest_ok {s t : State} (h : Pre s) (hc : Ctx s t) {dn : String} (hx0 : t.gpr .x0 = s.gpr .x2)
    (hx1 : t.gpr .x1 = BitVec.ofNat 64 32) (hx2 : t.gpr .x2 = s.gpr .x1) :
    WP isa (.call dn (dgCode v)) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .x1) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32) := by
  have hd := dg_depth v
  refine WP.of_syms (WP.callFV (dg_verified v).1 (dg_pre h hc hx0 hx1 hx2) (dg_cov h hc).1 (dg_cov h hc).2
    (fun t' hrd hwr hsp hf hcs hvs hpost hsy => ⟨?_, ?_⟩) (by omega_using [hd]))
  · exact Ctx.call h hc (by omega_using [hd]) (by simp) hrd hwr hsp hf hcs hvs hsy
  · sig_post [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, AArch64.abi,
      AArch64.argRegs] at hpost
    simp only [hx0, hx1, hx2, show (BitVec.ofNat 64 32).toNat = 32 from rfl] at hpost
    have hS : Spec.Ed25519.bytesAt t.mem (s.gpr .x2) 32 = Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 :=
      hc.bytes h.os.symm h.es.symm h.sc h.ks.symm (by decide)
    exact hpost.trans (congrArg Spec.Sha512.sha512 hS)

/-! ## The public key -/

/-- A write of a register the ABI does not preserve. -/
theorem Ctx.write {s t : State} (hc : Ctx s t) {r : Reg} (hr : r ∉ preserved) (x : BitVec 64) :
    Ctx s (t.write .x r x) :=
  ⟨hc.rd, hc.wr, hc.sp, fun q hq hq' => by
      have hne : ¬q = r := fun e => hr (e ▸ hq)
      rw [RegUpd.gpr_write_of_ne (h := hne)]; exact hc.cs q hq hq',
    hc.vs, hc.lr, hc.fOut, hc.fExp, hc.fScr, hc.sym, hc.frame⟩

/-- The public key's arguments, from the allocation. -/
theorem pkArgs_ok {s t : State} (hc : Ctx s t) :
    WP isa (.block pkArgs) t fun t' => Ctx s t' ∧ t'.mem = t.mem ∧ t'.gpr .x0 = s.gpr .x0 ∧
      t'.gpr .x1 = s.gpr .x1 ∧ t'.gpr .x2 = s.gpr .x3 := by
  have hin : ∀ d, d + 8 ≤ 32 → InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hc.wr, hc.sp, add_add]
    exact ⟨AL s, by simp, Offset.contains _ (by omega_using []) (by omega_using [hd]) (by omega_using [])⟩
  have h0 : InRegions (t.rd ++ t.wr) t.sp 8 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hin 0 (by decide)
  have h8 := hin 8 (by decide)
  have h16 := hin 16 (by decide)
  apply WP.of_runBlock
  simp only [pkArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, h0, h8, h16, ite_true,
    Nat.reduceMod, Nat.reduceLT, and_self, Option.map_some, Size.bits, BitVec.setWidth_eq, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', RegUpd.sp_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne (h := (show ¬Reg.x0 = Reg.x1 by decide)),
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x0 = Reg.x2 by decide)),
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x1 = Reg.x2 by decide))]
  have e0 : t.sp = K s + BitVec.ofNat 64 896 := hc.sp
  rw [e0, add_add, add_add]
  exact ⟨((hc.write (by decide) _).write (by decide) _).write (by decide) _, trivial, hc.fOut, hc.fExp,
    hc.fScr⟩

abbrev pkRd (s : State) : List Region := [EXP s, TB s]
abbrev pkWr (s : State) : List Region := [OUT s, SCR s]

theorem pk_depth : PublicKey.codeExpanded.aarch64Depth ≤ 22 := by
  have h := PublicKey.bodyE_depth
  simp only [PublicKey.codeExpanded, Impl.Ed25519.AArch64.Whole.wrap, Code.aarch64Depth,
    AArch64.Instr.frameUnits, Nat.zero_max]
  exact Nat.add_le_add_right (Nat.add_le_add_right h _) _

theorem ce_syms (t : State) (rd wr : List Region) : (t.callEntry.withRegions rd wr).syms = t.syms := rfl

theorem pk_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hx0 : t.gpr .x0 = s.gpr .x0)
    (hx1 : t.gpr .x1 = s.gpr .x1) (hx2 : t.gpr .x2 = s.gpr .x3) :
    PublicKey.pkLocalE.pre (t.callEntry.withRegions (pkRd s) (pkWr s)) := by
  simp only [PublicKey.pkLocalE, Proof.Ed25519.AArch64.PublicKey.pkLocalWith, CombHeld,
    ce_gpr t _ _ (show Reg.x0 ∉ linkRegs by decide), ce_gpr t _ _ (show Reg.x1 ∉ linkRegs by decide),
    ce_gpr t _ _ (show Reg.x2 ∉ linkRegs by decide), State.withRegions_sp, State.callEntry_sp,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.callEntry_mem, hc.sp, hx0, hx1,
    hx2, ce_syms, hc.sym, below]
  rw [off_sub _ (b := 352) (by decide) (by decide)]
  refine ⟨trivial, trivial, h.oe, h.oc, h.ec, h.kO (by decide), h.kE (by decide), h.kC (by decide), h.no, h.ne, h.nc,
    by rw [K_toNat h (by decide)]; omega_using [], fun i hi => ?_, h.fit, fun r hr => ?_⟩
  · rw [hc.frame.readW (r := TB s) (Offset.contains_base _ (by have := h.fit; omega_using [hi]) (by have := h.fit; omega_using [hi, this]))
      (fun r hr => ?_) (by decide)]
    · exact h.held i hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.tO
      · exact h.tE
      · exact h.tC
      · exact h.tK
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.tO
    · exact h.tC
    · exact h.kT (by decide)

theorem pk_cov {s t : State} (h : Pre s) (hc : Ctx s t) :
    Covers (pkRd s ++ pkWr s) (t.rd ++ t.wr) ∧ Covers (pkWr s) t.wr := by
  refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rw [hc.rd, hc.wr, h.rd, h.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

section
variable [Proof.Ed25519.AArch64.Divstep.Sound]

theorem pk_ok {s t : State} (h : Pre s) (hc : Ctx s t) {pn : String} (hx0 : t.gpr .x0 = s.gpr .x0)
    (hx1 : t.gpr .x1 = s.gpr .x1) (hx2 : t.gpr .x2 = s.gpr .x3)
    (hE : Spec.Ed25519.bytesAt t.mem (s.gpr .x1) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32)) :
    WP isa (.call pn PublicKey.codeExpanded) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .x1) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32) ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .x0) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32) := by
  have hd := pk_depth
  refine WP.of_syms (WP.callFV (k := PublicKey.pkLocalE) (fun _ h => PublicKey.pkE_ok h)
    (pk_pre h hc hx0 hx1 hx2) (pk_cov h hc).1 (pk_cov h hc).2
    (fun t' hrd hwr hsp hf hcs hvs hpost hsy =>
      ⟨Ctx.call h hc (by omega_using [hd]) (by simp) hrd hwr hsp hf hcs hvs hsy, ?_, ?_⟩) (by omega_using [hd]))
  · rw [← hE]
    refine bytesAt_frame hf (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.oe.symm
    · exact h.ec
    · exact h.ke.symm.sub_right (below_sub hc (by omega_using [hd]))
  · simp only [PublicKey.pkLocalE, Proof.Ed25519.AArch64.PublicKey.pkLocalWith, State.withRegions_mem,
      State.callEntry_mem, ce_gpr t _ _ (show Reg.x0 ∉ linkRegs by decide),
      ce_gpr t _ _ (show Reg.x1 ∉ linkRegs by decide), hx0, hx1] at hpost
    exact hpost _ (by simp [Spec.Ed25519.bytesAt]) hE

/-! ## The whole function -/

/-- The frame's body, from the allocation. -/
theorem body_ok {s : State} (h : Pre s) {dn pn : String} :
    WP isa (.seq (.block digestArgs) (.seq (.call dn (dgCode v)) (.seq (.block pkArgs)
      (.call pn PublicKey.codeExpanded)))) (entered s) fun t => Ctx s t ∧
      Spec.Ed25519.bytesAt t.mem (s.gpr .x1) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32) ∧
      Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32) := by
  refine WP.seq (WP.mono (digestArgs_ok s) fun t ⟨hc, hx0, hx1, hx2⟩ => ?_)
  refine WP.seq (WP.mono (digest_ok v h hc hx0 hx1 hx2) fun t ⟨hc, hE⟩ => ?_)
  refine WP.seq (WP.mono (pkArgs_ok hc) fun t' ⟨hc', hm, hx0, hx1, hx2⟩ => ?_)
  exact pk_ok h hc' hx0 hx1 hx2 (by rw [hm]; exact hE)

theorem keyPair_ok {s : State} (hs : spec.pre s) {dn pn : String} :
    WP isa (keyPair dn (dgCode v) pn PublicKey.codeExpanded) s fun s' =>
      abiPreserved s s' ∧ spec.post s s' := by
  have h := pre_of hs
  have hsp := h.sp
  refine WP.frameAlloc (by omega_using [hsp]) (by decide) ?_
    (WP.mono (body_ok v h) fun u ⟨hu, hE, hO⟩ m uu f => ⟨?_, ?_⟩)
  · show 32 ≤ (s.sp - 16).toNat
    rw [sp16, K_toNat h (by decide)]; omega_using []
  · have hsp' : (freed 32 u).sp = K s + BitVec.ofNat 64 928 := by
      show u.sp + BitVec.ofNat 64 32 = _; rw [hu.sp, add_add]
    refine ⟨fun r hr => ?_, ?_, fun r hr => hu.vs r hr⟩
    · by_cases h30 : r = .x30
      · subst h30
        show ((freed 32 u).mem.read (freed 32 u).sp 8).setWidth 64 = _
        rw [hsp', BitVec.setWidth_eq]; exact hu.lr
      · show (if r = .x30 then _ else u.gpr r) = _
        rw [ite_eq_right_iff.mpr (fun h => absurd h h30)]; exact hu.cs r hr h30
    · show (freed 32 u).sp + 16 = s.sp
      rw [hsp', sp_eq s]; exact add_add _ _ _
  · sig_post [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts]
    have hb : VG.AArch64.below s.sp 48 = ⟨K s + BitVec.ofNat 64 896, 48⟩ := by
      show (⟨s.sp - BitVec.ofNat 64 48, 48⟩ : Region) = _
      rw [sp_eq s, off_sub _ (by decide) (by decide)]
    have hl : ∀ {R : Region} {n : Nat}, Region.Disjoint ⟨K s + BitVec.ofNat 64 896, 48⟩ R → R.len = n →
        Spec.Ed25519.bytesAt m R.base n = Spec.Ed25519.bytesAt u.mem R.base n := by
      intro R n hd hn
      subst hn
      rw [← hb] at hd
      exact List.map_congr_left fun i hi => VG.AArch64.lost_byte f hd.symm (List.mem_range.mp hi)
    exact ⟨(hl (h.kE (by decide)) rfl).trans hE, (hl (h.kO (by decide)) rfl).trans hO⟩

end

/-! ## Constant time -/

structure Pub (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  x0 : s₁.gpr .x0 = s₂.gpr .x0
  x1 : s₁.gpr .x1 = s₂.gpr .x1
  x2 : s₁.gpr .x2 = s₂.gpr .x2
  x3 : s₁.gpr .x3 = s₂.gpr .x3
  sy : s₁.syms combSym = s₂.syms combSym
  dit : s₁.dit = s₂.dit

theorem pub_of {s₁ s₂ : State} (h : spec.pub s₁ s₂) : Pub s₁ s₂ := by
  sig_pub_keep [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords,
    AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts] at h
  obtain ⟨h0, hd, hs, h1, h2, h3, h4⟩ := h
  exact ⟨h0, h1, h2, h3, h4, hs, hd⟩

def Rel (Φ : State → State → Prop) (a b : State) : Prop :=
  ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧ Ctx s₁ a ∧ Ctx s₂ b ∧ Φ s₁ a ∧ Φ s₂ b ∧ a.dit = b.dit

theorem rel_wp {c : Prog isa} {Φ Ψ : State → State → Prop} (hd : DitDet c)
    (hct : RelCT isa (Rel Φ) c fun _ _ => True)
    (hw : ∀ s t, Pre s → Ctx s t → Φ s t → WP isa c t fun t' => Ctx s t' ∧ Ψ s t') :
    RelCT isa (Rel Φ) c (Rel Ψ) := by
  intro a b ta tb a' b' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, h₁, h₂, hp', c₁, c₂, f₁, f₂, hm⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw s₁ a h₁ c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw s₂ b h₂ c₂ f₂
  have hm' := hd _ _ _ _ _ e₁ (ht ▸ e₂) hm
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, s₁, s₂, h₁, h₂, hp', y₁.1, y₂.1, y₁.2, y₂.2, hm'⟩

theorem rel_sp {Φ : State → State → Prop} {a b : State} (h : Rel Φ a b) : a.sp = b.sp := by
  obtain ⟨_, _, _, _, hp, c₁, c₂, _⟩ := h
  rw [c₁.sp, c₂.sp, K, K, hp.sp]

variable [Proof.Ed25519.AArch64.Divstep.Sound]

abbrev Φ₁ (s t : State) : Prop :=
  t.gpr .x0 = s.gpr .x2 ∧ t.gpr .x1 = BitVec.ofNat 64 32 ∧ t.gpr .x2 = s.gpr .x1
abbrev Φ₂ (s t : State) : Prop :=
  Spec.Ed25519.bytesAt t.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32)
abbrev Φ₃ (s t : State) : Prop :=
  Φ₂ s t ∧ t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x3

theorem body_ct {dn pn : String} :
    RelCT isa (fun a b => ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂)
      (.seq (.block digestArgs) (.seq (.call dn (dgCode v)) (.seq (.block pkArgs)
        (.call pn PublicKey.codeExpanded)))) fun _ _ => True := by
  have b₁ : RelCT isa (fun a b => ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂)
      (.block digestArgs) (Rel Φ₁) := by
    intro a b ta tb a' b' hp e₁ e₂
    obtain ⟨ht, -⟩ := Whole.block_rel (P := fun a b => ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧
        a = entered s₁ ∧ b = entered s₂)
      (fun _ _ ⟨s₁, s₂, _, _, hp, ea, eb⟩ => by rw [ea, eb, entered_sp, entered_sp, K, K, hp.sp])
      (by taint_decide) _ _ _ _ _ _ hp e₁ e₂
    obtain ⟨s₁, s₂, h₁, h₂, hp', rfl, rfl⟩ := hp
    obtain ⟨_, u₁, x₁, y₁⟩ := digestArgs_ok s₁
    obtain ⟨_, u₂, x₂, y₂⟩ := digestArgs_ok s₂
    have hm' := DitDet.of_noWrite (c := .block digestArgs) (by decide) _ _ _ _ _ e₁ (ht ▸ e₂)
      (show (entered s₁).dit = (entered s₂).dit from hp'.dit)
    obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
    exact ⟨ht, s₁, s₂, h₁, h₂, hp', y₁.1, y₂.1, y₁.2, y₂.2, hm'⟩
  have b₂ : RelCT isa (Rel Φ₁) (.call dn (dgCode v)) (Rel Φ₂) := by
    refine rel_wp (DitDet.of_noWrite (dg_noDit v)) (RelCT.callEx (dg_verified v).1 (dg_verified v).2.1 fun a b hr => ?_)
      fun s _ h hc ⟨hx0, hx1, hx2⟩ => digest_ok v h hc hx0 hx1 hx2
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨d₁, i₁, x₁⟩, ⟨d₂, i₂, x₂⟩, hm⟩ := hr
    refine ⟨_, _, _, _, dg_pre h₁ c₁ d₁ i₁ x₁, dg_pre h₂ c₂ d₂ i₂ x₂, ?_, (dg_cov h₁ c₁).1, (dg_cov h₁ c₁).2,
      (dg_cov h₂ c₂).1, (dg_cov h₂ c₂).2⟩
    sig_pub [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, AArch64.abi,
      AArch64.argRegs]
    rw [c₁.sp, c₂.sp, d₁, d₂, i₁, i₂, x₁, x₂, K, K, hp.sp, hp.x2, hp.x1]
    exact ⟨rfl, hm, rfl, rfl, rfl⟩
  have b₃ : RelCT isa (Rel Φ₂) (.block pkArgs) (Rel Φ₃) :=
    rel_wp (DitDet.of_noWrite (by decide)) (Whole.block_rel (fun _ _ hr => rel_sp hr) (by taint_decide)) fun _ _ _ hc hE =>
      WP.mono (pkArgs_ok hc) fun _ ⟨hc', hm, a, b, d⟩ => ⟨hc', by rw [Φ₂, hm]; exact hE, a, b, d⟩
  have b₄ : RelCT isa (Rel Φ₃) (.call pn PublicKey.codeExpanded) fun _ _ => True := by
    refine RelCT.callEx (k := PublicKey.pkLocalE) (fun _ h => PublicKey.pkE_ok h) PublicKey.pkE_ct
      fun a b hr => ?_
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨-, d₁, i₁, x₁⟩, ⟨-, d₂, i₂, x₂⟩, -⟩ := hr
    refine ⟨_, _, _, _, pk_pre h₁ c₁ d₁ i₁ x₁, pk_pre h₂ c₂ d₂ i₂ x₂, ?_, (pk_cov h₁ c₁).1,
      (pk_cov h₁ c₁).2, (pk_cov h₂ c₂).1, (pk_cov h₂ c₂).2⟩
    simp only [PublicKey.pkLocalE, Proof.Ed25519.AArch64.PublicKey.pkLocalWith, State.withRegions_sp,
      State.callEntry_sp, ce_syms, ce_gpr _ _ _ (show Reg.x0 ∉ linkRegs by decide),
      ce_gpr _ _ _ (show Reg.x1 ∉ linkRegs by decide), ce_gpr _ _ _ (show Reg.x2 ∉ linkRegs by decide),
      c₁.sp, c₂.sp, d₁, d₂, i₁, i₂, x₁, x₂, c₁.sym, c₂.sym, K, hp.sp, hp.x0, hp.x1, hp.x3, hp.sy]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  exact b₁.seq (b₂.seq (b₃.seq b₄))

theorem keyPair_ct {dn pn : String} :
    ConstantTime isa spec.pre spec.pub (keyPair dn (dgCode v) pn PublicKey.codeExpanded) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => (pub_of h.2.2).sp)
    (RelCT.alloc (RelCT.mono (body_ct v) ?_ fun _ _ _ => trivial)))
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, pre_of h₁, pre_of h₂, pub_of hp, rfl, rfl⟩

/-! ## A witness, and the artifact's obligation -/

/-- A state satisfying the precondition: `out` at `0x1000`, `expanded` at `0x2000`, the seed at
`0x3000`, `scratch` at `0x4000`, the stack below `0x9000` and the comb's tables at `0x100000`. -/
def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x9000
  mem := PublicKey.satMemTE
  rd := [⟨0x3000, 32⟩, ⟨0x100000, 49152⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

omit [Proof.Ed25519.AArch64.Divstep.Sound] in
theorem sat_pre : Pre satState := by
  have hl := combWords_length
  refine ⟨by decide, by simp only [satState, SEED, TB, hl], rfl, PublicKey.satMemTE_held,
    by simp only [satState, hl]; decide,
    by simp only [TB, OUT, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, EXP, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, SCR, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, STK, hl]; exact Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩

omit [Proof.Ed25519.AArch64.Divstep.Sound] in
theorem sat : spec.pre satState := spec_of sat_pre (by decide)

theorem verified {dn pn : String} :
    Verified AArch64.target (keyPair dn (dgCode v) pn PublicKey.codeExpanded) spec :=
  ⟨fun _ h => keyPair_ok v h, keyPair_ct v, ⟨_, sat⟩⟩

/-! ## The function as emitted -/

omit [Proof.Ed25519.AArch64.Divstep.Sound] in
/-- A test of every instruction of `vg_ed25519_key_pair` and of what it
calls, from its own code's, the digest's and the public key's. -/
theorem keyPair_side {p : Instr → Bool} (dn pn : String) {dg pk : Prog isa}
    (h0 : ScrubAll.sideAll p (keyPair "" (.block []) "" (.block [])) = true)
    (hd : ScrubAll.sideAll p dg = true) (hk : ScrubAll.sideAll p pk = true) :
    ScrubAll.sideAll p (keyPair dn dg pn pk) = true := by
  simp only [keyPair, ScrubAll.sideAll, Bool.and_eq_true] at h0 ⊢
  revert h0
  repeat' first
    | exact id
    | exact fun _ => hd
    | exact fun _ => hk
    | refine And.imp ?_ ?_

/-- `vg_ed25519_key_pair` made with `v` as emitted, cleanup included
(`Impl.Ed25519.AArch64.KeyPair.Fn.keyPair`): it meets its contract in
constant time and returns without secret residue. -/
theorem keyPair_scrubbed :
    VerifiedScrubbed AArch64.target (Impl.Ed25519.AArch64.KeyPair.Fn.keyPair v.suffix v.code) spec 0 :=
  ScrubAll.verifiedScrubbedOf (verified v) Proof.Ed25519.AArch64.Scrub.keyPairOk (by decide)
    (by
      have h1 := dg_depth v
      have h2 := pk_depth
      simp only [keyPair, Code.aarch64Depth, Instr.frameUnits]
      omega)
    (keyPair_side _ _ (by kernel_rfl)
      (ScrubAll.sideAll_scrubAll (Proof.Pbkdf2.Md.AArch64.mdDigest_side _ _ _ (by kernel_rfl) v.side))
      (by kernel_rfl))
    (Or.inl rfl)

end VG.Proof.Ed25519.AArch64.KeyPair
