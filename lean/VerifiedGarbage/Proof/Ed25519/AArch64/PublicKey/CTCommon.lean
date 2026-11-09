module

public import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.AArch64.Ladder

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
    refine hc.frame.readW (r := L.TB) (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)
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
    (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)) ?_ (by decide)
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
  · have hw := Whole.saved_words hp (j := j) (by omega)
    have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases he with rfl | rfl | rfl <;> exact hw
  · obtain ⟨held, fit, dj⟩ := h.2.2.2.2.2.2.2.2.2.2.2.2
    have hf := Whole.saved_frame hp
    rw [← held i hi]
    refine hf.readW (r := TBL (s.syms Impl.Ed25519.AArch64.combSym))
      (Offset.contains_base _ (by omega) (by omega)) (fun r hr => ?_) (by decide)
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
