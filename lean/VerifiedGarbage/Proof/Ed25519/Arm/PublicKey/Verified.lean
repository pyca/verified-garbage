module

public import VerifiedGarbage.Impl.Ed25519.Arm.PublicKey
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Setup
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.HashPre
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.PruneCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Prune
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Offset

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Correct`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.Arm.PublicKey.Layout`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

structure Lay where
  out : BitVec 32
  seed : BitVec 32
  scr : BitVec 32
  E : BitVec 32
  /-- The address of the comb's tables (`combSym`). -/
  T : BitVec 32

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨State.addr L.out, 32⟩
abbrev SEED : Region := ⟨State.addr L.seed, 32⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := ⟨State.addr L.E, 280⟩
abbrev TB : Region := TBL L.T
def inputs : List Region := [L.SEED, L.TB, L.ARGS]
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
  no : L.out.toNat + 32 ≤ 2 ^ 32
  ns : L.seed.toNat + 32 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
  tfit : L.T.toNat + 98304 ≤ 2 ^ 32
  tout : L.TB.Disjoint L.OUT
  tscr : L.TB.Disjoint L.SCR
  tstk : L.TB.Disjoint L.STK
end Lay

/-- The comb's tables at `L.T` in `m`. -/
def Tbl (L : Lay) (m : Mem) : Prop :=
  ∀ j < 64 * 192, m.readW (State.addr L.T + BitVec.ofNat 64 (8 * j)) 64 = VG.Impl.Ed25519.Arm.combWord j

abbrev Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 3, m.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 = L.value j

def argValue (L : Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem frame_sub (L : Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 248 ≤ 280)
theorem args_sub (L : Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 248 + 24 ≤ 280)

theorem Ctx.seed_bytes (hc : Ctx L g m₀ t) (hL : L.Ok) :
    Spec.Ed25519.bytesAt t.mem (State.addr L.seed) 32 = Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := L.SEED) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (frame_sub L)).symm

theorem Ctx.arg_word (hc : Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 3) :
    t.mem.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS)
    (Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.ko.sub_left (args_sub L)
  · exact hL.kc.sub_left (args_sub L)
  · exact Offset.disjoint_base _ (by decide : 248 ≤ 248) (by decide : 248 + 24 ≤ 2 ^ 64)

theorem value_eq (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (v : Value) (hi : ∀ j d, v = .caller j d → j < 3) : Whole.value L.E t.mem v = argValue L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    simp only [Whole.value, argValue]
    rw [hc.arg_word hL (hi j d rfl), ha j (hi j d rfl)]

theorem setup_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} {stk : List Value} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3)
    (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, Whole.valid v)
    (his : ∀ v ∈ stk, ∀ j d, v = .caller j d → j < 3) :
    WP isa (.block (setup args stk)) t fun u => Ctx L g m₀ u ∧
      Frame [⟨State.addr L.E, 24⟩] t.mem u.mem ∧
      (∀ p ∈ args, u.gpr p.1 = argValue L p.2) ∧
      (∀ j (hj : j < stk.length), stackArg u j = argValue L (stk[j]'hj)) := by
  refine WP.mono (hc.setup hL.top hn hv hs hvs (by simp [Lay.inputs]) hr)
    fun u ⟨hu, hm, hregs, hstk⟩ => ⟨hu, hm, ?_, ?_⟩
  · intro p hp
    rw [hregs p hp, value_eq hc hL ha _ (hi p hp)]
  · intro j hj
    rw [hstk j hj, value_eq hc hL ha _ (his _ (List.getElem_mem hj))]

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Hash`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey
open VG.Impl.Ed25519.Arm.Whole (callWith)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem setup_repr (hL : L.Ok) {u : State} (hf : Frame [⟨State.addr L.E, 24⟩] t.mem u.mem)
    {msg : List Byte} (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr L.scr) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := t.mem) ?_ hh
  intro i hi
  refine hf.bytes (R := Whole.SHA L.scr) ?_ (by change 192 ≤ 2 ^ 64; decide) hi
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact ((hL.kc.sub_left (Region.sub_prefix (by decide : 24 ≤ 280))).sub_right (Whole.sha_sub L.scr)).symm

theorem init_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith initArgs Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512)) t
      fun u => Ctx L g m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr L.scr) [] := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := [(.r0, .caller 2 0)]) (stk := [])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, _, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact WP.mono (Whole.init_call hu (Whole.init_pre h0 hL.nc) (Whole.covers_writes hw) hw h0)
    fun v ⟨hv, _, hh⟩ => ⟨hv, hh⟩

theorem update_covers (L : Lay) : Covers (Whole.updateRd L.E L.seed 32 ++ Whole.hashWr L.scr)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨L.SEED, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by change 0 + (32#32).toNat ≤ 32; decide⟩
  · exact ⟨L.FR, by simp, 0, (BitVec.add_zero _).symm, by change 0 + 12 ≤ 248; decide⟩
  · exact ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 192 ≤ 8192; decide⟩
  · exact ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192 + 272 ≤ 8192; decide⟩

theorem update_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr) []) :
    WP isa (callWith updateArgs "vg_sha512_update_scratch" Impl.Sha512.Arm.Stream.update) t fun u =>
      Ctx L g m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr L.scr)
        (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.r0, .caller 2 0), (.r2, .const 0), (.r3, .const 0)])
    (stk := [.caller 1 0, .const 32, .caller 2 192])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp [Whole.valid]) (by simp)) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp)
  have h2 := hs (.r2, .const 0) (by simp)
  have h3 := hs (.r3, .const 0) (by simp)
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  have a2 := st 2 (by decide)
  simp only [argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h2 h3 a0 a1 a2
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  have hp := Whole.update_pre hu.sp h0 a0 a1 a2 hL.sc
    (hL.kc.sub_left (Region.sub_prefix (by decide : 12 ≤ 280))) hL.nc hL.ns
    (by have := hL.top; omega)
  have count : Proof.Sha512.countArm u = BitVec.ofNat 64 ([] : List Byte).length := by
    rw [Proof.Sha512.countArm, h2, h3]
    rfl
  refine WP.mono (Whole.update_call hu hp (update_covers L) hw h0 a0 a1 count (setup_repr hL hm hh))
    fun u' ⟨hu', _, hr⟩ => ⟨hu', ?_⟩
  change Spec.Sha512.Repr _ u'.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (State.addr L.seed) 32) at hr
  rw [List.nil_append, hu.seed_bytes hL] at hr
  exact hr

theorem digest_addr (hL : L.Ok) : State.addr (L.E + 184) = State.addr L.E + 184 :=
  addr_add (k := 184) (by have := hL.top; omega)

theorem finalize_writes (hL : L.Ok) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 184),
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 192 ≤ 8192; decide⟩
  · exact .inl ⟨184, digest_addr hL, by change 184 + 64 ≤ 248; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192 + 272 ≤ 8192; decide⟩

theorem finalize_covers (hL : L.Ok) :
    Covers (Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 184))
      (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  intro a n ⟨r, hr, hh⟩
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr] at hh
    exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, by
      change (a - State.addr L.E).toNat + n ≤ 248
      change (a - State.addr L.E).toNat + n ≤ 8 at hh
      omega⟩
  · exact Whole.covers_writes (finalize_writes hL) a n ⟨r, hr, hh⟩

theorem finalize_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
      (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)) :
    WP isa (callWith finalizeArgs "vg_sha512_finalize_scratch" Impl.Sha512.Arm.Stream.finalize) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.r0, .caller 2 0), (.r2, .const 32), (.r3, .const 0)])
    (stk := [.frame 184, .caller 2 192])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp [Whole.valid]) (by simp)) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp)
  have h2 := hs (.r2, .const 32) (by simp)
  have h3 := hs (.r3, .const 0) (by simp)
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  simp only [argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h2 h3 a0 a1
  have hd : Region.Disjoint ⟨State.addr (L.E + 184), 64⟩ L.SCR := by
    rw [digest_addr hL]
    exact hL.kc.sub_left (Offset.sub_base _ (by decide : 184 + 64 ≤ 280))
  have ds : (Whole.CALLARGS L.E 8).Disjoint ⟨State.addr (L.E + 184), 64⟩ := by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have nf : (L.E + 184).toNat + 64 ≤ 2 ^ 32 := by
    have ht := hL.top
    rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 184 < 2 ^ 32; omega)]
    change L.E.toNat + 184 + 64 ≤ 2 ^ 32
    omega
  have hp := Whole.finalize_pre hu.sp h0 a0 a1 hd
    (hL.kc.sub_left (Region.sub_prefix (by decide : 8 ≤ 280))) ds hL.nc nf
    (by have := hL.top; omega)
  have hl : (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  have count : Proof.Sha512.countArm u = BitVec.ofNat 64 (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32).length := by
    rw [hl, Proof.Sha512.countArm, h2, h3]
    rfl
  refine WP.mono (Whole.finalize_call hu hp (finalize_covers hL) (finalize_writes hL) h0 a0 count
    (setup_repr hL hm hh) (by rw [hl]; decide)) fun u' ⟨hu', _, hd⟩ => ⟨hu', ?_⟩
  rw [addr_add (k := 184) (by have := hL.top; omega)] at hd
  exact hd

theorem hash_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hash t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  exact WP.seq (WP.mono (init_step hc hL ha) fun t₁ ⟨h₁, hh₁⟩ =>
    WP.seq (WP.mono (update_step h₁ hL ha hh₁) fun t₂ ⟨h₂, hh₂⟩ => finalize_step h₂ hL ha hh₂))

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Base`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey
open VG.Impl.Ed25519.Arm.Whole (callWith)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem base_noFrames : Impl.Ed25519.Arm.scalarBase.noFrames = true := by lit_decide

def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .r0 = L.out ∧ t.gpr .r1 = L.E + 24 ∧ t.gpr .r2 = L.scr

theorem scalar_addr (hL : L.Ok) : State.addr (L.E + 24) = State.addr L.E + 24 :=
  addr_add (k := 24) (by have := hL.top; omega)

theorem base_pre (hL : L.Ok) (ha : BaseArgs L t) (hsy : t.syms VG.Impl.Ed25519.Arm.combSym = L.T)
    (hw : Tbl L t.mem) :
    scalarBaseLocal.pre (t.callEntry.withRegions [⟨State.addr L.E + 24, 32⟩, L.TB] L.outputs) := by
  obtain ⟨h0, h1, h2⟩ := ha
  have sy : (t.callEntry.withRegions [⟨State.addr L.E + 24, 32⟩, L.TB] L.outputs).syms
      VG.Impl.Ed25519.Arm.combSym = L.T := hsy
  simp only [scalarBaseLocal, sy, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, scalar_addr hL]
  refine ⟨True.intro, rfl, (hL.ko.sub_left (Offset.sub_base _ (by decide : 24 + 32 ≤ 280))).symm,
    hL.oc, hL.kc.sub_left (Offset.sub_base _ (by decide : 24 + 32 ≤ 280)), hL.no, ?_, hL.nc, hL.tfit, hw,
    hL.tout, hL.tscr⟩
  have h := hL.top
  rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 24 < 2 ^ 32; omega)]
  change L.E.toNat + 24 + 32 ≤ 2 ^ 32
  omega

theorem base_covers (L : Lay) : Covers ([⟨State.addr L.E + 24, 32⟩, L.TB] ++ L.outputs)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Whole.FR L.E, List.mem_append_right _ List.mem_cons_self, 24, rfl, by change 24 + 32 ≤ 248; decide⟩
    · exact ⟨L.TB, by simp [Lay.inputs], 0, by simp⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

/-- The tables in a memory the body leaves them in. -/
theorem Ctx.tbl (hc : Ctx L g m₀ t) (hL : L.Ok) (hw : Tbl L m₀) : Tbl L t.mem := fun j hj => by
  rw [← hw j hj]
  refine hc.frame.readW (r := L.TB) (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.tout
  · exact hL.tscr
  · exact hL.tstk.sub_right (frame_sub L)

theorem base_writes (L : Lay) : ∀ r ∈ L.outputs,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_call (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : BaseArgs L t)
    (hsy : t.syms VG.Impl.Ed25519.Arm.combSym = L.T) (hw : Tbl L t.mem) :
    WP isa (.call "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32) := by
  refine Whole.call_ok hc scalarBase_ok base_noFrames (base_pre hL ha hsy hw) (base_covers L)
    (base_writes L) fun u hu _ hp => ⟨hu, ?_⟩
  change Spec.Ed25519.bytesAt u.mem (State.addr (t.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (State.addr (t.callEntry.gpr .r1)) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1, scalar_addr hL] at hp
  exact hp

theorem prune_step (hc : Ctx L g m₀ t) (hL : L.Ok) {digest : List Byte}
    (hh : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 = digest) :
    WP isa (.block prune) t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32) = Spec.Ed25519.prune digest := by
  have hwrite : (⟨State.addr L.E, 248⟩ : Region) ∈ t.wr := by rw [hc.wr]; exact List.mem_cons_self
  refine WP.mono (prune_ok hc.sp (by have := hL.top; omega) hwrite hh) fun u ⟨hu, hf, hp⟩ => ⟨?_, hp⟩
  refine hc.of_frame hu.rd hu.wr hu.sp ?_ hf ?_
  · intro r hr _
    apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
  · rintro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 24 + 32 ≤ 248))

theorem base_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) (hw : Tbl L m₀)
    (hsy : t.syms VG.Impl.Ed25519.Arm.combSym = L.T) {n : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32) = n) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono_syms (setup_ok hc hL ha
    (args := [(.r0, .caller 0 0), (.r1, .frame 24), (.r2, .caller 2 0)]) (stk := [])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, hm, hav, _⟩ syu => ?_)
  have h0 := hav (.r0, .caller 0 0) (by simp)
  have h1 := hav (.r1, .frame 24) (by simp)
  have h2 := hav (.r2, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have he : Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32 =
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hm.bytes (R := ⟨State.addr L.E + 24, 32⟩) ?_
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine WP.mono (base_call hu hL ⟨h0, h1, h2⟩ (by rw [syu]; exact hsy) (hu.tbl hL hw))
    fun u' ⟨hu', hp⟩ => ⟨hu', ?_⟩
  rw [hp, he, Spec.Ed25519.scalarBase, hs]

theorem wipe_step (hc : Ctx L g m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 = Spec.Ed25519.bytesAt t.mem (State.addr L.out) 32 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 6) (count := 56) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 4 * 6 + 4 * 56 ≤ 280))).symm

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Entry`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm

def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let scr : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    let tb : Region := TBL (s.syms VG.Impl.Ed25519.Arm.combSym)
    s.rd = [seed, tb] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧
      (s.syms VG.Impl.Ed25519.Arm.combSym).toNat + 98304 ≤ 2 ^ 32 ∧
      (∀ j < 64 * 192, s.mem.readW (State.addr (s.syms VG.Impl.Ed25519.Arm.combSym) +
        BitVec.ofNat 64 (8 * j)) 64 = VG.Impl.Ed25519.Arm.combWord j) ∧
      tb.Disjoint out ∧ tb.Disjoint scr ∧ tb.Disjoint stk
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.syms VG.Impl.Ed25519.Arm.combSym = t.syms VG.Impl.Ed25519.Arm.combSym

def lay (s : State) : Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, Whole.base s, s.syms VG.Impl.Ed25519.Arm.combSym⟩

theorem lay_ok {s : State} (h : pkLocal.pre s) : (lay s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hb, tf, _, tout, tscr, tstk⟩ := h
  have he := Whole.base_addr hb
  have top := Whole.base_top hb
  have hs := s.sp.isLt
  refine ⟨by change (Whole.base s).toNat + 272 ≤ 2 ^ 32; omega, os, oc, sc, ?_, ?_, ?_, no, ns, nc,
    tf, tout, tscr, ?_⟩
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact ko
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact ks
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact kc
  · change Region.Disjoint _ (⟨State.addr (Whole.base s), 280⟩ : Region)
    rw [he]; exact tstk

theorem entry_below {s : State} (h : pkLocal.pre s) : 280 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.1

/-- The tables at the body's entry. -/
theorem entry_tbl {s p : State} (h : pkLocal.pre s) (hp : Whole.Saved (Whole.entered s) 3 p) :
    Tbl (lay s) p.mem := fun j hj => by
  have hf := Whole.saved_frame (entry_below h) hp
  have hw := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  rw [← hw]
  refine hf.readW (r := TBL (s.syms VG.Impl.Ed25519.Arm.combSym))
    (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)
  intro r hr
  rw [List.mem_singleton.mp hr]
  change Region.Disjoint _ (⟨State.addr (Whole.base s), 280⟩ : Region)
  rw [Whole.base_addr (entry_below h)]
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem entry_writes {s : State} (h : pkLocal.pre s) :
    ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (lay_ok h).ko
  · exact (lay_ok h).kc

theorem entry_ctx {s p : State} (h : pkLocal.pre s) (hp : Whole.Saved (Whole.entered s) 3 p) :
    Ctx (lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, Lay.TB, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hs : 280 ≤ s.sp.toNat) (hp : Whole.Saved (Whole.entered s) 3 p) : Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hs (by decide : 3 ≤ 6)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt) hp hj
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases he with rfl | rfl | rfl <;> exact hw

abbrev pkSpec : Contract isa :=
  Spec.Ed25519.publicKeyContract (Arm.abi.withConsts VG.Impl.Ed25519.Arm.combConsts) 280

theorem pk_pre {s : State} (h : pkSpec.pre s) : pkLocal.pre s := by
  have hp : (Spec.Ed25519.publicKeyContract Arm.abi 280).pre (stripConsts VG.Impl.Ed25519.Arm.combConsts s) ∧
      ConstsOk VG.Impl.Ed25519.Arm.combConsts 280 s := pre_consts.mp h
  have h1 := hp.1
  sig_pre [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
    stackBelow] at h1
  obtain ⟨hb, _, rd, wr, os, oc, sc, ko, ks, kc, no, ns, nc⟩ := h1
  have hk := hp.2
  have mem : (VG.Impl.Ed25519.Arm.combSym, VG.Impl.Ed25519.Arm.combWords) ∈
      VG.Impl.Ed25519.Arm.combConsts := List.mem_singleton_self _
  have fit := hk.fit mem
  rw [combWords_length] at fit
  have ht := hk.2.2.1 _ (by rw [combConsts_regs]; exact List.mem_singleton_self _)
  refine ⟨?_, wr, os, oc, sc, ko, ks, kc, no, ns, nc, hb, fit, fun j hj => ?_,
    ht.2.1 _ (by rw [wr]; exact List.mem_cons_self),
    ht.2.1 _ (by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self),
    ht.2.2 _ (by simp [Arm.abi, stackBelow])⟩
  · have e1 := hk.1
    rw [combConsts_regs] at e1
    have hl : VG.Impl.Ed25519.Arm.combConsts.length = 1 := rfl
    rw [hl] at e1
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, e1, rd, List.singleton_append]
    rfl
  · have hw := hk.2.1 _ mem j (by rw [combWords_length]; exact hj)
    dsimp only at hw
    rw [combWords_getD hj] at hw
    exact hw

def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := baseSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x100000, 98304⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

theorem pk_sat : pkSpec.pre satState := by
  have held := baseSatMem_held
  generalize eqs : satState = s
  sig_pre [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  rw [combWords_length]
  rw [combWords_length] at held
  refine ⟨by decide, by decide, by decide, held, by decide, ?_, Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide, by decide, by decide⟩
  intro r hr
  change r ∈ [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem pk_implies : pkLocal.Implies pkSpec where
  pre _ h := pk_pre h
  post := by
    intro s s' _ h
    sig_post [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig, Spec.Ed25519.scratchWords,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig, Spec.Ed25519.scratchWords,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, combConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨satState, pk_sat⟩

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem body_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) (hw : Tbl L m₀)
    (hsy : t.syms VG.Impl.Ed25519.Arm.combSym = L.T) :
    WP isa body t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  refine WP.seq (WP.mono_syms (hash_ok hc hL ha) fun u ⟨hu, hh⟩ syu => ?_)
  refine WP.seq (WP.mono_syms (prune_step hu hL hh) fun u' ⟨hu', hs⟩ syu' => ?_)
  refine WP.seq (WP.mono (base_step hu' hL ha hw (by rw [syu', syu]; exact hsy) hs)
    fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

theorem body_noFrames : body.noFrames = true := by
  simp only [body, Impl.Ed25519.Arm.PublicKey.hash, Impl.Ed25519.Arm.Whole.callWith, Code.noFrames,
    Impl.Sha512.Arm.Stream.init, Bool.and_self]
  rw [base_noFrames]
  rfl

theorem publicKey_ok {s : State} (h : pkLocal.pre s) :
    WP isa code s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := Whole.wrap_ok body_noFrames (by decide : 3 ≤ 6) (entry_below h)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt)
    (by intro j hj h4; omega) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (State.addr (s.gpr .r0)) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 32))
    (fun p hp => WP.mono (body_ok (entry_ctx h hp) (lay_ok h) (entry_args (entry_below h) hp)
      (entry_tbl h hp) (congrFun hp.step.syms _))
      fun u ⟨hu, ho⟩ => ⟨by
        simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
          Lay.SCR, Lay.ARGS, Lay.TB, lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 32 =
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨State.addr (s.gpr .r1), 32⟩) ?_
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r0)) 32 = _
  rw [hp, hs]

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.CT`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PublicKey.CTReady`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PublicKey.CTCommon`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

abbrev Two (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) := (Ctx L g₁ m₁ a ∧ P a) ∧ (Ctx L g₂ m₂ b ∧ P b)

def Slots (L : Lay) (args : List (Reg × Value)) (stk : List Value) (s : State) :=
  (∀ p ∈ args, s.gpr p.1 = argValue L p.2) ∧ ∀ j (hj : j < stk.length), stackArg s j = argValue L (stk[j]'hj)

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, Whole.valid v)
    (his : ∀ v ∈ stk, ∀ j d, v = .caller j d → j < 3) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stk))
      (Two L g₁ g₂ m₁ m₂ (Slots L args stk)) := by
  refine Whole.rel_wp ((Whole.setup_ct args stk).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL ha hn hv hi hr hs hvs his) fun _ ⟨hc, _, hg, ht⟩ => ⟨hc, hg, ht⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL hb hn hv hi hr hs hvs his) fun _ ⟨hc, _, hg, ht⟩ => ⟨hc, hg, ht⟩

theorem call_ct {args : List (Reg × Value)} {stk : List Value} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hn : c.noFrames = true)
    (ready : ∀ t, t.sp = L.E → Slots L args stk t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      (∀ j < stk.length, stackArg a j = stackArg b j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L args stk)) (.call name c)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
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

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

def initValues : List (Reg × Value) := [(.r0, .caller 2 0)]
def updateValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r2, .const 0), (.r3, .const 0)]
def updateStack : List Value := [.caller 1 0, .const 32, .caller 2 192]
def finalizeValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r2, .const 32), (.r3, .const 0)]
def finalizeStack : List Value := [.frame 184, .caller 2 192]
def baseValues : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .frame 24), (.r2, .caller 2 0)]

variable {L : Lay} {t : State}

def init_ready (hL : L.Ok) (hs : Slots L initValues [] t) :
    Whole.CallReady (Proof.Sha512.initArm Spec.Sha512.H0_512) L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [initValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre h0 hL.nc, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (he : t.sp = L.E) (hs : Slots L updateValues updateStack t) :
    Whole.CallReady Proof.Sha512.updateArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [updateValues])
  have a0 := hs.2 0 (by decide)
  have a1 := hs.2 1 (by decide)
  have a2 := hs.2 2 (by decide)
  simp only [updateStack, argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 a0 a1 a2
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd L.E L.seed 32, Whole.hashWr L.scr,
    Whole.update_pre he h0 a0 a1 a2 hL.sc
      (hL.kc.sub_left (Region.sub_prefix (by decide : 12 ≤ 280))) hL.nc hL.ns
      (by have := hL.top; omega), update_covers L, hw⟩

def finalize_ready (hL : L.Ok) (he : t.sp = L.E) (hs : Slots L finalizeValues finalizeStack t) :
    Whole.CallReady Proof.Sha512.finalizeArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [finalizeValues])
  have a0 := hs.2 0 (by decide)
  have a1 := hs.2 1 (by decide)
  simp only [finalizeStack, argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 a0 a1
  have hd : Region.Disjoint ⟨State.addr (L.E + 184), 64⟩ L.SCR := by
    rw [digest_addr hL]
    exact hL.kc.sub_left (Offset.sub_base _ (by decide : 184 + 64 ≤ 280))
  have ds : (Whole.CALLARGS L.E 8).Disjoint ⟨State.addr (L.E + 184), 64⟩ := by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have nf : (L.E + 184).toNat + 64 ≤ 2 ^ 32 := by
    have ht := hL.top
    rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 184 < 2 ^ 32; omega)]
    change L.E.toNat + 184 + 64 ≤ 2 ^ 32
    omega
  exact ⟨Whole.finalizeRd L.E, Whole.finalizeWr L.scr (L.E + 184),
    Whole.finalize_pre he h0 a0 a1 hd
      (hL.kc.sub_left (Region.sub_prefix (by decide : 8 ≤ 280))) ds hL.nc nf
      (by have := hL.top; omega), finalize_covers hL, finalize_writes hL⟩

/-- What the call of `vg_ed25519_scalar_base` needs besides its arguments: the tables' address
and words. -/
def BaseReady (L : Lay) (t : State) : Prop :=
  Slots L baseValues [] t ∧ t.syms VG.Impl.Ed25519.Arm.combSym = L.T ∧ Tbl L t.mem

def base_ready (hL : L.Ok) (hs : BaseReady L t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs.1.1 (.r0, .caller 0 0) (by simp [baseValues])
  have h1 := hs.1.1 (.r1, .frame 24) (by simp [baseValues])
  have h2 := hs.1.1 (.r2, .caller 2 0) (by simp [baseValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨State.addr L.E + 24, 32⟩, L.TB], L.outputs, base_pre hL ⟨h0, h1, h2⟩ hs.2.1 hs.2.2,
    base_covers L, base_writes L⟩

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L initValues []))
    (.call Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512)) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.Arm.Stream.init_verified _).1
    (Proof.Sha512.Arm.Stream.init_verified _).2.1 rfl (fun _ _ h => init_ready hL h)
  · intro a b ar aw br bw hsp hg ht
    exact hg (.r0, .caller 2 0) (by simp [initValues])
  · simp [initValues, linkRegs]

theorem update_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L updateValues updateStack))
    (.call "vg_sha512_update_scratch" Impl.Sha512.Arm.Stream.update) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Update.update_verified.1 Proof.Sha512.Arm.Stream.Update.update_verified.2.1
    Whole.update_noFrames (fun _ he h => update_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [updateValues]), hg (.r2, .const 0) (by simp [updateValues]), hg (.r3, .const 0) (by simp [updateValues]), ht 0 (by decide), ht 1 (by decide), ht 2 (by decide)⟩
  · simp [updateValues, linkRegs]

theorem finalize_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L finalizeValues finalizeStack))
    (.call "vg_sha512_finalize_scratch" Impl.Sha512.Arm.Stream.finalize) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Finalize.finalize_verified.1 Proof.Sha512.Arm.Stream.Finalize.finalize_verified.2.1
    Whole.finalize_noFrames (fun _ he h => finalize_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [finalizeValues]), hg (.r2, .const 32) (by simp [finalizeValues]), hg (.r3, .const 0) (by simp [finalizeValues]), ht 0 (by decide), ht 1 (by decide)⟩
  · simp [finalizeValues, linkRegs]

theorem base_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (BaseReady L))
    (.call "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ?_ ?_ ?_
  · refine Whole.callEx scalarBase_ok scalarBase_ct fun a b h => ?_
    let ra := base_ready hL h.1.2
    let rb := base_ready hL h.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    have hg : ∀ p ∈ baseValues, a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := fun p hp => by
      have hl : p.1 ∉ linkRegs := by simp only [baseValues, List.mem_cons, List.not_mem_nil, or_false] at hp
                                     rcases hp with rfl | rfl | rfl <;> decide
      rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl, h.1.2.1.1 p hp, h.2.2.1.1 p hp]
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      ⟨h.1.1.sp.trans h.2.1.sp.symm, hg (.r0, .caller 0 0) (by simp [baseValues]),
        hg (.r1, .frame 24) (by simp [baseValues]), hg (.r2, .caller 2 0) (by simp [baseValues]),
        h.1.2.2.1.trans h.2.2.2.1.symm⟩, ca, wa, cb, wb⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((base_ready hL hs).wp hc scalarBase_ok base_noFrames) fun _ hu => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((base_ready hL hs).wp hc scalarBase_ok base_noFrames) fun _ hu => ⟨hu, trivial⟩

theorem prune_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block prune)
    (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (prune_sp_ct.mono (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
    (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc hL (digest := Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc hL (digest := Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ((Whole.zeroWords_ct 6 56).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (hw₁ : Tbl L m₁)
    (hw₂ : Tbl L m₂) :
    RelCT isa (fun a b => Two L g₁ g₂ m₁ m₂ (fun _ => True) a b ∧
      a.syms VG.Impl.Ed25519.Arm.combSym = L.T ∧ b.syms VG.Impl.Ed25519.Arm.combSym = L.T)
      body (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have i := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb initValues []
    (by decide) (by simp [initValues, Whole.valid]) (by simp [initValues])
    (by simp [initValues, preserved]) (by decide) (by simp [Whole.valid])
    (by simp)
  have u := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb updateValues updateStack
    (by decide) (by simp [updateValues, Whole.valid]) (by simp [updateValues])
    (by simp [updateValues, preserved]) (by decide) (by simp [updateStack, Whole.valid])
    (by simp [updateStack])
  have f := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb finalizeValues finalizeStack
    (by decide) (by simp [finalizeValues, Whole.valid]) (by simp [finalizeValues])
    (by simp [finalizeValues, preserved]) (by decide) (by simp [finalizeStack, Whole.valid])
    (by simp [finalizeStack])
  have b := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb baseValues []
    (by decide) (by simp [baseValues, Whole.valid]) (by simp [baseValues])
    (by simp [baseValues, preserved]) (by decide) (by simp [Whole.valid])
    (by simp)
  have bc : RelCT isa (fun a b => Two L g₁ g₂ m₁ m₂ (Slots L baseValues []) a b ∧
      a.syms VG.Impl.Ed25519.Arm.combSym = L.T ∧ b.syms VG.Impl.Ed25519.Arm.combSym = L.T)
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase) (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
    (base_ct hL).mono (fun a b ⟨⟨⟨hca, hsa⟩, ⟨hcb, hsb⟩⟩, sa, sb⟩ =>
      ⟨⟨hca, hsa, sa, hca.tbl hL hw₁⟩, ⟨hcb, hsb, sb, hcb.tbl hL hw₂⟩⟩) fun _ _ h => h
  exact (Whole.keepSym VG.Impl.Ed25519.Arm.combSym L.T ((i.seq (init_ct hL)).seq ((u.seq (update_ct hL)).seq (f.seq (finalize_ct hL))))).seq
    ((Whole.keepSym VG.Impl.Ed25519.Arm.combSym L.T (prune_ct hL)).seq (((Whole.keepSym VG.Impl.Ed25519.Arm.combSym L.T b).seq bc).seq (wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, hy⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, hy]

theorem publicKey_ct : ConstantTime isa pkLocal.pre pkLocal.pub code := by
  refine Whole.wrap_ct (by decide : 3 ≤ 6) (fun _ _ hp => hp.1)
    (fun _ hs => entry_below hs) ?_ (by intro s hs j hj h4; omega) ?_ ?_
  · intro s _
    simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_of_lt s.sp.isLt
  · intro s hs p hp
    exact WP.mono (body_ok (entry_ctx hs hp) (lay_ok hs) (entry_args (entry_below hs) hp)
      (entry_tbl hs hp) (congrFun hp.step.syms _)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args (entry_below ht) hqb
    have hqw : Tbl (lay s) q.mem := he ▸ entry_tbl ht hqb
    have hqy : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms VG.Impl.Ed25519.Arm.combSym =
        (lay s).T := (congrFun hqb.step.syms _).trans hp.2.2.2.2.symm
    exact ⟨(body_ct (lay_ok hs) (entry_args (entry_below hs) hpa) hqa (entry_tbl hs hpa) hqw _ _ _ _ _ _
      ⟨⟨⟨entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩, congrFun hpa.step.syms _, hqy⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

theorem publicKey_verified :
    Verified Arm.target code pkSpec :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => publicKey_ok h) publicKey_ct (.refl pk_implies.sat_left))
    pk_implies

end VG.Proof.Ed25519.Arm.PublicKey
