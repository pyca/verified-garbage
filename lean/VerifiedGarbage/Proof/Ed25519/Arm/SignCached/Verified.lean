import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddVerified
import VerifiedGarbage.Proof.Sha512.Scratch
import VerifiedGarbage.Impl.Ed25519.Arm.SignCached
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Impl.Ed25519.Arm.SignCached.Prefix
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Verified
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Spec.Ed25519.CachedSign
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Layout`. -/
section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm

structure Lay where
  out : BitVec 32
  seed : BitVec 32
  pk : BitVec 32
  msg : BitVec 32
  len : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : VG.Proof.Ed25519.Arm.SignCached.Lay)
abbrev OUT : Region := ⟨State.addr L.out, 64⟩
abbrev SEED : Region := ⟨State.addr L.seed, 32⟩
abbrev PK : Region := ⟨State.addr L.pk, 32⟩
abbrev MSG : Region := ⟨State.addr L.msg, L.len.toNat⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
abbrev ORIGINALARGS : Region := ⟨State.addr L.E + BitVec.ofNat 64 280, 8⟩
abbrev ARGS : Region := ⟨State.addr L.E + BitVec.ofNat 64 248, 24⟩
abbrev FR : Region := Whole.FR L.E
def inputs : List Region := [L.SEED, L.PK, L.MSG, L.ORIGINALARGS, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : BitVec 32 :=
  match j with | 0 => L.out | 1 => L.seed | 2 => L.pk | 3 => L.msg | 4 => L.len | _ => L.scr

structure Ok : Prop where
  top : L.E.toNat + 272 ≤ 2 ^ 32
  os : ∀ r ∈ L.inputs, L.OUT.Disjoint r
  oc : L.OUT.Disjoint L.SCR
  ko : L.FR.Disjoint L.OUT
  no : L.out.toNat + 64 ≤ 2 ^ 32
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.FR.Disjoint r
  kc : L.FR.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 32
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  ns : L.seed.toNat + 32 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

/-- The scratch allocation leaves enough address space for either hash prefix. -/
theorem Lay.Ok.message_bound {L : VG.Proof.Ed25519.Arm.SignCached.Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 32 := by
  have hd := h.sc L.MSG (by simp [Lay.inputs])
  have nm := h.nm
  have nc := h.nc
  have ap : (State.addr L.msg).toNat = L.msg.toNat := BitVec.toNat_setWidth_of_le (by decide)
  have ac : (State.addr L.scr).toNat = L.scr.toNat := BitVec.toNat_setWidth_of_le (by decide)
  by_cases hz : L.len.toNat = 0
  · omega
  by_cases hp : State.addr L.msg ≤ State.addr L.scr
  · have hn : ¬ L.MSG.Contains (State.addr L.scr) 1 := fun hx => hd _ hx (by simp [Region.Contains])
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp] at hn
    have hp' : (State.addr L.msg).toNat ≤ (State.addr L.scr).toNat := hp
    rw [ap, ac] at hn hp'
    omega
  · have hp' : State.addr L.scr ≤ State.addr L.msg := by
      change (State.addr L.scr).toNat ≤ (State.addr L.msg).toNat
      change ¬ (State.addr L.msg).toNat ≤ (State.addr L.scr).toNat at hp
      omega
    have hn : ¬ L.SCR.Contains (State.addr L.msg) 1 := fun hx => hd _ (by simp [Region.Contains]; omega) hx
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp'] at hn
    have hp'' : (State.addr L.scr).toNat ≤ (State.addr L.msg).toNat := hp'
    rw [ap, ac] at hn hp''
    omega


abbrev Ctx (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

namespace Ctx
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem input_bytes (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok)
    {r : Region} (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem r.base r.len = Spec.Ed25519.bytesAt m₀ r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine Frame.bytes hc.frame ?_ hn (List.mem_range.mp hi)
  intro R hR
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact (hL.os r hr).symm
  · exact hL.sc r hr
  · exact (hL.ks r hr).symm

theorem arg_word (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 6) :
    t.mem.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl | rfl
    · exact (hL.os _ ha).symm
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm

end Ctx
end VG.Proof.Ed25519.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Args`. -/
section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def Arguments (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (m : Mem) : Prop :=
  ∀ j < 6, m.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 = L.value j

def value (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

def OutArgs (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (args : List (Reg × Value)) (s : State) : Prop :=
  ∀ p ∈ args, s.gpr p.1 = VG.Proof.Ed25519.Arm.SignCached.value L p.2

def StackArgs (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (vs : List Value) (s : State) : Prop :=
  ∀ j (hj : j < vs.length), stackArg s j = VG.Proof.Ed25519.Arm.SignCached.value L (vs[j]'hj)

theorem Ctx.value (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀) {v : Value} (hv : Whole.valid v) :
    Whole.value L.E s.mem v = VG.Proof.Ed25519.Arm.SignCached.value L v := by
  cases v with
  | const n => rfl
  | frame d => rfl
  | caller j d =>
    change _ + BitVec.ofNat 32 d = _ + BitVec.ofNat 32 d
    rw [hc.arg_word hL hv.1, ha j hv.1]

theorem args_regs_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (VG.Impl.Ed25519.Arm.Whole.setup args [])) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ t.mem = s.mem ∧ VG.Proof.Ed25519.Arm.SignCached.OutArgs L args t := by
  have rd : ∀ j < 6, InRegions (s.rd ++ s.wr) (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 4 := by
    intro j hj
    refine ⟨L.ARGS, ?_, Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)⟩
    rw [hc.rd]
    exact List.mem_append_left _ (by simp [Lay.inputs])
  refine WP.mono (Whole.setupRegs_ok hc.sp hL.top hn hv rd) fun t ⟨ht, hargs⟩ => ?_
  refine ⟨hc.regs ht.rd ht.wr ht.sp ?_ ht.mem, ht.mem, ?_⟩
  · intro r hpres _
    apply ht.regs
    intro hh
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hh
    exact hr p hp (he ▸ hpres)
  · intro p hp
    exact (hargs p hp).trans (hc.value hL ha (hv p hp))

theorem args_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀)
    {args : List (Reg × Value)} {stack : List Value}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hs : stack.length ≤ 6) (hvs : ∀ v ∈ stack, Whole.valid v)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (VG.Impl.Ed25519.Arm.Whole.setup args stack)) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Frame [⟨State.addr L.E, 24⟩] s.mem t.mem ∧ VG.Proof.Ed25519.Arm.SignCached.OutArgs L args t ∧ VG.Proof.Ed25519.Arm.SignCached.StackArgs L stack t := by
  refine WP.mono (Whole.Ctx.setup hc hL.top hn hv hs hvs (by simp [Lay.inputs]) hr)
    fun t ⟨ht, hf, hg, hstack⟩ => ⟨ht, hf, ?_, ?_⟩
  · intro p hp
    exact (hg p hp).trans (hc.value hL ha (hv p hp))
  · intro j hj
    exact (hstack j hj).trans (hc.value hL ha (hvs _ (List.getElem_mem hj)))

end VG.Proof.Ed25519.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Calls`. -/
section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm

variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay}

def field (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (d : Nat) : Region := ⟨State.addr L.E + BitVec.ofNat 64 d, 32⟩
def digest (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Region := ⟨State.addr L.E + BitVec.ofNat 64 184, 64⟩
def baseOut (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Region := ⟨State.addr L.out, 32⟩
def half (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Region := ⟨State.addr L.out + BitVec.ofNat 64 32, 32⟩

theorem fieldWithin (L : VG.Proof.Ed25519.Arm.SignCached.Lay) {d : Nat} (hd : d + 32 ≤ 248) : Whole.Within (VG.Proof.Ed25519.Arm.SignCached.field L d) L.FR :=
  ⟨d, rfl, hd⟩
theorem digestWithin (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Whole.Within (VG.Proof.Ed25519.Arm.SignCached.digest L) L.FR := ⟨184, rfl, by change 184 + 64 ≤ 248; decide⟩
theorem baseWithin (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Whole.Within (VG.Proof.Ed25519.Arm.SignCached.baseOut L) L.OUT := ⟨0, by simp [VG.Proof.Ed25519.Arm.SignCached.baseOut], by change 0 + 32 ≤ 64; decide⟩
theorem halfWithin (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Whole.Within (VG.Proof.Ed25519.Arm.SignCached.half L) L.OUT := ⟨32, rfl, by change 32 + 32 ≤ 64; decide⟩
theorem scratchWithin (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩

theorem covers {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R) :
    Covers rs (L.inputs ++ L.FR :: L.outputs) := by
  apply Covers.of_sub
  intro r hr
  rcases h r hr with hf | ⟨R, hR, hsub⟩
  · exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, hf⟩
  · refine ⟨R, ?_, hsub⟩
    rcases List.mem_append.mp hR with hi | ho
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)

theorem scratch_covered (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within L.SCR R :=
  ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed25519.Arm.SignCached.scratchWithin L⟩

theorem output_covered {r : Region} (h : Whole.Within r L.OUT) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨L.OUT, by simp [Lay.outputs], h⟩

theorem writes {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ Whole.Within r L.OUT ∨ Whole.Within r L.SCR) :
    ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rcases h r hr with hf | ho | hs
  · exact .inl hf
  · exact .inr ⟨L.OUT, by simp [Lay.outputs], ho⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], hs⟩

theorem field_scr (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 248) :
    (VG.Proof.Ed25519.Arm.SignCached.field L d).Disjoint L.SCR := hL.kc.sub_left (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L hd).sub

theorem field_mem {m n : Mem} (hm : n = m) (d : Nat) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by rw [hm]

theorem frame_addr (hL : L.Ok) {d : Nat} (hd : d < 272) :
    State.addr (L.E + BitVec.ofNat 32 d) = State.addr L.E + BitVec.ofNat 64 d :=
  addr_add (by have := hL.top; omega)

theorem frame_fit (hL : L.Ok) {d n : Nat} (hd : d + n ≤ 248) :
    (L.E + BitVec.ofNat 32 d).toNat + n ≤ 2 ^ 32 := by
  have ht := hL.top
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : L.E.toNat + d < 2 ^ 32)]
  omega

end VG.Proof.Ed25519.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Base`. -/
section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
open VG.Impl.Ed25519.Arm (scalarBase)

def baseRd (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : List Region := [VG.Proof.Ed25519.Arm.SignCached.field L 88]
def baseWr (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : List Region := [VG.Proof.Ed25519.Arm.SignCached.baseOut L, L.SCR]
def BaseArgs (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (s : State) : Prop :=
  s.gpr .r0 = L.out ∧ s.gpr .r1 = L.E + 88 ∧ s.gpr .r2 = L.scr

theorem base_noFrames : scalarBase.noFrames = true := by lit_decide

variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem base_pre (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.BaseArgs L s) :
    scalarBaseLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.Arm.SignCached.baseRd L) (VG.Proof.Ed25519.Arm.SignCached.baseWr L)) := by
  have ae : State.addr (L.E + 88) = State.addr L.E + 88 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 88) (by decide)
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2, ae]
  exact ⟨rfl, rfl, (hL.ko.sub_right (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub).symm.sub_right (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by decide)).sub,
    hL.oc.sub_left (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub, VG.Proof.Ed25519.Arm.SignCached.field_scr hL (by decide),
    by have := hL.no; omega, VG.Proof.Ed25519.Arm.SignCached.frame_fit hL (by decide), hL.nc⟩

theorem base_call (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.BaseArgs L s) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.SignCached.baseWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 88) 32) := by
  have cov : Covers (VG.Proof.Ed25519.Arm.SignCached.baseRd L ++ VG.Proof.Ed25519.Arm.SignCached.baseWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.Arm.SignCached.covers
    simp only [VG.Proof.Ed25519.Arm.SignCached.baseRd, VG.Proof.Ed25519.Arm.SignCached.baseWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by decide))
    · exact .inr (VG.Proof.Ed25519.Arm.SignCached.output_covered (VG.Proof.Ed25519.Arm.SignCached.baseWithin L))
    · exact .inr (VG.Proof.Ed25519.Arm.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.Arm.SignCached.baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.Arm.SignCached.writes
    simp only [VG.Proof.Ed25519.Arm.SignCached.baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (VG.Proof.Ed25519.Arm.SignCached.baseWithin L))
    · exact .inr (.inr (VG.Proof.Ed25519.Arm.SignCached.scratchWithin L))
  refine Whole.call_ok hc scalarBase_ok VG.Proof.Ed25519.Arm.SignCached.base_noFrames (VG.Proof.Ed25519.Arm.SignCached.base_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (s.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1] at hp
  have ae : State.addr (L.E + 88) = State.addr L.E + 88 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 88) (by decide)
  rw [ae] at hp
  exact hp

end VG.Proof.Ed25519.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.HashFrame`. -/
section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay}

def slots (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Region := ⟨State.addr L.E, 24⟩
def hashWrites (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : List Region := [L.SCR, VG.Proof.Ed25519.Arm.SignCached.slots L, VG.Proof.Ed25519.Arm.SignCached.digest L]

theorem setup_frame {m n : Mem} (hf : Frame [VG.Proof.Ed25519.Arm.SignCached.slots L] m n) : Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) m n :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨VG.Proof.Ed25519.Arm.SignCached.slots L, by simp [VG.Proof.Ed25519.Arm.SignCached.hashWrites], fun _ h => h⟩

theorem hash_frame {m n : Mem} {rs : List Region} (hf : Frame rs m n)
    (hw : ∀ r ∈ rs, Whole.Within r L.SCR ∨ Whole.Within r (VG.Proof.Ed25519.Arm.SignCached.digest L)) : Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) m n := by
  refine hf.sub fun r hr => ?_
  rcases hw r hr with hc | hd
  · exact ⟨L.SCR, by simp [VG.Proof.Ed25519.Arm.SignCached.hashWrites], hc.sub⟩
  · exact ⟨VG.Proof.Ed25519.Arm.SignCached.digest L, by simp [VG.Proof.Ed25519.Arm.SignCached.hashWrites], hd.sub⟩

theorem frame_bytes {m n : Mem} {ws : List Region} (hf : Frame ws m n) (r : Region)
    (hd : ∀ w ∈ ws, r.Disjoint w) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt n r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem setup_field_bytes {m n : Mem} (hf : Frame [VG.Proof.Ed25519.Arm.SignCached.slots L] m n)
    {d : Nat} (hd : d + 32 ≤ 248) (hmin : 24 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf (VG.Proof.Ed25519.Arm.SignCached.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ hmin (by omega)

theorem setup_repr {m n : Mem} (hL : L.Ok) (hf : Frame [VG.Proof.Ed25519.Arm.SignCached.slots L] m n) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 m (State.addr L.scr) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 n (State.addr L.scr) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := m) ?_ hr
  intro i hi
  exact hf.bytes (R := ⟨State.addr L.scr, 192⟩) (by
    rintro r hm; rw [List.mem_singleton.mp hm]
    exact (hL.kc.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by decide)))
    (by change 192 ≤ 2 ^ 64; decide) hi

theorem hash_field_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) m n)
    {d : Nat} (hd : d + 32 ≤ 184) (hmin : 24 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf (VG.Proof.Ed25519.Arm.SignCached.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.Arm.SignCached.hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.Proof.Ed25519.Arm.SignCached.field_scr hL (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)

theorem hash_out_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) m n) :
    Spec.Ed25519.bytesAt n (State.addr L.out) 32 = Spec.Ed25519.bytesAt m (State.addr L.out) 32 := by
  apply VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf (VG.Proof.Ed25519.Arm.SignCached.baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.Arm.SignCached.hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.oc.sub_left (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub
  · exact (hL.ko.sub_right (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub).symm.sub_right (Region.sub_prefix (by decide))
  · exact (hL.ko.sub_right (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub).symm.sub_right (VG.Proof.Ed25519.Arm.SignCached.digestWithin L).sub

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

end VG.Proof.Ed25519.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Reduce`. -/
section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
open VG.Impl.Ed25519.Arm (scalarReduce)

def reduceRd (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : List Region := [VG.Proof.Ed25519.Arm.SignCached.digest L]
def reduceWr (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (d : Nat) : List Region := [VG.Proof.Ed25519.Arm.SignCached.field L d, L.SCR]
def ReduceArgs (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .r0 = L.E + BitVec.ofNat 32 d ∧ s.gpr .r1 = L.E + 184 ∧ s.gpr .r2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184) (ha : VG.Proof.Ed25519.Arm.SignCached.ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.Arm.SignCached.reduceRd L) (VG.Proof.Ed25519.Arm.SignCached.reduceWr L d)) := by
  have ad := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := d) (by omega)
  have a184 : State.addr (L.E + 184) = State.addr L.E + 184 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 184) (by decide)
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2, ad, a184]
  have sep : (VG.Proof.Ed25519.Arm.SignCached.field L d).Disjoint (VG.Proof.Ed25519.Arm.SignCached.digest L) := Offset.disjoint _ (by omega) (by omega) (by decide)
  exact ⟨rfl, rfl, sep,
    VG.Proof.Ed25519.Arm.SignCached.field_scr hL (by omega), hL.kc.sub_left (VG.Proof.Ed25519.Arm.SignCached.digestWithin L).sub,
    VG.Proof.Ed25519.Arm.SignCached.frame_fit hL (by omega), VG.Proof.Ed25519.Arm.SignCached.frame_fit hL (by decide), hL.nc⟩

theorem reduce_call (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184)
    (ha : VG.Proof.Ed25519.Arm.SignCached.ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.SignCached.reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 184) 64) := by
  have cov : Covers (VG.Proof.Ed25519.Arm.SignCached.reduceRd L ++ VG.Proof.Ed25519.Arm.SignCached.reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.Arm.SignCached.covers
    simp only [VG.Proof.Ed25519.Arm.SignCached.reduceRd, VG.Proof.Ed25519.Arm.SignCached.reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.digestWithin L)
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by omega))
    · exact .inr (VG.Proof.Ed25519.Arm.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.Arm.SignCached.reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.Arm.SignCached.writes
    simp only [VG.Proof.Ed25519.Arm.SignCached.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by omega))
    · exact .inr (.inr (VG.Proof.Ed25519.Arm.SignCached.scratchWithin L))
  refine Whole.call_ok hc scalarReduce_ok VG.Proof.Ed25519.Arm.SignCached.reduce_noFrames (VG.Proof.Ed25519.Arm.SignCached.reduce_pre hL hd ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (s.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 64) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1] at hp
  have ad := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := d) (by omega)
  have a184 : State.addr (L.E + 184) = State.addr L.E + 184 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 184) (by decide)
  rw [ad, a184] at hp
  exact hp

end VG.Proof.Ed25519.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.MulAdd`. -/
section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def mulRd (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : List Region := [VG.Proof.Ed25519.Arm.SignCached.field L 88, VG.Proof.Ed25519.Arm.SignCached.field L 120, VG.Proof.Ed25519.Arm.SignCached.field L 24, ⟨State.addr L.E, 4⟩]
def mulWr (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : List Region := [VG.Proof.Ed25519.Arm.SignCached.half L, L.SCR]
def MulArgs (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (s : State) : Prop :=
  s.gpr .r0 = L.out + 32 ∧ s.gpr .r1 = L.E + 88 ∧ s.gpr .r2 = L.E + 120 ∧
    s.gpr .r3 = L.E + 24 ∧ stackArg s 0 = L.scr

theorem mul_noFrames : scalarMulAdd.noFrames = true := by lit_decide

theorem mul_pre (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.MulArgs L s) :
    scalarMulAddLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.Arm.SignCached.mulRd L) (VG.Proof.Ed25519.Arm.SignCached.mulWr L)) := by
  have ao : State.addr (L.out + 32) = State.addr L.out + 32 := addr_add (k := 32) (by have := hL.no; omega)
  have fo : (L.out + 32).toNat + 32 ≤ 2 ^ 32 := by
    have hn := hL.no
    change (L.out.toNat + 32) % 2 ^ 32 + 32 ≤ 2 ^ 32
    rw [Nat.mod_eq_of_lt (by omega : L.out.toNat + 32 < 2 ^ 32)]
    omega
  have st : stackArg (s.callEntry.withRegions (VG.Proof.Ed25519.Arm.SignCached.mulRd L) (VG.Proof.Ed25519.Arm.SignCached.mulWr L)) 0 = stackArg s 0 := rfl
  have a88 : State.addr (L.E + 88) = State.addr L.E + 88 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 88) (by decide)
  have a120 : State.addr (L.E + 120) = State.addr L.E + 120 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 120) (by decide)
  have a24 : State.addr (L.E + 24) = State.addr L.E + 24 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 24) (by decide)
  have he := hc.sp
  simp only [scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), st,
    ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2, ao, he,
    a88, a120, a24]
  exact ⟨rfl, rfl, hL.oc.sub_left (VG.Proof.Ed25519.Arm.SignCached.halfWithin L).sub,
    VG.Proof.Ed25519.Arm.SignCached.field_scr hL (by decide), VG.Proof.Ed25519.Arm.SignCached.field_scr hL (by decide), VG.Proof.Ed25519.Arm.SignCached.field_scr hL (by decide),
    (hL.ko.sub_right (VG.Proof.Ed25519.Arm.SignCached.halfWithin L).sub).symm.sub_right (Region.sub_prefix (by decide)),
    hL.kc.symm.sub_right (Region.sub_prefix (by decide)), fo,
    VG.Proof.Ed25519.Arm.SignCached.frame_fit hL (by decide), VG.Proof.Ed25519.Arm.SignCached.frame_fit hL (by decide), VG.Proof.Ed25519.Arm.SignCached.frame_fit hL (by decide),
    hL.nc, by have := hL.top; omega⟩

theorem mul_call (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.MulArgs L s) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.SignCached.mulWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out + 32) 32 =
        Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 88) 32)
          (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32)
          (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 24) 32) := by
  have cov : Covers (VG.Proof.Ed25519.Arm.SignCached.mulRd L ++ VG.Proof.Ed25519.Arm.SignCached.mulWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.Arm.SignCached.covers
    simp only [VG.Proof.Ed25519.Arm.SignCached.mulRd, VG.Proof.Ed25519.Arm.SignCached.mulWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by decide))
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by decide))
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by decide))
    · exact .inl ⟨0, by simp, by change 0 + 4 ≤ 248; decide⟩
    · exact .inr (VG.Proof.Ed25519.Arm.SignCached.output_covered (VG.Proof.Ed25519.Arm.SignCached.halfWithin L))
    · exact .inr (VG.Proof.Ed25519.Arm.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.Arm.SignCached.mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.Arm.SignCached.writes
    simp only [VG.Proof.Ed25519.Arm.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (VG.Proof.Ed25519.Arm.SignCached.halfWithin L))
    · exact .inr (.inr (VG.Proof.Ed25519.Arm.SignCached.scratchWithin L))
  refine Whole.call_ok hc scalarMulAdd_ok VG.Proof.Ed25519.Arm.SignCached.mul_noFrames (VG.Proof.Ed25519.Arm.SignCached.mul_pre hc hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  have ao : State.addr (L.out + 32) = State.addr L.out + 32 := addr_add (k := 32) (by have := hL.no; omega)
  change Spec.Ed25519.bytesAt t.mem (State.addr (s.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r2)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r3)) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1] at hp
  have a88 : State.addr (L.E + 88) = State.addr L.E + 88 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 88) (by decide)
  have a120 : State.addr (L.E + 120) = State.addr L.E + 120 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 120) (by decide)
  have a24 : State.addr (L.E + 24) = State.addr L.E + 24 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 24) (by decide)
  rw [ao, a88, a120, a24] at hp
  exact hp

end VG.Proof.Ed25519.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Secret`. -/
section

/-! Merged from `Proof.Ed25519.Arm.SignCached.HashSteps`. -/
section
/-! Merged from `Proof.Ed25519.Arm.SignCached.HashReady`. -/
section
/-! Merged from `Proof.Ed25519.Arm.SignCached.HashInputs`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay}

structure Input (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (p n : BitVec 32) : Prop where
  cover : Whole.Within ⟨State.addr p, n.toNat⟩ L.FR ∨
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨State.addr p, n.toNat⟩ R
  scratch : Region.Disjoint ⟨State.addr p, n.toNat⟩ L.SCR
  args : Region.Disjoint ⟨State.addr p, n.toNat⟩ (VG.Proof.Ed25519.Arm.SignCached.slots L)
  fit : p.toNat + n.toNat ≤ 2 ^ 32

theorem input_self {r : Region} (hr : r ∈ L.inputs) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨r, List.mem_append_left _ hr, 0, by simp, by simp⟩

theorem input_slots (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) : r.Disjoint (VG.Proof.Ed25519.Arm.SignCached.slots L) :=
  (hL.ks _ hr).symm.sub_right (Region.sub_prefix (by decide))

theorem seed_input (hL : L.Ok) : VG.Proof.Ed25519.Arm.SignCached.Input L L.seed 32 :=
  ⟨.inr (VG.Proof.Ed25519.Arm.SignCached.input_self (r := L.SEED) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    VG.Proof.Ed25519.Arm.SignCached.input_slots hL (by simp [Lay.inputs]), hL.ns⟩

theorem key_input (hL : L.Ok) : VG.Proof.Ed25519.Arm.SignCached.Input L L.pk 32 :=
  ⟨.inr (VG.Proof.Ed25519.Arm.SignCached.input_self (r := L.PK) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    VG.Proof.Ed25519.Arm.SignCached.input_slots hL (by simp [Lay.inputs]), hL.np⟩

theorem message_input (hL : L.Ok) : VG.Proof.Ed25519.Arm.SignCached.Input L L.msg L.len :=
  ⟨.inr (VG.Proof.Ed25519.Arm.SignCached.input_self (r := L.MSG) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    VG.Proof.Ed25519.Arm.SignCached.input_slots hL (by simp [Lay.inputs]), hL.nm⟩

theorem point_input (hL : L.Ok) : VG.Proof.Ed25519.Arm.SignCached.Input L L.out 32 :=
  ⟨.inr (VG.Proof.Ed25519.Arm.SignCached.output_covered (VG.Proof.Ed25519.Arm.SignCached.baseWithin L)), hL.oc.sub_left (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub,
    (hL.ko.sub_right (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub).symm.sub_right (Region.sub_prefix (by decide)),
    by have := hL.no; change L.out.toNat + 32 ≤ 2 ^ 32; omega⟩

theorem prefix_input (hL : L.Ok) : VG.Proof.Ed25519.Arm.SignCached.Input L (L.E + 56) 32 := by
  have ae : State.addr (L.E + 56) = State.addr L.E + 56 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 56) (by decide)
  refine ⟨?_, ?_, ?_, VG.Proof.Ed25519.Arm.SignCached.frame_fit hL (d := 56) (by decide)⟩
  · rw [ae]
    exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by decide))
  · rw [ae]
    exact VG.Proof.Ed25519.Arm.SignCached.field_scr hL (by decide)
  · rw [ae]
    exact Offset.disjoint_base _ (by decide) (by decide)

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay}

theorem shaWithin (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Whole.Within (Whole.SHA L.scr) L.SCR :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩
theorem workWithin (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : Whole.Within (Whole.WORK L.scr) L.SCR :=
  ⟨192, rfl, by change 192 + 272 ≤ 8192; decide⟩
theorem argsWithin (L : VG.Proof.Ed25519.Arm.SignCached.Lay) {n : Nat} (hn : n ≤ 248) :
    Whole.Within (Whole.CALLARGS L.E n) L.FR := ⟨0, by simp, by change 0 + n ≤ 248; omega⟩

theorem init_frame {m n : Mem} (hf : Frame (Whole.initWr L.scr) m n) : Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) m n := by
  apply VG.Proof.Ed25519.Arm.SignCached.hash_frame hf
  intro r hr; rw [List.mem_singleton.mp hr]
  exact .inl (VG.Proof.Ed25519.Arm.SignCached.shaWithin L)

theorem update_frame {m n : Mem} (hf : Frame (Whole.hashWr L.scr) m n) : Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) m n := by
  apply VG.Proof.Ed25519.Arm.SignCached.hash_frame hf
  simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (VG.Proof.Ed25519.Arm.SignCached.shaWithin L)
  · exact .inl (VG.Proof.Ed25519.Arm.SignCached.workWithin L)

theorem final_addr (hL : L.Ok) : State.addr (L.E + 184) = State.addr L.E + 184 :=
  VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 184) (by decide)

theorem finalize_frame (hL : L.Ok) {m n : Mem} (hf : Frame (Whole.finalizeWr L.scr (L.E + 184)) m n) :
    Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) m n := by
  apply VG.Proof.Ed25519.Arm.SignCached.hash_frame hf
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (VG.Proof.Ed25519.Arm.SignCached.shaWithin L)
  · exact .inr ⟨0, by rw [VG.Proof.Ed25519.Arm.SignCached.final_addr hL]; simp [VG.Proof.Ed25519.Arm.SignCached.digest], by change 0 + 64 ≤ 64; decide⟩
  · exact .inl (VG.Proof.Ed25519.Arm.SignCached.workWithin L)

theorem final_writes (hL : L.Ok) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 184),
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  apply VG.Proof.Ed25519.Arm.SignCached.writes
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr (.inr (VG.Proof.Ed25519.Arm.SignCached.shaWithin L))
  · exact .inl ⟨184, VG.Proof.Ed25519.Arm.SignCached.final_addr hL, by change 184 + 64 ≤ 248; decide⟩
  · exact .inr (.inr (VG.Proof.Ed25519.Arm.SignCached.workWithin L))

theorem update_covers {p n : BitVec 32} (hi : VG.Proof.Ed25519.Arm.SignCached.Input L p n) :
    Covers (Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (L.inputs ++ L.FR :: L.outputs) := by
  apply VG.Proof.Ed25519.Arm.SignCached.covers
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hi.cover
  · exact .inl (VG.Proof.Ed25519.Arm.SignCached.argsWithin L (by decide))
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed25519.Arm.SignCached.shaWithin L⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed25519.Arm.SignCached.workWithin L⟩

theorem finalize_covers (hL : L.Ok) :
    Covers (Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 184)) (L.inputs ++ L.FR :: L.outputs) := by
  apply VG.Proof.Ed25519.Arm.SignCached.covers
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact .inl (VG.Proof.Ed25519.Arm.SignCached.argsWithin L (by decide))
  · rcases VG.Proof.Ed25519.Arm.SignCached.final_writes hL r hr with hf | ⟨R, hR, hw⟩
    · exact .inl hf
    · exact .inr ⟨R, List.mem_append_right _ hR, hw⟩

def UpdateArgs (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (count p n : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = L.scr ∧ t.gpr .r2 = count ∧ t.gpr .r3 = 0 ∧
    stackArg t 0 = p ∧ stackArg t 1 = n ∧ stackArg t 2 = L.scr + 192

def FinalArgs (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (count : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = L.scr ∧ t.gpr .r2 = count ∧ t.gpr .r3 = 0 ∧
    stackArg t 0 = L.E + 184 ∧ stackArg t 1 = L.scr + 192

theorem update_pre {t : State} (hL : L.Ok) (he : t.sp = L.E)
    {count p n : BitVec 32} (ha : VG.Proof.Ed25519.Arm.SignCached.UpdateArgs L count p n t) (hi : VG.Proof.Ed25519.Arm.SignCached.Input L p n) :
    Proof.Sha512.updateArm.pre (t.callEntry.withRegions (Whole.updateRd L.E p n) (Whole.hashWr L.scr)) :=
  Whole.update_pre he ha.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2 hi.scratch
    (hL.kc.sub_left (Region.sub_prefix (by decide))) hL.nc hi.fit (by have := hL.top; omega)

theorem finalize_pre {t : State} (hL : L.Ok) (he : t.sp = L.E)
    {count : BitVec 32} (ha : VG.Proof.Ed25519.Arm.SignCached.FinalArgs L count t) :
    Proof.Sha512.finalizeArm.pre (t.callEntry.withRegions (Whole.finalizeRd L.E) (Whole.finalizeWr L.scr (L.E + 184))) := by
  refine Whole.finalize_pre he ha.1 ha.2.2.2.1 ha.2.2.2.2 ?_
    (hL.kc.sub_left (Region.sub_prefix (by decide))) ?_ hL.nc
    (VG.Proof.Ed25519.Arm.SignCached.frame_fit hL (d := 184) (by decide)) (by have := hL.top; omega)
  · rw [VG.Proof.Ed25519.Arm.SignCached.final_addr hL]
    exact hL.kc.sub_left (VG.Proof.Ed25519.Arm.SignCached.digestWithin L).sub
  · rw [VG.Proof.Ed25519.Arm.SignCached.final_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)

theorem count_zero_high (x : BitVec 32) : (0#32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat]
  change 0 * 2 ^ 32 + x.toNat = x.toNat % 2 ^ 64
  omega

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem init_step (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀) :
    WP isa init s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr) [] := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.args_regs_ok hc hL ha (args := [(.r0, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.r0, .caller 5 0) (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call hu (Whole.init_pre a0 hL.nc) (Whole.covers_writes hw) hw a0)
    fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, hp⟩
  rw [hm] at hf
  exact VG.Proof.Ed25519.Arm.SignCached.init_frame hf

theorem update_step (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀)
    (count : Nat) (p n : Value) (hc16 : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L p) (VG.Proof.Ed25519.Arm.SignCached.value L n)) {prev : List Byte}
    (hcount : count = prev.length) (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (setup [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)]
      [p, n, .caller 5 192])) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (VG.Proof.Ed25519.Arm.SignCached.value L p)) (VG.Proof.Ed25519.Arm.SignCached.value L n).toNat) := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)] →
      Whole.valid x.2 := by simp [Whole.valid, hc16]
  have hvs : ∀ v ∈ [p, n, Value.caller 5 192], Whole.valid v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl)
    · exact hp
    · exact hn
    · simp [Whole.valid]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.args_ok hc hL ha (by simp) hv (by simp) hvs (by simp [preserved]))
    fun u ⟨hu, hf, hs, hstack⟩ => ?_)
  have a0 := hs (.r0, .caller 5 0) (by simp)
  have a2 : u.gpr .r2 = BitVec.ofNat 32 count := hs (.r2, .const count) (by simp)
  have a3 : u.gpr .r3 = 0#32 := hs (.r3, .const 0) (by simp)
  have d0 := hstack 0 (by simp)
  have d1 := hstack 1 (by simp)
  have d2 := hstack 2 (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have args : VG.Proof.Ed25519.Arm.SignCached.UpdateArgs L (BitVec.ofNat 32 count) (VG.Proof.Ed25519.Arm.SignCached.value L p) (VG.Proof.Ed25519.Arm.SignCached.value L n) u := ⟨a0,a2,a3,d0,d1,d2⟩
  have ce : Proof.Sha512.countArm u = BitVec.ofNat 64 prev.length := by
    unfold Proof.Sha512.countArm
    rw [a3,a2,VG.Proof.Ed25519.Arm.SignCached.count_zero_high]
    change BitVec.ofNat 64 (count % 2^32) = _
    rw [Nat.mod_eq_of_lt (by omega),hcount]
  have huRepr := VG.Proof.Ed25519.Arm.SignCached.setup_repr hL hf hr
  have heq : Spec.Ed25519.bytesAt u.mem (State.addr (VG.Proof.Ed25519.Arm.SignCached.value L p)) (VG.Proof.Ed25519.Arm.SignCached.value L n).toNat =
      Spec.Ed25519.bytesAt s.mem (State.addr (VG.Proof.Ed25519.Arm.SignCached.value L p)) (VG.Proof.Ed25519.Arm.SignCached.value L n).toNat :=
    VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf ⟨State.addr (VG.Proof.Ed25519.Arm.SignCached.value L p), (VG.Proof.Ed25519.Arm.SignCached.value L n).toNat⟩
      (by simp only [List.mem_singleton]; intro r he; subst r; exact hi.args)
      (by have := (VG.Proof.Ed25519.Arm.SignCached.value L n).isLt; change (VG.Proof.Ed25519.Arm.SignCached.value L n).toNat ≤ 2^64; omega)
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.update_call hu (VG.Proof.Ed25519.Arm.SignCached.update_pre hL hu.sp args hi) (VG.Proof.Ed25519.Arm.SignCached.update_covers hi) hw
    a0 d0 d1 ce huRepr) fun t ⟨ht, hf', hrepr⟩ => ⟨ht, (VG.Proof.Ed25519.Arm.SignCached.setup_frame hf).trans (VG.Proof.Ed25519.Arm.SignCached.update_frame hf'), ?_⟩
  change Spec.Sha512.Repr _ t.mem _ (prev ++ Spec.Ed25519.bytesAt u.mem (State.addr (VG.Proof.Ed25519.Arm.SignCached.value L p)) (VG.Proof.Ed25519.Arm.SignCached.value L n).toNat) at hrepr
  rw [heq] at hrepr
  exact hrepr

theorem finalize_count (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (n : Nat) (b : Bool) :
    VG.Proof.Ed25519.Arm.SignCached.value L (if b then Value.caller 4 n else .const n) =
      BitVec.ofNat 32 ((if b then L.len.toNat else 0) + n) := by
  cases b <;> simp [VG.Proof.Ed25519.Arm.SignCached.value, Lay.value, BitVec.ofNat_add]

theorem finalize_step (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀)
    (n : Nat) (hn : n < 256) (b : Bool) {msg : List Byte}
    (hlen : msg.length < 2^32) (hcount : (if b then L.len.toNat else 0) + n = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) msg) :
    WP isa (finalize n b) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 = Spec.Sha512.sha512 msg := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.r0, .caller 5 0),
      (.r2, if b then .caller 4 n else .const n), (.r3, .const 0)] → Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    · simp [Whole.valid]
    · cases b <;> simp [Whole.valid] <;> omega
    · simp [Whole.valid]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.args_ok hc hL ha (by simp) hv (by simp)
    (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu,hf,hs,hstack⟩ => ?_)
  have a0 := hs (.r0, .caller 5 0) (by simp)
  have a2 := hs (.r2, if b then .caller 4 n else .const n) (by simp)
  have a3 : u.gpr .r3 = 0#32 := hs (.r3, .const 0) (by simp)
  have d0 := hstack 0 (by simp)
  have d1 := hstack 1 (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  rw [VG.Proof.Ed25519.Arm.SignCached.finalize_count,hcount] at a2
  have args : VG.Proof.Ed25519.Arm.SignCached.FinalArgs L (BitVec.ofNat 32 msg.length) u := ⟨a0,a2,a3,d0,d1⟩
  have ce : Proof.Sha512.countArm u = BitVec.ofNat 64 msg.length := by
    unfold Proof.Sha512.countArm
    rw [a3,a2,VG.Proof.Ed25519.Arm.SignCached.count_zero_high]
    change BitVec.ofNat 64 (msg.length % 2^32) = _
    rw [Nat.mod_eq_of_lt hlen]
  refine WP.mono (Whole.finalize_call hu (VG.Proof.Ed25519.Arm.SignCached.finalize_pre hL hu.sp args) (VG.Proof.Ed25519.Arm.SignCached.finalize_covers hL)
    (VG.Proof.Ed25519.Arm.SignCached.final_writes hL) a0 d0 ce (VG.Proof.Ed25519.Arm.SignCached.setup_repr hL hf hr) (by omega))
    fun t ⟨ht,hf',hh⟩ => ⟨ht,(VG.Proof.Ed25519.Arm.SignCached.setup_frame hf).trans (VG.Proof.Ed25519.Arm.SignCached.finalize_frame hL hf'),?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (L.E + 184)) 64 = _ at hh
  rw [VG.Proof.Ed25519.Arm.SignCached.final_addr hL] at hh
  exact hh

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Hashes`. -/
section
/-! Merged from `Proof.Ed25519.Arm.SignCached.HashUpdates`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem update_input (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀)
    (source count : Nat) (hj : source < 6) (hc16 : count < 65536) (hi : VG.Proof.Ed25519.Arm.SignCached.Input L (L.value source) 32)
    {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (inputArgs source count)) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (L.value source)) 32) := by
  have inp : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L (.caller source 0)) (VG.Proof.Ed25519.Arm.SignCached.value L (.const 32)) := by
    change VG.Proof.Ed25519.Arm.SignCached.Input L (L.value source + 0#32) 32#32
    rw [BitVec.add_zero]
    exact hi
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.update_step hc hL ha count (.caller source 0) (.const 32) hc16
    ⟨hj, by decide⟩ (by simp [Whole.valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  change Spec.Sha512.Repr _ t.mem _ (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (L.value source + 0#32)) 32) at hh
  rw [BitVec.add_zero] at hh
  exact hh

theorem update_prefix (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) []) :
    WP isa (update prefixArgs) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 56) 32) := by
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.update_step hc hL ha 0 (.frame 56) (.const 32) (by decide)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (VG.Proof.Ed25519.Arm.SignCached.prefix_input hL) rfl hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  change Spec.Sha512.Repr _ t.mem _ ([] ++ Spec.Ed25519.bytesAt s.mem (State.addr (L.E + 56)) 32) at hh
  have ae : State.addr (L.E + 56) = State.addr L.E + 56 := VG.Proof.Ed25519.Arm.SignCached.frame_addr hL (d := 56) (by decide)
  rw [List.nil_append, ae] at hh
  exact hh

theorem update_message (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀)
    (count : Nat) (hc16 : count < 65536) {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (messageArgs count)) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have inp : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L (.caller 3 0)) (VG.Proof.Ed25519.Arm.SignCached.value L (.caller 4 0)) := by
    simpa only [VG.Proof.Ed25519.Arm.SignCached.value, Lay.value, BitVec.add_zero] using VG.Proof.Ed25519.Arm.SignCached.message_input hL
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.update_step hc hL ha count (.caller 3 0) (.caller 4 0) hc16
    (by simp [Whole.valid]) (by simp [Whole.valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  simp only [VG.Proof.Ed25519.Arm.SignCached.value, Lay.value, BitVec.add_zero] at hh
  rw [hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (by have := L.len.isLt; change L.len.toNat ≤ 2^64; omega)] at hh
  exact hh

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashSeed_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀) :
    WP isa (hashSeed) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.update_input hu hL ha 1 0 (by decide) (by decide) (VG.Proof.Ed25519.Arm.SignCached.seed_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have hs := hu.input_bytes hL (r := L.SEED) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt u.mem (State.addr L.seed) 32 = Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32 at hs
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (State.addr L.seed) 32) at rv
  rw [List.nil_append, hs] at rv
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.finalize_step hv hL ha 32 (by decide) false
    (by rw [VG.Proof.Ed25519.Arm.SignCached.bytes_length]; decide) (by rw [VG.Proof.Ed25519.Arm.SignCached.bytes_length]; rfl) rv)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans ft), hd⟩

theorem hashNonce_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀) :
    WP isa (hashNonce) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 56) 32 ++
          Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.update_prefix hu hL ha ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have keep := VG.Proof.Ed25519.Arm.SignCached.hash_field_bytes hL fu (d := 56) (by decide) (by decide)
  change Spec.Ed25519.bytesAt u.mem (State.addr L.E + (56 : BitVec 64)) 32 = Spec.Ed25519.bytesAt s.mem (State.addr L.E + (56 : BitVec 64)) 32 at keep
  rw [keep] at rv
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.update_message hv hL ha 32 (by decide) (by rw [VG.Proof.Ed25519.Arm.SignCached.bytes_length]) rv)
    fun w ⟨hw, fw, rw'⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.finalize_step hw hL ha 32 (by decide) true ?_ ?_ rw')
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans ft)), hd⟩
  · rw [List.length_append, VG.Proof.Ed25519.Arm.SignCached.bytes_length, VG.Proof.Ed25519.Arm.SignCached.bytes_length]
    have := hL.message_bound; omega
  · rw [List.length_append, VG.Proof.Ed25519.Arm.SignCached.bytes_length, VG.Proof.Ed25519.Arm.SignCached.bytes_length]
    simp only [ite_true]; omega

theorem hashChallenge_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀) :
    WP isa (hashChallenge) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr L.out) 32 ++
          Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32 ++
          Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.update_input hu hL ha 0 0 (by decide) (by decide) (VG.Proof.Ed25519.Arm.SignCached.point_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32) at rv
  rw [List.nil_append, VG.Proof.Ed25519.Arm.SignCached.hash_out_bytes hL fu] at rv
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.update_input hv hL ha 2 32 (by decide) (by decide) (VG.Proof.Ed25519.Arm.SignCached.key_input hL)
    (by rw [VG.Proof.Ed25519.Arm.SignCached.bytes_length]) rv) fun w ⟨hw, fw, rw'⟩ => ?_)
  have hk := hv.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt v.mem (State.addr L.pk) 32 = Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32 at hk
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt v.mem (State.addr L.pk) 32) at rw'
  rw [hk] at rw'
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.update_message hw hL ha 64 (by decide) (by rw [List.length_append, VG.Proof.Ed25519.Arm.SignCached.bytes_length, VG.Proof.Ed25519.Arm.SignCached.bytes_length])
    rw') fun z ⟨hz, fz, rz⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.finalize_step hz hL ha 64 (by decide) true ?_ ?_ rz)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans (fz.trans ft))), hd⟩
  · rw [List.length_append, List.length_append, VG.Proof.Ed25519.Arm.SignCached.bytes_length, VG.Proof.Ed25519.Arm.SignCached.bytes_length, VG.Proof.Ed25519.Arm.SignCached.bytes_length]
    have := hL.message_bound; omega
  · rw [List.length_append, List.length_append, VG.Proof.Ed25519.Arm.SignCached.bytes_length, VG.Proof.Ed25519.Arm.SignCached.bytes_length, VG.Proof.Ed25519.Arm.SignCached.bytes_length]
    simp only [ite_true]; omega

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Preserve`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {m n : Mem}

theorem single_frame_bytes {d e k : Nat} (hf : Frame [⟨State.addr L.E + BitVec.ofNat 64 e, k⟩] m n)
    (hd : d + 32 ≤ 248) (he : e + k ≤ 248) (hs : d + 32 ≤ e ∨ e + k ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf (VG.Proof.Ed25519.Arm.SignCached.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ hs (by omega) (by omega)

theorem reduce_field_bytes (hL : L.Ok) {d out : Nat} (hf : Frame (VG.Proof.Ed25519.Arm.SignCached.reduceWr L out) m n)
    (hd : d + 32 ≤ 248) (ho : out + 32 ≤ 248) (hs : d + 32 ≤ out ∨ out + 32 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf (VG.Proof.Ed25519.Arm.SignCached.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.Arm.SignCached.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.disjoint _ hs (by omega) (by omega)
  · exact VG.Proof.Ed25519.Arm.SignCached.field_scr hL hd

theorem base_field_bytes (hL : L.Ok) (hf : Frame (VG.Proof.Ed25519.Arm.SignCached.baseWr L) m n) {d : Nat} (hd : d + 32 ≤ 248) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf (VG.Proof.Ed25519.Arm.SignCached.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.Arm.SignCached.baseWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hL.ko.sub_left (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L hd).sub).sub_right (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub
  · exact VG.Proof.Ed25519.Arm.SignCached.field_scr hL hd

theorem reduce_out_bytes (hL : L.Ok) {d : Nat} (hf : Frame (VG.Proof.Ed25519.Arm.SignCached.reduceWr L d) m n) (hd : d + 32 ≤ 248) :
    Spec.Ed25519.bytesAt n (State.addr L.out) 32 = Spec.Ed25519.bytesAt m (State.addr L.out) 32 := by
  apply VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf (VG.Proof.Ed25519.Arm.SignCached.baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.Arm.SignCached.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact ((hL.ko.sub_left (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L hd).sub).sub_right (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub).symm
  · exact hL.oc.sub_left (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub

theorem mul_out_bytes (hL : L.Ok) (hf : Frame (VG.Proof.Ed25519.Arm.SignCached.mulWr L) m n) :
    Spec.Ed25519.bytesAt n (State.addr L.out) 32 = Spec.Ed25519.bytesAt m (State.addr L.out) 32 := by
  apply VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf (VG.Proof.Ed25519.Arm.SignCached.baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.Arm.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact hL.oc.sub_left (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Prefix`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

structure PrefixStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → t.gpr r = s.gpr r

theorem PrefixStep.trans {s t u : State} (h : VG.Proof.Ed25519.Arm.SignCached.PrefixStep s t) (h' : VG.Proof.Ed25519.Arm.SignCached.PrefixStep t u) : VG.Proof.Ed25519.Arm.SignCached.PrefixStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem copyWord_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hr : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 8) :
    WP isa (.block (copyWord k)) s fun t => VG.Proof.Ed25519.Arm.SignCached.PrefixStep s t ∧
      t.mem = s.mem.writeW (State.addr E + BitVec.ofNat 64 (56 + 4 * k))
        (s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * k)) 32) := by
  have ae : State.addr (E + BitVec.ofNat 32 (216 + 4 * k)) = State.addr E + BitVec.ofNat 64 (216 + 4 * k) :=
    addr_add (by omega)
  have ad : State.addr (E + BitVec.ofNat 32 (56 + 4 * k)) = State.addr E + BitVec.ofNat 64 (56 + 4 * k) :=
    addr_add (by omega)
  have source : InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (216 + 4 * k)) 4 :=
    ⟨⟨State.addr E, 248⟩, List.mem_append_right _ hr, Offset.contains_base _ (by omega) (by omega)⟩
  have dest : InRegions s.wr (State.addr E + BitVec.ofNat 64 (56 + 4 * k)) 4 :=
    ⟨⟨State.addr E, 248⟩, hr, Offset.contains_base _ (by omega) (by omega)⟩
  have hl : exec (.ldrSp .r0 (216 + 4 * k)) s =
      some (s.setReg .r0 (s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * k)) 32)) := by
    simp only [exec, show 216 + 4 * k < 4096 from by omega, ite_true,
      State.load32, he, ae, source, Option.map_some]
  have ha {t : State} : exec (.addSp .r12 0) t = some (t.setReg .r12 t.sp) := by
    simp only [exec, show 0 < 256 from by decide, ite_true, BitVec.add_zero]
  apply WP.of_runBlock
  simp only [copyWord, runBlock_cons, runStep_some, hl, ha, RegUpd.sp_setReg]
  rw [exec_str (by omega) (by
    simpa only [RegUpd.wr_setReg, RegUpd.gpr_setReg_self, he, ad] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h0 h12
    simp only [RegUpd.gpr_setReg, h0, h12, ite_false]
  · simp only [RegUpd.mem_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, he, ad]

structure PrefixInv (E : BitVec 32) (s : State) (n : Nat) (t : State) : Prop where
  step : VG.Proof.Ed25519.Arm.SignCached.PrefixStep s t
  frame : Frame [⟨State.addr E + BitVec.ofNat 64 56, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (State.addr E + BitVec.ofNat 64 (56 + 4 * j)) 32 =
    s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * j)) 32

theorem copyPrefix_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hw : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap copyWord)) s (VG.Proof.Ed25519.Arm.SignCached.PrefixInv E s n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.copyPrefix_ok he hf hw n (by omega)) fun u hu => ?_
    refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.copyWord_ok (hu.step.sp.trans he) hf (hu.step.wr ▸ hw) (by omega : n < 8))
      fun t ⟨kt, mt⟩ => ?_
    have same : u.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * n)) 32 =
        s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * n)) 32 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega) (by omega) (by decide)
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (a := State.addr E + BitVec.ofNat 64 (56 + 4 * j))
          (b := State.addr E + BitVec.ofNat 64 (56 + 4 * n)) ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem prefix_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hw : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) :
    WP isa (.block copyPrefix) s fun t => VG.Proof.Ed25519.Arm.SignCached.PrefixStep s t ∧
      Frame [⟨State.addr E + 56, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr E + 56) 32 =
        Spec.Ed25519.bytesAt s.mem (State.addr E + 216) 32 := by
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.copyPrefix_ok he hf hw 8 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ed : State.addr E + 56 + BitVec.ofNat 64 i =
      (State.addr E + BitVec.ofNat 64 (56 + 4 * (i / 4))) + BitVec.ofNat 64 (i % 4) := by
    change State.addr E + BitVec.ofNat 64 56 + BitVec.ofNat 64 i = _
    rw [Offset.add_add, Offset.add_add]
    exact congrArg (fun n => State.addr E + BitVec.ofNat 64 n) (by omega)
  have es : State.addr E + 216 + BitVec.ofNat 64 i =
      (State.addr E + BitVec.ofNat 64 (216 + 4 * (i / 4))) + BitVec.ofNat 64 (i % 4) := by
    change State.addr E + BitVec.ofNat 64 216 + BitVec.ofNat 64 i = _
    rw [Offset.add_add, Offset.add_add]
    exact congrArg (fun n => State.addr E + BitVec.ofNat 64 n) (by omega)
  rw [ed, es, Mem.readW_byte t.mem _ (i := i % 4) (Nat.mod_lt _ (by decide)),
    Mem.readW_byte s.mem _ (i := i % 4) (Nat.mod_lt _ (by decide)), ht.words (i / 4) (by omega)]

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem prune_ctx {t : State} (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (ht : PublicKey.Step s t)
    (hf : Frame [⟨State.addr L.E + 24, 32⟩] s.mem t.mem) : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 24 + 32 ≤ 248))

theorem prefix_ctx {t : State} (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (ht : VG.Proof.Ed25519.Arm.SignCached.PrefixStep s t)
    (hf : Frame [⟨State.addr L.E + BitVec.ofNat 64 56, 32⟩] s.mem t.mem) : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 56 + 32 ≤ 248))

theorem saveSecret_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) {expanded : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (State.addr L.E + 184) 64 = expanded) :
    WP isa (.block saveSecret) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 56) 32 = expanded.drop 32 := by
  rw [saveSecret, WP.block_append_iff]
  have fr : (⟨State.addr L.E, 248⟩ : Region) ∈ s.wr := by rw [hc.wr]; exact List.mem_cons_self
  have fit : L.E.toNat + 248 ≤ 2 ^ 32 := by have := hL.top; omega
  refine WP.mono (PublicKey.prune_ok hc.sp fit fr he) fun u ⟨hu, hf, hs⟩ => ?_
  have hcu := VG.Proof.Ed25519.Arm.SignCached.prune_ctx hc hu hf
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.prefix_ok hcu.sp fit (by rw [hcu.wr]; exact List.mem_cons_self))
    fun t ⟨ht, hft, hp⟩ => ⟨VG.Proof.Ed25519.Arm.SignCached.prefix_ctx hcu ht hft, ?_, ?_⟩
  · have keep := VG.Proof.Ed25519.Arm.SignCached.single_frame_bytes (L := L) hft (d := 24) (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 = Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32 at keep
    rw [keep]
    have sc := Proof.Ed25519.bytesAt_encodeLE u.mem (State.addr L.E + 24) 32
    change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32) = Spec.Ed25519.prune expanded at hs
    rw [hs] at sc
    exact sc
  · rw [hp]
    have keep := VG.Proof.Ed25519.Arm.SignCached.single_frame_bytes (L := L) (e := 24) (k := 32) hf (d := 216)
      (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (State.addr L.E + 216) 32 = Spec.Ed25519.bytesAt s.mem (State.addr L.E + 216) 32 at keep
    rw [keep, ← he, Proof.Ed25519.signatureBytes_drop]
    rw [BitVec.add_assoc, show (184 : BitVec 64) + BitVec.ofNat 64 32 = (216 : BitVec 64) from rfl]

def expanded (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (m : Mem) : List Byte := Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m (State.addr L.seed) 32)
def scalar (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (m : Mem) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune (VG.Proof.Ed25519.Arm.SignCached.expanded L m))
def nonce (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (m : Mem) : List Byte := Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
  ((VG.Proof.Ed25519.Arm.SignCached.expanded L m).drop 32 ++ Spec.Ed25519.bytesAt m (State.addr L.msg) L.len.toNat))

structure SecretReady (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 = VG.Proof.Ed25519.Arm.SignCached.scalar L m
  prefixBytes : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 56) 32 = (VG.Proof.Ed25519.Arm.SignCached.expanded L m).drop 32

theorem secret_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀) :
    WP isa secretCode s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ VG.Proof.Ed25519.Arm.SignCached.SecretReady L m₀ t := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.hashSeed_ok hc hL ha) fun u ⟨hu, _, he⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.Arm.SignCached.saveSecret_ok hu hL he) fun t ⟨ht, hs, hp⟩ => ⟨ht, hs, hp⟩

end VG.Proof.Ed25519.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Body`. -/
section

/-! Merged from `Proof.Ed25519.Arm.SignCached.PrimitiveSteps`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_step (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀)
    (d : Nat) (hd : d + 32 ≤ 184) :
    WP isa (reduce d) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.SignCached.reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 184) 64) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.args_regs_ok hc hL ha
    (args := [(.r0, .frame d), (.r1, .frame 184), (.r2, .caller 5 0)])
    (by simp) (by simp [Whole.valid]; omega) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.r0, .frame d) (by simp)
  have a1 := hs (.r1, .frame 184) (by simp)
  have a2 := hs (.r2, .caller 5 0) (by simp)
  change u.gpr .r2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.reduce_call hu hL hd ⟨a0, a1, a2⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

theorem base_step (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.Arm.Whole.callWith baseArgs "vg_ed25519_scalar_base" VG.Impl.Ed25519.Arm.scalarBase) s
      fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.SignCached.baseWr L) s.mem t.mem ∧
        Spec.Ed25519.bytesAt t.mem (State.addr L.out) 32 =
          Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 88) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.args_regs_ok hc hL ha
    (args := [(.r0, .caller 0 0), (.r1, .frame 88), (.r2, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.r0, .caller 0 0) (by simp)
  have a1 := hs (.r1, .frame 88) (by simp)
  have a2 := hs (.r2, .caller 5 0) (by simp)
  change u.gpr .r0 = L.out + 0#32 at a0
  change u.gpr .r2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a0 a2
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.base_call hu hL ⟨a0, a1, a2⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

def mulStepWr (L : VG.Proof.Ed25519.Arm.SignCached.Lay) : List Region := VG.Proof.Ed25519.Arm.SignCached.slots L :: VG.Proof.Ed25519.Arm.SignCached.mulWr L

theorem mul_step (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.Arm.Whole.callWith mulAddArgs "vg_ed25519_scalar_mul_add" VG.Impl.Ed25519.Arm.scalarMulAdd) s
      fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.SignCached.mulStepWr L) s.mem t.mem ∧
        Spec.Ed25519.bytesAt t.mem (State.addr L.out + 32) 32 =
          Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 88) 32)
            (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32)
            (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 24) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.args_ok hc hL ha
    (args := [(.r0, .caller 0 32), (.r1, .frame 88), (.r2, .frame 120), (.r3, .frame 24)])
    (stack := [.caller 5 0]) (by decide) (by simp [Whole.valid]) (by decide)
    (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hf, hs, hst⟩ => ?_)
  have a0 := hs (.r0, .caller 0 32) (by simp)
  have a1 := hs (.r1, .frame 88) (by simp)
  have a2 := hs (.r2, .frame 120) (by simp)
  have a3 := hs (.r3, .frame 24) (by simp)
  have a4 := hst 0 (by decide)
  change stackArg u 0 = L.scr + 0#32 at a4
  rw [BitVec.add_zero] at a4
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.mul_call hu hL ⟨a0, a1, a2, a3, a4⟩) fun t ⟨ht, hft, hp⟩ => ⟨ht, ?_, ?_⟩
  · exact (hf.mono (by intro r hr; rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)).trans
      (hft.mono (fun _ hr => List.mem_cons_of_mem _ hr))
  · have a := VG.Proof.Ed25519.Arm.SignCached.setup_field_bytes (L := L) hf (d := 88) (by decide) (by decide)
    have b := VG.Proof.Ed25519.Arm.SignCached.setup_field_bytes (L := L) hf (d := 120) (by decide) (by decide)
    have c := VG.Proof.Ed25519.Arm.SignCached.setup_field_bytes (L := L) hf (d := 24) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (State.addr L.E + 88) 32 = _ at a
    change Spec.Ed25519.bytesAt u.mem (State.addr L.E + 120) 32 = _ at b
    change Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32 = _ at c
    rw [a, b, c] at hp
    exact hp

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem mul_step_out_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (VG.Proof.Ed25519.Arm.SignCached.mulStepWr L) m n) :
    Spec.Ed25519.bytesAt n (State.addr L.out) 32 = Spec.Ed25519.bytesAt m (State.addr L.out) 32 := by
  apply VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf (VG.Proof.Ed25519.Arm.SignCached.baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.Arm.SignCached.mulStepWr, VG.Proof.Ed25519.Arm.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact (hL.ko.sub_right (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub).symm.sub_right (Region.sub_prefix (by decide))
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact hL.oc.sub_left (VG.Proof.Ed25519.Arm.SignCached.baseWithin L).sub

structure NonceReady (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 = VG.Proof.Ed25519.Arm.SignCached.scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 88) 32 = VG.Proof.Ed25519.Arm.SignCached.nonce L m
  point : Spec.Ed25519.bytesAt t.mem (State.addr L.out) 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

theorem nonce_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀) (hs : VG.Proof.Ed25519.Arm.SignCached.SecretReady L m₀ s) :
    WP isa (nonceCode) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧ VG.Proof.Ed25519.Arm.SignCached.NonceReady L m₀ t := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.hashNonce_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.prefixBytes] at du
  have su := (VG.Proof.Ed25519.Arm.SignCached.hash_field_bytes hL fu (d := 24) (by decide) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.reduce_step hu hL ha 88 (by decide)) fun v ⟨hv, fv, nv⟩ => ?_)
  rw [du] at nv
  have sv := (VG.Proof.Ed25519.Arm.SignCached.reduce_field_bytes hL fv (d := 24) (by decide) (by decide) (by decide)).trans su
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.base_step hv hL ha) fun t ⟨ht, ft, pt⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (VG.Proof.Ed25519.Arm.SignCached.base_field_bytes hL ft (d := 24) (by decide)).trans sv
  · exact (VG.Proof.Ed25519.Arm.SignCached.base_field_bytes hL ft (d := 88) (by decide)).trans nv
  · change Spec.Ed25519.bytesAt v.mem (State.addr L.E + 88) 32 = _ at nv
    rw [nv] at pt
    exact pt

theorem challenge_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀) (hs : VG.Proof.Ed25519.Arm.SignCached.NonceReady L m₀ s)
    (hk : Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)) :
    WP isa (challengeCode) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)
        (Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.hashChallenge_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.point] at du
  have su := (VG.Proof.Ed25519.Arm.SignCached.hash_field_bytes hL fu (d := 24) (by decide) (by decide)).trans hs.scalar
  have nu := (VG.Proof.Ed25519.Arm.SignCached.hash_field_bytes hL fu (d := 88) (by decide) (by decide)).trans hs.nonce
  have pu := (VG.Proof.Ed25519.Arm.SignCached.hash_out_bytes hL fu).trans hs.point
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.reduce_step hu hL ha 120 (by decide)) fun v ⟨hv, fv, cv⟩ => ?_)
  rw [du] at cv
  have sv := (VG.Proof.Ed25519.Arm.SignCached.reduce_field_bytes hL fv (d := 24) (by decide) (by decide) (by decide)).trans su
  have nv := (VG.Proof.Ed25519.Arm.SignCached.reduce_field_bytes hL fv (d := 88) (by decide) (by decide) (by decide)).trans nu
  have pv := (VG.Proof.Ed25519.Arm.SignCached.reduce_out_bytes hL fv (by decide)).trans pu
  refine WP.mono (VG.Proof.Ed25519.Arm.SignCached.mul_step hv hL ha) fun t ⟨ht, ft, st⟩ => ⟨ht, ?_⟩
  change Spec.Ed25519.bytesAt v.mem (State.addr L.E + 88) 32 = _ at nv
  change Spec.Ed25519.bytesAt v.mem (State.addr L.E + 120) 32 = _ at cv
  change Spec.Ed25519.bytesAt v.mem (State.addr L.E + 24) 32 = _ at sv
  rw [nv, cv, sv] at st
  have pt := (VG.Proof.Ed25519.Arm.SignCached.mul_step_out_bytes hL ft).trans pv
  rw [Proof.Ed25519.signatureBytes_split, pt]
  change Spec.Ed25519.scalarBase (VG.Proof.Ed25519.Arm.SignCached.nonce L m₀) ++ Spec.Ed25519.bytesAt t.mem (State.addr L.out + (32 : BitVec 64)) 32 = _
  rw [st]
  exact Proof.Ed25519.sign_pipeline _ _ _ hk

theorem wipe_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) :
    WP isa (.block wipe) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out) 64 = Spec.Ed25519.bytesAt s.mem (State.addr L.out) 64 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 6) (count := 56) (by decide))
    fun t ⟨ht, hf, _⟩ => ⟨ht, ?_⟩
  refine VG.Proof.Ed25519.Arm.SignCached.frame_bytes hf L.OUT ?_ (by change 64 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 4 * 6 + 4 * 56 ≤ 248))).symm

theorem body_ok (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₀)
    (hk : Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)) :
    WP isa (body) s fun t => VG.Proof.Ed25519.Arm.SignCached.Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)
        (Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.secret_ok hc hL ha) fun u ⟨hu, su⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.nonce_ok hu hL ha su) fun v ⟨hv, nv⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.SignCached.challenge_ok hv hL ha nv hk) fun w ⟨hw, sw⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.Arm.SignCached.wipe_ok hw hL) fun t ⟨ht, same⟩ => ⟨ht, same.trans sw⟩

end VG.Proof.Ed25519.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTCommon`. -/
section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def Two (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (g₁ g₂ : Reg → BitVec 32)
    (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  VG.Proof.Ed25519.Arm.SignCached.Ctx L g₁ m₁ a ∧ VG.Proof.Ed25519.Arm.SignCached.Ctx L g₂ m₂ b ∧ P a ∧ P b

theorem two_sp {P : State → Prop} {a b : State} (h : VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ P a b) :
    a.sp = b.sp := h.1.sp.trans h.2.1.sp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, VG.Proof.Ed25519.Arm.SignCached.Ctx L g₁ m₁ t → P t → WP isa c t fun u => VG.Proof.Ed25519.Arm.SignCached.Ctx L g₁ m₁ u ∧ Q u)
    (hb : ∀ t, VG.Proof.Ed25519.Arm.SignCached.Ctx L g₂ m₂ t → P t → WP isa c t fun u => VG.Proof.Ed25519.Arm.SignCached.Ctx L g₂ m₂ u ∧ Q u) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ P) c (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

def AllArgs (L : VG.Proof.Ed25519.Arm.SignCached.Lay) (args : List (Reg × Value)) (stack : List Value) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.SignCached.OutArgs L args s ∧ VG.Proof.Ed25519.Arm.SignCached.StackArgs L stack s

theorem setup_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂)
    (args : List (Reg × Value)) (stack : List Value) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hs : stack.length ≤ 6)
    (hvs : ∀ v ∈ stack, Whole.valid v) (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stack))
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.SignCached.AllArgs L args stack)) := by
  refine VG.Proof.Ed25519.Arm.SignCached.two_wp ((Whole.setup_ct args stack).mono (fun _ _ h => VG.Proof.Ed25519.Arm.SignCached.two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro s hc _
    exact WP.mono (VG.Proof.Ed25519.Arm.SignCached.args_ok hc hL ha hn hv hs hvs hr) fun _ ⟨hu, _, hg, ht⟩ => ⟨hu, hg, ht⟩
  · intro s hc _
    exact WP.mono (VG.Proof.Ed25519.Arm.SignCached.args_ok hc hL hb hn hv hs hvs hr) fun _ ⟨hu, _, hg, ht⟩ => ⟨hu, hg, ht⟩

theorem args_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.SignCached.AllArgs L args stack) a b) {p : Reg × Value} (hp : p ∈ args) :
    a.gpr p.1 = b.gpr p.1 := (h.2.2.1.1 p hp).trans (h.2.2.2.1 p hp).symm

theorem call_gpr_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.SignCached.AllArgs L args stack) a b) {p : Reg × Value}
    (hp : p ∈ args) (hl : p.1 ∉ linkRegs) : a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := by
  rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl]
  exact VG.Proof.Ed25519.Arm.SignCached.args_eq h hp

theorem stack_arg_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.SignCached.AllArgs L args stack) a b) {j : Nat} (hj : j < stack.length) :
    stackArg a j = stackArg b j := (h.2.2.1.2 j hj).trans (h.2.2.2.2 j hj).symm

theorem call_ct {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hn : c.noFrames = true)
    (ready : ∀ {g m t}, VG.Proof.Ed25519.Arm.SignCached.Ctx L g m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ P) (.call name c)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.SignCached.two_wp
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.1
    let rb := ready h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := Whole.CallReady.covers_state h.1 ra
    obtain ⟨cb, wb⟩ := Whole.CallReady.covers_state h.2.1 rb
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb⟩
  · intro t hc hs
    exact WP.mono (Whole.CallReady.wp hc (ready hc hs) correct hn) fun _ hu => ⟨hu, trivial⟩
  · intro t hc hs
    exact WP.mono (Whole.CallReady.wp hc (ready hc hs) correct hn) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Verified`. -/
section

/-! Merged from `Proof.Ed25519.Arm.SignCached.CTReady`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {s : State}

def reduce_ready (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184) (ha : VG.Proof.Ed25519.Arm.SignCached.ReduceArgs L d s) : Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have cov : Covers (VG.Proof.Ed25519.Arm.SignCached.reduceRd L ++ VG.Proof.Ed25519.Arm.SignCached.reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.Arm.SignCached.covers
    simp only [VG.Proof.Ed25519.Arm.SignCached.reduceRd, VG.Proof.Ed25519.Arm.SignCached.reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.digestWithin L)
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by omega))
    · exact .inr (VG.Proof.Ed25519.Arm.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.Arm.SignCached.reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.Arm.SignCached.writes
    simp only [VG.Proof.Ed25519.Arm.SignCached.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by omega))
    · exact .inr (.inr (VG.Proof.Ed25519.Arm.SignCached.scratchWithin L))
  exact ⟨VG.Proof.Ed25519.Arm.SignCached.reduceRd L, VG.Proof.Ed25519.Arm.SignCached.reduceWr L d, VG.Proof.Ed25519.Arm.SignCached.reduce_pre hL hd ha, cov, ws⟩

def base_ready (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.BaseArgs L s) : Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs s := by
  have cov : Covers (VG.Proof.Ed25519.Arm.SignCached.baseRd L ++ VG.Proof.Ed25519.Arm.SignCached.baseWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.Arm.SignCached.covers
    simp only [VG.Proof.Ed25519.Arm.SignCached.baseRd, VG.Proof.Ed25519.Arm.SignCached.baseWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by decide))
    · exact .inr (VG.Proof.Ed25519.Arm.SignCached.output_covered (VG.Proof.Ed25519.Arm.SignCached.baseWithin L))
    · exact .inr (VG.Proof.Ed25519.Arm.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.Arm.SignCached.baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.Arm.SignCached.writes
    simp only [VG.Proof.Ed25519.Arm.SignCached.baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (VG.Proof.Ed25519.Arm.SignCached.baseWithin L))
    · exact .inr (.inr (VG.Proof.Ed25519.Arm.SignCached.scratchWithin L))
  exact ⟨VG.Proof.Ed25519.Arm.SignCached.baseRd L, VG.Proof.Ed25519.Arm.SignCached.baseWr L, VG.Proof.Ed25519.Arm.SignCached.base_pre hL ha, cov, ws⟩

def mul_ready {g m} (hc : VG.Proof.Ed25519.Arm.SignCached.Ctx L g m s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.MulArgs L s) : Whole.CallReady scalarMulAddLocal L.E L.inputs L.outputs s := by
  have cov : Covers (VG.Proof.Ed25519.Arm.SignCached.mulRd L ++ VG.Proof.Ed25519.Arm.SignCached.mulWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.Arm.SignCached.covers
    simp only [VG.Proof.Ed25519.Arm.SignCached.mulRd, VG.Proof.Ed25519.Arm.SignCached.mulWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by decide))
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by decide))
    · exact .inl (VG.Proof.Ed25519.Arm.SignCached.fieldWithin L (by decide))
    · exact .inl ⟨0, by simp, by change 0 + 4 ≤ 248; decide⟩
    · exact .inr (VG.Proof.Ed25519.Arm.SignCached.output_covered (VG.Proof.Ed25519.Arm.SignCached.halfWithin L))
    · exact .inr (VG.Proof.Ed25519.Arm.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.Arm.SignCached.mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.Arm.SignCached.writes
    simp only [VG.Proof.Ed25519.Arm.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (VG.Proof.Ed25519.Arm.SignCached.halfWithin L))
    · exact .inr (.inr (VG.Proof.Ed25519.Arm.SignCached.scratchWithin L))
  exact ⟨VG.Proof.Ed25519.Arm.SignCached.mulRd L, VG.Proof.Ed25519.Arm.SignCached.mulWr L, VG.Proof.Ed25519.Arm.SignCached.mul_pre hc hL ha, cov, ws⟩

def init_ready (hL : L.Ok) (ha : s.gpr .r0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initArm Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre ha hL.nc, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (he : s.sp = L.E) {count p len : BitVec 32}
    (hi : VG.Proof.Ed25519.Arm.SignCached.Input L p len) (ha : VG.Proof.Ed25519.Arm.SignCached.UpdateArgs L count p len s) :
    Whole.CallReady Proof.Sha512.updateArm L.E L.inputs L.outputs s := by
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd L.E p len, Whole.hashWr L.scr, VG.Proof.Ed25519.Arm.SignCached.update_pre hL he ha hi, VG.Proof.Ed25519.Arm.SignCached.update_covers hi, hw⟩

def finalize_ready (hL : L.Ok) (he : s.sp = L.E) {count : BitVec 32} (ha : VG.Proof.Ed25519.Arm.SignCached.FinalArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeArm L.E L.inputs L.outputs s :=
  ⟨Whole.finalizeRd L.E, Whole.finalizeWr L.scr (L.E + 184), VG.Proof.Ed25519.Arm.SignCached.finalize_pre hL he ha,
    VG.Proof.Ed25519.Arm.SignCached.finalize_covers hL, VG.Proof.Ed25519.Arm.SignCached.final_writes hL⟩

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.CTBody`. -/
section
/-! Merged from `Proof.Ed25519.Arm.SignCached.CTHash`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.SignCached.AllArgs L [(.r0, .caller 5 0)] []))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512))
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.SignCached.call_ct (Proof.Sha512.Arm.Stream.init_verified _).1
    (Proof.Sha512.Arm.Stream.init_verified _).2.1 rfl
  · intro g m t _ hs
    have h := hs.1 (.r0, .caller 5 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at h
    rw [BitVec.add_zero] at h
    exact VG.Proof.Ed25519.Arm.SignCached.init_ready hL h
  · intro a b ar aw br bw h
    exact VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r0, .caller 5 0)) h (by simp) (by simp [linkRegs])

theorem update_call_ct (hL : L.Ok) (count : Nat) (p n : Value)
    (hi : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L p) (VG.Proof.Ed25519.Arm.SignCached.value L n)) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.SignCached.AllArgs L
      [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)] [p,n,.caller 5 192]))
      (.call Spec.Sha512.updateScratchApi.name Impl.Sha512.Arm.Stream.update)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.SignCached.call_ct Proof.Sha512.Arm.Stream.Update.update_verified.1
    Proof.Sha512.Arm.Stream.Update.update_verified.2.1 Whole.update_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 5 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at a0
    rw [BitVec.add_zero] at a0
    exact VG.Proof.Ed25519.Arm.SignCached.update_ready hL hc.sp hi ⟨a0, hs.1 (.r2, .const count) (by simp),
      hs.1 (.r3, .const 0) (by simp), hs.2 0 (by simp), hs.2 1 (by simp), hs.2 2 (by simp)⟩
  · intro a b ar aw br bw h
    have hsp := VG.Proof.Ed25519.Arm.SignCached.two_sp h
    exact ⟨hsp, VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r0, .caller 5 0)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r2, .const count)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r3, .const 0)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.stack_arg_eq h (j := 0) (by simp), VG.Proof.Ed25519.Arm.SignCached.stack_arg_eq h (j := 1) (by simp), VG.Proof.Ed25519.Arm.SignCached.stack_arg_eq h (j := 2) (by simp)⟩

theorem finalize_call_ct (hL : L.Ok) (n : Nat) (b : Bool) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.SignCached.AllArgs L
      [(.r0, .caller 5 0), (.r2, if b then .caller 4 n else .const n), (.r3, .const 0)]
      [.frame 184, .caller 5 192]))
      (.call Spec.Sha512.finalizeScratchApi.name Impl.Sha512.Arm.Stream.finalize)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.SignCached.call_ct Proof.Sha512.Arm.Stream.Finalize.finalize_verified.1
    Proof.Sha512.Arm.Stream.Finalize.finalize_verified.2.1 Whole.finalize_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 5 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at a0
    rw [BitVec.add_zero] at a0
    exact VG.Proof.Ed25519.Arm.SignCached.finalize_ready hL hc.sp ⟨a0,
      hs.1 (.r2, if b then .caller 4 n else .const n) (by simp),
      hs.1 (.r3, .const 0) (by simp), hs.2 0 (by decide), hs.2 1 (by decide)⟩
  · intro a c ar aw br bw h
    have hsp := VG.Proof.Ed25519.Arm.SignCached.two_sp h
    exact ⟨hsp, VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r0, .caller 5 0)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r2, if b then .caller 4 n else .const n)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r3, .const 0)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.stack_arg_eq h (j := 0) (by decide), VG.Proof.Ed25519.Arm.SignCached.stack_arg_eq h (j := 1) (by decide)⟩

theorem init_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) init
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (VG.Proof.Ed25519.Arm.SignCached.setup_ct hL ha hb [(.r0, .caller 5 0)] [] (by decide) (by simp [Whole.valid])
    (by decide) (by simp) (by simp [preserved])).seq (VG.Proof.Ed25519.Arm.SignCached.init_call_ct hL)

theorem update_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂)
    (count : Nat) (p n : Value) (hc : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L p) (VG.Proof.Ed25519.Arm.SignCached.value L n)) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True)
      (update (setup [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)] [p,n,.caller 5 192]))
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : ∀ x : Reg × Value, x ∈ [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)] →
      Whole.valid x.2 := by simp [Whole.valid,hc]
  have hvs : ∀ v ∈ [p,n,Value.caller 5 192], Whole.valid v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl)
    · exact hp
    · exact hn
    · simp [Whole.valid]
  exact (VG.Proof.Ed25519.Arm.SignCached.setup_ct hL ha hb _ _ (by simp) hv (by simp) hvs (by simp [preserved])).seq
    (VG.Proof.Ed25519.Arm.SignCached.update_call_ct hL count p n hi)

theorem finalize_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂)
    (n : Nat) (hn : n < 256) (b : Bool) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) (finalize n b)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (if b then .caller 4 n else .const n) := by
    cases b <;> simp [Whole.valid] <;> omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.r0, .caller 5 0),
      (.r2, if b then .caller 4 n else .const n), (.r3, .const 0)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · simp [Whole.valid]
    · exact hv
    · simp [Whole.valid]
  exact (VG.Proof.Ed25519.Arm.SignCached.setup_ct hL ha hb _ _ (by simp) hvall (by decide) (by simp [Whole.valid])
    (by simp [preserved])).seq (VG.Proof.Ed25519.Arm.SignCached.finalize_call_ct hL n b)

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.CTHashPipeline`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem hashSeed_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) (hashSeed)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hi : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L (.caller 1 0)) (VG.Proof.Ed25519.Arm.SignCached.value L (.const 32)) := by
    change VG.Proof.Ed25519.Arm.SignCached.Input L (L.seed + 0#32) 32#32
    rw [BitVec.add_zero]
    exact VG.Proof.Ed25519.Arm.SignCached.seed_input hL
  exact (VG.Proof.Ed25519.Arm.SignCached.init_ct hL ha hb).seq ((VG.Proof.Ed25519.Arm.SignCached.update_ct hL ha hb 0 (.caller 1 0) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hi).seq
    (VG.Proof.Ed25519.Arm.SignCached.finalize_ct hL ha hb 32 (by decide) false))

theorem hashNonce_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) (hashNonce)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hp : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L (.frame 56)) (VG.Proof.Ed25519.Arm.SignCached.value L (.const 32)) := VG.Proof.Ed25519.Arm.SignCached.prefix_input hL
  have hm : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L (.caller 3 0)) (VG.Proof.Ed25519.Arm.SignCached.value L (.caller 4 0)) := by
    change VG.Proof.Ed25519.Arm.SignCached.Input L (L.msg + 0#32) (L.len + 0#32)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact VG.Proof.Ed25519.Arm.SignCached.message_input hL
  exact (VG.Proof.Ed25519.Arm.SignCached.init_ct hL ha hb).seq ((VG.Proof.Ed25519.Arm.SignCached.update_ct hL ha hb 0 (.frame 56) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hp).seq
    ((VG.Proof.Ed25519.Arm.SignCached.update_ct hL ha hb 32 (.caller 3 0) (.caller 4 0)
      (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hm).seq
      (VG.Proof.Ed25519.Arm.SignCached.finalize_ct hL ha hb 32 (by decide) true)))

theorem hashChallenge_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) (hashChallenge)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have ho : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L (.caller 0 0)) (VG.Proof.Ed25519.Arm.SignCached.value L (.const 32)) := by
    change VG.Proof.Ed25519.Arm.SignCached.Input L (L.out + 0#32) 32#32
    rw [BitVec.add_zero]
    exact VG.Proof.Ed25519.Arm.SignCached.point_input hL
  have hk : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L (.caller 2 0)) (VG.Proof.Ed25519.Arm.SignCached.value L (.const 32)) := by
    change VG.Proof.Ed25519.Arm.SignCached.Input L (L.pk + 0#32) 32#32
    rw [BitVec.add_zero]
    exact VG.Proof.Ed25519.Arm.SignCached.key_input hL
  have hm : VG.Proof.Ed25519.Arm.SignCached.Input L (VG.Proof.Ed25519.Arm.SignCached.value L (.caller 3 0)) (VG.Proof.Ed25519.Arm.SignCached.value L (.caller 4 0)) := by
    change VG.Proof.Ed25519.Arm.SignCached.Input L (L.msg + 0#32) (L.len + 0#32)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact VG.Proof.Ed25519.Arm.SignCached.message_input hL
  exact (VG.Proof.Ed25519.Arm.SignCached.init_ct hL ha hb).seq ((VG.Proof.Ed25519.Arm.SignCached.update_ct hL ha hb 0 (.caller 0 0) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) ho).seq
    ((VG.Proof.Ed25519.Arm.SignCached.update_ct hL ha hb 32 (.caller 2 0) (.const 32)
      (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hk).seq
      ((VG.Proof.Ed25519.Arm.SignCached.update_ct hL ha hb 64 (.caller 3 0) (.caller 4 0)
        (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hm).seq
        (VG.Proof.Ed25519.Arm.SignCached.finalize_ct hL ha hb 64 (by decide) true))))

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.CTPrimitives`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (d : Nat) (hd : d + 32 ≤ 184) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.SignCached.AllArgs L [(.r0, .frame d), (.r1, .frame 184), (.r2, .caller 5 0)] []))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.Arm.scalarReduce)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.SignCached.call_ct scalarReduce_ok scalarReduce_ct VG.Proof.Ed25519.Arm.SignCached.reduce_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .frame d) (by simp)
    have a1 := hs.1 (.r1, .frame 184) (by simp)
    have a2 := hs.1 (.r2, .caller 5 0) (by simp)
    change t.gpr .r2 = L.scr + 0#32 at a2
    rw [BitVec.add_zero] at a2
    exact VG.Proof.Ed25519.Arm.SignCached.reduce_ready hL hd ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := VG.Proof.Ed25519.Arm.SignCached.two_sp h
    exact ⟨hsp, VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r0, .frame d)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r1, .frame 184)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r2, .caller 5 0)) h (by simp) (by simp [linkRegs])⟩

theorem base_call_ct (hL : L.Ok) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.SignCached.AllArgs L [(.r0, .caller 0 0), (.r1, .frame 88), (.r2, .caller 5 0)] []))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.SignCached.call_ct scalarBase_ok scalarBase_ct VG.Proof.Ed25519.Arm.SignCached.base_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 0 0) (by simp)
    change t.gpr .r0 = L.out + 0#32 at a0
    rw [BitVec.add_zero] at a0
    have a1 := hs.1 (.r1, .frame 88) (by simp)
    have a2 := hs.1 (.r2, .caller 5 0) (by simp)
    change t.gpr .r2 = L.scr + 0#32 at a2
    rw [BitVec.add_zero] at a2
    exact VG.Proof.Ed25519.Arm.SignCached.base_ready hL ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := VG.Proof.Ed25519.Arm.SignCached.two_sp h
    exact ⟨hsp, VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r0, .caller 0 0)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r1, .frame 88)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r2, .caller 5 0)) h (by simp) (by simp [linkRegs])⟩

theorem mul_call_ct (hL : L.Ok) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.SignCached.AllArgs L [(.r0, .caller 0 32), (.r1, .frame 88), (.r2, .frame 120), (.r3, .frame 24)] [.caller 5 0]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.Arm.scalarMulAdd)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.SignCached.call_ct scalarMulAdd_ok scalarMulAdd_ct VG.Proof.Ed25519.Arm.SignCached.mul_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 0 32) (by simp)
    have a1 := hs.1 (.r1, .frame 88) (by simp)
    have a2 := hs.1 (.r2, .frame 120) (by simp)
    have a3 := hs.1 (.r3, .frame 24) (by simp)
    have a4 := hs.2 0 (by decide)
    change stackArg t 0 = L.scr + 0#32 at a4
    rw [BitVec.add_zero] at a4
    exact VG.Proof.Ed25519.Arm.SignCached.mul_ready hc hL ⟨a0, a1, a2, a3, a4⟩
  · intro a b ar aw br bw h
    have hsp := VG.Proof.Ed25519.Arm.SignCached.two_sp h
    exact ⟨hsp, VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r0, .caller 0 32)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r1, .frame 88)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r2, .frame 120)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.call_gpr_eq (p := (.r3, .frame 24)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.Arm.SignCached.stack_arg_eq h (j := 0) (by decide)⟩

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.CTBlocks`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem copyWord_ct (k : Nat) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (copyWord k)) (fun a b => a.sp = b.sp) :=
  Whole.step_sp_ct (fun _ _ h => by simp only [addrs,h]) (Whole.frame_store_ct 0 (56+4*k) .r0)

theorem copyPrefix_ct :
    RelCT isa (fun a b => a.sp = b.sp) (.block copyPrefix) (fun a b => a.sp = b.sp) :=
  Whole.flatMap_sp_ct _ _ (fun _ _ => VG.Proof.Ed25519.Arm.SignCached.copyWord_ct _)

theorem saveSecret_ct (hL : L.Ok) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have ct := Whole.block_append_ct PublicKey.prune_sp_ct VG.Proof.Ed25519.Arm.SignCached.copyPrefix_ct
  refine VG.Proof.Ed25519.Arm.SignCached.two_wp (ct.mono (fun _ _ h => VG.Proof.Ed25519.Arm.SignCached.two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro t hc _
    exact WP.mono (VG.Proof.Ed25519.Arm.SignCached.saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (VG.Proof.Ed25519.Arm.SignCached.saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.Arm.SignCached.two_wp ((Whole.zeroWords_ct 6 56).mono (fun _ _ h => VG.Proof.Ed25519.Arm.SignCached.two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro t hc _
    exact WP.mono (VG.Proof.Ed25519.Arm.SignCached.wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (VG.Proof.Ed25519.Arm.SignCached.wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : VG.Proof.Ed25519.Arm.SignCached.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂)
    (d : Nat) (hd : d + 32 ≤ 184) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) (reduce d)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (.frame d) := by change d < 256; omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.r0, .frame d), (.r1, .frame 184), (.r2, .caller 5 0)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · exact hv
    · simp [Whole.valid]
    · simp [Whole.valid]
  exact (VG.Proof.Ed25519.Arm.SignCached.setup_ct hL ha hb _ [] (by simp) hvall (by decide) (by simp) (by simp [preserved])).seq
    (VG.Proof.Ed25519.Arm.SignCached.reduce_call_ct hL d hd)

theorem base_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (VG.Proof.Ed25519.Arm.SignCached.setup_ct hL ha hb [(.r0, .caller 0 0), (.r1, .frame 88), (.r2, .caller 5 0)] []
    (by decide) (by simp [Whole.valid]) (by decide) (by simp [Whole.valid]) (by simp [preserved])).seq
    (VG.Proof.Ed25519.Arm.SignCached.base_call_ct hL)

theorem mul_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith mulAddArgs "vg_ed25519_scalar_mul_add" Impl.Ed25519.Arm.scalarMulAdd)
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (VG.Proof.Ed25519.Arm.SignCached.setup_ct hL ha hb [(.r0, .caller 0 32), (.r1, .frame 88), (.r2, .frame 120),
    (.r3, .frame 24)] [.caller 5 0]
    (by decide) (by simp [Whole.valid]) (by decide) (by simp [Whole.valid]) (by simp [preserved])).seq
    (VG.Proof.Ed25519.Arm.SignCached.mul_call_ct hL)

theorem body_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) body
      (VG.Proof.Ed25519.Arm.SignCached.Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  ((VG.Proof.Ed25519.Arm.SignCached.hashSeed_ct hL ha hb).seq (VG.Proof.Ed25519.Arm.SignCached.saveSecret_ct hL)).seq
    (((VG.Proof.Ed25519.Arm.SignCached.hashNonce_ct hL ha hb).seq ((VG.Proof.Ed25519.Arm.SignCached.reduce_ct hL ha hb 88 (by decide)).seq
      (VG.Proof.Ed25519.Arm.SignCached.base_ct hL ha hb))).seq
      (((VG.Proof.Ed25519.Arm.SignCached.hashChallenge_ct hL ha hb).seq ((VG.Proof.Ed25519.Arm.SignCached.reduce_ct hL ha hb 120 (by decide)).seq
        (VG.Proof.Ed25519.Arm.SignCached.mul_ct hL ha hb))).seq (VG.Proof.Ed25519.Arm.SignCached.wipe_ct hL)))

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Entry`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm

def signCachedLocal : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let pk : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let msg : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 8192⟩
    let args : Region := ⟨State.addr s.sp,8⟩
    let stk : Region := ⟨State.addr s.sp - 280,280⟩
    s.rd = [seed, pk, msg, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧ out.Disjoint scr ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 64 = Spec.Ed25519.sign
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1

def lay (s : State) : VG.Proof.Ed25519.Arm.SignCached.Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, stackArg s 0, stackArg s 1, Whole.base s⟩

theorem entry_below {s : State} (h : signCachedLocal.pre s) : 280 ≤ s.sp.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _, _⟩ := h
  exact hb

theorem entry_top {s : State} (h : signCachedLocal.pre s) : s.sp.toNat + 8 ≤ 2 ^ 32 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _⟩ := h
  exact ht

theorem original_args {s : State} (hb : 280 ≤ s.sp.toNat) :
    (VG.Proof.Ed25519.Arm.SignCached.lay s).ORIGINALARGS = ⟨State.addr s.sp,8⟩ := by
  unfold Lay.ORIGINALARGS VG.Proof.Ed25519.Arm.SignCached.lay
  rw [Whole.base_addr hb]
  change (⟨State.addr s.sp - 280 + 280,8⟩ : Region) = _
  rw [BitVec.sub_add_cancel]

theorem stack_eq {s : State} (hb : 280 ≤ s.sp.toNat) :
    Whole.stack s = ⟨State.addr s.sp-280,280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr hb]

theorem entry_writes {s : State} (h : signCachedLocal.pre s) :
    ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  have hb := VG.Proof.Ed25519.Arm.SignCached.entry_below h
  obtain ⟨_, hw, _, _, _, _, _, _, _, _, _, ko, _, _, _, kc, _⟩ := h
  intro r hr
  rw [hw] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [VG.Proof.Ed25519.Arm.SignCached.stack_eq hb]
  rcases hr with rfl | rfl
  · exact ko
  · exact kc

theorem lay_ok {s : State} (h : signCachedLocal.pre s) : (VG.Proof.Ed25519.Arm.SignCached.lay s).Ok := by
  obtain ⟨_, _, os, op, om, oa, oc, sc, pc, mc, ac, ko, ks, kp, km, kc, no, ns, np, nm, nc, hb, _, _⟩ := h
  have fr : Region.Sub (Whole.FR (Whole.base s)) (Whole.stack s) := Region.sub_prefix (by decide)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (Whole.stack s) := Offset.sub_base _ (by decide)
  rw [← VG.Proof.Ed25519.Arm.SignCached.stack_eq hb] at ko ks kp km kc
  refine ⟨?_, ?_, oc, ko.sub_left fr, no, ?_, ?_, kc.sub_left fr, np, nm, ns, nc⟩
  · have he := Whole.base_top (s := s) hb
    have hs := s.sp.isLt
    change (Whole.base s).toNat + 272 ≤ 2 ^ 32
    omega
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact os
    · exact op
    · exact om
    · rw [VG.Proof.Ed25519.Arm.SignCached.original_args hb]; exact oa
    · exact (ko.sub_left ar).symm
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact sc
    · exact pc
    · exact mc
    · rw [VG.Proof.Ed25519.Arm.SignCached.original_args hb]; exact ac
    · exact kc.sub_left ar
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact ks.sub_left fr
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)

theorem entry_ctx {s p : State} (h : signCachedLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    VG.Proof.Ed25519.Arm.SignCached.Ctx (VG.Proof.Ed25519.Arm.SignCached.lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (VG.Proof.Ed25519.Arm.SignCached.lay s).inputs (VG.Proof.Ed25519.Arm.SignCached.lay s).outputs _
  simp only [Lay.inputs, VG.Proof.Ed25519.Arm.SignCached.original_args (VG.Proof.Ed25519.Arm.SignCached.entry_below h)]
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, Lay.outputs,
    Lay.SEED, Lay.PK, Lay.MSG, Lay.OUT, Lay.SCR, Lay.ARGS, Whole.ARGS, show BitVec.ofNat 64 248 = (248 : Addr) from rfl, VG.Proof.Ed25519.Arm.SignCached.lay,
    List.cons_append, List.nil_append] using hc

theorem entry_regions {s : State} (h : signCachedLocal.pre s) :
    (VG.Proof.Ed25519.Arm.SignCached.lay s).inputs = Whole.bodyRd s ∧ (VG.Proof.Ed25519.Arm.SignCached.lay s).outputs = s.wr := by
  simp only [Lay.inputs, VG.Proof.Ed25519.Arm.SignCached.original_args (VG.Proof.Ed25519.Arm.SignCached.entry_below h)]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1,
    Lay.SEED, Lay.PK, Lay.MSG, Lay.OUT, Lay.SCR, Lay.ARGS, Whole.ARGS,
    show BitVec.ofNat 64 248 = (248 : Addr) from rfl, VG.Proof.Ed25519.Arm.SignCached.lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_args {s p : State} (h : signCachedLocal.pre s)
    (hp : Whole.Saved (Whole.entered s) 6 p) : VG.Proof.Ed25519.Arm.SignCached.Arguments (VG.Proof.Ed25519.Arm.SignCached.lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words (VG.Proof.Ed25519.Arm.SignCached.entry_below h) (by decide : 6 ≤ 6) (VG.Proof.Ed25519.Arm.SignCached.entry_top h) hp hj
  have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
      Nat.reduceSub, Nat.mul_zero, BitVec.add_zero, Lay.value, VG.Proof.Ed25519.Arm.SignCached.lay,
      stackArg, stackArgAddr] using hw

theorem entry_read {s : State} (h : signCachedLocal.pre s) : ∀ j < 6, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4*(j-4)))) 4 := by
  intro j hj h4
  have ht := VG.Proof.Ed25519.Arm.SignCached.entry_top h
  rw [addr_add (by omega)]
  exact ⟨⟨State.addr s.sp,8⟩, List.mem_append_left _ (by rw [h.1]; simp),
    Offset.contains_base _ (by omega) (by omega)⟩

theorem entry_input {s : State} (h : signCachedLocal.pre s) {m : Mem}
    (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  have hb := VG.Proof.Ed25519.Arm.SignCached.entry_below h
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, _, _, ks, kp, km, _⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [← VG.Proof.Ed25519.Arm.SignCached.stack_eq hb] at ks kp km
  rcases hr with rfl | rfl | rfl | rfl
  · exact ks.symm
  · exact kp.symm
  · exact km.symm
  · rw [← VG.Proof.Ed25519.Arm.SignCached.original_args hb]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm

theorem entry_key {s p : State} (h : signCachedLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Spec.Ed25519.bytesAt p.mem (State.addr (VG.Proof.Ed25519.Arm.SignCached.lay s).pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt p.mem (State.addr (VG.Proof.Ed25519.Arm.SignCached.lay s).seed) 32) := by
  have hk : Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk⟩ := h
    exact hk
  have hf := Whole.saved_frame (VG.Proof.Ed25519.Arm.SignCached.entry_below h) hp
  have hp' := VG.Proof.Ed25519.Arm.SignCached.entry_input h hf (r := ⟨State.addr (s.gpr .r2), 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  have hs' := VG.Proof.Ed25519.Arm.SignCached.entry_input h hf (r := ⟨State.addr (s.gpr .r1), 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r2)) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r1)) 32)
  rw [hp', hs']
  exact hk

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.CT`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

theorem lay_eq {s t : State} (hp : signCachedLocal.pub s t) : VG.Proof.Ed25519.Arm.SignCached.lay s = VG.Proof.Ed25519.Arm.SignCached.lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5⟩ := hp
  simp only [VG.Proof.Ed25519.Arm.SignCached.lay, Whole.base, sp, h0, h1, h2, h3, h4, h5]

theorem signCached_ct :
    ConstantTime isa signCachedLocal.pre signCachedLocal.pub VG.Impl.Ed25519.Arm.SignCached.code := by
  refine Whole.wrap_ct (by decide) (fun _ _ hp => hp.1)
    (fun _ h => VG.Proof.Ed25519.Arm.SignCached.entry_below h) (fun _ h => VG.Proof.Ed25519.Arm.SignCached.entry_top h) (fun _ h => VG.Proof.Ed25519.Arm.SignCached.entry_read h) ?_ ?_
  · intro s hs p hp
    exact WP.mono (VG.Proof.Ed25519.Arm.SignCached.body_ok (VG.Proof.Ed25519.Arm.SignCached.entry_ctx hs hp) (VG.Proof.Ed25519.Arm.SignCached.lay_ok hs) (VG.Proof.Ed25519.Arm.SignCached.entry_args hs hp) (VG.Proof.Ed25519.Arm.SignCached.entry_key hs hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := VG.Proof.Ed25519.Arm.SignCached.lay_eq hp
    have hq : VG.Proof.Ed25519.Arm.SignCached.Ctx (VG.Proof.Ed25519.Arm.SignCached.lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ VG.Proof.Ed25519.Arm.SignCached.entry_ctx ht hqb
    have hqa : VG.Proof.Ed25519.Arm.SignCached.Arguments (VG.Proof.Ed25519.Arm.SignCached.lay s) q.mem := he ▸ VG.Proof.Ed25519.Arm.SignCached.entry_args ht hqb
    exact ⟨(VG.Proof.Ed25519.Arm.SignCached.body_ct (VG.Proof.Ed25519.Arm.SignCached.lay_ok hs) (VG.Proof.Ed25519.Arm.SignCached.entry_args hs hpa) hqa _ _ _ _ _ _
      ⟨VG.Proof.Ed25519.Arm.SignCached.entry_ctx hs hpa, hq, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Correct`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

theorem body_noFrames : body.noFrames = true := by
  simp only [body, secretCode, nonceCode, challengeCode, hashSeed, hashNonce, hashChallenge,
    init, update, finalize, reduce, Impl.Ed25519.Arm.Whole.callWith, Code.noFrames,
    Impl.Sha512.Arm.Stream.init, Bool.and_self]
  rw [VG.Proof.Ed25519.Arm.SignCached.reduce_noFrames, VG.Proof.Ed25519.Arm.SignCached.base_noFrames, VG.Proof.Ed25519.Arm.SignCached.mul_noFrames]
  rfl

theorem signCached_ok {s : State} (h : signCachedLocal.pre s) :
    WP isa VG.Impl.Ed25519.Arm.SignCached.code s fun u => abiPreserved s u ∧ signCachedLocal.post s u := by
  have hw := Whole.wrap_ok VG.Proof.Ed25519.Arm.SignCached.body_noFrames (by decide : 6 ≤ 6) (VG.Proof.Ed25519.Arm.SignCached.entry_below h) (VG.Proof.Ed25519.Arm.SignCached.entry_top h) (VG.Proof.Ed25519.Arm.SignCached.entry_read h) (VG.Proof.Ed25519.Arm.SignCached.entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (State.addr (s.gpr .r0)) 64 = Spec.Ed25519.sign
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 32)
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r3)) (stackArg s 0).toNat))
    (fun p hp => WP.mono (VG.Proof.Ed25519.Arm.SignCached.body_ok (VG.Proof.Ed25519.Arm.SignCached.entry_ctx h hp) (VG.Proof.Ed25519.Arm.SignCached.lay_ok h) (VG.Proof.Ed25519.Arm.SignCached.entry_args h hp) (VG.Proof.Ed25519.Arm.SignCached.entry_key h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (VG.Proof.Ed25519.Arm.SignCached.lay s).inputs (VG.Proof.Ed25519.Arm.SignCached.lay s).outputs u at hu
        rw [(VG.Proof.Ed25519.Arm.SignCached.entry_regions h).1, (VG.Proof.Ed25519.Arm.SignCached.entry_regions h).2] at hu
        exact hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs := VG.Proof.Ed25519.Arm.SignCached.entry_input h hf (r := ⟨State.addr (s.gpr .r1), 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  have hm := VG.Proof.Ed25519.Arm.SignCached.entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by have := (stackArg s 0).isLt; change (stackArg s 0).toNat ≤ 2 ^ 64; omega)
  change Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r0)) 64 = _
  rw [hp, hs, hm]

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Contract`. -/
section
/-! Merged from `Proof.Ed25519.Arm.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey VG.Proof.Ed25519.Arm.SignCached.satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [VG.Proof.Ed25519.Arm.SignCached.satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3020 then VG.Proof.Ed25519.Arm.SignCached.satKey[a.toNat - 0x3000]?.getD 0
  else if a = 0x9005 then 0x50 else 0

theorem sat_seed : Spec.Ed25519.bytesAt VG.Proof.Ed25519.Arm.SignCached.satMem 0x2000 32 = VG.Proof.Ed25519.Arm.SignCached.satSeed := by
  unfold VG.Proof.Ed25519.Arm.SignCached.satSeed Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold VG.Proof.Ed25519.Arm.SignCached.satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed25519.bytesAt VG.Proof.Ed25519.Arm.SignCached.satMem 0x3000 32 = VG.Proof.Ed25519.Arm.SignCached.satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, VG.Proof.Ed25519.Arm.SignCached.satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Ed25519.Arm.SignCached.satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, show 0x3000 + i < 0x3020 from by omega, ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := VG.Proof.Ed25519.Arm.SignCached.satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩, ⟨0x9000, 8⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed25519.signCachedContract Arm.abi 280).pre s := by
  refine ⟨VG.Proof.Ed25519.Arm.SignCached.satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, VG.Proof.Ed25519.Arm.SignCached.satState]
    sig_and_intros
    · decide +kernel
    · decide +kernel
    · change Spec.Ed25519.bytesAt VG.Proof.Ed25519.Arm.SignCached.satMem 0x3000 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt VG.Proof.Ed25519.Arm.SignCached.satMem 0x2000 32)
      rw [VG.Proof.Ed25519.Arm.SignCached.sat_seed, VG.Proof.Ed25519.Arm.SignCached.sat_key]
      rfl

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm

theorem signCached_implies : signCachedLocal.Implies (Spec.Ed25519.signCachedContract Arm.abi 280) where
  pre := by
    intro s h
    sig_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, VG.Proof.Ed25519.Arm.SignCached.signCachedLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr] at h
    sig_split h
    sig_reduce [VG.Proof.Ed25519.Arm.SignCached.signCachedLocal, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
    sig_simp [] []
    simp only [BitVec.add_zero, show (280#64) = (280 : Addr) from rfl] at *
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, VG.Proof.Ed25519.Arm.SignCached.signCachedLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, VG.Proof.Ed25519.Arm.SignCached.signCachedLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  sat := VG.Proof.Ed25519.Arm.SignCached.sat

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

theorem signCached_verified :
    Verified Arm.target VG.Impl.Ed25519.Arm.SignCached.code (Spec.Ed25519.signCachedContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => VG.Proof.Ed25519.Arm.SignCached.signCached_ok h) VG.Proof.Ed25519.Arm.SignCached.signCached_ct (.refl signCached_implies.sat_left))
    VG.Proof.Ed25519.Arm.SignCached.signCached_implies

end VG.Proof.Ed25519.Arm.SignCached

end
