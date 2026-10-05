import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyVerified
import VerifiedGarbage.Proof.Sha512.Scratch
import VerifiedGarbage.Impl.Ed25519.Arm.VerifyMessage
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Body`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Layout`. -/
section

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm

structure Lay where
  pk : BitVec 32
  msg : BitVec 32
  len : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay)
abbrev SIG : Region := ⟨State.addr L.sig, 64⟩
abbrev PK : Region := ⟨State.addr L.pk, 32⟩
abbrev MSG : Region := ⟨State.addr L.msg, L.len.toNat⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
abbrev ARGS : Region := ⟨State.addr L.E + BitVec.ofNat 64 248, 24⟩
abbrev FR : Region := Whole.FR L.E
abbrev ORIGINALARGS : Region := ⟨State.addr L.E + 280, 4⟩
def inputs : List Region := [L.PK, L.MSG, L.SIG, L.ORIGINALARGS, L.ARGS]
def outputs : List Region := [L.SCR]
def value (j : Nat) : BitVec 32 :=
  match j with | 0 => L.pk | 1 => L.msg | 2 => L.len | 3 => L.sig | _ => L.scr

structure Ok : Prop where
  top : L.E.toNat + 272 ≤ 2 ^ 32
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.FR.Disjoint r
  kc : L.FR.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 32
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  ns : L.sig.toNat + 64 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

/-- The scratch allocation leaves enough address space for either hash prefix. -/
theorem Lay.Ok.message_bound {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 32 := by
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


abbrev Ctx (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

namespace Ctx
variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem input_bytes (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t) (hL : L.Ok)
    {r : Region} (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem r.base r.len = Spec.Ed25519.bytesAt m₀ r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine Frame.bytes hc.frame ?_ hn (List.mem_range.mp hi)
  intro R hR
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  · exact hL.sc r hr
  · exact (hL.ks r hr).symm

theorem arg_word (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 6) :
    t.mem.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm

end Ctx
end VG.Proof.Ed25519.Arm.VerifyMessage

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Args`. -/
section

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def Arguments (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (m : Mem) : Prop :=
  ∀ j < 5, m.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 = L.value j

def value (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

def valid : Value → Prop
  | .const n => n < 65536
  | .frame d => d < 256
  | .caller j d => j < 5 ∧ d < 256

theorem valid_whole {v : Value} (h : VG.Proof.Ed25519.Arm.VerifyMessage.valid v) : Whole.valid v := by
  cases v with
  | const n => exact h
  | frame d => exact h
  | caller j d => exact ⟨by have := h.1; omega,h.2⟩

def OutArgs (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (args : List (Reg × Value)) (s : State) : Prop :=
  ∀ p ∈ args, s.gpr p.1 = VG.Proof.Ed25519.Arm.VerifyMessage.value L p.2

def StackArgs (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (vs : List Value) (s : State) : Prop :=
  ∀ j (hj : j < vs.length), stackArg s j = VG.Proof.Ed25519.Arm.VerifyMessage.value L (vs[j]'hj)

theorem Ctx.value (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀) {v : Value} (hv : VG.Proof.Ed25519.Arm.VerifyMessage.valid v) :
    Whole.value L.E s.mem v = VG.Proof.Ed25519.Arm.VerifyMessage.value L v := by
  cases v with
  | const n => rfl
  | frame d => rfl
  | caller j d =>
    change _ + BitVec.ofNat 32 d = _ + BitVec.ofNat 32 d
    rw [hc.arg_word hL (by have := hv.1; omega), ha j hv.1]

theorem args_regs_ok (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed25519.Arm.VerifyMessage.valid p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (VG.Impl.Ed25519.Arm.Whole.setup args [])) s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧ t.mem = s.mem ∧ VG.Proof.Ed25519.Arm.VerifyMessage.OutArgs L args t := by
  have rd : ∀ j < 6, InRegions (s.rd ++ s.wr) (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 4 := by
    intro j hj
    refine ⟨L.ARGS, ?_, Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)⟩
    rw [hc.rd]
    exact List.mem_append_left _ (by simp [Lay.inputs])
  refine WP.mono (Whole.setupRegs_ok hc.sp hL.top hn (fun p hp => VG.Proof.Ed25519.Arm.VerifyMessage.valid_whole (hv p hp)) rd) fun t ⟨ht, hargs⟩ => ?_
  refine ⟨hc.regs ht.rd ht.wr ht.sp ?_ ht.mem, ht.mem, ?_⟩
  · intro r hpres _
    apply ht.regs
    intro hh
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hh
    exact hr p hp (he ▸ hpres)
  · intro p hp
    exact (hargs p hp).trans (hc.value hL ha (hv p hp))

theorem args_ok (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀)
    {args : List (Reg × Value)} {stack : List Value}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed25519.Arm.VerifyMessage.valid p.2)
    (hs : stack.length ≤ 6) (hvs : ∀ v ∈ stack, VG.Proof.Ed25519.Arm.VerifyMessage.valid v)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (VG.Impl.Ed25519.Arm.Whole.setup args stack)) s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧
      Frame [⟨State.addr L.E, 24⟩] s.mem t.mem ∧ VG.Proof.Ed25519.Arm.VerifyMessage.OutArgs L args t ∧ VG.Proof.Ed25519.Arm.VerifyMessage.StackArgs L stack t := by
  refine WP.mono (Whole.Ctx.setup hc hL.top hn (fun p hp => VG.Proof.Ed25519.Arm.VerifyMessage.valid_whole (hv p hp)) hs (fun v hv => VG.Proof.Ed25519.Arm.VerifyMessage.valid_whole (hvs v hv)) (by simp [Lay.inputs]) hr)
    fun t ⟨ht, hf, hg, hstack⟩ => ⟨ht, hf, ?_, ?_⟩
  · intro p hp
    exact (hg p hp).trans (hc.value hL ha (hv p hp))
  · intro j hj
    exact (hstack j hj).trans (hc.value hL ha (hvs _ (List.getElem_mem hj)))

end VG.Proof.Ed25519.Arm.VerifyMessage

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Calls`. -/
section

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm

variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay}

def field (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (d : Nat) : Region := ⟨State.addr L.E + BitVec.ofNat 64 d, 32⟩
def digest (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : Region := ⟨State.addr L.E + BitVec.ofNat 64 184, 64⟩
theorem fieldWithin (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) {d : Nat} (hd : d + 32 ≤ 248) : Whole.Within (VG.Proof.Ed25519.Arm.VerifyMessage.field L d) L.FR :=
  ⟨d, rfl, hd⟩
theorem digestWithin (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : Whole.Within (VG.Proof.Ed25519.Arm.VerifyMessage.digest L) L.FR := ⟨184, rfl, by change 184 + 64 ≤ 248; decide⟩
theorem scratchWithin (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩

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

theorem scratch_covered (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within L.SCR R :=
  ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed25519.Arm.VerifyMessage.scratchWithin L⟩

theorem writes {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ Whole.Within r L.SCR) :
    ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rcases h r hr with hf | hs
  · exact .inl hf
  · exact .inr ⟨L.SCR,by simp [Lay.outputs],hs⟩

theorem field_scr (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 248) :
    (VG.Proof.Ed25519.Arm.VerifyMessage.field L d).Disjoint L.SCR := hL.kc.sub_left (VG.Proof.Ed25519.Arm.VerifyMessage.fieldWithin L hd).sub

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

end VG.Proof.Ed25519.Arm.VerifyMessage

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Equation`. -/
section

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def signWord (b : Bool) : BitVec 32 := if b then 1 else 0

def challenge (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : Region := ⟨State.addr L.E+120,64⟩
def equationRd (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : List Region := [L.PK,L.SIG,VG.Proof.Ed25519.Arm.VerifyMessage.challenge L]
def equationWr (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : List Region := [L.SCR]
def EqArgs (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (s : State) : Prop := s.gpr .r0 = L.pk ∧
  s.gpr .r1 = L.sig ∧ s.gpr .r2 = L.E+120 ∧ s.gpr .r3 = L.scr

theorem equation_noFrames : verifyEquation.noFrames = true := by lit_decide

theorem challengeWithin (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : Whole.Within (VG.Proof.Ed25519.Arm.VerifyMessage.challenge L) L.FR :=
  ⟨120,rfl,by change 120+64≤248; decide⟩

theorem equation_pre (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.EqArgs L s) :
    verifyLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.Arm.VerifyMessage.equationRd L) (VG.Proof.Ed25519.Arm.VerifyMessage.equationWr L)) := by
  have ac : State.addr (L.E+120) = State.addr L.E+120 := VG.Proof.Ed25519.Arm.VerifyMessage.frame_addr hL (d := 120) (by decide)
  simp only [verifyLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,ac]
  exact ⟨rfl,rfl,hL.sc _ (by simp [Lay.inputs]),hL.sc _ (by simp [Lay.inputs]),
    hL.kc.sub_left (VG.Proof.Ed25519.Arm.VerifyMessage.challengeWithin L).sub,hL.np,hL.ns,VG.Proof.Ed25519.Arm.VerifyMessage.frame_fit hL (by decide),hL.nc⟩

theorem equation_covers : Covers (VG.Proof.Ed25519.Arm.VerifyMessage.equationRd L ++ VG.Proof.Ed25519.Arm.VerifyMessage.equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
  apply VG.Proof.Ed25519.Arm.VerifyMessage.covers
  simp only [VG.Proof.Ed25519.Arm.VerifyMessage.equationRd,VG.Proof.Ed25519.Arm.VerifyMessage.equationWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact .inr ⟨L.PK,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inr ⟨L.SIG,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.challengeWithin L)
  · exact .inr (VG.Proof.Ed25519.Arm.VerifyMessage.scratch_covered L)

theorem equation_writes : ∀ r ∈ VG.Proof.Ed25519.Arm.VerifyMessage.equationWr L,
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨L.SCR,by simp [Lay.outputs],VG.Proof.Ed25519.Arm.VerifyMessage.scratchWithin L⟩

theorem equation_call (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.EqArgs L s) :
    WP isa (.call "vg_ed25519_verify_equation" verifyEquation) s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧
      t.gpr .r0 = VG.Proof.Ed25519.Arm.VerifyMessage.signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem (State.addr L.pk) 32) (Spec.Ed25519.bytesAt s.mem (State.addr L.sig) 64)
        (Spec.Ed25519.bytesAt s.mem (State.addr L.E+120) 64)) := by
  refine Whole.call_ok hc verify_ok VG.Proof.Ed25519.Arm.VerifyMessage.equation_noFrames (VG.Proof.Ed25519.Arm.VerifyMessage.equation_pre hL ha)
    VG.Proof.Ed25519.Arm.VerifyMessage.equation_covers VG.Proof.Ed25519.Arm.VerifyMessage.equation_writes fun t ht _ hp => ⟨ht,?_⟩
  change (t.gpr .r0).toNat = (if Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r0)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 64)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r2)) 64) then 1 else 0) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),ha.1,ha.2.1,ha.2.2.1] at hp
  have ac : State.addr (L.E+120) = State.addr L.E+120 := VG.Proof.Ed25519.Arm.VerifyMessage.frame_addr hL (d := 120) (by decide)
  rw [ac] at hp
  apply BitVec.eq_of_toNat_eq
  rw [hp]
  cases Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (State.addr L.pk) 32) (Spec.Ed25519.bytesAt s.mem (State.addr L.sig) 64) (Spec.Ed25519.bytesAt s.mem (State.addr L.E+120) 64) <;> rfl

theorem equation_step (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.Arm.Whole.callWith VG.Impl.Ed25519.Arm.VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation) s
      fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧ t.gpr .r0 = VG.Proof.Ed25519.Arm.VerifyMessage.signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem (State.addr L.pk) 32) (Spec.Ed25519.bytesAt s.mem (State.addr L.sig) 64)
        (Spec.Ed25519.bytesAt s.mem (State.addr L.E+120) 64)) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.args_regs_ok hc hL ha
    (args := [(.r0,.caller 0 0),(.r1,.caller 3 0),(.r2,.frame 120),(.r3,.caller 4 0)])
    (by simp) (by simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid]) (by simp [preserved]))
    fun u ⟨hu,hm,hav⟩ => ?_)
  have a0 := hav (.r0,.caller 0 0) (by simp)
  have a1 := hav (.r1,.caller 3 0) (by simp)
  have a2 := hav (.r2,.frame 120) (by simp)
  have a3 := hav (.r3,.caller 4 0) (by simp)
  change u.gpr .r0 = L.pk+0#32 at a0
  change u.gpr .r1 = L.sig+0#32 at a1
  change u.gpr .r3 = L.scr+0#32 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  refine WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.equation_call hu hL ⟨a0,a1,a2,a3⟩) fun t ⟨ht,hp⟩ => ⟨ht,?_⟩
  rw [hm] at hp
  exact hp

end VG.Proof.Ed25519.Arm.VerifyMessage

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Body`. -/
section

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashSteps`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashReady`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashInputs`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashFrame`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay}

def slots (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : Region := ⟨State.addr L.E, 24⟩
def hashWrites (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : List Region := [L.SCR, VG.Proof.Ed25519.Arm.VerifyMessage.slots L, VG.Proof.Ed25519.Arm.VerifyMessage.digest L]

theorem setup_frame {m n : Mem} (hf : Frame [VG.Proof.Ed25519.Arm.VerifyMessage.slots L] m n) : Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) m n :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨VG.Proof.Ed25519.Arm.VerifyMessage.slots L, by simp [VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites], fun _ h => h⟩

theorem hash_frame {m n : Mem} {rs : List Region} (hf : Frame rs m n)
    (hw : ∀ r ∈ rs, Whole.Within r L.SCR ∨ Whole.Within r (VG.Proof.Ed25519.Arm.VerifyMessage.digest L)) : Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) m n := by
  refine hf.sub fun r hr => ?_
  rcases hw r hr with hc | hd
  · exact ⟨L.SCR, by simp [VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites], hc.sub⟩
  · exact ⟨VG.Proof.Ed25519.Arm.VerifyMessage.digest L, by simp [VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites], hd.sub⟩

theorem frame_bytes {m n : Mem} {ws : List Region} (hf : Frame ws m n) (r : Region)
    (hd : ∀ w ∈ ws, r.Disjoint w) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt n r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem setup_field_bytes {m n : Mem} (hf : Frame [VG.Proof.Ed25519.Arm.VerifyMessage.slots L] m n)
    {d : Nat} (hd : d + 32 ≤ 248) (hmin : 24 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.Arm.VerifyMessage.frame_bytes hf (VG.Proof.Ed25519.Arm.VerifyMessage.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ hmin (by omega)

theorem setup_repr {m n : Mem} (hL : L.Ok) (hf : Frame [VG.Proof.Ed25519.Arm.VerifyMessage.slots L] m n) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 m (State.addr L.scr) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 n (State.addr L.scr) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := m) ?_ hr
  intro i hi
  exact hf.bytes (R := ⟨State.addr L.scr, 192⟩) (by
    rintro r hm; rw [List.mem_singleton.mp hm]
    exact (hL.kc.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by decide)))
    (by change 192 ≤ 2 ^ 64; decide) hi

theorem hash_field_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) m n)
    {d : Nat} (hd : d + 32 ≤ 184) (hmin : 24 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.Arm.VerifyMessage.frame_bytes hf (VG.Proof.Ed25519.Arm.VerifyMessage.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.Proof.Ed25519.Arm.VerifyMessage.field_scr hL (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay}

structure Input (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (p n : BitVec 32) : Prop where
  cover : Whole.Within ⟨State.addr p, n.toNat⟩ L.FR ∨
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨State.addr p, n.toNat⟩ R
  scratch : Region.Disjoint ⟨State.addr p, n.toNat⟩ L.SCR
  args : Region.Disjoint ⟨State.addr p, n.toNat⟩ (VG.Proof.Ed25519.Arm.VerifyMessage.slots L)
  fit : p.toNat + n.toNat ≤ 2 ^ 32

theorem input_self {r : Region} (hr : r ∈ L.inputs) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨r, List.mem_append_left _ hr, 0, by simp, by simp⟩

theorem input_slots (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) : r.Disjoint (VG.Proof.Ed25519.Arm.VerifyMessage.slots L) :=
  (hL.ks _ hr).symm.sub_right (Region.sub_prefix (by decide))

theorem key_input (hL : L.Ok) : VG.Proof.Ed25519.Arm.VerifyMessage.Input L L.pk 32 :=
  ⟨.inr (VG.Proof.Ed25519.Arm.VerifyMessage.input_self (r := L.PK) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    VG.Proof.Ed25519.Arm.VerifyMessage.input_slots hL (by simp [Lay.inputs]), hL.np⟩

theorem message_input (hL : L.Ok) : VG.Proof.Ed25519.Arm.VerifyMessage.Input L L.msg L.len :=
  ⟨.inr (VG.Proof.Ed25519.Arm.VerifyMessage.input_self (r := L.MSG) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    VG.Proof.Ed25519.Arm.VerifyMessage.input_slots hL (by simp [Lay.inputs]), hL.nm⟩

theorem signature_input (hL : L.Ok) : VG.Proof.Ed25519.Arm.VerifyMessage.Input L L.sig 32 := by
  have sub : Region.Sub ⟨State.addr L.sig,32⟩ L.SIG := Region.sub_prefix (by decide)
  exact ⟨.inr ⟨L.SIG,by simp [Lay.inputs],0,by simp,by change 0+32≤64; decide⟩,
    (hL.sc _ (by simp [Lay.inputs])).sub_left sub,
    (VG.Proof.Ed25519.Arm.VerifyMessage.input_slots hL (by simp [Lay.inputs])).sub_left sub,by have := hL.ns; change L.sig.toNat+32≤2^32; omega⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay}

theorem shaWithin (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : Whole.Within (Whole.SHA L.scr) L.SCR :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩
theorem workWithin (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : Whole.Within (Whole.WORK L.scr) L.SCR :=
  ⟨192, rfl, by change 192 + 272 ≤ 8192; decide⟩
theorem argsWithin (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) {n : Nat} (hn : n ≤ 248) :
    Whole.Within (Whole.CALLARGS L.E n) L.FR := ⟨0, by simp, by change 0 + n ≤ 248; omega⟩

theorem init_frame {m n : Mem} (hf : Frame (Whole.initWr L.scr) m n) : Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) m n := by
  apply VG.Proof.Ed25519.Arm.VerifyMessage.hash_frame hf
  intro r hr; rw [List.mem_singleton.mp hr]
  exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.shaWithin L)

theorem update_frame {m n : Mem} (hf : Frame (Whole.hashWr L.scr) m n) : Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) m n := by
  apply VG.Proof.Ed25519.Arm.VerifyMessage.hash_frame hf
  simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.shaWithin L)
  · exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.workWithin L)

theorem final_addr (hL : L.Ok) : State.addr (L.E + 184) = State.addr L.E + 184 :=
  VG.Proof.Ed25519.Arm.VerifyMessage.frame_addr hL (d := 184) (by decide)

theorem finalize_frame (hL : L.Ok) {m n : Mem} (hf : Frame (Whole.finalizeWr L.scr (L.E + 184)) m n) :
    Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) m n := by
  apply VG.Proof.Ed25519.Arm.VerifyMessage.hash_frame hf
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.shaWithin L)
  · exact .inr ⟨0, by rw [VG.Proof.Ed25519.Arm.VerifyMessage.final_addr hL]; simp [VG.Proof.Ed25519.Arm.VerifyMessage.digest], by change 0 + 64 ≤ 64; decide⟩
  · exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.workWithin L)

theorem final_writes (hL : L.Ok) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 184),
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  apply VG.Proof.Ed25519.Arm.VerifyMessage.writes
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr (VG.Proof.Ed25519.Arm.VerifyMessage.shaWithin L)
  · exact .inl ⟨184, VG.Proof.Ed25519.Arm.VerifyMessage.final_addr hL, by change 184 + 64 ≤ 248; decide⟩
  · exact .inr (VG.Proof.Ed25519.Arm.VerifyMessage.workWithin L)

theorem update_covers {p n : BitVec 32} (hi : VG.Proof.Ed25519.Arm.VerifyMessage.Input L p n) :
    Covers (Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (L.inputs ++ L.FR :: L.outputs) := by
  apply VG.Proof.Ed25519.Arm.VerifyMessage.covers
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hi.cover
  · exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.argsWithin L (by decide))
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed25519.Arm.VerifyMessage.shaWithin L⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed25519.Arm.VerifyMessage.workWithin L⟩

theorem finalize_covers (hL : L.Ok) :
    Covers (Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 184)) (L.inputs ++ L.FR :: L.outputs) := by
  apply VG.Proof.Ed25519.Arm.VerifyMessage.covers
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.argsWithin L (by decide))
  · rcases VG.Proof.Ed25519.Arm.VerifyMessage.final_writes hL r hr with hf | ⟨R, hR, hw⟩
    · exact .inl hf
    · exact .inr ⟨R, List.mem_append_right _ hR, hw⟩

def UpdateArgs (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (count p n : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = L.scr ∧ t.gpr .r2 = count ∧ t.gpr .r3 = 0 ∧
    stackArg t 0 = p ∧ stackArg t 1 = n ∧ stackArg t 2 = L.scr + 192

def FinalArgs (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (count : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = L.scr ∧ t.gpr .r2 = count ∧ t.gpr .r3 = 0 ∧
    stackArg t 0 = L.E + 184 ∧ stackArg t 1 = L.scr + 192

theorem update_pre {t : State} (hL : L.Ok) (he : t.sp = L.E)
    {count p n : BitVec 32} (ha : VG.Proof.Ed25519.Arm.VerifyMessage.UpdateArgs L count p n t) (hi : VG.Proof.Ed25519.Arm.VerifyMessage.Input L p n) :
    Proof.Sha512.updateArm.pre (t.callEntry.withRegions (Whole.updateRd L.E p n) (Whole.hashWr L.scr)) :=
  Whole.update_pre he ha.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2 hi.scratch
    (hL.kc.sub_left (Region.sub_prefix (by decide))) hL.nc hi.fit (by have := hL.top; omega)

theorem finalize_pre {t : State} (hL : L.Ok) (he : t.sp = L.E)
    {count : BitVec 32} (ha : VG.Proof.Ed25519.Arm.VerifyMessage.FinalArgs L count t) :
    Proof.Sha512.finalizeArm.pre (t.callEntry.withRegions (Whole.finalizeRd L.E) (Whole.finalizeWr L.scr (L.E + 184))) := by
  refine Whole.finalize_pre he ha.1 ha.2.2.2.1 ha.2.2.2.2 ?_
    (hL.kc.sub_left (Region.sub_prefix (by decide))) ?_ hL.nc
    (VG.Proof.Ed25519.Arm.VerifyMessage.frame_fit hL (d := 184) (by decide)) (by have := hL.top; omega)
  · rw [VG.Proof.Ed25519.Arm.VerifyMessage.final_addr hL]
    exact hL.kc.sub_left (VG.Proof.Ed25519.Arm.VerifyMessage.digestWithin L).sub
  · rw [VG.Proof.Ed25519.Arm.VerifyMessage.final_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)

theorem count_zero_high (x : BitVec 32) : (0#32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat]
  change 0 * 2 ^ 32 + x.toNat = x.toNat % 2 ^ 64
  omega

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem init_step (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀) :
    WP isa init s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr) [] := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.args_regs_ok hc hL ha (args := [(.r0, .caller 4 0)])
    (by decide) (by simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.r0, .caller 4 0) (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call hu (Whole.init_pre a0 hL.nc) (Whole.covers_writes hw) hw a0)
    fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, hp⟩
  rw [hm] at hf
  exact VG.Proof.Ed25519.Arm.VerifyMessage.init_frame hf

theorem update_step (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀)
    (count : Nat) (p n : Value) (hc16 : count < 65536) (hp : VG.Proof.Ed25519.Arm.VerifyMessage.valid p) (hn : VG.Proof.Ed25519.Arm.VerifyMessage.valid n)
    (hi : VG.Proof.Ed25519.Arm.VerifyMessage.Input L (VG.Proof.Ed25519.Arm.VerifyMessage.value L p) (VG.Proof.Ed25519.Arm.VerifyMessage.value L n)) {prev : List Byte}
    (hcount : count = prev.length) (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (setup [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)]
      [p, n, .caller 4 192])) s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (VG.Proof.Ed25519.Arm.VerifyMessage.value L p)) (VG.Proof.Ed25519.Arm.VerifyMessage.value L n).toNat) := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] →
      VG.Proof.Ed25519.Arm.VerifyMessage.valid x.2 := by simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid, hc16]
  have hvs : ∀ v ∈ [p, n, Value.caller 4 192], VG.Proof.Ed25519.Arm.VerifyMessage.valid v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl)
    · exact hp
    · exact hn
    · simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.args_ok hc hL ha (by simp) hv (by simp) hvs (by simp [preserved]))
    fun u ⟨hu, hf, hs, hstack⟩ => ?_)
  have a0 := hs (.r0, .caller 4 0) (by simp)
  have a2 : u.gpr .r2 = BitVec.ofNat 32 count := hs (.r2, .const count) (by simp)
  have a3 : u.gpr .r3 = 0#32 := hs (.r3, .const 0) (by simp)
  have d0 := hstack 0 (by simp)
  have d1 := hstack 1 (by simp)
  have d2 := hstack 2 (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have args : VG.Proof.Ed25519.Arm.VerifyMessage.UpdateArgs L (BitVec.ofNat 32 count) (VG.Proof.Ed25519.Arm.VerifyMessage.value L p) (VG.Proof.Ed25519.Arm.VerifyMessage.value L n) u := ⟨a0,a2,a3,d0,d1,d2⟩
  have ce : Proof.Sha512.countArm u = BitVec.ofNat 64 prev.length := by
    unfold Proof.Sha512.countArm
    rw [a3,a2,VG.Proof.Ed25519.Arm.VerifyMessage.count_zero_high]
    change BitVec.ofNat 64 (count % 2^32) = _
    rw [Nat.mod_eq_of_lt (by omega),hcount]
  have huRepr := VG.Proof.Ed25519.Arm.VerifyMessage.setup_repr hL hf hr
  have heq : Spec.Ed25519.bytesAt u.mem (State.addr (VG.Proof.Ed25519.Arm.VerifyMessage.value L p)) (VG.Proof.Ed25519.Arm.VerifyMessage.value L n).toNat =
      Spec.Ed25519.bytesAt s.mem (State.addr (VG.Proof.Ed25519.Arm.VerifyMessage.value L p)) (VG.Proof.Ed25519.Arm.VerifyMessage.value L n).toNat :=
    VG.Proof.Ed25519.Arm.VerifyMessage.frame_bytes hf ⟨State.addr (VG.Proof.Ed25519.Arm.VerifyMessage.value L p), (VG.Proof.Ed25519.Arm.VerifyMessage.value L n).toNat⟩
      (by simp only [List.mem_singleton]; intro r he; subst r; exact hi.args)
      (by have := (VG.Proof.Ed25519.Arm.VerifyMessage.value L n).isLt; change (VG.Proof.Ed25519.Arm.VerifyMessage.value L n).toNat ≤ 2^64; omega)
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.update_call hu (VG.Proof.Ed25519.Arm.VerifyMessage.update_pre hL hu.sp args hi) (VG.Proof.Ed25519.Arm.VerifyMessage.update_covers hi) hw
    a0 d0 d1 ce huRepr) fun t ⟨ht, hf', hrepr⟩ => ⟨ht, (VG.Proof.Ed25519.Arm.VerifyMessage.setup_frame hf).trans (VG.Proof.Ed25519.Arm.VerifyMessage.update_frame hf'), ?_⟩
  change Spec.Sha512.Repr _ t.mem _ (prev ++ Spec.Ed25519.bytesAt u.mem (State.addr (VG.Proof.Ed25519.Arm.VerifyMessage.value L p)) (VG.Proof.Ed25519.Arm.VerifyMessage.value L n).toNat) at hrepr
  rw [heq] at hrepr
  exact hrepr

theorem finalize_count (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (n : Nat) (b : Bool) :
    VG.Proof.Ed25519.Arm.VerifyMessage.value L (if b then Value.caller 2 n else .const n) =
      BitVec.ofNat 32 ((if b then L.len.toNat else 0) + n) := by
  cases b <;> simp [VG.Proof.Ed25519.Arm.VerifyMessage.value, Lay.value, BitVec.ofNat_add]

theorem finalize_step (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀)
    (n : Nat) (hn : n < 256) (b : Bool) {msg : List Byte}
    (hlen : msg.length < 2^32) (hcount : (if b then L.len.toNat else 0) + n = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) msg) :
    WP isa (finalize n b) s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 = Spec.Sha512.sha512 msg := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.r0, .caller 4 0),
      (.r2, if b then .caller 2 n else .const n), (.r3, .const 0)] → VG.Proof.Ed25519.Arm.VerifyMessage.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    · simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid]
    · cases b <;> simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid] <;> omega
    · simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.args_ok hc hL ha (by simp) hv (by simp)
    (by simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid]) (by simp [preserved])) fun u ⟨hu,hf,hs,hstack⟩ => ?_)
  have a0 := hs (.r0, .caller 4 0) (by simp)
  have a2 := hs (.r2, if b then .caller 2 n else .const n) (by simp)
  have a3 : u.gpr .r3 = 0#32 := hs (.r3, .const 0) (by simp)
  have d0 := hstack 0 (by simp)
  have d1 := hstack 1 (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  rw [VG.Proof.Ed25519.Arm.VerifyMessage.finalize_count,hcount] at a2
  have args : VG.Proof.Ed25519.Arm.VerifyMessage.FinalArgs L (BitVec.ofNat 32 msg.length) u := ⟨a0,a2,a3,d0,d1⟩
  have ce : Proof.Sha512.countArm u = BitVec.ofNat 64 msg.length := by
    unfold Proof.Sha512.countArm
    rw [a3,a2,VG.Proof.Ed25519.Arm.VerifyMessage.count_zero_high]
    change BitVec.ofNat 64 (msg.length % 2^32) = _
    rw [Nat.mod_eq_of_lt hlen]
  refine WP.mono (Whole.finalize_call hu (VG.Proof.Ed25519.Arm.VerifyMessage.finalize_pre hL hu.sp args) (VG.Proof.Ed25519.Arm.VerifyMessage.finalize_covers hL)
    (VG.Proof.Ed25519.Arm.VerifyMessage.final_writes hL) a0 d0 ce (VG.Proof.Ed25519.Arm.VerifyMessage.setup_repr hL hf hr) (by omega))
    fun t ⟨ht,hf',hh⟩ => ⟨ht,(VG.Proof.Ed25519.Arm.VerifyMessage.setup_frame hf).trans (VG.Proof.Ed25519.Arm.VerifyMessage.finalize_frame hL hf'),?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (L.E + 184)) 64 = _ at hh
  rw [VG.Proof.Ed25519.Arm.VerifyMessage.final_addr hL] at hh
  exact hh

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashUpdates`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem update_input (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀)
    (source count : Nat) (hj : source < 5) (hc16 : count < 65536) (hi : VG.Proof.Ed25519.Arm.VerifyMessage.Input L (L.value source) 32)
    {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (prefixArgs source count)) s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (L.value source)) 32) := by
  have inp : VG.Proof.Ed25519.Arm.VerifyMessage.Input L (VG.Proof.Ed25519.Arm.VerifyMessage.value L (.caller source 0)) (VG.Proof.Ed25519.Arm.VerifyMessage.value L (.const 32)) := by
    change VG.Proof.Ed25519.Arm.VerifyMessage.Input L (L.value source + 0#32) 32#32
    rw [BitVec.add_zero]
    exact hi
  refine WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.update_step hc hL ha count (.caller source 0) (.const 32) hc16
    ⟨hj, by decide⟩ (by simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  change Spec.Sha512.Repr _ t.mem _ (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (L.value source + 0#32)) 32) at hh
  rw [BitVec.add_zero] at hh
  exact hh

theorem update_message (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀)
    (count : Nat) (hc16 : count < 65536) {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (messageArgs count)) s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.VerifyMessage.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have inp : VG.Proof.Ed25519.Arm.VerifyMessage.Input L (VG.Proof.Ed25519.Arm.VerifyMessage.value L (.caller 1 0)) (VG.Proof.Ed25519.Arm.VerifyMessage.value L (.caller 2 0)) := by
    simpa only [VG.Proof.Ed25519.Arm.VerifyMessage.value, Lay.value, BitVec.add_zero] using VG.Proof.Ed25519.Arm.VerifyMessage.message_input hL
  refine WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.update_step hc hL ha count (.caller 1 0) (.caller 2 0) hc16
    (by simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid]) (by simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  simp only [VG.Proof.Ed25519.Arm.VerifyMessage.value, Lay.value, BitVec.add_zero] at hh
  rw [hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (by have := L.len.isLt; change L.len.toNat ≤ 2^64; omega)] at hh
  exact hh

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def hashInput (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m (State.addr L.sig) 32 ++
    Spec.Ed25519.bytesAt m (State.addr L.pk) 32 ++
    Spec.Ed25519.bytesAt m (State.addr L.msg) L.len.toNat

theorem sig_prefix_same (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) :
    Spec.Ed25519.bytesAt s.mem (State.addr L.sig) 32 = Spec.Ed25519.bytesAt m₀ (State.addr L.sig) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hc.frame.bytes (R := L.SIG) (by
    intro r hr
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.sc _ (by simp [Lay.inputs])
    · exact (hL.ks _ (by simp [Lay.inputs])).symm)
    (by change 64 ≤ 2 ^ 64; decide) (by change i < 64; have := List.mem_range.mp hi; omega)

theorem hash_ok (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀) :
    WP isa VG.Impl.Ed25519.Arm.VerifyMessage.hash s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E+184) 64 = Spec.Sha512.sha512 (VG.Proof.Ed25519.Arm.VerifyMessage.hashInput L m₀) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.init_step hc hL ha) fun t ⟨ht,_,hinit⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.update_input ht hL ha 3 0 (by decide) (by decide)
    (VG.Proof.Ed25519.Arm.VerifyMessage.signature_input hL) rfl hinit) fun u ⟨hu,_,hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem (State.addr L.sig) 32) at hsig
  rw [List.nil_append,VG.Proof.Ed25519.Arm.VerifyMessage.sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.update_input hu hL ha 0 32 (by decide) (by decide)
    (VG.Proof.Ed25519.Arm.VerifyMessage.key_input hL) (VG.Proof.Ed25519.Arm.VerifyMessage.bytes_length _ _ _).symm hsig) fun w ⟨hw,_,hpk⟩ => ?_)
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem (State.addr L.pk) 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide)] at hpk
  have hpkl : (Spec.Ed25519.bytesAt m₀ (State.addr L.sig) 32 ++ Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32).length = 64 := by
    rw [List.length_append,VG.Proof.Ed25519.Arm.VerifyMessage.bytes_length,VG.Proof.Ed25519.Arm.VerifyMessage.bytes_length]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.update_message hw hL ha 64 (by decide) hpkl.symm hpk) fun z ⟨hz,_,hmsg⟩ => ?_)
  have hlen : (VG.Proof.Ed25519.Arm.VerifyMessage.hashInput L m₀).length = 64+L.len.toNat := by
    simp only [VG.Proof.Ed25519.Arm.VerifyMessage.hashInput,List.length_append,VG.Proof.Ed25519.Arm.VerifyMessage.bytes_length]
  refine WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.finalize_step hz hL ha 64 (by decide) true (msg := VG.Proof.Ed25519.Arm.VerifyMessage.hashInput L m₀)
    (by rw [hlen]; exact hL.message_bound) (by simp only [ite_true]; rw [hlen]; omega) hmsg)
    fun t ⟨ht,_,hh⟩ => ⟨ht,hh⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.Challenge`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.Reduce`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
open VG.Impl.Ed25519.Arm (scalarReduce)

def reduceRd (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) : List Region := [VG.Proof.Ed25519.Arm.VerifyMessage.digest L]
def reduceWr (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (d : Nat) : List Region := [VG.Proof.Ed25519.Arm.VerifyMessage.field L d, L.SCR]
def ReduceArgs (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .r0 = L.E + BitVec.ofNat 32 d ∧ s.gpr .r1 = L.E + 184 ∧ s.gpr .r2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.Arm.VerifyMessage.reduceRd L) (VG.Proof.Ed25519.Arm.VerifyMessage.reduceWr L d)) := by
  have ad := VG.Proof.Ed25519.Arm.VerifyMessage.frame_addr hL (d := d) (by omega)
  have a184 : State.addr (L.E + 184) = State.addr L.E + 184 := VG.Proof.Ed25519.Arm.VerifyMessage.frame_addr hL (d := 184) (by decide)
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2, ad, a184]
  have sep : (VG.Proof.Ed25519.Arm.VerifyMessage.field L d).Disjoint (VG.Proof.Ed25519.Arm.VerifyMessage.digest L) := Offset.disjoint _ (by omega) (by omega) (by decide)
  exact ⟨rfl, rfl, sep,
    VG.Proof.Ed25519.Arm.VerifyMessage.field_scr hL (by omega), hL.kc.sub_left (VG.Proof.Ed25519.Arm.VerifyMessage.digestWithin L).sub,
    VG.Proof.Ed25519.Arm.VerifyMessage.frame_fit hL (by omega), VG.Proof.Ed25519.Arm.VerifyMessage.frame_fit hL (by decide), hL.nc⟩

theorem reduce_call (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184)
    (ha : VG.Proof.Ed25519.Arm.VerifyMessage.ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.Arm.VerifyMessage.reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 184) 64) := by
  have cov : Covers (VG.Proof.Ed25519.Arm.VerifyMessage.reduceRd L ++ VG.Proof.Ed25519.Arm.VerifyMessage.reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.Arm.VerifyMessage.covers
    simp only [VG.Proof.Ed25519.Arm.VerifyMessage.reduceRd, VG.Proof.Ed25519.Arm.VerifyMessage.reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.digestWithin L)
    · exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.fieldWithin L (by omega))
    · exact .inr (VG.Proof.Ed25519.Arm.VerifyMessage.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.Arm.VerifyMessage.reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.Arm.VerifyMessage.writes
    simp only [VG.Proof.Ed25519.Arm.VerifyMessage.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.Arm.VerifyMessage.fieldWithin L (by omega))
    · exact .inr (VG.Proof.Ed25519.Arm.VerifyMessage.scratchWithin L)
  refine Whole.call_ok hc scalarReduce_ok VG.Proof.Ed25519.Arm.VerifyMessage.reduce_noFrames (VG.Proof.Ed25519.Arm.VerifyMessage.reduce_pre hL hd ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (s.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 64) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1] at hp
  have ad := VG.Proof.Ed25519.Arm.VerifyMessage.frame_addr hL (d := d) (by omega)
  have a184 : State.addr (L.E + 184) = State.addr L.E + 184 := VG.Proof.Ed25519.Arm.VerifyMessage.frame_addr hL (d := 184) (by decide)
  rw [ad, a184] at hp
  exact hp

theorem reduce_step (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.Arm.Whole.callWith VG.Impl.Ed25519.Arm.VerifyMessage.reduceArgs "vg_ed25519_scalar_reduce" scalarReduce) s
      fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.Arm.VerifyMessage.reduceWr L 120) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr L.E+184) 64) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.args_regs_ok hc hL ha
    (args := [(.r0,.frame 120),(.r1,.frame 184),(.r2,.caller 4 0)])
    (by simp) (by simp [VG.Proof.Ed25519.Arm.VerifyMessage.valid]) (by simp [preserved])) fun u ⟨hu,hm,hs⟩ => ?_)
  have a0 := hs (.r0,.frame 120) (by simp)
  have a1 := hs (.r1,.frame 184) (by simp)
  have a2 := hs (.r2,.caller 4 0) (by simp)
  change u.gpr .r2 = L.scr+0#32 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.reduce_call hu hL (d := 120) (by decide) ⟨a0,a1,a2⟩) fun t ⟨ht,hf,hp⟩ => ⟨ht,?_,?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem encodeLE_eq (n x : Nat) : Spec.Ed25519.encodeLE n x = Proof.X25519.leBytes n x := by
  unfold Spec.Ed25519.encodeLE Proof.X25519.leBytes
  apply congrArg (List.map · (List.range n))
  funext i
  rw [Nat.shiftRight_eq_div_pow,show 256^i=2^(8*i) by rw [Nat.pow_mul]]

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, VG.Proof.Ed25519.Arm.VerifyMessage.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem extend_step (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 38) (count := 8) (by decide)) fun t ⟨ht, hf, hz⟩ => ⟨ht, ?_⟩
  have low : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 32 =
      Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨State.addr L.E + 120, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have high : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 152) 32 = Spec.Ed25519.encodeLE 32 0 := by
    rw [VG.Proof.Ed25519.Arm.VerifyMessage.encodeLE_eq]
    have word (j : Nat) (hj : j < 8) : t.mem.readW (State.addr L.E + 152 + BitVec.ofNat 64 (4*j)) 32 = 0 := by
      have z := hz j hj
      have e : State.addr L.E + BitVec.ofNat 64 (4*(38+j)) = State.addr L.E + 152 + BitVec.ofNat 64 (4*j) := by
        rw [show 4*(38+j)=152+4*j by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [e] at z
      exact z
    apply Proof.X25519.bytesAt_leBytes_words32
    intro j hj
    simpa using congrArg BitVec.toNat (word j hj)
  change Spec.X25519.bytesAt t.mem (State.addr L.E + 120) (32 + 32) = _
  rw [Proof.X25519.bytesAt_add]
  change Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 32 ++
    Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120 + 32) 32 = _
  rw [show State.addr L.E + 120 + 32 = State.addr L.E + 152 by rw [BitVec.add_assoc]; rfl,
    low, hd, high, VG.Proof.Ed25519.Arm.VerifyMessage.reduced_challenge]

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : VG.Proof.Ed25519.Arm.VerifyMessage.Lay) (m : Mem) : VG.Proof.Ed25519.Arm.VerifyMessage.hashInput L m =
    (Spec.Ed25519.bytesAt m (State.addr L.sig) 64).take 32 ++
      Spec.Ed25519.bytesAt m (State.addr L.pk) 32 ++
      Spec.Ed25519.bytesAt m (State.addr L.msg) L.len.toNat := by
  have e : (Spec.Ed25519.bytesAt m (State.addr L.sig) 64).take 32 =
      Spec.Ed25519.bytesAt m (State.addr L.sig) 32 := by
    unfold Spec.Ed25519.bytesAt
    rw [← List.map_take, List.take_range]
    rfl
  rw [e]
  rfl

theorem body_ok (hc : VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok)
    (ha : VG.Proof.Ed25519.Arm.VerifyMessage.Arguments L m₀) :
    WP isa body s fun t => VG.Proof.Ed25519.Arm.VerifyMessage.Ctx L g m₀ t ∧
      t.gpr .r0 = VG.Proof.Ed25519.Arm.VerifyMessage.signWord (Spec.Ed25519.verify (Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32)
        (Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) (Spec.Ed25519.bytesAt m₀ (State.addr L.sig) 64)) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.hash_ok hc hL ha) fun t ⟨ht,hh⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.reduce_step ht hL ha) fun u ⟨hu,_,hr⟩ => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.extend_step hu hL hr) fun w ⟨hw,he⟩ => ?_)
  rw [VG.Proof.Ed25519.Arm.VerifyMessage.hashInput_eq] at he
  refine WP.mono (VG.Proof.Ed25519.Arm.VerifyMessage.equation_step hw hL ha) fun z ⟨hz,eq⟩ => ⟨hz,?_⟩
  rw [hw.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide),
    hw.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64≤2^64; decide),he] at eq
  exact eq

theorem body_noFrames : body.noFrames = true := by
  have hu := Whole.update_noFrames
  have hf := Whole.finalize_noFrames
  simp only [body,Impl.Ed25519.Arm.VerifyMessage.hash,init,update,finalize,Impl.Ed25519.Arm.Whole.callWith,
    Code.noFrames,Impl.Sha512.Arm.Stream.init,hu,hf,Bool.and_self]
  rw [VG.Proof.Ed25519.Arm.VerifyMessage.reduce_noFrames,VG.Proof.Ed25519.Arm.VerifyMessage.equation_noFrames]
  rfl

end VG.Proof.Ed25519.Arm.VerifyMessage

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Verified`. -/
section

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTReady`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTCommon`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def Two (L : Lay) (g₁ g₂ : Reg → BitVec 32)
    (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b ∧ P a ∧ P b

theorem two_sp {P : State → Prop} {a b : State} (h : Two L g₁ g₂ m₁ m₂ P a b) :
    a.sp = b.sp := h.1.sp.trans h.2.1.sp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ m₁ t → P t → WP isa c t fun u => Ctx L g₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ m₂ t → P t → WP isa c t fun u => Ctx L g₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) c (Two L g₁ g₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

def AllArgs (L : Lay) (args : List (Reg × Value)) (stack : List Value) (s : State) : Prop :=
  OutArgs L args s ∧ StackArgs L stack s

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (stack : List Value) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, valid p.2) (hs : stack.length ≤ 6)
    (hvs : ∀ v ∈ stack, valid v) (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stack))
      (Two L g₁ g₂ m₁ m₂ (AllArgs L args stack)) := by
  refine two_wp ((Whole.setup_ct args stack).mono (fun _ _ h => two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro s hc _
    exact WP.mono (args_ok hc hL ha hn hv hs hvs hr) fun _ ⟨hu, _, hg, ht⟩ => ⟨hu, hg, ht⟩
  · intro s hc _
    exact WP.mono (args_ok hc hL hb hn hv hs hvs hr) fun _ ⟨hu, _, hg, ht⟩ => ⟨hu, hg, ht⟩

theorem args_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : Two L g₁ g₂ m₁ m₂ (AllArgs L args stack) a b) {p : Reg × Value} (hp : p ∈ args) :
    a.gpr p.1 = b.gpr p.1 := (h.2.2.1.1 p hp).trans (h.2.2.2.1 p hp).symm

theorem call_gpr_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : Two L g₁ g₂ m₁ m₂ (AllArgs L args stack) a b) {p : Reg × Value}
    (hp : p ∈ args) (hl : p.1 ∉ linkRegs) : a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := by
  rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl]
  exact args_eq h hp

theorem stack_arg_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : Two L g₁ g₂ m₁ m₂ (AllArgs L args stack) a b) {j : Nat} (hj : j < stack.length) :
    stackArg a j = stackArg b j := (h.2.2.1.2 j hj).trans (h.2.2.2.2 j hj).symm

theorem call_ct {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hn : c.noFrames = true)
    (ready : ∀ {g m t}, Ctx L g m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, Two L g₁ g₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) (.call name c)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply two_wp
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

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
variable {L : Lay} {s : State}

def reduce_ready (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184) (ha : ReduceArgs L d s) : Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L (by omega))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L (by omega))
    · exact .inr (scratchWithin L)
  exact ⟨reduceRd L, reduceWr L d, reduce_pre hL hd ha, cov, ws⟩

def init_ready (hL : L.Ok) (ha : s.gpr .r0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initArm Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre ha hL.nc, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (he : s.sp = L.E) {count p len : BitVec 32}
    (hi : Input L p len) (ha : UpdateArgs L count p len s) :
    Whole.CallReady Proof.Sha512.updateArm L.E L.inputs L.outputs s := by
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd L.E p len, Whole.hashWr L.scr, update_pre hL he ha hi, update_covers hi, hw⟩

def finalize_ready (hL : L.Ok) (he : s.sp = L.E) {count : BitVec 32} (ha : FinalArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeArm L.E L.inputs L.outputs s :=
  ⟨Whole.finalizeRd L.E, Whole.finalizeWr L.scr (L.E + 184), finalize_pre hL he ha,
    finalize_covers hL, final_writes hL⟩

def equation_ready (hL : L.Ok) (ha : EqArgs L s) : Whole.CallReady verifyLocal L.E L.inputs L.outputs s :=
  ⟨equationRd L,equationWr L,equation_pre hL ha,equation_covers,equation_writes⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTBody`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTHash`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L [(.r0, .caller 4 0)] []))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.Arm.Stream.init_verified _).1
    (Proof.Sha512.Arm.Stream.init_verified _).2.1 rfl
  · intro g m t _ hs
    have h := hs.1 (.r0, .caller 4 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at h
    rw [BitVec.add_zero] at h
    exact init_ready hL h
  · intro a b ar aw br bw h
    exact call_gpr_eq (p := (.r0, .caller 4 0)) h (by simp) (by simp [linkRegs])

theorem update_call_ct (hL : L.Ok) (count : Nat) (p n : Value)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L
      [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] [p,n,.caller 4 192]))
      (.call Spec.Sha512.updateScratchApi.name Impl.Sha512.Arm.Stream.update)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Update.update_verified.1
    Proof.Sha512.Arm.Stream.Update.update_verified.2.1 Whole.update_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 4 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at a0
    rw [BitVec.add_zero] at a0
    exact update_ready hL hc.sp hi ⟨a0, hs.1 (.r2, .const count) (by simp),
      hs.1 (.r3, .const 0) (by simp), hs.2 0 (by simp), hs.2 1 (by simp), hs.2 2 (by simp)⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 4 0)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, .const count)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r3, .const 0)) h (by simp) (by simp [linkRegs]),
      stack_arg_eq h (j := 0) (by simp), stack_arg_eq h (j := 1) (by simp), stack_arg_eq h (j := 2) (by simp)⟩

theorem finalize_call_ct (hL : L.Ok) (n : Nat) (b : Bool) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L
      [(.r0, .caller 4 0), (.r2, if b then .caller 2 n else .const n), (.r3, .const 0)]
      [.frame 184, .caller 4 192]))
      (.call Spec.Sha512.finalizeScratchApi.name Impl.Sha512.Arm.Stream.finalize)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Finalize.finalize_verified.1
    Proof.Sha512.Arm.Stream.Finalize.finalize_verified.2.1 Whole.finalize_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 4 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at a0
    rw [BitVec.add_zero] at a0
    exact finalize_ready hL hc.sp ⟨a0,
      hs.1 (.r2, if b then .caller 2 n else .const n) (by simp),
      hs.1 (.r3, .const 0) (by simp), hs.2 0 (by decide), hs.2 1 (by decide)⟩
  · intro a c ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 4 0)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, if b then .caller 2 n else .const n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r3, .const 0)) h (by simp) (by simp [linkRegs]),
      stack_arg_eq h (j := 0) (by decide), stack_arg_eq h (j := 1) (by decide)⟩

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) init
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.r0, .caller 4 0)] [] (by decide) (by simp [valid])
    (by decide) (by simp) (by simp [preserved])).seq (init_call_ct hL)

theorem update_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hc : count < 65536) (hp : valid p) (hn : valid n)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (update (setup [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] [p,n,.caller 4 192]))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : ∀ x : Reg × Value, x ∈ [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] →
      valid x.2 := by simp [valid,hc]
  have hvs : ∀ v ∈ [p,n,Value.caller 4 192], valid v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl)
    · exact hp
    · exact hn
    · simp [valid]
  exact (setup_ct hL ha hb _ _ (by simp) hv (by simp) hvs (by simp [preserved])).seq
    (update_call_ct hL count p n hi)

theorem finalize_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 256) (b : Bool) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (finalize n b)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : valid (if b then .caller 2 n else .const n) := by
    cases b <;> simp [valid] <;> omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.r0, .caller 4 0),
      (.r2, if b then .caller 2 n else .const n), (.r3, .const 0)] → valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · simp [valid]
    · exact hv
    · simp [valid]
  exact (setup_ct hL ha hb _ _ (by simp) hvall (by decide) (by simp [valid])
    (by simp [preserved])).seq (finalize_call_ct hL n b)

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTHashPipeline`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem prefix_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (source count : Nat) (hj : source < 5) (hc : count < 65536) (hi : Input L (L.value source) 32) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (update (prefixArgs source count))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have inp : Input L (value L (.caller source 0)) (value L (.const 32)) := by
    change Input L (L.value source+0#32) 32#32
    rw [BitVec.add_zero]
    exact hi
  exact update_ct hL ha hb count (.caller source 0) (.const 32) hc ⟨hj,by decide⟩ (by simp [valid]) inp

theorem message_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (update (messageArgs 64))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have inp : Input L (value L (.caller 1 0)) (value L (.caller 2 0)) := by
    simpa only [value,Lay.value,BitVec.add_zero] using message_input hL
  exact update_ct hL ha hb 64 (.caller 1 0) (.caller 2 0) (by decide)
    (by simp [valid]) (by simp [valid]) inp

theorem hash_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) VG.Impl.Ed25519.Arm.VerifyMessage.hash
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (init_ct hL ha hb).seq ((prefix_ct hL ha hb 3 0 (by decide) (by decide) (signature_input hL)).seq
    ((prefix_ct hL ha hb 0 32 (by decide) (by decide) (key_input hL)).seq
      ((message_ct hL ha hb).seq (finalize_ct hL ha hb 64 (by decide) true))))

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTScalars`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def reduceValues : List (Reg × Value) := [(.r0,.frame 120),(.r1,.frame 184),(.r2,.caller 4 0)]

theorem reduce_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L reduceValues []))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.Arm.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarReduce_ok scalarReduce_ct reduce_noFrames
  · intro g m t _ hs
    have a0 := hs.1 (.r0,.frame 120) (by simp [reduceValues])
    have a1 := hs.1 (.r1,.frame 184) (by simp [reduceValues])
    have a2 := hs.1 (.r2,.caller 4 0) (by simp [reduceValues])
    change t.gpr .r2=L.scr+0#32 at a2
    exact reduce_ready hL (by decide) ⟨a0,a1,a2.trans (BitVec.add_zero _)⟩
  · intro a b ar aw br bw h
    simp only [scalarReduceLocal,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨two_sp h,call_gpr_eq h (p := (.r0,.frame 120)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.r1,.frame 184)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.r2,.caller 4 0)) (by simp [reduceValues]) (by decide)⟩

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+184) 64=digest)
      (callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.Arm.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 32=Spec.Ed25519.scalarReduce digest) := by
  have hs := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb reduceValues []
    (by decide) (by simp [reduceValues,valid]) (by decide) (by simp)
    (by simp [reduceValues,preserved])
  refine two_wp ((hs.seq (reduce_call_ct hL)).mono
    (fun _ _ h => ⟨h.1,h.2.1,trivial,trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc hd
    exact WP.mono (reduce_step hc hL ha) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩
  · intro s hc hd
    exact WP.mono (reduce_step hc hL hb) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩

theorem extend_ct (hL : L.Ok) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 32=Spec.Ed25519.scalarReduce digest)
      (.block extendChallenge)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 64=
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L)) := by
  refine two_wp ((Whole.zeroWords_ct 38 8).mono (fun _ _ h => two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro s hc hd
    exact extend_step hc hL hd
  · intro s hc hd
    exact extend_step hc hL hd

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTEquation`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem equation_setup_wp {g m t} (hc : Ctx L g m t) (hL : L.Ok) (ha : Arguments L m)
    {ch : List Byte} (hh : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = ch) :
    WP isa (.block VerifyMessage.equationArgs) t fun u => Ctx L g m u ∧ EqArgs L u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.E + 120) 64 = ch := by
  refine WP.mono (args_regs_ok hc hL ha
    (args := [(.r0,.caller 0 0),(.r1,.caller 3 0),(.r2,.frame 120),(.r3,.caller 4 0)])
    (by simp) (by simp [valid]) (by simp [preserved])) ?_
  intro u ⟨hu,hm,hav⟩
  have a0 := hav (.r0,.caller 0 0) (by simp)
  have a1 := hav (.r1,.caller 3 0) (by simp)
  have a2 := hav (.r2,.frame 120) (by simp)
  have a3 := hav (.r3,.caller 4 0) (by simp)
  change u.gpr .r0 = L.pk+0#32 at a0
  change u.gpr .r1 = L.sig+0#32 at a1
  change u.gpr .r3 = L.scr+0#32 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  exact ⟨hu,⟨a0,a1,a2,a3⟩,hm ▸ hh⟩

theorem equation_call_ct (hL : L.Ok) {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ (State.addr L.pk) 32 = Spec.Ed25519.bytesAt m₂ (State.addr L.pk) 32)
    (hsig : Spec.Ed25519.bytesAt m₁ (State.addr L.sig) 64 = Spec.Ed25519.bytesAt m₂ (State.addr L.sig) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => EqArgs L t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge)
      (.call "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct verify_ok verify_ct equation_noFrames (fun _ h => equation_ready hL h.1)
  intro a b ar aw br bw h
  have hsp := two_sp h
  have aa := h.2.2.1.1
  have ab := h.2.2.2.1
  have pk₁ := Ctx.input_bytes h.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  have pk₂ := Ctx.input_bytes h.2.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  have sig₁ := Ctx.input_bytes h.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)
  have sig₂ := Ctx.input_bytes h.2.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)
  simp only [verifyLocal, State.withRegions_gpr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_mem, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    aa.1, aa.2.1, aa.2.2.1, aa.2.2.2, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2]
  have ac : State.addr (L.E+120) = State.addr L.E+120 := frame_addr hL (d := 120) (by decide)
  rw [ac]
  refine ⟨hsp,trivial,trivial,trivial,trivial,?_⟩
  have kp := pk₁.trans (hpk.trans pk₂.symm)
  have ks := sig₁.trans (hsig.trans sig₂.symm)
  have kh := h.2.2.1.2.trans h.2.2.2.2.symm
  change Spec.Ed25519.bytesAt a.mem (State.addr L.pk) 32 = Spec.Ed25519.bytesAt b.mem (State.addr L.pk) 32 at kp
  change Spec.Ed25519.bytesAt a.mem (State.addr L.sig) 64 = Spec.Ed25519.bytesAt b.mem (State.addr L.sig) 64 at ks
  rw [kp,ks,kh]

theorem equation_step_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ (State.addr L.pk) 32 = Spec.Ed25519.bytesAt m₂ (State.addr L.pk) 32)
    (hsig : Spec.Ed25519.bytesAt m₁ (State.addr L.sig) 64 = Spec.Ed25519.bytesAt m₂ (State.addr L.sig) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge)
      (Whole.callWith VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hs : RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge)
      (.block VerifyMessage.equationArgs)
      (Two L g₁ g₂ m₁ m₂ fun t => EqArgs L t ∧ Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge) := by
    apply two_wp ((Whole.setup_ct
      [(.r0,.caller 0 0),(.r1,.caller 3 0),(.r2,.frame 120),(.r3,.caller 4 0)] []).mono
      (fun _ _ h => two_sp h) (fun _ _ _ => True.intro))
    · intro t hc hh
      exact equation_setup_wp hc hL ha hh
    · intro t hc hh
      exact equation_setup_wp hc hL hb hh
  exact hs.seq (equation_call_ct hL hpk hsig)

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem hash_result_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hm : hashInput L m₁ = hashInput L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) VG.Impl.Ed25519.Arm.VerifyMessage.hash
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+184) 64 =
        Spec.Sha512.sha512 (hashInput L m₁)) := by
  refine two_wp ((hash_ct hL ha hb).mono (fun _ _ h => h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro t hc _
    exact hash_ok hc hL ha
  · intro t hc _
    refine WP.mono (hash_ok hc hL hb) fun u ⟨hu,hh⟩ => ⟨hu,?_⟩
    rw [hm]
    exact hh

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hpk : Spec.Ed25519.bytesAt m₁ (State.addr L.pk) 32=Spec.Ed25519.bytesAt m₂ (State.addr L.pk) 32)
    (hmsg : Spec.Ed25519.bytesAt m₁ (State.addr L.msg) L.len.toNat=Spec.Ed25519.bytesAt m₂ (State.addr L.msg) L.len.toNat)
    (hsig : Spec.Ed25519.bytesAt m₁ (State.addr L.sig) 64=Spec.Ed25519.bytesAt m₂ (State.addr L.sig) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hm : hashInput L m₁=hashInput L m₂ := by
    rw [hashInput_eq,hashInput_eq,hpk,hmsg,hsig]
  exact (hash_result_ct hL ha hb hm).seq
    ((reduce_ct hL ha hb _).seq ((extend_ct hL _).seq (equation_step_ct hL ha hb hpk hsig)))

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.Entry`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm

def verifyMessageLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0),32⟩
    let msg : Region := ⟨State.addr (s.gpr .r1),(s.gpr .r2).toNat⟩
    let sig : Region := ⟨State.addr (s.gpr .r3),64⟩
    let scr : Region := ⟨State.addr (stackArg s 0),8192⟩
    let args : Region := ⟨State.addr s.sp,4⟩
    let stk : Region := ⟨State.addr s.sp - 280,280⟩
    s.rd = [pk,msg,sig,args] ∧ s.wr = [scr] ∧
    pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
    stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
    (s.gpr .r0).toNat+32≤2^32 ∧ (s.gpr .r1).toNat+(s.gpr .r2).toNat≤2^32 ∧
    (s.gpr .r3).toNat+64≤2^32 ∧ (stackArg s 0).toNat+8192≤2^32 ∧
    280≤s.sp.toNat ∧ s.sp.toNat+4≤2^32
  post s t := t.gpr .r0 = if Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) 64) then 1 else 0
  pub s t := s.sp=t.sp ∧ s.gpr .r0=t.gpr .r0 ∧ s.gpr .r1=t.gpr .r1 ∧
    s.gpr .r2=t.gpr .r2 ∧ s.gpr .r3=t.gpr .r3 ∧ stackArg s 0=stackArg t 0 ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32 = Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r0)) 32 ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r1)) (t.gpr .r2).toNat ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) 64 = Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r3)) 64

def lay (s : State) : Lay := ⟨s.gpr .r0,s.gpr .r1,s.gpr .r2,s.gpr .r3,stackArg s 0,Whole.base s⟩

theorem entry_below {s : State} (h : verifyMessageLocal.pre s) : 280≤s.sp.toNat := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hb,_⟩ := h
  exact hb

theorem entry_top {s : State} (h : verifyMessageLocal.pre s) : s.sp.toNat+4≤2^32 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,ht⟩ := h
  exact ht

theorem original_args {s : State} (hb : 280 ≤ s.sp.toNat) :
    (lay s).ORIGINALARGS = ⟨State.addr s.sp,4⟩ := by
  unfold Lay.ORIGINALARGS lay
  rw [Whole.base_addr hb, BitVec.sub_add_cancel]

theorem stack_eq {s : State} (hb : 280 ≤ s.sp.toNat) :
    Whole.stack s = ⟨State.addr s.sp-280,280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr hb]

theorem entry_writes {s : State} (h : verifyMessageLocal.pre s) :
    ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  have hb := entry_below h
  obtain ⟨_,hw,_,_,_,_,_,_,_,hc,_⟩ := h
  intro r hr
  rw [hw,List.mem_singleton] at hr
  subst r
  rw [stack_eq hb]
  exact hc

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨_,_,pc,mc,sc,ac,kp,km,ks,kc,np,nm,ns,nc,hb,_⟩ := h
  have fr : Region.Sub (Whole.FR (Whole.base s)) (Whole.stack s) := Region.sub_prefix (by decide)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (Whole.stack s) := Offset.sub_base _ (by decide)
  rw [← stack_eq hb] at kp km ks kc
  refine ⟨?_,?_,?_,kc.sub_left fr,np,nm,ns,nc⟩
  · have he := Whole.base_top (s := s) hb
    have hs := s.sp.isLt
    change (Whole.base s).toNat+272≤2^32
    omega
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact pc
    · exact mc
    · exact sc
    · rw [original_args hb]; exact ac
    · exact kc.sub_left ar
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact ks.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)

theorem entry_ctx {s p : State} (h : verifyMessageLocal.pre s) (hp : Whole.Saved (Whole.entered s) 5 p) :
    Ctx (lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs _
  simp only [Lay.inputs, original_args (entry_below h)]
  simpa only [Whole.bodyRd,h.1,Whole.bodyWr,h.2.1,Lay.outputs,
    Lay.PK,Lay.MSG,Lay.SIG,Lay.SCR,Lay.ARGS,Whole.ARGS,show BitVec.ofNat 64 248 = (248 : Addr) from rfl,lay,List.cons_append,List.nil_append] using hc

theorem entry_regions {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).inputs = Whole.bodyRd s ∧ (lay s).outputs = s.wr := by
  simp only [Lay.inputs, original_args (entry_below h)]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1,
    Lay.SIG, Lay.PK, Lay.MSG, Lay.SCR, Lay.ARGS, Whole.ARGS,
    show BitVec.ofNat 64 248 = (248 : Addr) from rfl, lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_args {s p : State} (h : verifyMessageLocal.pre s)
    (hp : Whole.Saved (Whole.entered s) 5 p) : Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words (entry_below h) (by decide : 5 ≤ 6) (entry_top h) hp hj
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
      Nat.reduceSub, Nat.mul_zero, BitVec.add_zero, Lay.value, lay,
      stackArg, stackArgAddr] using hw

theorem entry_read {s : State} (h : verifyMessageLocal.pre s) : ∀ j < 5, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4*(j-4)))) 4 := by
  intro j hj h4
  have : j = 4 := by omega
  subst j
  simp only [Nat.reduceSub,Nat.mul_zero,BitVec.add_zero]
  exact ⟨⟨State.addr s.sp,4⟩, List.mem_append_left _ (by rw [h.1]; simp), by simp [Region.Contains]⟩

theorem entry_input {s : State} (h : verifyMessageLocal.pre s) {m : Mem}
    (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len≤2^64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  have hb := entry_below h
  obtain ⟨hrd,_,_,_,_,_,kp,km,ks,_⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rw [← stack_eq hb] at kp km ks
  rcases hr with rfl | rfl | rfl | rfl
  · exact kp.symm
  · exact km.symm
  · exact ks.symm
  · rw [← original_args hb]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CT`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.Correct`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

theorem verifyMessage_ok {s : State} (h : verifyMessageLocal.pre s) :
    WP isa VG.Impl.Ed25519.Arm.VerifyMessage.code s fun u => abiPreserved s u ∧ verifyMessageLocal.post s u := by
  have hw := Whole.wrap_ok body_noFrames (by decide : 5 ≤ 6) (entry_below h) (entry_top h) (entry_read h) (entry_writes h)
    (P := fun m _ r => r = signWord (Spec.Ed25519.verify
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r0)) 32)
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r3)) 64)))
    (fun p hp => WP.mono (body_ok (entry_ctx h hp) (lay_ok h) (entry_args h hp))
      fun u ⟨hu,ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs u at hu
        rw [(entry_regions h).1, (entry_regions h).2] at hu
        exact hu,ho⟩)
  refine WP.mono hw fun u ⟨hu,m,hf,hp⟩ => ⟨hu,?_⟩
  have pk := entry_input h hf (r := ⟨State.addr (s.gpr .r0),32⟩) (by rw [h.1]; simp) (by change 32≤2^64; decide)
  have msg := entry_input h hf (r := ⟨State.addr (s.gpr .r1),(s.gpr .r2).toNat⟩) (by rw [h.1]; simp)
    (by change (s.gpr .r2).toNat≤2^64; have := (s.gpr .r2).isLt; omega)
  have sig := entry_input h hf (r := ⟨State.addr (s.gpr .r3),64⟩) (by rw [h.1]; simp) (by change 64≤2^64; decide)
  change u.gpr .r0 = signWord _
  rw [hp,pk,msg,sig]

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

theorem lay_eq {s t : State} (h : verifyMessageLocal.pub s t) : lay s=lay t := by
  obtain ⟨sp,h0,h1,h2,h3,h4,_⟩ := h
  simp only [lay,Whole.base,sp,h0,h1,h2,h3,h4]

theorem saved_inputs_eq {s t p q : State} (hs : verifyMessageLocal.pre s) (ht : verifyMessageLocal.pre t)
    (hp : verifyMessageLocal.pub s t) (hpa : Whole.Saved (Whole.entered s) 5 p)
    (hqb : Whole.Saved (Whole.entered t) 5 q) :
    Spec.Ed25519.bytesAt p.mem (State.addr (lay s).pk) 32 = Spec.Ed25519.bytesAt q.mem (State.addr (lay s).pk) 32 ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (lay s).msg) (lay s).len.toNat =
      Spec.Ed25519.bytesAt q.mem (State.addr (lay s).msg) (lay s).len.toNat ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (lay s).sig) 64 = Spec.Ed25519.bytesAt q.mem (State.addr (lay s).sig) 64 := by
  have fp := Whole.saved_frame (entry_below hs) hpa
  have fq := Whole.saved_frame (entry_below ht) hqb
  obtain ⟨_,h0,h1,h2,h3,_,pk,msg,sig⟩ := hp
  have epk := entry_input hs fp (r := ⟨State.addr (s.gpr .r0),32⟩) (by rw [hs.1]; simp) (by change 32≤2^64; decide)
  have fpk := entry_input ht fq (r := ⟨State.addr (t.gpr .r0),32⟩) (by rw [ht.1]; simp) (by change 32≤2^64; decide)
  have emsg := entry_input hs fp (r := ⟨State.addr (s.gpr .r1),(s.gpr .r2).toNat⟩) (by rw [hs.1]; simp)
    (by have := (s.gpr .r2).isLt; change (s.gpr .r2).toNat ≤ 2 ^ 64; omega)
  have fmsg := entry_input ht fq (r := ⟨State.addr (t.gpr .r1),(t.gpr .r2).toNat⟩) (by rw [ht.1]; simp)
    (by have := (t.gpr .r2).isLt; change (t.gpr .r2).toNat ≤ 2 ^ 64; omega)
  have esig := entry_input hs fp (r := ⟨State.addr (s.gpr .r3),64⟩) (by rw [hs.1]; simp) (by change 64≤2^64; decide)
  have fsig := entry_input ht fq (r := ⟨State.addr (t.gpr .r3),64⟩) (by rw [ht.1]; simp) (by change 64≤2^64; decide)
  change Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r0)) 32=Spec.Ed25519.bytesAt q.mem (State.addr (s.gpr .r0)) 32 ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat=Spec.Ed25519.bytesAt q.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r3)) 64=Spec.Ed25519.bytesAt q.mem (State.addr (s.gpr .r3)) 64
  rw [epk,emsg,esig,h0,h1,h2,h3,fpk,fmsg,fsig]
  rw [h0] at pk
  rw [h1,h2] at msg
  rw [h3] at sig
  exact ⟨pk,msg,sig⟩

theorem verifyMessage_ct :
    ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub VG.Impl.Ed25519.Arm.VerifyMessage.code := by
  refine Whole.wrap_ct (by decide : 5 ≤ 6) (fun _ _ hp => hp.1)
    (fun _ hs => entry_below hs) (fun _ hs => entry_top hs) (fun _ hs => entry_read hs) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p,q,hpa,hqb,rfl,rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    obtain ⟨pk,msg,sig⟩ := saved_inputs_eq hs ht hp hpa hqb
    exact ⟨(body_ct (lay_ok hs) (entry_args hs hpa) hqa pk msg sig _ _ _ _ _ _
      ⟨entry_ctx hs hpa,hq,trivial,trivial⟩ ea eb).1,trivial⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.Contract`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm

def verifySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 64 | .r3 => 0x3000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x9001 then 0x40 else 0
  rd := [⟨0x1000,32⟩,⟨0x2000,64⟩,⟨0x3000,64⟩,⟨0x9000,4⟩]
  wr := [⟨0x4000,8192⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

private theorem argAddr_zero (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

private theorem pre_bridge (s : State) (h : (Spec.Ed25519.verifyContract Arm.abi 280).pre s) :
    verifyMessageLocal.pre s := by
  sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
  sig_split h
  sig_reduce [verifyMessageLocal, Arm.State.addr]
  sig_simp [argAddr_zero, Arm.State.addr] [] at *
  simp only [Arm.State.addr, show (280#64) = (280 : Addr) from rfl] at *
  sig_and_intros
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

theorem verifyMessage_implies : verifyMessageLocal.Implies (Spec.Ed25519.verifyContract Arm.abi 280) where
  pre := pre_bridge
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, Arm.abi,Arm.argRegs,Arm.reduceClassify,Arm.Loc.val,Arm.State.addr]
    rw [BitVec.setWidth_append_eq_right]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, Arm.abi,Arm.argRegs,Arm.reduceClassify,Arm.Loc.val,Arm.State.addr] at h
    obtain ⟨sp, bytes, pk, msg, len, sig, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, len])
    exact ⟨sp, pk, msg, len, sig, base, first, middle, last⟩
  sat := by
    refine ⟨verifySatState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
        Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, verifySatState]
      decide +kernel


end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

theorem verifyMessage_verified :
    Verified Arm.target VG.Impl.Ed25519.Arm.VerifyMessage.code (Spec.Ed25519.verifyContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verifyMessage_ok h) verifyMessage_ct
      (.refl verifyMessage_implies.sat_left)) verifyMessage_implies

end VG.Proof.Ed25519.Arm.VerifyMessage

end
