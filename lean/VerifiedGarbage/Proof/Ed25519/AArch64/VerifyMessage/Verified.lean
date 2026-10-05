import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyMessage
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTReady`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Args`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Layout`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64

structure Lay where
  pk : BitVec 64
  msg : BitVec 64
  len : BitVec 64
  sig : BitVec 64
  scr : BitVec 64
  E : BitVec 64

namespace Lay
variable (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay)
abbrev PK : Region := ⟨L.pk, 32⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SIG : Region := ⟨L.sig, 64⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev CK : Region := Whole.CK L.E
def inputs : List Region := [L.PK, L.MSG, L.SIG, L.ARGS]
def outputs : List Region := [L.SCR]
def value (j : Nat) : BitVec 64 :=
  match j with | 0 => L.pk | 1 => L.msg | 2 => L.len | 3 => L.sig | _ => L.scr

structure Ok : Prop where
  top : L.E.toNat + 304 ≤ 2 ^ 64
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.FR.Disjoint r
  kc : L.FR.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 64
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  ns : L.sig.toNat + 64 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  e16 : 16 ≤ L.E.toNat
  ck : ∀ r ∈ L.inputs, L.CK.Disjoint r
  cc : L.CK.Disjoint L.SCR
end Lay

/-- An input is outside the frame of a call. -/
theorem Lay.Ok.ck_within {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} (h : L.Ok) {r : Region} (hi : ∃ R ∈ L.inputs, Whole.Within r R) :
    L.CK.Disjoint r := by
  obtain ⟨R, hR, hw⟩ := hi
  exact (h.ck R hR).sub_right hw.sub

/-- The disjoint scratch allocation leaves room for the hash's 64-byte prefix. -/
theorem Lay.Ok.message_bound {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 64 := by
  have hd := h.sc L.MSG (by simp [Lay.inputs])
  have nm := h.nm
  have nc := h.nc
  by_cases hz : L.len.toNat = 0
  · omega
  by_cases hp : L.msg ≤ L.scr
  · have hn : ¬ L.MSG.Contains L.scr 1 := fun hx => hd _ hx (by simp [Region.Contains])
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp] at hn
    have hp' : L.msg.toNat ≤ L.scr.toNat := hp
    omega
  · have hp' : L.scr ≤ L.msg := by
      change L.scr.toNat ≤ L.msg.toNat
      change ¬ L.msg.toNat ≤ L.scr.toNat at hp
      omega
    have hn : ¬ L.SCR.Contains L.msg 1 := fun hx => hd _ (by simp [Region.Contains]; omega) hx
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp'] at hn
    have hp'' : L.scr.toNat ≤ L.msg.toNat := hp'
    omega


abbrev Ctx (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) (g : Reg → BitVec 64) (v : VReg → BitVec 128) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g v m₀ L.inputs L.outputs t

namespace Ctx
variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem input_bytes (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t) (hL : L.Ok)
    {r : Region} (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem r.base r.len = Spec.Ed25519.bytesAt m₀ r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine Frame.bytes hc.frame ?_ hn (List.mem_range.mp hi)
  intro R hR
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact hL.sc r hr
  · exact (hL.ks r hr).symm
  · exact (hL.ck r hr).symm

theorem arg_word (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 6) :
    t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      m₀.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl | rfl
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm
    · exact (hL.ck _ ha).symm

end Ctx
end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def Arguments (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) (m : Mem) : Prop :=
  ∀ j < 5, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j

def known : Value → Prop
  | .caller j _ => j < 5
  | _ => True

def value (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) : Value → BitVec 64
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

def OutArgs (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) (args : List (Reg × Value)) (s : State) : Prop :=
  ∀ p ∈ args, s.gpr p.1 = VG.Proof.Ed25519.AArch64.VerifyMessage.value L p.2

variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem Ctx.value (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀)
    {a : Value} (hv : VG.Proof.Ed25519.AArch64.VerifyMessage.known a) : Whole.value L.E s.mem a = VG.Proof.Ed25519.AArch64.VerifyMessage.value L a := by
  cases a with
  | const => rfl
  | frame => rfl
  | caller j d =>
    change j < 5 at hv
    change s.mem.readW (L.E + BitVec.ofNat 64 (256 + 8*j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL (by omega), ha j hv]
    rfl

theorem args_ok (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hk : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.VerifyMessage.known p.2)
    (hregs : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) s fun t => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧
      t.mem = s.mem ∧ VG.Proof.Ed25519.AArch64.VerifyMessage.OutArgs L args t := by
  refine WP.mono (Whole.Ctx.setup hc hn hv (by simp [Lay.inputs, Lay.ARGS, Whole.ARGS]) hregs)
    fun t ⟨ht, hm, hvals⟩ => ⟨ht, hm, ?_⟩
  intro p hp
  exact (hvals p hp).trans (hc.value hL ha (hk p hp))

end VG.Proof.Ed25519.AArch64.VerifyMessage

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Body`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Hash`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem hash_writes : ∀ r ∈ Whole.hashWr L.scr,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  Whole.hash_writes (by simp [Lay.outputs])

theorem init_ok (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀) :
    WP isa init s fun t => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr [] := by
  unfold init VG.Impl.Ed25519.AArch64.Whole.callWith initArgs
  apply WP.seq
  refine WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.args_ok hc hL ha (args := [(.x0,.caller 4 0)]) (by decide) (by simp [Whole.valid]) (by simp [VG.Proof.Ed25519.AArch64.VerifyMessage.known]) (by decide)) ?_
  intro t ⟨ht, _, hv⟩
  have a0 : t.gpr .x0 = L.scr := by
    have hh := hv (.x0,.caller 4 0) (by simp)
    change t.gpr .x0 = L.scr + 0 at hh
    exact hh.trans (BitVec.add_zero _)
  have hw := Whole.init_writes (E := L.E) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call ht (Whole.init_pre a0)
    (Whole.covers_writes hw) hw a0) fun u ⟨hu, _, hr⟩ => ⟨hu, hr⟩

/-- Append a known input buffer without depending on its contents. -/
theorem update_ok (backend : Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok)
    (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀) {args : List (Reg × Value)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hk : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.VerifyMessage.known p.2) (hregs : ∀ p ∈ args, p.1 ∉ preserved)
    {p len : Addr} {prev : List Byte}
    (hargs : ∀ t, VG.Proof.Ed25519.AArch64.VerifyMessage.OutArgs L args t → t.gpr .x0 = L.scr ∧
      t.gpr .x1 = BitVec.ofNat 64 prev.length ∧ t.gpr .x2 = p ∧
      t.gpr .x3 = len ∧ t.gpr .x4 = L.scr + 192)
    (hd : Region.Disjoint ⟨p,len.toNat⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨p,len.toNat⟩ R)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix (setup args)) s fun t =>
      VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem p len.toNat) := by
  unfold update VG.Impl.Ed25519.AArch64.Whole.callWith
  apply WP.seq
  refine WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.args_ok hc hL ha hn hv hk hregs) ?_
  intro t ⟨ht, hm, hav⟩
  obtain ⟨a0,a1,a2,a3,a4⟩ := hargs t hav
  have hcov : Covers (Whole.updateRd p len ++ Whole.hashWr L.scr)
      (L.inputs ++ Whole.FR L.E :: L.outputs) := by
    refine Covers.of_sub fun R hR => ?_
    rcases List.mem_append.mp hR with hR | hR
    · simp only [Whole.updateRd, List.mem_singleton] at hR
      subst R
      obtain ⟨R,hR,hs⟩ := hi
      exact ⟨R,List.mem_append_left _ hR,hs⟩
    · rcases VG.Proof.Ed25519.AArch64.VerifyMessage.hash_writes R hR with hf | ⟨S,hS,hs⟩
      · exact ⟨Whole.FR L.E,List.mem_append_right _ List.mem_cons_self,hf⟩
      · exact ⟨S,List.mem_append_right _ (List.mem_cons_of_mem _ hS),hs⟩
  have hr' : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev := hm ▸ hr
  refine WP.mono (Whole.update_call backend ht (Whole.update_pre a0 a2 a3 a4 hd (by rw [ht.sp]; exact hL.e16)
    (by rw [ht.sp]; exact hL.cc) (by rw [ht.sp]; exact hL.ck_within hi))
    hcov VG.Proof.Ed25519.AArch64.VerifyMessage.hash_writes a0 a2 a3 a1 hr') fun u ⟨hu,_,huv⟩ => ⟨hu,?_⟩
  rw [hm] at huv
  exact huv

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Calls`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay}

def field (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) (d : Nat) : Region := ⟨L.E + BitVec.ofNat 64 d, 32⟩
def digest (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) : Region := ⟨L.E + BitVec.ofNat 64 192, 64⟩

theorem fieldWithin (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) {d : Nat} (hd : d + 32 ≤ 256) : Whole.Within (VG.Proof.Ed25519.AArch64.VerifyMessage.field L d) L.FR :=
  ⟨d, rfl, hd⟩
theorem digestWithin (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) : Whole.Within (VG.Proof.Ed25519.AArch64.VerifyMessage.digest L) L.FR := ⟨192, rfl, by change 192 + 64 ≤ 256; decide⟩
theorem scratchWithin (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩

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

theorem scratch_covered (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within L.SCR R :=
  ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed25519.AArch64.VerifyMessage.scratchWithin L⟩

theorem writes {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ Whole.Within r L.SCR) :
    ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rcases h r hr with hf | hs
  · exact .inl hf
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], hs⟩

theorem field_scr (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) :
    (VG.Proof.Ed25519.AArch64.VerifyMessage.field L d).Disjoint L.SCR := hL.kc.sub_left (VG.Proof.Ed25519.AArch64.VerifyMessage.fieldWithin L hd).sub

theorem field_mem {m n : Mem} (hm : n = m) (d : Nat) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by rw [hm]

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Equation`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

def challenge (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) : Region := ⟨L.E+128,64⟩
def equationRd (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) : List Region := [L.PK,L.SIG,VG.Proof.Ed25519.AArch64.VerifyMessage.challenge L]
def equationWr (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) : List Region := [L.SCR]
def EqArgs (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) (s : State) : Prop := s.gpr .x0 = L.pk ∧
  s.gpr .x1 = L.sig ∧ s.gpr .x2 = L.E+128 ∧ s.gpr .x3 = L.scr

theorem equation_noFrames : verifyEquation.noFrames = true := by lit_decide

theorem challengeWithin (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) : Whole.Within (VG.Proof.Ed25519.AArch64.VerifyMessage.challenge L) L.FR :=
  ⟨128,rfl,by change 128+64≤256; decide⟩

theorem equation_pre (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.EqArgs L s) :
    verifyLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.AArch64.VerifyMessage.equationRd L) (VG.Proof.Ed25519.AArch64.VerifyMessage.equationWr L)) := by
  simp only [verifyLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), ha.1,ha.2.1,ha.2.2.1,ha.2.2.2]
  exact ⟨rfl,rfl,hL.sc _ (by simp [Lay.inputs]),hL.sc _ (by simp [Lay.inputs]),
    hL.kc.sub_left (VG.Proof.Ed25519.AArch64.VerifyMessage.challengeWithin L).sub,hL.nc⟩

theorem equation_covers : Covers (VG.Proof.Ed25519.AArch64.VerifyMessage.equationRd L ++ VG.Proof.Ed25519.AArch64.VerifyMessage.equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
  apply VG.Proof.Ed25519.AArch64.VerifyMessage.covers
  simp only [VG.Proof.Ed25519.AArch64.VerifyMessage.equationRd,VG.Proof.Ed25519.AArch64.VerifyMessage.equationWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact .inr ⟨L.PK,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inr ⟨L.SIG,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inl (VG.Proof.Ed25519.AArch64.VerifyMessage.challengeWithin L)
  · exact .inr (VG.Proof.Ed25519.AArch64.VerifyMessage.scratch_covered L)

theorem equation_writes : ∀ r ∈ VG.Proof.Ed25519.AArch64.VerifyMessage.equationWr L,
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨L.SCR,by simp [Lay.outputs],VG.Proof.Ed25519.AArch64.VerifyMessage.scratchWithin L⟩

theorem equation_call (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.EqArgs L s) :
    WP isa (.call "vg_ed25519_verify_equation" verifyEquation) s fun t => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧
      t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem L.pk 32) (Spec.Ed25519.bytesAt s.mem L.sig 64)
        (Spec.Ed25519.bytesAt s.mem (L.E+128) 64)) := by
  refine Whole.call_ok hc verify_ok VG.Proof.Ed25519.AArch64.VerifyMessage.equation_noFrames (VG.Proof.Ed25519.AArch64.VerifyMessage.equation_pre hL ha)
    VG.Proof.Ed25519.AArch64.VerifyMessage.equation_covers VG.Proof.Ed25519.AArch64.VerifyMessage.equation_writes fun t ht _ hp => ⟨ht,?_⟩
  change t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x0) 32)
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x1) 64)
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x2) 64)) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),ha.1,ha.2.1,ha.2.2.1] at hp
  exact hp

theorem equation_step (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.AArch64.Whole.callWith VG.Impl.Ed25519.AArch64.VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation) s
      fun t => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧ t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem L.pk 32) (Spec.Ed25519.bytesAt s.mem L.sig 64)
        (Spec.Ed25519.bytesAt s.mem (L.E+128) 64)) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.args_ok hc hL ha
    (args := [(.x0,.caller 0 0),(.x1,.caller 3 0),(.x2,.frame 128),(.x3,.caller 4 0)])
    (by simp) (by simp [Whole.valid]) (by simp [VG.Proof.Ed25519.AArch64.VerifyMessage.known]) (by simp [preserved]))
    fun u ⟨hu,hm,hav⟩ => ?_)
  have a0 := hav (.x0,.caller 0 0) (by simp)
  have a1 := hav (.x1,.caller 3 0) (by simp)
  have a2 := hav (.x2,.frame 128) (by simp)
  have a3 := hav (.x3,.caller 4 0) (by simp)
  change u.gpr .x0 = L.pk+0#64 at a0
  change u.gpr .x1 = L.sig+0#64 at a1
  change u.gpr .x3 = L.scr+0#64 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  refine WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.equation_call hu hL ⟨a0,a1,a2,a3⟩) fun t ⟨ht,hp⟩ => ⟨ht,?_⟩
  rw [hm] at hp
  exact hp

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.HashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.HashInputs`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem prefix_step (backend : Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok)
    (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀) {source count : Nat} (hsource : source < 5)
    (hcount : count < 65536) {prev : List Byte} (hp : prev.length = count)
    (hd : Region.Disjoint ⟨L.value source,32⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨L.value source,32⟩ R)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix (prefixArgs source count)) s fun t =>
      VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem (L.value source) 32) := by
  apply VG.Proof.Ed25519.AArch64.VerifyMessage.update_ok backend hc hL ha (by simp)
    (by simp [Whole.valid]; omega) (by simp [VG.Proof.Ed25519.AArch64.VerifyMessage.known]; exact hsource) (by simp [preserved])
    (p := L.value source) (len := 32) (prev := prev) ?_ hd hi hr
  intro t hav
  have a0 := hav (.x0,.caller 4 0) (by simp)
  have a1 := hav (.x1,.const count) (by simp)
  have a2 := hav (.x2,.caller source 0) (by simp)
  have a3 := hav (.x3,.const 32) (by simp)
  have a4 := hav (.x4,.caller 4 192) (by simp)
  change t.gpr .x0 = L.scr + 0#64 at a0
  change t.gpr .x2 = L.value source + 0#64 at a2
  rw [BitVec.add_zero] at a0 a2
  exact ⟨a0, by rw [hp]; exact a1, a2, a3, a4⟩

theorem message_step (backend : Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok)
    (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀) {prev : List Byte} (hp : prev.length = 64)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix messageArgs) s fun t =>
      VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem L.msg L.len.toNat) := by
  apply VG.Proof.Ed25519.AArch64.VerifyMessage.update_ok backend hc hL ha (by simp) (by simp [Whole.valid])
    (by simp [VG.Proof.Ed25519.AArch64.VerifyMessage.known]) (by decide) (p := L.msg) (len := L.len) (prev := prev) ?_
    (hL.sc _ (by simp [Lay.inputs])) ?_ hr
  · intro t hav
    have a0 := hav (.x0,.caller 4 0) (by simp)
    have a1 := hav (.x1,.const 64) (by simp)
    have a2 := hav (.x2,.caller 1 0) (by simp)
    have a3 := hav (.x3,.caller 2 0) (by simp)
    have a4 := hav (.x4,.caller 4 192) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    change t.gpr .x2 = L.msg + 0#64 at a2
    change t.gpr .x3 = L.len + 0#64 at a3
    rw [BitVec.add_zero] at a0 a2 a3
    exact ⟨a0, by rw [hp]; exact a1, a2, a3, a4⟩
  · exact ⟨L.MSG, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by simp⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.HashFinalize`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem finalize_writes : ∀ r ∈ Whole.finalizeWr L.scr (L.E+192),
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0+192≤8192; decide⟩
  · exact .inl ⟨192, rfl, by change 192+64≤256; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192+688≤8192; decide⟩

theorem finalize_ok (backend : Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok)
    (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀) {msg : List Byte}
    (hm : msg.length = 64 + L.len.toNat)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr msg) :
    WP isa (finalize backend.code backend.suffix) s fun t => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E+192) 64 = Spec.Sha512.finalHash Spec.Sha512.H0_512 msg := by
  unfold finalize VG.Impl.Ed25519.AArch64.Whole.callWith finalizeArgs
  apply WP.seq
  refine WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.args_ok hc hL ha
    (args := [(.x0,.caller 4 0),(.x1,.caller 2 64),(.x2,.frame 192),(.x3,.caller 4 192)])
    (by decide) (by simp [Whole.valid]) (by simp [VG.Proof.Ed25519.AArch64.VerifyMessage.known]) (by decide)) ?_
  intro t ⟨ht, htmem, hav⟩
  have a0 : t.gpr .x0 = L.scr := by
    have hh := hav (.x0,.caller 4 0) (by simp)
    change t.gpr .x0 = L.scr + 0 at hh
    exact hh.trans (BitVec.add_zero _)
  have a1 : t.gpr .x1 = BitVec.ofNat 64 msg.length := by
    have hh := hav (.x1,.caller 2 64) (by simp)
    change t.gpr .x1 = L.len + 64 at hh
    rw [hh, hm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.add_comm]
    rfl
  have a2 : t.gpr .x2 = L.E+192 := hav (.x2,.frame 192) (by simp)
  have a3 : t.gpr .x3 = L.scr+192 := hav (.x3,.caller 4 192) (by simp)
  have hd : Region.Disjoint ⟨L.E+192,64⟩ L.SCR :=
    hL.kc.sub_left (Offset.sub_base _ (by decide))
  have hr' : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr msg := htmem ▸ hr
  refine WP.mono (Whole.finalize_call backend ht (Whole.finalize_pre a0 a2 a3 hd (by rw [ht.sp]; exact hL.e16)
    (by rw [ht.sp]; exact hL.cc) (by rw [ht.sp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)))
    (Whole.covers_writes VG.Proof.Ed25519.AArch64.VerifyMessage.finalize_writes) VG.Proof.Ed25519.AArch64.VerifyMessage.finalize_writes a0 a2 a1 hr'
    (by rw [hm]; exact hL.message_bound)) fun u ⟨hu,_,hp⟩ => ⟨hu,hp⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

def hashInput (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m L.sig 32 ++
    Spec.Ed25519.bytesAt m L.pk 32 ++
    Spec.Ed25519.bytesAt m L.msg L.len.toNat

theorem bytes_length (m : Mem) (p : BitVec 64) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

theorem sig_prefix_same (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok) :
    Spec.Ed25519.bytesAt s.mem L.sig 32 = Spec.Ed25519.bytesAt m₀ L.sig 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hc.frame.bytes (R := L.SIG) (by
    intro r hr
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.sc _ (by simp [Lay.inputs])
    · exact (hL.ks _ (by simp [Lay.inputs])).symm
    · exact (hL.ck _ (by simp [Lay.inputs])).symm)
    (by change 64 ≤ 2 ^ 64; decide) (by change i < 64; have := List.mem_range.mp hi; omega)

theorem input_sig (hL : L.Ok) : Region.Disjoint ⟨L.value 3,32⟩ L.SCR ∧
    ∃ R ∈ L.inputs, Whole.Within ⟨L.value 3,32⟩ R := by
  refine ⟨(hL.sc L.SIG (by simp [Lay.inputs])).sub_left (Region.sub_prefix (by decide)),
    L.SIG, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, ?_⟩
  change 0+32≤64
  decide

theorem input_pk (hL : L.Ok) : Region.Disjoint ⟨L.value 0,32⟩ L.SCR ∧
    ∃ R ∈ L.inputs, Whole.Within ⟨L.value 0,32⟩ R := by
  refine ⟨hL.sc L.PK (by simp [Lay.inputs]), L.PK, by simp [Lay.inputs], 0,
    (BitVec.add_zero _).symm, ?_⟩
  change 0+32≤32
  decide

theorem hash_ok (backend : Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s)
    (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀) :
    WP isa (hash backend.code backend.suffix) s fun t => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = Spec.Sha512.sha512 (VG.Proof.Ed25519.AArch64.VerifyMessage.hashInput L m₀) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.init_ok hc hL ha) fun t ⟨ht,hinit⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.prefix_step backend ht hL ha (source := 3) (count := 0)
    (by decide) (by decide) rfl (VG.Proof.Ed25519.AArch64.VerifyMessage.input_sig hL).1 (VG.Proof.Ed25519.AArch64.VerifyMessage.input_sig hL).2 hinit)
    fun u ⟨hu,hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem L.sig 32) at hsig
  rw [List.nil_append, VG.Proof.Ed25519.AArch64.VerifyMessage.sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.prefix_step backend hu hL ha (source := 0) (count := 32)
    (by decide) (by decide) (VG.Proof.Ed25519.AArch64.VerifyMessage.bytes_length _ _ _) (VG.Proof.Ed25519.AArch64.VerifyMessage.input_pk hL).1 (VG.Proof.Ed25519.AArch64.VerifyMessage.input_pk hL).2 hsig)
    fun w ⟨hw,hpk⟩ => ?_)
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem L.pk 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide)] at hpk
  have hpkl : (Spec.Ed25519.bytesAt m₀ L.sig 32 ++ Spec.Ed25519.bytesAt m₀ L.pk 32).length = 64 := by
    rw [List.length_append, VG.Proof.Ed25519.AArch64.VerifyMessage.bytes_length, VG.Proof.Ed25519.AArch64.VerifyMessage.bytes_length]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.message_step backend hw hL ha hpkl hpk) fun z ⟨hz,hmsg⟩ => ?_)
  rw [hw.input_bytes hL (r := L.MSG) (by simp [Lay.inputs])
    (by have := L.len.isLt; change L.len.toNat≤2^64; omega)] at hmsg
  have hlen : (VG.Proof.Ed25519.AArch64.VerifyMessage.hashInput L m₀).length = 64 + L.len.toNat := by
    simp only [VG.Proof.Ed25519.AArch64.VerifyMessage.hashInput, List.length_append, VG.Proof.Ed25519.AArch64.VerifyMessage.bytes_length]
  exact VG.Proof.Ed25519.AArch64.VerifyMessage.finalize_ok backend hz hL ha hlen hmsg

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Challenge`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Reduce`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
open VG.Impl.Ed25519.AArch64 (scalarReduce)

def reduceRd (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) : List Region := [VG.Proof.Ed25519.AArch64.VerifyMessage.digest L]
def reduceWr (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) (d : Nat) : List Region := [VG.Proof.Ed25519.AArch64.VerifyMessage.field L d, L.SCR]
def ReduceArgs (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .x0 = L.E + BitVec.ofNat 64 d ∧ s.gpr .x1 = L.E + 192 ∧ s.gpr .x2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.AArch64.VerifyMessage.reduceRd L) (VG.Proof.Ed25519.AArch64.VerifyMessage.reduceWr L d)) := by
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2]
  exact ⟨rfl, rfl, hL.kc.sub_left (VG.Proof.Ed25519.AArch64.VerifyMessage.digestWithin L).sub⟩

theorem reduce_call (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256)
    (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧
      Frame (VG.Proof.Ed25519.AArch64.VerifyMessage.reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  have cov : Covers (VG.Proof.Ed25519.AArch64.VerifyMessage.reduceRd L ++ VG.Proof.Ed25519.AArch64.VerifyMessage.reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.AArch64.VerifyMessage.covers
    simp only [VG.Proof.Ed25519.AArch64.VerifyMessage.reduceRd, VG.Proof.Ed25519.AArch64.VerifyMessage.reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.VerifyMessage.digestWithin L)
    · exact .inl (VG.Proof.Ed25519.AArch64.VerifyMessage.fieldWithin L hd)
    · exact .inr (VG.Proof.Ed25519.AArch64.VerifyMessage.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.AArch64.VerifyMessage.reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.AArch64.VerifyMessage.writes
    simp only [VG.Proof.Ed25519.AArch64.VerifyMessage.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.VerifyMessage.fieldWithin L hd)
    · exact .inr (VG.Proof.Ed25519.AArch64.VerifyMessage.scratchWithin L)
  refine Whole.call_ok hc scalarReduce_ok VG.Proof.Ed25519.AArch64.VerifyMessage.reduce_noFrames (VG.Proof.Ed25519.AArch64.VerifyMessage.reduce_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarReduceLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] using hp

theorem reduce_step (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.AArch64.Whole.callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce) s
      fun t => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧ Frame (VG.Proof.Ed25519.AArch64.VerifyMessage.reduceWr L 128) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 128) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.args_ok hc hL ha
    (args := [(.x0, .frame 128), (.x1, .frame 192), (.x2, .caller 4 0)])
    (by simp) (by simp [Whole.valid]) (by simp [VG.Proof.Ed25519.AArch64.VerifyMessage.known]) (by simp [preserved]))
    fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .frame 128) (by simp)
  have a1 := hs (.x1, .frame 192) (by simp)
  have a2 := hs (.x2, .caller 4 0) (by simp)
  change u.gpr .x2 = L.scr + 0#64 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.reduce_call hu hL (d := 128) (by decide) ⟨a0,a1,a2⟩)
    fun t ⟨ht,hf,hp⟩ => ⟨ht,?_,?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, Proof.Ed25519.AArch64.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem extend_step (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (L.E + 128) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 20) (count := 4) (by decide)) fun t ⟨ht, hf, hz⟩ => ⟨ht, ?_⟩
  have low : Spec.Ed25519.bytesAt t.mem (L.E + 128) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E + 128) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨L.E + 128, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have high : Spec.Ed25519.bytesAt t.mem (L.E + 160) 32 = Spec.Ed25519.encodeLE 32 0 := by
    rw [Proof.Ed25519.AArch64.encodeLE_eq]
    have word (j : Nat) (hj : j < 4) : t.mem.readW (L.E + 160 + BitVec.ofNat 64 (8*j)) 64 = 0 := by
      have z := hz j hj
      have e : L.E + BitVec.ofNat 64 (8*(20+j)) = L.E + 160 + BitVec.ofNat 64 (8*j) := by
        rw [show 8*(20+j)=160+8*j by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [e] at z
      exact z
    apply Proof.X25519.bytesAt_leBytes_words64
    · have z := word 0 (by decide)
      simpa using congrArg BitVec.toNat z
    · have z := word 1 (by decide)
      simpa using congrArg BitVec.toNat z
    · have z := word 2 (by decide)
      simpa using congrArg BitVec.toNat z
    · have z := word 3 (by decide)
      simpa using congrArg BitVec.toNat z
  change Spec.X25519.bytesAt t.mem (L.E + 128) (32 + 32) = _
  rw [Proof.X25519.bytesAt_add]
  change Spec.Ed25519.bytesAt t.mem (L.E + 128) 32 ++
    Spec.Ed25519.bytesAt t.mem (L.E + 128 + 32) 32 = _
  rw [show L.E + 128 + 32 = L.E + 160 by rw [BitVec.add_assoc]; rfl,
    low, hd, high, VG.Proof.Ed25519.AArch64.VerifyMessage.reduced_challenge]

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) (m : Mem) : VG.Proof.Ed25519.AArch64.VerifyMessage.hashInput L m =
    (Spec.Ed25519.bytesAt m L.sig 64).take 32 ++
      Spec.Ed25519.bytesAt m L.pk 32 ++
      Spec.Ed25519.bytesAt m L.msg L.len.toNat := by
  have e : (Spec.Ed25519.bytesAt m L.sig 64).take 32 =
      Spec.Ed25519.bytesAt m L.sig 32 := by
    unfold Spec.Ed25519.bytesAt
    rw [← List.map_take, List.take_range]
    rfl
  rw [e]
  rfl

theorem body_ok (backend : Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ s) (hL : L.Ok)
    (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₀) :
    WP isa (body backend.code backend.suffix) s fun t => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m₀ t ∧
      t.gpr .x0 = signWord (Spec.Ed25519.verify (Spec.Ed25519.bytesAt m₀ L.pk 32)
        (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) (Spec.Ed25519.bytesAt m₀ L.sig 64)) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.hash_ok backend hc hL ha) fun t ⟨ht,hh⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.reduce_step ht hL ha) fun u ⟨hu,_,hr⟩ => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.extend_step hu hr) fun w ⟨hw,he⟩ => ?_)
  rw [VG.Proof.Ed25519.AArch64.VerifyMessage.hashInput_eq] at he
  refine WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.equation_step hw hL ha) fun z ⟨hz,eq⟩ => ⟨hz,?_⟩
  rw [hw.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide),
    hw.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64≤2^64; decide),he] at eq
  exact eq

theorem body_depth (backend : Whole.Backend) : (body backend.code backend.suffix).aarch64Depth ≤ 1 := by
  have hu := Whole.update_depth backend
  have hf := Whole.finalize_depth backend
  change (Impl.Sha512.AArch64.Stream.updateWith backend.suffix backend.code).aarch64Depth ≤ 1 at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith backend.suffix backend.code).aarch64Depth ≤ 1 at hf
  have hr := Whole.depth_zero_of_noFrames VG.Proof.Ed25519.AArch64.VerifyMessage.reduce_noFrames
  have he := Whole.depth_zero_of_noFrames VG.Proof.Ed25519.AArch64.VerifyMessage.equation_noFrames
  simp only [body,Impl.Ed25519.AArch64.VerifyMessage.hash,init,update,finalize,Impl.Ed25519.AArch64.Whole.callWith,
    Code.aarch64Depth, Nat.max_le,Impl.Sha512.AArch64.Stream.init,hr,he]
  omega

end VG.Proof.Ed25519.AArch64.VerifyMessage

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTReady`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTCommon`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

def Two (L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay) (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128)
    (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g₁ v₁ m₁ a ∧ VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g₂ v₂ m₂ b ∧ P a ∧ P b

theorem two_sp {P : State → Prop} {a b : State} (h : VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ P a b) :
    a.sp = b.sp := h.1.sp.trans h.2.1.sp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g₁ v₁ m₁ t → P t → WP isa c t fun u => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g₁ v₁ m₁ u ∧ Q u)
    (hb : ∀ t, VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g₂ v₂ m₂ t → P t → WP isa c t fun u => VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g₂ v₂ m₂ u ∧ Q u) :
    RelCT isa (VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c (VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.VerifyMessage.Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hk : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.VerifyMessage.known p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.VerifyMessage.OutArgs L args)) := by
  refine VG.Proof.Ed25519.AArch64.VerifyMessage.two_wp (Whole.block_rel (fun _ _ h => VG.Proof.Ed25519.AArch64.VerifyMessage.two_sp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.args_ok hc hL ha hn hv hk hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (VG.Proof.Ed25519.AArch64.VerifyMessage.args_ok hc hL hb hn hv hk hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem args_eq {args : List (Reg × Value)} {a b : State}
    (h : VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.VerifyMessage.OutArgs L args) a b) {p : Reg × Value} (hp : p ∈ args) :
    a.gpr p.1 = b.gpr p.1 := (h.2.2.1 p hp).trans (h.2.2.2 p hp).symm

theorem call_gpr_eq {args : List (Reg × Value)} {a b : State}
    (h : VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.VerifyMessage.OutArgs L args) a b) {p : Reg × Value}
    (hp : p ∈ args) (hl : p.1 ∉ linkRegs) : a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := by
  rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl]
  exact VG.Proof.Ed25519.AArch64.VerifyMessage.args_eq h hp

theorem call_ct {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ {g v m t}, VG.Proof.Ed25519.AArch64.VerifyMessage.Ctx L g v m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ P) (.call name c)
      (VG.Proof.Ed25519.AArch64.VerifyMessage.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.VerifyMessage.two_wp
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.1
    let rb := ready h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := Whole.CallReady.covers_state h.1 ra
    obtain ⟨cb, wb⟩ := Whole.CallReady.covers_state h.2.1 rb
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb⟩
  · intro t hc hs
    exact WP.mono (Whole.CallReady.wpF hc (ready hc hs) correct hd) fun _ hu => ⟨hu, trivial⟩
  · intro t hc hs
    exact WP.mono (Whole.CallReady.wpF hc (ready hc hs) correct hd) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64
variable {L : VG.Proof.Ed25519.AArch64.VerifyMessage.Lay} {t : State}

def init_ready (h0 : t.gpr .x0=L.scr) :
    Whole.CallReady (Proof.Sha512.initAArch64 Spec.Sha512.H0_512) L.E L.inputs L.outputs t :=
  ⟨[],Whole.initWr L.scr,Whole.init_pre h0,
    Whole.covers_writes (Whole.init_writes (by simp [Lay.outputs])),
    Whole.init_writes (by simp [Lay.outputs])⟩

def update_ready (hL : L.Ok) (hsp : t.sp = L.E) {p len : Addr} (h0 : t.gpr .x0=L.scr) (h2 : t.gpr .x2=p)
    (h3 : t.gpr .x3=len) (h4 : t.gpr .x4=L.scr+192)
    (hd : Region.Disjoint ⟨p,len.toNat⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨p,len.toNat⟩ R) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  refine ⟨Whole.updateRd p len,Whole.hashWr L.scr,Whole.update_pre h0 h2 h3 h4 hd (by rw [hsp]; exact hL.e16)
    (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hL.ck_within hi),?_,VG.Proof.Ed25519.AArch64.VerifyMessage.hash_writes⟩
  apply VG.Proof.Ed25519.AArch64.VerifyMessage.covers
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    obtain ⟨R,hR,hs⟩ := hi
    exact .inr ⟨R,List.mem_append_left _ hR,hs⟩
  · rcases VG.Proof.Ed25519.AArch64.VerifyMessage.hash_writes r hr with hf | ⟨R,hR,hs⟩
    · exact .inl hf
    · exact .inr ⟨R,List.mem_append_right _ hR,hs⟩

def finalize_ready (hL : L.Ok) (hsp : t.sp = L.E) (h0 : t.gpr .x0=L.scr)
    (h2 : t.gpr .x2=L.E+192) (h3 : t.gpr .x3=L.scr+192) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs t :=
  ⟨[],Whole.finalizeWr L.scr (L.E+192),Whole.finalize_pre h0 h2 h3
    (hL.kc.sub_left (Offset.sub_base _ (by decide))) (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
    (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes VG.Proof.Ed25519.AArch64.VerifyMessage.finalize_writes,VG.Proof.Ed25519.AArch64.VerifyMessage.finalize_writes⟩

def reduce_ready (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.ReduceArgs L 128 t) :
    Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs t := by
  refine ⟨VG.Proof.Ed25519.AArch64.VerifyMessage.reduceRd L,VG.Proof.Ed25519.AArch64.VerifyMessage.reduceWr L 128,VG.Proof.Ed25519.AArch64.VerifyMessage.reduce_pre hL ha,?_,?_⟩
  · apply VG.Proof.Ed25519.AArch64.VerifyMessage.covers
    simp only [VG.Proof.Ed25519.AArch64.VerifyMessage.reduceRd,VG.Proof.Ed25519.AArch64.VerifyMessage.reduceWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.VerifyMessage.digestWithin L)
    · exact .inl (VG.Proof.Ed25519.AArch64.VerifyMessage.fieldWithin L (by decide))
    · exact .inr (VG.Proof.Ed25519.AArch64.VerifyMessage.scratch_covered L)
  · apply VG.Proof.Ed25519.AArch64.VerifyMessage.writes
    simp only [VG.Proof.Ed25519.AArch64.VerifyMessage.reduceWr,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.VerifyMessage.fieldWithin L (by decide))
    · exact .inr (VG.Proof.Ed25519.AArch64.VerifyMessage.scratchWithin L)

def equation_ready (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.VerifyMessage.EqArgs L t) :
    Whole.CallReady verifyLocal L.E L.inputs L.outputs t :=
  ⟨VG.Proof.Ed25519.AArch64.VerifyMessage.equationRd L,VG.Proof.Ed25519.AArch64.VerifyMessage.equationWr L,VG.Proof.Ed25519.AArch64.VerifyMessage.equation_pre hL ha,VG.Proof.Ed25519.AArch64.VerifyMessage.equation_covers,VG.Proof.Ed25519.AArch64.VerifyMessage.equation_writes⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Verified`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTHashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTHash`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

def initValues : List (Reg × Value) := [(.x0,.caller 4 0)]
def prefixValues (source count : Nat) : List (Reg × Value) :=
  [(.x0,.caller 4 0),(.x1,.const count),(.x2,.caller source 0),(.x3,.const 32),(.x4,.caller 4 192)]
def messageValues : List (Reg × Value) :=
  [(.x0,.caller 4 0),(.x1,.const 64),(.x2,.caller 1 0),(.x3,.caller 2 0),(.x4,.caller 4 192)]
def finalizeValues : List (Reg × Value) :=
  [(.x0,.caller 4 0),(.x1,.caller 2 64),(.x2,.frame 192),(.x3,.caller 4 192)]

theorem init_call_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L initValues))
    (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 (Whole.depth_of_noFrames rfl)
  · intro g v m t _ hs
    have a0 := hs (.x0,.caller 4 0) (by simp [initValues])
    change t.gpr .x0 = L.scr+0#64 at a0
    exact init_ready (a0.trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    simp only [Proof.Sha512.initAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨call_gpr_eq h (p := (.x0,.caller 4 0)) (by simp [initValues]) (by decide),two_sp h⟩

theorem update_call_ct (backend : Whole.Backend) {args : List (Reg × Value)}
    (ready : ∀ {t}, t.sp = L.E → OutArgs L args t →
      Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t)
    (hregs : ∀ r ∈ ([.x0,.x1,.x2,.x3,.x4] : List Reg), ∃ a, (r,a)∈args) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args))
      (.call (Spec.Sha512.updateScratchApi.name ++ backend.suffix) backend.update)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct backend.update_verified.1 backend.update_verified.2.1 (Whole.update_depth backend) (fun hc h => ready hc.sp h)
  intro a b ar aw br bw h
  have eq (r : Reg) (hr : r ∈ ([.x0,.x1,.x2,.x3,.x4] : List Reg)) : a.callEntry.gpr r=b.callEntry.gpr r := by
    obtain ⟨val,hval⟩ := hregs r hr
    exact call_gpr_eq h hval ((by decide : ∀ r ∈ ([.x0,.x1,.x2,.x3,.x4] : List Reg),r∉linkRegs) r hr)
  simp only [Proof.Sha512.updateAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
  exact ⟨eq .x0 (by simp),eq .x1 (by simp),eq .x2 (by simp),eq .x3 (by simp),eq .x4 (by simp),two_sp h⟩

theorem finalize_call_ct (backend : Whole.Backend) (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L finalizeValues))
      (.call (Spec.Sha512.finalizeScratchApi.name ++ backend.suffix) backend.finalize)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct backend.finalize_verified.1 backend.finalize_verified.2.1 (Whole.finalize_depth backend)
  · intro g v m t hc hs
    have a0 := hs (.x0,.caller 4 0) (by simp [finalizeValues])
    have a2 := hs (.x2,.frame 192) (by simp [finalizeValues])
    have a3 := hs (.x3,.caller 4 192) (by simp [finalizeValues])
    change t.gpr .x0=L.scr+0#64 at a0
    exact finalize_ready hL hc.sp (a0.trans (BitVec.add_zero _)) a2 a3
  · intro a b ar aw br bw h
    simp only [Proof.Sha512.finalizeAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨call_gpr_eq h (p := (.x0,.caller 4 0)) (by simp [finalizeValues]) (by decide),
      call_gpr_eq h (p := (.x1,.caller 2 64)) (by simp [finalizeValues]) (by decide),
      call_gpr_eq h (p := (.x2,.frame 192)) (by simp [finalizeValues]) (by decide),
      call_gpr_eq h (p := (.x3,.caller 4 192)) (by simp [finalizeValues]) (by decide),two_sp h⟩

def prefix_ready (hL : L.Ok) {source count : Nat}
    (hd : Region.Disjoint ⟨L.value source,32⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨L.value source,32⟩ R) {t : State} (hsp : t.sp = L.E)
    (hs : OutArgs L (prefixValues source count) t) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  have a0 := hs (.x0,.caller 4 0) (by simp [prefixValues])
  have a2 := hs (.x2,.caller source 0) (by simp [prefixValues])
  have a3 := hs (.x3,.const 32) (by simp [prefixValues])
  have a4 := hs (.x4,.caller 4 192) (by simp [prefixValues])
  change t.gpr .x0=L.scr+0#64 at a0
  change t.gpr .x2=L.value source+0#64 at a2
  exact update_ready hL hsp (a0.trans (BitVec.add_zero _)) (a2.trans (BitVec.add_zero _)) a3 a4 hd hi

def message_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : OutArgs L messageValues t) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  have a0 := hs (.x0,.caller 4 0) (by simp [messageValues])
  have a2 := hs (.x2,.caller 1 0) (by simp [messageValues])
  have a3 := hs (.x3,.caller 2 0) (by simp [messageValues])
  have a4 := hs (.x4,.caller 4 192) (by simp [messageValues])
  change t.gpr .x0=L.scr+0#64 at a0
  change t.gpr .x2=L.msg+0#64 at a2
  change t.gpr .x3=L.len+0#64 at a3
  exact update_ready hL hsp (a0.trans (BitVec.add_zero _)) (a2.trans (BitVec.add_zero _))
    (a3.trans (BitVec.add_zero _)) a4 (hL.sc _ (by simp [Lay.inputs]))
    ⟨L.MSG,by simp [Lay.inputs],0,(BitVec.add_zero _).symm,by simp⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem hash_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hash backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have i := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb initValues
    (by decide) (by simp [initValues,Whole.valid]) (by simp [initValues,known])
    (by simp [initValues,preserved]) (by taint_decide)
  have r := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb (prefixValues 3 0)
    (by decide) (by simp [prefixValues,Whole.valid]) (by simp [prefixValues,known])
    (by simp [prefixValues,preserved]) (by taint_decide)
  have a := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb (prefixValues 0 32)
    (by decide) (by simp [prefixValues,Whole.valid]) (by simp [prefixValues,known])
    (by simp [prefixValues,preserved]) (by taint_decide)
  have m := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb messageValues
    (by decide) (by simp [messageValues,Whole.valid]) (by simp [messageValues,known])
    (by simp [messageValues,preserved]) (by taint_decide)
  have f := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb finalizeValues
    (by decide) (by simp [finalizeValues,Whole.valid]) (by simp [finalizeValues,known])
    (by simp [finalizeValues,preserved]) (by taint_decide)
  have rc := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend (args := prefixValues 3 0) (prefix_ready hL (input_sig hL).1 (input_sig hL).2)
    (by simp [prefixValues])
  have ac := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend (args := prefixValues 0 32) (prefix_ready hL (input_pk hL).1 (input_pk hL).2)
    (by simp [prefixValues])
  have mc := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend (args := messageValues) (message_ready hL) (by simp [messageValues])
  exact (i.seq init_call_ct).seq ((r.seq rc).seq ((a.seq ac).seq ((m.seq mc).seq (f.seq (finalize_call_ct backend hL)))))

/-- Public inputs give a common digest for the equation check that follows. -/
theorem hash_result_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hm : hashInput L m₁ = hashInput L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hash backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+192) 64 =
        Spec.Sha512.sha512 (hashInput L m₁)) := by
  refine two_wp ((hash_ct backend hL ha hb).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc _
    exact hash_ok backend hc hL ha
  · intro s hc _
    have h := hash_ok backend hc hL hb
    rw [← hm] at h
    exact h

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Entry`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64

def verifyMessageLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .x0,32⟩
    let msg : Region := ⟨s.gpr .x1,(s.gpr .x2).toNat⟩
    let sig : Region := ⟨s.gpr .x3,64⟩
    let scr : Region := ⟨s.gpr .x4,8192⟩
    let stk : Region := below s.sp 352
    s.rd = [pk,msg,sig] ∧ s.wr = [scr] ∧
    pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧
    stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
    (s.gpr .x0).toNat+32≤2^64 ∧ (s.gpr .x1).toNat+(s.gpr .x2).toNat≤2^64 ∧
    (s.gpr .x3).toNat+64≤2^64 ∧ (s.gpr .x4).toNat+8192≤2^64 ∧ 352≤s.sp.toNat
  post s t := t.gpr .x0 = if Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .x3) 64) then 1 else 0
  pub s t := s.sp=t.sp ∧ s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧
    s.gpr .x2=t.gpr .x2 ∧ s.gpr .x3=t.gpr .x3 ∧ s.gpr .x4=t.gpr .x4 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32 = Spec.Ed25519.bytesAt t.mem (t.gpr .x0) 32 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Ed25519.bytesAt t.mem (t.gpr .x1) (t.gpr .x2).toNat ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x3) 64 = Spec.Ed25519.bytesAt t.mem (t.gpr .x3) 64

def lay (s : State) : Lay := ⟨s.gpr .x0,s.gpr .x1,s.gpr .x2,s.gpr .x3,s.gpr .x4,Whole.base s⟩

theorem entry_below {s : State} (h : verifyMessageLocal.pre s) : 352≤s.sp.toNat := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hb⟩ := h
  exact hb

theorem entry_writes {s : State} (h : verifyMessageLocal.pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  obtain ⟨_,hw,_,_,_,_,_,_,hc,_⟩ := h
  intro r hr
  rw [hw,List.mem_singleton] at hr
  subst r
  exact hc

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨_,_,pc,mc,sc,kp,km,ks,kc,np,nm,ns,nc,hb⟩ := h
  have stk := Whole.stk_sub s
  have fr : Region.Sub (Whole.FR (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Region.sub_prefix (by decide) : Region.Sub (Whole.FR (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Offset.sub_base _ (by decide) : Region.Sub (Whole.ARGS (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ck := Whole.ck_sub s
  refine ⟨?_,?_,?_,kc.sub_left fr,np,nm,ns,nc,Whole.base_16 hb,?_,kc.sub_left ck⟩
  · change (s.sp-336#64).toNat+304≤2^64
    rw [BitVec.toNat_sub_of_le (by change 336≤s.sp.toNat; omega)]
    have hs := s.sp.isLt
    change s.sp.toNat-336+304≤2^64
    omega
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact pc
    · exact mc
    · exact sc
    · exact kc.sub_left ar
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact ks.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact kp.sub_left ck
    · exact km.sub_left ck
    · exact ks.sub_left ck
    · exact Whole.ck_frame (by decide : 256 + 48 ≤ 304)

theorem entry_ctx {s p : State} (h : verifyMessageLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr s.v p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd,h.1,Whole.bodyWr,h.2.1,Ctx,Lay.inputs,Lay.outputs,
    Lay.PK,Lay.MSG,Lay.SIG,Lay.SCR,Lay.ARGS,lay,List.cons_append,List.nil_append] using hc

theorem entry_args {s p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hp (j := j) (by omega)
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl <;> exact hw

theorem entry_input {s : State} (h : verifyMessageLocal.pre s) {m : Mem}
    (hf : Frame [below s.sp 336] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len≤2^64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  obtain ⟨hrd,_,_,_,_,kp,km,ks,_⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  have hb : Region.Sub (below s.sp 336) (below s.sp 352) := below_sub (by decide) (by decide)
  rcases hr with rfl | rfl | rfl
  · exact (kp.sub_left hb).symm
  · exact (km.sub_left hb).symm
  · exact (ks.sub_left hb).symm

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CT`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTScalars`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

def reduceValues : List (Reg × Value) := [(.x0,.frame 128),(.x1,.frame 192),(.x2,.caller 4 0)]

theorem reduce_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L reduceValues))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarReduce_ok scalarReduce_ct (Whole.depth_of_noFrames reduce_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0,.frame 128) (by simp [reduceValues])
    have a1 := hs (.x1,.frame 192) (by simp [reduceValues])
    have a2 := hs (.x2,.caller 4 0) (by simp [reduceValues])
    change t.gpr .x2=L.scr+0#64 at a2
    exact reduce_ready hL ⟨a0,a1,a2.trans (BitVec.add_zero _)⟩
  · intro a b ar aw br bw h
    simp only [scalarReduceLocal,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨two_sp h,call_gpr_eq h (p := (.x0,.frame 128)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.x1,.frame 192)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.x2,.caller 4 0)) (by simp [reduceValues]) (by decide)⟩

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+192) 64=digest)
      (callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 32=Spec.Ed25519.scalarReduce digest) := by
  have hs := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb reduceValues
    (by decide) (by simp [reduceValues,Whole.valid]) (by simp [reduceValues,known])
    (by simp [reduceValues,preserved]) (by taint_decide)
  refine two_wp ((hs.seq (reduce_call_ct hL)).mono
    (fun _ _ h => ⟨h.1,h.2.1,trivial,trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc hd
    exact WP.mono (reduce_step hc hL ha) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩
  · intro s hc hd
    exact WP.mono (reduce_step hc hL hb) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩

theorem extend_ct (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 32=Spec.Ed25519.scalarReduce digest)
      (.block extendChallenge)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 64=
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro s hc hd
    exact extend_step hc hd
  · intro s hc hd
    exact extend_step hc hd

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTEquation`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem equation_setup_wp {g v m t} (hc : Ctx L g v m t) (hL : L.Ok) (ha : Arguments L m)
    {ch : List Byte} (hh : Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = ch) :
    WP isa (.block VerifyMessage.equationArgs) t fun u => Ctx L g v m u ∧ EqArgs L u ∧
      Spec.Ed25519.bytesAt u.mem (L.E + 128) 64 = ch := by
  refine WP.mono (args_ok hc hL ha
    (args := [(.x0,.caller 0 0),(.x1,.caller 3 0),(.x2,.frame 128),(.x3,.caller 4 0)])
    (by simp) (by simp [Whole.valid]) (by simp [known]) (by simp [preserved])) ?_
  intro u ⟨hu,hm,hav⟩
  have a0 := hav (.x0,.caller 0 0) (by simp)
  have a1 := hav (.x1,.caller 3 0) (by simp)
  have a2 := hav (.x2,.frame 128) (by simp)
  have a3 := hav (.x3,.caller 4 0) (by simp)
  change u.gpr .x0 = L.pk+0#64 at a0
  change u.gpr .x1 = L.sig+0#64 at a1
  change u.gpr .x3 = L.scr+0#64 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  exact ⟨hu,⟨a0,a1,a2,a3⟩,hm ▸ hh⟩

theorem equation_call_ct (hL : L.Ok) {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ L.pk 32 = Spec.Ed25519.bytesAt m₂ L.pk 32)
    (hsig : Spec.Ed25519.bytesAt m₁ L.sig 64 = Spec.Ed25519.bytesAt m₂ L.sig 64) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => EqArgs L t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge)
      (.call "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct verify_ok verify_ct (Whole.depth_of_noFrames equation_noFrames) (fun _ h => equation_ready hL h.1)
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
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    aa.1, aa.2.1, aa.2.2.1, aa.2.2.2, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2]
  exact ⟨hsp,trivial,trivial,trivial,trivial,pk₁.trans (hpk.trans pk₂.symm),
    sig₁.trans (hsig.trans sig₂.symm),h.2.2.1.2.trans h.2.2.2.2.symm⟩

theorem equation_step_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ L.pk 32 = Spec.Ed25519.bytesAt m₂ L.pk 32)
    (hsig : Spec.Ed25519.bytesAt m₁ L.sig 64 = Spec.Ed25519.bytesAt m₂ L.sig 64) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge)
      (Whole.callWith VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hs : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge)
      (.block VerifyMessage.equationArgs)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => EqArgs L t ∧ Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge) := by
    apply two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide))
    · intro t hc hh
      exact equation_setup_wp hc hL ha hh
    · intro t hc hh
      exact equation_setup_wp hc hL hb hh
  exact hs.seq (equation_call_ct hL hpk hsig)

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Correct`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

theorem verifyMessage_ok (backend : Whole.Backend) {s : State} (h : verifyMessageLocal.pre s) :
    WP isa (code backend.code backend.suffix) s fun u => abiPreserved s u ∧ verifyMessageLocal.post s u := by
  have hw := Whole.wrap_ok (body_depth backend) (entry_below h) (entry_writes h)
    (P := fun m _ r => r = signWord (Spec.Ed25519.verify
      (Spec.Ed25519.bytesAt m (s.gpr .x0) 32)
      (Spec.Ed25519.bytesAt m (s.gpr .x1) (s.gpr .x2).toNat)
      (Spec.Ed25519.bytesAt m (s.gpr .x3) 64)))
    (fun p hp => WP.mono (body_ok backend (entry_ctx h hp) (lay_ok h) (entry_args hp))
      fun u ⟨hu,ho⟩ => ⟨by
        simpa only [Whole.bodyRd,h.1,Ctx,Lay.inputs,Lay.outputs,Lay.PK,Lay.MSG,Lay.SIG,
          Lay.SCR,Lay.ARGS,lay,h.2.1,List.cons_append,List.nil_append] using hu,ho⟩)
  refine WP.mono hw fun u ⟨hu,m,hf,hp⟩ => ⟨hu,?_⟩
  have pk := entry_input h hf (r := ⟨s.gpr .x0,32⟩) (by rw [h.1]; simp) (by change 32≤2^64; decide)
  have msg := entry_input h hf (r := ⟨s.gpr .x1,(s.gpr .x2).toNat⟩) (by rw [h.1]; simp)
    (by change (s.gpr .x2).toNat≤2^64; exact Nat.le_of_lt (s.gpr .x2).isLt)
  have sig := entry_input h hf (r := ⟨s.gpr .x3,64⟩) (by rw [h.1]; simp) (by change 64≤2^64; decide)
  change u.gpr .x0 = signWord _
  rw [hp,pk,msg,sig]

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem body_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hpk : Spec.Ed25519.bytesAt m₁ L.pk 32=Spec.Ed25519.bytesAt m₂ L.pk 32)
    (hmsg : Spec.Ed25519.bytesAt m₁ L.msg L.len.toNat=Spec.Ed25519.bytesAt m₂ L.msg L.len.toNat)
    (hsig : Spec.Ed25519.bytesAt m₁ L.sig 64=Spec.Ed25519.bytesAt m₂ L.sig 64) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hm : hashInput L m₁=hashInput L m₂ := by
    rw [hashInput_eq,hashInput_eq,hpk,hmsg,hsig]
  exact (hash_result_ct backend hL ha hb hm).seq
    ((reduce_ct hL ha hb _).seq ((extend_ct _).seq (equation_step_ct hL ha hb hpk hsig)))

theorem lay_eq {s t : State} (h : verifyMessageLocal.pub s t) : lay s=lay t := by
  obtain ⟨sp,h0,h1,h2,h3,h4,_⟩ := h
  simp only [lay,Whole.base,sp,h0,h1,h2,h3,h4]

theorem saved_inputs_eq {s t p q : State} (hs : verifyMessageLocal.pre s) (ht : verifyMessageLocal.pre t)
    (hp : verifyMessageLocal.pub s t) (hpa : Whole.Saved (Whole.entered s) 6 p)
    (hqb : Whole.Saved (Whole.entered t) 6 q) :
    Spec.Ed25519.bytesAt p.mem (lay s).pk 32 = Spec.Ed25519.bytesAt q.mem (lay s).pk 32 ∧
    Spec.Ed25519.bytesAt p.mem (lay s).msg (lay s).len.toNat =
      Spec.Ed25519.bytesAt q.mem (lay s).msg (lay s).len.toNat ∧
    Spec.Ed25519.bytesAt p.mem (lay s).sig 64 = Spec.Ed25519.bytesAt q.mem (lay s).sig 64 := by
  have fp := Whole.saved_frame hpa
  have fq := Whole.saved_frame hqb
  obtain ⟨_,h0,h1,h2,h3,_,pk,msg,sig⟩ := hp
  have epk := entry_input hs fp (r := ⟨s.gpr .x0,32⟩) (by rw [hs.1]; simp) (by change 32≤2^64; decide)
  have fpk := entry_input ht fq (r := ⟨t.gpr .x0,32⟩) (by rw [ht.1]; simp) (by change 32≤2^64; decide)
  have emsg := entry_input hs fp (r := ⟨s.gpr .x1,(s.gpr .x2).toNat⟩) (by rw [hs.1]; simp)
    (Nat.le_of_lt (s.gpr .x2).isLt)
  have fmsg := entry_input ht fq (r := ⟨t.gpr .x1,(t.gpr .x2).toNat⟩) (by rw [ht.1]; simp)
    (Nat.le_of_lt (t.gpr .x2).isLt)
  have esig := entry_input hs fp (r := ⟨s.gpr .x3,64⟩) (by rw [hs.1]; simp) (by change 64≤2^64; decide)
  have fsig := entry_input ht fq (r := ⟨t.gpr .x3,64⟩) (by rw [ht.1]; simp) (by change 64≤2^64; decide)
  change Spec.Ed25519.bytesAt p.mem (s.gpr .x0) 32=Spec.Ed25519.bytesAt q.mem (s.gpr .x0) 32 ∧
    Spec.Ed25519.bytesAt p.mem (s.gpr .x1) (s.gpr .x2).toNat=Spec.Ed25519.bytesAt q.mem (s.gpr .x1) (s.gpr .x2).toNat ∧
    Spec.Ed25519.bytesAt p.mem (s.gpr .x3) 64=Spec.Ed25519.bytesAt q.mem (s.gpr .x3) 64
  rw [epk,emsg,esig,h0,h1,h2,h3,fpk,fmsg,fsig]
  rw [h0] at pk
  rw [h1,h2] at msg
  rw [h3] at sig
  exact ⟨pk,msg,sig⟩

theorem verifyMessage_ct (backend : Whole.Backend) :
    ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub (code backend.code backend.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok backend (entry_ctx hs hp) (lay_ok hs) (entry_args hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p,q,hpa,hqb,rfl,rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args hqb
    obtain ⟨pk,msg,sig⟩ := saved_inputs_eq hs ht hp hpa hqb
    exact ⟨(body_ct backend (lay_ok hs) (entry_args hpa) hqa pk msg sig _ _ _ _ _ _
      ⟨entry_ctx hs hpa,hq,trivial,trivial⟩ ea eb).1,trivial⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Contract`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64

def verifySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 64 | .x3 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000,32⟩,⟨0x2000,64⟩,⟨0x3000,64⟩]
  wr := [⟨0x4000,8192⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verifyMessage_implies : verifyMessageLocal.Implies (Spec.Ed25519.verifyContract AArch64.abi 352) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, verifyMessageLocal, below,
      AArch64.abi,AArch64.argRegs]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, AArch64.abi,AArch64.argRegs]
    change t.gpr .x0 = signWord _ at h
    rw [h]
    generalize Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x3) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, AArch64.abi,AArch64.argRegs] at h
    obtain ⟨sp, bytes, pk, msg, len, sig, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, len])
    exact ⟨sp, pk, msg, len, sig, base, first, middle, last⟩
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyContract,Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords,verifyMessageLocal,below,AArch64.abi,AArch64.argRegs]
      [verifySatState] using verifySatState

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

theorem verifyMessage_verified (backend : Whole.Backend) :
    Verified AArch64.target (code backend.code backend.suffix) (Spec.Ed25519.verifyContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verifyMessage_ok backend h) (verifyMessage_ct backend)
      (.refl verifyMessage_implies.sat_left)) verifyMessage_implies

end VG.Proof.Ed25519.AArch64.VerifyMessage

end
