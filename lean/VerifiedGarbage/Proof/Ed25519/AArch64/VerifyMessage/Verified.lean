module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
meta import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
meta import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit
meta import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup
public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTBody
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre
public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyVerified
public import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyMessage
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMain
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.AArch64.Codec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarLit
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup
meta import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTBody
meta import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre
meta import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyVerified
meta import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyMessage
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMain
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Codec
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarLit
meta import Mathlib.Tactic.NormNum.Prime
meta import Mathlib.Data.Nat.Totient
meta import Mathlib.Tactic.Positivity.Finset
meta import Mathlib.Algebra.Order.Field.Basic
meta import Mathlib.Tactic.NormNum.GCD
meta import Mathlib.Data.Sym.Sym2.Init
meta import Mathlib.Tactic.ContinuousFunctionalCalculus
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT

/-! ### `Ed25519.AArch64.VerifyMessage.CTReady`, which only this module used -/

section

/-! ### `Ed25519.AArch64.VerifyMessage.Body`, which only this module used -/

section

/-! ### `Ed25519.AArch64.VerifyMessage.Args`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Layout`. -/

@[expose] public section

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
  /-- The static of the cached `-[1]B … -[15]B`, which `vg_ed25519_verify_equation` reads. -/
  T : BitVec 64

namespace Lay
variable (L : Lay)
abbrev PK : Region := ⟨L.pk, 32⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SIG : Region := ⟨L.sig, 64⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev CK : Region := Whole.CK L.E
abbrev TB : Region := ⟨L.T, 1920⟩
def inputs : List Region := [L.PK, L.MSG, L.SIG, L.TB, L.ARGS]
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
  tbfit : L.T.toNat + 1920 ≤ 2 ^ 64
end Lay

/-- An input is outside the frame of a call. -/
theorem Lay.Ok.ck_within {L : Lay} (h : L.Ok) {r : Region} (hi : ∃ R ∈ L.inputs, Whole.Within r R) :
    L.CK.Disjoint r := by
  obtain ⟨R, hR, hw⟩ := hi
  exact (h.ck R hR).sub_right hw.sub

/-- The disjoint scratch allocation leaves room for the hash's 64-byte prefix. -/
theorem Lay.Ok.message_bound {L : Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 64 := by
  have hd := h.sc L.MSG (by simp [Lay.inputs])
  have nm := h.nm
  have nc := h.nc
  by_cases hz : L.len.toNat = 0
  · omega_using [hz]
  by_cases hp : L.msg ≤ L.scr
  · have hn : ¬ L.MSG.Contains L.scr 1 := fun hx => hd _ hx (by simp [Region.Contains])
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp] at hn
    have hp' : L.msg.toNat ≤ L.scr.toNat := hp
    omega_using [nc, hn]
  · have hp' : L.scr ≤ L.msg := by
      change L.scr.toNat ≤ L.msg.toNat
      change ¬ L.msg.toNat ≤ L.scr.toNat at hp
      omega_using [hp]
    have hn : ¬ L.SCR.Contains L.msg 1 := fun hx => hd _ (by simp [Region.Contains]; omega_using [hz]) hx
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp'] at hn
    have hp'' : L.scr.toNat ≤ L.msg.toNat := hp'
    omega_using [nm, hn]


abbrev Ctx (L : Lay) (g : Reg → BitVec 64) (v : VReg → BitVec 128) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g v m₀ L.inputs L.outputs t

namespace Ctx
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem input_bytes (hc : Ctx L g v m₀ t) (hL : L.Ok)
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

theorem arg_word (hc : Ctx L g v m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 6) :
    t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      m₀.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 256) (k := 48) (by omega_using []) (by omega_using [hj]) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl | rfl
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm
    · exact (hL.ck _ ha).symm

/-- The static's words, as on entry: no write reaches them. -/
theorem tbl (hc : Ctx L g v m₀ t) (hL : L.Ok) (hm : BWords L.T m₀) : BWords L.T t.mem :=
  fun i hi => by
    have := hL.tbfit
    have ht : L.TB ∈ L.inputs := by simp [Lay.inputs]
    rw [← hm i hi]
    refine hc.frame.readW (r := L.TB) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) ?_ (by decide)
    intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact hL.sc _ ht
    · exact (hL.ks _ ht).symm
    · exact (hL.ck _ ht).symm

end Ctx
end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

/-- The saved arguments, and the static's words. -/
def Arguments (L : Lay) (m : Mem) : Prop :=
  (∀ j < 5, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j) ∧ BWords L.T m

def known : Value → Prop
  | .caller j _ => j < 5
  | _ => True

instance : DecidablePred known
  | .caller j _ => inferInstanceAs (Decidable (j < 5))
  | .const _ => inferInstanceAs (Decidable True)
  | .frame _ => inferInstanceAs (Decidable True)

def value (L : Lay) : Value → BitVec 64
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

def OutArgs (L : Lay) (args : List (Reg × Value)) (s : State) : Prop :=
  ∀ p ∈ args, s.gpr p.1 = value L p.2

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem Ctx.value (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {a : Value} (hv : known a) : Whole.value L.E s.mem a = value L a := by
  cases a with
  | const => rfl
  | frame => rfl
  | caller j d =>
    change j < 5 at hv
    change s.mem.readW (L.E + BitVec.ofNat 64 (256 + 8*j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL (by omega_using [hv]), ha.1 j hv]
    rfl

theorem args_ok (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hk : ∀ p ∈ args, known p.2)
    (hregs : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) s fun t => Ctx L g v m₀ t ∧
      t.mem = s.mem ∧ OutArgs L args t := by
  refine WP.mono (Whole.Ctx.setup hc hn hv (by simp [Lay.inputs, Lay.ARGS, Whole.ARGS]) hregs)
    fun t ⟨ht, hm, hvals⟩ => ⟨ht, hm, ?_⟩
  intro p hp
  exact (hvals p hp).trans (hc.value hL ha (hk p hp))

end VG.Proof.Ed25519.AArch64.VerifyMessage

end

end


/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Hash`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem hash_writes : ∀ r ∈ Whole.hashWr L.scr,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  Whole.hash_writes (by simp [Lay.outputs])

theorem init_ok (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa init s fun t => Ctx L g v m₀ t ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr [] := by
  unfold init VG.Impl.Ed25519.AArch64.Whole.callWith initArgs
  apply WP.seq
  refine WP.mono (args_ok hc hL ha (args := [(.x0,.caller 4 0)]) (by decide) (by decide) (by decide) (by decide)) ?_
  intro t ⟨ht, _, hv⟩
  have a0 : t.gpr .x0 = L.scr := by
    have hh := hv (.x0,.caller 4 0) (by simp)
    change t.gpr .x0 = L.scr + 0 at hh
    exact hh.trans (BitVec.add_zero _)
  have hw := Whole.init_writes (E := L.E) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call ht (Whole.init_pre a0)
    (Whole.covers_writes hw) hw a0) fun u ⟨hu, _, hr⟩ => ⟨hu, hr⟩

/-- Append a known input buffer without depending on its contents. -/
theorem update_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {args : List (Reg × Value)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hk : ∀ p ∈ args, known p.2) (hregs : ∀ p ∈ args, p.1 ∉ preserved)
    {p len : Addr} {prev : List Byte}
    (hargs : ∀ t, OutArgs L args t → t.gpr .x0 = L.scr ∧
      t.gpr .x1 = BitVec.ofNat 64 prev.length ∧ t.gpr .x2 = p ∧
      t.gpr .x3 = len ∧ t.gpr .x4 = L.scr + 192)
    (hd : Region.Disjoint ⟨p,len.toNat⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨p,len.toNat⟩ R)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix (setup args)) s fun t =>
      Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem p len.toNat) := by
  unfold update VG.Impl.Ed25519.AArch64.Whole.callWith
  apply WP.seq
  refine WP.mono (args_ok hc hL ha hn hv hk hregs) ?_
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
    · rcases hash_writes R hR with hf | ⟨S,hS,hs⟩
      · exact ⟨Whole.FR L.E,List.mem_append_right _ List.mem_cons_self,hf⟩
      · exact ⟨S,List.mem_append_right _ (List.mem_cons_of_mem _ hS),hs⟩
  have hr' : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev := hm ▸ hr
  refine WP.mono (Whole.update_call backend ht (Whole.update_pre a0 a2 a3 a4 hd (by rw [ht.sp]; exact hL.e16)
    (by rw [ht.sp]; exact hL.cc) (by rw [ht.sp]; exact hL.ck_within hi))
    hcov hash_writes a0 a2 a3 a1 hr') fun u ⟨hu,_,huv⟩ => ⟨hu,?_⟩
  rw [hm] at huv
  exact huv

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Calls`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : Lay}

def field (L : Lay) (d : Nat) : Region := ⟨L.E + BitVec.ofNat 64 d, 32⟩
def digest (L : Lay) : Region := ⟨L.E + BitVec.ofNat 64 192, 64⟩

theorem fieldWithin (L : Lay) {d : Nat} (hd : d + 32 ≤ 256) : Whole.Within (field L d) L.FR :=
  ⟨d, rfl, hd⟩
theorem digestWithin (L : Lay) : Whole.Within (digest L) L.FR := ⟨192, rfl, by change 192 + 64 ≤ 256; decide⟩
theorem scratchWithin (L : Lay) : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩

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

theorem scratch_covered (L : Lay) : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within L.SCR R :=
  ⟨L.SCR, by simp [Lay.outputs], scratchWithin L⟩

theorem writes {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ Whole.Within r L.SCR) :
    ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rcases h r hr with hf | hs
  · exact .inl hf
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], hs⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Equation`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

def challenge (L : Lay) : Region := ⟨L.E+128,64⟩
def equationRd (L : Lay) : List Region := [L.PK,L.SIG,challenge L,L.TB]
def equationWr (L : Lay) : List Region := [L.SCR]
def EqArgs (L : Lay) (s : State) : Prop := s.gpr .x0 = L.pk ∧
  s.gpr .x1 = L.sig ∧ s.gpr .x2 = L.E+128 ∧ s.gpr .x3 = L.scr

theorem equation_noFrames : verifyEquation.noFrames = true := by lit_decide

theorem challengeWithin (L : Lay) : Whole.Within (challenge L) L.FR :=
  ⟨128,rfl,by change 128+64≤256; decide⟩

theorem equation_pre (hL : L.Ok) (ha : EqArgs L s) (hsy : s.syms bSym = L.T)
    (hm : BWords L.T s.mem) :
    verifyLocal.pre (s.callEntry.withRegions (equationRd L) (equationWr L)) := by
  have hT : (s.callEntry.withRegions (equationRd L) (equationWr L)).syms bSym = L.T := hsy
  have hB : BHeld (s.callEntry.withRegions (equationRd L) (equationWr L)) [L.SCR] := by
    refine ⟨fun i hi => ?_, ?_, fun r hr => ?_⟩
    · rw [hT]; exact hm i hi
    · rw [hT]; exact hL.tbfit
    · rw [hT, List.mem_singleton.mp hr]; exact hL.sc _ (by simp [Lay.inputs])
  simp only [verifyLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), ha.1,ha.2.1,ha.2.2.1,ha.2.2.2, hT]
  exact ⟨rfl,rfl,hL.sc _ (by simp [Lay.inputs]),hL.sc _ (by simp [Lay.inputs]),
    hL.kc.sub_left (challengeWithin L).sub,hL.nc,hB⟩

theorem equation_covers : Covers (equationRd L ++ equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  simp only [equationRd,equationWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl)
  · exact .inr ⟨L.PK,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inr ⟨L.SIG,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inl (challengeWithin L)
  · exact .inr ⟨L.TB,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inr (scratch_covered L)

theorem equation_writes : ∀ r ∈ equationWr L,
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨L.SCR,by simp [Lay.outputs],scratchWithin L⟩

theorem equation_call (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : EqArgs L s) (hsy : s.syms bSym = L.T)
    (hm : BWords L.T s.mem) :
    WP isa (.call "vg_ed25519_verify_equation" verifyEquation) s fun t => Ctx L g v m₀ t ∧
      t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem L.pk 32) (Spec.Ed25519.bytesAt s.mem L.sig 64)
        (Spec.Ed25519.bytesAt s.mem (L.E+128) 64)) := by
  refine Whole.call_ok hc verify_ok equation_noFrames (equation_pre hL ha hsy hm)
    equation_covers equation_writes fun t ht _ hp => ⟨ht,?_⟩
  change t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x0) 32)
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x1) 64)
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x2) 64)) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),ha.1,ha.2.1,ha.2.2.1] at hp
  exact hp

theorem equation_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hsy : s.syms bSym = L.T) :
    WP isa (VG.Impl.Ed25519.AArch64.Whole.callWith VG.Impl.Ed25519.AArch64.VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation) s
      fun t => Ctx L g v m₀ t ∧ t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem L.pk 32) (Spec.Ed25519.bytesAt s.mem L.sig 64)
        (Spec.Ed25519.bytesAt s.mem (L.E+128) 64)) := by
  refine WP.seq (WP.mono_syms (args_ok hc hL ha
    (args := [(.x0,.caller 0 0),(.x1,.caller 3 0),(.x2,.frame 128),(.x3,.caller 4 0)])
    (by simp) (by decide) (by decide) (by decide))
    fun u ⟨hu,hm,hav⟩ su => ?_)
  have a0 := hav (.x0,.caller 0 0) (by simp)
  have a1 := hav (.x1,.caller 3 0) (by simp)
  have a2 := hav (.x2,.frame 128) (by simp)
  have a3 := hav (.x3,.caller 4 0) (by simp)
  change u.gpr .x0 = L.pk+0#64 at a0
  change u.gpr .x1 = L.sig+0#64 at a1
  change u.gpr .x3 = L.scr+0#64 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  refine WP.mono (equation_call hu hL ⟨a0,a1,a2,a3⟩ (by rw [su]; exact hsy) (hu.tbl hL ha.2))
    fun t ⟨ht,hp⟩ => ⟨ht,?_⟩
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
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem prefix_step (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {source count : Nat} (hsource : source < 5)
    (hcount : count < 65536) {prev : List Byte} (hp : prev.length = count)
    (hd : Region.Disjoint ⟨L.value source,32⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨L.value source,32⟩ R)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix (prefixArgs source count)) s fun t =>
      Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem (L.value source) 32) := by
  apply update_ok backend hc hL ha (by simp)
    (by simp [Whole.valid]; omega_using [hsource, hcount]) (by simp [known]; exact hsource) (by simp [preserved])
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

theorem message_step (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {prev : List Byte} (hp : prev.length = 64)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix messageArgs) s fun t =>
      Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem L.msg L.len.toNat) := by
  apply update_ok backend hc hL ha (by simp) (by decide)
    (by decide) (by decide) (p := L.msg) (len := L.len) (prev := prev) ?_
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

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem finalize_writes : ∀ r ∈ Whole.finalizeWr L.scr (L.E+192),
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0+192≤8192; decide⟩
  · exact .inl ⟨192, rfl, by change 192+64≤256; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192+688≤8192; decide⟩

theorem finalize_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {msg : List Byte}
    (hm : msg.length = 64 + L.len.toNat)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr msg) :
    WP isa (finalize backend.code backend.suffix) s fun t => Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E+192) 64 = Spec.Sha512.finalHash Spec.Sha512.H0_512 msg := by
  unfold finalize VG.Impl.Ed25519.AArch64.Whole.callWith finalizeArgs
  apply WP.seq
  refine WP.mono (args_ok hc hL ha
    (args := [(.x0,.caller 4 0),(.x1,.caller 2 64),(.x2,.frame 192),(.x3,.caller 4 192)])
    (by decide) (by decide) (by decide) (by decide)) ?_
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
    (Whole.covers_writes finalize_writes) finalize_writes a0 a2 a1 hr'
    (by rw [hm]; exact hL.message_bound)) fun u ⟨hu,_,hp⟩ => ⟨hu,hp⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

def hashInput (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m L.sig 32 ++
    Spec.Ed25519.bytesAt m L.pk 32 ++
    Spec.Ed25519.bytesAt m L.msg L.len.toNat

theorem bytes_length (m : Mem) (p : BitVec 64) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

theorem sig_prefix_same (hc : Ctx L g v m₀ s) (hL : L.Ok) :
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
    (by change 64 ≤ 2 ^ 64; decide) (by change i < 64; have := List.mem_range.mp hi; omega_using [this])

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

theorem hash_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s)
    (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (hash backend.code backend.suffix) s fun t => Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = Spec.Sha512.sha512 (hashInput L m₀) := by
  refine WP.seq (WP.mono (init_ok hc hL ha) fun t ⟨ht,hinit⟩ => ?_)
  refine WP.seq (WP.mono (prefix_step backend ht hL ha (source := 3) (count := 0)
    (by decide) (by decide) rfl (input_sig hL).1 (input_sig hL).2 hinit)
    fun u ⟨hu,hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem L.sig 32) at hsig
  rw [List.nil_append, sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (prefix_step backend hu hL ha (source := 0) (count := 32)
    (by decide) (by decide) (bytes_length _ _ _) (input_pk hL).1 (input_pk hL).2 hsig)
    fun w ⟨hw,hpk⟩ => ?_)
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem L.pk 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide)] at hpk
  have hpkl : (Spec.Ed25519.bytesAt m₀ L.sig 32 ++ Spec.Ed25519.bytesAt m₀ L.pk 32).length = 64 := by
    rw [List.length_append, bytes_length, bytes_length]
  refine WP.seq (WP.mono (message_step backend hw hL ha hpkl hpk) fun z ⟨hz,hmsg⟩ => ?_)
  rw [hw.input_bytes hL (r := L.MSG) (by simp [Lay.inputs])
    (by have := L.len.isLt; change L.len.toNat≤2^64; omega_using [])] at hmsg
  have hlen : (hashInput L m₀).length = 64 + L.len.toNat := by
    simp only [hashInput, List.length_append, bytes_length]
  exact finalize_ok backend hz hL ha hlen hmsg

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Challenge`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Reduce`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
open VG.Impl.Ed25519.AArch64 (scalarReduce)

def reduceRd (L : Lay) : List Region := [digest L]
def reduceWr (L : Lay) (d : Nat) : List Region := [field L d, L.SCR]
def ReduceArgs (L : Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .x0 = L.E + BitVec.ofNat 64 d ∧ s.gpr .x1 = L.E + 192 ∧ s.gpr .x2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (ha : ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (reduceRd L) (reduceWr L d)) := by
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2]
  exact ⟨rfl, rfl, hL.kc.sub_left (digestWithin L).sub⟩

theorem reduce_call (hc : Ctx L g v m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256)
    (ha : ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => Ctx L g v m₀ t ∧
      Frame (reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L hd)
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L hd)
    · exact .inr (scratchWithin L)
  refine Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarReduceLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] using hp

theorem reduce_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.AArch64.Whole.callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce) s
      fun t => Ctx L g v m₀ t ∧ Frame (reduceWr L 128) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 128) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.x0, .frame 128), (.x1, .frame 192), (.x2, .caller 4 0)])
    (by simp) (by decide) (by decide) (by decide))
    fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .frame 128) (by simp)
  have a1 := hs (.x1, .frame 192) (by simp)
  have a2 := hs (.x2, .caller 4 0) (by simp)
  change u.gpr .x2 = L.scr + 0#64 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (reduce_call hu hL (d := 128) (by decide) ⟨a0,a1,a2⟩)
    fun t ⟨ht,hf,hp⟩ => ⟨ht,?_,?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, Proof.Ed25519.AArch64.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem extend_step (hc : Ctx L g v m₀ s) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (L.E + 128) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => Ctx L g v m₀ t ∧
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
        rw [show 8*(20+j)=160+8*j by omega_using [], BitVec.ofNat_add, BitVec.add_assoc]
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
    low, hd, high, reduced_challenge]

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : Lay) (m : Mem) : hashInput L m =
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

theorem body_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) (hsy : s.syms Impl.Ed25519.AArch64.bSym = L.T) :
    WP isa (body backend.code backend.suffix) s fun t => Ctx L g v m₀ t ∧
      t.gpr .x0 = signWord (Spec.Ed25519.verify (Spec.Ed25519.bytesAt m₀ L.pk 32)
        (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) (Spec.Ed25519.bytesAt m₀ L.sig 64)) := by
  refine WP.seq (WP.mono_syms (hash_ok backend hc hL ha) fun t ⟨ht,hh⟩ st => ?_)
  refine WP.seq (WP.mono_syms (reduce_step ht hL ha) fun u ⟨hu,_,hr⟩ su => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono_syms (extend_step hu hr) fun w ⟨hw,he⟩ sw => ?_)
  rw [hashInput_eq] at he
  refine WP.mono (equation_step hw hL ha (by rw [sw, su, st]; exact hsy)) fun z ⟨hz,eq⟩ => ⟨hz,?_⟩
  rw [hw.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide),
    hw.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64≤2^64; decide),he] at eq
  exact eq

theorem body_depth (backend : Whole.Backend) : (body backend.code backend.suffix).aarch64Depth ≤ 1 := by
  have hu := Whole.update_depth backend
  have hf := Whole.finalize_depth backend
  change (Impl.Sha512.AArch64.Stream.updateWith backend.suffix backend.code).aarch64Depth ≤ 1 at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith backend.suffix backend.code).aarch64Depth ≤ 1 at hf
  have hr := Whole.depth_zero_of_noFrames reduce_noFrames
  have he := Whole.depth_zero_of_noFrames equation_noFrames
  simp only [body,Impl.Ed25519.AArch64.VerifyMessage.hash,init,update,finalize,Impl.Ed25519.AArch64.Whole.callWith,
    Code.aarch64Depth, Nat.max_le,Impl.Sha512.AArch64.Stream.init,hr,he]
  omega_using [hu, hf]

end VG.Proof.Ed25519.AArch64.VerifyMessage

end

end


/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTCommon`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

/-- Both runs in their contexts, satisfying `P`, with the static where the layout says. -/
def Two (L : Lay) (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128)
    (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  Ctx L g₁ v₁ m₁ a ∧ Ctx L g₂ v₂ m₂ b ∧ P a ∧ P b ∧
    a.syms Impl.Ed25519.AArch64.bSym = L.T ∧ b.syms Impl.Ed25519.AArch64.bSym = L.T

theorem two_sp {P : State → Prop} {a b : State} (h : Two L g₁ g₂ v₁ v₂ m₁ m₂ P a b) :
    a.sp = b.sp := h.1.sp.trans h.2.1.sp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ v₁ m₁ t → P t → t.syms Impl.Ed25519.AArch64.bSym = L.T →
      WP isa c t fun u => Ctx L g₁ v₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ v₂ m₂ t → P t → t.syms Impl.Ed25519.AArch64.bSym = L.T →
      WP isa c t fun u => Ctx L g₂ v₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c (Two L g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have wa : ∀ a, Ctx L g₁ v₁ m₁ a → P a → a.syms Impl.Ed25519.AArch64.bSym = L.T →
      WP isa c a fun u => (Ctx L g₁ v₁ m₁ u ∧ Q u) ∧ u.syms Impl.Ed25519.AArch64.bSym = L.T :=
    fun a hc hp hy => WP.mono_syms (ha a hc hp hy) fun _ hu su => ⟨hu, by rw [su]; exact hy⟩
  have wb : ∀ b, Ctx L g₂ v₂ m₂ b → P b → b.syms Impl.Ed25519.AArch64.bSym = L.T →
      WP isa c b fun u => (Ctx L g₂ v₂ m₂ u ∧ Q u) ∧ u.syms Impl.Ed25519.AArch64.bSym = L.T :=
    fun b hc hp hy => WP.mono_syms (hb b hc hp hy) fun _ hu su => ⟨hu, by rw [su]; exact hy⟩
  exact (hct.wp fun a b h => ⟨wa a h.1 h.2.2.1 h.2.2.2.2.1, wb b h.2.1 h.2.2.2.1 h.2.2.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1.1, h.2.2.1.1, h.2.1.1.2, h.2.2.1.2, h.2.1.2, h.2.2.2⟩

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hk : ∀ p ∈ args, known p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) ht) ?_ ?_
  · intro s hc _ _
    exact WP.mono (args_ok hc hL ha hn hv hk hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _ _
    exact WP.mono (args_ok hc hL hb hn hv hk hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem args_eq {args : List (Reg × Value)} {a b : State}
    (h : Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args) a b) {p : Reg × Value} (hp : p ∈ args) :
    a.gpr p.1 = b.gpr p.1 := (h.2.2.1 p hp).trans (h.2.2.2.1 p hp).symm

theorem call_gpr_eq {args : List (Reg × Value)} {a b : State}
    (h : Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args) a b) {p : Reg × Value}
    (hp : p ∈ args) (hl : p.1 ∉ linkRegs) : a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := by
  rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl]
  exact args_eq h hp

theorem call_ct {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ {g v m t}, Ctx L g v m t → P t → t.syms Impl.Ed25519.AArch64.bSym = L.T →
      BWords L.T t.mem → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, Two L g₁ g₂ v₁ v₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) (.call name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply two_wp
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.1 h.2.2.2.2.1 (h.1.tbl hL ha.2)
    let rb := ready h.2.1 h.2.2.2.1 h.2.2.2.2.2 (h.2.1.tbl hL hb.2)
    obtain ⟨ca, wa⟩ := Whole.CallReady.covers_state h.1 ra
    obtain ⟨cb, wb⟩ := Whole.CallReady.covers_state h.2.1 rb
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb⟩
  · intro t hc hs hy
    exact WP.mono (Whole.CallReady.wpF hc (ready hc hs hy (hc.tbl hL ha.2)) correct hd)
      fun _ hu => ⟨hu, trivial⟩
  · intro t hc hs hy
    exact WP.mono (Whole.CallReady.wpF hc (ready hc hs hy (hc.tbl hL hb.2)) correct hd)
      fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64
variable {L : Lay} {t : State}

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
    (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hL.ck_within hi),?_,hash_writes⟩
  apply covers
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    obtain ⟨R,hR,hs⟩ := hi
    exact .inr ⟨R,List.mem_append_left _ hR,hs⟩
  · rcases hash_writes r hr with hf | ⟨R,hR,hs⟩
    · exact .inl hf
    · exact .inr ⟨R,List.mem_append_right _ hR,hs⟩

def finalize_ready (hL : L.Ok) (hsp : t.sp = L.E) (h0 : t.gpr .x0=L.scr)
    (h2 : t.gpr .x2=L.E+192) (h3 : t.gpr .x3=L.scr+192) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs t :=
  ⟨[],Whole.finalizeWr L.scr (L.E+192),Whole.finalize_pre h0 h2 h3
    (hL.kc.sub_left (Offset.sub_base _ (by decide))) (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
    (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes finalize_writes,finalize_writes⟩

def reduce_ready (hL : L.Ok) (ha : ReduceArgs L 128 t) :
    Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs t := by
  refine ⟨reduceRd L,reduceWr L 128,reduce_pre hL ha,?_,?_⟩
  · apply covers
    simp only [reduceRd,reduceWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (scratch_covered L)
  · apply writes
    simp only [reduceWr,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (scratchWithin L)

def equation_ready (hL : L.Ok) (ha : EqArgs L t) (hsy : t.syms Impl.Ed25519.AArch64.bSym = L.T)
    (hm : BWords L.T t.mem) : Whole.CallReady verifyLocal L.E L.inputs L.outputs t :=
  ⟨equationRd L,equationWr L,equation_pre hL ha hsy hm,equation_covers,equation_writes⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage

end

end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTHashPipeline`. -/

@[expose] public section

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

theorem init_call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L initValues))
    (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 (Whole.depth_of_noFrames rfl)
  · intro g v m t _ hs _ _
    have a0 := hs (.x0,.caller 4 0) (by decide)
    change t.gpr .x0 = L.scr+0#64 at a0
    exact init_ready (a0.trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    simp only [Proof.Sha512.initAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨call_gpr_eq h (p := (.x0,.caller 4 0)) (by decide) (by decide),two_sp h⟩

theorem update_call_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁)
    (hb : Arguments L m₂) {args : List (Reg × Value)}
    (ready : ∀ {t}, t.sp = L.E → OutArgs L args t →
      Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t)
    (hregs : ∀ r ∈ ([.x0,.x1,.x2,.x3,.x4] : List Reg), ∃ a, (r,a)∈args) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args))
      (.call ("vg_sha512_update_scratch" ++ backend.suffix) backend.update)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb backend.update_verified.1 backend.update_verified.2.1
    (Whole.update_depth backend) (fun hc h _ _ => ready hc.sp h)
  intro a b ar aw br bw h
  have eq (r : Reg) (hr : r ∈ ([.x0,.x1,.x2,.x3,.x4] : List Reg)) : a.callEntry.gpr r=b.callEntry.gpr r := by
    obtain ⟨val,hval⟩ := hregs r hr
    exact call_gpr_eq h hval ((by decide : ∀ r ∈ ([.x0,.x1,.x2,.x3,.x4] : List Reg),r∉linkRegs) r hr)
  simp only [Proof.Sha512.updateAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
  exact ⟨eq .x0 (by simp),eq .x1 (by simp),eq .x2 (by simp),eq .x3 (by simp),eq .x4 (by simp),two_sp h⟩

theorem finalize_call_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁)
    (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L finalizeValues))
      (.call ("vg_sha512_finalize_scratch" ++ backend.suffix) backend.finalize)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb backend.finalize_verified.1 backend.finalize_verified.2.1
    (Whole.finalize_depth backend)
  · intro g v m t hc hs _ _
    have a0 := hs (.x0,.caller 4 0) (by decide)
    have a2 := hs (.x2,.frame 192) (by decide)
    have a3 := hs (.x3,.caller 4 192) (by decide)
    change t.gpr .x0=L.scr+0#64 at a0
    exact finalize_ready hL hc.sp (a0.trans (BitVec.add_zero _)) a2 a3
  · intro a b ar aw br bw h
    simp only [Proof.Sha512.finalizeAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨call_gpr_eq h (p := (.x0,.caller 4 0)) (by decide) (by decide),
      call_gpr_eq h (p := (.x1,.caller 2 64)) (by decide) (by decide),
      call_gpr_eq h (p := (.x2,.frame 192)) (by decide) (by decide),
      call_gpr_eq h (p := (.x3,.caller 4 192)) (by decide) (by decide),two_sp h⟩

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
  have a0 := hs (.x0,.caller 4 0) (by decide)
  have a2 := hs (.x2,.caller 1 0) (by decide)
  have a3 := hs (.x3,.caller 2 0) (by decide)
  have a4 := hs (.x4,.caller 4 192) (by decide)
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
    (by decide) (by decide)
    (by decide)
    (by simp only [initValues, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]; decide) (by taint_decide)
  have r := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb (prefixValues 3 0)
    (by decide) (by decide)
    (by decide)
    (by simp only [prefixValues, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]; decide) (by taint_decide)
  have a := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb (prefixValues 0 32)
    (by decide) (by decide)
    (by decide)
    (by simp only [prefixValues, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]; decide) (by taint_decide)
  have m := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb messageValues
    (by decide) (by decide)
    (by decide)
    (by simp only [messageValues, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]; decide) (by taint_decide)
  have f := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb finalizeValues
    (by decide) (by decide)
    (by decide)
    (by simp only [finalizeValues, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]; decide) (by taint_decide)
  have rc := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend hL ha hb (args := prefixValues 3 0) (prefix_ready hL (input_sig hL).1 (input_sig hL).2)
    (by simp [prefixValues])
  have ac := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend hL ha hb (args := prefixValues 0 32) (prefix_ready hL (input_pk hL).1 (input_pk hL).2)
    (by simp [prefixValues])
  have mc := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend hL ha hb (args := messageValues) (message_ready hL) (by simp [messageValues])
  exact (i.seq (init_call_ct hL ha hb)).seq ((r.seq rc).seq ((a.seq ac).seq ((m.seq mc).seq
    (f.seq (finalize_call_ct backend hL ha hb)))))

/-- Public inputs give a common digest for the equation check that follows. -/
theorem hash_result_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hm : hashInput L m₁ = hashInput L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hash backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+192) 64 =
        Spec.Sha512.sha512 (hashInput L m₁)) := by
  refine two_wp ((hash_ct backend hL ha hb).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc _ _
    exact hash_ok backend hc hL ha
  · intro s hc _ _
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
    s.rd = [pk,msg,sig,⟨s.syms Impl.Ed25519.AArch64.bSym,1920⟩] ∧ s.wr = [scr] ∧
    pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧
    stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
    (s.gpr .x0).toNat+32≤2^64 ∧ (s.gpr .x1).toNat+(s.gpr .x2).toNat≤2^64 ∧
    (s.gpr .x3).toNat+64≤2^64 ∧ (s.gpr .x4).toNat+8192≤2^64 ∧ 352≤s.sp.toNat ∧
    BHeld s [scr,stk]
  post s t := t.gpr .x0 = if Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .x3) 64) then 1 else 0
  pub s t := s.sp=t.sp ∧ s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧
    s.gpr .x2=t.gpr .x2 ∧ s.gpr .x3=t.gpr .x3 ∧ s.gpr .x4=t.gpr .x4 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32 = Spec.Ed25519.bytesAt t.mem (t.gpr .x0) 32 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Ed25519.bytesAt t.mem (t.gpr .x1) (t.gpr .x2).toNat ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x3) 64 = Spec.Ed25519.bytesAt t.mem (t.gpr .x3) 64 ∧
    s.syms Impl.Ed25519.AArch64.bSym = t.syms Impl.Ed25519.AArch64.bSym

def lay (s : State) : Lay :=
  ⟨s.gpr .x0,s.gpr .x1,s.gpr .x2,s.gpr .x3,s.gpr .x4,Whole.base s,s.syms Impl.Ed25519.AArch64.bSym⟩

theorem entry_below {s : State} (h : verifyMessageLocal.pre s) : 352≤s.sp.toNat := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hb,_⟩ := h
  exact hb

theorem entry_writes {s : State} (h : verifyMessageLocal.pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  obtain ⟨_,hw,_,_,_,_,_,_,hc,_⟩ := h
  intro r hr
  rw [hw,List.mem_singleton] at hr
  subst r
  exact hc

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨_,_,pc,mc,sc,kp,km,ks,kc,np,nm,ns,nc,hb,-,fit,dj⟩ := h
  have dt := dj ⟨s.gpr .x4,8192⟩ (by simp)
  have dk := dj (below s.sp 352) (by simp)
  have stk := Whole.stk_sub s
  have fr : Region.Sub (Whole.FR (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Region.sub_prefix (by decide) : Region.Sub (Whole.FR (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Offset.sub_base _ (by decide) : Region.Sub (Whole.ARGS (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ck := Whole.ck_sub s
  refine ⟨?_,?_,?_,kc.sub_left fr,np,nm,ns,nc,Whole.base_16 hb,?_,kc.sub_left ck,fit⟩
  · change (s.sp-336#64).toNat+304≤2^64
    rw [BitVec.toNat_sub_of_le (by change 336≤s.sp.toNat; omega_using [hb])]
    have hs := s.sp.isLt
    change s.sp.toNat-336+304≤2^64
    omega_using []
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact pc
    · exact mc
    · exact sc
    · exact dt
    · exact kc.sub_left ar
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact ks.sub_left fr
    · exact (dk.sub_right fr).symm
    · exact Offset.base_disjoint _ (by decide) (by decide)
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact kp.sub_left ck
    · exact km.sub_left ck
    · exact ks.sub_left ck
    · exact (dk.sub_right ck).symm
    · exact Whole.ck_frame (by decide : 256 + 48 ≤ 304)

theorem entry_ctx {s p : State} (h : verifyMessageLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr s.v p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd,h.1,Whole.bodyWr,h.2.1,Ctx,Lay.inputs,Lay.outputs,
    Lay.PK,Lay.MSG,Lay.SIG,Lay.TB,Lay.SCR,Lay.ARGS,lay,List.cons_append,List.nil_append] using hc

theorem entry_args {s p : State} (h : verifyMessageLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Arguments (lay s) p.mem := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have hw := Whole.saved_words hp (j := j) (by omega_using [hj])
    have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega_using [hj]
    rcases he with rfl | rfl | rfl | rfl | rfl <;> exact hw
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,held,fit,dj⟩ := h
    have hf := Whole.saved_frame hp
    rw [← held i hi]
    refine hf.readW (r := ⟨s.syms Impl.Ed25519.AArch64.bSym,1920⟩)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton.mp hr]
    exact (dj (below s.sp 352) (by simp)).sub_right (below_sub (by decide) (by decide))

theorem entry_syms {s p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)).syms Impl.Ed25519.AArch64.bSym = (lay s).T :=
  congrFun hp.step.syms Impl.Ed25519.AArch64.bSym

theorem entry_input {s : State} (h : verifyMessageLocal.pre s) {m : Mem}
    (hf : Frame [below s.sp 336] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len≤2^64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  obtain ⟨hrd,_,_,_,_,kp,km,ks,_,_,_,_,_,_,_,_,dj⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  have hb : Region.Sub (below s.sp 336) (below s.sp 352) := below_sub (by decide) (by decide)
  rcases hr with rfl | rfl | rfl | rfl
  · exact (kp.sub_left hb).symm
  · exact (km.sub_left hb).symm
  · exact (ks.sub_left hb).symm
  · exact (dj (below s.sp 352) (by simp)).sub_right hb

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

theorem reduce_call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L reduceValues))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb scalarReduce_ok scalarReduce_ct (Whole.depth_of_noFrames reduce_noFrames)
  · intro g v m t _ hs _ _
    have a0 := hs (.x0,.frame 128) (by decide)
    have a1 := hs (.x1,.frame 192) (by decide)
    have a2 := hs (.x2,.caller 4 0) (by decide)
    change t.gpr .x2=L.scr+0#64 at a2
    exact reduce_ready hL ⟨a0,a1,a2.trans (BitVec.add_zero _)⟩
  · intro a b ar aw br bw h
    simp only [scalarReduceLocal,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨two_sp h,call_gpr_eq h (p := (.x0,.frame 128)) (by decide) (by decide),
      call_gpr_eq h (p := (.x1,.frame 192)) (by decide) (by decide),
      call_gpr_eq h (p := (.x2,.caller 4 0)) (by decide) (by decide)⟩

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+192) 64=digest)
      (callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 32=Spec.Ed25519.scalarReduce digest) := by
  have hs := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb reduceValues
    (by decide) (by decide)
    (by decide)
    (by simp only [reduceValues, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]; decide) (by taint_decide)
  refine two_wp ((hs.seq (reduce_call_ct hL ha hb)).mono
    (fun _ _ h => ⟨h.1,h.2.1,trivial,trivial,h.2.2.2.2⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc hd _
    exact WP.mono (reduce_step hc hL ha) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩
  · intro s hc hd _
    exact WP.mono (reduce_step hc hL hb) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩

theorem extend_ct (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 32=Spec.Ed25519.scalarReduce digest)
      (.block extendChallenge)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 64=
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro s hc hd _
    exact extend_step hc hd
  · intro s hc hd _
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
    (by simp) (by decide) (by decide) (by decide)) ?_
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

theorem equation_call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ L.pk 32 = Spec.Ed25519.bytesAt m₂ L.pk 32)
    (hsig : Spec.Ed25519.bytesAt m₁ L.sig 64 = Spec.Ed25519.bytesAt m₂ L.sig 64) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => EqArgs L t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge)
      (.call "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb verify_ok verify_ct (Whole.depth_of_noFrames equation_noFrames)
    (fun _ h hy hm => equation_ready hL h.1 hy hm)
  intro a b ar aw br bw h
  have hsp := two_sp h
  have aa := h.2.2.1.1
  have ab := h.2.2.2.1.1
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
    sig₁.trans (hsig.trans sig₂.symm),h.2.2.1.2.trans h.2.2.2.1.2.symm,
    h.2.2.2.2.1.trans h.2.2.2.2.2.symm⟩

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
    · intro t hc hh _
      exact equation_setup_wp hc hL ha hh
    · intro t hc hh _
      exact equation_setup_wp hc hL hb hh
  exact hs.seq (equation_call_ct hL ha hb hpk hsig)

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
    (hP := fun _ _ _ _ _ hq => hq)
    (fun p hp => WP.mono (body_ok backend (entry_ctx h hp) (lay_ok h) (entry_args h hp)
      (entry_syms hp))
      fun u ⟨hu,ho⟩ => ⟨by
        simpa only [Whole.bodyRd,h.1,Ctx,Lay.inputs,Lay.outputs,Lay.PK,Lay.MSG,Lay.SIG,Lay.TB,
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
  obtain ⟨sp,h0,h1,h2,h3,h4,_,_,_,hsy⟩ := h
  simp only [lay,Whole.base,sp,h0,h1,h2,h3,h4,hsy]

theorem saved_inputs_eq {s t p q : State} (hs : verifyMessageLocal.pre s) (ht : verifyMessageLocal.pre t)
    (hp : verifyMessageLocal.pub s t) (hpa : Whole.Saved (Whole.entered s) 6 p)
    (hqb : Whole.Saved (Whole.entered t) 6 q) :
    Spec.Ed25519.bytesAt p.mem (lay s).pk 32 = Spec.Ed25519.bytesAt q.mem (lay s).pk 32 ∧
    Spec.Ed25519.bytesAt p.mem (lay s).msg (lay s).len.toNat =
      Spec.Ed25519.bytesAt q.mem (lay s).msg (lay s).len.toNat ∧
    Spec.Ed25519.bytesAt p.mem (lay s).sig 64 = Spec.Ed25519.bytesAt q.mem (lay s).sig 64 := by
  have fp := Whole.saved_frame hpa
  have fq := Whole.saved_frame hqb
  obtain ⟨_,h0,h1,h2,h3,_,pk,msg,sig,_⟩ := hp
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
    exact WP.mono (body_ok backend (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp) (entry_syms hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p,q,hpa,hqb,rfl,rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    have hqs : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms Impl.Ed25519.AArch64.bSym =
        (lay s).T := he ▸ entry_syms hqb
    obtain ⟨pk,msg,sig⟩ := saved_inputs_eq hs ht hp hpa hqb
    exact ⟨(body_ct backend (lay_ok hs) (entry_args hs hpa) hqa pk msg sig _ _ _ _ _ _
      ⟨entry_ctx hs hpa,hq,trivial,trivial,entry_syms hpa,hqs⟩ ea eb).1,trivial⟩

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
  mem := bSatMem
  rd := [⟨0x1000,32⟩,⟨0x2000,64⟩,⟨0x3000,64⟩,⟨0x100000,1920⟩]
  wr := [⟨0x4000,8192⟩]
  syms _ := 0x100000

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

open VG.Impl.Ed25519.AArch64 (bSym bWords bConsts) in
/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State} (hsp : 352 ≤ s.sp.toNat)
    (hrd : s.rd = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x1, (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 64⟩,
      ⟨s.syms bSym, 8 * bWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x4, 8192⟩])
    (hheld : ∀ i < bWords.length,
      s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0)
    (hfit : (s.syms bSym).toNat + 8 * bWords.length ≤ 2 ^ 64)
    (hdw : Region.Disjoint ⟨s.syms bSym, 8 * bWords.length⟩ ⟨s.gpr .x4, 8192⟩)
    (hds : Region.Disjoint ⟨s.syms bSym, 8 * bWords.length⟩ ⟨s.sp - 352#64, 352⟩)
    (hal : (s.syms bSym).toNat % 64 = 0)
    (hrest : (⟨s.gpr .x0, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
      (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
      (⟨s.gpr .x3, 64⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x0, 32⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x3, 64⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
      (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64) :
    (Spec.Ed25519.verifyContract (AArch64.abi.withConsts bConsts) 352).pre s := by
  sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, bConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := hrest
  refine ⟨hsp, by rw [hrd]; rfl, hheld, hfit, fun r hr => ?_, hds, hal, by rw [hrd]; rfl, hw, r1, r2, r3,
    r4, r5, r6, r7, r8, r9, r10, r11⟩
  rw [hw, List.mem_singleton] at hr
  rw [hr]; exact hdw

theorem verifyMessage_implies : verifyMessageLocal.Implies
    (Spec.Ed25519.verifyContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.bConsts) 352) where
  pre s h := by
    sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, bConsts_eq, Abi.withConsts,
      Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hsp, hd, held, fit, hdw, hds, -, ht, hw, pc, mc, sc, kp, km, ks, kc, np, nm, ns, nc⟩ := h
    simp only [bWords_length, Nat.reduceMul] at hd held fit hdw hds
    refine ⟨?_, hw, pc, mc, sc, kp, km, ks, kc, np, nm, ns, nc, hsp, held, fit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hds
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, bConsts_eq, Abi.withConsts]
    change t.gpr .x0 = signWord _ at h
    rw [h]
    generalize Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x3) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, bConsts_eq, Abi.withConsts] at h
    obtain ⟨sp, hsy, bytes, pk, msg, len, sig, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, len])
    exact ⟨sp, pk, msg, len, sig, base, first, middle, last, hsy⟩
  sat := by
    have hl := bWords_length
    refine ⟨verifySatState, spec_pre (by decide) (by rw [hl]; rfl) rfl
      (fun i hi => bSatMem_held i (by rw [hl] at hi; exact hi)) (by rw [hl]; decide)
      (by rw [hl]; exact Region.disjoint_of_sep (by decide))
      (by rw [hl]; exact Region.disjoint_of_sep (by decide)) (by decide) ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

theorem verifyMessage_verified (backend : Whole.Backend) :
    Verified AArch64.target (code backend.code backend.suffix)
      (Spec.Ed25519.verifyContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.bConsts) 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verifyMessage_ok backend h) (verifyMessage_ct backend)
      (.refl verifyMessage_implies.sat_left)) verifyMessage_implies

end VG.Proof.Ed25519.AArch64.VerifyMessage
