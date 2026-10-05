import VerifiedGarbage.Impl.Ed25519.X86.VerifyMessage
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.X86.VerifyVerified
import VerifiedGarbage.Proof.Ed25519.X86.MulAddVerified
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Ed25519.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Body`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Args`. -/
section

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Layout`. -/
section
/-! Buffer geometry of complete Ed25519 verification on x86. -/
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86

structure Lay where
  pk : BitVec 32
  msg : BitVec 32
  len : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay)
abbrev PK : Region := ⟨L.pk.setWidth 64, 32⟩
abbrev MSG : Region := ⟨L.msg.setWidth 64, L.len.toNat⟩
abbrev SIG : Region := ⟨L.sig.setWidth 64, 64⟩
abbrev SCR : Region := ⟨L.scr.setWidth 64, 8192⟩
abbrev ARGS : Region := ⟨L.E.setWidth 64 + 260, 20⟩
abbrev RET : Region := ⟨L.E.setWidth 64 + 256, 4⟩
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := Whole.STK L.E
def inputs : List Region := [L.PK, L.MSG, L.SIG, L.ARGS]
def outputs : List Region := [L.SCR]
def value (j : Nat) : BitVec 32 :=
  match j with | 0 => L.pk | 1 => L.msg | 2 => L.len | 3 => L.sig | _ => L.scr

structure Ok : Prop where
  below : 24 ≤ L.E.toNat
  top : L.E.toNat + 280 ≤ 2 ^ 32
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.STK.Disjoint r
  rs : ∀ r ∈ L.inputs, L.RET.Disjoint r
  kc : L.STK.Disjoint L.SCR
  rc : L.RET.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 32
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  ns : L.sig.toNat + 64 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

abbrev Ctx (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

namespace Ctx
variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem input_bytes (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t) (hL : L.Ok)
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

theorem arg_word (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 5) :
    t.mem.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 =
      m₀.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 260) (k := 20) (by omega) (by omega) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm

end Ctx
end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

def Arguments (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) (m : Mem) : Prop :=
  ∀ j < 5, m.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 = L.value j

def value (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

def OutArgs (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) (vs : List Value) (s : State) : Prop :=
  ∀ j (hj : j < vs.length), s.mem.readW (addr L.E (4 * j)) 32 = VG.Proof.Ed25519.X86.VerifyMessage.value L (vs[j]'hj)

variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem Ctx.value (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀)
    {v : Value} (hv : Whole.valid 5 v) : Whole.value L.E s.mem v = VG.Proof.Ed25519.X86.VerifyMessage.value L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    change j < 5 at hv
    simp only [Whole.value, VerifyMessage.value]
    rw [addr_eq (by have := hL.top; omega), hc.arg_word hL hv, ha j hv]

theorem args_ok (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀)
    {vs : List Value} (hlen : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 5 v) :
    WP isa (.block (setup 0 vs)) s fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧
      VG.Frame [⟨L.E.setWidth 64, 24⟩] s.mem t.mem ∧ VG.Proof.Ed25519.X86.VerifyMessage.OutArgs L vs t := by
  refine WP.mono (Whole.Ctx.setup hc (by simpa using hL.top) ?_ (by omega) hv)
    fun t ⟨ht, hf, hvals⟩ => ⟨ht, hf, fun j hj => ?_⟩
  · intro j hj
    refine ⟨L.ARGS, ?_, ?_⟩
    · rw [hc.rd]; exact List.mem_append_left _ (by simp [Lay.inputs])
    · rw [addr_eq (by have := hL.top; omega)]
      exact Offset.contains _ (e := 260) (k := 20) (by omega) (by omega) (by decide)
  · simpa only [Nat.zero_add, hc.value hL ha (hv _ (List.getElem_mem _))] using hvals j hj

end VG.Proof.Ed25519.X86.VerifyMessage

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Body`. -/
section

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Hash`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.PublicKey (callWith)

variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashSpace (h : L.Ok) : Whole.HashSpace L.E L.scr :=
  ⟨h.below, by have := h.top; omega, h.nc, h.kc⟩

theorem shaWithin (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) : Whole.Within (Whole.SHA L.scr) L.SCR :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩

theorem workWithin (h : L.Ok) : Whole.Within (Whole.WORK L.scr) L.SCR :=
  ⟨192, (VG.Proof.Ed25519.X86.VerifyMessage.hashSpace h).work_addr, by change 192 + 272 ≤ 8192; decide⟩

theorem argsWithin (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) {n : Nat} (hn : n ≤ 256) :
    Whole.Within (Whole.ARGS L.E n) L.FR := ⟨0, by simp, by simpa using hn⟩

theorem hash_covers {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R) :
    Covers rs (L.inputs ++ L.FR :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases h r hr with h | ⟨R, hR, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨R, by simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using Or.inr hR, h⟩

theorem hash_writes {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ Whole.Within r L.SCR) :
    ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rcases h r hr with h | h
  · exact .inl h
  · exact .inr ⟨_, by simp [Lay.outputs], h⟩

theorem scratch_covered {r : Region} (h : Whole.Within r L.SCR) :
    Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  .inr ⟨_, by simp [Lay.outputs], h⟩

def hashWrites (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) : List Region :=
  [L.SCR, ⟨L.E.setWidth 64, 24⟩, below L.E 24, ⟨L.E.setWidth 64 + 192, 64⟩]

theorem setup_frame {m m' : Mem} (h : Frame [⟨L.E.setWidth 64, 24⟩] m m') : Frame (VG.Proof.Ed25519.X86.VerifyMessage.hashWrites L) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp [VG.Proof.Ed25519.X86.VerifyMessage.hashWrites], fun _ h => h⟩

theorem hash_frame {m m' : Mem} {wr : List Region}
    (h : Frame (wr ++ [below L.E 24]) m m')
    (hw : ∀ r ∈ wr, Whole.Within r L.SCR ∨ Whole.Within r ⟨L.E.setWidth 64 + 192, 64⟩) :
    Frame (VG.Proof.Ed25519.X86.VerifyMessage.hashWrites L) m m' := by
  refine h.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with h | h
    · exact ⟨_, by simp [VG.Proof.Ed25519.X86.VerifyMessage.hashWrites], h.sub⟩
    · exact ⟨_, by simp [VG.Proof.Ed25519.X86.VerifyMessage.hashWrites], h.sub⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp [VG.Proof.Ed25519.X86.VerifyMessage.hashWrites], fun _ h => h⟩

theorem setup_repr (hL : L.Ok) {u : State}
    (hf : Frame [⟨L.E.setWidth 64, 24⟩] s.mem u.mem) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (L.scr.setWidth 64) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := s.mem) ?_ hr
  intro i hi
  exact hf.bytes (R := Whole.SHA L.scr) (by
    rintro r hr; rw [List.mem_singleton.mp hr]
    exact ((VG.Proof.Ed25519.X86.VerifyMessage.hashSpace hL).args_sha (n := 24) (by decide)).symm) (by change 192 ≤ 2 ^ 64; decide) hi

theorem OutArgs.slot {vs : List Value} {t : State} (h : VG.Proof.Ed25519.X86.VerifyMessage.OutArgs L vs t) (hL : L.Ok)
    {j : Nat} (hj : j < vs.length) (hlen : vs.length ≤ 6) :
    Whole.slots L.E t j = VG.Proof.Ed25519.X86.VerifyMessage.value L (vs[j]'hj) := by
  have e := h j hj
  rw [addr_eq (by have := hL.top; omega)] at e
  exact e

theorem init_step (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀) :
    WP isa Impl.Ed25519.X86.VerifyMessage.init s fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.X86.VerifyMessage.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64) [] := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.args_ok hc hL ha (vs := [.caller 4 0]) (by decide) (by simp [Whole.valid]))
    fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 : Whole.slots L.E u 0 = L.scr := by
    have hh := hs.slot hL (j := 0) (by decide) (by decide)
    change Whole.slots L.E u 0 = L.scr + BitVec.ofNat 32 0 at hh
    simpa only [BitVec.add_zero] using hh
  have H := VG.Proof.Ed25519.X86.VerifyMessage.hashSpace hL
  have cov := VG.Proof.Ed25519.X86.VerifyMessage.hash_covers (L := L) (rs := Whole.initRd L.E ++ Whole.initWr L.scr) (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.argsWithin L (by decide))
    · exact VG.Proof.Ed25519.X86.VerifyMessage.scratch_covered (VG.Proof.Ed25519.X86.VerifyMessage.shaWithin L))
  have ws := VG.Proof.Ed25519.X86.VerifyMessage.hash_writes (L := L) (rs := Whole.initWr L.scr) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (VG.Proof.Ed25519.X86.VerifyMessage.shaWithin L))
  refine WP.mono (Whole.init_call hu H.below (Whole.init_pre hu.esp H a0) cov ws
    ((Whole.call_arg hu.esp H.below H.frameFit (by decide)).trans a0)) fun t ⟨ht, hft, hr⟩ =>
    ⟨ht, (VG.Proof.Ed25519.X86.VerifyMessage.setup_frame hf).trans (VG.Proof.Ed25519.X86.VerifyMessage.hash_frame hft ?_), hr⟩
  intro r hr; rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.shaWithin L)

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Equation`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86

variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def challenge (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) : Region := ⟨(L.E + 128).setWidth 64, 64⟩
def equationRd (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) : List Region := [L.PK, L.SIG, VG.Proof.Ed25519.X86.VerifyMessage.challenge L, ⟨L.E.setWidth 64, 16⟩]
def equationWr (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) : List Region := [⟨L.scr.setWidth 64, 0⟩, L.SCR]
def EqArgs (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) (s : State) : Prop := Whole.slots L.E s 0 = L.pk ∧
  Whole.slots L.E s 1 = L.sig ∧ Whole.slots L.E s 2 = L.E + 128 ∧ Whole.slots L.E s 3 = L.scr

theorem equation_nosp : NoSp verifyEquation := NoSp.of_all (by lit_decide)
theorem equation_stack : stackUse verifyEquation = 0 := by lit_decide

theorem challengeWithin (hL : L.Ok) : Whole.Within (VG.Proof.Ed25519.X86.VerifyMessage.challenge L) L.FR :=
  ⟨128, Whole.frame_addr (VG.Proof.Ed25519.X86.VerifyMessage.hashSpace hL).frameFit (by decide), by change 128 + 64 ≤ 256; decide⟩

theorem equation_pre (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.EqArgs L s) :
    verifyLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.X86.VerifyMessage.equationRd L) (VG.Proof.Ed25519.X86.VerifyMessage.equationWr L)) := by
  have H := VG.Proof.Ed25519.X86.VerifyMessage.hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  obtain ⟨a0, a1, a2, a3⟩ := ha
  have e0 := (ca (j := 0) (by decide)).trans a0
  have e1 := (ca (j := 1) (by decide)).trans a1
  have e2 := (ca (j := 2) (by decide)).trans a2
  have e3 := (ca (j := 3) (by decide)).trans a3
  have ab := Whole.arg_base hc.esp (VG.Proof.Ed25519.X86.VerifyMessage.equationRd L) (VG.Proof.Ed25519.X86.VerifyMessage.equationWr L)
  simp only [verifyLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, e0, e1, e2, e3, ab,
    VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero, VG.Proof.X25519.X86.scR]
  refine ⟨rfl, rfl, hL.sc _ (by simp [Lay.inputs]), hL.sc _ (by simp [Lay.inputs]),
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((VG.Proof.Ed25519.X86.VerifyMessage.challengeWithin hL).sub p hp)),
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p (Region.sub_prefix (by decide) p hp)),
    hL.kc.sub_left (Whole.below_sub_stack hL.below (by decide)), hL.np, hL.ns,
    Whole.frame_fit H.frameFit (by decide : 128 < 256) (by decide : 128 + 64 ≤ 256), hL.nc, ?_⟩
  have e : (L.E - 4).toNat = L.E.toNat - 4 := sub_toNat (k := 4) (by have := hL.below; omega)
  rw [e]
  have := hL.top; omega

theorem equation_correct_result (s : State) (h : verifyLocal.pre s) :
    ∃ tr t, Exec isa verifyEquation s tr t ∧ abiPreserved s t ∧ verifyLocal.post s t := verify_correct h

theorem equation_call (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.EqArgs L s) :
    WP isa (.call "vg_ed25519_verify_equation" verifyEquation) s fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧
      t.gpr .eax = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem (L.pk.setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem (L.sig.setWidth 64) 64)
        (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64)) := by
  have H := VG.Proof.Ed25519.X86.VerifyMessage.hashSpace hL
  have wz : Whole.Within ⟨L.scr.setWidth 64, 0⟩ L.SCR := ⟨0, by simp, by change 0 ≤ 8192; decide⟩
  have wsc : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩
  have cov : Covers (VG.Proof.Ed25519.X86.VerifyMessage.equationRd L ++ VG.Proof.Ed25519.X86.VerifyMessage.equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.X86.VerifyMessage.hash_covers
    simp only [VG.Proof.Ed25519.X86.VerifyMessage.equationRd, VG.Proof.Ed25519.X86.VerifyMessage.equationWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inr ⟨L.PK, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inr ⟨L.SIG, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.challengeWithin hL)
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.argsWithin L (by decide))
    · exact VG.Proof.Ed25519.X86.VerifyMessage.scratch_covered wz
    · exact VG.Proof.Ed25519.X86.VerifyMessage.scratch_covered wsc
  have ws : ∀ r ∈ VG.Proof.Ed25519.X86.VerifyMessage.equationWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
    VG.Proof.Ed25519.X86.VerifyMessage.hash_writes (by
      simp only [VG.Proof.Ed25519.X86.VerifyMessage.equationWr, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact .inr wz
      · exact .inr wsc)
  with_reducible
    refine Whole.call_ok hc hL.below VG.Proof.Ed25519.X86.VerifyMessage.equation_correct_result VG.Proof.Ed25519.X86.VerifyMessage.equation_nosp (by rw [VG.Proof.Ed25519.X86.VerifyMessage.equation_stack]; decide)
      (VG.Proof.Ed25519.X86.VerifyMessage.equation_pre hc hL ha) cov ws fun t ht _ _ post => ⟨ht, ?_⟩
  obtain ⟨t₂, hm, hg, hp⟩ := post
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  obtain ⟨a0, a1, a2, _⟩ := ha
  change t₂.gpr .eax = signWord (Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 0).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 64)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 2).setWidth 64) 64)) at hp
  rw [hg .eax (by decide), (ca (j := 0) (by decide)).trans a0,
    (ca (j := 1) (by decide)).trans a1, (ca (j := 2) (by decide)).trans a2] at hp
  have pk : Spec.Ed25519.bytesAt s.callEntry.mem (L.pk.setWidth 64) 32 =
      Spec.Ed25519.bytesAt s.mem (L.pk.setWidth 64) 32 := by
    apply Whole.callEntry_bytes (r := L.PK) ?_ (by change 32 ≤ 2 ^ 64; decide)
    rw [hc.esp]
    exact ((hL.ks _ (by simp [Lay.inputs])).sub_left (Whole.below_sub_stack hL.below (by decide))).symm
  have sg : Spec.Ed25519.bytesAt s.callEntry.mem (L.sig.setWidth 64) 64 =
      Spec.Ed25519.bytesAt s.mem (L.sig.setWidth 64) 64 := by
    apply Whole.callEntry_bytes (r := L.SIG) ?_ (by change 64 ≤ 2 ^ 64; decide)
    rw [hc.esp]
    exact ((hL.ks _ (by simp [Lay.inputs])).sub_left (Whole.below_sub_stack hL.below (by decide))).symm
  have ch : Spec.Ed25519.bytesAt s.callEntry.mem ((L.E + 128).setWidth 64) 64 =
      Spec.Ed25519.bytesAt s.mem ((L.E + 128).setWidth 64) 64 := by
    apply Whole.callEntry_bytes (r := VG.Proof.Ed25519.X86.VerifyMessage.challenge L) ?_ (by change 64 ≤ 2 ^ 64; decide)
    rw [hc.esp]
    exact (Whole.frame_below hL.below H.frameFit (by decide : 128 < 256) (by decide : 128 + 64 ≤ 256)).symm
  have ce : (L.E + 128).setWidth 64 = L.E.setWidth 64 + 128 := Whole.frame_addr H.frameFit (by decide : 128 < 256)
  rw [pk, sg, ch, ce] at hp
  exact hp

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashFinalize`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.FinalizeArgs`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole VG.Impl.Ed25519.X86.VerifyMessage

def FinArgs (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) (count : BitVec 64) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 3 = L.E + 192 ∧
    Whole.slots L.E t 4 = L.scr + 192 ∧
    Whole.slots L.E t 2 ++ Whole.slots L.E t 1 = count

variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_keep {t u : State} (hf : Frame [⟨L.E.setWidth 64 + 4, 8⟩] t.mem u.mem)
    {j : Nat} (hj : j = 0 ∨ j = 3 ∨ j = 4) : Whole.slots L.E u j = Whole.slots L.E t j := by
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  apply Offset.disjoint (e := 4) (k := 8)
  · rcases hj with rfl | rfl | rfl <;> decide
  · rcases hj with rfl | rfl | rfl <;> decide
  · decide

theorem count_frame {m m' : Mem} (hf : Frame [⟨L.E.setWidth 64 + 4, 8⟩] m m') :
    Frame [⟨L.E.setWidth 64, 24⟩] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (d := 4) (by decide)⟩

theorem finalizeArgs_ok (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀)
    :
    WP isa (.block finalizeArgs) s fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧
      Frame [⟨L.E.setWidth 64, 24⟩] s.mem t.mem ∧
      VG.Proof.Ed25519.X86.VerifyMessage.FinArgs L (BitVec.ofNat 64 (L.len.toNat + 64)) t := by
  rw [finalizeArgs, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.args_ok hc hL ha (vs := [.caller 4 0, .const 0, .const 0, .frame 192, .caller 4 192])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_
  have aa := hs.slot hL (j := 0) (by decide) (by decide)
  have ab := hs.slot hL (j := 1) (by decide) (by decide)
  have ac := hs.slot hL (j := 2) (by decide) (by decide)
  have ad := hs.slot hL (j := 3) (by decide) (by decide)
  have ae := hs.slot hL (j := 4) (by decide) (by decide)
  change Whole.slots L.E u 0 = L.scr + 0#32 at aa
  rw [BitVec.add_zero] at aa
  change Whole.slots L.E u 1 = 0#32 at ab
  change Whole.slots L.E u 2 = 0#32 at ac
  change Whole.slots L.E u 3 = L.E + 192 at ad
  change Whole.slots L.E u 4 = L.scr + 192 at ae
  have hr : InRegions (u.rd ++ u.wr) (addr L.E 268) 4 := by
    refine ⟨L.ARGS, ?_, ?_⟩
    · rw [hu.rd]; simp [Lay.inputs]
    · rw [addr_eq (by have := hL.top; omega)]
      exact Offset.contains _ (e := 260) (k := 20) (d := 268) (n := 4) (by decide) (by decide) (by decide)
  have hx : u.mem.readW (addr L.E 268) 32 = L.len := by
    rw [addr_eq (by have := hL.top; omega)]
    exact (hu.arg_word hL (j := 2) (by decide)).trans (ha 2 (by decide))
  refine WP.mono (Whole.Ctx.count hu (index := 2) (n := 64) (by have := hL.top; omega) hr hx)
    fun t ⟨ht, hft, hlo, hhi⟩ => ⟨ht, hf.trans (VG.Proof.Ed25519.X86.VerifyMessage.count_frame hft),
      (VG.Proof.Ed25519.X86.VerifyMessage.count_keep hft (.inl rfl)).trans aa,
      (VG.Proof.Ed25519.X86.VerifyMessage.count_keep hft (.inr (.inl rfl))).trans ad,
      (VG.Proof.Ed25519.X86.VerifyMessage.count_keep hft (.inr (.inr rfl))).trans ae, ?_⟩
  show (t.mem.readW (L.E.setWidth 64 + 8#64) 32 ++ t.mem.readW (L.E.setWidth 64 + 4#64) 32) = BitVec.ofNat 64 (L.len.toNat + 64)
  change t.mem.readW (L.E.setWidth 64 + 8#64) 32 = _ at hhi
  change t.mem.readW (L.E.setWidth 64 + 4#64) 32 = _ at hlo
  rw [hhi, hlo]
  exact Whole.count_pair L.len 64 (by decide)

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem digest_addr (hL : L.Ok) : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 :=
  addr_eq (x := L.E) (k := 192) (by have := hL.top; omega)

theorem digestWithin (hL : L.Ok) : Whole.Within ⟨(L.E + 192).setWidth 64, 64⟩ L.FR :=
  ⟨192, VG.Proof.Ed25519.X86.VerifyMessage.digest_addr hL, by change 192 + 64 ≤ 256; decide⟩

theorem digest_below (hL : L.Ok) : (below L.E 24).Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ := by
  change Region.Disjoint ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
  rw [Taint.sub_setWidth hL.below, VG.Proof.Ed25519.X86.VerifyMessage.digest_addr hL]
  exact Offset.disjoint_below_above _ (m := 24) (a := 192) (l := 64) (by decide)

theorem finalize_step (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀)
    {msg : List Byte}
    (hlen : msg.length < 2 ^ 64) (hcount : L.len.toNat + 64 = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) msg) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith finalizeArgs Spec.Sha512.finalizeScratchApi.name Impl.Sha512.X86.Stream.finalize) s fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.X86.VerifyMessage.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 msg := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.finalizeArgs_ok hc hL ha) fun u ⟨hu, hf, a0, a3, a4, ac⟩ => ?_)
  have H := VG.Proof.Ed25519.X86.VerifyMessage.hashSpace hL
  have fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega)]
    have := hL.top; omega
  have hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((VG.Proof.Ed25519.X86.VerifyMessage.digestWithin hL).sub p hp))
  have hp := Whole.finalize_pre hu.esp H a0 a3 a4 hd (VG.Proof.Ed25519.X86.VerifyMessage.digest_below hL) (by
    rw [VG.Proof.Ed25519.X86.VerifyMessage.digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)) fit
  have cov := VG.Proof.Ed25519.X86.VerifyMessage.hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.argsWithin L (by decide))
    · exact VG.Proof.Ed25519.X86.VerifyMessage.scratch_covered (VG.Proof.Ed25519.X86.VerifyMessage.shaWithin L)
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.digestWithin hL)
    · exact VG.Proof.Ed25519.X86.VerifyMessage.scratch_covered (VG.Proof.Ed25519.X86.VerifyMessage.workWithin hL))
  have ws := VG.Proof.Ed25519.X86.VerifyMessage.hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (VG.Proof.Ed25519.X86.VerifyMessage.shaWithin L)
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.digestWithin hL)
    · exact .inr (VG.Proof.Ed25519.X86.VerifyMessage.workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  have cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 msg.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), ac, hcount]
  have hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.finalize_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) cnt hbsha (VG.Proof.Ed25519.X86.VerifyMessage.setup_repr hL hf hr) hlen)
    fun t ⟨ht, hft, hdigest⟩ => ⟨ht, ?_, ?_⟩
  · refine (VG.Proof.Ed25519.X86.VerifyMessage.setup_frame hf).trans (VG.Proof.Ed25519.X86.VerifyMessage.hash_frame hft ?_)
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.shaWithin L)
    · exact .inr ⟨0, by rw [VG.Proof.Ed25519.X86.VerifyMessage.digest_addr hL]; simp, by change 0 + 64 ≤ 64; decide⟩
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.workWithin hL)
  · rw [VG.Proof.Ed25519.X86.VerifyMessage.digest_addr hL] at hdigest
    exact hdigest

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashInputs`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashUpdate`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

structure Input (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) (p n : BitVec 32) : Prop where
  cover : Whole.Within ⟨p.setWidth 64, n.toNat⟩ L.FR ∨
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p.setWidth 64, n.toNat⟩ R
  scratch : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ L.SCR
  below : (below L.E 24).Disjoint ⟨p.setWidth 64, n.toNat⟩
  args : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ ⟨L.E.setWidth 64, 24⟩
  fit : p.toNat + n.toNat ≤ 2 ^ 32

def UpdateArgs (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) (c p n : BitVec 32) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 1 = c ∧ Whole.slots L.E t 2 = 0 ∧
    Whole.slots L.E t 3 = p ∧ Whole.slots L.E t 4 = n ∧ Whole.slots L.E t 5 = L.scr + 192

variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_zero_high (x : BitVec 32) : (0#32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat]
  change 0 * 2 ^ 32 + x.toNat = x.toNat % 2 ^ 64
  omega

theorem update_step (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀)
    {vs : List Value} (hlen : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 5 v)
    {c p n : BitVec 32} (hargs : ∀ t, VG.Proof.Ed25519.X86.VerifyMessage.OutArgs L vs t → VG.Proof.Ed25519.X86.VerifyMessage.UpdateArgs L c p n t)
    (hi : VG.Proof.Ed25519.X86.VerifyMessage.Input L p n) {prev : List Byte} (hcount : c.toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update (setup 0 vs)) s fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.X86.VerifyMessage.hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.args_ok hc hL ha hlen hv) fun u ⟨hu, hf, hs⟩ => ?_)
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hargs u hs
  have H := VG.Proof.Ed25519.X86.VerifyMessage.hashSpace hL
  have hp := Whole.update_pre hu.esp H a0 a3 a4 a5 hi.scratch hi.below hi.fit
  have cov := VG.Proof.Ed25519.X86.VerifyMessage.hash_covers (L := L) (rs := Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hi.cover
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.argsWithin L (by decide))
    · exact VG.Proof.Ed25519.X86.VerifyMessage.scratch_covered (VG.Proof.Ed25519.X86.VerifyMessage.shaWithin L)
    · exact VG.Proof.Ed25519.X86.VerifyMessage.scratch_covered (VG.Proof.Ed25519.X86.VerifyMessage.workWithin hL))
  have ws := VG.Proof.Ed25519.X86.VerifyMessage.hash_writes (L := L) (rs := Whole.hashWr L.scr) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (VG.Proof.Ed25519.X86.VerifyMessage.shaWithin L)
    · exact .inr (VG.Proof.Ed25519.X86.VerifyMessage.workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  have cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 prev.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), a1, a2]
    exact (VG.Proof.Ed25519.X86.VerifyMessage.count_zero_high c).trans (congrArg (BitVec.ofNat 64) hcount)
  have hb : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ (below (u.gpr .esp) 4) := by
    rw [hu.esp]
    exact (hi.below.sub_left (below_sub (by decide) H.below)).symm
  have hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.update_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) (ca (by decide) |>.trans a4) cnt hbsha hb
    (VG.Proof.Ed25519.X86.VerifyMessage.setup_repr hL hf hr)) fun t ⟨ht, hft, hrepr⟩ => ⟨ht, ?_, ?_⟩
  · refine (VG.Proof.Ed25519.X86.VerifyMessage.setup_frame hf).trans (VG.Proof.Ed25519.X86.VerifyMessage.hash_frame hft ?_)
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.shaWithin L)
    · exact .inl (VG.Proof.Ed25519.X86.VerifyMessage.workWithin hL)
  · have same : Spec.Ed25519.bytesAt u.mem (p.setWidth 64) n.toNat =
        Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n.toNat := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      exact hf.bytes (R := ⟨p.setWidth 64, n.toNat⟩)
        (by rintro r hr; rw [List.mem_singleton.mp hr]; exact hi.args)
        (by have := n.isLt; change n.toNat ≤ 2 ^ 64; omega) (List.mem_range.mp hi')
    rw [same] at hrepr
    exact hrepr

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem input_geometry (hL : L.Ok) {p n : BitVec 32} {R : Region}
    (hr : R ∈ L.inputs) (hw : Whole.Within ⟨p.setWidth 64, n.toNat⟩ R)
    (hf : p.toNat + n.toNat ≤ 2 ^ 32) : VG.Proof.Ed25519.X86.VerifyMessage.Input L p n := by
  refine ⟨.inr ⟨R, List.mem_append_left _ hr, hw⟩, (hL.sc _ hr).sub_left hw.sub,
    ((hL.ks _ hr).sub_left (Whole.below_sub_stack hL.below (by simp))).sub_right hw.sub, ?_, hf⟩
  exact ((hL.ks _ hr).sub_left (fun p hp => Whole.frame_sub L.E p
    ((VG.Proof.Ed25519.X86.VerifyMessage.argsWithin L (n := 24) (by simp)).sub p hp))).symm.sub_left hw.sub

theorem input_pk (hL : L.Ok) : VG.Proof.Ed25519.X86.VerifyMessage.Input L L.pk 32 :=
  VG.Proof.Ed25519.X86.VerifyMessage.input_geometry hL (R := L.PK) (by simp [Lay.inputs]) ⟨0, by simp, by change 0 + 32 ≤ 32; decide⟩ hL.np

theorem input_sig (hL : L.Ok) : VG.Proof.Ed25519.X86.VerifyMessage.Input L L.sig 32 :=
  VG.Proof.Ed25519.X86.VerifyMessage.input_geometry hL (R := L.SIG) (by simp [Lay.inputs]) ⟨0, by simp, by change 0 + 32 ≤ 64; decide⟩
    (by change L.sig.toNat + 32 ≤ 2 ^ 32; have := hL.ns; omega)

theorem input_msg (hL : L.Ok) : VG.Proof.Ed25519.X86.VerifyMessage.Input L L.msg L.len :=
  VG.Proof.Ed25519.X86.VerifyMessage.input_geometry hL (R := L.MSG) (by simp [Lay.inputs]) ⟨0, by simp, by simp⟩ hL.nm

theorem prefix_step (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀)
    {source count : Nat} (hs : source < 5) {prev : List Byte}
    (hlen : prev.length = count) (hcount : count < 2 ^ 32)
    (hi : VG.Proof.Ed25519.X86.VerifyMessage.Input L (L.value source) 32)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update (Impl.Ed25519.X86.VerifyMessage.prefixArgs source count)) s
      fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.X86.VerifyMessage.hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem ((L.value source).setWidth 64) 32) := by
  apply VG.Proof.Ed25519.X86.VerifyMessage.update_step hc hL ha (vs := [.caller 4 0, .const count, .const 0,
    .caller source 0, .const 32, .caller 4 192]) (by simp)
    (by simp [Whole.valid, hs]) (c := BitVec.ofNat 32 count) (p := L.value source) (n := 32)
    ?_ hi (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcount] using hlen.symm) hr
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ht.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 1) (by simp) (by simp)
  · exact ht.slot hL (j := 2) (by simp) (by simp)
  · exact (ht.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 4) (by simp) (by simp)
  · exact ht.slot hL (j := 5) (by simp) (by simp)

theorem message_step (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀)
    {prev : List Byte} (hlen : prev.length = 64)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update Impl.Ed25519.X86.VerifyMessage.messageArgs) s
      fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧ Frame (VG.Proof.Ed25519.X86.VerifyMessage.hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem (L.msg.setWidth 64) L.len.toNat) := by
  apply VG.Proof.Ed25519.X86.VerifyMessage.update_step hc hL ha (vs := [.caller 4 0, .const 64, .const 0,
    .caller 1 0, .caller 2 0, .caller 4 192]) (by simp)
    (by simp [Whole.valid]) (c := 64) (p := L.msg) (n := L.len)
    ?_ (VG.Proof.Ed25519.X86.VerifyMessage.input_msg hL) hlen.symm hr
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ht.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 1) (by simp) (by simp)
  · exact ht.slot hL (j := 2) (by simp) (by simp)
  · exact (ht.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact (ht.slot hL (j := 4) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 5) (by simp) (by simp)

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Challenge`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashPipeline`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def hashInput (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 32 ++
    Spec.Ed25519.bytesAt m (L.pk.setWidth 64) 32 ++
    Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat

theorem bytes_length (m : Mem) (p : BitVec 64) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

theorem sig_prefix_same (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) :
    Spec.Ed25519.bytesAt s.mem (L.sig.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hc.frame.bytes (R := L.SIG) (by
    intro r hr
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.sc _ (by simp [Lay.inputs])
    · exact (hL.ks _ (by simp [Lay.inputs])).symm)
    (by change 64 ≤ 2 ^ 64; decide) (by change i < 64; have := List.mem_range.mp hi; omega)

theorem hash_ok (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀) :
    WP isa hash s fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 (VG.Proof.Ed25519.X86.VerifyMessage.hashInput L m₀) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.init_step hc hL ha) fun t ⟨ht, _, hinit⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.prefix_step ht hL ha (source := 3) (count := 0)
    (by decide) rfl (by decide) (VG.Proof.Ed25519.X86.VerifyMessage.input_sig hL) hinit) fun u ⟨hu, _, hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem (L.sig.setWidth 64) 32) at hsig
  rw [List.nil_append, VG.Proof.Ed25519.X86.VerifyMessage.sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.prefix_step hu hL ha (source := 0) (count := 32)
    (by decide) (VG.Proof.Ed25519.X86.VerifyMessage.bytes_length _ _ _) (by decide) (VG.Proof.Ed25519.X86.VerifyMessage.input_pk hL) hsig) fun v ⟨hv, _, hpk⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem (L.pk.setWidth 64) 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)] at hpk
  have hpkl : (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 32 ++
      Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32).length = 64 := by
    rw [List.length_append, VG.Proof.Ed25519.X86.VerifyMessage.bytes_length, VG.Proof.Ed25519.X86.VerifyMessage.bytes_length]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.message_step hv hL ha hpkl hpk) fun w ⟨hw, _, hmsg⟩ => ?_)
  rw [hv.input_bytes hL (r := L.MSG) (by simp [Lay.inputs])
    (by have := L.len.isLt; change L.len.toNat ≤ 2 ^ 64; omega)] at hmsg
  have hlen : (VG.Proof.Ed25519.X86.VerifyMessage.hashInput L m₀).length = L.len.toNat + 64 := by
    simp only [VG.Proof.Ed25519.X86.VerifyMessage.hashInput, List.length_append, VG.Proof.Ed25519.X86.VerifyMessage.bytes_length]
    omega
  refine WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.finalize_step hw hL ha (msg := VG.Proof.Ed25519.X86.VerifyMessage.hashInput L m₀)
    (by rw [hlen]; have := L.len.isLt; omega) hlen.symm hmsg) fun t ⟨ht, _, hd⟩ => ⟨ht, hd⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, Proof.Ed25519.X86.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem setup_bytes {u : State} {d n : Nat}
    (hf : Frame [⟨L.E.setWidth 64, 24⟩] s.mem u.mem) (hd : 24 ≤ d) (hn : d + n ≤ 256) :
    Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + BitVec.ofNat 64 d) n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩) (by
    rintro r hr; rw [List.mem_singleton.mp hr]
    exact (Offset.base_disjoint _ hd (by omega)).symm) (by change n ≤ 2 ^ 64; omega) (List.mem_range.mp hi)

theorem reduce_step (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce) s
      fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧ Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.args_ok hc hL ha (vs := [.frame 128, .frame 192, .caller 4 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by decide) (by decide)
  have a1 := hs.slot hL (j := 1) (by decide) (by decide)
  have a2 := (hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _)
  have H := VG.Proof.Ed25519.X86.VerifyMessage.hashSpace hL
  refine WP.mono (Whole.reduce_call hu H (by simp [Lay.outputs]) (d := 128)
    (by decide) (by decide) a0 a1 a2) fun t ⟨ht, _, hd⟩ => ⟨ht, ?_⟩
  have e128 : (L.E + 128).setWidth 64 = L.E.setWidth 64 + 128 := Whole.frame_addr H.frameFit (by decide : 128 < 256)
  have e192 : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 := Whole.frame_addr H.frameFit (by decide : 192 < 256)
  change Spec.Ed25519.bytesAt t.mem ((L.E + 128).setWidth 64) 32 = _ at hd
  have same : Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + 192) 64 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64 :=
    VG.Proof.Ed25519.X86.VerifyMessage.setup_bytes hf (by decide : 24 ≤ 192) (by decide : 192 + 64 ≤ 256)
  rw [e128, e192, same] at hd
  exact hd

theorem extend_step (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 40) (count := 8)
    (VG.Proof.Ed25519.X86.VerifyMessage.hashSpace hL).frameFit (by decide)) fun t ⟨ht, hf, hz⟩ => ⟨ht, ?_⟩
  have low : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨L.E.setWidth 64 + 128, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have high : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 160) 32 = Spec.Ed25519.encodeLE 32 0 := by
    rw [Proof.Ed25519.X86.encodeLE_eq]
    apply Proof.X25519.bytesAt_leBytes_words32
    intro j hj
    have z := hz j hj
    rw [addr_eq (by have := hL.top; omega)] at z
    have e : L.E.setWidth 64 + BitVec.ofNat 64 (4 * (40 + j)) =
        L.E.setWidth 64 + 160 + BitVec.ofNat 64 (4 * j) := by
      rw [show 4 * (40 + j) = 160 + 4 * j by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [e] at z
    rw [z]
    simp
  change Spec.X25519.bytesAt t.mem (L.E.setWidth 64 + 128) (32 + 32) = _
  rw [Proof.X25519.bytesAt_add]
  change Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 ++
    Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128 + 32) 32 = _
  rw [show L.E.setWidth 64 + 128 + 32 = L.E.setWidth 64 + 160 by rw [BitVec.add_assoc]; rfl,
    low, hd, high, VG.Proof.Ed25519.X86.VerifyMessage.reduced_challenge]

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : VG.Proof.Ed25519.X86.VerifyMessage.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : VG.Proof.Ed25519.X86.VerifyMessage.Lay) (m : Mem) : VG.Proof.Ed25519.X86.VerifyMessage.hashInput L m =
    (Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 64).take 32 ++
      Spec.Ed25519.bytesAt m (L.pk.setWidth 64) 32 ++
      Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat := by
  have e : (Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 64).take 32 =
      Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 32 := by
    unfold Spec.Ed25519.bytesAt
    rw [← List.map_take, List.take_range]
    rfl
  rw [e]
  rfl

theorem equation_step (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀)
    {challenge : List Byte}
    (hh : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 = challenge) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith equationArgs "vg_ed25519_verify_equation" Impl.Ed25519.X86.verifyEquation) s
      fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧ t.gpr .eax = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32)
        (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 64) challenge) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.args_ok hc hL ha
    (vs := [.caller 0 0, .caller 3 0, .frame 128, .caller 4 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := (hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)
  have a1 := (hs.slot hL (j := 1) (by decide) (by decide)).trans (BitVec.add_zero _)
  have a2 := hs.slot hL (j := 2) (by decide) (by decide)
  have a3 := (hs.slot hL (j := 3) (by decide) (by decide)).trans (BitVec.add_zero _)
  have he : Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + 128) 64 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 :=
    VG.Proof.Ed25519.X86.VerifyMessage.setup_bytes hf (by decide : 24 ≤ 128) (by decide : 128 + 64 ≤ 256)
  refine WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.equation_call hu hL ⟨a0, a1, a2, a3⟩) fun t ⟨ht, eq⟩ => ⟨ht, ?_⟩
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide),
    hu.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide), he, hh] at eq
  exact eq

theorem body_ok (hc : VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.VerifyMessage.Arguments L m₀) :
    WP isa body s fun t => VG.Proof.Ed25519.X86.VerifyMessage.Ctx L g m₀ t ∧ t.gpr .eax = signWord (Spec.Ed25519.verify
      (Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32)
      (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat)
      (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 64)) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.hash_ok hc hL ha) fun t ⟨ht, hh⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.reduce_step ht hL ha) fun u ⟨hu, hr⟩ => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.extend_step hu hL hr) fun v ⟨hv, he⟩ => ?_)
  rw [VG.Proof.Ed25519.X86.VerifyMessage.hashInput_eq] at he
  exact VG.Proof.Ed25519.X86.VerifyMessage.equation_step hv hL ha he

end VG.Proof.Ed25519.X86.VerifyMessage

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Verified`. -/
section

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTEquation`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTHashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTHash`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTCommon`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def Two (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b ∧ P a ∧ P b

theorem two_esp {P : State → Prop} {a b : State} (h : Two L g₁ g₂ m₁ m₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.esp.trans h.2.1.esp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ m₁ t → P t → WP isa c t fun u => Ctx L g₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ m₂ t → P t → WP isa c t fun u => Ctx L g₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) c (Two L g₁ g₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (vs : List Value) (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 5 v)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0 vs)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup 0 vs))
      (Two L g₁ g₂ m₁ m₂ (OutArgs L vs)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.args_ok hc hL ha hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.args_ok hc hL hb hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem call_args_eq (hL : L.Ok) {vs : List Value} (hn : vs.length ≤ 6)
    {a b : State} (h : Two L g₁ g₂ m₁ m₂ (OutArgs L vs) a b) {j : Nat} (hj : j < vs.length) :
    arg a.callEntry j = arg b.callEntry j := by
  have H := hashSpace hL
  rw [Whole.call_arg h.1.esp H.below H.frameFit (by omega),
    Whole.call_arg h.2.1.esp H.below H.frameFit (by omega),
    h.2.2.1.slot hL hj hn, h.2.2.2.slot hL hj hn]

theorem call_ct (hL : L.Ok) {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (sp : NoSp c) (stack : stackUse c ≤ 20)
    (ready : ∀ {g m t}, Ctx L g m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, Two L g₁ g₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) (.call name c) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply two_wp
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.1
    let rb := ready h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb, two_esp h⟩
  · intro t hc hs
    exact WP.mono ((ready hc hs).wp hc correct sp stack hL.below) fun _ hu => ⟨hu, trivial⟩
  · intro t hc hs
    exact WP.mono ((ready hc hs).wp hc correct sp stack hL.below) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTReady`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def init_ready (hc : Ctx L g m₀ s) (hL : L.Ok)
    (a0 : Whole.slots L.E s 0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initX86 Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have H := hashSpace hL
  have cov := hash_covers (L := L) (rs := Whole.initRd L.E ++ Whole.initWr L.scr) (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L))
  have ws := hash_writes (L := L) (rs := Whole.initWr L.scr) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin L))
  exact ⟨_, _, Whole.init_pre hc.esp H a0, cov, ws⟩

def update_ready (hc : Ctx L g m₀ s) (hL : L.Ok) {c p n : BitVec 32}
    (hi : Input L p n) (ha : UpdateArgs L c p n s) :
    Whole.CallReady Proof.Sha512.updateX86 L.E L.inputs L.outputs s := by
  obtain ⟨a0, _, _, a3, a4, a5⟩ := ha
  have H := hashSpace hL
  have hp := Whole.update_pre hc.esp H a0 a3 a4 a5 hi.scratch hi.below hi.fit
  have cov := hash_covers (L := L) (rs := Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hi.cover
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.hashWr L.scr) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inr (workWithin hL))
  exact ⟨_, _, hp, cov, ws⟩

def finalize_ready (hc : Ctx L g m₀ s) (hL : L.Ok) {count : BitVec 64}
    (ha : FinArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeX86 L.E L.inputs L.outputs s := by
  obtain ⟨a0, a3, a4, _⟩ := ha
  have H := hashSpace hL
  have fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega)]
    have := hL.top; omega
  have hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((digestWithin hL).sub p hp))
  have hp := Whole.finalize_pre hc.esp H a0 a3 a4 hd (digest_below hL) (by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)) fit
  have cov := hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact .inr (workWithin hL))
  exact ⟨_, _, hp, cov, ws⟩

def reduce_ready (hc : Ctx L g m₀ s) (hL : L.Ok)
    (a0 : Whole.slots L.E s 0 = L.E + 128)
    (a1 : Whole.slots L.E s 1 = L.E + 192) (a2 : Whole.slots L.E s 2 = L.scr) :
    Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have H := hashSpace hL
  have wo : Whole.Within ⟨(L.E + 128).setWidth 64, 32⟩ L.FR :=
    ⟨128, Whole.frame_addr H.frameFit (by decide), by change 128 + 32 ≤ 256; decide⟩
  have cov : Covers (Whole.reduceRd L.E ++ Whole.reduceWr L.E L.scr 128)
      (L.inputs ++ L.FR :: L.outputs) := by
    apply hash_covers
    simp only [Whole.reduceRd, Whole.reduceWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (digestWithin hL)
    · exact .inl (argsWithin L (by decide))
    · exact .inl wo
    · exact scratch_covered ⟨0, by simp, by simp⟩
  have ws : ∀ r ∈ Whole.reduceWr L.E L.scr 128,
      Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply hash_writes
    simp only [Whole.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl wo
    · exact .inr ⟨0, by simp, by simp⟩
  exact ⟨_, _, Whole.reduce_pre hc H (by decide) (by decide) a0 a1 a2, cov, ws⟩

def equation_ready (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : EqArgs L s) :
    Whole.CallReady verifyLocal L.E L.inputs L.outputs s := by
  have wz : Whole.Within ⟨L.scr.setWidth 64, 0⟩ L.SCR := ⟨0, by simp, by change 0 ≤ 8192; decide⟩
  have wsc : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩
  have cov : Covers (equationRd L ++ equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply hash_covers
    simp only [equationRd, equationWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inr ⟨L.PK, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inr ⟨L.SIG, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inl (challengeWithin hL)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered wz
    · exact scratch_covered wsc
  have ws : ∀ r ∈ equationWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
    hash_writes (by
      simp only [equationWr, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact .inr wz
      · exact .inr wsc)
  exact ⟨_, _, equation_pre hc hL ha, cov, ws⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 4 0]))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL (Proof.Sha512.X86.Stream.init_verified _).1
    (Proof.Sha512.X86.Stream.init_verified _).2.1 Whole.init_nosp (by rw [Whole.init_stack]; decide)
  · intro g m t hc hs
    apply init_ready hc hL
    exact (hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 1)⟩

theorem update_call_ct (hL : L.Ok) {vs : List Value} (hn : vs.length = 6)
    {c p n : BitVec 32} (hi : Input L p n)
    (hargs : ∀ t, OutArgs L vs t → UpdateArgs L c p n t) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L vs))
      (.call Spec.Sha512.updateScratchApi.name Impl.Sha512.X86.Stream.update)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL Proof.Sha512.X86.Stream.Update.update_verified.1
    Proof.Sha512.X86.Stream.Update.update_verified.2.1 Whole.update_nosp (by rw [Whole.update_stack])
  · intro g m t hc hs
    exact update_ready hc hL hi (hargs t hs)
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), fun j hj => call_args_eq hL (by omega) h (by omega)⟩

theorem append_pair_eq {a b c d : BitVec 32} (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  constructor
  · have e := congrArg (BitVec.extractLsb' 32 32) h
    simpa only [BitVec.extractLsb'_append_eq_left] using e
  · have e := congrArg (BitVec.extractLsb' 0 32) h
    simpa only [BitVec.extractLsb'_append_eq_right] using e

theorem finalize_call_ct (hL : L.Ok) (count : BitVec 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (FinArgs L count))
      (.call Spec.Sha512.finalizeScratchApi.name Impl.Sha512.X86.Stream.finalize)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL Proof.Sha512.X86.Stream.Finalize.finalize_verified.1
    Proof.Sha512.X86.Stream.Finalize.finalize_verified.2.1 Whole.finalize_nosp (by rw [Whole.finalize_stack])
  · intro g m t hc hs
    exact finalize_ready hc hL hs
  · intro a b ar aw br bw h
    refine ⟨congrArg (· - 4) (two_esp h), ?_⟩
    intro j hj
    have H := hashSpace hL
    rw [arg_withRegions, arg_withRegions, Whole.call_arg h.1.esp H.below H.frameFit (by omega),
      Whole.call_arg h.2.1.esp H.below H.frameFit (by omega)]
    obtain ⟨a0, a3, a4, ac⟩ := h.2.2.1
    obtain ⟨b0, b3, b4, bc⟩ := h.2.2.2
    have pair := append_pair_eq (ac.trans bc.symm)
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · exact a0.trans b0.symm
    · exact pair.2
    · exact pair.1
    · exact a3.trans b3.symm
    · exact a4.trans b4.symm

theorem finalize_args_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block finalizeArgs)
      (Two L g₁ g₂ m₁ m₂ (FinArgs L (BitVec.ofNat 64 (L.len.toNat + 64)))) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by taint_decide)) ?_ ?_
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL ha) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL hb) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem update_outArgs (hL : L.Ok) {source count : Nat} {nv : Value} {s : State}
    (hs : OutArgs L [.caller 4 0, .const count, .const 0, .caller source 0, nv, .caller 4 192] s) :
    UpdateArgs L (BitVec.ofNat 32 count) (L.value source) (value L nv) s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hs.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact hs.slot hL (j := 1) (by simp) (by simp)
  · exact hs.slot hL (j := 2) (by simp) (by simp)
  · exact (hs.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact hs.slot hL (j := 4) (by simp) (by simp)
  · exact hs.slot hL (j := 5) (by simp) (by simp)

theorem hash_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hash (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have ini := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0] (by decide) (by simp [Whole.valid]) (by taint_decide)
  have rs := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0, .const 0, .const 0, .caller 3 0, .const 32, .caller 4 192]
    (by decide) (by simp [Whole.valid]) (by taint_decide)
  have ps := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0, .const 32, .const 0, .caller 0 0, .const 32, .caller 4 192]
    (by decide) (by simp [Whole.valid]) (by taint_decide)
  have ms := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0, .const 64, .const 0, .caller 1 0, .caller 2 0, .caller 4 192]
    (by decide) (by simp [Whole.valid]) (by taint_decide)
  have r := update_call_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) hL
    (vs := [.caller 4 0, .const 0, .const 0, .caller 3 0, .const 32, .caller 4 192]) rfl
    (input_sig hL) (fun _ hs => update_outArgs hL hs)
  have p := update_call_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) hL
    (vs := [.caller 4 0, .const 32, .const 0, .caller 0 0, .const 32, .caller 4 192]) rfl
    (input_pk hL) (fun _ hs => update_outArgs hL hs)
  have m := update_call_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) hL
    (vs := [.caller 4 0, .const 64, .const 0, .caller 1 0, .caller 2 0, .caller 4 192]) rfl
    (input_msg hL) (fun _ hs => by
      have h := update_outArgs hL hs
      simpa only [value, Lay.value, BitVec.add_zero] using h)
  exact (ini.seq (init_call_ct hL)).seq ((rs.seq r).seq ((ps.seq p).seq
    ((ms.seq m).seq ((finalize_args_ct hL ha hb).seq (finalize_call_ct hL _)))))

theorem hash_ct_result (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (he : hashInput L m₁ = hashInput L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hash
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (hashInput L m₁)) := by
  refine two_wp ((hash_ct hL ha hb).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_ ?_
  · intro t hc _
    exact hash_ok hc hL ha
  · intro t hc _
    refine WP.mono (hash_ok hc hL hb) fun _ ⟨hu, hd⟩ => ⟨hu, ?_⟩
    rw [he]
    exact hd

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTScalars`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.frame 128, .frame 192, .caller 4 0]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarReduce_ok scalarReduce_ct Whole.reduce_nosp (by rw [Whole.reduce_stack]; decide)
  · intro g m t hc hs
    exact reduce_ready hc hL (hs.slot hL (j := 0) (by decide) (by decide))
      (hs.slot hL (j := 1) (by decide) (by decide))
      ((hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 3),
      call_args_eq hL (by decide) h (by decide : 1 < 3), call_args_eq hL (by decide) h (by decide : 2 < 3)⟩

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = digest)
      (VG.Impl.Ed25519.X86.PublicKey.callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 = Spec.Ed25519.scalarReduce digest) := by
  have ct := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 128, .frame 192, .caller 4 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq (reduce_call_ct hL)
  refine two_wp (ct.mono (fun _ _ h => ⟨h.1, h.2.1, trivial, trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro t hc hd
    refine WP.mono (reduce_step hc hL ha) fun _ ⟨hu, hr⟩ => ⟨hu, ?_⟩
    rw [hd] at hr
    exact hr
  · intro t hc hd
    refine WP.mono (reduce_step hc hL hb) fun _ ⟨hu, hr⟩ => ⟨hu, ?_⟩
    rw [hd] at hr
    exact hr

theorem extend_ct (hL : L.Ok) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 = Spec.Ed25519.scalarReduce digest)
      (.block extendChallenge)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L)) := by
  exact two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by taint_decide))
    (fun _ hc hd => extend_step hc hL hd) (fun _ hc hd => extend_step hc hL hd)

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def equationValues : List Value := [.caller 0 0, .caller 3 0, .frame 128, .caller 4 0]
def EqState (L : Lay) (ch : List Byte) (s : State) : Prop :=
  OutArgs L equationValues s ∧ Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 = ch

theorem eq_args (hL : L.Ok) {s : State} (hs : OutArgs L equationValues s) : EqArgs L s :=
  ⟨(hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _),
    (hs.slot hL (j := 1) (by decide) (by decide)).trans (BitVec.add_zero _),
    hs.slot hL (j := 2) (by decide) (by decide),
    (hs.slot hL (j := 3) (by decide) (by decide)).trans (BitVec.add_zero _)⟩

theorem ce_input {g : Reg → BitVec 32} {m : Mem} {s : State}
    (hc : Ctx L g m s) (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt s.callEntry.mem r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  have e := Whole.callEntry_bytes (t := s) (r := r) (by
    rw [hc.esp]
    exact ((hL.ks _ hr).sub_left (Whole.below_sub_stack hL.below (by decide))).symm) hn
  exact e.trans (hc.input_bytes hL hr hn)

theorem ce_challenge {g : Reg → BitVec 32} {m : Mem} {s : State}
    (hc : Ctx L g m s) (hL : L.Ok) {ch : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 = ch) :
    Spec.Ed25519.bytesAt s.callEntry.mem ((L.E + 128).setWidth 64) 64 = ch := by
  have e := Whole.callEntry_bytes (t := s) (r := challenge L) (by
    rw [hc.esp]
    exact (Whole.frame_below hL.below (hashSpace hL).frameFit
      (by decide : 128 < 256) (by decide : 128 + 64 ≤ 256)).symm) (by change 64 ≤ 2 ^ 64; decide)
  have ea : (L.E + 128).setWidth 64 = L.E.setWidth 64 + 128 :=
    Whole.frame_addr (hashSpace hL).frameFit (by decide : 128 < 256)
  change Spec.Ed25519.bytesAt s.callEntry.mem ((L.E + 128).setWidth 64) 64 =
    Spec.Ed25519.bytesAt s.mem ((L.E + 128).setWidth 64) 64 at e
  rw [ea] at e ⊢
  exact e.trans he

theorem equation_call_ct (hL : L.Ok) (ch : List Byte)
    (hp : Spec.Ed25519.bytesAt m₁ (L.pk.setWidth 64) 32 = Spec.Ed25519.bytesAt m₂ (L.pk.setWidth 64) 32)
    (hs : Spec.Ed25519.bytesAt m₁ (L.sig.setWidth 64) 64 = Spec.Ed25519.bytesAt m₂ (L.sig.setWidth 64) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (EqState L ch))
      (.call "vg_ed25519_verify_equation" Impl.Ed25519.X86.verifyEquation)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL equation_correct_result verify_ct equation_nosp (by rw [equation_stack]; decide)
  · intro g m t hc hh
    exact equation_ready hc hL (eq_args hL hh.1)
  · intro a b ar aw br bw h
    have hargs : Two L g₁ g₂ m₁ m₂ (OutArgs L equationValues) a b := ⟨h.1, h.2.1, h.2.2.1.1, h.2.2.2.1⟩
    have hj {j : Nat} (hh : j < 4) := call_args_eq hL (by decide) hargs hh
    have H := hashSpace hL
    have ea := eq_args hL h.2.2.1.1
    have eb := eq_args hL h.2.2.2.1
    have a0 := (Whole.call_arg h.1.esp H.below H.frameFit (by decide : 0 < 64)).trans ea.1
    have a1 := (Whole.call_arg h.1.esp H.below H.frameFit (by decide : 1 < 64)).trans ea.2.1
    have a2 := (Whole.call_arg h.1.esp H.below H.frameFit (by decide : 2 < 64)).trans ea.2.2.1
    have b0 := (Whole.call_arg h.2.1.esp H.below H.frameFit (by decide : 0 < 64)).trans eb.1
    have b1 := (Whole.call_arg h.2.1.esp H.below H.frameFit (by decide : 1 < 64)).trans eb.2.1
    have b2 := (Whole.call_arg h.2.1.esp H.below H.frameFit (by decide : 2 < 64)).trans eb.2.2.1
    refine ⟨congrArg (· - 4) (two_esp h), hj (by decide), hj (by decide), hj (by decide), hj (by decide), ?_, ?_, ?_⟩
    · simp only [arg_withRegions, State.withRegions_mem, a0, b0]
      exact (ce_input h.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)).trans
        (hp.trans (ce_input h.2.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)).symm)
    · simp only [arg_withRegions, State.withRegions_mem, a1, b1]
      exact (ce_input h.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)).trans
        (hs.trans (ce_input h.2.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)).symm)
    · simp only [arg_withRegions, State.withRegions_mem, a2, b2]
      exact (ce_challenge h.1 hL h.2.2.1.2).trans (ce_challenge h.2.1 hL h.2.2.2.2).symm

theorem equation_setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (ch : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 64 = ch)
      (.block equationArgs) (Two L g₁ g₂ m₁ m₂ (EqState L ch)) := by
  have ct := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb equationValues
    (by decide) (by simp [equationValues, Whole.valid]) (by taint_decide)
  refine two_wp (ct.mono (fun _ _ h => ⟨h.1, h.2.1, trivial, trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro t hc hd
    refine WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.args_ok hc hL ha (vs := equationValues) (by decide)
      (by simp [equationValues, Whole.valid])) fun u ⟨hu, hf, hs⟩ => ⟨hu, hs, ?_⟩
    exact (setup_bytes hf (by decide : 24 ≤ 128) (by decide : 128 + 64 ≤ 256)).trans hd
  · intro t hc hd
    refine WP.mono (VG.Proof.Ed25519.X86.VerifyMessage.args_ok hc hL hb (vs := equationValues) (by decide)
      (by simp [equationValues, Whole.valid])) fun u ⟨hu, hf, hs⟩ => ⟨hu, hs, ?_⟩
    exact (setup_bytes hf (by decide : 24 ≤ 128) (by decide : 128 + 64 ≤ 256)).trans hd

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Entry`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86

def verifyRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩,
    ⟨(arg s 3).setWidth 64, 64⟩, ⟨argAddr s 0, 20⟩]
def verifyWr (s : State) : List Region := [⟨(arg s 4).setWidth 64, 8192⟩]

def verifyMessageLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let sig : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let scr : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = verifyRd s ∧ s.wr = verifyWr s ∧
      pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s t := t.gpr .eax = signWord (Spec.Ed25519.verify
    (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
    (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 64))
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧ arg s 4 = arg t 4 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32 = Spec.Ed25519.bytesAt t.mem ((arg t 0).setWidth 64) 32 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Ed25519.bytesAt t.mem ((arg t 1).setWidth 64) (arg t 2).toNat ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 64 = Spec.Ed25519.bytesAt t.mem ((arg t 3).setWidth 64) 64

def lay (s : State) : Lay :=
  ⟨arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, s.gpr .esp - BitVec.ofNat 32 256⟩

theorem entry_bounds {s : State} (h : verifyMessageLocal.pre s) :
    280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem lay_base {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).E.setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 :=
  Taint.sub_setWidth (by have := (entry_bounds h).1; omega)

theorem lay_args {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).ARGS = ⟨argAddr s 0, 20⟩ := by
  rw [Lay.ARGS, lay_base h]
  have ha : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    addr_eq (by have := (entry_bounds h).2; omega)
  rw [ha]
  congr 1
  change _ - 256#64 + 260#64 = _ + 4#64
  rw [show BitVec.ofNat 64 260 = BitVec.ofNat 64 256 + BitVec.ofNat 64 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem lay_ret {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  rw [Lay.RET, lay_base h]
  change (⟨(s.gpr .esp).setWidth 64 - 256#64 + 256#64, 4⟩ : Region) = _
  rw [BitVec.sub_add_cancel]

theorem lay_stack {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩ := by
  rw [Lay.STK, Whole.STK, lay_base h, BitVec.sub_sub]
  rfl

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨rd, wr, pc, mc, sc, ac, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns, nc, nb, na⟩ := h
  have h : verifyMessageLocal.pre s := ⟨rd, wr, pc, mc, sc, ac, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns, nc, nb, na⟩
  have top : (lay s).E.toNat + 280 ≤ 2 ^ 32 := by
    change (s.gpr .esp - BitVec.ofNat 32 256).toNat + 280 ≤ _
    rw [sub_toNat (by omega)]
    omega
  refine ⟨?_, top, ?_, ?_, ?_, ?_, ?_, np, nm, ns, nc⟩
  · change 24 ≤ (s.gpr .esp - BitVec.ofNat 32 256).toNat
    rw [sub_toNat (by omega)]
    omega
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact pc
    · exact mc
    · exact sc
    · rw [lay_args h]; exact ac
  · intro r hr
    rw [lay_stack h]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact kp
    · exact km
    · exact ks
    · rw [Lay.ARGS, lay_base h]
      have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 + 260 =
          (s.gpr .esp).setWidth 64 + 4 := by
        change _ - 256#64 + 260#64 = _ + 4#64
        rw [show (260#64) = 256#64 + 4#64 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [e]
      exact Offset.disjoint_below_above _ (by decide)
  · intro r hr
    rw [lay_ret h]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact rp
    · exact rm
    · exact rs
    · rw [Lay.ARGS, lay_base h]
      have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 + 260 =
          (s.gpr .esp).setWidth 64 + 4 := by
        change _ - 256#64 + 260#64 = _ + 4#64
        rw [show (260#64) = 256#64 + 4#64 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [e]
      exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  · rw [lay_stack h]; exact kc
  · rw [lay_ret h]; exact rc

theorem lay_arguments {s : State} (h : verifyMessageLocal.pre s) : Arguments (lay s) s.mem := by
  intro j hj
  have hb := lay_ok h
  have e : (lay s).E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j) = argAddr s j := by
    rw [← addr_eq (by have := hb.top; omega)]
    simp only [addr, lay, argAddr]
    rw [show 260 + 4 * j = 256 + (4 + 4 * j) by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [e]
  change arg s j = (lay s).value j
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem push_ctx {s : State} (h : verifyMessageLocal.pre s) :
    Ctx (lay s) s.gpr s.mem (pushed (List.replicate 64 .eax) s) := by
  have hn := (entry_bounds h).1
  have hf := pushed_frame (s := s) (rs := List.replicate 64 .eax) (by simp)
    (by simp only [List.length_replicate]; omega)
  refine ⟨?_, ?_, ?_, fun r _ hn => pushed_gpr _ _ hn, ?_⟩
  · rw [pushed_rd, h.1]
    rw [Lay.inputs, lay_args h]
    rfl
  · rw [pushed_wr, h.2.1]
    simp only [List.length_replicate, Whole.FR, Lay.outputs, Lay.SCR, lay, verifyWr]
  · rw [pushed_esp, List.length_replicate]
    rfl
  · refine Frame.sub hf fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine ⟨(lay s).STK, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [lay_stack h, ← Taint.sub_setWidth hn]
    exact below_sub (by simp) hn

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Lit`. -/
section
namespace VG.Impl.Ed25519.X86.VerifyMessage
materialize_code code
end VG.Impl.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CT`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Correct`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem body_nosp : NoSp body := by
  have ni : NoSp (.block initArgs) := NoSp.of_all (by decide +kernel)
  have np0 : NoSp (.block (prefixArgs 3 0)) := NoSp.of_all (by decide +kernel)
  have np1 : NoSp (.block (prefixArgs 0 32)) := NoSp.of_all (by decide +kernel)
  have nm : NoSp (.block messageArgs) := NoSp.of_all (by decide +kernel)
  have nf : NoSp (.block finalizeArgs) := NoSp.of_all (by decide +kernel)
  have nr : NoSp (.block reduceArgs) := NoSp.of_all (by decide +kernel)
  have ne : NoSp (.block extendChallenge) := NoSp.of_all (by decide +kernel)
  have nq : NoSp (.block equationArgs) := NoSp.of_all (by decide +kernel)
  exact noSp_seq
    (noSp_seq (noSp_seq ni Whole.init_nosp)
      (noSp_seq (noSp_seq np0 Whole.update_nosp)
      (noSp_seq (noSp_seq np1 Whole.update_nosp)
      (noSp_seq (noSp_seq nm Whole.update_nosp) (noSp_seq nf Whole.finalize_nosp)))))
    (noSp_seq (noSp_seq nr Whole.reduce_nosp)
      (noSp_seq ne (noSp_seq nq equation_nosp)))

theorem verifyMessage_ok {s : State} (h : verifyMessageLocal.pre s) :
    WP isa code s fun t => abiPreserved s t ∧ verifyMessageLocal.post s t := by
  have hL := lay_ok h
  have hb := entry_bounds h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; omega) body_nosp
    (WP.mono (body_ok (push_ctx h) hL (lay_arguments h)) fun u ⟨hu, ho⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; simp [calleeSaved] at hr), hu.cs r hr he]
  · rw [popped_mem]
    refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
    · rw [lay_ret h]; exact Region.contains_self _ _
    · simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hL.rc
      · change (lay s).RET.Disjoint (lay s).STK
        rw [lay_ret h, lay_stack h]
        exact (Offset.below_disjoint _ (by decide)).symm
  · change (popped .edx (List.replicate 64 .eax).length u).gpr .eax = _
    rw [popped_gpr _ _ _ (by decide) (by decide)]
    exact ho

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hp : Spec.Ed25519.bytesAt m₁ (L.pk.setWidth 64) 32 = Spec.Ed25519.bytesAt m₂ (L.pk.setWidth 64) 32)
    (hm : Spec.Ed25519.bytesAt m₁ (L.msg.setWidth 64) L.len.toNat =
      Spec.Ed25519.bytesAt m₂ (L.msg.setWidth 64) L.len.toNat)
    (hs : Spec.Ed25519.bytesAt m₁ (L.sig.setWidth 64) 64 = Spec.Ed25519.bytesAt m₂ (L.sig.setWidth 64) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hi : hashInput L m₁ = hashInput L m₂ := by
    rw [hashInput_eq, hashInput_eq, hp, hm, hs]
  exact (hash_ct_result hL ha hb hi).seq ((reduce_ct hL ha hb _).seq
    ((extend_ct hL _).seq ((equation_setup_ct hL ha hb _).seq (equation_call_ct hL _ hp hs))))

theorem verifyMessage_ct : ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub code := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  obtain ⟨esp, a0, a1, a2, a3, a4, pk, msg, sig⟩ := hp
  have eqL : lay s₁ = lay s₂ := by simp only [lay, esp, a0, a1, a2, a3, a4]
  have h₂ : Ctx (lay s₁) s₂.gpr s₂.mem (pushed (List.replicate 64 .eax) s₂) := eqL.symm ▸ push_ctx p₂
  have arg₂ : Arguments (lay s₁) s₂.mem := eqL.symm ▸ lay_arguments p₂
  have pk' : Spec.Ed25519.bytesAt s₁.mem ((lay s₁).pk.setWidth 64) 32 =
      Spec.Ed25519.bytesAt s₂.mem ((lay s₁).pk.setWidth 64) 32 := by
    change Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 0).setWidth 64) 32 = Spec.Ed25519.bytesAt s₂.mem ((arg s₁ 0).setWidth 64) 32
    rw [← a0] at pk
    with_reducible exact pk
  have msg' : Spec.Ed25519.bytesAt s₁.mem ((lay s₁).msg.setWidth 64) (lay s₁).len.toNat =
      Spec.Ed25519.bytesAt s₂.mem ((lay s₁).msg.setWidth 64) (lay s₁).len.toNat := by
    change Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 1).setWidth 64) (arg s₁ 2).toNat = Spec.Ed25519.bytesAt s₂.mem ((arg s₁ 1).setWidth 64) (arg s₁ 2).toNat
    rw [← a1, ← a2] at msg
    with_reducible exact msg
  have sig' : Spec.Ed25519.bytesAt s₁.mem ((lay s₁).sig.setWidth 64) 64 =
      Spec.Ed25519.bytesAt s₂.mem ((lay s₁).sig.setWidth 64) 64 := by
    change Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 3).setWidth 64) 64 = Spec.Ed25519.bytesAt s₂.mem ((arg s₁ 3).setWidth 64) 64
    rw [← a3] at sig
    with_reducible exact sig
  exact ⟨(body_ct (lay_ok p₁) (lay_arguments p₁) arg₂ pk' msg' sig' _ _ _ _ _ _
    ⟨push_ctx p₁, h₂, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Contract`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86

def verifyWide : Contract isa := { verifyMessageLocal with
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let sig : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let scr : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [pk, msg, sig] ∧ s.wr = [scr, args] ∧
      pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

theorem verifyWide_pre (s : State) (h : verifyWide.pre s) :
    verifyMessageLocal.pre (s.withRegions (verifyRd s) (verifyWr s)) := by
  simp only [verifyMessageLocal, verifyRd, verifyWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

def verifySatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else
    if a = 0x800c then 0x40 else if a = 0x8011 then 0x30 else if a = 0x8015 then 0x40 else 0

def verifySatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := verifySatMem
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8004, 20⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verifyWide_implies : verifyWide.Implies (Spec.Ed25519.verifyContract X86.abi 280) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, verifyWide, verifyMessageLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    change t.gpr .eax = signWord _ at h
    rw [h, BitVec.setWidth_append_eq_right]
    generalize Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
      (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨sp, bytes, pk, msg, len, sig, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, len])
    exact ⟨sp, pk, msg, len, sig, base, first, middle, last⟩
  sat := by
    have a0 : arg verifySatState 0 = 0x1000 := by decide
    have a1 : arg verifySatState 1 = 0x2000 := by decide
    have a2 : arg verifySatState 2 = 64 := by decide
    have a3 : arg verifySatState 3 = 0x3000 := by decide
    have a4 : arg verifySatState 4 = 0x4000 := by decide
    have e : argAddr verifySatState 0 = 0x8004 := by decide
    have esp : verifySatState.gpr .esp = 0x8000 := rfl
    sig_implies_sat [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, verifyWide, verifyMessageLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, e, esp] using verifySatState

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

theorem verifyMessage_verified : Verified X86.target code (Spec.Ed25519.verifyContract X86.abi 280) := by
  have hsat := verifyWide_implies.sat_left
  have satLocal : ∃ s, verifyMessageLocal.pre s := hsat.elim fun s h => ⟨_, verifyWide_pre s h⟩
  have verifiedLocal : Verified X86.target code verifyMessageLocal :=
    Verified.of_correct (fun _ h => verifyMessage_ok h) verifyMessage_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal verifyRd verifyWr verifyWide_pre
    ?_ ?_ ?_ ?_ hsat) verifyWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [verifyRd, verifyWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [verifyWr, List.mem_singleton] at hr
    subst hr
    simp
  · intro s t _ h
    simpa only [verifyWide, verifyMessageLocal, arg_withRegions, State.withRegions_mem,
      State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [verifyWide, verifyMessageLocal, arg_withRegions, State.withRegions_gpr,
      State.withRegions_mem] using h

end VG.Proof.Ed25519.X86.VerifyMessage

end
