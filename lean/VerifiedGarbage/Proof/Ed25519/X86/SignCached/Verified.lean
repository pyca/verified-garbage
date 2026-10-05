import VerifiedGarbage.Impl.Ed25519.X86.SignCached
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.X86.MulAddVerified
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Spec.Ed25519.CachedSign
import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Ed25519.X86.ScalarVerified

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.CTReady`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.Args`. -/
section

/-! Merged from `Proof.Ed25519.X86.SignCached.Layout`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

structure Lay where
  out : BitVec 32
  seed : BitVec 32
  pk : BitVec 32
  msg : BitVec 32
  len : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : VG.Proof.Ed25519.X86.SignCached.Lay)
abbrev OUT : Region := ⟨L.out.setWidth 64, 64⟩
abbrev SEED : Region := ⟨L.seed.setWidth 64, 32⟩
abbrev PK : Region := ⟨L.pk.setWidth 64, 32⟩
abbrev MSG : Region := ⟨L.msg.setWidth 64, L.len.toNat⟩
abbrev SCR : Region := ⟨L.scr.setWidth 64, 8192⟩
abbrev ARGS : Region := ⟨L.E.setWidth 64 + 260, 24⟩
abbrev RET : Region := ⟨L.E.setWidth 64 + 256, 4⟩
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := Whole.STK L.E
def inputs : List Region := [L.SEED, L.PK, L.MSG, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : BitVec 32 :=
  match j with | 0 => L.out | 1 => L.seed | 2 => L.pk | 3 => L.msg | 4 => L.len | _ => L.scr

structure Ok : Prop where
  below : 24 ≤ L.E.toNat
  top : L.E.toNat + 284 ≤ 2 ^ 32
  os : ∀ r ∈ L.inputs, L.OUT.Disjoint r
  oc : L.OUT.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ro : L.RET.Disjoint L.OUT
  no : L.out.toNat + 64 ≤ 2 ^ 32
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.STK.Disjoint r
  rs : ∀ r ∈ L.inputs, L.RET.Disjoint r
  kc : L.STK.Disjoint L.SCR
  rc : L.RET.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 32
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  ns : L.seed.toNat + 32 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

abbrev Ctx (L : VG.Proof.Ed25519.X86.SignCached.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

namespace Ctx
variable {L : VG.Proof.Ed25519.X86.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem input_bytes (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t) (hL : L.Ok)
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

theorem arg_word (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 6) :
    t.mem.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 =
      m₀.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 260) (k := 24) (by omega) (by omega) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl | rfl
    · exact (hL.os _ ha).symm
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm

end Ctx
end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

def Arguments (L : VG.Proof.Ed25519.X86.SignCached.Lay) (m : Mem) : Prop :=
  ∀ j < 6, m.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 = L.value j

def value (L : VG.Proof.Ed25519.X86.SignCached.Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

def OutArgs (L : VG.Proof.Ed25519.X86.SignCached.Lay) (vs : List Value) (s : State) : Prop :=
  ∀ j (hj : j < vs.length), s.mem.readW (addr L.E (4 * j)) 32 = VG.Proof.Ed25519.X86.SignCached.value L (vs[j]'hj)

variable {L : VG.Proof.Ed25519.X86.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem Ctx.value (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.Arguments L m₀)
    {v : Value} (hv : Whole.valid 6 v) : Whole.value L.E s.mem v = VG.Proof.Ed25519.X86.SignCached.value L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    change j < 6 at hv
    simp only [Whole.value, SignCached.value]
    rw [addr_eq (by have := hL.top; omega), hc.arg_word hL hv, ha j hv]

theorem args_ok (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.Arguments L m₀)
    {vs : List Value} (hlen : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 6 v) :
    WP isa (.block (setup 0 vs)) s fun t => VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t ∧
      VG.Frame [⟨L.E.setWidth 64, 24⟩] s.mem t.mem ∧ VG.Proof.Ed25519.X86.SignCached.OutArgs L vs t := by
  refine WP.mono (Whole.Ctx.setup hc (by simpa using hL.top) ?_ (by omega) hv)
    fun t ⟨ht, hf, hvals⟩ => ⟨ht, hf, fun j hj => ?_⟩
  · intro j hj
    refine ⟨L.ARGS, ?_, ?_⟩
    · rw [hc.rd]; exact List.mem_append_left _ (by simp [Lay.inputs])
    · rw [addr_eq (by have := hL.top; omega)]
      exact Offset.contains _ (e := 260) (k := 24) (by omega) (by omega) (by decide)
  · simpa only [Nat.zero_add, hc.value hL ha (hv _ (List.getElem_mem _))] using hvals j hj

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.Hash`. -/
section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.PublicKey (callWith)

variable {L : VG.Proof.Ed25519.X86.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashSpace (h : L.Ok) : Whole.HashSpace L.E L.scr :=
  ⟨h.below, by have := h.top; omega, h.nc, h.kc⟩

theorem shaWithin (L : VG.Proof.Ed25519.X86.SignCached.Lay) : Whole.Within (Whole.SHA L.scr) L.SCR :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩

theorem workWithin (h : L.Ok) : Whole.Within (Whole.WORK L.scr) L.SCR :=
  ⟨192, (VG.Proof.Ed25519.X86.SignCached.hashSpace h).work_addr, by change 192 + 272 ≤ 8192; decide⟩

theorem argsWithin (L : VG.Proof.Ed25519.X86.SignCached.Lay) {n : Nat} (hn : n ≤ 256) :
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

def hashWrites (L : VG.Proof.Ed25519.X86.SignCached.Lay) : List Region :=
  [L.SCR, ⟨L.E.setWidth 64, 24⟩, below L.E 24, ⟨L.E.setWidth 64 + 192, 64⟩]

theorem setup_frame {m m' : Mem} (h : VG.Frame [⟨L.E.setWidth 64, 24⟩] m m') : VG.Frame (VG.Proof.Ed25519.X86.SignCached.hashWrites L) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp [VG.Proof.Ed25519.X86.SignCached.hashWrites], fun _ h => h⟩

theorem hash_frame {m m' : Mem} {wr : List Region}
    (h : VG.Frame (wr ++ [below L.E 24]) m m')
    (hw : ∀ r ∈ wr, Whole.Within r L.SCR ∨ Whole.Within r ⟨L.E.setWidth 64 + 192, 64⟩) :
    VG.Frame (VG.Proof.Ed25519.X86.SignCached.hashWrites L) m m' := by
  refine h.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with h | h
    · exact ⟨_, by simp [VG.Proof.Ed25519.X86.SignCached.hashWrites], h.sub⟩
    · exact ⟨_, by simp [VG.Proof.Ed25519.X86.SignCached.hashWrites], h.sub⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp [VG.Proof.Ed25519.X86.SignCached.hashWrites], fun _ h => h⟩

theorem setup_repr (hL : L.Ok) {u : State}
    (hf : VG.Frame [⟨L.E.setWidth 64, 24⟩] s.mem u.mem) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (L.scr.setWidth 64) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := s.mem) ?_ hr
  intro i hi
  exact hf.bytes (R := Whole.SHA L.scr) (by
    rintro r hr; rw [List.mem_singleton.mp hr]
    exact ((VG.Proof.Ed25519.X86.SignCached.hashSpace hL).args_sha (n := 24) (by decide)).symm) (by change 192 ≤ 2 ^ 64; decide) hi

theorem OutArgs.slot {vs : List Value} {t : State} (h : VG.Proof.Ed25519.X86.SignCached.OutArgs L vs t) (hL : L.Ok)
    {j : Nat} (hj : j < vs.length) (hlen : vs.length ≤ 6) :
    Whole.slots L.E t j = VG.Proof.Ed25519.X86.SignCached.value L (vs[j]'hj) := by
  have e := h j hj
  rw [addr_eq (by have := hL.top; omega)] at e
  exact e

theorem init_step (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.Arguments L m₀) :
    WP isa Impl.Ed25519.X86.SignCached.init s fun t => VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t ∧
      VG.Frame (VG.Proof.Ed25519.X86.SignCached.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64) [] := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.SignCached.args_ok hc hL ha (vs := [.caller 5 0]) (by decide) (by simp [Whole.valid]))
    fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 : Whole.slots L.E u 0 = L.scr := by
    have hh := hs.slot hL (j := 0) (by decide) (by decide)
    change Whole.slots L.E u 0 = L.scr + BitVec.ofNat 32 0 at hh
    simpa only [BitVec.add_zero] using hh
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have cov := VG.Proof.Ed25519.X86.SignCached.hash_covers (L := L) (rs := Whole.initRd L.E ++ Whole.initWr L.scr) (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered (VG.Proof.Ed25519.X86.SignCached.shaWithin L))
  have ws := VG.Proof.Ed25519.X86.SignCached.hash_writes (L := L) (rs := Whole.initWr L.scr) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (VG.Proof.Ed25519.X86.SignCached.shaWithin L))
  refine WP.mono (Whole.init_call hu H.below (Whole.init_pre hu.esp H a0) cov ws
    ((Whole.call_arg hu.esp H.below H.frameFit (by decide)).trans a0)) fun t ⟨ht, hft, hr⟩ =>
    ⟨ht, (VG.Proof.Ed25519.X86.SignCached.setup_frame hf).trans (VG.Proof.Ed25519.X86.SignCached.hash_frame hft ?_), hr⟩
  intro r hr; rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Ed25519.X86.SignCached.shaWithin L)

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.Calls`. -/
section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

def fp (L : VG.Proof.Ed25519.X86.SignCached.Lay) (d : Nat) : BitVec 32 := L.E + BitVec.ofNat 32 d
def field (L : VG.Proof.Ed25519.X86.SignCached.Lay) (d : Nat) : Region := ⟨(VG.Proof.Ed25519.X86.SignCached.fp L d).setWidth 64, 32⟩

variable {L : VG.Proof.Ed25519.X86.SignCached.Lay}

theorem fp_addr (hL : L.Ok) {d : Nat} (hd : d ≤ 256) :
    (VG.Proof.Ed25519.X86.SignCached.fp L d).setWidth 64 = L.E.setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hL.top; omega)

theorem fieldWithin (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) : Whole.Within (VG.Proof.Ed25519.X86.SignCached.field L d) L.FR :=
  ⟨d, VG.Proof.Ed25519.X86.SignCached.fp_addr hL (by omega), by exact hd⟩

theorem field_sub (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) : Region.Sub (VG.Proof.Ed25519.X86.SignCached.field L d) L.STK :=
  fun p hp => Whole.frame_sub L.E p ((VG.Proof.Ed25519.X86.SignCached.fieldWithin hL hd).sub p hp)

theorem field_fit (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) : (VG.Proof.Ed25519.X86.SignCached.fp L d).toNat + 32 ≤ 2 ^ 32 := by
  have he := hL.top
  simp only [VG.Proof.Ed25519.X86.SignCached.fp, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem field_ce {g : Reg → BitVec 32} {m₀ : Mem} {s : State} (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s)
    (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt s.callEntry.mem ((VG.Proof.Ed25519.X86.SignCached.fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.fp L d).setWidth 64) 32 := by
  apply Whole.callEntry_bytes (r := VG.Proof.Ed25519.X86.SignCached.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  change Region.Disjoint ⟨(VG.Proof.Ed25519.X86.SignCached.fp L d).setWidth 64, 32⟩ ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩
  rw [hc.esp, VG.Proof.Ed25519.X86.SignCached.fp_addr hL (by omega), Taint.sub_setWidth (m := 4) (by have := hL.below; omega)]
  exact Offset.disjoint_below _ (n := 4) (d := d) (k := 32) (by omega)

theorem field_setup {m m' : Mem} (hL : L.Ok) (hf : VG.Frame [⟨L.E.setWidth 64, 24⟩] m m')
    {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt m' ((VG.Proof.Ed25519.X86.SignCached.fp L d).setWidth 64) 32 = Spec.Ed25519.bytesAt m ((VG.Proof.Ed25519.X86.SignCached.fp L d).setWidth 64) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := VG.Proof.Ed25519.X86.SignCached.field L d) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr; rw [List.mem_singleton.mp hr]
  change Region.Disjoint ⟨(VG.Proof.Ed25519.X86.SignCached.fp L d).setWidth 64, 32⟩ _
  rw [VG.Proof.Ed25519.X86.SignCached.fp_addr hL (by omega)]
  exact Offset.disjoint_base _ (d := d) (n := 32) (k := 24) hd (by omega)

def primitiveWrites (L : VG.Proof.Ed25519.X86.SignCached.Lay) (out : Region) : List Region :=
  [out, L.SCR, ⟨L.E.setWidth 64, 24⟩, below L.E 24]

theorem primitive_frame {m m' m'' : Mem} {out : Region}
    (hf : VG.Frame [⟨L.E.setWidth 64, 24⟩] m m')
    (hc : VG.Frame ([out, L.SCR] ++ [below L.E 24]) m' m'') : VG.Frame (VG.Proof.Ed25519.X86.SignCached.primitiveWrites L out) m m'' := by
  refine (hf.sub ?_).trans (hc.sub ?_)
  · rintro r hr; rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp [VG.Proof.Ed25519.X86.SignCached.primitiveWrites], fun _ h => h⟩
  · intro r hr
    refine ⟨r, ?_, fun _ h => h⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [VG.Proof.Ed25519.X86.SignCached.primitiveWrites]

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.Base`. -/
section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
open VG.Impl.Ed25519.X86 (scalarBase)
open VG.Impl.Ed25519.X86.PublicKey (callWith)

def baseRd (L : VG.Proof.Ed25519.X86.SignCached.Lay) : List Region := [VG.Proof.Ed25519.X86.SignCached.field L 96, ⟨L.E.setWidth 64, 12⟩]
def baseOut (L : VG.Proof.Ed25519.X86.SignCached.Lay) : Region := ⟨L.out.setWidth 64, 32⟩
def baseWr (L : VG.Proof.Ed25519.X86.SignCached.Lay) : List Region := [VG.Proof.Ed25519.X86.SignCached.baseOut L, L.SCR]
def BaseArgs (L : VG.Proof.Ed25519.X86.SignCached.Lay) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.out ∧ Whole.slots L.E t 1 = VG.Proof.Ed25519.X86.SignCached.fp L 96 ∧ Whole.slots L.E t 2 = L.scr

theorem base_nosp : NoSp scalarBase := NoSp.of_all (by lit_decide)
theorem base_stack : stackUse scalarBase = 0 := by lit_decide

variable {L : VG.Proof.Ed25519.X86.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem base_pre (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.BaseArgs L s) :
    scalarBaseLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.X86.SignCached.baseRd L) (VG.Proof.Ed25519.X86.SignCached.baseWr L)) := by
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  have a0 := (ca (j := 0) (by decide)).trans ha.1
  have a1 := (ca (j := 1) (by decide)).trans ha.2.1
  have a2 := (ca (j := 2) (by decide)).trans ha.2.2
  have ae := Whole.arg_base hc.esp (VG.Proof.Ed25519.X86.SignCached.baseRd L) (VG.Proof.Ed25519.X86.SignCached.baseWr L)
  have ret : Region.Sub ⟨(L.E - 4).setWidth 64, 4⟩ L.STK := Whole.below_sub_stack H.below (by decide)
  have args : Region.Sub ⟨L.E.setWidth 64, 12⟩ L.STK :=
    fun p hp => Whole.frame_sub L.E p (Region.sub_prefix (by decide) p hp)
  have out : Region.Sub (VG.Proof.Ed25519.X86.SignCached.baseOut L) L.OUT := Region.sub_prefix (by decide)
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, a0, a1, a2, ae]
  refine ⟨rfl, rfl, hL.oc.sub_left out, hL.kc.sub_left (VG.Proof.Ed25519.X86.SignCached.field_sub hL (by decide)),
    (hL.ko.sub_left args).sub_right out, hL.kc.sub_left args,
    (hL.ko.sub_left ret).sub_right out, hL.kc.sub_left ret,
    by have := hL.no; omega, VG.Proof.Ed25519.X86.SignCached.field_fit hL (by decide), hL.nc, ?_⟩
  change (L.E - BitVec.ofNat 32 4).toNat + 16 ≤ 2 ^ 32
  rw [sub_toNat (k := 4) (by have := hL.below; omega)]
  have := hL.top; omega

theorem base_call (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.BaseArgs L s) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) s fun t => VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.X86.SignCached.baseWr L ++ [below L.E 24]) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.fp L 96).setWidth 64) 32) := by
  have cov := VG.Proof.Ed25519.X86.SignCached.hash_covers (L := L) (rs := VG.Proof.Ed25519.X86.SignCached.baseRd L ++ VG.Proof.Ed25519.X86.SignCached.baseWr L) (by
    simp only [VG.Proof.Ed25519.X86.SignCached.baseRd, VG.Proof.Ed25519.X86.SignCached.baseWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.fieldWithin hL (by decide))
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [VG.Proof.Ed25519.X86.SignCached.baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ VG.Proof.Ed25519.X86.SignCached.baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [VG.Proof.Ed25519.X86.SignCached.baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [VG.Proof.Ed25519.X86.SignCached.baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  with_reducible
    refine Whole.call_ok hc hL.below scalarBase_ok VG.Proof.Ed25519.X86.SignCached.base_nosp (by rw [VG.Proof.Ed25519.X86.SignCached.base_stack]; decide)
      (VG.Proof.Ed25519.X86.SignCached.base_pre hc hL ha) cov ws fun t ht hf _ post => ⟨ht, hf, ?_⟩
  obtain ⟨s₂, hm, _, hp⟩ := post
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  change Spec.Ed25519.bytesAt s₂.mem ((arg s.callEntry 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 32) at hp
  rw [hm, (ca (by decide)).trans ha.1, (ca (by decide)).trans ha.2.1] at hp
  rw [hp, VG.Proof.Ed25519.X86.SignCached.field_ce hc hL (by decide)]

theorem base_step (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith baseArgs "vg_ed25519_scalar_base" scalarBase) s fun t => VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t ∧
      Frame (VG.Proof.Ed25519.X86.SignCached.primitiveWrites L (VG.Proof.Ed25519.X86.SignCached.baseOut L)) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.fp L 96).setWidth 64) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.SignCached.args_ok hc hL ha (vs := [.caller 0 0, .frame 96, .caller 5 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by decide) (by decide)
  have a1 := hs.slot hL (j := 1) (by decide) (by decide)
  have a2 := hs.slot hL (j := 2) (by decide) (by decide)
  change Whole.slots L.E u 0 = L.out + 0#32 at a0
  change Whole.slots L.E u 2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a0 a2
  refine WP.mono (VG.Proof.Ed25519.X86.SignCached.base_call hu hL ⟨a0, a1, a2⟩) fun t ⟨ht, hft, hp⟩ =>
    ⟨ht, VG.Proof.Ed25519.X86.SignCached.primitive_frame hf hft, ?_⟩
  rw [hp, VG.Proof.Ed25519.X86.SignCached.field_setup hL hf (by decide) (by decide)]

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashUpdate`. -/
section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

structure Input (L : VG.Proof.Ed25519.X86.SignCached.Lay) (p n : BitVec 32) : Prop where
  cover : Whole.Within ⟨p.setWidth 64, n.toNat⟩ L.FR ∨
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p.setWidth 64, n.toNat⟩ R
  scratch : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ L.SCR
  below : (below L.E 24).Disjoint ⟨p.setWidth 64, n.toNat⟩
  args : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ ⟨L.E.setWidth 64, 24⟩
  fit : p.toNat + n.toNat ≤ 2 ^ 32

def UpdateArgs (L : VG.Proof.Ed25519.X86.SignCached.Lay) (c p n : BitVec 32) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 1 = c ∧ Whole.slots L.E t 2 = 0 ∧
    Whole.slots L.E t 3 = p ∧ Whole.slots L.E t 4 = n ∧ Whole.slots L.E t 5 = L.scr + 192

variable {L : VG.Proof.Ed25519.X86.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_zero_high (x : BitVec 32) : (0#32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat]
  change 0 * 2 ^ 32 + x.toNat = x.toNat % 2 ^ 64
  omega

theorem update_step (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.Arguments L m₀)
    {vs : List Value} (hlen : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 6 v)
    {c p n : BitVec 32} (hargs : ∀ t, VG.Proof.Ed25519.X86.SignCached.OutArgs L vs t → VG.Proof.Ed25519.X86.SignCached.UpdateArgs L c p n t)
    (hi : VG.Proof.Ed25519.X86.SignCached.Input L p n) {prev : List Byte} (hcount : c.toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.SignCached.update (setup 0 vs)) s fun t => VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t ∧
      VG.Frame (VG.Proof.Ed25519.X86.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.SignCached.args_ok hc hL ha hlen hv) fun u ⟨hu, hf, hs⟩ => ?_)
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hargs u hs
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have hp := Whole.update_pre hu.esp H a0 a3 a4 a5 hi.scratch hi.below hi.fit
  have cov := VG.Proof.Ed25519.X86.SignCached.hash_covers (L := L) (rs := Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hi.cover
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered (VG.Proof.Ed25519.X86.SignCached.shaWithin L)
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered (VG.Proof.Ed25519.X86.SignCached.workWithin hL))
  have ws := VG.Proof.Ed25519.X86.SignCached.hash_writes (L := L) (rs := Whole.hashWr L.scr) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (VG.Proof.Ed25519.X86.SignCached.shaWithin L)
    · exact .inr (VG.Proof.Ed25519.X86.SignCached.workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  have cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 prev.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), a1, a2]
    exact (VG.Proof.Ed25519.X86.SignCached.count_zero_high c).trans (congrArg (BitVec.ofNat 64) hcount)
  have hb : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ (below (u.gpr .esp) 4) := by
    rw [hu.esp]
    exact (hi.below.sub_left (below_sub (by decide) H.below)).symm
  have hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.update_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) (ca (by decide) |>.trans a4) cnt hbsha hb
    (VG.Proof.Ed25519.X86.SignCached.setup_repr hL hf hr)) fun t ⟨ht, hft, hrepr⟩ => ⟨ht, ?_, ?_⟩
  · refine (VG.Proof.Ed25519.X86.SignCached.setup_frame hf).trans (VG.Proof.Ed25519.X86.SignCached.hash_frame hft ?_)
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.shaWithin L)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.workWithin hL)
  · have same : Spec.Ed25519.bytesAt u.mem (p.setWidth 64) n.toNat =
        Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n.toNat := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      exact hf.bytes (R := ⟨p.setWidth 64, n.toNat⟩)
        (by rintro r hr; rw [List.mem_singleton.mp hr]; exact hi.args)
        (by have := n.isLt; change n.toNat ≤ 2 ^ 64; omega) (List.mem_range.mp hi')
    rw [same] at hrepr
    exact hrepr

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashFinalize`. -/
section

/-! Merged from `Proof.Ed25519.X86.SignCached.FinalizeArgs`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole VG.Impl.Ed25519.X86.SignCached

def FinArgs (L : VG.Proof.Ed25519.X86.SignCached.Lay) (count : BitVec 64) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 3 = L.E + 192 ∧
    Whole.slots L.E t 4 = L.scr + 192 ∧
    Whole.slots L.E t 2 ++ Whole.slots L.E t 1 = count

variable {L : VG.Proof.Ed25519.X86.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_keep {t u : State} (hf : VG.Frame [⟨L.E.setWidth 64 + 4, 8⟩] t.mem u.mem)
    {j : Nat} (hj : j = 0 ∨ j = 3 ∨ j = 4) : Whole.slots L.E u j = Whole.slots L.E t j := by
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  apply Offset.disjoint (e := 4) (k := 8)
  · rcases hj with rfl | rfl | rfl <;> decide
  · rcases hj with rfl | rfl | rfl <;> decide
  · decide

theorem count_frame {m m' : Mem} (hf : VG.Frame [⟨L.E.setWidth 64 + 4, 8⟩] m m') :
    VG.Frame [⟨L.E.setWidth 64, 24⟩] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (d := 4) (by decide)⟩

theorem finalizeArgs_ok (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.Arguments L m₀)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool) :
    WP isa (.block (finalizeArgs n b)) s fun t => VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t ∧
      VG.Frame [⟨L.E.setWidth 64, 24⟩] s.mem t.mem ∧
      VG.Proof.Ed25519.X86.SignCached.FinArgs L (BitVec.ofNat 64 ((if b then L.len.toNat else 0) + n)) t := by
  rw [finalizeArgs, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.SignCached.args_ok hc hL ha (vs := [.caller 5 0, .const n, .const 0, .frame 192, .caller 5 192])
    (by simp) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_
  have aa := hs.slot hL (j := 0) (by simp) (by simp)
  have ab := hs.slot hL (j := 1) (by simp) (by simp)
  have ac := hs.slot hL (j := 2) (by simp) (by simp)
  have ad := hs.slot hL (j := 3) (by simp) (by simp)
  have ae := hs.slot hL (j := 4) (by simp) (by simp)
  change Whole.slots L.E u 0 = L.scr + 0#32 at aa
  rw [BitVec.add_zero] at aa
  change Whole.slots L.E u 1 = BitVec.ofNat 32 n at ab
  change Whole.slots L.E u 2 = 0#32 at ac
  change Whole.slots L.E u 3 = L.E + 192 at ad
  change Whole.slots L.E u 4 = L.scr + 192 at ae
  cases b with
  | false =>
    refine WP.block_nil ⟨hu, hf, aa, ad, ae, ?_⟩
    rw [ac, ab]
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
    change (0#32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n
    rw [VG.Proof.Ed25519.X86.SignCached.count_zero_high, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  | true =>
    have hr : InRegions (u.rd ++ u.wr) (addr L.E 276) 4 := by
      refine ⟨L.ARGS, ?_, ?_⟩
      · rw [hu.rd]; simp [Lay.inputs]
      · rw [addr_eq (by have := hL.top; omega)]
        exact Offset.contains _ (e := 260) (k := 24) (d := 276) (n := 4) (by decide) (by decide) (by decide)
    have hx : u.mem.readW (addr L.E 276) 32 = L.len := by
      rw [addr_eq (by have := hL.top; omega)]
      exact (hu.arg_word hL (j := 4) (by decide)).trans (ha 4 (by decide))
    refine WP.mono (Whole.Ctx.count hu (index := 4) (n := n) (by have := hL.top; omega) hr hx)
      fun t ⟨ht, hft, hlo, hhi⟩ => ⟨ht, hf.trans (VG.Proof.Ed25519.X86.SignCached.count_frame hft),
        (VG.Proof.Ed25519.X86.SignCached.count_keep hft (.inl rfl)).trans aa,
        (VG.Proof.Ed25519.X86.SignCached.count_keep hft (.inr (.inl rfl))).trans ad,
        (VG.Proof.Ed25519.X86.SignCached.count_keep hft (.inr (.inr rfl))).trans ae, ?_⟩
    change (t.mem.readW (L.E.setWidth 64 + 8#64) 32 ++ t.mem.readW (L.E.setWidth 64 + 4#64) 32 : BitVec 64) = BitVec.ofNat 64 ((if true then L.len.toNat else 0) + n)
    change t.mem.readW (L.E.setWidth 64 + 8#64) 32 = _ at hhi
    change t.mem.readW (L.E.setWidth 64 + 4#64) 32 = _ at hlo
    rw [hhi, hlo]
    exact Whole.count_pair L.len n hn

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : VG.Proof.Ed25519.X86.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem digest_addr (hL : L.Ok) : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 :=
  addr_eq (x := L.E) (k := 192) (by have := hL.top; omega)

theorem digestWithin (hL : L.Ok) : Whole.Within ⟨(L.E + 192).setWidth 64, 64⟩ L.FR :=
  ⟨192, VG.Proof.Ed25519.X86.SignCached.digest_addr hL, by change 192 + 64 ≤ 256; decide⟩

theorem digest_below (hL : L.Ok) : (below L.E 24).Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ := by
  change Region.Disjoint ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
  rw [Taint.sub_setWidth hL.below, VG.Proof.Ed25519.X86.SignCached.digest_addr hL]
  exact (Offset.disjoint_below _ (n := 24) (d := 192) (k := 64) (by decide)).symm

theorem finalize_step (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.Arguments L m₀)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool) {msg : List Byte}
    (hlen : msg.length < 2 ^ 64) (hcount : (if b then L.len.toNat else 0) + n = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) msg) :
    WP isa (finalize n b) s fun t => VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t ∧ VG.Frame (VG.Proof.Ed25519.X86.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 msg := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.SignCached.finalizeArgs_ok hc hL ha n hn b) fun u ⟨hu, hf, a0, a3, a4, ac⟩ => ?_)
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega)]
    have := hL.top; omega
  have hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((VG.Proof.Ed25519.X86.SignCached.digestWithin hL).sub p hp))
  have hp := Whole.finalize_pre hu.esp H a0 a3 a4 hd (VG.Proof.Ed25519.X86.SignCached.digest_below hL) (by
    rw [VG.Proof.Ed25519.X86.SignCached.digest_addr hL]
    exact Offset.base_disjoint _ (k := 20) (e := 192) (n := 64) (by decide) (by decide)) fit
  have cov := VG.Proof.Ed25519.X86.SignCached.hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered (VG.Proof.Ed25519.X86.SignCached.shaWithin L)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.digestWithin hL)
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered (VG.Proof.Ed25519.X86.SignCached.workWithin hL))
  have ws := VG.Proof.Ed25519.X86.SignCached.hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (VG.Proof.Ed25519.X86.SignCached.shaWithin L)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.digestWithin hL)
    · exact .inr (VG.Proof.Ed25519.X86.SignCached.workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  have cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 msg.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), ac, hcount]
  have hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.finalize_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) cnt hbsha (VG.Proof.Ed25519.X86.SignCached.setup_repr hL hf hr) hlen)
    fun t ⟨ht, hft, hdigest⟩ => ⟨ht, ?_, ?_⟩
  · refine (VG.Proof.Ed25519.X86.SignCached.setup_frame hf).trans (VG.Proof.Ed25519.X86.SignCached.hash_frame hft ?_)
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.shaWithin L)
    · exact .inr ⟨0, by rw [VG.Proof.Ed25519.X86.SignCached.digest_addr hL]; simp, by change 0 + 64 ≤ 64; decide⟩
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.workWithin hL)
  · rw [VG.Proof.Ed25519.X86.SignCached.digest_addr hL] at hdigest
    exact hdigest

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.MulAdd`. -/
section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
open VG.Impl.Ed25519.X86 (scalarMulAdd)
open VG.Impl.Ed25519.X86.PublicKey (callWith)

def half (L : VG.Proof.Ed25519.X86.SignCached.Lay) : Region := ⟨(L.out + 32).setWidth 64, 32⟩
def mulRd (L : VG.Proof.Ed25519.X86.SignCached.Lay) : List Region := [VG.Proof.Ed25519.X86.SignCached.field L 96, VG.Proof.Ed25519.X86.SignCached.field L 128, VG.Proof.Ed25519.X86.SignCached.field L 32, ⟨L.E.setWidth 64, 20⟩]
def mulWr (L : VG.Proof.Ed25519.X86.SignCached.Lay) : List Region := [VG.Proof.Ed25519.X86.SignCached.half L, L.SCR]
def MulArgs (L : VG.Proof.Ed25519.X86.SignCached.Lay) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.out + 32 ∧ Whole.slots L.E t 1 = VG.Proof.Ed25519.X86.SignCached.fp L 96 ∧
    Whole.slots L.E t 2 = VG.Proof.Ed25519.X86.SignCached.fp L 128 ∧ Whole.slots L.E t 3 = VG.Proof.Ed25519.X86.SignCached.fp L 32 ∧ Whole.slots L.E t 4 = L.scr

theorem mul_nosp : NoSp scalarMulAdd := NoSp.of_all (by lit_decide)
theorem mul_stack : stackUse scalarMulAdd = 0 := by lit_decide

variable {L : VG.Proof.Ed25519.X86.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem half_addr (hL : L.Ok) : (L.out + 32).setWidth 64 = L.out.setWidth 64 + 32 :=
  addr_eq (x := L.out) (k := 32) (by have := hL.no; omega)

theorem halfWithin (hL : L.Ok) : Whole.Within (VG.Proof.Ed25519.X86.SignCached.half L) L.OUT :=
  ⟨32, VG.Proof.Ed25519.X86.SignCached.half_addr hL, by change 32 + 32 ≤ 64; decide⟩

theorem mul_pre (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.MulArgs L s) :
    scalarMulAddLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.X86.SignCached.mulRd L) (VG.Proof.Ed25519.X86.SignCached.mulWr L)) := by
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  have a0 := (ca (j := 0) (by decide)).trans ha.1
  have a1 := (ca (j := 1) (by decide)).trans ha.2.1
  have a2 := (ca (j := 2) (by decide)).trans ha.2.2.1
  have a3 := (ca (j := 3) (by decide)).trans ha.2.2.2.1
  have a4 := (ca (j := 4) (by decide)).trans ha.2.2.2.2
  have ae := Whole.arg_base hc.esp (VG.Proof.Ed25519.X86.SignCached.mulRd L) (VG.Proof.Ed25519.X86.SignCached.mulWr L)
  have ret : Region.Sub ⟨(L.E - 4).setWidth 64, 4⟩ L.STK := Whole.below_sub_stack H.below (by decide)
  have args : Region.Sub ⟨L.E.setWidth 64, 20⟩ L.STK :=
    fun p hp => Whole.frame_sub L.E p (Region.sub_prefix (by decide) p hp)
  have out := (VG.Proof.Ed25519.X86.SignCached.halfWithin hL).sub
  simp only [scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, a0, a1, a2, a3, a4, ae]
  refine ⟨rfl, rfl, hL.oc.sub_left out, hL.kc.sub_left (VG.Proof.Ed25519.X86.SignCached.field_sub hL (d := 96) (by decide)),
    hL.kc.sub_left (VG.Proof.Ed25519.X86.SignCached.field_sub hL (d := 128) (by decide)), hL.kc.sub_left (VG.Proof.Ed25519.X86.SignCached.field_sub hL (d := 32) (by decide)),
    (hL.ko.sub_left args).sub_right out, hL.kc.sub_left args,
    (hL.ko.sub_left ret).sub_right out, hL.kc.sub_left ret, ?_,
    VG.Proof.Ed25519.X86.SignCached.field_fit hL (by decide), VG.Proof.Ed25519.X86.SignCached.field_fit hL (by decide), VG.Proof.Ed25519.X86.SignCached.field_fit hL (by decide), hL.nc, ?_⟩
  · have h := hL.no
    rw [BitVec.toNat_add, show (32 : BitVec 32).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  · change (L.E - BitVec.ofNat 32 4).toNat + 24 ≤ 2 ^ 32
    rw [sub_toNat (k := 4) (by have := hL.below; omega)]
    have := hL.top; omega

theorem mul_call (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.MulArgs L s) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t ∧
      VG.Frame (VG.Proof.Ed25519.X86.SignCached.mulWr L ++ [below L.E 24]) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem ((L.out + 32).setWidth 64) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.fp L 96).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.fp L 128).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.fp L 32).setWidth 64) 32) := by
  have cov := VG.Proof.Ed25519.X86.SignCached.hash_covers (L := L) (rs := VG.Proof.Ed25519.X86.SignCached.mulRd L ++ VG.Proof.Ed25519.X86.SignCached.mulWr L) (by
    simp only [VG.Proof.Ed25519.X86.SignCached.mulRd, VG.Proof.Ed25519.X86.SignCached.mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.fieldWithin hL (by decide))
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.fieldWithin hL (by decide))
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.fieldWithin hL (by decide))
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], VG.Proof.Ed25519.X86.SignCached.halfWithin hL⟩
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ VG.Proof.Ed25519.X86.SignCached.mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [VG.Proof.Ed25519.X86.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], VG.Proof.Ed25519.X86.SignCached.halfWithin hL⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  with_reducible
    refine Whole.call_ok hc hL.below scalarMulAdd_ok VG.Proof.Ed25519.X86.SignCached.mul_nosp (by rw [VG.Proof.Ed25519.X86.SignCached.mul_stack]; decide)
      (VG.Proof.Ed25519.X86.SignCached.mul_pre hc hL ha) cov ws fun t ht hf _ post => ⟨ht, hf, ?_⟩
  obtain ⟨s₂, hm, _, hp⟩ := post
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  change Spec.Ed25519.bytesAt s₂.mem ((arg s.callEntry 0).setWidth 64) 32 = Spec.Ed25519.scalarMulAdd
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 2).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 3).setWidth 64) 32) at hp
  rw [hm, (ca (by decide)).trans ha.1, (ca (by decide)).trans ha.2.1,
    (ca (by decide)).trans ha.2.2.1, (ca (by decide)).trans ha.2.2.2.1] at hp
  rw [VG.Proof.Ed25519.X86.SignCached.field_ce hc hL (d := 96) (by decide), VG.Proof.Ed25519.X86.SignCached.field_ce hc hL (d := 128) (by decide),
    VG.Proof.Ed25519.X86.SignCached.field_ce hc hL (d := 32) (by decide)] at hp
  exact hp

theorem mul_step (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ t ∧
      VG.Frame (VG.Proof.Ed25519.X86.SignCached.primitiveWrites L (VG.Proof.Ed25519.X86.SignCached.half L)) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64 + 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.fp L 96).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.fp L 128).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.fp L 32).setWidth 64) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.SignCached.args_ok hc hL ha (vs := [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by decide) (by decide)
  have a1 := hs.slot hL (j := 1) (by decide) (by decide)
  have a2 := hs.slot hL (j := 2) (by decide) (by decide)
  have a3 := hs.slot hL (j := 3) (by decide) (by decide)
  have a4 := hs.slot hL (j := 4) (by decide) (by decide)
  change Whole.slots L.E u 4 = L.scr + 0#32 at a4
  rw [BitVec.add_zero] at a4
  refine WP.mono (VG.Proof.Ed25519.X86.SignCached.mul_call hu hL ⟨a0, a1, a2, a3, a4⟩) fun t ⟨ht, hft, hp⟩ =>
    ⟨ht, VG.Proof.Ed25519.X86.SignCached.primitive_frame hf hft, ?_⟩
  rw [VG.Proof.Ed25519.X86.SignCached.half_addr hL, VG.Proof.Ed25519.X86.SignCached.field_setup hL hf (d := 96) (by decide) (by decide),
    VG.Proof.Ed25519.X86.SignCached.field_setup hL hf (d := 128) (by decide) (by decide),
    VG.Proof.Ed25519.X86.SignCached.field_setup hL hf (d := 32) (by decide) (by decide)] at hp
  exact hp

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.CTReady`. -/
section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : VG.Proof.Ed25519.X86.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def init_ready (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok)
    (a0 : Whole.slots L.E s 0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initX86 Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have cov := VG.Proof.Ed25519.X86.SignCached.hash_covers (L := L) (rs := Whole.initRd L.E ++ Whole.initWr L.scr) (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered (VG.Proof.Ed25519.X86.SignCached.shaWithin L))
  have ws := VG.Proof.Ed25519.X86.SignCached.hash_writes (L := L) (rs := Whole.initWr L.scr) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (VG.Proof.Ed25519.X86.SignCached.shaWithin L))
  exact ⟨_, _, Whole.init_pre hc.esp H a0, cov, ws⟩

def update_ready (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) {c p n : BitVec 32}
    (hi : VG.Proof.Ed25519.X86.SignCached.Input L p n) (ha : VG.Proof.Ed25519.X86.SignCached.UpdateArgs L c p n s) :
    Whole.CallReady Proof.Sha512.updateX86 L.E L.inputs L.outputs s := by
  obtain ⟨a0, _, _, a3, a4, a5⟩ := ha
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have hp := Whole.update_pre hc.esp H a0 a3 a4 a5 hi.scratch hi.below hi.fit
  have cov := VG.Proof.Ed25519.X86.SignCached.hash_covers (L := L) (rs := Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hi.cover
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered (VG.Proof.Ed25519.X86.SignCached.shaWithin L)
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered (VG.Proof.Ed25519.X86.SignCached.workWithin hL))
  have ws := VG.Proof.Ed25519.X86.SignCached.hash_writes (L := L) (rs := Whole.hashWr L.scr) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (VG.Proof.Ed25519.X86.SignCached.shaWithin L)
    · exact .inr (VG.Proof.Ed25519.X86.SignCached.workWithin hL))
  exact ⟨_, _, hp, cov, ws⟩

def finalize_ready (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) {count : BitVec 64}
    (ha : VG.Proof.Ed25519.X86.SignCached.FinArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeX86 L.E L.inputs L.outputs s := by
  obtain ⟨a0, a3, a4, _⟩ := ha
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega)]
    have := hL.top; omega
  have hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((VG.Proof.Ed25519.X86.SignCached.digestWithin hL).sub p hp))
  have hp := Whole.finalize_pre hc.esp H a0 a3 a4 hd (VG.Proof.Ed25519.X86.SignCached.digest_below hL) (by
    rw [VG.Proof.Ed25519.X86.SignCached.digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)) fit
  have cov := VG.Proof.Ed25519.X86.SignCached.hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered (VG.Proof.Ed25519.X86.SignCached.shaWithin L)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.digestWithin hL)
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered (VG.Proof.Ed25519.X86.SignCached.workWithin hL))
  have ws := VG.Proof.Ed25519.X86.SignCached.hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (VG.Proof.Ed25519.X86.SignCached.shaWithin L)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.digestWithin hL)
    · exact .inr (VG.Proof.Ed25519.X86.SignCached.workWithin hL))
  exact ⟨_, _, hp, cov, ws⟩

def reduce_ready (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok)
    {d : Nat} (hd : 24 ≤ d) (hd' : d + 32 ≤ 256)
    (a0 : Whole.slots L.E s 0 = L.E + BitVec.ofNat 32 d)
    (a1 : Whole.slots L.E s 1 = L.E + 192) (a2 : Whole.slots L.E s 2 = L.scr) :
    Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have H := VG.Proof.Ed25519.X86.SignCached.hashSpace hL
  have wo : Whole.Within ⟨(L.E + BitVec.ofNat 32 d).setWidth 64, 32⟩ L.FR :=
    ⟨d, Whole.frame_addr H.frameFit (by omega), hd'⟩
  have cov : Covers (Whole.reduceRd L.E ++ Whole.reduceWr L.E L.scr d)
      (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.X86.SignCached.hash_covers
    simp only [Whole.reduceRd, Whole.reduceWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.digestWithin hL)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact .inl wo
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered ⟨0, by simp, by simp⟩
  have ws : ∀ r ∈ Whole.reduceWr L.E L.scr d,
      Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.X86.SignCached.hash_writes
    simp only [Whole.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl wo
    · exact .inr ⟨0, by simp, by simp⟩
  exact ⟨_, _, Whole.reduce_pre hc H hd hd' a0 a1 a2, cov, ws⟩

def base_ready (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.BaseArgs L s) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs s := by
  have cov := VG.Proof.Ed25519.X86.SignCached.hash_covers (L := L) (rs := VG.Proof.Ed25519.X86.SignCached.baseRd L ++ VG.Proof.Ed25519.X86.SignCached.baseWr L) (by
    simp only [VG.Proof.Ed25519.X86.SignCached.baseRd, VG.Proof.Ed25519.X86.SignCached.baseWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.fieldWithin hL (by decide))
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [VG.Proof.Ed25519.X86.SignCached.baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ VG.Proof.Ed25519.X86.SignCached.baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [VG.Proof.Ed25519.X86.SignCached.baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [VG.Proof.Ed25519.X86.SignCached.baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  exact ⟨_, _, VG.Proof.Ed25519.X86.SignCached.base_pre hc hL ha, cov, ws⟩

def mul_ready (hc : VG.Proof.Ed25519.X86.SignCached.Ctx L g m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.X86.SignCached.MulArgs L s) :
    Whole.CallReady scalarMulAddLocal L.E L.inputs L.outputs s := by
  have cov := VG.Proof.Ed25519.X86.SignCached.hash_covers (L := L) (rs := VG.Proof.Ed25519.X86.SignCached.mulRd L ++ VG.Proof.Ed25519.X86.SignCached.mulWr L) (by
    simp only [VG.Proof.Ed25519.X86.SignCached.mulRd, VG.Proof.Ed25519.X86.SignCached.mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.fieldWithin hL (by decide))
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.fieldWithin hL (by decide))
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.fieldWithin hL (by decide))
    · exact .inl (VG.Proof.Ed25519.X86.SignCached.argsWithin L (by decide))
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], VG.Proof.Ed25519.X86.SignCached.halfWithin hL⟩
    · exact VG.Proof.Ed25519.X86.SignCached.scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ VG.Proof.Ed25519.X86.SignCached.mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [VG.Proof.Ed25519.X86.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], VG.Proof.Ed25519.X86.SignCached.halfWithin hL⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  exact ⟨_, _, VG.Proof.Ed25519.X86.SignCached.mul_pre hc hL ha, cov, ws⟩

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.Entry`. -/
section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

def signRd (s : State) : List Region :=
  [⟨(VG.X86.arg s 1).setWidth 64, 32⟩, ⟨(VG.X86.arg s 2).setWidth 64, 32⟩,
    ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩, ⟨argAddr s 0, 24⟩]
def signWr (s : State) : List Region :=
  [⟨(VG.X86.arg s 0).setWidth 64, 64⟩, ⟨(VG.X86.arg s 5).setWidth 64, 8192⟩]

def signCachedLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(VG.X86.arg s 0).setWidth 64, 64⟩
    let seed : Region := ⟨(VG.X86.arg s 1).setWidth 64, 32⟩
    let pk : Region := ⟨(VG.X86.arg s 2).setWidth 64, 32⟩
    let msg : Region := ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩
    let scr : Region := ⟨(VG.X86.arg s 5).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = VG.Proof.Ed25519.X86.SignCached.signRd s ∧ s.wr = VG.Proof.Ed25519.X86.SignCached.signWr s ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint seed ∧ ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (VG.X86.arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat + (VG.X86.arg s 4).toNat ≤ 2 ^ 32 ∧
      (VG.X86.arg s 5).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      Spec.Ed25519.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((VG.X86.arg s 1).setWidth 64) 32)
  post s t := Spec.Ed25519.bytesAt t.mem ((VG.X86.arg s 0).setWidth 64) 64 = Spec.Ed25519.sign
    (Spec.Ed25519.bytesAt s.mem ((VG.X86.arg s 1).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.mem ((VG.X86.arg s 3).setWidth 64) (VG.X86.arg s 4).toNat)
  pub s t := s.gpr .esp = t.gpr .esp ∧ VG.X86.arg s 0 = VG.X86.arg t 0 ∧ VG.X86.arg s 1 = VG.X86.arg t 1 ∧
    VG.X86.arg s 2 = VG.X86.arg t 2 ∧ VG.X86.arg s 3 = VG.X86.arg t 3 ∧ VG.X86.arg s 4 = VG.X86.arg t 4 ∧ VG.X86.arg s 5 = VG.X86.arg t 5

def lay (s : State) : VG.Proof.Ed25519.X86.SignCached.Lay :=
  ⟨VG.X86.arg s 0, VG.X86.arg s 1, VG.X86.arg s 2, VG.X86.arg s 3, VG.X86.arg s 4, VG.X86.arg s 5, s.gpr .esp - BitVec.ofNat 32 256⟩

theorem entry_bounds {s : State} (h : signCachedLocal.pre s) :
    280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, ht, _⟩ := h
  exact ⟨hb, ht⟩

theorem entry_key {s : State} (h : signCachedLocal.pre s) :
    Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.lay s).pk.setWidth 64) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((VG.Proof.Ed25519.X86.SignCached.lay s).seed.setWidth 64) 32) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk⟩ := h
  exact hk

theorem lay_base {s : State} (h : signCachedLocal.pre s) :
    (VG.Proof.Ed25519.X86.SignCached.lay s).E.setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 :=
  Taint.sub_setWidth (by have := (VG.Proof.Ed25519.X86.SignCached.entry_bounds h).1; omega)

theorem lay_args {s : State} (h : signCachedLocal.pre s) :
    (VG.Proof.Ed25519.X86.SignCached.lay s).ARGS = ⟨argAddr s 0, 24⟩ := by
  rw [Lay.ARGS, VG.Proof.Ed25519.X86.SignCached.lay_base h]
  have ha : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    addr_eq (by have := (VG.Proof.Ed25519.X86.SignCached.entry_bounds h).2; omega)
  rw [ha]
  congr 1
  change _ - 256#64 + 260#64 = _ + 4#64
  rw [show BitVec.ofNat 64 260 = BitVec.ofNat 64 256 + BitVec.ofNat 64 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem lay_ret {s : State} (h : signCachedLocal.pre s) :
    (VG.Proof.Ed25519.X86.SignCached.lay s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  rw [Lay.RET, VG.Proof.Ed25519.X86.SignCached.lay_base h]
  change (⟨(s.gpr .esp).setWidth 64 - 256#64 + 256#64, 4⟩ : Region) = _
  rw [BitVec.sub_add_cancel]

theorem lay_stack {s : State} (h : signCachedLocal.pre s) :
    (VG.Proof.Ed25519.X86.SignCached.lay s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩ := by
  rw [Lay.STK, Whole.STK, VG.Proof.Ed25519.X86.SignCached.lay_base h, BitVec.sub_sub]
  rfl

theorem lay_ok {s : State} (h : signCachedLocal.pre s) : (VG.Proof.Ed25519.X86.SignCached.lay s).Ok := by
  have h₀ := h
  obtain ⟨_, _, os, op, om, oa, oc, ko, ro, sc, pc, mc, ac, rs, rp, rm, rc,
    ks, kp, km, kc, no, ns, np, nm, nc, nb, na, _⟩ := h₀
  have top : (VG.Proof.Ed25519.X86.SignCached.lay s).E.toNat + 284 ≤ 2 ^ 32 := by
    change (s.gpr .esp - BitVec.ofNat 32 256).toNat + 284 ≤ _
    rw [sub_toNat (by omega)]
    omega
  refine ⟨?_, top, ?_, oc, ?_, ?_, no, ?_, ?_, ?_, ?_, ?_, np, nm, ns, nc⟩
  · change 24 ≤ (s.gpr .esp - BitVec.ofNat 32 256).toNat
    rw [sub_toNat (by omega)]
    omega
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact os
    · exact op
    · exact om
    · rw [VG.Proof.Ed25519.X86.SignCached.lay_args h]; exact oa
  · rw [VG.Proof.Ed25519.X86.SignCached.lay_stack h]; exact ko
  · rw [VG.Proof.Ed25519.X86.SignCached.lay_ret h]; exact ro
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sc
    · exact pc
    · exact mc
    · rw [VG.Proof.Ed25519.X86.SignCached.lay_args h]; exact ac
  · intro r hr
    rw [VG.Proof.Ed25519.X86.SignCached.lay_stack h]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ks
    · exact kp
    · exact km
    · rw [Lay.ARGS, VG.Proof.Ed25519.X86.SignCached.lay_base h]
      have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 + 260 =
          (s.gpr .esp).setWidth 64 + 4 := by
        change _ - 256#64 + 260#64 = _ + 4#64
        rw [show (260#64) = 256#64 + 4#64 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [e]
      exact Offset.disjoint_below_above _ (by decide)
  · intro r hr
    rw [VG.Proof.Ed25519.X86.SignCached.lay_ret h]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact rs
    · exact rp
    · exact rm
    · rw [Lay.ARGS, VG.Proof.Ed25519.X86.SignCached.lay_base h]
      have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 + 260 =
          (s.gpr .esp).setWidth 64 + 4 := by
        change _ - 256#64 + 260#64 = _ + 4#64
        rw [show (260#64) = 256#64 + 4#64 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [e]
      exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  · rw [VG.Proof.Ed25519.X86.SignCached.lay_stack h]; exact kc
  · rw [VG.Proof.Ed25519.X86.SignCached.lay_ret h]; exact rc

theorem lay_arguments {s : State} (h : signCachedLocal.pre s) : VG.Proof.Ed25519.X86.SignCached.Arguments (VG.Proof.Ed25519.X86.SignCached.lay s) s.mem := by
  intro j hj
  have hb := VG.Proof.Ed25519.X86.SignCached.lay_ok h
  have e : (VG.Proof.Ed25519.X86.SignCached.lay s).E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j) = argAddr s j := by
    rw [← addr_eq (by have := hb.top; omega)]
    simp only [addr, VG.Proof.Ed25519.X86.SignCached.lay, argAddr]
    rw [show 260 + 4 * j = 256 + (4 + 4 * j) by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [e]
  change VG.X86.arg s j = (VG.Proof.Ed25519.X86.SignCached.lay s).value j
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem push_ctx {s : State} (h : signCachedLocal.pre s) :
    VG.Proof.Ed25519.X86.SignCached.Ctx (VG.Proof.Ed25519.X86.SignCached.lay s) s.gpr s.mem (pushed (List.replicate 64 .eax) s) := by
  have hn := (VG.Proof.Ed25519.X86.SignCached.entry_bounds h).1
  have hf := pushed_frame (s := s) (rs := List.replicate 64 .eax) (by simp)
    (by simp only [List.length_replicate]; omega)
  refine ⟨?_, ?_, ?_, fun r _ hn => pushed_gpr _ _ hn, ?_⟩
  · rw [pushed_rd, h.1]
    rw [Lay.inputs, VG.Proof.Ed25519.X86.SignCached.lay_args h]
    rfl
  · rw [pushed_wr, h.2.1]
    simp only [List.length_replicate, Whole.FR, Lay.outputs, Lay.SCR, VG.Proof.Ed25519.X86.SignCached.lay, VG.Proof.Ed25519.X86.SignCached.signWr]
  · rw [pushed_esp, List.length_replicate]
    rfl
  · refine Frame.sub hf fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine ⟨(VG.Proof.Ed25519.X86.SignCached.lay s).STK, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [VG.Proof.Ed25519.X86.SignCached.lay_stack h, ← Taint.sub_setWidth hn]
    exact below_sub (by simp) hn

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashInputs`. -/
section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : VG.Proof.Ed25519.X86.SignCached.Lay}

theorem update_args {t : State} (hL : L.Ok) (c : Nat) (p n : Value)
    (h : VG.Proof.Ed25519.X86.SignCached.OutArgs L [.caller 5 0, .const c, .const 0, p, n, .caller 5 192] t) :
    VG.Proof.Ed25519.X86.SignCached.UpdateArgs L (BitVec.ofNat 32 c) (VG.Proof.Ed25519.X86.SignCached.value L p) (VG.Proof.Ed25519.X86.SignCached.value L n) t := by
  have h0 := h.slot hL (j := 0) (by simp) (by simp)
  have h1 := h.slot hL (j := 1) (by simp) (by simp)
  have h2 := h.slot hL (j := 2) (by simp) (by simp)
  have h3 := h.slot hL (j := 3) (by simp) (by simp)
  have h4 := h.slot hL (j := 4) (by simp) (by simp)
  have h5 := h.slot hL (j := 5) (by simp) (by simp)
  change Whole.slots L.E t 0 = L.scr + 0#32 at h0
  rw [BitVec.add_zero] at h0
  exact ⟨h0, h1, h2, h3, h4, h5⟩

theorem Input.external {p n : BitVec 32}
    (hc : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p.setWidth 64, n.toNat⟩ R)
    (hs : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ L.SCR)
    (hk : L.STK.Disjoint ⟨p.setWidth 64, n.toNat⟩)
    (hL : L.Ok) (hf : p.toNat + n.toNat ≤ 2 ^ 32) : VG.Proof.Ed25519.X86.SignCached.Input L p n :=
  ⟨.inr hc, hs, hk.sub_left (Whole.below_sub_stack hL.below (by decide)),
    (hk.sub_left (fun a ha => Whole.frame_sub L.E a (Region.sub_prefix (by decide : 24 ≤ 256) a ha))).symm, hf⟩

theorem seed_input (hL : L.Ok) : VG.Proof.Ed25519.X86.SignCached.Input L L.seed 32 :=
  Input.external ⟨L.SEED, by simp [Lay.inputs], 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    (hL.sc _ (by simp [Lay.inputs])) (hL.ks _ (by simp [Lay.inputs])) hL hL.ns

theorem key_input (hL : L.Ok) : VG.Proof.Ed25519.X86.SignCached.Input L L.pk 32 :=
  Input.external ⟨L.PK, by simp [Lay.inputs], 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    (hL.sc _ (by simp [Lay.inputs])) (hL.ks _ (by simp [Lay.inputs])) hL hL.np

theorem message_input (hL : L.Ok) : VG.Proof.Ed25519.X86.SignCached.Input L L.msg L.len :=
  Input.external ⟨L.MSG, by simp [Lay.inputs], 0, by simp, by simp⟩
    (hL.sc _ (by simp [Lay.inputs])) (hL.ks _ (by simp [Lay.inputs])) hL hL.nm

theorem point_input (hL : L.Ok) : VG.Proof.Ed25519.X86.SignCached.Input L L.out 32 :=
  Input.external ⟨L.OUT, by simp [Lay.outputs], 0, by simp, by change 0 + 32 ≤ 64; decide⟩
    (hL.oc.sub_left (Region.sub_prefix (by decide)))
    (hL.ko.sub_right (Region.sub_prefix (by decide))) hL (by change L.out.toNat + 32 ≤ 2 ^ 32; have := hL.no; omega)

theorem prefix_input (hL : L.Ok) : VG.Proof.Ed25519.X86.SignCached.Input L (L.E + 64) 32 := by
  have ea : (L.E + 64).setWidth 64 = L.E.setWidth 64 + 64 :=
    addr_eq (x := L.E) (k := 64) (by have := hL.top; omega)
  have hin : Whole.Within ⟨(L.E + 64).setWidth 64, (32 : BitVec 32).toNat⟩ L.FR :=
    ⟨64, ea, by change 64 + 32 ≤ 256; decide⟩
  refine ⟨.inl hin, hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p (hin.sub p hp)), ?_, ?_, ?_⟩
  · change Region.Disjoint ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
    rw [Taint.sub_setWidth hL.below, ea]
    exact (Offset.disjoint_below _ (n := 24) (d := 64) (k := 32) (by decide)).symm
  · rw [ea]
    exact Offset.disjoint_base _ (d := 64) (n := 32) (k := 24) (by decide) (by decide)
  · rw [BitVec.toNat_add, show (64 : BitVec 32).toNat = 64 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega)]
    have := hL.top; change L.E.toNat + 64 + 32 ≤ 2 ^ 32; omega

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.Prefix`. -/
section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey VG.Impl.Ed25519.X86.SignCached
open VG.Proof.Ed25519.X86.PublicKey (Step frame_word decode_words)

theorem copyWord_ok {s : State} {E : BitVec 32} {k : Nat} (he : s.gpr .esp = E)
    (hr : InRegions (s.rd ++ s.wr) (addr E (224 + 4 * k)) 4)
    (hw : InRegions s.wr (addr E (64 + 4 * k)) 4) :
    WP isa (.block (copyWord 224 64 k)) s fun t => VG.Proof.Ed25519.X86.PublicKey.Step s t ∧
      t.mem = s.mem.writeW (addr E (64 + 4 * k)) (s.mem.readW (addr E (224 + 4 * k)) 32) := by
  simp only [copyWord, VG.Impl.Ed25519.X86.PublicKey.at_]
  refine Wp.wp_ldm he hr fun u hu => ?_
  refine Wp.wp_stm (hu.other _ (by decide) |>.trans he) (hu.wr ▸ hw) fun t ht => WP.block_nil ?_
  refine ⟨⟨ht.rd.trans hu.rd, ht.wr.trans hu.wr, fun r h => by rw [ht.gpr]; exact hu.other r h⟩, ?_⟩
  rw [ht.mem, hu.mem, hu.gpr]

structure PrefixInv (E : BitVec 32) (s : State) (n : Nat) (t : State) : Prop where
  step : VG.Proof.Ed25519.X86.PublicKey.Step s t
  frame : VG.Frame [⟨E.setWidth 64 + BitVec.ofNat 64 64, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (addr E (64 + 4 * j)) 32 =
    s.mem.readW (addr E (224 + 4 * j)) 32

theorem copyPrefix_ok {s : State} {E : BitVec 32} (he : s.gpr .esp = E)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap (copyWord 224 64))) s (VG.Proof.Ed25519.X86.SignCached.PrefixInv E s n)
  | 0, _ => WP.block_nil ⟨Step.refl s, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.X86.SignCached.copyPrefix_ok he hf hw n (by omega_using [hn])) fun u hu => ?_
    have ur : InRegions (u.rd ++ u.wr) (addr E (224 + 4 * n)) 4 := by
      obtain ⟨r, hr, hc⟩ := frame_word hf (hu.step.wr ▸ hw) (d := 224 + 4 * n) (by omega_using [hn])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    have uw := frame_word hf (hu.step.wr ▸ hw) (d := 64 + 4 * n) (by omega_using [hn])
    refine WP.mono (VG.Proof.Ed25519.X86.SignCached.copyWord_ok (hu.step.esp.trans he) ur uw) fun t ⟨kt, mt⟩ => ?_
    have a224 : addr E (224 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (224 + 4 * n) :=
      addr_eq (by omega_using [hf, hn])
    have a32 : addr E (64 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (64 + 4 * n) :=
      addr_eq (by omega_using [hf, hn])
    have same : u.mem.readW (addr E (224 + 4 * n)) 32 = s.mem.readW (addr E (224 + 4 * n)) 32 := by
      rw [a224]
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega_using [hn]) (by omega_using [hn]) (by omega_using [hn])
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt, a32]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (a := addr E (64 + 4 * j)) (b := addr E (64 + 4 * n)) ?_ (by decide)]
        · exact hu.words j (by omega_using [hj, hjn])
        · rw [a32, addr_eq (by omega_using [hf, hj, hn])]
          exact Offset.sep _ (by omega_using [hj, hjn]) (by omega_using [hj, hn]) (by omega_using [hn])

theorem prefix_ok {s : State} {E : BitVec 32} (he : s.gpr .esp = E)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr) :
    WP isa (.block copyPrefix) s fun t => VG.Proof.Ed25519.X86.PublicKey.Step s t ∧
      VG.Frame [⟨E.setWidth 64 + 64, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (E.setWidth 64 + 64) 32 =
        Spec.Ed25519.bytesAt s.mem (E.setWidth 64 + 224) 32 := by
  refine WP.mono (VG.Proof.Ed25519.X86.SignCached.copyPrefix_ok he hf hw 8 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  have words : ∀ j < 8, t.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (64 + 4 * j)) 32 =
      s.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (224 + 4 * j)) 32 := by
    intro j hj
    have h := ht.words j hj
    rw [addr_eq (by omega_using [hf, hj]), addr_eq (by omega_using [hf, hj])] at h
    exact h
  rw [Proof.Ed25519.bytesAt_encodeLE t.mem, Proof.Ed25519.bytesAt_encodeLE s.mem]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  rw [VG.Proof.Ed25519.X86.PublicKey.decode_words, VG.Proof.Ed25519.X86.PublicKey.decode_words]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  have w4 := words 4 (by decide)
  have w5 := words 5 (by decide)
  have w6 := words 6 (by decide)
  have w7 := words 7 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3 w4 w5 w6 w7
  change t.mem.readW (E.setWidth 64 + (64 : BitVec 64)) 32 = s.mem.readW (E.setWidth 64 + (224 : BitVec 64)) 32 at w0
  rw [w0, w1, w2, w3, w4, w5, w6, w7]

end VG.Proof.Ed25519.X86.SignCached

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.CT`. -/
section

/-! Merged from `Proof.Ed25519.X86.SignCached.CTCommon`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
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
    (vs : List Value) (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 6 v)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0 vs)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup 0 vs))
      (Two L g₁ g₂ m₁ m₂ (OutArgs L vs)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (VG.Proof.Ed25519.X86.SignCached.args_ok hc hL ha hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (VG.Proof.Ed25519.X86.SignCached.args_ok hc hL hb hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

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

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Body`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.Secret`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.Preserve`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.HashSteps`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.HashPreserve`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Ed25519.bytesAt m p n).length = n := by
  simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]

theorem hash_frame_bytes {L : Lay} (hL : L.Ok) {m m' : Mem} (hf : Frame (hashWrites L) m m')
    {d n : Nat} (hd : 24 ≤ d) (hn : d + n ≤ 192) :
    Spec.Ed25519.bytesAt m' (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.E.setWidth 64 + BitVec.ofNat 64 d) n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩) ?_ (by change n ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p (Offset.sub_base _ (by omega : d + n ≤ 256) p hp))
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · change Region.Disjoint _ ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩
    rw [Taint.sub_setWidth hL.below]
    exact Offset.disjoint_below _ (n := 24) (d := d) (k := n) (by omega)
  · exact Offset.disjoint _ (e := 192) (k := 64) (by omega) (by omega) (by decide)

theorem hash_out_bytes {L : Lay} (hL : L.Ok) {m m' : Mem} (hf : Frame (hashWrites L) m m') :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := ⟨L.out.setWidth 64, 32⟩) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  have ho : Region.Sub ⟨L.out.setWidth 64, 32⟩ L.OUT := Region.sub_prefix (by decide)
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.oc.sub_left ho
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Region.sub_prefix (by decide : 24 ≤ 256) p hp))).sub_right ho).symm
  · exact ((hL.ko.sub_left (Whole.below_sub_stack hL.below (by decide))).sub_right ho).symm
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Offset.sub_base _ (by decide : 192 + 64 ≤ 256) p hp))).sub_right ho).symm

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem update_input (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (source count : Nat) (hsource : source < 6) (hi : Input L (L.value source) 32)
    {prev : List Byte} (hcount : (BitVec.ofNat 32 count).toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (update (inputArgs source count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem ((L.value source).setWidth 64) 32) := by
  refine update_step hc hL ha (by simp) (by simp [Whole.valid, hsource]) ?_ hi hcount hr
  intro t ht
  have h := update_args hL count (.caller source 0) (.const 32) ht
  change UpdateArgs L (BitVec.ofNat 32 count) (L.value source) (32#32) t
  simpa only [value, BitVec.add_zero] using h

theorem update_prefix (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) []) :
    WP isa (update prefixArgs) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 64) 32) := by
  have e : (L.E + 64).setWidth 64 = L.E.setWidth 64 + 64 :=
    addr_eq (x := L.E) (k := 64) (by have := hL.top; omega)
  refine WP.mono (update_step hc hL ha (c := 0#32) (by decide) (by simp [Whole.valid]) ?_
    (prefix_input hL) (prev := []) (by decide) hr) fun t ⟨ht, hf, hp⟩ => ⟨ht, hf, ?_⟩
  · intro t ht
    exact update_args hL 0 (.frame 64) (.const 32) ht
  · simpa only [List.nil_append, e, show (32 : BitVec 32).toNat = 32 from rfl] using hp

theorem update_message (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (count : Nat) {prev : List Byte} (hcount : (BitVec.ofNat 32 count).toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (update (messageArgs count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.mono (update_step hc hL ha (by simp) (by simp [Whole.valid]) ?_
    (message_input hL) hcount hr) fun t ⟨ht, hf, hp⟩ => ⟨ht, hf, ?_⟩
  · intro t ht
    have h := update_args hL count (.caller 3 0) (.caller 4 0) ht
    simpa only [value, Lay.value, BitVec.add_zero] using h
  · rw [hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (by have := L.len.isLt; change L.len.toNat ≤ 2 ^ 64; omega)] at hp
    exact hp

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Reduce`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (d : Nat) (hd : 24 ≤ d) (hd' : d + 32 ≤ 256) :
    WP isa (reduce d) s fun t => Ctx L g m₀ t ∧
      Frame (primitiveWrites L (field L d)) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem ((fp L d).setWidth 64) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.SignCached.args_ok hc hL ha (vs := [.frame d, .frame 192, .caller 5 0])
    (by simp) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by simp) (by simp)
  have a1 := hs.slot hL (j := 1) (by simp) (by simp)
  have a2 := hs.slot hL (j := 2) (by simp) (by simp)
  change Whole.slots L.E u 0 = L.E + BitVec.ofNat 32 d at a0
  change Whole.slots L.E u 1 = L.E + 192 at a1
  change Whole.slots L.E u 2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (Whole.reduce_call hu (hashSpace hL) (by simp [Lay.outputs]) hd hd' a0 a1 a2)
    fun t ⟨ht, hft, hp⟩ => ⟨ht, primitive_frame hf hft, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((fp L d).setWidth 64) 32 = Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt u.mem ((L.E + 192).setWidth 64) 64) at hp
  rw [hp]
  refine congrArg Spec.Ed25519.scalarReduce ?_
  have ea : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 :=
    Whole.frame_addr (hashSpace hL).frameFit (by decide)
  rw [ea]
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨L.E.setWidth 64 + 192, 64⟩)
    (by
      rintro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base _ (d := 192) (n := 64) (k := 24) (by decide) (by decide))
    (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Hashes`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashSeed_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashSeed s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_input hu hL ha 1 0 (by decide) (seed_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have hs := hu.input_bytes hL (r := L.SEED) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt u.mem (L.seed.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32 at hs
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.seed.setWidth 64) 32) at rv
  rw [List.nil_append, hs] at rv
  refine WP.mono (finalize_step hv hL ha 32 (by decide) false
    (by rw [bytes_length]; decide) (by rw [bytes_length]; rfl) rv)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans ft), hd⟩

theorem hashNonce_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashNonce s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_prefix hu hL ha ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have keep := hash_frame_bytes hL fu (d := 64) (n := 32) (by decide) (by decide)
  change Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + (64 : BitVec 64)) 32 = Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + (64 : BitVec 64)) 32 at keep
  rw [keep] at rv
  refine WP.seq (WP.mono (update_message hv hL ha 32 (by rw [bytes_length]; rfl) rv)
    fun w ⟨hw, fw, rw'⟩ => ?_)
  refine WP.mono (finalize_step hw hL ha 32 (by decide) true ?_ ?_ rw')
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans ft)), hd⟩
  · rw [List.length_append, bytes_length, bytes_length]
    have := L.len.isLt; omega
  · rw [List.length_append, bytes_length, bytes_length]
    simp only [ite_true]; omega

theorem hashChallenge_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashChallenge s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.out.setWidth 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_input hu hL ha 0 0 (by decide) (point_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.out.setWidth 64) 32) at rv
  rw [List.nil_append, hash_out_bytes hL fu] at rv
  refine WP.seq (WP.mono (update_input hv hL ha 2 32 (by decide) (key_input hL)
    (by rw [bytes_length]; rfl) rv) fun w ⟨hw, fw, rw'⟩ => ?_)
  have hk := hv.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt v.mem (L.pk.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 at hk
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt v.mem (L.pk.setWidth 64) 32) at rw'
  rw [hk] at rw'
  refine WP.seq (WP.mono (update_message hw hL ha 64 (by rw [List.length_append, bytes_length, bytes_length]; rfl)
    rw') fun z ⟨hz, fz, rz⟩ => ?_)
  refine WP.mono (finalize_step hz hL ha 64 (by decide) true ?_ ?_ rz)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans (fz.trans ft))), hd⟩
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    have := L.len.isLt; omega
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    simp only [ite_true]; omega

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86
variable {L : Lay} {m m' : Mem}

theorem frame_bytes {rs : List Region} (hf : Frame rs m m') (r : Region)
    (hd : ∀ R ∈ rs, r.Disjoint R) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes hd hn (List.mem_range.mp hi)

theorem single_frame_bytes {d n e k : Nat} (hf : Frame [⟨L.E.setWidth 64 + BitVec.ofNat 64 e, k⟩] m m')
    (hsep : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 256) (he : e + k ≤ 256) :
    Spec.Ed25519.bytesAt m' (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.E.setWidth 64 + BitVec.ofNat 64 d) n :=
  frame_bytes hf ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩
    (by rintro r hr; rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hsep (by omega) (by omega))
    (by change n ≤ 2 ^ 64; omega)

theorem primitive_field_bytes (hL : L.Ok) {out : Region}
    (hf : Frame (primitiveWrites L out) m m') {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 256)
    (ho : (field L d).Disjoint out) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  refine frame_bytes hf (field L d) ?_ (by change 32 ≤ 2 ^ 64; decide)
  simp only [primitiveWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ho
  · exact hL.kc.sub_left (field_sub hL hb)
  · change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ _
    rw [fp_addr hL (by omega)]
    exact Offset.disjoint_base _ hd (by omega)
  · change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩
    rw [fp_addr hL (by omega), Taint.sub_setWidth hL.below]
    exact Offset.disjoint_below _ (n := 24) (d := d) (k := 32) (by omega)

theorem reduce_field_bytes (hL : L.Ok) {o d : Nat}
    (hf : Frame (primitiveWrites L (field L o)) m m') (hd : 24 ≤ d) (hb : d + 32 ≤ 256)
    (ho : o + 32 ≤ 256) (hs : d + 32 ≤ o ∨ o + 32 ≤ d) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  refine primitive_field_bytes hL hf hd hb ?_
  change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ ⟨(fp L o).setWidth 64, 32⟩
  rw [fp_addr hL (by omega), fp_addr hL (by omega)]
  exact Offset.disjoint _ hs (by omega) (by omega)

theorem base_field_bytes (hL : L.Ok) (hf : Frame (primitiveWrites L (baseOut L)) m m')
    {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 :=
  primitive_field_bytes hL hf hd hb ((hL.ko.sub_left (field_sub hL hb)).sub_right (Region.sub_prefix (by decide)))

theorem primitive_out_bytes (hL : L.Ok) {out : Region}
    (hf : Frame (primitiveWrites L out) m m') (ho : (baseOut L).Disjoint out) :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  refine frame_bytes hf (baseOut L) ?_ (by change 32 ≤ 2 ^ 64; decide)
  have hs : Region.Sub (baseOut L) L.OUT := Region.sub_prefix (by decide)
  simp only [primitiveWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ho
  · exact hL.oc.sub_left hs
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Region.sub_prefix (by decide : 24 ≤ 256) p hp))).sub_right hs).symm
  · exact ((hL.ko.sub_left (Whole.below_sub_stack hL.below (by decide))).sub_right hs).symm

theorem reduce_out_bytes (hL : L.Ok) {d : Nat} (hf : Frame (primitiveWrites L (field L d)) m m')
    (hd : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 :=
  primitive_out_bytes hL hf (((hL.ko.sub_left (field_sub hL hd)).sub_right (Region.sub_prefix (by decide))).symm)

theorem mul_out_bytes (hL : L.Ok) (hf : Frame (primitiveWrites L (half L)) m m') :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  refine primitive_out_bytes hL hf ?_
  change Region.Disjoint ⟨L.out.setWidth 64, 32⟩ ⟨(L.out + 32).setWidth 64, 32⟩
  rw [half_addr hL]
  exact Offset.base_disjoint _ (e := 32) (n := 32) (k := 32) (by decide) (by decide)

theorem hash_field_bytes (hL : L.Ok) (hf : Frame (hashWrites L) m m')
    {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 192) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  rw [fp_addr hL (by omega)]
  exact hash_frame_bytes hL hf hd hb

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem ctx_step {t : State} (hc : Ctx L g m₀ s) (ht : PublicKey.Step s t) {d n : Nat}
    (hf : Frame [⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩] s.mem t.mem) (hn : d + n ≤ 256) :
    Ctx L g m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.esp ?_ hf ?_
  · intro r hr _
    apply ht.regs
    rintro rfl; simp [calleeSaved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ hn)

theorem saveSecret_ok (hc : Ctx L g m₀ s) (hL : L.Ok) {expanded : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64 = expanded) :
    WP isa (.block saveSecret) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 64) 32 = expanded.drop 32 := by
  rw [saveSecret, WP.block_append_iff]
  have fr : Whole.FR L.E ∈ s.wr := by rw [hc.wr]; exact List.mem_cons_self
  have fit := (hashSpace hL).frameFit
  refine WP.mono (PublicKey.prune_ok hc.esp fit fr he) fun u ⟨hu, hf, hs⟩ => ?_
  have hcu := ctx_step hc hu (d := 32) (n := 32) hf (by decide)
  refine WP.mono (prefix_ok hcu.esp fit (by rw [hcu.wr]; exact List.mem_cons_self))
    fun t ⟨ht, hft, hp⟩ => ⟨ctx_step hcu ht (d := 64) (n := 32) hft (by decide), ?_, ?_⟩
  · rw [fp_addr hL (by decide)]
    have keep := single_frame_bytes (L := L) hft (d := 32) (n := 32) (e := 64) (k := 32)
      (by decide) (by decide) (by decide)
    rw [keep]
    have sc := Proof.Ed25519.bytesAt_encodeLE u.mem (L.E.setWidth 64 + 32) 32
    rw [hs] at sc
    exact sc
  · rw [hp]
    have keep := single_frame_bytes (L := L) hf (d := 224) (n := 32) (e := 32) (k := 32)
      (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + (224 : BitVec 64)) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + (224 : BitVec 64)) 32 at keep
    rw [keep, ← he, Proof.Ed25519.signatureBytes_drop]
    rw [BitVec.add_assoc, show (192 : BitVec 64) + BitVec.ofNat 64 32 = (224 : BitVec 64) from rfl]

def expanded (L : Lay) (m : Mem) : List Byte :=
  Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m (L.seed.setWidth 64) 32)
def scalar (L : Lay) (m : Mem) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune (expanded L m))
def nonce (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
    ((expanded L m).drop 32 ++ Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat))

structure SecretReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 = scalar L m
  prefixBytes : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 64) 32 = (expanded L m).drop 32

theorem secret_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (.seq hashSeed (.block saveSecret)) s fun t => Ctx L g m₀ t ∧ SecretReady L m₀ t := by
  refine WP.seq (WP.mono (hashSeed_ok hc hL ha) fun u ⟨hu, _, hd⟩ => ?_)
  exact WP.mono (saveSecret_ok hu hL hd) fun t ⟨ht, hs, hp⟩ => ⟨ht, hs, hp⟩

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

structure NonceReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 = scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem ((fp L 96).setWidth 64) 32 = nonce L m
  point : Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

theorem nonce_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : SecretReady L m₀ s) :
    WP isa nonceCode s fun t => Ctx L g m₀ t ∧ NonceReady L m₀ t := by
  refine WP.seq (WP.mono (hashNonce_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.prefixBytes] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (reduce_step hu hL ha 96 (by decide) (by decide)) fun v ⟨hv, fv, nv⟩ => ?_)
  rw [du] at nv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide) (by decide)).trans su
  refine WP.mono (base_step hv hL ha) fun t ⟨ht, ft, pt⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (base_field_bytes hL ft (d := 32) (by decide) (by decide)).trans sv
  · exact (base_field_bytes hL ft (d := 96) (by decide) (by decide)).trans nv
  · rw [nv] at pt
    exact pt

theorem challenge_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : NonceReady L m₀ s)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)) :
    WP isa challengeCode s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (hashChallenge_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.point] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide) (by decide)).trans hs.scalar
  have nu := (hash_field_bytes hL fu (d := 96) (by decide) (by decide)).trans hs.nonce
  have pu := (hash_out_bytes hL fu).trans hs.point
  refine WP.seq (WP.mono (reduce_step hu hL ha 128 (by decide) (by decide)) fun v ⟨hv, fv, cv⟩ => ?_)
  rw [du] at cv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide) (by decide)).trans su
  have nv := (reduce_field_bytes hL fv (d := 96) (by decide) (by decide) (by decide) (by decide)).trans nu
  have pv := (reduce_out_bytes hL fv (by decide)).trans pu
  refine WP.mono (mul_step hv hL ha) fun t ⟨ht, ft, st⟩ => ⟨ht, ?_⟩
  rw [nv, cv, sv] at st
  have pt := (mul_out_bytes hL ft).trans pv
  rw [Proof.Ed25519.signatureBytes_split, pt]
  change Spec.Ed25519.scalarBase (nonce L m₀) ++ Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64 + (32 : BitVec 64)) 32 = _
  rw [st]
  exact Proof.Ed25519.sign_pipeline _ _ _ hk

theorem wipe_ok (hc : Ctx L g m₀ s) (hL : L.Ok) :
    WP isa (.block wipe) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.bytesAt s.mem (L.out.setWidth 64) 64 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 8) (count := 56) (hashSpace hL).frameFit (by decide))
    fun t ⟨ht, hf, _⟩ => ⟨ht, ?_⟩
  refine frame_bytes hf L.OUT ?_ (by change 64 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
    (Offset.sub_base _ (by decide : 4 * 8 + 4 * 56 ≤ 256) p hp))).symm

theorem body_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)) :
    WP isa body s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (secret_ok hc hL ha) fun u ⟨hu, su⟩ => ?_)
  refine WP.seq (WP.mono (nonce_ok hu hL ha su) fun v ⟨hv, nv⟩ => ?_)
  refine WP.seq (WP.mono (challenge_ok hv hL ha nv hk) fun w ⟨hw, sw⟩ => ?_)
  exact WP.mono (wipe_ok hw hL) fun t ⟨ht, same⟩ => ⟨ht, same.trans sw⟩

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.CTPrimitives`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (d : Nat) (hd : 24 ≤ d) (hd' : d + 32 ≤ 256) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.frame d, .frame 192, .caller 5 0]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarReduce_ok scalarReduce_ct Whole.reduce_nosp (by rw [Whole.reduce_stack]; decide)
  · intro g m t hc hs
    exact reduce_ready hc hL hd hd' (hs.slot hL (j := 0) (by simp) (by simp))
      (hs.slot hL (j := 1) (by simp) (by simp))
      ((hs.slot hL (j := 2) (by simp) (by simp)).trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by simp) h (by decide : 0 < 3),
      call_args_eq hL (by simp) h (by decide : 1 < 3), call_args_eq hL (by simp) h (by decide : 2 < 3)⟩

theorem base_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 0 0, .frame 96, .caller 5 0]))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarBase_ok scalarBase_ct base_nosp (by rw [base_stack]; decide)
  · intro g m t hc hs
    exact base_ready hc hL ⟨((hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)),
      hs.slot hL (j := 1) (by decide) (by decide),
      ((hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _))⟩
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 3),
      call_args_eq hL (by decide) h (by decide : 1 < 3), call_args_eq hL (by decide) h (by decide : 2 < 3)⟩

theorem mul_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.X86.scalarMulAdd)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarMulAdd_ok scalarMulAdd_ct mul_nosp (by rw [mul_stack]; decide)
  · intro g m t hc hs
    exact mul_ready hc hL ⟨hs.slot hL (j := 0) (by decide) (by decide),
      hs.slot hL (j := 1) (by decide) (by decide), hs.slot hL (j := 2) (by decide) (by decide),
      hs.slot hL (j := 3) (by decide) (by decide),
      ((hs.slot hL (j := 4) (by decide) (by decide)).trans (BitVec.add_zero _))⟩
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 5),
      call_args_eq hL (by decide) h (by decide : 1 < 5), call_args_eq hL (by decide) h (by decide : 2 < 5),
      call_args_eq hL (by decide) h (by decide : 3 < 5), call_args_eq hL (by decide) h (by decide : 4 < 5)⟩

theorem saveSecret_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.CTHashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.CTHash`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 5 0]))
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

theorem finalize_args_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (finalizeArgs n b))
      (Two L g₁ g₂ m₁ m₂ (FinArgs L (BitVec.ofNat 64 ((if b then L.len.toNat else 0) + n)))) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL ha n hn b) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL hb n hn b) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) init (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [.caller 5 0] (by decide) (by simp [Whole.valid]) (by taint_decide)).seq
    (init_call_ct hL)

theorem update_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hp : Whole.valid 6 p) (hn : Whole.valid 6 n)
    (hi : Input L (value L p) (value L n))
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0
      [.caller 5 0, .const count, .const 0, p, n, .caller 5 192])) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (update (setup 0 [.caller 5 0, .const count, .const 0, p, n, .caller 5 192]))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb _ (by simp) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · simp [Whole.valid]
    · simp [Whole.valid]
    · exact hp
    · exact hn
    · simp [Whole.valid]) ht).seq
    (update_call_ct hL rfl hi (fun _ hs => update_args hL count p n hs))

theorem finalize_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (finalize n b)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (finalize_args_ct hL ha hb n hn b ht).seq (finalize_call_ct hL _)

theorem hashSeed_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashSeed
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hs := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.caller 1 0) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa [value, Lay.value] using seed_input hL)
    (by taint_decide)
  exact (init_ct hL ha hb).seq (hs.seq (finalize_ct hL ha hb 32 (by decide) false (by taint_decide)))

theorem hashNonce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashNonce
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hs := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.frame 64) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (prefix_input hL) (by taint_decide)
  have hm := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 32 (.caller 3 0) (.caller 4 0)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa only [value, Lay.value, BitVec.add_zero] using message_input hL)
    (by taint_decide)
  exact (init_ct hL ha hb).seq (hs.seq (hm.seq
    (finalize_ct hL ha hb 32 (by decide) true (by taint_decide))))

theorem hashChallenge_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashChallenge
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hr := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.caller 0 0) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa [value, Lay.value] using point_input hL)
    (by taint_decide)
  have hp := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 32 (.caller 2 0) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa [value, Lay.value] using key_input hL)
    (by taint_decide)
  have hm := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 64 (.caller 3 0) (.caller 4 0)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa only [value, Lay.value, BitVec.add_zero] using message_input hL)
    (by taint_decide)
  exact (init_ct hL ha hb).seq (hr.seq (hp.seq (hm.seq
    (finalize_ct hL ha hb 64 (by decide) true (by taint_decide)))))

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.CTBody`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have r96 := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 96, .frame 192, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq
    (reduce_call_ct hL 96 (by decide) (by decide))
  have r128 := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 128, .frame 192, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq
    (reduce_call_ct hL 128 (by decide) (by decide))
  have b := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 0 0, .frame 96, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq (base_call_ct hL)
  have m := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq (mul_call_ct hL)
  exact ((hashSeed_ct hL ha hb).seq (saveSecret_ct hL)).seq
    (((hashNonce_ct hL ha hb).seq (r96.seq b)).seq
      (((hashChallenge_ct hL ha hb).seq (r128.seq m)).seq (wipe_ct hL)))

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Correct`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

private theorem noSp_update {args : List Instr} (h : NoSp (.block args)) : NoSp (update args) :=
  noSp_seq h Whole.update_nosp

private theorem noSp_finalize {n : Nat} {b : Bool} (h : NoSp (.block (finalizeArgs n b))) :
    NoSp (finalize n b) := noSp_seq h Whole.finalize_nosp

private theorem noSp_reduce {n : Nat} (h : NoSp (.block (reduceArgs n))) : NoSp (reduce n) :=
  noSp_seq h Whole.reduce_nosp

theorem body_nosp : NoSp body := by
  have ni : NoSp init := noSp_seq (NoSp.of_all (by decide +kernel)) Whole.init_nosp
  have hs : NoSp hashSeed := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_finalize (NoSp.of_all (by decide +kernel))))
  have hn : NoSp hashNonce := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
      (noSp_finalize (NoSp.of_all (by decide +kernel)))))
  have hc : NoSp hashChallenge := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
      (noSp_finalize (NoSp.of_all (by decide +kernel))))))
  exact noSp_seq (noSp_seq hs (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_seq hn (noSp_seq (noSp_reduce (NoSp.of_all (by decide +kernel)))
      (noSp_seq (NoSp.of_all (by decide +kernel)) base_nosp)))
    (noSp_seq (noSp_seq hc (noSp_seq (noSp_reduce (NoSp.of_all (by decide +kernel)))
      (noSp_seq (NoSp.of_all (by decide +kernel)) mul_nosp))) (NoSp.of_all (by decide +kernel))))

theorem signCached_ok {s : State} (h : signCachedLocal.pre s) :
    WP isa code s fun t => abiPreserved s t ∧ signCachedLocal.post s t := by
  have hL := lay_ok h
  have hb := entry_bounds h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; omega) body_nosp
    (WP.mono (body_ok (push_ctx h) hL (lay_arguments h) (entry_key h)) fun u ⟨hu, ho⟩ => ?_)
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
      rintro r (rfl | rfl | rfl)
      · exact hL.ro
      · exact hL.rc
      · change (lay s).RET.Disjoint (lay s).STK
        rw [lay_ret h, lay_stack h]
        exact (Offset.below_disjoint _ (by decide)).symm
  · change Spec.Ed25519.bytesAt (popped .eax (List.replicate 64 .eax).length u).mem
      ((arg s 0).setWidth 64) 64 = _
    rw [popped_mem]
    exact ho

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

theorem lay_eq {s t : State} (h : signCachedLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, a0, a1, a2, a3, a4, a5⟩ := h
  simp only [lay, sp, a0, a1, a2, a3, a4, a5]

theorem signCached_ct : ConstantTime isa signCachedLocal.pre signCachedLocal.pub code := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  have he := lay_eq hp
  have h₂ : Ctx (lay s₁) s₂.gpr s₂.mem (pushed (List.replicate 64 .eax) s₂) :=
    he ▸ push_ctx p₂
  have ha₂ : Arguments (lay s₁) s₂.mem := he ▸ lay_arguments p₂
  exact ⟨(body_ct (lay_ok p₁) (lay_arguments p₁) ha₂ _ _ _ _ _ _
    ⟨push_ctx p₁, h₂, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.SignCached.Verified`. -/
section

/-! Merged from `Proof.Ed25519.X86.SignCached.Contract`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3020 then satKey[a.toNat - 0x3000]?.getD 0
  else if a = 0x9005 then 0x10 else if a = 0x9009 then 0x20 else
    if a = 0x900d then 0x30 else if a = 0x9011 then 0x40 else if a = 0x9019 then 0x50 else 0

theorem sat_seed : Spec.Ed25519.bytesAt VG.Proof.Ed25519.X86.SignCached.satMem 0x2000 32 = satSeed := by
  unfold satSeed Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold VG.Proof.Ed25519.X86.SignCached.satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed25519.bytesAt VG.Proof.Ed25519.X86.SignCached.satMem 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Ed25519.X86.SignCached.satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, show 0x3000 + i < 0x3020 from by omega, ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with | .esp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Ed25519.X86.SignCached.satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩, ⟨0x9004, 24⟩]

theorem sat : ∃ s, (Spec.Ed25519.signCachedContract X86.abi 280).pre s := by
  refine ⟨VG.Proof.Ed25519.X86.SignCached.satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, VG.Proof.Ed25519.X86.SignCached.satState]
    sig_and_intros
    · decide +kernel
    · decide +kernel
    · change Spec.Ed25519.bytesAt VG.Proof.Ed25519.X86.SignCached.satMem ((arg VG.Proof.Ed25519.X86.SignCached.satState 2).setWidth 64) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt VG.Proof.Ed25519.X86.SignCached.satMem ((arg VG.Proof.Ed25519.X86.SignCached.satState 1).setWidth 64) 32)
      have a1 : arg VG.Proof.Ed25519.X86.SignCached.satState 1 = 0x2000 := by decide
      have a2 : arg VG.Proof.Ed25519.X86.SignCached.satState 2 = 0x3000 := by decide
      rw [a1, a2]
      change Spec.Ed25519.bytesAt VG.Proof.Ed25519.X86.SignCached.satMem 0x3000 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt VG.Proof.Ed25519.X86.SignCached.satMem 0x2000 32)
      rw [sat_seed, sat_key]
      rfl

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

def signWide : Contract isa := { signCachedLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let pk : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed, pk, msg] ∧ s.wr = [out, scr, args] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint seed ∧ ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) }

theorem signWide_pre (s : State) (h : signWide.pre s) :
    signCachedLocal.pre (s.withRegions (signRd s) (signWr s)) := by
  simp only [signCachedLocal, signRd, signWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem signWide_implies : signWide.Implies (Spec.Ed25519.signCachedContract X86.abi 280) where
  pre := by
    sig_implies_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signWide, signCachedLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signWide, signCachedLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signWide, signCachedLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  sat := sat

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Lit`. -/
section
namespace VG.Impl.Ed25519.X86.SignCached
materialize_code code
end VG.Impl.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

theorem signCached_verified : Verified X86.target code (Spec.Ed25519.signCachedContract X86.abi 280) := by
  have hsat := signWide_implies.sat_left
  have satLocal : ∃ s, signCachedLocal.pre s := hsat.elim fun s h => ⟨_, signWide_pre s h⟩
  have verifiedLocal : Verified X86.target code signCachedLocal :=
    Verified.of_correct (fun _ h => signCached_ok h) signCached_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal signRd signWr signWide_pre
    ?_ ?_ ?_ ?_ hsat) signWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [signRd, signWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [signWide, signCachedLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [signWide, signCachedLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86.SignCached

end
