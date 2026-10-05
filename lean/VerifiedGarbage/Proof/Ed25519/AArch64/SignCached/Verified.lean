import VerifiedGarbage.Impl.Ed25519.AArch64.SignCached
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Impl.Ed25519.AArch64.SignCached.Prefix
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Verified
import VerifiedGarbage.Spec.Ed25519.CachedSign
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Args`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Layout`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

structure Lay where
  out : BitVec 64
  seed : BitVec 64
  pk : BitVec 64
  msg : BitVec 64
  len : BitVec 64
  scr : BitVec 64
  E : BitVec 64

namespace Lay
variable (L : VG.Proof.Ed25519.AArch64.SignCached.Lay)
abbrev OUT : Region := ⟨L.out, 64⟩
abbrev SEED : Region := ⟨L.seed, 32⟩
abbrev PK : Region := ⟨L.pk, 32⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev ARGS : Region := ⟨L.E + BitVec.ofNat 64 256, 48⟩
abbrev FR : Region := Whole.FR L.E
abbrev CK : Region := Whole.CK L.E
def inputs : List Region := [L.SEED, L.PK, L.MSG, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : BitVec 64 :=
  match j with | 0 => L.out | 1 => L.seed | 2 => L.pk | 3 => L.msg | 4 => L.len | _ => L.scr

structure Ok : Prop where
  top : L.E.toNat + 304 ≤ 2 ^ 64
  os : ∀ r ∈ L.inputs, L.OUT.Disjoint r
  oc : L.OUT.Disjoint L.SCR
  ko : L.FR.Disjoint L.OUT
  no : L.out.toNat + 64 ≤ 2 ^ 64
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.FR.Disjoint r
  kc : L.FR.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 64
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  ns : L.seed.toNat + 32 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  e16 : 16 ≤ L.E.toNat
  ck : ∀ r ∈ L.inputs, L.CK.Disjoint r
  co : L.CK.Disjoint L.OUT
  cc : L.CK.Disjoint L.SCR
end Lay

/-- The disjoint scratch allocation leaves room for the hash's 64-byte prefix. -/
theorem Lay.Ok.message_bound {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 64 := by
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


abbrev Ctx (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (g : Reg → BitVec 64) (v : VReg → BitVec 128) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g v m₀ L.inputs L.outputs t

namespace Ctx
variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem input_bytes (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ t) (hL : L.Ok)
    {r : Region} (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem r.base r.len = Spec.Ed25519.bytesAt m₀ r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine Frame.bytes hc.frame ?_ hn (List.mem_range.mp hi)
  intro R hR
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl | rfl
  · exact (hL.os r hr).symm
  · exact hL.sc r hr
  · exact (hL.ks r hr).symm
  · exact (hL.ck r hr).symm

theorem arg_word (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 6) :
    t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      m₀.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl | rfl | rfl
    · exact (hL.os _ ha).symm
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm
    · exact (hL.ck _ ha).symm

end Ctx
end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def Arguments (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (m : Mem) : Prop :=
  ∀ j < 6, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j

def value (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : Value → BitVec 64
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

def OutArgs (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (args : List (Reg × Value)) (t : State) : Prop :=
  ∀ p ∈ args, t.gpr p.1 = VG.Proof.Ed25519.AArch64.SignCached.value L p.2

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem Ctx.value (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀)
    {x : Value} (hx : Whole.valid x) : Whole.value L.E s.mem x = VG.Proof.Ed25519.AArch64.SignCached.value L x := by
  cases x with
  | const n => rfl
  | frame d => rfl
  | caller j d =>
    change s.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL hx.1, ha j hx.1]
    rfl

theorem args_ok (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ t ∧ t.mem = s.mem ∧ VG.Proof.Ed25519.AArch64.SignCached.OutArgs L args t := by
  refine WP.mono (hc.setup hn hv (by simp [Lay.inputs, Lay.ARGS, Whole.ARGS]) hr)
    fun t ⟨ht, hm, hs⟩ => ⟨ht, hm, ?_⟩
  intro p hp
  exact (hs p hp).trans (hc.value hL ha (hv p hp))

end VG.Proof.Ed25519.AArch64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Preserve`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Calls`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay}

def field (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (d : Nat) : Region := ⟨L.E + BitVec.ofNat 64 d, 32⟩
def digest (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : Region := ⟨L.E + BitVec.ofNat 64 192, 64⟩
def baseOut (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : Region := ⟨L.out, 32⟩
def half (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : Region := ⟨L.out + BitVec.ofNat 64 32, 32⟩

theorem fieldWithin (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) {d : Nat} (hd : d + 32 ≤ 256) : Whole.Within (VG.Proof.Ed25519.AArch64.SignCached.field L d) L.FR :=
  ⟨d, rfl, hd⟩
theorem digestWithin (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : Whole.Within (VG.Proof.Ed25519.AArch64.SignCached.digest L) L.FR := ⟨192, rfl, by change 192 + 64 ≤ 256; decide⟩
theorem baseWithin (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : Whole.Within (VG.Proof.Ed25519.AArch64.SignCached.baseOut L) L.OUT := ⟨0, by simp [VG.Proof.Ed25519.AArch64.SignCached.baseOut], by change 0 + 32 ≤ 64; decide⟩
theorem halfWithin (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : Whole.Within (VG.Proof.Ed25519.AArch64.SignCached.half L) L.OUT := ⟨32, rfl, by change 32 + 32 ≤ 64; decide⟩
theorem scratchWithin (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩

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

theorem scratch_covered (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within L.SCR R :=
  ⟨L.SCR, by simp [Lay.outputs], VG.Proof.Ed25519.AArch64.SignCached.scratchWithin L⟩

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

theorem field_scr (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) :
    (VG.Proof.Ed25519.AArch64.SignCached.field L d).Disjoint L.SCR := hL.kc.sub_left (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L hd).sub

theorem field_mem {m n : Mem} (hm : n = m) (d : Nat) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by rw [hm]

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Hashes`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.HashSteps`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.Hash`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

abbrev Backend := Whole.Backend
def hashWrites (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : List Region := [L.SCR, VG.Proof.Ed25519.AArch64.SignCached.digest L, L.CK]

theorem hash_frame {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {m n : Mem} {ws : List Region} (hf : Frame ws m n)
    (hw : ∀ r ∈ ws, Region.Sub r L.SCR ∨ Region.Sub r (VG.Proof.Ed25519.AArch64.SignCached.digest L) ∨ Region.Sub r L.CK) :
    Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) m n := by
  refine Frame.sub hf fun r hr => ?_
  rcases hw r hr with hs | hd | hk
  · exact ⟨L.SCR, by simp [VG.Proof.Ed25519.AArch64.SignCached.hashWrites], hs⟩
  · exact ⟨VG.Proof.Ed25519.AArch64.SignCached.digest L, by simp [VG.Proof.Ed25519.AArch64.SignCached.hashWrites], hd⟩
  · exact ⟨L.CK, by simp [VG.Proof.Ed25519.AArch64.SignCached.hashWrites], hk⟩

theorem init_frame {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {m n : Mem} (hf : Frame (Whole.initWr L.scr) m n) :
    Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) m n := by
  apply VG.Proof.Ed25519.AArch64.SignCached.hash_frame hf
  intro r hr; rw [List.mem_singleton.mp hr]
  exact .inl (Whole.sha_sub L.scr)

theorem update_frame {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {m n : Mem} (hf : Frame (Whole.hashWr L.scr ++ [L.CK]) m n) :
    Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) m n := by
  apply VG.Proof.Ed25519.AArch64.SignCached.hash_frame hf
  simp only [Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (Whole.sha_sub L.scr)
  · exact .inl (Whole.work_sub L.scr)
  · exact .inr (.inr fun _ h => h)

theorem finalize_frame {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {m n : Mem}
    (hf : Frame (Whole.finalizeWr L.scr (L.E + 192) ++ [L.CK]) m n) : Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) m n := by
  apply VG.Proof.Ed25519.AArch64.SignCached.hash_frame hf
  simp only [Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact .inl (Whole.sha_sub L.scr)
  · exact .inr (.inl fun _ h => h)
  · exact .inl (Whole.work_sub L.scr)
  · exact .inr (.inr fun _ h => h)

theorem final_writes (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) :
    ∀ r ∈ Whole.finalizeWr L.scr (L.E + 192),
      Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by change 0+192≤8192; decide⟩
  · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.digestWithin L)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192+688≤8192; decide⟩

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem init_step (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀) :
    WP isa init s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧ Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr [] := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.args_ok hc hL ha (args := [(.x0, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 5 0) (by simp)
  change u.gpr .x0 = L.scr + 0#64 at a0
  rw [BitVec.add_zero] at a0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call hu (Whole.init_pre a0) (Whole.covers_writes hw) hw a0)
    fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, hp⟩
  rw [hm] at hf
  exact VG.Proof.Ed25519.AArch64.SignCached.init_frame hf

structure Input (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (p n : Addr) : Prop where
  cover : Whole.Within ⟨p, n.toNat⟩ L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p,n.toNat⟩ R
  scratch : Region.Disjoint ⟨p,n.toNat⟩ L.SCR

/-- A hashed input is outside the frame of the hash function's calls. -/
theorem Input.ck {p n : Addr} (hL : L.Ok) (hi : VG.Proof.Ed25519.AArch64.SignCached.Input L p n) : L.CK.Disjoint ⟨p, n.toNat⟩ := by
  rcases hi.cover with ⟨off, hb, hl⟩ | ⟨R, hR, hw⟩
  · simp only at hb hl
    rw [hb]
    exact Whole.ck_frame (by change off + n.toNat ≤ 256 at hl; omega)
  · refine Region.Disjoint.sub_right ?_ hw.sub
    simp only [Lay.outputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with hR | rfl | rfl
    · exact hL.ck R hR
    · exact hL.co
    · exact hL.cc

theorem update_covers {p n : Addr} (hi : VG.Proof.Ed25519.AArch64.SignCached.Input L p n) :
    Covers (Whole.updateRd p n ++ Whole.hashWr L.scr) (L.inputs ++ L.FR :: L.outputs) := by
  apply VG.Proof.Ed25519.AArch64.SignCached.covers
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hi.cover
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by change 0+192≤8192; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192+688≤8192; decide⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem update_step (b : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀)
    (count : Nat) (p n : Value) (hc16 : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L p) (VG.Proof.Ed25519.AArch64.SignCached.value L n)) {prev : List Byte}
    (hcount : count = prev.length) (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update b.code b.suffix (setup [(.x0, .caller 5 0), (.x1, .const count),
      (.x2, p), (.x3, n), (.x4, .caller 5 192)])) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧
      Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem (VG.Proof.Ed25519.AArch64.SignCached.value L p) (VG.Proof.Ed25519.AArch64.SignCached.value L n).toNat) := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)] →
      Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · exact hc16
    · exact hp
    · exact hn
    · simp [Whole.valid]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.args_ok hc hL ha (by simp) hv (by simp [preserved]))
    fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 5 0) (by simp)
  have a1 := hs (.x1, .const count) (by simp)
  have a2 := hs (.x2, p) (by simp)
  have a3 := hs (.x3, n) (by simp)
  have a4 := hs (.x4, .caller 5 192) (by simp)
  change u.gpr .x0 = L.scr + 0#64 at a0
  rw [BitVec.add_zero] at a0
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  have huRepr : Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem L.scr prev := by rw [hm]; exact hr
  refine WP.mono (Whole.update_call b hu (Whole.update_pre a0 a2 a3 a4 hi.scratch
    (by rw [hu.sp]; exact hL.e16) (by rw [hu.sp]; exact hL.cc) (by rw [hu.sp]; exact hi.ck hL))
    (VG.Proof.Ed25519.AArch64.SignCached.update_covers hi) hw a0 a2 a3 (by rw [a1]; exact congrArg (BitVec.ofNat 64) hcount) huRepr)
    fun t ⟨ht, hf, hrepr⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact VG.Proof.Ed25519.AArch64.SignCached.update_frame hf
  · rw [hm] at hrepr; exact hrepr

theorem finalize_count (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (n : Nat) (b : Bool) :
    VG.Proof.Ed25519.AArch64.SignCached.value L (if b then Value.caller 4 n else .const n) =
      BitVec.ofNat 64 ((if b then L.len.toNat else 0) + n) := by
  cases b <;> simp [VG.Proof.Ed25519.AArch64.SignCached.value, Lay.value, BitVec.ofNat_add]

theorem finalize_step (v : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀)
    (n : Nat) (hn : n < 4096) (b : Bool) {msg : List Byte}
    (hlen : msg.length < 2 ^ 64) (hcount : (if b then L.len.toNat else 0) + n = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr msg) :
    WP isa (finalize v.code v.suffix n b) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧
      Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = Spec.Sha512.sha512 msg := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.x0, .caller 5 0), (.x1, if b then .caller 4 n else .const n),
      (.x2, .frame 192), (.x3, .caller 5 192)] → Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · cases b <;> simp [Whole.valid] <;> omega
    · simp [Whole.valid]
    · simp [Whole.valid]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.args_ok hc hL ha (by simp) hv (by simp [preserved]))
    fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 5 0) (by simp)
  have a1 := hs (.x1, if b then .caller 4 n else .const n) (by simp)
  have a2 := hs (.x2, .frame 192) (by simp)
  have a3 := hs (.x3, .caller 5 192) (by simp)
  change u.gpr .x0 = L.scr + 0#64 at a0
  rw [BitVec.add_zero] at a0
  have countEq : u.gpr .x1 = BitVec.ofNat 64 msg.length := by
    rw [a1, VG.Proof.Ed25519.AArch64.SignCached.finalize_count, hcount]
  have huRepr : Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem L.scr msg := by rw [hm]; exact hr
  have hw := VG.Proof.Ed25519.AArch64.SignCached.final_writes L
  refine WP.mono (Whole.finalize_call v hu (Whole.finalize_pre a0 a2 a3
    (hL.kc.sub_left (VG.Proof.Ed25519.AArch64.SignCached.digestWithin L).sub) (by rw [hu.sp]; exact hL.e16) (by rw [hu.sp]; exact hL.cc)
    (by rw [hu.sp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)))
    (Whole.covers_writes hw) hw a0 a2 countEq huRepr hlen)
    fun t ⟨ht, hf, hh⟩ => ⟨ht, ?_, hh⟩
  rw [hm] at hf
  exact VG.Proof.Ed25519.AArch64.SignCached.finalize_frame hf

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.HashUpdates`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.HashInputs`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay}

theorem input_self {r : Region} (hr : r ∈ L.inputs) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨r, List.mem_append_left _ hr, 0, by simp, by simp⟩

theorem seed_input (hL : L.Ok) : VG.Proof.Ed25519.AArch64.SignCached.Input L L.seed 32 :=
  ⟨.inr (VG.Proof.Ed25519.AArch64.SignCached.input_self (r := L.SEED) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs])⟩
theorem key_input (hL : L.Ok) : VG.Proof.Ed25519.AArch64.SignCached.Input L L.pk 32 :=
  ⟨.inr (VG.Proof.Ed25519.AArch64.SignCached.input_self (r := L.PK) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs])⟩
theorem message_input (hL : L.Ok) : VG.Proof.Ed25519.AArch64.SignCached.Input L L.msg L.len :=
  ⟨.inr (VG.Proof.Ed25519.AArch64.SignCached.input_self (r := L.MSG) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs])⟩
theorem point_input (hL : L.Ok) : VG.Proof.Ed25519.AArch64.SignCached.Input L L.out 32 :=
  ⟨.inr (VG.Proof.Ed25519.AArch64.SignCached.output_covered (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L)), hL.oc.sub_left (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L).sub⟩
theorem prefix_input (hL : L.Ok) : VG.Proof.Ed25519.AArch64.SignCached.Input L (L.E + 64) 32 :=
  ⟨.inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L (by decide)), VG.Proof.Ed25519.AArch64.SignCached.field_scr hL (by decide)⟩

theorem frame_bytes {m n : Mem} {ws : List Region} (hf : Frame ws m n) (r : Region)
    (hd : ∀ w ∈ ws, r.Disjoint w) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt n r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem hash_field_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) m n)
    {d : Nat} (hd : d + 32 ≤ 192) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.AArch64.SignCached.frame_bytes hf (VG.Proof.Ed25519.AArch64.SignCached.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.AArch64.SignCached.hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.Proof.Ed25519.AArch64.SignCached.field_scr hL (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)
  · exact (Whole.ck_frame (by omega)).symm

theorem hash_out_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) m n) :
    Spec.Ed25519.bytesAt n L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  apply VG.Proof.Ed25519.AArch64.SignCached.frame_bytes hf (VG.Proof.Ed25519.AArch64.SignCached.baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.AArch64.SignCached.hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.oc.sub_left (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L).sub
  · exact (hL.ko.sub_right (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L).sub).symm.sub_right (VG.Proof.Ed25519.AArch64.SignCached.digestWithin L).sub
  · exact (hL.co.sub_right (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L).sub).symm

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem update_input (v : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀)
    (source count : Nat) (hj : source < 6) (hc16 : count < 65536) (hi : VG.Proof.Ed25519.AArch64.SignCached.Input L (L.value source) 32)
    {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update v.code v.suffix (inputArgs source count)) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧
      Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem (L.value source) 32) := by
  have inp : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L (.caller source 0)) (VG.Proof.Ed25519.AArch64.SignCached.value L (.const 32)) := by
    change VG.Proof.Ed25519.AArch64.SignCached.Input L (L.value source + 0#64) 32#64
    rw [BitVec.add_zero]
    exact hi
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.update_step v hc hL ha count (.caller source 0) (.const 32) hc16
    ⟨hj, by decide⟩ (by simp [Whole.valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  change Spec.Sha512.Repr _ t.mem _ (prev ++ Spec.Ed25519.bytesAt s.mem (L.value source + 0#64) 32) at hh
  rw [BitVec.add_zero] at hh
  exact hh

theorem update_prefix (v : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr []) :
    WP isa (update v.code v.suffix prefixArgs) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧
      Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (Spec.Ed25519.bytesAt s.mem (L.E + 64) 32) := by
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.update_step v hc hL ha 0 (.frame 64) (.const 32) (by decide)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (VG.Proof.Ed25519.AArch64.SignCached.prefix_input hL) rfl hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  change Spec.Sha512.Repr _ t.mem _ ([] ++ Spec.Ed25519.bytesAt s.mem (L.E + 64) 32) at hh
  rw [List.nil_append] at hh
  exact hh

theorem update_message (v : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀)
    (count : Nat) (hc16 : count < 65536) {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update v.code v.suffix (messageArgs count)) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧
      Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
  have inp : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L (.caller 3 0)) (VG.Proof.Ed25519.AArch64.SignCached.value L (.caller 4 0)) := by
    simpa only [VG.Proof.Ed25519.AArch64.SignCached.value, Lay.value, BitVec.add_zero] using VG.Proof.Ed25519.AArch64.SignCached.message_input hL
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.update_step v hc hL ha count (.caller 3 0) (.caller 4 0) hc16
    (by simp [Whole.valid]) (by simp [Whole.valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  simp only [VG.Proof.Ed25519.AArch64.SignCached.value, Lay.value, BitVec.add_zero] at hh
  rw [hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (Nat.le_of_lt L.len.isLt)] at hh
  exact hh

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem hashSeed_ok (b : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀) :
    WP isa (hashSeed b.code b.suffix) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧ Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (L.seed) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.update_input b hu hL ha 1 0 (by decide) (by decide) (VG.Proof.Ed25519.AArch64.SignCached.seed_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have hs := hu.input_bytes hL (r := L.SEED) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt u.mem (L.seed) 32 = Spec.Ed25519.bytesAt m₀ (L.seed) 32 at hs
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.seed) 32) at rv
  rw [List.nil_append, hs] at rv
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.finalize_step b hv hL ha 32 (by decide) false
    (by rw [VG.Proof.Ed25519.AArch64.SignCached.bytes_length]; decide) (by rw [VG.Proof.Ed25519.AArch64.SignCached.bytes_length]; rfl) rv)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans ft), hd⟩

theorem hashNonce_ok (b : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀) :
    WP isa (hashNonce b.code b.suffix) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧ Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.E + 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.update_prefix b hu hL ha ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have keep := VG.Proof.Ed25519.AArch64.SignCached.hash_field_bytes hL fu (d := 64) (by decide)
  change Spec.Ed25519.bytesAt u.mem (L.E + (64 : BitVec 64)) 32 = Spec.Ed25519.bytesAt s.mem (L.E + (64 : BitVec 64)) 32 at keep
  rw [keep] at rv
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.update_message b hv hL ha 32 (by decide) (by rw [VG.Proof.Ed25519.AArch64.SignCached.bytes_length]) rv)
    fun w ⟨hw, fw, rw'⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.finalize_step b hw hL ha 32 (by decide) true ?_ ?_ rw')
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans ft)), hd⟩
  · rw [List.length_append, VG.Proof.Ed25519.AArch64.SignCached.bytes_length, VG.Proof.Ed25519.AArch64.SignCached.bytes_length]
    have := hL.message_bound; omega
  · rw [List.length_append, VG.Proof.Ed25519.AArch64.SignCached.bytes_length, VG.Proof.Ed25519.AArch64.SignCached.bytes_length]
    simp only [ite_true]; omega

theorem hashChallenge_ok (b : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀) :
    WP isa (hashChallenge b.code b.suffix) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧ Frame (VG.Proof.Ed25519.AArch64.SignCached.hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.out) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.pk) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.update_input b hu hL ha 0 0 (by decide) (by decide) (VG.Proof.Ed25519.AArch64.SignCached.point_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.out) 32) at rv
  rw [List.nil_append, VG.Proof.Ed25519.AArch64.SignCached.hash_out_bytes hL fu] at rv
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.update_input b hv hL ha 2 32 (by decide) (by decide) (VG.Proof.Ed25519.AArch64.SignCached.key_input hL)
    (by rw [VG.Proof.Ed25519.AArch64.SignCached.bytes_length]) rv) fun w ⟨hw, fw, rw'⟩ => ?_)
  have hk := hv.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt v.mem (L.pk) 32 = Spec.Ed25519.bytesAt m₀ (L.pk) 32 at hk
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt v.mem (L.pk) 32) at rw'
  rw [hk] at rw'
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.update_message b hw hL ha 64 (by decide) (by rw [List.length_append, VG.Proof.Ed25519.AArch64.SignCached.bytes_length, VG.Proof.Ed25519.AArch64.SignCached.bytes_length])
    rw') fun z ⟨hz, fz, rz⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.finalize_step b hz hL ha 64 (by decide) true ?_ ?_ rz)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans (fz.trans ft))), hd⟩
  · rw [List.length_append, List.length_append, VG.Proof.Ed25519.AArch64.SignCached.bytes_length, VG.Proof.Ed25519.AArch64.SignCached.bytes_length, VG.Proof.Ed25519.AArch64.SignCached.bytes_length]
    have := hL.message_bound; omega
  · rw [List.length_append, List.length_append, VG.Proof.Ed25519.AArch64.SignCached.bytes_length, VG.Proof.Ed25519.AArch64.SignCached.bytes_length, VG.Proof.Ed25519.AArch64.SignCached.bytes_length]
    simp only [ite_true]; omega

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Reduce`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
open VG.Impl.Ed25519.AArch64 (scalarReduce)

def reduceRd (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : List Region := [VG.Proof.Ed25519.AArch64.SignCached.digest L]
def reduceWr (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (d : Nat) : List Region := [VG.Proof.Ed25519.AArch64.SignCached.field L d, L.SCR]
def ReduceArgs (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .x0 = L.E + BitVec.ofNat 64 d ∧ s.gpr .x1 = L.E + 192 ∧ s.gpr .x2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (ha : VG.Proof.Ed25519.AArch64.SignCached.ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.AArch64.SignCached.reduceRd L) (VG.Proof.Ed25519.AArch64.SignCached.reduceWr L d)) := by
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2]
  exact ⟨rfl, rfl, hL.kc.sub_left (VG.Proof.Ed25519.AArch64.SignCached.digestWithin L).sub⟩

theorem reduce_call (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256)
    (ha : VG.Proof.Ed25519.AArch64.SignCached.ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ t ∧
      Frame (VG.Proof.Ed25519.AArch64.SignCached.reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  have cov : Covers (VG.Proof.Ed25519.AArch64.SignCached.reduceRd L ++ VG.Proof.Ed25519.AArch64.SignCached.reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.AArch64.SignCached.covers
    simp only [VG.Proof.Ed25519.AArch64.SignCached.reduceRd, VG.Proof.Ed25519.AArch64.SignCached.reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.digestWithin L)
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L hd)
    · exact .inr (VG.Proof.Ed25519.AArch64.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.AArch64.SignCached.reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.AArch64.SignCached.writes
    simp only [VG.Proof.Ed25519.AArch64.SignCached.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L hd)
    · exact .inr (.inr (VG.Proof.Ed25519.AArch64.SignCached.scratchWithin L))
  refine Whole.call_ok hc scalarReduce_ok VG.Proof.Ed25519.AArch64.SignCached.reduce_noFrames (VG.Proof.Ed25519.AArch64.SignCached.reduce_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarReduceLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] using hp

theorem reduce_step (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀)
    (d : Nat) (hd : d + 32 ≤ 256) :
    WP isa (reduce d) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ t ∧ Frame (VG.Proof.Ed25519.AArch64.SignCached.reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.args_ok hc hL ha
    (args := [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)])
    (by simp) (by simp [Whole.valid]; omega) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .frame d) (by simp)
  have a1 := hs (.x1, .frame 192) (by simp)
  have a2 := hs (.x2, .caller 5 0) (by simp)
  change u.gpr .x2 = L.scr + 0#64 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.reduce_call hu hL hd ⟨a0, a1, a2⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Base`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
open VG.Impl.Ed25519.AArch64 (scalarBase)
open VG.Impl.Ed25519.AArch64.Whole (callWith)

def baseRd (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : List Region := [VG.Proof.Ed25519.AArch64.SignCached.field L 96]
def baseWr (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : List Region := [VG.Proof.Ed25519.AArch64.SignCached.baseOut L, L.SCR]
def BaseArgs (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (s : State) : Prop :=
  s.gpr .x0 = L.out ∧ s.gpr .x1 = L.E + 96 ∧ s.gpr .x2 = L.scr

theorem base_noFrames : scalarBase.noFrames = true := by lit_decide

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem base_pre (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.BaseArgs L s) :
    scalarBaseLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.AArch64.SignCached.baseRd L) (VG.Proof.Ed25519.AArch64.SignCached.baseWr L)) := by
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2]
  exact ⟨rfl, rfl, VG.Proof.Ed25519.AArch64.SignCached.field_scr hL (by decide), hL.nc⟩

theorem base_call (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.BaseArgs L s) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ t ∧
      Frame (VG.Proof.Ed25519.AArch64.SignCached.baseWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem L.out 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) := by
  have cov : Covers (VG.Proof.Ed25519.AArch64.SignCached.baseRd L ++ VG.Proof.Ed25519.AArch64.SignCached.baseWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.AArch64.SignCached.covers
    simp only [VG.Proof.Ed25519.AArch64.SignCached.baseRd, VG.Proof.Ed25519.AArch64.SignCached.baseWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L (by decide))
    · exact .inr (VG.Proof.Ed25519.AArch64.SignCached.output_covered (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L))
    · exact .inr (VG.Proof.Ed25519.AArch64.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.AArch64.SignCached.baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.AArch64.SignCached.writes
    simp only [VG.Proof.Ed25519.AArch64.SignCached.baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L))
    · exact .inr (.inr (VG.Proof.Ed25519.AArch64.SignCached.scratchWithin L))
  refine Whole.call_ok hc scalarBase_ok VG.Proof.Ed25519.AArch64.SignCached.base_noFrames (VG.Proof.Ed25519.AArch64.SignCached.base_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarBaseLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] using hp

theorem base_step (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" scalarBase) s fun t =>
      VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ t ∧ Frame (VG.Proof.Ed25519.AArch64.SignCached.baseWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem L.out 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.args_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 0 0) (by simp)
  have a1 := hs (.x1, .frame 96) (by simp)
  have a2 := hs (.x2, .caller 5 0) (by simp)
  change u.gpr .x0 = L.out + 0#64 at a0
  change u.gpr .x2 = L.scr + 0#64 at a2
  rw [BitVec.add_zero] at a0 a2
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.base_call hu hL ⟨a0, a1, a2⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.MulAdd`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
open VG.Impl.Ed25519.AArch64 (scalarMulAdd)
open VG.Impl.Ed25519.AArch64.Whole (callWith)

def mulRd (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : List Region := [VG.Proof.Ed25519.AArch64.SignCached.field L 96, VG.Proof.Ed25519.AArch64.SignCached.field L 128, VG.Proof.Ed25519.AArch64.SignCached.field L 32]
def mulWr (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) : List Region := [VG.Proof.Ed25519.AArch64.SignCached.half L, L.SCR]
def MulArgs (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (s : State) : Prop :=
  s.gpr .x0 = L.out + 32 ∧ s.gpr .x1 = L.E + 96 ∧ s.gpr .x2 = L.E + 128 ∧
    s.gpr .x3 = L.E + 32 ∧ s.gpr .x4 = L.scr

theorem mul_noFrames : scalarMulAdd.noFrames = true := by lit_decide

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem mul_pre (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.MulArgs L s) :
    scalarMulAddLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.AArch64.SignCached.mulRd L) (VG.Proof.Ed25519.AArch64.SignCached.mulWr L)) := by
  simp only [scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2]
  exact ⟨rfl, rfl, VG.Proof.Ed25519.AArch64.SignCached.field_scr hL (by decide), VG.Proof.Ed25519.AArch64.SignCached.field_scr hL (by decide), VG.Proof.Ed25519.AArch64.SignCached.field_scr hL (by decide), hL.nc⟩

theorem mul_call (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.MulArgs L s) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ t ∧
      Frame (VG.Proof.Ed25519.AArch64.SignCached.mulWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out + 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) (Spec.Ed25519.bytesAt s.mem (L.E + 128) 32)
        (Spec.Ed25519.bytesAt s.mem (L.E + 32) 32) := by
  have cov : Covers (VG.Proof.Ed25519.AArch64.SignCached.mulRd L ++ VG.Proof.Ed25519.AArch64.SignCached.mulWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.AArch64.SignCached.covers
    simp only [VG.Proof.Ed25519.AArch64.SignCached.mulRd, VG.Proof.Ed25519.AArch64.SignCached.mulWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L (by decide))
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L (by decide))
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L (by decide))
    · exact .inr (VG.Proof.Ed25519.AArch64.SignCached.output_covered (VG.Proof.Ed25519.AArch64.SignCached.halfWithin L))
    · exact .inr (VG.Proof.Ed25519.AArch64.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.AArch64.SignCached.mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.AArch64.SignCached.writes
    simp only [VG.Proof.Ed25519.AArch64.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (VG.Proof.Ed25519.AArch64.SignCached.halfWithin L))
    · exact .inr (.inr (VG.Proof.Ed25519.AArch64.SignCached.scratchWithin L))
  refine Whole.call_ok hc scalarMulAdd_ok VG.Proof.Ed25519.AArch64.SignCached.mul_noFrames (VG.Proof.Ed25519.AArch64.SignCached.mul_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarMulAddLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1] using hp

theorem mul_step (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀) :
    WP isa (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t =>
      VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m₀ t ∧ Frame (VG.Proof.Ed25519.AArch64.SignCached.mulWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out + 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) (Spec.Ed25519.bytesAt s.mem (L.E + 128) 32)
        (Spec.Ed25519.bytesAt s.mem (L.E + 32) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.args_ok hc hL ha
    (args := [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128), (.x3, .frame 32), (.x4, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 0 32) (by simp)
  have a1 := hs (.x1, .frame 96) (by simp)
  have a2 := hs (.x2, .frame 128) (by simp)
  have a3 := hs (.x3, .frame 32) (by simp)
  have a4 := hs (.x4, .caller 5 0) (by simp)
  change u.gpr .x4 = L.scr + 0#64 at a4
  rw [BitVec.add_zero] at a4
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.mul_call hu hL ⟨a0, a1, a2, a3, a4⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64
variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {m n : Mem}

theorem single_frame_bytes {d e k : Nat} (hf : Frame [⟨L.E + BitVec.ofNat 64 e, k⟩] m n)
    (hd : d + 32 ≤ 256) (he : e + k ≤ 256) (hs : d + 32 ≤ e ∨ e + k ≤ d) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.AArch64.SignCached.frame_bytes hf (VG.Proof.Ed25519.AArch64.SignCached.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ hs (by omega) (by omega)

theorem reduce_field_bytes (hL : L.Ok) {d out : Nat} (hf : Frame (VG.Proof.Ed25519.AArch64.SignCached.reduceWr L out) m n)
    (hd : d + 32 ≤ 256) (ho : out + 32 ≤ 256) (hs : d + 32 ≤ out ∨ out + 32 ≤ d) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.AArch64.SignCached.frame_bytes hf (VG.Proof.Ed25519.AArch64.SignCached.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.AArch64.SignCached.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.disjoint _ hs (by omega) (by omega)
  · exact VG.Proof.Ed25519.AArch64.SignCached.field_scr hL hd

theorem base_field_bytes (hL : L.Ok) (hf : Frame (VG.Proof.Ed25519.AArch64.SignCached.baseWr L) m n) {d : Nat} (hd : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by
  apply VG.Proof.Ed25519.AArch64.SignCached.frame_bytes hf (VG.Proof.Ed25519.AArch64.SignCached.field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.AArch64.SignCached.baseWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hL.ko.sub_left (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L hd).sub).sub_right (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L).sub
  · exact VG.Proof.Ed25519.AArch64.SignCached.field_scr hL hd

theorem reduce_out_bytes (hL : L.Ok) {d : Nat} (hf : Frame (VG.Proof.Ed25519.AArch64.SignCached.reduceWr L d) m n) (hd : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt n L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  apply VG.Proof.Ed25519.AArch64.SignCached.frame_bytes hf (VG.Proof.Ed25519.AArch64.SignCached.baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.AArch64.SignCached.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact ((hL.ko.sub_left (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L hd).sub).sub_right (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L).sub).symm
  · exact hL.oc.sub_left (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L).sub

theorem mul_out_bytes (hL : L.Ok) (hf : Frame (VG.Proof.Ed25519.AArch64.SignCached.mulWr L) m n) :
    Spec.Ed25519.bytesAt n L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  apply VG.Proof.Ed25519.AArch64.SignCached.frame_bytes hf (VG.Proof.Ed25519.AArch64.SignCached.baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [VG.Proof.Ed25519.AArch64.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact hL.oc.sub_left (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L).sub

end VG.Proof.Ed25519.AArch64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Body`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Secret`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.Prefix`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

structure PrefixStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vec : t.v = s.v
  regs : ∀ r, r ≠ .x0 → r ≠ .x15 → t.gpr r = s.gpr r

theorem PrefixStep.trans {s t u : State} (h : VG.Proof.Ed25519.AArch64.SignCached.PrefixStep s t) (h' : VG.Proof.Ed25519.AArch64.SignCached.PrefixStep t u) : VG.Proof.Ed25519.AArch64.SignCached.PrefixStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.vec.trans h.vec,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem copyWord_ok {s : State} {E : Addr} (he : s.sp = E)
    (hr : (⟨E, 256⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 4) :
    WP isa (.block (copyWord k)) s fun t => VG.Proof.Ed25519.AArch64.SignCached.PrefixStep s t ∧
      t.mem = s.mem.writeW (E + BitVec.ofNat 64 (64 + 8 * k))
        (s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * k)) 64) := by
  have source : InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (224 + 8 * k)) 8 :=
    ⟨⟨E, 256⟩, List.mem_append_right _ hr, Offset.contains_base E (by omega) (by omega)⟩
  have dest : InRegions s.wr (E + BitVec.ofNat 64 (64 + 8 * k)) 8 :=
    ⟨⟨E, 256⟩, hr, Offset.contains_base E (by omega) (by omega)⟩
  have hl : exec (.ldrSp .x0 (224 + 8 * k)) s =
      some (s.write .x .x0 (s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * k)) 64)) := by
    simp only [exec, show (224 + 8 * k) % 8 = 0 ∧ 224 + 8 * k < 32768 from by omega,
      and_self, ite_true, State.load, he, source, Option.map_some, Mem.readW, BitVec.setWidth_eq]
  have ha {t : State} : exec (.addSp .x15 64) t = some (t.write .x .x15 (t.sp + BitVec.ofNat 64 64)) := by
    simp only [exec, show 64 < 4096 from by decide, ite_true]
  apply WP.of_runBlock
  simp only [copyWord, runBlock_cons, runStep_some, hl, ha, RegUpd.sp_write]
  rw [exec_str_x ⟨by omega, by omega⟩ (by
    simpa only [RegUpd.wr_write, RegUpd.gpr_write_self, BitVec.setWidth_eq, he, Offset.add_add] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h0 h15
    simp only [RegUpd.gpr_write, h0, h15, ite_false]
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
      BitVec.setWidth_eq, he, Offset.add_add]

structure PrefixInv (E : Addr) (s : State) (n : Nat) (t : State) : Prop where
  step : VG.Proof.Ed25519.AArch64.SignCached.PrefixStep s t
  frame : Frame [⟨E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (E + BitVec.ofNat 64 (64 + 8 * j)) 64 =
    s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * j)) 64

theorem copyPrefix_ok {s : State} {E : Addr} (he : s.sp = E)
    (hw : (⟨E, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap copyWord)) s (VG.Proof.Ed25519.AArch64.SignCached.PrefixInv E s n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.copyPrefix_ok he hw n (by omega)) fun u hu => ?_
    refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.copyWord_ok (hu.step.sp.trans he) (hu.step.wr ▸ hw) (by omega : n < 4))
      fun t ⟨kt, mt⟩ => ?_
    have same : u.mem.readW (E + BitVec.ofNat 64 (224 + 8 * n)) 64 =
        s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * n)) 64 := by
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
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (a := E + BitVec.ofNat 64 (64 + 8 * j))
          (b := E + BitVec.ofNat 64 (64 + 8 * n)) ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem prefix_ok {s : State} {E : Addr} (he : s.sp = E)
    (hw : (⟨E, 256⟩ : Region) ∈ s.wr) :
    WP isa (.block copyPrefix) s fun t => VG.Proof.Ed25519.AArch64.SignCached.PrefixStep s t ∧
      Frame [⟨E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (E + 64) 32 = Spec.Ed25519.bytesAt s.mem (E + 224) 32 := by
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.copyPrefix_ok he hw 4 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  rw [Proof.Ed25519.bytesAt_encodeLE t.mem, Proof.Ed25519.bytesAt_encodeLE s.mem]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (off E 64) 32) =
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off E 224) 32)
  rw [decodeLE_words, decodeLE_words]
  simp only [fe, word]
  rw [ht.words 0 (by decide), ht.words 1 (by decide), ht.words 2 (by decide), ht.words 3 (by decide)]

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem prune_ctx {t : State} (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (ht : PublicKey.Step s t)
    (hf : Frame [⟨s.sp + 32, 32⟩] s.mem t.mem) : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r _; rw [ht.v]
  · intro r hr; rw [List.mem_singleton.mp hr, hc.sp]
    exact .inl (Offset.sub_base _ (by decide : 32 + 32 ≤ 256))

theorem prefix_ctx {t : State} (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (ht : VG.Proof.Ed25519.AArch64.SignCached.PrefixStep s t)
    (hf : Frame [⟨L.E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem) : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r _; rw [ht.vec]
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 64 + 32 ≤ 256))

theorem saveSecret_ok (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) {expanded : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (L.E + 192) 64 = expanded) :
    WP isa (.block saveSecret) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 64) 32 = expanded.drop 32 := by
  rw [saveSecret, WP.block_append_iff]
  have fr : (⟨s.sp, 256⟩ : Region) ∈ s.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  have hd : Spec.Sha512.bytesAt s.mem (s.sp + 192) 64 = expanded := by rw [hc.sp]; exact he
  refine WP.mono (PublicKey.prune_ok fr hd) fun u ⟨hu, hf, hs⟩ => ?_
  have hcu := VG.Proof.Ed25519.AArch64.SignCached.prune_ctx hc hu hf
  rw [hc.sp] at hf hs
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.prefix_ok hcu.sp (by rw [hcu.wr]; exact List.mem_cons_self))
    fun t ⟨ht, hft, hp⟩ => ⟨VG.Proof.Ed25519.AArch64.SignCached.prefix_ctx hcu ht hft, ?_, ?_⟩
  · have keep := VG.Proof.Ed25519.AArch64.SignCached.single_frame_bytes (L := L) hft (d := 32) (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 = Spec.Ed25519.bytesAt u.mem (L.E + 32) 32 at keep
    rw [keep]
    have sc := Proof.Ed25519.bytesAt_encodeLE u.mem (L.E + 32) 32
    rw [hs] at sc
    exact sc
  · rw [hp]
    have keep := VG.Proof.Ed25519.AArch64.SignCached.single_frame_bytes (L := L) (e := 32) (k := 32) hf (d := 224)
      (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (L.E + 224) 32 = Spec.Ed25519.bytesAt s.mem (L.E + 224) 32 at keep
    rw [keep, ← he, Proof.Ed25519.signatureBytes_drop]
    rw [BitVec.add_assoc, show (192 : BitVec 64) + BitVec.ofNat 64 32 = (224 : BitVec 64) from rfl]

def expanded (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (m : Mem) : List Byte := Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m L.seed 32)
def scalar (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (m : Mem) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune (VG.Proof.Ed25519.AArch64.SignCached.expanded L m))
def nonce (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (m : Mem) : List Byte := Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
  ((VG.Proof.Ed25519.AArch64.SignCached.expanded L m).drop 32 ++ Spec.Ed25519.bytesAt m L.msg L.len.toNat))

structure SecretReady (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 = VG.Proof.Ed25519.AArch64.SignCached.scalar L m
  prefixBytes : Spec.Ed25519.bytesAt t.mem (L.E + 64) 32 = (VG.Proof.Ed25519.AArch64.SignCached.expanded L m).drop 32

theorem secret_ok (b : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀) :
    WP isa (secretCode b.code b.suffix) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧ VG.Proof.Ed25519.AArch64.SignCached.SecretReady L m₀ t := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.hashSeed_ok b hc hL ha) fun u ⟨hu, _, hd⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.AArch64.SignCached.saveSecret_ok hu hd) fun t ⟨ht, hs, hp⟩ => ⟨ht, hs, hp⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

structure NonceReady (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 = VG.Proof.Ed25519.AArch64.SignCached.scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem (L.E + 96) 32 = VG.Proof.Ed25519.AArch64.SignCached.nonce L m
  point : Spec.Ed25519.bytesAt t.mem (L.out) 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

theorem nonce_ok (b : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀) (hs : VG.Proof.Ed25519.AArch64.SignCached.SecretReady L m₀ s) :
    WP isa (nonceCode b.code b.suffix) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧ VG.Proof.Ed25519.AArch64.SignCached.NonceReady L m₀ t := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.hashNonce_ok b hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.prefixBytes] at du
  have su := (VG.Proof.Ed25519.AArch64.SignCached.hash_field_bytes hL fu (d := 32) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.reduce_step hu hL ha 96 (by decide)) fun v ⟨hv, fv, nv⟩ => ?_)
  rw [du] at nv
  have sv := (VG.Proof.Ed25519.AArch64.SignCached.reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide)).trans su
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.base_step hv hL ha) fun t ⟨ht, ft, pt⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (VG.Proof.Ed25519.AArch64.SignCached.base_field_bytes hL ft (d := 32) (by decide)).trans sv
  · exact (VG.Proof.Ed25519.AArch64.SignCached.base_field_bytes hL ft (d := 96) (by decide)).trans nv
  · change Spec.Ed25519.bytesAt v.mem (L.E + 96) 32 = _ at nv
    rw [nv] at pt
    exact pt

theorem challenge_ok (b : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀) (hs : VG.Proof.Ed25519.AArch64.SignCached.NonceReady L m₀ s)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed) 32)) :
    WP isa (challengeCode b.code b.suffix) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.hashChallenge_ok b hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.point] at du
  have su := (VG.Proof.Ed25519.AArch64.SignCached.hash_field_bytes hL fu (d := 32) (by decide)).trans hs.scalar
  have nu := (VG.Proof.Ed25519.AArch64.SignCached.hash_field_bytes hL fu (d := 96) (by decide)).trans hs.nonce
  have pu := (VG.Proof.Ed25519.AArch64.SignCached.hash_out_bytes hL fu).trans hs.point
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.reduce_step hu hL ha 128 (by decide)) fun v ⟨hv, fv, cv⟩ => ?_)
  rw [du] at cv
  have sv := (VG.Proof.Ed25519.AArch64.SignCached.reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide)).trans su
  have nv := (VG.Proof.Ed25519.AArch64.SignCached.reduce_field_bytes hL fv (d := 96) (by decide) (by decide) (by decide)).trans nu
  have pv := (VG.Proof.Ed25519.AArch64.SignCached.reduce_out_bytes hL fv (by decide)).trans pu
  refine WP.mono (VG.Proof.Ed25519.AArch64.SignCached.mul_step hv hL ha) fun t ⟨ht, ft, st⟩ => ⟨ht, ?_⟩
  change Spec.Ed25519.bytesAt v.mem (L.E + 96) 32 = _ at nv
  change Spec.Ed25519.bytesAt v.mem (L.E + 128) 32 = _ at cv
  change Spec.Ed25519.bytesAt v.mem (L.E + 32) 32 = _ at sv
  rw [nv, cv, sv] at st
  have pt := (VG.Proof.Ed25519.AArch64.SignCached.mul_out_bytes hL ft).trans pv
  rw [Proof.Ed25519.signatureBytes_split, pt]
  change Spec.Ed25519.scalarBase (VG.Proof.Ed25519.AArch64.SignCached.nonce L m₀) ++ Spec.Ed25519.bytesAt t.mem (L.out + (32 : BitVec 64)) 32 = _
  rw [st]
  exact Proof.Ed25519.sign_pipeline _ _ _ hk

theorem wipe_ok (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) :
    WP isa (.block wipe) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.bytesAt s.mem (L.out) 64 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 4) (count := 28) (by decide))
    fun t ⟨ht, hf, _⟩ => ⟨ht, ?_⟩
  refine VG.Proof.Ed25519.AArch64.SignCached.frame_bytes hf L.OUT ?_ (by change 64 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 4 + 8 * 28 ≤ 256))).symm

theorem body_ok (b : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hc : VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ s) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₀)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed) 32)) :
    WP isa (body b.code b.suffix) s fun t => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.secret_ok b hc hL ha) fun u ⟨hu, su⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.nonce_ok b hu hL ha su) fun v ⟨hv, nv⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.SignCached.challenge_ok b hv hL ha nv hk) fun w ⟨hw, sw⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.AArch64.SignCached.wipe_ok hw hL) fun t ⟨ht, same⟩ => ⟨ht, same.trans sw⟩

end VG.Proof.Ed25519.AArch64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTReady`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTCommon`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

def Two (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128)
    (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  VG.Proof.Ed25519.AArch64.SignCached.Ctx L g₁ v₁ m₁ a ∧ VG.Proof.Ed25519.AArch64.SignCached.Ctx L g₂ v₂ m₂ b ∧ P a ∧ P b

theorem two_sp {P : State → Prop} {a b : State} (h : VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ P a b) :
    a.sp = b.sp := h.1.sp.trans h.2.1.sp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, VG.Proof.Ed25519.AArch64.SignCached.Ctx L g₁ v₁ m₁ t → P t → WP isa c t fun u => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g₁ v₁ m₁ u ∧ Q u)
    (hb : ∀ t, VG.Proof.Ed25519.AArch64.SignCached.Ctx L g₂ v₂ m₂ t → P t → WP isa c t fun u => VG.Proof.Ed25519.AArch64.SignCached.Ctx L g₂ v₂ m₂ u ∧ Q u) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.SignCached.OutArgs L args)) := by
  refine VG.Proof.Ed25519.AArch64.SignCached.two_wp (Whole.block_rel (fun _ _ h => VG.Proof.Ed25519.AArch64.SignCached.two_sp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (VG.Proof.Ed25519.AArch64.SignCached.args_ok hc hL ha hn hv hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (VG.Proof.Ed25519.AArch64.SignCached.args_ok hc hL hb hn hv hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem args_eq {args : List (Reg × Value)} {a b : State}
    (h : VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.SignCached.OutArgs L args) a b) {p : Reg × Value} (hp : p ∈ args) :
    a.gpr p.1 = b.gpr p.1 := (h.2.2.1 p hp).trans (h.2.2.2 p hp).symm

theorem call_gpr_eq {args : List (Reg × Value)} {a b : State}
    (h : VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.SignCached.OutArgs L args) a b) {p : Reg × Value}
    (hp : p ∈ args) (hl : p.1 ∉ linkRegs) : a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := by
  rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl]
  exact VG.Proof.Ed25519.AArch64.SignCached.args_eq h hp

theorem call_ct {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ {g v m t}, VG.Proof.Ed25519.AArch64.SignCached.Ctx L g v m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ P) (.call name c)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.SignCached.two_wp
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

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64
variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {s : State}

def reduce_ready (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) (ha : VG.Proof.Ed25519.AArch64.SignCached.ReduceArgs L d s) : Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have cov : Covers (VG.Proof.Ed25519.AArch64.SignCached.reduceRd L ++ VG.Proof.Ed25519.AArch64.SignCached.reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.AArch64.SignCached.covers
    simp only [VG.Proof.Ed25519.AArch64.SignCached.reduceRd, VG.Proof.Ed25519.AArch64.SignCached.reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.digestWithin L)
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L hd)
    · exact .inr (VG.Proof.Ed25519.AArch64.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.AArch64.SignCached.reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.AArch64.SignCached.writes
    simp only [VG.Proof.Ed25519.AArch64.SignCached.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L hd)
    · exact .inr (.inr (VG.Proof.Ed25519.AArch64.SignCached.scratchWithin L))
  exact ⟨VG.Proof.Ed25519.AArch64.SignCached.reduceRd L, VG.Proof.Ed25519.AArch64.SignCached.reduceWr L d, VG.Proof.Ed25519.AArch64.SignCached.reduce_pre hL ha, cov, ws⟩

def base_ready (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.BaseArgs L s) : Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs s := by
  have cov : Covers (VG.Proof.Ed25519.AArch64.SignCached.baseRd L ++ VG.Proof.Ed25519.AArch64.SignCached.baseWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.AArch64.SignCached.covers
    simp only [VG.Proof.Ed25519.AArch64.SignCached.baseRd, VG.Proof.Ed25519.AArch64.SignCached.baseWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L (by decide))
    · exact .inr (VG.Proof.Ed25519.AArch64.SignCached.output_covered (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L))
    · exact .inr (VG.Proof.Ed25519.AArch64.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.AArch64.SignCached.baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.AArch64.SignCached.writes
    simp only [VG.Proof.Ed25519.AArch64.SignCached.baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (VG.Proof.Ed25519.AArch64.SignCached.baseWithin L))
    · exact .inr (.inr (VG.Proof.Ed25519.AArch64.SignCached.scratchWithin L))
  exact ⟨VG.Proof.Ed25519.AArch64.SignCached.baseRd L, VG.Proof.Ed25519.AArch64.SignCached.baseWr L, VG.Proof.Ed25519.AArch64.SignCached.base_pre hL ha, cov, ws⟩

def mul_ready (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.MulArgs L s) : Whole.CallReady scalarMulAddLocal L.E L.inputs L.outputs s := by
  have cov : Covers (VG.Proof.Ed25519.AArch64.SignCached.mulRd L ++ VG.Proof.Ed25519.AArch64.SignCached.mulWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply VG.Proof.Ed25519.AArch64.SignCached.covers
    simp only [VG.Proof.Ed25519.AArch64.SignCached.mulRd, VG.Proof.Ed25519.AArch64.SignCached.mulWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L (by decide))
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L (by decide))
    · exact .inl (VG.Proof.Ed25519.AArch64.SignCached.fieldWithin L (by decide))
    · exact .inr (VG.Proof.Ed25519.AArch64.SignCached.output_covered (VG.Proof.Ed25519.AArch64.SignCached.halfWithin L))
    · exact .inr (VG.Proof.Ed25519.AArch64.SignCached.scratch_covered L)
  have ws : ∀ r ∈ VG.Proof.Ed25519.AArch64.SignCached.mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply VG.Proof.Ed25519.AArch64.SignCached.writes
    simp only [VG.Proof.Ed25519.AArch64.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (VG.Proof.Ed25519.AArch64.SignCached.halfWithin L))
    · exact .inr (.inr (VG.Proof.Ed25519.AArch64.SignCached.scratchWithin L))
  exact ⟨VG.Proof.Ed25519.AArch64.SignCached.mulRd L, VG.Proof.Ed25519.AArch64.SignCached.mulWr L, VG.Proof.Ed25519.AArch64.SignCached.mul_pre hL ha, cov, ws⟩

def init_ready (ha : s.gpr .x0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initAArch64 Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre ha, Whole.covers_writes hw, hw⟩

def UpdateArgs (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (count p len : Addr) (s : State) : Prop :=
  s.gpr .x0 = L.scr ∧ s.gpr .x1 = count ∧ s.gpr .x2 = p ∧ s.gpr .x3 = len ∧ s.gpr .x4 = L.scr + 192

def update_ready (hL : L.Ok) (hsp : s.sp = L.E) {count p len : Addr} (hi : VG.Proof.Ed25519.AArch64.SignCached.Input L p len)
    (ha : VG.Proof.Ed25519.AArch64.SignCached.UpdateArgs L count p len s) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs s := by
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd p len, Whole.hashWr L.scr,
    Whole.update_pre ha.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 hi.scratch (by rw [hsp]; exact hL.e16)
      (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hi.ck hL), VG.Proof.Ed25519.AArch64.SignCached.update_covers hi, hw⟩

def FinalArgs (L : VG.Proof.Ed25519.AArch64.SignCached.Lay) (count : Addr) (s : State) : Prop :=
  s.gpr .x0 = L.scr ∧ s.gpr .x1 = count ∧ s.gpr .x2 = L.E + 192 ∧ s.gpr .x3 = L.scr + 192

def finalize_ready (hL : L.Ok) (hsp : s.sp = L.E) {count : Addr} (ha : VG.Proof.Ed25519.AArch64.SignCached.FinalArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs s :=
  ⟨[], Whole.finalizeWr L.scr (L.E + 192),
    Whole.finalize_pre ha.1 ha.2.2.1 ha.2.2.2 (hL.kc.sub_left (VG.Proof.Ed25519.AArch64.SignCached.digestWithin L).sub)
      (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
      (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes (VG.Proof.Ed25519.AArch64.SignCached.final_writes L), VG.Proof.Ed25519.AArch64.SignCached.final_writes L⟩

end VG.Proof.Ed25519.AArch64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Entry`. -/
section

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

def signCachedLocal : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 64⟩
    let seed : Region := ⟨s.gpr .x1, 32⟩
    let pk : Region := ⟨s.gpr .x2, 32⟩
    let msg : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [seed, pk, msg] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint scr ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32)
  post s t := Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 64 = Spec.Ed25519.sign
    (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.gpr .x5 = t.gpr .x5

def lay (s : State) : VG.Proof.Ed25519.AArch64.SignCached.Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, Whole.base s⟩

theorem entry_below {s : State} (h : signCachedLocal.pre s) : 352 ≤ s.sp.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := h
  exact hb

theorem entry_writes {s : State} (h : signCachedLocal.pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  obtain ⟨_, hw, _, _, _, _, _, _, _, ko, _, _, _, kc, _⟩ := h
  intro r hr
  rw [hw] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ko
  · exact kc

theorem lay_ok {s : State} (h : signCachedLocal.pre s) : (VG.Proof.Ed25519.AArch64.SignCached.lay s).Ok := by
  obtain ⟨_, _, os, op, om, oc, sc, pc, mc, ko, ks, kp, km, kc, no, ns, np, nm, nc, hb, _⟩ := h
  have stk := Whole.stk_sub s
  have fr : Region.Sub (Whole.FR (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Region.sub_prefix (by decide) : Region.Sub (Whole.FR (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Offset.sub_base _ (by decide) : Region.Sub (Whole.ARGS (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ck := Whole.ck_sub s
  refine ⟨?_, ?_, oc, ko.sub_left fr, no, ?_, ?_, kc.sub_left fr, np, nm, ns, nc, Whole.base_16 hb, ?_,
    ko.sub_left ck, kc.sub_left ck⟩
  · change (s.sp - 336#64).toNat + 304 ≤ 2 ^ 64
    rw [BitVec.toNat_sub_of_le (by change 336 ≤ s.sp.toNat; omega)]
    have hs := s.sp.isLt
    change s.sp.toNat - 336 + 304 ≤ 2 ^ 64
    omega
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact os
    · exact op
    · exact om
    · exact (ko.sub_left ar).symm
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact sc
    · exact pc
    · exact mc
    · exact kc.sub_left ar
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ks.sub_left fr
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ks.sub_left ck
    · exact kp.sub_left ck
    · exact km.sub_left ck
    · exact Whole.ck_frame (by decide : 256 + 48 ≤ 304)

theorem entry_ctx {s p : State} (h : signCachedLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    VG.Proof.Ed25519.AArch64.SignCached.Ctx (VG.Proof.Ed25519.AArch64.SignCached.lay s) s.gpr s.v p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, VG.Proof.Ed25519.AArch64.SignCached.Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.PK, Lay.MSG, Lay.OUT, Lay.SCR, Lay.ARGS, Whole.ARGS, show BitVec.ofNat 64 256 = (256 : Addr) from rfl, VG.Proof.Ed25519.AArch64.SignCached.lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : VG.Proof.Ed25519.AArch64.SignCached.Arguments (VG.Proof.Ed25519.AArch64.SignCached.lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hp hj
  have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

theorem entry_input {s : State} (h : signCachedLocal.pre s) {m : Mem}
    (hf : Frame [below s.sp 336] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, ks, kp, km, _⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have hb : Region.Sub (below s.sp 336) (below s.sp 352) := below_sub (by decide) (by decide)
  rcases hr with rfl | rfl | rfl
  · exact (ks.sub_left hb).symm
  · exact (kp.sub_left hb).symm
  · exact (km.sub_left hb).symm

theorem entry_key {s p : State} (h : signCachedLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Spec.Ed25519.bytesAt p.mem (VG.Proof.Ed25519.AArch64.SignCached.lay s).pk 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt p.mem (VG.Proof.Ed25519.AArch64.SignCached.lay s).seed 32) := by
  have hk : Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk⟩ := h
    exact hk
  have hf := Whole.saved_frame hp
  have hp' := VG.Proof.Ed25519.AArch64.SignCached.entry_input h hf (r := ⟨s.gpr .x2, 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  have hs' := VG.Proof.Ed25519.AArch64.SignCached.entry_input h hf (r := ⟨s.gpr .x1, 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt p.mem (s.gpr .x2) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt p.mem (s.gpr .x1) 32)
  rw [hp', hs']
  exact hk

end VG.Proof.Ed25519.AArch64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Verified`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Correct`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem body_depth (v : Whole.Backend) : (body v.code v.suffix).aarch64Depth ≤ 1 := by
  have hu := Whole.update_depth v
  have hf := Whole.finalize_depth v
  change (Impl.Sha512.AArch64.Stream.updateWith v.suffix v.code).aarch64Depth ≤ 1 at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith v.suffix v.code).aarch64Depth ≤ 1 at hf
  have hr := Whole.depth_zero_of_noFrames VG.Proof.Ed25519.AArch64.SignCached.reduce_noFrames
  have hb := Whole.depth_zero_of_noFrames VG.Proof.Ed25519.AArch64.SignCached.base_noFrames
  have hm := Whole.depth_zero_of_noFrames VG.Proof.Ed25519.AArch64.SignCached.mul_noFrames
  simp only [body, secretCode, nonceCode, challengeCode, hashSeed, hashNonce, hashChallenge,
    init, update, finalize, reduce, Impl.Ed25519.AArch64.Whole.callWith, Code.aarch64Depth, Nat.max_le,
    Impl.Sha512.AArch64.Stream.init, hr, hb, hm]
  omega

theorem signCached_ok (v : Whole.Backend) {s : State} (h : signCachedLocal.pre s) :
    WP isa (code v.code v.suffix) s fun u => abiPreserved s u ∧ signCachedLocal.post s u := by
  have hw := Whole.wrap_ok (VG.Proof.Ed25519.AArch64.SignCached.body_depth v) (VG.Proof.Ed25519.AArch64.SignCached.entry_below h) (VG.Proof.Ed25519.AArch64.SignCached.entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (s.gpr .x0) 64 = Spec.Ed25519.sign
      (Spec.Ed25519.bytesAt m (s.gpr .x1) 32)
      (Spec.Ed25519.bytesAt m (s.gpr .x3) (s.gpr .x4).toNat))
    (fun p hp => WP.mono (VG.Proof.Ed25519.AArch64.SignCached.body_ok v (VG.Proof.Ed25519.AArch64.SignCached.entry_ctx h hp) (VG.Proof.Ed25519.AArch64.SignCached.lay_ok h) (VG.Proof.Ed25519.AArch64.SignCached.entry_args hp) (VG.Proof.Ed25519.AArch64.SignCached.entry_key h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        simpa only [Whole.bodyRd, h.1, VG.Proof.Ed25519.AArch64.SignCached.Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.PK, Lay.MSG,
          Lay.OUT, Lay.SCR, Lay.ARGS, Whole.ARGS, show BitVec.ofNat 64 256 = (256 : Addr) from rfl, VG.Proof.Ed25519.AArch64.SignCached.lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs := VG.Proof.Ed25519.AArch64.SignCached.entry_input h hf (r := ⟨s.gpr .x1, 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  have hm := VG.Proof.Ed25519.AArch64.SignCached.entry_input h hf (r := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩) (by rw [h.1]; simp)
    (Nat.le_of_lt (s.gpr .x4).isLt)
  change Spec.Ed25519.bytesAt u.mem (s.gpr .x0) 64 = _
  rw [hp, hs, hm]

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTBody`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTHash`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem init_call_ct :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.SignCached.OutArgs L [(.x0, .caller 5 0)]))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.SignCached.call_ct (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 (Whole.depth_of_noFrames rfl)
  · intro g v m t _ hs
    have h := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at h
    rw [BitVec.add_zero] at h
    exact VG.Proof.Ed25519.AArch64.SignCached.init_ready h
  · intro a b ar aw br bw h
    have hsp := VG.Proof.Ed25519.AArch64.SignCached.two_sp h
    exact ⟨VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide), hsp⟩

theorem update_call_ct (backend : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hL : L.Ok) (count : Nat) (p n : Value)
    (hi : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L p) (VG.Proof.Ed25519.AArch64.SignCached.value L n)) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.SignCached.OutArgs L
      [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)]))
      (.call (Spec.Sha512.updateScratchApi.name ++ backend.suffix) backend.update)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.SignCached.call_ct backend.update_verified.1 backend.update_verified.2.1 (Whole.update_depth backend)
  · intro g v m t hc hs
    have a0 := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    rw [BitVec.add_zero] at a0
    exact VG.Proof.Ed25519.AArch64.SignCached.update_ready hL hc.sp hi ⟨a0, hs (.x1, .const count) (by simp), hs (.x2, p) (by simp),
      hs (.x3, n) (by simp), hs (.x4, .caller 5 192) (by simp)⟩
  · intro a b ar aw br bw h
    have hsp := VG.Proof.Ed25519.AArch64.SignCached.two_sp h
    exact ⟨VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x1, .const count)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x2, p)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x3, n)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x4, .caller 5 192)) h (by simp) (by decide), hsp⟩

theorem finalize_call_ct (backend : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hL : L.Ok) (n : Nat) (b : Bool) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.SignCached.OutArgs L
      [(.x0, .caller 5 0), (.x1, if b then .caller 4 n else .const n),
        (.x2, .frame 192), (.x3, .caller 5 192)]))
      (.call (Spec.Sha512.finalizeScratchApi.name ++ backend.suffix) backend.finalize)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.SignCached.call_ct backend.finalize_verified.1 backend.finalize_verified.2.1 (Whole.finalize_depth backend)
  · intro g v m t hc hs
    have a0 := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    rw [BitVec.add_zero] at a0
    exact VG.Proof.Ed25519.AArch64.SignCached.finalize_ready hL hc.sp ⟨a0, hs (.x1, if b then .caller 4 n else .const n) (by simp),
      hs (.x2, .frame 192) (by simp), hs (.x3, .caller 5 192) (by simp)⟩
  · intro a c ar aw br bw h
    have hsp := VG.Proof.Ed25519.AArch64.SignCached.two_sp h
    exact ⟨VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x1, if b then .caller 4 n else .const n)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x2, .frame 192)) h (by simp) (by decide),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x3, .caller 5 192)) h (by simp) (by decide), hsp⟩

theorem init_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) init
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (VG.Proof.Ed25519.AArch64.SignCached.setup_ct hL ha hb [(.x0, .caller 5 0)] (by decide) (by simp [Whole.valid])
    (by simp [preserved]) (by taint_decide)).seq VG.Proof.Ed25519.AArch64.SignCached.init_call_ct

theorem update_ct (backend : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂)
    (count : Nat) (p n : Value) (hc : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L p) (VG.Proof.Ed25519.AArch64.SignCached.value L n))
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup
      [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)])) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (update backend.code backend.suffix (setup
        [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)]))
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : ∀ x : Reg × Value, x ∈ [(.x0, .caller 5 0), (.x1, .const count),
      (.x2, p), (.x3, n), (.x4, .caller 5 192)] → Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · exact hc
    · exact hp
    · exact hn
    · simp [Whole.valid]
  exact (VG.Proof.Ed25519.AArch64.SignCached.setup_ct hL ha hb _ (by simp) hv (by simp [preserved]) ht).seq
    (VG.Proof.Ed25519.AArch64.SignCached.update_call_ct backend hL count p n hi)

theorem finalize_ct (backend : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂)
    (n : Nat) (hn : n < 4096) (b : Bool)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (finalize backend.code backend.suffix n b)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (if b then .caller 4 n else .const n) := by
    cases b <;> simp [Whole.valid] <;> omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.x0, .caller 5 0),
      (.x1, if b then .caller 4 n else .const n), (.x2, .frame 192), (.x3, .caller 5 192)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · exact hv
    · simp [Whole.valid]
    · simp [Whole.valid]
  exact (VG.Proof.Ed25519.AArch64.SignCached.setup_ct hL ha hb _ (by simp) hvall (by simp [preserved]) ht).seq
    (VG.Proof.Ed25519.AArch64.SignCached.finalize_call_ct backend hL n b)

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTHashPipeline`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem hashSeed_ct (backend : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hashSeed backend.code backend.suffix)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hi : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L (.caller 1 0)) (VG.Proof.Ed25519.AArch64.SignCached.value L (.const 32)) := by
    change VG.Proof.Ed25519.AArch64.SignCached.Input L (L.seed + 0#64) 32#64
    rw [BitVec.add_zero]
    exact VG.Proof.Ed25519.AArch64.SignCached.seed_input hL
  exact (VG.Proof.Ed25519.AArch64.SignCached.init_ct hL ha hb).seq ((VG.Proof.Ed25519.AArch64.SignCached.update_ct backend hL ha hb 0 (.caller 1 0) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hi (by taint_decide)).seq
    (VG.Proof.Ed25519.AArch64.SignCached.finalize_ct backend hL ha hb 32 (by decide) false (by taint_decide)))

theorem hashNonce_ct (backend : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hashNonce backend.code backend.suffix)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hp : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L (.frame 64)) (VG.Proof.Ed25519.AArch64.SignCached.value L (.const 32)) := VG.Proof.Ed25519.AArch64.SignCached.prefix_input hL
  have hm : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L (.caller 3 0)) (VG.Proof.Ed25519.AArch64.SignCached.value L (.caller 4 0)) := by
    change VG.Proof.Ed25519.AArch64.SignCached.Input L (L.msg + 0#64) (L.len + 0#64)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact VG.Proof.Ed25519.AArch64.SignCached.message_input hL
  exact (VG.Proof.Ed25519.AArch64.SignCached.init_ct hL ha hb).seq ((VG.Proof.Ed25519.AArch64.SignCached.update_ct backend hL ha hb 0 (.frame 64) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hp (by taint_decide)).seq
    ((VG.Proof.Ed25519.AArch64.SignCached.update_ct backend hL ha hb 32 (.caller 3 0) (.caller 4 0)
      (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hm (by taint_decide)).seq
      (VG.Proof.Ed25519.AArch64.SignCached.finalize_ct backend hL ha hb 32 (by decide) true (by taint_decide))))

theorem hashChallenge_ct (backend : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hashChallenge backend.code backend.suffix)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have ho : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L (.caller 0 0)) (VG.Proof.Ed25519.AArch64.SignCached.value L (.const 32)) := by
    change VG.Proof.Ed25519.AArch64.SignCached.Input L (L.out + 0#64) 32#64
    rw [BitVec.add_zero]
    exact VG.Proof.Ed25519.AArch64.SignCached.point_input hL
  have hk : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L (.caller 2 0)) (VG.Proof.Ed25519.AArch64.SignCached.value L (.const 32)) := by
    change VG.Proof.Ed25519.AArch64.SignCached.Input L (L.pk + 0#64) 32#64
    rw [BitVec.add_zero]
    exact VG.Proof.Ed25519.AArch64.SignCached.key_input hL
  have hm : VG.Proof.Ed25519.AArch64.SignCached.Input L (VG.Proof.Ed25519.AArch64.SignCached.value L (.caller 3 0)) (VG.Proof.Ed25519.AArch64.SignCached.value L (.caller 4 0)) := by
    change VG.Proof.Ed25519.AArch64.SignCached.Input L (L.msg + 0#64) (L.len + 0#64)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact VG.Proof.Ed25519.AArch64.SignCached.message_input hL
  exact (VG.Proof.Ed25519.AArch64.SignCached.init_ct hL ha hb).seq ((VG.Proof.Ed25519.AArch64.SignCached.update_ct backend hL ha hb 0 (.caller 0 0) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) ho (by taint_decide)).seq
    ((VG.Proof.Ed25519.AArch64.SignCached.update_ct backend hL ha hb 32 (.caller 2 0) (.const 32)
      (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hk (by taint_decide)).seq
      ((VG.Proof.Ed25519.AArch64.SignCached.update_ct backend hL ha hb 64 (.caller 3 0) (.caller 4 0)
        (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hm (by taint_decide)).seq
        (VG.Proof.Ed25519.AArch64.SignCached.finalize_ct backend hL ha hb 64 (by decide) true (by taint_decide)))))

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTPrimitives`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (d : Nat) (hd : d + 32 ≤ 256) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.SignCached.OutArgs L [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.SignCached.call_ct scalarReduce_ok scalarReduce_ct (Whole.depth_of_noFrames VG.Proof.Ed25519.AArch64.SignCached.reduce_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0, .frame d) (by simp)
    have a1 := hs (.x1, .frame 192) (by simp)
    have a2 := hs (.x2, .caller 5 0) (by simp)
    change t.gpr .x2 = L.scr + 0#64 at a2
    rw [BitVec.add_zero] at a2
    exact VG.Proof.Ed25519.AArch64.SignCached.reduce_ready hL hd ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := VG.Proof.Ed25519.AArch64.SignCached.two_sp h
    exact ⟨hsp, VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x0, .frame d)) h (by simp) (by simp [linkRegs]),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x1, .frame 192)) h (by simp) (by decide),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x2, .caller 5 0)) h (by simp) (by decide)⟩

theorem base_call_ct (hL : L.Ok) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.SignCached.OutArgs L [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.SignCached.call_ct scalarBase_ok scalarBase_ct (Whole.depth_of_noFrames VG.Proof.Ed25519.AArch64.SignCached.base_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0, .caller 0 0) (by simp)
    change t.gpr .x0 = L.out + 0#64 at a0
    rw [BitVec.add_zero] at a0
    have a1 := hs (.x1, .frame 96) (by simp)
    have a2 := hs (.x2, .caller 5 0) (by simp)
    change t.gpr .x2 = L.scr + 0#64 at a2
    rw [BitVec.add_zero] at a2
    exact VG.Proof.Ed25519.AArch64.SignCached.base_ready hL ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := VG.Proof.Ed25519.AArch64.SignCached.two_sp h
    exact ⟨hsp, VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x0, .caller 0 0)) h (by simp) (by decide),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x1, .frame 96)) h (by simp) (by decide),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x2, .caller 5 0)) h (by simp) (by decide)⟩

theorem mul_call_ct (hL : L.Ok) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.SignCached.OutArgs L [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128), (.x3, .frame 32), (.x4, .caller 5 0)]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.AArch64.scalarMulAdd)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.SignCached.call_ct scalarMulAdd_ok scalarMulAdd_ct (Whole.depth_of_noFrames VG.Proof.Ed25519.AArch64.SignCached.mul_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0, .caller 0 32) (by simp)
    have a1 := hs (.x1, .frame 96) (by simp)
    have a2 := hs (.x2, .frame 128) (by simp)
    have a3 := hs (.x3, .frame 32) (by simp)
    have a4 := hs (.x4, .caller 5 0) (by simp)
    change t.gpr .x4 = L.scr + 0#64 at a4
    rw [BitVec.add_zero] at a4
    exact VG.Proof.Ed25519.AArch64.SignCached.mul_ready hL ⟨a0, a1, a2, a3, a4⟩
  · intro a b ar aw br bw h
    have hsp := VG.Proof.Ed25519.AArch64.SignCached.two_sp h
    exact ⟨hsp, VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x0, .caller 0 32)) h (by simp) (by decide),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x1, .frame 96)) h (by simp) (by decide),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x2, .frame 128)) h (by simp) (by decide),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x3, .frame 32)) h (by simp) (by decide),
      VG.Proof.Ed25519.AArch64.SignCached.call_gpr_eq (p := (.x4, .caller 5 0)) h (by simp) (by decide)⟩

theorem saveSecret_ct :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.SignCached.two_wp (Whole.block_rel (fun _ _ h => VG.Proof.Ed25519.AArch64.SignCached.two_sp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (VG.Proof.Ed25519.AArch64.SignCached.saveSecret_ok hc rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (VG.Proof.Ed25519.AArch64.SignCached.saveSecret_ok hc rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.SignCached.two_wp (Whole.block_rel (fun _ _ h => VG.Proof.Ed25519.AArch64.SignCached.two_sp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (VG.Proof.Ed25519.AArch64.SignCached.wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (VG.Proof.Ed25519.AArch64.SignCached.wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : VG.Proof.Ed25519.AArch64.SignCached.Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem reduce_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂)
    (d : Nat) (hd : d + 32 ≤ 256)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (reduceArgs d)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (reduce d)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (.frame d) := by change d < 4096; omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · exact hv
    · simp [Whole.valid]
    · simp [Whole.valid]
  exact (VG.Proof.Ed25519.AArch64.SignCached.setup_ct hL ha hb _ (by simp) hvall (by simp [preserved]) ht).seq
    (VG.Proof.Ed25519.AArch64.SignCached.reduce_call_ct hL d hd)

theorem base_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (VG.Proof.Ed25519.AArch64.SignCached.setup_ct hL ha hb [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]
    (by decide) (by simp [Whole.valid]) (by simp [preserved]) (by taint_decide)).seq
    (VG.Proof.Ed25519.AArch64.SignCached.base_call_ct hL)

theorem mul_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (callWith mulAddArgs "vg_ed25519_scalar_mul_add" Impl.Ed25519.AArch64.scalarMulAdd)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (VG.Proof.Ed25519.AArch64.SignCached.setup_ct hL ha hb [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128),
    (.x3, .frame 32), (.x4, .caller 5 0)]
    (by decide) (by simp [Whole.valid]) (by simp [preserved]) (by taint_decide)).seq
    (VG.Proof.Ed25519.AArch64.SignCached.mul_call_ct hL)

theorem body_ct (backend : VG.Proof.Ed25519.AArch64.SignCached.Backend) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body backend.code backend.suffix)
      (VG.Proof.Ed25519.AArch64.SignCached.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  ((VG.Proof.Ed25519.AArch64.SignCached.hashSeed_ct backend hL ha hb).seq VG.Proof.Ed25519.AArch64.SignCached.saveSecret_ct).seq
    (((VG.Proof.Ed25519.AArch64.SignCached.hashNonce_ct backend hL ha hb).seq ((VG.Proof.Ed25519.AArch64.SignCached.reduce_ct hL ha hb 96 (by decide) (by taint_decide)).seq
      (VG.Proof.Ed25519.AArch64.SignCached.base_ct hL ha hb))).seq
      (((VG.Proof.Ed25519.AArch64.SignCached.hashChallenge_ct backend hL ha hb).seq ((VG.Proof.Ed25519.AArch64.SignCached.reduce_ct hL ha hb 128 (by decide) (by taint_decide)).seq
        (VG.Proof.Ed25519.AArch64.SignCached.mul_ct hL ha hb))).seq (VG.Proof.Ed25519.AArch64.SignCached.wipe_ct hL)))

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CT`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem lay_eq {s t : State} (hp : signCachedLocal.pub s t) : VG.Proof.Ed25519.AArch64.SignCached.lay s = VG.Proof.Ed25519.AArch64.SignCached.lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5⟩ := hp
  simp only [VG.Proof.Ed25519.AArch64.SignCached.lay, Whole.base, sp, h0, h1, h2, h3, h4, h5]

theorem signCached_ct (v : Whole.Backend) :
    ConstantTime isa signCachedLocal.pre signCachedLocal.pub (code v.code v.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (VG.Proof.Ed25519.AArch64.SignCached.body_ok v (VG.Proof.Ed25519.AArch64.SignCached.entry_ctx hs hp) (VG.Proof.Ed25519.AArch64.SignCached.lay_ok hs) (VG.Proof.Ed25519.AArch64.SignCached.entry_args hp) (VG.Proof.Ed25519.AArch64.SignCached.entry_key hs hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := VG.Proof.Ed25519.AArch64.SignCached.lay_eq hp
    have hq : VG.Proof.Ed25519.AArch64.SignCached.Ctx (VG.Proof.Ed25519.AArch64.SignCached.lay s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ VG.Proof.Ed25519.AArch64.SignCached.entry_ctx ht hqb
    have hqa : VG.Proof.Ed25519.AArch64.SignCached.Arguments (VG.Proof.Ed25519.AArch64.SignCached.lay s) q.mem := he ▸ VG.Proof.Ed25519.AArch64.SignCached.entry_args hqb
    exact ⟨(VG.Proof.Ed25519.AArch64.SignCached.body_ct v (VG.Proof.Ed25519.AArch64.SignCached.lay_ok hs) (VG.Proof.Ed25519.AArch64.SignCached.entry_args hpa) hqa _ _ _ _ _ _
      ⟨VG.Proof.Ed25519.AArch64.SignCached.entry_ctx hs hpa, hq, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Contract`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey VG.Proof.Ed25519.AArch64.SignCached.satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [VG.Proof.Ed25519.AArch64.SignCached.satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3020 then VG.Proof.Ed25519.AArch64.SignCached.satKey[a.toNat - 0x3000]?.getD 0
  else 0

theorem sat_seed : Spec.Ed25519.bytesAt VG.Proof.Ed25519.AArch64.SignCached.satMem 0x2000 32 = VG.Proof.Ed25519.AArch64.SignCached.satSeed := by
  unfold VG.Proof.Ed25519.AArch64.SignCached.satSeed Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold VG.Proof.Ed25519.AArch64.SignCached.satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed25519.bytesAt VG.Proof.Ed25519.AArch64.SignCached.satMem 0x3000 32 = VG.Proof.Ed25519.AArch64.SignCached.satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, VG.Proof.Ed25519.AArch64.SignCached.satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Ed25519.AArch64.SignCached.satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, show 0x3000 + i < 0x3020 from by omega, ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x5 => 0x5000 | _ => 0
  sp := 0x9000
  mem := VG.Proof.Ed25519.AArch64.SignCached.satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed25519.signCachedContract AArch64.abi 352).pre s := by
  refine ⟨VG.Proof.Ed25519.AArch64.SignCached.satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, VG.Proof.Ed25519.AArch64.SignCached.satState]
    sig_and_intros
    · decide +kernel
    · change Spec.Ed25519.bytesAt VG.Proof.Ed25519.AArch64.SignCached.satMem 0x3000 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt VG.Proof.Ed25519.AArch64.SignCached.satMem 0x2000 32)
      rw [VG.Proof.Ed25519.AArch64.SignCached.sat_seed, VG.Proof.Ed25519.AArch64.SignCached.sat_key]
      rfl

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

theorem signCached_implies : signCachedLocal.Implies (Spec.Ed25519.signCachedContract AArch64.abi 352) where
  pre := by
    sig_implies_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, VG.Proof.Ed25519.AArch64.SignCached.signCachedLocal, below, AArch64.abi, AArch64.argRegs]
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, VG.Proof.Ed25519.AArch64.SignCached.signCachedLocal, below, AArch64.abi, AArch64.argRegs]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, VG.Proof.Ed25519.AArch64.SignCached.signCachedLocal, below, AArch64.abi, AArch64.argRegs]
  sat := VG.Proof.Ed25519.AArch64.SignCached.sat

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem signCached_verified (v : Whole.Backend) :
    Verified AArch64.target (code v.code v.suffix) (Spec.Ed25519.signCachedContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => VG.Proof.Ed25519.AArch64.SignCached.signCached_ok v h) (VG.Proof.Ed25519.AArch64.SignCached.signCached_ct v) (.refl signCached_implies.sat_left))
    VG.Proof.Ed25519.AArch64.SignCached.signCached_implies

end VG.Proof.Ed25519.AArch64.SignCached

end
