module

public import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Verified
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CopyDigest
public import VerifiedGarbage.Spec.Ed25519.ExpandedKey
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Verified
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CopyDigest
meta import VerifiedGarbage.Spec.Ed25519.ExpandedKey
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # Ed25519 public-key derivation from the seed's cached SHA-512 digest (Arm)

`codeExpanded` is `code` with its first step, `hash`, replaced by `copyExpanded`: the digest at
the second argument is copied to `frame 184`, where `hash` leaves it. The rest is proven once,
by `bodyFrom_ok` and `bodyFrom_ct`, for both. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519 (sha512_length)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- The digest at `seed`, read only and outside what the derivation writes. -/
theorem copy_src (hL : L.Ok) (h64 : L.seedLen = 64) :
    Whole.CopySrc L.E L.inputs L.outputs L.seed := by
  have hs : (⟨State.addr L.seed, 64⟩ : Region) = L.SEED := by rw [Lay.SEED, h64]
  refine ⟨by rw [hs]; simp [Lay.inputs], fun r hr => ?_, by have := hL.ns; rw [h64] at this; exact this,
    by have := hL.top; omega⟩
  rw [hs]
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (frame_sub L)).symm

/-- The copy's arguments: the digest in `r1`, `frame 184` in `r2`. -/
theorem copy_args {u : State} (ho : ∀ p ∈ copyArgs, u.gpr p.1 = argValue L p.2) :
    u.gpr .r1 = L.seed ∧ u.gpr .r2 = L.E + BitVec.ofNat 32 184 := by
  have a1 := ho (.r1, .caller 1 0) (by simp [copyArgs])
  simp only [argValue, Lay.value, BitVec.add_zero] at a1
  exact ⟨a1, ho (.r2, .frame 184) (by simp [copyArgs])⟩

theorem copy_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) (h64 : L.seedLen = 64) :
    WP isa copyExpanded t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.E + 184) 64 =
        Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 64 := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := copyArgs) (stk := []) (by decide)
    (by simp [copyArgs, Whole.valid]) (by simp [copyArgs]) (by simp [copyArgs, preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, _, ho, _⟩ => ?_)
  have ⟨a1, a2⟩ := copy_args ho
  exact Whole.copy_digest (copy_src hL h64) ⟨hu, a1, a2, fun _ h => absurd h (Nat.not_lt_zero _)⟩

variable {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem copyWords_ct :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L copyArgs [])) (.block copyWords) fun _ _ => True :=
  ctRegs [.r1, .r2] (fun a b h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.1.2.1 (.r1, .caller 1 0) (by simp [copyArgs])).trans
          (h.2.2.1 (.r1, .caller 1 0) (by simp [copyArgs])).symm
      · exact (h.1.2.1 (.r2, .frame 184) (by simp [copyArgs])).trans
          (h.2.2.1 (.r2, .frame 184) (by simp [copyArgs])).symm)
    (by taint_decide)

theorem copy_ct (hL : L.Ok) (h64 : L.seedLen = 64) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) copyExpanded
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine (setup_ct hL ha hb copyArgs [] (by decide) (by simp [copyArgs, Whole.valid])
    (by simp [copyArgs]) (by simp [copyArgs, preserved]) (by decide) (by simp) (by simp)).seq
    (Whole.rel_wp copyWords_ct ?_ ?_)
  · intro u ⟨hc, ho⟩
    have ⟨a1, a2⟩ := copy_args ho.1
    exact WP.mono (Whole.copy_digest (copy_src hL h64)
      ⟨hc, a1, a2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun _ h => ⟨h.1, trivial⟩
  · intro u ⟨hc, ho⟩
    have ⟨a1, a2⟩ := copy_args ho.1
    exact WP.mono (Whole.copy_digest (copy_src hL h64)
      ⟨hc, a1, a2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun _ h => ⟨h.1, trivial⟩

/-! ## The expanded-key entry point -/

/-- The public key from the seed's digest at `r1`. -/
def pkLocalE : Contract isa := pkLocalWith 64 fun s t => ∀ seed : List Byte, seed.length = 32 →
  Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 = Spec.Sha512.sha512 seed →
  Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 = Spec.Ed25519.publicKey seed

theorem bodyE_noFrames : (bodyFrom copyExpanded).noFrames = true := by
  simp only [bodyFrom, copyExpanded, Impl.Ed25519.Arm.Whole.callWith, Code.noFrames, Bool.and_self]
  rw [base_noFrames]
  rfl

theorem pkE_ok {s : State} (h : pkLocalE.pre s) :
    WP isa codeExpanded s fun u => abiPreserved s u ∧ pkLocalE.post s u := by
  have hw := Whole.wrap_ok bodyE_noFrames (by decide : 3 ≤ 6) (entry_below h)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt)
    (by intro j hj h4; omega) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (State.addr (s.gpr .r0)) 32 = Spec.Ed25519.encodePoint
      (Spec.Ed25519.pointMul (Spec.Ed25519.prune (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 64))
        Spec.Ed25519.basePoint))
    (fun p hp => by
      have hc : Ctx (lay 64 s) s.gpr p.mem _ := entry_ctx h hp
      have hL : (lay 64 s).Ok := lay_ok h
      have ha : Arguments (lay 64 s) p.mem := entry_args (entry_below h) hp
      exact WP.mono (bodyFrom_ok (copy_ok hc hL ha rfl) hL ha (entry_tbl h hp)
        (congrFun hp.step.syms _)) fun u huo => ⟨by
          simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
            Lay.SCR, Lay.ARGS, Lay.TB, lay, h.2.1, List.cons_append, List.nil_append] using huo.1,
          huo.2⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, fun seed _ hs => ?_⟩
  have hd : Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 64 =
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨State.addr (s.gpr .r1), 64⟩) ?_
      (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r0)) 32 = _
  rw [hp, hd, hs]
  rfl

theorem pkE_ct : ConstantTime isa pkLocalE.pre pkLocalE.pub codeExpanded := by
  refine Whole.wrap_ct (by decide : 3 ≤ 6) (fun _ _ hp => hp.1)
    (fun _ hs => entry_below hs) ?_ (by intro s hs j hj h4; omega) ?_ ?_
  · intro s _
    simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_of_lt s.sp.isLt
  · intro s hs p hp
    have hL : (lay 64 s).Ok := lay_ok hs
    have ha : Arguments (lay 64 s) p.mem := entry_args (entry_below hs) hp
    exact WP.mono (bodyFrom_ok (copy_ok (entry_ctx hs hp) hL ha rfl) hL ha (entry_tbl hs hp)
      (congrFun hp.step.syms _)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq (n := 64) hp
    have hq : Ctx (lay 64 s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay 64 s) q.mem := he ▸ entry_args (entry_below ht) hqb
    have hqw : Tbl (lay 64 s) q.mem := he ▸ entry_tbl ht hqb
    have hqy : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms VG.Impl.Ed25519.Arm.combSym =
        (lay 64 s).T := (congrFun hqb.step.syms _).trans hp.2.2.2.2.symm
    have hL : (lay 64 s).Ok := lay_ok hs
    have hpa' : Arguments (lay 64 s) p.mem := entry_args (entry_below hs) hpa
    exact ⟨(bodyFrom_ct (copy_ct hL rfl hpa' hqa) hL hpa' hqa (entry_tbl hs hpa) hqw _ _ _ _ _ _
      ⟨⟨⟨entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩, congrFun hpa.step.syms _, hqy⟩ ea eb).1, trivial⟩

/-! ## A witness, and the shared contract -/

abbrev pkSpecE : Contract isa :=
  Spec.Ed25519.publicKeyExpandedContract (Arm.abi.withConsts VG.Impl.Ed25519.Arm.combConsts) 280

theorem pkE_pre {s : State} (h : pkSpecE.pre s) : pkLocalE.pre s := by
  have hp : (Spec.Ed25519.publicKeyExpandedContract Arm.abi 280).pre
      (stripConsts VG.Impl.Ed25519.Arm.combConsts s) ∧
      ConstsOk VG.Impl.Ed25519.Arm.combConsts 280 s := pre_consts.mp h
  have h1 := hp.1
  sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
    stackBelow] at h1
  obtain ⟨hb, _, rd, wr, os, oc, sc, ko, ks, kc, no, ns, nc, -⟩ := h1
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

/-- A seed of zeros, and its digest at `0x2000`. -/
def satSeedE : List Byte := List.replicate 32 0
def satDigestE : List Byte := Spec.Sha512.sha512 satSeedE

def satMemE (a : Addr) : Byte :=
  if a.toNat < 0x2000 then 0 else satDigestE[a.toNat - 0x2000]?.getD 0

theorem sat_digestE : Spec.Ed25519.bytesAt satMemE 0x2000 64 = satDigestE := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satDigestE, sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega, ite_false,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

/-- The witness's memory: `satMemE` below the tables, the tables from `0x100000`. -/
def satMemTE : Mem := fun a => if a.toNat < 0x100000 then satMemE a else baseSatMem a

theorem satMemTE_frame : Frame [⟨0, 0x100000⟩] baseSatMem satMemTE := by
  intro x hx
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  rw [show (x - 0 : Addr) = x from by simp] at hn
  simp only [satMemTE, show ¬ x.toNat < 0x100000 by omega, ↓reduceIte]

theorem satMemTE_held : ∀ i < 64 * 192,
    satMemTE.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.Ed25519.Arm.combWords.getD i 0 := by
  intro i hi
  rw [← baseSatMem_held i (by rw [combWords_length]; exact hi)]
  refine satMemTE_frame.readW (r := ⟨0x100000 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    ?_ (by decide)
  intro r hr
  rw [List.mem_singleton.mp hr]
  have e : (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat = 0x100000 + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (0x100000 + 8 * i % 2 ^ 64) % 2 ^ 64 = _
    omega
  refine (Offset.disjoint_of_le (r₁ := ⟨0, 0x100000⟩) ?_ ?_).symm
  · change 0 + 0x100000 ≤ (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat
    omega
  · change (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat + 8 ≤ 2 ^ 64
    omega

theorem satMemTE_digest : Spec.Ed25519.bytesAt satMemTE 0x2000 64 = satDigestE := by
  rw [← sat_digestE]
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have e : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  simp only [satMemTE, e, show 0x2000 + i < 0x100000 by omega, ↓reduceIte]

def satStateE : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := satMemTE
  rd := [⟨0x2000, 64⟩, ⟨0x100000, 98304⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

theorem pkE_sat : pkSpecE.pre satStateE := by
  have held := satMemTE_held
  generalize eqs : satStateE = s
  sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  rw [combWords_length]
  refine ⟨by decide, by decide, by decide, held, by decide, ?_, Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide, by decide, by decide,
    ⟨satSeedE, by simp [satSeedE], satMemTE_digest⟩⟩
  intro r hr
  change r ∈ [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem pkE_implies : pkLocalE.Implies pkSpecE where
  pre _ h := pkE_pre h
  post := by
    intro s s' _ h
    sig_post [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
      combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
      combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨satStateE, pkE_sat⟩

theorem publicKeyExpanded_verified : Verified Arm.target codeExpanded pkSpecE :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => pkE_ok h) pkE_ct (.refl pkE_implies.sat_left))
    pkE_implies

end VG.Proof.Ed25519.Arm.PublicKey
