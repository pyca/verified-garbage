module

public import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Verified
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Body
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CopyDigest
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Verified
meta import VerifiedGarbage.Spec.Ed25519.ExpandedSign
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Body
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CopyDigest
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # Complete Ed25519 signing with the seed's cached SHA-512 digest (AArch64)

`codeExpanded` is `code` with its first step, `hashSeed`, replaced by
`PublicKey.copyExpanded`: the digest at the second argument is copied to `frame 192`,
where `hashSeed` leaves it. The rest is proven once, by `bodyFrom_ok` and `bodyFrom_ct`, for
both. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.PublicKey (copyArgs copyWords copyExpanded)
open VG.Proof.Ed25519 (sign_of_sha512_eq sha512_length)

variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

/-- The digest at `seed`, read only and outside what signing writes. -/
theorem copy_src (hL : L.Ok) (h64 : L.seedLen = 64) : Whole.CopySrc L.E L.inputs L.outputs L.seed := by
  have hs : (⟨L.seed, 64⟩ : Region) = L.SEED := by rw [Lay.SEED, h64]
  refine ⟨hs ▸ by simp [Lay.inputs], fun r hr => ?_⟩
  have hi : L.SEED ∈ L.inputs := by simp [Lay.inputs]
  rw [hs]
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hL.os _ hi).symm
  · exact hL.sc _ hi
  · exact (hL.ks _ hi).symm
  · exact (hL.ck _ hi).symm

/-- The copy's arguments: the digest in `x1`, `frame 192` in `x15`. -/
theorem copy_args {t : State} (ho : OutArgs L copyArgs t) :
    t.gpr .x1 = L.seed ∧ t.gpr .x15 = L.E + BitVec.ofNat 64 192 := by
  have a1 := ho (.x1, .caller 1 0) (by simp [copyArgs])
  change t.gpr .x1 = L.seed + 0#64 at a1
  rw [BitVec.add_zero] at a1
  exact ⟨a1, ho (.x15, .frame 192) (by simp [copyArgs])⟩

theorem copy_ok (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (h64 : L.seedLen = 64) :
    WP isa copyExpanded s fun t =>
      Ctx L g vec m₀ t ∧ DigestReady L (Spec.Ed25519.bytesAt m₀ L.seed 64) t := by
  refine WP.seq (WP.mono (args_ok hc hL ha (args := copyArgs) (by decide) (by decide)
    (by simp [copyArgs, preserved])) fun t ⟨ht, _, ho⟩ => ?_)
  have ⟨a1, a15⟩ := copy_args ho
  exact Whole.copy_digest (copy_src hL h64) ⟨ht, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩

variable {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem copyWords_ct :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L copyArgs)) (.block copyWords) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x1, .x15]) (fun a b h => ⟨two_sp h, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact args_eq h (p := (.x1, .caller 1 0)) (by simp [copyArgs])
    · exact args_eq h (p := (.x15, .frame 192)) (by simp [copyArgs])⟩) (by taint_decide)

theorem copy_ct (hL : L.Ok) (h64 : L.seedLen = 64) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) copyExpanded
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine (setup_ct hL ha hb copyArgs (by decide) (by decide) (by simp [copyArgs, preserved])
    (by taint_decide)).seq (two_wp copyWords_ct ?_ ?_)
  · intro t hc ho
    have ⟨a1, a15⟩ := copy_args ho
    exact WP.mono (Whole.copy_digest (copy_src hL h64) ⟨hc, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun _ h => ⟨h.1, trivial⟩
  · intro t hc ho
    have ⟨a1, a15⟩ := copy_args ho
    exact WP.mono (Whole.copy_digest (copy_src hL h64) ⟨hc, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun _ h => ⟨h.1, trivial⟩

/-! ## The expanded-key entry point -/

/-- Signing with the seed's digest at `x1` and its public key at `x2`. -/
def signLocalE : Contract isa := signLocalWith 64
  (fun s => ∃ seed : List Byte, seed.length = 32 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 = Spec.Ed25519.publicKey seed)
  (fun s t => ∀ seed : List Byte, seed.length = 32 →
    Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed →
    Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 64 = Spec.Ed25519.sign seed
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat))

theorem expanded_key {s : State} (h : signLocalE.pre s) :
    ∃ seed : List Byte, seed.length = 32 ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 = Spec.Ed25519.publicKey seed := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, _⟩ := h
  exact hk

theorem bodyE_depth (v : Whole.Backend) :
    (bodyFrom copyExpanded v.code v.suffix).aarch64Depth ≤ 1 := by
  have hu := Whole.update_depth v
  have hf := Whole.finalize_depth v
  change (Impl.Sha512.AArch64.Stream.updateWith v.suffix v.code).aarch64Depth ≤ 1 at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith v.suffix v.code).aarch64Depth ≤ 1 at hf
  have hr := Whole.depth_zero_of_noFrames reduce_noFrames
  have hb := Whole.depth_zero_of_noFrames base_noFrames
  have hm := Whole.depth_zero_of_noFrames mul_noFrames
  simp only [bodyFrom, copyExpanded, nonceCode, challengeCode, hashNonce, hashChallenge,
    init, update, finalize, reduce, Impl.Ed25519.AArch64.Whole.callWith, Code.aarch64Depth, Nat.max_le,
    Impl.Sha512.AArch64.Stream.init, hr, hb, hm]
  omega

theorem signE_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] (v : Whole.Backend) {s : State}
    (h : signLocalE.pre s) :
    WP isa (codeExpanded v.code v.suffix) s fun u => abiPreserved s u ∧ signLocalE.post s u := by
  obtain ⟨seed, -, hE, hk⟩ := expanded_key h
  have hw := Whole.wrap_ok (bodyE_depth v) (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m (s.gpr .x1) 64 = Spec.Sha512.sha512 seed ∧
      Spec.Ed25519.bytesAt m' (s.gpr .x0) 64 = Spec.Ed25519.sign seed
        (Spec.Ed25519.bytesAt m (s.gpr .x3) (s.gpr .x4).toNat))
    (fun p hp => by
      have hf := Whole.saved_frame hp
      have hE' := (entry_input h hf (r := ⟨s.gpr .x1, 64⟩) (by rw [h.1]; simp)
        (by change 64 ≤ 2 ^ 64; decide)).trans hE
      have hk' := (entry_input h hf (r := ⟨s.gpr .x2, 32⟩) (by rw [h.1]; simp)
        (by change 32 ≤ 2 ^ 64; decide)).trans hk
      have hc : Ctx (lay 64 s) s.gpr s.v p.mem _ := entry_ctx h hp
      have hL : (lay 64 s).Ok := lay_ok h (by decide)
      have ha : Arguments (lay 64 s) p.mem := entry_args h hp
      exact WP.mono (bodyFrom_ok v (copy_ok hc hL ha rfl) hL ha hE' hk' (entry_syms hp))
        fun u huo => ⟨by
          simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.PK, Lay.MSG,
            Lay.OUT, Lay.SCR, Lay.ARGS, Lay.TB, Whole.ARGS, show BitVec.ofNat 64 256 = (256 : Addr) from rfl,
            lay, h.2.1, List.cons_append, List.nil_append] using huo.1, hE', huo.2⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hE', hp⟩ => ⟨hu, fun seed' _ hs' => ?_⟩
  have hm := entry_input h hf (r := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩) (by rw [h.1]; simp)
    (Nat.le_of_lt (s.gpr .x4).isLt)
  change Spec.Ed25519.bytesAt u.mem (s.gpr .x0) 64 = _
  rw [hp, hm]
  exact sign_of_sha512_eq (hE.symm.trans hs') _

theorem signE_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (v : Whole.Backend) :
    ConstantTime isa signLocalE.pre signLocalE.pub (codeExpanded v.code v.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    obtain ⟨seed, -, hE, hk⟩ := expanded_key hs
    have hf := Whole.saved_frame hp
    have hE' := (entry_input hs hf (r := ⟨s.gpr .x1, 64⟩) (by rw [hs.1]; simp)
      (by change 64 ≤ 2 ^ 64; decide)).trans hE
    have hk' := (entry_input hs hf (r := ⟨s.gpr .x2, 32⟩) (by rw [hs.1]; simp)
      (by change 32 ≤ 2 ^ 64; decide)).trans hk
    have hL := lay_ok hs (by decide)
    have ha := entry_args hs hp
    exact WP.mono (bodyFrom_ok v (copy_ok (entry_ctx hs hp) hL ha rfl) hL ha hE' hk' (entry_syms hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq (n := 64) hp
    have hq : Ctx (lay 64 s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay 64 s) q.mem := he ▸ entry_args ht hqb
    have hqs : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms Impl.Ed25519.AArch64.combSym =
        (lay 64 s).T := he ▸ entry_syms hqb
    have hL := lay_ok hs (by decide)
    have hpa' := entry_args hs hpa
    exact ⟨(bodyFrom_ct v (copy_ct hL rfl hpa' hqa) hL hpa' hqa _ _ _ _ _ _
      ⟨entry_ctx hs hpa, hq, trivial, trivial, entry_syms hpa, hqs⟩ ea eb).1, trivial⟩

/-! ## A witness, and the shared contract -/

open VG.Impl.Ed25519.AArch64 (combSym combWords combConsts)

def satDigest : List Byte := Spec.Sha512.sha512 satSeed

theorem satSeed_length : satSeed.length = 32 := by
  simp only [satSeed, Spec.Ed25519.bytesAt, List.length_map, List.length_range]

/-- The seed's digest at `0x2000` and its public key at `0x3000`. -/
def satMemE (a : Addr) : Byte :=
  if a.toNat < 0x2000 then 0
  else if a.toNat < 0x3000 then satDigest[a.toNat - 0x2000]?.getD 0
  else satKey[a.toNat - 0x3000]?.getD 0

theorem sat_digest : Spec.Ed25519.bytesAt satMemE 0x2000 64 = satDigest := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satDigest, sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega, show 0x2000 + i < 0x3000 from by omega, ite_false, ite_true,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_keyE : Spec.Ed25519.bytesAt satMemE 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x3000 + i < 0x2000 from by omega, show ¬ 0x3000 + i < 0x3000 from by omega, ite_false,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

/-- `satMemE`, and the comb's tables at `0x100000` (irreducible: unfolding it in a definitional
check would evaluate the tables). -/
@[irreducible] def satMemTE : Mem := fun a =>
  if 0x100000 ≤ a.toNat then constMem 0x100000 combWords a else satMemE a

theorem satMemTE_bytes {p : Addr} {n : Nat} (hp : p.toNat + n ≤ 0x100000) :
    Spec.Ed25519.bytesAt satMemTE p n = Spec.Ed25519.bytesAt satMemE p n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  unfold satMemTE
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  simp only [show ¬ 0x100000 ≤ (p.toNat + i) % 2 ^ 64 by omega, ite_false]

theorem satMemTE_held : ∀ i < combWords.length,
    satMemTE.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  have hl := combWords_length
  rw [← constMem_held 0x100000 combWords (by omega) i hi]
  refine Mem.readW_congr fun b hb => ?_
  have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b).toNat = 0x100000 + 8 * i + b := by
    have h0 : (0x100000 : Addr).toNat = 0x100000 := rfl
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat, h0,
      Nat.mod_eq_of_lt (a := 8 * i + b) (by omega)]
    omega
  unfold satMemTE
  simp only [e, show 0x100000 ≤ 0x100000 + 8 * i + b by omega, ↓reduceIte]

def satStateE : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x5 => 0x5000 | _ => 0
  sp := 0x9000
  mem := satMemTE
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩, ⟨0x100000, 49152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_preE {s : State} (hsp : 352 ≤ s.sp.toNat)
    (hrd : s.rd = [⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
      ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 64⟩, ⟨s.gpr .x5, 8192⟩])
    (hheld : ∀ i < combWords.length,
      s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0)
    (hfit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ r)
    (hds : Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ ⟨s.sp - 352#64, 352⟩)
    (hrest : (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x1, 64⟩ ∧
      (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x2, 32⟩ ∧
      (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧
      (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x5, 8192⟩ ∧
      (⟨s.gpr .x1, 64⟩ : Region).Disjoint ⟨s.gpr .x5, 8192⟩ ∧
      (⟨s.gpr .x2, 32⟩ : Region).Disjoint ⟨s.gpr .x5, 8192⟩ ∧
      (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint ⟨s.gpr .x5, 8192⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x0, 64⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x1, 64⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x2, 32⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x5, 8192⟩ ∧
      (s.gpr .x0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 64 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 8192 ≤ 2 ^ 64)
    (hk : ∃ seed : List Byte, seed.length = 32 ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 = Spec.Ed25519.publicKey seed) :
    (Spec.Ed25519.signExpandedContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
    Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17⟩ := hrest
  exact ⟨hsp, by rw [hrd]; rfl, hheld, hfit, hdw, hds, by rw [hrd]; rfl, hw, r1, r2, r3, r4, r5, r6, r7,
    r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, hk⟩

theorem satE : ∃ s, (Spec.Ed25519.signExpandedContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  have hl := combWords_length
  refine ⟨satStateE, spec_preE (by decide) (by rw [hl]; rfl) rfl satMemTE_held (by rw [hl]; decide) ?_
    (by rw [hl]; exact Region.disjoint_of_sep (by decide)) ?_ ⟨satSeed, satSeed_length, ?_, ?_⟩⟩
  · rw [hl]
    simp only [satStateE, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide
  · change Spec.Ed25519.bytesAt satMemTE 0x2000 64 = _
    rw [satMemTE_bytes (by decide), sat_digest]
    rfl
  · change Spec.Ed25519.bytesAt satMemTE 0x3000 32 = _
    rw [satMemTE_bytes (by decide), sat_keyE]
    rfl

theorem signE_implies : signLocalE.Implies
    (Spec.Ed25519.signExpandedContract (AArch64.abi.withConsts combConsts) 352) where
  pre s h := by
    sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hsp, hd, held, fit, hdw, hds, ht, hw, os, op, om, oc, sc, pc, mc, ko, ks, kp, km, kc,
      no, ns, np, nm, nc, hpk⟩ := h
    refine ⟨?_, hw, os, op, om, oc, sc, pc, mc, ko, ks, kp, km, kc, no, ns, np, nm, nc, hsp, hpk,
      held, fit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hds
  post := by
    sig_implies_post [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, signLocalE, signLocalWith, below, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
  pub := by
    sig_implies_pub [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, signLocalE, signLocalWith, below, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
  sat := satE

theorem signExpanded_verified [VG.Proof.Ed25519.AArch64.Divstep.Sound] (v : Whole.Backend) :
    Verified AArch64.target (codeExpanded v.code v.suffix)
      (Spec.Ed25519.signExpandedContract (AArch64.abi.withConsts combConsts) 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signE_ok v h) (signE_ct v) (.refl signE_implies.sat_left))
    signE_implies

end VG.Proof.Ed25519.AArch64.SignCached
