module

import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Verified
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CopyDigest
public import VerifiedGarbage.Spec.Ed25519.ExpandedKey
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Verified
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CopyDigest
meta import VerifiedGarbage.Spec.Ed25519.ExpandedKey
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.CTCommon
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.CTCommon
public import VerifiedGarbage.Proof.Framework.Contract

/-! # Ed25519 public-key derivation from the seed's cached SHA-512 digest (AArch64)

`codeExpanded` is `code` with its first step, `hash`, replaced by `copyExpanded`: the digest at
the second argument is copied to `frame 192`, where `hash` leaves it. The rest is proven once,
by `bodyFrom_ok` and `bodyFrom_ct`, for both. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey VG.Impl.Ed25519.AArch64.Whole
open VG.Proof.Ed25519 (publicKey_of_sha512_eq sha512_length)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- The digest at `seed`, read only and outside what the derivation writes. -/
theorem copy_src (hL : L.Ok) (h64 : L.seedLen = 64) : Whole.CopySrc L.E L.inputs L.outputs L.seed := by
  have hs : (⟨L.seed, 64⟩ : Region) = L.SEED := by rw [Lay.SEED, h64]
  refine ⟨hs ▸ by simp [Lay.inputs], fun r hr => ?_⟩
  rw [hs]
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (frame_sub L)).symm
  · exact hL.cs.symm

/-- The copy's arguments: the digest in `x1`, `frame 192` in `x15`. -/
theorem copy_args {u : State} (ho : ∀ p ∈ copyArgs, u.gpr p.1 = argValue L p.2) :
    u.gpr .x1 = L.seed ∧ u.gpr .x15 = L.E + BitVec.ofNat 64 192 := by
  have a1 := ho (.x1, .caller 1 0) (by simp [copyArgs])
  simp only [argValue, Lay.value, BitVec.add_zero] at a1
  exact ⟨a1, ho (.x15, .frame 192) (by simp [copyArgs])⟩

theorem copy_ok (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) (h64 : L.seedLen = 64) :
    WP isa copyExpanded t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem (L.E + 192) 64 = Spec.Ed25519.bytesAt m₀ L.seed 64 := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := copyArgs) (by decide) (by decide)
    (by simp [copyArgs]) (by simp [copyArgs, preserved])) fun u ⟨hu, _, ho⟩ => ?_)
  have ⟨a1, a15⟩ := copy_args ho
  exact Whole.copy_digest (copy_src hL h64) ⟨hu, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩

variable {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem copyWords_ct :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L copyArgs)) (.block copyWords) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x1, .x15]) (fun a b h => ⟨h.1.1.sp.trans h.2.1.sp.symm,
    fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.1.2.2 (.x1, .caller 1 0) (by simp [copyArgs])).trans
          (h.2.2.2 (.x1, .caller 1 0) (by simp [copyArgs])).symm
      · exact (h.1.2.2 (.x15, .frame 192) (by simp [copyArgs])).trans
          (h.2.2.2 (.x15, .frame 192) (by simp [copyArgs])).symm⟩) (by taint_decide)

theorem copy_ct (hL : L.Ok) (h64 : L.seedLen = 64) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) copyExpanded
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine (setup_ct hL ha hb copyArgs (by decide) (by decide) (by simp [copyArgs])
    (by simp [copyArgs, preserved]) (by taint_decide)).seq
    (Whole.rel_wp copyWords_ct ?_ ?_)
  · intro u ⟨hc, hy, ho⟩
    have ⟨a1, a15⟩ := copy_args ho
    exact WP.mono_syms (Whole.copy_digest (copy_src hL h64) ⟨hc, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun _ h sy => ⟨h.1, sy ▸ hy, trivial⟩
  · intro u ⟨hc, hy, ho⟩
    have ⟨a1, a15⟩ := copy_args ho
    exact WP.mono_syms (Whole.copy_digest (copy_src hL h64) ⟨hc, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun _ h sy => ⟨h.1, sy ▸ hy, trivial⟩

/-! ## The expanded-key entry point -/

/-- The public key from the seed's digest at `x1`. -/
def pkLocalE : Contract isa := pkLocalWith 64 fun s t => ∀ seed : List Byte, seed.length = 32 →
  Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed →
  Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 32 = Spec.Ed25519.publicKey seed

theorem bodyE_depth : (bodyFrom copyExpanded).aarch64Depth ≤ 1 := by
  have hb := Whole.depth_zero_of_noFrames base_noFrames
  simp only [bodyFrom, copyExpanded, Impl.Ed25519.AArch64.Whole.callWith, Code.aarch64Depth, Nat.max_le, hb]
  omega

theorem pkE_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s : State} (h : pkLocalE.pre s) :
    WP isa codeExpanded s fun u => abiPreserved s u ∧ pkLocalE.post s u := by
  have hw := Whole.wrap_ok bodyE_depth (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (s.gpr .x0) 32 = Spec.Ed25519.encodePoint
      (Spec.Ed25519.pointMul (Spec.Ed25519.prune (Spec.Ed25519.bytesAt m (s.gpr .x1) 64))
        Spec.Ed25519.basePoint))
    (fun p hp => by
      have hc : Ctx (lay 64 s) s.gpr s.v p.mem _ := entry_ctx h hp
      have hL : (lay 64 s).Ok := lay_ok h
      have ha : Arguments (lay 64 s) p.mem := entry_args h hp
      exact WP.mono (bodyFrom_ok (copy_ok hc hL ha rfl) hL ha (entry_syms hp)) fun u huo => ⟨by
          simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
            Lay.SCR, Lay.ARGS, Lay.TB, lay, h.2.1, List.cons_append, List.nil_append] using huo.1,
          huo.2⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, fun seed _ hs => ?_⟩
  have hd : Spec.Ed25519.bytesAt m (s.gpr .x1) 64 = Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨s.gpr .x1, 64⟩) ?_
      (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed25519.bytesAt u.mem (s.gpr .x0) 32 = _
  rw [hp, hd, hs]
  rfl

theorem pkE_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] :
    ConstantTime isa pkLocalE.pre pkLocalE.pub codeExpanded := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    have hL : (lay 64 s).Ok := lay_ok hs
    have ha := entry_args hs hp
    exact WP.mono (bodyFrom_ok (copy_ok (entry_ctx hs hp) hL ha rfl) hL ha (entry_syms hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq (n := 64) hp
    have hq : Ctx (lay 64 s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay 64 s) q.mem := he ▸ entry_args ht hqb
    have hqs : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms Impl.Ed25519.AArch64.combSym =
        (lay 64 s).T := he ▸ entry_syms hqb
    have hL : (lay 64 s).Ok := lay_ok hs
    have hpa' := entry_args hs hpa
    exact ⟨(bodyFrom_ct (copy_ct hL rfl hpa' hqa) hL hpa' hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, entry_syms hpa, trivial⟩, ⟨hq, hqs, trivial⟩⟩ ea eb).1, trivial⟩

/-! ## A witness, and the shared contract -/

open VG.Impl.Ed25519.AArch64 (combSym combWords combConsts)

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
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x9000
  mem := satMemTE
  rd := [⟨0x2000, 64⟩, ⟨0x100000, 49152⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_preE {s : State} (hsp : 352 ≤ s.sp.toNat)
    (hrd : s.rd = [⟨s.gpr .x1, 64⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩])
    (hheld : ∀ i < combWords.length,
      s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0)
    (hfit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ r)
    (hds : Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ ⟨s.sp - 352#64, 352⟩)
    (hrest : (⟨s.gpr .x0, 32⟩ : Region).Disjoint ⟨s.gpr .x1, 64⟩ ∧
      (⟨s.gpr .x0, 32⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (⟨s.gpr .x1, 64⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x0, 32⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x1, 64⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 64 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64)
    (hk : ∃ seed : List Byte, seed.length = 32 ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed) :
    (Spec.Ed25519.publicKeyExpandedContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hrest
  exact ⟨hsp, by rw [hrd]; rfl, hheld, hfit, hdw, hds, by rw [hrd]; rfl, hw, r1, r2, r3, r4, r5, r6, r7,
    r8, r9, hk⟩

theorem satE : ∃ s, (Spec.Ed25519.publicKeyExpandedContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  have hl := combWords_length
  refine ⟨satStateE, spec_preE (by decide) (by rw [hl]; rfl) rfl satMemTE_held (by rw [hl]; decide) ?_
    (by rw [hl]; exact Region.disjoint_of_sep (by decide)) ?_ ⟨satSeedE, by simp [satSeedE], ?_⟩⟩
  · rw [hl]
    simp only [satStateE, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide
  · change Spec.Ed25519.bytesAt satMemTE 0x2000 64 = _
    rw [satMemTE_bytes (by decide), sat_digestE]
    rfl

theorem pkE_implies : pkLocalE.Implies
    (Spec.Ed25519.publicKeyExpandedContract (AArch64.abi.withConsts combConsts) 352) where
  pre s h := by
    sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hsp, hd, held, fit, hdw, hds, ht, hw, os, oc, sc, ko, ks, kc, no, ns, nc, -⟩ := h
    refine ⟨?_, hw, os, oc, sc, ko, ks, kc, no, ns, nc, hsp, held, fit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hds
  post := by
    sig_implies_post [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, pkLocalE, pkLocalWith, below, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
  pub := by
    sig_implies_pub [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, pkLocalE, pkLocalWith, below, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
  sat := satE

theorem publicKeyExpanded_verified [VG.Proof.Ed25519.AArch64.Divstep.Sound] :
    Verified AArch64.target codeExpanded
      (Spec.Ed25519.publicKeyExpandedContract (AArch64.abi.withConsts combConsts) 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => pkE_ok h) pkE_ct (.refl pkE_implies.sat_left))
    pkE_implies

end VG.Proof.Ed25519.AArch64.PublicKey
