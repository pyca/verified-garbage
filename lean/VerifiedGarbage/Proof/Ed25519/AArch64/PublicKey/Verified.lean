import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.CTCommon
import VerifiedGarbage.Proof.Framework.ConstMem

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.CT`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.PublicKey.CTReady`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def initValues : List (Reg × Value) := [(.x0, .caller 2 0)]
def updateValues : List (Reg × Value) :=
  [(.x0, .caller 2 0), (.x1, .const 0), (.x2, .caller 1 0), (.x3, .const 32), (.x4, .caller 2 192)]
def finalizeValues : List (Reg × Value) :=
  [(.x0, .caller 2 0), (.x1, .const 32), (.x2, .frame 192), (.x3, .caller 2 192)]
def baseValues : List (Reg × Value) := [(.x0, .caller 0 0), (.x1, .frame 32), (.x2, .caller 2 0)]

variable {L : Lay} {t : State}

def init_ready (hs : Slots L initValues t) :
    Whole.CallReady (Proof.Sha512.initAArch64 Spec.Sha512.H0_512) L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [initValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre h0, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (hsp : t.sp = L.E) (hs : Slots L updateValues t) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [updateValues])
  have h2 := hs (.x2, .caller 1 0) (by simp [updateValues])
  have h3 := hs (.x3, .const 32) (by simp [updateValues])
  have h4 := hs (.x4, .caller 2 192) (by simp [updateValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h2 h3 h4
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine ⟨Whole.updateRd L.seed 32, Whole.hashWr L.scr, Whole.update_pre h0 h2 h3 h4 hL.sc
    (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hL.cs), ?_, hw⟩
  intro a n hin
  obtain ⟨r, hr, hh⟩ := hin
  rcases List.mem_append.mp hr with hr | hr
  · simp only [Whole.updateRd, List.mem_singleton] at hr
    subst r
    exact ⟨L.SEED, List.mem_append_left _ (by simp [Lay.inputs]), hh⟩
  · exact Whole.covers_writes hw a n ⟨r, hr, hh⟩

def finalize_ready (hL : L.Ok) (hsp : t.sp = L.E) (hs : Slots L finalizeValues t) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [finalizeValues])
  have h2 := hs (.x2, .frame 192) (by simp [finalizeValues])
  have h3 := hs (.x3, .caller 2 192) (by simp [finalizeValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h2 h3
  have hd : Region.Disjoint ⟨L.E + 192, 64⟩ L.SCR :=
    hL.kc.sub_left (Offset.sub_base _ (by decide : 192 + 64 ≤ 336))
  exact ⟨[], Whole.finalizeWr L.scr (L.E + 192), Whole.finalize_pre h0 h2 h3 hd
    (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
    (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes (finalize_writes L), finalize_writes L⟩

def base_ready (hL : L.Ok) (hsy : t.syms Impl.Ed25519.AArch64.combSym = L.T) (hm : TblWords L.T t.mem)
    (hs : Slots L baseValues t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 0 0) (by simp [baseValues])
  have h1 := hs (.x1, .frame 32) (by simp [baseValues])
  have h2 := hs (.x2, .caller 2 0) (by simp [baseValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨L.E + 32, 32⟩, L.TB], L.outputs, base_pre hL ⟨h0, h1, h2⟩ hsy hm, base_covers L, base_writes L⟩

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L initValues))
    (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 (Whole.depth_of_noFrames rfl)
    (fun _ _ _ _ h => init_ready h)
  · intro a b ar aw br bw hsp _ hg
    exact ⟨hg (.x0, .caller 2 0) (by simp [initValues]), hsp⟩
  · simp [initValues, linkRegs]

theorem update_ct (v : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L updateValues))
      (.call (Spec.Sha512.updateScratchApi.name ++ v.suffix) v.update)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb v.update_verified.1 v.update_verified.2.1 (Whole.update_depth v)
    (fun _ hsp _ _ h => update_ready hL hsp h)
  · intro a b ar aw br bw hsp _ hg
    exact ⟨hg (.x0, .caller 2 0) (by simp [updateValues]), hg (.x1, .const 0) (by simp [updateValues]),
      hg (.x2, .caller 1 0) (by simp [updateValues]), hg (.x3, .const 32) (by simp [updateValues]),
      hg (.x4, .caller 2 192) (by simp [updateValues]), hsp⟩
  · simp [updateValues, linkRegs]

theorem finalize_ct (v : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L finalizeValues))
      (.call (Spec.Sha512.finalizeScratchApi.name ++ v.suffix) v.finalize)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb v.finalize_verified.1 v.finalize_verified.2.1 (Whole.finalize_depth v)
    (fun _ hsp _ _ h => finalize_ready hL hsp h)
  · intro a b ar aw br bw hsp _ hg
    exact ⟨hg (.x0, .caller 2 0) (by simp [finalizeValues]), hg (.x1, .const 32) (by simp [finalizeValues]),
      hg (.x2, .frame 192) (by simp [finalizeValues]), hg (.x3, .caller 2 192) (by simp [finalizeValues]), hsp⟩
  · simp [finalizeValues, linkRegs]

theorem base_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L baseValues))
    (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb scalarBase_ok scalarBase_ct (Whole.depth_of_noFrames base_noFrames)
    (fun _ _ hy hm h => base_ready hL hy hm h)
  · intro a b ar aw br bw hsp hy hg
    exact ⟨hsp, hg (.x0, .caller 0 0) (by simp [baseValues]), hg (.x1, .frame 32) (by simp [baseValues]),
      hg (.x2, .caller 2 0) (by simp [baseValues]), hy⟩
  · simp [baseValues, linkRegs]

theorem prune_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block prune)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide)) ?_ ?_
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (prune_step hc (digest := Spec.Ed25519.bytesAt t.mem (L.E + 192) 64) rfl)
      fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (prune_step hc (digest := Spec.Ed25519.bytesAt t.mem (L.E + 192) 64) rfl)
      fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide)) ?_ ?_
  · intro t ⟨hc, hy, _⟩; exact WP.mono_syms (wipe_step hc hL) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, _⟩; exact WP.mono_syms (wipe_step hc hL) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

theorem body_ct (v : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body v.code v.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have i := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb initValues
    (by decide) (by simp [initValues, Whole.valid]) (by simp [initValues])
    (by simp [initValues, preserved]) (by taint_decide)
  have u := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb updateValues
    (by decide) (by simp [updateValues, Whole.valid]) (by simp [updateValues])
    (by simp [updateValues, preserved]) (by taint_decide)
  have f := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb finalizeValues
    (by decide) (by simp [finalizeValues, Whole.valid]) (by simp [finalizeValues])
    (by simp [finalizeValues, preserved]) (by taint_decide)
  have b := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb baseValues
    (by decide) (by simp [baseValues, Whole.valid]) (by simp [baseValues])
    (by simp [baseValues, preserved]) (by taint_decide)
  exact ((i.seq (init_ct hL ha hb)).seq ((u.seq (update_ct v hL ha hb)).seq
    (f.seq (finalize_ct v hL ha hb)))).seq (prune_ct.seq ((b.seq (base_ct hL ha hb)).seq (wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, hsy⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, hsy]

theorem publicKey_ct (v : Whole.Backend) : ConstantTime isa pkLocal.pre pkLocal.pub (code v.code v.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok v (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp) (entry_syms hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    have hqs : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms Impl.Ed25519.AArch64.combSym =
        (lay s).T := he ▸ entry_syms hqb
    exact ⟨(body_ct v (lay_ok hs) (entry_args hs hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, entry_syms hpa, trivial⟩, ⟨hq, hqs, trivial⟩⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

open VG.Impl.Ed25519.AArch64 (combSym combWords combConsts)

def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x9000
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State} (hsp : 352 ≤ s.sp.toNat)
    (hrd : s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩])
    (hheld : ∀ i < combWords.length,
      s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0)
    (hfit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ r)
    (hds : Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ ⟨s.sp - 352#64, 352⟩)
    (hrest : (⟨s.gpr .x0, 32⟩ : Region).Disjoint ⟨s.gpr .x1, 32⟩ ∧
      (⟨s.gpr .x0, 32⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x0, 32⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x1, 32⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64) :
    (Spec.Ed25519.publicKeyContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  sig_pre [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hrest
  exact ⟨hsp, by rw [hrd]; rfl, hheld, hfit, hdw, hds, by rw [hrd]; rfl, hw, r1, r2, r3, r4, r5, r6, r7,
    r8, r9⟩

theorem sat : ∃ s, (Spec.Ed25519.publicKeyContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  have hl := combWords_length
  refine ⟨satState, spec_pre (by decide) (by rw [hl]; rfl) rfl satMem_held (by rw [hl]; decide) ?_
    (by rw [hl]; exact Region.disjoint_of_sep (by decide)) ?_⟩
  · rw [hl]
    simp only [satState, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem pk_implies : pkLocal.Implies
    (Spec.Ed25519.publicKeyContract (AArch64.abi.withConsts combConsts) 352) where
  pre s h := by
    sig_pre [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hsp, hd, held, fit, hdw, hds, ht, hw, os, oc, sc, ko, ks, kc, no, ns, nc⟩ := h
    refine ⟨?_, hw, os, oc, sc, ko, ks, kc, no, ns, nc, hsp, held, fit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hds
  post := by
    sig_implies_post [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
      Spec.Ed25519.scratchWords, pkLocal, below, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
  pub := by
    sig_implies_pub [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
      Spec.Ed25519.scratchWords, pkLocal, below, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
  sat := sat

theorem publicKey_verified (v : Whole.Backend) :
    Verified AArch64.target (code v.code v.suffix)
      (Spec.Ed25519.publicKeyContract (AArch64.abi.withConsts combConsts) 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => publicKey_ok v h) (publicKey_ct v) (.refl pk_implies.sat_left))
    pk_implies

end VG.Proof.Ed25519.AArch64.PublicKey
