module

-- separate module: forsPk's assembled theorems, which only verify's FORS step needs, built apart from its constant-time lemmas

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsPk` is constant time, and `Verified`

The groups' loop and `pkFors` in two runs (`groups_rel`, `pkfin_rel`), the
whole function (`forsPk_ct`); its code has no frames and no depth, and what
the cleanup of its callers needs (`forsPk_side`); a state satisfies its
precondition (`forsPkSat_pre`); `forsPk_verified`, and its calls
(`forsPkcall_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.ForsPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase (relSeq relLoop wpLoop)
open VG.Proof.SlhDsa.AArch64.Fors (Agree As PkPre)
open VG.Proof.MlKem.AArch64 (Only Keep)

variable {p : Params}

theorem gi_start (hF : FP p) {σ : State} {S sig : Addr} {pk a : List Byte} {I : Nat → Nat} {t : State}
    (hK : FK p σ S sig pk a I t) (h22 : t.gpr .x22 = BitVec.ofNat 64 0) : GI p σ S sig pk a I (nG p) t :=
  ⟨by simp only [nG]; have := hF.k1; omega, Nat.le_refl _, hK, by rw [Nat.sub_self, h22],
    by rw [Nat.sub_self]; exact hF.k1, fun _ _ h => absurd h (by omega)⟩

theorem groups_rel (hF : FP p) (hA : As p) {σ₁ σ₂ : State} {S sig : Addr} (c₁ : Ctx p σ₁ S sig)
    (c₂ : Ctx p σ₂ S sig) {pk₁ a₁ pk₂ a₂ : List Byte} {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a)
    (hsp : σ₁.sp = σ₂.sp) (hkp : σ₁.gpr .x2 = σ₂.gpr .x2) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (ht : f.t4 = T.code) :
    RelCT isa (fun a b => GI p σ₁ S sig pk₁ a₁ I (nG p) a ∧ GI p σ₂ S sig pk₂ a₂ I (nG p) b)
      (.loop (Impl.SlhDsa.AArch64.Verify.forsGroup p f) (.nonzero .x .x9)) fun _ _ => True :=
  RelCT.mono (relLoop (fun m => decide (m ≠ 1)) (· - 1)
    (fun m => RelCT.mono (group_rel hF hA c₁ c₂ hIa hsp hkp T ht (4 * (nG p - m))) (fun _ _ h => ⟨h.1.2.2, h.2.2.2⟩)
      fun _ _ h => h)
    (groups_step hF c₁ hIa T ht) (groups_step hF c₂ hIa T ht) (nG p)) (fun _ _ h => h) fun _ _ _ => trivial

/-- `pkFors` and the restores, in two runs with `scratch` in `x19` and the same stack pointer. -/
theorem pkfin_rel (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (name : String) {S : Addr} {sp : BitVec 64} :
    RelCT isa (fun a b => PkPre S sp a ∧ PkPre S sp b)
      (.seq (Impl.SlhDsa.AArch64.Fors.pkFors ⟨p.n, p.len⟩ p.k name T.code)
        (.block (Impl.SlhDsa.AArch64.restoreRegs 2 Impl.SlhDsa.AArch64.Verify.fsaved))) fun _ _ => True := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  obtain ⟨hk, hk0⟩ := Fors.pkB_ok hA
  have eSB : Layout.strideB = 2208 := rfl
  have hB : ∀ t, PkPre S sp t → WP isa (Impl.SlhDsa.AArch64.Fors.pkFors ⟨p.n, p.len⟩ p.k name T.code) t
      fun w => w.gpr .x19 = S ∧ w.sp = sp := fun t ht =>
    Fors.pk_ok hz T name hk hk0 ht.x19 ht.kp ht.scr ht.fit fun t' _ _ hs g _ _ _ =>
      ⟨by rw [g .x19 (by decide) (by decide), ht.x19], by rw [hs, ht.sp]⟩
  refine relSeq (B₁ := fun w => w.gpr .x19 = S ∧ w.sp = sp) (B₂ := fun w => w.gpr .x19 = S ∧ w.sp = sp) ?_ hB hB
    (ct_frestore fun a b ⟨ha, hb⟩ => ⟨by rw [ha.2, hb.2], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.1, hb.1]⟩)
  unfold Impl.SlhDsa.AArch64.Fors.pkFors
  refine relSeq (B₁ := PkPre S sp) (B₂ := PkPre S sp)
    (Fors.ct_pkFields hz hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha.sp, hb.sp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.x19, hb.x19]⟩)
    (fun t ht => ht.fields hz) (fun t ht => ht.fields hz) ?_
  have hw : ∀ t, PkPre S sp t → WP isa (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oB
      Layout.strideB (p.n + 32 + p.k * p.n)) t fun w => w.gpr .x19 = S ∧ w.sp = sp := fun t ht =>
    WP.mono (Fors.tcall_wp T name ⟨p.n, p.len⟩ rfl hn32 (by decide) (by decide) (by decide) (by omega) (by
        rw [Nat.add_mod, Nat.mul_mod, Nat.add_mod p.n]; simp [hn8]) (by omega) (by omega) ht.x19 ht.scr ht.fit)
      fun w ⟨hs, _, g⟩ => ⟨by rw [g .x19 (by decide) (by decide), ht.x19], by rw [hs, ht.sp]⟩
  refine relSeq (B₁ := fun w => w.gpr .x19 = S ∧ w.sp = sp) (B₂ := fun w => w.gpr .x19 = S ∧ w.sp = sp)
    ?_ hw hw (Fors.ct_pkCopy hz hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha.2, hb.2], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.1, hb.1]⟩)
  by_cases hS : ∃ u, PkPre S sp u
  · obtain ⟨u₀, hu₀⟩ := hS
    exact Fors.tcall_ct T name ⟨p.n, p.len⟩ rfl hn32 (fun h => Fors.ct_argsB hz hA h) (by decide) (by decide)
      (by decide) (by omega) (by rw [Nat.add_mod, Nat.mul_mod, Nat.add_mod p.n]; simp [hn8]) (by omega) (by omega)
      hu₀.fit (fun a h => ⟨h.x19, h.scr⟩) (fun b h => ⟨h.x19, h.scr⟩) fun a b h h' => by rw [h.sp, h'.sp]
  · exact RelCT.of_false fun a b ⟨h, _⟩ => hS ⟨a, h⟩

/-! ## Two runs of the whole function -/

theorem forsPk_ct (hz : Sz p) (hp : X86_64.ForsCT.P6 p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (ht : f.t4 = T.code) :
    ConstantTime isa (forsPkContract p).pre (forsPkContract p).pub (Impl.SlhDsa.AArch64.Verify.forsPk p f) := by
  have hF := fp_of hz hp
  have hA : As p := hp
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨hp0, hp1, hp2, hsp, -, hdg⟩ := hpub
  obtain ⟨R₁, ⟨pk₁, a₁, E₁⟩, kp₁⟩ := h₁
  obtain ⟨R₂, ⟨pk₂, a₂, E₂⟩, kp₂⟩ := h₂
  obtain ⟨S, eS⟩ : ∃ S, s₁.gpr .x0 = S := ⟨_, rfl⟩
  obtain ⟨sig, eG⟩ : ∃ sig, s₁.gpr .x1 = sig := ⟨_, rfl⟩
  have c₁ : Ctx p s₁ S sig := ⟨eS, eG, by rw [← eS, ← eG]; exact R₁, kp₁⟩
  have c₂ : Ctx p s₂ S sig := ⟨by rw [← hp0, eS], by rw [← hp1, eG], by rw [← eS, ← eG, hp0, hp1]; exact R₂,
    kp₂⟩
  rw [eS] at E₁
  rw [← hp0, eS] at E₂ hdg
  let I := Ix p s₁.mem S
  have hIa : ∀ i < p.k, I i < 2 ^ p.a := fun i _ => ix_lt _ _ _
  have hI : ∀ i < p.k, Ix p s₂.mem S i = I i := fun i hi => by
    have hia : i * p.a / 8 + 3 ≤ p.mdLen + 2 := by
      rw [hF.md]; have := Nat.mul_le_mul_right p.a (show i + 1 ≤ p.k by omega); rw [Nat.succ_mul] at this
      have := hF.a1; omega
    have hb : ∀ j, j < p.mdLen + 2 → s₂.mem (at' S (Layout.oDigest + j)) = s₁.mem (at' S (Layout.oDigest + j)) :=
      fun j hj => by
        rw [← TreeBase.at_add, ← TreeBase.getD_bytesAt s₁.mem _ hj, ← TreeBase.getD_bytesAt s₂.mem _ hj, hdg]
    simp only [I, Ix, Fors.ixv]
    rw [hb _ (by omega), show Layout.oDigest + i * p.a / 8 + 1 = Layout.oDigest + (i * p.a / 8 + 1) by omega,
      hb _ (by omega), show Layout.oDigest + i * p.a / 8 + 2 = Layout.oDigest + (i * p.a / 8 + 2) by omega,
      hb _ (by omega)]
  have hkp : s₁.gpr .x2 = s₂.gpr .x2 := hp2
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.SlhDsa.AArch64.Verify.forsPk p f) fun _ _ => True := by
    unfold Impl.SlhDsa.AArch64.Verify.forsPk
    refine relSeq (B₁ := GI p s₁ S sig pk₁ a₁ I (nG p)) (B₂ := GI p s₂ S sig pk₂ a₂ I (nG p))
      (ct_fentry hA fun x y ⟨hx, hy⟩ => ⟨by rw [hx, hy, hsp], fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx, hy, hp0]⟩)
      (fun x hx => by rw [hx]; exact WP.mono (entry_ok hF c₁ E₁) fun t ⟨hK, h22⟩ => gi_start hF hK h22)
      (fun y hy => by
        rw [hy]; exact WP.mono (entry_ok hF c₂ E₂) fun t ⟨hK, h22⟩ => gi_start hF (hK.ofI hI) h22) ?_
    refine relSeq (B₁ := fun v => FK p s₁ S sig pk₁ a₁ I v) (B₂ := fun v => FK p s₂ S sig pk₂ a₂ I v)
      (groups_rel hF hA c₁ c₂ hIa hsp hkp T ht)
      (fun x hx => WP.mono (wpLoop _ _ (groups_step hF c₁ hIa T ht) _ hx) fun _ h => h.1)
      (fun y hy => WP.mono (wpLoop _ _ (groups_step hF c₂ hIa T ht) _ hy) fun _ h => h.1) ?_
    rw [ht]
    refine RelCT.mono (P := fun a b => PkPre S s₁.sp a ∧ PkPre S s₁.sp b) (pkfin_rel hz hA T f.t4name)
      (fun a b ⟨ha, hb⟩ => ⟨⟨ha.x19, by rw [ha.x20]; exact c₁.kp, by rw [ha.wr]; exact c₁.scr, c₁.fit, ha.sp⟩,
        ⟨hb.x19, by rw [hb.x20]; exact c₂.kp, by rw [hb.wr]; exact c₂.scr, c₁.fit, by rw [hb.sp, hsp]⟩⟩)
      fun _ _ h => h
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Frames, depth, and the cleanup's side conditions -/

theorem forsPk_noFrames (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) (h : f.t4.noFrames = true) :
    (Impl.SlhDsa.AArch64.Verify.forsPk p f).noFrames = true := by
  simp only [Impl.SlhDsa.AArch64.Verify.forsPk, Impl.SlhDsa.AArch64.Verify.forsGroup,
    Impl.SlhDsa.AArch64.Verify.forsLeaves, Impl.SlhDsa.AArch64.Verify.forsUp,
    Impl.SlhDsa.AArch64.Verify.forsUpLane, Impl.SlhDsa.AArch64.Fors.pkFors, Impl.SlhDsa.AArch64.thashCall,
    Code.noFrames, h, Bool.and_self]

theorem forsPk_depth (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) (h : f.t4.aarch64Depth = 0) :
    (Impl.SlhDsa.AArch64.Verify.forsPk p f).aarch64Depth = 0 := by
  simp only [Impl.SlhDsa.AArch64.Verify.forsPk, Impl.SlhDsa.AArch64.Verify.forsGroup,
    Impl.SlhDsa.AArch64.Verify.forsLeaves, Impl.SlhDsa.AArch64.Verify.forsUp,
    Impl.SlhDsa.AArch64.Verify.forsUpLane, Impl.SlhDsa.AArch64.Fors.pkFors, Impl.SlhDsa.AArch64.thashCall,
    Code.aarch64Depth, h, Nat.max_self]

/-- What the cleanup of `forsPk`'s callers needs of its code (`Scrub.sideAll`). -/
theorem forsPk_side (hz : Sz p) (hp : X86_64.ForsCT.P6 p) (f : Impl.SlhDsa.AArch64.Shake.Fns)
    (hT : Scrub.sideAll (fun i => !i.writesDit) f.t4 = true) :
    Scrub.sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Verify.forsPk p f) = true := by
  simp only [Impl.SlhDsa.AArch64.Verify.forsPk, Impl.SlhDsa.AArch64.Verify.forsGroup,
    Impl.SlhDsa.AArch64.Verify.forsLeaves, Impl.SlhDsa.AArch64.Verify.forsUp,
    Impl.SlhDsa.AArch64.Verify.forsUpLane, Impl.SlhDsa.AArch64.Fors.pkFors, Impl.SlhDsa.AArch64.thashCall,
    Impl.SlhDsa.AArch64.Shake.layout, Impl.SlhDsa.AArch64.Verify.treeT, Impl.SlhDsa.AArch64.Verify.treeSig]
  generalize f.t4 = t4 at hT ⊢
  have hl := hz.len
  generalize p.len = len at hl ⊢
  subst hl
  rcases hp with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    rw [hn, ha, hk] <;> simp only [Scrub.sideAll, hT, Bool.and_true] <;> decide

/-! ## A state satisfying the precondition -/

def pS : Addr := BitVec.ofNat 64 0x100000
def pSig : Addr := BitVec.ofNat 64 0x200000

/-- A state of the precondition: `scratch` and the signature apart, memory zero. -/
def forsPkSat (p : Params) : State where
  gpr r := match r with
    | .x0 => pS | .x1 => pSig | _ => 0
  sp := 0
  mem := fun _ => 0
  rd := [⟨pSig, p.forsSigLen⟩]
  wr := [⟨pS, scratchLen⟩, ⟨pS, 0⟩]

theorem forsPkSat_pre (hz : Sz p) (hp : X86_64.ForsCT.P6 p) : (forsPkContract p).pre (forsPkSat p) := by
  have hF := fp_of hz hp
  have hn32 := hF.n32
  have hSL : p.forsSigLen ≤ 35 * 15 * 32 := by
    simp only [Params.forsSigLen]
    exact Nat.mul_le_mul (Nat.mul_le_mul hF.k (by have := hF.a; omega)) hn32
  have eS : pS.toNat = 0x100000 := rfl
  have eG : pSig.toNat = 0x200000 := rfl
  refine ⟨⟨rfl, rfl, by show pS.toNat + scratchLen ≤ 2 ^ 64; rw [eS]; decide,
    by show pS.toNat + 0 ≤ 2 ^ 64; rw [eS]; decide, fun x h _ => by simp [Region.Contains] at h,
    fun r hr => ?_, fun r hr => ?_⟩,
    ⟨List.replicate p.n 0, List.replicate 16 0, fun k _ => Fors.bytes_zeroF _ _, fun k _ => Fors.bytes_zeroF _ _,
      fun k _ => Fors.bytes_zeroF _ _, fun k _ => Fors.bytes_zeroF _ _⟩, by show (0 : BitVec 64).toNat < 2 ^ 32; decide⟩
  · simp only [List.mem_singleton] at hr; subst hr
    show pSig.toNat + p.forsSigLen ≤ 2 ^ 64; rw [eG]; omega
  · simp only [List.mem_singleton] at hr; subst hr
    exact (Offset.disjoint_of_le (r₁ := ⟨pS, scratchLen⟩) (r₂ := ⟨pSig, p.forsSigLen⟩)
      (by show pS.toNat + scratchLen ≤ pSig.toNat; rw [eS, eG]; decide)
      (by show pSig.toNat + p.forsSigLen ≤ 2 ^ 64; rw [eG]; omega)).symm

/-! ## `Verified`, and calls of `forsPk` -/

/-- `forsPk` meets `forsPkContract`, for the six SHAKE parameter sets and every
implementation of `thash4`. -/
theorem forsPk_verified (hz : Sz p) (hp : X86_64.ForsCT.P6 p) (T : Thash4Impl p.n)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Verify.forsPk p f) (forsPkContract p) :=
  ⟨forsPk_correct hz hp T ht, forsPk_ct hz hp T ht, ⟨forsPkSat p, forsPkSat_pre hz hp⟩⟩

/-- A call of `forsPk`, given its precondition at the call's entry (narrowed
to the regions `rd` and `wr`). -/
theorem forsPkcall_ok (hz : Sz p) (hp : X86_64.ForsCT.P6 p) (T : Thash4Impl p.n)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code) (fn : String) {s : State} {rd wr : List Region}
    (hpre : (forsPkContract p).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      (forsPkContract p).post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call fn (Impl.SlhDsa.AArch64.Verify.forsPk p f)) s Q :=
  WP.callV (forsPk_correct hz hp T ht) hpre hc hw (fun s' h₁ h₂ h₃ h₄ h₅ _ h₇ h₈ => hQ s' h₁ h₂ h₃ h₄ h₅ h₇ h₈)
    (forsPk_noFrames p f (by rw [ht]; exact T.noFrames))

end VG.Proof.SlhDsa.AArch64.ForsPk
