module

-- separate module: the two-run proof of the whole of `forsSign`, rebuilt only when its parts change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsMainFin
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTMain
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCT
public import VerifiedGarbage.Proof.SlhDsa.AArch64.LevelsCT

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign` is constant time, and `Verified`

Two runs of `forsSign` from states of its precondition that agree on its
public data (`scratch`, the signature, the stack pointer) leak the same trace
(`fors_ct`): the prologue by the taint analysis from `x0` and `x1`; then each
run keeps its correctness invariant (`Front`, `TL`), with the same `scratch`,
signature buffer and stack pointer, so the loop of trees runs as many times
in both (`trees_ct`); then `T_k` of the roots and the epilogue (`pk_ct`).
The key pair, the seeds, the digest and the indices are secret. Then
`Verified` (`fors_verified`, with `levels_verified`), and a call of it
(`forscall_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase

variable {p : Params}

/-- What `pkFors` needs, after the trees. -/
theorem TL.pkpre {S SG : Addr} {pk a16 sk : List Byte} {ix : Nat → Nat} {t₀ : State} (M : MC p S SG t₀)
    {tt : Nat} {t : State} (h : TL p S SG pk a16 sk ix t₀ tt t) : PkPre S t₀.sp t :=
  ⟨by rw [h.cs .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      M.x19],
    by rw [h.cs .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
       exact M.kp,
    by rw [h.wr]; exact M.w, M.fit, h.sp⟩

/-- After the prologue, from the entry `σ`. -/
abbrev FT (p : Params) (σ : State) (S SG : Addr) (t₀ : State) : Prop :=
  ∃ pk a16, Front p σ S SG t₀ ∧ TL p S SG pk a16 (bytesAt σ.mem (at' S Layout.oSkSeed) p.n) (ixv σ.mem S p.a) t₀ 0 t₀

/-- After the trees. -/
abbrev FL (p : Params) (σ : State) (S SG : Addr) (w : State) : Prop :=
  ∃ t₀ pk a16, Front p σ S SG t₀ ∧
    TL p S SG pk a16 (bytesAt σ.mem (at' S Layout.oSkSeed) p.n) (ixv σ.mem S p.a) t₀ p.k w

theorem FL.pkpre {σ : State} {S SG : Addr} {w : State} (h : FL p σ S SG w) : PkPre S σ.sp w := by
  obtain ⟨t₀, _, _, hF, hT⟩ := h
  have := hT.pkpre hF.M
  rwa [hF.sp] at this

/-- `forsSign`'s loop of trees, for one run. -/
theorem trees_wp (T : Thash4Impl p.n) (t4name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true)
    {σ : State} {S SG : Addr} {t₀ : State} (h : FT p σ S SG t₀) :
    WP isa (.loop (Impl.SlhDsa.AArch64.Fors.treeBody ⟨p.n, p.len⟩ p.a p.k t4name ln T.code) (.nonzero .x .x9)) t₀
      (FL p σ S SG) := by
  obtain ⟨pk, a16, hF, hT⟩ := h
  exact WP.mono (trees_ok T t4name ln hL hLf hF.M (fun i _ => ixv_lt _ _ _ i) hT) fun w hw => ⟨t₀, pk, a16, hF, hw⟩

/-- Two runs of `forsSign`. -/
theorem fors_ct (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (t4name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true) :
    ConstantTime isa (forsContract p).pre (forsContract p).pub
      (Impl.SlhDsa.AArch64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k t4name ln T.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨hp0, hp1, hp3⟩ := hpub
  obtain ⟨hR₁, ⟨pk₁, a₁, hE₁⟩, hk₁⟩ := h₁
  obtain ⟨hR₂, ⟨pk₂, a₂, hE₂⟩, hk₂⟩ := h₂
  obtain ⟨S, eS⟩ : ∃ S, s₁.gpr .x0 = S := ⟨_, rfl⟩
  obtain ⟨SG, eG⟩ : ∃ SG, s₁.gpr .x1 = SG := ⟨_, rfl⟩
  have eS₂ : s₂.gpr .x0 = S := by rw [← hp0, eS]
  have eG₂ : s₂.gpr .x1 = SG := by rw [← hp1, eG]
  rw [eS, eG] at hR₁
  rw [eS] at hE₁
  rw [eS₂, eG₂] at hR₂
  rw [eS₂] at hE₂
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂)
      (Impl.SlhDsa.AArch64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k t4name ln T.code) fun _ _ => True := by
    unfold Impl.SlhDsa.AArch64.Fors.forsSign
    refine relSeq (B₁ := FT p s₁ S SG) (B₂ := FT p s₂ S SG)
      (ct_pro hA fun x y ⟨hx, hy⟩ => ⟨by rw [hx, hy, hp3], fun r hr => by
        subst hx hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp0
        · exact hp1⟩)
      (fun x hx => by
        subst hx; exact WP.mono (front_ok hA hz eS eG hR₁ hE₁ hk₁) fun t₀ ⟨hF, hT⟩ => ⟨pk₁, a₁, hF, hT⟩)
      (fun y hy => by
        subst hy; exact WP.mono (front_ok hA hz eS₂ eG₂ hR₂ hE₂ hk₂) fun t₀ ⟨hF, hT⟩ => ⟨pk₂, a₂, hF, hT⟩) ?_
    refine relSeq (B₁ := FL p s₁ S SG) (B₂ := FL p s₂ S SG) (RelCT.pointwise ?_) (fun _ h => trees_wp T t4name ln hL hLf h)
      (fun _ h => trees_wp T t4name ln hL hLf h)
      (RelCT.mono (pk_ct hz hA T t4name (S := S) (sp := s₁.sp)) (fun a b ⟨ha, hb⟩ =>
        ⟨ha.pkpre, by have := hb.pkpre; rw [← hp3] at this; exact this⟩) fun _ _ h => h)
    rintro a b ⟨⟨pa, qa, hFa, hTa⟩, ⟨pb, qb, hFb, hTb⟩⟩
    exact RelCT.mono (trees_ct hA T t4name ln hL hLf hFa.M hFb.M (fun i _ => ixv_lt _ _ _ i)
        (fun i _ => ixv_lt _ _ _ i) (by rw [hFa.sp, hFb.sp, hp3]) p.k)
      (fun x y ⟨ex, ey⟩ => by
        subst ex ey
        exact ⟨⟨0, by omega, hFa.M.k1, hTa⟩, ⟨0, by omega, hFb.M.k1, hTb⟩⟩)
      fun _ _ _ => trivial
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified`, and a call of `forsSign` -/

/-- `forsSign` for the SHAKE parameter sets, with any `thash4` and `levels`'s proof. -/
theorem fors_verified' (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (t4name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k t4name ln T.code)
      (forsContract p) :=
  ⟨fors_correct hz hA T t4name ln hL hLf, fors_ct hz hA T t4name ln hL hLf, ⟨forsSat p, forsSat_pre hz hA⟩⟩

/-- `forsSign` for the SHAKE parameter sets, with any `thash4`. -/
theorem fors_verified (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (t4name ln : String) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k t4name ln T.code)
      (forsContract p) :=
  fors_verified' hz hA T t4name ln (Levels.levels_verified hz T t4name) (Levels.levels_noFrames _ _ T.noFrames)

/-- A call of `forsSign`, given its precondition at the call's entry
(narrowed to the regions `rd` and `wr`). -/
theorem forscall_ok (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (t4name ln fn : String) {s : State}
    {rd wr : List Region} (hpre : (forsContract p).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      (forsContract p).post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call fn (Impl.SlhDsa.AArch64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k t4name ln T.code)) s Q :=
  WP.callV (fors_verified hz hA T t4name ln).1 hpre hc hw
    (fun s' h₁ h₂ h₃ h₄ h₅ _ h₇ h₈ => hQ s' h₁ h₂ h₃ h₄ h₅ h₇ h₈)
    (fors_noFrames _ _ _ _ _ T.noFrames (Levels.levels_noFrames _ _ T.noFrames))

end VG.Proof.SlhDsa.AArch64.Fors
