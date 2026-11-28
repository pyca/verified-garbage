module

-- separate module: a stage of forsPk's proof, rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsGroup
public import VerifiedGarbage.Proof.SlhDsa.ForsSpec
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `forsPk`: the groups, `T_k` of the roots, and correctness

The groups' loop (`groups_step`), `pkFors` and the restores (`forsPk_wp`),
and the FORS public key it computes, `forsPkFromSig` (`forsPk_correct`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.ForsPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase (in_scr in_scr' disj_scr bytesAt_frame readW_frame)
open VG.Proof.MlKem.AArch64 (Only Keep)

variable {p : Params}

/-! ## The groups -/

/-- The number of groups. -/
abbrev nG (p : Params) : Nat := (p.k + 3) / 4

/-- The groups' loop at measure `m`: the group from `4(G - m)`. -/
def GI (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (I : Nat → Nat) (m : Nat) (u : State) : Prop :=
  1 ≤ m ∧ m ≤ nG p ∧ GP p σ S sig pk a I (4 * (nG p - m)) u

theorem ite_ne (q : Prop) [Decidable q] :
    (BitVec.ofNat 64 (if q then 1 else 0) != 0) = decide q := by
  by_cases h : q <;> simp [h] <;> decide

/-- A pass of the groups' loop. -/
theorem groups_step (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (ht : f.t4 = T.code) (m : Nat) (u : State) (hu : GI p σ S sig pk a I m u) :
    WP isa (Impl.SlhDsa.AArch64.Verify.forsGroup p f) u fun u' =>
      isa.eval (.nonzero .x .x9) u' = some (decide (m ≠ 1)) ∧
      (decide (m ≠ 1) = false → FK p σ S sig pk a I u' ∧ RT p σ S sig pk a I p.k u'.mem) ∧
      (decide (m ≠ 1) = true → m - 1 < m ∧ GI p σ S sig pk a I (m - 1) u') := by
  obtain ⟨hm1, hmG, hg⟩ := hu
  have hk1 := hF.k1
  refine WP.mono (forsGroup_ok hF c hIa T ht hg) fun u' ⟨hK, h22, h9, hR⟩ => ?_
  have hmG' : m ≤ (p.k + 3) / 4 := hmG
  have hiff : (4 * (nG p - m) + 4 < p.k) ↔ m ≠ 1 := by simp only [nG]; omega
  refine ⟨by rw [MlKem.AArch64.eval_nonzero, h9, ite_ne]; exact congrArg some (decide_eq_decide.mpr hiff),
    fun hd => ⟨hK, fun c' hc _ => hR c' hc ?_⟩, fun hd => ?_⟩
  · have : m = 1 := by simpa using hd
    subst this; simp only [nG]; omega
  · have : m ≠ 1 := by simpa using hd
    exact ⟨by omega, by omega, by simp only [nG]; omega, hK, by rw [h22]; congr 1; simp only [nG]; omega,
      by simp only [nG]; omega,
      by rw [show 4 * (nG p - (m - 1)) = 4 * (nG p - m) + 4 by simp only [nG]; omega]; exact hR⟩

/-! ## `pkFors` and the restores -/

/-- Frame 2's slots, in the order of the restores (`x19`, the base, last). -/
def slotsR : List (Reg × Nat) :=
  [(.x20, 1288), (.x21, 1296), (.x22, 1304), (.x23, 1312), (.x24, 1320), (.x25, 1328), (.x26, 1336),
    (.x27, 1344), (.x30, 1352), (.x19, 1280)]

theorem restore_eq : Impl.SlhDsa.AArch64.restoreRegs 2 Impl.SlhDsa.AArch64.Verify.fsaved =
    Spill.restoreCode .x19 slotsR := rfl

/-- The roots, `n` bytes each. -/
theorem bytesAt_flat (m : Mem) (S : Addr) (b n : Nat) :
    ∀ L, bytesAt m (at' S b) (L * n) = (List.range L).flatMap fun i => bytesAt m (at' S (b + i * n)) n
  | 0 => by simp [bytesAt]
  | L + 1 => by
    rw [Nat.add_mul, Nat.one_mul, Fors.bytesAt_cat, bytesAt_flat m S b n L, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-- What `forsPk` leaves. -/
structure FPost (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (I : Nat → Nat) (s : State) : Prop where
  abi : abiPreserved σ s
  env : Env p s.mem S pk a
  frame : Frame (changes p S) σ.mem s.mem
  msg : bytesAt s.mem (at' S Layout.oMsg) p.n = shake256 (pk ++ a ++ Fors.pkF (σ.gpr .x2).toNat ++
    (List.range p.k).flatMap fun i => rootZ p σ.mem sig pk a (σ.gpr .x2).toNat I i p.a) p.n

theorem pkW_changes (hF : FP p) (S : Addr) : ∀ r ∈ Fors.pkW p.n S, ∃ R ∈ changes p S, Region.Sub r R := by
  have hn := hF.n32
  intro r hr
  simp only [Fors.pkW, Wots4.t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
  rcases hr with (rfl | ⟨j, hj, rfl⟩ | rfl) | rfl
  · refine ⟨⟨at' S (Layout.laneB 0 + p.n + 16), Layout.strideB - p.n - 16⟩, ?_, Region.sub_prefix (by
      simp only [Layout.strideB]; omega)⟩
    simp only [changes, laneTails, List.mem_append, List.mem_flatMap, List.mem_range]
    exact .inl (.inr ⟨0, by decide, List.mem_cons_of_mem _ List.mem_cons_self⟩)
  · refine ⟨⟨at' S (Layout.laneB j + p.n + 16), Layout.strideB - p.n - 16⟩, ?_, ?_⟩
    · simp only [changes, laneTails, List.mem_append, List.mem_flatMap, List.mem_range]
      exact .inl (.inr ⟨j, hj, List.mem_cons_of_mem _ List.mem_cons_self⟩)
    · simp only [Layout.laneB, Layout.oB, Layout.strideB]
      exact Offset.sub S (by omega) (by omega)
  · exact ⟨_, by simp [changes], fun _ h => h⟩
  · exact ⟨⟨at' S Layout.oMsg, 64⟩, by simp [changes], Region.sub_prefix (by omega)⟩

theorem pkW_disj (hF : FP p) (S : Addr) {o l : Nat} (h₀ : workUsed ≤ o) (h₁ : o + l ≤ 3136) (h₂ : o + l ≤ 1984 ∨ 2048 ≤ o) :
    ∀ r ∈ Fors.pkW p.n S, Region.Disjoint ⟨at' S o, l⟩ r := by
  have hn := hF.n32
  intro r hr
  simp only [Fors.pkW, Wots4.t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
  rcases hr with (rfl | ⟨j, hj, rfl⟩ | rfl) | rfl
  · rw [laneB0_eq]; exact disj_scr S (by omega) (by omega) (by omega)
  · simp only [Layout.oB, Layout.strideB]; exact disj_scr S (by omega) (by omega) (by omega)
  · have := disj_scr (o := o) (l := l) (o' := 0) (l' := workUsed) S (by omega) (by omega) (by simp only [workUsed]; omega)
    simpa using this
  · rw [oMsg_eq]; exact disj_scr S (by omega) (by omega) (by omega)

theorem forsPk_wp (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    (hE : Env p σ.mem S pk a) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code) :
    WP isa (Impl.SlhDsa.AArch64.Verify.forsPk p f) σ (FPost p σ S sig pk a (Ix p σ.mem S)) := by
  have hn32 := hF.n32
  have hkn := hF.kn
  have hIa : ∀ i < p.k, Ix p σ.mem S i < 2 ^ p.a := fun i _ => ix_lt _ _ _
  unfold Impl.SlhDsa.AArch64.Verify.forsPk
  refine WP.seq (WP.mono (entry_ok hF c hE) fun t₁ ⟨hK₁, h22⟩ => ?_)
  have g₁ : GI p σ S sig pk a (Ix p σ.mem S) (nG p) t₁ :=
    ⟨by simp only [nG]; have := hF.k1; omega, Nat.le_refl _, hK₁, by rw [Nat.sub_self, h22],
      by rw [Nat.sub_self]; exact hF.k1, fun _ _ h => absurd h (by omega)⟩
  refine WP.seq (WP.mono (TreeBase.wpLoop (Q := fun v => FK p σ S sig pk a (Ix p σ.mem S) v ∧
      RT p σ S sig pk a (Ix p σ.mem S) p.k v.mem) (fun m => decide (m ≠ 1)) (· - 1)
    (groups_step hF c hIa T ht) (nG p) g₁) fun t₂ ⟨hK₂, hR₂⟩ => ?_)
  refine WP.seq ?_
  rw [ht]
  simp only [Impl.SlhDsa.AArch64.Shake.layout]
  refine Fors.pk_ok hF.sz T f.t4name (by simp only [Layout.strideB]; omega) hF.k1 hK₂.x19
    (by rw [hK₂.x20]; exact c.kp) (by rw [hK₂.wr]; exact c.scr) c.fit fun t₃ r₃ w₃ sp₃ cs₃ v₃ m₃ f₃ => ?_
  have hsv₃ : Spill.Saved S σ.gpr slotsF t₃.mem :=
    hK₂.saved.frame_in (lo := 1280) (n := 80) slotsF_in f₃ (pkW_disj hF S (by simp only [workUsed]; omega)
      (by omega) (by omega))
  have hb₃ : t₃.gpr .x19 = S := by rw [cs₃ _ (by decide) (by decide), hK₂.x19]
  rw [restore_eq, ← List.append_nil (Spill.restoreCode _ _)]
  refine Spill.restore_ok hb₃ (by decide) (by decide)
    (fun q hq => in_scr' (by rw [w₃, hK₂.wr]; exact c.scr) (by
      simp only [slotsR, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    (hsv₃.sub (by decide)) fun s' hs => WP.block_nil ?_
  have hF₃ : Frame (changes p S) σ.mem t₃.mem := hK₂.frame.trans (f₃.sub (pkW_changes hF S))
  have hE₃ : Env p t₃.mem S pk a := env_keep hK₂.env f₃ (fun k hk r hr => ⟨?_, ?_⟩) hn32
  rotate_left
  · simp only [Fors.pkW, Wots4.t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
    rw [laneA_eq]
    rcases hr with (rfl | ⟨j, hj, rfl⟩ | rfl) | rfl
    · rw [laneB0_eq]; exact disj_scr S (by omega) (by omega) (by omega)
    · simp only [Layout.oB, Layout.strideB]; exact disj_scr S (by omega) (by omega) (by omega)
    · have := disj_scr (o := 3136 + 128 * k) (l := p.n + 16) (o' := 0) (l' := workUsed) S
        (by simp only [workUsed]; omega) (by omega) (by simp only [workUsed]; omega)
      simpa using this
    · rw [oMsg_eq]; exact disj_scr S (by omega) (by omega) (by omega)
  · simp only [Fors.pkW, Wots4.t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
    simp only [Layout.laneB, Layout.oB, Layout.strideB]
    rcases hr with (rfl | ⟨j, hj, rfl⟩ | rfl) | rfl
    · rw [laneB0_eq]; exact disj_scr S (by omega) (by omega) (by omega)
    · simp only [Layout.oB, Layout.strideB]; exact disj_scr S (by omega) (by omega) (by omega)
    · have := disj_scr (o := 3648 + 2208 * k) (l := p.n + 16) (o' := 0) (l' := workUsed) S
        (by simp only [workUsed]; omega) (by omega) (by simp only [workUsed]; omega)
      simpa using this
    · rw [oMsg_eq]; exact disj_scr S (by omega) (by omega) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [hs.sp, sp₃, hK₂.sp], fun r hr => by rw [hs.v, v₃ r hr, hK₂.vcs r hr]⟩,
    by rw [hs.mem]; exact hE₃, by rw [hs.mem]; exact hF₃, ?_⟩
  · by_cases h28 : r = .x28
    · subst h28; rw [hs.other _ (by decide), cs₃ _ (by decide) (by decide), hK₂.x28]
    · exact hs.gpr_of (.inl (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl h28))
  · rw [hs.mem, m₃, hK₂.x20, show Layout.laneB 0 + p.n + 32 = Layout.laneB 0 + p.n + 32 + 0 from rfl,
      bytesAt_flat, show p.n + 16 = p.n + 16 from rfl, Fors.bytesAt_cat, hK₂.env.seedB 0 (by decide),
      hK₂.env.adrsB 0 (by decide)]
    refine congrArg (shake256 · p.n) ?_
    simp only [List.append_assoc]
    refine congrArg (fun X => pk ++ (a ++ (Fors.pkF (σ.gpr .x2).toNat ++ X))) ?_
    exact flatMap_range_congr fun i hi => by rw [Nat.add_zero]; exact hR₂ i hi hi

/-! ## Correctness -/

theorem drop_take_bytes (m : Mem) (b : Addr) {L x y : Nat} (h : x + y ≤ L) :
    ((bytesAt m b L).drop x).take y = bytesAt m (b + BitVec.ofNat 64 x) y := by
  have hl : (((bytesAt m b L).drop x).take y).length = y := by
    simp only [List.length_take, List.length_drop, bytesAt, List.length_map, List.length_range]; omega
  apply List.ext_getElem (by rw [hl]; simp [bytesAt])
  intro i h₁ h₂
  have hi : i < y := by rw [hl] at h₁; exact h₁
  simp only [List.getElem_take, List.getElem_drop, bytesAt, List.getElem_map, List.getElem_range]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The indices are the specification's. -/
theorem ix_eq (hF : FP p) (m : Mem) (S : Addr) {i : Nat} (hi : i < p.k) :
    Ix p m S i = (base2b (mdAt p m S) p.a p.k).getD i 0 := by
  have hl : (mdAt p m S).length = (p.k * p.a + 7) / 8 := by rw [mdAt, TreeBase.bytesAt_length, hF.md]
  have hb : i * p.a / 8 < p.mdLen := by
    rw [hF.md]; have := Nat.mul_le_mul_right p.a (show i + 1 ≤ p.k by omega); rw [Nat.succ_mul] at this
    have := hF.a1; omega
  have gd : ∀ j, j < (mdAt p m S).length → ((mdAt p m S).getD j 0).toNat = (m (at' S (Layout.oDigest + j))).toNat :=
    fun j hj => by
      rw [mdAt, TreeBase.getD_bytesAt _ _ (by rw [mdAt, TreeBase.bytesAt_length] at hj; exact hj), TreeBase.at_add]
  refine (X86_64.Fors.index_eq hl hF.a hi (gd _ (by rw [mdAt, TreeBase.bytesAt_length]; exact hb)).symm
    (fun h => (gd _ h).symm) (fun h => (gd _ h).symm) (m _).isLt (m _).isLt).symm

theorem forsPk_correct (hz : Sz p) (hp : X86_64.ForsCT.P6 p) (T : Thash4Impl p.n)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code) :
    ∀ s, (forsPkContract p).pre s → ∃ t s', Exec isa (Impl.SlhDsa.AArch64.Verify.forsPk p f) s t s' ∧
      abiPreserved s s' ∧ (forsPkContract p).post s s' := by
  have hF := fp_of hz hp
  intro s ⟨R, ⟨pk, a, hE⟩, hkp⟩
  have c : Ctx p s (s.gpr .x0) (s.gpr .x1) := ⟨rfl, rfl, R, hkp⟩
  obtain ⟨t, s', he, q⟩ := forsPk_wp hF c hE T ht
  refine ⟨t, s', he, q.abi, fun pk' a' hE' => ?_⟩
  obtain ⟨e₁, e₂⟩ := TreeBase.env_unique hE hE'
  subst e₁ e₂
  refine ⟨q.env, ?_, q.frame⟩
  have hk32 : p.k * 2 ^ p.a ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.mul_le_mul hF.k hF.pa) (by decide)
  rw [q.msg, forsPkFromSig_eq p (TreeBase.env_a16 hE) hkp hk32]
  simp only [Spec.SlhDsa.T, hz.shake, shakeAdrs, adrsOf, Fors.pkF, List.append_assoc]
  refine congrArg (fun X => Spec.Sha3.shake256 (pk ++ (a ++ (toByte 4 4 ++ (toByte (s.gpr .x2).toNat 4 ++
    (toByte 0 4 ++ (toByte 0 4 ++ X)))))) p.n) (flatMap_range_congr fun i hi => ?_)
  have hsl := forsSig_le hi (Nat.le_refl p.a)
  have hfl : p.forsSigLen = p.k * (p.a + 1) * p.n := by rw [forsSigLen_eq, Nat.mul_comm, Nat.mul_assoc]
  simp only [rootZ]
  have e1 : p.n * (i * (p.a + 1) + 1) = p.n * (i * (p.a + 1)) + p.n := Nat.mul_succ _ _
  rw [ix_eq hF _ _ hi, chunk, drop_take_bytes _ _ (by rw [e1, Nat.mul_comm p.a p.n]; omega),
    drop_take_bytes _ _ (by omega), sigOff, e1]
  simp only [adrsOf, List.append_assoc]

end VG.Proof.SlhDsa.AArch64.ForsPk
