module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DescentRound
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.TonelliPowers
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.TonelliSetup
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Tonelli
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressFront
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressContract
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DescentPower
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Counter
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Carry P-224's public counter through existing field calls

The field calls preserve the scratch counter, but their pointer-based
stores cause the syntactic taint analysis to forget it. RelCT combines the
existing taint checks with the already-proved counter invariants.
-/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr)

def RootPublic (s t : State) : Prop := s.gpr .r12 = t.gpr .r12 ∧ s.gpr .lr = t.gpr .lr

def PowerPublic (s t : State) : Prop := RootPublic s t ∧ s.gpr .r11 = t.gpr .r11

def descentPrefix (c : Cfg) : Prog isa :=
  .block (copy (2 * c.n) (c.sl T3) (c.sl T0) ++ [.ldr .r11 wb (c.sl T2), decCounter])

def descentRest (c : Cfg) : Prog isa :=
  .seq (Impl.EcKey.Compressed.Arm.descentChoose c)
    (.seq (fprog c.SP (Impl.EcKey.Compressed.Arm.descentOps c))
      (.block (Impl.EcKey.Compressed.Arm.descentCounter c)))

structure LoopState (c : Cfg) (base : Addr) (j : Nat) (s : State) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  mod : ModOkW c.MP' size c.C.p s.mem base
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  counter : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j

def LoopPair (c : Cfg) (j : Nat) (s t : State) : Prop :=
  ∃ base, LoopState c base j s ∧ LoopState c base j t ∧ RootPublic s t

theorem RootPublic.keep {s t u v : State} (hp : RootPublic s t)
    (K : Rest powClob s u) (L : Rest powClob t v) : RootPublic u v := by
  rcases hp with ⟨hb, ho⟩
  exact ⟨by rw [K.gpr _ (by decide), L.gpr _ (by decide), hb],
    by rw [K.gpr _ (by decide), L.gpr _ (by decide), ho]⟩

theorem rel_of_ct {c : Prog isa} {P : State → State → Prop}
    (h : ConstantTime isa (fun _ => True) P c) : RelCT isa P c (fun _ _ => True) :=
  fun _ _ _ _ _ _ hp e₁ e₂ => ⟨h _ _ _ _ _ _ trivial trivial hp e₁ e₂, trivial⟩

theorem descentPrefix_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {j : Nat} {s : State}
    (hs : Scr s base size) (hj : 1 ≤ j)
    (hw : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (descentPrefix c) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (j - 1) ∧ Rest powClob s t := by
  have h7 := hc.n10
  have h0 := hc.n0
  have h3 := sl_le c h7 (i := T3) (by decide)
  have h2 := sl_le c h7 (i := T2) (by decide)
  unfold descentPrefix
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs (by omega)
    (by have := sl_le c h7 (i := T0) (by decide); omega)
    (by have := sl_apart c (i := T3) (j := T0) (by decide); omega)) fun s₁ ⟨_, K₁, O₁⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega] at O₁
  have hs₁ := hs.of_rest K₁ (by decide)
  refine wp_ldr (hs₁.off_lt (by omega)) (hs₁.ea (by omega)) (hs₁.read (by omega : c.sl T2 + 4 ≤ size))
    fun s₂ U₂ => ?_
  have hb₂ : s₂.gpr .r11 = BitVec.ofNat 32 j := by
    rw [U₂.gpr, BitVec.eq_of_toNat_eq (O₁.w32
      (by have := sl_apart c (i := T2) (j := T3) (by decide); omega)
      (by have := hs.nowrap; omega)), hw]
  refine wp_decCounter hj hb₂ fun t U₃ => WP.block_nil
    ⟨U₃.gpr, (K₁.mono (by decide)).trans
      ((U₂.rest (by simp [powClob])).trans (U₃.rest (by simp [powClob])))⟩

theorem descentRound_rel {c : Cfg} (hc : CfgOk c) {j : Nat}
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hprefix : ConstantTime isa (fun _ => True) RootPublic (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) PowerPublic (Impl.EcKey.Compressed.Arm.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) RootPublic (descentRest c)) :
    RelCT isa (LoopPair c j) (Impl.EcKey.Compressed.Arm.descentRound c) (fun _ _ => True) := by
  have Hprefix := ((rel_of_ct hprefix).mono (P' := LoopPair c j)
    (fun _ _ ⟨_, _, _, hp⟩ => hp) (fun _ _ _ => trivial)).wpDep
    (F := fun (s t : State) => t.gpr .r11 = BitVec.ofNat 32 (j - 1) ∧ Rest powClob s t)
    (fun s t ⟨base, I, J, _⟩ =>
      ⟨descentPrefix_ok hc I.scr hj I.counter, descentPrefix_ok hc J.scr hj J.counter⟩)
  have Hpower : RelCT isa (LoopPair c j) (Impl.EcKey.Compressed.Arm.descentPower c) (fun _ _ => True) := by
    apply RelCT.seq Hprefix
    apply (rel_of_ct hsquare).mono
    · rintro _ _ ⟨_, s, t, ⟨_, _, _, hp⟩, ⟨hs, K⟩, ⟨ht, L⟩⟩
      exact ⟨hp.keep K L, hs.trans ht.symm⟩
    · exact fun _ _ _ => trivial
  have Hpower' := Hpower.wpDep
    (F := fun (s t : State) => Rest powClob s t)
    (fun s t ⟨base, I, J, _⟩ => ⟨
      WP.mono (descentPower_ok hc I.scr I.far I.mod (I.lt _ (by simp)) hj hj' I.counter)
        (fun _ h => h.1),
      WP.mono (descentPower_ok hc J.scr J.far J.mod (J.lt _ (by simp)) hj hj' J.counter)
        (fun _ h => h.1)⟩)
  apply RelCT.seq Hpower'
  apply (rel_of_ct hrest).mono
  · rintro _ _ ⟨_, _, _, ⟨_, _, _, hp⟩, K, L⟩
    exact hp.keep K L
  · exact fun _ _ _ => trivial

theorem LoopState.step {c : Cfg} (hc : CfgOk c) {base : Addr} {j : Nat} {s t : State}
    (I : LoopState c base j s) (R : DescentRoundPost c base j s t) : LoopState c base (j - 1) t := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  refine ⟨R.scr, I.far.of_rest R.keep, modP_of hc ?_, ?_, R.lt, R.counter⟩
  · rw [sv_unch R.unch h7 hn (by decide) (apart_slWk h7 (by decide) (by decide : MP ∉ roundSlots))]
    exact I.mod.val
  · rw [sv, sv_unch R.unch h7 hn (by decide)
      (apart_slWk h7 (by decide) (by decide : ONEP ∉ roundSlots))]
    exact I.one

theorem descentLoop_rel {c : Cfg} (hc : CfgOk c) {count : Nat}
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 31)
    (hprefix : ConstantTime isa (fun _ => True) RootPublic (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) PowerPublic (Impl.EcKey.Compressed.Arm.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) RootPublic (descentRest c)) :
    RelCT isa (LoopPair c count) (.loop (Impl.EcKey.Compressed.Arm.descentRound c) .ne) RootPublic := by
  have H : ∀ j, RelCT isa (fun s t => 1 ≤ j ∧ j < 2 ^ 31 ∧ LoopPair c j s t)
      (Impl.EcKey.Compressed.Arm.descentRound c) fun u v =>
      isa.eval .ne u = isa.eval .ne v ∧ (isa.eval .ne u = some false → RootPublic u v) ∧
      (isa.eval .ne u = some true → ∃ k < j, 1 ≤ k ∧ k < 2 ^ 31 ∧ LoopPair c k u v) := by
    intro j
    intro s t ts tt u v hp es et
    rcases hp with ⟨hj, hj', base, I, J, hpub⟩
    obtain ⟨ht, _⟩ := descentRound_rel hc hj hj' hprefix hsquare hrest s t ts tt u v
      ⟨base, I, J, hpub⟩ es et
    obtain ⟨_, u', eu, R⟩ := descentRound_ok hc I.scr I.far I.mod I.lt I.one hj hj' I.counter
    obtain ⟨_, rfl⟩ := Exec.det es eu
    obtain ⟨_, v', ev, S⟩ := descentRound_ok hc J.scr J.far J.mod J.lt J.one hj hj' J.counter
    obtain ⟨_, rfl⟩ := Exec.det et ev
    refine ⟨ht, ?_, fun _ => hpub.keep R.keep S.keep, ?_⟩
    · rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, R.zf, S.zf]
    · intro he
      have hn : j - 1 ≠ 0 := by
        intro hz
        rw [VG.Proof.X25519.Arm.eval_ne, R.zf, decide_eq_true hz] at he
        cases he
      exact ⟨j - 1, by omega, by omega, by omega, base, I.step hc R, J.step hc S,
        hpub.keep R.keep S.keep⟩
  exact (RelCT.loop (fun j s t => 1 ≤ j ∧ j < 2 ^ 31 ∧ LoopPair c j s t) H count).mono
    (fun _ _ hp => ⟨hcount, hcount', hp⟩) (fun _ _ h => h)

def prepareRoot (c : Cfg) : Prog isa :=
  .seq (Impl.EcKey.Compressed.Arm.tonelliPowers c) (.block (Impl.EcKey.Compressed.Arm.tonelliSetup c))

structure RootInput (c : Cfg) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  mod : ModOkW c.MP' size c.C.p s.mem base
  rhs : sv c base s Impl.Ecdh.Arm.W2 < c.C.p
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p

def RootPair (c : Cfg) (s t : State) : Prop :=
  ∃ base, RootInput c base s ∧ RootInput c base t ∧ RootPublic s t

theorem prepareRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} (I : RootInput c base s) :
    WP isa (prepareRoot c) s fun t => LoopState c base 95 t ∧ Rest powClob s t := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  refine WP.seq (WP.mono (tonelliPowers_ok hc I.scr I.far I.mod I.rhs I.one)
    fun s₁ ⟨K₁, U₁, lt₁, ltr₁, _, _⟩ => ?_)
  have hs₁ := I.scr.of_rest K₁ (by decide)
  refine WP.mono (tonelliSetup_ok hc hs₁ ltr₁ lt₁) fun s₂ ⟨K₂, U₂, lt₂, counter₂, _, _, _⟩ => ?_
  have U₁₂ : Unch base (candidateWrites c) s.mem s₂.mem :=
    unch_same (U₁.mono (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact power_writes_subset c (.inl rfl) w hw
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem
            ((by decide : ∀ i ∈ [T5], i ∈ candidateSlots) i hi)))
      · exact power_writes_subset c (.inr rfl) w hw))
      (U₂.mono (by
        intro w hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem
          ((by decide : ∀ i ∈ [T0, ACC, T1, T2], i ∈ candidateSlots) i hi)))))
  have K := K₁.trans (K₂.mono (by decide))
  refine ⟨⟨hs₁.of_rest K₂ (by decide), I.far.of_rest K, modP_of hc ?_, ?_, lt₂, counter₂⟩, K⟩
  · rw [sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact I.mod.val
  · rw [sv, sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact I.one

theorem rootCandidate_rel {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 ≠ 3)
    (hprepare : ConstantTime isa (fun _ => True) RootPublic (prepareRoot c))
    (hprefix : ConstantTime isa (fun _ => True) RootPublic (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) PowerPublic (Impl.EcKey.Compressed.Arm.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) RootPublic (descentRest c)) :
    RelCT isa (RootPair c) (Impl.EcKey.Compressed.Arm.rootCandidate c) RootPublic := by
  have H := ((rel_of_ct hprepare).mono (P' := RootPair c)
    (fun _ _ ⟨_, _, _, hp⟩ => hp) (fun _ _ _ => trivial)).wpDep
    (F := fun (s t : State) => ∃ base, RootInput c base s ∧ LoopState c base 95 t ∧ Rest powClob s t)
    (by
      rintro s t ⟨base, I, J, _⟩
      exact ⟨WP.mono (prepareRoot_ok hc I) (fun _ ⟨L, K⟩ => ⟨base, I, L, K⟩),
        WP.mono (prepareRoot_ok hc J) (fun _ ⟨L, K⟩ => ⟨base, J, L, K⟩)⟩)
  simp only [Impl.EcKey.Compressed.Arm.rootCandidate, hp, ↓reduceIte]
  apply RelCT.assoc
  apply RelCT.seq H
  apply (descentLoop_rel hc (by decide : 1 ≤ 95) (by decide : 95 < 2 ^ 31) hprefix hsquare hrest).mono
  · rintro _ _ ⟨_, s, t, ⟨base, I, J, hp⟩, ⟨b₁, I₁, L, K⟩, ⟨b₂, I₂, R, N⟩⟩
    have h₁ : b₁ = base := by rw [← I₁.scr.wb, I.scr.wb]
    have h₂ : b₂ = base := by rw [← I₂.scr.wb, J.scr.wb]
    subst b₁; subst b₂
    exact ⟨base, L, R, hp.keep K N⟩
  · exact fun _ _ h => h

def conversionFront (c : Cfg) : Prog isa :=
  .seq (.seq (.block (c.setupWith Impl.EcKey.Compressed.Arm.args))
    (.block (Impl.EcKey.Compressed.Arm.decompressPeer c)))
    (fprog c.SP (Impl.EcKey.Compressed.Arm.rhsOps c))

def conversionSuffix (c : Cfg) : Prog isa :=
  .seq (Impl.EcKey.Compressed.Arm.selectRoot c)
    (.seq (Impl.EcKey.Compressed.Arm.checkRoot c) (.block (Impl.EcKey.Compressed.Arm.decompressFinish c)))

theorem conversionFront_ok {c : Cfg} (hc : CfgOk c) {s : State}
    (hp : InputPre c (1 + c.C.len) s) :
    WP isa (conversionFront c) s (DecompressFront c s) := by
  have h := decompressFront_ok hc hp (rest := .block []) (fun _ F => WP.block_nil F)
  simpa only [conversionFront, WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using h

theorem rel_assoc_left {a b c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s t ts tt u v hp es et
  cases es with
  | seq ab c₁ =>
    cases ab with
    | seq a₁ b₁ =>
      cases et with
      | seq ab c₂ =>
        cases ab with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          exact ⟨by simpa only [List.append_assoc] using ht, hq⟩

theorem decompress_tonelli_ct {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 ≠ 3)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C}
    (hfront : ConstantTime isa (fun _ => True) (decompressContract c.C root).pub (conversionFront c))
    (hprepare : ConstantTime isa (fun _ => True) RootPublic (prepareRoot c))
    (hprefix : ConstantTime isa (fun _ => True) RootPublic (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) PowerPublic (Impl.EcKey.Compressed.Arm.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) RootPublic (descentRest c))
    (hsuffix : ConstantTime isa (fun _ => True) RootPublic (conversionSuffix c)) :
    ConstantTime isa (decompressContract c.C root).pre (decompressContract c.C root).pub
      (Impl.EcKey.Compressed.Arm.decompress c) := by
  let P := fun s t => (decompressContract c.C root).pre s ∧
    (decompressContract c.C root).pre t ∧ (decompressContract c.C root).pub s t
  have Hfront := ((rel_of_ct hfront).mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ _ => trivial)).wpDep
    (F := fun s t => DecompressFront c s t)
    (by
      rintro s t ⟨hs, ht, _⟩
      have pre {u : State} (h : (decompressContract c.C root).pre u) : InputPre c (1 + c.C.len) u := by
        obtain ⟨hrd, hwr, _, hd, _, _, hpk, hws⟩ := h
        exact ⟨by rw [hrd]; simp [Nat.add_comm], by rw [hwr]; simp,
          by simpa only [Nat.add_comm] using hd, by omega, hws⟩
      exact ⟨conversionFront_ok hc (pre hs), conversionFront_ok hc (pre ht)⟩)
  have Hroot := rootCandidate_rel hc hp hprepare hprefix hsquare hrest
  have Hfront' : RelCT isa P (conversionFront c) (RootPair c) := Hfront.mono
    (fun _ _ h => h) (by
      rintro u v ⟨_, s, t, ⟨_, _, hp⟩, F, G⟩
      rcases hp with ⟨_, ho, _, hb⟩
      have I : RootInput c (ptr s .r2) u := ⟨F.scr, F.far, modP_of hc F.fixed.mp, F.rhs_lt, F.fixed.onep⟩
      have J : RootInput c (ptr s .r2) v := by
        rw [show ptr s .r2 = ptr t .r2 from congrArg State.addr hb]
        exact ⟨G.scr, G.far, modP_of hc G.fixed.mp, G.rhs_lt, G.fixed.onep⟩
      refine ⟨ptr s .r2, I, J, ?_, ?_⟩
      · apply BitVec.eq_of_toNat_eq
        rw [I.scr.wb_toNat, J.scr.wb_toNat]
      · rw [F.out, G.out, ho])
  have Hsuffix := rel_of_ct hsuffix
  have Hrecovery : RelCT isa (RootPair c)
      (.seq (Impl.EcKey.Compressed.Arm.recoverCoordinate c)
        (.block (Impl.EcKey.Compressed.Arm.decompressFinish c))) (fun _ _ => True) := by
    apply rel_assoc_left
    apply RelCT.seq Hroot
    exact rel_assoc_left Hsuffix
  apply RelCT.constantTime
  exact RelCT.assoc (RelCT.assoc (RelCT.seq Hfront' Hrecovery))

end VG.Proof.EcKey.Compressed.Arm
