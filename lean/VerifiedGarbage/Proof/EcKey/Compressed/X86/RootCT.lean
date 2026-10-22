module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DescentRound
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.TonelliPowers
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.TonelliSetup
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Tonelli
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressFront
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressContract
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Frame
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.EcKey.Compressed.X86.DescentPower
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Counter
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Exec

/-! # Carry P-224's public counter through existing field calls

The field calls preserve the scratch counter, but their pointer-based
stores cause the syntactic taint analysis to forget it. RelCT combines the
existing taint checks with the already-proved counter invariants.
-/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.X86.Wp

def rootT (c : Cfg) : VG.X86.Taint.T :=
  { regs := .ofList [.esp, .edi], flags := false,
    lens := [2 * c.C.len + 1, 8192], bases := [(.edi, 1, 0)], room := 28 }

def RootPublic (c : Cfg) (s t : State) : Prop :=
  VG.X86.Taint.Wf (rootT c) s ∧ VG.X86.Taint.Wf (rootT c) t ∧
  s.wr = t.wr ∧ s.gpr .edi = t.gpr .edi ∧ s.gpr .esp = t.gpr .esp

def PowerPublic (c : Cfg) (s t : State) : Prop := RootPublic c s t ∧ s.gpr .esi = t.gpr .esi

def descentPrefix (c : Cfg) : Prog isa :=
  .block (copy (2 * c.n) (c.sl T3) (c.sl T0) ++ [.mov .esi (.mem (sc (c.sl T2))), decCounter])

def descentKeeps (c : Cfg) : Prog isa :=
  .seq (Impl.EcKey.Compressed.X86.descentChoose c)
    (.seq (fprog c.SP (Impl.EcKey.Compressed.X86.descentOps c))
      (.block (Impl.EcKey.Compressed.X86.descentCounter c)))

structure LoopState (c : Cfg) (base : Addr) (j : Nat) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkW c.MP' size c.C.p s.mem base
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  counter : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j

def LoopPair (c : Cfg) (j : Nat) (s t : State) : Prop :=
  ∃ base, LoopState c base j s ∧ LoopState c base j t ∧ RootPublic c s t

theorem root_wf_keep {c : Cfg} {s t : State} (hw : VG.X86.Taint.Wf (rootT c) s)
    (K : Keeps powClob s t) : VG.X86.Taint.Wf (rootT c) t where
  lens h := by rw [K.2.2]; exact hw.lens h
  bases p hp := by
    simp only [rootT, List.mem_singleton] at hp
    subst p
    simpa only [K.1 .edi (by decide), VG.X86.Taint.region, K.2.2] using hw.bases (.edi, 1, 0) (by simp [rootT])
  wbases _ h := nomatch h
  args h := by cases h
  argBases _ h := nomatch h
  stk := by simpa only [rootT, VG.X86.Taint.depth, Nat.add_zero, K.1 .esp (by decide)] using hw.stk
  frames _ h := nomatch h
  room h := by
    simpa only [rootT, VG.X86.Taint.depth, VG.X86.Taint.nframes,
      Nat.add_zero, List.drop_zero, VG.X86.Taint.argByte, BitVec.add_zero,
      K.1 .esp (by decide), K.2.2] using hw.room h

theorem RootPublic.keep {c : Cfg} {s t u v : State} (hp : RootPublic c s t)
    (K : Keeps powClob s u) (L : Keeps powClob t v) : RootPublic c u v := by
  rcases hp with ⟨hs, ht, hw, hb, he⟩
  exact ⟨root_wf_keep hs K, root_wf_keep ht L, by rw [K.2.2, L.2.2, hw],
    by rw [K.1 _ (by decide), L.1 _ (by decide), hb],
    by rw [K.1 _ (by decide), L.1 _ (by decide), he]⟩

theorem rel_of_ct {c : Prog isa} {P : State → State → Prop}
    (h : ConstantTime isa (fun _ => True) P c) : RelCT isa P c (fun _ _ => True) :=
  fun _ _ _ _ _ _ hp e₁ e₂ => ⟨h _ _ _ _ _ _ trivial trivial hp e₁ e₂, trivial⟩

theorem descentPrefix_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {j : Nat} {s : State}
    (hs : Scr s base size) (hj : 1 ≤ j)
    (hw : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (descentPrefix c) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (j - 1) ∧ Keeps powClob s t := by
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
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine wp_movS (show readSrc s₁ (.mem (sc (c.sl T2))) = some (s₁.mem.readW (off base (c.sl T2)) 32) by
    simp only [readSrc, State.load32, hs₁.ea (d := c.sl T2) (by omega),
      hs₁.read (by omega : c.sl T2 + 4 ≤ size), ite_true]) fun s₂ U₂ _ => ?_
  have hb₂ : s₂.gpr .esi = BitVec.ofNat 32 j := by
    rw [U₂.gpr, BitVec.eq_of_toNat_eq (O₁.w32
      (by have := sl_apart c (i := T2) (j := T3) (by decide); omega)
      (by have := hs.nowrap; omega)), hw]
  refine wp_decCounter hj hb₂ fun t hb₃ K₃ _ => WP.block_nil
    ⟨hb₃, (K₁.mono (by decide)).trans
      ((U₂.keeps.mono (by decide)).trans (K₃.mono (by decide)))⟩

theorem descentRound_rel {c : Cfg} (hc : CfgOk c) {j : Nat}
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hprefix : ConstantTime isa (fun _ => True) (RootPublic c) (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) (PowerPublic c) (Impl.EcKey.Compressed.X86.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) (RootPublic c) (descentKeeps c)) :
    RelCT isa (LoopPair c j) (Impl.EcKey.Compressed.X86.descentRound c) (fun _ _ => True) := by
  have Hprefix := ((rel_of_ct hprefix).mono (P' := LoopPair c j)
    (fun _ _ ⟨_, _, _, hp⟩ => hp) (fun _ _ _ => trivial)).wpDep
    (F := fun (s t : State) => t.gpr .esi = BitVec.ofNat 32 (j - 1) ∧ Keeps powClob s t)
    (fun s t ⟨base, I, J, _⟩ =>
      ⟨descentPrefix_ok hc I.scr hj I.counter, descentPrefix_ok hc J.scr hj J.counter⟩)
  have Hpower : RelCT isa (LoopPair c j) (Impl.EcKey.Compressed.X86.descentPower c) (fun _ _ => True) := by
    apply RelCT.seq Hprefix
    apply (rel_of_ct hsquare).mono
    · rintro _ _ ⟨_, s, t, ⟨_, _, _, hp⟩, ⟨hs, K⟩, ⟨ht, L⟩⟩
      exact ⟨hp.keep K L, hs.trans ht.symm⟩
    · exact fun _ _ _ => trivial
  have Hpower' := Hpower.wpDep
    (F := fun (s t : State) => Keeps powClob s t)
    (fun s t ⟨base, I, J, _⟩ => ⟨
      WP.mono (descentPower_ok hc I.scr I.mod (I.lt _ (by simp)) hj hj' I.counter)
        (fun _ h => h.1),
      WP.mono (descentPower_ok hc J.scr J.mod (J.lt _ (by simp)) hj hj' J.counter)
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
  refine ⟨R.scr, modP_of hc ?_, ?_, R.lt, R.counter⟩
  · rw [sv_unch R.unch h7 hn (by decide) (apart_slWk (by decide) (by decide : MP ∉ roundSlots))]
    exact I.mod.val
  · rw [sv, sv_unch R.unch h7 hn (by decide)
      (apart_slWk (by decide) (by decide : ONEP ∉ roundSlots))]
    exact I.one

theorem descentLoop_rel {c : Cfg} (hc : CfgOk c) {count : Nat}
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 31)
    (hprefix : ConstantTime isa (fun _ => True) (RootPublic c) (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) (PowerPublic c) (Impl.EcKey.Compressed.X86.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) (RootPublic c) (descentKeeps c)) :
    RelCT isa (LoopPair c count) (.loop (Impl.EcKey.Compressed.X86.descentRound c) .ne) (RootPublic c) := by
  have H : ∀ j, RelCT isa (fun s t => 1 ≤ j ∧ j < 2 ^ 31 ∧ LoopPair c j s t)
      (Impl.EcKey.Compressed.X86.descentRound c) fun u v =>
      isa.eval .ne u = isa.eval .ne v ∧ (isa.eval .ne u = some false → RootPublic c u v) ∧
      (isa.eval .ne u = some true → ∃ k < j, 1 ≤ k ∧ k < 2 ^ 31 ∧ LoopPair c k u v) := by
    intro j
    intro s t ts tt u v hp es et
    rcases hp with ⟨hj, hj', base, I, J, hpub⟩
    obtain ⟨ht, _⟩ := descentRound_rel hc hj hj' hprefix hsquare hrest s t ts tt u v
      ⟨base, I, J, hpub⟩ es et
    obtain ⟨_, u', eu, R⟩ := descentRound_ok hc I.scr I.mod I.lt I.one hj hj' I.counter
    obtain ⟨_, rfl⟩ := Exec.det es eu
    obtain ⟨_, v', ev, S⟩ := descentRound_ok hc J.scr J.mod J.lt J.one hj hj' J.counter
    obtain ⟨_, rfl⟩ := Exec.det et ev
    refine ⟨ht, ?_, fun _ => hpub.keep R.keep S.keep, ?_⟩
    · simp only [VG.X86.eval, R.zf, S.zf]
    · intro he
      have hn : j - 1 ≠ 0 := by
        intro hz
        simp only [VG.X86.eval, R.zf, decide_eq_true hz, Option.map_some, Bool.not_true] at he
        cases he
      exact ⟨j - 1, by omega, by omega, by omega, base, I.step hc R, J.step hc S,
        hpub.keep R.keep S.keep⟩
  exact (RelCT.loop (fun j s t => 1 ≤ j ∧ j < 2 ^ 31 ∧ LoopPair c j s t) H count).mono
    (fun _ _ hp => ⟨hcount, hcount', hp⟩) (fun _ _ h => h)

def prepareRoot (c : Cfg) : Prog isa :=
  .seq (Impl.EcKey.Compressed.X86.tonelliPowers c) (.block (Impl.EcKey.Compressed.X86.tonelliSetup c))

structure RootInput (c : Cfg) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkW c.MP' size c.C.p s.mem base
  rhs : sv c base s Impl.Ecdh.X86.W2 < c.C.p
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p

def RootPair (c : Cfg) (s t : State) : Prop :=
  ∃ base, RootInput c base s ∧ RootInput c base t ∧ RootPublic c s t

theorem prepareRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} (I : RootInput c base s) :
    WP isa (prepareRoot c) s fun t => LoopState c base 95 t ∧ Keeps powClob s t := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  refine WP.seq (WP.mono (tonelliPowers_ok hc I.scr I.mod I.rhs I.one)
    fun s₁ ⟨K₁, U₁, lt₁, ltr₁, _, _⟩ => ?_)
  have hs₁ := I.scr.of_keeps K₁ (by decide)
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
  refine ⟨⟨hs₁.of_keeps K₂ (by decide), modP_of hc ?_, ?_, lt₂, counter₂⟩, K⟩
  · rw [sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact I.mod.val
  · rw [sv, sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact I.one

theorem rootCandidate_rel {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 ≠ 3)
    (hprepare : ConstantTime isa (fun _ => True) (RootPublic c) (prepareRoot c))
    (hprefix : ConstantTime isa (fun _ => True) (RootPublic c) (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) (PowerPublic c) (Impl.EcKey.Compressed.X86.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) (RootPublic c) (descentKeeps c)) :
    RelCT isa (RootPair c) (Impl.EcKey.Compressed.X86.rootCandidate c) (RootPublic c) := by
  have H := ((rel_of_ct hprepare).mono (P' := RootPair c)
    (fun _ _ ⟨_, _, _, hp⟩ => hp) (fun _ _ _ => trivial)).wpDep
    (F := fun (s t : State) => ∃ base, RootInput c base s ∧ LoopState c base 95 t ∧ Keeps powClob s t)
    (by
      rintro s t ⟨base, I, J, _⟩
      exact ⟨WP.mono (prepareRoot_ok hc I) (fun _ ⟨L, K⟩ => ⟨base, I, L, K⟩),
        WP.mono (prepareRoot_ok hc J) (fun _ ⟨L, K⟩ => ⟨base, J, L, K⟩)⟩)
  simp only [Impl.EcKey.Compressed.X86.rootCandidate, hp, ↓reduceIte]
  apply RelCT.assoc
  apply RelCT.seq H
  apply (descentLoop_rel hc (by decide : 1 ≤ 95) (by decide : 95 < 2 ^ 31) hprefix hsquare hrest).mono
  · rintro _ _ ⟨_, s, t, ⟨base, I, J, hp⟩, ⟨b₁, I₁, L, K⟩, ⟨b₂, I₂, R, N⟩⟩
    have h₁ : b₁ = base := by rw [← I₁.scr.edi, I.scr.edi]
    have h₂ : b₂ = base := by rw [← I₂.scr.edi, J.scr.edi]
    subst b₁; subst b₂
    exact ⟨base, L, R, hp.keep K N⟩
  · exact fun _ _ h => h


end VG.Proof.EcKey.Compressed.X86
