module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Attempt
import VerifiedGarbage.Proof.Dsa.Generation.SeedSuffix
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: the seeds

`sLoop_vp`: the seeds, one at a time, until one gives a domain (`fStatus`
:= 1, p‖q‖g at `sPacked`), a tape runs out or the seeds do (`fStatus` :=
2), as `Spec.Dsa.generateParameters.attempt` tries them.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

/-- What a geometry's code and the tapes give the search. -/
structure GenOk (G : GP) (g : Geo) (HO : HashOk g.G) (Lq Lp : Impl.Dsa.ProbablePrime.Layout) : Prop where
  okq : PrimeOk Lq g.qCode
  qlay : QLay G g Lq
  okp : PrimeOk Lp g.pCode
  lay : PLay G g Lp
  gcert : CertC G.pLen G.qLen
  hck : CheckOk g.checkCode
  hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32)
  hp : g.pLen = G.pLen
  hq : g.qLen = G.qLen
  hk4 : 4 * g.G.k = G.qLen
  hsb : G.seedsB.length = G.seedsLen
  hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m
  hwl : G.witB.length = G.witLen
  hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen
  hhsb : G.hsB.length = G.hsLen
  hmod : G.hsLen % G.pLen = 0
  h64 : G.hsLen < 2 ^ 64
  smod : G.seedsLen % G.qLen = 0
  s64 : G.seedsLen < 2 ^ 64

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

theorem GenOk.attempt_vp {g : Geo} {HO : HashOk g.G} {Lq Lp : Impl.Dsa.ProbablePrime.Layout}
    (O : GenOk G g HO Lq Lp) {k u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen) :
    VP (St G ((aBase G HO k).setV fUsed (BitVec.ofNat 64 u)) X) g.attempt
      (St G (aOut G HO k (VG.Proof.Dsa.Generation.seedResult (8 * G.pLen) (8 * G.qLen) (seedAt G k) (hsL G)
        (G.witB.drop u))) X) :=
  VG.Proof.Dsa.PPC64LE.Gen.attempt_vp HO O.okq O.qlay O.okp O.lay O.gcert O.hck O.hlq O.hp O.hq O.hk4 O.hsb O.hH
    O.hwl O.hlen O.hhsb O.hmod O.h64 hk hu

/-- The next seed: `fSeed` + `q`, `fSeedLeft` − `q`. -/
theorem sAdv_vp {d : Cfg} {q : Nat} (hq : q < 2 ^ 15) (hS : fSeed ∈ d.LS) (hL : fSeedLeft ∈ d.LS) :
    VP (St G d X) (.block [ld .r3 fSeed, .addi .r3 .r3 q, st .r3 fSeed, ld .r3 fSeedLeft, .subi .r3 .r3 q,
        st .r3 fSeedLeft])
      (St G ((d.setV fSeed (d.V fSeed + BitVec.ofNat 64 q)).setV fSeedLeft (d.V fSeedLeft - BitVec.ofNat 64 q)) X) := by
  rw [show ([ld .r3 fSeed, .addi .r3 .r3 q, st .r3 fSeed, ld .r3 fSeedLeft, .subi .r3 .r3 q, st .r3 fSeedLeft] :
      List Instr) = [ld .r3 fSeed] ++ ([.addi .r3 .r3 q] ++ ([st .r3 fSeed] ++ ([ld .r3 fSeedLeft] ++
        ([.subi .r3 .r3 q] ++ [st .r3 fSeedLeft])))) from rfl]
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = d.V fSeed)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => h.1.gi.slotV hS) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = d.V fSeed + BitVec.ofNat 64 q)
    (r3op_vp (c := fun _ => d) (f := (· + BitVec.ofNat 64 q)) (fun σ s h => h.1.1)
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3]) (.block [.addi .r3 .r3 q]), rfl⟩
      (fun s => exec_addi (d := .r3) (n := .r3) (by decide) hq)
      (fun σ s h => h.2) fun σ s t ⟨⟨_, x⟩, _⟩ h' e => ⟨⟨h', x⟩, e⟩) ?_
  have hL2 : fSeedLeft ∈ (d.setV fSeed (d.V fSeed + BitVec.ofNat 64 q)).LS := List.mem_cons_of_mem _ hL
  refine VP.block_append (G := St G (d.setV fSeed (d.V fSeed + BitVec.ofNat 64 q)) X)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩) ?_
  refine VP.block_append (G := fun σ s => St G (d.setV fSeed (d.V fSeed + BitVec.ofNat 64 q)) X σ s ∧
      s.gpr .r3 = d.V fSeedLeft)
    (ld_vp (c := fun _ => d.setV fSeed (d.V fSeed + BitVec.ofNat 64 q)) (fun σ s h => h.1) (by decide) (by decide)
      (by decide) (fun σ s h => (h.1.gi.slotV hL2).trans (by simp [upd, fSeedLeft, fSeed]))
      fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => St G (d.setV fSeed (d.V fSeed + BitVec.ofNat 64 q)) X σ s ∧
      s.gpr .r3 = d.V fSeedLeft - BitVec.ofNat 64 q)
    (r3op_vp (c := fun _ => d.setV fSeed (d.V fSeed + BitVec.ofNat 64 q)) (f := (· - BitVec.ofNat 64 q))
      (fun σ s h => h.1.1)
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3]) (.block [.subi .r3 .r3 q]), rfl⟩
      (fun s => exec_subi (d := .r3) (n := .r3) (by decide) (Nat.le_of_lt hq)) (fun σ s h => h.2)
      fun σ s t ⟨⟨_, x⟩, _⟩ h' e => ⟨⟨h', x⟩, e⟩) ?_
  exact st_vp (c := fun _ => d.setV fSeed (d.V fSeed + BitVec.ofNat 64 q)) (fun σ s h => h.1.1)
    (varOk_of (by decide)) fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩

/-- Seed `i`'s result, with `u` witnesses read. -/
abbrev sR (G : GP) (u i : Nat) : Option (Option Spec.Dsa.Params × List Byte) :=
  VG.Proof.Dsa.Generation.seedResult (8 * G.pLen) (8 * G.qLen) (seedAt G (i * G.qLen)) (hsL G) (G.witB.drop u)

/-- The witnesses read before seed `i`. -/
def sU (G : GP) (u0 : Nat) : Nat → Nat
  | 0 => u0
  | i + 1 => match sR G (sU G u0 i) i with
    | some (none, rest) => G.witLen - rest.length
    | _ => sU G u0 i

/-- The search's iterations from seed `i`, with `m` seeds after it. -/
def sCount (G : GP) (u0 : Nat) : Nat → Nat → Nat
  | 0, i => i + 1
  | m + 1, i => match sR G (sU G u0 i) i with
    | some (none, _) => sCount G u0 m (i + 1)
    | _ => i + 1

theorem sCount_gt (G : GP) (u0 : Nat) : ∀ m i, i < sCount G u0 m i
  | 0, i => by simp [sCount]
  | m + 1, i => by
    have := sCount_gt G u0 m (i + 1)
    simp only [sCount]; split <;> omega

/-- The spec's search from seed `i`. -/
abbrev sSpec (G : GP) (u0 i : Nat) : Option Spec.Dsa.Params :=
  Spec.Dsa.generateParameters.attempt (8 * G.pLen) (hsL G) (8 * G.qLen)
    (Spec.Dsa.generationChunks G.qLen (G.seedsB.drop (i * G.qLen))) (G.witB.drop (sU G u0 i))

/-- The stage after the search. -/
def sFin (G : GP) : Option Spec.Dsa.Params → Cfg
  | none => ({} : Cfg).setV fStatus 2
  | some a => ({ cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] } : Cfg).setV fStatus 1

/-- The search with `r` iterations left of `N`. -/
abbrev sInv (G : GP) (HO : HashOk Gh) (u0 N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r ≤ G.seedsLen / G.qLen ∧ sCount G u0 (G.seedsLen / G.qLen - (N - r)) (N - r) = N ∧
    sSpec G u0 (N - r) = sSpec G u0 0 ∧ sU G u0 (N - r) ≤ G.witLen) ∧
    St G ((aBase G HO ((N - r) * G.qLen)).setV fUsed (BitVec.ofNat 64 (sU G u0 (N - r)))) X σ s

/-- The spec's step at seed `i`. -/
theorem sSpec_step {G : GP} {u0 i : Nat} (hq0 : 0 < G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hi : i * G.qLen + G.qLen ≤ G.seedsLen) :
    sSpec G u0 i = match sR G (sU G u0 i) i with
      | none => none
      | some (none, rest) => Spec.Dsa.generateParameters.attempt (8 * G.pLen) (hsL G) (8 * G.qLen)
          (Spec.Dsa.generationChunks G.qLen (G.seedsB.drop ((i + 1) * G.qLen))) rest
      | some (some a, _) => some a := by
  rw [sSpec, VG.Proof.Dsa.Generation.generationChunks_step hq0 (by simp only [List.length_drop, hsb]; omega),
    VG.Proof.Dsa.Generation.parameterAttempt_seedResult _ _ _ _ _ _ (by
      simp only [List.length_take, List.length_drop, hsb]; omega), List.drop_drop,
    show (i + 1) * G.qLen = i * G.qLen + G.qLen from Nat.succ_mul _ _]
  rfl

theorem sBody_vp {g : Geo} {HO : HashOk g.G} {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (O : GenOk G g HO Lq Lp) {u0 N : Nat} (r : Nat) :
    VP (sInv G HO u0 N X (r + 1)) (seqs [.block (cmpF fSeedLeft 0),
        .ite (.zero .d .r0) (.block (stImm fStatus 2))
          (seqs [g.attempt, .block [ld .r3 fSeed, .addi .r3 .r3 g.qLen, st .r3 fSeed, ld .r3 fSeedLeft,
            .subi .r3 .r3 g.qLen, st .r3 fSeedLeft]]),
        .block (cmpF fStatus 0)])
      (fun σ s => isa.eval (.zero .d .r0) s = some (decide (0 < r)) ∧ (r = 0 → St G (sFin G (sSpec G u0 0)) X σ s) ∧
        (0 < r → sInv G HO u0 N X r σ s)) := by
  refine VP.intro fun ⟨hr, hi, hc, hR, hu⟩ => ?_
  have hq0 : 0 < G.qLen := by have := O.hlq; omega
  have hq32 : G.qLen ≤ 32 := by have := O.hlq; omega
  have s64 := O.s64
  generalize hMM : G.seedsLen / G.qLen = M at hi hc
  generalize hii : N - (r + 1) = i at hi hc hR hu
  have kL : ∀ j, j ≤ M → j * G.qLen ≤ G.seedsLen := fun j hj =>
    Nat.le_trans (Nat.mul_le_mul_right _ hj) (hMM ▸ Nat.div_mul_le_self _ _)
  rw [O.hq]
  refine VP.seq (G := fun σ s => St G ((aBase G HO (i * G.qLen)).setV fUsed (BitVec.ofNat 64 (sU G u0 i))) X σ s ∧
      isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 (G.seedsLen - i * G.qLen) == BitVec.ofNat 64 0))
    (cmpF_vp (x := BitVec.ofNat 64 (G.seedsLen - i * G.qLen)) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fSeedLeft, fUsed, fStatus]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, e⟩) ?_
  rcases Nat.lt_or_ge i M with hiM | hiM
  · -- A seed: the attempt, then the next.
    have hi1 : i * G.qLen + G.qLen ≤ G.seedsLen := by have := kL (i + 1) hiM; rwa [Nat.succ_mul] at this
    have e0 : (BitVec.ofNat 64 (G.seedsLen - i * G.qLen) == BitVec.ofNat 64 0) = false := by
      refine beq_false_of_ne fun e => ?_
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    obtain ⟨m, hm⟩ : ∃ m, M - i = m + 1 := ⟨M - i - 1, by omega⟩
    rw [hm] at hc
    have step := sSpec_step (u0 := u0) hq0 O.hsb hi1
    have eH : G.seeds + BitVec.ofNat 64 (i * G.qLen) + BitVec.ofNat 64 G.qLen =
        G.seeds + BitVec.ofNat 64 ((i + 1) * G.qLen) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul]
    have eL : BitVec.ofNat 64 (G.seedsLen - i * G.qLen) - BitVec.ofNat 64 G.qLen =
        BitVec.ofNat 64 (G.seedsLen - (i + 1) * G.qLen) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.succ_mul]; omega
    have attempt := O.attempt_vp (X := X) (k := i * G.qLen) (u := sU G u0 i) hi1 hu
    rcases hRi : VG.Proof.Dsa.Generation.seedResult (8 * G.pLen) (8 * G.qLen) (seedAt G (i * G.qLen)) (hsL G)
      (G.witB.drop (sU G u0 i)) with _ | ⟨_ | a, rest⟩ <;> rw [hRi] at attempt <;> simp only [sR, hRi] at step <;>
      simp only [sCount, sR, hRi] at hc
    · -- A tape ran out: `fStatus` = 2.
      have r0 : r = 0 := by omega
      subst r0
      refine VP.seq (G := St G ((((aBase G HO (i * G.qLen)).setV fStatus 2).setV fSeed
          (G.seeds + BitVec.ofNat 64 (i * G.qLen) + BitVec.ofNat 64 G.qLen)).setV fSeedLeft
          (BitVec.ofNat 64 (G.seedsLen - i * G.qLen) - BitVec.ofNat 64 G.qLen)) X)
        (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z)
          (VP.seq (attempt.mono (fun σ s h => h.1.1) fun _ _ h => h)
            ((sAdv_vp (by omega) (by simp [aOut]) (by simp [aOut])).mono (fun _ _ h => h) fun σ s h => by
              simpa [aOut, upd, fSeed, fStatus, fSeedLeft, fUsed] using h))) ?_
      refine cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fSeed, fStatus, fSeedLeft]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      rw [← hR, step]
      refine h'.mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [sFin]))
        (fun _ h' => absurd h' (by simp [sFin])) (fun _ h' => absurd h' (by simp [sFin]))
      change o ∈ [fStatus] at ho
      rw [List.mem_singleton] at ho; subst ho
      exact ⟨by simp, by simp [sFin, upd, fSeed, fStatus, fSeedLeft]⟩
    · -- The next seed.
      have hgt := sCount_gt G u0 m (i + 1)
      have rpos : 0 < r := by omega
      have hNr : N - r = i + 1 := by omega
      have hsuf : G.witB.drop (G.witLen - rest.length) = rest := by
        rw [← O.hwl]
        exact VG.Proof.Dsa.Generation.suffix_drop_length
          ((VG.Proof.Dsa.Generation.seedResult_suffix hRi).trans (List.drop_suffix _ _))
      have hu1 : sU G u0 (i + 1) = G.witLen - rest.length := by simp only [sU, sR, hRi]
      refine VP.seq (G := St G ((((aBase G HO (i * G.qLen)).setV fUsed (BitVec.ofNat 64 (G.witLen - rest.length))).setV
          fSeed (G.seeds + BitVec.ofNat 64 (i * G.qLen) + BitVec.ofNat 64 G.qLen)).setV fSeedLeft
          (BitVec.ofNat 64 (G.seedsLen - i * G.qLen) - BitVec.ofNat 64 G.qLen)) X)
        (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z)
          (VP.seq (attempt.mono (fun σ s h => h.1.1) fun _ _ h => h)
            ((sAdv_vp (by omega) (by simp [aOut]) (by simp [aOut])).mono (fun _ _ h => h) fun σ s h => by
              simpa [aOut, upd, fSeed, fUsed, fSeedLeft, fStatus] using h))) ?_
      refine cmpF_vp (x := BitVec.ofNat 64 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fSeed, fStatus, fSeedLeft, fUsed]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega), fun _ => ?_⟩
      simp only [sInv, hNr, hu1]
      refine ⟨⟨by omega, by omega, by rw [hMM, show M - (i + 1) = m by omega]; exact hc,
        by rw [← hR, step, sSpec, hu1, hsuf], by omega⟩, ?_, x⟩
      refine h'.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      · exact ⟨by simp, by simp [upd, fSeed, fUsed, fSeedLeft]⟩
      · exact ⟨by simp, by simp [upd, fSeed, fStatus, fSeedLeft, fUsed]⟩
      · exact ⟨by simp, by simp [upd, fSeedLeft, fUsed, fStatus, eL]⟩
      · exact ⟨by simp, by simp [upd, fSeed, fSeedLeft, fUsed, fStatus, eH]⟩
    · -- A domain: `fStatus` = 1.
      have r0 : r = 0 := by omega
      subst r0
      refine VP.seq (G := St G ((({ aBase G HO (i * G.qLen) with
          cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] }.setV fStatus 1).setV fSeed
          (G.seeds + BitVec.ofNat 64 (i * G.qLen) + BitVec.ofNat 64 G.qLen)).setV fSeedLeft
          (BitVec.ofNat 64 (G.seedsLen - i * G.qLen) - BitVec.ofNat 64 G.qLen)) X)
        (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z)
          (VP.seq (attempt.mono (fun σ s h => h.1.1) fun _ _ h => h)
            ((sAdv_vp (by omega) (by simp [aOut]) (by simp [aOut])).mono (fun _ _ h => h) fun σ s h => by
              simpa [aOut, upd, fSeed, fStatus, fSeedLeft, fUsed] using h))) ?_
      refine cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fSeed, fStatus, fSeedLeft]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      rw [← hR, step]
      refine h'.mono (fun o ho => ?_) (fun y hy => hy)
        (fun _ h' => absurd h' (by simp [sFin])) (fun _ h' => absurd h' (by simp [sFin]))
      change o ∈ [fStatus] at ho
      rw [List.mem_singleton] at ho; subst ho
      exact ⟨by simp, by simp [sFin, upd, fSeed, fStatus, fSeedLeft]⟩
  · -- No seed left: `fStatus` := 2.
    have hiM' : i = M := by omega
    subst hiM'
    have r0 : r = 0 := by simp only [Nat.sub_self, sCount] at hc; omega
    subst r0
    have hz : G.seedsLen - i * G.qLen = 0 := by
      have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero O.smod); rw [hMM] at this; omega
    have none0 : sSpec G u0 0 = none := by
      rw [← hR, sSpec, VG.Proof.Dsa.Generation.generationChunks_done (by simp only [List.length_drop, O.hsb]; omega)]
      rfl
    refine VP.seq (G := St G (((aBase G HO (i * G.qLen)).setV fUsed (BitVec.ofNat 64 (sU G u0 i))).setV fStatus
        (BitVec.ofNat 64 2)) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => (aBase G HO (i * G.qLen)).setV fUsed (BitVec.ofNat 64 (sU G u0 i)))
        (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, hz] at z; simp at z)) ?_
    refine cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
    rw [none0]
    refine h'.mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [sFin]))
      (fun _ h' => absurd h' (by simp [sFin])) (fun _ h' => absurd h' (by simp [sFin]))
    change o ∈ [fStatus] at ho
    rw [List.mem_singleton] at ho; subst ho
    exact ⟨by simp, by simp [sFin, upd]⟩

/-- The seeds, from the first with `u0` witnesses read. -/
theorem sLoop_vp {g : Geo} {HO : HashOk g.G} {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (O : GenOk G g HO Lq Lp) {u0 : Nat} (hu0 : u0 ≤ G.witLen) :
    VP (St G ((aBase G HO 0).setV fUsed (BitVec.ofNat 64 u0)) X)
      (.loop (seqs [.block (cmpF fSeedLeft 0),
        .ite (.zero .d .r0) (.block (stImm fStatus 2))
          (seqs [g.attempt, .block [ld .r3 fSeed, .addi .r3 .r3 g.qLen, st .r3 fSeed, ld .r3 fSeedLeft,
            .subi .r3 .r3 g.qLen, st .r3 fSeedLeft]]),
        .block (cmpF fStatus 0)]) (.zero .d .r0))
      (St G (sFin G (Spec.Dsa.generateParameters.attempt (8 * G.pLen) (hsL G) (8 * G.qLen)
        (Spec.Dsa.generationChunks G.qLen G.seedsB) (G.witB.drop u0))) X) := by
  have hN := sCount_gt G u0 (G.seedsLen / G.qLen) 0
  generalize hNN : sCount G u0 (G.seedsLen / G.qLen) 0 = N at hN
  have e0 : sSpec G u0 0 = Spec.Dsa.generateParameters.attempt (8 * G.pLen) (hsL G) (8 * G.qLen)
      (Spec.Dsa.generationChunks G.qLen G.seedsB) (G.witB.drop u0) := by simp [sSpec, sU]
  rw [← e0]
  refine VP.mono (F := sInv G HO u0 N X (N - 1 + 1)) ?_ (fun σ s h => ⟨⟨by omega,
    by rw [show N - (N - 1 + 1) = 0 by omega]; exact Nat.zero_le _,
    by rw [show N - (N - 1 + 1) = 0 by omega, Nat.sub_zero]; exact hNN, by rw [show N - (N - 1 + 1) = 0 by omega],
    by rw [show N - (N - 1 + 1) = 0 by omega]; exact hu0⟩, by rw [show N - (N - 1 + 1) = 0 by omega]; simpa [sU] using h⟩)
    fun _ _ h => h
  exact VP.loop (I := sInv G HO u0 N X) (sBody_vp O) _

end

end VG.Proof.Dsa.PPC64LE.Gen
