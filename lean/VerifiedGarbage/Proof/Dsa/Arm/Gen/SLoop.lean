module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Attempt
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Intro
import VerifiedGarbage.Proof.Dsa.Generation.SeedSuffix
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the seeds

`sLoop_vp`: the seeds, one at a time, until one gives a domain (`fStatus`
:= 1, p‖q‖g at `sPacked`), a tape runs out or the seeds do (`fStatus` :=
2), as `Spec.Dsa.generateParameters.attempt` tries them.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_dp op2_imm dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Arm.Keys (encodable_lt)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)

/-- What a geometry's code and the tapes give the search. -/
structure GenOk (G : GP) (g : Geo) (HO : HashOk g.G) (n : Nat) : Prop where
  okq : PrimeOk (8 * G.qLen) g.qCode
  okp : PrimeOk (8 * G.pLen) g.pCode
  certs : PArithCerts G.pLen G.qLen
  gcerts : GStepCerts g
  pow : PowOk n g.e g.powCode
  hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32)
  hp : g.pLen = G.pLen
  hq : g.qLen = G.qLen
  hk4 : 4 * g.G.k = G.qLen
  hsb : G.seedsB.length = G.seedsLen
  hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m
  hwl : G.witB.length = G.witLen
  hsize : keyOff + 8 * keyWords (8 * G.pLen) ≤ wa G.pLen
  hsizeq : keyOff + 8 * keyWords (8 * G.qLen) ≤ wa G.pLen
  hb8 : 8 * G.qLen / 8 ≤ wa G.pLen
  hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen
  hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters
  hn : 8 * n = G.pLen
  hpm : g.powMod = modS n
  hpb : g.powBase = baseS n
  hpe : g.powExp = expS n
  hpr : g.powRes = resS n
  hctx : contextBytes n ≤ wa G.pLen
  he4 : 4 * g.e ≤ 8 * n
  he0 : 0 < g.e
  he : 8 * G.pLen - 8 * G.qLen + 1 ≤ 32 * g.e
  hhsb : G.hsB.length = G.hsLen
  hmod : G.hsLen % G.pLen = 0
  h32 : G.hsLen < 2 ^ 32
  smod : G.seedsLen % G.qLen = 0
  s32 : G.seedsLen < 2 ^ 32

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

theorem GenOk.attempt_vp {g : Geo} {HO : HashOk g.G} {n : Nat} (O : GenOk G g HO n) {k u : Nat}
    (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen) :
    VP (St G ((aBase G HO k).setV fUsed (BitVec.ofNat 32 u)) X) g.attempt
      (St G (aOut G HO k (VG.Proof.Dsa.Generation.seedResult (8 * G.pLen) (8 * G.qLen) (seedAt G k) (hsL G)
        (G.witB.drop u))) X) :=
  VG.Proof.Dsa.Arm.Gen.attempt_vp HO O.okq O.okp O.certs O.gcerts O.pow O.hlq O.hp O.hq O.hk4 O.hsb O.hH O.hwl
    O.hsize O.hsizeq O.hb8 O.hlen O.hck O.hn O.hpm O.hpb O.hpe O.hpr O.hctx O.he4 O.he0 O.he O.hhsb O.hmod O.h32 hk hu

/-- The next seed: `fSeed` + `qLen`, `fSeedLeft` − `qLen`. -/
theorem sAdv_vp {d : Cfg} {q : Nat} (hq : q < 256) (hS : fSeed ∈ d.LS) (hL : fSeedLeft ∈ d.LS) :
    VP (St G d X) (VG.Impl.Rsa.Arm.Keys.seqs [.block [ld .r1 fSeed],
        .block [.dp .add .r1 .r1 (.imm (BitVec.ofNat 32 q))], .block (st .r1 fSeed), .block [ld .r1 fSeedLeft],
        .block [.dp .sub .r1 .r1 (.imm (BitVec.ofNat 32 q))], .block (st .r1 fSeedLeft)])
      (St G ((d.setV fSeed (d.V fSeed + BitVec.ofNat 32 q)).setV fSeedLeft (d.V fSeedLeft - BitVec.ofNat 32 q)) X) := by
  have taint1 : ∀ σ₁ σ₂ (s₁ s₂ : State) (P : State → State → Prop) (v : BitVec 32), (P σ₁ s₁ ∧ s₁.gpr .r1 = v) →
      (P σ₂ s₂ ∧ s₂.gpr .r1 = v) → ∀ r ∈ [Reg.r1], s₁.gpr r = s₂.gpr r := fun _ _ _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r1 = d.V fSeed)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => h.1.slotV hS)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r1 = d.V fSeed + BitVec.ofNat 32 q)
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.dp .add .r1 .r1 (.imm (BitVec.ofNat 32 0))]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => taint1 σ₁ σ₂ s₁ s₂ _ _ h₁ h₂)
      fun σ s ⟨⟨h, x⟩, r1⟩ => wp_dp (op2_imm (encodable_lt hq)) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by rw [u.gpr, dpVal, r1]⟩) ?_
  have hL2 : fSeedLeft ∈ (d.setV fSeed (d.V fSeed + BitVec.ofNat 32 q)).LS := List.mem_cons_of_mem _ hL
  refine VP.seq (G := St G (d.setV fSeed (d.V fSeed + BitVec.ofNat 32 q)) X)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨h, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩) ?_
  refine VP.seq (G := fun σ s => St G (d.setV fSeed (d.V fSeed + BitVec.ofNat 32 q)) X σ s ∧
      s.gpr .r1 = d.V fSeedLeft)
    (ld_vp (c := fun _ => d.setV fSeed (d.V fSeed + BitVec.ofNat 32 q)) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => (h.1.slotV hL2).trans (by
        show upd d.V fSeed (d.V fSeed + BitVec.ofNat 32 q) fSeedLeft = _; rw [upd_ne _ _ (by decide)]))
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G (d.setV fSeed (d.V fSeed + BitVec.ofNat 32 q)) X σ s ∧
      s.gpr .r1 = d.V fSeedLeft - BitVec.ofNat 32 q)
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.dp .sub .r1 .r1 (.imm (BitVec.ofNat 32 0))]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => taint1 σ₁ σ₂ s₁ s₂ _ _ h₁ h₂)
      fun σ s ⟨⟨h, x⟩, r1⟩ => wp_dp (op2_imm (encodable_lt hq)) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by rw [u.gpr, dpVal, r1]⟩) ?_
  exact st_vp (c := fun _ => d.setV fSeed (d.V fSeed + BitVec.ofNat 32 q)) (fun σ s h => h.1.1) (by decide)
    (varOk_of (by decide)) fun σ s t ⟨⟨h, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩

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
    St G ((aBase G HO ((N - r) * G.qLen)).setV fUsed (BitVec.ofNat 32 (sU G u0 (N - r)))) X σ s

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

theorem sBody_vp {g : Geo} {HO : HashOk g.G} {n : Nat} (O : GenOk G g HO n) {u0 N : Nat} (r : Nat) :
    VP (sInv G HO u0 N X (r + 1)) (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fSeedLeft 0),
        .ite .eq (.block (stImm fStatus 2))
          (VG.Impl.Rsa.Arm.Keys.seqs [g.attempt, .block [ld .r1 fSeed],
            .block [.dp .add .r1 .r1 (.imm (BitVec.ofNat 32 g.qLen))], .block (st .r1 fSeed), .block [ld .r1 fSeedLeft],
            .block [.dp .sub .r1 .r1 (.imm (BitVec.ofNat 32 g.qLen))], .block (st .r1 fSeedLeft)]),
        .block (cmpF fStatus 0)])
      (fun σ s => isa.eval .eq s = some (decide (0 < r)) ∧ (r = 0 → St G (sFin G (sSpec G u0 0)) X σ s) ∧
        (0 < r → sInv G HO u0 N X r σ s)) := by
  refine VG.Proof.Dsa.Arm.Gen.VP.intro fun ⟨hr, hi, hc, hR, hu⟩ => ?_
  have hq0 : 0 < G.qLen := by have := O.hlq; omega_arith
  have hq32 : G.qLen ≤ 32 := by have := O.hlq; omega_arith
  have s32 := O.s32
  generalize hMM : G.seedsLen / G.qLen = M at hi hc
  generalize hii : N - (r + 1) = i at hi hc hR hu
  have kL : ∀ j, j ≤ M → j * G.qLen ≤ G.seedsLen := fun j hj =>
    Nat.le_trans (Nat.mul_le_mul_right _ hj) (hMM ▸ Nat.div_mul_le_self _ _)
  rw [O.hq]
  refine VP.seq (G := fun σ s => St G ((aBase G HO (i * G.qLen)).setV fUsed (BitVec.ofNat 32 (sU G u0 i))) X σ s ∧
      isa.eval .eq s = some (BitVec.ofNat 32 (G.seedsLen - i * G.qLen) == BitVec.ofNat 32 0))
    (cmpF_vp (x := BitVec.ofNat 32 (G.seedsLen - i * G.qLen)) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fSeedLeft, fUsed, fStatus]))
      fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, e⟩) ?_
  rcases Nat.lt_or_ge i M with hiM | hiM
  · -- A seed: the attempt, then the next.
    have hi1 : i * G.qLen + G.qLen ≤ G.seedsLen := by have := kL (i + 1) hiM; rwa [Nat.succ_mul] at this
    have e0 : (BitVec.ofNat 32 (G.seedsLen - i * G.qLen) == BitVec.ofNat 32 0) = false := by
      refine beq_false_of_ne fun e => ?_
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega_arith
    obtain ⟨m, hm⟩ : ∃ m, M - i = m + 1 := ⟨M - i - 1, by omega_arith⟩
    rw [hm] at hc
    have step := sSpec_step (u0 := u0) hq0 O.hsb hi1
    have eH : G.seeds + BitVec.ofNat 32 (i * G.qLen) + BitVec.ofNat 32 G.qLen =
        G.seeds + BitVec.ofNat 32 ((i + 1) * G.qLen) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul]
    have eL : BitVec.ofNat 32 (G.seedsLen - i * G.qLen) - BitVec.ofNat 32 G.qLen =
        BitVec.ofNat 32 (G.seedsLen - (i + 1) * G.qLen) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.succ_mul]; omega_arith
    have attempt := O.attempt_vp (X := X) (k := i * G.qLen) (u := sU G u0 i) hi1 hu
    rcases hRi : VG.Proof.Dsa.Generation.seedResult (8 * G.pLen) (8 * G.qLen) (seedAt G (i * G.qLen)) (hsL G)
      (G.witB.drop (sU G u0 i)) with _ | ⟨_ | a, rest⟩ <;> rw [hRi] at attempt <;> simp only [sR, hRi] at step <;>
      simp only [sCount, sR, hRi] at hc
    · -- A tape ran out: `fStatus` = 2.
      have r0 : r = 0 := by omega_arith
      subst r0
      refine VP.seq (G := St G ((((aBase G HO (i * G.qLen)).setV fStatus 2).setV fSeed
          (G.seeds + BitVec.ofNat 32 (i * G.qLen) + BitVec.ofNat 32 G.qLen)).setV fSeedLeft
          (BitVec.ofNat 32 (G.seedsLen - i * G.qLen) - BitVec.ofNat 32 G.qLen)) X)
        (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z)
          (VP.seq (attempt.mono (fun σ s h => h.1.1) fun _ _ h => h)
            ((sAdv_vp (by omega_arith) (by simp [aOut]) (by simp [aOut])).mono (fun _ _ h => h) fun σ s h => by
              simpa [aOut, upd, fSeed, fStatus, fSeedLeft, fUsed] using h))) ?_
      refine cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fSeed, fStatus, fSeedLeft]))
        fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      rw [← hR, step]
      refine (h.of_rest R mm).mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [sFin]))
        (fun _ h' => absurd h' (by simp [sFin])) (fun _ h' => absurd h' (by simp [sFin]))
      change o ∈ [fStatus] at ho
      rw [List.mem_singleton] at ho; subst ho
      exact ⟨by simp, by simp [sFin, upd, fSeed, fStatus, fSeedLeft]⟩
    · -- The next seed.
      have hgt := sCount_gt G u0 m (i + 1)
      have rpos : 0 < r := by omega_arith
      have hNr : N - r = i + 1 := by omega_arith
      have hsuf : G.witB.drop (G.witLen - rest.length) = rest := by
        rw [← O.hwl]
        exact VG.Proof.Dsa.Generation.suffix_drop_length
          ((VG.Proof.Dsa.Generation.seedResult_suffix hRi).trans (List.drop_suffix _ _))
      have hu1 : sU G u0 (i + 1) = G.witLen - rest.length := by simp only [sU, sR, hRi]
      refine VP.seq (G := St G ((((aBase G HO (i * G.qLen)).setV fUsed (BitVec.ofNat 32 (G.witLen - rest.length))).setV
          fSeed (G.seeds + BitVec.ofNat 32 (i * G.qLen) + BitVec.ofNat 32 G.qLen)).setV fSeedLeft
          (BitVec.ofNat 32 (G.seedsLen - i * G.qLen) - BitVec.ofNat 32 G.qLen)) X)
        (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z)
          (VP.seq (attempt.mono (fun σ s h => h.1.1) fun _ _ h => h)
            ((sAdv_vp (by omega_arith) (by simp [aOut]) (by simp [aOut])).mono (fun _ _ h => h) fun σ s h => by
              simpa [aOut, upd, fSeed, fUsed, fSeedLeft, fStatus] using h))) ?_
      refine cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fSeed, fStatus, fSeedLeft, fUsed]))
        fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega_arith), fun _ => ?_⟩
      simp only [sInv, hNr, hu1]
      refine ⟨⟨by omega_arith, by omega_arith, by rw [hMM, show M - (i + 1) = m by omega_arith]; exact hc,
        by rw [← hR, step, sSpec, hu1, hsuf], by omega_arith⟩, ?_, x⟩
      refine (h.of_rest R mm).mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      · exact ⟨by simp, by simp [upd, fSeed, fUsed, fSeedLeft]⟩
      · exact ⟨by simp, by simp [upd, fSeed, fStatus, fSeedLeft, fUsed]⟩
      · exact ⟨by simp, by simp [upd, fSeedLeft, fUsed, fStatus, eL]⟩
      · exact ⟨by simp, by simp [upd, fSeed, fSeedLeft, fUsed, fStatus, eH]⟩
    · -- A domain: `fStatus` = 1.
      have r0 : r = 0 := by omega_arith
      subst r0
      refine VP.seq (G := St G ((({ aBase G HO (i * G.qLen) with
          cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] }.setV fStatus 1).setV fSeed
          (G.seeds + BitVec.ofNat 32 (i * G.qLen) + BitVec.ofNat 32 G.qLen)).setV fSeedLeft
          (BitVec.ofNat 32 (G.seedsLen - i * G.qLen) - BitVec.ofNat 32 G.qLen)) X)
        (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z)
          (VP.seq (attempt.mono (fun σ s h => h.1.1) fun _ _ h => h)
            ((sAdv_vp (by omega_arith) (by simp [aOut]) (by simp [aOut])).mono (fun _ _ h => h) fun σ s h => by
              simpa [aOut, upd, fSeed, fStatus, fSeedLeft, fUsed] using h))) ?_
      refine cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fSeed, fStatus, fSeedLeft]))
        fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      rw [← hR, step]
      refine (h.of_rest R mm).mono (fun o ho => ?_) (fun y hy => hy)
        (fun _ h' => absurd h' (by simp [sFin])) (fun _ h' => absurd h' (by simp [sFin]))
      change o ∈ [fStatus] at ho
      rw [List.mem_singleton] at ho; subst ho
      exact ⟨by simp, by simp [sFin, upd, fSeed, fStatus, fSeedLeft]⟩
  · -- No seed left: `fStatus` := 2.
    have hiM' : i = M := by omega_arith
    subst hiM'
    have r0 : r = 0 := by simp only [Nat.sub_self, sCount] at hc; omega_arith
    subst r0
    have hz : G.seedsLen - i * G.qLen = 0 := by
      have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero O.smod); rw [hMM] at this; omega_arith
    have none0 : sSpec G u0 0 = none := by
      rw [← hR, sSpec, VG.Proof.Dsa.Generation.generationChunks_done (by simp only [List.length_drop, O.hsb]; omega_arith)]
      rfl
    refine VP.seq (G := St G (((aBase G HO (i * G.qLen)).setV fUsed (BitVec.ofNat 32 (sU G u0 i))).setV fStatus
        (BitVec.ofNat 32 2)) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => (aBase G HO (i * G.qLen)).setV fUsed (BitVec.ofNat 32 (sU G u0 i)))
        (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, hz] at z; simp at z)) ?_
    refine cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
    rw [none0]
    refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [sFin]))
      (fun _ h' => absurd h' (by simp [sFin])) (fun _ h' => absurd h' (by simp [sFin]))
    change o ∈ [fStatus] at ho
    rw [List.mem_singleton] at ho; subst ho
    exact ⟨by simp, by simp [sFin, upd]⟩

/-- The seeds, from the first with `u0` witnesses read. -/
theorem sLoop_vp {g : Geo} {HO : HashOk g.G} {n : Nat} (O : GenOk G g HO n) {u0 : Nat} (hu0 : u0 ≤ G.witLen) :
    VP (St G ((aBase G HO 0).setV fUsed (BitVec.ofNat 32 u0)) X)
      (.loop (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fSeedLeft 0),
        .ite .eq (.block (stImm fStatus 2))
          (VG.Impl.Rsa.Arm.Keys.seqs [g.attempt, .block [ld .r1 fSeed],
            .block [.dp .add .r1 .r1 (.imm (BitVec.ofNat 32 g.qLen))], .block (st .r1 fSeed), .block [ld .r1 fSeedLeft],
            .block [.dp .sub .r1 .r1 (.imm (BitVec.ofNat 32 g.qLen))], .block (st .r1 fSeedLeft)]),
        .block (cmpF fStatus 0)]) .eq)
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

end VG.Proof.Dsa.Arm.Gen
