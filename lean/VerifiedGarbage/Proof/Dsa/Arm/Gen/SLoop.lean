module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Attempt
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Intro
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the controller

`sLoop_vp`: the seeds, one at a time from the cursor `fC`, with `fSeedLeft`
seeds left, until one gives a domain (`fStatus` := 1, p‖q‖g at `sPacked`),
`rand` runs out (2) or the seeds do (3), as `Spec.Dsa.parameterSearch` tries
them (`Proof/Dsa/Generation/RefillSearch.lean`): the stage it ends at is
`cFin`, and its result as the spec states it `cRes`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_dp wp_movw op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Arm.Keys (encodable_lt)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)
open VG.Proof.Dsa.Generation (refillAttempt ranOutResult)

/-- What a geometry's code and the tape give the search. -/
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
  h32 : G.witLen < 2 ^ 32
  hqL : G.qLen = Spec.Dsa.generationQLen G.pLen
  k0 : G.k0 ≤ Spec.Dsa.parameterSeeds

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

theorem GenOk.attempt_vp {g : Geo} {HO : HashOk g.G} {n : Nat} (O : GenOk G g HO n) {k u : Nat} {n' : BitVec 32}
    (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen) :
    VP (St G ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) X) g.attempt
      (St G (aOut G HO k n' (refillAttempt G.pLen G.qLen (seedAt G k) (G.witB.drop u))) X) :=
  VG.Proof.Dsa.Arm.Gen.attempt_vp HO O.okq O.okp O.certs O.gcerts O.pow O.hlq O.hp O.hq O.hk4 O.hwl O.hH O.hwl
    O.hsize O.hsizeq O.hb8 O.hlen O.hck O.hn O.hpm O.hpb O.hpe O.hpr O.hctx O.he4 O.he0 O.he O.h32 hk hu

/-! ## The controller's pieces -/

/-- Whether a seed's octets are left after the cursor `c`. -/
theorem avail_vp {g : Geo} (hq : g.qLen = G.qLen) {d : Cfg} {c : Nat} (hC : fC ∈ d.LS)
    (hCv : d.V fC = BitVec.ofNat 32 c) (hc : c ≤ G.witLen) (h32 : G.witLen < 2 ^ 32) (hq16 : G.qLen < 2 ^ 16) :
    VP (St G d X) g.avail
      (fun σ s => St G d X σ s ∧ isa.eval .eq s = some (decide (G.witLen - c < G.qLen))) := by
  unfold Geo.avail
  rw [hq]
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 G.witLen)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => h.1.fixedV (by simp [fixedWords]))
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 G.witLen) ∧
      s.gpr .r1 = BitVec.ofNat 32 c)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (by decide) (fun σ s h => (h.1.1.slotV hC).trans hCv)
      fun σ s t ⟨⟨h, x⟩, r0⟩ u => ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
        by rw [u.other _ (by decide), r0]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (G.witLen - c) ∧
      s.gpr .r1 = BitVec.ofNat 32 G.qLen)
    (VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
      (.block [.dp .sub .r0 .r0 (.reg .r1), .movw .r1 (BitVec.ofNat 16 0)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.2, h₂.1.2]
        · rw [h₁.2, h₂.2])
      fun σ s ⟨⟨⟨h, x⟩, r0⟩, r1⟩ => wp_dp (op2_reg _ _) fun s₁ u₁ => wp_movw fun t u => WP.block_nil
        ⟨⟨(h.of_rest (u₁.rest (ws := [.r0]) (by simp)) u₁.mem).of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
          ?_, by rw [u.gpr, setWidth_ofNat16 hq16]⟩) ?_
  · rw [u.other _ (by decide), u₁.gpr, dpVal, r0, r1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  exact less_vp (x := BitVec.ofNat 32 (G.witLen - c)) (y := BitVec.ofNat 32 G.qLen) (fun σ s h => h.2.1)
    (fun σ s h => h.2.2) fun σ s t ⟨⟨h, x⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by
      rw [e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]⟩

/-- The seed at the cursor `c`: `fSeed` := `rand + c`, its witnesses from `c + q_len`. -/
theorem seedStart_vp {g : Geo} (hq : g.qLen = G.qLen) {d : Cfg} {c : Nat} (hC : fC ∈ d.LS)
    (hCv : d.V fC = BitVec.ofNat 32 c) (hq8 : G.qLen < 256) :
    VP (St G d X) g.seedStart
      (St G ((d.setV fSeed (G.seeds + BitVec.ofNat 32 c)).setV fUsed (BitVec.ofNat 32 (c + G.qLen))) X) := by
  unfold Geo.seedStart
  rw [hq]
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = G.wit)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => h.1.fixedV (by simp [fixedWords]))
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G d X σ s ∧ s.gpr .r0 = G.wit) ∧ s.gpr .r1 = BitVec.ofNat 32 c)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (by decide) (fun σ s h => (h.1.1.slotV hC).trans hCv)
      fun σ s t ⟨⟨h, x⟩, r0⟩ u => ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
        by rw [u.other _ (by decide), r0]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G d X σ s ∧ s.gpr .r0 = G.seeds + BitVec.ofNat 32 c) ∧
      s.gpr .r1 = BitVec.ofNat 32 c)
    (VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
      (.block [.dp .add .r0 .r0 (.reg .r1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.2, h₂.1.2]
        · rw [h₁.2, h₂.2])
      fun σ s ⟨⟨⟨h, x⟩, r0⟩, r1⟩ => wp_dp (op2_reg _ _) fun t u => WP.block_nil
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, by rw [u.gpr, dpVal, r0, r1]⟩,
          by rw [u.other _ (by decide), r1]⟩) ?_
  refine VP.seq (G := fun σ s => St G (d.setV fSeed (G.seeds + BitVec.ofNat 32 c)) X σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 c)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨⟨_, x⟩, r0⟩, r1⟩ h' R => ⟨⟨r0 ▸ h', x⟩, by rw [R.gpr _ (by decide), r1]⟩) ?_
  refine VP.seq (G := fun σ s => St G (d.setV fSeed (G.seeds + BitVec.ofNat 32 c)) X σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 (c + G.qLen))
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.dp .add .r1 .r1 (.imm (BitVec.ofNat 32 0))]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨h, x⟩, r1⟩ => wp_dp (op2_imm (encodable_lt hq8)) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by rw [u.gpr, dpVal, r1, BitVec.ofNat_add]⟩) ?_
  exact st_vp (c := fun _ => d.setV fSeed (G.seeds + BitVec.ofNat 32 c)) (fun σ s h => h.1.1) (by decide)
    (varOk_of (by decide)) fun σ s t ⟨⟨_, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩

/-- A rejected seed: the cursor past it, one seed fewer left. -/
theorem rejected_vp {d : Cfg} {u j : Nat} (hU : fUsed ∈ d.LS) (hUv : d.V fUsed = BitVec.ofNat 32 u)
    (hL : fSeedLeft ∈ d.LS) (hLv : d.V fSeedLeft = BitVec.ofNat 32 (j + 1)) (hj : j + 1 < 2 ^ 32) :
    VP (St G d X) Geo.rejected
      (St G ((d.setV fC (BitVec.ofNat 32 u)).setV fSeedLeft (BitVec.ofNat 32 j)) X) := by
  unfold Geo.rejected
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 u)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hU).trans hUv)
      fun σ s t ⟨h, x⟩ u' => ⟨⟨h.of_rest (u'.rest (ws := [.r0]) (by simp)) u'.mem, x⟩, u'.gpr⟩) ?_
  refine VP.seq (G := St G (d.setV fC (BitVec.ofNat 32 u)) X)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r0⟩ h' _ => ⟨r0 ▸ h', x⟩) ?_
  have hL' : fSeedLeft ∈ (d.setV fC (BitVec.ofNat 32 u)).LS := List.mem_cons_of_mem _ hL
  refine VP.seq (G := fun σ s => St G (d.setV fC (BitVec.ofNat 32 u)) X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (j + 1))
    (ld_vp (c := fun _ => d.setV fC (BitVec.ofNat 32 u)) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => (h.1.slotV hL').trans ((upd_ne (o := fC) d.V (BitVec.ofNat 32 u) (by decide)).trans hLv))
      fun σ s t ⟨h, x⟩ u' => ⟨⟨h.of_rest (u'.rest (ws := [.r0]) (by simp)) u'.mem, x⟩, u'.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G (d.setV fC (BitVec.ofNat 32 u)) X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 j)
    (VP.taint [.r0] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0])
      (.block [.dp .sub .r0 .r0 (.imm 1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨h, x⟩, r0⟩ => wp_dp (op2_imm (by decide)) fun t u' => WP.block_nil
        ⟨⟨h.of_rest (u'.rest (ws := [.r0]) (by simp)) u'.mem, x⟩, ?_⟩) ?_
  · rw [u'.gpr, dpVal, r0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    have := hj
    omega_arith
  exact st_vp (c := fun _ => d.setV fC (BitVec.ofNat 32 u)) (fun σ s h => h.1.1) (by decide)
    (varOk_of (by decide)) fun σ s t ⟨⟨_, x⟩, r0⟩ h' _ => ⟨r0 ▸ h', x⟩

/-! ## The controller's spec -/

/-- The seed at the cursor `c`, as the code runs it. -/
abbrev sR (G : GP) (c : Nat) : Option (Option Spec.Dsa.Params × List Byte) :=
  refillAttempt G.pLen G.qLen (seedAt G c) (G.witB.drop (c + G.qLen))

/-- The controller's seeds left and cursor after `i` iterations. -/
def sPos (G : GP) : Nat → Nat × Nat
  | 0 => (G.k0, 0)
  | i + 1 => match sR G (sPos G i).2 with
    | some (none, rest) => ((sPos G i).1 - 1, G.witLen - rest.length)
    | _ => sPos G i

/-- The iterations, from the `i`-th at the cursor `c` with `j` seeds left. -/
def sCount (G : GP) : Nat → Nat → Nat → Nat
  | 0, _, i => i + 1
  | j + 1, c, i => if G.witLen - c < G.qLen then i + 1 else match sR G c with
    | some (none, rest) => sCount G j (G.witLen - rest.length) (i + 1)
    | _ => i + 1

theorem sCount_gt (G : GP) : ∀ j c i, i < sCount G j c i
  | 0, c, i => by simp [sCount]
  | j + 1, c, i => by
    have := sCount_gt G j
    simp only [sCount]; split
    · omega_arith
    · split
      · exact Nat.lt_of_succ_lt (this _ _)
      all_goals omega_arith

/-- How the controller ends. -/
inductive COut where
  | found (a : Spec.Dsa.Params) (u : Nat)
  | noSeeds (c : Nat)
  | ranOut (j c : Nat)

/-- The controller's end from seeds left `j` and the cursor `c`. -/
def cOutAt (G : GP) : Nat × Nat → COut
  | (0, c) => .noSeeds c
  | (j + 1, c) => if G.witLen - c < G.qLen then .ranOut (j + 1) c else match sR G c with
    | some (some a, rest) => .found a (G.witLen - rest.length)
    | _ => .ranOut (j + 1) c

/-- The stage it ends at. -/
def cFin (G : GP) : COut → Cfg
  | .found a u => ({ cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] } : Cfg).setV fUsed
      (BitVec.ofNat 32 u) |>.setV fStatus 1
  | .noSeeds c => (({} : Cfg).setV fC (BitVec.ofNat 32 c)).setV fStatus 3
  | .ranOut j c => ((({} : Cfg).setV fC (BitVec.ofNat 32 c)).setV fSeedLeft (BitVec.ofNat 32 j)).setV fStatus 2

/-- Its result, as the spec states it. -/
def cRes (G : GP) : COut → Spec.Dsa.ParameterSearchResult
  | .found a u => ⟨.accepted a, u, []⟩
  | .noSeeds c => ⟨.exhausted, c, []⟩
  | .ranOut j c => ranOutResult G.pLen j (G.witLen - c) c

/-- Its words' bounds. -/
def cOk (G : GP) : COut → Prop
  | .found _ u => u ≤ G.witLen
  | .noSeeds c => c ≤ G.witLen
  | .ranOut j c => c ≤ G.witLen ∧ j ≤ Spec.Dsa.parameterSeeds

/-- The whole search's result. -/
abbrev sW (G : GP) : Spec.Dsa.ParameterSearchResult := Spec.Dsa.parameterSearch G.pLen G.k0 G.witB

/-- The controller's stage at the cursor `c` with `j` seeds left. -/
abbrev cBase (G : GP) (HO : HashOk Gh) (c j : Nat) : Cfg :=
  ((({ cl := [(G.qLen, padTail HO.md G.qLen)] } : Cfg).setV fC (BitVec.ofNat 32 c)).setV fSeedLeft
    (BitVec.ofNat 32 j)).setV fStatus 0

/-- The search with `r` iterations left of `N`. -/
abbrev sInv (G : GP) (HO : HashOk Gh) (N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ sCount G (sPos G (N - r)).1 (sPos G (N - r)).2 (N - r) = N ∧
    (Spec.Dsa.parameterSearch G.pLen (sPos G (N - r)).1 (G.witB.drop (sPos G (N - r)).2)).consume
      (sPos G (N - r)).2 [] = sW G ∧
    (sPos G (N - r)).2 ≤ G.witLen ∧ (sPos G (N - r)).1 ≤ Spec.Dsa.parameterSeeds) ∧
    St G (cBase G HO (sPos G (N - r)).2 (sPos G (N - r)).1) X σ s

/-- The controller's end. -/
abbrev cOut (G : GP) (N : Nat) : COut := cOutAt G (sPos G (N - 1))

theorem sBody_vp {g : Geo} {HO : HashOk g.G} {n : Nat} (O : GenOk G g HO n) {N : Nat} (r : Nat) :
    VP (sInv G HO N X (r + 1)) (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fSeedLeft 0),
        .ite .eq (.block (stImm fStatus 3))
          (VG.Impl.Rsa.Arm.Keys.seqs [g.avail,
            .ite .eq (.block (stImm fStatus 2))
              (VG.Impl.Rsa.Arm.Keys.seqs [g.seedStart, g.attempt, .block (cmpF fStatus 0),
                .ite .eq Geo.rejected (.block [])])]),
        .block (cmpF fStatus 0)])
      (fun σ s => isa.eval .eq s = some (decide (0 < r)) ∧
        (r = 0 → St G (cFin G (cOut G N)) X σ s ∧ cRes G (cOut G N) = sW G ∧ cOk G (cOut G N)) ∧
        (0 < r → sInv G HO N X r σ s)) := by
  refine VG.Proof.Dsa.Arm.Gen.VP.intro fun ⟨hr, hc, hW, hcw, hj⟩ => ?_
  have hq0 : 0 < G.qLen := by have := O.hlq; omega_arith
  have hq8 : G.qLen < 256 := by have := O.hlq; omega_arith
  have hpL : 0 < G.pLen := by have := O.hlq; omega_arith
  have h32 := O.h32
  have hwl := O.hwl
  have hqL := O.hqL
  generalize hii : N - (r + 1) = i at hc hW hcw hj
  generalize hp : sPos G i = jc at hc hW hcw hj
  obtain ⟨j, c⟩ := jc
  dsimp only at hc hW hcw hj
  have hNi : N - 1 = i + r := by omega_arith
  refine VP.seq (G := fun σ s => St G (cBase G HO c j) X σ s ∧
      isa.eval .eq s = some (BitVec.ofNat 32 j == BitVec.ofNat 32 0))
    (cmpF_vp (x := BitVec.ofNat 32 j) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fSeedLeft, fStatus]))
      fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, e⟩) ?_
  have jl : j < 2 ^ 32 := by simp only [Spec.Dsa.parameterSeeds] at hj; omega_arith
  rcases j with _ | j
  · -- No seeds left: `fStatus` := 3.
    have r0 : r = 0 := by simp only [sCount] at hc; omega_arith
    subst r0
    have hout : cOut G N = .noSeeds c := by simp only [cOut, hNi, Nat.add_zero, hp, cOutAt]
    refine VP.seq (G := St G ((cBase G HO c 0).setV fStatus (BitVec.ofNat 32 3)) X) (VP.ite
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => cBase G HO c 0) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)) ?_
    refine cmpF_vp (x := BitVec.ofNat 32 3) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
    · rw [hout]
      refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin]))
        (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
      change o ∈ [fStatus, fC] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> exact ⟨by simp, by simp [cFin, upd, fStatus, fC, fSeedLeft]⟩
    · rw [hout, ← hW]; exact (VG.Proof.Dsa.Generation.search_zero _ _ _).symm
    · rw [hout]; exact hcw
  · have e0 : (BitVec.ofNat 32 (j + 1) == BitVec.ofNat 32 0) = false := by
      refine beq_false_of_ne fun e => ?_
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega_arith
    have notZ : ∀ {G₁ : State → State → Prop} {c' : Prog isa}, VP (fun σ s => (St G (cBase G HO c (j + 1)) X σ s ∧
        isa.eval .eq s = some (BitVec.ofNat 32 (j + 1) == BitVec.ofNat 32 0)) ∧
        isa.eval .eq s = some true) c' G₁ :=
      VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z
    have avail := (avail_vp (X := X) O.hq (d := cBase G HO c (j + 1)) (by simp)
      (by simp [upd, fC, fSeedLeft, fStatus]) hcw h32 (by omega_arith)).mono
      (F' := fun σ s => (St G (cBase G HO c (j + 1)) X σ s ∧
        isa.eval .eq s = some (BitVec.ofNat 32 (j + 1) == BitVec.ofNat 32 0)) ∧
        isa.eval .eq s = some false) (fun σ s h => h.1.1) fun _ _ h => h
    by_cases hshort : G.witLen - c < G.qLen
    · -- Too few octets for a seed: `fStatus` := 2.
      have r0 : r = 0 := by simp only [sCount, hshort, ↓reduceIte] at hc; omega_arith
      subst r0
      have hout : cOut G N = .ranOut (j + 1) c := by
        simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte]
      refine VP.seq (G := St G ((cBase G HO c (j + 1)).setV fStatus (BitVec.ofNat 32 2)) X)
        (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) notZ (VP.seq avail (VP.ite
          (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (stImm_vp (c := fun _ => cBase G HO c (j + 1)) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
            fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hshort] at z)))) ?_
      refine cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
      · rw [hout]
        refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin]))
          (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
        change o ∈ [fStatus, fSeedLeft, fC] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl <;> exact ⟨by simp, by simp [cFin, upd, fStatus, fC, fSeedLeft]⟩
      · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_short (by rw [hwl, ← hqL]; exact hshort), hwl]
      · rw [hout]; exact ⟨hcw, hj⟩
    · -- A seed.
      have hcq : c + G.qLen ≤ G.witLen := by omega_arith
      have attempt := O.attempt_vp (X := X) (k := c) (u := c + G.qLen) (n' := BitVec.ofNat 32 (j + 1)) hcq hcq
      have hmono : ∀ σ s, St G (((cBase G HO c (j + 1)).setV fSeed (G.seeds + BitVec.ofNat 32 c)).setV fUsed
          (BitVec.ofNat 32 (c + G.qLen))) X σ s →
          St G ((aBase G HO c (BitVec.ofNat 32 (j + 1))).setV fUsed (BitVec.ofNat 32 (c + G.qLen))) X σ s := by
        intro σ s h
        refine ⟨h.1.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
          (fun _ h' => absurd h' (by simp)), h.2⟩
        change o ∈ [fUsed, fStatus, fSeedLeft, fSeed, fC] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp, by simp [upd, fUsed, fStatus, fSeedLeft, fSeed, fC]⟩
      have start := (seedStart_vp (X := X) O.hq (d := cBase G HO c (j + 1)) (c := c) (by simp)
        (by simp [upd, fC, fSeedLeft, fStatus]) hq8).mono (F' := fun σ s =>
          (St G (cBase G HO c (j + 1)) X σ s ∧ isa.eval .eq s = some (decide (G.witLen - c < G.qLen))) ∧
          isa.eval .eq s = some false) (fun σ s h => h.1.1) hmono
      have wrap : ∀ {G₁ : State → State → Prop}, VP (St G ((aBase G HO c (BitVec.ofNat 32 (j + 1))).setV fUsed
          (BitVec.ofNat 32 (c + G.qLen))) X) (VG.Impl.Rsa.Arm.Keys.seqs [g.attempt, .block (cmpF fStatus 0),
            .ite .eq Geo.rejected (.block [])]) G₁ →
          VP (fun σ s => St G (cBase G HO c (j + 1)) X σ s ∧
            isa.eval .eq s = some (BitVec.ofNat 32 (j + 1) == BitVec.ofNat 32 0))
            (.ite .eq (.block (stImm fStatus 3))
              (VG.Impl.Rsa.Arm.Keys.seqs [g.avail,
                .ite .eq (.block (stImm fStatus 2))
                  (VG.Impl.Rsa.Arm.Keys.seqs [g.seedStart, g.attempt, .block (cmpF fStatus 0),
                    .ite .eq Geo.rejected (.block [])])])) G₁ := fun k =>
        VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) notZ (VP.seq avail (VP.ite
          (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hshort] at z) (VP.seq start k)))
      have hRc : (G.witB.drop c).take (Spec.Dsa.generationQLen G.pLen) = seedAt G c := by
        show _ = (G.witB.drop c).take G.qLen; rw [hqL]
      have hcq' : c + Spec.Dsa.generationQLen G.pLen ≤ G.witB.length := by rw [hwl, ← hqL]; exact hcq
      have suffix : ∀ {x : Option Spec.Dsa.Params} {rest : List Byte}, sR G c = some (x, rest) →
          G.witB.drop (G.witLen - rest.length) = rest := fun {x rest} e => by
        rw [← hwl]
        exact VG.Proof.Dsa.Generation.suffix_drop_length
          ((VG.Proof.Dsa.Generation.refillAttempt_suffix e).trans (List.drop_suffix _ _))
      change VP _ _ (St G (aOut G HO c (BitVec.ofNat 32 (j + 1)) (sR G c)) X) at attempt
      rcases hR : sR G c with _ | ⟨_ | a, rest⟩ <;> rw [hR] at attempt
      · -- `rand` ran out inside the seed.
        have r0 : r = 0 := by
          simp only [sCount, hshort, ↓reduceIte, hR] at hc; omega_arith
        subst r0
        have hout : cOut G N = .ranOut (j + 1) c := by
          simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte, hR]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 32 (j + 1)) none) X σ s ∧ isa.eval .eq s = some false)
          (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
            fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s h => h.1.1))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
          fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
        · rw [hout]
          refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin]))
            (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
          change o ∈ [fStatus, fSeedLeft, fC] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl <;>
            exact ⟨by simp [aOut], by simp [aOut, cFin, upd, fStatus, fC, fSeedLeft, fSeed]⟩
        · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_attemptNone hpL hcq' (by rw [hRc, ← hqL]; exact hR),
            hwl]
        · rw [hout]; exact ⟨hcw, hj⟩
      · -- Rejected: the next seed.
        have hsuf := suffix hR
        have hcs : sCount G (j + 1) c i = sCount G j (G.witLen - rest.length) (i + 1) := by
          simp only [sCount, hshort, ↓reduceIte, hR]
        have hgt := sCount_gt G j (G.witLen - rest.length) (i + 1)
        have rpos : 0 < r := by omega_arith
        have hNr : N - r = i + 1 := by omega_arith
        have hp1 : sPos G (i + 1) = (j, G.witLen - rest.length) := by
          simp only [sPos, hp, hR, Nat.add_sub_cancel]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 32 (j + 1)) (some (none, rest))) X σ s ∧
            isa.eval .eq s = some true)
          (cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd, fUsed, fStatus]))
            fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            ((rejected_vp (u := G.witLen - rest.length) (j := j) (by simp [aOut]) (by simp [aOut, upd])
              (by simp [aOut]) (by simp [aOut, upd, fUsed, fStatus, fSeedLeft]) (by omega_arith)).mono
                (fun σ s h => h.1.1) fun _ _ h => h)
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd, fUsed, fStatus, fC, fSeedLeft]))
          fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega_arith), fun _ => ?_⟩
        simp only [sInv, hNr, hp1]
        refine ⟨⟨by omega_arith, by rw [← hcs]; exact hc, ?_, Nat.sub_le _ _, by omega_arith⟩, ?_, x⟩
        · rw [← hW, VG.Proof.Dsa.Generation.search_rejected hpL hcq'
            (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_eq hwl.symm)) (by rw [hRc, ← hqL, hsuf]; exact hR)]
        · refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
            (fun _ h' => absurd h' (by simp))
          change o ∈ [fStatus, fSeedLeft, fC] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl <;>
            exact ⟨by simp [aOut], by simp [aOut, upd, fStatus, fC, fSeedLeft, fUsed]⟩
      · -- Parameters: `fStatus` = 1.
        have hsuf := suffix hR
        have r0 : r = 0 := by
          simp only [sCount, hshort, ↓reduceIte, hR] at hc; omega_arith
        subst r0
        have hout : cOut G N = .found a (G.witLen - rest.length) := by
          simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte, hR]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 32 (j + 1)) (some (some a, rest))) X σ s ∧
            isa.eval .eq s = some false)
          (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
            fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s h => h.1.1))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
          fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
        · rw [hout]
          refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => hy)
            (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
          change o ∈ [fStatus, fUsed] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> exact ⟨by simp [aOut], by simp [aOut, cFin, upd, fStatus, fUsed]⟩
        · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_accepted hpL hcq'
            (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_eq hwl.symm)) (by rw [hRc, ← hqL, hsuf]; exact hR)]
        · rw [hout]; exact Nat.sub_le _ _

/-- The seeds, from the cursor 0 with `state[0]` seeds left. -/
theorem sLoop_vp {g : Geo} {HO : HashOk g.G} {n : Nat} (O : GenOk G g HO n) :
    VP (St G (cBase G HO 0 G.k0) X)
      (.loop (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fSeedLeft 0),
        .ite .eq (.block (stImm fStatus 3))
          (VG.Impl.Rsa.Arm.Keys.seqs [g.avail,
            .ite .eq (.block (stImm fStatus 2))
              (VG.Impl.Rsa.Arm.Keys.seqs [g.seedStart, g.attempt, .block (cmpF fStatus 0),
                .ite .eq Geo.rejected (.block [])])]),
        .block (cmpF fStatus 0)]) .eq)
      (fun σ s => St G (cFin G (cOut G (sCount G G.k0 0 0))) X σ s ∧
        cRes G (cOut G (sCount G G.k0 0 0)) = sW G ∧ cOk G (cOut G (sCount G G.k0 0 0))) := by
  have hN := sCount_gt G G.k0 0 0
  generalize hNN : sCount G G.k0 0 0 = N at hN ⊢
  refine VP.mono (F := sInv G HO N X (N - 1 + 1)) ?_ (fun σ s h => ⟨⟨by omega,
    by rw [show N - (N - 1 + 1) = 0 by omega]; exact hNN,
    by rw [show N - (N - 1 + 1) = 0 by omega]; simp [sPos, sW, Spec.Entropy.Result.consume],
    by rw [show N - (N - 1 + 1) = 0 by omega]; simp [sPos], by rw [show N - (N - 1 + 1) = 0 by omega]; exact O.k0⟩,
    by rw [show N - (N - 1 + 1) = 0 by omega]; exact h⟩) fun _ _ h => h
  exact VP.loop (I := sInv G HO N X) (fun r => (sBody_vp O r).mono (fun _ _ h => h)
    fun σ s ⟨e, h0, hp⟩ => ⟨e, fun z => h0 z, hp⟩) _

end

end VG.Proof.Dsa.Arm.Gen
