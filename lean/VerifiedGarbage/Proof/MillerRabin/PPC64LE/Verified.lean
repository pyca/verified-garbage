module

import VerifiedGarbage.Proof.MillerRabin.PPC64LE.CT
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Fn
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.Inline

/-!
# The Miller–Rabin round on PPC64LE: the shared contract

As `Proof/Bignum/PPC64LE/MontVerified.lean`: `round` is proven against
`fnContract`, with the scratch buffer where it saves the nonvolatile
registers as a third argument; that is `roundContract` with the buffer
appended (`scratch_verified`), and `withStackScratch` allocates the buffer
in a frame of its own (`round_verified`), as the contract's precondition,
postcondition and leak read memory only within the working space when the
precondition holds.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Rsa.Mont (numAt wOf wordAt arrAt)
open VG.Proof.MillerRabin.Round (compact Layout Prepared Keeps)

/-- `roundContract`'s precondition. -/
def rPre : Curry (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) (Mem → Prop) := fun ws wsLen m =>
  Layout compact m ws wsLen.toNat ∧ Prepared compact m ws

/-- `roundContract`'s postcondition. -/
def rPost : Proof.MillerRabin.Round.roundSig.Post abi.ptrBits := fun ws wsLen m m' r =>
  let w := wOf m ws
  let c := numAt m ws w 0
  (∀ b, numAt m ws w 5 = b % c * 2 ^ (64 * w) % c → r.toNat = if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
    Keeps compact ws wsLen.toNat w m m'

/-- `roundContract`'s leak. -/
def rLeak : Curry (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) (Mem → List Nat) := fun ws _ m => [wOf m ws]

theorem roundContract_eq (stack : Nat) :
    Proof.MillerRabin.Round.roundContract abi compact stack =
      Proof.MillerRabin.Round.roundSig.contract abi rPre rPost false stack (some rLeak) := rfl

/-- `roundContract` with the 144-byte scratch buffer as a third argument. -/
abbrev scratchContract : Contract isa :=
  Sig.scratchContract abi Proof.MillerRabin.Round.roundSig "scratch" .u64 18 rPre rPost false 0 (some rLeak)

/-! ## Satisfiability -/

/-- A four-limb prepared workspace for the candidate 3 at `0x1000`, as on
AArch64. -/
def satWord (i : Nat) : BitVec 64 :=
  if i = 6 then 4 else if i = 7 then 0x5555555555555555 else
    if 8 ≤ i ∧ i < 16 then BitVec.ofNat 64 (0x1100 + 48 * (i - 8)) else
    if i = 28 then 48 else if i = 32 then 3 else if i = 62 then 2 else
    if i = 86 then 1 else if i = 92 then 2 else if i = 194 then 1 else if i = 198 then 2 else 0

def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 2048 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

theorem sat_layout : Layout compact satMem 0x1000 256 := by
  simp only [Layout, compact, Proof.Rsa.Mont.Layout, Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff,
    forall_const, true_and]
  decide +kernel

theorem sat_prepared : Prepared compact satMem 0x1000 := by
  have hw : wOf satMem 0x1000 = 4 := by decide +kernel
  have hc : numAt satMem 0x1000 4 0 = 3 := by
    rw [VG.Proof.Bignum.PPC64LE.numAt_eq]; decide +kernel
  have h5 : numAt satMem 0x1000 4 5 = 2 := by
    rw [VG.Proof.Bignum.PPC64LE.numAt_eq]; decide +kernel
  have h9 : numAt satMem 0x1000 4 9 = 1 := by
    rw [VG.Proof.Bignum.PPC64LE.numAt_eq]; decide +kernel
  have h10 : numAt satMem 0x1000 4 10 = 2 := by
    rw [VG.Proof.Bignum.PPC64LE.numAt_eq]; decide +kernel
  have h27 : numAt satMem 0x1000 4 27 = 1 := by
    rw [VG.Proof.Bignum.PPC64LE.numAt_eq]; decide +kernel
  simp only [Prepared, compact, hw, hc, h5, h9, h10, h27]
  decide +kernel

/-- A state meeting `scratchContract`: the scratch buffer at `0x2000`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 256 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 2048⟩, ⟨0x2000, 144⟩]

/-- `satState` without the scratch buffer: a state meeting `roundContract`. -/
def satState₀ : State := { satState with wr := [⟨0x1000, 2048⟩] }

theorem fn_implies : fnContract.Implies scratchContract where
  pre := by
    intro s h
    sig_pre [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, fnContract, abi, argRegs] at h
    sig_split h
    sig_reduce [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, fnContract, abi, argRegs]
    simp only [Prepared]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> with_reducible assumption
  post := by
    sig_implies_post [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, fnContract, abi, argRegs]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, fnContract, abi, argRegs] at h
    obtain ⟨hsp, hw, h3, h4, h5⟩ := h
    exact ⟨hsp, h3, h4, h5, List.singleton_inj.mp hw⟩
  sat := by
    refine ⟨satState, ?_⟩
    sig_pre [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, abi, argRegs]
    sig_and_intros
    · rfl
    · exact Region.disjoint_of_sep (by decide)
    · decide
    · decide
    · show Layout compact satMem 4096 (BitVec.toNat (256 : BitVec 64)) ∧ Prepared compact satMem 4096
      exact ⟨sat_layout, sat_prepared⟩

theorem scratch_verified : Verified target Impl.MillerRabin.PPC64LE.round scratchContract :=
  Verified.of_correct fn_correct fn_ct fn_implies

/-! ## Reading memory within the working space -/

theorem arrAt_le {w j k : Nat} (h : j ≤ k) : arrAt w j ≤ arrAt w k := by
  unfold arrAt; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- What the contract reads of `m₂` agrees with `m₁`, whose layout bounds it. -/
structure Same (ws : Addr) (m₁ m₂ : Mem) : Prop where
  w : wOf m₂ ws = wOf m₁ ws
  rd : ∀ d, d + 8 ≤ arrAt (wOf m₁ ws) 28 → m₂.readW (ws + BitVec.ofNat 64 d) 64 = m₁.readW (ws + BitVec.ofNat 64 d) 64
  num : ∀ j < 28, numAt m₂ ws (wOf m₁ ws) j = numAt m₁ ws (wOf m₁ ws) j

theorem same_of {m₁ m₂ : Mem} {ws : Addr} {n : Nat}
    (h : ∀ a, (⟨ws, n * 8⟩ : Region).Contains a 1 → m₂ a = m₁ a) (hl : Layout compact m₁ ws n) :
    Same ws m₁ m₂ := by
  dsimp only [Layout, compact] at hl
  obtain ⟨-, -, -, h128, hsp, -⟩ := hl
  have hsp' : arrAt (wOf m₁ ws) 28 ≤ n * 8 := by
    change arrAt (wOf m₁ ws) 28 ≤ 8 * n at hsp; omega_arith
  have hz : arrAt (wOf m₁ ws) 28 < 2 ^ 64 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have rd : ∀ d, d + 8 ≤ arrAt (wOf m₁ ws) 28 →
      m₂.readW (ws + BitVec.ofNat 64 d) 64 = m₁.readW (ws + BitVec.ofNat 64 d) 64 :=
    fun d hd => VG.Proof.Bignum.PPC64LE.agree_readW h (by omega_arith) (by omega_arith)
  have h48 : 8 * 6 + 8 ≤ arrAt (wOf m₁ ws) 28 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  refine ⟨?_, rd, fun j hj => ?_⟩
  · simp only [wOf, wordAt, Proof.Rsa.Mont.wWord]
    rw [rd _ h48]
  · have hj' := arrAt_le (w := wOf m₁ ws) (show j + 1 ≤ 28 by omega_arith)
    have e : arrAt (wOf m₁ ws) (j + 1) = arrAt (wOf m₁ ws) j + 8 * (wOf m₁ ws + 2) := by
      unfold arrAt; rw [Nat.add_mul, Nat.one_mul]; omega_arith
    simp only [numAt]
    rw [VG.Proof.Bignum.PPC64LE.agree_read h (by omega_arith) (by omega_arith)]

theorem layout_congr {m₁ m₂ : Mem} {ws : Addr} {n : Nat} (hS : Same ws m₁ m₂) (hl : Layout compact m₁ ws n) :
    Layout compact m₂ ws n := by
  have hl' := hl
  dsimp only [Layout, compact, Proof.Rsa.Mont.Layout] at hl' ⊢
  obtain ⟨h0, ⟨h2, h31, h8, harr⟩, h4, h128, hsp, hst⟩ := hl'
  rw [hS.w]
  have hz : 8 * 28 + 8 ≤ arrAt (wOf m₁ ws) 28 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  refine ⟨h0, ⟨h2, h31, h8, fun j hj => ?_⟩, h4, h128, hsp, ?_⟩
  · simp only [wordAt, Proof.Rsa.Mont.arrWord] at harr ⊢
    rw [hS.rd _ (by omega_arith)]; exact harr j hj
  · simp only [wordAt] at hst ⊢
    rw [hS.rd _ (by omega_arith)]; exact hst

theorem prepared_congr {m₁ m₂ : Mem} {ws : Addr} {n : Nat} (hS : Same ws m₁ m₂) (hl : Layout compact m₁ ws n)
    (hp : Prepared compact m₁ ws) : Prepared compact m₂ ws := by
  dsimp only [Layout, compact] at hl
  obtain ⟨-, -, -, h128, -, -⟩ := hl
  dsimp only [Prepared, compact] at hp ⊢
  rw [hS.w, hS.num 0 (by decide), hS.num 5 (by decide), hS.num 9 (by decide), hS.num 10 (by decide),
    hS.num 27 (by decide)]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hp
  have hz0 : arrAt (wOf m₁ ws) 0 + 8 ≤ arrAt (wOf m₁ ws) 28 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have hz7 : 8 * 7 + 8 ≤ arrAt (wOf m₁ ws) 28 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have hz27 : arrAt (wOf m₁ ws) 27 + 8 * wOf m₁ ws + 8 ≤ arrAt (wOf m₁ ws) 28 := by
    unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  refine ⟨a1, a2, ?_, a4, a5, a6, a7, ?_⟩
  · simp only [wordAt, Proof.Rsa.Mont.minvWord] at a3 ⊢
    rw [hS.rd _ hz0, hS.rd _ hz7]; exact a3
  · rw [hS.rd _ hz27]; exact a8

/-- The contract's arguments, as `Curry.apply` passes them. -/
theorem words_eq : Proof.MillerRabin.Round.roundSig.words abi.ptrBits = [.addr, .int 64] := rfl

theorem pre_local : ∀ vs m₁ m₂, vs.length = (Proof.MillerRabin.Round.roundSig.words abi.ptrBits).length →
    (∀ b ∈ Sig.bufs Proof.MillerRabin.Round.roundSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPre vs m₁ →
      Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPre vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  rw [words_eq] at hlen
  match vs, hlen with
  | [ws, l], _ =>
  simp only [Proof.MillerRabin.Round.roundSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  change Curry.apply [ArgWord.addr, .int 64] rPre _ m₁ at h
  change Curry.apply [ArgWord.addr, .int 64] rPre _ m₂
  dsimp only [Curry.apply, rPre, ArgWord.ofRaw] at h ⊢
  simp only [BitVec.setWidth_eq] at h ⊢
  obtain ⟨hl, hp⟩ := h
  have hS := same_of (m₁ := m₁) (m₂ := m₂) (n := l.toNat) (fun x hx => (hb x hx).symm) hl
  exact ⟨layout_congr hS hl, prepared_congr hS hl hp⟩

theorem post_local : ∀ vs m₁ m₂ m' r, vs.length = (Proof.MillerRabin.Round.roundSig.words abi.ptrBits).length →
    Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPre vs m₂ →
    (∀ b ∈ Sig.bufs Proof.MillerRabin.Round.roundSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPost vs m₁ m' r →
      Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPost vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hp hb h
  rw [words_eq] at hlen
  match vs, hlen with
  | [ws, l], _ =>
  simp only [Proof.MillerRabin.Round.roundSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  change Curry.apply [ArgWord.addr, .int 64] rPre _ m₂ at hp
  change Curry.apply [ArgWord.addr, .int 64] rPost _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, .int 64] rPost _ m₂ m' r
  dsimp only [Curry.apply, rPre, rPost, ArgWord.ofRaw] at hp h ⊢
  simp only [BitVec.setWidth_eq] at hp h ⊢
  obtain ⟨hl, -⟩ := hp
  have hS := same_of (m₁ := m₂) (m₂ := m₁) (n := l.toNat) hb hl
  obtain ⟨hr, hk⟩ := h
  simp only [hS.w, hS.num 0 (by decide), hS.num 5 (by decide)] at hr hk
  refine ⟨hr, fun i hi hh ha ht => ?_⟩
  rw [hk i hi hh ha ht]
  refine hb _ ?_
  show (ws + BitVec.ofNat 64 i - ws).toNat + 1 ≤ l.toNat * 8
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  have hi' : i < 8 * (l : BitVec 64).toNat := hi
  omega_arith

theorem leak_local : ∀ f, some rLeak = some f → ∀ vs m₁ m₂,
    vs.length = (Proof.MillerRabin.Round.roundSig.words abi.ptrBits).length →
    Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPre vs m₂ →
    (∀ b ∈ Sig.bufs Proof.MillerRabin.Round.roundSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply _ f vs m₁ = Curry.apply _ f vs m₂ := by
  intro f hf vs m₁ m₂ hlen hp hb
  cases hf
  rw [words_eq] at hlen
  match vs, hlen with
  | [ws, l], _ =>
  simp only [Proof.MillerRabin.Round.roundSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  change Curry.apply [ArgWord.addr, .int 64] rPre _ m₂ at hp
  change Curry.apply [ArgWord.addr, .int 64] rLeak _ m₁ = Curry.apply [ArgWord.addr, .int 64] rLeak _ m₂
  dsimp only [Curry.apply, rPre, rLeak, ArgWord.ofRaw] at hp ⊢
  simp only [BitVec.setWidth_eq] at hp
  rw [(same_of (m₁ := m₂) (m₂ := m₁) (n := l.toNat) hb hp.1).w]

/-- `vg_miller_rabin_round` with its scratch buffer in a frame of 176 bytes. -/
theorem round_verified : Verified target
    (Impl.StackScratch.PPC64LE.withStackScratch 176 .r5 Impl.MillerRabin.PPC64LE.round)
    (Proof.MillerRabin.Round.roundContract abi compact 176) :=
  Verified.stackScratchL (sig := Proof.MillerRabin.Round.roundSig) (nm := "scratch") (e := .u64) (n := 18)
    (post := rPost) (wa := false) (stack := 0) (bytes := 176) scratch_verified (by decide)
    (by decide) pre_local post_local leak_local
    ⟨satState₀, by
      sig_pre [Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, abi, argRegs]
      sig_and_intros
      · decide
      · decide
      · exact Region.disjoint_of_sep (by decide)
      · decide
      · exact sat_layout
      · exact sat_prepared⟩

end VG.Proof.MillerRabin.PPC64LE
