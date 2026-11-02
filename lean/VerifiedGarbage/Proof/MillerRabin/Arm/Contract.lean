module

public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.MillerRabin.Arm.Base
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The Miller–Rabin round on ARMv7: the contract its callers use

`roundContract`: the round's contract, as the code needs it and its callers
establish it: the working space laid out for Montgomery multiplication
(`LayoutLite`, with its first 28 arrays) and the candidate, the witness,
Montgomery one and minus one, the exponent and the word `2^(t mod 64)` after
it in it (`PreparedLite`), as in the shared contract, without its
representation's choice and stride. Only the arrays `wJs` and the header
words 23, 26, 29 and 30 change (`KeepsLite`).
It implies `Proof.MillerRabin.Round.roundContract` (`round_implies`, `Proof/MillerRabin/Arm/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt)

def LayoutLite (m : Mem) (ws : Addr) (len : Nat) : Prop :=
  Proof.Rsa.Mont.Layout m ws len ∧ 4 ≤ wOf m ws ∧ wOf m ws ≤ 128 ∧ arrAt (wOf m ws) nArr ≤ 8 * len

def PreparedLite (m : Mem) (ws : Addr) : Prop :=
  let w := wOf m ws
  let c := numAt m ws w 0
  let R := 2 ^ (64 * w)
  3 ≤ c ∧ c % 2 = 1 ∧
    ((m.readW (ws + BitVec.ofNat 64 (arrAt w 0)) 64).toNat * (wordAt m ws Proof.Rsa.Mont.minvWord).toNat + 1) %
      2 ^ 64 = 0 ∧
    numAt m ws w 5 < c ∧ numAt m ws w 9 = R % c ∧ numAt m ws w 10 = c - R % c ∧
    numAt m ws w 27 = Proof.MillerRabin.Round.exponent c ∧
    m.readW (ws + BitVec.ofNat 64 (arrAt w 27 + 8 * w)) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64)

/-- Only the header words 23, 26, 29 and 30 and the arrays `wJs` change. -/
def KeepsLite (ws : Addr) (len w : Nat) (m m' : Mem) : Prop :=
  ∀ i < 8 * len, (∀ k ∈ [23, 26, 29, 30], i < 8 * k ∨ 8 * k + 8 ≤ i) →
    (∀ j ∈ wJs, i < arrAt w j ∨ arrAt w j + 8 * (w + 2) ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

def roundPre (s : State) : Prop :=
  let ws := State.addr (s.gpr .r0)
  let n := (s.gpr .r1).toNat
  s.rd = [] ∧ s.wr = [⟨ws, 8 * n⟩] ∧ (s.gpr .r0).toNat + 8 * n ≤ 2 ^ 32 ∧ 56 ≤ s.sp.toNat ∧
    (FrameStack.belowA s.sp 56).Disjoint ⟨ws, 8 * n⟩ ∧ LayoutLite s.mem ws n ∧ PreparedLite s.mem ws

def roundPost (s t : State) : Prop :=
  let ws := State.addr (s.gpr .r0)
  let w := wOf s.mem ws
  let c := numAt s.mem ws w 0
  (∀ b, numAt s.mem ws w 5 = b % c * 2 ^ (64 * w) % c →
    (t.gpr .r0).toNat = if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
    KeepsLite ws (s.gpr .r1).toNat w s.mem t.mem

def roundPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    wOf s.mem (State.addr (s.gpr .r0)) = wOf t.mem (State.addr (t.gpr .r0))

/-- The round's contract on ARMv7, as its callers use it. -/
def roundContract : Contract isa where
  pre := roundPre
  post := roundPost
  pub := roundPub

/-! ## Memory that keeps its bytes -/

section
variable {m m' : Mem} {ws : Addr} {len : Nat}

theorem read_congr_on (h : ∀ i < 8 * len, m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i))
    {d n : Nat} (hd : d + n ≤ 8 * len) : m'.read (ws + BitVec.ofNat 64 d) n = m.read (ws + BitVec.ofNat 64 d) n :=
  Mem.read_congr fun i hi => by rw [Offset.add_add]; exact h _ (by omega)

theorem readW_congr_on (h : ∀ i < 8 * len, m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i))
    {d : Nat} (hd : d + 8 ≤ 8 * len) : m'.readW (ws + BitVec.ofNat 64 d) 64 = m.readW (ws + BitVec.ofNat 64 d) 64 := by
  simp only [Mem.readW, read_congr_on h hd]

theorem layout_congr (h : ∀ i < 8 * len, m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i))
    (hl : LayoutLite m ws len) : LayoutLite m' ws len ∧ wOf m' ws = wOf m ws := by
  obtain ⟨lay, w4, w128, fits⟩ := hl
  have h256 : 256 ≤ 8 * len := Nat.le_trans (Nat.le_add_right _ _) fits
  have hw : wOf m' ws = wOf m ws := congrArg BitVec.toNat (readW_congr_on h (d := 8 * 6) (by omega))
  refine ⟨⟨?_, by rw [hw]; exact w4, by rw [hw]; exact w128, by rw [hw]; exact fits⟩, hw⟩
  unfold Proof.Rsa.Mont.Layout at lay ⊢
  rw [hw]
  refine ⟨lay.1, lay.2.1, lay.2.2.1, fun j hj => ?_⟩
  unfold wordAt
  rw [readW_congr_on h (by simp only [Proof.Rsa.Mont.arrWord]; omega)]
  exact lay.2.2.2 j hj

theorem numAt_congr (h : ∀ i < 8 * len, m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i))
    {w j : Nat} (hj : arrAt w j + 8 * w ≤ 8 * len) : numAt m' ws w j = numAt m ws w j := by
  unfold numAt; rw [read_congr_on h hj]

theorem prepared_congr (h : ∀ i < 8 * len, m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i))
    (hl : LayoutLite m ws len) (hp : PreparedLite m ws) : PreparedLite m' ws := by
  obtain ⟨_, hw⟩ := layout_congr h hl
  have fits := hl.2.2.2
  have w4 := hl.2.1
  generalize hW : wOf m ws = w at fits w4
  have fit : ∀ j < 28, arrAt w j + 8 * (w + 2) ≤ 8 * len := fun j hj => by
    have : j * (8 * (w + 2)) ≤ 27 * (8 * (w + 2)) := Nat.mul_le_mul_right _ (by omega)
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes, nArr] at fits ⊢
    generalize 8 * (w + 2) = S at this fits ⊢
    omega
  unfold PreparedLite at hp ⊢
  simp only [hw, hW] at hp ⊢
  rw [numAt_congr h (by have := fit 0 (by omega); omega), numAt_congr h (by have := fit 5 (by omega); omega),
    numAt_congr h (by have := fit 9 (by omega); omega), numAt_congr h (by have := fit 10 (by omega); omega),
    numAt_congr h (by have := fit 27 (by omega); omega),
    readW_congr_on h (d := arrAt w 27 + 8 * w) (by have := fit 27 (by omega); omega)]
  refine ⟨hp.1, hp.2.1, ?_, hp.2.2.2⟩
  have e1 : m'.readW (ws + BitVec.ofNat 64 (arrAt w 0)) 64 = m.readW (ws + BitVec.ofNat 64 (arrAt w 0)) 64 :=
    readW_congr_on h (by have := fit 0 (by omega); simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this ⊢; omega)
  have e2 : wordAt m' ws Proof.Rsa.Mont.minvWord = wordAt m ws Proof.Rsa.Mont.minvWord :=
    readW_congr_on h (by have := fit 0 (by omega); simp only [arrAt, Proof.Rsa.Mont.hdrBytes, Proof.Rsa.Mont.minvWord] at this ⊢; omega)
  rw [e1, e2]
  exact hp.2.2.1

end

end VG.Proof.MillerRabin.Arm
