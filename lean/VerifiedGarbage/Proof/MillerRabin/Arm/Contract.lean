module

public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.MillerRabin.Arm.Base
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The Miller–Rabin round on ARMv7: the contract its callers use

`roundContract`: the round's contract, as the code needs it and its callers
establish it: the working space laid out for Montgomery multiplication
(`LayoutLite`, with its first 15 arrays) and the candidate, the witness and
Montgomery one and minus one in it (`PreparedLite`), without the shifted
exponent of the shared contract, which this implementation does not read.
Only the arrays and header words of `wJs` and `wDs` change (`KeepsLite`).
It implies `Spec.MillerRabin.roundContract` (`Proof/MillerRabin/Arm/Implies.lean`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt)

def LayoutLite (m : Mem) (ws : Addr) (len : Nat) : Prop :=
  Spec.Rsa.Mont.Layout m ws len ∧ 4 ≤ wOf m ws ∧ wOf m ws ≤ 128 ∧ arrAt (wOf m ws) nArr ≤ 8 * len

def PreparedLite (m : Mem) (ws : Addr) : Prop :=
  let w := wOf m ws
  let c := numAt m ws w 0
  let R := 2 ^ (64 * w)
  3 ≤ c ∧ c % 2 = 1 ∧
    ((m.readW (ws + BitVec.ofNat 64 (arrAt w 0)) 64).toNat * (wordAt m ws Spec.Rsa.Mont.minvWord).toNat + 1) %
      2 ^ 64 = 0 ∧
    numAt m ws w 5 < c ∧ numAt m ws w 9 = R % c ∧ numAt m ws w 10 = c - R % c

/-- Only the header words 23, 26 and 29 and the arrays `wJs` change. -/
def KeepsLite (ws : Addr) (len w : Nat) (m m' : Mem) : Prop :=
  ∀ i < 8 * len, (∀ k ∈ [23, 26, 29], i < 8 * k ∨ 8 * k + 8 ≤ i) →
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
    (t.gpr .r0).toNat = if Spec.MillerRabin.round c b then 1 else 0) ∧
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
  have h256 : 256 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
  have hw : wOf m' ws = wOf m ws := congrArg BitVec.toNat (readW_congr_on h (d := 8 * 6) (by omega))
  refine ⟨⟨?_, by rw [hw]; exact w4, by rw [hw]; exact w128, by rw [hw]; exact fits⟩, hw⟩
  unfold Spec.Rsa.Mont.Layout at lay ⊢
  rw [hw]
  refine ⟨lay.1, lay.2.1, lay.2.2.1, fun j hj => ?_⟩
  unfold wordAt
  rw [readW_congr_on h (by simp only [Spec.Rsa.Mont.arrWord]; omega)]
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
  have fit : ∀ j < 11, arrAt w j + 8 * w ≤ 8 * len := fun j hj => by
    have : j * (8 * (w + 2)) ≤ 14 * (8 * (w + 2)) := Nat.mul_le_mul_right _ (by omega)
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes, nArr] at fits ⊢; omega
  have f0 : 256 + 8 * w ≤ 8 * len := by have := fit 0 (by omega); simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at this; omega
  unfold PreparedLite at hp ⊢
  simp only [hw, hW] at hp ⊢
  rw [numAt_congr h (fit 0 (by omega)), numAt_congr h (fit 5 (by omega)), numAt_congr h (fit 9 (by omega)),
    numAt_congr h (fit 10 (by omega))]
  refine ⟨hp.1, hp.2.1, ?_, hp.2.2.2⟩
  have e1 : m'.readW (ws + BitVec.ofNat 64 (arrAt w 0)) 64 = m.readW (ws + BitVec.ofNat 64 (arrAt w 0)) 64 :=
    readW_congr_on h (by simp only [arrAt, Spec.Rsa.Mont.hdrBytes]; omega)
  have e2 : wordAt m' ws Spec.Rsa.Mont.minvWord = wordAt m ws Spec.Rsa.Mont.minvWord :=
    readW_congr_on h (by simp only [Spec.Rsa.Mont.minvWord]; omega)
  rw [e1, e2]
  exact hp.2.2.1

end

end VG.Proof.MillerRabin.Arm
