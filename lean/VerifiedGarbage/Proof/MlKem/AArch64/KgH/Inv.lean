module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgRows
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart

/-! # Key generation hashing `ek` during the matrix: its invariant

`Kem16P.keyGen` samples `Â` pair by pair and computes each row of `t̂` as soon
as its entries are sampled, while the third state of the `x3` calls absorbs the
blocks of `ek` the rows before have encoded. `IL n r h`: after `n` entries of
`Â`, `r` rows of `t̂` (encoded into both keys, over `Â` as memory holds it) and
`h` blocks of `ek` absorbed into the third state, at `scratch`; `Stk128K`, the
128 bytes below the stack pointer those calls use. `row_step`: a row keeps it. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (TStk hstate dB frame)
open VG.Impl.MlKem.AArch64.Noise (noiseOff)

variable {P : KemLay}

/-- The 128 bytes below the stack pointer, apart from the arguments. -/
structure Stk128K (P : KemLay) (s₀ : State) : Prop where
  sp : 128 ≤ s₀.sp.toNat
  args : ∀ b < 4, (frame s₀.sp).Disjoint ⟨kA s₀ b, kL P b⟩

theorem Stk128K.R {s₀ : State} (hk : Stk128K P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b) :
    (frame s₀.sp).Disjoint (R (kA s₀) b o l) :=
  (hk.args b hb).sub_right (R.sub f)

theorem foldK_congr {α : Type} {op : α → α → α} {z : α} {f g : Nat → α} :
    ∀ {k : Nat}, (∀ j < k, f j = g j) → KPke.foldK op z f k = KPke.foldK op z g k
  | 0, _ => rfl
  | 1, h => by simp only [KPke.foldK]; exact h 0 (by decide)
  | k + 2, h => by
    simp only [KPke.foldK]
    rw [foldK_congr (k := k + 1) (fun j hj => h j (by omega)), h (k + 1) (by omega)]

/-- Row `i` of `t̂` depends on row `i` of `Â` alone. -/
theorem tVW_congr {s₀ : State} {m m' : Mem} {i : Nat}
    (h : ∀ j < P.k, polyAtW 16 m (AR s₀ (P.k * i + j)) = polyAtW 16 m' (AR s₀ (P.k * i + j))) :
    tVW P s₀ m i = tVW P s₀ m' i := by
  simp only [tVW, KPke.kgT, KPke.dotK]
  rw [foldK_congr (fun j hj => by simp only [aMW]; rw [h j hj])]

/-- The hash of the first `b` blocks depends on their bytes alone. -/
theorem hstate_prefix {m m' : Mem} {p : Addr} {len b : Nat} {d : Byte} (hb : 136 * b ≤ len)
    (h : bytesAt m p (136 * b) = bytesAt m' p (136 * b)) :
    hstate (bytesAt m p len) b d = hstate (bytesAt m' p len) b d := by
  simp only [hstate, VG.Proof.MlKem.bytesAt_length, hb, ↓reduceIte,
    VG.Proof.MlKem.bytesAt_take _ _ hb, h]

/-- Rows `i' < r` of `t̂` encoded into both keys, over `Â` as `m` holds it. -/
def RowsDone (P : KemLay) (s₀ : State) (m : Mem) (r : Nat) : Prop :=
  ∀ i' < r, bytesAt m (kA s₀ 1 + BitVec.ofNat 64 (384 * i')) 384 = encode12 (tVW P s₀ m i') ∧
    bytesAt m (kA s₀ 2 + BitVec.ofNat 64 (384 * P.k + 384 * i')) 384 = encode12 (tVW P s₀ m i')

/-- After `G`, the noise, `ŝ` into `dk` and the all-zero third state: `n`
entries of `Â`, `r` rows of `t̂`, and `h` blocks of `ek` absorbed into the third
state (at `scratch`). -/
structure IL (P : KemLay) (s₀ : State) (n r h : Nat) (s : State) : Prop where
  b : BInvW true P s₀ n s
  sp : ∀ j < P.k, PolyIsW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  errors : ErrorsK P s₀ s
  dk : ∀ j < P.k, bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * j)) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j)
  rows : RowsDone P s₀ s.mem r
  rn : P.k * r ≤ n
  le : n ≤ P.k * P.k
  rk : r ≤ P.k
  hash : stateAt s.mem (kA s₀ 3) =
    hstate (bytesAt s.mem (kA s₀ 1) P.ekLen) h (Hybrid.dB (Impl.MlKem.AArch64.Kem16.kgSrc P))
  hr : 136 * h ≤ 384 * r
  tables : Tables s
  tstk : TStk s

/-- Writes that leave the rows' memory in `scratch`'s first 200 bytes, `ek` before
`384 r` and the matrix's first `n` entries as they were. -/
theorem IL.rowsDone_frame {s₀ : State} {m m' : Mem} {n r : Nat} (hrn : P.k * r ≤ n) (hr : RowsDone P s₀ m r)
    {W : List Region} (hf : Frame W m m')
    (hA : ∀ e < n, ∀ q ∈ W, (polyRegion (AR s₀ e)).Disjoint q)
    (hE : ∀ i' < r, ∀ q ∈ W, (R (kA s₀) 1 (384 * i') 384).Disjoint q ∧
      (R (kA s₀) 2 (384 * P.k + 384 * i') 384).Disjoint q) :
    RowsDone P s₀ m' r := by
  intro i' hi'
  have ht : tVW P s₀ m' i' = tVW P s₀ m i' := tVW_congr fun j hj =>
    polyAtW_frame (w16 := true) hf (hA _ (by
      have := Nat.mul_le_mul_left P.k (show i' + 1 ≤ r by omega)
      rw [Nat.mul_succ] at this; omega))
  rw [ht, bytesAt_frame hf (fun q hq => (hE i' hi' q hq).1) (by decide),
    bytesAt_frame hf (fun q hq => (hE i' hi' q hq).2) (by decide)]
  exact hr i' hi'

end VG.Proof.MlKem.AArch64.KeyGen
