module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Divstep.SignedWords
public import VerifiedGarbage.Proof.Divstep.Alg
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Rsa.AArch64.InvRow
import VerifiedGarbage.Proof.Rsa.AArch64.InvShr
import VerifiedGarbage.Proof.Rsa.AArch64.InvMred
import VerifiedGarbage.Proof.Rsa.Divstep.Batch64
import VerifiedGarbage.Proof.Divstep.MredWords
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops

/-!
# RSA private keys on AArch64: a batch of divsteps after its matrix

With the batch's matrix in the lanes of `v16` and `v17`, the rest of a
batch of `Keys.inverse`: `(f, g) := (u f + v g, q f + r g) / 2^59`
(`fgStage_ok`: two linear combinations, `rowP_ok`, then two shifts,
`shrP_ok`) and `(a, b) := (mredRaw (u a + v b), mredRaw (q a + r b))`
(`abStage_ok`: two linear combinations then two Montgomery words,
`mredP_ok`), as signed numbers of `n + 1` words (`Divstep.sgn`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Divstep (sgn)

/-- The values of an array that a piece leaves alone. -/
theorem wv_out {m m' : Mem} {B : Addr} {w o n j L : Nat} (h : Outside B (slot w o) n m m') (hjo : o ≠ j)
    (hn : n ≤ 8 * (w + 2)) (hL : L ≤ w + 2) (hZ : slot w 16 + B.toNat ≤ 2 ^ 64) (hj : j < 16) :
    wv m' B (slot w j) L = wv m B (slot w j) L := by
  have := slot_lt (w := w) hj
  exact h.wv (by rcases slot_apart (w := w) (a := 8 * L) (b := n) hjo.symm (by omega) hn with h' | h' <;> omega) (by omega)

/-- The `f`, `g` half of a batch: `(f, g) := (u f + v g, q f + r g) / 2^59`. -/
theorem fgStage_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iF iG iT : Nat}
    (hF : iF < 16) (hG : iG < 16) (hT : iT < 16) (dFG : iF ≠ iG) (dFT : iF ≠ iT) (dGT : iG ≠ iT)
    {u v q r f g f' g' : Int} (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (lu : laneOf s .v16 0 = BitVec.ofInt 64 u) (lv : laneOf s .v16 1 = BitVec.ofInt 64 v)
    (lq : laneOf s .v17 0 = BitVec.ofInt 64 q) (lr : laneOf s .v17 1 = BitVec.ofInt 64 r)
    (hf : sgn (n + 1) (wv s.mem B (slot w iF) (n + 1)) = f) (hg : sgn (n + 1) (wv s.mem B (slot w iG) (n + 1)) = g)
    (bf : |f| < 2 ^ (64 * n + 1)) (bg : |g| < 2 ^ (64 * n + 1))
    (ef : u * f + v * g = 2 ^ 59 * f') (eg : q * f + r * g = 2 ^ 59 * g') :
    WP isa (seqs [rowP .v16 iF iG iT, rowP .v17 iF iG iG, shrP iT iF, shrP iG iG]) s fun t =>
      sgn (n + 1) (wv t.mem B (slot w iF) (n + 1)) = f' ∧ sgn (n + 1) (wv t.mem B (slot w iG) (n + 1)) = g' ∧
      Frm B [(slot w iT, 8 * (n + 1)), (slot w iG, 8 * (n + 1)), (slot w iF, 8 * (n + 1))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have hZ' : slot w 16 + B.toNat ≤ 2 ^ 64 := by omega
  obtain ⟨u0, u1, v0, v1, uvA⟩ := Rsa.Divstep.row_parts huv
  obtain ⟨q0, q1, r0, r1, qrA⟩ := Rsa.Divstep.row_parts hqr
  obtain ⟨f0, f1⟩ := Rsa.Divstep.abs_lt_parts bf
  obtain ⟨g0, g1⟩ := Rsa.Divstep.abs_lt_parts bg
  have tu : (laneOf s .v16 0).toInt = u := by rw [lu]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tv : (laneOf s .v16 1).toInt = v := by rw [lv]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tq : (laneOf s .v17 0).toInt = q := by rw [lq]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tr : (laneOf s .v17 1).toInt = r := by rw [lr]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have hL : (1 : Nat) ≤ n + 1 := by omega
  obtain ⟨cr10, cr11⟩ := Rsa.Divstep.comb_range huv bf bg
  obtain ⟨cr20, cr21⟩ := Rsa.Divstep.comb_range hqr bf bg
  simp only [seqs]
  -- `[t] := u f + v g`.
  refine WP.seq (WP.mono (rowP_ok hs h0 h11 h12 hn hw hZ (.inl rfl) hF hG hT
    (by simp only [laneOf, Nat.mul_zero, Nat.mul_one] at tu tv; rw [tu, tv]; exact uvA))
    fun s₁ ⟨c₁, e₁, o₁, k₁, v₁⟩ => ?_)
  have F₁ := wv_out (L := n + 1) o₁ dFT.symm (by omega) (by omega) hZ' hF
  have G₁ := wv_out (L := n + 1) o₁ dGT.symm (by omega) (by omega) hZ' hG
  have sT : sgn (n + 1) (wv s₁.mem B (slot w iT) (n + 1)) = u * f + v * g := by
    simp only [laneOf, Nat.mul_zero, Nat.mul_one] at tu tv
    rw [tu, tv] at e₁
    rw [← hf, ← hg]
    exact Divstep.lin_sgn hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (wv_lt _ _ _ _) e₁ (by rw [hf, hg]; exact cr10)
      (by rw [hf, hg]; exact cr11)
  -- `[g] := q f + r g`.
  have e0 : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  have e11 : s₁.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr .x11 (by decide)).trans h11
  have e12 : s₁.gpr .x12 = BitVec.ofNat 64 n := (k₁.gpr .x12 (by decide)).trans h12
  have tq' : (laneOf s₁ .v17 0).toInt = q := by rw [laneOf, v₁]; exact tq
  have tr' : (laneOf s₁ .v17 1).toInt = r := by rw [laneOf, v₁]; exact tr
  simp only [laneOf, Nat.mul_zero, Nat.mul_one] at tq' tr'
  refine WP.seq (WP.mono (rowP_ok (hs.congr k₁.wr) e0 e11 e12 hn hw hZ (.inr rfl) hF hG hG
    (by rw [tq', tr']; exact qrA)) fun s₂ ⟨c₂, e₂, o₂, k₂, v₂⟩ => ?_)
  have sG₂ : sgn (n + 1) (wv s₂.mem B (slot w iG) (n + 1)) = q * f + r * g := by
    rw [tq', tr', F₁, G₁] at e₂
    rw [← hf, ← hg]
    exact Divstep.lin_sgn hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (wv_lt _ _ _ _) e₂ (by rw [hf, hg]; exact cr20)
      (by rw [hf, hg]; exact cr21)
  have T₂ := wv_out (L := n + 1) o₂ dGT (by omega) (by omega) hZ' hT
  have F₂ := wv_out (L := n + 1) o₂ dFG.symm (by omega) (by omega) hZ' hF
  -- `[f] := [t] >> 59`.
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (shrP_ok (hs.congr k12.wr) ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11) ((k12.gpr .x12 (by decide)).trans h12) hn1 hn hw hZ hT hF)
    fun s₃ ⟨e₃, o₃, k₃, v₃⟩ => ?_)
  have hf' : sgn (n + 1) (wv s₃.mem B (slot w iF) (n + 1)) = f' := by
    rw [T₂, sT, ef] at e₃
    have := Nat.mod_lt (wv s₁.mem B (slot w iT) (n + 1)) (show 0 < 2 ^ 59 by decide)
    omega
  have G₃ := wv_out (L := n + 1) o₃ dFG (by omega) (by omega) hZ' hG
  -- `[g] := [g] >> 59`.
  have k13 := k12.trans k₃
  refine WP.mono (shrP_ok (hs.congr k13.wr) ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11) ((k13.gpr .x12 (by decide)).trans h12) hn1 hn hw hZ hG hG)
    fun t ⟨e₄, o₄, k₄, v₄⟩ => ⟨?_, ?_, ?_, (k13.trans k₄).mono (by decide), by rw [v₄, v₃, v₂, v₁]⟩
  · rw [wv_out (L := n + 1) o₄ dFG.symm (by omega) (by omega) hZ' hF]; exact hf'
  · rw [G₃, sG₂, eg] at e₄
    have := Nat.mod_lt (wv s₂.mem B (slot w iG) (n + 1)) (show 0 < 2 ^ 59 by decide)
    omega
  · exact (((Frm.of_outside o₁ (by simp)).trans (Frm.of_outside o₂ (by simp))).trans
      (Frm.of_outside o₃ (by simp))).trans (Frm.of_outside o₄ (by simp))

/-- A frame by smaller ranges is one by larger. -/
theorem Frm.widen {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' :=
  fun x hx => h x fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := hs r hr
    have := hx r' hr'
    omega

/-- The `a`, `b` half of a batch: `(a, b) := (mredRaw (u a + v b), mredRaw (q a + r b))`. -/
theorem abStage_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iB iT iM : Nat}
    (hA : iA < 16) (hB : iB < 16) (hT : iT < 16) (hM : iM < 16) (dAB : iA ≠ iB) (dAT : iA ≠ iT) (dBT : iB ≠ iT)
    (dAM : iA ≠ iM) (dBM : iB ≠ iM) (dTM : iT ≠ iM)
    {u v q r a b a' b' : Int} {p : Nat} (hp : p < 2 ^ (64 * n)) (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (lu : laneOf s .v16 0 = BitVec.ofInt 64 u) (lv : laneOf s .v16 1 = BitVec.ofInt 64 v)
    (lq : laneOf s .v17 0 = BitVec.ofInt 64 q) (lr : laneOf s .v17 1 = BitVec.ofInt 64 r)
    (hm : ((p : Int) * (laneOf s .v18 1).toNat + 1) % 2 ^ 64 = 0) (hpm : wv s.mem B (slot w iM) n = p)
    (ha : sgn (n + 1) (wv s.mem B (slot w iA) (n + 1)) = a) (hb : sgn (n + 1) (wv s.mem B (slot w iB) (n + 1)) = b)
    (ra : -(p : Int) < a ∧ a < 2 * p) (rb : -(p : Int) < b ∧ b < 2 * p)
    (ea : a' = Divstep.mredRaw p (laneOf s .v18 1).toNat (u * a + v * b))
    (eb : b' = Divstep.mredRaw p (laneOf s .v18 1).toNat (q * a + r * b))
    (ra' : -(p : Int) < a' ∧ a' < 2 * p) (rb' : -(p : Int) < b' ∧ b' < 2 * p) :
    WP isa (seqs ([rowP .v16 iA iB iT, rowP .v17 iA iB iB] ++ mredP iT iM iA ++ mredP iB iM iB)) s fun t =>
      sgn (n + 1) (wv t.mem B (slot w iA) (n + 1)) = a' ∧ sgn (n + 1) (wv t.mem B (slot w iB) (n + 1)) = b' ∧
      Frm B [(slot w iT, 8 * (w + 2)), (slot w iA, 8 * (w + 2)), (slot w iB, 8 * (w + 2))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have hZ' : slot w 16 + B.toNat ≤ 2 ^ 64 := by omega
  obtain ⟨u0, u1, v0, v1, uvA⟩ := Rsa.Divstep.row_parts huv
  obtain ⟨q0, q1, r0, r1, qrA⟩ := Rsa.Divstep.row_parts hqr
  obtain ⟨baa, -, -⟩ := Rsa.Divstep.range_parts ra hp
  obtain ⟨bbb, -, -⟩ := Rsa.Divstep.range_parts rb hp
  obtain ⟨-, ra0, ra1⟩ := Rsa.Divstep.range_parts ra' hp
  obtain ⟨-, rb0, rb1⟩ := Rsa.Divstep.range_parts rb' hp
  obtain ⟨cr10, cr11⟩ := Rsa.Divstep.comb_range huv baa bbb
  obtain ⟨cr20, cr21⟩ := Rsa.Divstep.comb_range hqr baa bbb
  have tu : (laneOf s .v16 0).toInt = u := by rw [lu]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tv : (laneOf s .v16 1).toInt = v := by rw [lv]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tq : (laneOf s .v17 0).toInt = q := by rw [lq]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tr : (laneOf s .v17 1).toInt = r := by rw [lr]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  simp only [laneOf, Nat.mul_zero, Nat.mul_one] at tu tv tq tr
  have hL : (1 : Nat) ≤ n + 1 := by omega
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [mredP]) ?_
  simp only [seqs]
  -- `[t] := u a + v b`, `[b] := q a + r b`.
  refine WP.seq (WP.mono (rowP_ok hs h0 h11 h12 hn hw hZ (.inl rfl) hA hB hT (by rw [tu, tv]; exact uvA))
    fun s₁ ⟨c₁, e₁, o₁, k₁, v₁⟩ => ?_)
  have A₁ := wv_out (L := n + 1) o₁ dAT.symm (by omega) (by omega) hZ' hA
  have B₁ := wv_out (L := n + 1) o₁ dBT.symm (by omega) (by omega) hZ' hB
  have M₁ := wv_out (L := n) o₁ dTM (by omega) (by omega) hZ' hM
  have sT : sgn (n + 1) (wv s₁.mem B (slot w iT) (n + 1)) = u * a + v * b := by
    rw [tu, tv] at e₁
    rw [← ha, ← hb]
    exact Divstep.lin_sgn hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (wv_lt _ _ _ _) e₁ (by rw [ha, hb]; exact cr10)
      (by rw [ha, hb]; exact cr11)
  have e0 : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  have e11 : s₁.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr .x11 (by decide)).trans h11
  have e12 : s₁.gpr .x12 = BitVec.ofNat 64 n := (k₁.gpr .x12 (by decide)).trans h12
  have tq' : ((s₁.v .v17).extractLsb' 0 64).toInt = q := by rw [v₁]; exact tq
  have tr' : ((s₁.v .v17).extractLsb' 64 64).toInt = r := by rw [v₁]; exact tr
  refine WP.mono (rowP_ok (hs.congr k₁.wr) e0 e11 e12 hn hw hZ (.inr rfl) hA hB hB
    (by rw [tq', tr']; exact qrA)) fun s₂ ⟨c₂, e₂, o₂, k₂, v₂⟩ => ?_
  have sB₂ : sgn (n + 1) (wv s₂.mem B (slot w iB) (n + 1)) = q * a + r * b := by
    rw [tq', tr', A₁, B₁] at e₂
    rw [← ha, ← hb]
    exact Divstep.lin_sgn hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (wv_lt _ _ _ _) e₂ (by rw [ha, hb]; exact cr20)
      (by rw [ha, hb]; exact cr21)
  have T₂ := wv_out (L := n + 1) o₂ dBT (by omega) (by omega) hZ' hT
  have M₂ := wv_out (L := n) o₂ dBM (by omega) (by omega) hZ' hM
  have k12 := k₁.trans k₂
  have lm : (s₂.v .v18).extractLsb' 64 64 = laneOf s .v18 1 := by rw [v₂, v₁]
  -- `[a] := mredRaw [t]`.
  refine wp_seqs_append (by simp [mredP]) (by simp [mredP]) (WP.mono (mredP_ok (hs.congr k12.wr)
    ((k12.gpr .x0 (by decide)).trans h0) ((k12.gpr .x11 (by decide)).trans h11)
    ((k12.gpr .x12 (by decide)).trans h12) hn1 hn hw hZ hT hM hA dTM dAM
    (by rw [lm, M₂, M₁, hpm]; exact hm)) fun s₃ ⟨e₃, f₃, k₃, v₃⟩ => ?_)
  rw [lm, M₂, M₁, hpm, T₂, sT, ← ea] at e₃
  have sA₃ : sgn (n + 1) (wv s₃.mem B (slot w iA) (n + 1)) = a' :=
    Divstep.sgn_of_emod hL ra0 ra1 e₃
  have B₃ : wv s₃.mem B (slot w iB) (n + 1) = wv s₂.mem B (slot w iB) (n + 1) :=
    f₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * (n + 2)) dBT (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h
      · rcases slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * (n + 1)) dAB.symm (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h) (by have := slot_lt (w := w) hB; omega)
  have M₃ : wv s₃.mem B (slot w iM) n = wv s₂.mem B (slot w iM) n :=
    f₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases slot_apart (w := w) (a := 8 * n) (b := 8 * (n + 2)) dTM.symm (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h
      · rcases slot_apart (w := w) (a := 8 * n) (b := 8 * (n + 1)) dAM.symm (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h) (by have := slot_lt (w := w) hM; omega)
  have k13 := k12.trans k₃
  have lm' : (s₃.v .v18).extractLsb' 64 64 = laneOf s .v18 1 := by rw [v₃, lm]
  -- `[b] := mredRaw [b]`.
  refine WP.mono (mredP_ok (hs.congr k13.wr) ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11) ((k13.gpr .x12 (by decide)).trans h12) hn1 hn hw hZ hB hM hB dBM dBM
    (by rw [lm', M₃, M₂, M₁, hpm]; exact hm)) fun t ⟨e₄, f₄, k₄, v₄⟩ => ⟨?_, ?_, ?_, (k13.trans k₄).mono (by decide),
      by rw [v₄, v₃, v₂, v₁]⟩
  · rw [f₄.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * (n + 2)) dAB (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h
      · rcases slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * (n + 1)) dAB (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h) (by have := slot_lt (w := w) hA; omega)]
    exact sA₃
  · rw [lm', M₃, M₂, M₁, hpm, B₃, sB₂, ← eb] at e₄
    exact Divstep.sgn_of_emod hL rb0 rb1 e₄
  · refine (((Frm.widen (Frm.of_outside o₁ (List.mem_singleton.mpr rfl)) ?_).trans
      (Frm.widen (Frm.of_outside o₂ (List.mem_singleton.mpr rfl)) ?_)).trans (Frm.widen f₃ ?_)).trans
      (Frm.widen f₄ ?_)
    all_goals
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp <;> omega
end VG.Proof.Rsa.AArch64