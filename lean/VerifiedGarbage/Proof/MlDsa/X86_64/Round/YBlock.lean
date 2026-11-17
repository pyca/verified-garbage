module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Avx2
public import VerifiedGarbage.Proof.MlDsa.Round.Decompose
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlKem.X86_64.VLanes
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! ### `MlDsa.X86_64.Round.YLane`, which only this module used -/

section

/-!
# ML-DSA on x86-64: what the AVX2 rounding code computes in a doubleword

What `hbX` and `lbX` (`Impl/MlDsa/X86_64/Round/Avx2.lean`) compute in each
doubleword (`hbL`, `lbL`), and that it is `r₁` and `r₀` of `Decompose`
(`hbL_toNat`, `lbL_toNat`): every intermediate value fits in 32 bits.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Spec.MlDsa (q ofInt lowBits)
open VG.Proof.MlDsa (gamma2s)
open VG.Proof.MlDsa.Round (hbF hbM q_eq mem_gamma2s hbF_le hbF_eq hbM_mul lowBits_val)
open VG.Proof.MlDsa.X86_64.Arith (caddL caddL_toNat sshiftRight31)

/-- `t · (1 + Σ 2^k)` by shifts and additions, as `mulX` computes it. -/
def mulL (sh : List Nat) (t : BitVec 32) : BitVec 32 := sh.foldl (fun acc k => acc + (t <<< k)) t

theorem foldl_toNat (t : BitVec 32) : ∀ (sh : List Nat) (acc : BitVec 32),
    acc.toNat + t.toNat * (sh.map (2 ^ ·)).sum < 2 ^ 32 →
      (sh.foldl (fun acc k => acc + (t <<< k)) acc).toNat = acc.toNat + t.toNat * (sh.map (2 ^ ·)).sum
  | [], acc, _ => by simp
  | k :: sh, acc, h => by
    simp only [List.map_cons, List.sum_cons, Nat.mul_add] at h ⊢
    have hk : (t <<< k).toNat = t.toNat * 2 ^ k := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_using [h])]
    have ha : (acc + t <<< k).toNat = acc.toNat + t.toNat * 2 ^ k := by
      rw [BitVec.toNat_add, hk, Nat.mod_eq_of_lt (by omega_using [h])]
    rw [List.foldl_cons, foldl_toNat t sh _ (by rw [ha]; omega_using [h]), ha]
    omega_using []

theorem mulL_toNat (sh : List Nat) {t : BitVec 32} (h : t.toNat * (1 + (sh.map (2 ^ ·)).sum) < 2 ^ 32) :
    (mulL sh t).toNat = t.toNat * (1 + (sh.map (2 ^ ·)).sum) := by
  rw [mulL, foldl_toNat t sh t (by rw [Nat.mul_add] at h; omega_using [h]), Nat.mul_add]; omega_using []

theorem dSh_sum {g : Nat} (h : g ∈ gamma2s) : 1 + ((dSh g).map (2 ^ ·)).sum = dMul g := by
  rcases mem_gamma2s h with rfl | rfl <;> rfl

/-- `f`, as `hbX` computes it in a doubleword. -/
def hbFL (g : Nat) (x : BitVec 32) : BitVec 32 :=
  (mulL (dSh g) ((x + BitVec.ofNat 32 127) >>> 7) + BitVec.ofNat 32 (dAdd g)) >>> dShift g

/-- What `hbX` computes in a doubleword. -/
def hbL (g : Nat) (x : BitVec 32) : BitVec 32 :=
  hbFL g x &&& (hbFL g x - BitVec.ofNat 32 (dMod g)).sshiftRight (min (31 : BitVec 8).toNat 32)

theorem dMod_eq' {g : Nat} (h : g ∈ gamma2s) : dMod g = hbM g := by
  rcases mem_gamma2s h with rfl | rfl <;> rfl

/-- `f` in 32 bits. -/
theorem hbF32 {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (hbFL g x).toNat = hbF g x.toNat := by
  rw [q_eq] at hx
  have e1 : (x + BitVec.ofNat 32 127).toNat = x.toNat + 127 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hx]
  have e2 : ((x + BitVec.ofNat 32 127) >>> 7).toNat = (x.toNat + 127) / 128 := by
    rw [BitVec.toNat_ushiftRight, e1, Nat.shiftRight_eq_div_pow]
  have hM : dMul g ≤ 11275 := by unfold dMul; split <;> decide
  have hA : dAdd g ≤ 2 ^ 23 := by unfold dAdd; split <;> decide
  have hp : (x.toNat + 127) / 128 * dMul g ≤ 65473 * 11275 := Nat.mul_le_mul (by omega_using [hx]) hM
  have e3 : (mulL (dSh g) ((x + BitVec.ofNat 32 127) >>> 7)).toNat = (x.toNat + 127) / 128 * dMul g := by
    rw [mulL_toNat _ (by rw [e2, dSh_sum h]; omega_using [hp]), e2, dSh_sum h]
  have e4 : (mulL (dSh g) ((x + BitVec.ofNat 32 127) >>> 7) + BitVec.ofNat 32 (dAdd g)).toNat =
      (x.toNat + 127) / 128 * dMul g + dAdd g := by
    rw [BitVec.toNat_add, e3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show dAdd g < 2 ^ 32 by omega_using [hA])]; omega_using [hA, hp]
  rw [hbFL, BitVec.toNat_ushiftRight, e4, Nat.shiftRight_eq_div_pow, hbF_eq h (by rw [q_eq]; exact hx)]
  rfl

theorem hbL_toNat {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (hbL g x).toNat = hbF g x.toNat % hbM g := by
  have hf := hbF32 h hx
  have hle := hbF_le h hx
  have hm : dMod g ≤ 44 ∧ 16 ≤ dMod g := by unfold dMod; split <;> decide
  rw [← dMod_eq' h] at hle ⊢
  unfold hbL
  generalize hbFL g x = f at hf ⊢
  rw [sshiftRight31]
  have hsub : (f - BitVec.ofNat 32 (dMod g)).toNat = (f.toNat + 2 ^ 32 - dMod g) % 2 ^ 32 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show dMod g < 2 ^ 32 by omega_using [hm])]; omega_using [hm]
  by_cases e : hbF g x.toNat = dMod g
  · rw [ite_eq_left (by rw [hsub, hf, e]; omega_using []), show f &&& (0 : BitVec 32) = 0 from BitVec.and_zero, e, Nat.mod_self]; rfl
  · rw [ite_eq_right (by rw [hsub, hf]; omega_using [hle, hm, e]), show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes,
      hf, Nat.mod_eq_of_lt (by omega_using [hle, e])]

/-- `r₁ · 2γ₂` by shifts and additions, as `mul2X` computes it. -/
def mul2L (g : Nat) (r : BitVec 32) : BitVec 32 :=
  if g = 261888 then r <<< 19 - r <<< 9
  else [13, 14, 15, 17].foldl (fun acc k => acc + (r <<< k)) (r <<< 11)

theorem mul2L_toNat {g : Nat} (h : g ∈ gamma2s) {r : BitVec 32} (hr : r.toNat ≤ 44) :
    (mul2L g r).toNat = r.toNat * (2 * g) := by
  have s : ∀ k ≤ 19, (r <<< k).toNat = r.toNat * 2 ^ k := fun k hk => by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    calc r.toNat * 2 ^ k ≤ 44 * 2 ^ 19 := Nat.mul_le_mul hr (Nat.pow_le_pow_right (by decide) hk)
      _ < 2 ^ 32 := by decide
  rcases mem_gamma2s h with rfl | rfl
  · unfold mul2L
    rw [ite_eq_right (by decide)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, s 11 (by decide), s 13 (by decide),
      s 14 (by decide), s 15 (by decide), s 17 (by decide)]
    omega_using [hr]
  · unfold mul2L
    rw [ite_eq_left rfl, BitVec.toNat_sub, s 19 (by decide), s 9 (by decide)]
    omega_using [hr]

/-- What `lbX` computes in a doubleword. -/
def lbL (g : Nat) (x : BitVec 32) : BitVec 32 := caddL (x - mul2L g (hbL g x))

theorem lbL_toNat {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (lbL g x).toNat = (ofInt (lowBits g (Fin.ofNat q x.toNat))).val := by
  have hv : (Fin.ofNat q x.toNat).val = x.toNat := Nat.mod_eq_of_lt hx
  rw [lowBits_val h, hv]
  have hlt : hbF g x.toNat % hbM g < hbM g := Nat.mod_lt _ (by rcases mem_gamma2s h with rfl | rfl <;> decide)
  have hM : hbM g ≤ 44 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have hle : hbF g x.toNat % hbM g * (2 * g) ≤ q - 1 := by
    rw [← hbM_mul h]; exact Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
  have e1 : (mul2L g (hbL g x)).toNat = hbF g x.toNat % hbM g * (2 * g) := by
    rw [mul2L_toNat h (by rw [hbL_toNat h hx]; omega_using [hlt, hM]), hbL_toNat h hx]
  unfold lbL
  rw [caddL_toNat, BitVec.toNat_sub, e1]
  rw [q_eq] at hx hle ⊢
  split <;> split <;> omega_arith

end VG.Proof.MlDsa.X86_64.Round

end

end


/-!
# ML-DSA on x86-64: the SSE2 code of the AVX2 rounding, on a register

`hbX` and `lbX` compute `hbL` and `lbL` in each doubleword of `xmm0`
(`hbX_ok`, `lbX_ok`), with the constants in `xmm8`, `xmm9`, `xmm10` (and `q`
in `xmm15`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Proof.MlDsa.X86_64.Arith (dword_psubd dword_pand dword_psrad caddL caddV dword_caddV qV
  dword_qV)
open VG.Proof.MlKem.X86_64 (XOnly)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Proof.MlDsa (gamma2s)

/-- Each doubleword of `x` is `v`. -/
def Bc (x : BitVec 128) (v : BitVec 32) : Prop := ∀ e < 4, dword x e = v

theorem bc_ofDwords (v : BitVec 32) : Bc (ofDwords v v v v) v := fun e he => by
  rcases cases4 he with rfl | rfl | rfl | rfl <;> simp

/-- The constants of `hbX`. -/
structure HbC (g : Nat) (s : State) : Prop where
  c8 : Bc (s.xmm .xmm8) (BitVec.ofNat 32 127)
  c9 : Bc (s.xmm .xmm9) (BitVec.ofNat 32 (dAdd g))
  c10 : Bc (s.xmm .xmm10) (BitVec.ofNat 32 (dMod g))

theorem dSh_32 : dSh g32 = [10] := rfl
theorem dSh_88 : dSh g88 = [1, 3, 10, 11, 13] := rfl
theorem dShift_32 : dShift g32 = 22 := rfl
theorem dShift_88 : dShift g88 = 24 := rfl

theorem hbX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc : HbC g s) :
    WP isa (.block (hbX g)) s fun s' => (∀ e < 4, dword (s'.xmm .xmm0) e = hbL g (dword (s.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2] s s' := by
  rcases hg with rfl | rfl <;>
  · simp only [hbX, hfX, mulX, dSh_32, dSh_88, dShift_32, dShift_88, xmov, xb, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    vrun [VG.X86_64.eval_movdqa]
    refine ⟨fun e he => ?_, by xonly⟩
    simp (disch := first | decide | with_reducible assumption) only [dword_pand, dword_psrad, dword_psubd, dword_psrld,
      dword_pslld, dword_paddd, hc.c8 e he, hc.c9 e he, hc.c10 e he, BitVec.toNat_ofNat]
    rfl

/-- `hfX` computes `hbFL` in each doubleword. -/
theorem hfX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc8 : Bc (s.xmm .xmm8) (BitVec.ofNat 32 127))
    (hc9 : Bc (s.xmm .xmm9) (BitVec.ofNat 32 (dAdd g))) :
    WP isa (.block (hfX g)) s fun s' => (∀ e < 4, dword (s'.xmm .xmm0) e = hbFL g (dword (s.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2] s s' := by
  rcases hg with rfl | rfl <;>
  · simp only [hfX, mulX, dSh_32, dSh_88, dShift_32, dShift_88, xmov, xb, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    vrun [VG.X86_64.eval_movdqa]
    refine ⟨fun e he => ?_, by xonly⟩
    simp (disch := first | decide | with_reducible assumption) only [dword_psrld, dword_pslld, dword_paddd,
      hc8 e he, hc9 e he, BitVec.toNat_ofNat]
    rfl

theorem mul2X_32 : mul2X g32 = [xmov .xmm1 .xmm0, .xop (.shift .pslld .xmm1 19), xmov .xmm2 .xmm0,
    .xop (.shift .pslld .xmm2 9), xb .psubd .xmm1 .xmm2] := rfl

theorem mul2X_88 : mul2X g88 = [xmov .xmm1 .xmm0, .xop (.shift .pslld .xmm1 11)] ++ [13, 14, 15, 17].flatMap fun k =>
    [xmov .xmm2 .xmm0, .xop (.shift .pslld .xmm2 (BitVec.ofNat 8 k)), xb .paddd .xmm1 .xmm2] := rfl

/-- `mul2X` computes `mul2L` in each doubleword. -/
theorem mul2X_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) :
    WP isa (.block (mul2X g)) s fun s' =>
      (∀ e < 4, dword (s'.xmm .xmm1) e = mul2L g (dword (s.xmm .xmm0) e)) ∧ XOnly [.xmm1, .xmm2] s s' := by
  rcases hg with rfl | rfl <;>
  · simp only [mul2X_32, mul2X_88, xmov, xb, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    vrun [VG.X86_64.eval_movdqa]
    refine ⟨fun e he => ?_, by xonly⟩
    simp (disch := first | decide | with_reducible assumption) only [dword_psubd, dword_pslld,
      dword_paddd, BitVec.toNat_ofNat]
    rfl

/-- `lbX` as its parts, `hbX_ok` and `mul2X_ok`: unfolding `lbL` into the doublewords
the whole block computes repeats `hbL` in a term the kernel took 20 s to check. -/
theorem lbX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc : HbC g s) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (lbX g)) s fun s' => (∀ e < 4, dword (s'.xmm .xmm3) e = lbL g (dword (s.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3] s s' := by
  rw [show lbX g = [xmov .xmm3 .xmm0] ++ (hbX g ++ (mul2X g ++
      ([xb .psubd .xmm3 .xmm1] ++ VG.Impl.MlDsa.X86_64.Arith.vcadd .xmm3 .xmm1))) by
    simp only [lbX, List.cons_append, List.nil_append, List.append_assoc], WP.block_append_iff]
  simp only [xmov, xb]
  vrun [VG.X86_64.eval_movdqa]
  rw [WP.block_append_iff]
  refine WP.mono (hbX_ok hg _ ⟨?_, ?_, ?_⟩) fun s1 ⟨h1, k1⟩ => ?_
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide)]; exact hc.c8
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide)]; exact hc.c9
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide)]; exact hc.c10
  rw [WP.block_append_iff]
  refine WP.mono (mul2X_ok hg s1) fun s2 ⟨h2, k2⟩ => ?_
  have k : XOnly [.xmm0, .xmm1, .xmm2, .xmm3] s s2 :=
    (((XOnly.refl [.xmm3] s).setXmm (List.mem_singleton_self _) _).trans (k1.trans k2)).mono
      (by decide)
  have h3 : s2.xmm .xmm3 = s.xmm .xmm0 := by
    rw [k2.xmm _ (by decide), k1.xmm _ (by decide), RegUpd.xmm_setXmm_self]
  have h15 : s2.xmm .xmm15 = qV := by
    rw [k.xmm _ (by decide), hq]
  simp only [xb, VG.Impl.MlDsa.X86_64.Arith.vcadd, xmov, List.cons_append, List.nil_append]
  vrun [VG.X86_64.eval_movdqa]
  refine ⟨fun e he => ?_, by (repeat (refine XOnly.setXmm (by simp) ?_ _)) <;> exact k⟩
  rw [h15, show ∀ d, XBinOp.paddd.eval d (XBinOp.pand.eval (XShiftOp.psrad.eval d 31) qV) = caddV d from
    fun _ => rfl, dword_caddV _ he, dword_psubd _ _ he, h3, h2 e he, h1 e he, RegUpd.xmm_setXmm_of_ne _ _ (by decide)]
  rfl

end VG.Proof.MlDsa.X86_64.Round
