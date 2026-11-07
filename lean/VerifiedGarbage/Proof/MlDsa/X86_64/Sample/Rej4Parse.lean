module
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt4
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttLoop
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Base

import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNtt
import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, sampling

Each half of a seed's sampling (`half`) runs 168 iterations of
`vg_mldsa_rej_ntt_poly`'s loop (`rnBody_ok`) on the 504 bytes of the seed's
buffer, which hold bytes `504 h` to `504 h + 503` of its output `Xb` (`G` of
the seed, as `vg_mldsa_rej_ntt_poly` squeezes it: `Xb_getD`). The
coefficients written so far (`coeffsWr`), and what a write to the seed's
polynomial keeps (`frame_byte`, `sub_poly`, `scr_poly`, `poly_poly`,
`env_poly`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half)
open VG.Proof.MlKem.X86_64 (Keep ea_at wp_countdown add_ofNat_zero pR WP.keep ofNat64_pred)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold rnStep rnFold_snoc rnFold_length_le Stored stored_nil stored_frame G_eq G_length)
open VG.Proof.MlDsa.X86_64.Sample (rnBody_ok CoeffsWr)
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlKem (xofByte xof_squeezeFrom_getElem)

/-- ML-KEM's `S4.Env`, which this function shares. -/
abbrev EnvK := VG.Proof.MlKem.X86_64.S4.Env

/-- The 1008 bytes of output of seed `k`, which `vg_mldsa_rej_ntt_poly` samples from. -/
abbrev Xb (σ : State) (k : Nat) : List Byte := Spec.MlDsa.G (B σ k) 1008

theorem Xb_getD (σ : State) (k : Nat) {p : Nat} (hp : p < 1008) : (Xb σ k).getD p 0 = xofByte (B σ k) p := by
  have e := xof_squeezeFrom_getElem (B σ k) (pos := 0) (d := 1008) hp
  rw [Nat.zero_add] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Xb, G_length]; exact hp), Option.getD_some, ← e]
  simp only [Xb, G_eq]

/-- The coefficients of seed `k` after `n` iterations. -/
abbrev Lt (σ : State) (k n : Nat) : List Zq := rnFold [] ((Xb σ k).take (3 * n))

theorem Lt_length_le (σ : State) (k n : Nat) : (Lt σ k n).length ≤ 256 := rnFold_length_le (by simp) _

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A byte the frame's regions are apart from is unchanged. -/
theorem frame_byte {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region} (hd : ∀ r ∈ rs, R.Disjoint r)
    {x : Addr} (hx : R.Contains x 1) : m' x = m x :=
  hf x fun r hr hc => hd r hr x hx hc

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
/-- Polynomial `K` lies in `a`. -/
theorem sub_poly {K : Nat} (hK : K < 4) : Region.Sub (pR (Proof.MlKem.poly4 (aP σ) K)) (aR σ) := Offset.sub_base _ (by omega)

/-- A part of the scratch space is apart from polynomial `K`. -/
theorem scr_poly {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ 8192) :
    ∀ r ∈ [pR (Proof.MlKem.poly4 (aP σ) K)], Region.Disjoint ⟨at' σ a, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Region.Disjoint.sub_right (Region.Disjoint.sub_left hp.a_scr.symm (sub_scr h)) (sub_poly hK)

omit hp in
/-- Two polynomials are apart. -/
theorem poly_poly {K k : Nat} (hK : K < 4) (hk : k < 4) (hne : k ≠ K) :
    ∀ r ∈ [pR (Proof.MlKem.poly4 (aP σ) K)], (VG.Proof.MlDsa.Sample.polyR (Proof.MlKem.poly4 (aP σ) k)).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega) (by omega)
    (by omega)

/-- Writes to polynomial `K` keep `Env`. -/
theorem env_poly {K : Nat} (hK : K < 4) {s s' : State} (he : EnvK σ s)
    (hf : Frame [pR (Proof.MlKem.poly4 (aP σ) K)] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : EnvK σ s' := by
  have hsub := sub_poly (σ := σ) hK
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, he.frame.trans (hf.sub fun r hr => ?_)⟩
  · rw [hf.readW (Region.contains_self _ _) (scr_poly hp hK (by simp only [oSave]; omega)) (by decide)]
    exact he.saved i hi
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨aR σ, by simp, hsub⟩

/-- Each coefficient of polynomial `K` is writable. -/
theorem coeffsWr {K : Nat} (hK : K < 4) {s : State} (he : EnvK σ s) : CoeffsWr s.wr (Proof.MlKem.poly4 (aP σ) K) := by
  intro j hj
  rw [he.wr, hp.wr]
  refine ⟨aR σ, by simp, ?_⟩
  rw [VG.Proof.MlDsa.Sample.coeffAddr, Proof.MlKem.poly4, Offset.add_add]
  exact Offset.contains_base _ (by omega) (by omega)

end

/-! ## A half -/

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem sxP {K : Nat} (hK : K < 4) : BitVec.signExtend 64 (BitVec.ofNat 32 (1024 * K)) =
    BitVec.ofNat 64 (1024 * K) := sx_ofNat (by omega)

end

end VG.Proof.MlDsa.X86_64.Rej4
