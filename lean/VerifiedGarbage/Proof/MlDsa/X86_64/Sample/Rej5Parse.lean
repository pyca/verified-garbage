import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Parse
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (setup parse)
open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half)
open VG.Proof.MlKem.X86_64 (Keep ea_at wp_countdown add_ofNat_zero pR WP.keep ofNat64_pred)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold rnStep rnFold_snoc rnFold_length_le Stored stored_nil stored_frame G_eq G_length)
open VG.Proof.MlDsa.X86_64.Sample (rnBody_ok CoeffsWr)
open VG.Spec.MlKem (poly4 seed4)
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlKem (xofByte xof_squeezeFrom_getElem)

structure HAt (σ s₀ : State) (K h off count t : Nat) (s : State) : Prop where
  env : EnvK σ s
  rsi : s.gpr .rsi = at' σ (oBuf + 504 * K) + BitVec.ofNat 64 (3 * (off + t))
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ K (168 * h + off + t)).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (count - t)
  rbp : s.gpr .rbp = poly4 (aP σ) K
  out : ∀ p < 3 * (off + count), s.mem (at' σ (oBuf + 504 * K + p)) = xofByte (B σ K) (504 * h + p)
  stored : Stored s.mem (poly4 (aP σ) K) (Lt σ K (168 * h + off + t))
  fr : Frame [pR (poly4 (aP σ) K)] s₀.mem s.mem
  kp : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx, .rbp] s₀ s

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem hat_byte {s₀ : State} {K h off count t : Nat} (hh : h < 2) (hspan : off + count ≤ 168) {s : State} (hI : HAt σ s₀ K h off count t s) {j : Nat}
    (hj : 3 * (off + t) + j < 3 * (off + count)) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 j) = (Xb σ K).getD (3 * (168 * h + off + t) + j) 0 := by
  have e := hI.out (3 * (off + t) + j) hj
  rw [at'] at e
  rw [hI.rsi, at', Offset.add_add, Offset.add_add, e, Xb_getD σ K (by omega)]
  congr 1; omega

theorem hat_regions {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hspan : off + count ≤ 168) {s : State} (hI : HAt σ s₀ K h off count t s) {j : Nat}
    (hj : 3 * (off + t) + j < 3 * (off + count)) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 j) 1 := by
  rw [hI.rsi, at', Offset.add_add, Offset.add_add]
  exact in_scr' hp hI.env.rd hI.env.wr (by simp only [oBuf]; omega)

/-- An iteration. -/
theorem hat_step {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) (ht : t < count) {s : State}
    (hI : HAt σ s₀ K h off count t s) :
    WP isa rnBody s fun s' => HAt σ s₀ K h off count (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (count - t) - 1 == 0) := by
  refine WP.mono (rnBody_ok s (aP := poly4 (aP σ) K) hI.rbp hI.rdi (Lt_length_le σ K _) (coeffsWr hp hK hI.env)
    hI.stored (by simpa using hat_regions hp hK hspan hI (j := 0) (by omega)) (hat_regions hp hK hspan hI (by omega))
    (hat_regions hp hK hspan hI (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := hat_byte hh hspan hI (j := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  have ht3 : Lt σ K (168 * h + off + (t + 1)) = rnStep (Lt σ K (168 * h + off + t)) ((Xb σ K).getD (3 * (168 * h + off + t)) 0)
      ((Xb σ K).getD (3 * (168 * h + off + t) + 1) 0) ((Xb σ K).getD (3 * (168 * h + off + t) + 2) 0) := by
    simp only [Lt]
    rw [show 3 * (168 * h + off + (t + 1)) = 3 * (168 * h + off + t) + 3 by omega,
      VG.Proof.MlDsa.X86_64.Sample.RejNtt.take_add_three _ (by rw [Xb, G_length]; omega),
      rnFold_snoc _ (by rw [List.length_take, Xb, G_length]; omega)]
  rw [e0, hat_byte hh hspan hI (j := 1) (by omega), hat_byte hh hspan hI (j := 2) (by omega), ← ht3] at hdi hst
  have hk' : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx] s s' := hk
  refine ⟨⟨env_poly hp hK hI.env hf hk'.2.1 hk'.2.2 fun r hr => hk'.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hsi, hI.rsi, Offset.add_add, show 3 * (off + t) + 3 = 3 * (off + (t + 1)) by omega], hdi,
    by rw [hcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl,
    by rw [hk'.gpr (by decide), hI.rbp],
    fun p hp' => by
      rw [frame_byte hf (scr_poly hp hK (a := oBuf + 504 * K + p) (n := 1) (by simp only [oBuf]; omega))
        (Region.contains_self _ _)]
      exact hI.out p hp',
    hst, hI.fr.trans hf, (hI.kp.trans hk').mono (by simp)⟩, by rw [hz, hI.rcx]⟩

/-- A segment of the buffer, from iteration zero. -/
theorem hloop_ok {s₀ : State} {K h off count : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) (hpos : 0 < count) {s : State} (hI : HAt σ s₀ K h off count 0 s) :
    WP isa (.loop rnBody .ne) s (HAt σ s₀ K h off count count) := by
  refine wp_countdown (N := count) (by omega) (by omega) (fun t u => HAt σ s₀ K h off count t u)
    (fun t ht u hu _ => WP.mono (hat_step hp hK hh hspan ht hu) fun u' ⟨hu', hz⟩ => ⟨hu', ?_, by rw [hz, hu.rcx]⟩)
    (fun _ h => h) hI hI.rcx
  rw [hu'.rcx, hu.rcx, ofNat64_pred (by omega) (by omega)]; rfl


/-- Before a bounded segment of one seed's buffer. -/
structure HPre (σ : State) (K h off count : Nat) (s : State) : Prop where
  env : EnvK σ s
  out : ∀ p < 3 * (off + count), s.mem (at' σ (oBuf + 504 * K + p)) = xofByte (B σ K) (504 * h + p)
  j : s.mem.readW (at' σ (oJ + 8 * K)) 64 = BitVec.ofNat 64 (Lt σ K (168 * h + off)).length
  stored : Stored s.mem (poly4 (aP σ) K) (Lt σ K (168 * h + off))

theorem setup_ok {K h off count : Nat} (hK : K < 4) (hspan : off + count ≤ 168)
    {s : State} (hI : HPre σ K h off count s) :
    WP isa (.block (setup K off count)) s (HAt σ s K h off count 0) := by
  have hin : InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oJ + 8 * K)) 8 :=
    in_scr' hp hI.env.rd hI.env.wr (by simp only [oJ]; omega)
  have hsx : BitVec.signExtend 64 (BitVec.ofNat 32 (oBuf + 504 * K + 3 * off)) =
      BitVec.ofNat 64 (oBuf + 504 * K + 3 * off) := sx_ofNat (by simp only [oBuf]; omega)
  have hc : BitVec.setWidth 64 (BitVec.ofNat 32 count) = BitVec.ofNat 64 count := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.rsi, .rbp, .rdi, .rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ (oBuf + 504 * K + 3 * off) ∧ s'.gpr .rbp = poly4 (aP σ) K ∧
      s'.gpr .rdi = BitVec.ofNat 64 (Lt σ K (168 * h + off)).length ∧ s'.gpr .rcx = BitVec.ofNat 64 count)
    (by
      xrun [VG.Impl.MlDsa.X86_64.Sample.Rej5.setup, hI.env.rbx, hI.env.r13, hsx, sxP hK, hin, hI.j, hc]
      rfl)
    rfl) fun s₁ ⟨⟨hm, hsi, hbp, hdi, hcx⟩, k₁⟩ => ?_
  exact ⟨hI.env.keep hm k₁ (by decide), by rw [hsi, at', Offset.add_add]; rfl,
    by rw [hdi, Nat.add_zero], by rw [hcx, Nat.sub_zero], hbp, by rw [hm]; exact hI.out,
    by rw [hm, Nat.add_zero]; exact hI.stored,
    by rw [hm]; exact Frame.refl _ _, k₁.mono (by simp)⟩

theorem parse_ok {K h off count : Nat} (hK : K < 4) (hh : h < 2)
    (hspan : off + count ≤ 168) (hpos : 0 < count) {s : State} (hI : HPre σ K h off count s) :
    WP isa (parse K off count) s (HAt σ s K h off count count) :=
  WP.seq (WP.mono (setup_ok hp hK hspan hI) fun _ h₁ => hloop_ok hp hK hh hspan hpos h₁)


end
end VG.Proof.MlDsa.X86_64.Rej4.Segment
