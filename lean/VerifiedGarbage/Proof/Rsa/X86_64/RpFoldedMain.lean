module
import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Proof.Rsa.X86_64.RpIn

public import VerifiedGarbage.Proof.Rsa.X86_64.RpMain
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedRest
import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86_64.RpOut
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Rsa.RecoverFolded

/-! # Functional correctness of the folded recovery computation -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)

open VG.Impl.Rsa.X86_64.Keys.Recover.Folded

theorem rpMain_eq' (mul : Nat → Nat → Nat → Prog isa) :
    Folded.main mul = seqs (prefixList ++ ([.ite .ne fail (Folded.rest mul)] : List (Prog isa))) := by
  simp only [Folded.main, prefixList, List.append_assoc, List.cons_append, List.nil_append]

theorem rpMain_ok [InvLaw] (M : Mont) {I : RpIn} {s : State} (h : RpPre I s)
    (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    WP isa (Folded.main M.mm) s fun t => ∃ res : Option (Nat × Nat),
      (recoverPrimes I.N I.E I.D).1 = res ∧
      (List.range I.k).map (fun i => t.mem (I.pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (fstOr res) I.k ∧
      (List.range I.k).map (fun i => t.mem (I.pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (sndOr res) I.k ∧
      t.gpr .rax = BitVec.ofNat 64 res.isSome.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
      (∀ x, I.Z ≤ ofs I.B x → (∀ i < I.k, x ≠ I.pP + BitVec.ofNat 64 i) →
        (∀ i < I.k, x ≠ I.pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have L := h.L
  have k1 := L.k1
  have k2 := L.k2
  have hel1 := L.el1
  have hel2 := L.el2
  have hdl2 := L.dl2
  have hn := h.scr.nowrap
  have hZ := L.z
  obtain ⟨hNo, hlo⟩ := valid_lo hv
  have hlo' : 2 ^ (64 * (wk I.k - 1)) ≤ I.N := by
    refine Nat.le_trans ?_ hlo
    rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega)
  rw [rpMain_eq']
  refine wp_seqs_append (by simp) (by simp) (WP.mono (rpPrefix_ok h hv) fun s₅ ⟨S₅, hz₅, vM₅, vN₅, hi₅, hDE⟩ => ?_)
  have hspec : (I.D * I.E < 2 ∨ (I.D * I.E - 1) % 2 = 1) ↔ ¬(I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E) := by omega
  simp only [seqs]
  refine WP.ite (!decide (I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E)) (by simp [eval, hz₅]) (fun hb => ?_) (fun hb => ?_)
  · -- Zeros.
    have hb' : ¬(I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E) := by simp at hb; omega
    have hnone := VG.Proof.Rsa.recoverPrimes_none (n := I.N) (hspec.mpr hb')
    refine WP.mono (rpFail_ok S₅.ws.scr S₅.ws.rdi (by omega) S₅.args (by omega) (by omega)
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oP.wr i hi, h.oP.sep⟩
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oQ.wr i hi, h.oQ.sep⟩ h.a)
      fun t ⟨z1, z2, hax, hsv, hfr, hsp⟩ => ⟨none, by rw [hnone], ?_, ?_, by rw [hax]; rfl, hsv,
        fun x hx n1 n2 => by rw [hfr x n1 n2]; exact S₅.inScr x hx, hsp.trans (S₅.rsp.trans h.rsp.symm)⟩
    · rw [List.map_congr_left fun i hi => z1 i (List.mem_range.mp hi)]; rw [fstOr, i2osp_zero']; simp [List.map_const']
    · rw [List.map_congr_left fun i hi => z2 i (List.mem_range.mp hi)]; rw [sndOr, i2osp_zero']; simp [List.map_const']
  · -- `rest`.
    have hb' : I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E := by simpa using hb
    have hgo := VG.Proof.Rsa.recoverPrimes_go (n := I.N) (fun h' => (hspec.mp h') hb')
    refine WP.mono (rpRest_ok M (m := I.D * I.E - 1) (N := I.N) ⟨S₅, L, hNo, hlo', vN₅, hi₅,
      by rw [vM₅]; omega, by omega, by omega, by omega,
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oP.wr i hi, h.oP.sep⟩,
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oQ.wr i hi, h.oQ.sep⟩, h.a⟩)
      fun t ⟨res, cnt, hres, bP, bQ, hax, hsv, hfr, hsp⟩ => ?_
    refine ⟨res.map (pqOf I.N), by rw [hgo, hres], ?_, ?_, by rw [hax]; cases res <;> rfl, hsv, hfr,
      hsp.trans h.rsp.symm⟩
    · rw [bP]; cases res <;> rfl
    · rw [bQ]; cases res <;> rfl

end VG.Proof.Rsa.X86_64.RecoveryFolded
