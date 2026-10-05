import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
import VerifiedGarbage.Proof.RsaOaep.X86_64.Label

/-!
# RSAES-OAEP on x86-64: the label's hash in constant time

`hashLabel G o` is constant time in two runs with the same frame, regions
and label's address and length (`LQ`), whatever the label (`hashLabel_ct`):
the blocks between the calls are checked by the taint analysis, and the
calls' arguments are the same in both runs.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64 (off word Two Pins two_post)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

/-- The label's hash's public data: the frame, the working space, the other
two writable regions, and the label's address and length. -/
structure LQ where
  F : Addr
  S : Addr
  ws : List Region
  lab : Addr
  labLen : Nat

/-- A point of `hashLabel`. -/
structure LW (q : LQ) (t : State) : Prop where
  fv : FrV q.F q.ws t
  L : Lay t q.F q.S
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ LabAt t q.F q.S W q.lab q.labLen

theorem LW.congr {q : LQ} {t t' : State} (h : LW q t) (hsp : t'.gpr .rsp = t.gpr .rsp) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) : LW q t' := by
  obtain ⟨V, W, R, A⟩ := h.rep
  exact ⟨h.fv.congr hsp hwr, h.L.congr hsp hwr (by rw [hm]), V, W, hm ▸ R, A.congr hrd hwr rfl rfl⟩

theorem LW.after {q : LQ} {t t' : State} (h : LW q t) (L' : Lay t' q.F q.S) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t'.mem q.F q.S V W)
    (A : LabAt t q.F q.S W q.lab q.labLen) : LW q t' :=
  ⟨h.fv.congr (L'.rsp.trans h.L.rsp.symm) hwr, L', V, W, R, A.congr hrd hwr rfl rfl⟩

theorem LW.fr {q : LQ} {t : State} (h : LW q t) : FrV q.F q.ws t ∧ ∀ k ∈ ([] : List Nat), word t.mem q.F (8 * k) = 0 :=
  ⟨h.fv, fun _ h => absurd h List.not_mem_nil⟩

variable {G : Stream} (hG : StreamOK G)

include hG in
/-- The label's hash to `scratch + o`, in two runs with the same `LQ`. -/
theorem hashLabel_ct {o : Nat} (ho : o = oDig ∨ o = oLh) : RelCT isa (Two LW) (hashLabel G o) fun _ _ => True := by
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  unfold hashLabel seqs seqs seqs seqs seqs
  refine RelCT.seq (two_pieceF (Ψ := fun q t => LW q t ∧ t.gpr .rdi = off q.S oSt) [] [] LQ.F LQ.ws (fun _ _ => 0)
    (fun q t h => h.fr) nopin (by decide) ⟨_, by taint_decide⟩ fun q t h =>
      WP.mono (scr_ok h.L (d := .rdi) (by decide) (o := oSt) (by decide))
        fun t' ⟨hdi, hm, k⟩ => ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm, hdi⟩) ?_
  refine RelCT.seq (two_post (Ψ := LW) (two_init hG LQ.F LQ.S fun q t h => ⟨h.1.L, h.2⟩) fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.1.rep
    exact WP.mono (init_ok hG h.1.L R h.2) fun t' ⟨L', rd', wr', _, R', _⟩ => h.1.after L' rd' wr' R' A
  refine RelCT.seq (two_pieceF (Ψ := fun q t => LW q t ∧ t.gpr .rdi = off q.S oSt ∧
      t.gpr .rsi = BitVec.ofNat 64 0 ∧ t.gpr .rdx = q.lab ∧ t.gpr .rcx = BitVec.ofNat 64 q.labLen ∧
      t.gpr .r8 = off q.S oW) [] [] LQ.F LQ.ws (fun _ _ => 0)
    (fun q t h => h.fr) nopin (by decide) ⟨_, by taint_decide⟩ fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.rep
    exact WP.mono (labA_ok h.L R A) fun t' ⟨hdi, hsi, hdx, hcx, h8, hm, k⟩ =>
      ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := LW) (two_updExt hG LQ.F LQ.S LQ.lab LQ.labLen (fun _ => BitVec.ofNat 64 0)
    fun q t h => by
      obtain ⟨V, W, R, A⟩ := h.1.rep
      exact ⟨h.1.L, A.len, A.cov, A.dS, A.dK, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.1.rep
    exact WP.mono (updExt_ok hG h.1.L R A.len A.cov A.dS A.dK h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
      fun t' ⟨L', rd', wr', _, R', _⟩ => h.1.after L' rd' wr' R' A
  refine RelCT.seq (two_pieceF (Ψ := fun q t => LW q t ∧ t.gpr .rdi = off q.S oSt ∧
      t.gpr .rsi = BitVec.ofNat 64 q.labLen ∧ t.gpr .rdx = off q.S o ∧ t.gpr .rcx = off q.S oW) [] [] LQ.F LQ.ws
    (fun _ _ => 0) (fun q t h => h.fr) nopin (by decide) (by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.rep
    exact WP.mono (labF_ok h.L R A.hll (o := o) (by rcases ho with rfl | rfl <;> decide))
      fun t' ⟨hdi, hsi, hdx, hcx, hm, k⟩ => ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm, hdi, hsi, hdx, hcx⟩
  exact two_fin hG LQ.F LQ.S (fun _ => o) (fun q => BitVec.ofNat 64 q.labLen)
    fun q t h => ⟨h.1.L, Or.inr hoo, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end VG.Proof.RsaOaep.X86_64
