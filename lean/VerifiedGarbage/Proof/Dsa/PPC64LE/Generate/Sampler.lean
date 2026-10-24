module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Check
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Sample
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Prepare
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Q

/-!
# DSA key generation on PPC64LE: the sampler's data

q's octets `qbOf` (on entry); the sampler's data `seOf` for them, which are
`SE.Ok` and `SE.Q` when `q > 1`; `prepareQ_ok`: the scan of q keeps `Ctx`
and leaves its data in `r27`–`r29` (`Scanned`), from which `SEnv` follows
(`Scanned.env`), with the tape `randOf` (on entry).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (significant qSigOf)

/-- q's octets, on entry. -/
abbrev qbOf (L : GL) (m : Mem) : List Byte := Spec.Rsa.bytesAt m (off L.par L.pl) L.ql

/-- The tape, on entry. -/
abbrev randOf (L : GL) (m : Mem) : List Byte := Spec.Rsa.bytesAt m L.rand L.rl

/-- The sampler's data. -/
def seOf (L : GL) (qb : List Byte) : SE :=
  ⟨L.F, L.rand, L.rl, off (off L.par L.pl) (L.ql - (significant qb).1), L.ql, (significant qb).1,
    maskOf (significant qb).2.toNat, qSigOf qb⟩

theorem bytesAt_drop (m : Mem) (p : Addr) {n d : Nat} (h : d ≤ n) :
    (Spec.Rsa.bytesAt m p n).drop d = Spec.Rsa.bytesAt m (off p d) (n - d) := by
  have := VG.Proof.Dsa.bytesAt_slice m p (offset := d) (len := n - d) (total := n) (by omega)
  rw [← this, List.take_of_length_le]
  simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length]; omega

theorem qs_eq (L : GL) (m : Mem) :
    qSigOf (qbOf L m) = Spec.Rsa.bytesAt m (off (off L.par L.pl) (L.ql - (significant (qbOf L m)).1))
      (significant (qbOf L m)).1 := by
  have hf := Dsa.significant_fits (qbOf L m)
  rw [VG.Proof.Bignum.bytesAt_length] at hf
  rw [qSigOf, VG.Proof.Bignum.bytesAt_length, bytesAt_drop _ _ (by omega),
    show L.ql - (L.ql - (significant (qbOf L m)).1) = (significant (qbOf L m)).1 by omega]

theorem seOf_Q {L : GL} (m : Mem) (hq : 1 < Spec.Dsa.decodeBE (qbOf L m)) : (seOf L (qbOf L m)).Q (qbOf L m) :=
  ⟨VG.Proof.Bignum.bytesAt_length _ _ _, rfl, rfl, rfl, hq⟩

theorem seOf_ok {L : GL} (hL : L.Ok) (m : Mem) (hq : 1 < Spec.Dsa.decodeBE (qbOf L m)) :
    (seOf L (qbOf L m)).Ok := by
  have hQ := seOf_Q m hq
  have hW := hQ.W_pos
  have hf := Dsa.significant_fits (qbOf L m)
  rw [VG.Proof.Bignum.bytesAt_length] at hf
  have hqb := hL.ql
  have hpl := hL.pl
  have hk := hL.nwPar
  have ht : 0 < (significant (qbOf L m)).2.toNat := by
    have hn : (significant (qbOf L m)).2 ≠ 0 := fun h0 => by
      have := (Dsa.significant_nonzero (qbOf L m)).mpr h0
      simp only [seOf] at hW; omega
    exact Nat.pos_of_ne_zero fun h0 => hn (BitVec.eq_of_toNat_eq h0)
  have qoff : (off (off L.par L.pl) (L.ql - (significant (qbOf L m)).1)) =
      off L.par (L.pl + (L.ql - (significant (qbOf L m)).1)) := off_off _ _ _
  have qsub : Region.Sub ⟨off (off L.par L.pl) (L.ql - (significant (qbOf L m)).1), (significant (qbOf L m)).1⟩
      L.parR := by
    rw [qoff]; exact VG.Offset.sub_base _ (by simp only [GL.kl]; omega)
  refine ⟨hqb.2, hW, hf, maskOf_lt (significant (qbOf L m)).2.isLt ht, qSigOf_length _, hL.nwRand, hL.rl, ?_,
    hL.fnw, ?_, ?_⟩
  · simp only [seOf]
    rw [qoff, off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [GL.kl] at hk; omega)]
    simp only [GL.kl] at hk
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · exact (GL.Ok.frame_disj (d := oNonce) (n := 32) hL.dFR (by decide)).symm
  · exact (GL.Ok.frame_disj (d := oNonce) (n := 32) hL.dFK (by decide)).symm.sub_left qsub

/-- After the scan of q. -/
structure Scanned (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r27 : t.gpr .r27 = (seOf L (qbOf L s₀.mem)).qp
  r28 : t.gpr .r28 = BitVec.ofNat 64 (seOf L (qbOf L s₀.mem)).W
  r29 : 1 < Spec.Dsa.decodeBE (qbOf L s₀.mem) → t.gpr .r29 = BitVec.ofNat 64 (seOf L (qbOf L s₀.mem)).M

/-- q's octets as the key holds them in a state of the body. -/
theorem Ctx.qb {L : GL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    Spec.Rsa.bytesAt t.mem (off L.par L.pl) L.ql = qbOf L s₀.mem := by
  have := hL.ql
  rw [← VG.Proof.Dsa.bytesAt_slice t.mem L.par (total := L.kl) (by simp only [GL.kl]; omega), hc.par,
    VG.Proof.Dsa.bytesAt_slice s₀.mem L.par (total := L.kl) (by simp only [GL.kl]; omega)]

theorem prepareQ_ok {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa prepareQ t fun t' => Scanned (glOf s₀) s₀ t' ∧
      (t'.gpr .r0 = 0 ↔ ¬ 1 < Spec.Dsa.decodeBE (qbOf (glOf s₀) s₀.mem)) ∧ t'.mem = t.mem ∧
      Keep (([.r6, .r12] : List Reg) ++ prepRegs) t t' := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  obtain ⟨hrd, -⟩ := regions_eq h
  unfold prepareQ
  refine WP.seq (WP.mono (WP.keep [.r6, .r12] (Q := fun t₁ => t₁.gpr .r12 = off (glOf s₀).par (glOf s₀).pl ∧
    t₁.gpr .r6 = BitVec.ofNat 64 (glOf s₀).ql ∧ t₁.mem = t.mem) (by prun [hc.r19, hc.r20, hc.r21, add0]) (by decide))
    fun t₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  refine WP.mono (prepare_ok a12 a6 (by omega) hq.2 fun i hi => ?_) fun t' ⟨⟨b28, b27, b0, b29, m2⟩, k2⟩ => ?_
  · rw [k1.rd, k1.wr, hc.rd, off_off]
    exact ⟨(glOf s₀).parR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
      VG.Offset.contains_base _ (by simp only [GL.kl]; omega) (by omega)⟩
  have kk := k1.trans k2
  have eqb : Spec.Rsa.bytesAt t₁.mem (off (glOf s₀).par (glOf s₀).pl) (glOf s₀).ql = qbOf (glOf s₀) s₀.mem := by
    rw [m1]; exact hc.qb hL
  rw [eqb] at b28 b27 b0 b29
  have hdis : ∀ r ∈ ctxRegs, r ∉ ([.r6, .r12] ++ prepRegs : List Reg) := by decide
  refine ⟨⟨hc.step hL kk.sp kk.rd kk.wr (fun r hr => kk.gpr r (hdis r hr))
    (by rw [m2, m1]; exact Frame.refl _ _), b27, b28, b29⟩, b0, by rw [m2, m1], kk⟩

/-- The sampler's state, after the scan, for `q > 1`. -/
theorem Scanned.env {s₀ t : State} (h : gkContract.pre s₀) (hs : Scanned (glOf s₀) s₀ t)
    (hq : 1 < Spec.Dsa.decodeBE (qbOf (glOf s₀) s₀.mem)) :
    SEnv (seOf (glOf s₀) (qbOf (glOf s₀) s₀.mem)) (randOf (glOf s₀) s₀.mem) t := by
  have hL := glOf_ok h
  have hE := seOf_ok hL s₀.mem hq
  obtain ⟨hrd, -⟩ := regions_eq h
  have hc := hs.ctx
  have hW := hE.Wq
  have hk := hL.nwPar
  have hpl := hL.pl
  have hql := hL.ql
  refine ⟨hc.sp, hc.r21, hc.r23, hc.r24, hs.r27, hs.r28, hs.r29 hq, scr_nonce hL rfl hc.wr, fun i hi => ?_,
    fun i hi => ?_, hc.rand, ?_⟩
  · rw [hc.rd, hc.wr]
    exact ⟨(glOf s₀).randR, List.mem_append_left _ (by rw [hrd]; simp),
      VG.Offset.contains_base _ (by simp only [seOf] at hi ⊢; omega) (by have := hL.rl; simp only [seOf] at hi; omega)⟩
  · rw [hc.rd, hc.wr]
    simp only [seOf, off_off]
    simp only [seOf] at hW hi
    have ekl : (glOf s₀).kl = 2 * (glOf s₀).pl + (glOf s₀).ql := rfl
    exact ⟨(glOf s₀).parR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
      VG.Offset.contains_base _ (by omega) (by omega)⟩
  · have := qs_eq (glOf s₀) s₀.mem
    simp only [seOf] at this ⊢
    rw [this, off_off]
    simp only [seOf] at hW
    have e1 := VG.Proof.Dsa.bytesAt_slice t.mem (glOf s₀).par (total := (glOf s₀).kl)
      (offset := (glOf s₀).pl + ((glOf s₀).ql - (significant (qbOf (glOf s₀) s₀.mem)).1))
      (len := (significant (qbOf (glOf s₀) s₀.mem)).1) (by simp only [GL.kl]; omega)
    have e2 := VG.Proof.Dsa.bytesAt_slice s₀.mem (glOf s₀).par (total := (glOf s₀).kl)
      (offset := (glOf s₀).pl + ((glOf s₀).ql - (significant (qbOf (glOf s₀) s₀.mem)).1))
      (len := (significant (qbOf (glOf s₀) s₀.mem)).1) (by simp only [GL.kl]; omega)
    rw [hc.par] at e1
    exact e1.symm.trans e2

end VG.Proof.Dsa.PPC64LE.GK
