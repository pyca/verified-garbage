module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtMainPc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPcContract
public import VerifiedGarbage.Proof.Bignum.PrivPre
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: correctness

`Crt.code` with `pc`, from a state its contract allows, writes `privateCrt`
of its inputs if `pre` holds the key's precomputed values
(`crtPcCode_correct`), against `crtPcContract`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- What `Crt.code` with `pc` uses of its contract's precondition: what
`Crt.code` uses, and `pre` (stack argument 12) of `pre_len` words. -/
theorem crtCtxPc_of {s : State} (h : crtPcContract.pre s) :
    CrtCtx s ∧ PreSrc s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 12) (stackArg s 13).toNat ∧
      (stackArg s 13).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (stackArg s 1).toNat
        (stackArg s 3).toNat := by
  simp only [crtPcContract] at h
  sig_split h
  rename_i hsp hrd hwr dOn dOi dOp dOq dOdp dOdq dOqi dOpr dOs dOa dns dis dps dqs ddps ddqs dqis dprs dsa dRo
    dRn dRi dRp dRq dRdp dRdq dRqi dRpr dRs dRa wO wN wI wP wQ wDp wDq wQi wS wPr hk hol hil hpl1 hpl2 hql1
    hql2 hdpl hqil hdql hsl
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 10) ((stackArg s 11).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 112⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have hpr : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨⟨hk1, hk2, hpl1, hpl2, hql1, hql2, by omega, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 112) (by omega) (by omega))
      rw [← stackArgAddr_add s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega) (by rw [← hil]; exact dis),
    src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    src_of_region (by rw [hrd, ← hdpl]; simp) (by omega) (by rw [← hdpl]; exact ddps),
    src_of_region (by rw [hrd, ← hdql]; simp) (by omega) (by rw [← hdql]; exact ddqs),
    src_of_region (by rw [hrd, ← hqil]; simp) (by omega) (by rw [← hqil]; exact dqis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self, contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩,
    ⟨⟨_, hargs, by rw [stackArgAddr_eq s 12]; exact Offset.contains_base _ (by omega) (by omega)⟩,
      fun b hb => by
        have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * 12 + b) (len := 112) (by omega) (by omega))
        rwa [← stackArgAddr_add s 12 b] at this,
      rfl, fun i hi => ⟨_, hpr, Offset.contains_base _ (by omega) (by omega)⟩,
      fun i hi b hb => by
        have := out_scr dprs (contains_byte (stackArg s 12) (i := 8 * i + b) (len := (stackArg s 13).toNat * 8)
          (by omega) (by omega))
        rwa [show stackArg s 12 + BitVec.ofNat 64 (8 * i + b) = off (stackArg s 12) (8 * i) + BitVec.ofNat 64 b by
          rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]] at this⟩, h⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ (by omega) (by omega))⟩

/-- What `Crt.code` with `pc` leaves, from what `fail` or `main` leaves (the
result only if `ok`, which `pre` holding its values gives). -/
theorem crtPcCode_fin {s t₁ t₂ t : State} (c : CrtCtx s) (h : CrtHeadPost s t₁) (hm : t₂.mem = t₁.mem)
    (k : Keep [.rax, .rbp, .rsi] t₁ t₂) {r : Nat} {cb : Bool} {ok : Prop}
    (hp : CrtPost t₂ t (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) r cb ok)
    (hok : Spec.Rsa.privatePreOk s.mem (s.gpr .rdx) (s.gpr .rcx).toNat (stackArg s 0) (stackArg s 1).toNat
      (stackArg s 2) (stackArg s 3).toNat (stackArg s 12) (stackArg s 13).toNat → ok)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true →
      (cb = true ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .rcx).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) *
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)) ∧
      r = if cb then crtResult (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .rcx).toNat)) else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false → cb = false ∧ r = 0) :
    gprPreserved s t ∧ crtPcContract.post s t := by
  refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩,
    fun hpo => crtWritten_of (bytesAt_length _ _ _) (hp.bytes (hok hpo)) hp.rax hc hf⟩
  · have kk := h.keep.trans k
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.saved 0 (by decide)).trans (by rw [hm]; exact h.saved 0 (by decide))
    · exact (hp.saved 1 (by decide)).trans (by rw [hm]; exact h.saved 1 (by decide))
    · exact (hp.keep.gpr (by decide)).trans (kk.gpr (by decide))
    · exact (hp.saved 2 (by decide)).trans (by rw [hm]; exact h.saved 2 (by decide))
    · exact (hp.saved 3 (by decide)).trans (by rw [hm]; exact h.saved 3 (by decide))
    · exact (hp.saved 4 (by decide)).trans (by rw [hm]; exact h.saved 4 (by decide))
    · exact (hp.saved 5 (by decide)).trans (by rw [hm]; exact h.saved 5 (by decide))
  · obtain ⟨hZx, hne⟩ := c.hret b hb
    rw [hp.frame _ hZx hne, hm, h.inScr _ hZx]

/-- `pre` holding the key's precomputed values gives them in memory, at any
state with the same memory outside the working space. -/
theorem preVals_of {s : State} {m : Mem}
    (hpre : PreSrc s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 12) (stackArg s 13).toNat)
    (hW : (stackArg s 13).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (stackArg s 1).toNat
      (stackArg s 3).toNat)
    (hi : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem m)
    (hpo : Spec.Rsa.privatePreOk s.mem (s.gpr .rdx) (s.gpr .rcx).toNat (stackArg s 0) (stackArg s 1).toNat
      (stackArg s 2) (stackArg s 3).toNat (stackArg s 12) (stackArg s 13).toNat) :
    PreVals m (stackArg s 12) (((s.gpr .rcx).toNat + 7) / 8) (wsWords (stackArg s 1).toNat)
      (wsWords (stackArg s 3).toNat) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)) := by
  have hW' : 2 * (((s.gpr .rcx).toNat + 7) / 8) + wsWords (stackArg s 1).toNat + wsWords (stackArg s 3).toNat ≤
      (stackArg s 13).toNat := by
    rw [hW]; unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.primeWords
      Spec.Rsa.modulusWords wsWords; omega
  obtain ⟨-, -, h1, h2, h3⟩ := privatePre_vals (bytesAt_length _ _ _) (by
    have := hpo; unfold Spec.Rsa.privatePreOk at this; rw [this, hW, bytesAt_length, bytesAt_length]
    unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; rfl)
  rw [bytesAt_length] at h2 h3
  rw [bytesAt_length] at h3
  exact ⟨by rw [hpre.wv_eq hi (by omega)]; exact h1, by rw [hpre.wv_eq hi (by omega)]; exact h2,
    by rw [hpre.wv_eq hi (by omega)]; exact h3⟩

/-- `vg_rsa_private_crt_precomputed` with Montgomery multiplication `M`, given
that its code never loads MXCSR (which the registration file evaluates). -/
theorem crtPcCode_correct (M : Mont) (E : CrtExpL M)
    (hmx : (Crt.code M.mm E.code true).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtPcContract.pre s) :
    ∃ t s', Exec isa (Crt.code M.mm E.code true) s t s' ∧ abiPreserved s s' ∧ crtPcContract.post s s' := by
  obtain ⟨c, hpre, hW⟩ := crtCtxPc_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (Crt.code M.mm E.code true) s fun s' => gprPreserved s s' ∧ crtPcContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold Crt.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (crtHead_ok c) fun t₁ h₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by
    rw [bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have hpre₂ := crtPre_of c h₁ hm₂ k₂
  have i₂ : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t₂.mem := by rw [hm₂]; exact h₁.inScr
  have hp₂ := hpre.congrK i₂ (h₁.keep.trans k₂) (by decide)
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    exact WP.mono (fail_ok hpre₂.scr hpre₂.rdi (by omega)
      (by omega) (by omega) hpre₂.hO hpre₂.hK hpre₂.out hpre₂.outSep)
      fun t hp => crtPcCode_fin (ok := True) c h₁ hm₂ k₂ ⟨fun _ => hp.bytes, hp.rax, hp.saved, hp.frame, hp.keep⟩
        (fun _ => trivial) (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    have hW' : 2 * (((s.gpr .rcx).toNat + 7) / 8) + wsWords (stackArg s 1).toNat + wsWords (stackArg s 3).toNat ≤
        (stackArg s 13).toNat := by
      rw [hW]; unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.primeWords
        Spec.Rsa.modulusWords wsWords; omega
    exact WP.mono (crtMainPc_ok M E hpre₂ hv hp₂ hW') fun t ⟨Mk, hp, hiff⟩ => crtPcCode_fin c h₁ hm₂ k₂ hp
      (preVals_of hpre hW i₂) (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide)

end VG.Proof.Bignum.X86_64
