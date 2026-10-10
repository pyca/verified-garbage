import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
import VerifiedGarbage.Proof.Bignum.X86_64.CrtMain
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract

/-!
# RSA with the CRT on x86-64: correctness

`Crt.code`, from a state its contract allows, writes `privateCrt` of its
inputs (`crtCode_correct`), against `crtContract` (`CrtContract.lean`),
which states the shared contract's precondition on the registers and the
stack.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## The precondition, as `main` uses it -/

theorem stackArgAddr_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [stackArgAddr_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- What `Crt.code` uses of its contract's precondition, for the working
space `B` (stack argument 10) of `Z` bytes, `n`'s length `k` and the
primes' lengths (stack arguments 1 and 3). -/
structure CrtCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .rcx).toNat
  hk2 : (s.gpr .rcx).toNat ≤ 1024
  hpl1 : 1 ≤ (stackArg s 1).toNat
  hpl2 : (stackArg s 1).toNat < (s.gpr .rcx).toNat
  hql1 : 1 ≤ (stackArg s 3).toNat
  hql2 : (stackArg s 3).toNat < (s.gpr .rcx).toNat
  hZ : 128 * (s.gpr .rcx).toNat ≤ (stackArg s 11).toNat * 8
  hs : Scr s (stackArg s 10) ((stackArg s 11).toNat * 8)
  ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 11, ∀ m', Outside (stackArg s 10) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  hnb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  hxb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .rcx).toNat)
  hpb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  hqb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 2)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
  hdpb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 4)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
  hdqb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 6)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
  hqib : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 8)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
  hout : ∀ j < (s.gpr .rcx).toNat, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .rcx).toNat,
    (stackArg s 11).toNat * 8 ≤ ofs (stackArg s 10) (s.gpr .rdi + BitVec.ofNat 64 j)
  hret : ∀ b < 8, (stackArg s 11).toNat * 8 ≤ ofs (stackArg s 10) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ j < (s.gpr .rcx).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j

theorem crtCtx_of {s : State} (h : crtContract.pre s) : CrtCtx s := by
  simp only [crtContract] at h
  sig_split h
  rename_i hsp hrd hwr dOn dOi dOp dOq dOdp dOdq dOqi dOs dOa dns dis dps dqs ddps ddqs dqis dsa dRo
    dRn dRi dRp dRq dRdp dRdq dRqi dRs dRa wO wN wI wP wQ wDp wDq wQi wS hk hol hil hpl1 hpl2 hql1
    hql2 hdpl hqil hdql
  have hsl := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 10) ((stackArg s 11).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 96⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hpl1, hpl2, hql1, hql2, by omega, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 96) (by omega) (by omega))
      rw [← stackArgAddr_add s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega) (by rw [← hil]; exact dis),
    src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    src_of_region (by rw [hrd, ← hdpl]; simp) (by omega) (by rw [← hdpl]; exact ddps),
    src_of_region (by rw [hrd, ← hdql]; simp) (by omega) (by rw [← hdql]; exact ddqs),
    src_of_region (by rw [hrd, ← hqil]; simp) (by omega) (by rw [← hqil]; exact dqis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self, contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ (by omega) (by omega))⟩

/-- After `entry` and the reloads of `n` and `k`, from `s`. -/
structure CrtHeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 10) ((stackArg s 11).toNat * 8)
  rdi : t.gpr .rdi = stackArg s 10
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat
  saved : ∀ i < 6, word t.mem (stackArg s 10) (8 * i) = s.gpr (saved.getD i .rax)
  hO : word t.mem (stackArg s 10) (8 * sOut) = s.gpr .rdi
  hN : word t.mem (stackArg s 10) (8 * sN) = s.gpr .rdx
  hK : word t.mem (stackArg s 10) (8 * sK) = BitVec.ofNat 64 (s.gpr .rcx).toNat
  hIn : word t.mem (stackArg s 10) (8 * sIn) = s.gpr .r8
  hP : word t.mem (stackArg s 10) (8 * sP) = stackArg s 0
  hPl : word t.mem (stackArg s 10) (8 * sPlen) = BitVec.ofNat 64 (stackArg s 1).toNat
  hQ : word t.mem (stackArg s 10) (8 * sQ) = stackArg s 2
  hQl : word t.mem (stackArg s 10) (8 * sQlen) = BitVec.ofNat 64 (stackArg s 3).toNat
  hDp : word t.mem (stackArg s 10) (8 * sDp) = stackArg s 4
  hDq : word t.mem (stackArg s 10) (8 * sDq) = stackArg s 6
  hQi : word t.mem (stackArg s 10) (8 * sQinv) = stackArg s 8
  inScr : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t.mem
  keep : Keep [.r11, .rax, .rdi, .rdx, .rcx] s t

/-- `entry`, and `n` and `k` into `rdx` and `rcx`. -/
theorem crtHead_ok {s : State} (c : CrtCtx s) :
    WP isa (.block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr))) s
      (CrtHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 10) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (crtEntry_ok rfl hw c.ha c.hsep) fun t₀ ⟨hdi, hsv, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq,
    hQi, ho₀, k₀⟩ => ?_
  have hs₀ := c.hs.congr k₀.2.2
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.mem = t₀.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs₀.ld (d := 8 * sN) (by unfold sN sFn; omega),
      hs₀.ld (d := 8 * sK) (by unfold sK sFn; omega), hN, hK]) rfl) fun t₁ ⟨⟨hdx, hcx, hm⟩, k₁⟩ => ?_
  rw [← hm] at hsv hO hN hK hI hP hPl hQ hQl hDp hDq hQi
  exact ⟨hs₀.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, hdx, by rw [hcx, ofNat_toNat64], hsv, hO, hN,
    by rw [hK, ofNat_toNat64], hI, hP, by rw [hPl, ofNat_toNat64], hQ, by rw [hQl, ofNat_toNat64], hDp, hDq, hQi,
    by rw [hm]; exact InScr.of_outside ho₀ (by omega), (k₀.trans k₁).mono (by decide)⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem crtPre_of {s t₁ t : State} (c : CrtCtx s) (h : CrtHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.rax, .rbp, .rsi] t₁ t) :
    CrtPre t (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) (s.gpr .rdx)
      (s.gpr .r8) (stackArg s 0) (stackArg s 2) (stackArg s 4) (stackArg s 6) (stackArg s 8)
      (stackArg s 1).toNat (stackArg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat) := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  have hdi : t.gpr .rdi = stackArg s 10 := (k.gpr (by decide)).trans h.rdi
  have hz : offQ (((s.gpr .rcx).toNat + 7) / 8) (stackArg s 1).toNat + slot (wsWords (stackArg s 3).toNat) 8 +
      tabBytes (wsWords (stackArg s 3).toNat) ≤ (stackArg s 11).toNat * 8 := by
    unfold offQ slot wsWords hdrBytes tabBytes; omega
  exact
    { scr := h.scr.congr k.2.2, rdi := hdi, z := hz, zk := hZ, k1 := hk1, k2 := hk2, hO := (by rw [hm]; exact h.hO),
      hN := (by rw [hm]; exact h.hN), hK := (by rw [hm]; exact h.hK), hIn := (by rw [hm]; exact h.hIn),
      hP := (by rw [hm]; exact h.hP), hPl := (by rw [hm]; exact h.hPl), hQ := (by rw [hm]; exact h.hQ),
      hQl := (by rw [hm]; exact h.hQl), hDp := (by rw [hm]; exact h.hDp), hDq := (by rw [hm]; exact h.hDq),
      hQi := (by rw [hm]; exact h.hQi), n := c.hnb.congrK hi kk, x := c.hxb.congrK hi kk,
      p := c.hpb.congrK hi kk, q := c.hqb.congrK hi kk, dp := c.hdpb.congrK hi kk, dq := c.hdqb.congrK hi kk,
      qi := c.hqib.congrK hi kk, nl := bytesAt_length _ _ _, xl := bytesAt_length _ _ _,
      pbl := bytesAt_length _ _ _, qbl := bytesAt_length _ _ _, dpl := bytesAt_length _ _ _,
      dql := bytesAt_length _ _ _, qil := bytesAt_length _ _ _, pl1 := c.hpl1, pl2 := hpl2, ql1 := c.hql1,
      ql2 := hql2, out := (fun j hj => by rw [kk.2.2]; exact c.hout j hj), outSep := c.houts }

/-- What `Crt.code` leaves, from what `fail` or `main` leaves. -/
theorem crtCode_fin {s t₁ t₂ t : State} (c : CrtCtx s) (h : CrtHeadPost s t₁) (hm : t₂.mem = t₁.mem)
    (k : Keep [.rax, .rbp, .rsi] t₁ t₂) {r : Nat} {cb : Bool}
    (hp : MainPost t₂ t (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) r cb)
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
    gprPreserved s t ∧ crtContract.post s t := by
  refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩,
    crtWritten_of (bytesAt_length _ _ _) hp.bytes hp.rax hc hf⟩
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

/-- `vg_rsa_private_crt` with Montgomery multiplication `M`, given that its
code never loads MXCSR (which the registration file evaluates). -/
theorem crtCode_correct (M : Mont) (hmx : (Crt.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtContract.pre s) :
    ∃ t s', Exec isa (Crt.code M.mm) s t s' ∧ abiPreserved s s' ∧ crtContract.post s s' := by
  have c := crtCtx_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (Crt.code M.mm) s fun s' => gprPreserved s s' ∧ crtContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold Crt.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (crtHead_ok c) fun t₁ h₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by
    rw [bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have hpre := crtPre_of c h₁ hm₂ k₂
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    exact WP.mono (fail_ok hpre.scr hpre.rdi (by omega)
      (by omega) (by omega) hpre.hO hpre.hK hpre.out hpre.outSep)
      fun t hp => crtCode_fin c h₁ hm₂ k₂ hp (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    exact WP.mono (crtMain_ok M hpre hv) fun t ⟨Mk, hp, hiff⟩ => crtCode_fin c h₁ hm₂ k₂ hp
      (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide)

end VG.Proof.Bignum.X86_64
