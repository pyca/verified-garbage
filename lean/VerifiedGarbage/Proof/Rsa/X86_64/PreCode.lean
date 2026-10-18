module

public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCode
public import VerifiedGarbage.Proof.Rsa.X86_64.PreEntry
public import VerifiedGarbage.Proof.Rsa.X86_64.PreMain
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract

/-!
# `vg_rsa_private_precompute` on x86-64: correctness

`code`, from a state its contract allows, writes `privatePrecompute` of its
inputs to `pre` and returns 1, or writes zeros and returns 0
(`ppCode_correct`), against `ppContract`, which states the shared contract's
precondition on the registers and the stack.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (sN sK sMask exit invalid)

/-! ## The contract on the registers and the stack -/

/-- The key's precomputed values, from the arguments. -/
def ppOf (s : State) : Option (List (BitVec 64)) :=
  Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- `vg_rsa_private_precompute(pre = rdi, pre_len = rsi, n = rdx,
n_len = rcx, p = r8, p_len = r9, q = [rsp + 8], q_len = [rsp + 16],
scratch = [rsp + 24], scratch_len = [rsp + 32])`. -/
def ppContract : Contract isa where
  pre s :=
    let pre : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let p : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let q : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
      s.rd = [n, p, q, args] ∧ s.wr = [pre, scr] ∧
      pre.Disjoint n ∧ pre.Disjoint p ∧ pre.Disjoint q ∧ pre.Disjoint scr ∧ pre.Disjoint args ∧
      n.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint pre ∧ ret.Disjoint n ∧ ret.Disjoint p ∧ ret.Disjoint q ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .rcx).toNat ∧
      (s.gpr .rsi).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (s.gpr .r9).toNat
        (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    match ppOf s with
    | some ws => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = ws
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
      Spec.Rsa.wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = List.replicate (s.gpr .rsi).toNat 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat

/-! ## The precondition, as the code uses it -/

/-- What `code` uses of its contract's precondition, for the working space
`B` (stack argument 2) of `Z` bytes. -/
structure PpArgs (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  pl1 : 1 ≤ (s.gpr .r9).toNat
  pl2 : (s.gpr .r9).toNat < (s.gpr .rcx).toNat
  ql1 : 1 ≤ (stackArg s 1).toNat
  ql2 : (stackArg s 1).toNat < (s.gpr .rcx).toNat
  hL : (s.gpr .rsi).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (s.gpr .r9).toNat
    (stackArg s 1).toNat
  hZ : 128 * (s.gpr .rcx).toNat ≤ (stackArg s 3).toNat * 8
  hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8)
  ha : ∀ j < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 4, ∀ m', Outside (stackArg s 2) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  nb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  qb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  hpw : ∀ i < (s.gpr .rsi).toNat, InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8
  hps : ∀ i < 8 * (s.gpr .rsi).toNat, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rdi + BitVec.ofNat 64 i)
  hret : ∀ b < 8, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    8 * (s.gpr .rsi).toNat ≤ ofs (s.gpr .rdi) (s.gpr .rsp + BitVec.ofNat 64 b)

theorem ppArgs_of {s : State} (h : ppContract.pre s) : PpArgs s := by
  simp only [ppContract] at h
  obtain ⟨hsp, hrd, hwr, dPn, dPp, dPq, dPs, dPa, dns, dps, dqs, dsa, dRP, dRn, dRp, dRq, dRs, dRa, wP, wN, wP',
    wQ, wS, hk, hpl1, hpl2, hql1, hql2, hL, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have hpre : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  refine ⟨hk1, hk2, hpl1, hpl2, hql1, hql2, hL, by omega, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 32) (by omega) (by omega))
      rw [← stackArgAddr_add' s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    fun i hi => ⟨_, hpre, Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj => out_scr dPs (contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, by have := out_scr dRP hc; omega⟩

/-! ## The results -/

theorem privatePrecompute_valid {nb pb qb : List Byte} {k : Nat} (hnl : nb.length = k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    Spec.Rsa.privatePrecompute nb pb qb = if Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb then
      some (preWs k nb pb qb) else none := by
  simp only [Spec.Rsa.privatePrecompute, publicPrecompute_some hnl hv, preWs]

theorem privatePrecompute_invalid {nb pb qb : List Byte} {k : Nat} (hnl : nb.length = k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = false) : Spec.Rsa.privatePrecompute nb pb qb = none := by
  simp only [Spec.Rsa.privatePrecompute, Spec.Rsa.publicPrecompute, hnl, hv, Bool.false_eq_true, ite_false]

/-- `failZ`: zeros to `pre`, 0 returned, and the saved registers restored. -/
theorem failZ_ok {t : State} {B op : Addr} {Z L : Nat} (hs : Scr t B Z) (hdi : t.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    (hO : Bignum.word t.mem B (8 * sE) = op) (hLw : Bignum.word t.mem B (8 * sElen) = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hL2 : L < 2 ^ 31) (hpw : ∀ i < L, InRegions t.wr (off op (8 * i)) 8)
    (hps : ∀ i < 8 * L, Z ≤ ofs B (op + BitVec.ofNat 64 i)) :
    WP isa Impl.Rsa.X86_64.PrivPre.failZ t fun t' =>
      Spec.Rsa.wordsAt t'.mem op L = List.replicate L 0 ∧ t'.gpr .rax = BitVec.ofNat 64 0 ∧
      (∀ i < 6, t'.gpr (saved.getD i .rax) = Bignum.word t.mem B (8 * i)) ∧
      (∀ x, 8 * L ≤ ofs op x → t'.mem x = t.mem x) ∧ Keep mmRegs t t' := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have hsep : ∀ x, ofs B x < Z → 8 * L ≤ ofs op x := fun x hx => le_ofs_of_sep hps hx
  unfold Impl.Rsa.X86_64.PrivPre.failZ
  refine WP.seq (WP.mono (WP.keep [.rbx, .r12, .rax] (Q := fun u => u.gpr .rbx = op ∧
      u.gpr .r12 = BitVec.ofNat 64 L ∧ u.gpr .rax = 0 ∧ u.mem = t.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sE (by decide), hl sElen (by decide), hO, hLw]) rfl)
    fun u₁ ⟨⟨hbx₁, h12₁, hax₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (D := op) (eD := 0) (by rw [hbx₁]; simp [off]) h12₁ hax₁ hL1 hL2
    (by omega) (fun j hj => by rw [k₁.2.2, Nat.zero_add]; exact hpw j hj)) fun u₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  rw [hm₁] at ho₂
  have hin₂ : ∀ x, ofs B x < Z → u₂.mem x = t.mem x := fun x hx => ho₂ x (Or.inr (by have := hsep x hx; omega))
  have k12 := k₁.trans k₂
  refine WP.mono (failK_ok (hs.congr k12.2.2) ((k12.gpr (by decide)).trans hdi) hZ)
    fun t' ⟨hax, hsv, hm, kk⟩ => ⟨?_, hax, fun i hi => ?_, fun x hx => by rw [hm, ho₂ x (Or.inr (by omega))],
      (k12.trans kk).mono (by decide)⟩
  · rw [hm]
    apply List.ext_getElem
    · simp [Spec.Rsa.wordsAt]
    · intro i h₁ _
      simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range] at h₁
      have := hz₂ i h₁
      simp only [Bignum.word, off, Nat.zero_add] at this
      simp [Spec.Rsa.wordsAt, this]
  · rw [hsv i hi]
    exact Mem.readW_congr fun b hb => hin₂ _ (by rw [ofs_off B (d := 8 * i) (i := b) (by omega)]; omega)

/-- `main`'s hypotheses, after `entry` and the modulus' check, for a valid
modulus: `MainPre` with `d` as `n`, `dP` and `qInv` as `p` and `dQ` as `q`. -/
theorem PpArgs.mainPre {s t₁ t₂ : State} (c : PpArgs s) (h₁ : PpEntryPost s (stackArg s 2) t₁)
    (hm₂ : t₂.mem = t₁.mem) (k₂ : Keep [.rax, .rbp, .rsi] t₁ t₂)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (s.gpr .rcx).toNat = true) :
    MainPre t₂ (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdx) (s.gpr .rdx)
      (s.gpr .r8) (stackArg s 0) (s.gpr .r8) (stackArg s 0) (s.gpr .r8)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Bignum.word t₂.mem (stackArg s 2) (8 * sEv)).toNat := by
  have hZ := c.hZ
  have := c.k1
  have := c.k2
  have := c.pl1
  have := c.pl2
  have := c.ql1
  have := c.ql2
  have in₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₁.mem := InScr.of_outside h₁.out (by omega)
  have kk := h₁.keep.trans k₂
  have in₂ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₂.mem := by rw [hm₂]; exact in₁
  have hs₂ := c.hs.congr kk.2.2
  have hdi₂ : t₂.gpr .rdi = stackArg s 2 := (k₂.gpr (by decide)).trans h₁.rdi
  have src : ∀ {p : Addr} {bs : List Byte}, Src s (stackArg s 2) ((stackArg s 3).toNat * 8) p bs →
      Src t₂ (stackArg s 2) ((stackArg s 3).toNat * 8) p bs := fun h => h.congrK in₂ kk
  exact
    { scr := hs₂
      rdi := hdi₂
      zk := hZ
      k1 := c.k1
      k2 := c.k2
      nl := bytesAt_length _ _ _
      dl1 := by rw [bytesAt_length]; omega
      dl2 := by rw [bytesAt_length]
      pl1 := by rw [bytesAt_length]; omega
      pl2 := by rw [bytesAt_length]; omega
      ql1 := by rw [bytesAt_length]; omega
      ql2 := by rw [bytesAt_length]; omega
      dpl := rfl
      qil := rfl
      dql := rfl
      hK := by rw [hm₂, h₁.hK, ofNat_toNat64]
      hN := by rw [hm₂, h₁.hN]
      hD := by rw [hm₂, h₁.hD]
      hDl := by rw [hm₂, h₁.hDl, bytesAt_length, ofNat_toNat64]
      hP := by rw [hm₂, h₁.hP]
      hPl := by rw [hm₂, h₁.hPl, bytesAt_length, ofNat_toNat64]
      hQ := by rw [hm₂, h₁.hQ]
      hQl := by rw [hm₂, h₁.hQl, bytesAt_length, ofNat_toNat64]
      hDP := by rw [hm₂, h₁.hDP]
      hDQ := by rw [hm₂, h₁.hDQ]
      hQI := by rw [hm₂, h₁.hQI]
      hEv := rfl
      srN := src c.nb
      srD := src c.nb
      srP := src c.pb
      srQ := src c.qb
      srDP := src c.pb
      srDQ := src c.qb
      srQI := src c.pb
      mv := hv }

/-- `vg_rsa_private_precompute`, given that its code never loads MXCSR
(which the registration file evaluates). -/
theorem ppCode_correct (hmx : Impl.Rsa.X86_64.PrivPre.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : ppContract.pre s) :
    ∃ t s', Exec isa Impl.Rsa.X86_64.PrivPre.code s t s' ∧ abiPreserved s s' ∧ ppContract.post s s' := by
  have c := ppArgs_of h
  clear h
  suffices hwp : WP isa Impl.Rsa.X86_64.PrivPre.code s fun s' => gprPreserved s s' ∧ ppContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  have hZ := c.hZ
  have hn := c.hs.nowrap
  have := c.k1
  have := c.k2
  have := c.pl1
  have := c.pl2
  have := c.ql1
  have := c.ql2
  have hL := c.hL
  have hL4 : 4 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat < 2 ^ 31 := by
    rw [hL]; unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.primeWords
      Spec.Rsa.modulusWords; omega
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  unfold Impl.Rsa.X86_64.PrivPre.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (ppEntry_ok rfl hw c.ha c.hsep) fun t₁ h₁ => ?_
  have in₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₁.mem := InScr.of_outside h₁.out (by omega)
  have nb₁ := c.nb.congrK in₁ h₁.keep
  refine WP.mono (invalid_ok (s := t₁) (nb := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (h₁.keep.gpr (by decide)) (by rw [h₁.keep.gpr (by decide), ofNat_toNat64]) c.k1 c.k2 (bytesAt_length _ _ _)
    (fun i hi => nb₁.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => nb₁.val i _))
    fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have kk := h₁.keep.trans k₂
  have in₂ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₂.mem := by rw [hm₂]; exact in₁
  have hs₂ := c.hs.congr kk.2.2
  have hdi₂ : t₂.gpr .rdi = stackArg s 2 := (k₂.gpr (by decide)).trans h₁.rdi
  have rsp₂ : t₂.gpr .rsp = s.gpr .rsp := kk.gpr (by decide)
  have hO₂ : Bignum.word t₂.mem (stackArg s 2) (8 * sE) = s.gpr .rdi := by rw [hm₂]; exact h₁.hE
  have hL₂ : Bignum.word t₂.mem (stackArg s 2) (8 * sElen) = BitVec.ofNat 64 (s.gpr .rsi).toNat := by
    rw [hm₂, h₁.hEl, ofNat_toNat64]
  have hpw₂ : ∀ i < (s.gpr .rsi).toNat, InRegions t₂.wr (off (s.gpr .rdi) (8 * i)) 8 := fun i hi => by
    rw [kk.2.2]; exact c.hpw i hi
  -- What either branch leaves.
  have fin : ∀ t (cb : Bool) (ws : List (BitVec 64)), t.gpr .rax = BitVec.ofNat 64 cb.toNat →
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat = ws →
      (∀ i < 6, t.gpr (saved.getD i .rax) = Bignum.word t₂.mem (stackArg s 2) (8 * i)) →
      t.gpr .rsp = s.gpr .rsp →
      (∀ x, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x → 8 * (s.gpr .rsi).toNat ≤ ofs (s.gpr .rdi) x →
        t.mem x = t₂.mem x) →
      (ppOf s = if cb then some ws else none) → (cb = false → ws = List.replicate (s.gpr .rsi).toNat 0) →
      gprPreserved s t ∧ ppContract.post s t := by
    intro t cb ws hax hws hsv hsp hfr hpc hz
    have hsv' : ∀ i < 6, t.gpr (saved.getD i .rax) = s.gpr (saved.getD i .rax) := fun i hi => by
      rw [hsv i hi, hm₂]; exact h₁.saved i hi
    refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsv' 0 (by decide)
      · exact hsv' 1 (by decide)
      · exact hsp
      · exact hsv' 2 (by decide)
      · exact hsv' 3 (by decide)
      · exact hsv' 4 (by decide)
      · exact hsv' 5 (by decide)
    · obtain ⟨hZx, hPx⟩ := c.hret b hb
      rw [hfr _ hZx hPx, in₂ _ hZx]
    · simp only [ppContract]
      rw [hpc]
      cases cb
      · simp only [Bool.false_eq_true, ite_false]
        exact ⟨by rw [hax]; rfl, by rw [hws, hz rfl]⟩
      · simp only [ite_true]
        exact ⟨by rw [hax]; rfl, hws⟩
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    refine WP.mono (failZ_ok hs₂ hdi₂ (by omega) hO₂ hL₂ (by omega) hL4.2 hpw₂ c.hps)
      fun t ⟨hws, hax, hsv, hfr, kt⟩ => fin t false _ hax hws hsv ((kt.gpr (by decide)).trans rsp₂)
        (fun x _ hx => hfr x hx) ?_ fun _ => rfl
    simp only [ppOf, privatePrecompute_invalid (bytesAt_length _ _ _) hv, Bool.false_eq_true, ite_false]
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    have hmp := c.mainPre h₁ hm₂ k₂ hv
    refine WP.mono (preMain_ok hmp hO₂ hL₂ (by rw [hL, bytesAt_length, bytesAt_length]) hpw₂ c.hps)
      fun t ⟨hws, hax, hsv, hfr, _, _, kt⟩ => fin t _ _ hax hws hsv ((kt.gpr (by decide)).trans rsp₂) hfr ?_ ?_
    · rw [ppOf, privatePrecompute_valid (bytesAt_length _ _ _) hv]
      by_cases hpq : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) *
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) <;> simp [hpq]
    · intro hc
      simp only [decide_eq_false_iff_not] at hc
      simp [hc]

end VG.Proof.Rsa.X86_64.Key
