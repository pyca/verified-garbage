module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SharedCandidate
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Caller
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedKMain
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedContract
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCall
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Code
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `RsaKeyGen.X86_64.SharedCode`, which the modules that import this one used -/

section

/-! # The complete candidate with the callable shared Miller–Rabin round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

private theorem sharedCandEnd_post {s t₃ t : State} (c : KCtx s)
    (hsv : ∀ i < 6, word t₃.mem (arg s 3) (8 * i) = s.gpr (saved.getD i .rax))
    (hz : ∀ i < (s.gpr .rsi).toNat, t₃.mem (s.gpr .rdi + BitVec.ofNat 64 i) = 0)
    (hret : ∀ b < 8, t₃.mem (s.gpr .rsp + BitVec.ofNat 64 b) = s.mem (s.gpr .rsp + BitVec.ofNat 64 b))
    (hsp : t₃.gpr .rsp = s.gpr .rsp)
    (hext : ∀ b < 8, ¬(below (s.gpr .rsp) 128).Contains (s.gpr .rsp + BitVec.ofNat 64 b) 1)
    (h : SharedCandEnd t₃ t (arg s 3) (s.gpr .rsp) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat
      (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat) (candRes s)) :
    gprPreserved s t ∧ candPost s t := by
  have key : ∀ {st u : Nat} {outv : Option Nat}, st < 4 →
      SharedKEnd t₃ t (arg s 3) (s.gpr .rsp) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat st u outv →
      gprPreserved s t ∧ ((t.gpr .rax).setWidth 32).toNat = st ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat = (match outv with
        | some c => Spec.Rsa.i2osp c (s.gpr .rsi).toNat
        | none => List.replicate (s.gpr .rsi).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdx) 1 = [BitVec.ofNat 64 u] := by
    intro st u outv hst hk
    refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, ?_, ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hk.saved 0 (by decide)).trans (hsv 0 (by decide))
      · exact (hk.saved 1 (by decide)).trans (hsv 1 (by decide))
      · exact (hk.keep.gpr (by decide)).trans hsp
      · exact (hk.saved 2 (by decide)).trans (hsv 2 (by decide))
      · exact (hk.saved 3 (by decide)).trans (hsv 3 (by decide))
      · exact (hk.saved 4 (by decide)).trans (hsv 4 (by decide))
      · exact (hk.saved 5 (by decide)).trans (hsv 5 (by decide))
    · obtain ⟨hZx, hnu, hno⟩ := c.hret b (by omega_using [hb])
      rw [hk.frame _ (hext b (by omega_using [hb])) hZx hnu hno, hret b (by omega_using [hb])]
    · rw [hk.rax, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hst]
    · show outBytes t.mem _ _ = _
      have := hk.out
      cases outv
      · rw [this]
        show List.map _ _ = _
        rw [List.map_congr_left fun i hi => hz i (List.mem_range.mp hi)]; simp [List.map_const']
      · exact this
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
        hk.used]
  unfold candPost
  rcases hres : candRes s with _ | ⟨_ | _ | _, rest⟩ <;> rw [hres] at h <;> simp only [SharedCandEnd] at h
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, hw⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw, bytesAt_length]⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw, bytesAt_length]⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw, bytesAt_length]⟩

theorem sharedCode_correct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) (hmx : ctlOk (VG.Impl.RsaKeyGen.X86_64.Candidate.codeWith mm R.run) = true) (s : State)
    (h : sharedCandContract.pre s) : ∃ t s', Exec isa (VG.Impl.RsaKeyGen.X86_64.Candidate.codeWith mm R.run) s t s' ∧ abiPreserved s s' ∧ sharedCandContract.post s s' := by
  have c := kctx_of h.1
  have henv := h.2
  suffices hwp : WP isa (VG.Impl.RsaKeyGen.X86_64.Candidate.codeWith mm R.run) s fun s' => gprPreserved s s' ∧ candPost s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_ctl hmx he hg, hp⟩
  have hext : ∀ b < 8, ¬(below (s.gpr .rsp) 128).Contains (s.gpr .rsp + BitVec.ofNat 64 b) 1 := by
    intro b hb
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := 128) (k := 8) (by decide) _
      (Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb]))
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have hk2 := c.k2
  have hk8 := c.k8
  obtain ⟨w, hw⟩ : ∃ w, (s.gpr .rsi).toNat = 8 * w := ⟨(s.gpr .rsi).toNat / 8, by omega_using [hk8]⟩
  have hhw : ∀ i < 32, InRegions s.wr (off (arg s 3) (8 * i)) 8 := fun i hi => hs.st (by omega_using [hZ, hk1, hi])
  unfold VG.Impl.RsaKeyGen.X86_64.Candidate.codeWith
  simp only [seqs]
  refine WP.seq (WP.mono (kEntry_ok rfl hhw c.ha c.hsep) fun t₁ he => ?_)
  refine WP.assoc (WP.seq (WP.mono (front_ok c he) fun t₃ hf => ?_))
  -- Facts at `t₃`.
  have k13 : Keep [.r11, .rax, .rdi, .rsi, .rcx] s t₃ := (he.keep.trans hf.keep).mono (by decide)
  have hs₃ := hs.congr k13.2.2
  have hdi₃ : t₃.gpr .rdi = arg s 3 := (hf.keep.gpr (by decide)).trans he.rdi
  have hw₃ : ∀ i < 32, word t₃.mem (arg s 3) (8 * i) = word t₁.mem (arg s 3) (8 * i) := fun i hi => hf.word c hi
  have hsv : ∀ i < 6, word t₃.mem (arg s 3) (8 * i) = s.gpr (saved.getD i .rax) := fun i hi =>
    (hw₃ i (by omega_using [hi])).trans (he.saved i hi)
  have hhi : ∀ x, 8 * 32 ≤ ofs (arg s 3) x → (∀ j < (s.gpr .rsi).toNat, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      t₃.mem x = s.mem x := fun x hx hx' => by
    rw [hf.frame x hx', he.frame x (Or.inr (by omega))]
  have hret : ∀ b < 8, t₃.mem (s.gpr .rsp + BitVec.ofNat 64 b) = s.mem (s.gpr .rsp + BitVec.ofNat 64 b) :=
    fun b hb => hhi _ (by have := (c.hret b hb).1; omega_using [hZ, hk1, this]) (c.hret b hb).2.2
  have hsp : t₃.gpr .rsp = s.gpr .rsp := k13.gpr (by decide)
  have ho₃ : OutUp t₃ (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat :=
    c.ou.congr k13.2.2
  have h8 : 8 * 32 ≤ (arg s 4).toNat * 8 := by omega_using [hZ, hk1]
  refine WP.ite (decide ((arg s 2).toNat < (s.gpr .rsi).toNat)) (by simp [eval, hf.cf]) (fun hlt => ?_) (fun hlt => ?_)
  · -- Too few octets.
    simp only [decide_eq_true_eq] at hlt
    refine WP.mono (finNone_ok hs₃ hdi₃ h8 (by rw [hw₃ kUsedP (by decide)]; exact he.usedP) ho₃.upw ho₃.upZ)
      fun t ht => sharedCandEnd_post c hsv hf.zero hret hsp hext ?_
    have hnone : candRes s = none := by
      unfold candRes Spec.RsaKeyGen.candidateOp
      rw [VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega_using [hk1]), ite_f (by rw [bytesAt_length]; omega_using [hlt])]
    rw [hnone]; exact (KEnd.of_fin ho₃ ht).shared
  · -- `kMainWith`.
    simp only [decide_eq_false_iff_not, Nat.not_lt] at hlt
    refine WP.mono (sharedKMain_ok M hmc R (henv.kept k13 (by decide))
      (by simp only [slot, hdrBytes]; omega_arith) (mainCtx_of c he hf hw hlt)) fun t ht => sharedCandEnd_post c hsv hf.zero hret hsp hext ?_
    have hres : candRes s = VG.Proof.RsaKeyGen.afterDraw (64 * w)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat))
        (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat))
        (Spec.RsaKeyGen.candidate (64 * w)
          (Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat).take (8 * w))))
        ((Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat).drop (8 * w)) := by
      unfold candRes Spec.RsaKeyGen.candidateOp
      rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega_using [hk1, hw]), ite_t (by rw [bytesAt_length]; omega_using [hw, hlt]),
        seg_zero, show 8 * (8 * w) = 64 * w by omega_using []]
    rw [hres, ← hw]
    rw [← hw] at ht
    exact ht

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! # Instruction safety of generic RSA candidate callers -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Bignum.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate

private theorem all_seqs (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).allInstrs p = l.all (fun c => c.allInstrs p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.allInstrs, List.all_cons] at ih ⊢; rw [ih]

private theorem all_seqs' (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).all p = l.all (fun c => c.all p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.all, List.all_cons] at ih ⊢; rw [ih]

/-! The lemmas about `Code.allInstrs`, `Code.all` and `ctlC` with the code's types written as `simp` finds
them: it reduces `isa.Instr` in the code before it looks a lemma up, and a lemma stated with `Prog isa`
never matches. -/

private theorem i_seqs (p : Instr → Bool) (l : List (Code Instr Cond)) :
    @Code.allInstrs Instr Cond p (seqs l) = l.all (fun c => @Code.allInstrs Instr Cond p c) := all_seqs p l
private theorem i_ite (p : Instr → Bool) (c : Cond) (a b : Code Instr Cond) :
    @Code.allInstrs Instr Cond p (@Code.ite Instr Cond c a b) = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_loop (p : Instr → Bool) (a : Code Instr Cond) (c : Cond) :
    @Code.allInstrs Instr Cond p (@Code.loop Instr Cond a c) = a.allInstrs p := rfl
private theorem i_empty (p : Instr → Bool) :
    @Code.allInstrs Instr Cond p (@Code.block Instr Cond []) = true := rfl

private theorem a_seqs (p : Instr → Bool) (l : List (Code Instr Cond)) :
    @Code.all Instr Cond p (seqs l) = l.all (fun c => @Code.all Instr Cond p c) := all_seqs' p l
private theorem a_ite (p : Instr → Bool) (c : Cond) (a b : Code Instr Cond) :
    @Code.all Instr Cond p (@Code.ite Instr Cond c a b) = (a.all p && b.all p) := rfl
private theorem a_loop (p : Instr → Bool) (a : Code Instr Cond) (c : Cond) :
    @Code.all Instr Cond p (@Code.loop Instr Cond a c) = a.all p := rfl
private theorem a_empty (p : Instr → Bool) :
    @Code.all Instr Cond p (@Code.block Instr Cond []) = true := rfl

private theorem c_seqs (l : List (Code Instr Cond)) : ctlC (seqs l) = l.all ctlC := ctlC_seqs l
private theorem c_ite (c : Cond) (a b : Code Instr Cond) :
    ctlC (@Code.ite Instr Cond c a b) = (ctlC a && ctlC b) := rfl
private theorem c_loop (a : Code Instr Cond) (c : Cond) : ctlC (@Code.loop Instr Cond a c) = ctlC a := rfl
private theorem c_empty : ctlC (@Code.block Instr Cond []) = true := rfl

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa)
    (hp : (codeWith (fun _ _ _ => .block []) (.block [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) (hb : body.allInstrs p = true) :
    (codeWith mul body).allInstrs p = true := by
  unfold codeWith kMainWith millerRabinWith mrRoundWith montSetup at hp ⊢
  simp only [i_seqs, i_ite, i_loop, List.all_append, List.all_cons, hm, hb, i_empty] at hp ⊢
  exact hp

private theorem template_ctlC (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa)
    (hp : ctlC (codeWith (fun _ _ _ => .block []) (.block [])) = true)
    (hm : ∀ o a b, ctlC (mul o a b) = true) (hb : ctlC body = true) :
    ctlC (codeWith mul body) = true := by
  unfold codeWith kMainWith millerRabinWith mrRoundWith montSetup at hp ⊢
  simp only [c_seqs, c_ite, c_loop, List.all_append, List.all_cons, hm, hb, c_empty] at hp ⊢
  exact hp

private theorem template_all (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa)
    (hp : (codeWith (fun _ _ _ => .block []) (.block [])).all p = true)
    (hm : ∀ o a b, (mul o a b).all p = true) (hb : body.all p = true) :
    (codeWith mul body).all p = true := by
  unfold codeWith kMainWith millerRabinWith mrRoundWith montSetup at hp ⊢
  simp only [a_seqs, a_ite, a_loop, List.all_append, List.all_cons, hm, hb, a_empty] at hp ⊢
  exact hp

private theorem arith_mx (v : RoundImpl) (o a b : Nat) :
    (v.mm o a b).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := v.arithSafe o a b
  rw [← VG.Proof.Bignum.X86_64.allInstrs_inline, v.mmInline, Code.allInstrs_eq]
  rw [Code.allInstrs_eq] at h
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).1

private theorem arith_sp (v : RoundImpl) (o a b : Nat) :
    (v.mm o a b).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have h := v.arithSafe o a b
  rw [← VG.Proof.Bignum.X86_64.allInstrs_inline, v.mmInline, Code.allInstrs_eq]
  rw [Code.allInstrs_eq] at h
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).2

/-- The candidate as emitted: its products call `v.mm`'s function. -/
def sharedCandidateCode (v : RoundImpl) : Prog isa :=
  codeWith v.mm (VG.Impl.MillerRabin.X86_64.Caller.call v.name v.code)

/-- The candidate loads MXCSR only where the round restores it. -/
theorem sharedCandidate_ctlC (v : RoundImpl) : ctlC (sharedCandidateCode v) = true := by
  apply template_ctlC _ _ (by decide +kernel) (fun o a b => ctlC_of_noLoad (arith_mx v o a b))
  unfold VG.Impl.MillerRabin.X86_64.Caller.call
  rw [ctlC_seq, ctlC_seq, ctlC_call, v.ctl,
    show ctlC (Code.block VG.Impl.MillerRabin.X86_64.Caller.save : Prog isa) = true from by decide +kernel,
    show ctlC (Code.block VG.Impl.MillerRabin.X86_64.Caller.restore : Prog isa) = true from by decide +kernel]
  rfl

theorem sharedCandidate_ctl (v : RoundImpl) : ctlOk (sharedCandidateCode v) = true :=
  ctlOk_of_ctlC (sharedCandidate_ctlC v)

theorem sharedCandidate_sp (v : RoundImpl) :
    (sharedCandidateCode v).all (fun i => !isa.writesSp i) = true := by
  apply template_all _ _ _ (by decide +kernel) (arith_sp v)
  have h : v.code.all (fun i => !isa.writesSp i) = true := v.spSafe
  simp only [VG.Impl.MillerRabin.X86_64.Caller.call, Code.all, h]
  decide +kernel

end VG.Proof.RsaKeyGen.X86_64
