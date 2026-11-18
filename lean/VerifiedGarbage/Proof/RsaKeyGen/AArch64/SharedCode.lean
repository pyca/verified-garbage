module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedKMain
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Code
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTTail
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMr
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedMain
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedRound
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedRound
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Code
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Order.Defs.LinearOrder

/-! ### `RsaKeyGen.AArch64.SharedCTFront`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.AArch64.SharedCTCode`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.AArch64.CTCode`, which only this module used -/

section

/-!
# A candidate on AArch64: constant time, the front

For runs that agree on the arguments, `e` and `candidateLeak`: the entry,
the zeros to `out`, the length check and the end for too few octets depend
on the arguments alone, and `kMainWith` on the schedule the leak fixes
(`schedOf_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.RsaKeyGen (Sched schedOf)

/-- A state the contract allows, with the public data `q`. -/
structure CRel (q : FPub) (s : State) : Prop where
  pre : candPre s
  B : stackArg s 1 = q.B
  Z : (stackArg s 2).toNat * 8 = q.Z
  w : (s.gpr .x1).toNat = 8 * q.w
  op : s.gpr .x0 = q.op
  up : s.gpr .x2 = q.up
  eP : s.gpr .x3 = q.eP
  eB : Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat = q.eB
  pP : s.gpr .x5 = q.pP
  pl : (s.gpr .x6).toNat = q.pl
  rP : s.gpr .x7 = q.rP
  rl : (stackArg s 0).toNat = q.rl
  wr : s.wr = q.wr
  sch : 8 * q.w ≤ q.rl → schedOf (8 * q.w) (Spec.Rsa.os2ip q.eB)
    (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))
    (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat) = q.sch

/-- After `kEntry`'s first instruction. -/
def C1 (q : FPub) (t : State) : Prop :=
  ∃ s, CRel q s ∧ t.gpr .x8 = q.B ∧ WP isa (.block (kEntry.drop 1)) t (EntryPost s)

/-- After `kEntry`. -/
def C2 (q : FPub) (t : State) : Prop := ∃ s, CRel q s ∧ EntryPost s t

/-- After the zeros to `out`. -/
def C2' (q : FPub) (t : State) : Prop := ∃ s t₁, CRel q s ∧ EntryPost s t₁ ∧ Zeroed s t₁ t

/-- After the length check. -/
def C3 (q : FPub) (t : State) : Prop := ∃ s, CRel q s ∧ Front s t

theorem C3.x5 {q : FPub} {t : State} (h : C3 q t) :
    t.gpr .x5 = BitVec.ofNat 64 (decide (8 * q.w ≤ q.rl)).toNat := by
  obtain ⟨s, hs, hf⟩ := h
  rw [hf.x5, hs.w, hs.rl]

theorem kEntry_split : kEntry = ([.ldrSp .x8 8] : List Instr) ++ kEntry.drop 1 := rfl

theorem pins_C2 : Pins C2 [.x0] := fun _ _ _ ⟨s₁, c₁, h₁⟩ ⟨s₂, c₂, h₂⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.x0, h₂.x0, c₁.B, c₂.B]

/-- The registers `zeroOut`'s loop needs pinned. -/
def zoVal (ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x1 => ptr
  | .x2 => BitVec.ofNat 64 len
  | _ => 0

/-- `finNone` runs from the front. -/
theorem front_none_any {s t : State} (c : KCtx s) (h : Front s t) : WP isa finNone t fun _ => True := by
  have hZ := c.hZ
  have hk1 := c.k1
  exact WP.mono (finNone_ok (up := s.gpr .x2) (c.hs.congr h.keep.wr) h.x0 (by omega_using [hZ, hk1]) h.args.usedP
    (c.ou.congr h.keep.wr).upw) fun _ _ => trivial

/-- The end for too few octets. -/
theorem finNone_ct {Φ : FPub → State → Prop} (hΦ : ∀ q t, Φ q t → C3 q t) :
    RelCT isa (Two Φ) finNone fun _ _ => True := by
  have e : finNone = .block (([movi .x3 0, ldh .x2 kUsedP] : List Instr) ++ [st .x3 .x2, movi .x0 0]) := rfl
  rw [e]
  refine (RelCT.block_append (pin_ct (Ψ := fun _ _ => True) [.x0] [.x2] (fun q _ => q.up)
    (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨_, c₁, f₁⟩ := hΦ q s₁ h₁
      obtain ⟨_, c₂, f₂⟩ := hΦ q s₂ h₂
      rw [f₁.x0, f₂.x0, c₁.B, c₂.B]) (by taint_decide) ?_ (by taint_decide) ?_)).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · intro q t h
    obtain ⟨s, c, f⟩ := hΦ q t h
    have k := kctx_of c.pre
    have hs := k.hs.congr f.keep.wr
    have hn := hs.nowrap
    have hZ := k.hZ
    have hk1 := k.k1
    have hl : InRegions (t.rd ++ t.wr) (off (stackArg s 1) (8 * kUsedP)) 8 := hs.ld (by simp only [kUsedP, sFn]; omega_using [hZ, hk1])
    refine WP.mono (WP.keep [.x2, .x3] (Q := fun t' => t'.gpr .x2 = q.up) (by
      brun [f.x0, hdr_enc (show kUsedP < 32 by decide), hl, f.args.usedP, c.up]) (by decide) (by decide)
      (by decide +kernel)) fun t' ⟨h2, _⟩ r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact h2
  · intro q t h
    obtain ⟨s, c, f⟩ := hΦ q t h
    have k := kctx_of c.pre
    exact WP.seq_iff.mpr (WP.block_append_iff.mp (WP.mono (front_none_any k f) fun _ _ => trivial))

/-- `kEntry` leaks the same in runs with the same public data. -/
theorem entry_ct : RelCT isa (Two CRel) (.block kEntry) (Two C2) := by
  rw [kEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := C1) [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil)
    (by taint_decide) ?_)
    (two_piece [.x8] (fun q s₁ s₂ ⟨_, _, a₁, _⟩ ⟨_, _, a₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) (by taint_decide)
      fun q t ⟨s, hs, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro q s hs
  have c := kctx_of hs.pre
  have hh : WP isa (.block (([.ldrSp .x8 8] : List Instr) ++ kEntry.drop 1)) s (EntryPost s) := by
    rw [← kEntry_split]; exact entry_ok c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg s 1 := rfl
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := c.ha 1 (by decide)
  have ho : 8 % 8 = 0 ∧ 8 < 32768 := ⟨rfl, by decide⟩
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 1)
    (by brun [exec_ldrSp ho ha1, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, _⟩ =>
      ⟨s, hs, h8.trans hs.B, hw⟩

/-- The zeros to `out`. -/
theorem zeros_ct : RelCT isa (Two C2) (zeroOut kOut kLen) (Two C2') :=
  pin_ct [.x0] [.x1, .x2] (fun q => zoVal q.op (8 * q.w)) pins_C2 (by taint_decide)
    (fun q t ⟨s, c, he⟩ => by
      have k := kctx_of c.pre
      have hs := k.hs.congr he.keep.wr
      have hn := hs.nowrap
      have hZ := k.hZ
      have hk1 := k.k1
      have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (stackArg s 1) (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, hk1, hi])
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = q.op ∧
          t'.gpr .x2 = BitVec.ofNat 64 (8 * q.w)) (by
        brun [he.x0, hdr_enc (show kOut < 32 by decide), hdr_enc (show kLen < 32 by decide), hl kOut (by decide),
          hl kLen (by decide), he.args.out, he.args.len, c.op]
        rw [← c.w, ofNat_toNat64]) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun q t ⟨s, c, he⟩ => WP.mono (zeros_ok (kctx_of c.pre) he) fun t' hz => ⟨s, t, c, he, hz⟩

/-- The length check. -/
theorem lenCheck_ct : RelCT isa (Two C2') (.block ([ldh .x3 kRandLen, ldh .x4 kLen] ++ geFlag)) (Two C3) :=
  two_piece [.x0] (fun q s₁ s₂ ⟨σ₁, _, c₁, e₁, z₁⟩ ⟨σ₂, _, c₂, e₂, z₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [(z₁.keep.gpr .x0 (by decide)).trans e₁.x0, (z₂.keep.gpr .x0 (by decide)).trans e₂.x0, c₁.B, c₂.B])
    (by taint_decide) fun q t ⟨s, t₁, c, he, hz⟩ => WP.mono (lenCheck_ok (kctx_of c.pre) he hz) fun t' hf => ⟨s, c, hf⟩

/-- What `kMainWith` needs, from a state past the length check with enough
octets. -/
theorem C3.k0 {q : FPub} {t : State} (h : C3 q t) (hlt : 8 * q.w ≤ q.rl) : K0 q t := by
  obtain ⟨s, c, hf⟩ := h
  have k := kctx_of c.pre
  have hk1 := k.k1
  have hk2 := k.k2
  have hle : (s.gpr .x1).toNat ≤ (stackArg s 0).toNat := by rw [c.w, c.rl]; exact hlt
  have hm := mainCtx_of k hf c.w hle
  have hw := c.w
  rw [c.eB, c.B, c.Z, c.op, c.up, c.eP, c.pP, c.rP] at hm
  have hsch := c.sch hlt
  rw [c.pP, c.rP] at hsch
  refine ⟨hf.keep.wr.trans c.wr, ⟨by have := hm.z; exact this, by omega_using [hk1, hw], by omega_using [hk2, hw], by rw [← c.rl]; exact (stackArg s 0).isLt,
    hlt, ?_, ?_, ?_⟩, _, _, hm, by rw [bytesAt_length, c.pl], by rw [bytesAt_length, c.rl], hsch⟩
  · rw [← c.eB, bytesAt_length]; exact k.el1
  · rw [← c.eB, bytesAt_length]; exact k.el8
  · rw [← c.pl, ← c.w]; exact k.pl

theorem candPre_wr {s : State} (h : candPre s) :
    s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.gpr .x2, 8⟩, ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩] := h.2.2.1

/-- The public data of a state. -/
def cpubOf (s : State) : FPub :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .x1).toNat / 8, s.wr, s.gpr .x0, s.gpr .x2, s.gpr .x3,
    Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat, s.gpr .x5, (s.gpr .x6).toNat, s.gpr .x7,
    (stackArg s 0).toNat,
    schedOf (8 * ((s.gpr .x1).toNat / 8)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat))
      (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))
      (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat)⟩

theorem crel_self {s : State} (h : candPre s) : CRel (cpubOf s) s := by
  have := (kctx_of h).k8
  exact ⟨h, rfl, rfl, by dsimp only [cpubOf]; omega_using [this], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- Runs that agree on the arguments and the leak agree on the public data. -/
theorem crel_of {s₁ s₂ : State} (h₁ : candPre s₁) (h₂ : candPre s₂) (hp : candPub s₁ s₂) :
    CRel (cpubOf s₁) s₂ := by
  obtain ⟨hr, hsp, ha, hl⟩ := hp
  have r : ∀ x ∈ argRegs, s₂.gpr x = s₁.gpr x := fun x h => (hr x h).symm
  have c := kctx_of h₁
  have hk8 := c.k8
  have hk1 := c.k1
  unfold candLeak at hl
  obtain ⟨he, hl'⟩ := List.append_inj hl (by simp only [List.length_map, bytesAt_length, r .x4 (by decide)])
  have heB := VG.Proof.RsaKeyGen.map_toNat_inj he
  refine ⟨h₂, (ha 1 (by decide)).symm, by rw [← ha 2 (by decide)]; rfl,
    by dsimp only [cpubOf]; rw [r .x1 (by decide)]; omega_using [hk8], r .x0 (by decide), r .x2 (by decide), r .x3 (by decide),
    heB.symm, r .x5 (by decide),
    by rw [r .x6 (by decide)]; rfl, r .x7 (by decide), by rw [← ha 0 (by decide)]; rfl, ?_, fun hk => ?_⟩
  · show s₂.wr = s₁.wr
    rw [candPre_wr h₂, candPre_wr h₁, r .x0 (by decide), r .x1 (by decide), r .x2 (by decide), ha 1 (by decide),
      ha 2 (by decide)]
  · dsimp only [cpubOf] at hk ⊢
    rw [VG.Proof.RsaKeyGen.candidateLeak_eq, VG.Proof.RsaKeyGen.candidateLeak_eq] at hl'
    unfold Spec.RsaKeyGen.candidateOp at hl'
    rw [← heB, r .x1 (by decide)] at hl'
    rw [show 8 * ((s₁.gpr .x1).toNat / 8) = (s₁.gpr .x1).toNat by omega_using [hk8]] at hk ⊢
    refine (VG.Proof.RsaKeyGen.schedOf_eq (by omega_using [hk1]) (by rw [bytesAt_length, bytesAt_length, ha 0 (by decide)])
      (by rw [bytesAt_length]; omega_using [hk]) hl').symm

end VG.Proof.RsaKeyGen.AArch64

end

end

/-! # Constant time of the RSA candidate calling shared Miller–Rabin -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.RsaKeyGen (Sched schedOf)

theorem sharedCode_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) (hK : RelCT isa (Two K0) (kMainWith M.mm R.run) fun _ _ => True) :
    RelCT isa (Two CRel) (codeWith M.mm R.run) fun _ _ => True := by
  unfold codeWith
  simp only [seqs]
  refine RelCT.seq entry_ct (RelCT.seq zeros_ct (RelCT.seq lenCheck_ct ?_))
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.x5, h₂.x5]) ?_ ?_
  · exact finNone_ct fun _ _ h => h.1
  · exact hK.mono (fun _ _ h => two_bind (fun q t₁ t₂ h₁ h₂ => ⟨q, h₁.1.k0 (by
        have := h₁.2; rw [eval_zero, h₁.1.x5] at this; revert this
        cases hd : decide (8 * q.w ≤ q.rl) <;> simp_all), h₂.1.k0 (by
        have := h₂.2; rw [eval_zero, h₂.1.x5] at this; revert this
        cases hd : decide (8 * q.w ≤ q.rl) <;> simp_all)⟩) h) fun _ _ h => h
theorem sharedCode_constantTime (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) (hK : RelCT isa (Two K0) (kMainWith M.mm R.run) fun _ _ => True) :
    ConstantTime isa candPre candPub (codeWith M.mm R.run) :=
  RelCT.constantTime ((sharedCode_ct M R hK).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨cpubOf s₁, crel_self h₁, crel_of h₁ h₂ hp, hp.2.1⟩) fun _ _ h => h)

end VG.Proof.RsaKeyGen.AArch64

end

end

/-! # Constant time of RSA candidate checks with a shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)
open VG.Proof.RsaKeyGen (Sched schedOf)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aY)

theorem sharedKMain_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel)
    (hT : RelCT isa (Two TS) (seqs (montSetup M.mm ++ expSetup ++ millerRabinWith M.mm R.run ++ [mrResult])) fun _ _ => True) :
    RelCT isa (Two K0) (kMainWith M.mm R.run) fun _ _ => True := by
  unfold kMainWith
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [loadC]) (by simp [closeCheck])
    (RelCT.seq (two_post loadC_ct fun _ _ h => loadCStage_ok h) ?_)
  -- Too close to `p`.
  refine RelCT.seqs_append (by simp [closeCheck]) (by simp)
    (RelCT.seq (two_post closeCheck_ct fun _ _ h => closeStage_ok h) ?_)
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (finUsed2_ct fun _ _ h => h.1.1) ?_
  -- Trial division.
  refine RelCT.seqs_append (by simp [trial]) (by simp) (RelCT.seq (two_post (Ψ := fun q t =>
      (KSt q t ∧ (t.gpr .x1 != 0) = q.sch.comp) ∧ q.sch.close = false) (trial_ct fun _ _ h => h.1.1)
    fun q s h => ?_) ?_)
  · have hcl : q.sch.close = false := nonzero_false (by rw [h.1.2]; exact mask_bne _) h.2
    exact WP.mono (trialStage_ok h.1.1 hcl) fun t ht => ⟨ht, hcl⟩
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.1.2, h₂.1.2])
    (finUsed3_ct fun _ _ h => h.1.1.1) ?_
  -- `gcd(c − 1, e)`.
  refine RelCT.seqs_append (by simp [gcdCheck, loadE]) (by simp) (RelCT.seq (two_post (Ψ := fun q t =>
      (KSt q t ∧ (t.gpr .x3 != 0) = q.sch.gbad) ∧ q.sch.close = false ∧ q.sch.comp = false)
    (gcdCheck_ct fun _ _ h => h.1.1.1) fun q s h => ?_) ?_)
  · have hco : q.sch.comp = false := nonzero_false h.1.1.2 h.2
    exact WP.mono (gcdStage_ok h.1.1.1 h.1.2 hco) fun t ht => ⟨ht, h.1.2, hco⟩
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.1.2, h₂.1.2])
    (finUsed3_ct fun _ _ h => h.1.1.1) ?_
  -- Montgomery setup and Miller–Rabin.
  exact hT.mono (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1, h.1.2.2, nonzero_false h.1.1.2 h.2⟩) h)
    fun _ _ h => h

end VG.Proof.RsaKeyGen.AArch64

end

end

/-! ### `RsaKeyGen.AArch64.SharedCTTail`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.AArch64.SharedCTMain`, which only this module used -/

section

/-! ### `RsaKeyGen.AArch64.SharedCTRound`, which only this module used -/

section

/-! # Constant time of RSA's round with a shared prepared kernel -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MillerRabin.AArch64 (Kernel)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)

private def RoundReady (p : RP) :=
  VG.Proof.MillerRabin.AArch64.Caller.Before ⟨p.L.B, p.L.Z, p.L.w⟩

private theorem prefix_ct (M : Mont) : RelCT isa (Two R0)
    (seqs (mrWitness ++ ([M.mm aXm aX aR2, copyA aB aXm] : List (Prog isa)))) (Two RoundReady) := by
  refine two_post (ct_app' (by simp [mrWitness]) (by simp)
    witP1_ct (by
      simpa only [seqs] using (RelCT.seq (preMul_ct M) copyB_ct).mono
        (fun _ _ h => h) (fun _ _ _ => True.intro))) ?_
  rintro p s ⟨h4, h128, hEZ, c, bm, r, i, uni, ch, hc, he, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, -⟩
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_arith) hsh
  have hn := hc.ws.scr.nowrap
  refine WP.mono (sharedWitness_ok M h4 h128 hc hR2 hsh.1 hc1 hb hR hU hK hsrc hlen) ?_
  rintro t ⟨hct, hx, _, _, _, hf, _⟩
  refine ⟨h4, h128, hEZ, c, _, (wtOf c p.L.w p.u r).1, hct,
    he.of_frm hf (fun r hr => Or.inr ?_) (by omega_arith), hsh.1, by have := hsh.1; omega_arith, ?_⟩
  · apply roundRanges_lt p.L.w r
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))
  · simpa only [wtOf, Nat.mod_mul_mod] using hx

private theorem mid_ct (M : Mont) (R : Kernel) : RelCT isa (Two R0)
    (seqs ((mrWitness ++ ([M.mm aXm aX aR2, copyA aB aXm] : List (Prog isa))) ++ R.run)) (Two Rmid) := by
  refine two_post (ct_app' (by simp [mrWitness]) R.nonempty (prefix_ct M)
    (two_map (fun p : RP => (⟨p.L.B, p.L.Z, p.L.w⟩ : VG.Proof.Bignum.AArch64.Ws))
      (fun _ _ h => h) R.ct)) ?_
  rintro p s ⟨h4, h128, hEZ, c, bm, r, i, uni, ch, hc, he, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, hI, hN, hC, _, _, _, hp⟩
  exact WP.mono (sharedMid_ok M R h4 h128 hEZ hc he hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC)
    fun t ⟨⟨_, hct⟩, _, hf, _⟩ => ⟨hct.ws, by rw [hf, hp]⟩

theorem sharedRound_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two R0) (seqs (mrRoundWith M.mm R.run)) fun _ _ => True := by
  simp only [mrRoundWith]
  exact ct_app' (by simp [mrWitness]) (by simp) (mid_ct M R) roundTail_ct

end VG.Proof.RsaKeyGen.AArch64

end

end

/-! # Constant time of RSA witness policy with a shared prepared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)
open VG.Proof.RsaKeyGen (shapeOf itersOf passS checksW)

/-- At the head of iteration `j`. -/
def SharedLoopI (q : FPub) (j : Nat) (s : State) : Prop :=
  4 ≤ q.w ∧ q.w ≤ 128 ∧ slot q.w aE + 8 * (q.w + 2) ≤ q.Z ∧ q.rl < 2 ^ 64 ∧ ∃ (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte))
    (uni : Nat), SharedMrSt q.B q.Z q.w c (checksW q.w) q.rP r s₀ res (j + 1) uni (uOf q j) s ∧ shapeOf res = q.sch.mr ∧
    r.length = q.rl ∧ 1 < c ∧ VG.Proof.RsaKeyGen.PrimeShape (64 * q.w) c ∧ EndW q s₀ ∧
    itersOf (8 * q.w) q.rl q.sch.mr (uOf q j) = Nq q - j

/-- `SharedMrSt` survives changes to registers Montgomery multiplication may
change, and none to memory. -/
theorem SharedMrSt.congr {B : Addr} {Z w c ch : Nat} {rp : Addr} {r : List Byte} {s₀ : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat} {s t : State} {rs : List Reg}
    (h : SharedMrSt B Z w c ch rp r s₀ res i uni used s) (hm : t.mem = s.mem) (k : Keep rs s t)
    (hrs : ∀ r ∈ rs, r ∈ mmRegs) : SharedMrSt B Z w c ch rp r s₀ res i uni used t := by
  obtain ⟨⟨bm, hc⟩, hE, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨⟨bm, hc.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
    (fun h => by have := hrs _ h; simp [mmRegs] at this) (by simp) (by simp) (by simp) (by simp) (by simp)⟩,
    by rw [hm]; exact hE, by rw [hm]; exact h1, by rw [hm]; exact h2, by rw [hm]; exact h3, by rw [hm]; exact h4, by rw [hm]; exact h5,
    h6.congrK (by rw [hm]; exact InScr.refl _ _ _) k, by rw [hm]; exact h7, by rw [hm]; exact h8,
    by rw [hm]; exact h9, h10, h11, h12, h13, h14, by rw [hm]; exact h15, (h16.trans k).mono fun r hr => ?_⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact hr
  · exact hrs r hr

theorem sharedLoopI_ws {q : FPub} {j : Nat} {s : State} (h : SharedLoopI q j s) : Ws s q.B q.Z q.w := by
  obtain ⟨-, -, -, -, c, r, s₀, res, uni, hI, -⟩ := h
  obtain ⟨bm, hc⟩ := hI.ctx
  exact hc.ws

/-- Before the branch on `rand`'s length. -/
def SharedAvI (p : FPub × Nat) (s : State) : Prop :=
  SharedLoopI p.1 p.2 s ∧ isa.eval (.zero .x .x5) s = some (decide (p.1.rl < uOf p.1 p.2 + 8 * p.1.w))

theorem sharedAvI_r0 {p : FPub × Nat} {s : State} (h : SharedAvI p s) (hb : isa.eval (.zero .x .x5) s = some false) :
    R0 ⟨p.1.L, p.1.rP, uOf p.1 p.2, passS (8 * p.1.w) p.1.rl p.1.sch.mr (uOf p.1 p.2)⟩ s := by
  obtain ⟨⟨h4, h128, hEZ, hrl, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, -⟩, hcf⟩ := h
  rw [hcf] at hb
  simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at hb
  obtain ⟨bm, hc⟩ := hI.ctx
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [h4]) hsh
  have hiu := hI.iu
  have hul := hI.ul
  have hi : 32 * (p.2 + 1) ≤ 8 * p.1.w * (p.2 + 1) := Nat.mul_le_mul_right _ (by omega_using [h4])
  have hun := hI.unii
  refine ⟨h4, h128, hEZ, c, bm, r, p.2 + 1, uni, checksW p.1.w, hc, hI.ex, hI.r2, hc1, hsh, hI.rand, hI.kused, hI.len, hI.src,
    by rw [hrlen]; exact hb, hI.ki, hI.kuni, hI.chk, by omega_using [hrl, hb, hiu, hi], by omega_using [hrl, hb, hiu, hi, hun], checksW_lt _, ?_⟩
  rw [← hS, ← hI.rest, ← hrlen]
  exact (VG.Proof.RsaKeyGen.mr_pass hI.go hwb (by omega_using [h4]) (by rw [hrlen]; exact hb)).symm

/-- Where the loop ends. -/
def SharedLoopEnd (q : FPub) (s : State) : Prop :=
  4 ≤ q.w ∧ q.w ≤ 128 ∧ ∃ (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte)),
    SharedMrEnd q.B q.Z q.w c r s₀ res s ∧ shapeOf res = q.sch.mr ∧ r.length = q.rl ∧ EndW q s₀

/-- An iteration of the loop. -/
theorem sharedIterB_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) : RelCT isa (Two fun (p : FPub × Nat) s => p.2 < Nq p.1 ∧ SharedLoopI p.1 p.2 s)
    (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (mrRoundWith M.mm R.run)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) fun _ _ => True := by
  have pw : ∀ {Φ : FPub × Nat → State → Prop}, (∀ p s, Φ p s → Ws s p.1.B p.1.Z p.1.w) → Pins Φ [.x0] :=
    fun h => pins_ws' (fun p : FPub × Nat => p.1.B) (fun p : FPub × Nat => p.1.Z) (fun p : FPub × Nat => p.1.w) h
  refine RelCT.seq (two_piece (Ψ := SharedAvI) [.x0] (pw fun _ _ h => sharedLoopI_ws h.2) (by taint_decide) ?_)
    (RelCT.seq (R := Two fun (p : FPub × Nat) t => Ws t p.1.B p.1.Z p.1.w)
      (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
        (two_piece [.x0] (pw fun _ _ h => sharedLoopI_ws h.1.1) (by taint_decide) fun _ _ h => kStat0_ok (sharedLoopI_ws h.1.1))
        (two_post (two_map (fun p : FPub × Nat =>
            (⟨p.1.L, p.1.rP, uOf p.1 p.2, passS (8 * p.1.w) p.1.rl p.1.sch.mr (uOf p.1 p.2)⟩ : RP))
          (fun _ _ h => sharedAvI_r0 h.1 h.2) (sharedRound_ct M R)) ?_))
      (two_taint [.x0] (pw fun _ _ h => h) (by taint_decide)))
  · rintro ⟨q, j⟩ s ⟨hj, h⟩
    have h' := h
    obtain ⟨h4, h128, hEZ, hrl, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, hE, hit⟩ := h'
    obtain ⟨bm, hc⟩ := hI.ctx
    exact WP.mono (iterHead_ok (r := r) hc.ws h128 (by rw [hrlen]; exact hrl) hI.ul hI.len hI.rlen hI.kused)
      fun t ⟨hz, hm, k⟩ => ⟨⟨h4, h128, hEZ, hrl, c, r, s₀, res, uni, hI.congr hm k (by decide), hS, hrlen, hc1,
        hsh, hE, hit⟩, by rw [hz, hrlen]⟩
  · intro p s h
    have hr := sharedAvI_r0 h.1 h.2
    obtain ⟨h4, h128, hEZ, c, bm, r, i, uni, ch, hc, hE, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, hI, hN, hC, hi, huni,
      hch, -⟩ := hr
    exact WP.mono (sharedRound_ok M R h4 h128 hEZ hc hE hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC hi huni hch)
      fun t ⟨⟨_, hc'⟩, _⟩ => hc'.ws

/-- Miller–Rabin's loop leaks the same in runs that agree on the public data. -/
theorem sharedLoop_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) : RelCT isa (Two fun (q : FPub) s => 0 < Nq q ∧ SharedLoopI q 0 s)
    (.loop (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (mrRoundWith M.mm R.run)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) (.zero .x .x3)) (Two SharedLoopEnd) := by
  refine two_loop (Φ := SharedLoopI) Nq (sharedIterB_ct M R) ?_
  rintro q j s hj ⟨h4, h128, hEZ, hrl, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, hE, hit⟩
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [h4]) hsh
  refine WP.mono (sharedIter_ok M R h4 h128 hEZ hc1 hsh (by omega_using [hrl, hrlen]) (checksW_lt _) s hI) fun t ht => ?_
  rcases ht with ⟨he, hend, hnone, hsome⟩ | ⟨he, uni', hI'⟩
  · have h1 : itersOf (8 * q.w) q.rl q.sch.mr (uOf q j) = 1 := by
      rcases hres : res with _ | ⟨b, rest⟩
      · rw [← hS, hres]; exact VG.Proof.RsaKeyGen.iters_end_none (by omega_using [h4]) (by rw [← hrlen]; exact hnone hres)
      · rw [← hS, hres]
        exact VG.Proof.RsaKeyGen.iters_end_some (by omega_using [h4]) (by rw [← hrlen]; exact hsome b rest hres)
    refine ⟨by rw [he]; exact congrArg some (decide_eq_false (by omega_using [hit, h1])).symm, fun h => absurd h (by omega_using [hit, h1]),
      fun _ => ⟨h4, h128, c, r, s₀, res, hend, hS, hrlen, hE⟩⟩
  · have hu' : uOf q (j + 1) = uOf q j + 8 * q.w := by simp only [uOf]; rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    have hc := VG.Proof.RsaKeyGen.iters_cont (L := 8 * q.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
      (m := (Spec.Rsa.splitTwos (c - 1)).2) hI'.go hwb (by omega_using [h4]) (by omega_using []) hI'.ul
    have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c (checksW q.w) (Spec.Rsa.splitTwos (c - 1)).1
        (Spec.Rsa.splitTwos (c - 1)).2) (j + 1 + 1, uni') (List.drop (uOf q j + 8 * q.w) r) = res := hI'.rest
    rw [show uOf q j + 8 * q.w - 8 * q.w = uOf q j by omega_using [], hr', hS, hrlen] at hc
    refine ⟨by rw [he]; exact congrArg some (decide_eq_true (by omega_using [hit, hc])).symm, fun _ => ?_,
      fun h => absurd h (by omega_using [hit, hc])⟩
    rw [← hu'] at hI'
    exact ⟨h4, h128, hEZ, hrl, c, r, s₀, res, uni', hI', hS, hrlen, hc1, hsh, hE, by rw [hu']; omega_using [hit, hc]⟩

/-- `millerRabinWith` leaks the same in runs that agree on the public data. -/
theorem sharedMillerRabin_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) : RelCT isa (Two MrPre) (seqs (millerRabinWith M.mm R.run)) (Two SharedLoopEnd) := by
  unfold millerRabinWith
  refine RelCT.seq (two_piece [.x0] (pins_ws' (fun q : FPub => q.B) (fun q : FPub => q.Z) (fun q : FPub => q.w)
    fun _ _ ⟨_, _, _, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide) ?_) (sharedLoop_ct M R)
  rintro q s ⟨h4, h128, hEZ, hrl, c, bm, r, hc, hEc, hr2, hc1, hsh, hR, hRL, hrlen, hC, hsrc, hU, hu1, hS, hE⟩
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [h4]) hsh
  have hN : 1 ≤ Nq q := by
    have := (VG.Proof.RsaKeyGen.iters_cont (L := 8 * q.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
      (m := (Spec.Rsa.splitTwos (c - 1)).2) (ch := checksW q.w) (i := 1) (uni := 0) (Or.inl (by decide)) hwb
      (by omega_using [h4]) (Nat.le_refl _) hu1).2
    have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c (checksW q.w) (Spec.Rsa.splitTwos (c - 1)).1
        (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (List.drop (8 * q.w) r) = mrRest c (checksW q.w) r 1 0 (8 * q.w) :=
      rfl
    rwa [hr', hS, hrlen] at this
  have hK : word s.mem q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w) := hE.2.2.1
  exact WP.mono (sharedInit_ok hc hEc hEZ hr2 hR hK hRL hC hsrc hU (Nat.le_refl _) hu1) fun t hI =>
    ⟨hN, h4, h128, hEZ, hrl, c, r, s, _, 0, by simpa [uOf] using hI, hS, hrlen, hc1, hsh, hE, by simp [uOf]⟩

end VG.Proof.RsaKeyGen.AArch64

end

end

/-! # Constant time of RSA setup, shared Miller–Rabin, and result -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)
open VG.Proof.RsaKeyGen (shapeOf itersOf passS checksW)

theorem sharedLoopEnd_endq {q : FPub} {s : State} (h : SharedLoopEnd q s) : EndQ q s := by
  obtain ⟨-, -, c, r, s₀, res, ⟨⟨bm, hc⟩, h0, h1, hf, k⟩, hS, -, hO, hU, hK, ho⟩ := h
  have hw : ∀ {i : Nat}, (i = kRand ∨ i = kLen ∨ i = kRandLen ∨ i = kChecks ∨ i = kOut ∨ i = kUsedP) →
      word s.mem q.B (8 * i) = word s₀.mem q.B (8 * i) := fun hi =>
    hf.word_eq (sharedRoundRanges_hdr _ hi) (by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨hc.ws, (hw (by simp)).trans hO, (hw (by simp)).trans hK, (hw (by simp)).trans hU, ho.congr k.wr, ?_⟩
  rw [← hS]
  rcases hres : res with _ | ⟨b, rest⟩
  · exact h0 hres
  · exact (h1 b rest hres).1

theorem sharedTail_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) :
    RelCT isa (Two TS) (seqs (montSetup M.mm ++ expSetup ++ millerRabinWith M.mm R.run ++ [mrResult])) fun _ _ => True := by
  rw [List.append_assoc, List.append_assoc]
  exact ct_app' (by simp [montSetup]) (by simp [expSetup, lowWord])
    (two_post (two_map FPub.L (fun _ _ h => ts_ms0 h) (montSetup_ct M)) fun _ _ h => ms_mrpre M h)
    (ct_app' (by simp [expSetup, lowWord]) (by simp [millerRabinWith]) expSetup_ct (ct_app' (by simp [millerRabinWith]) (by simp)
      ((sharedMillerRabin_ct M R).mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => sharedLoopEnd_endq h) h)
      mrResult_ct))

end VG.Proof.RsaKeyGen.AArch64

end

end

/-! # Correctness of the RSA candidate calling shared Miller–Rabin -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- `vg_rsa_keygen_candidate` ends as the specification says. -/
theorem sharedCode_correct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) (s : State) (h : candContract.pre s) :
    ∃ t s', Exec isa (codeWith M.mm R.run) s t s' ∧ abiPreserved s s' ∧ candContract.post s s' := by
  have c := kctx_of h
  suffices hwp : WP isa (codeWith M.mm R.run) s fun s' => abiPreserved s s' ∧ candPost s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hk1 := c.k1
  have hk8 := c.k8
  obtain ⟨w, hw⟩ : ∃ w, (s.gpr .x1).toNat = 8 * w := ⟨(s.gpr .x1).toNat / 8, by omega_using [hk8]⟩
  unfold codeWith
  simp only [seqs]
  refine WP.seq (WP.mono (entry_ok c) fun t₁ he => ?_)
  refine WP.seq (WP.mono (zeros_ok c he) fun t₂ hz => ?_)
  refine WP.seq (WP.mono (lenCheck_ok c he hz) fun t₄ hf => ?_)
  refine WP.ite (!decide ((s.gpr .x1).toNat ≤ (stackArg s 0).toNat))
    (by rw [eval_zero, hf.x5]; cases decide ((s.gpr .x1).toNat ≤ (stackArg s 0).toNat) <;> rfl)
    (fun hlt => ?_) (fun hlt => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at hlt
    exact front_none c hf hlt
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hlt
    refine WP.mono (sharedKMain_ok M R (mainCtx_of c hf hw hlt)) fun t ht => candEnd_post hf.zero hf.keep ?_
    rw [candRes_main hw (by omega_using [hk1, hw]) hlt, hw]
    exact ht

end VG.Proof.RsaKeyGen.AArch64
