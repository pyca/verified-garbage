module

public import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedTest
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp
meta import VerifiedGarbage.Impl.Rsa.AArch64.Folded
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedTest
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Bignum.AArch64.FoldedExp
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual

/-! ### `Bignum.AArch64.FoldedFixedCT`, which only this module used -/

section

/-! ### `Bignum.AArch64.FoldedCT`, which only this module used -/

section

/-! ### `Bignum.AArch64.FoldedCTLoop`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum.AArch64

structure PublicData where
  L : Lay
  N : Nat

def Facts (p : PublicData) : Prop :=
  slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2^31 ∧
  Nat.Coprime (2^(64*p.L.w)) p.N

def Inv (p : PublicData) (i : Nat) (s : State) : Prop :=
  ∃ s₀ X x, SquareInv s₀ p.L.B p.L.Z p.L.w p.N X x p.L.minv i s ∧ Facts p

theorem step_ct (M : Mont) :
    RelCT isa (Two fun (q : PublicData × Nat) s => q.2 < 16 ∧ Inv q.1 q.2 s)
      (Folded.squareStep M.mm) (fun _ _ => True) := by
  unfold Folded.squareStep
  refine RelCT.seq (two_post (Ψ := fun (q : PublicData × Nat) t => t.gpr .x0 = q.1.L.B)
    (two_map (fun (q : PublicData × Nat) => q.1.L)
      (fun _ _ ⟨_,_,_,_,h,hf⟩ => ⟨h.ctx.good,hf.1⟩)
      (M.ctL (o := aY) (a := aY) (b := aY) (by unfold MmUse; decide))) ?_)
    (two_taint [.x0] (fun q s t hs ht r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact hs.trans ht.symm) (by taint_decide))
  rintro q s ⟨_,s₀,X,x,h,hf⟩
  exact WP.mono (M.mm_ok h.ctx.good hf.1 hf.2.1 hf.2.2.1 (o := aY) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h.ctx.inv (by rw [h.ctx.n]; exact h.reduced)) fun t ⟨hg,_⟩ => hg.x0

theorem squares_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < 16 ∧ Inv p 0 s)
      (.loop (Folded.squareStep M.mm) (.nonzero .x .x3)) (Two fun p s => Inv p 16 s) := by
  refine two_loop (Φ := Inv) (fun _ => 16) (step_ct M) ?_
  rintro p i s hi ⟨s₀,X,x,h,hf⟩
  exact WP.mono (loopStep_ok M hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hi h)
    fun t ⟨hz,ht⟩ => ⟨eval_count_r hi hz, fun _ => ⟨s₀,X,x,ht,hf⟩,
      fun he => he ▸ ⟨s₀,X,x,ht,hf⟩⟩

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end

@[expose] public section

namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def Pre (p : PublicData) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ Facts p ∧ X < p.N ∧
    X % p.N = x * 2^(64*p.L.w) % p.N

def Ready (p : PublicData) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ Facts p ∧
    wv s.mem p.L.B (slot p.L.w aY) p.L.w < p.N ∧
    wv s.mem p.L.B (slot p.L.w aY) p.L.w % p.N = x * 2^(64*p.L.w) % p.N

theorem start_fw (p : PublicData) (s : State) (h : Pre p s) :
    WP isa Precomputed.start s (Ready p) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := h
  exact WP.mono (start_ok hc hf.1 (by have := hf.2.1; omega_using [this]) hf.2.2.1)
    fun t ⟨ct,yt,_,_,_⟩ => ⟨X,x,ct,hf,by rw [yt]; exact hlt,by rw [yt]; exact hx⟩

theorem init_fw (p : PublicData) (s : State) (h : Ready p s) :
    WP isa (.block [movi .x3 16, sth .x3 sI]) s (Inv p 0) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := h
  have hb : p.L.B.toNat + slot p.L.w 8 ≤ 2^64 := by
    have := hc.good.scr.nowrap; have := hf.1; omega_arith
  refine WP.mono (init_ok hc.good hf.1) fun t ⟨mt,kt⟩ => ?_
  have ct := ExpCtx.store hc hf.1 (i := sI) (by decide) (by decide) mt kt.wr
    ((kt.gpr .x0 (by decide)).trans hc.good.x0)
  have yt : wv t.mem p.L.B (slot p.L.w aY) p.L.w = wv s.mem p.L.B (slot p.L.w aY) p.L.w := by
    rw [mt,hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hb]
  exact ⟨t,X,x,⟨ct,by rw [yt]; exact hlt,by simpa only [yt,Nat.pow_zero,Nat.pow_one] using hx,
    by rw [mt,word_writeW_self]; rfl,Frm.refl _ _ _,Keep.refl _ _⟩,hf⟩

/-- `Y := X` and sixteen squares leak the same in runs with the same public
data. -/
theorem exp65536_ct (M : Mont) :
    RelCT isa (Two Pre) (Folded.exp65536 M.mm) (fun _ _ => True) := by
  unfold Folded.exp65536
  simp only [seqs]
  refine RelCT.seq (two_post (two_map (fun p : PublicData => p.L)
    (fun _ _ ⟨_,_,hc,hf,_⟩ => ⟨hc.good,hf.1⟩) VG.Proof.Bignum.AArch64.start_ct) start_fw) ?_
  refine RelCT.seq (two_piece [.x0]
    (fun p s t ⟨_,_,hs,_⟩ ⟨_,_,ht,_⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst r; rw [hs.good.x0,ht.good.x0])
    (by taint_decide) init_fw) ?_
  exact (two_map id (fun _ _ h => ⟨by decide,h⟩) (squares_ct M)).mono (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum.AArch64

def FinalReady (p : PublicData) (s : State) : Prop :=
  ∃ X, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ Facts p ∧
    wv s.mem p.L.B (slot p.L.w aY) p.L.w < p.N

theorem exp65536_fw (M : Mont) (p : PublicData) (s : State) (h : Pre p s) :
    WP isa (Folded.exp65536 M.mm) s (FinalReady p) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := h
  exact WP.mono (exp65536_ok M hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hlt hx)
    fun t ⟨ct,yt,_⟩ => ⟨X,ct,hf,yt⟩

/-- The final multiplication keeps the second operand canonical even when
an invalid ordinary input will subsequently be masked out. -/
theorem finalAndMark_ct (M : Mont) :
    RelCT isa (Two FinalReady)
      (.seq (M.mm aY aX aY) (.block [movi .x3 2, sth .x3 sStarted])) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun (p : PublicData) t => t.gpr .x0 = p.L.B)
    (two_map (fun p : PublicData => p.L)
      (fun _ _ ⟨_,hc,hf,_⟩ => ⟨hc.good,hf.1⟩)
      (M.ctL (o := aY) (a := aX) (b := aY) (by simp [MmUse]))) ?_)
    (two_taint [.x0] (fun _ _ _ hs ht r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact hs.trans ht.symm) (by taint_decide))
  rintro p s ⟨X,hc,hf,hlt⟩
  exact WP.mono (M.mm_ok hc.good hf.1 hf.2.1 hf.2.2.1 (o := aY) (a := aX) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hc.inv (by rw [hc.n]; exact hlt)) fun t ⟨hg,_⟩ => hg.x0

theorem fixedLoop_ct (M : Mont) :
    RelCT isa (Two Pre) (Folded.fixedLoop M.mm) (fun _ _ => True) := by
  change RelCT isa (Two Pre) (seqs ([Precomputed.start, .block [movi .x3 16, sth .x3 sI],
    .loop (Folded.squareStep M.mm) (.nonzero .x .x3)] ++
    [M.mm aY aX aY, .block [movi .x3 2, sth .x3 sStarted]])) (fun _ _ => True)
  apply RelCT.seqs_append (by simp) (by simp)
  exact RelCT.seq (two_post (exp65536_ct M) (exp65536_fw M)) (finalAndMark_ct M)

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem pExpPre_mem {a : EPub} {s t : State} (h : PExpPre a s)
    {rs : List Reg} (hm : t.mem = s.mem) (hk : Keep rs s t) (h0 : .x0 ∉ rs) :
    PExpPre a t := by
  obtain ⟨X,x,hc,hf,he,hl,hL,hs⟩ := h
  refine ⟨X,x,hc.mem hm hk h0,hf,by rw [hm]; exact he,by rw [hm]; exact hl,hL,?_⟩
  exact ⟨hs.1,hs.2.1,by rw [hk.rd,hk.wr]; exact hs.2.2.1,
    by rw [hm]; exact hs.2.2.2.1,hs.2.2.2.2⟩

theorem pins_exp : Pins PExpPre [.x0] := by
  intro a s t ⟨_,_,hs,_⟩ ⟨_,_,ht,_⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  rw [hs.good.x0,ht.good.x0]

theorem lengthTest_ct : RelCT isa (Two PExpPre) (.block Folded.lengthTest)
    (Two fun a s => PExpPre a s ∧ isa.eval (.zero .x .x3) s = some (decide (a.len=3))) := by
  refine two_piece [.x0] pins_exp (by taint_decide) ?_
  intro a s h
  have orig := h
  obtain ⟨X,x,hc,hf,he,hl,hL,hs⟩ := h
  exact WP.mono (lengthTest_ok hc.good hf.1 hs.2.1 hl) fun t ⟨ht,hm,hk⟩ =>
    ⟨pExpPre_mem orig hm hk (by decide),ht⟩

/-- The byte addresses are derived solely from the public exponent pointer. -/
theorem bytesTest_ct : RelCT isa (Two PExpPre) (.block Folded.bytesTest) (fun _ _ => True) := by
  change RelCT isa (Two PExpPre) (.block ([ldh .x8 sE] ++
    [.ldrb .x3 .x8 0,.subImm .x .x3 .x3 1,.ldrb .x4 .x8 1,
     .logic .orr .x .x3 .x3 .x4,.ldrb .x4 .x8 2,.subImm .x .x4 .x4 1,
     .logic .orr .x .x3 .x3 .x4])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun (a : EPub) t => t.gpr .x8 = a.ep)
    [.x0] pins_exp (by taint_decide) ?_)
    (two_taint [.x8] (fun a s t hs ht r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact hs.trans ht.symm) (by taint_decide))
  rintro a s ⟨_,_,hc,hf,he,_⟩
  have bound : 8*sE+8 ≤ a.L.Z := by
    have := hdr_lt_slot a.L.w 8 (show sE < 32 by decide); have := hf.1; omega_arith
  brun [hc.good.x0,hdr_enc (show sE < 32 by decide),hc.good.scr.ld bound,he]

theorem bytesTest_fw (a : EPub) (s : State) (h : PExpPre a s) (h3 : a.len=3) :
    WP isa (.block Folded.bytesTest) s fun t => PExpPre a t ∧
      isa.eval (.zero .x .x3) t = some (decide (Spec.Rsa.os2ip a.eb=65537)) := by
  have orig := h
  obtain ⟨X,x,hc,hf,he,hl,hL,hs⟩ := h
  have hel : a.eb.length=3 := hs.1.trans h3
  have heb := List.eq_getElem_of_length_eq_three a.eb hel
  refine WP.mono (bytesTest_ok hc.good hf.1 he (a.eb[0]'(by omega_using [hel])) (a.eb[1]'(by omega_using [hel])) (a.eb[2]'(by omega_using [hel])) (by rw [← h3]; exact hs.2.2.1)
    (by simpa only [BitVec.add_zero] using hs.bytes 0 (by omega_using [h3]))
    (hs.bytes 1 (by omega_using [h3])) (hs.bytes 2 (by omega_using [h3]))) fun t ⟨ht,hm,hk⟩ => ?_
  refine ⟨pExpPre_mem orig hm hk (by decide),?_⟩
  simpa only [← heb] using ht

theorem fastLoop_ct (M : Mont) :
    RelCT isa (Two PExpPre) (Folded.fastLoop M.mm) (fun _ _ => True) := by
  unfold Folded.fastLoop
  refine RelCT.seq lengthTest_ct (two_ite (fun _ _ _ hs ht => by rw [hs.2,ht.2]) ?_ ?_)
  · refine RelCT.seq (two_post (Ψ := fun a s => PExpPre a s ∧ isa.eval (.zero .x .x3) s = some (decide (Spec.Rsa.os2ip a.eb=65537))) (two_map id (fun _ _ h => h.1.1) bytesTest_ct) ?_) ?_
    · intro a s h
      have eq := h.2
      rw [h.1.2] at eq
      exact bytesTest_fw a s h.1.1 (by simpa using eq)
    · refine two_ite (fun _ _ _ hs ht => by rw [hs.2,ht.2]) ?_ ?_
      · exact two_map (fun a : EPub => (⟨a.L,a.N⟩ : PublicData))
          (fun _ _ ⟨⟨⟨X,x,hc,hf,_⟩,_⟩,_⟩ =>
            ⟨X,x,hc,⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩,hf.2.2.2.2.1,hf.2.2.2.2.2⟩)
          (fixedLoop_ct M)
      · exact (two_map id (fun _ _ h => h.1.1) (pExpLoop_ct (M := M))).mono
          (fun _ _ h => h) (fun _ _ _ => trivial)
  · exact (two_map id (fun _ _ h => h.1.1) (pExpLoop_ct (M := M))).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.AArch64.FoldedPublic
