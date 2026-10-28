module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Public
import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Body
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGeneratorCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT -- shake: keep (pairs with its `public meta import` for `taint_decide`)
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackPart
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Public
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Body
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGeneratorCT
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
public meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorSearch
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Finish
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Saves
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

/-! # The generator stage's timing depends only on its public inputs

Its arguments, the stack pointer, p, q and the h tape determine the stage's
public plan (`publicOf`), and each piece of the stage runs from states that
agree on it: the generation's own timing lemmas cover the search, the gate,
the packing and the domain check. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout VG.Impl.Dsa.AArch64.Generator
open VG.Proof.Dsa.AArch64.Generation (allocState GeneratorSearchStart PackBefore
  ValidateBefore)
open VG.Proof.RsaOaep.AArch64 (Lay Rep)

variable {pLen : Nat}

def Start (hb : Supported pLen) (P : StagePublic) (u : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, publicOf hb A = P ∧ u = allocState 272 s

def Linked (hb : Supported pLen) (P : StagePublic) (u : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, publicOf hb A = P ∧ u = savedState (allocState 272 s)

def Ready (hb : Supported pLen) (P : StagePublic) (u : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, publicOf hb A = P ∧ Entered pLen s u

def Srch (hb : Supported pLen) (P : StagePublic) (t : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, ∃ u, publicOf hb A = P ∧ Searched hb A u t

def PackMem (hb : Supported pLen) (P : StagePublic) (t : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, publicOf hb A = P ∧ Lay t (frameBase s) (hashBase s) ∧
    (∃ V W, Rep t.mem (frameBase s) (hashBase s) V W ∧ W 5 = s.gpr .x0) ∧ Scr t (s.gpr .x0) (usedBytes pLen)

def Pk (hb : Supported pLen) (P : StagePublic) (t : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, ∃ u, publicOf hb A = P ∧ Packed hb A u t

theorem save_ct (hb : Supported pLen) :
    RelCT isa (Two (Start hb)) (.block save) (Two (Linked hb)) :=
  two_piece [.x0] (by
      rintro P u₁ u₂ ⟨s₁, A₁, rfl, rfl⟩ ⟨s₂, A₂, h₂, rfl⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      have := congrArg (fun P => P.plan.core.B) h₂
      exact this.symm)
    (by taint_decide) fun P u ⟨s, A, hP, hu⟩ => by
    subst hu
    exact WP.mono (save_saved hb A) fun t ht => ⟨s, A, hP, ht⟩

theorem entry_ct (hb : Supported pLen) : RelCT isa (Two (Linked hb)) (.block entry) (Two (Ready hb)) :=
  two_piece [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) fun P u ⟨s, A, hP, hu⟩ => by
    subst hu
    exact WP.mono (entry_entered (pLen := pLen) s) fun t ⟨E, _⟩ => ⟨s, A, hP, E⟩

theorem search_ct (M : Mont) (hb : Supported pLen) :
    RelCT isa (Two (Ready hb)) (Impl.Dsa.AArch64.Generation.generatorSearch M.mm pLen) (Two (Srch hb)) :=
  two_post (two_map (fun P => P.plan) (fun P u ⟨s, A, hP, E⟩ => by
      subst hP; exact ⟨⟨_, prepared hb A E⟩, rfl⟩)
    (VG.Proof.Dsa.AArch64.Generation.nativeGenerator_ct M pLen hb))
    fun P u ⟨s, A, hP, E⟩ => WP.mono (search_ok M hb A E) fun t S => ⟨s, A, u, hP, S⟩

/-- Copying a part keeps the frame and the working space. -/
theorem packPart_stage (hb : Supported pLen) {s : State} (A : StageABI pLen s) {t : State}
    {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (frameBase s) (hashBase s)) (R : Rep t.mem (frameBase s) (hashBase s) V W)
    (h5 : W 5 = s.gpr .x0) (scr : Scr t (s.gpr .x0) (usedBytes pLen))
    (src dst len : Nat) (hsrc : src + len ≤ packed) (hdst : packed ≤ dst)
    (hend : dst + len ≤ packed + 800) (hlen : 2 ≤ len ∧ len ≤ 384) :
    WP isa (Impl.Dsa.AArch64.Generation.packPart src dst len) t fun t' =>
      Lay t' (frameBase s) (hashBase s) ∧ Rep t'.mem (frameBase s) (hashBase s) V W ∧
        Scr t' (s.gpr .x0) (usedBytes pLen) := by
  have c1 : packed = 27008 := rfl
  have c6 : domainCheck = 40960 := rfl
  have c12 : usedBytes pLen = domainCheck + 128 * pLen := rfl
  have srcB := used_small hb (d := src) (n := len) (by omega) (by unfold arithmeticBytes; omega)
  have dstB := used_small hb (d := dst) (n := len) (by omega) (by unfold arithmeticBytes; omega)
  let bs := Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) src) len
  have bl : bs.length = len := bytesAt_length _ _ _
  have source : Src t (off (s.gpr .x0) dst) len (off (s.gpr .x0) src) bs := by
    apply VG.Proof.Dsa.AArch64.Generation.arena_source scr (by rw [bl]; exact srcB)
      (by rw [bl]; omega) (by rw [bl])
    rw [bl]; exact A.parts hb srcB dstB (Or.inl (by omega))
  have hashSep : (⟨hashBase s, oRsa⟩ : Region).Disjoint ⟨off (s.gpr .x0) dst, len⟩ := by
    have hh := used_small hb (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
    have c8 : VG.Impl.Dsa.Generation.Layout.hash = 16384 := rfl
    have c9 : oRsa = 8192 := rfl
    exact A.parts hb hh dstB (Or.inl (by omega))
  have call := VG.Proof.Dsa.AArch64.Generation.packPart_ok (src := src) (dst := dst) (bs := bs) L R
    (by omega) (by omega) (by rw [bl]; omega)
  rw [h5] at call
  have run := call source.rd (fun i hi => by
    rw [off_off]; exact scr.region (by rw [bl] at hi; omega) (by decide))
    (fun i hi => by simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using source.val i hi)
    (fun i hi j hj heq => by
      have outside := source.out i hi
      change len ≤ ofs (off (s.gpr .x0) dst) (off (off (s.gpr .x0) src) i) at outside
      rw [heq] at outside
      rw [bl] at hj
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)] at outside
      omega)
    (by rw [bl]; exact A.framePart hb dstB) (by rw [bl]; exact hashSep)
  rw [bl] at run
  exact WP.mono run fun t' ⟨_, Lt, Rt, _, kt⟩ => ⟨Lt, Rt, scr.congr kt.wr⟩

theorem packPart_mem_ct (hb : Supported pLen) (src dst len : Nat) (hsrc : src + len ≤ packed) (hdst : packed ≤ dst)
    (hend : dst + len ≤ packed + 800) (hlen : 2 ≤ len ∧ len ≤ 384)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.packArgs src dst len)) hc).isSome = true) :
    RelCT isa (Two (PackMem hb)) (Impl.Dsa.AArch64.Generation.packPart src dst len) (Two (PackMem hb)) := by
  refine two_post (two_map StagePublic.pack (fun P t ⟨s, A, hP, L, ⟨V, W, R, h5⟩, _⟩ => by
      subst hP; exact ⟨L, V, W, R, h5⟩)
    (VG.Proof.Dsa.AArch64.Generation.packPart_ct src dst len (by unfold packed at *; omega)
      (by unfold packed at *; omega) (by omega) ht)) ?_
  intro P t ⟨s, A, hP, L, ⟨V, W, R, h5⟩, scr⟩
  exact WP.mono (packPart_stage hb A L R h5 scr src dst len hsrc hdst hend hlen)
    fun t' ⟨L', R', scr'⟩ => ⟨s, A, hP, L', ⟨V, W, R', h5⟩, scr'⟩

theorem pack_mem_ct (hb : Supported pLen) :
    RelCT isa (Two (PackMem hb)) (Impl.Dsa.AArch64.Generation.pack pLen (qLen pLen)) fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generation.pack
  simp only [Impl.Bignum.AArch64.seqs]
  have last : ∀ {c : Prog isa}, RelCT isa (Two (PackMem hb)) c (Two (PackMem hb)) →
      RelCT isa (Two (PackMem hb)) c fun _ _ => True := fun h => h.mono (fun _ _ h => h) fun _ _ _ => True.intro
  rcases hb with rfl | rfl | rfl
  all_goals
    exact RelCT.seq (packPart_mem_ct _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide))
      (RelCT.seq (packPart_mem_ct _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide))
        (last (packPart_mem_ct _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide))))

theorem Supported.sizes {pLen : Nat} (hb : Supported pLen) :
    (pLen = 128 ∧ qLen pLen = 20) ∨ (pLen = 256 ∧ qLen pLen = 32) ∨ (pLen = 384 ∧ qLen pLen = 32) := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem finish_ct (M : Mont) (hb : Supported pLen) :
    RelCT isa (Two fun P t => Srch hb P t ∧ P.status = 1)
      (Impl.Dsa.AArch64.Generation.finishDomain M.mm pLen (qLen pLen)) fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generation.finishDomain
  refine RelCT.seq (two_post (Ψ := Pk hb) (two_map (fun P => P) (fun P t ⟨⟨s, A, u, hP, S⟩, _⟩ => by
      obtain ⟨V, W, R, h5, _⟩ := S.rep
      exact ⟨s, A, hP, S.lay, ⟨V, W, R, h5⟩, S.scr⟩) (pack_mem_ct hb))
    fun P t ⟨⟨s, A, u, hP, S⟩, h1⟩ => by
      subst hP
      exact WP.mono (pack_stage_ok hb A S h1) fun t' Pd => ⟨s, A, u, rfl, Pd⟩) ?_
  refine two_map (StagePublic.validate hb) (fun P t ⟨s, A, u, hP, Pd⟩ => ?_)
    (VG.Proof.Dsa.AArch64.Generation.validate_ct M pLen (qLen pLen) hb.sizes)
  subst hP
  obtain ⟨V, W, R, h5⟩ := Pd.rep
  exact ⟨Pd.lay, ⟨V, W, R, h5⟩, Pd.check_scr, Pd.check_src, rfl, rfl⟩

theorem stage_ct (M : Mont) (hb : Supported pLen) :
    RelCT isa (Two (Ready hb)) (Impl.Dsa.AArch64.Generator.stage M.mm pLen) fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generator.stage
  refine RelCT.seq (search_ct M hb) (VG.Proof.Dsa.AArch64.Generation.onSuccess_ct_of StagePublic.status
    (fun P t ⟨s, A, u, hP, S⟩ => ?_) (fun P t t' ⟨s, A, u, hP, S⟩ hm hk => ⟨s, A, u, hP, S.congr hm hk⟩)
    (finish_ct M hb))
  subst hP
  obtain ⟨V, W, R, _, h19⟩ := S.rep
  exact ⟨_, _, V, W, S.lay, R, h19⟩

def Done (hb : Supported pLen) (P : StagePublic) (t : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, ∃ u, publicOf hb A = P ∧ Staged pLen s u t

def Exited (hb : Supported pLen) (P : StagePublic) (t : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, publicOf hb A = P ∧ Lay t (frameBase s) (hashBase s) ∧
    ∃ V W, Rep t.mem (frameBase s) (hashBase s) V W ∧ W 5 = s.gpr .x0

def Based (P : StagePublic) (t : State) : Prop := t.gpr .x9 = P.plan.core.B

theorem staged_ct (M : Mont) (hb : Supported pLen) :
    RelCT isa (Two (Ready hb)) (Impl.Dsa.AArch64.Generator.stage M.mm pLen) (Two (Done hb)) :=
  two_post (stage_ct M hb) fun _ u ⟨s, A, hP, E⟩ => WP.mono (stage_ok M hb A E) fun _ T => ⟨s, A, u, hP, T⟩

theorem exit_ct (hb : Supported pLen) : RelCT isa (Two (Done hb)) (.block exit) (Two (Exited hb)) :=
  two_piece [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) fun P t ⟨s, A, u, hP, T⟩ => by
    obtain ⟨V, W, R, h5, _⟩ := T.rep
    exact WP.mono (exit_ok T.lay R) fun t' ⟨hm, _, k⟩ =>
      ⟨s, A, hP, T.lay.congr k.sp k.wr (by rw [hm]), V, W, hm ▸ R, h5⟩

theorem restore_ct (hb : Supported pLen) : RelCT isa (Two (Exited hb)) (.block restore) fun _ _ => True := by
  have base : RelCT isa (Two (Exited hb)) (.block [.ldrSp .x9 40]) (Two Based) :=
    two_piece [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) fun P t ⟨s, A, hP, L, V, W, R, h5⟩ => by
      subst hP
      have hw : t.mem.readW (t.sp + BitVec.ofNat 64 40) 64 = s.gpr .x0 := by
        rw [L.sp]; exact (R.fr 5 (by decide)).trans h5
      have hl : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 40) 8 := by rw [L.sp]; exact L.ld (d := 40) (by decide)
      brun [State.write, exec_ldrSp (off := 40) (by decide), hw, hl]
      rfl
  unfold restore
  rw [List.append_assoc]
  refine RelCT.block_append (RelCT.seq base ?_)
  exact two_taint [.x9] (fun P t₁ t₂ h₁ h₂ r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact h₁.trans h₂.symm) (by taint_decide)

theorem code_ct (M : Mont) (hb : Supported pLen) :
    ConstantTime isa (contract pLen).pre (contract pLen).pub (code M.mm pLen) := by
  intro s t xs ys u v hs ht hp es et
  have ct : RelCT isa (fun s t => (contract pLen).pre s ∧ (contract pLen).pre t ∧ (contract pLen).pub s t)
      (code M.mm pLen) (fun _ _ => True) := by
    apply RelCT.alloc
    refine RelCT.mono (RelCT.seq (save_ct hb) (RelCT.seq (entry_ct hb) (RelCT.seq (staged_ct M hb)
      (RelCT.seq (exit_ct hb) (restore_ct hb))))) ?_ fun _ _ _ => True.intro
    rintro a b ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩
    have hv := view_of_pub hp
    have A₁ := stageABI_of h₁
    have A₂ := stageABI_of h₂
    refine ⟨publicOf hb A₁, ⟨s₁, A₁, rfl, rfl⟩, ⟨s₂, A₂, (publicOf_eq hb A₁ A₂ hv).symm, rfl⟩, ?_⟩
    simp only [view, View.mk.injEq] at hv
    change s₁.sp - _ = s₂.sp - _
    rw [hv.2.2.2.2.1]
  exact (ct _ _ _ _ _ _ ⟨hs, ht, hp⟩ es et).1

end VG.Proof.Dsa.AArch64.Generator
