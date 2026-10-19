module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Squeeze
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid

/-!
# The main squeezes of a hashing pair leak only public pointers

The taint analysis does not follow `vg_keccak_f1600_x3_sha3`'s frame (its
pointers come back from the stack), so the squeezes are checked in pieces
(`step3_relCT`): the XOR of a block of `ek` and the call's set-up by the taint
analysis, from the pointers in `x19`, `x25` and `x28`; the call by its own
constant-time proof (`RelCT.call`, from `X3.ct`), whose public arguments
are those pointers in both runs; and the rest by the taint analysis again,
from `x19`, `x20`, `x21`, which the call keeps.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr outAddr)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR scrR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR K)
open VG.Proof.MlKem.AArch64.Paired (rateR21 Rate21 Blocks blockAt)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)
open VG.Spec.Sha3 (stateAt bytesAt keccakF)

/-- What the call of `vg_keccak_f1600_x3_sha3` needs of the memory. -/
structure CallLay (p q st : Addr) (s : State) : Prop where
  hq : p + BitVec.ofNat 64 1536 = q
  d01 : (pairR p).Disjoint (stR st)
  d02 : (pairR p).Disjoint (callR q)
  d12 : (stR st).Disjoint (callR q)
  sp : 128 ≤ s.sp.toNat
  f0 : (frame s.sp).Disjoint (pairR p)
  f1 : (frame s.sp).Disjoint (stR st)
  f2 : (frame s.sp).Disjoint (callR q)
  cov : Covers [pairR p, stR st, callR q] s.wr

theorem CallLay.frame {p q st : Addr} {s t : State} (h : CallLay p q st s) (hw : t.wr = s.wr)
    (hsp : t.sp = s.sp) : CallLay p q st t := by
  refine ⟨h.hq, h.d01, h.d02, h.d12, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hw, hsp]
  exacts [h.sp, h.f0, h.f1, h.f2, h.cov]

/-- The call's set-up. -/
def preCode : List Instr :=
  [.addImm .x .x2 .x19 1536, .str .x .x30 .x2 128, .addImm .x .x0 .x19 0, .addImm .x .x1 .x28 0]

theorem x3call_eq : Impl.MlKem.AArch64.Hybrid.x3call =
    .seq (.block preCode) (.seq (.call Impl.Sha3.AArch64.Hybrid.X3.name Impl.Sha3.AArch64.Hybrid.X3.code)
      (.block [.ldr .x .x30 .x19 1664])) := rfl

structure PreX3 (p q st : Addr) (s s₄ : State) : Prop where
  x0 : s₄.gpr .x0 = p
  x1 : s₄.gpr .x1 = st
  x2 : s₄.gpr .x2 = q
  x19 : s₄.gpr .x19 = p
  rd : s₄.rd = s.rd
  wr : s₄.wr = s.wr
  sp : s₄.sp = s.sp

theorem pre_ok {s : State} {p q st : Addr} (hp : s.gpr .x19 = p) (hst : s.gpr .x28 = st)
    (h : CallLay p q st s) : WP isa (.block preCode) s (PreX3 p q st s) := by
  have hslotR : (callR q).Contains (q + BitVec.ofNat 64 128) 8 := Offset.contains_base q (by decide) (by decide)
  have hslot : InRegions s.wr (q + BitVec.ofNat 64 128) 8 := h.cov _ _ ⟨callR q, by simp, hslotR⟩
  unfold preCode
  refine VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₁ o₁ e₁ => ?_
  have h2 : s₁.gpr .x2 = q := by rw [e₁, hp, h.hq]
  refine VG.Proof.Sha3.AArch64.wp_str ⟨by decide, by decide⟩ (by rw [h2]) (by rw [o₁.wr]; exact hslot)
    fun s₂ m₂ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₃ o₃ e₃ =>
      VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₄ o₄ e₄ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o₄.gpr _ (by decide), e₃, BitVec.add_zero, m₂.gpr, o₁.gpr _ (by decide), hp]
  · rw [e₄, BitVec.add_zero, o₃.gpr _ (by decide), m₂.gpr, o₁.gpr _ (by decide), hst]
  · rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), m₂.gpr, h2]
  · rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), m₂.gpr, o₁.gpr _ (by decide), hp]
  · rw [o₄.rd, o₃.rd, m₂.rd, o₁.rd]
  · rw [o₄.wr, o₃.wr, m₂.wr, o₁.wr]
  · rw [o₄.sp, o₃.sp, m₂.sp, o₁.sp]

theorem ent_gpr (s : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  simp only [State.withRegions_gpr]; exact State.callEntry_gpr s h

theorem kpre {s s₄ : State} {p q st : Addr} (h : CallLay p q st s) (h₄ : PreX3 p q st s s₄) :
    K.pre (s₄.callEntry.withRegions [] [pairR p, stR st, scrR q]) := by
  have hscr : Region.Sub (scrR q) (callR q) := Region.sub_prefix (by decide : 128 ≤ 136)
  have e0 := ent_gpr s₄ [] [pairR p, stR st, scrR q] (r := .x0) (by decide)
  have e1 := ent_gpr s₄ [] [pairR p, stR st, scrR q] (r := .x1) (by decide)
  have e2 := ent_gpr s₄ [] [pairR p, stR st, scrR q] (r := .x2) (by decide)
  have esp : (s₄.callEntry.withRegions [] [pairR p, stR st, scrR q]).sp = s.sp := by
    simp only [State.withRegions_sp, State.callEntry_sp, h₄.sp]
  refine ⟨rfl, by simp only [State.withRegions_wr, e0, e1, e2, h₄.x0, h₄.x1, h₄.x2], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, e1, h₄.x0, h₄.x1]; exact h.d01
  · rw [e0, e2, h₄.x0, h₄.x2]; exact h.d02.sub_right hscr
  · rw [e1, e2, h₄.x1, h₄.x2]; exact h.d12.sub_right hscr
  · rw [esp]; exact h.sp
  · rw [esp, e0, h₄.x0]; exact h.f0
  · rw [esp, e1, h₄.x1]; exact h.f1
  · rw [esp, e2, h₄.x2]; exact h.f2.sub_right hscr

theorem call_covers {p q st : Addr} {X : List Region} (hcov : Covers [pairR p, stR st, callR q] X) :
    Covers [pairR p, stR st, scrR q] X :=
  (Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨pairR p, by simp, 0, (BitVec.add_zero p).symm, Nat.le_of_eq (Nat.zero_add _)⟩
    · exact ⟨stR st, by simp, 0, (BitVec.add_zero st).symm, Nat.le_of_eq (Nat.zero_add _)⟩
    · exact ⟨callR q, by simp, 0, (BitVec.add_zero q).symm, by simp only [scrR, callR]; decide⟩).trans hcov

theorem call_keeps {s s₄ : State} {p q st : Addr} (h : CallLay p q st s) (h₄ : PreX3 p q st s s₄) :
    WP isa (.call Impl.Sha3.AArch64.Hybrid.X3.name Impl.Sha3.AArch64.Hybrid.X3.code) s₄ fun t =>
      t.gpr .x19 = s₄.gpr .x19 ∧ t.sp = s₄.sp := by
  have hc := call_covers (X := s₄.wr) (by rw [h₄.wr]; exact h.cov)
  exact WP.callFV (k := K) (rd := []) (wr := [pairR p, stR st, scrR q])
    VG.Proof.Sha3.AArch64.Hybrid.X3.correct (kpre h h₄) (Covers.right hc) hc
    (fun t _ _ hsp _ hk _ _ => ⟨hk .x19 (by decide) (by decide), hsp⟩) (by rw [depth]; decide)

/-- **The call** leaks only its public pointers. -/
theorem x3call_relCT {σ₁ σ₂ : State} {p q st : Addr} (h₁ : CallLay p q st σ₁) (h₂ : CallLay p q st σ₂)
    (p₁ : σ₁.gpr .x19 = p) (p₂ : σ₂.gpr .x19 = p) (s₁ : σ₁.gpr .x28 = st) (s₂ : σ₂.gpr .x28 = st)
    (sp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) Impl.MlKem.AArch64.Hybrid.x3call TT := by
  rw [x3call_eq]
  refine rel_seq (rel_taint [.x19, .x28] sp (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [p₁, p₂]
      · rw [s₁, s₂]) ⟨_, by taint_decide⟩)
    (pre_ok p₁ s₁ h₁) (pre_ok p₂ s₂ h₂) fun v₁ v₂ hv₁ hv₂ => ?_
  refine rel_seq ((RelCT.call (k := K) VG.Proof.Sha3.AArch64.Hybrid.X3.correct
      VG.Proof.Sha3.AArch64.Hybrid.X3.ct [] [pairR p, stR st, scrR q] fun a b ⟨ha, hb⟩ => by
        subst ha hb
        refine ⟨kpre h₁ hv₁, kpre h₂ hv₂, ?_, ?_, ?_, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_⟩
          · rw [ent_gpr _ _ _ (by decide), ent_gpr _ _ _ (by decide), hv₁.x0, hv₂.x0]
          · rw [ent_gpr _ _ _ (by decide), ent_gpr _ _ _ (by decide), hv₁.x1, hv₂.x1]
          · rw [ent_gpr _ _ _ (by decide), ent_gpr _ _ _ (by decide), hv₁.x2, hv₂.x2]
          · simp only [State.withRegions_sp, State.callEntry_sp, hv₁.sp, hv₂.sp, sp]
        · exact Covers.right (call_covers (by rw [hv₁.wr]; exact h₁.cov))
        · exact call_covers (by rw [hv₁.wr]; exact h₁.cov)
        · exact Covers.right (call_covers (by rw [hv₂.wr]; exact h₂.cov))
        · exact call_covers (by rw [hv₂.wr]; exact h₂.cov)).mono (fun _ _ h => h) fun _ _ _ => trivial)
    (call_keeps h₁ hv₁) (call_keeps h₂ hv₂) fun w₁ w₂ hw₁ hw₂ => ?_
  exact rel_taint [.x19] (by rw [hw₁.2, hw₂.2, hv₁.sp, hv₂.sp, sp]) (by
      intro r hr; rw [List.mem_singleton.mp hr, hw₁.1, hw₂.1, hv₁.x19, hv₂.x19]) ⟨_, by taint_decide⟩

theorem StepLay.callLay {S : Impl.MlKem.AArch64.Hybrid.HSrc} {p a b e st : Addr} {s : State}
    (h : StepLay S p a b e st s) : CallLay p (p + 1536) st s :=
  ⟨rfl, h.dPS, h.dPC, h.dSC, h.sp, h.fP, h.fS, h.fC, h.cov⟩

theorem regEq {a b c e : Addr} (h₁ : a + c = e) (h₂ : b + c = e) : a = b := by
  have h := congrArg (· - c) (h₁.trans h₂.symm)
  simpa only [BitVec.add_sub_cancel] using h

/-- **A main squeeze** leaks only its public pointers, if the XOR of its block does. -/
theorem step3_relCT (S : Impl.MlKem.AArch64.Hybrid.HSrc) (hS : SrcOk S) {σ₁ σ₂ : State} {p a b e st : Addr}
    {A₁ B₁ A₂ B₂ : Spec.Sha3.State} {E₁ E₂ : List Byte} {blk : Nat}
    (h19₁ : σ₁.gpr .x19 = p) (h20₁ : σ₁.gpr .x20 = a) (h21₁ : σ₁.gpr .x21 = b)
    (h25₁ : σ₁.gpr S.r + BitVec.ofNat 64 S.base = e) (h28₁ : σ₁.gpr .x28 = st)
    (h19₂ : σ₂.gpr .x19 = p) (h20₂ : σ₂.gpr .x20 = a) (h21₂ : σ₂.gpr .x21 = b)
    (h25₂ : σ₂.gpr S.r + BitVec.ofNat 64 S.base = e) (h28₂ : σ₂.gpr .x28 = st) (sp : σ₁.sp = σ₂.sp)
    (hb : 136 * blk < S.len)
    (hE₁ : bytesAt σ₁.mem e S.len = E₁) (hst₁ : stateAt σ₁.mem st = hstate E₁ blk (dB S))
    (hE₂ : bytesAt σ₂.mem e S.len = E₂) (hst₂ : stateAt σ₂.mem st = hstate E₂ blk (dB S))
    (pair₁ : PairAt σ₁.mem p A₁ B₁) (pair₂ : PairAt σ₂.mem p A₂ B₂)
    (hl₁ : StepLay S p a b e st σ₁) (hl₂ : StepLay S p a b e st σ₂)
    (habs : ∃ h, (taint.check (Taint.ofRegs [S.r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock S blk)) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (Impl.MlKem.AArch64.Hybrid.step3 S blk) TT := by
  unfold Impl.MlKem.AArch64.Hybrid.step3
  refine rel_seq (rel_taint [S.r, .x28] sp (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact regEq h25₁ h25₂
      · rw [h28₁, h28₂]) habs)
    (absorbBlock_ok S hS h25₁ h28₁ hb hE₁ hst₁ hl₁.ek (covers_mono hl₁.cov (by simp)) hl₁.dSE)
    (absorbBlock_ok S hS h25₂ h28₂ hb hE₂ hst₂ hl₂.ek (covers_mono hl₂.cov (by simp)) hl₂.dSE)
    fun u₁ u₂ ⟨ku₁, fu₁, _⟩ ⟨ku₂, fu₂, _⟩ => ?_
  have pu₁ : PairAt u₁.mem p A₁ B₁ :=
    VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pair₁ fu₁ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl₁.dPS)
  have pu₂ : PairAt u₂.mem p A₂ B₂ :=
    VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pair₂ fu₂ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl₂.dPS)
  have c₁ := hl₁.callLay.frame ku₁.wr ku₁.sp
  have c₂ := hl₂.callLay.frame ku₂.wr ku₂.sp
  have u19₁ : u₁.gpr .x19 = p := by rw [ku₁.get .x19, h19₁]
  have u19₂ : u₂.gpr .x19 = p := by rw [ku₂.get .x19, h19₂]
  have u28₁ : u₁.gpr .x28 = st := by rw [ku₁.get .x28, h28₁]
  have u28₂ : u₂.gpr .x28 = st := by rw [ku₂.get .x28, h28₂]
  refine rel_seq (x3call_relCT c₁ c₂ u19₁ u19₂ u28₁ u28₂ (by rw [ku₁.sp, ku₂.sp, sp]))
    (x3call_ok (S := stateAt u₁.mem st) u19₁ c₁.hq u28₁ pu₁ rfl c₁.d01 c₁.d02 c₁.d12 c₁.sp c₁.f0 c₁.f1 c₁.f2 c₁.cov)
    (x3call_ok (S := stateAt u₂.mem st) u19₂ c₂.hq u28₂ pu₂ rfl c₂.d01 c₂.d02 c₂.d12 c₂.sp c₂.f0 c₂.f1 c₂.f2 c₂.cov)
    fun v₁ v₂ ⟨kv₁, _⟩ ⟨kv₂, _⟩ => ?_
  have k₁ := ku₁.trans kv₁
  have k₂ := ku₂.trans kv₂
  exact rel_taint [.x19, .x20, .x21] (by rw [k₁.sp, k₂.sp, sp]) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [k₁.get .x19 (by simp [clobbered]), k₂.get .x19 (by simp [clobbered]), h19₁, h19₂]
      · rw [k₁.get .x20 (by simp [clobbered]), k₂.get .x20 (by simp [clobbered]), h20₁, h20₂]
      · rw [k₁.get .x21 (by simp [clobbered]), k₂.get .x21 (by simp [clobbered]), h21₁, h21₂])
    ⟨_, by taint_decide⟩

theorem sinv3_zero (S : Impl.MlKem.AArch64.Hybrid.HSrc) {s : State} {p e st : Addr} {E : List Byte}
    {A B : Spec.Sha3.State} {i : Nat} (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = p + 400)
    (h21 : s.gpr .x21 = p + 904) (pair : PairAt s.mem p A B) (hash : stateAt s.mem st = hstate E (3 * i) (dB S))
    (hE : bytesAt s.mem e S.len = E) : SInv3 S s p e st E A B i 0 s :=
  ⟨Keep.refl _ _, pair, h19, by rw [h20]; exact (BitVec.add_zero _).symm,
    by rw [h21]; exact (BitVec.add_zero _).symm, Frame.refl _ _,
    fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _), hash, hE⟩

theorem sstep_relCT (S : Impl.MlKem.AArch64.Hybrid.HSrc) (hS : SrcOk S) {init₁ init₂ s₁ s₂ : State}
    {p e st : Addr} {E₁ E₂ : List Byte} {A₁ B₁ A₂ B₂ : Spec.Sha3.State} {i k : Nat} (hk : k < 3)
    (hb : 136 * (3 * i + k) < S.len)
    (hl₁ : SqLay S p e st init₁) (hl₂ : SqLay S p e st init₂)
    (e25₁ : init₁.gpr S.r + BitVec.ofNat 64 S.base = e) (e28₁ : init₁.gpr .x28 = st)
    (e25₂ : init₂.gpr S.r + BitVec.ofNat 64 S.base = e) (e28₂ : init₂.gpr .x28 = st) (sp : init₁.sp = init₂.sp)
    (h₁ : SInv3 S init₁ p e st E₁ A₁ B₁ i k s₁) (h₂ : SInv3 S init₂ p e st E₂ A₂ B₂ i k s₂)
    (habs : ∃ h, (taint.check (Taint.ofRegs [S.r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock S (3 * i + k))) h).isSome = true) :
    RelCT isa (Eq2 s₁ s₂) (Impl.MlKem.AArch64.Hybrid.step3 S (3 * i + k)) TT :=
  step3_relCT S hS h₁.ptr h₁.pa h₁.pb (by rw [hS.keep h₁.keep (by decide) (by decide)]; exact e25₁)
    (by rw [h₁.keep.get .x28]; exact e28₁)
    h₂.ptr h₂.pa h₂.pb (by rw [hS.keep h₂.keep (by decide) (by decide)]; exact e25₂)
    (by rw [h₂.keep.get .x28]; exact e28₂)
    (by rw [h₁.keep.sp, h₂.keep.sp, sp]) hb h₁.ek h₁.hash h₂.ek h₂.hash h₁.pair h₂.pair
    ((hl₁.frame h₁.keep.rd h₁.keep.wr h₁.keep.sp).stepLay hk)
    ((hl₂.frame h₂.keep.rd h₂.keep.wr h₂.keep.sp).stepLay hk) habs

/-- **The three main squeezes** leak only public pointers. -/
theorem squeeze3_relCT (S : Impl.MlKem.AArch64.Hybrid.HSrc) (hS : SrcOk S) {s₁ s₂ : State} {p e st : Addr}
    {E₁ E₂ : List Byte} {A₁ B₁ A₂ B₂ : Spec.Sha3.State} {i : Nat}
    (hb : 136 * (3 * i + 2) < S.len)
    (hl₁ : SqLay S p e st s₁) (hl₂ : SqLay S p e st s₂)
    (e25₁ : s₁.gpr S.r + BitVec.ofNat 64 S.base = e) (e28₁ : s₁.gpr .x28 = st)
    (e25₂ : s₂.gpr S.r + BitVec.ofNat 64 S.base = e) (e28₂ : s₂.gpr .x28 = st) (sp : s₁.sp = s₂.sp)
    (h₁ : SInv3 S s₁ p e st E₁ A₁ B₁ i 0 s₁) (h₂ : SInv3 S s₂ p e st E₂ A₂ B₂ i 0 s₂)
    (habs : ∀ blk, 136 * blk < S.len → ∃ h, (taint.check (Taint.ofRegs [S.r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock S blk)) h).isSome = true) :
    RelCT isa (Eq2 s₁ s₂) (Impl.MlKem.AArch64.Hybrid.squeeze3 S i) TT := by
  unfold Impl.MlKem.AArch64.Hybrid.squeeze3
  refine rel_seq (sstep_relCT S hS (k := 0) (by decide) (by omega) hl₁ hl₂ e25₁ e28₁ e25₂ e28₂ sp h₁ h₂
      (habs _ (by omega)))
    (sstep_ok S (k := 0) (by decide) hS (by omega) hl₁ e28₁ e25₁ h₁)
    (sstep_ok S (k := 0) (by decide) hS (by omega) hl₂ e28₂ e25₂ h₂) fun t₁ t₂ ht₁ ht₂ => ?_
  refine rel_seq (sstep_relCT S hS (k := 1) (by decide) (by omega) hl₁ hl₂ e25₁ e28₁ e25₂ e28₂ sp ht₁ ht₂
      (habs _ (by omega)))
    (sstep_ok S (k := 1) (by decide) hS (by omega) hl₁ e28₁ e25₁ ht₁)
    (sstep_ok S (k := 1) (by decide) hS (by omega) hl₂ e28₂ e25₂ ht₂) fun u₁ u₂ hu₁ hu₂ => ?_
  exact sstep_relCT S hS (k := 2) (by decide) hb hl₁ hl₂ e25₁ e28₁ e25₂ e28₂ sp hu₁ hu₂ (habs _ hb)

end VG.Proof.MlKem.AArch64.Hybrid
