module

public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Squeeze
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Absorb
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Call
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeBlock

/-! ### `MlKem.AArch64.Hybrid.Step`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Hybrid.X3Call`, which only this module used -/

section

/-!
# Calls of `vg_keccak_f1600_x3` from ML-KEM's matrix

`x3call_ok`: the call (`Hybrid.x3call`) on the pair at `x19`, the third
state at `x28` and the working space at `x19 + 1536` (with `x30` kept in the
8 bytes after it, `X2.callR`) permutes the three states, changes memory only
in them, the working space and the function's 128-byte frame below the stack
pointer, keeps every register but `x0`–`x17` (`x30` is reloaded), from the
function's own proof (`X3.correct`, by `WP.callFV`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid
variable {sha3 : Bool}

open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR pair_contains)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR scrR pairAt_stateX2 stateX2_of_pairAt)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Spec.Sha3 (stateAt keccakF)

/-- The registers a call may change. -/
def clobbered : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem clobbered_preserved (r : Reg) (h : r ∉ clobbered) : r ∈ preserved := by
  cases r <;> first | exact absurd (by decide) h | decide

theorem depth (sha3 : Bool) : (Impl.Sha3.AArch64.Hybrid.X3.code sha3).aarch64Depth ≤ 8 := by
  cases sha3 <;> decide

/-- The function's frame. -/
abbrev frame (sp : Addr) : Region := below sp 128

/-- **A call** of `vg_keccak_f1600_x3` on the pair at `p` (`x19`) and
the state at `st` (`x28`). -/
theorem x3call_ok {s : State} {p q st : Addr} {A B S : Spec.Sha3.State}
    (hp : s.gpr .x19 = p) (hq : p + BitVec.ofNat 64 1536 = q) (hst : s.gpr .x28 = st)
    (hpair : PairAt s.mem p A B) (hS : stateAt s.mem st = S)
    (d01 : (pairR p).Disjoint (stR st)) (d02 : (pairR p).Disjoint (callR q))
    (d12 : (stR st).Disjoint (callR q))
    (hsp : 128 ≤ s.sp.toNat)
    (f0 : (frame s.sp).Disjoint (pairR p)) (f1 : (frame s.sp).Disjoint (stR st))
    (f2 : (frame s.sp).Disjoint (callR q))
    (hcov : Covers [pairR p, stR st, callR q] s.wr) :
    WP isa (Impl.MlKem.AArch64.Hybrid.x3call sha3) s fun t =>
      Keep clobbered s t ∧
      Frame [pairR p, stR st, callR q, frame s.sp] s.mem t.mem ∧
      PairAt t.mem p (keccakF A) (keccakF B) ∧ stateAt t.mem st = keccakF S := by
  obtain hscr : Region.Sub (scrR q) (callR q) := Region.sub_prefix (by decide : 128 ≤ 136)
  obtain hslotS : Region.Sub ⟨q + BitVec.ofNat 64 128, 8⟩ (callR q) :=
    Offset.sub_base q (d := 128) (n := 8) (k := 136) (by decide)
  obtain hslotR : (callR q).Contains (q + BitVec.ofNat 64 128) 8 := Offset.contains_base q (by decide) (by decide)
  obtain hslot : InRegions s.wr (q + BitVec.ofNat 64 128) 8 :=
    hcov _ _ ⟨callR q, by simp, hslotR⟩
  obtain hsub : Covers [pairR p, stR st, scrR q] [pairR p, stR st, callR q] :=
    Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨pairR p, by simp, 0, (BitVec.add_zero p).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨stR st, by simp, 0, (BitVec.add_zero st).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨callR q, by simp, 0, (BitVec.add_zero q).symm, by simp only [scrR, callR]; decide⟩
  obtain hslot_sep : ∀ r ∈ [pairR p, stR st, scrR q] ++ [below s.sp (16 * 8)],
      (⟨q + BitVec.ofNat 64 128, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (d02.sub_right hslotS).symm
    · exact (d12.sub_right hslotS).symm
    · exact Offset.disjoint_base q (d := 128) (n := 8) (k := 128) (by decide) (by decide)
    · exact (f2.sub_right hslotS).symm
  unfold Impl.MlKem.AArch64.Hybrid.x3call
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₁ o₁ e₁ => ?_)
  obtain h2 : s₁.gpr .x2 = q := by rw [e₁, hp, hq]
  refine VG.Proof.Sha3.AArch64.wp_str ⟨by decide, by decide⟩ (by rw [h2]) (by rw [o₁.wr]; exact hslot)
    fun s₂ m₂ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₃ o₃ e₃ =>
      VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₄ o₄ e₄ => WP.block_nil ?_
  obtain h0 : s₄.gpr .x0 = p := by
    rw [o₄.gpr _ (by decide), e₃, BitVec.add_zero, m₂.gpr, o₁.gpr _ (by decide), hp]
  obtain h1 : s₄.gpr .x1 = st := by
    rw [e₄, BitVec.add_zero, o₃.gpr _ (by decide), m₂.gpr, o₁.gpr _ (by decide), hst]
  obtain h2' : s₄.gpr .x2 = q := by
    rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), m₂.gpr, h2]
  obtain hlr : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → s₄.gpr r = s.gpr r := fun r h0 h1 h2 => by
    rw [o₄.gpr _ (by simpa using h1), o₃.gpr _ (by simpa using h0), m₂.gpr, o₁.gpr _ (by simpa using h2)]
  obtain hm : s₄.mem = s.mem.writeW (q + BitVec.ofNat 64 128) (s.gpr .x30) := by
    rw [o₄.mem, o₃.mem, m₂.mem, o₁.mem, o₁.gpr _ (by decide)]
  obtain hw : s₄.wr = s.wr := o₄.wr.trans (o₃.wr.trans (m₂.wr.trans o₁.wr))
  obtain hsp₄ : s₄.sp = s.sp := o₄.sp.trans (o₃.sp.trans (m₂.sp.trans o₁.sp))
  obtain ent : ∀ r, r = .x0 ∨ r = .x1 ∨ r = .x2 → (s₄.callEntry.withRegions [] [pairR p, stR st, scrR q]).gpr r = s₄.gpr r := by
    intro r hr
    simp only [State.withRegions_gpr]
    rcases hr with rfl | rfl | rfl <;> exact State.callEntry_gpr s₄ (by decide)
  refine WP.seq (WP.callFV (k := VG.Proof.Sha3.AArch64.Hybrid.X3.K) (rd := [])
    (wr := [pairR p, stR st, scrR q]) (VG.Proof.Sha3.AArch64.Hybrid.X3.correct sha3)
    ⟨rfl, by simp only [State.withRegions_wr, ent .x0 (by simp), ent .x1 (by simp), ent .x2 (by simp), h0, h1, h2'],
      by simpa only [ent .x0 (by simp), ent .x1 (by simp), h0, h1] using d01,
      by simpa only [ent .x0 (by simp), ent .x2 (by simp), h0, h2'] using d02.sub_right hscr,
      by simpa only [ent .x1 (by simp), ent .x2 (by simp), h1, h2'] using d12.sub_right hscr,
      by simpa only [State.withRegions_sp, State.callEntry_sp, hsp₄] using hsp,
      by simp only [State.withRegions_sp, State.callEntry_sp, hsp₄, ent .x0 (by simp), h0]; exact f0,
      by simp only [State.withRegions_sp, State.callEntry_sp, hsp₄, ent .x1 (by simp), h1]; exact f1,
      by simp only [State.withRegions_sp, State.callEntry_sp, hsp₄, ent .x2 (by simp), h2']
         exact f2.sub_right hscr⟩
    (by rw [hw]; exact Covers.right (hsub.trans hcov)) (by rw [hw]; exact hsub.trans hcov) ?_
    (by have hd := depth sha3; omega_using [hd]))
  intro t hr hwr hsp hf hk hv hpost
  rw [hsp₄] at hf
  obtain hf : Frame ([pairR p, stR st, scrR q] ++ [below s.sp (16 * 8)]) s₄.mem t.mem :=
    hf.sub fun r hr => by
      rw [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          below_sub (by have hd := depth sha3; omega_using [hd]) (by decide)⟩
  obtain hf₄ : Frame [callR q] s.mem s₄.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hslotR
  obtain hpair₄ : PairAt s₄.mem p A B := fun i hi => by
    rw [hf₄.read (pair_contains p hi) (by simpa using d02) (by decide)]; exact hpair i hi
  obtain hS₄ : stateAt s₄.mem st = S := by
    rw [← hS]
    exact VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame hf₄ (by simpa using d12)
  simp only [VG.Proof.Sha3.AArch64.Hybrid.X3.K, State.withRegions_mem, State.callEntry_mem,
    ent .x0 (by simp), ent .x1 (by simp), h0, h1] at hpost
  obtain ⟨hA, hB⟩ := stateX2_of_pairAt hpair₄
  rw [hA, hB, hS₄] at hpost
  obtain hval : t.mem.readW (q + BitVec.ofNat 64 128) 64 = s.gpr .x30 := by
    rw [hf.readW (r := ⟨q + BitVec.ofNat 64 128, 8⟩) (Region.contains_self _ _) hslot_sep (by decide),
      hm, Mem.readW_writeW_self64]
  obtain ht19 : t.gpr .x19 = p := by rw [hk .x19 (by decide) (by decide), hlr .x19 (by decide) (by decide) (by decide), hp]
  refine VG.Proof.Sha3.AArch64.wp_ldr (a := q + BitVec.ofNat 64 128) ⟨by decide, by decide⟩
    (by rw [ht19, ← hq, BitVec.add_assoc]; rfl)
    (by obtain ⟨R, hR, hc⟩ := hslot
        refine ⟨R, ?_, hc⟩
        rw [hwr, hw]
        exact List.mem_append_right _ hR)
    fun u hu => WP.block_nil ⟨⟨fun r hr' => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · by_cases h30 : r = .x30
    · subst r; rw [hu.gpr, hval]
    · have hpres := clobbered_preserved r hr'
      rw [hu.other r h30, hk r hpres h30]
      have : r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 := by
        simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        exact ⟨hr'.1, hr'.2.1, hr'.2.2.1⟩
      exact hlr r this.1 this.2.1 this.2.2
  · rw [hu.rd, hr, o₄.rd, o₃.rd, m₂.rd, o₁.rd]
  · rw [hu.wr, hwr, hw]
  · rw [hu.sp, hsp, hsp₄]
  · intro r hr
    rw [hu.vec, hv r hr, o₄.vcs r hr, o₃.vcs r hr, m₂.vec, o₁.vcs r hr]
  · rw [hu.mem]
    refine (hf₄.mono (fun r hr => by simp at hr; simp [hr])).trans (hf.sub fun r hr => ?_)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨pairR p, by simp, fun _ h => h⟩
    · exact ⟨stR st, by simp, fun _ h => h⟩
    · exact ⟨callR q, by simp, hscr⟩
    · exact ⟨frame s.sp, by simp, fun _ h => h⟩
  · rw [hu.mem]
    have := pairAt_stateX2 t.mem p
    rwa [hpost.1, hpost.2.1] at this
  · rw [hu.mem]; exact hpost.2.2

end VG.Proof.MlKem.AArch64.Hybrid

end

end


/-!
# One main squeeze of a hashing pair

`step3_ok`: block `blk` of the message's padding XORed into the third state, the `x3`
call, then both SHAKE128 states' 21 words to their stream buffers. `plainStep_ok`: the
same squeeze absorbing no block, with `vg_keccak_f1600_x2`, which leaves the third
state as it was.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid
variable {sha3 : Bool}

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr outAddr)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (rateR21 Rate21)
open VG.Spec.Sha3 (stateAt bytesAt keccakF)

theorem covers_mono {xs ys X : List Region} (h : Covers ys X) (hs : ∀ r ∈ xs, r ∈ ys) : Covers xs X :=
  fun a n ⟨r, hr, hc⟩ => h a n ⟨r, hs r hr, hc⟩

/-- The squeeze's tail. -/
theorem tail_ok {s : State} {p a b : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19 = p) (ha : s.gpr .x20 = a) (hb : s.gpr .x21 = b)
    (pair : PairAt s.mem p A B)
    (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (wordAddr p i) 16)
    (hwa : ∀ i < 21, InRegions s.wr (outAddr a i) 8)
    (hwb : ∀ i < 21, InRegions s.wr (outAddr b i) 8)
    (hd : (rateR21 a).Disjoint (rateR21 b))
    (hpa : (pairR p).Disjoint (rateR21 a)) (hpb : (pairR p).Disjoint (rateR21 b)) :
    WP isa (.block Impl.MlKem.AArch64.Hybrid.squeezeTail) s fun t =>
      Keep [.x6, .x7, .x20, .x21] s t ∧ Frame [rateR21 a, rateR21 b] s.mem t.mem ∧
      Rate21 t.mem a A ∧ Rate21 t.mem b B ∧ t.gpr .x20 = a + 168 ∧ t.gpr .x21 = b + 168 := by
  unfold Impl.MlKem.AArch64.Hybrid.squeezeTail
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.X2.squeeze_ok (n := 21) (by decide) hp ha hb
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) pair hd hpa hpb hin hwa hwb)
    fun u ⟨hu, hfu, hau, hbu⟩ => ?_
  refine wp_addImm (by decide) fun v1 h1 e1 => wp_addImm (by decide) fun t h2 e2 => wp_nil ?_
  obtain ku : Keep [.x6, .x7] s u := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hu.gpr r hr.1 hr.2,
    hu.rd, hu.wr, hu.sp, fun r _ => by rw [hu.vec]⟩
  obtain ot : Only [.x20, .x21] u t := (h1.trans h2).mono (by simp)
  have hm : t.mem = u.mem := ot.mem
  refine ⟨(ku.trans ot.keep).mono (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact hfu
  · rw [hm]; exact hau
  · rw [hm]; exact hbu
  · rw [h2.get .x20 (by decide), e1, hu.gpr .x20 (by decide) (by decide), ha]; rfl
  · rw [e2, h1.get .x21 (by decide), hu.gpr .x21 (by decide) (by decide), hb]; rfl

/-- The registers a main squeeze may change. -/
def stepRegs : List Reg := clobbered ++ [.x20, .x21]

/-- The regions a main squeeze writes. -/
def step3Writes (p a b st sp : Addr) : List Region :=
  [pairR p, rateR21 a, rateR21 b, callR (p + 1536), stR st, frame sp]

/-- What a main squeeze needs of its memory. -/
structure StepLay (S : Impl.MlKem.AArch64.Hybrid.HSrc) (p a b e st : Addr) (s : State) : Prop where
  cov : Covers [pairR p, stR st, callR (p + 1536)] s.wr
  ek : Covers [⟨e, S.len⟩] (s.rd ++ s.wr)
  hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (wordAddr p i) 16
  hwa : ∀ i < 21, InRegions s.wr (outAddr a i) 8
  hwb : ∀ i < 21, InRegions s.wr (outAddr b i) 8
  sp : 128 ≤ s.sp.toNat
  dAB : (rateR21 a).Disjoint (rateR21 b)
  dPA : (pairR p).Disjoint (rateR21 a)
  dPB : (pairR p).Disjoint (rateR21 b)
  dPS : (pairR p).Disjoint (stR st)
  dPC : (pairR p).Disjoint (callR (p + 1536))
  dSC : (stR st).Disjoint (callR (p + 1536))
  dSA : (stR st).Disjoint (rateR21 a)
  dSB : (stR st).Disjoint (rateR21 b)
  dSE : (stR st).Disjoint ⟨e, S.len⟩
  fP : (frame s.sp).Disjoint (pairR p)
  fS : (frame s.sp).Disjoint (stR st)
  fC : (frame s.sp).Disjoint (callR (p + 1536))

/-- **A main squeeze** absorbing block `blk`. -/
theorem step3_ok (S : Impl.MlKem.AArch64.Hybrid.HSrc) {s : State} {p a b e st : Addr}
    {A B : Spec.Sha3.State} {E : List Byte} {blk : Nat} (hS : SrcOk S)
    (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = a) (h21 : s.gpr .x21 = b)
    (h25 : s.gpr S.r + BitVec.ofNat 64 S.base = e) (h28 : s.gpr .x28 = st)
    (hb : 136 * blk < S.len)
    (hE : bytesAt s.mem e S.len = E) (hst : stateAt s.mem st = hstate E blk (dB S))
    (pair : PairAt s.mem p A B) (hl : StepLay S p a b e st s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.step3 sha3 S blk) s fun t =>
      Keep stepRegs s t ∧
      Frame (step3Writes p a b st s.sp) s.mem t.mem ∧
      PairAt t.mem p (keccakF A) (keccakF B) ∧
      Rate21 t.mem a (keccakF A) ∧ Rate21 t.mem b (keccakF B) ∧
      stateAt t.mem st = hstate E (blk + 1) (dB S) ∧
      t.gpr .x20 = a + 168 ∧ t.gpr .x21 = b + 168 := by
  refine WP.seq (WP.mono (absorbBlock_ok S hS h25 h28 hb hE hst hl.ek
    (covers_mono hl.cov (by simp))
    hl.dSE) fun u ⟨ku, fu, su⟩ => ?_)
  obtain pu : PairAt u.mem p A B :=
    VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pair fu (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl.dPS)
  refine WP.seq (WP.mono (x3call_ok (sha3 := sha3) (q := p + 1536) (S := stateAt u.mem st)
    (by rw [ku.get .x19, h19]) rfl (by rw [ku.get .x28, h28]) pu rfl hl.dPS hl.dPC hl.dSC
    (by rw [ku.sp]; exact hl.sp) (by rw [ku.sp]; exact hl.fP) (by rw [ku.sp]; exact hl.fS)
    (by rw [ku.sp]; exact hl.fC) (by rw [ku.wr]; exact hl.cov)) fun v ⟨kv, fv, pv, sv⟩ => ?_)
  rw [ku.sp] at fv
  obtain kuv := ku.trans kv
  refine WP.mono (tail_ok (by rw [kuv.get .x19, h19]) (by rw [kuv.get .x20, h20])
    (by rw [kuv.get .x21, h21]) pv
    (fun i hi => by rw [kuv.rd, kuv.wr]; exact hl.hin i hi)
    (fun i hi => by rw [kuv.wr]; exact hl.hwa i hi) (fun i hi => by rw [kuv.wr]; exact hl.hwb i hi)
    hl.dAB hl.dPA hl.dPB) fun t ⟨kt, ft, at', bt, t20, t21⟩ => ?_
  obtain fvt : ∀ r ∈ [rateR21 a, rateR21 b], (pairR p).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; exact hl.dPA; exact hl.dPB
  obtain svt : ∀ r ∈ [rateR21 a, rateR21 b], (stR st).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; exact hl.dSA; exact hl.dSB
  refine ⟨(kuv.trans kt).mono (by simp [stepRegs, clobbered]), ?_, ?_, at', bt, ?_, t20, t21⟩
  · refine ((fu.mono (by simp [step3Writes])).trans (fv.mono (by simp [step3Writes]))).trans
      (ft.mono (by simp [step3Writes]))
  · exact VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pv ft fvt
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame ft svt, sv, su]

/-- **A main squeeze absorbing no block.** -/
theorem plainStep_ok (S : Impl.MlKem.AArch64.Hybrid.HSrc) {s : State} {p a b e st : Addr}
    {A B : Spec.Sha3.State}
    (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = a) (h21 : s.gpr .x21 = b)
    (pair : PairAt s.mem p A B) (hl : StepLay S p a b e st s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.plainStep sha3) s fun t =>
      Keep stepRegs s t ∧
      Frame (step3Writes p a b st s.sp) s.mem t.mem ∧
      PairAt t.mem p (keccakF A) (keccakF B) ∧
      Rate21 t.mem a (keccakF A) ∧ Rate21 t.mem b (keccakF B) ∧
      stateAt t.mem st = stateAt s.mem st ∧
      t.gpr .x20 = a + 168 ∧ t.gpr .x21 = b + 168 := by
  obtain hc := Paired.squeezeBlock_ok (sha3 := sha3) (rp := .x19) (ra := .x20) (rb := .x21) h19 h20 h21 (by rw [h19]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pair hl.hin hl.hwa hl.hwb hl.dAB hl.dPA hl.dPB hl.dPC
    (covers_mono hl.cov (by simp))
  unfold Impl.MlKem.AArch64.Hybrid.plainStep Impl.MlKem.AArch64.Hybrid.squeezeTail
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp hc) fun u hu => ?_
  rw [WP.block_append_iff]
  refine WP.mono hu fun v ⟨kv, pv, av, bv, fv, vv⟩ => ?_
  refine wp_addImm (by decide) fun v1 h1 e1 => wp_addImm (by decide) fun t h2 e2 => wp_nil ?_
  obtain hv : Keep Paired.blockRegs s v := ⟨kv.gpr, kv.rd, kv.wr, kv.sp, vv⟩
  obtain ot : Only [.x20, .x21] v t := (h1.trans h2).mono (by simp)
  have hm : t.mem = v.mem := ot.mem
  obtain fr : ∀ r ∈ [pairR p, rateR21 a, rateR21 b, callR (p + 1536)], (stR st).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hl.dPS.symm
    · exact hl.dSA
    · exact hl.dSB
    · exact hl.dSC
  refine ⟨(hv.trans ot.keep).mono (by simp [stepRegs, clobbered, Paired.blockRegs, VG.Proof.Sha3.AArch64.Neon.X2.volatile]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact fv.mono (by simp [step3Writes])
  · rw [hm]; exact pv
  · rw [hm]; exact av
  · rw [hm]; exact bv
  · rw [hm]; exact VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fv fr
  · rw [h2.get .x20 (by decide), e1, kv.gpr .x20 (by decide), h20]; rfl
  · rw [e2, h1.get .x21 (by decide), kv.gpr .x21 (by decide), h21]; rfl

end VG.Proof.MlKem.AArch64.Hybrid

end

end

/-!
# The three main squeezes of a hashing pair

`squeezeM_ok`: the three main squeezes of a pair (`squeezeM`) squeeze three
SHAKE128 blocks of each matrix stream, as `Paired.squeeze` does, and the first
`m` absorb blocks `j`, …, `j + m - 1` of the message's padding into the third
state. `startM_ok`: with the pair's initialization before them (as
`Paired.start_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid
variable {sha3 : Bool}

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr outAddr)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (rateR21 Rate21 Blocks blockAt streamR block_sub)
open VG.Proof.Sha3 (iterF iterF_succ)
open VG.Spec.Sha3 (stateAt bytesAt keccakF)

/-- What a hashing pair's squeezes may write. -/
def squeezeWrites (p st sp : Addr) : List Region :=
  [pairR p, streamR (p + 400), streamR (p + 904), callR (p + 1536), stR st, frame sp]

/-- What a hashing pair's start may write. -/
def startWrites (p st sp : Addr) : List Region := [⟨p, 2048⟩, stR st, frame sp]

/-- After `k` of the three main squeezes, the first `m` absorbing from block `j`. -/
structure SInvM (S : Impl.MlKem.AArch64.Hybrid.HSrc) (initial : State) (p e st : Addr) (E : List Byte)
    (A B : Spec.Sha3.State) (j m k : Nat) (s : State) : Prop where
  keep : Keep stepRegs initial s
  pair : PairAt s.mem p (iterF k A) (iterF k B)
  ptr : s.gpr .x19 = p
  pa : s.gpr .x20 = blockAt (p + 400) k
  pb : s.gpr .x21 = blockAt (p + 904) k
  frame : Frame (squeezeWrites p st initial.sp) initial.mem s.mem
  oa : Blocks s.mem (p + 400) k A
  ob : Blocks s.mem (p + 904) k B
  hash : stateAt s.mem st = hstate E (j + min k m) (dB S)
  ek : bytesAt s.mem e S.len = E

/-- What the pair's memory is. -/
structure SqLay (S : Impl.MlKem.AArch64.Hybrid.HSrc) (p e st : Addr) (s : State) : Prop where
  scratch : Covers [⟨p, 2048⟩] s.wr
  state : Covers [stR st] s.wr
  ekr : Covers [⟨e, S.len⟩] (s.rd ++ s.wr)
  sp : 128 ≤ s.sp.toNat
  dSP : (stR st).Disjoint ⟨p, 2048⟩
  dSE : (stR st).Disjoint ⟨e, S.len⟩
  dEP : (Region.mk e S.len).Disjoint ⟨p, 2048⟩
  fP : (frame s.sp).Disjoint ⟨p, 2048⟩
  fS : (frame s.sp).Disjoint (stR st)
  fE : (frame s.sp).Disjoint ⟨e, S.len⟩

theorem SqLay.frame {S : Impl.MlKem.AArch64.Hybrid.HSrc} {p e st : Addr} {s t : State} (h : SqLay S p e st s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp) : SqLay S p e st t := by
  refine ⟨?_, ?_, ?_, ?_, h.dSP, h.dSE, h.dEP, ?_, ?_, ?_⟩ <;> simp only [hr, hw, hsp]
  exacts [h.scratch, h.state, h.ekr, h.sp, h.fP, h.fS, h.fE]

theorem in_scratch {X : List Region} {p : Addr} (h : Covers [⟨p, 2048⟩] X) {o n : Nat} (ho : o + n ≤ 2048) :
    InRegions X (p + BitVec.ofNat 64 o) n := covers_in h ho (by decide)

theorem cov_scratch {X : List Region} {p : Addr} (h : Covers [⟨p, 2048⟩] X) {o n : Nat} (ho : o + n ≤ 2048) :
    Covers [⟨p + BitVec.ofNat 64 o, n⟩] X :=
  (Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, o, rfl, ho⟩).trans h

theorem blockAt_eq (p : Addr) (o k : Nat) :
    blockAt (p + BitVec.ofNat 64 o) k = p + BitVec.ofNat 64 (o + 168 * k) := by
  simp only [blockAt]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem outAddr_eq (p : Addr) (o i : Nat) :
    outAddr (p + BitVec.ofNat 64 o) i = p + BitVec.ofNat 64 (o + 8 * i) := by
  simp only [outAddr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem SqLay.stepLay {S : Impl.MlKem.AArch64.Hybrid.HSrc} {p e st : Addr} {s : State} (h : SqLay S p e st s)
    {k : Nat} (hk : k < 3) :
    StepLay S p (blockAt (p + 400) k) (blockAt (p + 904) k) e st s := by
  have ea : blockAt (p + 400) k = p + BitVec.ofNat 64 (400 + 168 * k) := blockAt_eq p 400 k
  have eb : blockAt (p + 904) k = p + BitVec.ofNat 64 (904 + 168 * k) := blockAt_eq p 904 k
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  have subP : Region.Sub (pairR p) ⟨p, 2048⟩ := Region.sub_prefix (by decide : 400 ≤ 2048)
  rw [ea, eb]
  refine ⟨?_, h.ekr, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, h.sp,
    Offset.disjoint p (by omega_arith) (by omega_arith) (by omega_arith),
    Offset.base_disjoint p (by omega_arith) (by omega_arith), Offset.base_disjoint p (by omega_arith) (by omega_arith),
    (h.dSP.sub_right subP).symm, Offset.base_disjoint p (e := 1536) (n := 136) (by decide) (by decide),
    h.dSP.sub_right (sub (o := 1536) (n := 136) (by decide)), h.dSP.sub_right (sub (by omega_arith)),
    h.dSP.sub_right (sub (by omega_arith)),
    h.dSE, h.fP.sub_right subP, h.fS, h.fP.sub_right (sub (o := 1536) (n := 136) (by decide))⟩
  · refine Covers.cons ?_ (Covers.cons (covers_mono h.state (by simp)) (Covers.cons ?_ Covers.nil))
    · simpa only [BitVec.add_zero, pairR] using cov_scratch (o := 0) (n := 400) h.scratch (by decide)
    · exact cov_scratch (o := 1536) (n := 136) h.scratch (by decide)
  · exact Covers.right (cov_scratch h.scratch (o := 16 * i) (n := 16) (by omega_arith)) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  · rw [outAddr_eq]; exact in_scratch h.scratch (by omega_arith)
  · rw [outAddr_eq]; exact in_scratch h.scratch (by omega_arith)

theorem extend_blocks3 {m m' : Mem} {p a b st sp : Addr} {A : Spec.Sha3.State} {k : Nat} (hk : k < 3)
    (old : Blocks m a k A) (new : Rate21 m' (blockAt a k) (iterF (k + 1) A))
    (hf : Frame (step3Writes p (blockAt a k) (blockAt b k) st sp) m m')
    (hpa : (pairR p).Disjoint (streamR a)) (hab : (streamR a).Disjoint (streamR b))
    (hwa : (callR (p + 1536)).Disjoint (streamR a)) (hsa : (stR st).Disjoint (streamR a))
    (hfa : (frame sp).Disjoint (streamR a)) : Blocks m' a (k + 1) A := by
  intro j hj
  by_cases he : j = k
  · subst j; exact new
  · have hjk : j < k := by omega_arith
    intro i hi
    have hc : (rateR21 (blockAt a j)).Contains (outAddr (blockAt a j) i) 8 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [hf.readW hc (by
        intro r hr; simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (hpa.sub_right (block_sub a (by omega_arith))).symm
        · exact Offset.disjoint a (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
        · exact (hab.sub_left (block_sub a (by omega_arith))).sub_right (block_sub b hk)
        · exact (hwa.sub_right (block_sub a (by omega_arith))).symm
        · exact (hsa.sub_right (block_sub a (by omega_arith))).symm
        · exact (hfa.sub_right (block_sub a (by omega_arith))).symm) (by decide)]
    exact old j hjk i hi

/-- One of the three main squeezes. -/
theorem sstep_ok (S : Impl.MlKem.AArch64.Hybrid.HSrc) {initial s : State} {p e st : Addr} {E : List Byte}
    {A B : Spec.Sha3.State} {j m k : Nat} (hk : k < 3) (hS : SrcOk S)
    (hb : k < m → 136 * (j + k) < S.len)
    (hl : SqLay S p e st initial) (h28 : initial.gpr .x28 = st)
    (h25 : initial.gpr S.r + BitVec.ofNat 64 S.base = e)
    (h : SInvM S initial p e st E A B j m k s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.stepM sha3 S j m k) s (SInvM S initial p e st E A B j m (k + 1)) := by
  have hls : SqLay S p e st s := hl.frame h.keep.rd h.keep.wr h.keep.sp
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  have next : ∀ {t : State}, Keep stepRegs s t → Frame (step3Writes p (blockAt (p + 400) k)
      (blockAt (p + 904) k) st s.sp) s.mem t.mem →
      PairAt t.mem p (keccakF (iterF k A)) (keccakF (iterF k B)) →
      Rate21 t.mem (blockAt (p + 400) k) (keccakF (iterF k A)) →
      Rate21 t.mem (blockAt (p + 904) k) (keccakF (iterF k B)) →
      stateAt t.mem st = hstate E (j + min (k + 1) m) (dB S) →
      t.gpr .x20 = blockAt (p + 400) k + 168 → t.gpr .x21 = blockAt (p + 904) k + 168 →
      SInvM S initial p e st E A B j m (k + 1) t := by
    intro t kt ft pt at' bt st' t20 t21
    have fsub : Frame (squeezeWrites p st initial.sp) s.mem t.mem := by
      rw [h.keep.sp] at ft
      refine ft.sub fun r hr => ?_
      simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨pairR p, by simp [squeezeWrites], fun _ h => h⟩
      · exact ⟨streamR (p + 400), by simp [squeezeWrites], block_sub _ hk⟩
      · exact ⟨streamR (p + 904), by simp [squeezeWrites], block_sub _ hk⟩
      · exact ⟨callR (p + 1536), by simp [squeezeWrites], fun _ h => h⟩
      · exact ⟨stR st, by simp [squeezeWrites], fun _ h => h⟩
      · exact ⟨frame initial.sp, by simp [squeezeWrites], fun _ h => h⟩
    have dP : ∀ {o : Nat}, o + 504 ≤ 2048 → (frame initial.sp).Disjoint (streamR (p + BitVec.ofNat 64 o)) :=
      fun h => hl.fP.sub_right (sub h)
    rw [h.keep.sp] at ft
    refine ⟨(h.keep.trans kt).mono (fun r hr => by rcases List.mem_append.mp hr with h | h <;> exact h), ?_, (kt.get .x19).trans h.ptr, ?_, ?_,
      h.frame.trans fsub, ?_, ?_, st', ?_⟩
    · simpa only [iterF_succ] using pt
    · rw [t20]; show (p + 400 + BitVec.ofNat 64 (168 * k)) + BitVec.ofNat 64 168 = p + 400 + BitVec.ofNat 64 (168 * (k + 1))
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 168 * k + 168 = 168 * (k + 1) by omega_arith]
    · rw [t21]; show (p + 904 + BitVec.ofNat 64 (168 * k)) + BitVec.ofNat 64 168 = p + 904 + BitVec.ofNat 64 (168 * (k + 1))
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 168 * k + 168 = 168 * (k + 1) by omega_arith]
    · exact extend_blocks3 hk h.oa (by simpa only [iterF_succ] using at') ft
        (Offset.base_disjoint p (by decide) (by decide)) (Offset.disjoint p (by decide) (by decide) (by decide))
        (Offset.disjoint p (by decide) (by decide) (by decide)) (hl.dSP.sub_right (sub (by decide)))
        (dP (by decide))
    · refine extend_blocks3 hk h.ob (by simpa only [iterF_succ] using bt) (ft.mono ?_)
        (Offset.base_disjoint p (by decide) (by decide))
        (Offset.disjoint p (d := 400) (n := 504) (e := 904) (k := 504) (by decide) (by decide) (by decide)).symm
        (Offset.disjoint p (by decide) (by decide) (by decide)) (hl.dSP.sub_right (sub (by decide)))
        (dP (by decide))
      intro r hr; simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h <;> simp [h]
    · rw [VG.Proof.MlKem.bytesAt_frame ft (fun r hr => ?_) (by have := hS.lim; omega_arith)]
      · exact h.ek
      simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
      have dEP := hl.dEP
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact dEP.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048))
      · show Region.Disjoint _ ⟨blockAt (p + BitVec.ofNat 64 400) k, 168⟩
        rw [blockAt_eq]; exact dEP.sub_right (sub (by omega_arith))
      · show Region.Disjoint _ ⟨blockAt (p + BitVec.ofNat 64 904) k, 168⟩
        rw [blockAt_eq]; exact dEP.sub_right (sub (by omega_arith))
      · exact dEP.sub_right (sub (by decide))
      · exact hl.dSE.symm
      · exact hl.fE.symm
  unfold Impl.MlKem.AArch64.Hybrid.stepM
  split
  · rename_i hkm
    refine WP.mono (step3_ok (sha3 := sha3) S hS h.ptr h.pa h.pb
      (by rw [hS.keep h.keep (by decide) (by decide)]; exact h25)
      (by rw [h.keep.get .x28]; exact h28) (hb hkm) h.ek
      (by rw [h.hash, Nat.min_eq_left (Nat.le_of_lt hkm)]) h.pair (hls.stepLay hk))
      fun t ⟨kt, ft, pt, at', bt, st', t20, t21⟩ => next kt ft pt at' bt ?_ t20 t21
    rw [st', Nat.min_eq_left (show k + 1 ≤ m by omega_arith), Nat.add_assoc]
  · rename_i hkm
    refine WP.mono (plainStep_ok (sha3 := sha3) S h.ptr h.pa h.pb h.pair (hls.stepLay hk))
      fun t ⟨kt, ft, pt, at', bt, st', t20, t21⟩ => next kt ft pt at' bt ?_ t20 t21
    rw [st', h.hash, Nat.min_eq_right (show m ≤ k by omega_arith), Nat.min_eq_right (show m ≤ k + 1 by omega_arith)]

/-- **The three main squeezes** of a pair, the first `m` absorbing from block `j`. -/
theorem squeezeM_ok (S : Impl.MlKem.AArch64.Hybrid.HSrc) {s : State} {p e st : Addr} {E : List Byte}
    {A B : Spec.Sha3.State} {j m : Nat} (hS : SrcOk S)
    (hb : ∀ k < m, k < 3 → 136 * (j + k) < S.len)
    (hl : SqLay S p e st s) (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = p + 400)
    (h21 : s.gpr .x21 = p + 904) (h25 : s.gpr S.r + BitVec.ofNat 64 S.base = e) (h28 : s.gpr .x28 = st)
    (pair : PairAt s.mem p A B) (hash : stateAt s.mem st = hstate E j (dB S))
    (hE : bytesAt s.mem e S.len = E) :
    WP isa (Impl.MlKem.AArch64.Hybrid.squeezeM sha3 S j m) s (SInvM S s p e st E A B j m 3) := by
  have h0 : SInvM S s p e st E A B j m 0 s :=
    ⟨Keep.refl _ _, pair, h19, by rw [h20]; exact (BitVec.add_zero _).symm,
      by rw [h21]; exact (BitVec.add_zero _).symm, Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
      by rw [hash, Nat.zero_min, Nat.add_zero], hE⟩
  unfold Impl.MlKem.AArch64.Hybrid.squeezeM
  refine WP.seq (WP.mono (sstep_ok (sha3 := sha3) S (k := 0) (by decide) hS (fun h => hb 0 h (by decide)) hl h28 h25 h0)
    fun t ht => ?_)
  refine WP.seq (WP.mono (sstep_ok (sha3 := sha3) S (k := 1) (by decide) hS (fun h => hb 1 h (by decide)) hl h28 h25 ht)
    fun u hu => ?_)
  exact sstep_ok (sha3 := sha3) S (k := 2) (by decide) hS (fun h => hb 2 h (by decide)) hl h28 h25 hu

def startRegs3 : List Reg := Paired.initRegs ++ stepRegs

/-- **A hashing pair's initialization and main squeezes** (as `Paired.start_ok`). -/
theorem startM_ok (L : Impl.MlKem.AArch64.KemLay) (S : Impl.MlKem.AArch64.Hybrid.HSrc) {s : State}
    {p seed e st : Addr} {E : List Byte} {sb ss a b j m : Nat} (hS : SrcOk S)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0)
    (hp : s.gpr .x28 + BitVec.ofNat 64 ss = p) (ha : s.gpr .x28 + BitVec.ofNat 64 sb = seed)
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (seed + BitVec.ofNat 64 (8 * j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p, 2048⟩)
    (hl : SqLay S p e st s) (h25 : s.gpr S.r + BitVec.ofNat 64 S.base = e) (h28 : s.gpr .x28 = st)
    (hb : ∀ k < m, k < 3 → 136 * (j + k) < S.len)
    (hash : stateAt s.mem st = hstate E j (dB S)) (hE : bytesAt s.mem e S.len = E) :
    WP isa (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b L.k)) (Impl.MlKem.AArch64.Hybrid.squeezeM sha3 S j m)) s
      fun t =>
      Keep startRegs3 s t ∧ Frame (startWrites p st s.sp) s.mem t.mem ∧ Noise.Saved p s t.mem ∧
      t.gpr .x19 = p ∧
      PairAt t.mem p (iterF 3 (Paired.seedState s.mem seed a L.k)) (iterF 3 (Paired.seedState s.mem seed b L.k)) ∧
      Blocks t.mem (p + 400) 3 (Paired.seedState s.mem seed a L.k) ∧
      Blocks t.mem (p + 904) 3 (Paired.seedState s.mem seed b L.k) ∧
      stateAt t.mem st = hstate E (j + min 3 m) (dB S) ∧ bytesAt t.mem e S.len = E := by
  have hc := hl.scratch
  have iw {o l : Nat} (h : o + l ≤ 2048) := Noise.inScratch hc h (by decide)
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  refine WP.seq (WP.mono (Paired.init_ok hss hsb h8b hp ha hin
    (fun j hj => iw (by omega_arith)) (fun j hj => iw (by omega_arith))
    (hsep.sub_right (Offset.sub_base p (by decide)))
    (hsep.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048)))
    (Offset.disjoint_base p (by decide) (by decide))) fun u ⟨ku, fu, sv, h19, h20, h21, h22, pair⟩ => ?_)
  have fi : Frame [⟨p, 2048⟩] s.mem u.mem := fu.sub (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨p, 2048⟩, by simp, Offset.sub_base p (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp, Region.sub_prefix (by decide : 400 ≤ 2048)⟩)
  have hsu : stateAt u.mem st = hstate E j (dB S) := by
    rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fi (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl.dSP), hash]
  have heu : bytesAt u.mem e S.len = E := by
    rw [VG.Proof.MlKem.bytesAt_frame fi (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl.dEP) (by have := hS.lim; omega_arith), hE]
  refine WP.mono (squeezeM_ok (sha3 := sha3) S hS hb (hl.frame ku.rd ku.wr ku.sp) h19 h20 h21
    (by rw [hS.keep ku (by decide) (by decide)]; exact h25) (by rw [ku.get .x28]; exact h28) pair hsu heu) fun t ht => ?_
  refine ⟨ku.trans ht.keep, ?_, ?_, ht.ptr, ht.pair, ht.oa, ht.ob, ht.hash, ht.ek⟩
  · have ft := ht.frame
    rw [ku.sp] at ft
    refine (fi.mono (by simp [startWrites])).trans (ft.sub fun r hr => ?_)
    simp only [squeezeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨p, 2048⟩, by simp [startWrites], Region.sub_prefix (by decide : 400 ≤ 2048)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWrites], sub (o := 400) (n := 504) (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWrites], sub (o := 904) (n := 504) (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWrites], sub (o := 1536) (n := 136) (by decide)⟩
    · exact ⟨stR st, by simp [startWrites], fun _ h => h⟩
    · exact ⟨frame s.sp, by simp [startWrites], fun _ h => h⟩
  · apply sv.frame ht.frame
    intro r hr; simp only [squeezeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact (hl.dSP.sub_right (sub (o := 1800) (n := 48) (by decide))).symm
    · rw [ku.sp]; exact (hl.fP.sub_right (sub (o := 1800) (n := 48) (by decide))).symm

end VG.Proof.MlKem.AArch64.Hybrid
