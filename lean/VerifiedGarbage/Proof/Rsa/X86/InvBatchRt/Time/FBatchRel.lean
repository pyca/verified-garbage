module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.FRowRel
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FBatch
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FScatter
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Framework.Omega

/-! # The fused batches' operations in both runs

Each is `relOp` or `leafU` of its correctness, as the batched inverse's other operations
(`Kinds`), but the rows (`relRow`); a batch's rows keep the masks they read (`ME`), which
`coefMasks` and `mdme` write. `relBatchCodeF`: a batch, given the analysis's checks of its parts.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.X86.InvBatchRt.F (maskW startF startF_ok coefMasks_ok mdme_ok batchCodeF scatter_ok gather_ok
  eOne_ok countF_ok RowWr de0 mul_step)
open VG.Impl.Rsa.X86.Keys (seqs)

/-- The terms of a batch from byte `i` of the elements. -/
def tU (i : Nat) : Term := ⟨i, win + 12, sMu⟩
def tV (i : Nat) : Term := ⟨i + 4, win + 16, sMu + 4⟩
def tQ (i : Nat) : Term := ⟨i, win + 20, sMu + 8⟩
def tR (i : Nat) : Term := ⟨i + 4, win + 24, sMu + 12⟩
def tD : Term := ⟨16, sMd + 8, sMm⟩
def tE : Term := ⟨16, sMd + 12, sMm + 4⟩

/-- The masks of the matrix, then those of `md`, `me` too. -/
def ms4 (i : Nat) : List Term := [tU i, tV i, tQ i, tR i]
def ms6 (i : Nat) : List Term := ms4 i ++ [tD, tE]

variable {L : Lay} {B : Addr} {Z len N n : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}

local notation "T2" => fun _ : Reg → BitVec 32 => True ∧ True

/-- The runs between operations that keep the masks `ms`. -/
abbrev BM (L : Lay) (B : Addr) (Z len N n : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (C : Nat → Prop)
    (ms : List Term) (s t : State) : Prop :=
  Pre L B Z len N n args sp (ME B C ms) s ∧ Pre L B Z len N n args sp (ME B C ms) t

theorem relStartF {i : Nat} (hi : i + 8 ≤ fgSz) (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z)
    (h : Ok L (.block (startF L i))) :
    RelCT isa (Both L B Z len N n args sp C T2) (.block (startF L i)) (Both L B Z len N n args sp C T2) := by
  obtain ⟨_, h⟩ := h
  exact relOp (ws := [(win + 4, 24)]) (by decide) (stable_true _) (fun w hw => by
      simp only [List.mem_singleton] at hw; subst w; exact ⟨.inr (by decide), by simp only [win]; omega⟩)
    (fun s hb _ => WP.mono (startF_ok hb hi) fun _ ⟨H, _, K, O⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relCoefMasks {i : Nat} (h : Ok L (.block coefMasks)) :
    RelCT isa (Both L B Z len N n args sp C T2) (.block coefMasks) (BM L B Z len N n args sp C (ms4 i)) := by
  obtain ⟨_, h⟩ := h
  refine leafU (fun s ps => WP.mono (coefMasks_ok ps.1) fun u ⟨H, M, O, K⟩ => ?_) h
  have hn := ps.1.nowrap
  have hZ := ps.1.halfZ
  have hf := ps.1.fits16
  have eM : sMu = 160 := rfl; have e16 : win = 16 := rfl
  have co : ∀ j < 4, u.mem.readW (off B (win + 12 + 4 * j)) 32 = s.mem.readW (off B (win + 12 + 4 * j)) 32 :=
    fun j hj => BitVec.eq_of_toNat_eq (O.w32 (.inl (by omega)) (by omega))
  refine ⟨H, ps.2.1.keep K (by decide) (O.mono (Nat.zero_le _) (by omega)), ?_, fun t ht => ?_⟩
  · rw [O.w32 (.inl (by omega)) (by omega)]; exact ps.2.2.1
  · simp only [ms4, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · have := M 0 (by decide); have := co 0 (by decide); simp_all [tU]
    · have := M 1 (by decide); have := co 1 (by decide); simp_all [tV]
    · have := M 2 (by decide); have := co 2 (by decide); simp_all [tQ]
    · have := M 3 (by decide); have := co 3 (by decide); simp_all [tR]

theorem relMdme {i : Nat} (hi : i + 8 ≤ deSz) (h : Ok L (.block (mdme L i))) :
    RelCT isa (BM L B Z len N (nw len) args sp C (ms4 i)) (.block (mdme L i))
      (BM L B Z len N (nw len) args sp C (ms6 i)) := by
  obtain ⟨_, h⟩ := h
  refine leafU (fun s ps => WP.mono (mdme_ok ps.1 hi) fun u ⟨H, O, K, D⟩ => ?_) h
  have hn := ps.1.nowrap
  have hf := ps.1.fits16
  have eD : sMd = 184 := rfl; have eM : sMm = 200 := rfl; have eU : sMu = 160 := rfl; have e16 : win = 16 := rfl
  refine ⟨H, ps.2.1.keep K (by decide) (O.mono (Nat.zero_le _) (by omega)), ?_, fun t ht => ?_⟩
  · rw [O.w32 (.inl (by omega)) (by omega)]; exact ps.2.2.1
  · simp only [ms6, ms4, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    have keep4 : ∀ t ∈ ms4 i, u.mem.readW (off B t.m) 32 = maskW (u.mem.readW (off B t.c) 32) := by
      intro t ht
      have ht' := ps.2.2.2 t ht
      simp only [ms4, List.mem_cons, List.not_mem_nil, or_false] at ht
      have hc : t.c + 4 ≤ sMu + 16 ∧ t.m + 4 ≤ sMu + 16 := by
        rcases ht with rfl | rfl | rfl | rfl <;> simp only [tU, tV, tQ, tR, win, sMu] <;> omega
      rw [BitVec.eq_of_toNat_eq (O.w32 (d := t.m) (.inl (by omega)) (by omega)),
        BitVec.eq_of_toNat_eq (O.w32 (d := t.c) (.inl (by omega)) (by omega))]
      exact ht'
    rcases ht with (rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact keep4 _ (by simp [ms4])
    · exact keep4 _ (by simp [ms4])
    · exact keep4 _ (by simp [ms4])
    · exact keep4 _ (by simp [ms4])
    · exact D.mmd
    · exact D.mme

/-- A row writes its elements and the header's scratch words. -/
theorem RowWr.unch {A0 sz o n : Nat} {m m' : Mem} (h : RowWr B A0 sz o n m m') (ho : o + 4 ≤ sz) :
    Unch B [(A0, sz * (n + 2)), (sP, 8)] m m' := fun x hx => by
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  refine h x (fun j hj => ?_) h2
  have := mul_step (sz := sz) hj
  dsimp only at h1; omega

theorem relScatter {arr sz x : Nat} {src : Ref} (hx : x + 4 ≤ sz)
    (hfit : rv (kw len) { arr := arr } n + sz * (n + 2) < Z) (hA : sP + 8 ≤ rv (kw len) { arr := arr } n)
    (hsrc : rv (kw len) src n + 4 * (n + 1) ≤ Z)
    (sep : rv (kw len) src n + 4 * (n + 1) ≤ rv (kw len) { arr := arr } n + sz ∨
      rv (kw len) { arr := arr } n + sz + sz * (n + 1) ≤ rv (kw len) src n)
    (h : Ok L (scatter L arr sz x src)) :
    RelCT isa (Both L B Z len N n args sp C T2) (scatter L arr sz x src) (Both L B Z len N n args sp C T2) := by
  obtain ⟨_, h⟩ := h
  exact relOp (ws := [(rv (kw len) { arr := arr } n, sz * (n + 2)), (sP, 8)]) (by decide) (stable_true _)
    (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> simp only [sP] at * <;> omega)
    (fun s hb _ => WP.mono (scatter_ok hb hx hfit hA hsrc sep) fun _ ⟨H, R, _, K⟩ => ⟨H, K, RowWr.unch R hx, trivial⟩) h

theorem relGather {arr sz x : Nat} {dst : Ref} (hx : x + 4 ≤ sz)
    (hfit : rv (kw len) { arr := arr } n + sz * (n + 2) < Z)
    (hdst : rv (kw len) dst n + 4 * (n + 1) ≤ Z)
    (sep : rv (kw len) dst n + 4 * (n + 1) ≤ rv (kw len) { arr := arr } n + sz ∨
      rv (kw len) { arr := arr } n + sz + sz * (n + 1) ≤ rv (kw len) dst n)
    (h : Ok L (gather L arr sz x dst)) :
    RelCT isa (Both L B Z len N n args sp C T2) (gather L arr sz x dst) (Both L B Z len N n args sp C T2) := by
  obtain ⟨_, h⟩ := h
  exact relOp (by decide) (stable_true _) (ws1 (by have := rv_ge (kw len) dst n; omega) hdst)
    (fun s hb _ => WP.mono (gather_ok hb hx hfit hdst sep) fun _ ⟨H, O, _, K⟩ => ⟨H, K, O.unch, trivial⟩) h

/-- `e = 1`. -/
theorem relEOne (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z)
    (h : Ok L (.block (ptr L .eax { arr := deArr, byte := deSz } .edx ++ [.mov .ecx (.imm 1), .store (at_ .eax 4) .ecx]))) :
    RelCT isa (Both L B Z len N (nw len) args sp C T2)
      (.block (ptr L .eax { arr := deArr, byte := deSz } .edx ++ [.mov .ecx (.imm 1), .store (at_ .eax 4) .ecx]))
      (Both L B Z len N (nw len) args sp C T2) := by
  obtain ⟨_, h⟩ := h
  have ke := kw_eq len
  have r11 : de0 len = 160 + 11 * (4 * kw len + 8) + 20 := by simp only [de0, rv_arr]; rfl
  exact relOp (ws := [(de0 len + 4, 4)]) (by decide) (stable_true _) (ws1 (by omega) (by omega))
    (fun s hb _ => WP.mono (eOne_ok hb) fun t ⟨H, M, K⟩ => ⟨H, K, by
      rw [M]; exact (writeW32_outside _ _ _ (by have := hb.nowrap; omega)).unch, trivial⟩) h

/-- The count of double batches, `(3 n + 2) / 2`. -/
theorem relCountF (F : Fits Z len)
    (h : Ok L (.block (nBytes .eax 0 ++ ([.shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .ecx),
      .alu .add .eax (.reg .ecx), .alu .add .eax (.imm 2), .shift .shr .eax 1, .store (sc 100) .eax] : List Instr)))) :
    RelCT isa (Both L B Z len N (nw len) args sp C T2)
      (.block (nBytes .eax 0 ++ ([.shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .ecx),
        .alu .add .eax (.reg .ecx), .alu .add .eax (.imm 2), .shift .shr .eax 1, .store (sc 100) .eax] : List Instr)))
      (Both L B Z len N (nw len) args sp (· = (3 * nw len + 2) / 2) T2) := by
  obtain ⟨_, h⟩ := h
  have F4 := F.small
  refine leafU (fun s ps => WP.mono (countF_ok ps.1) fun t ⟨H, M, K⟩ => ?_) h
  have hn := ps.1.nowrap
  have hf := ps.1.fits16
  have O : Outside B 100 4 s.mem t.mem := by rw [M]; exact writeW32_outside _ _ _ (by omega)
  refine ⟨H, ps.2.1.keep K (by decide) (O.mono (Nat.zero_le _) (by omega)), ?_, trivial,
    trivial⟩
  show w32 t.mem B 100 = (3 * nw len + 2) / 2
  rw [M, w32_write_self, BitVec.toNat_ofNat]
  omega

/-! ## A batch -/

/-- The analysis's checks of a batch's parts. -/
structure BatchChecks (L : Lay) (i o : Nat) : Prop where
  start : Ok L (.block (startF L i))
  steps : Ok L (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30)
  masks : Ok L (.block coefMasks)
  r₁ : RowChecks L false fgArr fgSz o [tU i, tV i] [tU i, tV i]
  r₂ : RowChecks L false fgArr fgSz (o + 4) [tQ i, tR i] [tQ i, tR i]
  mdme : Ok L (.block (mdme L i))
  r₃ : RowChecks L true deArr deSz o [tU i, tV i, tD] [tU i, tV i]
  r₄ : RowChecks L true deArr deSz (o + 4) [tQ i, tR i, tE] [tQ i, tR i]

theorem relBatchCodeF (F : Fits Z len) {i o : Nat} (hio : i = 0 ∧ o = 8 ∨ i = 8 ∧ o = 0) (K : BatchChecks L i o) :
    RelCT isa (Both L B Z len N (nw len) args sp C T2) (batchCodeF L i o)
      (Both L B Z len N (nw len) args sp C T2) := by
  have F1 := F.fit; have F2 := F.two; have he := F.even
  have r4 : rv (kw len) { arr := fgArr } (nw len) = 160 + 4 * (8 * nw len + 8) := rv_a len 4
  have r11 : rv (kw len) { arr := deArr } (nw len) = 160 + 11 * (8 * nw len + 8) := rv_a len 11
  have hi : i ≤ 8 := by omega
  have ho : o ≤ 8 := by omega
  have eP : sP = 176 := rfl; have eU : sMu = 160 := rfl; have eD : sMd = 184 := rfl; have eM : sMm = 200 := rfl
  have e16 : win = 16 := rfl; have efs : fgSz = 16 := rfl; have eds : deSz = 20 := rfl
  have f2 : fgSz * (nw len + 2) = 16 * (nw len + 2) := rfl
  have d2 : deSz * (nw len + 2) = 20 * (nw len + 2) := rfl
  -- The rows' places.
  have hm4 : ∀ (arr : Nat), 208 ≤ rv (kw len) { arr := arr } (nw len) → ∀ t ∈ ms6 i,
      t.c + 4 ≤ rv (kw len) { arr := arr } (nw len) ∧ t.m + 4 ≤ rv (kw len) { arr := arr } (nw len) ∧
      (t.c + 4 ≤ sP ∨ sP + 8 ≤ t.c) ∧ (t.m + 4 ≤ sP ∨ sP + 8 ≤ t.m) := by
    intro arr ha t ht
    simp only [ms6, ms4, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with (rfl | rfl | rfl | rfl) | (rfl | rfl) <;> simp only [tU, tV, tQ, tR, tD, tE] <;> omega
  have hm4' : ∀ (arr : Nat), 208 ≤ rv (kw len) { arr := arr } (nw len) → ∀ t ∈ ms4 i,
      t.c + 4 ≤ rv (kw len) { arr := arr } (nw len) ∧ t.m + 4 ≤ rv (kw len) { arr := arr } (nw len) ∧
      (t.c + 4 ≤ sP ∨ sP + 8 ≤ t.c) ∧ (t.m + 4 ≤ sP ∨ sP + 8 ≤ t.m) :=
    fun arr ha t ht => hm4 arr ha t (List.mem_append_left _ ht)
  have m4 : ∀ t ∈ ms4 i, t ∈ ms6 i := fun t ht => List.mem_append_left _ ht
  have H₁ : RowHyp len Z (nw len) fgArr fgSz o [tU i, tV i] [tU i, tV i] (ms4 i) :=
    ⟨F2, he, .inl rfl, by omega, by omega, by omega, hm4' _ (by omega), fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact ⟨by simp [ms4], by simp only [tU, tV]; omega⟩, fun _ h => h⟩
  have H₂ : RowHyp len Z (nw len) fgArr fgSz (o + 4) [tQ i, tR i] [tQ i, tR i] (ms4 i) :=
    ⟨F2, he, .inl rfl, by omega, by omega, by omega, hm4' _ (by omega), fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact ⟨by simp [ms4], by simp only [tQ, tR]; omega⟩, fun _ h => h⟩
  have H₃ : RowHyp len Z (nw len) deArr deSz o [tU i, tV i, tD] [tU i, tV i] (ms6 i) :=
    ⟨F2, he, .inr rfl, by omega, by omega, by omega, hm4 _ (by omega), fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> exact ⟨by simp [ms6, ms4], by simp only [tU, tV, tD]; omega⟩,
      fun t ht => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
        rcases ht with rfl | rfl <;> simp⟩
  have H₄ : RowHyp len Z (nw len) deArr deSz (o + 4) [tQ i, tR i, tE] [tQ i, tR i] (ms6 i) :=
    ⟨F2, he, .inr rfl, by omega, by omega, by omega, hm4 _ (by omega), fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> exact ⟨by simp [ms6, ms4], by simp only [tQ, tR, tE]; omega⟩,
      fun t ht => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
        rcases ht with rfl | rfl <;> simp⟩
  have toBoth : ∀ {ms : List Term} s t, BM L B Z len N (nw len) args sp C ms s t →
      Both L B Z len N (nw len) args sp C T2 s t :=
    fun _ _ ⟨ps, pt⟩ => ⟨⟨ps.1, ps.2.1, ps.2.2.1, trivial, trivial⟩, ⟨pt.1, pt.2.1, pt.2.2.1, trivial, trivial⟩⟩
  have mono4 : ∀ s t, BM L B Z len N (nw len) args sp C (ms6 i) s t →
      BM L B Z len N (nw len) args sp C (ms6 i) s t := fun _ _ h => h
  unfold batchCodeF
  simp only [seqs]
  refine RelCT.seq (relStartF (by omega) F1 K.start) ?_
  refine RelCT.seq (relWordSteps (stable_true _) F1 (K.steps.choose_spec)) ?_
  refine RelCT.seq (relCoefMasks (i := i) K.masks) ?_
  refine RelCT.seq (relRow H₁ K.r₁) ?_
  refine RelCT.seq (relRow H₂ K.r₂) ?_
  refine RelCT.seq (relMdme (by omega) K.mdme) ?_
  refine RelCT.seq (relRow H₃ K.r₃) ?_
  exact (relRow H₄ K.r₄).mono (fun _ _ h => mono4 _ _ h) toBoth

end VG.Proof.Rsa.X86.InvBatchRt.Time
