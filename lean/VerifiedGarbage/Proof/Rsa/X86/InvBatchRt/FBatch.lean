module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FRows
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Weierstrass.X86.InvMatrix
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Divstep.Word32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Ring.Abs

/-! # The fused batches on i686: the window

`startF_ok`: the window's low words from element 0 of the interleaved `f, g` (at byte `i` of it),
and the identity matrix; `coefMasks_ok`, `mdme_ok`: the masks, `md` and `me`; `batchCodeF`: a
batch's code.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob wordState atWord)
open VG.Proof.Rsa.X86.InvBatchRt (rv Bx kw_eq rv_arr)
open VG.Impl.Rsa.X86.Keys (seqs)
open VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass.X86.Inv VG.Proof.Bignum.X86.R2Words

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- The start of a fused batch's code. -/
def startF (L : Lay) (i : Nat) : List Instr :=
  ptr L .ebx { arr := fgArr, byte := fgSz } .edx ++
    [.mov .eax (.mem (at_ .ebx i)), .store (sc (win + 4)) .eax, .mov .eax (.mem (at_ .ebx (i + 4))),
     .store (sc (win + 8)) .eax] ++ setConst 2 (win + 12) (1 + 2 ^ 96)

/-- The byte of element 0 of the interleaved `f, g`. -/
abbrev fg0 (len : Nat) : Nat := rv (kw len) { arr := fgArr, byte := fgSz }

theorem startF_ok {s : State} (h : Bx L s B Z len N) {i : Nat} (hi : i + 8 ≤ fgSz) :
    WP isa (.block (startF L i)) s fun u =>
      Bx L u B Z len N ∧
      wordState u.mem B win =
        ⟨s.mem.readW (off B win) 32, s.mem.readW (off B (fg0 len + i)) 32,
          s.mem.readW (off B (fg0 len + (i + 4))) 32, 1, 0, 0, 1⟩ ∧
      Keeps wordClob s u ∧ Outside B (win + 4) 24 s.mem u.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have e16 : win = 16 := rfl
  have efs : fgSz = 16 := rfl
  have r4 : fg0 len = 160 + 4 * (4 * kw len + 8) + 16 := by simp only [fg0, rv_arr]; rfl
  have ke := kw_eq len
  unfold startF
  simp only [List.append_assoc]
  refine ptr_ok h.ws h.slots hZ (r := .ebx) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    (by intro e; cases e) (by rw [← fg0, r4]; omega) fun s₁ K₁ m₁ p₁ => ?_
  rw [← fg0] at p₁
  simp only [List.cons_append, List.nil_append]
  have H₁ : Bx L s₁ B Z len N := h.keep K₁ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₁]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  refine wp_movS (readSrc_ptr H₁.ws.rt p₁ (d := i) (by omega)) fun s₂ U₂ _ => ?_
  have hs₂ := H₁.ws.ws.workspace.of_keeps U₂.keeps (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write (d := win + 4) (n := 4) (by omega)) fun s₃ U₃ => ?_
  have K₃ : Keeps [.eax, .ebx, .edx] s s₃ :=
    ((K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps _)
  have O₃ : Outside B (win + 4) 4 s.mem s₃.mem := by
    rw [U₃.mem, U₂.mem, m₁]; exact writeW32_outside _ _ _ (by omega)
  have H₃ : Bx L s₃ B Z len N := h.keepLow K₃ (by decide) (by decide) O₃ (by decide)
  have F₃ : w32 s₃.mem B (win + 4) = w32 s.mem B (fg0 len + i) := by
    rw [U₃.mem, w32_write_self, U₂.gpr, m₁]
  have p₃ : PtrAt s₃ B .ebx (fg0 len) := by
    rw [PtrAt, (U₃.keeps []).1 _ (by decide), U₂.other _ (by decide)]; exact p₁
  refine wp_movS (readSrc_ptr H₃.ws.rt p₃ (d := i + 4) (by omega)) fun s₅ U₅ _ => ?_
  have hs₅ := H₃.ws.ws.workspace.of_keeps U₅.keeps (by decide)
  refine wp_storeS (hs₅.ea (by omega)) (hs₅.write (d := win + 8) (n := 4) (by omega)) fun s₆ U₆ => ?_
  have K₆ : Keeps [.eax, .ebx, .edx] s₃ s₆ := (U₅.keeps.mono (by decide)).trans (U₆.keeps _)
  have O₆ : Outside B (win + 8) 4 s₃.mem s₆.mem := by
    rw [U₆.mem, U₅.mem]; exact writeW32_outside _ _ _ (by omega)
  have H₆ : Bx L s₆ B Z len N := H₃.keepLow K₆ (by decide) (by decide) O₆ (by decide)
  have G₆ : w32 s₆.mem B (win + 8) = w32 s.mem B (fg0 len + (i + 4)) := by
    rw [U₆.mem, w32_write_self, U₅.gpr, ← O₃.w32 (d := fg0 len + (i + 4)) (by omega) (by omega)]
  -- The identity matrix.
  refine WP.mono (VG.Proof.Weierstrass.X86.Inv.setMatrix_ok H₆.ws.ws.workspace (dst := win + 12) (by omega))
    fun u ⟨U, V, Q, R, K₇, O₇⟩ => ?_
  have H₇ : Bx L u B Z len N := H₆.keepLow K₇ (by decide) (by decide) O₇ (by decide)
  refine ⟨H₇, ?_, ((K₃.trans K₆).trans (K₇.mono (by decide))).mono (by decide), ?_⟩
  · have D : w32 u.mem B win = w32 s.mem B win := by
      rw [O₇.w32 (by omega) (by omega), O₆.w32 (by omega) (by omega), O₃.w32 (by omega) (by omega)]
    have F : w32 u.mem B (win + 4) = w32 s.mem B (fg0 len + i) := by
      rw [O₇.w32 (by omega) (by omega), O₆.w32 (by omega) (by omega), F₃]
    have G : w32 u.mem B (win + 8) = w32 s.mem B (fg0 len + (i + 4)) := by
      rw [O₇.w32 (by omega) (by omega), G₆]
    simp only [wordState, atWord, Divstep.W32.WSt.mk.injEq, Nat.reduceMul, Nat.add_zero]
    refine ⟨BitVec.eq_of_toNat_eq D, BitVec.eq_of_toNat_eq F, BitVec.eq_of_toNat_eq G,
      BitVec.eq_of_toNat_eq U, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem B (win + 16) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using V
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem B (win + 20) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using Q
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem B (win + 24) = 1
      simpa only [Nat.add_assoc, Nat.reduceAdd] using R
  · intro x hx
    rw [O₇ x (by omega), O₆ x (by omega), O₃ x (by omega)]

/-! ## The matrix's sign masks -/

theorem signMask (x : BitVec 32) :
    0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (2 ^ 32 ≤ x.toNat + x.toNat))) = maskW x := by
  unfold maskW
  by_cases h : 2 ^ 31 ≤ x.toNat
  · rw [decide_eq_true (by omega)]; simp only [h, ↓reduceIte]; simp
  · rw [decide_eq_false (by omega)]; simp only [h, ↓reduceIte]; simp

/-- One mask: `[dst] = mask [src]`. -/
theorem maskStep_ok {s : State} {W : Addr} {bytes src dst : Nat} (ws : Ws s W bytes) (di : PtrAt s W .edi 0)
    (hs : src + 4 ≤ bytes) (hd : dst + 4 ≤ bytes) :
    WP isa (.block (([.mov .eax (.mem (sc src))] : List Instr) ++ signEax ++ ([.store (sc dst) .eax] : List Instr))) s fun u =>
      u.mem = s.mem.writeW (off W dst) (maskW (s.mem.readW (off W src) 32)) ∧ Keeps [.eax] s u := by
  have nw := ws.nowrap
  obtain ⟨hdi, aS, rS⟩ := ptrRead ws di (d := src) (by omega)
  obtain ⟨-, aD, -⟩ := ptrRead ws di (d := dst) (by omega)
  simp only [Nat.zero_add] at aS rS aD
  have wD := ws_write ws hd
  refine WP.mono (WP.keeps [.eax] (Q := fun u =>
      u.mem = s.mem.writeW (off W dst) (maskW (s.mem.readW (off W src) 32))) ?_ rfl) fun u ⟨h, k⟩ => ⟨h, k⟩
  xrun [signEax, sc, hdi, aS, rS, aD, wD, List.cons_append, List.nil_append]
  rw [signMask]

theorem coefMasks_ok {s : State} (h : Bx L s B Z len N) :
    WP isa (.block coefMasks) s fun u =>
      Bx L u B Z len N ∧ (∀ j < 4, u.mem.readW (off B (sMu + 4 * j)) 32 = maskW (s.mem.readW (off B (win + 12 + 4 * j)) 32)) ∧
      Outside B sMu 16 s.mem u.mem ∧ Keeps [.eax] s u := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have scr := h.ws.ws.workspace
  have ws : Ws s B Z := ⟨scr.wr, scr.nowrap⟩
  have di : PtrAt s B .edi 0 := by rw [PtrAt, RtWs.edi_eq h.ws, BitVec.toNat_ofNat]; omega
  have e16 : win = 16 := rfl
  have eM : sMu = 160 := rfl
  have code : coefMasks = ([.mov .eax (.mem (sc (win + 12 + 4 * 0)))] ++ signEax ++ [.store (sc (sMu + 4 * 0)) .eax]) ++
      (([.mov .eax (.mem (sc (win + 12 + 4 * 1)))] ++ signEax ++ [.store (sc (sMu + 4 * 1)) .eax]) ++
      (([.mov .eax (.mem (sc (win + 12 + 4 * 2)))] ++ signEax ++ [.store (sc (sMu + 4 * 2)) .eax]) ++
      ([.mov .eax (.mem (sc (win + 12 + 4 * 3)))] ++ signEax ++ [.store (sc (sMu + 4 * 3)) .eax]))) := rfl
  rw [code, WP.block_append_iff]
  refine WP.mono (maskStep_ok ws di (by omega) (by omega)) fun u₁ ⟨m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have ws₁ := ws.of_keeps k₁
  have di₁ : PtrAt u₁ B .edi 0 := by rw [PtrAt, k₁.1 _ (by decide)]; exact di
  refine WP.mono (maskStep_ok ws₁ di₁ (by omega) (by omega)) fun u₂ ⟨m₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  have ws₂ := ws₁.of_keeps k₂
  have di₂ : PtrAt u₂ B .edi 0 := by rw [PtrAt, k₂.1 _ (by decide)]; exact di₁
  refine WP.mono (maskStep_ok ws₂ di₂ (by omega) (by omega)) fun u₃ ⟨m₃, k₃⟩ => ?_
  have ws₃ := ws₂.of_keeps k₃
  have di₃ : PtrAt u₃ B .edi 0 := by rw [PtrAt, k₃.1 _ (by decide)]; exact di₂
  refine WP.mono (maskStep_ok ws₃ di₃ (by omega) (by omega)) fun u ⟨m₄, k₄⟩ => ?_
  have K : Keeps [.eax] s u := ((k₁.trans k₂).trans k₃).trans k₄
  have O : Outside B sMu 16 s.mem u.mem := fun x hx => by
    rw [m₄, m₃, m₂, m₁]
    rw [writeW32_outside _ _ _ (by omega) x (by omega), writeW32_outside _ _ _ (by omega) x (by omega),
      writeW32_outside _ _ _ (by omega) x (by omega), writeW32_outside _ _ _ (by omega) x (by omega)]
  refine ⟨h.keep K (by decide) (by decide) O (by decide) (by omega), ?_, O, K⟩
  -- The masks, through the later stores.
  have src : ∀ k < 4, ∀ {m : Mem}, Outside B sMu 16 s.mem m →
      m.readW (off B (win + 12 + 4 * k)) 32 = s.mem.readW (off B (win + 12 + 4 * k)) 32 := fun k hk m hm =>
    BitVec.eq_of_toNat_eq (hm.w32 (.inl (by omega)) (by omega))
  have O₁ : Outside B sMu 16 s.mem u₁.mem := fun x hx => by
    rw [m₁, writeW32_outside _ _ _ (by omega) x (by omega)]
  have O₂ : Outside B sMu 16 s.mem u₂.mem := fun x hx => by
    rw [m₂, writeW32_outside _ _ _ (by omega) x (by omega), O₁ x hx]
  have O₃ : Outside B sMu 16 s.mem u₃.mem := fun x hx => by
    rw [m₃, writeW32_outside _ _ _ (by omega) x (by omega), O₂ x hx]
  have ne : ∀ {m : Mem} {d d' : Nat} (v : BitVec 32), d + 4 ≤ d' ∨ d' + 4 ≤ d → d + 4 ≤ Z → d' + 4 ≤ Z →
      (m.writeW (off B d') v).readW (off B d) 32 = m.readW (off B d) 32 := fun v hd h1 h2 =>
    BitVec.eq_of_toNat_eq (w32_write_ne (size := Z) hn h2 h1 hd v)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [m₄, ne _ (by omega) (by omega) (by omega), m₃, ne _ (by omega) (by omega) (by omega), m₂,
      ne _ (by omega) (by omega) (by omega), m₁, Mem.readW_writeW_self32]
  · rw [m₄, ne _ (by omega) (by omega) (by omega), m₃, ne _ (by omega) (by omega) (by omega), m₂,
      Mem.readW_writeW_self32, src 1 (by omega) O₁]
  · rw [m₄, ne _ (by omega) (by omega) (by omega), m₃, Mem.readW_writeW_self32, src 2 (by omega) O₂]
  · rw [m₄, Mem.readW_writeW_self32, src 3 (by omega) O₃]

/-! ## `md`, `me` -/

/-- The word `mdme` computes for one row: `md₀ - ((md₀ - np cd) mod 2^30)`. -/
def mdWord (U V SD SE D0 E0 NP : BitVec 32) : BitVec 32 :=
  let md0 := (U &&& SD) + (V &&& SE)
  md0 - ((md0 - NP * (U * D0 + V * E0)) &&& 0x3FFFFFFF#32)

theorem mulOf (a b : BitVec 32) : BitVec.ofNat 32 (a.toNat * b.toNat) = a * b :=
  BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_mul])

/-- One row's `md`. -/
theorem mdStep_ok {s : State} {W : Addr} {bytes cu cv dst : Nat} (ws : Ws s W bytes) (di : PtrAt s W .edi 0)
    (hu : cu + 4 ≤ bytes) (hv : cv + 4 ≤ bytes) (hd : dst + 4 ≤ bytes) (hm : sMd + 8 ≤ bytes)
    (hi : win + 32 ≤ bytes) :
    WP isa (.block [.mov .esi (.mem (sc cu)), .alu .and .esi (.mem (sc sMd)), .mov .eax (.mem (sc cv)),
     .alu .and .eax (.mem (sc (sMd + 4))), .alu .add .esi (.reg .eax),
     .mov .eax (.mem (sc cu)), .mul .ebx, .mov .ebp (.reg .eax), .mov .eax (.mem (sc cv)), .mul .ecx,
     .alu .add .ebp (.reg .eax),
     .mov .eax (.mem (sc (win + 28))), .mul .ebp, .mov .edx (.reg .esi), .alu .sub .edx (.reg .eax),
     .alu .and .edx (.imm 0x3FFFFFFF), .alu .sub .esi (.reg .edx),
     .store (sc dst) .esi]) s fun u =>
      u.mem = s.mem.writeW (off W dst) (mdWord (s.mem.readW (off W cu) 32) (s.mem.readW (off W cv) 32)
        (s.mem.readW (off W sMd) 32) (s.mem.readW (off W (sMd + 4)) 32) (s.gpr .ebx) (s.gpr .ecx)
        (s.mem.readW (off W (win + 28)) 32)) ∧ Keeps [.eax, .edx, .ebp, .esi] s u := by
  have nw := ws.nowrap
  obtain ⟨hdi, aU, rU⟩ := ptrRead ws di (d := cu) (by omega)
  obtain ⟨-, aV, rV⟩ := ptrRead ws di (d := cv) (by omega)
  obtain ⟨-, aS, rS⟩ := ptrRead ws di (d := sMd) (by unfold sMd at *; omega)
  obtain ⟨-, aT, rT⟩ := ptrRead ws di (d := sMd + 4) (by unfold sMd at *; omega)
  obtain ⟨-, aI, rI⟩ := ptrRead ws di (d := win + 28) (by omega)
  obtain ⟨-, aD, -⟩ := ptrRead ws di (d := dst) (by omega)
  simp only [Nat.zero_add] at aU rU aV rV aS rS aT rT aI rI aD
  have wD := ws_write ws hd
  refine WP.mono (WP.keeps [.eax, .edx, .ebp, .esi] (Q := fun u =>
      u.mem = s.mem.writeW (off W dst) (mdWord (s.mem.readW (off W cu) 32) (s.mem.readW (off W cv) 32)
        (s.mem.readW (off W sMd) 32) (s.mem.readW (off W (sMd + 4)) 32) (s.gpr .ebx) (s.gpr .ecx)
        (s.mem.readW (off W (win + 28)) 32))) ?_ rfl) fun u ⟨h, k⟩ => ⟨h, k⟩
  xrun [sc, execMul, hdi, aU, rU, aV, rV, aS, rS, aT, rT, aI, rI, aD, wD]
  simp only [mulOf]
  rfl

/-- `mdme`'s loads: `d`, `e`'s low words at byte `dx` of element 0, and `esi` on to element `n`. -/
theorem loadsDE_ok {u : State} {W : Addr} {bytes e dx n : Nat} (ws : Ws u W bytes) (di : PtrAt u W .edi 0)
    (si : PtrAt u W .esi e) (hh : u.mem.readW (off W halfSlot) 32 = BitVec.ofNat 32 (4 * n))
    (hhb : halfSlot + 4 ≤ bytes) (hx : e + dx + 8 ≤ bytes) :
    WP isa (.block [.mov .ebx (.mem (at_ .esi dx)), .mov .ecx (.mem (at_ .esi (dx + 4))),
      .mov .eax (.mem (sc halfSlot)), .mov .edx (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .edx), .alu .add .esi (.reg .eax)]) u fun v =>
      v.gpr .ebx = u.mem.readW (off W (e + dx)) 32 ∧ v.gpr .ecx = u.mem.readW (off W (e + (dx + 4))) 32 ∧
      PtrAt v W .esi (e + 20 * n) ∧ v.mem = u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] u v := by
  have nw := ws.nowrap
  obtain ⟨hsi, a1, r1⟩ := ptrRead ws si (d := dx) (by omega)
  obtain ⟨-, a2, r2⟩ := ptrRead ws si (d := dx + 4) (by omega)
  obtain ⟨hdi, aH, rH⟩ := ptrRead ws di (d := halfSlot) (by omega)
  simp only [Nat.zero_add] at aH rH
  refine WP.mono (WP.keeps [.eax, .ebx, .ecx, .edx, .esi] (Q := fun v =>
      v.gpr .ebx = u.mem.readW (off W (e + dx)) 32 ∧ v.gpr .ecx = u.mem.readW (off W (e + (dx + 4))) 32 ∧
      (v.gpr .esi).toNat = (W.toNat + (e + 20 * n)) % 2 ^ 32 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h1, h2, h3, h4⟩, k⟩ => ⟨h1, h2, h3, h4, k⟩
  xrun [sc, hsi, a1, r1, a2, r2, hdi, aH, rH, hh]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A mask through `esi`: `[dst] = mask [esi + d]`. -/
theorem maskStepR_ok {s : State} {W : Addr} {bytes e d dst : Nat} (ws : Ws s W bytes) (di : PtrAt s W .edi 0)
    (si : PtrAt s W .esi e) (hs : e + d + 4 ≤ bytes) (hd : dst + 4 ≤ bytes) :
    WP isa (.block (([.mov .eax (.mem (at_ .esi d))] : List Instr) ++ signEax ++ ([.store (sc dst) .eax] : List Instr))) s fun u =>
      u.mem = s.mem.writeW (off W dst) (maskW (s.mem.readW (off W (e + d)) 32)) ∧ Keeps [.eax] s u := by
  have nw := ws.nowrap
  obtain ⟨hsi, aS, rS⟩ := ptrRead ws si (d := d) (by omega)
  obtain ⟨hdi, aD, -⟩ := ptrRead ws di (d := dst) (by omega)
  simp only [Nat.zero_add] at aD
  have wD := ws_write ws hd
  refine WP.mono (WP.keeps [.eax] (Q := fun u =>
      u.mem = s.mem.writeW (off W dst) (maskW (s.mem.readW (off W (e + d)) 32))) ?_ rfl) fun u ⟨h, k⟩ => ⟨h, k⟩
  xrun [signEax, sc, hsi, hdi, aS, rS, aD, wD, List.cons_append, List.nil_append]
  rw [signMask]

/-- What `mdme` leaves in the header, from `d`, `e` at byte `dx` of the elements from `de0`
(`n + 1` of them) and the matrix in `m₀`. -/
structure MdmeAt (m₀ m : Mem) (B : Addr) (de0 n dx : Nat) : Prop where
  sd : m.readW (off B sMd) 32 = maskW (m₀.readW (off B (de0 + 20 * n + dx)) 32)
  se : m.readW (off B (sMd + 4)) 32 = maskW (m₀.readW (off B (de0 + 20 * n + (dx + 4))) 32)
  md : m.readW (off B (sMd + 8)) 32 = mdWord (m₀.readW (off B (win + 12)) 32) (m₀.readW (off B (win + 16)) 32)
    (maskW (m₀.readW (off B (de0 + 20 * n + dx)) 32)) (maskW (m₀.readW (off B (de0 + 20 * n + (dx + 4))) 32))
    (m₀.readW (off B (de0 + dx)) 32) (m₀.readW (off B (de0 + (dx + 4))) 32) (m₀.readW (off B (win + 28)) 32)
  me : m.readW (off B (sMd + 12)) 32 = mdWord (m₀.readW (off B (win + 20)) 32) (m₀.readW (off B (win + 24)) 32)
    (maskW (m₀.readW (off B (de0 + 20 * n + dx)) 32)) (maskW (m₀.readW (off B (de0 + 20 * n + (dx + 4))) 32))
    (m₀.readW (off B (de0 + dx)) 32) (m₀.readW (off B (de0 + (dx + 4))) 32) (m₀.readW (off B (win + 28)) 32)
  mmd : m.readW (off B sMm) 32 = maskW (m.readW (off B (sMd + 8)) 32)
  mme : m.readW (off B (sMm + 4)) 32 = maskW (m.readW (off B (sMd + 12)) 32)

/-- The byte of element 0 of the interleaved `d, e, p`. -/
abbrev de0 (len : Nat) : Nat := rv (kw len) { arr := deArr, byte := deSz }

theorem mdme_code (L : Lay) (dx : Nat) : mdme L dx = ptr L .esi { arr := deArr, byte := deSz } .edx ++
    ([.mov .ebx (.mem (at_ .esi dx)), .mov .ecx (.mem (at_ .esi (dx + 4))),
      .mov .eax (.mem (sc halfSlot)), .mov .edx (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .edx), .alu .add .esi (.reg .eax)] ++
    (([.mov .eax (.mem (at_ .esi dx))] ++ signEax ++ [.store (sc sMd) .eax]) ++
    (([.mov .eax (.mem (at_ .esi (dx + 4)))] ++ signEax ++ [.store (sc (sMd + 4)) .eax]) ++
    ([.mov .esi (.mem (sc (win + 12 + 8 * 0))), .alu .and .esi (.mem (sc sMd)), .mov .eax (.mem (sc (win + 16 + 8 * 0))),
      .alu .and .eax (.mem (sc (sMd + 4))), .alu .add .esi (.reg .eax),
      .mov .eax (.mem (sc (win + 12 + 8 * 0))), .mul .ebx, .mov .ebp (.reg .eax), .mov .eax (.mem (sc (win + 16 + 8 * 0))),
      .mul .ecx, .alu .add .ebp (.reg .eax),
      .mov .eax (.mem (sc (win + 28))), .mul .ebp, .mov .edx (.reg .esi), .alu .sub .edx (.reg .eax),
      .alu .and .edx (.imm 0x3FFFFFFF), .alu .sub .esi (.reg .edx), .store (sc (sMd + 8 + 4 * 0)) .esi] ++
    ([.mov .esi (.mem (sc (win + 12 + 8 * 1))), .alu .and .esi (.mem (sc sMd)), .mov .eax (.mem (sc (win + 16 + 8 * 1))),
      .alu .and .eax (.mem (sc (sMd + 4))), .alu .add .esi (.reg .eax),
      .mov .eax (.mem (sc (win + 12 + 8 * 1))), .mul .ebx, .mov .ebp (.reg .eax), .mov .eax (.mem (sc (win + 16 + 8 * 1))),
      .mul .ecx, .alu .add .ebp (.reg .eax),
      .mov .eax (.mem (sc (win + 28))), .mul .ebp, .mov .edx (.reg .esi), .alu .sub .edx (.reg .eax),
      .alu .and .edx (.imm 0x3FFFFFFF), .alu .sub .esi (.reg .edx), .store (sc (sMd + 8 + 4 * 1)) .esi] ++
    (([.mov .eax (.mem (sc (sMd + 8)))] ++ signEax ++ [.store (sc sMm) .eax]) ++
    (([.mov .eax (.mem (sc (sMd + 12)))] ++ signEax ++ [.store (sc (sMm + 4)) .eax]) ++ restoreEdi L))))))) := by
  rfl

theorem mdme_ok {s : State} (h : Bx L s B Z len N) {dx : Nat} (hdx : dx + 8 ≤ deSz) :
    WP isa (.block (mdme L dx)) s fun t =>
      Bx L t B Z len N ∧ Outside B sMd 24 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      MdmeAt s.mem t.mem B (de0 len) (nw len) dx := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have ke := kw_eq len
  have e16 : win = 16 := rfl; have eD : sMd = 184 := rfl; have eM : sMm = 200 := rfl
  have eds : deSz = 20 := rfl; have eH : halfSlot = 96 := rfl
  have r11 : de0 len = 160 + 11 * (4 * kw len + 8) + 20 := by simp only [de0, rv_arr]; rfl
  have scr := h.ws.ws.workspace
  have ws : Ws s B Z := ⟨scr.wr, scr.nowrap⟩
  have di : PtrAt s B .edi 0 := by rw [PtrAt, RtWs.edi_eq h.ws, BitVec.toNat_ofNat]; omega
  rw [mdme_code]
  refine ptr_ok h.ws h.slots hZ (r := .esi) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    (by intro e; cases e) (by rw [← de0, r11]; omega) fun u K₁ m₁ p₁ => ?_
  rw [← de0] at p₁
  have wsu := ws.of_keeps K₁
  have diu : PtrAt u B .edi 0 := by rw [PtrAt, K₁.1 _ (by decide)]; exact di
  have hh : u.mem.readW (off B halfSlot) 32 = BitVec.ofNat 32 (4 * nw len) := by
    rw [m₁, h.slots.halfW]; congr 1; omega
  rw [WP.block_append_iff]
  refine WP.mono (loadsDE_ok (n := nw len) wsu diu p₁ hh (by omega) (by omega)) fun u₂ ⟨b₂, c₂, p₂, m₂, K₂⟩ => ?_
  have ws₂ := wsu.of_keeps K₂
  have di₂ : PtrAt u₂ B .edi 0 := by rw [PtrAt, K₂.1 _ (by decide)]; exact diu
  rw [WP.block_append_iff]
  refine WP.mono (maskStepR_ok ws₂ di₂ p₂ (d := dx) (dst := sMd) (by omega) (by omega)) fun u₃ ⟨m₃, K₃⟩ => ?_
  have ws₃ := ws₂.of_keeps K₃
  have di₃ : PtrAt u₃ B .edi 0 := by rw [PtrAt, K₃.1 _ (by decide)]; exact di₂
  have p₃ : PtrAt u₃ B .esi (de0 len + 20 * nw len) := by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂
  rw [WP.block_append_iff]
  refine WP.mono (maskStepR_ok ws₃ di₃ p₃ (d := dx + 4) (dst := sMd + 4) (by omega) (by omega))
    fun u₄ ⟨m₄, K₄⟩ => ?_
  have ws₄ := ws₃.of_keeps K₄
  have di₄ : PtrAt u₄ B .edi 0 := by rw [PtrAt, K₄.1 _ (by decide)]; exact di₃
  rw [WP.block_append_iff]
  refine WP.mono (mdStep_ok ws₄ di₄ (cu := win + 12 + 8 * 0) (cv := win + 16 + 8 * 0) (dst := sMd + 8 + 4 * 0)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun u₅ ⟨m₅, K₅⟩ => ?_
  have ws₅ := ws₄.of_keeps K₅
  have di₅ : PtrAt u₅ B .edi 0 := by rw [PtrAt, K₅.1 _ (by decide)]; exact di₄
  rw [WP.block_append_iff]
  refine WP.mono (mdStep_ok ws₅ di₅ (cu := win + 12 + 8 * 1) (cv := win + 16 + 8 * 1) (dst := sMd + 8 + 4 * 1)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun u₆ ⟨m₆, K₆⟩ => ?_
  have ws₆ := ws₅.of_keeps K₆
  have di₆ : PtrAt u₆ B .edi 0 := by rw [PtrAt, K₆.1 _ (by decide)]; exact di₅
  rw [WP.block_append_iff]
  refine WP.mono (maskStep_ok ws₆ di₆ (src := sMd + 8) (dst := sMm) (by omega) (by omega)) fun u₇ ⟨m₇, K₇⟩ => ?_
  have ws₇ := ws₆.of_keeps K₇
  have di₇ : PtrAt u₇ B .edi 0 := by rw [PtrAt, K₇.1 _ (by decide)]; exact di₆
  rw [WP.block_append_iff]
  refine WP.mono (maskStep_ok ws₇ di₇ (src := sMd + 12) (dst := sMm + 4) (by omega) (by omega))
    fun w ⟨m₈, K₈⟩ => ?_
  -- The frame.
  have O : Outside B sMd 24 s.mem w.mem := fun x hx => by
    rw [m₈, writeW32_outside _ _ _ (by omega) x (by omega), m₇, writeW32_outside _ _ _ (by omega) x (by omega),
      m₆, writeW32_outside _ _ _ (by omega) x (by omega), m₅, writeW32_outside _ _ _ (by omega) x (by omega),
      m₄, writeW32_outside _ _ _ (by omega) x (by omega), m₃, writeW32_outside _ _ _ (by omega) x (by omega),
      m₂, m₁]
  have KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s w := by
    refine (K₁.mono (by decide)).trans ((K₂.mono (by decide)).trans ((K₃.mono (by decide)).trans
      ((K₄.mono (by decide)).trans ((K₅.mono (by decide)).trans ((K₆.mono (by decide)).trans
      ((K₇.mono (by decide)).trans (K₈.mono (by decide))))))))
  have O0 : Outside B 0 Z s.mem w.mem := O.mono (Nat.zero_le _) (by omega)
  unfold restoreEdi
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  have K' : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi])
      ((KK.mono (by decide)).trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h.ws).symm)
  have O' : Outside B sMd 24 s.mem t₁.mem := by rw [U.mem]; exact O
  refine ⟨h.keep K' (by decide) (by decide) O' (by omega) (by omega), O', K', ?_⟩
  -- The values.
  have ne : ∀ {m : Mem} {d d' : Nat} (v : BitVec 32), d + 4 ≤ d' ∨ d' + 4 ≤ d → d + 4 ≤ Z → d' + 4 ≤ Z →
      (m.writeW (off B d') v).readW (off B d) 32 = m.readW (off B d) 32 := fun v hd h1 h2 =>
    BitVec.eq_of_toNat_eq (w32_write_ne (size := Z) hn h2 h1 hd v)
  rw [U.mem]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at m₅ m₆
  rw [show sMd + 8 + 4 = sMd + 12 from rfl, show win + 12 + 8 = win + 20 from rfl,
    show win + 16 + 8 = win + 24 from rfl] at m₆
  -- `ebx`, `ecx` at the `md` steps: `d`, `e`'s low words.
  have eb₄ : u₄.gpr .ebx = s.mem.readW (off B (de0 len + dx)) 32 := by
    rw [K₄.1 _ (by decide), K₃.1 _ (by decide), b₂, m₁]
  have ec₄ : u₄.gpr .ecx = s.mem.readW (off B (de0 len + (dx + 4))) 32 := by
    rw [K₄.1 _ (by decide), K₃.1 _ (by decide), c₂, m₁]
  have eb₅ : u₅.gpr .ebx = u₄.gpr .ebx := K₅.1 _ (by decide)
  have ec₅ : u₅.gpr .ecx = u₄.gpr .ecx := K₅.1 _ (by decide)
  -- Reads of what the steps do not write.
  have O₄ : Outside B sMd 24 s.mem u₄.mem := fun x hx => by
    rw [m₄, writeW32_outside _ _ _ (by omega) x (by omega), m₃, writeW32_outside _ _ _ (by omega) x (by omega), m₂, m₁]
  have O₅ : Outside B sMd 24 s.mem u₅.mem := fun x hx => by
    rw [m₅, writeW32_outside _ _ _ (by omega) x (by omega), O₄ x hx]
  have rd : ∀ {m : Mem}, Outside B sMd 24 s.mem m → ∀ d, d + 4 ≤ sMd ∨ sMd + 24 ≤ d → d + 4 ≤ Z →
      m.readW (off B d) 32 = s.mem.readW (off B d) 32 := fun hm d hd hdz =>
    BitVec.eq_of_toNat_eq (hm.w32 hd (by omega))
  have sd₄ : u₄.mem.readW (off B sMd) 32 = maskW (s.mem.readW (off B (de0 len + 20 * nw len + dx)) 32) := by
    rw [m₄, ne _ (by omega) (by omega) (by omega), m₃, Mem.readW_writeW_self32, m₂, m₁]
  have se₄ : u₄.mem.readW (off B (sMd + 4)) 32 =
      maskW (s.mem.readW (off B (de0 len + 20 * nw len + (dx + 4))) 32) := by
    rw [m₄, Mem.readW_writeW_self32, m₃, ne _ (by omega) (by omega) (by omega), m₂, m₁]
  have md₅ : u₅.mem.readW (off B (sMd + 8)) 32 = mdWord (s.mem.readW (off B (win + 12)) 32) (s.mem.readW (off B (win + 16)) 32)
      (maskW (s.mem.readW (off B (de0 len + 20 * nw len + dx)) 32))
      (maskW (s.mem.readW (off B (de0 len + 20 * nw len + (dx + 4))) 32))
      (s.mem.readW (off B (de0 len + dx)) 32) (s.mem.readW (off B (de0 len + (dx + 4))) 32)
      (s.mem.readW (off B (win + 28)) 32) := by
    rw [m₅, Mem.readW_writeW_self32, sd₄, se₄, eb₄, ec₄, rd O₄ _ (by omega) (by omega), rd O₄ _ (by omega) (by omega),
      rd O₄ (win + 28) (by omega) (by omega)]
  have me₆ : u₆.mem.readW (off B (sMd + 12)) 32 = mdWord (s.mem.readW (off B (win + 20)) 32) (s.mem.readW (off B (win + 24)) 32)
      (maskW (s.mem.readW (off B (de0 len + 20 * nw len + dx)) 32))
      (maskW (s.mem.readW (off B (de0 len + 20 * nw len + (dx + 4))) 32))
      (s.mem.readW (off B (de0 len + dx)) 32) (s.mem.readW (off B (de0 len + (dx + 4))) 32)
      (s.mem.readW (off B (win + 28)) 32) := by
    have sd₅ : u₅.mem.readW (off B sMd) 32 = u₄.mem.readW (off B sMd) 32 := by
      rw [m₅, ne _ (by omega) (by omega) (by omega)]
    have se₅ : u₅.mem.readW (off B (sMd + 4)) 32 = u₄.mem.readW (off B (sMd + 4)) 32 := by
      rw [m₅, ne _ (by omega) (by omega) (by omega)]
    rw [m₆, Mem.readW_writeW_self32, sd₅, se₅, sd₄, se₄, eb₅, ec₅, eb₄, ec₄, rd O₅ (win + 20) (by omega) (by omega),
      rd O₅ (win + 24) (by omega) (by omega), rd O₅ (win + 28) (by omega) (by omega)]
  have md₆ : u₆.mem.readW (off B (sMd + 8)) 32 = u₅.mem.readW (off B (sMd + 8)) 32 := by
    rw [m₆, ne _ (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₈, ne _ (by omega) (by omega) (by omega), m₇, ne _ (by omega) (by omega) (by omega), m₆,
      ne _ (by omega) (by omega) (by omega), m₅, ne _ (by omega) (by omega) (by omega), sd₄]
  · rw [m₈, ne _ (by omega) (by omega) (by omega), m₇, ne _ (by omega) (by omega) (by omega), m₆,
      ne _ (by omega) (by omega) (by omega), m₅, ne _ (by omega) (by omega) (by omega), se₄]
  · rw [m₈, ne _ (by omega) (by omega) (by omega), m₇, ne _ (by omega) (by omega) (by omega), md₆, md₅]
  · rw [m₈, ne _ (by omega) (by omega) (by omega), m₇, ne _ (by omega) (by omega) (by omega), me₆]
  · rw [m₈, ne (d := sMm) (d' := sMm + 4) _ (by omega) (by omega) (by omega),
      ne (d := sMd + 8) (d' := sMm + 4) _ (by omega) (by omega) (by omega), m₇, Mem.readW_writeW_self32,
      ne (d := sMd + 8) (d' := sMm) _ (by omega) (by omega) (by omega)]
  · rw [m₈, Mem.readW_writeW_self32, ne (d := sMd + 12) (d' := sMm + 4) _ (by omega) (by omega) (by omega)]

/-! ## A batch's code -/

/-- The batch's code, for the half at byte `i` to the one at byte `o`. -/
def batchCodeF (L : Lay) (i o : Nat) : Prog isa :=
  let u : Term := ⟨i, win + 12, sMu⟩
  let v : Term := ⟨i + 4, win + 16, sMu + 4⟩
  let q : Term := ⟨i, win + 20, sMu + 8⟩
  let r : Term := ⟨i + 4, win + 24, sMu + 12⟩
  seqs [.block (startF L i), VG.Impl.Weierstrass.X86.Inv.wordSteps win 30, .block coefMasks,
    row L false fgArr fgSz o [u, v] [u, v], row L false fgArr fgSz (o + 4) [q, r] [q, r],
    .block (mdme L i),
    row L true deArr deSz o [u, v, ⟨16, sMd + 8, sMm⟩] [u, v],
    row L true deArr deSz (o + 4) [q, r, ⟨16, sMd + 12, sMm + 4⟩] [q, r]]

theorem batchF_eq (L : Lay) (h : Bool) :
    batchF L h = batchCodeF L (if h then 0 else 8) (if h then 8 else 0) := by
  cases h <;> rfl

end VG.Proof.Rsa.X86.InvBatchRt.F
