module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega

/-! # `redSum`'s parts, each in both runs

`redSum` reads the slots after its row's stores, so its start, its row and its end are checked one
at a time; their frames are `redSum_ok`'s steps.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)

variable {L : Lay} {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}
  {G : (Reg → BitVec 32) → Prop}

theorem redHead_frame {s : State} (h : Bx L s B Z len N) {acc : Ref} (hah : acc.half = 0) (hab : acc.byte = 0)
    (haz : rv (kw len) acc + 4 * (nw len + 2) ≤ Z) :
    WP isa (.block (redHead L acc)) s fun t => Bx L t B Z len N ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t ∧
      Unch B [(rv (kw len) acc + 4 * (nw len + 1), 4), (signSlot, 4)] s.mem t.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have ke := kw_eq len
  have ra := rv_ge (kw len) acc
  have e48 : signSlot = 48 := rfl
  have e16 : win = 16 := rfl
  have r1 : rv (kw len) { acc with half := 1 } = rv (kw len) acc + 4 * nw len := by
    have := rv_half (kw len) acc hah 0; simp only [hab, Nat.add_zero] at this ⊢; rw [this]; omega
  have r2 : rv (kw len) { acc with half := 1, byte := 4 } = rv (kw len) acc + 4 * (nw len + 1) := by
    have := rv_half (kw len) acc hah 4; simp only [hab, Nat.zero_add] at this; rw [this]; omega
  simp only [redHead, List.append_assoc]
  refine maskAt_ok h (x := { acc with half := 1 }) (by rw [r1]; omega) fun u₁ K₁ m₁ _ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun s₂ U₂ _ => ?_
  have K₂ : Keeps [.eax, .ebx, .ecx, .edx, .esi] s s₂ := (K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have m₂ : s₂.mem = s.mem := by rw [U₂.mem, m₁]
  have h₂ : Bx L s₂ B Z len N := h.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _) ra haz
  refine zeroWord_ok h₂ (x := { acc with half := 1, byte := 4 }) (by rw [r2]; omega) fun s₃ h₃ K₃ O₃ _ => ?_
  rw [r2] at O₃
  refine ptr_ok h₃.ws h₃.slots hZ (r := .ebx) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    (by intro e; cases e) (by omega) fun s₄ K₄ m₄ p₄ => ?_
  have h₄ : Bx L s₄ B Z len N := h₃.keep K₄ (by decide) (by decide) (by rw [m₄]; exact Outside.refl _ _ _ _) ra haz
  refine wp_movS (readSrc_ptr (h₄.ws.rt) p₄ (d := 0) (by omega)) fun s₅ U₅ _ => ?_
  have hs₅ := h₄.ws.ws.workspace.of_keeps U₅.keeps (by decide)
  refine wp_movS (readSrc_sc hs₅ (d := win + 28) (by omega)) fun s₆ U₆ _ => ?_
  refine wp_mul fun s₇ U₇ => ?_
  refine wp_movS rfl fun s₈ U₈ _ => ?_
  have K₈ : Keeps [.eax, .ecx, .edx] s₄ s₈ :=
    (((U₅.keeps.mono (by decide)).trans (U₆.keeps.mono (by decide))).trans (U₇.keeps.mono (by decide))).trans
      (U₈.keeps.mono (by decide))
  have m₈ : s₈.mem = s₄.mem := by rw [U₈.mem, U₇.mem, U₆.mem, U₅.mem]
  have hs₈ := h₄.ws.ws.workspace.of_keeps K₈ (by decide)
  refine wp_storeS (hs₈.ea (by omega)) (hs₈.write (d := signSlot) (n := 4) (by omega)) fun s₉ U₉ => WP.block_nil ?_
  have K₉ : Keeps [.eax, .ecx, .edx] s₄ s₉ := K₈.trans (U₉.keeps _)
  have O₉ : Outside B signSlot 4 s₄.mem s₉.mem := by
    rw [U₉.mem, m₈]; exact writeW32_outside _ _ _ (by omega)
  refine ⟨h₄.keepLow K₉ (by decide) (by decide) O₉ (by decide), ?_, ?_⟩
  · exact (((K₂.mono (by decide)).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans
      (K₉.mono (by decide))
  · intro x hx
    rw [O₉ x (hx (signSlot, 4) (by simp)), m₄, O₃ x (hx _ (List.mem_cons_self ..)), m₂]

theorem redTail_frame {s : State} (h : Bx L s B Z len N) {acc : Ref} (hah : acc.half = 0) (hab : acc.byte = 0)
    (haz : rv (kw len) acc + 4 * (nw len + 2) ≤ Z) :
    WP isa (.block (redTail L acc)) s fun t => Bx L t B Z len N ∧ Keeps [.eax, .ebx, .edx] s t ∧
      Unch B [(rv (kw len) acc + 4 * (nw len + 1), 4)] s.mem t.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have ke := kw_eq len
  have ra := rv_ge (kw len) acc
  have e48 : signSlot = 48 := rfl
  have r2 : rv (kw len) { acc with half := 1, byte := 4 } = rv (kw len) acc + 4 * (nw len + 1) := by
    have := rv_half (kw len) acc hah 4; simp only [hab, Nat.zero_add] at this; rw [this]; omega
  simp only [redTail]
  refine ptr_ok h.ws h.slots hZ (r := .ebx) (t := .edx) (x := { acc with half := 1, byte := 4 }) (by decide)
    (by decide) (by decide) (by decide) (by intro e; cases e) (by rw [r2]; omega) fun t₁ K₁' m₁' p₁' => ?_
  rw [r2] at p₁'
  have hw₁ := h.ws.rt.of_keeps K₁'
  refine wp_movS (readSrc_ptr hw₁ p₁' (d := 0) (by omega)) fun t₂ V₂ _ => ?_
  have hs₂' := (h.ws.ws.workspace.of_keeps K₁' (by decide)).of_keeps V₂.keeps (by decide)
  refine wp_addS (readSrc_sc hs₂' (d := signSlot) (by omega)) fun t₃ V₃ _ => ?_
  have hw₃ := (hw₁.of_keeps V₂.keeps).of_keeps V₃.keeps
  have p₃ : PtrAt t₃ B .ebx (rv (kw len) acc + 4 * (nw len + 1)) := by
    rw [PtrAt, V₃.other _ (by decide), V₂.other _ (by decide)]; exact p₁'
  have ea : t₃.ea (at_ .ebx 0) = off B (rv (kw len) acc + 4 * (nw len + 1)) := by
    simpa using ea_ptr hw₃ p₃ (d := 0) (by omega)
  refine wp_storeS ea (ws_write hw₃ (by omega)) fun z Uz => WP.block_nil ?_
  have Kz : Keeps [.eax, .ebx, .edx] s z :=
    ((K₁'.mono (by decide)).trans (V₂.keeps.mono (by decide))).trans ((V₃.keeps.mono (by decide)).trans (Uz.keeps _))
  have Oz : Outside B (rv (kw len) acc + 4 * (nw len + 1)) 4 s.mem z.mem := by
    rw [Uz.mem, V₃.mem, V₂.mem, m₁']; exact writeW32_outside _ _ _ (by omega)
  exact ⟨h.keep Kz (by decide) (by decide) Oz (by omega) (by omega), Kz, Oz.unch⟩

theorem relRedHead {acc : Ref} (hG : Stable [.eax, .ebx, .ecx, .edx, .esi] G)
    (hah : acc.half = 0) (hab : acc.byte = 0) (haz : rv (kw len) acc + 4 * (nw len + 2) ≤ Z)
    {hc : VG.Taint.Hint VG.X86.Taint.T} (h : (VG.Taint.check sseTaint (τS L) (.block (redHead L acc)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (.block (redHead L acc))
      (Both L B Z len N args sp C fun g => G g ∧ True) := by
  have ra := rv_ge (kw len) acc
  refine relOp (by decide) hG (fun w hw => ?_)
    (fun s hb _ => WP.mono (redHead_frame hb hah hab haz) fun _ ⟨H, K, U⟩ => ⟨H, K, U, trivial⟩) h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨.inl (by omega), by omega⟩
  · exact ⟨.inr (by decide), by simp only [signSlot]; omega⟩

theorem relMulRow {acc src : Ref} {e : Nat} (hG : Stable [.eax, .ebx, .edx, .ebp, .esi] G)
    (he : e ≤ 4) (hsh : src.half = 0)
    (haz : rv (kw len) acc + 4 * (nw len + e + 2) ≤ Z) (hsz : rv (kw len) src + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) src + 4 * (nw len + e) ≤ rv (kw len) acc ∨
      rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) src) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (mulRow L false acc src (nBytes .esi e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (mulRow L false acc src (nBytes .esi e))
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) acc; omega) haz)
    (fun s hb _ => WP.mono (mulRow_gen hb he hsh haz hsz sep) fun _ ⟨H, O, _, K⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relRedTail {acc : Ref} (hG : Stable [.eax, .ebx, .edx] G)
    (hah : acc.half = 0) (hab : acc.byte = 0) (haz : rv (kw len) acc + 4 * (nw len + 2) ≤ Z)
    {hc : VG.Taint.Hint VG.X86.Taint.T} (h : (VG.Taint.check sseTaint (τS L) (.block (redTail L acc)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (.block (redTail L acc))
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) acc; omega) (by omega))
    (fun s hb _ => WP.mono (redTail_frame hb hah hab haz) fun _ ⟨H, K, U⟩ => ⟨H, K, U, trivial⟩) h

end VG.Proof.Rsa.X86.InvBatchRt.Time
