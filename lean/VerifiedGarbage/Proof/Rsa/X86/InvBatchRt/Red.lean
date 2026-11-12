module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.RowOp
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedWord
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.SelectX
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega

/-! # Subtraction of the modulus at a run-time width

`csub_ok`: `[o] = [src] mod m` for `[src] < 2 m`, by `borrowMask_ok` and a selection
(`select3_ok` where `o` is not `src`); and the writes to the header that keep the context.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- Writes to the header below the slots keep the context. -/
theorem Bx.keepLow {s t : State} {n : Nat} (h : Bx L s B Z len N n) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) {o c : Nat} (O : Outside B o c s.mem t.mem)
    (hc : o + c ≤ slotBase) : Bx L t B Z len N n := by
  have nw := h.nowrap
  have hZ := h.halfZ
  have e96 : halfSlot = 96 := rfl
  have e52 : slotBase = 52 := rfl
  refine ⟨h.ws.keep K edi esp (O.mono (Nat.zero_le _) (by omega)), ⟨fun j d hd => ?_, ?_, h.slots.small, h.slots.pos⟩, h.room⟩
  · have := slot_le hd
    rw [O.w32 (.inr (by omega)) (by omega)]
    exact h.slots.addr j d hd
  · rw [O.w32 (.inr (by omega)) (by omega)]
    exact h.slots.half

/-- Writes to the header above the slots keep the context. -/
theorem Bx.keepHigh {s t : State} (h : Bx L s B Z len N) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) {o c : Nat} (O : Outside B o c s.mem t.mem)
    (ho : halfSlot + 4 ≤ o) (hc : o + c ≤ Z) : Bx L t B Z len N := by
  have nw := h.nowrap
  refine ⟨h.ws.keep K edi esp (O.mono (Nat.zero_le _) (by omega)), ⟨fun j d hd => ?_, ?_, h.slots.small, h.slots.pos⟩, h.room⟩
  · have := slot_le hd
    rw [O.w32 (.inl (by omega)) (by omega)]
    exact h.slots.addr j d hd
  · rw [O.w32 (.inl (by omega)) (by omega)]
    exact h.slots.half

/-- The selection of `csub` into a different `[o]`: `[o] = k ? [b] : [a]`, `n` words, by `ecx`'s mask. -/
theorem select3_ok {s : State} (h : Bx L s B Z len N) {o a b : Ref} {k : Bool} (hk : s.gpr .ecx = cmask k)
    (hoh : o.half = 0) (hoz : rv (kw len) o + 4 * nw len ≤ Z) (haz : rv (kw len) a + 4 * nw len ≤ Z)
    (hbz : rv (kw len) b + 4 * nw len ≤ Z)
    (soa : rv (kw len) o + 4 * nw len ≤ rv (kw len) a ∨ rv (kw len) a + 4 * nw len ≤ rv (kw len) o)
    (sob : rv (kw len) o + 4 * nw len ≤ rv (kw len) b ∨ rv (kw len) b + 4 * nw len ≤ rv (kw len) o) :
    WP isa (.seq (.block (ptr L .ebp a .edx ++ ptr L .ebx b .edx ++ nBytes .edx 0 ++ ptr L .edi o .eax))
      (.seq select3LoopX (.block (restoreEdi L)))) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) o) (4 * nw len) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o) (nw len) =
        (if k then val32 s.mem B (rv (kw len) b) (nw len) else val32 s.mem B (rv (kw len) a) (nw len)) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  have hn := h.nowrap
  have hpos := h.ws.kw_pos
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have hZ := h.halfZ
  have ro := rv_ge (kw len) o
  rw [show ptr L .edi o .eax = ptr L .edi o .eax ++ [] from (List.append_nil _).symm]
  simp only [List.append_assoc]
  refine WP.seq (ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₁ K₁ m₁ p₁ => ?_)
  have h₁ : Bx L u₁ B Z len N := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _) ro hoz
  refine ptr_ok h₁.ws h₁.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₂ K₂ m₂ p₂ => ?_
  have h₂ : Bx L u₂ B Z len N := h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _) ro hoz
  refine nBytes_ok h₂.ws.ws.workspace h₂.slots hZ (by omega) (e := 0) (by decide) fun u₃ K₃ m₃ c₃ => ?_
  have h₃ : Bx L u₃ B Z len N := h₂.keep K₃ (by decide) (by decide) (by rw [m₃]; exact Outside.refl _ _ _ _) ro hoz
  refine ptr_ok h₃.ws h₃.slots hZ (by decide) (by decide) (by decide) (by decide) (fun _ => hoh)
    (by omega) fun u K₄ m₄ p₄ => WP.block_nil ?_
  have K : Keeps [.eax, .ebx, .edx, .ebp, .edi] s u :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))
  have m : u.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  refine WP.seq (WP.mono (select3LoopX_ok (h.ws.rt.of_keeps K) k (N := nw len) (by omega) haz hbz hoz soa sob
    (by rw [PtrAt, K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [PtrAt, K₄.1 _ (by decide), K₃.1 _ (by decide)]; exact p₂) p₄
    (by rw [K₄.1 _ (by decide), c₃]; omega) (by rw [K.1 _ (by decide)]; exact hk)) fun t ⟨O, V, Kt⟩ => ?_)
  rw [m] at O V
  have KK : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := K.trans Kt
  have O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega)
  unfold restoreEdi
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  have K' : Keeps [.eax, .ebx, .edx, .ebp] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp])
      (KK.trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h.ws).symm)
  refine ⟨h.keep K' (by decide) (by decide) (by rw [U.mem]; exact O) ro hoz, by rw [U.mem]; exact O, ?_, K'⟩
  rw [U.mem, V]

/-- `borrowMask src`: `ecx` all ones where `[src + 4 n]` does not borrow the carry `c` of `ecx`'s
mask. -/
theorem borrowMask_ok {s : State} (h : Bx L s B Z len N) {src : Ref} (hsh : src.half = 0)
    (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z) {c : Bool} (hc : s.gpr .ecx = cmask c)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Bx L u B Z len N → Keeps [.eax, .ebx, .ecx, .edx] s u → u.mem = s.mem →
      u.gpr .ecx = cmask (!decide (w32 s.mem B (rv (kw len) src + 4 * nw len) < c.toNat)) →
      WP isa (.block is) u Q) :
    WP isa (.block (borrowMask L src ++ is)) s Q := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have ke := kw_eq len
  have rs := rv_ge (kw len) src
  have r1 : rv (kw len) { src with half := 1 } = rv (kw len) src + 4 * nw len := by
    rw [rv_half1 _ _ hsh]
  simp only [borrowMask, List.append_assoc]
  refine ptr_ok h.ws h.slots hZ (r := .ebx) (t := .edx) (x := { src with half := 1 }) (by decide)
    (by decide) (by decide) (by decide) (by intro e; cases e) (by rw [r1]; omega) fun s₂ K₂ m₂ p₂ => ?_
  rw [r1] at p₂
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr (h.ws.rt.of_keeps K₂) p₂ (d := 0) (by omega)) fun s₃ U₃ _ => ?_
  have hc₃ : s₃.gpr .ecx = cmask c := by rw [U₃.other _ (by decide), K₂.1 _ (by decide)]; exact hc
  refine VG.Proof.Bignum.X86.PublicRt.wp_carry hc₃ fun s₄ U₄ cf₄ => ?_
  refine wp_sbbS rfl cf₄ fun s₅ U₅ cf₅ => ?_
  refine wp_sbbS rfl cf₅ fun s₆ U₆ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₇ U₇ => ?_
  refine wp_movS rfl fun s₈ U₈ _ => ?_
  have K₈ : Keeps [.eax, .ebx, .ecx, .edx] s s₈ :=
    ((((((K₂.mono (by decide)).trans (U₃.keeps.mono (by decide))).trans (U₄.keeps.mono (by decide))).trans
      (U₅.keeps.mono (by decide))).trans (U₆.keeps.mono (by decide))).trans (U₇.keeps.mono (by decide))).trans
      (U₈.keeps.mono (by decide))
  have m₈ : s₈.mem = s.mem := by rw [U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, m₂]
  refine k s₈ (h.keep K₈ (by decide) (by decide) (by rw [m₈]; exact Outside.refl _ _ _ _) rs hsz) K₈ m₈ ?_
  have e7 := U₇.gpr
  simp only [reduceCtorEq, ite_false] at e7
  rw [U₈.gpr, e7, U₆.gpr, Mont.X86.mask_val]
  have t₃ : (s₃.gpr .eax).toNat = w32 s.mem B (rv (kw len) src + 4 * nw len) := by
    rw [U₃.gpr, m₂, Nat.add_zero]
  rw [U₄.other _ (by decide), t₃]
  simp [cmask]

/-- `csub src o`: `[o] = [src] mod m` for `[src] < 2 m` (`n` words and a top word), as `Mont.csub_ok`
states it. -/
theorem csub_ok {s : State} (h : Bx L s B Z len N) {src o : Ref} (hsh : src.half = 0) (hoh : o.half = 0)
    (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z) (hoz : rv (kw len) o + 4 * nw len ≤ Z)
    (htz : rv (kw len) tmp + 4 * nw len ≤ Z) (hmz : rv (kw len) mo + 4 * nw len ≤ Z)
    (hts : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len + 1) ≤ rv (kw len) tmp)
    (htm : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) mo ∨ rv (kw len) mo + 4 * nw len ≤ rv (kw len) tmp)
    (hos : o ≠ src → rv (kw len) o + 4 * nw len ≤ rv (kw len) src ∨ rv (kw len) src + 4 * nw len ≤ rv (kw len) o)
    (hot : rv (kw len) o + 4 * nw len ≤ rv (kw len) tmp ∨ rv (kw len) tmp + 4 * nw len ≤ rv (kw len) o)
    {m : Nat} (hm : val32 s.mem B (rv (kw len) mo) (nw len) = m)
    (hV : val32 s.mem B (rv (kw len) src) (nw len + 1) < 2 * m) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.csub L src o) s fun u =>
      Bx L u B Z len N ∧ Unch B [(rv (kw len) tmp, 4 * nw len), (rv (kw len) o, 4 * nw len)] s.mem u.mem ∧
      val32 u.mem B (rv (kw len) o) (nw len) = val32 s.mem B (rv (kw len) src) (nw len + 1) % m ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have ke := kw_eq len
  have rs := rv_ge (kw len) src
  have rt := rv_ge (kw len) tmp
  have r1 : rv (kw len) { src with half := 1 } = rv (kw len) src + 4 * nw len := by
    rw [rv_half1 _ _ hsh]
  unfold VG.Impl.Rsa.X86.InvBatchRt.csub
  -- The difference, `n` words.
  refine WP.seq (WP.mono (chainSub_ok h (o := tmp) (a := src) (b := mo) (e := 0) (by decide) rfl
    (by simpa using htz) (by simpa using (by omega : rv (kw len) src + 4 * nw len ≤ Z))
    (by simpa using hmz) (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega))
    fun s₁ ⟨H₁, O₁, ⟨c, hc, V₁⟩, K₁⟩ => ?_)
  simp only [Nat.add_zero] at O₁ V₁
  -- The mask: all ones where the top word does not borrow.
  rw [show borrowMask L src = borrowMask L src ++ [] from (List.append_nil _).symm]
  refine WP.seq (borrowMask_ok H₁ hsh hsz hc fun s₈ H₈ K₈ m₈ mask => WP.block_nil ?_)
  have topw : w32 s₁.mem B (rv (kw len) src + 4 * nw len) = w32 s.mem B (rv (kw len) src + 4 * nw len) :=
    O₁.w32 (by omega) (by omega)
  rw [topw] at mask
  -- The arithmetic.
  have T₁ : val32 s₁.mem B (rv (kw len) src) (nw len) = val32 s.mem B (rv (kw len) src) (nw len) :=
    O₁.val32 (by omega) (by omega)
  have hval : (if (!decide (w32 s.mem B (rv (kw len) src + 4 * nw len) < c.toNat))
      then val32 s₁.mem B (rv (kw len) tmp) (nw len) else val32 s.mem B (rv (kw len) src) (nw len)) =
      val32 s.mem B (rv (kw len) src) (nw len + 1) % m := by
    have hmX : m < 2 ^ (32 * nw len) := hm ▸ val32_lt _ _ _ _
    have A := csub_arith (T := val32 s.mem B (rv (kw len) src) (nw len)) (D := val32 s₁.mem B (rv (kw len) tmp) (nw len))
      (top := w32 s.mem B (rv (kw len) src + 4 * nw len)) (b := c) hmX (val32_lt _ _ _ _)
      (by rw [← val32_succ]; exact hV) (by rw [← hm]; exact V₁)
    rw [val32_succ s.mem B (rv (kw len) src) (nw len), ← A]
    by_cases hb : w32 s.mem B (rv (kw len) src + 4 * nw len) < c.toNat
    · simp only [hb, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    · simp only [hb, decide_false, Bool.not_false, ite_true, ite_false]
  have KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s s₈ := (K₁.mono (by decide)).trans (K₈.mono (by decide))
  by_cases ho : o = src
  · subst ho
    rw [ite_eq_left_of_eq_true _ _ (eq_self o)]
    refine WP.mono (selIn_ok H₈ (o := o) (a := tmp) (e := 0) mask (by decide) (by simpa using hoz)
      (by simpa using htz) (by simp only [Nat.add_zero]; omega)) fun u ⟨Hu, Ou, Vu, Ku⟩ => ?_
    simp only [Nat.add_zero] at Ou Vu
    refine ⟨Hu, ?_, ?_, (KK.mono (by decide)).trans (Ku.mono (by decide))⟩
    · intro x hx
      rw [Ou x (hx (rv (kw len) o, 4 * nw len) (by simp)), m₈, O₁ x (hx (rv (kw len) tmp, 4 * nw len) (by simp))]
    · rw [Vu, m₈, T₁, hval]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ho)]
    refine WP.mono (select3_ok H₈ (o := o) (a := src) (b := tmp) mask hoh hoz
      (by omega) htz (hos ho) hot) fun u ⟨Hu, Ou, Vu, Ku⟩ => ?_
    refine ⟨Hu, ?_, ?_, (KK.mono (by decide)).trans (Ku.mono (by decide))⟩
    · intro x hx
      rw [Ou x (hx (rv (kw len) o, 4 * nw len) (by simp)), m₈, O₁ x (hx (rv (kw len) tmp, 4 * nw len) (by simp))]
    · rw [Vu, m₈, T₁, hval]

end VG.Proof.Rsa.X86.InvBatchRt
