module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ptr
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.SelectX
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
public import VerifiedGarbage.Proof.Rsa.X86.Chain
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift

/-! # The run-time-width batch's operations on its arrays

`Bx`: what every operation needs of a state, `KeyRt`'s `RtWs`, the header words
`Slots` and room for sixteen arrays; `Bx.keep`: kept by writes to the arrays.
`selIn_ok`, `copy_ok`, `zeros_ok`, `chainAdd_ok` and `chainSub_ok`: `KeyRt`'s
loops at `Ref`s, over `n + e` words for `n = w / 2`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (arr)

/-- The primes' words, half the modulus's. -/
abbrev nw (len : Nat) : Nat := kw len / 2

theorem kw_eq (len : Nat) : kw len = 2 * nw len := by simp only [nw, kw]; omega

/-- What the batch's operations need of a state. -/
structure Bx (L : Lay) (s : State) (B : Addr) (Z len N : Nat) : Prop where
  ws : RtWs L s B Z len N
  slots : Slots s.mem B (kw len)
  room : 16 ≤ N

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem Bx.fits {s : State} (h : Bx L s B Z len N) : VG.Impl.Rsa.X86.InvBatch.offset (kw len) 16 ≤ Z := by
  have := h.ws.ws.fits
  rw [offset_eq]
  exact Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.room) _) this

theorem Bx.nowrap {s : State} (h : Bx L s B Z len N) : B.toNat + Z ≤ 2 ^ 32 := h.ws.ws.workspace.nowrap

theorem Bx.halfZ {s : State} (h : Bx L s B Z len N) : halfSlot + 4 ≤ Z := by
  have := h.fits; simp only [VG.Impl.Rsa.X86.InvBatch.offset, halfSlot] at *; omega

/-- Writes to `[o, o + c)` above the header, inside the working space, keep the context. -/
theorem Bx.keep {s t : State} (h : Bx L s B Z len N) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) {o c : Nat} (O : Outside B o c s.mem t.mem)
    (ho : 160 ≤ o) (hc : o + c ≤ Z) : Bx L t B Z len N := by
  have nw := h.nowrap
  have e96 : halfSlot = 96 := rfl
  refine ⟨h.ws.keep K edi esp (O.mono (Nat.zero_le _) (by omega)), ⟨fun j d hd => ?_, ?_, h.slots.small⟩, h.room⟩
  · have := slot_le hd
    rw [O.w32 (.inl (by omega)) (by omega)]
    exact h.slots.addr j d hd
  · rw [O.w32 (.inl (by omega)) (by omega)]
    exact h.slots.half

theorem rv_ge (w : Nat) (x : Ref) : 160 ≤ rv w x := by
  simp only [rv, VG.Impl.Rsa.X86.InvBatch.offset]; omega

/-! ## Selections and copies -/

/-- `selIn o a (nBytes .edi e)`: `[o] = [a]` where the mask `ecx` is all ones, else kept, `n + e`
words. -/
theorem selIn_ok {s : State} (h : Bx L s B Z len N) {o a : Ref} {e : Nat} {k : Bool}
    (hk : s.gpr .ecx = cmask k) (he : e ≤ 4)
    (hoz : rv (kw len) o + 4 * (nw len + e) ≤ Z) (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) o + 4 * (nw len + e) ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) o) :
    WP isa (selIn L o a (nBytes .edi e)) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) o) (4 * (nw len + e)) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o) (nw len + e) =
        (if k then val32 s.mem B (rv (kw len) a) (nw len + e) else val32 s.mem B (rv (kw len) o) (nw len + e)) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  have hn := h.nowrap
  have hw := kw_bound h.ws.lenLe
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have hZ := h.halfZ
  unfold selIn
  rw [show nBytes .edi e = nBytes .edi e ++ [] from (List.append_nil _).symm]
  simp only [List.append_assoc]
  refine WP.seq (ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₁ K₁ m₁ p₁ => ?_)
  have h₁ : Bx L u₁ B Z len N := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine ptr_ok h₁.ws h₁.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₂ K₂ m₂ p₂ => ?_
  have h₂ : Bx L u₂ B Z len N := h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine nBytes_ok h₂.ws.ws.workspace h₂.slots hZ (by omega) he fun u K₃ m₃ c₃ => WP.block_nil ?_
  have K : Keeps [.ebx, .edx, .ebp, .edi] s u :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide)))
  have m : u.mem = s.mem := by rw [m₃, m₂, m₁]
  have ecx : u.gpr .ecx = cmask k := by rw [K.1 _ (by decide)]; exact hk
  refine WP.seq (WP.mono (selectLoopX_ok (h.ws.rt.of_keeps K) (x := rv (kw len) a) (d := rv (kw len) o)
    (N := nw len + e) k (by omega) (by omega) sep
    (by rw [PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂) (by rw [c₃]; omega) ecx) fun t ⟨O, V, _, Kt⟩ => ?_)
  rw [m] at O V
  have KK : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  have O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega)
  unfold restoreEdi
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  have K' : Keeps [.eax, .ebx, .edx, .ebp] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp])
      (KK.trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h.ws).symm)
  exact ⟨h.keep K' (by decide) (by decide) (by rw [U.mem]; exact O) (rv_ge _ o) hoz,
    by rw [U.mem]; exact O, by rw [U.mem]; exact V, K'⟩

/-- `copy o a (nBytes .edi e)`: `[o] = [a]`, `n + e` words. -/
theorem copy_ok {s : State} (h : Bx L s B Z len N) {o a : Ref} {e : Nat} (he : e ≤ 4)
    (hoz : rv (kw len) o + 4 * (nw len + e) ≤ Z) (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) o + 4 * (nw len + e) ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) o) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.copy L o a (nBytes .edi e)) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) o) (4 * (nw len + e)) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o) (nw len + e) = val32 s.mem B (rv (kw len) a) (nw len + e) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Rsa.X86.InvBatchRt.copy
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have hu : Bx L u B Z len N := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine WP.mono (selIn_ok hu (k := true) (by rw [U.gpr]; rfl) he hoz haz sep) fun t ⟨H, O, V, K⟩ =>
    ⟨H, by rw [U.mem] at O; exact O, by rw [V, U.mem]; rfl, (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩

/-! ## Counts, zeroing, chains, signs -/

/-- Code that sets `r` to `4 c`, the bytes of `c` words, from the header. -/
def CountSpec (cnt : List Instr) (r : Reg) (B : Addr) (Z w c : Nat) : Prop :=
  ∀ (u : State) (is : List Instr) (Q : State → Prop), Scr u B Z → Slots u.mem B w →
    (∀ v, Keeps [r] u v → v.mem = u.mem → (v.gpr r).toNat = 4 * c → WP isa (.block is) v Q) →
    WP isa (.block (cnt ++ is)) u Q

theorem nBytes_spec {r : Reg} {e w : Nat} (hz : halfSlot + 4 ≤ Z) (hw : 2 * w ≤ 4104) (he : e ≤ 4)
    (hw2 : w % 2 = 0) : CountSpec (nBytes r e) r B Z w (w / 2 + e) :=
  fun _ _ _ hs hsl k => nBytes_ok hs hsl hz hw he fun v K m c => k v K m (by rw [c]; omega)

theorem wBytes_spec {r : Reg} {w : Nat} (hz : halfSlot + 4 ≤ Z) (hw : 2 * w ≤ 4104) :
    CountSpec (wBytes r) r B Z w w :=
  fun _ _ _ hs hsl k => wBytes_ok hs hsl hz hw k

/-- `zeros o cnt`: `[o]` zeroed, `c` words. -/
theorem zeros_ok {s : State} (h : Bx L s B Z len N) {o : Ref} {cnt : List Instr} {c : Nat}
    (hc : CountSpec cnt .ecx B Z (kw len) c) (hc0 : 0 < c) (hoz : rv (kw len) o + 4 * c ≤ Z) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.zeros L o cnt) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) o) (4 * c) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o) c = 0 ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hn := h.nowrap
  have hZ := h.halfZ
  unfold VG.Impl.Rsa.X86.InvBatchRt.zeros
  simp only [List.append_assoc]
  refine WP.seq (ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₁ K₁ m₁ p₁ => ?_)
  have h₁ : Bx L u₁ B Z len N := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine hc u₁ _ _ h₁.ws.ws.workspace h₁.slots fun u₂ K₂ m₂ c₂ => wp_movS rfl fun u U _ => WP.block_nil ?_
  have K : Keeps [.eax, .ecx, .edx, .ebp] s u :=
    ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (U.keeps.mono (by decide))
  have m : u.mem = s.mem := by rw [U.mem, m₂, m₁]
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.zeroLoop_ok (h.ws.rt.of_keeps K) (x := rv (kw len) o) (N := c) hc0
    hoz (by rw [PtrAt, U.other _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [U.other _ (by decide)]; exact c₂) U.gpr) fun t ⟨O, V, Kt⟩ => ?_
  rw [m] at O
  exact ⟨h.keep (K.trans (Kt.mono (by decide))) (by decide) (by decide) O (rv_ge _ o) hoz, O, V,
    K.trans (Kt.mono (by decide))⟩

/-- The setup of `chain`: the pointers at `a`, `b` and `o`, the count, no carry. -/
theorem chainSetup_ok {s : State} (h : Bx L s B Z len N) {o a b : Ref} {e : Nat} (he : e ≤ 4)
    (hoh : o.half = 0) (hoz : rv (kw len) o + 4 * (nw len + e) ≤ Z) (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z)
    (hbz : rv (kw len) b + 4 * (nw len + e) ≤ Z) :
    WP isa (.block (ptr L .ebp a .edx ++ ptr L .ebx b .edx ++ nBytes .edx e ++ ptr L .edi o .eax ++
      ([.mov .ecx (.imm 0)] : List Instr))) s fun u =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s u ∧ u.mem = s.mem ∧ PtrAt u B .ebp (rv (kw len) a) ∧
      PtrAt u B .ebx (rv (kw len) b) ∧ PtrAt u B .edi (rv (kw len) o) ∧
      (u.gpr .edx).toNat = 4 * (nw len + e) ∧ u.gpr .ecx = cmask false := by
  have hn := h.nowrap
  have hpos := h.ws.kw_pos
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have hZ := h.halfZ
  simp only [List.append_assoc]
  refine ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₁ K₁ m₁ p₁ => ?_
  have h₁ : Bx L u₁ B Z len N := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine ptr_ok h₁.ws h₁.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₂ K₂ m₂ p₂ => ?_
  have h₂ : Bx L u₂ B Z len N := h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine nBytes_ok h₂.ws.ws.workspace h₂.slots hZ (by omega) he fun u₃ K₃ m₃ c₃ => ?_
  have h₃ : Bx L u₃ B Z len N := h₂.keep K₃ (by decide) (by decide) (by rw [m₃]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine ptr_ok h₃.ws h₃.slots hZ (by decide) (by decide) (by decide) (by decide) (fun _ => hoh)
    (by omega) fun u₄ K₄ m₄ p₄ => wp_movS rfl fun u U _ => WP.block_nil ?_
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s u :=
    ((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))).trans (U.keeps.mono (by decide))
  refine ⟨K, by rw [U.mem, m₄, m₃, m₂, m₁], ?_, ?_, ?_, ?_, U.gpr⟩
  · rw [PtrAt, U.other _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁
  · rw [PtrAt, U.other _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide)]; exact p₂
  · rw [PtrAt, U.other _ (by decide)]; exact p₄
  · rw [U.other _ (by decide), K₄.1 _ (by decide), c₃]; omega

/-- What `chain` keeps of the context, from the loop's frame and `edi` set back. -/
theorem chain_frame {s t : State} (h : Bx L s B Z len N) {o : Ref} {c : Nat} (hoz : rv (kw len) o + 4 * c ≤ Z)
    (O : Outside B (rv (kw len) o) (4 * c) s.mem t.mem)
    (Kt : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t) (edi : t.gpr .edi = BitVec.ofNat 32 B.toNat) :
    Bx L t B Z len N ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have K' : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) Kt
      (edi.trans (RtWs.edi_eq h.ws).symm)
  exact ⟨h.keep K' (by decide) (by decide) O (rv_ge _ o) hoz, K'⟩

/-- `chain .sbb o a b (nBytes .edx e)`: `[o] = [a] - [b]`, `n + e` words, the borrow as a mask in `ecx`. -/
theorem chainSub_ok {s : State} (h : Bx L s B Z len N) {o a b : Ref} {e : Nat} (he : e ≤ 4)
    (hoh : o.half = 0) (hoz : rv (kw len) o + 4 * (nw len + e) ≤ Z) (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z)
    (hbz : rv (kw len) b + 4 * (nw len + e) ≤ Z)
    (da : rv (kw len) o ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) o)
    (db : rv (kw len) o ≤ rv (kw len) b ∨ rv (kw len) b + 4 * (nw len + e) ≤ rv (kw len) o) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.chain L .sbb o a b (nBytes .edx e)) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) o) (4 * (nw len + e)) s.mem t.mem ∧
      (∃ c : Bool, t.gpr .ecx = cmask c ∧
        val32 t.mem B (rv (kw len) o) (nw len + e) + val32 s.mem B (rv (kw len) b) (nw len + e) =
          val32 s.mem B (rv (kw len) a) (nw len + e) + 2 ^ (32 * (nw len + e)) * c.toNat) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := h.nowrap
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  unfold VG.Impl.Rsa.X86.InvBatchRt.chain
  refine WP.seq (WP.mono (chainSetup_ok h he hoh hoz haz hbz) fun u ⟨K, m, pa, pb, po, e', c⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Chain.subLoop_ok (h.ws.rt.of_keeps K) (n := nw len + e)
    (by omega) haz hbz hoz da db pa pb po e' c) fun t ⟨O, _, V, Kt⟩ => ?_)
  rw [m] at O V
  have KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  have O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega)
  unfold restoreEdi
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain ⟨F, Kr⟩ := chain_frame h hoz (by rw [U.mem]; exact O) (KK.trans (U.keeps.mono (by decide))) U.gpr
  refine ⟨F, by rw [U.mem]; exact O, ?_, Kr⟩
  obtain ⟨cb, C, V'⟩ := V
  exact ⟨cb, by rw [U.other _ (by decide)]; exact C, by rw [U.mem]; exact V'⟩

/-- `chain .adc o a b (nBytes .edx e)`: `[o] = [a] + [b]`, `n + e` words, the carry as a mask in `ecx`. -/
theorem chainAdd_ok {s : State} (h : Bx L s B Z len N) {o a b : Ref} {e : Nat} (he : e ≤ 4)
    (hoh : o.half = 0) (hoz : rv (kw len) o + 4 * (nw len + e) ≤ Z) (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z)
    (hbz : rv (kw len) b + 4 * (nw len + e) ≤ Z)
    (da : rv (kw len) o ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) o)
    (db : rv (kw len) o ≤ rv (kw len) b ∨ rv (kw len) b + 4 * (nw len + e) ≤ rv (kw len) o) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.chain L .adc o a b (nBytes .edx e)) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) o) (4 * (nw len + e)) s.mem t.mem ∧
      (∃ c : Bool, t.gpr .ecx = cmask c ∧
        val32 t.mem B (rv (kw len) o) (nw len + e) + 2 ^ (32 * (nw len + e)) * c.toNat =
          val32 s.mem B (rv (kw len) a) (nw len + e) + val32 s.mem B (rv (kw len) b) (nw len + e)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := h.nowrap
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  unfold VG.Impl.Rsa.X86.InvBatchRt.chain
  refine WP.seq (WP.mono (chainSetup_ok h he hoh hoz haz hbz) fun u ⟨K, m, pa, pb, po, e', c⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Chain.addLoop_ok (h.ws.rt.of_keeps K) (n := nw len + e)
    (by omega) haz hbz hoz da db pa pb po e' c) fun t ⟨O, _, _, V, Kt⟩ => ?_)
  rw [m] at O V
  have KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  have O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega)
  unfold restoreEdi
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain ⟨F, Kr⟩ := chain_frame h hoz (by rw [U.mem]; exact O) (KK.trans (U.keeps.mono (by decide))) U.gpr
  refine ⟨F, by rw [U.mem]; exact O, ?_, Kr⟩
  obtain ⟨cb, C, V'⟩ := V
  exact ⟨cb, by rw [U.other _ (by decide)]; exact C, by rw [U.mem]; exact V'⟩

/-- `signOf`: `ecx` the mask of the sign of the word at `ebx`. -/
theorem signOf_ok {s : State} {W : Addr} {Y x : Nat} (hw : Ws s W Y) (p : PtrAt s W .ebx x) (hx : x + 4 ≤ Y)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Keeps [.eax, .ecx] s u → u.mem = s.mem →
      u.gpr .ecx = (if 2 ^ 31 ≤ w32 s.mem W x then BitVec.allOnes 32 else 0) → WP isa (.block is) u Q) :
    WP isa (.block (signOf ++ is)) s Q := by
  simp only [signOf, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr hw p (d := 0) (by omega)) fun s₁ U₁ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₂ U₂ => ?_
  refine wp_movS rfl fun s₃ U₃ _ => wp_subS rfl fun u U₄ _ => ?_
  refine k u (((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
    ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))) (by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]) ?_
  rw [U₄.gpr, U₃.gpr, U₃.other _ (by decide), U₂.gpr, U₁.gpr, Nat.add_zero]
  exact VG.Proof.Weierstrass.X86.Inv.signMask_eq _

/-- `maskAt x`: `ecx` the mask of the sign of the word at `x`. -/
theorem maskAt_ok {s : State} (h : Bx L s B Z len N) {x : Ref} (hxz : rv (kw len) x + 4 ≤ Z)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Keeps [.eax, .ebx, .ecx, .edx] s u → u.mem = s.mem →
      u.gpr .ecx = (if 2 ^ 31 ≤ w32 s.mem B (rv (kw len) x) then BitVec.allOnes 32 else 0) →
      WP isa (.block is) u Q) :
    WP isa (.block (maskAt L x ++ is)) s Q := by
  have hn := h.nowrap
  have hZ := h.halfZ
  simp only [maskAt, List.append_assoc]
  refine ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₁ K₁ m₁ p₁ => ?_
  refine signOf_ok (h.ws.rt.of_keeps K₁) p₁ hxz fun u K₂ m₂ c₂ => k u ((K₁.mono (by decide)).trans (K₂.mono (by decide)))
    (by rw [m₂, m₁]) (by rw [c₂, m₁])

/-- `zeroWord x`: the word at `x` zeroed. -/
theorem zeroWord_ok {s : State} (h : Bx L s B Z len N) {x : Ref} (hxz : rv (kw len) x + 4 ≤ Z)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Bx L u B Z len N → Keeps [.eax, .ebx, .edx] s u → Outside B (rv (kw len) x) 4 s.mem u.mem →
      w32 u.mem B (rv (kw len) x) = 0 → WP isa (.block is) u Q) :
    WP isa (.block (zeroWord L x ++ is)) s Q := by
  have hn := h.nowrap
  have hZ := h.halfZ
  simp only [zeroWord, List.append_assoc, List.cons_append, List.nil_append]
  refine ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₁ K₁ m₁ p₁ => ?_
  have hw₁ := h.ws.rt.of_keeps K₁
  refine wp_movS rfl fun s₁ U₁ _ => ?_
  have hw₂ := hw₁.of_keeps U₁.keeps
  have p₂ : PtrAt s₁ B .ebx (rv (kw len) x) := by rw [PtrAt, U₁.other .ebx (by decide)]; exact p₁
  have ea : s₁.ea (at_ .ebx 0) = off B (rv (kw len) x) := by simpa using ea_ptr hw₂ p₂ (d := 0) (by omega)
  refine wp_storeS ea (ws_write hw₂ (by omega)) fun u M => ?_
  have K : Keeps [.eax, .ebx, .edx] s u := ((K₁.mono (by decide)).trans (U₁.keeps.mono (by decide))).trans (M.keeps _)
  have O : Outside B (rv (kw len) x) 4 s.mem u.mem := by
    rw [M.mem, U₁.mem, m₁]; exact writeW32_outside _ _ _ (by omega)
  refine k u (h.keep K (by decide) (by decide) O (rv_ge _ x) hxz) K O ?_
  rw [M.mem, w32_write_self, U₁.gpr]; rfl

end VG.Proof.Rsa.X86.InvBatchRt
