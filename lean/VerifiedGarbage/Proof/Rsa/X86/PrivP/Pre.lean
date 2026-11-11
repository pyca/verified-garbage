module

public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtArgs
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # `vg_rsa_private_checked_precomputed` on x86: `pre` and the call's arguments 18 and 19

What the wrapper keeps of `pre` (its arguments 20 and 21) from its entry on
(`PreCtx`), and `vg_rsa_private_crt_precomputed`'s arguments: `crtArgs`'
eighteen, then the primes' values `pre + 16 w` and their words
`pre_len - 2 w` (`crtArgsP_ok`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

/-- `pre` (argument 20, `pre_len = L` words in argument 21) through the body: the arguments and
`pre` readable and apart from what the body writes, and `pre` the key's precomputed values. -/
structure PreCtx (g : PrivGeometry) (bs : Fin 8 → List Byte) (P : BitVec 32) (L : Nat) (s : State) : Prop where
  high : g.stack.toNat + VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 88 ≤ 2 ^ 32
  ptr : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 100)) 32 = P
  len : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 104)) 32 =
    BitVec.ofNat 32 L
  argsRead : InRegions (s.rd ++ s.wr) (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 100)) 8
  argsSep : ∀ r ∈ bodyWrites g,
    Region.Disjoint ⟨byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 100), 8⟩ r
  preRead : InRegions (s.rd ++ s.wr) (byteAddr P) (8 * L)
  preFit : P.toNat + 8 * L ≤ 2 ^ 32
  preSep : ∀ r ∈ bodyWrites g, Region.Disjoint ⟨byteAddr P, 8 * L⟩ r
  lenEq : L = 2 * Spec.Rsa.modulusWords g.length + Spec.Rsa.primeWords g.pLength + Spec.Rsa.primeWords g.qLength
  key : Spec.Rsa.privatePrecompute (bs 0) (bs 3) (bs 4) = some (Spec.Rsa.wordsAt s.mem (byteAddr P) L)

theorem PreCtx.after {g : PrivGeometry} {bs : Fin 8 → List Byte} {P : BitVec 32} {L : Nat} {s t : State}
    {rs : List Reg} (H : PreCtx g bs P L s) (frame : Frame (bodyWrites g) s.mem t.mem) (rest : Keeps rs s t) :
    PreCtx g bs P L t := by
  have word : ∀ d, d + 4 ≤ 8 → t.mem.readW (byteAddr g.stack +
      BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 100) + BitVec.ofNat 64 d) 32 =
      s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 100) +
        BitVec.ofNat 64 d) 32 := fun d hd =>
    frame.readW (Offset.contains_base _ (by omega : d + 32 / 8 ≤ 8) (by omega)) H.argsSep (by decide)
  refine ⟨H.high, ?_, ?_, by rw [rest.2.1, rest.2.2]; exact H.argsRead, H.argsSep,
    by rw [rest.2.1, rest.2.2]; exact H.preRead, H.preFit, H.preSep, H.lenEq, ?_⟩
  · have w := word 0 (by decide)
    simp only [BitVec.add_zero] at w
    rw [w]; exact H.ptr
  · have w := word 4 (by decide)
    rw [Offset.add_add] at w
    rw [w]; exact H.len
  · rw [VG.Proof.Rsa.wordsAt_frame frame (by have := H.preFit; omega) H.preSep]; exact H.key

section
variable {g : PrivGeometry} {bs : Fin 8 → List Byte} {P : BitVec 32} {L : Nat}

/-- An address in the wrapper's frame and arguments, from `esp`. -/
theorem PreCtx.address {s : State} (h : PrivContext g bs s) (H : PreCtx g bs P L s) {d : Nat}
    (hd : d < VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 88) :
    addr (s.gpr .esp) d = byteAddr g.stack + BitVec.ofNat 64 d := by
  rw [h.sp]
  exact addr_eq (by have := H.high; omega)

/-- `vg_rsa_private_crt_precomputed`'s arguments: `crtArgument`'s eighteen, then the primes' values
`pre + 16 w` and their `pre_len - 2 w` words. -/
def crtArgumentP (g : PrivGeometry) (P : BitVec 32) (L : Nat) (j : Nat) : BitVec 32 :=
  if j < 18 then crtArgument g j
  else if j = 18 then P + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)
  else BitVec.ofNat 32 (L - 2 * Spec.Rsa.modulusWords g.length)

def CrtArgsP (g : PrivGeometry) (P : BitVec 32) (L : Nat) (s : State) : Prop :=
  ∀ j < 20, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) 32 = crtArgumentP g P L j

theorem preR2Args_ok (s : State) (h : PrivContext g bs s) (H : PreCtx g bs P L s) :
    WP isa (.block preR2Args) s fun t => PrivContext g bs t ∧ PreCtx g bs P L t ∧
      t.mem = (s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 76)
        (BitVec.ofNat 32 (L - 2 * Spec.Rsa.modulusWords g.length))).writeW
          (byteAddr g.stack + BitVec.ofNat 64 72) (P + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 72, 8⟩] s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  have hl := h.valid.maxLength
  have hlen := H.lenEq
  have w32 : 16 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by simp only [Spec.Rsa.modulusWords]; omega
  have L32 : L < 2 ^ 32 := by have := H.preFit; omega
  have rd20 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 4 * 20)) 4 := by
    rw [H.address h (by omega)]
    have := CallLay.inRegions_sub (off := 0) H.argsRead (l := 4) (by omega) (by decide)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 4 * 20 =
      VG.Impl.Rsa.X86.PrivChecked.frameBytes + 100 by omega] using this
  have rd21 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 4 * 21)) 4 := by
    rw [H.address h (by omega)]
    have := CallLay.inRegions_sub (off := 4) H.argsRead (l := 4) (by omega) (by decide)
    rw [Offset.add_add] at this
    exact this
  unfold preR2Args incoming stackAt
  refine wp_ldm rfl (h.readArg (j := 3) (by decide)) fun u₁ U₁ => ?_
  refine wp_addS rfl fun u₂ U₂ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₃ U₃ => ?_
  refine wp_addS rfl fun u₄ U₄ _ => ?_
  have sp₄ : u₄.gpr .esp = s.gpr .esp := by
    rw [U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide)]
  have m₄ : u₄.mem = s.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have rw₄ : u₄.rd ++ u₄.wr = s.rd ++ s.wr := by rw [U₄.rd, U₃.rd, U₂.rd, U₁.rd, U₄.wr, U₃.wr, U₂.wr, U₁.wr]
  refine wp_ldm sp₄ (by rw [rw₄]; exact rd21) fun u₅ U₅ => ?_
  refine wp_subS rfl fun u₆ U₆ _ => ?_
  have sp₆ : u₆.gpr .esp = s.gpr .esp := by rw [U₆.other _ (by decide), U₅.other _ (by decide), sp₄]
  have wr₆ : u₆.wr = s.wr := by rw [U₆.wr, U₅.wr, U₄.wr, U₃.wr, U₂.wr, U₁.wr]
  refine wp_stm sp₆ (by rw [wr₆, H.address h (by decide)]; exact h.inner.write (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)) fun u₇ U₇ => ?_
  refine wp_addS rfl fun u₈ U₈ _ => wp_addS rfl fun u₉ U₉ _ => wp_addS rfl fun u₁₀ U₁₀ _ => ?_
  have sp₁₀ : u₁₀.gpr .esp = s.gpr .esp := by
    rw [U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide), U₇.gpr, sp₆]
  have rw₁₀ : u₁₀.rd ++ u₁₀.wr = s.rd ++ s.wr := by
    rw [U₁₀.rd, U₉.rd, U₈.rd, U₇.rd, U₆.rd, U₅.rd, U₁₀.wr, U₉.wr, U₈.wr, U₇.wr, wr₆, U₄.rd, U₃.rd, U₂.rd, U₁.rd]
  refine wp_addS (readSrc_mem sp₁₀ (by rw [rw₁₀]; exact rd20)) fun u₁₁ U₁₁ _ => ?_
  have sp₁₁ : u₁₁.gpr .esp = s.gpr .esp := by rw [U₁₁.other _ (by decide), sp₁₀]
  have wr₁₁ : u₁₁.wr = s.wr := by rw [U₁₁.wr, U₁₀.wr, U₉.wr, U₈.wr, U₇.wr, wr₆]
  refine wp_stm sp₁₁ (by rw [wr₁₁, H.address h (by decide)]; exact h.inner.write (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)) fun t T => WP.block_nil ?_
  -- The values.
  have a3 := h.argumentValue (j := 3) (by decide)
  simp only [PrivGeometry.argument] at a3
  have eax₄ : u₄.gpr .eax = BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length) := by
    rw [U₄.gpr, U₃.gpr, U₂.gpr, U₁.gpr, a3]
    apply BitVec.eq_of_toNat_eq
    have h7 : (7 : BitVec 32).toNat = 7 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Spec.Rsa.modulusWords, h7]
    omega
  have ecx₅ : u₅.gpr .ecx = BitVec.ofNat 32 L := by
    rw [U₅.gpr, m₄, H.address h (by omega), show VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 4 * 21 =
      VG.Impl.Rsa.X86.PrivChecked.frameBytes + 104 by omega]
    exact H.len
  have ecx₆ : u₆.gpr .ecx = BitVec.ofNat 32 (L - 2 * Spec.Rsa.modulusWords g.length) := by
    rw [U₆.gpr, ecx₅, U₅.other _ (by decide), eax₄]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have m₇ : u₇.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 76)
      (BitVec.ofNat 32 (L - 2 * Spec.Rsa.modulusWords g.length)) := by
    rw [U₇.mem, U₆.mem, U₅.mem, m₄, H.address h (by decide), ecx₆]
  have eax₁₀ : u₁₀.gpr .eax = BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length) := by
    rw [U₁₀.gpr, U₉.gpr, U₈.gpr, U₇.gpr, U₆.other _ (by decide), U₅.other _ (by decide), eax₄]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have m₁₀ : u₁₀.mem = u₇.mem := by rw [U₁₀.mem, U₉.mem, U₈.mem]
  have F₇ : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 76, 4⟩] s.mem u₇.mem := by
    rw [m₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have p₁₀ : u₁₀.mem.readW (addr (s.gpr .esp) (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 4 * 20)) 32 = P := by
    rw [m₁₀, H.address h (by omega), show VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 4 * 20 =
      VG.Impl.Rsa.X86.PrivChecked.frameBytes + 100 by omega]
    rw [F₇.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 100), 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint _ (.inr (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega))
          (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega) (by omega)) (by decide)]
    exact H.ptr
  have eax₁₁ : u₁₁.gpr .eax = P + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length) := by
    rw [U₁₁.gpr, eax₁₀, p₁₀, BitVec.add_comm]
  have M : t.mem = (s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 76)
      (BitVec.ofNat 32 (L - 2 * Spec.Rsa.modulusWords g.length))).writeW
        (byteAddr g.stack + BitVec.ofNat 64 72) (P + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)) := by
    rw [T.mem, U₁₁.mem, m₁₀, m₇, H.address h (by decide), eax₁₁]
  have K : Keeps [.eax, .ecx] s t :=
    ((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))).trans
      (((U₅.keeps.mono (by decide)).trans (U₆.keeps.mono (by decide))).trans (U₇.keeps _))).trans
      ((((U₈.keeps.mono (by decide)).trans (U₉.keeps.mono (by decide))).trans
        ((U₁₀.keeps.mono (by decide)).trans (U₁₁.keeps.mono (by decide)))).trans (T.keeps _))
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 72, 8⟩] s.mem t.mem := by
    rw [M]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
    · have := Offset.contains_base (byteAddr g.stack + BitVec.ofNat 64 72) (d := 4) (n := 32 / 8) (k := 8)
        (by decide) (by decide)
      rwa [Offset.add_add] at this
    · have := Offset.contains_base (byteAddr g.stack + BitVec.ofNat 64 72) (d := 0) (n := 32 / 8) (k := 8)
        (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
  have sub : ∀ r ∈ [(⟨byteAddr g.stack + BitVec.ofNat 64 72, 8⟩ : Region)], ∃ R ∈ bodyWrites g, r.Sub R := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)⟩
  exact ⟨h.after (F.sub sub) K (K.1 .esp (by decide)), H.after (F.sub sub) K, M, F, K⟩

end

end VG.Proof.Rsa.X86.PrivChecked
