import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds

/-!
# AES rounds with interleaved work that writes scratch memory

The intervening work preserves the AES states and the key invariant, but
may prepare the next batch in memory and reuse the round-key register.
`Q` describes that work; ordinary AES rounds preserve it through `YFrame`.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.StitchAvx8 (aesFixed)
open VG.Impl.Aes.X86_64.Vaes (keyOpL roundL)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.Vaes (RInv lanes keyOpL_ok roundL_ok)
open VG.Proof.Aes.X86_64.AesNi (Keys st rnds_zero cipher_eq ea_at
  byte_roundKey pxor_st aesenclast_st)
open VG.Spec.Aes (roundKey cipher)

theorem fixedRounds_ok (regs : List XReg) (hnd : regs.Nodup) (h1 : .xmm1 ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Nat → Spec.Aes.State}
    (g : Nat → List Instr) (Q : Nat → State → Prop)
    (hkeys : ∀ j s, Q j s → Keys nr w s)
    (hg : ∀ j, 1 ≤ j → j < nr → ∀ s, Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧
        ∀ b ∈ regs, ∀ l < lanes .l128, s'.lane b l = s.lane b l)
    (hq : ∀ j s s', Q j s → YFrame (.xmm1 :: regs) s s' → Q j s')
    (k : Nat) (s : State) (hk : k < nr)
    (hI : RInv .l128 regs w x 0 s) (hQ : Q 1 s) :
    WP isa (.block ((List.range k).flatMap fun j =>
      roundL .l128 .xmm1 regs (j + 1) ++ g (j + 1))) s fun s' =>
      RInv .l128 regs w x k s' ∧ Q (k + 1) s' := by
  induction k with
  | zero =>
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hI, hQ⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hQ₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (roundL_ok .l128 .xmm1 regs hnd h1 (k := k) (by omega)
      (hkeys _ _ hQ₁) hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_
    refine WP.mono (hg (k + 1) (by omega) hk s₂ (hq _ _ _ hQ₁ hf₂))
      fun s' ⟨hQ', he⟩ => ⟨fun b hb l hl => ?_, hQ'⟩
    rw [he b hb l hl]
    exact hI₂ b hb l hl

theorem aesFixed_ok (nr : Nat) (hnr : 0 < nr) (regs : List XReg)
    (hnd : regs.Nodup) (h1 : .xmm1 ∉ regs) {w : List Byte}
    (g : Nat → List Instr) (Q : Nat → State → Prop)
    (hkeys : ∀ j s, Q j s → Keys nr w s)
    (hg : ∀ j, 1 ≤ j → j < nr → ∀ s, Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧
        ∀ b ∈ regs, ∀ l < lanes .l128, s'.lane b l = s.lane b l)
    (hq : ∀ j s s', Q j s → YFrame (.xmm1 :: regs) s s' → Q j s')
    (hlast : ∀ s, Q nr s →
      s.ea (at_ .r10 0) = s.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int))
    (s : State) (hQ : Q 1 s) :
    WP isa (aesFixed nr regs g) s fun s' =>
      (∀ b ∈ regs, ∀ l < lanes .l128,
        st (s'.lane b l) = cipher nr w (st (s.lane b l))) ∧ Q nr s' := by
  let x : XReg → Nat → Spec.Aes.State := fun b l => st (s.lane b l)
  have hK := hkeys _ _ hQ
  have k0 := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  rw [aesFixed, List.append_assoc, WP.block_append_iff]
  refine WP.mono (keyOpL_ok .l128 .xmm1 regs .vpxor _ s hnd h1
    (by rw [ea_at]; exact hK.keys 0 (by omega))) fun s₁ ⟨hv₁, hf₁⟩ => ?_
  have hI₁ : RInv .l128 regs w x 0 s₁ := fun b hb l hl => by
    rw [hv₁ b hb l hl]
    show st (XBinOp.eval .pxor _ _) = _
    rw [pxor_st _ _ (roundKey w 0) (by rw [hK.sched, ea_at]; exact k0), rnds_zero]
  rw [WP.block_append_iff]
  refine WP.mono (fixedRounds_ok regs hnd h1 g Q hkeys hg hq (nr - 1) s₁
    (by omega) hI₁ (hq _ _ _ hQ hf₁)) fun s₂ ⟨hI₂, hQ₂⟩ => ?_
  have hn : nr - 1 + 1 = nr := by omega
  rw [hn] at hQ₂
  have hK₂ := hkeys _ _ hQ₂
  have hea := hlast _ hQ₂
  refine WP.mono (keyOpL_ok .l128 .xmm1 regs .vaesenclast _ s₂ hnd h1
    (by rw [hea]; exact hK₂.keys nr (Nat.le_refl _))) fun s' ⟨hv, hf⟩ =>
      ⟨fun b hb l hl => ?_, hq _ _ _ hQ₂ hf⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesenclast _ _) = _
  rw [aesenclast_st _ _ (roundKey w nr) (by
    rw [hea, hK₂.sched]; exact byte_roundKey _ _ (by omega)), hI₂ b hb l hl, cipher_eq]

end VG.Proof.Gcm.X86_64.StitchAvx8
