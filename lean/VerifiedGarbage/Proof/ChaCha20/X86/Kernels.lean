import VerifiedGarbage.Proof.ChaCha20.X86.Quad

/-!
# ChaCha20 on x86 (32-bit): the quarter rounds of the four-block code

`sse2Ok` and `ssse3Ok` are what the four-block code needs of its quarter
round (`Quad.KernelOk`): `vqr` needs nothing; `vqr3` needs its `pshufb`
controls in `buf[288, 320)`, which `masks` stores there and the four-block
code never writes.
-/

namespace VG.Proof.ChaCha20.X86.Kernels

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Impl.ChaCha20.X86.Xor
open VG.Proof.ChaCha20.X86.Quad (KernelOk kR bufR in_buf out_buf w32_other)

/-- `vqr`, in the baseline ISA. -/
def sse2Ok : KernelOk sse2 where
  Inv _ _ := True
  inv_frame _ _ _ := trivial
  qr_ok hab hac had hbc hbd hcd ha hb hc hd s _ _ _ := vqr_ok hab hac had hbc hbd hcd ha hb hc hd s
  init_ok _ _ _ := WP.block_nil ⟨trivial, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩

/-- `vqr3`'s controls are in `buf`. -/
def Masks (buf : Addr) (m : Mem) : Prop :=
  m.readW (buf + BitVec.ofNat 64 rot16Off) 128 = mask16 ∧ m.readW (buf + BitVec.ofNat 64 rot8Off) 128 = mask8

theorem maskWords_getD : ∀ k, k < 8 → (maskWords.getD k (0, 0)).2 = 288 + 4 * k := by decide

theorem masks_eq : masks = (List.range 8).flatMap fun k =>
    [.mov .eax (.imm (maskWords.getD k (0, 0)).1), .store (at_ .edi (maskWords.getD k (0, 0)).2) .eax] := rfl

/-- After the stores of the first `n` words of the controls. -/
structure MI (buf : Addr) (s₀ : State) (n : Nat) (s : State) : Prop where
  words : ∀ k, k < n → s.mem.readW (buf + BitVec.ofNat 64 (288 + 4 * k)) 32 = (maskWords.getD k (0, 0)).1
  frame : Frame [kR buf] s₀.mem s.mem
  keep : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem mask_dwords (buf : Addr) (m : Mem) {o : Nat} {v : BitVec 128}
    (h : ∀ i, i < 4 → m.readW (buf + BitVec.ofNat 64 (o + 4 * i)) 32 = dword v i) :
    m.readW (buf + BitVec.ofNat 64 o) 128 = v := by
  have e : ∀ i, i < 4 → dword (m.readW (buf + BitVec.ofNat 64 o) 128) i = dword v i := fun i hi => by
    rw [dword_readW _ _ hi, Offset.add_add]; exact h i hi
  exact ext_dword (e 0 (by decide)) (e 1 (by decide)) (e 2 (by decide)) (e 3 (by decide))

/-- `vqr3`, with SSSE3. -/
def ssse3Ok : KernelOk ssse3 where
  Inv := Masks
  inv_frame {buf m m' rs} h hf hd :=
    ⟨by rw [hf.readW (r := kR buf) (Offset.contains _ (by decide) (by decide) (by decide)) hd (by decide)]
        exact h.1,
     by rw [hf.readW (r := kR buf) (Offset.contains _ (by decide) (by decide) (by decide)) hd (by decide)]
        exact h.2⟩
  qr_ok := fun {buf} {_ _ _ _} hab hac had hbc hbd hcd ha hb hc hd s he hw hi =>
    vqr3_ok hab hac had hbc hbd hcd ha hb hc hd s (he _ (by decide)) (he _ (by decide))
      (in_buf (d := rot16Off) hw (by decide)) (in_buf (d := rot8Off) hw (by decide)) hi.1 hi.2
  init_ok {buf} s he hw := by
    show WP isa (.block masks) s _
    rw [masks_eq]
    refine WP.mono (wp_range_flatMap (M := isa) (MI buf s) (fun k s' hk h => ?_) 8 (Nat.le_refl _) s
      ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩) fun s' h => ?_
    · have hd := maskWords_getD k hk
      have e : addr (s.gpr .edi) (maskWords.getD k (0, 0)).2 = buf + BitVec.ofNat 64 (288 + 4 * k) := by
        rw [hd]; exact he _ (by omega)
      refine Wp.wp_movi fun s₁ u₁ => ?_
      refine Wp.wp_stm (by rw [u₁.other _ (by decide), h.keep _ (by decide)])
        (by rw [e, u₁.wr, h.wr]; exact out_buf hw (by omega)) fun s₂ u₂ => WP.block_nil ?_
      have hm : s₂.mem = s'.mem.writeW (buf + BitVec.ofNat 64 (288 + 4 * k)) (maskWords.getD k (0, 0)).1 := by
        rw [u₂.mem, e, u₁.gpr, u₁.mem]
      refine ⟨fun j hj => ?_, ?_, fun r hr => ?_, by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr]⟩
      · rw [hm]
        by_cases hjk : j = k
        · subst hjk; exact Mem.readW_writeW_self32 _ _ _
        · rw [w32_other _ _ _ (by omega) (by omega) (by omega)]; exact h.words j (by omega)
      · rw [hm]
        exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by decide))
      · rw [u₂.gpr, u₁.other r hr, h.keep r hr]
    · refine ⟨⟨mask_dwords buf s'.mem (o := 288) fun i hi => ?_,
        mask_dwords buf s'.mem (o := 304) fun i hi => ?_⟩, h.frame, h.keep, h.rd, h.wr⟩
      · rw [h.words i (by omega)]
        rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
      · rw [show 304 + 4 * i = 288 + 4 * (i + 4) by omega, h.words (i + 4) (by omega)]
        rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.ChaCha20.X86.Kernels
