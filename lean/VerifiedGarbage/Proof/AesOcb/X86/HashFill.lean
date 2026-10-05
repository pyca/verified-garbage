import VerifiedGarbage.Proof.AesOcb.X86.Nonce

/-!
# AES-OCB on x86: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xor16W_ok`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of in_off toNat_w64 add_ofNat_assoc32
  toNat_ofNat32)

/-- The XOR of the blocks at `P` and `Q`, stored at `D` as four words. -/
def xor2Mem (m : Mem) (P Q D : Addr) : Mem :=
  Proof.Cmac.store4 m D (m.readW P 32 ^^^ m.readW Q 32)
    (m.readW (P + BitVec.ofNat 64 4) 32 ^^^ m.readW (Q + BitVec.ofNat 64 4) 32)
    (m.readW (P + BitVec.ofNat 64 8) 32 ^^^ m.readW (Q + BitVec.ofNat 64 8) 32)
    (m.readW (P + BitVec.ofNat 64 12) 32 ^^^ m.readW (Q + BitVec.ofNat 64 12) 32)

theorem xor2Mem_block (m : Mem) (P Q D : Addr) :
    blockAtMem (xor2Mem m P Q D) D = blockAtMem m P ^^^ blockAtMem m Q := by
  rw [blockAtMem, xor2Mem, Proof.Cmac.bytesAt_store4, Proof.Cmac.xor_words4, ← Proof.Ocb.xor_eq,
    Proof.Ocb.ofBytes_xor (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)]
  rfl

theorem sub1_32 {n : Nat} (h : 1 ≤ n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 n - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat32 hn, toNat_ofNat32 (by decide), toNat_ofNat32 (by omega)]
  omega

theorem beq_zero32 {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n == 0) = decide (n = 0) := by
  by_cases h : n = 0
  · subst h; rfl
  · have : BitVec.ofNat 32 n ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat32 hn] at this)
    rw [show (BitVec.ofNat 32 n == 0) = false from beq_eq_false_iff_ne.mpr this]; simp [h]

/-- The blocks of the associated data at `A`, `al` bytes. -/
structure ABuf (p : Prm) (s : State) (A : BitVec 32) (k : Nat) : Prop where
  fit : A.toNat + k ≤ 2 ^ 32
  w : (⟨w64 A, k⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  stk : (stk p).Disjoint ⟨w64 A, k⟩
  rd : Covers [⟨w64 A, k⟩] (s.rd ++ s.wr)

/-- The regions `hashFill` writes, for slot `i` of the buffer. -/
abbrev fillR (p : Prm) (i : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩, ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩, ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩]

/-- What one `hashFill` leaves. -/
structure FillPost (p : Prm) (A : BitVec 32) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame (fillR p i) t.mem t'.mem
  oh : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * i)) =
    blockAtMem t.mem (w64 (A + BitVec.ofNat 32 (16 * (j + i)))) ^^^ offAt 0 l (j + i + 1)
  fp : slotv t'.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * (i + 1))
  esi : t'.gpr .esi = A + BitVec.ofNat 32 (16 * (j + i + 1))
  edi : t'.gpr .edi = BitVec.ofNat 32 (j + i + 2)
  ebx : t'.gpr .ebx = BitVec.ofNat 32 (c - (i + 1))
  zf : t'.zf = some (decide (i + 1 = c))
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {A : BitVec 32} {l : Block} {j i c : Nat}
    (hi : i < c) (hc : c ≤ 8) (hj : j + i + 2 < 2 ^ 32)
    (hdi : t.gpr .edi = BitVec.ofNat 32 (j + i + 1)) (hsi : t.gpr .esi = A + BitVec.ofNat 32 (16 * (j + i)))
    (hbx : t.gpr .ebx = BitVec.ofNat 32 (c - i)) (hfp : slotv t.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * i))
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i))
    (hA : ABuf p t (A + BitVec.ofNat 32 (16 * (j + i))) 16) :
    WP isa hashFill t (FillPost p A l j i c t) := by
  unfold hashFill
  refine WP.seq (WP.mono (lNtz_ok L E (by omega) (by omega) hdi hl0) fun t₁ P₁ => ?_)
  have E₁ := P₁.env L E
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E₁ (s := lO) (d := ohO) (by decide) (by decide) (.inl (by decide))
  have E₂ : Env p t₂ := E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp]) (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (frame_toMut (by rw [m₂]; exact xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  have fa : Frame (fillR p i) t.mem t₁.mem := P₁.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
  have fb : Frame (fillR p i) t₁.mem t₂.mem := by
    rw [m₂]
    exact (xorMem16_frame _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; simp
  have fr₂ : Frame (fillR p i) t.mem t₂.mem := fa.trans fb
  have oh₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [m₂, xorMem16_block, P₁.val, Proof.Ocb.blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), hoh]
    rfl
  -- what the block reads, in `t₂`
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
      ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans (by
      rw [m₂]
      exact (xorMem16_frame _ _ _ _ _).mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; simp)
  have hfp₂ : t₂.mem.readW (w64 p.W + BitVec.ofNat 64 fpO) 32 = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by
    rw [← hfp, slotv_eq]
    exact f₂.readW (r := ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)) (by decide)
  have g₂' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₂ r h₁, P₁.gpr r h₁ h₂ h₃]
  have si₂ : t₂.gpr .esi = A + BitVec.ofNat 32 (16 * (j + i)) := by
    rw [g₂' _ (by decide) (by decide) (by decide), hsi]
  have di₂ : t₂.gpr .edi = BitVec.ofNat 32 (j + i + 1) := by rw [g₂' _ (by decide) (by decide) (by decide), hdi]
  have bx₂ : t₂.gpr .ebx = BitVec.ofNat 32 (c - i) := by rw [g₂' _ (by decide) (by decide) (by decide), hbx]
  have rd₂' : t₂.rd = t.rd := by rw [rd₂, P₁.rd]
  have wr₂' : t₂.wr = t.wr := by rw [wr₂, P₁.wr]
  generalize hA' : A + BitVec.ofNat 32 (16 * (j + i)) = A' at si₂ hA ⊢
  have aA : ∀ {k : Nat}, k < 16 → w64 (A' + BitVec.ofNat 32 k) = w64 A' + BitVec.ofNat 64 k := fun hk =>
    w64_add (by have := hA.fit; omega)
  have aA0 : w64 (A' + BitVec.ofNat 32 0) = w64 A' := by rw [aA (by decide)]; exact BitVec.add_zero _
  have rA : ∀ {k : Nat}, k + 4 ≤ 16 → InRegions (t₂.rd ++ t₂.wr) (w64 A' + BitVec.ofNat 64 k) 4 := fun hk => by
    rw [rd₂', wr₂']; exact in_off hA.rd hk (by decide)
  have rA0 : InRegions (t₂.rd ++ t₂.wr) (w64 A') 4 := by simpa using rA (k := 0) (by decide)
  have hAk : (w64 A').toNat + 16 ≤ 2 ^ 32 := by rw [toNat_w64]; exact hA.fit
  have aQ : ∀ {k : Nat}, k < 16 → w64 (p.W + BitVec.ofNat 32 (bufO + 16 * i) + BitVec.ofNat 32 k) =
      w64 p.W + BitVec.ofNat 64 (bufO + 16 * i + k) := fun hk => by
    rw [add_ofNat_assoc32]; exact L.aW (by simp only [bufO]; omega)
  have aQ0 : w64 (p.W + BitVec.ofNat 32 (bufO + 16 * i) + BitVec.ofNat 32 0) = w64 p.W + BitVec.ofNat 64 (bufO + 16 * i) := by
    rw [aQ (by decide)]; rfl
  obtain ⟨t₃, run₃, m₃, si₃, di₃, bx₃, zf₃, g₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa ([.mov .edx (slot fpO)] ++
      [0, 4, 8, 12].flatMap (fun k => [.mov .eax (.mem (at_ .esi k)), .alu .xor .eax (slot (ohO + k)),
        .store (at_ .edx k) .eax]) ++
      [.alu .add .edx (imm 16), .store (at_ .ebp fpO) .edx, .alu .add .esi (imm 16), .alu .add .edi (imm 1),
       .alu .sub .ebx (imm 1)]) t₂ = some t₃ ∧
      t₃.mem = (xor2Mem t₂.mem (w64 A') (w64 p.W + BitVec.ofNat 64 ohO)
        (w64 p.W + BitVec.ofNat 64 (bufO + 16 * i))).writeW (w64 p.W + BitVec.ofNat 64 fpO)
          (p.W + BitVec.ofNat 32 (bufO + 16 * i) + BitVec.ofNat 32 16) ∧
      t₃.gpr .esi = A' + BitVec.ofNat 32 16 ∧ t₃.gpr .edi = BitVec.ofNat 32 (j + i + 1) + BitVec.ofNat 32 1 ∧
      t₃.gpr .ebx = BitVec.ofNat 32 (c - i) - BitVec.ofNat 32 1 ∧
      t₃.zf = some (BitVec.ofNat 32 (c - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → r ≠ .esi → r ≠ .edi → t₃.gpr r = t₂.gpr r) ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by grun [List.flatMap_cons, List.flatMap_nil, E₂.ebp, L.aW, E₂.perm.wR, E₂.perm.wW, hfp₂, si₂, di₂,
      bx₂, aA, aA0, rA, rA0, aQ, aQ0, (readW_XW L hAk hA.w)], ?_, by gregs [si₂], by gregs [di₂], by gregs [bx₂],
      by gmems [bx₂], fun r h₁ h₂ h₃ h₄ h₅ => by gregs [h₁, h₂, h₃, h₄, h₅], by gmems [], by gmems []⟩
    gmems [(readW_XW L hAk hA.w)]
    simp only [xor2Mem, Proof.Cmac.store4, add_ofNat_assoc, Nat.add_zero, Nat.reduceAdd,
      show w64 A' + 0#64 = w64 A' from BitVec.add_zero _]
  refine WP.of_runBlock ⟨t₃, by simpa only [List.append_assoc] using runBlock_app_of run₂ run₃, ?_⟩
  have fQ : ∀ M : Mem, Frame [⟨w64 p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩] M
      (xor2Mem M (w64 A') (w64 p.W + BitVec.ofNat 64 ohO) (w64 p.W + BitVec.ofNat 64 (bufO + 16 * i))) :=
    fun M => Proof.Cmac.frame_store4 _ _ _ _ _
  have fF : ∀ (M : Mem) (v : BitVec 32), Frame [⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩] M
      (M.writeW (w64 p.W + BitVec.ofNat 64 fpO) v) :=
    fun M v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have dQ : ∀ {d k : Nat}, d + k ≤ bufO → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint
      ⟨w64 p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩ := fun h => by
    simp only [bufO] at h ⊢; exact Lay.w_w (.inl (by omega)) (by omega) (by omega)
  have dF : ∀ {d k : Nat}, d + k ≤ fpO ∨ fpO + 4 ≤ d → d + k ≤ 2560 →
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩ :=
    fun h h' => Lay.w_w h h' (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_, by rw [rd₃, rd₂'], by rw [wr₃, wr₂']⟩
  · rw [m₃]
    exact (fr₂.trans ((fQ _).mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
      ((fF _ _).mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
  · rw [m₃, Proof.Ocb.blockAtMem_frame (fF _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dF (by decide) (by decide)),
      Proof.Ocb.blockAtMem_frame (fQ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dQ (by decide)), oh₂]
  · rw [m₃, Proof.Ocb.blockAtMem_frame (fF _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dF (.inr (by simp only [fpO, bufO]; omega)) (by simp only [bufO]; omega)),
      xor2Mem_block, oh₂, Proof.Ocb.blockAtMem_frame f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hA.w.sub_right (Lay.wSub (by decide))), hA']
  · rw [slotv_eq, m₃, Mem.readW_writeW_self32, add_ofNat_assoc32, show bufO + 16 * i + 16 = bufO + 16 * (i + 1) by omega]
  · rw [si₃, ← hA', add_ofNat_assoc32, show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega]
  · rw [di₃, ← BitVec.ofNat_add]
  · rw [bx₃, sub1_32 (by omega) (by omega), show c - i - 1 = c - (i + 1) by omega]
  · rw [zf₃, sub1_32 (by omega) (by omega), beq_zero32 (by omega)]; congr 2; exact propext ⟨fun h => by omega,
      fun h => by omega⟩
  · rw [g₃ r h₁ h₂ h₄ h₅ h₆, g₂' r h₁ h₃ h₄]

end VG.Proof.AesOcb.X86
