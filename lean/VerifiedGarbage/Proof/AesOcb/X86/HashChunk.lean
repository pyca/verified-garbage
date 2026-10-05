import VerifiedGarbage.Proof.AesOcb.X86.HashFill

/-!
# AES-OCB on x86: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`),
`esi` points at block `j`, `edi` is `j + 1`, and `m − j` is kept in `W`.
`hashChunk` takes `c = min(8, m − j)` blocks: fills the buffer with each
block XORed with its offset (`fill_ok`), enciphers the buffer, adds it to
the sum (`hashSum_ok`), and leaves `HInv` at `j + c` (`hashChunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt hsum)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of in_off toNat_w64 add_ofNat_assoc32
  toNat_ofNat32 toNat_add32 covers_off length_bytesAt)

/-- What `HASH` writes: the sum, `L_{ntz(i)}`, the offset, `i`, the
variables at `[264, 280)`, the buffer and the working space of the functions
called, and the stack. -/
abbrev hashR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩, ⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩, wC p.W, stk p]

/-- A part of `W` within `hashR`. -/
theorem inHashR (p : Prm) {d k : Nat}
    (h : 48 ≤ d ∧ d + k ≤ 64 ∨ 96 ≤ d ∧ d + k ≤ 112 ∨ 160 ≤ d ∧ d + k ≤ 176 ∨ 220 ≤ d ∧ d + k ≤ 224 ∨
      264 ≤ d ∧ d + k ≤ 280 ∨ 384 ≤ d ∧ d + k ≤ 2560) :
    ∃ r' ∈ hashR p, Region.Sub ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | h | h | h | h | h
  · exact ⟨_, by simp, Offset.sub _ (e := 48) (k := 16) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 96) (k := 16) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 160) (k := 16) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 220) (k := 4) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 264) (k := 16) (by omega) (by omega)⟩
  · exact ⟨wC p.W, by simp, Offset.sub _ (by omega) (by omega)⟩

theorem hashR_wR {p : Prm} {m m' : Mem} (h : Frame (hashR p) m m') : Frame (wR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inW_wR p (.inl (by decide))
  · exact inW_wR p (.inl (by decide))
  · exact inW_wR p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `HASH` needs of its start, `s₀`: the key context's cipher and
`L_*`, and the associated data. -/
structure HCtx (p : Prm) (ciph : Cipher) (l : Block) (a : List Byte) (s₀ : State) : Prop where
  lay : Lay p
  ciph : ctxCiph s₀.mem (w64 p.K) p.R = ciph
  lstar : ctxLstar s₀.mem (w64 p.K) = l
  aad : bytesAt s₀.mem (w64 p.A) p.al = a

/-- What holds of `HASH` of `a` after `j` of its whole blocks, from the
state `s₀` at its start. -/
structure HInv (p : Prm) (ciph : Cipher) (l : Block) (a : List Byte) (s₀ s : State) (j : Nat) : Prop where
  env : Env p s
  frame : Frame (hashR p) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : j ≤ p.al / 16
  sum : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  oh : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l j
  esi : s.gpr .esi = p.A + BitVec.ofNat 32 (16 * j)
  edi : s.gpr .edi = BitVec.ofNat 32 (j + 1)
  hl : slotv s.mem p.W hlO = BitVec.ofNat 32 (p.al / 16 - j)
  rest : slotv s.mem p.W restO = BitVec.ofNat 32 (p.al % 16)
  l0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0

namespace HCtx

variable {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : HCtx p ciph l a s₀)
include C

theorem len : a.length = p.al := by rw [← C.aad, length_bytesAt]

/-- Block `i` of the associated data, in a state after `s₀`. -/
theorem blk {m : Mem} (h : Frame (mutR p) s₀.mem m) {i : Nat} (hi : i < p.al / 16) :
    blockAtMem m (w64 (p.A + BitVec.ofNat 32 (16 * i))) = blockAt a i := by
  have L := C.lay
  rw [w64_add (by have := L.aw; omega), ← C.aad, ← aad_mut L h, Proof.Ocb.blockAt_bytesAt _ _ (by omega)]

/-- Block `i` of the associated data, for `hashFill`. -/
theorem abuf {s : State} (E : Env p s) {i : Nat} (hi : i < p.al / 16) :
    ABuf p s (p.A + BitVec.ofNat 32 (16 * i)) 16 := by
  have L := C.lay
  have hA := L.aw
  have a16 : w64 (p.A + BitVec.ofNat 32 (16 * i)) = w64 p.A + BitVec.ofNat 64 (16 * i) := w64_add (by omega)
  have sub : Region.Sub ⟨w64 (p.A + BitVec.ofNat 32 (16 * i)), 16⟩ ⟨w64 p.A, p.al⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega)
  refine ⟨by rw [toNat_add32 (by omega)]; omega, L.a_w.sub_left sub, L.ba.sub_right sub, ?_⟩
  rw [a16]; exact covers_off E.perm.aad (by omega) (by omega)

theorem ciph' {m : Mem} (h : Frame (mutR p) s₀.mem m) : ctxCiph m (w64 p.K) p.R = ciph := by
  rw [ctxCiph_mut C.lay h, C.ciph]

end HCtx

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (p : Prm) (ciph : Cipher) (l : Block) (a : List Byte) (s₀ : State) (j c : Nat) (t : State)
    (i : Nat) : Prop where
  env : Env p t
  frame : Frame (hashR p) s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  esi : t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (j + i))
  edi : t.gpr .edi = BitVec.ofNat 32 (j + i + 1)
  ebx : t.gpr .ebx = BitVec.ofNat 32 (c - i)
  fp : slotv t.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * i)
  cnt : slotv t.mem p.W cntO = BitVec.ofNat 32 c
  oh : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)
  buf : ∀ k < i, blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * k)) =
    blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)
  sum : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  hl : slotv t.mem p.W hlO = BitVec.ofNat 32 (p.al / 16 - j)
  rest : slotv t.mem p.W restO = BitVec.ofNat 32 (p.al % 16)
  l0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0

theorem fill_step {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : HCtx p ciph l a s₀)
    {j c : Nat} (hc : c ≤ 8) (hjc : j + c ≤ p.al / 16) {t : State} {i : Nat} (hi : i < c)
    (F : FillInv p ciph l a s₀ j c t i) :
    WP isa hashFill t fun t' => FillInv p ciph l a s₀ j c t' (i + 1) ∧ t'.zf = some (decide (i + 1 = c)) := by
  have L := C.lay
  have hal := L.al32
  refine WP.mono (hashFill_ok L F.env hi hc (by omega) F.edi F.esi F.ebx F.fp F.l0 F.oh
    (C.abuf F.env (i := j + i) (by omega))) fun t' P => ⟨?_, P.zf⟩
  have hfr : Frame (hashR p) t.mem t'.mem := P.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact inHashR p (.inr (.inl ⟨by decide, by decide⟩))
    · exact inHashR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
    · exact inHashR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by simp only [bufO]; omega, by simp only [bufO]; omega⟩)))))
    · exact inHashR p (.inr (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩)))))
  have dis : ∀ {d k : Nat}, (d + k ≤ lO ∨ lO + 16 ≤ d) → (d + k ≤ kO ∨ kO + 4 ≤ d) → (d + k ≤ ohO ∨ ohO + 16 ≤ d) →
      (d + k ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) → (d + k ≤ fpO ∨ fpO + 4 ≤ d) → d + k ≤ 2560 →
      ∀ r ∈ fillR p i, (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h₁ h₂ h₃ h₄ h₅ h₆ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w h₁ h₆ (by decide)
    · exact Lay.w_w h₂ h₆ (by decide)
    · exact Lay.w_w h₃ h₆ (by decide)
    · exact Lay.w_w h₄ h₆ (by simp only [bufO]; omega)
    · exact Lay.w_w h₅ h₆ (by decide)
  have keepB : ∀ {d : Nat}, (d + 16 ≤ lO ∨ lO + 16 ≤ d) → (d + 16 ≤ kO ∨ kO + 4 ≤ d) →
      (d + 16 ≤ ohO ∨ ohO + 16 ≤ d) → (d + 16 ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) →
      (d + 16 ≤ fpO ∨ fpO + 4 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun h₁ h₂ h₃ h₄ h₅ h₆ => Proof.Ocb.blockAtMem_frame P.frame (dis h₁ h₂ h₃ h₄ h₅ h₆)
  have keepW : ∀ {d : Nat}, (d + 4 ≤ lO ∨ lO + 16 ≤ d) → (d + 4 ≤ kO ∨ kO + 4 ≤ d) →
      (d + 4 ≤ ohO ∨ ohO + 16 ≤ d) → (d + 4 ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) →
      (d + 4 ≤ fpO ∨ fpO + 4 ≤ d) → d + 4 ≤ 2560 → slotv t'.mem p.W d = slotv t.mem p.W d :=
    fun h₁ h₂ h₃ h₄ h₅ h₆ => P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _)
      (dis h₁ h₂ h₃ h₄ h₅ h₆) (by decide)
  refine
    { env := F.env.mut L (by rw [P.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          F.env.ebp]) (by rw [P.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          F.env.esp]) P.rd P.wr (wR_mut (hashR_wR hfr))
      frame := F.frame.trans hfr
      rd := by rw [P.rd, F.rd]
      wr := by rw [P.wr, F.wr]
      esi := by rw [P.esi, show j + i + 1 = j + (i + 1) by omega]
      edi := by rw [P.edi, show j + i + 2 = j + (i + 1) + 1 by omega]
      ebx := P.ebx
      fp := P.fp
      cnt := by rw [keepW (by decide) (by decide) (by decide) (by simp only [cntO, bufO]; omega) (by decide)
        (by decide), F.cnt]
      oh := by rw [P.oh, show j + i + 1 = j + (i + 1) by omega]
      buf := fun k hk => ?_
      sum := by rw [keepB (by decide) (by decide) (by decide) (by simp only [sumO, bufO]; omega) (by decide)
        (by decide), F.sum]
      hl := by rw [keepW (by decide) (by decide) (by decide) (by simp only [hlO, bufO]; omega) (by decide)
        (by decide), F.hl]
      rest := by rw [keepW (by decide) (by decide) (by decide) (by simp only [restO, bufO]; omega) (by decide)
        (by decide), F.rest]
      l0 := by rw [keepB (by decide) (by decide) (by decide) (by simp only [l0O, bufO]; omega) (by decide)
        (by decide), F.l0] }
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [keepB (by simp only [lO, bufO]; omega) (by simp only [kO, bufO]; omega) (by simp only [ohO, bufO]; omega)
      (by omega) (by simp only [fpO, bufO]; omega) (by simp only [bufO]; omega), F.buf k hk']
  · obtain rfl : k = i := by omega
    rw [P.buf, C.blk (wR_mut (hashR_wR F.frame)) (by omega)]

theorem fill_ok {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : HCtx p ciph l a s₀)
    {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ p.al / 16) {t : State}
    (F : FillInv p ciph l a s₀ j c t 0) :
    WP isa (.loop hashFill .ne) t fun t' => FillInv p ciph l a s₀ j c t' c := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ FillInv p ciph l a s₀ j c u i) ?_ (c - 0) _
    ⟨0, rfl, hc0, F⟩
  rintro k u ⟨i, rfl, hi, F⟩
  refine WP.mono (fill_step C hc hjc hi F) fun u' ⟨F', hz⟩ => ?_
  by_cases he : i + 1 = c
  · left; exact ⟨(eval_ne hz).trans (by simp [he]), he ▸ F'⟩
  · right; exact ⟨(eval_ne hz).trans (by simp [he]), c - (i + 1), by omega, i + 1, rfl, by omega, F'⟩

end VG.Proof.AesOcb.X86
