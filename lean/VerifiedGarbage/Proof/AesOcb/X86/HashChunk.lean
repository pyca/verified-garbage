import VerifiedGarbage.Proof.AesOcb.X86.HashFill
import VerifiedGarbage.Proof.Ocb.Sum

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
open VG.Proof.Ocb (offAt hsum sumOf)
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

/-! ## Adding the buffer to the sum -/

theorem hashSum_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {c : Nat} (hc0 : 0 < c) (hc : c ≤ 8)
    (hcnt : slotv t.mem p.W cntO = BitVec.ofNat 32 c) {g : Nat → Block}
    (hg : ∀ k < c, blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * k)) = g k) :
    WP isa hashSum t fun t' => Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem t'.mem ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) =
        sumOf (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO)) g c ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [slotv_eq] at hcnt
  obtain ⟨t₁, run₁, bx₁, dx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .ebx (slot cntO), .mov .edx (.reg .ebp),
      .alu .add .edx (imm bufO)] t = some t₁ ∧ t₁.gpr .ebx = BitVec.ofNat 32 (c - 0) ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 (bufO + 16 * 0) ∧
      (∀ r, r ≠ .ebx → r ≠ .edx → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hcnt], by gregs [hcnt, Nat.sub_zero], by gregs [E.ebp],
      fun r h₁ h₂ => by gregs [h₁, h₂], by gmems [], by gmems [], by gmems []⟩
  unfold hashSum
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ Env p u ∧
      u.gpr .edx = p.W + BitVec.ofNat 32 (bufO + 16 * i) ∧ u.gpr .ebx = BitVec.ofNat 32 (c - i) ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem u.mem ∧
      blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 sumO) =
        sumOf (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO)) g i ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → u.gpr r = t.gpr r) ∧ u.rd = t.rd ∧ u.wr = t.wr)
    ?_ (c - 0) _ ⟨0, rfl, hc0, E.keep (by rw [g₁ _ (by decide) (by decide)]) (by rw [g₁ _ (by decide) (by decide)])
      rd₁ wr₁ m₁, dx₁, bx₁, by rw [m₁]; exact Frame.refl _ _, by rw [m₁]; rfl, fun r _ h₂ h₃ => g₁ r h₂ h₃, rd₁, wr₁⟩
  rintro k u ⟨i, rfl, hi, Eu, dx, bx, fr, sum, gu, rd, wr⟩
  obtain ⟨u₁, run₁', m₁', g₁', rd₁', wr₁'⟩ := xor16P_ok L Eu (b := .edx) (by decide) dx
    (e := bufO + 16 * i) (d := sumO) (by simp only [bufO]; omega) (by decide) (.inr (by simp only [bufO, sumO]; omega))
  have dx₁ : u₁.gpr .edx = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [g₁' _ (by decide), dx]
  have bx₁ : u₁.gpr .ebx = BitVec.ofNat 32 (c - i) := by rw [g₁' _ (by decide), bx]
  obtain ⟨u₂, run₂, dx₂, bx₂, zf₂, g₂, m₂, rd₂, wr₂⟩ : ∃ u₂, runBlock isa [.alu .add .edx (imm 16),
      .alu .sub .ebx (imm 1)] u₁ = some u₂ ∧ u₂.gpr .edx = p.W + BitVec.ofNat 32 (bufO + 16 * (i + 1)) ∧
      u₂.gpr .ebx = BitVec.ofNat 32 (c - (i + 1)) ∧ u₂.zf = some (decide (i + 1 = c)) ∧
      (∀ r, r ≠ .ebx → r ≠ .edx → u₂.gpr r = u₁.gpr r) ∧ u₂.mem = u₁.mem ∧ u₂.rd = u₁.rd ∧ u₂.wr = u₁.wr := by
    refine ⟨_, by grun [], ?_, ?_, ?_, fun r h₁ h₂ => by gregs [h₁, h₂], by gmems [], by gmems [], by gmems []⟩
    · gregs [dx₁]; rw [add_ofNat_assoc32, show bufO + 16 * i + 16 = bufO + 16 * (i + 1) by omega]
    · gregs [bx₁]; rw [sub1_32 (by omega) (by omega), show c - i - 1 = c - (i + 1) by omega]
    · gmems [bx₁]
      rw [sub1_32 (by omega) (by omega), beq_zero32 (by omega)]
      exact congrArg some (decide_eq_decide.mpr (by omega))
  refine WP.of_runBlock ⟨u₂, runBlock_app_of run₁' run₂, ?_⟩
  have Eu₂ : Env p u₂ := Eu.mut L (by rw [g₂ _ (by decide) (by decide), g₁' _ (by decide), Eu.ebp])
    (by rw [g₂ _ (by decide) (by decide), g₁' _ (by decide), Eu.esp]) (by rw [rd₂, rd₁']) (by rw [wr₂, wr₁'])
    (frame_toMut (by rw [m₂, m₁']; exact xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have hbuf : blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * i)) = g i := by
    rw [Proof.Ocb.blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inr (by simp only [bufO, sumO]; omega)) (by simp only [bufO]; omega) (by decide),
      hg i hi]
  have fr' : Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem u₂.mem := by
    rw [m₂, m₁']; exact fr.trans (xorMem16_frame _ _ _ _ _)
  have sum' : blockAtMem u₂.mem (w64 p.W + BitVec.ofNat 64 sumO) =
      sumOf (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO)) g (i + 1) := by
    rw [m₂, m₁', xorMem16_block, sum, hbuf]; rfl
  have gu' : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → u₂.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₂ r h₂ h₃, g₁' r h₁, gu r h₁ h₂ h₃]
  by_cases he : i + 1 = c
  · left
    exact ⟨(eval_ne zf₂).trans (by simp [he]), fr', he ▸ sum', gu', by rw [rd₂, rd₁', rd], by rw [wr₂, wr₁', wr]⟩
  · right
    exact ⟨(eval_ne zf₂).trans (by simp [he]), c - (i + 1), by omega, i + 1, rfl, by omega, Eu₂, dx₂, bx₂, fr',
      sum', gu', by rw [rd₂, rd₁', rd], by rw [wr₂, wr₁', wr]⟩

/-! ## A chunk -/

theorem sub32' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat32 ha, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  omega

/-- `HInv` after code that keeps the registers it holds and changes only
words of `W` it does not mention. -/
theorem HInv.of_keep {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ s s' : State} {j : Nat}
    (H : HInv p ciph l a s₀ s j) (hg : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : HInv p ciph l a s₀ s' j :=
  { H with
    env := H.env.keep (by rw [hg _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [hg _ (by decide) (by decide) (by decide) (by decide)]) hrd hwr hm
    frame := by rw [hm]; exact H.frame
    rd := by rw [hrd, H.rd]
    wr := by rw [hwr, H.wr]
    sum := by rw [hm, H.sum]
    oh := by rw [hm, H.oh]
    esi := by rw [hg _ (by decide) (by decide) (by decide) (by decide), H.esi]
    edi := by rw [hg _ (by decide) (by decide) (by decide) (by decide), H.edi]
    hl := by rw [hm, H.hl]
    rest := by rw [hm, H.rest]
    l0 := by rw [hm, H.l0] }

/-- `min(8, m − j)` in `ebx`. -/
theorem chunkHead_ok {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : HCtx p ciph l a s₀)
    {t : State} {j : Nat} (H : HInv p ciph l a s₀ t j) :
    WP isa (.seq (.block [.mov .ebx (slot hlO), .alu .cmp .ebx (imm 8)])
      (.ite .b (.block []) (.block [.mov .ebx (imm 8)]))) t fun t' =>
        HInv p ciph l a s₀ t' j ∧ t'.gpr .ebx = BitVec.ofNat 32 (min 8 (p.al / 16 - j)) := by
  have L := C.lay
  have hal := L.al32
  have hl := H.hl
  simp only [slotv_eq] at hl
  obtain ⟨t₁, run₁, bx₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .ebx (slot hlO), .alu .cmp .ebx (imm 8)] t =
      some t₁ ∧ t₁.gpr .ebx = BitVec.ofNat 32 (p.al / 16 - j) ∧ t₁.cf = some (decide (p.al / 16 - j < 8)) ∧
      (∀ r, r ≠ .ebx → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [H.env.ebp, L.aW, H.env.perm.wR, hl], by gregs [hl], ?_, fun r h => by gregs [h], by gmems [],
      by gmems [], by gmems []⟩
    gmems [hl, toNat_ofNat32 (show p.al / 16 - j < 2 ^ 32 by omega), toNat_ofNat32 (show 8 < 2 ^ 32 by decide)]
  have H₁ := H.of_keep (fun r _ h₂ _ _ => g₁ r h₂) m₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (p.al / 16 - j < 8)) (eval_b cf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hlt : p.al / 16 - j < 8 := of_decide_eq_true hb
    rw [show min 8 (p.al / 16 - j) = p.al / 16 - j by omega]
    exact ⟨H₁, bx₁⟩
  · have hge : ¬ p.al / 16 - j < 8 := of_decide_eq_false hb
    obtain ⟨t₂, run₂, bx₂, g₂, m₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa [.mov .ebx (imm 8)] t₁ = some t₂ ∧
        t₂.gpr .ebx = BitVec.ofNat 32 8 ∧ (∀ r, r ≠ .ebx → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧ t₂.rd = t₁.rd ∧
        t₂.wr = t₁.wr :=
      ⟨_, by grun [], by gregs [], fun r h => by gregs [h], by gmems [], by gmems [], by gmems []⟩
    refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
    rw [show min 8 (p.al / 16 - j) = 8 by omega]
    exact ⟨H₁.of_keep (fun r _ h₂ _ _ => g₂ r h₂) m₂ rd₂ wr₂, bx₂⟩

/-- A chunk of `c` blocks from `ebx`. -/
theorem chunkRest_ok (v : BlocksImpl) {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) {t : State} {j c : Nat} (H : HInv p ciph l a s₀ t j) (hc0 : 0 < c) (hc : c ≤ 8)
    (hjc : j + c ≤ p.al / 16) (hbx : t.gpr .ebx = BitVec.ofNat 32 c) :
    WP isa (.seq (.block [.store (at_ .ebp cntO) .ebx, .mov .eax (.reg .ebp), .alu .add .eax (imm bufO),
          .store (at_ .ebp fpO) .eax])
        (.seq (.loop hashFill .ne)
          (.seq (callBlocks (callees v).enc [.mov .edx (.reg .ebp), .alu .add .edx (imm bufO), .mov .ebx (slot cntO)])
            (.seq hashSum
              (.block [.mov .eax (slot hlO), .alu .sub .eax (slot cntO), .store (at_ .ebp hlO) .eax]))))) t
      fun t' => HInv p ciph l a s₀ t' (j + c) ∧ t'.zf = some (decide (p.al / 16 - (j + c) = 0)) := by
  have L := C.lay
  have hal := L.al32
  have E := H.env
  -- the chunk's count and the buffer's start
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.store (at_ .ebp cntO) .ebx, .mov .eax (.reg .ebp),
      .alu .add .eax (imm bufO), .store (at_ .ebp fpO) .eax] t = some t₁ ∧
      t₁.mem = (t.mem.writeW (w64 p.W + BitVec.ofNat 64 cntO) (BitVec.ofNat 32 c)).writeW
        (w64 p.W + BitVec.ofNat 64 fpO) (p.W + BitVec.ofNat 32 bufO) ∧
      (∀ r, r ≠ .eax → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wW, hbx], by gmems [E.ebp, hbx], fun r h => by gregs [h], by gmems [],
      by gmems []⟩
  have fr₁ : Frame (hashR p) t.mem t₁.mem := by
    rw [m₁]
    have hm : (⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩ : Region) ∈ hashR p := by simp
    exact ((Frame.refl _ _).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 272) (n := 4) (by decide)
      (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 268) (n := 4) (by decide)
      (by decide) (by decide))
  have kW₁ : ∀ {d : Nat}, (d + 4 ≤ 268 ∨ 276 ≤ d) → d + 4 ≤ 2560 → slotv t₁.mem p.W d = slotv t.mem p.W d :=
    fun h h' => by
      rw [slotv_eq, slotv_eq, m₁, Mem.readW_writeW_sep (Offset.sep _ (by simp only [fpO]; omega) (by omega) (by decide))
        (by decide), Mem.readW_writeW_sep (Offset.sep _ (by simp only [cntO]; omega) (by omega) (by decide)) (by decide)]
  have kB₁ : ∀ {d : Nat}, d + 16 ≤ 268 → blockAtMem t₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) := fun h =>
    Proof.Ocb.blockAtMem_frame (rs := [⟨w64 p.W + BitVec.ofNat 64 268, 8⟩]) (by
      rw [m₁]
      have hm := List.mem_singleton_self (⟨w64 p.W + BitVec.ofNat 64 268, 8⟩ : Region)
      exact ((Frame.refl _ _).writeW hm _ (Offset.contains _ (e := 268) (k := 8) (d := 272) (n := 4) (by decide)
        (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 268) (k := 8) (d := 268) (n := 4) (by decide)
        (by decide) (by decide))) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  have F₀ : FillInv p ciph l a s₀ j c t₁ 0 :=
    { env := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
        (wR_mut (hashR_wR fr₁))
      frame := H.frame.trans fr₁
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      esi := by rw [g₁ _ (by decide), H.esi, Nat.add_zero]
      edi := by rw [g₁ _ (by decide), H.edi]
      ebx := by rw [g₁ _ (by decide), hbx, Nat.sub_zero]
      fp := by rw [slotv_eq, m₁, Mem.readW_writeW_self32]
      cnt := by
        rw [slotv_eq, m₁, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
          Mem.readW_writeW_self32]
      oh := by rw [kB₁ (by decide), H.oh, Nat.add_zero]
      buf := fun k hk => absurd hk (Nat.not_lt_zero _)
      sum := by rw [kB₁ (by decide), H.sum]
      hl := by rw [kW₁ (.inl (by decide)) (by decide), H.hl]
      rest := by rw [kW₁ (.inr (by decide)) (by decide), H.rest]
      l0 := by rw [kB₁ (by decide), H.l0] }
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (fill_ok C hc0 hc hjc F₀) fun t₂ F => ?_)
  -- the call
  have hcnt₂ := F.cnt
  simp only [slotv_eq] at hcnt₂
  have hargs : ∃ s₁, runBlock isa [.mov .edx (.reg .ebp), .alu .add .edx (imm bufO), .mov .ebx (slot cntO)] t₂ =
      some s₁ ∧ s₁.gpr .edx = p.W + BitVec.ofNat 32 bufO ∧ s₁.gpr .ebx = BitVec.ofNat 32 c ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = t₂.gpr r) ∧ s₁.mem = t₂.mem ∧
      s₁.rd = t₂.rd ∧ s₁.wr = t₂.wr :=
    ⟨_, by grun [F.env.ebp, L.aW, F.env.perm.wR, hcnt₂], by gregs [F.env.ebp], by gregs [hcnt₂],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L F.env hargs
    (DReg.w L F.env (d := bufO) (n := c) (by simp only [bufO, scrO]; omega) (.inr (.inr (.inr (by decide))))))
    fun t₃ P₃ => ?_)
  have aB : w64 (p.W + BitVec.ofNat 32 bufO) = w64 p.W + BitVec.ofNat 64 bufO := L.aW (by decide)
  have dis₃ : ∀ {d k : Nat}, d + k ≤ bufO → ∀ r ∈ [⟨w64 (p.W + BitVec.ofNat 32 bufO), 16 * c⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [aB]; exact Lay.w_w (.inl h) (by simp only [bufO] at h; omega) (by simp only [bufO]; omega)
    · exact Lay.w_w (.inl (by simp only [bufO, scrO] at h ⊢; omega)) (by simp only [bufO] at h; omega) (by decide)
    · exact (L.bw' (by simp only [bufO] at h; omega)).symm
  have kB₃ : ∀ {d : Nat}, d + 16 ≤ bufO → blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 d) := fun h => Proof.Ocb.blockAtMem_frame P₃.frame (dis₃ h)
  have kW₃ : ∀ {d : Nat}, d + 4 ≤ bufO → slotv t₃.mem p.W d = slotv t₂.mem p.W d := fun h =>
    P₃.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _) (dis₃ h) (by decide)
  have fr₃ : Frame (hashR p) t₂.mem t₃.mem := P₃.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [aB]; exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by simp only [bufO]; omega⟩)))))
    · exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    · exact ⟨_, by simp, fun _ h => h⟩
  have hg : ∀ k < c, blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by
    have := P₃.enc hk
    rw [aB, add_ofNat_assoc] at this
    rw [this, F.buf k hk, C.ciph' (wR_mut (hashR_wR F.frame))]
  have hcnt₃ : slotv t₃.mem p.W cntO = BitVec.ofNat 32 c := by rw [kW₃ (by decide), F.cnt]
  refine WP.seq (WP.mono (hashSum_ok L P₃.env hc0 hc hcnt₃ hg) fun t₄ ⟨fr₄, sum₄, g₄, rd₄, wr₄⟩ => ?_)
  have E₄ : Env p t₄ := P₃.env.mut L (by rw [g₄ _ (by decide) (by decide) (by decide), P₃.env.ebp])
    (by rw [g₄ _ (by decide) (by decide) (by decide), P₃.env.esp]) rd₄ wr₄
    (frame_toMut fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have kW₄ : ∀ {d : Nat}, 64 ≤ d → d + 4 ≤ 2560 → slotv t₄.mem p.W d = slotv t₃.mem p.W d := fun h h' =>
    fr₄.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by simp only [sumO]; omega)) h' (by decide))
      (by decide)
  have kB₄ : ∀ {d : Nat}, (d + 16 ≤ sumO ∨ 64 ≤ d) → d + 16 ≤ 2560 → blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 d) := fun h h' =>
    Proof.Ocb.blockAtMem_frame fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by simp only [sumO] at h ⊢; omega) h' (by decide)
  have hl₄ : t₄.mem.readW (w64 p.W + BitVec.ofNat 64 hlO) 32 = BitVec.ofNat 32 (p.al / 16 - j) := by
    rw [← slotv_eq, kW₄ (by decide) (by decide), kW₃ (by decide), F.hl]
  have cnt₄ : t₄.mem.readW (w64 p.W + BitVec.ofNat 64 cntO) 32 = BitVec.ofNat 32 c := by
    rw [← slotv_eq, kW₄ (by decide) (by decide), hcnt₃]
  obtain ⟨t₅, run₅, m₅, zf₅, g₅, rd₅, wr₅⟩ : ∃ t₅, runBlock isa [.mov .eax (slot hlO), .alu .sub .eax (slot cntO),
      .store (at_ .ebp hlO) .eax] t₄ = some t₅ ∧
      t₅.mem = t₄.mem.writeW (w64 p.W + BitVec.ofNat 64 hlO) (BitVec.ofNat 32 (p.al / 16 - (j + c))) ∧
      t₅.zf = some (decide (p.al / 16 - (j + c) = 0)) ∧
      (∀ r, r ≠ .eax → t₅.gpr r = t₄.gpr r) ∧ t₅.rd = t₄.rd ∧ t₅.wr = t₄.wr := by
    have e := sub32' (show c ≤ p.al / 16 - j by omega) (by omega)
    rw [show p.al / 16 - j - c = p.al / 16 - (j + c) by omega] at e
    refine ⟨_, by grun [E₄.ebp, L.aW, E₄.perm.wR, E₄.perm.wW, hl₄, cnt₄], by gmems [hl₄, cnt₄, e], ?_,
      fun r h => by gregs [h], by gmems [], by gmems []⟩
    gmems [hl₄, cnt₄, e]
    rw [beq_zero32 (by omega)]
  refine WP.of_runBlock ⟨t₅, run₅, ?_⟩
  have kB₅ : ∀ {d : Nat}, d + 16 ≤ hlO → blockAtMem t₅.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 d) := fun h => by
    rw [m₅]
    exact Proof.Ocb.blockAtMem_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by simp only [hlO] at h; omega) (by decide)
  have fr₅ : Frame (hashR p) t₄.mem t₅.mem := by
    rw [m₅]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains _ (e := 264) (k := 16) (d := 264) (n := 4) (by decide)
      (by decide) (by decide))
  refine ⟨⟨E₄.mut L (by rw [g₅ _ (by decide), E₄.ebp]) (by rw [g₅ _ (by decide), E₄.esp]) rd₅ wr₅
      (wR_mut (hashR_wR fr₅)), F.frame.trans (fr₃.trans ((fr₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans fr₅)),
      by rw [rd₅, rd₄, P₃.rd, F.rd], by rw [wr₅, wr₄, P₃.wr, F.wr], by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, zf₅⟩
  · rw [kB₅ (by decide), sum₄, kB₃ (by decide), F.sum, Proof.Ocb.hsum_add]
  · rw [kB₅ (by decide), kB₄ (.inr (by decide)) (by decide), kB₃ (by decide), F.oh]
  · rw [g₅ _ (by decide), g₄ _ (by decide) (by decide) (by decide), P₃.gpr _ (by decide) (by decide) (by decide)
      (by decide), F.esi]
  · rw [g₅ _ (by decide), g₄ _ (by decide) (by decide) (by decide), P₃.gpr _ (by decide) (by decide) (by decide)
      (by decide), F.edi]
  · rw [slotv_eq, m₅, Mem.readW_writeW_self32]
  · rw [slotv_eq, m₅, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), ← slotv_eq,
      kW₄ (by decide) (by decide), kW₃ (by decide), F.rest]
  · rw [kB₅ (by decide), kB₄ (.inr (by decide)) (by decide), kB₃ (by decide), F.l0]

theorem hashChunk_ok (v : BlocksImpl) {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) {t : State} {j : Nat} (H : HInv p ciph l a s₀ t j) (hj : j < p.al / 16) :
    WP isa (hashChunk (callees v)) t fun t' =>
      HInv p ciph l a s₀ t' (j + min 8 (p.al / 16 - j)) ∧
        t'.zf = some (decide (p.al / 16 - (j + min 8 (p.al / 16 - j)) = 0)) := by
  unfold hashChunk
  refine seq_assoc (WP.seq (WP.mono (chunkHead_ok C H) fun t₁ ⟨H₁, bx⟩ =>
    chunkRest_ok v C H₁ (by omega) (by omega) (by omega) bx))

end VG.Proof.AesOcb.X86
