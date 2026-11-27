module

public import VerifiedGarbage.Proof.AesOcb.X86.Blk
import VerifiedGarbage.Proof.AesOcb.X86.PadTo
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesOcb.X86.Calls
import VerifiedGarbage.Proof.AesOcb.X86.NonceBlock
import VerifiedGarbage.Proof.AesOcb.X86.Setup
import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesOcb.X86.HashFill
public import VerifiedGarbage.Proof.AesOcb.X86.Nonce
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.Loops
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `AesOcb.X86.HashChunk`, which this module and modules that import it used -/

section

/-! ### `Ocb.Sum`, which this module and modules that import it used -/

section

/-!
# OCB: the sum of `HASH` a chunk at a time

Untrusted: everything here is checked by Lean. `Sum_{j+c}` is `Sum_j` with
the `c` enciphered blocks after block `j` added (`hsum_add`); a checksum of
blocks is the spec's when the blocks are (`ckOf_eq`, `ckOf_dck`).
-/

@[expose] public section

namespace VG.Proof.Ocb

open VG.Spec.Ocb (Block Cipher blockAt)

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, hsum ciph l a (j + c) =
      sumOf (hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, hsum, hsum_add ciph l a j c]; rfl

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = blockAt p i) :
    ckOf X m = ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, ckAt, ih (fun i hi => h i (by omega_using [hi])), h m (by omega_using [])]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = decBlock inv o0 l c i) : ckOf X m = dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, dckAt, ih (fun i hi => h i (by omega_using [hi])), h m (by omega_using [])]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega_using [hi]))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega_using [])]

end VG.Proof.Ocb

end

end

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

@[expose] public section

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
  · exact ⟨_, by simp, Offset.sub _ (e := 48) (k := 16) (by omega_arith) (by omega_arith)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 96) (k := 16) (by omega_arith) (by omega_arith)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 160) (k := 16) (by omega_arith) (by omega_arith)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 220) (k := 4) (by omega_arith) (by omega_arith)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 264) (k := 16) (by omega_arith) (by omega_arith)⟩
  · exact ⟨wC p.W, by simp, Offset.sub _ (by omega_arith) (by omega_arith)⟩

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
  rw [w64_add (by have := L.aw; omega_arith), ← C.aad, ← aad_mut L h, Proof.Ocb.blockAt_bytesAt _ _ (by omega_arith)]

/-- Block `i` of the associated data, for `hashFill`. -/
theorem abuf {s : State} (E : Env p s) {i : Nat} (hi : i < p.al / 16) :
    ABuf p s (p.A + BitVec.ofNat 32 (16 * i)) 16 := by
  have L := C.lay
  have hA := L.aw
  obtain a16 : w64 (p.A + BitVec.ofNat 32 (16 * i)) = w64 p.A + BitVec.ofNat 64 (16 * i) := w64_add (by omega_arith)
  obtain sub : Region.Sub ⟨w64 (p.A + BitVec.ofNat 32 (16 * i)), 16⟩ ⟨w64 p.A, p.al⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨by rw [toNat_add32 (by omega_arith)]; omega_arith, L.a_w.sub_left sub, L.ba.sub_right sub, ?_⟩
  rw [a16]; exact covers_off E.perm.aad (by omega_arith) (by omega_arith)

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
  refine WP.mono (hashFill_ok L F.env hi hc (by omega_arith) F.edi F.esi F.ebx F.fp F.l0 F.oh
    (C.abuf F.env (i := j + i) (by omega_arith))) fun t' P => ⟨?_, P.zf⟩
  obtain hfr : Frame (hashR p) t.mem t'.mem := P.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact inHashR p (.inr (.inl ⟨by decide, by decide⟩))
    · exact inHashR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
    · exact inHashR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by simp only [bufO]; omega_arith, by simp only [bufO]; omega_arith⟩)))))
    · exact inHashR p (.inr (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩)))))
  obtain dis : ∀ {d k : Nat}, (d + k ≤ lO ∨ lO + 16 ≤ d) → (d + k ≤ kO ∨ kO + 4 ≤ d) → (d + k ≤ ohO ∨ ohO + 16 ≤ d) →
      (d + k ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) → (d + k ≤ fpO ∨ fpO + 4 ≤ d) → d + k ≤ 2560 →
      ∀ r ∈ fillR p i, (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h₁ h₂ h₃ h₄ h₅ h₆ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w h₁ h₆ (by decide)
    · exact Lay.w_w h₂ h₆ (by decide)
    · exact Lay.w_w h₃ h₆ (by decide)
    · exact Lay.w_w h₄ h₆ (by simp only [bufO]; omega_arith)
    · exact Lay.w_w h₅ h₆ (by decide)
  obtain keepB : ∀ {d : Nat}, (d + 16 ≤ lO ∨ lO + 16 ≤ d) → (d + 16 ≤ kO ∨ kO + 4 ≤ d) →
      (d + 16 ≤ ohO ∨ ohO + 16 ≤ d) → (d + 16 ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) →
      (d + 16 ≤ fpO ∨ fpO + 4 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun h₁ h₂ h₃ h₄ h₅ h₆ => Proof.Ocb.blockAtMem_frame P.frame (dis h₁ h₂ h₃ h₄ h₅ h₆)
  obtain keepW : ∀ {d : Nat}, (d + 4 ≤ lO ∨ lO + 16 ≤ d) → (d + 4 ≤ kO ∨ kO + 4 ≤ d) →
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
      esi := by rw [P.esi, show j + i + 1 = j + (i + 1) by omega_arith]
      edi := by rw [P.edi, show j + i + 2 = j + (i + 1) + 1 by omega_arith]
      ebx := P.ebx
      fp := P.fp
      cnt := by rw [keepW (by decide) (by decide) (by decide) (by simp only [cntO, bufO]; omega_arith) (by decide)
        (by decide), F.cnt]
      oh := by rw [P.oh, show j + i + 1 = j + (i + 1) by omega_arith]
      buf := fun k hk => ?_
      sum := by rw [keepB (by decide) (by decide) (by decide) (by simp only [sumO, bufO]; omega_arith) (by decide)
        (by decide), F.sum]
      hl := by rw [keepW (by decide) (by decide) (by decide) (by simp only [hlO, bufO]; omega_arith) (by decide)
        (by decide), F.hl]
      rest := by rw [keepW (by decide) (by decide) (by decide) (by simp only [restO, bufO]; omega_arith) (by decide)
        (by decide), F.rest]
      l0 := by rw [keepB (by decide) (by decide) (by decide) (by simp only [l0O, bufO]; omega_arith) (by decide)
        (by decide), F.l0] }
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [keepB (by simp only [lO, bufO]; omega_arith) (by simp only [kO, bufO]; omega_arith) (by simp only [ohO, bufO]; omega_arith)
      (by omega_arith) (by simp only [fpO, bufO]; omega_arith) (by simp only [bufO]; omega_arith), F.buf k hk']
  · obtain rfl : k = i := by omega_arith
    rw [P.buf, C.blk (wR_mut (hashR_wR F.frame)) (by omega_arith)]

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
  · right; exact ⟨(eval_ne hz).trans (by simp [he]), c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, F'⟩

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
    (e := bufO + 16 * i) (d := sumO) (by simp only [bufO]; omega_arith) (by decide) (.inr (by simp only [bufO, sumO]; omega_arith))
  obtain dx₁ : u₁.gpr .edx = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [g₁' _ (by decide), dx]
  obtain bx₁ : u₁.gpr .ebx = BitVec.ofNat 32 (c - i) := by rw [g₁' _ (by decide), bx]
  obtain ⟨u₂, run₂, dx₂, bx₂, zf₂, g₂, m₂, rd₂, wr₂⟩ : ∃ u₂, runBlock isa [.alu .add .edx (imm 16),
      .alu .sub .ebx (imm 1)] u₁ = some u₂ ∧ u₂.gpr .edx = p.W + BitVec.ofNat 32 (bufO + 16 * (i + 1)) ∧
      u₂.gpr .ebx = BitVec.ofNat 32 (c - (i + 1)) ∧ u₂.zf = some (decide (i + 1 = c)) ∧
      (∀ r, r ≠ .ebx → r ≠ .edx → u₂.gpr r = u₁.gpr r) ∧ u₂.mem = u₁.mem ∧ u₂.rd = u₁.rd ∧ u₂.wr = u₁.wr := by
    refine ⟨_, by grun [], ?_, ?_, ?_, fun r h₁ h₂ => by gregs [h₁, h₂], by gmems [], by gmems [], by gmems []⟩
    · gregs [dx₁]; rw [add_ofNat_assoc32, show bufO + 16 * i + 16 = bufO + 16 * (i + 1) by omega_arith]
    · gregs [bx₁]; rw [sub1_32 (by omega_arith) (by omega_arith), show c - i - 1 = c - (i + 1) by omega_arith]
    · gmems [bx₁]
      rw [sub1_32 (by omega_arith) (by omega_arith), beq_zero32 (by omega_arith)]
      exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  refine WP.of_runBlock ⟨u₂, runBlock_app_of run₁' run₂, ?_⟩
  obtain Eu₂ : Env p u₂ := Eu.mut L (by rw [g₂ _ (by decide) (by decide), g₁' _ (by decide), Eu.ebp])
    (by rw [g₂ _ (by decide) (by decide), g₁' _ (by decide), Eu.esp]) (by rw [rd₂, rd₁']) (by rw [wr₂, wr₁'])
    (frame_toMut (by rw [m₂, m₁']; exact xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain hbuf : blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * i)) = g i := by
    rw [Proof.Ocb.blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inr (by simp only [bufO, sumO]; omega_arith)) (by simp only [bufO]; omega_arith) (by decide),
      hg i hi]
  obtain fr' : Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem u₂.mem := by
    rw [m₂, m₁']; exact fr.trans (xorMem16_frame _ _ _ _ _)
  obtain sum' : blockAtMem u₂.mem (w64 p.W + BitVec.ofNat 64 sumO) =
      sumOf (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO)) g (i + 1) := by
    rw [m₂, m₁', xorMem16_block, sum, hbuf]; rfl
  obtain gu' : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → u₂.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₂ r h₂ h₃, g₁' r h₁, gu r h₁ h₂ h₃]
  by_cases he : i + 1 = c
  · left
    exact ⟨(eval_ne zf₂).trans (by simp [he]), fr', he ▸ sum', gu', by rw [rd₂, rd₁', rd], by rw [wr₂, wr₁', wr]⟩
  · right
    exact ⟨(eval_ne zf₂).trans (by simp [he]), c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, Eu₂, dx₂, bx₂, fr',
      sum', gu', by rw [rd₂, rd₁', rd], by rw [wr₂, wr₁', wr]⟩

/-! ## A chunk -/

theorem sub32' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat32 ha, toNat_ofNat32 (by omega_arith), toNat_ofNat32 (by omega_arith)]
  omega_arith

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
    gmems [hl, toNat_ofNat32 (show p.al / 16 - j < 2 ^ 32 by omega_arith), toNat_ofNat32 (show 8 < 2 ^ 32 by decide)]
  obtain H₁ := H.of_keep (fun r _ h₂ _ _ => g₁ r h₂) m₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (p.al / 16 - j < 8)) (eval_b cf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hlt : p.al / 16 - j < 8 := of_decide_eq_true hb
    rw [show min 8 (p.al / 16 - j) = p.al / 16 - j by omega_arith]
    exact ⟨H₁, bx₁⟩
  · have hge : ¬ p.al / 16 - j < 8 := of_decide_eq_false hb
    obtain ⟨t₂, run₂, bx₂, g₂, m₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa [.mov .ebx (imm 8)] t₁ = some t₂ ∧
        t₂.gpr .ebx = BitVec.ofNat 32 8 ∧ (∀ r, r ≠ .ebx → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧ t₂.rd = t₁.rd ∧
        t₂.wr = t₁.wr :=
      ⟨_, by grun [], by gregs [], fun r h => by gregs [h], by gmems [], by gmems [], by gmems []⟩
    refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
    rw [show min 8 (p.al / 16 - j) = 8 by omega_arith]
    exact ⟨H₁.of_keep (fun r _ h₂ _ _ => g₂ r h₂) m₂ rd₂ wr₂, bx₂⟩

/-- The start of a chunk of `c` blocks from `ebx`: its count and the buffer's
start kept in `W`. -/
theorem chunkStart_ok {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) {t : State} {j c : Nat} (H : HInv p ciph l a s₀ t j)
    (hbx : t.gpr .ebx = BitVec.ofNat 32 c) :
    ∃ t₁, runBlock isa [.store (at_ .ebp cntO) .ebx, .mov .eax (.reg .ebp), .alu .add .eax (imm bufO),
      .store (at_ .ebp fpO) .eax] t = some t₁ ∧ FillInv p ciph l a s₀ j c t₁ 0 := by
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
  obtain fr₁ : Frame (hashR p) t.mem t₁.mem := by
    rw [m₁]
    obtain hm : (⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩ : Region) ∈ hashR p := by simp
    exact ((Frame.refl _ _).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 272) (n := 4) (by decide)
      (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 268) (n := 4) (by decide)
      (by decide) (by decide))
  obtain kW₁ : ∀ {d : Nat}, (d + 4 ≤ 268 ∨ 276 ≤ d) → d + 4 ≤ 2560 → slotv t₁.mem p.W d = slotv t.mem p.W d :=
    fun h h' => by
      rw [slotv_eq, slotv_eq, m₁, Mem.readW_writeW_sep (Offset.sep _ (by simp only [fpO]; omega_arith) (by omega_arith) (by decide))
        (by decide), Mem.readW_writeW_sep (Offset.sep _ (by simp only [cntO]; omega_arith) (by omega_arith) (by decide)) (by decide)]
  obtain kB₁ : ∀ {d : Nat}, d + 16 ≤ 268 → blockAtMem t₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) := fun h =>
    Proof.Ocb.blockAtMem_frame (rs := [⟨w64 p.W + BitVec.ofNat 64 268, 8⟩]) (by
      rw [m₁]
      obtain hm := List.mem_singleton_self (⟨w64 p.W + BitVec.ofNat 64 268, 8⟩ : Region)
      exact ((Frame.refl _ _).writeW hm _ (Offset.contains _ (e := 268) (k := 8) (d := 272) (n := 4) (by decide)
        (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 268) (k := 8) (d := 268) (n := 4) (by decide)
        (by decide) (by decide))) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  obtain F₀ : FillInv p ciph l a s₀ j c t₁ 0 :=
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
  exact ⟨t₁, run₁, F₀⟩

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
  obtain ⟨t₁, run₁, F₀⟩ := chunkStart_ok C H hbx
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (fill_ok C hc0 hc hjc F₀) fun t₂ F => ?_)
  -- the call
  have hcnt₂ := F.cnt
  simp only [slotv_eq] at hcnt₂
  obtain hargs : ∃ s₁, runBlock isa [.mov .edx (.reg .ebp), .alu .add .edx (imm bufO), .mov .ebx (slot cntO)] t₂ =
      some s₁ ∧ s₁.gpr .edx = p.W + BitVec.ofNat 32 bufO ∧ s₁.gpr .ebx = BitVec.ofNat 32 c ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = t₂.gpr r) ∧ s₁.mem = t₂.mem ∧
      s₁.rd = t₂.rd ∧ s₁.wr = t₂.wr :=
    ⟨_, by grun [F.env.ebp, L.aW, F.env.perm.wR, hcnt₂], by gregs [F.env.ebp], by gregs [hcnt₂],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L F.env hargs
    (DReg.w L F.env (d := bufO) (n := c) (by simp only [bufO, scrO]; omega_arith) (.inr (.inr (.inr (by decide))))))
    fun t₃ P₃ => ?_)
  obtain aB : w64 (p.W + BitVec.ofNat 32 bufO) = w64 p.W + BitVec.ofNat 64 bufO := L.aW (by decide)
  obtain dis₃ : ∀ {d k : Nat}, d + k ≤ bufO → ∀ r ∈ [⟨w64 (p.W + BitVec.ofNat 32 bufO), 16 * c⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [aB]; exact Lay.w_w (.inl h) (by simp only [bufO] at h; omega_arith) (by simp only [bufO]; omega_arith)
    · exact Lay.w_w (.inl (by simp only [bufO, scrO] at h ⊢; omega_arith)) (by simp only [bufO] at h; omega_arith) (by decide)
    · exact (L.bw' (by simp only [bufO] at h; omega_arith)).symm
  obtain kB₃ : ∀ {d : Nat}, d + 16 ≤ bufO → blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 d) := fun h => Proof.Ocb.blockAtMem_frame P₃.frame (dis₃ h)
  obtain kW₃ : ∀ {d : Nat}, d + 4 ≤ bufO → slotv t₃.mem p.W d = slotv t₂.mem p.W d := fun h =>
    P₃.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _) (dis₃ h) (by decide)
  obtain fr₃ : Frame (hashR p) t₂.mem t₃.mem := P₃.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [aB]; exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by simp only [bufO]; omega_arith⟩)))))
    · exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain hg : ∀ k < c, blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by
    have := P₃.enc hk
    rw [aB, add_ofNat_assoc] at this
    rw [this, F.buf k hk, C.ciph' (wR_mut (hashR_wR F.frame))]
  obtain hcnt₃ : slotv t₃.mem p.W cntO = BitVec.ofNat 32 c := by rw [kW₃ (by decide), F.cnt]
  refine WP.seq (WP.mono (hashSum_ok L P₃.env hc0 hc hcnt₃ hg) fun t₄ ⟨fr₄, sum₄, g₄, rd₄, wr₄⟩ => ?_)
  obtain E₄ : Env p t₄ := P₃.env.mut L (by rw [g₄ _ (by decide) (by decide) (by decide), P₃.env.ebp])
    (by rw [g₄ _ (by decide) (by decide) (by decide), P₃.env.esp]) rd₄ wr₄
    (frame_toMut fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain kW₄ : ∀ {d : Nat}, 64 ≤ d → d + 4 ≤ 2560 → slotv t₄.mem p.W d = slotv t₃.mem p.W d := fun h h' =>
    fr₄.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by simp only [sumO]; omega_arith)) h' (by decide))
      (by decide)
  obtain kB₄ : ∀ {d : Nat}, (d + 16 ≤ sumO ∨ 64 ≤ d) → d + 16 ≤ 2560 → blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 d) := fun h h' =>
    Proof.Ocb.blockAtMem_frame fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by simp only [sumO] at h ⊢; omega_arith) h' (by decide)
  obtain hl₄ : t₄.mem.readW (w64 p.W + BitVec.ofNat 64 hlO) 32 = BitVec.ofNat 32 (p.al / 16 - j) := by
    rw [← slotv_eq, kW₄ (by decide) (by decide), kW₃ (by decide), F.hl]
  obtain cnt₄ : t₄.mem.readW (w64 p.W + BitVec.ofNat 64 cntO) 32 = BitVec.ofNat 32 c := by
    rw [← slotv_eq, kW₄ (by decide) (by decide), hcnt₃]
  obtain ⟨t₅, run₅, m₅, zf₅, g₅, rd₅, wr₅⟩ : ∃ t₅, runBlock isa [.mov .eax (slot hlO), .alu .sub .eax (slot cntO),
      .store (at_ .ebp hlO) .eax] t₄ = some t₅ ∧
      t₅.mem = t₄.mem.writeW (w64 p.W + BitVec.ofNat 64 hlO) (BitVec.ofNat 32 (p.al / 16 - (j + c))) ∧
      t₅.zf = some (decide (p.al / 16 - (j + c) = 0)) ∧
      (∀ r, r ≠ .eax → t₅.gpr r = t₄.gpr r) ∧ t₅.rd = t₄.rd ∧ t₅.wr = t₄.wr := by
    obtain e := sub32' (show c ≤ p.al / 16 - j by omega_arith) (by omega_arith)
    rw [show p.al / 16 - j - c = p.al / 16 - (j + c) by omega_arith] at e
    refine ⟨_, by grun [E₄.ebp, L.aW, E₄.perm.wR, E₄.perm.wW, hl₄, cnt₄], by gmems [hl₄, cnt₄, e], ?_,
      fun r h => by gregs [h], by gmems [], by gmems []⟩
    gmems [hl₄, cnt₄, e]
    rw [beq_zero32 (by omega_arith)]
  refine WP.of_runBlock ⟨t₅, run₅, ?_⟩
  obtain kB₅ : ∀ {d : Nat}, d + 16 ≤ hlO → blockAtMem t₅.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 d) := fun h => by
    rw [m₅]
    exact Proof.Ocb.blockAtMem_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by simp only [hlO] at h; omega_arith) (by decide)
  obtain fr₅ : Frame (hashR p) t₄.mem t₅.mem := by
    rw [m₅]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains _ (e := 264) (k := 16) (d := 264) (n := 4) (by decide)
      (by decide) (by decide))
  refine ⟨⟨E₄.mut L (by rw [g₅ _ (by decide), E₄.ebp]) (by rw [g₅ _ (by decide), E₄.esp]) rd₅ wr₅
      (wR_mut (hashR_wR fr₅)), F.frame.trans (fr₃.trans ((fr₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans fr₅)),
      by rw [rd₅, rd₄, P₃.rd, F.rd], by rw [wr₅, wr₄, P₃.wr, F.wr], by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, zf₅⟩
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
    chunkRest_ok v C H₁ (by omega_arith) (by omega_arith) (by omega_arith) bx))

end VG.Proof.AesOcb.X86

end

end

/-!
# AES-OCB on x86: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset, keeps the number of whole blocks of the associated data and the
length of the rest in `W`, takes the whole blocks a chunk at a time
(`hashChunk_ok`), and the rest, padded, XORed with `Offset_m ⊕ L_*` and
enciphered (`hashRest_ok`): the sum is §4.1's `HASH(K, A)` (`hash_ok`,
`Proof.Ocb.hash_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt hsum)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off
  length_bytesAt)

/-- `L_*`, after a frame within `mutR`. -/
theorem lstar_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (mutR p) m m') :
    ctxLstar m' (w64 p.K) = ctxLstar m (w64 p.K) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => (k_mut L r hr).sub_left (Offset.sub_base _ (by decide))

/-- The head of `hashRest`: `Offset_m ⊕ L_*` to `W + ohO`. -/
theorem hashRestHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₂, runBlock isa (([.mov .ebx (slot ctxO)] : List Instr) ++ xor16 .ebx 240 ohO) t = some t₂ ∧ Env p t₂ ∧
      t₂.mem = xorMem16 t.mem (w64 p.K) 240 (w64 p.W) ohO ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → t₂.gpr r = t.gpr r) ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr := by
  have hc := E.slots.ctx
  simp only [slotv_eq] at hc
  obtain ⟨t₁, run₁, bx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .ebx (slot ctxO)] t = some t₁ ∧
      t₁.gpr .ebx = p.K ∧ (∀ r, r ≠ .ebx → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gregs [hc], fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
  obtain E₁ : Env p t₁ := E.keep (by rw [g₁ _ (by decide)]) (by rw [g₁ _ (by decide)]) rd₁ wr₁ m₁
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16R_ok L E₁ (b := .ebx) (by decide) bx₁ L.kw L.k_w
    E₁.perm.k (s := 240) (d := ohO) (by decide) (by decide)
  refine ⟨t₂, runBlock_app_of run₁ run₂, E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp])
    (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (frame_toMut (by rw [m₂]; exact xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))),
    by rw [m₂, m₁], fun r h₁ h₂ => by rw [g₂ r h₁, g₁ r h₂], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- The padded rest of the associated data, after its `m` whole blocks. -/
theorem hashRest_ok (v : BlocksImpl) {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) {t : State} (H : HInv p ciph l a s₀ t (p.al / 16)) (hr : 0 < p.al % 16) :
    WP isa (hashRest (callees v)) t fun t' => Env p t' ∧ Frame (hashR p) s₀.mem t'.mem ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧
      t'.wr = s₀.wr := by
  have L := C.lay
  have E := H.env
  have hal := L.aw
  generalize hm : p.al / 16 = m at H
  -- `Offset_m ⊕ L_*`
  obtain ⟨t₂, run₂, E₂, m₂, g₂, rd₂, wr₂⟩ := hashRestHead_ok L E
  obtain fr₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem := by
    rw [m₂]; exact xorMem16_frame _ _ _ _ _
  obtain fH₂ : Frame (hashR p) s₀.mem t₂.mem := H.frame.trans (fr₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inHashR p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  obtain oh₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [m₂, xorMem16_block, H.oh, ← C.lstar, ← lstar_mut L (wR_mut (hashR_wR H.frame))]; rfl
  -- `pad(A_*)`
  obtain si₂ : t₂.gpr .esi = p.A + BitVec.ofNat 32 (16 * m) := by rw [g₂ _ (by decide) (by decide), H.esi]
  obtain rest₂ : slotv t₂.mem p.W restO = BitVec.ofNat 32 (p.al % 16) := by
    rw [← H.rest]
    exact fr₂.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)
  obtain a16 : w64 (p.A + BitVec.ofNat 32 (16 * m)) = w64 p.A + BitVec.ofNat 64 (16 * m) := w64_add (by omega_using [hr, hal, hm])
  obtain sub : Region.Sub ⟨w64 (p.A + BitVec.ofNat 32 (16 * m)), p.al % 16⟩ ⟨w64 p.A, p.al⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega_using [hm])
  obtain hS : SBuf p t₂ (p.A + BitVec.ofNat 32 (16 * m)) (p.al % 16) := by
    refine ⟨?_, L.a_w.sub_left sub, ?_⟩
    · rw [toNat_add32 (by omega_using [hr, hal, hm])]; omega_using [hal, hm]
    · rw [a16]; exact covers_off E₂.perm.aad (by omega_using [hm]) (by omega_using [hal])
  obtain hrestb : bytesAt t₂.mem (w64 (p.A + BitVec.ofNat 32 (16 * m))) (p.al % 16) = a.drop (16 * (a.length / 16)) := by
    rw [C.len, hm, ← C.aad, Proof.Ocb.bytesAt_drop _ _ (by omega_using [hm]), show p.al - 16 * m = p.al % 16 by omega_using [hm], a16]
    obtain ad : ∀ r ∈ mutR p, (⟨w64 p.A, p.al⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact L.a_w.sub_right (Region.sub_prefix (by decide))
      · exact L.a_w.sub_right (Lay.wSub (by decide))
      · exact L.a_w.sub_right (Lay.wSub (by decide))
      · exact L.a_w.sub_right (Lay.wSub (by decide))
      · exact L.ba.symm
      · exact L.a_d
    exact Proof.AesGcm.X86.bytesAt_frame (wR_mut (hashR_wR fH₂))
      (fun r hr => (ad r hr).sub_left (Offset.sub_base _ (by omega_using [hm]))) (by omega_using [])
  unfold hashRest
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (padTo_ok L E₂ (d := bufO) (cO := restO) hr (by omega_using []) (by decide) (by decide)
    (.inl (by decide)) si₂ rest₂ hS) fun t₃ ⟨fr₃, pad₃, g₃, rd₃, wr₃⟩ => ?_)
  rw [hrestb] at pad₃
  obtain E₃ : Env p t₃ := E₂.mut L (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), E₂.ebp])
    (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), E₂.esp]) rd₃ wr₃
    (frame_toMut fr₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩))))
  obtain oh₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [Proof.Ocb.blockAtMem_frame fr₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide), oh₂]
  -- XORed with the offset
  obtain ⟨t₄, run₄, m₄, g₄, rd₄, wr₄⟩ := xor16W_ok L E₃ (s := ohO) (d := bufO) (by decide) (by decide)
    (.inl (by decide))
  obtain E₄ : Env p t₄ := E₃.mut L (by rw [g₄ _ (by decide), E₃.ebp]) (by rw [g₄ _ (by decide), E₃.esp]) rd₄ wr₄
    (frame_toMut (by rw [m₄]; exact xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩))))
  obtain buf₄ : blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 bufO) =
      pad (a.drop (16 * (a.length / 16))) ^^^ (offAt 0 l m ^^^ l) := by rw [m₄, xorMem16_block, pad₃, oh₃]
  obtain fH₄ : Frame (hashR p) s₀.mem t₄.mem := fH₂.trans ((fr₃.trans (by rw [m₄]; exact xorMem16_frame _ _ _ _ _)).sub
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩))))))
  refine WP.seq (WP.of_runBlock ⟨t₄, run₄, ?_⟩)
  -- enciphered
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₄
    (oneBlock_ok E₄ bufO) (DReg.w L E₄ (d := bufO) (n := 1) (by decide) (.inr (.inr (.inr (by decide))))))
    fun t₅ P₅ => ?_)
  obtain aB : w64 (p.W + BitVec.ofNat 32 bufO) = w64 p.W + BitVec.ofNat 64 bufO := L.aW (by decide)
  obtain buf₅ : blockAtMem t₅.mem (w64 p.W + BitVec.ofNat 64 bufO) =
      ciph (pad (a.drop (16 * (a.length / 16))) ^^^ (offAt 0 l m ^^^ l)) := by
    have := P₅.enc (i := 0) (by decide)
    rw [aB, show w64 p.W + BitVec.ofNat 64 bufO + BitVec.ofNat 64 (16 * 0) = w64 p.W + BitVec.ofNat 64 bufO from
      BitVec.add_zero _] at this
    rw [this, buf₄, C.ciph' (wR_mut (hashR_wR fH₄))]
  obtain fH₅ : Frame (hashR p) s₀.mem t₅.mem := fH₄.trans (P₅.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [aB]; exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    · exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    · exact ⟨_, by simp, fun _ h => h⟩)
  obtain kS : ∀ {rs : List Region} {u u' : State}, Frame rs u.mem u'.mem →
      (∀ r ∈ rs, (⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint r) →
      blockAtMem u'.mem (w64 p.W + BitVec.ofNat 64 sumO) = blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 sumO) :=
    fun h hd => Proof.Ocb.blockAtMem_frame h hd
  obtain sum₅ : blockAtMem t₅.mem (w64 p.W + BitVec.ofNat 64 sumO) = hsum ciph l a m := by
    rw [kS P₅.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [aB]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm),
      kS (u := t₃) (rs := [⟨w64 p.W + BitVec.ofNat 64 bufO, 16⟩]) (by rw [m₄]; exact xorMem16_frame _ _ _ _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      kS fr₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      kS (u := t) (rs := [⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩]) fr₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      H.sum]
  -- added to the sum
  obtain ⟨t₆, run₆, m₆, g₆, rd₆, wr₆⟩ := xor16W_ok L P₅.env (s := bufO) (d := sumO) (by decide) (by decide)
    (.inr (by decide))
  refine WP.of_runBlock ⟨t₆, run₆, P₅.env.mut L (by rw [g₆ _ (by decide), P₅.env.ebp])
    (by rw [g₆ _ (by decide), P₅.env.esp]) rd₆ wr₆ (frame_toMut (by rw [m₆]; exact xorMem16_frame _ _ _ _ _)
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide))),
    fH₅.trans (by
      rw [m₆]
      exact (xorMem16_frame _ _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact inHashR p (.inl ⟨by decide, by decide⟩)), ?_,
    by rw [rd₆, P₅.rd, rd₄, rd₃, rd₂, H.rd], by rw [wr₆, P₅.wr, wr₄, wr₃, wr₂, H.wr]⟩
  rw [m₆, xorMem16_block, sum₅, buf₅, Proof.Ocb.hash_eq]
  simp only [C.len, hm]
  obtain hlen : (a.drop (16 * m)).length = p.al % 16 := by simp [C.len]; omega_using [hm]
  simp only [hlen, show p.al % 16 > 0 from hr, ↓reduceIte]

/-- After the whole blocks: the rest, if any. -/
theorem hashTail_ok (v : BlocksImpl) {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) {t : State} (H : HInv p ciph l a s₀ t (p.al / 16)) :
    WP isa (.seq (.block [.mov .eax (slot restO), .alu .test .eax (.reg .eax)])
      (.ite .e (.block []) (hashRest (callees v)))) t fun t' => Env p t' ∧ Frame (hashR p) s₀.mem t'.mem ∧
        blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧
        t'.wr = s₀.wr := by
  have L := C.lay
  have rest := H.rest
  simp only [slotv_eq] at rest
  obtain ⟨t₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .eax (slot restO), .alu .test .eax (.reg .eax)] t =
      some t₁ ∧ t₁.zf = some (decide (p.al % 16 = 0)) ∧
      (∀ r, r ≠ .eax → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [H.env.ebp, L.aW, H.env.perm.wR, rest], ?_, fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
    gmems [rest, BitVec.and_self, beq_zero32 (show p.al % 16 < 2 ^ 32 by omega_using [])]
  obtain H₁ := H.of_keep (fun r h₁ _ _ _ => g₁ r h₁) m₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (p.al % 16 = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : p.al % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₁.env, H₁.frame, ?_, H₁.rd, H₁.wr⟩
    rw [H₁.sum, Proof.Ocb.hash_eq, C.len]
    obtain hlen : (a.drop (16 * (p.al / 16))).length = 0 := by simp [C.len]; omega_using [h0]
    simp [hlen]
  · exact hashRest_ok v C H₁ (by have := of_decide_eq_false hb; omega_using [this])

theorem shr4_32 {v : Nat} (hv : v < 2 ^ 32) : BitVec.ofNat 32 v >>> 4 = BitVec.ofNat 32 (v / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat32 hv, toNat_ofNat32 (by omega_using [hv]), Nat.shiftRight_eq_div_pow]

/-- The start of `HASH`: the sum and the offset zeroed, the counts. -/
theorem hashHead_ok {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : HCtx p ciph l a s₀)
    (E : Env p s₀) (hl0 : blockAtMem s₀.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block (zero4 sumO ++ zero4 ohO ++
      ([.mov .esi (slot aadO), .mov .eax (slot alenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
       .store (at_ .ebp restO) .ecx, .shift .shr .eax 4, .store (at_ .ebp hlO) .eax, .mov .edi (imm 1),
       .alu .test .eax (.reg .eax)] : List Instr))) s₀ fun s =>
      HInv p ciph l a s₀ s 0 ∧ s.zf = some (decide (p.al / 16 = 0)) := by
  have L := C.lay
  have hal := L.al32
  have hA := E.slots.aad
  have hn := E.slots.alen
  simp only [slotv_eq] at hA hn
  obtain z₁ := zero4_fold s₀.mem p.W sumO
  obtain z₂ := zero4_fold (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO)) p.W ohO
  obtain fz : Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] s₀.mem
      (Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO)) (w64 p.W + BitVec.ofNat 64 ohO)) :=
    ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp)).trans ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  obtain rz : ∀ {d : Nat}, 176 ≤ d → d + 4 ≤ 2560 →
      (Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO))
        (w64 p.W + BitVec.ofNat 64 ohO)).readW (w64 p.W + BitVec.ofNat 64 d) 32 =
      s₀.mem.readW (w64 p.W + BitVec.ofNat 64 d) 32 := fun h h' =>
    fz.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (.inr (by simp only [sumO, ohO]; omega_using [h])) h' (by decide)) (by decide)
  obtain hA' := (rz (d := aadO) (by decide) (by decide)).trans hA
  obtain hn' := (rz (d := alenO) (by decide) (by decide)).trans hn
  simp only [sumO, ohO, aadO, alenO, Nat.reduceAdd] at hA' hn'
  obtain ⟨s₁, run₁, m₁, si₁, di₁, zf₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa (zero4 sumO ++ zero4 ohO ++
      [.mov .esi (slot aadO), .mov .eax (slot alenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
       .store (at_ .ebp restO) .ecx, .shift .shr .eax 4, .store (at_ .ebp hlO) .eax, .mov .edi (imm 1),
       .alu .test .eax (.reg .eax)]) s₀ = some s₁ ∧
      s₁.mem = ((Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO))
        (w64 p.W + BitVec.ofNat 64 ohO)).writeW (w64 p.W + BitVec.ofNat 64 restO)
          (BitVec.ofNat 32 (p.al % 16))).writeW (w64 p.W + BitVec.ofNat 64 hlO) (BitVec.ofNat 32 (p.al / 16)) ∧
      s₁.gpr .esi = p.A ∧ s₁.gpr .edi = BitVec.ofNat 32 1 ∧ s₁.zf = some (decide (p.al / 16 = 0)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₁.gpr r = s₀.gpr r) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
    refine ⟨_, by grun [zero4, E.ebp, L.aW, E.perm.wR, E.perm.wW, hA, hn, z₁, z₂, hA', hn'], ?_, by gregs [hA, hA'], by gregs [],
      ?_, fun r h₁ h₂ h₃ h₄ => by gregs [h₁, h₂, h₃, h₄], by gmems [], by gmems []⟩
    · gmems [hA', hn', z₁, z₂, and15_32 hal, shr4_32 hal]
    · gmems [hA', hn', z₁, z₂, shr4_32 hal, BitVec.and_self, beq_zero32 (show p.al / 16 < 2 ^ 32 by omega_using [hal])]
  obtain F : Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩] s₀.mem s₁.mem := by
    rw [m₁]
    obtain hm : (⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩ : Region) ∈ [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩] := by simp
    exact (((fz.mono (by simp)).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 276) (n := 4) (by decide)
      (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 264) (n := 4) (by decide)
      (by decide) (by decide)))
  obtain fH : Frame (hashR p) s₀.mem s₁.mem := F.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact inHashR p (.inl ⟨by decide, by decide⟩)
    · exact inHashR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inHashR p (.inr (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩)))))
  obtain kz : ∀ {d : Nat}, d + 16 ≤ 264 → blockAtMem s₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem (Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO))
        (w64 p.W + BitVec.ofNat 64 ohO)) (w64 p.W + BitVec.ofNat 64 d) := fun h => by
    rw [m₁]
    obtain hm := List.mem_singleton_self (⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩ : Region)
    exact Proof.Ocb.blockAtMem_frame (((Frame.refl _ _).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 276)
      (n := 4) (by decide) (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 264)
      (n := 4) (by decide) (by decide) (by decide))) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by omega_using [h]) (by decide)
  refine WP.of_runBlock ⟨s₁, run₁, ⟨E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (wR_mut (hashR_wR fH)), fH,
      rd₁, wr₁, Nat.zero_le _, ?_, ?_, by rw [si₁]; exact (BitVec.add_zero _).symm, di₁, ?_, ?_, ?_⟩, zf₁⟩
  · have fz0 : ∀ (m : Mem) (c : Addr), Frame [⟨c, 16⟩] m (Proof.Cmac.zero4 m c) :=
      fun m c => Proof.Cmac.frame_store4 _ _ _ _ _
    rw [kz (by decide), Proof.Ocb.blockAtMem_frame (fz0 _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      blockAtMem_zero4]; rfl
  · rw [kz (by decide), blockAtMem_zero4]; rfl
  · rw [slotv_eq, m₁, Mem.readW_writeW_self32, Nat.sub_zero]
  · rw [slotv_eq, m₁, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [kz (by decide), Proof.Ocb.blockAtMem_frame fz (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), hl0]

/-- The chunks of `HASH`, from the first. -/
theorem hashLoop_ok (v : BlocksImpl) {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) {t : State} (H₀ : HInv p ciph l a s₀ t 0) (hm : 0 < p.al / 16) :
    WP isa (.loop (hashChunk (callees v)) .ne) t fun u => HInv p ciph l a s₀ u (p.al / 16) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ j, k = p.al / 16 - j ∧ j < p.al / 16 ∧ HInv p ciph l a s₀ u j) ?_
    (p.al / 16 - 0) _ ⟨0, rfl, hm, H₀⟩
  rintro k u ⟨j, rfl, hj, H⟩
  refine WP.mono (hashChunk_ok v C H hj) fun u' ⟨H', hz⟩ => ?_
  by_cases he : p.al / 16 - (j + min 8 (p.al / 16 - j)) = 0
  · left
    obtain hje : j + min 8 (p.al / 16 - j) = p.al / 16 := by omega_using [hj, he]
    exact ⟨(eval_ne hz).trans (by simp [he]), hje ▸ H'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), p.al / 16 - (j + min 8 (p.al / 16 - j)), by omega_using [hj],
      j + min 8 (p.al / 16 - j), rfl, by omega_using [he], H'⟩

theorem hash_ok (v : BlocksImpl) {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) (E : Env p s₀) (hl0 : blockAtMem s₀.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (Impl.AesOcb.X86.hash (callees v)) s₀ fun t' => Env p t' ∧ Frame (hashR p) s₀.mem t'.mem ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧
      t'.wr = s₀.wr := by
  unfold Impl.AesOcb.X86.hash
  refine WP.seq (WP.mono (hashHead_ok C E hl0) fun s₃ ⟨H₀, zf₃⟩ => ?_)
  refine WP.seq (WP.ite (decide (p.al / 16 = 0)) (eval_e zf₃) (fun hb => WP.block_nil ?_) (fun hb => ?_))
  · have h0 : p.al / 16 = 0 := of_decide_eq_true hb
    exact hashTail_ok v C (h0 ▸ H₀)
  · exact WP.mono (hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb))) fun u H => hashTail_ok v C H

end VG.Proof.AesOcb.X86
