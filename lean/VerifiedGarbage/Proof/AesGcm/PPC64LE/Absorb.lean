module

import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Data.List.Induction
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Spec.Gcm

/-!
# AES-GCM on PPC64LE: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/Absorb.lean`): `absorb yo` absorbs the `r25` bytes at
`r24` into GHASH, with the accumulator at `st + yo` and the `r26` buffered
bytes at `st + 32` (`absorb_ok`): it fills the buffer (`headPre_ok`,
`head_ok`), absorbs whole blocks (`whole_ok`) and buffers the rest
(`tail_ok`), by the steps of `Proof/Gcm/Stream.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- Branching on a register holding `n`. -/
theorem eval_zero {s : State} {r : Reg} {n : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    isa.eval (.zero .d r) s = some (decide (n = 0)) := by
  show some _ = _
  simp only [State.read, Size.bits, BitVec.setWidth_eq, h]
  by_cases h0 : n = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 n ≠ 0 := fun e => h0 ((ofNat_eq_zero hn).mp e)
    simp only [h0, decide_false, beq_eq_false_iff_ne.mpr this]

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.Cmac.bytesAt_frame hf hd hn

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, bytesAt_frame hf hd (by decide)]

/-- The regions `absorb` writes. -/
abbrev absFrame (st w : Addr) (yo : Nat) : List Region :=
  [⟨st + BitVec.ofNat 64 yo, 16⟩, ⟨st + BitVec.ofNat 64 32, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩]

/-- Before `absorb yo`: GHASH has absorbed `x` (with hash subkey `H`), and
`r24`, `r25`, `r26` hold the data, its length and `len(x) mod 16`. -/
structure AbsIn (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x : List Byte) (D : Addr)
    (n : Nat) (s : State) : Prop where
  env : Env V sp s
  r24 : s.gpr .r24 = D
  r25 : s.gpr .r25 = BitVec.ofNat 64 n
  r26 : s.gpr .r26 = BitVec.ofNat 64 (x.length % 16)
  data : DataOk (V .r30) (V .r31) s D n
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x : List Byte) (D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env V sp s
  le : j ≤ n
  r24 : s.gpr .r24 = D + BitVec.ofNat 64 j
  r25 : s.gpr .r25 = BitVec.ofNat 64 (n - j)
  data : DataOk (V .r30) (V .r31) s D n
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (V .r30 + BitVec.ofNat 64 yo) (V .r30 + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (V .r30 + BitVec.ofNat 64 yo) (V .r30 + BitVec.ofNat 64 32) H
      (x ++ bytesAt m₀ D j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (absFrame (V .r30) (V .r31) yo) m₀ s.mem

/-- After: everything absorbed, from `x₀` absorbed in `m₀` to `x`. -/
structure AbsOut (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  abs : Absorbed m₀ (V .r30 + BitVec.ofNat 64 yo) (V .r30 + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (V .r30 + BitVec.ofNat 64 yo) (V .r30 + BitVec.ofNat 64 32) H x
  frame : Frame (absFrame (V .r30) (V .r31) yo) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31)) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : Addr} {n : Nat} (hd : DataOk (V .r30) (V .r31) s D n) :
    ∀ r ∈ absFrame (V .r30) (V .r31) yo, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))

/-- The hash subkey is apart from what `absorb` writes. -/
theorem ctx_absFrame : ∀ r ∈ absFrame (V .r30) (V .r31) yo,
    (⟨V .r29 + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)

omit L hyo in
/-- A write within the buffer is within what `absorb` writes. -/
theorem buf_absFrame {m m' : Mem} {o k : Nat} (h : Frame [⟨V .r30 + BitVec.ofNat 64 (32 + o), k⟩] m m')
    (hk : o + k ≤ 16) : Frame (absFrame (V .r30) (V .r31) yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega) (by omega)⟩

omit L hyo in
theorem gh_absFrame {m m' : Mem} (h : Frame [⟨V .r30 + BitVec.ofNat 64 yo, 16⟩,
    ⟨V .r31 + BitVec.ofNat 64 512, 256⟩] m m') : Frame (absFrame (V .r30) (V .r31) yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

/-- The hash subkey is apart from what a call of `vg_ghash` writes. -/
theorem ctx_ghFrame : ∀ r ∈ [(⟨V .r30 + BitVec.ofNat 64 yo, 16⟩ : Region),
    ⟨V .r31 + BitVec.ofNat 64 512, 256⟩], (⟨V .r29 + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_w (by decide) (by decide)

end

/-- After `headPre`: `k = min (16 - o, n)` bytes copied into the buffer, the
arguments advanced, and `r6` zero iff the buffer is full. -/
structure HeadMid (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x : List Byte) (D : Addr)
    (n : Nat) (m₀ : Mem) (k : Nat) (s : State) : Prop where
  env : Env V sp s
  kmin : k = min (16 - x.length % 16) n
  k1 : 1 ≤ k
  k16 : x.length % 16 + k ≤ 16
  kn : k ≤ n
  r24 : s.gpr .r24 = D + BitVec.ofNat 64 k
  r25 : s.gpr .r25 = BitVec.ofNat 64 (n - k)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (x.length % 16 + k) - BitVec.ofNat 64 16
  data : DataOk (V .r30) (V .r31) s D n
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H
  buf : bytesAt s.mem (V .r30 + BitVec.ofNat 64 32) (x.length % 16 + k) =
    bytesAt m₀ (V .r30 + BitVec.ofNat 64 32) (x.length % 16) ++ bytesAt m₀ D k
  hY : blockAt s.mem (V .r30 + BitVec.ofNat 64 yo) = blockAt m₀ (V .r30 + BitVec.ofNat 64 yo)
  fw : Frame [⟨V .r30 + BitVec.ofNat 64 (32 + x.length % 16), k⟩] m₀ s.mem

/-- `r6 = a - 16` is zero iff `a = 16`, for `a ≤ 16`. -/
theorem eval_sub16 {s : State} {a : Nat} (h : s.gpr .r6 = BitVec.ofNat 64 a - BitVec.ofNat 64 16)
    (ha : a ≤ 16) : isa.eval (.zero .d .r6) s = some (decide (a = 16)) := by
  show some _ = _
  simp only [State.read, Size.bits, BitVec.setWidth_eq, h]
  congr 1
  by_cases h16 : a = 16
  · subst h16; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 16 ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, toNat64 (by omega), toNat64 (by omega)] at this
      simp at this; omega
    simp only [h16, decide_false, beq_eq_false_iff_ne.mpr this]

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31)) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- Filling the buffer: `minLen`, the copy and the comparison with 16. -/
theorem headPre_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn V sp yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa headPre s (fun s' => ∃ k, HeadMid V sp yo H x D n s.mem k s') := by
  have hlt : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn64 : n < 2 ^ 64 := h.data.lt
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.r26 h.r25 (by omega) hn64) fun s₁ ⟨h5, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - x.length % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h5
  have hk1 : 1 ≤ k := by omega
  have hk16 : x.length % 16 + k ≤ 16 := by omega
  have hkn : k ≤ n := by omega
  have e30 : s₁.gpr .r30 = V .r30 := (hg _ (by decide) (by decide)).trans he.r30
  have e24 : s₁.gpr .r24 = D := (hg _ (by decide) (by decide)).trans h.r24
  have e25 : s₁.gpr .r25 = BitVec.ofNat 64 n := (hg _ (by decide) (by decide)).trans h.r25
  have e26 : s₁.gpr .r26 = BitVec.ofNat 64 (x.length % 16) := (hg _ (by decide) (by decide)).trans h.r26
  have h₂ : WP isa (.block [.addi .r4 .r30 32, .add .r4 .r4 .r26, mov .r3 .r24, .add .r24 .r24 .r5,
      .sub .r25 .r25 .r5, .add .r26 .r26 .r5]) s₁ (fun s₂ : State =>
      s₂.gpr .r3 = D ∧ s₂.gpr .r4 = V .r30 + BitVec.ofNat 64 (32 + x.length % 16) ∧
      s₂.gpr .r24 = D + BitVec.ofNat 64 k ∧ s₂.gpr .r25 = BitVec.ofNat 64 (n - k) ∧
      s₂.gpr .r26 = BitVec.ofNat 64 (x.length % 16 + k) ∧ s₂.gpr .r5 = BitVec.ofNat 64 k ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → s₂.gpr r = s₁.gpr r) ∧
      Keeps s₁ s₂) := by
    crun [e30, e24, e25, e26, h5, mov, BitVec.or_self]
    exact ⟨by rw [add_ofNat_assoc], ofNat_sub64 hkn hn64, ofNat_add64 _ _,
      fun r a b c d e => by simp [a, b, c, d, e], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨h3, h4, h24, h25, h26, h5', hg₂, hk₂⟩ => ?_)
  have hk₂' := hk.trans hk₂
  have lp : LoopPre s₂ D (V .r30 + BitVec.ofNat 64 (32 + x.length % 16)) k := by
    refine ⟨h3, h4, h5', hk1, by omega, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr]; exact (h.data.take hkn).rd
    · rw [hk₂'.wr]; exact he.perm.stC (by omega)
    · exact (h.data.take hkn).st.sub_right (Lay.stSub (by omega))
  refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_)
  rw [hk₂'.mem] at hm₃
  have g₃ : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₃.gpr r = s₂.gpr r := lo.other
  have e26' : s₃.gpr .r26 = BitVec.ofNat 64 (x.length % 16 + k) :=
    (g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h26
  have h₄ : WP isa (.block [.subi .r6 .r26 16]) s₃ (fun s₄ : State =>
      s₄.gpr .r6 = BitVec.ofNat 64 (x.length % 16 + k) - BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .r6 → s₄.gpr r = s₃.gpr r) ∧ Keeps s₃ s₄) := by
    crun [e26']
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono h₄ fun s₄ ⟨h6, g₄, hk₄⟩ => ?_
  have g : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₄.gpr r = s₂.gpr r :=
    fun r a b c d e => by rw [g₄ r e, g₃ r a b c d e]
  have k4rd : s₄.rd = s₂.rd := by rw [hk₄.rd, lo.keeps.1]
  have k4wr : s₄.wr = s₂.wr := by rw [hk₄.wr, lo.keeps.2.1]
  have k4sp : s₄.sp = s₂.sp := by rw [hk₄.sp, lo.keeps.2.2.1]
  -- The bytes copied, and the buffer.
  have hdk := length_bytesAt s.mem D k
  have fw : Frame [⟨V .r30 + BitVec.ofNat 64 (32 + x.length % 16), k⟩] s.mem s₄.mem := by
    rw [hk₄.mem, hm₃]; exact writeBytes_frame' _ hdk
  refine ⟨k, he.keep (fun r hr => by
      rw [g r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide),
        hg₂ r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide),
        hg r (by revert r; decide) (by revert r; decide)])
      (by rw [k4sp, hk₂'.sp]) (by rw [k4rd, hk₂'.rd]) (by rw [k4wr, hk₂'.wr]),
    hk'.symm, hk1, hk16, hkn, ?_, ?_, h6, h.data.of_eq (by rw [k4rd, hk₂'.rd]) (by rw [k4wr, hk₂'.wr]),
    ?_, ?_, ?_, fw⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h24]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h25]
  · rw [blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by omega), h.hH]
  · rw [hk₄.mem, hm₃, show V .r30 + BitVec.ofNat 64 (32 + x.length % 16) =
        V .r30 + BitVec.ofNat 64 32 + BitVec.ofNat 64 (x.length % 16) from (add_ofNat_assoc _ _ _).symm]
    have := bytesAt_writeBytes s.mem (V .r30 + BitVec.ofNat 64 32) (x.length % 16)
      (bytesAt s.mem D k) (by rw [hdk]; omega)
    rwa [hdk] at this
  · exact blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by omega)) (by omega) (by omega)

/-- After `headPre`: the buffer absorbed if full. -/
theorem headPost_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {k : Nat} {s : State}
    (h : HeadMid V sp yo H x D n m₀ k s) :
    WP isa (.ite (.zero .d .r6) (ghash1 yo .r30 32) (.block [])) s
      (fun s' => ∃ j, j = k ∧ AbsMid V sp yo H x D n m₀ j s') := by
  have he := h.env
  have hk1 := h.k1; have hk16 := h.k16; have hkn := h.kn; have hkm := h.kmin
  have hdk := length_bytesAt m₀ D k
  refine WP.ite (decide (x.length % 16 + k = 16)) (eval_sub16 h.r6 hk16) (fun ht => ?_) (fun hf => ?_)
  · -- The buffer is full: absorbed.
    have h16 : x.length % 16 + k = 16 := by simpa using ht
    refine WP.mono (ghash1_ok L hyo he .r30 32 (.inl rfl) (by decide) (P := V .r30 + BitVec.ofNat 64 32)
      (by rw [he.r30]) (Lay.st_st (.inl (by omega)) (by omega) (by decide))
      (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)) (covers_left (he.perm.stC (by decide))))
      fun s₅ g => ?_
    refine ⟨k, rfl, g.env he, hkn, by rw [g.saved _ (by decide)]; exact h.r24,
      by rw [g.saved _ (by decide)]; exact h.r25, h.data.of_eq g.rd g.wr, ?_, ?_, .inr (by omega), ?_⟩
    · rw [blockAt_frame g.frame (ctx_ghFrame L hyo), h.hH]
    · intro ha
      refine Proof.Gcm.absorb_complete ha (by rw [hdk]; exact h16)
        (B := bytesAt s.mem (V .r30 + BitVec.ofNat 64 32) 16) ?_ ?_
      · rw [← h16, h.buf, ha.2]
      · rw [g.out, h.hY, h.hH]; rfl
    · exact (buf_absFrame (yo := yo) (V := V) h.fw hk16).trans (gh_absFrame g.frame)
  · -- Not full: the data is used up.
    have h16 : x.length % 16 + k < 16 := by simp at hf; omega
    refine WP.block_nil ⟨k, rfl, he, hkn, h.r24, h.r25, h.data, h.hH, fun ha => ?_, .inl (by omega),
      buf_absFrame (yo := yo) (V := V) h.fw hk16⟩
    exact Proof.Gcm.absorb_fill ha (by rw [hdk]; exact h16) h.hY (by rw [hdk]; exact h.buf)

/-- Filling the buffer. -/
theorem head_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn V sp yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa (absorbHead yo) s (fun s' => ∃ j, j = min (16 - x.length % 16) n ∧
      AbsMid V sp yo H x D n s.mem j s') :=
  WP.seq (WP.mono (headPre_ok L hyo h hn ho) fun _ ⟨_, hm⟩ =>
    WP.mono (headPost_ok L hyo hm) fun _ ⟨j, hj, h'⟩ => ⟨j, hj.trans hm.kmin, h'⟩)

omit L hyo in
/-- The split of the rest into whole blocks and the last bytes. -/
theorem split_ok {s : State} {D : Addr} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64)
    (h24 : s.gpr .r24 = D + BitVec.ofNat 64 j) (h25 : s.gpr .r25 = BitVec.ofNat 64 (n - j)) :
    WP isa (.block splitWhole) s fun s' =>
      s'.gpr .r5 = D + BitVec.ofNat 64 j ∧ s'.gpr .r6 = BitVec.ofNat 64 ((n - j) / 16) ∧
      s'.gpr .r24 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .r25 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16))) ∧
      (∀ r, r ≠ .r0 → r ≠ .r5 → r ≠ .r6 → r ≠ .r8 → r ≠ .r9 → r ≠ .r24 → r ≠ .r25 →
        s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have hand := and15 (BitVec.ofNat 64 (n - j))
  rw [toNat64 (by omega)] at hand
  have hsub : BitVec.ofNat 64 (n - j) - BitVec.ofNat 64 ((n - j) % 16) =
      BitVec.ofNat 64 (16 * ((n - j) / 16)) := by
    rw [ofNat_sub64 (Nat.mod_le _ _) (by omega)]; congr 1; omega
  simp only [splitWhole]
  crun [h24, h25, mov, BitVec.or_self, hand, hsub, shr4 (show n - j < 2 ^ 64 by omega), add_ofNat_assoc]
  refine ⟨by congr 1; omega, fun r a b c d e f g => by simp [a, b, c, d, e, f, g],
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The whole blocks. -/
theorem whole_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid V sp yo H x D n m₀ j s) (hm₀ : bytesAt s.mem D n = bytesAt m₀ D n) :
    WP isa (absorbWhole yo) s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧
      AbsMid V sp yo H x D n m₀ j' s' ∧ n - j' < 16) := by
  have hn' := h.data.lt
  have he := h.env
  refine WP.seq (WP.mono (split_ok h.le hn' h.r24 h.r25) fun s₁ ⟨h5, h6, h24, h25, hg₁, hk₁⟩ => ?_)
  generalize hnb : (n - j) / 16 = nb at h6 h24 h25
  have h16 : 16 * nb ≤ n - j := by omega
  have he₁ : Env V sp s₁ := he.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr
  have hd₁ : DataOk (V .r30) (V .r31) s₁ D n := h.data.of_eq hk₁.rd hk₁.wr
  refine WP.ite (decide (nb = 0)) (eval_zero h6 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega, ⟨he₁, h.le, by rw [h24]; rfl, by rw [h25]; rfl, hd₁,
      by rw [hk₁.mem]; exact h.hH, fun ha => by rw [hk₁.mem]; exact h.abs ha, h.whole,
      by rw [hk₁.mem]; exact h.frame⟩, by omega⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left (by omega)
    have hdj := h.data.sub (j := j) (k := 16 * nb) (by omega) (by omega)
    have h29 := he₁.r29; have h30 := he₁.r30; have h31 := he₁.r31
    have hyo' : yo < 2 ^ 15 := by omega
    have h₂ : WP isa (.block [.addi .r3 .r29 240, .addi .r4 .r30 yo, .addi .r7 .r31 scrO]) s₁
        (fun s₂ : State => s₂.gpr .r3 = V .r29 + BitVec.ofNat 64 240 ∧
          s₂.gpr .r4 = V .r30 + BitVec.ofNat 64 yo ∧ s₂.gpr .r7 = V .r31 + BitVec.ofNat 64 512 ∧
          (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂) := by
      crun [scrO, h29, h30, h31, hyo']
      exact ⟨fun r a b d => by simp [a, b, d], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    refine WP.seq (WP.mono h₂ fun s₂ ⟨h3', h4', h7', hg₂, hk₂⟩ => ?_)
    have he₂ : Env V sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
    refine WP.mono (ghCall_ok L hyo he₂ (P := D + BitVec.ofNat 64 j) (n := nb) h3' h4'
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h5])
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h6]) h7' (by omega)
      (hdj.st.sub_right (Lay.stSub (by omega))).symm (hdj.w.sub_right (Lay.wSub (by decide)))
      (by rw [hk₂.rd, hk₂.wr, hk₁.rd, hk₁.wr]; exact hdj.rd)) fun s₃ g => ?_
    refine ⟨j + 16 * nb, by omega, ⟨g.env he₂, by omega, ?_, ?_,
      hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr), ?_, ?_, .inr (by omega), ?_⟩, by omega⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h24]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h25]
    · rw [blockAt_frame g.frame (ctx_ghFrame L hyo), hk₂.mem, hk₁.mem]; exact h.hH
    · intro ha
      have ex : x ++ bytesAt m₀ D (j + 16 * nb) =
          (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb) := by
        rw [bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (h.abs ha) (by simp [length_bytesAt]; omega)
        (by simp [length_bytesAt]) ?_
      rw [g.out, hk₂.mem, hk₁.mem, h.hH, Proof.Gcm.blocksAt_eq]
      congr 2
      -- The data is as in `m₀`.
      have e₁ := congrArg (fun l => l.drop j) hm₀
      have e₂ : ∀ m : Mem, (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) :=
        fun m => by
          rw [show n = j + (n - j) by omega, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
            Nat.add_sub_cancel_left]
      simp only [e₂] at e₁
      have e₃ := congrArg (fun l => l.take (16 * nb)) e₁
      have e₄ : ∀ m : Mem, (bytesAt m (D + BitVec.ofNat 64 j) (n - j)).take (16 * nb) =
          bytesAt m (D + BitVec.ofNat 64 j) (16 * nb) := fun m => by
        rw [show n - j = 16 * nb + (n - j - 16 * nb) by omega, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _)]
      simp only [e₄] at e₃
      exact e₃
    · have := g.frame; rw [hk₂.mem, hk₁.mem] at this; exact h.frame.trans (gh_absFrame this)

omit L in
/-- The last bytes, buffered. -/
theorem tail_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid V sp yo H x D n m₀ j s) (hj : n - j < 16) (hm₀ : bytesAt s.mem D n = bytesAt m₀ D n) :
    WP isa absorbTail s (AbsOut V sp yo H x (x ++ bytesAt m₀ D n) m₀) := by
  have hn' := h.data.lt
  have he := h.env
  refine WP.ite (decide (n - j = 0)) (eval_zero h.r25 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega
    subst h0
    exact WP.block_nil ⟨he, h.abs, h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left h0
    have hdj := h.data.sub (j := j) (k := n - j) (by omega) (by omega)
    have h30 := he.r30
    have h₂ : WP isa (.block [mov .r3 .r24, .addi .r4 .r30 32, mov .r5 .r25]) s (fun s₂ : State =>
        s₂.gpr .r3 = D + BitVec.ofNat 64 j ∧ s₂.gpr .r4 = V .r30 + BitVec.ofNat 64 32 ∧
        s₂.gpr .r5 = BitVec.ofNat 64 (n - j) ∧
        (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂) := by
      crun [mov, BitVec.or_self, h.r24, h.r25, h30]
      exact ⟨fun r a b d => by simp [a, b, d], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    refine WP.seq (WP.mono h₂ fun s₂ ⟨h3', h4', h5', hg₂, hk₂⟩ => ?_)
    have lp : LoopPre s₂ (D + BitVec.ofNat 64 j) (V .r30 + BitVec.ofNat 64 32) (n - j) := by
      refine ⟨h3', h4', h5', by omega, by omega, ?_, ?_, ?_⟩
      · rw [hk₂.rd, hk₂.wr]; exact hdj.rd
      · rw [hk₂.wr]; exact he.perm.stC (by omega)
      · exact hdj.st.sub_right (Lay.stSub (by omega))
    refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
    rw [hk₂.mem] at hm₃
    have hlen := length_bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j)
    have fw : Frame [⟨V .r30 + BitVec.ofNat 64 32, n - j⟩] s.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame' _ hlen
    refine ⟨he.keep (fun r hr => by
      rw [lo.other r (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide) (by revert r; decide),
        hg₂ r (by revert r; decide) (by revert r; decide) (by revert r; decide)])
        (lo.keeps.2.2.1.trans hk₂.sp) (lo.keeps.1.trans hk₂.rd) (lo.keeps.2.1.trans hk₂.wr), ?_, ?_⟩
    · intro ha
      have ex : x ++ bytesAt m₀ D n =
          (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
        rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' h.le]
      have ed : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) =
          bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
        have e₁ := congrArg (fun l => l.drop j) hm₀
        have e₂ : ∀ m : Mem, (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) :=
          fun m => by
            rw [show n = j + (n - j) by omega, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
              Nat.add_sub_cancel_left]
        simpa only [e₂] using e₁
      rw [ex, ← ed]
      refine Proof.Gcm.absorb_tail (h.abs ha) (by simp [length_bytesAt]; omega) (by rw [hlen]; omega) ?_ ?_
      · rw [blockAt_frame fw fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Lay.st_st (.inl (by omega)) (by omega) (by omega)]
      · rw [hm₃]; exact bytesAt_writeBytes_self _ _ _ (by rw [hlen]; omega)
    · exact h.frame.trans ((fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega)⟩))

omit L in
theorem AbsMid.data_eq {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid V sp yo H x D n m₀ j s) : bytesAt s.mem D n = bytesAt m₀ D n :=
  bytesAt_frame h.frame (data_absFrame hyo h.data) (by have := h.data.lt; omega)

/-- After the first test: the buffer filled if it holds bytes. -/
theorem absorbFill_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn V sp yo H x D n s) (h0 : n ≠ 0) :
    WP isa (absorbFill yo) s (fun s' => ∃ j, j = (if x.length % 16 = 0 then 0 else min (16 - x.length % 16) n) ∧
      AbsMid V sp yo H x D n s.mem j s') := by
  refine WP.ite (decide (x.length % 16 = 0)) (eval_zero h.r26 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have ho : x.length % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h.env, by omega, by rw [h.r24, BitVec.add_zero],
      by rw [h.r25, Nat.sub_zero], h.data, h.hH, fun ha => by simpa [bytesAt] using ha, .inr (by omega),
      Frame.refl _ _⟩
  · have ho : x.length % 16 ≠ 0 := by simpa using hf
    exact WP.mono (head_ok L hyo h h0 ho) fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [ho, ite_false]; exact hj, hm⟩

/-- `absorb yo`. -/
theorem absorb_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn V sp yo H x D n s) :
    WP isa (absorb yo) s (AbsOut V sp yo H x (x ++ bytesAt s.mem D n) s.mem) := by
  have hn' := h.data.lt
  refine WP.ite (decide (n = 0)) (eval_zero h.r25 hn') (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h.env, fun ha => by simpa [bytesAt] using ha, Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.seq (WP.mono (absorbFill_ok L hyo h h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (whole_ok L hyo hj (hj.data_eq hyo)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact tail_ok hyo hj' hlt (hj'.data_eq hyo)

end

end VG.Proof.AesGcm.PPC64LE
