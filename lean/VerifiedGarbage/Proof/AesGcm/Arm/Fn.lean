module

public import VerifiedGarbage.Proof.AesGcm.Arm.Tag
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesGcm.Arm.Flush
import VerifiedGarbage.Proof.Cmac.Dbl32
public import VerifiedGarbage.Proof.AesGcm.Arm.Blocks
public import VerifiedGarbage.Proof.AesGcm.Arm.Env
public import VerifiedGarbage.Proof.AesGcm.Arm.Run
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
import VerifiedGarbage.Proof.AesGcm.Arm.Loops

/-! ### `AesGcm.Arm.J0`, which this module and modules that import it used -/

section

/-! ### `AesGcm.Arm.Absorb`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. `absorb yo` absorbs the
`r5` bytes at `r4` into GHASH, with the accumulator at `St + yo` and the
`r6` buffered bytes at `St + 32` (`absorb_ok`): it fills the buffer
(`headPre_ok`, `head_ok`), absorbs whole blocks (`whole_ok`) and buffers the
rest (`tail_ok`), by the steps of `Proof/Gcm/Stream.lean`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- The regions `absorb` writes. -/
abbrev absFrame (st w sp : BitVec 32) (yo : Nat) : List Region :=
  [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩, ⟨State.addr st + BitVec.ofNat 64 32, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

/-- Before `absorb yo`: GHASH has absorbed `x` (with hash subkey `H`), and
`r4`, `r5`, `r6` hold the data, its length and `len(x) mod 16`. -/
structure AbsIn (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x : List Byte) (D : BitVec 32) (n : Nat)
    (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  r4 : s.gpr .r4 = D
  r5 : s.gpr .r5 = BitVec.ofNat 32 n
  r6 : s.gpr .r6 = BitVec.ofNat 32 (x.length % 16)
  data : DataOk st w sp s D n
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x : List Byte) (D : BitVec 32) (n : Nat)
    (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  le : j ≤ n
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)
  data : DataOk st w sp s D n
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H
      (x ++ bytesAt m₀ (State.addr D) j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (absFrame st w sp yo) m₀ s.mem

/-- After: everything absorbed, from `x₀` absorbed in `m₀` to `x`. -/
structure AbsOut (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env c st w sp k7 k8 s
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x
  frame : Frame (absFrame st w sp yo) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk st w sp s D n) :
    ∀ r ∈ absFrame st w sp yo, (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega_arith))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

/-- The context is apart from what `absorb` writes. -/
theorem ctx_absFrame : ∀ r ∈ absFrame st w sp yo,
    (⟨State.addr c + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega_arith)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

omit L hyo in
/-- A write within the buffer is within what `absorb` writes. -/
theorem buf_absFrame {m m' : Mem} {o k : Nat} (h : Frame [⟨State.addr st + BitVec.ofNat 64 (32 + o), k⟩] m m')
    (hk : o + k ≤ 16) : Frame (absFrame st w sp yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega_arith) (by omega_arith)⟩

omit L hyo in
theorem gh_absFrame {m m' : Mem} (h : Frame [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp] m m') : Frame (absFrame st w sp yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

end

/-- After `headPre`: `k = min (16 - o, n)` bytes copied into the buffer, the
arguments advanced, and `Z` set iff the buffer is full. -/
structure HeadMid (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x : List Byte) (D : BitVec 32) (n : Nat)
    (m₀ : Mem) (k : Nat) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  kmin : k = min (16 - x.length % 16) n
  k1 : 1 ≤ k
  k16 : x.length % 16 + k ≤ 16
  kn : k ≤ n
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 (k)
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - k)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (x.length % 16 + k)
  z : s.z = decide (x.length % 16 + k = 16)
  data : DataOk st w sp s D n
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  buf : bytesAt s.mem (State.addr st + BitVec.ofNat 64 32) (x.length % 16 + k) =
    bytesAt m₀ (State.addr st + BitVec.ofNat 64 32) (x.length % 16) ++
      bytesAt m₀ (State.addr D) (k)
  hY : blockAt s.mem (State.addr st + BitVec.ofNat 64 yo) = blockAt m₀ (State.addr st + BitVec.ofNat 64 yo)
  fw : Frame [⟨State.addr st + BitVec.ofNat 64 (32 + x.length % 16), k⟩] m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- Filling the buffer: `minLen`, the copy and the comparison with 16. -/
theorem headPre_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : AbsIn c st w sp k7 k8 yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa headPre s (fun s' => ∃ k, HeadMid c st w sp k7 k8 yo H x D n s.mem k s') := by
  obtain hlt : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn32 : n < 2 ^ 32 := h.data.lt32
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.r6 h.r5 (by omega_arith) hn32) fun s₁ ⟨h3, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - x.length % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h3
  obtain hk1 : 1 ≤ k := by omega_arith
  obtain hk16 : x.length % 16 + k ≤ 16 := by omega_arith
  obtain hkn : k ≤ n := by omega_arith
  obtain ⟨s₂, run₂, h1, h2, h4, h5, h6, h3', hg₂, hk₂⟩ : ∃ s₂, runBlock isa [addI .r2 .r10 32,
      .dp .add .r2 .r2 (.reg .r6), .mov .r1 (.reg .r4), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3),
      .dp .add .r6 .r6 (.reg .r3)] s₁ = some s₂ ∧
      s₂.gpr .r1 = D ∧ s₂.gpr .r2 = st + BitVec.ofNat 32 (32 + x.length % 16) ∧
      s₂.gpr .r4 = D + BitVec.ofNat 32 k ∧ s₂.gpr .r5 = BitVec.ofNat 32 (n - k) ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (x.length % 16 + k) ∧ s₂.gpr .r3 = BitVec.ofNat 32 k ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    obtain e10 := hg .r10 (by decide) (by decide)
    obtain e4 := hg .r4 (by decide) (by decide)
    obtain e5 := hg .r5 (by decide) (by decide)
    obtain e6 := hg .r6 (by decide) (by decide)
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e4, h.r4]
    · simp [gpr_setReg, e10, e6, he.r10, h.r6, add32_ofNat_assoc]
    · simp [gpr_setReg, e4, h.r4, h3]
    · simp [gpr_setReg, e5, h.r5, h3, ofNat_sub32 hkn hn32]
    · simp [gpr_setReg, e6, h.r6, h3, ofNat_add32]
    · simp [gpr_setReg, h3]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain hk₂' := hk.trans hk₂
  obtain eB : State.addr (st + BitVec.ofNat 32 (32 + x.length % 16)) =
      State.addr st + BitVec.ofNat 64 (32 + x.length % 16) := L.stA (by omega_arith)
  obtain lp : LoopPre s₂ D (st + BitVec.ofNat 32 (32 + x.length % 16)) k := by
    refine ⟨h1, h2, h3', hk1, by omega_arith, by have := h.data.fit; omega_arith,
      by rw [L.stN (by omega_arith)]; have := L.sw; omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr]; exact (h.data.take hkn).rd
    · rw [hk₂'.wr, eB]; exact he.perm.stC (by omega_arith)
    · rw [eB]; exact (h.data.take hkn).st.sub_right (Lay.stSub (by omega_arith))
  refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_)
  rw [eB, hk₂'.mem] at hm₃
  obtain ⟨s₄, run₄, hz₄, hg₄, hk₄⟩ := cmpk_ok s₃ .r6 (n := x.length % 16 + k) (k := 16)
    (by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]) (by omega_arith)
    (by decide) (by decide)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  obtain g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₄.gpr r = s₂.gpr r :=
    fun r a b c d e => by rw [hg₄, lo.other r a b c d e]
  -- The bytes copied, and the buffer.
  obtain hdk := length_bytesAt s.mem (State.addr D) k
  obtain fw : Frame [⟨State.addr st + BitVec.ofNat 64 (32 + x.length % 16), k⟩] s.mem s₄.mem := by
    rw [hk₄.1, hm₃]; exact writeBytes_frame' _ hdk
  refine ⟨k, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hg _ (by decide) (by decide)])
      (by rw [hk₄.2.2.2, lo.sp, hk₂'.sp]) (by rw [hk₄.2.1, lo.rd, hk₂'.rd]) (by rw [hk₄.2.2.1, lo.wr, hk₂'.wr]),
    hk'.symm, hk1, hk16, hkn, ?_, ?_, ?_, hz₄, h.data.of_eq (by rw [hk₄.2.1, lo.rd, hk₂'.rd]) (by rw [hk₄.2.2.1, lo.wr, hk₂'.wr]),
    ?_, ?_, ?_, fw⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h4]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h5]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]
  · rw [blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by omega_arith), h.hH]
  · rw [hk₄.1, hm₃, show State.addr st + BitVec.ofNat 64 (32 + x.length % 16) =
        State.addr st + BitVec.ofNat 64 32 + BitVec.ofNat 64 (x.length % 16) from (add_ofNat_assoc _ _ _).symm]
    have := bytesAt_writeBytes s.mem (State.addr st + BitVec.ofNat 64 32) (x.length % 16)
      (bytesAt s.mem (State.addr D) k) (by rw [hdk]; omega_arith)
    rwa [hdk] at this
  · exact blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by omega_arith)) (by omega_arith) (by omega_arith)

end

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- After `headPre`: the buffer absorbed if full. -/
theorem headPost_ok [VG.Proof.Gcm.Arm.GhashLaw] {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {k : Nat} {s : State}
    (h : HeadMid c st w sp k7 k8 yo H x D n m₀ k s) :
    WP isa (.ite .eq (ghash1 yo .r10 32) (.block [])) s
      (fun s' => ∃ j, j = k ∧ AbsMid c st w sp k7 k8 yo H x D n m₀ j s') := by
  have he := h.env
  obtain hk1 := h.k1; have hk16 := h.k16; have hkn := h.kn; have hkm := h.kmin
  obtain hdk := length_bytesAt m₀ (State.addr D) k
  refine WP.ite (decide (x.length % 16 + k = 16)) (eval_eq' h.z) (fun ht => ?_) (fun hf => ?_)
  · -- The buffer is full: absorbed.
    obtain h16 : x.length % 16 + k = 16 := by simpa using ht
    refine WP.mono (ghash1_ok L hyo he .r10 32 (.inl rfl) (by decide) (P := st + BitVec.ofNat 32 32)
      (by rw [he.r10]) (by rw [L.stN (by decide)]; have := L.sw; omega_arith) ?_ ?_ ?_ ?_) fun s₅ g => ?_
    · rw [L.stA (by decide)]; exact Lay.st_st (.inl (by omega_arith)) (by omega_arith) (by decide)
    · rw [L.stA (by decide)]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · rw [L.stA (by decide)]; exact L.stk_st (by decide)
    · rw [L.stA (by decide)]; exact covers_left (he.perm.stC (by decide))
    refine ⟨k, rfl, g.env he, hkn, by rw [g.saved _ (by decide) (by decide)]; exact h.r4,
      by rw [g.saved _ (by decide) (by decide)]; exact h.r5, h.data.of_eq g.rd g.wr, ?_, ?_, .inr (by omega_arith), ?_⟩
    · rw [blockAt_frame g.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega_arith)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm, h.hH]
    · intro ha
      refine Proof.Gcm.absorb_complete ha (by rw [hdk]; exact h16)
        (B := bytesAt s.mem (State.addr st + BitVec.ofNat 64 32) 16) ?_ ?_
      · rw [← h16, h.buf, ha.2]
      · rw [g.out, h.hY, h.hH, L.stA (by decide)]; rfl
    · exact (buf_absFrame (yo := yo) (w := w) (sp := sp) h.fw hk16).trans (gh_absFrame g.frame)
  · -- Not full: the data is used up.
    obtain h16 : x.length % 16 + k < 16 := by simp at hf; omega_arith
    refine WP.block_nil ⟨k, rfl, he, hkn, h.r4, h.r5, h.data, h.hH, fun ha => ?_, .inl (by omega_arith),
      buf_absFrame (yo := yo) (w := w) (sp := sp) h.fw hk16⟩
    exact Proof.Gcm.absorb_fill ha (by rw [hdk]; exact h16) h.hY (by rw [hdk]; exact h.buf)

/-- Filling the buffer. -/
theorem head_ok [VG.Proof.Gcm.Arm.GhashLaw] {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : AbsIn c st w sp k7 k8 yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa (absorbHead yo) s (fun s' => ∃ j, j = min (16 - x.length % 16) n ∧
      AbsMid c st w sp k7 k8 yo H x D n s.mem j s') :=
  WP.seq (WP.mono (headPre_ok L hyo h hn ho) fun _ ⟨_, hm⟩ =>
    WP.mono (headPost_ok L hyo hm) fun _ ⟨j, hj, h'⟩ => ⟨j, hj.trans hm.kmin, h'⟩)

end

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L hyo in
/-- The split of the rest into whole blocks and the last bytes. -/
theorem split_ok {s : State} {D : BitVec 32} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 32)
    (h4 : s.gpr .r4 = D + BitVec.ofNat 32 j) (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)) :
    ∃ s', runBlock isa splitWhole s = some s' ∧
      s'.gpr .r2 = D + BitVec.ofNat 32 j ∧ s'.gpr .r3 = BitVec.ofNat 32 ((n - j) / 16) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .r5 = BitVec.ofNat 32 (n - (j + 16 * ((n - j) / 16))) ∧
      s'.z = decide ((n - j) / 16 = 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain hand := and15 (BitVec.ofNat 32 (n - j))
  rw [toNat32 (by omega_arith)] at hand
  obtain hsub : BitVec.ofNat 32 (n - j) - BitVec.ofNat 32 ((n - j) % 16) = BitVec.ofNat 32 (16 * ((n - j) / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) (by omega_arith)]; congr 1; omega_arith
  refine ⟨_, by simp only [splitWhole]; arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h4]
  · simp [gpr_setReg, h5, shr4 (show n - j < 2 ^ 32 by omega_arith)]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h4, h5, hand, hsub, add32_ofNat_assoc]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, hand]
    congr 1; omega_arith
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, shr4 (show n - j < 2 ^ 32 by omega_arith)]
    rw [z_cmp (by omega_arith) (by decide)]
  · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The whole blocks. -/
theorem whole_ok [VG.Proof.Gcm.Arm.GhashLaw] {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid c st w sp k7 k8 yo H x D n m₀ j s) (hm₀ : bytesAt s.mem (State.addr D) n = bytesAt m₀ (State.addr D) n) :
    WP isa (absorbWhole yo) s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧
      AbsMid c st w sp k7 k8 yo H x D n m₀ j' s' ∧ n - j' < 16) := by
  have hn' := h.data.lt32
  have he := h.env
  obtain ⟨s₁, run₁, h2, h3, h4, h5, hz, hg₁, hk₁⟩ := split_ok h.le hn' h.r4 h.r5
  generalize hnb : (n - j) / 16 = nb at h3 h4 h5 hz
  obtain h16 : 16 * nb ≤ n - j := by omega_arith
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) hk₁.sp hk₁.rd hk₁.wr
  obtain hd₁ : DataOk st w sp s₁ D n := h.data.of_eq hk₁.rd hk₁.wr
  refine WP.ite (decide (nb = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega_arith, ⟨he₁, h.le, by rw [h4]; rfl, by rw [h5]; rfl, hd₁, by rw [hk₁.mem]; exact h.hH,
      fun ha => by rw [hk₁.mem]; exact h.abs ha, h.whole, by rw [hk₁.mem]; exact h.frame⟩, by omega_arith⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    obtain hw : (x.length + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
    obtain hdj := h.data.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    obtain h9 := he₁.r9; have h10 := he₁.r10; have h11 := he₁.r11
    obtain ⟨s₂, run₂, h0', h1', h12', hg₂, hk₂⟩ : ∃ s₂, runBlock isa
        [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r12 .r11 scrO] s₁ = some s₂ ∧
        s₂.gpr .r0 = c + BitVec.ofNat 32 240 ∧ s₂.gpr .r1 = st + BitVec.ofNat 32 yo ∧
        s₂.gpr .r12 = w + BitVec.ofNat 32 512 ∧
        (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r12 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
      refine ⟨_, by arun [show encodable (BitVec.ofNat 32 yo) = true by rcases hyo with rfl | rfl <;> decide], ?_,
        ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h9]
      · simp [gpr_setReg, h10]
      · simp [gpr_setReg, h11]
      · intro r a b d; simp [gpr_setReg, a, b, d]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    obtain he₂ : Env c st w sp k7 k8 s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hk₂.sp hk₂.rd hk₂.wr
    obtain eD := h.data.addr (j := j) (by omega_arith)
    refine WP.mono (ghCall_ok L hyo he₂ (P := D + BitVec.ofNat 32 j) (n := nb) h0' h1'
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h2])
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h3]) h12' (by have := hdj.fit; omega_arith)
      (hdj.st.sub_right (Lay.stSub (by omega_arith))).symm (hdj.w.sub_right (Lay.wSub (by decide))) hdj.stk
      (by rw [hk₂.rd, hk₂.wr, hk₁.rd, hk₁.wr]; exact hdj.rd)) fun s₃ g => ?_
    refine ⟨j + 16 * nb, by omega_arith, ⟨g.env he₂, by omega_arith, ?_, ?_, hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr), ?_, ?_,
      .inr (by omega_arith), ?_⟩, by omega_arith⟩
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide), h4]
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide), h5]
    · rw [blockAt_frame g.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega_arith)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm), hk₂.mem, hk₁.mem]; exact h.hH
    · intro ha
      obtain ex : x ++ bytesAt m₀ (State.addr D) (j + 16 * nb) =
          (x ++ bytesAt m₀ (State.addr D) j) ++ bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (16 * nb) := by
        rw [bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (h.abs ha) (by simp [length_bytesAt]; omega_arith) (by simp [length_bytesAt]) ?_
      rw [g.out, hk₂.mem, hk₁.mem, h.hH, Proof.Gcm.blocksAt_eq, eD]
      congr 2
      -- The data is as in `m₀`.
      obtain e₁ := congrArg (fun l => l.drop j) hm₀
      obtain e₂ : ∀ m : Mem, (bytesAt m (State.addr D) n).drop j =
          bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j) := fun m => by
        rw [show n = j + (n - j) by omega_arith, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
          Nat.add_sub_cancel_left]
      simp only [e₂] at e₁
      obtain e₃ := congrArg (fun l => l.take (16 * nb)) e₁
      obtain e₄ : ∀ m : Mem, (bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j)).take (16 * nb) =
          bytesAt m (State.addr D + BitVec.ofNat 64 j) (16 * nb) := fun m => by
        rw [show n - j = 16 * nb + (n - j - 16 * nb) by omega_arith, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _)]
      simp only [e₄] at e₃
      exact e₃
    · have := g.frame; rw [hk₂.mem, hk₁.mem] at this; exact h.frame.trans (gh_absFrame this)

/-- The last bytes, buffered. -/
theorem tail_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid c st w sp k7 k8 yo H x D n m₀ j s) (hj : n - j < 16)
    (hm₀ : bytesAt s.mem (State.addr D) n = bytesAt m₀ (State.addr D) n) :
    WP isa absorbTail s (AbsOut c st w sp k7 k8 yo H x (x ++ bytesAt m₀ (State.addr D) n) m₀) := by
  have hn' := h.data.lt32
  have he := h.env
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 h.r5 (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁
  refine WP.ite (decide (n - j = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega_arith
    subst h0
    exact WP.block_nil ⟨he₁, fun ha => by rw [hm₁]; exact h.abs ha, by rw [hm₁]; exact h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    obtain hw : (x.length + j) % 16 = 0 := h.whole.resolve_left h0
    obtain hdj := h.data.sub (j := j) (k := n - j) (by omega_arith) (by omega_arith)
    obtain eD := h.data.addr (j := j) (by omega_arith)
    have h10 := he₁.r10
    obtain ⟨s₂, run₂, h1', h2', h3', hg₂, hk₂⟩ : ∃ s₂, runBlock isa
        [.mov .r1 (.reg .r4), addI .r2 .r10 32, .mov .r3 (.reg .r5)] s₁ = some s₂ ∧
        s₂.gpr .r1 = D + BitVec.ofNat 32 j ∧ s₂.gpr .r2 = st + BitVec.ofNat 32 32 ∧
        s₂.gpr .r3 = BitVec.ofNat 32 (n - j) ∧
        (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
      refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, hg₁, h.r4]
      · simp [gpr_setReg, h10]
      · simp [gpr_setReg, hg₁, h.r5]
      · intro r a b d; simp [gpr_setReg, a, b, d]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    obtain eB := L.stA (d := 32) (by decide)
    obtain lp : LoopPre s₂ (D + BitVec.ofNat 32 j) (st + BitVec.ofNat 32 32) (n - j) := by
      refine ⟨h1', h2', h3', by omega_arith, by omega_arith, hdj.fit, by rw [L.stN (by decide)]; have := L.sw; omega_arith, ?_, ?_, ?_⟩
      · rw [hk₂.rd, hk₂.wr, hrd₁, hwr₁]; exact hdj.rd
      · rw [hk₂.wr, hwr₁, eB]; exact he.perm.stC (by omega_arith)
      · rw [eB]; exact hdj.st.sub_right (Lay.stSub (by omega_arith))
    refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
    rw [hk₂.mem, hm₁, eB, eD] at hm₃
    obtain hlen := length_bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j)
    obtain fw : Frame [⟨State.addr st + BitVec.ofNat 64 32, n - j⟩] s.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame' _ hlen
    refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hg₂ _ (by decide) (by decide) (by decide)]) (lo.sp.trans hk₂.sp) (lo.rd.trans hk₂.rd)
          (lo.wr.trans hk₂.wr), ?_, ?_⟩
    · intro ha
      obtain ex : x ++ bytesAt m₀ (State.addr D) n =
          (x ++ bytesAt m₀ (State.addr D) j) ++ bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j) := by
        rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' h.le]
      obtain ed : bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j) =
          bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j) := by
        obtain e₁ := congrArg (fun l => l.drop j) hm₀
        obtain e₂ : ∀ m : Mem, (bytesAt m (State.addr D) n).drop j =
            bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j) := fun m => by
          rw [show n = j + (n - j) by omega_arith, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
            Nat.add_sub_cancel_left]
        simpa only [e₂] using e₁
      rw [ex, ← ed]
      refine Proof.Gcm.absorb_tail (h.abs ha) (by simp [length_bytesAt]; omega_arith) (by rw [hlen]; omega_arith) ?_ ?_
      · rw [blockAt_frame fw fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]
      · rw [hm₃]; exact bytesAt_writeBytes_self _ _ _ (by rw [hlen]; omega_arith)
    · exact h.frame.trans ((fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega_arith)⟩))

omit L hyo in
theorem AbsIn.keep {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s s' : State}
    (h : AbsIn c st w sp k7 k8 yo H x D n s) (hg : s'.gpr = s.gpr) (hk : Keeps s s') : AbsIn c st w sp k7 k8 yo H x D n s' where
  env := h.env.keep (fun r _ => by rw [hg]) hk.sp hk.rd hk.wr
  r4 := by rw [hg]; exact h.r4
  r5 := by rw [hg]; exact h.r5
  r6 := by rw [hg]; exact h.r6
  data := h.data.of_eq hk.rd hk.wr
  hH := by rw [hk.mem]; exact h.hH

omit L in
theorem AbsMid.data_eq {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid c st w sp k7 k8 yo H x D n m₀ j s) : bytesAt s.mem (State.addr D) n = bytesAt m₀ (State.addr D) n :=
  bytesAt_frame h.frame (data_absFrame hyo h.data) (by have := h.data.lt; omega_arith)

/-- After the first test: the buffer filled if it holds bytes. -/
theorem absorbFill_ok [VG.Proof.Gcm.Arm.GhashLaw] {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : AbsIn c st w sp k7 k8 yo H x D n s) (h0 : n ≠ 0) :
    WP isa (absorbFill yo) s (fun s' => ∃ j, j = (if x.length % 16 = 0 then 0 else min (16 - x.length % 16) n) ∧
      AbsMid c st w sp k7 k8 yo H x D n s.mem j s') := by
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂, hsp₂⟩ := cmp0_ok s .r6 h.r6
    (by have := Nat.mod_lt x.length (show 16 > 0 by decide); omega_arith)
  obtain h₂ := h.keep hg₂ ⟨hm₂, hrd₂, hwr₂, hsp₂⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.ite (decide (x.length % 16 = 0)) (eval_eq' hz₂) (fun ht => ?_) (fun hf => ?_)
  · have ho : x.length % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h₂.env, by omega_arith, by rw [h₂.r4, add_ofNat_zero], by rw [h₂.r5, Nat.sub_zero], h₂.data,
      h₂.hH, fun ha => by rw [hm₂]; simpa [bytesAt] using ha, .inr (by omega_arith), by rw [hm₂]; exact Frame.refl _ _⟩
  · have ho : x.length % 16 ≠ 0 := by simpa using hf
    have := head_ok L hyo h₂ h0 ho
    rw [hm₂] at this
    exact WP.mono this fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [ho, ite_false]; exact hj, hm⟩

/-- `absorb yo`. -/
theorem absorb_ok [VG.Proof.Gcm.Arm.GhashLaw] {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : AbsIn c st w sp k7 k8 yo H x D n s) :
    WP isa (absorb yo) s (AbsOut c st w sp k7 k8 yo H x (x ++ bytesAt s.mem (State.addr D) n) s.mem) := by
  have hn' := h.data.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 h.r5 hn'
  obtain h₁ := h.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨h₁.env, fun ha => by rw [hm₁]; simpa [bytesAt] using ha, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    rw [← hm₁]
    refine WP.seq (WP.mono (absorbFill_ok L hyo h₁ h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (whole_ok L hyo hj (hj.data_eq hyo)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact tail_ok L hyo hj' hlt (hj'.data_eq hyo)

end

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`r5`-byte nonce at `r4` to the state: its words and `0x00000001` for a
12-byte nonce (`j012_ok`), and otherwise GHASH of the nonce padded with
zeros and the lengths block, with `absorb`, `flush` and `lens` on the
accumulator at the state's first block (`j0hash_ok`), the nonce's length
kept in `r7`. `initState` then zeroes the accumulator and writes the first
counter block `inc₃₂(J₀)` (`initState_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem inc32_words (a b c d : BitVec 32) : inc32 (a ++ b ++ c ++ d) = a ++ b ++ c ++ (d + 1) := by
  obtain h₁ : (a ++ b ++ c ++ d).extractLsb' 32 96 = a ++ b ++ c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    simp only [show ¬ (32 + i < 32) by omega_using [], ite_false, show 32 + i - 32 = i by omega_using []]
  obtain h₂ : (a ++ b ++ c ++ d).extractLsb' 0 32 = d := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]
  simp only [inc32, h₁, h₂]

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  obtain h := Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32,
    Cmac.byteRev32_byteRev32] at h
  rw [h, Cmac.ofBytes_toBytes]

/-- The regions `j0` writes. -/
abbrev j0Frame (st w sp : BitVec 32) : List Region :=
  [⟨State.addr st, 80⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

/-- Before `j0`: the `n`-byte nonce at `Np`. -/
structure J0In (c st w sp k7 k8 : BitVec 32) (H : Block) (Np : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  r4 : s.gpr .r4 = Np
  r5 : s.gpr .r5 = BitVec.ofNat 32 n
  data : DataOk st w sp s Np n

/-- `J₀` written, from `m₀`, with some value of `r7`. -/
structure J0Mid (c st w sp k8 : BitVec 32) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (State.addr st) = Spec.Gcm.j0 H iv
  frame : Frame (j0Frame st w sp) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (c st w sp k8 : BitVec 32) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (State.addr st) = Spec.Gcm.j0 H iv
  y : blockAt s.mem (State.addr st + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (State.addr st + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (j0Frame st w sp) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨State.addr st + BitVec.ofNat 64 d, k⟩] m m')
    (hk : d + k ≤ 80) : Frame (j0Frame st w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Lay.stSub hk⟩

/-- `J₀` of a 12-byte nonce. -/
theorem j012_ok {H : Block} {Np : BitVec 32} {s : State} (h : J0In c st w sp k7 k8 H Np 12 s) :
    WP isa (.block j012) s (J0Mid c st w sp k8 H (bytesAt s.mem (State.addr Np) 12) s.mem) := by
  have he := h.env
  have h10 := he.r10
  have hd := h.data
  obtain a₁ := hd.addr (j := 4) (by decide)
  obtain a₂ := hd.addr (j := 8) (by decide)
  obtain r₀ := in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  obtain r₁ := in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  obtain r₂ := in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  simp only [add_ofNat_zero] at r₀
  obtain w₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  obtain w₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  obtain w₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  obtain w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at w₀
  have h4 := h.r4
  obtain ⟨s', run, hm, hg, hrd, hwr, hsp⟩ : ∃ s', runBlock isa j012 s = some s' ∧
      s'.mem = store4 s.mem (State.addr st) (s.mem.readW (State.addr Np) 32)
        (s.mem.readW (State.addr Np + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr Np + BitVec.ofNat 64 8) 32)
        (BitVec.ofNat 32 0x01000000) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    refine ⟨_, by simp only [j012]; arun [h4, h10, add_ofNat_zero, a₁, a₂, L.stA, r₀, r₁, r₂, w₀, w₁, w₂, w₃],
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, store4_eq]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    all_goals rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  obtain f : Frame [⟨State.addr st + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [hm]; simpa using Cmac.frame_store4 (m := s.mem) (State.addr st) _ _ _ _
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide) (by decide))
      hsp hrd hwr⟩, ?_, ?_, st_j0Frame f (by decide)⟩
  · rw [blockAt_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
  · have hb : bytesAt s.mem (State.addr Np) 12 = bytesAt s.mem (State.addr Np) 4 ++
        bytesAt s.mem (State.addr Np + BitVec.ofNat 64 4) 4 ++ bytesAt s.mem (State.addr Np + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, bytesAt_add,
        add_ofNat_assoc, List.append_assoc]
    rw [Proof.Gcm.j0_12 _ (length_bytesAt _ _ _), blockAt, hm, Cmac.bytesAt_store4, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, le4_one, hb]

/-- The first counter block, and the accumulator zeroed. -/
theorem initState_ok {H : Block} {iv : List Byte} {m₀ : Mem} {s : State} (h : J0Mid c st w sp k8 H iv m₀ s) :
    WP isa (.block initState) s (J0Out c st w sp k8 H iv m₀) := by
  obtain ⟨k7', he⟩ := h.env
  have h10 := he.r10
  obtain r₀ := he.perm.stR (show 0 + 4 ≤ 80 by decide)
  obtain r₁ := he.perm.stR (show 4 + 4 ≤ 80 by decide)
  obtain r₂ := he.perm.stR (show 8 + 4 ≤ 80 by decide)
  obtain r₃ := he.perm.stR (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at r₀
  obtain w₀ := he.perm.stW (show 48 + 4 ≤ 80 by decide)
  obtain w₁ := he.perm.stW (show 52 + 4 ≤ 80 by decide)
  obtain w₂ := he.perm.stW (show 56 + 4 ≤ 80 by decide)
  obtain w₃ := he.perm.stW (show 60 + 4 ≤ 80 by decide)
  obtain z₀ := he.perm.stW (show 16 + 4 ≤ 80 by decide)
  obtain z₁ := he.perm.stW (show 20 + 4 ≤ 80 by decide)
  obtain z₂ := he.perm.stW (show 24 + 4 ≤ 80 by decide)
  obtain z₃ := he.perm.stW (show 28 + 4 ≤ 80 by decide)
  generalize hw : s.mem.readW (State.addr st + BitVec.ofNat 64 12) 32 = w3
  have split : initState =
      [.ldr .r0 .r10 0, .ldr .r1 .r10 4, .ldr .r2 .r10 8, .ldr .r3 .r10 12, .rev .r3 .r3, addI .r3 .r3 1,
        .rev .r3 .r3, .str .r0 .r10 48, .str .r1 .r10 52, .str .r2 .r10 56, .str .r3 .r10 60] ++
      [.mov .r0 (imm 0), .str .r0 .r10 16, .str .r0 .r10 20, .str .r0 .r10 24, .str .r0 .r10 28] := rfl
  obtain ⟨s₁, run₁, hm₁, hg₁, hrd₁, hwr₁, hsp₁⟩ : ∃ s₁, runBlock isa
      [.ldr .r0 .r10 0, .ldr .r1 .r10 4, .ldr .r2 .r10 8, .ldr .r3 .r10 12, .rev .r3 .r3, addI .r3 .r3 1,
        .rev .r3 .r3, .str .r0 .r10 48, .str .r1 .r10 52, .str .r2 .r10 56, .str .r3 .r10 60] s = some s₁ ∧
      s₁.mem = store4 s.mem (State.addr st + BitVec.ofNat 64 48) (s.mem.readW (State.addr st) 32)
        (s.mem.readW (State.addr st + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr st + BitVec.ofNat 64 8) 32)
        (byteRev32 (byteRev32 w3 + BitVec.ofNat 32 1)) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      s₁.sp = s.sp := by
    refine ⟨_, by arun [h10, add_ofNat_zero, L.stA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, store4_eq, add_ofNat_assoc,
        rev_eq, hw, Nat.reduceAdd]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    all_goals rfl
  obtain h10' : s₁.gpr .r10 = st := by rw [hg₁ _ (by decide) (by decide) (by decide) (by decide), h10]
  rw [← hwr₁] at z₀ z₁ z₂ z₃
  obtain ⟨s', run, hm, hg, hrd, hwr, hsp⟩ : ∃ s', runBlock isa
      [.mov .r0 (imm 0), .str .r0 .r10 16, .str .r0 .r10 20, .str .r0 .r10 24, .str .r0 .r10 28] s₁ = some s' ∧
      s'.mem = store4 s₁.mem (State.addr st + BitVec.ofNat 64 16) 0 0 0 0 ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s₁.gpr r) ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧ s'.sp = s₁.sp := by
    refine ⟨_, by arun [h10', L.stA, z₀, z₁, z₂, z₃], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc, Nat.reduceAdd]; rfl
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  rw [split]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s', run, ?_⟩⟩)
  obtain f₄ : Frame [⟨State.addr st + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by
    rw [hm₁]; exact Cmac.frame_store4 _ _ _ _ _
  obtain fz : Frame [⟨State.addr st + BitVec.ofNat 64 16, 16⟩] s₁.mem s'.mem := by
    rw [hm]; exact Cmac.frame_store4 _ _ _ _ _
  obtain dz : (⟨State.addr st + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨State.addr st + BitVec.ofNat 64 16, 16⟩ :=
    Lay.st_st (.inr (by decide)) (by decide) (by decide)
  obtain ff : Frame [⟨State.addr st + BitVec.ofNat 64 0, 80⟩] s.mem s'.mem := by
    refine (f₄.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  obtain hJ : blockAt s'.mem (State.addr st) = blockAt s.mem (State.addr st) := by
    rw [blockAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide)
          (by decide)),
      blockAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 48) (k := 16) (.inl (by decide)) (by decide)
          (by decide))]
  refine ⟨⟨k7', he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [hg _ (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide)])
      (hsp.trans hsp₁) (hrd.trans hrd₁) (hwr.trans hwr₁)⟩, ?_, by rw [hJ, h.j0], ?_, ?_,
    h.frame.trans (st_j0Frame ff (by decide))⟩
  · rw [blockAt_frame ff (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm, Cmac.bytesAt_store4, Cmac.le4_zero]; decide
  · rw [blockAt, bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dz) (by decide),
      hm₁, Cmac.bytesAt_store4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, ← h.j0, blockAt,
      Cmac.ofBytes_rev4, ← Cmac.le4_readW s.mem (State.addr st), ← Cmac.le4_readW, ← Cmac.le4_readW, ofBytes_le4, hw,
      Cmac.byteRev32_byteRev32, inc32_words]
    rfl

end

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

omit L in
theorem abs_j0Frame {m m' : Mem} (h : Frame (absFrame st w sp 0) m m') : Frame (j0Frame st w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (tFrame st w sp 0) m m') : Frame (j0Frame st w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- The first block of `j0hash`: the accumulator at the state zeroed, the
nonce's length kept in `r7`. -/
theorem j0zero_ok {H : Block} {Np : BitVec 32} {n : Nat} {s : State} (h : J0In c st w sp k7 k8 H Np n s) :
    WP isa (.block [.mov .r0 (imm 0), .str .r0 .r10 0, .str .r0 .r10 4, .str .r0 .r10 8, .str .r0 .r10 12,
      .mov .r7 (.reg .r5), .mov .r6 (imm 0)]) s
      (fun s' => AbsIn c st w sp (BitVec.ofNat 32 n) k8 0 H [] Np n s' ∧
        blockAt s'.mem (State.addr st + BitVec.ofNat 64 0) = 0 ∧
        bytesAt s'.mem (State.addr Np) n = bytesAt s.mem (State.addr Np) n ∧
        Frame [⟨State.addr st, 16⟩] s.mem s'.mem) := by
  have he := h.env
  have hd := h.data
  have h10 := he.r10
  obtain z₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  obtain z₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  obtain z₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  obtain z₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at z₀
  obtain ⟨s₁, run₁, hm₁, h6, h7, hg₁, hrd₁, hwr₁, hsp₁⟩ : ∃ s₁, runBlock isa [.mov .r0 (imm 0), .str .r0 .r10 0,
      .str .r0 .r10 4, .str .r0 .r10 8, .str .r0 .r10 12, .mov .r7 (.reg .r5), .mov .r6 (imm 0)] s = some s₁ ∧
      s₁.mem = store4 s.mem (State.addr st) 0 0 0 0 ∧ s₁.gpr .r6 = BitVec.ofNat 32 0 ∧
      s₁.gpr .r7 = BitVec.ofNat 32 n ∧ (∀ r, r ≠ .r0 → r ≠ .r6 → r ≠ .r7 → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    refine ⟨_, by arun [h10, add_ofNat_zero, L.stA, z₀, z₁, z₂, z₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq]; rfl
    · simp [gpr_setReg]
    · simp [gpr_setReg, h.r5]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain he₁ := he.set7 h7 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hsp₁ hrd₁ hwr₁
  obtain f₁ : Frame [⟨State.addr st, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact Cmac.frame_store4 _ _ _ _ _
  obtain dD : ∀ r ∈ [(⟨State.addr st, 16⟩ : Region)], (⟨State.addr Np, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hd.st.sub_right (Region.sub_prefix (by decide))
  refine ⟨⟨he₁, by rw [hg₁ _ (by decide) (by decide) (by decide), h.r4],
    by rw [hg₁ _ (by decide) (by decide) (by decide), h.r5], h6, hd.of_eq hrd₁ hwr₁, ?_⟩, ?_,
    bytesAt_frame f₁ dD (by have := hd.lt; omega_using [this]), f₁⟩
  · rw [blockAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.ctx_st (a := 240) (n := 16) (d := 0) (k := 16) (by decide) (by decide)), h.hH]
  · rw [add_ofNat_zero, blockAt, hm₁, Cmac.bytesAt_store4, Cmac.le4_zero]; decide

/-- `J₀` of a nonce of any length but 12: GHASH of the nonce padded and of
the lengths block. -/
theorem j0hash_ok [VG.Proof.Gcm.Arm.GhashLaw] {H : Block} {Np : BitVec 32} {n : Nat} {s : State} (h : J0In c st w sp k7 k8 H Np n s)
    (hn : n ≠ 12) :
    WP isa j0hash s (J0Mid c st w sp k8 H (bytesAt s.mem (State.addr Np) n) s.mem) := by
  have hd := h.data
  have hlt := hd.lt32
  refine WP.seq (WP.mono (j0zero_ok L h) fun s₁ ⟨hai, hY₁, hiv, f₁⟩ => ?_)
  refine WP.seq (WP.mono (absorb_ok L (yo := 0) (.inl rfl) hai) fun s₂ ho => ?_)
  rw [List.nil_append, hiv] at ho
  obtain hab₂ := ho.abs (Proof.Gcm.absorbed_nil H hY₁)
  have he₂ := ho.env
  obtain hH₂ : blockAt s₂.mem (State.addr c + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho.frame (ctx_absFrame L (.inl rfl)), hai.hH]
  obtain ⟨s₃, run₃, h6₃, hg₃, hk₃⟩ : ∃ s₃, runBlock isa [.dp .and .r6 .r7 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 (n % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    obtain hand := and15 (BitVec.ofNat 32 n)
    rw [toNat32 hlt] at hand
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, he₂.r7, hand]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hk₃.sp hk₃.rd hk₃.wr
  refine WP.seq (WP.mono (flush_ok L (yo := 0) (.inl rfl) (x := bytesAt s.mem (State.addr Np) n) ⟨he₃, by
    rw [hk₃.mem, hH₂]⟩ (by rw [h6₃, length_bytesAt])) fun s₄ hf => ?_)
  have he₄ := hf.env
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, hg₅, hk₅⟩ : ∃ s₅, runBlock isa [.mov .r4 (imm 0), .mov .r5 (imm 0),
      .mov .r6 (.reg .r7), .mov .r7 (imm 0)] s₄ = some s₅ ∧
      s₅.gpr .r4 = 0 ∧ s₅.gpr .r5 = 0 ∧ s₅.gpr .r6 = BitVec.ofNat 32 n ∧ s₅.gpr .r7 = 0 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₄.r7]
    · simp [gpr_setReg]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  obtain he₅ := he₄.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide) (by decide))
    hk₅.sp hk₅.rd hk₅.wr
  refine WP.mono (lens_ok L (yo := 0) (.inl rfl) (H := H) he₅ (by rw [hk₅.mem]; exact hf.hH))
    fun s₆ ⟨he₆, hH₆, hY₆, f₆⟩ => ?_
  refine ⟨⟨_, he₆⟩, hH₆, ?_, ?_⟩
  · have hw := (hf.abs (by rw [hk₃.mem]; exact hab₂)).whole_eq (by
      simp only [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod n)
    rw [length_bytesAt] at hw
    rw [h4₅, h5₅, h6₅, h7₅, show ((0 : BitVec 32) ++ (0 : BitVec 32)).toNat = 0 from rfl,
      show ((0 : BitVec 32) ++ BitVec.ofNat 32 n).toNat = n by
        rw [Proof.Gcm.toNat_append, toNat32 hlt]; simp, hk₅.mem, hw] at hY₆
    rw [Proof.Gcm.j0_eq H (by rw [length_bytesAt]; exact hn), length_bytesAt, ← hY₆, add_ofNat_zero]
  · have g₁ : Frame (j0Frame st w sp) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    obtain g₄ := t_j0Frame hf.frame
    obtain g₆ := t_j0Frame f₆
    rw [hk₃.mem] at g₄
    rw [hk₅.mem] at g₆
    exact ((g₁.trans (abs_j0Frame ho.frame)).trans g₄).trans g₆

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem j0_ok [VG.Proof.Gcm.Arm.GhashLaw] {H : Block} {Np : BitVec 32} {n : Nat} {s : State} (h : J0In c st w sp k7 k8 H Np n s) :
    WP isa j0 s (J0Out c st w sp k8 H (bytesAt s.mem (State.addr Np) n) s.mem) := by
  have hlt := h.data.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmpk_ok s .r5 h.r5 hlt (k := 12) (by decide) (by decide)
  obtain h₁ : J0In c st w sp k7 k8 H Np n s₁ :=
    ⟨h.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, by rw [hm₁]; exact h.hH, by rw [hg₁]; exact h.r4,
      by rw [hg₁]; exact h.r5, h.data.of_eq hrd₁ hwr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  rw [← hm₁]
  refine WP.seq (WP.ite (decide (n = 12)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_))
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact WP.mono (j012_ok L h₁) fun _ hm => initState_ok L hm
  · exact WP.mono (j0hash_ok L h₁ (by simpa using hf)) fun _ hm => initState_ok L hm

end

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: what every function does

Untrusted: everything here is checked by Lean. Each function saves our
caller's `r4`–`r11` and `lr` at `W + 128` (`save_ok`) and restores them
(`restore_ok`, `exit_ok`); the pieces it runs in between never write there.

The postconditions quantify over what the state represents (the nonce, the
additional data, the text so far), which the code never looks at: each
function runs the same for all of them, so one run satisfies each instance
of its proof (`WP.forall_det`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.MdStream.Arm (saveMem saveList_ok readW_writeW_save)

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-- Code never changes the permissions or the stack pointer. -/
theorem WP.with_rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨t, s', e, q⟩ := h
  obtain ⟨-, hw, -⟩ := Exec.rdwr e
  exact ⟨t, s', e, q, (Exec.rdwr e).1, hw, Exec.sp e⟩

/-- Where `save` puts our caller's registers. -/
def SavedAt (m : Mem) (w : BitVec 32) (s₀ : State) : Prop :=
  ∀ p ∈ saved, m.readW (State.addr w + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

/-- The saved registers' slots. -/
abbrev savedR (w : BitVec 32) : Region := ⟨State.addr w + BitVec.ofNat 64 128, 36⟩

theorem saved_bound : ∀ p ∈ saved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 164 := by decide

theorem saveMem_frame_off (m : Mem) (B : Addr) (g : Reg → BitVec 32) {lo L : Nat} (hL : lo + L < 2 ^ 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, lo ≤ p.2 ∧ p.2 + 4 ≤ lo + L) →
      Frame [⟨B + BitVec.ofNat 64 lo, L⟩] m (saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ h.1 (by omega_using [h]) (by omega_using [hL]))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

set_option simprocs false in
theorem saveMem_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (saveMem m B g saved).readW (B + BitVec.ofNat 64 d) 32 = g r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

/-- Saving the registers at `b + 128`, where `b` holds `W`. -/
theorem save_ok {s : State} {b : Reg} {w : BitVec 32} (hb : s.gpr b = w) (hfit : w.toNat + 2560 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr w, 2560⟩] s.wr) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → SavedAt s'.mem w s →
      Frame [savedR w] s.mem s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  refine saveList_ok (b := b) saved s Q (fun p hp => ?_) fun s' g rd wr sp m => k s' g rd wr sp ?_ ?_
  · have hbd := saved_bound p hp
    rw [hb]
    exact ⟨by omega_using [hbd], by omega_using [hfit, hbd], in_off hw (by omega_using [hbd]) (by decide)⟩
  · intro p hp
    rw [m, hb]; exact saveMem_slot _ _ _ hp
  · rw [m, hb]; exact saveMem_frame_off _ _ _ (by decide) saved fun p hp => saved_bound p hp

/-- The saved registers stay where they are, outside a frame. -/
theorem SavedAt.frame {m m' : Mem} {w : BitVec 32} {s₀ : State} (h : SavedAt m w s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savedR w).Disjoint r) : SavedAt m' w s₀ := by
  intro p hp
  have hb := saved_bound p hp
  have hs : Region.Sub ⟨State.addr w + BitVec.ofNat 64 p.2, 4⟩ (savedR w) := Offset.sub _ hb.1 (by omega_using [hb])
  rw [hf.readW (r := ⟨State.addr w + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left hs) (by decide), h p hp]

/-- The end of every function: our caller's registers restored. -/
theorem restore_ok {s s₀ : State} {w : BitVec 32} (h11 : s.gpr .r11 = w) (hfit : w.toNat + 2560 ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr w, 2560⟩] (s.rd ++ s.wr)) (hs : SavedAt s.mem w s₀) (hsp : s.sp = s₀.sp) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hA : ∀ d, d < 2560 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega_using [hfit, hd])
  have r₁ := in_off hr (show 128 + 4 ≤ 2560 by decide) (by decide)
  have r₂ := in_off hr (show 132 + 4 ≤ 2560 by decide) (by decide)
  have r₃ := in_off hr (show 136 + 4 ≤ 2560 by decide) (by decide)
  have r₄ := in_off hr (show 140 + 4 ≤ 2560 by decide) (by decide)
  have r₅ := in_off hr (show 144 + 4 ≤ 2560 by decide) (by decide)
  have r₆ := in_off hr (show 148 + 4 ≤ 2560 by decide) (by decide)
  have r₇ := in_off hr (show 152 + 4 ≤ 2560 by decide) (by decide)
  have r₈ := in_off hr (show 156 + 4 ≤ 2560 by decide) (by decide)
  have r₉ := in_off hr (show 160 + 4 ≤ 2560 by decide) (by decide)
  have e : ∀ p ∈ saved, s.mem.readW (State.addr w + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1 := hs
  have e₁ := e (.r4, 128) (by simp [saved]); have e₂ := e (.r5, 132) (by simp [saved])
  have e₃ := e (.r6, 136) (by simp [saved]); have e₄ := e (.r7, 140) (by simp [saved])
  have e₅ := e (.r8, 144) (by simp [saved]); have e₆ := e (.r9, 148) (by simp [saved])
  have e₇ := e (.r10, 152) (by simp [saved]); have e₈ := e (.r11, 156) (by simp [saved])
  have e₉ := e (.lr, 160) (by simp [saved])
  simp only at e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
  refine WP.of_runBlock ⟨_, by simp only [restore, restored, List.map]; arun [h11, hA, r₁, r₂, r₃, r₄, r₅, r₆, r₇,
    r₈, r₉], ⟨fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_setReg, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉]
  all_goals first | rfl | simp [gpr_setReg, sp_setReg, mem_setReg, rd_setReg, wr_setReg, hsp]

/-- The layout, from disjointness of the context, the state, `W` and the stack. -/
theorem Lay.of {c st w sp : BitVec 32} (cw : c.toNat + 256 ≤ 2 ^ 32) (sw : st.toNat + 80 ≤ 2 ^ 32)
    (ww : w.toNat + 2560 ≤ 2 ^ 32) (sp8 : 8 ≤ sp.toNat) (cs : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr st, 80⟩)
    (cW : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr w, 2560⟩)
    (sW : (⟨State.addr st, 80⟩ : Region).Disjoint ⟨State.addr w, 2560⟩)
    (kc : (below sp).Disjoint ⟨State.addr c, 256⟩) (ks : (below sp).Disjoint ⟨State.addr st, 80⟩)
    (kw : (below sp).Disjoint ⟨State.addr w, 2560⟩) : Lay c st w sp :=
  ⟨cw, sw, ww, sp8, cs, cW, sW.sub_right (Region.sub_prefix (by decide)), sW.sub_right (Lay.wSub (by decide)),
    kc, ks, kw⟩

theorem ctxH_eq (m : Mem) (p : Addr) : Spec.Gcm.ctxH m p = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 240) := rfl

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem saved_absFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ absFrame st w sp yo, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega_using [hyo]) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ tagFrame st w sp o, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by omega_using [ho])) (by decide) (by omega_using [ho])
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_j0Frame : ∀ r ∈ j0Frame st w sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_crFrame {c k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (hd : DataW c st w sp k7 k8 s D n) :
    ∀ r ∈ crFrame st w sp D n, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

end

end VG.Proof.AesGcm.Arm
