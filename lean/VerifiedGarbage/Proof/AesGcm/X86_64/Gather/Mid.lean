import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Base

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: between the calls

Untrusted: everything here is checked by Lean. The memory the code reads
and does not write (the key context, the nonce, the additional data, the
descriptors and the slices) is what it was on entry outside the regions the
code writes and the stack (`iv_eq`, `ad_eq`, `desc_eq`, `slice_eq`); the
slices one at a time (`gl_succ`, `pt_succ`); and, with `i` slices done, the
streaming state represents the message with the additional data `A` and the
encryption of the first `i` slices, which the output holds (`Mid`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block StreamRepr ctxCiph ctxH gctr inc32 j0 gathered gatheredLen)

section
variable (s : State)

/-- The rounds. -/
abbrev R : Nat := (s.gpr .rsi).toNat
/-- The cipher and the hash subkey of the key context. -/
abbrev ciph : Block → Block := ctxCiph s.mem (K s) (R s)
abbrev hk : Block := ctxH s.mem (K s)
/-- The IV and the additional data. -/
abbrev iv : List Byte := bytesAt s.mem (Nn s) (NL s)
abbrev ad : List Byte := bytesAt s.mem (Ad s) (AL s).toNat
/-- The first counter block. -/
abbrev icb : Block := inc32 (j0 (hk s) (iv s))
/-- The encryption of the first `i` slices. -/
abbrev ct (i : Nat) : List Byte := gctr (ciph s) (icb s) (pt s i)

/-- Slice `i`: its address and its length, in the memory on entry. -/
abbrev sb (i : Nat) : Addr := s.mem.readW (Src s + BitVec.ofNat 64 (16 * i)) 64
abbrev sl (i : Nat) : Nat := (s.mem.readW (Src s + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8) 64).toNat

end

/-! ## The slices -/

theorem desc_off (i : Nat) : i * (2 * (64 / 8)) = 16 * i := by omega

theorem gl_succ (s : State) (i : Nat) : gl s (i + 1) = gl s i + sl s i := by
  simp only [gl, sl]
  rw [Proof.Gcm.gatheredLen_succ, desc_off]

theorem pt_succ (s : State) (i : Nat) : pt s (i + 1) = pt s i ++ bytesAt s.mem (sb s i) (sl s i) := by
  simp only [pt, sb, sl]
  rw [Proof.Gcm.gathered_succ, desc_off, BitVec.setWidth_eq]

theorem length_pt (s : State) (i : Nat) : (pt s i).length = gl s i := Proof.Gcm.length_gathered _ _ _ _

theorem length_ct (s : State) (i : Nat) : (ct s i).length = gl s i := by
  rw [ct, Proof.Gcm.length_gctr, length_pt]

theorem gl_mono (s : State) {i j : Nat} (h : i ≤ j) : gl s i ≤ gl s j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · rw [gl_succ]; exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

/-- Slice `i` is listed. -/
theorem slice_mem (s : State) {i : Nat} (hi : i < Cnt s) : (⟨sb s i, sl s i⟩ : Region) ∈ lsR s := by
  simp only [lsR, Sig.listed, List.mem_map, List.mem_range]
  refine ⟨i, hi, ?_⟩
  simp only [desc_off, BitVec.setWidth_eq, Elem.size, Nat.mul_one]

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

theorem gl_le {i : Nat} (hi : i ≤ Cnt s) : gl s i ≤ L s := hp.glen ▸ gl_mono s hi

theorem gl_succ_le {i : Nat} (hi : i < Cnt s) : gl s i + sl s i ≤ L s := gl_succ s i ▸ gl_le hp hi

/-! ## What the code reads and does not write -/

/-- A region apart from the regions written and the stack. -/
abbrev Apart (r : Region) (s : State) : Prop := ∀ t ∈ wR s ++ [tR s], r.Disjoint t

omit hp in
theorem apart_of {r : Region} (hd : r.Disjoint (dR s)) (ht : r.Disjoint (tgR s)) (hw : r.Disjoint (wkR s))
    (hb : (tR s).Disjoint r) : Apart r s := by
  intro t ht'
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht'
  rcases ht' with (rfl | rfl | rfl) | rfl
  exacts [hd, ht, hw, hb.symm]

theorem k_apart : Apart (kR M s) s := apart_of hp.k_d hp.k_t hp.k_w hp.b_k
theorem n_apart : Apart (nR s) s := apart_of hp.n_d hp.n_t hp.n_w hp.b_n
theorem a_apart : Apart (aR s) s := apart_of hp.a_d hp.a_t hp.a_w hp.b_a
theorem ds_apart : Apart (dsR s) s := apart_of hp.ds_d hp.ds_t hp.ds_w hp.b_ds
theorem ls_apart {r : Region} (hr : r ∈ lsR s) : Apart r s :=
  apart_of (hp.ls r hr).1 (hp.ls r hr).2.1 (hp.ls r hr).2.2 (hp.b_ls r hr)

/-- The cipher, through a frame of the regions written and the stack. -/
theorem ciph_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) : ctxCiph m (K s) (R s) = ciph s := by
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  simp only [ciph, ctxCiph]
  rw [bytesAt_frame hf (fun r hr => (k_apart hp r hr).sub_left (Region.sub_prefix (Nat.le_trans hRb M.ge)))
    (by have := hp.w_k; have := M.ge; omega)]

/-- The hash subkey, through a frame of the regions written and the stack. -/
theorem hk_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) : ctxH m (K s) = hk s := by
  simp only [hk, ctxH]
  exact blockAt_frame hf fun r hr => (k_apart hp r hr).sub_left (Offset.sub_base _ (by have := M.ge; omega))

theorem iv_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) : bytesAt m (Nn s) (NL s) = iv s :=
  bytesAt_frame hf (n_apart hp) (by have := hp.w_n; omega)

theorem ad_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) : bytesAt m (Ad s) (AL s).toNat = ad s :=
  bytesAt_frame hf (a_apart hp) (by have := hp.w_ad; omega)

/-- The descriptors, through a frame of the regions written and the stack. -/
theorem desc_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) {j : Nat} (hj : j + 8 ≤ Cnt s * 16) :
    m.readW (Src s + BitVec.ofNat 64 j) 64 = s.mem.readW (Src s + BitVec.ofNat 64 j) 64 :=
  hf.readW (Offset.contains_base _ hj (by have := hp.w_ds; omega)) (ds_apart hp) (by decide)

/-- Slice `i`'s address and length, through a frame. -/
theorem sb_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) {i : Nat} (hi : i < Cnt s) :
    m.readW (Src s + BitVec.ofNat 64 (16 * i)) 64 = sb s i := desc_eq hp hf (by omega)

theorem sl_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) {i : Nat} (hi : i < Cnt s) :
    m.readW (Src s + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (sl s i) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, desc_eq hp hf (by omega), sl, ofNat_toNat, BitVec.add_assoc,
    ← BitVec.ofNat_add]

/-- Slice `i`'s bytes, through a frame. -/
theorem slice_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) {i : Nat} (hi : i < Cnt s) :
    bytesAt m (sb s i) (sl s i) = bytesAt s.mem (sb s i) (sl s i) :=
  bytesAt_frame hf (ls_apart hp (slice_mem s hi)) (by have := hp.w_ls _ (slice_mem s hi); simp at this; omega)

end

/-! ## Between the calls -/

/-- What holds between the calls, with the length `ap` of the additional data
so far and `i` slices done: `rsp`, the callee-saved registers and the
regions are those of the entry, the slots are kept, and the memory changed
only where the code writes. -/
structure Base (s : State) (ap : BitVec 64) (i : Nat) (st : State) : Prop where
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s ap i st.mem
  frame : Frame (wR s ++ [tR s]) s.mem st.mem

/-- `Base`, and the streaming state represents the message with the
additional data `A` and the encryption of the first `i` slices, which the
output holds. -/
structure Mid (s : State) (ap : BitVec 64) (i : Nat) (A : List Byte) (st : State) : Prop extends
    Base s ap i st where
  i_le : i ≤ Cnt s
  sr : StreamRepr st.mem (St s) (ciph s) (hk s) (iv s) A (ct s i)
  out : bytesAt st.mem (Dst s) (gl s i) = ct s i

/-- `Base` through code that changes no memory, `rsp` or callee-saved register. -/
theorem Base.regs {s : State} {ap : BitVec 64} {i : Nat} {st st' : State} (h : Base s ap i st)
    (hm : st'.mem = st.mem) (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd)
    (hwr : st'.wr = st.wr) : Base s ap i st' :=
  ⟨by rw [hcs _ (by decide), h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr], hrd.trans h.rd, hwr.trans h.wr,
    hm ▸ h.kept, hm ▸ h.frame⟩

theorem Mid.regs {s : State} {ap : BitVec 64} {i : Nat} {A : List Byte} {st st' : State} (h : Mid s ap i A st)
    (hm : st'.mem = st.mem) (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd)
    (hwr : st'.wr = st.wr) : Mid s ap i A st' :=
  ⟨h.toBase.regs hm hcs hrd hwr, h.i_le, hm ▸ h.sr, hm ▸ h.out⟩

/-- A frame of the slots kept is one of the regions written. -/
theorem frame_kpR {s : State} {m m' : Mem} (hf : Frame [kpR s] m m') : Frame (wR s ++ [tR s]) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wkR s, by simp, kpR_sub⟩

/-- `work` on the stack, readable and the entry's, between the calls. -/
theorem Base.w {M : CtxMode} {s : State} (hp : SG M s) {ap : BitVec 64} {i : Nat} {st : State}
    (h : Base s ap i st) :
    InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 48) 8 ∧
      st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 48) 64 = W s :=
  ⟨by rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 5) (by decide), by rw [h.rsp]; exact keep_w hp h.frame⟩

/-- A slot of `work`, readable between the calls. -/
theorem Base.slot {M : CtxMode} {s : State} (hp : SG M s) {ap : BitVec 64} {i : Nat} {st : State}
    (h : Base s ap i st) {d : Nat} (hd : d + 8 ≤ 184) : InRegions (st.rd ++ st.wr) (W s + BitVec.ofNat 64 d) 8 := by
  rw [h.rd, h.wr]; exact w_in' hp hd

/-- The 16 zero bytes of `work`. -/
theorem Kept.zeros {s : State} {ap : BitVec 64} {i : Nat} {m : Mem} (h : Kept s ap i m) {k : Nat} (hk : k ≤ 16) :
    bytesAt m (W s + BitVec.ofNat 64 88) k = Spec.Gcm.zeros k := by
  have byte : ∀ j < 16, m (W s + BitVec.ofNat 64 88 + BitVec.ofNat 64 j) = 0 := by
    intro j hj
    by_cases h8 : j < 8
    · rw [← Mem.extractLsb'_read m _ (n := 8) h8]
      have := h.z₀; simp only [Mem.readW] at this
      rw [show m.read (W s + BitVec.ofNat 64 88) 8 = 0 by simpa using this]; simp
    · have e : W s + BitVec.ofNat 64 88 + BitVec.ofNat 64 j = W s + BitVec.ofNat 64 96 + BitVec.ofNat 64 (j - 8) := by
        rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]; congr 2; omega
      rw [e, ← Mem.extractLsb'_read m _ (n := 8) (by omega)]
      have := h.z₁; simp only [Mem.readW] at this
      rw [show m.read (W s + BitVec.ofNat 64 96) 8 = 0 by simpa using this]; simp
  simp only [bytesAt, Spec.Gcm.zeros]
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  simp only [List.length_map, List.length_range] at h₁
  exact byte j (by omega)

end VG.Proof.AesGcm.X86_64.Gather
