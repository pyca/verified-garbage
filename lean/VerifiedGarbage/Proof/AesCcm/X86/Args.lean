import VerifiedGarbage.Proof.AesCcm.X86.Entry
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES-CCM on x86: the arguments

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`).
Between the entry and the exit, the pieces only write the parts of `W` in
`mutR`, the stack below `SP` and the data, so they keep the slots, the saved
registers, the key schedule, the nonce and the associated data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 slotv argsR argsR_eq below_eq SavedAt savedR ofNat_toNat32)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the working
space at `W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W SP s N nl
  aad : Buf W SP s A al
  data : Buf W SP s D n
  tag : Buf W SP s T tl
  dw : Covers [⟨w64 D, n⟩] s.wr
  dk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩
  nd : (⟨w64 N, nl⟩ : Region).Disjoint ⟨w64 D, n⟩
  ad : (⟨w64 A, al⟩ : Region).Disjoint ⟨w64 D, n⟩
  td : (⟨w64 T, tl⟩ : Region).Disjoint ⟨w64 D, n⟩
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  al32 : al < 2 ^ 32
  n32 : n < 2 ^ 32
  retW : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  retD : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 D, n⟩
  retT : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 T, tl⟩
  args : Covers [argsR SP 11] (s.rd ++ s.wr)
  argsW : (argsR SP 11).Disjoint ⟨w64 W, 2560⟩
  fa : SP.toNat + 4 + 4 * 11 ≤ 2 ^ 32

/-- `Args`, from what both preconditions say, with the key schedule, the
nonce, the associated data and the tag readable and the data, the working
space and the arguments writable. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (mrd : ∀ r ∈ [schR s, nonceR s, aadR s, tagR s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [dataR s, workR s, argsR' s], Covers [r] s.wr) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  simp only [oneLay, stackR] at h
  obtain ⟨d1, d2, _, d4, d5, _, d7, d8, _, d10, d11, _, d13, _, d15, _, _, _, d19, d20, d21, _,
    b1, b2, b3, b4, b5, b6, _, f1, f2, f3, f4, f5, f6, hsp, hfa, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  rw [show (56 : Addr) = BitVec.ofNat 64 56 from rfl, below_eq hsp] at b1 b2 b3 b4 b5 b6
  exact {
    lay := ⟨f1, f6, hsp, d2, b1, b6⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), f2, d5, b2⟩
    aad := ⟨mrd _ (by simp), f3, d8, b3⟩
    data := ⟨Proof.AesGcm.X86.covers_left (mwr _ (by simp)), f4, d11, b4⟩
    tag := ⟨mrd _ (by simp), f5, d13, b5⟩
    dw := mwr _ (by simp)
    dk := d1
    nd := d4
    ad := d7
    td := d10.symm
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    al32 := BitVec.isLt _
    n32 := BitVec.isLt _
    retW := d21
    retD := d19
    retT := d20
    args := by rw [argsR_eq]; exact Proof.AesGcm.X86.covers_left (mwr _ (by simp))
    argsW := by rw [argsR_eq]; exact d15.symm
    fa := by omega_arith }

theorem args_of_seal {s : State} (h : sealPre s) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine args_of_lay hl (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_right _ (by rw [hwr]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)

/-- In `seal`, the tag is writable. -/
theorem tag_wr {s : State} (h : sealPre s) : Covers [tagR s] s.wr :=
  covers_of_mem (by rw [h.2.1]; simp)

theorem args_of_open {s : State} (h : openPre s) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  obtain ⟨hrd, hwr, hl⟩ := h
  exact args_of_lay hl (fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr)))
    (fun r hr => covers_of_mem (by rw [hwr]; exact hr))

/-! ## What the pieces keep -/

section
variable {K W SP D : BitVec 32} {n : Nat} {m m' : Mem}

theorem saved_mut (L : Lay K W SP) (hD : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩)
    (hf : Frame (mutR W SP D n) m m') {s₀ : State} (S : SavedAt m W s₀) : SavedAt m' W s₀ :=
  S.frame hf fun r hr => (kept_mut L hD (d := 128) (k := 16) (.inl ⟨by decide, by decide⟩) r hr)

theorem ciph_mut (L : Lay K W SP) (hdk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hf : Frame (mutR W SP D n) m m') :
    Spec.Ccm.ctxCiph m' (w64 K) R = Spec.Ccm.ctxCiph m (w64 K) R :=
  ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact L.k_w.sub_right (Region.sub_prefix (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_k.symm
    · exact hdk) (by rcases hR with h | h | h <;> subst h <;> decide)

theorem buf_mut {s : State} {P : BitVec 32} {len : Nat} (hP : Buf W SP s P len)
    (hPD : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (by have := hP.lt; omega_arith)

end

/-- Every region of `rs` is part of one of `mutR`. -/
abbrev InMut (W SP D : BitVec 32) (n : Nat) (rs : List Region) : Prop :=
  ∀ r ∈ rs, ∃ r' ∈ mutR W SP D n, Region.Sub r r'

theorem inMut_macR (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) : InMut W SP D n (macR W SP y) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 56, by simp, fun _ h => h⟩

theorem inMut_ctrR (W SP D : BitVec 32) (n : Nat) : InMut W SP D n (ctrR W SP D n) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 56, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem frame_toMut {W SP D : BitVec 32} {n : Nat} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (h : InMut W SP D n rs) : Frame (mutR W SP D n) m m' := hf.sub h

end VG.Proof.AesCcm.X86
