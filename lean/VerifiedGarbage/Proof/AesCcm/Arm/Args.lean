import VerifiedGarbage.Proof.AesCcm.Arm.Crypt

/-!
# AES-CCM on ARMv7: the arguments, and what the pieces write

Untrusted: everything here is checked by Lean. What the contracts'
preconditions give about the arguments (`Args`, `TagB`, `args_of_seal`,
`args_of_open`), and the regions
the pieces after the entry write (`mutR`: `W` but for our caller's saved
registers, the stack below `sp` and the data), which miss the saved
registers, the key schedule, the stack arguments, the nonce and the
associated data.
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (covers_left covers_of_mem savedR bytesAt_frame ArgsKeep)

/-- What the arguments of `seal` and `open` are. -/
structure Args (s : State) (k w N A D : BitVec 32) (R nl al n tl : Nat) : Prop where
  lay : Lay k w s.sp
  perm : Perm k w s
  stk : Stk w s s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf w s.sp s N nl
  aad : Buf w s.sp s A al
  data : Dat k w s.sp s D n
  nd : (⟨State.addr N, nl⟩ : Region).Disjoint ⟨State.addr D, n⟩
  ad : (⟨State.addr A, al⟩ : Region).Disjoint ⟨State.addr D, n⟩
  da : (⟨State.addr D, n⟩ : Region).Disjoint (args s 7)
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  n32 : n < 2 ^ 32
  al32 : al < 2 ^ 32

/-- The tag, the `tl` bytes at `T`: apart from the data, `W` and the stack
below `sp`. -/
structure TagB (w sp D : BitVec 32) (n : Nat) (T : BitVec 32) (tl : Nat) : Prop where
  d : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr D, n⟩
  w : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk : (blw sp).Disjoint ⟨State.addr T, tl⟩
  wrap : T.toNat + tl ≤ 2 ^ 32

/-- `Args` and `TagB` from the layout, with the buffers covered as each
function's permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨State.addr (s.gpr .r0), 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨State.addr (arg s 0), (arg s 1).toNat⟩] (s.rd ++ s.wr)) (ha : args s 7 ∈ s.rd)
    (hD : Covers [⟨State.addr (arg s 2), (arg s 3).toNat⟩] s.wr) (hW : Covers [⟨State.addr (arg s 6), 2560⟩] s.wr) :
    Args s (s.gpr .r0) (arg s 6) (s.gpr .r2) (arg s 0) (arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
        (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat ∧
      TagB (arg s 6) s.sp (arg s 2) (arg s 3).toNat (arg s 4) (arg s 5).toNat := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5, f1, f2, f3, f4, f5, sp16, sp28, hR,
    hv, t1, t2, t3, t4⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact ⟨{
    lay := ⟨f1, f5, sp16, d2, b1, b5⟩
    perm := ⟨hk, hW⟩
    stk := ⟨ArgsKeep.refl 7 s, sp28, ha, d9.symm⟩
    rounds := hR
    nonce := ⟨hN, f2, d4, b2⟩
    aad := ⟨hA, f3, d6, b3⟩
    data := ⟨⟨covers_left hD, f4, d7, b4⟩, hD, d1⟩
    nd := d3
    ad := d5
    da := d8
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    n32 := BitVec.isLt _
    al32 := BitVec.isLt _ }, ⟨t1, t2, t3, t4⟩⟩

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    (Args s (s.gpr .r0) (arg s 6) (s.gpr .r2) (arg s 0) (arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
        (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat ∧
      TagB (arg s 6) s.sp (arg s 2) (arg s 3).toNat (arg s 4) (arg s 5).toNat) ∧
      Covers [⟨State.addr (arg s 4), (arg s 5).toNat⟩] s.wr ∧
      (⟨State.addr (arg s 4), (arg s 5).toNat⟩ : Region).Disjoint (args s 7) := by
  obtain ⟨hrd, hwr, hl, ht⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩,
      ⟨State.addr (arg s 0), (arg s 1).toNat⟩, args s 7], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 2), (arg s 3).toNat⟩ : Region), ⟨State.addr (arg s 4), (arg s 5).toNat⟩,
      ⟨State.addr (arg s 6), 2560⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (by rw [hrd]; simp)
    (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp), ht⟩

/-- `open`'s arguments, and its received tag, to read. -/
theorem args_of_open {s : State} (h : openPre s) :
    (Args s (s.gpr .r0) (arg s 6) (s.gpr .r2) (arg s 0) (arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
        (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat ∧
      TagB (arg s 6) s.sp (arg s 2) (arg s 3).toNat (arg s 4) (arg s 5).toNat) ∧
      Covers [⟨State.addr (arg s 4), (arg s 5).toNat⟩] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩,
      ⟨State.addr (arg s 0), (arg s 1).toNat⟩, ⟨State.addr (arg s 4), (arg s 5).toNat⟩, args s 7],
      Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 2), (arg s 3).toNat⟩ : Region), ⟨State.addr (arg s 6), 2560⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (by rw [hrd]; simp)
    (mwr _ (by simp)) (mwr _ (by simp)), mrd _ (by simp)⟩

/-- What the pieces after the entry write: `W` but for the saved registers,
the stack below `sp` and the data. -/
abbrev mutR (w sp D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr w, 128⟩, ⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, blw sp, ⟨State.addr D, n⟩]

theorem w_mut {w sp D : BitVec 32} {n a l : Nat} (h : a + l ≤ 128 ∨ (164 ≤ a ∧ a + l ≤ 2560)) :
    ∃ r' ∈ mutR w sp D n, Region.Sub ⟨State.addr w + BitVec.ofNat 64 a, l⟩ r' := by
  rcases h with h | h
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ h⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, by simp, Offset.sub _ h.1 (by omega_arith)⟩

theorem blw_mut {w sp D : BitVec 32} {n : Nat} : ∃ r' ∈ mutR w sp D n, Region.Sub (blw sp) r' :=
  ⟨_, by simp, fun _ h => h⟩

theorem macR_mut {w sp D : BitVec 32} {n y : Nat} (hy : y = 0 ∨ y = 112) :
    ∀ r ∈ macR w sp y, ∃ r' ∈ mutR w sp D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact w_mut (.inl (by omega_arith))
  · exact w_mut (.inl (by decide))
  · exact w_mut (.inr ⟨by decide, by decide⟩)
  · exact blw_mut

theorem ctrR_mut {w sp D : BitVec 32} {n : Nat} : ∀ r ∈ ctrR w sp D n, ∃ r' ∈ mutR w sp D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact w_mut (.inl (by decide))
  · exact w_mut (.inr ⟨by decide, by decide⟩)
  · exact blw_mut
  · exact ⟨_, by simp, fun _ h => h⟩

section
variable {s : State} {k w N A D : BitVec 32} {R nl al n tl : Nat} (Ar : Args s k w N A D R nl al n tl)
include Ar

theorem saved_mut : ∀ r ∈ mutR w s.sp D n, (savedR w).Disjoint r := by
  have L := Ar.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 36) (d := 0) (m := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm
  · exact (Ar.data.buf.w.sub_right (Lay.wSub (by decide))).symm

theorem k_mut : ∀ r ∈ mutR w s.sp D n, (⟨State.addr k, 240⟩ : Region).Disjoint r := by
  have L := Ar.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w' (by decide)
  · exact L.stk_k.symm
  · exact Ar.data.k

theorem args_mut : ∀ r ∈ mutR w s.sp D n, (args s 7).Disjoint r := by
  have L := Ar.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Ar.stk.aw.sub_right (Region.sub_prefix (by decide))
  · exact Ar.stk.aw.sub_right (Lay.wSub (by decide))
  · exact Ar.stk.blw_args rfl
  · exact Ar.da.symm

/-- The nonce and the associated data miss what the pieces write. -/
theorem nonce_mut : ∀ r ∈ mutR w s.sp D n, (⟨State.addr N, nl⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Ar.nonce.w.sub_right (Region.sub_prefix (by decide))
  · exact Ar.nonce.w.sub_right (Lay.wSub (by decide))
  · exact Ar.nonce.stk.symm
  · exact Ar.nd

theorem aad_mut : ∀ r ∈ mutR w s.sp D n, (⟨State.addr A, al⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Ar.aad.w.sub_right (Region.sub_prefix (by decide))
  · exact Ar.aad.w.sub_right (Lay.wSub (by decide))
  · exact Ar.aad.stk.symm
  · exact Ar.ad

end

/-- The tag misses what the pieces write. -/
theorem tag_mut {w sp D T : BitVec 32} {n tl : Nat} (hT : TagB w sp D n T tl) :
    ∀ r ∈ mutR w sp D n, (⟨State.addr T, tl⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hT.w.sub_right (Region.sub_prefix (by decide))
  · exact hT.w.sub_right (Lay.wSub (by decide))
  · exact hT.stk.symm
  · exact hT.d

end VG.Proof.AesCcm.Arm
