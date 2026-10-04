import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Entry

/-!
# AES-GCM-SIV on x86-64: the arguments

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`TagBuf`, `args_of_seal`, `args_of_open`). Between `entry` and `restore`, the
pieces only write the parts of `W` below 144, from 192 to 200 and from 248
on, the stack below `SP` and the data (`mutR`), so they keep the slots, the
saved registers, the key schedule, the nonce, the additional data and the
tag's address on the stack (`argT_kept`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64
open VG.Impl.AesGcmSiv.X86_64 (saved)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (covers_left covers_of_mem bytesAt_frame)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (12 bytes at `N`), the additional data (`al` bytes at
`A`), the data (`n` bytes at `D`), the working space at `W` and the stack
pointer `SP`. -/
structure Args (s : State) (K W SP N A D : Addr) (R al n : Nat) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 14
  nonce : Buf K W SP s N 12
  aad : Buf K W SP s A al
  data : Buf K W SP s D n
  dw : Covers [⟨D, n⟩] s.wr
  dk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩
  nd : (⟨N, 12⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 3816⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 24⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 3816⟩
  argsD : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩

/-- The tag, the 16 bytes at `T`: apart from the data, `W` and the stack
below `SP`. -/
structure TagBuf (W SP D : Addr) (n : Nat) (T : Addr) : Prop where
  d : (⟨T, 16⟩ : Region).Disjoint ⟨D, n⟩
  w : (⟨T, 16⟩ : Region).Disjoint ⟨W, 3816⟩
  stk : (below SP 8).Disjoint ⟨T, 16⟩
  wrap : T.toNat + 16 ≤ 2 ^ 64

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 := rfl

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨s.gpr .rdi, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .rdx, 12⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [args s 3] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .r9, (arg s 0).toNat⟩] s.wr) (hW : Covers [⟨arg s 2, 3816⟩] s.wr) :
    Args s (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9) (s.gpr .rsi).toNat
        (s.gpr .r8).toNat (arg s 0).toNat ∧
      TagBuf (arg s 2) (s.gpr .rsp) (s.gpr .r9) (arg s 0).toNat (arg s 1) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, b20, b21, b22, b23,
    b24, b25, b26, _, hR⟩ := h
  exact ⟨{
    lay := ⟨b20, b25, d2, d14, d19, b26⟩
    perm := ⟨hk, hW⟩
    rounds := hR
    nonce := ⟨hN, by decide, b21, d4, d15⟩
    aad := ⟨hA, BitVec.isLt _, b22, d6, d16⟩
    data := ⟨covers_left hD, BitVec.isLt _, b23, d9, d17⟩
    dw := hD
    dk := d1
    nd := d3
    ad := d5
    retW := d13
    retD := d12
    args := ha
    argsW := d11.symm
    argsD := d10.symm }, ⟨d7, d8, d18, b24⟩⟩

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    (Args s (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9) (s.gpr .rsi).toNat
        (s.gpr .r8).toNat (arg s 0).toNat ∧
      TagBuf (arg s 2) (s.gpr .rsp) (s.gpr .r9) (arg s 0).toNat (arg s 1)) ∧
      Covers [⟨arg s 1, 16⟩] s.wr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨arg s 1, 16⟩ := by
  obtain ⟨hrd, hwr, hl, hrt⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, 12⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
      args s 3], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r9, (arg s 0).toNat⟩ : Region), ⟨arg s 1, 16⟩, ⟨arg s 2, 3816⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)), mwr _ (by simp), hrt⟩

/-- `open`'s arguments, and its received tag, to read. -/
theorem args_of_open {s : State} (h : openPre s) :
    (Args s (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9) (s.gpr .rsi).toNat
        (s.gpr .r8).toNat (arg s 0).toNat ∧
      TagBuf (arg s 2) (s.gpr .rsp) (s.gpr .r9) (arg s 0).toNat (arg s 1)) ∧
      Covers [⟨arg s 1, 16⟩] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, 12⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
      ⟨arg s 1, 16⟩, args s 3], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r9, (arg s 0).toNat⟩ : Region), ⟨arg s 2, 3816⟩], Covers [r] s.wr := fun r hr =>
    covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)), mrd _ (by simp)⟩

/-- The tag as a buffer to read. -/
theorem TagBuf.buf {K W SP D T : Addr} {n : Nat} {s : State} (h : TagBuf W SP D n T)
    (hr : Covers [⟨T, 16⟩] (s.rd ++ s.wr)) : Buf K W SP s T 16 :=
  ⟨hr, by decide, h.wrap, h.w, h.stk⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- The cipher of a key schedule outside a frame's regions. -/
theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

section
variable {K W SP N A D : Addr} {R al n : Nat} {m m' : Mem}

/-- The tag's address, at `SP + 16`, misses what the entry and the pieces
write. -/
theorem argT_disj (hW : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hD : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨SP + BitVec.ofNat 64 16, 8⟩ ⟨SP + BitVec.ofNat 64 8, 24⟩ := by
    rw [show SP + BitVec.ofNat 64 16 = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]]
    exact Offset.sub_base _ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hW.sub_left hs).sub_right (Region.sub_prefix (by decide))
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact Offset.disjoint_below SP (by decide)
  · exact hD.sub_left hs

/-- The tag's address, at `SP + 16`, through the entry and the pieces. -/
theorem argT_kept (hf : Frame (entryR W :: mutR W SP D n) m m')
    (hW : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hD : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩) :
    m'.readW (SP + BitVec.ofNat 64 16) 64 = m.readW (SP + BitVec.ofNat 64 16) 64 :=
  hf.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (argT_disj hW hD) (by decide)

/-- The tag, through the entry and the pieces. -/
theorem tag_kept {T : Addr} (hT : TagBuf W SP D n T) (hf : Frame (entryR W :: mutR W SP D n) m m') :
    bytesAt m' T 16 = bytesAt m T 16 :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.w.sub_right (Region.sub_prefix (by decide))
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.stk.symm
    · exact hT.d) (by decide)

theorem slots_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hf : Frame (mutR W SP D n) m m') (S : Slots W R N A D al n m) : Slots W R N A D al n m' := by
  have k : ∀ d, (144 ≤ d ∧ d + 8 ≤ 192 ∨ 200 ≤ d ∧ d + 8 ≤ 248) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD hd) (by decide)
  exact ⟨by rw [k 200 (by decide)]; exact S.rounds, by rw [k 208 (by decide)]; exact S.nonce,
    by rw [k 216 (by decide)]; exact S.aad, by rw [k 224 (by decide)]; exact S.alen,
    by rw [k 232 (by decide)]; exact S.data, by rw [k 240 (by decide)]; exact S.len⟩

theorem saved_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hf : Frame (mutR W SP D n) m m') {g : Reg → BitVec 64} (S : Saved m W g) : Saved m' W g := by
  intro p hp
  rw [← S p hp]
  have hd : 144 ≤ p.2 ∧ p.2 + 8 ≤ 192 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD (.inl hd))
    (by decide)

theorem ciph_mut (L : Lay K W SP) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) (hR : R = 10 ∨ R = 14)
    (hf : Frame (mutR W SP D n) m m') : Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R :=
  ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.k_w.sub_right (Region.sub_prefix (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_k.symm
    · exact hdk) (by rcases hR with h | h <;> subst h <;> decide)

theorem buf_mut {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (hPD : (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    bytesAt m' P len = bytesAt m P len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (by have := hP.lt; omega)

end

end VG.Proof.AesGcmSiv.X86_64
