import VerifiedGarbage.Proof.AesCcm.X86_64.Entry

/-!
# AES-CCM on x86-64: the arguments

Untrusted: everything here is checked by Lean. The precondition `onePre`
gives the facts the proofs use about the arguments (`Args`, `args_of`).
Between `entry` and `restore`, the pieces only write the parts of `W` below
112, from 216 to 232 and from 240 on, the stack below `SP` and the data
(`mutR`), so they keep the slots, the saved registers, the key schedule, the
nonce and the associated data (`Kept`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64
open VG.Impl.AesCcm.X86_64 (saved)
open VG.Spec.Aes (bytesAt)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), a tag of `tl` bytes, the working space at
`W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D : Addr) (R nl al n tl : Nat) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf K W SP s N nl
  aad : Buf K W SP s A al
  data : Buf K W SP s D n
  dw : Covers [⟨D, n⟩] s.wr
  dk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 32⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 32⟩ : Region).Disjoint ⟨W, 2560⟩

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 := rfl

theorem args_of {s : State} (h : onePre s) :
    Args s (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat := by
  obtain ⟨hrd, hwr, d3, d4, d5, d6, d7, d8, d9, _, d11, d12, d13, d14, d15, d16, d17, d18, b19, b20, b21, b22, b23,
    b24, _, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      args s 4], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨arg s 0, (arg s 1).toNat⟩ : Region), ⟨arg s 2, 2560⟩], Covers [r] s.wr := fun r hr =>
    covers_of_mem (by rw [hwr]; exact hr)
  exact {
    lay := ⟨b19, b23, d4, d14, d18, b24⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), BitVec.isLt _, b20, d6, d15⟩
    aad := ⟨mrd _ (by simp), BitVec.isLt _, b21, d8, d16⟩
    data := ⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b22, d9, d17⟩
    dw := mwr _ (by simp)
    dk := d3
    nd := d5
    ad := d7
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    retW := d13
    retD := d12
    args := mrd (args s 4) (by simp)
    argsW := d11.symm }

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- What the pieces before the data is written may change. -/
abbrev wR (W SP : Addr) : List Region := [wA W, wK W, wC W, below SP 16]

theorem wR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ wR W SP, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  refine ⟨r, ?_, fun _ h => h⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl <;> simp

section
variable {K W SP N A D : Addr} {R nl al n tl : Nat} {m m' : Mem}

theorem slots_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (mutR W SP D n) m m') (S : Slots W R N A D nl al n tl m) : Slots W R N A D nl al n tl m' := by
  have k : ∀ d, (112 ≤ d ∧ d + 8 ≤ 216 ∨ 232 ≤ d ∧ d + 8 ≤ 240) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD hd) (by decide)
  exact ⟨by rw [k 232 (by decide)]; exact S.rounds, by rw [k 160 (by decide)]; exact S.nonce,
    by rw [k 168 (by decide)]; exact S.nlen, by rw [k 176 (by decide)]; exact S.aad,
    by rw [k 184 (by decide)]; exact S.alen, by rw [k 192 (by decide)]; exact S.data,
    by rw [k 200 (by decide)]; exact S.len, by rw [k 208 (by decide)]; exact S.tl⟩

theorem saved_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (mutR W SP D n) m m') {g : Reg → BitVec 64} (S : Saved m W g) : Saved m' W g := by
  intro p hp
  rw [← S p hp]
  have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 216 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD (.inl hd))
    (by decide)

theorem ciph_mut (L : Lay K W SP) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hf : Frame (mutR W SP D n) m m') : Spec.Ccm.ctxCiph m' K R = Spec.Ccm.ctxCiph m K R :=
  ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.k_w.sub_right (Region.sub_prefix (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_k.symm
    · exact hdk) (by rcases hR with h | h | h <;> subst h <;> decide)

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

theorem buf_wR {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len) (hf : Frame (wR W SP) m m') :
    bytesAt m' P len = bytesAt m P len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

end

end VG.Proof.AesCcm.X86_64
