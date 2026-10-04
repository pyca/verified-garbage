import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Entry

/-!
# AES-GCM-SIV on x86-64: the arguments

Untrusted: everything here is checked by Lean. The precondition `onePre`
gives the facts the proofs use about the arguments (`Args`, `args_of`).
Between `entry` and `restore`, the pieces only write the parts of `W` below
160, from 208 to 216 and from 512 on, the stack below `SP` and the data
(`mutR`), so they keep the slots, the saved registers, the key schedule, the
nonce and the additional data.
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
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 4096⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 16⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 4096⟩

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 := rfl

theorem args_of {s : State} (h : onePre s) :
    Args s (s.gpr .rdi) (arg s 1) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9) (s.gpr .rsi).toNat
      (s.gpr .r8).toNat (arg s 0).toNat := by
  obtain ⟨hrd, hwr, d3, d4, d5, d6, d7, d8, d9, _, d11, d12, d13, d14, d15, d16, d17, d18, b19, b20, b21, b22, b23,
    b24, _, hR⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, 12⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
      args s 2], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r9, (arg s 0).toNat⟩ : Region), ⟨arg s 1, 4096⟩], Covers [r] s.wr := fun r hr =>
    covers_of_mem (by rw [hwr]; exact hr)
  exact {
    lay := ⟨b19, b23, d4, d14, d18, b24⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), by decide, b20, d6, d15⟩
    aad := ⟨mrd _ (by simp), BitVec.isLt _, b21, d8, d16⟩
    data := ⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b22, d9, d17⟩
    dw := mwr _ (by simp)
    dk := d3
    nd := d5
    ad := d7
    retW := d13
    retD := d12
    args := mrd (args s 2) (by simp)
    argsW := d11.symm }

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- The cipher of a key schedule outside a frame's regions. -/
theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

section
variable {K W SP N A D : Addr} {R al n : Nat} {m m' : Mem}

theorem slots_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩)
    (hf : Frame (mutR W SP D n) m m') (S : Slots W R N A D al n m) : Slots W R N A D al n m' := by
  have k : ∀ d, (160 ≤ d ∧ d + 8 ≤ 208 ∨ 216 ≤ d ∧ d + 8 ≤ 512) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD hd) (by decide)
  exact ⟨by rw [k 272 (by decide)]; exact S.rounds, by rw [k 280 (by decide)]; exact S.nonce,
    by rw [k 288 (by decide)]; exact S.aad, by rw [k 296 (by decide)]; exact S.alen,
    by rw [k 304 (by decide)]; exact S.data, by rw [k 312 (by decide)]; exact S.len⟩

theorem saved_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩)
    (hf : Frame (mutR W SP D n) m m') {g : Reg → BitVec 64} (S : Saved m W g) : Saved m' W g := by
  intro p hp
  rw [← S p hp]
  have hd : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := by
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
