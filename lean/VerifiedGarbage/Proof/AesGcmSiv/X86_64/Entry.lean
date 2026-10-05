import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Env

/-!
# AES-GCM-SIV on x86-64: the entry, the exit and the arguments

Untrusted: everything here is checked by Lean. `entry` reads the stack
arguments, saves our caller's registers at `W + 144` and keeps the arguments
but `tag` in `W` (`entry_ok`); `restore` reads the registers back (`restore_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (in_off)
open VG.Spec.Aes (bytesAt)

/-- Our caller's registers, saved at `W + 144`. -/
def Saved (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The save area and the slots, which `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 144, 104⟩

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- `entry`. -/
theorem entry_ok {K W SP : Addr} {s : State} (P : Perm K W s) {R : Nat} {N A D : Addr} {al n : Nat}
    (hsp : s.gpr .rsp = SP) (hargs : Covers [⟨SP + BitVec.ofNat 64 8, 24⟩] (s.rd ++ s.wr))
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    ∃ s₁, runBlock isa entry s = some s₁ ∧ Env K W SP s₁ ∧ Slots W R N A D al n s₁.mem ∧
      Saved s₁.mem W s.gpr ∧ Frame [entryR W] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₈ := in_off (d := 0) (n := 8) hargs (by decide) (by decide)
  have a₂₄ := in_off (d := 16) (n := 8) hargs (by decide) (by decide)
  rw [add_ofNat_assoc, show 8 + 0 = 8 from rfl] at a₈
  rw [add_ofNat_assoc] at a₂₄
  simp only [Nat.reduceAdd] at a₂₄
  have w₁ := P.wW (show 144 + 8 ≤ 3816 by decide)
  have w₂ := P.wW (show 152 + 8 ≤ 3816 by decide)
  have w₃ := P.wW (show 160 + 8 ≤ 3816 by decide)
  have w₄ := P.wW (show 168 + 8 ≤ 3816 by decide)
  have w₅ := P.wW (show 176 + 8 ≤ 3816 by decide)
  have w₆ := P.wW (show 184 + 8 ≤ 3816 by decide)
  have w₇ := P.wW (show 200 + 8 ≤ 3816 by decide)
  have w₈ := P.wW (show 208 + 8 ≤ 3816 by decide)
  have w₉ := P.wW (show 216 + 8 ≤ 3816 by decide)
  have w₁₀ := P.wW (show 224 + 8 ≤ 3816 by decide)
  have w₁₁ := P.wW (show 232 + 8 ≤ 3816 by decide)
  have w₁₂ := P.wW (show 240 + 8 ≤ 3816 by decide)
  have cE : ∀ d, 144 ≤ d → d + 8 ≤ 248 → (entryR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
  refine ⟨_, by srun [entry, save, saved, List.map_cons, List.map_nil, hW, hsp, hn, a₈, a₂₄, w₁, w₂, w₃, w₄,
      w₅, w₆, w₇, w₈, w₉, w₁₀, w₁₁, w₁₂], ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hdi]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hsp]
  · exact P.of_eq rfl rfl
  iterate 6
    · simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64, gpr_setReg,
        ite_true, ite_false, reduceCtorEq, hsi, hdx, hcx, hr8, hr9, hn]
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64]
  · simp only [mem_setReg]
    repeat (first | exact Frame.refl _ _ |
      refine Frame.writeW ?_ (List.mem_singleton_self _) _ (cE _ (by decide) (by decide)))
  all_goals rfl

/-- `restore`: our caller's registers back. -/
theorem restore_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {g : Reg → BitVec 64} (hs : Saved s.mem W g) :
    ∃ s', runBlock isa restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.mem = s.mem ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rax = s.gpr .rax := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 144 + 8 ≤ 3816 by decide)
  have r₂ := E.perm.wR (show 152 + 8 ≤ 3816 by decide)
  have r₃ := E.perm.wR (show 160 + 8 ≤ 3816 by decide)
  have r₄ := E.perm.wR (show 168 + 8 ≤ 3816 by decide)
  have r₅ := E.perm.wR (show 176 + 8 ≤ 3816 by decide)
  have r₆ := E.perm.wR (show 184 + 8 ≤ 3816 by decide)
  have v₁ := hs (.rbx, 144) (by decide)
  have v₂ := hs (.rbp, 152) (by decide)
  have v₃ := hs (.r12, 160) (by decide)
  have v₄ := hs (.r13, 168) (by decide)
  have v₅ := hs (.r14, 176) (by decide)
  have v₆ := hs (.r15, 184) (by decide)
  refine ⟨_, by srun [restore, saved, List.map_cons, List.map_nil, h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, v₁, v₂, v₃, v₄, v₅, v₆]
  · rfl
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesGcmSiv.X86_64

/-!
## The arguments

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

/-!
## The arguments of the functions called

Untrusted: everything here is checked by Lean. The calls are those of
AES-GCM (`Proof.AesGcm.X86_64.ctr_call`, `gh_call`, `key_call`); `cargs`,
`gargs` and `kargs` build their arguments from the environment: the key
schedule of the key-generating key (`keyK`) or of the encryption key at
`W + 248` (`keyS`), blocks of `W` as counter blocks, states and data, the
data itself, and the working spaces at `W + 1512` and `W + 1768`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (CtrCall GhCall KeyCall covers_left covers_cons covers_nil covers_append)

theorem toNat_W {W : Addr} (hw : W.toNat + 3816 ≤ 2 ^ 64) {d : Nat} (hd : d < 3816) :
    (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Data for a call: `k` bytes at `Q`, which the code may read, apart from
the working spaces at `W + 1512` and the stack below `SP`. -/
structure Src (W SP : Addr) (s : State) (Q : Addr) (k : Nat) : Prop where
  rd : Covers [⟨Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 64
  qs : (⟨Q, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 1512, 2304⟩
  stk : (below SP 8).Disjoint ⟨Q, k⟩

/-- Bytes of `W` below 1512 as data. -/
theorem srcW {K W SP : Addr} {s : State} (L : Lay K W SP) (P : Perm K W s) {t k : Nat} (hk : t + k ≤ 1512) :
    Src W SP s (W + BitVec.ofNat 64 t) k where
  rd := P.wCR (by omega)
  wrap := by rw [toNat_W L.ww (by omega)]; have := L.ww; omega
  qs := L.w_w (.inl (by omega)) (by omega) (by decide)
  stk := L.stk_w' (by omega)

/-- A buffer as data. -/
theorem srcBuf {K W SP : Addr} {s : State} {Q : Addr} {k : Nat} (h : Buf K W SP s Q k) : Src W SP s Q k :=
  ⟨h.rd, h.wrap, h.w.sub_right (Lay.wSub (by decide)), h.stk⟩

/-- A key schedule for `vg_aes_ctr32`, apart from the blocks of `W` below
248 and the working space at `W + 1768`. -/
structure Key (W SP : Addr) (s : State) (Kc : Addr) : Prop where
  rd : Covers [⟨Kc, 240⟩] (s.rd ++ s.wr)
  stk : (below SP 8).Disjoint ⟨Kc, 240⟩
  lo : (⟨Kc, 240⟩ : Region).Disjoint ⟨W, 248⟩
  hi : (⟨Kc, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 1768, 2048⟩

/-- The key-generating key's schedule. -/
theorem keyK {K W SP : Addr} {s : State} (L : Lay K W SP) (P : Perm K W s) : Key W SP s K :=
  ⟨P.k, L.stk_k, L.k_w.sub_right (Region.sub_prefix (by decide)), L.k_w' (by decide)⟩

/-- The encryption key's schedule, at `W + 248`. -/
theorem keyS {K W SP : Addr} {s : State} (L : Lay K W SP) (P : Perm K W s) : Key W SP s (W + BitVec.ofNat 64 248) :=
  ⟨P.wCR (by decide), L.stk_w' (by decide),
    by simpa using L.w_w (a := 248) (n := 240) (d := 0) (k := 248) (.inr (by decide)) (by decide) (by decide),
    L.w_w (.inl (by decide)) (by decide) (by decide)⟩

/-- The arguments of `vg_aes_ctr32`: the key schedule at `Kc`, the counter
block at `W + c`, `n` blocks at `Q`, which it may write, and the working
space at `W + 1768`. -/
theorem cargs {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 14) {Kc : Addr} (hk : Key W SP s Kc) {c : Nat} (hc : c + 16 ≤ 248) {Q : Addr} {n : Nat}
    (hq : Src W SP s Q (16 * n)) (hqc : (⟨Q, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 c, 16⟩)
    (hqk : (⟨Kc, 240⟩ : Region).Disjoint ⟨Q, 16 * n⟩) (hqw : Covers [⟨Q, 16 * n⟩] s.wr)
    (rdi : s.gpr .rdi = Kc) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 c)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 1768) :
    CtrCall s Kc (W + BitVec.ofNat 64 c) Q (W + BitVec.ofNat 64 1768) R n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := by omega
  wrap := hq.wrap
  kc := hk.lo.sub_right (Offset.sub_base W hc)
  kd := hqk
  ks := hk.hi
  cd := hqc.symm
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  ds := hq.qs.sub_right (Offset.sub W (by decide) (by decide))
  stkK := by rw [E.rsp]; exact hk.stk
  stkC := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkD := by rw [E.rsp]; exact hq.stk
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := covers_append (covers_cons hk.rd covers_nil)
    (covers_cons (E.perm.wCR (by omega)) (covers_cons hq.rd (covers_cons (E.perm.wCR (by decide)) covers_nil)))
  writes := covers_cons (E.perm.wC (by omega)) (covers_cons hqw (covers_cons (E.perm.wC (by decide)) covers_nil))

/-- The arguments of `vg_ghash`: GHASH's key at `W + 64`, its accumulator at
`W + 80`, `n` blocks at `W + d` and the working space at `W + 1512`. -/
theorem gargs {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {d n : Nat} (hd : 96 ≤ d)
    (hdn : d + 16 * n ≤ 1512) (rdi : s.gpr .rdi = W + BitVec.ofNat 64 64) (rsi : s.gpr .rsi = W + BitVec.ofNat 64 80)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 d) (rcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (r8 : s.gpr .r8 = W + BitVec.ofNat 64 1512) :
    GhCall s (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 d) (W + BitVec.ofNat 64 1512) n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  n_lt := by omega
  hy := L.w_w (.inl (by decide)) (by decide) (by decide)
  hs := L.w_w (.inl (by decide)) (by decide) (by decide)
  yd := L.w_w (.inl (by omega)) (by decide) (by omega)
  ys := L.w_w (.inl (by decide)) (by decide) (by decide)
  ds := L.w_w (.inl (by omega)) (by omega) (by decide)
  stkH := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkY := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkD := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := covers_append (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by omega)) covers_nil))
    (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by decide)) covers_nil))
  writes := covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- The arguments of `vg_aes_expand_key`: the `l`-byte encryption key at
`W + 32`, its schedule at `W + 248` and the working space at `W + 1768`. -/
theorem kargs {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {l : Nat} (hl : l = 16 ∨ l = 32)
    (rdi : s.gpr .rdi = W + BitVec.ofNat 64 32) (rsi : s.gpr .rsi = BitVec.ofNat 64 l)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 248) (rcx : s.gpr .rcx = W + BitVec.ofNat 64 1768) :
    KeyCall s (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 1768) l where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  len := by omega
  kc := L.w_w (.inl (by omega)) (by omega) (by decide)
  ks := L.w_w (.inl (by omega)) (by omega) (by decide)
  cs := L.w_w (.inl (by decide)) (by decide) (by decide)
  stkK := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkC := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := covers_append (covers_cons (E.perm.wCR (by omega)) covers_nil)
    (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by decide)) covers_nil))
  writes := covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

end VG.Proof.AesGcmSiv.X86_64
