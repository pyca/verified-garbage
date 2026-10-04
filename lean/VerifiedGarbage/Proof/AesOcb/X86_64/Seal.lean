import VerifiedGarbage.Proof.AesOcb.X86_64.Body
import VerifiedGarbage.Proof.AesOcb.X86_64.Entry
import VerifiedGarbage.Proof.AesOcb.X86_64.Hash
import VerifiedGarbage.Proof.AesOcb.X86_64.Contract

/-!
# AES-OCB on x86-64: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. The precondition `onePre`
gives the facts the proofs use about the arguments (`Args`, `args_of`).
`seal` is `entry`, `Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`),
the tag at `W` (`tag`) and `restore` (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame covers_left covers_of_mem)

/-- What `seal` and `open` are given: the key context at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), a tag of `tl` bytes, the working space at
`W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D : Addr) (R nl al n tl : Nat) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W SP s N nl
  aad : Buf W SP s A al
  data : DBuf K W SP s D n
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  n1 : 1 ≤ nl
  n15 : nl ≤ 15
  t1 : 1 ≤ tl
  t16 : tl ≤ 16
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 32⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 32⟩ : Region).Disjoint ⟨W, 2560⟩

theorem args_of {s : State} (h : onePre s) :
    Args s (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat := by
  obtain ⟨hrd, hwr, d3, d4, d5, d6, d7, d8, d9, _, d11, d12, d13, d14, d15, d16, d17, d18, b19, b20, b21, b22, b23,
    b24, _, hR, hv⟩ := h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 256⟩ : Region), ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
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
    data := ⟨⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b22, d9, d17⟩, mwr _ (by simp), d3⟩
    nd := d5
    ad := d7
    n1 := hn1
    n15 := hn15
    t1 := ht1
    t16 := ht16
    retW := d13
    retD := d12
    args := mrd (args s 4) (by simp)
    argsW := d11.symm }

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

section
variable {K W SP D : Addr} {n : Nat} {m m' : Mem}

theorem saved_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (mutR W SP D n) m m') {g : Reg → BitVec 64} (S : Saved m W g) : Saved m' W g := by
  intro p hp
  rw [← S p hp]
  have hd : 160 ≤ p.2 ∧ p.2 + 8 ≤ 248 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD (.inl hd))
    (by decide)

theorem buf_mut {s : State} {P : Addr} {len : Nat} (hP : Buf W SP s P len)
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

theorem lstar_mut (L : Lay K W SP) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    ctxLstar m' K = ctxLstar m K :=
  blockAtMem_frame hf fun r hr => (k_mut L hD r hr).sub_left (Lay.kSub (by decide))

end

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {W SP D : Addr} {n d : Nat} (hd : d + 16 ≤ 160) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, wC W, below SP 8] m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., sub_wA hd⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The return address is outside what the functions write. -/
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega)
  · exact hD

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega,
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-- What the pieces before the data leave: the offset, the checksum, `L_$`,
`L_0` and `HASH`. -/
structure Pre (K W SP N A D : Addr) (R nl al n tl : Nat) (s s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (entryR W :: mutR W SP D n) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : Slots W R N A D nl n tl s'.mem
  saved : Saved s'.mem W s.gpr
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  ck : blockAtMem s'.mem (W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K)
  l0 : blockAtMem s'.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al)
  ciph : ctxCiph s'.mem K R = ctxCiph s.mem K R
  lstar : ctxLstar s'.mem K = ctxLstar s.mem K
  data : bytesAt s'.mem D n = bytesAt s.mem D n
  tagIn : bytesAt s'.mem W 16 = bytesAt s.mem W 16

/-- The first block of `W` misses what the pieces before the data write. -/
theorem w16_disj {d k : Nat} (W : Addr) (h : 16 ≤ d) (hk : d + k ≤ 2560) :
    (⟨W, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.base_disjoint W h (by omega)

/-- `entry`, `nonce` and `hash`. -/
theorem pre_wp (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al)
    {k : Prog isa} {Q : State → Prop} (hk : ∀ s', Pre K W SP N A D R nl al n tl s s' → WP isa k s' Q) :
    WP isa (.seq (.block entry) (.seq (nonce (callees v)) (.seq (hash (callees v)) k))) s Q := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, P₁⟩ := entry_ok L Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have eK : ctxCiph s₁.mem K R = ctxCiph s.mem K R := by
    unfold ctxCiph
    rw [bytesAt_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega)]
  have eL : ctxLstar s₁.mem K = ctxLstar s.mem K := blockAtMem_frame P₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide)))
  have eB : ∀ {P : Addr} {k : Nat}, Buf W SP s P k → bytesAt s₁.mem P k = bytesAt s.mem P k := fun hP =>
    bytesAt_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  -- `Offset_0`.
  refine WP.seq (WP.mono (nonce_ok v L P₁.env Ar.rounds P₁.slots.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega) (Ar.nonce.of_eq P₁.rd P₁.wr) Ar.data.k Ar.data.w) fun s₂ P₂ => ?_)
  have F₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := nonceR_mut P₂.frame
  have S₂ := Slots.of_mut L Ar.data.w F₂ P₁.slots
  have c₂ : ctxCiph s₂.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₂ Ar.rounds).trans eK
  have l₂ : ctxLstar s₂.mem K = ctxLstar s.mem K := (lstar_mut L Ar.data.k F₂).trans eL
  have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := (buf_mut Ar.aad Ar.ad F₂).trans (eB Ar.aad)
  -- `HASH`.
  have C : HCtx K W SP D n R (ctxCiph s.mem K R) (ctxLstar s.mem K) A (bytesAt s.mem A al) s₂ :=
    { lay := L, rounds := Ar.rounds, ciph := c₂, lstar := l₂
      buf := by rw [length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans P₁.rd) (P₂.wr.trans P₁.wr)
      aad := by rw [length_bytesAt, a₂]
      ad := by rw [length_bytesAt]; exact Ar.ad
      kd := Ar.data.k, dw := Ar.data.w, rnd := S₂.rounds
      short := by rw [length_bytesAt]; exact Ar.aad.lt }
  refine WP.seq (WP.mono (hash_ok v C P₂.env S₂.aad (by rw [P₂.alen, P₁.alen, length_bytesAt])
    (by rw [P₂.keep (by decide) (by decide), P₁.l0])) fun s₃ ⟨E₃, F₃, sum₃, rd₃, wr₃⟩ => ?_)
  have F₃' : Frame (mutR W SP D n) s₂.mem s₃.mem := hashR_mut F₃
  have k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (256 ≤ d ∧ d + 16 ≤ 384)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) := fun {d} hd =>
    blockAtMem_frame F₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
  refine hk s₃ ⟨E₃, ?_, by rw [rd₃, P₂.rd, P₁.rd], by rw [wr₃, P₂.wr, P₁.wr], Slots.of_mut L Ar.data.w F₃' S₂,
    saved_mut L Ar.data.w (F₂.trans F₃') P₁.saved, ?_, ?_, ?_, ?_, ?_, by rw [sum₃],
    (ctxCiph_mut L Ar.data.k F₃' Ar.rounds).trans c₂, (lstar_mut L Ar.data.k F₃').trans l₂, ?_, ?_⟩
  · exact (P₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩).trans
      ((F₂.trans F₃').sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  · rw [k₃ (d := ofsO) (by decide), P₂.ofs, eK, eB Ar.nonce]
  · rw [k₃ (d := o0O) (by decide), P₂.o0, eK, eB Ar.nonce]
  · rw [k₃ (d := ckO) (by decide), P₂.keep (by decide) (by decide), P₁.ck]
  · rw [k₃ (d := ldO) (by decide), P₂.keep (by decide) (by decide), P₁.ld]
  · rw [k₃ (d := l0O) (by decide), P₂.keep (by decide) (by decide), P₁.l0]
  · have hd := Ar.data
    rw [bytesAt_frame F₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.stk.symm) (by have := hd.lt; omega),
      bytesAt_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.stk.symm) (by have := hd.lt; omega), eB hd.toBuf]
  · have st16 : (below SP 8).Disjoint ⟨W, 16⟩ := L.stk_w.sub_right (Region.sub_prefix (by decide))
    rw [bytesAt_frame F₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact w16_disj W (by decide) (by decide)
        · exact w16_disj W (by decide) (by decide)
        · exact w16_disj W (by decide) (by decide)
        · exact w16_disj W (by decide) (by decide)
        · exact st16.symm) (by decide),
      bytesAt_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact w16_disj W (by decide) (by decide)
        · exact w16_disj W (by decide) (by decide)
        · exact w16_disj W (by decide) (by decide)
        · exact st16.symm) (by decide),
      bytesAt_frame P₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact w16_disj W (by decide) (by decide)) (by decide)]

/-- `body`'s frame misses a block of `W` outside the offset, the checksum and
`[96, 144)`. -/
theorem body_keep {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame (bodyR W SP D n) m m') {d : Nat} (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (144 ≤ d ∧ d + 16 ≤ 384)) :
    blockAtMem m' (W + BitVec.ofNat 64 d) = blockAtMem m (W + BitVec.ofNat 64 d) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact (L.stk_w' (by omega)).symm
    · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («seal» (callees v)) s fun s' => gprPreserved s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem W tl) := by
  have L := Ar.lay
  unfold «seal»
  refine pre_wp v Ar hsp hD hn hW htl hdi hsi hdx hcx hr8 hr9 fun s₃ P₃ => ?_
  have hD₃ : DBuf K W SP s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  refine WP.seq (WP.mono (bodySeal_ok v L P₃.env Ar.rounds P₃.slots.rounds hD₃ P₃.slots.data P₃.slots.len P₃.ofs
    P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar])) fun s₄ B => ?_)
  have F₄ : Frame (mutR W SP D n) s₃.mem s₄.mem := bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans P₃.ciph
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L B.env Ar.rounds ((kept_read L Ar.data.w F₄ (d := 232) (by decide)).trans
    P₃.slots.rounds) (.inl rfl)) fun s₅ T => ?_)
  have F₅ : Frame (mutR W SP D n) s₄.mem s₅.mem := tagR_mut (by decide) T.frame
  -- `restore`.
  obtain ⟨s₆, run₆, hg₆, hm₆, hsp₆, _⟩ := restore_ok T.env (saved_mut L Ar.data.w (F₄.trans F₅) P₃.saved)
  refine WP.of_runBlock ⟨s₆, run₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₆ (.rbx, savO) (by decide)
    · exact hg₆ (.rbp, savO + 8) (by decide)
    · rw [hsp₆, T.env.rsp, hsp]
    · exact hg₆ (.r12, savO + 16) (by decide)
    · exact hg₆ (.r13, savO + 24) (by decide)
    · exact hg₆ (.r14, savO + 32) (by decide)
    · exact hg₆ (.r15, savO + 40) (by decide)
  · have fall : Frame (entryR W :: mutR W SP D n) s.mem s₅.mem :=
      P₃.frame.trans ((F₄.trans F₅).sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₆, hsp]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The ciphertext and the tag.
    have hout := B.out
    rw [P₃.ciph, P₃.lstar, P₃.data] at hout
    have hofs := B.ofs
    rw [P₃.lstar] at hofs
    have hck := B.ck
    rw [P₃.data] at hck
    have d₆ : bytesAt s₆.mem D n = bytesAt s₄.mem D n := by
      rw [hm₆]
      exact bytesAt_frame T.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Ar.data.w.sub_right (Lay.wSub (by decide))
        · exact Ar.data.w.sub_right (Lay.wSub (by decide))
        · exact Ar.data.w.sub_right (Lay.wSub (by decide))
        · exact Ar.data.stk.symm) (by have := Ar.data.lt; omega)
    have tv := T.val
    rw [show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
    have t₆ : bytesAt s₆.mem W tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem W)).take tl := by
      rw [hm₆, bytesAt_take_block _ _ Ar.t16]
    rw [Proof.Ocb.encryptWith_eq, d₆, hout, t₆, tv, hck, hofs, ld₄, sum₄, cK₄]
    simp only [length_bytesAt, List.length_drop]
    by_cases hr : 0 < n % 16
    · have h' : n - 16 * (n / 16) > 0 := by omega
      simp only [h', hr, ↓reduceIte]
    · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
      simp only [h', hr, ↓reduceIte]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp (v : BlocksImpl) {s : State} (h : onePre s) :
    WP isa («seal» (callees v)) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' :=
  seal_wp' v (args_of h) rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.X86_64
