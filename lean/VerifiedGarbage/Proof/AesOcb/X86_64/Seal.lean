import VerifiedGarbage.Proof.AesOcb.X86_64.Body
import VerifiedGarbage.Proof.AesOcb.X86_64.Entry
import VerifiedGarbage.Proof.AesOcb.X86_64.Hash
import VerifiedGarbage.Proof.AesOcb.X86_64.Contract

/-!
# AES-OCB on x86-64: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. The preconditions `sealPreX`
and `openPreX` give the facts the proofs use about the arguments (`Args`,
`sealArgs_of`, `openArgs_of`). `seal` is `front`: `entry`, the table of
`L_j` (`table`), `Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`)
and the tag at `W` (`tag`)
(`sealFront_wp`); then the copy of the tag to `tag` (`tagOut`) and
`restore` (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame covers_left covers_of_mem)

/-- What `seal` and `open` are given: the key context at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the working
space at `W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W SP s N nl
  aad : Buf W SP s A al
  data : DBuf K W SP s D n
  tag : Buf W SP s T tl
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  td : (⟨T, tl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  n1 : 1 ≤ nl
  n15 : nl ≤ 15
  t1 : 1 ≤ tl
  t16 : tl ≤ 16
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 3584⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  retT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, tl⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 3584⟩

/-- `Args` from the facts both preconditions give, for a state that may
read the key context, the nonce, the associated data, the tag and the
arguments on the stack, and write the data and `W`. -/
theorem args_of {s : State} (h : oneFacts s)
    (mrd : ∀ r ∈ [aCtx s, aNonce s, aAad s, args s 5, aTag s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [aData s, aWork s], Covers [r] s.wr) :
    Args s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) := by
  obtain ⟨d3, d4, d5, d6, d7, d8, t1, t2, d9, _, d11, d12, d13, t3, d14, d15, d16, d17, d18, t4, b19, b20, b21, b22,
    bt, b23, b24, _, hR, hv⟩ := h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  exact {
    lay := ⟨b19, b23, d4, d14, d18, b24⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), BitVec.isLt _, b20, d6, d15⟩
    aad := ⟨mrd _ (by simp), BitVec.isLt _, b21, d8, d16⟩
    data := ⟨⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b22, d9, d17⟩, mwr _ (by simp), d3⟩
    tag := ⟨mrd _ (by simp), BitVec.isLt _, bt, t2, t4⟩
    nd := d5
    ad := d7
    td := t1
    n1 := hn1
    n15 := hn15
    t1 := ht1
    t16 := ht16
    retW := d13
    retD := d12
    retT := t3
    args := mrd (args s 5) (by simp)
    argsW := d11.symm }

theorem sealArgs_of {s : State} (h : sealPreX s) :
    Args s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) := by
  obtain ⟨hrd, hwr, -, -, -, -, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem openArgs_of {s : State} (h : openPreX s) :
    Args s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) := by
  obtain ⟨hrd, hwr, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

section
variable {K W SP D : Addr} {n : Nat} {m m' : Mem}

theorem saved_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩)
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
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD
    · exact hP.w.sub_right (Lay.wSub (by decide))) (by have := hP.lt; omega)

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
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 3584⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega)
  · exact hD
  · exact hW.sub_right (Lay.wSub (by decide))

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega,
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-- What the pieces before the data leave: the offset, the checksum, `L_$`,
the table of `L_j` and `HASH`. -/
structure Pre (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (s s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (entryR W :: mutR W SP D n) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : Slots W R N A D nl n tl s'.mem
  tg : s'.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  saved : Saved s'.mem W s.gpr
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  ck : blockAtMem s'.mem (W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K)
  tbl : TblL W (ctxLstar s.mem K) n s'.mem
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al)
  ciph : ctxCiph s'.mem K R = ctxCiph s.mem K R
  lstar : ctxLstar s'.mem K = ctxLstar s.mem K
  data : bytesAt s'.mem D n = bytesAt s.mem D n

/-- The table misses what `nonce` writes. -/
theorem wT_nonceR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ nonceR W SP, (wT W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.wT_w (by decide)
  · exact L.wT_w (by decide)
  · exact L.wT_w (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- The table misses what `HASH` writes. -/
theorem wT_hashR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ hashR W SP, (wT W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.wT_w (by decide)
  · exact L.wT_w (by decide)
  · exact L.wT_w (by decide)
  · exact L.wT_w (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- A frame within the table is within what the pieces write. -/
theorem wT_mut {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame [wT W] m m') : Frame (mutR W SP D n) m m' :=
  h.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-- `entry`, `table`, `nonce` and `hash`. -/
theorem pre_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (.seq (.block entry) (.seq table (.seq (nonce (callees v)) (hash (callees v))))) s
      (Pre K W SP N A D R nl al n tl T s) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain ⟨s₀, run₀, P₀⟩ := entry_ok L Ar.perm hsp Ar.args Ar.argsW hD hn hT htl hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  -- The table.
  refine WP.seq (WP.mono (table_ok P₀.env Ar.data.lt Ar.aad.lt P₀.slots.len P₀.alen P₀.l0) fun s₁ Q₁ => ?_)
  have F₁ : Frame (mutR W SP D n) s₀.mem s₁.mem := wT_mut Q₁.frame
  have kW₁ : ∀ {d : Nat}, d + 16 ≤ 2560 →
      blockAtMem s₁.mem (W + BitVec.ofNat 64 d) = blockAtMem s₀.mem (W + BitVec.ofNat 64 d) := fun hd =>
    blockAtMem_frame Q₁.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.wT_w hd).symm
  have S₁ := Slots.of_mut L Ar.data.w F₁ P₀.slots
  have rd₁ : s₁.rd = s.rd := by rw [Q₁.rd, P₀.rd]
  have wr₁ : s₁.wr = s.wr := by rw [Q₁.wr, P₀.wr]
  have eK : ctxCiph s₁.mem K R = ctxCiph s.mem K R := by
    rw [ctxCiph_mut L Ar.data.k F₁ Ar.rounds]
    unfold ctxCiph
    rw [bytesAt_frame P₀.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega)]
  have eL : ctxLstar s₁.mem K = ctxLstar s.mem K := by
    rw [lstar_mut L Ar.data.k F₁]
    exact blockAtMem_frame P₀.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide)))
  have eB : ∀ {P : Addr} {k : Nat}, Buf W SP s P k → bytesAt s₁.mem P k = bytesAt s.mem P k := fun hP => by
    rw [bytesAt_frame Q₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)]
    exact bytesAt_frame P₀.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have alen₁ : s₁.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al := by
    rw [Q₁.frame.readW (r := ⟨W + BitVec.ofNat 64 alenO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.wT_w (by decide)).symm) (by decide), P₀.alen]
  -- `Offset_0`.
  refine WP.seq (WP.mono (nonce_ok v L Q₁.env Ar.rounds S₁.rounds S₁.nonce S₁.nlen S₁.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega) (Ar.nonce.of_eq rd₁ wr₁) Ar.data.k Ar.data.w) fun s₂ P₂ => ?_)
  have F₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := nonceR_mut P₂.frame
  have S₂ := Slots.of_mut L Ar.data.w F₂ S₁
  have c₂ : ctxCiph s₂.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₂ Ar.rounds).trans eK
  have l₂ : ctxLstar s₂.mem K = ctxLstar s.mem K := (lstar_mut L Ar.data.k F₂).trans eL
  have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := (buf_mut Ar.aad Ar.ad F₂).trans (eB Ar.aad)
  -- `HASH`.
  have C : HCtx K W SP D n R (ctxCiph s.mem K R) (ctxLstar s.mem K) A (bytesAt s.mem A al) s₂ :=
    { lay := L, rounds := Ar.rounds, ciph := c₂, lstar := l₂
      buf := by rw [length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans rd₁) (P₂.wr.trans wr₁)
      aad := by rw [length_bytesAt, a₂]
      ad := by rw [length_bytesAt]; exact Ar.ad
      kd := Ar.data.k, dw := Ar.data.w, rnd := S₂.rounds
      short := by rw [length_bytesAt]; exact Ar.aad.lt
      tbl := by
        rw [length_bytesAt]
        exact ⟨_, Q₁.tbl.frame P₂.frame (wT_nonceR L), Nat.div_le_div_right Nat.right_le_or⟩ }
  refine WP.mono (hash_ok v C P₂.env S₂.aad (by rw [P₂.alen, alen₁, length_bytesAt]))
    fun s₃ ⟨E₃, F₃, sum₃, rd₃, wr₃⟩ => ?_
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
  refine ⟨E₃, ?_, by rw [rd₃, P₂.rd, rd₁], by rw [wr₃, P₂.wr, wr₁], Slots.of_mut L Ar.data.w F₃' S₂,
    by rw [kept_read L Ar.data.w (F₁.trans (F₂.trans F₃')) (d := tgO) (by decide), P₀.tg],
    saved_mut L Ar.data.w (F₁.trans (F₂.trans F₃')) P₀.saved, ?_, ?_, ?_, ?_, ?_, by rw [sum₃],
    (ctxCiph_mut L Ar.data.k F₃' Ar.rounds).trans c₂, (lstar_mut L Ar.data.k F₃').trans l₂, ?_⟩
  · exact (P₀.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩).trans
      ((F₁.trans (F₂.trans F₃')).sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  · rw [k₃ (d := ofsO) (by decide), P₂.ofs, eK, eB Ar.nonce]
  · rw [k₃ (d := o0O) (by decide), P₂.o0, eK, eB Ar.nonce]
  · rw [k₃ (d := ckO) (by decide), P₂.keep (by decide) (by decide), kW₁ (by decide), P₀.ck]
  · rw [k₃ (d := ldO) (by decide), P₂.keep (by decide) (by decide), kW₁ (by decide), P₀.ld]
  · exact ⟨_, (Q₁.tbl.frame P₂.frame (wT_nonceR L)).frame F₃ (wT_hashR L),
      Nat.div_le_div_right Nat.left_le_or⟩
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

/-- `entry`, `table`, `nonce` and `hash`, then `k`. -/
theorem pre_wp (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al)
    {k : Prog isa} {Q : State → Prop} (hk : ∀ s', Pre K W SP N A D R nl al n tl T s s' → WP isa k s' Q) :
    WP isa (.seq (.block entry) (.seq table (.seq (nonce (callees v)) (.seq (hash (callees v)) k)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (pre_wp' v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9)) fun _ h₁ =>
    WP.seq (WP.mono (WP.seq_iff.mp h₁) fun _ h₂ => wp_seq_assoc (WP.seq (WP.mono h₂ hk))))

/-- `body`'s frame misses a block of `W` outside the offset, the checksum and
`[96, 144)`. -/
theorem body_keep {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {m m' : Mem}
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

/-- What `front` leaves for `seal`: the environment, the slots and the
address of the tag, our caller's registers, the encrypted data and the tag
at `W`. -/
structure SFront (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (s s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (entryR W :: mutR W SP D n) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : Slots W R N A D nl n tl s'.mem
  tg : s'.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  saved : Saved s'.mem W s.gpr
  out : Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
    (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem W tl)

/-- `seal`'s `front`, for its arguments. -/
theorem sealFront_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (front (callees v) true tagO) s (SFront K W SP N A D R nl al n tl T s) := by
  have L := Ar.lay
  unfold front
  refine pre_wp v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9 fun s₃ P₃ => ?_
  have hD₃ : DBuf K W SP s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  refine WP.seq (WP.mono (bodySeal_ok v L P₃.env Ar.rounds P₃.slots.rounds hD₃ P₃.slots.data P₃.slots.len P₃.ofs
    P₃.o0 P₃.ck (by rw [P₃.lstar]; exact P₃.tbl)) fun s₄ B => ?_)
  have F₄ : Frame (mutR W SP D n) s₃.mem s₄.mem := bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans P₃.ciph
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag.
  refine WP.mono (tag_ok v L B.env Ar.rounds ((kept_read L Ar.data.w F₄ (d := 232) (by decide)).trans
    P₃.slots.rounds) (.inl rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (mutR W SP D n) s₄.mem s₅.mem := tagR_mut (by decide) T₅.frame
  refine ⟨T₅.env, P₃.frame.trans ((F₄.trans F₅).sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩),
    by rw [T₅.rd, B.rd, P₃.rd], by rw [T₅.wr, B.wr, P₃.wr], Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots,
    by rw [kept_read L Ar.data.w (F₄.trans F₅) (d := tgO) (by decide), P₃.tg],
    saved_mut L Ar.data.w (F₄.trans F₅) P₃.saved, ?_⟩
  -- The ciphertext and the tag.
  have hout := B.out
  rw [P₃.ciph, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.data] at hck
  have d₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n :=
    bytesAt_frame T₅.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm) (by have := Ar.data.lt; omega)
  have tv := T₅.val
  rw [show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
  have t₅ : bytesAt s₅.mem W tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem W)).take tl :=
    bytesAt_take_block _ _ Ar.t16
  rw [Proof.Ocb.encryptWith_eq, d₅, hout, t₅, tv, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

/-- The arguments of `copyLoop` for the copy of the tag: from `W` to the
tag, whose address is at `W + tgO`. -/
theorem tagOutArgs_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {T : Addr} {tl : Nat}
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    ∃ s', runBlock isa [mvr .rbx .r15, ld .rsi .r15 tgO, ld .r12 .r15 tlO, .mov .rcx (.imm 0)] s = some s' ∧
      s'.gpr .rbx = W ∧ s'.gpr .rsi = T ∧ s'.gpr .r12 = BitVec.ofNat 64 tl ∧ s'.gpr .rcx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → r ≠ .r12 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [tgO, tlO] at htg htl
  have r₁ := E.perm.wR (show 304 + 8 ≤ 3584 by decide)
  have r₂ := E.perm.wR (show 224 + 8 ≤ 3584 by decide)
  refine ⟨_, by orun [E.r15, r₁, r₂, htg, htl], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htg]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htl]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sext0]
  · simp only [gpr_setReg, h₁, h₂, h₃, h₄, ite_false]
  all_goals rfl

/-- The received tag's arguments of `copyLoop`: from the tag, whose address
is at `W + tgO`, to `W`. -/
theorem recvArgs_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {T : Addr} {tl : Nat}
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    ∃ s', runBlock isa [ld .rbx .r15 tgO, mvr .rsi .r15, ld .r12 .r15 tlO, .mov .rcx (.imm 0)] s = some s' ∧
      s'.gpr .rbx = T ∧ s'.gpr .rsi = W ∧ s'.gpr .r12 = BitVec.ofNat 64 tl ∧ s'.gpr .rcx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → r ≠ .r12 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [tgO, tlO] at htg htl
  have r₁ := E.perm.wR (show 304 + 8 ≤ 3584 by decide)
  have r₂ := E.perm.wR (show 224 + 8 ≤ 3584 by decide)
  refine ⟨_, by orun [E.r15, r₁, r₂, htg, htl], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htg]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htl]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sext0]
  · simp only [gpr_setReg, h₁, h₂, h₃, h₄, ite_false]
  all_goals rfl

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`, which the
state may write. -/
theorem tagOut_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {T : Addr} {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : Covers [⟨T, tl⟩] s.wr) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 3584⟩) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem T (bytesAt s.mem W tl) ∧
      (∀ r ∈ [Reg.r14, .r15, .rsp], t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, rbx₁, rsi₁, r12₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := tagOutArgs_ok E htg htl
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (copyLoop_ok s₁ (S := W) (Dd := T) (n := tl) (by omega) (by omega) rbx₁ rsi₁ rcx₁ r12₁
    (by rw [rd₁, wr₁]; exact covers_left (covers_prefix E.perm.w (by omega))) (by rw [wr₁]; exact hT)
    (hTW.sub_right (Region.sub_prefix (by omega))).symm) fun t ⟨m, _, g, rd, wr⟩ => ⟨by rw [m, m₁], ?_,
      by rw [rd, rd₁], by rw [wr, wr₁]⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rw [g _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)]

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W SP N A D R nl al n tl T) (hTw : Covers [⟨T, tl⟩] s.wr) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («seal» (callees v)) s fun s' => gprPreserved s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  have L := Ar.lay
  unfold «seal»
  refine WP.seq (WP.mono (sealFront_wp' v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9) fun s₅ F => ?_)
  -- The copy of the tag.
  refine WP.seq (WP.mono (tagOut_ok F.env Ar.t1 Ar.t16 F.tg F.slots.tl (by rw [F.wr]; exact hTw) Ar.tag.w)
    fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  have E₆ : Env K W SP s₆ := F.env.keep g₆ rd₆ wr₆
  have F₆ : Frame [⟨T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  have S₆ : Saved s₆.mem W s.gpr := fun p hp => by
    rw [← F.saved p hp]
    exact F₆.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have hd : p.2 + 8 ≤ 3584 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (Ar.tag.w.sub_right (Lay.wSub hd)).symm) (by decide)
  -- `restore`.
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, _⟩ := restore_ok E₆ S₆
  refine WP.of_runBlock ⟨s₇, run₇, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₇ (.rbx, savO) (by decide)
    · exact hg₇ (.rbp, savO + 8) (by decide)
    · rw [hsp₇, E₆.rsp, hsp]
    · exact hg₇ (.r12, savO + 16) (by decide)
    · exact hg₇ (.r13, savO + 24) (by decide)
    · exact hg₇ (.r14, savO + 32) (by decide)
    · exact hg₇ (.r15, savO + 40) (by decide)
  · rw [hm₇, hsp, F₆.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.retT) (by decide)]
    exact F.frame.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The ciphertext and the tag.
    have hn := Ar.data.lt
    have ht := Ar.tag.lt
    rw [F.out, hm₇, bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by omega), m₆,
      Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) ht, length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp (v : BlocksImpl) {s : State} (h : sealPreX s) :
    WP isa («seal» (callees v)) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' :=
  seal_wp' v (sealArgs_of h) (covers_of_mem (by rw [h.2.1]; simp)) rfl rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.X86_64
