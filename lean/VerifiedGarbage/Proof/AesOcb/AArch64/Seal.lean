import VerifiedGarbage.Proof.AesOcb.AArch64.Body
import VerifiedGarbage.Proof.AesOcb.AArch64.Entry
import VerifiedGarbage.Proof.AesOcb.AArch64.Hash
import VerifiedGarbage.Proof.AesOcb.AArch64.Nonce

/-!
# AES-OCB on AArch64: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. The preconditions `sealPreA`
and `openPreA` give the facts the proofs use about the arguments (`Args`,
`sealArgs_of`, `openArgs_of`). `seal` is `front`: `entry`, `Offset_0`
(`nonce`), `HASH` (`hash`), the data (`body`) and the tag at `W` (`tag`);
then the copy of the tag to `tag`, whose address is on the stack
(`tagOut`), and `restore` (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_left)

/-- What `seal` and `open` are given: the key context at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`) and the
working space at `W`. -/
structure Args (s : State) (K W N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop where
  lay : Lay K W
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W s N nl
  aad : Buf W s A al
  data : DBuf K W s D n
  tag : Buf W s T tl
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  td : (⟨T, tl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  n1 : 1 ≤ nl
  n15 : nl ≤ 15
  t1 : 1 ≤ tl
  t16 : tl ≤ 16
  args : Covers [⟨s.sp, 24⟩] (s.rd ++ s.wr)
  argsW : (⟨s.sp, 24⟩ : Region).Disjoint ⟨W, 2560⟩
  argsD : (⟨s.sp, 24⟩ : Region).Disjoint ⟨D, n⟩

/-- `Args` from the facts both preconditions give, for a state that may
read the key context, the nonce, the associated data, the arguments on the
stack and the tag, and write the data and `W`. -/
theorem args_of {s : State} (h : oneFacts s)
    (mrd : ∀ r ∈ [aCtx s, aNonce s, aAad s, args s 3, aTag s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [aData s, aWork s], Covers [r] s.wr) :
    Args s (s.gpr .x0) (stackArg s 2) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x1).toNat (s.gpr .x3).toNat
      (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨d3, d4, d5, d6, d7, d8, t1, t2, d9, d10, d11, b12, b13, b14, b15, bt, b16, _, hR, hv⟩ := h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  have sp0 : stackArgAddr s 0 = s.sp := by simp [stackArgAddr]
  have ha := mrd (args s 3) (by simp)
  simp only [args, sp0] at ha d10 d11
  exact {
    lay := ⟨b12, b16, d4⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), BitVec.isLt _, b13, d6⟩
    aad := ⟨mrd _ (by simp), BitVec.isLt _, b14, d8⟩
    data := ⟨⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b15, d9⟩, mwr _ (by simp), d3⟩
    tag := ⟨mrd _ (by simp), BitVec.isLt _, bt, t2⟩
    nd := d5
    ad := d7
    td := t1
    n1 := hn1
    n15 := hn15
    t1 := ht1
    t16 := ht16
    args := ha
    argsW := d11.symm
    argsD := d10.symm }

theorem sealArgs_of {s : State} (h : sealPreA s) :
    Args s (s.gpr .x0) (stackArg s 2) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x1).toNat (s.gpr .x3).toNat
      (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, -, -, -, -, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem openArgs_of {s : State} (h : openPreA s) :
    Args s (s.gpr .x0) (stackArg s 2) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x1).toNat (s.gpr .x3).toNat
      (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-! ## Frames -/

/-- A frame within `W`. -/
theorem frameW {W : Addr} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨W, 2560⟩) : Frame [⟨W, 2560⟩] m m' :=
  h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem entryR_W (W : Addr) : ∀ r ∈ [entryR W], Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)

theorem nonceR_W (W : Addr) : ∀ r ∈ nonceR W, Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem hashR_W (W : Addr) : ∀ r ∈ hashR W, Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact Lay.wSub (by decide)

/-- A buffer apart from `W`, after a frame within `W`. -/
theorem bytesAt_W {W P : Addr} {k : Nat} (hP : (⟨P, k⟩ : Region).Disjoint ⟨W, 2560⟩) (hk : k < 2 ^ 64) {m m' : Mem}
    (h : Frame [⟨W, 2560⟩] m m') : bytesAt m' P k = bytesAt m P k :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hP) (by omega)

theorem ctxCiph_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [bytesAt_W (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega) h]

theorem ctxInv_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : Spec.Ocb.ctxInv m' K R = Spec.Ocb.ctxInv m K R := by
  unfold Spec.Ocb.ctxInv
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [bytesAt_W (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega) h]

theorem ctxLstar_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') :
    ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_left (Lay.kSub (by decide))

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {W D : Addr} {n d : Nat} (hd : d + 16 ≤ 160) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩] m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA hd
  · exact in_mutB (by decide) (by decide)

/-- The saved registers, after a frame within the parts the pieces write. -/
theorem saved_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {g : Reg → BitVec 64} {m m' : Mem} (h : Spill.Saved W g saved m) (hf : Frame (mutR W D n) m m') :
    Spill.Saved W g saved m' :=
  Spill.Saved.frame_in h saved_in hf (kept_mut L hD (by decide))

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega,
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-! ## Before the data -/

/-- What the pieces before the data leave: the offset, the checksum, `L_$`,
`L_0` and `HASH`. -/
structure Pre (K W D : Addr) (R n : Nat) (N A : Addr) (nl al tl : Nat) (s s' : State) : Prop where
  env : Env K W D R n s.sp s'
  frame : Frame [⟨W, 2560⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : Slots W N A nl al tl s'.mem
  saved : Spill.Saved W s.gpr saved s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  ck : blockAtMem s'.mem (W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K)
  l0 : blockAtMem s'.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al)

/-- What `HASH` needs, after `entry` and `nonce`. -/
theorem hctx_of {s : State} {K W N A D : Addr} {R nl al n tl : Nat} {T : Addr} (Ar : Args s K W N A D R nl al n tl T)
    {s₁ s₂ : State} (P₁ : EntryPost K W D R n N A nl al tl s s₁) {SP : Addr} {o : Block}
    (P₂ : NonceOk K W D R n SP o s₁ s₂) :
    HCtx K W D n R (ctxCiph s.mem K R) (ctxLstar s.mem K) A (bytesAt s.mem A al) s₂ :=
  have L := Ar.lay
  have F₁ : Frame [⟨W, 2560⟩] s.mem s₁.mem := frameW P₁.frame (entryR_W W)
  have F₂ : Frame [⟨W, 2560⟩] s₁.mem s₂.mem := frameW P₂.frame (nonceR_W W)
  { lay := L, rounds := Ar.rounds
    ciph := by rw [ctxCiph_W L F₂ Ar.rounds, ctxCiph_W L F₁ Ar.rounds]
    lstar := by rw [ctxLstar_W L F₂, ctxLstar_W L F₁]
    buf := by rw [length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans P₁.rd) (P₂.wr.trans P₁.wr)
    aad := by rw [length_bytesAt, bytesAt_W Ar.aad.w Ar.aad.lt F₂, bytesAt_W Ar.aad.w Ar.aad.lt F₁]
    ad := by rw [length_bytesAt]; exact Ar.ad
    kd := Ar.data.k, dw := Ar.data.w }

/-- `entry`, `nonce` and `hash`. -/
theorem pre_wp' (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W N A D R nl al n tl T) (hW : stackArg s 2 = W)
    (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa (.seq (.block entry) (.seq (nonce (callees v)) (hash (callees v)))) s
      (Pre K W D R n N A nl al tl s) := by
  have L := Ar.lay
  refine WP.seq (WP.mono (entry_ok L Ar.perm hW htl Ar.args Ar.argsW h0 h1 h2 h3 h4 h5 h6 h7) fun s₁ P₁ => ?_)
  have F₁ : Frame [⟨W, 2560⟩] s.mem s₁.mem := frameW P₁.frame (entryR_W W)
  -- `Offset_0`.
  refine WP.seq (WP.mono (nonce_ok v L P₁.env Ar.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega) (Ar.nonce.of_eq P₁.rd P₁.wr) Ar.data.k) fun s₂ P₂ => ?_)
  have F₂ : Frame [⟨W, 2560⟩] s₁.mem s₂.mem := frameW P₂.frame (nonceR_W W)
  have S₂ := Slots.of_mut L Ar.data.w (nonceR_mut (D := D) (n := n) P₂.frame) P₁.slots
  -- `HASH`.
  have C := hctx_of Ar P₁ P₂
  refine WP.mono (hash_ok v C P₂.env S₂.aad (by rw [length_bytesAt]; exact S₂.alen)
    (by rw [P₂.keep (by decide) (by decide), P₁.l0])) fun s₃ ⟨E₃, F₃, sum₃, rd₃, wr₃⟩ => ?_
  have F₃' : Frame [⟨W, 2560⟩] s₂.mem s₃.mem := frameW F₃ (hashR_W W)
  have k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (160 ≤ d ∧ d + 16 ≤ 384)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) := fun {d} hd =>
    blockAtMem_frame F₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact L.w_w (by omega) (by omega) (by decide)
  refine ⟨E₃, F₁.trans (F₂.trans F₃'), by rw [rd₃, P₂.rd, P₁.rd], by rw [wr₃, P₂.wr, P₁.wr],
    Slots.of_mut L Ar.data.w (hashR_mut F₃) S₂,
    saved_mut L Ar.data.w (saved_mut L Ar.data.w P₁.saved (nonceR_mut P₂.frame)) (hashR_mut F₃), ?_, ?_, ?_, ?_,
    ?_, by rw [sum₃]⟩
  · rw [k₃ (d := ofsO) (by decide), P₂.ofs, ctxCiph_W L F₁ Ar.rounds, bytesAt_W Ar.nonce.w Ar.nonce.lt F₁]
  · rw [k₃ (d := o0O) (by decide), P₂.o0, ctxCiph_W L F₁ Ar.rounds, bytesAt_W Ar.nonce.w Ar.nonce.lt F₁]
  · rw [k₃ (d := ckO) (by decide), P₂.keep (by decide) (by decide), P₁.ck]
  · rw [k₃ (d := ldO) (by decide), P₂.keep (by decide) (by decide), P₁.ld]
  · rw [k₃ (d := l0O) (by decide), P₂.keep (by decide) (by decide), P₁.l0]

/-- `entry`, `nonce` and `hash`, then `k`. -/
theorem pre_wp (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W N A D R nl al n tl T) (hW : stackArg s 2 = W)
    (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n)
    {k : Prog isa} {Q : State → Prop} (hk : ∀ s', Pre K W D R n N A nl al tl s s' → WP isa k s' Q) :
    WP isa (.seq (.block entry) (.seq (nonce (callees v)) (.seq (hash (callees v)) k))) s Q := by
  exact WP.seq (WP.mono (WP.seq_iff.mp (pre_wp' v Ar hW htl h0 h1 h2 h3 h4 h5 h6 h7)) fun _ h₁ =>
    WP.assoc (WP.seq (WP.mono h₁ hk)))

/-- `body`'s frame misses a block of `W` outside the offset, the checksum and
`[96, 144)`. -/
theorem body_keep {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame (bodyR W D n) m m') {d : Nat} (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (144 ≤ d ∧ d + 16 ≤ 512)) :
    blockAtMem m' (W + BitVec.ofNat 64 d) = blockAtMem m (W + BitVec.ofNat 64 d) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- `tag d`'s frame misses the data. -/
theorem tag_data {W D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hd : d + 16 ≤ 512) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩],
      (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hD.sub_right (Lay.wSub (by first | omega | (simp only [tmpO]; omega)))

/-- The registers `restore` restores are our caller's. -/
theorem restore_abi {s t t' : State} (h : Spill.Restored s.gpr saved t t') (hsp : t.sp = s.sp) : GprAbi s t' := by
  refine ⟨fun r hr => ?_, by rw [h.sp, hsp]⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((by decide : ∀ r ∈ preserved, r ∈ saved.map Prod.fst) r hr)
  exact h.gpr p hp

/-- `restore`. -/
theorem restore_wp' {K W D : Addr} {R n : Nat} {SP : Addr} {t : State} (E : Env K W D R n SP t)
    {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved t.mem) :
    WP isa (.block restore) t (Spill.Restored g saved t) := by
  rw [restore_eq]
  exact Spill.restore_wp E.x19 saved_fits.1 (by decide) (fun p hp => E.perm.wR (by have := saved_in p hp; omega))
    hsv

/-- The arguments on the stack, apart from `W` and the data, are kept by a
frame within them. -/
theorem args_kept {W D : Addr} {n : Nat} {SP : Addr} (hW : (⟨SP, 24⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP, 24⟩ : Region).Disjoint ⟨D, n⟩) {m m' : Mem} (h : Frame [⟨W, 2560⟩, ⟨D, n⟩] m m') {i : Nat}
    (hi : i < 3) : m'.readW (SP + BitVec.ofNat 64 (8 * i)) 64 = m.readW (SP + BitVec.ofNat 64 (8 * i)) 64 :=
  h.readW (r := ⟨SP + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hW.sub_left (Offset.sub_base _ (by omega))
    · exact hD.sub_left (Offset.sub_base _ (by omega))) (by decide)

/-- The frame of `front`, from those of its pieces. -/
theorem front_frame {W D : Addr} {n : Nat} {m₀ m₃ m₄ m₅ : Mem} {d : Nat} (hd : d + 16 ≤ 160)
    (P : Frame [⟨W, 2560⟩] m₀ m₃) (B : Frame (bodyR W D n) m₃ m₄)
    (T : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩] m₄ m₅) :
    Frame [⟨W, 2560⟩, ⟨D, n⟩] m₀ m₅ :=
  have M : Frame (mutR W D n) m₃ m₅ := (bodyR_mut B).trans (tagR_mut hd T)
  (P.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans (M.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)

/-- The first block of `tagOut`: the tag's address from the stack, `W` and
the tag length. -/
theorem tagOutHead_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {T : Addr}
    {tl : Nat} (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT : stackArg s 0 = T)
    (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8) :
    ∃ s₁, runBlock isa [.ldrSp .x11 0, Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] s = some s₁ ∧
      s₁.gpr .x11 = T ∧ s₁.gpr .x12 = W ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧ s₁.mem = s.mem ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  obtain ⟨_, run₀, rfl⟩ := ldrSp_ok (t := .x11) (s := s) (i := 0) (by decide) ha
  simp only [Nat.reduceMul] at run₀
  have r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 248) 8 := E.perm.wR (by decide)
  have h19 : (s.write .x .x11 (stackArg s 0)).gpr .x19 = W := by simp [gpr_write, E.x19]
  have htl' : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl := htl
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] (s.write .x .x11 (stackArg s 0)) = some s₁ ∧
      s₁.gpr .x11 = stackArg s 0 ∧ s₁.gpr .x12 = W ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [E.x19, r₀, htl'], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, htl']
    · simp only [Proof.AesGcm.AArch64.loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1]
    all_goals rfl
  exact ⟨s₁, by rw [show ([.ldrSp .x11 0, Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] : List Instr) =
    [.ldrSp .x11 0] ++ [Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] from rfl, runBlock_append, run₀,
    Option.bind_some, run₁], by rw [x11₁, hT], x12₁, x13₁, m₁, g₁, sp₁, rd₁, wr₁⟩

/-- The first block of `recv`: `W`, the tag's address from the stack and the
tag length. -/
theorem recvHead_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {T : Addr}
    {tl : Nat} (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT : stackArg s 0 = T)
    (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8) :
    ∃ s₁, runBlock isa [Impl.AesGcm.AArch64.mov .x11 .x19, .ldrSp .x12 0, ld .x13 .x19 tlO] s = some s₁ ∧
      s₁.gpr .x11 = W ∧ s₁.gpr .x12 = T ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧ s₁.mem = s.mem ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  obtain ⟨s₀, run₀, x11₀, g₀, m₀, sp₀, rd₀, wr₀⟩ : ∃ s₀, runBlock isa [Impl.AesGcm.AArch64.mov .x11 .x19] s = some s₀ ∧
      s₀.gpr .x11 = W ∧ (∀ r, r ≠ .x11 → s₀.gpr r = s.gpr r) ∧ s₀.mem = s.mem ∧ s₀.sp = s.sp ∧ s₀.rd = s.rd ∧
      s₀.wr = s.wr := by
    refine ⟨_, by orun [E.x19], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, E.x19]
    · simp [gpr_write, hr]
    all_goals rfl
  have ha₀ : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 (8 * 0)) 8 := by rw [rd₀, wr₀, sp₀]; exact ha
  obtain ⟨_, run₁, rfl⟩ := ldrSp_ok (t := .x12) (s := s₀) (i := 0) (by decide) ha₀
  simp only [Nat.reduceMul] at run₁
  have hT₀ : stackArg s₀ 0 = T := by rw [← hT]; simp only [stackArg, stackArgAddr, m₀, sp₀]
  have r₀ : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 248) 8 := by
    rw [rd₀, wr₀]; exact E.perm.wR (by decide)
  have h19 : s₀.gpr .x19 = W := by rw [g₀ .x19 (by decide), E.x19]
  have htl' : s₀.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl := by rw [m₀]; exact htl
  obtain ⟨s₁, run₂, x11₁, x12₁, x13₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [ld .x13 .x19 tlO]
      (s₀.write .x .x12 (stackArg s₀ 0)) = some s₁ ∧
      s₁.gpr .x11 = W ∧ s₁.gpr .x12 = T ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [h19, r₀, htl'], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, x11₀]
    · simp [gpr_write, hT₀]
    · simp [gpr_write, h19, htl']
    · simp only [Proof.AesGcm.AArch64.loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, g₀ r hr.1]
    · simp [mem_write, m₀]
    · simp [sp_write, sp₀]
    · simp [rd_write, rd₀]
    · simp [wr_write, wr₀]
  exact ⟨s₁, by rw [show ([Impl.AesGcm.AArch64.mov .x11 .x19, .ldrSp .x12 0, ld .x13 .x19 tlO] : List Instr) =
    [Impl.AesGcm.AArch64.mov .x11 .x19] ++ ([.ldrSp .x12 0] ++ [ld .x13 .x19 tlO]) from rfl, runBlock_append,
    run₀, Option.bind_some, runBlock_append, run₁, Option.bind_some, run₂], x11₁, x12₁, x13₁, m₁, g₁, sp₁, rd₁,
    wr₁⟩

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`, which the
state may write. -/
theorem tagOut_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {T : Addr}
    {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : stackArg s 0 = T) (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (hTw : Covers [⟨T, tl⟩] s.wr) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem T (bytesAt s.mem W tl) ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := tagOutHead_ok E htl hT ha
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (Proof.AesGcm.AArch64.copyLoop_ok s₁ x12₁ x11₁ x13₁ (by omega)
    ⟨by omega, by
      rw [rd₁, wr₁]
      exact covers_left fun a m ⟨r, hr, hc⟩ => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩,
      by rw [wr₁]; exact hTw,
      (hTW.sub_right (Region.sub_prefix (by omega))).symm⟩)
    fun t ⟨m, _, _, g, sp, rd, wr⟩ => ⟨by rw [m, m₁], fun r hr => by rw [g r hr, g₁ r hr], by rw [sp, sp₁],
      by rw [rd, rd₁], by rw [wr, wr₁]⟩

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W N A D R nl al n tl T) (hTw : Covers [⟨T, tl⟩] s.wr) (hW : stackArg s 2 = W)
    (hT : stackArg s 0 = T) (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa («seal» (callees v)) s fun s' => GprAbi s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  have L := Ar.lay
  unfold «seal» front
  refine WP.seq (pre_wp v Ar hW htl h0 h1 h2 h3 h4 h5 h6 h7 fun s₃ P₃ => ?_)
  have hD₃ : DBuf K W s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  have c₃ : ctxCiph s₃.mem K R = ctxCiph s.mem K R := ctxCiph_W L P₃.frame Ar.rounds
  have l₃ : ctxLstar s₃.mem K = ctxLstar s.mem K := ctxLstar_W L P₃.frame
  have d₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := bytesAt_W Ar.data.w Ar.data.lt P₃.frame
  refine WP.seq (WP.mono (bodySeal_ok v L P₃.env Ar.rounds hD₃ P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, l₃]))
    fun s₄ B => ?_)
  have F₄ : Frame (mutR W D n) s₃.mem s₄.mem := bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans c₃
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag.
  refine WP.mono (tag_ok v L B.env Ar.rounds (.inl rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (mutR W D n) s₄.mem s₅.mem := tagR_mut (by decide) T₅.frame
  have S₅ := Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots
  have sv₅ := saved_mut L Ar.data.w (saved_mut L Ar.data.w P₃.saved F₄) F₅
  have Ff := front_frame (by decide) P₃.frame B.frame T₅.frame
  have sp₅ : s₅.sp = s.sp := T₅.env.sp
  -- The copy of the tag.
  have hT₅ : stackArg s₅ 0 = T := by
    rw [← hT]; simp only [stackArg, stackArgAddr, sp₅]
    exact args_kept Ar.argsW Ar.argsD Ff (i := 0) (by decide)
  have ha₅ : InRegions (s₅.rd ++ s₅.wr) (s₅.sp + BitVec.ofNat 64 (8 * 0)) 8 := by
    rw [T₅.rd, B.rd, P₃.rd, T₅.wr, B.wr, P₃.wr, sp₅]
    exact Proof.AesGcm.AArch64.in_off Ar.args (by decide) (by decide)
  refine WP.seq (WP.mono (tagOut_ok T₅.env Ar.t1 Ar.t16 S₅.tl hT₅ ha₅
    (by rw [T₅.wr, B.wr, P₃.wr]; exact hTw) Ar.tag.w) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_)
  have E₆ := T₅.env.others g₆ sp₆ rd₆ wr₆
  have F₆ : Frame [⟨T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  have sv₆ : Spill.Saved W s.gpr saved s₆.mem :=
    Spill.Saved.frame_in sv₅ saved_in F₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Ar.tag.w.sub_right (Lay.wSub (by decide))).symm
  -- `restore`.
  refine WP.mono (restore_wp' E₆ sv₆) fun s₇ Rs => ⟨restore_abi Rs E₆.sp, ?_⟩
  have hout := B.out
  rw [c₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [l₃] at hofs
  have hck := B.ck
  rw [d₃] at hck
  have hn := Ar.data.lt
  have ht := Ar.tag.lt
  have d₇ : bytesAt s₇.mem D n = bytesAt s₄.mem D n := by
    rw [Rs.mem, Proof.Cmac.bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by omega)]
    exact Proof.Cmac.bytesAt_frame T₅.frame (tag_data Ar.data.w (by decide)) (by omega)
  have tv := T₅.val
  rw [show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
  have t₇ : bytesAt s₇.mem T tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem W)).take tl := by
    rw [Rs.mem, m₆, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) ht, length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, bytesAt_take_block _ _ Ar.t16]
  rw [Proof.Ocb.encryptWith_eq, d₇, hout, t₇, tv, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp (v : BlocksImpl) {s : State} (h : sealAArch64.pre s) :
    WP isa («seal» (callees v)) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' :=
  seal_wp' v (sealArgs_of h) (covers_of_mem (by rw [h.2.1]; simp)) rfl rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.AArch64
