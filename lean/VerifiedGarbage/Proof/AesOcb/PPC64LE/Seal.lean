module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Body
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Entry
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Hash
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Nonce
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Contract
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-OCB on PPC64LE: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. The preconditions `sealPreA`
and `openPreA` give the facts the proofs use about the arguments (`FnArgs`,
`sealArgs_of`, `openArgs_of`). `seal` is `front`: `entry`, `Offset_0`
(`nonce`), `HASH` (`hash`), the data (`body`) and the tag at `W` (`tag`);
then the copy of the tag to `tag` (`tagOut`), and `restore` (`seal_wp`). The
environment after the entry is the state's own registers (`EntryPost`). As
on AArch64 (`Proof/AesOcb/AArch64/Seal.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (covers_mem covers_left in_left in_off SavedAt savedR Keeps Keeps')
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_or → cwp_or

/-- What `seal` and `open` are given: the key context at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`) and the
working space at `W`. -/
structure FnArgs (s : State) (K W N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop where
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
  args : Covers [⟨s.sp + BitVec.ofNat 64 96, 24⟩] (s.rd ++ s.wr)
  argsW : (⟨s.sp + BitVec.ofNat 64 96, 24⟩ : Region).Disjoint ⟨W, 2560⟩
  argsD : (⟨s.sp + BitVec.ofNat 64 96, 24⟩ : Region).Disjoint ⟨D, n⟩

/-- `FnArgs` from the facts both preconditions give, for a state that may
read the key context, the nonce, the associated data, the arguments on the
stack and the tag, and write the data and `W`. -/
theorem args_of {s : State} (h : oneFacts s)
    (mrd : ∀ r ∈ [aCtx s, aNonce s, aAad s, args s 3, aTag s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [aData s, aWork s], Covers [r] s.wr) :
    FnArgs s (s.gpr .r3) (stackArg s 2) (s.gpr .r5) (s.gpr .r7) (s.gpr .r9) (s.gpr .r4).toNat (s.gpr .r6).toNat
      (s.gpr .r8).toNat (s.gpr .r10).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨d3, d4, d5, d6, d7, d8, t1, t2, d9, d10, d11, b12, b13, b14, b15, bt, b16, _, hR, hv⟩ := h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  have sp0 : stackArgAddr s 0 = s.sp + BitVec.ofNat 64 96 := rfl
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
    FnArgs s (s.gpr .r3) (stackArg s 2) (s.gpr .r5) (s.gpr .r7) (s.gpr .r9) (s.gpr .r4).toNat (s.gpr .r6).toNat
      (s.gpr .r8).toNat (s.gpr .r10).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, -, -, -, -, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_mem (by simp))

theorem openArgs_of {s : State} (h : openPreA s) :
    FnArgs s (s.gpr .r3) (stackArg s 2) (s.gpr .r5) (s.gpr .r7) (s.gpr .r9) (s.gpr .r4).toNat (s.gpr .r6).toNat
      (s.gpr .r8).toNat (s.gpr .r10).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_mem (by simp))

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-! ## Frames -/

/-- A frame within `W`. -/
theorem frameW {W : Addr} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨W, 2560⟩) : Frame [⟨W, 2560⟩] m m' :=
  h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem entryR_W (W : Addr) : ∀ r ∈ [savedR W, ⟨W + BitVec.ofNat 64 32, 64⟩], Region.Sub r ⟨W, 2560⟩ :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem nonceR_W (W : Addr) : ∀ r ∈ nonceR W, Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem hashR_W (W : Addr) : ∀ r ∈ hashR W, Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Lay.wSub (by decide)

/-- A buffer apart from `W`, after a frame within `W`. -/
theorem bytesAt_W {W P : Addr} {k : Nat} (hP : (⟨P, k⟩ : Region).Disjoint ⟨W, 2560⟩) (hk : k < 2 ^ 64)
    {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') : bytesAt m' P k = bytesAt m P k :=
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
theorem tagR_mut {W D : Addr} {n d : Nat} (hd : d + 16 ≤ 128 ∨ (256 ≤ d ∧ d + 16 ≤ 2560)) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩] m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutW hd
  · exact in_mutB (by decide) (by decide)

/-- Our caller's registers saved in `W`, after a frame within the parts the pieces write. -/
theorem saved_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {s₀ : State} {m m' : Mem} (h : SavedAt m W s₀) (hf : Frame (mutR W D n) m m') : SavedAt m' W s₀ :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa using L.w_w (a := 128) (n := 120) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (a := 128) (n := 120) (d := 256) (k := 2304) (.inl (by decide)) (by decide) (by decide)
    · exact (hD.sub_right (Lay.wSub (W := W) (d := 128) (n := 120) (by decide))).symm

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega,
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-! ## Before the data -/

/-- What the pieces before the data leave, from `s₀` and with `V` the
registers after the entry: the offset, the checksum, `L_$`, `L_0` and
`HASH`. -/
structure Pre (V : Reg → BitVec 64) (K W N A : Addr) (R nl al tl : Nat) (s₀ s' : State) : Prop where
  env : Env V s₀.sp s'
  frame : Frame [⟨W, 2560⟩] s₀.mem s'.mem
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  saved : SavedAt s'.mem W s₀
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)
  ck : blockAtMem s'.mem (W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s₀.mem K)
  l0 : blockAtMem s'.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₀.mem K) 0
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) (bytesAt s₀.mem A al)

/-- `nonce` and `hash`, after the entry (in `s₁`, whose registers are `V`). -/
theorem preRest_wp {s₀ s₁ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (P₁ : EntryPost W T s₀ s₁) (htl : stackArg s₀ 1 = BitVec.ofNat 64 tl)
    (h3 : s₀.gpr .r3 = K) (h4 : s₀.gpr .r4 = BitVec.ofNat 64 R) (h5 : s₀.gpr .r5 = N)
    (h6 : s₀.gpr .r6 = BitVec.ofNat 64 nl) (h7 : s₀.gpr .r7 = A) (h8 : s₀.gpr .r8 = BitVec.ofNat 64 al) :
    WP isa (.seq nonce Impl.AesOcb.PPC64LE.hash) s₁ (Pre s₁.gpr K W N A R nl al tl s₀) := by
  have L : Lay (s₁.gpr .r29) (s₁.gpr .r31) := by rw [P₁.r29, P₁.r31, h3]; exact Ar.lay
  have E₁ := P₁.env
  have h28 : s₁.gpr .r28 = BitVec.ofNat 64 R := P₁.r28.trans h4
  have F₁ : Frame [⟨W, 2560⟩] s₀.mem s₁.mem := frameW P₁.frame (entryR_W W)
  have rd₁ := P₁.keeps.rd
  have wr₁ := P₁.keeps.wr
  have hW₁ : s₁.gpr .r31 = W := P₁.r31
  have hK₁ : s₁.gpr .r29 = K := P₁.r29.trans h3
  have hKD : (⟨s₁.gpr .r29, 256⟩ : Region).Disjoint ⟨D, n⟩ := by rw [hK₁]; exact Ar.data.k
  -- `Offset_0`.
  refine WP.seq (WP.mono (nonce_ok L Ar.rounds h28 E₁ (P₁.r24.trans h5) (P₁.r25.trans h6) (P₁.r19.trans htl)
    Ar.n1 Ar.n15 (by have := Ar.t16; omega) (by rw [hW₁]; exact Ar.nonce.of_eq rd₁ wr₁) hKD) fun s₂ P₂ => ?_)
  have pf₂ : Frame (nonceR W) s₁.mem s₂.mem := by have := P₂.frame; rwa [hW₁] at this
  have ofs₂ := P₂.ofs
  have o0₂ := P₂.o0
  rw [hW₁] at ofs₂ o0₂
  have keep₂ : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
      blockAtMem s₂.mem (W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ => by
    have := P₂.keep h₁ h₂; rwa [hW₁] at this
  have F₂ : Frame [⟨W, 2560⟩] s₁.mem s₂.mem := frameW pf₂ (nonceR_W W)
  -- `HASH`.
  have F₁₂ := F₁.trans F₂
  have C : HCtx (s₁.gpr .r29) (s₁.gpr .r31) D n R (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) A (bytesAt s₀.mem A al)
      s₂ :=
    { lay := L, rounds := Ar.rounds
      ciph := by rw [hK₁, ctxCiph_W Ar.lay F₁₂ Ar.rounds]
      lstar := by rw [hK₁, ctxLstar_W Ar.lay F₁₂]
      buf := by rw [length_bytesAt, hW₁]; exact Ar.aad.of_eq (P₂.rd.trans rd₁) (P₂.wr.trans wr₁)
      aad := by rw [length_bytesAt, bytesAt_W Ar.aad.w Ar.aad.lt F₁₂]
      ad := by rw [length_bytesAt]; exact Ar.ad
      kd := hKD, dw := by rw [hW₁]; exact Ar.data.w }
  refine WP.mono (hash_ok C P₂.env h28 (P₁.r21.trans h7) (by rw [P₁.r22, h8, length_bytesAt])
    (by rw [hW₁, keep₂ (by decide) (by decide), P₁.l0, h3])) fun s₃ H₃ => ?_
  have F₃ : Frame [⟨W, 2560⟩] s₂.mem s₃.mem := by have := H₃.frame; rw [hW₁] at this; exact frameW this (hashR_W W)
  have k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 272) ∨
      (288 ≤ d ∧ d + 16 ≤ 296) ∨ (312 ≤ d ∧ d + 16 ≤ 384)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) := fun {d} hd =>
    blockAtMem_frame (by have := H₃.frame; rwa [hW₁] at this) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Ar.lay.w_w (by omega) (by omega) (by decide)
  have sv₂ : SavedAt s₂.mem W s₀ := saved_mut Ar.lay Ar.data.w P₁.saved (nonceR_mut (D := D) (n := n) pf₂)
  have sv₃ : SavedAt s₃.mem W s₀ := saved_mut Ar.lay Ar.data.w sv₂ (hashR_mut (D := D) (n := n)
    (by have := H₃.frame; rwa [hW₁] at this))
  have nonce₁ : bytesAt s₁.mem N nl = bytesAt s₀.mem N nl := bytesAt_W Ar.nonce.w Ar.nonce.lt F₁
  refine ⟨H₃.env, F₁₂.trans F₃, by rw [H₃.rd, P₂.rd, rd₁], by rw [H₃.wr, P₂.wr, wr₁], sv₃, ?_, ?_, ?_, ?_, ?_,
    by have := H₃.sum; rwa [hW₁] at this⟩
  · rw [k₃ (d := ofsO) (by decide), ofs₂, hK₁, ctxCiph_W Ar.lay F₁ Ar.rounds, nonce₁]
  · rw [k₃ (d := o0O) (by decide), o0₂, hK₁, ctxCiph_W Ar.lay F₁ Ar.rounds, nonce₁]
  · rw [k₃ (d := ckO) (by decide), keep₂ (by decide) (by decide), P₁.ck]
  · rw [k₃ (d := ldO) (by decide), keep₂ (by decide) (by decide), P₁.ld, h3]
  · rw [k₃ (d := l0O) (by decide), keep₂ (by decide) (by decide), P₁.l0, h3]

/-- `body`'s frame misses a block of `W` outside the offset, the checksum,
`[96, 128)` and `[256, 272)`. -/
theorem body_keep {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (bodyR W D n) m m') {d : Nat}
    (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (128 ≤ d ∧ d + 16 ≤ 256) ∨ (272 ≤ d ∧ d + 16 ≤ 512)) :
    blockAtMem m' (W + BitVec.ofNat 64 d) = blockAtMem m (W + BitVec.ofNat 64 d) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- `tag d`'s frame misses the data. -/
theorem tag_data {W D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hd : d + 16 ≤ 512) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 d, 16⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩], (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hD.sub_right (Lay.wSub (by first | omega | (simp only [tmpO]; omega)))

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T` (in `r20`),
`tl` in `r19`, which the state may write. -/
theorem tagOut_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) {tl : Nat} (h1 : 1 ≤ tl)
    (h16 : tl ≤ 16) (h19 : V .r19 = BitVec.ofNat 64 tl) (hTw : Covers [⟨V .r20, tl⟩] s.wr)
    (hTW : (⟨V .r20, tl⟩ : Region).Disjoint ⟨V .r31, 2560⟩) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem (V .r20) (bytesAt s.mem (V .r31) tl) ∧
      (∀ r, r ∉ xpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hA : WP isa (.block [Impl.AesGcm.PPC64LE.mov .r3 .r31, Impl.AesGcm.PPC64LE.mov .r4 .r20,
      Impl.AesGcm.PPC64LE.mov .r5 .r19]) s fun s₃ =>
      s₃.gpr .r3 = V .r31 ∧ s₃.gpr .r4 = V .r20 ∧ s₃.gpr .r5 = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ :=
    cwp_or fun s₁ u₁ => cwp_or fun s₂ u₂ => cwp_or fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, BitVec.or_self, E.r31],
        by rw [u₃.other _ (by decide), u₂.gpr, BitVec.or_self, u₁.other _ (by decide), E.r20],
        by rw [u₃.gpr, BitVec.or_self, u₂.other _ (by decide), u₁.other _ (by decide), E.r19, h19],
        fun q a b c => by rw [u₃.other _ c, u₂.other _ b, u₁.other _ a],
        ⟨by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
          by rw [u₃.sp, u₂.sp, u₁.sp], by rw [u₃.lr, u₂.lr, u₁.lr]⟩⟩
  unfold tagOut
  refine WP.seq (WP.mono hA fun s₁ ⟨r3₁, r4₁, r5₁, g₁, k₁⟩ => ?_)
  refine WP.mono (Proof.AesGcm.PPC64LE.copyLoop_ok s₁ ⟨r3₁, r4₁, r5₁, h1, by omega,
    by rw [k₁.rd, k₁.wr]; exact covers_left (Proof.AesGcm.PPC64LE.covers_prefix E.perm.w (by omega)),
    by rw [k₁.wr]; exact hTw, (hTW.sub_right (Region.sub_prefix (by omega))).symm⟩) fun t ⟨mt, ot⟩ => ?_
  obtain ⟨rdt, wrt, spt, lrt⟩ := ot.keeps
  refine ⟨by rw [mt, k₁.mem], fun q hq => ?_, by rw [spt, k₁.sp], by rw [lrt, k₁.lr], by rw [rdt, k₁.rd],
    by rw [wrt, k₁.wr]⟩
  simp only [xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  rw [ot.other q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2, g₁ q hq.2.1 hq.2.2.1 hq.2.2.2.1]

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' {s₀ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (hTw : Covers [⟨T, tl⟩] s₀.wr) (hW : stackArg s₀ 2 = W)
    (hT : stackArg s₀ 0 = T) (htl : stackArg s₀ 1 = BitVec.ofNat 64 tl)
    (h3 : s₀.gpr .r3 = K) (h4 : s₀.gpr .r4 = BitVec.ofNat 64 R) (h5 : s₀.gpr .r5 = N)
    (h6 : s₀.gpr .r6 = BitVec.ofNat 64 nl) (h7 : s₀.gpr .r7 = A) (h8 : s₀.gpr .r8 = BitVec.ofNat 64 al)
    (h9 : s₀.gpr .r9 = D) (h10 : s₀.gpr .r10 = BitVec.ofNat 64 n) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Ocb.encryptWith (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) tl (bytesAt s₀.mem N nl)
        (bytesAt s₀.mem A al) (bytesAt s₀.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  have L₀ : Lay (s₀.gpr .r3) W := by rw [h3]; exact Ar.lay
  have hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr) := by rw [h3]; exact Ar.perm.k
  unfold «seal» front
  refine WP.seq (WP.seq (WP.mono (entry_ok L₀ Ar.perm.w hC hW hT Ar.args Ar.argsW) fun s₁ P₁ => ?_))
  have hW₁ : s₁.gpr .r31 = W := P₁.r31
  have hK₁ : s₁.gpr .r29 = K := P₁.r29.trans h3
  have hD₁ : s₁.gpr .r27 = D := P₁.r27.trans h9
  have h28 : s₁.gpr .r28 = BitVec.ofNat 64 R := P₁.r28.trans h4
  have h23 : s₁.gpr .r23 = BitVec.ofNat 64 n := P₁.r23.trans h10
  have L : Lay (s₁.gpr .r29) (s₁.gpr .r31) := by rw [hK₁, hW₁]; exact Ar.lay
  refine WP.assoc (WP.seq (WP.mono (preRest_wp Ar P₁ htl h3 h4 h5 h6 h7 h8) fun s₃ P₃ => ?_))
  have hD₃ : DBuf (s₁.gpr .r29) (s₁.gpr .r31) s₃ (s₁.gpr .r27) n := by
    rw [hK₁, hW₁, hD₁]; exact Ar.data.of_eq P₃.rd P₃.wr
  have c₃ : ctxCiph s₃.mem K R = ctxCiph s₀.mem K R := ctxCiph_W Ar.lay P₃.frame Ar.rounds
  have l₃ : ctxLstar s₃.mem K = ctxLstar s₀.mem K := ctxLstar_W Ar.lay P₃.frame
  have d₃ : bytesAt s₃.mem D n = bytesAt s₀.mem D n := bytesAt_W Ar.data.w Ar.data.lt P₃.frame
  refine WP.seq (WP.mono (bodySeal_ok L P₃.env Ar.rounds h28 h23 hD₃
    (O0 := Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)) (by rw [hW₁]; exact P₃.ofs)
    (by rw [hW₁]; exact P₃.o0) (by rw [hW₁]; exact P₃.ck) (by rw [hW₁, hK₁, P₃.l0, l₃])) fun s₄ B => ?_)
  have Bf : Frame (bodyR W D n) s₃.mem s₄.mem := by have := B.frame; rwa [hW₁, hD₁] at this
  have F₄ : Frame (mutR W D n) s₃.mem s₄.mem := bodyR_mut Bf
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s₀.mem K R := (ctxCiph_mut Ar.lay Ar.data.k F₄ Ar.rounds).trans c₃
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s₀.mem K) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) (bytesAt s₀.mem A al) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := sumO) (by decide), P₃.sum]
  -- The tag.
  refine WP.mono (tag_ok L B.env Ar.rounds h28 (.inl rfl)) fun s₅ T₅ => ?_
  have Tf : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 tagO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]
      s₄.mem s₅.mem := by have := T₅.frame; rwa [hW₁] at this
  have F₅ : Frame (mutR W D n) s₄.mem s₅.mem := tagR_mut (.inl (by decide)) Tf
  have sv₅ := saved_mut Ar.lay Ar.data.w (saved_mut Ar.lay Ar.data.w P₃.saved F₄) F₅
  -- The copy of the tag.
  have E₅ := T₅.env
  have hTd : (⟨s₁.gpr .r20, tl⟩ : Region).Disjoint ⟨s₁.gpr .r31, 2560⟩ := by rw [P₁.r20, hW₁]; exact Ar.tag.w
  refine WP.seq (WP.mono (tagOut_ok E₅ Ar.t1 Ar.t16 (P₁.r19.trans htl)
    (by rw [P₁.r20, T₅.wr, B.wr, P₃.wr]; exact hTw) hTd) fun s₆ ⟨m₆, g₆, sp₆, lr₆, rd₆, wr₆⟩ => ?_)
  have E₆ := E₅.others g₆ sp₆ rd₆ wr₆
  rw [P₁.r20, hW₁] at m₆
  have F₆ : Frame [⟨T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  have sv₆ : SavedAt s₆.mem W s₀ := sv₅.frame F₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (Ar.tag.w.sub_right (Lay.wSub (W := W) (d := 128) (n := 120) (by decide))).symm
  -- `restore`.
  refine WP.mono (Proof.AesGcm.PPC64LE.restore_ok (E₆.r31.trans hW₁)
    (by rw [rd₆, wr₆, T₅.rd, T₅.wr, B.rd, B.wr, P₃.rd, P₃.wr]; exact covers_left Ar.perm.w) sv₆
    (by rw [E₆.sp]) (fun r hr => by
      rw [E₆.fr r (by revert hr; revert r; decide), P₁.low r hr])) fun s₇ ⟨abi, m₇, _, _, _⟩ => ⟨abi, ?_⟩
  have hout := B.out
  rw [hK₁, hD₁, c₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [hW₁, hK₁, l₃] at hofs
  have hck := B.ck
  rw [hW₁, hD₁, d₃] at hck
  have hn := Ar.data.lt
  have ht := Ar.tag.lt
  have d₇ : bytesAt s₇.mem D n = bytesAt s₄.mem D n := by
    rw [m₇, Proof.Cmac.bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by omega)]
    exact Proof.Cmac.bytesAt_frame Tf (tag_data Ar.data.w (by decide)) (by omega)
  have tv := T₅.val
  rw [hW₁, hK₁, show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
  have t₇ : bytesAt s₇.mem T tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem W)).take tl := by
    rw [m₇, m₆, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) ht, length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, bytesAt_take_block _ _ Ar.t16]
  rw [Proof.Ocb.encryptWith_eq, d₇, hout, t₇, tv, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp {s : State} (h : sealPPC64LE.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  seal_wp' (sealArgs_of h) (covers_mem (by rw [h.2.1]; simp)) rfl rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.PPC64LE
