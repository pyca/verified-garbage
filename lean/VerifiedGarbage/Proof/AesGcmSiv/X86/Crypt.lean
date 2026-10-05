import VerifiedGarbage.Proof.AesGcmSiv.X86.Tag

/-!
# AES-GCM-SIV on x86: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. The counter block at
`W + 96` starts as the tag with the top bit of its last byte set
(`cryptHead_ok`); each block of the data is encrypted in place by
`vg_aes_ctr32` from a copy of it at `W + 112`, after which its first word is
incremented (`cryptBlock_ok`); the last bytes are XORed with the keystream
block, computed at `W + 224` (`cryptTail_ok`). `crypt_ok`: the data becomes
`ctr` of it (RFC 8452 §4). The pointer is in `esi` and the number of bytes
left at `W + nO`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Impl.AesGcm.X86 (at_ imm slot xorLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add slotv slotv_eq GcmImpl readW_writeW_off covers_left
  covers_off XorPre XorPost xorLoop_ok xorBytes length_bytesAt sub_beq32)

theorem ctr32_single (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb x : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem toBytes_xor (a b : Spec.Gcm.Block) :
    Spec.Gcm.toBytes (a ^^^ b) = Spec.Cmac.xor (Spec.Gcm.toBytes a) (Spec.Gcm.toBytes b) := by
  apply List.ext_getElem (by simp [Spec.Gcm.toBytes, Spec.Cmac.xor])
  intro i h₁ h₂
  simp [Spec.Gcm.toBytes, Spec.Cmac.xor, BitVec.extractLsb'_xor]

/-- What the counter block at `W + 96` holds before block `j`: the first
word of `icb` plus `j`, and the rest of `icb`. -/
structure CtrSt (W : Addr) (icb : List Byte) (j : Nat) (m : Mem) : Prop where
  word : m.readW (W + BitVec.ofNat 64 96) 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)
  rest : bytesAt m (W + BitVec.ofNat 64 100) 12 = icb.drop 4

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, add_ofNat_assoc, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega) (by omega) (by omega) _ (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega) (by omega)) hc

/-- What counter mode writes: the counter block and its copy, the bytes
left, the block at `W + 224`, `vg_aes_ctr32`'s working space, the data and
the stack below `SP`. -/
abbrev cryR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, ⟨w64 p.D, p.n⟩, stk p]

theorem inMut_cryR (p : Prm) : InMut p (cryR p) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact inMut_d p
  · exact inMut_stk p

/-- Byte `j` of the data, as a 64-bit address. -/
theorem Lay.dA {p : Prm} (L : Lay p) {j : Nat} (hj : j < p.n) : w64 (p.D + BitVec.ofNat 32 j) = w64 p.D + BitVec.ofNat 64 j :=
  w64_add (by have := L.dw; omega)

theorem Lay.dN {p : Prm} (L : Lay p) {j : Nat} (hj : j < p.n) : (p.D + BitVec.ofNat 32 j).toNat = p.D.toNat + j :=
  toNat_add32 (by have := L.dw; omega)

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * (j + 1))
  n : slotv t'.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * (j + 1))
  z : t'.zf = some (decide ((p.n - 16 * (j + 1)) / 16 = 0))
  ctr : CtrSt (w64 p.W) icb (j + 1) t'.mem
  data : bytesAt t'.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (cryR p) t.mem t'.mem

/-- The arguments of a block's call. -/
theorem blkArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat}
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) :
    ∃ t₁ : State, runBlock isa blockArgs t = some t₁ ∧ t₁.mem = copyMem t.mem (w64 p.W) ∧
      t₁.gpr .eax = p.W + BitVec.ofNat 32 512 ∧ t₁.gpr .ecx = BitVec.ofNat 32 p.R ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .ebx = p.D + BitVec.ofNat 32 (16 * j) ∧
      t₁.gpr .edi = BitVec.ofNat 32 1 ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.gpr .esi = t.gpr .esi ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have hR := E.slots.rounds
  simp only [slotv_eq, roundsO] at hR
  have hcp : ((((t.mem.writeW (w64 p.W + BitVec.ofNat 64 112) (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 116) (t.mem.readW (w64 p.W + BitVec.ofNat 64 100) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 120) (t.mem.readW (w64 p.W + BitVec.ofNat 64 104) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 124) (t.mem.readW (w64 p.W + BitVec.ofNat 64 108) 32)) = copyMem t.mem (w64 p.W) := by
    simp only [copyMem, Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]
  have rR : (copyMem t.mem (w64 p.W)).readW (w64 p.W + BitVec.ofNat 64 148) 32 = BitVec.ofNat 32 p.R := by
    rw [copyMem, Proof.Cmac.store4]
    simp (disch := decide) only [add_ofNat_assoc, Nat.reduceAdd, readW_writeW_off]
    exact hR
  refine ⟨_, by simp only [blockArgs, copy16]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hcp, rR], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hcp]
  · gregs [E.ebp]
  · gregs [rR]
  · gregs [E.ebp]
  · gregs [hsi]
  · gregs []
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals rfl

/-- The code after a block's call. -/
theorem blkPost_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * j)) :
    ∃ t' : State, runBlock isa blockNext t = some t' ∧
      t'.mem = (t.mem.writeW (w64 p.W + BitVec.ofNat 64 96)
        (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 + BitVec.ofNat 32 1)).writeW (w64 p.W + BitVec.ofNat 64 176)
        (BitVec.ofNat 32 (p.n - 16 * (j + 1))) ∧
      t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * (j + 1)) ∧
      t'.zf = some (decide ((p.n - 16 * (j + 1)) / 16 = 0)) ∧ t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hn' := L.n32
  simp only [slotv_eq, nO] at hn
  have e5 : BitVec.ofNat 32 (p.n - 16 * j) - BitVec.ofNat 32 16 = BitVec.ofNat 32 (p.n - 16 * (j + 1)) := by
    rw [ofNat_sub32 (by omega) (by omega), show p.n - 16 * j - 16 = p.n - 16 * (j + 1) by omega]
  have rn : (t.mem.writeW (w64 p.W + BitVec.ofNat 64 96) (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 +
      BitVec.ofNat 32 1)).readW (w64 p.W + BitVec.ofNat 64 176) 32 = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide), hn]
  refine ⟨_, by simp only [blockNext, wholeLeft]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, rn, e5], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · gmems [rn, e5]
  · gregs [hsi, add32_ofNat_assoc, Nat.mul_succ]
  · gmems [rn, e5, ofNat_lsr32 (show p.n - 16 * (j + 1) < 2 ^ 32 by omega)]
    rw [BitVec.and_self, show BitVec.ofNat 32 ((p.n - 16 * (j + 1)) / 16) =
      BitVec.ofNat 32 ((p.n - 16 * (j + 1)) / 16) - BitVec.ofNat 32 0 by simp, sub_beq32 (by omega) (by decide)]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

theorem cryptBlock_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {j : Nat}
    (hj : 16 * (j + 1) ≤ p.n) (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j))
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * j)) (C : CtrSt (w64 p.W) icb j t.mem)
    (hx : bytesAt t.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph) :
    WP isa (cryptBlock v.callees) t (BlockPost p ciph icb x j t) := by
  have hw := L.ww
  have hn' := L.n32
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, si₁, rd₁, wr₁⟩ := blkArgs_ok L E hsi
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact copyMem_frame _ _
  have E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inl (by decide)))
  have eQ : w64 (p.D + BitVec.ofNat 32 (16 * j)) = w64 p.D + BitVec.ofNat 64 (16 * j) := L.dA (by omega)
  have dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have hD : Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.D + BitVec.ofNat 32 (16 * j)) (16 * 1) := by
    refine ⟨?_, by rw [L.dN (by omega)]; omega, ?_, ?_, ?_, ?_⟩ <;> rw [eQ]
    · exact covers_off E₁.perm.d (by omega) (by omega)
    · rw [L.aW (by decide)]; exact (dQ.sub_right (Lay.wSub (show 512 + 240 ≤ 2816 by decide))).symm
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact L.bd.sub_right (Offset.sub_base _ (by omega))
  -- What the copy changed.
  have dD : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨w64 p.D, p.n⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hcb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁, copyMem_bytes, C.block]
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph := by
    rw [← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (Lay.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hx₁ : bytesAt t₁.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ dD (by omega), hx]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (callCtr_ok v L E₁ (keyS L E₁.perm) hD (by rw [eQ]; exact ⟨⟨w64 p.D, p.n⟩, by simp,
    Offset.sub_base _ (by omega)⟩) eax ecx edx ebx edi) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  simp only [eQ, Nat.mul_one] at fc hout
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    ctr32_single, List.cons.injEq, and_true] at hout
  rw [L.aW (by decide)] at hout
  have hb₂ : bytesAt t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁.mem (w64 p.D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 512) (16 * (p.R + 1))) =
        Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R from rfl, hc₁, hcb]
  have hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have hx₂ : bytesAt t₂.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x _ (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega)])
    rw [hxl]
    refine frame_outside fc (fun q hq => ?_) (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inl rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inr L.bd.symm
  -- What the first two pieces changed.
  have f₂' : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, stk p] t.mem t₂.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  have dC : ∀ {d k : Nat}, (96 ≤ d ∧ d + k ≤ 112 ∨ 176 ≤ d ∧ d + k ≤ 184) →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, stk p], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (by omega) (by omega) (by decide)
      · exact (dQ.sub_right (Lay.wSub (by omega))).symm
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.bw' (by omega)).symm
  have w₂ : t₂.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 = t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (.inl ⟨Nat.le_refl _, by decide⟩)) (by decide)
  have n₂ : slotv t₂.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [← hn]; exact f₂'.readW (Region.contains_self _ _) (dC (k := 4) (.inr ⟨Nat.le_refl _, by decide⟩)) (by decide)
  have r₂ : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 100) 12 = bytesAt t.mem (w64 p.W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.X86.bytesAt_frame f₂' (dC (.inl ⟨by decide, by decide⟩)) (by decide)
  have si₂ : t₂.gpr .esi = p.D + BitVec.ofNat 32 (16 * j) := by rw [P.saved _ (by decide), si₁, hsi]
  obtain ⟨t₃, run₃, hm₃, si₃, z₃, bp₃, sp₃, rd₃, wr₃⟩ := blkPost_ok L P.env hj si₂ n₂
  have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 4⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₂.mem t₃.mem := by
    rw [hm₃]
    have g : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 4⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₂.mem
        (t₂.mem.writeW (w64 p.W + BitVec.ofNat 64 96) (t₂.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 +
          BitVec.ofNat 32 1)) := (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
    exact g.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
  have fm₃ : Frame (cryR p) t₂.mem t₃.mem := f₃.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have E₃ : Env p t₃ := P.env.mut L bp₃ sp₃ rd₃ wr₃ (frame_toMut fm₃ (inMut_cryR p))
  have f₂ : Frame (cryR p) t.mem t₂.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine WP.of_runBlock ⟨t₃, run₃, E₃, by rw [rd₃, P.rd, rd₁], by rw [wr₃, P.wr, wr₁], si₃,
    by rw [slotv_eq, hm₃, Mem.readW_writeW_self32], z₃, ⟨?_, ?_⟩, ?_, f₂.trans fm₃⟩
  · rw [hm₃, readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, w₂, C.word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), r₂, C.rest]
  · rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> exact L.d_w' (by decide)) (Nat.le_of_lt (by omega)), hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega]

/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {p : Prm} (L : Lay p) :
    ∀ r ∈ cryR p, (⟨w64 p.W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm
  · exact (L.bw' (by decide)).symm

theorem ciph_cryR {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (cryR p) m m') :
    Spec.GcmSiv.ctxCiph m' (w64 p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph m (w64 p.W + BitVec.ofNat 64 512) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (key_cryR L r hr).sub_left (Region.sub_prefix L.rounds_le))
    (by have := L.rounds_le; omega)]

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * b)
  n : slotv t'.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * b)
  ctr : CtrSt (w64 p.W) icb b t'.mem
  data : bytesAt t'.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (cryR p) t.mem t'.mem

theorem blocks_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) (hb1 : 1 ≤ p.n / 16)
    (hsi : t.gpr .esi = p.D) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 p.n)
    (C : CtrSt (w64 p.W) icb 0 t.mem) (hx : bytesAt t.mem (w64 p.D) p.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph) :
    WP isa (.loop (cryptBlock v.callees) .ne) t (BlocksPost p ciph icb x (p.n / 16) t) := by
  refine WP.loop (M := isa) (body := cryptBlock v.callees) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BlocksPost p ciph icb x j t t') ?_
    (p.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨E, rfl, rfl, by rw [hsi, Nat.mul_zero, BitVec.add_zero], by rw [hn, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro k t' ⟨j, rfl, hj, P⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph := by
    rw [ciph_cryR L P.frame, hc]
  refine WP.mono (cryptBlock_ok v L P.env hxl (j := j) (by omega) P.esi P.n P.ctr P.data hc') fun t'' Q => ?_
  have P' : BlocksPost p ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.esi, Q.n, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  have ev := eval_ne Q.z
  by_cases he : j + 1 = p.n / 16
  · left
    exact ⟨ev.trans (by simp; omega), he ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, P'⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  data : bytesAt t'.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x p.n
  frame : Frame (cryR p) t.mem t'.mem

theorem cryptTail_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {b r : Nat}
    (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * b))
    (hnr : slotv t.mem p.W nO = BitVec.ofNat 32 r) (C : CtrSt (w64 p.W) icb b t.mem)
    (hx : bytesAt t.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph) :
    WP isa (cryptTail v.callees) t (TailPost p ciph icb x t) := by
  have hn' := L.n32
  have hdw := L.dw
  have hw := L.ww
  refine WP.seq (WP.mono (tag_ok v L E (o := 224) (by decide)) fun t₂ T => ?_)
  have fT := T.frame
  have dT : ∀ q ∈ tagWr p 224, (⟨w64 p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  have hx₂ : bytesAt t₂.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.AesGcm.X86.bytesAt_frame fT dT (by omega), hx]
  have hks : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  have hnr₂ : slotv t₂.mem p.W nO = BitVec.ofNat 32 r := by
    rw [← hnr]
    exact fT.readW (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  simp only [slotv_eq, nO] at hnr₂
  obtain ⟨t₃, run₃, dx₃, di₃, cx₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [.mov .edx (.reg .ebp), .alu .add .edx (imm bO), .mov .edi (.reg .esi), .mov .ecx (slot nO)] t₂ = some t₃ ∧
      t₃.gpr .edx = p.W + BitVec.ofNat 32 224 ∧ t₃.gpr .edi = p.D + BitVec.ofNat 32 (16 * b) ∧
      t₃.gpr .ecx = BitVec.ofNat 32 r ∧ t₃.mem = t₂.mem ∧ t₃.gpr .ebp = p.W ∧ t₃.gpr .esp = p.SP ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr :=
    ⟨_, by grun [T.env.ebp, L.aW, T.env.perm.wR, hnr₂], by gregs [T.env.ebp], by gregs [T.esi, hsi],
      by gregs [hnr₂], by gmems [], by gregs [T.env.ebp], by gregs [T.env.esp], by gmems [], by gmems []⟩
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have eD := L.dA (j := 16 * b) (by omega)
  have dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have lp : XorPre t₃ (p.W + BitVec.ofNat 32 224) (p.D + BitVec.ofNat 32 (16 * b)) r := by
    refine ⟨dx₃, di₃, cx₃, by omega, by omega, by rw [L.nW (by decide)]; omega, by rw [L.dN (by omega)]; omega,
      ?_, ?_, ?_⟩
    · rw [rd₃, wr₃, L.aW (by decide)]
      exact covers_prefix (T.env.perm.wCR (show 224 + 16 ≤ 2816 by decide)) (by omega)
    · rw [wr₃, eD]; exact covers_off T.env.perm.d (by omega) (by omega)
    · rw [eD, L.aW (by decide)]
      exact ((dQ.sub_right (Lay.wSub (show 224 + 16 ≤ 2816 by decide))).sub_right (Region.sub_prefix (by omega))).symm
  refine WP.mono (xorLoop_ok t₃ lp) fun t₄ O => ?_
  have hm₄ := O.mem
  rw [m₃, eD, L.aW (by decide)] at hm₄
  have hl : (xorBytes t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) (w64 p.W + BitVec.ofNat 64 224) r).length = r := by
    simp [xorBytes, Proof.Cmac.bytesAt_length]
  have fw := Proof.AesGcm.X86.writeBytes_frame' t₂.mem (q := w64 p.D + BitVec.ofNat 64 (16 * b)) hl
  rw [← hm₄] at fw
  have hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have fwm : Frame (mutR p) t₃.mem t₄.mem := by
    rw [m₃]
    exact frame_toMut fw fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩
  have E₄ : Env p t₄ := T.env.mut L
    (by rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide), bp₃])
    (by rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide), sp₃])
    (by rw [O.rd, rd₃]) (by rw [O.wr, wr₃]) (by rw [← m₃]; exact fwm)
  refine ⟨E₄, by rw [O.rd, rd₃, T.rd], by rw [O.wr, wr₃, T.wr], ?_, ?_⟩
  · have hb' : bytesAt t₄.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      have e := Proof.AesGcm.X86.bytesAt_writeBytes_self t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) (w64 p.W + BitVec.ofNat 64 224) r) (by omega)
      rw [hl] at e
      have hs := Proof.Cmac.bytesAt_add t₂.mem (w64 p.W + BitVec.ofNat 64 224) r (16 - r)
      rw [show r + (16 - r) = 16 by omega, hks] at hs
      rw [hm₄, e, xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x _ (i := b) (n := r) (by omega) hk (by rw [hxl]; exact hx₂)
      (frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; omega) (by omega)) hb'
    rwa [hxl, ← hn] at this
  · refine (fT.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR p) t.mem t'.mem
  data : bytesAt t'.mem (w64 p.D) p.n =
    Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) (bytesAt t.mem (w64 p.D) p.n)

/-- The memory `cryptHead` leaves: the counter block from the tag, and the
data's length as the bytes left. -/
def headMem (m : Mem) (W : Addr) (n : Nat) : Mem :=
  (Proof.Cmac.store4 m (W + BitVec.ofNat 64 96) (m.readW (W + BitVec.ofNat 64 0) 32)
    (m.readW (W + BitVec.ofNat 64 4) 32) (m.readW (W + BitVec.ofNat 64 8) 32)
    (m.readW (W + BitVec.ofNat 64 12) 32 ||| 0x80000000#32)).writeW (W + BitVec.ofNat 64 176) (BitVec.ofNat 32 n)

/-- The start of `crypt`: the counter block from the tag, and the data as
the bytes to encrypt. -/
theorem cryptHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁ : State, runBlock isa cryptHead t = some t₁ ∧ t₁.mem = headMem t.mem (w64 p.W) p.n ∧
      t₁.gpr .esi = p.D ∧ t₁.zf = some (decide (p.n / 16 = 0)) ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have hD := E.slots.data
  have hn := E.slots.len
  simp only [slotv_eq, dataO, lenO] at hD hn
  refine ⟨_, by simp only [cryptHead, onStr, wholeLeft]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · gmems [headMem, Proof.Cmac.store4, add_ofNat_assoc, hD, hn]
  · gmems [hD, Proof.Cmac.store4, add_ofNat_assoc]
  · gmems [hD, hn, ofNat_lsr32 L.n32, Proof.Cmac.store4, add_ofNat_assoc]
    rw [BitVec.and_self, show BitVec.ofNat 32 (p.n / 16) = BitVec.ofNat 32 (p.n / 16) - BitVec.ofNat 32 0 by simp,
      sub_beq32 (by have := L.n32; omega) (by decide)]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

/-- What `cryptHead` leaves, from `t`. -/
structure CStart (p : Prm) (t t₁ : State) : Prop where
  env : Env p t₁
  rd : t₁.rd = t.rd
  wr : t₁.wr = t.wr
  esi : t₁.gpr .esi = p.D
  z : t₁.zf = some (decide (p.n / 16 = 0))
  n : slotv t₁.mem p.W nO = BitVec.ofNat 32 p.n
  ctr : CtrSt (w64 p.W) (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) 0 t₁.mem
  data : bytesAt t₁.mem (w64 p.D) p.n = bytesAt t.mem (w64 p.D) p.n
  ciph : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
    Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R
  frame : Frame (cryR p) t.mem t₁.mem

theorem cryptStart_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁, runBlock isa cryptHead t = some t₁ ∧ CStart p t t₁ := by
  have hw := L.ww
  have hn := L.n32
  obtain ⟨t₁, run₁, hm₁, si₁, z₁, bp₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem (w64 p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₁.mem := by
    rw [hm₁, headMem]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
  have dD : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩],
      (⟨w64 p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.d_w' (by decide)
  have hx₁ : bytesAt t₁.mem (w64 p.D) p.n = bytesAt t.mem (w64 p.D) p.n :=
    Proof.AesGcm.X86.bytesAt_frame f₁ dD (by omega)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;>
        exact (Lay.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hcb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 96) 16 =
      bytesAt (Proof.Cmac.store4 t.mem (w64 p.W + BitVec.ofNat 64 96) (t.mem.readW (w64 p.W + BitVec.ofNat 64 0) 32)
        (t.mem.readW (w64 p.W + BitVec.ofNat 64 4) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 8) 32)
        (t.mem.readW (w64 p.W + BitVec.ofNat 64 12) 32 ||| 0x80000000#32)) (w64 p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, headMem]
    exact Proof.AesGcm.X86.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  have hicb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 96) 16 =
      Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16) := by
    rw [hcb, Proof.Cmac.bytesAt_store4, BitVec.add_zero, ← GcmSiv.Words32.initialCounter_words,
      Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
      ← Proof.Cmac.bytesAt_split4]
  have h4 := Proof.Cmac.bytesAt_add t₁.mem (w64 p.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, add_ofNat_assoc] at h4
  have C₀ : CtrSt (w64 p.W) (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  have fm₁ : Frame (cryR p) t.mem t₁.mem := f₁.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut fm₁ (inMut_cryR p))
  have n₁ : slotv t₁.mem p.W nO = BitVec.ofNat 32 p.n := by rw [slotv_eq, hm₁, headMem, Mem.readW_writeW_self32]
  exact ⟨t₁, run₁, E₁, rd₁, wr₁, si₁, z₁, n₁, C₀, hx₁, hc₁, fm₁⟩

theorem crypt_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (crypt v.callees) t (CryptPost p t) := by
  have hw := L.ww
  have hn := L.n32
  obtain ⟨t₁, run₁, ⟨E₁, rd₁, wr₁, si₁, z₁, n₁, C₀, hx₁, hc₁, fm₁⟩⟩ := cryptStart_ok L E
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem (w64 p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The whole blocks.
  have hmid : WP isa (.ite .e (.block []) (.loop (cryptBlock v.callees) .ne)) t₁
      (BlocksPost p (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) (bytesAt t.mem (w64 p.D) p.n) (p.n / 16) t₁) := by
    refine WP.ite (decide (p.n / 16 = 0)) (eval_e z₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨E₁, rfl, rfl, by rw [si₁, Nat.mul_zero, BitVec.add_zero], by rw [n₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact blocks_ok v L E₁ hxl (by omega) si₁ n₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have n₂ : slotv t₂.mem p.W nO = BitVec.ofNat 32 (p.n % 16) := by rw [B.n]; congr 1; omega
  obtain ⟨t₃, run₃, z₃, E₃, si₃, m₃, rd₃, wr₃⟩ := anyLeft_ok L B.env (by omega) n₂
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  refine WP.ite (decide (p.n % 16 = 0)) (eval_e z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨E₃, by rw [rd₃, B.rd, rd₁], by rw [wr₃, B.wr, wr₁], by rw [m₃]; exact fm₁.trans B.frame, ?_⟩
    rw [m₃, B.data, show 16 * (p.n / 16) = p.n by omega, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : p.n % 16 ≠ 0 := by simpa using hf
    have hc₂ : Spec.GcmSiv.ctxCiph t₃.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
        Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R := by
      rw [m₃, ciph_cryR L B.frame, hc₁]
    refine WP.mono (cryptTail_ok v L E₃ hxl (b := p.n / 16) (r := p.n % 16) (by omega) (by omega) (by omega)
      (by rw [si₃, B.esi]) (by rw [slotv_eq, m₃]; exact n₂) (m₃ ▸ B.ctr) (by rw [m₃]; exact B.data) hc₂)
      fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, rd₃, B.rd, rd₁], by rw [T.wr, wr₃, B.wr, wr₁],
      (fm₁.trans (m₃ ▸ B.frame)).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.X86
