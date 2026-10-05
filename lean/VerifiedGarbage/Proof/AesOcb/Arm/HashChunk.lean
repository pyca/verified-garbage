import VerifiedGarbage.Proof.AesOcb.Arm.HashFill
import VerifiedGarbage.Proof.AesOcb.Arm.Mut

/-!
# AES-OCB on ARMv7: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`), `r4`
points at block `j`, `r6` is `j + 1` and `r7` is `m − j`. `hashChunk` takes
`c = min(16, m − j)` blocks: fills the buffer with each block XORed with its
offset (`fill_ok`), enciphers the buffer, adds it to the sum (`sum_ok`), and
leaves `HInv` at `j + c` (`hashChunk_ok`), as on AArch64
(`Proof.AesOcb.AArch64.hashChunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0 dec32 z_dec mem_store gpr_store rd_store wr_store
  sp_store)

/-- The associated data in the memory `m`. -/
abbrev aadOf (p : Prm) (m : Mem) : List Byte := bytesAt m (State.addr p.A) p.al

/-- `ENCIPHER(K, ·)` of the key context in the memory `m`. -/
abbrev ciphOf (p : Prm) (m : Mem) : Cipher := Spec.Ocb.aesWith p.R (sched p m)

/-- `L_*` of the key context in the memory `m`. -/
abbrev lstarOf (p : Prm) (m : Mem) : Block := Spec.Ocb.ctxLstar m (State.addr p.K)

/-- What `HASH` writes: the sum, `L_{ntz(i)}`, its offset and the count of a
chunk, the buffer and the working space of the functions called, and the
stack below `SP`. -/
abbrev hashR (p : Prm) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 48, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 192, 24⟩, ⟨State.addr p.W + BitVec.ofNat 64 256, 2304⟩,
   Proof.AesGcm.Arm.below p.SP]

theorem hashR_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (hashR p) m m') : Frame (mutR p) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact below_mut L

/-- A part of one of the parts of `W` that `HASH` writes. -/
theorem w_hash {p : Prm} {a l b k : Nat} (hb : (⟨State.addr p.W + BitVec.ofNat 64 b, k⟩ : Region) ∈ hashR p)
    (h : b ≤ a ∧ a + l ≤ b + k) (_hk : b + k ≤ 2560) :
    ∃ r' ∈ hashR p, Region.Sub ⟨State.addr p.W + BitVec.ofNat 64 a, l⟩ r' :=
  ⟨_, hb, Offset.sub _ h.1 (by omega)⟩

/-- What holds of `HASH` after `j` of the whole blocks of the associated data,
from the state `t₀` at its start. -/
structure HInv (p : Prm) (t₀ t : State) (j : Nat) : Prop where
  env : Env p t
  frame : Frame (hashR p) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  le : j ≤ p.al / 16
  sum : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    hsum (ciphOf p t₀.mem) (lstarOf p t₀.mem) (aadOf p t₀.mem) j
  oh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 (lstarOf p t₀.mem) j
  r4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * j)
  r6 : t.gpr .r6 = BitVec.ofNat 32 (j + 1)
  r7 : t.gpr .r7 = BitVec.ofNat 32 (p.al / 16 - j)
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p t₀.mem) 0

/-- Block `i` of the associated data, in a state after `t₀`. -/
theorem aadBlk {p : Prm} (L : Lay p) {t₀ : State} {m : Mem} (h : Frame (mutR p) t₀.mem m) {i : Nat}
    (hi : i < p.al / 16) :
    blockAtMem m (State.addr p.A + BitVec.ofNat 64 (16 * i)) = blockAt (aadOf p t₀.mem) i := by
  rw [Proof.Ocb.blockAt_bytesAt _ _ (by omega), aadBlk_mut L h (by omega)]

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (p : Prm) (t₀ : State) (j c : Nat) (t : State) (i : Nat) : Prop where
  env : Env p t
  frame : Frame (hashR p) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i))
  r6 : t.gpr .r6 = BitVec.ofNat 32 (j + i + 1)
  r8 : t.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (c - i)
  r7 : t.gpr .r7 = BitVec.ofNat 32 (p.al / 16 - j - c)
  oh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 (lstarOf p t₀.mem) (j + i)
  buf : ∀ k < i, blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k)) =
    blockAt (aadOf p t₀.mem) (j + k) ^^^ offAt 0 (lstarOf p t₀.mem) (j + k + 1)
  sum : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    hsum (ciphOf p t₀.mem) (lstarOf p t₀.mem) (aadOf p t₀.mem) j
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p t₀.mem) 0
  cnt : t.mem.readW (State.addr p.W + BitVec.ofNat 64 cnO) 32 = BitVec.ofNat 32 c

theorem fill_step {p : Prm} (L : Lay p) {t₀ : State} {j c : Nat} (hc : c ≤ 16) (hjc : j + c ≤ p.al / 16)
    {t : State} {i : Nat} (hi : i < c) (F : FillInv p t₀ j c t i) :
    WP isa hashFill t fun t' => FillInv p t₀ j c t' (i + 1) ∧ t'.z = decide (i + 1 = c) := by
  refine WP.mono (hashFill_ok L F.env hi hc (by omega) F.r6 F.r4 F.r8 F.r5 F.l0 F.oh) fun t' P => ?_
  have hfr : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩], ∃ r' ∈ hashR p, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact w_hash (b := 96) (k := 16) (by simp) (by decide) (by decide)
    · exact w_hash (b := 192) (k := 24) (by simp) (by decide) (by decide)
    · exact w_hash (b := 256) (k := 2304) (by simp) ⟨by simp only [bufO]; omega, by simp only [bufO]; omega⟩
        (by decide)
  have kept : ∀ {d k : Nat}, d + k ≤ 2560 →
      (∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩,
        ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩],
        (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r) →
      bytesAt t'.mem (State.addr p.W + BitVec.ofNat 64 d) k = bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 d) k :=
    fun hd h => Proof.Cmac.bytesAt_frame P.frame h (by omega)
  have kblk : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ lO ∨ lO + 16 ≤ d) → (d + 16 ≤ ohO ∨ ohO + 16 ≤ d) →
      (d + 16 ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) →
      blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd h₁ h₂ h₃ => by
      unfold blockAtMem
      rw [kept hd (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.w_w h₁ hd (by decide)
        · exact L.w_w h₂ hd (by decide)
        · exact L.w_w h₃ hd (by simp only [bufO]; omega))]
  refine ⟨⟨F.env.of_others P.gpr P.sp P.rd P.wr, F.frame.trans (P.frame.sub hfr), by rw [P.rd, F.rd],
    by rw [P.wr, F.wr], by rw [P.r4]; congr 2, by rw [P.r6]; congr 1, P.r8, P.r5,
    by rw [P.gpr _ (by decide), F.r7], by rw [P.oh]; rfl, fun k hk => ?_, ?_, ?_, ?_⟩, P.z⟩
  · rcases (show k < i ∨ k = i by omega) with hk | rfl
    · rw [kblk (by simp only [bufO]; omega) (.inr (by simp only [lO, bufO]; omega))
        (.inr (by simp only [ohO, bufO]; omega)) (.inl (by omega)), F.buf k hk]
    · rw [P.buf, aadBlk L (hashR_mut L F.frame) (by omega)]
  · rw [kblk (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by simp only [sumO, bufO]; omega)), F.sum]
  · rw [kblk (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by simp only [l0O, bufO]; omega)), F.l0]
  · rw [P.frame.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 cnO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by simp only [cnO, bufO]; omega)) (by decide) (by simp only [bufO]; omega)) (by decide),
      F.cnt]

theorem fill_ok {p : Prm} (L : Lay p) {t₀ : State} {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 16)
    (hjc : j + c ≤ p.al / 16) {t : State} (F : FillInv p t₀ j c t 0) :
    WP isa (.loop hashFill .ne) t fun t' => FillInv p t₀ j c t' c := by
  refine WP.loop (M := isa) (fun k t' => ∃ i, k = c - i ∧ i < c ∧ FillInv p t₀ j c t' i) ?_ (c - 0) t
    ⟨0, rfl, hc0, F⟩
  rintro k t' ⟨i, rfl, hi, Fi⟩
  refine WP.mono (fill_step L hc hjc hi Fi) fun t'' ⟨F', z⟩ => ?_
  by_cases h : i + 1 = c
  · left
    refine ⟨(eval_ne' z).trans (by simp [h]), ?_⟩
    subst h; exact F'
  · right
    exact ⟨(eval_ne' z).trans (by simp [h]), c - (i + 1), by omega, i + 1, rfl, by omega, F'⟩

/-! ## Adding the buffer to the sum -/

/-- The sum loop after `k` of the `c` enciphered blocks of a chunk from block
`j`. -/
structure SumInv (p : Prm) (t₀ : State) (j c : Nat) (t : State) (k : Nat) : Prop where
  env : Env p t
  frame : Frame (hashR p) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + c))
  r6 : t.gpr .r6 = BitVec.ofNat 32 (j + c + 1)
  r8 : t.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * k)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (c - k)
  r7 : t.gpr .r7 = BitVec.ofNat 32 (p.al / 16 - j - c)
  oh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 (lstarOf p t₀.mem) (j + c)
  buf : ∀ k' < c, blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k')) =
    ciphOf p t₀.mem (blockAt (aadOf p t₀.mem) (j + k') ^^^ offAt 0 (lstarOf p t₀.mem) (j + k' + 1))
  sum : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    hsum (ciphOf p t₀.mem) (lstarOf p t₀.mem) (aadOf p t₀.mem) (j + k)
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p t₀.mem) 0

theorem sum_step {p : Prm} (L : Lay p) {t₀ : State} {j c : Nat} (hc : c ≤ 16)
    {t : State} {k : Nat} (hk : k < c) (S : SumInv p t₀ j c t k) :
    WP isa (.block (xorB .r11 .r8 .r11 sumO 0 sumO ++ [Impl.AesGcm.Arm.addI .r8 .r8 16, .subs .r5 .r5 (Impl.AesGcm.Arm.imm 1)]))
      t fun t' => SumInv p t₀ j c t' (k + 1) ∧ t'.z = decide (k + 1 = c) := by
  have fw := L.ww
  have eB : State.addr (p.W + BitVec.ofNat 32 (bufO + 16 * k)) = State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k) :=
    L.wA (by simp only [bufO]; omega)
  refine WP.block_append (WP.mono (xorB_wp (s := t) (pb := .r11) (qb := .r8) (cb := .r11) (pd := sumO) (qd := 0)
    (cd := sumO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [S.env.r11]; simp only [sumO]; omega) (by rw [S.r8, L.wN (by simp only [bufO]; omega)]; simp only [bufO]; omega)
    (by rw [S.env.r11]; simp only [sumO]; omega) (by rw [S.env.r11]; exact S.env.perm.wCR (by decide))
    (by rw [S.r8, eB, BitVec.add_zero]; exact S.env.perm.wCR (by simp only [bufO]; omega))
    (by rw [S.env.r11]; exact S.env.perm.wC (by decide))) fun t₁ R₁ => ?_)
  rw [S.env.r11, S.r8, eB, BitVec.add_zero] at R₁
  have dSB : (⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint
      ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k), 16⟩ :=
    L.w_w (.inl (by simp only [sumO, bufO]; omega)) (by decide) (by simp only [bufO]; omega)
  have r5₁ : t₁.gpr .r5 = BitVec.ofNat 32 (c - k) := by rw [R₁.gpr _ (by decide), S.r5]
  have r8₁ : t₁.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * k) := by rw [R₁.gpr _ (by decide), S.r8]
  refine WP.of_runBlock ⟨_, by orun [r5₁, r8₁], ?_⟩
  have fr : Frame [⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have kblk : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ sumO ∨ sumO + 16 ≤ d) →
      blockAtMem t₁.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd h => blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w h hd (by decide)
  refine ⟨⟨S.env.of_others (rs := [.r0, .r1, .r5, .r8]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, hr.2.2.1, hr.2.2.2, ↓reduceIte]
      exact R₁.gpr r (by simp [hr.1, hr.2.1])) (by simp [sp_setReg, Proof.AesGcm.Arm.sp_subFlags, R₁.sp])
      (by simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, R₁.rd]) (by simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, R₁.wr]),
    ?_, by simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, R₁.rd, S.rd], by simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, R₁.wr, S.wr],
    by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, R₁.gpr .r4 (by decide), S.r4],
    by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, R₁.gpr .r6 (by decide), S.r6], ?_, ?_,
    by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, R₁.gpr .r7 (by decide), S.r7], ?_, fun k' hk' => ?_, ?_, ?_⟩,
    ?_⟩
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    exact S.frame.trans (fr.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact w_hash (b := 48) (k := 16) (by simp) (by decide) (by decide))
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    congr 2
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, dec32 hk (by omega)]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kblk (by decide) (.inr (by decide)), S.oh]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kblk (by simp only [bufO]; omega) (.inr (by simp only [sumO, bufO]; omega)), S.buf k' hk']
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [R₁.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint dSB), S.sum, S.buf k hk]
    rfl
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kblk (by decide) (.inr (by decide)), S.l0]
  · simp only [z_setReg, z_subFlags, dec32 hk (by omega), z_dec hk (by omega)]

theorem sum_ok {p : Prm} (L : Lay p) {t₀ : State} {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 16) {t : State}
    (S : SumInv p t₀ j c t 0) : WP isa hashSum t fun t' => SumInv p t₀ j c t' c := by
  refine WP.loop (M := isa) (fun k t' => ∃ i, k = c - i ∧ i < c ∧ SumInv p t₀ j c t' i) ?_ (c - 0) t
    ⟨0, rfl, hc0, S⟩
  rintro k t' ⟨i, rfl, hi, Si⟩
  refine WP.mono (sum_step L hc hi Si) fun t'' ⟨S', z⟩ => ?_
  by_cases h : i + 1 = c
  · left
    refine ⟨(eval_ne' z).trans (by simp [h]), ?_⟩
    subst h; exact S'
  · right
    exact ⟨(eval_ne' z).trans (by simp [h]), c - (i + 1), by omega, i + 1, rfl, by omega, S'⟩

/-! ## The chunk -/

/-- The start of a chunk of `c` blocks from block `j`, once `c` is in `r5`:
`c` saved at `W + cnO`, the blocks left in `r7` and the buffer in `r8`. -/
theorem chunkHead_ok {p : Prm} (L : Lay p) {t₀ : State} {t : State} {j c : Nat}
    (H : HInv p t₀ t j) (_hc : c ≤ 16) (hjc : j + c ≤ p.al / 16)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 c) :
    WP isa (.block [.str .r5 .r11 cnO, .dp .sub .r7 .r7 (.reg .r5), Impl.AesGcm.Arm.addI .r8 .r11 bufO]) t fun t' => FillInv p t₀ j c t' 0 := by
  have fw := L.ww
  have al32 := L.al_lt
  have E := H.env
  have eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  have wC : InRegions t.wr (State.addr p.W + BitVec.ofNat 64 212) 4 := E.perm.wW (by decide)
  have kblk0 : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ cnO ∨ cnO + 4 ≤ d) → ∀ m : Mem, ∀ v : BitVec 32,
      blockAtMem (m.writeW (State.addr p.W + BitVec.ofNat 64 212) v) (State.addr p.W + BitVec.ofNat 64 d) =
        blockAtMem m (State.addr p.W + BitVec.ofNat 64 d) := fun hd h m v =>
    blockAtMem_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.w_w h hd (by decide)
  refine WP.of_runBlock ⟨_, by orun [E.r11, h5, eC, wC, H.r7], ?_⟩
  refine ⟨H.env.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl), ?_, by simp [rd_setReg, rd_store, H.rd],
    by simp [wr_setReg, wr_store, H.wr], by simp [gpr_setReg, gpr_store, H.r4], by simp [gpr_setReg, gpr_store, H.r6], ?_,
    by simp [gpr_setReg, gpr_store, h5], ?_,
    ?_, fun k hk => absurd hk (Nat.not_lt_zero _), ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store]
    exact H.frame.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact w_hash (b := 192) (k := 24) (by simp) (by decide) (by decide))
  · simp [gpr_setReg, gpr_store, E.r11, bufO]
  · simp only [gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, H.r7, h5]
    rw [Offset.ofNat_sub_ofNat (by omega)]
  · simp only [mem_setReg, mem_store]; rw [kblk0 (by decide) (.inl (by decide)), H.oh]; simp
  · simp only [mem_setReg, mem_store]; rw [kblk0 (by decide) (.inl (by decide)), H.sum]
  · simp only [mem_setReg, mem_store]; rw [kblk0 (by decide) (.inl (by decide)), H.l0]
  · simp only [mem_setReg, mem_store, cnO, Mem.readW_writeW_self32]

/-- The state at the chunk's call. -/
abbrev chunkCallSt (p : Prm) (c : Nat) (t : State) : State :=
  ((((t.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12 (p.W + BitVec.ofNat 32 scrO)).setReg .r2
    (p.W + BitVec.ofNat 32 bufO)).setReg .r3 (BitVec.ofNat 32 c)

/-- The arguments of the chunk's call. -/
theorem chunkArgs_run {p : Prm} (L : Lay p) {t₀ t : State} {j c : Nat} (F : FillInv p t₀ j c t c) :
    runBlock isa (callArgs ++ [Impl.AesGcm.Arm.addI .r2 .r11 bufO, .ldr .r3 .r11 cnO]) t =
      some (chunkCallSt p c t) := by
  have E₂ := F.env
  have eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  have rC : InRegions (t.rd ++ t.wr) (State.addr p.W + BitVec.ofNat 64 212) 4 := E₂.perm.wR (by decide)
  have cnt : t.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := F.cnt
  orun [callArgs, E₂.r9, E₂.r10, E₂.r11, eC, rC, cnt]

/-- The chunk's call, set up. -/
theorem chunkCall_blk {p : Prm} (L : Lay p) {t₀ t : State} {j c : Nat} (F : FillInv p t₀ j c t c) (hc : c ≤ 16) :
    BlkCall (chunkCallSt p c t) p.K (p.W + BitVec.ofNat 32 bufO) (p.W + BitVec.ofNat 32 scrO) p.R c ∧
      Env p (chunkCallSt p c t) := by
  have fw := L.ww
  have E₂ := F.env
  have eB : State.addr (p.W + BitVec.ofNat 32 bufO) = State.addr p.W + BitVec.ofNat 64 bufO := L.wA (by decide)
  have E' : Env p (chunkCallSt p c t) :=
    E₂.of_others (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac) (by rfl) (by rfl) (by rfl)
  exact ⟨blkCall_of L E' (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by decide)]; simp only [bufO]; omega)
      (by rw [eB]; exact E₂.perm.wC (by simp only [bufO]; omega)) (by rw [eB]; exact L.k_w' (by simp only [bufO]; omega))
      (by rw [eB]; exact L.w_w (.inl (by simp only [scrO, bufO]; omega)) (by simp only [bufO]; omega) (by decide))
      (by rw [eB]; exact L.bw' (by simp only [bufO]; omega)), E'⟩

/-- The rest of a chunk, from its call. -/
theorem chunkTail_ok {p : Prm} (L : Lay p) {t₀ t₂ : State} {j c : Nat} (F : FillInv p t₀ j c t₂ c)
    (hc0 : 0 < c) (hc : c ≤ 16) (hjc : j + c ≤ p.al / 16) :
    WP isa (.seq encFrame
      (.seq (.block [Impl.AesGcm.Arm.addI .r8 .r11 bufO, .ldr .r5 .r11 cnO])
      (.seq hashSum (.block [.cmp .r7 (Impl.AesGcm.Arm.imm 0)]))))
      (chunkCallSt p c t₂) fun t' => HInv p t₀ t' (j + c) ∧ t'.z = decide (p.al / 16 - (j + c) = 0) := by
  have fw := L.ww
  have al32 := L.al_lt
  have E₂ := F.env
  have eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  have eB : State.addr (p.W + BitVec.ofNat 32 bufO) = State.addr p.W + BitVec.ofNat 64 bufO := L.wA (by decide)
  have cnt : t₂.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := F.cnt
  have hB := blkFrame_ok encF L (t := chunkCallSt p c t₂)
    (D := p.W + BitVec.ofNat 32 bufO) (n := c) (chunkCall_blk L F hc).2 (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by decide)]; simp only [bufO]; omega)
      (by rw [eB]; exact E₂.perm.wC (by simp only [bufO]; omega)) (by rw [eB]; exact L.k_w' (by simp only [bufO]; omega))
      (by rw [eB]; exact L.w_w (.inl (by simp only [scrO, bufO]; omega)) (by simp only [bufO]; omega) (by decide))
      (by rw [eB]; exact L.bw' (by simp only [bufO]; omega))
  rw [eB] at hB
  refine WP.seq (WP.mono (encFrame_eq ▸ hB) fun t₃ C₃ => ?_)
  -- what the call leaves
  have g₃ : ∀ r ∈ keptRegs, t₃.gpr r = t₂.gpr r := fun r hr => by
    rw [C₃.saved r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  have E₃ : Env p t₃ := E₂.keep (fun r hr => g₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))
    (by rw [C₃.sp]; rfl) (by rw [C₃.rd]; rfl) (by rw [C₃.wr]; rfl)
  have frC : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 bufO, 16 * c⟩ : Region),
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, Proof.AesGcm.Arm.below p.SP], ∃ r' ∈ hashR p, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by simp only [bufO]; omega⟩ (by decide)
    · exact w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact ⟨_, by simp, fun _ h => h⟩
  have fr₃ : Frame (hashR p) t₀.mem t₃.mem := F.frame.trans (C₃.frame.sub frC)
  have kW : ∀ {d k : Nat}, d + k ≤ bufO → (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint
      ⟨State.addr p.W + BitVec.ofNat 64 bufO, 16 * c⟩ ∧
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩ ∧
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (Proof.AesGcm.Arm.below p.SP) := fun hd =>
    ⟨L.w_w (.inl hd) (by simp only [bufO] at hd ⊢; omega) (by simp only [bufO]; omega),
      L.w_w (.inl (by simp only [bufO, scrO] at hd ⊢; omega)) (by simp only [bufO] at hd ⊢; omega) (by decide),
      (L.bw' (by simp only [bufO] at hd ⊢; omega)).symm⟩
  have kblk : ∀ {d : Nat}, d + 16 ≤ bufO →
      blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd => blockAtMem_frame C₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [(kW hd).1, (kW hd).2.1, (kW hd).2.2]
  have cnt₃ : t₃.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := by
    rw [C₃.frame.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 212, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [(kW (by decide)).1, (kW (by decide)).2.1, (kW (by decide)).2.2]) (by decide)]
    exact cnt
  have rC₃ : InRegions (t₃.rd ++ t₃.wr) (State.addr p.W + BitVec.ofNat 64 212) 4 := E₃.perm.wR (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E₃.r11, eC, rC₃, cnt₃], ?_⟩)
  have hsched : sched p t₂.mem = sched p t₀.mem := sched_mut L (hashR_mut L F.frame)
  refine WP.seq (WP.mono (sum_ok L (t₀ := t₀) (j := j) (c := c) hc0 hc ?S0) fun t₄ S => ?_)
  case S0 =>
    refine ⟨E₃.of_others (rs := [.r5, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl),
      by simp only [mem_setReg]; exact fr₃, by simp [rd_setReg, C₃.rd, F.rd], by simp [wr_setReg, C₃.wr, F.wr],
      by simp [gpr_setReg, g₃ .r4 (by decide), F.r4], by simp [gpr_setReg, g₃ .r6 (by decide), F.r6],
      by simp [gpr_setReg, E₃.r11, bufO], by simp [gpr_setReg],
      by simp [gpr_setReg, g₃ .r7 (by decide), F.r7], ?_, fun k hk => ?_, ?_, ?_⟩
    · simp only [mem_setReg]; rw [kblk (by decide), F.oh]
    · simp only [mem_setReg]
      have := C₃.out k hk
      simp only [mem_setReg, Offset.add_add] at this
      rw [this, F.buf k hk, encF_ciph]
      simp only [mem_setReg, hsched]
    · simp only [mem_setReg]; rw [kblk (by decide), F.sum]; simp
    · simp only [mem_setReg]; rw [kblk (by decide), F.l0]
  -- the end
  refine WP.of_runBlock ⟨_, by orun [S.r7], ?_⟩
  refine ⟨⟨S.env.of_others (rs := []) (by others_tac) (by rfl) (by rfl) (by rfl), S.frame, S.rd, S.wr, hjc,
    S.sum, S.oh, S.r4, S.r6, by simp only [Proof.AesGcm.Arm.gpr_subFlags, S.r7]; congr 1; omega, S.l0⟩, ?_⟩
  simp only [z_subFlags, S.r7, BitVec.sub_zero, z_cmp0 (show p.al / 16 - j - c < 2 ^ 32 by omega)]
  congr 1; apply propext; omega


/-- A chunk of `c` blocks from block `j`, once `c` is in `r5`. -/
theorem chunkRest_ok {p : Prm} (L : Lay p) {t₀ : State} {t : State} {j c : Nat}
    (H : HInv p t₀ t j) (hc0 : 0 < c) (hc : c ≤ 16) (hjc : j + c ≤ p.al / 16)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 c) :
    WP isa (.seq (.block [.str .r5 .r11 cnO, .dp .sub .r7 .r7 (.reg .r5), Impl.AesGcm.Arm.addI .r8 .r11 bufO])
      (.seq (.loop hashFill .ne)
      (.seq (.block (callArgs ++ [Impl.AesGcm.Arm.addI .r2 .r11 bufO, .ldr .r3 .r11 cnO]))
      (.seq encFrame
      (.seq (.block [Impl.AesGcm.Arm.addI .r8 .r11 bufO, .ldr .r5 .r11 cnO])
      (.seq hashSum (.block [.cmp .r7 (Impl.AesGcm.Arm.imm 0)])))))))
      t fun t' => HInv p t₀ t' (j + c) ∧ t'.z = decide (p.al / 16 - (j + c) = 0) :=
  WP.seq (WP.mono (chunkHead_ok L H hc hjc h5) fun _ F₁ => WP.seq (WP.mono (fill_ok L hc0 hc hjc F₁)
    fun _ F₂ => WP.seq (WP.of_runBlock ⟨_, chunkArgs_run L F₂, chunkTail_ok L F₂ hc0 hc hjc⟩)))

theorem hashChunk_ok {p : Prm} (L : Lay p) {t₀ : State} {t : State} {j : Nat}
    (H : HInv p t₀ t j) (hj : j < p.al / 16) :
    WP isa hashChunk t fun t' => HInv p t₀ t' (j + min 16 (p.al / 16 - j)) ∧
      t'.z = decide (p.al / 16 - (j + min 16 (p.al / 16 - j)) = 0) := by
  have al32 := L.al_lt
  have m32 : p.al / 16 - j < 2 ^ 32 := by omega
  unfold hashChunk
  have z₁ : (BitVec.ofNat 32 (p.al / 16 - j) >>> 4 == 0) = decide (p.al / 16 - j < 16) := by
    rw [ofNat_lsr32 m32, z_cmp0 (by omega)]; congr 1; apply propext; omega
  refine WP.seq (WP.of_runBlock ⟨_, by orun [H.r7], ?_⟩)
  have Hk : ∀ {t' : State}, t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp →
      Others [.r5, .r12] t t' → HInv p t₀ t' j := fun hm hrd hwr hsp ho =>
    ⟨H.env.of_others ho hsp hrd hwr, by rw [hm]; exact H.frame, by rw [hrd, H.rd], by rw [hwr, H.wr], H.le,
      by rw [hm]; exact H.sum, by rw [hm]; exact H.oh, by rw [ho _ (by decide), H.r4], by rw [ho _ (by decide), H.r6],
      by rw [ho _ (by decide), H.r7], by rw [hm]; exact H.l0⟩
  refine WP.seq (WP.ite (decide (p.al / 16 - j < 16))
    (eval_eq' (by simp only [z_subFlags, gpr_setReg, ite_true, H.r7, BitVec.sub_zero, z₁])) (fun hb => ?_)
    (fun hb => ?_))
  · have hlt : p.al / 16 - j < 16 := of_decide_eq_true hb
    refine WP.of_runBlock ⟨_, by orun [H.r7], ?_⟩
    have e : min 16 (p.al / 16 - j) = p.al / 16 - j := by omega
    rw [e]
    exact chunkRest_ok L (Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac)) (by omega) (by omega) (by omega)
      (by simp [gpr_setReg, H.r7])
  · have hlt : ¬ p.al / 16 - j < 16 := by simpa using hb
    refine WP.of_runBlock ⟨_, by orun [], ?_⟩
    have e : min 16 (p.al / 16 - j) = 16 := by omega
    rw [e]
    exact chunkRest_ok L (Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac)) (by omega) (by omega) (by omega)
      (by simp [gpr_setReg])

end VG.Proof.AesOcb.Arm