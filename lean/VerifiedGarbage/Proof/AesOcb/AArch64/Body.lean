import VerifiedGarbage.Proof.AesOcb.AArch64.RestTag

/-!
# AES-OCB on AArch64: the data (`body`)

Untrusted: everything here is checked by Lean. `body` takes the whole blocks
(if any, `wholeIte_ok`) and then the rest (if any, `restIte_ok`); for `seal`
the result is `OCB-ENCRYPT`'s ciphertext, offset and checksum
(`bodySeal_ok`), for `open` `OCB-DECRYPT`'s (`bodyOpen_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (eval_zero toNat_ofNat_of_lt lsr_ofNat and15)

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {pm qm : CkMode} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, BodyOk W post (fun b o => b ^^^ o) fC2)
    (hM1 : fC1 = ckOp pm) (hM2 : fC2 = ckOp qm)
    {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {s : State} (E : Env K W D R n SP s)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : DBuf K W s D n) {O0 l : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.lsr .x .x26 .x28 4]) (.ite (.zero .x .x26) (.block []) (whole b pre post pm qm))) s
      (WholePost K W D R n SP (n / 16) O0 l
        (fun k => G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.lsr .x .x26 .x28 4] s = some s₁ ∧
      s₁ = s.write .x .x26 (s.gpr .x28 >>> 4) := ⟨_, by orun [], rfl⟩
  subst h₁
  have x26₁ : (s.write .x .x26 (s.gpr .x28 >>> 4)).gpr .x26 = BitVec.ofNat 64 (n / 16) := by
    simp [gpr_write, E.x28, lsr_ofNat _ _ hn]
  have E₁ : Env K W D R n SP (s.write .x .x26 (s.gpr .x28 >>> 4)) :=
    E.others (rs := [.x26]) (fun r hr => by simp at hr; simp [gpr_write, hr]) rfl rfl rfl
  refine WP.seq (WP.of_runBlock ⟨_, run₁, ?_⟩)
  refine WP.ite _ (eval_zero x26₁ (by omega)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, Frame.refl _ _, rfl, rfl, fun k hk => absurd hk (by omega),
      by rw [mem_write, hofs, hm]; rfl, by rw [mem_write, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    refine WP.mono (whole_ok (O0 := O0) (l := l) ok nf hcall hB1 hB2 hM1 hM2 L E₁ hR (hD.of_eq rfl rfl)
      (Nat.mul_div_le n 16) (by omega) (by omega) x26₁ hofs ho0 hck hl0 hckF1 hckF2₀ hckF2) fun t P => ?_
    exact ⟨P.env, P.frame, P.rd, P.wr, P.blk, P.ofs, P.ck⟩

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {K W D : Addr} {R n : Nat} {SP : Addr} {t : State} (E : Env K W D R n SP t) (hn : n < 2 ^ 64) :
    ∃ t₁, runBlock isa [Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x28 .x10, .sub .x .x9 .x28 .x24,
        .add .x .x23 .x21 .x9] t = some t₁ ∧
      t₁.gpr .x23 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .x24 = BitVec.ofNat 64 (n % 16) ∧
      t₁.mem = t.mem ∧ (∀ r, r ∉ [.x9, .x10, .x23, .x24] → t₁.gpr r = t.gpr r) ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [Proof.AesGcm.AArch64.ofNat_sub (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega]
  refine ⟨_, by orun [], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, E.x28, E.x21, and15, toNat_ofNat_of_lt hn, hsub]
  · simp [gpr_write, E.x28, and15, toNat_ofNat_of_lt hn]
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  all_goals rfl

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (K W D : Addr) (R n : Nat) (SP : Addr) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : Env K W D R n SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K
    else blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K)))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (W + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (v : BlocksImpl) (enc : Bool) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {t : State}
    (E : Env K W D R n SP t) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : DBuf K W t D n) :
    WP isa (.seq (.block [Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x28 .x10, .sub .x .x9 .x28 .x24,
        .add .x .x23 .x21 .x9]) (.ite (.zero .x .x24) (.block []) (rest (callees v) enc))) t
      (TailPost enc K W D R n SP (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, x23₁, x24₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := bodyTail_ok E hn
  have E₁ := E.others g₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_zero x24₁ (by omega)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega
    refine ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, m₁]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega
    have hP : DBuf K W t₁ (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)).of_eq rd₁ wr₁
    refine WP.mono (rest_ok v enc L E₁ hR hr (Nat.mod_lt _ (by decide)) x23₁ x24₁ hP) fun t' P => ?_
    refine ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, m₁]
    · rw [P.out, m₁]
    · rw [P.ck, m₁]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called, the stack and the data. -/
abbrev bodyR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 48⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem bodyR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (bodyR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (K W D : Addr) (R n : Nat) (SP : Addr) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : Env K W D R n SP t
  frame : Frame (bodyR W D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt p i) :
    ckOf X m = Proof.Ocb.ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega)]

/-- `ENCIPHER` from the key schedule, whatever its length. -/
def encG (ks : List Byte) : Cipher := Spec.Ocb.aesWith (ks.length / 16 - 1) ks

/-- `DECIPHER` from the key schedule, whatever its length. -/
def decG (ks : List Byte) : Cipher := Spec.Ocb.aesInvWith (ks.length / 16 - 1) ks

theorem encG_eq (m : Mem) (K : Addr) (R : Nat) : encG (bytesAt m K (16 * (R + 1))) = ctxCiph m K R := by
  rw [encG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega]; rfl

theorem decG_eq (m : Mem) (K : Addr) (R : Nat) : decG (bytesAt m K (16 * (R + 1))) = Spec.Ocb.ctxInv m K R := by
  rw [decG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega]; rfl

theorem hcall_enc {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.cipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      encG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.enc hi, encG_eq]; rfl

theorem hcall_dec {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.invCipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      decG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.dec hi, decG_eq]; rfl

/-- A buffer apart from `W` and `⟨P, r⟩` misses what `rest` writes. -/
theorem disj_tail {W Q P : Addr} {k r : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨P, r⟩) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩], (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

/-- A buffer apart from `W` and `⟨D, n⟩` misses what `whole` writes. -/
theorem disj_whole {W Q D : Addr} {k n : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ x ∈ wholeR W D n, (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

theorem wholeR_sub {W D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ wholeR W D k, ∃ r' ∈ bodyR W D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

theorem tailR_sub {W D : Addr} {n a r : Nat} (h : a + r ≤ n) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ bodyR W D n, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {s : State}
    (E : Env K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : DBuf K W s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0) :
    WP isa (body (callees v) true) s (BodyPost K W D R n SP
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) ^^^ pad ((bytesAt s.mem D n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf K W s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf K W s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega)).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K)
    (ckF1 := ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    v.encOk v.encNoFrames hcall_enc sealPre_ok xorOfs_ok rfl rfl L E hR hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR W D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  refine WP.mono (restIte_ok v true L Pw.env hR (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem K R = ctxCiph s.mem K R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega), Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, encG_eq, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
    rw [show 16 * (n / 16) + n % 16 = n by omega] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

/-- `body` for `open`. -/
theorem bodyOpen_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {s : State}
    (E : Env K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : DBuf K W s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0) :
    WP isa (body (callees v) false) s (BodyPost K W D R n SP
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf K W s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf K W s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem K (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem K) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem K) (i + 1))
    v.decOk v.decNoFrames hcall_dec xorOfs_ok openPost_ok rfl rfl L E hR hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR W D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  refine WP.mono (restIte_ok v false L Pw.env hR (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem K R = ctxCiph s.mem K R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega), Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, decG_eq, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at e
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.AArch64
