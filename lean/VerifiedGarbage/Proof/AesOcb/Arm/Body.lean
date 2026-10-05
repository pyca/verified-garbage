import VerifiedGarbage.Proof.AesOcb.Arm.RestTag

/-!
# AES-OCB on ARMv7: the data (`body`)

Untrusted: everything here is checked by Lean. `body` takes the whole blocks
(if any, `wholeIte_ok`) and then the rest (if any, `restIte_ok`); for `seal`
the result is `OCB-ENCRYPT`'s ciphertext, offset and checksum
(`bodySeal_ok`), for `open` `OCB-DECRYPT`'s (`bodyOpen_ok`), as on AArch64
(`Proof.AesOcb.AArch64.bodySeal_ok`, `Proof.AesOcb.AArch64.bodyOpen_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Impl.AesGcm.Arm (imm)
open VG.Proof.AesGcm.Arm (eval_eq' z_subFlags z_cmp0 and15 ofNat_sub32 below)

/-- What the whole blocks leave, if there are any. -/
structure WholeIte (p : Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame (wholeR p m) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ck
  r8 : t'.gpr .r8 = p.D

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok (F : BlkFn) {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block}
    {ckF1 ckF2 : Nat → Block} {p : Prm} (L : Lay p)
    (hB1 : BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk p post (fun b o => b ^^^ o) fC2)
    {s : State} (E : Env p s) (A : Args p s.mem) {O0 l : Block}
    (hofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) =
      fC1 (ckF1 i) (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (p.n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (F.ciph p.R (sched p s.mem) (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4), .cmp .r7 (imm 0)])
      (.ite .eq (.block []) (whole (blkFrame F) pre post))) s
      (WholeIte p (p.n / 16) O0 l
        (fun k => F.ciph p.R (sched p s.mem)
          (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (p.n / 16)) s) := by
  have n32 := L.n_lt
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  have a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E.sp, a₈, a₁₂, A.a8, A.a12], ?_⟩)
  refine WP.ite (decide (p.n / 16 = 0)) (eval_eq' (by
    simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, ofNat_lsr32 n32,
      Nat.reducePow, z_cmp0 (show p.n / 16 < 2 ^ 32 by omega)])) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hm : p.n / 16 = 0 := of_decide_eq_true hb
    refine ⟨E.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl), Frame.refl _ _, rfl, rfl,
      fun k hk => absurd hk (by omega), ?_, ?_, ?_⟩
    · show blockAtMem s.mem _ = _
      rw [hofs, hm]; rfl
    · show blockAtMem s.mem _ = _
      rw [hck, hm, hckF2₀, hm]
    · simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]
  · have hm : p.n / 16 ≠ 0 := by simpa using hb
    refine WP.mono (whole_ok F L hB1 hB2 (E.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl)) (m := p.n / 16) (O0 := O0) (l := l) (Nat.mul_div_le p.n 16)
      (by omega) (by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg])
      (by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ofNat_lsr32 n32]) hofs ho0 hck hl0 hckF1 hckF2₀ hckF2)
      fun t P => ⟨P.env, P.frame, P.rd, P.wr, P.blk, P.ofs, P.ck, ?_⟩
    rw [P.gpr .r8 (by decide)]
    simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]

/-- What the rest of the data leaves, if there is any: `r` bytes at `D + a`. -/
structure TailPost (enc : Bool) (p : Prm) (a r : Nat) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem
    else blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem (State.addr p.D + BitVec.ofNat 64 a) r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r)
      (Spec.Ocb.toBytes (ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem)))
    else bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
      pad (bytesAt (if enc then t.mem else t'.mem) (State.addr p.D + BitVec.ofNat 64 a) r)
    else blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (enc : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem)
    (h8 : t.gpr .r8 = p.D) :
    WP isa (.seq (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12, .dp .sub .r4 .r4 (.reg .r5),
        .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) (.ite .eq (.block []) (rest enc))) t
      (TailPost enc p (16 * (p.n / 16)) (p.n % 16) t) := by
  have n32 := L.n_lt
  have a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E.sp, a₁₂, A.a12, h8], ?_⟩)
  refine WP.ite (decide (p.n % 16 = 0)) (eval_eq' (by
    simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, and15,
      toNat_ofNat32 n32, z_cmp0 (show p.n % 16 < 2 ^ 32 by omega)])) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hr : ¬ 0 < p.n % 16 := by have := of_decide_eq_true hb; omega
    refine ⟨E.of_others (rs := [.r4, .r5]) (by others_tac) (by rfl) (by rfl) (by rfl), Frame.refl _ _, rfl, rfl, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte] <;> rfl
  · have hr : 0 < p.n % 16 := by have : p.n % 16 ≠ 0 := by simpa using hb
                                 omega
    refine WP.mono (rest_ok enc L (E.of_others (rs := [.r4, .r5]) (by others_tac) (by rfl) (by rfl) (by rfl)) ⟨by omega, hr, Nat.mod_lt _ (by decide)⟩ ?_ ?_) fun t' P =>
      ⟨P.env, P.frame, P.rd, P.wr, ?_, ?_, ?_⟩
    · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
        toNat_ofNat32 n32, h8]
      rw [ofNat_sub32 (Nat.mod_le _ _) n32, BitVec.add_comm, show p.n - p.n % 16 = 16 * (p.n / 16) by omega]
    · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
        toNat_ofNat32 n32]
    · simp only [hr, ↓reduceIte]; exact P.ofs
    · simp only [hr, ↓reduceIte]; exact P.out
    · simp only [hr, ↓reduceIte]; exact P.ck

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad`,
`pad(·)`, the working space of the functions called, the stack and the
data. -/
abbrev bodyR (p : Prm) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, ⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 512, 2048⟩, below p.SP,
   ⟨State.addr p.D, p.n⟩]

theorem bodyR_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (bodyR p) m m') : Frame (mutR p) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact below_mut L
    · exact ⟨_, by simp, fun _ h => h⟩

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (p : Prm) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : Env p t
  frame : Frame (bodyR p) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem (State.addr p.D) p.n = out
  ofs : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {q : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt q i) :
    ckOf X m = Proof.Ocb.ckAt q m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega)]

section
variable {p : Prm} (L : Lay p)

include L in
/-- The rest of the data misses what `whole` writes. -/
theorem disj_whole {a r : Nat} (ha : 16 * (p.n / 16) ≤ a) (hf : a + r ≤ p.n) :
    ∀ x ∈ wholeR p (p.n / 16), (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hf)
  · exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hf)
  · exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hf)
  · exact (Offset.base_disjoint _ ha (by have := L.dw; omega)).symm
  · exact (L.bd.sub_right (Offset.sub_base _ hf)).symm

include L in
/-- The whole blocks miss what `rest` writes. -/
theorem disj_tail {a r : Nat} (ha : 16 * (p.n / 16) ≤ a) (hf : a + r ≤ p.n) :
    ∀ x ∈ [(⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩],
      (⟨State.addr p.D, 16 * (p.n / 16)⟩ : Region).Disjoint x := by
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨State.addr p.D, 16 * (p.n / 16)⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
    fun h => (L.d_w' h).sub_left (Region.sub_prefix (Nat.mul_div_le p.n 16))
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dW (by decide)
  · exact dW (by decide)
  · exact dW (by decide)
  · exact dW (by decide)
  · exact dW (by decide)
  · exact (L.bd.sub_right (Region.sub_prefix (Nat.mul_div_le p.n 16))).symm
  · exact Offset.base_disjoint _ ha (by have := L.dw; omega)

theorem wholeR_sub : ∀ r ∈ wholeR p (p.n / 16), ∃ r' ∈ bodyR p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, by simp [scrO], fun _ h => h⟩
  · exact ⟨⟨State.addr p.D, p.n⟩, by simp, Region.sub_prefix (Nat.mul_div_le p.n 16)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem tailR_sub {a r : Nat} (h : a + r ≤ p.n) :
    ∀ x ∈ [(⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ bodyR p, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, by simp [scrO], fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨⟨State.addr p.D, p.n⟩, by simp, Offset.sub_base _ h⟩

end

/-- `body` for `seal`. -/
theorem bodySeal_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) {O0 : Block}
    (hofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p s.mem) 0) :
    WP isa (body true) s (BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.encBlocks (ciphOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ciphOf p s.mem (offAt O0 (lstarOf p s.mem) (p.n / 16) ^^^ lstarOf p s.mem)))
      else Proof.Ocb.encBlocks (ciphOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (lstarOf p s.mem) (p.n / 16) ^^^ lstarOf p s.mem
       else offAt O0 (lstarOf p s.mem) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ^^^
          pad ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16)) s) := by
  have hn := L.n_lt
  have hmn : 16 * (p.n / 16) ≤ p.n := Nat.mul_div_le p.n 16
  have hl : ∀ i < p.n / 16, blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) =
      Spec.Ocb.blockAt (bytesAt s.mem (State.addr p.D) p.n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem _ (by omega)).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok encF (O0 := O0) (l := lstarOf p s.mem)
    (ckF1 := ckOf fun i => blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
    L (sealPre_ok L) (xorOfs_ok L) E A hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR p) s.mem t.mem := wholeR_mut L hmn Pw.frame
  refine WP.mono (restIte_ok true L Pw.env (A.mut L fW) Pw.r8) fun t' Pt => ?_
  have cT : ciphOf p t.mem = ciphOf p s.mem := by simp only [ciphOf, sched_mut L fW]
  have lT : lstarOf p t.mem = lstarOf p s.mem := lstar_mut L fW
  have pT : bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) := by
    exact Proof.Cmac.bytesAt_frame Pw.frame (disj_whole L (Nat.le_refl _) (by omega)) (by omega)
  have rest : (bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem _ hmn, show p.n - 16 * (p.n / 16) = p.n % 16 by omega]
  have ckT : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.ckAt (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  have blk : bytesAt t'.mem (State.addr p.D) (16 * (p.n / 16)) =
      Proof.Ocb.encBlocks (ciphOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail L (Nat.le_refl _) (by omega)) (by omega),
      Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, encF_ciph, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub wholeR_sub).trans (Pt.frame.sub (tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem (State.addr p.D) (16 * (p.n / 16)) (p.n % 16)
    rw [show 16 * (p.n / 16) + p.n % 16 = p.n by omega] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show p.n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

/-- `DECIPHER` with the key schedule in `m`. -/
abbrev invOf (p : Prm) (m : Mem) : Cipher := Spec.Ocb.aesInvWith p.R (sched p m)

/-- `body` for `open`. -/
theorem bodyOpen_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) {O0 : Block}
    (hofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p s.mem) 0) :
    WP isa (body false) s (BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.decBlocks (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ciphOf p s.mem (offAt O0 (lstarOf p s.mem) (p.n / 16) ^^^ lstarOf p s.mem)))
      else Proof.Ocb.decBlocks (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (lstarOf p s.mem) (p.n / 16) ^^^ lstarOf p s.mem
       else offAt O0 (lstarOf p s.mem) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.dckAt (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ciphOf p s.mem (offAt O0 (lstarOf p s.mem) (p.n / 16) ^^^ lstarOf p s.mem))))
      else Proof.Ocb.dckAt (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16)) s) := by
  have hn := L.n_lt
  have hmn : 16 * (p.n / 16) ≤ p.n := Nat.mul_div_le p.n 16
  have hl : ∀ i < p.n / 16, blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) =
      Spec.Ocb.blockAt (bytesAt s.mem (State.addr p.D) p.n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem _ (by omega)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok decF (O0 := O0) (l := lstarOf p s.mem) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => invOf p s.mem
      (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (lstarOf p s.mem) (i + 1)) ^^^
        offAt O0 (lstarOf p s.mem) (i + 1))
    L (xorOfs_ok L) (openPost_ok L) E A hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR p) s.mem t.mem := wholeR_mut L hmn Pw.frame
  refine WP.mono (restIte_ok false L Pw.env (A.mut L fW) Pw.r8) fun t' Pt => ?_
  have cT : ciphOf p t.mem = ciphOf p s.mem := by simp only [ciphOf, sched_mut L fW]
  have lT : lstarOf p t.mem = lstarOf p s.mem := lstar_mut L fW
  have pT : bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole L (Nat.le_refl _) (by omega)) (by omega)
  have rest : (bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem _ hmn, show p.n - 16 * (p.n / 16) = p.n % 16 by omega]
  have ckT : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem (State.addr p.D) (16 * (p.n / 16)) =
      Proof.Ocb.decBlocks (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail L (Nat.le_refl _) (by omega)) (by omega),
      Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, decF_ciph, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem (State.addr p.D) (16 * (p.n / 16)) (p.n % 16)
  rw [show 16 * (p.n / 16) + p.n % 16 = p.n by omega] at e
  refine ⟨Pt.env, (Pw.frame.sub wholeR_sub).trans (Pt.frame.sub (tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show p.n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < p.n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.Arm
