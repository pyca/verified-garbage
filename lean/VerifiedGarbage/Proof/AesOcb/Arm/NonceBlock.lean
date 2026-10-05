import VerifiedGarbage.Proof.AesOcb.Arm.LNtz
import VerifiedGarbage.Proof.Ocb.Nonce
import VerifiedGarbage.Proof.Ocb.Bytes

/-!
# AES-OCB on ARMv7: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`), as on AArch64
(`Proof.AesOcb.AArch64.nonceBlock_ok`): zeros, the 1 before where the nonce
goes, the nonce copied to the end (`copyLoop`), `TAGLEN mod 128` ORed into
the first byte, and the last byte split into `bottom` and the rest. The 16
bytes are followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase length_bytesAt bytesAt_writeBytes_at bytesAt_writeW8_at bytesAt_writeW8_base)
open VG.Proof.AesGcm.Arm (copyLoop_ok LoopPre in_left in_off and15 mem_store rd_store wr_store sp_store gpr_store add_ofNat_zero setWidth8_32)

theorem ofNat_shl4 (a : Nat) : BitVec.ofNat 32 a <<< 4 = BitVec.ofNat 32 (16 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]
  congr 1; omega

theorem or_byte32 (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 b ||| BitVec.ofNat 32 v) = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, show i < 32 by omega, hi,
    decide_true, Bool.true_and]

theorem and_byte32 (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 b &&& BitVec.ofNat 32 v) = b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, show i < 32 by omega, hi,
    decide_true, Bool.true_and]

theorem and63_32 (b : Byte) : BitVec.setWidth 32 b &&& BitVec.ofNat 32 63 = BitVec.ofNat 32 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    show (63 : Nat) % 2 ^ 32 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega) (by decide)

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp [show min k L.length = k by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega, ↓reduceIte]
    congr 2; omega

/-- What `nonceBlock` leaves. -/
structure NoncePost (W : Addr) (t : Nat) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 4⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) = nonceN t nonce &&& ~~~(63 : Block)
  bot : s'.mem.readW (W + BitVec.ofNat 64 botO) 32 = BitVec.ofNat 32 ((nonceN t nonce).extractLsb' 0 6).toNat
  gpr : Others [.r0, .r1, .r2, .r3, .r12] s s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem w127 (W : BitVec 32) {nl : Nat} (h : nl ≤ 15) :
    W + BitVec.ofNat 32 127 - BitVec.ofNat 32 nl = W + BitVec.ofNat 32 (127 - nl) := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat (by omega)]

theorem w128 (W : BitVec 32) {nl : Nat} (h : nl ≤ 15) :
    W + BitVec.ofNat 32 (127 - nl) + BitVec.ofNat 32 1 = W + BitVec.ofNat 32 (128 - nl) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

theorem nonceBlock_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem)
    (h4 : s.gpr .r4 = p.N) (h5 : s.gpr .r5 = BitVec.ofNat 32 p.nl) :
    WP isa nonceBlock s (NoncePost (State.addr p.W) p.tl (bytesAt s.mem (State.addr p.N) p.nl) s) := by
  have fw := L.ww
  have h1 := L.nl1
  have h15 := L.nl15
  have nl32 : p.nl < 2 ^ 32 := by omega
  unfold nonceBlock
  refine WP.seq (WP.block_append (WP.mono (zero16_wp (o := tmpO) (by decide) (by rw [E.r11]; simp only [tmpO]; omega)
    (by rw [E.r11]; exact E.perm.wC (by decide))) fun s₁ R₁ => ?_))
  rw [E.r11] at R₁
  have r11₁ : s₁.gpr .r11 = p.W := by rw [R₁.gpr _ (by decide), E.r11]
  have r4₁ : s₁.gpr .r4 = p.N := by rw [R₁.gpr _ (by decide), h4]
  have r5₁ : s₁.gpr .r5 = BitVec.ofNat 32 p.nl := by rw [R₁.gpr _ (by decide), h5]
  have ea : State.addr (p.W + BitVec.ofNat 32 (127 - p.nl)) = State.addr p.W + BitVec.ofNat 64 (127 - p.nl) :=
    addr_add (by omega)
  have w₁ : InRegions s₁.wr (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) 1 := by
    rw [R₁.wr]; exact E.perm.wW (d := 127 - p.nl) (n := 1) (by omega)
  have eD : State.addr (p.W + BitVec.ofNat 32 (128 - p.nl)) = State.addr p.W + BitVec.ofNat 64 (128 - p.nl) :=
    addr_add (by omega)
  refine WP.of_runBlock ⟨_, by orun [r11₁, r4₁, r5₁, w127 _ h15, add_ofNat_zero, ea, w₁, w128 _ h15], ?_⟩
  refine WP.seq (WP.mono (copyLoop_ok _ (S := p.N) (D := p.W + BitVec.ofNat 32 (128 - p.nl)) (n := p.nl)
    ⟨by simp [gpr_setReg, r4₁], by simp [gpr_setReg], by simp [gpr_setReg, r5₁], h1, nl32, L.nw,
      by rw [L.wN (by omega)]; omega, by simp only [rd_setReg, wr_setReg, rd_store, wr_store, R₁.rd, R₁.wr]; exact E.perm.non,
      by simp only [wr_setReg, wr_store, R₁.wr, eD]; exact E.perm.wC (d := 128 - p.nl) (n := p.nl) (by omega),
      by rw [eD]; exact L.n_w' (by omega)⟩) fun s₃ ⟨m₃, O₃⟩ => ?_)
  simp only [mem_store, mem_setReg, eD] at m₃
  -- what the first two pieces wrote
  have e127 : State.addr p.W + BitVec.ofNat 64 (127 - p.nl) =
      State.addr p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - p.nl) := by
    rw [Offset.add_add, show 112 + (15 - p.nl) = 127 - p.nl by omega]
  have e128 : State.addr p.W + BitVec.ofNat 64 (128 - p.nl) =
      State.addr p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - p.nl) := by
    rw [Offset.add_add, show 112 + (16 - p.nl) = 128 - p.nl by omega]
  have f₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩] s.mem
      (s₁.mem.writeW (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) (BitVec.setWidth 8 (BitVec.ofNat 32 1))) := by
    rw [R₁.mem]
    refine (Proof.Cmac.frame_store4 _ _ _ _ _).writeW (List.mem_singleton_self _) _ ?_
    rw [e127]; exact Offset.contains_base _ (by omega) (by omega)
  have f₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩] s.mem s₃.mem := by
    rw [m₃]
    refine fun x hx => (writeBytes_frame _ _ _ ?_ x hx).trans (f₂ x hx)
    rw [length_bytesAt, e128]; exact Offset.contains_base _ (by omega) (by omega)
  have A₃ : Args p s₃.mem := A.frame L f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.args_w' (by decide))
  have sp₃ : s₃.sp = p.SP := by rw [O₃.sp]; simp [sp_setReg, sp_store, R₁.sp, E.sp]
  have rd₃ : s₃.rd = s.rd := by rw [O₃.rd]; simp [rd_setReg, rd_store, R₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [O₃.wr]; simp [wr_setReg, wr_store, R₁.wr]
  have r11₃ : s₃.gpr .r11 = p.W := by
    rw [O₃.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, gpr_store, r11₁]
  have P₃ : Perm p s₃ := E.perm.of_eq rd₃ wr₃
  have a₂₀ := P₃.argR' L (k := 20) (by decide)
  have rb₀ : InRegions (s₃.rd ++ s₃.wr) (State.addr p.W + BitVec.ofNat 64 112) 1 := P₃.wR (by decide)
  have wb₀ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 112) 1 := P₃.wW (by decide)
  have rb₁ : InRegions (s₃.rd ++ s₃.wr) (State.addr p.W + BitVec.ofNat 64 127) 1 := P₃.wR (by decide)
  have wb₁ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 127) 1 := P₃.wW (by decide)
  have wb₂ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 208) 4 := P₃.wW (by decide)
  have ne : (State.addr p.W + BitVec.ofNat 64 127 = State.addr p.W + BitVec.ofNat 64 112) = False := by
    simp only [eq_iff_iff, iff_false]
    intro h
    have := congrArg (· - State.addr p.W) h
    simp only [Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  have ew : ∀ k, k < 2560 → State.addr (p.W + BitVec.ofNat 32 k) = State.addr p.W + BitVec.ofNat 64 k :=
    fun k hk => L.wA hk
  have e112 := ew 112 (by decide)
  have e127' := ew 127 (by decide)
  have e208 := ew 208 (by decide)
  refine WP.of_runBlock ⟨_, by orun [r11₃, sp₃, A₃.a20, a₂₀, e112, e127', e208, rb₀, wb₀, rb₁, wb₁, wb₂,
    WriteBytes.writeW8_apply, ne], ?_⟩
  have htl : p.tl < 2 ^ 32 := by have := L.tl16; omega
  simp only [and15, toNat_ofNat32 htl, ofNat_shl4, or_byte32, and_byte32, and63_32]
  -- the bytes at `W + tmpO`, step by step
  have hlen : (bytesAt s.mem (State.addr p.N) p.nl).length = p.nl := length_bytesAt _ _ _
  have eN : bytesAt (s₁.mem.writeW (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) (BitVec.setWidth 8 (BitVec.ofNat 32 1)))
      (State.addr p.N) p.nl = bytesAt s.mem (State.addr p.N) p.nl :=
    Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.n_w' (by decide)) (by omega)
  rw [eN] at m₃
  have L₁ : bytesAt s₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := by
    rw [R₁.mem]; exact Proof.Cmac.zero4_bytes _ _
  have L₂ : bytesAt (s₁.mem.writeW (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) (BitVec.setWidth 8 (BitVec.ofNat 32 1)))
      (State.addr p.W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (15 - p.nl) ++ [1] ++ Spec.Ocb.zeros p.nl := by
    rw [e127, bytesAt_writeW8_at _ _ _ (by omega) (by decide), L₁]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate, show min (15 - p.nl) 16 = 15 - p.nl by omega,
      show 16 - (15 - p.nl + 1) = p.nl by omega]
    rfl
  have L₃ : bytesAt s₃.mem (State.addr p.W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (15 - p.nl) ++ [1] ++ bytesAt s.mem (State.addr p.N) p.nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by omega) (by decide), L₂, hlen]
    rw [show 16 - p.nl + p.nl = 16 by omega]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, List.length_append, List.length_singleton, List.append_assoc]
    simp only [show min (16 - p.nl) (15 - p.nl) = 15 - p.nl by omega, show 16 - p.nl - (15 - p.nl) = 1 by omega,
      show 16 - (15 - p.nl) = p.nl + 1 by omega, show 15 - p.nl + (1 + p.nl) = 16 by omega]
    simp only [show 1 - 1 = 0 from rfl, Nat.zero_min, List.replicate_zero, List.nil_append,
      show 15 - p.nl - 16 = 0 by omega, List.take_one, List.head?_cons, Option.toList_some,
      List.drop_eq_nil_of_le (show [(1 : Byte)].length ≤ p.nl + 1 by simp), show p.nl - (p.nl + 1 - 1) = 0 by omega,
      List.append_nil]
  have L₃d : ∀ k < 16, (bytesAt s₃.mem (State.addr p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      nbase (bytesAt s.mem (State.addr p.N) p.nl) k := fun k hk => by
    have := Proof.Ocb.nbase_list (bytesAt s.mem (State.addr p.N) p.nl) (by rw [hlen]; omega) (by rw [hlen]; omega) hk
    rw [hlen] at this; rw [L₃]; exact this
  have b0 : s₃.mem (State.addr p.W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem (State.addr p.N) p.nl) 0 := by
    have := getD_bytesAt_eq s₃.mem (State.addr p.W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [BitVec.add_zero] at this
    rw [this, L₃d 0 (by decide)]
  have e127' : State.addr p.W + BitVec.ofNat 64 127 = State.addr p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 :=
    (Offset.add_add _ 112 15).symm
  have b15 : s₃.mem (State.addr p.W + BitVec.ofNat 64 127) = nb p.tl (bytesAt s.mem (State.addr p.N) p.nl) 15 := by
    rw [e127', getD_bytesAt_eq s₃.mem (State.addr p.W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide),
      L₃d 15 (by decide)]
    rfl
  have fr208 : ∀ (M : Mem) (v : BitVec 32), Frame [⟨State.addr p.W + BitVec.ofNat 64 208, 4⟩] M
      (M.writeW (State.addr p.W + BitVec.ofNat 64 208) v) :=
    fun M v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have L₄d : ∀ k < 16, (bytesAt (((s₃.mem.writeW (State.addr p.W + BitVec.ofNat 64 112)
        (s₃.mem (State.addr p.W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (p.tl % 16)))).writeW
        (State.addr p.W + BitVec.ofNat 64 208)
        (BitVec.ofNat 32 ((s₃.mem (State.addr p.W + BitVec.ofNat 64 127)).toNat % 64))).writeW
        (State.addr p.W + BitVec.ofNat 64 127) (s₃.mem (State.addr p.W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192))
        (State.addr p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb p.tl (bytesAt s.mem (State.addr p.N) p.nl) 15 &&& 0xc0
      else nb p.tl (bytesAt s.mem (State.addr p.N) p.nl) k := by
    intro k hk
    rw [b15, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.Cmac.bytesAt_frame (fr208 _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := 112) (n := 16) (d := 208) (k := 4) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      getD_set16 _ (length_bytesAt _ _ _) (by decide) _ hk]
    split
    · rfl
    · rename_i hk15
      rw [bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0]
      unfold nb
      rcases k with _ | k
      · rfl
      · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
          show 1 + k = k + 1 by omega]
        exact L₃d (k + 1) hk
  have fs₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 botO, 4⟩]
      s.mem s₃.mem := f₃.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [tmpO])
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [mem_store, tmpO, botO]
    refine ((fs₃.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Region.contains_self _ _)).writeW (List.mem_cons_self ..) _ ?_
    · exact contains_pre _ (by decide)
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · simp only [mem_store, tmpO]
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _)]
    refine Proof.Cmac.ext16 (length_bytesAt _ _ _) (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₄d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega) (by omega) hk]
  · simp only [mem_store, botO]
    rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, b15, Proof.Ocb.nonceN_bottom _ _ (by omega) (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_store, gpr_setReg, hr.1, hr.2.1, ↓reduceIte]
    rw [O₃.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2]
    simp only [gpr_store, gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ↓reduceIte]
    exact R₁.gpr r (by simp [hr.1])
  · simp only [sp_store, sp_setReg]; rw [O₃.sp]; simp [sp_store, sp_setReg, R₁.sp]
  · simp only [rd_store, rd_setReg]; exact rd₃
  · simp only [wr_store, wr_setReg]; exact wr₃

end VG.Proof.AesOcb.Arm
