import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeLoop
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLoop
import VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish
import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
import VerifiedGarbage.Proof.X448.Arm.Finish

/-!
# Ed448 verification's equation on ARMv7: the whole function

`vg_ed448_verify_equation(pk = r0, signature = r1, challenge = r2, scratch = r3)`
returns `verifyEquation` of its inputs (`verifyEquation_main`), given the
reference computations' agreement with the specification (`RecoverOk`,
`VerifyEqOk`): the entry, the bits of `S` and `k`, the check of `S`, `A`
decoded and negated, `Q = [S]B + [k](-A)` by the loop, `R` decoded, and the
comparison of `[4]Q` and `[4]R`. Every write is in the working space, so the
inputs are read unchanged; the callee-saved registers are restored from the
working space, and the return address is kept.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk VerifyEqOk vladder negPoint double verifyEquation_none)
open VG.Impl.X448.Arm (slot X2 BITS ACC TMP saved ld copy Op)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-! ## The bytes of the inputs -/

theorem bytesAt_take57 (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  simp [bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [bytesAt]) fun i _ _ => ?_
  simp only [bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt114_len (m : Mem) (p : Addr) : (bytesAt m p 114).length = 57 + 57 := by
  simp [bytesAt]

/-- Bytes far from the working space, after writes only to it. -/
theorem far_bytes {base p : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (by have := hf i (List.mem_range.mp hi); omega))

theorem far_bytes' {base p : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) : ∀ i < n,
      m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  fun i hi => h _ (Or.inr (by have := hf i hi; omega))

theorem outA {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : ACC ≤ o)
    (h2 : o + n ≤ ACC + 512) : Outside2 base 64 2816 ACC 512 m m' := fun p _ hq => h p (by omega)

/-! ## The entry and the start -/

theorem ventry_eq : ventry = setupHead ++
    ([.mov .r12 (.reg .r1), .str .lr .r0 LR] : List Instr) := rfl

theorem ventry_ok {s : State} {base : Addr} (hc : State.addr (s.gpr .r3) = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32) :
    WP isa (.block ventry) s fun t =>
      Scr t base ∧ t.gpr .r8 = s.gpr .r0 ∧ t.gpr .r12 = s.gpr .r1 ∧ t.gpr .r2 = s.gpr .r2 ∧
      Saved base s.gpr t.mem ∧ Outside base 0 (LR + 4) s.mem t.mem ∧ word t.mem base LR = s.gpr .lr ∧
      Keeps [.r10, .r0, .r6, .r8, .r12] s t := by
  rw [ventry_eq]
  refine VG.Proof.X25519.Arm.WP.append (setupHead_ok hc hw hn) fun v ⟨hsv, rv, _, svv, ov, kv⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun w hw' => ?_
  have k : Keeps [.r12] v w := rest_keeps (hw'.rest (by decide))
  have hsw := hsv.of_keeps k (by decide)
  refine VG.Proof.X25519.Arm.wp_str (a := off base LR) (by decide) (hsw.ea (by decide))
    (hsw.write (by decide)) fun t ht => WP.block_nil ?_
  have wv : w.mem = v.mem := hw'.mem
  have ot : Outside base LR 4 v.mem t.mem := by rw [ht.mem, wv]; exact writeW_outside _ _ _ (by decide)
  have kt : Keeps [] w t := ⟨fun r _ => by rw [ht.gpr], ht.rd, ht.wr⟩
  refine ⟨hsw.of_keeps kt (by decide), ?_, ?_, ?_, ?_, ?_, ?_,
    (kv.mono (by decide)).trans ((k.mono (by decide)).trans (kt.mono (by decide)))⟩
  · rw [ht.gpr, hw'.other _ (by decide), rv]
  · rw [ht.gpr, hw'.gpr, kv.1 _ (by decide)]
  · rw [ht.gpr, hw'.other _ (by decide), kv.1 _ (by decide)]
  · exact svv.outside ot (by decide)
  · exact (ov.mono (by decide) (by decide)).trans (ot.mono (by decide) (by decide))
  · show t.mem.readW (off base LR) 32 = _
    rw [ht.mem, Mem.readW_writeW_self32, hw'.other _ (by decide), kv.1 _ (by decide)]

theorem vstart_eq : vstart = .mov .r10 (.imm 0) :: (sCheck ++ (initSlots ++
    copy (slot (21 : Index).val) (slot (1 : Index).val))) := by
  simp only [vstart, List.append_assoc]; rfl

/-- `BAD = 0`, the check of `S` (at `sq`), and the slots initialized: `Q` the
neutral point, `B`, `1` in slot 10 and `d`. -/
theorem vstart_ok {s : State} {base sq : Addr} (hs : Scr s base)
    (hq : State.addr (s.gpr .r12) + BitVec.ofNat 64 57 = sq) (hfit : (s.gpr .r12).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (sq + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (sq + BitVec.ofNat 64 j)) :
    WP isa (.block vstart) s fun t =>
      CKeep base s t ∧ t.gpr .r12 = s.gpr .r12 ∧ BoundedEnv t.mem base ∧
      BadUpd (decodeLE (bytesAt s.mem sq 57) < Spec.Ed448.L) 0 (t.gpr .r10) ∧
      pt (E t.mem base) 0 21 2 = Spec.Ed448.identity ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 10 = 1 ∧ E t.mem base 11 = Spec.Ed448.d := by
  rw [vstart_eq]
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  have hsu := hs.of_upd hu (by decide) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (sCheck_ok hsu (by rw [hu.other _ (by decide)]; exact hq)
    (by rw [hu.other _ (by decide)]; exact hfit) (by rw [hu.rd, hu.wr]; exact hr) hd)
    fun v ⟨bv, ov, kv⟩ => ?_
  have hsv := hsu.of_keeps kv (by decide)
  refine VG.Proof.X25519.Arm.WP.append (initSlots_ok hsv) fun w ⟨lw, ow, kw⟩ => ?_
  have hsw := hsv.of_keeps kw (by decide)
  refine WP.mono (copyE3 hsw (initSlots_bounded lw) 21 1) fun t ⟨kt, k3, bt, et⟩ => ?_
  have ev : ∀ i : Index, i ≠ 21 → E t.mem base i = Proof.X448.toFe (initVal i.val) := fun i hi => by
    rw [et, opCopy, Function.update_of_ne hi, initSlots_E lw i]
  have e21 : E t.mem base 21 = Proof.X448.toFe (initVal 1) := by
    rw [et, opCopy, Function.update_self, initSlots_E lw 1]; rfl
  refine ⟨⟨?_, ?_⟩, ?_, bt, ?_, ?_, ?_, ?_, ?_⟩
  · refine (rest_keeps (hu.rest (ws := .r10 :: .r11 :: workRegs) (by decide))).trans
      ((kv.mono ?_).trans ((kw.mono ?_).trans (kt.regs.mono ?_))) <;> decide
  · rw [← hu.mem]
    exact ((outA ov (by decide) (by decide)).trans (outC ow (by decide) (by decide))).trans kt.mem
  · rw [k3.1 _ (by decide), kw.1 _ (by decide), kv.1 _ (by decide), hu.other _ (by decide)]
  · rw [hu.gpr] at bv
    rw [kt.regs.1 .r10 (by decide), kw.1 .r10 (by decide), ← hu.mem]
    exact bv
  · show (⟨E t.mem base 0, E t.mem base 21, E t.mem base 2⟩ : Spec.Ed448.Point) = _
    rw [ev 0 (by decide), e21, ev 2 (by decide), show ((0 : Index) : Nat) = 0 from rfl,
      show ((2 : Index) : Nat) = 2 from rfl, show initVal 0 = Spec.Ed448.identity.X.val from rfl,
      show initVal 1 = Spec.Ed448.identity.Y.val from rfl, show initVal 2 = Spec.Ed448.identity.Z.val from rfl,
      Proof.X448.toFe_self, Proof.X448.toFe_self, Proof.X448.toFe_self]
  · show (⟨E t.mem base 8, E t.mem base 9, E t.mem base 10⟩ : Spec.Ed448.Point) = _
    rw [ev 8 (by decide), ev 9 (by decide), ev 10 (by decide), show ((8 : Index) : Nat) = 8 from rfl,
      show ((9 : Index) : Nat) = 9 from rfl, show ((10 : Index) : Nat) = 10 from rfl,
      show initVal 8 = Spec.Ed448.basePoint.X.val from rfl, show initVal 9 = Spec.Ed448.basePoint.Y.val from rfl,
      show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self, Proof.X448.toFe_self,
      Proof.X448.toFe_self]
  · rw [ev 10 (by decide), show ((10 : Index) : Nat) = 10 from rfl,
      show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self]; rfl
  · rw [ev 11 (by decide), show ((11 : Index) : Nat) = 11 from rfl, show initVal 11 = Spec.Ed448.d.val from rfl,
      Proof.X448.toFe_self]

/-! ## The whole function -/

/-- The precondition of `vg_ed448_verify_equation`, by name. -/
structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 57⟩, ⟨State.addr (s.gpr .r1), 114⟩, ⟨State.addr (s.gpr .r2), 57⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r3), 8192⟩]
  pk_ws : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  sig_ws : (⟨State.addr (s.gpr .r1), 114⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  ch_ws : (⟨State.addr (s.gpr .r2), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  f0 : (s.gpr .r0).toNat + 57 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 114 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32

theorem BadUpd.zero {P : Prop} {b : BitVec 32} (h : BadUpd P 0 b) : (b = 0 ↔ P) ∧ b.toNat < 65536 := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  have e : (0 : BitVec 32) ||| c = c := BitVec.zero_or
  rw [e]
  exact ⟨hp, hc⟩

theorem bits_kept {base : Addr} {m m' : Mem} (h : DFrame base m m') :
    ∀ t < 456, m' (off base (VBITS + t)) = m (off base (VBITS + t)) := fun t ht =>
  h _ (by rw [ofs_off' base (by simp only [VBITS]; omega)]; simp only [VBITS]; omega)
    (by rw [ofs_off' base (by simp only [VBITS]; omega)]; simp only [VBITS, ACC]; omega)

/-- The link register's word, above `RY`, is kept by writes below `VBITS` or of the bits. -/
theorem lr_kept {base : Addr} {m m' : Mem} (h : DFrame base m m') : word m' base LR = word m base LR :=
  h.word (by decide) (by decide) (by decide)

theorem verifyEquation_main (hR : RecoverOk) (hE : VerifyEqOk) {s : State} (h : VerifyPre s) :
    WP isa verifyEquation s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.gpr .r0 = if Spec.Ed448.verifyEquation (bytesAt s.mem (State.addr (s.gpr .r0)) 57)
        (bytesAt s.mem (State.addr (s.gpr .r1)) 114) (bytesAt s.mem (State.addr (s.gpr .r2)) 57)
        then 1 else 0 := by
  obtain ⟨base, hbase⟩ : ∃ b, State.addr (s.gpr .r3) = b := ⟨_, rfl⟩
  obtain ⟨pk, hpk⟩ : ∃ p, State.addr (s.gpr .r0) = p := ⟨_, rfl⟩
  obtain ⟨sig, hsig⟩ : ∃ p, State.addr (s.gpr .r1) = p := ⟨_, rfl⟩
  obtain ⟨ch, hch⟩ : ∃ p, State.addr (s.gpr .r2) = p := ⟨_, rfl⟩
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [h.wr, hbase]; simp
  have rpk : ∀ j < 57, InRegions (s.rd ++ s.wr) (pk + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨pk, 57⟩, by rw [h.rd, hpk]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have rsg : ∀ j < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨sig, 114⟩, by rw [h.rd, hsig]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have rS : ∀ j < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 j) 1 :=
    fun j hj => ⟨⟨sig, 114⟩, by rw [h.rd, hsig]; simp,
      by rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have rch : ∀ j < 57, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨ch, 57⟩, by rw [h.rd, hch]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have fpk : ∀ j < 57, 8192 ≤ ofs base (pk + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hpk ▸ hbase ▸ h.pk_ws) hj (by decide)
  have fsg : ∀ j < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hsig ▸ hbase ▸ h.sig_ws) (by omega) (by decide)
  have fS : ∀ j < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 j) := fun j hj => by
    rw [Offset.add_add]; exact far_ws (hsig ▸ hbase ▸ h.sig_ws) (by omega) (by decide)
  have fch : ∀ j < 57, 8192 ≤ ofs base (ch + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hch ▸ hbase ▸ h.ch_ws) hj (by decide)
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 57) 57) = S := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, decodeLE (bytesAt s.mem ch 57) = K := ⟨_, rfl⟩
  unfold verifyEquation
  -- The entry.
  refine WP.seq (WP.mono (ventry_ok hbase hw₀ h.f3) fun s1 ⟨hs1, r81, r121, r21, sv1, o1, lr1, k1⟩ => ?_)
  have rr1 : s1.rd ++ s1.wr = s.rd ++ s.wr := by rw [k1.2.1, k1.2.2]
  have O1 : Outside base 0 8192 s.mem s1.mem := o1.mono (by decide) (by decide)
  -- The bits of `S` and `k`.
  refine WP.seq (WP.mono (vbits_ok hs1 (sq := sig + BitVec.ofNat 64 57) (kq := ch)
    (by rw [r121, hsig]) (by rw [r21, hch]) (by rw [r121]; exact h.f1) (by rw [r21]; exact h.f2)
    (by rw [rr1]; exact rS) (by rw [rr1]; exact rch) fS fch) fun s2 ⟨g2, rd2, wr2, o2, bits2⟩ => ?_)
  rw [far_bytes O1 fS, hS, far_bytes O1 fch, hK] at bits2
  have hs2 : Scr s2 base := hs1.of_keeps ⟨g2, rd2, wr2⟩ (by decide)
  have rr2 : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [rd2, wr2, rr1]
  have O2 : Outside base 0 8192 s.mem s2.mem := O1.trans (o2.mono (by decide) (by decide))
  have r122 : s2.gpr .r12 = s.gpr .r1 := by rw [g2 _ (by decide), r121]
  have r82 : s2.gpr .r8 = s.gpr .r0 := by rw [g2 _ (by decide), r81]
  -- `BAD = 0`, the check of `S`, and the slots.
  refine WP.seq (WP.mono (vstart_ok hs2 (sq := sig + BitVec.ofNat 64 57) (by rw [r122, hsig])
    (by rw [r122]; exact h.f1) (by rw [rr2]; exact rS) fS) fun s3 ⟨k3, r12s3, b3, c3, q3, p3, h103, h113⟩ => ?_)
  rw [far_bytes O2 fS, hS] at c3
  have hs3 := k3.scr hs2
  have rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by rw [k3.regs.2.1, k3.regs.2.2, rr2]
  have O3 : Outside base 0 8192 s.mem s3.mem := O2.trans (k3.mem.whole (by decide) (by decide))
  have r83 : s3.gpr .r8 = s.gpr .r0 := by rw [k3.regs.1 _ (by decide), r82]
  have r123 : s3.gpr .r12 = s.gpr .r1 := by rw [r12s3, r122]
  -- `R` and `A`.
  have inR : DecIn s3 base sig .r12 :=
    ⟨by rw [r123, hsig], by rw [r123]; have := h.f1; omega, by rw [rr3]; exact rsg, fsg⟩
  have inA : DecIn s3 base pk .r8 := ⟨by rw [r83, hpk], by rw [r83]; exact h.f0, by rw [rr3]; exact rpk, fpk⟩
  refine WP.seq (WP.mono (vdecode_ok hR hs3 b3 inR inA h103 h113)
    fun s4 ⟨k4, f4, b4, c4, v4, w4, bx4, by4, e4⟩ => ?_)
  rw [far_bytes O3 fsg, far_bytes O3 fpk] at c4
  rw [far_bytes O3 fsg] at w4
  rw [far_bytes O3 fpk] at v4
  have hs4 := hs3.of_keeps k4 (by decide)
  have O4 : Outside base 0 8192 s.mem s4.mem :=
    O3.trans fun p hp => f4 p (by omega) (by simp only [ACC]; omega)
  -- `-A`.
  rw [show ([.sub (slot 6) (slot 0) (slot 6)] : List Op) = ([.sub 6 0 6] : List FieldOp).map FieldOp.impl
    from rfl]
  refine WP.seq (WP.mono (ops_ok hs4 b4 [.sub 6 0 6]) fun s5 ⟨k5, b5, e5⟩ => ?_)
  have hs5 := k5.scr hs4
  have O5 : Outside base 0 8192 s.mem s5.mem := O4.trans (k5.mem.whole (by decide) (by decide))
  have k5' : ∀ i : Index, i ≠ 6 → E s5.mem base i = E s4.mem base i := fun i hi => by
    rw [e5]; exact Function.update_of_ne hi _ _
  have k43 : ∀ i : Index, i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) ∨ i.val = 21 →
      E s5.mem base i = E s3.mem base i := fun i hi => by
    rw [k5' i (fun h => by subst h; omega), e4 i (fun h => by subst h; omega) (fun h => by subst h; omega)
      (by omega)]
  -- The loop.
  have bits5 : ∀ t < 456, s5.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pair2 S K t) := fun t ht => by
    rw [bits_kept ((Outside2.widen k5.mem).mono (by decide) (by decide)) t ht, bits_kept f4 t ht,
      bits_kept ((Outside2.widen k3.mem).mono (by decide) (by decide)) t ht]
    exact bits2 t ht
  refine WP.seq (WP.mono (vloop_ok (s₀ := s5) (A := pt (E s5.mem base) 6 7 10) bits5
    (fun s' h1 h2 h3 h4 h5 => ?_)) fun s6 I6 => ?_)
  · have k' : Keeps (.r11 :: workRegs) s5 s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hs5.of_keeps k' (by decide), h3 ▸ b5, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [h3, Nat.sub_self, pt_congr' (k43 0 (by decide)) (k43 21 (by decide)) (k43 2 (by decide)), q3]
      rfl
    · rw [h3, pt_congr' (k43 8 (by decide)) (k43 9 (by decide)) (k43 10 (by decide)), p3]
    · rw [h3]
    · rw [h3, k43 11 (by decide), h113]
  -- `R` into slots 8–9.
  have hs6 := I6.scr
  have O6 : Outside base 0 8192 s.mem s6.mem := O5.trans (I6.mem.whole (by decide) (by decide))
  have lx6 : ∀ i < 28, limbs s6.mem base RX i = limbs s4.mem base RX i := fun i hi => by
    rw [limbs_mid I6.mem (by decide) (by decide) hi, limbs_mid k5.mem (by decide) (by decide) hi]
  have ly6 : ∀ i < 28, limbs s6.mem base RY i = limbs s4.mem base RY i := fun i hi => by
    rw [limbs_mid I6.mem (by decide) (by decide) hi, limbs_mid k5.mem (by decide) (by decide) hi]
  have h106 : E s6.mem base 10 = 1 := congrArg Spec.Ed448.Point.Z I6.q
  refine WP.seq (WP.mono (vR_ok hs6 I6.bounded (fun i hi => by rw [lx6 i hi]; exact bx4 i hi)
    (fun i hi => by rw [ly6 i hi]; exact by4 i hi)) fun s7 ⟨k7, b7, e78, e79, e7⟩ => ?_)
  have hs7 := k7.scr hs6
  -- `BAD`.
  have c4' : BadUpd ((Spec.Ed448.decodePoint (bytesAt s.mem sig 57)).isSome = true ∧
      (Spec.Ed448.decodePoint (bytesAt s.mem pk 57)).isSome = true) (s3.gpr .r10) (s7.gpr .r10) := by
    rw [k7.regs.1 .r10 (by decide), I6.regs.1 .r10 (by decide), k5.regs.1 .r10 (by decide)]; exact c4
  have c6 := c3.trans c4'
  -- The comparison.
  have sv7 : Saved base s.gpr s7.mem :=
    (((((sv1.outside o2 (by decide)).outside2 k3.mem (by decide) (by decide)).outside2 f4 (by decide)
      (by decide)).outside2 k5.mem (by decide) (by decide)).outside2 I6.mem (by decide) (by decide)).outside2
      k7.mem (by decide) (by decide)
  have lr7 : word s7.mem base LR = s.gpr .lr := by
    rw [lr_kept ((Outside2.widen k7.mem).mono (by decide) (by decide)),
      lr_kept ((Outside2.widen I6.mem).mono (by decide) (by decide)),
      lr_kept ((Outside2.widen k5.mem).mono (by decide) (by decide)), lr_kept f4,
      lr_kept ((Outside2.widen k3.mem).mono (by decide) (by decide)), o2.word (by decide) (by decide), lr1]
  have z7 := c6.zero
  refine WP.mono (vfinish_ok hs7 b7 sv7 z7.2) fun t ⟨rt, st, lt, gt⟩ => ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact st 0 (by decide)
    · exact st 1 (by decide)
    · exact st 2 (by decide)
    · exact st 3 (by decide)
    · exact st 4 (by decide)
    · exact st 5 (by decide)
    · exact st 6 (by decide)
    · exact st 7 (by decide)
    · rw [lt, lr7]
  · rw [rt, hpk, hsig, hch]
    refine if_congr ?_ rfl rfl
    rw [z7.1]
    cases ha : Spec.Ed448.decodePoint (bytesAt s.mem pk 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      exact ⟨fun h => absurd h.1.2.2 (by simp), fun h => absurd h (by decide)⟩
    | some a =>
      cases hr : Spec.Ed448.decodePoint ((bytesAt s.mem sig 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hr)]
        rw [bytesAt_take57] at hr
        exact ⟨fun h => absurd h.1.2.1 (by rw [hr]; decide), fun h => absurd h (by decide)⟩
      | some r =>
        have hr' := hr
        rw [bytesAt_take57] at hr'
        obtain ⟨ax, ay, az⟩ := v4 a ha
        obtain ⟨rx, ry, rz⟩ := w4 r hr'
        have e40 : E s4.mem base 0 = 0 := by
          rw [e4 0 (by decide) (by decide) (Or.inl rfl)]; exact congrArg Spec.Ed448.Point.X q3
        have e410 : E s4.mem base 10 = 1 := by
          rw [e4 10 (by decide) (by decide) (by decide)]; exact h103
        have hA : pt (E s5.mem base) 6 7 10 = negPoint a := by
          show (⟨E s5.mem base 6, E s5.mem base 7, E s5.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
          rw [show E s5.mem base 6 = E s4.mem base 0 - E s4.mem base 6 by rw [e5]; rfl,
            k5' 7 (by decide), k5' 10 (by decide), e40, ax, ay, e410, az]
        have hQ : pt (E s7.mem base) 0 21 2 = vladder S K (negPoint a) 456 := by
          rw [pt_congr' (e7 0 (by decide) (by decide)) (e7 21 (by decide) (by decide))
            (e7 2 (by decide) (by decide)), I6.rep, hA]
        have hRR : pt (E s7.mem base) 8 9 10 = r := by
          show (⟨E s7.mem base 8, E s7.mem base 9, E s7.mem base 10⟩ : Spec.Ed448.Point) = r
          rw [e78, e79, show F s6.mem base RX = F s4.mem base RX from
              congrArg Proof.X448.toFe (valN_congr lx6),
            show F s6.mem base RY = F s4.mem base RY from congrArg Proof.X448.toFe (valN_congr ly6), rx, ry,
            e7 10 (by decide) (by decide), h106, ← rz]
        rw [hE _ _ _ _ _ (bytesAt57_len _ _) (bytesAt114_len _ _) (bytesAt57_len _ _) ha hr, hQ, hRR,
          bytesAt_drop57, hS, hK, hr']
        simp only [Option.isSome_some, and_true, Bool.and_eq_true, decide_eq_true_eq]

end VG.Proof.Ed448.Arm
