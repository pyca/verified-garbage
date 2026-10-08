import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode

/-!
# Ed448 verification's equation on ARMv7: decoding `R` and `A`

`vdecode_ok`: `vdecode` decodes the point at `r12` (`R`), then the one at
`r8` (`A`), each into slots 6–7 (`decode_ok`),
after keeping slots 6–7 at `RX` and `RY` (`stash_ok`): `A` ends in slots 6–7
and `R` at `RX` and `RY`, and `BAD` records both checks. Its writes are in the
working space below `VBITS` or in the multiplication's area (`DFrame`).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk)
open VG.Impl.X448.Arm (slot ACC copy)
open VG.Spec.Ed448 (bytesAt decodePoint)

/-- Writes only in the working space below `VBITS` (from the saved registers on) or in the
multiplication's area. -/
abbrev DFrame (base : Addr) (m m' : Mem) : Prop := Outside2 base 32 3072 ACC 512 m m'

theorem VKeep.dframe {base : Addr} {s t : State} (h : VKeep base s t) : DFrame base s.mem t.mem :=
  h.mem.mono (by decide) (by decide)

/-- Limbs between the slots and the multiplication's area are kept by a decoding. -/
theorem limbs_above {base : Addr} {m m' : Mem} (h : Outside2 base 32 2848 ACC 512 m m') {d : Nat}
    (hd : 2880 ≤ d) (hd' : d + 112 ≤ 3584) {i : Nat} (hi : i < 28) :
    limbs m' base d i = limbs m base d i :=
  congrArg BitVec.toNat (h.word (Or.inr (by omega)) (Or.inl (by simp only [ACC]; omega)) (by omega))

/-- `R`'s place, from the slots. -/
theorem stash_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (copy RX (slot 6) ++ copy RY (slot 7))) s fun t =>
      Keeps [.r3] s t ∧ Outside base RX 224 s.mem t.mem ∧
      (∀ i < 28, limbs t.mem base RX i = limbs s.mem base (slot 6) i) ∧
      (∀ i < 28, limbs t.mem base RY i = limbs s.mem base (slot 7) i) := by
  refine VG.Proof.X25519.Arm.WP.append (copy3_ok hs (by decide) (by decide) (Or.inr (Or.inr (by decide))))
    fun u ⟨uf, uo, uk⟩ => ?_
  have hu := hs.of_keeps uk (by decide)
  refine WP.mono (copy3_ok hu (by decide) (by decide) (Or.inr (Or.inr (by decide)))) fun t ⟨tf, to, tk⟩ =>
    ⟨uk.trans tk, (uo.mono (by decide) (by decide)).trans (to.mono (by decide) (by decide)), fun i hi => ?_,
      fun i hi => ?_⟩
  · rw [to.limbs (by decide) (by decide) hi]; exact uf i hi
  · rw [tf i hi]; exact uo.limbs (by decide) (by decide) hi

/-- Slots below `RX` are kept by writes from it on. -/
theorem stash_E {base : Addr} {m m' : Mem} (h : Outside base RX 224 m m') (i : Index) :
    E m' base i = E m base i := by
  have := i.isLt
  show F m' base (slot i.val) = F m base (slot i.val)
  exact congrArg Proof.X448.toFe (h.fe (d := slot i.val) (Or.inl (by simp only [RX, slot]; omega))
    (by simp only [slot]; omega))

theorem stash_bounded {base : Addr} {m m' : Mem} (h : Outside base RX 224 m m') (hb : BoundedEnv m base) :
    BoundedEnv m' base := fun i j hj => by
  have := i.isLt
  rw [h.limbs (Or.inl (by simp only [RX, slot]; omega)) (by simp only [slot]; omega) hj]
  exact hb i j hj

/-- What an iteration's input needs: the point's bytes at `q`, readable and away from the
working space. -/
structure DecIn (s : State) (base q : Addr) (p : Reg) : Prop where
  addr : State.addr (s.gpr p) = q
  fit : (s.gpr p).toNat + 57 ≤ 2 ^ 32
  rd : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1
  far : ∀ j < 57, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)

theorem DecIn.keep {s t : State} {base q : Addr} {p : Reg} (h : DecIn s base q p) {rs : List Reg}
    (hk : Keeps rs s t) (hp : p ∉ rs) : DecIn t base q p :=
  ⟨by rw [hk.1 _ hp]; exact h.addr, by rw [hk.1 _ hp]; exact h.fit,
    by rw [hk.2.1, hk.2.2]; exact h.rd, h.far⟩

theorem DecIn.move {s t : State} {base q : Addr} {p p' : Reg} (h : DecIn s base q p)
    (he : t.gpr p' = s.gpr p) (hr : t.rd ++ t.wr = s.rd ++ s.wr) : DecIn t base q p' :=
  ⟨by rw [he]; exact h.addr, by rw [he]; exact h.fit, by rw [hr]; exact h.rd, h.far⟩

/-- Bytes away from the working space are kept by writes in it. -/
theorem DFrame.bytes {base q : Addr} {m m' : Mem} (h : DFrame base m m')
    (hf : ∀ j < 57, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) : bytesAt m' q 57 = bytesAt m q 57 := by
  simp only [bytesAt]
  exact List.map_congr_left fun j hj => by
    have := hf j (List.mem_range.mp hj)
    exact h _ (Or.inr (by omega)) (Or.inr (by simp only [ACC]; omega))

/-- One decoding: slots 6–7 kept at `RX` and `RY`, the point at `p` decoded into them. -/
theorem vdecodeBody_ok (hR : RecoverOk) {s : State} {base q : Addr} (hs : Scr s base)
    (hb : BoundedEnv s.mem base) {p : Reg} (hp : p = .r8 ∨ p = .r12) (hin : DecIn s base q p)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (vdecodeBody p) s fun t =>
      Keeps (.r10 :: .r11 :: workRegs) s t ∧ DFrame base s.mem t.mem ∧
      BoundedEnv t.mem base ∧
      (∀ i < 28, limbs t.mem base RX i = limbs s.mem base (slot 6) i) ∧
      (∀ i < 28, limbs t.mem base RY i = limbs s.mem base (slot 7) i) ∧
      BadUpd ((decodePoint (bytesAt s.mem q 57)).isSome) (s.gpr .r10) (t.gpr .r10) ∧
      (∀ a, decodePoint (bytesAt s.mem q 57) = some a →
        E t.mem base 6 = a.X ∧ E t.mem base 7 = a.Y ∧ a.Z = 1) ∧
      (∀ i : Index, i ≠ 6 → i ≠ 7 → (i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) ∨ i.val = 21) →
        E t.mem base i = E s.mem base i) := by
  have hpc : p ∉ [.r3] := by rcases hp with rfl | rfl <;> decide
  unfold vdecodeBody
  -- slots 6–7 kept
  refine WP.seq (WP.mono (stash_ok hs) fun s1 ⟨k1, o1, x1, y1⟩ => ?_)
  have hs1 := hs.of_keeps k1 (by decide)
  have e1 : ∀ i : Index, E s1.mem base i = E s.mem base i := stash_E o1
  have in1 := hin.keep k1 hpc
  have byt1 : bytesAt s1.mem q 57 = bytesAt s.mem q 57 := by
    simp only [bytesAt]
    exact List.map_congr_left fun j hj => o1 _ (Or.inr (by
      have := hin.far j (List.mem_range.mp hj); simp only [RX]; omega))
  -- the decoding
  refine WP.mono (decode_ok hR hs1 (stash_bounded o1 hb) (p := p) hp in1.addr in1.fit
    in1.rd in1.far 6 7 (Or.inl ⟨rfl, rfl⟩) (by rw [e1]; exact h10) (by rw [e1]; exact h11))
    fun t ⟨k2, b2, c2, v2, e2⟩ => ?_
  rw [byt1] at c2 v2
  refine ⟨(k1.mono (by decide)).trans (k2.regs.mono (by decide)), ?_, b2, fun i hi => ?_, fun i hi => ?_,
    ?_, v2, fun i h6 h7 hi => ?_⟩
  · exact Outside2.trans (show DFrame base s.mem s1.mem from fun p h1 _ => o1 p (by unfold RX; omega))
      (VKeep.dframe k2)
  · rw [limbs_above k2.mem (by decide) (by decide) hi]; exact x1 i hi
  · rw [limbs_above k2.mem (by decide) (by decide) hi]; exact y1 i hi
  · rw [← k1.1 .r10 (by decide)]; exact c2
  · rw [e2 i h6 h7 (by omega), e1]

/-- `R` (at `r12`) and then `A` (at `r8`) decoded: `A` into slots 6–7, `R` at `RX` and `RY`. -/
theorem vdecode_ok (hR : RecoverOk) {s : State} {base qR qA : Addr} (hs : Scr s base)
    (hb : BoundedEnv s.mem base) (inR : DecIn s base qR .r12) (inA : DecIn s base qA .r8)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa vdecode s fun t =>
      Keeps (.r10 :: .r11 :: workRegs) s t ∧ DFrame base s.mem t.mem ∧
      BoundedEnv t.mem base ∧
      BadUpd ((decodePoint (bytesAt s.mem qR 57)).isSome ∧ (decodePoint (bytesAt s.mem qA 57)).isSome)
        (s.gpr .r10) (t.gpr .r10) ∧
      (∀ a, decodePoint (bytesAt s.mem qA 57) = some a →
        E t.mem base 6 = a.X ∧ E t.mem base 7 = a.Y ∧ a.Z = 1) ∧
      (∀ r, decodePoint (bytesAt s.mem qR 57) = some r →
        F t.mem base RX = r.X ∧ F t.mem base RY = r.Y ∧ r.Z = 1) ∧
      Bounded t.mem base RX ∧ Bounded t.mem base RY ∧
      (∀ i : Index, i ≠ 6 → i ≠ 7 → (i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) ∨ i.val = 21) →
        E t.mem base i = E s.mem base i) := by
  unfold vdecode
  -- `R`
  refine WP.seq (WP.mono (vdecodeBody_ok hR hs hb (.inr rfl) inR h10 h11)
    fun t ⟨kt, ft, bt, _, _, ct, vt, et⟩ => ?_)
  have ht := hs.of_keeps kt (by decide)
  have h10' : E t.mem base 10 = 1 := by rw [et 10 (by decide) (by decide) (by decide)]; exact h10
  have h11' : E t.mem base 11 = Spec.Ed448.d := by rw [et 11 (by decide) (by decide) (by decide)]; exact h11
  -- `A`
  refine WP.mono (vdecodeBody_ok hR ht bt (.inl rfl) (inA.keep kt (by decide)) h10' h11')
    fun u ⟨ku, fu, bu, xu, yu, cu, vu, eu⟩ => ?_
  have byA : bytesAt t.mem qA 57 = bytesAt s.mem qA 57 := ft.bytes inA.far
  rw [byA] at cu vu
  refine ⟨kt.trans ku, ft.trans fu, bu, ct.trans cu, vu, fun r hr => ?_,
    fun i hi => by rw [xu i hi]; exact bt 6 i hi, fun i hi => by rw [yu i hi]; exact bt 7 i hi,
    fun i h6 h7 hi => by rw [eu i h6 h7 hi]; exact et i h6 h7 hi⟩
  obtain ⟨rx, ry, rz⟩ := vt r hr
  exact ⟨(congrArg Proof.X448.toFe (valN_congr xu)).trans rx,
    (congrArg Proof.X448.toFe (valN_congr yu)).trans ry, rz⟩

/-! ## `R` into slots 8–9 -/

/-- Limbs between the slots and the multiplication's area are kept by field operations. -/
theorem limbs_mid {base : Addr} {m m' : Mem} (h : Outside2 base 64 2816 ACC 512 m m') {d : Nat}
    (hd : 2880 ≤ d) (hd' : d + 112 ≤ 3584) {i : Nat} (hi : i < 28) :
    limbs m' base d i = limbs m base d i :=
  limbs_above (Outside2.widen h) hd hd' hi

/-- A slot from a place above the slots. -/
theorem copyFrom_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o : Index)
    {a : Nat} (ha1 : 2880 ≤ a) (ha2 : a + 112 ≤ 3584) (hba : Bounded s.mem base a) :
    WP isa (.block (copy (slot o.val) a)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = Function.update (E s.mem base) o (F s.mem base a) := by
  have sep : slot o.val + 112 ≤ a := by have := o.isLt; simp only [slot]; omega
  refine WP.mono (copy_ok hs (Nat.le_trans (slot_bound o) (by decide)) (by omega) (Or.inr (Or.inl sep)))
    fun t ⟨tf, tm, tk⟩ => ?_
  have op : Op base (slot o.val) s t := ⟨tk, FieldMem.output tm⟩
  refine ⟨op.keep, bounded_update op.mem hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hba i hi
  · rw [E_update op.mem, show F t.mem base (slot o.val) = F s.mem base a from
      congrArg Proof.X448.toFe (valN_congr tf)]

theorem vR_eq : vR = copy (slot (8 : Index).val) RX ++ copy (slot (9 : Index).val) RY := rfl

/-- `R`, at `RX` and `RY`, into slots 8–9. -/
theorem vR_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hx : Bounded s.mem base RX) (hy : Bounded s.mem base RY) :
    WP isa (.block vR) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base 8 = F s.mem base RX ∧
      E t.mem base 9 = F s.mem base RY ∧ ∀ i : Index, i ≠ 8 → i ≠ 9 → E t.mem base i = E s.mem base i := by
  rw [vR_eq]
  refine VG.Proof.X25519.Arm.WP.append (copyFrom_ok hs hb 8 (by decide) (by decide) hx)
    fun u ⟨ku, bu, eu⟩ => ?_
  have ly : ∀ i < 28, limbs u.mem base RY i = limbs s.mem base RY i :=
    fun i hi => limbs_mid ku.mem (by decide) (by decide) hi
  refine WP.mono (copyFrom_ok (ku.scr hs) bu 9 (by decide) (by decide) (fun i hi => by rw [ly i hi]; exact hy i hi))
    fun t ⟨kt, bt, et⟩ => ⟨ku.trans kt, bt, ?_, ?_, fun i h8 h9 => ?_⟩
  · rw [et, Function.update_of_ne (by decide), eu, Function.update_self]
  · rw [et, Function.update_self]; exact congrArg Proof.X448.toFe (valN_congr ly)
  · rw [et, Function.update_of_ne h9, eu, Function.update_of_ne h8]

end VG.Proof.Ed448.Arm
