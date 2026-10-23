module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.ChainPath
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Common
public import VerifiedGarbage.Spec.Cmac.TripleDesContract

/-!
# Streaming TDEA-CMAC on PPC64LE: `absorb` is correct

`absorb_wp`: `absorb` appends the data to the message the state
represents, through the path the flag chooses (`fill_spec`, `chain_spec`),
and restores the registers it saved.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.CmacTripleDes.Stream (held nblocks)

theorem take_bytesAt (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    (Spec.Aes.bytesAt m p n).take k = Spec.Aes.bytesAt m p k := by
  simp only [Spec.Aes.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem fill_spec {m m' : Mem} {S D : Addr} {key msg : List Byte} {len : Nat}
    (hr : Spec.Cmac.tdesRepr m S key msg) (hl : len ≤ 8 - held msg.length)
    (hc : Copied m D (S + BitVec.ofNat 64 (408 + held msg.length)) len m') :
    Spec.Cmac.tdesRepr m' S key (msg ++ Spec.Aes.bytesAt m D len) := by
  have hh := Proof.CmacTripleDes.Stream.held_le msg.length
  have ne : ∀ a, a < 408 + held msg.length → ∀ i < len,
      S + BitVec.ofNat 64 a ≠ S + BitVec.ofNat 64 (408 + held msg.length) + BitVec.ofNat 64 i := fun a ha i hi => by
    rw [VG.Offset.add_add]; exact VG.Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
  refine Proof.CmacTripleDes.Stream.repr_fill hr (fun i hi => hc.rest _ (ne i (by omega)))
    (by simp [Spec.Aes.bytesAt]; exact hl) ?_ ?_
  · rw [show S + 400 = S + BitVec.ofNat 64 400 from rfl]
    exact Proof.CmacTripleDes.Stream.bytesAt_congr fun i hi => by
      rw [VG.Offset.add_add]; exact hc.rest _ (ne _ (by omega))
  · have hlen : (Spec.Aes.bytesAt m D len).length = len := by simp [Spec.Aes.bytesAt]
    rw [hlen, show S + 408 = S + BitVec.ofNat 64 408 from rfl, Proof.Cmac.Stream.bytesAt_append, VG.Offset.add_add]
    congr 1
    · exact Proof.CmacTripleDes.Stream.bytesAt_congr fun i hi => by
        rw [VG.Offset.add_add]; exact hc.rest _ (ne _ (by omega))
    · exact List.map_congr_left fun i hi => hc.copied i (List.mem_range.mp hi)

theorem chain_spec {m m' : Mem} {S D : Addr} {key msg : List Byte} {len : Nat}
    (hr : Spec.Cmac.tdesRepr m S key msg) (hl : 8 - held msg.length < len)
    (hc : ChainMem m S D len (held msg.length) m') :
    Spec.Cmac.tdesRepr m' S key (msg ++ Spec.Aes.bytesAt m D len) := by
  have hh := Proof.CmacTripleDes.Stream.held_le msg.length
  have hlen : (Spec.Aes.bytesAt m D len).length = len := by simp [Spec.Aes.bytesAt]
  have hnb : nblocks msg.length len = nbOf len (8 - held msg.length) := rfl
  have hnb8 : 8 * nbOf len (8 - held msg.length) ≤ len - (8 - held msg.length) - 1 := by
    show 8 * ((len - (8 - held msg.length) - 1) / 8) ≤ _; omega
  refine Proof.CmacTripleDes.Stream.repr_chain hr hc.key (by rw [hlen]; exact hl) ?_ ?_
  · rw [show S + 400 = S + BitVec.ofNat 64 400 from rfl, show S + 408 = S + BitVec.ofNat 64 408 from rfl,
      hc.chain, hr.2.1, hlen, hnb, take_bytesAt _ _ (by omega), ← Proof.Cmac.Stream.bytesAt_offset _ _ (by omega),
      Proof.CmacTripleDes.Stream.blocksAt_eq]
    rfl
  · rw [show S + 408 = S + BitVec.ofNat 64 408 from rfl, hlen, hnb, List.drop_drop]
    have e := hc.held
    rw [Proof.Cmac.Stream.bytesAt_offset m D (n := len) (by
      show 8 - held msg.length + 8 * nbOf len (8 - held msg.length) +
        (len - (8 - held msg.length) - 8 * nbOf len (8 - held msg.length)) ≤ len; omega)] at e
    exact e.trans (List.take_of_length_le (by
      rw [List.length_drop, hlen]
      show len - _ ≤ len - (8 - held msg.length) - 8 * nbOf len (8 - held msg.length); omega))

/-- What `absorb` leaves, for a state that represents a message of `count`
bytes. -/
def AbsorbOut (m : Mem) (S D : Addr) (count len : Nat) (m' : Mem) : Prop :=
  ∀ key msg, Spec.Cmac.tdesRepr m S key msg → msg.length = count →
    Spec.Cmac.tdesRepr m' S key (msg ++ Spec.Aes.bytesAt m D len)

theorem absorb_wp (s : State) (hp : AbsorbPre s) :
    WP isa absorb s fun f => (∀ r ∈ preserved, f.gpr r = s.gpr r) ∧ f.lr = s.lr ∧
      AbsorbOut s.mem (s.gpr .r3) (s.gpr .r5) (s.gpr .r4).toNat (s.gpr .r6).toNat f.mem := by
  have hW : (⟨s.gpr .r7, 688⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hS : (⟨s.gpr .r3, 416⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hDr : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  have hfW := hp.scrFit
  have hh := Proof.CmacTripleDes.Stream.held_le (s.gpr .r4).toNat
  have cW : ∀ off, off + 8 ≤ 688 → (⟨s.gpr .r7, 688⟩ : Region).Contains (s.gpr .r7 + BitVec.ofNat 64 off) (64 / 8) :=
    fun off h => VG.Offset.contains_base _ h (by omega)
  unfold absorb
  refine WP.seq ?_
  rw [← List.append_nil absorbSave]
  refine absorbSave_wp hp fun t ht => wp_nil ?_
  have F0 : Frame [⟨s.gpr .r7, 688⟩] s.mem t.mem := by
    rw [ht.mem]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (cW lrOff (by decide))).writeW List.mem_cons_self _
      (cW r29Off (by decide))).writeW List.mem_cons_self _ (cW r30Off (by decide))).writeW List.mem_cons_self _
      (cW r31Off (by decide))
  refine WP.seq (heldCode_wp (s.gpr .r4).isLt (by rw [ht.regs _ (by decide) (by decide) (by decide),
    BitVec.ofNat_toNat, BitVec.setWidth_eq]) fun t₁ h8 g₁ m₁ rd₁ wr₁ => ?_)
  refine WP.seq ?_
  rw [← List.append_nil absorbFlag]
  refine flag_wp hh (s.gpr .r6).isLt (len := (s.gpr .r6).toNat) h8 (by
    rw [g₁ _ (by decide) (by decide), ht.regs _ (by decide) (by decide) (by decide), BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) fun u r9 ev gu mu rdu wru => wp_nil ?_
  have gu' : ∀ r, r ≠ .r0 → r ≠ .r5 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r29 → u.gpr r = s.gpr r :=
    fun r h0 h5 h8 h9 h10 h11 h29 => by rw [gu r h9 h10 h11, g₁ r h8 h9, ht.regs r h0 h5 h29]
  have rdu' : u.rd = s.rd := by rw [rdu, rd₁, ht.rd]
  have wru' : u.wr = s.wr := by rw [wru, wr₁, ht.wr]
  have he : PathEnv u (s.gpr .r3) (s.gpr .r5) (s.gpr .r7) (s.gpr .r6).toNat (held (s.gpr .r4).toNat) :=
    { r3 := gu' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r5 := by rw [gu _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), ht.r5]
      r6 := by
        rw [gu' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          BitVec.ofNat_toNat, BitVec.setWidth_eq]
      r8 := by rw [gu _ (by decide) (by decide) (by decide), h8]
      r9 := r9
      r29 := by rw [gu _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), ht.r29]
      hh := hh
      lenLt := (s.gpr .r6).isLt
      data := by rw [rdu']; exact hDr
      state := by rw [wru']; exact hS
      scr := by rw [wru']; exact hW
      dataState := hp.dataState
      dataScr := hp.dataScr
      stateScr := hp.stateScr
      stateFit := hp.stateFit
      dataFit := hp.dataFit
      scrFit := hp.scrFit }
  -- The data and the state's bytes are as they were before the saves.
  have hmu : u.mem = t.mem := by rw [mu, m₁]
  have stEq : ∀ i < 416, u.mem (s.gpr .r3 + BitVec.ofNat 64 i) = s.mem (s.gpr .r3 + BitVec.ofNat 64 i) :=
    fun i hi => by
      rw [hmu]; exact F0.bytes (R := ⟨s.gpr .r3, 416⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.stateScr) (by show 416 ≤ 2 ^ 64; decide) hi
  have dEq : Spec.Aes.bytesAt u.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Aes.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat :=
    List.map_congr_left fun i hi => by
      rw [hmu]; exact F0.bytes (R := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dataScr)
        (by show (s.gpr .r6).toNat ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
  have hb : WP isa (.ite (.nonzero .d .r10) chainPath fillPath) u fun v =>
      PathOut u (s.gpr .r3) (s.gpr .r7) v ∧
        AbsorbOut s.mem (s.gpr .r3) (s.gpr .r5) (s.gpr .r4).toNat (s.gpr .r6).toNat v.mem := by
    by_cases hc : 8 - held (s.gpr .r4).toNat < (s.gpr .r6).toNat
    · refine WP.ite true (by rw [ev, decide_eq_true hc]) (fun _ => ?_) (fun h => by cases h)
      refine WP.mono (chain_wp he hc) fun v ⟨po, cm⟩ => ⟨po, fun key msg hr hn => ?_⟩
      rw [← dEq]
      rw [← hn] at hc cm
      exact chain_spec (Proof.CmacTripleDes.Stream.repr_congr_416 stEq hr) hc cm
    · refine WP.ite false (by rw [ev, decide_eq_false hc]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (fill_wp he (by omega)) fun v ⟨po, cp⟩ => ⟨po, fun key msg hr hn => ?_⟩
      rw [← dEq]
      rw [← hn] at hc cp
      exact fill_spec (Proof.CmacTripleDes.Stream.repr_congr_416 stEq hr) (by omega) cp
  refine WP.seq (WP.mono hb fun v hv => ?_)
  obtain ⟨po, out⟩ := hv
  -- The saved registers, back.
  have slot : ∀ off, 528 ≤ off → off + 8 ≤ 688 →
      v.mem.readW (s.gpr .r7 + BitVec.ofNat 64 off) 64 = t.mem.readW (s.gpr .r7 + BitVec.ofNat 64 off) 64 :=
    fun off h1 h2 => by
      rw [po.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hp.stateScr.sub_right (VG.Offset.sub_base _ h2)).symm
        · exact VG.Offset.disjoint_base _ (by omega) (by omega)) (by decide), hmu]
  have hR : ∀ (w : State), w.rd = s.rd → w.wr = s.wr → ∀ off, off + 8 ≤ 688 →
      InRegions (w.rd ++ w.wr) (s.gpr .r7 + BitVec.ofNat 64 off) 8 := fun w hrd hwr off h => by
    rw [hrd, hwr]; exact ⟨_, List.mem_append_right _ hW, VG.Offset.contains_base _ h (by omega)⟩
  have v5 : v.gpr .r5 = s.gpr .r7 := po.r5
  have rdv : v.rd = s.rd := by rw [po.rd, rdu']
  have wrv : v.wr = s.wr := by rw [po.wr, wru']
  simp only [absorbRestore]
  refine wp_ld (a := s.gpr .r7 + BitVec.ofNat 64 lrOff) (by decide) (by decide) (by rw [v5])
    (hR _ rdv wrv _ (by decide)) fun w₁ x₁ => ?_
  refine wp_ld (a := s.gpr .r7 + BitVec.ofNat 64 r29Off) (by decide) (by decide) (by rw [x₁.other _ (by decide), v5])
    (hR _ (by rw [x₁.rd, rdv]) (by rw [x₁.wr, wrv]) _ (by decide)) fun w₂ x₂ => ?_
  refine wp_ld (a := s.gpr .r7 + BitVec.ofNat 64 r30Off) (by decide) (by decide)
    (by rw [x₂.other _ (by decide), x₁.other _ (by decide), v5])
    (hR _ (by rw [x₂.rd, x₁.rd, rdv]) (by rw [x₂.wr, x₁.wr, wrv]) _ (by decide)) fun w₃ x₃ => ?_
  refine wp_ld (a := s.gpr .r7 + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [x₃.other _ (by decide), x₂.other _ (by decide), x₁.other _ (by decide), v5])
    (hR _ (by rw [x₃.rd, x₂.rd, x₁.rd, rdv]) (by rw [x₃.wr, x₂.wr, x₁.wr, wrv]) _ (by decide)) fun w₄ x₄ =>
      wp_mtlr (wp_nil ?_)
  have mw : w₄.mem = v.mem := by rw [x₄.mem, x₃.mem, x₂.mem, x₁.mem]
  have sl : ∀ off, (off = lrOff ∨ off = r29Off ∨ off = r30Off ∨ off = r31Off) →
      v.mem.readW (s.gpr .r7 + BitVec.ofNat 64 off) 64 = t.mem.readW (s.gpr .r7 + BitVec.ofNat 64 off) 64 := by
    rintro off (rfl | rfl | rfl | rfl) <;> exact slot _ (by decide) (by decide)
  have dj : ∀ a b, a + 8 ≤ b ∨ b + 8 ≤ a → b + 8 ≤ 688 → a + 8 ≤ 688 →
      Region.Disjoint ⟨s.gpr .r7 + BitVec.ofNat 64 a, 8⟩ ⟨s.gpr .r7 + BitVec.ofNat 64 b, 8⟩ :=
    fun a b h hb ha => VG.Offset.disjoint _ h (by omega) (by omega)
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · show w₄.gpr r = _
    by_cases e31 : r = .r31
    · subst e31
      rw [x₄.gpr, x₃.mem, x₂.mem, x₁.mem, sl _ (by simp), ht.mem, Mem.readW_writeW_self64]
    by_cases e30 : r = .r30
    · subst e30
      rw [x₄.other _ (by decide), x₃.gpr, x₂.mem, x₁.mem, sl _ (by simp), ht.mem,
        readW_sep64 (dj _ _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
    by_cases e29 : r = .r29
    · subst e29
      rw [x₄.other _ (by decide), x₃.other _ (by decide), x₂.gpr, x₁.mem, sl _ (by simp), ht.mem,
        readW_sep64 (dj _ _ (by decide) (by decide) (by decide)),
        readW_sep64 (dj _ _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
    obtain ⟨h0, -, -, h5, -, -, h8, h9, h10, h11, -⟩ := preserved_ne r hr
    rw [x₄.other r e31, x₃.other r e30, x₂.other r e29, x₁.other r h0, po.regs r hr e29 e30 e31,
      gu' r h0 h5 h8 h9 h10 h11 e29]
  · show w₄.gpr .r0 = _
    rw [x₄.other _ (by decide), x₃.other _ (by decide), x₂.other _ (by decide), x₁.gpr, sl _ (by simp), ht.mem,
      readW_sep64 (dj _ _ (by decide) (by decide) (by decide)),
      readW_sep64 (dj _ _ (by decide) (by decide) (by decide)),
      readW_sep64 (dj _ _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · show AbsorbOut _ _ _ _ _ w₄.mem
    rw [mw]; exact out

end VG.Proof.CmacTripleDes.Stream.PPC64LE
