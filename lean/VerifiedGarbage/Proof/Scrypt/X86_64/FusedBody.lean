import VerifiedGarbage.Proof.Scrypt.X86_64.FusedTail
namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Scrypt.X86_64.Retained (Words Meta memWords)

/-- Lift only the core's actual writes into the established BlockMix frame. -/
theorem core_frame {s₀ : State} {off : Nat} {m m' : Mem}
    (hf : Frame [VG.Proof.Scrypt.X86_64.bR (yP s₀ + BitVec.ofNat 64 off), VG.Proof.Scrypt.X86_64.slotR (sc s₀),
      Retained.tempR (sc s₀)] m m') :
    Frame [slot s₀ off, ⟨sc s₀, 64⟩, stkR s₀] m m' := by
  apply hf.sub
  intro R hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact ⟨slot s₀ off, by simp, fun _ h => h⟩
  · exact ⟨⟨sc s₀, 64⟩, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨⟨sc s₀, 64⟩, by simp, by simpa only [Retained.tempR, bufAt, ofInt_natCast] using
      (Offset.sub_base (sc s₀) (d := 48) (n := 8) (k := 64) (by decide))⟩

theorem half_ok {s₀ s : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀)
    (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) {prev : Addr}
    (words : Words (sc s₀) (memWords s.mem prev) s)
    (metadata : Meta (sc s₀) (bB s₀ k) (yE s₀ k) (yO s₀ k) (BitVec.ofNat 64 (rr s₀ - k)) s.mem)
    (odd : Bool) :
    WP isa (fusedHalf (if odd then 64 else 0) odd) s fun t =>
      Words (sc s₀) (memWords t.mem (if odd then yO s₀ k else yE s₀ k)) t ∧
      bytesAt t.mem (if odd then yO s₀ k else yE s₀ k) 64 = Spec.Scrypt.salsa
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem prev 64)
          (bytesAt s.mem (bB s₀ k + BitVec.ofNat 64 (if odd then 64 else 0)) 64)) ∧
      Frame [VG.Proof.Scrypt.X86_64.bR (if odd then yO s₀ k else yE s₀ k), VG.Proof.Scrypt.X86_64.slotR (sc s₀),
        Retained.tempR (sc s₀)] s.mem t.mem ∧
      Meta (sc s₀) (bB s₀ k) (yE s₀ k) (yO s₀ k) (BitVec.ofNat 64 (rr s₀ - k)) t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rsp = s.gpr .rsp := by
  apply Retained.half_ok words metadata _ (by cases odd <;> simp) odd
  · rw [rd, wr, hp.rd, hp.wr]
    refine ⟨bR s₀, by simp, ?_⟩
    simp only [bB, Memory.add_ofNat]
    exact in_b hp (by cases odd <;> simp <;> omega)
  · rw [wr, hp.wr]
    refine ⟨yR s₀, by simp, ?_⟩
    cases odd <;> exact in_y hp (by omega)
  · rw [wr, hp.wr]
    exact ⟨scR s₀, by simp, by simpa only [BitVec.add_zero] using in_s s₀ (o := 0) (n := 64) (by decide)⟩
  · cases odd <;> exact slot_s hp (by omega)
  · simp only [bB, Memory.add_ofNat]
    cases odd <;> exact (yb_disj hp (by omega) (by simp; omega)).symm
  · simp only [bB, Memory.add_ofNat]
    exact (hp.b_s.sub_left (b_sub hp (by cases odd <;> simp <;> omega))).sub_right
      (Region.sub_prefix (by decide))

theorem body_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) :
    WP isa fusedBody s fun t => Inv s₀ (k + 1) t ∧
      t.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0) := by
  unfold fusedBody
  refine WP.seq (WP.mono (half_ok hp hk h.rd h.wr h.words h.metadata false) fun a ha => ?_)
  obtain ⟨wa, ba, fa, ma, ra, wra, spa⟩ := ha
  simp only [Bool.false_eq_true, ite_false, BitVec.add_zero] at wa ba fa
  refine WP.seq (WP.mono (half_ok hp hk (ra.trans h.rd) (wra.trans h.wr) wa ma true) fun b hb => ?_)
  obtain ⟨wb, bb, fb, mb, rb, wrb, spb⟩ := hb
  simp only [ite_true] at wb bb fb
  have baddr : bB s₀ k + BitVec.ofNat 64 64 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [bB, Memory.add_ofNat]; congr 2; omega
  rw [baddr] at bb
  obtain ⟨ff, saved, done⟩ := mem_ok hp hk h.toLogical.old (core_frame fa) ba (core_frame fb) bb
  have logical : Logical s₀ (k + 1) b :=
    ⟨by omega, rb.trans (ra.trans h.rd), wrb.trans (wra.trans h.wr), spb.trans (spa.trans h.rsp),
      ff, saved, done, by show bytesAt b.mem (yO s₀ k) 64 = _; rw [(done k (by omega)).2]; rfl⟩
  have hs : InRegions b.wr (sc s₀) 64 := by
    rw [logical.wr, hp.wr]; exact ⟨scR s₀, by simp, by simpa only [BitVec.add_zero] using in_s s₀ (o := 0) (n := 64) (by decide)⟩
  refine WP.mono (Retained.tail_ok wb.rsi hs mb) fun t ⟨ht, mt, hz⟩ => ?_
  have lt := r_lt hp
  have nextb : bB s₀ k + 128 = bB s₀ (k + 1) := by
    change bP s₀ + BitVec.ofNat 64 (128 * k) + BitVec.ofNat 64 128 = _
    rw [Memory.add_ofNat]; congr 2
  have nexte : yE s₀ k + 64 = yE s₀ (k + 1) := by
    change yP s₀ + BitVec.ofNat 64 (64 * k) + BitVec.ofNat 64 64 = _
    rw [Memory.add_ofNat]; congr 2
  have nexto : yO s₀ k + 64 = yO s₀ (k + 1) := by
    change yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + k)) + BitVec.ofNat 64 64 = _
    rw [Memory.add_ofNat]; congr 2
  have nextc : BitVec.ofNat 64 (rr s₀ - k) - 1 = BitVec.ofNat 64 (rr s₀ - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, Memory.toNat_ofNat_lt (by omega), Memory.toNat_ofNat_lt (by omega),
      show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  rw [nextb, nexte, nexto, nextc] at mt
  refine ⟨⟨logical.scratch hp ht.scratch ht.rd ht.wr (ht.keep _ (by decide)), ?_, mt⟩, hz⟩
  have mw := memWords_frame ht.scratch (p := yO s₀ k) (fun R hR => by
    simp only [List.mem_singleton] at hR; subst R; exact slot_s hp (by omega))
  change Words (sc s₀) (memWords t.mem (yO s₀ k)) t
  rw [mw]; exact wb.tail ht
end VG.Proof.Scrypt.X86_64.BlockMix.Fused
