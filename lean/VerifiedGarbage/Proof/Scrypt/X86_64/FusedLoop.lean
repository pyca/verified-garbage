import VerifiedGarbage.Proof.Scrypt.X86_64.Retained
import VerifiedGarbage.Proof.Scrypt.X86_64.BlockMixCT

/-! Public loop metadata for the scalar core's retained-state BlockMix loop. -/
namespace VG.Proof.Scrypt.X86_64.Retained
open VG VG.X86_64 VG.Impl.Scrypt.X86_64

structure Meta (p b e o count : Addr) (m : Mem) : Prop where
  input : m.readW (bufAt p 16) 64 = b
  even : m.readW (bufAt p 24) 64 = e
  odd : m.readW (bufAt p 32) 64 = o
  count : m.readW (bufAt p 40) 64 = count

theorem meta_disjoint (p : Addr) {off : Nat} (h : off = 16 ∨ off = 24 ∨ off = 32 ∨ off = 40) :
    (⟨bufAt p off, 8⟩ : Region).Disjoint (slotR p) ∧
      (⟨bufAt p off, 8⟩ : Region).Disjoint (tempR p) := by
  have first : (⟨bufAt p off, 8⟩ : Region).Disjoint (slotR p) := by
    simpa [bufAt, ofInt_natCast, slotR] using
      (Offset.disjoint p (d := off) (n := 8) (e := 0) (k := 16)
        (by rcases h with rfl | rfl | rfl | rfl <;> decide)
        (by rcases h with rfl | rfl | rfl | rfl <;> decide) (by decide))
  refine ⟨first, ?_⟩
  simpa only [bufAt, ofInt_natCast, tempR] using
    (Offset.disjoint p (d := off) (n := 8) (e := 48) (k := 8)
      (by rcases h with rfl | rfl | rfl | rfl <;> decide)
      (by rcases h with rfl | rfl | rfl | rfl <;> decide) (by decide))

theorem Meta.frame {p b e o count d : Addr} {m m' : Mem} (h : Meta p b e o count m)
    (hd : (bR d).Disjoint (scR p))
    (hf : Frame [bR d, slotR p, tempR p] m m') : Meta p b e o count m' := by
  have keep : ∀ off, (off = 16 ∨ off = 24 ∨ off = 32 ∨ off = 40) →
      m'.readW (bufAt p off) 64 = m.readW (bufAt p off) 64 := by
    intro off ho
    have sub : Region.Sub ⟨bufAt p off, 8⟩ (scR p) := by
      simpa only [bufAt, ofInt_natCast] using Offset.sub_base p (d := off) (n := 8) (k := 64)
        (by rcases ho with rfl | rfl | rfl | rfl <;> decide)
    refine hf.readW (Region.contains_self _ _) (fun R hR => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact hd.symm.sub_left sub
    · exact (meta_disjoint p ho).1
    · exact (meta_disjoint p ho).2
  exact ⟨(keep 16 (by simp)).trans h.input, (keep 24 (by simp)).trans h.even,
    (keep 32 (by simp)).trans h.odd, (keep 40 (by simp)).trans h.count⟩

open VG.Spec.Scrypt (Word bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)

def memWords (m : Mem) (p : Addr) : Vector Word 16 :=
  Vector.ofFn fun j => m.readW (bufAt p (4 * j.1)) 32

theorem word_xor (a b : List Byte) (ha : a.length = 64) (hb : b.length = 64) {j : Nat} (hj : j < 16) :
    Spec.Scrypt.wordLE (xorBytes a b) j = Spec.Scrypt.wordLE a j ^^^ Spec.Scrypt.wordLE b j := by
  have get : ∀ k < 64, (xorBytes a b).getD k 0 = a.getD k 0 ^^^ b.getD k 0 := by
    intro k hk
    rw [← List.getElem_eq_getD (h := by simp only [xorBytes, List.length_zipWith, ha, hb]; omega),
      ← List.getElem_eq_getD (l := a) (i := k) (h := by omega), ← List.getElem_eq_getD (l := b) (i := k) (h := by omega)]
    exact List.getElem_zipWith
  simp only [Spec.Scrypt.wordLE, get _ (by omega : 4 * j + 3 < 64),
    get _ (by omega : 4 * j + 2 < 64), get _ (by omega : 4 * j + 1 < 64),
    get _ (by omega : 4 * j < 64)]
  ext i
  simp only [BitVec.getElem_append, BitVec.getElem_xor]
  by_cases h0 : i < 8
  · simp only [h0, dite_true]
  · simp only [h0, dite_false]
    by_cases h1 : i - 8 < 8
    · simp only [h1, dite_true]
    · simp only [h1, dite_false]
      by_cases h2 : i - 8 - 8 < 8
      · simp only [h2, dite_true]
      · simp only [h2, dite_false]

theorem words_xor (m : Mem) (a b : Addr) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (xorBytes (bytesAt m a 64) (bytesAt m b 64)) j.1) =
      (memWords m a).zipWith (· ^^^ ·) (memWords m b) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Vector.getElem_zipWith, memWords]
  rw [word_xor _ _ (Memory.bytesAt_length _ _ _) (Memory.bytesAt_length _ _ _) hj,
    wordLE_bytesAt _ _ (by omega), wordLE_bytesAt _ _ (by omega)]
  simp only [bufAt, ofInt_natCast]

theorem core_bytes {m m' : Mem} {a b d : Addr}
    (h : ∀ j (hj : j < 16), m'.readW (bufAt d (4 * j)) 32 =
      (Spec.Scrypt.core ((memWords m a).zipWith (· ^^^ ·) (memWords m b)))[j]) :
    bytesAt m' d 64 = Spec.Scrypt.salsa (xorBytes (bytesAt m a 64) (bytesAt m b 64)) := by
  rw [Spec.Scrypt.salsa, words_xor]
  exact bytesAt_eq_serialize _ _ _ fun j hj => by simpa only [bufAt, ofInt_natCast] using h j hj

theorem core_widen {p d src prev : Addr} {s : State}
    (h : Words p (memWords s.mem prev) s)
    (hi : InRegions (s.rd ++ s.wr) src 64) (hb : InRegions s.wr d 64) (hs : InRegions s.wr p 64)
    (hd : (bR d).Disjoint (scR p)) (hsd : (bR src).Disjoint (bR d))
    (hss : (bR src).Disjoint (scR p)) (hdi : s.gpr .rdi = d) (ha : s.gpr .rax = src) :
    WP isa fusedCore s fun t =>
      Words p (memWords t.mem d) t ∧
      bytesAt t.mem d 64 = Spec.Scrypt.salsa (xorBytes (bytesAt s.mem prev 64) (bytesAt s.mem src 64)) ∧
      Frame [bR d, slotR p, tempR p] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .rdi = d ∧ t.gpr .rsp = s.gpr .rsp := by
  let q := s.withRegions [bR src] [bR d, scR p]
  have hq : Words p (memWords s.mem prev) q := ⟨h.regs, h.slots, h.rsi⟩
  obtain ⟨tr, t, ex, wt, ot, ft, _, _, dt, st⟩ := core_ok (p := p) (d := d) (src := src) (s := q)
    (v := memWords s.mem prev) (x := memWords s.mem src) hq
    (fun j hj => by simp only [q, State.withRegions_mem, memWords, Vector.getElem_ofFn])
    (by simp only [q, State.withRegions_rd, State.withRegions_wr]; simp)
    (by simp only [q, State.withRegions_wr]; simp) (by simp only [q, State.withRegions_wr]; simp) hd hsd hss hdi ha
  have cw : Covers [bR d, scR p] s.wr := Covers.pair (Covers.one hb) (Covers.one hs)
  have cr : Covers ([bR src] ++ [bR d, scR p]) (s.rd ++ s.wr) :=
    Covers.append_left (Covers.one hi) cw.right
  have ex' := VG.X86_64.Exec.widen ex (rd := s.rd) (wr := s.wr) cr cw
  have eq : q.withRegions s.rd s.wr = s := by simp [q, State.withRegions]
  rw [eq] at ex'
  have words : memWords t.mem d = Spec.Scrypt.core
      ((memWords s.mem prev).zipWith (· ^^^ ·) (memWords s.mem src)) := by
    apply Vector.ext
    intro j hj
    simp only [memWords, Vector.getElem_ofFn]
    exact ot j hj
  refine ⟨tr, t.withRegions s.rd s.wr, ex', ?_, core_bytes (m := s.mem) (m' := t.mem) (a := prev) (b := src) (d := d) ot, ft, rfl, rfl, dt, st⟩
  change Words p (memWords t.mem d) (t.withRegions s.rd s.wr)
  rw [words]
  exact ⟨wt.regs, wt.slots, wt.rsi⟩
end VG.Proof.Scrypt.X86_64.Retained
