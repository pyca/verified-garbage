module

public import VerifiedGarbage.Proof.Aes.X86_64.Sse.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Interleave

/-! # A batch of eight blocks -/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes

/-- Block `i` of the buffer. -/
def bufAddr (b : Addr) (i : Nat) : Addr := b + BitVec.ofNat 64 (16 * bufSlot i)

/-- The buffer holds the eight blocks `S`. -/
def BufIs (m : Mem) (b : Addr) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 8, ∀ n < 16, m (bufAddr b i + BitVec.ofNat 64 n) = (S i).getD n 0

theorem ea_slot (s : State) (k : Nat) : s.ea (slot k) = s.gpr .r9 + BitVec.ofNat 64 (16 * k) := by
  simp only [State.ea, slot, BitVec.ofInt_natCast]

/-! ## Loading the buffer -/

theorem loadStep (q0 q4 : XReg) (k : Nat) (s : State) (h : q0 ≠ .xmm8 ∧ q4 ≠ .xmm8 ∧ q0 ≠ q4)
    (h1 : InRegions (s.rd ++ s.wr) (bufAddr (s.gpr .r9) k) 16)
    (h2 : InRegions (s.rd ++ s.wr) (bufAddr (s.gpr .r9) (k + 4)) 16) :
    ∃ s', runBlock isa [ldx q0 (bufSlot k), ldx .xmm8 (bufSlot (k + 4)), mv q4 q0, unpckl q0 .xmm8, unpckh q4 .xmm8] s = some s' ∧
      (∀ l < 2, qword (s'.xmm q0) l = s.mem.readW (bufAddr (s.gpr .r9) (k + 4 * l)) 64) ∧
      (∀ l < 2, qword (s'.xmm q4) l = s.mem.readW (bufAddr (s.gpr .r9) (k + 4 * l) + BitVec.ofNat 64 8) 64) ∧
      (∀ x, x ≠ q0 → x ≠ q4 → x ≠ .xmm8 → s'.xmm x = s.xmm x) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨a1, a2, a3⟩ := h
  have hrun : runBlock isa [ldx q0 (bufSlot k), ldx .xmm8 (bufSlot (k + 4)), mv q4 q0, unpckl q0 .xmm8, unpckh q4 .xmm8] s =
      some ((XOp.bin .punpckhqdq q4 .xmm8).exec ((XOp.bin .punpcklqdq q0 .xmm8).exec ((XOp.bin .movdqa q4 q0).exec
        ((s.setXmm q0 (s.mem.readW (bufAddr (s.gpr .r9) k) 128)).setXmm .xmm8
          (s.mem.readW (bufAddr (s.gpr .r9) (k + 4)) 128))))) := by
    rw [bufAddr] at h1 h2
    simp only [ldx, mv, unpckl, unpckh, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.load128,
      ea_slot, gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, bufAddr, h1, h2, ite_true, Option.map_some]
  refine ⟨_, hrun, fun l hl => ?_, fun l hl => ?_, fun x c d e => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [XOp.exec, xmm_setXmm, a1, a3, a1.symm, a2.symm, ite_true, ite_false]
    rw [qword_unpckl _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]; rw [qword_readW _ _ (by decide)]; simp
    · simp only [Nat.one_ne_zero, ite_false]; rw [qword_readW _ _ (by decide)]; simp
  · simp only [XOp.exec, xmm_setXmm, a1, a2.symm, a3.symm, a1.symm, ite_true, ite_false]
    rw [qword_unpckh _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true, XBinOp.eval]; rw [qword_readW _ _ (by decide)]; simp
    · simp only [Nat.one_ne_zero, ite_false]; rw [qword_readW _ _ (by decide)]
  · simp only [XOp.exec, xmm_setXmm, c, d, e, ite_false]

theorem q_ne : ∀ i < 8, q i ≠ .xmm8 ∧ q i ≠ .xmm9 ∧ ∀ j < 8, q i = q j → i = j := by decide

theorem loadSteps (s : State) (hin : ∀ i < 8, InRegions (s.rd ++ s.wr) (bufAddr (s.gpr .r9) i) 16) :
    ∀ n ≤ 4, ∃ s', runBlock isa ((List.range n).flatMap fun k =>
        [ldx (q k) (bufSlot k), ldx .xmm8 (bufSlot (k + 4)), mv (q (k + 4)) (q k), unpckl (q k) .xmm8,
          unpckh (q (k + 4)) .xmm8]) s = some s' ∧
      (∀ l < 2, ∀ k < n, ∀ h < 2, lane q s' l (k + 4 * h) =
        s.mem.readW (bufAddr (s.gpr .r9) (k + 4 * l) + BitVec.ofNat 64 (8 * h)) 64) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact ⟨s, rfl, fun l _ j hj => absurd hj (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s1, e1, h1, g1, m1, r1, w1⟩ := ih (by omega)
    obtain ⟨s2, e2, ha, hb, hc, g2, m2, r2, w2⟩ := loadStep (q n) (q (n + 4)) n s1
      ⟨(q_ne _ (by omega)).1, (q_ne _ (by omega)).1, fun h => by have := (q_ne n (by omega)).2.2 _ (by omega) h; omega⟩
      (by rw [r1, w1, g1]; exact hin _ (by omega)) (by rw [r1, w1, g1]; exact hin _ (by omega))
    refine ⟨s2, ?_, fun l hl k hk h hh => ?_, g2.trans g1, m2.trans m1, r2.trans r1, w2.trans w1⟩
    · rw [List.range_succ, List.flatMap_append, Interleave.runBlock_append, e1, Option.bind_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, e2]
    · rw [g1, m1] at ha hb
      by_cases hk' : k = n
      · subst hk'
        rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
        · simpa [lane] using ha l hl
        · simpa [lane] using hb l hl
      · have := h1 l hl k (by omega) h hh
        simp only [lane] at this ⊢
        rw [hc _ (fun e => by have := (q_ne _ (by omega)).2.2 _ (by omega) e; omega)
          (fun e => by have := (q_ne _ (by omega)).2.2 _ (by omega) e; omega) (q_ne _ (by omega)).1, this]

/-- The buffer's bytes, in the halves of its blocks. -/
theorem half_bit {m : Mem} {b : Addr} {S : Nat → Spec.Aes.State} (h : BufIs m b S) {i n j : Nat} (hi : i < 8)
    (hn : n < 16) (hj : j < 8) :
    (m.readW (bufAddr b i + BitVec.ofNat 64 (8 * (n / 8))) 64).getLsbD (8 * (n % 8) + j) = ((S i).getD n 0).getLsbD j := by
  rw [Mem.readW, BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and, getLsbD_read _ _ (by omega),
    BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * (n / 8) + (8 * (n % 8) + j) / 8 = n by omega, h i hi n hn,
    show (8 * (n % 8) + j) % 8 = j by omega]

theorem toBs_bits {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State}
    (hq : ∀ l < 2, ∀ k < 4, ∀ n < 16, ∀ j < 8,
      (lane q s l (k + 4 * (n / 8))).getLsbD (8 * (n % 8) + j) = ((S (4 * l + k)).getD n 0).getLsbD j) :
    ∃ s', runBlock isa toBs s = some s' ∧ Keep s s' ∧ Holds false q s' S := by
  obtain ⟨s', e, k, h⟩ := layer_ok toBs_check (by decide +kernel) (by decide) he
  refine ⟨s', e, k, fun l hl j hj n hn k hk => ?_⟩
  rw [h l hl j hj _ (Nat.lt_of_lt_of_le (posAt_lt false hn hk) (by decide))]
  simp only [toBsT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, byteAt_posAt false hn hk,
    posAt_mod false n hk]
  exact hq l hl k hk n hn j hj

theorem toBs_holds {s : State} (he : Env0 s) {m : Mem} {b : Addr} {S : Nat → Spec.Aes.State} (hB : BufIs m b S)
    (hq : ∀ l < 2, ∀ k < 4, ∀ h < 2, lane q s l (k + 4 * h) =
      m.readW (bufAddr b (k + 4 * l) + BitVec.ofNat 64 (8 * h)) 64) :
    ∃ s', runBlock isa toBs s = some s' ∧ Keep s s' ∧ Holds false q s' S :=
  toBs_bits he fun l hl k hk n hn j hj => by
    rw [hq l hl k hk _ (by omega), half_bit hB (by omega) hn hj, Nat.add_comm k]

theorem fromBs_bits {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds false q s S) :
    ∃ s', runBlock isa fromBs s = some s' ∧ Keep s s' ∧ ∀ l < 2, ∀ k < 4, ∀ n < 16, ∀ j < 8,
      (lane q s' l (k + 4 * (n / 8))).getLsbD (8 * (n % 8) + j) = ((S (4 * l + k)).getD n 0).getLsbD j := by
  obtain ⟨s', e, k, h⟩ := layer_ok fromBs_check (by decide +kernel) (by decide) he
  refine ⟨s', e, k, fun l hl k hk n hn j hj => ?_⟩
  rw [h l hl _ (by omega) _ (by omega)]
  simp only [fromBsT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]
  rw [show (8 * (n % 8) + j) % 8 = j by omega, show (8 * ((k + 4 * (n / 8)) / 4) + (8 * (n % 8) + j) / 8) = n by omega,
    show (k + 4 * (n / 8)) % 4 = k by omega]
  exact hS l hl j hj n hn k hk

/-! ## Storing the buffer -/

theorem readW_writeW_self128 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 128 = v :=
  Mem.readW_writeW_self m a 16 v (by decide)

theorem storeStep (q0 q4 : XReg) (k : Nat) (hk : k < 4) (s : State) (h : q0 ≠ .xmm8 ∧ q4 ≠ .xmm8 ∧ q0 ≠ q4)
    (h1 : InRegions s.wr (bufAddr (s.gpr .r9) k) 16)
    (h2 : InRegions s.wr (bufAddr (s.gpr .r9) (k + 4)) 16) :
    ∃ s', ∃ A B : BitVec 128, runBlock isa [mv .xmm8 q0, unpckl .xmm8 q4, unpckh q0 q4, stx (bufSlot k) .xmm8, stx (bufSlot (k + 4)) q0] s =
        some s' ∧
      s'.mem = (s.mem.writeW (bufAddr (s.gpr .r9) k) A).writeW (bufAddr (s.gpr .r9) (k + 4)) B ∧
      (∀ l < 2, ∀ h < 2, s'.mem.readW (bufAddr (s.gpr .r9) (k + 4 * l) + BitVec.ofNat 64 (8 * h)) 64 =
        qword (s.xmm (if h = 0 then q0 else q4)) l) ∧
      (∀ x, x ≠ q0 → x ≠ .xmm8 → s'.xmm x = s.xmm x) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨A, hA⟩ : ∃ A, A = XBinOp.eval .punpcklqdq (s.xmm q0) (s.xmm q4) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = XBinOp.eval .punpckhqdq (s.xmm q0) (s.xmm q4) := ⟨_, rfl⟩
  have hrun : ∃ s', runBlock isa [mv .xmm8 q0, unpckl .xmm8 q4, unpckh q0 q4, stx (bufSlot k) .xmm8, stx (bufSlot (k + 4)) q0] s =
      some s' ∧ s'.mem = (s.mem.writeW (bufAddr (s.gpr .r9) k) A).writeW (bufAddr (s.gpr .r9) (k + 4)) B ∧
      (∀ x, x ≠ q0 → x ≠ .xmm8 → s'.xmm x = s.xmm x) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    rw [bufAddr] at h1 h2
    subst hA hB
    simp only [stx, mv, unpckl, unpckh, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.store128,
      XOp.exec, ea_slot, gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, h1, h2, ite_true, xmm_setXmm, a1, a2, a1.symm,
      ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun x c d => ?_, trivial, trivial, trivial⟩
    simp only [c, d, ite_false]
  obtain ⟨s', hr, hm, hx, hg, hrd, hwr⟩ := hrun
  refine ⟨s', A, B, hr, hm, fun l hl h hh => ?_, hx, hg, hrd, hwr⟩
  have hsep : Mem.Sep (bufAddr (s.gpr .r9) k) (128 / 8) (bufAddr (s.gpr .r9) (k + 4)) (128 / 8) :=
    Offset.sep _ (.inl (by simp only [bufSlot]; omega)) (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega)
  rw [← qword_readW _ _ hh, hm]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [show k + 4 * 0 = k by omega, Mem.readW_writeW_sep hsep (by decide), readW_writeW_self128, hA]
    rw [qword_unpckl _ _ hh]
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp
  · rw [show k + 4 * 1 = k + 4 by omega, readW_writeW_self128, hB]
    rw [qword_unpckh _ _ hh]
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp

/-- The buffer. -/
def bufR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 288, 128⟩

theorem buf_contains (b : Addr) {i : Nat} (hi : i < 8) : (bufR b).Contains (bufAddr b i) 16 :=
  Offset.contains _ (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega) (by decide)

theorem storeSteps (s : State) (hin : ∀ i < 8, InRegions s.wr (bufAddr (s.gpr .r9) i) 16) :
    ∀ n ≤ 4, ∃ s', runBlock isa ((List.range n).flatMap fun k =>
        [mv .xmm8 (q k), unpckl .xmm8 (q (k + 4)), unpckh (q k) (q (k + 4)), stx (bufSlot k) .xmm8,
          stx (bufSlot (k + 4)) (q k)]) s = some s' ∧
      (∀ l < 2, ∀ k < n, ∀ h < 2, s'.mem.readW (bufAddr (s.gpr .r9) (k + 4 * l) + BitVec.ofNat 64 (8 * h)) 64 =
        lane q s l (k + 4 * h)) ∧
      (∀ j < 8, n ≤ j % 4 → s'.xmm (q j) = s.xmm (q j)) ∧
      s'.gpr = s.gpr ∧ Frame [bufR (s.gpr .r9)] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact ⟨s, rfl, fun l _ j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl, rfl, Frame.refl _ _, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s1, e1, h1, x1, g1, f1, r1, w1⟩ := ih (by omega)
    obtain ⟨s2, A, B, e2, hm, ha, hc, g2, r2, w2⟩ := storeStep (q n) (q (n + 4)) n (by omega) s1
      ⟨(q_ne _ (by omega)).1, (q_ne _ (by omega)).1, fun h => by have := (q_ne n (by omega)).2.2 _ (by omega) h; omega⟩
      (by rw [w1, g1]; exact hin _ (by omega)) (by rw [w1, g1]; exact hin _ (by omega))
    rw [g1] at hm ha
    refine ⟨s2, ?_, fun l hl k hk h hh => ?_, fun j hj hnj => ?_, g2.trans g1, ?_, r2.trans r1, w2.trans w1⟩
    · rw [List.range_succ, List.flatMap_append, Interleave.runBlock_append, e1, Option.bind_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, e2]
    · by_cases hk' : k = n
      · subst hk'
        rw [ha l hl h hh, lane]
        rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
        · simp only [ite_true, Nat.mul_zero, Nat.add_zero, x1 k (by omega) (by omega)]
        · simp only [Nat.one_ne_zero, ite_false, Nat.mul_one, x1 (k + 4) (by omega) (by omega)]
      · rw [← h1 l hl k (by omega) h hh, hm]
        have sep : ∀ i < 8, i ≠ k + 4 * l → Mem.Sep (bufAddr (s.gpr .r9) (k + 4 * l) + BitVec.ofNat 64 (8 * h)) (64 / 8)
            (bufAddr (s.gpr .r9) i) (128 / 8) := fun i hi hne => by
          simp only [bufAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
          exact Offset.sep _ (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega)
        rw [Mem.readW_writeW_sep (sep _ (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (sep _ (by omega) (by omega)) (by decide)]
    · rw [hc _ (fun e => by have := (q_ne j hj).2.2 _ (by omega) e; omega) (q_ne j hj).1, x1 j hj (by omega)]
    · rw [hm]
      exact (f1.writeW List.mem_cons_self _ (buf_contains _ (by omega))).writeW List.mem_cons_self _
        (buf_contains _ (by omega))

theorem bufIs_of {m : Mem} {b : Addr} {S : Nat → Spec.Aes.State}
    (h : ∀ l < 2, ∀ k < 4, ∀ n < 16, ∀ j < 8,
      (m.readW (bufAddr b (k + 4 * l) + BitVec.ofNat 64 (8 * (n / 8))) 64).getLsbD (8 * (n % 8) + j) =
        ((S (4 * l + k)).getD n 0).getLsbD j) : BufIs m b S := fun i hi n hn => byte_ext fun j hj => by
  have := h (i / 4) (by omega) (i % 4) (by omega) n hn j hj
  rw [show 4 * (i / 4) + i % 4 = i by omega, show i % 4 + 4 * (i / 4) = i by omega] at this
  rw [← this, Mem.readW, BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and,
    getLsbD_read _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8 * (n / 8) + (8 * (n % 8) + j) / 8 = n by omega, show (8 * (n % 8) + j) % 8 = j by omega]

/-! ## The cipher on the buffer -/

/-- The cipher after the first round key and `m` middle rounds. -/
def encMid (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => rnd w (j + 1) s) (Spec.Aes.addRoundKey x (Spec.Aes.roundKey w 0))

theorem encMid_succ (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    encMid w (m + 1) x = rnd w (m + 1) (encMid w m x) := by
  simp [encMid, List.range_succ, List.foldl_append]

theorem cipher_encMid (nr : Nat) (w : List Byte) (x : Spec.Aes.State) :
    Spec.Aes.cipher nr w x = Spec.Aes.addRoundKey (Spec.Aes.shiftRows (Spec.Aes.subBytes (encMid w (nr - 1) x)))
      (Spec.Aes.roundKey w nr) := rfl

variable {b : Addr} {nr : Nat} {w : List Byte}

/-- What a batch needs: the round keys, and the buffer. -/
structure BatchPre (b : Addr) (nr : Nat) (w : List Byte) (S : Nat → Spec.Aes.State) (s : State) : Prop where
  ready : Ready b nr w s.mem s.rd s.wr
  r9 : s.gpr .r9 = b
  rsi : s.gpr .rsi = BitVec.ofNat 64 nr
  buf : BufIs s.mem b S

/-- What a batch leaves. -/
structure BatchPost (b : Addr) (nr : Nat) (w : List Byte) (S : Nat → Spec.Aes.State) (s s' : State) : Prop where
  ready : Ready b nr w s'.mem s'.rd s'.wr
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨b, 416⟩] s.mem s'.mem
  buf : BufIs s'.mem b S

theorem BatchPre.env {S : Nat → Spec.Aes.State} {s : State} (h : BatchPre b nr w S s) : Env0 s where
  ok := ⟨fun k hk => by
    rw [show s.gpr cfg.base = b from h.r9]
    exact h.ready.inWr (by simp only [cfg] at hk; omega), by decide⟩
  masks := by rw [h.r9]; exact h.ready.masks

theorem Ready.bufIn {m : Mem} {rd wr : List Region} (h : Ready b nr w m rd wr) {i : Nat} (hi : i < 8) :
    InRegions wr (bufAddr b i) 16 := h.inWr (by simp only [bufSlot]; omega)

/-- The buffer loaded and transposed. -/
theorem loadBuf_ok {S : Nat → Spec.Aes.State} {s : State} (h : BatchPre b nr w S s) :
    WP isa (.block (loadBuf ++ toBs)) s fun s' => Keep s s' ∧ Holds false q s' S := by
  obtain ⟨s1, e1, h1, g1, m1, r1, w1⟩ := loadSteps s (fun i hi => by
    rw [h.r9]
    obtain ⟨R, hR, hc⟩ := h.ready.bufIn hi
    exact ⟨R, List.mem_append_right _ hR, hc⟩) 4 (by decide)
  have k1 := keep_of h.env g1 m1 r1 w1
  obtain ⟨s2, e2, k2, h2⟩ := toBs_holds k1.env h.buf (by rw [h.r9] at h1; exact h1)
  refine WP.block_append (WP.of_runBlock ⟨s1, e1, WP.of_runBlock ⟨s2, e2, k1.trans k2, h2⟩⟩)

/-- The states to the buffer. -/
theorem storeBuf_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} 
    (h : RS s₁ b nr w cnt i false q S s) :
    WP isa (.block (fromBs ++ storeBuf)) s (BatchPost b nr w S s₁) := by
  obtain ⟨s2, e2, k2, h2⟩ := fromBs_bits h.env h.holds
  have hf2 : Frame [⟨b, 288⟩] s.mem s2.mem := by
    have := k2.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  have hready2 : Ready b nr w s2.mem s2.rd s2.wr := by
    refine ⟨by rw [k2.wr]; exact h.ready.sc, fun i hi => ?_, ?_, h.ready.nrs, h.ready.len⟩
    · refine (h.ready.keys i hi).congrW fun j hj => ?_
      have := h.ready.nrs
      rw [hf2.readW (r := ⟨b + BitVec.ofNat 64 keysOff, 960⟩) ?_ (low_disj b) (by decide)]
      rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega) (by decide)
    · have := k2.env.masks
      rwa [k2.gpr, h.r9] at this
  have h9 : s2.gpr .r9 = b := by rw [k2.gpr, h.r9]
  obtain ⟨s3, e3, h3, -, g3, f3, r3, w3⟩ := storeSteps s2 (fun i hi => by rw [h9]; exact hready2.bufIn hi) 4 (by decide)
  rw [h9] at h3 f3
  refine WP.block_append (WP.of_runBlock ⟨s2, e2, WP.of_runBlock ⟨s3, e3, ?_⟩⟩)
  refine ⟨?_, fun x a c => by rw [g3, k2.gpr, h.gpr x a c], (r3.trans k2.rd).trans h.rd, (w3.trans k2.wr).trans h.wr,
    ?_, bufIs_of fun l hl k hk n hn j hj => ?_⟩
  · rw [r3, w3]
    refine hready2.frame f3 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨Offset.disjoint _ (.inr (by decide)) (by decide) (by decide),
      Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)⟩
  · have sub : ∀ r ∈ [(⟨b, 288⟩ : Region), bufR b], ∃ r' ∈ [(⟨b, 416⟩ : Region)], Region.Sub r r' := by
      intro r hr
      refine ⟨_, List.mem_singleton.mpr rfl, fun x hx => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Region.Contains] at hx ⊢; omega
      · simp only [Region.Contains, bufR] at hx ⊢; bv_omega
    have a1 := (h.frame.trans hf2).sub (rs' := [⟨b, 416⟩]) fun r hr => sub r (by simp_all)
    exact a1.trans (f3.sub fun r hr => sub r (by simp_all))
  · rw [h3 l hl k hk _ (by omega), h2 l hl k hk n hn j hj]

theorem sh1 : ∀ n, n = 10 ∨ n = 12 ∨ n = 14 →
    (BitVec.ofNat 64 n >>> (1 : Nat) : BitVec 64) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (n / 2 - 1) := by
  rintro n (rfl | rfl | rfl) <;> decide

theorem keyAddr_zero (b : Addr) : keyAddr b 0 = b + BitVec.signExtend 64 (BitVec.ofNat 32 keysOff) := rfl

/-- The registers a batch's setup writes. -/
theorem setup_ok {S : Nat → Spec.Aes.State} {s s1 : State} (h : BatchPre b nr w S s) (k : Keep s s1)
    (hh : Holds false q s1 S) :
    WP isa (.block (pairs ++ ([.mov kp (.reg .r9), .alu .add kp (.imm (BitVec.ofNat 32 keysOff))] : List Instr))) s1
      (RS s b nr w (BitVec.ofNat 64 (nr / 2 - 1)) 0 false q S) := by
  have hsi : s1.gpr .rsi = BitVec.ofNat 64 nr := by rw [k.gpr, h.rsi]
  have h9 : s1.gpr .r9 = b := by rw [k.gpr, h.r9]
  have hf : Frame [⟨b, 288⟩] s.mem s1.mem := by
    have := k.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  have hready : Ready b nr w s1.mem s1.rd s1.wr := by
    refine ⟨by rw [k.wr]; exact h.ready.sc, fun i hi => ?_, ?_, h.ready.nrs, h.ready.len⟩
    · refine (h.ready.keys i hi).congrW fun j hj => ?_
      have := h.ready.nrs
      rw [hf.readW (r := ⟨b + BitVec.ofNat 64 keysOff, 960⟩) ?_ (low_disj b) (by decide)]
      rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega) (by decide)
    · have := k.env.masks
      rwa [k.gpr, h.r9] at this
  apply WP.of_runBlock
  simp only [pairs, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec,
    execAlu, execShift, readSrc, Option.bind_some, Option.map_some, show kp = Reg.rax from rfl, Nat.le_refl,
    Nat.reduceLeDiff, and_self, ite_true, Option.some.injEq, exists_eq_left', gpr_setReg, gpr_arithFlags, gpr_setFlags,
    reduceCtorEq, ite_false, hsi, h9]
  refine ⟨hready, ?_, fun x a c => ?_, ?_, ?_, k.rd, k.wr, hf, hh⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, h9]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, c, ite_false, k.gpr]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, ite_true]
    exact sh1 nr h.ready.nrs
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, ite_true]
    exact (keyAddr_zero b).symm

theorem beq_zero {c : Nat} (hc : c < 2 ^ 64) : (BitVec.ofNat 64 c == 0) = decide (c = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [Nat.mod_eq_of_lt hc] using this
  · rintro rfl; rfl

/-- The loop counter counted down. -/
theorem RS.count {s₁ s : State} {c i : Nat} {r : Nat → XReg} {S : Nat → Spec.Aes.State} {f : Bool}
    (h : RS s₁ b nr w (BitVec.ofNat 64 (c + 1)) i f r S s) (hc : c < 2 ^ 32) :
    WP isa (.block ([.alu .sub .r10 (.imm 1)] : List Instr)) s fun s' =>
      RS s₁ b nr w (BitVec.ofNat 64 c) i f r S s' ∧ X86_64.eval .ne s' = some (decide (c ≠ 0)) := by
  apply WP.of_runBlock
  have e : s.gpr .r10 - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 c := by
    rw [h.cnt, show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec,
    execAlu, readSrc, Option.bind_some, Option.some.injEq, exists_eq_left', e]
  refine ⟨⟨h.ready, ?_, fun x a d => ?_, ?_, ?_, h.rd, h.wr, h.frame, h.holds⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, h.r9]
  · simp only [gpr_setReg, gpr_arithFlags, d, ite_false]; exact h.gpr x a d
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, h.kpAt]
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

theorem encPair_ok {s₁ s : State} {cnt : BitVec 64} {m : Nat} {S : Nat → Spec.Aes.State} (hm : 2 * m + 2 ≤ nr)
    (h : RS s₁ b nr w cnt (2 * m + 1) false q (fun k => encMid w (2 * m) (S k)) s) :
    WP isa (.block (roundA ++ roundB)) s (RS s₁ b nr w cnt (2 * (m + 1) + 1) false q fun k => encMid w (2 * (m + 1)) (S k)) := by
  refine WP.block_append (WP.mono (roundA_ok (by omega) (by omega) h) fun s2 h2 => ?_)
  refine WP.mono (roundB_ok (by omega) (by omega) (by omega) h2) fun s3 h3 => h3.congr fun k _ => ?_
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, encMid_succ, encMid_succ]

theorem moveBack_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} {f : Bool}
    (h : RS s₁ b nr w cnt i f p S s) : WP isa (.block moveBack) s (RS s₁ b nr w cnt i f q S) := by
  obtain ⟨s', e, k, hb⟩ := layer_ok move_check (by decide +kernel) (by decide) h.env
  refine h.step ⟨s', e, k, fun l hl => ?_⟩
  refine (h.holds l hl).congrW fun j hj => BitVec.eq_of_getLsbD_eq fun x hx => ?_
  rw [hb l hl j hj x hx]
  simp [termsXor, idT]

theorem encLast_ok {s₁ s : State} {cnt : BitVec 64} {S : Nat → Spec.Aes.State}
    (h : RS s₁ b nr w cnt (nr - 1) false q (fun k => encMid w (nr - 2) (S k)) s) :
    WP isa (.block (roundA ++ lastB ++ fromBs ++ storeBuf)) s (BatchPost b nr w (fun k => Spec.Aes.cipher nr w (S k)) s₁) := by
  have hn := h.ready.nrs
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (roundA_ok (by omega) (by omega) h) fun s2 h2 => ?_)
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append ?_)))
  refine WP.mono (h2.step (sub_holds h2.env h2.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.step (sr2_holds h3.env h3.holds)) fun s4 h4 => ?_
  rw [show nr - 1 + 1 = nr by omega] at h4
  refine WP.mono (h4.ark regs_p (by rcases hn with rfl | rfl | rfl <;> rfl) (Nat.le_refl _)) fun s5 h5 => ?_
  refine WP.mono (moveBack_ok h5) fun s6 h6 => ?_
  refine storeBuf_ok (h6.congr fun k _ => ?_)
  rw [kr, ite_eq_right (by omega), lastRound63 _ (h.ready.len nr (Nat.le_refl _)), cipher_encMid,
    show nr - 1 = (nr - 2) + 1 by omega, encMid_succ]

theorem encrypt8_ok {S : Nat → Spec.Aes.State} {s : State} (h : BatchPre b nr w S s) :
    WP isa encrypt8 s (BatchPost b nr w (fun k => Spec.Aes.cipher nr w (S k)) s) := by
  have hn := h.ready.nrs
  refine WP.seq ?_
  rw [List.append_assoc (loadBuf ++ toBs) pairs]
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (loadBuf_ok h) fun s1 ⟨k1, h1⟩ => ?_
  refine WP.mono (setup_ok h k1 h1) fun s2 h2 => ?_
  refine WP.mono (h2.ark regs_q rfl (Nat.zero_le _)) fun s3 h3 => ?_
  refine WP.mono h3.next fun s4 h4 => ?_
  refine WP.seq (WP.mono (Q := RS s b nr w 0 (nr - 1) false q fun k => encMid w (nr - 2) (S k)) ?_
    fun s5 h5 => encLast_ok h5)
  let I : Nat → State → Prop := fun c s' => ∃ m, c = nr / 2 - 1 - m ∧ m < nr / 2 - 1 ∧
    RS s b nr w (BitVec.ofNat 64 (nr / 2 - 1 - m)) (2 * m + 1) false q (fun k => encMid w (2 * m) (S k)) s'
  refine WP.loop (M := isa) I ?_ (nr / 2 - 1) s4 ⟨0, rfl, by omega, h4.congr fun k _ => rfl⟩
  rintro c s' ⟨m, rfl, hm, hs'⟩
  refine WP.block_append (WP.mono (encPair_ok (by omega) hs') fun s6 h6 => ?_)
  rw [show nr / 2 - 1 - m = (nr / 2 - 1 - (m + 1)) + 1 by omega] at h6
  refine WP.mono (h6.count (by omega)) fun s7 ⟨h7, hz⟩ => ?_
  by_cases hl : nr / 2 - 1 - (m + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    have e1 : 2 * (m + 1) + 1 = nr - 1 := by omega
    have e2 : 2 * (m + 1) = nr - 2 := by omega
    rw [hl, e1, e2] at h7
    exact h7
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, m + 1, rfl, by omega, h7⟩

/-! ## The inverse cipher on the buffer -/

theorem shl6 : ∀ n, n = 10 ∨ n = 12 ∨ n = 14 → (BitVec.ofNat 64 n <<< (6 : Nat) : BitVec 64) = BitVec.ofNat 64 (64 * n) := by
  rintro n (rfl | rfl | rfl) <;> decide

theorem Keep.ready {S : Nat → Spec.Aes.State} {s s1 : State} (h : BatchPre b nr w S s) (k : Keep s s1) :
    Frame [⟨b, 288⟩] s.mem s1.mem ∧ Ready b nr w s1.mem s1.rd s1.wr := by
  have hf : Frame [⟨b, 288⟩] s.mem s1.mem := by
    have := k.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  refine ⟨hf, ⟨by rw [k.wr]; exact h.ready.sc, fun i hi => ?_, ?_, h.ready.nrs, h.ready.len⟩⟩
  · refine (h.ready.keys i hi).congrW fun j hj => ?_
    have := h.ready.nrs
    rw [hf.readW (r := ⟨b + BitVec.ofNat 64 keysOff, 960⟩) ?_ (low_disj b) (by decide)]
    rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega) (by decide)
  · have := k.env.masks
    rwa [k.gpr, h.r9] at this

theorem keyAddr_last (b : Addr) (n : Nat) :
    keyAddr b n = BitVec.ofNat 64 (64 * n) + b + BitVec.signExtend 64 (BitVec.ofNat 32 keysOff) := by
  rw [keyAddr, show BitVec.signExtend 64 (BitVec.ofNat 32 keysOff) = BitVec.ofNat 64 keysOff by decide,
    BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 (64 * n)) b, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 keysOff)]

theorem setupDec_ok {S : Nat → Spec.Aes.State} {s s1 : State} (h : BatchPre b nr w S s) (k : Keep s s1)
    (hh : Holds false q s1 S) :
    WP isa (.block (pairs ++ ([.mov kp (.reg .rsi), .shift .shl kp 6, .alu .add kp (.reg .r9),
        .alu .add kp (.imm (BitVec.ofNat 32 keysOff))] : List Instr))) s1
      (RS s b nr w (BitVec.ofNat 64 (nr / 2 - 1)) nr false q S) := by
  have hsi : s1.gpr .rsi = BitVec.ofNat 64 nr := by rw [k.gpr, h.rsi]
  have h9 : s1.gpr .r9 = b := by rw [k.gpr, h.r9]
  obtain ⟨hf, hready⟩ := Keep.ready h k
  apply WP.of_runBlock
  simp only [pairs, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec,
    execAlu, execShift, readSrc, Option.bind_some, Option.map_some, show kp = Reg.rax from rfl, Nat.le_refl,
    Nat.reduceLeDiff, and_self, ite_true, Option.some.injEq, exists_eq_left', gpr_setReg, gpr_arithFlags, gpr_setFlags,
    reduceCtorEq, ite_false, hsi, h9]
  refine ⟨hready, ?_, fun x a c => ?_, ?_, ?_, k.rd, k.wr, hf, hh⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, h9]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, c, ite_false, k.gpr]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, ite_true]
    exact sh1 nr h.ready.nrs
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, shl6 nr h.ready.nrs]
    exact (keyAddr_last b nr).symm

theorem RS.prev {s₁ s : State} {cnt : BitVec 64} {i : Nat} {r : Nat → XReg}
    {S : Nat → Spec.Aes.State} {f : Bool} (h : RS s₁ b nr w cnt (i + 1) f r S s) :
    WP isa (.block [prevKey]) s (RS s₁ b nr w cnt i f r S) := by
  apply WP.of_runBlock
  have e : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  simp only [prevKey, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, e, Option.bind_some,
    Option.some.injEq, exists_eq_left', show kp = Reg.rax from rfl]
  refine ⟨h.ready, ?_, fun x a c => ?_, ?_, ?_, h.rd, h.wr, h.frame, h.holds⟩
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags]; exact h.r9
  · rw [gpr_setReg_of_ne _ _ a, gpr_arithFlags]; exact h.gpr x a c
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags]; exact h.cnt
  · rw [gpr_setReg_self, h.kpAt, keyAddr, keyAddr, show keysOff + 64 * (i + 1) = keysOff + 64 * i + 64 by omega,
      BitVec.ofNat_add (keysOff + 64 * i), ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _

/-- A round of the inverse cipher, between states with `{63}` added. -/
def irnd0 (w : List Byte) (i : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  Spec.Aes.invMixColumns (Spec.Aes.addRoundKey ((Spec.Aes.invShiftRows x).map invSbox0) (kr w i))

theorem irnd0_c63 {i j : Nat} (h0 : i ≠ 0) (hl : (Spec.Aes.roundKey w i).length = 16) (hj : i = nr - 1 - j)
    (x : Spec.Aes.State) : irnd0 w i (c63 x) = c63 (irnd nr w j x) := by
  rw [irnd0, kr, ite_eq_right h0, invRound63 _ hl, irnd, hj]

theorem invRoundA_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} (hi : i % 2 = 0) (hn : i + 1 ≤ nr)
    (h : RS s₁ b nr w cnt (i + 1) false q S s) :
    WP isa (.block invRoundA) s (RS s₁ b nr w cnt i true q fun k => irnd0 w (i + 1) (S k)) := by
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append ?_)))
  refine WP.mono (h.step (invSr2_holds h.env h.holds)) fun s2 h2 => ?_
  refine WP.mono (h2.step (invSub_holds h2.env h2.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.ark regs_p (by simp; omega) hn) fun s4 h4 => ?_
  refine WP.mono (h4.step (invMc_holds true h4.env h4.holds)) fun s5 h5 => ?_
  exact h5.prev

theorem invRoundB_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} (hi : i % 2 = 1) (hn : i + 1 ≤ nr)
    (h : RS s₁ b nr w cnt (i + 1) true q S s) :
    WP isa (.block invRoundB) s (RS s₁ b nr w cnt i false q fun k => irnd0 w (i + 1) (S k)) := by
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (h.skipInv.step (invSub_holds h.env h.skipInv.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.ark regs_p (by simp; omega) hn) fun s4 h4 => ?_
  refine WP.mono (h4.step (invMc_holds false h4.env h4.holds)) fun s5 h5 => ?_
  exact h5.prev

/-- The states before the pair of rounds `m`. -/
def decMid (nr : Nat) (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  c63 (invMid nr w m (Spec.Aes.addRoundKey x (Spec.Aes.roundKey w nr)))

theorem decPair_ok {s₁ s : State} {cnt : BitVec 64} {m : Nat} {S : Nat → Spec.Aes.State} (hm : 2 * m + 4 ≤ nr)
    (h : RS s₁ b nr w cnt (nr - 1 - 2 * m) false q (fun k => decMid nr w (2 * m) (S k)) s) :
    WP isa (.block (invRoundA ++ invRoundB)) s
      (RS s₁ b nr w cnt (nr - 1 - 2 * (m + 1)) false q fun k => decMid nr w (2 * (m + 1)) (S k)) := by
  have hn := h.ready.nrs
  have e1 : nr - 1 - 2 * m = nr - 1 - 2 * (m + 1) + 1 + 1 := by omega
  rw [e1] at h
  refine WP.block_append (WP.mono (invRoundA_ok (by omega) (by omega) h) fun s2 h2 => ?_)
  refine WP.mono (invRoundB_ok (by omega) (by omega) h2) fun s3 h3 => h3.congr fun k _ => ?_
  simp only [decMid]
  rw [irnd0_c63 (nr := nr) (j := 2 * m) (by omega) (h.ready.len _ (by omega)) (by omega),
    irnd0_c63 (nr := nr) (j := 2 * m + 1) (by omega) (h.ready.len _ (by omega)) (by omega),
    show 2 * (m + 1) = 2 * m + 1 + 1 by omega, invMid_succ, invMid_succ]

theorem decLast_ok {s₁ s : State} {cnt : BitVec 64} {S : Nat → Spec.Aes.State}
    (h : RS s₁ b nr w cnt 1 false q (fun k => decMid nr w (nr - 2) (S k)) s) :
    WP isa (.block (invRoundA ++ invLastB ++ fromBs ++ storeBuf)) s
      (BatchPost b nr w (fun k => Spec.Aes.invCipher nr w (S k)) s₁) := by
  have hn := h.ready.nrs
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (invRoundA_ok (i := 0) rfl (by omega) h) fun s2 h2 => ?_)
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (h2.skipInv.step (invSub_holds h2.env h2.skipInv.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.ark regs_p rfl (Nat.zero_le _)) fun s5 h5 => ?_
  refine WP.mono (moveBack_ok h5) fun s6 h6 => ?_
  refine storeBuf_ok (h6.congr fun k _ => ?_)
  simp only [decMid]
  rw [irnd0_c63 (nr := nr) (j := nr - 2) (by omega) (h.ready.len _ (by omega)) (by omega), invShiftRows_c63,
    map_invSbox0, kr, ite_eq_left rfl, invCipher_eq, show nr - 1 = (nr - 2) + 1 by omega, invMid_succ]

theorem decrypt8_ok {S : Nat → Spec.Aes.State} {s : State} (h : BatchPre b nr w S s) :
    WP isa decrypt8 s (BatchPost b nr w (fun k => Spec.Aes.invCipher nr w (S k)) s) := by
  have hn := h.ready.nrs
  refine WP.seq ?_
  rw [List.append_assoc (loadBuf ++ toBs) pairs]
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (loadBuf_ok h) fun s1 ⟨k1, h1⟩ => ?_
  refine WP.mono (setupDec_ok h k1 h1) fun s2 h2 => ?_
  refine WP.mono (h2.ark regs_q (by rcases hn with rfl | rfl | rfl <;> rfl) (Nat.le_refl _)) fun s3 h3 => ?_
  rw [show nr = nr - 1 + 1 by omega] at h3
  refine WP.mono h3.prev fun s4 h4 => ?_
  rw [← show nr = nr - 1 + 1 by omega] at h4
  refine WP.seq (WP.mono (Q := RS s b nr w 0 1 false q fun k => decMid nr w (nr - 2) (S k)) ?_
    fun s5 h5 => decLast_ok h5)
  let I : Nat → State → Prop := fun c s' => ∃ m, c = nr / 2 - 1 - m ∧ m < nr / 2 - 1 ∧
    RS s b nr w (BitVec.ofNat 64 (nr / 2 - 1 - m)) (nr - 1 - 2 * m) false q (fun k => decMid nr w (2 * m) (S k)) s'
  refine WP.loop (M := isa) I ?_ (nr / 2 - 1) s4 ⟨0, rfl, by omega, h4.congr fun k _ => ?_⟩
  · rintro c s' ⟨m, rfl, hm, hs'⟩
    refine WP.block_append (WP.mono (decPair_ok (by omega) hs') fun s6 h6 => ?_)
    rw [show nr / 2 - 1 - m = (nr / 2 - 1 - (m + 1)) + 1 by omega] at h6
    refine WP.mono (h6.count (by omega)) fun s7 ⟨h7, hz⟩ => ?_
    by_cases hl : nr / 2 - 1 - (m + 1) = 0
    · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
      have e1 : nr - 1 - 2 * (m + 1) = 1 := by omega
      have e2 : 2 * (m + 1) = nr - 2 := by omega
      rw [hl, e1, e2] at h7
      exact h7
    · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, m + 1, rfl, by omega, h7⟩
  · rw [kr, ite_eq_right (by omega), addRoundKey_rk63 _ (h.ready.len nr (Nat.le_refl _))]
    rfl

end VG.Proof.Aes.X86_64.Sse
