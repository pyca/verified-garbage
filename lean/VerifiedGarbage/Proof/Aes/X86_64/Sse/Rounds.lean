module

public import VerifiedGarbage.Proof.Aes.X86_64.Sse.Layers
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Framework.Block

/-! # The rounds of bitsliced AES in SSE2 -/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes

/-! ## Quadwords -/

theorem qword_readW (m : Mem) (a : Addr) {l : Nat} (hl : l < 2) :
    qword (m.readW a 128) l = m.readW (a + BitVec.ofNat 64 (8 * l)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  rw [getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega)]
  rw [show a + BitVec.ofNat 64 ((64 * l + i) / 8) = a + BitVec.ofNat 64 (8 * l) + BitVec.ofNat 64 (i / 8) by
    rw [show (64 * l + i) / 8 = 8 * l + i / 8 by omega, BitVec.ofNat_add, BitVec.add_assoc]]
  rw [decide_eq_true (by omega), Bool.true_and]; exact congrArg _ (by omega)

theorem dup44 (a : BitVec 128) : shufDwords a 0x44 = ofDwords (dword a 0) (dword a 1) (dword a 0) (dword a 1) := rfl
theorem dupee (a : BitVec 128) : shufDwords a 0xee = ofDwords (dword a 2) (dword a 3) (dword a 2) (dword a 3) := rfl

theorem qword_dup44 (a : BitVec 128) {l : Nat} (hl : l < 2) : qword (shufDwords a 0x44) l = qword a 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_qword _ hi, getLsbD_qword _ hi, dup44, getLsbD_ofDwords]
  simp only [getLsbD_dword]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  all_goals
    rcases (by omega : i < 32 ∨ 32 ≤ i) with h | h
    all_goals
      simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, decide_eq_true, Bool.true_and]
      exact congrArg _ (by omega)

theorem qword_dupee (a : BitVec 128) {l : Nat} (hl : l < 2) : qword (shufDwords a 0xee) l = qword a 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_qword _ hi, getLsbD_qword _ hi, dupee, getLsbD_ofDwords]
  simp only [getLsbD_dword]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  all_goals
    rcases (by omega : i < 32 ∨ 32 ≤ i) with h | h
    all_goals
      simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, decide_eq_true, Bool.true_and]
      exact congrArg _ (by omega)

theorem qword_unpckl (a b : BitVec 128) {l : Nat} (hl : l < 2) :
    qword (XBinOp.eval .punpcklqdq a b) l = if l = 0 then qword a 0 else qword b 0 := by
  simp only [XBinOp.eval]; rw [StraightY.qword_app _ _ hl]

theorem qword_unpckh (a b : BitVec 128) {l : Nat} (hl : l < 2) :
    qword (XBinOp.eval .punpckhqdq a b) l = if l = 0 then qword a 1 else qword b 1 := by
  simp only [XBinOp.eval]; rw [StraightY.qword_app _ _ hl]

/-! ## Adding a round key -/

/-- The round key `rk` is at `a`, in slices in form `f`, a quadword for each. -/
def KeyAt (m : Mem) (a : Addr) (f : Bool) (rk : List Byte) : Prop :=
  BsRel 4 f (fun j => m.readW (a + BitVec.ofNat 64 (8 * j)) 64) fun _ => rkState rk

/-- One step of `addRoundKey`. -/
theorem arkStep (r0 r1 t u : XReg) (i : Nat) (s : State)
    (h : r0 ≠ t ∧ r0 ≠ u ∧ r1 ≠ t ∧ r1 ≠ u ∧ t ≠ u ∧ r0 ≠ r1)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (16 * i)) 16) :
    ∃ s', runBlock isa [.movdquLoad t (Impl.Aes.X86_64.at_ kp (16 * i)), dupLow u t, dupHigh t t, px r0 u, px r1 t] s = some s' ∧
      (∀ l < 2, qword (s'.xmm r0) l = qword (s.xmm r0) l ^^^ s.mem.readW (s.gpr kp + BitVec.ofNat 64 (16 * i)) 64) ∧
      (∀ l < 2, qword (s'.xmm r1) l = qword (s.xmm r1) l ^^^ s.mem.readW (s.gpr kp + BitVec.ofNat 64 (16 * i + 8)) 64) ∧
      (∀ x, x ≠ r0 → x ≠ r1 → x ≠ t → x ≠ u → s'.xmm x = s.xmm x) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hea : s.ea (Impl.Aes.X86_64.at_ kp (16 * i)) = s.gpr kp + BitVec.ofNat 64 (16 * i) := by
    simp only [State.ea, Impl.Aes.X86_64.at_, BitVec.ofInt_natCast]
  have hrun : runBlock isa [.movdquLoad t (Impl.Aes.X86_64.at_ kp (16 * i)), dupLow u t, dupHigh t t, px r0 u, px r1 t] s =
      some ((XOp.bin XBinOp.pxor r1 t).exec ((XOp.bin XBinOp.pxor r0 u).exec ((XOp.pshufd t t 0xee).exec
        ((XOp.pshufd u t 0x44).exec (s.setXmm t (s.mem.readW (s.gpr kp + BitVec.ofNat 64 (16 * i)) 128)))))) := by
    simp only [dupLow, dupHigh, px, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.load128, hea,
      hin, ite_true, Option.map_some]
  refine ⟨_, hrun, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro l hl
    simp only [XOp.exec, xmm_setXmm, h1, h2, h3, h4, h5, h6, h1.symm, h5.symm, h6.symm,
      ite_true, ite_false, XBinOp.eval, StraightY.qword_xor, qword_dup44 _ hl]
    rw [qword_readW _ _ (by decide)]; simp
  · intro l hl
    simp only [XOp.exec, xmm_setXmm, h1, h2, h3, h4, h5, h1.symm, h5.symm, h6.symm,
      ite_true, ite_false, XBinOp.eval, StraightY.qword_xor, qword_dupee _ hl]
    rw [qword_readW _ _ (by decide), BitVec.add_assoc, ← BitVec.ofNat_add]
  · intro x a b c d
    simp only [XOp.exec, xmm_setXmm, a, b, c, d, ite_false]

/-- The registers of the slices, and two others, as `addRoundKey` takes them. -/
def Regs (r : Nat → XReg) (t u : XReg) : Prop := (∀ j < 8, r j ≠ t ∧ r j ≠ u) ∧ t ≠ u ∧ ∀ i < 8, ∀ j < 8, r i = r j → i = j

theorem regs_q : Regs q .xmm8 .xmm9 := ⟨by decide, by decide, by decide⟩
theorem regs_p : Regs p .xmm0 .xmm1 := ⟨by decide, by decide, by decide⟩

theorem ark_steps {r : Nat → XReg} {t u : XReg} (hr : Regs r t u) (s : State)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (16 * i)) 16) :
    ∀ n ≤ 4, ∃ s', runBlock isa ((List.range n).flatMap fun i =>
        [.movdquLoad t (Impl.Aes.X86_64.at_ kp (16 * i)), dupLow u t, dupHigh t t, px (r (2 * i)) u, px (r (2 * i + 1)) t]) s = some s' ∧
      (∀ l < 2, ∀ j < 8, lane r s' l j = if j < 2 * n then lane r s l j ^^^ s.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * j)) 64
        else lane r s l j) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact ⟨s, rfl, fun l _ j _ => by simp, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s1, e1, h1, g1, m1, r1, w1⟩ := ih (by omega)
    obtain ⟨ht, htu, hinj⟩ := hr
    obtain ⟨s2, e2, ha, hb, hc, g2, m2, r2, w2⟩ := arkStep (r (2 * n)) (r (2 * n + 1)) t u n s1
      ⟨(ht _ (by omega)).1, (ht _ (by omega)).2, (ht _ (by omega)).1, (ht _ (by omega)).2, htu,
        fun h => by have := hinj _ (by omega) _ (by omega) h; omega⟩
      (by rw [r1, w1, g1]; exact hin n (by omega))
    refine ⟨s2, ?_, fun l hl j hj => ?_, g2.trans g1, m2.trans m1, r2.trans r1, w2.trans w1⟩
    · rw [List.range_succ, List.flatMap_append, VG.Interleave.runBlock_append, e1, Option.bind_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, e2]
    · rw [g1, m1] at ha hb
      by_cases h0 : j = 2 * n
      · subst h0
        have := h1 l hl (2 * n) hj
        simp only [Nat.lt_irrefl, ite_false] at this
        simp only [lane] at this ⊢
        rw [ha l hl, this, show 16 * n = 8 * (2 * n) by omega]; simp
      by_cases h0' : j = 2 * n + 1
      · subst h0'
        have := h1 l hl (2 * n + 1) hj
        simp only [show ¬ 2 * n + 1 < 2 * n by omega, ite_false] at this
        simp only [lane] at this ⊢
        rw [hb l hl, this, show 16 * n + 8 = 8 * (2 * n + 1) by omega]; simp; omega
      · have := h1 l hl j hj
        simp only [lane] at this ⊢
        rw [hc (r j) (fun h => h0 (hinj _ hj _ (by omega) h)) (fun h => h0' (hinj _ hj _ (by omega) h)) (ht j hj).1
          (ht j hj).2, this]
        simp only [show (j < 2 * (n + 1)) = (j < 2 * n) by apply propext; omega]

theorem keep_of {s s' : State} (he : Env0 s) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hr : s'.rd = s.rd)
    (hw : s'.wr = s.wr) : Keep s s' where
  env := ⟨he.ok.congr (by rw [hg]) hw, fun m h l hl => by rw [hm, hg]; exact he.masks m h l hl⟩
  gpr := hg
  rd := hr
  wr := hw
  frame := by rw [hm]; exact Frame.refl _ _

theorem ark_ok {r : Nat → XReg} {t u : XReg} (hr : Regs r t u) {s : State} (he : Env0 s)
    {f : Bool} {S : Nat → Spec.Aes.State} (hS : Holds f r s S) {rk : List Byte} (hK : KeyAt s.mem (s.gpr kp) f rk)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (16 * i)) 16) :
    ∃ s', runBlock isa (addRoundKey r t u) s = some s' ∧ Keep s s' ∧
      Holds f r s' fun k => Spec.Aes.addRoundKey (S k) rk := by
  obtain ⟨s', e, h, g, m, hrd, hwr⟩ := ark_steps hr s hin 4 (by decide)
  refine ⟨s', e, keep_of he g m hrd hwr, fun l hl => ?_⟩
  refine BsRel.addRoundKey (rk := fun _ => rk) (hS l hl) hK fun j hj x _ => ?_
  rw [h l hl j hj, ite_eq_left_of_eq_true _ _ (by simp; omega), BitVec.getLsbD_xor]

/-! ## The layers, on states -/

theorem sub_holds {f : Bool} {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds f q s S) :
    ∃ s', runBlock isa subBytes s = some s' ∧ Keep s s' ∧ Holds f p s' fun k => (S k).map sbox0 := by
  obtain ⟨s', e, k, h⟩ := sub_ok sbox_check (fun _ _ => sbox0T_bit) (by decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).map sbox0 fun j hj x hx => h l hl j hj x hx⟩

theorem invSub_holds {f : Bool} {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds f q s S) :
    ∃ s', runBlock isa invSubBytes s = some s' ∧ Keep s s' ∧ Holds f p s' fun k => (S k).map invSbox0 := by
  obtain ⟨s', e, k, h⟩ := sub_ok invSbox_check (fun _ _ => invSbox0T_bit) (by decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).map invSbox0 fun j hj x hx => h l hl j hj x hx⟩

theorem mc_holds (f : Bool) {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds f p s S) :
    ∃ s', runBlock isa (Impl.Aes.X86_64.Sse.mixColumns f) s = some s' ∧ Keep s s' ∧
      Holds f q s' fun k => Spec.Aes.mixColumns (S k) := by
  obtain ⟨s', e, k, h⟩ := layer_ok (is := Impl.Aes.X86_64.Sse.mixColumns f) (r := p) (r' := q)
    (T := mixT mcCoeffs 4 f) (by cases f; exact mc0_check; exact mc1_check) (by cases f <;> decide +kernel)
    (by cases f <;> decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).mixColumns fun j hj x hx => h l hl j hj x hx⟩

theorem invMc_holds (f : Bool) {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds f p s S) :
    ∃ s', runBlock isa (Impl.Aes.X86_64.Sse.invMixColumns f) s = some s' ∧ Keep s s' ∧
      Holds f q s' fun k => Spec.Aes.invMixColumns (S k) := by
  obtain ⟨s', e, k, h⟩ := layer_ok (is := Impl.Aes.X86_64.Sse.invMixColumns f) (r := p) (r' := q)
    (T := mixT invMcCoeffs 4 f) (by cases f; exact invMc0_check; exact invMc1_check)
    (by cases f <;> decide +kernel) (by cases f <;> decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).invMixColumns fun j hj x hx => h l hl j hj x hx⟩

theorem sr2_holds {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds true p s S) :
    ∃ s', runBlock isa (sr2 p .xmm0 .xmm1) s = some s' ∧ Keep s s' ∧
      Holds false p s' fun k => Spec.Aes.shiftRows (S k) := by
  obtain ⟨s', e, k, h⟩ := layer_ok sr2p_check (by decide +kernel) (by decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).sr2 fun j hj x hx => h l hl j hj x hx⟩

theorem invSr2_holds {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds false q s S) :
    ∃ s', runBlock isa (sr2 q .xmm8 .xmm9) s = some s' ∧ Keep s s' ∧
      Holds true q s' fun k => Spec.Aes.invShiftRows (S k) := by
  obtain ⟨s', e, k, h⟩ := layer_ok sr2q_check (by decide +kernel) (by decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).invSr2 fun j hj x hx => h l hl j hj x hx⟩

/-! ## Rounds -/

/-- Round key `i` as stored: `{63}` is added to all but the first. -/
def kr (w : List Byte) (i : Nat) : List Byte :=
  if i = 0 then Spec.Aes.roundKey w 0 else rk63 (Spec.Aes.roundKey w i)

/-- A middle round of the cipher. -/
def rnd (w : List Byte) (i : Nat) (s : Spec.Aes.State) : Spec.Aes.State :=
  Spec.Aes.addRoundKey (Spec.Aes.mixColumns (Spec.Aes.shiftRows (Spec.Aes.subBytes s))) (Spec.Aes.roundKey w i)

/-- The address of round key `i`. -/
def keyAddr (b : Addr) (i : Nat) : Addr := b + BitVec.ofNat 64 (keysOff + 64 * i)

/-- The scratch buffer at `b`, with the round keys: what a batch needs. -/
structure Ready (b : Addr) (nr : Nat) (w : List Byte) (m : Mem) (rd wr : List Region) : Prop where
  sc : ⟨b, 2048⟩ ∈ wr ∨ ⟨b, 1480⟩ ∈ wr
  keys : ∀ i ≤ nr, KeyAt m (keyAddr b i) (i % 2 == 1) (kr w i)
  masks : ∀ k ∈ maskVals, ∀ l < 2, qword (m.readW (xAddr b k.1) 128) l = k.2
  nrs : nr = 10 ∨ nr = 12 ∨ nr = 14
  len : ∀ i ≤ nr, (Spec.Aes.roundKey w i).length = 16

variable {b : Addr} {nr : Nat} {w : List Byte}

theorem Ready.inWr {m : Mem} {rd wr : List Region} (h : Ready b nr w m rd wr) {d n : Nat} (hd : d + n ≤ 1480) :
    InRegions wr (b + BitVec.ofNat 64 d) n := by
  rcases h.sc with h | h
  · exact ⟨_, h, Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨_, h, Offset.contains_base _ hd (by omega)⟩

theorem Ready.frame {m m' : Mem} {rd wr : List Region} (h : Ready b nr w m rd wr) {rs : List Region}
    (hf : Frame rs m m')
    (hk : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 keysOff, 960⟩ r ∧ Region.Disjoint ⟨b + BitVec.ofNat 64 144, 144⟩ r) :
    Ready b nr w m' rd wr where
  sc := h.sc
  nrs := h.nrs
  len := h.len
  keys i hi := by
    refine (h.keys i hi).congrW fun j hj => ?_
    have := h.nrs
    rw [hf.readW (r := ⟨b + BitVec.ofNat 64 keysOff, 960⟩) ?_ (fun r hr => (hk r hr).1) (by decide)]
    rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega) (by decide)
  masks k hm l hl := by
    have h1 := mask_ge k hm
    have h2 := mask_slots k hm
    rw [hf.readW (r := ⟨b + BitVec.ofNat 64 144, 144⟩) ?_ (fun r hr => (hk r hr).2) (by decide)]
    · exact h.masks k hm l hl
    · exact Offset.contains _ (by omega) (by omega) (by decide)

/-- The state between layers: slices of `S` in form `f` in `r`, the next
round key `i` at `kp`; `s₁` is where the batch started. -/
structure RS (s₁ : State) (b : Addr) (nr : Nat) (w : List Byte) (cnt : BitVec 64) (i : Nat) (f : Bool) (r : Nat → XReg)
    (S : Nat → Spec.Aes.State) (s : State) : Prop where
  ready : Ready b nr w s.mem s.rd s.wr
  r9 : s.gpr .r9 = b
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → s.gpr x = s₁.gpr x
  cnt : s.gpr .r10 = cnt
  kpAt : s.gpr .rax = keyAddr b i
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨b, 288⟩] s₁.mem s.mem
  holds : Holds f r s S

theorem RS.env {s₁ s : State} {cnt : BitVec 64} {i : Nat} {f : Bool} {r : Nat → XReg} {S : Nat → Spec.Aes.State}
    (h : RS s₁ b nr w cnt i f r S s) : Env0 s where
  ok := ⟨fun k hk => by
    rw [show s.gpr cfg.base = b from h.r9]
    exact h.ready.inWr (by simp only [cfg] at hk; omega), by decide⟩
  masks := by rw [h.r9]; exact h.ready.masks

theorem low_disj (b : Addr) : ∀ r ∈ [(⟨b, 288⟩ : Region)],
    Region.Disjoint ⟨b + BitVec.ofNat 64 keysOff, 960⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ (by decide) (by decide)

theorem RS.step {s₁ s : State} {cnt : BitVec 64} {i : Nat} {f f' : Bool} {r r' : Nat → XReg}
    {S S' : Nat → Spec.Aes.State} (h : RS s₁ b nr w cnt i f r S s) {is : List Instr}
    (hs : ∃ s', runBlock isa is s = some s' ∧ Keep s s' ∧ Holds f' r' s' S') :
    WP isa (.block is) s (RS s₁ b nr w cnt i f' r' S') := by
  obtain ⟨s', e, k, hh⟩ := hs
  refine WP.of_runBlock ⟨s', e, ?_⟩
  have hf : Frame [⟨b, 288⟩] s.mem s'.mem := by
    have := k.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  refine ⟨⟨by rw [k.wr]; exact h.ready.sc, fun i hi => ?_, ?_, h.ready.nrs, h.ready.len⟩, by rw [k.gpr, h.r9],
    fun x a c => by rw [k.gpr, h.gpr x a c], by rw [k.gpr, h.cnt], by rw [k.gpr, h.kpAt], k.rd.trans h.rd,
    k.wr.trans h.wr, h.frame.trans hf, hh⟩
  · refine (h.ready.keys i hi).congrW fun j hj => ?_
    have := h.ready.nrs
    rw [hf.readW (r := ⟨b + BitVec.ofNat 64 keysOff, 960⟩) ?_ (low_disj b) (by decide)]
    rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega) (by decide)
  · have := k.env.masks
    rwa [k.gpr, h.r9] at this

theorem RS.congr {s₁ s : State} {cnt : BitVec 64} {i : Nat} {f : Bool} {r : Nat → XReg}
    {S S' : Nat → Spec.Aes.State} (h : RS s₁ b nr w cnt i f r S s) (hS : ∀ k < 8, S k = S' k) :
    RS s₁ b nr w cnt i f r S' s :=
  { h with holds := fun l hl => (h.holds l hl).congr fun k hk => hS _ (by omega) }

theorem RS.skip {s₁ s : State} {cnt : BitVec 64} {i : Nat} {r : Nat → XReg}
    {S : Nat → Spec.Aes.State} (h : RS s₁ b nr w cnt i false r S s) :
    RS s₁ b nr w cnt i true r (fun k => Spec.Aes.shiftRows (S k)) s :=
  { h with holds := fun l hl => (h.holds l hl).skipShift }

theorem RS.skipInv {s₁ s : State} {cnt : BitVec 64} {i : Nat} {r : Nat → XReg}
    {S : Nat → Spec.Aes.State} (h : RS s₁ b nr w cnt i true r S s) :
    RS s₁ b nr w cnt i false r (fun k => Spec.Aes.invShiftRows (S k)) s :=
  { h with holds := fun l hl => (h.holds l hl).skipInvShift }

theorem RS.ark {s₁ s : State} {cnt : BitVec 64} {i : Nat} {r : Nat → XReg} {t u : XReg} (hr : Regs r t u)
    {S : Nat → Spec.Aes.State} {f : Bool} (hf : f = (i % 2 == 1)) (hi : i ≤ nr) (h : RS s₁ b nr w cnt i f r S s) :
    WP isa (.block (Impl.Aes.X86_64.Sse.addRoundKey r t u)) s
      (RS s₁ b nr w cnt i f r fun k => Spec.Aes.addRoundKey (S k) (kr w i)) := by
  subst hf
  refine h.step (ark_ok hr h.env h.holds (by rw [show s.gpr kp = keyAddr b i from h.kpAt]; exact h.ready.keys i hi)
    fun j hj => ?_)
  rw [show s.gpr kp = keyAddr b i from h.kpAt, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  have := h.ready.nrs
  obtain ⟨R, hR, hc⟩ := h.ready.inWr (d := keysOff + 64 * i + 16 * j) (n := 16) (by simp only [keysOff]; omega)
  exact ⟨R, List.mem_append_right _ hR, hc⟩

theorem RS.next {s₁ s : State} {cnt : BitVec 64} {i : Nat} {r : Nat → XReg}
    {S : Nat → Spec.Aes.State} {f : Bool} (h : RS s₁ b nr w cnt i f r S s) :
    WP isa (.block [nextKey]) s (RS s₁ b nr w cnt (i + 1) f r S) := by
  apply WP.of_runBlock
  have e : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  simp only [nextKey, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, e, Option.bind_some,
    Option.some.injEq, exists_eq_left', show Impl.Aes.X86_64.Sse.kp = Reg.rax from rfl]
  refine ⟨h.ready, ?_, fun x a c => ?_, ?_, ?_, h.rd, h.wr, h.frame, h.holds⟩
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags]; exact h.r9
  · rw [gpr_setReg_of_ne _ _ a, gpr_arithFlags]; exact h.gpr x a c
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags]; exact h.cnt
  · rw [gpr_setReg_self, h.kpAt, keyAddr, keyAddr, BitVec.add_assoc]
    congr 1
    rw [show keysOff + 64 * (i + 1) = keysOff + 64 * i + 64 by omega, BitVec.ofNat_add (keysOff + 64 * i)]
    rfl

theorem roundA_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} (hi : i % 2 = 1) (hn : i ≤ nr)
    (h : RS s₁ b nr w cnt i false q S s) :
    WP isa (.block roundA) s (RS s₁ b nr w cnt (i + 1) true q fun k => rnd w i (S k)) := by
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (h.step (sub_holds h.env h.holds)) fun s2 h2 => ?_
  refine WP.mono (h2.skip.step (mc_holds true h2.env h2.skip.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.ark regs_q (by simp [hi]) hn) fun s4 h4 => ?_
  refine WP.mono h4.next fun s5 h5 => h5.congr fun k _ => ?_
  rw [kr, ite_eq_right (by omega), round63 _ (h.ready.len i hn), rnd]

theorem roundB_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} (hi : i % 2 = 0) (h0 : i ≠ 0)
    (hn : i ≤ nr) (h : RS s₁ b nr w cnt i true q S s) :
    WP isa (.block roundB) s (RS s₁ b nr w cnt (i + 1) false q fun k => rnd w i (S k)) := by
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append ?_)))
  refine WP.mono (h.step (sub_holds h.env h.holds)) fun s2 h2 => ?_
  refine WP.mono (h2.step (sr2_holds h2.env h2.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.step (mc_holds false h3.env h3.holds)) fun s4 h4 => ?_
  refine WP.mono (h4.ark regs_q (by simp [hi]) hn) fun s5 h5 => ?_
  refine WP.mono h5.next fun s6 h6 => h6.congr fun k _ => ?_
  rw [kr, ite_eq_right h0, round63 _ (h.ready.len i hn), rnd]

end VG.Proof.Aes.X86_64.Sse
