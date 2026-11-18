module

public import VerifiedGarbage.Proof.Blowfish.X86.Ecb
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Rc4.Scan32
public import VerifiedGarbage.Proof.Blowfish.KeyTable
public import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run

/-! ### `Blowfish.X86.KeyP`, which this module and modules that import it used -/

section

/-!
# Blowfish on x86 (32-bit): the initial schedule and the key into the P-array

`initSchedule_steps`: the 1042 words of the initial schedule's image, from
immediates, into the schedule at `ebx`. `keyP_run`: Pᵢ ^= the `i`-th 32 bits
of the key, cycling through its bytes, for the 18 entries.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-! ## The initial schedule -/

theorem initWord32_byte (i : Nat) {b : Nat} (hb : b < 4) :
    (initWord32 i).extractLsb' (8 * b) 8 = initByte (4 * i + b) := by
  have h := initWord_byte (i / 2) (b := 4 * (i % 2) + b) (by omega_arith)
  rw [show 8 * (i / 2) + (4 * (i % 2) + b) = 4 * i + b by omega_arith] at h
  rw [← h, initWord32]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    show 8 * b + j < 32 by omega_arith]
  congr 1; omega_arith

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- One word of the initial schedule. -/
theorem initStore_run (u : State) {i : Nat} (hi : i < 1042) {K : BitVec 32} (fit : K.toNat + 4168 ≤ 2 ^ 32)
    (hb : u.gpr .ebx = K + BitVec.ofNat 32 0) (hw : InRegions u.wr (K.setWidth 64 + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (initStore i)) u fun t =>
      t.mem = u.mem.writeW (K.setWidth 64 + BitVec.ofNat 64 (4 * i)) (initWord32 i) := by
  have ea : addr (K + BitVec.ofNat 32 0) (4 * i) = K.setWidth 64 + BitVec.ofNat 64 (4 * i) := by
    rw [BitVec.add_zero]; exact addr_of_fit (by omega_arith)
  unfold initStore
  brun [hb, ea, hw]

/-- After the first `n` words, from `u₀`. -/
structure InitInv (u₀ : State) (K : BitVec 32) (n : Nat) (t : State) : Prop where
  bytes : ∀ o < 4 * n, t.mem (K.setWidth 64 + BitVec.ofNat 64 o) = initByte o
  frame : Frame [⟨K.setWidth 64, 4168⟩] u₀.mem t.mem
  keep : Keep [.ecx] u₀ t

theorem initSchedule_steps (u₀ : State) {K : BitVec 32} (fit : K.toNat + 4168 ≤ 2 ^ 32)
    (hb : u₀.gpr .ebx = K + BitVec.ofNat 32 0) (hw : InRegions u₀.wr (K.setWidth 64) 4168) :
    ∀ n ≤ 1042, WP isa (.block ((List.range n).flatMap initStore)) u₀ (InitInv u₀ K n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun o ho => absurd ho (by omega_arith), Frame.refl _ _, Keep.refl _ _⟩
  | succ n ih =>
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun t I => ?_
    have hwt : InRegions t.wr (K.setWidth 64 + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [I.keep.2.2]; exact inRegions_off hw (by omega_arith)
    refine WP.mono (WP.keep [.ecx] (initStore_run t (by omega_arith) fit (by rw [I.keep.gpr (by decide), hb]) hwt)
      (by simp [writesOnly, initStore, Code.allInstrs, Taint.clobbers, Taint.dst,
        VG.Proof.MlDsa.X86.Pack.allRegs]))
      fun t' ⟨tm, tk⟩ => ⟨fun o ho => ?_, ?_, (I.keep.trans tk).mono (by decide)⟩
    · rw [tm]
      by_cases hl : o < 4 * n
      · rw [writeW32_other _ (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)), I.bytes o hl]
      · rw [show o = 4 * n + (o - 4 * n) by omega_arith, ← Offset.add_add, st_byte _ _ _ (by omega_arith),
          initWord32_byte _ (by omega_arith)]
    · rw [tm]
      exact I.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))

/-! ## The key into the P-array -/

/-- The key offset after `c`, advanced: back to 0 at the key length. -/
theorem key_next (c L : Nat) (hL : 0 < L) (hL' : L < 2 ^ 32) :
    (if (BitVec.ofNat 32 (c % L) + BitVec.ofNat 32 1 - BitVec.ofNat 32 L == 0) = true then 0#32
      else BitVec.ofNat 32 (c % L) + BitVec.ofNat 32 1) = BitVec.ofNat 32 ((c + 1) % L) := by
  have hb := Nat.mod_lt c hL
  have e1 : BitVec.ofNat 32 (c % L) + BitVec.ofNat 32 1 = BitVec.ofNat 32 (c % L + 1) := by
    rw [← BitVec.ofNat_add]
  have ha : (c + 1) % L = (c % L + 1) % L := by simp only [Nat.add_mod, Nat.mod_mod]
  rw [e1, ofNat_sub_beq' (by omega_arith) hL']
  by_cases h : c % L + 1 = L
  · simp only [decide_eq_true h, ↓reduceIte]; rw [ha, h, Nat.mod_self]
  · rw [decide_eq_false h]
    simp only [Bool.false_eq_true, ite_false]
    rw [ha, Nat.mod_eq_of_lt (show c % L + 1 < L by omega_arith)]

/-- The key bytes: `key` at `Kk`, `L` bytes long, its address and length the
first two arguments on the stack. -/
structure KeyEnv (Kk : BitVec 32) (L : Nat) (u : State) : Prop where
  aRd : ∀ i, i < 2 → InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (4 + 4 * i)) 4
  kVal : u.mem.readW (addr (u.gpr .esp) 4) 32 = Kk
  lVal : u.mem.readW (addr (u.gpr .esp) 8) 32 = BitVec.ofNat 32 L
  pos : 0 < L
  small : L ≤ 56
  fit : Kk.toNat + L ≤ 2 ^ 32
  rd : InRegions (u.rd ++ u.wr) (Kk.setWidth 64) L
  spFit : (u.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem KeyEnv.keep {Kk : BitVec 32} {L : Nat} {u t : State} (E : KeyEnv Kk L u) {rs : List Reg}
    (h : Keep rs u t) (hsp : Reg.esp ∉ rs) (hm : t.mem = u.mem) : KeyEnv Kk L t :=
  ⟨fun i hi => by rw [keep_reads h, h.gpr hsp]; exact E.aRd i hi, by rw [hm, h.gpr hsp]; exact E.kVal,
    by rw [hm, h.gpr hsp]; exact E.lVal, E.pos, E.small, E.fit, by rw [keep_reads h]; exact E.rd,
    by rw [h.gpr hsp]; exact E.spFit⟩

/-- `KeyEnv` after writes apart from the key's address and length. -/
theorem KeyEnv.frame {Kk : BitVec 32} {L : Nat} {u t : State} (E : KeyEnv Kk L u) {rs : List Reg}
    (h : Keep rs u t) (hsp : Reg.esp ∉ rs) {rs' : List Region} (hf : Frame rs' u.mem t.mem)
    (hd : ∀ r ∈ rs', Region.Disjoint ⟨addr (u.gpr .esp) 4, 8⟩ r) : KeyEnv Kk L t := by
  have sp := E.spFit
  refine ⟨fun i hi => by rw [keep_reads h, h.gpr hsp]; exact E.aRd i hi, ?_, ?_, E.pos, E.small, E.fit,
    by rw [keep_reads h]; exact E.rd, by rw [h.gpr hsp]; exact sp⟩
  · rw [h.gpr hsp, hf.readW (contains_pre _ (by decide)) hd (by decide)]; exact E.kVal
  · rw [h.gpr hsp, hf.readW (r := ⟨addr (u.gpr .esp) 4, 8⟩) ?_ hd (by decide)]
    · exact E.lVal
    · rw [addr_of_fit (by omega_arith), addr_of_fit (by omega_arith)]
      exact Offset.contains _ (by decide) (by decide) (by decide)

theorem keyByte_run (u : State) {Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u) (c : Nat)
    (hsi : u.gpr .esi = BitVec.ofNat 32 (c % L)) :
    WP isa keyByte u fun t =>
      t.gpr .edx = (u.gpr .edx).rotateRight 24 ||| (u.mem (Kk.setWidth 64 + BitVec.ofNat 64 (c % L))).setWidth 32 ∧
        t.gpr .esi = BitVec.ofNat 32 ((c + 1) % L) ∧ t.mem = u.mem ∧ Keep [.eax, .ecx, .edx, .esi] u t := by
  have hc := Nat.mod_lt c E.pos
  have fit := E.fit
  have ea : addr (Kk + BitVec.ofNat 32 (c % L)) 0 = Kk.setWidth 64 + BitVec.ofNat 64 (c % L) := by
    unfold addr; rw [BitVec.add_zero, ← addr, addr_of_fit (by omega_arith)]
  have hr : InRegions (u.rd ++ u.wr) (Kk.setWidth 64 + BitVec.ofNat 64 (c % L)) 1 := inRegions_off E.rd (by omega_arith)
  have r4 := E.aRd 0 (by decide)
  have r8 := E.aRd 1 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceAdd] at r4 r8
  unfold keyByte
  apply WP.seq
  refine WP.mono (WP.keep [.eax, .ecx, .edx, .esi] (Q := fun t =>
      t.gpr .edx = (u.gpr .edx).rotateRight 24 ||| (u.mem (Kk.setWidth 64 + BitVec.ofNat 64 (c % L))).setWidth 32 ∧
      t.gpr .esi = BitVec.ofNat 32 (c % L) + BitVec.ofNat 32 1 ∧
      t.zf = some (BitVec.ofNat 32 (c % L) + BitVec.ofNat 32 1 - BitVec.ofNat 32 L == 0) ∧ t.mem = u.mem)
    (by brun [hsi, ea, hr, r4, r8, E.kVal, E.lVal]) (by decide)) fun v ⟨⟨v5, v4, vz, vm⟩, vk⟩ => ?_
  have nx := key_next c L E.pos (by have := E.small; omega_arith)
  refine WP.ite _ (by rw [eval_e, vz]) (fun hz => ?_) (fun hz => ?_)
  · rw [hz] at nx
    refine WP.mono (WP.keep [.esi] (Q := fun t => t.gpr .esi = 0#32 ∧ t.gpr .edx = v.gpr .edx ∧ t.mem = v.mem)
      (by brun) (by decide)) fun t ⟨⟨t4, t5, tm⟩, tk⟩ =>
        ⟨by rw [t5, v5], by rw [t4, ← nx]; rfl, by rw [tm, vm], (vk.trans tk).mono (by decide)⟩
  · rw [hz] at nx
    exact WP.block_nil ⟨v5, by rw [v4, ← nx]; rfl, vm, vk⟩

/-- Rotating right by 24 a word with a clear top byte is a shift left by 8. -/
theorem ror24_small (x : BitVec 32) (h : x.toNat < 2 ^ 24) : x.rotateRight 24 = x <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · have : x.getLsbD (24 + i) = false := by
      simp only [BitVec.getLsbD, Nat.testBit]
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 24 ≤ 24 + i by omega_arith); omega_arith)]
      rfl
    simp [h8, this]
  · simp [h8]

theorem step_small (x : BitVec 32) (b : BitVec 8) {k : Nat} (hx : x.toNat < 2 ^ k) (hk : k + 8 ≤ 32) :
    (x <<< 8 ||| b.setWidth 32).toNat < 2 ^ (k + 8) := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
  have hb := b.isLt
  have h8 : 2 ^ 8 ≤ 2 ^ (k + 8) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  apply Nat.or_lt_two_pow
  · rw [Nat.shiftLeft_eq, Nat.pow_add]
    have := Nat.mod_le (x.toNat * 2 ^ 8) (2 ^ 32)
    have : x.toNat * 2 ^ 8 < 2 ^ k * 2 ^ 8 := Nat.mul_lt_mul_of_pos_right hx (by decide)
    omega_arith
  · have := Nat.mod_le b.toNat (2 ^ 32)
    omega_arith

/-- Four bytes accumulated by rotations, as by shifts. -/
theorem rot_chain (b0 b1 b2 b3 : Byte) :
    ((((0 : Word).rotateRight 24 ||| b0.setWidth 32).rotateRight 24 ||| b1.setWidth 32).rotateRight 24 |||
        b2.setWidth 32).rotateRight 24 ||| b3.setWidth 32 =
      (((((0 : Word) <<< 8 ||| b0.setWidth 32) <<< 8 ||| b1.setWidth 32) <<< 8 ||| b2.setWidth 32) <<< 8 |||
        b3.setWidth 32) := by
  have a1 := step_small 0 b0 (k := 0) (by decide) (by decide)
  have a2 := step_small _ b1 a1 (by decide)
  have a3 := step_small _ b2 a2 (by decide)
  rw [ror24_small 0 (by decide), ror24_small ((0 : Word) <<< 8 ||| b0.setWidth 32) (by omega_arith),
    ror24_small (((0 : Word) <<< 8 ||| b0.setWidth 32) <<< 8 ||| b1.setWidth 32) (by omega_arith), ror24_small _ a3]

/-- The key's byte `c` (mod its length) in memory `m`. -/
abbrev kb (m : Mem) (Kk : BitVec 32) (L c : Nat) : Byte := m (Kk.setWidth 64 + BitVec.ofNat 64 (c % L))

theorem kb_keyWord (m : Mem) (Kk : BitVec 32) {L : Nat} (hL : 0 < L) (w : Nat) :
    (((((0 : Word) <<< 8 ||| (kb m Kk L (4 * w + 0)).setWidth 32) <<< 8 ||| (kb m Kk L (4 * w + 1)).setWidth 32) <<< 8 |||
      (kb m Kk L (4 * w + 2)).setWidth 32) <<< 8 ||| (kb m Kk L (4 * w + 3)).setWidth 32) =
      Spec.Blowfish.keyWord (bytesAt m (Kk.setWidth 64) L) w := by
  have hl : (bytesAt m (Kk.setWidth 64) L).length = L := by simp [bytesAt]
  rw [keyWord_eq, hl, bytesAt_getD _ _ (Nat.mod_lt _ hL), bytesAt_getD _ _ (Nat.mod_lt _ hL),
    bytesAt_getD _ _ (Nat.mod_lt _ hL), bytesAt_getD _ _ (Nat.mod_lt _ hL)]

/-- The tail of `keyWord`. -/
def keyTail : List Instr :=
  [.mov .eax (.mem (at_ .ebx pOff)), .alu .xor .eax (.reg .edx), .store (at_ .ebx pOff) .eax,
   .alu .add .ebx (imm 4), .alu .sub .edi (imm 1)]

/-- The key word of entry `w`: four bytes, the first the most significant,
then `keyTail`. -/
theorem keyWord_run (u : State) {Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u) (w : Nat)
    (hsi : u.gpr .esi = BitVec.ofNat 32 ((4 * w) % L)) {Q : State → Prop}
    (hQ : ∀ t, t.gpr .edx = Spec.Blowfish.keyWord (bytesAt u.mem (Kk.setWidth 64) L) w →
        t.gpr .esi = BitVec.ofNat 32 ((4 * (w + 1)) % L) → t.mem = u.mem → Keep [.eax, .ecx, .edx, .esi] u t →
        WP isa (.block keyTail) t Q) :
    WP isa Impl.Blowfish.X86.keyWord u Q := by
  unfold Impl.Blowfish.X86.keyWord
  apply WP.seq
  refine WP.mono (WP.keep [.edx] (Q := fun t => t.gpr .edx = 0 ∧ t.mem = u.mem) (by brun) (by decide))
    fun t0 ⟨⟨a5, am⟩, ak⟩ => ?_
  have E0 := E.keep ak (by decide) am
  apply WP.seq
  refine WP.mono (keyByte_run t0 E0 (4 * w + 0) (by rw [ak.gpr (by decide), hsi, Nat.add_zero]))
    fun t1 ⟨b5, b4, bm, bk⟩ => ?_
  have E1 := E0.keep bk (by decide) bm
  apply WP.seq
  refine WP.mono (keyByte_run t1 E1 (4 * w + 1) b4) fun t2 ⟨c5, c4, cm, ck⟩ => ?_
  have E2 := E1.keep ck (by decide) cm
  apply WP.seq
  refine WP.mono (keyByte_run t2 E2 (4 * w + 2) c4) fun t3 ⟨d5, d4, dm, dk⟩ => ?_
  have E3 := E2.keep dk (by decide) dm
  refine WP.seq (WP.mono (keyByte_run t3 E3 (4 * w + 3) d4) fun t4 ⟨e5, e4, em, ek⟩ => ?_)
  refine hQ t4 ?_ (by rw [e4]; congr 2) (by rw [em, dm, cm, bm, am])
    (((((ak.trans bk).trans ck).trans dk).trans ek).mono (by decide))
  rw [e5, d5, c5, b5, a5, dm, cm, bm, am, rot_chain]
  exact kb_keyWord _ _ E.pos w

theorem keyTail_run (t : State) {K V : BitVec 32} {a : Addr} (w : Nat)
    (hb : t.gpr .ebx = K + BitVec.ofNat 32 (4 * w)) (hd : t.gpr .edx = V)
    (ea : addr (K + BitVec.ofNat 32 (4 * w)) 4096 = a) (hw : InRegions t.wr a 4) :
    WP isa (.block keyTail) t fun t' =>
      t'.mem = t.mem.writeW a (t.mem.readW a 32 ^^^ V) ∧
      t'.gpr .ebx = K + BitVec.ofNat 32 (4 * (w + 1)) ∧
      t'.gpr .edi = t.gpr .edi - BitVec.ofNat 32 1 ∧ t'.zf = some (t.gpr .edi - BitVec.ofNat 32 1 == 0) := by
  have hr := region_in (rs := t.rd) hw
  unfold keyTail
  brun [hb, hd, ea, hw, hr, pOff]
  rw [ofs_add]; congr 2

/-- After the key words of entries `0, …, w - 1`, from `u₀`. -/
structure KPInv (u₀ : State) (K Kk : BitVec 32) (L w : Nat) (t : State) : Prop where
  le : w ≤ 18
  esi : t.gpr .esi = BitVec.ofNat 32 ((4 * w) % L)
  ebx : t.gpr .ebx = K + BitVec.ofNat 32 (4 * w)
  edi : t.gpr .edi = BitVec.ofNat 32 (18 - w)
  keep : Keep [.eax, .ebx, .ecx, .edx, .esi, .edi] u₀ t
  done : ∀ j < w, t.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * j)) 32 =
    u₀.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * j)) 32 ^^^
      Spec.Blowfish.keyWord (bytesAt u₀.mem (Kk.setWidth 64) L) j
  rest : ∀ j, w ≤ j → j < 18 → t.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * j)) 32 =
    u₀.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * j)) 32
  frame : Frame [⟨K.setWidth 64 + BitVec.ofNat 64 4096, 72⟩] u₀.mem t.mem

theorem keyStep {u₀ : State} {K Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u₀) (fit : K.toNat + 4168 ≤ 2 ^ 32)
    (hw : InRegions u₀.wr (K.setWidth 64 + BitVec.ofNat 64 4096) 72)
    (hd : Region.Disjoint ⟨Kk.setWidth 64, L⟩ ⟨K.setWidth 64 + BitVec.ofNat 64 4096, 72⟩)
    (hA : Region.Disjoint ⟨addr (u₀.gpr .esp) 4, 8⟩ ⟨K.setWidth 64 + BitVec.ofNat 64 4096, 72⟩)
    {w : Nat} (hw18 : w < 18) {t : State} (I : KPInv u₀ K Kk L w t) :
    WP isa Impl.Blowfish.X86.keyWord t fun t' =>
      KPInv u₀ K Kk L (w + 1) t' ∧ t'.zf = some (BitVec.ofNat 32 (18 - (w + 1)) == 0) := by
  have Et := E.frame I.keep (by decide) I.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hA
  refine keyWord_run t Et w I.esi fun v v5 v4 vm vk => ?_
  have ea : addr (K + BitVec.ofNat 32 (4 * w)) 4096 = K.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * w) := by
    unfold addr; rw [ofs_add, ← addr, addr_of_fit (by omega_arith)]; congr 2; omega_arith
  have hwv : InRegions v.wr (K.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * w)) 4 := by
    rw [vk.2.2, I.keep.2.2, ← Offset.add_add]; exact inRegions_off hw (by omega_arith)
  refine WP.mono (WP.keep [.eax, .ebx, .edi] (keyTail_run v w (by rw [vk.gpr (by decide), I.ebx]) v5 ea hwv)
    (by decide))
    fun t' ⟨⟨tm, tb, td, tz⟩, tk⟩ => ?_
  -- the key's bytes are where they were
  have hkey : bytesAt t.mem (Kk.setWidth 64) L = bytesAt u₀.mem (Kk.setWidth 64) L :=
    bytesAt_frame I.frame fun c hc r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact fun h => hd _ (Offset.contains_base _ (by omega_arith) (by have := E.fit; omega_arith)) h
  have hv8 : v.gpr .edi = BitVec.ofNat 32 (18 - w) := by rw [vk.gpr (by decide), I.edi]
  have h8 : BitVec.ofNat 32 (18 - w) - BitVec.ofNat 32 1 = BitVec.ofNat 32 (18 - (w + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  have sepw : ∀ j, j < 18 → j ≠ w → Mem.Sep (K.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * j)) (32 / 8)
      (K.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * w)) (32 / 8) :=
    fun j hj hne => Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨⟨by omega_arith, by rw [tk.gpr (by decide), v4], tb, by rw [td, hv8, h8],
    ((I.keep.trans vk).trans tk).mono (by decide), fun j hj => ?_, fun j h1 h2 => ?_, ?_⟩, by rw [tz, hv8, h8]⟩
  · rw [tm, vm]
    by_cases e : j = w
    · subst e
      rw [Mem.readW_writeW_self32, I.rest j (by omega_arith) hw18, hkey]
    · rw [Mem.readW_writeW_sep (sepw j (by omega_arith) e) (by decide)]; exact I.done j (by omega_arith)
  · rw [tm, vm, Mem.readW_writeW_sep (sepw j h2 (by omega_arith)) (by decide)]; exact I.rest j (by omega_arith) h2
  · rw [tm, vm]
    exact I.frame.writeW List.mem_cons_self _ (Offset.contains (e := 4096) (k := 72) (d := 4096 + 4 * w)
      (n := 4) _ (by omega_arith) (by omega_arith) (by omega_arith))

theorem keyP_run {u₀ : State} {K Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u₀)
    (r12 : InRegions (u₀.rd ++ u₀.wr) (addr (u₀.gpr .esp) 12) 4) (hK : u₀.mem.readW (addr (u₀.gpr .esp) 12) 32 = K)
    (fit : K.toNat + 4168 ≤ 2 ^ 32)
    (hw : InRegions u₀.wr (K.setWidth 64 + BitVec.ofNat 64 4096) 72)
    (hd : Region.Disjoint ⟨Kk.setWidth 64, L⟩ ⟨K.setWidth 64 + BitVec.ofNat 64 4096, 72⟩)
    (hA : Region.Disjoint ⟨addr (u₀.gpr .esp) 4, 8⟩ ⟨K.setWidth 64 + BitVec.ofNat 64 4096, 72⟩) :
    WP isa keyP u₀ (KPInv u₀ K Kk L 18) := by
  unfold keyP
  apply WP.seq
  refine WP.mono (WP.keep [.ebx, .esi, .edi] (Q := fun t => t.gpr .esi = 0#32 ∧
      t.gpr .ebx = K + BitVec.ofNat 32 0 ∧ t.gpr .edi = BitVec.ofNat 32 18 ∧ t.mem = u₀.mem)
    (by brun [r12, hK]) (by decide)) fun u₁ ⟨⟨a4, a12, a8, am⟩, ak⟩ => ?_
  have I0 : KPInv u₀ K Kk L 0 u₁ :=
    ⟨by decide, by rw [a4, Nat.mul_zero, Nat.zero_mod], by rw [a12], by rw [a8], ak.mono (by decide),
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ _ => by rw [am], by rw [am]; exact Frame.refl _ _⟩
  refine WP.loop (M := isa) (Q := KPInv u₀ K Kk L 18)
    (fun (n : Nat) (v : State) => ∃ w, w < 18 ∧ n = 18 - w ∧ KPInv u₀ K Kk L w v) ?_ 18 u₁ ⟨0, by decide, rfl, I0⟩
  intro n v ⟨w, hw', hn, J⟩
  refine WP.mono (keyStep E fit hw hd hA hw' J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : w + 1 = 18
  · left
    exact ⟨by rw [e]; rfl, e ▸ J'⟩
  · right
    have nz : BitVec.ofNat 32 (18 - (w + 1)) ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_arith, w + 1, by omega_arith, rfl, J'⟩

end VG.Proof.Blowfish.X86

end

end

/-! ### `Blowfish.X86.KeyEnc`, which this module and modules that import it used -/

section

/-!
# Blowfish on x86 (32-bit): key expansion's 521 encryptions

Each encryption runs the block function under the schedule as written so
far, and its output replaces the next two entries: the P-array's, as words
(`encryptP_run`), then the S-boxes', a byte per plane (`encryptS_run`). The
pointer to the next entries and the encryptions left are in the working
space, at `ebp + 32` and `ebp + 36`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- What the encryptions need of the state they start in: the schedule at
`K` (its address the third argument) and the working space at `B`, writable,
apart from each other and from the argument. -/
structure EncEnv (K B : BitVec 32) (s₀ : State) : Prop where
  fitK : K.toNat + 4168 ≤ 2 ^ 32
  fitB : B.toNat + 64 ≤ 2 ^ 32
  wrK : InRegions s₀.wr (K.setWidth 64) 4168
  wrB : InRegions s₀.wr (B.setWidth 64) 64
  sep : Region.Disjoint ⟨K.setWidth 64, 4168⟩ ⟨B.setWidth 64, 64⟩
  rdA : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 12) 4
  valA : s₀.mem.readW (addr (s₀.gpr .esp) 12) 32 = K
  sepKA : Region.Disjoint ⟨K.setWidth 64, 4168⟩ ⟨addr (s₀.gpr .esp) 12, 4⟩
  sepBA : Region.Disjoint ⟨B.setWidth 64, 64⟩ ⟨addr (s₀.gpr .esp) 12, 4⟩

/-- After `j` encryptions. -/
structure EncInv (key : List Byte) (K B : BitVec 32) (s₀ : State) (j : Nat) (u : State) : Prop where
  le : j ≤ 521
  esp : u.gpr .esp = s₀.gpr .esp
  ebp : u.gpr .ebp = B
  sched : scheduleAt u.mem (K.setWidth 64) = (ksIter key j).1
  halves : (u.mem.readW (slot B 16) 32, u.mem.readW (slot B 20) 32) = (ksIter key j).2
  saved : Saved u.mem B s₀
  frame : Frame [⟨K.setWidth 64, 4168⟩, ⟨B.setWidth 64, 64⟩] s₀.mem u.mem
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr

theorem EncEnv.wK {K B : BitVec 32} {s₀ u : State} (E : EncEnv K B s₀) (hw : u.wr = s₀.wr) {o n : Nat}
    (h : o + n ≤ 4168) : InRegions u.wr (K.setWidth 64 + BitVec.ofNat 64 o) n := by
  rw [hw]; exact inRegions_off E.wrK h

theorem EncEnv.wB {K B : BitVec 32} {s₀ u : State} (E : EncEnv K B s₀) (hw : u.wr = s₀.wr) {o n : Nat}
    (h : o + n ≤ 64) : InRegions u.wr (slot B o) n := by
  rw [hw]; exact inRegions_off E.wrB h

/-- The schedule's address on the stack, after writes to the schedule and the working space. -/
theorem EncEnv.arg {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {m : Mem}
    (hf : Frame [⟨K.setWidth 64, 4168⟩, ⟨B.setWidth 64, 64⟩] s₀.mem m) :
    m.readW (addr (s₀.gpr .esp) 12) 32 = K := by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => (mem_two hr).elim (· ▸ E.sepKA.symm) (· ▸ E.sepBA.symm))
    (by decide)]
  exact E.valA

theorem EncInv.cenv {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {j : Nat} {u : State}
    (I : EncInv key K B s₀ j u) : CipherEnv 12 K B u := by
  have fK := E.fitK
  have fB := E.fitB
  refine ⟨I.ebp, by omega_arith, by rw [I.wr]; exact inRegions_pre E.wrB (by decide), ?_, ?_, fK, fun o ho => ?_,
    E.sep.symm.sub_left (Region.sub_prefix (by decide)), ?_⟩
  · rw [I.rd, I.wr, I.esp]; exact E.rdA
  · rw [I.esp]; exact E.arg I.frame
  · rw [I.rd, I.wr]; exact region_in (inRegions_off E.wrK (by omega_arith))
  · rw [I.esp]; exact E.sepBA.sub_left (Region.sub_prefix (by decide))

/-- The schedule after the block function's writes to the working space. -/
theorem EncEnv.sched_c {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {m m' : Mem}
    (hf : Frame (cRegion B) m m') : scheduleAt m' (K.setWidth 64) = scheduleAt m (K.setWidth 64) :=
  scheduleAt_eq_of_frame _ hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact E.sep.sub_right (Offset.sub_base _ (by decide))

/-- An address at an offset of a pointer at an offset of `K`. -/
theorem addr_ofs {K : BitVec 32} {a b : Nat} (h : K.toNat + a + b < 2 ^ 32) :
    addr (K + BitVec.ofNat 32 a) b = K.setWidth 64 + BitVec.ofNat 64 (a + b) := by
  unfold addr; rw [ofs_add, ← addr, addr_of_fit (by omega_arith)]

theorem ord_true : ord true = id := rfl

/-- The encryption of the last output. -/
theorem enc_cipher {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {j : Nat} {u : State}
    (I : EncInv key K B s₀ j u) :
    WP isa (cipher 12 true) u fun u' =>
      (u'.mem.readW (slot B 16) 32, u'.mem.readW (slot B 20) 32) =
        encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2 ∧
        Keep lookRegs u u' ∧ Frame (cRegion B) u.mem u'.mem := by
  refine WP.mono (cipher_run (I.cenv E) true) fun u' ⟨h, k, m⟩ => ⟨?_, k, m⟩
  rw [h, I.sched, ord_true, ← I.halves]; rfl

theorem ksIter_step (key : List Byte) {j : Nat} (hj : j < 521) :
    ksIter key (j + 1) =
      (((ksIter key j).1.set (2 * j) (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1
          (by omega_arith)).set (2 * j + 1)
          (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 (by omega_arith),
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1,
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2) := by
  rw [ksIter_succ, ksStep, set!_eq_set _ (by omega_arith), set!_eq_set _ (by omega_arith)]

/-- The working space's pointer and counter, written. -/
theorem slots_facts (m : Mem) (B : BitVec 32) (P C : BitVec 32) :
    let M := (m.writeW (slot B 32) P).writeW (slot B 36) C
    M.readW (slot B 32) 32 = P ∧ M.readW (slot B 36) 32 = C ∧ Frame [⟨slot B 32, 8⟩] m M := by
  intro M
  refine ⟨by rw [Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32], Mem.readW_writeW_self32 _ _ _, ?_⟩
  exact ((Frame.refl _ m).writeW List.mem_cons_self _
    (Offset.contains (e := 32) (k := 8) (d := 32) (n := 4) _ (by decide) (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains (e := 32) (k := 8) (d := 36) (n := 4) _ (by decide) (by decide) (by decide))

/-- The output's words to the P-array entries at the pointer, the next pair's
pointer, and the counter less one. -/
theorem storeP_run (u : State) {B P C : BitVec 32} {Pa : Addr} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (r16 : InRegions (u.rd ++ u.wr) (slot B 16) 4)
    (r20 : InRegions (u.rd ++ u.wr) (slot B 20) 4) (w32 : InRegions u.wr (slot B 32) 4)
    (w36 : InRegions u.wr (slot B 36) 4) (hP : u.mem.readW (slot B 32) 32 = P)
    (hC : u.mem.readW (slot B 36) 32 = C) (e0 : addr P 0 = Pa) (e4 : addr P 4 = Pa + BitVec.ofNat 64 4)
    (w0 : InRegions u.wr Pa 4) (w4 : InRegions u.wr (Pa + BitVec.ofNat 64 4) 4)
    (sep : Mem.Sep (slot B 20) (32 / 8) Pa (32 / 8)) :
    WP isa (.block storeP) u fun t =>
      t.mem = (((u.mem.writeW Pa (u.mem.readW (slot B 16) 32)).writeW (Pa + BitVec.ofNat 64 4)
          (u.mem.readW (slot B 20) 32)).writeW (slot B 32) (P + BitVec.ofNat 32 8)).writeW (slot B 36)
          (C - BitVec.ofNat 32 1) ∧
        t.zf = some (C - BitVec.ofNat 32 1 == 0) := by
  obtain r32 := region_in (rs := u.rd) w32
  obtain r36 := region_in (rs := u.rd) w36
  obtain e : ∀ v : BitVec 32, (u.mem.writeW Pa v).readW (slot B 20) 32 = u.mem.readW (slot B 20) 32 :=
    fun v => Mem.readW_writeW_sep sep (by decide)
  unfold storeP
  brun [hb, addr_slot bfit, r16, r20, r32, r36, w32, w36, hP, hC, e0, e4, w0, w4, e]

/-- The P-array phase: after `j` encryptions, the pointer at P-array entry
`2 j` and `9 - j` left. -/
structure PInv (key : List Byte) (K B : BitVec 32) (s₀ : State) (j : Nat) (u : State) : Prop where
  enc : EncInv key K B s₀ j u
  le : j ≤ 9
  ptr : u.mem.readW (slot B 32) 32 = K + BitVec.ofNat 32 (4096 + 8 * j)
  cnt : u.mem.readW (slot B 36) 32 = BitVec.ofNat 32 (9 - j)

/-- The block function's writes, and the stores' to the working space. -/
abbrev wRegions (K B : BitVec 32) : List Region := [⟨K.setWidth 64, 4168⟩, ⟨slot B 16, 24⟩]

theorem saved_frame {m m' : Mem} {K B : BitVec 32} {s₀ : State} (h : Saved m B s₀) (hf : Frame (wRegions K B) m m')
    (sep : Region.Disjoint ⟨K.setWidth 64, 4168⟩ ⟨B.setWidth 64, 64⟩) (fB : B.toNat + 64 ≤ 2 ^ 32) : Saved m' B s₀ :=
  h.frame hf fun r hr => by
    rcases mem_two hr with rfl | rfl
    · exact sep.symm.sub_left (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint _ (by decide) (by have := fB; omega_arith)

theorem wRegions_sub {K B : BitVec 32} {r : Region} (hr : r ∈ wRegions K B) :
    ∃ r' ∈ [(⟨K.setWidth 64, 4168⟩ : Region), ⟨B.setWidth 64, 64⟩], Region.Sub r r' := by
  rcases mem_two hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩

/-- A slot of the working space, apart from the schedule. -/
theorem EncEnv.sepKB {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {d o : Nat} (hd : d + 4 ≤ 64)
    (ho : o + 4 ≤ 4168) : Mem.Sep (slot B d) (32 / 8) (K.setWidth 64 + BitVec.ofNat 64 o) (32 / 8) :=
  E.sep.symm.sep (Offset.contains_base _ hd (by omega_arith)) (Offset.contains_base _ ho (by omega_arith))

/-- The block function's writes leave the working space's pointer and counter. -/
theorem cipher_past {B : BitVec 32} {m m' : Mem} (hf : Frame (cRegion B) m m') {d : Nat} (h1 : 32 ≤ d)
    (h2 : d + 4 ≤ 40) : m'.readW (slot B d) 32 = m.readW (slot B d) 32 :=
  hf.readW (r := ⟨slot B d, 4⟩) (contains_pre _ (by decide)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint (B.setWidth 64) (d := d) (n := 4) (e := 16) (k := 16) (by omega_arith) (by omega_arith)
      (by omega_arith)) (by decide)

theorem cipher_wide {K B : BitVec 32} {m m' : Mem} (hf : Frame (cRegion B) m m') : Frame (wRegions K B) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩

theorem slots_wide {K B : BitVec 32} {m m' : Mem} (hf : Frame [⟨slot B 32, 8⟩] m m') : Frame (wRegions K B) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩

theorem encP_step {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {j : Nat} (hj : j < 9)
    {u : State} (I : PInv key K B s₀ j u) :
    WP isa (.seq (cipher 12 true) (.block storeP)) u fun u' =>
      PInv key K B s₀ (j + 1) u' ∧ u'.zf = some (BitVec.ofNat 32 (9 - (j + 1)) == 0) := by
  have fK := E.fitK
  have fB := E.fitB
  have J := I.enc
  apply WP.seq
  refine WP.mono (enc_cipher E J) fun u₁ ⟨c12, ck, cf⟩ => ?_
  let out := encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2
  let a := 4096 + 4 * (2 * j)
  obtain e0 : addr (K + BitVec.ofNat 32 (4096 + 8 * j)) 0 = K.setWidth 64 + BitVec.ofNat 64 a := by
    rw [addr_ofs (by omega_arith)]; congr 2; omega_arith
  obtain e4 : addr (K + BitVec.ofNat 32 (4096 + 8 * j)) 4 = K.setWidth 64 + BitVec.ofNat 64 a + BitVec.ofNat 64 4 := by
    rw [addr_ofs (by omega_arith), Offset.add_add]; congr 2; omega_arith
  obtain w₁ : u₁.wr = s₀.wr := by rw [ck.2.2, J.wr]
  refine WP.mono (WP.keep [.eax, .ebx, .edx] (storeP_run u₁ (C := BitVec.ofNat 32 (9 - j))
    ((ck.gpr (by decide)).trans J.ebp) (by omega_arith) (region_in (E.wB w₁ (by decide)))
    (region_in (E.wB w₁ (by decide))) (E.wB w₁ (by decide)) (E.wB w₁ (by decide))
    (by rw [cipher_past cf (by decide) (by decide)]; exact I.ptr)
    (by rw [cipher_past cf (by decide) (by decide)]; exact I.cnt) e0 e4 (E.wK w₁ (by omega_arith))
    (by rw [Offset.add_add]; exact E.wK w₁ (by omega_arith)) (E.sepKB (by decide) (by omega_arith))) (by
      decide))
    fun u₂ ⟨⟨sm, sz⟩, sk⟩ => ?_
  rw [Offset.add_add] at sm
  obtain ⟨M32, M36, MF⟩ := slots_facts ((u₁.mem.writeW (K.setWidth 64 + BitVec.ofNat 64 a)
    (u₁.mem.readW (slot B 16) 32)).writeW (K.setWidth 64 + BitVec.ofNat 64 (a + 4)) (u₁.mem.readW (slot B 20) 32))
    B (K + BitVec.ofNat 32 (4096 + 8 * j) + BitVec.ofNat 32 8) (BitVec.ofNat 32 (9 - j) - BitVec.ofNat 32 1)
  rw [← sm] at M32 M36 MF
  obtain F2 : Frame [⟨K.setWidth 64, 4168⟩] u₁.mem ((u₁.mem.writeW (K.setWidth 64 + BitVec.ofNat 64 a)
      (u₁.mem.readW (slot B 16) 32)).writeW (K.setWidth 64 + BitVec.ofNat 64 (a + 4)) (u₁.mem.readW (slot B 20) 32)) :=
    ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  obtain FF : Frame (wRegions K B) u.mem u₂.mem :=
    ((cipher_wide cf).trans (F2.mono (by simp))).trans (slots_wide MF)
  obtain h1 : u₁.mem.readW (slot B 16) 32 = out.1 := congrArg Prod.fst c12
  obtain h2 : u₁.mem.readW (slot B 20) 32 = out.2 := congrArg Prod.snd c12
  obtain hsched : scheduleAt u₂.mem (K.setWidth 64) = (ksIter key (j + 1)).1 := by
    rw [scheduleAt_eq_of_frame _ MF (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.sep.sub_right (Offset.sub_base _ (by decide))),
      show a + 4 = 4096 + 4 * (2 * j + 1) by omega_arith,
      scheduleAt_writeW_P _ _ (by omega_arith), scheduleAt_writeW_P _ _ (by omega_arith),
      E.sched_c cf, J.sched, ksIter_step key (by omega_arith), h1, h2]
  obtain rd2 : ∀ d, d + 4 ≤ 32 → u₂.mem.readW (slot B d) 32 = u₁.mem.readW (slot B d) 32 := fun d hd => by
    rw [sm, Mem.readW_writeW_sep (slot_sep B (by omega_arith) (by omega_arith) (by decide)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (by omega_arith) (by omega_arith) (by decide)) (by decide),
      Mem.readW_writeW_sep (E.sepKB (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (E.sepKB (by omega_arith) (by omega_arith)) (by decide)]
  refine ⟨⟨⟨by omega_arith, (sk.gpr (by decide)).trans ((ck.gpr (by decide)).trans J.esp),
    (sk.gpr (by decide)).trans ((ck.gpr (by decide)).trans J.ebp), hsched, ?_,
    saved_frame J.saved FF E.sep fB, J.frame.trans (FF.sub fun r hr => wRegions_sub hr), by rw [sk.2.1, ck.2.1, J.rd],
    by rw [sk.2.2, w₁]⟩, by omega_arith, by rw [M32, ofs_add]; congr 2, ?_⟩, ?_⟩
  · rw [rd2 16 (by decide), rd2 20 (by decide), c12, ksIter_step key (by omega_arith)]
  · rw [M36]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  · rw [sz]; congr 2; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith

/-- Writing the working space's pointer and counter keeps an encryption's
invariant. -/
theorem EncInv.slots {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {j : Nat}
    {u u' : State} (I : EncInv key K B s₀ j u) {P C : BitVec 32}
    (hm : u'.mem = (u.mem.writeW (slot B 32) P).writeW (slot B 36) C) {rs : List Reg} (k : Keep rs u u')
    (hsp : Reg.esp ∉ rs) (hbp : Reg.ebp ∉ rs) :
    EncInv key K B s₀ j u' ∧ u'.mem.readW (slot B 32) 32 = P ∧ u'.mem.readW (slot B 36) 32 = C := by
  obtain ⟨M32, M36, MF⟩ := slots_facts u.mem B P C
  rw [← hm] at M32 M36 MF
  obtain rd : ∀ d, d + 4 ≤ 32 → u'.mem.readW (slot B d) 32 = u.mem.readW (slot B d) 32 := fun d hd => by
    rw [hm, Mem.readW_writeW_sep (slot_sep B (by omega_arith) (by omega_arith) (by decide)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (by omega_arith) (by omega_arith) (by decide)) (by decide)]
  refine ⟨⟨I.le, (k.gpr hsp).trans I.esp, (k.gpr hbp).trans I.ebp, ?_, by rw [rd 16 (by decide),
    rd 20 (by decide), I.halves], saved_frame I.saved (slots_wide MF) E.sep E.fitB,
    I.frame.trans ((slots_wide MF).sub fun r hr => wRegions_sub hr), by rw [k.2.1, I.rd], by rw [k.2.2, I.wr]⟩,
    M32, M36⟩
  rw [scheduleAt_eq_of_frame _ MF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact E.sep.sub_right (Offset.sub_base _ (by decide))), I.sched]

theorem encryptP_run {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {u : State}
    (I : EncInv key K B s₀ 0 u) : WP isa encryptP u (EncInv key K B s₀ 9) := by
  have fB := E.fitB
  obtain w32 := E.wB I.wr (o := 32) (n := 4) (by decide)
  obtain w36 := E.wB I.wr (o := 36) (n := 4) (by decide)
  obtain rA : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 12) 4 := by rw [I.rd, I.wr, I.esp]; exact E.rdA
  obtain vA : u.mem.readW (addr (u.gpr .esp) 12) 32 = K := by rw [I.esp]; exact E.arg I.frame
  unfold encryptP
  apply WP.seq
  refine WP.mono (WP.keep [.ebx, .ecx] (Q := fun t => t.mem = (u.mem.writeW (slot B 32)
      (K + BitVec.ofNat 32 4096)).writeW (slot B 36) (BitVec.ofNat 32 9))
    (by brun [I.ebp, addr_slot (show B.toNat + 40 ≤ 2 ^ 32 by omega_arith), w32, w36, rA, vA, pOff]) (by
      decide))
    fun u₁ ⟨m₁, k₁⟩ => ?_
  obtain ⟨J, j32, j36⟩ := I.slots E m₁ k₁ (by decide) (by decide)
  refine WP.mono (WP.loop (M := isa) (Q := PInv key K B s₀ 9)
    (fun (n : Nat) (v : State) => ∃ j, j < 9 ∧ n = 9 - j ∧ PInv key K B s₀ j v) ?_ 9 u₁
    ⟨0, by decide, rfl, ⟨J, by decide, by rw [j32], by rw [j36]⟩⟩) fun v V => V.enc
  intro n v ⟨j, hj, hn, P⟩
  refine WP.mono (encP_step E hj P) fun v' ⟨P', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : j + 1 = 9
  · left
    exact ⟨by rw [e]; rfl, e ▸ P'⟩
  · right
    obtain nz : BitVec.ofNat 32 (9 - (j + 1)) ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_arith, j + 1, by omega_arith, rfl, P'⟩

/-- The bytes of `x` and `y` into the planes of S-box entries `q` and `q + 1`. -/
def sWrites (m : Mem) (Ka : Addr) (q : Nat) (x y : BitVec 32) : Mem :=
  (((((((m.writeW (Ka + BitVec.ofNat 64 (q + 0)) (BitVec.setWidth 8 x)).writeW
    (Ka + BitVec.ofNat 64 (q + 256)) (BitVec.setWidth 8 (x >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 512)) (BitVec.setWidth 8 (x >>> 8 >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 768)) (BitVec.setWidth 8 (x >>> 8 >>> 8 >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 1)) (BitVec.setWidth 8 y)).writeW
    (Ka + BitVec.ofNat 64 (q + 257)) (BitVec.setWidth 8 (y >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 513)) (BitVec.setWidth 8 (y >>> 8 >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 769)) (BitVec.setWidth 8 (y >>> 8 >>> 8 >>> 8))

/-- A byte written into the schedule. -/
theorem frame_byte {m m' : Mem} {Ka : Addr} (hf : Frame [⟨Ka, 4168⟩] m m') {o : Nat} (ho : o < 4168)
    (v : Byte) : Frame [⟨Ka, 4168⟩] m (m'.writeW (Ka + BitVec.ofNat 64 o) v) :=
  hf.writeW List.mem_cons_self _ (Offset.contains_base _ (by show o + 1 ≤ 4168; omega_arith) (by omega_arith))

/-- What four byte writes into the schedule leave: four bytes apart from it. -/
theorem read_past_bytes {m : Mem} {Ka a : Addr} (hd : Region.Disjoint ⟨a, 4⟩ ⟨Ka, 4168⟩) {o0 o1 o2 o3 : Nat}
    (h0 : o0 < 4168) (h1 : o1 < 4168) (h2 : o2 < 4168) (h3 : o3 < 4168) (v0 v1 v2 v3 : Byte) :
    ((((m.writeW (Ka + BitVec.ofNat 64 o0) v0).writeW (Ka + BitVec.ofNat 64 o1) v1).writeW
      (Ka + BitVec.ofNat 64 o2) v2).writeW (Ka + BitVec.ofNat 64 o3) v3).readW a 32 = m.readW a 32 :=
  (frame_byte (frame_byte (frame_byte (frame_byte (Frame.refl _ m) h0 v0) h1 v1) h2 v2) h3 v3).readW
    (r := ⟨a, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)

theorem read_past_sWrites {m : Mem} {Ka a : Addr} (hd : Region.Disjoint ⟨a, 4⟩ ⟨Ka, 4168⟩) {q : Nat}
    (hq : q + 770 ≤ 4168) (x y : BitVec 32) : (sWrites m Ka q x y).readW a 32 = m.readW a 32 := by
  unfold sWrites
  rw [read_past_bytes hd (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
    read_past_bytes hd (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]

theorem sWrites_frame (m : Mem) (Ka : Addr) {q : Nat} (hq : q + 770 ≤ 4168) (x y : BitVec 32) :
    Frame [⟨Ka, 4168⟩] m (sWrites m Ka q x y) := by
  unfold sWrites
  exact frame_byte (frame_byte (frame_byte (frame_byte (frame_byte (frame_byte (frame_byte (frame_byte
    (Frame.refl _ _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _)
    (by omega_arith) _) (by omega_arith) _

/-- The head of `storeS`. -/
def storeSHead : List Instr :=
  [.mov .ebx (.mem (at_ .ebp ptrOff)), .mov .edx (.mem (at_ .ebp cntOff)), .mov .eax (.mem (at_ .ebp xlOff))] ++
    storeEntry 0 ++ [.mov .eax (.mem (at_ .ebp xrOff))] ++ storeEntry 1 ++
    [.alu .add .ebx (imm 2), .mov .ecx (.mem (at_ .esp 12)), .alu .sub .ecx (.reg .ebx), .alu .test .ecx (imm 255)]

theorem storeSHead_run (u : State) {B K C : BitVec 32} {q : Nat} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (r16 : InRegions (u.rd ++ u.wr) (slot B 16) 4)
    (r20 : InRegions (u.rd ++ u.wr) (slot B 20) 4) (r32 : InRegions (u.rd ++ u.wr) (slot B 32) 4)
    (r36 : InRegions (u.rd ++ u.wr) (slot B 36) 4)
    (hP : u.mem.readW (slot B 32) 32 = K + BitVec.ofNat 32 q) (hC : u.mem.readW (slot B 36) 32 = C)
    (rA : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 12) 4)
    (eK : ∀ c, c < 770 → addr (K + BitVec.ofNat 32 q) c = K.setWidth 64 + BitVec.ofNat 64 (q + c))
    (w : ∀ c, c < 770 → InRegions u.wr (K.setWidth 64 + BitVec.ofNat 64 (q + c)) 1) (hq : q + 770 ≤ 4168)
    (d20 : Region.Disjoint ⟨slot B 20, 4⟩ ⟨K.setWidth 64, 4168⟩)
    (dA : Region.Disjoint ⟨addr (u.gpr .esp) 12, 4⟩ ⟨K.setWidth 64, 4168⟩) :
    WP isa (.block storeSHead) u fun t =>
      t.mem = sWrites u.mem (K.setWidth 64) q (u.mem.readW (slot B 16) 32) (u.mem.readW (slot B 20) 32) ∧
      t.gpr .ebx = K + BitVec.ofNat 32 q + BitVec.ofNat 32 2 ∧ t.gpr .edx = C ∧
      t.zf = some ((u.mem.readW (addr (u.gpr .esp) 12) 32 - (K + BitVec.ofNat 32 q + BitVec.ofNat 32 2) &&&
        BitVec.ofNat 32 255) == 0) := by
  obtain p20 := read_past_bytes (m := u.mem) d20 (o0 := q + 0) (o1 := q + 256) (o2 := q + 512) (o3 := q + 768)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
  obtain pA' := fun v0 v1 v2 v3 v4 v5 v6 v7 => (read_past_bytes (m := (((u.mem.writeW
    (K.setWidth 64 + BitVec.ofNat 64 (q + 0)) v0).writeW (K.setWidth 64 + BitVec.ofNat 64 (q + 256)) v1).writeW
    (K.setWidth 64 + BitVec.ofNat 64 (q + 512)) v2).writeW (K.setWidth 64 + BitVec.ofNat 64 (q + 768)) v3)
    dA (o0 := q + 1) (o1 := q + 257) (o2 := q + 513) (o3 := q + 769) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    v4 v5 v6 v7).trans (read_past_bytes (m := u.mem) dA (o0 := q + 0) (o1 := q + 256) (o2 := q + 512)
    (o3 := q + 768) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) v0 v1 v2 v3)
  unfold sWrites
  obtain e1 := eK 0 (by decide)
  obtain e2 := eK 256 (by decide)
  obtain e3 := eK 512 (by decide)
  obtain e4 := eK 768 (by decide)
  obtain e5 := eK 1 (by decide)
  obtain e6 := eK 257 (by decide)
  obtain e7 := eK 513 (by decide)
  obtain e8 := eK 769 (by decide)
  obtain w1 := w 0 (by decide)
  obtain w2 := w 256 (by decide)
  obtain w3 := w 512 (by decide)
  obtain w4 := w 768 (by decide)
  obtain w5 := w 1 (by decide)
  obtain w6 := w 257 (by decide)
  obtain w7 := w 513 (by decide)
  obtain w8 := w 769 (by decide)
  unfold storeSHead storeEntry
  brun [hb, addr_slot bfit, r16, r20, r32, r36, hP, hC, rA, e1, e2, e3, e4, e5, e6, e7, e8, w1, w2, w3, w4,
    w5, w6, w7, w8, Nat.reduceAdd, p20, pA']

theorem sAnd_z (K : BitVec 32) (q : Nat) (hq : q + 2 < 2 ^ 32) :
    (K - (K + BitVec.ofNat 32 q + BitVec.ofNat 32 2) &&& BitVec.ofNat 32 255 == 0) =
      decide ((q + 2) % 256 = 0) := by
  obtain e : K - (K + BitVec.ofNat 32 q + BitVec.ofNat 32 2) &&& BitVec.ofNat 32 255 =
      BitVec.ofNat 32 ((2 ^ 32 - (q + 2)) % 256) := by
    rw [ofs_add, ofs_neg]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (255 % 2 ^ 32 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega_arith
  rw [e]
  by_cases h : (q + 2) % 256 = 0
  · have : (2 ^ 32 - (q + 2)) % 256 = 0 := by omega_arith
    rw [this]; simp [h]
  · have : BitVec.ofNat 32 ((2 ^ 32 - (q + 2)) % 256) ≠ 0 := by
      intro e'; have := congrArg BitVec.toNat e'; simp at this; omega_arith
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem storeSTail_run (u : State) {B C : BitVec 32} (hb : u.gpr .ebp = B) (bfit : B.toNat + 40 ≤ 2 ^ 32)
    (w32 : InRegions u.wr (slot B 32) 4) (w36 : InRegions u.wr (slot B 36) 4) (hd : u.gpr .edx = C) :
    WP isa (.block [.store (at_ .ebp ptrOff) .ebx, .alu .sub .edx (imm 1), .store (at_ .ebp cntOff) .edx]) u
      fun t => t.mem = (u.mem.writeW (slot B 32) (u.gpr .ebx)).writeW (slot B 36) (C - BitVec.ofNat 32 1) ∧
        t.zf = some (C - BitVec.ofNat 32 1 == 0) := by
  brun [hb, addr_slot bfit, w32, w36, hd]

/-- The offset of S-box entry `sDone j`'s first plane. -/
def sOff (j : Nat) : Nat := 1024 * (sDone j / 256) + sDone j % 256

theorem sOff_entry {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) {b k : Nat} (hk : k < 2) :
    sOff j + (256 * b + k) = entryOff (2 * j + k) b := by
  rw [← entryOff_sbox h9 hj k hk, sOff]

theorem sOff_lt {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) : sOff j ≤ 3326 := by
  unfold sOff sDone; omega_arith

theorem sOff_succ {j : Nat} (h9 : 9 ≤ j) :
    sOff (j + 1) = if (sOff j + 2) % 256 = 0 then sOff j + 2 + 768 else sOff j + 2 := by
  unfold sOff sDone; split <;> omega_arith

theorem shr_shr (x : BitVec 32) : x >>> 8 >>> 8 = x >>> 16 := by rw [← BitVec.shiftRight_add]
theorem shr_shr_shr (x : BitVec 32) : x >>> 8 >>> 8 >>> 8 = x >>> 24 := by
  rw [shr_shr, ← BitVec.shiftRight_add]

theorem low_byte (x : BitVec 32) : x.setWidth 8 = x.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem sWrites_sched (m : Mem) (Ka : Addr) {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) (x y : BitVec 32) :
    scheduleAt (sWrites m Ka (sOff j) x y) Ka = ((scheduleAt m Ka).set (2 * j) x (by omega_arith)).set (2 * j + 1) y
      (by omega_arith) := by
  obtain e : ∀ b k, k < 2 → sOff j + (256 * b + k) = entryOff (2 * j + k) b := fun b k hk => sOff_entry h9 hj hk
  unfold sWrites
  simp only [Proof.Rc4.writeW_byte8, shr_shr_shr]
  simp only [shr_shr]
  simp only [shr_byte]
  simp only [low_byte]
  rw [show sOff j + 0 = entryOff (2 * j + 0) 0 from e 0 0 (by decide),
    show sOff j + 256 = entryOff (2 * j + 0) 1 from e 1 0 (by decide),
    show sOff j + 512 = entryOff (2 * j + 0) 2 from e 2 0 (by decide),
    show sOff j + 768 = entryOff (2 * j + 0) 3 from e 3 0 (by decide),
    show sOff j + 1 = entryOff (2 * j + 1) 0 from e 0 1 (by decide),
    show sOff j + 257 = entryOff (2 * j + 1) 1 from e 1 1 (by decide),
    show sOff j + 513 = entryOff (2 * j + 1) 2 from e 2 1 (by decide),
    show sOff j + 769 = entryOff (2 * j + 1) 3 from e 3 1 (by decide)]
  rw [scheduleAt_write_bytes _ _ (by omega_arith), Nat.add_zero, scheduleAt_write_bytes _ _ (by omega_arith)]

/-- The S-box phase: after `j` encryptions, the pointer at S-box entry
`sDone j` and `521 - j` left. -/
structure SInv (key : List Byte) (K B : BitVec 32) (s₀ : State) (j : Nat) (u : State) : Prop where
  enc : EncInv key K B s₀ j u
  ge : 9 ≤ j
  ptr : u.mem.readW (slot B 32) 32 = K + BitVec.ofNat 32 (sOff j)
  cnt : u.mem.readW (slot B 36) 32 = BitVec.ofNat 32 (521 - j)

theorem encS_step {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {j : Nat}
    (hj : j < 521) {u : State} (I : SInv key K B s₀ j u) :
    WP isa (.seq (cipher 12 true) storeS) u fun u' =>
      SInv key K B s₀ (j + 1) u' ∧ u'.zf = some (BitVec.ofNat 32 (521 - (j + 1)) == 0) := by
  have fK := E.fitK
  have fB := E.fitB
  have J := I.enc
  have h9 := I.ge
  obtain hq := sOff_lt h9 hj
  apply WP.seq
  refine WP.mono (enc_cipher E J) fun u₁ ⟨c12, ck, cf⟩ => ?_
  obtain w₁ : u₁.wr = s₀.wr := by rw [ck.2.2, J.wr]
  obtain e1 : u₁.gpr .esp = s₀.gpr .esp := (ck.gpr (by decide)).trans J.esp
  obtain F1 : Frame [⟨K.setWidth 64, 4168⟩, ⟨B.setWidth 64, 64⟩] s₀.mem u₁.mem :=
    J.frame.trans ((cipher_wide cf).sub fun r hr => wRegions_sub hr)
  unfold storeS
  apply WP.seq
  refine WP.mono (WP.keep [.eax, .ebx, .ecx, .edx] (storeSHead_run u₁ (K := K) (q := sOff j)
    (C := BitVec.ofNat 32 (521 - j)) ((ck.gpr (by decide)).trans J.ebp) (by omega_arith)
    (region_in (E.wB w₁ (by decide))) (region_in (E.wB w₁ (by decide))) (region_in (E.wB w₁ (by decide)))
    (region_in (E.wB w₁ (by decide))) (by rw [cipher_past cf (by decide) (by decide)]; exact I.ptr)
    (by rw [cipher_past cf (by decide) (by decide)]; exact I.cnt)
    (by rw [ck.2.1, ck.2.2, J.rd, J.wr, e1]; exact E.rdA) (fun c hc => addr_ofs (by omega_arith))
    (fun c hc => E.wK w₁ (by omega_arith)) (by omega_arith) (E.sep.symm.sub_left (Offset.sub_base _ (by decide)))
    (by rw [e1]; exact E.sepKA.symm)) (by decide))
    fun u₂ ⟨⟨hm, hbx, hdx, hz⟩, hk⟩ => ?_
  rw [e1, E.arg F1, sAnd_z K _ (by omega_arith)] at hz
  -- past the other planes after an S-box's last entry
  apply WP.seq
  obtain hite : WP isa (.ite .e (.block [.alu .add .ebx (imm 768)]) (.block [])) u₂ fun u₃ =>
      u₃.gpr .ebx = K + BitVec.ofNat 32 (sOff (j + 1)) ∧ u₃.mem = u₂.mem ∧ Keep [.ebx] u₂ u₃ := by
    refine WP.ite _ (by rw [eval_e, hz]) (fun h => ?_) (fun h => ?_)
    · refine WP.mono (WP.keep [.ebx] (Q := fun t => t.gpr .ebx = u₂.gpr .ebx + BitVec.ofNat 32 768 ∧
        t.mem = u₂.mem) (by brun) (by decide)) fun t ⟨⟨t12, tm⟩, tk⟩ => ⟨?_, tm, tk⟩
      rw [t12, hbx, ofs_add, ofs_add, sOff_succ h9, ite_eq_left (of_decide_eq_true h)]
    · refine WP.block_nil ⟨?_, rfl, Keep.refl _ _⟩
      rw [hbx, ofs_add, sOff_succ h9, ite_eq_right (of_decide_eq_false h)]
  refine WP.mono hite fun u₃ ⟨g12, gm, gk⟩ => ?_
  obtain k₃ : Keep lookRegs u u₃ := ((ck.trans hk).trans gk).mono (by decide)
  obtain w₃ : u₃.wr = s₀.wr := by rw [k₃.2.2, J.wr]
  obtain F8 := sWrites_frame u₁.mem (K.setWidth 64) (q := sOff j) (by omega_arith) (u₁.mem.readW (slot B 16) 32)
    (u₁.mem.readW (slot B 20) 32)
  rw [← hm, ← gm] at F8
  refine WP.mono (WP.keep [.edx] (storeSTail_run u₃ (C := BitVec.ofNat 32 (521 - j))
    ((k₃.gpr (by decide)).trans J.ebp) (by omega_arith) (E.wB w₃ (by decide)) (E.wB w₃ (by decide))
    (by rw [gk.gpr (by decide), hdx])) (by decide))
    fun u₄ ⟨⟨tm, tz⟩, tk⟩ => ?_
  obtain ⟨M32, M36, MF⟩ := slots_facts u₃.mem B (u₃.gpr .ebx) (BitVec.ofNat 32 (521 - j) - BitVec.ofNat 32 1)
  rw [← tm] at M32 M36 MF
  obtain FF : Frame (wRegions K B) u.mem u₄.mem :=
    ((cipher_wide cf).trans (F8.mono (by simp))).trans (slots_wide MF)
  obtain h1 : u₁.mem.readW (slot B 16) 32 = (encryptWords (ksIter key j).1 (ksIter key j).2.1
      (ksIter key j).2.2).1 := congrArg Prod.fst c12
  obtain h2 : u₁.mem.readW (slot B 20) 32 = (encryptWords (ksIter key j).1 (ksIter key j).2.1
      (ksIter key j).2.2).2 := congrArg Prod.snd c12
  obtain hsched : scheduleAt u₄.mem (K.setWidth 64) = (ksIter key (j + 1)).1 := by
    rw [scheduleAt_eq_of_frame _ MF (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.sep.sub_right (Offset.sub_base _ (by decide))), gm, hm,
      sWrites_sched _ _ h9 hj, E.sched_c cf, J.sched, ksIter_step key hj, h1, h2]
  obtain rd4 : ∀ d, d + 4 ≤ 32 → u₄.mem.readW (slot B d) 32 = u₁.mem.readW (slot B d) 32 := fun d hd => by
    rw [tm, Mem.readW_writeW_sep (slot_sep B (by omega_arith) (by omega_arith) (by decide)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (by omega_arith) (by omega_arith) (by decide)) (by decide), gm, hm,
      read_past_sWrites (E.sep.symm.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith)]
  obtain k₄ : Keep lookRegs u u₄ := (k₃.trans tk).mono (by decide)
  refine ⟨⟨⟨by omega_arith, (k₄.gpr (by decide)).trans J.esp, (k₄.gpr (by decide)).trans J.ebp, hsched, ?_,
    saved_frame J.saved FF E.sep fB, J.frame.trans (FF.sub fun r hr => wRegions_sub hr), by rw [k₄.2.1, J.rd],
    by rw [k₄.2.2, J.wr]⟩, by omega_arith, by rw [M32, g12], ?_⟩, ?_⟩
  · rw [rd4 16 (by decide), rd4 20 (by decide), c12, ksIter_step key hj]
  · rw [M36]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  · rw [tz]; congr 2; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith

theorem encryptS_run {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {u : State}
    (I : EncInv key K B s₀ 9 u) : WP isa encryptS u (EncInv key K B s₀ 521) := by
  have fB := E.fitB
  obtain w32 := E.wB I.wr (o := 32) (n := 4) (by decide)
  obtain w36 := E.wB I.wr (o := 36) (n := 4) (by decide)
  obtain rA : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 12) 4 := by rw [I.rd, I.wr, I.esp]; exact E.rdA
  obtain vA : u.mem.readW (addr (u.gpr .esp) 12) 32 = K := by rw [I.esp]; exact E.arg I.frame
  unfold encryptS
  apply WP.seq
  refine WP.mono (WP.keep [.ebx, .ecx] (Q := fun t => t.mem = (u.mem.writeW (slot B 32) K).writeW (slot B 36)
      (BitVec.ofNat 32 512))
    (by brun [I.ebp, addr_slot (show B.toNat + 40 ≤ 2 ^ 32 by omega_arith), w32, w36, rA, vA]) (by
      decide))
    fun u₁ ⟨m₁, k₁⟩ => ?_
  obtain ⟨J, j32, j36⟩ := I.slots E m₁ k₁ (by decide) (by decide)
  refine WP.loop (M := isa) (Q := EncInv key K B s₀ 521)
    (fun (n : Nat) (v : State) => ∃ j, j < 521 ∧ n = 521 - j ∧ SInv key K B s₀ j v) ?_ 512 u₁
    ⟨9, by decide, rfl, ⟨J, by decide, by rw [j32, show sOff 9 = 0 by decide, BitVec.add_zero], by rw [j36]⟩⟩
  intro n v ⟨j, hj, hn, P⟩
  refine WP.mono (encS_step E hj P) fun v' ⟨P', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : j + 1 = 521
  · left
    exact ⟨by rw [e]; rfl, e ▸ P'.enc⟩
  · right
    obtain nz : BitVec.ofNat 32 (521 - (j + 1)) ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_arith, j + 1, by omega_arith, rfl, P'⟩

end VG.Proof.Blowfish.X86

end

end

/-!
# Blowfish on x86 (32-bit): key expansion

`expandKey_correct`: our caller's registers saved, the initial schedule
written, the key XORed into the P-array, the 521 encryptions, and the
registers restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- The key, the schedule and the working space of `s`. -/
abbrev keyR (s : State) : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
abbrev kSchR (s : State) : Region := ⟨(arg s 2).setWidth 64, 4168⟩
abbrev kBufR (s : State) : Region := ⟨(arg s 3).setWidth 64, 64⟩

/-- What key expansion may assume: the key and the arguments readable, the
schedule and the working space writable, apart, none wrapping around, and a
valid key length. -/
structure KeyPre (s : State) : Prop where
  rd : s.rd = [keyR s, argR s]
  wr : s.wr = [kSchR s, kBufR s]
  ks : (keyR s).Disjoint (kSchR s)
  kb : (keyR s).Disjoint (kBufR s)
  sb : (kSchR s).Disjoint (kBufR s)
  as : (argR s).Disjoint (kSchR s)
  ab : (argR s).Disjoint (kBufR s)
  rs : (retR s).Disjoint (kSchR s)
  rb : (retR s).Disjoint (kBufR s)
  fKey : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  fSch : (arg s 2).toNat + 4168 ≤ 2 ^ 32
  fBuf : (arg s 3).toNat + 64 ≤ 2 ^ 32
  fsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  valid : validKey (arg s 1).toNat

/-- What key expansion guarantees. -/
def KeyPost (s t : State) : Prop :=
  abiPreserved s t ∧
    scheduleAt t.mem ((arg s 2).setWidth 64) = expandKey (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)

/-- The argument `i` (of the first four) within the arguments' region. -/
theorem argR_contains (s : State) (hsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (argR s).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  show Region.Contains ⟨addr (s.gpr .esp) 4, 16⟩ (addr (s.gpr .esp) (4 + 4 * i)) 4
  rw [addr_of_fit (by omega_arith), addr_of_fit (by omega_arith), ← Offset.add_add]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- Saving our caller's registers in the working space at `B`, its address the fourth argument. -/
theorem save_run (s : State) {B : BitVec 32} (bfit : B.toNat + 40 ≤ 2 ^ 32)
    (hA : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4) (hv : s.mem.readW (addr (s.gpr .esp) 16) 32 = B)
    (w : ∀ d, d + 4 ≤ 16 → InRegions s.wr (slot B d) 4) :
    WP isa (.block save) s fun t =>
      t.mem = savedMem s.mem B (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi) (s.gpr .ebp) ∧ t.gpr .ebp = B := by
  unfold save savedMem
  brun [addr_slot bfit, hA, hv, w 0 (by decide), w 4 (by decide), w 8 (by decide), w 12 (by decide)]

theorem argR_sub (s : State) (hsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    Region.Sub ⟨addr (s.gpr .esp) (4 + 4 * i), 4⟩ (argR s) := by
  show Region.Sub ⟨addr (s.gpr .esp) (4 + 4 * i), 4⟩ ⟨addr (s.gpr .esp) 4, 16⟩
  rw [addr_of_fit (by omega_arith), addr_of_fit (by omega_arith)]
  exact Offset.sub _ (by omega_arith) (by omega_arith)

theorem expandKey_correct {s : State} (h : KeyPre s) : WP isa Impl.Blowfish.X86.expandKey s (KeyPost s) := by
  obtain ⟨hrd, hwr, ks, kb, sb, as, ab, rs, rb, fKey, fSch, fBuf, fsp, valid⟩ := h
  let K := arg s 2
  let B := arg s 3
  have eK : K.toNat = (arg s 2).toNat := rfl
  have eB : B.toNat = (arg s 3).toNat := rfl
  have hL := valid.1
  have hL' := valid.2
  obtain bfit : B.toNat + 40 ≤ 2 ^ 32 := by omega_arith
  obtain bR : kBufR s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain sR : kSchR s ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  obtain rA : ∀ i, i < 4 → InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := fun i hi => by
    rw [hrd]; exact ⟨argR s, List.mem_cons_of_mem _ List.mem_cons_self, argR_contains s fsp hi⟩
  obtain argF : ∀ {m : Mem}, Frame [kSchR s, kBufR s] s.mem m → ∀ i, i < 4 →
      m.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := fun hf i hi =>
    hf.readW (r := argR s) (argR_contains s fsp hi) (fun r hr => (mem_two hr).elim (· ▸ as) (· ▸ ab))
      (by decide)
  let key := bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
  unfold Impl.Blowfish.X86.expandKey initSchedule
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ebp] (save_run s bfit (rA 3 (by decide)) rfl (fun d hd =>
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)) (by decide))
    fun u₁ ⟨⟨m₁, b₁⟩, k₁⟩ => ?_
  obtain F₁ : Frame [kSchR s, kBufR s] s.mem u₁.mem := by
    rw [m₁]
    refine (savedMem_frame s.mem B _ _ _ _).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨kBufR s, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by decide)⟩
  obtain r12 : InRegions (u₁.rd ++ u₁.wr) (addr (u₁.gpr .esp) 12) 4 := by
    rw [keep_reads k₁, k₁.gpr (by decide)]; exact rA 2 (by decide)
  obtain v12 : u₁.mem.readW (addr (u₁.gpr .esp) 12) 32 = K := by
    rw [k₁.gpr (by decide)]; exact argF F₁ 2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.ebx] (Q := fun t => t.gpr .ebx = K + BitVec.ofNat 32 0 ∧ t.mem = u₁.mem)
    (by brun [r12, v12]) (by decide)) fun u₂ ⟨⟨b₂, m₂⟩, k₂⟩ => ?_
  refine WP.mono (initSchedule_steps u₂ fSch b₂
    (by rw [k₂.2.2, k₁.2.2]; exact ⟨_, sR, Region.contains_self _ _⟩) 1042 (by decide)) fun u₃ I₃ => ?_
  obtain k₃ : Keep [.eax, .ebp, .ebx, .ecx] s u₃ := (k₁.trans (k₂.trans I₃.keep)).mono (by decide)
  obtain F₃ : Frame [kSchR s, kBufR s] s.mem u₃.mem := by
    refine F₁.trans ?_
    rw [← m₂]; exact I₃.frame.mono (by simp)
  -- the key into the P-array
  obtain KE : KeyEnv (arg s 0) (arg s 1).toNat u₃ := by
    refine ⟨fun i hi => ?_, ?_, ?_, by omega_arith, hL', fKey, ?_, by rw [k₃.gpr (by decide)]; exact fsp⟩
    · rw [keep_reads k₃, k₃.gpr (by decide)]; exact rA i (by omega_arith)
    · rw [k₃.gpr (by decide)]; exact argF F₃ 0 (by decide)
    · rw [k₃.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact argF F₃ 1 (by decide)
    · rw [keep_reads k₃, hrd]; exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
  obtain subP : Region.Sub ⟨K.setWidth 64 + BitVec.ofNat 64 4096, 72⟩ (kSchR s) := Offset.sub_base _ (by decide)
  apply WP.seq
  refine WP.mono (keyP_run KE (by rw [keep_reads k₃, k₃.gpr (by decide)]; exact rA 2 (by decide))
    (by rw [k₃.gpr (by decide)]; exact argF F₃ 2 (by decide)) fSch
    (by rw [k₃.2.2]; exact ⟨_, sR, Offset.contains_base _ (by decide) (by omega_arith)⟩) (ks.sub_right subP)
    (by rw [k₃.gpr (by decide)]
        exact (as.sub_left (Region.sub_prefix (by decide))).sub_right subP)) fun u₄ I₄ => ?_
  obtain k₄ : Keep [.eax, .ebp, .ebx, .ecx, .edx, .esi, .edi] s u₄ := (k₃.trans I₄.keep).mono (by decide)
  obtain F₃₄ : Frame [kSchR s, kBufR s] u₃.mem u₄.mem := I₄.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, subP⟩
  -- the schedule so far
  obtain hkey : bytesAt u₃.mem ((arg s 0).setWidth 64) (arg s 1).toNat = key :=
    bytesAt_frame F₃ fun c hc r hr => by
      rcases mem_two hr with rfl | rfl
      · exact ks _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
      · exact kb _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  obtain hP : ∀ i < 18, u₄.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * i)) 32 =
      initial.getD i 0 ^^^ Spec.Blowfish.keyWord key i := fun i hi => by
    rw [I₄.done i hi, hkey, table_P I₃.bytes hi]
  obtain hS : ∀ o < 4096, u₄.mem (K.setWidth 64 + BitVec.ofNat 64 o) = initByte o := fun o ho => by
    rw [I₄.frame _ fun r hr => ?_, I₃.bytes o (by omega_arith)]
    simp only [List.mem_singleton] at hr; subst hr
    exact (Offset.disjoint _ (d := o) (n := 1) (e := 4096) (k := 72) (by omega_arith) (by omega_arith) (by decide)) _
      (Region.contains_self _ _)
  obtain hK : scheduleAt u₄.mem (K.setWidth 64) = keyed key := keyed_of_mem hS hP
  -- the halves zeroed
  obtain k₁₄ : Keep [.ebx, .ecx, .eax, .edx, .esi, .edi] u₁ u₄ := ((k₂.trans I₃.keep).trans I₄.keep).mono (by decide)
  obtain b₄ : u₄.gpr .ebp = B := (k₁₄.gpr (by decide)).trans b₁
  obtain w16 : InRegions u₄.wr (slot B 16) 4 := by
    rw [k₄.2.2]; exact ⟨_, bR, Offset.contains_base _ (by decide) (by omega_arith)⟩
  obtain w20 : InRegions u₄.wr (slot B 20) 4 := by
    rw [k₄.2.2]; exact ⟨_, bR, Offset.contains_base _ (by decide) (by omega_arith)⟩
  apply WP.seq
  refine WP.mono (WP.keep [.eax] (Q := fun t => t.mem = (u₄.mem.writeW (slot B 16) (0#32)).writeW (slot B 20)
      (0#32)) (by brun [b₄, addr_slot bfit, w16, w20]) (by decide)) fun u₅ ⟨m₅, k₅⟩ => ?_
  obtain F₄₅ : Frame [⟨slot B 16, 8⟩] u₄.mem u₅.mem := by
    rw [m₅]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _
      (Offset.contains (e := 16) (k := 8) (d := 16) (n := 4) _ (by decide) (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains (e := 16) (k := 8) (d := 20) (n := 4) _ (by decide) (by decide)
        (by decide))
  obtain F₅ : Frame [kSchR s, kBufR s] s.mem u₅.mem := (F₃.trans F₃₄).trans (F₄₅.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩)
  -- the encryptions
  obtain EE : EncEnv K B s := by
    refine ⟨fSch, fBuf, ⟨_, sR, Region.contains_self _ _⟩, ⟨_, bR, Region.contains_self _ _⟩, sb,
      rA 2 (by decide), rfl, ?_, ?_⟩
    · exact as.symm.sub_right (argR_sub s fsp (i := 2) (by decide))
    · exact ab.symm.sub_right (argR_sub s fsp (i := 2) (by decide))
  obtain k₅' : Keep [.eax, .ebp, .ebx, .ecx, .edx, .esi, .edi] s u₅ := (k₄.trans k₅).mono (by decide)
  obtain I₅ : EncInv key K B s 0 u₅ := by
    refine ⟨by decide, k₅'.gpr (by decide), (k₅.gpr (by decide)).trans b₄, ?_, ?_, ?_, F₅, k₅'.2.1, k₅'.2.2⟩
    · rw [scheduleAt_eq_of_frame _ F₄₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sb.sub_right (Offset.sub_base _ (by decide))), hK, ksIter_zero]
    · rw [m₅, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32, Mem.readW_writeW_self32, ksIter_zero]; rfl
    · have S₁ : Saved u₁.mem B s := by rw [m₁]; exact saved_savedMem s.mem B s
      refine S₁.frame (rs := [kSchR s, ⟨slot B 16, 8⟩]) ?_ fun r hr => ?_
      · rw [← m₂]
        refine ((I₃.frame.mono (by simp)).trans (I₄.frame.sub fun r hr => ?_)).trans (F₄₅.mono (by simp))
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, subP⟩
      · rcases mem_two hr with rfl | rfl
        · exact sb.symm.sub_left (Region.sub_prefix (by decide))
        · exact Offset.base_disjoint _ (by decide) (by omega_arith)
  apply WP.seq
  refine WP.mono (encryptP_run EE I₅) fun u₆ I₆ => ?_
  apply WP.seq
  refine WP.mono (encryptS_run EE I₆) fun u₇ I₇ => ?_
  obtain hr : ∀ d, d + 4 ≤ 16 → InRegions (u₇.rd ++ u₇.wr) (slot B d) 4 := fun d hd => by
    rw [I₇.rd, I₇.wr]; exact region_in (EE.wB rfl (by omega_arith))
  refine WP.mono (WP.keep [.ebx, .esi, .edi, .ebp] (restore_run u₇ s I₇.ebp bfit hr I₇.saved) (by
      decide))
    fun t ⟨⟨tb, ts, td, tp, tm⟩, tk⟩ => ⟨⟨fun r hr => ?_, ?_⟩, by rw [tm, I₇.sched, expandKey_eq]⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [tb, ts, td, tp, (tk.gpr (by decide)).trans I₇.esp]
  · rw [tm]
    refine I₇.frame.readW (r := retR s) (contains_pre _ (by decide)) (fun r hr => ?_) (by decide)
    rcases mem_two hr with rfl | rfl
    exacts [rs, rb.sub_right (Region.sub_prefix (by decide))]

end VG.Proof.Blowfish.X86
