module
public import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run

import VerifiedGarbage.Proof.Blowfish.X86.Ecb
import VerifiedGarbage.Proof.Blowfish.KeyTable
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Blowfish.Table

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
