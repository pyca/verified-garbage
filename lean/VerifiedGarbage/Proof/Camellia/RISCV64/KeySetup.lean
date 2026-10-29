module

public import VerifiedGarbage.Proof.Camellia.RISCV64.KaKb
public import VerifiedGarbage.Proof.Camellia.RISCV64.KeyChecks2
public import VerifiedGarbage.Proof.Camellia.RISCV64.Prologue
public import VerifiedGarbage.Proof.Camellia.RISCV64.KeyStore
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Camellia.RISCV64.KeyPair
import VerifiedGarbage.Proof.Camellia.RISCV64.Keys
import VerifiedGarbage.Proof.Camellia.RISCV64.Group
import VerifiedGarbage.Proof.Camellia.RISCV64.Crypt8
import VerifiedGarbage.Proof.Camellia.KeySched
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The Camellia key schedule on RISC-V: its parts

As on PPC64LE (`Proof/Camellia/PPC64LE/KeySetup.lean`): the prologue saves
the callee-saved registers, sets the masks and stores the planes of
`Sigma1 … Sigma6` as a table of subkeys (`ekPrologue_ok`; each plane built
by `movImm64` and stored: `sigmaStores_ok`); `loadKey_wp` copies `KL` and
`KR` into their slots a byte at a time, and `loadValues_ok` reads the four
values big-endian into registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 t2 u7 kp movR ldS stS xorR notR)
open VG.Proof.Camellia (HalfRel pair hiW loW pos)

/-! ## Single instructions -/

/-- `sd r, 8 k(sb)`, as slots. -/
theorem st_ok {s : State} {k : Nat} (r : Reg) (hal : (s.gpr sb).toNat % 8 = 0)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < keySlot) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ slotW s' k = s.gpr r ∧
      (∀ j < slots, j ≠ k → slotW s' j = slotW s j) ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hk' : k < slots := by rw [keySlot_eq] at hk; rw [slots_eq]; omega_arith
  obtain ⟨s', e, m, g, rd, wr⟩ := stS_slot (k := k) r rfl hal hscr hk
  refine ⟨s', e, ?_, fun j hj hjk => ?_, g, by rw [m]; exact frame_slot _ hk', rd, wr⟩
  · rw [slotW_store m g hk' hk', ite_eq_left rfl]
  · rw [slotW_store m g hj hk', ite_eq_right hjk]

/-! ## The table of `Sigma1 … Sigma6` -/

/-- Plane `j` of the constant `x`, built in `t0` and stored to the entry at `kp`. -/
def sigmaStore (x : BitVec 64) (j : Nat) : List Instr :=
  Impl.Words64.RISCV64.movImm64 t0 t1 (keyPlane x j) ++ [.store .d t0 kp (8 * j)]

theorem sigmaOne_eq (x : BitVec 64) :
    sigmaOne x = (List.range 8).flatMap (sigmaStore x) ++ ([.addi kp kp 64] : List Instr) := rfl

/-- The planes stored so far. -/
structure SigInv (x : BitVec 64) (s : State) (n : Nat) (s' : State) : Prop where
  planes : ∀ j < n, s'.mem.readW (wordAddr (s.gpr kp) j) 64 = keyPlane x j
  frame : Frame [⟨s.gpr kp, 64⟩] s.mem s'.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The stores of `sigmaOne x`: the planes of `x` to the entry at `kp`. -/
theorem sigmaStores_ok (x : BitVec 64) (s : State) (hal : (s.gpr kp).toNat % 8 = 0)
    (hw : ∀ j < 8, InRegions s.wr (s.gpr kp + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa ((List.range 8).flatMap (sigmaStore x)) s = some s' ∧ SigInv x s 8 s' := by
  refine WP.runBlock_of (wp_range_flatMap (M := isa) (SigInv x s) (fun k s₁ hk h => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega), Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl⟩)
  rw [sigmaStore, WP.block_append_iff (M := isa)]
  refine WP.mono (Words64.movImm64_ok (s := s₁) (d := t0) (tmp := t1) (by decide) (keyPlane x k))
    fun s₂ ⟨v₂, g₂, m₂, rd₂, wr₂, _⟩ => ?_
  have hkp : s₂.gpr kp = s.gpr kp := by rw [g₂ _ (by decide) (by decide), h.regs _ (by decide) (by decide)]
  refine Steps.wp_sd (a := wordAddr (s.gpr kp) k) (by omega) (by rw [hkp])
    (Spill.al8 hal (by omega)) (by rw [wr₂, h.wr]; exact hw k hk) fun s₃ u₃ => WP.block_nil ?_
  have hm₃ : s₃.mem = s₁.mem.writeW (wordAddr (s.gpr kp) k) (keyPlane x k) := by rw [u₃.mem, m₂, v₂]
  refine ⟨fun j hj => ?_, ?_, fun r h0 h1 => by rw [u₃.gpr, g₂ r h0 h1, h.regs r h0 h1],
    by rw [u₃.rd, rd₂, h.rd], by rw [u₃.wr, wr₂, h.wr]⟩
  · rw [hm₃]
    by_cases hjk : j = k
    · subst hjk; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hjk) (by decide)]
      exact h.planes j (by omega)
  · rw [hm₃]
    exact h.frame.trans (frame_writeW _ (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega)))

/-- `sigmaOne x`: the planes of `x` to the entry at `kp`, and `kp` to the next. -/
theorem sigmaOne_ok (x : BitVec 64) (s : State) (hal : (s.gpr kp).toNat % 8 = 0)
    (hw : ∀ j < 8, InRegions s.wr (s.gpr kp + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (sigmaOne x) s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * j)) 64 = keyPlane x j) ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 ∧ Frame [⟨s.gpr kp, 64⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, h₁⟩ := sigmaStores_ok x s hal hw
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 64 (by decide)
  refine ⟨s₂, by rw [sigmaOne_eq, runBlock_append', e₁, Option.bind_some, e₂], fun j hj => by
      rw [m₂]; exact h₁.planes j hj,
    by rw [a₂, h₁.regs _ (by decide) (by decide)], by rw [m₂]; exact h₁.frame,
    fun r h0 h1 h2 => by rw [o₂ r h2, h₁.regs r h0 h1], by rw [rd₂, h₁.rd], by rw [wr₂, h₁.wr]⟩

theorem sigmaList_ok {b : Addr} (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) (hal : b.toNat % 8 = 0) :
    ∀ (xs : List (BitVec 64)) (e : Nat) (s : State), (⟨b, 8 * slots⟩ : Region) ∈ s.wr →
      s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e) → e + xs.length ≤ 34 →
      ∃ s', runBlock isa (xs.flatMap sigmaOne) s = some s' ∧
        (∀ i < xs.length, ∀ j < 8, entryW s'.mem b (e + i) j = keyPlane (xs.getD i 0) j) ∧
        Frame [⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64 * xs.length⟩] s.mem s'.mem ∧
        s'.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e + xs.length)) ∧
        (∀ r, r ≠ t0 → r ≠ t1 → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], e, s, _, hr, _ => ⟨s, rfl, fun i hi => absurd hi (by simp), Frame.refl _ _, by simpa using hr,
      fun _ _ _ _ => rfl, rfl, rfl⟩
  | x :: xs, e, s, hscr, hr, hl => by
    rw [slots_eq] at hfit
    have hk := keySlot_eq
    simp only [List.length_cons] at hl
    obtain ⟨s₁, e₁, v₁, r₁, f₁, g₁, rd₁, wr₁⟩ := sigmaOne_ok x s (by rw [hr]; exact Spill.al8 hal (by omega_arith))
      (fun j hj => ⟨_, hscr, by
        rw [hr, Offset.add_add]
        exact VG.Offset.contains_base _ (by rw [slots_eq]; omega_arith) (by omega_arith)⟩)
    obtain ⟨s', e', v', f', r', g', rd', wr'⟩ := sigmaList_ok hfit hal xs (e + 1) s₁
      (by rw [wr₁]; exact hscr)
      (by rw [r₁, hr, Offset.add_add, show 8 * keySlot + 64 * e + 64 = 8 * keySlot + 64 * (e + 1) by omega_arith])
      (by omega_arith)
    refine ⟨s', by rw [List.flatMap_cons, runBlock_append', e₁, Option.bind_some, e'], fun i hi j hj => ?_,
      ?_, by rw [r', List.length_cons, show e + 1 + xs.length = e + (xs.length + 1) by omega_arith],
      fun r h0 h1 h2 => by rw [g' r h0 h1 h2, g₁ r h0 h1 h2], by rw [rd', rd₁], by rw [wr', wr₁]⟩
    · rcases i with _ | i
      · rw [entryW, Nat.add_zero, ← Offset.add_add, ← hr]
        refine (f'.readW (Region.contains_self _ _) (fun r hr' => ?_) (by decide)).trans (v₁ j hj)
        simp only [List.mem_singleton] at hr'; subst hr'
        rw [hr, Offset.add_add]
        exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
      · rw [show e + (i + 1) = e + 1 + i by omega_arith]
        exact v' i (by simpa using hi) j hj
    · refine Frame.trans (f₁.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩)
        (f'.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
        (simp only [List.mem_singleton] at hr'; subst hr')
      · rw [hr]; exact Region.sub_prefix (by simp only [List.length_cons]; omega_arith)
      · exact VG.Offset.sub b (by omega_arith) (by simp only [List.length_cons]; omega_arith)

/-- The table's entries `0 … 5` hold `Sigma1 … Sigma6`, as `KeyCtx` reads them. -/
theorem sigmas_rel {m : Mem} {b : Addr}
    (h : ∀ i < 6, ∀ j < 8, entryW m b i j = keyPlane (sigmas.getD i 0) j) :
    ∀ i < 6, HalfRel (entryW m b i) fun _ => sigE i := fun i hi bb hb c hc j hj => by
  rw [h i hi j hj]; exact sigma_planes _ hb hc hj

/-! ## Loading the key -/

/-- Eight bytes copied: the word they make, in the order ECB loads it. -/
theorem wordOf_copy {m m' : Mem} {a b : Addr} (h : ∀ i < 8, m' (b + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) :
    WordOf (m'.readW b 64) (Spec.Camellia.wordAt m a) := fun i hi j hj => by
  rw [Camellia.readW64_bit m' b hi hj, h i hi, Camellia.byteOf_wordAt m a hi]

/-- A step that writes only `t0` and `t1`. -/
structure Pure (s s' : State) : Prop where
  mem : s'.mem = s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- What a part of `loadKey` keeps: the slots but those of `KL` and `KR`,
the registers but `t0` and `t1`. -/
structure LkKeep (s s' : State) : Prop where
  keep : ∀ k < slots, (k < klSlot ∨ krSlot + 2 ≤ k) → slotW s' k = slotW s k
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem LkKeep.trans {s₁ s₂ s₃ : State} (h₁ : LkKeep s₁ s₂) (h₂ : LkKeep s₂ s₃) : LkKeep s₁ s₃ where
  keep k hk h := (h₂.keep k hk h).trans (h₁.keep k hk h)
  regs r h0 h1 := (h₂.regs r h0 h1).trans (h₁.regs r h0 h1)
  frame := h₁.frame.trans (by have := h₂.frame; rw [h₁.regs _ (by decide) (by decide)] at this; exact this)
  rd := h₂.rd.trans h₁.rd
  wr := h₂.wr.trans h₁.wr

theorem LkKeep.of_pure {s s' : State} (h : Pure s s') : LkKeep s s' :=
  ⟨fun k _ _ => slotW_eq_of h.mem (h.regs _ (by decide) (by decide)) k, h.regs,
    by rw [h.mem]; exact Frame.refl _ _, h.rd, h.wr⟩

/-- `copyBytes t0 a0 sb soff (8 k) nb`, `nb = 8 n`: `n` words of the key to
slots `k … k + n - 1`. -/
theorem copyKey_ok {s : State} {len soff k n nb : Nat} (hnb : nb = 8 * n)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hkey : (⟨s.gpr .a0, len⟩ : Region) ∈ s.rd)
    (hks : Region.Disjoint ⟨s.gpr .a0, len⟩ ⟨s.gpr sb, 8 * slots⟩) (hlen : len ≤ 32)
    (hsl : soff + 8 * n ≤ len) (hk2 : k + n ≤ keySlot) :
    ∃ s', runBlock isa (copyBytes t0 .a0 sb soff (8 * k) nb) s = some s' ∧
      (∀ w < n, WordOf (slotW s' (k + w))
        (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 (soff + 8 * w)))) ∧
      (∀ j < slots, (j < k ∨ k + n ≤ j) → slotW s' j = slotW s j) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  subst hnb
  have hK := keySlot_eq
  have hS := slots_eq
  obtain ⟨s', e', c'⟩ := WP.runBlock_of (Bytes.copyBytes_ok (s := s) (tmp := t0) (src := .a0) (dst := sb)
    (soff := soff) (doff := 8 * k) (n := 8 * n) (by decide) (by decide) (by omega_arith) (by omega_arith)
    (fun i hi => ⟨_, List.mem_append_left _ hkey, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi => ⟨_, hscr, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi hc => hks _ (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
      ((VG.Offset.sub_base _ (by omega_arith)) _ hc)))
  have hb : s'.gpr sb = s.gpr sb := c'.gpr _ (by decide)
  refine ⟨s', e', fun w hw => ?_, fun j hj hjk => ?_, c'.gpr, ?_, c'.rd, c'.wr⟩
  · simp only [slotW, hb, wordAddr]
    refine wordOf_copy fun i hi => ?_
    have := c'.copied (8 * w + i) (by omega_arith)
    rw [Offset.add_add, Offset.add_add, show 8 * (k + w) + i = 8 * k + (8 * w + i) by omega_arith,
      show soff + 8 * w + i = soff + (8 * w + i) by omega_arith]
    exact this
  · simp only [slotW, hb]
    refine c'.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr]
    exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact c'.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base _ (by omega_arith)⟩

/-- `KL` and `KR`, from the key's bytes. -/
abbrev klOf (m : Mem) (a : Addr) (len : Nat) : BitVec 128 := (Spec.Camellia.klkr (Spec.Camellia.bytesAt m a len)).1
abbrev krOf (m : Mem) (a : Addr) (len : Nat) : BitVec 128 := (Spec.Camellia.klkr (Spec.Camellia.bytesAt m a len)).2

theorem ofInt_neg_one : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by decide

/-- What `loadKey` needs: the scratch buffer and the key, apart. -/
structure LkPre (s : State) (len : Nat) : Prop where
  al : (s.gpr sb).toNat % 8 = 0
  scr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr
  key : (⟨s.gpr .a0, len⟩ : Region) ∈ s.rd
  sep : Region.Disjoint ⟨s.gpr .a0, len⟩ ⟨s.gpr sb, 8 * slots⟩
  alen : s.gpr .a3 = BitVec.ofNat 64 len
  hl : len = 16 ∨ len = 24 ∨ len = 32

theorem LkPre.of_keep {s t : State} {len : Nat} (h : LkPre s len) (hk : LkKeep s t)
    (ha3 : t.gpr .a3 = s.gpr .a3) : LkPre t len where
  al := by rw [hk.regs _ (by decide) (by decide)]; exact h.al
  scr := by rw [hk.regs _ (by decide) (by decide), hk.wr]; exact h.scr
  key := by rw [hk.regs _ (by decide) (by decide), hk.rd]; exact h.key
  sep := by rw [hk.regs _ (by decide) (by decide), hk.regs _ (by decide) (by decide)]; exact h.sep
  alen := by rw [ha3]; exact h.alen
  hl := h.hl

/-- The key's words are those on entry, as long as only the scratch buffer changes. -/
theorem LkPre.word {s t : State} {len : Nat} (h : LkPre s len) (hk : LkKeep s t) {off : Nat}
    (hoff : off + 8 ≤ len) :
    Spec.Camellia.wordAt t.mem (t.gpr .a0 + BitVec.ofNat 64 off) =
      Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 off) := by
  rw [hk.regs _ (by decide) (by decide)]
  refine wordAt_frame hk.frame fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact h.sep.sub_left (VG.Offset.sub_base _ (by omega_arith))

/-- What each of `loadKey`'s branches leaves, from `u`: `KR`'s halves. -/
structure KrDone (s u u' : State) (len : Nat) : Prop where
  kr : WordsAt u' krSlot (hiW (krOf s.mem (s.gpr .a0) len), loW (krOf s.mem (s.gpr .a0) len))
  keep : LkKeep u u'
  low : ∀ k < slots, k < krSlot → slotW u' k = slotW u k

/-- A key of 16 bytes: `KR = 0`. -/
theorem kr16_ok {s u : State} {len : Nat} (hp : LkPre u len) (h16 : len = 16) :
    ∃ u', runBlock isa [.li t0 0, stS krSlot t0, stS (krSlot + 1) t0] u = some u' ∧ KrDone s u u' len := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨-, -, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) (Or.inl h16)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := liN_ok u t0 0 (by decide)
  have lk₃ : LkKeep u s₃ := LkKeep.of_pure ⟨m₃, fun r h0 _ => o₃ r h0, rd₃, wr₃⟩
  have hp₃ := hp.of_keep lk₃ (o₃ _ (by decide))
  obtain ⟨s₄, e₄, v₄, k₄, g₄, f₄, rd₄, wr₄⟩ := st_ok (k := krSlot) t0 hp₃.al hp₃.scr (by omega_arith)
  obtain ⟨s₅, e₅, v₅, k₅, g₅, f₅, rd₅, wr₅⟩ := st_ok (k := krSlot + 1) t0
    (by rw [g₄]; exact hp₃.al) (by rw [g₄, wr₄]; exact hp₃.scr) (by omega_arith)
  refine ⟨s₅, by
    rw [show ([.li t0 0, stS krSlot t0, stS (krSlot + 1) t0] : List Instr) =
        [.li t0 0] ++ ([stS krSlot t0] ++ [stS (krSlot + 1) t0]) from rfl,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅],
    ⟨?_, ?_⟩, ?_, fun k hk h => ?_⟩
  · rw [k₅ _ (by omega_arith) (by omega_arith), v₄, a₃, hK2, ite_eq_left h16]; exact WordOf.zero
  · rw [v₅, g₄, a₃, hK3, ite_eq_left h16]; exact WordOf.zero
  · refine lk₃.trans ⟨fun k hk h => by rw [k₅ k hk (by omega_arith), k₄ k hk (by omega_arith)],
      fun r _ _ => by rw [g₅, g₄], ?_, by rw [rd₅, rd₄], by rw [wr₅, wr₄]⟩
    exact f₄.trans (by rw [g₄] at f₅; exact f₅)
  · rw [k₅ k hk (by omega_arith), k₄ k hk (by omega_arith)]
    exact slotW_eq_of m₃ (o₃ _ (by decide)) k

/-- A key of 24 bytes: `KR`'s low half is the complement of its high half. -/
theorem kr24_ok {s u : State} {len : Nat} (hs : LkPre s len) (hp : LkPre u len)
    (h24 : len = 24) (hw : WordOf (slotW u krSlot) (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 16))) :
    ∃ u', runBlock isa [ldS t0 krSlot, notR t0, stS (krSlot + 1) t0] u = some u' ∧ KrDone s u u' len := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨-, -, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) hs.hl
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅⟩ := ldS_ok (k := krSlot) t0 rfl hp.al hp.scr (by omega_arith)
  let s₆ := s₅.write t0 (s₅.gpr t0 ^^^ BitVec.ofInt 64 (-1))
  have e₆ : runBlock isa [notR t0] s₅ = some s₆ := by
    simp only [notR, runBlock_cons, exec_logicImm (show imm12 (-1 : Int) by decide), runStep_some,
      runBlock_nil]
    rfl
  have a₆ : s₆.gpr t0 = ~~~ slotW u krSlot := by
    rw [RegUpd.gpr_write_self, a₅, ofInt_neg_one, BitVec.xor_allOnes]
  have o₆ : ∀ r, r ≠ t0 → s₆.gpr r = u.gpr r := fun r hr => by
    rw [RegUpd.gpr_write_of_ne _ _ hr, o₅ r hr]
  have lk₆ : LkKeep u s₆ := LkKeep.of_pure ⟨m₅, fun r h0 _ => o₆ r h0, rd₅, wr₅⟩
  have hp₆ := hp.of_keep lk₆ (o₆ _ (by decide))
  obtain ⟨s₇, e₇, v₇, k₇, g₇, f₇, rd₇, wr₇⟩ := st_ok (k := krSlot + 1) t0 hp₆.al hp₆.scr (by omega_arith)
  have hs₆ : ∀ k, slotW s₆ k = slotW u k := slotW_eq_of m₅ (o₆ _ (by decide))
  refine ⟨s₇, by
    rw [show ([ldS t0 krSlot, notR t0, stS (krSlot + 1) t0] : List Instr) =
        [ldS t0 krSlot] ++ ([notR t0] ++ [stS (krSlot + 1) t0]) from rfl,
      runBlock_append', e₅, Option.bind_some, runBlock_append', e₆, Option.bind_some, e₇],
    ⟨?_, ?_⟩, lk₆.trans ⟨fun k hk h => k₇ k hk (by omega_arith), fun r _ _ => by rw [g₇], f₇, rd₇, wr₇⟩,
    fun k hk h => ?_⟩
  · rw [k₇ _ (by omega_arith) (by omega_arith), hs₆, hK2, ite_eq_right (by omega_arith)]; exact hw
  · rw [v₇, a₆, hK3, ite_eq_right (by omega_arith), ite_eq_left h24]; exact hw.not
  · rw [k₇ k hk (by omega_arith), hs₆]

/-- A key of 32 bytes: `KR`'s low half is the key's fourth word. -/
theorem kr32_ok {s u : State} {len : Nat} (hs : LkPre s len) (hk : LkKeep s u) (hp : LkPre u len)
    (h16 : len ≠ 16) (h24 : len ≠ 24)
    (hw : WordOf (slotW u krSlot) (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 16))) :
    ∃ u', runBlock isa (copyBytes t0 .a0 sb 24 (8 * (krSlot + 1)) 8) u = some u' ∧ KrDone s u u' len := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨-, -, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) hs.hl
  have h32 : len = 32 := by rcases hs.hl with h | h | h <;> omega_arith
  obtain ⟨s₅, e₅, w₅, k₅, g₅, f₅, rd₅, wr₅⟩ := copyKey_ok (s := u) (soff := 24) (k := krSlot + 1) (n := 1)
    (nb := 8) rfl hp.scr hp.key hp.sep (by omega_arith) (by omega_arith) (by omega_arith)
  have lk₅ : LkKeep u s₅ := ⟨fun k hk h => k₅ k hk (by omega_arith), fun r h0 _ => g₅ r h0, f₅, rd₅, wr₅⟩
  refine ⟨s₅, e₅, ⟨?_, ?_⟩, lk₅, fun k hk h => k₅ k hk (by omega_arith)⟩
  · rw [k₅ _ (by omega_arith) (by omega_arith), hK2, ite_eq_right h16]; exact hw
  · have := w₅ 0 (by decide)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero, hs.word hk (by omega_arith)] at this
    rw [hK3, ite_eq_right h16, ite_eq_right h24]; exact this

/-- The first block of `loadKey`: `KL`, and `t1 := len - 16`. -/
theorem klBlock_ok {s : State} {len : Nat} (hs : LkPre s len) :
    ∃ s', runBlock isa (copyBytes t0 .a0 sb 0 (8 * klSlot) 16 ++ ([.addi t1 .a3 (-16)] : List Instr)) s =
        some s' ∧ LkKeep s s' ∧ s'.gpr .a3 = s.gpr .a3 ∧
      WordsAt s' klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)) ∧
      (s'.gpr t1 == 0) = decide (len = 16) := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨hK0, hK1, -, -⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) hs.hl
  have hl32 : len ≤ 32 := by rcases hs.hl with h | h | h <;> omega_arith
  have hz : s.gpr .a0 + BitVec.ofNat 64 (0 + 8 * 0) = s.gpr .a0 := by simp
  obtain ⟨s₁, e₁, w₁, k₁, g₁, f₁, rd₁, wr₁⟩ := copyKey_ok (soff := 0) (k := klSlot) (n := 2) (nb := 16) rfl
    hs.scr hs.key hs.sep hl32 (by rcases hs.hl with h | h | h <;> omega_arith) (by omega_arith)
  obtain ⟨s₂, e₂, z₂, o₂, m₂, rd₂, wr₂⟩ := subI_ok s₁ t1 .a3 16 (by decide)
  have hs₂ : ∀ k, slotW s₂ k = slotW s₁ k := slotW_eq_of m₂ (o₂ _ (by decide))
  refine ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some]; exact e₂,
    ⟨fun k hk h => by rw [hs₂, k₁ k hk (by omega_arith)], fun r h0 h1 => by rw [o₂ r h1, g₁ r h0],
      by rw [m₂]; exact f₁, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩,
    by rw [o₂ _ (by decide), g₁ _ (by decide)], ⟨?_, ?_⟩, ?_⟩
  · rw [hs₂, hK0, ← hz]; exact w₁ 0 (by decide)
  · rw [hs₂, hK1]; exact w₁ 1 (by decide)
  · rw [z₂, g₁ _ (by decide), hs.alen, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]

/-- The block of `loadKey` for keys of 24 or 32 bytes: `KR`'s high half, and `t1 := len - 24`. -/
theorem krBlock_ok {s u : State} {len : Nat} (hs : LkPre s len) (hk : LkKeep s u) (hp : LkPre u len)
    (h16 : len ≠ 16) :
    ∃ u', runBlock isa (copyBytes t0 .a0 sb 16 (8 * krSlot) 8 ++ ([.addi t1 .a3 (-24)] : List Instr)) u =
        some u' ∧ LkKeep u u' ∧ u'.gpr .a3 = u.gpr .a3 ∧ (∀ k < slots, k < krSlot → slotW u' k = slotW u k) ∧
      WordOf (slotW u' krSlot) (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 16)) ∧
      (u'.gpr t1 == 0) = decide (len = 24) := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  have hl32 : len ≤ 32 := by rcases hs.hl with h | h | h <;> omega_arith
  have hl24 : 24 ≤ len := by rcases hs.hl with h | h | h <;> omega_arith
  obtain ⟨s₃, e₃, w₃, k₃, g₃, f₃, rd₃, wr₃⟩ := copyKey_ok (s := u) (soff := 16) (k := krSlot) (n := 1) (nb := 8)
    rfl hp.scr hp.key hp.sep hl32 (by omega_arith) (by omega_arith)
  obtain ⟨s₄, e₄, z₄, o₄, m₄, rd₄, wr₄⟩ := subI_ok s₃ t1 .a3 24 (by decide)
  have hs₄ : ∀ k, slotW s₄ k = slotW s₃ k := slotW_eq_of m₄ (o₄ _ (by decide))
  refine ⟨s₄, by rw [runBlock_append', e₃, Option.bind_some]; exact e₄,
    ⟨fun k hk h => by rw [hs₄, k₃ k hk (by omega_arith)], fun r h0 h1 => by rw [o₄ r h1, g₃ r h0],
      by rw [m₄]; exact f₃, by rw [rd₄, rd₃], by rw [wr₄, wr₃]⟩,
    by rw [o₄ _ (by decide), g₃ _ (by decide)], fun k hk h => by rw [hs₄, k₃ k hk (Or.inl h)], ?_, ?_⟩
  · have := w₃ 0 (by decide)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero, hs.word hk (by omega_arith)] at this
    rw [hs₄]; exact this
  · rw [z₄, g₃ _ (by decide), hp.alen, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]

/-- `loadKey`'s postcondition, from `KL`'s block and `KR`'s branch. -/
theorem lkPost_of {s s₂ s' : State} {len : Nat}
    (hkl : WordsAt s₂ klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)))
    (lk₂ : LkKeep s s₂) (h : KrDone s s₂ s' len) :
    WordsAt s' klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)) ∧
      WordsAt s' krSlot (hiW (krOf s.mem (s.gpr .a0) len), loW (krOf s.mem (s.gpr .a0) len)) ∧
      LkKeep s s' := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  exact ⟨hkl.congr (h.low _ (by omega_arith) (by omega_arith)) (h.low _ (by omega_arith) (by omega_arith)),
    h.kr, lk₂.trans h.keep⟩

/-- `KrDone` from the state before the block of `KR`'s high half. -/
theorem krDone_trans {s s₂ s₄ s' : State} {len : Nat} (lk₄ : LkKeep s₂ s₄)
    (lo₄ : ∀ k < slots, k < krSlot → slotW s₄ k = slotW s₂ k) (h : KrDone s s₄ s' len) : KrDone s s₂ s' len :=
  ⟨h.kr, lk₄.trans h.keep, fun k hk h' => by rw [h.low k hk h', lo₄ k hk h']⟩

/-- `loadKey`: `KL`'s and `KR`'s halves, as words, in their slots. -/
theorem loadKey_wp {s : State} {len : Nat} (hs : LkPre s len) :
    WP isa loadKey s fun s' =>
      WordsAt s' klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)) ∧
      WordsAt s' krSlot (hiW (krOf s.mem (s.gpr .a0) len), loW (krOf s.mem (s.gpr .a0) len)) ∧
      LkKeep s s' := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨s₂, e₂, lk₂, a3₂, hkl, hz₂⟩ := klBlock_ok hs
  have hp₂ := hs.of_keep lk₂ a3₂
  unfold loadKey
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  refine WP.mono (Q := fun s' => KrDone s s₂ s' len)
    (WP.ite (decide (len = 16)) ((eval_zero s₂ t1).trans (by rw [hz₂])) (fun h16 => ?_) (fun h16 => ?_))
    fun s' h => lkPost_of hkl lk₂ h
  · obtain ⟨u', e', h'⟩ := kr16_ok (s := s) hp₂ (by simpa using h16)
    exact WP.of_runBlock ⟨u', e', h'⟩
  · have h16 : len ≠ 16 := by simpa using h16
    obtain ⟨s₄, e₄, lk₄, a3₄, lo₄, w₄, hz₄⟩ := krBlock_ok hs lk₂ hp₂ h16
    have lk₂₄ := lk₂.trans lk₄
    have hp₄ := hs.of_keep lk₂₄ (a3₄.trans a3₂)
    refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
    refine WP.mono (Q := fun s' => KrDone s s₄ s' len)
      (WP.ite (decide (len = 24)) ((eval_zero s₄ t1).trans (by rw [hz₄])) (fun h24 => ?_) (fun h24 => ?_))
      fun s' h => krDone_trans lk₄ lo₄ h
    · obtain ⟨u', e', h'⟩ := kr24_ok hs hp₄ (by simpa using h24) w₄
      exact WP.of_runBlock ⟨u', e', h'⟩
    · obtain ⟨u', e', h'⟩ := kr32_ok hs lk₂₄ hp₄ h16 (by simpa using h24) w₄
      exact WP.of_runBlock ⟨u', e', h'⟩


/-! ## Loading the values -/

def lvChunk (v k : Nat) : List Instr :=
  loadBE64 (hiReg v) t0 sb (8 * k) ++ loadBE64 (loReg v) t0 sb (8 * (k + 1))

theorem loadValues_eq :
    loadValues = lvChunk 0 klSlot ++ (lvChunk 1 krSlot ++ (lvChunk 2 kaSlot ++ lvChunk 3 kbSlot)) := by
  rfl

theorem regs_lt4 {v : Nat} (hv : v < 4) : hiReg v ≠ sb ∧ loReg v ≠ sb ∧ hiReg v ≠ loReg v ∧
    hiReg v ≠ t0 ∧ loReg v ≠ t0 := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

/-- `loadBE64 t t0 sb (8 k)`: slot `k`, read big-endian. -/
theorem ldBE_ok {s : State} {k : Nat} (t : Reg) (ht : t ≠ sb) (ht0 : t ≠ t0)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < keySlot) {H : BitVec 64}
    (hw : WordOf (slotW s k) H) :
    ∃ s', runBlock isa (loadBE64 t t0 sb (8 * k)) s = some s' ∧ s'.gpr t = H ∧
      (∀ r, r ≠ t → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hk' : k < slots := by rw [keySlot_eq] at hk; rw [slots_eq]; omega_arith
  obtain ⟨r, hr, hc⟩ := scr_in hscr hk'
  obtain ⟨s', e', h'⟩ := WP.runBlock_of (ByteLoad.loadBE64_ok (s := s) (d := t) (tmp := t0) (n := sb)
    (off := 8 * k) ht (by decide) ht0 (by rw [keySlot_eq] at hk; omega_arith) ⟨r, List.mem_append_right _ hr, hc⟩)
  subst h'
  refine ⟨_, e', ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · rw [RegUpd.gpr_write_self]; exact be64_of_wordOf hw
  · rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]

theorem lvChunk_ok {s : State} {v k : Nat} (hv : v < 4) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k + 1 < keySlot) {H L : BitVec 64} (hw : WordsAt s k (H, L)) :
    ∃ s', runBlock isa (lvChunk v k) s = some s' ∧ s'.gpr (hiReg v) = H ∧ s'.gpr (loReg v) = L ∧
      (∀ r, r ≠ hiReg v → r ≠ loReg v → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := regs_lt4 hv
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := ldBE_ok (k := k) (hiReg v) n1 n4 hscr (by omega_arith) hw.1
  have hb₂ : s₂.gpr sb = s.gpr sb := o₂ _ n1.symm (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := ldBE_ok (s := s₂) (k := k + 1) (loReg v) n2 n5
    (by rw [hb₂, wr₂]; exact hscr) hk (by rw [slotW_eq_of m₂ hb₂]; exact hw.2)
  refine ⟨s₄, by rw [lvChunk, runBlock_append', e₂, Option.bind_some, e₄], ?_, a₄,
    fun r h1 h2 h3 => by rw [o₄ r h2 h3, o₂ r h1 h3], by rw [m₄, m₂], by rw [rd₄, rd₂], by rw [wr₄, wr₂]⟩
  rw [o₄ _ n3 n4, a₂]

/-- `loadValues`: the four values' halves, read big-endian into `hiReg v` and `loReg v`. -/
theorem loadValues_ok {s : State} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (vs : List (BitVec 128))
    (hw : ∀ v < 4, WordsAt s ([klSlot, krSlot, kaSlot, kbSlot].getD v 0) (hiW (vs.getD v 0), loW (vs.getD v 0))) :
    ∃ s', runBlock isa loadValues s = some s' ∧
      (∀ v < 4, s'.gpr (hiReg v) = hiW (vs.getD v 0) ∧ s'.gpr (loReg v) = loW (vs.getD v 0)) ∧
      (∀ r, (∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v) → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl, hr, hW, hA, hB, -, hK, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, h₁, l₁, o₁, m₁, rd₁, wr₁⟩ := lvChunk_ok (v := 0) (k := klSlot) (by decide) hscr (by omega_arith)
    (hw 0 (by decide))
  have hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (by decide) (by decide) (by decide)
  have hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ hb₁
  obtain ⟨s₂, e₂, h₂, l₂, o₂, m₂, rd₂, wr₂⟩ := lvChunk_ok (v := 1) (k := krSlot) (by decide)
    (by rw [hb₁, wr₁]; exact hscr) (by omega_arith) ((hw 1 (by decide)).congr (hs₁ _) (hs₁ _))
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide) (by decide) (by decide), hb₁]
  have hs₂ : ∀ k, slotW s₂ k = slotW s k := fun k => by rw [slotW_eq_of m₂ (by rw [hb₂, hb₁]), hs₁]
  obtain ⟨s₃, e₃, h₃, l₃, o₃, m₃, rd₃, wr₃⟩ := lvChunk_ok (v := 2) (k := kaSlot) (by decide)
    (by rw [hb₂, wr₂, wr₁]; exact hscr) (by omega_arith) ((hw 2 (by decide)).congr (hs₂ _) (hs₂ _))
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [o₃ _ (by decide) (by decide) (by decide), hb₂]
  have hs₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by rw [slotW_eq_of m₃ (by rw [hb₃, hb₂]), hs₂]
  obtain ⟨s₄, e₄, h₄, l₄, o₄, m₄, rd₄, wr₄⟩ := lvChunk_ok (v := 3) (k := kbSlot) (by decide)
    (by rw [hb₃, wr₃, wr₂, wr₁]; exact hscr) (by omega_arith) ((hw 3 (by decide)).congr (hs₃ _) (hs₃ _))
  refine ⟨s₄, by rw [loadValues_eq, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂,
      Option.bind_some, runBlock_append', e₃, Option.bind_some, e₄], fun v hv => ?_,
    fun r hr h0 => by
      obtain ⟨a0, b0⟩ := hr 0 (by decide); obtain ⟨a1, b1⟩ := hr 1 (by decide)
      obtain ⟨a2, b2⟩ := hr 2 (by decide); obtain ⟨a3, b3⟩ := hr 3 (by decide)
      rw [o₄ r a3 b3 h0, o₃ r a2 b2 h0, o₂ r a1 b1 h0, o₁ r a0 b0 h0],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · exact ⟨by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide),
        o₂ _ (by decide) (by decide) (by decide), h₁],
      by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide),
        o₂ _ (by decide) (by decide) (by decide), l₁]⟩
  · exact ⟨by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide), h₂],
      by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide), l₂]⟩
  · exact ⟨by rw [o₄ _ (by decide) (by decide) (by decide), h₃],
      by rw [o₄ _ (by decide) (by decide) (by decide), l₃]⟩
  · exact ⟨h₄, l₄⟩

/-! ## The prologue -/

theorem sreg_ne' (i : Nat) (hi : i < 12) : sreg i ≠ sb ∧ sreg i ≠ .a3 := by
  revert i; decide

theorem ekPrologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .a3 = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr)
    (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) (hal : b.toNat % 8 = 0) :
    ∃ s, runBlock isa ([movR sb .a3, movR .a3 .a1] ++ saveRegs ++ setSlots allMasks ++ tableSetup ++
        sigmas.flatMap sigmaOne) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .a3 = s₀.gpr .a1 ∧
      (∀ r, r ≠ sb → r ≠ .a3 → r ≠ t0 → r ≠ t1 → r ≠ kp → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧
      (∀ i < 6, ∀ j < 8, entryW s.mem b i j = keyPlane (sigmas.getD i 0) j) ∧
      Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hk := keySlot_eq
  have hsv := savedSlot_eq
  have hS := slots_eq
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ sb .a3
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₁a .a3 .a1
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), r₁a, hb]
  have g₁ : ∀ r, r ≠ sb → r ≠ .a3 → s₁.gpr r = s₀.gpr r := fun r h1 h2 => by rw [o₁ r h2, o₁a r h1]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁, wr₁a]; exact hw) hb₁ hal
  obtain ⟨s₃, e₃, v₃, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) (by rw [wr₂, wr₁, wr₁a]; exact hw)
    (by rw [g₂, hb₁]) hal
  have hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide), g₂, hb₁]
  obtain ⟨s₄, e₄, k₄, o₄, m₄, rd₄, wr₄⟩ := setKp_ok s₃
  have hb₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), hb₃]
  obtain ⟨s₅, e₅, v₅, f₅, r₅, g₅, rd₅, wr₅⟩ := sigmaList_ok hfit hal sigmas 0 s₄
    (by rw [wr₄, wr₃, wr₂, wr₁, wr₁a]; exact hw)
    (by rw [k₄, hb₃]; simp) (by decide)
  have hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide) (by decide), hb₄]
  -- The slots outside the table keep their values.
  have hs₅ : ∀ k, k < keySlot ∨ keySlot + 48 ≤ k → k < slots → slotW s₅ k = slotW s₃ k := fun k h1 h2 => by
    simp only [slotW, hb₅, hb₃]
    rw [← m₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [wordAddr, Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
    exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨s₅, ?_, hb₅, ?_, fun r h1 h2 h3 h4 h5 => ?_, fun i hi => ?_, fun kv hkv => ?_,
    fun i hi j hj => ?_, ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁, rd₁a],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁, wr₁a]⟩
  · rw [runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      show ([movR sb .a3, movR .a3 .a1] : List Instr) = [movR sb .a3] ++ [movR .a3 .a1] from rfl,
      runBlock_append', e₁a, Option.bind_some, e₁, Option.bind_some, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some, e₅]
  · rw [g₅ _ (by decide) (by decide) (by decide), o₄ _ (by decide), g₃ _ (by decide) (by decide), g₂, r₁,
      o₁a _ (by decide)]
  · rw [g₅ r h3 h4 h5, o₄ r h5, g₃ r h3 h4, g₂, g₁ r h1 h2]
  · have n := sreg_ne' i hi
    have := sv₂ i hi
    rw [show s₁.gpr (sreg i) = s₀.gpr (sreg i) from g₁ _ n.1 n.2] at this
    rw [← this]
    have h' := hs₅ (savedSlot + i) (Or.inl (by omega_arith)) (by omega_arith)
    simp only [slotW, hb₅, hb₃] at h'
    rw [h']
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by omega_arith) (by omega_arith)
  · have := mask_lt hkv
    rw [hs₅ _ (Or.inl (by omega_arith)) (by omega_arith)]
    exact v₃ kv hkv
  · have := v₅ i (by simpa [sigmas] using hi) j hj
    rw [Nat.zero_add] at this
    exact this
  · have sub : ∀ {r : Region}, Region.Sub r ⟨b, 8 * slots⟩ → ∀ r' ∈ [r], ∃ r'' ∈ [(⟨b, 8 * slots⟩ : Region)],
        Region.Sub r' r'' := fun hs r' hr' => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr'; subst hr'; exact hs⟩
    have f₂' : Frame [⟨b, 8 * slots⟩] s₁.mem s₂.mem :=
      f₂.sub (sub (VG.Offset.sub_base b (by omega_arith)))
    have f₃' : Frame [⟨b, 8 * slots⟩] s₂.mem s₃.mem := f₃.sub (sub (Region.sub_prefix (by omega_arith)))
    have f₅' : Frame [⟨b, 8 * slots⟩] s₄.mem s₅.mem := f₅.sub (sub (by
      simp only [Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
      exact VG.Offset.sub_base b (by omega_arith)))
    rw [m₁, m₁a] at f₂'
    rw [m₄] at f₅'
    exact f₂'.trans (f₃'.trans f₅')

end VG.Proof.Camellia.RISCV64
