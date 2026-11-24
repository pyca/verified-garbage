module

public import VerifiedGarbage.Proof.Camellia.X86.SseCore
public import VerifiedGarbage.Proof.Camellia.X86.AesNiExpandKey
public import VerifiedGarbage.Impl.Camellia.X86.SseExpandKey
meta import VerifiedGarbage.Proof.Camellia.X86.ExpandKey
meta import VerifiedGarbage.Impl.Camellia.X86.SseExpandKey
import VerifiedGarbage.Proof.Camellia.X86.SseKeyLit
meta import VerifiedGarbage.Proof.Camellia.X86.SseKeyLit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-!
# Camellia's key schedule on x86 (32-bit) in XMM registers

`mid_ok`: the block for `KA` and `KB` (`Impl/Camellia/X86/SseExpandKey.lean`)
leaves what the key schedule's proof (`ExpandKey.lean`) needs. A value's
bytes become the planes of its halves in all sixteen blocks (`spread_chk`),
which the core's rounds (`SseCore.round_ok`) take through the specification's,
and come back from them (`pack_chk`); `pair_ok` composes these.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.SseKey

open VG VG.X86 VG.X86.StraightSse VG.Bitslice VG.Impl.Camellia.X86.Sse VG.Impl.Camellia.X86.SseKey
open VG.Proof.Camellia.X86.Sse
open VG.Impl.Modes.X86 (sb)
open VG.Impl.Camellia.X86 (klSlot krSlot kaSlot kbSlot)
open VG.Proof.Camellia (pair byteOf sigE kaW kaD1 kaD2 kaD3)
open VG.X86.Straight (wordAddr)

/-! ## The checks -/

def spreadG (h j p : Nat) : List Nat := [8 * (8 * h + p / 16) + j]

theorem spread_chk : check (ofDom (lanes 128 7)) cfg (fun _ => none) spreadV (linEnv [(vS, 0, 0)])
    (linPost 60 7 (((List.range 8).map fun j => (d1 + j, spreadG 0 j)) ++ (List.range 8).map fun j => (d2 + j, spreadG 1 j))) =
      true := by
  kernel_rfl

/-- Bit `t % 8` of byte `t / 8`, from block `t % 8`. -/
def packG (t : Nat) : List Nat := [128 * (8 * (t / 64) + t % 8) + 16 * (t / 8 % 8) + t % 8]

def packOk (dst : Nat) : Bool :=
  check (ofDom (lanes 128 11)) cfg (fun _ => none) (packV dst) (linEnv (planesIn d1 0 ++ planesIn d2 8))
    (linPost 60 11 [(dst, packG)])

theorem pack_chk : (packOk vS && packOk kaS && packOk kbS) = true := by kernel_rfl

def atomsEnv : Env XE := { reg := fun _ => none, slot := fun k => some (.atom k) }

def xorOk (a b : Nat) : Bool :=
  check exprs cfg (fun _ => none) (xorV a b) atomsEnv fun e => e.slot vS == some (.bin .pxor (.atom a) (.atom b))

theorem xor_chk : (xorOk klS krS && xorOk vS klS && xorOk kaS krS) = true := by kernel_rfl

def storesK : Bool :=
  storesOk spreadV (fun k => d1 ≤ k && k < d1 + 16) && storesOk (packV vS) (· == vS) && storesOk (packV kaS) (· == kaS) &&
    storesOk (packV kbS) (· == kbS) && storesOk (xorV klS krS) (· == vS) && storesOk (xorV vS klS) (· == vS) &&
    storesOk (xorV kaS krS) (· == vS)

theorem stores_chk : storesK = true := by kernel_rfl

/-- The whole scratch buffer. -/
def cfgA : Cfg := ⟨sb, 92, kr, 0, tbr, tableName, table⟩

/-- The core's slot `k`, from `edi` not moved. -/
def sh24 (k : Nat) : Nat := 24 + k

theorem copyIn_chk : check exprs cfgA (fun _ => none) copyIn atomsEnv (fun e =>
    e.slot (sh24 klS) == some (.atom 18) && e.slot (sh24 krS) == some (.atom 19) &&
    (List.range 6).all fun i => e.slot (sh24 (62 + i)) == some (.const (tblAt table (144 + 16 * i)))) = true := by
  kernel_rfl

theorem copyOut_chk : check exprs cfgA (fun _ => none) copyOut atomsEnv (fun e =>
    e.slot 21 == some (.atom (sh24 kaS)) && e.slot 22 == some (.atom (sh24 kbS))) = true := by
  kernel_rfl

theorem copy_stores : ((stored cfgA copyIn).all (fun k => 24 ≤ k) && (stored cfgA copyOut).all fun k => k == 21 || k == 22) = true := by
  kernel_rfl

/-- The table's constants as subkeys. -/
theorem sig_chk : ∀ i < 6, tblAt table (144 + 16 * i) = spread (sigE i) ^^^ uW := by decide +kernel

/-! ## The values -/

/-- The bytes of a value, the most significant first. -/
def VB (x : BitVec 128) (v : BitVec 64 × BitVec 64) : Prop :=
  ∀ c < 16, ∀ j < 8, x.getLsbD (8 * c + j) = (byteOf (if c < 8 then v.1 else v.2) (c % 8)).getLsbD j

theorem VB.xor {x y : BitVec 128} {u v : BitVec 64 × BitVec 64} (hx : VB x u) (hy : VB y v) :
    VB (x ^^^ y) (u.1 ^^^ v.1, u.2 ^^^ v.2) := fun c hc j hj => by
  rw [BitVec.getLsbD_xor, hx c hc j hj, hy c hc j hj, ← BitVec.getLsbD_xor, ← Proof.Camellia.byteOf_xor]
  split <;> rfl

/-- The four words at slot `4 k` hold a value if the 16 bytes there do. -/
theorem VW_iff {s : State} {b : BitVec 32} (hb : s.gpr sb = b) {k : Nat} (hfit : b.toNat + 16 * k + 16 ≤ 2 ^ 32)
    {v : BitVec 64 × BitVec 64} : VW s (4 * k) v ↔ VB (W s.mem b k) v := by
  have e := AesNiKey.VW_iff (s := s) (b := b) hb (a := 4 * k) (by omega_arith) (v := v)
  rw [e, W, show 4 * (4 * k) = 16 * k by omega_arith]
  have bit : ∀ c j, j < 8 → (byte (s.mem.readW (addr b (16 * k)) 128) c).getLsbD j =
      (s.mem.readW (addr b (16 * k)) 128).getLsbD (8 * c + j) := fun c j hj => by
    rw [byte, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
  constructor
  · intro h c hc j hj
    rw [← bit c j hj, h c hc]
  · intro h c hc
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [bit c j hj, h c hc j hj]

/-! ## The parts -/

section
variable {s₀ s : State} {B : BitVec 32} {q m : Nat}

theorem xorV_ok (h : At s₀ B q s) (hs : Sse.Slots m s₀ B) (hq : 60 + q + 4 ≤ m) {a b : Nat} (hchk : xorOk a b = true)
    (hst : storesOk (xorV a b) (· == vS) = true) :
    ∃ s', runBlock isa (xorV a b) s = some s' ∧ At s₀ B q s' ∧ s'.gpr = s.gpr ∧
      W s'.mem B vS = W s.mem B a ^^^ W s.mem B b ∧ ∀ k < 60, k ≠ vS → W s'.mem B k = W s.mem B k := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (fun (e : XE) x => x = e.eval fun n => W s.mem B n) cfg (fun _ => none) atomsEnv s :=
    ⟨(fun r a ha => by cases ha), (fun k a hk ha => by cases ha; exact h.slot k), fun k a hk ha => by cases ha⟩
  obtain ⟨s', hs', p'⟩ := run (exprs_sound fun n => W s.mem B n) (h.ok hs hq) hrel he
  refine ⟨s', hs', h.runs p'.runs hst rfl, p'.gpr, ?_, fun k hk hne => h.kept p'.runs hst hk (by simp [hne])⟩
  have := p'.rel.slot vS _ (by decide) (eq_of_beq hpost)
  rw [p'.gpr, h.slot'] at this
  exact this

/-- The running value to the planes of its halves, in every block. -/
theorem spread_ok (h : At s₀ B q s) (hs : Sse.Slots m s₀ B) (hq : 60 + q + 4 ≤ m) {v : BitVec 64 × BitVec 64}
    (hv : VB (W s.mem B vS) v) :
    ∃ s', runBlock isa spreadV s = some s' ∧ At s₀ B q s' ∧ s'.gpr = s.gpr ∧ PAt s'.mem B d1 (fun _ => v.1) ∧
      PAt s'.mem B d2 (fun _ => v.2) ∧ ∀ k, 44 ≤ k → k < 60 → W s'.mem B k = W s.mem B k := by
  obtain ⟨s', hr', p', ho⟩ := linear_ok0 spread_chk (h.ok hs hq) (fun _ => W s.mem B vS) fun j i w hm _ => by
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    refine ⟨by decide, ?_⟩
    rw [h.slot]; exact xor0 _
  have st := stores_chk
  simp only [storesK, Bool.and_eq_true] at st
  refine ⟨s', hr', h.runs p' st.1.1.1.1.1.1 rfl, p'.gpr, fun b hb i hi j hj => ?_, fun b hb i hi j hj => ?_,
    fun k h1 h2 => h.kept p' st.1.1.1.1.1.1 h2 (by
      rw [show d1 = 28 from rfl, decide_eq_false (show ¬ k < 28 + 16 by omega_arith), Bool.and_false])⟩
  · have g := ho (d1 + j) (spreadG 0 j) (List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
      (16 * i + b) (by omega_arith)
    rw [h.slot', spreadG, xorBits_cons, xorBits_nil, Bool.xor_false, show (16 * i + b) / 16 = i by omega_arith] at g
    rw [g, show 8 * (8 * 0 + i) + j = 128 * 0 + (8 * i + j) by omega_arith, bitOf_word _ _ _ (by omega_arith),
      hv i (by omega_arith) j hj, ite_eq_left hi, Nat.mod_eq_of_lt hi]
  · have g := ho (d2 + j) (spreadG 1 j) (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
      (16 * i + b) (by omega_arith)
    rw [h.slot', spreadG, xorBits_cons, xorBits_nil, Bool.xor_false, show (16 * i + b) / 16 = i by omega_arith] at g
    rw [g, show 8 * (8 * 1 + i) + j = 128 * 0 + (8 * (8 + i) + j) by omega_arith, bitOf_word _ _ _ (by omega_arith),
      hv (8 + i) (by omega_arith) j hj, ite_eq_right (by omega_arith), show (8 + i) % 8 = i by omega_arith]

/-- And back. -/
theorem pack_ok (h : At s₀ B q s) (hs : Sse.Slots m s₀ B) (hq : 60 + q + 4 ≤ m) {dst : Nat} (hchk : packOk dst = true)
    (hst : storesOk (packV dst) (· == dst) = true) (hd : 44 ≤ dst ∧ dst < 60) {v : BitVec 64 × BitVec 64}
    (h1 : PAt s.mem B d1 (fun _ => v.1)) (h2 : PAt s.mem B d2 (fun _ => v.2)) :
    ∃ s', runBlock isa (packV dst) s = some s' ∧ At s₀ B q s' ∧ s'.gpr = s.gpr ∧ VB (W s'.mem B dst) v ∧
      ∀ k, k < 60 → k ≠ dst → W s'.mem B k = W s.mem B k := by
  obtain ⟨s', hr', p', ho⟩ := linear_ok0 hchk (h.ok hs hq)
    (fun i => if i < 8 then W s.mem B (d1 + i) else W s.mem B (d2 + (i - 8))) fun j i w hm _ => by
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨t, ht, rfl, rfl, rfl⟩ := mem_planesIn hm
      refine ⟨by omega_arith, ?_⟩
      rw [h.slot, ite_eq_left (by omega_arith), xor0, Nat.zero_add]
    · obtain ⟨t, ht, rfl, rfl, rfl⟩ := mem_planesIn hm
      refine ⟨by omega_arith, ?_⟩
      rw [h.slot, ite_eq_right (by omega_arith), xor0, Nat.add_sub_cancel_left]
  have hne : (tblSlot == dst) = false := beq_eq_false_iff_ne.mpr (by have := hd.1; show 26 ≠ dst; omega_arith)
  refine ⟨s', hr', h.runs p' hst hne, p'.gpr, fun c hc j hj => ?_,
    fun k hk hn => h.kept p' hst hk (beq_eq_false_iff_ne.mpr hn)⟩
  have g := ho dst packG List.mem_cons_self (8 * c + j) (by omega_arith)
  rw [h.slot', packG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ (by omega_arith),
    show (8 * c + j) / 64 = c / 8 by omega_arith, show (8 * c + j) % 8 = j by omega_arith,
    show (8 * c + j) / 8 % 8 = c % 8 by omega_arith] at g
  rw [g]
  by_cases h8 : c < 8
  · rw [ite_eq_left (by omega_arith), ite_eq_left h8, show 8 * (c / 8) + j = j by omega_arith,
      h1 j (by omega_arith) (c % 8) (by omega_arith) j hj]
  · rw [ite_eq_right (by omega_arith), ite_eq_right h8, show 8 * (c / 8) + j - 8 = j by omega_arith,
      h2 j (by omega_arith) (c % 8) (by omega_arith) j hj]

/-- A pair of rounds on the running value. -/
theorem pair_ok (h : At s₀ B q s) (hs : Sse.Slots m s₀ B) (hq : 60 + q + 4 ≤ m) {dst : Nat} (hchk : packOk dst = true)
    (hst : storesOk (packV dst) (· == dst) = true) (hd : 44 ≤ dst ∧ dst < 60) {v : BitVec 64 × BitVec 64}
    (hv : VB (W s.mem B vS) v) {k₁ k₂ : BitVec 64} (h1 : W s₀.mem B (60 + q + 2) = spread k₁ ^^^ uW)
    (h2 : W s₀.mem B (60 + q + 3) = spread k₂ ^^^ uW) :
    ∃ s', runBlock isa (pairV dst) s = some s' ∧ At s₀ B q s' ∧ s'.gpr = s.gpr ∧ VB (W s'.mem B dst) (pair k₁ k₂ v) ∧
      ∀ k, 44 ≤ k → k < 60 → k ≠ dst → W s'.mem B k = W s.mem B k := by
  have st := parts_rounds
  simp only [Bool.and_eq_true] at st
  obtain ⟨s₁, r₁, a₁, g₁, x₁, y₁, e₁⟩ := spread_ok h hs hq hv
  have key : ∀ {u : State}, At s₀ B q u → ∀ r, r < 4 → W u.mem B (60 + q + r) = W s₀.mem B (60 + q + r) := fun a r hr => by
    rw [Nat.add_assoc]; exact a.key hs (by omega_arith)
  obtain ⟨s₂, r₂, a₂, x₂, y₂, g₂, e₂⟩ := round_ok a₁ hs hq (r := 2) (src := d1) (dst := d2) (by decide) roundIn_chk1
    roundOut_chk2 st.1.1.1 st.1.1.2 (by decide) (by decide) (by decide) (by decide) (by decide) x₁ y₁
    ((key a₁ 2 (by decide)).trans h1)
  obtain ⟨s₃, r₃, a₃, x₃, y₃, g₃, e₃⟩ := round_ok a₂ hs hq (r := 3) (src := d2) (dst := d1) (by decide) roundIn_chk2
    roundOut_chk1 st.1.2 st.2 (by decide) (by decide) (by decide) (by decide) (by decide) y₂ x₂
    ((key a₂ 3 (by decide)).trans h2)
  obtain ⟨s₄, r₄, a₄, g₄, v₄, e₄⟩ := pack_ok a₃ hs hq hchk hst hd (v := pair k₁ k₂ v) y₃ x₃
  refine ⟨s₄, ?_, a₄, g₄.trans (g₃.trans (g₂.trans g₁)), v₄, fun k hk1 hk2 hk3 => ?_⟩
  · rw [pairV, List.append_assoc, List.append_assoc]
    exact run_append r₁ (run_append r₂ (run_append r₃ r₄))
  · rw [e₄ k hk2 hk3, e₃ k hk1 hk2, e₂ k hk1 hk2, e₁ k hk1 hk2]

/-- The constants, as subkeys. -/
def Sigs (m : Mem) (B : BitVec 32) : Prop := ∀ i < 6, W m B (62 + i) = spread (sigE i) ^^^ uW

theorem next_wp {is : List Instr} {Q : State → Prop} (h : At s₀ B q s)
    (K : ∀ s', At s₀ B (q + 2) s' → s'.mem = s.mem → WP isa (.block is) s' Q) : WP isa (.block (next :: is)) s Q :=
  Wp.wp_addi fun s' u => K s' (h.next u) u.mem

/-- `KA` and `KB`, in the core's slots. -/
theorem kaKb_wp (h : At s₀ B 0 s₀) (hs : Sse.Slots 68 s₀ B) (hk : Sigs s₀.mem B) {KL KR : BitVec 64 × BitVec 64}
    (hl : VB (W s₀.mem B klS) KL) (hr : VB (W s₀.mem B krS) KR) {is : List Instr} {Q : State → Prop}
    (K : ∀ s', At s₀ B 4 s' → VB (W s'.mem B kaS) (kaD2 KL KR) → VB (W s'.mem B kbS) (kaD3 KL KR) →
      WP isa (.block is) s' Q) :
    WP isa (.block (kaKb ++ is)) s₀ Q := by
  have cx := xor_chk
  have cp := pack_chk
  have st := stores_chk
  simp only [Bool.and_eq_true, storesK] at cx cp st
  unfold kaKb
  simp only [List.append_assoc, List.cons_append]
  -- The first pair, on `KL ^ KR`.
  obtain ⟨s₁, r₁, a₁, -, v₁, e₁⟩ := xorV_ok h hs (by decide) cx.1.1 st.1.1.2
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, r₁, ?_⟩)
  obtain ⟨s₂, r₂, a₂, -, v₂, e₂⟩ := pair_ok a₁ hs (by decide) cp.1.1 st.1.1.1.1.1.2 (by decide) (v := kaW KL KR 0)
    (by rw [v₁]; exact hl.xor hr) (hk 0 (by decide)) (hk 1 (by decide))
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₂, r₂, ?_⟩)
  -- The second, with `KL`.
  obtain ⟨s₃, r₃, a₃, -, v₃, e₃⟩ := xorV_ok a₂ hs (by decide) cx.1.2 st.1.2
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₃, r₃, ?_⟩)
  refine next_wp a₃ fun s₄ a₄ m₄ => ?_
  obtain ⟨s₅, r₅, a₅, -, v₅, e₅⟩ := pair_ok a₄ hs (by decide) cp.1.2 st.1.1.1.1.2 (by decide) (v := kaW KL KR 1)
    (by
      rw [m₄, v₃, e₂ klS (by decide) (by decide) (by decide), e₁ klS (by decide) (by decide)]
      exact v₂.xor hl) (hk 2 (by decide)) (hk 3 (by decide))
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₅, r₅, ?_⟩)
  -- The third, with `KR`.
  obtain ⟨s₆, r₆, a₆, -, v₆, e₆⟩ := xorV_ok a₅ hs (by decide) cx.2 st.2
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₆, r₆, ?_⟩)
  refine next_wp a₆ fun s₇ a₇ m₇ => ?_
  obtain ⟨s₈, r₈, a₈, -, v₈, e₈⟩ := pair_ok a₇ hs (by decide) cp.2 st.1.1.1.2 (by decide) (v := kaW KL KR 2)
    (by
      rw [m₇, v₆, e₅ krS (by decide) (by decide) (by decide), m₄, e₃ krS (by decide) (by decide),
        e₂ krS (by decide) (by decide) (by decide), e₁ krS (by decide) (by decide)]
      exact v₅.xor hr) (hk 4 (by decide)) (hk 5 (by decide))
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₈, r₈, K s₈ a₈ ?_ v₈⟩)
  rw [e₈ kaS (by decide) (by decide) (by decide), m₇, e₆ kaS (by decide) (by decide)]
  exact v₅

end

/-! ## The block -/

section
variable {s : State} {b : BitVec 32}

/-- The scratch buffer, as slots of 16 bytes. -/
theorem ok_all (hb : s.gpr sb = b) (hw : ScrInN 368 s.wr b) (ht : s.gpr tbr = s.syms tableName) : Ok cfgA s := by
  have hf := hw.fit
  obtain ⟨n, hn, hf', hr⟩ := hw.mem
  refine ⟨fun k hk => ?_, fun k hk => absurd hk (Nat.not_lt_zero _), ?_, fun k hk j hj => absurd hj (Nat.not_lt_zero _), ht⟩
  · have hk : k < 92 := hk
    refine ⟨_, hr, ?_⟩
    show Region.Contains _ (addr (s.gpr sb) (16 * k)) 16
    rw [hb, addr_eq (by omega_arith)]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · show (s.gpr sb).toNat + 16 * 92 ≤ _
    rw [hb]; omega_arith

/-- The core's slot `k`, from the scratch buffer's base. -/
theorem W_shift (m : Mem) (k : Nat) : W m (b + BitVec.ofNat 32 384) k = W m b (24 + k) := by
  rw [W, W, Straight.addr_add_ofNat, show 384 + 16 * k = 16 * (24 + k) by omega_arith]

theorem copyIn_ok (hb : s.gpr sb = b) (hw : ScrInN 368 s.wr b) (ht : s.gpr tbr = s.syms tableName) :
    ∃ s', runBlock isa copyIn s = some s' ∧ Runs cfgA copyIn s s' ∧ Sigs s'.mem (b + BitVec.ofNat 32 384) ∧
      W s'.mem (b + BitVec.ofNat 32 384) klS = W s.mem b 18 ∧ W s'.mem (b + BitVec.ofNat 32 384) krS = W s.mem b 19 ∧
      ∀ k < 24, W s'.mem b k = W s.mem b k := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ copyIn_chk
  have hsl : ∀ m : Mem, ∀ k, m.readW (xAddr (s.gpr cfgA.base) k) 128 = W m b k := fun m k => by
    show m.readW (addr (s.gpr sb) _) 128 = _
    rw [hb]; rfl
  have hrel : Rel (fun (e : XE) x => x = e.eval fun n => W s.mem b n) cfgA (fun _ => none) atomsEnv s :=
    ⟨(fun r a ha => by cases ha), (fun k a hk ha => by cases ha; exact hsl _ k), fun k a hk ha => by cases ha⟩
  obtain ⟨s', hs', p'⟩ := run (exprs_sound fun n => W s.mem b n) (ok_all hb hw ht) hrel he
  simp only [Bool.and_eq_true] at hpost
  have get : ∀ {k : Nat} {e : XE}, k < 92 → e'.slot k = some e → W s'.mem b k = e.eval fun n => W s.mem b n :=
    fun {k e} hk hv => by
      have := p'.rel.slot k _ hk hv
      rwa [p'.gpr, hsl] at this
  refine ⟨s', hs', p'.runs, fun i hi => ?_, ?_, ?_, fun k hk => ?_⟩
  · have hk : sh24 (62 + i) < 92 := by unfold sh24; omega_arith
    have := get hk (eq_of_beq (List.all_eq_true.mp hpost.2 i (List.mem_range.mpr hi)))
    rw [W_shift, show 24 + (62 + i) = sh24 (62 + i) from rfl, this, XE.eval, sig_chk i hi]
  · rw [W_shift]; exact get (by decide) (eq_of_beq hpost.1.1)
  · rw [W_shift]; exact get (by decide) (eq_of_beq hpost.1.2)
  · rw [← hsl, ← hsl]
    refine p'.runs.kept k (show k < 92 by omega_arith) fun hm => ?_
    have st := copy_stores
    rw [Bool.and_eq_true] at st
    have := of_decide_eq_true (List.all_eq_true.mp st.1 k hm)
    omega_arith

theorem copyOut_ok (hb : s.gpr sb = b) (hw : ScrInN 368 s.wr b) (ht : s.gpr tbr = s.syms tableName) :
    ∃ s', runBlock isa copyOut s = some s' ∧ Runs cfgA copyOut s s' ∧
      W s'.mem b 21 = W s.mem (b + BitVec.ofNat 32 384) kaS ∧ W s'.mem b 22 = W s.mem (b + BitVec.ofNat 32 384) kbS ∧
      ∀ k < 24, k ≠ 21 → k ≠ 22 → W s'.mem b k = W s.mem b k := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ copyOut_chk
  have hsl : ∀ m : Mem, ∀ k, m.readW (xAddr (s.gpr cfgA.base) k) 128 = W m b k := fun m k => by
    show m.readW (addr (s.gpr sb) _) 128 = _
    rw [hb]; rfl
  have hrel : Rel (fun (e : XE) x => x = e.eval fun n => W s.mem b n) cfgA (fun _ => none) atomsEnv s :=
    ⟨(fun r a ha => by cases ha), (fun k a hk ha => by cases ha; exact hsl _ k), fun k a hk ha => by cases ha⟩
  obtain ⟨s', hs', p'⟩ := run (exprs_sound fun n => W s.mem b n) (ok_all hb hw ht) hrel he
  simp only [Bool.and_eq_true] at hpost
  have get : ∀ {k : Nat} {e : XE}, k < 92 → e'.slot k = some e → W s'.mem b k = e.eval fun n => W s.mem b n :=
    fun {k e} hk hv => by
      have := p'.rel.slot k _ hk hv
      rwa [p'.gpr, hsl] at this
  refine ⟨s', hs', p'.runs, ?_, ?_, fun k hk h1 h2 => ?_⟩
  · rw [W_shift]; exact get (by decide) (eq_of_beq hpost.1)
  · rw [W_shift]; exact get (by decide) (eq_of_beq hpost.2)
  · rw [← hsl, ← hsl]
    refine p'.runs.kept k (show k < 92 by omega_arith) fun hm => ?_
    have st := copy_stores
    rw [Bool.and_eq_true] at st
    have := List.all_eq_true.mp st.2 k hm
    rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at this
    omega_arith

/-- A doubleword of a slot of 16 bytes. -/
theorem word_of_W {m m' : Mem} {k : Nat} (h : W m' b (k / 4) = W m b (k / 4)) (hf : b.toNat + 4 * k + 16 ≤ 2 ^ 32) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  have e : ∀ m : Mem, m.readW (wordAddr b k) 32 = dword (W m b (k / 4)) (k % 4) := fun m => by
    rw [W, dword_readW _ _ (Nat.mod_lt _ (by decide)), wordAddr, addr_eq (by omega_arith), addr_eq (by omega_arith),
      Offset.add_ofNat_add_ofNat, show 16 * (k / 4) + 4 * (k % 4) = 4 * k by omega_arith]
  rw [e, e, h]

theorem mid_ok : MidOk 368 tableName mid := by
  intro s b KL KR hb ht hw hl hr
  have hb : s.gpr sb = b := hb
  have hf := hw.fit
  obtain ⟨B, hB⟩ : ∃ B : BitVec 32, B = b + BitVec.ofNat 32 384 := ⟨_, rfl⟩
  have hBn : B.toNat = b.toNat + 384 := by rw [hB]; exact Straight.toNat_add_off (by omega_arith)
  have hl' : VB (W s.mem b 18) KL := (VW_iff (k := 18) hb (by omega_arith)).mp hl
  have hr' : VB (W s.mem b 19) KR := (VW_iff (k := 19) hb (by omega_arith)).mp hr
  unfold mid
  refine Wp.wp_mov fun s₁ u₁ => ?_
  have b₁ : s₁.gpr sb = b := by rw [u₁.other _ (by decide), hb]
  have t₁ : s₁.gpr tbr = s₁.syms tableName := by rw [u₁.gpr, u₁.syms, ht]
  have w₁ : ScrInN 368 s₁.wr b := by rw [u₁.wr]; exact hw
  obtain ⟨s₂, r₂, p₂, sg, kl, kr', k₂⟩ := copyIn_ok b₁ w₁ t₁
  rw [← hB] at sg kl kr'
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₂, r₂, ?_⟩)
  refine Wp.wp_addi fun s₃ u₃ => Wp.wp_mov fun s₄ u₄ => Wp.wp_addi fun s₅ u₅ => ?_
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have B₅ : s₅.gpr sb = B := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, p₂.gpr, b₁, hB]; rfl
  have t₅ : s₅.gpr tbr = s₅.syms tableName := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), p₂.gpr, t₁, u₅.syms, u₄.syms, u₃.syms, p₂.syms]
  have k₅ : s₅.gpr kr = B + BitVec.ofNat 32 (16 * (60 + 0)) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, p₂.gpr, b₁, hB]; rfl
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, p₂.wr, u₁.wr]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, p₂.rd, u₁.rd]
  have sp₅ : s₅.gpr .esp = s.gpr .esp := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), p₂.gpr, u₁.other _ (by decide)]
  have hsl : Sse.Slots 68 s₅ B := by
    refine ⟨fun k hk => ?_, by omega_arith⟩
    obtain ⟨n, hn, hf', hr⟩ := hw.mem
    refine ⟨_, by rw [wr₅]; exact hr, ?_⟩
    rw [hB, Straight.addr_add_ofNat, addr_eq (by omega_arith)]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have a₅ : At s₅ B 0 s₅ := ⟨B₅, rfl, k₅, t₅, rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  refine kaKb_wp a₅ hsl (fun i hi => by rw [m₅]; exact sg i hi) (KL := KL) (KR := KR)
    (by rw [m₅, kl, u₁.mem]; exact hl') (by rw [m₅, kr', u₁.mem]; exact hr') fun s₆ a₆ ka kb => ?_
  refine Wp.wp_subi fun s₇ u₇ _ _ => ?_
  have b₇ : s₇.gpr sb = b := by
    rw [u₇.gpr, a₆.base, hB, show (384 : BitVec 32) = BitVec.ofNat 32 384 from rfl, BitVec.add_sub_cancel]
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, a₆.wr, wr₅]
  obtain ⟨s₈, r₈, p₈, w21, w22, k₈⟩ := copyOut_ok b₇ (by rw [wr₇]; exact hw)
    (by rw [u₇.other _ (by decide), a₆.tb, u₇.syms, a₆.syms])
  rw [← hB, u₇.mem] at w21 w22
  -- The slots before the core's.
  have k₆ : ∀ k < 24, W s₆.mem b k = W s₅.mem b k := fun k hk => W_frame a₆.frame (by omega_arith) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨B.setWidth 64 + BitVec.ofNat 64 (16 * 0), 16 * 60⟩
    rw [hB, show (b + BitVec.ofNat 32 384).setWidth 64 = b.setWidth 64 + BitVec.ofNat 64 384 from addr_eq (by omega_arith),
      Offset.add_ofNat_add_ofNat]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  have keep : ∀ k < 24, k ≠ 21 → k ≠ 22 → W s₈.mem b k = W s.mem b k := fun k hk h1 h2 => by
    rw [k₈ k hk h1 h2, u₇.mem, k₆ k hk, m₅, k₂ k hk, u₁.mem]
  have b₈ : s₈.gpr sb = b := by rw [p₈.gpr, b₇]
  refine WP.of_runBlock ⟨s₈, r₈, b₈, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k h1 h2 => ?_, ?_⟩
  · rw [p₈.gpr, u₇.other _ (by decide), a₆.esp, sp₅]
  · rw [p₈.rd, u₇.rd, a₆.rd, rd₅]
  · rw [p₈.wr, wr₇]
  · refine (VW_iff (k := 18) b₈ (by omega_arith)).mpr ?_
    rw [keep 18 (by decide) (by decide) (by decide)]; exact hl'
  · refine (VW_iff (k := 19) b₈ (by omega_arith)).mpr ?_
    rw [keep 19 (by decide) (by decide) (by decide)]; exact hr'
  · refine (VW_iff (k := 21) b₈ (by omega_arith)).mpr ?_
    rw [w21]; exact ka
  · refine (VW_iff (k := 22) b₈ (by omega_arith)).mpr ?_
    rw [w22]; exact kb
  · exact word_of_W (keep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
  · have f₂ : Frame [⟨b.setWidth 64, 4 * 368⟩] s.mem s₂.mem := by
      have := p₂.frame
      simp only [slotRegion, show s₁.gpr cfgA.base = b from b₁, u₁.mem] at this
      exact this
    have f₈ : Frame [⟨b.setWidth 64, 4 * 368⟩] s₆.mem s₈.mem := by
      have := p₈.frame
      simp only [slotRegion, show s₇.gpr cfgA.base = b from b₇, u₇.mem] at this
      exact this
    have f₆ : Frame [⟨b.setWidth 64, 4 * 368⟩] s₂.mem s₆.mem := by
      rw [← m₅]
      refine a₆.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
      rw [List.mem_singleton] at hr; subst hr
      show Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 (16 * 0), 16 * 60⟩ _
      rw [hB, show (b + BitVec.ofNat 32 384).setWidth 64 = b.setWidth 64 + BitVec.ofNat 64 384 from addr_eq (by omega_arith),
        Offset.add_ofNat_add_ofNat]
      exact Offset.sub_base _ (by decide)
    exact (f₂.trans f₆).trans f₈

end

/-! ## The contract, and constant time -/

theorem expandKey_ct : ConstantTime isa (expandKeyC 368).pre (expandKeyC 368).pub expandKey :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (ekTaint 368) (fun _ _ h₁ h₂ hp => ekTaint_agree h₁ h₂ hp) (by taint_decide)

/-- Memory holding the arguments `0x1000, 16, 0x2000, 0x3000` at `0x8004`. -/
def sat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800D then 0x20 else
    if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x2000, 272⟩, ⟨0x3000, 1472⟩]

theorem expandKey_verified :
    Verified X86.target expandKey (Proof.Camellia.expandKeyScratchContract X86.abi 184 4) :=
  Verified.of_correct (fun _ hs => expandKey_wp (by decide) mid_ok hs) expandKey_ct (by
    sig_implies [Proof.Camellia.expandKeyScratchContract, Proof.Camellia.expandKeyScratchSig,
      Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre, Spec.Camellia.expandKeyPost, expandKeyC, expandKeyX86N,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [sat, arg, argAddr, Mem.readW, Mem.read] using sat)

/-- A state satisfying `vg_camellia_expand_key`'s precondition: a key of 16
bytes at `0x1000` and the schedule at `0x2000`, as stack arguments at
`0x8004`. -/
theorem frameSat : ∃ s, (Spec.Camellia.expandKeyContract X86.abi 1508).pre s := by
  implies_sat [Spec.Camellia.expandKeyContract, Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre,
    Spec.Camellia.expandKeyPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

/-- `expandKey` with its working space on the stack. -/
theorem expandKey_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1504 3 368 expandKey)
      (Spec.Camellia.expandKeyContract X86.abi 1508) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.expandKeySig) (nm := "scratch") (e := .u64) (n := 184)
    (pre := Spec.Camellia.expandKeyPre X86.abi.ptrBits) (post := Spec.Camellia.expandKeyPost X86.abi.ptrBits)
    (wa := false) (stack := 4) (bytes := 1504)
    (by rw [← Proof.Camellia.expandKeyScratchContract_eq]; exact expandKey_verified)
    (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.expandKeyPre_local _) (Proof.Camellia.expandKeyPost_local _)
    (Proof.Camellia.expandKeyPostOut_local _) frameSat

/-- `Spec.Camellia.expandKeyApi` as emitted (`Impl.Camellia.X86.SseKey.Fn.expandKey`) meets its contract
in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.SseKey.Fn.expandKey (Spec.Camellia.expandKeyContract X86.abi 1508) 0 :=
  X86.Scrub.verifiedScrubbedSel (api := Spec.Camellia.expandKeyApi) (W := 1508)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1504 3 368 expandKey
      verified := expandKey_framed }
    Fn.words (X86.Scrub.postOut_of_local (leak := none) X86.Scrub.ScrubAbi.plain
      (Proof.Camellia.expandKeyPostOut_local _)) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Camellia.X86.SseKey
