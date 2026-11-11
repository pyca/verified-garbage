module

public import VerifiedGarbage.Impl.Scrub.X86_64
public import VerifiedGarbage.TCB.X86_64.Residue
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# Returning without secret residue (x86-64)

`Verified.scrub`: code verified against a contract that `Sig.contract`
derives, whose frames and calls use at most the contract's `stack` bytes,
followed by `Impl.Scrub.X86_64.scrubTail` (`scrub`), is verified against the
same contract and returns without secret residue (`NoResidue`). The proof of
the code is used as it is: what `scrub` adds is checked once, here, for all
code (`tail_run`): it zeroes the stack below `rsp` (`wipe_run`), the SSE
registers and the caller-saved general-purpose registers, and its trace
depends only on `rsp`. What the code itself must satisfy is decidable
(`SpSafe`, its depth, the level of its vector instructions,
`ResidueKeep.lean`), but for its postcondition, which must read the memory
on return only within the buffers (`hpost`).
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

open VG.X86_64 VG.X86_64.Residue

/-- The trace of `storesF v ks off base f k` from `rsp = p`. -/
def storesTr (v : VecLevel) (ks : List Nat) (off : Nat) (p : Addr) (base : Nat) : Nat → Nat → List Leak
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, k + 1 =>
    (if span v ks (off + base) (k + 1) = 0 then []
      else [.addr (p + BitVec.ofNat 64 (base + 16 * (k + 1 - span v ks (off + base) (k + 1))))]) ++
    storesTr v ks off p base f (k + 1 - max (span v ks (off + base) (k + 1)) 1)

/-- The trace of `chunkStores v ks off b` from `rsp = p`. -/
def chunkTr (v : VecLevel) (ks : List Nat) (off : Nat) (p : Addr) (b : Nat) : List Leak :=
  storesTr v ks off p (b % 16) (b / 16) (b / 16) ++ (if b % 16 = 8 && ks.contains off then [.addr p] else [])

/-- Whether `chunkStores v ks off b` zeroes the byte at offset `d` of its frame. -/
def covC (ks : List Nat) (off b d : Nat) : Bool :=
  if d < b % 16 then b % 16 == 8 && ks.contains off
  else ks.contains (off + b % 16 + 16 * ((d - b % 16) / 16))

/-- Whether `wipe v ks cs` zeroes the byte at offset `i` from the bottom of the
`cs.sum` bytes it wipes. -/
def cov (ks : List Nat) : List Nat → Nat → Bool
  | [], _ => false
  | b :: bs, i => if i < bs.sum then cov ks bs i else decide (i - bs.sum < b) && covC ks bs.sum b (i - bs.sum)

theorem ea_rsp (u : State) (off : Nat) :
    u.ea { base := .rsp, disp := (off : Int) } = u.gpr .rsp + BitVec.ofNat 64 off := by
  simp [State.ea, BitVec.ofInt_natCast]

theorem ea_rsp2 (u : State) (a k : Nat) :
    u.ea { base := .rsp, disp := (a : Int) + 16 * (k : Int) } = u.gpr .rsp + BitVec.ofNat 64 (a + 16 * k) := by
  rw [show (a : Int) + 16 * (k : Int) = ((a + 16 * k : Nat) : Int) by push_cast; rfl, ea_rsp]

theorem off_lt (x p : Addr) (o n : Nat) (ho : o + n < 2 ^ 64) :
    (x - (p + BitVec.ofNat 64 o)).toNat < n ↔ o ≤ (x - p).toNat ∧ (x - p).toNat < o + n := by
  have e : (x - (p + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o = x - p := by bv_omega
  have e' := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)] at e'
  have h1 := (x - (p + BitVec.ofNat 64 o)).isLt
  have h2 := (x - p).isLt
  generalize (x - (p + BitVec.ofNat 64 o)).toNat = r at *
  generalize (x - p).toNat = d at *
  by_cases hc : r + o < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc] at e'; omega
  · rw [show r + o = (r + o - 2 ^ 64) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at e'
    omega

theorem writeW_zero128 (m : Mem) (a x : Addr) :
    m.writeW a (0 : BitVec 128) x = if (x - a).toNat < 16 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

theorem ite_t {p : Prop} [Decidable p] {α : Type} {a b : α} (h : p) : (if p then a else b) = a := by
  simp only [h, ↓reduceIte]

theorem ite_f {p : Prop} [Decidable p] {α : Type} {a b : α} (h : ¬ p) : (if p then a else b) = b := by
  simp only [h, ↓reduceIte]

/-- What `storesF v ks off base f k` zeroes, for `k ≤ f`, at offset `d` of `rsp`. -/
def SCov (ks : List Nat) (off base k d : Nat) : Prop :=
  base ≤ d ∧ d < base + 16 * k ∧ ks.contains (off + base + 16 * ((d - base) / 16)) = true

theorem writeW_zero (m : Mem) (a x : Addr) (w : Nat) :
    m.writeW a (0 : BitVec w) x = if (x - a).toNat < w / 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- What the wide stores read of `xmm0`, zero after the clearing: its low
128 bits, and above the level `sse` the rest of `zmm0`. -/
def X0 (v : VecLevel) (u : State) : Prop :=
  u.xmm .xmm0 = 0 ∧ (v ≠ .sse → u.ymmHi .xmm0 = 0 ∧ u.zmmHi .xmm0 = 0)

theorem span_le (v : VecLevel) (ks : List Nat) (o k : Nat) (hk : 0 < k) : span v ks o k ≤ k := by
  unfold span; split
  · omega
  · split
    · omega
    · split <;> omega

theorem span_cases (v : VecLevel) (ks : List Nat) (o k : Nat) :
    span v ks o k = 0 ∨ span v ks o k = 1 ∨ (span v ks o k = 2 ∧ v ≠ .sse) ∨
      (span v ks o k = 4 ∧ v = .evex) := by
  unfold span; split
  · rename_i h; exact .inr (.inr (.inr ⟨rfl, h.1⟩))
  · split
    · rename_i _ h; exact .inr (.inr (.inl ⟨rfl, h.1⟩))
    · split
      · exact .inr (.inl rfl)
      · exact .inl rfl

theorem span_zero {v : VecLevel} {ks : List Nat} {o k : Nat} (h : span v ks o k = 0) :
    ks.contains (o + 16 * (k - 1)) = false := by
  unfold span at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hc; simpa using hc

/-- Every granule a store zeroes is in `ks`. -/
theorem span_in {v : VecLevel} {ks : List Nat} {o k : Nat} (hk : 0 < k) :
    ∀ i, k - span v ks o k ≤ i → i < k → ks.contains (o + 16 * i) = true := by
  intro i h1 h2
  have hall : ∀ {j n : Nat}, allIn ks o j n = true → j ≤ i → i < j + n → ks.contains (o + 16 * i) = true :=
    fun {j n} ha hj hi => by
      have := List.all_eq_true.mp ha (i - j) (List.mem_range.mpr (by omega))
      rwa [show j + (i - j) = i by omega] at this
  unfold span at h1
  split at h1
  · rename_i hc; exact hall hc.2.2 (by omega) (by omega)
  · split at h1
    · rename_i _ hc; exact hall hc.2.2 (by omega) (by omega)
    · split at h1
      · rename_i _ _ hc; rwa [show i = k - 1 by omega]
      · omega

/-- A store of `n` granules zeroes them. -/
theorem zeroW_run (v : VecLevel) (n a b : Nat) (u : State) (hb : b < 2 ^ 64) (hR : ⟨u.gpr .rsp, b⟩ ∈ u.wr)
    (hab : a + 16 * n ≤ b) (hn : n = 1 ∨ (n = 2 ∧ v ≠ .sse) ∨ (n = 4 ∧ v = .evex)) (hx : X0 v u) :
    ∃ m', execBlock isa [zeroW v n a] u = some ({ u with mem := m' }, [.addr (u.gpr .rsp + BitVec.ofNat 64 a)]) ∧
      ∀ x, m' x = if a ≤ (x - u.gpr .rsp).toNat ∧ (x - u.gpr .rsp).toNat < a + 16 * n then 0 else u.mem x := by
  have hin : ∀ w, a + w ≤ b → InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 a) w := fun w hw => by
    refine ⟨_, hR, ?_⟩
    simp only [Region.Contains]
    rw [show u.gpr .rsp + BitVec.ofNat 64 a - u.gpr .rsp = BitVec.ofNat 64 a by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hm : ∀ (w : Nat), 16 * n = w / 8 → ∀ x, (u.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 a) (0 : BitVec w)) x =
      if a ≤ (x - u.gpr .rsp).toNat ∧ (x - u.gpr .rsp).toNat < a + 16 * n then 0 else u.mem x := fun w hw x => by
    simp only [writeW_zero, ← hw, off_lt _ _ _ _ (show a + 16 * n < 2 ^ 64 by omega)]
  obtain ⟨hx0, hy⟩ := hx
  rcases hn with rfl | ⟨rfl, hv⟩ | ⟨rfl, rfl⟩
  · refine ⟨_, ?_, hm 128 rfl⟩
    cases v
    all_goals
      simp only [zeroW, execBlock, isa, reduceExec, ea_rsp, State.store128, hin 16 (by omega), hx0,
        Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, ↓reduceIte]
  · obtain ⟨hy1, -⟩ := hy hv
    have hyz : u.ymm .xmm0 = 0 := by simp only [State.ymm, hx0, hy1]; exact BitVec.zero_append_zero
    refine ⟨_, ?_, hm 256 rfl⟩
    cases v
    · exact absurd rfl hv
    all_goals
      simp only [zeroW, execBlock, isa, reduceExec, ea_rsp, State.store256, hin 32 (by omega), hyz,
        Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, ↓reduceIte]
  · obtain ⟨hy1, hz1⟩ := hy (by decide)
    have hz : u.zmm .xmm0 = 0 := by
      simp only [State.zmm, State.ymm, hx0, hy1, hz1]
      exact (congrArg (fun y => (0 : BitVec 256) ++ y) BitVec.zero_append_zero).trans BitVec.zero_append_zero
    refine ⟨_, ?_, hm 512 rfl⟩
    simp only [zeroW, execBlock, isa, reduceExec, ea_rsp, State.store512, hin 64 (by omega), hz,
      Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, ↓reduceIte]

theorem storesF_run (v : VecLevel) (ks : List Nat) (off b base : Nat) (hb : b < 2 ^ 64) :
    ∀ (f k : Nat) (u : State), k ≤ f →
    ⟨u.gpr .rsp, b⟩ ∈ u.wr → (ks ≠ [] → X0 v u) → base + 16 * k ≤ b →
    ∃ m', execBlock isa (storesF v ks off base f k) u =
        some ({ u with mem := m' }, storesTr v ks off (u.gpr .rsp) base f k) ∧
      (∀ x, SCov ks off base k (x - u.gpr .rsp).toNat → m' x = 0) ∧
      (∀ x, ¬ SCov ks off base k (x - u.gpr .rsp).toNat → m' x = u.mem x)
  | 0, k, u, hk, _, _, _ => ⟨u.mem, by simp [storesF, storesTr, execBlock], fun _ h => absurd h.2.1 (by have := h.1; omega),
      fun _ _ => rfl⟩
  | _ + 1, 0, u, _, _, _, _ => ⟨u.mem, by simp [storesF, storesTr, execBlock],
      fun _ h => absurd h.2.1 (by have := h.1; omega), fun _ _ => rfl⟩
  | f + 1, k + 1, u, hk, hR, hx, hkb => by
    have hle := span_le v ks (off + base) (k + 1) (by omega)
    have hzero := @span_zero v ks (off + base) (k + 1)
    have hin := @span_in v ks (off + base) (k + 1) (by omega)
    have hcs := span_cases v ks (off + base) (k + 1)
    simp only [storesF, storesTr]
    generalize span v ks (off + base) (k + 1) = n at hle hzero hin hcs ⊢
    by_cases hn : n = 0
    · subst hn
      have hc := hzero rfl
      obtain ⟨m', he, hz, hu⟩ := storesF_run v ks off b base hb f k u (by omega) hR hx (by omega)
      refine ⟨m', ?_, fun x h => ?_, fun x h => ?_⟩
      · simp only [↓reduceIte, List.nil_append, show k + 1 - max 0 1 = k by omega, he]
      · obtain ⟨h1, h2, h3⟩ := h
        by_cases hc' : (x - u.gpr .rsp).toNat < base + 16 * k
        · exact hz x ⟨h1, hc', h3⟩
        · rw [show ((x - u.gpr .rsp).toNat - base) / 16 = k by omega] at h3
          rw [show k + 1 - 1 = k by omega] at hc
          rw [hc] at h3; cases h3
      · exact hu x fun h' => h ⟨h'.1, by have := h'.2.1; omega, h'.2.2⟩
    · have hne : ks ≠ [] := fun e => by have := hin k (by omega) (by omega); rw [e] at this; cases this
      have hn' : n = 1 ∨ (n = 2 ∧ v ≠ .sse) ∨ (n = 4 ∧ v = .evex) := hcs.resolve_left hn
      obtain ⟨m₁, he₁, hm₁⟩ := zeroW_run v n (base + 16 * (k + 1 - n)) b u hb hR (by omega) hn' (hx hne)
      let u₁ : State := { u with mem := m₁ }
      obtain ⟨m', he, hz, hu⟩ := storesF_run v ks off b base hb f (k + 1 - n) u₁ (by omega) hR
        (fun h => hx h) (by omega)
      refine ⟨m', ?_, fun x h => ?_, fun x h => ?_⟩
      · rw [show max n 1 = n by omega, ite_f hn, execBlock_append, he₁]
        simp only [Option.bind_some]
        rw [show ({ u with mem := m₁ } : State) = u₁ from rfl, he]
        simp [u₁, hn]
      · obtain ⟨h1, h2, h3⟩ := h
        by_cases hc : (x - u.gpr .rsp).toNat < base + 16 * (k + 1 - n)
        · exact hz x ⟨h1, hc, h3⟩
        · rw [hu x (fun h' => hc h'.2.1), show u₁.mem x = m₁ x from rfl, hm₁ x, ite_t ⟨by omega, by omega⟩]
      · have hk' : ¬ SCov ks off base (k + 1 - n) (x - u.gpr .rsp).toNat :=
          fun h' => h ⟨h'.1, by have := h'.2.1; omega, h'.2.2⟩
        rw [hu x hk', show u₁.mem x = m₁ x from rfl, hm₁ x, ite_f fun hg => h ⟨by omega, by omega, by
          exact hin _ (by omega) (by omega)⟩]

theorem writeW_zero64 (m : Mem) (a x : Addr) :
    m.writeW a (0 : BitVec 64) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- What `chunkStores v ks off b` zeroes, at offset `d` of `rsp`. -/
def CCov (ks : List Nat) (off b d : Nat) : Prop := d < b ∧ covC ks off b d = true

theorem chunk_run (v : VecLevel) (ks : List Nat) (off b : Nat) (hb : b < 2 ^ 64) (h8 : b % 8 = 0) (u : State)
    (hR : ⟨u.gpr .rsp, b⟩ ∈ u.wr) (hx : ks ≠ [] → X0 v u) (hr : ks ≠ [] → u.gpr .r11 = 0) :
    ∃ m', execBlock isa (chunkStores v ks off b) u = some ({ u with mem := m' }, chunkTr v ks off (u.gpr .rsp) b) ∧
      (∀ x, CCov ks off b (x - u.gpr .rsp).toNat → m' x = 0) ∧
      (∀ x, ¬ CCov ks off b (x - u.gpr .rsp).toNat → m' x = u.mem x) := by
  obtain ⟨m₁, he, hz, hu⟩ := storesF_run v ks off b (b % 16) hb (b / 16) (b / 16) u (Nat.le_refl _) hR hx (by omega)
  have hbb : b % 16 + 16 * (b / 16) = b := by omega
  -- `SCov` within the chunk is `CCov` above its 8-byte granule.
  have hsc : ∀ d, SCov ks off (b % 16) (b / 16) d ↔ b % 16 ≤ d ∧ CCov ks off b d := by
    intro d
    simp only [SCov, CCov, covC, hbb]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by simp only [show ¬ d < b % 16 by omega, ↓reduceIte]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩; simp only [show ¬ d < b % 16 by omega, ↓reduceIte] at h3; exact ⟨h1, h2, h3⟩
  unfold chunkStores store8s
  rw [execBlock_append, he]
  by_cases h16 : (b % 16 = 8 && ks.contains off) = true
  · have h0 : BitVec.ofInt 64 0 = 0 := rfl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h16
    have hr := hr (fun h => by have := h16.2; rw [h] at this; cases this)
    have hin8 : InRegions u.wr (u.gpr .rsp) 8 := by
      refine ⟨_, hR, ?_⟩; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    have hea : u.gpr .rsp + BitVec.ofInt 64 0 = u.gpr .rsp := by rw [h0]; bv_omega
    refine ⟨m₁.writeW (u.gpr .rsp) (u.gpr .r11), ?_, fun x h => ?_, fun x h => ?_⟩
    · simp only [h16, decide_true, Bool.and_self, ↓reduceIte, Option.bind_some, execBlock, isa, reduceExec,
        State.store64, State.ea, hea, hin8]
      simp [chunkTr, addrs, State.ea, h16, List.contains_iff_mem.mp h16.2]
    · rw [hr, writeW_zero64]
      split
      · rfl
      · exact hz x ((hsc _).mpr ⟨by omega, h⟩)
    · rw [hr, writeW_zero64]
      split
      · exact absurd ⟨by omega, by
          unfold covC; rw [h16.1]
          simp only [show (x - u.gpr .rsp).toNat < 8 by omega, ↓reduceIte, beq_self_eq_true, h16.2,
            Bool.and_self]⟩ h
      · exact hu x fun h' => h ((hsc _).mp h').2
  · refine ⟨m₁, ?_, fun x h => ?_, fun x h => hu x fun h' => h ((hsc _).mp h').2⟩
    · have h16' : ¬ (b % 16 = 8 ∧ off ∈ ks) := fun ⟨a, c⟩ => h16 (by simp [a, c])
      simp [h16', chunkTr, execBlock]
    · by_cases hd : (x - u.gpr .rsp).toNat < b % 16
      · obtain ⟨-, h2⟩ := h
        simp only [covC, hd, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h2
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h16
        exact absurd h2.2 (by simpa using h16 h2.1)
      · exact hz x ((hsc _).mpr ⟨by omega, h⟩)

theorem below_split (p : Addr) (b n : Nat) (h : b + n ≤ p.toNat) (x : Addr) :
    (⟨p - BitVec.ofNat 64 (b + n), b + n⟩ : Region).Contains x 1 ↔
      (x - (p - BitVec.ofNat 64 b)).toNat < b ∨
        (⟨p - BitVec.ofNat 64 b - BitVec.ofNat 64 n, n⟩ : Region).Contains x 1 := by
  have hp := p.isLt
  have hx := x.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_ofNat]
  generalize p.toNat = P at *
  generalize x.toNat = X at *
  rw [Nat.mod_eq_of_lt (a := b + n) (by omega), Nat.mod_eq_of_lt (a := b) (by omega),
    Nat.mod_eq_of_lt (a := n) (by omega)]
  omega

/-- The offsets of `x` from the bottom of a frame of `b` bytes below `p` and
of the `n` bytes below that. -/
theorem below_idx (p : Addr) (b n : Nat) (h : b + n ≤ p.toNat) (x : Addr) :
    (x - (p - BitVec.ofNat 64 b - BitVec.ofNat 64 n)).toNat = (x - (p - BitVec.ofNat 64 (b + n))).toNat ∧
      (n ≤ (x - (p - BitVec.ofNat 64 (b + n))).toNat →
        (x - (p - BitVec.ofNat 64 b)).toNat = (x - (p - BitVec.ofNat 64 (b + n))).toNat - n) ∧
      ((x - (p - BitVec.ofNat 64 b)).toNat < b →
        (x - (p - BitVec.ofNat 64 (b + n))).toNat = n + (x - (p - BitVec.ofNat 64 b)).toNat) := by
  have hp := p.isLt
  have hx := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  generalize p.toNat = P at *
  generalize x.toNat = X at *
  rw [Nat.mod_eq_of_lt (a := b + n) (by omega), Nat.mod_eq_of_lt (a := b) (by omega),
    Nat.mod_eq_of_lt (a := n) (by omega)]
  refine ⟨by congr 1; omega, fun h' => by omega, fun h' => by omega⟩

/-- What `wipe v ks cs` from `rsp = p` zeroes. -/
def WCov (ks cs : List Nat) (p x : Addr) : Prop :=
  (⟨p - BitVec.ofNat 64 cs.sum, cs.sum⟩ : Region).Contains x 1 ∧
    cov ks cs (x - (p - BitVec.ofNat 64 cs.sum)).toNat = true

/-- The trace of `wipe v ks cs` from `rsp = p`. -/
def wipeTr (v : VecLevel) (ks : List Nat) : List Nat → Addr → List Leak
  | [], _ => []
  | b :: bs, p => chunkTr v ks bs.sum (p - BitVec.ofNat 64 b) b ++ wipeTr v ks bs (p - BitVec.ofNat 64 b)

theorem wipe_run (v : VecLevel) (ks : List Nat) : ∀ (cs : List Nat) (u : State), (∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) →
    cs.sum ≤ (u.gpr .rsp).toNat → (ks ≠ [] → X0 v u) → (ks ≠ [] → u.gpr .r11 = 0) →
    ∃ m', Exec isa (wipe v ks cs) u (wipeTr v ks cs (u.gpr .rsp)) { u with mem := m' } ∧
      (∀ x, WCov ks cs (u.gpr .rsp) x → m' x = 0) ∧ (∀ x, ¬ WCov ks cs (u.gpr .rsp) x → m' x = u.mem x)
  | [], u, _, _, _, _ =>
    ⟨u.mem, .block rfl, fun x h => by simp [WCov, cov] at h, fun _ _ => rfl⟩
  | b :: bs, u, hv, hs, hx, hr => by
    obtain ⟨hb0, hb4, hb8⟩ := hv b (List.mem_cons_self ..)
    simp only [List.sum_cons] at hs
    let p := u.gpr .rsp
    let q := p - BitVec.ofNat 64 b
    let u₁ : State := { u.setReg .rsp q with wr := ⟨q, b⟩ :: u.wr }
    have hpush : isa.push (.alloc b) u = some u₁ := by
      simp only [isa, push, u₁, q, p]; rw [ite_eq_left ⟨hb0, hb4, hb8, by omega⟩]
    have hq : u₁.gpr .rsp = q := by simp [u₁, State.setReg]
    obtain ⟨m₁, he₁, hz₁, hu₁⟩ := chunk_run v ks bs.sum b (by omega) hb8 u₁ (by rw [hq]; simp [u₁])
      (fun h => hx h) (by simpa [u₁, State.setReg] using hr)
    let u₂ : State := { u₁ with mem := m₁ }
    have hqn : bs.sum ≤ q.toNat := by
      have := p.isLt
      have h' : b + bs.sum ≤ p.toNat := hs
      simp only [q, BitVec.toNat_sub, BitVec.toNat_ofNat]
      generalize p.toNat = P at *
      rw [Nat.mod_eq_of_lt (a := b) (by omega)]
      omega
    obtain ⟨m₂, he₂, hz₂, hu₂⟩ := wipe_run v ks bs u₂ (fun b' h => hv b' (List.mem_cons_of_mem _ h))
      (by simpa [u₂, hq] using hqn) (fun h => hx h)
      (by simpa [u₂, u₁, State.setReg] using hr)
    have hpop : isa.pop (.free b) u₁ { u₂ with mem := m₂ } = some { u with mem := m₂ } := by
      simp only [isa, pop, u₂]
      split
      rotate_left
      · rename_i hn; exact (hn ⟨hb0, hb4, hb8, trivial, trivial, by simp [u₁, State.setReg]⟩).elim
      congr 1
      simp only [u₁, State.setReg, State.mk.injEq, and_true, List.tail_cons]
      funext r
      by_cases h : r = .rsp
      · subst h; simp [q, p, BitVec.sub_add_cancel]
      · simp [h]
    refine ⟨m₂, ?_, fun x hx' => ?_, fun x hx' => ?_⟩
    · have e := Exec.frame (M := isa) hpush (.seq (.block he₁) he₂) hpop
      have htr : wipeTr v ks (b :: bs) p = (isa.addrs (.alloc b) u).map Leak.addr ++
          (chunkTr v ks bs.sum (u₁.gpr .rsp) b ++ wipeTr v ks bs (u₂.gpr .rsp)) ++
          (isa.addrs (.free b) { u₂ with mem := m₂ }).map Leak.addr := by
        simp [wipeTr, addrs, u₂, hq, q]
      rw [htr]; exact e
    all_goals
      have hs' : b + bs.sum ≤ p.toNat := hs
      have hsplit := below_split p b bs.sum hs' x
      obtain ⟨hi1, hi2, hi3⟩ := below_idx p b bs.sum hs' x
      replace hi1 : (x - (q - BitVec.ofNat 64 bs.sum)).toNat = (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat := hi1
      replace hi2 : bs.sum ≤ (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat →
        (x - q).toNat = (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat - bs.sum := hi2
      replace hi3 : (x - q).toNat < b →
        (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat = bs.sum + (x - q).toNat := hi3
      replace hsplit : _ ↔ (x - q).toNat < b ∨ (⟨q - BitVec.ofNat 64 bs.sum, bs.sum⟩ : Region).Contains x 1 := hsplit
      have e₂ : u₂.gpr .rsp = q := hq
      have hz₂ := hz₂ x
      have hu₂ := hu₂ x
      have hz₁ := hz₁ x
      have hu₁ := hu₁ x
      simp only [WCov, List.sum_cons, e₂, hq, Region.Contains, CCov] at hx' hz₂ hu₂ hz₁ hu₁ hsplit ⊢
      rw [hi1] at hz₂ hu₂ hsplit
      generalize (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat = I at hi2 hi3 hsplit hx' hz₂ hu₂
    · -- Zeroed.
      obtain ⟨h1, h2⟩ := hx'
      try simp only [cov] at h2
      by_cases hlt : I < bs.sum
      · simp only [hlt, ↓reduceIte] at h2
        exact hz₂ ⟨by omega, h2⟩
      · simp only [hlt, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h2
        rw [hu₂ (fun h => by omega)]
        exact hz₁ ⟨by rw [hi2 (by omega)]; omega, by rw [hi2 (by omega)]; exact h2.2⟩
    · -- Kept.
      rw [hu₂ (fun ⟨h1, h2⟩ => hx' ⟨by omega, by simp only [cov, show I < bs.sum by omega, ↓reduceIte]; exact h2⟩)]
      exact hu₁ (fun ⟨h1, h2⟩ => hx' ⟨by rw [hi3 h1]; omega, by
        simp only [cov, hi3 h1, show ¬ (bs.sum + (x - q).toNat < bs.sum) by omega, ↓reduceIte,
          Nat.add_sub_cancel_left, h1, decide_true, Bool.true_and]
        exact h2⟩)

/-! ## Clearing the registers -/

/-- The state after zeroing the SSE registers `xs` at level `v`. -/
def clearedV (v : VecLevel) (xs : List XReg) (s : State) : State :=
  { s with
    xmm := fun x => if x ∈ xs then 0 else s.xmm x
    ymmHi := fun x => if v ≠ .sse ∧ x ∈ xs then 0 else s.ymmHi x
    zmmHi := fun x => if v ≠ .sse ∧ x ∈ xs then 0 else s.zmmHi x }

theorem execBlock_vecs (v : VecLevel) (xs : List XReg) (s : State) :
    execBlock isa (xs.map (zeroX v)) s = some (clearedV v xs s, []) := by
  induction xs generalizing s with
  | nil => simp [execBlock, clearedV]
  | cons x xs ih =>
    cases v
    all_goals
      simp only [List.map_cons, execBlock, zeroX, isa, reduceExec, ih, Option.map_some, addrs,
        List.map_nil, List.nil_append]
      simp only [clearedV, XOp.exec, VOp.exec, State.setXmm, State.setV, XBinOp.eval, VBinOp.sse,
        BitVec.xor_self, List.mem_cons, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [State.mk.injEq, true_and, and_true]
      first
        | (funext y; by_cases h1 : y = x <;> by_cases h2 : y ∈ xs <;> simp [h1, h2])
        | (refine ⟨?_, ?_, ?_⟩ <;> funext y <;> by_cases h1 : y = x <;> by_cases h2 : y ∈ xs <;>
            simp [h1, h2])

/-- The state after `clearHigh v`: at the level `evex`, `zmm16`–`zmm31` zero. -/
def clearedH (v : VecLevel) (s : State) : State :=
  match v with
  | .evex => { s with ymmH := fun _ => 0, zmmHiH := fun _ => 0 }
  | _ => s

theorem mem_hregs (h : HReg) : h ∈ hregs := by cases h <;> decide

theorem execBlock_zeroH (hs : List HReg) (s : State) :
    execBlock isa (hs.map zeroH) s = some ({ s with
      ymmH := fun h => if h ∈ hs then 0 else s.ymmH h
      zmmHiH := fun h => if h ∈ hs then 0 else s.zmmHiH h }, []) := by
  induction hs generalizing s with
  | nil => simp [execBlock]
  | cons h hs ih =>
    simp only [List.map_cons, execBlock, zeroH, isa, reduceExec, ih, Option.map_some, addrs,
      List.map_nil, List.nil_append]
    simp only [E5Op.exec, State.setVz, State.setZH, EBinOp.sse, XBinOp.eval, BitVec.xor_self, List.mem_cons,
      Option.some.injEq, Prod.mk.injEq, and_true]
    simp only [State.mk.injEq, true_and, and_true]
    refine ⟨?_, ?_⟩ <;> funext y <;> by_cases h1 : y = h <;> by_cases h2 : y ∈ hs <;> simp [h1, h2]

theorem execBlock_high (v : VecLevel) (s : State) :
    execBlock isa (clearHigh v) s = some (clearedH v s, []) := by
  cases v
  · rfl
  · rfl
  · rw [clearHigh, execBlock_zeroH]
    simp only [clearedH, mem_hregs, ↓reduceIte]

/-- The state after zeroing the general-purpose registers `rs` with `xor`. -/
def clearedG (rs : List Reg) (s : State) : State :=
  { s with
    gpr := fun r => if r ∈ rs then 0 else s.gpr r
    cf := some false, of := some false, zf := some true, sf := some false }

theorem execBlock_gprs (rs : List Reg) (hrs : rs ≠ []) (s : State) :
    execBlock isa (rs.map zeroR) s = some (clearedG rs s, []) := by
  induction rs generalizing s with
  | nil => exact absurd rfl hrs
  | cons r rs ih =>
    simp only [List.map_cons, execBlock, zeroR, isa, reduceExec, addrs, srcAddrs, execAlu32, readSrc32,
      Option.bind_some, BitVec.xor_self, List.map_nil, List.nil_append]
    by_cases hn : rs = []
    · subst hn
      simp only [List.map_nil, execBlock, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg, List.mem_singleton]
      simp
    · rw [ih hn]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg, List.mem_cons]
      simp only [State.mk.injEq, and_true]
      funext y; by_cases h1 : y = r <;> by_cases h2 : y ∈ rs <;> simp [h1, h2]

/-- What `retFix retBits` leaves in `rax`. -/
def retVal (retBits : Nat) (x : BitVec 64) : BitVec 64 :=
  if retBits = 0 then 0
  else if retBits < 32 then ((x.setWidth 32) &&& BitVec.ofNat 32 (2 ^ retBits - 1)).setWidth 64
  else if retBits = 32 then (x.setWidth 32).setWidth 64
  else x

/-- `rs` cleared, if any (`execBlock` of no instruction leaves the flags). -/
def clearedP (rs : List Reg) (s : State) : State := if rs = [] then s else clearedG rs s

theorem execBlock_gprsP (rs : List Reg) (s : State) :
    execBlock isa (rs.map zeroR) s = some (clearedP rs s, []) := by
  by_cases h : rs = []
  · subst h; simp [execBlock, clearedP]
  · rw [execBlock_gprs rs h]; simp [clearedP, h]

theorem execBlock_clearGpr (rb : Nat) (gs : List Reg) (hgs : gs ≠ []) (hax : .rax ∉ gs) (s : State) :
    execBlock isa (retFix rb ++ gs.map zeroR) s =
      some (clearedG gs (s.setReg .rax (retVal rb (s.gpr .rax))), []) := by
  unfold retFix retVal
  by_cases h0 : rb = 0
  · simp only [h0, ↓reduceIte, List.singleton_append]
    rw [show zeroR .rax :: gs.map zeroR = (Reg.rax :: gs).map zeroR from rfl,
      execBlock_gprs _ (by simp)]
    simp only [clearedG, State.setReg, Option.some.injEq, Prod.mk.injEq, and_true, State.mk.injEq]
    funext r; by_cases hr : r = .rax
    · subst hr; simp [hax]
    · simp [hr]
  by_cases h1 : rb < 32
  · simp only [h0, h1, ↓reduceIte, List.singleton_append, execBlock, isa, reduceExec, execAlu32, readSrc32,
      Option.bind_some, addrs, srcAddrs, execBlock_gprs _ hgs, Option.map_some, List.map_nil,
      List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
    simp only [clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg]
    try (funext r; by_cases hr : r = .rax <;> simp [hr, hax])
  by_cases h2 : rb = 32
  · subst h2
    simp only [h0, h1, ↓reduceIte, List.singleton_append, execBlock, isa, reduceExec, readSrc32,
      Option.map_some, addrs, srcAddrs, execBlock_gprs _ hgs, List.map_nil,
      List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
    simp only [clearedG, State.setReg32, State.setReg]
    try (funext r; by_cases hr : r = .rax <;> simp [hr, hax])
  · simp only [h0, h1, h2, ↓reduceIte, List.nil_append, execBlock_gprs _ hgs, Option.some.injEq,
      Prod.mk.injEq, and_true]
    simp only [clearedG, State.setReg, State.mk.injEq, and_true]
    funext r; by_cases hr : r = .rax
    · subst hr; simp [hax]
    · simp [hr]

/-! ## MXCSR -/

/-- MXCSR after `mxFix v`. -/
def fixMx (v : VecLevel) (x : BitVec 32) : BitVec 32 :=
  match v with
  | .evex => x &&& 0xFFC0
  | _ => x

/-- The trace of `mxFix v` from `rsp = p`. -/
def mxTr (v : VecLevel) (p : Addr) : List Leak :=
  match v with
  | .evex => [.addr (p - 16#64), .addr (p - 16#64), .addr (p - 16#64), .addr (p - 16#64 + 4#64),
      .addr (p - 16#64 + 4#64), .addr (p - 16#64)]
  | _ => []

theorem ctl_hi (x : BitVec 32) : (x &&& 0xFFC0#32).extractLsb' 16 16 = 0 := by
  rw [BitVec.extractLsb'_and, show (0xFFC0#32).extractLsb' 16 16 = 0#16 by decide]
  exact BitVec.and_zero

/-- `mxFix` keeps MXCSR's control bits. -/
theorem fixMx_ctl (v : VecLevel) (x : BitVec 32) : (fixMx v x).extractLsb' 6 10 = x.extractLsb' 6 10 := by
  cases v
  · rfl
  · rfl
  · show (x &&& 0xFFC0#32).extractLsb' 6 10 = _
    rw [BitVec.extractLsb'_and, show (0xFFC0#32).extractLsb' 6 10 = BitVec.allOnes 10 by decide, BitVec.and_allOnes]

/-- What it leaves is a function of them. -/
theorem fixMx_congr (v : VecLevel) {x y : BitVec 32} (hv : v = .evex)
    (h : x.extractLsb' 6 10 = y.extractLsb' 6 10) : fixMx v x = fixMx v y := by
  subst hv
  show x &&& 0xFFC0#32 = y &&& 0xFFC0#32
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  by_cases hc : (0xFFC0#32).getLsbD i = true
  · have h6 : 6 ≤ i ∧ i < 16 := by
      have : ∀ i < 32, (0xFFC0#32).getLsbD i = true → 6 ≤ i ∧ i < 16 := by decide
      exact this i hi hc
    have e := congrArg (fun z : BitVec 10 => z.getLsbD (i - 6)) h
    simp only [BitVec.getLsbD_extractLsb', show i - 6 < 10 by omega, decide_true, Bool.true_and,
      show 6 + (i - 6) = i by omega] at e
    rw [e]
  · simp only [Bool.not_eq_true] at hc
    rw [hc, Bool.and_false, Bool.and_false]

/-- `mxFix v`, where `r11` is zero and the flags are those of an `xor` of a
register with itself (what clearing `ps` leaves): MXCSR as `fixMx` says, and
at the level `evex` 8 bytes of the 16 below the stack pointer. -/
theorem mxFix_run (v : VecLevel) (u : State) (h16 : v = .evex → 16 ≤ (u.gpr .rsp).toNat)
    (hr : v = .evex → u.gpr .r11 = 0 ∧ u.cf = some false ∧ u.of = some false ∧ u.zf = some true ∧
      u.sf = some false) :
    ∃ m', Exec isa (mxFix v) u (mxTr v (u.gpr .rsp)) { u with mem := m', mxcsr := fixMx v u.mxcsr } ∧
      ∀ x, ¬ (v = .evex ∧ (x - (u.gpr .rsp - 16#64)).toNat < 8) → m' x = u.mem x := by
  cases v
  · exact ⟨u.mem, .block rfl, fun _ _ => rfl⟩
  · exact ⟨u.mem, .block rfl, fun _ _ => rfl⟩
  · obtain ⟨h0, hcf, hof, hzf, hsf⟩ := hr rfl
    have h16 := h16 rfl
    let p := u.gpr .rsp
    let q := p - 16#64
    let u₁ : State := { u.setReg .rsp q with wr := ⟨q, 16⟩ :: u.wr }
    have hpush : isa.push (.alloc 16) u = some u₁ := by
      simp only [isa, push, u₁, q, p]
      rw [ite_eq_left ⟨by decide, by decide, by decide, h16⟩]
    have hq : u₁.gpr .rsp = q := by simp [u₁, State.setReg]
    have hin : InRegions u₁.wr q 4 := by
      refine ⟨⟨q, 16⟩, by simp [u₁], ?_⟩
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    have hin' : InRegions (u₁.rd ++ u₁.wr) q 4 := by
      obtain ⟨r, hr, hc⟩ := hin; exact ⟨r, List.mem_append_right _ hr, hc⟩
    have hea : u₁.gpr .rsp + BitVec.ofInt 64 0 = q := by rw [hq]; show q + 0#64 = q; rw [BitVec.add_zero]
    let w : BitVec 32 := u.mxcsr &&& 0xFFC0#32
    let m₂ : Mem := ((u.mem.writeW q u.mxcsr).writeW q w).writeW (q + 4#64) (0x1FBF#32)
    have hw : w.extractLsb' 16 16 = 0 := ctl_hi _
    have hin4 : InRegions u₁.wr (q + 4#64) 4 := by
      refine ⟨⟨q, 16⟩, by simp [u₁], ?_⟩
      simp only [Region.Contains]
      bv_omega
    have hin4' : InRegions (u₁.rd ++ u₁.wr) (q + 4#64) 4 := by
      obtain ⟨r, hr, hc⟩ := hin4; exact ⟨r, List.mem_append_right _ hr, hc⟩
    have hea4 : u₁.gpr .rsp + BitVec.ofInt 64 4 = q + 4#64 := by rw [hq]; rfl
    have hsep : Mem.Sep q (32 / 8) (q + 4#64) (32 / 8) := by
      intro x hx
      have hx : (x - q).toNat < 4 := hx
      show ¬ (x - (q + 4#64)).toNat < 4
      bv_omega
    have hb : execBlock isa [.stmxcsr { base := .rsp }, .mov32 .r11 (.mem { base := .rsp }),
        .alu32 .and .r11 (.imm 0xFFC0), .store32 { base := .rsp } .r11,
        .mov32 .r11 (.imm 0x1FBF), .store32 { base := .rsp, disp := 4 } .r11,
        .ldmxcsr { base := .rsp, disp := 4 }, .lfence, .lfence, .ldmxcsr { base := .rsp },
        .alu32 .xor .r11 (.reg .r11)] u₁ =
        some ({ u₁ with mem := m₂, mxcsr := w },
          [.addr q, .addr q, .addr q, .addr (q + 4#64), .addr (q + 4#64), .addr q]) := by
      have h11 : u₁.gpr .r11 = 0 := by simp [u₁, State.setReg, h0]
      have sw : ∀ x : BitVec 32, (x.setWidth 64).setWidth 32 = x := fun x => by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth]
        have := x.isLt
        omega
      simp only [execBlock, isa, reduceExec, State.store32, State.load32, State.ea, execAlu32, readSrc32, addrs,
        srcAddrs, arithFlags, State.setFlags, State.setReg32, State.setReg, reduceCtorEq, ↓reduceIte, hea, hea4,
        hin, hin', hin4, hin4', Option.bind_some, Option.map_some, Mem.readW_writeW_self32,
        Mem.readW_writeW_sep hsep (by decide), sw, BitVec.xor_self,
        show u₁.mxcsr = u.mxcsr from rfl, show u₁.mem = u.mem from rfl,
        show (u.mxcsr &&& 65472).extractLsb' 16 16 = 0 from hw,
        show (8127 : BitVec 32).extractLsb' 16 16 = 0 from by decide,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [State.mk.injEq, and_true, true_and]
      refine ⟨?_, hcf.symm, ?_, ?_, hof.symm, rfl, rfl⟩
      · funext r
        by_cases hr : r = .r11
        · subst hr; rw [ite_eq_left rfl, h11]; rfl
        · rw [ite_eq_right hr, ite_eq_right hr, ite_eq_right hr, ite_eq_right hr]
      · exact hzf.symm
      · exact hsf.symm
    let u₂ : State := { u₁ with mem := m₂, mxcsr := w }
    have hpop : isa.pop (.free 16) u₁ u₂ = some { u with mem := m₂, mxcsr := w } := by
      simp only [isa, pop, u₂]
      split
      rotate_left
      · rename_i hn; exact (hn ⟨by decide, by decide, by decide, trivial, trivial, by simp [u₁, State.setReg]⟩).elim
      congr 1
      simp only [u₁, State.setReg, State.mk.injEq, and_true, List.tail_cons]
      funext r
      by_cases h : r = .rsp
      · subst h; simp [q, p, BitVec.sub_add_cancel]
      · simp [h]
    refine ⟨m₂, ?_, fun x hx => ?_⟩
    · have e := Exec.frame (M := isa) hpush (.block hb) hpop
      have htr : mxTr .evex p = (isa.addrs (.alloc 16) u).map Leak.addr ++
          [.addr q, .addr q, .addr q, .addr (q + 4#64), .addr (q + 4#64), .addr q] ++
          (isa.addrs (.free 16) u₂).map Leak.addr := by
        simp [mxTr, addrs, q]
      rw [show mxTr .evex (u.gpr .rsp) = mxTr .evex p from rfl, htr]
      exact e
    · have hx' : ¬ (x - q).toNat < 8 := fun h => hx ⟨rfl, h⟩
      have hx4 : ¬ (x - (q + 4#64)).toNat < 4 := by bv_omega
      show (((u.mem.writeW q u.mxcsr).writeW q w).writeW (q + 4#64) (0x1FBF#32)) x = u.mem x
      simp only [Mem.writeW, Mem.write]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The state `scrubTail v rb xs ps gs ks cs` leaves, given the memory `m'` its wipe leaves. -/
def finState (v : VecLevel) (rb : Nat) (xs : List XReg) (ps gs : List Reg) (m' : Mem) (u : State) : State :=
  clearedG gs
    (({ clearedP ps (clearedH v (clearedV v xs u)) with mem := m', mxcsr := fixMx v u.mxcsr } : State).setReg .rax
      (retVal rb (u.gpr .rax)))

theorem mem_xregs (x : XReg) : x ∈ xregs := by cases x <;> decide

/-- What `scrubTail` needs of what it clears. -/
structure TailOk (rb : Nat) (xs : List XReg) (ps gs : List Reg) (ks : List Nat) : Prop where
  x0 : ks ≠ [] → .xmm0 ∈ xs
  r11 : ks ≠ [] → .r11 ∈ ps
  psOk : ∀ r ∈ ps, r ∈ scratchRegs
  gsOk : ∀ r ∈ gs, r ∈ scratchRegs
  gne : gs ≠ []

/-- What the level `evex` needs of the wipe from `rsp = p`: that it zeroes
the bytes `mxFix` stores, in the 16 below the stack pointer. -/
def EvexOk (v : VecLevel) (ks cs : List Nat) (p : Addr) : Prop :=
  v = .evex → ks ≠ [] ∧ 16 ≤ cs.sum ∧ ∀ x, (x - (p - 16#64)).toNat < 8 → WCov ks cs p x

/-- The trace of `scrubTail` from `rsp = p`. -/
def tailTr (v : VecLevel) (ks cs : List Nat) (p : Addr) : List Leak := mxTr v p ++ wipeTr v ks cs p

theorem tail_run (v : VecLevel) (rb : Nat) {xs : List XReg} {ps gs : List Reg} {ks : List Nat} (cs : List Nat)
    (ht : TailOk rb xs ps gs ks) (u : State)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) (hs : cs.sum ≤ (u.gpr .rsp).toNat)
    (hev : EvexOk v ks cs (u.gpr .rsp)) :
    ∃ m', Exec isa (scrubTail v rb xs ps gs ks cs) u (tailTr v ks cs (u.gpr .rsp)) (finState v rb xs ps gs m' u) ∧
      (∀ x, WCov ks cs (u.gpr .rsp) x → m' x = 0) ∧ (∀ x, ¬ WCov ks cs (u.gpr .rsp) x → m' x = u.mem x) := by
  let u₁ := clearedP ps (clearedH v (clearedV v xs u))
  have h₁ : execBlock isa (xs.map (zeroX v) ++ clearHigh v ++ ps.map zeroR) u = some (u₁, []) := by
    rw [execBlock_append, execBlock_append, execBlock_vecs]
    simp only [Option.bind_some]
    rw [execBlock_high]
    simp only [Option.bind_some, Option.map_some]
    rw [execBlock_gprsP]
    rfl
  have hcH : ∀ w : State, (clearedH v w).gpr = w.gpr ∧ (clearedH v w).xmm = w.xmm ∧ (clearedH v w).mem = w.mem ∧
      (clearedH v w).mxcsr = w.mxcsr := fun w => by cases v <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hsp : u₁.gpr .rsp = u.gpr .rsp := by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).1]; rfl
    · simp only [clearedG, show Reg.rsp ∉ ps from fun h => absurd (ht.psOk _ h) (by decide : Reg.rsp ∉ scratchRegs),
        ↓reduceIte]
      rw [(hcH _).1]; rfl
  have hx0 : ks ≠ [] → X0 v u₁ := fun h => by
    have hw : ∀ w : State, (clearedP ps (clearedH v w)).xmm = w.xmm ∧ (clearedP ps (clearedH v w)).ymmHi = w.ymmHi ∧
        (clearedP ps (clearedH v w)).zmmHi = w.zmmHi := fun w => by
      unfold clearedP; split <;> cases v <;> exact ⟨rfl, rfl, rfl⟩
    obtain ⟨e1, e2, e3⟩ := hw (clearedV v xs u)
    refine ⟨?_, fun hv => ⟨?_, ?_⟩⟩
    · show (clearedP ps (clearedH v (clearedV v xs u))).xmm .xmm0 = 0
      rw [e1]; simp [clearedV, ht.x0 h]
    · show (clearedP ps (clearedH v (clearedV v xs u))).ymmHi .xmm0 = 0
      rw [e2]; simp [clearedV, ht.x0 h, hv]
    · show (clearedP ps (clearedH v (clearedV v xs u))).zmmHi .xmm0 = 0
      rw [e3]; simp [clearedV, ht.x0 h, hv]
  have hr11 : ks ≠ [] → u₁.gpr .r11 = 0 := fun h => by
    simp only [u₁, clearedP]; split
    · rename_i hp; exact absurd (ht.r11 h) (by rw [hp]; simp)
    · simp [clearedG, ht.r11 h]
  have hmem : u₁.mem = u.mem := by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).2.2.1]; rfl
    · show (clearedH v (clearedV v xs u)).mem = u.mem
      rw [(hcH _).2.2.1]; rfl
  have hmx : u₁.mxcsr = u.mxcsr := by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).2.2.2]; rfl
    · show (clearedH v (clearedV v xs u)).mxcsr = u.mxcsr
      rw [(hcH _).2.2.2]; rfl
  -- `mxFix`.
  obtain ⟨m₁, hem, hm₁⟩ := mxFix_run v u₁ (fun h => by rw [hsp]; have := (hev h).2.1; omega) (fun h => by
    have hp : ps ≠ [] := fun e => absurd (ht.r11 (hev h).1) (by rw [e]; simp)
    refine ⟨hr11 (hev h).1, ?_, ?_, ?_, ?_⟩ <;> simp only [u₁, clearedP, hp, ↓reduceIte, clearedG])
  rw [hsp, hmx] at hem
  rw [hsp, hmem] at hm₁
  let u₂ : State := { u₁ with mem := m₁, mxcsr := fixMx v u.mxcsr }
  obtain ⟨m', he, ho, hi⟩ := wipe_run v ks cs u₂ hv (by show cs.sum ≤ (u₁.gpr .rsp).toNat; rw [hsp]; exact hs)
    hx0 hr11
  rw [show u₂.gpr .rsp = u.gpr .rsp from hsp] at he ho hi
  refine ⟨m', ?_, ho, fun x hx => ?_⟩
  · have h₃ := execBlock_clearGpr rb gs ht.gne
      (fun h => absurd (ht.gsOk _ h) (by decide : Reg.rax ∉ scratchRegs)) { u₂ with mem := m' }
    have e := Exec.seq (M := isa) (.block h₁) (.seq hem (.seq he (.block h₃)))
    simp only [List.nil_append, List.append_nil] at e
    have hax : u₁.gpr .rax = u.gpr .rax := by
      simp only [u₁, clearedP]; split
      · rw [(hcH _).1]; rfl
      · simp only [clearedG, show Reg.rax ∉ ps from fun h => absurd (ht.psOk _ h) (by decide : Reg.rax ∉ scratchRegs),
          ↓reduceIte]
        rw [(hcH _).1]; rfl
    have hf : finState v rb xs ps gs m' u =
        clearedG gs (({ u₂ with mem := m' } : State).setReg .rax (retVal rb (u₂.gpr .rax))) := by
      rw [show u₂.gpr .rax = u.gpr .rax from hax]; rfl
    rw [hf]
    exact e
  · rw [hi x hx]
    exact hm₁ x fun ⟨h, hs4⟩ => hx ((hev h).2.2 x hs4)

/-! ## What `Sig.contract` gives -/

/-- What `Verified.scrub` needs of the calling convention a contract is for:
`abi`'s, possibly with tables of constants (`Abi.withConsts`), which add
readable regions apart from the stack the function uses, and with tables of
functions (`Abi.withTables`). -/
structure ScrubAbi (A : Abi isa) : Prop where
  ptrBits : A.ptrBits = 64
  reserved : A.reserved = abi.reserved
  wr : ∀ s, A.wr s = s.wr
  wf : ∀ ws n s, A.wf ws n s → (n = 0 ∨ n ≤ (s.gpr .rsp).toNat) ∧
    ∀ r ∈ s.rd, r ∉ A.rd s → ∀ q ∈ abi.reserved n s, q.Disjoint r
  pub : ∀ s₁ s₂, A.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp
  mem : ∀ s, A.mem s = s.mem
  ret : ∀ s, A.ret s = s.gpr .rax
  rdSub : ∀ s r, r ∈ A.rd s → r ∈ s.rd
  argsLen : ∀ ws f, A.args ws = some f → ∀ s, (f s).length = ws.length
  args : ∀ ws, A.args ws = abi.args ws
  argRo : ∀ ws s, ∀ p ∈ A.argArea ws s, p.2 = false

theorem abi_args_len (ws : List Nat) (f : State → List (BitVec 64)) (h : abi.args ws = some f) (s : State) :
    (f s).length = ws.length := by
  have h6 : argRegs.length = 6 := rfl
  simp only [abi] at h
  split at h <;> cases h
  · rename_i hl; simp only [List.length_map, List.length_take]; omega
  · rename_i hl; simp only [List.length_append, List.length_map, List.length_range]; omega

theorem abi_wf_stack {ws : List Nat} {n : Nat} {s : State} (h : abi.wf ws n s) :
    n = 0 ∨ n ≤ (s.gpr .rsp).toNat := by
  simp only [abi] at h
  split at h
  · cases n with
    | zero => exact .inl rfl
    | succ n => exact .inr h
  · cases n with
    | zero => exact .inl rfl
    | succ n => exact .inr h.1

theorem abi_argRo (ws : List Nat) (s : State) : ∀ p ∈ abi.argArea ws s, p.2 = false := by
  intro p hp
  simp only [abi] at hp
  split at hp
  · cases hp
  · simp only [List.mem_singleton] at hp; subst hp; rfl

theorem ScrubAbi.plain : ScrubAbi abi :=
  ⟨rfl, rfl, fun _ => rfl, fun _ _ _ h => ⟨abi_wf_stack h, fun _ hr hn => absurd hr hn⟩,
    fun _ _ h => h, fun _ => rfl, fun _ => rfl, fun _ _ h => h, abi_args_len, fun _ => rfl, abi_argRo⟩

theorem ScrubAbi.consts (cs : List (String × List (BitVec 64))) : ScrubAbi (abi.withConsts cs) := by
  cases cs with
  | nil => exact ScrubAbi.plain
  | cons c cs =>
    refine ⟨rfl, rfl, fun _ => rfl, fun ws n s h => ?_, fun _ _ h => h.1, fun _ => rfl, fun _ => rfl,
      fun _ _ h => List.mem_of_mem_take h, abi_args_len, fun _ => rfl, abi_argRo⟩
    obtain ⟨hw, hdrop, -, hdis, -⟩ := h
    refine ⟨abi_wf_stack hw, fun r hr hn q hq => ?_⟩
    have hr' : r ∈ (abi.rd s).drop ((abi.rd s).length - (c :: cs).length) := by
      change r ∈ abi.rd s at hr
      rw [← List.take_append_drop ((abi.rd s).length - (c :: cs).length) (abi.rd s)] at hr
      rcases List.mem_append.mp hr with h | h
      · exact absurd h hn
      · exact h
    rw [hdrop] at hr'
    exact ((hdis r hr').2.2 q hq).symm

theorem ScrubAbi.tables {A : Abi isa} (hA : ScrubAbi A) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi (A.withTables sig ts) := by
  cases ts with
  | nil => exact hA
  | cons t ts =>
    exact ⟨hA.ptrBits, hA.reserved, hA.wr, fun ws n s h => hA.wf ws n s h.1,
      fun s₁ s₂ h => hA.pub s₁ s₂ h.1, hA.mem, hA.ret, hA.rdSub, hA.argsLen, hA.args, hA.argRo⟩

theorem withMode_ptrBits (A : Abi isa) (b : Bool) : (A.withMode b).ptrBits = A.ptrBits := by
  cases b <;> rfl

/-- With what two runs must also agree on to be related as public
(`Abi.withMode`). -/
theorem ScrubAbi.mode {A : Abi isa} (hA : ScrubAbi A) (b : Bool) : ScrubAbi (A.withMode b) := by
  cases b with
  | false => exact hA
  | true => exact { hA with pub := fun s₁ s₂ h => hA.pub s₁ s₂ h.1 }

/-- The calling convention of every x86-64 artifact (`Api.artifact`). -/
theorem ScrubAbi.of (cs : List (String × List (BitVec 64))) (sig : Sig) (ts : List (String × List FnTable))
    (b : Bool) : ScrubAbi (((abi.withConsts cs).withTables sig ts).withMode b) :=
  ((ScrubAbi.consts cs).tables sig ts).mode b

/-! ## What `Sig.contract` gives -/

theorem contract_pre_scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) :
    (stack = 0 ∨ stack ≤ (s.gpr .rsp).toNat) ∧
      ∀ r ∈ s.rd ++ s.wr, (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r ∧
        (stack ≠ 0 → (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Disjoint r) := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals _
  obtain ⟨hwf, hrd, hwr, -, hres, -⟩ := h
  obtain ⟨hst, hcon⟩ := hA.wf _ _ _ hwf
  have hres' : ∀ r ∈ abi.reserved stack s, ∀ a ∈ (Sig.bufs sig.params (vals s) ++
      (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)) ++
      (A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)), r.Disjoint a.1 := by
    rw [← hA.reserved]; exact hres
  have key : ∀ r ∈ s.rd ++ s.wr, ∀ q ∈ abi.reserved stack s, q.Disjoint r := by
    intro r hr q hq
    rcases List.mem_append.mp hr with hr | hr
    · by_cases hn : r ∈ A.rd s
      · rw [hrd] at hn
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
        exact hres' q hq a (List.mem_filter.mp ha).1
      · exact hcon r hr hn q hq
    · rw [← hA.wr, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hres' q hq a (List.mem_filter.mp ha).1
  refine ⟨hst, fun r hr => ⟨key r hr _ (by simp [abi]), fun hn => key r hr _ ?_⟩⟩
  cases stack with
  | zero => exact absurd rfl hn
  | succ n => simp [abi, stackBelow]

theorem contract_pub_rsp {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : s₁.gpr .rsp = s₂.gpr .rsp := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact hA.pub _ _ h.1
    | some f => exact hA.pub _ _ h.1.1

/-! ## The result -/

theorem retVal_low {rb : Nat} (hrb : rb ≤ 32 ∨ rb = 64) (x : BitVec 64) :
    (retVal rb x).setWidth rb = x.setWidth rb := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, retVal]
  by_cases h0 : rb = 0
  · subst h0; simp [Nat.mod_one]
  by_cases h1 : rb < 32
  · simp only [h0, h1, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 2 ^ rb - 1) (by have := Nat.pow_lt_pow_right (a := 2) (by omega) h1; omega),
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
      Nat.mod_eq_of_lt (a := x.toNat % 2 ^ 32 % 2 ^ rb) (by
        have := Nat.mod_lt (x.toNat % 2 ^ 32) (Nat.two_pow_pos rb)
        have := Nat.pow_le_pow_right (n := 2) (by omega) (show rb ≤ 64 by omega); omega),
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  by_cases h2 : rb = 32
  · subst h2; simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]
  · have : rb = 64 := by omega
    subst this; simp

theorem retVal_hi {rb : Nat} (hrb : rb ≤ 32 ∨ rb = 64) (x : BitVec 64) : retVal rb x >>> rb = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, retVal, Nat.shiftRight_eq_div_pow]
  apply Nat.div_eq_of_lt
  by_cases h0 : rb = 0
  · subst h0; simp
  by_cases h1 : rb < 32
  · simp only [h0, h1, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 2 ^ rb - 1) (by have := Nat.pow_lt_pow_right (a := 2) (by omega) h1; omega),
      Nat.and_two_pow_sub_one_eq_mod]
    have h3 := Nat.mod_lt (x.toNat % 2 ^ 32) (Nat.two_pow_pos rb)
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show rb ≤ 64 by omega)
    rw [Nat.mod_eq_of_lt (by omega)]; exact h3
  by_cases h2 : rb = 32
  · subst h2; simp only [h0, h1, ↓reduceIte, BitVec.toNat_setWidth]
    have := Nat.mod_lt x.toNat (Nat.two_pow_pos 32)
    rw [Nat.mod_eq_of_lt (by omega)]; exact this
  · have : rb = 64 := by omega
    subst this; simp only [h0, h1, h2, ↓reduceIte]; exact x.isLt

/-- How `scrub` clears the vector registers, as an instruction level. -/
def _root_.VG.Impl.Scrub.X86_64.VecLevel.level : VecLevel → Nat
  | .sse => 0
  | .avx => 1
  | .evex => 2

/-! ## The theorem -/

theorem clearedH_keep (v : VecLevel) (w : State) :
    (clearedH v w).gpr = w.gpr ∧ (clearedH v w).xmm = w.xmm ∧ (clearedH v w).ymmHi = w.ymmHi ∧
      (clearedH v w).zmmHi = w.zmmHi ∧ (clearedH v w).mem = w.mem ∧ (clearedH v w).rd = w.rd ∧
      (clearedH v w).wr = w.wr ∧ (clearedH v w).mxcsr = w.mxcsr := by
  cases v <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem clearedP_gpr {ps : List Reg} {s : State} {r : Reg} :
    (clearedP ps s).gpr r = if r ∈ ps then 0 else s.gpr r := by
  unfold clearedP; split
  · rename_i h; subst h; simp
  · simp [clearedG]

theorem finState_gpr {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State}
    {r : Reg} (hp : r ∉ ps) (hg : r ∉ gs) (h₂ : r ≠ .rax) :
    (finState v rb xs ps gs m' u).gpr r = u.gpr r := by
  simp only [finState, clearedG, State.setReg, hg, h₂, ↓reduceIte, clearedP_gpr, hp]
  rw [(clearedH_keep v _).1]
  rfl

theorem finState_rax {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State}
    (hg : Reg.rax ∉ gs) : (finState v rb xs ps gs m' u).gpr .rax = retVal rb (u.gpr .rax) := by
  simp only [finState, clearedG, State.setReg, hg, ↓reduceIte]

theorem finState_xmm {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State} :
    (finState v rb xs ps gs m' u).xmm = fun x => if x ∈ xs then 0 else u.xmm x := by
  simp only [finState, clearedG, State.setReg, clearedP]
  split <;> exact (clearedH_keep v _).2.1

theorem finState_ymmHi {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State} :
    (finState v rb xs ps gs m' u).ymmHi = fun x => if v ≠ .sse ∧ x ∈ xs then 0 else u.ymmHi x := by
  simp only [finState, clearedG, State.setReg, clearedP]
  split <;> exact (clearedH_keep v _).2.2.1

theorem finState_zmmHi {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State} :
    (finState v rb xs ps gs m' u).zmmHi = fun x => if v ≠ .sse ∧ x ∈ xs then 0 else u.zmmHi x := by
  simp only [finState, clearedG, State.setReg, clearedP]
  split <;> exact (clearedH_keep v _).2.2.2.1

theorem finState_other {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State} :
    (finState v rb xs ps gs m' u).mem = m' ∧ (finState v rb xs ps gs m' u).rd = u.rd ∧
      (finState v rb xs ps gs m' u).wr = u.wr ∧ (finState v rb xs ps gs m' u).ymmH = (clearedH v u).ymmH ∧
      (finState v rb xs ps gs m' u).zmmHiH = (clearedH v u).zmmHiH ∧
      (finState v rb xs ps gs m' u).mxcsr = fixMx v u.mxcsr ∧
      (finState v rb xs ps gs m' u).cf = some false ∧ (finState v rb xs ps gs m' u).zf = some true ∧
      (finState v rb xs ps gs m' u).sf = some false ∧ (finState v rb xs ps gs m' u).of = some false := by
  have k := clearedH_keep v (clearedV v xs u)
  have hy : (clearedH v (clearedV v xs u)).ymmH = (clearedH v u).ymmH := by cases v <;> rfl
  have hz : (clearedH v (clearedV v xs u)).zmmHiH = (clearedH v u).zmmHiH := by cases v <;> rfl
  unfold finState clearedP
  split
  · exact ⟨rfl, k.2.2.2.2.2.1, k.2.2.2.2.2.2.1, hy, hz, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, k.2.2.2.2.2.1, k.2.2.2.2.2.2.1, hy, hz, rfl, rfl, rfl, rfl, rfl⟩

theorem slot_not_below {sp x : Addr} {n : Nat} (hn : n + 8 < 2 ^ 64)
    (hx : (⟨sp, 8⟩ : Region).Contains x 1) : ¬ (⟨sp - BitVec.ofNat 64 n, n⟩ : Region).Contains x 1 := by
  have := sp.isLt; have := x.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_ofNat] at hx ⊢
  generalize sp.toNat = P at *
  generalize x.toNat = X at *
  rw [Nat.mod_eq_of_lt (a := n) (by omega)]
  omega

/-- Two runs of `c` leave the same bytes in the `stack` bytes below the stack
pointer on entry but those `wipe v ks cs` zeroes. -/
def ResOk (c : Prog isa) (k : Contract isa) (stack : Nat) (ks cs : List Nat) : Prop :=
  ∀ s₁ s₂ t₁ t₂ u₁ u₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ → s₁.unknowns = s₂.unknowns →
    Exec isa c s₁ t₁ u₁ → Exec isa c s₂ t₂ u₂ →
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 →
      ¬ WCov ks cs (s₁.gpr .rsp) x → u₁.mem x = u₂.mem x

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- Code verified against a contract that `Sig.contract` derives, whose
frames and calls use at most `stack` bytes, run by `scrub`, which clears
the granules `ks` of the `cs.sum = stack` bytes of stack below `rsp`:
verified against the same contract, and without secret residue, if the
postcondition reads the memory on return only within the buffers (`hpost`)
and the code leaves the same bytes in both runs in the rest of that stack
(`hres`, which `RTaint` derives from its analysis). -/
theorem Verified.scrub {c : Prog isa} {v : VecLevel} {xs : List XReg} {ps gs : List Reg} {ks cs : List Nat}
    (hA : ScrubAbi A)
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ stack) (hcs : cs.sum = stack) (hst : stack + 8 < 2 ^ 64)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hlv : ∀ i ∈ instrs c, i.vecLevel ≤ v.level)
    (hrb : sig.retBits A.ptrBits ≤ 32 ∨ sig.retBits A.ptrBits = 64)
    (hpost : ∀ s u u', (sig.contract A pre post wa stack leak).pre s →
      (sig.contract A pre post wa stack leak).post s u →
      (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
      (u'.gpr .rax).setWidth (sig.retBits A.ptrBits) = (u.gpr .rax).setWidth (sig.retBits A.ptrBits) →
      (sig.contract A pre post wa stack leak).post s u')
    (hres : ResOk c (sig.contract A pre post wa stack leak) stack ks cs)
    (ht : TailOk (sig.retBits A.ptrBits) xs ps gs ks)
    (hxs : (∀ x, x ∈ xs) ∨ ∀ i ∈ instrs c, writesVec i = false)
    (hxe : v = .evex → ∀ x, x ∈ xs) (hev : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk v ks cs p)
    (hgk : ∀ r ∈ scratchRegs, r ∉ gs → r ∉ ps → ∀ i ∈ instrs c, Taint.clobbers i r = false) :
    Verified target (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) xs ps gs ks cs c)
        (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) xs ps gs ks cs c)
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  have hnps : ∀ r, r ∉ scratchRegs → r ∉ ps := fun r h h' => h (ht.psOk r h')
  have hngs : ∀ r, r ∉ scratchRegs → r ∉ gs := fun r h h' => h (ht.gsOk r h')
  obtain ⟨hcor, hct, hsat⟩ := h
  -- What a run of `c`, then of the clearing, gives.
  have run : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      abiPreserved s u ∧ (sig.contract A pre post wa stack leak).post s u ∧
      u.gpr .rsp = s.gpr .rsp ∧ cs.sum ≤ (u.gpr .rsp).toNat := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, hp⟩ := hcor s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
    refine ⟨ha, hp, hr, ?_⟩
    rcases (contract_pre_scrub hA hs).1 with h0 | h0
    · rw [hcs, h0]; exact Nat.zero_le _
    · rw [hcs, hr]; exact h0
  -- The clearing's run.
  have tail : ∀ s t u s' t', (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      Exec isa (Impl.Scrub.X86_64.scrubTail v (sig.retBits A.ptrBits) xs ps gs ks cs) u t' s' →
      ∃ m', t' = tailTr v ks cs (s.gpr .rsp) ∧ s' = finState v (sig.retBits A.ptrBits) xs ps gs m' u ∧
        (∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x) ∧
        (∀ x, WCov ks cs (s.gpr .rsp) x → m' x = 0) ∧ (∀ x, ¬ WCov ks cs (s.gpr .rsp) x → m' x = u.mem x) := by
    intro s t u s' t' hs he het
    obtain ⟨-, -, hr, hl⟩ := run s t u hs he
    obtain ⟨m', e, hz, hu⟩ := tail_run v (sig.retBits A.ptrBits) cs ht u hv hl (hev _ hl)
    obtain ⟨rfl, rfl⟩ := Exec.det het e
    rw [hr] at hz hu
    have ho : ∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x :=
      fun x h => hu x fun hw => h (hcs ▸ hw.1)
    exact ⟨m', by rw [hr], rfl, ho, hz, hu⟩
  -- Buffers are not in the stack the clearing wipes.
  have outB : ∀ s, (sig.contract A pre post wa stack leak).pre s → ∀ x,
      (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) →
        ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 := by
    intro s hs x ⟨r, hr, hx⟩ hb
    by_cases h0 : stack = 0
    · subst h0; simp [Region.Contains] at hb
    · exact ((contract_pre_scrub hA hs).2 r hr).2 h0 x hb hx
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hun e₁ e₂ => ?_⟩
  · -- Correctness.
    obtain ⟨t, u, he, -⟩ := hcor s hs
    obtain ⟨ha, hq, hr, hl⟩ := run s t u hs he
    obtain ⟨m', et, hz, hu⟩ := tail_run v (sig.retBits A.ptrBits) cs ht u hv hl (hev _ hl)
    rw [hr] at hz hu
    have hmo : ∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x :=
      fun x h => hu x fun hw => h (hcs ▸ hw.1)
    refine ⟨_, _, .seq he et, ⟨fun r hr' => ?_, ?_, ?_⟩, ?_⟩
    · have h1 : r ∉ scratchRegs := by revert hr'; revert r; decide
      have h2 : r ≠ .rax := by
        have : ∀ r ∈ calleeSaved, r ≠ Reg.rax := by decide
        exact this r hr'
      rw [finState_gpr (hnps r h1) (hngs r h1) h2]
      exact ha.1 r hr'
    · rw [← ha.2.1]
      apply Mem.readW_congr
      intro i hi
      rw [finState_other.1]
      exact hmo _ (slot_not_below hst (by
        simp only [Region.Contains]
        rw [show s.gpr .rsp + BitVec.ofNat 64 i - s.gpr .rsp = BitVec.ofNat 64 i by
          rw [BitVec.add_comm, BitVec.add_sub_cancel], BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [Nat.reduceDiv] at hi; omega))
    · rw [finState_other.2.2.2.2.2.1, fixMx_ctl]; exact ha.2.2
    · refine hpost s u _ hs hq (fun x hx => hmo x (outB s hs x hx)) ?_
      rw [finState_rax (hngs _ (by decide))]
      exact retVal_low hrb _
  · -- Constant time.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨m₁, rfl, -⟩ := tail s₁ _ _ _ _ h₁ a₁ b₁
    obtain ⟨m₂, rfl, -⟩ := tail s₂ _ _ _ _ h₂ a₂ b₂
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, contract_pub_rsp hA hp]
  · -- No residue.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    rename_i u₁ _ _ u₂ _ _
    obtain ⟨m₁, -, rfl, hmo₁, hz₁, hu₁⟩ := tail s₁ _ _ _ _ h₁ a₁ b₁
    obtain ⟨m₂, -, rfl, hmo₂, hz₂, hu₂⟩ := tail s₂ _ _ _ _ h₂ a₂ b₂
    obtain ⟨ha₁, -, -, -⟩ := run s₁ _ _ h₁ a₁
    obtain ⟨ha₂, -, -, -⟩ := run s₂ _ _ h₂ a₂
    have ho' := ho
    obtain ⟨hrd, hwr, hg, -, -, -, -, -, hxm, hy, hz, hyH, hzH, hmx, hm⟩ := ho
    have hsp' : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
    have rw₁ := Exec.rdwr a₁
    have rw₂ := Exec.rdwr a₂
    -- Below the level `evex`, the code keeps `zmm16`–`zmm31` and MXCSR.
    have lv1 : v ≠ .evex → ∀ i ∈ instrs c, i.vecLevel ≤ 1 := fun hne i hi => by
      have := hlv i hi
      cases v
      · simp only [VecLevel.level] at this; omega
      · exact this
      · exact absurd rfl hne
    have k1 : v ≠ .evex → (u₁.ymmH = s₁.ymmH ∧ u₁.zmmHiH = s₁.zmmHiH ∧ u₁.mxcsr = s₁.mxcsr) ∧
        (u₂.ymmH = s₂.ymmH ∧ u₂.zmmHiH = s₂.zmmHiH ∧ u₂.mxcsr = s₂.mxcsr) := fun hne => by
      have k₁ := Exec.vecKeep1 (lv1 hne) a₁
      have k₂ := Exec.vecKeep1 (lv1 hne) a₂
      simp only [vk1, Prod.mk.injEq] at k₁ k₂
      exact ⟨k₁, k₂⟩
    have cH : v ≠ .evex → ∀ w : State, (clearedH v w).ymmH = w.ymmH ∧ (clearedH v w).zmmHiH = w.zmmHiH :=
      fun hne w => by cases v <;> first | exact ⟨rfl, rfl⟩ | exact absurd rfl hne
    have hdep : c.x86_64Depth < 2 ^ 64 := by omega
    have f₁ := Exec.stackFrame hsp a₁ hdep
    have f₂ := Exec.stackFrame hsp a₂ hdep
    have cs_ : ∀ r : Reg, r ∉ scratchRegs → r ≠ .rax → r ∈ calleeSaved := by intro r; cases r <;> decide
    -- With the vector registers' upper halves kept: code of level 0, or that writes none.
    have l0 : (∃ x, x ∉ xs ∧ v ≠ .sse) → ∀ i ∈ instrs c, i.vecLevel = 0 := by
      rintro ⟨x, hx, -⟩ i hi
      by_cases he : v = .evex
      · exact absurd (hxe he x) hx
      · rcases hxs with h | h
        · exact absurd (h x) hx
        · exact vecLevel_of_writesVec (h i hi) (lv1 he i hi)
    have upper : ∀ x, ¬ (v ≠ .sse ∧ x ∈ xs) → u₁.ymmHi x = u₂.ymmHi x ∧ u₁.zmmHi x = u₂.zmmHi x := by
      intro x hn
      have hl : ∀ i ∈ instrs c, i.vecLevel = 0 := by
        by_cases hs : v = .sse
        · subst hs; exact fun i hi => by simpa [VecLevel.level] using hlv i hi
        · exact l0 ⟨x, fun h => hn ⟨hs, h⟩, hs⟩
      have k₁ := Exec.vecKeep0 hl a₁
      have k₂ := Exec.vecKeep0 hl a₂
      simp only [vk0, Prod.mk.injEq] at k₁ k₂
      rw [k₁.2.2.2.1, k₂.2.2.2.1, k₁.2.2.2.2, k₂.2.2.2.2, hy, hz]
      exact ⟨rfl, rfl⟩
    refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
    · rw [finState_other.2.1, finState_other.2.1, rw₁.1, rw₂.1, hrd]
    · rw [finState_other.2.2.1, finState_other.2.2.1, rw₁.2, rw₂.2, hwr]
    · by_cases hs : r ∈ scratchRegs
      · have h11 : r ≠ .rax := hr
        by_cases hg' : r ∈ gs
        · simp [finState, clearedG, hg']
        · by_cases hp' : r ∈ ps
          · simp [finState, clearedG, State.setReg, clearedP_gpr, hg', hp', h11]
          · rw [finState_gpr hp' hg' h11, finState_gpr hp' hg' h11, Exec.gpr (hgk r hs hg' hp') a₁,
              Exec.gpr (hgk r hs hg' hp') a₂]
            exact hg r hr
      · rw [finState_gpr (hnps r hs) (hngs r hs) hr, finState_gpr (hnps r hs) (hngs r hs) hr,
          ha₁.1 r (cs_ r hs hr), ha₂.1 r (cs_ r hs hr)]
        exact hg r hr
    · rw [finState_rax (hngs _ (by decide)), finState_rax (hngs _ (by decide)), retVal_hi hrb, retVal_hi hrb]
    · rw [finState_other.2.2.2.2.2.2.1, finState_other.2.2.2.2.2.2.1]
    · rw [finState_other.2.2.2.2.2.2.2.1, finState_other.2.2.2.2.2.2.2.1]
    · rw [finState_other.2.2.2.2.2.2.2.2.1, finState_other.2.2.2.2.2.2.2.2.1]
    · rw [finState_other.2.2.2.2.2.2.2.2.2, finState_other.2.2.2.2.2.2.2.2.2]
    · rw [finState_xmm, finState_xmm]
      funext x
      split
      · rfl
      · rename_i hx
        rcases hxs with h | h
        · exact absurd (h x) hx
        · rw [Exec.xmmKeep h a₁, Exec.xmmKeep h a₂, hxm]
    · rw [finState_ymmHi, finState_ymmHi]
      funext x
      split
      · rfl
      · rename_i hn; exact (upper x hn).1
    · rw [finState_zmmHi, finState_zmmHi]
      funext x
      split
      · rfl
      · rename_i hn; exact (upper x hn).2
    · rw [finState_other.2.2.2.1, finState_other.2.2.2.1]
      by_cases he : v = .evex
      · subst he; rfl
      · rw [(cH he _).1, (cH he _).1, (k1 he).1.1, (k1 he).2.1, hyH]
    · rw [finState_other.2.2.2.2.1, finState_other.2.2.2.2.1]
      by_cases he : v = .evex
      · subst he; rfl
      · rw [(cH he _).2, (cH he _).2, (k1 he).1.2.1, (k1 he).2.2.1, hzH]
    · rw [finState_other.2.2.2.2.2.1, finState_other.2.2.2.2.2.1]
      by_cases he : v = .evex
      · exact fixMx_congr v he (by rw [ha₁.2.2, ha₂.2.2, hmx])
      · rw [(k1 he).1.2.2, (k1 he).2.2.2, hmx]
    · rw [finState_other.1, finState_other.1]
      have hx' : ∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1 := by
        rw [finState_other.2.1, finState_other.2.2.1, rw₁.1, rw₁.2] at hx
        exact hx
      by_cases hb : (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1
      · by_cases hw : WCov ks cs (s₁.gpr .rsp) x
        · rw [hz₁ x hw, hz₂ x (hsp' ▸ hw)]
        · rw [hu₁ x hw, hu₂ x (hsp' ▸ hw)]
          exact hres _ _ _ _ _ _ h₁ h₂ hp ho' hun a₁ a₂ x hb hw
      · have nd : ∀ sp : Addr, sp = s₁.gpr .rsp →
            ¬ (⟨sp - BitVec.ofNat 64 c.x86_64Depth, c.x86_64Depth⟩ : Region).Contains x 1 := by
          rintro sp rfl hc; exact hb (below_sub hd (by omega) x hc)
        have nw : ∀ r ∈ s₁.wr, ¬ r.Contains x 1 := fun r hr => hx' r (List.mem_append_right _ hr)
        rw [hmo₁ x hb, hmo₂ x (hsp' ▸ hb),
          f₁ x (fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact nw r hr
            · simp only [List.mem_singleton] at hr; subst hr; exact nd _ rfl),
          f₂ x (fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact nw r (hwr ▸ hr)
            · simp only [List.mem_singleton] at hr; subst hr; exact nd _ hsp'.symm)]
        exact hm x hx'

end

/-! ## Registering scrubbed code -/

/-- A postcondition that reads the memory on return only within the
buffers, and of the result only its `rb` bits (`Verified.scrub`'s `hpost`). -/
def PostOut (k : Contract isa) (rb : Nat) : Prop :=
  ∀ s u u', k.pre s → k.post s u →
    (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
    (u'.gpr .rax).setWidth rb = (u.gpr .rax).setWidth rb → k.post s u'

/-- `PostOut` of a contract `Sig.contract` derives, from its postcondition's
reading the memory on return only within the buffers. -/
theorem postOut_of_local {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -⟩ := hs
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers where the precondition holds (e.g. one that reads
an output buffer by a length the precondition equates with the buffer's). -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

theorem zeroW_spSafe (v : VecLevel) (n a : Nat) : (!isa.writesSp (zeroW v n a)) = true := by
  unfold zeroW; split <;> rfl

theorem storesF_spSafe (v : VecLevel) (ks : List Nat) (off base : Nat) :
    ∀ f k, (storesF v ks off base f k).all (fun i => !isa.writesSp i) = true
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | f + 1, k + 1 => by
    simp only [storesF]
    rw [List.all_append, storesF_spSafe v ks off base f, Bool.and_true]
    split
    · rfl
    · rw [List.all_cons, List.all_nil, Bool.and_true]; exact zeroW_spSafe _ _ _

theorem wipe_spSafe (v : VecLevel) (ks : List Nat) : ∀ cs : List Nat, (wipe v ks cs).all (fun i => !isa.writesSp i) = true
  | [] => rfl
  | b :: bs => by
    simp only [wipe, Code.all, chunkStores, List.all_append, storesF_spSafe, wipe_spSafe v ks bs,
      Bool.true_and, Bool.and_true, store8s]
    split <;> rfl

theorem zeroR_spSafe : ∀ r ∈ scratchRegs, (!isa.writesSp (zeroR r)) = true := by decide

theorem scrub_spSafe {c : Prog isa} (v : VecLevel) (rb : Nat) (xs : List XReg) (ps gs : List Reg)
    (ks cs : List Nat) (hps : ∀ r ∈ ps, r ∈ scratchRegs) (hgs : ∀ r ∈ gs, r ∈ scratchRegs)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrub v rb xs ps gs ks cs c).all (fun i => !isa.writesSp i) = true := by
  have hx : (xs.map (zeroX v)).all (fun i => !isa.writesSp i) = true := by
    simp only [List.all_map, List.all_eq_true]
    exact fun x _ => by cases v <;> rfl
  have hp : (ps.map zeroR).all (fun i => !isa.writesSp i) = true := by
    simp only [List.all_map, List.all_eq_true]
    exact fun r hr => zeroR_spSafe r (hps r hr)
  have hh : (clearHigh v).all (fun i => !isa.writesSp i) = true := by cases v <;> rfl
  have hm : (mxFix v).all (fun i => !isa.writesSp i) = true := by cases v <;> rfl
  have hv : (xs.map (zeroX v) ++ clearHigh v ++ ps.map zeroR).all (fun i => !isa.writesSp i) = true := by
    rw [List.all_append, List.all_append, hx, hh, hp]; rfl
  have hg : (retFix rb ++ gs.map zeroR).all (fun i => !isa.writesSp i) = true := by
    simp only [List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, fun r hr => zeroR_spSafe r (hgs r hr)⟩
    unfold retFix
    split
    · intro i hi; simp at hi; subst hi; rfl
    · split
      · intro i hi; simp at hi; subst hi; rfl
      · split
        · intro i hi; simp at hi; subst hi; rfl
        · intro i hi; simp at hi
  rw [scrub, scrubTail]
  simp only [Code.all]
  rw [h, hv, hm, wipe_spSafe v ks cs, hg]
  rfl

/-! ## What `scrub` clears, from the code -/

theorem tailOk_of (rb : Nat) (c : Prog isa) (ks : List Nat) :
    TailOk rb (xsOf c ks) (psOf ks) (gsOf Taint.clobbers c) ks where
  x0 h := by unfold xsOf; split <;> first | simp [mem_xregs] | simp [h]
  r11 h := by simp [psOf, h]
  psOk r hr := by unfold psOf at hr; split at hr <;> simp_all [scratchRegs]
  gsOk r hr := by
    unfold gsOf at hr; simp only at hr; split at hr
    · simp_all [scratchRegs]
    · exact (List.mem_filter.mp hr).1
  gne := by unfold gsOf; simp only; split <;> simp_all

theorem xs_of (c : Prog isa) (ks : List Nat) :
    (∀ x, x ∈ xsOf c ks) ∨ ∀ i ∈ instrs c, writesVec i = false := by
  unfold xsOf; split
  · rename_i h; exact .inr fun i hi => by simpa using Code.all_instrs h i hi
  · exact .inl mem_xregs

theorem gs_of (c : Prog isa) (ks : List Nat) :
    ∀ r ∈ scratchRegs, r ∉ gsOf Taint.clobbers c → r ∉ psOf ks → ∀ i ∈ instrs c, Taint.clobbers i r = false := by
  intro r hr hg _ i hi
  have hall : c.all (fun i => !Taint.clobbers i r) = true := by
    unfold gsOf at hg; simp only at hg
    split at hg
    · rename_i hw
      by_contra hc
      have : r ∈ scratchRegs.filter fun r => !c.all (fun i => !Taint.clobbers i r) := by
        simp only [List.mem_filter, hr, true_and, Bool.not_eq_true']
        simpa using hc
      rw [hw] at this; cases this
    · by_contra hc
      exact hg (List.mem_filter.mpr ⟨hr, by simpa using hc⟩)
  simpa using Code.all_instrs hall i hi

theorem chunksAux_spec : ∀ f n, n / 4080 < f →
    (chunksAux f n).sum = n ∧ ∀ b ∈ chunksAux f n, 0 < b ∧ b ≤ 4080 ∧ (n % 8 = 0 → b % 8 = 0)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => ⟨rfl, fun _ h => by simp [chunksAux] at h⟩
  | f + 1, n + 1, h => by
    simp only [chunksAux]
    split
    · exact ⟨by simp, fun b hb => by simp at hb; subst hb; omega⟩
    · obtain ⟨hs, hv⟩ := chunksAux_spec f (n + 1 - 4080) (by omega)
      refine ⟨by rw [List.sum_cons, hs]; omega, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · have := hv b hb; omega

theorem chunks_sum (n : Nat) : (chunks n).sum = n := (chunksAux_spec _ n (by omega)).1

theorem chunks_valid {n : Nat} (h8 : n % 8 = 0) : ∀ b ∈ chunks n, 0 < b ∧ b < 4096 ∧ b % 8 = 0 :=
  fun b hb => by have := (chunksAux_spec _ n (by omega)).2 b hb; omega

/-! ## Wiping every granule

With every granule of the stack in `ks`, `ResOk` asks nothing of the code:
what code the residue analysis cannot follow is scrubbed so. -/

/-- Every granule of `wipe _ _ cs`. -/
def allKs : List Nat → List Nat
  | [] => []
  | b :: bs => bs.sum :: ((List.range (b / 16)).map fun t => bs.sum + b % 16 + 16 * t) ++ allKs bs

theorem covC_mono {ks ks' : List Nat} (h : ∀ k ∈ ks, k ∈ ks') {off b d : Nat} (hc : covC ks off b d = true) :
    covC ks' off b d = true := by
  unfold covC at hc ⊢
  split
  · rename_i hd
    simp only [hd, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hc
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hc.1, List.contains_iff_mem.mpr (h _ (List.contains_iff_mem.mp hc.2))⟩
  · rename_i hd
    simp only [hd, ↓reduceIte] at hc
    exact List.contains_iff_mem.mpr (h _ (List.contains_iff_mem.mp hc))

theorem cov_mono {ks ks' : List Nat} (h : ∀ k ∈ ks, k ∈ ks') : ∀ (cs : List Nat) (i : Nat),
    cov ks cs i = true → cov ks' cs i = true
  | [], _, hc => by simp [cov] at hc
  | b :: bs, i, hc => by
    simp only [cov] at hc ⊢
    split
    · rename_i hlt
      simp only [hlt, ↓reduceIte] at hc
      exact cov_mono h bs i hc
    · rename_i hlt
      simp only [hlt, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hc.1, covC_mono h hc.2⟩

theorem cov_all : ∀ cs : List Nat, (∀ b ∈ cs, b % 8 = 0) → ∀ i < cs.sum, cov (allKs cs) cs i = true
  | [], _, i, hi => by simp at hi
  | b :: bs, h8, i, hi => by
    have hb8 := h8 b (List.mem_cons_self ..)
    simp only [List.sum_cons] at hi
    simp only [cov]
    split
    · rename_i hlt
      exact cov_mono (fun k hk => by simp only [allKs, List.mem_cons, List.mem_append]; exact .inr hk) bs i
        (cov_all bs (fun b' hb' => h8 b' (List.mem_cons_of_mem _ hb')) i hlt)
    · rename_i hlt
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by omega, ?_⟩
      unfold covC
      split
      · simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨by omega, List.contains_iff_mem.mpr (by simp [allKs])⟩
      · refine List.contains_iff_mem.mpr ?_
        simp only [allKs, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
        exact .inl (.inr ⟨(i - bs.sum - b % 16) / 16, by omega, rfl⟩)

theorem wcov_all {cs : List Nat} (h8 : ∀ b ∈ cs, b % 8 = 0) {p x : Addr}
    (hx : (⟨p - BitVec.ofNat 64 cs.sum, cs.sum⟩ : Region).Contains x 1) : WCov (allKs cs) cs p x :=
  ⟨hx, cov_all cs h8 _ (by simp only [Region.Contains] at hx; omega)⟩

/-- `ResOk`, with every granule wiped. -/
theorem resOk_all (c : Prog isa) (k : Contract isa) {stack : Nat} (h8 : stack % 8 = 0) :
    ResOk c k stack (allKs (chunks stack)) (chunks stack) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ _ _ _ _ _ _ _ x hx hn
  exact absurd (wcov_all (fun b hb => (chunks_valid h8 b hb).2.2) (by rw [chunks_sum]; exact hx)) hn

theorem evexOk_all (v : VecLevel) {cs : List Nat} (h8 : ∀ b ∈ cs, b % 8 = 0) (h16 : 16 ≤ cs.sum)
    (hs : cs.sum < 2 ^ 64) {p : Addr} (hp : cs.sum ≤ p.toNat) : EvexOk v (allKs cs) cs p := by
  intro _
  refine ⟨?_, h16, fun x hx => wcov_all h8 ?_⟩
  · cases cs with
    | nil => simp at h16
    | cons b bs => simp [allKs]
  · have := p.isLt
    have := x.isLt
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_ofNat] at hx ⊢
    generalize p.toNat = P at *
    generalize x.toNat = X at *
    generalize cs.sum = S at *
    rw [Nat.mod_eq_of_lt (a := S) (by omega)]
    rw [Nat.mod_eq_of_lt (a := 16) (by decide)] at hx
    omega

/-! ## Registering scrubbed code, continued -/

/-- What the level `evex` needs of a registration's clearing (nothing, below
it): every SSE register cleared, and `mxFix`'s bytes wiped. -/
def EvexReg (c : Prog isa) (v : VecLevel) (ks : List Nat) (stack : Nat) : Prop :=
  (v = .evex → ∀ x, x ∈ xsOf c ks) ∧ ∀ p : Addr, (chunks stack).sum ≤ p.toNat → EvexOk v ks (chunks stack) p

theorem evexReg_of_ne {c : Prog isa} {v : VecLevel} {ks : List Nat} {stack : Nat} (h : v ≠ .evex) :
    EvexReg c v ks stack := ⟨fun e => absurd e h, fun _ _ e => absurd e h⟩

/-- At the level `evex`, with every granule wiped, for code that writes a
vector register and has 16 bytes of stack. -/
theorem evexReg_all {c : Prog isa} {v : VecLevel} {stack : Nat} (h8 : stack % 8 = 0) (hst : stack + 8 < 2 ^ 64)
    (hev : v = .evex → 16 ≤ stack ∧ c.all (fun i => !writesVec i) = false) :
    EvexReg c v (allKs (chunks stack)) stack := by
  refine ⟨fun e x => ?_, fun p hp e => ?_⟩
  · unfold xsOf; rw [(hev e).2]; exact mem_xregs x
  · exact evexOk_all v (fun b hb => (chunks_valid h8 b hb).2.2) (by rw [chunks_sum]; exact (hev e).1)
      (by rw [chunks_sum]; omega) hp e

/-- `r`'s code, scrubbed as `scrubRegE` does, returns without secret residue. -/
theorem scrubCodeE_noResidue {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack)) (he : EvexReg r.code v ks r.stack) :
    NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code) r.contract
      (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hr := hres
  rw [e] at hv hp hr ⊢
  have hrb' := hrb
  rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
  exact (Verified.scrub (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
    (chunks_sum r.stack) hst (chunks_valid h8)
    (fun i hi => by simpa using Code.all_instrs hlv i hi) hrb' hp hr (tailOk_of _ _ _) (xs_of _ _) he.1 he.2
    (gs_of _ _)).2

/-- `r`, scrubbed: its code followed by the clearing (`scrub`), at level `v`,
with the granules `ks` of `r.stack` bytes of stack wiped. -/
def scrubRegE {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack)) (he : EvexReg r.code v ks r.stack)
    (hw : r.written = []) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    have hr := hres
    rw [e] at hv hp hr ⊢
    have hrb' := hrb
    rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
    exact (Verified.scrub (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
      (chunks_sum r.stack) hst (chunks_valid h8)
      (fun i hi => by simpa using Code.all_instrs hlv i hi) hrb' hp hr (tailOk_of _ _ _) (xs_of _ _) he.1 he.2
      (gs_of _ _)).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrub_spSafe v _ _ _ _ _ _ (tailOk_of 0 r.code ks).psOk (tailOk_of 0 r.code ks).gsOk r.spSafe
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  residue := some ⟨scrubCodeE_noResidue r v ks hd hst h8 hlv hrb hpost hres he⟩

/-- `scrubRegE`, below the level `evex`. -/
def scrubReg {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack))
    (hw : r.written = []) (hne : v ≠ .evex := by decide) : Registration api target :=
  scrubRegE r v ks hd hst h8 hlv hrb hpost hres (evexReg_of_ne hne) hw

theorem scrubReg_noResidue {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack)) (hw : r.written = [])
    (hne : v ≠ .evex := by decide) :
    NoResidue (scrubReg r v ks hd hst h8 hlv hrb hpost hres hw hne).code r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) :=
  scrubCodeE_noResidue r v ks hd hst h8 hlv hrb hpost hres (evexReg_of_ne hne)

/-- `r`, scrubbed with every granule of its stack wiped: for code the
residue analysis does not follow. At the level `evex` (code that may write
`zmm16`–`zmm31` or MXCSR), it has 16 bytes of stack and writes a vector
register. -/
def scrubRegAll {api : Api} (r : Registration api target) (v : VecLevel)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hev : v = .evex → 16 ≤ r.stack ∧ r.code.all (fun i => !writesVec i) = false)
    (hw : r.written = []) : Registration api target :=
  scrubRegE r v (allKs (chunks r.stack)) hd hst h8 hlv hrb hpost (resOk_all _ _ h8) (evexReg_all h8 hst hev) hw

/-- The level `scrub` clears the vector registers at for `code`, the lowest
that covers its instructions. -/
def levelAll (code : Prog isa) : VecLevel :=
  if code.all (fun i => decide (i.vecLevel ≤ VecLevel.sse.level)) then .sse
  else if code.all (fun i => decide (i.vecLevel ≤ VecLevel.avx.level)) then .avx else .evex

/-- `r`, returning without secret residue with every granule of its stack
wiped (`scrubRegAll`), at the level of its code, if `scrub`'s side conditions
hold and the clearing needs no CPU feature that `r`'s code does not
(`Code.requiresDedup`); otherwise `r` itself, which then has no proof
(`Registration.residue`), as the emitter allows only of what
`ci/residue_allowlist.txt` lists. For a caller generic over the
implementations of the functions it calls, whose code the residue analysis
does not follow. The level is that of every instruction the code may run,
those of the functions of the tables it takes included (`Code.all`), whose
features are not the code's own: a function that needs no AVX but may run
an AVX2 hash function through a table is left as it is. -/
def withScrubAll {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  let v := levelAll r.code
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if h8 : r.stack % 8 = 0 then
  if hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
  if hev : v = .evex → 16 ≤ r.stack ∧ r.code.all (fun i => !writesVec i) = false then
    let r' := scrubRegAll r v hd hst h8 hlv hrb hpost hev hw
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r
  else r else r else r else r else r else r else r

end VG.X86_64.Scrub
