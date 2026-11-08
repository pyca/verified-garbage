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

/-- The trace of `stores16 ks off base k` from `rsp = p`. -/
def storesTr (ks : List Nat) (off : Nat) (p : Addr) (base : Nat) : Nat → List Leak
  | 0 => []
  | k + 1 => (if ks.contains (off + base + 16 * k) then [.addr (p + BitVec.ofNat 64 (base + 16 * k))] else []) ++
    storesTr ks off p base k

/-- The trace of `chunkStores ks off b` from `rsp = p`. -/
def chunkTr (ks : List Nat) (off : Nat) (p : Addr) (b : Nat) : List Leak :=
  storesTr ks off p (b % 16) (b / 16) ++ (if b % 16 = 8 && ks.contains off then [.addr p] else [])

/-- Whether `chunkStores ks off b` zeroes the byte at offset `d` of its frame. -/
def covC (ks : List Nat) (off b d : Nat) : Bool :=
  if d < b % 16 then b % 16 == 8 && ks.contains off
  else ks.contains (off + b % 16 + 16 * ((d - b % 16) / 16))

/-- Whether `wipe ks cs` zeroes the byte at offset `i` from the bottom of the
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

/-- What `stores16 ks off base k` zeroes, at offset `d` of `rsp`. -/
def SCov (ks : List Nat) (off base k d : Nat) : Prop :=
  base ≤ d ∧ d < base + 16 * k ∧ ks.contains (off + base + 16 * ((d - base) / 16)) = true

theorem stores16_run (ks : List Nat) (off b base : Nat) (hb : b < 2 ^ 64) : ∀ (k : Nat) (u : State),
    ⟨u.gpr .rsp, b⟩ ∈ u.wr → (ks ≠ [] → u.xmm .xmm0 = 0) → base + 16 * k ≤ b →
    ∃ m', execBlock isa (stores16 ks off base k) u =
        some ({ u with mem := m' }, storesTr ks off (u.gpr .rsp) base k) ∧
      (∀ x, SCov ks off base k (x - u.gpr .rsp).toNat → m' x = 0) ∧
      (∀ x, ¬ SCov ks off base k (x - u.gpr .rsp).toNat → m' x = u.mem x)
  | 0, u, _, _, _ => ⟨u.mem, rfl, fun _ h => absurd h.2.1 (by have := h.1; omega), fun _ _ => rfl⟩
  | k + 1, u, hR, hx, hk => by
    by_cases hkeep : ks.contains (off + base + 16 * k) = true
    · have hx := hx (fun h => by rw [h] at hkeep; cases hkeep)
      have hin : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (base + 16 * k)) 16 := by
        refine ⟨_, hR, ?_⟩
        simp only [Region.Contains]
        rw [show u.gpr .rsp + BitVec.ofNat 64 (base + 16 * k) - u.gpr .rsp = BitVec.ofNat 64 (base + 16 * k) by
          bv_omega]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      let a := u.gpr .rsp + BitVec.ofNat 64 (base + 16 * k)
      let u₁ : State := { u with mem := u.mem.writeW a (u.xmm .xmm0) }
      obtain ⟨m', he, hz, hu⟩ := stores16_run ks off b base hb k u₁ hR (fun _ => hx) (by omega)
      have hw : ∀ x, u₁.mem x = if base + 16 * k ≤ (x - u.gpr .rsp).toNat ∧
          (x - u.gpr .rsp).toNat < base + 16 * k + 16 then 0 else u.mem x := fun x => by
        simp only [u₁, hx, writeW_zero128, a, off_lt _ _ _ _ (show base + 16 * k + 16 < 2 ^ 64 by omega)]
      refine ⟨m', ?_, fun x h => ?_, fun x h => ?_⟩
      · simp only [stores16, hkeep, ↓reduceIte, List.singleton_append, execBlock, isa, reduceExec, zero16,
          ea_rsp, State.store128, hin]
        rw [show ({ u with mem := u.mem.writeW a (u.xmm .xmm0) } : State) = u₁ from rfl, he]
        simp [storesTr, addrs, ea_rsp2, u₁, List.contains_iff_mem.mp hkeep]
      · obtain ⟨h1, h2, h3⟩ := h
        by_cases hc : (x - u.gpr .rsp).toNat < base + 16 * k
        · exact hz x ⟨h1, hc, h3⟩
        · rw [hu x (fun h' => hc h'.2.1), hw x, ite_t ⟨by omega, by omega⟩]
      · have hk' : ¬ SCov ks off base k (x - u.gpr .rsp).toNat := fun h' => h ⟨h'.1, by have := h'.2.1; omega, h'.2.2⟩
        rw [hu x hk', hw x, ite_f fun hg => h ⟨by omega, by omega, by
          rw [show ((x - u.gpr .rsp).toNat - base) / 16 = k by omega]; exact hkeep⟩]
    · obtain ⟨m', he, hz, hu⟩ := stores16_run ks off b base hb k u hR hx (by omega)
      refine ⟨m', ?_, fun x h => ?_, fun x h => ?_⟩
      · simp only [stores16, hkeep, Bool.false_eq_true, ↓reduceIte, List.nil_append, he, storesTr]
      · obtain ⟨h1, h2, h3⟩ := h
        by_cases hc : (x - u.gpr .rsp).toNat < base + 16 * k
        · exact hz x ⟨h1, hc, h3⟩
        · rw [show ((x - u.gpr .rsp).toNat - base) / 16 = k by omega] at h3
          exact absurd h3 hkeep
      · exact hu x fun h' => h ⟨h'.1, by have := h'.2.1; omega, h'.2.2⟩

theorem writeW_zero64 (m : Mem) (a x : Addr) :
    m.writeW a (0 : BitVec 64) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- What `chunkStores ks off b` zeroes, at offset `d` of `rsp`. -/
def CCov (ks : List Nat) (off b d : Nat) : Prop := d < b ∧ covC ks off b d = true

theorem chunk_run (ks : List Nat) (off b : Nat) (hb : b < 2 ^ 64) (h8 : b % 8 = 0) (u : State)
    (hR : ⟨u.gpr .rsp, b⟩ ∈ u.wr) (hx : ks ≠ [] → u.xmm .xmm0 = 0) (hr : ks ≠ [] → u.gpr .r11 = 0) :
    ∃ m', execBlock isa (chunkStores ks off b) u = some ({ u with mem := m' }, chunkTr ks off (u.gpr .rsp) b) ∧
      (∀ x, CCov ks off b (x - u.gpr .rsp).toNat → m' x = 0) ∧
      (∀ x, ¬ CCov ks off b (x - u.gpr .rsp).toNat → m' x = u.mem x) := by
  obtain ⟨m₁, he, hz, hu⟩ := stores16_run ks off b (b % 16) hb (b / 16) u hR hx (by omega)
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

/-- What `wipe ks cs` from `rsp = p` zeroes. -/
def WCov (ks cs : List Nat) (p x : Addr) : Prop :=
  (⟨p - BitVec.ofNat 64 cs.sum, cs.sum⟩ : Region).Contains x 1 ∧
    cov ks cs (x - (p - BitVec.ofNat 64 cs.sum)).toNat = true

/-- The trace of `wipe ks cs` from `rsp = p`. -/
def wipeTr (ks : List Nat) : List Nat → Addr → List Leak
  | [], _ => []
  | b :: bs, p => chunkTr ks bs.sum (p - BitVec.ofNat 64 b) b ++ wipeTr ks bs (p - BitVec.ofNat 64 b)

theorem wipe_run (ks : List Nat) : ∀ (cs : List Nat) (u : State), (∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) →
    cs.sum ≤ (u.gpr .rsp).toNat → (ks ≠ [] → u.xmm .xmm0 = 0) → (ks ≠ [] → u.gpr .r11 = 0) →
    ∃ m', Exec isa (wipe ks cs) u (wipeTr ks cs (u.gpr .rsp)) { u with mem := m' } ∧
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
    obtain ⟨m₁, he₁, hz₁, hu₁⟩ := chunk_run ks bs.sum b (by omega) hb8 u₁ (by rw [hq]; simp [u₁])
      (by simpa [u₁, State.setReg] using hx) (by simpa [u₁, State.setReg] using hr)
    let u₂ : State := { u₁ with mem := m₁ }
    have hqn : bs.sum ≤ q.toNat := by
      have := p.isLt
      have h' : b + bs.sum ≤ p.toNat := hs
      simp only [q, BitVec.toNat_sub, BitVec.toNat_ofNat]
      generalize p.toNat = P at *
      rw [Nat.mod_eq_of_lt (a := b) (by omega)]
      omega
    obtain ⟨m₂, he₂, hz₂, hu₂⟩ := wipe_run ks bs u₂ (fun b' h => hv b' (List.mem_cons_of_mem _ h))
      (by simpa [u₂, hq] using hqn) (by simpa [u₂, u₁, State.setReg] using hx)
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
      have htr : wipeTr ks (b :: bs) p = (isa.addrs (.alloc b) u).map Leak.addr ++
          (chunkTr ks bs.sum (u₁.gpr .rsp) b ++ wipeTr ks bs (u₂.gpr .rsp)) ++
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
    ymmHi := fun x => if v = .avx ∧ x ∈ xs then 0 else s.ymmHi x
    zmmHi := fun x => if v = .avx ∧ x ∈ xs then 0 else s.zmmHi x }

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

/-- The state `scrubTail v rb xs ps gs ks cs` leaves, given the memory `m'` its wipe leaves. -/
def finState (v : VecLevel) (rb : Nat) (xs : List XReg) (ps gs : List Reg) (m' : Mem) (u : State) : State :=
  clearedG gs
    (({ clearedP ps (clearedV v xs u) with mem := m' } : State).setReg .rax (retVal rb (u.gpr .rax)))

theorem mem_xregs (x : XReg) : x ∈ xregs := by cases x <;> decide

/-- What `scrubTail` needs of what it clears. -/
structure TailOk (rb : Nat) (xs : List XReg) (ps gs : List Reg) (ks : List Nat) : Prop where
  x0 : ks ≠ [] → .xmm0 ∈ xs
  r11 : ks ≠ [] → .r11 ∈ ps
  psOk : ∀ r ∈ ps, r ∈ scratchRegs
  gsOk : ∀ r ∈ gs, r ∈ scratchRegs
  gne : gs ≠ []

theorem tail_run (v : VecLevel) (rb : Nat) {xs : List XReg} {ps gs : List Reg} {ks : List Nat} (cs : List Nat)
    (ht : TailOk rb xs ps gs ks) (u : State)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) (hs : cs.sum ≤ (u.gpr .rsp).toNat) :
    ∃ m', Exec isa (scrubTail v rb xs ps gs ks cs) u (wipeTr ks cs (u.gpr .rsp)) (finState v rb xs ps gs m' u) ∧
      (∀ x, WCov ks cs (u.gpr .rsp) x → m' x = 0) ∧ (∀ x, ¬ WCov ks cs (u.gpr .rsp) x → m' x = u.mem x) := by
  let u₁ := clearedP ps (clearedV v xs u)
  have h₁ : execBlock isa (xs.map (zeroX v) ++ ps.map zeroR) u = some (u₁, []) := by
    rw [execBlock_append, execBlock_vecs]
    simp only [Option.bind_some]
    rw [execBlock_gprsP]
    rfl
  have hsp : u₁.gpr .rsp = u.gpr .rsp := by
    simp only [u₁, clearedP]; split
    · rfl
    · simp only [clearedG, show Reg.rsp ∉ ps from fun h => absurd (ht.psOk _ h) (by decide : Reg.rsp ∉ scratchRegs), ↓reduceIte]; rfl
  have hx0 : ks ≠ [] → u₁.xmm .xmm0 = 0 := fun h => by
    simp only [u₁, clearedP]; split <;> simp [clearedG, clearedV, ht.x0 h]
  have hr11 : ks ≠ [] → u₁.gpr .r11 = 0 := fun h => by
    simp only [u₁, clearedP]; split
    · rename_i hp; exact absurd (ht.r11 h) (by rw [hp]; simp)
    · simp [clearedG, ht.r11 h]
  have hmem : u₁.mem = u.mem := by simp only [u₁, clearedP]; split <;> rfl
  obtain ⟨m', he, ho, hi⟩ := wipe_run ks cs u₁ hv (by rw [hsp]; exact hs) hx0 hr11
  rw [hsp] at he ho hi
  rw [hmem] at hi
  refine ⟨m', ?_, ho, hi⟩
  have h₃ := execBlock_clearGpr rb gs ht.gne (fun h => absurd (ht.gsOk _ h) (by decide : Reg.rax ∉ scratchRegs)) { u₁ with mem := m' }
  have e := Exec.seq (M := isa) (.block h₁) (.seq he (.block h₃))
  simp only [List.nil_append, List.append_nil] at e
  have hax : u₁.gpr .rax = u.gpr .rax := by
    simp only [u₁, clearedP]; split
    · rfl
    · simp only [clearedG, show Reg.rax ∉ ps from fun h => absurd (ht.psOk _ h) (by decide : Reg.rax ∉ scratchRegs), ↓reduceIte]; rfl
  have hf : finState v rb xs ps gs m' u =
      clearedG gs (({ u₁ with mem := m' } : State).setReg .rax (retVal rb (u₁.gpr .rax))) := by
    rw [hax]; rfl
  rw [hf]
  exact e

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

/-! ## The theorem -/

theorem clearedP_gpr {ps : List Reg} {s : State} {r : Reg} :
    (clearedP ps s).gpr r = if r ∈ ps then 0 else s.gpr r := by
  unfold clearedP; split
  · rename_i h; subst h; simp
  · simp [clearedG]

theorem finState_gpr {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State}
    {r : Reg} (hp : r ∉ ps) (hg : r ∉ gs) (h₂ : r ≠ .rax) :
    (finState v rb xs ps gs m' u).gpr r = u.gpr r := by
  simp only [finState, clearedG, State.setReg, hg, h₂, ↓reduceIte, clearedP_gpr, hp]
  rfl

theorem finState_rax {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State}
    (hg : Reg.rax ∉ gs) : (finState v rb xs ps gs m' u).gpr .rax = retVal rb (u.gpr .rax) := by
  simp only [finState, clearedG, State.setReg, hg, ↓reduceIte]

theorem finState_xmm {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State} :
    (finState v rb xs ps gs m' u).xmm = fun x => if x ∈ xs then 0 else u.xmm x := by
  simp only [finState, clearedG, State.setReg, clearedP]; split <;> rfl

theorem finState_ymmHi {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State} :
    (finState v rb xs ps gs m' u).ymmHi = fun x => if v = .avx ∧ x ∈ xs then 0 else u.ymmHi x := by
  simp only [finState, clearedG, State.setReg, clearedP]; split <;> rfl

theorem finState_zmmHi {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State} :
    (finState v rb xs ps gs m' u).zmmHi = fun x => if v = .avx ∧ x ∈ xs then 0 else u.zmmHi x := by
  simp only [finState, clearedG, State.setReg, clearedP]; split <;> rfl

theorem finState_other {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {u : State} :
    (finState v rb xs ps gs m' u).mem = m' ∧ (finState v rb xs ps gs m' u).rd = u.rd ∧
      (finState v rb xs ps gs m' u).wr = u.wr ∧ (finState v rb xs ps gs m' u).ymmH = u.ymmH ∧
      (finState v rb xs ps gs m' u).zmmHiH = u.zmmHiH ∧ (finState v rb xs ps gs m' u).mxcsr = u.mxcsr ∧
      (finState v rb xs ps gs m' u).cf = some false ∧ (finState v rb xs ps gs m' u).zf = some true ∧
      (finState v rb xs ps gs m' u).sf = some false ∧ (finState v rb xs ps gs m' u).of = some false := by
  simp only [finState, clearedG, State.setReg, clearedP]; split <;> simp [clearedV]

theorem slot_not_below {sp x : Addr} {n : Nat} (hn : n + 8 < 2 ^ 64)
    (hx : (⟨sp, 8⟩ : Region).Contains x 1) : ¬ (⟨sp - BitVec.ofNat 64 n, n⟩ : Region).Contains x 1 := by
  have := sp.isLt; have := x.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_ofNat] at hx ⊢
  generalize sp.toNat = P at *
  generalize x.toNat = X at *
  rw [Nat.mod_eq_of_lt (a := n) (by omega)]
  omega

/-- Two runs of `c` leave the same bytes in the `stack` bytes below the stack
pointer on entry but those `wipe ks cs` zeroes. -/
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
      ∃ m', t' = wipeTr ks cs (s.gpr .rsp) ∧ s' = finState v (sig.retBits A.ptrBits) xs ps gs m' u ∧
        (∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x) ∧
        (∀ x, WCov ks cs (s.gpr .rsp) x → m' x = 0) ∧ (∀ x, ¬ WCov ks cs (s.gpr .rsp) x → m' x = u.mem x) := by
    intro s t u s' t' hs he het
    obtain ⟨-, -, hr, hl⟩ := run s t u hs he
    obtain ⟨m', e, hz, hu⟩ := tail_run v (sig.retBits A.ptrBits) cs ht u hv hl
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
    obtain ⟨m', et, hz, hu⟩ := tail_run v (sig.retBits A.ptrBits) cs ht u hv hl
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
    · rw [finState_other.2.2.2.2.2.1]; exact ha.2.2
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
    have k1₁ := Exec.vecKeep1 (fun i hi => by have := hlv i hi; cases v <;> simp [VecLevel.level] at this ⊢ <;> omega) a₁
    have k1₂ := Exec.vecKeep1 (fun i hi => by have := hlv i hi; cases v <;> simp [VecLevel.level] at this ⊢ <;> omega) a₂
    simp only [vk1, Prod.mk.injEq] at k1₁ k1₂
    have hdep : c.x86_64Depth < 2 ^ 64 := by omega
    have f₁ := Exec.stackFrame hsp a₁ hdep
    have f₂ := Exec.stackFrame hsp a₂ hdep
    have cs_ : ∀ r : Reg, r ∉ scratchRegs → r ≠ .rax → r ∈ calleeSaved := by intro r; cases r <;> decide
    -- With the vector registers' upper halves kept: code of level 0, or that writes none.
    have l0 : (∃ x, x ∉ xs ∧ v = .avx) → ∀ i ∈ instrs c, i.vecLevel = 0 := by
      rintro ⟨x, hx, -⟩ i hi
      rcases hxs with h | h
      · exact absurd (h x) hx
      · exact vecLevel_of_writesVec (h i hi)
          (by have := hlv i hi; cases v <;> simp [VecLevel.level] at this ⊢ <;> omega)
    have upper : ∀ x, ¬ (v = .avx ∧ x ∈ xs) → u₁.ymmHi x = u₂.ymmHi x ∧ u₁.zmmHi x = u₂.zmmHi x := by
      intro x hn
      have hl : ∀ i ∈ instrs c, i.vecLevel = 0 := by
        cases v
        · exact fun i hi => by simpa [VecLevel.level] using hlv i hi
        · exact l0 ⟨x, fun h => hn ⟨rfl, h⟩, rfl⟩
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
    · rw [finState_other.2.2.2.1, finState_other.2.2.2.1, k1₁.1, k1₂.1, hyH]
    · rw [finState_other.2.2.2.2.1, finState_other.2.2.2.2.1, k1₁.2.1, k1₂.2.1, hzH]
    · rw [finState_other.2.2.2.2.2.1, finState_other.2.2.2.2.2.1, k1₁.2.2, k1₂.2.2, hmx]
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

theorem stores16_spSafe (ks : List Nat) (off base : Nat) :
    ∀ k, (stores16 ks off base k).all (fun i => !isa.writesSp i) = true
  | 0 => rfl
  | k + 1 => by
    simp only [stores16, List.all_append, stores16_spSafe ks off base k, Bool.and_true]
    split <;> rfl

theorem wipe_spSafe (ks : List Nat) : ∀ cs : List Nat, (wipe ks cs).all (fun i => !isa.writesSp i) = true
  | [] => rfl
  | b :: bs => by
    simp only [wipe, Code.all, chunkStores, List.all_append, stores16_spSafe, wipe_spSafe ks bs,
      Bool.true_and, Bool.and_true, store8s]
    split <;> rfl

theorem zeroR_spSafe : ∀ r ∈ scratchRegs, (!isa.writesSp (zeroR r)) = true := by decide

theorem scrub_spSafe {c : Prog isa} (v : VecLevel) (rb : Nat) (xs : List XReg) (ps gs : List Reg)
    (ks cs : List Nat) (hps : ∀ r ∈ ps, r ∈ scratchRegs) (hgs : ∀ r ∈ gs, r ∈ scratchRegs)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrub v rb xs ps gs ks cs c).all (fun i => !isa.writesSp i) = true := by
  have hv : (xs.map (zeroX v) ++ ps.map zeroR).all (fun i => !isa.writesSp i) = true := by
    simp only [List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun x _ => by cases v <;> rfl, fun r hr => zeroR_spSafe r (hps r hr)⟩
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
  rw [h, hv, wipe_spSafe ks cs, hg]
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

/-- `r`'s code, scrubbed as `scrubReg` does, returns without secret residue. -/
theorem scrubCode_noResidue {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack)) :
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
    (fun i hi => by simpa using Code.all_instrs hlv i hi) hrb' hp hr (tailOk_of _ _ _) (xs_of _ _) (gs_of _ _)).2

/-- `r`, scrubbed: its code followed by the clearing (`scrub`), at level `v`,
with the granules `ks` of `r.stack` bytes of stack wiped. -/
def scrubReg {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack))
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
      (fun i hi => by simpa using Code.all_instrs hlv i hi) hrb' hp hr (tailOk_of _ _ _) (xs_of _ _) (gs_of _ _)).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrub_spSafe v _ _ _ _ _ _ (tailOk_of 0 r.code ks).psOk (tailOk_of 0 r.code ks).gsOk r.spSafe
  features := r.features
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  residue := some ⟨scrubCode_noResidue r v ks hd hst h8 hlv hrb hpost hres⟩

theorem scrubReg_noResidue {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack)) (hw : r.written = []) :
    NoResidue (scrubReg r v ks hd hst h8 hlv hrb hpost hres hw).code r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) :=
  scrubCode_noResidue r v ks hd hst h8 hlv hrb hpost hres

end VG.X86_64.Scrub
