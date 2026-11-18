module

public import VerifiedGarbage.Proof.Framework.AArch64.Residue
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Code reads and writes memory only inside its regions (AArch64)

`exec_in`: an instruction runs from a state whose memory is replaced by one
that agrees with it inside its regions (`MemIn`) as it runs from the state
itself: it reads memory only inside the regions (loads fault outside them),
and writes there the same bytes (stores fault outside the writable ones).
The two memories then still agree inside the regions, and the replaced one
is unchanged outside the writable regions. `push_in` and `pop_in` say the
same of the push and the pop of a frame.

So a run is determined, but for memory outside its regions, by the memory
inside them: a residue analysis may compare a run with one whose memory
outside the regions is another run's, where the two runs' memories outside
the regions differ (a released frame's bytes, below the stack pointer).
-/

@[expose] public section

namespace VG.AArch64.Residue

open VG.AArch64

/-- The memories `m₁` and `m₂` agree inside the regions `rs`. -/
def MemIn (rs : List Region) (m₁ m₂ : Mem) : Prop :=
  ∀ x, (∃ r ∈ rs, r.Contains x 1) → m₁ x = m₂ x

theorem contains_of_off {r : Region} {a x : Addr} {n : Nat} (h : r.Contains a n)
    (hx : (x - a).toNat < n) : r.Contains x 1 := by
  unfold Region.Contains at h ⊢
  rw [show x - r.base = (x - a) + (a - r.base) by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add]
    omega, BitVec.toNat_add]
  have := Nat.mod_le ((x - a).toNat + (a - r.base).toNat) (2 ^ 64)
  omega

theorem off_ofNat_lt {a : Addr} {i n : Nat} (h : i < n) :
    (a + BitVec.ofNat 64 i - a).toNat < n := by
  rw [BitVec.add_sub_comm, BitVec.sub_self, BitVec.zero_add, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

theorem read_in {rs : List Region} {m₁ m₂ : Mem} (hm : MemIn rs m₁ m₂) {a : Addr} {n : Nat}
    (h : InRegions rs a n) : m₁.read a n = m₂.read a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact Mem.read_congr fun i hi => hm _ ⟨r, hr, contains_of_off hc (off_ofNat_lt hi)⟩

theorem memIn_write {rs : List Region} {m₁ m₂ : Mem} (hm : MemIn rs m₁ m₂) (a : Addr) (n : Nat)
    (v : BitVec (8 * n)) : MemIn rs (m₁.write a n v) (m₂.write a n v) := by
  intro x hx
  simp only [Mem.write]
  split
  · rfl
  · exact hm x hx

/-- A write within the regions `ws` leaves memory outside them as it was. -/
theorem memOff_write_in {ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) (m : Mem)
    (v : BitVec (8 * n)) : MemOff ws m (m.write a n v) := by
  intro x hx
  simp only [Mem.write]
  split
  · rename_i hlt
    obtain ⟨r, hr, hc⟩ := h
    exact absurd (contains_of_off hc hlt) (hx r hr)
  · rfl

theorem memIn_mono {rs rs' : List Region} {m₁ m₂ : Mem} (hm : MemIn rs m₁ m₂)
    (h : ∀ r ∈ rs', r ∈ rs) : MemIn rs' m₁ m₂ :=
  fun x ⟨r, hr, hc⟩ => hm x ⟨r, h r hr, hc⟩

/-- `s`, with its memory replaced by `m`. -/
abbrev _root_.VG.AArch64.State.withM (s : State) (m : Mem) : State := s.withMS m s.syms

theorem load_in {s : State} {m : Mem} (hm : MemIn (s.rd ++ s.wr) s.mem m) (a : Addr) (n : Nat) :
    (s.withM m).load a n = s.load a n := by
  simp only [State.load]
  split
  · rename_i h
    rw [read_in hm h]
  · rfl

theorem store_in {s t : State} {m : Mem} (hm : MemIn (s.rd ++ s.wr) s.mem m) {a : Addr} {n : Nat}
    {v : BitVec (8 * n)} (h : s.store a n v = some t) :
    (s.withM m).store a n v = some (t.withM (m.write a n v)) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.syms = s.syms ∧ MemIn (t.rd ++ t.wr) t.mem (m.write a n v) ∧
      MemOff s.wr m (m.write a n v) := by
  simp only [State.store] at h ⊢
  split at h
  · rename_i hin
    obtain rfl := Option.some.inj h
    rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]
    exact ⟨rfl, rfl, rfl, rfl, memIn_write hm a n v, memOff_write_in hin m v⟩
  · cases h

/-- What `exec_in` says of a run of `i` from `s` to `t`, and from `s.withM m`. -/
def RunIn (s t : State) (m : Mem) (t' : Option State) : Prop :=
  ∃ m', t' = some (t.withM m') ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms ∧
    MemIn (t.rd ++ t.wr) t.mem m' ∧ MemOff s.wr m m'

theorem runIn_store {s t : State} {m : Mem} (hm : MemIn (s.rd ++ s.wr) s.mem m) {a : Addr}
    {n : Nat} {v : BitVec (8 * n)} (h : s.store a n v = some t) :
    RunIn s t m ((s.withM m).store a n v) := by
  obtain ⟨e, h₁, h₂, h₃, h₄, h₅⟩ := store_in hm h
  exact ⟨_, e, h₁, h₂, h₃, h₄, h₅⟩

theorem runIn_same {s t : State} {m : Mem} (hm : MemIn (s.rd ++ s.wr) s.mem m)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsy : t.syms = s.syms) (hmem : t.mem = s.mem) :
    RunIn s t m (some (t.withM m)) :=
  ⟨m, rfl, hrd, hwr, hsy, by rw [hrd, hwr, hmem]; exact hm, fun _ _ => rfl⟩

/-- An instruction runs from `s.withM m`, where `m` agrees with `s`'s memory
inside its regions, as from `s`, but for the memory outside the regions,
which it leaves as `m` has it outside the writable ones. -/
theorem exec_in {i : Instr} {s t : State} {m : Mem} (hm : MemIn (s.rd ++ s.wr) s.mem m)
    (h : exec i s = some t) : RunIn s t m (exec i (s.withM m)) := by
  by_cases hr : regOnly i = true
  · rw [exec_withMS hr, h]
    obtain ⟨hrd, hwr, hmem⟩ := exec_regOnly hr h
    have hsy : t.syms = s.syms := by
      cases i <;> cases hr
      all_goals
        simp only [exec] at h
        first
        | (obtain rfl := Option.some.inj h; rfl)
        | (split at h <;> first | (obtain rfl := Option.some.inj h; rfl) | cases h)
        | (cases he : VOp.eval s _ with
            | none => rw [he] at h; cases h
            | some p => rw [he] at h; obtain rfl := Option.some.inj h; rfl)
        | (split at h <;> (try split at h) <;>
            first | (obtain rfl := Option.some.inj h; rfl) | cases h)
    rw [Option.map_some, ← hsy]
    exact runIn_same hm hrd hwr hsy hmem
  · cases i <;> simp only [regOnly, Bool.false_eq_true, not_false_eq_true, not_true_eq_false] at hr
    case ldr sz d n off =>
      simp only [exec, addr_withMS] at h ⊢
      cases ha : addr s sz.bytes n off with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h; simp only [Option.bind_some] at h ⊢
        rw [load_in hm]
        cases hl : s.load a sz.bytes with
        | none => rw [hl] at h; cases h
        | some v =>
          rw [hl] at h; obtain rfl := Option.some.inj h
          exact runIn_same hm rfl rfl rfl rfl
    case ldrb d n off =>
      simp only [exec, addr_withMS] at h ⊢
      cases ha : addr s 1 n off with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h; simp only [Option.bind_some] at h ⊢
        rw [load_in hm]
        cases hl : s.load a 1 with
        | none => rw [hl] at h; cases h
        | some v =>
          rw [hl] at h; obtain rfl := Option.some.inj h
          exact runIn_same hm rfl rfl rfl rfl
    case ldrq d n off =>
      simp only [exec, addr_withMS] at h ⊢
      cases ha : addr s 16 n off with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h; simp only [Option.bind_some] at h ⊢
        rw [load_in hm]
        cases hl : s.load a 16 with
        | none => rw [hl] at h; cases h
        | some v =>
          rw [hl] at h; obtain rfl := Option.some.inj h
          exact runIn_same hm rfl rfl rfl rfl
    case ldrSp d off =>
      simp only [exec] at h ⊢
      split at h
      · rename_i hc
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc), load_in hm]
        cases hl : s.load (s.sp + BitVec.ofNat 64 off) 8 with
        | none => rw [hl] at h; cases h
        | some v =>
          rw [hl] at h; obtain rfl := Option.some.inj h
          exact runIn_same hm rfl rfl rfl rfl
      · cases h
    case ldp d₁ d₂ n off =>
      simp only [exec] at h ⊢
      split at h
      · rename_i hc
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc), load_in hm, load_in hm]
        cases hl : s.load (s.gpr n + BitVec.ofNat 64 off) 8 with
        | none => rw [hl] at h; cases h
        | some v =>
          rw [hl] at h
          simp only [Option.bind_some] at h ⊢
          cases hl' : s.load (s.gpr n + BitVec.ofNat 64 off + 8) 8 with
          | none => rw [hl'] at h; cases h
          | some v' =>
            rw [hl'] at h; obtain rfl := Option.some.inj h
            exact runIn_same hm rfl rfl rfl rfl
      · cases h
    case str sz d n off =>
      simp only [exec, addr_withMS] at h ⊢
      cases ha : addr s sz.bytes n off with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h; simp only [Option.bind_some] at h ⊢
        exact runIn_store hm h
    case strb d n off =>
      simp only [exec, addr_withMS] at h ⊢
      cases ha : addr s 1 n off with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h; simp only [Option.bind_some] at h ⊢
        exact runIn_store hm h
    case strq d n off =>
      simp only [exec, addr_withMS] at h ⊢
      cases ha : addr s 16 n off with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h; simp only [Option.bind_some] at h ⊢
        exact runIn_store hm h
    case strSp d off =>
      simp only [exec] at h ⊢
      split at h
      · rename_i hc
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
        exact runIn_store hm h
      · cases h
    case stp d₁ d₂ n off =>
      simp only [exec] at h ⊢
      split at h
      · rename_i hc
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
        obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨e₁, r₁, w₁, y₁, i₁, o₁⟩ := store_in hm hu
        change RunIn s t m (((s.withM m).store _ 8 ((s.read .x d₁).setWidth 64)).bind
          fun s' => s'.store _ 8 ((s.read .x d₂).setWidth 64))
        rw [e₁, Option.bind_some]
        obtain ⟨e₂, r₂, w₂, y₂, i₂, o₂⟩ := store_in i₁ h
        refine ⟨_, ?_, r₂.trans r₁, w₂.trans w₁, y₂.trans y₁, i₂, fun x hx => ?_⟩
        · rw [← e₂]
        · rw [← o₂ x (by rw [w₁]; exact hx), o₁ x hx]
      · cases h
    case ldrqTbl d n off name ws =>
      simp only [exec] at h ⊢
      split at h
      · rename_i hc
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; obtain rfl := Option.some.inj h
        exact runIn_same hm rfl rfl rfl rfl
      · cases h
    case ldrTbl sz d n off name ws =>
      simp only [exec] at h ⊢
      split at h
      · rename_i hc
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; obtain rfl := Option.some.inj h
        exact runIn_same hm rfl rfl rfl rfl
      · cases h
    case ccmp sz n imm nzcv cond =>
      have e : exec (.ccmp sz n imm nzcv cond) (s.withM m) =
          (exec (.ccmp sz n imm nzcv cond) s).map (·.withM m) := by
        simp only [exec, show CondCode.holds (s.withM m) cond = CondCode.holds s cond from rfl]
        split
        · rw [Option.map_some]; split <;> rfl
        · rfl
      rw [e, h, Option.map_some]
      simp only [exec] at h
      split at h
      · obtain rfl := Option.some.inj h
        split <;> exact runIn_same hm rfl rfl rfl rfl
      · cases h
    case adrSym d name =>
      simp only [exec] at h ⊢
      obtain rfl := Option.some.inj h
      exact runIn_same hm rfl rfl rfl rfl
    all_goals simp only [exec] at h; cases h

end VG.AArch64.Residue
