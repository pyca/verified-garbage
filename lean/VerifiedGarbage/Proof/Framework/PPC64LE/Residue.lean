module

public import VerifiedGarbage.Proof.Framework.RelSteps
public import VerifiedGarbage.TCB.PPC64LE.Residue

/-!
# Returning without secret residue, for code that reads no memory (PPC64LE)

`noResidue_of_blind`: code made of blocks, sequences, branches and loops
(`Code.plainAll`) whose every instruction is `blind`, reading neither memory
nor the address of a static (`syms`, which `Outside` does not relate), returns
without secret residue (`PPC64LE.NoResidue`), whatever its contract.

Two such runs from states that agree outside the buffers (`Outside 0`, and the
same `unknowns` and `undef`) stay in states that differ in their memory and `syms` only,
and in their memory only inside the regions (`Off`): every register an
instruction writes is computed from registers, `unknowns` and `undef` (`mtvsrd`), which
agree, and every store writes the same bytes at the same address in both, so
that the bytes outside the regions, which agree, stay so. Their conditions read
registers only, and so agree, and their instructions access the same addresses
(`RelCT.of_steps`). At the end, the two runs therefore agree outside the
buffers (`Outside r`) for any `r`.
-/

@[expose] public section

namespace VG.PPC64LE

/-- `s` with the memory `m` and the addresses of statics `y`. -/
abbrev State.withMS (s : State) (m : Mem) (y : String → BitVec 64) : State :=
  { s with mem := m, syms := y }

namespace Residue

/-- The memories `m₁` and `m₂` agree outside the regions `rs`. -/
def MemOff (rs : List Region) (m₁ m₂ : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, ¬ r.Contains x 1) → m₁ x = m₂ x

/-- Two states differ only in their memory inside their regions, and in the
addresses of their statics. -/
def Off (s₁ s₂ : State) : Prop :=
  s₂ = s₁.withMS s₂.mem s₂.syms ∧ MemOff (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

theorem off_of_outside {s₁ s₂ : State} (h : Outside 0 s₁ s₂) (hu : s₁.unknowns = s₂.unknowns)
    (hf : s₁.undef = s₂.undef) :
    Off s₁ s₂ := by
  obtain ⟨hrd, hwr, hg, hr3, hv, hl, hsp, hc, hm⟩ := h
  refine ⟨?_, hm⟩
  have hg' : s₂.gpr = s₁.gpr := by
    funext r
    by_cases hr : r = .r3
    · subst hr; simpa using hr3.symm
    · exact (hg r hr).symm
  cases s₁; cases s₂
  simp only at hrd hwr hv hl hsp hc hu hf hg' ⊢
  subst hrd hwr hv hl hsp hc hu hf hg'
  rfl

theorem outside_of_off {s₁ s₂ : State} (h : Off s₁ s₂) (r : Nat) : Outside r s₁ s₂ := by
  obtain ⟨he, hm⟩ := h
  rw [he]
  exact ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, hm⟩

/-- The instructions whose run reads and writes only registers, `LR`, CA, the
vector registers and `unknowns`, never memory or `syms`. -/
def regOnly : Instr → Bool
  | .add .. | .sub .. | .mul .. | .mulhu .. | .addc .. | .adde .. | .addze ..
  | .subc .. | .sube .. | .addi .. | .subi .. | .li .. | .lis .. | .ori .. | .oris ..
  | .logic .. | .rotr .. | .lsr .. | .lsl .. | .mflr .. | .mtlr .. | .addSp ..
  | .vop .. | .mtvsrd .. | .mfvsrd .. => true
  | _ => false

/-- The stores, which write memory from registers. -/
def isStore : Instr → Bool
  | .store .. | .stb .. | .storeRev .. | .stxvd2x .. => true
  | _ => false

/-- The instructions that read no memory and no `syms`. -/
def blind (i : Instr) : Bool := regOnly i || isStore i

/-- A register-only instruction runs on `s.withMS m y` as on `s`, keeping `m`
and `y`. -/
theorem exec_withMS {i : Instr} (hi : regOnly i = true) (s : State) (m : Mem)
    (y : String → BitVec 64) :
    exec i (s.withMS m y) = (exec i s).map fun t => t.withMS m y := by
  cases i <;> simp only [regOnly, Bool.false_eq_true] at hi
  all_goals first
    | rfl
    | (simp only [exec]; split <;> rfl)
    | (simp only [exec]; cases VOp.eval s.vpr _ <;> rfl)

/-- A register-only instruction changes neither the regions nor the memory. -/
theorem exec_regOnly {i : Instr} (hi : regOnly i = true) {s t : State} (h : exec i s = some t) :
    t.rd = s.rd ∧ t.wr = s.wr ∧ t.mem = s.mem := by
  cases i <;> simp only [regOnly, Bool.false_eq_true] at hi
  all_goals
    simp only [exec] at h
    first
    | (obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, rfl⟩)
    | (split at h <;> first | (obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, rfl⟩) | cases h)
    | (cases he : VOp.eval s.vpr _ with
        | none => rw [he] at h; cases h
        | some p => rw [he] at h; obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, rfl⟩)

theorem memOff_write {rs : List Region} {m₁ m₂ : Mem} (h : MemOff rs m₁ m₂) (a : Addr) (n : Nat)
    (v : BitVec (8 * n)) : MemOff rs (m₁.write a n v) (m₂.write a n v) := by
  intro x hx
  simp only [Mem.write]
  split
  · rfl
  · exact h x hx

theorem addrs_withMS (i : Instr) (s : State) (m : Mem) (y : String → BitVec 64) :
    addrs i (s.withMS m y) = addrs i s := by
  cases i <;> rfl

theorem eval_withMS (c : Cond) (s : State) (m : Mem) (y : String → BitVec 64) :
    eval c (s.withMS m y) = eval c s := by
  cases c <;> rfl

theorem addr_withMS (s : State) (m : Mem) (y : String → BitVec 64) (n : Nat) (r : Reg) (o : Nat) :
    addr (s.withMS m y) n r o = addr s n r o := rfl

theorem addrX_withMS (s : State) (m : Mem) (y : String → BitVec 64) (a b : Reg) :
    addrX (s.withMS m y) a b = addrX s a b := rfl

/-- A store of `n` bytes on two states that differ as `Off` says. -/
theorem off_store {s : State} {m : Mem} {y : String → BitVec 64} (hm : MemOff (s.rd ++ s.wr) s.mem m)
    {a : Addr} {n : Nat} {v : BitVec (8 * n)} {t₁ t₂ : State} (h₁ : s.store a n v = some t₁)
    (h₂ : (s.withMS m y).store a n v = some t₂) : Off t₁ t₂ := by
  simp only [State.store] at h₁ h₂
  split at h₁
  · obtain rfl := Option.some.inj h₁
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))] at h₂
    obtain rfl := Option.some.inj h₂
    exact ⟨rfl, memOff_write hm a n v⟩
  · cases h₁

/-- A store at the address `ea` that both runs compute. -/
theorem off_store_bind {s : State} {m : Mem} {y : String → BitVec 64}
    (hm : MemOff (s.rd ++ s.wr) s.mem m) {ea : Option Addr} {n : Nat} {v : BitVec (8 * n)}
    {t₁ t₂ : State} (h₁ : ea.bind (fun a => s.store a n v) = some t₁)
    (h₂ : ea.bind (fun a => (s.withMS m y).store a n v) = some t₂) : Off t₁ t₂ := by
  cases ea with
  | none => cases h₁
  | some a => exact off_store hm h₁ h₂

/-- Off is kept by a blind instruction, which accesses the same addresses in
both runs. -/
theorem off_step {i : Instr} (hi : blind i = true) {s₁ s₂ a b : State} (h : Off s₁ s₂)
    (h₁ : exec i s₁ = some a) (h₂ : exec i s₂ = some b) :
    Off a b ∧ addrs i s₁ = addrs i s₂ := by
  obtain ⟨he, hm⟩ := h
  generalize s₂.mem = m, s₂.syms = y at he
  subst he
  refine ⟨?_, (addrs_withMS i s₁ m y).symm⟩
  rcases Bool.or_eq_true_iff.mp hi with hr | hs
  · rw [exec_withMS hr, h₁] at h₂
    obtain rfl := Option.some.inj h₂
    obtain ⟨hrd, hwr, hmem⟩ := exec_regOnly hr h₁
    exact ⟨rfl, by rw [hrd, hwr, hmem]; exact hm⟩
  · cases i <;> simp only [isStore, Bool.false_eq_true] at hs
    case store sz t n off =>
      simp only [exec, addr_withMS] at h₁ h₂
      exact off_store_bind hm h₁ h₂
    case stb t n off =>
      simp only [exec, addr_withMS] at h₁ h₂
      exact off_store_bind hm h₁ h₂
    case stxvd2x n a b =>
      simp only [exec, addrX_withMS] at h₁ h₂
      exact off_store_bind hm h₁ h₂
    case storeRev sz t a b =>
      cases sz <;> simp only [exec, addrX_withMS] at h₁ h₂ <;> exact off_store_bind hm h₁ h₂

/-- Plain code of blind instructions (`Code.plainAll blind`) returns without
secret residue, whatever its contract. -/
theorem noResidue_of_blind {c : Prog isa} (hc : c.plainAll blind = true) (k : Contract isa)
    (r : Nat) : NoResidue c k r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ _ ho hu hf e₁ e₂
  have hrel : RelCT isa Off c Off :=
    RelCT.of_steps (p := blind) (fun _ hi _ _ _ _ h h₁ h₂ => off_step hi h h₁ h₂)
      (fun c s₁ s₂ h => by
        obtain ⟨he, -⟩ := h
        rw [he]
        exact (eval_withMS c s₁ _ _).symm) hc
  exact outside_of_off (hrel _ _ _ _ _ _ (off_of_outside ho hu hf) e₁ e₂).2 r

end Residue

end VG.PPC64LE
