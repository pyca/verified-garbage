module

public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
public import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Compress
public import VerifiedGarbage.Impl.Sha512.X86_64.Stream
public import VerifiedGarbage.Proof.Sha512.X86_64.Compress
public import VerifiedGarbage.Proof.Sha512.X86_64.Wide
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Sha512.Md
meta import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Compress
meta import VerifiedGarbage.Impl.Sha512.X86_64.Stream
meta import VerifiedGarbage.Proof.Sha512.X86_64.Compress
meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Compress
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Compress
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Impl.Sha512.X86_64.Rolled
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Sha512.X86_64.Wide
meta import VerifiedGarbage.Impl.Sha512.X86_64.Rolled
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Compress
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `Sha512.X86_64.Avx2Rolled.CT`, which this module and modules that import it used -/

section

/-!
# SHA-512 with AVX2 on x86-64, rolled: constant time

The taint analysis checks the prologue, the halves of a lone block and of
a pair (`first false`, `loneRest`, `first true`, `pairRest`), the test of
the count before the pairs and the epilogue, each from the pointers and the
block count being public. It cannot check a pair in one go: `first` keeps
`rdi` and `rdx` in the scratch space while the schedule stores secret words
through the index, at offsets the analysis cannot bound, so it forgets that
the slots hold public values. The proof composes the checks (`RelCT`): at
the start of each part, the registers it needs public agree in both runs
because each run's correctness (`Compress.lean`) says what they hold, which
the public data determines.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx2.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2Rolled
open VG.Proof.Sha512.X86_64 (st bp nb scr stR blR retR blkAddr)

/-- The public data: the pointers and the block count. The table's address
need not be: its reads are observed as offsets in it (`aluTbl`). -/
def PubK (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx

abbrev A : VG.Taint isa := taint

/-- The pointers and the count are public; `rdi` and `rcx` point at the
hash value and the scratch space. -/
def τA : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx], flags := false, lens := [64, 1328],
    bases := [(.rdi, 0, 0), (.rcx, 1, 0)] }

/-- The epilogue's: the scratch space's address is public. -/
def τR : X86_64.Taint.T := { regs := .ofList [.rcx], flags := false }

theorem agreeA {s₁ s₂ : State}
    (hr : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx], s₁.gpr r = s₂.gpr r)
    (hw₁ : s₁.wr = [⟨s₁.gpr .rdi, 64⟩, ⟨s₁.gpr .rcx, 1328⟩])
    (hw₂ : s₂.wr = [⟨s₂.gpr .rdi, 64⟩, ⟨s₂.gpr .rcx, 1328⟩])
    (hd₁ : Region.Disjoint ⟨s₁.gpr .rdi, 64⟩ ⟨s₁.gpr .rcx, 1328⟩)
    (hd₂ : Region.Disjoint ⟨s₂.gpr .rdi, 64⟩ ⟨s₂.gpr .rcx, 1328⟩) : A.Agree τA s₁ s₂ := by
  have wf : ∀ s : State, s.wr = [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .rcx, 1328⟩] →
      Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, 1328⟩ → X86_64.Taint.Wf τA s := by
    intro s hw hd
    refine ⟨fun _ => ⟨by simp [hw, τA], by simp [hw, hd], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr' => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ hw₁ hd₁, wf _ hw₂ hd₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τA, RegSet.mem_ofList] at hr'
    exact hr r hr'
  · rw [hw₁, hw₂, hr .rdi (by simp), hr .rcx (by simp)]
  · intro sl h; simp [τA] at h
  · intro sl h; simp [τA] at h

theorem agreeR {s₁ s₂ : State} (hrcx : s₁.gpr .rcx = s₂.gpr .rcx) : A.Agree τR s₁ s₂ := by
  refine ⟨⟨fun r hr' => ?_, fun h => by cases h⟩, fun h => absurd rfl h, ⟨fun h => absurd rfl h, ?_⟩,
    ⟨fun h => absurd rfl h, ?_⟩, ?_, ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τR, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'; exact hrcx
  · intro p hp; simp [τR] at hp
  · intro p hp; simp [τR] at hp
  · intro sl h; simp [τR] at h
  · intro sl h; simp [τR] at h

/-! ## The parts -/

theorem first_rel (keep : Bool) {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τA s₁ s₂) :
    RelCT isa P (first keep) fun _ _ => True := by
  cases keep
  · exact RelCT.taint (A := A) τA hp (by taint_decide)
  · exact RelCT.taint (A := A) τA hp (by taint_decide)

theorem loneRest_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τA s₁ s₂) :
    RelCT isa P (.block loneRest) fun _ _ => True :=
  RelCT.taint (A := A) τA hp (by taint_decide)

theorem pairRest_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τA s₁ s₂) :
    RelCT isa P pairRest fun _ _ => True :=
  RelCT.taint (A := A) τA hp (by taint_decide)

theorem pro_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τA s₁ s₂) :
    RelCT isa P (.block (save ++ Impl.Sha512.X86_64.Avx2.const Impl.Sha512.X86_64.Avx2.mBswap
      Impl.Sha512.X86_64.Avx2.bswapMask ++ ([.alu .test .rdx (.imm 1)] : List Instr))) fun _ _ => True :=
  RelCT.taint (A := A) τA hp (by taint_decide)

theorem test_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τA s₁ s₂) :
    RelCT isa P (.block [.alu .test .rdx (.reg .rdx)]) fun _ _ => True :=
  RelCT.taint (A := A) τA hp (by taint_decide)

theorem res_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τR s₁ s₂) :
    RelCT isa P (.block restore) fun _ _ => True :=
  RelCT.taint (A := A) τR hp (by taint_decide)

theorem wipe_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τR s₁ s₂) :
    RelCT isa P (.block wipe) fun _ _ => True :=
  RelCT.taint (A := A) τR hp (by taint_decide)

theorem rel_nil {P : State → State → Prop} : RelCT isa P (.block []) fun s₁ s₂ => P s₁ s₂ := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁; obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hP⟩

/-! ## The whole function -/

/-- What the prologue leaves (`prologue_ok`). -/
def ProPost (s₀ s₁ : State) : Prop :=
  (∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
    s₁.syms = s₀.syms ∧ s₁.zf = some (s₀.gpr .rdx &&& BitVec.signExtend 64 (1 : BitVec 32) == 0) ∧ Masks s₁

theorem ProPost.linv {s₀ s₁ : State} (hp : Pre s₀) (h : ProPost s₀ s₁) : LInv s₀ 0 s₁ :=
  { common_zero hp h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2 with
    rsi := by rw [h.1 _ (by decide)]; simp [blkAddr]
    rdx := by rw [h.1 _ (by decide)]; simp [nb] }

theorem wr_eq {s₀ s : State} (hp : Pre s₀) (hw : s.wr = s₀.wr) (hrdi : s.gpr .rdi = st s₀)
    (hrcx : s.gpr .rcx = scr s₀) : s.wr = [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .rcx, 1328⟩] := by
  rw [hw, hp.wr, hrdi, hrcx]

theorem st_scr' {s₀ s : State} (hp : Pre s₀) (hrdi : s.gpr .rdi = st s₀) (hrcx : s.gpr .rcx = scr s₀) :
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, 1328⟩ := by
  rw [hrdi, hrcx]; exact hp.st_scr

theorem compress_rel {σ₁ σ₂ : State} (h₁ : Pre σ₁) (h₂ : Pre σ₂) (hpub : PubK σ₁ σ₂) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) compress fun _ _ => True := by
  obtain ⟨e_rdi, e_rsi, e_rdx, e_rcx⟩ := hpub
  have hnb : nb σ₂ = nb σ₁ := by simp only [nb, e_rdx]
  have hpro := (pro_rel (P := fun a b => a = σ₁ ∧ b = σ₂) fun a b ⟨ha, hb⟩ => by
    subst ha hb
    exact agreeA (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption)
      (wr_eq h₁ rfl rfl rfl) (wr_eq h₂ rfl rfl rfl) h₁.st_scr h₂.st_scr).wp
    (F₁ := ProPost σ₁) (F₂ := ProPost σ₂) fun a b ⟨ha, hb⟩ => by
      subst ha hb; exact ⟨prologue_ok h₁, prologue_ok h₂⟩
  have agL : ∀ {i a b}, LInv σ₁ i a → LInv σ₂ i b → A.Agree τA a b := fun {i a b} l₁ l₂ =>
    agreeA (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [l₁.rdi, l₂.rdi]; exact e_rdi
        · rw [l₁.rsi, l₂.rsi]; simp only [blkAddr, bp, e_rsi]
        · rw [l₁.rdx, l₂.rdx, hnb]
        · rw [l₁.rcx, l₂.rcx]; exact e_rcx)
      (wr_eq h₁ l₁.wr l₁.rdi l₁.rcx) (wr_eq h₂ l₂.wr l₂.rdi l₂.rcx) (st_scr' h₁ l₁.rdi l₁.rcx)
      (st_scr' h₂ l₂.rdi l₂.rcx)
  have agA : ∀ {keep i a b}, AtLeave keep σ₁ i a → AtLeave keep σ₂ i b → A.Agree τA a b :=
    fun {keep i a b} l₁ l₂ =>
    agreeA (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [l₁.rdi, l₂.rdi]; exact e_rdi
        · rw [l₁.rsi, l₂.rsi]; simp only [blkAddr, bp, e_rsi]
        · rw [l₁.rdx, l₂.rdx, hnb]
        · rw [l₁.rcx, l₂.rcx]; exact e_rcx)
      (wr_eq h₁ l₁.wr l₁.rdi l₁.rcx) (wr_eq h₂ l₂.wr l₂.rdi l₂.rcx) (st_scr' h₁ l₁.rdi l₁.rcx)
      (st_scr' h₂ l₂.rdi l₂.rcx)
  -- The block the pairs start at, the same in both runs.
  have hk : nb σ₂ % 2 = nb σ₁ % 2 := by rw [hnb]
  refine RelCT.seq hpro (RelCT.seq (R := fun a b => LInv σ₁ (nb σ₁ % 2) a ∧ LInv σ₂ (nb σ₁ % 2) b) ?_
    (RelCT.seq (R := fun a b => (LInv σ₁ (nb σ₁ % 2) a ∧ eval .e a = some (BitVec.ofNat 64 (nb σ₁ - nb σ₁ % 2) == 0)) ∧
      (LInv σ₂ (nb σ₁ % 2) b ∧ eval .e b = some (BitVec.ofNat 64 (nb σ₂ - nb σ₁ % 2) == 0))) ?_
    (RelCT.seq (Q := fun _ _ => True) (R := fun a b => Ending σ₁ a ∧ Ending σ₂ b) ?_ ?_)))
  · refine RelCT.ite (fun a b ⟨_, p₁, p₂⟩ => by
      show eval .ne a = eval .ne b
      simp only [eval, p₁.2.2.2.2.2.1, p₂.2.2.2.2.2.1, e_rdx]) ?_ ?_
    · refine RelCT.seq (R := fun a b => (nb σ₁ % 2 = 1 ∧ AtLeave false σ₁ 0 a) ∧ AtLeave false σ₂ 0 b) ?_ ?_
      · refine ((first_rel false (P := fun a b => (True ∧ ProPost σ₁ a ∧ ProPost σ₂ b) ∧ eval .ne a = some true)
          fun a b h => agL (h.1.2.1.linv h₁) (h.1.2.2.linv h₂)).wp
          (F₁ := fun s => nb σ₁ % 2 = 1 ∧ AtLeave false σ₁ 0 s) (F₂ := AtLeave false σ₂ 0)
          fun a b ⟨⟨_, p₁, p₂⟩, he⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
        have ho : nb σ₁ % 2 = 1 := by
          have := he; rw [eval, p₁.2.2.2.2.2.1, and_one] at this
          simp only [Option.map_some, Option.some.injEq, Bool.not_eq_true', beq_eq_false_iff_ne] at this
          simp only [nb]; omega_arith
        exact ⟨WP.mono (prefix_ok h₁ false (by omega_arith) (fun h => absurd h (by decide)) (p₁.linv h₁))
            fun _ h => ⟨ho, h⟩,
          prefix_ok h₂ false (by rw [hnb]; omega_arith) (fun h => absurd h (by decide)) (p₂.linv h₂)⟩
      · refine ((loneRest_rel (P := fun a b => (nb σ₁ % 2 = 1 ∧ AtLeave false σ₁ 0 a) ∧ AtLeave false σ₂ 0 b)
          fun a b h => agA h.1.2 h.2).wp (F₁ := fun s => nb σ₁ % 2 = 1 ∧ LInv σ₁ (0 + 1) s)
          (F₂ := LInv σ₂ (0 + 1))
          fun a b ⟨⟨ho, l₁⟩, l₂⟩ => ⟨WP.mono (loneRest_ok h₁ (by omega_arith) l₁) fun _ h => ⟨ho, h⟩,
            loneRest_ok h₂ (by rw [hnb]; omega_arith) l₂⟩).mono (fun _ _ h => h)
          fun _ _ ⟨_, ⟨ho, l₁⟩, l₂⟩ => ⟨by rw [ho]; exact l₁, by rw [ho]; exact l₂⟩
    · exact rel_nil.mono (fun _ _ h => h) fun a b ⟨⟨_, p₁, p₂⟩, he⟩ => by
        have he' : nb σ₁ % 2 = 0 := by
          have : eval .ne a = some false := he
          rw [eval, p₁.2.2.2.2.2.1, and_one] at this
          simp only [Option.map_some, Option.some.injEq, Bool.not_eq_false', beq_iff_eq] at this
          simp only [nb]; omega_arith
        rw [he']; exact ⟨p₁.linv h₁, p₂.linv h₂⟩
  · exact ((test_rel (P := fun a b => LInv σ₁ (nb σ₁ % 2) a ∧ LInv σ₂ (nb σ₁ % 2) b) fun a b h => agL h.1 h.2).wp
      (F₁ := fun s => LInv σ₁ (nb σ₁ % 2) s ∧ eval .e s = some (BitVec.ofNat 64 (nb σ₁ - nb σ₁ % 2) == 0))
      (F₂ := fun s => LInv σ₂ (nb σ₁ % 2) s ∧ eval .e s = some (BitVec.ofNat 64 (nb σ₂ - nb σ₁ % 2) == 0))
      fun a b h => ⟨test_step h₁ h.1, test_step h₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  · refine RelCT.ite (fun a b ⟨⟨_, e₁⟩, ⟨_, e₂⟩⟩ => by
      show eval .e a = eval .e b
      rw [e₁, e₂, hnb]) ?_ ?_
    · refine rel_nil.mono (fun _ _ h => h) fun a b ⟨⟨⟨l₁, e₁⟩, ⟨l₂, _⟩⟩, he⟩ => ?_
      have he' : eval .e a = some true := he
      rw [e₁, Option.some.injEq] at he'
      obtain hn : nb σ₁ % 2 = nb σ₁ := by rcases nb_eq_of h₁ he' with h | h <;> omega_arith
      rw [hn] at l₁; rw [hn, ← hnb] at l₂
      exact ⟨l₁.toCommon.ending, l₂.toCommon.ending⟩
    · refine RelCT.seq (R := fun a b => Common σ₁ (nb σ₁) a ∧ Common σ₂ (nb σ₂) b) ?_ ?_
      · let I : Nat → State → State → Prop := fun n a b =>
          ∃ i, n = nb σ₁ - i ∧ i + 2 ≤ nb σ₁ ∧ (nb σ₁ - i) % 2 = 0 ∧ LInv σ₁ i a ∧ LInv σ₂ i b
        have hstep : ∀ n, RelCT isa (I n) Impl.Sha512.X86_64.Avx2Rolled.pair fun a b => isa.eval .ne a = isa.eval .ne b ∧
            (isa.eval .ne a = some false → Common σ₁ (nb σ₁) a ∧ Common σ₂ (nb σ₂) b) ∧
            (isa.eval .ne a = some true → ∃ m < n, I m a b) := by
          intro n
          refine RelCT.exists_ fun i => ?_
          by_cases hi : i + 2 ≤ nb σ₁
          swap
          · exact RelCT.of_false fun _ _ h => hi h.2.1
          by_cases hn : n = nb σ₁ - i
          swap
          · exact RelCT.of_false fun _ _ h => hn h.1
          by_cases hev : (nb σ₁ - i) % 2 = 0
          swap
          · exact RelCT.of_false fun _ _ h => hev h.2.2.1
          have hi₂ : i + 2 ≤ nb σ₂ := by rw [hnb]; exact hi
          have hev₂ : (nb σ₂ - i) % 2 = 0 := by rw [hnb]; exact hev
          refine RelCT.seq (R := fun a b => AtLeave true σ₁ i a ∧ AtLeave true σ₂ i b) ?_ ?_
          · exact ((first_rel true (P := fun a b => n = nb σ₁ - i ∧ i + 2 ≤ nb σ₁ ∧ (nb σ₁ - i) % 2 = 0 ∧
                LInv σ₁ i a ∧ LInv σ₂ i b) fun a b h => agL h.2.2.2.1 h.2.2.2.2).wp
              (F₁ := AtLeave true σ₁ i) (F₂ := AtLeave true σ₂ i)
              fun a b h => ⟨prefix_ok h₁ true (by omega_arith) (fun _ => by omega_arith) h.2.2.2.1,
                prefix_ok h₂ true (by omega_arith) (fun _ => by omega_arith) h.2.2.2.2⟩).mono
              (fun _ _ h => h) fun _ _ h => h.2
          · refine ((pairRest_rel (P := fun a b => AtLeave true σ₁ i a ∧ AtLeave true σ₂ i b)
                fun a b h => agA h.1 h.2).wp (F₁ := PairPost σ₁ i) (F₂ := PairPost σ₂ i)
              fun a b h => ⟨pairRest_ok h₁ hi h.1, pairRest_ok h₂ hi₂ h.2⟩).mono (fun _ _ h => h)
              fun a b ⟨_, q₁, q₂⟩ => ?_
            have heq : eval .ne a = eval .ne b := by rw [q₁.2.1, q₂.2.1, hnb]
            rcases pair_next h₁ hi hev q₁ with ⟨f₁, c₁⟩ | ⟨t₁, x₁, v₁, l₁⟩ <;>
              rcases pair_next h₂ hi₂ hev₂ q₂ with ⟨f₂, c₂⟩ | ⟨t₂, x₂, v₂, l₂⟩
            · exact ⟨heq, fun _ => ⟨c₁, c₂⟩, fun h => absurd (h.symm.trans f₁) (by simp)⟩
            · exact absurd (f₁.symm.trans (heq.trans t₂)) (by simp)
            · exact absurd (t₁.symm.trans (heq.trans f₂)) (by simp)
            · exact ⟨heq, fun h => absurd (h.symm.trans t₁) (by simp),
                fun _ => ⟨nb σ₁ - (i + 2), by omega_arith, i + 2, rfl, x₁, v₁, l₁, l₂⟩⟩
        refine (RelCT.loop I hstep (nb σ₁ - nb σ₁ % 2)).mono (fun a b ⟨⟨⟨l₁, e₁⟩, ⟨l₂, _⟩⟩, he⟩ => ?_)
          fun _ _ h => h
        have he' : eval .e a = some false := he
        rw [e₁, Option.some.injEq] at he'
        obtain h0 : nb σ₁ - nb σ₁ % 2 ≠ 0 := fun e => by rw [e] at he'; simp at he'
        exact ⟨nb σ₁ % 2, rfl, by omega_arith, by omega_arith, l₁, l₂⟩
      · exact ((wipe_rel (P := fun a b => Common σ₁ (nb σ₁) a ∧ Common σ₂ (nb σ₂) b)
          fun a b ⟨c₁, c₂⟩ => agreeR (by rw [c₁.rcx, c₂.rcx]; exact e_rcx)).wp
          (F₁ := Ending σ₁) (F₂ := Ending σ₂) fun a b ⟨c₁, c₂⟩ => ⟨epi_wipe h₁ c₁, epi_wipe h₂ c₂⟩).mono
          (fun _ _ h => h) fun _ _ h => h.2
  · exact res_rel fun a b ⟨c₁, c₂⟩ => agreeR (by rw [c₁.rcx, c₂.rcx]; exact e_rcx)

theorem compress_ct : ConstantTime isa Pre PubK compress :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => (compress_rel h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Sha512.X86_64.Avx2.Rolled

end

end

/-! ### `Sha512.X86_64.Rolled.Verified`, which this module and modules that import it used -/

section

/-! ### `Sha512.X86_64.Rolled.Compress`, which only this module used -/

section

/-! ### `Sha512.X86_64.Rolled.Rounds`, which only this module used -/

section

/-!
# SHA-512 on x86-64, rolled: a round, and `Kₜ` from the table

`Rolled.round t k` is round `t` when `k` addresses `Kₜ` in the table, the
base register holding the table's address (`exec_kSlot0`, `exec_kSlot`).
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64 VG.Impl.Sha512.X86_64.Rolled
open VG.Proof.Sha512.X86_64 (Vars pubRegs var_succ var_succ_zero var_not_pub pubRegs_ne round_nodup
  ofInt_natCast)
open VG.Spec.Sha512 (HashValue Word Block K W)

/-- The index of iteration `j`. -/
abbrev idx (j : Nat) : BitVec 64 := BitVec.ofNat 64 (128 * j)

theorem Ks_length : Spec.Sha512.Ks.length = 80 := rfl

/-- Round `t < 16` reads `Kₜ`. -/
theorem exec_kSlot0 (s : State) (h : Reg) {t : Nat} (ht : t < 16) (hb : s.gpr .rsi = s.syms kSym) :
    X86_64.exec (.aluTbl .add h (kSlot0 t) kSym Spec.Sha512.Ks) s = execAluW .add h (K t) s := by
  obtain e : s.ea (kSlot0 t) - s.syms kSym = BitVec.ofNat 64 (8 * t) := by
    simp only [State.ea, kSlot0, ofInt_natCast]
    rw [hb, BitVec.add_comm, BitVec.add_sub_cancel]
  obtain e' : (BitVec.ofNat 64 (8 * t)).toNat = 8 * t := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [ht])]
  obtain hl : t < Spec.Sha512.Ks.length := by rw [Ks_length]; omega_using [ht]
  simp only [X86_64.exec, e, e', show (kSlot0 t).base = .rsi from rfl, hb, Nat.mul_mod_right,
    Nat.mul_div_right t (by decide : 0 < 8), hl, and_self, ↓reduceIte]
  rfl

theorem kSlot_ea (s : State) {j : Nat} (h : s.gpr .rdx = idx j) (t' : Nat) :
    s.ea (kSlot t') = s.gpr .rsi + BitVec.ofNat 64 (8 * (16 * j + t')) := by
  simp only [State.ea, kSlot, h, ofInt_natCast, BitVec.mul_one]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 128 * j + 8 * t' = 8 * (16 * j + t') by omega_using []]

/-- Round `16 j + t'` of iteration `j` reads `K (16 j + t')`. -/
theorem exec_kSlot (s : State) (h : Reg) {j : Nat} (t' : Nat) (hrdx : s.gpr .rdx = idx j)
    (hb : s.gpr .rsi = s.syms kSym) (hn : 16 * j + t' < 80) :
    X86_64.exec (.aluTbl .add h (kSlot t') kSym Spec.Sha512.Ks) s = execAluW .add h (K (16 * j + t')) s := by
  obtain e : s.ea (kSlot t') - s.syms kSym = BitVec.ofNat 64 (8 * (16 * j + t')) := by
    rw [kSlot_ea s hrdx, hb, BitVec.add_comm, BitVec.add_sub_cancel]
  obtain e' : (BitVec.ofNat 64 (8 * (16 * j + t'))).toNat = 8 * (16 * j + t') := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]
  obtain hl : 16 * j + t' < Spec.Sha512.Ks.length := by rw [Ks_length]; exact hn
  simp only [X86_64.exec, e, e', show (kSlot t').base = .rsi from rfl, hb, Nat.mul_mod_right,
    Nat.mul_div_right (16 * j + t') (by decide : 0 < 8), hl, and_self, ↓reduceIte]
  rfl

/-- `T₁` as the round adds it, `Kₜ` and `Wₜ` first, in `a'`. -/
theorem t1_order (h k w s c r : Word) :
    h + (k + (w + (s + (c + r)))) = h + (s + (c + (k + (w + r)))) := by
  ac_rfl

/-- `T₁` as the round adds it, `Kₜ` and `Wₜ` first, in `e'`. -/
theorem t1_order' (d h k w s c : Word) :
    d + (h + (k + (w + (s + c)))) = d + (h + (s + (c + (k + w)))) := by
  ac_rfl

/-- The round is symbolically executed once, for any registers `a … h`,
given what its read of the table adds. -/
theorem round_ok (t : Nat) (k : MemOp) (s : State) (v : HashValue) (kv w : Word)
    (hv : Vars t s v) (hk : X86_64.exec (.aluTbl .add (var t 7) k kSym Spec.Sha512.Ks) s =
      execAluW .add (var t 7) kv s) (hw : s.gpr T0 = w) :
    WP isa (.block (Rolled.round t k)) s fun s' =>
      Vars (t + 1) s' (roundKW v kv w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain hd := round_nodup t
  obtain hd' := VG.nodup_reverse hd
  obtain p3 := var_not_pub t 3
  obtain p7 := var_not_pub t 7
  apply WP.of_runBlock
  rw [show Rolled.round t k = .aluTbl .add (var t 7) k kSym Spec.Sha512.Ks :: (Rolled.round t k).tail
    from rfl, runBlock_cons, hk]
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega_using []),
    var_succ t _ (show 1 < 7 by omega_using []), var_succ t _ (show 2 < 7 by omega_using []),
    var_succ t _ (show 3 < 7 by omega_using []), var_succ t _ (show 4 < 7 by omega_using []),
    var_succ t _ (show 5 < 7 by omega_using []), var_succ t _ (show 6 < 7 by omega_using [])] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  simp only [Rolled.round, List.tail_cons]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [T0, T1, T2, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hd hd' hw ⊢
  simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reducePow, and_self, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, execAluW, execShift, readSrc,
    isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, hd, hd',
    h0, h1, h2, h3, h4, h5, h6, h7, hw,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · obtain ⟨-, n1, n2⟩ := pubRegs_ne hr
    obtain nh : r ≠ h := fun e => p7 (e ▸ hr)
    obtain nd : r ≠ d := fun e => p3 (e ▸ hr)
    simp only [T1, T2] at n1 n2
    simp only [nh, nd, n1, n2, ite_false]
  all_goals
    simp only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6,
      roundKW_7, bsig1_eq, ch_eq, bsig0_eq, maj_eq, BitVec.add_assoc]
  · exact t1_order _ _ _ _ _ _
  · exact t1_order' _ _ _ _ _ _

end VG.Proof.Sha512.X86_64.Rolled

end

end


/-!
# SHA-512 on x86-64, rolled: the compression function

`correct` proves `Impl.Sha512.X86_64.Rolled.compress` correct from
`Avx2.PreN 192`, the precondition of `Proof.Sha512.compressWideX86_64S 192` (192 bytes
of scratch space). The proof follows the unrolled one
(`Proof/Sha512/X86_64/Compress.lean`), whose lemmas for the schedule, the
loading and the updating of the hash value it uses: the first sixteen rounds
run unrolled (`first_ok`), the others sixteen per iteration of a loop
(`iter_ok`), through the index `rdx = 128 j`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64 VG.Impl.Sha512.X86_64.Rolled
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks compress)
open VG.Proof.Sha512.X86_64 (Vars pubRegs st bp nb scr stR blR retR H₀ blkAddr blk blk_word
  compressBlocks_succ contains_offset contains_offset' ofInt_natCast stateAt_get stateAt_eq
  writeState stateAt_writeState frame_writeState slotAddr winRegion win_contains slot_sep
  schedule_ok load_ok_of update_ok_of work_ne var_mem pubRegs_ne ea_at Saved saved_bound saveMem)

/-- The scratch space of the shared contract. -/
abbrev scrW (s₀ : State) : Region := ⟨scr s₀, 192⟩

/-! ## Regions -/

namespace Pre
variable {s₀ : State} (h : Avx2.PreN 192 s₀)
include h

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 8 :=
  ⟨scrW s₀, by simp [h.wr], contains_offset' (by omega_arith) (by omega_arith)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 8 :=
  ⟨scrW s₀, by simp [h.wr], contains_offset' (by omega_arith) (by omega_arith)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 8 := by
  have := h.nb_lt
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 (8 * t) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 8 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega_arith) (by omega_arith)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 8 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## Keeping `rsi` and `rdx` in the scratch space -/

/-- Where `enter` keeps `rsi` and `rdx`. -/
abbrev spA (scr : Addr) : Addr := Spill.slot scr 176
abbrev spB (scr : Addr) : Addr := Spill.slot scr 184

/-- The slots that keep `rsi` and `rdx`. -/
abbrev spR (p : Addr) : Region := ⟨spA p, 16⟩

theorem sp_sub (p : Addr) : Region.Sub (spR p) ⟨p, 192⟩ := Offset.sub_base _ (by omega_arith)

theorem win_sp (p : Addr) : Region.Disjoint (winRegion p) (spR p) :=
  Offset.base_disjoint _ (by omega_arith) (by omega_arith)

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 192⟩ := Region.sub_prefix (by omega_arith)

theorem enter_ok (s : State) (hA : InRegions s.wr (spA (s.gpr .rcx)) 8)
    (hB : InRegions s.wr (spB (s.gpr .rcx)) 8) :
    WP isa (.block enter) s fun s' =>
      s'.gpr .rsi = s.syms kSym ∧ s'.gpr .rdx = s.gpr .rsi ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW (spA (s.gpr .rcx)) (s.gpr .rsi)).writeW (spB (s.gpr .rcx)) (s.gpr .rdx) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [enter, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.store64,
    Spill.ea_slot, hA, hB, ite_true, State.setReg, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨by simp, by simp, fun r h1 h2 => by simp [h1, h2], by simp, trivial, trivial⟩

theorem leave_ok (s : State) (hA : InRegions (s.rd ++ s.wr) (spA (s.gpr .rcx)) 8)
    (hB : InRegions (s.rd ++ s.wr) (spB (s.gpr .rcx)) 8) :
    WP isa (.block leave) s fun s' =>
      s'.gpr .rsi = s.mem.readW (spA (s.gpr .rcx)) 64 ∧ s'.gpr .rdx = s.mem.readW (spB (s.gpr .rcx)) 64 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [leave, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.load64,
    Spill.ea_slot, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    reduceCtorEq, ↓reduceIte, hA, hB, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial⟩

theorem spill_read (p : Addr) (m : Mem) (a b : BitVec 64) :
    ((m.writeW (spA p) a).writeW (spB p) b).readW (spA p) 64 = a ∧
      ((m.writeW (spA p) a).writeW (spB p) b).readW (spB p) 64 = b :=
  ⟨(Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)).trans
    (Mem.readW_writeW_self m _ 8 a (by decide)), Mem.readW_writeW_self _ _ 8 b (by decide)⟩

theorem spA_in (p : Addr) : (spR p).Contains (spA p) 8 :=
  Offset.contains (e := 176) (d := 176) (n := 8) (k := 16) p (by omega_arith) (by omega_arith) (by omega_arith)

theorem spB_in (p : Addr) : (spR p).Contains (spB p) 8 :=
  Offset.contains (e := 176) (d := 184) (n := 8) (k := 16) p (by omega_arith) (by omega_arith) (by omega_arith)

theorem spill_frame (p : Addr) (m : Mem) (a b : BitVec 64) :
    Frame [spR p] m ((m.writeW (spA p) a).writeW (spB p) b) := by
  refine ((Frame.refl _ m).writeW (List.mem_singleton_self _) a ?_).writeW (List.mem_singleton_self _) b ?_
  · exact spA_in p
  · exact spB_in p

theorem spill_keep {p : Addr} {m m' : Mem} (hf : Frame [winRegion p] m m') :
    m'.readW (spA p) 64 = m.readW (spA p) 64 ∧ m'.readW (spB p) 64 = m.readW (spB p) 64 :=
  ⟨hf.readW (spA_in _) (by simpa using (win_sp _).symm) (by decide),
    hf.readW (spB_in _) (by simpa using (win_sp _).symm) (by decide)⟩

theorem sp_in {s₀ : State} (hp : Avx2.PreN 192 s₀) {s : State} (hrcx : s.gpr .rcx = scr s₀)
    (hwr : s.wr = s₀.wr) :
    InRegions s.wr (spA (s.gpr .rcx)) 8 ∧ InRegions s.wr (spB (s.gpr .rcx)) 8 := by
  rw [hrcx, hwr]
  exact ⟨⟨scrW s₀, by simp [hp.wr], Offset.contains_base (d := 176) (n := 8) (k := 192) _ (by omega_arith) (by omega_arith)⟩,
    ⟨scrW s₀, by simp [hp.wr], Offset.contains_base (d := 184) (n := 8) (k := 192) _ (by omega_arith) (by omega_arith)⟩⟩

theorem sp_in' {s₀ : State} (hp : Avx2.PreN 192 s₀) {s : State} (hrcx : s.gpr .rcx = scr s₀)
    (hwr : s.wr = s₀.wr) :
    InRegions (s.rd ++ s.wr) (spA (s.gpr .rcx)) 8 ∧ InRegions (s.rd ++ s.wr) (spB (s.gpr .rcx)) 8 := by
  obtain ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩⟩ := sp_in hp hrcx hwr
  exact ⟨⟨r, List.mem_append_right _ hr, hc⟩, ⟨r', List.mem_append_right _ hr', hc'⟩⟩

/-! ## The loop's index -/

theorem e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide

theorem toLoop_ok (s : State) :
    WP isa (.block toLoop) s fun s' =>
      s'.gpr .rdx = idx 1 ∧ (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [toLoop, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.setReg,
    Option.map_some, Option.some.injEq, exists_eq_left', e128, ↓reduceIte]
  exact ⟨rfl, fun r h => by simp [h], trivial, trivial, trivial⟩

theorem step_ok (s : State) :
    WP isa (.block step) s fun s' =>
      eval .ne s' = some (!(s.gpr .rdx + 128 - BitVec.signExtend 64 (640 : BitVec 32) == 0)) ∧
      s'.gpr .rdx = s.gpr .rdx + 128 ∧ (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [step, ↓reduceIte, Nat.reducePow, and_self, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, State.setReg, arithFlags, State.setFlags, e128,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial, fun r h => by simp [h], trivial⟩

/-- The loop stops after iteration 4: `128 (j + 1) = 640`. -/
theorem step_idx {j : Nat} (hj : j < 5) :
    (idx j + 128 - BitVec.signExtend 64 (640 : BitVec 32) == 0) = (j + 1 == 5) := by
  revert j; decide

theorem idx_succ (j : Nat) : idx j + 128 = idx (j + 1) := by
  simp only [idx]
  rw [show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, ← BitVec.ofNat_add]
  congr 1

/-! ## The first sixteen rounds -/

/-- `schedule t` (`t < 16`), reading the block through `rdx`. -/
theorem schedule0_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hrdx : s.gpr .rdx = bp) (hrcx : s.gpr .rcx = scr)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 8)
    (hbin : InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ↑(8 * t)) 8)
    (hblk : bswap64 (s.mem.readW (bp + BitVec.ofInt 64 ↑(8 * t)) 64) = W M t) :
    WP isa (.block (schedule0 t)) s fun s' =>
      s'.gpr T0 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ T0 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hout ⊢
  apply WP.of_runBlock
  simp only [schedule0, slot, at_, T0]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, State.ea,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, hrdx, hrcx, hbin, hout, hblk,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r h0 => ?_⟩
  simp [h0]

/-- The registers the rounds keep. -/
theorem pub_of {s s' : State} (h : ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) :
    ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := fun r hr =>
  have := pubRegs_ne hr; h r this.1 this.2.1 this.2.2

theorem vars_of {t : Nat} {s s' : State} {v : HashValue} (hv : Vars t s v)
    (h : ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) : Vars t s' v := by
  obtain e : ∀ k, s'.gpr (var t k) = s.gpr (var t k) := fun k =>
    have := work_ne (var_mem t k); h _ this.1 this.2.1 this.2.2
  simp only [Vars, e] at hv ⊢
  exact hv

/-- What the rounds keep of the state `sE` they start from, and the window
of the schedule after round `n`. -/
structure Win (M : Block) (scr : Addr) (sE : State) (n : Nat) (s : State) : Prop where
  rd : s.rd = sE.rd
  wr : s.wr = sE.wr
  syms : s.syms = sE.syms
  frame : Frame [winRegion scr] sE.mem s.mem
  win : ∀ j < n, n ≤ j + 16 → s.mem.readW (slotAddr scr j) 64 = W M j

/-- After round `t`'s schedule step and round, the window holds `W M t`. -/
theorem Win.step {M : Block} {scr : Addr} {sE s s' : State} {t : Nat} (h : Win M scr sE t s)
    (hm : s'.mem = s.mem.writeW (slotAddr scr t) (W M t)) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) : Win M scr sE (t + 1) s' := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.syms, ?_, fun j hj hj' => ?_⟩
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
  · rw [hm]
    by_cases hjt : j = t
    · subst hjt; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (slot_sep scr (by omega_arith)) (by decide)]
      exact h.win j (by omega_arith) (by omega_arith)

/-- The first `n ≤ 16` rounds, from `sE`, after `enter`: the block at `rdx`, the table at `rsi`. -/
theorem first_ok (H : HashValue) (M : Block) (bp scr : Addr) (sE : State)
    (hrdx : sE.gpr .rdx = bp) (hrcx : sE.gpr .rcx = scr) (hrsi : sE.gpr .rsi = sE.syms kSym)
    (hout : ∀ j, InRegions sE.wr (slotAddr scr j) 8)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sE.rd ++ sE.wr) (bp + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 8)
    (hblk : ∀ m, Frame [winRegion scr] sE.mem m →
      ∀ t : Nat, t < 16 → bswap64 (m.readW (bp + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M t)
    (h0 : Vars 0 sE H) :
    ∀ n ≤ 16, WP isa (first n) sE fun s =>
      Vars n s (VG.Spec.Sha512.rounds H M n) ∧ (∀ r ∈ pubRegs, s.gpr r = sE.gpr r) ∧
      Win M scr sE n s := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨by rw [rounds_zero]; exact h0, fun _ _ => rfl,
      ⟨rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega_arith)⟩⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_arith)) fun s ⟨hv, hpub, hW⟩ => ?_)
    rw [WP.block_append_iff]
    obtain hs_rdx : s.gpr .rdx = bp := (hpub .rdx (by decide)).trans hrdx
    obtain hs_rcx : s.gpr .rcx = scr := (hpub .rcx (by decide)).trans hrcx
    refine VG.X86_64.WP.mono_syms (schedule0_ok n s M bp scr hs_rdx hs_rcx
      (by rw [hW.wr]; exact hout) (by rw [hW.rd, hW.wr]; exact hbin n (by omega_arith))
      (hblk _ hW.frame n (by omega_arith))) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ hsy₁ => ?_
    obtain hr₁' : ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → s₁.gpr r = s.gpr r := fun r h _ _ => hr₁ r h
    obtain hv₁ := vars_of hv hr₁'
    obtain hb : s₁.gpr .rsi = s₁.syms kSym := by
      rw [hr₁' .rsi (by decide) (by decide) (by decide), hpub .rsi (by decide), hrsi, hsy₁, hW.syms]
    refine VG.X86_64.WP.mono_syms (round_ok n (kSlot0 n) s₁ _ (K n) _ hv₁
      (exec_kSlot0 s₁ _ (by omega_arith) hb) hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ hsy₂ => ?_
    refine ⟨by rw [rounds_succ, round_eq]; exact hv₂, fun r hr => ?_,
      hW.step (hm₂.trans hm₁) (hrd₂.trans hrd₁) (hwr₂.trans hwr₁) (hsy₂.trans hsy₁)⟩
    rw [hr₂ r hr, pub_of hr₁' r hr, hpub r hr]

/-! ## The iterations -/

theorem slot_mod {a b : Nat} (h : a % 16 = b % 16) : slot a = slot b := by
  simp only [slot, h]

/-- The schedule step of round `16 + t'` is that of round `16 j + t'`. -/
theorem schedule_shift {j t' : Nat} (hj : 1 ≤ j) :
    schedule (16 + t') = schedule (16 * j + t') := by
  simp only [Impl.Sha512.X86_64.schedule, show ¬(16 + t' < 16) by omega_arith, show ¬(16 * j + t' < 16) by omega_arith,
    ite_false, slot_mod (show (16 + t' + 14) % 16 = (16 * j + t' + 14) % 16 by omega_arith),
    slot_mod (show (16 + t' + 9) % 16 = (16 * j + t' + 9) % 16 by omega_arith),
    slot_mod (show (16 + t' + 1) % 16 = (16 * j + t' + 1) % 16 by omega_arith),
    slot_mod (show (16 + t') % 16 = (16 * j + t') % 16 by omega_arith)]

theorem vars16 {s : State} {v : HashValue} : Vars 16 s v ↔ Vars 0 s v := by
  simp only [Vars, var]

/-- The first `n ≤ 16` rounds of iteration `j` (`1 ≤ j < 5`), from its start `sI`. -/
theorem iter_ok (H : HashValue) (M : Block) (scr : Addr) (sE sI : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 5)
    (hrcx : sE.gpr .rcx = scr) (hrsi : sE.gpr .rsi = sE.syms kSym)
    (hout : ∀ i, InRegions sE.wr (slotAddr scr i) 8)
    (hin : ∀ i, InRegions (sE.rd ++ sE.wr) (slotAddr scr i) 8)
    (h0 : Vars 0 sI (VG.Spec.Sha512.rounds H M (16 * j)))
    (hpub0 : ∀ r ∈ pubRegs, r ≠ .rdx → sI.gpr r = sE.gpr r) (hrdx0 : sI.gpr .rdx = idx j)
    (hW0 : Win M scr sE (16 * j) sI) :
    ∀ n ≤ 16, WP isa (iter n) sI fun s =>
      Vars n s (VG.Spec.Sha512.rounds H M (16 * j + n)) ∧
      (∀ r ∈ pubRegs, r ≠ .rdx → s.gpr r = sE.gpr r) ∧ s.gpr .rdx = idx j ∧
      Win M scr sE (16 * j + n) s := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil (M := isa) ⟨h0, hpub0, hrdx0, hW0⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_arith)) fun s ⟨hv, hpub, hrdx, hW⟩ => ?_)
    rw [WP.block_append_iff, schedule_shift hj]
    obtain hs_rcx : s.gpr .rcx = scr := (hpub .rcx (by decide) (by decide)).trans hrcx
    refine VG.X86_64.WP.mono_syms (schedule_ok (16 * j + n) s M (s.gpr .rsi) scr rfl hs_rcx
      (by rw [hW.rd, hW.wr]; exact hin) (by rw [hW.wr]; exact hout)
      (fun h => absurd h (by omega_arith)) (fun h => absurd h (by omega_arith)) (fun _ => hW.win))
      fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ hsy₁ => ?_
    obtain hv₁ : Vars n s₁ (VG.Spec.Sha512.rounds H M (16 * j + n)) := vars_of hv hr₁
    obtain hrdx₁ : s₁.gpr .rdx = idx j := (hr₁ .rdx (by decide) (by decide) (by decide)).trans hrdx
    obtain hb : s₁.gpr .rsi = s₁.syms kSym := by
      rw [hr₁ .rsi (by decide) (by decide) (by decide), hpub .rsi (by decide) (by decide), hrsi, hsy₁,
        hW.syms]
    refine VG.X86_64.WP.mono_syms (round_ok n (kSlot n) s₁ _ (K (16 * j + n)) _ hv₁
      (exec_kSlot s₁ _ n hrdx₁ hb (by omega_arith)) hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ hsy₂ => ?_
    refine ⟨by rw [show 16 * j + (n + 1) = 16 * j + n + 1 by omega_arith, rounds_succ, round_eq]; exact hv₂,
      fun r hr hr' => ?_, by rw [hr₂ .rdx (by decide)]; exact hrdx₁, ?_⟩
    · rw [hr₂ r hr, pub_of hr₁ r hr, hpub r hr hr']
    · rw [show 16 * j + (n + 1) = 16 * j + n + 1 by omega_arith]
      exact hW.step (hm₂.trans hm₁) (hrd₂.trans hrd₁) (hwr₂.trans hwr₁) (hsy₂.trans hsy₁)

/-- `Win` through code that changes only `rdx` and the flags. -/
theorem Win.of_eq {M : Block} {scr : Addr} {sE s s' : State} {n : Nat} (h : Win M scr sE n s)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms) :
    Win M scr sE n s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.syms, hm ▸ h.frame, fun j hj hj' => hm ▸ h.win j hj hj'⟩

/-- Rounds 16–79: the loop's four iterations. -/
theorem loop_ok (H : HashValue) (M : Block) (scr : Addr) (sE sL : State)
    (hrcx : sE.gpr .rcx = scr) (hrsi : sE.gpr .rsi = sE.syms kSym)
    (hout : ∀ i, InRegions sE.wr (slotAddr scr i) 8)
    (hin : ∀ i, InRegions (sE.rd ++ sE.wr) (slotAddr scr i) 8)
    (h0 : Vars 0 sL (VG.Spec.Sha512.rounds H M 16))
    (hpub0 : ∀ r ∈ pubRegs, r ≠ .rdx → sL.gpr r = sE.gpr r) (hrdx0 : sL.gpr .rdx = idx 1)
    (hW0 : Win M scr sE 16 sL) :
    WP isa (.loop (.seq (iter 16) (.block step)) .ne) sL fun s =>
      Vars 0 s (VG.Spec.Sha512.rounds H M 80) ∧ (∀ r ∈ pubRegs, r ≠ .rdx → s.gpr r = sE.gpr r) ∧
      Win M scr sE 80 s := by
  let Inv : Nat → State → Prop := fun m s => ∃ j, m = 5 - j ∧ 1 ≤ j ∧ j < 5 ∧
    Vars 0 s (VG.Spec.Sha512.rounds H M (16 * j)) ∧ (∀ r ∈ pubRegs, r ≠ .rdx → s.gpr r = sE.gpr r) ∧
    s.gpr .rdx = idx j ∧ Win M scr sE (16 * j) s
  obtain hstep : ∀ m s, Inv m s → WP isa (.seq (iter 16) (.block step)) s (fun s' =>
      (eval .ne s' = some false ∧ Vars 0 s' (VG.Spec.Sha512.rounds H M 80) ∧
        (∀ r ∈ pubRegs, r ≠ .rdx → s'.gpr r = sE.gpr r) ∧ Win M scr sE 80 s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨j, rfl, hj, hj', hv, hpub, hrdx, hW⟩
    refine WP.seq (WP.mono (iter_ok H M scr sE s hj hj' hrcx hrsi hout hin hv hpub hrdx hW 16 (Nat.le_refl _))
      fun s₁ ⟨hv₁, hpub₁, hrdx₁, hW₁⟩ => ?_)
    refine VG.X86_64.WP.mono_syms (step_ok s₁) fun s₂ ⟨he, hrdx₂, hg, hm, hrd, hwr⟩ hsy => ?_
    obtain hv₂ : Vars 0 s₂ (VG.Spec.Sha512.rounds H M (16 * (j + 1))) := by
      rw [show 16 * (j + 1) = 16 * j + 16 by omega_arith]
      have := vars16.mp hv₁
      simp only [Vars] at this ⊢
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := this
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hg _ (by decide)]; assumption
    obtain hpub₂ : ∀ r ∈ pubRegs, r ≠ .rdx → s₂.gpr r = sE.gpr r := fun r hr hr' =>
      (hg r hr').trans (hpub₁ r hr hr')
    obtain hW₂ : Win M scr sE (16 * (j + 1)) s₂ := by
      rw [show 16 * (j + 1) = 16 * j + 16 by omega_arith]; exact hW₁.of_eq hm hrd hwr hsy
    rw [hrdx₁, step_idx hj'] at he
    by_cases hlast : j + 1 = 5
    · left
      obtain hb : (j + 1 == 5) = true := beq_iff_eq.mpr hlast
      refine ⟨by rw [he, hb]; rfl, ?_, hpub₂, ?_⟩
      · rw [show 80 = 16 * (j + 1) by omega_arith]; exact hv₂
      · rw [show 80 = 16 * (j + 1) by omega_arith]; exact hW₂
    · right
      obtain hb : (j + 1 == 5) = false := beq_eq_false_iff_ne.mpr hlast
      refine ⟨by rw [he, hb]; rfl, 5 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, by omega_arith, hv₂, hpub₂,
        by rw [hrdx₂, hrdx₁, idx_succ], hW₂⟩
  exact WP.loop (M := isa) Inv hstep 4 sL ⟨1, rfl, Nat.le_refl _, by decide, h0, hpub0, hrdx0, hW0⟩

/-! ## One block -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rcx : s.gpr .rcx = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrW s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i
  saved : Saved s₀ s.mem
  syms : s.syms = s₀.syms

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

theorem saved_frame {s₀ : State} (hp : Avx2.PreN 192 s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [winRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m' ∨ Frame [spR (scr s₀)] m m') :
    Saved s₀ m' := by
  rcases hf with hf | hf | hf <;> refine Spill.Saved.frame h hf fun p hp' r hr => ?_ <;>
    rw [List.mem_singleton.mp hr] <;> have := saved_bound p hp'
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by omega_arith))
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The hash value, through a frame of the window or of the spill slots. -/
theorem state_frame {s₀ : State} (hp : Avx2.PreN 192 s₀) {m m' : Mem}
    (hf : Frame [winRegion (scr s₀)] m m' ∨ Frame [spR (scr s₀)] m m') :
    stateAt m' (st s₀) = stateAt m (st s₀) := by
  apply stateAt_eq
  intro k hk
  rcases hf with hf | hf
  · rw [hf.readW (contains_offset' (off := 8 * k) (len := 64) (by omega_arith) (by omega_arith))
      (by simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)) (by decide), ← stateAt_get _ _ hk]
  · rw [hf.readW (contains_offset' (off := 8 * k) (len := 64) (by omega_arith) (by omega_arith))
      (by simpa using Region.Disjoint.sub_right hp.st_scr (sp_sub _)) (by decide), ← stateAt_get _ _ hk]

theorem sub_scrW (s₀ : State) {r : Region} (h : Region.Sub r ⟨scr s₀, 192⟩) :
    ∀ r' ∈ [r], ∃ r'' ∈ [stR s₀, scrW s₀], Region.Sub r' r'' :=
  fun r' hr => ⟨scrW s₀, by simp, by simp at hr; subst hr; exact h⟩

theorem body_ok {s₀ : State} (hp : Avx2.PreN 192 s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa Rolled.body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  obtain hscr : (⟨scr s₀, 192⟩ : Region) ∈ s₀.wr := by simp [hp.wr]
  -- load and enter
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine VG.X86_64.WP.mono_syms (load_ok_of hL.rdi (by rw [hL.rd, hL.wr]; exact fun k hk => hp.in_state hk))
    fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ hsy₁ => ?_
  obtain hrcx₁ : s₁.gpr .rcx = scr s₀ := (hpub₁ .rcx (by decide)).trans hL.rcx
  obtain hwr₁' : s₁.wr = s₀.wr := hwr₁.trans hL.wr
  obtain hrd₁' : s₁.rd = s₀.rd := hrd₁.trans hL.rd
  obtain ⟨spa, spb⟩ := sp_in hp hrcx₁ hwr₁'
  refine VG.X86_64.WP.mono_syms (enter_ok s₁ spa spb)
    fun sE ⟨hrsiE, hrdxE, hgE, hmE, hrdE, hwrE⟩ hsyE => ?_
  obtain hrcxE : sE.gpr .rcx = scr s₀ := by rw [hgE _ (by decide) (by decide)]; exact hrcx₁
  obtain hrdxE' : sE.gpr .rdx = blkAddr s₀ i := by rw [hrdxE, hpub₁ .rsi (by decide), hL.rsi]
  obtain hrsiE' : sE.gpr .rsi = sE.syms kSym := by rw [hrsiE, hsyE]
  obtain hspE : Frame [spR (scr s₀)] s₁.mem sE.mem := by rw [hmE, hrcx₁]; exact spill_frame _ _ _ _
  obtain hvE : Vars 0 sE (stateAt s.mem (st s₀)) := by
    obtain e : ∀ k, sE.gpr (var 0 k) = s₁.gpr (var 0 k) := fun k =>
      hgE _ (fun h => (by decide : ∀ r ∈ work, r ≠ .rsi) _ (var_mem 0 k) h)
        (fun h => (by decide : ∀ r ∈ work, r ≠ .rdx) _ (var_mem 0 k) h)
    simp only [Vars, e] at hv₁ ⊢
    exact hv₁
  obtain hblkR : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  obtain hblk : ∀ m, Frame [winRegion (scr s₀)] sE.mem m → ∀ t : Nat, t < 16 →
      bswap64 (m.readW (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (Pre.blk_contains hp hi ht) hblkR (by decide),
      hspE.readW (Pre.blk_contains hp hi ht) (by simpa using Region.Disjoint.sub_right hp.blk_scr (sp_sub _))
        (by decide), hm₁,
      hL.frame.readW (Pre.blk_contains hp hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  -- the first sixteen rounds
  refine WP.seq (WP.mono (first_ok _ (blk s₀ i) _ (scr s₀) sE hrdxE' hrcxE hrsiE'
    (by rw [hwrE, hwr₁']; exact Pre.out_slot hp)
    (fun t ht => by rw [hrdE, hwrE, hrd₁', hwr₁']; exact Pre.in_blk hp hi ht) hblk hvE 16 (Nat.le_refl _))
    fun sF ⟨hvF, hpubF, hWF⟩ => ?_)
  -- the loop
  refine WP.seq (VG.X86_64.WP.mono_syms (Q := fun sL => Vars 0 sL
      (VG.Spec.Sha512.rounds (stateAt s.mem (st s₀)) (blk s₀ i) 16) ∧
      (∀ r ∈ pubRegs, r ≠ .rdx → sL.gpr r = sE.gpr r) ∧ sL.gpr .rdx = idx 1 ∧
      Win (blk s₀ i) (scr s₀) sE 16 sL) ?_ fun sL ⟨hvL, hpubL, hrdxL, hWL⟩ _ => ?_)
  · refine VG.X86_64.WP.mono_syms (toLoop_ok sF) fun sL ⟨hrdxL, hgL, hmL, hrdL, hwrL⟩ hsyL => ?_
    refine ⟨?_, fun r hr hr' => (hgL r hr').trans (hpubF r hr), hrdxL, hWF.of_eq hmL hrdL hwrL hsyL⟩
    have := vars16.mp hvF
    simp only [Vars] at this ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [hgL _ (by decide)]; assumption
  refine WP.seq (WP.mono (loop_ok _ (blk s₀ i) (scr s₀) sE sL hrcxE hrsiE'
    (by rw [hwrE, hwr₁']; exact Pre.out_slot hp)
    (by rw [hrdE, hwrE, hrd₁', hwr₁']; exact Pre.in_slot hp) hvL hpubL hrdxL hWL)
    fun s₃ ⟨hv₃, hpub₃, hW₃⟩ => ?_)
  -- leave, update and advance
  rw [List.append_assoc, WP.block_append_iff]
  obtain hrcx₃ : s₃.gpr .rcx = scr s₀ := (hpub₃ .rcx (by decide) (by decide)).trans hrcxE
  obtain hwr₃ : s₃.wr = s₀.wr := by rw [hW₃.wr, hwrE, hwr₁']
  obtain hrd₃ : s₃.rd = s₀.rd := by rw [hW₃.rd, hrdE, hrd₁']
  obtain ⟨spa', spb'⟩ := sp_in' hp hrcx₃ hwr₃
  refine VG.X86_64.WP.mono_syms (leave_ok s₃ spa' spb')
    fun s₄ ⟨hrsi₄, hrdx₄, hg₄, hm₄, hrd₄, hwr₄⟩ hsy₄ => ?_
  obtain sk := spill_keep (p := scr s₀) hW₃.frame
  obtain sr := spill_read (scr s₀) s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)
  rw [← hrcx₁, ← hmE] at sr
  rw [hrcx₃, sk.1, ← hrcx₁, sr.1, hpub₁ .rsi (by decide)] at hrsi₄
  rw [hrcx₃, sk.2, ← hrcx₁, sr.2, hpub₁ .rdx (by decide)] at hrdx₄
  obtain hrdi₄ : s₄.gpr .rdi = st s₀ := by
    rw [hg₄ _ (by decide) (by decide), hpub₃ .rdi (by decide) (by decide), hgE _ (by decide) (by decide),
      hpub₁ .rdi (by decide), hL.rdi]
  obtain hst₄ : stateAt s₄.mem (st s₀) = stateAt s.mem (st s₀) := by
    rw [hm₄, state_frame hp (.inl hW₃.frame), state_frame hp (.inr hspE), hm₁]
  obtain hv₄ : Vars 0 s₄ (VG.Spec.Sha512.rounds (stateAt s.mem (st s₀)) (blk s₀ i) 80) := by
    simp only [Vars] at hv₃ ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv₃
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [hg₄ _ (by decide) (by decide)]; assumption
  refine VG.X86_64.WP.mono_syms (update_ok_of _ (stateAt s.mem (st s₀)) hv₄ hrdi₄
    (by rw [hrd₄, hwr₄, hrd₃, hwr₃]; exact fun k hk => hp.in_state hk)
    (by rw [hwr₄, hwr₃]; exact fun k hk => hp.out_state hk)
    fun k hk => by rw [← hst₄, stateAt_get _ _ hk]) fun s₅ h₅ hsy₅ => ?_
  obtain ⟨hm₅, hrsi₅, hrdx₅, hzf₅, hrdi₅, hrcx₅, hrsp₅, hrd₅, hwr₅⟩ := h₅
  obtain hrdx : s₄.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hrdx₄, hL.rdx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  obtain hframe : Frame [stR s₀, scrW s₀] s₀.mem s₅.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hspE.sub (sub_scrW s₀ (sp_sub _))) ?_
    refine Frame.trans (hW₃.frame.sub (sub_scrW s₀ (win_sub _))) ?_
    rw [hm₅, hm₄]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain hrsp₄ : s₄.gpr .rsp = s₀.gpr .rsp := by
    rw [hg₄ _ (by decide) (by decide), hpub₃ .rsp (by decide) (by decide), hgE _ (by decide) (by decide),
      hpub₁ .rsp (by decide), hL.rsp]
  obtain hcommon : Common s₀ (i + 1) s₅ := by
    refine ⟨by rw [hrdi₅, hrdi₄], by rw [hrcx₅, hg₄ _ (by decide) (by decide)]; exact hrcx₃,
      by rw [hrsp₅, hrsp₄], by rw [hrd₅, hrd₄, hrd₃], by rw [hwr₅, hwr₄, hwr₃], hframe, ?_, ?_, ?_⟩
    · rw [hm₅, stateAt_writeState, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₅]
      refine saved_frame hp ?_ (.inr (.inl (frame_writeState (Frame.refl _ _) _)))
      rw [hm₄]
      refine saved_frame hp ?_ (.inl hW₃.frame)
      refine saved_frame hp ?_ (.inr (.inr hspE))
      rw [hm₁]; exact hL.saved
    · rw [hsy₅, hsy₄, hW₃.syms, hsyE, hsy₁]; exact hL.syms
  obtain hev : eval .ne s₅ = some (!(s₄.gpr .rdx - 1 == 0)) := by
    simp [eval, hzf₅]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    obtain hne : nb s₀ - (i + 1) ≠ 0 := by omega_arith
    refine ⟨?_, by omega_arith, { hcommon with rsi := ?_, rdx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      obtain h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        obtain h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at h'
        exact hne h'
      simpa using h0
    · rw [hrsi₅, hrsi₄, hL.rsi]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (128 : BitVec _) = BitVec.ofNat _ 128 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hrdx₅, hrdx]

/-! ## Prologue and epilogue -/

theorem save_ok {s₀ : State} (hp : Avx2.PreN 192 s₀) :
    WP isa (.block (save ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_ok .rcx saved s₀ fun p hp' => ?_) fun s₁ ⟨hg, hrd, hwr, hm⟩ => ?_
  · have := saved_bound p hp'
    exact ⟨scrW s₀, by simp [hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
      State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨hg, hrd, hwr, hm, by rw [hg]⟩

theorem saveMem_frame {s₀ : State} : Frame [scrW s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := saved_bound p hp; omega_arith) (by decide)

theorem common_zero {s₀ : State} (hp : Avx2.PreN 192 s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) (hsy : s₁.syms = s₀.syms) :
    Common s₀ 0 s₁ := by
  refine ⟨by rw [hg], by rw [hg], by rw [hg], hrd, hwr, ?_, ?_,
    by rw [hm]; exact Spill.saveMem_saved _ _ _ _ (by decide), hsy⟩
  · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq
    intro k hk
    rw [saveMem_frame.readW (contains_offset' (off := 8 * k) (len := 64) (by omega_arith) (by omega_arith))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get _ _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Avx2.PreN 192 s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha512.compressWideX86_64.post s₀ s' := by
  obtain hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  refine WP.mono (Spill.restore_ok .rcx saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [hc.rcx]; exact hc.saved)) fun s' ⟨h₁, h₂, hm, _⟩ => ?_
  · have := saved_bound p hp'
    rw [hc.rcx, hc.rd, hc.wr]
    exact ⟨scrW s₀, by simp [hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · exact ⟨⟨Spill.calleeSaved_ok h₁ h₂ (by decide) hc.rsp, by rw [hm]; exact hret⟩,
      by show stateAt _ _ = _; rw [hm]; exact hc.state⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Avx2.PreN 192 s₀) :
    WP isa Rolled.compress s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha512.compressWideX86_64.post s₀ s' := by
  refine WP.seq (VG.X86_64.WP.mono_syms (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hzf⟩ hsy => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  obtain hc₀ := common_zero hp hg hrd hwr hm hsy
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    obtain hstep : ∀ m s, Inv m s → WP isa Rolled.body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_arith, i + 1, rfl, hi', hL'⟩
    obtain hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg]; simp [blkAddr]
        rdx := by rw [hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

end VG.Proof.Sha512.X86_64.Rolled

end

end

/-!
# SHA-512 on x86-64, rolled: verified

`compress_verified`: `Impl.Sha512.X86_64.Rolled.compress` against
`Proof.Sha512.compressWideX86_64`, under the plain calling convention: the
table of round constants is carried by the code (`aluTbl`). Constant time is
one run of the taint analysis: the schedule's stores are at fixed offsets of
`rcx`, and the table's reads at the public index `rdx`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Rolled

open VG VG.X86_64

/-- The pointers and the count are public; `rdi` and `rcx` point at the
hash value and the scratch space. -/
def τW : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx], flags := false, lens := [64, 192],
    bases := [(.rdi, 0, 0), (.rcx, 1, 0)] }

theorem agreeW {s₁ s₂ : State}
    (hr : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx], s₁.gpr r = s₂.gpr r)
    (hw₁ : s₁.wr = [⟨s₁.gpr .rdi, 64⟩, ⟨s₁.gpr .rcx, 192⟩])
    (hw₂ : s₂.wr = [⟨s₂.gpr .rdi, 64⟩, ⟨s₂.gpr .rcx, 192⟩])
    (hd₁ : Region.Disjoint ⟨s₁.gpr .rdi, 64⟩ ⟨s₁.gpr .rcx, 192⟩)
    (hd₂ : Region.Disjoint ⟨s₂.gpr .rdi, 64⟩ ⟨s₂.gpr .rcx, 192⟩) : taint.Agree τW s₁ s₂ := by
  have wf : ∀ s : State, s.wr = [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .rcx, 192⟩] →
      Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, 192⟩ → X86_64.Taint.Wf τW s := by
    intro s hw hd
    refine ⟨fun _ => ⟨by simp [hw, τW], by simp [hw, hd], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τW, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr' => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ hw₁ hd₁, wf _ hw₂ hd₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τW, RegSet.mem_ofList] at hr'
    exact hr r hr'
  · rw [hw₁, hw₂, hr .rdi (by simp), hr .rcx (by simp)]
  · intro sl h; simp [τW] at h
  · intro sl h; simp [τW] at h

/-- The compression function, verified with the 192 bytes of scratch space it
uses. -/
theorem compress_verified192 :
    Verified X86_64.target Impl.Sha512.X86_64.Rolled.compress (Proof.Sha512.compressWideX86_64S 192) := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (Avx2.preN_of 192 s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) τW ?_ (by taint_decide)
    intro s₁ s₂ hp₁ hp₂ ⟨h1, h2, h3, h4⟩
    have p₁ := Avx2.preN_of 192 s₁ hp₁
    have p₂ := Avx2.preN_of 192 s₂ hp₂
    refine agreeW (fun r hr => ?_) p₁.wr p₂.wr p₁.st_scr p₂.st_scr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · exact wideSatS 192 (.inr (.inl rfl))

/-- `compress_verified192`, with the scratch space of the shared contract. -/
theorem compress_verified :
    Verified X86_64.target Impl.Sha512.X86_64.Rolled.compress Proof.Sha512.compressWideX86_64 :=
  compressWideS_widen compress_verified192 (by decide) (wideSatS 1328 (.inr (.inr rfl)))

end VG.Proof.Sha512.X86_64.Rolled

end

end

/-! ### `Sha512.X86_64.Avx2Rolled.Verified`, which this module and modules that import it used -/

section

/-!
# SHA-512 with AVX2 on x86-64, rolled: verified

`compress_verified`: `Impl.Sha512.X86_64.Avx2Rolled.compress` against
`Proof.Sha512.compressWideX86_64`, the contract of the unrolled code, under
the plain calling convention: the table of round constants is carried by
the code (`aluTbl`), not given by the contract.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx2.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2Rolled

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressWideX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem compress_verified :
    Verified X86_64.target compress Proof.Sha512.compressWideX86_64 := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    exact compress_ct s₁ s₂ t₁ t₂ s₁' s₂' (pre_of s₁ h₁) (pre_of s₂ h₂) ⟨h1, h2, h3, h4⟩ e₁ e₂
  · refine ⟨Avx2.satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha512.X86_64.Avx2.Rolled

end

end

/-!
# Streaming SHA-512 on x86-64: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86_64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86_64/`) for the SHA-512 family's instance
(`Proof/Sha512/Md.lean`), for any implementation `f` of the compression function
(`CalleeOk`: `scalar_ok`, `avx2_ok`, `shani_ok`), given what the family's own
pieces do: its length field and digest (`shape`) and that the taint analysis
accepts its code between the calls (`taints`).
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (len64 out64)
open VG.Impl.Sha512.X86_64 (at_)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append)
open VG.Impl.Sha512.X86_64.Stream (Callee update finalize)

abbrev params := Impl.Sha512.X86_64.Stream.params

theorem dims : Dims params := ⟨.inr rfl, by decide, by decide, by decide⟩

theorem wp_shri {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {n : Nat}
    (hn : 1 ≤ n ∧ n ≤ 63) (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_)
  · simp [exec, execShift, hn]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

theorem lenOf_split (x : BitVec 64) :
    md.lenOf x = bytes64 true (x >>> 61) ++ bytes64 true (BitVec.ofNat 64 (8 * x.toNat)) :=
  Proof.Sha512.lenOf_split x

/-- The length field: `count >> 61`, then `8 count`, big-endian. -/
theorem len_ok (s : State) (hout : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 176) 16) :
    WP isa (.block params.len) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = writeBytes s.mem (s.gpr .rbx + BitVec.ofNat 64 176) (md.lenOf (s.gpr .r12)) := by
  have h176 : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 176) 8 := by
    obtain ⟨R, hR, hc⟩ := hout
    exact ⟨R, hR, by unfold Region.Contains at *; omega_using [hc]⟩
  have e184 : s.gpr .rbx + BitVec.ofNat 64 176 + BitVec.ofNat 64 8 = s.gpr .rbx + BitVec.ofNat 64 184 := by
    rw [BitVec.add_assoc]; rfl
  have h184 : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 184) 8 := by
    rw [← e184]; exact InRegions.offset hout (by omega_using []) (by omega_using [])
  show WP isa (.block (.mov .rax (.reg .r12) :: .shift .shr .rax 61 :: .bswap .rax ::
    .store (at_ .rbx 176) .rax :: (len64 184 true ++ []))) s _
  refine wp_mov fun s₁ u₁ _ _ => wp_shri (by decide) fun s₂ u₂ => wp_bswap fun s₃ u₃ =>
    wp_store (a := s.gpr .rbx + BitVec.ofNat 64 176)
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ofInt_natCast])
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact h176) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  have k₄ : ∀ r, r ≠ .rax → s₄.gpr r = s.gpr r := fun r h => by
    rw [g₄, u₃.other r h, u₂.other r h, u₁.other r h]
  have e₄ : s₄.mem = writeBytes s.mem (s.gpr .rbx + BitVec.ofNat 64 176) (bytes64 true (s.gpr .r12 >>> 61)) := by
    rw [m₄, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, ← writeW64 _ _ true]; rfl
  refine len64_ok (by rw [wr₄, u₃.wr, u₂.wr, u₁.wr, k₄ _ (by decide)]; exact h184)
    fun s' g rd wr m => WP.block_nil ⟨fun r h => by rw [g r h, k₄ r h], by rw [rd, rd₄, u₃.rd, u₂.rd, u₁.rd],
      by rw [wr, wr₄, u₃.wr, u₂.wr, u₁.wr], ?_⟩
  have e' : s.gpr .rbx + BitVec.ofNat 64 176 + BitVec.ofNat 64 (bytes64 true (s.gpr .r12 >>> 61)).length =
      s.gpr .rbx + BitVec.ofNat 64 184 := by rw [bytes64_length]; exact e184
  rw [m, e₄, k₄ _ (by decide), k₄ _ (by decide), ← e',
    writeBytes_append _ _ _ _ (by rw [bytes64_length, bytes64_length]; decide), lenOf_split]

theorem digest_eq (mem : Mem) (p : Addr) :
    md.digest (md.stateAt mem p) = (List.range 8).flatMap fun k =>
      bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) := by
  simp [md, Spec.Sha512.stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ, bytes64,
    Spec.Sha512.wordBytes]

theorem shape : Shape (P := params) md where
  lenV s := (lenV128_ok s).mono fun _ ⟨g, rd, wr, m, x0, x7⟩ => ⟨g, rd, wr, m, x0, by
    rw [x7, lenOf_split]; rfl⟩
  len s hout := len_ok s hout
  out s hin hout hd := by
    refine (out64_ok (n := 8) (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem taints : Taints params :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, by decide, by decide⟩

theorem scalar_ok : CalleeOk (P := params) md Callee.scalar.code :=
  .of_verified Rolled.compress_verified.1 Rolled.compress_verified.2.1
    (by change (instrs Impl.Sha512.X86_64.Rolled.compress).all _ = true; rw [← Code.allInstrs_eq]; lit_decide)
    (by change Impl.Sha512.X86_64.Rolled.compress.depth = 0; lit_decide)

theorem avx2_ok : CalleeOk (P := params) md Callee.avx2.code :=
  .of_verified Avx2.Rolled.compress_verified.1 Avx2.Rolled.compress_verified.2.1
    (by change (instrs Impl.Sha512.X86_64.Avx2Rolled.compress).all _ = true; rw [← Code.allInstrs_eq]; lit_decide)
    (by change Impl.Sha512.X86_64.Avx2Rolled.compress.depth = 0; lit_decide)

theorem shani_ok : CalleeOk (P := params) md Callee.shani.code :=
  .of_verified ShaNi.compressWide_verified.1 ShaNi.compressWide_verified.2.1
    (by change (instrs Impl.Sha512.X86_64.ShaNi.compress).all _ = true; rw [← Code.allInstrs_eq]; lit_decide)
    (by change Impl.Sha512.X86_64.ShaNi.compress.depth = 0; lit_decide)

/-- `params` with `so` bytes of working space for the compression function
(`Impl.Pbkdf2.Md.X86_64.Hash.withWs`), for the implementations that use
less than AVX2's: the functions made with it give the compression function
only that much. -/
abbrev paramsS (so : Nat) : Impl.MdStream.X86_64.Params := { params with so := so }

theorem taintsS (so : Nat) (h : so = 0 ∨ so = 192) : Taints (paramsS so) := by
  rcases h with rfl | rfl <;>
  exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, by decide, by decide⟩

/-- `taintsS`, for each implementation's scratch space, AVX2's too. -/
theorem taintsS3 (so : Nat) (h : so = 0 ∨ so = 192 ∨ so = 1328) : Taints (paramsS so) := by
  rcases h with h | h | rfl
  · exact taintsS so (.inl h)
  · exact taintsS so (.inr h)
  · exact taints

/-- An implementation verified with `so` bytes of scratch space, as the code
made with `paramsS so` calls it. -/
theorem calleeS {code : Prog isa} (hf : CalleeOk (P := params) md code) {so : Nat}
    (hv : Verified X86_64.target code (Proof.Sha512.compressWideX86_64S so)) :
    CalleeOk (P := paramsS so) md code :=
  ⟨hv.1, hv.2.1, hf.nosp, hf.depth, hf.keeps_rdi, hf.keeps_rcx⟩

/-- The scalar compression function, verified with the scratch space it uses. -/
theorem scalar_verified192 :
    Verified X86_64.target Callee.scalar.code (Proof.Sha512.compressWideX86_64S 192) :=
  Rolled.compress_verified192

/-- The compression function with the SHA512 extension, verified with no
scratch space, which it does not use. -/
theorem shani_verified0 : Verified X86_64.target Callee.shani.code (Proof.Sha512.compressWideX86_64S 0) :=
  ShaNi.compress_verified0

theorem dimsS (so : Nat) (h : so ≤ 2048) : Dims (paramsS so) := ⟨dims.B, dims.N, dims.L, h⟩

theorem shapeS (so : Nat) : Shape (P := paramsS so) md := ⟨shape.len, shape.lenV, shape.out⟩

/-- `update` made with `so` bytes of working space for the compression
function, for an implementation verified with that much (`hv`). -/
theorem Update.verifiedS {so : Nat} (h : so = 0 ∨ so = 192) {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hv : Verified X86_64.target f.code (Proof.Sha512.compressWideX86_64S so))
    (hm : (Impl.MdStream.X86_64.update (paramsS so) f.name f.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.MdStream.X86_64.update (paramsS so) f.name f.code)
      (Proof.Sha512.updateX86_64S (so + 48)) :=
  MdStream.X86_64.Update.verified (dimsS so (by omega_using [h])) (taintsS so h) (calleeS hf hv) hm

/-- `finalize` made with `so` bytes of working space for the compression
function, for an implementation verified with that much (`hv`). -/
theorem Finalize.verifiedS {so : Nat} (h : so = 0 ∨ so = 192) {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hv : Verified X86_64.target f.code (Proof.Sha512.compressWideX86_64S so))
    (hm : (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code)
      (Proof.Sha512.finalizeX86_64S (so + 48)) :=
  MdStream.X86_64.Finalize.verified (dimsS so (by omega_using [h])) (shapeS so) (taintsS so h) (calleeS hf hv) hm

namespace Update

/-- `update` is verified if it never loads MXCSR. -/
theorem verified_of {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : (update f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (update f) Proof.Sha512.updateX86_64 :=
  MdStream.X86_64.Update.verified dims taints hf hm

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Update.sat params

end Update

namespace Finalize

/-- `finalize` is verified if it never loads MXCSR. -/
theorem verified_of {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : (finalize f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalize f) Proof.Sha512.finalizeX86_64 :=
  MdStream.X86_64.Finalize.verified dims shape taints hf hm

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Finalize.sat params

end Finalize

/-! ### With the scratch space the compression function uses

`updateOwn` and `finalizeOwn` give the compression function only the
scratch space it uses (`Callee.so`), and are verified against the contracts
with the scratch space of the slowest implementation, which their callers
by name give them (`updateS_widen`: they run as they do with less). -/

/-- `update` verified with `a` bytes of scratch space is with any `b ≥ a`. -/
theorem updateS_widen {c : Prog isa} {a b : Nat} (h : Verified X86_64.target c (Proof.Sha512.updateX86_64S a))
    (hab : a ≤ b) (hsat : ∃ s, (Proof.Sha512.updateX86_64S b).pre s) :
    Verified X86_64.target c (Proof.Sha512.updateX86_64S b) :=
  Verified.widen h (fun s => [⟨s.gpr .rdi, 192⟩, ⟨s.gpr .r8, a⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ => ⟨h₁, rfl, h₃.sub_right (Region.sub_prefix hab), h₄, h₅.sub_right (Region.sub_prefix hab), h₆,
      h₇.sub_right (Region.sub_prefix hab), h₈, h₉, h₁₀.sub_right (Region.sub_prefix hab)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hab⟩ .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- `finalize` verified with `a` bytes of scratch space is with any `b ≥ a`. -/
theorem finalizeS_widen {c : Prog isa} {a b : Nat} (h : Verified X86_64.target c (Proof.Sha512.finalizeX86_64S a))
    (hab : a ≤ b) (hsat : ∃ s, (Proof.Sha512.finalizeX86_64S b).pre s) :
    Verified X86_64.target c (Proof.Sha512.finalizeX86_64S b) :=
  Verified.widen h (fun s => [⟨s.gpr .rdi, 192⟩, ⟨s.gpr .rdx, 64⟩, ⟨s.gpr .rcx, a⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ => ⟨h₁, rfl, h₃, h₄.sub_right (Region.sub_prefix hab), h₅.sub_right (Region.sub_prefix hab),
      h₆, h₇, h₈.sub_right (Region.sub_prefix hab), h₉, h₁₀, h₁₁.sub_right (Region.sub_prefix hab)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hab⟩ .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- `Impl.Sha512.X86_64.Stream.updateOwn`, for an implementation of the
compression function correct with the scratch space it uses (`hf`), if it
never loads MXCSR. -/
theorem updateOwn_verified {f : Callee} (h : f.so = 0 ∨ f.so = 192 ∨ f.so = 1328)
    (hf : CalleeOk (P := paramsS f.so) md f.code)
    (hm : (Impl.Sha512.X86_64.Stream.updateOwn f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, Proof.Sha512.updateX86_64.pre s) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.updateOwn f) Proof.Sha512.updateX86_64 :=
  updateS_widen (a := f.so + 48)
    (MdStream.X86_64.Update.verified (dimsS f.so (by omega_using [h])) (taintsS3 f.so h) hf hm)
    (by omega_using [h]) hsat

/-- `Impl.Sha512.X86_64.Stream.finalizeOwn`, likewise. -/
theorem finalizeOwn_verified {f : Callee} (h : f.so = 0 ∨ f.so = 192 ∨ f.so = 1328)
    (hf : CalleeOk (P := paramsS f.so) md f.code)
    (hm : (Impl.Sha512.X86_64.Stream.finalizeOwn f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, Proof.Sha512.finalizeX86_64.pre s) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.finalizeOwn f) Proof.Sha512.finalizeX86_64 :=
  finalizeS_widen (a := f.so + 48)
    (MdStream.X86_64.Finalize.verified (dimsS f.so (by omega_using [h])) (shapeS f.so) (taintsS3 f.so h) hf hm)
    (by omega_using [h]) hsat

end VG.Proof.Sha512.X86_64.Stream
