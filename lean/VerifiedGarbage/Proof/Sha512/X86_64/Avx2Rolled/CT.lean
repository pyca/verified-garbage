module

public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Compress
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Compress
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum

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
