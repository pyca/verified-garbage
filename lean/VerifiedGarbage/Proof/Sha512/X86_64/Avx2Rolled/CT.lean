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

The taint analysis checks the prologue, the first and second halves of an iteration (`first`, `rest`) and
the epilogue, each from the pointers and the block count being public. It
cannot check an iteration in one go: `first` keeps `rdi` and `rdx` in the
scratch space while the schedule stores secret words through the index, at
offsets the analysis cannot bound, so it forgets that the slots hold public
values. The proof composes the checks (`RelCT`): at the start of each part,
the registers it needs public agree in both runs because each run's
correctness (`Compress.lean`) says what they hold, which the public data
determines.
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

theorem first_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τA s₁ s₂) :
    RelCT isa P first fun _ _ => True :=
  RelCT.taint (A := A) τA hp (by taint_decide)

theorem rest_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τA s₁ s₂) :
    RelCT isa P rest fun _ _ => True :=
  RelCT.taint (A := A) τA hp (by taint_decide)

theorem pro_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τA s₁ s₂) :
    RelCT isa P (.block (save ++ Impl.Sha512.X86_64.Avx2.const Impl.Sha512.X86_64.Avx2.mBswap
      Impl.Sha512.X86_64.Avx2.bswapMask ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) fun _ _ => True :=
  RelCT.taint (A := A) τA hp (by taint_decide)

theorem res_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τR s₁ s₂) :
    RelCT isa P (.block restore) fun _ _ => True :=
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
    s₁.syms = s₀.syms ∧ s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) ∧ Masks s₁ ∧
    (s₁.xmm .xmm14).extractLsb' 0 64 = s₀.gpr .r14 ∧ (s₁.xmm .xmm15).extractLsb' 0 64 = s₀.gpr .r15

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
  refine RelCT.seq hpro (RelCT.seq (Q := fun _ _ => True)
    (R := fun a b => Common σ₁ (nb σ₁) a ∧ Common σ₂ (nb σ₂) b) ?_ ?_)
  · refine RelCT.ite (fun a b ⟨_, p₁, p₂⟩ => by
      show a.zf = b.zf
      rw [p₁.2.2.2.2.2.1, p₂.2.2.2.2.2.1, e_rdx]) ?_ ?_
    · refine (rel_nil).mono (fun _ _ h => h) fun a b ⟨⟨_, p₁, p₂⟩, he⟩ => ?_
      obtain ⟨hg₁, hrd₁, hwr₁, hm₁, hsy₁, hz₁, hk₁, x₁, y₁⟩ := p₁
      obtain ⟨hg₂, hrd₂, hwr₂, hm₂, hsy₂, hz₂, hk₂, x₂, y₂⟩ := p₂
      have he₂ : b.zf = some true := by rw [hz₂, ← e_rdx, ← hz₁]; exact he
      have z₁ : nb σ₁ = 0 := by
        have := he; simp only [eval, hz₁, Option.some.injEq] at this; simp at this; simp [nb, this]
      have z₂ : nb σ₂ = 0 := by rw [hnb]; exact z₁
      exact ⟨z₁ ▸ common_zero h₁ hg₁ hrd₁ hwr₁ hm₁ hsy₁ hk₁ x₁ y₁,
        z₂ ▸ common_zero h₂ hg₂ hrd₂ hwr₂ hm₂ hsy₂ hk₂ x₂ y₂⟩
    · let I : Nat → State → State → Prop := fun n a b =>
        ∃ i, n = nb σ₁ - i ∧ i < nb σ₁ ∧ LInv σ₁ i a ∧ LInv σ₂ i b
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
      have agA : ∀ {i a b}, AtLeave σ₁ i a → AtLeave σ₂ i b → A.Agree τA a b := fun {i a b} l₁ l₂ =>
        agreeA (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · rw [l₁.rdi, l₂.rdi]; exact e_rdi
            · rw [l₁.rsi, l₂.rsi]; simp only [blkAddr, bp, e_rsi]
            · rw [l₁.rdx, l₂.rdx, hnb]
            · rw [l₁.rcx, l₂.rcx]; exact e_rcx)
          (wr_eq h₁ l₁.wr l₁.rdi l₁.rcx) (wr_eq h₂ l₂.wr l₂.rdi l₂.rcx) (st_scr' h₁ l₁.rdi l₁.rcx)
          (st_scr' h₂ l₂.rdi l₂.rcx)
      have hstep : ∀ n, RelCT isa (I n) body fun a b => isa.eval .ne a = isa.eval .ne b ∧
          (isa.eval .ne a = some false → Common σ₁ (nb σ₁) a ∧ Common σ₂ (nb σ₂) b) ∧
          (isa.eval .ne a = some true → ∃ m < n, I m a b) := by
        intro n
        refine RelCT.exists_ fun i => ?_
        by_cases hi : i < nb σ₁
        swap
        · exact RelCT.of_false fun _ _ h => hi h.2.1
        by_cases hn : n = nb σ₁ - i
        swap
        · exact RelCT.of_false fun _ _ h => hn h.1
        have hi₂ : i < nb σ₂ := by rw [hnb]; exact hi
        refine RelCT.seq (R := fun a b => AtLeave σ₁ i a ∧ AtLeave σ₂ i b) ?_ ?_
        · exact ((first_rel (P := fun a b => n = nb σ₁ - i ∧ i < nb σ₁ ∧ LInv σ₁ i a ∧ LInv σ₂ i b)
            fun a b h => agL h.2.2.1 h.2.2.2).wp (F₁ := AtLeave σ₁ i) (F₂ := AtLeave σ₂ i)
            fun a b h => ⟨prefix_ok h₁ hi h.2.2.1, prefix_ok h₂ hi₂ h.2.2.2⟩).mono (fun _ _ h => h)
            fun _ _ h => h.2
        · refine ((rest_rel (P := fun a b => AtLeave σ₁ i a ∧ AtLeave σ₂ i b) fun a b h => agA h.1 h.2).wp
            (F₁ := BodyPost σ₁ i) (F₂ := BodyPost σ₂ i)
            fun a b h => ⟨rest_ok h₁ hi h.1, rest_ok h₂ hi₂ h.2⟩).mono (fun _ _ h => h) fun a b ⟨_, q₁, q₂⟩ => ?_
          have hx : nxtI σ₂ i = nxtI σ₁ i := by simp only [nxtI, hnb]
          rcases q₁ with ⟨x₁, f₁, c₁⟩ | ⟨x₁, t₁, l₁⟩ <;> rcases q₂ with ⟨x₂, f₂, c₂⟩ | ⟨x₂, t₂, l₂⟩
          · exact ⟨f₁.trans f₂.symm, fun _ => ⟨c₁, c₂⟩, fun h => absurd (h.symm.trans f₁) (by simp)⟩
          · exfalso; rw [hx, hnb] at x₂; omega
          · exfalso; rw [hx, hnb] at x₂; omega
          · refine ⟨t₁.trans t₂.symm, fun h => absurd (h.symm.trans t₁) (by simp),
              fun _ => ⟨nb σ₁ - nxtI σ₁ i, ?_, nxtI σ₁ i, rfl, x₁, l₁, hx ▸ l₂⟩⟩
            have : i < nxtI σ₁ i := by simp only [nxtI]; split <;> omega
            omega
      refine (RelCT.loop I hstep (nb σ₁)).mono (fun a b ⟨⟨_, p₁, p₂⟩, he⟩ => ?_) fun _ _ h => h
      obtain ⟨hg₁, hrd₁, hwr₁, hm₁, hsy₁, hz₁, hk₁, x₁, y₁⟩ := p₁
      obtain ⟨hg₂, hrd₂, hwr₂, hm₂, hsy₂, hz₂, hk₂, x₂, y₂⟩ := p₂
      have hpos : 0 < nb σ₁ := by
        have := he; simp only [eval, hz₁, Option.some.injEq] at this
        simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at this
        exact Nat.pos_of_ne_zero fun h' => this (BitVec.eq_of_toNat_eq (by simpa using h'))
      have c₁ := common_zero h₁ hg₁ hrd₁ hwr₁ hm₁ hsy₁ hk₁ x₁ y₁
      have c₂ := common_zero h₂ hg₂ hrd₂ hwr₂ hm₂ hsy₂ hk₂ x₂ y₂
      exact ⟨0, rfl, hpos,
        { c₁ with rsi := by rw [hg₁ _ (by decide)]; simp [blkAddr], rdx := by rw [hg₁ _ (by decide)]; simp [nb] },
        { c₂ with rsi := by rw [hg₂ _ (by decide)]; simp [blkAddr], rdx := by rw [hg₂ _ (by decide)]; simp [nb] }⟩
  · exact res_rel fun a b ⟨c₁, c₂⟩ => agreeR (by rw [c₁.rcx, c₂.rcx]; exact e_rcx)

theorem compress_ct : ConstantTime isa Pre PubK compress :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => (compress_rel h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Sha512.X86_64.Avx2.Rolled
