import VerifiedGarbage.Proof.AesOcb.X86.Seal

/-!
# AES-OCB on x86: constant time, the shared pieces

Untrusted: everything here is checked by Lean. The taint analysis knows the
registers, not memory, so a value loaded from a slot is secret to it: where
a block uses such a value as an address, it is split there
(`RelCT.block_append`), and the value is pinned by what the first part
leaves. The loops whose condition comes from memory are run for their
number of iterations (`CT.loopN`). Here: pinned registers (`pin1` …),
`lNtz` (`lNtz_ct`), the calls of `vg_aes_*_blocks` (`callBlocks_ct`) and
`padTo` (`padTo_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ntz)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq copyLoop_ct)

/-- One register pinned. -/
theorem pin1 {I : State → Prop} {a : Reg} {x : BitVec 32} (h : ∀ s, I s → s.gpr a = x) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h _ h₁, h _ h₂]

/-- Four registers pinned. -/
theorem pin4 {I : State → Prop} {a b c d : Reg} {x y z w : BitVec 32}
    (h : ∀ s, I s → s.gpr a = x ∧ s.gpr b = y ∧ s.gpr c = z ∧ s.gpr d = w) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a, b, c, d], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [(h _ h₁).1, (h _ h₂).1]
  · rw [(h _ h₁).2.1, (h _ h₂).2.1]
  · rw [(h _ h₁).2.2.1, (h _ h₂).2.2.1]
  · rw [(h _ h₁).2.2.2, (h _ h₂).2.2.2]

/-- A loop of `n` iterations, its body constant time and leaving the
condition to loop back exactly while iterations are left. -/
theorem CT.loopN {body : Prog isa} {c : Cond} (Inv : Nat → State → Prop)
    (hb : ∀ n, CT (Inv n) body)
    (hw : ∀ n s, Inv n s → WP isa body s fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s'))
    (n : Nat) : CT (Inv n) (.loop body c) := by
  refine RelCT.loop (M := isa) (Q := fun _ _ => True) (fun n (s₁ s₂ : State) => Inv n s₁ ∧ Inv n s₂) (fun n => ?_) n
  have h := RelCT.wp (hb n) (F₁ := fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s')) (F₂ := fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s')) fun s₁ s₂ h => ⟨hw n s₁ h.1, hw n s₂ h.2⟩
  refine RelCT.mono h (fun _ _ h => h) fun s₁ s₂ ⟨_, ⟨hn, c₁, i₁⟩, ⟨_, c₂, i₂⟩⟩ => ⟨by rw [c₁, c₂], fun _ => trivial,
    fun ht => ?_⟩
  rw [c₁] at ht
  have h1 : n ≠ 1 := by simpa using ht
  exact ⟨n - 1, by omega, i₁ h1, i₂ h1⟩

/-! ## `lNtz` -/

/-- What `lNtz`'s loop needs: `n` iterations are left while `W + kO` holds
an even `k` with `ntz(k) = n`. -/
def NtzInv (p : Prm) (n : Nat) (t : State) : Prop :=
  Env p t ∧ ∃ k, 0 < k ∧ k % 2 = 0 ∧ k < 2 ^ 32 ∧ ntz k = n ∧ slotv t.mem p.W kO = BitVec.ofNat 32 k

theorem lNtz_ct {I : State → Prop} {p : Prm} (L : Lay p) {i : Nat} (hi : 0 < i) (hi' : i < 2 ^ 32)
    (hI : ∀ s, I s → Env p s ∧ s.gpr .edi = BitVec.ofNat 32 i) : CT I lNtz := by
  unfold lNtz
  refine CT.seq (J := fun t => Env p t ∧ slotv t.mem p.W kO = BitVec.ofNat 32 i ∧
      t.zf = some (decide (i % 2 = 0)))
    (CT.taint [.ebp, .edi] (pin2 fun s h => ⟨(hI s h).1.ebp, (hI s h).2⟩) (by taint_decide)) (fun s hs => ?_) ?_
  · obtain ⟨E, hdi⟩ := hI s hs
    obtain ⟨s₂, run₂, fr₂, -, k₂, zf₂, g₂, rd₂, wr₂⟩ := lNtzHead_ok L E hi' hdi
    exact WP.of_runBlock ⟨s₂, run₂, E.mut L (by rw [g₂ _ (by decide), E.ebp]) (by rw [g₂ _ (by decide), E.esp])
      rd₂ wr₂ (frame_toMut fr₂ (inMut_lNtzR p)), k₂, zf₂⟩
  refine CT.ite (decide (i % 2 = 0)) (fun _ h => eval_e h.2.2) (fun hb => ?_) (fun _ => CT.nil)
  have he : i % 2 = 0 := of_decide_eq_true hb
  refine (CT.loopN (NtzInv p) (fun _ => by exact CT.taint [.ebp] (pin1 fun _ h => h.1.ebp) (by taint_decide))
    (fun n t ⟨Et, k, hk0, hke, hk, hn, kt⟩ => ?_) (ntz i)).mono fun t ⟨Et, kt, _⟩ => ⟨Et, i, hi, he, hi', rfl, kt⟩
  obtain ⟨t₂, run, fr, -, kt', zf', g', rd', wr'⟩ := lNtzStep_ok L Et hk kt
  have hn' : n = ntz (k / 2) + 1 := by rw [← hn, Proof.Ocb.ntz_even hk0 hke]
  have hodd : k / 2 % 2 = 0 ↔ n ≠ 1 := by
    constructor
    · intro h; rw [hn', Proof.Ocb.ntz_even (by omega) h]; omega
    · intro h; by_contra h'; exact h (by rw [hn', Proof.Ocb.ntz_odd (by omega)])
  refine WP.of_runBlock ⟨t₂, run, by omega, (eval_e zf').trans (by simp only [decide_eq_decide.mpr hodd]),
    fun h1 => ⟨Et.mut L (by rw [g' _ (by decide) (by decide) (by decide), Et.ebp])
      (by rw [g' _ (by decide) (by decide) (by decide), Et.esp]) rd' wr' (frame_toMut fr (inMut_lNtzR p)),
      k / 2, by omega, hodd.mpr h1, by omega, by omega, kt'⟩⟩

/-! ## Calls -/

/-- `callBlocks`: `args` (constant time from `ebp`, `hct`), which leave the
blocks' address and number public, then the call. -/
theorem callBlocks_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub fn.code)
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {I : State → Prop} {p : Prm} (L : Lay p)
    {args : List Instr} {D : BitVec 32} {n : Nat}
    (hI : ∀ s, I s → Env p s ∧ DReg p s D n ∧ ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .edx = D ∧
      s₁.gpr .ebx = BitVec.ofNat 32 n ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr)
    (hct : ∀ {J : State → Prop}, (∀ s, J s → s.gpr .ebp = p.W) →
      CT J (.block (args ++ [.mov .eax (slot ctxO), .mov .ecx (slot rndO), .alu .add .ebp (imm scrO)]))) :
    CT I (callBlocks fn args) := by
  unfold callBlocks
  refine CT.seq (J := fun s₁ => BCall s₁ p.K D (p.W + BitVec.ofNat 32 scrO) p.R n ∧ s₁.gpr .esp = p.SP)
    (hct fun s h => (hI s h).1.ebp) (fun s hs => ?_)
    (CT.seq (J := fun s => s.gpr .ebp = p.W + BitVec.ofNat 32 scrO) (blk_ct ok ct fun s h => h)
      (fun s h => WP.mono (blk_call ok nosp stack h.1) fun s' P => by rw [P.saved _ (by decide), h.1.ebp])
      (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)))
  obtain ⟨E, hD, s₁, run₁, dx₁, bx₁, g₁, m₁, rd₁, wr₁⟩ := hI s hs
  have E₁ : Env p s₁ := E.keep (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁
  obtain ⟨s₂, run₂, bc, hsp, -⟩ := callArgs_ok L E₁ dx₁ bx₁ (hD.of_eq wr₁)
  exact WP.of_runBlock ⟨s₂, Proof.AesGcm.X86.runBlock_app_of run₁ run₂, bc, hsp⟩

/-- `callBlocks` of one block of `W`. -/
theorem oneCall_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub fn.code)
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {I : State → Prop} {p : Prm} (L : Lay p) {d : Nat}
    (hd : d = tmpO ∨ d = bufO) (hI : ∀ s, I s → Env p s) : CT I (callBlocks fn (oneBlock d)) := by
  refine callBlocks_ct ok ct nosp stack L (fun s h => ⟨hI s h, DReg.w L (hI s h) (n := 1)
    (by rcases hd with rfl | rfl <;> decide) (by rcases hd with rfl | rfl <;> decide), oneBlock_ok (hI s h) d⟩) fun hJ => ?_
  rcases hd with rfl | rfl
  · exact CT.taint [.ebp] (pin_ebp hJ) (by taint_decide)
  · exact CT.taint [.ebp] (pin_ebp hJ) (by taint_decide)

/-! ## `padTo` -/

theorem padTo_ct {I : State → Prop} {p : Prm} (L : Lay p) {S : BitVec 32} {n d : Nat}
    (hd : d = bufO ∨ d = t2O)
    (hI : ∀ s, I s → Env p s ∧ s.gpr .esi = S ∧ slotv s.mem p.W restO = BitVec.ofNat 32 n) :
    CT I (padTo d restO) := by
  have hJ : ∀ s, I s → WP isa (.block (zero4 d ++ ([.mov .edi (.reg .esi), .mov .edx (.reg .ebp),
      .alu .add .edx (imm d), .mov .ecx (slot restO)] : List Instr))) s
      (fun t => t.gpr .edi = S ∧ t.gpr .edx = p.W + BitVec.ofNat 32 d ∧ t.gpr .ecx = BitVec.ofNat 32 n) :=
    fun s hs => by
      obtain ⟨E, hsi, hc⟩ := hI s hs
      obtain ⟨s₁, run₁, -, di₁, dx₁, cx₁, -⟩ := padToHead_ok L E (S := S) (n := n) (d := d) (cO := restO)
        (by rcases hd with rfl | rfl <;> decide) (by decide) (by rcases hd with rfl | rfl <;> decide) hsi hc
      exact WP.of_runBlock ⟨s₁, run₁, di₁, dx₁, cx₁⟩
  unfold padTo
  rcases hd with rfl | rfl
  · exact CT.seq (CT.taint [.ebp, .esi] (pin2 fun s h => ⟨(hI s h).1.ebp, (hI s h).2.1⟩) (by taint_decide)) hJ
      (CT.taint [.edi, .edx, .ecx] (pin3 fun _ h => h) (by taint_decide))
  · exact CT.seq (CT.taint [.ebp, .esi] (pin2 fun s h => ⟨(hI s h).1.ebp, (hI s h).2.1⟩) (by taint_decide)) hJ
      (CT.taint [.edi, .edx, .ecx] (pin3 fun _ h => h) (by taint_decide))

/-! ## Loads of public slots -/

/-- A block followed by code, as its two parts in sequence: it runs the same
and leaks the same trace. -/
theorem CT.block_split {I : State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    (h : CT I (.seq (.block l₁) (.seq (.block l₂) c))) : CT I (.seq (.block (l₁ ++ l₂)) c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq b₁ k₁ =>
    cases e₂ with
    | seq b₂ k₂ =>
      rw [Exec.block_iff, execBlock_append] at b₁ b₂
      obtain ⟨⟨a₁, u₁⟩, ha₁, hb₁⟩ := Option.bind_eq_some_iff.mp b₁
      obtain ⟨⟨c₁, w₁⟩, hc₁, he₁⟩ := Option.map_eq_some_iff.mp hb₁
      obtain ⟨⟨a₂, u₂⟩, ha₂, hb₂⟩ := Option.bind_eq_some_iff.mp b₂
      obtain ⟨⟨c₂, w₂⟩, hc₂, he₂⟩ := Option.map_eq_some_iff.mp hb₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha₁) (.seq (.block hc₁) k₁))
        (.seq (.block ha₂) (.seq (.block hc₂) k₂))
      simp only [List.append_assoc]
      exact ⟨ht, hq⟩

/-- What a load of `v` into `r` leaves, from a state satisfying `I`. -/
def Ld (I : State → Prop) (r : Reg) (v : BitVec 32) (s : State) : Prop :=
  ∃ s₀, I s₀ ∧ s.gpr r = v ∧ (∀ q, q ≠ r → s.gpr q = s₀.gpr q) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- A block that starts with a load of a public slot, then code: the rest
is constant time once the value is in its register. -/
theorem load_ct {I : State → Prop} {p : Prm} (L : Lay p) {r : Reg} {o : Nat} (ho : o + 4 ≤ 2560) {v : BitVec 32}
    {rest : List Instr} {c : Prog isa} (hI : ∀ s, I s → Env p s ∧ slotv s.mem p.W o = v)
    (h₁ : CT (fun s => s.gpr .ebp = p.W) (.block [.mov r (slot o)]))
    (h : CT (Ld I r v) (.seq (.block rest) c)) : CT I (.seq (.block (.mov r (slot o) :: rest)) c) := by
  rw [← List.singleton_append]
  refine CT.block_split (CT.seq (J := Ld I r v) (h₁.mono fun s hs => (hI s hs).1.ebp) (fun s hs => ?_) h)
  obtain ⟨E, hv⟩ := hI s hs
  simp only [slotv_eq] at hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR ho, hv], s, hs, by gregs [hv],
    fun q hq => by gregs [hq], by gmems [], by gmems [], by gmems []⟩

/-- A block that starts with a load of a public slot. -/
theorem load_blk_ct {I : State → Prop} {p : Prm} (L : Lay p) {r : Reg} {o : Nat} (ho : o + 4 ≤ 2560)
    {v : BitVec 32} {rest : List Instr} (hI : ∀ s, I s → Env p s ∧ slotv s.mem p.W o = v)
    (h₁ : CT (fun s => s.gpr .ebp = p.W) (.block [.mov r (slot o)]))
    (h : CT (Ld I r v) (.block rest)) : CT I (.block (.mov r (slot o) :: rest)) := by
  rw [← List.singleton_append]
  refine RelCT.block_append (CT.seq (J := Ld I r v) (h₁.mono fun s hs => (hI s hs).1.ebp) (fun s hs => ?_) h)
  obtain ⟨E, hv⟩ := hI s hs
  simp only [slotv_eq] at hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR ho, hv], s, hs, by gregs [hv],
    fun q hq => by gregs [hq], by gmems [], by gmems [], by gmems []⟩

/-- A register other than the one loaded keeps what `I` says of it. -/
theorem Ld.reg {I : State → Prop} {r q : Reg} {v x : BitVec 32} (hq : q ≠ r) (h : ∀ s, I s → s.gpr q = x) :
    ∀ s, Ld I r v s → s.gpr q = x := fun _ ⟨s₀, h₀, _, g, _⟩ => by rw [g q hq, h s₀ h₀]

/-- The environment, across a load into a register other than `ebp` and `esp`. -/
theorem Ld.env {I : State → Prop} {p : Prm} {r : Reg} {v : BitVec 32} (h1 : r ≠ .ebp) (h2 : r ≠ .esp)
    (h : ∀ s, I s → Env p s) : ∀ s, Ld I r v s → Env p s := fun _ ⟨s₀, h₀, _, g, m, rd, wr⟩ =>
  (h s₀ h₀).keep (g _ (Ne.symm h1)) (g _ (Ne.symm h2)) rd wr m

end VG.Proof.AesOcb.X86
