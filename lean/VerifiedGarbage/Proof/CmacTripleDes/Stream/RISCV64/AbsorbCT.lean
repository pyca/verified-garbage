module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Absorb
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.InitCT
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Absorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls
meta import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Streaming TDEA-CMAC on RISC-V: `absorb` in constant time

As `stream_init` (`InitCT.lean`): the code between the calls is constant
time by the taint analysis, from the registers that hold public values there
(`count`, `len`, the pointers, and what the code computes from them: the
bytes held back, the room after them, the blocks and the bytes left), pinned
by what the code before each piece leaves, and the calls by their own proof
(`ecb_rel`); the loop by `RelCT.loop`, with the blocks chained in both runs.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.Proof.CmacTripleDes.Stream (held)

section
variable {s₀ s₀' : State} {St D S : Addr} {n L : Nat}

/-- What `heldCode` leaves. -/
def HH (s₀ : State) (St D S : Addr) (n L : Nat) (s : State) : Prop :=
  ∃ s₁, AMid s₀ St D S n L s₁ ∧ s.gpr .t0 = BitVec.ofNat 64 (held n) ∧ (∀ r, r ≠ .t0 → s.gpr r = s₁.gpr r) ∧
    s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp

/-- What `absFlag` leaves. -/
def HF (s₀ : State) (St D S : Addr) (n L : Nat) (s : State) : Prop :=
  ∃ s₁, AMid s₀ St D S n L s₁ ∧ AFl St D S n L s₁ s

theorem HF.cpre {s : State} (h : HF s₀ St D S n L s) (hc : 8 - held n < L) : CPre s₀ St D S (held n) L s := by
  obtain ⟨s₁, h₁, hu⟩ := h
  exact ⟨by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s1],
    by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s2],
    by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s3],
    by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.a3], hu.t0, hu.t1,
    Proof.CmacTripleDes.Stream.held_le n, hc, by rw [hu.rd, h₁.rd], by rw [hu.wr, h₁.wr], by rw [hu.sp, h₁.sp]⟩

theorem HF.sp {s : State} (h : HF s₀ St D S n L s) : s.sp = s₀.sp := by
  obtain ⟨s₁, h₁, hu⟩ := h; rw [hu.sp, h₁.sp]

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (St D S : Addr) (h L : Nat) (m : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, m = nbOf L (8 - h) - k ∧ k < nbOf L (8 - h) ∧ (∃ e, CInv s₀ St D S h L e k s₁) ∧
    ∃ e, CInv s₀' St D S h L e k s₂

theorem body_ct (hp : APre s₀ St D S n L) (hp' : APre s₀' St D S n L) (qsp : s₀.sp = s₀'.sp) {h : Nat}
    (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < nbOf L (8 - h) ∧ (∃ e, CInv s₀ St D S h L e k s₁) ∧
      ∃ e, CInv s₀' St D S h L e k s₂) chainBody
      fun s₁ s₂ => (∃ e, CInv s₀ St D S h L e (k + 1) s₁) ∧ ∃ e, CInv s₀' St D S h L e (k + 1) s₂ := by
  obtain ⟨_, hA⟩ : ∃ hh, (taint.check (Taint.ofRegs [.s1, .s3, .s5])
      (.block (([.addi .t3 .s1 400] : List Instr) ++ Impl.Words.RISCV64.xorBytes .t0 .t1 .t3 .s3 8 ++
        ([.addi .s3 .s3 8, .addi .s5 .s5 (-1)] : List Instr) ++ ecbArgs 400)) hh).isSome = true := ⟨_, by taint_decide⟩
  refine (RelCT.exists_ (P := fun (hk : k < nbOf L (8 - h)) s₁ s₂ =>
      (∃ e, CInv s₀ St D S h L e k s₁) ∧ ∃ e, CInv s₀' St D S h L e k s₂) fun hk => ?_).mono
    (fun _ _ h => ⟨h.1, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ (P := fun e s₁ s₂ => CInv s₀ St D S h L e k s₁ ∧ ∃ e, CInv s₀' St D S h L e k s₂)
    fun e => ?_).mono (fun _ _ h => let ⟨e, he⟩ := h.1; ⟨e, he, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ (P := fun e' s₁ s₂ => CInv s₀ St D S h L e k s₁ ∧ CInv s₀' St D S h L e' k s₂)
    fun e' => ?_).mono (fun _ _ h => let ⟨e', he'⟩ := h.2; ⟨e', h.1, he'⟩) fun _ _ h => h
  have a := (taintRegs (P := fun s₁ s₂ => CInv s₀ St D S h L e k s₁ ∧ CInv s₀' St D S h L e' k s₂) [.s1, .s3, .s5]
    (fun s₁ s₂ hh => ⟨by rw [hh.1.sp, hh.2.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hh.1.s1, hh.2.s1]
      · rw [hh.1.s3, hh.2.s3]
      · rw [hh.1.s5, hh.2.s5]⟩) hA).wp
    (F₁ := fun s => ∃ s₁, CInv s₀ St D S h L e k s₁ ∧ BMid s₀ St D S h L e k s₁ s)
    (F₂ := fun s => ∃ s₁, CInv s₀' St D S h L e' k s₁ ∧ BMid s₀' St D S h L e' k s₁ s)
    fun s₁ s₂ hh => ⟨WP.mono (bodyBlk_wp hp hk hh.1) fun _ b => ⟨_, hh.1, b⟩,
      WP.mono (bodyBlk_wp hp' hk hh.2) fun _ b => ⟨_, hh.2, b⟩⟩
  have c := (ecb_rel (P := fun s₁ s₂ => (∃ x, CInv s₀ St D S h L e k x ∧ BMid s₀ St D S h L e k x s₁) ∧
      ∃ x, CInv s₀' St D S h L e' k x ∧ BMid s₀' St D S h L e' k x s₂)
    fun s₁ s₂ ⟨⟨_, _, b₁⟩, ⟨_, _, b₂⟩⟩ => ⟨b₁.args, b₂.args, by rw [b₁.sp, b₂.sp, qsp]⟩)
  have whole : RelCT isa (fun s₁ s₂ => CInv s₀ St D S h L e k s₁ ∧ CInv s₀' St D S h L e' k s₂) chainBody
      fun _ _ => True :=
    (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c
  exact (whole.wp (F₁ := fun s => ∃ e, CInv s₀ St D S h L e (k + 1) s)
    (F₂ := fun s => ∃ e, CInv s₀' St D S h L e (k + 1) s)
    fun s₁ s₂ hh => ⟨WP.mono (body_ok hp hk hh.1) fun _ x => ⟨e, x⟩,
      WP.mono (body_ok hp' hk hh.2) fun _ x => ⟨e', x⟩⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem loop_ct (hp : APre s₀ St D S n L) (hp' : APre s₀' St D S n L) (qsp : s₀.sp = s₀'.sp) {h : Nat}
    (m : Nat) :
    RelCT isa (LRel s₀ s₀' St D S h L m) (.loop chainBody (.nonzero .s5))
      fun s₁ s₂ => (∃ e, CInv s₀ St D S h L e (nbOf L (8 - h)) s₁) ∧
        ∃ e, CInv s₀' St D S h L e (nbOf L (8 - h)) s₂ := by
  have hN : nbOf L (8 - h) < 2 ^ 64 := by have := hp.hL; unfold nbOf; omega
  refine RelCT.loop (M := isa) (LRel s₀ s₀' St D S h L) (fun m => ?_) m
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (hh : LRel s₀ s₀' St D S h L m s₁ s₂) => hh) fun _ _ h => h
  by_cases hm : m = nbOf L (8 - h) - k
  swap
  · exact RelCT.of_false fun _ _ h => hm h.1
  subst hm
  by_cases hk : k < nbOf L (8 - h)
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  refine (body_ct hp hp' qsp k).mono (fun _ _ h => h.2) fun s₁ s₂ ⟨⟨e₁, l₁⟩, ⟨e₂, l₂⟩⟩ => ?_
  have bd : nbOf L (8 - h) - (k + 1) < 2 ^ 64 := by omega
  have v₁ := Steps.eval_nonzero_ofNat s₁ .s5 bd l₁.s5
  have v₂ := Steps.eval_nonzero_ofNat s₂ .s5 bd l₂.s5
  refine ⟨by rw [v₁, v₂], fun hf => ?_, fun ht => ?_⟩
  · rw [v₁] at hf
    have h0 : nbOf L (8 - h) = k + 1 := by
      have : nbOf L (8 - h) - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨⟨e₁, h0 ▸ l₁⟩, ⟨e₂, h0 ▸ l₂⟩⟩
  · rw [v₁] at ht
    have h0 : nbOf L (8 - h) - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨nbOf L (8 - h) - (k + 1), by omega, k + 1, rfl, by omega, ⟨e₁, l₁⟩, ⟨e₂, l₂⟩⟩

end


/-! ## The chaining path -/

/-- What the block before the last copy leaves. -/
theorem tailBlk_wp {s₀ e s : State} {St D S : Addr} {h L : Nat} (hi : CInv s₀ St D S h L e (nbOf L (8 - h)) s) :
    WP isa (.block [.addi .t3 .s1 408, mov .t4 .s3, mov .t5 .s4]) s fun s' =>
      s'.gpr .t3 = St + BitVec.ofNat 64 408 ∧
      s'.gpr .t4 = D + BitVec.ofNat 64 (8 - h + 8 * nbOf L (8 - h)) ∧
      s'.gpr .t5 = BitVec.ofNat 64 (tailOf L (8 - h)) ∧ s'.sp = s₀.sp := by
  unfold mov
  refine wp_addi (imm := 408) (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  exact ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hi.s1],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hi.s3],
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hi.s4], by rw [u₃.sp, u₂.sp, u₁.sp, hi.sp]⟩

theorem chain_ct {s₀ s₀' : State} {St D S : Addr} {n L : Nat} (hp : APre s₀ St D S n L)
    (hp' : APre s₀' St D S n L) (qsp : s₀.sp = s₀'.sp) :
    RelCT isa (fun a b => (HF s₀ St D S n L a ∧ HF s₀' St D S n L b) ∧ isa.eval (.nonzero .t2) a = some true)
      chainPath fun _ _ => True := by
  have hN : nbOf L (8 - held n) < 2 ^ 64 := by have := hp.hL; unfold nbOf; omega
  have hl : ∀ {a : State}, HF s₀ St D S n L a → isa.eval (.nonzero .t2) a = some true → 8 - held n < L :=
    fun {a} ⟨_, _, hu⟩ he => by
      rw [eval_nonzero, hu.t2] at he; split at he <;> simp_all
  -- The relations, by the pieces' correctness.
  obtain ⟨_, h1⟩ : ∃ hh, (taint.check (Taint.ofRegs [.a3, .t1, .s1, .t0, .s3])
      (.block (([.sub .s4 .a3 .t1] : List Instr) ++ toHeld .t1)) hh).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, h2⟩ : ∃ hh, (taint.check (Taint.ofRegs [.t3, .t4, .t5]) (copy .t6 .t4 .t3 .t5) hh).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, h3⟩ : ∃ hh, (taint.check (Taint.ofRegs [.s1, .s3, .s4, .t1]) (.block chainSetup) hh).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, h6⟩ : ∃ hh, (taint.check (Taint.ofRegs [.s1, .s3, .s4])
      (.block [.addi .t3 .s1 408, mov .t4 .s3, mov .t5 .s4]) hh).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ hh, (taint.check (Taint.ofRegs []) (.block []) hh).isSome = true := ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => (HF s₀ St D S n L a ∧ HF s₀' St D S n L b) ∧
      isa.eval (.nonzero .t2) a = some true) [.a3, .t1, .s1, .t0, .s3]
    (fun a b hh => by
      have c₁ := hh.1.1.cpre (hl hh.1.1 hh.2)
      have c₂ := hh.1.2.cpre (hl hh.1.1 hh.2)
      refine ⟨by rw [c₁.sp, c₂.sp, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [c₁.a3, c₂.a3]
      · rw [c₁.t1, c₂.t1]
      · rw [c₁.s1, c₂.s1]
      · rw [c₁.t0, c₂.t0]
      · rw [c₁.s3, c₂.s3]) h1).wp
    (F₁ := fun s => ∃ u, CPre s₀ St D S (held n) L u ∧ C1 s₀ St D S (held n) L u s)
    (F₂ := fun s => ∃ u, CPre s₀' St D S (held n) L u ∧ C1 s₀' St D S (held n) L u s)
    fun a b hh => ⟨WP.mono (pre1_wp (hh.1.1.cpre (hl hh.1.1 hh.2))) fun _ x => ⟨_, hh.1.1.cpre (hl hh.1.1 hh.2), x⟩,
      WP.mono (pre1_wp (hh.1.2.cpre (hl hh.1.1 hh.2))) fun _ x => ⟨_, hh.1.2.cpre (hl hh.1.1 hh.2), x⟩⟩
  have b := (taintRegs (P := fun a b => (∃ u, CPre s₀ St D S (held n) L u ∧ C1 s₀ St D S (held n) L u a) ∧
      ∃ u, CPre s₀' St D S (held n) L u ∧ C1 s₀' St D S (held n) L u b) [.t3, .t4, .t5]
    (fun a b ⟨⟨_, _, x₁⟩, ⟨_, _, x₂⟩⟩ => ⟨by rw [x₁.sp, x₂.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [x₁.t3, x₂.t3]
      · rw [x₁.t4, x₂.t4]
      · rw [x₁.t5, x₂.t5]⟩) h2).wp
    (F₁ := fun s => ∃ u, CPre s₀ St D S (held n) L u ∧ CCopy s₀ St D S (held n) L u s)
    (F₂ := fun s => ∃ u, CPre s₀' St D S (held n) L u ∧ CCopy s₀' St D S (held n) L u s)
    fun a b ⟨⟨_, c₁, x₁⟩, ⟨_, c₂, x₂⟩⟩ => ⟨WP.mono (copy1_wp hp c₁ x₁) fun _ y => ⟨_, c₁, y⟩,
      WP.mono (copy1_wp hp' c₂ x₂) fun _ y => ⟨_, c₂, y⟩⟩
  have c := (taintRegs (P := fun a b => (∃ u, CPre s₀ St D S (held n) L u ∧ CCopy s₀ St D S (held n) L u a) ∧
      ∃ u, CPre s₀' St D S (held n) L u ∧ CCopy s₀' St D S (held n) L u b) [.s1, .s3, .s4, .t1]
    (fun a b ⟨⟨_, _, x₁⟩, ⟨_, _, x₂⟩⟩ => ⟨by rw [x₁.sp, x₂.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [x₁.s1, x₂.s1]
      · rw [x₁.s3, x₂.s3]
      · rw [x₁.s4, x₂.s4]
      · rw [x₁.t1, x₂.t1]⟩) h3).wp
    (F₁ := fun s => ∃ c, CSet s₀ St D S (held n) L c s) (F₂ := fun s => ∃ c, CSet s₀' St D S (held n) L c s)
    fun a b ⟨⟨_, c₁, x₁⟩, ⟨_, c₂, x₂⟩⟩ => ⟨WP.mono (setup_wp hp c₁ x₁) fun _ y => ⟨_, y⟩,
      WP.mono (setup_wp hp' c₂ x₂) fun _ y => ⟨_, y⟩⟩
  have ie {s₀ : State} {z e : State} {c : State} (hz : CSet s₀ St D S (held n) L c z) (he : EPost z St 400 e) :
      CInv s₀ St D S (held n) L e 0 e :=
    ⟨by rw [he.saved _ (by decide), hz.s1], by rw [he.saved _ (by decide), hz.s2],
      by rw [he.saved _ (by decide), hz.s3, Nat.mul_zero, Nat.add_zero], by rw [he.saved _ (by decide), hz.s4],
      by rw [he.saved _ (by decide), hz.s5, Nat.sub_zero], fun _ _ _ _ => rfl, by rw [he.rd, hz.rd],
      by rw [he.wr, hz.wr], by rw [he.sp, hz.sp], Frame.refl _ _, rfl⟩
  have d := (ecb_rel (P := fun a b => (∃ c, CSet s₀ St D S (held n) L c a) ∧ ∃ c, CSet s₀' St D S (held n) L c b)
    fun a b ⟨⟨_, x₁⟩, ⟨_, x₂⟩⟩ => ⟨x₁.args, x₂.args, by rw [x₁.sp, x₂.sp, qsp]⟩).wp
    (F₁ := fun s => CInv s₀ St D S (held n) L s 0 s) (F₂ := fun s => CInv s₀' St D S (held n) L s 0 s)
    fun a b ⟨⟨_, x₁⟩, ⟨_, x₂⟩⟩ => ⟨WP.mono (ecb_call x₁.args) fun _ y => ie x₁ y,
      WP.mono (ecb_call x₂.args) fun _ y => ie x₂ y⟩
  have ev {t e s : State} (hi : CInv t St D S (held n) L e 0 s) :
      isa.eval (.zero .s5) s = some (decide (nbOf L (8 - held n) = 0)) := by
    have := Steps.eval_zero_ofNat s .s5 (k := nbOf L (8 - held n) - 0) (by omega) hi.s5
    rwa [Nat.sub_zero] at this
  have e : RelCT isa (fun a b => CInv s₀ St D S (held n) L a 0 a ∧ CInv s₀' St D S (held n) L b 0 b) chainLoop
      fun a b => (∃ e, CInv s₀ St D S (held n) L e (nbOf L (8 - held n)) a) ∧
        ∃ e, CInv s₀' St D S (held n) L e (nbOf L (8 - held n)) b := by
    refine RelCT.ite (fun a b hh => by rw [ev hh.1, ev hh.2]) ?_ ?_
    · refine ((taintRegs (P := fun a b => (CInv s₀ St D S (held n) L a 0 a ∧ CInv s₀' St D S (held n) L b 0 b) ∧
          isa.eval (.zero .s5) a = some true) [] (fun _ _ hh => ⟨by rw [hh.1.1.sp, hh.1.2.sp, qsp], fun r hr => by
            simp at hr⟩) hnil).wp
        (F₁ := fun s => ∃ e, CInv s₀ St D S (held n) L e (nbOf L (8 - held n)) s)
        (F₂ := fun s => ∃ e, CInv s₀' St D S (held n) L e (nbOf L (8 - held n)) s) fun a b hh => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : nbOf L (8 - held n) = 0 := by
        have := hh.2; rw [ev hh.1.1] at this; simpa using this
      exact ⟨WP.block_nil ⟨a, h0 ▸ hh.1.1⟩, WP.block_nil ⟨b, h0 ▸ hh.1.2⟩⟩
    · refine ((loop_ct (h := held n) hp hp' qsp (nbOf L (8 - held n) - 0)).mono
        (fun a b hh => ⟨0, rfl, ?_, ⟨a, hh.1.1⟩, ⟨b, hh.1.2⟩⟩) fun _ _ h => h)
      have := hh.2; rw [ev hh.1.1] at this
      have : nbOf L (8 - held n) ≠ 0 := by simpa using this
      omega
  have f := (taintRegs (P := fun a b => (∃ e, CInv s₀ St D S (held n) L e (nbOf L (8 - held n)) a) ∧
      ∃ e, CInv s₀' St D S (held n) L e (nbOf L (8 - held n)) b) [.s1, .s3, .s4]
    (fun a b ⟨⟨_, x₁⟩, ⟨_, x₂⟩⟩ => ⟨by rw [x₁.sp, x₂.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [x₁.s1, x₂.s1]
      · rw [x₁.s3, x₂.s3]
      · rw [x₁.s4, x₂.s4]⟩) h6).wp
    (F₁ := fun (s : State) => s.gpr .t3 = St + BitVec.ofNat 64 408 ∧
      s.gpr .t4 = D + BitVec.ofNat 64 (8 - held n + 8 * nbOf L (8 - held n)) ∧
      s.gpr .t5 = BitVec.ofNat 64 (tailOf L (8 - held n)) ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .t3 = St + BitVec.ofNat 64 408 ∧
      s.gpr .t4 = D + BitVec.ofNat 64 (8 - held n + 8 * nbOf L (8 - held n)) ∧
      s.gpr .t5 = BitVec.ofNat 64 (tailOf L (8 - held n)) ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨_, x₁⟩, ⟨_, x₂⟩⟩ => ⟨tailBlk_wp x₁, tailBlk_wp x₂⟩
  have g := taintRegs (P := fun a b => (a.gpr .t3 = St + BitVec.ofNat 64 408 ∧
      a.gpr .t4 = D + BitVec.ofNat 64 (8 - held n + 8 * nbOf L (8 - held n)) ∧
      a.gpr .t5 = BitVec.ofNat 64 (tailOf L (8 - held n)) ∧ a.sp = s₀.sp) ∧
      b.gpr .t3 = St + BitVec.ofNat 64 408 ∧
      b.gpr .t4 = D + BitVec.ofNat 64 (8 - held n + 8 * nbOf L (8 - held n)) ∧
      b.gpr .t5 = BitVec.ofNat 64 (tailOf L (8 - held n)) ∧ b.sp = s₀'.sp) [.t3, .t4, .t5]
    (fun a b hh => ⟨by rw [hh.1.2.2.2, hh.2.2.2.2, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hh.1.1, hh.2.1]
      · rw [hh.1.2.1, hh.2.2.1]
      · rw [hh.1.2.2.1, hh.2.2.2.1]⟩) h2
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((b.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((d.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      (e.seq ((f.mono (fun _ _ h => h) fun _ _ h => h.2).seq g)))))


/-! ## The whole function -/

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbRISCV64.pre s₀) (h0' : absorbRISCV64.pre s₀')
    (hq : absorbRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a4) (s₀.gpr .a1).toNat (s₀.gpr .a3).toNat := by
    rw [q3, q4, q5, q6, q7]; exact APre.of h0'
  generalize s₀.gpr .a0 = St at hp hp'
  generalize s₀.gpr .a2 = D at hp hp'
  generalize s₀.gpr .a4 = S at hp hp'
  generalize (s₀.gpr .a1).toNat = n at hp hp'
  generalize (s₀.gpr .a3).toNat = L at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (.block absSave) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.a1]) heldCode h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.t0, .a3]) (.block absFlag) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hF⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .t0, .s3, .a3]) fillPath h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hE⟩ : ∃ h, (taint.check (Taint.ofRegs [.s2]) (.block (restoreRegs absSaved)) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := AMid s₀ St D S n L) (F₂ := AMid s₀' St D S n L) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absSave_wp hp, absSave_wp hp'⟩
  have b := (taintRegs (P := fun a b => AMid s₀ St D S n L a ∧ AMid s₀' St D S n L b) [.a1]
    (fun a b h => ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h.1.a1, h.2.a1]⟩) hB).wp
    (F₁ := HH s₀ St D S n L) (F₂ := HH s₀' St D S n L) fun a b h =>
      ⟨WP.mono (heldCode_wp hp.hn h.1.a1) fun _ ⟨t0, g, m, rd, wr, sp⟩ => ⟨a, h.1, t0, g, m, rd, wr, sp⟩,
       WP.mono (heldCode_wp hp.hn h.2.a1) fun _ ⟨t0, g, m, rd, wr, sp⟩ => ⟨b, h.2, t0, g, m, rd, wr, sp⟩⟩
  have c := (taintRegs (P := fun a b => HH s₀ St D S n L a ∧ HH s₀' St D S n L b) [.t0, .a3]
    (fun a b ⟨⟨_, x₁, t₁, g₁, _, _, _, sp₁⟩, ⟨_, x₂, t₂, g₂, _, _, _, sp₂⟩⟩ =>
      ⟨by rw [sp₁, sp₂, x₁.sp, x₂.sp, qsp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [t₁, t₂]
        · rw [g₁ _ (by decide), g₂ _ (by decide), x₁.a3, x₂.a3]⟩) hC).wp
    (F₁ := HF s₀ St D S n L) (F₂ := HF s₀' St D S n L)
    fun a b ⟨⟨s₁, x₁, t₁, g₁, m₁, rd₁, wr₁, sp₁⟩, ⟨s₂, x₂, t₂, g₂, m₂, rd₂, wr₂, sp₂⟩⟩ =>
      ⟨WP.mono (absFlag_wp hp.hL x₁.a3 t₁ g₁ m₁ rd₁ wr₁ sp₁) fun _ y => ⟨s₁, x₁, y⟩,
       WP.mono (absFlag_wp hp.hL x₂.a3 t₂ g₂ m₂ rd₂ wr₂ sp₂) fun _ y => ⟨s₂, x₂, y⟩⟩
  have t2eq : ∀ {t : State} {s : State}, HF t St D S n L s → s.gpr .t2 = if 8 - held n < L then 1 else 0 :=
    fun {_ _} ⟨_, _, hu⟩ => hu.t2
  have fill := taintRegs (P := fun a b => (HF s₀ St D S n L a ∧ HF s₀' St D S n L b) ∧
      isa.eval (.nonzero .t2) a = some false) [.s1, .t0, .s3, .a3]
    (fun a b ⟨⟨⟨_, x₁, y₁⟩, ⟨_, x₂, y₂⟩⟩, _⟩ => ⟨by rw [y₁.sp, y₂.sp, x₁.sp, x₂.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [y₁.keep _ (by decide) (by decide) (by decide), y₂.keep _ (by decide) (by decide) (by decide), x₁.s1, x₂.s1]
      · rw [y₁.t0, y₂.t0]
      · rw [y₁.keep _ (by decide) (by decide) (by decide), y₂.keep _ (by decide) (by decide) (by decide), x₁.s3, x₂.s3]
      · rw [y₁.keep _ (by decide) (by decide) (by decide), y₂.keep _ (by decide) (by decide) (by decide), x₁.a3,
          x₂.a3]⟩) hF
  have d : RelCT isa (fun a b => HF s₀ St D S n L a ∧ HF s₀' St D S n L b) (.ite (.nonzero .t2) chainPath fillPath)
      fun _ _ => True :=
    RelCT.ite (fun a b h => by rw [eval_nonzero, eval_nonzero, t2eq h.1, t2eq h.2]) (chain_ct hp hp' qsp) fill
  have d' := d.wp (F₁ := fun (s : State) => s.gpr .s2 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s2 = S ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨s₁, x₁, y₁⟩, ⟨s₂, x₂, y₂⟩⟩ =>
      ⟨WP.mono (paths_wp hp x₁ y₁) fun _ z => ⟨by
          rw [z.keep _ (by decide) (by decide) (by decide) (by decide), y₁.keep _ (by decide) (by decide) (by decide),
            x₁.s2], z.sp⟩,
       WP.mono (paths_wp hp' x₂ y₂) fun _ z => ⟨by
          rw [z.keep _ (by decide) (by decide) (by decide) (by decide), y₂.keep _ (by decide) (by decide) (by decide),
            x₂.s2], z.sp⟩⟩
  have e := taintRegs (P := fun a b => (a.gpr .s2 = S ∧ a.sp = s₀.sp) ∧ b.gpr .s2 = S ∧ b.sp = s₀'.sp) [.s2]
    (fun a b h => ⟨by rw [h.1.2, h.2.2, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h.1.1, h.2.1]⟩) hE
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((b.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((d'.mono (fun _ _ h => h) fun _ _ h => h.2).seq e)))

theorem absorb_ct : ConstantTime isa absorbRISCV64.pre absorbRISCV64.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.RISCV64
