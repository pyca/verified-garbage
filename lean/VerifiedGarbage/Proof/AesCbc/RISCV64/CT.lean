module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
meta import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified

/-!
# AES-CBC on RISC-V: constant time

As on PPC64LE (`Proof/AesCbc/PPC64LE/CT.lean`): two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proof pins to the public arguments (`LInv`) and the stack
pointer, and each call of a block function is constant time by its own
proof (`blk_rel`). (The taint analysis alone cannot see through the calls:
the block functions reload the callee-saved registers from memory, which it
counts as secret.) `whole_ct`: if one run of `body` is (`BodyCt`), `whole
body` is.
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64 VG.Impl.AesCbc.RISCV64

/-- Calls of a block function on one block, with the same arguments in both
runs, are constant time. -/
theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksRISCV64 f).pre (Proof.Aes.blocksRISCV64 f).pub c)
    {P : State → State → Prop} {W D S : Addr} {R : Nat}
    (h : ∀ s₁ s₂, P s₁ s₂ → CallPre s₁ W D S R ∧ CallPre s₂ W D S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name c) fun _ _ => True := by
  refine RelCT.call ok ct [⟨W, 240⟩] [⟨D, 16⟩, ⟨S, 2048⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.blk_pre, h₂.blk_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.blocksRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a4 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- Code the taint analysis proves constant time from the registers `rs`
(and the stack pointer). -/
theorem taintRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r h' => (hr x y hp).2 r (Taint.mem_ofRegs.mp h')⟩) h

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

section
variable {M : Mode} {s₀ s₀' : State} (hq : (modeRISCV64 M).pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_a1 : s₀.gpr .a1 = s₀'.gpr .a1 := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_a1 hq]
theorem pub_Iv : Iv s₀ = Iv s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2
theorem pub_blk (k : Nat) : blk s₀ k = blk s₀' k := by rw [blk, blk, pub_Dp hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv M s₀ k s₁) (h₂ : LInv M s₀' k s₂) :
    ∀ r ∈ vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.s1, h₂.s1, pub_W hq]
  · rw [h₁.s2, h₂.s2, pub_a1 hq]
  · rw [h₁.s3, h₂.s3, pub_Iv hq]
  · rw [h₁.s4, h₂.s4, pub_blk hq]
  · rw [h₁.s5, h₂.s5, pub_N hq]
  · rw [h₁.s6, h₂.s6, pub_S hq]

end

/-- One run of `body` from `k` blocks is constant time. -/
def BodyCt (M : Mode) (body : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (modeRISCV64 M).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂) body fun _ _ => True

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (D : Addr) (s : State) : Prop where
  pre : CallPre s (W s₀) D (S s₀) (R s₀)
  s3 : s.gpr .s3 = Iv s₀
  s4 : s.gpr .s4 = blk s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  s6 : s.gpr .s6 = S s₀
  sp : s.sp = s₀.sp

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  s3 : s.gpr .s3 = Iv s₀
  s4 : s.gpr .s4 = blk s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  s6 : s.gpr .s6 = S s₀
  sp : s.sp = s₀.sp

theorem Mid.of {s₀ : State} {k : Nat} {D : Addr} {m : Mem} {s s₁ : State} {M : Mode} (h : LInv M s₀ k s)
    (a : Pre s₀ D m s s₁) : Mid s₀ k D s₁ :=
  ⟨a.pre, by rw [a.saved .s3 (by decide), h.s3], by rw [a.saved .s4 (by decide), h.s4],
    by rw [a.saved .s5 (by decide), h.s5], by rw [a.saved .s6 (by decide), h.s6], a.sp.trans h.sp⟩

theorem After.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat}
    {D : Addr} {s s' : State} (h : Mid s₀ k D s) (hc : CallPost f s (W s₀) D (S s₀) (R s₀) s') :
    After s₀ k s' :=
  ⟨by rw [hc.saved .s3 (by decide), h.s3], by rw [hc.saved .s4 (by decide), h.s4],
    by rw [hc.saved .s5 (by decide), h.s5], by rw [hc.saved .s6 (by decide), h.s6],
    hc.sp.trans h.sp⟩

/-- A body: code before the call (`pre`), the call of a block function on
the block at `D s₀ k` (public), and code after it (`post`), constant time
when `pre`'s addresses and branches depend only on the registers the
invariant pins and `post`'s on `s3` to `s6`. -/
theorem body_ct {M : Mode} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {name : String} {c : Prog isa} {pre post : List Instr} {D : State → Nat → Addr}
    (pubD : ∀ {s₀ s₀' : State}, (modeRISCV64 M).pub s₀ s₀' → ∀ k, D s₀ k = D s₀' k)
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksRISCV64 f).pre (Proof.Aes.blocksRISCV64 f).pub c)
    (nf : c.noFrames = true)
    (hA : ∃ h, (taint.check (Taint.ofRegs vars) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6]) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv M s₀ k s →
      WP isa (.block pre) s fun s₁ => ∃ m, Pre s₀ (D s₀ k) m s s₁)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeRISCV64 M).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂)
      (.seq (.block pre) (.seq (.call name c) (.block post))) fun _ _ => True := by
  obtain ⟨_, hA⟩ := hA
  obtain ⟨_, hB⟩ := hB
  have a := (taintRegs (P := fun s₁ s₂ => k < N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂) vars
    (fun _ _ h => ⟨by rw [h.2.1.sp, h.2.2.sp, pub_sp hq], LInv.agree hq h.2.1 h.2.2⟩) hA).wp
    (F₁ := Mid s₀ k (D s₀ k)) (F₂ := Mid s₀' k (D s₀' k)) fun _ _ h =>
      ⟨WP.mono (wpA hp h.1 h.2.1) fun _ ⟨_, a⟩ => Mid.of h.2.1 a,
       WP.mono (wpA hp' (by rw [← pub_N hq]; exact h.1) h.2.2) fun _ ⟨_, a⟩ => Mid.of h.2.2 a⟩
  have c := (blk_rel (name := name) ok ct (P := fun s₁ s₂ => Mid s₀ k (D s₀ k) s₁ ∧ Mid s₀' k (D s₀' k) s₂)
    fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_S hq, pubD hq k, pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, pub_sp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call (name := name) ok nf h.1.pre) fun _ hc => After.of h.1 hc,
       WP.mono (blk_call (name := name) ok nf h.2.pre) fun _ hc => After.of h.2 hc⟩
  have b := taintRegs (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) [.s3, .s4, .s5, .s6]
    (fun s₁ s₂ h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.s3, h.2.s3, pub_Iv hq]
      · rw [h.1.s4, h.2.s4, pub_blk hq]
      · rw [h.1.s5, h.2.s5, pub_N hq]
      · rw [h.1.s6, h.2.s6, pub_S hq]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-- The block XORed with the one at `s3`, and the arguments of a call on it (as before AES-XTS's
encryption, `Proof/AesXts/RISCV64/Body.lean`). -/
theorem encA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv M s₀ k s) :
    WP isa (.block (xorInto .s4 .s3 ++ callArgs)) s fun s₁ => ∃ m, Pre s₀ (blk s₀ k) m s s₁ :=
  xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    h.s4 h.s3 (h.rIv hp) (h.wBlk hp hk) (hp.blk_iv hk) fun s₁ g₁ _ _ rd₁ wr₁ sp₁ =>
      WP.mono (callArgs_pre hp hk h (fun r hr => g₁ r (preserved_ne hr).2.2.1 (preserved_ne hr).2.2.2)
        rfl rd₁ wr₁ sp₁) fun _ a => ⟨_, a⟩

theorem encPre_taint : ∃ h, (taint.check (Taint.ofRegs vars)
    (.block (xorInto .s4 .s3 ++ callArgs)) h).isSome = true := ⟨_, by taint_decide⟩

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (M : Mode) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂

theorem loop_ct {M : Mode} {body : Prog isa} (hb : BodyOk M body) (hc : BodyCt M body)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeRISCV64 M).pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel M s₀ s₀' n) (.loop body (.nonzero .s5))
      fun s₁ s₂ => LInv M s₀ (N s₀) s₁ ∧ LInv M s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel M s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hb₀ := (s₀.gpr .a4).isLt
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel M s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (hc hp hp' hq k).wp (F₁ := LInv M s₀ (k + 1)) (F₂ := LInv M s₀' (k + 1))
    fun _ _ h => ⟨hb hp h.1 h.2.1, hb hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, l₁, l₂⟩ => ?_
  have bd : N s₀ - (k + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb₀
  have e₁ := Steps.eval_nonzero_ofNat s₁ .s5 bd l₁.s5
  have e₂ := Steps.eval_nonzero_ofNat s₂ .s5 (k := N s₀ - (k + 1)) bd (by rw [l₂.s5, hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, by omega, l₁, l₂⟩

/-! ## The whole function -/

theorem prologue_taint : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
    (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩

theorem epilogue_taint : ∃ h, (taint.check (Taint.ofRegs [.s6]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The registers saved and the arguments set up, `mid` run unless there are
no blocks, and the registers restored, constant time when two runs of `mid`
from the invariant after no blocks are (`whole_rel`: `body`'s loop). -/
theorem ends_rel {M : Mode} {mid : Prog isa}
    {s₀ s₀' : State} (h0 : (modeRISCV64 M).pre s₀) (h0' : (modeRISCV64 M).pre s₀')
    (hq : (modeRISCV64 M).pub s₀ s₀')
    (hm : UPre s₀ → UPre s₀' → 0 < N s₀ →
      RelCT isa (fun a b => LInv M s₀ 0 a ∧ LInv M s₀' 0 b) mid
        fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀')
      (.seq (.block (save ++ setup)) (.seq (.ite (.zero .s5) (.block []) mid) (.block restore)))
      fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  obtain ⟨_, hpro⟩ := prologue_taint
  obtain ⟨_, hepi⟩ := epilogue_taint
  obtain ⟨_, hnil⟩ := nil_taint
  have pro := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4, .a5]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨pub_sp hq, fun r hr => ?_⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h1, h2, h3, h4, h5, h6]) hpro).wp
    (F₁ := LInv M s₀ 0) (F₂ := LInv M s₀' 0)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have ev {t : State} {s : State} (h : LInv M t 0 s) : isa.eval (.zero .s5) s = some (decide (N t = 0)) := by
    have := Steps.eval_zero_ofNat s .s5 (k := N t - 0)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (t.gpr .a4).isLt) h.s5
    rwa [Nat.sub_zero] at this
  have nil := taintRegs (P := fun a b => (LInv M s₀ 0 a ∧ LInv M s₀' 0 b) ∧
      isa.eval (.zero .s5) a = some true) []
    (fun _ _ h => ⟨by rw [h.1.1.sp, h.1.2.sp, pub_sp hq], fun r hr => by simp at hr⟩) hnil
  have mid : RelCT isa (fun a b => LInv M s₀ 0 a ∧ LInv M s₀' 0 b) (.ite (.zero .s5) (.block []) mid)
      (fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1, ev h.2, hN]) ?_ ?_
    · refine (nil.wp (F₁ := LInv M s₀ (N s₀)) (F₂ := LInv M s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (RelCT.exists_ fun (hn : 0 < N s₀) => hm hp hp' hn).mono
        (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := taintRegs (P := fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b) [.s6]
    (fun a b h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.s6, h.2.s6, pub_S hq]⟩) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem whole_rel {M : Mode} {body : Prog isa} (hb : BodyOk M body) (hc : BodyCt M body)
    {s₀ s₀' : State} (h0 : (modeRISCV64 M).pre s₀) (h0' : (modeRISCV64 M).pre s₀')
    (hq : (modeRISCV64 M).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (whole body) fun _ _ => True :=
  ends_rel h0 h0' hq fun hp hp' hn =>
    (loop_ct hb hc hp hp' hq (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hn, h.1, h.2⟩) fun _ _ h => h

theorem whole_ct {M : Mode} {body : Prog isa} (hb : BodyOk M body) (hc : BodyCt M body) :
    ConstantTime isa (modeRISCV64 M).pre (modeRISCV64 M).pub (whole body) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel hb hc h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCbc.RISCV64
