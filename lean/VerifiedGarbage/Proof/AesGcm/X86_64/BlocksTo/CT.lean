import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT

/-!
# AES-GCM on whole blocks out of place, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments go through the same pieces: each load of `scratch`
from the stack gives both the same pointer (`rel_r11`), after which the taint
analysis checks the piece from it and `rsp`; the interleaved loops are checked
from the arguments in their registers and the output in `r10`; the branch on
the blocks left agrees (`tailHead_ok`); and the copy and the call get the same
pointers and lengths (`blkE_rel`), from what correctness says of each run
(`rel_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `scratch`, loaded from the stack into `r11`. -/
theorem loadR11_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 24))]) s fun s' =>
      s'.gpr .r11 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .r11 → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r a; simp [gpr_setReg, a]

theorem loadR11_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (at_ .rsp 24))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- A block that first loads `scratch` into `r11`, from states that agree on
`rs` (with `rsp`) and hold the same pointer there, checked from `r11` and
`rs`. -/
theorem rel_r11 {P : State → State → Prop} {l₀ l : List Instr}
    (hl : l₀ = ([.mov .r11 (.mem (at_ .rsp 24))] : List Instr) ++ l) (rs rs' : List Reg) (hrs : .rsp ∈ rs)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hS : ∀ s₁ s₂, P s₁ s₂ → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 24) 64 =
      s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 24) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 24) 8)
    (hc : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: rs)) (.block l) hc).map fun τ' =>
      (RegSet.ofList rs').subset τ'.regs && (!false || τ'.flags)) = some true) :
    RelCT isa P (.block l₀) fun s₁ s₂ => ∀ r ∈ rs', s₁.gpr r = s₂.gpr r := by
  subst hl
  have l₁ := RelCT.wpDep (rel_taint (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hag _ _ h _ hrs) loadR11_check)
    (F := fun (σ s' : State) => s'.gpr .r11 = σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      ∀ r, r ≠ .r11 → s'.gpr r = σ.gpr r)
    fun s₁ s₂ h => ⟨loadR11_ok (hS _ _ h).2.1, loadR11_ok (hS _ _ h).2.2⟩
  refine rel_block_split (RelCT.seq l₁ ((rel_regs (.r11 :: rs) rs' false (fun s₁ s₂ h r hr => ?_) hc).mono
    (fun _ _ h => h) fun _ _ h => h.1))
  obtain ⟨-, σ₁, σ₂, hσ, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ := h
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [a₁, a₂]; exact (hS _ _ hσ).1
  · by_cases hx : r = .r11
    · subst hx; rw [a₁, a₂]; exact (hS _ _ hσ).1
    · rw [b₁ r hx, b₂ r hx]; exact hag _ _ hσ r hr

/-- The blocks of `tail`. -/
abbrev headB : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 24)), .mov .rcx (.mem (at_ .r11 argN)), .alu .test .rcx (.reg .rcx)]
abbrev ptrsB : List Instr := [.mov .rsi (.mem (at_ .r11 argSrc)), .mov .rdi (.mem (at_ .r11 argDst))]
abbrev argsB : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 24)), .mov .rdi (.mem (at_ .r11 argCtx)), .mov .rsi (.mem (at_ .r11 argRounds)),
    .mov .rdx (.mem (at_ .r11 argCtr)), .mov .rcx (.mem (at_ .r11 argY)), .mov .r8 (.mem (at_ .r11 argDst)),
    .mov .r9 (.mem (at_ .r11 argN)), .mov .rax (.reg .r11)]

theorem tail_eq (enc : Fn) : tail enc = .seq (.block headB) (.ite .e (.block [])
    (.seq (.block ptrsB) (.seq copyBlocks (.seq (.block argsB)
      (.frame (.push [.rax]) (.call enc.name enc.code) (.pop .rax 1)))))) := rfl

/-- `Mid`, with the arguments of the call in their registers. -/
def AP (s : State) (q : Nat) (st : State) : Prop :=
  Mid s q q st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = C s ∧ st.gpr .rcx = Y s ∧
    st.gpr .r8 = dq s q ∧ st.gpr .r9 = BitVec.ofNat 64 (n s - q) ∧ st.gpr .rax = S s

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- `scratch` on the stack, at `Mid`. -/
theorem mid_S {q k : Nat} {st : State} (h : Mid s q k st) :
    st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s ∧
      InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
  refine ⟨?_, ?_⟩
  · rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  · rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)

/-- `Mid` after the pointers of the copy. -/
theorem ptrsM_ok {q : Nat} {st : State} (h : Mid s q q st) (h11 : st.gpr .r11 = S s)
    (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa (.block ptrsB) st fun st' => Mid s q q st' ∧ st'.gpr .rsi = sq s q ∧ st'.gpr .rdi = dq s q ∧
      st'.gpr .rcx = BitVec.ofNat 64 (n s - q) :=
  WP.mono (ptrs_ok hp h h11) fun _ ⟨hsi, hdi, g₂, m₂, rd₂, wr₂⟩ =>
    ⟨h.copy hp (by rw [m₂]; exact Frame.refl _ _) (g₂ _ (by decide) (by decide))
      (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂,
      hsi, hdi, by rw [g₂ _ (by decide) (by decide), hcx]⟩

/-- `Mid` after the copy. -/
theorem copyM_ok {q : Nat} {st : State} (h : Mid s q q st) (hlt : q < n s)
    (hsi : st.gpr .rsi = sq s q) (hdi : st.gpr .rdi = dq s q) (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa copyBlocks st (Mid s q q) :=
  WP.mono (copy_ok hp h hlt hsi hdi hcx) fun _ ⟨_, f₃, g₃, rd₃, wr₃⟩ =>
    h.copy hp f₃ (g₃ _ (by decide) (by decide))
      (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃

/-- `Mid` after the arguments of the call. -/
theorem argsM_ok {q : Nat} {st : State} (h : Mid s q q st) : WP isa (.block argsB) st (AP s q) :=
  WP.mono (args_ok hp h) fun _ ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, sp₄, cs₄, m₄, rd₄, wr₄⟩ =>
    ⟨h.slots hp (by rw [sp₄, h.rsp]) (fun r hr => by rw [cs₄ r hr, h.saved r hr]) (by rw [m₄]; exact h.kept)
      (by rw [m₄]; exact Frame.refl _ _) rd₄ wr₄, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩

end

/-! ## Two runs -/

/-- What two entry states with the same public arguments share. -/
structure Pub (s₀ s₀' : State) : Prop where
  k : K s₀' = K s₀
  rsi : s₀'.gpr .rsi = s₀.gpr .rsi
  c : C s₀' = C s₀
  y : Y s₀' = Y s₀
  src : Src s₀' = Src s₀
  r9 : s₀'.gpr .r9 = s₀.gpr .r9
  sp : SP s₀' = SP s₀
  dst : Dst s₀' = Dst s₀
  sc : S s₀' = S s₀

theorem Pub.of {s₀ s₀' : State} (h : Proof.AesGcm.blocksToPub s₀ s₀') : Pub s₀ s₀' :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm,
    h.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.2.2.symm⟩

theorem Pub.en {s₀ s₀' : State} (pb : Pub s₀ s₀') : n s₀' = n s₀ := by simp only [n, pb.r9]
theorem Pub.eR {s₀ s₀' : State} (pb : Pub s₀ s₀') : R s₀' = R s₀ := by simp only [R, pb.rsi]
theorem Pub.esq {s₀ s₀' : State} (pb : Pub s₀ s₀') (q : Nat) : sq s₀' q = sq s₀ q := by simp only [sq, pb.src]
theorem Pub.edq {s₀ s₀' : State} (pb : Pub s₀ s₀') (q : Nat) : dq s₀' q = dq s₀ q := by simp only [dq, pb.dst]

/-- The registers of the arguments, which the entry keeps. -/
def args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

theorem entry_check : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: args)) (.block entry.tail) hc).map fun τ' =>
    (RegSet.ofList (.r11 :: args)).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem rest_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block rest.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem nil_check : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: args)) (.block []) hc).map
    fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem tailHead_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block headB.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem ptrs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block ptrsB) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem copy_check : ∃ hc, (taint.check (Taint.ofRegs [.rsi, .rdi, .rcx]) copyBlocks hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem args_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block argsB.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem empty_check : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true := ⟨_, by taint_decide⟩

/-- What the head of `tail` leaves. -/
def TH (s : State) (q : Nat) (st : State) : Prop :=
  Mid s q q st ∧ st.zf = some (decide (n s - q = 0)) ∧ st.gpr .r11 = S s ∧
    st.gpr .rcx = BitVec.ofNat 64 (n s - q)

/-- What the entry leaves. -/
def EntryPost (s₀ s₁ : State) : Prop :=
  s₁.gpr .r11 = S s₀ ∧ s₁.gpr .r10 = Dst s₀ ∧ (∀ r, r ≠ .r11 → r ≠ .r10 → s₁.gpr r = s₀.gpr r) ∧
    Kept s₀ 0 s₁.mem ∧ Frame [kR' s₀] s₀.mem s₁.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : BT M s₀) (hp' : BT M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

/-- Loading `scratch` from the stack, in two runs at `Mid`. -/
theorem mid_hS {q k q' k' : Nat} {s₁ s₂ : State} (h₁ : Mid s₀ q k s₁) (h₂ : Mid s₀' q' k' s₂) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 24) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 24) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 24) 8 :=
  ⟨by rw [(mid_S hp h₁).1, (mid_S hp' h₂).1, pb.sc], (mid_S hp h₁).2, (mid_S hp' h₂).2⟩

omit hp hp' in
theorem mid_rsp {q k q' k' : Nat} {s₁ s₂ : State} (h₁ : Mid s₀ q k s₁) (h₂ : Mid s₀' q' k' s₂) :
    ∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp, pb.sp]

/-- The entry, in two runs. -/
theorem entry_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ =>
    (∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂ := by
  have ea : ∀ r ∈ args, s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pb.k.symm, pb.rsi.symm, pb.c.symm, pb.y.symm, pb.src.symm, pb.r9.symm, pb.sp.symm]
  refine rel_wp (rel_r11 (l₀ := entry) (l := entry.tail) rfl args (.r11 :: args) (by simp [args])
    (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ea) (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pb.sc.symm, a_in hp (i := 2) (by decide), a_in hp' (i := 2) (by decide)⟩) entry_check)
    (fun _ _ h => h) (fun s h => by subst h; exact entry_ok hp) (fun s h => by subst h; exact entry_ok hp')

/-- The interleaved part (or nothing) and `rest`, in two runs. -/
theorem part_rel {aligned : Bool} (st : Option (StitchToCode M aligned)) :
    RelCT isa (fun s₁ s₂ => (∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂)
      (head (st.map (·.enc)) aligned (encFullTo st))
      fun s₁ s₂ => ∃ q, Mid s₀ q q s₁ ∧ Mid s₀' q q s₂ := by
  have me : ∀ (s s₁ : State), BT M s → EntryPost s s₁ → Mid s 0 0 s₁ := fun s s₁ hp h => by
    obtain ⟨_, _, g₁, k₁, f₁, rd₁, wr₁⟩ := h
    exact mid_entry hp (g₁ _ (by decide) (by decide))
      (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      k₁ f₁ rd₁ wr₁
  cases st with
  | none =>
    refine ((rel_regs (.r11 :: args) [.rsp] false (fun _ _ h => h.1) nil_check).wp
      (F₁ := Mid s₀ 0 0) (F₂ := Mid s₀' 0 0) fun s₁ s₂ h => ⟨WP.block_nil (me _ _ hp h.2.1),
        WP.block_nil (me _ _ hp' h.2.2)⟩).mono (fun _ _ h => h) fun _ _ h => ⟨0, h.2.1, h.2.2⟩
  | some p =>
    have ag : ∀ s₁ s₂, ((∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂) →
        ∀ r ∈ [Reg.r10, .r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r := by
      intro s₁ s₂ h r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [h.2.1.2.1, h.2.2.2.1, pb.dst]
      · exact h.1 r hr
    rcases p with ⟨enc, full, ok, P⟩
    cases full with
    | false =>
      have a := rel_wp (rel_regs _ [.rsp] false ag P.ct) (fun _ _ h => h.2)
        (fun _ h => stitch_ok hp ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
        (fun _ h => stitch_ok hp' ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
      have b := rel_wp (rel_r11 (l₀ := rest) (l := rest.tail) rfl
        (P := fun s₁ s₂ => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
          Mid s₀ (n s₀ - n s₀ % 16) 0 s₁ ∧ Mid s₀' (n s₀' - n s₀' % 16) 0 s₂) [.rsp] [.rsp] (by simp)
        (fun _ _ h => h.1) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) rest_check)
        (fun _ _ h => h.2) (fun _ h => rest_ok hp rfl h) (fun _ h => rest_ok hp' rfl h)
      refine (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2⟩) b).mono (fun _ _ h => h)
        fun _ _ h => ⟨n s₀ - n s₀ % 16, h.2.1, ?_⟩
      rw [← pb.en]; exact h.2.2
    | true =>
      have eq : qf s₀' = qf s₀ := by simp only [qf, pb.en]
      have a := rel_wp (rel_regs _ [.rsp] false ag P.ct) (fun _ _ h => h.2)
        (fun _ h => stitchFullTo_ok hp ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
        (fun _ h => stitchFullTo_ok hp' ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
      have b := rel_wp (rel_r11 (l₀ := rest) (l := rest.tail) rfl
        (P := fun s₁ s₂ => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
          Mid s₀ (qf s₀) (qf s₀) s₁ ∧ Mid s₀' (qf s₀') (qf s₀') s₂) [.rsp] [.rsp] (by simp)
        (fun _ _ h => h.1) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) rest_check)
        (fun _ _ h => h.2) (fun _ h => restFullTo_ok hp h) (fun _ h => restFullTo_ok hp' h)
      refine (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2⟩) b).mono (fun _ _ h => h)
        fun _ _ h => ⟨qf s₀, h.2.1, ?_⟩
      rw [← eq]; exact h.2.2

/-- The call, in two runs at the same point. -/
theorem frame_rel (B : BlkFn M) {q : Nat} (hlt : q < n s₀) :
    RelCT isa (fun s₁ s₂ => AP s₀ q s₁ ∧ AP s₀' q s₂)
      (.frame (.push [.rax]) (.call B.enc.name B.enc.code) (.pop .rax 1)) fun _ _ => True := by
  have hlt' : q < n s₀' := by rw [pb.en]; exact hlt
  refine RelCT.frame (fun _ _ h => by rw [h.1.1.rsp, h.2.1.rsp, pb.sp]) (blkE_rel B fun _ _ ⟨s₁, s₂, h, ha, hb⟩ => ?_)
  obtain ⟨⟨M₁, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩, ⟨M₂, b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩⟩ := h
  have c₂ := blkCall_of hp' M₂ hlt' b₁ b₂ b₃ b₄ b₅ b₆ b₇
  rw [pb.k, pb.c, pb.y, pb.edq, pb.sc, pb.eR, pb.en] at c₂
  exact ⟨_, _, _, _, _, _, _, ha ▸ blkCall_of hp M₁ hlt a₁ a₂ a₃ a₄ a₅ a₆ a₇, hb ▸ c₂,
    by rw [ha, hb, pushed_rsp, pushed_rsp, M₁.rsp, M₂.rsp, pb.sp]⟩

/-- `tail`, from two runs at the same point. -/
theorem tail_rel (B : BlkFn M) {q : Nat} :
    RelCT isa (fun s₁ s₂ => Mid s₀ q q s₁ ∧ Mid s₀' q q s₂) (tail B.enc) fun _ _ => True := by
  have a := rel_wp (rel_r11 (l₀ := headB) (l := headB.tail) rfl
      (P := fun s₁ s₂ => Mid s₀ q q s₁ ∧ Mid s₀' q q s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => mid_rsp pb h.1 h.2) (fun _ _ h => mid_hS hp hp' pb h.1 h.2) tailHead_check)
    (fun _ _ h => h) (G₁ := TH s₀ q) (G₂ := TH s₀' q)
    (fun _ h => WP.mono (tailHead_ok hp h) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (fun _ h => WP.mono (tailHead_ok hp' h) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
  rw [tail_eq]
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.2.1, h.2.2.2.1, pb.en]) ?_ ?_)
  · exact (rel_taint [] (fun _ _ _ r hr => by cases hr) empty_check).mono (fun _ _ h => h) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨⟨-, ⟨M₁, z₁, r11₁, cx₁⟩, ⟨M₂, z₂, r11₂, cx₂⟩⟩, hz⟩ := hP
  have hlt : q < n s₀ := by
    rw [hz] at z₁; simp only [Option.some.injEq, Bool.false_eq, decide_eq_false_iff_not] at z₁; omega
  have hlt' : q < n s₀' := by rw [pb.en]; exact hlt
  -- The pointers of the copy.
  have b := rel_wp (rel_taint (P := fun s₁ s₂ =>
      (Mid s₀ q q s₁ ∧ s₁.gpr .r11 = S s₀ ∧ s₁.gpr .rcx = BitVec.ofNat 64 (n s₀ - q)) ∧
      (Mid s₀' q q s₂ ∧ s₂.gpr .r11 = S s₀' ∧ s₂.gpr .rcx = BitVec.ofNat 64 (n s₀' - q))) (c := .block ptrsB)
      [.r11] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1, pb.sc]) ptrs_check)
    (fun _ _ h => h) (fun _ h => ptrsM_ok hp h.1 h.2.1 h.2.2) (fun _ h => ptrsM_ok hp' h.1 h.2.1 h.2.2)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧
      (Mid s₀ q q s₁ ∧ s₁.gpr .rsi = sq s₀ q ∧ s₁.gpr .rdi = dq s₀ q ∧ s₁.gpr .rcx = BitVec.ofNat 64 (n s₀ - q)) ∧
      (Mid s₀' q q s₂ ∧ s₂.gpr .rsi = sq s₀' q ∧ s₂.gpr .rdi = dq s₀' q ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (n s₀' - q))) (c := copyBlocks)
      [.rsi, .rdi, .rcx] (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1, pb.esq]
        · rw [h.2.1.2.2.1, h.2.2.2.2.1, pb.edq]
        · rw [h.2.1.2.2.2, h.2.2.2.2.2, pb.en]) copy_check)
    (fun _ _ h => h.2) (fun _ h => copyM_ok hp h.1 hlt h.2.1 h.2.2.1 h.2.2.2)
    (fun _ h => copyM_ok hp' h.1 hlt' h.2.1 h.2.2.1 h.2.2.2)
  have d := rel_wp (rel_r11 (l₀ := argsB) (l := argsB.tail) rfl
      (P := fun s₁ s₂ => True ∧ Mid s₀ q q s₁ ∧ Mid s₀' q q s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => mid_rsp pb h.2.1 h.2.2) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) args_check)
    (fun _ _ h => h.2) (G₁ := AP s₀ q) (G₂ := AP s₀' q) (fun _ h => argsM_ok hp h) (fun _ h => argsM_ok hp' h)
  have e := (frame_rel hp hp' pb B hlt).mono (P' := fun (s₁ s₂ : State) => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
    AP s₀ q s₁ ∧ AP s₀' q s₂) (fun _ _ h => h.2) fun _ _ h => h
  exact (RelCT.seq b (RelCT.seq c (RelCT.seq d e))) _ _ _ _ _ _ ⟨⟨M₁, r11₁, cx₁⟩, ⟨M₂, r11₂, cx₂⟩⟩ e₁ e₂

end

theorem encrypt_ct {M : CtxMode} (B : BlkFn M) {aligned : Bool} (st : Option (StitchToCode M aligned)) :
    ConstantTime isa (Proof.AesGcm.encryptBlocksToX86_64M M).pre Proof.AesGcm.blocksToPub
      (encrypt B.enc (st.map (·.enc)) aligned (encFullTo st)) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BT.ofM h
  have hp' := BT.ofM h'
  have pb := Pub.of hq
  refine RelCT.seq (entry_rel hp hp' pb) (RelCT.seq (part_rel hp hp' pb st) ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
  exact tail_rel hp hp' pb B _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

end VG.Proof.AesGcm.X86_64.BlocksTo
