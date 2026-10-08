import VerifiedGarbage.Proof.AesCbc.X86.Body
import VerifiedGarbage.Proof.Framework.X86.ArgTaint

/-!
# AES-CBC on x86: constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the taint
analysis covers the code between the calls, from `esp`, the stack arguments
(which nothing writes, `argTaint`) and `esi` (the next block, which the
correctness proof pins to the public arguments), and each call of a block
function, in its frame, is constant time by its own proof (`blk_rel`).
`whole_ct`: if one run of `body` is (`BodyCt`), `whole body` is.
-/

namespace VG.Proof.AesCbc.X86

open VG VG.X86 VG.Impl.AesCbc.X86
open VG.Impl.CmacAes.X86 (setup restore)
open VG.Proof.MdStream.X86 (eval_e eval_ne)
open VG.Proof.Aes.X86 (BlocksImpl)

/-- The stack arguments of a state with the entry stack pointer, from
those of the entry state. -/
theorem arg_cur {s₀ s : State} (hesp : s.gpr .esp = s₀.gpr .esp) {i : Nat}
    (hm : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) : arg s i = arg s₀ i := by
  show s.mem.readW (argAddr s i) 32 = _
  rw [show argAddr s i = argAddr s₀ i by simp only [argAddr, hesp]]; exact hm

theorem UPre.argsOut {s₀ : State} (hp : UPre s₀) {s : State} (hesp : s.gpr .esp = E s₀) (hwr : s.wr = s₀.wr) :
    ArgsOut 6 s := by
  have hs : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  refine ⟨by rw [hesp]; omega, ?_⟩
  rw [hwr, hp.wr, hesp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_iv hp.args_iv
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_data hp.args_data
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.args_scr

/-- What two runs agree on at a point between the calls. -/
structure Pt (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = E s₀
  wr : s.wr = s₀.wr
  args : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (cbcX86 enc).pub s₀ s₀')
include hq

theorem pub_E : E s₀ = E s₀' := hq.1
theorem pub_arg {i : Nat} (hi : i < 6) : arg s₀ i = arg s₀' i := hq.2 i hi
theorem pub_N : N s₀ = N s₀' := by rw [N, N, pub_arg hq (by decide)]
theorem pub_W : W s₀ = W s₀' := pub_arg hq (by decide)
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_arg hq (by decide)]
theorem pub_Dp : Dp s₀ = Dp s₀' := pub_arg hq (by decide)
theorem pub_S : S s₀ = S s₀' := pub_arg hq (by decide)
theorem pub_D32 (k : Nat) : D32 s₀ k = D32 s₀' k := by rw [D32, D32, pub_Dp hq]

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem Pt.agree (hp : UPre s₀) (hp' : UPre s₀') {rs : List Reg} {s₁ s₂ : State} (h₁ : Pt s₀ s₁)
    (h₂ : Pt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp, pub_E hq]) (hp.argsOut h₁.esp h₁.wr) (hp'.argsOut h₂.esp h₂.wr)
    fun i hi => by rw [arg_cur (h₁.esp) (h₁.args i hi), arg_cur (h₂.esp) (h₂.args i hi), pub_arg hq hi]

end

theorem LInv.pt {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv enc s₀ k s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (UPre.big_of h.frame) hi⟩

/-- One run of `body` from `k` blocks is constant time. -/
def BodyCt (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (cbcX86 enc).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (fun s₁ s₂ => (k < N s₀ ∧ LInv enc s₀ k s₁) ∧ (k < N s₀' ∧ LInv enc s₀' k s₂)) body
      fun _ _ => True

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  lt : k < N s₀
  pre : BlkPre s (W s₀) (D32 s₀ k) (S s₀) (R s₀)
  esi : s.gpr .esi = D32 s₀ k
  pt : Pt s₀ s
  big : Frame (Big s₀) s₀.mem s.mem

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = D32 s₀ k
  pt : Pt s₀ s

theorem call_after {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : Mid s₀ k s) :
    WP isa (blkCall b) s (After s₀ k) :=
  WP.mono (blk_call ok nosp stack h.pre) fun s' hc => by
    have hk := h.lt
    have hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [h.pt.esp]; exact hp.below_eq
    have fr := hc.frame
    rw [hb, hp.d32 hk] at fr
    have big : Frame (Big s₀) s₀.mem s'.mem := h.big.trans (fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
    exact ⟨by rw [hc.saved .esi (by simp [calleeSaved]), h.esi],
      ⟨by rw [hc.saved .esp (by simp [calleeSaved]), h.pt.esp], by rw [hc.wr, h.pt.wr],
        fun _ hi => hp.arg_keep big hi⟩⟩

/-- A body: code before the call (`pre`), the call of `b`, and code after it
(`post`), whose addresses and branches depend only on `esp`, the stack
arguments and `esi`. -/
theorem body_ct {enc : Bool} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks} {pre post : List Instr}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub b.code)
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hA : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
      WP isa (.block pre) s (Mid s₀ k))
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cbcX86 enc).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => (k < N s₀ ∧ LInv enc s₀ k s₁) ∧ (k < N s₀' ∧ LInv enc s₀' k s₂))
      (.seq (.block pre) (.seq (blkCall b) (.block post))) fun _ _ => True := by
  obtain ⟨_, hA⟩ := hA
  obtain ⟨_, hB⟩ := hB
  have a := ((RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (k < N s₀ ∧ LInv enc s₀ k s₁) ∧ (k < N s₀' ∧ LInv enc s₀' k s₂))
    (argTaint [.esi] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp hp' (h.1.2.pt hp) (h.2.2.pt hp') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.esi, h.2.2.esi, pub_Dp hq]) hA).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k)
      fun _ _ h => ⟨wpA hp h.1.1 h.1.2, wpA hp' h.2.1 h.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have c := ((blk_rel ok ct (E := E s₀) (P := fun s₁ s₂ => Mid s₀ k s₁ ∧ Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_D32 hq, pub_S hq, pub_R hq]; exact h.2.pre, h.1.pt.esp,
        h.2.pt.esp.trans (pub_E hq).symm⟩).wp (F₁ := After s₀ k) (F₂ := After s₀' k)
      fun _ _ h => ⟨call_after ok nosp stack hp h.1, call_after ok nosp stack hp' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂)
    (argTaint [.esi] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp hp' h.1.pt h.2.pt fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.esi, h.2.esi, pub_D32 hq]) hB
  exact a.seq (c.seq b)

/-- What the code before the call leaves, as `Mid`. -/
theorem Mid.of {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₁ : State} {m : Mem}
    (h : LInv enc s₀ k s) (a : PreA s₀ k s m s₁) (hm : Frame [⟨blk s₀ k, 16⟩, ⟨Sv s₀, 16⟩] s.mem m) :
    Mid s₀ k s₁ := by
  have big : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (by
    rw [a.mem]
    exact hm.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
      · exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  exact ⟨hk, a.pre, by rw [a.esi, h.esi], ⟨by rw [a.esp, h.esp], by rw [a.wr, h.wr],
    fun _ hi => hp.arg_keep big hi⟩, big⟩

theorem encPre_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block encPre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block encPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decPre_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block decPre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block decPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encBody_ct (v : BlocksImpl) : BodyCt true (encBody v.enc) :=
  fun hp hp' hq k => body_ct v.encOk v.encCt v.encNosp v.encStack encPre_taint encPost_taint
    (@fun _ hp _ hk _ h => WP.mono (encA_wp hp hk h) fun _ a => Mid.of hp hk h a
      ((Proof.Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt false (decBody v.dec) :=
  fun hp hp' hq k => body_ct v.decOk v.decCt v.decNosp v.decStack decPre_taint decPost_taint
    (@fun _ hp _ hk _ h => WP.mono (decA_wp hp hk h) fun _ a => Mid.of hp hk h a
      ((copy4Mem_frame _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)) hp hp' hq k

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (enc : Bool) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ (k < N s₀ ∧ LInv enc s₀ k s₁) ∧ (k < N s₀' ∧ LInv enc s₀' k s₂)

theorem loop_ct {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cbcX86 enc).pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel enc s₀ s₀' n) (.loop body .ne)
      fun s₁ s₂ => LInv enc s₀ (N s₀) s₁ ∧ LInv enc s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel enc s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel enc s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (hc hp hp' hq k).wp
    (F₁ := fun (s : State) => (LInv enc s₀ (k + 1) s ∧ s.zf = some (decide (k + 1 = N s₀))) ∧ k < N s₀)
    (F₂ := fun (s : State) => LInv enc s₀' (k + 1) s ∧ s.zf = some (decide (k + 1 = N s₀')))
    fun _ _ h => ⟨WP.mono (hb hp h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩, hb hp' h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hk⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s₁ = _; rw [eval_ne, z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + 1 = N s₀ := by simpa using hf
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : k + 1 ≠ N s₀ := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, ⟨by omega, l₁⟩, ⟨by omega, l₂⟩⟩

/-! ## The whole function -/

theorem whole_rel {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body)
    {s₀ s₀' : State} (h0 : (cbcX86 enc).pre s₀) (h0' : (cbcX86 enc).pre s₀')
    (hq : (cbcX86 enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (whole body) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  have pt₀ : ∀ {t : State}, UPre t → Pt t t := fun _ => ⟨rfl, rfl, fun _ _ => rfl⟩
  have pro := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact Pt.agree hq hp hp' (pt₀ hp) (pt₀ hp') fun r hr => by simp at hr)
    (c := .block setup) (by taint_decide)).wp
    (F₁ := fun (s : State) => LInv enc s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)))
    (F₂ := fun (s : State) => LInv enc s₀' 0 s ∧ s.zf = some (decide (N s₀' = 0)))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have ev {s : State} (h : s.zf = some (decide (N s₀ = 0))) : isa.eval .e s = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [eval_e, h]
  have ev' {s : State} (h : s.zf = some (decide (N s₀' = 0))) : isa.eval .e s = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [eval_e, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv enc s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv enc s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0)))) ∧ isa.eval .e a = some true) (argTaint [] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp hp' (h.1.1.1.pt hp) (h.1.2.1.pt hp') fun r hr => by simp at hr)
    (c := .block []) (by taint_decide)
  have mid : RelCT isa (fun a b => (LInv enc s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv enc s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0))))
      (.ite .e (.block []) (.loop body .ne)) (fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv enc s₀ (N s₀)) (F₂ := LInv enc s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (loop_ct hb hc hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ⟨?_, h.1.1.1⟩, ⟨?_, h.1.2.1⟩⟩)
        fun _ _ h => h
      all_goals
        have := h.2; rw [ev h.1.1.2] at this
        have : N s₀ ≠ 0 := by simpa using this
        omega
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b)
    (argTaint [] (4 + 4 * 6)) (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (c := .block (restore 5)) (by taint_decide)
  exact pro.seq (mid.seq epi)

theorem whole_ct {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body) :
    ConstantTime isa (cbcX86 enc).pre (cbcX86 enc).pub (whole body) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel hb hc h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCbc.X86
