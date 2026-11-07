module

public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksToDec.Run
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Tail
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Stitch
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksToDec.Run
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Tail
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Stitch
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.CT
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksToDec.Contract
public import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksToDec
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Verified
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM decryption of whole blocks out of place, x86-64: constant time, and the callee

Untrusted: everything here is checked by Lean. `BlkToDecFn M`: an instance of
`vg_aes_gcm_decrypt_blocks_to` for a key context of kind `M`, with what its
callers need: its contract (`decryptBlocksToX86_64M`), constant time, and its
code's static facts (no load of `mxcsr`, `rsp` kept, 24 bytes of stack).
`BlkToDecFn.ofBlocks` builds it from an instance of
`vg_aes_gcm_decrypt_blocks` and, if any, an out-of-place decryption loop.

Constant time (`decrypt_ct`), as `BlocksTo/CT.lean` proves of
`vg_aes_gcm_encrypt_blocks_to`, whose code this is, from `MidD` in place of
`Mid`: the entry and the blocks of `tail` are checked by the taint
analysis (`BlocksTo.entry_rel`, `rel_r11`, the `_check`s), the out-of-place
decryption loop from the arguments in their registers and the output in
`r10` (`PieceTo.ct`), the branch on the blocks left agrees, and the copy and
the call of `vg_aes_gcm_decrypt_blocks` get the same pointers and lengths
(`blkD_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksToDec

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Proof.AesGcm.X86_64.BlocksTo
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `MidD`, with the arguments of the call in their registers. -/
def AP (s : State) (q : Nat) (st : State) : Prop :=
  MidD s q q st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = C s ∧ st.gpr .rcx = Y s ∧
    st.gpr .r8 = dq s q ∧ st.gpr .r9 = BitVec.ofNat 64 (n s - q) ∧ st.gpr .rax = S s

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp


/-- `scratch` on the stack, at `MidD`. -/
theorem mid_S {q k : Nat} {st : State} (h : MidD s q k st) :
    st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s ∧
      InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
  refine ⟨?_, ?_⟩
  · rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  · rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)

/-- `MidD` after the pointers of the copy. -/
theorem ptrsM_ok {q : Nat} {st : State} (h : MidD s q q st) (h11 : st.gpr .r11 = S s)
    (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa (.block ptrsB) st fun st' => MidD s q q st' ∧ st'.gpr .rsi = sq s q ∧ st'.gpr .rdi = dq s q ∧
      st'.gpr .rcx = BitVec.ofNat 64 (n s - q) :=
  WP.mono (BlocksToDec.ptrs_ok hp h h11) fun _ ⟨hsi, hdi, g₂, m₂, rd₂, wr₂⟩ =>
    ⟨h.copy hp (by rw [m₂]; exact Frame.refl _ _) (g₂ _ (by decide) (by decide))
      (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂,
      hsi, hdi, by rw [g₂ _ (by decide) (by decide), hcx]⟩

/-- `MidD` after the copy. -/
theorem copyM_ok {q : Nat} {st : State} (h : MidD s q q st) (hlt : q < n s)
    (hsi : st.gpr .rsi = sq s q) (hdi : st.gpr .rdi = dq s q) (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa copyBlocks st (MidD s q q) :=
  WP.mono (BlocksToDec.copy_ok hp h hlt hsi hdi hcx) fun _ ⟨_, f₃, g₃, rd₃, wr₃⟩ =>
    h.copy hp f₃ (g₃ _ (by decide) (by decide))
      (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃

/-- `MidD` after the arguments of the call. -/
theorem argsM_ok {q : Nat} {st : State} (h : MidD s q q st) : WP isa (.block argsB) st (AP s q) :=
  WP.mono (BlocksToDec.args_ok hp h) fun _ ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, sp₄, cs₄, m₄, rd₄, wr₄⟩ =>
    ⟨h.slots hp (by rw [sp₄, h.rsp]) (fun r hr => by rw [cs₄ r hr, h.saved r hr]) (by rw [m₄]; exact h.kept)
      (by rw [m₄]; exact Frame.refl _ _) rd₄ wr₄, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩

end

/-- What the head of `tail` leaves. -/
def TH (s : State) (q : Nat) (st : State) : Prop :=
  MidD s q q st ∧ st.zf = some (decide (n s - q = 0)) ∧ st.gpr .r11 = S s ∧
    st.gpr .rcx = BitVec.ofNat 64 (n s - q)

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : BT M s₀) (hp' : BT M s₀') (pb : Pub s₀ s₀')
include hp hp' pb


/-- Loading `scratch` from the stack, in two runs at `MidD`. -/
theorem mid_hS {q k q' k' : Nat} {s₁ s₂ : State} (h₁ : MidD s₀ q k s₁) (h₂ : MidD s₀' q' k' s₂) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 24) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 24) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 24) 8 :=
  ⟨by rw [(mid_S hp h₁).1, (mid_S hp' h₂).1, pb.sc], (mid_S hp h₁).2, (mid_S hp' h₂).2⟩

omit hp hp' in
theorem mid_rsp {q k q' k' : Nat} {s₁ s₂ : State} (h₁ : MidD s₀ q k s₁) (h₂ : MidD s₀' q' k' s₂) :
    ∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp, pb.sp]

/-- The interleaved part (or nothing) and `rest`, in two runs. -/
theorem part_rel {aligned : Bool} (st : Option (StitchToDecCode M aligned)) :
    RelCT isa (fun s₁ s₂ => (∀ r ∈ .r11 :: BlocksTo.args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂)
      (head (st.map (·.dec)) aligned false)
      fun s₁ s₂ => ∃ q, MidD s₀ q q s₁ ∧ MidD s₀' q q s₂ := by
  have me : ∀ (s s₁ : State), BT M s → EntryPost s s₁ → MidD s 0 0 s₁ := fun s s₁ hp h => by
    obtain ⟨_, _, g₁, k₁, f₁, rd₁, wr₁⟩ := h
    exact BlocksToDec.mid_entry hp (g₁ _ (by decide) (by decide))
      (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      k₁ f₁ rd₁ wr₁
  cases st with
  | none =>
    refine ((rel_regs (.r11 :: BlocksTo.args) [.rsp] false (fun _ _ h => h.1) nil_check).wp
      (F₁ := MidD s₀ 0 0) (F₂ := MidD s₀' 0 0) fun s₁ s₂ h => ⟨WP.block_nil (me _ _ hp h.2.1),
        WP.block_nil (me _ _ hp' h.2.2)⟩).mono (fun _ _ h => h) fun _ _ h => ⟨0, h.2.1, h.2.2⟩
  | some p =>
    have ag : ∀ s₁ s₂, ((∀ r ∈ .r11 :: BlocksTo.args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂) →
        ∀ r ∈ [Reg.r10, .r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r := by
      intro s₁ s₂ h r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [h.2.1.2.1, h.2.2.2.1, pb.dst]
      · exact h.1 r hr
    rcases p with ⟨dec, ok, P⟩
    have a := rel_wp (rel_regs _ [.rsp] false ag P.ct) (fun _ _ h => h.2)
      (fun _ h => BlocksToDec.stitch_ok hp ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
      (fun _ h => BlocksToDec.stitch_ok hp' ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
    have b := rel_wp (rel_r11 (l₀ := rest) (l := rest.tail) rfl
      (P := fun s₁ s₂ => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
        MidD s₀ (n s₀ - n s₀ % 16) 0 s₁ ∧ MidD s₀' (n s₀' - n s₀' % 16) 0 s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => h.1) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) rest_check)
      (fun _ _ h => h.2) (fun _ h => BlocksToDec.rest_ok hp rfl h) (fun _ h => BlocksToDec.rest_ok hp' rfl h)
    refine (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2⟩) b).mono (fun _ _ h => h)
      fun _ _ h => ⟨n s₀ - n s₀ % 16, h.2.1, ?_⟩
    rw [← pb.en]; exact h.2.2

/-- The call, in two runs at the same point. -/
theorem frame_rel (B : BlkFn M) {q : Nat} (hlt : q < n s₀) :
    RelCT isa (fun s₁ s₂ => AP s₀ q s₁ ∧ AP s₀' q s₂)
      (.frame (.push [.rax]) (.call B.dec.name B.dec.code) (.pop .rax 1)) fun _ _ => True := by
  have hlt' : q < n s₀' := by rw [pb.en]; exact hlt
  refine RelCT.frame (fun _ _ h => by rw [h.1.1.rsp, h.2.1.rsp, pb.sp]) (blkD_rel B fun _ _ ⟨s₁, s₂, h, ha, hb⟩ => ?_)
  obtain ⟨⟨M₁, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩, ⟨M₂, b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩⟩ := h
  have c₂ := BlocksToDec.blkCall_of hp' M₂ hlt' b₁ b₂ b₃ b₄ b₅ b₆ b₇
  rw [pb.k, pb.c, pb.y, pb.edq, pb.sc, pb.eR, pb.en] at c₂
  exact ⟨_, _, _, _, _, _, _, ha ▸ BlocksToDec.blkCall_of hp M₁ hlt a₁ a₂ a₃ a₄ a₅ a₆ a₇, hb ▸ c₂,
    by rw [ha, hb, pushed_rsp, pushed_rsp, M₁.rsp, M₂.rsp, pb.sp]⟩

/-- `tail`, from two runs at the same point. -/
theorem tail_rel (B : BlkFn M) {q : Nat} :
    RelCT isa (fun s₁ s₂ => MidD s₀ q q s₁ ∧ MidD s₀' q q s₂) (tail B.dec) fun _ _ => True := by
  have a := rel_wp (rel_r11 (l₀ := headB) (l := headB.tail) rfl
      (P := fun s₁ s₂ => MidD s₀ q q s₁ ∧ MidD s₀' q q s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => mid_rsp pb h.1 h.2) (fun _ _ h => mid_hS hp hp' pb h.1 h.2) tailHead_check)
    (fun _ _ h => h) (G₁ := TH s₀ q) (G₂ := TH s₀' q)
    (fun _ h => WP.mono (BlocksToDec.tailHead_ok hp h) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (fun _ h => WP.mono (BlocksToDec.tailHead_ok hp' h) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
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
      (MidD s₀ q q s₁ ∧ s₁.gpr .r11 = S s₀ ∧ s₁.gpr .rcx = BitVec.ofNat 64 (n s₀ - q)) ∧
      (MidD s₀' q q s₂ ∧ s₂.gpr .r11 = S s₀' ∧ s₂.gpr .rcx = BitVec.ofNat 64 (n s₀' - q))) (c := .block ptrsB)
      [.r11] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1, pb.sc]) ptrs_check)
    (fun _ _ h => h) (fun _ h => ptrsM_ok hp h.1 h.2.1 h.2.2) (fun _ h => ptrsM_ok hp' h.1 h.2.1 h.2.2)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧
      (MidD s₀ q q s₁ ∧ s₁.gpr .rsi = sq s₀ q ∧ s₁.gpr .rdi = dq s₀ q ∧ s₁.gpr .rcx = BitVec.ofNat 64 (n s₀ - q)) ∧
      (MidD s₀' q q s₂ ∧ s₂.gpr .rsi = sq s₀' q ∧ s₂.gpr .rdi = dq s₀' q ∧
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
      (P := fun s₁ s₂ => True ∧ MidD s₀ q q s₁ ∧ MidD s₀' q q s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => mid_rsp pb h.2.1 h.2.2) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) args_check)
    (fun _ _ h => h.2) (G₁ := AP s₀ q) (G₂ := AP s₀' q) (fun _ h => argsM_ok hp h) (fun _ h => argsM_ok hp' h)
  have e := (frame_rel hp hp' pb B hlt).mono (P' := fun (s₁ s₂ : State) => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
    AP s₀ q s₁ ∧ AP s₀' q s₂) (fun _ _ h => h.2) fun _ _ h => h
  exact (RelCT.seq b (RelCT.seq c (RelCT.seq d e))) _ _ _ _ _ _ ⟨⟨M₁, r11₁, cx₁⟩, ⟨M₂, r11₂, cx₂⟩⟩ e₁ e₂

end

theorem decrypt_ct {M : CtxMode} (B : BlkFn M) {aligned : Bool} (st : Option (StitchToDecCode M aligned)) :
    ConstantTime isa (Proof.AesGcm.decryptBlocksToX86_64M M).pre Proof.AesGcm.blocksToPub
      (BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BT.ofM h
  have hp' := BT.ofM h'
  have pb := Pub.of hq
  unfold BlocksToDec.decrypt BlocksTo.encrypt
  refine RelCT.seq (entry_rel hp hp' pb) (RelCT.seq (part_rel hp hp' pb st) ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
  exact tail_rel hp hp' pb B _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

end VG.Proof.AesGcm.X86_64.BlocksToDec



namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

/-- An instance of `vg_aes_gcm_decrypt_blocks_to`, with what its callers need. -/
structure BlkToDecFn (M : CtxMode) where
  fn : Fn
  ok : ∀ s, (Proof.AesGcm.decryptBlocksToX86_64M M).pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.AesGcm.decryptBlocksToX86_64M M).post s s'
  ct : ConstantTime isa (Proof.AesGcm.decryptBlocksToX86_64M M).pre Proof.AesGcm.blocksToPub fn.code
  sp : SpSafe fn.code
  xd : fn.code.x86_64Depth ≤ 24
  mx : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spAll : fn.code.all (fun i => !X86_64.isa.writesSp i) = true

section
variable {M : CtxMode} {aligned : Bool} (st : Option (StitchToDecCode M aligned)) (B : BlkFn M)

theorem headFrom_mx : (BlocksTo.head (st.map (·.dec)) aligned false).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases st with _ | ⟨dec, ok, P⟩
  · rfl
  · simp only [Option.map, BlocksTo.head, BlocksTo.stitchPart, Code.allInstrs, P.mxcsr]
    cases aligned <;> rfl

theorem headFrom_spSafe : (BlocksTo.head (st.map (·.dec)) aligned false).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases st with _ | ⟨dec, ok, P⟩
  · rfl
  · simp only [Option.map, BlocksTo.head, BlocksTo.stitchPart, Code.all, P.spSafe]
    cases aligned <;> rfl

theorem headFrom_xdepth : (BlocksTo.head (st.map (·.dec)) aligned false).x86_64Depth = 0 := by
  rcases st with _ | ⟨dec, ok, P⟩
  · rfl
  · simp only [Option.map, BlocksTo.head, BlocksTo.stitchPart, Code.x86_64Depth, P.xdepth]
    cases aligned <;> rfl

theorem decryptTo_mx : (BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.decMx
  simp only [BlocksToDec.decrypt, BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.allInstrs, headFrom_mx st, e,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem decryptTo_spSafe :
    (BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.decSp
  simp only [BlocksToDec.decrypt, BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.all, headFrom_spSafe st, e,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem decryptTo_xdepth : (BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned).x86_64Depth ≤ 24 := by
  have e := B.decXd
  simp only [BlocksToDec.decrypt, BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.x86_64Depth,
    X86_64.Instr.frameBytes, List.length_cons, List.length_nil, headFrom_xdepth st, Nat.max_le]
  omega

theorem decryptToM_correct (s : State) (hs : (Proof.AesGcm.decryptBlocksToX86_64M M).pre s) :
    ∃ t s', Exec isa (BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.blocksToDecPost s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := BlocksToDec.decrypt_wp B aligned (st.map (·.dec))
    (fun p e => by obtain ⟨i, rfl, rfl⟩ := Option.map_eq_some_iff.1 e; exact i.ok) hs
  exact ⟨t, s', he, abiPreserved_of_exec (decryptTo_mx st B) he hg, hp⟩

end

/-- The instance of `vg_aes_gcm_decrypt_blocks_to` named `n`, calling `B`'s
`vg_aes_gcm_decrypt_blocks` and running the out-of-place loop `st`, if any. -/
def BlkToDecFn.ofBlocks {M : CtxMode} (n : String) (B : BlkFn M) {aligned : Bool}
    (st : Option (StitchToDecCode M aligned)) : BlkToDecFn M where
  fn := ⟨n, BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned⟩
  ok := decryptToM_correct st B
  ct := BlocksToDec.decrypt_ct B st
  sp := SpSafe.of_all (decryptTo_spSafe st B)
  xd := decryptTo_xdepth st B
  mx := decryptTo_mx st B
  spAll := decryptTo_spSafe st B

end VG.Proof.AesGcm.X86_64
