module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndCTScan
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndHeads
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcContract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCT
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndCTScan
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndHeads
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcContract
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86-64: constant time

## The call

With `PS` full: the tape's address and the call's arguments by the taint
analysis, from the registers correctness fixes; the call of
`vg_rsa_pkcs1_encrypt_precomputed`, constant time for its contract, whose
public data (the key, `pre`, the pointers and lengths) both runs share; and
the status and the wipe of `PS`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (encStack)
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- With `PS` full, before the call's arguments. -/
def AccPt (a t : State) : Prop :=
  ∃ s, PR a s ∧ Ready s t (N a) (kept s (N a))

def LoadedPt (a u : State) : Prop :=
  ∃ s t, PR a s ∧ Ready s t (N a) (kept s (N a)) ∧ u.gpr .rax = s.gpr .rdx ∧ Keep [.rax] t u

def TapePt (a u : State) : Prop :=
  ∃ s t, PR a s ∧ Ready s t (N a) (kept s (N a)) ∧ u.mem = tapeMem s t.mem (N a) ∧ Keep [.rax, .r10] t u

def ArgsPt (a w : State) : Prop := ∃ s, PR a s ∧ Args s w (N a) (kept s (N a))

def AfterPt (a u : State) : Prop := ∃ s, PR a s ∧ AfterCall s u (N a) (kept s (N a))

def StatPt (a v : State) : Prop :=
  ∃ s, PR a s ∧ v.gpr .rdi = off (fb s) oBuf ∧ v.gpr .rcx = BitVec.ofNat 64 (psLen s) ∧
    v.gpr .r10 = BitVec.ofNat 64 0

theorem tape_two : RelCT isa (Two AccPt) tapeArgs (Two TapePt) := by
  refine two_post (RelCT.seq (two_piece [.rsp] (fun a t₁ t₂ ⟨s₁, S₁, R₁⟩ ⟨s₂, S₂, R₂⟩ r hr => ?_)
      (by taint_decide) (Ψ := LoadedPt) fun a t ⟨s, S, R⟩ =>
        WP.mono (WP.keep [.rax] (tapeLoad_ok S.pre R.rsp R.wr R.slots.sTape) rfl) fun u ⟨h, k⟩ =>
          ⟨s, t, S, R, h, k⟩)
    (two_taint [.rax, .rcx] (fun a u₁ u₂ ⟨s₁, t₁, S₁, R₁, x₁, k₁⟩ ⟨s₂, t₂, S₂, R₂, x₂, k₂⟩ r hr => ?_)
      (by taint_decide))) fun a t ⟨s, S, R⟩ =>
        WP.mono (tapeArgs_ok S.pre R.rsp R.wr R.slots.sTape R.rcx) fun u ⟨hm, k⟩ => ⟨s, t, S, R, hm, k⟩
  · rw [List.mem_singleton.mp hr, R₁.rsp, R₂.rsp, S₁.fbEq, S₂.fbEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [x₁, x₂, S₁.gprEq (by decide), S₂.gprEq (by decide)]
    · rw [(k₁.gpr (by decide)).trans R₁.rcx, (k₂.gpr (by decide)).trans R₂.rcx]

theorem args_two : RelCT isa (Two TapePt) (.seq stackArgs (.block regArgs)) (Two ArgsPt) :=
  two_post (two_taint [.rsp] (fun a u₁ u₂ ⟨s₁, t₁, S₁, R₁, _, k₁⟩ ⟨s₂, t₂, S₂, R₂, _, k₂⟩ r hr => by
      rw [List.mem_singleton.mp hr, (k₁.gpr (by decide)).trans R₁.rsp, (k₂.gpr (by decide)).trans R₂.rsp,
        S₁.fbEq, S₂.fbEq]) (by taint_decide))
    fun a u ⟨s, t, S, R, hm, k⟩ => WP.mono (prep_rest_ok S.pre R hm k) fun w ⟨h, _⟩ => ⟨s, S, h⟩

/-- The memory the callee sees: changed since the entry only in the stack and
the tape. -/
theorem entry_frame {s w : State} {i : Nat} {ps : List Byte} (h : Args s w i ps)
    (rd wr : List Region) : Frame [stkR s, tapeR s] s.mem (w.callEntry.withRegions rd wr).mem := by
  rw [State.withRegions_mem, State.callEntry_mem, h.rsp, fb_sub8]
  exact h.fr.writeW (r := stkR s) (List.mem_cons_self ..) _
    (show (stkR s).Contains (off (kb s) encStack) 8 from by
      rw [stkR_eq]; exact Offset.contains_base _ (by decide) (by decide))

/-- What the callee's contract makes public, at its entry. -/
theorem entry_view {s w : State} (hp : RPre s) {i : Nat} {ps : List Byte} (h : Args s w i ps) :
    let E := w.callEntry.withRegions (callRd s) (callWr s)
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map E.gpr =
      [s.gpr .rdi, s.gpr .r8, s.gpr .rcx, s.gpr .r8, s.gpr .r9, stackArg s 0, fb s - 8] ∧
    (List.range 8).map (stackArg E) = (List.range 8).map (callArg s) ∧
    Spec.Rsa.bytesAt E.mem (E.gpr .rdx) (E.gpr .rcx).toNat = nB s ∧
    Spec.Rsa.bytesAt E.mem (E.gpr .r8) (E.gpr .r9).toNat = eB s ∧
    Spec.Rsa.wordsAt E.mem (stackArg E 6) (stackArg E 7).toNat = preW s := by
  intro E
  have hE (j : Nat) (hj : j < 8) : stackArg E j = callArg s j :=
    (stackArg_entry h.rsp _ _ (by omega)).trans (h.args j hj)
  have hf := entry_frame h (callRd s) (callWr s)
  have g : ∀ r, r ≠ .rsp → E.gpr r = w.gpr r := fun r hr => by
    simp only [E, State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, g .rdi (by decide), g .rsi (by decide), g .rdx (by decide),
      g .rcx (by decide), g .r8 (by decide), g .r9 (by decide), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9]
    simp only [E, State.withRegions_gpr, State.callEntry_rsp, h.rsp]
  · exact List.map_congr_left fun j hj => hE j (List.mem_range.mp hj)
  · rw [g .rdx (by decide), g .rcx (by decide), h.rdx, h.rcx]
    exact bytes_apart (R := nR s) hf hp.dKn hp.dTn (by have := hp.wN; unfold nR; dsimp only; omega)
  · rw [g .r8 (by decide), g .r9 (by decide), h.r8, h.r9]
    exact bytes_apart (R := eR s) hf hp.dKe hp.dTe (by have := hp.wE; unfold eR; dsimp only; omega)
  · rw [hE 6 (by decide), hE 7 (by decide)]
    exact words_apart hf hp.dKq hp.dTq hp.wQ

theorem call_ct (v : PublicImpl) : RelCT isa (Two ArgsPt) (.call (encName v) (encCode v)) fun _ _ => True := by
  refine RelCT.callEx (k := VG.Proof.RsaPkcs1Enc.X86_64.Pc.contract)
    (VG.Proof.RsaPkcs1Enc.X86_64.Pc.code_correct v) (PcCT.code_constantTime v)
    fun w₁ w₂ ⟨a, ⟨s₁, S₁, A₁⟩, ⟨s₂, S₂, A₂⟩⟩ => ?_
  obtain ⟨r₁, g₁, n₁, e₁, q₁⟩ := entry_view S₁.pre A₁
  obtain ⟨r₂, g₂, n₂, e₂, q₂⟩ := entry_view S₂.pre A₂
  obtain ⟨c₁, w₁'⟩ := call_covers S₁.pre A₁
  obtain ⟨c₂, w₂'⟩ := call_covers S₂.pre A₂
  have hr : [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map
        (w₁.callEntry.withRegions (callRd s₁) (callWr s₁)).gpr =
      [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (w₂.callEntry.withRegions (callRd s₂) (callWr s₂)).gpr := by
    rw [r₁, r₂, S₁.gprEq (r := .rdi) (by decide), S₂.gprEq (r := .rdi) (by decide),
      S₁.gprEq (r := .r8) (by decide), S₂.gprEq (r := .r8) (by decide),
      S₁.gprEq (r := .rcx) (by decide), S₂.gprEq (r := .rcx) (by decide),
      S₁.gprEq (r := .r9) (by decide), S₂.gprEq (r := .r9) (by decide),
      S₁.argEq (j := 0) (by decide), S₂.argEq (j := 0) (by decide), S₁.fbEq, S₂.fbEq]
  have hc : (List.range 8).map (callArg s₁) = (List.range 8).map (callArg s₂) := by
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil, callArg, S₁.argEq (by decide : 1 < 9),
      S₂.argEq (by decide : 1 < 9), S₁.argEq (by decide : 2 < 9), S₂.argEq (by decide : 2 < 9),
      S₁.argEq (by decide : 5 < 9), S₂.argEq (by decide : 5 < 9), S₁.argEq (by decide : 6 < 9),
      S₂.argEq (by decide : 6 < 9), S₁.argEq (by decide : 7 < 9), S₂.argEq (by decide : 7 < 9),
      S₁.argEq (by decide : 8 < 9), S₂.argEq (by decide : 8 < 9), S₁.fbEq, S₂.fbEq, S₁.psEq, S₂.psEq]
  have ga : ∀ j < 8, stackArg (w₁.callEntry.withRegions (callRd s₁) (callWr s₁)) j =
      stackArg (w₂.callEntry.withRegions (callRd s₂) (callWr s₂)) j := fun j hj => by
    have h₁ := congrArg (fun l => l.getD j 0) (g₁.trans (hc.trans g₂.symm))
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hj] using h₁
  refine ⟨callRd s₁, callWr s₁, callRd s₂, callWr s₂, call_pre S₁.pre A₁, call_pre S₂.pre A₂, ?_, c₁, w₁', c₂,
    w₂', by rw [A₁.rsp, A₂.rsp, S₁.fbEq, S₂.fbEq]⟩
  refine ⟨⟨fun r hr' => ?_, ?_, ?_, ?_⟩, ga 6 (by decide), ga 7 (by decide), ?_⟩
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · apply List.ext_getElem (by simp)
    intro j h₁ _
    simp only [List.length_map, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_range]
    exact ga j (by omega)
  · rw [n₁, n₂, S₁.2.2.2.2.1.symm.trans S₂.2.2.2.2.1]
  · rw [e₁, e₂, S₁.2.2.2.2.2.1.symm.trans S₂.2.2.2.2.2.1]
  · rw [q₁, q₂, S₁.2.2.2.2.2.2.1.symm.trans S₂.2.2.2.2.2.2.1]

theorem call_two (v : PublicImpl) : RelCT isa (Two ArgsPt) (.call (encName v) (encCode v)) (Two AfterPt) :=
  two_post (call_ct v) fun _ _ ⟨s, S, A⟩ => WP.mono (call_ok v S.pre A) fun _ ⟨h, _, _⟩ => ⟨s, S, h⟩

theorem status_two : RelCT isa (Two AfterPt) (.block status) (Two StatPt) :=
  two_piece [.rsp] (fun a u₁ u₂ ⟨s₁, S₁, A₁⟩ ⟨s₂, S₂, A₂⟩ r hr => by
      rw [List.mem_singleton.mp hr, A₁.rsp, A₂.rsp, S₁.fbEq, S₂.fbEq]) (by taint_decide)
    fun _ _ ⟨s, S, A⟩ => WP.mono (statusHead_ok S.pre A) fun _ h => ⟨s, S, h⟩

theorem wipe_two : RelCT isa (Two StatPt) (.seq wipe (.block [.mov32 .rax (.reg .r11)])) fun _ _ => True :=
  two_taint [.rdi, .rcx, .r10] (fun a v₁ v₂ ⟨s₁, S₁, d₁, c₁, z₁⟩ ⟨s₂, S₂, d₂, c₂, z₂⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [d₁, d₂, S₁.fbEq, S₂.fbEq]
    · rw [c₁, c₂, S₁.psEq, S₂.psEq]
    · rw [z₁, z₂]) (by taint_decide)

theorem accept_ct (v : PublicImpl) : RelCT isa (Two AccPt) (accept (encName v) (encCode v)) fun _ _ => True :=
  RelCT.seq (RelCT.seq tape_two args_two) (RelCT.seq (call_two v) (RelCT.seq status_two wipe_two))

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd

/-!
## The whole function

The short tape's path (`reject_ct`: `out` zeroed, the drawn octets wiped, the
budget and the request, whose branch is on public lengths), the whole body
(`body_ct`), and `Verified`.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (encStack allocState_gpr)
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-! ## The short tape -/

/-- The tape read, with fewer than `psLen` nonzero octets. -/
def RejPt (a u : State) : Prop :=
  ∃ s t₀, PR a s ∧ Before s t₀ ∧ At s t₀ (N a) u ∧ N a = (stackArg s 4).toNat ∧
    (kept s (N a)).length < psLen s

/-- The facts the short tape's blocks need. -/
def RZ (a u : State) : Prop :=
  ∃ s, PR a s ∧ u.gpr .rsp = fb s ∧ u.wr = ⟨fb s, frameBytes⟩ :: s.wr ∧ Slots s u.mem ∧
    u.gpr .rdx = BitVec.ofNat 64 (kept s (N a)).length ∧ u.gpr .r11 = stackArg s 4 ∧
    (kept s (N a)).length < psLen s

def ZhPt (a u : State) : Prop := ∃ s, PR a s ∧ u.gpr .rdi = s.gpr .rdi ∧ u.gpr .r10 = s.gpr .r8

theorem rej_slots {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u) :
    Slots s u.mem := by
  have hF := fb_toNat hp
  have w : ∀ {d : Nat}, d + 8 ≤ oBuf → word u.mem (fb s) d = word t₀.mem (fb s) d := fun hd =>
    hI.out.word (.inl hd) (by unfold frameBytes oBuf at *; omega)
  exact ⟨(w (by decide)).trans hb.slots.sOut, (w (by decide)).trans hb.slots.sTape,
    (w (by decide)).trans hb.slots.sN, (w (by decide)).trans hb.slots.sK, (w (by decide)).trans hb.slots.sE,
    (w (by decide)).trans hb.slots.sPs⟩

theorem zero_two : RelCT isa (Two RejPt) zeroOut (Two RZ) := by
  refine two_post (RelCT.seq (two_piece [.rsp] (fun a u₁ u₂ ⟨s₁, t₁, S₁, B₁, I₁, _⟩ ⟨s₂, t₂, S₂, B₂, I₂, _⟩ r hr => ?_)
      (by taint_decide) (Ψ := ZhPt) fun a u ⟨s, t₀, S, B, I, _, _⟩ =>
        WP.mono (zeroHead_ok S.pre ((I.keep.gpr (by decide)).trans B.rsp) (I.keep.2.2.trans B.wr)
          (rej_slots S.pre B I)) fun v h => ⟨s, S, h⟩)
    (two_taint [.rdi, .r10] (fun a v₁ v₂ ⟨s₁, S₁, d₁, z₁⟩ ⟨s₂, S₂, d₂, z₂⟩ r hr => ?_) (by taint_decide))) ?_
  · rw [List.mem_singleton.mp hr, (I₁.keep.gpr (by decide)).trans B₁.rsp, (I₂.keep.gpr (by decide)).trans B₂.rsp,
      S₁.fbEq, S₂.fbEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [d₁, d₂, S₁.gprEq (by decide), S₂.gprEq (by decide)]
    · rw [z₁, z₂, S₁.gprEq (by decide), S₂.gprEq (by decide)]
  · intro a u ⟨s, t₀, S, B, I, hN, hc⟩
    have hp := S.pre
    have hsp : u.gpr .rsp = fb s := (I.keep.gpr (by decide)).trans B.rsp
    have hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr := I.keep.2.2.trans B.wr
    refine WP.mono (zeroOut_ok hp hsp hwr (rej_slots hp B I)) fun u₁ ⟨f₁, _, k₁⟩ => ?_
    have hsl := rej_slots hp B I
    have slotOut : ∀ {d : Nat}, d + 8 ≤ frameBytes → (⟨off (fb s) d, 8⟩ : Region).Disjoint (outR s) :=
      fun hd => hp.dKo.sub_left (frame_sub s hd)
    have w : ∀ {d : Nat}, d + 8 ≤ frameBytes → word u₁.mem (fb s) d = word u.mem (fb s) d := fun hd =>
      f₁.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact slotOut hd)
        (by decide)
    exact ⟨s, S, (k₁.gpr (by decide)).trans hsp, k₁.2.2.trans hwr,
      ⟨(w (by decide)).trans hsl.sOut, (w (by decide)).trans hsl.sTape, (w (by decide)).trans hsl.sN,
        (w (by decide)).trans hsl.sK, (w (by decide)).trans hsl.sE, (w (by decide)).trans hsl.sPs⟩,
      (k₁.gpr (by decide)).trans I.rdx,
      (k₁.gpr (by decide)).trans ((I.keep.gpr (by decide)).trans B.r11), hc⟩

theorem wipeD_two : RelCT isa (Two RZ) wipeDrawn (Two RZ) := by
  refine two_post (two_taint [.rsp, .rdx] (fun a u₁ u₂ ⟨s₁, S₁, p₁, _, _, d₁, _, _⟩ ⟨s₂, S₂, p₂, _, _, d₂, _, _⟩ r hr => ?_)
    (by taint_decide)) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [p₁, p₂, S₁.fbEq, S₂.fbEq]
    · rw [d₁, d₂, S₁.keptEq (Nat.le_refl _), S₂.keptEq (Nat.le_refl _)]
  · intro a u ⟨s, S, hsp, hwr, hsl, hdx, h11, hc⟩
    have hp := S.pre
    have hF := fb_toNat hp
    have hP := hp.ps
    refine WP.mono (wipeDrawn_ok hp hsp hwr hc hdx) fun u₂ ⟨f₂, k₂, hdx₂⟩ => ?_
    have bufD : ∀ {d : Nat}, d + 8 ≤ oBuf →
        (⟨off (fb s) d, 8⟩ : Region).Disjoint ⟨off (fb s) oBuf, (kept s (N a)).length⟩ :=
      fun hd => Offset.disjoint (fb s) (.inl hd) (by unfold frameBytes oBuf at *; omega)
        (by unfold frameBytes oBuf at *; omega)
    have w : ∀ {d : Nat}, d + 8 ≤ oBuf → word u₂.mem (fb s) d = word u.mem (fb s) d := fun hd =>
      f₂.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact bufD hd)
        (by decide)
    exact ⟨s, S, (k₂.gpr (by decide)).trans hsp, k₂.2.2.trans hwr,
      ⟨(w (by decide)).trans hsl.sOut, (w (by decide)).trans hsl.sTape, (w (by decide)).trans hsl.sN,
        (w (by decide)).trans hsl.sK, (w (by decide)).trans hsl.sE, (w (by decide)).trans hsl.sPs⟩,
      hdx₂.trans hdx, (k₂.gpr (by decide)).trans h11, hc⟩

/-- After the budget's block. -/
def BPt (a x : State) : Prop :=
  ∃ s, PR a s ∧ x.gpr .r10 = BitVec.ofNat 64 (cap s) ∧ x.gpr .r8 = s.gpr .rdx ∧
    x.cf = some (decide ((stackArg s 4).toNat < cap s)) ∧ x.gpr .r11 = stackArg s 4 ∧
    x.gpr .rsp = fb s ∧ x.gpr .rdx = BitVec.ofNat 64 (kept s (N a)).length

theorem budget_two : RelCT isa (Two RZ) (.seq (.block budget) (.ite .ae (.block exhausted) (.block request)))
    fun _ _ => True := by
  refine RelCT.seq (two_piece [.rsp, .r11] (fun a u₁ u₂ ⟨s₁, S₁, p₁, _, _, _, e₁, _⟩ ⟨s₂, S₂, p₂, _, _, _, e₂, _⟩ r hr => ?_)
    (by taint_decide) (Ψ := BPt) fun a u ⟨s, S, hsp, hwr, hsl, hdx, h11, _⟩ =>
      WP.mono (WP.keep [.r10, .r8, .r11] (budgetHead_ok S.pre hsp hwr hsl h11) rfl)
        fun x ⟨⟨h10, h8, hcf, h11'⟩, k⟩ => ⟨s, S, h10, h8, hcf, h11', (k.gpr (by decide)).trans hsp,
          (k.gpr (by decide)).trans hdx⟩)
    (two_ite (fun a x₁ x₂ ⟨s₁, S₁, _, _, c₁, _⟩ ⟨s₂, S₂, _, _, c₂, _⟩ => ?_)
      (two_taint [.r8, .r11] (fun a x₁ x₂ ⟨⟨s₁, S₁, _, h₁, _, e₁, _⟩, _⟩ ⟨⟨s₂, S₂, _, h₂, _, e₂, _⟩, _⟩ r hr => ?_)
        (by taint_decide))
      (two_taint [.r8, .r10, .r11, .rdx, .rsp]
        (fun a x₁ x₂ ⟨⟨s₁, S₁, z₁, h₁, _, e₁, p₁, d₁⟩, _⟩ ⟨⟨s₂, S₂, z₂, h₂, _, e₂, p₂, d₂⟩, _⟩ r hr => ?_)
        (by taint_decide)))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [p₁, p₂, S₁.fbEq, S₂.fbEq]
    · rw [e₁, e₂, S₁.argEq (by decide), S₂.argEq (by decide)]
  · show x₁.cf.map (!·) = x₂.cf.map (!·)
    rw [c₁, c₂, S₁.lenEq, S₂.lenEq]
    simp only [cap, S₁.psEq, S₂.psEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁, h₂, S₁.gprEq (by decide), S₂.gprEq (by decide)]
    · rw [e₁, e₂, S₁.argEq (by decide), S₂.argEq (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁, h₂, S₁.gprEq (by decide), S₂.gprEq (by decide)]
    · rw [z₁, z₂]; simp only [cap, S₁.psEq, S₂.psEq]
    · rw [e₁, e₂, S₁.argEq (by decide), S₂.argEq (by decide)]
    · rw [d₁, d₂, S₁.keptEq (Nat.le_refl _), S₂.keptEq (Nat.le_refl _)]
    · rw [p₁, p₂, S₁.fbEq, S₂.fbEq]

theorem reject_ct : RelCT isa (Two RejPt) reject fun _ _ => True :=
  RelCT.seq zero_two (RelCT.seq wipeD_two budget_two)

/-! ## The body -/

def AllocPt (a t : State) : Prop := ∃ s, PR a s ∧ t = allocState frameBytes s

def FullPt (a w : State) : Prop :=
  ∃ s t₀, PR a s ∧ Before s t₀ ∧ At s t₀ (N a) w ∧ w.zf = some (decide ((kept s (N a)).length = psLen s))

theorem setup_two : RelCT isa (Two AllocPt) (.block setup) (Two ScanPt) :=
  two_piece [.rsp] (fun a t₁ t₂ ⟨s₁, S₁, e₁⟩ ⟨s₂, S₂, e₂⟩ r hr => by
      rw [List.mem_singleton.mp hr, e₁, e₂]
      simp only [allocState_gpr, ↓reduceIte]
      exact S₁.fbEq.trans S₂.fbEq.symm) (by taint_decide)
    fun a t ⟨s, S, e⟩ => by
      subst e; exact WP.mono (before_ok S.pre) fun u ⟨B, hcx, hdx, hz, _⟩ => ⟨s, S, B, hcx, hdx, hz⟩

theorem full_two : RelCT isa (Two ScanDone) (.block [.alu .cmp .rdx (.mem (sp oPs))]) (Two FullPt) :=
  two_piece [.rsp] (fun a u₁ u₂ ⟨s₁, t₁, S₁, B₁, I₁⟩ ⟨s₂, t₂, S₂, B₂, I₂⟩ r hr => by
      rw [List.mem_singleton.mp hr, (I₁.keep.gpr (by decide)).trans B₁.rsp,
        (I₂.keep.gpr (by decide)).trans B₂.rsp, S₁.fbEq, S₂.fbEq]) (by taint_decide)
    fun a u ⟨s, t₀, S, B, I⟩ => WP.mono (cmpAt_ok S.pre B I) fun v ⟨h, hz⟩ => ⟨s, t₀, S, B, h, hz⟩

theorem body_ct (v : PublicImpl) : RelCT isa (Two AllocPt) (body (encName v) (encCode v)) fun _ _ => True := by
  refine RelCT.seq setup_two (RelCT.seq scan_two (RelCT.seq full_two (two_ite
    (fun a w₁ w₂ ⟨s₁, t₁, S₁, _, _, z₁⟩ ⟨s₂, t₂, S₂, _, _, z₂⟩ => by
      rw [eval_e z₁, eval_e z₂, S₁.keptEq (Nat.le_refl _), S₂.keptEq (Nat.le_refl _), S₁.psEq, S₂.psEq])
    ((accept_ct v).mono (fun w₁ w₂ ⟨a, ⟨⟨s₁, t₁, S₁, B₁, I₁, z₁⟩, e₁⟩, ⟨⟨s₂, t₂, S₂, B₂, I₂, z₂⟩, e₂⟩⟩ => ?_)
      fun _ _ h => h)
    (reject_ct.mono (fun w₁ w₂ ⟨a, ⟨⟨s₁, t₁, S₁, B₁, I₁, z₁⟩, e₁⟩, ⟨⟨s₂, t₂, S₂, B₂, I₂, z₂⟩, e₂⟩⟩ => ?_)
      fun _ _ h => h))))
  · have f₁ : (kept s₁ (N a)).length = psLen s₁ := by
      rw [eval_e z₁] at e₁; exact of_decide_eq_true (Option.some.inj e₁)
    have f₂ : (kept s₂ (N a)).length = psLen s₂ := by
      rw [eval_e z₂] at e₂; exact of_decide_eq_true (Option.some.inj e₂)
    exact ⟨a, ⟨s₁, S₁, ready_of S₁.pre B₁ I₁ f₁⟩, ⟨s₂, S₂, ready_of S₂.pre B₂ I₂ f₂⟩⟩
  · have rej : ∀ {s t₀ w : State}, PR a s → At s t₀ (N a) w →
        w.zf = some (decide ((kept s (N a)).length = psLen s)) → isa.eval .e w = some false →
        N a = (stackArg s 4).toNat ∧ (kept s (N a)).length < psLen s := fun {s t₀ w} S I z e => by
      have hne : (kept s (N a)).length ≠ psLen s := by
        rw [eval_e z] at e; exact of_decide_eq_false (Option.some.inj e)
      have hc : (kept s (N a)).length < psLen s := by have := I.hc; omega
      refine ⟨?_, hc⟩
      have hle := VG.Proof.RsaPkcs1Enc.scanLen_le (psLen s) (randB s)
      rw [randB_length, S.scanEq] at hle
      by_contra hlt
      have := VG.Proof.RsaPkcs1Enc.lt_scanLen (n := psLen s) (rand := randB s) (i := N a) hc
        (by rw [randB_length]; omega)
      rw [S.scanEq] at this; omega
    obtain ⟨n₁, c₁⟩ := rej S₁ I₁ z₁ e₁
    obtain ⟨n₂, c₂⟩ := rej S₂ I₂ z₂ e₂
    exact ⟨a, ⟨s₁, t₁, S₁, B₁, I₁, n₁, c₁⟩, ⟨s₂, t₂, S₂, B₂, I₂, n₂, c₂⟩⟩

theorem pub_refl (s : State) : pub s s :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem code_constantTime (v : PublicImpl) :
    ConstantTime isa contract.pre contract.pub (code (encName v) (encCode v)) :=
  RelCT.constantTime (VG.Proof.RsaPkcs1Enc.X86_64.relCT_alloc ((body_ct v).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, e₁⟩, ⟨s₂, ⟨h₂, hpub⟩, e₂⟩⟩)
    fun _ _ h => h))

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed` with the
implementation `v` of the precomputed public operation, meets the shared contract. -/
theorem code_verified (v : PublicImpl) :
    Verified target (code (encName v) (encCode v)) (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack) :=
  Verified.of_correct (k := contract) (code_correct v) (code_constantTime v) implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : PublicImpl) :
    (code (encName v) (encCode v)).all (fun i => !isa.writesSp i) = true := by
  have h := PcCT.code_spSafe v
  simp only [code, body, accept, reject, scan, step, more, zeroOut, wipeDrawn, tapeArgs, stackArgs, wipe,
    Code.all, encCode, h, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd
