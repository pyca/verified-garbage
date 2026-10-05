import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT2
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecLoops

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: constant time, `CL` and `AM`

IRPRF's loops: each block's counter is public (a function of the block's
index), and so are its number of blocks and every address (`prfLoop_ct`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress}

/-- No two runs. -/
theorem relCT_vac {P Q : State → State → Prop} {c : Prog isa} (h : ∀ s₁ s₂, P s₁ s₂ → False) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp _ _ => (h _ _ hp).elim

/-- A block from a state with `Cx`, facts `G` about the memory and `A`. -/
theorem cxm_blk {G : State → Mem → Prop} {A A' : State → State → Prop} {is : List Instr}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true)
    (hw : ∀ s t R EM, DPre s → Ctx s R EM t → G s t.mem → A s t →
      WP isa (.block is) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ A' s t') :
    RelCT isa (Two (At fun s t => Cx s t ∧ G s t.mem ∧ A s t)) (.block is)
      (Two (At fun s t => Cx s t ∧ G s t.mem ∧ A' s t)) :=
  cx_blk h fun s t R EM hp hc ⟨g, a⟩ => WP.mono (hw s t R EM hp hc g a) fun _ ⟨hc', hm, a'⟩ =>
    ⟨hc', by rw [hm]; exact g, a'⟩

/-- A call from a state with `Cx`, facts `G` about the frame and `A`. -/
theorem cxm_call {G : State → Mem → Prop} {A : State → State → Prop} {c : Prog isa}
    (hG : ∀ s m m', G s m → FrmKeep s m m' → G s m')
    (hct : RelCT isa (Two (At fun s t => Cx s t ∧ G s t.mem ∧ A s t)) c fun _ _ => True)
    (hw : ∀ s t R EM, DPre s → Ctx s R EM t → A s t → WP isa c t fun t' => Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem) :
    RelCT isa (Two (At fun s t => Cx s t ∧ G s t.mem ∧ A s t)) c
      (Two (At fun s t => Cx s t ∧ G s t.mem ∧ True)) :=
  two_then hct fun s t hp ⟨⟨R, EM, hc⟩, g, a⟩ => WP.mono (hw s t R EM hp hc a) fun _ h =>
    ⟨⟨R, EM, h.1⟩, hG _ _ _ g h.2, trivial⟩

/-- The message's block keeps `Ctx` and the frame. -/
theorem msg_ctx {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t t' : State} (hc : Ctx s R EM t)
    (ho : Outside (sc s) sMsg 16 t.mem t'.mem) (k : Keep [.rdx] t t') :
    Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem := by
  have hf : Frame [⟨scA s sMsg, 16⟩] t.mem t'.mem := frame_of_out ho (by decide)
  exact ⟨hc.step hp k.2.1 k.2.2 (k.cs (by decide)) hf fun r hr => by
      rw [List.mem_singleton.mp hr]; exact scS (by decide),
    frmKeep_of_frame (lo := [(sMsg, 16)]) (ws := [⟨scA s sMsg, 16⟩]) (n := 0) hp (by decide)
      (hf.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
      fun r hr => ⟨sMsg, 16, List.mem_singleton.mp hr, by decide, .inr (List.mem_singleton_self _)⟩⟩

/-- Block `j` of a loop of `N` blocks: its counter and the number of `AM`'s
blocks in their slots. -/
def GW (N : State → Nat) (j : Nat) (s : State) (m : Mem) : Prop :=
  j < N s ∧ word m (fb s) oI = BitVec.ofNat 64 j ∧ word m (fb s) oNB = BitVec.ofNat 64 (nbOf s)

theorem GW.keep {N : State → Nat} {j : Nat} : ∀ s m m', GW N j s m → FrmKeep s m m' → GW N j s m' :=
  fun _ _ _ ⟨h1, h2, h3⟩ fk => ⟨h1, (fk _ (by decide)).trans h2, (fk _ (by decide)).trans h3⟩

section
variable {label : List Nat} {lenC : List Instr} {dst : Nat} {count : Src} {N : State → Nat}

/-- One block, for constant time. -/
theorem prfBody_ct (j : Nat) (hL16 : label.length + 4 ≤ 16) (hd1 : sKDK + 32 ≤ dst)
    (hNb : ∀ s, DPre s → dst + 32 * N s ≤ scrBytes)
    (hmsg : ∀ s, DPre s → ∀ R EM t i, Ctx s R EM t → i < N s → t.gpr .rdi = sc s → t.gpr .rax = BitVec.ofNat 64 i →
      t.gpr .r9 = s.gpr .r8 → WP isa (.block (msgBytes label lenC)) t fun t' =>
        Outside (sc s) sMsg 16 t.mem t'.mem ∧ Keep [.rdx] t t')
    {hm : VG.Taint.Hint VG.X86_64.Taint.T}
    (tm : (taint.check (Taint.ofRegs [.rdi]) (.block (msgBytes label lenC)) hm).isSome = true)
    {hu : VG.Taint.Hint VG.X86_64.Taint.T}
    (tu : (taint.check (Taint.ofRegs [.rsp]) (.block (prfUpdArgs (label.length + 4))) hu).isSome = true)
    {hf : VG.Taint.Hint VG.X86_64.Taint.T}
    (tf : (taint.check (Taint.ofRegs [.rsp]) (.block (prfFinArgs (label.length + 4) dst)) hf).isSome = true)
    {hi : VG.Taint.Hint VG.X86_64.Taint.T}
    (ti : (taint.check (Taint.ofRegs [.rsp]) (.block (incr count)) hi).isSome = true) :
    RelCT isa (Two (At fun s t => Cx s t ∧ GW N j s t.mem ∧ True)) (prfBody (HH v) label lenC dst count)
      fun _ _ => True := by
  by_cases hj : dst + 32 * j + 32 ≤ scrBytes
  case neg =>
    exact relCT_vac fun _ _ ⟨_, ⟨s, S, _, ⟨hjN, _⟩, _⟩, _⟩ => hj (by have := hNb s S.p; omega)
  have hhd : sMsg ≤ dst + 32 * j := by unfold sMsg sKDK at *; omega
  refine RelCT.seq (cxm_blk (A' := fun s t => t.gpr .rdi = sc s ∧ t.gpr .rax = BitVec.ofNat 64 j ∧
      t.gpr .r9 = s.gpr .r8) (by taint_decide)
    fun s t R EM hp hc g _ => WP.mono (prfStart_run hp hc g.2.1) fun _ ⟨hc', hm', h⟩ => ⟨hc', hm', h⟩) ?_
  refine RelCT.seq (two_blk (J' := fun s t => Cx s t ∧ GW N j s t.mem ∧ True) [.rdi]
    (pins (J := fun s t => Cx s t ∧ GW N j s t.mem ∧ (t.gpr .rdi = sc s ∧ t.gpr .rax = BitVec.ofNat 64 j ∧
      t.gpr .r9 = s.gpr .r8)) [(.rdi, sc)] (by
        simp only [List.mem_singleton]; rintro p rfl s t h; exact h.2.2.1)
      (by simp only [List.mem_singleton]; rintro p rfl; exact sc_pin)) tm
    fun s t hp ⟨⟨R, EM, hc⟩, g, d, a, r⟩ => WP.mono (hmsg s hp R EM t j hc g.1 d a r) fun _ ⟨ho, k⟩ => by
      obtain ⟨hc', fk⟩ := msg_ctx hp hc ho k
      exact ⟨⟨R, EM, hc'⟩, GW.keep _ _ _ g fk, trivial⟩) ?_
  refine RelCT.seq (cxm_blk (A' := HIA sKDK) (by taint_decide)
    fun s t R EM hp hc _ _ => WP.mono (macInitArgs_run hp hc (by decide)) fun _ ⟨hc', hm', h⟩ => ⟨hc', hm', h⟩) ?_
  refine RelCT.seq (cxm_call GW.keep (hinit_two (v := v) (by decide) (by decide) fun _ _ h => ⟨h.1, h.2.2⟩)
    fun s t R EM hp hc ⟨h1, h2, h3, h4, h5⟩ => hinit_cx hp hc (by decide) (by decide) h1 h2 h3 h4 h5) ?_
  refine RelCT.seq (cxm_blk (A' := fun s t => t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = BitVec.ofNat 64 64 ∧
      t.gpr .rdx = scA s sMsg ∧ (t.gpr .rcx).toNat = label.length + 4 ∧ t.gpr .r8 = scA s sWork) tu
    fun s t R EM hp hc _ _ => WP.mono (prfUpdArgs_run hp hc (by omega)) fun _ ⟨hc', hm', h⟩ => ⟨hc', hm', h⟩) ?_
  have hdm : ∀ s, DPre s → DataOk s (scA s sMsg) (label.length + 4) := fun s hp =>
    DataOk.scr hp (le_refl _) (by unfold scrBytes sMsg; omega)
  refine RelCT.seq (cxm_call GW.keep (upd_two (v := v) (da := fun s => scA s sMsg) (L := fun _ => label.length + 4)
      (si := fun _ => BitVec.ofNat 64 64) (fun _ _ h => ⟨h.1, h.2.2⟩) hdm (scA_pin sMsg) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl))
    fun s t R EM hp hc ⟨h1, _, h3, h4, h5⟩ => upd_cx hp hc (hdm s hp) h1 h3 h4 h5) ?_
  refine RelCT.seq (cxm_blk (A' := fun s t => t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = scA s sOuter ∧
      t.gpr .rdx = BitVec.ofNat 64 (64 + (label.length + 4)) ∧ t.gpr .rcx = scA s (dst + 32 * j) ∧
      t.gpr .r8 = scA s sWork) tf
    fun s t R EM hp hc g _ => WP.mono (prfFinArgs_run hp hc (by omega) (by unfold scrBytes at hj; omega) g.2.1)
      fun _ ⟨hc', hm', h⟩ => ⟨hc', hm', h⟩) ?_
  refine RelCT.seq (cxm_call GW.keep (hfin_two (v := v) (dOff := fun _ => dst + 32 * j)
      (cnt := fun _ => BitVec.ofNat 64 (64 + (label.length + 4))) (fun _ => hhd) (fun _ => hj)
      (fun _ _ h => ⟨h.1, h.2.2⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl))
    fun s t R EM hp hc ⟨h1, h2, h3, h4, h5⟩ => hfin_cx hp hc hhd hj h1 h2 h3 h4 h5) ?_
  exact two_taint [.rsp] (rsp_pin fun _ _ h => h.1) ti

/-- The loop of IRPRF's blocks, for constant time. -/
theorem prfLoop_ct (hNs : ∀ a s, Sib a s → N s = N a)
    (hL16 : label.length + 4 ≤ 16) (hd1 : sKDK + 32 ≤ dst) (hNb : ∀ s, DPre s → dst + 32 * N s ≤ scrBytes)
    (hmsg : ∀ s, DPre s → ∀ R EM t i, Ctx s R EM t → i < N s → t.gpr .rdi = sc s → t.gpr .rax = BitVec.ofNat 64 i →
      t.gpr .r9 = s.gpr .r8 → WP isa (.block (msgBytes label lenC)) t fun t' =>
        Outside (sc s) sMsg 16 t.mem t'.mem ∧ Keep [.rdx] t t')
    (hincr : ∀ s, DPre s → ∀ R EM t i, Ctx s R EM t → i < N s → word t.mem (fb s) oI = BitVec.ofNat 64 i →
      word t.mem (fb s) oNB = BitVec.ofNat 64 (nbOf s) → WP isa (.block (incr count)) t (Incr s R EM t i (N s)))
    {hm : VG.Taint.Hint VG.X86_64.Taint.T}
    (tm : (taint.check (Taint.ofRegs [.rdi]) (.block (msgBytes label lenC)) hm).isSome = true)
    {hu : VG.Taint.Hint VG.X86_64.Taint.T}
    (tu : (taint.check (Taint.ofRegs [.rsp]) (.block (prfUpdArgs (label.length + 4))) hu).isSome = true)
    {hf : VG.Taint.Hint VG.X86_64.Taint.T}
    (tf : (taint.check (Taint.ofRegs [.rsp]) (.block (prfFinArgs (label.length + 4) dst)) hf).isSome = true)
    {hi : VG.Taint.Hint VG.X86_64.Taint.T}
    (ti : (taint.check (Taint.ofRegs [.rsp]) (.block (incr count)) hi).isSome = true) :
    RelCT isa (Two (At fun s t => Cx s t ∧ GW N 0 s t.mem ∧ True))
      (.loop (prfBody (HH v) label lenC dst count) .ne) fun _ _ => True := by
  have key := two_loop (α := State) (Φ := fun a j t => At (fun s t => Cx s t ∧ GW N j s t.mem ∧ True) a t)
    (Ψ := fun _ _ => True) (body := prfBody (HH v) label lenC dst count) (cond := .ne) N
    ((relCT_union fun j => prfBody_ct (v := v) j hL16 hd1 hNb hmsg tm tu tf ti).mono
      (fun _ _ ⟨p, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨p.2, p.1, h₁, h₂⟩) fun _ _ q => q)
    fun a j t _ ⟨s, S, ⟨R, EM, hc⟩, ⟨hjN, hI, hNB⟩, _⟩ => by
      have hp := S.p
      refine WP.mono (prf_body_ctx (v := v) hp hL16 hd1 (hNb s hp) (hmsg s hp R EM) (hincr s hp R EM) hjN hc hI hNB)
        fun t' ⟨hz, hc', hI', hNB'⟩ => ⟨?_, fun hl => ⟨s, S, ⟨R, EM, hc'⟩, ⟨by rw [hNs _ _ S]; exact hl, hI', hNB'⟩,
          trivial⟩, fun _ => trivial⟩
      rw [hNs _ _ S] at hz
      by_cases he : j + 1 = N a
      · simp [eval, hz, he]
      · simp [eval, hz, he]; omega
  exact key.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨let ⟨s, S, _, g, _⟩ := h₁; by rw [← hNs _ _ S]; exact g.1, h₁⟩,
    ⟨let ⟨s, S, _, g, _⟩ := h₂; by rw [← hNs _ _ S]; exact g.1, h₂⟩⟩) fun _ _ _ => trivial

end

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
